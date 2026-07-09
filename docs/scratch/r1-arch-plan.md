# Issue #1 Architecture Audit — Bounded PR Plan

**Planner:** lean-planner  
**Source commit:** 11a2073 / main  
**Issue:** #1 (Lean architecture audit)

---

## 1. What the issue reports (reconstructed from cited files)

The issue lists at least two findings:

**Finding 1 — Typeclass instances bundled as structure fields.**  
`DissipativeEvolution` (`EvolutionTriple.lean`) and `GelfandTriple`
(`Bochner/GelfandTriple.lean`) carry Hilbert-space instances as named fields
(`instNACG`, `instIPS`, `instCS`, `instNACG_V`, `instNACG_H`, …) rather than as
typeclass parameters.  This requires `letI := E.instNACG` threading at every call site
and prevents the standard Lean elaboration pipeline from synthesizing instances normally.

**Finding 2 — Two `ALLOW_SORRY` holes in `GelfandTriple.ofDissipativeEvolution`.**  
The original `GelfandTriple` stored `ι : V → H` as a bare function with Prop fields
`ι_linear`/`ι_continuous`, which could not be derived from `Subtype.val` against free
`normV`/`ipsV` instances.

**Finding 2 status: already closed.**  
Reading `GelfandTriple.lean` lines 55–58 and the entire `ofDissipativeEvolution` body
(lines 198–250) confirms: the CLM refactor is complete.  The field is now
`ι : V →L[ℝ] H` in the bridge constructor, and the proof body closes without any
`sorry`.  The file docstring explicitly records "0 `sorry` / 0 `ALLOW_SORRY`."
There is nothing left to prove for finding 2.

**Finding 2 for `AxiomaticClosure` imports through root — also substantially addressed.**  
`LerayHopf.Core` is explicitly axiom-free and `sorry`-free.  The root `LerayHopf.lean`
deliberately re-exports all three layers; the comment says "Core work should use
`import LerayHopf.Core`."  That separation already exists and is documented.

---

## 2. Ripple assessment for each candidate slice

### Candidate A — Finding 2 GelfandTriple sorrys (CLOSED; nothing to do)

Zero open obligations.  The CLM refactor landed in a previous PR (the docstring cites
"Issue #1 item 1" as the fix motivation).  **This slice is NOT a PR target.**

### Candidate B — Finding 1: convert structure fields to typeclass params

Changing `DissipativeEvolution.instNACG` / `instIPS` / `instCS` from fields to
`[instNACG : NormedAddCommGroup H]` typeclass parameters would require touching every
`letI := E.instNACG` / `letI := E.instIPS` / `letI := E.instCS` site.

Dependent files (grepped for `DissipativeEvolution`):
- `LerayHopf/EvolutionTriple.lean` — definition site; `WeakFormNS` uses `letI` blocks
- `LerayHopf/Torus/SolutionInterfaces.lean` — `torus3Evolution`, `GalerkinSolutionData`,
  `build_galerkin_package_of_galSeq`, assembly
- `LerayHopf/R3/SolutionInterfaces.lean` — `r3Evolution`, the ℝ³ counterpart
- `LerayHopf/Bochner/GelfandTriple.lean` — `ofDissipativeEvolution` signature and body

Changing `GelfandTriple.instNACG_V` etc. from fields to typeclass params touches:
- `LerayHopf/Bochner/GelfandTriple.lean` — definition site
- `LerayHopf/Bochner/TimeSobolev.lean` — `GelfandTriple.ιCLM`, `Vprime`,
  `hToVprime`, `W1pTime`, `w1pTime_continuous_in_H` — all use `letI := GT.instNACG_V`
  and similar
- `LerayHopf/Torus/SolutionInterfaces.lean` — `GelfandTriple.IsOfDissipativeEvolution` uses
  `GT.instNACG_H`, `GT.instIPS_H` via `HEq`

Total dependent files for the combined field→param refactor: **5 files with dense
`letI` threading throughout.**  The `HEq` constraints in `IsOfDissipativeEvolution`
(comparing `GT.instNACG_H` to `E.instNACG`) become structurally different when
instances are typeclass parameters — the `HEq.rfl` proofs in `ofDissipativeEvolution`
must be re-examined because the types differ in whether instances are explicit.

This is a signature refactor that propagates into at least 5 files and whose
correctness requires re-verifying the `HEq`-based faithfulness proof.  On a
lock-starved build (40-min CI, no local parallel build), a cascade of 5 files with
non-trivial `letI`-threading rewrites is HIGH RISK for a single PR.

**Assessment: NOT bounded enough for a single PR as-is.**

### Candidate C — Import hygiene: stop AxiomaticClosure from leaking through root

**Current state:** The separation is ALREADY IMPLEMENTED:
- `import LerayHopf.Core` — axiom-free, documented
- `import LerayHopf.Torus.Capstone` — torus axiomatic layer
- `import LerayHopf.R3Capstone` — ℝ³ axiomatic layer
- `import LerayHopf` — intentional re-export of all three

The root module docstring (lines 25–31) explicitly documents this.  There is nothing
"leaking" — the root is a deliberate umbrella.

**Assessment: Not a real open finding; already resolved by the Wave-0 refactor.**

### Candidate D — `GelfandTriple.ι` field: bare function vs CLM (partial refactor)

The `GelfandTriple` structure still stores `ι : V → H` as a bare function with
`ι_linear : IsLinearMap ℝ ι` and `ι_continuous : Continuous ι` as Prop fields
(lines 109–125 of `GelfandTriple.lean`).  The `ofDissipativeEvolution` bridge
constructor takes a genuine `ContinuousLinearMap ι : V →L[ℝ] E.H` and then stores
`fun v => ι v` as the bare function.

Changing `GelfandTriple.ι` from `V → H` to `V →L[ℝ] H` (bundled CLM), removing the
Prop fields `ι_linear` / `ι_continuous`, would:
- Simplify `TimeSobolev.lean`'s `ιCLM` def (which reconstructs the CLM from the bare
  function + Prop fields)
- Remove boilerplate at every usage site that calls `ι_linear` or `ι_continuous`

Dependent files: `GelfandTriple.lean`, `TimeSobolev.lean`, and any downstream consumer
of `GT.ι`, `GT.ι_linear`, `GT.ι_continuous`.

Grepping for `ι_linear\|ι_continuous\|GT\.ι\|\.ι `:
- `TimeSobolev.lean` — `GT.ι` appears at several sites; `ιCLM` is defined from the
  bare function + Prop fields (that def would be simplified to just `GT.ι` after the
  change)
- `GelfandTriple.lean` — definition site and `IsOfDissipativeEvolution` contract

**Ripple count: 2 files** (`GelfandTriple.lean`, `TimeSobolev.lean`).  No downstream
consumers outside the Bochner sublibrary use `GT.ι` directly.

**Assessment: This is the lowest-ripple structural improvement available.**  Two files,
no proof obligations (it is a pure signature/constructor refactor), no sorrys to
discharge, no axioms.  The `ιCLM` definition in `TimeSobolev` becomes a one-liner or
disappears.  The `IsOfDissipativeEvolution` contract in `GelfandTriple.lean` uses
`GT.ι` only in `Set.range (fun v => cast hH (GT.ι v))` — after the change this
becomes `Set.range (fun v => cast hH (GT.ι v : H))` (same shape, the CLM coercion is
automatic via `FunLike`).  The `ofDissipativeEvolution` body stores `ι := ι` instead
of `ι := fun v => ι v`; `ι_linear` and `ι_continuous` fields disappear; the structure
no longer needs them.

---

## 3. Chosen slice: `GelfandTriple.ι` field — bare function → bundled CLM

**Why this one:**
- Ripple = 2 files, both in the Bochner sublibrary (not touching Core, not touching
  any axiomatic closure).
- Zero new proofs, zero sorry discharge, zero axioms.  It is a mechanical refactor
  with a clear before/after.
- Genuinely improves the architecture: downstream users get standard CLM API
  (`ContinuousLinearMap.comp`, etc.) rather than manually managing `ι_linear` /
  `ι_continuous` props.
- The `ιCLM` definition in `TimeSobolev.lean` (which reconstructs the CLM) becomes
  either trivially `GT.ι` or a definitional equality, eliminating dead code.
- Does NOT require touching `DissipativeEvolution` (no instance-field avalanche).
- Does NOT affect the `Core` import surface.
- CI gate is the only build check needed; no sorry count changes.

---

## 4. Ordered task list

### Files to touch (in dependency order)

1. **`LerayHopf/Bochner/GelfandTriple.lean`** (lean-coder)
2. **`LerayHopf/Bochner/TimeSobolev.lean`** (lean-coder, then lean-prover for any
   proof that uses `ι_linear` / `ι_continuous` props directly)

### Declaration changes

#### `LerayHopf/Bochner/GelfandTriple.lean`

| Declaration | Change | Classification |
|---|---|---|
| `GelfandTriple.ι` | field type `V → H` → `V →L[ℝ] H` | **mechanical** (signature) |
| `GelfandTriple.ι_linear` | REMOVE (subsumed by CLM `map_add`/`map_smul`) | **mechanical** |
| `GelfandTriple.ι_continuous` | REMOVE (subsumed by CLM `.continuous`) | **mechanical** |
| `GelfandTriple.ι_injective` | change type to `Function.Injective (GT.ι : V → H)` — same statement, but now `GT.ι` coerces via `FunLike.coe` | **mechanical** |
| `GelfandTriple.ι_denseRange` | same update for CLM coercion | **mechanical** |
| `GelfandTriple.IsOfDissipativeEvolution` | `Set.range (fun v => cast hH (GT.ι v))` — no text change needed; `GT.ι v` now means `(GT.ι : V → H) v` via `FunLike`; check that `simpa` still fires | **must-verify** (lean-prover check) |
| `GelfandTriple.ofDissipativeEvolution` body | `ι := ι` instead of `ι := fun v => ι v`; remove the two `ι_linear` / `ι_continuous` goals | **mechanical** |

#### `LerayHopf/Bochner/TimeSobolev.lean`

| Declaration | Change | Classification |
|---|---|---|
| `GelfandTriple.ιCLM` | Currently constructs `V →L[ℝ] H` from bare function + Prop fields. After the change, this becomes `GT.ι` directly (or a `@[simp]` alias). **REMOVE or simplify to `def ιCLM := GT.ι`**. | **mechanical** |
| Any site using `GT.ι_linear` or `GT.ι_continuous` | Update to use `GT.ι.isLinear` / `GT.ι.continuous` | **mechanical** |
| `GelfandTriple.hToVprime` and `hToVprimeCLM` | Use `GT.ι.adjoint`-style or `innerSL`-based construction — check for any `ι_linear`/`ι_continuous` references | **mechanical** |
| `W1pTime` structure | `letI := GT.instNACG_V` threading — NOT changed in this slice | unchanged |
| `w1pTime_continuous_in_H` | Still carries `sorry -- ALLOW_SORRY` (months-class residual); NOT a target of this PR | unchanged |

### Dependency edges

```
GelfandTriple.lean (field change)
  └─→ TimeSobolev.lean (ιCLM simplification, usage site updates)
       └─→ LerayHopf.lean (import-only; no decl changes)
```

`SolutionInterfaces.lean` does NOT use `GT.ι_linear` or `GT.ι_continuous` directly
(confirmed by grep: `GelfandTriple` is imported in `SolutionInterfaces.lean` only via
`Bochner/GelfandTriple.lean`, and the `GelfandTriple.IsOfDissipativeEvolution` Prop
is defined there — its `Set.range (fun v => cast hH (GT.ι v))` expression is a
coercion site that should be transparent after the CLM change).

### Assumptions to package as `axiom`

None. This PR introduces zero new axioms.

---

## 5. Codex review points

Before proofs are attempted (i.e., immediately after lean-coder produces the new
signatures):

- `/codex:adversarial-review` on **`GelfandTriple` structure** (new `ι : V →L[ℝ] H`
  field, removed Prop fields): verify that `ι_denseRange` and `ι_injective` still
  typecheck correctly when `ι` is a CLM coerced to a function; check whether any
  `Submodule`-membership or `Set.range` usage breaks.
- `/codex:adversarial-review` on **`IsOfDissipativeEvolution`** predicate: the `HEq`
  components do not mention `ι`'s type, but the range component
  `Set.range (fun v => cast hH (GT.ι v))` uses the coercion — confirm the simpa proof
  still fires and does not silently change meaning.
- `/codex:adversarial-review` on **`ιCLM` removal / simplification** in
  `TimeSobolev.lean`: confirm downstream uses of `ιCLM` (in `hToVprime`, `W1pTime`,
  etc.) are correctly updated and that no `ι_linear`/`ι_continuous` prop is accessed
  after removal.

---

## 6. Definition of done for this PR

The PR is done when:

1. `lake build` passes (CI green) with zero new sorry and zero new axioms.
2. `scripts/check-no-sorry.sh` passes (no unmarked sorry).
3. `scripts/check-no-axiom.sh` passes (no new unmarked axiom).
4. `GelfandTriple` structure has `ι : V →L[ℝ] H` with no `ι_linear`/`ι_continuous`
   fields.
5. `GelfandTriple.ιCLM` in `TimeSobolev.lean` is either removed or is a trivial alias
   `def ιCLM := GT.ι`.
6. The 1 existing `sorry` in `TimeSobolev.lean` (`w1pTime_continuous_in_H`) and the 1
   in `Statement.lean` remain untouched (they are out of scope).
7. Codex adversarial review has been run on the three review points above and any
   findings addressed.

---

## 7. What is explicitly left for follow-up (issue #1 stays open)

- **Finding 1 full scope (instance-fields → typeclass params)** for both
  `DissipativeEvolution` and `GelfandTriple`: too wide for one PR (5 files, `HEq`
  faithfulness proof must be re-examined). Scope as a separate PR after this one
  lands, since this PR shrinks the `GelfandTriple` field count first.
- **`w1pTime_continuous_in_H` sorry** (Lions–Magenes embedding): months-class residual,
  blocked on vector-valued time-Sobolev in Mathlib.  Out of scope for any near-term
  architecture PR.
- Any other findings in issue #1 not addressed here (import hygiene is already resolved
  by the Core/TorusAxiomatic/R3Axiomatic split from Wave-0).

---

## 8. Is any finding genuinely NOT one-PR-bounded?

**Finding 1 (full instance-field → typeclass-param refactor):** Confirmed too wide.
Five files, `HEq`-based faithfulness proofs, and `letI` threading across the axiomatic
closures.  Recommend sequencing as: (a) this PR (GelfandTriple.ι CLM), then (b) a
follow-up PR tackling `DissipativeEvolution` instance fields once the Bochner sublibrary
is already cleanly CLM-based.
