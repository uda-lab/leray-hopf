# Pillar D — `Nonempty SchwartzGalerkinBasis` axiom-free (Helmholtz/Weyl density)

**Milestone:** `helmholtz-density`
**Author:** lean-planner
**Status:** task contract (no Lean edited; docs only)
**Lane:** parallel with Rellich-on-balls and ODE-continuation tracks — stays in its lane
(it touches only a NEW sibling file; does NOT edit `SolutionInterfaces.lean`).

## Goal

Discharge the single classical input that P5 (`GalerkinScheme.lean`) isolated as the
hypothesis field `SchwartzGalerkinBasis.dense_span`, by PROVING — eventually axiom-free —
the existence of the basis itself:

```
theorem nonempty_schwartzGalerkinBasis : Nonempty SchwartzGalerkinBasis
```

`SchwartzGalerkinBasis` is the structure in `LerayHopf/R3/GalerkinScheme.lean:94-108`
(fields `e : ℕ → L2VF_R3`, `e_schwartz`, `e_mem_sigma`, `dense_span`). If proven, it
combines with P5's `nonempty_r3GalerkinScheme_of_basis` (GalerkinScheme.lean:338) to
discharge `r3GalerkinScheme_exists`. **That capstone wiring is OUT OF SCOPE here** — this
milestone produces only the basis-existence result, in a NEW standalone sibling file.

**Confirmation: no `SolutionInterfaces.lean` edit.** The axiom-removal capstone (rewiring
`r3GalerkinScheme_exists` through this result) is a later sequential PR, explicitly
deferred. This milestone is read-only with respect to every existing Lean file; it only
ADDS `LerayHopf/R3/SchwartzDivFreeBasis.lean`.

---

## FEASIBILITY VERDICT: PARTIAL — blocked on one isolated analytic pillar (the curl/Helmholtz density)

Honest assessment after grepping real mathlib (`.lake/packages/mathlib/`):

### What mathlib HAS (the easy 2/3 of the problem)

1. **Schwartz density in `Lp`.** `SchwartzMap.denseRange_toLpCLM`
   (`Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:1379`):
   for `FiniteDimensional ℝ E`, `BorelSpace E`, `p ≠ ⊤`, `μ` `HasTemperateGrowth` and
   `IsFiniteMeasureOnCompacts`, `DenseRange (SchwartzMap.toLpCLM ℝ F p μ)`. All hypotheses
   hold for `Domain3 = ℝ³`, `volume`, `p = 2`. So **scalar Schwartz functions are dense in
   `Lp ℝ 2 volume`**, hence (componentwise) Schwartz vector fields are dense in the FULL
   `L2VF_R3 = L²(ℝ³;ℝ³)`. This gives density in L², NOT in the div-free subspace L²_σ.

2. **Separability / countability.** `Lp.SecondCountableTopology`
   (`Mathlib/MeasureTheory/Measure/SeparableMeasure.lean:425`) makes `L2VF_R3`
   second-countable (volume is separable; `EuclideanSpace ℝ (Fin 3)` second-countable),
   hence `SeparableSpace`. Then `exists_dense_seq` / `TopologicalSpace.exists_countable_dense`
   (`Mathlib/Topology/Bases.lean:337,346`) extract a countable dense `ℕ`-indexed family.
   This handles the `e : ℕ → …` countability requirement and the prefix-span totality
   mechanics, GIVEN a dense SET to thin out.

3. **Schwartz partial derivatives stay Schwartz (curl is constructible).**
   `lineDerivOpCLM ℝ 𝓢(Domain3,ℝ) (EuclideanSpace.single a 1) : 𝓢 →L[ℝ] 𝓢`
   (`Mathlib/Analysis/Distribution/DerivNotation.lean:185`, already used in
   `DivergenceFree.lean:72`) gives `∂_a ψ` as a Schwartz function. Therefore the curl of a
   Schwartz vector potential, `(curl ψ)_i = ∂_{a} ψ_{b} − ∂_{b} ψ_{a}` (i,a,b a cyclic
   triple in Fin 3), is a genuine Schwartz field. **This resolves the `e_schwartz`
   constraint cleanly: curls are honestly Schwartz, not Leray-projected** (the Leray
   projection is a Fourier multiplier singular at ξ=0 and need NOT preserve Schwartz, so
   the "project a Schwartz field" route would SMUGGLE a non-Schwartz field — see Codex
   review point C2). And `div(curl ψ) = 0` pointwise (Clairaut / `lineDeriv` commute) gives
   `e_mem_sigma` directly via the weak-div pairing in `DivergenceFree.lean`.

### What mathlib LACKS (the irreducible hard pillar)

4. **NO Helmholtz / Leray decomposition, NO `curl`, NO `divergence` operator, and NO
   "smooth/Schwartz divergence-free fields are dense in L²_σ".** Grep confirms zero hits for
   `Helmholtz|lerayProjection|divergenceFree|curl` as real definitions in mathlib (the
   stray `curl` matches are substrings like "curly"/"Polyrith"). There is no theorem of the
   form `DenseRange (curl ∘ toLp)` or `closure(span of Schwartz div-free) = L²_σ`.

   This is THE missing analytic content. Density of Schwartz div-free fields in L²_σ is
   classically true (curls of Schwartz potentials are dense in the solenoidal subspace; or
   equivalently the Leray projection of the dense Schwartz set is dense in L²_σ, the
   Helmholtz/Weyl lemma), but it requires either:
   - the Helmholtz decomposition `L² = L²_σ ⊕ ∇H¹` with continuity of the Leray projection
     (Fourier-multiplier or variational proof), composed with (1); OR
   - a direct curl-density argument: that `closure(span{curl ψ : ψ ∈ 𝓢})  ⊇ L²_σ`.

   Neither is in mathlib, and building either from scratch is a multi-month analytic
   undertaking (Fourier multipliers / Calderón–Zygmund OR a Bogovskii-type / vector
   potential construction). **This is the genuine blocker; it CANNOT be discharged
   axiom-free against today's mathlib.**

### Verdict

**PARTIAL (blocked on one cleanly-isolated pillar).** Components (1)(2)(3) are axiom-free
and buildable now and constitute real, reviewable progress that THINS the frontier from a
fat 6-field structure (`R3GalerkinScheme`) and an opaque `dense_span` hypothesis down to a
SINGLE scalar density statement. Component (4) — the curl/Helmholtz L²_σ density — must be
carried as the smallest honest isolated sub-hypothesis (no-smuggle), exactly the way P5
carried `dense_span`, but now strictly THINNER (see "minimal isolated sub-hypothesis").

Anyone who claims a fully axiom-free `nonempty_schwartzGalerkinBasis` today is smuggling
(4) — most likely by mis-asserting that the Leray projection preserves Schwartz, or by
asserting curl-density without proof. The contract below forbids that.

---

## The minimal honest isolated sub-hypothesis (no-smuggle)

P5 isolated `dense_span` as a `Submodule` inequality on an EXTERNALLY-SUPPLIED family. This
milestone refines it to the single irreducible scalar fact, removing the externally-supplied
family entirely (we CONSTRUCT the family from curls; only the density survives as input).

Two candidate framings; **prefer SDF-1** (smallest, most honest, decoupled from any chosen
enumeration):

### SDF-1 (recommended) — bare curl-density of L²_σ

```
/-- The single classical input: the L²-closure of the span of curls of Schwartz vector
potentials contains the whole weakly-divergence-free subspace L²_σ(ℝ³).  This is the
Helmholtz/Weyl density fact, NOT in mathlib.  Carried as a hypothesis (a `Submodule`
inequality), exactly the analogue of P5's `dense_span` but STRICTLY THINNER: it removes
the externally supplied basis family and the Schwartz/div-free witnesses (those are now
PROVED from curl structure), leaving only the density. -/
def CurlSchwartzDense : Prop :=
  (L2Sigma_R3 : Submodule ℝ L2VF_R3) ≤
    (Submodule.span ℝ (Set.range curlSchwartzL2)).topologicalClosure
```
where `curlSchwartzL2 : (Fin 3 → SchwartzMap Domain3 ℝ) → L2VF_R3` is the L²-class of the
curl of a Schwartz vector potential (a CONSTRUCTED, proved-Schwartz, proved-div-free map;
see C-decls below).

### SDF-2 (fallback, if SDF-1's span manipulation proves awkward) — Helmholtz projection density

```
/-- Fallback isolated input: the Leray projection of the (dense) Schwartz fields is dense in
L²_σ.  Equivalent classical content; use only if SDF-1's curl-span is awkward to thin to ℕ. -/
def LerayProjSchwartzDense : Prop := …  -- closure(span (lerayProjection_R3 '' Schwartz)) ⊇ L²_σ
```
SDF-2 risks SMUGGLING the Schwartz constraint: `lerayProjection_R3` need not preserve
Schwartz, so its image is NOT Schwartz, breaking `e_schwartz`. **Codex MUST gate SDF-2 (see
C2).** SDF-1 avoids this entirely because curls ARE Schwartz by construction.

Either way: the survivor input is ONE `Prop` (a density), down from P5's bundled structure
hypothesis. This is monotone refinement of the frontier, not relabeling.

---

## New file

`LerayHopf/R3/SchwartzDivFreeBasis.lean`

### Imports
```
import LerayHopf.R3.GalerkinScheme          -- SchwartzGalerkinBasis (the target structure)
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic    -- toLpCLM, denseRange_toLpCLM
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv    -- fderivCLM / lineDerivOpCLM
import Mathlib.MeasureTheory.Measure.SeparableMeasure       -- Lp.SecondCountableTopology
import Mathlib.Topology.Bases                               -- exists_dense_seq
```
(`GalerkinScheme.lean` already imports `AxiomaticClosure`, so importing it transitively pulls
the structure. We do NOT need to mention `R3GalerkinScheme`; only `SchwartzGalerkinBasis`.
Justify any import beyond these. Do NOT import `AxiomaticClosure` directly — go through
`GalerkinScheme` so the dependency edge is explicit and the capstone stays separable.)

### DAG position
```
DivergenceFree.lean
  └── … ── SolutionInterfaces.lean
              └── GalerkinScheme.lean        (SchwartzGalerkinBasis)
                      └── SchwartzDivFreeBasis.lean   [THIS FILE]
                            (NOT imported by anything yet; capstone wires it later)
```
No cycle. `SolutionInterfaces.lean` is untouched.

### Namespace / opens
```
namespace LerayHopf
open MeasureTheory SchwartzMap
open scoped Topology
```

---

## Declarations in dependency order

Marker key: **[coder]** = signature/def/structure/import (lean-coder); **[prover]** = proof
body (lean-prover). **scaffold-only** = may carry marked `sorry`/be a `Prop` field;
**must-prove** = sorry-free target for THIS milestone.

### Tier A — the constructed Schwartz div-free building block (axiom-free, must-prove)

- **A1 `curlSchwartz` [coder]** — must-prove (def, no proof obligation beyond typechecking).
  `noncomputable def curlSchwartz (ψ : Fin 3 → SchwartzMap Domain3 ℝ) : Fin 3 → SchwartzMap Domain3 ℝ`
  with `(curlSchwartz ψ) i = ∂_{a(i)} (ψ (b i)) − ∂_{b(i)} (ψ (a i))` for the cyclic triple,
  each summand `lineDerivOpCLM ℝ 𝓢 (EuclideanSpace.single _ 1) (ψ _)`. **Deps:** none (mathlib).

- **A2 `curlSchwartzL2` [coder]** — must-prove (def).
  `noncomputable def curlSchwartzL2 (ψ : Fin 3 → SchwartzMap Domain3 ℝ) : L2VF_R3` — the
  L²(ℝ³;ℝ³) vector field whose `j`-th component is `(curlSchwartz ψ j).toLp 2 volume`.
  Built so that `L2VF_projComponent_R3 j (curlSchwartzL2 ψ) = (curlSchwartz ψ j).toLp …`
  holds definitionally or by a one-line lemma A2'. **Deps:** A1.
  *Risk H1 (medium):* assembling a vector `L2VF_R3` from three scalar `Lp ℝ 2` components is
  the inverse of `L2VF_projComponent_R3`. Verify the assembling map exists / is constructible
  (e.g. via `MeasureTheory.Lp` of `EuclideanSpace` from components, or sum of single-component
  embeddings). If no clean inverse exists in mathlib, lean-coder adds a small
  `L2VF_ofComponents` helper def + its `projComponent` round-trip lemma. Flag to orchestrator.

- **A3 `curlSchwartz_isSchwartz` [prover]** — must-prove. Witnesses the `e_schwartz`-shape
  fact for `curlSchwartzL2 ψ`: `∃ φ : Fin 3 → 𝓢, ∀ j, L2VF_projComponent_R3 j (curlSchwartzL2 ψ)
  = (φ j).toLp 2 volume`. Proof: take `φ = curlSchwartz ψ`, use A2'. **Deps:** A1,A2.

- **A4 `curlSchwartzL2_mem_sigma` [prover]** — must-prove. `curlSchwartzL2 ψ ∈ L2Sigma_R3`.
  Proof: unfold `L2Sigma_R3 = ⨅ φ, ker(divTestFunctional φ)`; for each test `φ` show the
  weak-div pairing vanishes. Mathematically `∑_j ∫ (curl ψ)_j ∂_j φ = ∫ (div curl ψ) φ = 0`
  by Clairaut (mixed partials of Schwartz commute) + integration by parts (Schwartz decay).
  **Deps:** A1,A2. *Risk H2 (high effort, but axiom-free):* this is a genuine
  integration-by-parts + Clairaut computation on Schwartz functions. mathlib has
  `lineDeriv`/`fderiv` commutation (`Schwartz` is smooth) and Schwartz integration-by-parts
  (`SchwartzMap.integral_pderiv*` / `integral_lineDeriv_smul` family — lean-coder to confirm
  exact names). Decompose into small lemmas: (a) the weak pairing equals minus the integral
  of `φ · div(curl ψ)`; (b) `div(curl ψ) = 0` pointwise. Keep each ≤ ~30 lines.

### Tier B — countability via separability (axiom-free, must-prove)

- **B1 `instSeparableSpace_L2VF_R3` [coder]** — scaffold/instance, must-prove (instance, no
  body beyond `inferInstance`). Confirms `SeparableSpace L2VF_R3` (from
  `Lp.SecondCountableTopology` + `SecondCountableTopology → SeparableSpace`). **Deps:** none.

- **B2 `exists_denseSeq_curlSchwartz` [prover]** — must-prove. From SDF-1 (`CurlSchwartzDense`)
  + separability, produce a SINGLE sequence `e : ℕ → L2VF_R3` of curl-fields whose prefix
  spans are dense in `L²_σ`. Strategy: the set `S := Set.range curlSchwartzL2` has
  `closure(span S) ⊇ L²_σ` by hypothesis; `span S` is separable (subspace of separable
  L2VF_R3); pick a countable dense `ℕ`-indexed subset of `S`-combinations, OR more simply
  enumerate a countable dense subset of `span S` and note each lies in a finite prefix.
  **Deps:** A2, B1, the SDF-1 hypothesis. *Risk H3 (medium):* turning "closure of span of an
  uncountable family ⊇ L²_σ" into "closure of ⨆ prefix-spans of an ℕ-enumeration ⊇ L²_σ" is
  the separability-thinning step. mathlib `exists_dense_seq` gives a dense ℕ-sequence of the
  separable space `(span S).topologicalClosure`; each point is a finite combination of
  finitely many `curlSchwartzL2 ψ`'s, so flatten the (finite-set-indexed) generators into one
  ℕ-enumeration. Provide as 2–3 small lemmas. This is bookkeeping, not analysis — feasible.

### Tier C — the deliverable (must-prove, MODULO the SDF input)

- **C1 `schwartzGalerkinBasis_of_curlDense` [prover]** — must-prove (the real deliverable,
  parameterized by the isolated hypothesis).
  `theorem schwartzGalerkinBasis_of_curlDense (h : CurlSchwartzDense) : Nonempty SchwartzGalerkinBasis`
  Assemble: `e` from B2; `e_schwartz` from A3; `e_mem_sigma` from A4; `dense_span` from B2 +
  `h`. **Deps:** A3, A4, B2. This is the honest, axiom-free-modulo-`h` headline.

- **C2 `nonempty_schwartzGalerkinBasis` [coder/prover]** — **scaffold-only THIS milestone.**
  `theorem nonempty_schwartzGalerkinBasis : Nonempty SchwartzGalerkinBasis`
  Proof body: `schwartzGalerkinBasis_of_curlDense curlSchwartzDense_holds` where
  `curlSchwartzDense_holds : CurlSchwartzDense` is the ONE remaining gap. Because pillar (4)
  is not in mathlib, `curlSchwartzDense_holds` is **either** a marked
  `axiom curlSchwartzDense_holds : CurlSchwartzDense  -- ALLOW_AXIOM: Helmholtz/Weyl density,
  not in mathlib (see helmholtz-density.md §4)` **or** `nonempty_schwartzGalerkinBasis` itself
  carries `sorry -- ALLOW_SORRY: depends on CurlSchwartzDense (Helmholtz density frontier)`.
  **Orchestrator decides axiom-vs-sorry at gate** (axiom is preferred: it is auditable by
  `#print axioms` and matches the project's existing axiom-frontier discipline). Either way
  `C1` (the conditional theorem) is the genuine must-prove deliverable; `C2` only exposes the
  remaining frontier honestly.

### Assembly / DAG summary

A1 → A2 → {A3, A4}; B1 → B2 (also needs A2 + SDF input); {A3, A4, B2} → C1 → C2.

---

## Assumptions to package as marked `axiom`s (the deferred result)

ONE, and only one, and only if the orchestrator picks the axiom route for C2:

```
axiom curlSchwartzDense_holds : CurlSchwartzDense
-- ALLOW_AXIOM: density of curls of Schwartz vector potentials in L²_σ(ℝ³) (Helmholtz/Weyl
-- lemma). NOT in mathlib; requires Helmholtz decomposition or Fourier-multiplier Leray
-- projection. Strictly thinner than P5's bundled `dense_span` hypothesis: a single scalar
-- density Prop, with the Schwartz + div-free witnesses PROVED (A3/A4), not assumed.
```
Record it in the file's assumptions section per Hard rule 5. Everything else (A1–A4, B1–B2,
C1) is must-prove, sorry-free, axiom-free. `CurlSchwartzDense` itself is a `def : Prop`
(scaffold-of-interface, no proof obligation), NOT an axiom.

**Net frontier change vs. status quo:** the current `axiom r3GalerkinScheme_exists` (fat
6-field structure) is replaced (at the later capstone) by this one thin scalar density axiom
plus proved construction. This milestone DELIVERS the proved construction (C1) and the thin
axiom statement (the SDF Prop), so the capstone becomes mechanical.

---

## Codex review points (`/codex:adversarial-review --effort xhigh`, BEFORE proofs)

- **C-A (curl is genuinely Schwartz — the central no-smuggle check).** Review A1/A2/A3:
  confirm `curlSchwartz ψ` is a HONEST `SchwartzMap` built from `lineDerivOpCLM` (Schwartz
  derivatives stay Schwartz), and that `e_schwartz` is satisfied by these REAL Schwartz
  components — NOT by Leray-projecting a Schwartz field (which would not stay Schwartz). This
  is the load-bearing honesty point flagged in the task.
- **C-B (div-free is proved, not assumed).** Review A4: confirm `curlSchwartzL2 ψ ∈ L2Sigma_R3`
  is an actual integration-by-parts + Clairaut proof, with no analytic claim hidden in a name.
- **C-C (the isolated input is minimal and honest).** Review `CurlSchwartzDense` (SDF-1):
  confirm it is the SMALLEST honest survivor (a single `Submodule` density inequality), that
  it does not re-bundle the Schwartz/div-free facts already proved, and that it is strictly
  thinner than P5's `dense_span`. Reject SDF-2 if it smuggles non-Schwartz fields.
- **C-D (separability thinning is sound).** Review B2/C1: confirm the ℕ-enumeration of
  prefix-spans faithfully yields `dense_span` from `CurlSchwartzDense` (no totality overclaim,
  no off-by-prefix error).
- **C-E (C2 frontier exposure).** Confirm the axiom-vs-sorry choice for
  `nonempty_schwartzGalerkinBasis` honestly exposes pillar (4) and does not overclaim an
  axiom-free unconditional result.

---

## Definition of done

- New file `LerayHopf/R3/SchwartzDivFreeBasis.lean` compiles (`lake build` green);
  `scripts/agent-preflight.sh` green.
- **Must-prove, sorry-free, axiom-free:** A1, A2 (+ A2' round-trip), A3, A4, B1, B2, and the
  conditional deliverable **C1 `schwartzGalerkinBasis_of_curlDense`**.
  `#print axioms schwartzGalerkinBasis_of_curlDense` → only `[propext, Classical.choice,
  Quot.sound]` (it must NOT depend on `curlSchwartzDense_holds`).
- **Scaffold-only (frontier-exposing):** `CurlSchwartzDense` (def), and C2
  `nonempty_schwartzGalerkinBasis` carrying exactly ONE marked axiom
  (`curlSchwartzDense_holds`) OR one marked `sorry`, per orchestrator decision at gate.
  No OTHER axiom/opaque/sorry anywhere in the file.
- `SolutionInterfaces.lean` and all other existing files UNCHANGED (confirmed by git diff).
- Codex `/codex:adversarial-review --effort xhigh` → approve on C-A…C-E before proof work.
- Report records: the curl-density (4) frontier as the single survivor, and that the capstone
  (wiring `r3GalerkinScheme_exists` through C1 + P5's `nonempty_r3GalerkinScheme_of_basis`)
  is the deferred sequential next PR.

---

## Risks / gating notes (summary)

- **H1 (medium):** assembling `L2VF_R3` from three scalar `Lp` components (inverse of
  `L2VF_projComponent_R3`). May need a small `L2VF_ofComponents` helper + round-trip lemma.
- **H2 (high effort, axiom-free):** A4's `div(curl)=0` weak-pairing — genuine Schwartz IBP +
  Clairaut. Decompose into small lemmas; confirm exact mathlib IBP lemma names first.
- **H3 (medium, bookkeeping):** B2 separability-thinning of an uncountable curl family to one
  ℕ-prefix-span enumeration. mathlib `exists_dense_seq` + finite-combination flattening.
- **H4 (the blocker, isolated):** pillar (4) curl/Helmholtz density — NOT in mathlib, carried
  as the single thin hypothesis `CurlSchwartzDense`. Not dischargeable axiom-free today.

## First task to hand to lean-coder

Land `LerayHopf/R3/SchwartzDivFreeBasis.lean` with imports, namespace/opens, the def
`CurlSchwartzDense` (SDF-1), defs **A1 `curlSchwartz`** and **A2 `curlSchwartzL2`** (+ any
`L2VF_ofComponents` helper H1 needs), instance **B1**, and the STATEMENTS of A2', A3, A4, B2,
C1, C2 with each proof body a marked `sorry -- ALLOW_SORRY: helmholtz-density lean-prover
target` so the file compiles. Then hand to Codex (review points C-A…C-E), then to lean-prover
in order A2' → A3 → A4 → B2 → C1, and finally resolve C2 per the orchestrator's
axiom-vs-sorry decision.
