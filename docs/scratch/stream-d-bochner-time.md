# Stream D — Abstract Bochner–Sobolev-in-time + Aubin–Lions/Simon library (task contract)

**Planner:** lean-planner. **Status:** planning artifact only (no `.lean` edited).
**Scope source of truth:** `docs/milestone.md` (M6/M8), `docs/leray_hopf_lean_mvp_plan.md`,
`HANDOFF.md` §5–6 (pillar **P2**), and the existing axiom signatures in
`LerayHopf/AxiomaticClosure.lean` + `LerayHopf/R3/AxiomaticClosure.lean`.
**Discipline:** `lean-formalization-discipline` skill — Mathlib boundary first, honest
gap-sizing, least-abstract isolation, no over-strength / no-smuggle, standard over bespoke.

> This is the multi-month centerpiece (HANDOFF §6 estimates ~6–10 person-months for the
> full pillar). This contract decomposes it into landable stages with honest per-stage
> gap-sizes. **Do not promise a single push closes the four time-side axioms.** A realistic
> one-push target is Stages D0–D2 (definitions + the *reachable* lemmas) plus closing P2's
> open `kineticEnergy_lsc_bound` (E1) and `aubinLionsPackage_R3_of_timeCompactness` (C2)
> once D2 lands the measurable-representative primitive they are blocked on.

---

## 0. The four target axioms this stream substantiates (NOT removed this stream)

The capstone wiring (the `aubin_lions*` / `galerkin_limit_passage*` axioms in the two
`AxiomaticClosure.lean` files) is **deferred** and **untouched** here. Stream D builds the
*substantiating* abstract library in NEW files; only a later, separately-contracted
"capstone-swap" stream rewrites those four axioms into theorems applying this library.

| Axiom | File:line | Time-side content this stream must reach |
|---|---|---|
| `aubin_lions` (T³) | `AxiomaticClosure.lean:340` | Bochner-time compactness half |
| `galerkin_limit_passage` (T³) | `AxiomaticClosure.lean:394` | good representative + weak-in-time continuity + initial trace |
| `aubin_lions_R3` | `R3/AxiomaticClosure.lean:458` | Bochner-time half (spatial = P3, local) |
| `galerkin_limit_passage_R3` | `R3/AxiomaticClosure.lean:496` | good representative + trace (local form) |

**Two-domain leverage.** All four are stated over the abstract layer
(`DissipativeEvolution`, `WeakFormNS`, `r3Evolution`/`torus3Evolution`). Stream D's library
is built over an abstract **Gelfand triple** `V ↪ H ↪ V'` (`H = E.H`, `V` = the regularity
space whose squared norm is `E.reg`). Because both `torus3Evolution` and `r3Evolution` are
instances of `DissipativeEvolution`, one abstract Aubin–Lions/limit-passage theorem
discharges the time-side content on **both** domains at once. The ℝ³ spatial half stays
local (P3); only the **time** primitives are domain-neutral — which is exactly the split the
existing axioms already encode (`aubin_lions*` "covers only the Bochner-time half").

---

## 1. Mathlib boundary (pressure-tested against `.lake/packages/mathlib/`)

**Confirmed PRESENT (reuse, do not rebuild):**

- Bochner integral of Banach-valued maps; vector-valued `Lp` spaces
  (`MeasureTheory/Function/LpSpace/*`, `Integral/Bochner/*`).
- FTC-2 for `ℝ → E` valued maps: `intervalIntegral.integral_eq_sub_of_hasDerivAt`
  (already used in `EnergyEstimate.lean`).
- Bochner interval integral + `intervalIntegral.norm_integral_le_of_norm_le_const`
  (already used by P2's Steklov helpers).
- Arzelà–Ascoli: `Topology/UniformSpace/Ascoli.lean`,
  `Topology/ContinuousMap/Bounded/ArzelaAscoli.lean` (abstract; usable for the
  time-equicontinuity ⇒ uniform-compactness step, though P2 chose a direct δ-mesh).
- a.e.-extraction from L²/measure convergence: `TendstoInMeasure.exists_seq_tendsto_ae`,
  `tendstoInMeasure_of_tendsto_eLpNorm` (named in P2's E1 TODO).
- Line-derivative integration by parts: `Analysis/Calculus/LineDeriv/IntegrationByParts.lean`.
- Bochner average / `setAverage` (`Integral/Average.lean`) — for Steklov/mollification.

**Confirmed ABSENT (this is the genuinely-missing pillar — search returned nothing):**

- Any `W^{1,p}(0,T;X)` / vector-valued time-Sobolev space.
- Vector-valued **weak time derivative** (distributional `u' ∈ L^q(0,T;V')`).
- **Aubin–Lions** / **Simon's** compactness lemma (no occurrence of `Aubin`/`AubinLions`).
- Time-mollification / Steklov averaging **API** (P2 hand-rolled `steklovAvg` locally).
- Measurable-representative selection for a curve known only via space-time integral
  convergence (the exact blocker of P2's E1 and the lsc transfer).
- Weak-in-time continuity (`C_w([0,T];H)`) representative theory.

**Verdict (honest gap-size):** this is a *sub-library*, not a lemma. Mathlib gives the
scalar/Banach calculus substrate; the entire evolution-equation layer (W^{1,p}(0,T;X) →
Aubin–Lions → good representative) is missing and must be built. Full closure ≈ multi-person
months. The decomposition below isolates the *reachable* fraction.

---

## 2. Staged decomposition (abstract Bochner-time core → Aubin–Lions → two-domain wiring)

Each stage lists files, declarations (with exact intended names + informal signatures),
scaffold-only vs must-prove, gap-size, and dependency edges. **No new `axiom`** anywhere:
genuinely-missing inputs are isolated as explicit **structure/hypothesis arguments**
(the established pattern: P3 `LocalRellichInput`, P2 `TimeCompactnessInput`,
R3-d `hdiv`, P5 `dense_span`).

All files live under `LerayHopf/Bochner/` (new module dir). They depend only on
`LerayHopf/EvolutionTriple.lean`, `LerayHopf/EnergyEstimate.lean`, and mathlib — so they
are **domain-neutral** and importable by both T³ and ℝ³ capstone-swaps without cycles.

### Stage D0 — Gelfand triple + Bochner-time space definitions  *(reachable)*

**File:** `LerayHopf/Bochner/GelfandTriple.lean`

- `structure GelfandTriple` — **scaffold-only (definitions)**.
  Bundles `V H : Type*` with normed/inner-product/complete instances, a continuous dense
  embedding `ι : V →L[ℝ] H` (informally `V ↪ H` dense), and the pairing data identifying
  `H ⊆ V'`. Keep MINIMAL: only what Aubin–Lions and the energy law consume. Do **not**
  encode `divergence-free` or any NS-specific structure (No-overclaim).
  Edge: depends on nothing but mathlib.
- `def GelfandTriple.ofDissipativeEvolution (E : DissipativeEvolution) (...) : GelfandTriple`
  — **must-prove** (it is a construction, sorry-free) — `H := E.H`, `V` carved from
  `{u | E.reg u < ∞}` with norm² `= E.reg`. This is the **bridge** that makes the library
  apply to `torus3Evolution`/`r3Evolution`. Gap: medium (carving `V` as a normed subspace
  from `reg` needs `reg` to be a genuine squared seminorm; may require a refined hypothesis
  packaged as a field, not an axiom).

### Stage D1 — vector-valued time-Sobolev `W^{1,p}(0,T;X)` + weak time derivative  *(months-class core; partially reachable)*

**File:** `LerayHopf/Bochner/TimeSobolev.lean`

- `def IsWeakTimeDeriv (T : ℝ) (u v : ℝ → X) : Prop` — **scaffold-only (definition)**.
  `∀ ψ : ℝ → ℝ, C¹, supp ⊆ (0,T) → ∫₀ᵀ ψ'(t) • u t = - ∫₀ᵀ ψ(t) • v t` (Bochner
  integrals; `X` a Banach space). Mirrors `WeakFormNS`'s test-function convention exactly
  (compact support in `Ioo 0 T`), so it composes cleanly. Gap: small (definition only).
- `theorem isWeakTimeDeriv_unique` — **must-prove** — weak time derivative is a.e. unique.
  Gap: small–medium (du Bois-Reymond / fundamental lemma of calculus of variations for
  Bochner integrals; reachable from mathlib's Bochner machinery).
- `theorem hasDerivAt_isWeakTimeDeriv` — **must-prove** — a classical `HasDerivAt`
  derivative is a weak time derivative (IBP via `intervalIntegral.integral_eq_sub…`). Gap:
  small. **This is the entry point that connects the Galerkin curves' `u_hasDeriv` field to
  the abstract weak-derivative API.**
- `structure W1pTime (p q : ℝ≥0∞) (T : ℝ) (V H : ...) ` — **scaffold-only (definition)**.
  `u ∈ L^p(0,T;V)` with weak time-derivative `u' ∈ L^q(0,T;V')`. Bundle the membership
  facts as fields. Gap: medium (needs the `Lp(0,T;X)` membership predicate; mathlib's
  `MemLp`/`Lp` for Bochner is usable).
- `theorem w1pTime_continuous_in_H` — **must-prove if reached; else scaffold-only with a
  marked `sorry` + TODO** — the Lions–Magenes embedding `W^{1,p}(0,T;V) ∩ ... ↪ C([0,T];H)`
  (the **weak-in-time continuity / good representative** existence). Gap: **HEAVY / months**
  — this is the deepest single theorem and is exactly what `galerkin_limit_passage*`'s
  "weakly-continuous representative" defers. **Honest:** likely lands as scaffold-only first
  with a precise TODO; revisited after D2.

### Stage D2 — measurable representative + Steklov/time-mollification API  *(reachable; unblocks P2)*

**File:** `LerayHopf/Bochner/TimeMollification.lean`

This stage *promotes* P2's hand-rolled `steklovAvg` into a reusable, domain-neutral API and
delivers the **measurable-representative primitive** that P2's E1/C2 are blocked on.

- `def timeSteklov (X) (T : ℝ) (u : ℝ → X) (δ : ℝ) : ℝ → X` — **scaffold-only (def)** —
  `t ↦ δ⁻¹ • ∫_{t}^{t+δ} u s`. Generalizes P2's `steklovAvg`. Gap: small.
- `theorem timeSteklov_norm_le` — **must-prove** — uniform L² bound (generalizes P2's
  `steklovAvg_norm_le_u0`). Gap: small (P2 already proved the concrete case).
- `theorem timeSteklov_approx` — **must-prove** — average↔curve estimate under a time
  modulus (generalizes P2's `steklovAvg_approx`). Gap: small.
- `theorem timeSteklov_jensen_reg` — **must-prove** — Jensen bound: the viscous/regularity
  seminorm of the average ≤ the time-average of the seminorm. Gap: **medium** — this is
  P2 C2's open "step 2" (Bochner-average ↔ pointwise-form interchange). Reachable but the
  real new content of this stage.
- `theorem aeStronglyMeasurable_of_spaceTimeL2` — **must-prove if reached; this is the
  KEY PRIMITIVE** — from space-time L²(0,T;L²(B_R)) convergence of a measurable sequence,
  the limit admits a jointly `(t,x)`-measurable representative; a.e.-in-`t` subsequence
  extraction follows. Uses `TendstoInMeasure.exists_seq_tendsto_ae`. Gap: **medium–heavy** —
  this is the precise ingredient P2's E1 names as its sole blocker. **Landing this directly
  unblocks `kineticEnergy_lsc_bound`.**
- `theorem kineticEnergy_lsc_transfer` — **must-prove** — norm-lsc transfer of a uniform
  bound to the limit at a.e. time, *given* the measurable representative. Gap: medium.

### Stage D3 — abstract Aubin–Lions / Simon compactness lemma  *(heavy; the centerpiece theorem)*

**File:** `LerayHopf/Bochner/AubinLions.lean`

- `structure AubinLionsHypotheses (GT : GelfandTriple) (T) (uSeq : ℕ → ℝ → GT.H)` —
  **scaffold-only (definitions)** — packages the genuinely-required inputs as explicit
  hypotheses (NOT axioms): (i) uniform `L²(0,T;V)` bound, (ii) uniform time-equicontinuity
  modulus in `H` (the abstract form of P2's `TimeCompactnessInput`; in principle derivable
  from a uniform `W^{1,q}(0,T;V')` bound via D1, but isolated here so the lemma is usable
  before D1's heavy embedding lands), (iii) a **spatial-compactness input** `V ↪↪ H` as an
  explicit argument (discharged on T³ by `rellich_L2Sigma`, on ℝ³ by P3's local form —
  this is the no-smuggle isolation of the domain-specific half).
- `theorem aubinLions_strongL2` — **must-prove if reached; else scaffold-only + marked
  `sorry`** — under `AubinLionsHypotheses`, a subsequence converges strongly in
  `L²(0,T;H)`. Gap: **HEAVY** — the genuine Aubin–Lions/Simon argument (Steklov + spatial
  compactness + δ-mesh diagonalization). This is exactly P2's open C2 at the abstract level;
  D2's Steklov API + spatial input feed it. Realistic: first push gets the *statement* + the
  reachable sub-steps; the diagonalization assembly is the months-class residual.

### Stage D4 — two-domain wiring (substantiation, capstone deferred)  *(reachable once D3 lands)*

**Files:** `LerayHopf/Bochner/WiringTorus.lean`, `LerayHopf/Bochner/WiringR3.lean`

- `theorem aubinLions_torus3_of_library` / `aubinLions_R3_of_library` — **must-prove
  (conditional on D3 + spatial input)** — instantiate the abstract `aubinLions_strongL2` at
  `torus3Evolution`/`r3Evolution`, producing the *conclusion type* of `aubin_lions` /
  `aubin_lions_R3` (the `AubinLionsPackage*` data) from the library. **Does NOT edit
  `AxiomaticClosure.lean`** — these are standalone wiring theorems proving the axiom's
  statement; the axiom-swap is a later capstone stream. Gap: medium (mostly type-plumbing,
  given D0's bridge + D3).
- Update P2's `aubinLionsPackage_R3_of_timeCompactness` (C2) and `kineticEnergy_lsc_bound`
  (E1) to *use* D2/D3 — this **closes P2's two open `sorry`s**. (Edit lives in P2's file via
  lean-coder/prover, not here; flagged as the concrete downstream payoff.)

---

## 3. Per-stage feasibility + honest gap-size summary

| Stage | Deliverable | One-push reachable? | Gap-size |
|---|---|---|---|
| D0 | Gelfand triple defs + `ofDissipativeEvolution` bridge | **Yes** | small–medium |
| D1 defs | `IsWeakTimeDeriv`, `W1pTime`, uniqueness, `hasDerivAt_isWeakTimeDeriv` | **Yes** | small–medium |
| D1 embedding | `w1pTime_continuous_in_H` (good representative) | **No** (scaffold first) | **HEAVY / months** |
| D2 | Steklov API + Jensen + measurable-representative primitive | **Mostly** | medium–heavy |
| D3 statement | `AubinLionsHypotheses`, `aubinLions_strongL2` stmt | **Yes** | small (stmt) |
| D3 proof | full Aubin–Lions/Simon assembly | **No** | **HEAVY / months** |
| D4 | two-domain wiring theorems | Yes (after D3) | medium |
| P2 close | E1 + C2 via D2/D3 | Yes (after D2; C2 needs D3) | medium |

**Reachable in a focused push:** D0, D1-defs (+ uniqueness, `hasDerivAt`), D2 (incl. the
measurable-representative primitive ⇒ **close P2's E1**), D3-statement, D3's reusable
sub-steps. **Months-class residuals:** `w1pTime_continuous_in_H` and the full
`aubinLions_strongL2` proof (≈ the abstract C2).

---

## 4. Minimal isolated primitives (no-smuggle ledger)

These are explicit hypothesis/structure ARGUMENTS, never `axiom`s. Each speaks only about
its own input and asserts no downstream conclusion:

1. **Spatial compactness `V ↪↪ H`** — argument to `AubinLionsHypotheses`. Discharged: T³
   `rellich_L2Sigma` (proved), ℝ³ P3 `localCompactness_R3_of_ballCompact` (local). No-smuggle:
   carries no time content, no subsequence for the *time* problem, no limit curve.
2. **Uniform time-equicontinuity modulus** — abstract form of P2's `TimeCompactnessInput`.
   In-principle derivable from D1's uniform `W^{1,q}(0,T;V')` bound; isolated so D3 is usable
   before D1's embedding. No-smuggle: supplies a modulus only — no subsequence, no limit.
3. **`reg` is a genuine squared seminorm on `V`** — field of `GelfandTriple` /
   `ofDissipativeEvolution` hypotheses, needed to carve `V`. No-smuggle: a property of the
   given `reg`, not a new space.

**Forbidden (would smuggle the conclusion):** a `GoodRepresentativeInput` bundling
`WeakFormNS`/trace/energy-class as hypotheses (P2 explicitly DROPPED this — see
`AubinLionsLimitPassage.lean` header). Stream D must *derive* those, not re-assert them.

---

## 5. New file/module layout

```
LerayHopf/Bochner/
  GelfandTriple.lean        (D0)  imports: EvolutionTriple, mathlib
  TimeSobolev.lean          (D1)  imports: GelfandTriple, EnergyEstimate, mathlib
  TimeMollification.lean    (D2)  imports: GelfandTriple, mathlib (Average, LpSpace)
  AubinLions.lean           (D3)  imports: TimeSobolev, TimeMollification
  WiringTorus.lean          (D4)  imports: AubinLions, AxiomaticClosure (read-only use)
  WiringR3.lean             (D4)  imports: AubinLions, R3.AxiomaticClosure, R3.SpatialCompactness
```

Acyclic: D0 depends only on `EvolutionTriple` (which has 0 axioms and no Bochner deps);
D1–D3 are domain-neutral; only D4 touches the domain closures, and only by *importing* them
(to reference the package types), never editing them.

---

## 6. Codex adversarial-review points (orchestrator-owned; BLOCKING gate before any proof)

Every new **definition** and **theorem statement** gets `/codex:adversarial-review --effort
xhigh` *before* proofs are attempted. Priority targets (highest soundness risk):

- `IsWeakTimeDeriv` — test-function convention must match `WeakFormNS` (compact support in
  `Ioo 0 T`); verify no boundary-term smuggle, no vacuity.
- `GelfandTriple` + `ofDissipativeEvolution` — verify `V` carving does not silently force
  div-free or over-strength `reg` properties; verify density/embedding faithfulness.
- `AubinLionsHypotheses` — **the no-smuggle gate**: confirm the isolated inputs (spatial
  compactness, time modulus) do NOT encode a subsequence/limit/weak-form (P2 lesson 2 + 7).
- `aubinLions_strongL2` statement — confirm conclusion is genuine strong-L²(0,T;H)
  convergence (not pointwise-in-time, not null-set-blind in a way that lets a trivial
  representative satisfy it).
- `w1pTime_continuous_in_H` — confirm the embedding statement is the genuine
  Lions–Magenes form, not weakened.
- D4 wiring theorems — confirm they produce the *exact* `AubinLionsPackage*` conclusion type
  byte-for-byte (so a later capstone-swap is a drop-in).

Apply preemptively the 8 NL↔Lean traps from HANDOFF §8 — especially #1 (`tsum`/energy-class
non-vacuity), #2 (measure-zero representatives ⇒ existential + a.e.-link), #6 (canonical
test class), #7 (non-vacuity pin).

---

## 7. Definition of done

**Stream-D-Phase-1 (this push) DoD — all must-prove targets sorry-free:**

- D0: `GelfandTriple`, `ofDissipativeEvolution` compile; bridge instantiates at both
  `torus3Evolution` and `r3Evolution`.
- D1: `IsWeakTimeDeriv`, `W1pTime` defined; `isWeakTimeDeriv_unique`,
  `hasDerivAt_isWeakTimeDeriv` **sorry-free**.
- D2: `timeSteklov` + `timeSteklov_norm_le` + `timeSteklov_approx` +
  `timeSteklov_jensen_reg` + `aeStronglyMeasurable_of_spaceTimeL2` +
  `kineticEnergy_lsc_transfer` **sorry-free**.
- **P2 payoff:** `kineticEnergy_lsc_bound` (E1) closed sorry-free using D2.
- D3: `AubinLionsHypotheses`, `aubinLions_strongL2` **statements** compile; reachable
  sub-steps proved; the full assembly may remain a marked `sorry` with a precise TODO.
- `w1pTime_continuous_in_H` and the full `aubinLions_strongL2` proof may remain
  scaffold-only (marked `sorry` + TODO) — these are the declared months-class residuals.
- **No new `axiom`/`opaque`/`constant`.** `bash scripts/agent-preflight.sh` green.
- **No edit to either `AxiomaticClosure.lean`** (substantiation only; capstone deferred).

**Stream-D-final DoD (later streams):** `aubinLions_strongL2` + `w1pTime_continuous_in_H`
sorry-free; D4 wiring proved; a separate capstone-swap stream rewrites the four time-side
axioms into theorems applying D4.

---

## 8. Parallel-safety vs Streams A/B/C

- **No file collisions:** Stream D writes ONLY new files under `LerayHopf/Bochner/`. It does
  not edit `AxiomaticClosure.lean` (T³ or ℝ³), `TrilinearEstimate.lean` (Stream re: P1 / b),
  `GalerkinScheme.lean` (P5), or `SpatialCompactness.lean` (P3).
- **Read-only dependence:** D4 *imports* the domain closures and P3 but does not modify them;
  if A/B/C change those files' proof bodies, D4 is unaffected (it references types/statements).
- **Shared upstream (`EvolutionTriple`, `EnergyEstimate`):** Stream D only *imports* these
  (0-axiom abstract layer); it must not edit them. If another stream needs to edit them,
  coordinate via the orchestrator (low risk — they are stable).
- **P2 file (`AubinLionsLimitPassage.lean`):** Stream D's D4/P2-close step edits this file's
  two open `sorry`s. If another stream is in that file, serialize through the orchestrator.

---

## Report

- **Contract path:** `/Users/uda/Documents/research/lean-pde/docs/scratch/stream-d-bochner-time.md`
- **Ordered declaration list (dependency order):**
  1. `GelfandTriple` (scaffold) → `GelfandTriple.ofDissipativeEvolution` (must-prove)
  2. `IsWeakTimeDeriv` (scaffold) → `isWeakTimeDeriv_unique` (must-prove) →
     `hasDerivAt_isWeakTimeDeriv` (must-prove) → `W1pTime` (scaffold) →
     `w1pTime_continuous_in_H` (scaffold-first, months-class)
  3. `timeSteklov` (scaffold) → `timeSteklov_norm_le` / `timeSteklov_approx` /
     `timeSteklov_jensen_reg` (must-prove) → `aeStronglyMeasurable_of_spaceTimeL2`
     (must-prove, KEY primitive) → `kineticEnergy_lsc_transfer` (must-prove)
  4. `AubinLionsHypotheses` (scaffold) → `aubinLions_strongL2` (statement must compile;
     proof scaffold-first, months-class)
  5. `aubinLions_torus3_of_library` / `aubinLions_R3_of_library` (must-prove, after D3)
  6. P2 close: `kineticEnergy_lsc_bound` (E1), then `aubinLionsPackage_R3_of_timeCompactness` (C2)
- **Must-prove vs scaffold-only:**
  - *Must-prove this push:* `ofDissipativeEvolution`, `isWeakTimeDeriv_unique`,
    `hasDerivAt_isWeakTimeDeriv`, all D2 lemmas (incl. the measurable-representative
    primitive), `kineticEnergy_lsc_bound` (P2 E1).
  - *Scaffold-only / months-class residual:* `w1pTime_continuous_in_H`,
    `aubinLions_strongL2` proof body (statement must compile).
  - *Definitions (scaffold):* `GelfandTriple`, `IsWeakTimeDeriv`, `W1pTime`, `timeSteklov`,
    `AubinLionsHypotheses`.
- **Recommended first task for `lean-coder`:** create
  `LerayHopf/Bochner/GelfandTriple.lean` with the `GelfandTriple` structure and the
  `ofDissipativeEvolution` signature (Stage D0), then `LerayHopf/Bochner/TimeSobolev.lean`
  with `IsWeakTimeDeriv` + `W1pTime` definitions and the bare signatures of
  `isWeakTimeDeriv_unique` / `hasDerivAt_isWeakTimeDeriv`. Route all new statements to Codex
  before handing proof bodies to `lean-prover`.
- **Honest one-push estimate:** Stages D0, D1-defs, D2 (the measurable-representative
  primitive ⇒ **closing P2's E1**), and D3-statement are realistically achievable in one
  focused push. The two months-class residuals (`w1pTime_continuous_in_H`, the full
  `aubinLions_strongL2`/C2 assembly) are explicitly deferred with precise TODOs. This is the
  multi-month centerpiece; one push lands the foundation + the highest-leverage primitive,
  not the full pillar.
