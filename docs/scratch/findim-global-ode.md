# Task Contract — Construct `FinDimGlobalODE` axiom-free (Pillar E, R-global: finite-dim Galerkin ODE global existence)

**Milestone:** `findim-global-ode` (Pillar E — the LAST frontier of milestone E)
**Author:** lean-planner
**Status:** task contract (NO Lean edited)
**File deliverable:** `LerayHopf/R3/GalerkinODESolve.lean` (NEW, standalone sibling under `LerayHopf/R3/`)
**Runs in PARALLEL with:** another planner (Fourier foundation + pillars 1 & 2). **Stay in lane:**
this file touches ONLY finite-dim ODE existence (`FinDimGlobalODE` construction). It does NOT touch
`SchwartzGalerkinBasis`/`dense_span`, Rellich/compactness, or the Fourier API.
**Does NOT edit `AxiomaticClosure.lean`.** (Confirmed below, §0.) Root import added later by coder.

---

## 0. Goal and scope

`GalerkinODEExistence.lean` (already shipped, all proofs done) reduced `GalerkinSolutionData_R3`
over the concrete scheme `schemeOfBasis B` to a single isolated hypothesis
`FinDimGlobalODE B F ν u₀ n` (`GalerkinODEExistence.lean:445`), carrying the one residual gap:

> **R-global** — a GLOBAL (two-sided, `∀ t : Time = ℝ`) solution `c : Time → galerkinSpan B n` of the
> AUTONOMOUS finite-dim field equation `c'(t) = galerkinODE_vectorField B F ν n (c t)`, with
> `c 0 = galerkinP B n u₀`.

This milestone **constructs** a term `Nonempty (FinDimGlobalODE B F ν u₀ n)` axiom-free, discharging
R-global. Combined with the already-proved `galerkinODEInput_of_basis`
(`GalerkinODEExistence.lean:522`) and `galerkinSolutionData_R3_of_input` (`GalerkinODE.lean:307`),
this makes the Galerkin ODE solution UNCONDITIONAL over `schemeOfBasis B` — a big step toward
removing the `galerkin_ode_solution_R3` axiom (the abstraction-barrier capstone, §1.4 of
`ode-continuation.md`, is a SEPARATE later step and is NOT in scope here).

The deliverable is the headline term (one of, coder/Codex pick the exact shape):

```lean
theorem finDimGlobalODE_exists
    (B : SchwartzGalerkinBasis) (F : R3NSForms (schemeOfBasis B)) (ν : ℝ) (hν : 0 < ν)
    (u₀ : L2Sigma_R3) (n : ℕ) :
    Nonempty (FinDimGlobalODE B F ν u₀ n)
```

The new file MAY import `GalerkinODEExistence.lean` (and transitively `GalerkinODE`,
`GalerkinScheme`, `AxiomaticClosure`) to name `FinDimGlobalODE`, `galerkinODE_vectorField`,
`galerkinODE_vectorField_spec`, `galerkinSpan`, `galerkinP`, `R3NSForms`, `Time`, etc. It is NOT
imported by any of those (one-directional DAG, no cycle), exactly like the existing siblings.

> **DAG check (lean-coder):**
> `AxiomaticClosure → GalerkinODE → GalerkinODEExistence → GalerkinODESolve [THIS FILE]` and
> `GalerkinScheme → GalerkinODEExistence`. Confirm NO cycle. Add to root `LerayHopf.lean` AFTER the
> `import LerayHopf.R3.GalerkinODEExistence` line.

---

## 1. FEASIBILITY VERDICT — **feasible-with-noted-gaps** (one isolated honest sub-gap: backward-time confinement)

**Bottom line.** The hard part the parent contract feared ("no continuation theorem in mathlib")
is **circumventable** because the field `G_n` is `C¹` everywhere on the finite-dim `V_n`, and
mathlib's `ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt` gives a
**uniform local-existence time `ε` on a whole ball** (uniform over the starting point AND over the
initial time `t₀`). This is exactly the ingredient needed to TILE the time axis. The remaining
genuine subtlety is the **two-sided** requirement (`Time = ℝ`), where the energy a-priori bound
confines the solution only forward in time; the backward confinement needs a separate (small)
argument. Detailed grep-backed findings below; the recommended deliverable shape (§2) handles all
of it, with one clearly-named fallback if the backward bound proves heavy.

### 1.1 The field `G_n` is `C¹` on the finite-dim `V_n` — KEY ENABLER (re-verified)

`galerkinODE_vectorField B F ν n : V_n → V_n` (`V_n := galerkinSpan B n`) is
`(toDual ℝ V_n).symm ∘ galerkinODE_functional B F ν n`, where the functional is
`u ↦ (w ↦ −ν·stokesTestPairing_R3(u,w) − F.b (σu)(σu)(σw))`. As a map of `u`:

- `−ν·stokesTestPairing_R3(u,·)` is **linear** in `u` (R1 already proves linearity in the 2nd slot;
  symmetric reasoning / `real_inner` gives linearity in `u` too — or use the bilinear form on
  `V_n × V_n`).
- `F.b (σu)(σu)(σw)` is **quadratic** in `u` (`b_add_1`/`b_smul_1`, `b_add_2`/`b_smul_2`).

On a finite-dim space **every multilinear map is continuous/bounded** and **every continuous
multilinear (in particular bilinear) map is `ContDiff ℝ ⊤`** (`IsBoundedBilinearMap.contDiff`,
`Mathlib/Analysis/Calculus/ContDiff/Basic.lean:194`; finite-dim continuity via
`LinearMap.continuous_of_finiteDimensional`, `Mathlib/Analysis/Normed/Module/FiniteDimension.lean`).
The Riesz iso `(toDual ℝ V_n).symm` is a CLM, hence `ContinuousLinearMap.contDiff`
(`ContDiff/Basic.lean:161`). Composition/sum/diagonal of `ContDiff` maps is `ContDiff`. Therefore
**`G_n` is `ContDiff ℝ 1` (indeed `⊤`)** — axiom-free, using only the abstract `R3NSForms` algebra
(`b_add_*`, `b_smul_*`) plus finite-dimensionality of `V_n`. **No continuity hypothesis on `b` is
needed**: finite-dim auto-continuity supplies it. This is the load-bearing new lemma (C1 below).

> **Subtlety the coder must resolve cleanly (GR-quad):** to invoke `IsBoundedBilinearMap.contDiff`
> we need `G_n` expressed via a *continuous bilinear* `V_n × V_n → V_n` map plus a *continuous
> linear* `V_n → V_n` map, then `u ↦ Bil(u,u) + Lin u`. Build the bilinear/linear maps as bare
> `LinearMap`/`bilinear `MultilinearMap`/`LinearMap.toBilinForm`-style algebraic objects from the
> `R3NSForms` axioms, then upgrade to continuous via finite-dim auto-continuity
> (`LinearMap.toContinuousLinearMap`, `ContinuousMultilinearMap`/`mkContinuousOfFiniteDimensional`).
> The diagonal `u ↦ Bil(u,u)` is `ContDiff` via `Bil.contDiff.comp` with the diagonal CLM
> `u ↦ (u,u)`. If the bilinear packaging is fiddly, the alternative is `contDiff_clm_apply_iff`
> (`ContDiff/FiniteDimension.lean:51`): `G_n` is `ContDiff` iff each coordinate (testing against a
> fixed basis vector via the inner product / `toDual`) is `ContDiff`, and each coordinate is an
> explicit quadratic-in-coordinates polynomial. Pick whichever lands smaller; the bilinear route is
> preferred (fewer basis manipulations).

### 1.2 Uniform local existence time on a ball — the TILING enabler (grep-confirmed)

`Mathlib/Analysis/ODE/ExistUnique.lean:145`,
`ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt`:

```
(hf : ContDiffAt ℝ 1 f x₀) (t₀ : ℝ) :
  ∃ r > 0, ∃ ε > 0, ∀ x ∈ closedBall x₀ r, ∃ α : ℝ → E, α t₀ = x ∧
    ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), HasDerivAt α (f (α t)) t
```

Crucially `ε` is **uniform over the starting point `x ∈ closedBall x₀ r`** and (since the field is
autonomous, by translation in `t₀`) **uniform over `t₀`**. The underlying
`IsPicardLindelof.of_contDiffAt_one` (`Mathlib/Analysis/ODE/PicardLindelof.lean:675`) returns `ε, a,
r, L, K` and the Picard data **for every `t₀ : ℝ`** — exactly the autonomous uniform-time fact. This
is the piece the parent contract said "must be built from scratch"; it EXISTS in mathlib for `C¹`
autonomous fields. Combined with the a-priori bound it gives global existence by tiling.

Uniqueness for gluing: `ODE_solution_unique_of_mem_Icc` / `ODE_solution_unique_of_mem_Ioo`
(`ExistUnique.lean:252,279`) — local Lipschitz on the relevant ball (from `C¹`) gives uniqueness on
overlaps so spliced pieces agree.

### 1.3 The a-priori energy bound (forward) — REUSE the existing energy algebra

For ANY local solution `c` of `c' = G_n(c)`, the energy `E(t) = ½‖c t‖²` satisfies
`E'(t) = ⟪c t, c'(t)⟫ = ⟪c t, G_n(c t)⟫ = −ν·stokes(c t, c t) − b(c t, c t, c t)
= −ν·viscousFormSq_R3 1 (c t) ≤ 0` using `galerkinODE_vectorField_spec` (R2),
`R3NSForms.b_self_zero`, `stokesTestPairing_R3_diag` (`GalerkinODE.lean:122`), and
`viscousFormSq_R3_nonneg`. Hence `‖c t‖ ≤ ‖c 0‖ = ‖galerkinP B n u₀‖` for `t ≥ 0`: the solution
stays in the **fixed closed ball** `closedBall 0 R`, `R := ‖galerkinP B n u₀‖`, where the uniform
existence time `ε` of §1.2 applies — so forward continuation never stalls ⟹ forward-global.

The energy-identity ALGEBRA is already isolated in `GalerkinODE.lean` (E1
`galerkin_energy_identity`) but stated for a `GalerkinODEInput` (global curve). For the construction
we need the SAME identity along a LOCAL solution on an interval. **Plan:** prove a small local
variant `energy_hasDerivAt_of_localSolution` (A2 below) directly from R2 + `b_self_zero` +
`stokesTestPairing_R3_diag` (it does not need globality — only `HasDerivAt c (G_n (c t)) t` at the
point), then `antitone_of_hasDerivAt_nonpos`-style argument on the relevant interval.

### 1.4 The genuine residual subtlety — BACKWARD time (`Time = ℝ`), HONEST naming

`FinDimGlobalODE` requires `c : Time → galerkinSpan B n` with `c_hasDeriv`/`ode` for **all**
`t : Time = ℝ` (confirmed: `Basic.lean:22` `abbrev Time := ℝ`; structure fields
`GalerkinODEExistence.lean:452,456` quantify `∀ t` unrestricted). So we need a **two-sided** global
solution. Forward (`t ≥ 0`) is closed by §1.1–1.3. **Backward** (`t ≤ 0`) the energy a-priori bound
does NOT apply (energy GROWS as `t` decreases), so it does not directly confine `c` backward.

Three honest resolutions, in preference order:

- **(BWD-reflect, RECOMMENDED).** Solve the time-reversed autonomous field `−G_n` forward and splice
  at `t = 0`. The reversed field `−G_n` is also `C¹` (negation of `ContDiff` is `ContDiff`). The
  reversed energy `Ẽ(t) := ½‖c̃ t‖²` for `c̃' = −G_n(c̃)` has `Ẽ'(t) = −⟪c̃, G_n c̃⟫
  = +ν·viscousFormSq_R3 1 (c̃ t) ≥ 0`, so `Ẽ` is monotone INCREASING — which again does NOT give an
  a-priori UPPER bound forward. **So reflection alone does not close it either.** Keep reading.
- **(BWD-finite-energy, the actual closer).** The honest fact: on the finite-dim `V_n` a `C¹`
  autonomous field has a maximal solution on an OPEN interval `(α, β) ∋ 0`, and the blow-up
  alternative says if `α > −∞` then `‖c t‖ → ∞` as `t ↓ α`. **For the BACKWARD direction there is no
  a-priori bound**, so we genuinely cannot exclude finite-time backward blow-up from the energy
  estimate. This is mathematically real: Galerkin solutions need NOT be globally backward-defined.
  **Therefore a literal two-sided global curve on all of `ℝ` is NOT derivable from the a-priori
  bound.** This is the one isolated honest gap of this milestone (see verdict + §2 shapes).
- **(BWD-zero-extension / structural).** Because downstream usage of `FinDimGlobalODE.c` only ever
  reads `t ≥ 0` (energy bound `galerkin_energy_bound` takes `ht : 0 ≤ t`; `galerkin_reg_bound` takes
  `T > 0`; the Leray–Hopf solution is built on `[0,∞)`), the cleanest honest fix is to **change the
  curve's effective domain to forward time** — but that requires editing the `FinDimGlobalODE`
  structure (`∀ t` → `∀ t ≥ 0`) in `GalerkinODEExistence.lean`, which is OWNED by the
  ode-continuation deliverable and is a signature change. See §2-A note (coordinate via orchestrator
  — this is the clean long-term fix and does NOT weaken any downstream claim because nothing reads
  `t < 0`).

**Verdict:** **feasible-with-noted-gaps.** Forward-global existence is fully constructible
axiom-free (C1/A1/A2/A3 + tiling). The two-sided `∀ t : ℝ` requirement has ONE genuine residual:
backward-time confinement is not given by the energy estimate. The recommended deliverable (§2-A)
closes the whole thing by a tiny structure-signature adjustment (forward time), coordinated with the
ode-continuation owner; the no-edit fallback (§2-B) lands the forward-global construction and isolates
the backward `∀ t<0` piece as a precise named TODO / minimal sub-hypothesis. **Do NOT fabricate a
two-sided global curve from the one-sided a-priori bound (no-smuggle / Hard rule 3).**

---

## 2. Deliverable shape — choose at the Codex statement gate

### 2-A (RECOMMENDED) — forward-time structure adjustment + fully axiom-free construction

Coordinate with the orchestrator to make ONE small, claim-preserving edit to
`GalerkinODEExistence.lean`: relax `FinDimGlobalODE.c_hasDeriv`/`.ode` from `∀ t` to `∀ t, 0 ≤ t →`
(and `c : Time → V_n` unchanged, value at `t<0` irrelevant). This is NOT a weakening of any
downstream theorem: every consumer (`galerkin_energy_bound` `ht : 0 ≤ t`, `galerkin_reg_bound`
`hT : 0 < T`, `galerkinODEInput_of_globalCurve`'s `u_hasDeriv`/`u_ode` — re-check these are
forward-only after the edit) reads only `t ≥ 0`. With forward time, the construction is **fully
axiom-free** (C1/A1/A2/A3 + tiling, §3). **This is the honest, complete close of R-global.**

> Because the edit is to a structure OWNED by the ode-continuation deliverable, the orchestrator
> must sequence it: (i) lean-coder edits the two `FinDimGlobalODE` field quantifiers + re-checks the
> three downstream `∀ t`→`∀ t≥0` propagations in `galerkinODEInput_of_globalCurve`; (ii) Codex
> confirms no downstream claim weakened; (iii) THEN this file's construction lands. If the
> orchestrator declines the structure edit, fall back to 2-B.

### 2-B (fallback, NO structure edit) — forward-global construction + isolated backward sub-hypothesis

Keep `FinDimGlobalODE` as-is (`∀ t : ℝ`). Build the forward-global solution axiom-free (C1/A1/A2/A3).
For the backward `t < 0` portion, EITHER:

- splice a backward continuation as far as it exists and isolate ONLY the irreducible
  backward-global piece in a minimal named sub-hypothesis `FinDimBackwardGlobal` (a curve on
  `(−∞,0]` solving `c'=G_n(c)`), OR
- leave the `∀ t` curve's `t<0` branch carrying a precise `-- TODO: backward-global existence of the
  C¹ autonomous ODE on (−∞,0] is not implied by the forward a-priori energy bound; see
  findim-global-ode.md §1.4` and a marked `sorry -- ALLOW_SORRY:` ONLY if a clean isolation is not
  possible.

**Statements stay intact, no weakening** (Hard rule 8). 2-B ships the substantive content
(forward-global, the whole point) while being honest about the one residual.

### 2-C (NOT recommended) — assume the whole curve

Bundle the two-sided global curve as a hypothesis (i.e. re-export `FinDimGlobalODE` trivially). This
proves nothing new (R-global stays assumed) — it would defeat the milestone. Skip.

---

## 3. Declarations in dependency order (shape 2-A; 2-B identical up to the backward step)

New file `LerayHopf/R3/GalerkinODESolve.lean`.

### Imports
```
import LerayHopf.R3.GalerkinODEExistence       -- FinDimGlobalODE, galerkinODE_vectorField(_spec), schemeOfBasis
import Mathlib.Analysis.ODE.PicardLindelof     -- IsPicardLindelof.of_contDiffAt_one (uniform local time)
import Mathlib.Analysis.ODE.Gronwall           -- ODE_solution_unique* (gluing) — via ExistUnique re-export
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension  -- contDiff_clm_apply_iff (C1 fallback route)
```
`GalerkinODE`, `GalerkinScheme`, `GalerkinODEExistence` transitively supply
`stokesTestPairing_R3_diag`, `viscousFormSq_R3_nonneg`, `R3NSForms`, `galerkinSpan`, `galerkinP`,
`Time`. `ExistUnique.lean` is imported transitively by `PicardLindelof`/`Gronwall` (coder confirms
the exact module path for `ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt`
and `ODE_solution_unique_of_mem_Icc`). Justify each ODE import in-file.

### Namespace
```
namespace LerayHopf
open MeasureTheory Metric Set
open scoped Topology InnerProductSpace
```

### C1 — `galerkinODE_vectorField_contDiff` (the field is `C¹` — MUST-PROVE, lean-prover)
```
/-- The Galerkin field `G_n` is `C¹` (indeed smooth) on the finite-dim `V_n`: it is a
    quadratic-plus-linear map (Riesz-rep of a form linear+quadratic in `u`), and on a
    finite-dim space such maps are `ContDiff` (auto-continuity of multilinear maps +
    `IsBoundedBilinearMap.contDiff` + `ContinuousLinearMap.contDiff`). -/
theorem galerkinODE_vectorField_contDiff
    (B : SchwartzGalerkinBasis) (F : R3NSForms (schemeOfBasis B)) (ν : ℝ) (n : ℕ) :
    ContDiff ℝ 1 (galerkinODE_vectorField B F ν n)
```
**Deps:** R1/R2 (existing), `galerkinSpan_finiteDimensional`, `LinearMap.continuous_of_finiteDimensional`,
`IsBoundedBilinearMap.contDiff`, `ContinuousLinearMap.contDiff`, `(toDual ℝ V_n).symm` CLM-ness.
**This is the single hardest new lemma** (GR-quad, §1.1). lean-coder MAY want to split it into:
- `galerkinODE_bilinearPart` (continuous bilinear `V_n × V_n → V_n` from the `b`-quadratic) and
- `galerkinODE_linearPart` (CLM `V_n → V_n` from `−ν·stokes`),
both as lean-coder helper defs, with C1 = `(bil.diag + lin).contDiff`.

### A1 — `galerkinField_apply_inner_self` (energy derivative sign — MUST-PROVE, lean-prover)
```
/-- `⟪v, G_n v⟫ = −ν · viscousFormSq_R3 1 v ≤ 0` for `v ∈ V_n` (the dissipation identity at a
    point), from R2 + `b_self_zero` + `stokesTestPairing_R3_diag`. -/
theorem galerkinField_inner_self_nonpos
    (B F ν n) (hν : 0 < ν) (v : galerkinSpan B n) :
    inner (𝕜 := ℝ) (v : L2VF_R3) (galerkinODE_vectorField B F ν n v : L2VF_R3) ≤ 0
```
(plus the exact-value form `= −ν·viscousFormSq_R3 1 v` if convenient). **Deps:** R2
(`galerkinODE_vectorField_spec`), `R3NSForms.b_self_zero`, `stokesTestPairing_R3_diag`,
`viscousFormSq_R3_nonneg`, `real_inner_comm`.

### A2 — `energy_hasDerivAt_of_localSolution` (local energy identity — MUST-PROVE, lean-prover)
```
/-- Along ANY (local) solution `c` of `c' = G_n(c)` (here `c : ℝ → V_n` with `HasDerivAt` at `t`
    into the ambient `L2VF_R3`), the energy `½‖c t‖²` is non-increasing: its derivative is
    `−ν·viscousFormSq_R3 1 (c t) ≤ 0`. Local analogue of `galerkin_energy_identity`. -/
theorem energy_hasDerivAt_of_localSolution
    (B F ν n) (c : ℝ → galerkinSpan B n) (t : ℝ)
    (hc : HasDerivAt (fun s => (c s : L2VF_R3)) ((galerkinODE_vectorField B F ν n (c t) : L2VF_R3)) t) :
    HasDerivAt (fun s => (1/2 : ℝ) * ‖(c s : L2VF_R3)‖ ^ 2)
      (- ν * viscousFormSq_R3 1 (c t : L2VF_R3)) t
```
**Deps:** A1, `HasDerivAt.inner`, `real_inner_self_eq_norm_sq` (mirror `galerkin_energy_identity`,
`GalerkinODE.lean:176`, but local). **Reuse that proof's structure verbatim.**

### A3 — `norm_le_of_forwardSolution` (forward a-priori bound — MUST-PROVE, lean-prover)
```
/-- Any forward local solution on `[0, T]` stays in the ball `‖c t‖ ≤ ‖c 0‖`. -/
theorem norm_le_of_forwardSolution
    (B F ν n) (hν : 0 < ν) (c : ℝ → galerkinSpan B n) {T : ℝ} (hT : 0 ≤ T)
    (hsol : ∀ t ∈ Icc (0:ℝ) T, HasDerivAt (fun s => (c s : L2VF_R3))
      ((galerkinODE_vectorField B F ν n (c t) : L2VF_R3)) t) :
    ∀ t ∈ Icc (0:ℝ) T, ‖(c t : L2VF_R3)‖ ≤ ‖(c 0 : L2VF_R3)‖
```
**Deps:** A2, `antitone_of_hasDerivAt_nonpos`-on-`Icc` (or `Convex.inner_le`-style monotone from
nonpos derivative on the interval), `viscousFormSq_R3_nonneg`, `mul_nonneg hν.le`. (mathlib:
`AntitoneOn` from nonpositive within-interval derivative — `Mathlib/Analysis/Calculus/MeanValue.lean`,
already imported transitively via `GalerkinODE`.)

### G1 — `forwardGlobalSolution_exists` (TILING / continuation — MUST-PROVE, lean-prover; THE core)
```
/-- Forward-global existence: there is `c : ℝ → V_n` with `c 0 = galerkinP B n u₀ (∈ V_n)` and
    `∀ t ≥ 0, HasDerivAt (↑∘c) (G_n (c t)) t`. Built by tiling `[0,∞)` with the uniform
    local-existence time on the fixed a-priori ball. -/
theorem forwardGlobalSolution_exists
    (B F ν) (hν : 0 < ν) (u₀) (n) :
    ∃ c : ℝ → galerkinSpan B n,
      (c 0 : L2VF_R3) = galerkinP B n (u₀ : L2VF_R3) ∧
      ∀ t, 0 ≤ t → HasDerivAt (fun s => (c s : L2VF_R3))
        ((galerkinODE_vectorField B F ν n (c t) : L2VF_R3)) t
```
**Construction (the heart of the milestone):**
1. Transport `G_n` to an ambient field on `L2VF_R3` OR work intrinsically on `V_n` (preferred:
   `V_n` is a `NormedAddCommGroup`+`InnerProductSpace`+finite-dim, so it is a complete
   `NormedSpace ℝ`; run Picard-Lindelöf INSIDE `V_n` so solutions automatically stay in `V_n`, then
   transport derivatives to ambient via the CLM inclusion `V_n ↪ L2VF_R3`,
   `ContinuousLinearMap.comp_hasDerivAt`). **Recommended: intrinsic-in-`V_n`** — it dodges the
   "solution stays in `V_n`" obligation entirely.
2. From C1 (`ContDiff ℝ 1 G_n` on `V_n`), get the uniform local time:
   `ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt` applied at each
   center on the a-priori ball `closedBall (0:V_n) R`, `R := ‖galerkinP B n u₀‖`. **Subtlety:** that
   lemma's `r,ε` are tied to ONE center `x₀`; to cover the whole ball uniformly, either (a) re-center
   at each tiling step's endpoint (which lies in `closedBall 0 R` by A3) and use the lemma's "for all
   `x ∈ closedBall x₀ r`" with `x₀` = current endpoint, OR (b) cover the compact `closedBall 0 R` by
   finitely many `r`-balls and take `ε := min` of the finitely many times (compactness). **Route (a)
   is cleaner**: at step `k`, center `x₀ := c(kδ)` (in the a-priori ball), get its own `ε_{x₀}>0` and
   solve on `(kδ−ε, kδ+ε)`; but `ε_{x₀}` could shrink near the ball boundary IF `C¹` were only local
   — here `G_n` is `C¹` on ALL of `V_n`, so use route (b): one uniform `δ>0` from compactness of the
   ball, then tile with fixed step `δ`. **Recommend route (b) (compactness ⟹ single uniform `δ`).**
3. **Tiling/splicing:** define `c` piecewise on `[kδ,(k+1)δ]` by the local solution started at
   `c(kδ)`; the local solutions agree on overlaps by `ODE_solution_unique_of_mem_Icc` (Lipschitz from
   `C¹` on the ball). Assemble a single `c : ℝ → V_n` (e.g. via strong induction / `Nat.rec` on the
   step index, or a `⨆`-style maximal-solution glue). Prove `HasDerivAt` at each `t ≥ 0` by locating
   `t` in its tile.
4. The a-priori bound A3 guarantees each `c(kδ) ∈ closedBall 0 R`, so the SAME `δ` works at every
   step ⟹ the tiling reaches every `t ≥ 0` ⟹ forward-global.
**Deps:** C1, A3, the two ODE lemmas (`…Ioo_hasDerivAt`, `ODE_solution_unique_of_mem_Icc`),
`isCompact_closedBall`, CLM inclusion `V_n ↪ L2VF_R3` for ambient transport.
**This is the largest single proof; lean-coder should pre-factor helper lemmas** (uniform-`δ` lemma;
single-step extension lemma; splice-agreement lemma) so lean-prover works in small pieces (Hard rule
9 / Small-PR).

### D — `finDimGlobalODE_exists` (DELIVERABLE — MUST-PROVE, lean-prover)
```
/-- **Deliverable (Pillar E, R-global).** A global solution of the autonomous finite-dim Galerkin
    ODE exists — discharging the last frontier behind `galerkin_ode_solution_R3` over the concrete
    scheme. -/
theorem finDimGlobalODE_exists
    (B F) (ν) (hν : 0 < ν) (u₀) (n) : Nonempty (FinDimGlobalODE B F ν u₀ n)
```
**Body (shape 2-A, forward-time structure):** from G1 get `c`, package the four fields; `c_initial`
:= G1's first conjunct; `c_hasDeriv` := derive `HasDerivAt … (deriv …)` from the explicit derivative
(`HasDerivAt.deriv` round-trip) for `t ≥ 0`; `ode` := G1's second conjunct rewritten through
`HasDerivAt.deriv`. **Deps:** G1, the (2-A-adjusted) `FinDimGlobalODE` fields.
**Body (shape 2-B):** same for `t ≥ 0`; the `t < 0` branch carries the isolated backward
hypothesis / precise `-- TODO` per §1.4 / §2-B.

### Optional D' — unconditional Galerkin solution data (lean-prover, thin)
```
/-- Optional: the unconditional Galerkin solution data over `schemeOfBasis B`, combining D with the
    existing `galerkinSolutionData_of_basis` (`GalerkinODEExistence.lean:531`). -/
noncomputable def galerkinSolutionData_unconditional
    (B F) (ν) (hν : 0 < ν) (u₀) (n) : GalerkinSolutionData_R3 (schemeOfBasis B) F ν u₀ n :=
  galerkinSolutionData_of_basis B F ν hν u₀ n (finDimGlobalODE_exists B F ν hν u₀ n).some
```
Lands the headline "unconditional over `schemeOfBasis B`" payoff. Only after D is sorry-free.

---

## 4. lean-coder vs lean-prover split

- **lean-coder** (signatures, structure, imports, statements; bodies = marked
  `sorry -- ALLOW_SORRY: findim-global-ode lean-prover target` so the file compiles):
  - file skeleton + imports + namespace/opens + root-build entry (after
    `import LerayHopf.R3.GalerkinODEExistence`);
  - helper defs for C1 (`galerkinODE_bilinearPart`, `galerkinODE_linearPart`) and for G1
    (uniform-`δ`, single-step-extension, splice-agreement helper statements);
  - the *statements* of C1, A1, A2, A3, G1, D (+ optional D');
  - **DAG confirmation** (no cycle) and import justification comments.
  - **(2-A only)** the small `FinDimGlobalODE` quantifier edit in `GalerkinODEExistence.lean`
    (`∀ t` → `∀ t, 0 ≤ t →` on `c_hasDeriv`/`ode`) + re-checking the three downstream propagations in
    `galerkinODEInput_of_globalCurve` — sequenced by orchestrator, Codex-gated BEFORE this file.
- **lean-prover** (proof bodies only), in dependency order: **C1 → A1 → A2 → A3 → G1 → D** (→ D').

---

## 5. Assumptions / axioms

**NO new `axiom`, `opaque`, `constant`, or `unsafe`.** Zero.

- **Shape 2-A:** ZERO residual hypotheses — R-global is fully PROVED (forward time, which is all the
  structure needs after the claim-preserving quantifier edit). `#print axioms finDimGlobalODE_exists`
  → only `[propext, Classical.choice, Quot.sound]`. **This fully closes R-global.**
- **Shape 2-B:** forward-global PROVED axiom-free; the backward `t<0` piece either (i) isolated in a
  minimal named sub-hypothesis `FinDimBackwardGlobal` (a bundle, not an environment axiom — honest
  analogue of `LocalRellichInput`), or (ii) a precise `-- TODO`/marked `sorry`. Report says so
  explicitly; NO overclaim that two-sided global is proved.

**`AxiomaticClosure.lean` is NOT edited.** (2-A edits ONLY `GalerkinODEExistence.lean`'s structure
quantifiers, not the axiom block, and only with orchestrator sequencing + Codex sign-off.)

---

## 6. Codex review points (`/codex:adversarial-review --effort xhigh`)

Review **statements** before any proof is attempted:

1. **`C1` (`G_n` is `C¹`) — the enabler.** Confirm the finite-dim auto-continuity + bilinear/linear
   `ContDiff` route is SOUND and uses ONLY the abstract `R3NSForms` algebra (no smuggled continuity
   hypothesis on `b`), and that `V_n` is genuinely a complete finite-dim `NormedSpace ℝ` for the
   intrinsic Picard-Lindelöf.
2. **Tiling soundness (`G1`).** Confirm the uniform-`δ`-on-the-a-priori-ball argument is valid:
   `ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt` gives `ε` uniform
   over the ball; compactness of `closedBall 0 R` yields one `δ`; A3 keeps every tile-endpoint in the
   ball; `ODE_solution_unique_of_mem_Icc` glues. Confirm NO circular use of the a-priori bound (A3
   needs only the local solution on each tile, not the global curve).
3. **The backward-time honesty gate (§1.4) — THE central no-overclaim check.** Confirm that the
   two-sided `∀ t : ℝ` requirement is NOT silently satisfied by the forward-only a-priori bound, and
   that the chosen shape handles it honestly: 2-A by the claim-preserving forward-time quantifier
   edit (Codex must confirm NO downstream theorem reads `t<0`, so no weakening), OR 2-B by an
   isolated named sub-hypothesis / precise TODO. **Reject any "global on ℝ" claim derived from the
   one-sided bound.**
4. **(2-A only) structure-edit non-weakening.** Confirm `FinDimGlobalODE.c_hasDeriv`/`ode`
   `∀ t` → `∀ t, 0 ≤ t →` does NOT weaken `galerkinODEInput_of_globalCurve`,
   `galerkin_energy_bound`, `galerkin_reg_bound`, or any consumer (all read `t ≥ 0`). This is the
   gate that licenses the edit.
5. **Deliverable wiring (`D`/`D'`).** Confirm `finDimGlobalODE_exists` packages the four
   `FinDimGlobalODE` fields faithfully (initial value, `HasDerivAt`/`deriv` round-trip, autonomous
   `ode`), and that `galerkinSolutionData_unconditional` correctly chains through the existing
   `galerkinSolutionData_of_basis`.

---

## 7. Definition of done

- New file `LerayHopf/R3/GalerkinODESolve.lean` compiles (`lake build` green); added to root
  `LerayHopf.lean` after the `GalerkinODEExistence` import.
- **Must-prove, sorry-free:** C1, A1, A2, A3, G1, D (+ optional D').
- **Shape 2-A (RECOMMENDED, full close):** R-global PROVED axiom-free;
  `#print axioms finDimGlobalODE_exists` → `[propext, Classical.choice, Quot.sound]` only. The
  Galerkin ODE solution is now UNCONDITIONAL over `schemeOfBasis B`. The `FinDimGlobalODE`
  quantifier edit landed + Codex-confirmed non-weakening.
- **Shape 2-B (fallback):** forward-global PROVED axiom-free; backward `t<0` isolated in a minimal
  named sub-hypothesis or precise TODO; report states honestly that two-sided `∀ t:ℝ` global is NOT
  unconditionally proved (only forward-global is).
- **`AxiomaticClosure.lean` NOT edited;** no import cycle.
- **Zero new axioms / opaque / unsafe.** Only transient `ALLOW_SORRY` during coder→prover handoff.
- `#print axioms exists_lerayHopf_r3` unchanged (this file not on the closure import path).
- `bash scripts/agent-preflight.sh` green.
- Codex `/codex:adversarial-review --effort xhigh` → approve on statements (points 1–5), routed by
  orchestrator before and after proof work.
- STATUS.md row: R-global (finite-dim Galerkin ODE forward-global existence) proved axiom-free via
  `C¹`-field + uniform-time tiling; two-sided handled by 2-A (forward-time structure) or isolated by
  2-B.

---

## 8. Risks / gating notes (summary)

- **GR-quad (MEDIUM, §1.1 / C1):** packaging `G_n` as `ContDiff` via continuous bilinear+linear on
  finite-dim `V_n`. The enabling lemmas exist (`IsBoundedBilinearMap.contDiff`,
  finite-dim auto-continuity, `contDiff_clm_apply_iff`); the work is the bilinear assembly from the
  `R3NSForms` algebra. Pre-factor helper defs.
- **GR-tile (MEDIUM-HIGH, §1.2 / G1):** the splicing/continuation is hand-built but ENABLED by the
  uniform local time (`…Ioo_hasDerivAt`) + a-priori bound + uniqueness — all in mathlib. The
  parent contract's "no continuation theorem ⟹ huge" fear is **defused** for the `C¹` autonomous
  case. Still the largest proof; split into uniform-`δ`, single-step, splice-agreement helpers.
- **GR-bwd (the one genuine residual, §1.4):** two-sided `∀ t:ℝ` is NOT given by the forward energy
  bound. Resolved cleanly by 2-A (forward-time structure edit, no weakening) or isolated by 2-B. **Do
  not smuggle.** Codex gate point 3.
- **GR-intrinsic (LOW):** run Picard-Lindelöf intrinsically in `V_n` (complete finite-dim
  `NormedSpace`) to avoid the "stays in `V_n`" obligation; transport derivative to ambient
  `L2VF_R3` via the inclusion CLM. Routine.

---

## 9. First task to hand to lean-coder

Land `LerayHopf/R3/GalerkinODESolve.lean` with: imports (`GalerkinODEExistence`, `ODE.PicardLindelof`,
`ODE.Gronwall`, `ContDiff.FiniteDimension`), `namespace LerayHopf` + opens, DAG/import justification,
the helper-def stubs for C1 (`galerkinODE_bilinearPart`, `galerkinODE_linearPart`) and G1
(uniform-`δ`, single-step-extension, splice-agreement), and the *statements* of **C1, A1, A2, A3, G1,
D** (+ optional D'), each proof body `sorry -- ALLOW_SORRY: findim-global-ode lean-prover target` so
the file compiles. Add the file to root `LerayHopf.lean` after the `GalerkinODEExistence` import;
confirm no cycle. **If shape 2-A is chosen by the orchestrator,** FIRST (separately) make the
claim-preserving `FinDimGlobalODE` quantifier edit in `GalerkinODEExistence.lean` (Codex point 4)
before this file's construction. Then hand to Codex (review points 1–5), then to lean-prover for
proofs in order C1 → A1 → A2 → A3 → G1 → D.
