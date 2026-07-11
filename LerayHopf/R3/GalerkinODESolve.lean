import LerayHopf.R3.GalerkinODEExistence
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.ODE.ExistUnique  -- issue #111 PR-3: the pinned mathlib now has this
  -- file (it did not when the local wrappers below were written); it directly provides
  -- IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt,
  -- ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt, and
  -- ODE_solution_unique_of_mem_Icc_{right,left,''} with identical statements.
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-!
# Forward-global existence of the finite-dim Galerkin ODE on ℝ³ (Pillar E, R-global)

**Milestone:** `findim-global-ode` (Pillar E — the last frontier of milestone E).

This file **constructs** a term `Nonempty (FinDimGlobalODE B F ν u₀ n)` — UNCONDITIONALLY,
discharging the residual R-global hypothesis isolated in `GalerkinODEExistence.lean`. Combined
with the already-proved `galerkinODEInput_of_basis`, the Galerkin ODE solution becomes
unconditional over the concrete scheme `schemeOfBasis B`.

## HONEST scope (forward time)

The deliverable proves **FORWARD-time global existence** of the autonomous finite-dim Galerkin
ODE `c' = G_n(c)` on `V_n := galerkinSpan B n`:

* the vector field `G_n := galerkinODE_vectorField B F ν n` is `C¹` (C1);
* along any local solution the energy `½‖c t‖²` is non-increasing (the dissipation identity
  `d/dt ½‖c‖² = −ν·viscousFormSq_R3 1 (c t) ≤ 0`, A1/A2), giving the forward a-priori bound
  `‖c t‖ ≤ ‖c 0‖` (A3);
* forward-global existence follows by tiling/gluing (G1).

This is **exactly** what `FinDimGlobalODE` now requires: after the forward-time refactor of that
structure (`c_hasDeriv`/`ode` quantified `∀ t, 0 ≤ t →`), the deliverable D is constructible from
G1 with no residual hypothesis. The two-sided `∀ t : ℝ` requirement no longer exists, so there is
**no backward-time smuggling**: backward-time confinement (which the energy bound does NOT supply,
see `docs/scratch/findim-global-ode.md` §1.4) is simply not needed.

## Structure (issue #112 PR-B: witness + bridge + corollaries over `LerayHopf.Galerkin`)

`R3/GalerkinODEExistence.lean` supplies `r3FieldForms B F n : Galerkin.FieldForms (galerkinSpan B n)`
(the generic-layer witness packaging `R3NSForms.b` and `stokesTestPairing_R3`) and the equality
bridge `galerkinODE_vectorField_eq_generic` (the concrete `galerkinODE_vectorField` equals
`(r3FieldForms B F n).vectorField ν`, proved by `ext_inner_right` + both specs). Every theorem in
this file — C1 (`galerkinODE_vectorField_contDiff`), A1 (`galerkinField_inner_self_nonpos`), A2
(`energy_hasDerivAt_of_localSolution`), A3 (`norm_le_of_forwardSolution`), the G1 helpers
(`galerkinField_uniform_local_time`, `galerkinField_solution_agree`), and G1 itself
(`forwardGlobalSolution_exists`) — is now a corollary of that bridge composed with the generic
`LerayHopf.Galerkin.{DissipativeODE,QuadraticField}` layer, deriving its content from
`Galerkin.FieldForms`'s theorems / `Galerkin.uniform_local_time` / `Galerkin.solution_agree` /
`Galerkin.coe_hasDerivAt` rather than a locally-duplicated CLM tower or tiling/gluing proof. The
local CLM tower and the `solve_hasDerivAt_ambient`/`solve_exists_on_step` tiling helpers that
used to carry this content directly were deleted as dead code once the corollaries landed
(deduplicated against the generic layer, which is the whole point of the `Galerkin.FieldForms`
refactor). All statements are unchanged — this is a proof-route change, not a statement change.

## DAG (no cycle)

`SolutionInterfaces → GalerkinODE → GalerkinODEExistence → GalerkinODESolve [THIS FILE]` and
`GalerkinScheme → GalerkinODEExistence`. This file is imported by no other `LerayHopf` module
(one-directional DAG, like the existing siblings); root `LerayHopf.lean` adds it after the
`import LerayHopf.R3.GalerkinODEExistence` line (deferred — done by the root consolidation step).

## Assumptions / axioms

**Zero** new `axiom`/`opaque`/`constant`/`unsafe`. **Zero** `sorry` in this file (all of A1–A3,
C1, and G1 are fully proved corollaries of the generic layer).
-/

namespace LerayHopf

open MeasureTheory Metric Set
open MeasureTheory FourierTransform
open scoped Topology InnerProductSpace FourierTransform SchwartzMap NNReal

/-! ## C1 — the Galerkin field is `C¹` on the finite-dim `V_n` (issue #112 PR-B: now a corollary
of the generic `Galerkin.FieldForms.vectorField_contDiff` via `galerkinODE_vectorField_eq_generic`;
the local CLM tower `rieszSymmCLM`/`bInner`/`bMid`/`bOut`/`stokesInner`/`stokesInner_add`/
`stokesInner_smul`/`stokesOut`/`galerkinODE_bilinearPart`/`galerkinODE_linearPart`/
`galerkinODE_vectorField_eq_parts` was deleted as dead code, deduplicated against
`LerayHopf/Galerkin/QuadraticField.lean`). -/

/-- **C1 (the enabler, MUST-PROVE).** The Galerkin field `G_n` is `C¹` on the finite-dim `V_n`. -/
theorem galerkinODE_vectorField_contDiff
    (B : SchwartzGalerkinBasis) (F : R3NSForms (schemeOfBasis B)) (ν : ℝ) (n : ℕ) :
    ContDiff ℝ 1 (galerkinODE_vectorField B F ν n) := by
  rw [galerkinODE_vectorField_eq_generic]
  exact (r3FieldForms B F n).vectorField_contDiff ν

/-! ## A1 — the dissipation identity at a point -/

/-- **A1 (MUST-PROVE).** `⟪v, G_n v⟫ = −ν · viscousFormSq_R3 1 v ≤ 0` for `v ∈ V_n` (the
dissipation identity at a point), from R2 + `b_self_zero` + `stokesTestPairing_R3_diag`.

Proof sketch: apply `galerkinODE_vectorField_spec B F ν n v v` (testing `G_n v` against `v`),
then `R3NSForms.b_self_zero` kills the `b`-term and `stokesTestPairing_R3_diag` turns the stokes
term into `viscousFormSq_R3 1 v`; the result `−ν·viscousFormSq_R3 1 v ≤ 0` follows from
`viscousFormSq_R3_nonneg` and `mul_nonneg hν.le`. (Use `real_inner_comm` to align slots with R2.) -/
theorem galerkinField_inner_self_nonpos
    (B : SchwartzGalerkinBasis) (F : R3NSForms (schemeOfBasis B)) (ν : ℝ) (n : ℕ) (hν : 0 < ν)
    (v : galerkinSpan B n) :
    inner (𝕜 := ℝ) (v : L2VF_R3) (galerkinODE_vectorField B F ν n v : L2VF_R3) ≤ 0 := by
  rw [← Submodule.coe_inner, galerkinODE_vectorField_eq_generic]
  exact (r3FieldForms B F n).inner_self_vectorField_nonpos hν v

/-- Reflect an ambient `HasDerivAt` of a `V_n`-curve back to the intrinsic one — the reverse of
`Galerkin.coe_hasDerivAt`, via the orthogonal-projection retraction `orthogonalProjectionOnto`
(a continuous linear left inverse of the subspace inclusion). Lets the ambient-curve energy/
a-priori corollaries below feed the generic intrinsic-curve `Galerkin` lemmas. -/
private theorem hasDerivAt_intrinsic_of_coe (B : SchwartzGalerkinBasis) (n : ℕ)
    (c : ℝ → galerkinSpan B n) (v : galerkinSpan B n) (t : ℝ)
    (h : HasDerivAt (fun s => (c s : L2VF_R3)) (v : L2VF_R3) t) :
    HasDerivAt c v t := by
  have hcomp := ((galerkinSpan B n).orthogonalProjectionOnto).hasFDerivAt.comp_hasDerivAt t h
  simpa [Function.comp_def] using hcomp

/-! ## A2 — the local energy identity (forward) -/

/-- **A2 (MUST-PROVE).** Along ANY (local) solution `c` of `c' = G_n(c)` (here `c : ℝ → V_n` with
`HasDerivAt` at `t` into the ambient `L2VF_R3`), the energy `½‖c t‖²` has derivative
`−ν·viscousFormSq_R3 1 (c t) ≤ 0`. Local analogue of `galerkin_energy_identity`.

Proof sketch (mirror `galerkin_energy_identity`, `GalerkinODE.lean:185`, but local): rewrite
`½‖c s‖²` as `½⟪c s, c s⟫` via `real_inner_self_eq_norm_sq`; differentiate via `hc.inner ℝ hc`
giving `½(⟪c t, c'⟫ + ⟪c', c t⟫)`; with `c' = G_n (c t)`, `real_inner_comm` + A1's exact-value
form (`⟪c t, G_n (c t)⟫ = −ν·viscousFormSq_R3 1 (c t)`) collapse it to
`−ν·viscousFormSq_R3 1 (c t)`. -/
theorem energy_hasDerivAt_of_localSolution
    (B : SchwartzGalerkinBasis) (F : R3NSForms (schemeOfBasis B)) (ν : ℝ) (n : ℕ)
    (c : ℝ → galerkinSpan B n) (t : ℝ)
    (hc : HasDerivAt (fun s => (c s : L2VF_R3))
      (galerkinODE_vectorField B F ν n (c t) : L2VF_R3) t) :
    HasDerivAt (fun s => (1 / 2 : ℝ) * ‖(c s : L2VF_R3)‖ ^ 2)
      (- ν * viscousFormSq_R3 1 (c t : L2VF_R3)) t := by
  have hc' : HasDerivAt c ((r3FieldForms B F n).vectorField ν (c t)) t := by
    rw [← galerkinODE_vectorField_eq_generic]
    exact hasDerivAt_intrinsic_of_coe B n c _ t hc
  have hgen := (r3FieldForms B F n).energy_hasDerivAt ν c t hc'
  have hval : -((ν : ℝ) * (r3FieldForms B F n).sV (c t) (c t))
      = - ν * viscousFormSq_R3 1 (c t : L2VF_R3) := by
    show -((ν : ℝ) * stokesTestPairing_R3 (c t : L2VF_R3) (c t : L2VF_R3))
      = - ν * viscousFormSq_R3 1 (c t : L2VF_R3)
    rw [stokesTestPairing_R3_diag]; ring
  have hfun : (fun s => (1 / 2 : ℝ) * ‖c s‖ ^ 2)
      = fun s => (1 / 2 : ℝ) * ‖(c s : L2VF_R3)‖ ^ 2 := by
    funext s; rw [Submodule.norm_coe]
  rw [hval, hfun] at hgen
  exact hgen

/-! ## A3 — the forward a-priori energy bound -/

/-- **A3 (MUST-PROVE).** Any forward local solution on `[0, T]` stays in the ball
`‖c t‖ ≤ ‖c 0‖`.

Proof sketch: from A2, `t ↦ ½‖c t‖²` has nonpositive derivative `−ν·viscousFormSq_R3 1 (c t)`
on `Icc 0 T` (`viscousFormSq_R3_nonneg`, `mul_nonneg hν.le`), hence is `AntitoneOn (Icc 0 T)`
(`Convex`/`MeanValue` antitone-from-nonpositive-derivative); so `½‖c t‖² ≤ ½‖c 0‖²` for
`t ∈ Icc 0 T`, giving `‖c t‖ ≤ ‖c 0‖` after clearing the `½` and taking square roots
(`sq_le_sq'`/`abs_le_abs` + `norm_nonneg`). -/
theorem norm_le_of_forwardSolution
    (B : SchwartzGalerkinBasis) (F : R3NSForms (schemeOfBasis B)) (ν : ℝ) (n : ℕ) (hν : 0 < ν)
    (c : ℝ → galerkinSpan B n) {T : ℝ} (hT : 0 ≤ T)
    (hsol : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt (fun s => (c s : L2VF_R3))
      (galerkinODE_vectorField B F ν n (c t) : L2VF_R3) t) :
    ∀ t ∈ Icc (0 : ℝ) T, ‖(c t : L2VF_R3)‖ ≤ ‖(c 0 : L2VF_R3)‖ := by
  have hdiss : ∀ w : galerkinSpan B n,
      inner (𝕜 := ℝ) w ((r3FieldForms B F n).vectorField ν w) ≤ 0 :=
    fun w => (r3FieldForms B F n).inner_self_vectorField_nonpos hν w
  have hsol' : ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivAt c ((r3FieldForms B F n).vectorField ν (c t)) t := by
    intro t ht
    rw [← galerkinODE_vectorField_eq_generic]
    exact hasDerivAt_intrinsic_of_coe B n c _ t (hsol t ht)
  intro t ht
  have hbound := Galerkin.norm_le_of_forwardSolution_of_dissipative
    ((r3FieldForms B F n).vectorField ν) hdiss c hT hsol' t ht
  rw [Submodule.norm_coe, Submodule.norm_coe]
  exact hbound

/-! ## G1 — forward-global existence by tiling/continuation (the core)

The largest single proof. Pre-factored into helper statements: a uniform local-existence time
on the a-priori ball, a single-step extension, and splice-agreement of overlapping local
solutions.
-/

/-- **Helper (G1, uniform-`δ`).** From C1 (the field is `C¹` on `V_n`) and compactness of the
a-priori ball `closedBall (0 : V_n) R`, there is a single uniform local-existence time `δ > 0`
valid from every center in the ball: for each `x₀ ∈ closedBall 0 R` there is a local solution on
`(t₀ − δ, t₀ + δ)` starting at `x₀` at `t₀`, for every `t₀` (autonomy ⟹ time-uniform).

Proof sketch: apply `ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt`
(uniform `ε` over a ball around each point) at each `x₀`, cover the compact `closedBall 0 R` by
finitely many such balls (`isCompact_closedBall`), and take `δ := min` of the finitely many `ε`s.
The field's `ContDiffAt` at every point is `galerkinODE_vectorField_contDiff …|>.contDiffAt`. -/
theorem galerkinField_uniform_local_time
    (B : SchwartzGalerkinBasis) (F : R3NSForms (schemeOfBasis B)) (ν : ℝ) (n : ℕ) (R : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x₀ ∈ closedBall (0 : galerkinSpan B n) R, ∀ t₀ : ℝ,
      ∃ α : ℝ → galerkinSpan B n, α t₀ = x₀ ∧
        ∀ t ∈ Ioo (t₀ - δ) (t₀ + δ),
          HasDerivAt α (galerkinODE_vectorField B F ν n (α t)) t :=
  Galerkin.uniform_local_time (galerkinODE_vectorField B F ν n)
    (galerkinODE_vectorField_contDiff B F ν n) R

/-- **Helper (G1, splice-agreement).** Two local solutions of the autonomous field on overlapping
closed intervals that agree at one common point agree on the whole overlap.

Proof sketch: local Lipschitz of `G_n` on the relevant ball (from C1 /
`ContDiff.lipschitzOnWith`) feeds `ODE_solution_unique_of_mem_Icc`, giving uniqueness on the
overlap, so the two pieces coincide there. -/
theorem galerkinField_solution_agree
    (B : SchwartzGalerkinBasis) (F : R3NSForms (schemeOfBasis B)) (ν : ℝ) (n : ℕ)
    (α β : ℝ → galerkinSpan B n) {a b t₀ : ℝ} (hab : a ≤ b) (ht₀ : t₀ ∈ Icc a b)
    (hαβ : α t₀ = β t₀)
    (hα : ∀ t ∈ Icc a b, HasDerivAt α (galerkinODE_vectorField B F ν n (α t)) t)
    (hβ : ∀ t ∈ Icc a b, HasDerivAt β (galerkinODE_vectorField B F ν n (β t)) t) :
    ∀ t ∈ Icc a b, α t = β t :=
  Galerkin.solution_agree (galerkinODE_vectorField B F ν n)
    (galerkinODE_vectorField_contDiff B F ν n) α β hab ht₀ hαβ hα hβ

/-! ### G1 — forward-global existence (issue #112 PR-B: now a corollary of the generic
`Galerkin.FieldForms.forwardGlobalSolution_exists` via `galerkinODE_vectorField_eq_generic`; the
local tiling/gluing helpers `solve_hasDerivAt_ambient`/`solve_exists_on_step` were deleted as
dead code, deduplicated against `LerayHopf/Galerkin/DissipativeODE.lean`). -/

/-- **G1 (THE core, MUST-PROVE).** Forward-global existence: there is `c : ℝ → V_n` with
`c 0 = galerkinP B n u₀ (∈ V_n)` and `∀ t ≥ 0, HasDerivAt (↑∘c) (G_n (c t)) t`. -/
theorem forwardGlobalSolution_exists
    (B : SchwartzGalerkinBasis) (F : R3NSForms (schemeOfBasis B)) (ν : ℝ) (hν : 0 < ν)
    (u₀ : L2Sigma_R3) (n : ℕ) :
    ∃ c : ℝ → galerkinSpan B n,
      (c 0 : L2VF_R3) = galerkinP B n (u₀ : L2VF_R3) ∧
      ∀ t, 0 ≤ t → HasDerivAt (fun s => (c s : L2VF_R3))
        (galerkinODE_vectorField B F ν n (c t) : L2VF_R3) t := by
  have hx₀mem : galerkinP B n (u₀ : L2VF_R3) ∈ galerkinSpan B n := galerkinP_mem_span B n _
  obtain ⟨c, hc0, hd⟩ := (r3FieldForms B F n).forwardGlobalSolution_exists hν
    (⟨galerkinP B n (u₀ : L2VF_R3), hx₀mem⟩ : galerkinSpan B n)
  refine ⟨c, ?_, fun t ht => ?_⟩
  · rw [hc0]
  · rw [galerkinODE_vectorField_eq_generic]
    exact Galerkin.coe_hasDerivAt (galerkinSpan B n) c _ t (hd t ht)


/-! ## D — the deliverable (UNCONDITIONAL) -/

/-- **Deliverable (Pillar E, R-global, MUST-PROVE).** A forward-global solution of the autonomous
finite-dim Galerkin ODE exists — discharging the last frontier behind `galerkin_ode_solution_R3`
over the concrete scheme `schemeOfBasis B`. **UNCONDITIONAL**: `FinDimGlobalODE` is now a
forward-time structure (`c_hasDeriv`/`ode` quantified `∀ t, 0 ≤ t →`), so the forward-global
solution G1 supplies it with no residual hypothesis.

Proof sketch: from `forwardGlobalSolution_exists` obtain `c` and its two properties; package the
four `FinDimGlobalODE` fields — `c := c`; `c_initial :=` G1's first conjunct;
`c_hasDeriv t ht :=` rewrite G1's explicit-derivative `HasDerivAt` through `HasDerivAt.deriv`
(`(hc t ht).hasDerivAt` form / `HasDerivAt.deriv`); `ode t ht :=` G1's second conjunct rewritten
through `HasDerivAt.deriv`. -/
theorem finDimGlobalODE_exists
    (B : SchwartzGalerkinBasis) (F : R3NSForms (schemeOfBasis B)) (ν : ℝ) (hν : 0 < ν)
    (u₀ : L2Sigma_R3) (n : ℕ) :
    Nonempty (FinDimGlobalODE B F ν u₀ n) := by
  obtain ⟨c, hc0, hd⟩ := forwardGlobalSolution_exists B F ν hν u₀ n
  refine ⟨{ c := c, c_initial := hc0, c_hasDeriv := ?_, ode := ?_ }⟩
  · intro t ht
    have hderiv : deriv (fun s => (c s : L2VF_R3)) t
        = (galerkinODE_vectorField B F ν n (c t) : L2VF_R3) := (hd t ht).deriv
    rw [hderiv]
    exact hd t ht
  · intro t ht
    exact (hd t ht).deriv

/-! ## D' — optional: unconditional Galerkin solution data over `schemeOfBasis B` -/

/-- **Optional (D', thin).** The UNCONDITIONAL Galerkin solution data over `schemeOfBasis B`,
combining the deliverable D with the existing `galerkinSolutionData_of_basis`
(`GalerkinODEExistence.lean`). Lands the headline "unconditional over `schemeOfBasis B`" payoff.

Proof sketch: feed `(finDimGlobalODE_exists B F ν hν u₀ n).some` into
`galerkinSolutionData_of_basis B F ν hν u₀ n`. -/
noncomputable def galerkinSolutionData_unconditional
    (B : SchwartzGalerkinBasis) (F : R3NSForms (schemeOfBasis B)) (ν : ℝ) (hν : 0 < ν)
    (u₀ : L2Sigma_R3) (n : ℕ) :
    GalerkinSolutionData_R3 (schemeOfBasis B) F ν u₀ n :=
  galerkinSolutionData_of_basis B F ν hν u₀ n (finDimGlobalODE_exists B F ν hν u₀ n).some

end LerayHopf
