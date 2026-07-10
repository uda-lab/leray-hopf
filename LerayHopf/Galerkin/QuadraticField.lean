import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import LerayHopf.Galerkin.DissipativeODE

/-!
# Generic quadratic-plus-linear Galerkin vector field (issue #112)

**Campaign:** `docs/scratch/galerkin-domain-plan.md` §3.2 (PR-A). `FieldForms` packages the
raw trilinear convection form and viscous form data on a finite-dimensional real
inner-product space `V`, deduplicating the two lane CLM towers
(`LerayHopf/R3/GalerkinODESolve.lean`'s `rieszSymmCLM`/`bInner`/`bMid`/`bOut`/`stokesInner`/
`stokesOut` and `LerayHopf/Torus/GalerkinODESolve.lean`'s byte-parallel copy) into a single
construction proved ONCE. `FieldForms.vectorField` is the Riesz representative of the
functional `w ↦ -ν * D.sV u w - D.bV u u w`, matching each lane's
`galerkinODE_functional`/`galerkinODE_vectorField` sign/`ν` convention.

Linearity is stated raw (no `ContinuousLinearMap` data in the structure fields): on the
finite-dimensional `V` every linear map is automatically continuous
(`LinearMap.toContinuousLinearMap`), so continuity does not need to be threaded through the
structure — it is recovered where needed (`vectorField_contDiff`) from finite-dimensionality
alone. PR-B (issue #112 lane rewiring) supplies the two lane witnesses `torusFieldForms` /
`r3FieldForms` and bridges each lane's existing `galerkinODE_vectorField` to
`(FieldForms).vectorField` by `ext_inner_right` + both specs (plan §3.3).

Generic-layer only: mathlib plus `LerayHopf.Galerkin.DissipativeODE` (itself mathlib-only) —
no NS/domain/Galerkin-scheme content. The `DissipativeODE` import is needed for
`forwardGlobalSolution_exists`'s frozen proof route (plan §3.2): it is derived from
`DissipativeODE.forwardGlobalSolution_exists` applied to `vectorField_contDiff` and
`inner_self_vectorField_nonpos`. Pdelib-grade is a property of the `LerayHopf/Galerkin/`
generic layer as a whole (flagged in `docs/pdelib-staging.md`) and is preserved by this
intra-layer dependency; this file is consumed by nothing in `LerayHopf` yet (PR-A has no
consumers by design; wiring happens in PR-B).

## Scaffold status

`FieldForms.vectorField` is a REAL definition (PR-A, coder pass): it is a mechanical
transcription of the lane `galerkinODE_functional`/`galerkinODE_vectorField` pair (via the
private helper `vectorFieldFunctional`, mirroring `rieszSymmCLM ∘ galerkinODE_functional`),
substituting the abstract `D.bV`/`D.sV` for each lane's concrete `F.b`/`stokesTestPairing`.
Every THEOREM body below is `sorry`-scaffolded; statements are FROZEN by the architect
(plan §3.2) and must not be altered. The CLM-tower proof route for `vectorField_contDiff` is
recorded in the plan's proof-route note and left for `lean-prover` (opus tier, PR-A).
-/

namespace LerayHopf.Galerkin

/-- Raw trilinear + viscous form data restricted to a finite-dimensional real
inner-product space, sufficient to build the Galerkin vector field.  Linearity is stated
raw (no CLM data): on the finite-dimensional `V` continuity is automatic. -/
structure FieldForms (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] where
  bV : V → V → V → ℝ
  bV_add_1 : ∀ u u' v w, bV (u + u') v w = bV u v w + bV u' v w
  bV_add_2 : ∀ u v v' w, bV u (v + v') w = bV u v w + bV u v' w
  bV_add_3 : ∀ u v w w', bV u v (w + w') = bV u v w + bV u v w'
  bV_smul_1 : ∀ (a : ℝ) u v w, bV (a • u) v w = a * bV u v w
  bV_smul_2 : ∀ (a : ℝ) u v w, bV u (a • v) w = a * bV u v w
  bV_smul_3 : ∀ (a : ℝ) u v w, bV u v (a • w) = a * bV u v w
  bV_diag_zero : ∀ v, bV v v v = 0
  sV : V → V → ℝ
  sV_symm : ∀ u w, sV u w = sV w u
  sV_add_right : ∀ u w w', sV u (w + w') = sV u w + sV u w'
  sV_smul_right : ∀ (a : ℝ) u w, sV u (a • w) = a * sV u w
  sV_diag_nonneg : ∀ v, 0 ≤ sV v v

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- The continuous linear functional on `V` whose Riesz representative is the Galerkin
vector field at `u`: `w ↦ -ν * D.sV u w - D.bV u u w`. Right-linearity in `w` is
`D.sV_add_right`/`D.sV_smul_right` (slot 2) and `D.bV_add_3`/`D.bV_smul_3` (slot 3);
continuity is automatic on the finite-dim `V`. Mirrors each lane's
`galerkinODE_functional`. -/
private noncomputable def vectorFieldFunctional (D : FieldForms V) (ν : ℝ) (u : V) :
    V →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => -ν * D.sV u w - D.bV u u w
      map_add' := by
        intro w w'
        rw [D.sV_add_right, D.bV_add_3]; ring
      map_smul' := by
        intro a w
        rw [D.sV_smul_right, D.bV_smul_3]
        simp only [RingHom.id_apply, smul_eq_mul]; ring }

@[simp] private theorem vectorFieldFunctional_apply (D : FieldForms V) (ν : ℝ) (u w : V) :
    vectorFieldFunctional D ν u w = -ν * D.sV u w - D.bV u u w := rfl

/-- Riesz representative of `w ↦ -ν * D.sV u w - D.bV u u w`. -/
noncomputable def FieldForms.vectorField (D : FieldForms V) (ν : ℝ) : V → V :=
  fun u => (InnerProductSpace.toDual ℝ V).symm (vectorFieldFunctional D ν u)

theorem FieldForms.vectorField_spec (D : FieldForms V) (ν : ℝ) (u w : V) :
    inner (𝕜 := ℝ) (D.vectorField ν u) w = -ν * D.sV u w - D.bV u u w := by
  sorry -- ALLOW_SORRY: PR-A scaffold, prover fills (issue #112)

theorem FieldForms.vectorField_contDiff (D : FieldForms V) (ν : ℝ) :
    ContDiff ℝ 1 (D.vectorField ν) := by
  sorry -- ALLOW_SORRY: PR-A scaffold, prover fills (issue #112)

theorem FieldForms.inner_self_vectorField (D : FieldForms V) (ν : ℝ) (v : V) :
    inner (𝕜 := ℝ) v (D.vectorField ν v) = -(ν * D.sV v v) := by
  sorry -- ALLOW_SORRY: PR-A scaffold, prover fills (issue #112)

theorem FieldForms.inner_self_vectorField_nonpos (D : FieldForms V) {ν : ℝ}
    (hν : 0 < ν) (v : V) : inner (𝕜 := ℝ) v (D.vectorField ν v) ≤ 0 := by
  sorry -- ALLOW_SORRY: PR-A scaffold, prover fills (issue #112)

theorem FieldForms.energy_hasDerivAt (D : FieldForms V) (ν : ℝ) (c : ℝ → V) (t : ℝ)
    (hc : HasDerivAt c (D.vectorField ν (c t)) t) :
    HasDerivAt (fun s => (1 / 2 : ℝ) * ‖c s‖ ^ 2) (-(ν * D.sV (c t) (c t))) t := by
  sorry -- ALLOW_SORRY: PR-A scaffold, prover fills (issue #112)

theorem FieldForms.forwardGlobalSolution_exists (D : FieldForms V) {ν : ℝ}
    (hν : 0 < ν) (x₀ : V) :
    ∃ c : ℝ → V, c 0 = x₀ ∧ ∀ t, 0 ≤ t → HasDerivAt c (D.vectorField ν (c t)) t := by
  sorry -- ALLOW_SORRY: PR-A scaffold, prover fills (issue #112)

end LerayHopf.Galerkin
