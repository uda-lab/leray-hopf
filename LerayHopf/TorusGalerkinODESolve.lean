import LerayHopf.TorusGalerkinScheme
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Forward-global existence of the finite-dim Galerkin ODE on 𝕋³ (issue #24)

This file **constructs** the per-`n` Galerkin solver `galerkinSolutionData_torus`, discharging the
project axiom `galerkin_ode_solution` (deleted once the capstone reroutes through this file).  It is
the torus analog of `R3/GalerkinODESolve.lean` + the R1/R2 field of `R3/GalerkinODEExistence.lean`.

The structure mirrors R3 closely (the ODE existence content is domain-agnostic):
- **B.0** stokes linearity/diagonal on `Vₙ` (torus-specific: the `∑'`-tsum collapses to a finite
  `fourierBox n` sum, cleaner than R3's Schwartz Fourier-decay integrability route);
- **B.1** R1/R2 — the Riesz vector field `G_n` and its defining identity;
- **B.2** C1 — `G_n` is `C¹` (the enabler for Picard–Lindelöf);
- **B.3** A1/A2/A3 — dissipation + the a-priori energy bound;
- **B.4** generic mathlib ODE wrappers (`{E}`-polymorphic, copied from R3);
- **B.5** G1 — `forwardGlobalSolution_exists` (the tiling/gluing core);
- **B.6** D — `galerkinSolutionData_torus` assembling all 8 `GalerkinSolutionData` fields.

HONEST scope (forward time): the deliverable proves FORWARD-time global existence (`0 ≤ t`); the
quadratic field can blow up in finite backward time, so there is no backward-time overclaim — the
energy bound confines the curve only on `t ≥ 0`, which is exactly what `GalerkinSolutionData`
requires.

**Zero** new `axiom`/`opaque`/`constant`/`unsafe`.
-/

namespace LerayHopf

open MeasureTheory Metric Set Filter Topology
open scoped Topology InnerProductSpace NNReal

/-! ## B.0 — stokes linearity/diagonal on `Vₙ`

On `Vₙ` the `∑'`-tsum collapses to a finite sum over `fourierBox n` (`coeff_zero_outside_box`),
so right-linearity is immediate from the finite-sum algebra; symmetry is pointwise (no
convergence). -/

/-- The torus stokes pairing is symmetric: `stokesTestPairing u w = stokesTestPairing w u`.

Pointwise, `Re[ûⱼ(k)·conj(ŵⱼ(k))] = Re[ŵⱼ(k)·conj(ûⱼ(k))]` (conjugate transpose), so each
summand of the `∑'`-tsum matches; no convergence is needed. -/
theorem stokesTestPairing_symm (u w : L2VF) :
    stokesTestPairing u w = stokesTestPairing w u := by
  unfold stokesTestPairing
  refine Finset.sum_congr rfl (fun j _ => ?_)
  refine tsum_congr (fun k => ?_)
  congr 1
  rw [← Complex.conj_re (mFourierCoeff3 (L2VF_projComponentC j w) k *
      (starRingEnd ℂ) (mFourierCoeff3 (L2VF_projComponentC j u) k))]
  congr 1
  rw [map_mul, Complex.conj_conj]
  ring

/-- **Stokes diagonal.** `stokesTestPairing u u = viscousFormSq 1 u` for all `u`.

Both are global `∑'`-tsums; on the diagonal `Re[ûⱼ(k)·conj(ûⱼ(k))] = ‖ûⱼ(k)‖²`, matching
`viscousFormSq 1`'s integrand termwise. -/
theorem stokesTestPairing_diag (u : L2VF) :
    stokesTestPairing u u = viscousFormSq 1 u := by
  unfold stokesTestPairing viscousFormSq
  rw [one_mul]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  refine tsum_congr (fun k => ?_)
  have hre : (mFourierCoeff3 (L2VF_projComponentC j u) k *
        (starRingEnd ℂ) (mFourierCoeff3 (L2VF_projComponentC j u) k)).re
      = ‖mFourierCoeff3 (L2VF_projComponentC j u) k‖ ^ 2 := by
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  rw [hre]

/-! ### Finite-sum truncation of `stokesTestPairing` on `Vₙ`

For `u, w ∈ Vₙ` the tsum over `k` is supported in `fourierBox n` and collapses to a finite sum;
right-additivity/homogeneity follow from the finite-sum algebra. -/

/-- Right-additivity of `stokesTestPairing` on `Vₙ`: linearity in the second slot.

On `Vₙ` the coefficient of `w` (and `w'`) vanishes outside `fourierBox n`; the bilinear
integrand is additive in `ŵ`, and the per-`k` term is additive, so the `∑'` is additive.  Proved
via `tsum`-additivity using that each tsum is actually a finite sum over the box. -/
theorem stokesTestPairing_add_right (n : ℕ) (u w w' : L2VF)
    (hu : velocityProjection_n n u = u) :
    stokesTestPairing u (w + w') = stokesTestPairing u w + stokesTestPairing u w' := by
  unfold stokesTestPairing
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  -- Each `j`-tsum is supported in `fourierBox n` because `û_j(u, k) = 0` outside the box.
  have hsupp : ∀ x : L2VF,
      (Function.support (fun k => ((2 * Real.pi) ^ 2 * (∑ i : Fin 3, (k i : ℝ) ^ 2) : ℝ) *
        (mFourierCoeff3 (L2VF_projComponentC j u) k *
          (starRingEnd ℂ) (mFourierCoeff3 (L2VF_projComponentC j x) k)).re)) ⊆ fourierBox n := by
    intro x k hk
    simp only [Function.mem_support, ne_eq] at hk
    by_contra hkbox
    rw [Finset.mem_coe] at hkbox
    exact hk (by rw [coeff_zero_outside_box n u hu j k hkbox]; simp)
  rw [← Summable.tsum_add (summable_of_ne_finset_zero (s := fourierBox n)
        (fun k hk => Function.notMem_support.mp (fun hmem => hk (hsupp w hmem))))
      (summable_of_ne_finset_zero (s := fourierBox n)
        (fun k hk => Function.notMem_support.mp (fun hmem => hk (hsupp w' hmem))))]
  refine tsum_congr (fun k => ?_)
  have hadd : mFourierCoeff3 (L2VF_projComponentC j (w + w')) k
      = mFourierCoeff3 (L2VF_projComponentC j w) k
        + mFourierCoeff3 (L2VF_projComponentC j w') k := by
    simp [mFourierCoeff3, map_add]
  rw [hadd, map_add, mul_add, Complex.add_re, mul_add]

/-- Right-homogeneity of `stokesTestPairing` on `Vₙ`. -/
theorem stokesTestPairing_smul_right (n : ℕ) (c : ℝ) (u w : L2VF)
    (_hu : velocityProjection_n n u = u) :
    stokesTestPairing u (c • w) = c * stokesTestPairing u w := by
  unfold stokesTestPairing
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← tsum_mul_left]
  refine tsum_congr (fun k => ?_)
  have hsmul : mFourierCoeff3 (L2VF_projComponentC j (c • w)) k
      = (c : ℂ) * mFourierCoeff3 (L2VF_projComponentC j w) k := by
    rw [map_smul, mFourierCoeff3, mFourierCoeff3,
      RCLike.real_smul_eq_coe_smul (K := ℂ), map_smul, lp.coeFn_smul, Pi.smul_apply,
      smul_eq_mul]
    norm_cast
  -- Pull the real scalar `c` out of the `.re` of the product.
  have hprod : (mFourierCoeff3 (L2VF_projComponentC j u) k *
        (starRingEnd ℂ) (mFourierCoeff3 (L2VF_projComponentC j (c • w)) k)).re
      = c * (mFourierCoeff3 (L2VF_projComponentC j u) k *
        (starRingEnd ℂ) (mFourierCoeff3 (L2VF_projComponentC j w) k)).re := by
    rw [hsmul, map_mul, Complex.conj_ofReal, mul_left_comm, Complex.re_ofReal_mul]
  rw [hprod]; ring

/-- Left-additivity on `Vₙ`, via right-additivity + symmetry. -/
theorem stokesTestPairing_add_left (n : ℕ) (u u' w : L2VF)
    (hw : velocityProjection_n n w = w) :
    stokesTestPairing (u + u') w = stokesTestPairing u w + stokesTestPairing u' w := by
  rw [stokesTestPairing_symm (u + u') w, stokesTestPairing_add_right n w u u' hw,
    stokesTestPairing_symm w u, stokesTestPairing_symm w u']

/-- Left-homogeneity on `Vₙ`, via right-homogeneity + symmetry. -/
theorem stokesTestPairing_smul_left (n : ℕ) (c : ℝ) (u w : L2VF)
    (hw : velocityProjection_n n w = w) :
    stokesTestPairing (c • u) w = c * stokesTestPairing u w := by
  rw [stokesTestPairing_symm (c • u) w, stokesTestPairing_smul_right n c w u hw,
    stokesTestPairing_symm w u]

/-! ## B.1 — R1/R2: the Riesz vector field `G_n` and its defining identity

Mirror of `R3/GalerkinODEExistence.lean`'s `galerkinODE_functional`/`galerkinODE_vectorField`/
`_spec`, over `velocitySpan n` and `Torus3NSForms`. -/

/-- `velocityProjection_n n` fixes any element of `velocitySpan n` (as a `velocitySpan`-coercion
hypothesis convenient for the stokes right-linearity helpers). -/
private theorem velocityP_fixes_coe (n : ℕ) (w : velocitySpan n) :
    velocityProjection_n n (w : L2VF) = (w : L2VF) := velocityP_fixes_span n w

/-- The continuous linear functional on `Vₙ := velocitySpan n` whose Riesz representative is the
Galerkin vector field: `φ w = - ν · stokesTestPairing(u, w) - F.b(σu, σu, σw)`.

Right-linearity in `w` comes from `stokesTestPairing_add_right`/`_smul_right` (valid on `Vₙ`
elements via `velocityP_fixes_span`) and `F.b_add_3`/`F.b_smul_3` (with `velocitySpanToSigma`
additive/homogeneous).  Continuity is automatic on the finite-dim `Vₙ`. -/
noncomputable def galerkinODE_functional
    (F : Torus3NSForms) (ν : ℝ) (n : ℕ) (u : velocitySpan n) : velocitySpan n →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => - ν * stokesTestPairing (u : L2VF) (w : L2VF)
        - F.b (velocitySpanToSigma n u) (velocitySpanToSigma n u) (velocitySpanToSigma n w)
      map_add' := by
        intro w w'
        rw [show ((w + w' : velocitySpan n) : L2VF) = (w : L2VF) + (w' : L2VF) from rfl,
          stokesTestPairing_add_right n (u : L2VF) (w : L2VF) (w' : L2VF) (velocityP_fixes_coe n u),
          velocitySpanToSigma_add,
          F.b_add_3 (velocitySpanToSigma n u) (velocitySpanToSigma n u)
            (velocitySpanToSigma n w) (velocitySpanToSigma n w')]
        ring
      map_smul' := by
        intro c w
        rw [show ((c • w : velocitySpan n) : L2VF) = c • (w : L2VF) from rfl,
          stokesTestPairing_smul_right n c (u : L2VF) (w : L2VF) (velocityP_fixes_coe n u),
          velocitySpanToSigma_smul,
          F.b_smul_3 c (velocitySpanToSigma n u) (velocitySpanToSigma n u)
            (velocitySpanToSigma n w)]
        simp only [RingHom.id_apply, smul_eq_mul]
        ring }

@[simp] theorem galerkinODE_functional_apply (F : Torus3NSForms) (ν : ℝ) (n : ℕ)
    (u w : velocitySpan n) :
    galerkinODE_functional F ν n u w
      = - ν * stokesTestPairing (u : L2VF) (w : L2VF)
        - F.b (velocitySpanToSigma n u) (velocitySpanToSigma n u) (velocitySpanToSigma n w) := rfl

/-- The finite-dim Galerkin vector field `G_n` on `Vₙ`: the Riesz representative of
`galerkinODE_functional`. -/
noncomputable def galerkinODE_vectorField (F : Torus3NSForms) (ν : ℝ) (n : ℕ)
    (u : velocitySpan n) : velocitySpan n :=
  (InnerProductSpace.toDual ℝ (velocitySpan n)).symm (galerkinODE_functional F ν n u)

/-- **R2 (the weak↔vector-field bridge).** Testing `G_n u` against any `w ∈ Vₙ` recovers the
functional `w ↦ -ν·stokes(u,w) - b(u,u,w)`.  Sign/`ν` conventions match `u_ode`. -/
theorem galerkinODE_vectorField_spec (F : Torus3NSForms) (ν : ℝ) (n : ℕ)
    (u w : velocitySpan n) :
    inner (𝕜 := ℝ) (galerkinODE_vectorField F ν n u : L2VF) (w : L2VF)
      = - ν * stokesTestPairing (u : L2VF) (w : L2VF)
        - F.b (velocitySpanToSigma n u) (velocitySpanToSigma n u) (velocitySpanToSigma n w) := by
  rw [show inner (𝕜 := ℝ) (galerkinODE_vectorField F ν n u : L2VF) (w : L2VF)
      = inner (𝕜 := ℝ) (galerkinODE_vectorField F ν n u) w from
        (Submodule.coe_inner (velocitySpan n) (galerkinODE_vectorField F ν n u) w).symm]
  rw [galerkinODE_vectorField, InnerProductSpace.toDual_symm_apply,
    galerkinODE_functional_apply]

/-! ## B.2 — C1: the Galerkin field is `C¹`

Mirror of `R3/GalerkinODESolve.lean`'s `rieszSymmCLM`/`bInner`/`bMid`/`bOut`/`stokesInner`/
`stokesOut` CLM tower.  The field is `Bil(u,u) + Lin u` with both parts continuous-(bi)linear on
the finite-dim `Vₙ`, hence `ContDiff ℝ 1`. -/

/-- The Riesz inverse as a `ContinuousLinearMap` `(Vₙ →L[ℝ] ℝ) →L[ℝ] Vₙ`. -/
private noncomputable def rieszSymmCLM (n : ℕ) :
    (velocitySpan n →L[ℝ] ℝ) →L[ℝ] velocitySpan n :=
  (InnerProductSpace.toDual ℝ (velocitySpan n)).symm.toContinuousLinearMap

@[simp] private theorem rieszSymmCLM_apply (n : ℕ) (φ : velocitySpan n →L[ℝ] ℝ) :
    rieszSymmCLM n φ = (InnerProductSpace.toDual ℝ (velocitySpan n)).symm φ := rfl

/-- Inner functional (slot 3): `w ↦ -b(σu, σu', σw)`. -/
private noncomputable def bInner (F : Torus3NSForms) (n : ℕ) (u u' : velocitySpan n) :
    velocitySpan n →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => - F.b (velocitySpanToSigma n u) (velocitySpanToSigma n u')
          (velocitySpanToSigma n w)
      map_add' := by
        intro w w'
        rw [velocitySpanToSigma_add, F.b_add_3]; ring
      map_smul' := by
        intro c w
        rw [velocitySpanToSigma_smul, F.b_smul_3]
        simp only [RingHom.id_apply, smul_eq_mul]; ring }

@[simp] private theorem bInner_apply (F : Torus3NSForms) (n : ℕ) (u u' w : velocitySpan n) :
    bInner F n u u' w = - F.b (velocitySpanToSigma n u) (velocitySpanToSigma n u')
      (velocitySpanToSigma n w) := rfl

/-- Middle map (slot 2): `u' ↦ bInner u u'`. -/
private noncomputable def bMid (F : Torus3NSForms) (n : ℕ) (u : velocitySpan n) :
    velocitySpan n →L[ℝ] velocitySpan n →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun u' => bInner F n u u'
      map_add' := by
        intro u' u''
        ext w
        simp only [ContinuousLinearMap.add_apply, bInner_apply, velocitySpanToSigma_add,
          F.b_add_2]; ring
      map_smul' := by
        intro c u'
        ext w
        simp only [RingHom.id_apply, ContinuousLinearMap.smul_apply, bInner_apply,
          velocitySpanToSigma_smul, F.b_smul_2, smul_eq_mul]; ring }

@[simp] private theorem bMid_apply (F : Torus3NSForms) (n : ℕ) (u u' : velocitySpan n) :
    bMid F n u u' = bInner F n u u' := rfl

/-- Outer map (slot 1): `u ↦ bMid u`. -/
private noncomputable def bOut (F : Torus3NSForms) (n : ℕ) :
    velocitySpan n →L[ℝ] velocitySpan n →L[ℝ] velocitySpan n →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun u => bMid F n u
      map_add' := by
        intro u u''
        ext u' w
        simp only [ContinuousLinearMap.add_apply, bMid_apply, bInner_apply,
          velocitySpanToSigma_add, F.b_add_1]; ring
      map_smul' := by
        intro c u
        ext u' w
        simp only [RingHom.id_apply, ContinuousLinearMap.smul_apply, bMid_apply, bInner_apply,
          velocitySpanToSigma_smul, F.b_smul_1, smul_eq_mul]; ring }

@[simp] private theorem bOut_apply (F : Torus3NSForms) (n : ℕ) (u : velocitySpan n) :
    bOut F n u = bMid F n u := rfl

/-- The bilinear part of the Galerkin field `(u, u') ↦ (toDual).symm (w ↦ -b(u,u',w))`. -/
noncomputable def galerkinODE_bilinearPart (F : Torus3NSForms) (ν : ℝ) (n : ℕ) :
    velocitySpan n →L[ℝ] velocitySpan n →L[ℝ] velocitySpan n :=
  (ContinuousLinearMap.compL ℝ (velocitySpan n) (velocitySpan n →L[ℝ] ℝ)
      (velocitySpan n) (rieszSymmCLM n)).comp (bOut F n)

@[simp] private theorem galerkinODE_bilinearPart_apply (F : Torus3NSForms) (ν : ℝ) (n : ℕ)
    (u u' : velocitySpan n) :
    galerkinODE_bilinearPart F ν n u u' = rieszSymmCLM n (bInner F n u u') := rfl

/-- Inner functional: `w ↦ -ν·stokes(σu, σw)`. -/
private noncomputable def stokesInner (ν : ℝ) (n : ℕ) (u : velocitySpan n) :
    velocitySpan n →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => - ν * stokesTestPairing (u : L2VF) (w : L2VF)
      map_add' := by
        intro w w'
        rw [show ((w + w' : velocitySpan n) : L2VF) = (w : L2VF) + (w' : L2VF) from rfl,
          stokesTestPairing_add_right n (u : L2VF) (w : L2VF) (w' : L2VF)
            (velocityP_fixes_coe n u)]; ring
      map_smul' := by
        intro c w
        rw [show ((c • w : velocitySpan n) : L2VF) = c • (w : L2VF) from rfl,
          stokesTestPairing_smul_right n c (u : L2VF) (w : L2VF) (velocityP_fixes_coe n u)]
        simp only [RingHom.id_apply, smul_eq_mul]; ring }

@[simp] private theorem stokesInner_apply (ν : ℝ) (n : ℕ) (u w : velocitySpan n) :
    stokesInner ν n u w = - ν * stokesTestPairing (u : L2VF) (w : L2VF) := rfl

/-- Outer map: `u ↦ stokesInner u`, linear in `u` by left-linearity of stokes on `Vₙ`. -/
private noncomputable def stokesOut (ν : ℝ) (n : ℕ) :
    velocitySpan n →L[ℝ] velocitySpan n →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun u => stokesInner ν n u
      map_add' := by
        intro u u'
        ext w
        simp only [ContinuousLinearMap.add_apply, stokesInner_apply]
        rw [show ((u + u' : velocitySpan n) : L2VF) = (u : L2VF) + (u' : L2VF) from rfl,
          stokesTestPairing_add_left n (u : L2VF) (u' : L2VF) (w : L2VF)
            (velocityP_fixes_coe n w)]; ring
      map_smul' := by
        intro c u
        ext w
        simp only [RingHom.id_apply, ContinuousLinearMap.smul_apply, stokesInner_apply,
          smul_eq_mul]
        rw [show ((c • u : velocitySpan n) : L2VF) = c • (u : L2VF) from rfl,
          stokesTestPairing_smul_left n c (u : L2VF) (w : L2VF) (velocityP_fixes_coe n w)]; ring }

@[simp] private theorem stokesOut_apply (ν : ℝ) (n : ℕ) (u : velocitySpan n) :
    stokesOut ν n u = stokesInner ν n u := rfl

/-- The linear part of the Galerkin field `u ↦ (toDual).symm (w ↦ -ν·stokes(u,w))`. -/
noncomputable def galerkinODE_linearPart (F : Torus3NSForms) (ν : ℝ) (n : ℕ) :
    velocitySpan n →L[ℝ] velocitySpan n :=
  (rieszSymmCLM n).comp (stokesOut ν n)

@[simp] private theorem galerkinODE_linearPart_apply (F : Torus3NSForms) (ν : ℝ) (n : ℕ)
    (u : velocitySpan n) :
    galerkinODE_linearPart F ν n u = rieszSymmCLM n (stokesInner ν n u) := rfl

/-- The Galerkin field equals `Bil(u,u) + Lin u`, by Riesz injectivity (test against all `w`). -/
private theorem galerkinODE_vectorField_eq_parts (F : Torus3NSForms) (ν : ℝ) (n : ℕ)
    (u : velocitySpan n) :
    galerkinODE_vectorField F ν n u
      = galerkinODE_bilinearPart F ν n u u + galerkinODE_linearPart F ν n u := by
  refine ext_inner_right ℝ (fun w => ?_)
  have hLHS : inner (𝕜 := ℝ) (galerkinODE_vectorField F ν n u) w
      = - ν * stokesTestPairing (u : L2VF) (w : L2VF)
        - F.b (velocitySpanToSigma n u) (velocitySpanToSigma n u) (velocitySpanToSigma n w) := by
    rw [Submodule.coe_inner (velocitySpan n) (galerkinODE_vectorField F ν n u) w]
    exact galerkinODE_vectorField_spec F ν n u w
  have hbil : inner (𝕜 := ℝ) (galerkinODE_bilinearPart F ν n u u) w
      = - F.b (velocitySpanToSigma n u) (velocitySpanToSigma n u) (velocitySpanToSigma n w) := by
    rw [galerkinODE_bilinearPart_apply, rieszSymmCLM_apply,
      InnerProductSpace.toDual_symm_apply, bInner_apply]
  have hlin : inner (𝕜 := ℝ) (galerkinODE_linearPart F ν n u) w
      = - ν * stokesTestPairing (u : L2VF) (w : L2VF) := by
    rw [galerkinODE_linearPart_apply, rieszSymmCLM_apply,
      InnerProductSpace.toDual_symm_apply, stokesInner_apply]
  rw [hLHS, inner_add_left, hbil, hlin]
  ring

/-- **C1 (the enabler).** The Galerkin field `G_n` is `C¹` on the finite-dim `Vₙ`. -/
theorem galerkinODE_vectorField_contDiff (F : Torus3NSForms) (ν : ℝ) (n : ℕ) :
    ContDiff ℝ 1 (galerkinODE_vectorField F ν n) := by
  have hfun : galerkinODE_vectorField F ν n
      = fun u => galerkinODE_bilinearPart F ν n u u + galerkinODE_linearPart F ν n u := by
    funext u; exact galerkinODE_vectorField_eq_parts F ν n u
  rw [hfun]
  have hbil : ContDiff ℝ 1 (fun u => galerkinODE_bilinearPart F ν n u u) :=
    (galerkinODE_bilinearPart F ν n).contDiff.clm_apply contDiff_id
  have hlin : ContDiff ℝ 1 (fun u => galerkinODE_linearPart F ν n u) :=
    (galerkinODE_linearPart F ν n).contDiff
  exact hbil.add hlin

/-! ## B.3 — A1/A2/A3: dissipation identity + the forward a-priori energy bound

Mirror of `R3/GalerkinODESolve.lean`'s A1/A2/A3 (domain-agnostic given B.1/B.2 + the diagonal). -/

/-- **A1.** `⟪v, G_n v⟫ ≤ 0` for `v ∈ Vₙ` (dissipation at a point), from R2 + `b_self_zero` +
`stokesTestPairing_diag`. -/
theorem galerkinField_inner_self_nonpos (F : Torus3NSForms) (ν : ℝ) (n : ℕ) (hν : 0 < ν)
    (v : velocitySpan n) :
    inner (𝕜 := ℝ) (v : L2VF) (galerkinODE_vectorField F ν n v : L2VF) ≤ 0 := by
  have hval : inner (𝕜 := ℝ) (v : L2VF) (galerkinODE_vectorField F ν n v : L2VF)
      = - ν * viscousFormSq 1 (v : L2VF) := by
    rw [real_inner_comm]
    have hspec := galerkinODE_vectorField_spec F ν n v v
    rw [hspec, Torus3NSForms.b_self_zero F (velocitySpanToSigma n v), sub_zero,
      stokesTestPairing_diag]
  rw [hval, neg_mul]
  exact neg_nonpos.mpr (mul_nonneg hν.le (viscousFormSq_nonneg zero_le_one _))

/-- **A2.** Along any local solution `c' = G_n(c)`, the energy `½‖c t‖²` has derivative
`-ν·viscousFormSq 1 (c t) ≤ 0`. -/
theorem energy_hasDerivAt_of_localSolution (F : Torus3NSForms) (ν : ℝ) (n : ℕ)
    (c : ℝ → velocitySpan n) (t : ℝ)
    (hc : HasDerivAt (fun s => (c s : L2VF))
      (galerkinODE_vectorField F ν n (c t) : L2VF) t) :
    HasDerivAt (fun s => (1 / 2 : ℝ) * ‖(c s : L2VF)‖ ^ 2)
      (- ν * viscousFormSq 1 (c t : L2VF)) t := by
  have hinnerval : inner (𝕜 := ℝ) (c t : L2VF) (galerkinODE_vectorField F ν n (c t) : L2VF)
      = - ν * viscousFormSq 1 (c t : L2VF) := by
    rw [real_inner_comm]
    have hspec := galerkinODE_vectorField_spec F ν n (c t) (c t)
    rw [hspec, Torus3NSForms.b_self_zero F (velocitySpanToSigma n (c t)), sub_zero,
      stokesTestPairing_diag]
  have hinner :
      HasDerivAt (fun s => inner (𝕜 := ℝ) (c s : L2VF) (c s : L2VF))
        (inner (𝕜 := ℝ) (c t : L2VF) (galerkinODE_vectorField F ν n (c t) : L2VF)
          + inner (𝕜 := ℝ) (galerkinODE_vectorField F ν n (c t) : L2VF) (c t : L2VF)) t :=
    hc.inner ℝ hc
  have hfun : (fun s => (1 / 2 : ℝ) * ‖(c s : L2VF)‖ ^ 2)
      = fun s => (1 / 2 : ℝ) * inner (𝕜 := ℝ) (c s : L2VF) (c s : L2VF) := by
    funext s; rw [real_inner_self_eq_norm_sq]
  rw [hfun]
  have hval : (1 / 2 : ℝ) *
      (inner (𝕜 := ℝ) (c t : L2VF) (galerkinODE_vectorField F ν n (c t) : L2VF)
        + inner (𝕜 := ℝ) (galerkinODE_vectorField F ν n (c t) : L2VF) (c t : L2VF))
      = - ν * viscousFormSq 1 (c t : L2VF) := by
    have hcomm : inner (𝕜 := ℝ) (galerkinODE_vectorField F ν n (c t) : L2VF) (c t : L2VF)
        = inner (𝕜 := ℝ) (c t : L2VF) (galerkinODE_vectorField F ν n (c t) : L2VF) :=
      real_inner_comm _ _
    rw [hcomm, hinnerval]; ring
  rw [← hval]
  exact hinner.const_mul (1 / 2 : ℝ)

/-- **A3.** Any forward local solution on `[0, T]` stays in the ball `‖c t‖ ≤ ‖c 0‖`. -/
theorem norm_le_of_forwardSolution (F : Torus3NSForms) (ν : ℝ) (n : ℕ) (hν : 0 < ν)
    (c : ℝ → velocitySpan n) {T : ℝ} (hT : 0 ≤ T)
    (hsol : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt (fun s => (c s : L2VF))
      (galerkinODE_vectorField F ν n (c t) : L2VF) t) :
    ∀ t ∈ Icc (0 : ℝ) T, ‖(c t : L2VF)‖ ≤ ‖(c 0 : L2VF)‖ := by
  set E : ℝ → ℝ := fun s => (1 / 2 : ℝ) * ‖(c s : L2VF)‖ ^ 2 with hE
  have hderiv : ∀ s ∈ Icc (0 : ℝ) T,
      HasDerivAt E (- ν * viscousFormSq 1 (c s : L2VF)) s := fun s hs =>
    energy_hasDerivAt_of_localSolution F ν n c s (hsol s hs)
  have hAnti : AntitoneOn E (Icc (0 : ℝ) T) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 T) ?_ ?_ ?_
    · exact fun s hs => (hderiv s hs).continuousAt.continuousWithinAt
    · intro s hs
      have hs' : s ∈ Icc (0 : ℝ) T := interior_subset hs
      exact (hderiv s hs').differentiableAt.differentiableWithinAt
    · intro s hs
      have hs' : s ∈ Icc (0 : ℝ) T := interior_subset hs
      rw [(hderiv s hs').deriv]
      have : 0 ≤ ν * viscousFormSq 1 (c s : L2VF) :=
        mul_nonneg hν.le (viscousFormSq_nonneg zero_le_one _)
      rw [neg_mul]; linarith
  intro t ht
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_refl 0, hT⟩
  have hle : E t ≤ E 0 := hAnti h0 ht ht.1
  have hsq : ‖(c t : L2VF)‖ ^ 2 ≤ ‖(c 0 : L2VF)‖ ^ 2 := by
    simp only [hE] at hle; linarith
  have := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at this

end LerayHopf
