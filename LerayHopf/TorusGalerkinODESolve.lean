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

/-! ## B.4 — generic mathlib ODE wrappers (copied verbatim from R3; `{E}`-polymorphic)

These five are domain-generic local re-derivations of the C¹ local-existence and `Icc`-uniqueness
wrappers from the unimported `Mathlib.Analysis.ODE.ExistUnique`, rebuilt from the imported
`PicardLindelof` + `Gronwall`.  They are `private` in R3's file, so copied here. -/

open ODE in
/-- Local copy of `IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt`. -/
private theorem solve_pl_exists {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {f : ℝ → E → E} {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {x₀ x : E}
    {a r L K : ℝ≥0} (hf : IsPicardLindelof f t₀ x₀ a r L K) (hx : x ∈ closedBall x₀ r) :
    ∃ α : ℝ → E, α t₀ = x ∧
      ∀ t ∈ Icc tmin tmax, HasDerivWithinAt α (f t (α t)) (Icc tmin tmax) t := by
  obtain ⟨α, hα⟩ := ODE.FunSpace.exists_isFixedPt_next hf hx
  refine ⟨α.compProj, by rw [ODE.FunSpace.compProj_val, ← hα,
    ODE.FunSpace.next_apply₀], fun t ht ↦ ?_⟩
  apply ODE.hasDerivWithinAt_picard_Icc t₀.2 hf.continuousOn_uncurry
    α.continuous_compProj.continuousOn
    (fun _ ht' ↦ α.compProj_mem_closedBall hf.mul_max_le) x ht |>.congr_of_mem _ ht
  intro t' ht'
  nth_rw 1 [← hα]
  rw [ODE.FunSpace.compProj_of_mem ht', ODE.FunSpace.next_apply]

/-- Local copy of `ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt`. -/
private theorem solve_c1_exists {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {f : E → E} {x₀ : E} (hf : ContDiffAt ℝ 1 f x₀) (t₀ : ℝ) :
    ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ), ∀ x ∈ closedBall x₀ r, ∃ α : ℝ → E, α t₀ = x ∧
      ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), HasDerivAt α (f (α t)) t := by
  obtain ⟨ε, hε, a, r, _, _, hr, hpl⟩ := IsPicardLindelof.of_contDiffAt_one hf
  refine ⟨r, hr, ε, hε, fun x hx ↦ ?_⟩
  obtain ⟨α, hα1, hα2⟩ := solve_pl_exists (hpl t₀) hx
  refine ⟨α, hα1, fun t ht ↦ ?_⟩
  exact hα2 t (Ioo_subset_Icc_self ht) |>.hasDerivAt (Icc_mem_nhds ht.1 ht.2)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Forward uniqueness on `Icc a b` with `a` the initial time. -/
private theorem solve_ode_unique_right {v : ℝ → E → E} {s : ℝ → Set E} {K : ℝ≥0}
    {f' g' : ℝ → E} {a b : ℝ}
    (hv : ∀ t ∈ Ico a b, LipschitzOnWith K (v t) (s t))
    (hf : ContinuousOn f' (Icc a b))
    (hf' : ∀ t ∈ Ico a b, HasDerivWithinAt f' (v t (f' t)) (Ici t) t)
    (hfs : ∀ t ∈ Ico a b, f' t ∈ s t)
    (hg : ContinuousOn g' (Icc a b))
    (hg' : ∀ t ∈ Ico a b, HasDerivWithinAt g' (v t (g' t)) (Ici t) t)
    (hgs : ∀ t ∈ Ico a b, g' t ∈ s t)
    (ha : f' a = g' a) :
    EqOn f' g' (Icc a b) := fun t ht ↦ by
  have := dist_le_of_trajectories_ODE_of_mem hv hf hf' hfs hg hg' hgs
    (dist_le_zero.2 ha) t ht
  rwa [zero_mul, dist_le_zero] at this

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Backward uniqueness on `Icc a b` with `b` the initial time (time-reversed). -/
private theorem solve_ode_unique_left {v : ℝ → E → E} {s : ℝ → Set E} {K : ℝ≥0}
    {f' g' : ℝ → E} {a b : ℝ}
    (hv : ∀ t ∈ Ioc a b, LipschitzOnWith K (v t) (s t))
    (hf : ContinuousOn f' (Icc a b))
    (hf' : ∀ t ∈ Ioc a b, HasDerivWithinAt f' (v t (f' t)) (Iic t) t)
    (hfs : ∀ t ∈ Ioc a b, f' t ∈ s t)
    (hg : ContinuousOn g' (Icc a b))
    (hg' : ∀ t ∈ Ioc a b, HasDerivWithinAt g' (v t (g' t)) (Iic t) t)
    (hgs : ∀ t ∈ Ioc a b, g' t ∈ s t)
    (hb : f' b = g' b) :
    EqOn f' g' (Icc a b) := by
  have hv' : ∀ t ∈ Ico (-b) (-a), LipschitzOnWith K (Neg.neg ∘ (v (-t))) (s (-t)) := by
    intro t ht
    have ht' : -t ∈ Ioc a b := ⟨lt_neg.mp ht.2, neg_le.mp ht.1⟩
    rw [← one_mul K]
    exact LipschitzWith.id.neg.comp_lipschitzOnWith (hv _ ht')
  have hmt1 : MapsTo Neg.neg (Icc (-b) (-a)) (Icc a b) :=
    fun _ ht ↦ ⟨le_neg.mp ht.2, neg_le.mp ht.1⟩
  have hmt2 : MapsTo Neg.neg (Ico (-b) (-a)) (Ioc a b) :=
    fun _ ht ↦ ⟨lt_neg.mp ht.2, neg_le.mp ht.1⟩
  have hmt3 (t : ℝ) : MapsTo Neg.neg (Ici t) (Iic (-t)) :=
    fun _ ht' ↦ mem_Iic.mpr <| neg_le_neg ht'
  suffices h : EqOn (f' ∘ Neg.neg) (g' ∘ Neg.neg) (Icc (-b) (-a)) by
    rw [eqOn_comp_right_iff] at h
    convert h
    simp
  apply solve_ode_unique_right hv'
    (hf.comp continuousOn_neg hmt1) _ (fun _ ht ↦ hfs _ (hmt2 ht))
    (hg.comp continuousOn_neg hmt1) _ (fun _ ht ↦ hgs _ (hmt2 ht)) (by simp [hb])
  · intro t ht
    have := HasFDerivWithinAt.comp_hasDerivWithinAt t (hf' (-t) (hmt2 ht))
      (hasDerivAt_neg t).hasDerivWithinAt (hmt3 t)
    simpa using this
  · intro t ht
    have := HasFDerivWithinAt.comp_hasDerivWithinAt t (hg' (-t) (hmt2 ht))
      (hasDerivAt_neg t).hasDerivWithinAt (hmt3 t)
    simpa using this

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Two-sided uniqueness on `Icc a b` with interior initial time `t₀`. -/
private theorem solve_ode_unique_Icc {v : ℝ → E → E} {s : ℝ → Set E} {K : ℝ≥0}
    {f' g' : ℝ → E} {a b t₀ : ℝ}
    (hv : ∀ t ∈ Ioo a b, LipschitzOnWith K (v t) (s t))
    (ht : t₀ ∈ Ioo a b)
    (hf : ContinuousOn f' (Icc a b))
    (hf' : ∀ t ∈ Ioo a b, HasDerivAt f' (v t (f' t)) t)
    (hfs : ∀ t ∈ Ioo a b, f' t ∈ s t)
    (hg : ContinuousOn g' (Icc a b))
    (hg' : ∀ t ∈ Ioo a b, HasDerivAt g' (v t (g' t)) t)
    (hgs : ∀ t ∈ Ioo a b, g' t ∈ s t)
    (heq : f' t₀ = g' t₀) :
    EqOn f' g' (Icc a b) := by
  rw [← Icc_union_Icc_eq_Icc (le_of_lt ht.1) (le_of_lt ht.2)]
  apply EqOn.union
  · have hss : Ioc a t₀ ⊆ Ioo a b := Ioc_subset_Ioo_right ht.2
    exact solve_ode_unique_left (fun t ht ↦ hv t (hss ht))
      (hf.mono <| Icc_subset_Icc_right <| le_of_lt ht.2)
      (fun _ ht' ↦ (hf' _ (hss ht')).hasDerivWithinAt) (fun _ ht' ↦ (hfs _ (hss ht')))
      (hg.mono <| Icc_subset_Icc_right <| le_of_lt ht.2)
      (fun _ ht' ↦ (hg' _ (hss ht')).hasDerivWithinAt) (fun _ ht' ↦ (hgs _ (hss ht'))) heq
  · have hss : Ico t₀ b ⊆ Ioo a b := Ico_subset_Ioo_left ht.1
    exact solve_ode_unique_right (fun t ht ↦ hv t (hss ht))
      (hf.mono <| Icc_subset_Icc_left <| le_of_lt ht.1)
      (fun _ ht' ↦ (hf' _ (hss ht')).hasDerivWithinAt) (fun _ ht' ↦ (hfs _ (hss ht')))
      (hg.mono <| Icc_subset_Icc_left <| le_of_lt ht.1)
      (fun _ ht' ↦ (hg' _ (hss ht')).hasDerivWithinAt) (fun _ ht' ↦ (hgs _ (hss ht'))) heq

/-! ## B.5 — G1: forward-global existence by tiling (the core)

Mirror of `R3/GalerkinODESolve.lean`'s G1 chain, over `velocitySpan n` /
`galerkinODE_vectorField F ν n`.  The argument is domain-agnostic; only the subspace and field
names change. -/

/-- **G1 helper (uniform `δ`).** A single uniform local-existence time on the a-priori ball. -/
theorem galerkinField_uniform_local_time (F : Torus3NSForms) (ν : ℝ) (n : ℕ) (R : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x₀ ∈ closedBall (0 : velocitySpan n) R, ∀ t₀ : ℝ,
      ∃ α : ℝ → velocitySpan n, α t₀ = x₀ ∧
        ∀ t ∈ Ioo (t₀ - δ) (t₀ + δ),
          HasDerivAt α (galerkinODE_vectorField F ν n (α t)) t := by
  set g := galerkinODE_vectorField F ν n with hg
  have hcd : ∀ x : velocitySpan n, ContDiffAt ℝ 1 g x := fun x =>
    (galerkinODE_vectorField_contDiff F ν n).contDiffAt
  have hloc : ∀ y : velocitySpan n, ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ),
      ∀ x ∈ closedBall y r, ∃ α : ℝ → velocitySpan n, α 0 = x ∧
        ∀ t ∈ Ioo (0 - ε) (0 + ε), HasDerivAt α (g (α t)) t := fun y =>
    solve_c1_exists (hcd y) 0
  choose r hr ε hε Hsol using hloc
  have hcover : closedBall (0 : velocitySpan n) R ⊆ ⋃ y, ball y (r y) := by
    intro x _
    exact mem_iUnion.mpr ⟨x, mem_ball_self (hr x)⟩
  obtain ⟨I, hI⟩ := (isCompact_closedBall (0 : velocitySpan n) R).elim_finite_subcover
    (fun y => ball y (r y)) (fun y => isOpen_ball) hcover
  rcases I.eq_empty_or_nonempty with hIemp | hIne
  · refine ⟨1, one_pos, fun x₀ hx₀ t₀ => ?_⟩
    rw [hIemp] at hI
    simp only [Finset.notMem_empty, iUnion_of_empty, iUnion_empty,
      subset_empty_iff] at hI
    exact absurd (hI ▸ hx₀) (Set.notMem_empty x₀)
  · refine ⟨I.inf' hIne ε, ?_, fun x₀ hx₀ t₀ => ?_⟩
    · rw [Finset.lt_inf'_iff]
      exact fun y _ => hε y
    · set δ := I.inf' hIne ε with hδ
      have hx₀' : x₀ ∈ ⋃ y ∈ I, ball y (r y) := hI hx₀
      rw [mem_iUnion₂] at hx₀'
      obtain ⟨y, hyI, hxy⟩ := hx₀'
      have hxmem : x₀ ∈ closedBall y (r y) := ball_subset_closedBall hxy
      obtain ⟨α, hα0, hαsol⟩ := Hsol y x₀ hxmem
      refine ⟨fun t => α (t - t₀), by simp only [sub_self]; exact hα0, fun t ht => ?_⟩
      have hδε : δ ≤ ε y := Finset.inf'_le _ hyI
      have htmem : t - t₀ ∈ Ioo (0 - ε y) (0 + ε y) := by
        rw [mem_Ioo] at ht ⊢
        refine ⟨by rw [zero_sub]; linarith [ht.1], by rw [zero_add]; linarith [ht.2]⟩
      have hd := hαsol (t - t₀) htmem
      have hsub : HasDerivAt (fun t : ℝ => t - t₀) 1 t := (hasDerivAt_id t).sub_const t₀
      have hcomp := hd.scomp t hsub
      simp only [one_smul, Function.comp_def] at hcomp
      exact hcomp

/-- Transport an intrinsic `HasDerivAt` in `Vₙ` to the ambient `L2VF` curve. -/
private theorem solve_hasDerivAt_ambient (F : Torus3NSForms) (ν : ℝ) (n : ℕ)
    (c : ℝ → velocitySpan n) (t : ℝ)
    (h : HasDerivAt c (galerkinODE_vectorField F ν n (c t)) t) :
    HasDerivAt (fun s => (c s : L2VF))
      (galerkinODE_vectorField F ν n (c t) : L2VF) t := by
  have hl : HasFDerivAt (Submodule.subtypeL (velocitySpan n))
      (Submodule.subtypeL (velocitySpan n)) (c t) :=
    (Submodule.subtypeL (velocitySpan n)).hasFDerivAt
  have hcomp := hl.comp_hasDerivAt t h
  simpa [Function.comp_def, Submodule.subtypeL_apply] using hcomp

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
/-- **G1 helper (splice-agreement).** Two local solutions agreeing at one point agree on the
overlap. -/
theorem galerkinField_solution_agree (F : Torus3NSForms) (ν : ℝ) (n : ℕ)
    (α β : ℝ → velocitySpan n) {a b t₀ : ℝ} (hab : a ≤ b) (ht₀ : t₀ ∈ Icc a b)
    (hαβ : α t₀ = β t₀)
    (hα : ∀ t ∈ Icc a b, HasDerivAt α (galerkinODE_vectorField F ν n (α t)) t)
    (hβ : ∀ t ∈ Icc a b, HasDerivAt β (galerkinODE_vectorField F ν n (β t)) t) :
    ∀ t ∈ Icc a b, α t = β t := by
  set g := galerkinODE_vectorField F ν n with hg
  have hαc : ContinuousOn α (Icc a b) := fun t ht => (hα t ht).continuousAt.continuousWithinAt
  have hβc : ContinuousOn β (Icc a b) := fun t ht => (hβ t ht).continuousAt.continuousWithinAt
  obtain ⟨Mα, hMα⟩ := (((isCompact_Icc).image_of_continuousOn hαc).image continuous_norm).bddAbove
  obtain ⟨Mβ, hMβ⟩ := (((isCompact_Icc).image_of_continuousOn hβc).image continuous_norm).bddAbove
  set M : ℝ := max (max Mα Mβ) 0 with hMdef
  have hM0 : 0 ≤ M := le_max_right _ _
  have hαM : ∀ t ∈ Icc a b, α t ∈ closedBall (0 : velocitySpan n) M := by
    intro t ht
    rw [mem_closedBall, dist_zero_right]
    refine le_trans (hMα ⟨α t, ⟨t, ht, rfl⟩, rfl⟩) ?_
    exact le_trans (le_max_left Mα Mβ) (le_max_left _ _)
  have hβM : ∀ t ∈ Icc a b, β t ∈ closedBall (0 : velocitySpan n) M := by
    intro t ht
    rw [mem_closedBall, dist_zero_right]
    refine le_trans (hMβ ⟨β t, ⟨t, ht, rfl⟩, rfl⟩) ?_
    exact le_trans (le_max_right Mα Mβ) (le_max_left _ _)
  have hgcd : ContDiff ℝ 1 g := galerkinODE_vectorField_contDiff F ν n
  obtain ⟨K, hlip⟩ := (hgcd.contDiffOn (s := closedBall (0 : velocitySpan n) M)).exists_lipschitzOnWith
    one_ne_zero (convex_closedBall _ _) (isCompact_closedBall _ _)
  have hbwd : EqOn α β (Icc a t₀) := by
    have hsub : Icc a t₀ ⊆ Icc a b := Icc_subset_Icc_right ht₀.2
    refine solve_ode_unique_left (a := a) (b := t₀) (K := K)
      (s := fun _ => closedBall (0 : velocitySpan n) M)
      (fun t' _ => hlip) (hαc.mono hsub)
      (fun t' ht' => (hα t' (hsub ⟨ht'.1.le, ht'.2⟩)).hasDerivWithinAt)
      (fun t' ht' => hαM t' (hsub ⟨ht'.1.le, ht'.2⟩))
      (hβc.mono hsub)
      (fun t' ht' => (hβ t' (hsub ⟨ht'.1.le, ht'.2⟩)).hasDerivWithinAt)
      (fun t' ht' => hβM t' (hsub ⟨ht'.1.le, ht'.2⟩)) hαβ
  have hfwd : EqOn α β (Icc t₀ b) := by
    have hsub : Icc t₀ b ⊆ Icc a b := Icc_subset_Icc_left ht₀.1
    refine solve_ode_unique_right (a := t₀) (b := b) (K := K)
      (s := fun _ => closedBall (0 : velocitySpan n) M)
      (fun t' _ => hlip) (hαc.mono hsub)
      (fun t' ht' => (hα t' (hsub ⟨ht'.1, ht'.2.le⟩)).hasDerivWithinAt)
      (fun t' ht' => hαM t' (hsub ⟨ht'.1, ht'.2.le⟩))
      (hβc.mono hsub)
      (fun t' ht' => (hβ t' (hsub ⟨ht'.1, ht'.2.le⟩)).hasDerivWithinAt)
      (fun t' ht' => hβM t' (hsub ⟨ht'.1, ht'.2.le⟩)) hαβ
  intro t ht
  rcases le_total t t₀ with hle | hle
  · exact hbwd ⟨ht.1, hle⟩
  · exact hfwd ⟨hle, ht.2⟩

set_option maxHeartbeats 1600000 in
/-- Tiling induction: a forward solution exists on `[0, k·δ/2]` for every `k`. -/
private theorem solve_exists_on_step (F : Torus3NSForms) (ν : ℝ) (hν : 0 < ν) (n : ℕ)
    (x₀ : velocitySpan n) {δ : ℝ} (hδ : 0 < δ)
    (huniform : ∀ y ∈ closedBall (0 : velocitySpan n) ‖x₀‖, ∀ t₀ : ℝ,
      ∃ α : ℝ → velocitySpan n, α t₀ = y ∧
        ∀ t ∈ Ioo (t₀ - δ) (t₀ + δ),
          HasDerivAt α (galerkinODE_vectorField F ν n (α t)) t) :
    ∀ k : ℕ, ∃ c : ℝ → velocitySpan n, c 0 = x₀ ∧
      ∀ t ∈ Icc (0 : ℝ) (k * (δ / 2)),
        HasDerivAt c (galerkinODE_vectorField F ν n (c t)) t := by
  set g := galerkinODE_vectorField F ν n with hg
  set R := ‖x₀‖ with hR
  have hs2 : (0 : ℝ) < δ / 2 := by positivity
  intro k
  induction k with
  | zero =>
    have hx₀mem : x₀ ∈ closedBall (0 : velocitySpan n) R := by
      rw [mem_closedBall, dist_zero_right, hR]
    obtain ⟨α, hα0, hαsol⟩ := huniform x₀ hx₀mem 0
    refine ⟨α, hα0, fun t ht => ?_⟩
    simp only [Nat.cast_zero, zero_mul] at ht
    have hts : t = 0 := le_antisymm ht.2 ht.1
    subst hts
    exact hαsol 0 ⟨by linarith, by linarith⟩
  | succ k ih =>
    obtain ⟨c, hc0, hcsol⟩ := ih
    have hkδ0 : (0 : ℝ) ≤ k * (δ / 2) := by positivity
    have hcsol_amb : ∀ t ∈ Icc (0 : ℝ) (k * (δ / 2)),
        HasDerivAt (fun s => (c s : L2VF)) (g (c t) : L2VF) t :=
      fun t ht => solve_hasDerivAt_ambient F ν n c t (hcsol t ht)
    have hbound := norm_le_of_forwardSolution F ν n hν c hkδ0 hcsol_amb
      (k * (δ / 2)) ⟨hkδ0, le_rfl⟩
    have hc0amb : (c 0 : L2VF) = (x₀ : L2VF) := by rw [hc0]
    have hckmem : c (k * (δ / 2)) ∈ closedBall (0 : velocitySpan n) R := by
      rw [mem_closedBall, dist_zero_right, hR]
      have h1 : ‖(c (k * (δ / 2)) : L2VF)‖ ≤ ‖(x₀ : L2VF)‖ := by rw [← hc0amb]; exact hbound
      rw [Submodule.norm_coe, Submodule.norm_coe] at h1
      exact h1
    obtain ⟨α, hα0, hαsol⟩ := huniform (c (k * (δ / 2))) hckmem (k * (δ / 2))
    refine ⟨fun t => if t ≤ k * (δ / 2) then c t else α t, ?_, fun t ht => ?_⟩
    · simp only [show (0 : ℝ) ≤ k * (δ / 2) from hkδ0, if_pos]; exact hc0
    · rcases lt_trichotomy t (k * (δ / 2)) with hlt | heq | hgt
      · have hmem : t ∈ Icc (0 : ℝ) (k * (δ / 2)) := ⟨ht.1, le_of_lt hlt⟩
        have hev : (fun t => if t ≤ k * (δ / 2) then c t else α t) =ᶠ[nhds t] c := by
          filter_upwards [Iio_mem_nhds hlt] with s hs
          simp only [if_pos (le_of_lt (mem_Iio.mp hs))]
        rw [hev.hasDerivAt_iff]
        simp only [if_pos (le_of_lt hlt)]
        exact hcsol t hmem
      · set m : ℝ := k * (δ / 2) with hm
        rw [heq]
        have hval : α m = c m := hα0
        have hpw_t : (if m ≤ m then c m else α m) = c m := by rw [if_pos le_rfl]
        have hleft : HasDerivWithinAt (fun s => if s ≤ m then c s else α s)
            (g (c m)) (Iic m) m := by
          refine (hcsol m ⟨by rw [← heq]; exact ht.1, le_rfl⟩).hasDerivWithinAt.congr_of_mem
            (fun s hs => ?_) (mem_Iic.mpr le_rfl)
          simp only [if_pos (mem_Iic.mp hs)]
        have htmem : m ∈ Ioo (m - δ) (m + δ) := ⟨by linarith, by linarith⟩
        have hαt : HasDerivAt α (g (α m)) m := hαsol m htmem
        have hright : HasDerivWithinAt (fun s => if s ≤ m then c s else α s)
            (g (c m)) (Ici m) m := by
          have hαdw : HasDerivWithinAt α (g (c m)) (Ici m) m := by
            rw [← hval]; exact hαt.hasDerivWithinAt
          refine hαdw.congr_of_mem (fun s hs => ?_) (mem_Ici.mpr le_rfl)
          rcases eq_or_lt_of_le (mem_Ici.mp hs) with hse | hslt
          · simp only [← hse, if_pos le_rfl]; exact hval.symm
          · simp only [if_neg (not_le.mpr hslt)]
        have hunion := hleft.union hright
        rw [Iic_union_Ici, hasDerivWithinAt_univ] at hunion
        show HasDerivAt (fun s => if s ≤ m then c s else α s)
          (g (if m ≤ m then c m else α m)) m
        rw [hpw_t]
        exact hunion
      · have hub : t ≤ (k + 1 : ℝ) * (δ / 2) := by
          have h2 := ht.2; push_cast at h2 ⊢; linarith
        have htmem : t ∈ Ioo (k * (δ / 2) - δ) (k * (δ / 2) + δ) := by
          refine ⟨by linarith, ?_⟩
          have : (k + 1 : ℝ) * (δ / 2) = k * (δ / 2) + δ / 2 := by ring
          have hδ2 : δ / 2 < δ := by linarith
          linarith [hub, this]
        have hev : (fun s => if s ≤ k * (δ / 2) then c s else α s) =ᶠ[nhds t] α := by
          filter_upwards [Ioi_mem_nhds hgt] with s hs
          simp only [if_neg (not_le.mpr (mem_Ioi.mp hs))]
        rw [hev.hasDerivAt_iff]
        show HasDerivAt α (g (if t ≤ k * (δ / 2) then c t else α t)) t
        rw [if_neg (not_le.mpr hgt)]
        exact hαsol t htmem

set_option maxHeartbeats 800000 in
/-- **G1 (THE core).** Forward-global existence: there is `c : ℝ → Vₙ` with
`c 0 = velocityProjection_n n u₀` and `∀ t ≥ 0, HasDerivAt (↑∘c) (G_n (c t)) t`. -/
theorem forwardGlobalSolution_exists (F : Torus3NSForms) (ν : ℝ) (hν : 0 < ν)
    (u₀ : L2Sigma) (n : ℕ) :
    ∃ c : ℝ → velocitySpan n,
      (c 0 : L2VF) = velocityProjection_n n (u₀ : L2VF) ∧
      ∀ t, 0 ≤ t → HasDerivAt (fun s => (c s : L2VF))
        (galerkinODE_vectorField F ν n (c t) : L2VF) t := by
  classical
  set g := galerkinODE_vectorField F ν n with hg
  have hx₀mem : velocityProjection_n n (u₀ : L2VF) ∈ velocitySpan n := velocityP_initial_mem n u₀
  set x₀ : velocitySpan n := ⟨velocityProjection_n n (u₀ : L2VF), hx₀mem⟩ with hx₀
  set R := ‖x₀‖ with hR
  obtain ⟨δ, hδ, huniform⟩ := galerkinField_uniform_local_time F ν n R
  have hstep := solve_exists_on_step F ν hν n x₀ hδ huniform
  set s2 : ℝ := δ / 2 with hs2def
  have hs2 : (0 : ℝ) < s2 := by rw [hs2def]; positivity
  choose ck hck0 hcksol using hstep
  set N : ℝ → ℕ := fun t => ⌊t / s2⌋₊ + 1 with hN
  set c : ℝ → velocitySpan n := fun t => ck (N t) t with hc
  have hltN : ∀ t : ℝ, t < N t * s2 := by
    intro t
    rcases lt_or_ge t 0 with ht0 | ht0
    · have hN1 : (1 : ℝ) ≤ (N t : ℝ) := by
        rw [hN]; push_cast; have := Nat.zero_le (⌊t / s2⌋₊); push_cast; linarith
      have hpos : (0 : ℝ) < N t * s2 := mul_pos (by linarith) hs2
      linarith
    · have hlt : t / s2 < (⌊t / s2⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one (t / s2)
      have heq2 : t = (t / s2) * s2 := by field_simp
      have hmul := mul_lt_mul_of_pos_right hlt hs2
      rw [← heq2] at hmul
      rw [hN]; push_cast
      exact hmul
  have hmemN : ∀ t, 0 ≤ t → t ∈ Icc (0 : ℝ) (N t * s2) := fun t ht => ⟨ht, le_of_lt (hltN t)⟩
  have hagree : ∀ j k : ℕ, ∀ t ∈ Icc (0 : ℝ) (min (j * s2) (k * s2)), ck j t = ck k t := by
    intro j k t ht
    have hjk : (0 : ℝ) ≤ min (j * s2) (k * s2) := le_min (by positivity) (by positivity)
    refine galerkinField_solution_agree F ν n (ck j) (ck k) hjk ⟨le_refl 0, hjk⟩
      (by rw [hck0 j, hck0 k]) ?_ ?_ t ht
    · intro u hu
      exact hcksol j u ⟨hu.1, le_trans hu.2 (min_le_left _ _)⟩
    · intro u hu
      exact hcksol k u ⟨hu.1, le_trans hu.2 (min_le_right _ _)⟩
  refine ⟨c, ?_, ?_⟩
  · show (ck (N 0) 0 : L2VF) = velocityProjection_n n (u₀ : L2VF)
    rw [hck0 (N 0)]
  · intro t ht
    have hsol := hcksol (N t) t (hmemN t ht)
    have hsol_amb := solve_hasDerivAt_ambient F ν n (ck (N t)) t hsol
    have hN1 : ∀ u : ℝ, u < s2 → N u = 1 := by
      intro u hu
      show ⌊u / s2⌋₊ + 1 = 1
      have hfloor : ⌊u / s2⌋₊ = 0 := by
        apply Nat.floor_eq_zero.mpr
        rw [div_lt_one hs2]; exact hu
      rw [hfloor]
    have hev : (fun s => (c s : L2VF)) =ᶠ[nhds t]
        (fun u => (ck (N t) u : L2VF)) := by
      rcases eq_or_lt_of_le ht with ht0 | ht0
      · rw [← ht0]
        have hVnhds : Iio s2 ∈ nhds (0 : ℝ) := Iio_mem_nhds hs2
        filter_upwards [hVnhds] with u hu
        show (ck (N u) u : L2VF) = (ck (N 0) u : L2VF)
        rw [hN1 u hu, hN1 0 hs2]
      · have hVnhds : Iio (N t * s2) ∩ Ioi 0 ∈ nhds t :=
          Filter.inter_mem (Iio_mem_nhds (hltN t)) (Ioi_mem_nhds ht0)
        filter_upwards [hVnhds] with u hu
        show (ck (N u) u : L2VF) = (ck (N t) u : L2VF)
        have humem : u ∈ Icc (0 : ℝ) (min (N u * s2) (N t * s2)) :=
          ⟨le_of_lt (mem_Ioi.mp hu.2), le_min (le_of_lt (hltN u)) (le_of_lt (mem_Iio.mp hu.1))⟩
        rw [hagree (N u) (N t) u humem]
    have hgoal : HasDerivAt (fun s => (ck (N t) s : L2VF))
        (galerkinODE_vectorField F ν n (c t) : L2VF) t := by
      have hct : (c t : velocitySpan n) = ck (N t) t := rfl
      rw [show (galerkinODE_vectorField F ν n (c t) : L2VF)
          = (galerkinODE_vectorField F ν n (ck (N t) t) : L2VF) from by rw [hct]]
      exact hsol_amb
    exact (hev.hasDerivAt_iff).mpr hgoal

/-! ## B.6 — D: assemble `GalerkinSolutionData`

Build the per-`n` solver `galerkinSolutionData_torus`, deriving all 8 fields directly from G1 +
R2 (no `GalerkinODEInput` intermediate, per the phase plan).  The energy/regularity payoff
(`reg_mem`/`energy_bound`/`reg_bound`) is derived axiom-free from the dissipation identity. -/

/-- H¹ regularity of any `Vₙ`-curve point: a finite-Fourier-support field is in `memH1VF`. -/
theorem galerkinCurve_reg_mem (n : ℕ) (v : L2VF)
    (hv : velocityProjection_n n v = v) : memH1VF v := by
  intro j
  -- `memH1Torus (componentC j v)` = summability of the H¹-weight sum; finite support ⟹ summable.
  apply summable_of_ne_finset_zero (s := fourierBox n)
  intro k hk
  rw [coeff_zero_outside_box n v hv j k hk]
  simp

/-- **Pythagorean L²-norm decomposition.** `‖u‖²_{L2VF} = ∑ⱼ ‖componentC j u‖²_{L2C}`.

The L²-inner product is the integral of the pointwise Euclidean inner product; the Euclidean
norm² of a `Fin 3`-vector is the sum of its component squares; and `‖componentC j u‖` (complex
embedding) equals `‖projComponent j u‖` (real component). -/
theorem L2VF_norm_sq_eq_sum_componentC (u : L2VF) :
    ‖u‖ ^ 2 = ∑ j : Fin 3, ‖L2VF_projComponentC j u‖ ^ 2 := by
  -- a.e. description of the complex `j`-th component as `x ↦ (u x j : ℂ)`.
  have hcompCx : ∀ j : Fin 3, ⇑(L2VF_projComponentC j u) =ᵐ[haarTorus3]
      fun x => ((u x j : ℝ) : ℂ) := by
    intro j
    have h1 := ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := haarTorus3)
      (RCLike.ofRealCLM (K := ℂ)) (L2VF_projComponent j u)
    have h2 := ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := haarTorus3)
      (EuclideanSpace.proj j (𝕜 := ℝ)) u
    filter_upwards [h1, h2] with x hx1 hx2
    show (RCLike.ofRealCLM (K := ℂ)).compLpL 2 haarTorus3 (L2VF_projComponent j u) x = _
    rw [hx1, show (L2VF_projComponent j u) x = u x j from hx2]; rfl
  -- Each complex component norm² is the integral of its pointwise square `∫ (u x j)²`.
  have hpc : ∀ j : Fin 3, ‖L2VF_projComponentC j u‖ ^ 2 = ∫ x, ‖u x j‖ ^ 2 ∂haarTorus3 := by
    intro j
    rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hcompCx j] with x hx
    show RCLike.re (inner (𝕜 := ℂ) (L2VF_projComponentC j u x) (L2VF_projComponentC j u x)) = _
    rw [hx, inner_self_eq_norm_sq, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simp_rw [hpc]
  -- Integrability of each `x ↦ ‖u x j‖²` (from `Lp.memLp` of the complex component).
  have hint : ∀ j : Fin 3, MeasureTheory.Integrable (fun x => ‖u x j‖ ^ 2) haarTorus3 := by
    intro j
    have hL2 := (Lp.memLp (L2VF_projComponentC j u)).integrable_norm_rpow
      (by norm_num) (by norm_num)
    refine (hL2.congr ?_)
    filter_upwards [hcompCx j] with x hx
    rw [hx, Complex.norm_real, show ((2 : ENNReal).toReal) = (2 : ℝ) by norm_num, Real.rpow_two,
      Real.norm_eq_abs, ← sq_abs]
  -- `‖u‖² = ∫ ⟪u x, u x⟫ = ∫ ∑ⱼ ‖u x j‖² = ∑ⱼ ∫ ‖u x j‖²`.
  rw [← real_inner_self_eq_norm_sq u, MeasureTheory.L2.inner_def,
    show (fun x => inner (𝕜 := ℝ) (u x) (u x))
      = fun x => ∑ j : Fin 3, ‖u x j‖ ^ 2 from ?_,
    integral_finsetSum _ (fun j _ => hint j)]
  funext x
  rw [real_inner_self_eq_norm_sq, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]

/-- The energy identity along the field flow (forward time), mirroring `galerkin_energy_identity`:
`d/dt ½‖c t‖² = -ν·viscousFormSq 1 (c t)`.  Here `c : ℝ → velocitySpan n` is the G1 curve and the
ambient derivative is the field. -/
private theorem galerkin_energy_identity_curve (F : Torus3NSForms) (ν : ℝ) (n : ℕ)
    (c : ℝ → velocitySpan n) (t : ℝ) (ht : 0 ≤ t)
    (hd : ∀ s, 0 ≤ s → HasDerivAt (fun r => (c r : L2VF))
      (galerkinODE_vectorField F ν n (c s) : L2VF) s) :
    HasDerivAt (fun s => (1 / 2 : ℝ) * ‖(c s : L2VF)‖ ^ 2)
      (- ν * viscousFormSq 1 (c t : L2VF)) t :=
  energy_hasDerivAt_of_localSolution F ν n c t (hd t ht)

/-! ### The `h1EnergySq = L² + gradient` split on `Vₙ` (planner risk #3) -/

/-- Each `Vₙ`-element component's weighted coefficient sum is a finite sum over `fourierBox n`. -/
private theorem componentC_h1_summable (n : ℕ) (u : L2VF) (hu : velocityProjection_n n u = u)
    (j : Fin 3) (g : (Fin 3 → ℤ) → ℝ) :
    Summable (fun k : Fin 3 → ℤ => g k * ‖mFourierCoeff3 (L2VF_projComponentC j u) k‖ ^ 2) := by
  apply summable_of_ne_finset_zero (s := fourierBox n)
  intro k hk
  rw [coeff_zero_outside_box n u hu j k hk]; simp

/-- **`h1EnergySq` split on `Vₙ`.** For `u ∈ Vₙ` (finite Fourier support):
`h1EnergySq u = ‖u‖²_{L2VF} + (2π)²⁻¹ · viscousFormSq 1 u`.

The H¹ weight `(1 + ∑ᵢkᵢ²)` splits into the L²-part (`1`) — which is `‖u‖²` by Parseval +
Pythagoras — and the gradient part (`∑ᵢkᵢ²`), which is `(2π)²⁻¹·viscousFormSq 1 u`. -/
theorem h1EnergySq_eq_L2_add_viscous (n : ℕ) (u : L2VF) (hu : velocityProjection_n n u = u) :
    h1EnergySq u = ‖u‖ ^ 2 + ((2 * Real.pi) ^ 2)⁻¹ * viscousFormSq 1 u := by
  -- Parseval per component: `‖componentC j u‖² = ∑'ₖ ‖ûⱼ(k)‖²`.
  have hL2 : ‖u‖ ^ 2 = ∑ j : Fin 3, ∑' k : Fin 3 → ℤ,
      ‖mFourierCoeff3 (L2VF_projComponentC j u) k‖ ^ 2 := by
    rw [L2VF_norm_sq_eq_sum_componentC]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    exact L2C_norm_sq_eq_tsum_coeff_sq (L2VF_projComponentC j u)
  rw [hL2, h1EnergySq, viscousFormSq, one_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  -- Rewrite each per-`j` summand into the split form, then split the tsum.
  have hsplit : (fun k : Fin 3 → ℤ =>
        (1 + ∑ i : Fin 3, (k i : ℝ) ^ 2) * ‖mFourierCoeff3 (L2VF_projComponentC j u) k‖ ^ 2)
      = fun k => ‖mFourierCoeff3 (L2VF_projComponentC j u) k‖ ^ 2
        + ((2 * Real.pi) ^ 2)⁻¹ * ((2 * Real.pi) ^ 2 * (∑ i : Fin 3, (k i : ℝ) ^ 2) *
            ‖mFourierCoeff3 (L2VF_projComponentC j u) k‖ ^ 2) := by
    funext k
    have hne : ((2 * Real.pi) ^ 2) ≠ 0 := by positivity
    field_simp
  rw [hsplit, Summable.tsum_add (componentC_h1_summable n u hu j (fun _ => 1) |>.congr (by intro k; ring))
    (by
      have := componentC_h1_summable n u hu j (fun k => ((2 * Real.pi) ^ 2)⁻¹ *
        ((2 * Real.pi) ^ 2 * (∑ i : Fin 3, (k i : ℝ) ^ 2)))
      refine this.congr (fun k => ?_); ring),
    ← tsum_mul_left]

/-- **E2 — uniform energy bound.** `½‖c t‖² ≤ ½‖Pₙ u₀‖²` for the G1 curve at `t ≥ 0`. -/
private theorem galerkin_energy_bound_curve (F : Torus3NSForms) (ν : ℝ) (hν : 0 < ν) (n : ℕ)
    (u₀ : L2Sigma) (c : ℝ → velocitySpan n)
    (hc0 : (c 0 : L2VF) = velocityProjection_n n (u₀ : L2VF))
    (hd : ∀ s, 0 ≤ s → HasDerivAt (fun r => (c r : L2VF))
      (galerkinODE_vectorField F ν n (c s) : L2VF) s)
    (t : ℝ) (ht : 0 ≤ t) :
    (1 / 2 : ℝ) * ‖(c t : L2VF)‖ ^ 2 ≤
    (1 / 2 : ℝ) * ‖velocityProjection_n n (u₀ : L2VF)‖ ^ 2 := by
  have hnorm : ‖(c t : L2VF)‖ ≤ ‖(c 0 : L2VF)‖ :=
    norm_le_of_forwardSolution F ν n hν c ht
      (fun s hs => hd s hs.1) t ⟨ht, le_rfl⟩
  rw [hc0] at hnorm
  have hsq : ‖(c t : L2VF)‖ ^ 2 ≤ ‖velocityProjection_n n (u₀ : L2VF)‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  linarith

/-- The squared Fourier coefficients of any `f : L2C` are summable (from `lp` membership). -/
theorem summable_norm_mFourierCoeff3_sq (f : L2C) :
    Summable (fun k : Fin 3 → ℤ => ‖mFourierCoeff3 f k‖ ^ 2) := by
  have hmem : Memℓp (torus3_mFourierBasis.repr f) 2 := (torus3_mFourierBasis.repr f).2
  have hp : (0 : ℝ) < (2 : ENNReal).toReal := by norm_num
  have := (memℓp_gen_iff hp).mp hmem
  refine this.congr (fun k => ?_)
  rw [show ((2 : ENNReal).toReal) = (2 : ℝ) by norm_num, Real.rpow_two]
  rfl

/-- The Galerkin projection is L²-nonexpansive: `‖Pₙ u‖ ≤ ‖u‖`.

By Pythagoras + per-component Parseval, `‖Pₙ u‖² = ∑ⱼ∑_{k∈box}‖ûⱼ(k)‖² ≤ ∑ⱼ∑'ₖ‖ûⱼ(k)‖² = ‖u‖²`
(the cutoff `Pₙ` only drops Fourier modes). -/
theorem velocityProjection_n_norm_le (n : ℕ) (u : L2VF) :
    ‖velocityProjection_n n u‖ ≤ ‖u‖ := by
  have hsq : ‖velocityProjection_n n u‖ ^ 2 ≤ ‖u‖ ^ 2 := by
    rw [L2VF_norm_sq_eq_sum_componentC, L2VF_norm_sq_eq_sum_componentC]
    refine Finset.sum_le_sum (fun j _ => ?_)
    rw [L2C_norm_sq_eq_tsum_coeff_sq, L2C_norm_sq_eq_tsum_coeff_sq]
    -- Per-coefficient: `‖(Pₙu)^ⱼ(k)‖² ≤ ‖ûⱼ(k)‖²` (equal in-box, `0 ≤ ‖·‖²` out-of-box).
    have hcoe : ∀ k : Fin 3 → ℤ,
        ‖mFourierCoeff3 (L2VF_projComponentC j (velocityProjection_n n u)) k‖ ^ 2
        ≤ ‖mFourierCoeff3 (L2VF_projComponentC j u) k‖ ^ 2 := by
      intro k
      rw [velocityProjection_n_component_comm, ContinuousLinearMap.coe_restrictScalars',
        fourierProjection_n_mFourierCoeff]
      by_cases hk : k ∈ fourierBox n
      · rw [if_pos hk]
      · rw [if_neg hk]; simp
    exact Summable.tsum_le_tsum hcoe
      (summable_norm_mFourierCoeff3_sq (L2VF_projComponentC j (velocityProjection_n n u)))
      (summable_norm_mFourierCoeff3_sq (L2VF_projComponentC j u))
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (by norm_num)).mp hsq

/-- **E3-analog — viscous dissipation bound.** `∫₀ᵀ viscousFormSq 1 (c t) dt ≤ ‖u₀‖²/(2ν)`.

From the energy identity `d/dt ½‖c t‖² = -ν·viscousFormSq 1 (c t)`, integrating the negation
`-½‖c t‖²` (whose forward derivative is `ν·viscousFormSq 1 (c t) ≥ 0`) over `[0,T]` gives
`ν∫ viscousFormSq 1 (c t) ≤ ½‖c 0‖² - ½‖c T‖² ≤ ½‖c 0‖² ≤ ½‖u₀‖²`.  Case-splits on integrability
of the viscous integrand (mirrors R3's E3); when non-integrable the integral is `0` and the bound
is vacuous (RHS `≥ 0`). -/
private theorem galerkin_viscous_bound (F : Torus3NSForms) (ν : ℝ) (hν : 0 < ν) (n : ℕ)
    (u₀ : L2Sigma) (c : ℝ → velocitySpan n)
    (hc0 : (c 0 : L2VF) = velocityProjection_n n (u₀ : L2VF))
    (hd : ∀ s, 0 ≤ s → HasDerivAt (fun r => (c r : L2VF))
      (galerkinODE_vectorField F ν n (c s) : L2VF) s)
    {T : ℝ} (hT : 0 < T) :
    ∫ t in (0 : ℝ)..T, viscousFormSq 1 (c t : L2VF) ≤ ‖(u₀ : L2VF)‖ ^ 2 / (2 * ν) := by
  set E : ℝ → ℝ := fun s => (1 / 2 : ℝ) * ‖(c s : L2VF)‖ ^ 2 with hE
  -- `E 0 = ½‖Pₙu₀‖² ≤ ½‖u₀‖²`.
  have hE0 : E 0 ≤ (1 / 2 : ℝ) * ‖(u₀ : L2VF)‖ ^ 2 := by
    rw [hE]; simp only; rw [hc0]
    have hle : ‖velocityProjection_n n (u₀ : L2VF)‖ ≤ ‖(u₀ : L2VF)‖ :=
      velocityProjection_n_norm_le n (u₀ : L2VF)
    have : ‖velocityProjection_n n (u₀ : L2VF)‖ ^ 2 ≤ ‖(u₀ : L2VF)‖ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hle 2
    linarith
  have hET : 0 ≤ E T := by rw [hE]; positivity
  -- It suffices to bound `∫ ν·viscousFormSq 1 ≤ ½‖u₀‖²`, then divide by `ν`.
  rw [show ‖(u₀ : L2VF)‖ ^ 2 / (2 * ν)
      = ((1 / 2 : ℝ) * ‖(u₀ : L2VF)‖ ^ 2) / ν from by rw [mul_comm 2 ν]; field_simp,
    le_div_iff₀ hν, mul_comm, ← intervalIntegral.integral_const_mul]
  by_cases hint : IntervalIntegrable
      (fun t => ν * viscousFormSq 1 (c t : L2VF)) MeasureTheory.volume (0 : ℝ) T
  · -- FTC: `∫ (-E)' = -E T - (-E 0) = E 0 - E T`, with `(-E)' = ν·viscousFormSq 1`.
    have hcont : ContinuousOn (fun s => - E s) (Set.Icc (0 : ℝ) T) := by
      refine ContinuousOn.neg (fun x hx => ?_)
      exact (energy_hasDerivAt_of_localSolution F ν n c x
        (hd x hx.1)).continuousAt.continuousWithinAt
    have hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) T,
        HasDerivWithinAt (fun s => - E s) (ν * viscousFormSq 1 (c x : L2VF)) (Set.Ioi x) x := by
      intro x hx
      have hd' : HasDerivAt E (- ν * viscousFormSq 1 (c x : L2VF)) x :=
        energy_hasDerivAt_of_localSolution F ν n c x (hd x (le_of_lt hx.1))
      have := hd'.neg
      rw [neg_mul, neg_neg] at this
      exact this.hasDerivWithinAt
    have hφint : MeasureTheory.IntegrableOn
        (fun t => ν * viscousFormSq 1 (c t : L2VF)) (Set.Icc (0 : ℝ) T) MeasureTheory.volume :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hT.le).1 hint
    have hle := intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le hT.le hcont hderiv hφint
      (fun x _ => le_rfl)
    have heq : (fun s => - E s) T - (fun s => - E s) 0 = E 0 - E T := by simp; ring
    rw [heq] at hle
    linarith
  · rw [intervalIntegral.integral_undef hint]
    have : 0 ≤ (1 / 2 : ℝ) * ‖(u₀ : L2VF)‖ ^ 2 := by positivity
    linarith

end LerayHopf
