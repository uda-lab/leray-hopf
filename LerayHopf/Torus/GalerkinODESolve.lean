import LerayHopf.Torus.GalerkinScheme
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.ODE.ExistUnique  -- issue #111 PR-3: the pinned mathlib now has this
  -- file, providing IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt,
  -- ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt, and
  -- ODE_solution_unique_of_mem_Icc_{right,left,''} directly (same as R3's fix).
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Normed.Module.FiniteDimension
import LerayHopf.Galerkin.QuadraticField  -- issue #112 PR-B: generic FieldForms witness (torusFieldForms)

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

/-! The torus finite-dim Galerkin ODE solver lives in the nested `LerayHopf.Torus` namespace so its
declaration names (`galerkinODE_vectorField`, `forwardGlobalSolution_exists`, …) do not collide with
the ℝ³ sibling's identically-shaped names in `LerayHopf` (the ℝ³ versions carry a
`SchwartzGalerkinBasis`/`R3NSForms` argument; the torus versions take `Torus3NSForms`).  The
deliverable `Torus.galerkinSolutionData_torus` is consumed by the downstream capstone. -/
namespace Torus

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

/-! ## B.0a — generic `FieldForms` witness (issue #112 PR-B, plan §3.3)

`torusFieldForms` packages `Torus3NSForms.b` and `stokesTestPairing` as a
`Galerkin.FieldForms (velocitySpan n)` instance, deduplicating this file's CLM tower against
`LerayHopf/Galerkin/QuadraticField.lean`'s generic construction. All 13 obligations are
discharged mechanically from the lemmas already proved above (B.0) and `Torus3NSForms`'s own
algebraic fields — no new proof content. -/

/-- The generic `FieldForms` witness for the torus Galerkin ODE layer: `bV` is `F.b` composed
with `velocitySpanToSigma`, `sV` is `stokesTestPairing` on the ambient `L2VF` coercion. -/
noncomputable def torusFieldForms (F : Torus3NSForms) (n : ℕ) :
    Galerkin.FieldForms (velocitySpan n) where
  bV u u' w := F.b (velocitySpanToSigma n u) (velocitySpanToSigma n u') (velocitySpanToSigma n w)
  bV_add_1 u u' v w := by
    show F.b (velocitySpanToSigma n (u + u')) (velocitySpanToSigma n v) (velocitySpanToSigma n w)
        = F.b (velocitySpanToSigma n u) (velocitySpanToSigma n v) (velocitySpanToSigma n w)
          + F.b (velocitySpanToSigma n u') (velocitySpanToSigma n v) (velocitySpanToSigma n w)
    rw [velocitySpanToSigma_add]; exact F.b_add_1 _ _ _ _
  bV_add_2 u v v' w := by
    show F.b (velocitySpanToSigma n u) (velocitySpanToSigma n (v + v')) (velocitySpanToSigma n w)
        = F.b (velocitySpanToSigma n u) (velocitySpanToSigma n v) (velocitySpanToSigma n w)
          + F.b (velocitySpanToSigma n u) (velocitySpanToSigma n v') (velocitySpanToSigma n w)
    rw [velocitySpanToSigma_add]; exact F.b_add_2 _ _ _ _
  bV_add_3 u v w w' := by
    show F.b (velocitySpanToSigma n u) (velocitySpanToSigma n v) (velocitySpanToSigma n (w + w'))
        = F.b (velocitySpanToSigma n u) (velocitySpanToSigma n v) (velocitySpanToSigma n w)
          + F.b (velocitySpanToSigma n u) (velocitySpanToSigma n v) (velocitySpanToSigma n w')
    rw [velocitySpanToSigma_add]; exact F.b_add_3 _ _ _ _
  bV_smul_1 a u v w := by
    show F.b (velocitySpanToSigma n (a • u)) (velocitySpanToSigma n v) (velocitySpanToSigma n w)
        = a * F.b (velocitySpanToSigma n u) (velocitySpanToSigma n v) (velocitySpanToSigma n w)
    rw [velocitySpanToSigma_smul]; exact F.b_smul_1 _ _ _ _
  bV_smul_2 a u v w := by
    show F.b (velocitySpanToSigma n u) (velocitySpanToSigma n (a • v)) (velocitySpanToSigma n w)
        = a * F.b (velocitySpanToSigma n u) (velocitySpanToSigma n v) (velocitySpanToSigma n w)
    rw [velocitySpanToSigma_smul]; exact F.b_smul_2 _ _ _ _
  bV_smul_3 a u v w := by
    show F.b (velocitySpanToSigma n u) (velocitySpanToSigma n v) (velocitySpanToSigma n (a • w))
        = a * F.b (velocitySpanToSigma n u) (velocitySpanToSigma n v) (velocitySpanToSigma n w)
    rw [velocitySpanToSigma_smul]; exact F.b_smul_3 _ _ _ _
  bV_diag_zero v := F.b_self_zero (velocitySpanToSigma n v)
  sV u w := stokesTestPairing (u : L2VF) (w : L2VF)
  sV_symm u w := stokesTestPairing_symm (u : L2VF) (w : L2VF)
  sV_add_right u w w' := by
    show stokesTestPairing (u : L2VF) ((w + w' : velocitySpan n) : L2VF)
        = stokesTestPairing (u : L2VF) (w : L2VF) + stokesTestPairing (u : L2VF) (w' : L2VF)
    rw [show ((w + w' : velocitySpan n) : L2VF) = (w : L2VF) + (w' : L2VF) from rfl]
    exact stokesTestPairing_add_right n (u : L2VF) (w : L2VF) (w' : L2VF) (velocityP_fixes_coe n u)
  sV_smul_right a u w := by
    show stokesTestPairing (u : L2VF) ((a • w : velocitySpan n) : L2VF)
        = a * stokesTestPairing (u : L2VF) (w : L2VF)
    rw [show ((a • w : velocitySpan n) : L2VF) = a • (w : L2VF) from rfl]
    exact stokesTestPairing_smul_right n a (u : L2VF) (w : L2VF) (velocityP_fixes_coe n u)
  sV_diag_nonneg v := by
    show (0 : ℝ) ≤ stokesTestPairing (v : L2VF) (v : L2VF)
    rw [stokesTestPairing_diag]
    exact viscousFormSq_nonneg zero_le_one _

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

/-- **Equality bridge (issue #112 PR-B, plan §3.3).** The concrete lane vector field equals
the generic `FieldForms` construction — proved by `ext_inner_right` + both specs, per the
plan's equality-bridge rule (no redefinition of `galerkinODE_vectorField`). -/
theorem galerkinODE_vectorField_eq_generic (F : Torus3NSForms) (ν : ℝ) (n : ℕ) :
    galerkinODE_vectorField F ν n = (torusFieldForms F n).vectorField ν := by
  funext u
  refine ext_inner_right ℝ (fun w => ?_)
  rw [Submodule.coe_inner (velocitySpan n) (galerkinODE_vectorField F ν n u) w,
    galerkinODE_vectorField_spec F ν n u w, (torusFieldForms F n).vectorField_spec]
  rfl

/-! ## B.2 — C1: the Galerkin field is `C¹` (issue #112 PR-B: now a corollary of the generic
`Galerkin.FieldForms.vectorField_contDiff` via `galerkinODE_vectorField_eq_generic`; the local
CLM tower `rieszSymmCLM`/`bInner`/`bMid`/`bOut`/`stokesInner`/`stokesOut`/
`galerkinODE_bilinearPart`/`galerkinODE_linearPart`/`galerkinODE_vectorField_eq_parts` was
deleted as dead code, deduplicated against `LerayHopf/Galerkin/QuadraticField.lean`). -/

/-- **C1 (the enabler).** The Galerkin field `G_n` is `C¹` on the finite-dim `Vₙ`. -/
theorem galerkinODE_vectorField_contDiff (F : Torus3NSForms) (ν : ℝ) (n : ℕ) :
    ContDiff ℝ 1 (galerkinODE_vectorField F ν n) := by
  rw [galerkinODE_vectorField_eq_generic]
  exact (torusFieldForms F n).vectorField_contDiff ν

/-! ## B.3 — A1/A2/A3: dissipation identity + the forward a-priori energy bound

Mirror of `R3/GalerkinODESolve.lean`'s A1/A2/A3 (domain-agnostic given B.1/B.2 + the diagonal). -/

/-- Reflect an ambient `HasDerivAt` of a `Vₙ`-curve back to the intrinsic one — the reverse of
`Galerkin.coe_hasDerivAt`, via the orthogonal-projection retraction `orthogonalProjectionOnto`
(a continuous linear left inverse of the subspace inclusion). Lets the ambient-curve energy/
a-priori corollaries below feed the generic intrinsic-curve `Galerkin` lemmas. -/
private theorem hasDerivAt_intrinsic_of_coe (n : ℕ) (c : ℝ → velocitySpan n)
    (v : velocitySpan n) (t : ℝ)
    (h : HasDerivAt (fun s => (c s : L2VF)) (v : L2VF) t) :
    HasDerivAt c v t := by
  have hcomp := ((velocitySpan n).orthogonalProjectionOnto).hasFDerivAt.comp_hasDerivAt t h
  simpa [Function.comp_def] using hcomp

/-- **A1.** `⟪v, G_n v⟫ ≤ 0` for `v ∈ Vₙ` (dissipation at a point), from R2 + `b_self_zero` +
`stokesTestPairing_diag`. -/
theorem galerkinField_inner_self_nonpos (F : Torus3NSForms) (ν : ℝ) (n : ℕ) (hν : 0 < ν)
    (v : velocitySpan n) :
    inner (𝕜 := ℝ) (v : L2VF) (galerkinODE_vectorField F ν n v : L2VF) ≤ 0 := by
  rw [← Submodule.coe_inner, galerkinODE_vectorField_eq_generic]
  exact (torusFieldForms F n).inner_self_vectorField_nonpos hν v

/-- **A2.** Along any local solution `c' = G_n(c)`, the energy `½‖c t‖²` has derivative
`-ν·viscousFormSq 1 (c t) ≤ 0`. -/
theorem energy_hasDerivAt_of_localSolution (F : Torus3NSForms) (ν : ℝ) (n : ℕ)
    (c : ℝ → velocitySpan n) (t : ℝ)
    (hc : HasDerivAt (fun s => (c s : L2VF))
      (galerkinODE_vectorField F ν n (c t) : L2VF) t) :
    HasDerivAt (fun s => (1 / 2 : ℝ) * ‖(c s : L2VF)‖ ^ 2)
      (- ν * viscousFormSq 1 (c t : L2VF)) t := by
  have hc' : HasDerivAt c ((torusFieldForms F n).vectorField ν (c t)) t := by
    rw [← galerkinODE_vectorField_eq_generic]
    exact hasDerivAt_intrinsic_of_coe n c _ t hc
  have hgen := (torusFieldForms F n).energy_hasDerivAt ν c t hc'
  have hval : -((ν : ℝ) * (torusFieldForms F n).sV (c t) (c t))
      = - ν * viscousFormSq 1 (c t : L2VF) := by
    show -((ν : ℝ) * stokesTestPairing (c t : L2VF) (c t : L2VF))
      = - ν * viscousFormSq 1 (c t : L2VF)
    rw [stokesTestPairing_diag]; ring
  have hfun : (fun s => (1 / 2 : ℝ) * ‖c s‖ ^ 2)
      = fun s => (1 / 2 : ℝ) * ‖(c s : L2VF)‖ ^ 2 := by
    funext s; rw [Submodule.norm_coe]
  rw [hval, hfun] at hgen
  exact hgen

/-- **A3.** Any forward local solution on `[0, T]` stays in the ball `‖c t‖ ≤ ‖c 0‖`. -/
theorem norm_le_of_forwardSolution (F : Torus3NSForms) (ν : ℝ) (n : ℕ) (hν : 0 < ν)
    (c : ℝ → velocitySpan n) {T : ℝ} (hT : 0 ≤ T)
    (hsol : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt (fun s => (c s : L2VF))
      (galerkinODE_vectorField F ν n (c t) : L2VF) t) :
    ∀ t ∈ Icc (0 : ℝ) T, ‖(c t : L2VF)‖ ≤ ‖(c 0 : L2VF)‖ := by
  have hdiss : ∀ w : velocitySpan n,
      inner (𝕜 := ℝ) w ((torusFieldForms F n).vectorField ν w) ≤ 0 :=
    fun w => (torusFieldForms F n).inner_self_vectorField_nonpos hν w
  have hsol' : ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivAt c ((torusFieldForms F n).vectorField ν (c t)) t := by
    intro t ht
    rw [← galerkinODE_vectorField_eq_generic]
    exact hasDerivAt_intrinsic_of_coe n c _ t (hsol t ht)
  intro t ht
  have hbound := Galerkin.norm_le_of_forwardSolution_of_dissipative
    ((torusFieldForms F n).vectorField ν) hdiss c hT hsol' t ht
  rw [Submodule.norm_coe, Submodule.norm_coe]
  exact hbound

/-! ## B.5 — G1: forward-global existence by tiling (the core)

Mirror of `R3/GalerkinODESolve.lean`'s G1 chain, over `velocitySpan n` /
`galerkinODE_vectorField F ν n`.  The argument is domain-agnostic; only the subspace and field
names change. -/

/-- **G1 helper (uniform `δ`).** A single uniform local-existence time on the a-priori ball. -/
theorem galerkinField_uniform_local_time (F : Torus3NSForms) (ν : ℝ) (n : ℕ) (R : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x₀ ∈ closedBall (0 : velocitySpan n) R, ∀ t₀ : ℝ,
      ∃ α : ℝ → velocitySpan n, α t₀ = x₀ ∧
        ∀ t ∈ Ioo (t₀ - δ) (t₀ + δ),
          HasDerivAt α (galerkinODE_vectorField F ν n (α t)) t :=
  Galerkin.uniform_local_time (galerkinODE_vectorField F ν n)
    (galerkinODE_vectorField_contDiff F ν n) R

/-- **G1 helper (splice-agreement).** Two local solutions agreeing at one point agree on the
overlap. -/
theorem galerkinField_solution_agree (F : Torus3NSForms) (ν : ℝ) (n : ℕ)
    (α β : ℝ → velocitySpan n) {a b t₀ : ℝ} (hab : a ≤ b) (ht₀ : t₀ ∈ Icc a b)
    (hαβ : α t₀ = β t₀)
    (hα : ∀ t ∈ Icc a b, HasDerivAt α (galerkinODE_vectorField F ν n (α t)) t)
    (hβ : ∀ t ∈ Icc a b, HasDerivAt β (galerkinODE_vectorField F ν n (β t)) t) :
    ∀ t ∈ Icc a b, α t = β t :=
  Galerkin.solution_agree (galerkinODE_vectorField F ν n)
    (galerkinODE_vectorField_contDiff F ν n) α β hab ht₀ hαβ hα hβ

/-- **G1 (THE core).** Forward-global existence: there is `c : ℝ → Vₙ` with
`c 0 = velocityProjection_n n u₀` and `∀ t ≥ 0, HasDerivAt (↑∘c) (G_n (c t)) t`. -/
theorem forwardGlobalSolution_exists (F : Torus3NSForms) (ν : ℝ) (hν : 0 < ν)
    (u₀ : L2Sigma) (n : ℕ) :
    ∃ c : ℝ → velocitySpan n,
      (c 0 : L2VF) = velocityProjection_n n (u₀ : L2VF) ∧
      ∀ t, 0 ≤ t → HasDerivAt (fun s => (c s : L2VF))
        (galerkinODE_vectorField F ν n (c t) : L2VF) t := by
  have hx₀mem : velocityProjection_n n (u₀ : L2VF) ∈ velocitySpan n := velocityP_initial_mem n u₀
  obtain ⟨c, hc0, hd⟩ := (torusFieldForms F n).forwardGlobalSolution_exists hν
    (⟨velocityProjection_n n (u₀ : L2VF), hx₀mem⟩ : velocitySpan n)
  refine ⟨c, ?_, fun t ht => ?_⟩
  · rw [hc0]
  · rw [galerkinODE_vectorField_eq_generic]
    exact Galerkin.coe_hasDerivAt (velocitySpan n) c _ t (hd t ht)

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

/-- `t ↦ ‖c t‖²` is continuous (the ambient curve is differentiable, hence continuous). -/
private theorem normSq_curve_continuous (F : Torus3NSForms) (ν : ℝ) (n : ℕ)
    (c : ℝ → velocitySpan n)
    (hd : ∀ s, 0 ≤ s → HasDerivAt (fun r => (c r : L2VF))
      (galerkinODE_vectorField F ν n (c s) : L2VF) s)
    {T : ℝ} :
    ContinuousOn (fun t => ‖(c t : L2VF)‖ ^ 2) (Set.Icc (0 : ℝ) T) := by
  refine ContinuousOn.pow (fun x hx => ?_) 2
  exact (hd x hx.1).continuousAt.norm.continuousWithinAt

/-- **reg_bound (E3 torus form, planner risk #3).**
`∫₀ᵀ h1EnergySq (c t) ≤ T‖u₀‖² + ‖u₀‖²/(2ν)`.

Split `h1EnergySq = ‖·‖² + (2π)²⁻¹·viscousFormSq 1`; the L²-part integrates to `≤ T‖u₀‖²`
(pointwise `‖c t‖² ≤ ‖u₀‖²` from A3 + nonexpansive `Pₙ`), and the gradient part is
`≤ (2π)²⁻¹·‖u₀‖²/(2ν) ≤ ‖u₀‖²/(2ν)` (since `(2π)²⁻¹ ≤ 1`) via `galerkin_viscous_bound`. -/
private theorem galerkin_reg_bound_curve (F : Torus3NSForms) (ν : ℝ) (hν : 0 < ν) (n : ℕ)
    (u₀ : L2Sigma) (c : ℝ → velocitySpan n)
    (hc0 : (c 0 : L2VF) = velocityProjection_n n (u₀ : L2VF))
    (hd : ∀ s, 0 ≤ s → HasDerivAt (fun r => (c r : L2VF))
      (galerkinODE_vectorField F ν n (c s) : L2VF) s)
    {T : ℝ} (hT : 0 < T) :
    ∫ t in (0 : ℝ)..T, h1EnergySq (c t : L2VF) ≤
      T * ‖(u₀ : L2VF)‖ ^ 2 + ‖(u₀ : L2VF)‖ ^ 2 / (2 * ν) := by
  -- Pointwise split of the integrand on `Vₙ`.
  have hsplitfun : ∀ t, h1EnergySq (c t : L2VF)
      = ‖(c t : L2VF)‖ ^ 2 + ((2 * Real.pi) ^ 2)⁻¹ * viscousFormSq 1 (c t : L2VF) :=
    fun t => h1EnergySq_eq_L2_add_viscous n (c t : L2VF) (velocityP_fixes_span n (c t))
  -- L²-part: `∫ ‖c t‖² ≤ T‖u₀‖²`.
  have hL2cont : ContinuousOn (fun t => ‖(c t : L2VF)‖ ^ 2) (Set.Icc (0 : ℝ) T) :=
    normSq_curve_continuous F ν n c hd
  have hL2int : IntervalIntegrable (fun t => ‖(c t : L2VF)‖ ^ 2) MeasureTheory.volume 0 T :=
    (hL2cont.intervalIntegrable_of_Icc hT.le)
  have hpt : ∀ t ∈ Set.Icc (0 : ℝ) T, ‖(c t : L2VF)‖ ^ 2 ≤ ‖(u₀ : L2VF)‖ ^ 2 := by
    intro t ht
    have hnorm : ‖(c t : L2VF)‖ ≤ ‖(c 0 : L2VF)‖ :=
      norm_le_of_forwardSolution F ν n hν c hT.le (fun s hs => hd s hs.1) t ht
    rw [hc0] at hnorm
    have hle : ‖(c t : L2VF)‖ ≤ ‖(u₀ : L2VF)‖ :=
      hnorm.trans (velocityProjection_n_norm_le n (u₀ : L2VF))
    exact pow_le_pow_left₀ (norm_nonneg _) hle 2
  have hL2bound : ∫ t in (0 : ℝ)..T, ‖(c t : L2VF)‖ ^ 2 ≤ T * ‖(u₀ : L2VF)‖ ^ 2 := by
    calc ∫ t in (0 : ℝ)..T, ‖(c t : L2VF)‖ ^ 2
        ≤ ∫ _t in (0 : ℝ)..T, ‖(u₀ : L2VF)‖ ^ 2 := by
          apply intervalIntegral.integral_mono_on hT.le hL2int (intervalIntegrable_const) hpt
      _ = T * ‖(u₀ : L2VF)‖ ^ 2 := by
          rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  -- gradient part: `(2π)²⁻¹ ∫ viscousFormSq 1 ≤ (2π)²⁻¹ · ‖u₀‖²/(2ν) ≤ ‖u₀‖²/(2ν)`.
  have hvisc := galerkin_viscous_bound F ν hν n u₀ c hc0 hd hT
  have hvnn : 0 ≤ ‖(u₀ : L2VF)‖ ^ 2 / (2 * ν) := by positivity
  have hpiinv : ((2 * Real.pi) ^ 2)⁻¹ ≤ 1 := by
    rw [inv_le_one₀ (by positivity)]
    nlinarith [Real.two_le_pi]
  -- integrability bookkeeping: viscous integrable iff h1 integrable; use case-split.
  by_cases hint : IntervalIntegrable
      (fun t => viscousFormSq 1 (c t : L2VF)) MeasureTheory.volume (0 : ℝ) T
  · -- both parts integrable: split the integral.
    have hsum : (fun t => h1EnergySq (c t : L2VF))
        = fun t => ‖(c t : L2VF)‖ ^ 2 + ((2 * Real.pi) ^ 2)⁻¹ * viscousFormSq 1 (c t : L2VF) :=
      funext hsplitfun
    rw [hsum, intervalIntegral.integral_add hL2int (hint.const_mul _),
      intervalIntegral.integral_const_mul]
    have hgrad : ((2 * Real.pi) ^ 2)⁻¹ * ∫ t in (0:ℝ)..T, viscousFormSq 1 (c t : L2VF)
        ≤ ‖(u₀ : L2VF)‖ ^ 2 / (2 * ν) := by
      have hge : 0 ≤ ∫ t in (0:ℝ)..T, viscousFormSq 1 (c t : L2VF) := by
        apply intervalIntegral.integral_nonneg hT.le
        intro t _; exact viscousFormSq_nonneg zero_le_one _
      calc ((2 * Real.pi) ^ 2)⁻¹ * ∫ t in (0:ℝ)..T, viscousFormSq 1 (c t : L2VF)
          ≤ 1 * ∫ t in (0:ℝ)..T, viscousFormSq 1 (c t : L2VF) :=
            mul_le_mul_of_nonneg_right hpiinv hge
        _ = ∫ t in (0:ℝ)..T, viscousFormSq 1 (c t : L2VF) := one_mul _
        _ ≤ ‖(u₀ : L2VF)‖ ^ 2 / (2 * ν) := hvisc
    linarith
  · -- viscous non-integrable ⟹ h1 non-integrable (they differ by a continuous term); integral 0.
    have hh1int : ¬ IntervalIntegrable (fun t => h1EnergySq (c t : L2VF))
        MeasureTheory.volume (0 : ℝ) T := by
      intro hh1
      apply hint
      have heq : (fun t => viscousFormSq 1 (c t : L2VF))
          = fun t => ((2 * Real.pi) ^ 2) *
              (h1EnergySq (c t : L2VF) - ‖(c t : L2VF)‖ ^ 2) := by
        funext t
        rw [hsplitfun t]
        have hne : ((2 * Real.pi) ^ 2) ≠ 0 := by positivity
        field_simp
        ring
      rw [heq]
      exact ((hh1.sub hL2int).const_mul _)
    rw [intervalIntegral.integral_undef hh1int]
    have : 0 ≤ T * ‖(u₀ : L2VF)‖ ^ 2 := by positivity
    linarith

/-! ### D — `galerkinSolutionData_torus` (the deliverable)

The torus `GalerkinSolutionData` (`SolutionInterfaces.lean`) now quantifies `u_hasDeriv`/`u_ode` over
forward time `∀ t, 0 ≤ t →` (issue #24 soundness correction, matching the merged ℝ³ sibling
`GalerkinSolutionData_R3`).  This is exactly what the forward-global Galerkin solver (G1) supplies:
the quadratic field blows up in finite *backward* time, so the previous all-`t` form was an
un-physical over-claim the global solver could not honor.  All 8 fields are assembled below
sorry-free / axiom-free. -/

/-- Forward-time differentiability of the assembled curve (proved; `t ≥ 0`). -/
private theorem solutionCurve_hasDeriv_forward (F : Torus3NSForms) (ν : ℝ) (n : ℕ)
    (c : ℝ → velocitySpan n)
    (hd : ∀ s, 0 ≤ s → HasDerivAt (fun r => (c r : L2VF))
      (galerkinODE_vectorField F ν n (c s) : L2VF) s)
    (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt (fun s => (velocitySpanToSigma n (c s) : L2VF))
      (deriv (fun s => (velocitySpanToSigma n (c s) : L2VF)) t) t := by
  have heq : (fun s => (velocitySpanToSigma n (c s) : L2VF)) = fun s => (c s : L2VF) := by
    funext s; rw [velocitySpanToSigma_coe]
  rw [heq]
  exact (hd t ht).differentiableAt.hasDerivAt

/-- The ambient derivative of the assembled curve equals the field, at forward times. -/
private theorem solutionCurve_deriv_eq (F : Torus3NSForms) (ν : ℝ) (n : ℕ)
    (c : ℝ → velocitySpan n)
    (hd : ∀ s, 0 ≤ s → HasDerivAt (fun r => (c r : L2VF))
      (galerkinODE_vectorField F ν n (c s) : L2VF) s)
    (t : ℝ) (ht : 0 ≤ t) :
    deriv (fun s => (velocitySpanToSigma n (c s) : L2VF)) t
      = (galerkinODE_vectorField F ν n (c t) : L2VF) := by
  have heq : (fun s => (velocitySpanToSigma n (c s) : L2VF)) = fun s => (c s : L2VF) := by
    funext s; rw [velocitySpanToSigma_coe]
  rw [heq]
  exact (hd t ht).deriv

/-- **D — the per-`n` Galerkin solver (the deliverable).**  Assemble all 8 fields of the torus
`GalerkinSolutionData` from the forward-global curve `forwardGlobalSolution_exists` (G1) + the
Riesz characterization R2, the dissipation bounds, and the H¹ regularity — sorry-free, axiom-free.

The weak Galerkin ODE field `u_ode` is DERIVED from the autonomous field equation `c' = G_n(c)`
via R2 (`galerkinODE_vectorField_spec`): an arbitrary test `w : L2Sigma` fixed by `Pₙ` is viewed in
`Vₙ` (`mem_velocitySpan_of_fixed`, using `w ∈ L2Sigma`), then the spec converts the curve derivative
into the `-ν·stokes - b` weak form.  Forward-time (`0 ≤ t`) per the corrected structure. -/
noncomputable def galerkinSolutionData_torus (F : Torus3NSForms) (ν : ℝ) (hν : 0 < ν)
    (u₀ : L2Sigma) (n : ℕ) :
    GalerkinSolutionData F ν u₀ n := by
  -- `GalerkinSolutionData` lives in `Type`, so extract the curve via `Exists.choose`
  -- (cannot `obtain` an `Exists` into `Type`).
  have hex := forwardGlobalSolution_exists F ν hν u₀ n
  set c : ℝ → velocitySpan n := hex.choose with hc
  have hc0 : (c 0 : L2VF) = velocityProjection_n n (u₀ : L2VF) := hex.choose_spec.1
  have hd : ∀ s, 0 ≤ s → HasDerivAt (fun r => (c r : L2VF))
      (galerkinODE_vectorField F ν n (c s) : L2VF) s := hex.choose_spec.2
  refine
    { u := fun t => velocitySpanToSigma n (c t)
      u_initial := ?_
      u_inVn := ?_
      u_hasDeriv := ?_
      u_ode := ?_
      reg_mem := ?_
      energy_bound := ?_
      reg_bound := ?_ }
  · -- `u 0 = ⟨Pₙ u₀, …⟩`.  Equate underlying `L2VF` vectors via `hc0`.
    apply Subtype.ext
    show (c 0 : L2VF) = velocityProjection_n n (u₀ : L2VF)
    exact hc0
  · -- The curve stays in `Vₙ`: `(u t : L2VF) = c t` is fixed by `Pₙ`.
    intro t
    show (c t : L2VF) = velocityProjection_n n (c t : L2VF)
    exact (velocityP_fixes_span n (c t)).symm
  · -- Forward differentiability of the ambient curve.
    intro t ht
    exact solutionCurve_hasDeriv_forward F ν n c hd t ht
  · -- Derive the weak Galerkin ODE from `c' = G_n(c)` + R2 (forward time).
    intro t ht w hw
    -- View `w` as an element of `Vₙ` (fixed by `Pₙ`, and divergence-free).
    have hwmem : (w : L2VF) ∈ velocitySpan n :=
      mem_velocitySpan_of_fixed n (w : L2VF) w.2 hw.symm
    set wV : velocitySpan n := ⟨(w : L2VF), hwmem⟩ with hwV
    have hbw : velocitySpanToSigma n wV = w := by apply Subtype.ext; rfl
    -- Rewrite the ambient derivative via the field equation, then R2.
    rw [solutionCurve_deriv_eq F ν n c hd t ht]
    have hspec := galerkinODE_vectorField_spec F ν n (c t) wV
    show inner (𝕜 := ℝ) (galerkinODE_vectorField F ν n (c t) : L2VF) (w : L2VF)
        + ν * stokesTestPairing (velocitySpanToSigma n (c t) : L2VF) (w : L2VF)
        + F.b (velocitySpanToSigma n (c t)) (velocitySpanToSigma n (c t)) w = 0
    rw [show (w : L2VF) = (wV : L2VF) from rfl, hspec, ← hbw]
    simp only [velocitySpanToSigma_coe]
    ring
  · -- H¹ regularity: each `Vₙ`-curve point is in H¹ (finite Fourier support).
    intro t
    exact galerkinCurve_reg_mem n (velocitySpanToSigma n (c t) : L2VF)
      (velocityP_fixes_span n (c t))
  · -- Uniform energy bound (E2).
    intro t ht
    exact galerkin_energy_bound_curve F ν hν n u₀ c hc0 hd t ht
  · -- Uniform regularity bound (E3 torus form).
    intro T hT
    exact galerkin_reg_bound_curve F ν hν n u₀ c hc0 hd hT

end Torus

end LerayHopf
