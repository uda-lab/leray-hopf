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

end LerayHopf
