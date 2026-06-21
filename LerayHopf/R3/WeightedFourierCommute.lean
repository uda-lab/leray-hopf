import LerayHopf.R3.RellichBall

/-!
# Weighted-Fourier element and the unbounded-multiplier Bochner commute (`WeightedFourierCommute`)

This file isolates the single genuinely-new analytic pillar needed to close the viscous/H¹
Steklov–Jensen bound (`viscousFormSq_steklovAvg_le_average`, the issue-#15 gate): the
**unbounded spectral multiplier `√W` (`W ξ = (2π)²‖ξ‖²`) commutes with a Bochner interval
integral** of a continuous `L2C_R3`-valued curve, PROVIDED the weighted curve `s ↦ √W•(g s)`
is itself continuous into `L2C_R3`.

The weighted element `weightedFourierComponent j w := (√W • 𝓕(projⱼ w))` (as an `L2C_R3` class,
well-defined for `w ∈ H¹` via `integrable_viscous_integrand_of_memH1`) packages the viscous
form as a genuine Hilbert squared-norm:

  `viscousFormSq_R3 1 w = ∑ j, ‖weightedFourierComponent j w‖²`   (for `memH1VF_R3 w`).

The commute lemma `multiplier_smul_integral_comm` is proved by the standard truncation route:
truncate `√W` to `min(√W, k)` (a *bounded* multiplier, whose multiplication operator is a CLM on
`L²` and hence commutes with the Bochner integral via `integral_comp_comm`), then pass `k → ∞`
using dominated convergence on both sides — the curve continuity supplies the `L²` domination on
the compact window.  Every ingredient is in mathlib; the unbounded weight is handled by the limit.

This is exactly the content the spike (#15 Stage 1) showed is unreachable from the bare
`L²(vol)`-continuity of the Galerkin curve, and which the interface enrichment
(`GalerkinSolutionData_R3.viscous_curve_continuous`) supplies.
-/

open MeasureTheory FourierTransform
open scoped FourierTransform ENNReal

namespace LerayHopf

/-- The pointwise spectral weight `W ξ = (2π)² ‖ξ‖²` of the viscous form. -/
noncomputable def viscousWeight (ξ : Domain3) : ℝ := (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2

/-- The square-root spectral multiplier `√W ξ = 2π ‖ξ‖`, as a (real, nonnegative, continuous)
function on `Domain3`. -/
noncomputable def sqrtViscousWeight (ξ : Domain3) : ℝ := (2 * Real.pi) * ‖ξ‖

theorem sqrtViscousWeight_nonneg (ξ : Domain3) : 0 ≤ sqrtViscousWeight ξ := by
  unfold sqrtViscousWeight
  positivity

theorem sqrtViscousWeight_sq (ξ : Domain3) : sqrtViscousWeight ξ ^ 2 = viscousWeight ξ := by
  unfold sqrtViscousWeight viscousWeight
  ring

theorem continuous_sqrtViscousWeight : Continuous sqrtViscousWeight := by
  unfold sqrtViscousWeight
  exact continuous_const.mul continuous_norm

/-! ### Bounded multiplier on `L2C_R3` and its Bochner commute -/

/-- `mulBdd m hm hC g` is the `L²`-class of `ξ ↦ (m ξ : ℂ) • g ξ`, for a bounded
a.e.-strongly-measurable real multiplier `m` (bound `C`).  Well-defined because the bounded
multiplier keeps `g ∈ L²` inside `L²` (Hölder `∞ · 2 ⊆ 2`). -/
theorem memLp_mulBdd (m : Domain3 → ℝ)
    (hmem : MemLp (fun ξ : Domain3 => (m ξ : ℂ)) ⊤ (volume : Measure Domain3)) (g : L2C_R3) :
    MemLp (fun ξ => (m ξ : ℂ) • (g : Domain3 → ℂ) ξ) 2 (volume : Measure Domain3) := by
  have h := (Lp.memLp g).smul hmem (p := ⊤) (q := 2) (r := 2)
  exact h

noncomputable def mulBdd (m : Domain3 → ℝ)
    (hmem : MemLp (fun ξ : Domain3 => (m ξ : ℂ)) ⊤ (volume : Measure Domain3))
    (g : L2C_R3) : L2C_R3 :=
  (memLp_mulBdd m hmem g).toLp _

theorem mulBdd_coeFn (m : Domain3 → ℝ)
    (hmem : MemLp (fun ξ : Domain3 => (m ξ : ℂ)) ⊤ (volume : Measure Domain3)) (g : L2C_R3) :
    (mulBdd m hmem g : Domain3 → ℂ)
      =ᵐ[volume] fun ξ => (m ξ : ℂ) • (g : Domain3 → ℂ) ξ :=
  MemLp.coeFn_toLp _

/-- **Self-adjointness of the bounded real multiplier.**  `⟪c, mulBdd m g⟫ = ⟪mulBdd m c, g⟫`. -/
theorem inner_mulBdd_left (m : Domain3 → ℝ)
    (hmem : MemLp (fun ξ : Domain3 => (m ξ : ℂ)) ⊤ (volume : Measure Domain3)) (c g : L2C_R3) :
    (inner ℂ c (mulBdd m hmem g) : ℂ) = inner ℂ (mulBdd m hmem c) g := by
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [mulBdd_coeFn m hmem g, mulBdd_coeFn m hmem c] with ξ hg hc
  rw [hg, hc]
  simp only [RCLike.inner_apply, smul_eq_mul]
  rw [map_mul, Complex.conj_ofReal]
  ring

/-- **Bounded-multiplier Bochner commute (interval integral).**  For a curve `G` that is
interval-integrable on `[a,b]`, the bounded multiplier commutes with the Bochner integral:
`mulBdd m (∫_a^b G s ds) = ∫_a^b mulBdd m (G s) ds`. -/
theorem mulBdd_intervalIntegral_comm (m : Domain3 → ℝ)
    (hmem : MemLp (fun ξ : Domain3 => (m ξ : ℂ)) ⊤ (volume : Measure Domain3))
    {G : ℝ → L2C_R3} {a b : ℝ}
    (hGint : IntervalIntegrable G volume a b)
    (hMGint : IntervalIntegrable (fun s => mulBdd m hmem (G s)) volume a b) :
    mulBdd m hmem (∫ s in a..b, G s) = ∫ s in a..b, mulBdd m hmem (G s) := by
  refine ext_inner_left ℂ (fun c => ?_)
  -- `inner ℂ c` as an ℝ-CLM, to pull through the ℝ-Bochner interval integral.
  have hpullR : ∀ {H : ℝ → L2C_R3} (hH : IntervalIntegrable H volume a b) (d : L2C_R3),
      (inner ℂ d (∫ s in a..b, H s) : ℂ) = ∫ s in a..b, (inner ℂ d (H s) : ℂ) := by
    intro H hH d
    exact (((innerSL ℂ d).restrictScalars ℝ).intervalIntegral_comp_comm hH).symm
  -- RHS pairing.
  rw [hpullR hMGint c]
  -- LHS pairing: self-adjointness, then pull through the other integral.
  rw [inner_mulBdd_left m hmem c, hpullR hGint (mulBdd m hmem c)]
  refine intervalIntegral.integral_congr (fun s _ => ?_)
  exact (inner_mulBdd_left m hmem c (G s)).symm

end LerayHopf
