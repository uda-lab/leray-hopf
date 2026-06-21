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

/-- Truncated square-root weight `min(√W ξ, k)` — bounded by `k`, continuous, nonneg. -/
noncomputable def sqrtViscousWeightTrunc (k : ℕ) (ξ : Domain3) : ℝ :=
  min (sqrtViscousWeight ξ) k

theorem sqrtViscousWeightTrunc_nonneg (k : ℕ) (ξ : Domain3) : 0 ≤ sqrtViscousWeightTrunc k ξ :=
  le_min (sqrtViscousWeight_nonneg ξ) (Nat.cast_nonneg k)

theorem sqrtViscousWeightTrunc_abs_le (k : ℕ) (ξ : Domain3) :
    |sqrtViscousWeightTrunc k ξ| ≤ k := by
  rw [abs_of_nonneg (sqrtViscousWeightTrunc_nonneg k ξ)]
  exact min_le_right _ _

theorem continuous_sqrtViscousWeightTrunc (k : ℕ) : Continuous (sqrtViscousWeightTrunc k) :=
  continuous_sqrtViscousWeight.min continuous_const

/-- The ℂ-coerced truncated weight is in `L^∞`. -/
theorem memLp_top_sqrtViscousWeightTrunc (k : ℕ) :
    MemLp (fun ξ : Domain3 => (sqrtViscousWeightTrunc k ξ : ℂ)) ⊤ (volume : Measure Domain3) := by
  refine memLp_top_of_bound
    (Complex.continuous_ofReal.comp (continuous_sqrtViscousWeightTrunc k)).aestronglyMeasurable
    (k : ℝ) ?_
  filter_upwards with ξ
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact sqrtViscousWeightTrunc_abs_le k ξ

/-- The truncated weights increase to `√W` pointwise: `min(√W,k) ↑ √W` as `k → ∞`. -/
theorem tendsto_sqrtViscousWeightTrunc (ξ : Domain3) :
    Filter.Tendsto (fun k : ℕ => sqrtViscousWeightTrunc k ξ) Filter.atTop
      (nhds (sqrtViscousWeight ξ)) := by
  -- For `k ≥ ⌈√W ξ⌉₊`, `min(√W ξ, k) = √W ξ`; the family is eventually constant.
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop (⌈sqrtViscousWeight ξ⌉₊)] with k hk
  symm
  rw [sqrtViscousWeightTrunc, min_eq_left]
  exact (Nat.le_ceil _).trans (Nat.cast_le.mpr hk)

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

/-- **ℝ-homogeneity of the bounded multiplier.** -/
theorem mulBdd_smul (m : Domain3 → ℝ)
    (hmem : MemLp (fun ξ : Domain3 => (m ξ : ℂ)) ⊤ (volume : Measure Domain3)) (r : ℝ)
    (g : L2C_R3) :
    mulBdd m hmem (r • g) = r • mulBdd m hmem g := by
  apply Lp.ext
  filter_upwards [mulBdd_coeFn m hmem (r • g), Lp.coeFn_smul r (mulBdd m hmem g),
    mulBdd_coeFn m hmem g, Lp.coeFn_smul r g] with ξ h1 h2 h3 h4
  rw [h1, h2, Pi.smul_apply, h4, h3, Pi.smul_apply]
  simp only [smul_eq_mul, Complex.real_smul]
  ring

/-- **Additivity of the bounded multiplier.** -/
theorem mulBdd_add (m : Domain3 → ℝ)
    (hmem : MemLp (fun ξ : Domain3 => (m ξ : ℂ)) ⊤ (volume : Measure Domain3)) (g h : L2C_R3) :
    mulBdd m hmem (g + h) = mulBdd m hmem g + mulBdd m hmem h := by
  apply Lp.ext
  filter_upwards [mulBdd_coeFn m hmem (g + h), Lp.coeFn_add (mulBdd m hmem g) (mulBdd m hmem h),
    mulBdd_coeFn m hmem g, mulBdd_coeFn m hmem h, Lp.coeFn_add g h] with ξ h1 h2 h3 h4 h5
  rw [h1, h2, Pi.add_apply, h3, h4, h5, Pi.add_apply, smul_add]

/-- **Squared `L²`-norm of `mulBdd m g` as the weighted integral** `∫ (m ξ)² ‖g ξ‖²`. -/
theorem norm_mulBdd_sq (m : Domain3 → ℝ)
    (hmem : MemLp (fun ξ : Domain3 => (m ξ : ℂ)) ⊤ (volume : Measure Domain3)) (g : L2C_R3) :
    ‖mulBdd m hmem g‖ ^ 2
      = ∫ ξ : Domain3, (m ξ) ^ 2 * ‖(g : Domain3 → ℂ) ξ‖ ^ 2 ∂(volume : Measure Domain3) := by
  rw [FourierL2.normSq_eq_integral_normSq_C (mulBdd m hmem g)]
  refine integral_congr_ae ?_
  filter_upwards [mulBdd_coeFn m hmem g] with ξ hξ
  rw [hξ]
  rw [norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- **Operator bound for the bounded multiplier:** `‖mulBdd m g‖ ≤ C ‖g‖` whenever `|m| ≤ C`
everywhere (the sup bound on `m` dominates the operator). -/
theorem norm_mulBdd_le (m : Domain3 → ℝ)
    (hmem : MemLp (fun ξ : Domain3 => (m ξ : ℂ)) ⊤ (volume : Measure Domain3)) {C : ℝ}
    (hC : 0 ≤ C) (hmle : ∀ ξ, |m ξ| ≤ C) (g : L2C_R3) :
    ‖mulBdd m hmem g‖ ≤ C * ‖g‖ := by
  have hsq : ‖mulBdd m hmem g‖ ^ 2 ≤ (C * ‖g‖) ^ 2 := by
    rw [norm_mulBdd_sq m hmem g, mul_pow, FourierL2.normSq_eq_integral_normSq_C g,
      ← integral_const_mul]
    have hgint : Integrable (fun ξ : Domain3 => ‖(g : Domain3 → ℂ) ξ‖ ^ 2)
        (volume : Measure Domain3) :=
      (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable g)).mp (Lp.memLp g)
    refine integral_mono_of_nonneg ?_ (hgint.const_mul (C ^ 2)) ?_
    · filter_upwards with ξ; positivity
    · filter_upwards with ξ
      have hmsq : (m ξ) ^ 2 ≤ C ^ 2 := by
        rw [← sq_abs (m ξ)]; exact pow_le_pow_left₀ (abs_nonneg _) (hmle ξ) 2
      have hgnn : (0:ℝ) ≤ ‖(g : Domain3 → ℂ) ξ‖ ^ 2 := by positivity
      exact mul_le_mul_of_nonneg_right hmsq hgnn
  have hrhs : 0 ≤ C * ‖g‖ := mul_nonneg hC (norm_nonneg _)
  nlinarith [norm_nonneg (mulBdd m hmem g), hsq, hrhs]

/-- **Subtractivity of the bounded multiplier.** -/
theorem mulBdd_sub (m : Domain3 → ℝ)
    (hmem : MemLp (fun ξ : Domain3 => (m ξ : ℂ)) ⊤ (volume : Measure Domain3)) (g h : L2C_R3) :
    mulBdd m hmem (g - h) = mulBdd m hmem g - mulBdd m hmem h := by
  apply Lp.ext
  filter_upwards [mulBdd_coeFn m hmem (g - h), Lp.coeFn_sub (mulBdd m hmem g) (mulBdd m hmem h),
    mulBdd_coeFn m hmem g, mulBdd_coeFn m hmem h, Lp.coeFn_sub g h] with ξ h1 h2 h3 h4 h5
  rw [h1, h2, Pi.sub_apply, h3, h4, h5, Pi.sub_apply, smul_sub]

/-- **Continuity of the bounded multiplier operator** (it is `C`-Lipschitz). -/
theorem continuous_mulBdd (m : Domain3 → ℝ)
    (hmem : MemLp (fun ξ : Domain3 => (m ξ : ℂ)) ⊤ (volume : Measure Domain3)) {C : ℝ}
    (hC : 0 ≤ C) (hmle : ∀ ξ, |m ξ| ≤ C) :
    Continuous (fun g => mulBdd m hmem g) := by
  refine (LipschitzWith.of_dist_le_mul (K := C.toNNReal) ?_).continuous
  intro g h
  rw [dist_eq_norm, dist_eq_norm, ← mulBdd_sub m hmem g h, Real.coe_toNNReal C hC]
  exact norm_mulBdd_le m hmem hC hmle (g - h)

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
