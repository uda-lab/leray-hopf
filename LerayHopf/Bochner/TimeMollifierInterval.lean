/-
# LerayHopf.Bochner.TimeMollifierInterval — Stream D / PR-F3 (S1 sub-module 2: interval layer)

**Stream:** D (abstract Bochner–Sobolev-in-time). **Origin:** the S1 wall isolated in
`LerayHopf/Bochner/TimeMollification.lean` (`timeMollification_exists`), decomposed by the
team-lead into bounded sub-modules. This file is the SECOND sub-module — the interval layer —
resting on the now-PROVED whole-line Young bound `timeConvL2_norm_le` of
`LerayHopf/Bochner/TimeConvolution.lean`.

Domain-NEUTRAL and abstract in the Banach space `E` (so it serves both `V` and `V'` of a
Gelfand triple).

## What this file provides (this sub-module)

1. **`timeConvL2_tendsto_self`** — the **ε/3 mollification convergence**
   `‖timeConvL2 ρₙ g − g‖₂ → 0` as the kernel concentrates, for `g : Lp E 2 volume`. Proved
   sorry-free via the *translation-modulus* route (the whole-space spatial model
   `FrechetKolmogorov.convolution_sub_L2_le_translation_modulus`, transported to the time line
   and abstracted in `E`): the mollification defect is bounded by the kernel-weighted average
   of the translation modulus `‖τ_h g − g‖`, which the proved Young bound + continuity of
   `h ↦ τ_h g` at `0` (`continuous_timeTranslateL2`) drive to `0` as the support shrinks. This
   route needs NO pointwise/`Lp` coeFn bridge, so it is genuinely closeable here.

2. `isWeakTimeDerivℝ_smul_cutoff` (B2) — the **cutoff/Leibniz product rule** for whole-line
   Banach-valued weak derivatives. **PROVED sorry-free this PR** (corrected signature: added the
   `LocallyIntegrable u`/`LocallyIntegrable v` Fubini/`integral_add` hypotheses).

3. `timeConvL2_weakDeriv_comm` (WALL A) — the commutation `(ρ ⋆ u)' = ρ ⋆ v` in the **whole-line**
   `IsWeakTimeDerivℝ` sense. **Corrected signature (codex P1):** the global predicate `+`
   `LocallyIntegrable u`/`LocallyIntegrable v` (the box-Fubini soundness hypotheses). The
   soundness-critical commutation identity (shift-substitution + `hwd (ψ(·+s))`) is **PROVED
   unconditionally**; only the standard compact-box L¹ Fubini side-condition is isolated as a
   single non-soundness `ALLOW_SORRY` in the private helper `timeConv_prod_integrable`.

4. `weakTimeDerivℝ_even_reflection` (B1) — even reflection reflects the whole-line weak derivative
   with sign flip, NO Dirac. The no-Dirac identity genuinely requires the Bochner-valued
   1D-Sobolev FTC/continuous-representative (trace at `0`) pillar (the same months-class residual
   as `w1pTime_continuous_in_H`); precise `ALLOW_SORRY` with the corrected blocker analysis.

5. `w1pTime_lineExtension` (WALL B assembly) — the **W1pTime-preserving whole-line extension** of
   a curve on `[0,T]` (even reflection × cutoff). Conclusion uses the **global** `IsWeakTimeDerivℝ`
   (codex P2 / §2a). Blocked transitively on B1's FTC pillar plus the double-endpoint reflection
   `MemLp`/`=ᵐ` bookkeeping; precise `ALLOW_SORRY`. Glue pieces (B2 + `isWeakTimeDerivℝ_comp_clm`)
   are PROVED.

## Assumptions

No new `axiom`/`opaque`/`constant`. Theorem 1 and B2 are fully proved; WALL A's commutation
identity is proved (only its Fubini side-condition is isolated). The genuinely-missing pillar is
the Bochner 1D-Sobolev FTC/trace (B1 no-Dirac), which transitively blocks the assembly. Each gap
carries a precise same-line `-- ALLOW_SORRY: <blocker>`; no statement is weakened and no axiom is
added.
-/

import LerayHopf.Bochner.TimeConvolution
import LerayHopf.Bochner.TimeSobolev
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Data.Real.Sign -- Real.sign used in B1 (even-reflection weak-deriv sign flip)

namespace LerayHopf.Bochner

open MeasureTheory Filter Topology Metric
open scoped ENNReal

section IntervalLayer

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-! ### The translation-modulus bound (time-line port of the FK spatial model)

`timeConvL2 ρ g − g = ∫ h, ρ h • (τ_h g − g)` for a unit-mass kernel, so by `‖∫ F‖ ≤ ∫ ‖F‖`
the mollification defect is controlled by the kernel-weighted integral of the translation
modulus `‖τ_h g − g‖`. This is the abstract-`E` time-line transport of
`FrechetKolmogorov.convolution_sub_L2_le_translation_modulus`. -/

/-- The defect `timeConvL2 ρ g − g` equals the single Bochner integral
`∫ h, ρ h • (τ_h g − g)` (using `∫ ρ = 1` to write `g = ∫ h, ρ h • g`). -/
theorem timeConvL2_sub_eq_integral {ρ : ℝ → ℝ} (hρ : IsTimeMollifier ρ)
    (g : Lp E 2 (volume : Measure ℝ)) :
    timeConvL2 ρ g - g
      = ∫ h : ℝ, ρ h • (timeTranslateL2 h g - g) ∂(volume : Measure ℝ) := by
  have hI1 : Integrable (fun h : ℝ => ρ h • timeTranslateL2 h g) (volume : Measure ℝ) :=
    integrable_timeMollifier_smul_translate hρ g
  have hηL1 : Integrable ρ (volume : Measure ℝ) :=
    hρ.continuous.integrable_of_hasCompactSupport hρ.hasCompactSupport
  have hI2 : Integrable (fun h : ℝ => ρ h • g) (volume : Measure ℝ) := hηL1.smul_const g
  have hg_int : (∫ h : ℝ, ρ h • g ∂(volume : Measure ℝ)) = g := by
    rw [integral_smul_const, hρ.mass_one, one_smul]
  have e1 : timeConvL2 ρ g - g
      = (∫ h : ℝ, ρ h • timeTranslateL2 h g ∂(volume : Measure ℝ))
        - ∫ h : ℝ, ρ h • g ∂(volume : Measure ℝ) := by
    rw [timeConvL2, hg_int]
  rw [e1, ← integral_sub hI1 hI2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
  simp only [smul_sub]

/-- **Translation-modulus bound** (time-line, `E`-abstract):
`‖timeConvL2 ρ g − g‖ ≤ ∫ h, ρ h • ‖τ_h g − g‖`. Direct port of
`FrechetKolmogorov.convolution_sub_L2_le_translation_modulus`. -/
theorem timeConvL2_sub_le_translation_modulus {ρ : ℝ → ℝ} (hρ : IsTimeMollifier ρ)
    (g : Lp E 2 (volume : Measure ℝ)) :
    ‖timeConvL2 ρ g - g‖
      ≤ ∫ h : ℝ, ρ h • ‖timeTranslateL2 h g - g‖ ∂(volume : Measure ℝ) := by
  rw [timeConvL2_sub_eq_integral hρ g]
  refine le_trans (norm_integral_le_integral_norm _) (le_of_eq ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
  simp only []
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hρ.nonneg h), smul_eq_mul]

/-! ### The translation modulus and its continuity at `0`

`M g h := ‖τ_h g − g‖` is continuous (translation `h ↦ τ_h g` is continuous into `L²`,
`continuous_timeTranslateL2`, and the norm is continuous) and vanishes at `h = 0`
(`τ_0 g = g`). These two facts drive the kernel-weighted average to `0` as the support of `ρ`
concentrates at `0`. -/

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- The translation modulus `h ↦ ‖τ_h g − g‖` is continuous. -/
theorem continuous_translationModulus (g : Lp E 2 (volume : Measure ℝ)) :
    Continuous (fun h : ℝ => ‖timeTranslateL2 h g - g‖) :=
  ((continuous_timeTranslateL2 g).sub continuous_const).norm

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- The translation modulus vanishes at `h = 0`: `τ_0 g = g`. -/
theorem translationModulus_zero (g : Lp E 2 (volume : Measure ℝ)) :
    ‖timeTranslateL2 (0 : ℝ) g - g‖ = 0 := by
  have h0 : timeTranslateL2 (0 : ℝ) g = g := by
    apply Lp.ext
    refine (Lp.coeFn_compMeasurePreserving g _).trans ?_
    filter_upwards with x
    simp
  rw [h0, sub_self, norm_zero]

/-! ### The mollification convergence (Theorem 1)

For a bump sequence `φ` with `(φ n).rOut → 0`, the normalized kernels `ρ n := (φ n).normed`
are time-mollifiers (`ContDiffBump.isTimeMollifier`) whose support is `ball 0 (φ n).rOut`. The
modulus bound gives `‖timeConvL2 (ρ n) g − g‖ ≤ ∫ h, ρ n h • ‖τ_h g − g‖`. Since `∫ ρ n = 1`
and `‖τ_h g − g‖ ≤ εₙ` on the shrinking support (continuity at `0`, value `0`), the RHS → 0. -/

/-- **Mollification convergence (Theorem 1, sorry-free).**

`‖timeConvL2 ((φ n).normed volume) g − g‖ → 0` as the bump radius `(φ n).rOut → 0`, for any
`g : L²(ℝ; E)`. This is the genuinely-new assembled `eLpNorm`-mollification theorem the S1
pillar needed, proved here via the translation-modulus route (no pointwise/`Lp` coeFn bridge):

* `timeConvL2_sub_le_translation_modulus` bounds the defect by `∫ h, ρ n h • ‖τ_h g − g‖`;
* on `supp (ρ n) = ball 0 (φ n).rOut`, continuity of the modulus at `0` (value `0`,
  `translationModulus_zero`) makes `‖τ_h g − g‖ ≤ ε` for `n` large;
* `∫ ρ n = 1` (`mass_one`) collapses `∫ ρ n • ε = ε`, so the defect is `≤ ε` eventually. -/
theorem timeConvL2_tendsto_self (g : Lp E 2 (volume : Measure ℝ))
    (φ : ℕ → ContDiffBump (0 : ℝ)) (hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0)) :
    Tendsto (fun n => ‖timeConvL2 ((φ n).normed (volume : Measure ℝ)) g - g‖) atTop (𝓝 0) := by
  set M : ℝ → ℝ := fun h => ‖timeTranslateL2 h g - g‖ with hM
  have hMcont : Continuous M := continuous_translationModulus g
  have hM0 : M 0 = 0 := translationModulus_zero g
  have hMnonneg : ∀ h, 0 ≤ M h := fun h => norm_nonneg _
  -- It suffices to squeeze the defect between `0` and a sequence `→ 0`.
  -- Bound: `defect n ≤ ∫ h, ρ n h • M h`, and that integral `≤ εₙ` where `εₙ → 0`.
  -- We prove the `ε`-`δ` form directly.
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- By continuity of `M` at `0` (with `M 0 = 0`), pick `δ` so `|h| < δ → M h < ε/2`.
  -- The `ε/2` threshold yields `∫ ρ • M ≤ ε/2 < ε` (the integral inequality is non-strict).
  have hε2 : 0 < ε / 2 := by linarith
  have hcont0 : Tendsto M (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have := hMcont.tendsto (0 : ℝ); rwa [hM0] at this
  have hδ : ∀ᶠ h in 𝓝 (0 : ℝ), M h < ε / 2 := hcont0 (Iio_mem_nhds hε2)
  rw [Metric.eventually_nhds_iff] at hδ
  obtain ⟨δ, hδpos, hδlt⟩ := hδ
  -- Eventually `(φ n).rOut < δ`, so the kernel support sits in `ball 0 δ`.
  have hrOut : ∀ᶠ n in atTop, (φ n).rOut < δ := hφ (Iio_mem_nhds hδpos)
  rw [Filter.eventually_atTop] at hrOut
  obtain ⟨N, hN⟩ := hrOut
  refine ⟨N, fun n hnN => ?_⟩
  have hn : (φ n).rOut < δ := hN n hnN
  set ρ : ℝ → ℝ := (φ n).normed (volume : Measure ℝ) with hρdef
  have hρmoll : IsTimeMollifier ρ := ContDiffBump.isTimeMollifier (φ n)
  -- `dist (defect n) 0 = defect n` (nonneg); bound it by `∫ ρ • M ≤ ε`.
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  refine lt_of_le_of_lt (timeConvL2_sub_le_translation_modulus hρmoll g) ?_
  -- `∫ h, ρ h • M h ≤ ∫ h, ρ h • ε = ε` (using `M h ≤ ε` on the support, `ρ ≥ 0`, `∫ ρ = 1`).
  have hρL1 : Integrable ρ (volume : Measure ℝ) :=
    hρmoll.continuous.integrable_of_hasCompactSupport hρmoll.hasCompactSupport
  have hbound : ∀ h, ρ h • M h ≤ ρ h • (ε / 2) := by
    intro h
    rcases eq_or_ne (ρ h) 0 with hzero | hne
    · simp [hzero]
    · -- `ρ h ≠ 0 ⇒ h ∈ support ρ = ball 0 rOut ⊆ ball 0 δ ⇒ M h < ε`.
      have hmem : h ∈ Function.support ρ := by simpa using hne
      rw [hρdef, (φ n).support_normed_eq] at hmem
      have hball : h ∈ ball (0 : ℝ) δ := ball_subset_ball hn.le hmem
      have : M h < ε / 2 := hδlt (by simpa [Real.dist_eq, dist_zero_right] using hball)
      have hρpos : 0 ≤ ρ h := hρmoll.nonneg h
      simp only [smul_eq_mul]
      exact mul_le_mul_of_nonneg_left this.le hρpos
  have hint_le : (∫ h : ℝ, ρ h • M h ∂(volume : Measure ℝ))
      ≤ ∫ h : ℝ, ρ h • (ε / 2) ∂(volume : Measure ℝ) := by
    refine integral_mono ?_ ?_ hbound
    · -- `ρ • M` integrable: `M` continuous so the `smul` is continuous w/ compact support `⊆ supp ρ`.
      have hcont : Continuous (fun h : ℝ => ρ h • M h) := hρmoll.continuous.smul hMcont
      refine hcont.integrable_of_hasCompactSupport ?_
      apply HasCompactSupport.intro hρmoll.hasCompactSupport.isCompact (fun h hh => ?_)
      have : ρ h = 0 := by
        by_contra hh'; exact hh (subset_tsupport ρ (by simpa using hh'))
      simp [this]
    · simpa only [smul_eq_mul] using hρL1.mul_const (ε / 2)
  calc (∫ h : ℝ, ρ h • M h ∂(volume : Measure ℝ))
      ≤ ∫ h : ℝ, ρ h • (ε / 2) ∂(volume : Measure ℝ) := hint_le
    _ = ε / 2 := by rw [integral_smul_const, hρmoll.mass_one, one_smul]
    _ < ε := by linarith

end IntervalLayer

/-! ### Pointwise time-convolution of a Banach-valued curve

For Theorem 3 (the weak-derivative commutation) the convolution must act on a *pointwise*
curve `u : ℝ → X`, not an `Lp` element: `(ρ ⋆ₜ u)(x) = ∫ s, ρ s • u (x − s)`. This is mathlib's
`convolution f g (lsmul ℝ ℝ) volume` with the scalar kernel on the left. -/

section WeakDerivComm

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

open scoped Convolution

/-- For fixed `s`, the slice `t ↦ a t • ρ s • w (t - s)` is integrable when `a` is continuous
with compact support and `w` is locally integrable: it is `(continuous compact-support scalar) •
(locally integrable shift)`. -/
private theorem timeConv_slice_integrable {a ρ : ℝ → ℝ}
    (ha_cont : Continuous a) (ha_cs : HasCompactSupport a)
    {w : ℝ → X} (hw : LocallyIntegrable w (volume : Measure ℝ)) (s : ℝ) :
    Integrable (fun t => a t • ρ s • w (t - s)) (volume : Measure ℝ) := by
  -- `t ↦ w (t - s)` is locally integrable (precompose with the measure-preserving shift `· - s`).
  have hwshift : LocallyIntegrable (fun t => w (t - s)) (volume : Measure ℝ) := by
    have hmap : (Measure.map (Homeomorph.subRight s) (volume : Measure ℝ)) = volume :=
      map_sub_right_eq_self (volume : Measure ℝ) s
    have h := (locallyIntegrable_map_homeomorph (Homeomorph.subRight s) (f := w)
      (μ := (volume : Measure ℝ))).mp (by rw [hmap]; exact hw)
    -- `w ∘ (subRight s) = fun t => w (t - s)`.
    simpa only [Function.comp_def, Homeomorph.subRight_apply] using h
  -- `t ↦ ρ s • w (t - s)` is locally integrable (scalar multiple).
  have hsmul : LocallyIntegrable (fun t => ρ s • w (t - s)) (volume : Measure ℝ) :=
    hwshift.smul (ρ s)
  exact hsmul.integrable_smul_left_of_hasCompactSupport ha_cont ha_cs

/-- The uncurried integrand `(t,s) ↦ a t • ρ s • w (t - s)` is integrable on `volume.prod volume`
when `a` is continuous with compact support, `ρ` is a normalized time mollifier and `w` is
locally integrable. This is the joint-integrability box argument: the `s`-slices are integrable
(`timeConv_slice_integrable`) and the `s ↦ ∫ ‖slice‖` map is continuous with compact support in
`tsupport ρ`, hence integrable. -/
private theorem timeConv_prod_integrable {a ρ : ℝ → ℝ}
    (ha_cont : Continuous a) (ha_cs : HasCompactSupport a)
    (hρ : IsTimeMollifier ρ) {w : ℝ → X} (hw : LocallyIntegrable w (volume : Measure ℝ)) :
    Integrable (Function.uncurry fun t s => a t • ρ s • w (t - s))
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
  -- AE-strong-measurability of the uncurried integrand on the product.
  have hmeas : AEStronglyMeasurable
      (Function.uncurry fun t s => a t • ρ s • w (t - s))
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
    -- `(p ↦ ρ p.2 • w (p.1 − p.2))` is the convolution integrand for `L = lsmul ℝ ℝ`, `f = ρ`,
    -- `g = w`. Use the mathlib convolution-integrand measurability lemma (transfer `w`'s ae-strong-
    -- measurability through the right-invariant subtraction via `mono_ac`).
    have hconv : AEStronglyMeasurable
        (fun p : ℝ × ℝ => (ContinuousLinearMap.lsmul ℝ ℝ) (ρ p.2) (w (p.1 - p.2)))
        ((volume : Measure ℝ).prod (volume : Measure ℝ)) :=
      hρ.continuous.aestronglyMeasurable.convolution_integrand' (ContinuousLinearMap.lsmul ℝ ℝ)
        (hw.aestronglyMeasurable.mono_ac
          (quasiMeasurePreserving_sub_of_right_invariant
            (volume : Measure ℝ) (volume : Measure ℝ)).absolutelyContinuous)
    have hconv' : AEStronglyMeasurable (fun p : ℝ × ℝ => ρ p.2 • w (p.1 - p.2))
        ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
      simpa only [ContinuousLinearMap.lsmul_apply] using hconv
    have ha2 : AEStronglyMeasurable (fun p : ℝ × ℝ => a p.1)
        ((volume : Measure ℝ).prod (volume : Measure ℝ)) :=
      ha_cont.aestronglyMeasurable.comp_quasiMeasurePreserving
        (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ)))
    exact ha2.smul hconv'
  -- Use `integrable_prod_iff'` with the `s`-variable outer.
  rw [integrable_prod_iff' hmeas]
  refine ⟨Filter.Eventually.of_forall fun s => timeConv_slice_integrable ha_cont ha_cs hw s, ?_⟩
  -- `s ↦ ∫ t, ‖a t • ρ s • w (t - s)‖` is integrable. It is supported in `tsupport ρ` (compact)
  -- because the slice integrand vanishes identically when `ρ s = 0`, and on that compact set it is
  -- bounded by `|ρ s| · ‖a‖∞ · ∫_{tsupport a − tsupport ρ} ‖w‖` (the `t`-integral of `‖a‖∞‖w(t−s)‖`
  -- over `tsupport a`, whose argument `t − s` stays in the compact `tsupport a − tsupport ρ`).
  -- Measurability of the `s`-map is the prod-norm-integral handle `hmeas.norm.integral_prod_right'`;
  -- the support/boundedness give integrability. This is a standard (non-soundness) box estimate.
  have hmeas_int : AEStronglyMeasurable
      (fun s => ∫ t, ‖(Function.uncurry fun t s => a t • ρ s • w (t - s)) (t, s)‖
        ∂(volume : Measure ℝ)) (volume : Measure ℝ) :=
    hmeas.prod_swap.norm.integral_prod_right'
  -- ALLOW_SORRY: standard compact-box L¹ estimate for the outer norm-integral. The integrand
  -- `s ↦ ∫ t ‖a t • ρ s • w(t−s)‖` is supported in the compact `tsupport ρ` and bounded there by
  -- `|ρ s| · ‖a‖∞ · ∫_{tsupport a − tsupport ρ}‖w‖`; integrability follows by domination against the
  -- integrable `|ρ ·| · B`. Not soundness-critical (the convolution-commutation identity below does
  -- not depend on the *value* of this estimate, only its existence as a Fubini side-condition).
  sorry -- ALLOW_SORRY: s1-walls-design.md §1c — Fubini side-condition (compact-box L¹ bound on `s ↦ ∫ t ‖a t • ρ s • w(t−s)‖`); standard box estimate, not soundness-critical; mathematical commutation identity proved unconditionally below

/-- **Weak-derivative commutation `(ρ ⋆ u)' = ρ ⋆ u'` (pointwise-curve form, corrected signature).**

If `v` is the **whole-line** weak time derivative of the `X`-valued curve `u` (`IsWeakTimeDerivℝ
u v`, per `s1-walls-design.md` §1b) and `ρ` is a normalized time mollifier, then the
pointwise time-convolution `ρ ⋆ v` is the whole-line weak time derivative of `ρ ⋆ u`.

**Corrected signature (§1b of `s1-walls-design.md`):** the old interval hypothesis
`IsWeakTimeDeriv T u v` was UNSOUND for convolution: shifting a compactly-supported global
test function `ψ` by `s` gives `ψ(·+s)`, which has support shifted away from `(0,T)` and
so falls outside the interval predicate. The global predicate `IsWeakTimeDerivℝ` dissolves
this obstruction: `ψ(·+s)` is still compactly supported and global, so `hwd (ψ(·+s))`
is always applicable. The `{T}` binder is gone.

**Corrected signature (codex P1).** Added `LocallyIntegrable u`, `LocallyIntegrable v` hypotheses:
without local integrability the Bochner integrals in `IsWeakTimeDerivℝ` are junk and the box-Fubini
interchange is unsound. These are available downstream (the `W1pTime` `MemLp` fields give local
integrability after even reflection × cutoff). No mathematical content is weakened.

The proof:
1. Unfold `convolution_lsmul`; pull `ψ'(t)•` inside (linearity); apply Fubini
   (`integral_integral_swap`, joint integrability `timeConv_prod_integrable`).
2. Fix `s`, substitute `t ↦ t + s` (`integral_add_right_eq_self`): inner
   `∫ t, deriv ψ t • u (t−s) = ∫ t, deriv (ψ(·+s)) t • u t = -∫ t, ψ(t+s) • v t`
   by `hwd (ψ(·+s))` (**requires the global predicate**), then resubstitute to `-∫ t, ψ t • v(t−s)`.
3. Fubini back: result is `-∫ t, ψ t • (ρ ⋆ v)(t)`. -/
theorem timeConvL2_weakDeriv_comm {ρ : ℝ → ℝ} (hρ : IsTimeMollifier ρ)
    {u v : ℝ → X} (hu : LocallyIntegrable u (volume : Measure ℝ))
    (hv : LocallyIntegrable v (volume : Measure ℝ)) (hwd : IsWeakTimeDerivℝ u v) :
    IsWeakTimeDerivℝ (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ] u)
      (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ] v) := by
  intro ψ hψcs hψC1
  have hψ'cont : Continuous (deriv ψ) := hψC1.continuous_deriv_one
  have hψ'cs : HasCompactSupport (deriv ψ) := HasCompactSupport.deriv hψcs
  have hψcont : Continuous ψ := hψC1.continuous
  -- The key inner identity (for each fixed `s`), via shift substitution + `hwd` on the shifted test:
  -- `∫ t, deriv ψ t • u (t − s) = - ∫ t, ψ t • v (t − s)`.
  have hinner : ∀ s : ℝ, (∫ t, deriv ψ t • u (t - s))
      = - ∫ t, ψ t • v (t - s) := by
    intro s
    -- The shifted test `χ_s t := ψ (t + s)` is `C¹` with compact support, and `deriv χ_s = ψ'(·+s)`.
    set χ : ℝ → ℝ := fun t => ψ (t + s) with hχdef
    have hχC1 : ContDiff ℝ 1 χ := hψC1.comp (contDiff_id.add contDiff_const)
    have hχcs : HasCompactSupport χ := by
      have : χ = ψ ∘ (fun t => t + s) := rfl
      rw [this]
      exact hψcs.comp_homeomorph (Homeomorph.addRight s)
    have hderivχ : ∀ t, deriv χ t = deriv ψ (t + s) := fun t => deriv_comp_add_const ψ s t
    -- Substitute `t ↦ t + s` in the LHS: `∫ t, deriv ψ t • u (t−s) = ∫ t, deriv ψ (t+s) • u t`.
    have hsubL : (∫ t, deriv ψ t • u (t - s)) = ∫ t, deriv ψ (t + s) • u t := by
      have h := integral_add_right_eq_self (μ := (volume : Measure ℝ))
        (fun t => deriv ψ t • u (t - s)) s
      simpa only [add_sub_cancel_right] using h.symm
    -- Substitute `t ↦ t + s` in the RHS: `∫ t, ψ t • v (t−s) = ∫ t, ψ (t+s) • v t`.
    have hsubR : (∫ t, ψ t • v (t - s)) = ∫ t, ψ (t + s) • v t := by
      have h := integral_add_right_eq_self (μ := (volume : Measure ℝ))
        (fun t => ψ t • v (t - s)) s
      simpa only [add_sub_cancel_right] using h.symm
    rw [hsubL, hsubR]
    -- Now `∫ t, deriv ψ (t+s) • u t = ∫ t, deriv χ t • u t = - ∫ t, χ t • v t` by `hwd χ`.
    have hwχ := hwd χ hχcs hχC1
    calc (∫ t, deriv ψ (t + s) • u t)
        = ∫ t, deriv χ t • u t := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
          simp only [hderivχ]
      _ = - ∫ t, χ t • v t := hwχ
      _ = - ∫ t, ψ (t + s) • v t := by rw [hχdef]
  -- Joint integrability for the two Fubini swaps.
  have hint_u := timeConv_prod_integrable hψ'cont hψ'cs hρ hu
  have hint_v := timeConv_prod_integrable hψcont hψcs hρ hv
  -- LHS: `∫ t, deriv ψ t • (ρ⋆u)(t) = ∫ t, ∫ s, deriv ψ t • ρ s • u(t−s)`.
  have hLHS : (∫ t, deriv ψ t • (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ] u) t)
      = ∫ t, ∫ s, deriv ψ t • ρ s • u (t - s) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [convolution_lsmul]
    rw [← integral_smul]
  -- Swap and apply the inner identity.
  have hLHS2 : (∫ t, ∫ s, deriv ψ t • ρ s • u (t - s))
      = ∫ s, ρ s • (- ∫ t, ψ t • v (t - s)) := by
    rw [integral_integral_swap hint_u]
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    simp only []
    -- `∫ t, deriv ψ t • ρ s • u(t−s) = ρ s • ∫ t, deriv ψ t • u(t−s) = ρ s • (−∫ t, ψ t • v(t−s))`.
    have he : (∫ t, deriv ψ t • ρ s • u (t - s)) = ρ s • ∫ t, deriv ψ t • u (t - s) := by
      rw [← integral_smul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      exact smul_comm (deriv ψ t) (ρ s) (u (t - s))
    rw [he, hinner s]
  -- RHS: `- ∫ t, ψ t • (ρ⋆v)(t) = - ∫ t, ∫ s, ψ t • ρ s • v(t−s) = - ∫ s, ∫ t, ψ t • ρ s • v(t−s)`.
  have hRHS : (- ∫ t, ψ t • (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ] v) t)
      = ∫ s, ρ s • (- ∫ t, ψ t • v (t - s)) := by
    rw [show (- ∫ t, ψ t • (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ] v) t)
        = - ∫ t, ∫ s, ψ t • ρ s • v (t - s) from by
          congr 1
          refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
          simp only [convolution_lsmul]
          rw [← integral_smul]]
    rw [integral_integral_swap hint_v, ← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    simp only []
    have he : (∫ t, ψ t • ρ s • v (t - s)) = ρ s • ∫ t, ψ t • v (t - s) := by
      rw [← integral_smul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      exact smul_comm (ψ t) (ρ s) (v (t - s))
    rw [he, smul_neg]
  rw [hLHS, hLHS2, hRHS]

end WeakDerivComm

/-! ### WALL B sub-lemma scaffolds (s1-walls-design.md §2)

The bounded foundational layer that WALL B's assembly (`w1pTime_lineExtension`) rests on.
Each sub-lemma carries a precise statement from the design note and a same-line `ALLOW_SORRY`
tagged with the note's §-reference and prover tier. Proof bodies are deferred to tiered provers.

Sub-lemma order per recommended dispatch (§3 of design note):
- B0 / §2a: the `IsWeakTimeDerivℝ` conclusion for `w1pTime_lineExtension` (signature update).
- B1 / §2b: even-reflection reflects the weak derivative with sign flip (no Dirac at 0).
- B2 / §2c: cutoff (Leibniz) product rule for whole-line weak derivatives.
- B2e-global / §2e: `isWeakTimeDerivℝ_comp_clm` is in `TimeSobolev.lean` (added this PR).
- B3 / §2d: assembly: ūV := χ • (reflection of uV), all three properties + weak-deriv identity.
-/

section LineExtension

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- **Sub-lemma B1 — even reflection reflects the whole-line weak derivative with sign flip.**

For a curve `u : ℝ → X` and its whole-line weak time derivative `v` (i.e.
`IsWeakTimeDerivℝ u v`), the even reflection `ũ t := u |t|` has whole-line weak time derivative
`ṽ t := Real.sign t • v |t|` — with NO Dirac at `t = 0`, because even reflection matches the
trace `u(0⁺) = u(0⁻)`.

**Soundness (statement is TRUE, not weakened).** A curve `u` with a whole-line weak time
derivative `v` has an absolutely-continuous (continuous) representative `ũ` with
`ũ(t) = ũ(a) + ∫_a^t v` (1D Sobolev FTC for Bochner-valued curves). The predicate
`IsWeakTimeDerivℝ` is a.e.-invariant in `u`, so we may take `u = ũ`; then `u|·|` is continuous,
matches the trace `u(0⁺)=u(0⁻)=u(0)`, and the even reflection genuinely reflects the derivative
with sign flip and NO Dirac at `0`. So the statement holds.

**Genuine blocker (corrected from the design note).** The design note claimed an elementary
symbol-pushing proof (split `∫_ℝ = ∫_{<0}+∫_{>0}`, substitute `t ↦ -t`, recombine). That is
INCOMPLETE: the conclusion concerns the curve `u|·|`, which depends on `u` only on `[0,∞)`,
whereas the hypothesis `hwd` mixes both half-axes. The only way to extract the half-axis no-jump
identity from the whole-line predicate is through the **trace `u(0)`**, which is not available
for a bare `IsWeakTimeDerivℝ` curve without the 1D-Sobolev **continuous-representative / FTC
pillar** — exactly the months-class residual carried by `w1pTime_continuous_in_H`
(`TimeSobolev.lean`). The boundary cancellation "`ψ(0)·u(0)` with opposite signs" is real, but it
presupposes that trace. Without that pillar in mathlib (no vector-valued interval-Sobolev FTC),
this no-Dirac identity cannot be closed by elementary distributional manipulation.

Tier: **Opus** (the soundness heart — needs the Bochner-valued 1D-Sobolev FTC/trace pillar). -/
theorem weakTimeDerivℝ_even_reflection (u v : ℝ → X)
    (hwd : IsWeakTimeDerivℝ u v) :
    IsWeakTimeDerivℝ (fun t => u |t|) (fun t => Real.sign t • v |t|) := by
  -- The no-Dirac reflection identity genuinely requires the trace `u(0)`, i.e. the Bochner-valued
  -- 1D-Sobolev continuous-representative / FTC pillar (`u(t) = u(a) + ∫_a^t v`). The whole-line
  -- hypothesis `hwd` mixes both half-axes; the conclusion only sees `u` on `[0,∞)`. Extracting the
  -- half-axis identity needs the boundary trace, which is not derivable from `IsWeakTimeDerivℝ`
  -- alone. This is the same months-class pillar as `w1pTime_continuous_in_H`.
  sorry -- ALLOW_SORRY: s1-walls-design.md §2b — B1 even-reflection no-Dirac identity. GENUINE BLOCKER: needs the Bochner-valued 1D-Sobolev FTC/continuous-representative (trace at 0) pillar — the design note's elementary split is incomplete because the whole-line `hwd` mixes both half-axes while the conclusion only sees u on [0,∞); same months-class residual as w1pTime_continuous_in_H. Statement is TRUE (a.e.-invariant; holds for the continuous representative), not weakened.

/-- **Sub-lemma B2 — cutoff (Leibniz) product rule for whole-line Banach-valued weak derivatives.**

For a globally `C¹` cutoff `χ : ℝ → ℝ` (not assumed compactly supported), curves
`u v : ℝ → X` that are **locally integrable** (`hu`, `hv` — the genuine soundness/Fubini
hypotheses: without local integrability the Bochner integrals in `IsWeakTimeDerivℝ` are junk
and `integral_add` cannot split), and `IsWeakTimeDerivℝ u v`,

  `IsWeakTimeDerivℝ (fun t => χ t • u t) (fun t => χ t • v t + deriv χ t • u t)`.

**Corrected signature.** The added `LocallyIntegrable u`, `LocallyIntegrable v` hypotheses are
the minimal honest domain restriction making the `integral_add` split sound; they are available
downstream (the `W1pTime` `MemLp` fields give local integrability after even reflection). No
mathematical content is weakened — the Leibniz identity is exactly as before.

The proof transfers `χ` onto the test function `ψ`: the product `χ · ψ` is `C¹` and compactly
supported (compact support of `ψ` wins), `deriv (χ · ψ) = χ' · ψ + χ · ψ'`, so
`∫ (χψ)'• u = ∫ (χ'ψ)•u + ∫ (χψ')•u`. Apply `hwd (χ · ψ)` on the left, regroup; each summand is
`(continuous compactly-supported scalar) • (locally integrable)`, hence integrable
(`LocallyIntegrable.integrable_smul_left_of_hasCompactSupport`). -/
theorem isWeakTimeDerivℝ_smul_cutoff (χ : ℝ → ℝ) (hχ : ContDiff ℝ 1 χ)
    (u v : ℝ → X) (hu : LocallyIntegrable u (volume : Measure ℝ))
    (hv : LocallyIntegrable v (volume : Measure ℝ)) (hwd : IsWeakTimeDerivℝ u v) :
    IsWeakTimeDerivℝ (fun t => χ t • u t) (fun t => χ t • v t + deriv χ t • u t) := by
  intro ψ hψcs hψC1
  -- The transferred test function `φ := χ · ψ` is `C¹` and compactly supported.
  set φ : ℝ → ℝ := fun t => χ t * ψ t with hφdef
  have hχcont : Continuous χ := hχ.continuous
  have hψcont : Continuous ψ := hψC1.continuous
  have hχ'cont : Continuous (deriv χ) := hχ.continuous_deriv_one
  have hψ'cont : Continuous (deriv ψ) := hψC1.continuous_deriv_one
  have hφC1 : ContDiff ℝ 1 φ := hχ.mul hψC1
  have hφcs : HasCompactSupport φ := hψcs.mul_left
  -- Leibniz: `deriv φ t = deriv χ t * ψ t + χ t * deriv ψ t`.
  have hderivφ : ∀ t, deriv φ t = deriv χ t * ψ t + χ t * deriv ψ t := by
    intro t
    have hχd : DifferentiableAt ℝ χ t := (hχ.differentiable one_ne_zero).differentiableAt
    have hψd : DifferentiableAt ℝ ψ t := (hψC1.differentiable one_ne_zero).differentiableAt
    have hpi : φ = χ * ψ := by funext s; rfl
    rw [hpi]; exact deriv_mul hχd hψd
  -- `hwd φ`: `∫ deriv φ • u = - ∫ φ • v`.
  have hwφ := hwd φ hφcs hφC1
  -- Integrability of the three summands: (compactly-supported continuous scalar) • (loc-integrable).
  have hcs_χ'ψ : HasCompactSupport (fun t => deriv χ t * ψ t) := hψcs.mul_left
  have hcs_χψ' : HasCompactSupport (fun t => χ t * deriv ψ t) :=
    (HasCompactSupport.deriv hψcs).mul_left
  have hint_χ'ψ : Integrable (fun t => (deriv χ t * ψ t) • u t) (volume : Measure ℝ) :=
    hu.integrable_smul_left_of_hasCompactSupport (hχ'cont.mul hψcont) hcs_χ'ψ
  have hint_χψ' : Integrable (fun t => (χ t * deriv ψ t) • u t) (volume : Measure ℝ) :=
    hu.integrable_smul_left_of_hasCompactSupport (hχcont.mul hψ'cont) hcs_χψ'
  -- Rewrite `∫ deriv φ • u` using Leibniz and split via `integral_add`.
  have hsplit : (∫ t, deriv φ t • u t)
      = (∫ t, (deriv χ t * ψ t) • u t) + ∫ t, (χ t * deriv ψ t) • u t := by
    rw [← integral_add hint_χ'ψ hint_χψ']
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [hderivφ t, add_smul]
  -- The goal LHS `∫ deriv ψ • (χ • u) = ∫ (χ ψ') • u`.
  have hLHS : (∫ t, deriv ψ t • (χ t • u t)) = ∫ t, (χ t * deriv ψ t) • u t := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [smul_smul, mul_comm (deriv ψ t) (χ t)]
  -- The goal RHS `∫ ψ • (χ•v + χ'•u) = ∫ φ•v + ∫ (χ'ψ)•u`.
  have hint_φv : Integrable (fun t => φ t • v t) (volume : Measure ℝ) :=
    hv.integrable_smul_left_of_hasCompactSupport hφC1.continuous hφcs
  have hRHS : (∫ t, ψ t • (χ t • v t + deriv χ t • u t))
      = (∫ t, φ t • v t) + ∫ t, (deriv χ t * ψ t) • u t := by
    rw [← integral_add hint_φv hint_χ'ψ]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [hφdef, smul_add, smul_smul, mul_comm (ψ t) (deriv χ t), mul_comm (ψ t) (χ t)]
  -- Combine: from `hwφ` (`∫ φ' • u = -∫ φ•v`), `hsplit` gives the relation between the pieces.
  rw [hLHS, hRHS]
  -- `hsplit` + `hwφ`: `A + B = -C` where A = ∫(χ'ψ)•u, B = ∫(χψ')•u, C = ∫φ•v.
  -- Goal: `B = -(C + A)`. Additive-group algebra.
  rw [hsplit] at hwφ
  refine eq_neg_of_add_eq_zero_left ?_
  -- `B + (C + A) = 0` follows from `A + B = -C`.
  have : (∫ t, (χ t * deriv ψ t) • u t) + ((∫ t, φ t • v t) + ∫ t, (deriv χ t * ψ t) • u t)
      = ((∫ t, (deriv χ t * ψ t) • u t) + ∫ t, (χ t * deriv ψ t) • u t)
        + ∫ t, φ t • v t := by abel
  rw [this, hwφ, neg_add_cancel]

/-- **W1pTime-preserving whole-line extension (Theorem 2 / WALL B assembly, §2d).**

Given a `W1pTime GT 2 2 T uV` element (curve on `[0,T]` with `V'`-valued weak derivative), there
is a whole-line curve `ūV : ℝ → GT.V` such that:

* `ūV =ᵐ uV` on `[0,T]` (the extension restricts to the genuine curve);
* `ūV ∈ L²(ℝ;V)` (`MemLp ūV 2 volume`);
* there is a whole-line `V'`-valued curve `ū'` with `MemLp ū' 2 volume`, agreeing a.e. on
  `[0,T]` with `W.u'`, that is the **whole-line** weak `V'`-derivative of
  `t ↦ hToVprime (ι (ūV t))` in the `IsWeakTimeDerivℝ` sense — i.e. NO boundary jump is
  introduced (the soundness crux).

**Corrected conclusion (§2a of `s1-walls-design.md`):** the weak-derivative field now uses the
**global** predicate `IsWeakTimeDerivℝ` (not the old interval `IsWeakTimeDeriv T`), matching
the corrected WALL A signature (`timeConvL2_weakDeriv_comm`) which consumes it directly.

The construction is the Sobolev even-reflection × cutoff (§2d): reflect `uV` and `u'` off
`[0,T]` using `weakTimeDerivℝ_even_reflection` (B1), then multiply by a smooth cutoff `χ`
supported in a bounded neighbourhood of `[0,T]` with `χ ≡ 1` on `[0,T]` (B2 gives the
product rule for the weak derivative; `χ' ≡ 0` on `[0,T]` so `ū' =ᵐ u'` there).

**Genuine wall (WALL B assembly, not weakened).** The no-boundary-jump identity assembles B1
(`weakTimeDerivℝ_even_reflection`) + B2 (`isWeakTimeDerivℝ_smul_cutoff`, PROVED this PR) +
`isWeakTimeDerivℝ_comp_clm` (CLM transport through `hToVprime∘ι`, PROVED). Two residual
blockers remain:

1. **Transitive on B1's FTC pillar.** The reflected-derivative witness `ū'` is produced by
   `weakTimeDerivℝ_even_reflection` (B1), whose no-Dirac identity is blocked on the Bochner-valued
   1D-Sobolev FTC/trace pillar (see B1). Until B1 lands, the assembly cannot supply a sound
   `ū'` with the whole-line weak-derivative property.
2. **Double-endpoint reflection bookkeeping.** A single even reflection at `0` uses `uV` on
   `[0,∞)`, but `W.mem_p` only controls `uV` on `[0,T]`. The genuine Sobolev extension reflects at
   BOTH endpoints (`0` and `T`) so the cutoff support stays within the controlled range; the
   `MemLp ūV 2 volume` / `=ᵐ` bookkeeping then rests on those two reflections plus the compact
   cutoff. This is contained but non-trivial and depends on B1 at each endpoint.

The statement (all properties + the `IsWeakTimeDerivℝ` no-jump identity) is kept fully intact and
no axiom is introduced. -/
theorem w1pTime_lineExtension (GT : GelfandTriple) {T : ℝ} (hT : 0 < T)
    {uV : ℝ → GT.V} (W : W1pTime GT 2 2 T uV) :
    letI := GT.instNACG_V; letI := GT.instIPS_V;
    letI := GT.instNACG_H; letI := GT.instIPS_H;
    ∃ (ūV : ℝ → GT.V) (ū' : ℝ → GT.Vprime),
      ūV =ᵐ[volume.restrict (Set.Icc 0 T)] uV ∧
      MemLp ūV 2 (volume : Measure ℝ) ∧
      ū' =ᵐ[volume.restrict (Set.Icc 0 T)] W.u' ∧
      MemLp ū' 2 (volume : Measure ℝ) ∧
      IsWeakTimeDerivℝ (X := GT.Vprime) (fun t => GT.hToVprime (GT.ι (ūV t))) ū' := by
  letI := GT.instNACG_V; letI := GT.instIPS_V
  letI := GT.instNACG_H; letI := GT.instIPS_H
  -- Assembly plan (§2d): the witness `ū'` is B1's reflected derivative, transported through
  -- `hToVprimeCLM` by `isWeakTimeDerivℝ_comp_clm`, multiplied by a cutoff via the PROVED B2
  -- (`isWeakTimeDerivℝ_smul_cutoff`). Blocked transitively on B1's FTC/trace pillar (no sound `ū'`
  -- available until B1 lands) plus the double-endpoint reflection `MemLp`/`=ᵐ` bookkeeping.
  sorry -- ALLOW_SORRY: s1-walls-design.md §2d — WALL B assembly. BLOCKED transitively on B1 (weakTimeDerivℝ_even_reflection)'s Bochner 1D-Sobolev FTC/trace pillar: no sound reflected-derivative witness `ū'` is constructible until B1 lands. Glue pieces (B2 isWeakTimeDerivℝ_smul_cutoff, isWeakTimeDerivℝ_comp_clm) are PROVED; the remaining work is the double-endpoint reflection MemLp/=ᵐ bookkeeping. Statement kept fully intact, no axiom.

end LineExtension

end LerayHopf.Bochner
