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

2. `w1pTime_lineExtension` — the **W1pTime-preserving whole-line extension** of a curve on
   `[0,T]` (even reflection × cutoff, per the design note in `TimeConvolution.lean`). The
   reflected weak-`V'`-derivative no-jump identity is the soundness crux; isolated where it
   genuinely requires the months-class reflection calculus.

3. `timeConvL2_weakDeriv_comm` — the commutation `(ρ ⋆ ι u)' = ρ ⋆ u'` in the
   `IsWeakTimeDeriv` sense, via the CLM machinery (`isWeakTimeDeriv_comp_clm`).

## Assumptions

No new `axiom`/`opaque`/`constant`. Theorem 1 is fully proved. Where a sub-step genuinely
requires the months-class reflection/extension calculus or the pointwise–`Lp` convolution
bridge (the FrechetKolmogorov `convL2_coeFn_ae` frontier, transported to time), it carries a
precise same-line `-- ALLOW_SORRY: <blocker>`; no statement is weakened and no axiom is added.
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

The proof strategy (§1c, Opus tier) is:
1. Unfold `convolution_lsmul`; pull `ψ'(t)•` inside (linearity); apply Fubini
   (`integral_integral_swap`) — joint integrability: integrand supported in
   `(supp ψ) × (supp ρ)` (compact×compact), bounded by `‖ψ'‖∞ · ρ s · ‖u(t−s)‖`,
   L¹ on that box (`u` L²-loc ⇒ L¹ on bounded set).
2. Fix `s`, substitute `r = t−s`: inner `= ∫ r, deriv(ψ(·+s)) r • u r = -∫ r, ψ(r+s) • v r`
   by `hwd (ψ(·+s))` — **this step requires the global predicate**.
3. Fubini back + resubstitute: result is `-∫ t, ψ t • (ρ ⋆ v)(t)`.
Tier: **Opus** (box-Fubini + `deriv (ψ(·+s)) = (deriv ψ)(·+s)` rewrite). -/
theorem timeConvL2_weakDeriv_comm {ρ : ℝ → ℝ} (hρ : IsTimeMollifier ρ)
    {u v : ℝ → X} (hwd : IsWeakTimeDerivℝ u v) :
    IsWeakTimeDerivℝ (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ] u)
      (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ] v) := by
  -- TODO (s1-walls-design.md §1c, Opus): IBP+Fubini interchange for the corrected global signature.
  -- Step 1: unfold convolution, Fubini (box compact×compact, L¹ by Cauchy–Schwarz on bounded set).
  -- Step 2: `hwd (ψ(·+s))` — applicable because `ψ(·+s)` is compactly supported (global predicate).
  -- Step 3: Fubini back, resubstitute.
  -- Key rewrite: `deriv (fun t => ψ (t + s)) = fun t => deriv ψ (t + s)` (`deriv_comp_add_const`).
  sorry -- ALLOW_SORRY: s1-walls-design.md §1b/§1c — corrected whole-line signature; Opus tier; proof by box-Fubini + shifted test function argument; joint integrability by compact support × compact support box argument

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

The proof splits `∫_ℝ = ∫_{t < 0} + ∫_{t > 0}`, changes variables `t ↦ -t` on the left half
(`integral_comp_neg`, measure-preserving), recombines; boundary terms at `0` cancel precisely
because the global `C¹` test `ψ` sees `ψ(0)·u(0)` with opposite signs from the two halves
(this cancellation is the "no Dirac" soundness heart). The whole-line predicate `IsWeakTimeDerivℝ`
is required because the reflected test function `ψ(-·)` is globally compactly supported, not
confined to any `(0, T)`.

Tier: **Opus** (the soundness heart — distributional IBP with cancellation at `t = 0`). -/
theorem weakTimeDerivℝ_even_reflection (u v : ℝ → X)
    (hwd : IsWeakTimeDerivℝ u v) :
    IsWeakTimeDerivℝ (fun t => u |t|) (fun t => Real.sign t • v |t|) := by
  -- TODO (s1-walls-design.md §2b, Opus): distributional IBP with split at t=0.
  -- Split: ∫_ℝ ψ'(t) • u|t| = ∫_{<0} + ∫_{>0}.
  -- On {t > 0}: t ↦ |t| = t, so inner = ∫_{>0} ψ'(t) • u(t).
  -- On {t < 0}: substitute r = -t (measure-preserving); |t| = r; ψ'(t) = -ψ'(-r)·(-1) wait —
  --   deriv(ψ(-·)) r = -deriv ψ (-r) = -(deriv ψ)(−r) by chain rule (deriv_comp_neg);
  --   integrand becomes -ψ'(−r) • u(r). Combine: = ∫_ℝ_+ [ψ'(t) - ψ'(-t)] • u(t).
  -- Apply hwd to the globally compactly-supported test ψ and to ψ(-·) separately, recombine.
  -- Sign-flip at 0 cancels because ψ(0) appears with opposite signs from two IBPs; no Dirac.
  -- Conclude: RHS = -∫_ℝ ψ(t) • (sign t • v|t|).
  sorry -- ALLOW_SORRY: s1-walls-design.md §2b — B1 even-reflection no-Dirac identity; Opus tier; distributional IBP with split at t=0, sign cancellation at the boundary

/-- **Sub-lemma B2 — cutoff (Leibniz) product rule for whole-line Banach-valued weak derivatives.**

For a globally `C¹` cutoff `χ : ℝ → ℝ` (not assumed compactly supported) and curves
`u v : ℝ → X` with `IsWeakTimeDerivℝ u v`,

  `IsWeakTimeDerivℝ (fun t => χ t • u t) (fun t => χ t • v t + deriv χ t • u t)`.

The proof transfers `χ` onto the test function `ψ`: the product `χ · ψ` is `C¹` and compactly
supported (compact support of `ψ` wins), `deriv (χ · ψ) = χ · ψ' + χ' · ψ`, so
`∫ (χψ)'• u = ∫ χ ψ' • u + ∫ χ' ψ • u`. Apply `hwd (χ · ψ)` on the left, regroup.

Tier: **Sonnet** (mechanical IBP once B1's pattern exists; no boundary subtlety because
`χ` is global `C¹` and `ψ` compactly supported). Promote to Opus only if `smul`/`deriv`
rewrites fight back. -/
theorem isWeakTimeDerivℝ_smul_cutoff (χ : ℝ → ℝ) (hχ : ContDiff ℝ 1 χ)
    (u v : ℝ → X) (hwd : IsWeakTimeDerivℝ u v) :
    IsWeakTimeDerivℝ (fun t => χ t • u t) (fun t => χ t • v t + deriv χ t • u t) := by
  -- TODO (s1-walls-design.md §2c, Sonnet): Leibniz/product rule for distributional derivatives.
  -- For test ψ (HasCompactSupport, ContDiff ℝ 1): χ·ψ is C¹ and compactly supported.
  -- deriv (χ·ψ) = χ·ψ' + χ'·ψ (Leibniz).
  -- Apply hwd (χ·ψ): ∫ deriv(χψ) • u = -∫ (χψ) • v.
  -- Expand LHS = ∫ χ ψ' • u + ∫ χ' ψ • u; RHS = -∫ ψ • (χ v + χ' u). QED.
  sorry -- ALLOW_SORRY: s1-walls-design.md §2c — B2 cutoff product rule; Sonnet tier; Leibniz (χψ)' = χψ' + χ'ψ argument

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

**Genuine wall (WALL B assembly, not weakened).** The no-boundary-jump identity is the
soundness crux: it assembles B1 (even-reflection sign flip) + B2 (cutoff product rule) +
`isWeakTimeDerivℝ_comp_clm` (CLM transport through `hToVprime∘ι`). The `=ᵐ`/`MemLp`
bookkeeping is Sonnet-mechanical; the glue is Opus.

Body deferred to tiered provers (Sonnet for `=ᵐ`/`MemLp`; Opus for the assembly glue). -/
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
  -- TODO (s1-walls-design.md §2d, Opus glue + Sonnet bookkeeping): WALL B assembly.
  -- 1. Apply weakTimeDerivℝ_even_reflection (B1) to reflect uV/W.u' off [0,T].
  -- 2. Multiply by cutoff χ (ContDiff, HasCompactSupport near [0,T], χ ≡ 1 on [0,T]).
  -- 3. Apply isWeakTimeDerivℝ_smul_cutoff (B2): get IsWeakTimeDerivℝ on (χ • reflected uV).
  -- 4. Transport through isWeakTimeDerivℝ_comp_clm with hToVprimeCLM (§2e, in TimeSobolev).
  -- 5. =ᵐ/MemLp bookkeeping: χ ≡ 1 on [0,T]; reflection agrees on [0,T]; MemLp by compact supp.
  sorry -- ALLOW_SORRY: s1-walls-design.md §2d — WALL B assembly (B1+B2+CLM transport+MemLp); Opus glue tier; body deferred; statement (all three properties + IsWeakTimeDerivℝ no-jump weak-derivative identity) kept fully intact, no axiom

end LineExtension

end LerayHopf.Bochner
