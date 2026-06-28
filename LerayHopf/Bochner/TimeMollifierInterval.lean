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

/-- **Weak-derivative commutation `(ρ ⋆ u)' = ρ ⋆ u'` (pointwise-curve form).**

If `v` is the weak time derivative of the `X`-valued curve `u` on `(0, T)` and `ρ` is a
normalized time mollifier, then the pointwise time-convolution `ρ ⋆ v` is the weak time
derivative of `ρ ⋆ u` on `(0, T)`.

This is the third S1 ingredient: the convolution (a linear time operation) commutes with the
distributional time derivative. The defining IBP identity transports through the Fubini
interchange
`∫ ψ'(t) (ρ ⋆ u)(t) dt = ∫ ρ(s) (∫ ψ'(t) u(t−s) dt) ds = −∫ ρ(s) (∫ ψ(t) v(t−s) dt) ds
  = −∫ ψ(t) (ρ ⋆ v)(t) dt`,
where the inner identity `∫ ψ'(t) u(t−s) = −∫ ψ(t) v(t−s)` is the weak-derivative property of
`u` tested against the shifted test function `ψ(· + s)` (whose support stays in `Ioo 0 T` for
`s` in the kernel support, *provided the test function's support is interior enough* — this is
why the whole-line `W1pTime` extension of Theorem 2 is needed upstream so that `u`/`v` are
defined on all of `ℝ`).

**Genuine wall (isolated, not weakened).** The Fubini interchange of the two time integrals
requires joint integrability of `(t, s) ↦ ψ'(t) ρ(s) u(t − s)` on `ℝ²`. For an `L²`-only curve
`u` this double integral is NOT absolutely convergent on `ℝ²` (the time-line transport of the
exact obstruction `FrechetKolmogorov.convL2_coeFn_ae` had to resolve via finite-set
restriction); the honest discharge is the same finite-support Fubini argument carried out
there, lifted to the Banach-valued weak-derivative test integrals. That assembled
Banach-valued interchange is the S1 sub-build flagged months-class by SPIKE-1; it is isolated
here as a single `ALLOW_SORRY` with the statement kept intact. -/
theorem timeConvL2_weakDeriv_comm {ρ : ℝ → ℝ} (hρ : IsTimeMollifier ρ) {T : ℝ}
    {u v : ℝ → X} (hwd : IsWeakTimeDeriv T u v) :
    IsWeakTimeDeriv T (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ] u)
      (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ] v) := by
  -- TODO (PR-F3 S1, Theorem 3): the IBP+Fubini interchange of the test-time integrals.
  -- `∫ ψ'(t) (ρ ⋆ u)(t) = ∫ ρ(s) ∫ ψ'(t) u(t−s)` (Fubini) `= −∫ ρ(s) ∫ ψ(t) v(t−s)`
  -- (weak-deriv of `u` against `ψ(·+s)`, support preserved on the whole-line extension)
  -- `= −∫ ψ(t) (ρ ⋆ v)(t)` (Fubini back). The two Fubini steps need joint integrability of
  -- `(t,s) ↦ ψ'(t) ρ(s) u(t−s)` on ℝ², which is NOT absolutely convergent for L²-only `u`;
  -- the honest discharge is the finite-support double-integral argument of
  -- `FrechetKolmogorov.convL2_coeFn_ae`, lifted to the Banach-valued weak-derivative test
  -- integrals. SPIKE-1 S1 sub-build (months-class), isolated soundly here.
  sorry -- ALLOW_SORRY: PR-F3 S1 Theorem 3 — the Banach-valued IBP+Fubini interchange `∫ψ'(ρ⋆u)=−∫ψ(ρ⋆v)`. The two time-integral Fubini swaps need joint integrability of `(t,s)↦ψ'(t)ρ(s)u(t−s)` on ℝ², which is NOT absolutely convergent for an L²-only curve `u` (the exact obstruction `FrechetKolmogorov.convL2_coeFn_ae` resolved by finite-set restriction on ℝ³); the sound discharge is that finite-support double-integral argument lifted to the Banach-valued weak-derivative test integrals. SPIKE-1 S1 (months-class), statement kept intact, no axiom.

end WeakDerivComm

/-! ### W1pTime-preserving whole-line extension (Theorem 2)

A `W1pTime GT 2 2 T uV` curve lives on `[0,T]`; the whole-line Young bound (and the pointwise
convolution of Theorem 3) need a curve defined on all of `ℝ`. The sound extension is the
Sobolev even-reflection × cutoff of the design note: it agrees with `uV` a.e. on `[0,T]`, lies
in `L²(ℝ;V)`, and its whole-line weak `V'`-derivative agrees with `u'` a.e. on `[0,T]` WITHOUT
a boundary jump (the reflected weak derivative is the reflection of the derivative — the
soundness crux). -/

section LineExtension

/-- **W1pTime-preserving whole-line extension (Theorem 2).**

Given a `W1pTime GT 2 2 T uV` element (curve on `[0,T]` with `V'`-valued weak derivative), there
is a whole-line curve `ūV : ℝ → V` such that:

* `ūV =ᵐ uV` on `[0,T]` (the extension restricts to the genuine curve);
* `ūV ∈ L²(ℝ;V)` (`MemLp ūV 2 volume`);
* there is a whole-line `V'`-valued curve `ū'` with `MemLp ū' 2 volume`, agreeing a.e. on
  `[0,T]` with `W.u'`, that is the whole-line weak `V'`-derivative of `t ↦ hToVprime (ι (ūV t))`
  — i.e. NO boundary jump is introduced (the soundness crux).

The construction is the Sobolev even-reflection × cutoff: reflect across `t = 0` and `t = T`
and multiply by a fixed smooth cutoff supported near `[0,T]`. Reflection matches the trace at
each endpoint, so the weak derivative of the reflected extension is the (sign-flipped)
reflection of `u'` with no Dirac boundary term.

**Genuine wall (isolated, not weakened).** The no-boundary-jump identity for the reflected
weak `V'`-derivative is the soundness crux flagged MONTHS-CLASS by the design note: it requires
the vector-valued Sobolev reflection calculus (even reflection preserves the weak derivative up
to sign, the cutoff product rule for weak derivatives, and absence of an endpoint Dirac term),
none of which is assembled in mathlib for Banach/`V'`-valued curves. The statement is kept
fully intact (all three properties, including the no-jump weak-derivative identity); the body
is isolated as a single `ALLOW_SORRY`, with neither the no-jump property weakened nor an axiom
introduced. -/
theorem w1pTime_lineExtension (GT : GelfandTriple) {T : ℝ} (hT : 0 < T)
    {uV : ℝ → GT.V} (W : W1pTime GT 2 2 T uV) :
    letI := GT.instNACG_V; letI := GT.instIPS_V;
    letI := GT.instNACG_H; letI := GT.instIPS_H;
    ∃ (ūV : ℝ → GT.V) (ū' : ℝ → GT.Vprime),
      ūV =ᵐ[volume.restrict (Set.Icc 0 T)] uV ∧
      MemLp ūV 2 (volume : Measure ℝ) ∧
      ū' =ᵐ[volume.restrict (Set.Icc 0 T)] W.u' ∧
      MemLp ū' 2 (volume : Measure ℝ) ∧
      IsWeakTimeDeriv (X := GT.Vprime) T (fun t => GT.hToVprime (GT.ι (ūV t))) ū' := by
  letI := GT.instNACG_V; letI := GT.instIPS_V
  letI := GT.instNACG_H; letI := GT.instIPS_H
  -- TODO (PR-F3 S1, Theorem 2): the Sobolev even-reflection × cutoff extension and its
  -- no-boundary-jump reflected weak-`V'`-derivative identity. Requires the vector-valued
  -- Sobolev reflection calculus (even reflection ⇒ weak derivative reflects with a sign flip;
  -- cutoff product rule for weak derivatives; no endpoint Dirac term), none assembled in
  -- mathlib for `V'`-valued curves. MONTHS-CLASS per the `TimeConvolution.lean` design note.
  sorry -- ALLOW_SORRY: PR-F3 S1 Theorem 2 — the W1pTime-preserving whole-line extension (even reflection × cutoff) and its no-boundary-jump reflected weak-V'-derivative identity (the soundness crux). Needs the vector-valued Sobolev reflection calculus (even reflection reflects the weak derivative with a sign flip; cutoff product rule for weak derivatives; absence of an endpoint Dirac term), none assembled in mathlib for V'-valued curves. MONTHS-CLASS per the TimeConvolution.lean design note; statement (all three properties, incl. the no-jump weak-derivative identity) kept fully intact, no axiom.

end LineExtension

end LerayHopf.Bochner
