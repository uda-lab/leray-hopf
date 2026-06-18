import LerayHopf.R3.RellichBall                  -- FrechetKolmogorovInput, translate_L2VF, L2ballR3, restrictToBall
import Mathlib.Analysis.Convolution               -- MeasureTheory.convolution, ContDiffBump approximate identity
import Mathlib.Topology.UniformSpace.Cauchy       -- TotallyBounded, isCompact_iff_totallyBounded_isComplete
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving -- Lp translation-continuity (Filter.Tendsto.compMeasurePreservingLp)

namespace LerayHopf
open MeasureTheory Filter Topology Metric TemperedDistribution
open scoped FourierTransform ENNReal SchwartzMap

/-!
# Fréchet–Kolmogorov L²-precompactness criterion (Pillar B, Stream B)

**Milestone id:** `frechet-kolmogorov` (Stream B — discharge the isolated FK hypothesis).

This file **discharges** the isolated analytic frontier
`FrechetKolmogorovInput` defined in `RellichBall.lean` (the standard Fréchet–Kolmogorov /
Riesz L²-precompactness criterion that mathlib still lacks).  It produces a genuine term

  `frechetKolmogorov_holds : FrechetKolmogorovInput`,

whose type is copied **verbatim** from `RellichBall.lean` — no weakening, no added
hypotheses.  Once proved, `localRellichInput_of_frechetKolmogorov frechetKolmogorov_holds`
becomes an *unconditional* `LocalRellichInput`, which later (a separate capstone) lets
`AxiomaticClosure.lean` rewrite `spatial_compactness_R3` from `axiom` to `theorem`.

## What `FrechetKolmogorovInput` actually demands (copied from `RellichBall.lean`)

A family `S : Set (L2ballR3 R)`, with a global representative `rep f : L2VF_R3` for each
`f ∈ S` (`restrictToBall R (rep f) = f`), that is

* uniformly L²-bounded inside the ball (`∀ f ∈ S, ‖f‖ ≤ C`),
* uniformly L²-bounded GLOBALLY on the representative (`∀ f ∈ S, ‖rep f‖ ≤ C` — the standard
  Riesz full-mass control), and
* uniformly translation-equicontinuous in the GLOBAL L²-norm
  (`∀ ε > 0, ∃ δ > 0, ∀ f ∈ S, ∀ h, ‖h‖ < δ → ‖translate_L2VF h (rep f) − rep f‖ < ε`)

is contained in a compact `K ⊆ L2ballR3 R`.

It mentions NO Sobolev/gradient/`viscousFormSq`/`L2Sigma`/subsequence/limit object — it is
the pure abstract compactness *criterion*.  This file proves exactly that criterion.

## The standard FK route (decomposition into local lemmas)

The proof is the classical mollification + Arzelà–Ascoli + total-boundedness argument:

1. **Mollification (approximate identity).**  Convolve every family member with a CONCRETE
   smooth compactly-supported scalar kernel `K : MollifierKernel`, whose explicit continuous
   representative is `mollifyRep K f = η ⋆ f`.  `convolution_l2_tendsto_uniform`: the
   convolutions approximate the originals in L² *uniformly over the family*, with the rate
   controlled by the uniform translation modulus (this is where the FK hypothesis is consumed).
2. **Equicontinuity / equiboundedness of the mollified family.**
   `mollified_family_equicontinuous` + `mollified_family_uniformly_bounded`: the explicit
   representative `mollifyRep K (rep f)`, restricted to `x ∈ B_R`, is uniformly bounded and
   uniformly equicontinuous (Young's inequality `‖(η ⋆ g) x‖ ≤ ‖η‖₂‖g‖₂` + the kernel-only modulus
   of `η`).  The mass factor `‖g‖₂` localizes to the kernel-support enlargement `B_{R+r}` (the
   only region the kernel reaches from `B_R`), so these bounds need only the ENLARGED-BALL bound
   `‖restrictToBall (R+r) (rep f)‖ ≤ C`, which is supplied directly from the criterion's GLOBAL
   bound `hbddGlobal : ‖rep f‖ ≤ C` by ball-mass monotonicity (the strengthened
   `FrechetKolmogorovInput`, round 4).  They are stated for the genuine smooth representative
   `mollifyRep` on `B_R`,
   NOT for an arbitrary operator `L2VF_R3 → L2VF_R3` (for which they would be false — e.g. `ρ = id`).
3. **Arzelà–Ascoli ⇒ total boundedness of the mollified family in C(ball), hence in L²(ball).**
   `mollified_family_totallyBounded_L2`.
4. **Total-boundedness transfer.**  `totallyBounded_of_uniform_approx`: a set that is
   uniformly ε-approximable (step 1) by a totally bounded set (step 3) is itself totally
   bounded; with completeness of `L2ballR3 R` this gives precompactness
   (`isCompact_iff_totallyBounded_isComplete`).

The top-level `frechetKolmogorov_holds` assembles 1–4 into the FK criterion.

## Closing `RellichBall.lean`'s residual `sorry` (`integrable_viscous_integrand_of_memH1`)

That residual `sorry` (H¹ ⇒ concrete `(2π)²‖ξ‖²`-weighted L²-integrability of the L²-Fourier
transform) is a pure proof-body fill on an *existing* statement in `RellichBall.lean`; it is a
`lean-prover` task and must NOT be restated/weakened.  Its only genuinely missing ingredient
is an a.e. characterization of `TemperedDistribution.smulLeftCLM` for the UNBOUNDED weight
`(1+‖ξ‖²)^(1/2)` on an `Lp`-coerced distribution (mathlib's `Lp.toTemperedDistribution_smul_eq`
covers only `MemLp`-bounded multipliers).  We expose that single missing ingredient here as a
helper SIGNATURE `memH1_weightedL2_integrable` (distribution-faithful, derived directly from the
`MemSobolev 1 2` definition of `memH1VF_R3`), so the prover can wire it into the RellichBall
body without editing any RellichBall *statement*.

## Honest scope (no overclaim) — SCAFFOLD pass

This file is presently **scaffold only**: every obligation below is a marked `sorry`
(`-- ALLOW_SORRY:`) for `lean-prover` to fill.  No `axiom`/`opaque`/`constant` is introduced.
`frechetKolmogorov_holds` is a genuine DISCHARGE target (a term of the existing
`FrechetKolmogorovInput` type), not a new isolated hypothesis.

**Codex Gate round 3 (high) — local helper bounds vs. the deliverable, RESOLVED upstream.**
The mollifier-family helper bounds (steps 1–3) are TRUE only with an ENLARGED-BALL mass bound on
the kernel-support enlargement `B_{R + r}` (`r =` kernel support radius `K.supportRadius`), since
the mollified field on `B_R` only sees the original field over `B_{R+r}`.  A single-radius ball
bound on `B_R` plus a translation modulus does NOT control annulus mass on `B_{R+r} ∖ B_R`, so
the enlarged-ball bound is not recoverable from those two data alone.  This is now fixed UPSTREAM:
`RellichBall.FrechetKolmogorovInput` was strengthened to ALSO carry a uniform GLOBAL L²-norm bound
`hbddGlobal : ∀ f ∈ S, ‖rep f‖ ≤ C` (the standard Riesz full-mass control), from which any
enlarged-ball bound `‖restrictToBall (R + r₀) (rep f)‖ ≤ C` follows immediately by monotonicity of
ball mass in the radius (`‖restrictToBall R' g‖ ≤ ‖g‖`).  Hence the helper chain's `hbdEnl` is now
supplied directly from the criterion's own data, and `frechetKolmogorov_holds` is a pure
(proof-body) discharge — no upstream blocker remains.

## Architecture (standalone sibling)

Imports `R3.RellichBall` (for `FrechetKolmogorovInput`, `translate_L2VF`, `L2ballR3`,
`restrictToBall`), plus targeted mathlib (convolution + uniform-space compactness).  It does
NOT import `AxiomaticClosure.lean` and does NOT edit the root `LerayHopf.lean` (deferred wiring).

DAG position:
```
R3/SpatialCompactness.lean   (L2ballR3, restrictToBall, LocalRellichInput)
  └── R3/RellichBall.lean     (FrechetKolmogorovInput, translate_L2VF) [Stream B prereq]
        └── R3/FrechetKolmogorov.lean   [THIS FILE; discharges FrechetKolmogorovInput]
```

## Declarations (dependency order)

- `memH1_weightedL2_integrable`            : helper SIG for RellichBall's residual sorry (H¹ ⇒ weighted-L² integrability)
- `MollifierKernel`                        : concrete smooth compactly-supported scalar kernel (mollifier data)
- `mollifyRep`                             : explicit continuous representative of the mollified field (`η ⋆ f`)
- `convolution_l2_tendsto_uniform`         : FK step 1 — uniform L²-mollification approximate identity
- `mollified_family_uniformly_bounded`     : FK step 2 — equibounded smoothed family (concrete `mollifyRep`)
- `mollified_family_equicontinuous`        : FK step 2 — equicontinuous smoothed family (concrete `mollifyRep`)
- `mollified_family_totallyBounded_L2`     : FK step 3 — Arzelà–Ascoli ⇒ totally bounded in L²(ball)
- `totallyBounded_of_uniform_approx`       : FK step 4 — total-boundedness transfer under uniform approximation
- `frechetKolmogorov_holds`                : DELIVERABLE — discharges `FrechetKolmogorovInput`

## Assumptions

Zero new `axiom`/`opaque`/`constant`.  Every gap is a marked `-- ALLOW_SORRY:` proof body,
to be discharged by `lean-prover`.  `frechetKolmogorov_holds` is a real discharge of an
existing hypothesis type, not a new hypothesis.
-/

/-! ### Helper for RellichBall's residual `sorry` -/

/-- The Bessel weight `ξ ↦ ((1 + ‖ξ‖²)^(1/2) : ℝ) : ℂ` of order `s = 1` (`s/2 = 1/2`), the
multiplier appearing in `memSobolev_iff_exists_smulLeftCLM_fourier` for `MemSobolev 1 2`. -/
private noncomputable def besselWeightC : Domain3 → ℂ :=
  fun ξ => (((1 + ‖ξ‖ ^ 2) ^ ((1 : ℝ) / 2) : ℝ) : ℂ)

/-- The Bessel weight is real-valued and nonnegative, with squared modulus `1 + ‖ξ‖²`. -/
private theorem normSq_besselWeightC (ξ : Domain3) : ‖besselWeightC ξ‖ ^ 2 = 1 + ‖ξ‖ ^ 2 := by
  have hnn : (0 : ℝ) ≤ 1 + ‖ξ‖ ^ 2 := by positivity
  rw [besselWeightC, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hnn _),
    ← Real.rpow_natCast ((1 + ‖ξ‖ ^ 2) ^ ((1 : ℝ) / 2)) 2, ← Real.rpow_mul hnn]
  norm_num

/-- The Bessel weight has temperate growth (`= ofReal ∘ (1+‖·‖²)^(1/2)`). -/
private theorem hasTemperateGrowth_besselWeightC :
    Function.HasTemperateGrowth besselWeightC := by
  have hr : Function.HasTemperateGrowth (fun ξ : Domain3 => (1 + ‖ξ‖ ^ 2) ^ ((1 : ℝ) / 2)) :=
    Function.hasTemperateGrowth_one_add_norm_sq_rpow Domain3 ((1 : ℝ) / 2)
  have hc := (Complex.ofRealCLM.hasTemperateGrowth).comp hr
  exact hc

/-- The Bessel weight is continuous. -/
private theorem continuous_besselWeightC : Continuous besselWeightC :=
  hasTemperateGrowth_besselWeightC.1.continuous

/-- **Local integrability of the weighted Fourier transform.** For `g : L2C_R3`, the pointwise
product `ξ ↦ besselWeightC ξ • g ξ` (an unbounded-multiplier product) is locally integrable:
on each ball the continuous weight is bounded and `g ∈ L²` is integrable. -/
private theorem locallyIntegrable_besselWeight_smul (g : L2C_R3) :
    LocallyIntegrable (fun ξ : Domain3 => besselWeightC ξ • (g : Domain3 → ℂ) ξ)
      (volume : Measure Domain3) := by
  intro x
  -- a nbhd of `x`: the closed unit ball around `x` (a compact set, member of `𝓝 x`).
  refine ⟨Metric.closedBall x 1, Metric.closedBall_mem_nhds x one_pos, ?_⟩
  have hK : IsCompact (Metric.closedBall x 1) := isCompact_closedBall x 1
  -- `g` is integrable on the (finite-measure) ball.
  have hg_int : IntegrableOn (g : Domain3 → ℂ) (Metric.closedBall x 1) volume :=
    ((Lp.memLp g).locallyIntegrable (by norm_num)).integrableOn_isCompact hK
  -- the continuous weight is bounded on the compact ball.
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    (continuous_besselWeightC.continuousOn (s := Metric.closedBall x 1))
  -- product is integrable on the ball: `weight • g`, weight bounded, g integrable.
  have hmul : IntegrableOn (fun ξ => besselWeightC ξ * (g : Domain3 → ℂ) ξ)
      (Metric.closedBall x 1) volume := by
    refine hg_int.bdd_mul (c := C) ?_ ?_
    · exact (continuous_besselWeightC.aestronglyMeasurable).restrict
    · refine ae_restrict_of_forall_mem measurableSet_closedBall (fun y hy => ?_)
      exact hC y hy
  simpa only [smul_eq_mul] using hmul

/-- **Helper for `RellichBall.integrable_viscous_integrand_of_memH1`.**

For `w ∈ H¹(ℝ³)` (i.e. `memH1VF_R3 w`, defined as `TemperedDistribution.MemSobolev 1 2` on each
complex component `cⱼ = L2VF_projComponentC_R3 j w`), the L²-Fourier transform `𝓕 cⱼ` is
square-integrable against the genuine `H¹` weight `1 + ‖ξ‖²`. -/
theorem memH1_weightedL2_integrable (w : L2VF_R3) (hw : memH1VF_R3 w) (j : Fin 3) :
    Integrable (fun ξ : Domain3 =>
        (1 + ‖ξ‖ ^ 2) * ‖(𝓕 (L2VF_projComponentC_R3 j w) : L2C_R3) ξ‖ ^ 2)
      (volume : Measure Domain3) := by
  classical
  -- Abbreviation for the complex component and its L²-Fourier transform.
  set cF : L2C_R3 := 𝓕 (L2VF_projComponentC_R3 j w) with hcF
  -- From `MemSobolev 1 2 (cⱼ : 𝓢')` get an `Lp 2` witness `f'` for the weighted Fourier transform.
  have hsob : TemperedDistribution.MemSobolev (1 : ℝ) 2
      (L2VF_projComponentC_R3 j w : 𝓢'(Domain3, ℂ)) := hw j
  obtain ⟨f', hf'⟩ :=
    TemperedDistribution.memSobolev_iff_exists_smulLeftCLM_fourier.mp hsob
  -- `hf'` : `smulLeftCLM ℂ (weight) (𝓕 (cⱼ : 𝓢')) = (f' : 𝓢')`, weight `= (1+‖ξ‖²)^(1/2)`.
  -- Bridge `𝓕 (cⱼ : 𝓢')` to the L²-Fourier `(cF : 𝓢')`.
  have hbridge : (𝓕 (L2VF_projComponentC_R3 j w : 𝓢'(Domain3, ℂ)))
      = (cF : 𝓢'(Domain3, ℂ)) := by
    rw [hcF]; exact (MeasureTheory.Lp.fourier_toTemperedDistribution_eq _)
  rw [hbridge] at hf'
  -- The weight function `(1+‖ξ‖²)^(1/2)` (ℂ-coerced) is exactly `besselWeightC`.
  have hweq : (fun x : Domain3 => (((1 + ‖x‖ ^ 2) ^ ((1 : ℝ) / 2) : ℝ) : ℂ)) = besselWeightC := rfl
  rw [hweq] at hf'
  -- du Bois–Reymond: extract the a.e. identity `besselWeightC • cF = f'`.
  have hlhs_li : LocallyIntegrable (fun ξ : Domain3 => besselWeightC ξ • (cF : Domain3 → ℂ) ξ)
      (volume : Measure Domain3) := locallyIntegrable_besselWeight_smul cF
  have hrhs_li : LocallyIntegrable (f' : Domain3 → ℂ) (volume : Measure Domain3) :=
    (Lp.memLp f').locallyIntegrable (by norm_num)
  have hae : (fun ξ : Domain3 => besselWeightC ξ • (cF : Domain3 → ℂ) ξ)
      =ᵐ[volume] (f' : Domain3 → ℂ) := by
    refine ae_eq_of_integral_contDiff_smul_eq hlhs_li hrhs_li ?_
    intro g g_smooth g_cpt
    -- Test function as a Schwartz map.
    have hg_supp : HasCompactSupport (Complex.ofRealCLM ∘ g) := g_cpt.comp_left rfl
    have hg_diff := Complex.ofRealCLM.contDiff.comp g_smooth
    set φ : SchwartzMap Domain3 ℂ := hg_supp.toSchwartzMap hg_diff with hφ
    have hφ_coe : (φ : Domain3 → ℂ) = fun x => ((g x : ℝ) : ℂ) := rfl
    -- Pair both sides of `hf'` with `φ`.
    have hpair : smulLeftCLM ℂ besselWeightC (cF : 𝓢'(Domain3, ℂ)) φ
        = ((f' : 𝓢'(Domain3, ℂ)) φ) := by rw [hf']
    -- LHS distribution pairing: `smulLeftCLM weight (cF : 𝓢') φ = (cF : 𝓢') (weight • φ)`.
    rw [TemperedDistribution.smulLeftCLM_apply_apply,
        MeasureTheory.Lp.toTemperedDistribution_apply,
        MeasureTheory.Lp.toTemperedDistribution_apply] at hpair
    -- Convert goal into `hpair` by matching the integrands pointwise.
    rw [show (fun x => (g x : ℝ) • (besselWeightC x • (cF : Domain3 → ℂ) x))
          = fun x => ((SchwartzMap.smulLeftCLM ℂ besselWeightC φ) x) • (cF : Domain3 → ℂ) x from ?_,
        show (fun x => (g x : ℝ) • (f' : Domain3 → ℂ) x)
          = fun x => (φ x) • (f' : Domain3 → ℂ) x from ?_]
    · exact hpair
    · funext x
      show (g x : ℝ) • (f' : Domain3 → ℂ) x = (φ x) • (f' : Domain3 → ℂ) x
      rw [hφ_coe]
      simp only [Complex.real_smul, smul_eq_mul]
    · funext x
      show (g x : ℝ) • (besselWeightC x • (cF : Domain3 → ℂ) x)
          = ((SchwartzMap.smulLeftCLM ℂ besselWeightC φ) x) • (cF : Domain3 → ℂ) x
      rw [SchwartzMap.smulLeftCLM_apply_apply hasTemperateGrowth_besselWeightC, hφ_coe]
      simp only [Complex.real_smul, smul_eq_mul]
      ring
  -- Now the integrand `(1+‖ξ‖²)·‖cF ξ‖² = ‖besselWeightC ξ • cF ξ‖² =ᵐ ‖f' ξ‖²`, which is integrable.
  have hf'_sq : Integrable (fun ξ : Domain3 => ‖(f' : Domain3 → ℂ) ξ‖ ^ 2)
      (volume : Measure Domain3) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f')).mp (Lp.memLp f')
  refine hf'_sq.congr ?_
  filter_upwards [hae] with ξ hξ
  rw [← hξ, norm_smul, mul_pow, normSq_besselWeightC]

/-! ### Concrete mollifier — kernel data and explicit continuous representative

The Codex statement-gate flagged that mollifier-family bounds are FALSE when phrased for an
*arbitrary* operator `ρ : L2VF_R3 → L2VF_R3` (e.g. `ρ = id`): an L²-bounded family need not have
a pointwise sup bound or an equicontinuous representative, and pointwise evaluation of an `Lp`
class is not a faithful smooth representative.  The fix is to fix a CONCRETE mollification by an
explicit smooth, compactly supported scalar kernel `η : Domain3 → ℝ`, and to state every bound
for an EXPLICIT continuous representative

  `mollifyRep η f x := ∫ y, η (x − y) • (f y) ∂volume`,

which is a genuine pointwise-defined function of `x` (a vector-valued convolution `η ⋆ f`).  The
kernel-smoothness/compact-support hypotheses are exactly what make the bounds TRUE (Young's
inequality on the sup norm; equicontinuity from the kernel's own modulus). -/

/-- **Kernel data for the mollifier.**  A scalar approximate-identity kernel
`η : Domain3 → ℝ` that is smooth (`ContDiff ℝ ⊤`) and compactly supported — i.e. an admissible
mollifier.  Bundling the smoothness/compact-support hypotheses makes the family bounds below
genuinely true (rather than vacuously or falsely true for an arbitrary operator). -/
structure MollifierKernel where
  /-- The scalar kernel function. -/
  η : Domain3 → ℝ
  /-- The kernel is `C^∞`. -/
  smooth : ContDiff ℝ (⊤ : ℕ∞) η
  /-- The kernel has compact support (so all convolution integrals converge and are smooth). -/
  hasCompactSupport : HasCompactSupport η
  /-- An explicit support radius `r ≥ 0`: the kernel vanishes outside `closedBall 0 r`.  This
  is the enlargement radius the local family bounds are parameterized by — the mollified field
  on `B_R` only sees the original field over `B_{R+r}` (kernel reach), so an enlarged-ball bound
  on `B_{R+r}` is exactly what Young / Arzelà–Ascoli on `B_R` need; it is obtained from the
  criterion's GLOBAL bound `hbddGlobal : ‖rep f‖ ≤ C` by ball-mass monotonicity. -/
  supportRadius : ℝ
  /-- The support radius is nonnegative. -/
  supportRadius_nonneg : 0 ≤ supportRadius
  /-- The kernel is supported in `closedBall 0 supportRadius`. -/
  tsupport_subset : tsupport η ⊆ Metric.closedBall (0 : Domain3) supportRadius

/-- **Explicit continuous representative of the mollified field.**

`mollifyRep K f x = ∫ y, K.η (x − y) • (f y : EuclideanSpace ℝ (Fin 3)) ∂volume` is the
genuine pointwise-defined vector-valued convolution `η ⋆ f`.  Because `K.η` is smooth and
compactly supported, this integral converges for every `x` and defines a smooth (in particular
continuous) function `Domain3 → EuclideanSpace ℝ (Fin 3)` — a *faithful* representative of the
mollified L²-class, on which pointwise sup and equicontinuity bounds are legitimate.

This is the concrete operator the family lemmas below are stated for, replacing the unsound
arbitrary `ρ : L2VF_R3 → L2VF_R3`. -/
noncomputable def mollifyRep (K : MollifierKernel) (f : L2VF_R3) :
    Domain3 → EuclideanSpace ℝ (Fin 3) :=
  fun x => ∫ y : Domain3, K.η (x - y) • (f y : EuclideanSpace ℝ (Fin 3))
    ∂(volume : Measure Domain3)

/-! ### Mollifier sub-library — kernel as a scalar L²-class and reusable estimates

The two mollifier-family lemmas (`mollified_family_uniformly_bounded`,
`mollified_family_equicontinuous`) are short consequences of three reusable estimates about the
CONCRETE kernel.  We factor them out as named lemmas so each family lemma becomes a bounded
derivation rather than a monolithic analytic proof:

* `kernel_translate_L2_tendsto` — the kernel's own L²-translation modulus vanishes (η smooth +
  compact support ⇒ uniformly continuous ⇒ DCT).  This is the *uniform* (g-independent) modulus
  driving equicontinuity.
* `mollifyRep_sup_le` — Cauchy–Schwarz/Young pointwise sup bound on `B_R`, with the mass factor
  localized to the kernel-reach enlargement `B_{R + K.supportRadius}`.
* `mollifyRep_sub_le` — the convolution-difference estimate on `B_R`, factoring the modulus of
  `mollifyRep K f` through the kernel's L²-translation modulus times the enlarged-ball mass.

To state the kernel modulus we coerce the scalar kernel `K.η : Domain3 → ℝ` into the scalar L²
space `Lp ℝ 2 volume` (`kernelL2R`) and use the scalar translation `translate_L2R` (the scalar
mirror of `translate_L2VF`, same measure-preserving `(· + h)` plumbing). -/

/-- Scalar L² translation `τ_h g (x) = g (x − h)`, the `Lp ℝ 2 volume` mirror of
`translate_L2VF` (same measure-preserving `(· + h)` route). -/
noncomputable def translate_L2R (h : Domain3) (g : Lp ℝ 2 (volume : Measure Domain3)) :
    Lp ℝ 2 (volume : Measure Domain3) :=
  Lp.compMeasurePreserving (· + h)
    (measurePreserving_add_right (volume : Measure Domain3) h) g

/-- The scalar kernel `K.η`, coerced to a scalar L²-class.  It is `MemLp` because it is continuous
(`K.smooth.continuous`) with compact support (`K.hasCompactSupport`). -/
noncomputable def kernelL2R (K : MollifierKernel) : Lp ℝ 2 (volume : Measure Domain3) :=
  MemLp.toLp K.η
    (K.smooth.continuous.memLp_of_hasCompactSupport (p := 2) (μ := volume) K.hasCompactSupport)

/-- **Helper 1 — the kernel's L²-translation modulus vanishes.**

For a `MollifierKernel K`, the map `h ↦ ‖translate_L2R h (kernelL2R K) − kernelL2R K‖` tends to `0`
as `h → 0` in `Domain3`.  `K.η` is smooth with compact support, hence uniformly continuous and
dominated by a fixed compactly supported `L²` envelope, so dominated convergence gives L²-continuity
of translation of the kernel.  This is the *uniform* (g-independent) modulus that drives the
equicontinuity of the mollified family. -/
theorem kernel_translate_L2_tendsto (K : MollifierKernel) :
    Filter.Tendsto
      (fun h : Domain3 => ‖translate_L2R h (kernelL2R K) - kernelL2R K‖)
      (𝓝 (0 : Domain3)) (𝓝 (0 : ℝ)) := by
  -- mathlib provides L²-translation continuity off the shelf: `compMeasurePreserving` of an `Lp`
  -- class with a measure-preserving continuous map is continuous in both arguments
  -- (`Filter.Tendsto.compMeasurePreservingLp`).  We feed in the translations `(· + h)` (a continuous
  -- measure-preserving family on `Domain3`) and the constant class `kernelL2R K`.
  set μ : Measure Domain3 := volume with hμ
  -- the translation maps as continuous maps, measure preserving for every `h`.
  set g : Domain3 → C(Domain3, Domain3) :=
    fun h => ⟨(· + h), continuous_id.add continuous_const⟩ with hg
  have hgm : ∀ h : Domain3, MeasurePreserving (g h) μ μ := fun h =>
    measurePreserving_add_right μ h
  -- `Tendsto (g ·) (𝓝 0) (𝓝 (g 0))`: the family `h ↦ (· + h)` is continuous in `h`.
  have hgcont : Continuous g := by
    refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
    show Continuous (fun p : Domain3 × Domain3 => p.2 + p.1)
    exact continuous_snd.add continuous_fst
  have htend := Filter.Tendsto.compMeasurePreservingLp
    (μ := μ) (ν := μ) (E := ℝ) (p := 2)
    (f := fun _ : Domain3 => kernelL2R K) (f₀ := kernelL2R K)
    (g := g) (g₀ := g 0)
    tendsto_const_nhds (hgcont.tendsto 0) hgm (hgm 0) (by simp)
  -- identify the two `compMeasurePreserving` expressions with `translate_L2R` and `kernelL2R K`.
  have heq : (fun h : Domain3 => Lp.compMeasurePreserving (g h) (hgm h) (kernelL2R K))
      = fun h : Domain3 => translate_L2R h (kernelL2R K) := rfl
  have h0 : Lp.compMeasurePreserving (g 0) (hgm 0) (kernelL2R K) = kernelL2R K := by
    have : (g 0 : Domain3 → Domain3) = id := by
      funext x; simp [hg]
    -- `g 0 = (· + 0) = id`, so the composition is the identity on `Lp`.
    refine Lp.ext ?_
    have hcoe := Lp.coeFn_compMeasurePreserving (kernelL2R K) (hgm 0)
    filter_upwards [hcoe] with x hx
    rw [hx]
    simp [hg]
  rw [heq, h0] at htend
  -- continuity of the norm-of-difference turns the `Lp`-convergence into the scalar `Tendsto`.
  have hsub : Filter.Tendsto
      (fun h : Domain3 => translate_L2R h (kernelL2R K) - kernelL2R K)
      (𝓝 0) (𝓝 (kernelL2R K - kernelL2R K)) := htend.sub tendsto_const_nhds
  have hnorm := hsub.norm
  simpa using hnorm

/-- **Helper 2 — pointwise sup bound for the mollified field (Cauchy–Schwarz / Young).**

For `x ∈ closedBall 0 R`, the convolution value `mollifyRep K f x = ∫ y, K.η (x−y) • f y` is bounded
by `‖kernelL2R K‖ · ‖restrictToBall (R + K.supportRadius) f‖`.  Cauchy–Schwarz on the integrand
`K.η(x−y) • f y` gives `‖kernel‖₂ · ‖f‖₂`, and because `K.η` is supported in
`closedBall 0 K.supportRadius` the integral only sees `f` over `y ∈ B_{R + K.supportRadius}`
(kernel reach from `B_R`), localizing the mass factor to the enlarged ball. -/
theorem mollifyRep_sup_le (K : MollifierKernel) (f : L2VF_R3) (R : ℝ)
    {x : Domain3} (hx : x ∈ Metric.closedBall (0 : Domain3) R) :
    ‖mollifyRep K f x‖
      ≤ ‖kernelL2R K‖ * ‖restrictToBall (R + K.supportRadius) f‖ := by
  classical
  set r := K.supportRadius with hr
  -- The enlarged ball `B_{R+r}` (kernel reach from `B_R`).
  set B : Set Domain3 := Metric.closedBall (0 : Domain3) (R + r) with hB
  -- The kernel as an `L²`-class envelope, and the two scalar L² factors of Cauchy–Schwarz.
  have hηmem : MemLp K.η 2 (volume : Measure Domain3) :=
    K.smooth.continuous.memLp_of_hasCompactSupport (p := 2) (μ := volume) K.hasCompactSupport
  have hηaesm : AEStronglyMeasurable K.η (volume : Measure Domain3) := hηmem.aestronglyMeasurable
  have hmp := Measure.measurePreserving_sub_left (volume : Measure Domain3) x
  -- factor `a = |K.η(x−·)|` (kernel slice), `b = 1_B · ‖f·‖` (localized mass).
  have ha : MemLp (fun y : Domain3 => |K.η (x - y)|) 2 (volume : Measure Domain3) :=
    (hηmem.comp_measurePreserving hmp).abs
  have hfnorm : MemLp (fun y : Domain3 => ‖(f y : EuclideanSpace ℝ (Fin 3))‖) 2
      (volume : Measure Domain3) := (Lp.memLp f).norm
  have hb : MemLp (B.indicator (fun y : Domain3 => ‖(f y : EuclideanSpace ℝ (Fin 3))‖)) 2
      (volume : Measure Domain3) := hfnorm.indicator measurableSet_closedBall
  -- STEP 1: `‖mollifyRep K f x‖ ≤ ∫ |K.η(x−y)| · 1_B(y) ‖f y‖` (kernel-reach localization).
  have hstep1 : ‖mollifyRep K f x‖
      ≤ ∫ y : Domain3, |K.η (x - y)| * B.indicator
          (fun z : Domain3 => ‖(f z : EuclideanSpace ℝ (Fin 3))‖) y
          ∂(volume : Measure Domain3) := by
    rw [mollifyRep]
    refine le_trans (norm_integral_le_integral_norm _) (le_of_eq (integral_congr_ae ?_))
    filter_upwards with y
    rw [norm_smul, Real.norm_eq_abs]
    by_cases hzero : K.η (x - y) = 0
    · simp [hzero]
    · have hmem : x - y ∈ tsupport K.η := subset_tsupport K.η (by simpa using hzero)
      have hball : x - y ∈ Metric.closedBall (0 : Domain3) r := K.tsupport_subset hmem
      have hxy : ‖x - y‖ ≤ r := by simpa [dist_eq_norm] using hball
      have hxR : ‖x‖ ≤ R := by simpa [dist_eq_norm] using hx
      have hyR : ‖y‖ ≤ R + r := by
        have h1 : y = x - (x - y) := by abel
        have h2 : ‖y‖ ≤ ‖x‖ + ‖x - y‖ := by
          rw [h1]; exact (norm_sub_le _ _).trans_eq (by rw [sub_sub_cancel])
        linarith
      have hyball : y ∈ B := by simpa [hB, dist_eq_norm] using hyR
      rw [Set.indicator_of_mem hyball]
  -- STEP 2: Cauchy–Schwarz in `Lp ℝ 2` on the two factors.
  have hcs := real_inner_le_norm (ha.toLp _) (hb.toLp _)
  rw [L2.inner_def] at hcs
  have heq : (∫ y : Domain3, |K.η (x - y)| * B.indicator
        (fun z : Domain3 => ‖(f z : EuclideanSpace ℝ (Fin 3))‖) y ∂(volume : Measure Domain3))
      = ∫ y : Domain3, (inner ℝ ((ha.toLp _ : Domain3 → ℝ) y) ((hb.toLp _ : Domain3 → ℝ) y))
          ∂(volume : Measure Domain3) := by
    refine integral_congr_ae ?_
    filter_upwards [ha.coeFn_toLp, hb.coeFn_toLp] with y hay hby
    simp only [RCLike.inner_apply, conj_trivial]
    rw [hay, hby, mul_comm]
  -- STEP 3: identify the two `Lp`-norms with `‖kernelL2R K‖` and `‖restrictToBall (R+r) f‖`.
  have hna : ‖ha.toLp _‖ = ‖kernelL2R K‖ := by
    rw [kernelL2R, Lp.norm_toLp, Lp.norm_toLp]
    congr 1
    have habs : AEStronglyMeasurable (fun y : Domain3 => |K.η y|) (volume : Measure Domain3) :=
      hηaesm.norm.congr (by filter_upwards with y using (Real.norm_eq_abs _))
    rw [show (fun y : Domain3 => |K.η (x - y)|) = (fun y : Domain3 => |K.η y|) ∘ (fun y => x - y)
        from rfl, eLpNorm_comp_measurePreserving habs hmp]
    rw [show (fun y : Domain3 => |K.η y|) = (fun y : Domain3 => ‖K.η y‖) from
        funext fun y => (Real.norm_eq_abs _).symm, eLpNorm_norm]
  have hnb : ‖hb.toLp _‖ = ‖restrictToBall (R + r) f‖ := by
    rw [restrictToBall, Lp.norm_toLp, Lp.norm_toLp,
      ← eLpNorm_norm (f : Domain3 → EuclideanSpace ℝ (Fin 3)),
      eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_closedBall]
  -- Assemble.
  calc ‖mollifyRep K f x‖
      ≤ ∫ y : Domain3, |K.η (x - y)| * B.indicator
          (fun z : Domain3 => ‖(f z : EuclideanSpace ℝ (Fin 3))‖) y
          ∂(volume : Measure Domain3) := hstep1
    _ = ∫ y : Domain3, (inner ℝ ((ha.toLp _ : Domain3 → ℝ) y) ((hb.toLp _ : Domain3 → ℝ) y))
          ∂(volume : Measure Domain3) := heq
    _ ≤ ‖ha.toLp _‖ * ‖hb.toLp _‖ := hcs
    _ = ‖kernelL2R K‖ * ‖restrictToBall (R + r) f‖ := by rw [hna, hnb]

/-- **Helper 3 — convolution-difference estimate (modulus of the mollified field).**

For `x, y ∈ closedBall 0 R`, the increment of the mollified field is bounded by the enlarged-ball
mass of `f` times the kernel's own L²-translation modulus at the shift `x − y`:

  `‖mollifyRep K f x − mollifyRep K f y‖`
      `≤ ‖restrictToBall (R + K.supportRadius) f‖ · ‖translate_L2R (x − y) (kernelL2R K) − kernelL2R K‖`.

After the change of variables `z = x − y'` the difference is `∫ (K.η(x−·) − K.η(y−·)) • f`, and
Cauchy–Schwarz factors it as (kernel translation-modulus)·(enlarged-ball mass of `f`). -/
theorem mollifyRep_sub_le (K : MollifierKernel) (f : L2VF_R3) (R : ℝ)
    {x y : Domain3} (hx : x ∈ Metric.closedBall (0 : Domain3) R)
    (hy : y ∈ Metric.closedBall (0 : Domain3) R) :
    ‖mollifyRep K f x - mollifyRep K f y‖
      ≤ ‖restrictToBall (R + K.supportRadius) f‖
          * ‖translate_L2R (x - y) (kernelL2R K) - kernelL2R K‖ := by
  sorry -- ALLOW_SORRY: scaffold — `mollifyRep K f x − mollifyRep K f y = ∫ y', (K.η(x−y') − K.η(y−y')) • f y'`,
  -- whose integrand involves the kernel difference `K.η(x−·) − K.η(y−·)`, a translate by `x − y` of
  -- `K.η(y−·)`; by reflection/translation invariance its L²-norm equals
  -- `‖translate_L2R (x−y) (kernelL2R K) − kernelL2R K‖`.  Both kernel slices are supported so the
  -- integrand only sees `f` over `B_{R+K.supportRadius}` (`x, y ∈ B_R`, `K.tsupport_subset`); Cauchy–Schwarz
  -- then gives `(enlarged-ball mass of f) · (kernel translation-modulus at x−y)`.

/-! ### FK step 1 — uniform L²-mollification approximate identity -/

/-- **FK step 1.**  Uniform L²-approximation of a translation-equicontinuous family by its
mollifications, for the CONCRETE mollifier.

If a family `{rep f | f ∈ S}` of L²(ℝ³) fields has a uniform L²-translation modulus
(the second hypothesis of `FrechetKolmogorovInput`), then for every tolerance `ε > 0` there is
an admissible smooth compactly supported kernel `K` and a choice of L²-classes `ρf : S → L2VF_R3`
whose chosen pointwise representative is `mollifyRep K (rep f)`, such that every member is within
`ε` in L² of its mollification:

  `∀ f ∈ S, ‖f − restrictToBall R (ρf f)‖ < ε`,

with the rate controlled UNIFORMLY over the family by the translation modulus (Minkowski +
`‖η ⋆ g − g‖₂ ≤ sup_{‖h‖ ≤ supp K.η} ‖τ_h g − g‖₂` for a mass-one kernel).  The mollified image
is totally bounded in L² (step 3).  This is the genuinely-missing analytic core (mathlib has only
the *pointwise* `convolution_tendsto_right`).

**Norm-correctness (Codex Gate round 3 → resolved round 4).**  The total-boundedness conjunct
delegates to `mollified_family_totallyBounded_L2` (steps 2+3), whose bounds need a ball-mass bound
on the kernel-support enlargement `B_{R+K.supportRadius}`.  The local hypothesis is an
ENLARGED-BALL bound at a fixed enlargement budget `r₀ ≥ 0`:
`hbdEnl : ∀ f ∈ S, ‖restrictToBall (R + r₀) (rep f)‖ ≤ C`, which the caller obtains directly from
`FrechetKolmogorovInput`'s GLOBAL bound `‖rep f‖ ≤ C` by ball-mass monotonicity (a single-radius
ball bound `‖f‖ ≤ C` alone would not control annulus mass, but the strengthened criterion carries
the global bound, so the enlarged bound is immediate).  The kernel `K` produced has support
radius `K.supportRadius ≤ r₀`, so by monotonicity of ball mass in the radius the step-3 bound on
`B_{R + K.supportRadius}` follows from `hbdEnl`.  The ball restriction bound `‖f‖ ≤ C` is retained
as `hbd` only for the L²-approximation conjunct (which compares ball-restrictions); it does NOT
control the convolution. -/
theorem convolution_l2_tendsto_uniform (R C r₀ : ℝ) (S : Set (L2ballR3 R))
    (rep : L2ballR3 R → L2VF_R3)
    (hrep : ∀ f ∈ S, restrictToBall R (rep f) = f)
    (hr₀ : 0 ≤ r₀)
    (hbd : ∀ f ∈ S, ‖f‖ ≤ C)
    (hbdEnl : ∀ f ∈ S, ‖restrictToBall (R + r₀) (rep f)‖ ≤ C)
    (hmod : ∀ ε > 0, ∃ δ > 0, ∀ f ∈ S, ∀ h : Domain3, ‖h‖ < δ →
        ‖translate_L2VF h (rep f) - rep f‖ < ε)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (K : MollifierKernel) (ρf : L2ballR3 R → L2VF_R3),
      K.supportRadius ≤ r₀ ∧
      (∀ f ∈ S, (ρf f : Domain3 → EuclideanSpace ℝ (Fin 3))
          =ᵐ[volume] mollifyRep K (rep f)) ∧
      (∀ f ∈ S, ‖f - restrictToBall R (ρf f)‖ < ε) ∧
      TotallyBounded ((fun f => restrictToBall R (ρf f)) '' S) := by
  sorry -- ALLOW_SORRY: scaffold — uniform L²-mollification approximate identity.  The rate
  -- `‖η ⋆ g − g‖₂ ≤ sup_{‖h‖≤K.supportRadius} ‖τ_h g − g‖₂` (mass-one kernel) is bounded uniformly
  -- over `S` by the FK modulus `hmod`; mathlib has only the pointwise `convolution_tendsto_right`,
  -- so this is the missing L²-norm convolution approximate-identity.  Choose the kernel with
  -- support radius `≤ r₀` (small enough to make the rate `< ε`).  Total boundedness of the mollified
  -- image comes from `mollified_family_totallyBounded_L2` (Arzelà–Ascoli, step 3), fed the
  -- ENLARGED-BALL bound on `B_{R+K.supportRadius}` obtained from `hbdEnl` (at radius `R+r₀`) by
  -- monotonicity of ball mass in the radius (`K.supportRadius ≤ r₀`).

/-! ### FK step 2 — equiboundedness + equicontinuity of the mollified family -/

/-- **FK step 2 (equiboundedness).**  The CONCRETE mollified family has a uniform sup bound on
its explicit representative.

For a fixed smooth compactly supported kernel `K`, convolving an L²-bounded family with `K.η`
gives a family with a common `L^∞`-bound via Young's inequality
`‖η ⋆ g‖_∞ ≤ ‖η‖₂ · ‖g‖₂` (the kernel is in `L²` because it is continuous with compact support).
The bound is stated for the genuine representative `mollifyRep K (rep f)`, NOT for the pointwise
evaluation of an arbitrary `Lp`-class.

**Norm-correctness (Codex Gate round 3 → resolved round 4).**  Young's inequality bounds
`‖η ⋆ g‖_∞` by `‖η‖₂‖g‖₂`.  The OUTPUT bound is needed only on `x ∈ B_R` (the region the
ball-restriction of `mollifyRep` keeps), and there `mollifyRep K (rep f) x = ∫ y, η(x−y)·rep f(y)`
only sees `rep f` over the kernel-reach `B_{R + K.supportRadius}` (since `η` is supported in
`closedBall 0 K.supportRadius`).  Hence the local hypothesis is the ENLARGED-BALL bound
`hbdEnl : ∀ f ∈ S, ‖restrictToBall (R + K.supportRadius) (rep f)‖ ≤ C`
on the kernel-support enlargement `B_{R+r}` — exactly what Young needs on `B_R`.  This bound is
supplied at the call site directly from `FrechetKolmogorovInput`'s GLOBAL bound
`hbddGlobal : ‖rep f‖ ≤ C` by ball-mass monotonicity (`‖restrictToBall (R+r) g‖ ≤ ‖g‖`), so
there is no longer any upstream gap: the criterion's own strengthened data furnishes it.  The
output bound is stated for `x ∈ B_R` only. -/
theorem mollified_family_uniformly_bounded (R C : ℝ) (S : Set (L2ballR3 R))
    (rep : L2ballR3 R → L2VF_R3) (K : MollifierKernel)
    (hbdEnl : ∀ f ∈ S, ‖restrictToBall (R + K.supportRadius) (rep f)‖ ≤ C) :
    ∃ B : ℝ, ∀ f ∈ S, ∀ x : Domain3, x ∈ Metric.closedBall (0 : Domain3) R →
        ‖mollifyRep K (rep f) x‖ ≤ B := by
  -- Uniform sup-bound `B := ‖kernelL2R K‖ · C`: each pointwise value is bounded by the kernel
  -- L²-norm times the enlarged-ball mass (`mollifyRep_sup_le`), which is ≤ C by `hbdEnl`.
  refine ⟨‖kernelL2R K‖ * C, fun f hf x hx => ?_⟩
  calc ‖mollifyRep K (rep f) x‖
      ≤ ‖kernelL2R K‖ * ‖restrictToBall (R + K.supportRadius) (rep f)‖ :=
        mollifyRep_sup_le K (rep f) R hx
    _ ≤ ‖kernelL2R K‖ * C :=
        mul_le_mul_of_nonneg_left (hbdEnl f hf) (norm_nonneg _)

/-- **FK step 2 (equicontinuity).**  The CONCRETE mollified family is uniformly equicontinuous on
its explicit representative.

For a fixed smooth compactly supported kernel `K`, the modulus of continuity of `η ⋆ g` is
controlled by `‖g‖₂` times the (kernel-only) modulus of `η`
(`‖(η ⋆ g)(x) − (η ⋆ g)(y)‖ ≤ ‖g‖₂ · ‖τ_{x−y} η − η‖₂`), uniformly over the L²-bounded family —
because `K.η`, being smooth with compact support, is uniformly continuous with an L²-modulus
independent of `g`.  Stated for `mollifyRep K (rep f)`, NOT for an arbitrary operator.

**Norm-correctness (Codex Gate round 3 → resolved round 4).**  Restricting attention to
`x, y ∈ B_R` (the region the ball-restriction keeps) and bounding the difference quotient by the
kernel modulus localizes the mass factor `‖g‖₂` to the kernel-reach `B_{R + K.supportRadius}`:
the relevant inequality is
`‖(η⋆g)(x)−(η⋆g)(y)‖ ≤ ‖restrictToBall (R+K.supportRadius) g‖ · ‖τ_{x−y}K.η − K.η‖₂` for
`x, y ∈ B_R`.  Hence the local hypothesis is the ENLARGED-BALL bound `hbdEnl` on `B_{R+r}`, which
the call site supplies from `FrechetKolmogorovInput`'s GLOBAL bound `hbddGlobal : ‖rep f‖ ≤ C`
by ball-mass monotonicity (no upstream gap).  The equicontinuity conclusion is stated for
`x, y ∈ B_R` only. -/
theorem mollified_family_equicontinuous (R C : ℝ) (S : Set (L2ballR3 R))
    (rep : L2ballR3 R → L2VF_R3) (K : MollifierKernel)
    (hbdEnl : ∀ f ∈ S, ‖restrictToBall (R + K.supportRadius) (rep f)‖ ≤ C) :
    ∀ ε > 0, ∃ δ > 0, ∀ f ∈ S, ∀ x y : Domain3,
      x ∈ Metric.closedBall (0 : Domain3) R → y ∈ Metric.closedBall (0 : Domain3) R →
      ‖x - y‖ < δ →
      ‖mollifyRep K (rep f) x - mollifyRep K (rep f) y‖ < ε := by
  -- ε→δ via the kernel's L²-translation modulus `kernel_translate_L2_tendsto`, scaled by the
  -- uniform enlarged-ball mass (≤ |C|+1).  The increment is bounded by
  -- (enlarged mass)·(kernel modulus) via `mollifyRep_sub_le`.
  intro ε hε
  -- Uniform mass bound `M := |C| + 1 > 0`, so it can divide ε.
  set M : ℝ := |C| + 1 with hM
  have hMpos : 0 < M := by positivity
  -- The kernel modulus `m h := ‖τ_h kernel − kernel‖ → 0` as `h → 0`; choose δ making it < ε/M.
  have htend := kernel_translate_L2_tendsto K
  have hpos : 0 < ε / M := div_pos hε hMpos
  -- Pull back the `< ε/M` neighborhood of `0 ∈ ℝ` along the modulus to a `0`-neighborhood in
  -- `Domain3`, then extract a metric radius δ.
  have hball : {z : ℝ | z < ε / M} ∈ 𝓝 (0 : ℝ) :=
    IsOpen.mem_nhds (isOpen_Iio) (by simpa using hpos)
  have hpre : (fun h : Domain3 => ‖translate_L2R h (kernelL2R K) - kernelL2R K‖) ⁻¹'
      {z : ℝ | z < ε / M} ∈ 𝓝 (0 : Domain3) := htend hball
  rw [Metric.mem_nhds_iff] at hpre
  obtain ⟨δ, hδpos, hδsub⟩ := hpre
  refine ⟨δ, hδpos, fun f hf x y hx hy hxy => ?_⟩
  -- The shift `x − y` lies in the δ-ball around 0, so the kernel modulus there is `< ε/M`.
  have hmem : (x - y) ∈ Metric.ball (0 : Domain3) δ := by
    simp only [Metric.mem_ball, dist_zero_right]
    simpa using hxy
  have hmod_lt : ‖translate_L2R (x - y) (kernelL2R K) - kernelL2R K‖ < ε / M := hδsub hmem
  have hmod_nonneg : 0 ≤ ‖translate_L2R (x - y) (kernelL2R K) - kernelL2R K‖ := norm_nonneg _
  -- Enlarged-ball mass ≤ C ≤ |C| < M.
  have hmass : ‖restrictToBall (R + K.supportRadius) (rep f)‖ ≤ M :=
    le_trans (hbdEnl f hf) (by rw [hM]; linarith [le_abs_self C])
  have hmass_nonneg : 0 ≤ ‖restrictToBall (R + K.supportRadius) (rep f)‖ := norm_nonneg _
  -- Combine: increment ≤ mass · modulus ≤ M · (ε/M) = ε  (strict because modulus < ε/M, M > 0).
  calc ‖mollifyRep K (rep f) x - mollifyRep K (rep f) y‖
      ≤ ‖restrictToBall (R + K.supportRadius) (rep f)‖
          * ‖translate_L2R (x - y) (kernelL2R K) - kernelL2R K‖ :=
        mollifyRep_sub_le K (rep f) R hx hy
    _ ≤ M * ‖translate_L2R (x - y) (kernelL2R K) - kernelL2R K‖ :=
        mul_le_mul_of_nonneg_right hmass hmod_nonneg
    _ < M * (ε / M) := by
        exact mul_lt_mul_of_pos_left hmod_lt hMpos
    _ = ε := by field_simp

/-! ### FK step 3 — Arzelà–Ascoli ⇒ total boundedness in L²(ball) -/

/-- **FK step 3.**  Arzelà–Ascoli: a uniformly bounded, uniformly equicontinuous family of
continuous functions on the compact ball `B_R` is totally bounded in `C(B_R)`, hence (via the
continuous embedding `C(B_R) ↪ L²(B_R)` on a finite-measure ball) totally bounded in `L²(B_R)`.

Consumes `mollified_family_uniformly_bounded` (step 2a) and `mollified_family_equicontinuous`
(step 2b) for the CONCRETE kernel `K`; produces the total boundedness used by
`convolution_l2_tendsto_uniform`.  The L²-classes `ρf f` whose representative is
`mollifyRep K (rep f)` are supplied (with the a.e. agreement hypothesis `hρf`) so the result
lands in `L²(B_R)` rather than `C(B_R)`.

**Norm-correctness (Codex Gate round 3 → resolved round 4).**  Both steps 2a/2b it consumes are
stated on `B_R` only and rest on the ENLARGED-BALL bound
`‖restrictToBall (R+K.supportRadius) (rep f)‖ ≤ C`, which the call site derives from
`FrechetKolmogorovInput`'s GLOBAL bound `hbddGlobal : ‖rep f‖ ≤ C` by ball-mass monotonicity.
Arzelà–Ascoli runs on the COMPACT ball `B_R`, where
the ball-restriction `restrictToBall R (ρf f)` lives, so the enlarged-ball sup/equicontinuity bounds
on `B_R` are exactly enough.  This lemma threads the same enlarged-ball bound `hbdEnl`. -/
theorem mollified_family_totallyBounded_L2 (R C : ℝ) (S : Set (L2ballR3 R))
    (rep : L2ballR3 R → L2VF_R3) (K : MollifierKernel)
    (ρf : L2ballR3 R → L2VF_R3)
    (hρf : ∀ f ∈ S, (ρf f : Domain3 → EuclideanSpace ℝ (Fin 3))
        =ᵐ[volume] mollifyRep K (rep f))
    (hbdEnl : ∀ f ∈ S, ‖restrictToBall (R + K.supportRadius) (rep f)‖ ≤ C) :
    TotallyBounded ((fun f => restrictToBall R (ρf f)) '' S) := by
  sorry -- ALLOW_SORRY: scaffold — Arzelà–Ascoli on the compact ball `B_R` (mathlib's abstract
  -- `ArzelaAscoli.isCompact_of_equicontinuous` / total-boundedness form) from steps 2a+2b
  -- (each fed the ENLARGED-BALL bound `hbdEnl` on `B_{R+K.supportRadius}` and stated on `B_R`,
  -- NOT a global bound) for the concrete `mollifyRep K (rep f)`, then transfer
  -- `C(B_R)`-total-boundedness to `L²(B_R)` via the finite-measure embedding (using `hρf` to
  -- identify representatives; only `x ∈ B_R` values of `mollifyRep` enter `restrictToBall R`).

/-! ### FK step 4 — total-boundedness transfer under uniform approximation -/

/-- **FK step 4.**  Total-boundedness transfer.  In a metric space, a set `S` that is uniformly
ε-approximable (for every `ε > 0`) by a totally bounded set is itself totally bounded.

This is the abstract glue between step 1 (uniform mollification approximation) and step 3
(total boundedness of the mollified family): an ε-net of the approximant, fattened by ε, is a
`2ε`-net of `S`. -/
theorem totallyBounded_of_uniform_approx {α : Type*} [PseudoMetricSpace α] (S : Set α)
    (happrox : ∀ ε > 0, ∃ T : Set α, TotallyBounded T ∧
      ∀ s ∈ S, ∃ t ∈ T, dist s t < ε) :
    TotallyBounded S := by
  rw [Metric.totallyBounded_iff]
  intro ε hε
  -- Approximate `S` within `ε/2` by a totally bounded `T`.
  obtain ⟨T, hT, hTapprox⟩ := happrox (ε / 2) (by linarith)
  -- A finite `ε/2`-net `t` of `T`.
  obtain ⟨t, ht_fin, ht_cover⟩ := (Metric.totallyBounded_iff.mp hT) (ε / 2) (by linarith)
  -- `t` is an `ε`-net of `S` by the triangle inequality.
  refine ⟨t, ht_fin, fun s hs => ?_⟩
  obtain ⟨τ, hτT, hsτ⟩ := hTapprox s hs
  have hτ_mem : τ ∈ ⋃ y ∈ t, Metric.ball y (ε / 2) := ht_cover hτT
  simp only [Set.mem_iUnion, Metric.mem_ball, exists_prop] at hτ_mem ⊢
  obtain ⟨y, hyt, hτy⟩ := hτ_mem
  refine ⟨y, hyt, ?_⟩
  calc dist s y ≤ dist s τ + dist τ y := dist_triangle s τ y
    _ < ε / 2 + ε / 2 := by linarith
    _ = ε := by ring

/-! ### DELIVERABLE — discharge of `FrechetKolmogorovInput` -/

/-- **DELIVERABLE.  Fréchet–Kolmogorov (Riesz) L²-precompactness criterion** — a genuine
discharge of `RellichBall.FrechetKolmogorovInput` (type copied verbatim, no weakening).

Assembles the standard mollification route: from the uniform L²-translation modulus
(`convolution_l2_tendsto_uniform`, step 1) each family member is uniformly ε-approximated by its
mollification, whose image is totally bounded by Arzelà–Ascoli
(`mollified_family_totallyBounded_L2`, step 3); the transfer lemma
(`totallyBounded_of_uniform_approx`, step 4) makes `S` totally bounded, and completeness of
`L2ballR3 R` upgrades total boundedness to precompactness
(`isCompact_iff_totallyBounded_isComplete`), giving the compact `K ⊇ S`.

**Enlarged-ball bound — RESOLVED via the criterion's global bound (Codex Gate round 3, high).**
The helper lemmas (steps 1–3) require, honestly, an ENLARGED-BALL bound
`hbdEnl : ∀ f ∈ S, ‖restrictToBall (R + r₀) (rep f)‖ ≤ C` on the kernel-support enlargement
`B_{R+r₀}` (NOT just the single-radius ball bound `‖f‖ ≤ C`, which cannot prevent arbitrarily
large low-frequency mass on the annulus `B_{R+r₀} ∖ B_R`).

`FrechetKolmogorovInput`'s strengthened type hands the prover, beyond the in-ball bound `hbd` and
the translation modulus `hmod`, a uniform GLOBAL L²-norm bound on the representatives:
* `hbddGlobal : ∀ f ∈ S, ‖rep f‖ ≤ C`.

From `hbddGlobal` the enlarged-ball bound is IMMEDIATE for any `r₀ ≥ 0`, by monotonicity of ball
mass in the radius: `‖restrictToBall (R + r₀) (rep f)‖ ≤ ‖rep f‖ ≤ C` (the same
`restrict_le_self`/`eLpNorm_mono_measure` chain as `RellichBall.admissible_family_uniform_bound`).
This is the standard Riesz full-mass control of Fréchet–Kolmogorov; it carries no Sobolev/gradient
content.  The actual Navier–Stokes call site `localRellichInput_of_frechetKolmogorov` supplies it
from its admissible family's GLOBAL `‖w‖ ≤ M` bound.

**Assembly (pure proof-body fill, no upstream blocker).**  Derive `hbdEnl` from `hbddGlobal` by
ball-mass monotonicity; feed `hbdEnl`, `hbd`, `hrep`, `hmod` into `convolution_l2_tendsto_uniform`
(step 1) to get, for each `ε`, a totally bounded mollified image approximating `S` within `ε`;
`totallyBounded_of_uniform_approx` (step 4) makes `S` totally bounded; closure of the totally
bounded `S` is compact (`isCompact_iff_totallyBounded_isComplete`, `L2ballR3 R` complete); take
`K := closure S`. -/
theorem frechetKolmogorov_holds : FrechetKolmogorovInput := by
  sorry -- ALLOW_SORRY: scaffold — pure proof-body fill (no upstream blocker after the
  -- `FrechetKolmogorovInput` strengthening).  Derive the enlarged-ball bound
  -- `hbdEnl : ‖restrictToBall (R+r₀) (rep f)‖ ≤ C` from the criterion's GLOBAL bound
  -- `hbddGlobal : ‖rep f‖ ≤ C` by monotonicity of ball mass in the radius (restrict_le_self /
  -- eLpNorm_mono_measure, as in RellichBall.admissible_family_uniform_bound).  Then feed
  -- `hbdEnl`/`hbd`/`hrep`/`hmod` into convolution_l2_tendsto_uniform → totallyBounded_of_uniform_approx
  -- → take `K := closure S` (compact via isCompact_iff_totallyBounded_isComplete; L2ballR3 R complete).

end LerayHopf
