import LerayHopf.R3.RellichBall                  -- FrechetKolmogorovInput, translate_L2VF, L2ballR3, restrictToBall
import Mathlib.Analysis.Convolution               -- MeasureTheory.convolution, ContDiffBump approximate identity
import Mathlib.Topology.UniformSpace.Cauchy       -- TotallyBounded, isCompact_iff_totallyBounded_isComplete

namespace LerayHopf
open MeasureTheory Filter Topology Metric
open scoped FourierTransform ENNReal

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

/-- **Helper signature for `RellichBall.integrable_viscous_integrand_of_memH1`.**

For `w ∈ H¹(ℝ³)` (i.e. `memH1VF_R3 w`, defined as `TemperedDistribution.MemSobolev 1 2` on each
complex component `cⱼ = L2VF_projComponentC_R3 j w`), the L²-Fourier transform `𝓕 cⱼ` is
square-integrable against the genuine `H¹` weight `1 + ‖ξ‖²`:

  `Integrable (fun ξ ↦ (1 + ‖ξ‖²) · ‖(𝓕 cⱼ) ξ‖²)`.

This is the distribution-faithful core that mathlib lacks: it is precisely the assertion that
the `MemSobolev 1 2` membership (an existence-of-`Lp`-witness for the UNBOUNDED multiplier
`(1+‖ξ‖²)^(1/2)` applied to `𝓕 (cⱼ : 𝓢')`) extracts the concrete weighted-L²
integrability of the L²-Fourier representative.  Once available, domination by
`(2π)²‖ξ‖² ≤ (2π)²(1+‖ξ‖²)` (and `(2π)²(1+‖ξ‖²)·‖·‖² = (2π)²(weighted integrand)`) closes
`RellichBall.integrable_viscous_integrand_of_memH1` as a pure proof-body fill — the prover
wires this helper there WITHOUT editing that statement.

NOTE (lean-coder): the residual `sorry` in `RellichBall.lean` is on an EXISTING statement and
is itself a pure proof-body fill (a `lean-prover` task); this lemma is the single missing
ingredient it needs.  The reduction is "extract a.e. `(1+‖ξ‖²)^(1/2)·(𝓕 cⱼ) = f' ∈ L²` from
`MemSobolev`, square, recognize the integrand".  -/
theorem memH1_weightedL2_integrable (w : L2VF_R3) (hw : memH1VF_R3 w) (j : Fin 3) :
    Integrable (fun ξ : Domain3 =>
        (1 + ‖ξ‖ ^ 2) * ‖(𝓕 (L2VF_projComponentC_R3 j w) : L2C_R3) ξ‖ ^ 2)
      (volume : Measure Domain3) := by
  sorry -- ALLOW_SORRY: scaffold — H¹ (MemSobolev 1 2 on each component) ⇒ concrete weighted-L²
  -- integrability of the L²-Fourier transform.  Needs the a.e. characterization of
  -- `TemperedDistribution.smulLeftCLM` for the UNBOUNDED weight `(1+‖ξ‖²)^(1/2)` on an
  -- `Lp`-coerced distribution (mathlib `Lp.toTemperedDistribution_smul_eq` covers only
  -- MemLp-bounded multipliers).  This is the single ingredient RellichBall's residual sorry needs.

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
  sorry -- ALLOW_SORRY: scaffold — for `x ∈ B_R`, Young's inequality `‖(η ⋆ g) x‖ ≤ ‖K.η‖₂ · ‖g‖₂`
  -- localizes: the integrand `η(x−y)·g(y)` is supported in `y ∈ B_{R + K.supportRadius}` (kernel
  -- reach), so `‖(η ⋆ g) x‖ ≤ ‖K.η‖₂ · ‖restrictToBall (R+K.supportRadius) g‖`, giving the uniform
  -- sup-bound `B := ‖K.η‖₂ · C` over `B_R` from the ENLARGED-BALL hypothesis `hbdEnl` (itself
  -- supplied from `FrechetKolmogorovInput`'s GLOBAL bound `hbddGlobal` by ball-mass monotonicity);
  -- `K.η ∈ L²` from continuity + compact support (`K.smooth.continuous`, `K.hasCompactSupport`).

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
  sorry -- ALLOW_SORRY: scaffold — for `x, y ∈ B_R`, `‖(η⋆g)(x)−(η⋆g)(y)‖ ≤ ‖restrictToBall
  -- (R+K.supportRadius) g‖ · ‖τ_{x−y}K.η − K.η‖₂` with `g = rep f` (kernel reach `K.supportRadius`
  -- localizes the mass factor to `B_{R+r}`); the kernel modulus is independent of `g` (uniform
  -- continuity of `K.η` from `K.smooth`/`K.hasCompactSupport`), giving uniform equicontinuity on
  -- `B_R` over the family from the ENLARGED-BALL hypothesis `hbdEnl` (itself supplied from
  -- `FrechetKolmogorovInput`'s GLOBAL bound `hbddGlobal` by ball-mass monotonicity).

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
  sorry -- ALLOW_SORRY: scaffold — fatten an ε-net of the totally bounded approximant `T` by ε
  -- to get a `2ε`-net of `S`; `totallyBounded_iff` / triangle inequality.

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
