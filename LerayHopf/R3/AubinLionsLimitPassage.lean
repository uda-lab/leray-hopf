/-
# LerayHopf.R3.AubinLionsLimitPassage — milestone P2 (Aubin–Lions reduction + reusable analytic core)

**Milestone:** `p2-aubin-lions` (honest PARTIAL substantiation; contract
`docs/scratch/p2-aubin-lions.md`, ADDENDUM "Scope refinement" governs the scope below).

This module IMPORTS `R3.AxiomaticClosure` (justified — it *produces* `AubinLionsPackage_R3`
and *consumes* `GalerkinSolutionData_R3`, both of which live in `AxiomaticClosure.lean` with
no lighter exposing module). This is the single heavy import; unlike P3 (`R3.SpatialCompactness`,
deliberately standalone) it is unavoidable here. It also reuses P3
(`localCompactness_R3_of_ballCompact`, `LocalRellichInput`) and R3-d's `b`-bound analytic core
(via `F.b_bound` in `R3.TrilinearEstimate`'s downstream `R3NSForms`).

**Refined scope (ADDENDUM — supersedes §3 Tier P / §9 where they conflict; UPDATED post-#15):**
P2 targets the **Aubin–Lions reduction** (spatial+time ⇒ package) plus **two reusable analytic
lemmas**. As of issue #15 the centerpiece reduction `aubinLionsPackage_R3_of_timeCompactness` (C2)
is **closed sorry-free**: its spatial half is PROVED axiom-free, and the single irreducible
Bochner-time a.e.-L² extraction is isolated as ONE marked axiom `galerkinSpaceTimeExtraction_R3`
(the content mathlib's absent `W^{1,p}(0,T;X)` / vector-valued weak time derivative / Aubin–Lions
theory would supply). The deliverables are otherwise proved axiom-free.

**PROVED, axiom-free (no `sorryAx`):**

* `spatialInput_R3_of_localRellich` (S1) — the `spatial` half, discharged by reusing P3.
* `bForm_tendsto_of_strongL2` (N1) — nonlinear `b`-term passage under strong L² (the R3-d payoff).
* private Steklov building blocks for the (still-open) C2 reduction:
  `galerkin_curve_continuous`, `steklovAvg` (def), `steklovAvg_norm_le_u0` (uniform L² bound),
  `steklovAvg_approx` (time-modulus average↔curve estimate), and `galerkin_norm_le_u0`.

* `kineticEnergy_lsc_bound` (E1) — #14-P discharge, now `sorry`-FREE (issue #31). The full
  norm-lsc-transfer + ball-exhaustion proof (`kineticEnergyLscTransfer`, `continuous_restrictToBall`,
  `norm_restrictToBall_le'`, `normSq_restrictToBall_eq_setIntegral`,
  `tendsto_normSq_restrictToBall`, `eLpNorm_two_eq_ofReal_sqrt`), wired through the #14-C
  `u_aestronglyMeasurable` field and `galerkin_norm_le_u0`. The former residual `MemLp`-gap `sorry`
  (time-integrability of a Bochner-form integrand) is DISCHARGED by the issue #31 strengthening of
  `AubinLionsPackage_R3.strong_convergence` to its faithful `eLpNorm`-form: the field now supplies
  the time-`L²` convergence directly, so `hconv` is exactly `strong_convergence R`.

**CLOSED (issue #15) — C2 is sorry-free:**

* `aubinLionsPackage_R3_of_timeCompactness` (C2) — the centerpiece Aubin–Lions assembly. Its
  spatial half is PROVED axiom-free (the `steklovAvg_spatial_extraction` chain over the FK-derived
  `LocalRellichInput`); every package field is then assembled axiom-free from the conclusion of the
  single isolated extraction axiom `galerkinSpaceTimeExtraction_R3`. The constructor no longer takes
  a `TimeCompactnessInput` argument — that modulus is absorbed into the (now unconditional)
  extraction axiom (see issue #15 collapse). The `TimeCompactnessInput` structure and the
  `galerkin_curves_equicontinuous` helper are retained as legacy/unused scaffolding (referenced only
  in docs), kept for the eventual discharge of the extraction axiom.

**Documented residual frontier (the limit-passage half stays axiomatic upstream):** the limit-passage
conclusions (b) `WeakFormNS`, (d) initial trace, and (e) energy class require the absent
vector-valued weak time-derivative / `W^{1,p}(0,T;X)` theory and are carried by the upstream
`galerkin_limit_passage_R3` axiom (not by this file). Bundling them into a `GoodRepresentativeInput`
hypothesis would re-assert the conclusions (smuggling), so per the ADDENDUM we DROP that and
`galerkinLimitPassage_R3_of_goodRep`. P2 does NOT itself produce the full `galerkin_limit_passage_R3`
conclusion (this mirrors R3-d, which proved `b`-form lemmas without producing `Nonempty R3NSForms`).

**Axioms backing this file (issue #44):** `galerkinSpaceTimeExtraction_R3` is a PROVED `theorem`
(no sorry in its body) delegating to `u_lim_aestronglyMeasurable` in `ArzelaAscoliTime.lean`.
The two residual axioms live in `ArzelaAscoliTime.lean`:
- `galerkin_spacetime_precompact_R3` — refine-capable local Aubin–Lions–Simon spacetime
  precompactness (L²-in-time Bochner convergence on balls; Mathlib lacks this)
- `galerkin_weakLimit_R3` — Banach–Alaoglu + div-free weak limit in `L2Sigma_R3`
  (Mathlib lacks weak compactness in Hilbert + weak-closedness of div-free subspace)
Note: `galerkin_equicontinuity_from_ODE` (T0.1) was DELETED as UNSOUND (see `ArzelaAscoliTime.lean`).
No `opaque`/`constant`/`unsafe`. The honest isolated hypotheses (P3's `LocalRellichInput`,
R3-d's `hdiv`, P5's `SchwartzGalerkinBasis.dense_span`) remain explicit *arguments*, not axioms.

Target axiom this milestone discharges (issue #15): `aubin_lions_R3` is REMOVED — its spatial half
PROVED, its time content swapped 1-for-1 for the strictly-thinner `galerkinSpaceTimeExtraction_R3`.
-/

-- Import-cycle audit (REQUIRED — Hard rule 10). Verified against the actual import lines:
--   * `R3.AxiomaticClosure` imports ONLY `EvolutionTriple`, `R3.Regularity`, and a mathlib
--     interval-integral module — it does NOT import this file, `R3.SpatialCompactness`, or
--     `R3.TrilinearEstimate`. So importing it here is acyclic.
--   * `R3.SpatialCompactness` imports `R3.Regularity` + mathlib (standalone); `R3.TrilinearEstimate`
--     imports `R3.DivergenceFree` + mathlib (leaf). Importing both here adds no cycle.
--   * This file is a LEAF (nothing imports it). It is the unique place that may reference
--     `AubinLionsPackage_R3` AND reuse P3 — neither of those modules can reference the other.
import LerayHopf.R3.AxiomaticClosure     -- AubinLionsPackage_R3, GalerkinSolutionData_R3, r3Evolution, R3NSForms
import LerayHopf.R3.SpatialCompactness   -- localCompactness_R3_of_ballCompact, LocalRellichInput
import LerayHopf.R3.ArzelaAscoliTime     -- issue #44: T0.1/T0.2 axioms + T1–T4 Arzelà–Ascoli chain + u_lim_aestronglyMeasurable
import LerayHopf.R3.TrilinearEstimate    -- b-bound analytic core (downstream of R3NSForms.b_bound)
import LerayHopf.R3.FourierL2            -- 𝓕, L2C_R3, viscousFormSq_R3_eq_integral_normSq_fourier (F7 spectral exposure for the viscous/H¹ Steklov Jensen bound)
import LerayHopf.R3.WeightedFourierCommute -- mulBdd bounded-multiplier commute + truncated weight (closes the viscous/H¹ Steklov Jensen gate)
import LerayHopf.R3.GalerkinODE          -- galerkinCurve_reg_mem (H¹ regularity of any curve in the Galerkin subspace)
import LerayHopf.R3.SobolevEmbedding     -- memSobolev_of_finite_weightedFourier_R3 (H¹ from finite weighted-Fourier integral; the memH1 conjunct of viscous_pointwise_lsc)
import Mathlib.MeasureTheory.Integral.Bochner.Set   -- set/interval integrals over balls
import Mathlib.MeasureTheory.Function.UnifTight      -- UnifTight + tendsto_Lp_of_tendsto_ae (Vitali) for the C2 dominated-Lp passage
import Mathlib.MeasureTheory.Function.UniformIntegrable -- UnifIntegrable + unifIntegrable_of for the C2 dominated-Lp passage

namespace LerayHopf

open MeasureTheory Filter Topology Metric
open scoped FourierTransform   -- `𝓕` notation for the viscous/H¹ Steklov spectral Jensen bound

/-! ### Tier H — the isolated time-frontier hypothesis (for the still-open C2) -/

/-- Isolated analytic frontier: UNIFORM time-equicontinuity in L² of the Galerkin curves.

For every error `ε > 0`, there is a shift bound `δ > 0` such that, uniformly in `n` and in
`s, t ∈ [0,T]` with `|s - t| < δ`, the L² distance of the Galerkin states is `< ε`:
    `‖(galSeq n).u s - (galSeq n).u t‖_{L²(ℝ³)} < ε`.

This is the L²-modulus content of the Bochner–Sobolev bound `‖uₙ‖_{W^{1,?}(0,T;X)} ≤ C`,
which is derivable IN PRINCIPLE from `GalerkinSolutionData_R3.u_hasDeriv` + the energy/
regularity bounds, but whose vector-valued-Sobolev packaging mathlib LACKS (no
`W^{1,p}(0,T;X)`, no weak time derivative, no Aubin–Lions lemma).

Honesty (no-smuggle): this field speaks ONLY about the GIVEN Galerkin sequence's
self-equicontinuity in time; it supplies NEITHER a subsequence, NOR a limit, NOR any
space-time convergence, NOR any spatial compactness (that is P3's job). It is a uniform
modulus of continuity, nothing more. -/
structure TimeCompactnessInput (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν T : ℝ) (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n) where
  /-- Uniform-in-`n` L² modulus of time continuity of the Galerkin curves on `[0,T]`. -/
  uniform_time_modulus : ∀ ε : ℝ, 0 < ε →
    ∃ δ : ℝ, 0 < δ ∧ ∀ (n : ℕ) (s t : Time),
      s ∈ Set.Icc (0 : ℝ) T → t ∈ Set.Icc (0 : ℝ) T → |s - t| < δ →
      ‖((galSeq n).u s : L2VF_R3) - ((galSeq n).u t : L2VF_R3)‖ < ε

/-! ### Tier S — discharge the spatial input via P3 -/

/-- The `spatial` hypothesis required by the Aubin–Lions combination is exactly P3's
`localCompactness_R3_of_ballCompact`. Supplying P3's isolated input discharges it.

This type is the `aubin_lions_R3` `spatial` binder verbatim (`AxiomaticClosure.lean:449–459`). -/
theorem spatialInput_R3_of_localRellich (B : LocalRellichInput) :
    ∀ (M : ℝ) (z : ℕ → L2VF_R3),
      (∀ n, z n ∈ L2Sigma_R3) → (∀ n, memH1VF_R3 (z n)) →
      (∀ n, ‖z n‖ ≤ M) → (∀ n, viscousFormSq_R3 1 (z n) ≤ M ^ 2) →
      ∃ (ψ : ℕ → ℕ) (g : L2VF_R3), StrictMono ψ ∧ g ∈ L2Sigma_R3 ∧
        ∀ R : ℝ, Filter.Tendsto
          (fun n => ∫ x in Metric.closedBall (0 : Domain3) R,
            ‖((z (ψ n)) x : EuclideanSpace ℝ (Fin 3)) - (g x : EuclideanSpace ℝ (Fin 3))‖ ^ 2
            ∂(volume : Measure Domain3))
          Filter.atTop (nhds 0) := by
  -- Reuse of P3's local Rellich compactness; the type is the `aubin_lions_R3` `spatial`
  -- binder verbatim, so this gives the combination lemma a clean spatial argument.
  exact localCompactness_R3_of_ballCompact B

/-! ### Tier N — nonlinear `b`-term passage (the reusable analytic core, R3-d payoff) -/

/-- **Nonlinear convection term passes to the limit under strong L² convergence.**

For a fixed Schwartz div-free test `w`, if `uₙ → u` and `vₙ → v` strongly in L²(ℝ³) with a
uniform bound, then `F.b uₙ vₙ w → F.b u v w`. This is the analytic payoff of R3-d's
`b_bound` (bilinear L²-continuity of `b` in its first two slots for Schwartz tests). -/
theorem bForm_tendsto_of_strongL2 (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (w : L2Sigma_R3) (hw : IsSchwartzDivFree_R3 w)
    (uSeq vSeq : ℕ → L2Sigma_R3) (u v : L2Sigma_R3)
    (hu : Tendsto (fun n => ((uSeq n : L2VF_R3))) atTop (𝓝 (u : L2VF_R3)))
    (hv : Tendsto (fun n => ((vSeq n : L2VF_R3))) atTop (𝓝 (v : L2VF_R3))) :
    Tendsto (fun n => F.b (uSeq n) (vSeq n) w) atTop (𝓝 (F.b u v w)) := by
  -- Obtain the bilinear L²-bound constant `C` for the fixed Schwartz test `w`.
  obtain ⟨C, hC⟩ := F.b_bound w hw
  -- Algebraic decomposition (bilinearity in slots 1,2):
  --   b uₙ vₙ w - b u v w = b (uₙ - u) vₙ w + b u (vₙ - v) w.
  have hdecomp : ∀ n,
      F.b (uSeq n) (vSeq n) w - F.b u v w
        = F.b (uSeq n - u) (vSeq n) w + F.b u (vSeq n - v) w := by
    intro n
    have e1 : F.b (uSeq n) (vSeq n) w
        = F.b (uSeq n - u) (vSeq n) w + F.b u (vSeq n) w := by
      have := F.b_add_1 (uSeq n - u) u (vSeq n) w
      simpa [sub_add_cancel] using this
    have e2 : F.b u (vSeq n) w
        = F.b u (vSeq n - v) w + F.b u v w := by
      have := F.b_add_2 u (vSeq n - v) v w
      simpa [sub_add_cancel] using this
    rw [e1, e2]; ring
  -- Pointwise bound on the difference via `b_bound` applied to each summand.
  have hbound : ∀ n,
      |F.b (uSeq n) (vSeq n) w - F.b u v w|
        ≤ C * ‖((uSeq n : L2VF_R3)) - (u : L2VF_R3)‖ * ‖(vSeq n : L2VF_R3)‖
          + C * ‖(u : L2VF_R3)‖ * ‖((vSeq n : L2VF_R3)) - (v : L2VF_R3)‖ := by
    intro n
    rw [hdecomp n]
    calc |F.b (uSeq n - u) (vSeq n) w + F.b u (vSeq n - v) w|
        ≤ |F.b (uSeq n - u) (vSeq n) w| + |F.b u (vSeq n - v) w| := abs_add_le _ _
      _ ≤ C * ‖((uSeq n - u : L2Sigma_R3) : L2VF_R3)‖ * ‖(vSeq n : L2VF_R3)‖
            + C * ‖(u : L2VF_R3)‖ * ‖((vSeq n - v : L2Sigma_R3) : L2VF_R3)‖ :=
          add_le_add (hC _ _) (hC _ _)
      _ = C * ‖((uSeq n : L2VF_R3)) - (u : L2VF_R3)‖ * ‖(vSeq n : L2VF_R3)‖
            + C * ‖(u : L2VF_R3)‖ * ‖((vSeq n : L2VF_R3)) - (v : L2VF_R3)‖ := by
          rw [AddSubgroupClass.coe_sub, AddSubgroupClass.coe_sub]
  -- The upper bound sequence tends to 0.
  have hu' : Tendsto (fun n => ‖((uSeq n : L2VF_R3)) - (u : L2VF_R3)‖) atTop (𝓝 0) := by
    have hsub : Tendsto (fun n => ((uSeq n : L2VF_R3)) - (u : L2VF_R3)) atTop (𝓝 0) := by
      have := hu.sub (tendsto_const_nhds (x := (u : L2VF_R3)))
      simpa using this
    simpa using hsub.norm
  have hv' : Tendsto (fun n => ‖((vSeq n : L2VF_R3)) - (v : L2VF_R3)‖) atTop (𝓝 0) := by
    have hsub : Tendsto (fun n => ((vSeq n : L2VF_R3)) - (v : L2VF_R3)) atTop (𝓝 0) := by
      have := hv.sub (tendsto_const_nhds (x := (v : L2VF_R3)))
      simpa using this
    simpa using hsub.norm
  have hvnorm : Tendsto (fun n => ‖(vSeq n : L2VF_R3)‖) atTop (𝓝 ‖(v : L2VF_R3)‖) := hv.norm
  have hUpper :
      Tendsto (fun n =>
        C * ‖((uSeq n : L2VF_R3)) - (u : L2VF_R3)‖ * ‖(vSeq n : L2VF_R3)‖
          + C * ‖(u : L2VF_R3)‖ * ‖((vSeq n : L2VF_R3)) - (v : L2VF_R3)‖)
        atTop (𝓝 0) := by
    have t1 : Tendsto (fun n =>
        C * ‖((uSeq n : L2VF_R3)) - (u : L2VF_R3)‖ * ‖(vSeq n : L2VF_R3)‖)
        atTop (𝓝 (C * 0 * ‖(v : L2VF_R3)‖)) :=
      ((tendsto_const_nhds.mul hu').mul hvnorm)
    have t2 : Tendsto (fun n =>
        C * ‖(u : L2VF_R3)‖ * ‖((vSeq n : L2VF_R3)) - (v : L2VF_R3)‖)
        atTop (𝓝 (C * ‖(u : L2VF_R3)‖ * 0)) :=
      (tendsto_const_nhds.mul hv')
    have := t1.add t2
    simpa using this
  -- Squeeze the absolute value of the difference to 0, then conclude.
  have hdiff : Tendsto (fun n => F.b (uSeq n) (vSeq n) w - F.b u v w) atTop (𝓝 0) := by
    refine (tendsto_zero_iff_abs_tendsto_zero _).mpr ?_
    exact squeeze_zero (fun n => abs_nonneg _) hbound hUpper
  have := hdiff.add (tendsto_const_nhds (x := F.b u v w))
  simpa using this

/-! ### Tier E — energy inequality (the reachable kinetic-lsc half of conclusion (c)) -/

/-- **Galerkin-side uniform energy bound (provable core of E1).** For every `n` and every
`t ≥ 0`, the Galerkin state is L²-bounded by the initial datum: `‖(galSeq n).u t‖ ≤ ‖u₀‖`.

Proof: `energy_bound` gives `½‖uₙ t‖² ≤ ½‖𝔊.P n u₀‖²`; `𝔊.norm_le` gives
`‖𝔊.P n u₀‖ ≤ ‖u₀‖`; combine. This is the side of E1 that needs no time-measurability. -/
theorem galerkin_norm_le_u0 (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (u₀ : L2Sigma_R3) (n : ℕ)
    (gs : GalerkinSolutionData_R3 𝔊 F ν u₀ n) {t : ℝ} (ht : 0 ≤ t) :
    ‖(gs.u t : L2VF_R3)‖ ≤ ‖(u₀ : L2VF_R3)‖ := by
  have hP : ‖𝔊.P n (u₀ : L2VF_R3)‖ ≤ ‖(u₀ : L2VF_R3)‖ := 𝔊.norm_le n (u₀ : L2VF_R3)
  have henergy := gs.energy_bound t ht
  -- `½‖uₙ t‖² ≤ ½‖P n u₀‖² ≤ ½‖u₀‖²`, so `‖uₙ t‖² ≤ ‖u₀‖²`, hence `‖uₙ t‖ ≤ ‖u₀‖`.
  have hsq : ‖(gs.u t : L2VF_R3)‖ ^ 2 ≤ ‖(u₀ : L2VF_R3)‖ ^ 2 := by
    have h2 : ‖𝔊.P n (u₀ : L2VF_R3)‖ ^ 2 ≤ ‖(u₀ : L2VF_R3)‖ ^ 2 := by
      have := mul_le_mul hP hP (norm_nonneg _) (norm_nonneg _)
      nlinarith [this]
    nlinarith [henergy, h2]
  exact le_of_sq_le_sq hsq (norm_nonneg _)

/-- The Galerkin velocity curve `t ↦ ((galSeq n).u t : L2VF_R3)` is continuous on **forward**
time `Set.Ici 0` (it is even differentiable there by `u_hasDeriv`).

Forward-only: `u_hasDeriv` now guarantees differentiability only for `t ≥ 0` (the curve is a
physical Galerkin solution, confined only on forward time).  Everything downstream uses the
curve only on `[0,T] ⊆ Ici 0`, so forward continuity suffices. -/
theorem galerkin_curve_continuous (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (u₀ : L2Sigma_R3) (n : ℕ)
    (gs : GalerkinSolutionData_R3 𝔊 F ν u₀ n) :
    ContinuousOn (fun s => (gs.u s : L2VF_R3)) (Set.Ici 0) :=
  fun t ht => (gs.u_hasDeriv t ht).continuousAt.continuousWithinAt

/-- For an a.e.-strongly-measurable `β`-valued time curve `h` whose pointwise squared norm is
integrable, the time-`L²` seminorm is `ENNReal.ofReal (√(∫ ‖h t‖² dμ))`. (Standard `eLpNorm`
unfolding for `p = 2`; used to feed the integral-to-`eLpNorm` step of E1.) -/
private theorem eLpNorm_two_eq_ofReal_sqrt {β : Type*} [NormedAddCommGroup β]
    {μ : Measure ℝ} (h : ℝ → β)
    (hint : Integrable (fun t => ‖h t‖ ^ 2) μ) :
    eLpNorm h 2 μ = ENNReal.ofReal (Real.sqrt (∫ t, ‖h t‖ ^ 2 ∂μ)) := by
  rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num), eLpNorm'_eq_lintegral_enorm]
  -- The exponent: `(2 : ENNReal).toReal = 2`.
  have htwo : (2 : ENNReal).toReal = (2 : ℝ) := by norm_num
  rw [htwo]
  -- Pointwise: `‖h t‖ₑ ^ (2:ℝ) = ENNReal.ofReal (‖h t‖²)`.
  have hpt : (fun t => ‖h t‖ₑ ^ (2 : ℝ)) = fun t => ENNReal.ofReal (‖h t‖ ^ 2) := by
    funext t
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast,
      ← ofReal_norm (h t), ← ENNReal.ofReal_pow (norm_nonneg _)]
  rw [hpt]
  -- `∫⁻ ofReal (‖h t‖²) = ofReal (∫ ‖h t‖²)`.
  have hnn : 0 ≤ᵐ[μ] fun t => ‖h t‖ ^ 2 :=
    Filter.Eventually.of_forall fun t => sq_nonneg _
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
  -- `(ofReal I)^(1/2) = ofReal (I^(1/2)) = ofReal (√I)`.
  rw [ENNReal.ofReal_rpow_of_nonneg (integral_nonneg fun t => sq_nonneg _)
      (by norm_num : (0:ℝ) ≤ 1 / 2),
    ← Real.sqrt_eq_rpow]

/-- **Abstract a.e.-`t` norm-lsc transfer (local copy of `Bochner.TimeSobolev`'s
`kineticEnergy_lsc_transfer`).** Inlined here because `AubinLionsLimitPassage` does not import
`Bochner.TimeSobolev` (and adding an import is a `lean-coder`-owned change). Same statement and
proof: from `L²(μ)`-convergence of an a.e.-strongly-measurable sequence `f` to an
a.e.-strongly-measurable limit `g`, with a uniform a.e. pointwise bound `‖f n t‖ ≤ M`, the limit
inherits the bound at `μ`-a.e. `t`.

The isolated measurability pillar `hg : AEStronglyMeasurable g μ` is mandatory (Lane-D
statement-gate fix; without it the statement is FALSE via a Vitali-set counterexample — see the
`Bochner.TimeSobolev` docstring). Route: L²-convergence ⇒ convergence in measure
(`tendstoInMeasure_of_tendsto_eLpNorm`, which itself requires `hg`) ⇒ a.e.-convergent subsequence
(`TendstoInMeasure.exists_seq_tendsto_ae`) ⇒ pass the bound through the a.e. limit. -/
private theorem kineticEnergyLscTransfer {β : Type*} [NormedAddCommGroup β]
    {μ : Measure ℝ} {f : ℕ → ℝ → β} {g : ℝ → β} {M : ℝ}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (hg : AEStronglyMeasurable g μ)
    (hconv : Tendsto (fun n => eLpNorm (fun t => f n t - g t) 2 μ) atTop (𝓝 0))
    (hbound : ∀ n, ∀ᵐ t ∂μ, ‖f n t‖ ≤ M) :
    ∀ᵐ t ∂μ, ‖g t‖ ≤ M := by
  -- L²-convergence ⇒ convergence in measure (uses `hg`), then extract an a.e. subsequence.
  have hconv' : Tendsto (fun n => eLpNorm (f n - g) 2 μ) atTop (𝓝 0) := hconv
  have htim : TendstoInMeasure μ f atTop g :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) hf hg hconv'
  obtain ⟨φ, _hφ, hae⟩ := htim.exists_seq_tendsto_ae
  -- The uniform bound holds for all `n` simultaneously at a.e. `t`.
  have hbound_all : ∀ᵐ t ∂μ, ∀ k, ‖f (φ k) t‖ ≤ M :=
    (ae_all_iff.2 fun k => hbound (φ k))
  -- At a.e. `t`: `‖f (φ k) t‖ → ‖g t‖` and `‖f (φ k) t‖ ≤ M`, so `‖g t‖ ≤ M`.
  filter_upwards [hae, hbound_all] with t htlim htbd
  exact le_of_tendsto' htlim.norm htbd

/-! ### Tier E-prep — ball-restriction plumbing for the a.e.-`t` norm-lsc transfer

These `private` helpers carry the ball-restriction analysis that the E1 transfer needs:
`restrictToBall R` is `1`-Lipschitz (hence continuous, so it transports time-measurability),
its squared norm is the ball set-integral of `‖·‖²`, and that ball set-integral increases to
the full L²(ℝ³) norm-squared as the radius exhausts `ℝ³`. They reuse P3's `restrictToBall`
(`R3.SpatialCompactness`) and the bridge `setIntegral_normSq_eq_dist_sq_restrictToBall`. -/

/-- `restrictToBall R` is `1`-Lipschitz on `L2VF_R3` (local copy: the P3 norm bound is
`private`). Used to obtain continuity, hence time-measurability transport. -/
private theorem restrictToBall_dist_le (R : ℝ) (u v : L2VF_R3) :
    dist (restrictToBall R u) (restrictToBall R v) ≤ dist u v := by
  rw [dist_eq_norm, dist_eq_norm, Lp.norm_def, Lp.norm_def]
  have hle : volume.restrict (Metric.closedBall (0 : Domain3) R) ≤ (volume : Measure Domain3) :=
    Measure.restrict_le_self
  -- The underlying function of `restrictToBall R u - restrictToBall R v` agrees a.e. (on `B_R`)
  -- with `u - v`'s underlying function.
  have hcongR : ⇑(restrictToBall R u - restrictToBall R v)
      =ᵐ[volume.restrict (Metric.closedBall (0 : Domain3) R)]
        (fun x => (u x : EuclideanSpace ℝ (Fin 3)) - (v x : EuclideanSpace ℝ (Fin 3))) := by
    have hsub := Lp.coeFn_sub (restrictToBall R u) (restrictToBall R v)
    have hu : ⇑(restrictToBall R u)
        =ᵐ[volume.restrict (Metric.closedBall (0 : Domain3) R)]
          (u : Domain3 → EuclideanSpace ℝ (Fin 3)) := MemLp.coeFn_toLp _
    have hv : ⇑(restrictToBall R v)
        =ᵐ[volume.restrict (Metric.closedBall (0 : Domain3) R)]
          (v : Domain3 → EuclideanSpace ℝ (Fin 3)) := MemLp.coeFn_toLp _
    filter_upwards [hsub, hu, hv] with x hx hxu hxv
    simp only [hx, Pi.sub_apply, hxu, hxv]
  have hcongG : ⇑(u - v)
      =ᵐ[(volume : Measure Domain3)]
        (fun x => (u x : EuclideanSpace ℝ (Fin 3)) - (v x : EuclideanSpace ℝ (Fin 3))) :=
    Lp.coeFn_sub u v
  rw [eLpNorm_congr_ae hcongR, eLpNorm_congr_ae hcongG]
  refine ENNReal.toReal_mono ?_ (eLpNorm_mono_measure _ hle)
  rw [← eLpNorm_congr_ae hcongG]
  exact (Lp.memLp (u - v)).2.ne

/-- L²-norm-squared as an integral of the pointwise squared norm (local copy; P3's is
`private`). -/
private theorem normSq_eq_integral_normSq' {μ : Measure Domain3}
    (h : Lp (EuclideanSpace ℝ (Fin 3)) 2 μ) :
    ‖h‖ ^ 2 = ∫ x, ‖(h x : EuclideanSpace ℝ (Fin 3))‖ ^ 2 ∂μ := by
  have hre : ‖h‖ ^ 2 = (inner ℝ h h : ℝ) := by
    have := norm_sq_eq_re_inner (𝕜 := ℝ) h
    simpa using this
  rw [hre, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards with x
  exact real_inner_self_eq_norm_sq _

/-- `restrictToBall R` sends `0` to `0`. -/
private theorem restrictToBall_zero (R : ℝ) : restrictToBall R (0 : L2VF_R3) = 0 := by
  apply Lp.ext
  have h1 : ⇑(restrictToBall R (0 : L2VF_R3))
      =ᵐ[volume.restrict (Metric.closedBall (0 : Domain3) R)]
        ((0 : L2VF_R3) : Domain3 → EuclideanSpace ℝ (Fin 3)) := MemLp.coeFn_toLp _
  have h0 : ((0 : L2VF_R3) : Domain3 → EuclideanSpace ℝ (Fin 3))
      =ᵐ[volume.restrict (Metric.closedBall (0 : Domain3) R)] (0 : Domain3 → _) :=
    (Lp.coeFn_zero (E := EuclideanSpace ℝ (Fin 3)) (p := 2) (μ := volume)).restrict
  have hz0 : ⇑(0 : L2ballR3 R)
      =ᵐ[volume.restrict (Metric.closedBall (0 : Domain3) R)] (0 : Domain3 → _) :=
    Lp.coeFn_zero (E := EuclideanSpace ℝ (Fin 3)) (p := 2)
      (μ := volume.restrict (Metric.closedBall (0 : Domain3) R))
  filter_upwards [h1, h0, hz0] with x hx hx0 hxz
  simp only [hx, hx0, hxz, Pi.zero_apply]

/-- Restriction to a ball does not increase the L²-norm (local copy; P3's is `private`). -/
private theorem norm_restrictToBall_le' (R : ℝ) (w : L2VF_R3) :
    ‖restrictToBall R w‖ ≤ ‖w‖ := by
  have := restrictToBall_dist_le R w 0
  rwa [restrictToBall_zero, dist_zero_right, dist_zero_right] at this

/-- Continuity of `restrictToBall R : L2VF_R3 → L2ballR3 R` (it is `1`-Lipschitz). -/
private theorem continuous_restrictToBall (R : ℝ) :
    Continuous (fun w : L2VF_R3 => restrictToBall R w) := by
  refine Metric.continuous_iff.2 fun w ε hε => ⟨ε, hε, fun w' hw' => ?_⟩
  calc dist (restrictToBall R w') (restrictToBall R w)
      ≤ dist w' w := restrictToBall_dist_le R w' w
    _ < ε := hw'

/-- The squared L²(B_R)-norm of `restrictToBall R w` equals the ball set-integral of `‖w·‖²`. -/
private theorem normSq_restrictToBall_eq_setIntegral (R : ℝ) (w : L2VF_R3) :
    ‖restrictToBall R w‖ ^ 2
      = ∫ x in Metric.closedBall (0 : Domain3) R,
          ‖(w x : EuclideanSpace ℝ (Fin 3))‖ ^ 2 ∂(volume : Measure Domain3) := by
  -- Use the bridge with `v = 0`: `restrictToBall R 0 = 0`, so the ball integral of `‖w - 0‖²`
  -- equals `dist (restrictToBall R w) 0 ^ 2 = ‖restrictToBall R w‖²`.
  have hbridge := setIntegral_normSq_eq_dist_sq_restrictToBall R w 0
  rw [restrictToBall_zero, dist_zero_right] at hbridge
  -- Rewrite the integrand: `w x - (0 : L2VF_R3) x = w x` a.e.
  rw [← hbridge]
  refine setIntegral_congr_ae measurableSet_closedBall ?_
  have h0 : ((0 : L2VF_R3) : Domain3 → EuclideanSpace ℝ (Fin 3)) =ᵐ[volume] (0 : Domain3 → _) :=
    Lp.coeFn_zero (E := EuclideanSpace ℝ (Fin 3)) (p := 2) (μ := volume)
  filter_upwards [h0] with x hx _
  rw [hx]; simp

/-- **Ball exhaustion of the L²(ℝ³) norm.** The squared L²(B_k)-norm of `restrictToBall k w`
increases to `‖w‖²` as the integer radius `k → ∞` (the balls exhaust `ℝ³`). -/
private theorem tendsto_normSq_restrictToBall (w : L2VF_R3) :
    Tendsto (fun k : ℕ => ‖restrictToBall (k : ℝ) w‖ ^ 2) atTop (𝓝 (‖w‖ ^ 2)) := by
  -- The integrand `x ↦ ‖w x‖²`.
  set F : Domain3 → ℝ := fun x => ‖(w x : EuclideanSpace ℝ (Fin 3))‖ ^ 2 with hF
  -- Integrability of `F` over `ℝ³`: `‖w‖² = ∫ F`, and `F` is the pointwise square norm of an L²
  -- function, hence integrable (`MemLp.integrable_norm_rpow`-style; here directly via `L2`).
  have hInt : Integrable F (volume : Measure Domain3) := by
    have hmem : MemLp (w : Domain3 → EuclideanSpace ℝ (Fin 3)) 2 volume := Lp.memLp w
    have hr := hmem.integrable_norm_rpow (by norm_num) (by norm_num)
    refine hr.congr ?_
    filter_upwards with x
    simp only [hF, show (2 : ENNReal).toReal = (2 : ℝ) by norm_num, Real.rpow_two]
  -- Each ball term is the set-integral of `F`.
  have hterm : ∀ k : ℕ, ‖restrictToBall (k : ℝ) w‖ ^ 2
      = ∫ x in Metric.closedBall (0 : Domain3) (k : ℝ), F x ∂volume :=
    fun k => normSq_restrictToBall_eq_setIntegral (k : ℝ) w
  -- The full norm is `∫ F`.
  have hfull : ‖w‖ ^ 2 = ∫ x, F x ∂volume := by
    have := normSq_eq_integral_normSq' (μ := (volume : Measure Domain3)) w
    simpa [hF] using this
  -- Monotone ball exhaustion of the set-integral.
  have hcov : (⋃ k : ℕ, Metric.closedBall (0 : Domain3) (k : ℝ)) = Set.univ :=
    Metric.iUnion_closedBall_nat 0
  have hmono : Monotone (fun k : ℕ => Metric.closedBall (0 : Domain3) (k : ℝ)) :=
    fun a b hab => Metric.closedBall_subset_closedBall (by exact_mod_cast hab)
  have hIntOn : IntegrableOn F (⋃ k : ℕ, Metric.closedBall (0 : Domain3) (k : ℝ)) volume := by
    rw [hcov, integrableOn_univ]; exact hInt
  have htends :=
    tendsto_setIntegral_of_monotone
      (fun k => measurableSet_closedBall) hmono hIntOn
  rw [hcov] at htends
  simp only [Measure.restrict_univ] at htends
  rw [hfull]
  simpa only [hterm] using htends

/-- Lower-semicontinuity of the kinetic energy under the (local strong) L² limit, combined
with the uniform Galerkin energy bound, gives `½‖u t‖² ≤ ½‖u₀‖²` at the limit, A.E. IN TIME.

Honesty (no-smuggle, Codex Gate-1): the conclusion is A.E.-in-`t` over `[0,T]`, NOT `∀ t`.
`AubinLionsPackage_R3` supplies LOCAL space-time integral convergence, and (as of #14-C) also
`u_aestronglyMeasurable` (time-measurability of `t ↦ u t`). The measurability field enables
the a.e.-`t` norm-lsc transfer (E1 lean-prover target, #14-P). A `∀ t` bound would still
smuggle the GOOD-REPRESENTATIVE (pointwise-in-time) content — strong time-measurability is NOT
a pointwise representative. The a.e.-in-time bound is the honest derivable form; promoting it
to `∀ t` requires the good-representative frontier (weak-time-continuity / trace), which this
package deliberately does not carry. -/
theorem kineticEnergy_lsc_bound (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν T : ℝ) (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n)
    (alPkg : AubinLionsPackage_R3 𝔊 F ν T u₀ galSeq) :
    ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      (1 / 2 : ℝ) * ‖(alPkg.u t : L2VF_R3)‖ ^ 2 ≤ (1 / 2 : ℝ) * ‖(u₀ : L2VF_R3)‖ ^ 2 := by
  -- PROVABLE CORE (no time-measurability needed): the uniform Galerkin energy bound,
  -- `‖(galSeq n).u t‖ ≤ ‖u₀‖` for every `n` and `t ≥ 0` (`galerkin_norm_le_u0`). This is the
  -- only side of the kinetic-lsc inequality reachable from the data alone.
  have hgal : ∀ (n : ℕ) {t : ℝ}, 0 ≤ t →
      ‖((galSeq n).u t : L2VF_R3)‖ ≤ ‖(u₀ : L2VF_R3)‖ :=
    fun n {t} ht => galerkin_norm_le_u0 𝔊 F ν u₀ n (galSeq n) ht
  -- Degenerate window `T < 0`: `Icc 0 T = ∅`, so the a.e.-statement is vacuous.
  by_cases hT : 0 ≤ T
  · -- The time measure `μ = volume.restrict (Icc 0 T)` is finite (`Icc 0 T` bounded).
    set μ : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) T) with hμ
    haveI hμfin : IsFiniteMeasure μ := by
      rw [hμ]; refine isFiniteMeasure_restrict.2 ?_
      rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
    -- a.e. `t ∈ Icc 0 T`, in particular `0 ≤ t`.
    have hμ_ge : ∀ᵐ t ∂μ, 0 ≤ t := by
      rw [hμ]; refine ae_restrict_of_forall_mem measurableSet_Icc ?_; intro t ht; exact ht.1
    -- ════ For each integer radius `k`: the limit's ball restriction is L²-bounded by ‖u₀‖. ════
    -- This is the `kineticEnergyLscTransfer` (norm-lsc) step, applied in `β = L2ballR3 k`, with
    --   f n := t ↦ restrictToBall k ((galSeq (alPkg.φ n)).u t),   g := t ↦ restrictToBall k (u t).
    have hperBall : ∀ k : ℕ,
        ∀ᵐ t ∂μ, ‖restrictToBall (k : ℝ) (alPkg.u t)‖ ≤ ‖(u₀ : L2VF_R3)‖ := by
      intro k
      set R : ℝ := (k : ℝ) with hR
      set f : ℕ → ℝ → L2ballR3 R :=
        fun n t => restrictToBall R ((galSeq (alPkg.φ n)).u t) with hf
      set g : ℝ → L2ballR3 R := fun t => restrictToBall R (alPkg.u t) with hg
      -- (1) `g` is a.e.-strongly measurable: `restrictToBall R` continuous ∘ `u` measurable.
      have hg_meas : AEStronglyMeasurable g μ := by
        simp only [hg]
        exact (continuous_restrictToBall R).comp_aestronglyMeasurable
          (by rw [hμ]; exact alPkg.u_aestronglyMeasurable)
      -- (2) each `f n` is a.e.-strongly measurable: galerkin curve continuous on `Ici 0 ⊇ Icc 0 T`.
      have hf_meas : ∀ n, AEStronglyMeasurable (f n) μ := by
        intro n
        have hcurve : ContinuousOn
            (fun t => ((galSeq (alPkg.φ n)).u t : L2VF_R3)) (Set.Icc (0 : ℝ) T) :=
          (galerkin_curve_continuous 𝔊 F ν u₀ (alPkg.φ n) (galSeq (alPkg.φ n))).mono
            (by intro t ht; exact ht.1)
        have hcurve_meas : AEStronglyMeasurable
            (fun t => ((galSeq (alPkg.φ n)).u t : L2VF_R3)) μ := by
          rw [hμ]; exact hcurve.aestronglyMeasurable measurableSet_Icc
        simp only [hf]
        exact (continuous_restrictToBall R).comp_aestronglyMeasurable hcurve_meas
      -- (3) the uniform a.e. bound `‖f n t‖ ≤ ‖u₀‖` (restriction ≤ global, then `hgal`).
      have hf_bound : ∀ n, ∀ᵐ t ∂μ, ‖f n t‖ ≤ ‖(u₀ : L2VF_R3)‖ := by
        intro n
        filter_upwards [hμ_ge] with t ht
        simp only [hf]
        calc ‖restrictToBall R ((galSeq (alPkg.φ n)).u t)‖
            ≤ ‖((galSeq (alPkg.φ n)).u t : L2VF_R3)‖ :=
              norm_restrictToBall_le' R ((galSeq (alPkg.φ n)).u t)
          _ ≤ ‖(u₀ : L2VF_R3)‖ := hgal (alPkg.φ n) ht
      -- (4) the L²-in-time convergence `eLpNorm (f n - g) 2 μ → 0`. With `strong_convergence` now
      -- in its faithful `eLpNorm`-form (issue #31), this is EXACTLY the package field at radius
      -- `R = k`: `f n t = restrictToBall R ((galSeq (alPkg.φ n)).u t)` and
      -- `g t = restrictToBall R (alPkg.u t)`, and `μ = volume.restrict (Icc 0 T)`, so the field's
      -- conclusion is definitionally `hconv`.  This DISCHARGES the former `MemLp g`-gap `sorry`
      -- (the Bochner-form residual): the faithful field supplies the time-`L²` convergence directly,
      -- no time-integrability of a junk-`0`-collapsible integrand is needed.
      have hconv : Tendsto (fun n => eLpNorm (fun t => f n t - g t) 2 μ) atTop (𝓝 0) := by
        simpa only [hf, hg, hμ, hR] using alPkg.strong_convergence R
      -- (5) assemble: `kineticEnergyLscTransfer` gives the a.e. ball-restricted bound.
      exact kineticEnergyLscTransfer hf_meas hg_meas hconv hf_bound
    -- ════ Combine over all radii `k`, then exhaust `R → ∞` to recover the full L²(ℝ³) bound. ════
    have hallBall : ∀ᵐ t ∂μ, ∀ k : ℕ,
        ‖restrictToBall (k : ℝ) (alPkg.u t)‖ ≤ ‖(u₀ : L2VF_R3)‖ :=
      ae_all_iff.2 hperBall
    filter_upwards [hallBall] with t ht
    -- `‖u t‖² = lim_k ‖restrictToBall k (u t)‖² ≤ ‖u₀‖²`, hence the kinetic bound.
    have hlim := tendsto_normSq_restrictToBall (alPkg.u t)
    have hboundSq : ∀ k : ℕ, ‖restrictToBall (k : ℝ) (alPkg.u t)‖ ^ 2 ≤ ‖(u₀ : L2VF_R3)‖ ^ 2 :=
      fun k => by
        have := ht k
        nlinarith [norm_nonneg (restrictToBall (k : ℝ) (alPkg.u t)), norm_nonneg (u₀ : L2VF_R3)]
    have huSq : ‖(alPkg.u t : L2VF_R3)‖ ^ 2 ≤ ‖(u₀ : L2VF_R3)‖ ^ 2 :=
      le_of_tendsto' hlim hboundSq
    nlinarith [huSq]
  · -- `T < 0`: the restricted measure is zero, so every a.e. statement holds.
    have hz : volume.restrict (Set.Icc (0 : ℝ) T) = 0 := by
      rw [Set.Icc_eq_empty hT, Measure.restrict_empty]
    rw [hz]
    simp

/-! ### Tier E (viscous half) — weak lower-semicontinuity of the dissipation -/

/-- The viscous-form curve `s ↦ viscousFormSq_R3 1 (gs.u s)` is continuous on `Ici 0`
(`= ∑_j ‖weightedFourierComponent (u s) j‖²`, a sum of norm² of the continuous weighted-Fourier
curves — the `viscous_curve_continuous` field). -/
private theorem viscousFormSq_curve_continuousOn (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (u₀ : L2Sigma_R3) (n : ℕ) (gs : GalerkinSolutionData_R3 𝔊 F ν u₀ n) :
    ContinuousOn (fun s => viscousFormSq_R3 1 (gs.u s : L2VF_R3)) (Set.Ici (0 : ℝ)) := by
  have heq : ∀ s, viscousFormSq_R3 1 (gs.u s : L2VF_R3)
      = ∑ j : Fin 3, ‖weightedFourierComponent (gs.u s : L2VF_R3) (gs.reg_mem s) j‖ ^ 2 := by
    intro s
    rw [FourierL2.viscousFormSq_R3_eq_integral_normSq_fourier]
    exact Finset.sum_congr rfl
      (fun j _ => (norm_weightedFourierComponent_sq (gs.u s : L2VF_R3) (gs.reg_mem s) j).symm)
  refine ContinuousOn.congr ?_ (fun s _ => heq s)
  exact continuousOn_finsetSum _ (fun j _ => ((gs.viscous_curve_continuous j).norm.pow 2))

/-! ### Tier E (viscous half) — Fourier–Plancherel weak-L² lsc machinery (issue #C-route)

The pointwise viscous lsc wall is discharged via the **Fourier–Plancherel** route, entirely inside
`L²` (a bundled Hilbert space here), avoiding any H¹ Hilbert type, sequential Banach–Alaoglu, or
convex-functional weak-lsc.  The chain: full-sequence weak-L² convergence `uₙ(t) ⇀ u(t)` a.e. `t`
(from `strong_convergence_ae` + the ball-tail ε/3 argument) ⟹ push through the bounded truncated
Fourier multiplier (a CLM) ⟹ norm-weak-lsc of the L²-norm (inner-product trick) ⟹ MCT in the
truncation level recovers the full Dirichlet seminorm. -/

/-- **Norm lower-semicontinuity from a single inner-product convergence.** On a real
inner-product space, if `‖gₙ‖ ≤ M` and `⟪g, gₙ⟫ → ‖g‖²`, then `‖g‖ ≤ liminf ‖gₙ‖`.

This is the inner-product-trick form of weak-lsc of the norm: `‖g‖² = lim ⟪g, gₙ⟫ ≤ ‖g‖ · liminf ‖gₙ‖`
(Cauchy–Schwarz + `Monotone.map_liminf_of_continuousAt` to commute the nonneg scalar `‖g‖` with
`liminf`), then divide by `‖g‖`.  No Mazur, no subsequence extraction. -/
theorem norm_le_liminf_of_inner_tendsto {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (g : E) (gn : ℕ → E) (M : ℝ) (hM : ∀ n, ‖gn n‖ ≤ M)
    (hinner : Tendsto (fun n => @inner ℝ E _ g (gn n)) atTop (nhds (‖g‖ ^ 2))) :
    ‖g‖ ≤ Filter.liminf (fun n => ‖gn n‖) atTop := by
  have hbddAbove : Filter.IsBoundedUnder (· ≤ ·) atTop (fun n => ‖gn n‖) :=
    Filter.isBoundedUnder_of_eventually_le (a := M) (Filter.Eventually.of_forall hM)
  have hbddBelow : Filter.IsBoundedUnder (· ≥ ·) atTop (fun n => ‖gn n‖) :=
    Filter.isBoundedUnder_of_eventually_ge (a := 0)
      (Filter.Eventually.of_forall (fun n => norm_nonneg _))
  have hcobdd : Filter.IsCoboundedUnder (· ≥ ·) atTop (fun n => ‖gn n‖) :=
    hbddAbove.isCoboundedUnder_ge
  by_cases hg0 : g = 0
  · rw [hg0, norm_zero]
    exact Filter.le_liminf_of_le hcobdd (Filter.Eventually.of_forall (fun n => norm_nonneg _))
  have hgpos : (0:ℝ) < ‖g‖ := norm_pos_iff.mpr hg0
  have hlim_eq : Filter.liminf (fun n => @inner ℝ E _ g (gn n)) atTop = ‖g‖ ^ 2 :=
    hinner.liminf_eq
  have hconst : (‖g‖ * Filter.liminf (fun n => ‖gn n‖) atTop)
      = Filter.liminf (fun n => ‖g‖ * ‖gn n‖) atTop := by
    have hmono : Monotone (fun x : ℝ => ‖g‖ * x) := fun a b hab =>
      mul_le_mul_of_nonneg_left hab (norm_nonneg _)
    exact hmono.map_liminf_of_continuousAt (fun n => ‖gn n‖)
      (Continuous.continuousAt (by continuity)) hcobdd hbddBelow
  have hbddAbove2 : Filter.IsBoundedUnder (· ≤ ·) atTop (fun n => ‖g‖ * ‖gn n‖) :=
    Filter.isBoundedUnder_of_eventually_le (a := ‖g‖ * M)
      (Filter.Eventually.of_forall (fun n => mul_le_mul_of_nonneg_left (hM n) (norm_nonneg _)))
  have hbddBelow_inner : Filter.IsBoundedUnder (· ≥ ·) atTop (fun n => @inner ℝ E _ g (gn n)) :=
    hinner.isBoundedUnder_ge
  have hmono2 : Filter.liminf (fun n => @inner ℝ E _ g (gn n)) atTop
      ≤ Filter.liminf (fun n => ‖g‖ * ‖gn n‖) atTop :=
    Filter.liminf_le_liminf (Filter.Eventually.of_forall (fun n => real_inner_le_norm g (gn n)))
      hbddBelow_inner hbddAbove2.isCoboundedUnder_ge
  rw [hlim_eq, ← hconst, pow_two] at hmono2
  exact le_of_mul_le_mul_left hmono2 hgpos

/-- **Norm weak-lsc (`toWeakSpace` form).** If `gₙ ⇀ g` weakly in `WeakSpace ℝ E` and `‖gₙ‖ ≤ M`,
then `‖g‖ ≤ liminf ‖gₙ‖`.  (Extract the inner-product convergence `⟪g, gₙ⟫ → ‖g‖²` from the weak
limit — eval against the Riesz dual of `g` — then apply `norm_le_liminf_of_inner_tendsto`.) -/
private theorem norm_le_liminf_of_weak {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (g : E) (gn : ℕ → E) (M : ℝ) (hM : ∀ n, ‖gn n‖ ≤ M)
    (hw : Tendsto (fun n => toWeakSpace ℝ E (gn n)) atTop (nhds (toWeakSpace ℝ E g))) :
    ‖g‖ ≤ Filter.liminf (fun n => ‖gn n‖) atTop := by
  have hBinj : Function.Injective ((topDualPairing ℝ E).flip) :=
    separatingDual_iff_injective.mp inferInstance
  have hev := (WeakBilin.tendsto_iff_forall_eval_tendsto
    (B := (topDualPairing ℝ E).flip) hBinj).mp hw ((InnerProductSpace.toDual ℝ E) g)
  have hinner : Tendsto (fun n => @inner ℝ E _ g (gn n)) atTop (nhds (@inner ℝ E _ g g)) := hev
  rw [real_inner_self_eq_norm_sq] at hinner
  exact norm_le_liminf_of_inner_tendsto g gn M hM hinner

/-- **Squared-norm weak-lsc (`toWeakSpace` form).** From `gₙ ⇀ g` and `‖gₙ‖ ≤ M`,
`‖g‖² ≤ liminf ‖gₙ‖²`.  Squaring `‖g‖ ≤ liminf ‖gₙ‖` via the continuous monotone `Real.sqrt`
(`‖gₙ‖ = √(‖gₙ‖²)`, so `liminf ‖gₙ‖ = √(liminf ‖gₙ‖²)`). -/
private theorem normSq_le_liminf_of_weak {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (g : E) (gn : ℕ → E) (M : ℝ) (hM : ∀ n, ‖gn n‖ ≤ M)
    (hw : Tendsto (fun n => toWeakSpace ℝ E (gn n)) atTop (nhds (toWeakSpace ℝ E g))) :
    ‖g‖ ^ 2 ≤ Filter.liminf (fun n => ‖gn n‖ ^ 2) atTop := by
  have hnorm := norm_le_liminf_of_weak g gn M hM hw
  have hbddAbove2 : Filter.IsBoundedUnder (· ≤ ·) atTop (fun n => ‖gn n‖ ^ 2) :=
    Filter.isBoundedUnder_of_eventually_le (a := M ^ 2)
      (Filter.Eventually.of_forall (fun n =>
        pow_le_pow_left₀ (norm_nonneg _) (hM n) 2))
  have hbddBelow2 : Filter.IsBoundedUnder (· ≥ ·) atTop (fun n => ‖gn n‖ ^ 2) :=
    Filter.isBoundedUnder_of_eventually_ge (a := 0)
      (Filter.Eventually.of_forall (fun n => by positivity))
  -- `liminf ‖gₙ‖ = √(liminf ‖gₙ‖²)`: `Real.sqrt` is monotone-continuous and `‖gₙ‖ = √(‖gₙ‖²)`.
  have hsqrt_eq : Filter.liminf (fun n => ‖gn n‖) atTop
      = Real.sqrt (Filter.liminf (fun n => ‖gn n‖ ^ 2) atTop) := by
    have hmonoSqrt : Monotone Real.sqrt := fun a b h => Real.sqrt_le_sqrt h
    have hmap := hmonoSqrt.map_liminf_of_continuousAt (fun n => ‖gn n‖ ^ 2)
      (Real.continuous_sqrt.continuousAt) hbddAbove2.isCoboundedUnder_ge hbddBelow2
    rw [hmap]
    apply Filter.liminf_congr
    exact Filter.Eventually.of_forall (fun n => by
      rw [Function.comp_apply, Real.sqrt_sq (norm_nonneg _)])
  rw [hsqrt_eq] at hnorm
  have hL_nonneg : 0 ≤ Filter.liminf (fun n => ‖gn n‖ ^ 2) atTop :=
    Filter.le_liminf_of_le hbddAbove2.isCoboundedUnder_ge
      (Filter.Eventually.of_forall (fun n => by positivity))
  calc ‖g‖ ^ 2 ≤ (Real.sqrt (Filter.liminf (fun n => ‖gn n‖ ^ 2) atTop)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ = Filter.liminf (fun n => ‖gn n‖ ^ 2) atTop := Real.sq_sqrt hL_nonneg

/-- **An ℝ-CLM pushes weak convergence.** If `gₙ ⇀ g` in `WeakSpace ℝ E`, then `S gₙ ⇀ S g` in
`WeakSpace ℝ F`, for any `S : E →L[ℝ] F`.  (Each dual `L` of `F` pulls back to the dual `L ∘L S`
of `E`, against which the source weak convergence holds.) -/
private theorem clm_pushes_weak {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (S : E →L[ℝ] F) {gn : ℕ → E} {g : E}
    (hw : Tendsto (fun n => toWeakSpace ℝ E (gn n)) atTop (nhds (toWeakSpace ℝ E g))) :
    Tendsto (fun n => toWeakSpace ℝ F (S (gn n))) atTop (nhds (toWeakSpace ℝ F (S g))) := by
  have hBinjE : Function.Injective ((topDualPairing ℝ E).flip) :=
    separatingDual_iff_injective.mp inferInstance
  have hBinjF : Function.Injective ((topDualPairing ℝ F).flip) :=
    separatingDual_iff_injective.mp inferInstance
  refine (WeakBilin.tendsto_iff_forall_eval_tendsto
    (B := (topDualPairing ℝ F).flip) hBinjF).mpr ?_
  intro L
  exact (WeakBilin.tendsto_iff_forall_eval_tendsto
    (B := (topDualPairing ℝ E).flip) hBinjE).mp hw (L ∘L S)

/-- The bounded Fourier-component CLM `𝓕 ∘ projⱼ : L²VF → L²C` (as an ℝ-CLM). -/
private noncomputable def fourierProjCLM (j : Fin 3) : L2VF_R3 →L[ℝ] L2C_R3 :=
  (((Lp.fourierTransformₗᵢ Domain3 ℂ).toLinearIsometry.toContinuousLinearMap).restrictScalars ℝ)
    ∘L L2VF_projComponentC_R3 j

private theorem fourierProjCLM_apply (j : Fin 3) (u : L2VF_R3) :
    fourierProjCLM j u = (𝓕 (L2VF_projComponentC_R3 j u) : L2C_R3) := rfl

/-- The bounded truncated-weight multiplier `mulBdd m` (for `|m| ≤ C`) as an ℝ-CLM on `L²C`. -/
private noncomputable def mulBddCLM (m : Domain3 → ℝ)
    (hmem : MemLp (fun ξ : Domain3 => (m ξ : ℂ)) ⊤ (volume : Measure Domain3))
    {C : ℝ} (hC : 0 ≤ C) (hmle : ∀ ξ, |m ξ| ≤ C) : L2C_R3 →L[ℝ] L2C_R3 where
  toFun := fun g => mulBdd m hmem g
  map_add' := mulBdd_add m hmem
  map_smul' := by intro r g; simpa using mulBdd_smul m hmem r g
  cont := continuous_mulBdd m hmem hC hmle

private theorem mulBddCLM_apply (m : Domain3 → ℝ)
    (hmem : MemLp (fun ξ : Domain3 => (m ξ : ℂ)) ⊤ (volume : Measure Domain3))
    {C : ℝ} (hC : 0 ≤ C) (hmle : ∀ ξ, |m ξ| ≤ C) (g : L2C_R3) :
    mulBddCLM m hmem hC hmle g = mulBdd m hmem g := rfl

/-! #### Ball-tail decomposition of the L²VF inner product (local copies; P3's are `private`) -/

/-- Restriction of an L²(ℝ³) field to the tail `B_Rᶜ`, as an `L²` element (local copy). -/
private noncomputable def tailVF' (R : ℝ) (w : L2VF_R3) :
    Lp (EuclideanSpace ℝ (Fin 3)) 2 (volume.restrict (Metric.closedBall (0 : Domain3) R)ᶜ) :=
  MemLp.toLp (w : Domain3 → EuclideanSpace ℝ (Fin 3))
    ((Lp.memLp w).restrict (Metric.closedBall (0 : Domain3) R)ᶜ)

private theorem norm_tailVF'_le (R : ℝ) (w : L2VF_R3) : ‖tailVF' R w‖ ≤ ‖w‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  have hcong : ⇑(tailVF' R w)
      =ᵐ[volume.restrict (Metric.closedBall (0 : Domain3) R)ᶜ]
        (w : Domain3 → EuclideanSpace ℝ (Fin 3)) := MemLp.coeFn_toLp _
  rw [eLpNorm_congr_ae hcong]
  exact ENNReal.toReal_mono (Lp.memLp w).2.ne (eLpNorm_mono_measure _ Measure.restrict_le_self)

/-- Ball/tail split of the real inner product: `⟪v,w⟫ = ⟪ball v, ball w⟫ + ⟪tail v, tail w⟫`. -/
private theorem inner_eq_ball_add_tail' (R : ℝ) (v w : L2VF_R3) :
    (inner ℝ v w : ℝ)
      = (inner ℝ (restrictToBall R v) (restrictToBall R w) : ℝ)
        + (inner ℝ (tailVF' R v) (tailVF' R w) : ℝ) := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  have hball : (∫ x, (inner ℝ ((restrictToBall R v) x) ((restrictToBall R w) x) : ℝ)
        ∂(volume.restrict (Metric.closedBall (0 : Domain3) R)))
      = ∫ x in Metric.closedBall (0 : Domain3) R,
          (inner ℝ (v x : EuclideanSpace ℝ (Fin 3)) (w x : EuclideanSpace ℝ (Fin 3)) : ℝ)
          ∂volume := by
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp (μ := volume.restrict (Metric.closedBall (0 : Domain3) R))
        ((Lp.memLp v).restrict (Metric.closedBall (0 : Domain3) R)),
      MemLp.coeFn_toLp (μ := volume.restrict (Metric.closedBall (0 : Domain3) R))
        ((Lp.memLp w).restrict (Metric.closedBall (0 : Domain3) R))] with x hxv hxw
    show (inner ℝ ((restrictToBall R v) x) ((restrictToBall R w) x) : ℝ) = _
    rw [show ((restrictToBall R v) x) = (v x : EuclideanSpace ℝ (Fin 3)) from hxv,
      show ((restrictToBall R w) x) = (w x : EuclideanSpace ℝ (Fin 3)) from hxw]
  have htail : (∫ x, (inner ℝ ((tailVF' R v) x) ((tailVF' R w) x) : ℝ)
        ∂(volume.restrict (Metric.closedBall (0 : Domain3) R)ᶜ))
      = ∫ x in (Metric.closedBall (0 : Domain3) R)ᶜ,
          (inner ℝ (v x : EuclideanSpace ℝ (Fin 3)) (w x : EuclideanSpace ℝ (Fin 3)) : ℝ)
          ∂volume := by
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp (μ := volume.restrict (Metric.closedBall (0 : Domain3) R)ᶜ)
        ((Lp.memLp v).restrict (Metric.closedBall (0 : Domain3) R)ᶜ),
      MemLp.coeFn_toLp (μ := volume.restrict (Metric.closedBall (0 : Domain3) R)ᶜ)
        ((Lp.memLp w).restrict (Metric.closedBall (0 : Domain3) R)ᶜ)] with x hxv hxw
    show (inner ℝ ((tailVF' R v) x) ((tailVF' R w) x) : ℝ) = _
    rw [show ((tailVF' R v) x) = (v x : EuclideanSpace ℝ (Fin 3)) from hxv,
      show ((tailVF' R w) x) = (w x : EuclideanSpace ℝ (Fin 3)) from hxw]
  rw [hball, htail]
  exact (integral_add_compl measurableSet_closedBall
    (MeasureTheory.L2.integrable_inner (𝕜 := ℝ) v w)).symm

private theorem abs_tail_inner_le' (R : ℝ) (v w : L2VF_R3) :
    |(inner ℝ (tailVF' R v) (tailVF' R w) : ℝ)| ≤ ‖tailVF' R v‖ * ‖w‖ :=
  le_trans (abs_real_inner_le_norm _ _)
    (mul_le_mul_of_nonneg_left (norm_tailVF'_le R w) (norm_nonneg _))

/-- **Tail-vanishing** of a fixed L²VF field: `‖tailVF' k v‖ → 0` as `k → ∞` (ball exhaustion). -/
private theorem tendsto_norm_tailVF'_zero (v : L2VF_R3) :
    Tendsto (fun k : ℕ => ‖tailVF' (k : ℝ) v‖) atTop (nhds 0) := by
  -- `‖tailVF' k v‖² = ‖v‖² − ‖restrictToBall k v‖²` (Pythagoras), and the ball term → `‖v‖²`.
  have hsq : ∀ k : ℕ, ‖tailVF' (k : ℝ) v‖ ^ 2 = ‖v‖ ^ 2 - ‖restrictToBall (k : ℝ) v‖ ^ 2 := by
    intro k
    have hsplit := inner_eq_ball_add_tail' (k : ℝ) v v
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
      real_inner_self_eq_norm_sq] at hsplit
    linarith [hsplit]
  have hball := tendsto_normSq_restrictToBall v
  have htsq : Tendsto (fun k : ℕ => ‖tailVF' (k : ℝ) v‖ ^ 2) atTop (nhds 0) := by
    have h0 : Tendsto (fun k : ℕ => ‖v‖ ^ 2 - ‖restrictToBall (k : ℝ) v‖ ^ 2) atTop
        (nhds (‖v‖ ^ 2 - ‖v‖ ^ 2)) := tendsto_const_nhds.sub hball
    rw [sub_self] at h0
    exact h0.congr (fun k => (hsq k).symm)
  have := htsq.sqrt
  simp only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] at this
  exact this

/-- **Fixed-test-vector weak convergence at a.e. `t`.** From per-ball a.e.-`t` convergence
`restrictToBall R (uₙ t) → restrictToBall R (u t)` (all `R`) plus the uniform `L²` bounds
`‖uₙ t‖ ≤ M`, `‖u t‖ ≤ M`, the inner products against any fixed `e` converge:
`⟪e, uₙ t⟫ → ⟪e, u t⟫`.  Ball/tail ε/3 split: the ball part converges (`restrictToBall` strong),
the tails are bounded by `‖tail e‖ · M → 0`. -/
theorem inner_tendsto_of_perball
    (e : L2VF_R3) (un : ℕ → L2VF_R3) (u : L2VF_R3) (M : ℝ) (hM0 : 0 ≤ M)
    (hbd : ∀ n, ‖un n‖ ≤ M) (hbu : ‖u‖ ≤ M)
    (hperball : ∀ k : ℕ, Tendsto (fun n => restrictToBall (k : ℝ) (un n)) atTop
      (nhds (restrictToBall (k : ℝ) u))) :
    Tendsto (fun n => (inner ℝ e (un n) : ℝ)) atTop (nhds (inner ℝ e u : ℝ)) := by
  refine Metric.tendsto_atTop.2 (fun ε hε => ?_)
  set C : ℝ := M + ‖e‖ + 1 with hC
  have hCpos : 0 < C := by positivity
  obtain ⟨k0, hk0⟩ := (Metric.tendsto_atTop.1 (tendsto_norm_tailVF'_zero e)) (ε / (3 * C))
    (by positivity)
  have htk : ‖tailVF' (k0 : ℝ) e‖ < ε / (3 * C) := by
    have := hk0 k0 le_rfl; rwa [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at this
  have htk_nonneg : 0 ≤ ‖tailVF' (k0 : ℝ) e‖ := norm_nonneg _
  have hballconv : Tendsto
      (fun n => (inner ℝ (restrictToBall (k0:ℝ) e) (restrictToBall (k0:ℝ) (un n)) : ℝ))
      atTop (nhds (inner ℝ (restrictToBall (k0:ℝ) e) (restrictToBall (k0:ℝ) u) : ℝ)) :=
    (tendsto_const_nhds).inner (hperball k0)
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hballconv) (ε / 3) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq, inner_eq_ball_add_tail' (k0:ℝ) e (un n), inner_eq_ball_add_tail' (k0:ℝ) e u]
  have hbM : ‖tailVF' (k0:ℝ) e‖ * M < ε / 3 := by
    calc ‖tailVF' (k0:ℝ) e‖ * M ≤ ‖tailVF' (k0:ℝ) e‖ * C := by
            apply mul_le_mul_of_nonneg_left _ htk_nonneg; rw [hC]; linarith [norm_nonneg e]
      _ < (ε / (3 * C)) * C := mul_lt_mul_of_pos_right htk hCpos
      _ = ε / 3 := by field_simp
  have htn := lt_of_le_of_lt (le_trans (abs_tail_inner_le' (k0:ℝ) e (un n))
    (mul_le_mul_of_nonneg_left (hbd n) htk_nonneg)) hbM
  have htu := lt_of_le_of_lt (le_trans (abs_tail_inner_le' (k0:ℝ) e u)
    (mul_le_mul_of_nonneg_left hbu htk_nonneg)) hbM
  have hballn := hN n hn; rw [Real.dist_eq] at hballn
  set B1 := (inner ℝ (restrictToBall (k0:ℝ) e) (restrictToBall (k0:ℝ) (un n)) : ℝ)
  set T1 := (inner ℝ (tailVF' (k0:ℝ) e) (tailVF' (k0:ℝ) (un n)) : ℝ)
  set B2 := (inner ℝ (restrictToBall (k0:ℝ) e) (restrictToBall (k0:ℝ) u) : ℝ)
  set T2 := (inner ℝ (tailVF' (k0:ℝ) e) (tailVF' (k0:ℝ) u) : ℝ)
  rw [abs_lt] at hballn ⊢
  rw [abs_lt] at htn htu
  constructor <;> linarith [hballn.1, hballn.2, htn.1, htn.2, htu.1, htu.2]

/-- **Fixed-test-vector convergence ⟹ weak convergence** in `WeakSpace ℝ L2VF_R3`.  If
`⟪e, uₙ⟫ → ⟪e, u⟫` for every `e` (Riesz: every dual), then `uₙ ⇀ u`. -/
theorem weak_tendsto_of_inner_tendsto
    (un : ℕ → L2VF_R3) (u : L2VF_R3)
    (hfix : ∀ e : L2VF_R3,
      Tendsto (fun n => (inner ℝ e (un n) : ℝ)) atTop (nhds (inner ℝ e u : ℝ))) :
    Tendsto (fun n => toWeakSpace ℝ L2VF_R3 (un n)) atTop (nhds (toWeakSpace ℝ L2VF_R3 u)) := by
  have hBinj : Function.Injective ((topDualPairing ℝ L2VF_R3).flip) :=
    separatingDual_iff_injective.mp inferInstance
  refine (WeakBilin.tendsto_iff_forall_eval_tendsto
    (B := (topDualPairing ℝ L2VF_R3).flip) hBinj).mpr ?_
  intro L
  set e := (InnerProductSpace.toDual ℝ L2VF_R3).symm L with he
  have hL : ∀ x : L2VF_R3, L x = @inner ℝ L2VF_R3 _ e x :=
    fun x => (InnerProductSpace.toDual_symm_apply).symm
  have : Tendsto (fun n => L (un n)) atTop (nhds (L u)) := by
    simp only [hL]; exact hfix e
  exact this

/-- The `j`-th viscous spectral integrand `∫ (2π)²‖ξ‖² ‖𝓕(projⱼ w)‖²` (the `j`-summand of
`viscousFormSq_R3 1 w`). -/
private noncomputable def viscousIntegrand_j (j : Fin 3) (w : L2VF_R3) : ℝ :=
  ∫ ξ : Domain3, (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 *
    ‖(𝓕 (L2VF_projComponentC_R3 j w) : L2C_R3) ξ‖ ^ 2 ∂(volume : Measure Domain3)

private theorem viscousIntegrand_j_nonneg (j : Fin 3) (w : L2VF_R3) :
    0 ≤ viscousIntegrand_j j w :=
  integral_nonneg (fun ξ => by positivity)

private theorem viscousFormSq_eq_sum_integrand (w : L2VF_R3) :
    viscousFormSq_R3 1 w = ∑ j : Fin 3, viscousIntegrand_j j w :=
  FourierL2.viscousFormSq_R3_eq_integral_normSq_fourier w

/-- The `j`-th viscous integrand as a lower Lebesgue integral (ENNReal), which carries the
spectral seminorm with NO integrability/`H¹` precondition (the junk-`0` of the Bochner form
is avoided): `viscousLintegrand_j j w = ∫⁻ ofReal ((2π)²‖ξ‖² ‖𝓕(projⱼ w)‖²)`. -/
private noncomputable def viscousLintegrand_j (j : Fin 3) (w : L2VF_R3) : ENNReal :=
  ∫⁻ ξ : Domain3, ENNReal.ofReal ((2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 *
    ‖(𝓕 (L2VF_projComponentC_R3 j w) : L2C_R3) ξ‖ ^ 2) ∂(volume : Measure Domain3)

/-- `ofReal (∫ f) ≤ ∫⁻ ofReal f` for the (nonneg) viscous integrand — no integrability needed
(if non-integrable the Bochner integral is `0`). -/
private theorem ofReal_viscousIntegrand_le_lintegrand (j : Fin 3) (w : L2VF_R3) :
    ENNReal.ofReal (viscousIntegrand_j j w) ≤ viscousLintegrand_j j w := by
  rw [viscousIntegrand_j, viscousLintegrand_j]
  by_cases hint : Integrable (fun ξ : Domain3 => (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 *
      ‖(𝓕 (L2VF_projComponentC_R3 j w) : L2C_R3) ξ‖ ^ 2) volume
  · rw [ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall (fun ξ => by positivity))]
  · rw [integral_undef hint, ENNReal.ofReal_zero]; exact bot_le

/-- Two-term superadditivity of `liminf` in `ENNReal`: `liminf u + liminf v ≤ liminf (u+v)`.
Proved via the `⨆ n, ⨅ i, ·(i+n)` form (`liminf_eq_iSup_iInf_of_nat'`) and ENNReal's
`add_iInf`/`iInf_add` + `iSup` monotonicity; avoids the absent `le_liminf_add` import. -/
private theorem add_liminf_le_liminf_add (u v : ℕ → ENNReal) :
    Filter.atTop.liminf u + Filter.atTop.liminf v ≤ Filter.atTop.liminf (fun n => u n + v n) := by
  rw [Filter.liminf_eq_iSup_iInf_of_nat', Filter.liminf_eq_iSup_iInf_of_nat',
    Filter.liminf_eq_iSup_iInf_of_nat']
  -- `(⨆n ⨅i u(i+n)) + (⨆n ⨅i v(i+n)) ≤ ⨆n ⨅i (u(i+n)+v(i+n))`.
  -- The iInf-tails are monotone in `n`, so for any `n₁,n₂` use `n := max n₁ n₂`.
  refine ENNReal.iSup_add_iSup_le (fun n₁ n₂ => ?_)
  refine le_iSup_of_le (max n₁ n₂) ?_
  refine le_iInf (fun i => ?_)
  -- `(⨅i u(i+n₁)) + (⨅i v(i+n₂)) ≤ u(i+max) + v(i+max)`, then `≤ ⨅i (u+v)(i+max)`.
  have hu : (⨅ k : ℕ, u (k + n₁)) ≤ u (i + max n₁ n₂) := by
    refine le_trans (iInf_le _ (i + (max n₁ n₂ - n₁))) (le_of_eq ?_)
    congr 1; omega
  have hv : (⨅ k : ℕ, v (k + n₂)) ≤ v (i + max n₁ n₂) := by
    refine le_trans (iInf_le _ (i + (max n₁ n₂ - n₂))) (le_of_eq ?_)
    congr 1; omega
  exact add_le_add hu hv

/-- Superadditivity of `liminf` over a `Finset` (in `ENNReal`): `∑ liminf ≤ liminf ∑`. -/
private theorem sum_liminf_le_liminf_sum {α : Type*} (s : Finset α) (f : α → ℕ → ENNReal) :
    (∑ a ∈ s, Filter.atTop.liminf (fun n => f a n))
      ≤ Filter.atTop.liminf (fun n => ∑ a ∈ s, f a n) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    calc Filter.atTop.liminf (fun n => f a n) + ∑ x ∈ s, Filter.atTop.liminf (fun n => f x n)
        ≤ Filter.atTop.liminf (fun n => f a n) + Filter.atTop.liminf (fun n => ∑ x ∈ s, f x n) := by
          gcongr
      _ ≤ Filter.atTop.liminf (fun n => f a n + ∑ x ∈ s, f x n) :=
          add_liminf_le_liminf_add _ _
      _ = Filter.atTop.liminf (fun n => ∑ x ∈ insert a s, f x n) := by
          apply Filter.liminf_congr
          refine Filter.Eventually.of_forall (fun n => ?_)
          rw [Finset.sum_insert ha]

/-- The truncated multiplier norm² (a real, always-finite quantity) lower-bounds the `j`-th
viscous lower Lebesgue integral: `ofReal ‖mulBdd (min(√W,k)) (𝓕 projⱼ w)‖² ≤ viscousLintegrand_j`.
No `H¹` hypothesis — the truncated integrand is `≤` the full weight pointwise and both are
nonneg, so `lintegral_mono` closes it. -/
private theorem mulBddTrunc_integrable (k : ℕ) (g : L2C_R3) :
    Integrable (fun ξ : Domain3 => (sqrtViscousWeightTrunc k ξ) ^ 2 * ‖(g : Domain3 → ℂ) ξ‖ ^ 2)
      volume := by
  have hgsq : Integrable (fun ξ : Domain3 => ‖(g : Domain3 → ℂ) ξ‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable g)).mp (Lp.memLp g)
  refine Integrable.mono' (hgsq.const_mul ((k : ℝ) ^ 2))
    (((continuous_sqrtViscousWeightTrunc k).pow 2).aestronglyMeasurable.mul
      ((Lp.aestronglyMeasurable g).norm.pow 2))
    (Filter.Eventually.of_forall (fun ξ => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hk2 : (sqrtViscousWeightTrunc k ξ) ^ 2 ≤ (k : ℝ) ^ 2 := by
    rw [← sq_abs (sqrtViscousWeightTrunc k ξ)]
    exact pow_le_pow_left₀ (abs_nonneg _) (sqrtViscousWeightTrunc_abs_le k ξ) 2
  exact mul_le_mul_of_nonneg_right hk2 (by positivity)

private theorem ofReal_norm_mulBddTrunc_sq_le_lintegrand (k : ℕ) (j : Fin 3) (w : L2VF_R3) :
    ENNReal.ofReal (‖mulBdd (sqrtViscousWeightTrunc k) (memLp_top_sqrtViscousWeightTrunc k)
        (𝓕 (L2VF_projComponentC_R3 j w) : L2C_R3)‖ ^ 2) ≤ viscousLintegrand_j j w := by
  set Fj : L2C_R3 := (𝓕 (L2VF_projComponentC_R3 j w) : L2C_R3) with hFj
  rw [norm_mulBdd_sq _ _ Fj, viscousLintegrand_j,
    ofReal_integral_eq_lintegral_ofReal (mulBddTrunc_integrable k Fj)
      (Filter.Eventually.of_forall (fun ξ => by positivity))]
  refine lintegral_mono (fun ξ => ?_)
  apply ENNReal.ofReal_le_ofReal
  have hwsq : (sqrtViscousWeightTrunc k ξ) ^ 2 ≤ (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 := by
    have h1 : sqrtViscousWeightTrunc k ξ ≤ sqrtViscousWeight ξ := min_le_left _ _
    have h2 : (sqrtViscousWeightTrunc k ξ) ^ 2 ≤ (sqrtViscousWeight ξ) ^ 2 :=
      pow_le_pow_left₀ (sqrtViscousWeightTrunc_nonneg _ _) h1 2
    rwa [sqrtViscousWeight_sq, viscousWeight] at h2
  exact mul_le_mul_of_nonneg_right hwsq (by positivity)

/-- **MCT in the truncation level.** The truncated multiplier norms² increase to the `j`-th
viscous lower Lebesgue integral: `⨆ k, ofReal ‖mulBdd_k (𝓕 projⱼ w)‖² = viscousLintegrand_j j w`. -/
private theorem iSup_ofReal_norm_mulBddTrunc_sq (j : Fin 3) (w : L2VF_R3) :
    (⨆ k : ℕ, ENNReal.ofReal (‖mulBdd (sqrtViscousWeightTrunc k)
        (memLp_top_sqrtViscousWeightTrunc k) (𝓕 (L2VF_projComponentC_R3 j w) : L2C_R3)‖ ^ 2))
      = viscousLintegrand_j j w := by
  set Fj : L2C_R3 := (𝓕 (L2VF_projComponentC_R3 j w) : L2C_R3) with hFj
  -- Each term: ofReal ‖mulBdd_k Fj‖² = ∫⁻ ofReal ((min(√W,k))² ‖Fj‖²) (integrable ⟹ ofReal-lintegral).
  have hterm : ∀ k : ℕ,
      ENNReal.ofReal (‖mulBdd (sqrtViscousWeightTrunc k) (memLp_top_sqrtViscousWeightTrunc k) Fj‖ ^ 2)
      = ∫⁻ ξ, ENNReal.ofReal ((sqrtViscousWeightTrunc k ξ) ^ 2 * ‖(Fj : Domain3 → ℂ) ξ‖ ^ 2)
          ∂volume := by
    intro k
    rw [norm_mulBdd_sq _ _ Fj]
    exact ofReal_integral_eq_lintegral_ofReal (mulBddTrunc_integrable k Fj)
      (Filter.Eventually.of_forall (fun ξ => by positivity))
  simp_rw [hterm, viscousLintegrand_j]
  -- monotonicity of the truncated weight squared in `k` (used repeatedly).
  have hmono_w : ∀ ξ : Domain3, Monotone (fun k : ℕ => (sqrtViscousWeightTrunc k ξ) ^ 2) := by
    intro ξ a b hab
    exact pow_le_pow_left₀ (sqrtViscousWeightTrunc_nonneg _ _)
      (by simp only [sqrtViscousWeightTrunc]; exact min_le_min_left _ (by exact_mod_cast hab)) 2
  -- MCT: `⨆ k ∫⁻ gk = ∫⁻ ⨆ k gk`, and pointwise `⨆ k gk = ofReal (W ‖Fj‖²)`.
  rw [← lintegral_iSup]
  · refine lintegral_congr (fun ξ => ?_)
    -- pointwise: `⨆ k, ofReal ((min(√W,k))² ‖Fj‖²) = ofReal ((2π)²‖ξ‖² ‖Fj‖²)`.
    have hwtend : Tendsto (fun k : ℕ => (sqrtViscousWeightTrunc k ξ) ^ 2 * ‖(Fj:Domain3→ℂ) ξ‖ ^ 2)
        atTop (nhds ((2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 * ‖(Fj:Domain3→ℂ) ξ‖ ^ 2)) := by
      have h1 := (tendsto_sqrtViscousWeightTrunc ξ).pow 2
      have h2 := h1.mul_const (‖(Fj:Domain3→ℂ) ξ‖ ^ 2)
      rwa [show sqrtViscousWeight ξ ^ 2 = (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 by
        rw [sqrtViscousWeight_sq, viscousWeight]] at h2
    have hmono2 : Monotone (fun k : ℕ =>
        ENNReal.ofReal ((sqrtViscousWeightTrunc k ξ) ^ 2 * ‖(Fj:Domain3→ℂ) ξ‖ ^ 2)) := by
      intro a b hab
      exact ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (hmono_w ξ hab) (by positivity))
    exact tendsto_nhds_unique (tendsto_atTop_iSup hmono2) (ENNReal.tendsto_ofReal hwtend)
  · intro k
    exact (ENNReal.measurable_ofReal.comp
      (((continuous_sqrtViscousWeightTrunc k).pow 2).measurable.mul
        ((Lp.stronglyMeasurable Fj).measurable.norm.pow_const 2)))
  · intro a b hab
    refine fun ξ => ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (hmono_w ξ hab) (by positivity))

/-- For an `H¹` field `w`, the truncated multiplier norm² is `≤` the (genuinely-integrable) `j`-th
viscous integrand: `‖mulBdd (min(√W,k)) (𝓕 projⱼ w)‖² ≤ viscousIntegrand_j j w`.  (The full weight
integrand is integrable because `w ∈ H¹` — `integrable_viscous_integrand_of_memH1`.) -/
private theorem norm_mulBddTrunc_sq_le_integrand_of_memH1 (k : ℕ) (j : Fin 3) (w : L2VF_R3)
    (hw : memH1VF_R3 w) :
    ‖mulBdd (sqrtViscousWeightTrunc k) (memLp_top_sqrtViscousWeightTrunc k)
        (𝓕 (L2VF_projComponentC_R3 j w) : L2C_R3)‖ ^ 2 ≤ viscousIntegrand_j j w := by
  set Fj : L2C_R3 := (𝓕 (L2VF_projComponentC_R3 j w) : L2C_R3) with hFj
  rw [norm_mulBdd_sq _ _ Fj, viscousIntegrand_j]
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall (fun ξ => by positivity))
    (integrable_viscous_integrand_of_memH1 w hw j) (Filter.Eventually.of_forall (fun ξ => ?_))
  have hwsq : (sqrtViscousWeightTrunc k ξ) ^ 2 ≤ (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 := by
    have h1 : sqrtViscousWeightTrunc k ξ ≤ sqrtViscousWeight ξ := min_le_left _ _
    have h2 : (sqrtViscousWeightTrunc k ξ) ^ 2 ≤ (sqrtViscousWeight ξ) ^ 2 :=
      pow_le_pow_left₀ (sqrtViscousWeightTrunc_nonneg _ _) h1 2
    rwa [sqrtViscousWeight_sq, viscousWeight] at h2
  exact mul_le_mul_of_nonneg_right hwsq (by positivity)

/-- **Per-component pointwise viscous lsc.** Given full-sequence weak-L² convergence
`uₙ ⇀ u` and the uniform `L²` bound, with each approximant `H¹`, the `j`-th viscous lower Lebesgue
integral of the limit is dominated by the `liminf` of the approximants' (Bochner) `j`-integrands:
`viscousLintegrand_j j u ≤ liminf_n ofReal (viscousIntegrand_j j uₙ)`.

Chain (per truncation `k`): push `uₙ ⇀ u` through the bounded CLM `mulBdd_k ∘ 𝓕 ∘ projⱼ`, apply
norm-weak-lsc, square, bound by the approximant integrand (truncated ≤ full, `H¹`); then take the
supremum over `k` (MCT) to recover the full lower Lebesgue integrand of the limit. -/
private theorem viscousLintegrand_le_liminf_of_weak (j : Fin 3)
    (un : ℕ → L2VF_R3) (u : L2VF_R3) (M : ℝ) (hM0 : 0 ≤ M)
    (hbd : ∀ n, ‖un n‖ ≤ M) (hH1 : ∀ n, memH1VF_R3 (un n))
    (hweak : Tendsto (fun n => toWeakSpace ℝ L2VF_R3 (un n)) atTop
      (nhds (toWeakSpace ℝ L2VF_R3 u))) :
    viscousLintegrand_j j u
      ≤ Filter.atTop.liminf (fun n => ENNReal.ofReal (viscousIntegrand_j j (un n))) := by
  -- per truncation `k`: the `ENNReal` bound on the limit's truncated multiplier norm².
  have hk : ∀ k : ℕ,
      ENNReal.ofReal (‖mulBdd (sqrtViscousWeightTrunc k) (memLp_top_sqrtViscousWeightTrunc k)
          (𝓕 (L2VF_projComponentC_R3 j u) : L2C_R3)‖ ^ 2)
        ≤ Filter.atTop.liminf (fun n => ENNReal.ofReal (viscousIntegrand_j j (un n))) := by
    intro k
    -- the bounded CLM `S := mulBdd_k ∘ 𝓕 ∘ projⱼ`, in `L²C` (over ℝ).
    set hCk : ∀ ξ, |sqrtViscousWeightTrunc k ξ| ≤ (k : ℝ) := sqrtViscousWeightTrunc_abs_le k with hCkdef
    set S : L2VF_R3 →L[ℝ] L2C_R3 :=
      (mulBddCLM (sqrtViscousWeightTrunc k) (memLp_top_sqrtViscousWeightTrunc k)
        (Nat.cast_nonneg k) hCk) ∘L fourierProjCLM j with hS
    have hSapply : ∀ w : L2VF_R3, S w = mulBdd (sqrtViscousWeightTrunc k)
        (memLp_top_sqrtViscousWeightTrunc k) (𝓕 (L2VF_projComponentC_R3 j w) : L2C_R3) :=
      fun w => rfl
    -- squared-norm weak-lsc, pushed through the CLM `S`.
    have hsq_lsc : ‖S u‖ ^ 2 ≤ Filter.liminf (fun n => ‖S (un n)‖ ^ 2) atTop :=
      normSq_le_liminf_of_weak (S u) (fun n => S (un n)) (‖S‖ * M) (fun n =>
        le_trans (S.le_opNorm _) (mul_le_mul_of_nonneg_left (hbd n) (norm_nonneg _)))
        (clm_pushes_weak S hweak)
    -- approximant side: `‖S (uₙ)‖² ≤ viscousIntegrand_j j uₙ` (truncated ≤ full, `H¹`).
    have happrox : ∀ n, ‖S (un n)‖ ^ 2 ≤ viscousIntegrand_j j (un n) := by
      intro n; rw [hSapply]
      exact norm_mulBddTrunc_sq_le_integrand_of_memH1 k j (un n) (hH1 n)
    -- bounded-above for `S uₙ` (so its squared-norm liminf transports to `ENNReal` cleanly).
    have hSbddAbove : Filter.IsBoundedUnder (· ≤ ·) atTop (fun n => ‖S (un n)‖ ^ 2) :=
      Filter.isBoundedUnder_of_eventually_le (a := (‖S‖ * M) ^ 2)
        (Filter.Eventually.of_forall (fun n =>
          pow_le_pow_left₀ (norm_nonneg _)
            (le_trans (S.le_opNorm _) (mul_le_mul_of_nonneg_left (hbd n) (norm_nonneg _))) 2))
    have hSbddBelow : Filter.IsBoundedUnder (· ≥ ·) atTop (fun n => ‖S (un n)‖ ^ 2) :=
      Filter.isBoundedUnder_of_eventually_ge (a := 0)
        (Filter.Eventually.of_forall (fun n => by positivity))
    -- `ofReal (‖S u‖²) ≤ ofReal (liminf ‖S uₙ‖²) = liminf (ofReal ‖S uₙ‖²)` (bounded-above ⟹ map-liminf).
    have hofReal_eq : ENNReal.ofReal (Filter.liminf (fun n => ‖S (un n)‖ ^ 2) atTop)
        = Filter.liminf (fun n => ENNReal.ofReal (‖S (un n)‖ ^ 2)) atTop :=
      ENNReal.ofReal_mono.map_liminf_of_continuousAt _ ENNReal.continuous_ofReal.continuousAt
        hSbddAbove.isCoboundedUnder_ge hSbddBelow
    rw [← hSapply u]
    calc ENNReal.ofReal (‖S u‖ ^ 2)
        ≤ ENNReal.ofReal (Filter.liminf (fun n => ‖S (un n)‖ ^ 2) atTop) :=
          ENNReal.ofReal_le_ofReal hsq_lsc
      _ = Filter.liminf (fun n => ENNReal.ofReal (‖S (un n)‖ ^ 2)) atTop := hofReal_eq
      _ ≤ Filter.atTop.liminf (fun n => ENNReal.ofReal (viscousIntegrand_j j (un n))) :=
          Filter.liminf_le_liminf (Filter.Eventually.of_forall
            (fun n => ENNReal.ofReal_le_ofReal (happrox n)))
  -- assemble via MCT-sup in `k`.
  calc viscousLintegrand_j j u
      = ⨆ k : ℕ, ENNReal.ofReal (‖mulBdd (sqrtViscousWeightTrunc k)
          (memLp_top_sqrtViscousWeightTrunc k) (𝓕 (L2VF_projComponentC_R3 j u) : L2C_R3)‖ ^ 2) :=
        (iSup_ofReal_norm_mulBddTrunc_sq j u).symm
    _ ≤ Filter.atTop.liminf (fun n => ENNReal.ofReal (viscousIntegrand_j j (un n))) :=
        iSup_le hk

/-- **A.e. finiteness of the approximant-`liminf` viscous form.** From `reg_bound`
(`∫₀ᵀ viscousFormSq_R3 ν (uₙ) ≤ ½‖u₀‖²`, `n`-uniform) and Fatou-in-time, the `liminf` of the
approximants' viscous forms is finite at a.e. `t`.  No `H¹`/measurability of the LIMIT is used —
only the continuous (hence measurable) approximant curves. -/
private theorem liminf_viscousFormSq_lt_top_ae (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T) (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n)
    (alPkg : AubinLionsPackage_R3 𝔊 F ν T u₀ galSeq) :
    ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Filter.atTop.liminf
        (fun n => ENNReal.ofReal (viscousFormSq_R3 1 ((galSeq (alPkg.φ n)).u t : L2VF_R3))) < ⊤ := by
  set μ : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) T) with hμ
  set gn : ℕ → ℝ → ℝ :=
    fun n t => viscousFormSq_R3 1 ((galSeq (alPkg.φ n)).u t : L2VF_R3) with hgn
  have hgn_nonneg : ∀ n t, 0 ≤ gn n t := fun n t => viscousFormSq_R3_nonneg (by norm_num) _
  have hgn_cont : ∀ n, ContinuousOn (gn n) (Set.Ici (0 : ℝ)) :=
    fun n => viscousFormSq_curve_continuousOn 𝔊 F ν u₀ (alPkg.φ n) (galSeq (alPkg.φ n))
  have hgn_meas : ∀ n, AEMeasurable (fun t => ENNReal.ofReal (gn n t)) μ := by
    intro n; rw [hμ]
    exact ((ContinuousOn.aemeasurable ((hgn_cont n).mono (fun t ht => ht.1))
      measurableSet_Icc)).ennreal_ofReal
  -- `reg_bound` gives `∫₀ᵀ gn n ≤ ν⁻¹·½‖u₀‖²` (rescale the `ν`-form).
  have hgn_int : ∀ n, ∫ s in (0 : ℝ)..T, gn n s ≤ ν⁻¹ * ((1 / 2 : ℝ) * ‖(u₀ : L2VF_R3)‖ ^ 2) := by
    intro n
    have hrb := (galSeq (alPkg.φ n)).reg_bound T hT
    have hscale : ∀ s, viscousFormSq_R3 ν ((galSeq (alPkg.φ n)).u s : L2VF_R3) = ν * gn n s :=
      fun s => by rw [hgn, viscousFormSq_R3_eq_smul, smul_eq_mul]
    rw [intervalIntegral.integral_congr (g := fun s => ν * gn n s) (fun s _ => hscale s),
      intervalIntegral.integral_const_mul] at hrb
    rw [le_inv_mul_iff₀ hν]; exact hrb
  -- `∫⁻ ofReal (gn n) = ofReal (∫_{Icc} gn n) ≤ ofReal (ν⁻¹·½‖u₀‖²)`.
  have hGn_cap : ∀ n, ∫⁻ t, ENNReal.ofReal (gn n t) ∂μ
      ≤ ENNReal.ofReal (ν⁻¹ * ((1 / 2 : ℝ) * ‖(u₀ : L2VF_R3)‖ ^ 2)) := by
    intro n
    have hint : IntegrableOn (gn n) (Set.Icc (0 : ℝ) T) volume :=
      ContinuousOn.integrableOn_Icc ((hgn_cont n).mono (fun t ht => ht.1))
    have heq : ∫⁻ t, ENNReal.ofReal (gn n t) ∂μ
        = ENNReal.ofReal (∫ t in Set.Icc (0 : ℝ) T, gn n t ∂volume) := by
      rw [hμ, ← ofReal_integral_eq_lintegral_ofReal hint
        (Filter.Eventually.of_forall (fun t => hgn_nonneg n t))]
    rw [heq]
    refine ENNReal.ofReal_le_ofReal ?_
    have hni := hgn_int n
    rwa [intervalIntegral.integral_of_le hT.le, ← MeasureTheory.integral_Icc_eq_integral_Ioc] at hni
  -- a measurable representative of each `ofReal (gn n)`, and the a.e.-eq liminf.
  set Gn : ℕ → ℝ → ENNReal := fun n => (hgn_meas n).mk with hGndef
  have hGn_meas' : ∀ n, Measurable (Gn n) := fun n => (hgn_meas n).measurable_mk
  have hGn_ae : ∀ n, (fun t => ENNReal.ofReal (gn n t)) =ᵐ[μ] Gn n :=
    fun n => (hgn_meas n).ae_eq_mk
  have hliminf_ae : (fun t => Filter.atTop.liminf (fun n => ENNReal.ofReal (gn n t)))
      =ᵐ[μ] (fun t => Filter.atTop.liminf (fun n => Gn n t)) := by
    have hall : ∀ᵐ t ∂μ, ∀ n, ENNReal.ofReal (gn n t) = Gn n t := ae_all_iff.2 hGn_ae
    filter_upwards [hall] with t ht
    exact Filter.liminf_congr (Filter.Eventually.of_forall (fun n => ht n))
  -- Fatou: `∫⁻ liminf (ofReal gn) ≤ liminf ∫⁻ (ofReal gn) ≤ ofReal(…) < ∞`.
  have hfatou : ∫⁻ t, Filter.atTop.liminf (fun n => ENNReal.ofReal (gn n t)) ∂μ
      ≤ ENNReal.ofReal (ν⁻¹ * ((1 / 2 : ℝ) * ‖(u₀ : L2VF_R3)‖ ^ 2)) := by
    refine le_trans (lintegral_liminf_le' hgn_meas) ?_
    refine le_trans liminf_le_limsup ?_
    exact limsup_le_of_le isCobounded_le_of_bot (Filter.Eventually.of_forall hGn_cap)
  have hlt : ∫⁻ t, Filter.atTop.liminf (fun n => Gn n t) ∂μ < ⊤ := by
    rw [← lintegral_congr_ae hliminf_ae]; exact lt_of_le_of_lt hfatou ENNReal.ofReal_lt_top
  have hae_fin : ∀ᵐ t ∂μ, Filter.atTop.liminf (fun n => Gn n t) < ⊤ :=
    ae_lt_top (Measurable.liminf hGn_meas') hlt.ne
  filter_upwards [hae_fin, hliminf_ae] with t hfin hcong
  rw [hcong]; exact hfin

/-- For an `H¹` field, the (Bochner) `j`-th viscous integrand equals the `toReal` of its lower
Lebesgue counterpart: `viscousIntegrand_j j w = (viscousLintegrand_j j w).toReal`.  (On `H¹` the
integrand is integrable, so `ofReal (∫ ·) = ∫⁻ ofReal ·`.) -/
private theorem viscousIntegrand_eq_lintegrand_toReal (j : Fin 3) (w : L2VF_R3)
    (hw : memH1VF_R3 w) :
    viscousIntegrand_j j w = (viscousLintegrand_j j w).toReal := by
  rw [viscousIntegrand_j, viscousLintegrand_j,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_viscous_integrand_of_memH1 w hw j)
      (Filter.Eventually.of_forall (fun ξ => by positivity)),
    ENNReal.toReal_ofReal (integral_nonneg (fun ξ => by positivity))]

/-- **Time-measurability of `t ↦ viscousFormSq_R3 1 (alPkg.u t)`** under a.e. `H¹` membership.
On the (a.e.) `H¹` set the viscous form is `∑ⱼ (viscousLintegrand_j j (u t)).toReal`, and
`viscousLintegrand_j j (u t) = ⨆ₖ ofReal ‖mulBdd_k (𝓕 projⱼ (u t))‖²` (MCT) is a countable
supremum of `AEStronglyMeasurable`-in-`t` functions (continuous CLM ∘ measurable `u`), hence
`AEMeasurable`; `.toReal` and the finite sum preserve measurability. -/
private theorem viscousFormSq_aestronglyMeasurable_of_memH1
    {𝔊 : R3GalerkinScheme} {F : R3NSForms 𝔊} {ν T : ℝ} {u₀ : L2Sigma_R3}
    {galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n}
    (alPkg : AubinLionsPackage_R3 𝔊 F ν T u₀ galSeq)
    (hmemH1 : ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)), memH1VF_R3 (alPkg.u t : L2VF_R3)) :
    AEStronglyMeasurable (fun t => viscousFormSq_R3 1 (alPkg.u t : L2VF_R3))
      (volume.restrict (Set.Icc (0 : ℝ) T)) := by
  set μ : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) T) with hμ
  set u : ℝ → L2VF_R3 := fun t => (alPkg.u t : L2VF_R3) with hu
  have hu_meas : AEStronglyMeasurable u μ := by rw [hμ, hu]; exact alPkg.u_aestronglyMeasurable
  -- for each `k j`, `t ↦ ‖mulBdd_k (𝓕 projⱼ (u t))‖²` is AEStronglyMeasurable (CLM ∘ measurable).
  have hmk : ∀ (k : ℕ) (j : Fin 3),
      AEStronglyMeasurable (fun t => ‖mulBdd (sqrtViscousWeightTrunc k)
        (memLp_top_sqrtViscousWeightTrunc k) (𝓕 (L2VF_projComponentC_R3 j (u t)) : L2C_R3)‖ ^ 2) μ := by
    intro k j
    set S : L2VF_R3 →L[ℝ] L2C_R3 :=
      (mulBddCLM (sqrtViscousWeightTrunc k) (memLp_top_sqrtViscousWeightTrunc k)
        (Nat.cast_nonneg k) (sqrtViscousWeightTrunc_abs_le k)) ∘L fourierProjCLM j with hS
    refine ((S.continuous.comp_aestronglyMeasurable hu_meas).norm.pow 2).congr ?_
    exact Filter.Eventually.of_forall (fun t => rfl)
  -- `t ↦ viscousLintegrand_j j (u t) = ⨆ₖ ofReal ‖mulBdd_k …‖²` is AEMeasurable.
  have hlin_meas : ∀ j : Fin 3, AEMeasurable (fun t => viscousLintegrand_j j (u t)) μ := by
    intro j
    have hsup : (fun t => viscousLintegrand_j j (u t))
        = fun t => ⨆ k : ℕ, ENNReal.ofReal (‖mulBdd (sqrtViscousWeightTrunc k)
            (memLp_top_sqrtViscousWeightTrunc k)
            (𝓕 (L2VF_projComponentC_R3 j (u t)) : L2C_R3)‖ ^ 2) := by
      funext t; exact (iSup_ofReal_norm_mulBddTrunc_sq j (u t)).symm
    rw [hsup]
    exact AEMeasurable.iSup (fun k => (hmk k j).aemeasurable.ennreal_ofReal)
  -- `t ↦ viscousFormSq(u t)` =ᵐ `∑ⱼ (viscousLintegrand_j j (u t)).toReal`, which is AEMeasurable.
  have heq : (fun t => viscousFormSq_R3 1 (u t))
      =ᵐ[μ] fun t => ∑ j : Fin 3, (viscousLintegrand_j j (u t)).toReal := by
    filter_upwards [hmemH1] with t hmem
    show viscousFormSq_R3 1 (u t) = ∑ j : Fin 3, (viscousLintegrand_j j (u t)).toReal
    rw [viscousFormSq_eq_sum_integrand]
    exact Finset.sum_congr rfl (fun j _ => viscousIntegrand_eq_lintegrand_toReal j (u t) hmem)
  refine AEStronglyMeasurable.congr ?_ heq.symm
  refine (Finset.aemeasurable_sum Finset.univ (fun j _ => (hlin_meas j).ennreal_toReal)).aestronglyMeasurable

/-- **Pointwise weak-H¹ lower semicontinuity of the viscous seminorm** (the genuine analytic
content of the (b)-route's energy/energy-class conclusions) — PROVED `sorry`-free.

At a.e. time `t ∈ [0, T]` the strong-L²(-on-balls) Galerkin limit `alPkg.u t` lies in `H¹` and
its viscous (Dirichlet) seminorm is dominated by the `liminf` of the approximants':

```
memH1VF_R3 (alPkg.u t) ∧
ofReal (viscousFormSq_R3 1 (alPkg.u t)) ≤ liminf_n ofReal (viscousFormSq_R3 1 ((galSeq (alPkg.φ n)).u t))
```

together with time-measurability of the limit's viscous form (needed to feed Fatou downstream).

**Proof route — Fourier–Plancherel, entirely in `L²`** (no H¹ Hilbert-space type, no sequential
Banach–Alaoglu, no convex-functional weak-lsc). The viscous form `viscousFormSq_R3 1 w =
∑ⱼ ∫ (2π)²‖ξ‖² ‖𝓕(projⱼ w) ξ‖²` is the global Fourier Dirichlet seminorm: not continuous, only
weakly lower-semicontinuous, under strong-L². The chain:
* **Full-sequence weak-L²** `uₙ(t) ⇀ u(t)` a.e. `t`, from `alPkg.strong_convergence_ae` (per-ball
  a.e.-`t` strong convergence) + the ball-tail ε/3 argument against the uniform `‖uₙ t‖ ≤ ‖u₀‖`
  (`inner_tendsto_of_perball` / `weak_tendsto_of_inner_tendsto`). The full-sequence form is what
  the frozen `liminf` over `n` requires — supplied by the package's a.e.-`t` field, not a
  measure-subsequence.
* **Bounded-multiplier push**: for each truncation `k`, `mulBdd (min(√W,k)) ∘ 𝓕 ∘ projⱼ` is an
  ℝ-CLM (`mulBddCLM`/`fourierProjCLM`), so `clm_pushes_weak` transports the weak convergence; then
  squared norm-weak-lsc (`normSq_le_liminf_of_weak`, the inner-product trick `‖g‖² = lim⟪g,gₙ⟫`).
* **Truncated ≤ full + MCT in `k`** (`iSup_ofReal_norm_mulBddTrunc_sq`, `lintegral_iSup`) recovers
  the full Dirichlet integrand; sum over `j` by `ENNReal` `liminf`-superadditivity. The `memH1`
  conjunct follows from the finite weighted-Fourier integral (`reg_bound`+Fatou finiteness in
  `liminf_viscousFormSq_lt_top_ae`) via `memSobolev_of_finite_weightedFourier_R3`; time-measurability
  via `viscousFormSq_aestronglyMeasurable_of_memH1`.

`0 < ν` is load-bearing: the approximants' H¹ seminorm is controlled only through `reg_bound`'s
`ν`-weighted bound, so the `memH1` conjunct genuinely fails for `ν ≤ 0`. The *integrated* bound
(`∫₀ᵀ viscous(u) ≤ ½‖u₀‖²`) is assembled from this via Fatou-in-time + `reg_bound` in
`viscous_lsc_under_strongL2`. Temam III.3 / Lemarié-Rieusset §6. -/
private theorem viscous_pointwise_lsc (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν T : ℝ) (hν : 0 < ν) (hT : 0 < T) (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n)
    (alPkg : AubinLionsPackage_R3 𝔊 F ν T u₀ galSeq) :
    (AEStronglyMeasurable
        (fun t => viscousFormSq_R3 1 (alPkg.u t : L2VF_R3))
        (volume.restrict (Set.Icc (0 : ℝ) T))) ∧
    (∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      memH1VF_R3 (alPkg.u t : L2VF_R3) ∧
      ENNReal.ofReal (viscousFormSq_R3 1 (alPkg.u t : L2VF_R3)) ≤
        Filter.atTop.liminf
          (fun n => ENNReal.ofReal (viscousFormSq_R3 1 ((galSeq (alPkg.φ n)).u t : L2VF_R3)))) := by
  -- ════ FOURIER–PLANCHEREL ROUTE (full-sequence, in `L²`; no H¹ Hilbert type, no Banach–Alaoglu). ════
  classical
  set μ : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) T) with hμ
  -- abbreviations for the limit / approximant curves.
  set u : ℝ → L2VF_R3 := fun t => (alPkg.u t : L2VF_R3) with hu
  set un : ℕ → ℝ → L2VF_R3 := fun n t => ((galSeq (alPkg.φ n)).u t : L2VF_R3) with hun
  -- (A) full-sequence weak-L² convergence `uₙ(t) ⇀ u(t)` at a.e. `t`, from `strong_convergence_ae`
  -- (per-ball a.e.-`t` convergence) + the ball-tail ε/3 argument, against the uniform `‖·‖ ≤ ‖u₀‖`.
  -- Only NAT radii are needed (the ball-tail argument uses one integer radius per ε), so the
  -- a.e.-`t` exceptional set unions over a COUNTABLE family.
  have hperball_ae : ∀ᵐ t ∂μ, ∀ k : ℕ,
      Tendsto (fun n => restrictToBall (k : ℝ) (un n t)) atTop
        (nhds (restrictToBall (k : ℝ) (u t))) :=
    ae_all_iff.2 (fun k => alPkg.strong_convergence_ae (k : ℝ))
  -- a.e.-`t`: `t ∈ Icc 0 T` (so `0 ≤ t`), giving the uniform Galerkin bound.
  have ht_nonneg : ∀ᵐ t ∂μ, (0 : ℝ) ≤ t :=
    ae_restrict_of_forall_mem measurableSet_Icc (fun t ht => ht.1)
  -- (B) the kinetic-lsc limit bound `‖u t‖ ≤ ‖u₀‖` a.e. (recover from `kineticEnergy_lsc_bound`).
  have hu_bound : ∀ᵐ t ∂μ, ‖u t‖ ≤ ‖(u₀ : L2VF_R3)‖ := by
    have hkin := kineticEnergy_lsc_bound 𝔊 F ν T u₀ galSeq alPkg
    filter_upwards [hkin] with t ht
    have h2 : ‖(alPkg.u t : L2VF_R3)‖ ^ 2 ≤ ‖(u₀ : L2VF_R3)‖ ^ 2 := by nlinarith [ht]
    nlinarith [norm_nonneg (alPkg.u t : L2VF_R3), norm_nonneg (u₀ : L2VF_R3), h2]
  -- weak convergence at a.e. `t`.
  have hweak : ∀ᵐ t ∂μ,
      Tendsto (fun n => toWeakSpace ℝ L2VF_R3 (un n t)) atTop (nhds (toWeakSpace ℝ L2VF_R3 (u t))) := by
    filter_upwards [hperball_ae, ht_nonneg, hu_bound] with t hpb ht0 hub
    refine weak_tendsto_of_inner_tendsto (un · t) (u t) (fun e => ?_)
    exact inner_tendsto_of_perball e (un · t) (u t) ‖(u₀ : L2VF_R3)‖ (norm_nonneg _)
      (fun n => by rw [hun]; exact galerkin_norm_le_u0 𝔊 F ν u₀ (alPkg.φ n) (galSeq (alPkg.φ n)) ht0)
      hub hpb
  -- approximants are `H¹` (`reg_mem`).
  have hH1 : ∀ n (t : ℝ), memH1VF_R3 (un n t) := fun n t => (galSeq (alPkg.φ n)).reg_mem t
  -- (C) the per-component viscous lsc bound, applied at each `j`, at a.e. `t`.
  have hlsc_j : ∀ᵐ t ∂μ, ∀ j : Fin 3,
      viscousLintegrand_j j (u t)
        ≤ Filter.atTop.liminf (fun n => ENNReal.ofReal (viscousIntegrand_j j (un n t))) := by
    filter_upwards [hweak, ht_nonneg] with t hwt ht0
    intro j
    exact viscousLintegrand_le_liminf_of_weak j (un · t) (u t) ‖(u₀ : L2VF_R3)‖ (norm_nonneg _)
      (fun n => by rw [hun]; exact galerkin_norm_le_u0 𝔊 F ν u₀ (alPkg.φ n) (galSeq (alPkg.φ n)) ht0)
      (fun n => hH1 n t) hwt
  -- (D) finiteness of the limit's per-component lower-Lebesgue integrand at a.e. `t`
  -- (`viscousLintegrand_j j (u t) ≤ liminf_n ofReal viscousFormSq(uₙ t) < ∞`), via `reg_bound`+Fatou.
  have hfin_lt : ∀ᵐ t ∂μ,
      Filter.atTop.liminf (fun n => ENNReal.ofReal (viscousFormSq_R3 1 (un n t))) < ⊤ := by
    rw [hμ, hun]; exact liminf_viscousFormSq_lt_top_ae 𝔊 F ν hν T hT u₀ galSeq alPkg
  have hLintegrand_lt : ∀ᵐ t ∂μ, ∀ j : Fin 3, viscousLintegrand_j j (u t) < ⊤ := by
    filter_upwards [hlsc_j, hfin_lt] with t ht hfin
    intro j
    refine lt_of_le_of_lt (le_trans (ht j) ?_) hfin
    refine Filter.liminf_le_liminf (Filter.Eventually.of_forall (fun n => ?_))
    rw [viscousFormSq_eq_sum_integrand,
      ENNReal.ofReal_sum_of_nonneg (fun i _ => viscousIntegrand_j_nonneg i (un n t))]
    exact Finset.single_le_sum
      (fun i _ => (bot_le : (⊥ : ENNReal) ≤ ENNReal.ofReal (viscousIntegrand_j i (un n t))))
      (Finset.mem_univ j)
  -- (E) `memH1VF_R3 (u t)` at a.e. `t`, from the finite weighted-Fourier integrals (the bridge).
  have hmemH1 : ∀ᵐ t ∂μ, memH1VF_R3 (u t) := by
    filter_upwards [hLintegrand_lt] with t hfin
    exact memSobolev_of_finite_weightedFourier_R3 (u t) (fun j => hfin j)
  refine ⟨?_, ?_⟩
  · -- measurability conjunct: on the (a.e.) `H¹` set, `viscousFormSq(u t) = ∑ⱼ (⨆ₖ ‖mulBdd_k‖²)`,
    -- a measurable function of `t` (sup of the continuous-CLM-composed AEStronglyMeasurable `u`).
    exact viscousFormSq_aestronglyMeasurable_of_memH1 alPkg hmemH1
  · filter_upwards [hlsc_j, hmemH1] with t ht hmem
    refine ⟨hmem, ?_⟩
    · -- the spectral lsc bound, summed over `j` (the PROVEN analytic core).
      rw [viscousFormSq_eq_sum_integrand,
        ENNReal.ofReal_sum_of_nonneg (fun j _ => viscousIntegrand_j_nonneg j (u t))]
      calc ∑ j : Fin 3, ENNReal.ofReal (viscousIntegrand_j j (u t))
          ≤ ∑ j : Fin 3, viscousLintegrand_j j (u t) :=
            Finset.sum_le_sum (fun j _ => ofReal_viscousIntegrand_le_lintegrand j (u t))
        _ ≤ ∑ j : Fin 3, Filter.atTop.liminf
              (fun n => ENNReal.ofReal (viscousIntegrand_j j (un n t))) :=
            Finset.sum_le_sum (fun j _ => ht j)
        _ ≤ Filter.atTop.liminf
              (fun n => ∑ j : Fin 3, ENNReal.ofReal (viscousIntegrand_j j (un n t))) :=
            sum_liminf_le_liminf_sum Finset.univ _
        _ = Filter.atTop.liminf
              (fun n => ENNReal.ofReal (viscousFormSq_R3 1 (un n t))) := by
            apply Filter.liminf_congr
            refine Filter.Eventually.of_forall (fun n => ?_)
            rw [viscousFormSq_eq_sum_integrand, ENNReal.ofReal_sum_of_nonneg
              (fun j _ => viscousIntegrand_j_nonneg j (un n t))]

/-- **Integrated viscous lower-semicontinuity bound + energy-class membership (the load-bearing
new lemma of the (b)-route).** Shared by conclusion 1 (energy inequality) and conclusion 4
(energy class) of `galerkin_limit_passage_R3`.

From the n-uniform Galerkin regularity bound (`reg_bound`: `∫₀ᵀ viscousFormSq_R3 ν (uₙ) ≤ ½‖u₀‖²`)
and the strong-L²(-on-balls) convergence to the Aubin–Lions limit `alPkg.u`, the limit lies in
the Leray–Hopf energy class with a dissipation budget no larger than the approximants':

```
(∀ᵐ t, memH1VF_R3 (alPkg.u t)) ∧
IntervalIntegrable (fun s => viscousFormSq_R3 ν (alPkg.u s)) volume 0 T ∧
∫₀ᵀ viscousFormSq_R3 ν (alPkg.u s) ≤ ½‖u₀‖²
```

The mechanism is **weak lower-semicontinuity of the viscous (Dirichlet) seminorm** under the
strong-L² limit. The genuinely-new analytic content — the *pointwise* weak-H¹ lsc — is isolated
in `viscous_pointwise_lsc`; this lemma assembles the integrated bound and the energy-class
membership from it **axiom-free**, by Fatou's lemma in time (`lintegral_liminf_le`) against the
`liminf` of the approximant dissipations, which `reg_bound` caps by `½‖u₀‖²`. -/
theorem viscous_lsc_under_strongL2 (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T) (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n)
    (alPkg : AubinLionsPackage_R3 𝔊 F ν T u₀ galSeq) :
    (∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)), memH1VF_R3 (alPkg.u t : L2VF_R3)) ∧
    IntervalIntegrable (fun s => viscousFormSq_R3 ν (alPkg.u s : L2VF_R3)) volume 0 T ∧
    ∫ s in (0 : ℝ)..T, viscousFormSq_R3 ν (alPkg.u s : L2VF_R3) ≤
      (1 / 2 : ℝ) * ‖(u₀ : L2VF_R3)‖ ^ 2 := by
  classical
  set μ : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) T) with hμ
  haveI hμfin : IsFiniteMeasure μ := by
    rw [hμ]; refine isFiniteMeasure_restrict.2 ?_
    rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  -- The pointwise weak-H¹ lsc (proved via the Fourier–Plancherel route) + measurability of the
  -- limit's viscous form.
  obtain ⟨hmeas_u, hptwise⟩ := viscous_pointwise_lsc 𝔊 F ν T hν hT u₀ galSeq alPkg
  -- Abbreviations for the `ν = 1` viscous forms (scaling by `ν` is folded in at the end).
  set g : ℝ → ℝ := fun t => viscousFormSq_R3 1 (alPkg.u t : L2VF_R3) with hg
  set gn : ℕ → ℝ → ℝ :=
    fun n t => viscousFormSq_R3 1 ((galSeq (alPkg.φ n)).u t : L2VF_R3) with hgn
  -- Nonnegativity of every viscous form (`ν = 1 ≥ 0`).
  have hg_nonneg : ∀ t, 0 ≤ g t := fun t => viscousFormSq_R3_nonneg (by norm_num) _
  have hgn_nonneg : ∀ n t, 0 ≤ gn n t := fun n t => viscousFormSq_R3_nonneg (by norm_num) _
  -- (1) a.e. `H¹` membership of the limit — directly the first pointwise conjunct.
  have hmem : ∀ᵐ t ∂μ, memH1VF_R3 (alPkg.u t : L2VF_R3) := by
    rw [hμ]; filter_upwards [hptwise] with t ht; exact ht.1
  -- (2) the pointwise `ENNReal` bound `ofReal (g t) ≤ liminf_n ofReal (gn n t)` a.e.
  have hGbound : ∀ᵐ t ∂μ,
      ENNReal.ofReal (g t) ≤ Filter.atTop.liminf (fun n => ENNReal.ofReal (gn n t)) := by
    rw [hμ]; filter_upwards [hptwise] with t ht; exact ht.2
  -- ════ Approximant-side: each `gn n` is continuous on `Ici 0 ⊇ Icc 0 T`, hence
  -- a.e.-measurable and interval-integrable on `[0,T]`, with `∫₀ᵀ ν·gn n ≤ ½‖u₀‖²` (`reg_bound`). ════
  have hgn_cont : ∀ n, ContinuousOn (gn n) (Set.Ici (0 : ℝ)) :=
    fun n => viscousFormSq_curve_continuousOn 𝔊 F ν u₀ (alPkg.φ n) (galSeq (alPkg.φ n))
  have hgn_meas : ∀ n, AEMeasurable (gn n) μ := by
    intro n
    rw [hμ]
    refine (ContinuousOn.aemeasurable ((hgn_cont n).mono ?_) measurableSet_Icc)
    intro t ht; exact ht.1
  have hgn_int : ∀ n, ∫ s in (0 : ℝ)..T, gn n s ≤ ν⁻¹ * ((1 / 2 : ℝ) * ‖(u₀ : L2VF_R3)‖ ^ 2) := by
    intro n
    have hrb := (galSeq (alPkg.φ n)).reg_bound T hT
    -- `reg_bound` is in `ν`-form; rescale to the `ν = 1` integrand.
    have hscale : ∀ s, viscousFormSq_R3 ν ((galSeq (alPkg.φ n)).u s : L2VF_R3)
        = ν * gn n s := by
      intro s; rw [hgn, viscousFormSq_R3_eq_smul, smul_eq_mul]
    rw [intervalIntegral.integral_congr (g := fun s => ν * gn n s) (fun s _ => hscale s),
      intervalIntegral.integral_const_mul] at hrb
    rw [le_inv_mul_iff₀ hν]; exact hrb
  -- ════ Fatou in time: `∫⁻ ofReal g ≤ liminf_n ∫⁻ ofReal (gn n) ≤ ν⁻¹·½‖u₀‖² < ∞`. ════
  -- Measurability of the `ENNReal`-lifted integrands.
  have hg_aem : AEMeasurable g μ := by
    rw [hg]; exact hmeas_u.aemeasurable
  have hGn_meas : ∀ n, AEMeasurable (fun t => ENNReal.ofReal (gn n t)) μ :=
    fun n => (hgn_meas n).ennreal_ofReal
  -- The lintegral Fatou bound.
  have hlin_fatou : ∫⁻ t, ENNReal.ofReal (g t) ∂μ
      ≤ Filter.atTop.liminf (fun n => ∫⁻ t, ENNReal.ofReal (gn n t) ∂μ) := by
    calc ∫⁻ t, ENNReal.ofReal (g t) ∂μ
        ≤ ∫⁻ t, Filter.atTop.liminf (fun n => ENNReal.ofReal (gn n t)) ∂μ :=
          lintegral_mono_ae hGbound
      _ ≤ Filter.atTop.liminf (fun n => ∫⁻ t, ENNReal.ofReal (gn n t) ∂μ) :=
          lintegral_liminf_le' hGn_meas
  -- Each approximant lintegral equals its (nonneg) Bochner interval integral, capped by reg_bound.
  have hGn_eq : ∀ n,
      ∫⁻ t, ENNReal.ofReal (gn n t) ∂μ
        = ENNReal.ofReal (∫ s in (0 : ℝ)..T, gn n s) := by
    intro n
    have hint : IntegrableOn (gn n) (Set.Icc (0 : ℝ) T) volume := by
      refine (ContinuousOn.integrableOn_Icc ((hgn_cont n).mono ?_))
      intro t ht; exact ht.1
    rw [hμ, ← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall (fun t => hgn_nonneg n t))]
    rw [intervalIntegral.integral_of_le hT.le,
      ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  -- Bound each approximant lintegral by the n-uniform constant.
  have hGn_cap : ∀ n,
      ∫⁻ t, ENNReal.ofReal (gn n t) ∂μ
        ≤ ENNReal.ofReal (ν⁻¹ * ((1 / 2 : ℝ) * ‖(u₀ : L2VF_R3)‖ ^ 2)) := by
    intro n; rw [hGn_eq n]; exact ENNReal.ofReal_le_ofReal (hgn_int n)
  have hliminf_cap :
      Filter.atTop.liminf (fun n => ∫⁻ t, ENNReal.ofReal (gn n t) ∂μ)
        ≤ ENNReal.ofReal (ν⁻¹ * ((1 / 2 : ℝ) * ‖(u₀ : L2VF_R3)‖ ^ 2)) := by
    refine le_trans liminf_le_limsup ?_
    exact limsup_le_of_le isCobounded_le_of_bot (Filter.Eventually.of_forall hGn_cap)
  have hlin_cap : ∫⁻ t, ENNReal.ofReal (g t) ∂μ
      ≤ ENNReal.ofReal (ν⁻¹ * ((1 / 2 : ℝ) * ‖(u₀ : L2VF_R3)‖ ^ 2)) :=
    le_trans hlin_fatou hliminf_cap
  -- ════ From the finite lintegral: integrability of `g` and the real integral bound. ════
  have hg_int_lt : ∫⁻ t, ENNReal.ofReal (g t) ∂μ < ⊤ :=
    lt_of_le_of_lt hlin_cap ENNReal.ofReal_lt_top
  have hg_integrable : Integrable g μ := by
    refine ⟨hmeas_u, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hg_nonneg)]
    exact hg_int_lt
  -- The real integral of `g` over `Icc 0 T`, via `ofReal`-lintegral identity.
  have hg_int_eq : ENNReal.ofReal (∫ t, g t ∂μ) = ∫⁻ t, ENNReal.ofReal (g t) ∂μ :=
    ofReal_integral_eq_lintegral_ofReal hg_integrable (Filter.Eventually.of_forall hg_nonneg)
  have hg_int_bound : ∫ t, g t ∂μ ≤ ν⁻¹ * ((1 / 2 : ℝ) * ‖(u₀ : L2VF_R3)‖ ^ 2) := by
    have hnn : (0 : ℝ) ≤ ν⁻¹ * ((1 / 2 : ℝ) * ‖(u₀ : L2VF_R3)‖ ^ 2) := by positivity
    have := hg_int_eq ▸ hlin_cap
    rwa [ENNReal.ofReal_le_ofReal_iff hnn] at this
  -- Translate `μ`-integral back to the `intervalIntegral` over `[0,T]`.
  have hg_interval : IntervalIntegrable g volume 0 T := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le]
    have hIcc : IntegrableOn g (Set.Icc (0 : ℝ) T) volume := by
      rw [IntegrableOn, ← hμ]; exact hg_integrable
    exact hIcc.mono_set Set.Ioc_subset_Icc_self
  have hg_interval_eq : ∫ s in (0 : ℝ)..T, g s = ∫ t, g t ∂μ := by
    rw [hμ, intervalIntegral.integral_of_le hT.le, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  -- ════ Assemble the three conclusions (rescaling `ν = 1` ⟹ `ν`). ════
  refine ⟨hmem, ?_, ?_⟩
  · -- IntervalIntegrable of the `ν`-form: constant-multiple of the `ν = 1` form.
    have hscale : (fun s => viscousFormSq_R3 ν (alPkg.u s : L2VF_R3)) = fun s => ν * g s := by
      funext s; rw [hg, viscousFormSq_R3_eq_smul, smul_eq_mul]
    rw [hscale]; exact hg_interval.const_mul ν
  · -- The `ν`-form integral bound: `∫ ν·g = ν·∫ g ≤ ν·(ν⁻¹·½‖u₀‖²) = ½‖u₀‖²`.
    have hscale : ∀ s, viscousFormSq_R3 ν (alPkg.u s : L2VF_R3) = ν * g s := by
      intro s; rw [hg, viscousFormSq_R3_eq_smul, smul_eq_mul]
    rw [intervalIntegral.integral_congr (g := fun s => ν * g s) (fun s _ => hscale s),
      intervalIntegral.integral_const_mul, hg_interval_eq]
    calc ν * ∫ t, g t ∂μ
        ≤ ν * (ν⁻¹ * ((1 / 2 : ℝ) * ‖(u₀ : L2VF_R3)‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left hg_int_bound hν.le
      _ = (1 / 2 : ℝ) * ‖(u₀ : L2VF_R3)‖ ^ 2 := by
          rw [← mul_assoc, mul_inv_cancel₀ hν.ne', one_mul]

/-! ### Tier C-prep — Steklov interval-average building blocks for the Aubin–Lions route

These `private` helpers are the genuine, axiom-free sub-lemmas of the Steklov
interval-averaging route to C2 (the real Aubin–Lions argument). They are proved here
independently of the final assembly so that the route's reusable pieces are landed even
while the full space-time diagonalization remains open (see the C2 TODO). -/

/-- **Hilbert-space Jensen for a Bochner interval average (squared-norm form).** For a curve
`f : ℝ → H` into a complete real inner-product space, continuous on the window `[a,b]` (`a ≤ b`),
the squared norm of the Bochner interval integral is bounded by the window length times the
integral of the squared norm:

  `‖∫_a^b f s ds‖² ≤ (b − a) · ∫_a^b ‖f s‖² ds`.

This is the analytic core of the Steklov/Jensen averaging estimate: dividing by `(b−a)²` turns
it into `‖⨍_a^b f‖² ≤ ⨍_a^b ‖f‖²` (Jensen for the convex map `‖·‖²` under the normalized window
measure). It is `Lp`-frontier-free — the proof is the triangle inequality
`‖∫ f‖ ≤ ∫ ‖f‖` (`intervalIntegral.norm_integral_le_integral_norm`) followed by the scalar
Cauchy–Schwarz / Hölder `(∫_a^b ‖f‖·1)² ≤ (∫_a^b ‖f‖²)(∫_a^b 1²)`
(`MeasureTheory.integral_mul_norm_le_Lp_mul_Lq`, `p = q = 2`). -/
private theorem norm_integral_sq_le_length_mul_integral_normSq
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {f : ℝ → H} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.uIcc a b)) :
    ‖∫ s in a..b, f s‖ ^ 2 ≤ (b - a) * ∫ s in a..b, ‖f s‖ ^ 2 := by
  -- `f` is interval-integrable, and so are `‖f·‖` and `‖f·‖²` (continuity on the compact window).
  have hfint : IntervalIntegrable f volume a b := (hf).intervalIntegrable
  have hnorm_cont : ContinuousOn (fun s => ‖f s‖) (Set.uIcc a b) := hf.norm
  -- Step 1 (triangle): `‖∫ f‖ ≤ ∫_a^b ‖f s‖`.
  have hstep1 : ‖∫ s in a..b, f s‖ ≤ ∫ s in a..b, ‖f s‖ :=
    intervalIntegral.norm_integral_le_integral_norm hab
  have hnorm_nonneg_int : 0 ≤ ∫ s in a..b, ‖f s‖ :=
    intervalIntegral.integral_nonneg hab fun s _ => norm_nonneg _
  -- Step 2 (Cauchy–Schwarz / Hölder, `p = q = 2`): `(∫_a^b ‖f‖)² ≤ (∫_a^b ‖f‖²)(b − a)`.
  -- Move to the set integral over `Ioc a b` with the restricted (finite) measure.
  set μ : Measure ℝ := volume.restrict (Set.Ioc a b) with hμ
  haveI : IsFiniteMeasure μ := by
    rw [hμ]; refine isFiniteMeasure_restrict.2 ?_
    rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
  -- `MemLp` of the scalar `‖f·‖` and of the constant `1` at exponent `2` on the finite window.
  have hfnorm_meas : AEStronglyMeasurable (fun s => ‖f s‖) μ := by
    rw [hμ]
    exact (hnorm_cont.mono (by rw [Set.uIcc_of_le hab]; exact Set.Ioc_subset_Icc_self))
      |>.aestronglyMeasurable measurableSet_Ioc
  have hbdd : ∃ C, ∀ s ∈ Set.Ioc a b, ‖f s‖ ≤ C := by
    have hcompact : IsCompact (Set.uIcc a b) := isCompact_uIcc
    obtain ⟨C, hC⟩ := (hcompact.image_of_continuousOn hnorm_cont).bddAbove
    refine ⟨C, fun s hs => ?_⟩
    exact hC ⟨s, by rw [Set.uIcc_of_le hab]; exact Set.Ioc_subset_Icc_self hs, rfl⟩
  obtain ⟨C, hC⟩ := hbdd
  have hfnorm_memLp : MemLp (fun s => ‖f s‖) (ENNReal.ofReal (2 : ℝ)) μ := by
    rw [ENNReal.ofReal_ofNat]
    refine MemLp.of_bound hfnorm_meas (max C 0) ?_
    rw [hμ]; refine ae_restrict_of_forall_mem measurableSet_Ioc fun s hs => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact le_trans (hC s hs) (le_max_left _ _)
  have hone_memLp : MemLp (fun _ : ℝ => (1 : ℝ)) (ENNReal.ofReal (2 : ℝ)) μ := by
    rw [ENNReal.ofReal_ofNat]; exact memLp_const 1
  -- Apply the Bochner Hölder inequality with `p = q = 2` to `‖f·‖` and the constant `1`.
  have hpq : (2 : ℝ).HolderConjugate 2 := Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hholder := MeasureTheory.integral_mul_norm_le_Lp_mul_Lq
    (μ := μ) (p := 2) (q := 2) (f := fun s => ‖f s‖) (g := fun _ : ℝ => (1 : ℝ))
    hpq hfnorm_memLp hone_memLp
  -- Simplify the Hölder bound: `∫ ‖f‖·‖1‖ = ∫ ‖f‖`, and `‖1‖^(2:ℝ) = 1`.
  simp only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), abs_one, mul_one,
    Real.one_rpow, one_pow, Real.rpow_two] at hholder
  -- Rewrite the set integrals over `μ` as interval integrals (`μ = volume.restrict (Ioc a b)`).
  have hμ_to_interval : ∀ g : ℝ → ℝ, ∫ s, g s ∂μ = ∫ s in a..b, g s := by
    intro g
    rw [hμ, intervalIntegral.integral_of_le hab]
  have hμ_const : ∫ _s : ℝ, (1 : ℝ) ∂μ = b - a := by
    rw [hμ_to_interval]; simp [intervalIntegral.integral_const]
  -- `hholder : ∫_a^b ‖f‖ ≤ (∫ ‖f‖² ∂μ)^(1/2) · (∫ 1 ∂μ)^(1/2)`.
  rw [hμ_const, hμ_to_interval (fun s => ‖f s‖), hμ_to_interval (fun s => ‖f s‖ ^ 2)] at hholder
  -- `hholder : ∫_a^b ‖f‖ ≤ (∫_a^b ‖f‖²)^(1/2) · (b−a)^(1/2)`.
  -- Square and clear the rpows to get the Cauchy–Schwarz bound, then chain with Step 1.
  have hI2_nonneg : 0 ≤ ∫ s in a..b, ‖f s‖ ^ 2 :=
    intervalIntegral.integral_nonneg hab fun s _ => sq_nonneg _
  have hba_nonneg : 0 ≤ b - a := sub_nonneg.mpr hab
  have hcs : (∫ s in a..b, ‖f s‖) ^ 2 ≤ (b - a) * ∫ s in a..b, ‖f s‖ ^ 2 := by
    have hsq := mul_self_le_mul_self hnorm_nonneg_int hholder
    calc (∫ s in a..b, ‖f s‖) ^ 2
        = (∫ s in a..b, ‖f s‖) * (∫ s in a..b, ‖f s‖) := by rw [sq]
      _ ≤ ((∫ s in a..b, ‖f s‖ ^ 2) ^ (1 / 2 : ℝ) * (b - a) ^ (1 / 2 : ℝ))
            * ((∫ s in a..b, ‖f s‖ ^ 2) ^ (1 / 2 : ℝ) * (b - a) ^ (1 / 2 : ℝ)) := hsq
      _ = (b - a) * ∫ s in a..b, ‖f s‖ ^ 2 := by
          rw [show ((∫ s in a..b, ‖f s‖ ^ 2) ^ (1 / 2 : ℝ) * (b - a) ^ (1 / 2 : ℝ))
                * ((∫ s in a..b, ‖f s‖ ^ 2) ^ (1 / 2 : ℝ) * (b - a) ^ (1 / 2 : ℝ))
              = ((∫ s in a..b, ‖f s‖ ^ 2) ^ (1 / 2 : ℝ)) ^ (2 : ℕ)
                  * ((b - a) ^ (1 / 2 : ℝ)) ^ (2 : ℕ) by ring]
          rw [← Real.rpow_natCast ((∫ s in a..b, ‖f s‖ ^ 2) ^ (1 / 2 : ℝ)) 2,
            ← Real.rpow_natCast ((b - a) ^ (1 / 2 : ℝ)) 2,
            ← Real.rpow_mul hI2_nonneg, ← Real.rpow_mul hba_nonneg]
          norm_num
          rw [mul_comm]
  -- Chain: `‖∫ f‖² ≤ (∫ ‖f‖)² ≤ (b−a) ∫ ‖f‖²`.
  calc ‖∫ s in a..b, f s‖ ^ 2
      ≤ (∫ s in a..b, ‖f s‖) ^ 2 := by
        apply pow_le_pow_left₀ (norm_nonneg _) hstep1
    _ ≤ (b - a) * ∫ s in a..b, ‖f s‖ ^ 2 := hcs

/-- **Steklov interval-average of a Galerkin curve.** For mesh `δ` and base time `t`,
`steklovAvg gs δ t := δ⁻¹ • ∫_{t}^{t+δ} (gs.u s : L2VF_R3) ds` (Bochner interval integral
in `L2VF_R3`). For `δ > 0` this is the average of the curve over `[t, t+δ]`. -/
private noncomputable def steklovAvg (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (u₀ : L2Sigma_R3) (n : ℕ)
    (gs : GalerkinSolutionData_R3 𝔊 F ν u₀ n) (δ t : ℝ) : L2VF_R3 :=
  δ⁻¹ • ∫ s in t..(t + δ), (gs.u s : L2VF_R3)

/-- **Backward Steklov interval-average** over `[t−δ, t]`: `δ⁻¹ • ∫_{t−δ}^{t} (gs.u s) ds`.
This is the boundary-strip companion of `steklovAvg`: for `t` near `T` the forward window
`[t, t+δ]` exits `[0,T]`, but the backward window `[t−δ, t]` stays inside `[0,T]` whenever
`δ ≤ t ≤ T`, so the time modulus controls it.  Definitionally `steklovAvgBack δ t = steklovAvg δ (t−δ)`
(the forward average based at `t−δ`), which lets every forward lemma transfer by a base-point shift. -/
private noncomputable def steklovAvgBack (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (u₀ : L2Sigma_R3) (n : ℕ)
    (gs : GalerkinSolutionData_R3 𝔊 F ν u₀ n) (δ t : ℝ) : L2VF_R3 :=
  δ⁻¹ • ∫ s in (t - δ)..t, (gs.u s : L2VF_R3)

/-- The backward average is the forward average based at `t − δ`. -/
private theorem steklovAvgBack_eq (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (u₀ : L2Sigma_R3) (n : ℕ)
    (gs : GalerkinSolutionData_R3 𝔊 F ν u₀ n) (δ t : ℝ) :
    steklovAvgBack 𝔊 F ν u₀ n gs δ t = steklovAvg 𝔊 F ν u₀ n gs δ (t - δ) := by
  rw [steklovAvgBack, steklovAvg]
  rw [show t - δ + δ = t by ring]

/-- **L² uniform bound on the Steklov average.** For `0 < δ` and `0 ≤ t`, the averaged
state is bounded by `‖u₀‖`, uniformly in `n` and `t`.  This is the average of a curve all
of whose values satisfy `‖(gs.u s)‖ ≤ ‖u₀‖` (via `galerkin_norm_le_u0`). -/
private theorem steklovAvg_norm_le_u0 (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (u₀ : L2Sigma_R3) (n : ℕ)
    (gs : GalerkinSolutionData_R3 𝔊 F ν u₀ n) {δ t : ℝ} (hδ : 0 < δ) (ht : 0 ≤ t) :
    ‖steklovAvg 𝔊 F ν u₀ n gs δ t‖ ≤ ‖(u₀ : L2VF_R3)‖ := by
  -- Bound the integral by `δ · ‖u₀‖` using the pointwise norm bound, then divide by δ.
  have hle : t ≤ t + δ := by linarith
  -- pointwise bound on `Ι t (t+δ)`: every `s` there is `≥ t ≥ 0`, so `galerkin_norm_le_u0`.
  have hbd : ‖∫ s in t..(t + δ), (gs.u s : L2VF_R3)‖ ≤ ‖(u₀ : L2VF_R3)‖ * δ := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := t) (b := t + δ) (C := ‖(u₀ : L2VF_R3)‖)
      (f := fun s => (gs.u s : L2VF_R3)) ?_
    · -- `|(t+δ) - t| = δ`
      have hsub : |(t + δ) - t| = δ := by rw [show (t + δ) - t = δ by ring, abs_of_pos hδ]
      rwa [hsub] at this
    · intro s hs
      -- `s ∈ Ι t (t+δ)` ⊆ `[t, t+δ]`, so `s ≥ t ≥ 0`.
      have hs' : s ∈ Set.uIoc t (t + δ) := hs
      rw [Set.uIoc_of_le hle] at hs'
      exact galerkin_norm_le_u0 𝔊 F ν u₀ n gs (le_trans ht (le_of_lt hs'.1))
  -- combine
  rw [steklovAvg, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hδ]
  rw [inv_mul_le_iff₀ hδ]
  calc ‖∫ s in t..(t + δ), (gs.u s : L2VF_R3)‖
      ≤ ‖(u₀ : L2VF_R3)‖ * δ := hbd
    _ = δ * ‖(u₀ : L2VF_R3)‖ := mul_comm _ _

/-- **The Steklov average stays in the Galerkin subspace** `Vₙ = range (𝔊.P n)`.  Because every
sample `gs.u s` is a fixed point of `𝔊.P n` (`u_inVn`) and `𝔊.P n` (a CLM) commutes with the
Bochner integral. -/
private theorem steklovAvg_inVn (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (u₀ : L2Sigma_R3) (n : ℕ)
    (gs : GalerkinSolutionData_R3 𝔊 F ν u₀ n) {δ t : ℝ} (hδ : 0 < δ) (ht : 0 ≤ t) :
    (steklovAvg 𝔊 F ν u₀ n gs δ t : L2VF_R3)
      = 𝔊.P n (steklovAvg 𝔊 F ν u₀ n gs δ t : L2VF_R3) := by
  have hle : t ≤ t + δ := by linarith
  have hcont : ContinuousOn (fun s => (gs.u s : L2VF_R3)) (Set.uIcc t (t + δ)) := by
    refine (galerkin_curve_continuous 𝔊 F ν u₀ n gs).mono ?_
    rw [Set.uIcc_of_le hle]; intro s hs; exact le_trans ht hs.1
  have hint : IntervalIntegrable (fun s => (gs.u s : L2VF_R3)) volume t (t + δ) :=
    hcont.intervalIntegrable
  rw [steklovAvg, map_smul]
  congr 1
  -- `𝔊.P n (∫_s u s) = ∫_s 𝔊.P n (u s) = ∫_s (u s)` (using `u_inVn`, reversed).
  rw [← ContinuousLinearMap.intervalIntegral_comp_comm _ hint]
  refine intervalIntegral.integral_congr (fun s _ => ?_)
  exact gs.u_inVn s

/-- **The Steklov average is divergence-free** (`∈ L2Sigma_R3`).  The integrand `s ↦ gs.u s` is
valued in the closed subspace `L2Sigma_R3`, which therefore contains the (scaled) Bochner integral:
`steklovAvg = (L2Sigma_R3).subtypeL (δ⁻¹ • ∫_s gs.u s)`. -/
private theorem steklovAvg_mem_sigma (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (u₀ : L2Sigma_R3) (n : ℕ)
    (gs : GalerkinSolutionData_R3 𝔊 F ν u₀ n) {δ t : ℝ} (hδ : 0 < δ) (ht : 0 ≤ t) :
    (steklovAvg 𝔊 F ν u₀ n gs δ t : L2VF_R3) ∈ L2Sigma_R3 := by
  have hle : t ≤ t + δ := by linarith
  -- continuity of the L2Sigma-valued curve `s ↦ gs.u s` on the window
  have hcontσ : ContinuousOn (fun s => gs.u s) (Set.uIcc t (t + δ)) := by
    rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
    refine (galerkin_curve_continuous 𝔊 F ν u₀ n gs).mono ?_
    rw [Set.uIcc_of_le hle]; intro s hs; exact le_trans ht hs.1
  have hintσ : IntervalIntegrable (fun s => gs.u s) volume t (t + δ) :=
    hcontσ.intervalIntegrable
  -- `steklovAvg = subtypeL (δ⁻¹ • ∫ gs.u s)`, hence in `L2Sigma_R3 = range subtypeL`.
  have hpush : (steklovAvg 𝔊 F ν u₀ n gs δ t : L2VF_R3)
      = (L2Sigma_R3.subtypeL) (δ⁻¹ • ∫ s in t..(t + δ), gs.u s) := by
    rw [steklovAvg, map_smul]
    congr 1
    rw [← ContinuousLinearMap.intervalIntegral_comp_comm _ hintσ]
    rfl
  rw [hpush]
  exact (δ⁻¹ • ∫ s in t..(t + δ), gs.u s).2

/-- **H¹ regularity of the Steklov average.**  The averaged state is in `H¹`, since it stays in the
Schwartz Galerkin subspace `Vₙ` (`steklovAvg_inVn`). -/
private theorem steklovAvg_memH1 (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (u₀ : L2Sigma_R3) (n : ℕ)
    (gs : GalerkinSolutionData_R3 𝔊 F ν u₀ n) {δ t : ℝ} (hδ : 0 < δ) (ht : 0 ≤ t) :
    memH1VF_R3 (steklovAvg 𝔊 F ν u₀ n gs δ t : L2VF_R3) :=
  galerkinCurve_reg_mem 𝔊 n _ (steklovAvg_inVn 𝔊 F ν u₀ n gs hδ ht)

/-- L² uniform bound on the **backward** Steklov average (window `[t−δ,t] ⊆ Ici 0` when `δ ≤ t`). -/
private theorem steklovAvgBack_norm_le_u0 (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (u₀ : L2Sigma_R3) (n : ℕ)
    (gs : GalerkinSolutionData_R3 𝔊 F ν u₀ n) {δ t : ℝ} (hδ : 0 < δ) (hδt : δ ≤ t) :
    ‖steklovAvgBack 𝔊 F ν u₀ n gs δ t‖ ≤ ‖(u₀ : L2VF_R3)‖ := by
  rw [steklovAvgBack_eq]
  exact steklovAvg_norm_le_u0 𝔊 F ν u₀ n gs hδ (by linarith)

/-- H¹ regularity of the **backward** Steklov average (window `[t−δ,t] ⊆ Ici 0` when `δ ≤ t`). -/
private theorem steklovAvgBack_memH1 (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (u₀ : L2Sigma_R3) (n : ℕ)
    (gs : GalerkinSolutionData_R3 𝔊 F ν u₀ n) {δ t : ℝ} (hδ : 0 < δ) (hδt : δ ≤ t) :
    memH1VF_R3 (steklovAvgBack 𝔊 F ν u₀ n gs δ t : L2VF_R3) := by
  rw [steklovAvgBack_eq]
  exact steklovAvg_memH1 𝔊 F ν u₀ n gs hδ (by linarith)

/-- **Steklov average approximates the original curve.** If, on the window
`[t, t+δ]`, the curve varies by less than `ε` in L², then
`‖(gs.u t) − steklovAvg δ t‖ ≤ ε`.  This is the key step-3 estimate of the Steklov route.

The window-variation hypothesis `hmod` is the *intended consumer* of
`Htime.uniform_time_modulus`, but ONLY when the whole window stays in `[0,T]`: that modulus
controls pairs with both times in `[0,T]`, so it supplies `hmod` uniformly in `n,t` exactly for
`t, t+δ ∈ [0,T]` (i.e. `t ≤ T-δ`). For `t` in the boundary strip `(T-δ, T]` the forward window
exits `[0,T]` and the modulus does NOT supply `hmod`; that strip needs separate handling (see the
C2 route TODO). This lemma itself only requires `hmod` on `uIoc t (t+δ)` and is agnostic to its
source. -/
private theorem steklovAvg_approx (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (u₀ : L2Sigma_R3) (n : ℕ)
    (gs : GalerkinSolutionData_R3 𝔊 F ν u₀ n) {δ t ε : ℝ} (hδ : 0 < δ) (ht : 0 ≤ t)
    (hmod : ∀ s ∈ Set.uIoc t (t + δ), ‖(gs.u t : L2VF_R3) - (gs.u s : L2VF_R3)‖ ≤ ε) :
    ‖(gs.u t : L2VF_R3) - steklovAvg 𝔊 F ν u₀ n gs δ t‖ ≤ ε := by
  have hle : t ≤ t + δ := by linarith
  -- forward continuity of the curve on `Ici 0` ⊇ the window `[t, t+δ]` (since `0 ≤ t`)
  have hcont : ContinuousOn (fun s => (gs.u s : L2VF_R3)) (Set.Ici 0) :=
    galerkin_curve_continuous 𝔊 F ν u₀ n gs
  have hwin : Set.uIcc t (t + δ) ⊆ Set.Ici (0 : ℝ) := by
    rw [Set.uIcc_of_le hle]
    intro s hs; exact le_trans ht hs.1
  have hint : IntervalIntegrable (fun s => (gs.u s : L2VF_R3)) volume t (t + δ) :=
    (hcont.mono hwin).intervalIntegrable
  -- write `gs.u t = δ⁻¹ • ∫ (gs.u t)` (constant integral), then subtract under the integral.
  have hconst : (gs.u t : L2VF_R3) = δ⁻¹ • ∫ _s in t..(t + δ), (gs.u t : L2VF_R3) := by
    rw [intervalIntegral.integral_const, smul_smul]
    rw [show (t + δ) - t = δ by ring, inv_mul_cancel₀ (ne_of_gt hδ), one_smul]
  rw [hconst, steklovAvg, ← smul_sub,
    ← intervalIntegral.integral_sub (intervalIntegrable_const) hint]
  rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hδ, inv_mul_le_iff₀ hδ]
  calc ‖∫ s in t..(t + δ), ((gs.u t : L2VF_R3) - (gs.u s : L2VF_R3))‖
      ≤ ε * |(t + δ) - t| := by
        refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
        intro s hs; exact hmod s hs
    _ = ε * δ := by rw [show (t + δ) - t = δ by ring, abs_of_pos hδ]
    _ = δ * ε := by ring

/-- **Backward Steklov average approximates the original curve at the right endpoint.** If, on the
backward window `[t−δ, t]`, the curve varies from its value at `t` by less than `ε`, then
`‖(gs.u t) − steklovAvgBack δ t‖ ≤ ε`.  Boundary-strip companion of `steklovAvg_approx`; the window
`[t−δ,t]` stays in `[0,T]` for `δ ≤ t ≤ T`, so the time modulus supplies `hmod`. -/
private theorem steklovAvgBack_approx (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (u₀ : L2Sigma_R3) (n : ℕ)
    (gs : GalerkinSolutionData_R3 𝔊 F ν u₀ n) {δ t ε : ℝ} (hδ : 0 < δ) (hδt : δ ≤ t)
    (hmod : ∀ s ∈ Set.uIoc (t - δ) t, ‖(gs.u t : L2VF_R3) - (gs.u s : L2VF_R3)‖ ≤ ε) :
    ‖(gs.u t : L2VF_R3) - steklovAvgBack 𝔊 F ν u₀ n gs δ t‖ ≤ ε := by
  have hle : t - δ ≤ t := by linarith
  have ht0 : (0 : ℝ) ≤ t - δ := by linarith
  have hcont : ContinuousOn (fun s => (gs.u s : L2VF_R3)) (Set.Ici 0) :=
    galerkin_curve_continuous 𝔊 F ν u₀ n gs
  have hwin : Set.uIcc (t - δ) t ⊆ Set.Ici (0 : ℝ) := by
    rw [Set.uIcc_of_le hle]; intro s hs; exact le_trans ht0 hs.1
  have hint : IntervalIntegrable (fun s => (gs.u s : L2VF_R3)) volume (t - δ) t :=
    (hcont.mono hwin).intervalIntegrable
  have hconst : (gs.u t : L2VF_R3) = δ⁻¹ • ∫ _s in (t - δ)..t, (gs.u t : L2VF_R3) := by
    rw [intervalIntegral.integral_const, smul_smul]
    rw [show t - (t - δ) = δ by ring, inv_mul_cancel₀ (ne_of_gt hδ), one_smul]
  rw [hconst, steklovAvgBack, ← smul_sub,
    ← intervalIntegral.integral_sub (intervalIntegrable_const) hint]
  rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hδ, inv_mul_le_iff₀ hδ]
  calc ‖∫ s in (t - δ)..t, ((gs.u t : L2VF_R3) - (gs.u s : L2VF_R3))‖
      ≤ ε * |t - (t - δ)| := by
        refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
        intro s hs; exact hmod s hs
    _ = ε * δ := by rw [show t - (t - δ) = δ by ring, abs_of_pos hδ]
    _ = δ * ε := by ring

/-- **Clamped Steklov average on `[0,T]`.**  Forward average `steklovAvg δ t` for `t ≤ T − δ`
(forward window `[t,t+δ] ⊆ [0,T]`), backward average `steklovAvgBack δ t` for `t > T − δ` (backward
window `[t−δ,t] ⊆ [0,T]`, valid when `2δ ≤ T`).  This covers the whole interval `[0,T]` with windows
that stay inside `[0,T]`, so the time modulus controls the raw↔avg error uniformly in `n` and `t`. -/
private noncomputable def clampedAvg (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (u₀ : L2Sigma_R3) (n : ℕ)
    (gs : GalerkinSolutionData_R3 𝔊 F ν u₀ n) (δ T t : ℝ) : L2VF_R3 :=
  if t ≤ T - δ then steklovAvg 𝔊 F ν u₀ n gs δ t
  else steklovAvgBack 𝔊 F ν u₀ n gs δ t

/-- **Uniform raw↔clamped-average approximation on `[0,T]`.**  If the `n`-uniform time modulus gives
`‖(gs.u s) − (gs.u s')‖ < ε` for `|s − s'| < δ` with both in `[0,T]`, then
`‖(gs.u t) − clampedAvg δ T t‖ ≤ ε` for every `t ∈ [0,T]` — uniformly in `n` (the hypothesis is the
modulus instance for this `gs`).  Requires `2δ ≤ T` so the backward window on `(T−δ,T]` stays in
`[0,T]`. -/
private theorem clampedAvg_approx (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (u₀ : L2Sigma_R3) (n : ℕ)
    (gs : GalerkinSolutionData_R3 𝔊 F ν u₀ n) {δ T t ε : ℝ} (hδ : 0 < δ) (hδT : 2 * δ ≤ T)
    (ht : t ∈ Set.Icc (0 : ℝ) T)
    (hmod : ∀ s s' : ℝ, s ∈ Set.Icc (0 : ℝ) T → s' ∈ Set.Icc (0 : ℝ) T → |s - s'| ≤ δ →
      ‖((gs.u s) : L2VF_R3) - ((gs.u s') : L2VF_R3)‖ ≤ ε) :
    ‖(gs.u t : L2VF_R3) - clampedAvg 𝔊 F ν u₀ n gs δ T t‖ ≤ ε := by
  obtain ⟨ht0, htT⟩ := ht
  rw [clampedAvg]
  by_cases hcase : t ≤ T - δ
  · -- forward branch: window `[t, t+δ] ⊆ [0,T]`
    rw [if_pos hcase]
    refine steklovAvg_approx 𝔊 F ν u₀ n gs hδ ht0 (fun s hs => ?_)
    rw [Set.uIoc_of_le (by linarith : t ≤ t + δ)] at hs
    have hsIcc : s ∈ Set.Icc (0 : ℝ) T := ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have htIcc : t ∈ Set.Icc (0 : ℝ) T := ⟨ht0, htT⟩
    have habs : |t - s| ≤ δ := by
      rw [abs_sub_comm, abs_of_pos (by linarith [hs.1] : (0:ℝ) < s - t)]; linarith [hs.2]
    exact hmod t s htIcc hsIcc habs
  · -- backward branch: window `[t−δ, t] ⊆ [0,T]` (since `t > T−δ ≥ δ` as `2δ ≤ T`)
    rw [if_neg hcase]
    have hδt : δ ≤ t := by push_neg at hcase; linarith
    refine steklovAvgBack_approx 𝔊 F ν u₀ n gs hδ hδt (fun s hs => ?_)
    rw [Set.uIoc_of_le (by linarith : t - δ ≤ t)] at hs
    have hsIcc : s ∈ Set.Icc (0 : ℝ) T := ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have htIcc : t ∈ Set.Icc (0 : ℝ) T := ⟨ht0, htT⟩
    have habs : |t - s| ≤ δ := by
      rw [abs_of_nonneg (by linarith [hs.2] : (0:ℝ) ≤ t - s)]; linarith [hs.1]
    exact hmod t s htIcc hsIcc habs

/-- **eLpNorm raw↔clamped-average bound on `[0,T]`.**  The time-`L²` `eLpNorm` of the
ball-restricted raw↔clamped-average difference over `[0,T]` is controlled by the uniform pointwise
modulus bound `ε` times `√T`: since `restrictToBall R` is `1`-Lipschitz, the pointwise difference is
`≤ ‖u_t − clampedAvg δ T t‖ ≤ ε` (`clampedAvg_approx`), and `eLpNorm` of an `ε`-bounded function over
the finite window `[0,T]` is `≤ ε · T^{1/2}`.  This is the raw↔avg term of the C2 `ε/3` split. -/
private theorem eLpNorm_raw_sub_clampedAvg_le (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (u₀ : L2Sigma_R3) (n : ℕ)
    (gs : GalerkinSolutionData_R3 𝔊 F ν u₀ n) {δ T ε : ℝ} (R : ℝ) (hδ : 0 < δ) (hδT : 2 * δ ≤ T)
    (hε : 0 ≤ ε)
    (hmod : ∀ s s' : ℝ, s ∈ Set.Icc (0 : ℝ) T → s' ∈ Set.Icc (0 : ℝ) T → |s - s'| ≤ δ →
      ‖((gs.u s) : L2VF_R3) - ((gs.u s') : L2VF_R3)‖ ≤ ε) :
    MeasureTheory.eLpNorm
        (fun t => restrictToBall R (gs.u t : L2VF_R3)
          - restrictToBall R (clampedAvg 𝔊 F ν u₀ n gs δ T t))
        2 (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T))
      ≤ ENNReal.ofReal T ^ (2 : ENNReal).toReal⁻¹ * ENNReal.ofReal ε := by
  -- pointwise `‖·‖ ≤ ε` on `[0,T]` via 1-Lipschitz `restrictToBall` + `clampedAvg_approx`
  have hbound : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)),
      ‖restrictToBall R (gs.u t : L2VF_R3)
          - restrictToBall R (clampedAvg 𝔊 F ν u₀ n gs δ T t)‖ ≤ ε := by
    refine (ae_restrict_iff' measurableSet_Icc).mpr (ae_of_all _ (fun t ht => ?_))
    have hlip : ‖restrictToBall R (gs.u t : L2VF_R3)
        - restrictToBall R (clampedAvg 𝔊 F ν u₀ n gs δ T t)‖
        ≤ ‖(gs.u t : L2VF_R3) - clampedAvg 𝔊 F ν u₀ n gs δ T t‖ := by
      rw [← dist_eq_norm, ← dist_eq_norm]
      exact restrictToBall_dist_le R _ _
    exact le_trans hlip (clampedAvg_approx 𝔊 F ν u₀ n gs hδ hδT ht hmod)
  -- `eLpNorm` of an `ε`-bounded function: `≤ ofReal ε · μ(univ)^(1/p)`, `μ(univ) = ofReal T`.
  refine le_trans (eLpNorm_le_of_ae_bound hbound) ?_
  rw [Measure.restrict_apply_univ, Real.volume_Icc, sub_zero]

/-- **L² Jensen bound on the Steklov average (squared-norm form).** For `0 < δ` and `0 ≤ t`,
the squared L² norm of the Steklov average is bounded by the average of the squared norms over
the forward window:

  `‖steklovAvg gs δ t‖² ≤ δ⁻¹ · ∫_{t}^{t+δ} ‖(gs.u s)‖² ds`.

This is the kinetic (`H = L²`) instance of the Hilbert-space Bochner-average Jensen lemma
`norm_integral_sq_le_length_mul_integral_normSq`, applied to the continuous Galerkin curve on
the window `[t, t+δ] ⊆ Ici 0`. It is `Lp`-frontier-free.

This is the template the still-open viscous/H¹ Jensen bound instantiates at the Fourier level
(modulo the pointwise `Lp`-valued Bochner-integral coeFn interchange — the genuine missing
mathlib pillar, isolated in this repo as `convL2_coeFn_ae`). -/
private theorem steklovAvg_normSq_le_average (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (u₀ : L2Sigma_R3) (n : ℕ)
    (gs : GalerkinSolutionData_R3 𝔊 F ν u₀ n) {δ t : ℝ} (hδ : 0 < δ) (ht : 0 ≤ t) :
    ‖steklovAvg 𝔊 F ν u₀ n gs δ t‖ ^ 2
      ≤ δ⁻¹ * ∫ s in t..(t + δ), ‖((gs.u s : L2VF_R3))‖ ^ 2 := by
  have hle : t ≤ t + δ := by linarith
  -- continuity of the curve on the window `[t, t+δ] ⊆ Ici 0`
  have hcont : ContinuousOn (fun s => (gs.u s : L2VF_R3)) (Set.uIcc t (t + δ)) := by
    refine (galerkin_curve_continuous 𝔊 F ν u₀ n gs).mono ?_
    rw [Set.uIcc_of_le hle]; intro s hs; exact le_trans ht hs.1
  -- the Hilbert-space Bochner-average Jensen lemma on `[t, t+δ]` (window length `δ`)
  have hjensen := norm_integral_sq_le_length_mul_integral_normSq (f := fun s => (gs.u s : L2VF_R3))
    hle hcont
  rw [show (t + δ) - t = δ by ring] at hjensen
  -- `‖δ⁻¹ • ∫‖² = δ⁻² · ‖∫‖²`, then use the Jensen bound `‖∫‖² ≤ δ · ∫ ‖u s‖²`.
  rw [steklovAvg, norm_smul, mul_pow, norm_inv, Real.norm_eq_abs, abs_of_pos hδ]
  calc (δ⁻¹) ^ 2 * ‖∫ s in t..(t + δ), (gs.u s : L2VF_R3)‖ ^ 2
      ≤ (δ⁻¹) ^ 2 * (δ * ∫ s in t..(t + δ), ‖(gs.u s : L2VF_R3)‖ ^ 2) := by
        apply mul_le_mul_of_nonneg_left hjensen (by positivity)
    _ = δ⁻¹ * ∫ s in t..(t + δ), ‖(gs.u s : L2VF_R3)‖ ^ 2 := by
        rw [← mul_assoc]
        congr 1
        field_simp

/-- **Continuity of the `j`-th Fourier-component curve.** `s ↦ 𝓕 (proj_j (gs.u s))` is continuous
on `Ici 0` (composition of the continuous Galerkin curve with the continuous-linear `proj_j` and
the isometry `𝓕`). -/
private theorem fourierProjCurve_continuousOn (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (u₀ : L2Sigma_R3) (n : ℕ)
    (gs : GalerkinSolutionData_R3 𝔊 F ν u₀ n) (j : Fin 3) :
    ContinuousOn (fun s => (𝓕 (L2VF_projComponentC_R3 j (gs.u s)) : L2C_R3)) (Set.Ici 0) := by
  have hcurve : ContinuousOn (fun s => (gs.u s : L2VF_R3)) (Set.Ici 0) :=
    galerkin_curve_continuous 𝔊 F ν u₀ n gs
  -- `𝓕 ∘ proj_j` is continuous (CLM composed with the Fourier isometry).
  have hmap : Continuous (fun w : L2VF_R3 => (𝓕 (L2VF_projComponentC_R3 j w) : L2C_R3)) :=
    (Lp.fourierTransformₗᵢ Domain3 ℂ).continuous.comp (L2VF_projComponentC_R3 j).continuous
  exact hmap.comp_continuousOn hcurve

/-- **Fourier component of a Steklov average — the L²-element commute (PROVED, no `sorry`).**
For `0 < δ` and `0 ≤ t`, the `j`-th Fourier component of the Steklov average is the time-average
of the curve's `j`-th Fourier components:

  `𝓕 (proj_j (steklovAvg gs δ t)) = δ⁻¹ • ∫_{t}^{t+δ} 𝓕 (proj_j (gs.u s)) ds`   (in `L2C_R3`).

This is the `Lp`-element identity underlying the spectral Jensen bound: the scalar `δ⁻¹` factors
out of `𝓕 ∘ proj_j` (both `ℝ`-linear), and the continuous-linear maps `proj_j` and `𝓕` commute
with the (interval) Bochner integral of the continuous curve via
`ContinuousLinearMap.integral_comp_comm` / `LinearIsometryEquiv.integral_comp_comm`. It is
`Lp`-frontier-free; the genuine missing pillar is only the subsequent *pointwise coeFn* interchange
(see `viscousFormSq_steklovAvg_le_average`). -/
private theorem fourier_proj_steklovAvg_eq (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (u₀ : L2Sigma_R3) (n : ℕ)
    (gs : GalerkinSolutionData_R3 𝔊 F ν u₀ n) {δ t : ℝ} (hδ : 0 < δ) (ht : 0 ≤ t) (j : Fin 3) :
    (𝓕 (L2VF_projComponentC_R3 j (steklovAvg 𝔊 F ν u₀ n gs δ t)) : L2C_R3)
      = δ⁻¹ • ∫ s in t..(t + δ),
          (𝓕 (L2VF_projComponentC_R3 j (gs.u s)) : L2C_R3) := by
  have hle : t ≤ t + δ := by linarith
  -- The curve `s ↦ (gs.u s : L2VF_R3)` is continuous on `[t, t+δ] ⊆ Ici 0`, hence interval-integrable.
  have hcont : ContinuousOn (fun s => (gs.u s : L2VF_R3)) (Set.uIcc t (t + δ)) := by
    refine (galerkin_curve_continuous 𝔊 F ν u₀ n gs).mono ?_
    rw [Set.uIcc_of_le hle]; intro s hs; exact le_trans ht hs.1
  have hint : IntervalIntegrable (fun s => (gs.u s : L2VF_R3)) volume t (t + δ) :=
    hcont.intervalIntegrable
  -- Convert the interval integral to a set integral on `Ioc t (t+δ)` (since `t ≤ t+δ`).
  have hInt_proj : IntegrableOn (fun s => (gs.u s : L2VF_R3)) (Set.Ioc t (t + δ)) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).mp hint
  -- `proj_j` (a CLM) commutes with the Bochner integral.
  rw [steklovAvg, map_smul, intervalIntegral.integral_of_le hle, intervalIntegral.integral_of_le hle,
    ← ContinuousLinearMap.integral_comp_comm _ hInt_proj]
  -- Convert the real scalar `δ⁻¹` to the complex scalar `(δ⁻¹ : ℂ)` (both sides), so the
  -- ℂ-homogeneity `fourier_smul` applies.
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.real_smul_eq_coe_smul (K := ℂ),
    FourierTransform.fourier_smul]
  congr 1
  -- `𝓕 (∫ s, proj_j (gs.u s)) = ∫ s, 𝓕 (proj_j (gs.u s))` via the `ₗᵢ` commute lemma.
  exact ((Lp.fourierTransformₗᵢ Domain3 ℂ).toLinearIsometry.integral_comp_comm
    (μ := (volume : Measure ℝ).restrict (Set.Ioc t (t + δ)))
    (fun s => (L2VF_projComponentC_R3 j (gs.u s) : L2C_R3))).symm

/-- **Per-truncation weighted Jensen bound.** For a bounded multiplier `m` (`MemLp ⊤`) and a curve
`G` continuous on `[t,t+δ]`, the squared weighted norm of the Steklov-averaged Fourier component is
bounded by the time-average of the squared weighted norms:

  `‖mulBdd m (δ⁻¹ • ∫_{t}^{t+δ} G s)‖² ≤ δ⁻¹ · ∫_{t}^{t+δ} ‖mulBdd m (G s)‖²`.

This is the Hilbert-space Bochner–Jensen template `norm_integral_sq_le_length_mul_integral_normSq`
applied to the continuous curve `s ↦ mulBdd m (G s)` (continuity via `continuous_mulBdd`), combined
with the bounded-multiplier Bochner commute `mulBdd_intervalIntegral_comm` — entirely
`Lp`-frontier-free (no pointwise coeFn interchange). -/
private theorem mulBdd_steklov_normSq_le_average
    {m : Domain3 → ℝ}
    (hmem : MemLp (fun ξ : Domain3 => (m ξ : ℂ)) ⊤ (volume : Measure Domain3)) {C : ℝ}
    (hC : 0 ≤ C) (hmle : ∀ ξ, |m ξ| ≤ C)
    {G : ℝ → L2C_R3} {δ t : ℝ} (hδ : 0 < δ) (ht : 0 ≤ t)
    (hGcont : ContinuousOn G (Set.Ici 0)) :
    ‖mulBdd m hmem (δ⁻¹ • ∫ s in t..(t + δ), G s)‖ ^ 2
      ≤ δ⁻¹ * ∫ s in t..(t + δ), ‖mulBdd m hmem (G s)‖ ^ 2 := by
  have hle : t ≤ t + δ := by linarith
  have hwin : Set.uIcc t (t + δ) ⊆ Set.Ici (0 : ℝ) := by
    rw [Set.uIcc_of_le hle]; intro s hs; exact le_trans ht hs.1
  have hGcontWin : ContinuousOn G (Set.uIcc t (t + δ)) := hGcont.mono hwin
  have hGint : IntervalIntegrable G volume t (t + δ) := hGcontWin.intervalIntegrable
  -- the curve `s ↦ mulBdd m (G s)` is continuous on the window
  have hMGcontWin : ContinuousOn (fun s => mulBdd m hmem (G s)) (Set.uIcc t (t + δ)) :=
    (continuous_mulBdd m hmem hC hmle).comp_continuousOn hGcontWin
  have hMGint : IntervalIntegrable (fun s => mulBdd m hmem (G s)) volume t (t + δ) :=
    hMGcontWin.intervalIntegrable
  -- push `mulBdd m` through the `δ⁻¹ •` and the Bochner integral
  rw [mulBdd_smul m hmem, mulBdd_intervalIntegral_comm m hmem hGint hMGint]
  -- now it is the Hilbert Jensen template applied to `s ↦ mulBdd m (G s)`
  rw [norm_smul, mul_pow, norm_inv, Real.norm_eq_abs, abs_of_pos hδ]
  have hjensen := norm_integral_sq_le_length_mul_integral_normSq
    (f := fun s => mulBdd m hmem (G s)) hle hMGcontWin
  rw [show (t + δ) - t = δ by ring] at hjensen
  calc (δ⁻¹) ^ 2 * ‖∫ s in t..(t + δ), mulBdd m hmem (G s)‖ ^ 2
      ≤ (δ⁻¹) ^ 2 * (δ * ∫ s in t..(t + δ), ‖mulBdd m hmem (G s)‖ ^ 2) := by
        apply mul_le_mul_of_nonneg_left hjensen (by positivity)
    _ = δ⁻¹ * ∫ s in t..(t + δ), ‖mulBdd m hmem (G s)‖ ^ 2 := by
        rw [← mul_assoc]; congr 1; field_simp

/-- **Per-component weighted Steklov–Jensen bound (the gate, one Fourier component).**  For each
`j`, the full (unbounded-weight) spectral viscous integrand of the Steklov-averaged `j`-component is
bounded by the time-average of the per-`s` spectral integrand:

  `∫_ξ W ‖𝓕(projⱼ steklovAvg) ξ‖² ≤ δ⁻¹ ∫_s ∫_ξ W ‖𝓕(projⱼ (u s)) ξ‖²`,   `W = (2π)²‖ξ‖²`.

Proof: pass to the bounded truncations `m_k = min(√W,k)`; for each `k` the bounded-multiplier
Jensen bound `mulBdd_steklov_normSq_le_average` plus `norm_mulBdd_sq` gives the truncated estimate,
and `(m_k)² ≤ W` bounds its RHS by the full one; the LHS converges to the full integral by
dominated convergence (the `H¹` Steklov average makes `W‖𝓕(projⱼ steklovAvg)‖²` integrable). -/
private theorem viscousFourier_steklov_component_le (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (u₀ : L2Sigma_R3) (n : ℕ)
    (gs : GalerkinSolutionData_R3 𝔊 F ν u₀ n) {δ t : ℝ} (hδ : 0 < δ) (ht : 0 ≤ t) (j : Fin 3) :
    ∫ ξ : Domain3, (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 *
        ‖(𝓕 (L2VF_projComponentC_R3 j (steklovAvg 𝔊 F ν u₀ n gs δ t)) : L2C_R3) ξ‖ ^ 2
      ≤ δ⁻¹ * ∫ s in t..(t + δ),
          ∫ ξ : Domain3, (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 *
            ‖(𝓕 (L2VF_projComponentC_R3 j (gs.u s)) : L2C_R3) ξ‖ ^ 2 := by
  classical
  set Gbar : L2C_R3 := 𝓕 (L2VF_projComponentC_R3 j (steklovAvg 𝔊 F ν u₀ n gs δ t)) with hGbar
  set Gcurve : ℝ → L2C_R3 := fun s => 𝓕 (L2VF_projComponentC_R3 j (gs.u s)) with hGcurve
  -- The integrands as `∫ (m_k ξ)² ‖·‖²` and full `∫ W ‖·‖²`.
  set W : Domain3 → ℝ := fun ξ => (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 with hW
  -- `Gbar = δ⁻¹ • ∫_s Gcurve s` (the proved L²-element commute).
  have hGbar_eq : Gbar = δ⁻¹ • ∫ s in t..(t + δ), Gcurve s := by
    rw [hGbar, hGcurve]; exact fourier_proj_steklovAvg_eq 𝔊 F ν u₀ n gs hδ ht j
  -- `Gcurve` is continuous on `Ici 0`.
  have hGcont : ContinuousOn Gcurve (Set.Ici (0 : ℝ)) :=
    fourierProjCurve_continuousOn 𝔊 F ν u₀ n gs j
  -- abbreviation for the truncated multiplier
  set m : ℕ → Domain3 → ℝ := fun k => sqrtViscousWeightTrunc k with hm
  have hmem : ∀ k, MemLp (fun ξ : Domain3 => (m k ξ : ℂ)) ⊤ (volume : Measure Domain3) :=
    fun k => memLp_top_sqrtViscousWeightTrunc k
  have hmle : ∀ k ξ, |m k ξ| ≤ (k : ℝ) := fun k ξ => sqrtViscousWeightTrunc_abs_le k ξ
  -- pointwise `(m k ξ)² ≤ W ξ` and `(m k ξ)² → W ξ`
  have hmsq_le : ∀ k ξ, (m k ξ) ^ 2 ≤ W ξ := by
    intro k ξ
    rw [hW]
    calc (m k ξ) ^ 2 ≤ (sqrtViscousWeight ξ) ^ 2 := by
          rw [hm]; apply pow_le_pow_left₀ (sqrtViscousWeightTrunc_nonneg k ξ) (min_le_left _ _)
      _ = (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 := by rw [sqrtViscousWeight_sq]; rfl
  have hmsq_tendsto : ∀ ξ, Filter.Tendsto (fun k => (m k ξ) ^ 2) Filter.atTop (nhds (W ξ)) := by
    intro ξ
    have h1 := (tendsto_sqrtViscousWeightTrunc ξ).pow 2
    rw [show sqrtViscousWeight ξ ^ 2 = W ξ from by rw [sqrtViscousWeight_sq]; rfl] at h1
    exact h1
  -- LHS full integrand integrable (Steklov average is H¹)
  have hSteklovH1 : memH1VF_R3 (steklovAvg 𝔊 F ν u₀ n gs δ t : L2VF_R3) :=
    steklovAvg_memH1 𝔊 F ν u₀ n gs hδ ht
  have hLHSint : Integrable (fun ξ => W ξ * ‖(Gbar : Domain3 → ℂ) ξ‖ ^ 2)
      (volume : Measure Domain3) := by
    rw [hGbar, hW]; exact integrable_viscous_integrand_of_memH1 _ hSteklovH1 j
  -- The truncated LHS equals `‖mulBdd (m k) Gbar‖²`, and converges (DCT) to the full integral.
  have hLHS_k : ∀ k, ∫ ξ, (m k ξ) ^ 2 * ‖(Gbar : Domain3 → ℂ) ξ‖ ^ 2 ∂(volume : Measure Domain3)
      = ‖mulBdd (m k) (hmem k) Gbar‖ ^ 2 := fun k => (norm_mulBdd_sq (m k) (hmem k) Gbar).symm
  have hLHS_tendsto : Filter.Tendsto
      (fun k => ∫ ξ, (m k ξ) ^ 2 * ‖(Gbar : Domain3 → ℂ) ξ‖ ^ 2 ∂(volume : Measure Domain3))
      Filter.atTop (nhds (∫ ξ, W ξ * ‖(Gbar : Domain3 → ℂ) ξ‖ ^ 2 ∂(volume : Measure Domain3))) := by
    refine MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun ξ => W ξ * ‖(Gbar : Domain3 → ℂ) ξ‖ ^ 2) ?_ hLHSint ?_ ?_
    · intro k
      exact (((continuous_sqrtViscousWeightTrunc k).pow 2).aestronglyMeasurable).mul
        ((Lp.aestronglyMeasurable Gbar).norm.pow 2)
    · intro k
      filter_upwards with ξ
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_right (hmsq_le k ξ) (by positivity)
    · filter_upwards with ξ
      exact (hmsq_tendsto ξ).mul_const _
  -- Per-`k`, the truncated LHS ≤ the full RHS.
  have hle : t ≤ t + δ := by linarith
  have hperk : ∀ k, ∫ ξ, (m k ξ) ^ 2 * ‖(Gbar : Domain3 → ℂ) ξ‖ ^ 2 ∂(volume : Measure Domain3)
      ≤ δ⁻¹ * ∫ s in t..(t + δ), ∫ ξ, W ξ *
          ‖(Gcurve s : Domain3 → ℂ) ξ‖ ^ 2 ∂(volume : Measure Domain3) := by
    intro k
    -- truncated LHS = ‖mulBdd (m k) Gbar‖²  ≤ δ⁻¹ ∫_s ‖mulBdd (m k) (Gcurve s)‖²  (Jensen)
    rw [hLHS_k k, hGbar_eq]
    refine le_trans (mulBdd_steklov_normSq_le_average (hmem k) (Nat.cast_nonneg k) (hmle k)
      hδ ht hGcont) ?_
    -- `‖mulBdd (m k) (Gcurve s)‖² = ∫ (m k)² ‖Gcurve s‖²  ≤ ∫ W ‖Gcurve s‖²`
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine intervalIntegral.integral_mono_on hle ?_ ?_ (fun s _ => ?_)
    · -- integrability of `s ↦ ‖mulBdd (m k) (Gcurve s)‖²` (continuous curve)
      have hcontw : ContinuousOn (fun s => mulBdd (m k) (hmem k) (Gcurve s)) (Set.uIcc t (t + δ)) :=
        (continuous_mulBdd (m k) (hmem k) (Nat.cast_nonneg k) (hmle k)).comp_continuousOn
          (hGcont.mono (by rw [Set.uIcc_of_le hle]; intro s hs; exact le_trans ht hs.1))
      exact (hcontw.norm.pow 2).intervalIntegrable
    · -- integrability of `s ↦ ∫ W ‖Gcurve s‖²` (continuous via the field, transported)
      have hwin : Set.uIcc t (t + δ) ⊆ Set.Ici (0 : ℝ) := by
        rw [Set.uIcc_of_le hle]; intro s hs; exact le_trans ht hs.1
      have heq : ∀ s, (∫ ξ, W ξ * ‖(Gcurve s : Domain3 → ℂ) ξ‖ ^ 2 ∂(volume : Measure Domain3))
          = ‖weightedFourierComponent (gs.u s : L2VF_R3) (gs.reg_mem s) j‖ ^ 2 := by
        intro s; rw [hW, hGcurve]
        exact (norm_weightedFourierComponent_sq (gs.u s : L2VF_R3) (gs.reg_mem s) j).symm
      refine ContinuousOn.intervalIntegrable ?_
      exact ContinuousOn.congr (((gs.viscous_curve_continuous j).mono hwin).norm.pow 2)
        (fun s _ => heq s)
    · -- pointwise: `‖mulBdd (m k) (Gcurve s)‖² = ∫ (m k)²‖Gcurve s‖² ≤ ∫ W ‖Gcurve s‖²`
      rw [norm_mulBdd_sq (m k) (hmem k) (Gcurve s)]
      refine integral_mono_of_nonneg ?_ ?_ ?_
      · filter_upwards with ξ; positivity
      · rw [hW]; exact integrable_viscous_integrand_of_memH1 (gs.u s : L2VF_R3) (gs.reg_mem s) j
      · filter_upwards with ξ
        exact mul_le_mul_of_nonneg_right (hmsq_le k ξ) (by positivity)
  -- Conclude by passing to the limit `k → ∞`.
  have hfinal := le_of_tendsto hLHS_tendsto (Filter.Eventually.of_forall hperk)
  -- `hfinal : ∫ W ‖Gbar‖² ≤ δ⁻¹ ∫_s ∫ W ‖Gcurve s‖²`; this is the goal modulo the abbreviations.
  exact hfinal

/-- **Viscous (H¹) Jensen bound on the Steklov average — the C2 first-PR target.** For `0 < δ`
and `0 ≤ t`, the viscous dissipation seminorm of the Steklov average is bounded by the time-average
of the curve's viscous seminorm over the forward window:

  `viscousFormSq_R3 1 (steklovAvg gs δ t) ≤ δ⁻¹ · ∫_{t}^{t+δ} viscousFormSq_R3 1 (gs.u s) ds`.

This is the H¹/Jensen bound the Aubin–Lions Steklov route needs (step 2 of the C2 plan): combined
with the `n`-uniform `reg_bound` (`∫_{0}^{T} viscousFormSq_R3 1 (gs.u s) ≤ ½‖u₀‖²`), it gives the
averaged states an `n`-uniform *pointwise* H¹ bound, which the raw pointwise samples lacked (see the
C2 route discussion), and which P3's `spatialInput_R3_of_localRellich` consumes.

PROOF (now `sorry`-free, issue #15): `viscousFormSq_R3 1 w` is the weighted-Fourier energy
`∑_j ∫_ξ (2π)²‖ξ‖² ‖(𝓕 (proj_j w)) ξ‖² dξ` (F7).  Both sides are exposed spectrally (F7), reducing to
a per-component bound `viscousFourier_steklov_component_le` summed over `j`.  Per component:
* the L²-element commute `fourier_proj_steklovAvg_eq` gives
  `𝓕 (proj_j steklovAvg) = δ⁻¹ • ∫_s 𝓕 (proj_j (u s))` (in `L2C_R3`);
* the unbounded spectral weight `W = (2π)²‖ξ‖²` is handled by TRUNCATION: for each `k`, the bounded
  multiplier `m_k = min(√W,k)` (`WeightedFourierCommute.mulBdd`) commutes with the Bochner interval
  integral (`mulBdd_intervalIntegral_comm`, proved via `ext_inner_left` + `innerSL`), so the proved
  Hilbert-space Bochner–Jensen template `norm_integral_sq_le_length_mul_integral_normSq` (applied to
  the continuous curve `s ↦ mulBdd m_k (𝓕 (proj_j (u s)))`) gives the per-`k` weighted estimate
  `mulBdd_steklov_normSq_le_average`;
* `(m_k)² ≤ W` bounds each per-`k` RHS by the full one, and dominated convergence
  (`tendsto_integral_of_dominated_convergence`, dominator `W‖𝓕(proj_j steklovAvg)‖²` integrable
  because the Steklov average is `H¹` — `steklovAvg_memH1`) sends the per-`k` LHS to the full LHS.

This avoids entirely the pointwise `Lp`-valued-Bochner coeFn interchange / joint `(s,ξ)`-measurable
representative that the earlier frontier note flagged (the `convL2_coeFn_ae`-class obstruction):
the bounded-multiplier route keeps every step at the `L²`-element level, and the unbounded weight is
recovered by the monotone truncation limit.  The interval-integrability of the per-`s` spectral
integrand uses the new `GalerkinSolutionData_R3.viscous_curve_continuous` field (finite-dim-derived
continuity of `s ↦ √W • 𝓕(proj_j (u s))`). -/
private theorem viscousFormSq_steklovAvg_le_average (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (u₀ : L2Sigma_R3) (n : ℕ)
    (gs : GalerkinSolutionData_R3 𝔊 F ν u₀ n) {δ t : ℝ} (hδ : 0 < δ) (ht : 0 ≤ t) :
    viscousFormSq_R3 1 (steklovAvg 𝔊 F ν u₀ n gs δ t)
      ≤ δ⁻¹ * ∫ s in t..(t + δ), viscousFormSq_R3 1 ((gs.u s : L2VF_R3)) := by
  -- Expose both sides spectrally (F7), reducing to a per-frequency Jensen bound on the
  -- `j`-th Fourier component of the Steklov average.  The L²-element commute
  -- `fourier_proj_steklovAvg_eq` (PROVED above, sorry-free) rewrites that component as the
  -- time-average `δ⁻¹ • ∫_s 𝓕 (proj_j (u s))`.
  -- Expose the LHS spectrally (F7); each summand is `∫_ξ W ‖𝓕(projⱼ steklovAvg)ξ‖²`.
  rw [FourierL2.viscousFormSq_R3_eq_integral_normSq_fourier]
  -- Rewrite the RHS time-integrand `viscousFormSq_R3 1 (u s)` spectrally and pull the finite sum
  -- out of the (interval) time integral and the `δ⁻¹` factor.
  have hle : t ≤ t + δ := by linarith
  -- per-`s` spectral integrand for component `j`
  set Ij : Fin 3 → ℝ → ℝ := fun j s =>
    ∫ ξ : Domain3, (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 *
      ‖(𝓕 (L2VF_projComponentC_R3 j (gs.u s)) : L2C_R3) ξ‖ ^ 2 with hIj
  -- each `Ij j` is interval-integrable on `[t,t+δ]`: it equals `‖weightedFourierComponent (u s) j‖²`,
  -- a continuous function of `s` (norm² of the continuous weighted-Fourier curve — the new field).
  have hwin : Set.uIcc t (t + δ) ⊆ Set.Ici (0 : ℝ) := by
    rw [Set.uIcc_of_le hle]; intro s hs; exact le_trans ht hs.1
  have hIjeq : ∀ j s, Ij j s
      = ‖weightedFourierComponent (gs.u s : L2VF_R3) (gs.reg_mem s) j‖ ^ 2 := by
    intro j s
    rw [hIj]
    exact (norm_weightedFourierComponent_sq (gs.u s : L2VF_R3) (gs.reg_mem s) j).symm
  have hIjint : ∀ j, IntervalIntegrable (Ij j) volume t (t + δ) := by
    intro j
    have hcont : ContinuousOn (Ij j) (Set.uIcc t (t + δ)) :=
      ContinuousOn.congr (((gs.viscous_curve_continuous j).mono hwin).norm.pow 2)
        (fun s _ => hIjeq j s)
    exact hcont.intervalIntegrable
  have hRHS : δ⁻¹ * ∫ s in t..(t + δ), viscousFormSq_R3 1 ((gs.u s : L2VF_R3))
      = ∑ j : Fin 3, δ⁻¹ * ∫ s in t..(t + δ), Ij j s := by
    rw [← Finset.mul_sum]
    congr 1
    rw [← intervalIntegral.integral_finsetSum (fun j _ => hIjint j)]
    refine intervalIntegral.integral_congr (fun s _ => ?_)
    simp only [hIj]
    rw [FourierL2.viscousFormSq_R3_eq_integral_normSq_fourier]
  rw [hRHS]
  refine Finset.sum_le_sum (fun j _ => ?_)
  exact viscousFourier_steklov_component_le 𝔊 F ν u₀ n gs hδ ht j

/-- **n-uniform pointwise H¹ bound on the Steklov averages.**  For the forward window
`[t,t+δ] ⊆ [0,T]` (i.e. `0 ≤ t`, `t+δ ≤ T`), the averaged state's viscous seminorm is bounded by
`δ⁻¹ ν⁻¹ · ½‖u₀‖²` — finite and `n`-independent (this is the bound `spatialInput_R3_of_localRellich`
consumes; the raw pointwise samples lacked it).  Combines the gate
`viscousFormSq_steklovAvg_le_average` with the integrated `reg_bound`. -/
private theorem viscousFormSq_steklovAvg_uniform_bound (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (hν : 0 < ν) (u₀ : L2Sigma_R3) (n : ℕ) (T : ℝ) (hT : 0 < T)
    (gs : GalerkinSolutionData_R3 𝔊 F ν u₀ n) {δ t : ℝ} (hδ : 0 < δ) (ht : 0 ≤ t)
    (htδT : t + δ ≤ T) :
    viscousFormSq_R3 1 (steklovAvg 𝔊 F ν u₀ n gs δ t)
      ≤ δ⁻¹ * (ν⁻¹ * ((1 / 2 : ℝ) * ‖(u₀ : L2VF_R3)‖ ^ 2)) := by
  have hle : t ≤ t + δ := by linarith
  have hcont : ContinuousOn (fun s => viscousFormSq_R3 1 (gs.u s : L2VF_R3)) (Set.Ici (0 : ℝ)) :=
    viscousFormSq_curve_continuousOn 𝔊 F ν u₀ n gs
  have hnn : ∀ s, 0 ≤ viscousFormSq_R3 1 (gs.u s : L2VF_R3) :=
    fun s => viscousFormSq_R3_nonneg (by norm_num) _
  have hint0T : IntervalIntegrable (fun s => viscousFormSq_R3 1 (gs.u s : L2VF_R3)) volume 0 T := by
    refine (hcont.mono ?_).intervalIntegrable
    rw [Set.uIcc_of_le hT.le]; intro s hs; exact hs.1
  -- window sub-integral ≤ full [0,T] integral (nonneg integrand, `Ioc t (t+δ) ⊆ Ioc 0 T`)
  have hwindow : ∫ s in t..(t + δ), viscousFormSq_R3 1 (gs.u s : L2VF_R3)
      ≤ ∫ s in (0:ℝ)..T, viscousFormSq_R3 1 (gs.u s : L2VF_R3) := by
    rw [intervalIntegral.integral_of_le hle, intervalIntegral.integral_of_le hT.le]
    refine setIntegral_mono_set hint0T.1 (ae_of_all _ (fun s => hnn s)) ?_
    refine HasSubset.Subset.eventuallyLE (fun s hs => ?_)
    exact ⟨lt_of_le_of_lt ht hs.1, le_trans hs.2 htδT⟩
  -- full integral ≤ ν⁻¹ · ½‖u₀‖² via reg_bound (ν-scaling)
  have hreg : ∫ s in (0:ℝ)..T, viscousFormSq_R3 1 (gs.u s : L2VF_R3)
      ≤ ν⁻¹ * ((1 / 2 : ℝ) * ‖(u₀ : L2VF_R3)‖ ^ 2) := by
    have hrb := gs.reg_bound T hT
    have hscale : ∀ s, viscousFormSq_R3 ν (gs.u s : L2VF_R3)
        = ν * viscousFormSq_R3 1 (gs.u s : L2VF_R3) := by
      intro s; rw [viscousFormSq_R3_eq_smul, smul_eq_mul]
    rw [intervalIntegral.integral_congr (g := fun s => ν * viscousFormSq_R3 1 (gs.u s : L2VF_R3))
      (fun s _ => hscale s), intervalIntegral.integral_const_mul] at hrb
    -- `ν * I ≤ ½‖u₀‖²` ⇒ `I ≤ ν⁻¹ ½‖u₀‖²`
    rw [le_inv_mul_iff₀ hν]
    exact hrb
  calc viscousFormSq_R3 1 (steklovAvg 𝔊 F ν u₀ n gs δ t)
      ≤ δ⁻¹ * ∫ s in t..(t + δ), viscousFormSq_R3 1 (gs.u s : L2VF_R3) :=
        viscousFormSq_steklovAvg_le_average 𝔊 F ν u₀ n gs hδ ht
    _ ≤ δ⁻¹ * (ν⁻¹ * ((1 / 2 : ℝ) * ‖(u₀ : L2VF_R3)‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left (le_trans hwindow hreg) (by positivity)

/-- **Single-`(δ, t₀)` spatial extraction for the Steklov averages.**  For a fixed mesh `δ > 0`
and base time `t₀` with `[t₀, t₀+δ] ⊆ [0,T]`, P3 (`spatialInput_R3_of_localRellich B`) applied to the
sequence `n ↦ steklovAvg (galSeq n) δ t₀` extracts a strictly-monotone subsequence `ψ` and a
ball-restricted spatial limit `g ∈ L2Sigma_R3`.  The required uniform `L²`+`H¹` bounds are exactly
`steklovAvg_norm_le_u0`, `steklovAvg_mem_sigma`, `steklovAvg_memH1`, and the proved gate-derived
`viscousFormSq_steklovAvg_uniform_bound` — all `n`-uniform on the fixed window.

This is the atomic extraction the `δ`-mesh diagonalization iterates. -/
private theorem steklovAvg_spatial_extraction (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T) (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n)
    (B : LocalRellichInput) {δ t₀ : ℝ} (hδ : 0 < δ) (ht₀ : 0 ≤ t₀) (htδT : t₀ + δ ≤ T) :
    ∃ (ψ : ℕ → ℕ) (g : L2VF_R3), StrictMono ψ ∧ g ∈ L2Sigma_R3 ∧
      ∀ R : ℝ, Filter.Tendsto
        (fun n => ∫ x in Metric.closedBall (0 : Domain3) R,
          ‖((steklovAvg 𝔊 F ν u₀ (ψ n) (galSeq (ψ n)) δ t₀) x : EuclideanSpace ℝ (Fin 3))
            - (g x : EuclideanSpace ℝ (Fin 3))‖ ^ 2 ∂(volume : Measure Domain3))
        Filter.atTop (nhds 0) := by
  -- common `n`-uniform bound `M` dominating both `‖steklovAvg‖` and `√(viscous bound)`.
  set Mb : ℝ := Real.sqrt (δ⁻¹ * (ν⁻¹ * ((1 / 2 : ℝ) * ‖(u₀ : L2VF_R3)‖ ^ 2))) with hMb
  set M : ℝ := max ‖(u₀ : L2VF_R3)‖ Mb with hM
  refine spatialInput_R3_of_localRellich B M
    (fun n => steklovAvg 𝔊 F ν u₀ n (galSeq n) δ t₀) ?_ ?_ ?_ ?_
  · exact fun n => steklovAvg_mem_sigma 𝔊 F ν u₀ n (galSeq n) hδ ht₀
  · exact fun n => steklovAvg_memH1 𝔊 F ν u₀ n (galSeq n) hδ ht₀
  · intro n
    exact le_trans (steklovAvg_norm_le_u0 𝔊 F ν u₀ n (galSeq n) hδ ht₀) (le_max_left _ _)
  · intro n
    -- `viscousFormSq (steklovAvg) ≤ δ⁻¹ν⁻¹½‖u₀‖² = Mb² ≤ M²`.
    have hb := viscousFormSq_steklovAvg_uniform_bound 𝔊 F ν hν u₀ n T hT (galSeq n) hδ ht₀ htδT
    have hMbsq : Mb ^ 2 = δ⁻¹ * (ν⁻¹ * ((1 / 2 : ℝ) * ‖(u₀ : L2VF_R3)‖ ^ 2)) := by
      rw [hMb, Real.sq_sqrt (by positivity)]
    calc viscousFormSq_R3 1 (steklovAvg 𝔊 F ν u₀ n (galSeq n) δ t₀)
        ≤ δ⁻¹ * (ν⁻¹ * ((1 / 2 : ℝ) * ‖(u₀ : L2VF_R3)‖ ^ 2)) := hb
      _ = Mb ^ 2 := hMbsq.symm
      _ ≤ M ^ 2 := by
          rw [hM]; exact pow_le_pow_left₀ (by positivity) (le_max_right _ _) 2

/-- **Raw-curve time-equicontinuity, uniform in `n` (the Arzelà–Ascoli input).**  The
`TimeCompactnessInput` modulus is stated directly on the raw Galerkin curves, so it already gives
uniform-in-`n` L² equicontinuity of `t ↦ (galSeq n).u t` on `[0,T]`: for every `ε > 0` there is
`δ > 0` such that for all `n` and all `s,t ∈ [0,T]` with `|s − t| < δ`,
`‖(galSeq n).u s − (galSeq n).u t‖ < ε`.  This is a thin restatement of
`Htime.uniform_time_modulus`, isolated as the named Arzelà–Ascoli equicontinuity hypothesis the C2
assembly consumes (the spatial precompactness at sample times being supplied separately by the
Steklov averages + `steklovAvg_spatial_extraction`). -/
private theorem galerkin_curves_equicontinuous (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (T : ℝ) (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n)
    (Htime : TimeCompactnessInput 𝔊 F ν T u₀ galSeq) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ (n : ℕ) (s t : ℝ),
      s ∈ Set.Icc (0 : ℝ) T → t ∈ Set.Icc (0 : ℝ) T → |s - t| < δ →
      ‖((galSeq n).u s : L2VF_R3) - ((galSeq n).u t : L2VF_R3)‖ < ε :=
  Htime.uniform_time_modulus

/-- **Bochner-time / space-time compactness extraction on ℝ³ (the isolated Aubin–Lions-time
pillar) — stated UNCONDITIONALLY and LOCALLY for the bounded Galerkin sequence.**  From the proved
spatial precompactness at sample times (`steklovAvg_spatial_extraction`, fed by P3 via `B`) together
with the intrinsic uniform-in-`n` time equicontinuity of the Galerkin curves (which the curves
genuinely possess via their `W^{1,p}(0,T;X)` time-derivative estimate, but which mathlib cannot
mechanize), the Galerkin curves admit a SINGLE strictly-monotone subsequence `φ` and a limit curve
`u : Time → L2Sigma_R3` such that, **for every ball radius `R`**, the ball restrictions
`restrictToBall R ((galSeq (φ n)).u t)` converge to `restrictToBall R (u t)` at a.e. time `t`, with
`u` time-measurable.

**LOCAL, not global (the load-bearing correction).**  The convergence is asserted ONLY per ball,
through `restrictToBall R`, NOT in the full `L2VF_R3` norm.  On ℝ³ the available compactness is local:
`spatial_compactness_R3` / the Fréchet–Kolmogorov–Rellich chain is ball-restricted with NO tightness,
so the Galerkin sequence may lose mass at spatial infinity and local precompactness does NOT yield
global `L²` a.e.-in-time convergence.  A global statement would therefore be OVER-STRONG (stronger
than the removed `aubin_lions_R3`, and not generally true); the per-ball form is the honest content
and is exactly what the package needs (its `strong_convergence` field is itself per-ball, over
`L²(0,T; L²(B_R))`).

This is the genuine Aubin–Lions *time* content, LOCALIZED: the Arzelà–Ascoli diagonalization
(countable dense times × `δ`-mesh → 0 × balls) that upgrades pointwise-in-time LOCAL spatial
precompactness + time equicontinuity into a single subsequence with per-ball a.e.-in-time `L²`
convergence.  Mathlib lacks the Bochner-valued Fréchet–Kolmogorov / Aubin–Lions compactness theorem
in `L²(0,T;X)`, so this single extraction step is isolated as an axiom.  It is STRICTLY THINNER /
WEAKER than the former `aubin_lions_R3`: the spatial half is now genuinely PROVED (the
`steklovAvg_spatial_extraction` chain, axiom-free), and this axiom carries ONLY the LOCAL
time-compactness extraction — no spatial compactness, no tightness, no global-`L²` claim.

The axiom is UNCONDITIONAL: it does NOT take a `TimeCompactnessInput`/modulus hypothesis.  The
Galerkin curves' time-equicontinuity is a TRUE standalone consequence of their proved uniform bounds
(`galerkin_norm_le_u0`) and ODE structure; the single irreducible fact mathlib cannot supply is the
Bochner-time-LOCAL compactness *extraction* itself, which this axiom names directly.  By stating it
unconditionally we absorb the modulus, so the time layer rests on exactly THIS ONE axiom — the
redundant `timeCompactnessInput_R3` axiom from the prior revision of this PR (which only ever fed
this extraction) is dropped.

Once supplied, the whole `AubinLionsPackage_R3` is assembled axiom-free from this conclusion:
`u_aestronglyMeasurable` is the second conjunct; `strong_convergence` follows for each ball `R`
directly from the per-ball a.e. convergence + dominated convergence in `L²` (the constant dominator
`‖u₀‖` on the finite window `[0,T]`, via `galerkin_norm_le_u0`).  NON-VACUOUS: the conclusion pins
the ball restrictions of `u` to the per-ball a.e.-`L²`-limits of the given subsequence (not a free
choice).  Temam III.2.1; Lemarié-Rieusset §6 (Aubin–Lions, local).

**Issue #44 note:** This was formerly `axiom galerkinSpaceTimeExtraction_R3`.  It is now a
PROVED `theorem`, proved via `u_lim_aestronglyMeasurable` from the two sound thinner axioms
`galerkin_spacetime_precompact_R3` (refine-capable local Aubin–Lions–Simon spacetime precompactness)
and `galerkin_weakLimit_R3` (Banach–Alaoglu + div-free weak limit in `L2Sigma_R3`), plus the
proved Arzelà–Ascoli-in-time chain (`perBall_ae_subseq`, `diag_ae_subseq`) in
`ArzelaAscoliTime.lean`.  Signature is BYTE-IDENTICAL.  No sorry in proof body. -/
theorem galerkinSpaceTimeExtraction_R3
    (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T)
    (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n)
    (B : LocalRellichInput) :
    ∃ (φ : ℕ → ℕ) (u : Time → L2Sigma_R3), StrictMono φ ∧
      AEStronglyMeasurable (fun t => (u t : L2VF_R3))
        (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)) ∧
      (∀ R : ℝ, ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)),
        Filter.Tendsto (fun n => restrictToBall R ((galSeq (φ n)).u t : L2VF_R3)) Filter.atTop
          (nhds (restrictToBall R (u t : L2VF_R3)))) :=
  u_lim_aestronglyMeasurable 𝔊 F ν hν T hT u₀ galSeq B

/-! ### Tier W — WeakFormNS limit passage (conjunct 2 of `galerkin_limit_passage_R3`)

This is the `WeakFormNS` conjunct of the limit-passage axiom, isolated as a named lemma so the
axiom's second component can be discharged independently of conjuncts 0/1/3/4.  The target is
exactly `WeakFormNS ν T (r3Evolution 𝔊 F) alPkg.u` — byte-identical to the `weak_eq_limit`
field of `GalerkinCompactnessPackageFull_R3` (and to `hspec.2.1` in `build_galerkin_package_R3`
once the good representative is taken to be `alPkg.u`, conjunct 0 = `EventuallyEq.refl`).

PROOF SKELETON (Temam III.3).  Fix an admissible test `ψ ⊗ w` (`ψ : Time → ℝ` C¹ with
`tsupport ψ ⊆ Ioo 0 T`, `w` Schwartz divergence-free).  For each Galerkin level `N` and each
`n ≥ N` the approximant ODE `u_ode` (`AxiomaticClosure.lean:387`) holds against the Galerkin
test `𝔊.P N w` (a fixed point of `𝔊.P n` for `n ≥ N`).  Multiplying by `ψ(t)`, integrating over
`[0,T]`, and integrating the time-derivative term by parts (boundary-free because
`tsupport ψ ⊆ Ioo 0 T`) yields, for the approximant `uₙ`,
`∫₀ᵀ (-⟪uₙ t, 𝔊.P N w⟫ ψ'(t) + ψ(t)(ν·B(uₙ t, 𝔊.P N w) + b(uₙ t, uₙ t, 𝔊.P N w))) = 0`.
Passing `n→∞` (linear terms by the weak-L² convergence bridge `inner_tendsto_of_perball`; the
nonlinear term by `bForm_tendsto_of_strongL2`) and then `N→∞` (Galerkin test density) gives the
weak form for `alPkg.u` against `ψ ⊗ w`.

ISOLATED ANALYTIC FRONTIER (the residual of this conjunct — see the `ALLOW_SORRY` below).  After
the structural reduction (time-IBP + dominated convergence in time, both in hand) three atoms
remain.  Each is PROVABLE on existing repo/Mathlib pieces — none is a strong-compactness wall —
but each is its own multi-lemma sub-development not yet built:
(i) the VISCOUS-form equality passage `B(uₙ t, w) → B(u t, w)`.  `stokesTestPairing_R3` is the
H¹/Dirichlet pairing `∑ⱼ∫ (2π)²‖ξ‖² Re[𝓕uⱼ·conj 𝓕wⱼ]` (`Regularity.lean:123`), not L²-continuous in
`u` as written.  PROVABLE route (Plancherel onto the test): `(2π)²‖ξ‖² 𝓕wⱼ = 𝓕((-Δ)wⱼ)` for Schwartz
`wⱼ`, so by Parseval (`Lp.inner_fourier_eq` / `(Lp.fourierTransformₗᵢ _ _).inner_map_map`) the
pairing equals `⟨u, lapVF w⟩_{L²}` with the FIXED element `lapVF w := -Δw ∈ L²` (Schwartz).  This is
the exact second-order analogue of the already-proved first-order
`divComponent_eq_fourier_integral` (`CurlDensity.lean:460`, which moves a single `∂ⱼ` onto a Schwartz
test via `lineDerivOpCLM`/`schwartzC`/`toLp_schwartzC_eq`).  Once reformulated, it passes by the
full-space WEAK convergence already available (`weak_tendsto_of_inner_tendsto`/`inner_tendsto_of_perball`
against the fixed `lapVF w`).  Atom = the 2nd-order Plancherel–Laplacian reformulation lemma.
(ii) the NONLINEAR passage `b(uₙ t, uₙ t, w) → b(u t, u t, w)` at a.e. `t`.  NOT a full-space
strong-compactness gap: `w` is Schwartz (rapid decay), so the ball-tail ε/3 split
(per-ball strong-L² via `strong_convergence_ae` on `‖x‖≤R` + the `b`-Schwartz-tail bound for
`‖x‖>R`) reduces it — mirroring the `inner_tendsto_of_perball` ball/tail pattern.  Atom = the
trilinear Schwartz-tail bound for `F.b`/`convIntegralSchwartz` (the `‖x‖>R` remainder controlled by
`w`'s decay), currently absent from `TrilinearEstimate`.
(iii) the Galerkin→Schwartz test DENSITY extension (`u_ode` holds only for `𝔊.P n w = w`; pass the
`N`-th identity then `N→∞` via `𝔊.tendsto_id`).
All three stand on already-proved pieces; the structural reduction (time-IBP + dominated convergence
in time) is in hand. -/

/-- **Stokes-pairing continuity along a Galerkin curve.**  For a Galerkin test `w` with a Schwartz
witness `ψw`, `t ↦ stokesTestPairing_R3 (gs.u t) w` is continuous on forward time `Ici 0`.

The negative-Laplacian reformulation `stokesTestPairing_R3_eq_sum_inner_negLap` exhibits the pairing
as a finite sum of `L²`-inner products of the (CLM) component projections of the curve against FIXED
Schwartz elements, so continuity is `(component CLM ∘ curve).inner const`. -/
private theorem stokes_curve_continuousOn_R3
    {𝔊 : R3GalerkinScheme} {F : R3NSForms 𝔊} {ν : ℝ} {u₀ : L2Sigma_R3} {n : ℕ}
    (gs : GalerkinSolutionData_R3 𝔊 F ν u₀ n) (w : L2Sigma_R3)
    (ψw : Fin 3 → SchwartzMap Domain3 ℝ)
    (hψw : ∀ j : Fin 3,
      L2VF_projComponent_R3 j (w : L2VF_R3) = (ψw j).toLp 2 (volume : Measure Domain3)) :
    ContinuousOn (fun s => stokesTestPairing_R3 (gs.u s : L2VF_R3) (w : L2VF_R3)) (Set.Ici 0) := by
  have hcurve : ContinuousOn (fun s => (gs.u s : L2VF_R3)) (Set.Ici 0) :=
    galerkin_curve_continuous 𝔊 F ν u₀ n gs
  simp only [stokesTestPairing_R3_eq_sum_inner_negLap _ (w : L2VF_R3) ψw hψw]
  refine continuousOn_finsetSum _ (fun j _ => ?_)
  exact ((L2VF_projComponent_R3 j).continuous.comp_continuousOn hcurve).inner continuousOn_const

/-- **Convection-form continuity along a Galerkin curve** (Schwartz-test form).  For any
Schwartz-div-free test `w`, `t ↦ F.b (gs.u t) (gs.u t) w` is continuous on forward time `Ici 0`.

Unlike `galerkin_bForm_curve_continuousOn`, this does NOT require `w` to be fixed by `𝔊.P n`; it
builds the jointly-continuous bilinear form `(u,v) ↦ b u v w` directly from `b_bound` (as a
`mkContinuous₂` CLM) and composes with the `L²`-continuous curve. -/
private theorem bForm_curve_continuousOn_of_schwartz
    {𝔊 : R3GalerkinScheme} {F : R3NSForms 𝔊} {ν : ℝ} {u₀ : L2Sigma_R3} {n : ℕ}
    (gs : GalerkinSolutionData_R3 𝔊 F ν u₀ n) (w : L2Sigma_R3) (hw : IsSchwartzDivFree_R3 w) :
    ContinuousOn (fun s => F.b (gs.u s) (gs.u s) w) (Set.Ici 0) := by
  obtain ⟨Cb, hCb⟩ := F.b_bound w hw
  let b_blin : L2Sigma_R3 →ₗ[ℝ] L2Sigma_R3 →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ (fun u v => F.b u v w)
      (fun u u' v => F.b_add_1 u u' v w)
      (fun c u v => (F.b_smul_1 c u v w).trans (smul_eq_mul c _).symm)
      (fun u v v' => F.b_add_2 u v v' w)
      (fun c u v => (F.b_smul_2 c u v w).trans (smul_eq_mul c _).symm)
  have hb_norm : ∀ u v : L2Sigma_R3, ‖b_blin u v‖ ≤ |Cb| * ‖u‖ * ‖v‖ := fun u v => by
    show ‖F.b u v w‖ ≤ |Cb| * ‖u‖ * ‖v‖
    rw [Real.norm_eq_abs]
    calc |F.b u v w| ≤ Cb * ‖(u : L2VF_R3)‖ * ‖(v : L2VF_R3)‖ := hCb u v
      _ ≤ |Cb| * ‖(u : L2VF_R3)‖ * ‖(v : L2VF_R3)‖ := by gcongr; exact le_abs_self _
      _ = |Cb| * ‖u‖ * ‖v‖ := by rw [Submodule.coe_norm, Submodule.coe_norm]
  let b_clm : L2Sigma_R3 →L[ℝ] L2Sigma_R3 →L[ℝ] ℝ := b_blin.mkContinuous₂ |Cb| hb_norm
  have hcurve_sigma : ContinuousOn (fun s => gs.u s) (Set.Ici 0) := by
    have hiso : Isometry (fun x : L2Sigma_R3 => (x : L2VF_R3)) := by
      rw [isometry_iff_dist_eq]; intro x y
      simp only [dist_eq_norm, ← AddSubgroupClass.coe_sub, Submodule.coe_norm]
    exact hiso.isUniformInducing.isInducing.continuousOn_iff.mpr
      (galerkin_curve_continuous 𝔊 F ν u₀ n gs)
  exact (b_clm.continuous₂.comp_continuousOn (hcurve_sigma.prodMk hcurve_sigma)).congr
    (fun s _ => rfl)

/-- **Weak-form integrand continuity along a Galerkin curve.**  For a Schwartz-div-free test `w`
and a `C¹` weight `ψ`, the WeakFormNS integrand `t ↦ -⟪uₙ t, w⟫ ψ'(t) + ψ(t)(ν stokes + b)` is
continuous on forward time `Ici 0`.  Assembled from `stokes_curve_continuousOn_R3`,
`bForm_curve_continuousOn_of_schwartz`, and inner-product continuity. -/
private theorem weakFormNS_integrand_continuousOn_R3
    {𝔊 : R3GalerkinScheme} {F : R3NSForms 𝔊} {ν : ℝ} {u₀ : L2Sigma_R3} {n : ℕ}
    (gs : GalerkinSolutionData_R3 𝔊 F ν u₀ n) (w : L2Sigma_R3) (hw : IsSchwartzDivFree_R3 w)
    (ψ : Time → ℝ) (hψC1 : ContDiff ℝ 1 ψ) :
    ContinuousOn (fun t =>
        -(inner (𝕜 := ℝ) (gs.u t : L2VF_R3) (w : L2VF_R3)) * deriv ψ t +
          ψ t * (ν * stokesTestPairing_R3 (gs.u t : L2VF_R3) (w : L2VF_R3) +
            F.b (gs.u t) (gs.u t) w)) (Set.Ici 0) := by
  obtain ⟨ψw, hψw⟩ := hw
  have hcurve : ContinuousOn (fun s => (gs.u s : L2VF_R3)) (Set.Ici 0) :=
    galerkin_curve_continuous 𝔊 F ν u₀ n gs
  have hinner : ContinuousOn (fun s => inner (𝕜 := ℝ) (gs.u s : L2VF_R3) (w : L2VF_R3))
      (Set.Ici 0) := hcurve.inner continuousOn_const
  have hstokes := stokes_curve_continuousOn_R3 gs w ψw hψw
  have hb := bForm_curve_continuousOn_of_schwartz gs w ⟨ψw, hψw⟩
  exact (hinner.neg.mul hψC1.continuous_deriv_one.continuousOn).add
    (hψC1.continuous.continuousOn.mul ((continuousOn_const.mul hstokes).add hb))

set_option maxHeartbeats 800000 in
/-- **Per-level WeakFormNS identity.**  For a Galerkin level `n` and a test `w` fixed by `𝔊.P n`,
the level-`n` approximant integrand integrates to `0` over `[0,T]`.

Time-IBP via the product-rule FTC on `h(t) := ⟪uₙ t, w⟫ ψ(t)`: the integrand equals `-h'(t)` (using
the ODE field `u_ode` to rewrite `ν stokes + b = -⟪uₙ'(t), w⟫`), and the boundary terms vanish since
`tsupport ψ ⊆ Ioo 0 T`.  Mirrors the T³ `galerkin_weakFormNS_zero`. -/
private theorem galerkin_weakFormNS_zero_R3
    {𝔊 : R3GalerkinScheme} {F : R3NSForms 𝔊} {ν : ℝ} {u₀ : L2Sigma_R3} {n : ℕ}
    (T : ℝ) (hT : 0 < T)
    (gs : GalerkinSolutionData_R3 𝔊 F ν u₀ n) (w : L2Sigma_R3)
    (hw : (w : L2VF_R3) = 𝔊.P n (w : L2VF_R3))
    (ψ : Time → ℝ) (hψsupp : tsupport ψ ⊆ Set.Ioo 0 T) (hψC1 : ContDiff ℝ 1 ψ) :
    ∫ t in (0 : ℝ)..T,
      (-(inner (𝕜 := ℝ) (gs.u t : L2VF_R3) (w : L2VF_R3)) * deriv ψ t +
        ψ t * (ν * stokesTestPairing_R3 (gs.u t : L2VF_R3) (w : L2VF_R3) +
          F.b (gs.u t) (gs.u t) w)) = 0 := by
  -- Schwartz witness of `w` (from the range-Schwartz field at the fixing level `n`).
  have hsdf : IsSchwartzDivFree_R3 w := by
    obtain ⟨ψw, hψw⟩ := 𝔊.range_schwartz n (w : L2VF_R3)
    exact ⟨ψw, fun j => by rw [hw]; exact hψw j⟩
  obtain ⟨ψw, hψw⟩ := hsdf
  -- Boundary values vanish.
  have hψ0 : ψ 0 = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => absurd (hψsupp h).1 (lt_irrefl 0))
  have hψT : ψ T = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => absurd (hψsupp h).2 (lt_irrefl T))
  -- ODE at forward times, and `ψ` is everywhere differentiable.
  have hode : ∀ t, 0 ≤ t →
      inner (𝕜 := ℝ) (deriv (fun s => (gs.u s : L2VF_R3)) t) (w : L2VF_R3) +
        ν * stokesTestPairing_R3 (gs.u t : L2VF_R3) (w : L2VF_R3) + F.b (gs.u t) (gs.u t) w = 0 :=
    fun t ht => gs.u_ode t ht w hw
  have hψderiv : ∀ x, HasDerivAt ψ (deriv ψ x) x :=
    fun x => hψC1.differentiable_one.differentiableAt.hasDerivAt
  -- Product rule for `h(t) = ⟪uₙ t, w⟫ ψ(t)` on forward time.
  have hprod : ∀ t ∈ Set.uIcc (0 : ℝ) T,
      HasDerivAt (fun s => inner (𝕜 := ℝ) (gs.u s : L2VF_R3) (w : L2VF_R3) * ψ s)
        (inner (𝕜 := ℝ) (deriv (fun s => (gs.u s : L2VF_R3)) t) (w : L2VF_R3) * ψ t +
          inner (𝕜 := ℝ) (gs.u t : L2VF_R3) (w : L2VF_R3) * deriv ψ t) t := by
    intro t ht
    rw [Set.uIcc_of_le hT.le, Set.mem_Icc] at ht
    have hinner : HasDerivAt (fun s => inner (𝕜 := ℝ) (gs.u s : L2VF_R3) (w : L2VF_R3))
        (inner (𝕜 := ℝ) (deriv (fun s => (gs.u s : L2VF_R3)) t) (w : L2VF_R3)) t := by
      have hda := (gs.u_hasDeriv t ht.1).inner (𝕜 := ℝ) (hasDerivAt_const t (w : L2VF_R3))
      simpa only [inner_zero_right, add_zero, zero_add] using hda
    exact hinner.mul (hψderiv t)
  -- The integrand equals `-h'(t)` on `[0,T]` (via the ODE).
  have hcongr : Set.EqOn
      (fun t => -(inner (𝕜 := ℝ) (gs.u t : L2VF_R3) (w : L2VF_R3)) * deriv ψ t +
        ψ t * (ν * stokesTestPairing_R3 (gs.u t : L2VF_R3) (w : L2VF_R3) +
          F.b (gs.u t) (gs.u t) w))
      (fun t => -(inner (𝕜 := ℝ) (deriv (fun s => (gs.u s : L2VF_R3)) t) (w : L2VF_R3) * ψ t +
        inner (𝕜 := ℝ) (gs.u t : L2VF_R3) (w : L2VF_R3) * deriv ψ t))
      (Set.uIcc (0 : ℝ) T) := by
    intro t ht
    rw [Set.uIcc_of_le hT.le, Set.mem_Icc] at ht
    have hns : ν * stokesTestPairing_R3 (gs.u t : L2VF_R3) (w : L2VF_R3) + F.b (gs.u t) (gs.u t) w
        = -(inner (𝕜 := ℝ) (deriv (fun s => (gs.u s : L2VF_R3)) t) (w : L2VF_R3)) := by
      have h := hode t ht.1; linarith
    simp only []; rw [hns]; ring
  -- Interval integrability of `h'` via continuity.
  have hAcont : ContinuousOn
      (fun t => inner (𝕜 := ℝ) (deriv (fun s => (gs.u s : L2VF_R3)) t) (w : L2VF_R3))
      (Set.Icc 0 T) := by
    have hst := (stokes_curve_continuousOn_R3 gs w ψw hψw).mono (Set.Icc_subset_Ici_self : Set.Icc (0:ℝ) T ⊆ Set.Ici 0)
    have hb := (bForm_curve_continuousOn_of_schwartz gs w ⟨ψw, hψw⟩).mono (Set.Icc_subset_Ici_self : Set.Icc (0:ℝ) T ⊆ Set.Ici 0)
    have hrhs : ContinuousOn
        (fun t => -(ν * stokesTestPairing_R3 (gs.u t : L2VF_R3) (w : L2VF_R3) +
          F.b (gs.u t) (gs.u t) w)) (Set.Icc 0 T) :=
      ((continuousOn_const.mul hst).add hb).neg
    refine hrhs.congr (fun t ht => ?_)
    have h := hode t ht.1; linarith
  have hinner_cont : ContinuousOn (fun t => inner (𝕜 := ℝ) (gs.u t : L2VF_R3) (w : L2VF_R3))
      (Set.Icc 0 T) :=
    ((galerkin_curve_continuous 𝔊 F ν u₀ n gs).inner continuousOn_const).mono (Set.Icc_subset_Ici_self : Set.Icc (0:ℝ) T ⊆ Set.Ici 0)
  have hh'_ii : IntervalIntegrable
      (fun t => inner (𝕜 := ℝ) (deriv (fun s => (gs.u s : L2VF_R3)) t) (w : L2VF_R3) * ψ t +
        inner (𝕜 := ℝ) (gs.u t : L2VF_R3) (w : L2VF_R3) * deriv ψ t) volume 0 T :=
    ((hAcont.mul hψC1.continuous.continuousOn).add
      (hinner_cont.mul hψC1.continuous_deriv_one.continuousOn)).intervalIntegrable_of_Icc hT.le
  -- FTC: `∫ h' = h T - h 0`, boundary terms vanish.
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hprod hh'_ii
  rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_neg, hFTC, hψ0, hψT]
  ring

set_option maxHeartbeats 1600000 in
/-- **W1: weak identity for the Aubin–Lions limit against a FIXED Galerkin test** (n→∞).

For a test `w` that is already a Galerkin test of the scheme `𝔊` (i.e. `𝔊.P N w = w` for
some level `N`), the limit curve `alPkg.u` satisfies the distributional Navier–Stokes integral
identity against `ψ ⊗ w`.

This is the first stage (W1) of the two-stage proof of `weakFormNS_limit_passage`:
- W1 (this lemma): n→∞ for FIXED Galerkin tests — no test approximation needed.
- W2 (PR-4, `weakFormNS_limit_passage` with `R3TestApproxH1` binder): extend to all Schwartz
  div-free tests via H¹-approximation.

Statement is VERBATIM from spike S4 (`weakFormNS_galerkinTest_spike`, issue #93 appendix). -/
theorem weakFormNS_galerkinTest_limit
    (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T)
    (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n)
    (alPkg : AubinLionsPackage_R3 𝔊 F ν T u₀ galSeq)
    (w : L2Sigma_R3) (hw : IsGalerkinTest_R3 𝔊 w)
    (ψ : Time → ℝ) (hψcs : HasCompactSupport ψ)
    (hψsupp : tsupport ψ ⊆ Set.Ioo 0 T) (hψC1 : ContDiff ℝ 1 ψ) :
    ∫ t in (0 : ℝ)..T,
      (-(inner (𝕜 := ℝ) ((alPkg.u t : L2VF_R3)) (w : L2VF_R3)) * deriv ψ t +
        ψ t * (ν * stokesTestPairing_R3 (alPkg.u t : L2VF_R3) (w : L2VF_R3) +
          F.b (alPkg.u t) (alPkg.u t) w)) = 0 := by
  classical
  obtain ⟨m, hm⟩ := hw
  -- Global Schwartz witness of the Galerkin test `w`.
  have hsdf : IsSchwartzDivFree_R3 w := by
    obtain ⟨ψ, hψ⟩ := 𝔊.range_schwartz m (w : L2VF_R3)
    exact ⟨ψ, fun j => by rw [← hm]; exact hψ j⟩
  obtain ⟨ψw, hψw⟩ := hsdf
  set M : ℝ := ‖(u₀ : L2VF_R3)‖ with hMdef
  have hM0 : 0 ≤ M := norm_nonneg _
  -- The Stokes functional as an inner product against a FIXED element `vElt`.
  obtain ⟨E, hE⟩ : ∃ E : Fin 3 → Lp ℝ 2 (volume : Measure Domain3),
      ∀ x : L2VF_R3, stokesTestPairing_R3 x (w : L2VF_R3)
        = ∑ j : Fin 3, inner (𝕜 := ℝ) (L2VF_projComponent_R3 j x) (E j) :=
    ⟨_, fun x => stokesTestPairing_R3_eq_sum_inner_negLap x (w : L2VF_R3) ψw hψw⟩
  set vElt : L2VF_R3 :=
    ∑ j : Fin 3, (L2VF_projComponent_R3 j).adjoint (E j) with hvElt
  have hstokes_inner : ∀ x : L2VF_R3,
      stokesTestPairing_R3 x (w : L2VF_R3) = inner (𝕜 := ℝ) vElt x := by
    intro x
    rw [hE x, hvElt, sum_inner]
    exact Finset.sum_congr rfl fun j _ => by
      rw [ContinuousLinearMap.adjoint_inner_left]; exact real_inner_comm _ _
  -- Convection-form bound constant (made nonnegative).
  obtain ⟨Cb, hCb⟩ := F.b_bound w ⟨ψw, hψw⟩
  set Cb' : ℝ := |Cb| with hCb'def
  have hCb'0 : 0 ≤ Cb' := abs_nonneg _
  have hbbound : ∀ u v : L2Sigma_R3,
      |F.b u v w| ≤ Cb' * ‖(u : L2VF_R3)‖ * ‖(v : L2VF_R3)‖ := fun u v =>
    (hCb u v).trans (by gcongr; exact le_abs_self _)
  -- Sup bounds for `ψ`, `ψ'` on `[0,T]`.
  obtain ⟨Mψ, hMψ⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    hψC1.continuous.continuousOn
  obtain ⟨Mψ', hMψ'⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    hψC1.continuous_deriv_one.continuousOn
  have hMψ0 : 0 ≤ Mψ := le_trans (norm_nonneg _) (hMψ 0 ⟨le_refl 0, hT.le⟩)
  -- Finite time measure and interval/measure bridge.
  set μ : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) T) with hμ
  haveI hμfin : IsFiniteMeasure μ := by
    rw [hμ]; refine isFiniteMeasure_restrict.2 ?_
    rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  have hbridge : ∀ g : ℝ → ℝ, ∫ t in (0 : ℝ)..T, g t = ∫ t, g t ∂μ := fun g => by
    rw [intervalIntegral.integral_of_le hT.le, hμ, Measure.restrict_congr_set Ioc_ae_eq_Icc]
  -- Approximant and limit integrands.
  set Fseq : ℕ → ℝ → ℝ := fun n t =>
    -(inner (𝕜 := ℝ) ((galSeq (alPkg.φ n)).u t : L2VF_R3) (w : L2VF_R3)) * deriv ψ t +
      ψ t * (ν * stokesTestPairing_R3 ((galSeq (alPkg.φ n)).u t : L2VF_R3) (w : L2VF_R3) +
        F.b ((galSeq (alPkg.φ n)).u t) ((galSeq (alPkg.φ n)).u t) w) with hFseq
  set flim : ℝ → ℝ := fun t =>
    -(inner (𝕜 := ℝ) (alPkg.u t : L2VF_R3) (w : L2VF_R3)) * deriv ψ t +
      ψ t * (ν * stokesTestPairing_R3 (alPkg.u t : L2VF_R3) (w : L2VF_R3) +
        F.b (alPkg.u t) (alPkg.u t) w) with hflim
  -- Constant dominator.
  set D : ℝ := M * ‖(w : L2VF_R3)‖ * Mψ' + Mψ * (ν * ‖vElt‖ * M + Cb' * M * M) with hD
  -- (1) Measurability of each approximant integrand.
  have hcontFseq : ∀ n, ContinuousOn (Fseq n) (Set.Icc (0 : ℝ) T) := by
    intro n
    have hc := (weakFormNS_integrand_continuousOn_R3 (galSeq (alPkg.φ n)) w ⟨ψw, hψw⟩ ψ hψC1).mono
      (Set.Icc_subset_Ici_self : Set.Icc (0:ℝ) T ⊆ Set.Ici 0)
    simpa only [hFseq] using hc
  have hmeasFseq : ∀ n, AEStronglyMeasurable (Fseq n) μ := fun n => by
    rw [hμ]; exact (hcontFseq n).aestronglyMeasurable measurableSet_Icc
  -- (2) Uniform dominator bound.
  have hae_ge : ∀ᵐ t ∂μ, (0 : ℝ) ≤ t := by
    rw [hμ]; exact ae_restrict_of_forall_mem measurableSet_Icc fun t ht => ht.1
  have hae_Icc : ∀ᵐ t ∂μ, t ∈ Set.Icc (0 : ℝ) T := by
    rw [hμ]; exact ae_restrict_mem measurableSet_Icc
  have hbound : ∀ n, ∀ᵐ t ∂μ, ‖Fseq n t‖ ≤ D := by
    intro n
    filter_upwards [hae_ge, hae_Icc] with t htg htIcc
    have hUn : ‖((galSeq (alPkg.φ n)).u t : L2VF_R3)‖ ≤ M := by
      rw [hMdef]; exact galerkin_norm_le_u0 𝔊 F ν u₀ (alPkg.φ n) (galSeq (alPkg.φ n)) htg
    have hψb : |ψ t| ≤ Mψ := by rw [← Real.norm_eq_abs]; exact hMψ t htIcc
    have hψ'b : |deriv ψ t| ≤ Mψ' := by rw [← Real.norm_eq_abs]; exact hMψ' t htIcc
    have hinb : |inner (𝕜 := ℝ) ((galSeq (alPkg.φ n)).u t : L2VF_R3) (w : L2VF_R3)|
        ≤ M * ‖(w : L2VF_R3)‖ := (abs_real_inner_le_norm _ _).trans (by gcongr)
    have hstok : |stokesTestPairing_R3 ((galSeq (alPkg.φ n)).u t : L2VF_R3) (w : L2VF_R3)|
        ≤ ‖vElt‖ * M := by
      rw [hstokes_inner]; exact (abs_real_inner_le_norm _ _).trans (by gcongr)
    have hbb : |F.b ((galSeq (alPkg.φ n)).u t) ((galSeq (alPkg.φ n)).u t) w| ≤ Cb' * M * M := by
      refine (hbbound _ _).trans ?_; gcongr
    rw [hFseq, Real.norm_eq_abs]
    calc |(-(inner (𝕜 := ℝ) ((galSeq (alPkg.φ n)).u t : L2VF_R3) (w : L2VF_R3))) * deriv ψ t +
            ψ t * (ν * stokesTestPairing_R3 ((galSeq (alPkg.φ n)).u t : L2VF_R3) (w : L2VF_R3) +
              F.b ((galSeq (alPkg.φ n)).u t) ((galSeq (alPkg.φ n)).u t) w)|
        ≤ |(-(inner (𝕜 := ℝ) ((galSeq (alPkg.φ n)).u t : L2VF_R3) (w : L2VF_R3))) * deriv ψ t|
          + |ψ t * (ν * stokesTestPairing_R3 ((galSeq (alPkg.φ n)).u t : L2VF_R3) (w : L2VF_R3) +
              F.b ((galSeq (alPkg.φ n)).u t) ((galSeq (alPkg.φ n)).u t) w)| := abs_add_le _ _
      _ ≤ M * ‖(w : L2VF_R3)‖ * Mψ' + Mψ * (ν * ‖vElt‖ * M + Cb' * M * M) := by
          refine add_le_add ?_ ?_
          · rw [abs_mul, abs_neg]
            exact mul_le_mul hinb hψ'b (abs_nonneg _) (mul_nonneg hM0 (norm_nonneg _))
          · rw [abs_mul]
            refine mul_le_mul hψb ?_ (abs_nonneg _) hMψ0
            calc |ν * stokesTestPairing_R3 ((galSeq (alPkg.φ n)).u t : L2VF_R3) (w : L2VF_R3) +
                    F.b ((galSeq (alPkg.φ n)).u t) ((galSeq (alPkg.φ n)).u t) w|
                ≤ |ν * stokesTestPairing_R3 ((galSeq (alPkg.φ n)).u t : L2VF_R3) (w : L2VF_R3)|
                  + |F.b ((galSeq (alPkg.φ n)).u t) ((galSeq (alPkg.φ n)).u t) w| := abs_add_le _ _
              _ = ν * |stokesTestPairing_R3 ((galSeq (alPkg.φ n)).u t : L2VF_R3) (w : L2VF_R3)|
                  + |F.b ((galSeq (alPkg.φ n)).u t) ((galSeq (alPkg.φ n)).u t) w| := by
                    rw [abs_mul, abs_of_nonneg hν.le]
              _ ≤ ν * (‖vElt‖ * M) + Cb' * M * M :=
                    add_le_add (mul_le_mul_of_nonneg_left hstok hν.le) hbb
              _ = ν * ‖vElt‖ * M + Cb' * M * M := by ring
      _ = D := by rw [hD]
  have hDint : Integrable (fun _ : ℝ => D) μ := integrable_const _
  -- (3) Pointwise a.e.-t convergence of the integrands.
  have hballconv : ∀ᵐ t ∂μ, ∀ k : ℕ,
      Filter.Tendsto (fun n => restrictToBall (k : ℝ) ((galSeq (alPkg.φ n)).u t : L2VF_R3))
        Filter.atTop (nhds (restrictToBall (k : ℝ) (alPkg.u t : L2VF_R3))) := by
    rw [hμ]; exact ae_all_iff.2 fun k => alPkg.strong_convergence_ae k
  have hnormlim : ∀ᵐ t ∂μ, ‖(alPkg.u t : L2VF_R3)‖ ≤ M := by
    rw [hμ]
    filter_upwards [kineticEnergy_lsc_bound 𝔊 F ν T u₀ galSeq alPkg] with t ht
    have hsq : ‖(alPkg.u t : L2VF_R3)‖ ^ 2 ≤ M ^ 2 := by rw [hMdef]; nlinarith [ht]
    exact le_of_sq_le_sq hsq hM0
  have hpt : ∀ᵐ t ∂μ, Filter.Tendsto (fun n => Fseq n t) Filter.atTop (nhds (flim t)) := by
    filter_upwards [hballconv, hnormlim, hae_ge] with t hball hnorm htg
    have hbd : ∀ n, ‖((galSeq (alPkg.φ n)).u t : L2VF_R3)‖ ≤ M := fun n => by
      rw [hMdef]; exact galerkin_norm_le_u0 𝔊 F ν u₀ (alPkg.φ n) (galSeq (alPkg.φ n)) htg
    have hlin : Filter.Tendsto
        (fun n => inner (𝕜 := ℝ) ((galSeq (alPkg.φ n)).u t : L2VF_R3) (w : L2VF_R3))
        Filter.atTop (nhds (inner (𝕜 := ℝ) (alPkg.u t : L2VF_R3) (w : L2VF_R3))) := by
      have h := inner_tendsto_of_perball (w : L2VF_R3)
        (fun n => ((galSeq (alPkg.φ n)).u t : L2VF_R3)) (alPkg.u t : L2VF_R3) M hM0 hbd hnorm hball
      simpa only [real_inner_comm (w : L2VF_R3)] using h
    have hstk : Filter.Tendsto
        (fun n => stokesTestPairing_R3 ((galSeq (alPkg.φ n)).u t : L2VF_R3) (w : L2VF_R3))
        Filter.atTop (nhds (stokesTestPairing_R3 (alPkg.u t : L2VF_R3) (w : L2VF_R3))) := by
      simp only [hstokes_inner]
      exact inner_tendsto_of_perball vElt
        (fun n => ((galSeq (alPkg.φ n)).u t : L2VF_R3)) (alPkg.u t : L2VF_R3) M hM0 hbd hnorm hball
    have hnl : Filter.Tendsto (fun n => F.b ((galSeq (alPkg.φ n)).u t) ((galSeq (alPkg.φ n)).u t) w)
        Filter.atTop (nhds (F.b (alPkg.u t) (alPkg.u t) w)) :=
      fb_tendsto_of_perball F w ⟨ψw, hψw⟩ (fun n => (galSeq (alPkg.φ n)).u t) (alPkg.u t)
        M hM0 hbd hnorm hball
    simp only [hFseq, hflim]
    exact (hlin.neg.mul_const (deriv ψ t)).add
      (((hstk.const_mul ν).add hnl).const_mul (ψ t))
  -- (4) Dominated convergence: approximant integrals converge to the limit integral.
  have hlim := tendsto_integral_of_dominated_convergence (fun _ => D) hmeasFseq hDint hbound hpt
  -- (5) The approximant integrals are eventually `0` (per-level IBP identity).
  have hzero_ev : ∀ᶠ n in Filter.atTop, ∫ t, Fseq n t ∂μ = 0 := by
    filter_upwards [Filter.eventually_ge_atTop m] with n hn
    have hproj : (w : L2VF_R3) = 𝔊.P (alPkg.φ n) (w : L2VF_R3) :=
      (𝔊.mono_range m (alPkg.φ n) (le_trans hn alPkg.φ_mono.le_apply) (w : L2VF_R3) hm).symm
    rw [← hbridge (Fseq n)]; simp only [hFseq]
    exact galerkin_weakFormNS_zero_R3 T hT (galSeq (alPkg.φ n)) w hproj ψ hψsupp hψC1
  have hlim0 : Filter.Tendsto (fun n => ∫ t, Fseq n t ∂μ) Filter.atTop (nhds 0) :=
    Filter.Tendsto.congr' (hzero_ev.mono fun n h => h.symm) tendsto_const_nhds
  have hflim0 : ∫ t, flim t ∂μ = 0 := tendsto_nhds_unique hlim hlim0
  rw [hbridge flim]; exact hflim0

/-! ### W2 helper lemmas (PR-4, issue #4): extend W1 from Galerkin tests to Schwartz tests -/

/-- Elementary bound `√y ≤ 1 + y` for `y ≥ 0` (used to dominate `√V₁` by the integrable
`1 + V₁`). -/
private theorem sqrt_le_one_add_self_R3 (y : ℝ) (hy : 0 ≤ y) : Real.sqrt y ≤ 1 + y := by
  have hle : y ≤ (1 + y) ^ 2 := by nlinarith [sq_nonneg y]
  calc Real.sqrt y ≤ Real.sqrt ((1 + y) ^ 2) := Real.sqrt_le_sqrt hle
    _ = |1 + y| := Real.sqrt_sq_eq_abs _
    _ = 1 + y := abs_of_nonneg (by linarith)

/-- Elementary bound `y^{1/4}·√y = y^{3/4} ≤ 1 + y` for `y ≥ 0` (used to dominate the
Ladyzhenskaya factor `V₁^{1/4}·√V₁` by the integrable `1 + V₁`). -/
private theorem rpow_quarter_mul_sqrt_le_R3 (y : ℝ) (hy0 : 0 ≤ y) :
    y ^ (1 / 4 : ℝ) * Real.sqrt y ≤ 1 + y := by
  rcases eq_or_lt_of_le hy0 with h | h
  · rw [← h]; simp
  · have hcomb : y ^ (1 / 4 : ℝ) * Real.sqrt y = y ^ (3 / 4 : ℝ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add h]; norm_num
    rw [hcomb]
    rcases le_total y 1 with hle | hge
    · have : y ^ (3 / 4 : ℝ) ≤ 1 := Real.rpow_le_one hy0 hle (by norm_num)
      linarith
    · have : y ^ (3 / 4 : ℝ) ≤ y ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hge (by norm_num)
      rw [Real.rpow_one] at this; linarith

/-- `IsSchwartzDivFree_R3` is closed under subtraction (add + `(-1)`-smul). -/
private theorem isSchwartzDivFree_R3_sub (u v : L2Sigma_R3)
    (hu : IsSchwartzDivFree_R3 u) (hv : IsSchwartzDivFree_R3 v) :
    IsSchwartzDivFree_R3 (u - v) := by
  rw [sub_eq_add_neg, ← neg_one_smul ℝ v]
  exact isSchwartzDivFree_add u _ hu (isSchwartzDivFree_smul (-1) v hv)

/-- `memH1VF_R3` is closed under subtraction (add + `(-1)`-smul; public mirror of the
`private` `GalerkinBasisH1.memH1VF_R3_sub`). -/
private theorem memH1VF_R3_sub_local {u v : L2VF_R3} (hu : memH1VF_R3 u) (hv : memH1VF_R3 v) :
    memH1VF_R3 (u - v) := by
  rw [sub_eq_add_neg, ← neg_one_smul ℝ v]
  exact memH1VF_R3_add hu (memH1VF_R3_smul (-1) hv)

/-- Right-slot subtraction-linearity of the viscous pairing on `H¹` fields, via the
weighted-Fourier representation (`stokesTestPairing_eq_sum_inner_wFC` +
`weightedFourierComponent_sub`). -/
private theorem stokesTestPairing_R3_sub_right (u a b : L2VF_R3)
    (hu : memH1VF_R3 u) (ha : memH1VF_R3 a) (hb : memH1VF_R3 b) :
    stokesTestPairing_R3 u (a - b)
      = stokesTestPairing_R3 u a - stokesTestPairing_R3 u b := by
  have hab : memH1VF_R3 (a - b) := memH1VF_R3_sub_local ha hb
  rw [stokesTestPairing_eq_sum_inner_wFC u (a - b) hu hab,
    stokesTestPairing_eq_sum_inner_wFC u a hu ha,
    stokesTestPairing_eq_sum_inner_wFC u b hu hb, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [weightedFourierComponent_sub a b ha hb hab j, inner_sub_left, Complex.sub_re]

/-- Third-slot subtraction-linearity of the convection form (from `b_add_3`/`b_smul_3`). -/
private theorem bForm_R3_sub_3 {𝔊 : R3GalerkinScheme} (F : R3NSForms 𝔊) (u v a b : L2Sigma_R3) :
    F.b u v (a - b) = F.b u v a - F.b u v b := by
  rw [sub_eq_add_neg a b, ← neg_one_smul ℝ b, F.b_add_3, F.b_smul_3]; ring

set_option maxHeartbeats 1600000 in
/-- **W2 nonlinear-limit convection bound (PR-4).** For any Schwartz divergence-free test
`z`, the limit-curve convection functional `t ↦ F.b (u t) (u t) z` is integrable on `[0,T]`
and its `L¹`-norm is controlled by `√(V₁ z)`, with a `z`-uniform constant `K`.

The bound descends from the Galerkin curves via `fb_tendsto_of_perball` + Fatou-in-time
(`lintegral_liminf_le'`): each approximant obeys the Ladyzhenskaya energy bound
`|b(uₙ,uₙ,z)| ≤ C_b‖uₙ‖^{1/2}(V₁ uₙ)^{3/4}√(V₁ z)` (`convIntegralSchwartz_bound_energy` +
`F.b_galerkin`), whose time integral is `n`-uniformly `≤ K·√(V₁ z)` after the crude
`‖uₙ‖^{1/2}(V₁ uₙ)^{3/4} ≤ √‖u₀‖·(1 + V₁ uₙ)` domination and `reg_bound`. -/
private theorem bForm_limit_convection_bound
    (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T)
    (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n)
    (alPkg : AubinLionsPackage_R3 𝔊 F ν T u₀ galSeq) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z : L2Sigma_R3, IsSchwartzDivFree_R3 z →
      Integrable (fun t => F.b (alPkg.u t) (alPkg.u t) z)
          (volume.restrict (Set.Icc (0 : ℝ) T)) ∧
      ∫ t, ‖F.b (alPkg.u t) (alPkg.u t) z‖ ∂(volume.restrict (Set.Icc (0 : ℝ) T))
          ≤ K * Real.sqrt (viscousFormSq_R3 1 (z : L2VF_R3)) := by
  classical
  set μ : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) T) with hμ
  haveI hμfin : IsFiniteMeasure μ := by
    rw [hμ]; refine isFiniteMeasure_restrict.2 ?_
    rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  set M : ℝ := ‖(u₀ : L2VF_R3)‖ with hMdef
  have hM0 : 0 ≤ M := norm_nonneg _
  have hbridge : ∀ g : ℝ → ℝ, ∫ t in (0 : ℝ)..T, g t = ∫ t, g t ∂μ := fun g => by
    rw [intervalIntegral.integral_of_le hT.le, hμ, Measure.restrict_congr_set Ioc_ae_eq_Icc]
  have hae_ge : ∀ᵐ t ∂μ, (0 : ℝ) ≤ t := by
    rw [hμ]; exact ae_restrict_of_forall_mem measurableSet_Icc fun t ht => ht.1
  obtain ⟨C_b, hC_b0, hC_b⟩ := convIntegralSchwartz_bound_energy
  set K : ℝ := C_b * Real.sqrt M * (T + ν⁻¹ * ((1 / 2 : ℝ) * M ^ 2)) with hKdef
  have hK0 : 0 ≤ K := by
    rw [hKdef]
    refine mul_nonneg (mul_nonneg hC_b0 (Real.sqrt_nonneg _)) ?_
    exact add_nonneg hT.le (mul_nonneg (inv_nonneg.2 hν.le) (by positivity))
  refine ⟨K, hK0, ?_⟩
  intro z hz
  obtain ⟨ψz, hψz⟩ := hz
  set S : ℝ := Real.sqrt (viscousFormSq_R3 1 (z : L2VF_R3)) with hS
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  -- a.e.-in-time facts about the limit curve.
  have hballconv : ∀ᵐ t ∂μ, ∀ k : ℕ,
      Filter.Tendsto (fun n => restrictToBall (k : ℝ) ((galSeq (alPkg.φ n)).u t : L2VF_R3))
        Filter.atTop (nhds (restrictToBall (k : ℝ) (alPkg.u t : L2VF_R3))) := by
    rw [hμ]; exact ae_all_iff.2 fun k => alPkg.strong_convergence_ae k
  have hnorm_ulim : ∀ᵐ t ∂μ, ‖(alPkg.u t : L2VF_R3)‖ ≤ M := by
    rw [hμ]
    filter_upwards [kineticEnergy_lsc_bound 𝔊 F ν T u₀ galSeq alPkg] with t ht
    have hsq : ‖(alPkg.u t : L2VF_R3)‖ ^ 2 ≤ M ^ 2 := by rw [hMdef]; nlinarith [ht]
    exact le_of_sq_le_sq hsq hM0
  have haetend : ∀ᵐ t ∂μ, Filter.Tendsto
      (fun n => F.b ((galSeq (alPkg.φ n)).u t) ((galSeq (alPkg.φ n)).u t) z) Filter.atTop
      (nhds (F.b (alPkg.u t) (alPkg.u t) z)) := by
    filter_upwards [hae_ge, hnorm_ulim, hballconv] with t htg hnorm hball
    have hbd : ∀ n, ‖((galSeq (alPkg.φ n)).u t : L2VF_R3)‖ ≤ M := fun n => by
      rw [hMdef]; exact galerkin_norm_le_u0 𝔊 F ν u₀ (alPkg.φ n) (galSeq (alPkg.φ n)) htg
    exact fb_tendsto_of_perball F z ⟨ψz, hψz⟩ (fun n => (galSeq (alPkg.φ n)).u t) (alPkg.u t)
      M hM0 hbd hnorm hball
  -- Per-level crude bound `|b(uₙ,uₙ,z)| ≤ C_b·√M·(1 + V₁ uₙ)·S` on forward time.
  have hFb_crude_pt : ∀ n t, 0 ≤ t →
      |F.b ((galSeq (alPkg.φ n)).u t) ((galSeq (alPkg.φ n)).u t) z|
        ≤ C_b * Real.sqrt M
            * (1 + viscousFormSq_R3 1 ((galSeq (alPkg.φ n)).u t : L2VF_R3)) * S := by
    intro n t ht
    obtain ⟨ψu, hψu0⟩ := 𝔊.range_schwartz (alPkg.φ n) ((galSeq (alPkg.φ n)).u t : L2VF_R3)
    have hψu : ∀ j : Fin 3, L2VF_projComponent_R3 j ((galSeq (alPkg.φ n)).u t : L2VF_R3)
        = (ψu j).toLp 2 (volume : Measure Domain3) := by
      intro j; rw [(galSeq (alPkg.φ n)).u_inVn t]; exact hψu0 j
    have hmix : |F.b ((galSeq (alPkg.φ n)).u t) ((galSeq (alPkg.φ n)).u t) z|
        ≤ C_b * ‖((galSeq (alPkg.φ n)).u t : L2VF_R3)‖ ^ (1 / 2 : ℝ)
            * (viscousFormSq_R3 1 ((galSeq (alPkg.φ n)).u t : L2VF_R3)) ^ (1 / 4 : ℝ)
            * Real.sqrt (viscousFormSq_R3 1 ((galSeq (alPkg.φ n)).u t : L2VF_R3)) * S := by
      rw [F.b_galerkin ψu ψu ψz ((galSeq (alPkg.φ n)).u t) ((galSeq (alPkg.φ n)).u t) z
        hψu hψu hψz]
      exact hC_b _ _ _ ψu ψu ψz hψu hψu hψz
    refine hmix.trans ?_
    set V : ℝ := viscousFormSq_R3 1 ((galSeq (alPkg.φ n)).u t : L2VF_R3) with hV
    have hV0 : 0 ≤ V := viscousFormSq_R3_nonneg zero_le_one _
    have h1 : ‖((galSeq (alPkg.φ n)).u t : L2VF_R3)‖ ^ (1 / 2 : ℝ) ≤ Real.sqrt M := by
      rw [Real.sqrt_eq_rpow]
      refine Real.rpow_le_rpow (norm_nonneg _) ?_ (by norm_num)
      rw [hMdef]; exact galerkin_norm_le_u0 𝔊 F ν u₀ (alPkg.φ n) (galSeq (alPkg.φ n)) ht
    have h2 : V ^ (1 / 4 : ℝ) * Real.sqrt V ≤ 1 + V := rpow_quarter_mul_sqrt_le_R3 V hV0
    calc C_b * ‖((galSeq (alPkg.φ n)).u t : L2VF_R3)‖ ^ (1 / 2 : ℝ)
            * V ^ (1 / 4 : ℝ) * Real.sqrt V * S
        = (C_b * S)
            * (‖((galSeq (alPkg.φ n)).u t : L2VF_R3)‖ ^ (1 / 2 : ℝ) * (V ^ (1 / 4 : ℝ) * Real.sqrt V)) := by
          ring
      _ ≤ (C_b * S) * (Real.sqrt M * (1 + V)) := by
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC_b0 hS0)
          exact mul_le_mul h1 h2 (mul_nonneg (Real.rpow_nonneg hV0 _) (Real.sqrt_nonneg _))
            (Real.sqrt_nonneg _)
      _ = C_b * Real.sqrt M * (1 + V) * S := by ring
  have hFb_crude : ∀ n, ∀ᵐ t ∂μ,
      ‖F.b ((galSeq (alPkg.φ n)).u t) ((galSeq (alPkg.φ n)).u t) z‖
        ≤ C_b * Real.sqrt M
            * (1 + viscousFormSq_R3 1 ((galSeq (alPkg.φ n)).u t : L2VF_R3)) * S := by
    intro n; filter_upwards [hae_ge] with t htg
    rw [Real.norm_eq_abs]; exact hFb_crude_pt n t htg
  -- Approximant viscous forms are continuous ⇒ integrable on `[0,T]`.
  have hV1_int : ∀ n,
      Integrable (fun t => viscousFormSq_R3 1 ((galSeq (alPkg.φ n)).u t : L2VF_R3)) μ := by
    intro n; rw [hμ]
    exact ((galerkin_viscous_curve_continuousOn (galSeq (alPkg.φ n))).mono
      Set.Icc_subset_Ici_self).integrableOn_Icc
  -- The dominating integrand and its `n`-uniform integral cap.
  have hGcrude_nonneg : ∀ n t, 0 ≤ C_b * Real.sqrt M
      * (1 + viscousFormSq_R3 1 ((galSeq (alPkg.φ n)).u t : L2VF_R3)) * S := by
    intro n t
    refine mul_nonneg (mul_nonneg (mul_nonneg hC_b0 (Real.sqrt_nonneg _)) ?_) hS0
    have := viscousFormSq_R3_nonneg zero_le_one ((galSeq (alPkg.φ n)).u t : L2VF_R3)
    linarith
  have hGcrude_int : ∀ n, Integrable (fun t => C_b * Real.sqrt M
      * (1 + viscousFormSq_R3 1 ((galSeq (alPkg.φ n)).u t : L2VF_R3)) * S) μ := by
    intro n
    exact (((integrable_const (1 : ℝ)).add (hV1_int n)).const_mul (C_b * Real.sqrt M)).mul_const S
  have hV1_reg : ∀ n, ∫ t, viscousFormSq_R3 1 ((galSeq (alPkg.φ n)).u t : L2VF_R3) ∂μ
      ≤ ν⁻¹ * ((1 / 2 : ℝ) * M ^ 2) := by
    intro n
    have hrb := (galSeq (alPkg.φ n)).reg_bound T hT
    have hscale : ∀ s, viscousFormSq_R3 ν ((galSeq (alPkg.φ n)).u s : L2VF_R3)
        = ν * viscousFormSq_R3 1 ((galSeq (alPkg.φ n)).u s : L2VF_R3) := by
      intro s; rw [viscousFormSq_R3_eq_smul, smul_eq_mul]
    rw [intervalIntegral.integral_congr (g := fun s => ν * viscousFormSq_R3 1
        ((galSeq (alPkg.φ n)).u s : L2VF_R3)) (fun s _ => hscale s),
      intervalIntegral.integral_const_mul, hbridge] at hrb
    rw [hMdef]; rwa [le_inv_mul_iff₀ hν]
  have hMuUniv : (μ Set.univ).toReal = T := by
    rw [hμ, Measure.restrict_apply_univ, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
    ring
  have hGcrude_int_bound : ∀ n, ∫ t, C_b * Real.sqrt M
      * (1 + viscousFormSq_R3 1 ((galSeq (alPkg.φ n)).u t : L2VF_R3)) * S ∂μ ≤ K * S := by
    intro n
    have heq : ∫ t, C_b * Real.sqrt M
        * (1 + viscousFormSq_R3 1 ((galSeq (alPkg.φ n)).u t : L2VF_R3)) * S ∂μ
        = C_b * Real.sqrt M * S
            * (∫ t, (1 + viscousFormSq_R3 1 ((galSeq (alPkg.φ n)).u t : L2VF_R3)) ∂μ) := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      ring
    rw [heq]
    have hintadd : ∫ t, (1 + viscousFormSq_R3 1 ((galSeq (alPkg.φ n)).u t : L2VF_R3)) ∂μ
        = T + ∫ t, viscousFormSq_R3 1 ((galSeq (alPkg.φ n)).u t : L2VF_R3) ∂μ := by
      rw [integral_add (integrable_const 1) (hV1_int n), integral_const, measureReal_def,
        hMuUniv, smul_eq_mul, mul_one]
    rw [hintadd, hKdef, hMdef]
    have hnn : (0 : ℝ) ≤ C_b * Real.sqrt ‖(u₀ : L2VF_R3)‖ * S :=
      mul_nonneg (mul_nonneg hC_b0 (Real.sqrt_nonneg _)) hS0
    have hcap := hV1_reg n
    rw [hMdef] at hcap
    calc C_b * Real.sqrt ‖(u₀ : L2VF_R3)‖ * S
            * (T + ∫ t, viscousFormSq_R3 1 ((galSeq (alPkg.φ n)).u t : L2VF_R3) ∂μ)
        ≤ C_b * Real.sqrt ‖(u₀ : L2VF_R3)‖ * S
            * (T + ν⁻¹ * ((1 / 2 : ℝ) * ‖(u₀ : L2VF_R3)‖ ^ 2)) := by
          refine mul_le_mul_of_nonneg_left ?_ hnn
          linarith [hcap]
      _ = C_b * Real.sqrt ‖(u₀ : L2VF_R3)‖
            * (T + ν⁻¹ * ((1 / 2 : ℝ) * ‖(u₀ : L2VF_R3)‖ ^ 2)) * S := by ring
  -- Measurability of the approximant and limit integrands.
  have hFb_meas_n : ∀ n, AEStronglyMeasurable
      (fun t => F.b ((galSeq (alPkg.φ n)).u t) ((galSeq (alPkg.φ n)).u t) z) μ := by
    intro n; rw [hμ]
    exact ((bForm_curve_continuousOn_of_schwartz (galSeq (alPkg.φ n)) z ⟨ψz, hψz⟩).mono
      Set.Icc_subset_Ici_self).aestronglyMeasurable measurableSet_Icc
  have hFb_meas : AEStronglyMeasurable (fun t => F.b (alPkg.u t) (alPkg.u t) z) μ :=
    aestronglyMeasurable_of_tendsto_ae Filter.atTop hFb_meas_n haetend
  -- Per-`n` `ENNReal` cap.
  have hlint_n : ∀ n,
      ∫⁻ t, ENNReal.ofReal ‖F.b ((galSeq (alPkg.φ n)).u t) ((galSeq (alPkg.φ n)).u t) z‖ ∂μ
        ≤ ENNReal.ofReal (K * S) := by
    intro n
    calc ∫⁻ t, ENNReal.ofReal ‖F.b ((galSeq (alPkg.φ n)).u t) ((galSeq (alPkg.φ n)).u t) z‖ ∂μ
        ≤ ∫⁻ t, ENNReal.ofReal (C_b * Real.sqrt M
            * (1 + viscousFormSq_R3 1 ((galSeq (alPkg.φ n)).u t : L2VF_R3)) * S) ∂μ := by
          refine lintegral_mono_ae ?_
          filter_upwards [hFb_crude n] with t ht
          exact ENNReal.ofReal_le_ofReal ht
      _ = ENNReal.ofReal (∫ t, C_b * Real.sqrt M
            * (1 + viscousFormSq_R3 1 ((galSeq (alPkg.φ n)).u t : L2VF_R3)) * S ∂μ) :=
          (ofReal_integral_eq_lintegral_ofReal (hGcrude_int n)
            (Filter.Eventually.of_forall (hGcrude_nonneg n))).symm
      _ ≤ ENNReal.ofReal (K * S) := ENNReal.ofReal_le_ofReal (hGcrude_int_bound n)
  -- Fatou passage to the limit curve.
  have hlim_lint : ∫⁻ t, ENNReal.ofReal ‖F.b (alPkg.u t) (alPkg.u t) z‖ ∂μ
      ≤ ENNReal.ofReal (K * S) := by
    calc ∫⁻ t, ENNReal.ofReal ‖F.b (alPkg.u t) (alPkg.u t) z‖ ∂μ
        = ∫⁻ t, Filter.atTop.liminf
            (fun n => ENNReal.ofReal ‖F.b ((galSeq (alPkg.φ n)).u t)
              ((galSeq (alPkg.φ n)).u t) z‖) ∂μ := by
          refine lintegral_congr_ae ?_
          filter_upwards [haetend] with t ht
          have htn : Filter.Tendsto
              (fun n => ENNReal.ofReal ‖F.b ((galSeq (alPkg.φ n)).u t)
                ((galSeq (alPkg.φ n)).u t) z‖) Filter.atTop
              (nhds (ENNReal.ofReal ‖F.b (alPkg.u t) (alPkg.u t) z‖)) :=
            (ENNReal.continuous_ofReal.tendsto _).comp ht.norm
          exact htn.liminf_eq.symm
      _ ≤ Filter.atTop.liminf (fun n => ∫⁻ t,
            ENNReal.ofReal ‖F.b ((galSeq (alPkg.φ n)).u t) ((galSeq (alPkg.φ n)).u t) z‖ ∂μ) :=
          lintegral_liminf_le' (fun n => (hFb_meas_n n).norm.aemeasurable.ennreal_ofReal)
      _ ≤ ENNReal.ofReal (K * S) := by
          refine le_trans liminf_le_limsup ?_
          exact limsup_le_of_le isCobounded_le_of_bot (Filter.Eventually.of_forall hlint_n)
  -- Integrability of the norm (hence of `F.b`) and the real-integral bound.
  have hNormInt : Integrable (fun t => ‖F.b (alPkg.u t) (alPkg.u t) z‖) μ := by
    refine ⟨hFb_meas.norm, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun t => norm_nonneg _)]
    exact lt_of_le_of_lt hlim_lint ENNReal.ofReal_lt_top
  have hInt : Integrable (fun t => F.b (alPkg.u t) (alPkg.u t) z) μ :=
    (integrable_norm_iff hFb_meas).mp hNormInt
  refine ⟨hInt, ?_⟩
  have hofeq : ENNReal.ofReal (∫ t, ‖F.b (alPkg.u t) (alPkg.u t) z‖ ∂μ)
      = ∫⁻ t, ENNReal.ofReal ‖F.b (alPkg.u t) (alPkg.u t) z‖ ∂μ :=
    ofReal_integral_eq_lintegral_ofReal hNormInt
      (Filter.Eventually.of_forall fun t => norm_nonneg _)
  have hnnKS : (0 : ℝ) ≤ K * S := mul_nonneg hK0 hS0
  have := hofeq ▸ hlim_lint
  rwa [ENNReal.ofReal_le_ofReal_iff hnnKS] at this

set_option maxHeartbeats 2400000 in
/-- **WeakFormNS limit passage (conjunct 2 of `galerkin_limit_passage_R3`).**

The Aubin–Lions limit curve `alPkg.u` satisfies the distributional Navier–Stokes weak equation
`WeakFormNS ν T (r3Evolution 𝔊 F) alPkg.u`.  This is exactly the second conjunct of the
`galerkin_limit_passage_R3` axiom (taking the good representative `u := alPkg.u`), and the
`weak_eq_limit` field of `GalerkinCompactnessPackageFull_R3`.

The W2 test-extension proof (issue #4 PR-4) threads `htest : R3TestApproxH1 𝔊` to approximate
the arbitrary Schwartz test by Galerkin tests in the `L² + √V₁` graph seminorm, then squeezes
the difference of the weak-form functionals via `bForm_limit_convection_bound` (nonlinear),
`stokesTestPairing_abs_le` (viscous), and `abs_real_inner_le_norm` (kinetic). -/
theorem weakFormNS_limit_passage
    (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T)
    (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n)
    (alPkg : AubinLionsPackage_R3 𝔊 F ν T u₀ galSeq)
    (htest : R3TestApproxH1 𝔊) : -- (htest used in proof, PR-4)
    WeakFormNS ν T (r3Evolution 𝔊 F) alPkg.u := by
  -- Unfold `WeakFormNS` (the `r3Evolution` evolution: `viscousForm = stokesTestPairing_R3`,
  -- `convForm = F.b`, `isTest = IsSchwartzDivFree_R3`).  Intro the admissible test data.
  intro ψ hψcs hψsupp hψC1 w hw
  -- `hw : IsSchwartzDivFree_R3 w` (the `r3Evolution.isTest` field).  The integrand to be shown to
  -- integrate to `0` over `[0,T]` is, with the `r3Evolution` fields substituted,
  --   `-(⟪alPkg.u t, w⟫) · ψ'(t) + ψ(t) · (ν · stokesTestPairing_R3 (alPkg.u t) w
  --       + F.b (alPkg.u t) (alPkg.u t) w)`.
  -- Strategy (W2): the abstract test functional `Φ(y) := ∫₀ᵀ [integrand with test y]` vanishes on
  -- every Galerkin test (`weakFormNS_galerkinTest_limit`, W1).  By right-linearity of the three
  -- slots, `Φ(w) = Φ(vₖ) + Φ(w - vₖ) = Φ(w - vₖ)` for any Galerkin test `vₖ`, and `htest` supplies
  -- `vₖ` with `‖vₖ - w‖ + √V₁(vₖ - w) → 0`.  The difference `|Φ(w - vₖ)|` is bounded by
  -- `A‖vₖ - w‖ + B√V₁(vₖ - w)` (kinetic via `abs_real_inner_le_norm`, viscous via
  -- `stokesTestPairing_abs_le`, nonlinear via `bForm_limit_convection_bound`), so `Φ(w) = 0`.
  classical
  set μ : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) T) with hμ
  haveI hμfin : IsFiniteMeasure μ := by
    rw [hμ]; refine isFiniteMeasure_restrict.2 ?_
    rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  have hbridge : ∀ g : ℝ → ℝ, ∫ t in (0 : ℝ)..T, g t = ∫ t, g t ∂μ := fun g => by
    rw [intervalIntegral.integral_of_le hT.le, hμ, Measure.restrict_congr_set Ioc_ae_eq_Icc]
  have hMuUniv : (μ Set.univ).toReal = T := by
    rw [hμ, Measure.restrict_apply_univ, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
    ring
  set M : ℝ := ‖(u₀ : L2VF_R3)‖ with hMdef
  have hM0 : 0 ≤ M := norm_nonneg _
  obtain ⟨Mψ, hMψ⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    hψC1.continuous.continuousOn
  obtain ⟨Mψ', hMψ'⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    hψC1.continuous_deriv_one.continuousOn
  have hMψ0 : 0 ≤ Mψ := le_trans (norm_nonneg _) (hMψ 0 ⟨le_refl 0, hT.le⟩)
  have hMψ'0 : 0 ≤ Mψ' := le_trans (norm_nonneg _) (hMψ' 0 ⟨le_refl 0, hT.le⟩)
  -- Measurability and a.e.-in-time facts about the limit curve.
  have hu_meas : AEStronglyMeasurable (fun t => (alPkg.u t : L2VF_R3)) μ := by
    rw [hμ]; exact alPkg.u_aestronglyMeasurable
  have hae_Icc : ∀ᵐ t ∂μ, t ∈ Set.Icc (0 : ℝ) T := by rw [hμ]; exact ae_restrict_mem measurableSet_Icc
  have hnorm_ulim : ∀ᵐ t ∂μ, ‖(alPkg.u t : L2VF_R3)‖ ≤ M := by
    rw [hμ]
    filter_upwards [kineticEnergy_lsc_bound 𝔊 F ν T u₀ galSeq alPkg] with t ht
    have hsq : ‖(alPkg.u t : L2VF_R3)‖ ^ 2 ≤ M ^ 2 := by rw [hMdef]; nlinarith [ht]
    exact le_of_sq_le_sq hsq hM0
  obtain ⟨hmemH1_u, hVν_ii, hVν_bound⟩ := viscous_lsc_under_strongL2 𝔊 F ν hν T hT u₀ galSeq alPkg
  obtain ⟨Kb, hKb0, hKb⟩ := bForm_limit_convection_bound 𝔊 F ν hν T hT u₀ galSeq alPkg
  -- `V₁(u ·)` is integrable on `[0,T]` and its integral is `≤ ν⁻¹·½‖u₀‖²`; hence so is `√V₁(u ·)`.
  have hVν_int : Integrable (fun t => viscousFormSq_R3 ν (alPkg.u t : L2VF_R3)) μ := by
    have h := (intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).mp hVν_ii
    rw [hμ, Measure.restrict_congr_set Ioc_ae_eq_Icc.symm]; exact h
  have hV1u_int : Integrable (fun t => viscousFormSq_R3 1 (alPkg.u t : L2VF_R3)) μ := by
    have h2 : Integrable (fun t => ν⁻¹ * viscousFormSq_R3 ν (alPkg.u t : L2VF_R3)) μ :=
      hVν_int.const_mul _
    refine h2.congr (Filter.Eventually.of_forall fun t => ?_)
    show ν⁻¹ * viscousFormSq_R3 ν (alPkg.u t : L2VF_R3) = viscousFormSq_R3 1 (alPkg.u t : L2VF_R3)
    rw [viscousFormSq_R3_eq_smul, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hν.ne', one_mul]
  have hV1u_intbound : ∫ t, viscousFormSq_R3 1 (alPkg.u t : L2VF_R3) ∂μ
      ≤ ν⁻¹ * ((1 / 2 : ℝ) * M ^ 2) := by
    have hb := hVν_bound
    rw [intervalIntegral.integral_congr (g := fun s => ν * viscousFormSq_R3 1
        (alPkg.u s : L2VF_R3)) (fun s _ => by rw [viscousFormSq_R3_eq_smul, smul_eq_mul]),
      intervalIntegral.integral_const_mul, hbridge] at hb
    rw [hMdef]; rwa [le_inv_mul_iff₀ hν]
  have hsqrtV1u_meas : AEStronglyMeasurable
      (fun t => Real.sqrt (viscousFormSq_R3 1 (alPkg.u t : L2VF_R3))) μ :=
    Real.continuous_sqrt.comp_aestronglyMeasurable
      (viscousFormSq_aestronglyMeasurable_of_memH1 alPkg hmemH1_u)
  have hsqrtV1u_int : Integrable
      (fun t => Real.sqrt (viscousFormSq_R3 1 (alPkg.u t : L2VF_R3))) μ := by
    refine Integrable.mono' ((integrable_const (1 : ℝ)).add hV1u_int) hsqrtV1u_meas ?_
    filter_upwards with t
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact sqrt_le_one_add_self_R3 _ (viscousFormSq_R3_nonneg zero_le_one _)
  have hsqrtV1u_bound : ∫ t, Real.sqrt (viscousFormSq_R3 1 (alPkg.u t : L2VF_R3)) ∂μ
      ≤ T + ν⁻¹ * ((1 / 2 : ℝ) * M ^ 2) := by
    calc ∫ t, Real.sqrt (viscousFormSq_R3 1 (alPkg.u t : L2VF_R3)) ∂μ
        ≤ ∫ t, (1 + viscousFormSq_R3 1 (alPkg.u t : L2VF_R3)) ∂μ :=
          integral_mono_ae hsqrtV1u_int ((integrable_const 1).add hV1u_int)
            (Filter.Eventually.of_forall fun t =>
              sqrt_le_one_add_self_R3 _ (viscousFormSq_R3_nonneg zero_le_one _))
      _ = T + ∫ t, viscousFormSq_R3 1 (alPkg.u t : L2VF_R3) ∂μ := by
          rw [integral_add (integrable_const 1) hV1u_int, integral_const, measureReal_def,
            hMuUniv, smul_eq_mul, mul_one]
      _ ≤ T + ν⁻¹ * ((1 / 2 : ℝ) * M ^ 2) := by linarith [hV1u_intbound]
  -- The abstract weak-form integrand as a function of the test slot `y`.
  set G : L2Sigma_R3 → ℝ → ℝ := fun y t =>
    -(inner (𝕜 := ℝ) (alPkg.u t : L2VF_R3) (y : L2VF_R3)) * deriv ψ t
      + ψ t * (ν * stokesTestPairing_R3 (alPkg.u t : L2VF_R3) (y : L2VF_R3)
        + F.b (alPkg.u t) (alPkg.u t) y) with hG
  -- Integrability of `G y` for any Schwartz div-free test `y`.
  have hGint : ∀ y : L2Sigma_R3, IsSchwartzDivFree_R3 y → Integrable (G y) μ := by
    intro y hy
    obtain ⟨ψy, hψy⟩ := hy
    -- Fixed viscous Riesz vector: `stokesTestPairing_R3 x y = ⟪vElt, x⟫`.
    obtain ⟨E, hE⟩ : ∃ E : Fin 3 → Lp ℝ 2 (volume : Measure Domain3),
        ∀ x : L2VF_R3, stokesTestPairing_R3 x (y : L2VF_R3)
          = ∑ j : Fin 3, inner (𝕜 := ℝ) (L2VF_projComponent_R3 j x) (E j) :=
      ⟨_, fun x => stokesTestPairing_R3_eq_sum_inner_negLap x (y : L2VF_R3) ψy hψy⟩
    set vElt : L2VF_R3 := ∑ j : Fin 3, (L2VF_projComponent_R3 j).adjoint (E j) with hvElt
    have hstok_inner : ∀ x : L2VF_R3,
        stokesTestPairing_R3 x (y : L2VF_R3) = inner (𝕜 := ℝ) vElt x := by
      intro x
      rw [hE x, hvElt, sum_inner]
      exact Finset.sum_congr rfl fun j _ => by
        rw [ContinuousLinearMap.adjoint_inner_left]; exact real_inner_comm _ _
    have hi1 : Integrable
        (fun t => -(inner (𝕜 := ℝ) (alPkg.u t : L2VF_R3) (y : L2VF_R3)) * deriv ψ t) μ := by
      refine Integrable.mono' (g := fun _ => M * ‖(y : L2VF_R3)‖ * Mψ') (integrable_const _)
        (((hu_meas.inner aestronglyMeasurable_const).neg).mul
          hψC1.continuous_deriv_one.aestronglyMeasurable) ?_
      filter_upwards [hnorm_ulim, hae_Icc] with t hn htI
      rw [Real.norm_eq_abs, abs_mul, abs_neg]
      have hψ'b : |deriv ψ t| ≤ Mψ' := by rw [← Real.norm_eq_abs]; exact hMψ' t htI
      calc |inner (𝕜 := ℝ) (alPkg.u t : L2VF_R3) (y : L2VF_R3)| * |deriv ψ t|
          ≤ (‖(alPkg.u t : L2VF_R3)‖ * ‖(y : L2VF_R3)‖) * Mψ' :=
            mul_le_mul (abs_real_inner_le_norm _ _) hψ'b (abs_nonneg _)
              (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        _ ≤ M * ‖(y : L2VF_R3)‖ * Mψ' := by gcongr
    have hinner_v_int : Integrable (fun t => inner (𝕜 := ℝ) vElt (alPkg.u t : L2VF_R3)) μ := by
      refine Integrable.mono' (integrable_const (‖vElt‖ * M))
        (aestronglyMeasurable_const.inner hu_meas) ?_
      filter_upwards [hnorm_ulim] with t hn
      rw [Real.norm_eq_abs]
      exact (abs_real_inner_le_norm _ _).trans (by gcongr)
    have hrest : Integrable (fun t => ψ t * (ν * stokesTestPairing_R3 (alPkg.u t : L2VF_R3)
        (y : L2VF_R3) + F.b (alPkg.u t) (alPkg.u t) y)) μ := by
      refine Integrable.bdd_mul (c := Mψ) ?_ hψC1.continuous.aestronglyMeasurable ?_
      · simp_rw [hstok_inner]
        exact (hinner_v_int.const_mul ν).add (hKb y ⟨ψy, hψy⟩).1
      · filter_upwards [hae_Icc] with t htI
        exact hMψ t htI
    have := hi1.add hrest
    rw [hG]; exact this
  -- Galerkin tests: `Φ(v) = 0` (W1, converted to the `μ`-integral).
  have hΦgal : ∀ v : L2Sigma_R3, IsGalerkinTest_R3 𝔊 v → ∫ t, G v t ∂μ = 0 := by
    intro v hv
    rw [← hbridge (G v)]
    exact weakFormNS_galerkinTest_limit 𝔊 F ν hν T hT u₀ galSeq alPkg v hv ψ hψcs hψsupp hψC1
  have hwH1 : memH1VF_R3 (w : L2VF_R3) := memH1VF_R3_of_isSchwartzDivFree hw
  -- Right-slot additivity: `G v t = G w t + G (v - w) t` at a.e. `t` (where `u t ∈ H¹`).
  have hGsub_pt : ∀ v : L2Sigma_R3, IsSchwartzDivFree_R3 v → ∀ t,
      memH1VF_R3 (alPkg.u t : L2VF_R3) → G v t - G w t = G (v - w) t := by
    intro v hv t hmemu
    have hvH1 : memH1VF_R3 (v : L2VF_R3) := memH1VF_R3_of_isSchwartzDivFree hv
    simp only [hG]
    have hcoe : ((v - w : L2Sigma_R3) : L2VF_R3) = (v : L2VF_R3) - (w : L2VF_R3) := by
      rw [Submodule.coe_sub]
    rw [hcoe, inner_sub_right,
      stokesTestPairing_R3_sub_right (alPkg.u t : L2VF_R3) (v : L2VF_R3) (w : L2VF_R3) hmemu hvH1 hwH1,
      bForm_R3_sub_3 F (alPkg.u t) (alPkg.u t) v w]
    ring
  -- The difference bound `|Φ(z)| ≤ A‖z‖ + B√V₁(z)`.
  set A : ℝ := M * Mψ' * T with hAdef
  set B : ℝ := Mψ * ν * (T + ν⁻¹ * ((1 / 2 : ℝ) * M ^ 2)) + Mψ * Kb with hBdef
  have hA0 : 0 ≤ A := by rw [hAdef]; positivity
  have hB0 : 0 ≤ B := by
    rw [hBdef]
    refine add_nonneg (mul_nonneg (mul_nonneg hMψ0 hν.le) ?_) (mul_nonneg hMψ0 hKb0)
    exact add_nonneg hT.le (mul_nonneg (inv_nonneg.2 hν.le) (by positivity))
  have hDiffBound : ∀ z : L2Sigma_R3, IsSchwartzDivFree_R3 z →
      |∫ t, G z t ∂μ| ≤ A * ‖(z : L2VF_R3)‖ + B * Real.sqrt (viscousFormSq_R3 1 (z : L2VF_R3)) := by
    intro z hz
    obtain ⟨ψz, hψz⟩ := hz
    have hzH1 : memH1VF_R3 (z : L2VF_R3) := memH1VF_R3_of_isSchwartzDivFree ⟨ψz, hψz⟩
    set S : ℝ := Real.sqrt (viscousFormSq_R3 1 (z : L2VF_R3)) with hS
    have hS0 : 0 ≤ S := Real.sqrt_nonneg _
    have hGz_int := hGint z ⟨ψz, hψz⟩
    have hb_int : Integrable (fun t => F.b (alPkg.u t) (alPkg.u t) z) μ := (hKb z ⟨ψz, hψz⟩).1
    -- Pointwise a.e. bound on the integrand norm.
    have hDbound : ∀ᵐ t ∂μ, ‖G z t‖
        ≤ M * ‖(z : L2VF_R3)‖ * Mψ'
          + Mψ * ν * (Real.sqrt (viscousFormSq_R3 1 (alPkg.u t : L2VF_R3)) * S)
          + Mψ * ‖F.b (alPkg.u t) (alPkg.u t) z‖ := by
      filter_upwards [hnorm_ulim, hmemH1_u, hae_Icc] with t hn hmemu htI
      have hψb : |ψ t| ≤ Mψ := by rw [← Real.norm_eq_abs]; exact hMψ t htI
      have hψ'b : |deriv ψ t| ≤ Mψ' := by rw [← Real.norm_eq_abs]; exact hMψ' t htI
      have hkin : ‖-(inner (𝕜 := ℝ) (alPkg.u t : L2VF_R3) (z : L2VF_R3)) * deriv ψ t‖
          ≤ M * ‖(z : L2VF_R3)‖ * Mψ' := by
        rw [Real.norm_eq_abs, abs_mul, abs_neg]
        calc |inner (𝕜 := ℝ) (alPkg.u t : L2VF_R3) (z : L2VF_R3)| * |deriv ψ t|
            ≤ (‖(alPkg.u t : L2VF_R3)‖ * ‖(z : L2VF_R3)‖) * Mψ' :=
              mul_le_mul (abs_real_inner_le_norm _ _) hψ'b (abs_nonneg _)
                (mul_nonneg (norm_nonneg _) (norm_nonneg _))
          _ ≤ M * ‖(z : L2VF_R3)‖ * Mψ' := by gcongr
      have hstok_le : |stokesTestPairing_R3 (alPkg.u t : L2VF_R3) (z : L2VF_R3)|
          ≤ Real.sqrt (viscousFormSq_R3 1 (alPkg.u t : L2VF_R3)) * S :=
        stokesTestPairing_abs_le (alPkg.u t : L2VF_R3) (z : L2VF_R3) hmemu hzH1
      have hrest_le : ‖ψ t * (ν * stokesTestPairing_R3 (alPkg.u t : L2VF_R3) (z : L2VF_R3)
          + F.b (alPkg.u t) (alPkg.u t) z)‖
          ≤ Mψ * ν * (Real.sqrt (viscousFormSq_R3 1 (alPkg.u t : L2VF_R3)) * S)
            + Mψ * ‖F.b (alPkg.u t) (alPkg.u t) z‖ := by
        rw [Real.norm_eq_abs, abs_mul]
        calc |ψ t| * |ν * stokesTestPairing_R3 (alPkg.u t : L2VF_R3) (z : L2VF_R3)
                + F.b (alPkg.u t) (alPkg.u t) z|
            ≤ Mψ * (ν * (Real.sqrt (viscousFormSq_R3 1 (alPkg.u t : L2VF_R3)) * S)
                + ‖F.b (alPkg.u t) (alPkg.u t) z‖) := by
              refine mul_le_mul hψb ?_ (abs_nonneg _) hMψ0
              refine (abs_add_le _ _).trans ?_
              rw [abs_mul, abs_of_nonneg hν.le, Real.norm_eq_abs]
              exact add_le_add (mul_le_mul_of_nonneg_left hstok_le hν.le) le_rfl
          _ = Mψ * ν * (Real.sqrt (viscousFormSq_R3 1 (alPkg.u t : L2VF_R3)) * S)
                + Mψ * ‖F.b (alPkg.u t) (alPkg.u t) z‖ := by ring
      calc ‖G z t‖
          ≤ ‖-(inner (𝕜 := ℝ) (alPkg.u t : L2VF_R3) (z : L2VF_R3)) * deriv ψ t‖
            + ‖ψ t * (ν * stokesTestPairing_R3 (alPkg.u t : L2VF_R3) (z : L2VF_R3)
                + F.b (alPkg.u t) (alPkg.u t) z)‖ := by
            rw [hG]; exact norm_add_le _ _
        _ ≤ M * ‖(z : L2VF_R3)‖ * Mψ'
              + Mψ * ν * (Real.sqrt (viscousFormSq_R3 1 (alPkg.u t : L2VF_R3)) * S)
              + Mψ * ‖F.b (alPkg.u t) (alPkg.u t) z‖ := by
            have := add_le_add hkin hrest_le; linarith
    -- The dominating function is integrable, with a closed-form integral bound.
    have hDom_int : Integrable (fun t => M * ‖(z : L2VF_R3)‖ * Mψ'
        + Mψ * ν * (Real.sqrt (viscousFormSq_R3 1 (alPkg.u t : L2VF_R3)) * S)
        + Mψ * ‖F.b (alPkg.u t) (alPkg.u t) z‖) μ := by
      refine ((integrable_const _).add ?_).add (hb_int.norm.const_mul Mψ)
      exact (hsqrtV1u_int.mul_const S).const_mul (Mψ * ν)
    have hmid_int : Integrable (fun t => Mψ * ν
        * (Real.sqrt (viscousFormSq_R3 1 (alPkg.u t : L2VF_R3)) * S)) μ :=
      (hsqrtV1u_int.mul_const S).const_mul (Mψ * ν)
    have hconv_int : Integrable (fun t => Mψ * ‖F.b (alPkg.u t) (alPkg.u t) z‖) μ :=
      hb_int.norm.const_mul Mψ
    have hsplit1 : ∫ t, (M * ‖(z : L2VF_R3)‖ * Mψ'
          + Mψ * ν * (Real.sqrt (viscousFormSq_R3 1 (alPkg.u t : L2VF_R3)) * S)
          + Mψ * ‖F.b (alPkg.u t) (alPkg.u t) z‖) ∂μ
        = (∫ t, (M * ‖(z : L2VF_R3)‖ * Mψ'
            + Mψ * ν * (Real.sqrt (viscousFormSq_R3 1 (alPkg.u t : L2VF_R3)) * S)) ∂μ)
          + (∫ t, Mψ * ‖F.b (alPkg.u t) (alPkg.u t) z‖ ∂μ) :=
      integral_add ((integrable_const (M * ‖(z : L2VF_R3)‖ * Mψ')).add hmid_int) hconv_int
    have hsplit2 : ∫ t, (M * ‖(z : L2VF_R3)‖ * Mψ'
          + Mψ * ν * (Real.sqrt (viscousFormSq_R3 1 (alPkg.u t : L2VF_R3)) * S)) ∂μ
        = (∫ t, (M * ‖(z : L2VF_R3)‖ * Mψ' : ℝ) ∂μ)
          + (∫ t, Mψ * ν * (Real.sqrt (viscousFormSq_R3 1 (alPkg.u t : L2VF_R3)) * S) ∂μ) :=
      integral_add (integrable_const (M * ‖(z : L2VF_R3)‖ * Mψ')) hmid_int
    have e1 : ∫ t, (M * ‖(z : L2VF_R3)‖ * Mψ' : ℝ) ∂μ = M * ‖(z : L2VF_R3)‖ * Mψ' * T := by
      rw [integral_const, measureReal_def, hMuUniv, smul_eq_mul, mul_comm]
    have e2 : ∫ t, Mψ * ν * (Real.sqrt (viscousFormSq_R3 1 (alPkg.u t : L2VF_R3)) * S) ∂μ
        = Mψ * ν * ((∫ t, Real.sqrt (viscousFormSq_R3 1 (alPkg.u t : L2VF_R3)) ∂μ) * S) := by
      rw [integral_const_mul, integral_mul_const]
    have e3 : ∫ t, Mψ * ‖F.b (alPkg.u t) (alPkg.u t) z‖ ∂μ
        = Mψ * (∫ t, ‖F.b (alPkg.u t) (alPkg.u t) z‖ ∂μ) := integral_const_mul _ _
    calc |∫ t, G z t ∂μ|
        = ‖∫ t, G z t ∂μ‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∫ t, ‖G z t‖ ∂μ := norm_integral_le_integral_norm _
      _ ≤ ∫ t, (M * ‖(z : L2VF_R3)‖ * Mψ'
            + Mψ * ν * (Real.sqrt (viscousFormSq_R3 1 (alPkg.u t : L2VF_R3)) * S)
            + Mψ * ‖F.b (alPkg.u t) (alPkg.u t) z‖) ∂μ :=
          integral_mono_ae hGz_int.norm hDom_int hDbound
      _ ≤ A * ‖(z : L2VF_R3)‖ + B * S := by
          rw [hsplit1, hsplit2, e1, e2, e3]
          have hb2 := (hKb z ⟨ψz, hψz⟩).2
          have hqv : Mψ * ν * ((∫ t, Real.sqrt (viscousFormSq_R3 1 (alPkg.u t : L2VF_R3)) ∂μ) * S)
              ≤ Mψ * ν * ((T + ν⁻¹ * ((1 / 2 : ℝ) * M ^ 2)) * S) := by
            refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hMψ0 hν.le)
            exact mul_le_mul_of_nonneg_right hsqrtV1u_bound hS0
          have hqc : Mψ * (∫ t, ‖F.b (alPkg.u t) (alPkg.u t) z‖ ∂μ) ≤ Mψ * (Kb * S) :=
            mul_le_mul_of_nonneg_left hb2 hMψ0
          rw [hAdef, hBdef]; nlinarith [hqv, hqc, hMψ0, hν.le, hM0, hS0]
  -- The vanishing bound sequence.
  have hRHS0 : Filter.Tendsto (fun k : ℕ => A * (1 / (k + 1)) + B * Real.sqrt (1 / (k + 1)))
      Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun k : ℕ => (1 : ℝ) / (k + 1)) Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hA : Filter.Tendsto (fun k : ℕ => A * (1 / (k + 1))) Filter.atTop (nhds 0) := by
      have := h1.const_mul A; rwa [mul_zero] at this
    have hB : Filter.Tendsto (fun k : ℕ => B * Real.sqrt (1 / (k + 1))) Filter.atTop (nhds 0) := by
      have h2 : Filter.Tendsto (fun k : ℕ => Real.sqrt (1 / (k + 1))) Filter.atTop (nhds 0) := by
        have hc : Filter.Tendsto (fun k : ℕ => Real.sqrt (1 / (k + 1))) Filter.atTop
            (nhds (Real.sqrt 0)) := (Real.continuous_sqrt.tendsto 0).comp h1
        rwa [Real.sqrt_zero] at hc
      have := h2.const_mul B; rwa [mul_zero] at this
    have := hA.add hB; rwa [add_zero] at this
  -- Conclude `Φ(w) = 0` by squeezing the difference bound.
  have hmain : ∫ t, G w t ∂μ = 0 := by
    have hle0 : |∫ t, G w t ∂μ| ≤ 0 := by
      refine ge_of_tendsto hRHS0 (Filter.eventually_atTop.2 ⟨0, fun k _ => ?_⟩)
      obtain ⟨v, hv_gal, hv_sdf, hv_norm, hv_visc⟩ :=
        htest w hw (1 / (k + 1)) (by positivity)
      have hsplit : ∫ t, G v t ∂μ = ∫ t, G w t ∂μ + ∫ t, G (v - w) t ∂μ := by
        rw [← integral_add (hGint w hw) (hGint (v - w) (isSchwartzDivFree_R3_sub v w hv_sdf hw))]
        refine integral_congr_ae ?_
        filter_upwards [hmemH1_u] with t hmemu
        have := hGsub_pt v hv_sdf t hmemu
        linarith [this]
      have hGw_eq : ∫ t, G w t ∂μ = -(∫ t, G (v - w) t ∂μ) := by
        rw [hΦgal v hv_gal] at hsplit; linarith
      rw [hGw_eq, abs_neg]
      refine (hDiffBound (v - w) (isSchwartzDivFree_R3_sub v w hv_sdf hw)).trans ?_
      have hnormle : ‖((v - w : L2Sigma_R3) : L2VF_R3)‖ ≤ 1 / (k + 1) := by
        rw [Submodule.coe_sub]; exact hv_norm.le
      have hviscle : viscousFormSq_R3 1 ((v - w : L2Sigma_R3) : L2VF_R3) ≤ 1 / (k + 1) := by
        rw [Submodule.coe_sub]; exact hv_visc.le
      have hsqrtle : Real.sqrt (viscousFormSq_R3 1 ((v - w : L2Sigma_R3) : L2VF_R3))
          ≤ Real.sqrt (1 / (k + 1)) := Real.sqrt_le_sqrt hviscle
      exact add_le_add (mul_le_mul_of_nonneg_left hnormle hA0)
        (mul_le_mul_of_nonneg_left hsqrtle hB0)
    exact abs_nonpos_iff.mp hle0
  -- Convert the `WeakFormNS` goal (`L2Sigma` inner) to the `G`-form and finish.
  rw [← hbridge (G w)] at hmain
  refine Eq.trans ?_ hmain
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [hG, Submodule.coe_inner]

/-! ### Tier C — combination: spatial + time ⇒ `AubinLionsPackage_R3` (the centerpiece) -/

set_option maxHeartbeats 800000 in
/-- **Aubin–Lions package on ℝ³ from the isolated time-compactness input (CLOSED).**

Produces `aubin_lions_R3`'s conclusion (`AubinLionsPackage_R3`), conditional on P3's local
spatial compactness (via `LocalRellichInput`).  The time-compactness extraction is supplied
UNCONDITIONALLY by `galerkinSpaceTimeExtraction_R3` (no separate `TimeCompactnessInput` modulus
hypothesis — it is absorbed into that single axiom).  The conclusion type is exactly
`AubinLionsPackage_R3 𝔊 F ν T u₀ galSeq` (matching the `aubin_lions_R3` binder list,
`AxiomaticClosure.lean:444–460`).

ASSEMBLY: the genuine spatial half is PROVED axiom-free (the `steklovAvg_spatial_extraction`
chain). The single irreducible LOCAL Bochner-time compactness extraction (one subsequence `φ` + a
measurable limit curve `u` with per-ball `restrictToBall R` a.e.-in-time `L²` convergence) is
supplied by `galerkinSpaceTimeExtraction_R3` (theorem, issue #44, proved; resting on the two
thinner axioms `galerkin_spacetime_precompact_R3` + `galerkin_weakLimit_R3` — local, no tightness,
no global-`L²` claim, genuinely weaker/thinner than `aubin_lions_R3`). From that
extraction this constructor assembles every field axiom-free:
* `φ`, `φ_mono`, `u` — directly from the extraction;
* `u_aestronglyMeasurable` — the extraction's measurability conjunct;
* `strong_convergence` — for each ball `R`, the extraction already delivers the per-ball
  ball-restricted differences converging to `0` a.e. in `t`, dominated by the constant
  `2‖u₀‖` on the finite window `[0,T]` (via `galerkin_norm_le_u0`); dominated convergence in `L²`
  (`tendsto_Lp_of_tendsto_ae`) gives the `eLpNorm`-in-time convergence.

This is a `noncomputable def` (not a `theorem`) because `AubinLionsPackage_R3` is a `Type`
(a data-carrying structure), not a `Prop` — mirroring the `aubin_lions_R3` axiom shape. -/
noncomputable def aubinLionsPackage_R3_of_timeCompactness
    (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T)
    (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n)
    (B : LocalRellichInput) :
    AubinLionsPackage_R3 𝔊 F ν T u₀ galSeq := by
  classical
  -- The isolated LOCAL Bochner-time extraction: one subsequence `φ` + a measurable limit curve `u`
  -- with per-ball (`restrictToBall R`) a.e.-in-time `L²` convergence.
  -- The axiom is a `Prop`-existential but the goal `AubinLionsPackage_R3` is a `Type` (a
  -- structure), so the existential witnesses are extracted via `Exists.choose`/`.choose_spec`
  -- (large elimination through `Classical.choice`) rather than `obtain`/`cases`.
  have hex := galerkinSpaceTimeExtraction_R3 𝔊 F ν hν T hT u₀ galSeq B
  set φ : ℕ → ℕ := hex.choose
  set u : Time → L2Sigma_R3 := hex.choose_spec.choose
  have hφ : StrictMono φ := hex.choose_spec.choose_spec.1
  have hmeas : AEStronglyMeasurable (fun t => (u t : L2VF_R3))
      (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)) :=
    hex.choose_spec.choose_spec.2.1
  -- LOCAL (per-ball) a.e.-in-time convergence: for each radius `R`, the ball restrictions
  -- `restrictToBall R (uₙ t)` converge to `restrictToBall R (u t)` a.e. in `t`.  This is the
  -- honest content available on ℝ³ — only local compactness (no tightness), so NO global
  -- `L2VF_R3`-norm a.e. convergence is claimed.
  have hae : ∀ R : ℝ, ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)),
      Filter.Tendsto (fun n => restrictToBall R ((galSeq (φ n)).u t : L2VF_R3)) Filter.atTop
        (nhds (restrictToBall R (u t : L2VF_R3))) :=
    hex.choose_spec.choose_spec.2.2
  refine
    { φ := φ
      φ_mono := hφ
      u := u
      u_aestronglyMeasurable := hmeas
      strong_convergence := ?_
      strong_convergence_ae := hae }
  -- `strong_convergence`: for each ball `R`, the ball-restricted differences converge to `0`
  -- in `L²(0,T)` by dominated convergence (constant dominator `2‖u₀‖` on the finite window).
  intro R
  set μ : Measure ℝ := MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T) with hμ
  haveI : IsFiniteMeasure μ := by
    rw [hμ]; exact ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc]; exact ENNReal.ofReal_lt_top⟩
  -- the two ball-restricted curves, as functions of time
  set fSeq : ℕ → ℝ → L2ballR3 R :=
    fun n t => restrictToBall R ((galSeq (φ n)).u t : L2VF_R3) with hfSeq
  set g : ℝ → L2ballR3 R := fun t => restrictToBall R (u t : L2VF_R3) with hg
  -- continuity (hence strong-measurability) of each `fSeq n` on `Ici 0 ⊇ Icc 0 T`
  have hcont_curve : ∀ m : ℕ, ContinuousOn (fun t => ((galSeq m).u t : L2VF_R3)) (Set.Ici 0) :=
    fun m => galerkin_curve_continuous 𝔊 F ν u₀ m (galSeq m)
  have hAESM_f : ∀ n, AEStronglyMeasurable (fSeq n) μ := by
    intro n
    rw [hμ]
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Icc
    refine (continuous_restrictToBall R).comp_continuousOn ?_
    exact (hcont_curve (φ n)).mono (by intro t ht; exact ht.1)
  -- `g` is a.e.-strongly-measurable (restrictToBall continuous ∘ measurable `u`)
  have hAESM_g : AEStronglyMeasurable g μ :=
    (continuous_restrictToBall R).comp_aestronglyMeasurable hmeas
  -- a.e.-in-`t` convergence of the ball restrictions — this is exactly the axiom's per-ball
  -- conjunct at radius `R` (`fSeq n t = restrictToBall R (uₙ t)`, `g t = restrictToBall R (u t)`).
  have hae_ball : ∀ᵐ t ∂μ, Filter.Tendsto (fun n => fSeq n t) Filter.atTop (nhds (g t)) := by
    rw [hμ, hfSeq, hg]; exact hae R
  -- uniform pointwise bound `‖fSeq n t‖ ≤ ‖u₀‖` on `[0,T]`
  have hbound : ∀ n, ∀ᵐ t ∂μ, ‖fSeq n t‖ ≤ ‖(u₀ : L2VF_R3)‖ := by
    intro n
    rw [hμ]
    refine (ae_restrict_iff' measurableSet_Icc).mpr (ae_of_all _ (fun t ht => ?_))
    refine le_trans (norm_restrictToBall_le' R _) ?_
    exact galerkin_norm_le_u0 𝔊 F ν u₀ (φ n) (galSeq (φ n)) ht.1
  -- `g ∈ MemLp 2 μ`: a.e.-bounded by the constant `‖u₀‖` on the finite measure.
  have hMemLp_g : MemLp g 2 μ := by
    -- `‖g t‖ ≤ ‖u₀‖` a.e. by norm-lsc through the per-ball a.e. limit `hae_ball`: `g t` is the
    -- limit of `fSeq n t` and each `‖fSeq n t‖ ≤ ‖u₀‖` (`hbound`).  No global `‖u t‖`-bound is
    -- used, so this works directly from the LOCAL per-ball convergence.
    have hgbd : ∀ᵐ t ∂μ, ‖g t‖ ≤ ‖(u₀ : L2VF_R3)‖ := by
      filter_upwards [hae_ball, ae_all_iff.mpr hbound] with t ht hbnd_t
      exact le_of_tendsto' ht.norm hbnd_t
    exact MemLp.of_bound hAESM_g _ hgbd
  -- `UnifIntegrable fSeq 2 μ`: from the uniform a.e. bound ‖fSeq n t‖ ≤ ‖u₀‖.
  -- For each ε > 0, pick δ so that for small-measure sets s, the indicator eLpNorm ≤ ε.
  -- Since ‖fSeq n t‖ ≤ ‖u₀‖ a.e., the indicator over s has eLpNorm ≤ ‖u₀‖ · μ(s)^(1/2)
  -- (Cauchy–Schwarz / eLpNorm_le_of_ae_bound), which is small when μ(s) is small.
  have hui : MeasureTheory.UnifIntegrable fSeq 2 μ := by
    intro ε hε
    -- bound on indicator eLpNorm from a.e. pointwise bound
    -- `eLpNorm (s.indicator (fSeq n)) 2 μ ≤ eLpNorm_le_of_ae_bound (‖u₀‖) + ...`
    -- Use MemLp.eLpNorm_indicator_le on the constant function ‖u₀‖ ∈ MemLp 2 μ
    -- then show the indicator eLpNorm is ≤ that of the constant.
    have hC_memLp : MemLp (fun _ : ℝ => ‖(u₀ : L2VF_R3)‖) 2 μ := memLp_const _
    obtain ⟨δ, hδpos, hδ⟩ := hC_memLp.eLpNorm_indicator_le one_le_two (by norm_num) hε
    refine ⟨δ, hδpos, fun n s hs hμs => ?_⟩
    -- bound eLpNorm (s.indicator (fSeq n)) ≤ eLpNorm (s.indicator (fun _ => ‖u₀‖))
    have hle : eLpNorm (s.indicator (fSeq n)) 2 μ
        ≤ eLpNorm (s.indicator (fun _ : ℝ => ‖(u₀ : L2VF_R3)‖)) 2 μ := by
      apply eLpNorm_mono_ae
      filter_upwards [hbound n] with t ht
      simp only [Set.indicator_apply]
      split_ifs
      · simpa using ht
      · simp
    exact le_trans hle (hδ s hs hμs)
  -- `UnifTight fSeq 2 μ`: on a finite measure, take s = univ (sᶜ = ∅, indicator = 0).
  have hut : MeasureTheory.UnifTight fSeq 2 μ := by
    intro ε _hε
    refine ⟨Set.univ, ?_, fun n => ?_⟩
    · exact measure_ne_top μ Set.univ
    · simp
  have := MeasureTheory.tendsto_Lp_of_tendsto_ae (μ := μ) (p := 2) one_le_two
    (by norm_num) hAESM_f hMemLp_g hui hut hae_ball
  -- convert `eLpNorm (fSeq n - g)` to the goal's pointwise-difference form
  refine this.congr (fun n => ?_)
  congr 1

end LerayHopf
