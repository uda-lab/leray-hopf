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

**Refined scope (ADDENDUM — supersedes §3 Tier P / §9 where they conflict):** P2 targets the
**Aubin–Lions reduction** (spatial+time ⇒ package) plus **two reusable analytic lemmas**,
conditional only on the single isolated frontier hypothesis `TimeCompactnessInput` (the honest
uniform-in-`n` L² time modulus that mathlib's absent `W^{1,p}(0,T;X)` / vector-valued weak time
derivative / Aubin–Lions theory would supply). This is an **HONEST PARTIAL milestone**: part of
the deliverables are proved axiom-free, two are still open (`sorry` with truthful TODOs).

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

**OPEN / PARTIAL (currently `sorry` with truthful TODO — NOT impossible, NOT unsound):**

* `aubinLionsPackage_R3_of_timeCompactness` (C2, ~line 417) — the centerpiece Aubin–Lions
  assembly via the viable Steklov interval-averaging route. The building blocks above are proved;
  the REMAINING work is an OPEN ENGINEERING target: δ-mesh diagonalization + H¹/Jensen bound on
  the interval average + Bochner-average measurability. See the in-body TODO.

**Documented residual frontier (NOT reconstructed here, axioms retained):** the limit-passage
conclusions (b) `WeakFormNS`, (d) initial trace, and (e) energy class require the absent
vector-valued weak time-derivative / `W^{1,p}(0,T;X)` theory. Bundling them into a
`GoodRepresentativeInput` hypothesis would re-assert the conclusions (smuggling), so per the
ADDENDUM we DROP that and `galerkinLimitPassage_R3_of_goodRep`. P2 does NOT claim to produce the
full `galerkin_limit_passage_R3` conclusion (this mirrors R3-d, which proved `b`-form lemmas
without producing `Nonempty R3NSForms`).

**Zero new `axiom`/`opaque`/`constant`.** Honest isolated hypotheses: `TimeCompactnessInput` is an
explicit *argument* (not an axiom) — the intended time-frontier feeding the still-open C2 reduction,
exactly as P3's `LocalRellichInput`, R3-d's `hdiv`, P5's `SchwartzGalerkinBasis.dense_span`. It is
NOT the only non-proved item: E1 and C2 remain open `sorry`s as described above.

Target axioms this milestone partially substantiates (NOT removed):
`aubin_lions_R3` (`AxiomaticClosure.lean:444–460`, package `406–428`).
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
import LerayHopf.R3.TrilinearEstimate    -- b-bound analytic core (downstream of R3NSForms.b_bound)
import LerayHopf.R3.FourierL2            -- 𝓕, L2C_R3, viscousFormSq_R3_eq_integral_normSq_fourier (F7 spectral exposure for the viscous/H¹ Steklov Jensen bound)
import LerayHopf.R3.WeightedFourierCommute -- mulBdd bounded-multiplier commute + truncated weight (closes the viscous/H¹ Steklov Jensen gate)
import LerayHopf.R3.GalerkinODE          -- galerkinCurve_reg_mem (H¹ regularity of any curve in the Galerkin subspace)
import Mathlib.MeasureTheory.Integral.Bochner.Set   -- set/interval integrals over balls

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
private theorem galerkin_norm_le_u0 (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
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
private theorem galerkin_curve_continuous (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
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

/-- The viscous-form curve `s ↦ viscousFormSq_R3 1 (gs.u s)` is continuous on `Ici 0`
(`= ∑_j ‖weightedFourierComponent (u s) j‖²`, a sum of norm² of the continuous weighted-Fourier
curves — the new `viscous_curve_continuous` field). -/
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
  exact continuousOn_finset_sum _ (fun j _ => ((gs.viscous_curve_continuous j).norm.pow 2))

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

/-! ### Tier C — combination: spatial + time ⇒ `AubinLionsPackage_R3` (the centerpiece) -/

/-- **Aubin–Lions package on ℝ³ from the isolated time-compactness input (OPEN — `sorry`).**

TARGET/INTENT: produce `aubin_lions_R3`'s conclusion (`AubinLionsPackage_R3`) axiom-free,
conditional on (i) P3's local spatial compactness (via `LocalRellichInput`) and (ii) the isolated
uniform time-equicontinuity `TimeCompactnessInput`. The conclusion type is exactly
`AubinLionsPackage_R3 𝔊 F ν T u₀ galSeq` (matching the `aubin_lions_R3` binder list,
`AxiomaticClosure.lean:444–460`).

CURRENT STATUS: this is NOT yet substantiated — the body is `sorry` (C2). The Steklov
interval-averaging route is viable and its reusable helpers (`steklovAvg`, `steklovAvg_norm_le_u0`,
`steklovAvg_approx`, `galerkin_curve_continuous`) are proved axiom-free; the final assembly
(H¹/Jensen bound on the average + Bochner-average measurability + δ-mesh diagonalization) is the
OPEN engineering TODO below. The statement/hypotheses are kept intact (Hard rule 8).

This is a `noncomputable def` (not a `theorem`) because `AubinLionsPackage_R3` is a `Type`
(a data-carrying structure), not a `Prop` — mirroring the `aubin_lions_R3` axiom shape. -/
noncomputable def aubinLionsPackage_R3_of_timeCompactness
    (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T)
    (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n)
    (B : LocalRellichInput)
    (Htime : TimeCompactnessInput 𝔊 F ν T u₀ galSeq) :
    AubinLionsPackage_R3 𝔊 F ν T u₀ galSeq := by
  -- Proof sketch: assemble the `strong_convergence` field (local space-time L²(0,T;L²(B_R)) on
  -- every ball) by:
  --   1. apply `spatialInput_R3_of_localRellich B` to extract, at a dense set of sample times, a
  --      common subsequence `φ` with ball-restricted spatial convergence (diagonal-over-balls is
  --      already inside P3);
  --   2. use `Htime.uniform_time_modulus` to upgrade convergence at sample times to space-time
  --      L²(0,T;L²(B_R)) convergence (equicontinuity-in-time ⇒ the time-integral of the spatial
  --      error is controlled by the sample-time error + the modulus) — the Arzelà–Ascoli-in-time
  --      ε/3 step (NOT mathlib's abstract `ArzelaAscoli.*`; prove directly via a `δ`-mesh, gating
  --      note G2);
  --   3. package `φ`, the limit curve `u`, and the `strong_convergence` `Tendsto`.
  --
  -- PROVABLE CORE (no missing pillar): the uniform, POINTWISE-in-`t` L² bound
  -- `‖(galSeq n).u t‖ ≤ ‖u₀‖` (all `n`, `t ≥ 0`) is available via `galerkin_norm_le_u0`.
  have _hL2bound : ∀ (n : ℕ) {t : ℝ}, 0 ≤ t →
      ‖((galSeq n).u t : L2VF_R3)‖ ≤ ‖(u₀ : L2VF_R3)‖ :=
    fun n {t} ht => galerkin_norm_le_u0 𝔊 F ν u₀ n (galSeq n) ht
  -- WHICH ROUTE IS CORRECT (Codex xhigh adjudication): the *pointwise-sample* shortcut — pick a
  -- common sample time `tₖ`, hope for an `n`-uniform pointwise H¹ bound
  -- `viscousFormSq_R3 1 ((galSeq n).u tₖ) ≤ M²` and apply P3 to the raw states — does NOT work:
  -- the data only gives the TIME-INTEGRATED `reg_bound T`
  -- (`∫₀ᵀ viscousFormSq_R3 ν ((galSeq n).u t) dt ≤ C`, `C` `n`-independent), and by Markov the
  -- per-`n` bad sets `{t : viscous_n t > M²}` move with `n`, so no single dense/positive-measure
  -- sample set carries an `n`-uniform pointwise H¹ bound. That observation rules out ONLY the
  -- pointwise-sample shortcut; it does NOT make C2 mathematically impossible.
  --
  -- THE VIABLE ROUTE (Codex xhigh: the Steklov interval-averaging argument IS the right one and is
  -- viable here): replace pointwise samples by interval averages `steklovAvg gs δ t` (defined and
  -- analyzed above). Concretely:
  --   1. Control the raw curves by their interval averages via the time modulus:
  --      `‖(gs.u t) − steklovAvg gs δ t‖ ≤ ε` (`steklovAvg_approx`, fed by
  --      `Htime.uniform_time_modulus`); the averages are also `‖·‖ ≤ ‖u₀‖` uniformly
  --      (`steklovAvg_norm_le_u0`).
  --      BOUNDARY CAVEAT (not yet handled — see TODO below): `steklovAvg_approx` needs the modulus
  --      on the whole window `[t, t+δ]`, but `Htime.uniform_time_modulus` only controls pairs with
  --      BOTH times in `[0,T]`. So this forward-average control is uniform in `n,t` ONLY for
  --      `t ≤ T-δ`, where `[t, t+δ] ⊆ [0,T]`. For `t` in the boundary strip `(T-δ, T]` the forward
  --      window exits `[0,T]` and the hypothesis gives nothing; that strip needs SEPARATE handling
  --      (e.g. a direct boundary-strip estimate, or clipped/backward Steklov averages over
  --      `[t-δ, t]` whose windows stay inside `[0,T]`). This is part of the open assembly below,
  --      not a solved point.
  --   2. Bound the averages' H¹ seminorm by JENSEN from the INTEGRATED `reg_bound`:
  --      `viscousFormSq_R3 1 (steklovAvg gs δ t) ≤ δ⁻¹ ∫_{t}^{t+δ} viscousFormSq_R3 1 (gs.u s) ds`,
  --      which is finite and `n`-UNIFORM on each fixed δ-window — so the averaged states DO carry
  --      the `n`-uniform pointwise H¹ bound P3 needs (this is what the raw pointwise samples lacked).
  --   3. Apply P3 (`spatialInput_R3_of_localRellich B`) to the averaged states at the (finitely
  --      many, per δ-mesh) window base-points to extract a common ball-restricted spatial limit.
  --   4. Diagonalize over a refining δ-mesh (δ → 0): step 1 makes the average→raw error vanish,
  --      step 3 gives spatial convergence of the averages, and the time-`eLpNorm` (issue #31
  --      faithful form) `eLpNorm (fun t => restrictToBall R (uₙ t) − restrictToBall R (u t)) 2
  --      (volume.restrict (Icc 0 T)) → 0` follows by the ε/3 split (raw↔avg, avg-spatial, mesh).
  --
  -- STATUS: the reusable building blocks of this route are PROVED above and axiom-free —
  -- `galerkin_curve_continuous`, `steklovAvg` (def), `steklovAvg_norm_le_u0` (uniform L² bound),
  -- and `steklovAvg_approx` (time-modulus average↔curve estimate). What REMAINS is an OPEN
  -- ENGINEERING assembly, not a mathematical impossibility:
  --   • the H¹/Jensen bound on the average (step 2): `viscousFormSq_R3 1 (steklovAvg …) ≤
  --     δ⁻¹ ∫ viscousFormSq_R3 1 (gs.u s)` — Jensen for the convex viscous form under the Bochner
  --     average (needs the Bochner-average ↔ pointwise-form interchange);
  --   • Bochner-average measurability / joint `(t,x)`-measurability of the assembled limit for the
  --     outer interval-integral passage (step 4);
  --   • the BOUNDARY STRIP `(T-δ, T]` (step 1): the forward window `[t, t+δ]` leaves `[0,T]` there,
  --     so `Htime.uniform_time_modulus` (both times in `[0,T]`) does not feed `steklovAvg_approx`;
  --     handle it by a separate boundary-strip estimate or by clipped/backward averages over
  --     `[t-δ, t] ⊆ [0,T]`;
  --   • the full space-time δ-mesh diagonalization wiring (steps 3–4).
  -- TODO(C2): complete the Steklov interval-averaging Aubin–Lions assembly (steps 2–4 above) into
  -- the `AubinLionsPackage_R3` `strong_convergence` field. This is reachable from `galSeq` + `Htime`
  -- + P3 via the proved Steklov helpers; it is an engineering target, NOT blocked by a missing
  -- mathlib pillar. Statement/hypotheses kept intact (Hard rule 8); deferred this cycle.
  --
  -- TODO(E1-scaffold): the new `u_aestronglyMeasurable` field (added in #14-C) is also covered
  -- by this sorry. Its discharge path: use `aeStronglyMeasurable_of_spaceTimeL2` (the D2
  -- primitive in `Bochner/TimeSobolev.lean`) applied to the Steklov-assembled limit curve once
  -- C2 is resolved. See `#14-P` (#14-P E1 measurability target).
  sorry -- ALLOW_SORRY: #14-P E1 measurability + C2 centerpiece — this sorry covers: (1) `u_aestronglyMeasurable` (new #14-C field): discharged via D2 primitive aeStronglyMeasurable_of_spaceTimeL2 once C2 is resolved; (2) `strong_convergence` (C2): Steklov interval-averaging route viable, helpers proved, remaining = H¹ Jensen bound + Bochner-avg measurability + δ-mesh diagonalization

end LerayHopf
