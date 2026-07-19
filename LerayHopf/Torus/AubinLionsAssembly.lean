/-
# LerayHopf.Torus.AubinLionsAssembly

Final assembly of the torus `aubin_lions` mode-wise construction (issue #23): defines
`torusAubinLionsPackage_of_galSeq`, the proof that replaces the former `aubin_lions` axiom,
wired into the consumer `TorusGalerkinODECapstone.lean`.
-/

-- `TorusModeTail` transitively provides the whole chain:
-- TorusModeCompactness → {GalerkinODESolve, TestFamily, ConvectionExtension,
-- ScalarEquicontinuity} → SolutionInterfaces (AubinLionsPackage in scope).
import LerayHopf.Torus.ModeTail
-- `TorusProjectionAdjoint` is REQUIRED: the proof below depends on
-- `velocityProjection_n_pythagoras` (TorusProjectionAdjoint.lean:136), which the
-- TorusModeTail transitive chain does NOT reach.
-- Both imports are acyclic (TorusProjectionAdjoint imports TorusGalerkinODESolve only).
import LerayHopf.Torus.ProjectionAdjoint
import LerayHopf.Analysis.PlancherelKernels -- eLpNorm_two_eq_ofReal_sqrt (issue #111 PR-2)

open MeasureTheory Filter Topology Set

namespace LerayHopf

/-! ## P0.8 — `∫₀ᵀ ‖·‖² → 0` ⇒ `eLpNorm → 0` conversion (field 4's exact shape)

T-AL-6 GATE (architect, 2026-07-04): CONFIRMED AS-FROZEN, verbatim from Phase-0.
Proof route: the #44/#47 `eLpNorm`↔`lintegral` bridge patterns (`MemLp` from the
`M`-bound + AESM on the finite measure; `eLpNorm`² = lintegral of `ofReal ‖·‖²`;
interval integral → set integral over `Ioc ⊆ Icc`, endpoint null). -/

-- `eLpNorm_two_eq_ofReal_sqrt'` (was private here, byte-identical to `AubinLionsLimitPassage`'s
-- private `eLpNorm_two_eq_ofReal_sqrt`) moved to
-- `LerayHopf.Analysis.PlancherelKernels.eLpNorm_two_eq_ofReal_sqrt` (issue #111 PR-2);
-- its one call site below now uses the shared version directly.

private theorem eLpNorm_tendsto_of_integral_sq_tendsto
    (T : ℝ) (hT : 0 < T) (M : ℝ) (f : ℕ → ℝ → L2VF)
    (hmeas : ∀ n, AEStronglyMeasurable (f n) (volume.restrict (Icc (0 : ℝ) T)))
    (hb : ∀ n t, t ∈ Icc (0 : ℝ) T → ‖f n t‖ ≤ M)
    (hint : Tendsto (fun n => ∫ t in (0 : ℝ)..T, ‖f n t‖ ^ 2) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (f n) 2 (volume.restrict (Icc (0 : ℝ) T))) atTop
      (𝓝 0) := by
  -- Each `‖f n ·‖²` is integrable on the finite interval measure (AESM + `M`-bound).
  have hInt : ∀ n, Integrable (fun t => ‖f n t‖ ^ 2)
      (volume.restrict (Icc (0 : ℝ) T)) := by
    intro n
    have haesm : AEStronglyMeasurable (fun t => ‖f n t‖ ^ 2)
        (volume.restrict (Icc (0 : ℝ) T)) :=
      (continuous_pow 2).comp_aestronglyMeasurable (hmeas n).norm
    refine Integrable.mono' (integrable_const (M ^ 2)) haesm ?_
    rw [ae_restrict_iff' measurableSet_Icc]
    refine Filter.Eventually.of_forall fun t ht => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [hb n t ht, norm_nonneg (f n t)]
  -- Rewrite each `eLpNorm` as `ofReal (√(interval integral))`.
  have hkey : ∀ n, eLpNorm (f n) 2 (volume.restrict (Icc (0 : ℝ) T))
      = ENNReal.ofReal (Real.sqrt (∫ t in (0 : ℝ)..T, ‖f n t‖ ^ 2)) := by
    intro n
    rw [PlancherelKernels.eLpNorm_two_eq_ofReal_sqrt (f n) (hInt n)]
    congr 2
    rw [intervalIntegral.integral_of_le hT.le,
      MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [tendsto_congr hkey]
  -- Compose continuity of `√` and `ENNReal.ofReal` at `0` with `hint`.
  have hsqrt : Tendsto (fun n => Real.sqrt (∫ t in (0 : ℝ)..T, ‖f n t‖ ^ 2)) atTop
      (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hint
    simpa [Function.comp_def] using this
  have := (ENNReal.continuous_ofReal.tendsto 0).comp hsqrt
  simpa [Function.comp_def] using this

/-! ## P0.16 — Step F core: strong `L²(0,T; L²)` convergence of the extracted Galerkin
subsequence to the limit curve, from Step-D projected convergence + T-AL-5 tail bounds
via Pythagoras split and ε-squeeze over the level `N`. -/

/-- Parallelogram-type bound `‖a - b‖² ≤ 2‖a‖² + 2‖b‖²`. -/
private theorem norm_sub_sq_le {β : Type*} [NormedAddCommGroup β] (a b : β) :
    ‖a - b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h2 : ‖a - b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le a b) 2
  nlinarith [sq_nonneg (‖a‖ - ‖b‖), h2]

/-- The Fourier–Galerkin projection is norm-nonincreasing (Pythagoras). -/
private theorem norm_velocityProjection_le (N : ℕ) (x : L2VF) :
    ‖velocityProjection_n N x‖ ≤ ‖x‖ := by
  have h := velocityProjection_n_pythagoras N x
  have h2 : ‖velocityProjection_n N x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    nlinarith [sq_nonneg ‖x - velocityProjection_n N x‖]
  calc ‖velocityProjection_n N x‖
      = Real.sqrt (‖velocityProjection_n N x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (‖x‖ ^ 2) := Real.sqrt_le_sqrt h2
    _ = ‖x‖ := Real.sqrt_sq (norm_nonneg _)

/-- The truncation tail is norm-nonincreasing (Pythagoras). -/
private theorem norm_sub_velocityProjection_le (N : ℕ) (x : L2VF) :
    ‖x - velocityProjection_n N x‖ ≤ ‖x‖ := by
  have h := velocityProjection_n_pythagoras N x
  have h2 : ‖x - velocityProjection_n N x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    nlinarith [sq_nonneg ‖velocityProjection_n N x‖]
  calc ‖x - velocityProjection_n N x‖
      = Real.sqrt (‖x - velocityProjection_n N x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (‖x‖ ^ 2) := Real.sqrt_le_sqrt h2
    _ = ‖x‖ := Real.sqrt_sq (norm_nonneg _)

/-- An a.e.-strongly-measurable curve bounded by `C` on `[0,T]` has integrable squared
norm on the finite interval measure. -/
private theorem integrable_sq_of_aesm_bounded {β : Type*} [NormedAddCommGroup β]
    (T C : ℝ) (g : ℝ → β)
    (hg : AEStronglyMeasurable g (volume.restrict (Icc (0 : ℝ) T)))
    (hbnd : ∀ t ∈ Icc (0 : ℝ) T, ‖g t‖ ≤ C) :
    Integrable (fun t => ‖g t‖ ^ 2) (volume.restrict (Icc (0 : ℝ) T)) := by
  have haesm : AEStronglyMeasurable (fun t => ‖g t‖ ^ 2)
      (volume.restrict (Icc (0 : ℝ) T)) :=
    (continuous_pow 2).comp_aestronglyMeasurable hg.norm
  refine Integrable.mono' (integrable_const (C ^ 2)) haesm ?_
  rw [ae_restrict_iff' measurableSet_Icc]
  refine Filter.Eventually.of_forall fun t ht => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  nlinarith [hbnd t ht, norm_nonneg (g t)]

/-- (P0.16) Step F core — strong `L²(0,T; L²)` convergence of the extracted Galerkin
subsequence to the limit curve, from the Step-D projected convergence + the two
T-AL-5 tail bounds via the Pythagoras split and an ε-squeeze over the level `N`.
Conclusion shape = P0.8's `hint` input verbatim. -/
private theorem integral_sq_sub_tendsto_zero_of_galSeq
    (F : Torus3NSForms) (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T)
    (u₀ : L2Sigma) (galSeq : ∀ n, GalerkinSolutionData F ν u₀ n)
    (φ : ℕ → ℕ) (u : Time → L2Sigma)
    (hub : ∀ t ∈ Icc (0 : ℝ) T, ‖(u t : L2VF)‖ ≤ ‖(u₀ : L2VF)‖)
    (hmeas : AEStronglyMeasurable (fun t => (u t : L2VF))
      (volume.restrict (Icc (0 : ℝ) T)))
    (hweak : ∀ t ∈ Icc (0 : ℝ) T, ∀ z : L2Sigma,
      Tendsto (fun n => inner (𝕜 := ℝ) (((galSeq (φ n)).u t : L2VF)) ((z : L2VF)))
        atTop (𝓝 (inner (𝕜 := ℝ) ((u t : L2VF)) ((z : L2VF)))))
    (hD : ∀ N : ℕ, Tendsto (fun n => ∫ t in (0 : ℝ)..T,
        ‖velocityProjection_n N (((galSeq (φ n)).u t : L2VF)) -
          velocityProjection_n N ((u t : L2VF))‖ ^ 2) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ t in (0 : ℝ)..T,
        ‖((galSeq (φ n)).u t : L2VF) - (u t : L2VF)‖ ^ 2) atTop (𝓝 0) := by
  -- The finite-interval energy budget `B` and its per-level tail constant `c N`.
  set B : ℝ := T * ‖(u₀ : L2VF)‖ ^ 2 + ‖(u₀ : L2VF)‖ ^ 2 / (2 * ν) with hB_def
  have hB0 : 0 ≤ B :=
    add_nonneg (mul_nonneg hT.le (sq_nonneg _))
      (div_nonneg (sq_nonneg _) (by positivity))
  set c : ℕ → ℝ := fun N => B / (1 + (N : ℝ) ^ 2) with hc_def
  -- Interval integral over `0..T` = set integral over the finite measure on `Icc 0 T`.
  have hconv : ∀ g : ℝ → ℝ, (∫ t in (0 : ℝ)..T, g t)
      = ∫ t, g t ∂(volume.restrict (Icc (0 : ℝ) T)) := by
    intro g
    rw [intervalIntegral.integral_of_le hT.le, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  -- Galerkin curves are a.e.-strongly-measurable on the interval measure.
  have hw_meas : ∀ n, AEStronglyMeasurable (fun t => ((galSeq (φ n)).u t : L2VF))
      (volume.restrict (Icc (0 : ℝ) T)) := fun n =>
    ContinuousOn.aestronglyMeasurable
      (fun s hs => (((galSeq (φ n)).u_hasDeriv s hs.1).continuousAt).continuousWithinAt)
      measurableSet_Icc
  -- Master inequality: `I n ≤ (projected part) + 4·c N`, for every level `N`.
  have hmaster : ∀ N : ℕ, ∀ n : ℕ,
      (∫ t in (0 : ℝ)..T, ‖((galSeq (φ n)).u t : L2VF) - (u t : L2VF)‖ ^ 2)
        ≤ (∫ t in (0 : ℝ)..T,
            ‖velocityProjection_n N (((galSeq (φ n)).u t : L2VF)) -
              velocityProjection_n N ((u t : L2VF))‖ ^ 2) + 4 * c N := by
    intro N n
    have hPw : AEStronglyMeasurable
        (fun t => velocityProjection_n N (((galSeq (φ n)).u t : L2VF)))
        (volume.restrict (Icc (0 : ℝ) T)) :=
      (velocityProjection_n N).continuous.comp_aestronglyMeasurable (hw_meas n)
    have hPu : AEStronglyMeasurable
        (fun t => velocityProjection_n N ((u t : L2VF)))
        (volume.restrict (Icc (0 : ℝ) T)) :=
      (velocityProjection_n N).continuous.comp_aestronglyMeasurable hmeas
    -- Integrabilities on the finite-interval measure.
    have hInt_d : Integrable
        (fun t => ‖((galSeq (φ n)).u t : L2VF) - (u t : L2VF)‖ ^ 2)
        (volume.restrict (Icc (0 : ℝ) T)) :=
      integrable_sq_of_aesm_bounded T (2 * ‖(u₀ : L2VF)‖)
        (fun t => ((galSeq (φ n)).u t : L2VF) - (u t : L2VF))
        ((hw_meas n).sub hmeas)
        (fun t ht => by
          have h1 := galerkin_u_norm_le F ν u₀ (φ n) (galSeq (φ n)) t ht.1
          have h2 := hub t ht
          calc ‖((galSeq (φ n)).u t : L2VF) - (u t : L2VF)‖
              ≤ ‖((galSeq (φ n)).u t : L2VF)‖ + ‖(u t : L2VF)‖ := norm_sub_le _ _
            _ ≤ 2 * ‖(u₀ : L2VF)‖ := by linarith)
    have hInt_a : Integrable
        (fun t => ‖velocityProjection_n N (((galSeq (φ n)).u t : L2VF)) -
          velocityProjection_n N ((u t : L2VF))‖ ^ 2)
        (volume.restrict (Icc (0 : ℝ) T)) :=
      integrable_sq_of_aesm_bounded T (2 * ‖(u₀ : L2VF)‖)
        (fun t => velocityProjection_n N (((galSeq (φ n)).u t : L2VF)) -
          velocityProjection_n N ((u t : L2VF)))
        (hPw.sub hPu)
        (fun t ht => by
          have h1 := galerkin_u_norm_le F ν u₀ (φ n) (galSeq (φ n)) t ht.1
          have h2 := hub t ht
          calc ‖velocityProjection_n N (((galSeq (φ n)).u t : L2VF)) -
                velocityProjection_n N ((u t : L2VF))‖
              ≤ ‖velocityProjection_n N (((galSeq (φ n)).u t : L2VF))‖ +
                  ‖velocityProjection_n N ((u t : L2VF))‖ := norm_sub_le _ _
            _ ≤ ‖((galSeq (φ n)).u t : L2VF)‖ + ‖(u t : L2VF)‖ :=
                add_le_add (norm_velocityProjection_le N _) (norm_velocityProjection_le N _)
            _ ≤ 2 * ‖(u₀ : L2VF)‖ := by linarith)
    have hInt_b : Integrable
        (fun t => ‖((galSeq (φ n)).u t : L2VF) -
          velocityProjection_n N (((galSeq (φ n)).u t : L2VF))‖ ^ 2)
        (volume.restrict (Icc (0 : ℝ) T)) :=
      integrable_sq_of_aesm_bounded T ‖(u₀ : L2VF)‖
        (fun t => ((galSeq (φ n)).u t : L2VF) -
          velocityProjection_n N (((galSeq (φ n)).u t : L2VF)))
        ((hw_meas n).sub hPw)
        (fun t ht => by
          have h1 := galerkin_u_norm_le F ν u₀ (φ n) (galSeq (φ n)) t ht.1
          exact (norm_sub_velocityProjection_le N _).trans h1)
    have hInt_e : Integrable
        (fun t => ‖(u t : L2VF) - velocityProjection_n N ((u t : L2VF))‖ ^ 2)
        (volume.restrict (Icc (0 : ℝ) T)) :=
      integrable_sq_of_aesm_bounded T ‖(u₀ : L2VF)‖
        (fun t => (u t : L2VF) - velocityProjection_n N ((u t : L2VF)))
        (hmeas.sub hPu)
        (fun t ht => (norm_sub_velocityProjection_le N _).trans (hub t ht))
    -- Pointwise Pythagoras split + parallelogram bound.
    have hpt_le : ∀ t,
        ‖((galSeq (φ n)).u t : L2VF) - (u t : L2VF)‖ ^ 2
          ≤ ‖velocityProjection_n N (((galSeq (φ n)).u t : L2VF)) -
              velocityProjection_n N ((u t : L2VF))‖ ^ 2
            + (2 * ‖((galSeq (φ n)).u t : L2VF) -
                velocityProjection_n N (((galSeq (φ n)).u t : L2VF))‖ ^ 2
              + 2 * ‖(u t : L2VF) -
                velocityProjection_n N ((u t : L2VF))‖ ^ 2) := by
      intro t
      set a : L2VF := ((galSeq (φ n)).u t : L2VF) with ha
      set b : L2VF := (u t : L2VF) with hb
      have hid : ‖a - b‖ ^ 2
          = ‖velocityProjection_n N a - velocityProjection_n N b‖ ^ 2
            + ‖(a - velocityProjection_n N a) - (b - velocityProjection_n N b)‖ ^ 2 := by
        have hpyth := velocityProjection_n_pythagoras N (a - b)
        have e1 : velocityProjection_n N (a - b)
            = velocityProjection_n N a - velocityProjection_n N b := map_sub _ _ _
        have e2 : (a - b) - (velocityProjection_n N a - velocityProjection_n N b)
            = (a - velocityProjection_n N a) - (b - velocityProjection_n N b) := by abel
        rw [e1, e2] at hpyth
        linarith [hpyth]
      rw [hid]
      have hns := norm_sub_sq_le (a - velocityProjection_n N a) (b - velocityProjection_n N b)
      linarith [hns]
    -- Integrate the pointwise bound; split the majorant integral by linearity.
    have hb2_int : Integrable (fun t => 2 * ‖((galSeq (φ n)).u t : L2VF) -
        velocityProjection_n N (((galSeq (φ n)).u t : L2VF))‖ ^ 2)
        (volume.restrict (Icc (0 : ℝ) T)) := hInt_b.const_mul 2
    have he2_int : Integrable (fun t => 2 * ‖(u t : L2VF) -
        velocityProjection_n N ((u t : L2VF))‖ ^ 2)
        (volume.restrict (Icc (0 : ℝ) T)) := hInt_e.const_mul 2
    have hbe_int : Integrable (fun t =>
        2 * ‖((galSeq (φ n)).u t : L2VF) -
            velocityProjection_n N (((galSeq (φ n)).u t : L2VF))‖ ^ 2
          + 2 * ‖(u t : L2VF) - velocityProjection_n N ((u t : L2VF))‖ ^ 2)
        (volume.restrict (Icc (0 : ℝ) T)) := hb2_int.add he2_int
    have hM_int : Integrable (fun t =>
        ‖velocityProjection_n N (((galSeq (φ n)).u t : L2VF)) -
          velocityProjection_n N ((u t : L2VF))‖ ^ 2
        + (2 * ‖((galSeq (φ n)).u t : L2VF) -
            velocityProjection_n N (((galSeq (φ n)).u t : L2VF))‖ ^ 2
          + 2 * ‖(u t : L2VF) - velocityProjection_n N ((u t : L2VF))‖ ^ 2))
        (volume.restrict (Icc (0 : ℝ) T)) := hInt_a.add hbe_int
    have hstep1 := integral_mono hInt_d hM_int hpt_le
    have hM_eq : (∫ t, (‖velocityProjection_n N (((galSeq (φ n)).u t : L2VF)) -
            velocityProjection_n N ((u t : L2VF))‖ ^ 2
          + (2 * ‖((galSeq (φ n)).u t : L2VF) -
              velocityProjection_n N (((galSeq (φ n)).u t : L2VF))‖ ^ 2
            + 2 * ‖(u t : L2VF) - velocityProjection_n N ((u t : L2VF))‖ ^ 2))
        ∂(volume.restrict (Icc (0 : ℝ) T)))
        = (∫ t, ‖velocityProjection_n N (((galSeq (φ n)).u t : L2VF)) -
              velocityProjection_n N ((u t : L2VF))‖ ^ 2
            ∂(volume.restrict (Icc (0 : ℝ) T)))
          + (2 * (∫ t, ‖((galSeq (φ n)).u t : L2VF) -
                velocityProjection_n N (((galSeq (φ n)).u t : L2VF))‖ ^ 2
              ∂(volume.restrict (Icc (0 : ℝ) T)))
            + 2 * (∫ t, ‖(u t : L2VF) -
                velocityProjection_n N ((u t : L2VF))‖ ^ 2
              ∂(volume.restrict (Icc (0 : ℝ) T)))) := by
      rw [integral_add hInt_a hbe_int, integral_add hb2_int he2_int,
        integral_const_mul, integral_const_mul]
    rw [hM_eq] at hstep1
    -- Tail bounds (T-AL-5), transported from `∫₀ᵀ` to the set integral.
    have hb_bound : (∫ t, ‖((galSeq (φ n)).u t : L2VF) -
        velocityProjection_n N (((galSeq (φ n)).u t : L2VF))‖ ^ 2
        ∂(volume.restrict (Icc (0 : ℝ) T))) ≤ c N := by
      rw [← hconv (fun t => ‖((galSeq (φ n)).u t : L2VF) -
        velocityProjection_n N (((galSeq (φ n)).u t : L2VF))‖ ^ 2)]
      exact integral_tail_sq_galerkin_le F ν u₀ (φ n) (galSeq (φ n)) T hT N
    have he_bound : (∫ t, ‖(u t : L2VF) -
        velocityProjection_n N ((u t : L2VF))‖ ^ 2
        ∂(volume.restrict (Icc (0 : ℝ) T))) ≤ c N := by
      rw [← hconv (fun t => ‖(u t : L2VF) -
        velocityProjection_n N ((u t : L2VF))‖ ^ 2)]
      exact integral_tail_sq_limit_le F ν hν T hT u₀ galSeq φ u hub hmeas hweak N
    -- Assemble, converting the two interval integrals in the goal to set integrals.
    rw [hconv (fun t => ‖((galSeq (φ n)).u t : L2VF) - (u t : L2VF)‖ ^ 2),
      hconv (fun t => ‖velocityProjection_n N (((galSeq (φ n)).u t : L2VF)) -
        velocityProjection_n N ((u t : L2VF))‖ ^ 2)]
    linarith [hstep1, hb_bound, he_bound]
  -- ε-squeeze over the level `N`, using the master bound and Step-D (`hD`).
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨m, hm⟩ := exists_nat_gt (8 * B / ε)
  have hden : (0 : ℝ) < 1 + (m : ℝ) ^ 2 := by positivity
  have hm3 : 8 * B < ε * (1 + (m : ℝ) ^ 2) := by
    have hlt : 8 * B / ε < 1 + (m : ℝ) ^ 2 := by
      nlinarith [hm, sq_nonneg ((m : ℝ) - 1 / 2)]
    calc 8 * B = (8 * B / ε) * ε := by field_simp
      _ < (1 + (m : ℝ) ^ 2) * ε := mul_lt_mul_of_pos_right hlt hε
      _ = ε * (1 + (m : ℝ) ^ 2) := by ring
  have hNbound : 4 * c m < ε / 2 := by
    have hcm : c m = B / (1 + (m : ℝ) ^ 2) := rfl
    rw [hcm, ← mul_div_assoc, div_lt_iff₀ hden]
    nlinarith [hm3]
  obtain ⟨n₀, hn₀⟩ := Metric.tendsto_atTop.mp (hD m) (ε / 2) (half_pos hε)
  refine ⟨n₀, fun n hn => ?_⟩
  have hproj : |∫ t in (0 : ℝ)..T,
      ‖velocityProjection_n m (((galSeq (φ n)).u t : L2VF)) -
        velocityProjection_n m ((u t : L2VF))‖ ^ 2| < ε / 2 := by
    have := hn₀ n hn
    rwa [Real.dist_eq, sub_zero] at this
  have hInn : 0 ≤ ∫ t in (0 : ℝ)..T,
      ‖((galSeq (φ n)).u t : L2VF) - (u t : L2VF)‖ ^ 2 :=
    intervalIntegral.integral_nonneg hT.le (fun t _ => sq_nonneg _)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hInn]
  have hI := hmaster m n
  linarith [hI, hproj, hNbound, le_abs_self (∫ t in (0 : ℝ)..T,
    ‖velocityProjection_n m (((galSeq (φ n)).u t : L2VF)) -
      velocityProjection_n m ((u t : L2VF))‖ ^ 2)]

/-! ## P0.7 — the REPLACEMENT def (ALL FIVE fields; the axiom-deletion target)

Binder list is byte-identical to `axiom aubin_lions` (`SolutionInterfaces.lean:376`) —
same types in the same order, so the consumer rewire is a pure name swap.  The
`spatial` binder is UNUSED by the mode-wise proof (renamed `_spatial`; the consumer
keeps feeding `rellich_L2Sigma` positionally).  `Type`-valued, so a `noncomputable
def`; the Prop→Type extraction from the T-AL-4 capstone's existential goes through
`Classical.choose` (∃ has no large elimination; the ∧ chain does).

The body below is the REAL Step-F assembly wiring — sorry-free modulo the two leaves
P0.8 and P0.16 (unqualified calls: same-gate freeze placeholders, per anti-shadowing
rule 2); all previously-merged production calls are `_root_`-qualified.  It verifies
ALL FIVE `AubinLionsPackage` field shapes against the real construction. -/

/-- Assembles an `AubinLionsPackage` (all five fields) for a Galerkin solution family on the
torus, from mode-wise compactness — the axiom-deletion replacement for `axiom aubin_lions`. -/
noncomputable def torusAubinLionsPackage_of_galSeq
    (F : Torus3NSForms) (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T)
    (u₀ : L2Sigma)
    (galSeq : ∀ n, GalerkinSolutionData F ν u₀ n)
    (_spatial : ∀ (M : ℝ) (z : ℕ → L2VF),
      (∀ n, z n ∈ L2Sigma) →
      (∀ n, memH1VF (z n)) →
      (∀ n, h1EnergySq (z n) ≤ M ^ 2) →
      ∃ (ψ : ℕ → ℕ) (g : L2VF), StrictMono ψ ∧ g ∈ L2Sigma ∧
        Filter.Tendsto (fun n => z (ψ n)) Filter.atTop (nhds g)) :
    AubinLionsPackage F ν T u₀ galSeq := by
  classical
  -- T-AL-4 capstone (production): the extraction φ, the limit curve u, and the four
  -- analytic conjuncts.  Type-valued goal ⇒ extract the ∃-witnesses by choice.
  have H := _root_.LerayHopf.exists_limit_curve_of_galSeq F ν hν T hT u₀ galSeq
  obtain ⟨hφ, hweak, hub, hmeas, hD⟩ := H.choose_spec.choose_spec
  -- Fields 1–3 and 5 are direct; field 4 (strong_convergence) is Step F.
  refine ⟨H.choose, hφ, H.choose_spec.choose, ?_, hmeas⟩
  -- Continuity of the reindexed Galerkin curves (production T-AL-3 export).
  have hcont : ∀ n, ContinuousOn
      (fun t => ((galSeq (H.choose n)).u t : L2VF)) (Icc (0 : ℝ) T) := fun n =>
    (_root_.LerayHopf.galerkin_u_continuousOn F ν u₀ (H.choose n)
      (galSeq (H.choose n))).mono Icc_subset_Ici_self
  -- Step F: split-convergence core (P0.16) → eLpNorm conversion (P0.8).
  exact eLpNorm_tendsto_of_integral_sq_tendsto T hT (2 * ‖(u₀ : L2VF)‖)
    (fun n t => ((galSeq (H.choose n)).u t : L2VF) - (H.choose_spec.choose t : L2VF))
    (fun n => ((hcont n).aestronglyMeasurable measurableSet_Icc).sub hmeas)
    (fun n t ht =>
      (norm_sub_le _ _).trans (by
        have h1 := _root_.LerayHopf.galerkin_u_norm_le F ν u₀ (H.choose n)
          (galSeq (H.choose n)) t ht.1
        have h2 := hub t ht
        linarith))
    (integral_sq_sub_tendsto_zero_of_galSeq F ν hν T hT u₀ galSeq
      H.choose H.choose_spec.choose hub hmeas hweak hD)

end LerayHopf
