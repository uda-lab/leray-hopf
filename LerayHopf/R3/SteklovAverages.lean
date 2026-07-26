/-
# LerayHopf.R3.SteklovAverages — Tier C-prep: Steklov interval-average building blocks

**Split off `R3.AubinLionsLimitPassage.lean` (issue #114 Tier 1, commit 2).** Verbatim move of
three sections: "Tier H — the isolated time-frontier hypothesis", "Tier S — discharge the
spatial input via P3", and "Tier C-prep — Steklov interval-average building blocks for the
Aubin–Lions route" (module docstring lines ~107–1092 as of the split, MINUS "Tier N —
nonlinear `b`-term passage", which stays in `AubinLionsLimitPassage.lean` — Tier C-prep does
not use it). No statement, proof, or namespace changed — only the file location. Module paths
are not yet a stable public API pre-release (issue #109 set the precedent of clean moves
without shims), so no compatibility alias is kept.

**Why Tier H and Tier S moved too, despite the plan's boundary being just Tier C-prep:**
Tier C-prep's `galerkin_curves_equicontinuous` uses the `TimeCompactnessInput` structure
(defined in Tier H), and `steklovAvg_spatial_extraction`/friends use
`spatialInput_R3_of_localRellich` (defined in Tier S) directly. Both `TimeCompactnessInput`
and `spatialInput_R3_of_localRellich` are used ONLY by Tier C-prep — real-code-verified, not
just by inspection: every other apparent reference anywhere else in
`AubinLionsLimitPassage.lean` (and the rest of the repo) is prose in a docstring, not a
compiled term. Since nothing outside the moved range needs either, and
`AubinLionsLimitPassage.lean` needs none of the Tier C-prep content back (verified the same
way — the "Tier C" combination centerpiece's own docstring admits this whole route is "proved
here independently of the final assembly", not yet wired into it), moving all three sections
together keeps this file's only external dependency direction outward (no cycle) and keeps
`AubinLionsLimitPassage.lean → R3.SteklovAverages` a clean one-way import.

These `private` helpers (plus the two public prerequisite theorems, `TimeCompactnessInput`,
and the deliverable `galerkinSpaceTimeExtraction_R3`) are the genuine, axiom-free sub-lemmas
of the Steklov interval-averaging route to the C2 Aubin–Lions reduction. They are proved
independently of the final assembly so that the route's reusable pieces are landed even while
the full space-time diagonalization remains open (see `AubinLionsLimitPassage.lean`'s C2 TODO).

## Assumptions

No `axiom`/`opaque`/`constant`/`unsafe` in this file.
-/

import LerayHopf.R3.SolutionInterfaces   -- R3GalerkinScheme, R3NSForms, GalerkinSolutionData_R3,
                                          -- AubinLionsPackage_R3 (theorem-signature types)
import LerayHopf.R3.SpatialCompactness   -- LocalRellichInput, localCompactness_R3_of_ballCompact,
                                          -- restrictToBall, L2ballR3
import LerayHopf.R3.EnergyWeakLsc        -- galerkin_norm_le_u0, galerkin_curve_continuous,
                                          -- viscousFormSq_curve_continuousOn (Tier E, issue #114
                                          -- Tier 1 commit 1)
import LerayHopf.R3.GalerkinODE          -- galerkinCurve_reg_mem, viscousFormSq_R3_eq_smul
import LerayHopf.R3.FourierL2            -- 𝓕, L2C_R3
import LerayHopf.R3.WeightedFourierCommute -- mulBdd bounded-multiplier commute + truncated weight
import LerayHopf.R3.ArzelaAscoliTime     -- u_lim_aestronglyMeasurable (issue #44 T4)
import Mathlib.MeasureTheory.Integral.Bochner.Set   -- set/interval integrals over balls

namespace LerayHopf

open MeasureTheory Filter Topology Metric
open scoped FourierTransform

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

This type is the `aubin_lions_R3` `spatial` binder verbatim (`SolutionInterfaces.lean:449–459`). -/
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
    one_pow, Real.rpow_two] at hholder
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
    have hδt : δ ≤ t := by push Not at hcase; linarith
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
    (_hε : 0 ≤ ε)
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
earlier, redundant `timeCompactnessInput_R3` axiom (which only ever fed this extraction) has
been dropped.

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


end LerayHopf
