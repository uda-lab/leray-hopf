/-
# LerayHopf.R3.SpacetimePrecompact — Issue #46 PR-4 (File E)

**Goal:** The assembly layer of the Simon compactness route that discharges the axiom
`galerkin_spacetime_precompact_R3` (plan: `docs/scratch/issue46-spacetime-precompact-plan.md`,
§3 File E).  Given the generic step-curve `Lp` compactness (File A), the Galerkin curve
library (File B), the energy-class trilinear bound (File C), and the master `n`-uniform
integrated sampling-error modulus (File D, D3), this file assembles the LOCAL
Aubin–Lions–Simon spacetime precompactness statement — the exact proposition currently
held as the axiom `galerkin_spacetime_precompact_R3` in `ArzelaAscoliTime.lean`.

This file sits STRICTLY UPSTREAM of `ArzelaAscoliTime.lean`: it does NOT import it.  The
axiom→theorem conversion (E3) happens later in `ArzelaAscoliTime.lean` itself, by
`import`-ing this module and delegating to `galerkin_spacetime_precompact_of_goodSampling`;
this keeps the import graph acyclic.

- `restrictToBall_comp_curve_memLp` (E1): the ball-restricted Galerkin curve
  `t ↦ restrictToBall k (u t)` is `MemLp 2` on `[0, T]` (continuity via B1 +
  1-Lipschitz ball restriction on a compact interval).
- `galerkin_spacetime_precompact_of_goodSampling` (E2): the LOCAL Aubin–Lions–Simon
  precompactness conclusion.  Its statement is **binder-for-binder identical** to the
  residual `galerkin_spacetime_precompact_R3` (`ArzelaAscoliTime.lean`) — only the name
  differs; no hypothesis is dropped, no conclusion narrowed.

## Plan §3 File E mapping

- `restrictToBall_comp_curve_memLp`                : E1 — `MemLp 2` of the ball-restricted curve
- `galerkin_spacetime_precompact_of_goodSampling`  : E2 — assembled LOCAL precompactness (≡ axiom body)

Dependency edges (plan): A6, A4, A5 + D3 + E1 → E2 → E3 (in `ArzelaAscoliTime.lean`).

## Assumptions

No axioms are introduced by this file (`axiom` count: 0), and the file is `sorry`-free
(`sorry` count: 0): both E1 (`restrictToBall_comp_curve_memLp`) and E2
(`galerkin_spacetime_precompact_of_goodSampling`) are fully proved.  No statement was
weakened, renamed, or made vacuous; E2's statement is byte-identical to the residual it will
discharge.

The proofs use fresh local copies (docstring-linked) of four downstream-`private` primitives
(`measurable_natFloor_real`, `restrictToBall_dist_le'`, `continuous_restrictToBall'`,
`stepCurve_eval`) plus two private assembly lemmas (`eLpNorm_restrictToBall_stepCurve_diff_le`,
`totallyBounded_restrictToBall_toLp_range`).  `totallyBounded_restrictToBall_toLp_range`
carries a scoped `set_option maxHeartbeats 1200000` (the A5 transfer performs several
unifications in the doubly-nested `Lp (L2ballR3 k) 2 μ_T` space).
-/

import LerayHopf.R3.GalerkinTimeModulus        -- D3 galerkin_sampling_error_bound; transitively SolutionInterfaces (GalerkinSolutionData_R3, R3GalerkinScheme, R3NSForms, L2Sigma_R3), FrechetKolmogorov/RellichBall (frechetKolmogorov_holds, localRellichInput_of_frechetKolmogorov)
import LerayHopf.R3.GalerkinCurveBounds        -- B1 galerkinCurve_continuousOn, B2 galerkin_norm_le_u0 (curve continuity + energy bound for E1/E2)
import LerayHopf.R3.SpatialCompactness         -- L2ballR3, restrictToBall, LocalRellichInput.ballCompact (mirrors ArzelaAscoliTime's source of the ball-restriction primitives)
import LerayHopf.Bochner.StepFunctionCompactness  -- A4 isCompact_stepCurve_toLp, A5 totallyBounded_of_uniform_approx', A6 exists_subseq_tendsto_eLpNorm_of_totallyBounded (step-curve compactness engine for E2)

namespace LerayHopf

open MeasureTheory Filter Topology

/-! ### Local helpers (fresh copies of downstream-`private` primitives)

The following four helpers re-derive, locally and without new imports, facts that already
exist but only as `private` declarations in modules this file must NOT import
(`ArzelaAscoliTime`, `AubinLionsLimitPassage`, `StepFunctionCompactness`).  Each is
docstring-linked to the original. -/

/-- Local helper (fresh copy of the `private` `measurable_natFloor_real` in
`LerayHopf.Bochner.StepFunctionCompactness`): `Nat.floor : ℝ → ℕ` is measurable.  Fiber-wise
proof, keeping this file free of `Mathlib.MeasureTheory.Function.Floor`. -/
private theorem measurable_natFloor_real : Measurable (fun x : ℝ => ⌊x⌋₊) := by
  refine measurable_to_countable' fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h : (fun x : ℝ => ⌊x⌋₊) ⁻¹' {0} = Set.Iio 1 := by ext x; simp
    rw [h]; exact measurableSet_Iio
  · have h : (fun x : ℝ => ⌊x⌋₊) ⁻¹' {n} = Set.Ico (n : ℝ) ((n : ℝ) + 1) := by
      ext x; simp [Nat.floor_eq_iff' hn.ne']
    rw [h]; exact measurableSet_Ico

/-- Local helper (fresh copy of the `private` `restrictToBall_dist_le` in
`LerayHopf.R3.AubinLionsLimitPassage`): `restrictToBall R` is `1`-Lipschitz on `L2VF_R3`.
Restriction only shrinks the domain, so the `L²`-seminorm of the difference cannot grow. -/
private theorem restrictToBall_dist_le' (R : ℝ) (u v : L2VF_R3) :
    dist (restrictToBall R u) (restrictToBall R v) ≤ dist u v := by
  rw [dist_eq_norm, dist_eq_norm, Lp.norm_def, Lp.norm_def]
  have hle : volume.restrict (Metric.closedBall (0 : Domain3) R) ≤ (volume : Measure Domain3) :=
    Measure.restrict_le_self
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

/-- Local helper (fresh copy of the `private` `continuous_restrictToBall` in
`LerayHopf.R3.AubinLionsLimitPassage`): `restrictToBall R : L2VF_R3 → L2ballR3 R` is
continuous (it is `1`-Lipschitz by `restrictToBall_dist_le'`). -/
private theorem continuous_restrictToBall' (R : ℝ) :
    Continuous (fun w : L2VF_R3 => restrictToBall R w) := by
  refine Metric.continuous_iff.2 fun w ε hε => ⟨ε, hε, fun w' hw' => ?_⟩
  calc dist (restrictToBall R w') (restrictToBall R w)
      ≤ dist w' w := restrictToBall_dist_le' R w' w
    _ < ε := hw'

/-- Local helper (fresh copy of the `private` `stepCurve_apply` in
`LerayHopf.Bochner.StepFunctionCompactness`): evaluation of the step curve for a positive
mesh count. -/
private theorem stepCurve_eval {X : Type*} [NormedAddCommGroup X] {T : ℝ} {m : ℕ} (hm : 0 < m)
    (y : Fin m → X) (t : ℝ) :
    stepCurve T m y t
      = y ⟨min ⌊t * (m : ℝ) / T⌋₊ (m - 1),
           lt_of_le_of_lt (min_le_right _ _) (Nat.sub_lt hm Nat.one_pos)⟩ :=
  dif_pos hm

/-! ### E1 — `MemLp 2` of the ball-restricted Galerkin curve -/

/-- **E1.** The ball-restricted Galerkin solution curve `t ↦ restrictToBall k (u t)` is
`MemLp 2` on the compact interval `[0, T]` (with the restricted Lebesgue measure).

Route (plan §3 E1): `t ↦ (gs.u t : L2VF_R3)` is continuous on `Ici 0` (B1
`galerkinCurve_continuousOn`), and `restrictToBall k` is 1-Lipschitz, so the composition is
continuous on `[0, T]`; a continuous curve into a normed space is `MemLp 2` on a finite
interval. -/
theorem restrictToBall_comp_curve_memLp
    (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T) (u₀ : L2Sigma_R3) (n : ℕ)
    (gs : GalerkinSolutionData_R3 𝔊 F ν u₀ n) (k : ℕ) :
    MemLp (fun t => restrictToBall k ((gs.u t : L2VF_R3))) 2
      (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)) := by
  have hcurve : ContinuousOn (fun t => (gs.u t : L2VF_R3)) (Set.Icc (0 : ℝ) T) :=
    (galerkinCurve_continuousOn gs).mono (fun x hx => hx.1)
  have hcont : ContinuousOn (fun t => restrictToBall k ((gs.u t : L2VF_R3)))
      (Set.Icc (0 : ℝ) T) :=
    (continuous_restrictToBall' (k : ℝ)).comp_continuousOn hcurve
  haveI : IsFiniteMeasure (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Icc_lt_top⟩
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn hcont
  refine MemLp.of_bound (hcont.aestronglyMeasurable measurableSet_Icc) C ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact hC t ht

/-! ### Core analytic helper for E2 — the step-curve `L²`-approximation bound -/

/-- **Core helper for E2.** Given the D3 good-sample data `τ` (per-cell sample times with
the integrated modulus bound `∑ᵢ ∫ ‖u(t) − u(τᵢ)‖² ≤ B`), the ball-restricted Galerkin
curve `t ↦ restrictToBall k (u t)` is `L²(0,T)`-close to the mesh-`m` step curve sampled at
`τ`, with the quantitative bound `√B`.

Route: `restrictToBall k` is `1`-Lipschitz, so pointwise the difference is dominated by
`gg t := ‖u(t) − u(τ(cell t))‖`; the `L²`-norm of `gg` is computed cell-by-cell (each cell's
integrand agrees a.e. with the continuous `‖u(·) − u(τᵢ)‖²`), giving `∫ gg² = ∑ᵢ ∫ cell ≤ B`,
whence `‖·‖_{L²} = √(∫ gg²) ≤ √B`. -/
private theorem eLpNorm_restrictToBall_stepCurve_diff_le
    (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊) (ν : ℝ) (u₀ : L2Sigma_R3) (n : ℕ)
    (gs : GalerkinSolutionData_R3 𝔊 F ν u₀ n) (k : ℕ) (T : ℝ) (hT : 0 < T)
    (m : ℕ) (hm : 0 < m) (τ : Fin m → ℝ)
    (hτmem : ∀ i : Fin m,
      τ i ∈ Set.Icc (((i : ℕ) : ℝ) * (T / (m : ℝ))) ((((i : ℕ) : ℝ) + 1) * (T / (m : ℝ))))
    (w : ℝ → L2ballR3 k) (hweq : ∀ t, w t = restrictToBall (k : ℝ) (gs.u t : L2VF_R3))
    (B : ℝ)
    (hsum : (∑ i : Fin m,
        ∫ t in (((i : ℕ) : ℝ) * (T / (m : ℝ)))..((((i : ℕ) : ℝ) + 1) * (T / (m : ℝ))),
          ‖(gs.u t : L2VF_R3) - (gs.u (τ i) : L2VF_R3)‖ ^ 2) ≤ B) :
    (eLpNorm (fun t => w t
        - stepCurve T m (fun i => restrictToBall (k : ℝ) (gs.u (τ i) : L2VF_R3)) t) 2
      (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T))).toReal ≤ Real.sqrt B := by
  classical
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hd0 : (0 : ℝ) < T / (m : ℝ) := div_pos hT hmR
  have hdm : (T / (m : ℝ)) * (m : ℝ) = T := by field_simp
  set μT := MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T) with hμT
  haveI : IsFiniteMeasure μT :=
    ⟨by rw [hμT, Measure.restrict_apply_univ]; exact measure_Icc_lt_top⟩
  set y : Fin m → L2ballR3 k := fun i => restrictToBall (k : ℝ) (gs.u (τ i) : L2VF_R3) with hy
  set cellNat : ℝ → ℕ := fun t => min ⌊t * (m : ℝ) / T⌋₊ (m - 1) with hcellNat
  have hcellLt : ∀ t, cellNat t < m := fun t =>
    lt_of_le_of_lt (min_le_right _ _) (Nat.sub_lt hm Nat.one_pos)
  set cellFin : ℝ → Fin m := fun t => ⟨cellNat t, hcellLt t⟩ with hcellFin
  set gg : ℝ → ℝ := fun t => ‖(gs.u t : L2VF_R3) - (gs.u (τ (cellFin t)) : L2VF_R3)‖ with hgg
  -- step-curve evaluation and the pointwise Lipschitz domination
  have hstep : ∀ t, stepCurve T m y t = restrictToBall (k : ℝ) (gs.u (τ (cellFin t)) : L2VF_R3) :=
    fun t => stepCurve_eval hm y t
  have hpt : ∀ t, ‖w t - stepCurve T m y t‖ ≤ gg t := by
    intro t
    rw [hstep t, hweq t]
    simp only [hgg, ← dist_eq_norm]
    exact restrictToBall_dist_le' (k : ℝ) _ _
  -- strong measurability of the sampled (step) curve
  have hSC : StronglyMeasurable (fun t => (gs.u (τ (cellFin t)) : L2VF_R3)) := by
    have hg : StronglyMeasurable fun j : ℕ =>
        (gs.u (τ ⟨min j (m - 1), lt_of_le_of_lt (min_le_right _ _)
          (Nat.sub_lt hm Nat.one_pos)⟩) : L2VF_R3) := StronglyMeasurable.of_discrete
    have hidx : Measurable fun t : ℝ => ⌊t * (m : ℝ) / T⌋₊ :=
      measurable_natFloor_real.comp ((measurable_id.mul_const (m : ℝ)).div_const T)
    have hfun : (fun t => (gs.u (τ (cellFin t)) : L2VF_R3))
        = (fun j : ℕ => (gs.u (τ ⟨min j (m - 1), lt_of_le_of_lt (min_le_right _ _)
            (Nat.sub_lt hm Nat.one_pos)⟩) : L2VF_R3)) ∘ (fun t : ℝ => ⌊t * (m : ℝ) / T⌋₊) :=
      funext fun t => rfl
    rw [hfun]; exact hg.comp_measurable hidx
  -- `MemLp` of the real dominating function `gg`
  have haesmGG : AEStronglyMeasurable gg μT := by
    have h1 : AEStronglyMeasurable (fun t => (gs.u t : L2VF_R3)) μT :=
      ((galerkinCurve_continuousOn gs).mono (fun x hx => hx.1)).aestronglyMeasurable
        measurableSet_Icc
    exact (h1.sub hSC.aestronglyMeasurable).norm
  have hmemGG : MemLp gg 2 μT := by
    refine MemLp.of_bound haesmGG (2 * ‖(u₀ : L2VF_R3)‖) ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have hnn : (0 : ℝ) ≤ gg t := norm_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    have hb1 : ‖(gs.u t : L2VF_R3)‖ ≤ ‖(u₀ : L2VF_R3)‖ := galerkinCurve_norm_le_u0 gs t ht.1
    have hb2 : ‖(gs.u (τ (cellFin t)) : L2VF_R3)‖ ≤ ‖(u₀ : L2VF_R3)‖ := by
      refine galerkinCurve_norm_le_u0 gs (τ (cellFin t)) ?_
      exact le_trans (mul_nonneg (Nat.cast_nonneg _) hd0.le) (hτmem (cellFin t)).1
    calc gg t ≤ ‖(gs.u t : L2VF_R3)‖ + ‖(gs.u (τ (cellFin t)) : L2VF_R3)‖ := norm_sub_le _ _
      _ ≤ 2 * ‖(u₀ : L2VF_R3)‖ := by linarith
  -- cell arithmetic: the mesh cell index is `i` on the open `i`-th cell
  have hcell_le : ∀ i : Fin m,
      ((i : ℕ) : ℝ) * (T / (m : ℝ)) ≤ (((i : ℕ) : ℝ) + 1) * (T / (m : ℝ)) := by
    intro i
    have : ((i : ℕ) : ℝ) ≤ ((i : ℕ) : ℝ) + 1 := by linarith
    exact mul_le_mul_of_nonneg_right this hd0.le
  have hcellEq : ∀ (i : Fin m) (t : ℝ), ((i : ℕ) : ℝ) * (T / (m : ℝ)) < t →
      t < (((i : ℕ) : ℝ) + 1) * (T / (m : ℝ)) → cellFin t = i := by
    intro i t hlt hgt
    apply Fin.ext
    have hru : t / (T / (m : ℝ)) = t * (m : ℝ) / T := div_div_eq_mul_div t T (m : ℝ)
    have hidt : ((i : ℕ) : ℝ) < t / (T / (m : ℝ)) := (lt_div_iff₀ hd0).mpr hlt
    have hdti : t / (T / (m : ℝ)) < ((i : ℕ) : ℝ) + 1 := (div_lt_iff₀ hd0).mpr hgt
    have hfloor : ⌊t * (m : ℝ) / T⌋₊ = (i : ℕ) := by
      rw [← hru, Nat.floor_eq_iff (le_of_lt (lt_of_le_of_lt (Nat.cast_nonneg (i : ℕ)) hidt))]
      exact ⟨le_of_lt hidt, hdti⟩
    show min ⌊t * (m : ℝ) / T⌋₊ (m - 1) = (i : ℕ)
    rw [hfloor, min_eq_left (Nat.le_sub_one_of_lt i.isLt)]
  -- per-cell continuity / interval integrability of the fixed-sample integrand
  have hFic : ∀ i : Fin m,
      ContinuousOn (fun t => ‖(gs.u t : L2VF_R3) - (gs.u (τ i) : L2VF_R3)‖ ^ 2)
        (Set.Icc (0 : ℝ) T) :=
    fun i => ((((galerkinCurve_continuousOn gs).mono (fun x hx => hx.1)).sub
      continuousOn_const).norm.pow 2)
  have hEqOn : ∀ i : Fin m,
      Set.EqOn (fun t => ‖(gs.u t : L2VF_R3) - (gs.u (τ i) : L2VF_R3)‖ ^ 2)
        (fun t => gg t ^ 2)
        (Set.uIoo (((i : ℕ) : ℝ) * (T / (m : ℝ))) ((((i : ℕ) : ℝ) + 1) * (T / (m : ℝ)))) := by
    intro i t ht
    rw [Set.uIoo_of_le (hcell_le i)] at ht
    have heq := hcellEq i t ht.1 ht.2
    show ‖(gs.u t : L2VF_R3) - (gs.u (τ i) : L2VF_R3)‖ ^ 2 = gg t ^ 2
    rw [hgg]; simp only; rw [heq]
  have hIcell : ∀ i : Fin m, IntervalIntegrable (fun t => gg t ^ 2) volume
      (((i : ℕ) : ℝ) * (T / (m : ℝ))) ((((i : ℕ) : ℝ) + 1) * (T / (m : ℝ))) := by
    intro i
    have hsub : Set.Icc (((i : ℕ) : ℝ) * (T / (m : ℝ))) ((((i : ℕ) : ℝ) + 1) * (T / (m : ℝ)))
        ⊆ Set.Icc (0 : ℝ) T := by
      refine Set.Icc_subset_Icc (mul_nonneg (Nat.cast_nonneg _) hd0.le) ?_
      calc (((i : ℕ) : ℝ) + 1) * (T / (m : ℝ))
          ≤ (m : ℝ) * (T / (m : ℝ)) := by
            refine mul_le_mul_of_nonneg_right ?_ hd0.le
            exact_mod_cast Nat.succ_le_of_lt i.isLt
        _ = T := by rw [mul_comm]; exact hdm
    exact ((hFic i).mono hsub).intervalIntegrable_of_Icc (hcell_le i) |>.congr_uIoo (hEqOn i)
  -- decompose `∫ gg²` over the mesh cells and bound by `B`
  have hsumEq : (∑ i : Fin m,
        ∫ t in (((i : ℕ) : ℝ) * (T / (m : ℝ)))..((((i : ℕ) : ℝ) + 1) * (T / (m : ℝ))), gg t ^ 2)
      = ∫ t in (0 : ℝ)..T, gg t ^ 2 := by
    have key : (∑ q ∈ Finset.range m,
        ∫ t in ((fun j : ℕ => (j : ℝ) * (T / (m : ℝ))) q)..
            ((fun j : ℕ => (j : ℝ) * (T / (m : ℝ))) (q + 1)), gg t ^ 2)
        = ∫ t in ((fun j : ℕ => (j : ℝ) * (T / (m : ℝ))) 0)..
            ((fun j : ℕ => (j : ℝ) * (T / (m : ℝ))) m), gg t ^ 2 := by
      refine intervalIntegral.sum_integral_adjacent_intervals (fun q hq => ?_)
      have := hIcell ⟨q, hq⟩
      simpa using this
    simp only [Nat.cast_zero, zero_mul, Nat.cast_add, Nat.cast_one] at key
    rw [show (m : ℝ) * (T / (m : ℝ)) = T by rw [mul_comm]; exact hdm] at key
    rw [Fin.sum_univ_eq_sum_range
      (fun q => ∫ t in ((q : ℝ) * (T / (m : ℝ)))..(((q : ℝ) + 1) * (T / (m : ℝ))), gg t ^ 2) m]
    exact key
  have hcellCongr : ∀ i : Fin m,
      (∫ t in (((i : ℕ) : ℝ) * (T / (m : ℝ)))..((((i : ℕ) : ℝ) + 1) * (T / (m : ℝ))), gg t ^ 2)
      = ∫ t in (((i : ℕ) : ℝ) * (T / (m : ℝ)))..((((i : ℕ) : ℝ) + 1) * (T / (m : ℝ))),
          ‖(gs.u t : L2VF_R3) - (gs.u (τ i) : L2VF_R3)‖ ^ 2 := by
    intro i
    refine intervalIntegral.integral_congr_ae ?_
    rw [Set.uIoc_of_le (hcell_le i)]
    have hb : (volume : Measure ℝ) {(((i : ℕ) : ℝ) + 1) * (T / (m : ℝ))} = 0 := by simp
    filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr hb] with t htc hmem
    have htne : t ≠ (((i : ℕ) : ℝ) + 1) * (T / (m : ℝ)) := htc
    have hlt2 : t < (((i : ℕ) : ℝ) + 1) * (T / (m : ℝ)) := lt_of_le_of_ne hmem.2 htne
    have heq := hcellEq i t hmem.1 hlt2
    show gg t ^ 2 = ‖(gs.u t : L2VF_R3) - (gs.u (τ i) : L2VF_R3)‖ ^ 2
    rw [hgg]; simp only; rw [heq]
  have hIle : ∫ t in Set.Icc (0 : ℝ) T, gg t ^ 2 ∂volume ≤ B := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hT.le, ← hsumEq]
    calc (∑ i : Fin m,
          ∫ t in (((i : ℕ) : ℝ) * (T / (m : ℝ)))..((((i : ℕ) : ℝ) + 1) * (T / (m : ℝ))),
            gg t ^ 2)
        = ∑ i : Fin m,
          ∫ t in (((i : ℕ) : ℝ) * (T / (m : ℝ)))..((((i : ℕ) : ℝ) + 1) * (T / (m : ℝ))),
            ‖(gs.u t : L2VF_R3) - (gs.u (τ i) : L2VF_R3)‖ ^ 2 :=
          Finset.sum_congr rfl (fun i _ => hcellCongr i)
      _ ≤ B := hsum
  -- assemble: `‖diff‖_{L²} ≤ ‖gg‖_{L²} = √(∫ gg²) ≤ √B`
  have hI_nonneg : 0 ≤ ∫ t in Set.Icc (0 : ℝ) T, gg t ^ 2 ∂volume :=
    setIntegral_nonneg measurableSet_Icc (fun t _ => sq_nonneg _)
  have hggReal : (eLpNorm gg 2 μT).toReal ≤ Real.sqrt B := by
    rw [MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num) hmemGG,
      ENNReal.toReal_ofReal
        (Real.rpow_nonneg (integral_nonneg (fun t => by positivity)) _)]
    have hPint : (∫ t, ‖gg t‖ ^ (2 : ENNReal).toReal ∂μT)
        = ∫ t in Set.Icc (0 : ℝ) T, gg t ^ 2 ∂volume := by
      rw [hμT]
      refine setIntegral_congr_fun measurableSet_Icc (fun t _ => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
        show ((2 : ENNReal).toReal) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [hPint]
    calc (∫ t in Set.Icc (0 : ℝ) T, gg t ^ 2 ∂volume) ^ (2 : ENNReal).toReal⁻¹
        ≤ B ^ (2 : ENNReal).toReal⁻¹ :=
          Real.rpow_le_rpow hI_nonneg hIle (by norm_num)
      _ = Real.sqrt B := by
          rw [Real.sqrt_eq_rpow, show ((2 : ENNReal).toReal)⁻¹ = 1 / (2 : ℝ) by norm_num]
  calc (eLpNorm (fun t => w t - stepCurve T m y t) 2 μT).toReal
      ≤ (eLpNorm gg 2 μT).toReal :=
        ENNReal.toReal_mono hmemGG.eLpNorm_ne_top (eLpNorm_mono_real hpt)
    _ ≤ Real.sqrt B := hggReal

/-! ### STEP 1 of E2 — total-boundedness of the ball-restricted `toLp` range -/

set_option maxHeartbeats 1200000 in
/-- **STEP 1 of E2.**  The `toLp` classes of the ball-restricted Galerkin curves form a
totally bounded subset of `Lp (L2ballR3 k) 2 μ_T`.

`f` is kept abstract (with the pointwise identity `hfeq` linking it to the ball-restricted
curve) so that the matching against the core step-curve bound is syntactic — this keeps the
elaboration budget small.  Route: given `ε`, choose a fine mesh `m` (D3's uniform modulus
coefficient `C_mod` fixes `m` so `√(C_mod·√(T/m)) < ε`); D3's per-cell samples place each slice
in the compact `LocalRellichInput.ballCompact Mδ k` (B2 for the `L²` bound, D3 for the `V₁`
bound); the mesh-`m` step-curve set is compact (A4), hence totally bounded, and each curve is
within `ε` of its step curve (core helper); A5 transfers total-boundedness. -/
private theorem totallyBounded_restrictToBall_toLp_range
    (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊) (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T)
    (u₀ : L2Sigma_R3) (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n) (ψ : ℕ → ℕ) (k : ℕ)
    (f : ℕ → ℝ → L2ballR3 k)
    (hf : ∀ j, MemLp (f j) 2 (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)))
    (hfeq : ∀ j t, f j t = restrictToBall (k : ℝ) ((galSeq (ψ j)).u t : L2VF_R3)) :
    TotallyBounded (Set.range fun j => (hf j).toLp (f j)) := by
  classical
  obtain ⟨C_b, hC_b0, hC_b⟩ := bForm_galerkin_abs_le (𝔊 := 𝔊) (F := F)
  obtain ⟨C_mod, hC_mod0, hD3⟩ :=
    galerkin_sampling_error_bound (𝔊 := 𝔊) (F := F) ν T hν hT u₀ C_b hC_b0 hC_b
  refine totallyBounded_of_uniform_approx' _ (fun ε hε => ?_)
  -- choose a fine enough mesh `m`
  -- choose a fine enough mesh count `m` (kept opaque so that `(m : ℝ)` casts stay cheap)
  set c : ℝ := ε ^ 2 / (C_mod + 1) with hc
  have hc0 : 0 < c := div_pos (by positivity) (by linarith)
  obtain ⟨m, hm, hTmc2⟩ : ∃ m : ℕ, 0 < m ∧ T / (m : ℝ) < c ^ 2 := by
    refine ⟨⌊T / c ^ 2⌋₊ + 1, Nat.succ_pos _, ?_⟩
    have hmR' : (0 : ℝ) < ((⌊T / c ^ 2⌋₊ + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos _)
    have hmgt : T / c ^ 2 < ((⌊T / c ^ 2⌋₊ + 1 : ℕ) : ℝ) := by
      push_cast; exact Nat.lt_floor_add_one _
    rw [div_lt_iff₀ hmR']
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < c ^ 2)] at hmgt
    nlinarith [hmgt]
  have hmR : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  have hd0_aux : (0 : ℝ) < T / (m : ℝ) := div_pos hT hmR
  have hCmoddε : C_mod * Real.sqrt (T / (m : ℝ)) < ε ^ 2 := by
    have hsqrtc : Real.sqrt (T / (m : ℝ)) < c := (Real.sqrt_lt' hc0).mpr hTmc2
    have h1 : C_mod * Real.sqrt (T / (m : ℝ)) ≤ (C_mod + 1) * Real.sqrt (T / (m : ℝ)) := by
      nlinarith [Real.sqrt_nonneg (T / (m : ℝ))]
    have h2 : (C_mod + 1) * Real.sqrt (T / (m : ℝ)) < (C_mod + 1) * c :=
      mul_lt_mul_of_pos_left hsqrtc (by linarith)
    have h3 : (C_mod + 1) * c = ε ^ 2 := by rw [hc]; field_simp
    linarith
  -- the per-`ε` uniform bound `Mδ` and the compact ball set `K`
  set Mδ : ℝ := max ‖(u₀ : L2VF_R3)‖
    (Real.sqrt (2 * (T / (m : ℝ))⁻¹ * ν⁻¹ * ((1 / 2 : ℝ) * ‖(u₀ : L2VF_R3)‖ ^ 2))) with hMδ
  obtain ⟨K, hK, hKmem⟩ :=
    (localRellichInput_of_frechetKolmogorov frechetKolmogorov_holds).ballCompact Mδ (k : ℝ)
  -- the approximant: the mesh-`m` step-curve set valued in `K` (A4 compact, hence tot. bdd)
  refine ⟨(fun yv : Fin m → L2ballR3 k =>
      (stepCurve_memLp T hT m hm yv).toLp (stepCurve T m yv)) '' {yv | ∀ i, yv i ∈ K},
    (isCompact_stepCurve_toLp T hT m hm hK).totallyBounded, ?_⟩
  rintro s ⟨j, rfl⟩
  -- D3 good-sample data for the `j`-th curve
  obtain ⟨τ, hτmem, hτV1, hτsum⟩ := hD3 (ψ j) (galSeq (ψ j)) m hm
  refine ⟨(stepCurve_memLp T hT m hm
      (fun i => restrictToBall (k : ℝ) ((galSeq (ψ j)).u (τ i) : L2VF_R3))).toLp
      (stepCurve T m (fun i => restrictToBall (k : ℝ) ((galSeq (ψ j)).u (τ i) : L2VF_R3))),
    ⟨_, ?_, rfl⟩, ?_⟩
  · -- each sample slice lands in the compact `K`
    intro i
    show restrictToBall (k : ℝ) ((galSeq (ψ j)).u (τ i) : L2VF_R3) ∈ K
    refine hKmem ((galSeq (ψ j)).u (τ i) : L2VF_R3) ((galSeq (ψ j)).u (τ i)).2
      ((galSeq (ψ j)).reg_mem (τ i)) ?_ ?_
    · -- `‖u(τᵢ)‖ ≤ ‖u₀‖ ≤ Mδ`
      refine le_trans (galerkinCurve_norm_le_u0 (galSeq (ψ j)) (τ i) ?_) (le_max_left _ _)
      exact le_trans (mul_nonneg (Nat.cast_nonneg _)
        (div_nonneg hT.le (Nat.cast_nonneg _))) (hτmem i).1
    · -- `V₁(u(τᵢ)) ≤ 2δ⁻¹ν⁻¹E₀ ≤ Mδ²`
      have harg : (0 : ℝ) ≤
          2 * (T / (m : ℝ))⁻¹ * ν⁻¹ * ((1 / 2 : ℝ) * ‖(u₀ : L2VF_R3)‖ ^ 2) :=
        mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
          (inv_nonneg.mpr hd0_aux.le)) (inv_nonneg.mpr hν.le)) (by positivity)
      calc viscousFormSq_R3 1 ((galSeq (ψ j)).u (τ i) : L2VF_R3)
          ≤ 2 * (T / (m : ℝ))⁻¹ * ν⁻¹ * ((1 / 2 : ℝ) * ‖(u₀ : L2VF_R3)‖ ^ 2) := hτV1 i
        _ = (Real.sqrt (2 * (T / (m : ℝ))⁻¹ * ν⁻¹
              * ((1 / 2 : ℝ) * ‖(u₀ : L2VF_R3)‖ ^ 2))) ^ 2 := (Real.sq_sqrt harg).symm
        _ ≤ Mδ ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) (le_max_right _ _) 2
  · -- the `Lp`-distance is `< ε` by the core step-curve bound
    rw [dist_toLp_stepCurve T hT m hm
      (fun i => restrictToBall (k : ℝ) ((galSeq (ψ j)).u (τ i) : L2VF_R3)) (hf j)]
    refine lt_of_le_of_lt (eLpNorm_restrictToBall_stepCurve_diff_le 𝔊 F ν u₀ (ψ j)
      (galSeq (ψ j)) k T hT m hm τ hτmem (f j) (fun t => hfeq j t)
      (C_mod * Real.sqrt (T / (m : ℝ))) hτsum) ?_
    exact (Real.sqrt_lt' hε).mpr hCmoddε

/-! ### E2 — assembled LOCAL Aubin–Lions–Simon spacetime precompactness -/

/-- **E2.** LOCAL Aubin–Lions–Simon spacetime precompactness on ℝ³ (refine-capable form).

For every input subsequence `ψ` (strictly monotone) and every ball radius `k : ℕ`, there is
a further strictly-monotone `ρ` and a measurable limit curve `g_k : ℝ → L2ballR3 k` such
that the Bochner `L²`-in-time norm of `restrictToBall k ((galSeq (ψ (ρ n))).u t) - g_k t`
tends to `0`.

The statement is **binder-for-binder identical** to the axiom
`galerkin_spacetime_precompact_R3` in `ArzelaAscoliTime.lean` — only the name differs.  This
is the theorem that will discharge that axiom (E3).

Route (plan §3 E2): fix `ψ, k`; the family `t ↦ restrictToBall k ((galSeq (ψ n)).u t)` is
`MemLp` by E1; its `toLp` range is totally bounded (D3's `n`-uniform integrated sampling
modulus places each sample slice in the compact `LocalRellichInput.ballCompact`, A4 gives a
compact step-curve set, A5 transfers total-boundedness); A6 extracts the convergent
subsequence. -/
theorem galerkin_spacetime_precompact_of_goodSampling
    (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T) (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n)
    (ψ : ℕ → ℕ) (hψ : StrictMono ψ) (k : ℕ) :
    ∃ (ρ : ℕ → ℕ) (g_k : ℝ → L2ballR3 k), StrictMono ρ ∧
      AEStronglyMeasurable g_k (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)) ∧
      Filter.Tendsto
        (fun n => eLpNorm
          (fun t => restrictToBall k ((galSeq (ψ (ρ n))).u t : L2VF_R3) - g_k t)
          2 (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)))
        Filter.atTop (nhds 0) := by
  classical
  -- the ball-restricted family and its `MemLp` witnesses (E1)
  have hf : ∀ j, MemLp (fun t => restrictToBall (k : ℝ) ((galSeq (ψ j)).u t : L2VF_R3)) 2
      (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)) := fun j =>
    restrictToBall_comp_curve_memLp 𝔊 F ν hν T hT u₀ (ψ j) (galSeq (ψ j)) k
  -- STEP 1: the `toLp` range is totally bounded (A5 transfer via A4 step-curve compactness)
  have htb : TotallyBounded (Set.range fun j =>
      (hf j).toLp (fun t => restrictToBall (k : ℝ) ((galSeq (ψ j)).u t : L2VF_R3))) :=
    totallyBounded_restrictToBall_toLp_range 𝔊 F ν hν T hT u₀ galSeq ψ k _ hf
      (fun _ _ => rfl)
  -- STEP 2: sequential extraction (A6) and conversion to the stated `eLpNorm` form
  obtain ⟨ρ, G, hρ, htend⟩ := exists_subseq_tendsto_eLpNorm_of_totallyBounded T
    (fun j t => restrictToBall (k : ℝ) ((galSeq (ψ j)).u t : L2VF_R3)) hf htb
  exact ⟨ρ, fun t => G t, hρ, Lp.aestronglyMeasurable G, htend⟩

end LerayHopf
