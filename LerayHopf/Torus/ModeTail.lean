/-
# LerayHopf.Torus.ModeTail

Tail bounds for the torus `aubin_lions` mode-wise construction (issue #23): eight leaf
lemmas that feed the `AubinLionsAssembly.lean` assembly step, all sorry-free (one private
helper `tendsto_real_functional_of_weak` for the weak-lsc coefficient convergence).

Assumptions: none beyond what `TorusModeCompactness` already carries.
-/
import LerayHopf.Torus.ModeCompactness

open MeasureTheory Filter Topology Set

namespace LerayHopf

/-- (a) Vector tail identity: Pythagoras + componentwise
`L2C_norm_sub_fourierProjection_sq` through `L2VF_norm_sq_eq_sum_componentC`
(`TorusGalerkinODESolve.lean:898`, `LerayHopf.Torus` namespace) +
`velocityProjection_n_component_comm`. -/
theorem L2VF_norm_sub_velocityProjection_sq (N : ℕ) (u : L2VF) :
    ‖u - velocityProjection_n N u‖ ^ 2 =
      ∑ j : Fin 3, ∑' k : {k : Fin 3 → ℤ // k ∉ fourierBox N},
        ‖mFourierCoeff3 (L2VF_projComponentC j u) k‖ ^ 2 := by
  rw [Torus.L2VF_norm_sq_eq_sum_componentC]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_sub, velocityProjection_n_component_comm,
    ContinuousLinearMap.coe_restrictScalars']
  exact L2C_norm_sub_fourierProjection_sq N (L2VF_projComponentC j u)

/-- (b) H¹ domination of the tail, for H¹ fields (the Galerkin curves: `reg_mem`).
The `memH1VF` hypothesis supplies the summability that keeps `h1EnergySq`'s `tsum`
honest (no junk-0 collapse); the LIMIT curve does NOT get this lemma — it goes through
the ENNReal Fatou route (c). -/
theorem tail_sq_le_h1EnergySq_div (N : ℕ) (u : L2VF) (hu : memH1VF u) :
    ‖u - velocityProjection_n N u‖ ^ 2 ≤ h1EnergySq u / (1 + (N : ℝ) ^ 2) := by
  rw [L2VF_norm_sub_velocityProjection_sq, h1EnergySq, Finset.sum_div]
  refine Finset.sum_le_sum fun j _ => ?_
  set Wj : ℝ := ∑' k : Fin 3 → ℤ, (1 + ∑ i : Fin 3, (k i : ℝ) ^ 2) *
      ‖mFourierCoeff3 (L2VF_projComponentC j u) k‖ ^ 2 with hWjdef
  have hWj0 : 0 ≤ Wj := tsum_nonneg fun k => by positivity
  have hb := H1_tail_bound N (L2VF_projComponentC j u) (hu j) (Real.sqrt Wj)
    (le_of_eq (by rw [Real.sq_sqrt hWj0]))
  rwa [Real.sq_sqrt hWj0] at hb

/-- (b′) Integrability side condition to consume `reg_bound` soundly: for a Galerkin
curve (band-limited at level `n`), `t ↦ h1EnergySq (u_n t)` is continuous on `[0,∞)`
(finite `fourierBox` sum of squared moduli of continuous coefficient functions). -/
theorem h1EnergySq_continuousOn_galerkin
    (F : Torus3NSForms) (ν : ℝ) (u₀ : L2Sigma) (n : ℕ)
    (D : GalerkinSolutionData F ν u₀ n) :
    ContinuousOn (fun t => h1EnergySq ((D.u t : L2VF))) (Ici (0 : ℝ)) := by
  have hcurve : ContinuousOn (fun t => (D.u t : L2VF)) (Ici 0) :=
    fun s hs => ((D.u_hasDeriv s hs).continuousAt).continuousWithinAt
  have hband : ∀ t, h1EnergySq (D.u t : L2VF)
      = ∑ j : Fin 3, ∑ k ∈ fourierBox n, (1 + ∑ i : Fin 3, (k i : ℝ) ^ 2)
          * ‖mFourierCoeff3 (L2VF_projComponentC j (D.u t : L2VF)) k‖ ^ 2 := by
    intro t
    unfold h1EnergySq
    refine Finset.sum_congr rfl fun j _ => ?_
    refine tsum_eq_sum fun k hk => ?_
    rw [coeff_zero_outside_box n _ (D.u_inVn t).symm j k hk]; simp
  simp_rw [hband]
  apply continuousOn_finsetSum Finset.univ; intro j _
  apply continuousOn_finsetSum (fourierBox n); intro k _
  apply ContinuousOn.const_mul
  apply ContinuousOn.pow; apply ContinuousOn.norm
  have heq : ∀ s, mFourierCoeff3 (L2VF_projComponentC j (D.u s : L2VF)) k =
      fourierCoeffCLM k (L2VF_projComponentC j (D.u s : L2VF)) :=
    fun s => (fourierCoeffCLM_apply k _).symm
  simp_rw [heq]
  exact ((fourierCoeffCLM k).continuous.comp
    (L2VF_projComponentC j).continuous).comp_continuousOn hcurve

/-- **Weak convergence propagates through continuous ℝ-linear functionals.**  If
`⟪vk i, y⟫ → ⟪v, y⟫` for every test `y`, then `L (vk i) → L v` for every
`L : L2VF →L[ℝ] ℝ` (Riesz representation of `L`). -/
private theorem tendsto_real_functional_of_weak (v : L2VF) (vk : ℕ → L2VF)
    (hweak : ∀ y : L2VF,
      Tendsto (fun i => inner (𝕜 := ℝ) (vk i) y) atTop (𝓝 (inner (𝕜 := ℝ) v y)))
    (L : L2VF →L[ℝ] ℝ) :
    Tendsto (fun i => L (vk i)) atTop (𝓝 (L v)) := by
  set y0 : L2VF := (InnerProductSpace.toDual ℝ L2VF).symm L with hy0
  have hrep : ∀ x : L2VF, L x = inner (𝕜 := ℝ) x y0 := by
    intro x
    rw [real_inner_comm, hy0, InnerProductSpace.toDual_symm_apply]
  simp_rw [hrep]
  exact hweak y0

/-- (c) ENNReal tail lower-semicontinuity under WEAK convergence (the limit-curve tail;
mirrors `viscousEnn_lsc`'s Fatou structure, with per-coefficient convergence supplied by
weak convergence — each coefficient functional is a continuous linear functional). -/
theorem tailEnn_lsc_of_weak (N : ℕ) (v : L2VF) (vk : ℕ → L2VF)
    (hweak : ∀ y : L2VF,
      Tendsto (fun i => inner (𝕜 := ℝ) (vk i) y) atTop (𝓝 (inner (𝕜 := ℝ) v y))) :
    (∑ j : Fin 3, ∑' k : {k : Fin 3 → ℤ // k ∉ fourierBox N},
        ENNReal.ofReal (‖mFourierCoeff3 (L2VF_projComponentC j v) k‖ ^ 2)) ≤
      Filter.liminf (fun i => ∑ j : Fin 3, ∑' k : {k : Fin 3 → ℤ // k ∉ fourierBox N},
        ENNReal.ofReal (‖mFourierCoeff3 (L2VF_projComponentC j (vk i)) k‖ ^ 2)) atTop := by
  classical
  -- Reindex the finite `j`-sum of tails as a single tsum over the product index.
  set G : (Fin 3 × {k : Fin 3 → ℤ // k ∉ fourierBox N}) → L2VF → ENNReal :=
    fun p x => ENNReal.ofReal (‖mFourierCoeff3 (L2VF_projComponentC p.1 x) (p.2 : Fin 3 → ℤ)‖ ^ 2)
    with hGdef
  have hunfold : ∀ x : L2VF,
      (∑ j : Fin 3, ∑' k : {k : Fin 3 → ℤ // k ∉ fourierBox N},
        ENNReal.ofReal (‖mFourierCoeff3 (L2VF_projComponentC j x) (k : Fin 3 → ℤ)‖ ^ 2))
        = ∑' p, G p x := by
    intro x
    rw [ENNReal.tsum_prod', tsum_fintype]
  -- Per-coefficient convergence under weak convergence.
  have hGtend : ∀ p, Tendsto (fun i => G p (vk i)) atTop (𝓝 (G p v)) := by
    intro p
    set M : L2VF →L[ℝ] ℂ :=
      (fourierCoeffCLM (p.2 : Fin 3 → ℤ)).restrictScalars ℝ ∘L (L2VF_projComponentC p.1)
      with hMdef
    have hMapp : ∀ x : L2VF,
        mFourierCoeff3 (L2VF_projComponentC p.1 x) (p.2 : Fin 3 → ℤ) = M x := by
      intro x
      rw [hMdef]
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars']
      rw [fourierCoeffCLM_apply]
    have hre := tendsto_real_functional_of_weak v vk hweak (Complex.reCLM.comp M)
    have him := tendsto_real_functional_of_weak v vk hweak (Complex.imCLM.comp M)
    simp only [ContinuousLinearMap.comp_apply, Complex.reCLM_apply, Complex.imCLM_apply]
      at hre him
    have key : Tendsto (fun i => M (vk i)) atTop (𝓝 (M v)) := by
      rw [← Complex.re_add_im (M v)]
      have h1 : Tendsto (fun i => ((M (vk i)).re : ℂ)) atTop (𝓝 (((M v).re : ℝ) : ℂ)) :=
        (Complex.continuous_ofReal.tendsto _).comp hre
      have h2 : Tendsto (fun i => ((M (vk i)).im : ℂ)) atTop (𝓝 (((M v).im : ℝ) : ℂ)) :=
        (Complex.continuous_ofReal.tendsto _).comp him
      exact (h1.add (h2.mul_const Complex.I)).congr (fun i => Complex.re_add_im (M (vk i)))
    have hnorm : Tendsto (fun i => ENNReal.ofReal (‖M (vk i)‖ ^ 2)) atTop
        (𝓝 (ENNReal.ofReal (‖M v‖ ^ 2))) :=
      (ENNReal.continuous_ofReal.tendsto _).comp ((key.norm).pow 2)
    simp only [hGdef, hMapp]
    exact hnorm
  -- Fatou / finite-subsum exhaustion, exactly as in `viscousEnn_lsc`.
  rw [hunfold v, ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  have hsum : Tendsto (fun i => ∑ p ∈ s, G p (vk i)) atTop (𝓝 (∑ p ∈ s, G p v)) :=
    tendsto_finsetSum s fun p _ => hGtend p
  have hle : ∀ i, ∑ p ∈ s, G p (vk i)
      ≤ ∑ j : Fin 3, ∑' k : {k : Fin 3 → ℤ // k ∉ fourierBox N},
        ENNReal.ofReal (‖mFourierCoeff3 (L2VF_projComponentC j (vk i)) (k : Fin 3 → ℤ)‖ ^ 2) :=
    fun i => by rw [hunfold (vk i)]; exact ENNReal.sum_le_tsum s
  calc ∑ p ∈ s, G p v
      = Filter.liminf (fun i => ∑ p ∈ s, G p (vk i)) atTop := hsum.liminf_eq.symm
    _ ≤ _ := Filter.liminf_le_liminf (Filter.Eventually.of_forall hle)

/-- (P0.12) Weak-convergence upgrade `L2Sigma` tests → all `L2VF` tests, via the Leray
projection: for div-free `v n, u`, testing against `y : L2VF` equals testing against
`L2Sigma.starProjection y ∈ L2Sigma`.  Makes P0.6c's premise reachable from the T-AL-4
capstone's weak-convergence conjunct. -/
theorem tendsto_inner_L2VF_of_tendsto_inner_L2Sigma
    (v : ℕ → L2Sigma) (u : L2Sigma)
    (h : ∀ z : L2Sigma, Tendsto (fun n => inner (𝕜 := ℝ) ((v n : L2VF)) ((z : L2VF)))
      atTop (𝓝 (inner (𝕜 := ℝ) ((u : L2VF)) ((z : L2VF)))))
    (y : L2VF) :
    Tendsto (fun n => inner (𝕜 := ℝ) ((v n : L2VF)) y) atTop
      (𝓝 (inner (𝕜 := ℝ) ((u : L2VF)) y)) := by
  -- `starProjection y ∈ L2Sigma`; test against it and use symmetry + fixed-point of L2Sigma.
  have hmem : L2Sigma.starProjection y ∈ L2Sigma := L2Sigma.starProjection_apply_mem y
  have key := h ⟨L2Sigma.starProjection y, hmem⟩
  have hvn : ∀ n, inner (𝕜 := ℝ) ((v n : L2VF)) (L2Sigma.starProjection y)
      = inner (𝕜 := ℝ) ((v n : L2VF)) y := fun n => by
    rw [← lerayProjection_isSymmetric, lerayProjection_fixes_divFree _ (v n).2]
  have hu_eq : inner (𝕜 := ℝ) ((u : L2VF)) (L2Sigma.starProjection y)
      = inner (𝕜 := ℝ) ((u : L2VF)) y := by
    rw [← lerayProjection_isSymmetric, lerayProjection_fixes_divFree _ u.2]
  rw [hu_eq] at key
  exact key.congr hvn

/-- (P0.13) ENNReal bridge for the tail identity: valid for EVERY `v : L2VF` (the mode
tail is a sub-family of the always-summable Parseval family; no `memH1VF` needed).
Connects the real integrals of P0.14/P0.15 to P0.6c's ENNReal mode sums. -/
theorem ofReal_tail_sq_eq_tailEnn (N : ℕ) (v : L2VF) :
    ENNReal.ofReal (‖v - velocityProjection_n N v‖ ^ 2) =
      ∑ j : Fin 3, ∑' k : {k : Fin 3 → ℤ // k ∉ fourierBox N},
        ENNReal.ofReal (‖mFourierCoeff3 (L2VF_projComponentC j v) k‖ ^ 2) := by
  rw [L2VF_norm_sub_velocityProjection_sq,
    ENNReal.ofReal_sum_of_nonneg (fun j _ => tsum_nonneg fun k => by positivity)]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hsummable : Summable (fun i : {k : Fin 3 → ℤ // k ∉ fourierBox N} =>
      ‖mFourierCoeff3 (L2VF_projComponentC j v) (i : Fin 3 → ℤ)‖ ^ 2) :=
    (Torus.summable_norm_mFourierCoeff3_sq (L2VF_projComponentC j v)).subtype _
  rw [ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hsummable]

/-- (P0.14) Step E, Galerkin side — the n-UNIFORM tail integral bound.  Pointwise
P0.6b (fed by `reg_mem : ∀ t, memH1VF (u_n t)`), interval-integral monotonicity
(integrands continuous: `galerkin_u_continuousOn` + CLM for the LHS, P0.6b′ for the
majorant), then the `reg_bound` field divided by `1 + N²`.  No `0 < ν` binder: the
chain runs entirely through `reg_bound`. -/
theorem integral_tail_sq_galerkin_le
    (F : Torus3NSForms) (ν : ℝ) (u₀ : L2Sigma) (n : ℕ)
    (D : GalerkinSolutionData F ν u₀ n) (T : ℝ) (hT : 0 < T) (N : ℕ) :
    ∫ t in (0 : ℝ)..T,
        ‖(D.u t : L2VF) - velocityProjection_n N ((D.u t : L2VF))‖ ^ 2
      ≤ (T * ‖(u₀ : L2VF)‖ ^ 2 + ‖(u₀ : L2VF)‖ ^ 2 / (2 * ν)) / (1 + (N : ℝ) ^ 2) := by
  -- continuity of the Galerkin curve on `[0,T]`
  have hcurve : ContinuousOn (fun t => (D.u t : L2VF)) (Icc 0 T) :=
    fun s hs => ((D.u_hasDeriv s hs.1).continuousAt).continuousWithinAt
  -- LHS integrand is continuous on `[0,T]`, hence interval-integrable
  have hlhs_cont : ContinuousOn
      (fun t => ‖(D.u t : L2VF) - velocityProjection_n N (D.u t : L2VF)‖ ^ 2) (Icc 0 T) :=
    (ContinuousOn.norm
      (hcurve.sub ((velocityProjection_n N).continuous.comp_continuousOn hcurve))).pow 2
  have hlhs_int : IntervalIntegrable
      (fun t => ‖(D.u t : L2VF) - velocityProjection_n N (D.u t : L2VF)‖ ^ 2)
      MeasureTheory.volume 0 T := hlhs_cont.intervalIntegrable_of_Icc hT.le
  -- majorant `h1EnergySq (u t) / (1 + N²)` is continuous on `[0,T]`, hence interval-integrable
  have hmaj_cont : ContinuousOn
      (fun t => h1EnergySq (D.u t : L2VF) / (1 + (N : ℝ) ^ 2)) (Icc 0 T) :=
    ((h1EnergySq_continuousOn_galerkin F ν u₀ n D).mono Set.Icc_subset_Ici_self).div_const _
  have hmaj_int : IntervalIntegrable
      (fun t => h1EnergySq (D.u t : L2VF) / (1 + (N : ℝ) ^ 2))
      MeasureTheory.volume 0 T := hmaj_cont.intervalIntegrable_of_Icc hT.le
  -- pointwise tail bound (P0.6b) via `reg_mem`
  have hmono := intervalIntegral.integral_mono_on hT.le hlhs_int hmaj_int
    (fun t _ => tail_sq_le_h1EnergySq_div N (D.u t : L2VF) (D.reg_mem t))
  rw [intervalIntegral.integral_div] at hmono
  refine hmono.trans ?_
  gcongr
  exact D.reg_bound T hT

/-- (P0.15) Step E, limit side — the SAME tail bound for the limit curve, WITHOUT any
`memH1VF (u t)` (none is available; smuggling it would be unsound).  Route: P0.13 turns
the pointwise tails into ENNReal mode sums; P0.12 upgrades `hweak` to `L2VF` tests;
P0.6c gives pointwise-in-`t` lsc under the weak convergence; `lintegral` Fatou in `t`;
P0.14 bounds the Galerkin side; `hν` + `hub`/`hmeas` close the `toReal` round-trip
(bound nonneg; limit tail integrable from the `2‖u₀‖` bound on the finite measure). -/
theorem integral_tail_sq_limit_le
    (F : Torus3NSForms) (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T)
    (u₀ : L2Sigma) (galSeq : ∀ n, GalerkinSolutionData F ν u₀ n)
    (φ : ℕ → ℕ) (u : Time → L2Sigma)
    (_hub : ∀ t ∈ Icc (0 : ℝ) T, ‖(u t : L2VF)‖ ≤ ‖(u₀ : L2VF)‖)
    (hmeas : AEStronglyMeasurable (fun t => (u t : L2VF))
      (volume.restrict (Icc (0 : ℝ) T)))
    (hweak : ∀ t ∈ Icc (0 : ℝ) T, ∀ z : L2Sigma,
      Tendsto (fun n => inner (𝕜 := ℝ) (((galSeq (φ n)).u t : L2VF)) ((z : L2VF)))
        atTop (𝓝 (inner (𝕜 := ℝ) ((u t : L2VF)) ((z : L2VF)))))
    (N : ℕ) :
    ∫ t in (0 : ℝ)..T,
        ‖(u t : L2VF) - velocityProjection_n N ((u t : L2VF))‖ ^ 2
      ≤ (T * ‖(u₀ : L2VF)‖ ^ 2 + ‖(u₀ : L2VF)‖ ^ 2 / (2 * ν)) / (1 + (N : ℝ) ^ 2) := by
  set c : ℝ := (T * ‖(u₀ : L2VF)‖ ^ 2 + ‖(u₀ : L2VF)‖ ^ 2 / (2 * ν)) / (1 + (N : ℝ) ^ 2) with hcdef
  have hc0 : 0 ≤ c :=
    div_nonneg
      (add_nonneg (mul_nonneg hT.le (sq_nonneg _))
        (div_nonneg (sq_nonneg _) (mul_pos two_pos hν).le))
      (by positivity)
  -- ═══ pointwise-in-`t` weak lower-semicontinuity (P0.13 bridge + P0.6c, via P0.12) ═══
  have hpt : ∀ t ∈ Icc (0 : ℝ) T,
      ENNReal.ofReal (‖(u t : L2VF) - velocityProjection_n N (u t : L2VF)‖ ^ 2)
        ≤ Filter.liminf (fun i => ENNReal.ofReal
            (‖((galSeq (φ i)).u t : L2VF)
              - velocityProjection_n N ((galSeq (φ i)).u t : L2VF)‖ ^ 2)) atTop := by
    intro t ht
    have hw : ∀ y : L2VF,
        Tendsto (fun i => inner (𝕜 := ℝ) (((galSeq (φ i)).u t : L2VF)) y) atTop
          (𝓝 (inner (𝕜 := ℝ) ((u t : L2VF)) y)) := fun y =>
      tendsto_inner_L2VF_of_tendsto_inner_L2Sigma
        (fun i => (galSeq (φ i)).u t) (u t) (hweak t ht) y
    have h1 := tailEnn_lsc_of_weak N (u t : L2VF) (fun i => ((galSeq (φ i)).u t : L2VF)) hw
    rw [← ofReal_tail_sq_eq_tailEnn N (u t : L2VF)] at h1
    have hR : (fun i => ∑ j : Fin 3, ∑' k : {k : Fin 3 → ℤ // k ∉ fourierBox N},
          ENNReal.ofReal
            (‖mFourierCoeff3 (L2VF_projComponentC j ((galSeq (φ i)).u t : L2VF)) k‖ ^ 2))
        = fun i => ENNReal.ofReal (‖((galSeq (φ i)).u t : L2VF)
            - velocityProjection_n N ((galSeq (φ i)).u t : L2VF)‖ ^ 2) := by
      funext i; exact (ofReal_tail_sq_eq_tailEnn N _).symm
    rw [hR] at h1
    exact h1
  -- ═══ measurability of the Galerkin ENNReal integrands ═══
  have hcurve_meas : ∀ m : ℕ, AEStronglyMeasurable (fun t => ((galSeq m).u t : L2VF))
      (volume.restrict (Icc (0 : ℝ) T)) := fun m =>
    ContinuousOn.aestronglyMeasurable
      (fun s hs => (((galSeq m).u_hasDeriv s hs.1).continuousAt).continuousWithinAt)
      measurableSet_Icc
  have hG_aemeas : ∀ i, AEMeasurable (fun t => ENNReal.ofReal
      (‖((galSeq (φ i)).u t : L2VF)
        - velocityProjection_n N ((galSeq (φ i)).u t : L2VF)‖ ^ 2))
      (volume.restrict (Icc 0 T)) := by
    intro i
    have h1 := hcurve_meas (φ i)
    have h2 : AEStronglyMeasurable
        (fun t => velocityProjection_n N ((galSeq (φ i)).u t : L2VF))
        (volume.restrict (Icc 0 T)) :=
      (velocityProjection_n N).continuous.comp_aestronglyMeasurable h1
    exact ENNReal.measurable_ofReal.comp_aemeasurable
      ((continuous_pow 2).comp_aestronglyMeasurable ((h1.sub h2).norm)).aemeasurable
  -- ═══ per-approximant tail-integral bound (P0.14), transported to `∫⁻` ═══
  have hbi : ∀ i, ∫⁻ t, ENNReal.ofReal
      (‖((galSeq (φ i)).u t : L2VF)
        - velocityProjection_n N ((galSeq (φ i)).u t : L2VF)‖ ^ 2)
      ∂(volume.restrict (Icc 0 T)) ≤ ENNReal.ofReal c := by
    intro i
    have hcont : ContinuousOn (fun t => ‖((galSeq (φ i)).u t : L2VF)
        - velocityProjection_n N ((galSeq (φ i)).u t : L2VF)‖ ^ 2) (Icc 0 T) := by
      have hcurve : ContinuousOn (fun t => ((galSeq (φ i)).u t : L2VF)) (Icc 0 T) :=
        fun s hs => (((galSeq (φ i)).u_hasDeriv s hs.1).continuousAt).continuousWithinAt
      exact (ContinuousOn.norm (hcurve.sub
        ((velocityProjection_n N).continuous.comp_continuousOn hcurve))).pow 2
    have hInt : Integrable (fun t => ‖((galSeq (φ i)).u t : L2VF)
        - velocityProjection_n N ((galSeq (φ i)).u t : L2VF)‖ ^ 2)
        (volume.restrict (Icc 0 T)) := hcont.integrableOn_Icc
    have hnn : 0 ≤ᵐ[volume.restrict (Icc 0 T)]
        (fun t => ‖((galSeq (φ i)).u t : L2VF)
          - velocityProjection_n N ((galSeq (φ i)).u t : L2VF)‖ ^ 2) :=
      Filter.Eventually.of_forall fun t => sq_nonneg _
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt hnn]
    apply ENNReal.ofReal_le_ofReal
    have hval : ∫ t, ‖((galSeq (φ i)).u t : L2VF)
        - velocityProjection_n N ((galSeq (φ i)).u t : L2VF)‖ ^ 2
        ∂(volume.restrict (Icc 0 T))
        = ∫ t in (0 : ℝ)..T, ‖((galSeq (φ i)).u t : L2VF)
            - velocityProjection_n N ((galSeq (φ i)).u t : L2VF)‖ ^ 2 := by
      rw [intervalIntegral.integral_of_le hT.le, MeasureTheory.integral_Icc_eq_integral_Ioc]
    rw [hval]
    exact integral_tail_sq_galerkin_le F ν u₀ (φ i) (galSeq (φ i)) T hT N
  -- ═══ Fatou in time: `∫⁻ ofReal(tail limit) ≤ ofReal c` ═══
  have hbound : ∫⁻ t, ENNReal.ofReal (‖(u t : L2VF) - velocityProjection_n N (u t : L2VF)‖ ^ 2)
      ∂(volume.restrict (Icc 0 T)) ≤ ENNReal.ofReal c := by
    have hpt_ae : ∀ᵐ t ∂(volume.restrict (Icc 0 T)),
        ENNReal.ofReal (‖(u t : L2VF) - velocityProjection_n N (u t : L2VF)‖ ^ 2)
          ≤ Filter.liminf (fun i => ENNReal.ofReal
              (‖((galSeq (φ i)).u t : L2VF)
                - velocityProjection_n N ((galSeq (φ i)).u t : L2VF)‖ ^ 2)) atTop :=
      (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mpr
        (Filter.Eventually.of_forall fun t ht => hpt t ht)
    calc ∫⁻ t, ENNReal.ofReal (‖(u t : L2VF) - velocityProjection_n N (u t : L2VF)‖ ^ 2)
            ∂(volume.restrict (Icc 0 T))
        ≤ ∫⁻ t, Filter.liminf (fun i => ENNReal.ofReal
            (‖((galSeq (φ i)).u t : L2VF)
              - velocityProjection_n N ((galSeq (φ i)).u t : L2VF)‖ ^ 2)) atTop
            ∂(volume.restrict (Icc 0 T)) := lintegral_mono_ae hpt_ae
      _ ≤ Filter.liminf (fun i => ∫⁻ t, ENNReal.ofReal
            (‖((galSeq (φ i)).u t : L2VF)
              - velocityProjection_n N ((galSeq (φ i)).u t : L2VF)‖ ^ 2)
            ∂(volume.restrict (Icc 0 T))) atTop := lintegral_liminf_le' hG_aemeas
      _ ≤ Filter.liminf (fun _ : ℕ => ENNReal.ofReal c) atTop :=
            Filter.liminf_le_liminf (Filter.Eventually.of_forall hbi)
      _ = ENNReal.ofReal c := Filter.liminf_const _
  -- ═══ `toReal` round-trip: reduce the interval integral and close ═══
  rw [intervalIntegral.integral_of_le hT.le, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  have hf_nn : 0 ≤ᵐ[volume.restrict (Icc 0 T)]
      (fun t => ‖(u t : L2VF) - velocityProjection_n N (u t : L2VF)‖ ^ 2) :=
    Filter.Eventually.of_forall fun t => sq_nonneg _
  have hf_aesm : AEStronglyMeasurable
      (fun t => ‖(u t : L2VF) - velocityProjection_n N (u t : L2VF)‖ ^ 2)
      (volume.restrict (Icc 0 T)) := by
    have h2 := (velocityProjection_n N).continuous.comp_aestronglyMeasurable hmeas
    exact (continuous_pow 2).comp_aestronglyMeasurable (hmeas.sub h2).norm
  have hf_int : Integrable
      (fun t => ‖(u t : L2VF) - velocityProjection_n N (u t : L2VF)‖ ^ 2)
      (volume.restrict (Icc 0 T)) :=
    ⟨hf_aesm, (MeasureTheory.hasFiniteIntegral_iff_ofReal hf_nn).mpr
      (lt_of_le_of_lt hbound ENNReal.ofReal_lt_top)⟩
  have hfinal : ENNReal.ofReal (∫ t, ‖(u t : L2VF)
      - velocityProjection_n N (u t : L2VF)‖ ^ 2 ∂(volume.restrict (Icc 0 T)))
      ≤ ENNReal.ofReal c := by
    rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hf_int hf_nn]; exact hbound
  exact (ENNReal.ofReal_le_ofReal_iff hc0).mp hfinal

end LerayHopf
