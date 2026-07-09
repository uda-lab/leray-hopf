import LerayHopf.R3.GoodRepresentative
import LerayHopf.R3.GalerkinCurveBounds

/-! # LerayHopf.R3.LimitPassage — PROVED `galerkin_limit_passage_R3`

This file provides the **proved replacement** for the former project axiom
`galerkin_limit_passage_R3` (AX-3, issue #4).  The proof assembles four earlier
PR-level deliverables:

| Source | What it contributes |
|---|---|
| `GoodRepresentative` | The ∀t-weakly-continuous representative `v`, initial data `v 0 = u₀`, and Lipschitz-over-Galerkin-tests condition for the strong trace |
| `AubinLionsLimitPassage.weakFormNS_limit_passage` | `WeakFormNS` for `alPkg.u`; transferred to `v` via a.e. equality |
| `AubinLionsLimitPassage.viscous_pointwise_lsc` | a.e. ENNReal viscous-form lsc on `[0,T]` (ν = 1 form) |
| `GalerkinCurveBounds.galerkinCurve_energy_identity` | Per-n exact energy identity `½‖cₙ(t)‖² + ∫₀ᵗ ν·V₁(cₙ) = ½‖cₙ(0)‖²` |

The three main pieces are:

1. `energy_ineq_of_representative_R3` (private) — ∀t energy inequality for `v`,
   using `normSq_le_liminf_of_inner_tendsto` (kinetic lsc) + Fatou + liminf
   superadditivity (`le_liminf_add`).

2. `galerkin_limit_passage_R3` (theorem) — the 5-conjunct good-representative
   existential, assembling the above with `strong_trace_of_props_R3`.

## Context in the campaign

This file is the **final PR (PR-6)** of the six-PR `galerkin_limit_passage_R3`
removal campaign (issue #4).  After this file, `exists_lerayHopf_r3` has
**zero project axioms** (`#print axioms` = kernel-only: `propext`,
`Classical.choice`, `Quot.sound`).
-/

namespace LerayHopf

open MeasureTheory Filter Topology Set intervalIntegral

/-- **∀t energy inequality for the good representative** (private helper).

Given the good representative `v` produced by `exists_weak_representative_R3`, prove
the Leray–Hopf energy inequality `½‖v(t)‖² + ∫₀ᵗ ν·V₁(v) ≤ ½‖u₀‖²` for every
`t ∈ [0,T]`.  The proof follows the torus `energy_ineq_of_representative` template:

- **Kinetic lsc** via `normSq_le_liminf_of_inner_tendsto`: weak-∀t convergence `cₙ(t) ⇀ v(t)`
  + uniform bound `‖cₙ(t)‖ ≤ ‖u₀‖` imply `‖v(t)‖² ≤ liminf ‖cₙ(t)‖²`.
- **Viscous Fatou** (ν = 1): `viscous_pointwise_lsc` gives the a.e. ENNReal pointwise
  bound; Fatou (`lintegral_liminf_le'`) + `Monotone.map_liminf_of_continuousAt`
  give `∫₀ᵗ V₁(v) ≤ liminf_n ∫₀ᵗ V₁(cₙ)`.
- **Scaling**: `∫₀ᵗ ν·V₁(v) ≤ liminf_n ∫₀ᵗ ν·V₁(cₙ)` via real liminf commutativity.
- **Superadditivity** (`le_liminf_add`) + per-n energy identity close the bound. -/
private theorem energy_ineq_of_representative_R3
    (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T) (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n)
    (alPkg : AubinLionsPackage_R3 𝔊 F ν T u₀ galSeq)
    (v : Time → L2Sigma_R3)
    (hae : ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)), v t = alPkg.u t)
    (hweak : ∀ t, t ∈ Set.Icc (0 : ℝ) T → ∀ z : L2VF_R3,
      Tendsto (fun n => inner (𝕜 := ℝ) (((galSeq (alPkg.φ n)).u t : L2VF_R3)) z) atTop
        (𝓝 (inner (𝕜 := ℝ) ((v t : L2VF_R3)) z)))
    (hInt : IntervalIntegrable (fun s => viscousFormSq_R3 ν (v s : L2VF_R3))
        MeasureTheory.volume 0 T) :
    ∀ t, 0 ≤ t → t ≤ T →
      (1 / 2 : ℝ) * ‖(v t : L2VF_R3)‖ ^ 2 +
        ∫ s in (0 : ℝ)..t, viscousFormSq_R3 ν (v s : L2VF_R3) ≤
      (1 / 2 : ℝ) * ‖(u₀ : L2VF_R3)‖ ^ 2 := by
  intro t ht0 htT
  have htIcc : t ∈ Set.Icc (0 : ℝ) T := ⟨ht0, htT⟩
  -- abbreviations
  set c : ℕ → ℝ → L2VF_R3 := fun n s => ((galSeq (alPkg.φ n)).u s : L2VF_R3) with hcdef
  set E : ℝ := (1 / 2 : ℝ) * ‖(u₀ : L2VF_R3)‖ ^ 2 with hEdef
  set a : ℕ → ℝ := fun n => (1 / 2 : ℝ) * ‖c n t‖ ^ 2 with hadef
  -- ν = 1 dissipation integrals for approximants
  set b : ℕ → ℝ :=
    fun n => ∫ s in (0 : ℝ)..t, viscousFormSq_R3 1 (c n s) with hbdef
  -- ════ Per-n energy bound: a n + ν * b n ≤ E ════
  have hab : ∀ n, a n + ν * b n ≤ E := by
    intro n
    -- energy identity: ½‖c n t‖² - ½‖c n 0‖² = -∫₀ᵗ ν·V₁(c n)
    have hid :=
      galerkinCurve_energy_identity (galSeq (alPkg.φ n)) 0 t (le_refl 0) ht0
    -- ∫₀ᵗ viscous_ν(c n) = ν * b n
    have hscale : ∫ s in (0 : ℝ)..t, viscousFormSq_R3 ν (c n s) = ν * b n := by
      rw [hbdef, ← intervalIntegral.integral_const_mul]
      refine integral_congr (fun s _ => ?_)
      rw [viscousFormSq_R3_eq_smul, smul_eq_mul]
    -- a n + ν * b n = ½‖c n 0‖² (exact from identity + scale)
    -- hid : ½‖c n t‖² - ½‖c n 0‖² = -∫₀ᵗ viscous_ν(c n)
    -- hscale : ∫₀ᵗ viscous_ν(c n) = ν * b n
    have hid' : a n + ν * b n = (1 / 2 : ℝ) * ‖c n 0‖ ^ 2 := by
      have : (1 / 2 : ℝ) * ‖c n t‖ ^ 2 - (1 / 2 : ℝ) * ‖c n 0‖ ^ 2 = -(ν * b n) := by
        rw [← hscale]; exact hid
      -- a n = (1/2) * ‖c n t‖² by the `set` definition; provide it explicitly to linarith
      linarith [this, show a n = (1 / 2 : ℝ) * ‖c n t‖ ^ 2 from rfl]
    -- norm bound: ‖c n 0‖ ≤ ‖u₀‖
    have hn0 : ‖c n 0‖ ≤ ‖(u₀ : L2VF_R3)‖ :=
      galerkin_norm_le_u0 𝔊 F ν u₀ (alPkg.φ n) (galSeq (alPkg.φ n)) (le_refl 0)
    linarith [pow_le_pow_left₀ (norm_nonneg (c n 0)) hn0 2, hid']
  have ha0 : ∀ n, 0 ≤ a n := fun n => by positivity
  have hb0 : ∀ n, 0 ≤ b n := fun n =>
    integral_nonneg ht0 fun s _ => viscousFormSq_R3_nonneg (by norm_num) _
  have haE : ∀ n, a n ≤ E := fun n => by linarith [hab n, mul_nonneg hν.le (hb0 n)]
  have hbM : ∀ n, b n ≤ ν⁻¹ * E := fun n => by
    rw [le_inv_mul_iff₀ hν]; linarith [hab n, ha0 n]
  -- ════ Kinetic: (1/2)‖v t‖² ≤ liminf a ════
  have hkin_normSq : ‖(v t : L2VF_R3)‖ ^ 2 ≤
      Filter.liminf (fun n => ‖c n t‖ ^ 2) atTop := by
    refine normSq_le_liminf_of_inner_tendsto ((v t : L2VF_R3)) (fun n => c n t)
      ‖(u₀ : L2VF_R3)‖
      (fun n => galerkin_norm_le_u0 𝔊 F ν u₀ (alPkg.φ n) (galSeq (alPkg.φ n)) ht0) ?_
    have h := hweak t htIcc ((v t : L2VF_R3))
    rwa [real_inner_self_eq_norm_sq] at h
  have hbdd_below_normsq : IsBoundedUnder (· ≥ ·) atTop (fun n => ‖c n t‖ ^ 2) :=
    isBoundedUnder_of_eventually_ge (a := 0)
      (Eventually.of_forall fun n => by positivity)
  have hbdd_above_normsq : IsBoundedUnder (· ≤ ·) atTop (fun n => ‖c n t‖ ^ 2) :=
    isBoundedUnder_of_eventually_le (a := ‖(u₀ : L2VF_R3)‖ ^ 2)
      (Eventually.of_forall fun n =>
        pow_le_pow_left₀ (norm_nonneg _)
          (galerkin_norm_le_u0 𝔊 F ν u₀ (alPkg.φ n) (galSeq (alPkg.φ n)) ht0) 2)
  have hkin : (1 / 2 : ℝ) * ‖(v t : L2VF_R3)‖ ^ 2 ≤ Filter.liminf a atTop := by
    have hmono : Monotone (fun r : ℝ => (1 / 2 : ℝ) * r) :=
      fun x y hxy => mul_le_mul_of_nonneg_left hxy (by norm_num)
    have hmap :=
      hmono.map_liminf_of_continuousAt (fun n => ‖c n t‖ ^ 2)
        (continuous_const.mul continuous_id).continuousAt
        hbdd_above_normsq.isCoboundedUnder_ge hbdd_below_normsq
    -- a n = (1/2) * ‖c n t‖² by the `set` definition, so liminf a = liminf (1/2 * ‖c n t‖²)
    -- hmap : 1/2 * liminf (‖c n t‖²) = liminf ((1/2 * ·) ∘ (‖c n t‖²))
    -- The rhs of hmap equals liminf a (by definitional equality of a)
    have ha_eq : Filter.liminf a atTop =
        Filter.liminf ((fun r : ℝ => (1 / 2 : ℝ) * r) ∘ fun n => ‖c n t‖ ^ 2) atTop := rfl
    linarith [mul_le_mul_of_nonneg_left hkin_normSq (by norm_num : (0:ℝ) ≤ 1/2),
              hmap.le, ha_eq.ge]
  -- ════ Viscous Fatou (ν = 1 form): ∫₀ᵗ V₁(v) ≤ liminf b ════
  have hbdd_below_b : IsBoundedUnder (· ≥ ·) atTop b :=
    isBoundedUnder_of_eventually_ge (a := 0) (Eventually.of_forall hb0)
  have hcobdd_b : IsCoboundedUnder (· ≥ ·) atTop b :=
    (isBoundedUnder_of_eventually_le (a := ν⁻¹ * E)
      (Eventually.of_forall hbM)).isCoboundedUnder_ge
  have hliminfb0 : 0 ≤ Filter.liminf b atTop :=
    le_liminf_of_le hcobdd_b (Eventually.of_forall hb0)
  -- integrability of V₁(v) on [0,t] (from hInt by ν⁻¹-scaling)
  have hInt1 : IntervalIntegrable
      (fun s => viscousFormSq_R3 1 (v s : L2VF_R3)) MeasureTheory.volume 0 t := by
    have hInt1T : IntervalIntegrable
        (fun s => viscousFormSq_R3 1 (v s : L2VF_R3)) MeasureTheory.volume 0 T := by
      have heq : (fun s => viscousFormSq_R3 1 (v s : L2VF_R3)) =
          fun s => ν⁻¹ * viscousFormSq_R3 ν (v s : L2VF_R3) := by
        ext s
        conv_rhs => rw [viscousFormSq_R3_eq_smul]
        rw [smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hν.ne', one_mul]
      rw [heq]
      exact hInt.const_mul ν⁻¹
    exact hInt1T.mono_set (uIcc_subset_uIcc left_mem_uIcc
      (by rw [uIcc_of_le hT.le]; exact ⟨ht0, htT⟩))
  have hfIntOn1 : IntegrableOn (fun s => viscousFormSq_R3 1 (v s : L2VF_R3))
      (Set.Ioc 0 t) MeasureTheory.volume := hInt1.1
  -- real integral = lintegral.toReal (ν = 1 form)
  have hreal1 :
      ∫ s in (0 : ℝ)..t, viscousFormSq_R3 1 (v s : L2VF_R3) =
      (∫⁻ s in Set.Ioc (0 : ℝ) t,
          ENNReal.ofReal (viscousFormSq_R3 1 (v s : L2VF_R3))).toReal := by
    rw [integral_of_le ht0]
    exact integral_eq_lintegral_of_nonneg_ae
      (Eventually.of_forall fun s => viscousFormSq_R3_nonneg (by norm_num) _)
      hfIntOn1.aestronglyMeasurable
  -- a.e. ENNReal lsc on [0,t] (restrict viscous_pointwise_lsc + v = alPkg.u a.e.)
  have hsub : Set.Ioc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T :=
    fun s hs => ⟨hs.1.le, hs.2.trans htT⟩
  have hae' : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) t)), v s = alPkg.u s :=
    ae_restrict_of_ae_restrict_of_subset hsub hae
  obtain ⟨_, hptwise⟩ := viscous_pointwise_lsc 𝔊 F ν T hν hT u₀ galSeq alPkg
  have hptwise' :
      ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) t)),
      ENNReal.ofReal (viscousFormSq_R3 1 (alPkg.u s : L2VF_R3)) ≤
        Filter.atTop.liminf
          (fun n => ENNReal.ofReal (viscousFormSq_R3 1 ((galSeq (alPkg.φ n)).u s : L2VF_R3))) := by
    exact ae_restrict_of_ae_restrict_of_subset hsub
      (by filter_upwards [hptwise] with s hs; exact hs.2)
  have hae_lsc :
      ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) t)),
      ENNReal.ofReal (viscousFormSq_R3 1 (v s : L2VF_R3)) ≤
        Filter.atTop.liminf
          (fun n => ENNReal.ofReal (viscousFormSq_R3 1 (c n s))) := by
    filter_upwards [hae', hptwise'] with s hveq hbound
    have hcoe : (v s : L2VF_R3) = (alPkg.u s : L2VF_R3) := congrArg _ hveq
    rw [hcoe]; exact hbound
  -- AEMeasurability of approximant integrands on Ioc 0 t
  have hmeas_k : ∀ n,
      AEMeasurable (fun s => ENNReal.ofReal (viscousFormSq_R3 1 (c n s)))
        (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) t)) := fun n =>
    ENNReal.measurable_ofReal.comp_aemeasurable
      ((viscousFormSq_curve_continuousOn 𝔊 F ν u₀ (alPkg.φ n) (galSeq (alPkg.φ n))).mono
        (fun s hs => hs.1.le) |>.aemeasurable measurableSet_Ioc)
  -- Fatou: ∫⁻ V₁(v) ≤ liminf_n ∫⁻ V₁(c n)
  have hFatou :
      ∫⁻ s in Set.Ioc (0 : ℝ) t, ENNReal.ofReal (viscousFormSq_R3 1 (v s : L2VF_R3)) ≤
      Filter.atTop.liminf
        (fun n => ∫⁻ s in Set.Ioc (0 : ℝ) t,
            ENNReal.ofReal (viscousFormSq_R3 1 (c n s))) :=
    (MeasureTheory.lintegral_mono_ae hae_lsc).trans (MeasureTheory.lintegral_liminf_le' hmeas_k)
  -- Each approximant lintegral = ofReal (b n)
  have hbk_eq : ∀ n,
      ∫⁻ s in Set.Ioc (0 : ℝ) t, ENNReal.ofReal (viscousFormSq_R3 1 (c n s)) =
      ENNReal.ofReal (b n) := by
    intro n
    have hcont : ContinuousOn (fun s => viscousFormSq_R3 1 (c n s)) (Set.Icc 0 t) :=
      (viscousFormSq_curve_continuousOn 𝔊 F ν u₀ (alPkg.φ n) (galSeq (alPkg.φ n))).mono
        (fun s hs => hs.1)
    have hint : IntegrableOn (fun s => viscousFormSq_R3 1 (c n s)) (Set.Ioc 0 t) MeasureTheory.volume :=
      (hcont.intervalIntegrable_of_Icc ht0).1
    have h1 : b n =
        (∫⁻ s in Set.Ioc (0 : ℝ) t,
          ENNReal.ofReal (viscousFormSq_R3 1 (c n s))).toReal := by
      rw [hbdef]; simp only
      rw [integral_of_le ht0]
      exact integral_eq_lintegral_of_nonneg_ae
        (Eventually.of_forall fun s => viscousFormSq_R3_nonneg (by norm_num) _)
        hint.aestronglyMeasurable
    have h2 : ∫⁻ s in Set.Ioc (0 : ℝ) t,
        ENNReal.ofReal (viscousFormSq_R3 1 (c n s)) < ⊤ :=
      hint.lintegral_lt_top
    rw [h1, ENNReal.ofReal_toReal h2.ne]
  -- ofReal commutes with the (bounded) real liminf b
  have hcomm :
      Filter.atTop.liminf (fun n => ENNReal.ofReal (b n)) =
      ENNReal.ofReal (Filter.atTop.liminf b) := by
    have hmono : Monotone ENNReal.ofReal := fun x y h => ENNReal.ofReal_le_ofReal h
    exact (hmono.map_liminf_of_continuousAt b
      ENNReal.continuous_ofReal.continuousAt hcobdd_b hbdd_below_b).symm
  -- Chain: ∫⁻ V₁(v) ≤ ofReal (liminf b)
  have hchain :
      ∫⁻ s in Set.Ioc (0 : ℝ) t, ENNReal.ofReal (viscousFormSq_R3 1 (v s : L2VF_R3)) ≤
      ENNReal.ofReal (Filter.atTop.liminf b) := by
    calc ∫⁻ s in Set.Ioc (0 : ℝ) t, ENNReal.ofReal (viscousFormSq_R3 1 (v s : L2VF_R3))
        ≤ Filter.atTop.liminf
            (fun n => ∫⁻ s in Set.Ioc (0 : ℝ) t,
                ENNReal.ofReal (viscousFormSq_R3 1 (c n s))) := hFatou
      _ = Filter.atTop.liminf (fun n => ENNReal.ofReal (b n)) := by
            congr 1; funext n; exact hbk_eq n
      _ = ENNReal.ofReal (Filter.atTop.liminf b) := hcomm
  -- Convert to real: ∫₀ᵗ V₁(v) ≤ liminf b
  have hdiss1 :
      ∫ s in (0 : ℝ)..t, viscousFormSq_R3 1 (v s : L2VF_R3) ≤
      Filter.atTop.liminf b := by
    rw [hreal1]
    calc (∫⁻ s in Set.Ioc (0 : ℝ) t,
            ENNReal.ofReal (viscousFormSq_R3 1 (v s : L2VF_R3))).toReal
        ≤ (ENNReal.ofReal (Filter.atTop.liminf b)).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hchain
      _ = Filter.atTop.liminf b := ENNReal.toReal_ofReal hliminfb0
  -- ════ Scale to ν-form dissipation ════
  -- ∫₀ᵗ viscous_ν(v) = ν * ∫₀ᵗ V₁(v)
  have hdiss_eq :
      ∫ s in (0 : ℝ)..t, viscousFormSq_R3 ν (v s : L2VF_R3) =
      ν * ∫ s in (0 : ℝ)..t, viscousFormSq_R3 1 (v s : L2VF_R3) := by
    rw [← intervalIntegral.integral_const_mul]
    refine integral_congr (fun s _ => ?_)
    rw [viscousFormSq_R3_eq_smul, smul_eq_mul]
  -- ν * liminf b = liminf (ν * b) via real Monotone.map_liminf_of_continuousAt
  have hbdd_below_νb : IsBoundedUnder (· ≥ ·) atTop (fun n => ν * b n) :=
    isBoundedUnder_of_eventually_ge (a := 0)
      (Eventually.of_forall fun n => mul_nonneg hν.le (hb0 n))
  have hcobdd_νb : IsCoboundedUnder (· ≥ ·) atTop (fun n => ν * b n) :=
    (isBoundedUnder_of_eventually_le (a := E)
      (Eventually.of_forall (fun n => by linarith [hab n, ha0 n]))).isCoboundedUnder_ge
  have hν_mul_liminf :
      ν * Filter.atTop.liminf b = Filter.atTop.liminf (fun n => ν * b n) := by
    have hmono : Monotone (fun r : ℝ => ν * r) :=
      fun x y hxy => mul_le_mul_of_nonneg_left hxy hν.le
    exact hmono.map_liminf_of_continuousAt b
      (continuous_const.mul continuous_id).continuousAt hcobdd_b hbdd_below_b
  -- ∫₀ᵗ viscous_ν(v) ≤ liminf (ν * b)
  have hdiss :
      ∫ s in (0 : ℝ)..t, viscousFormSq_R3 ν (v s : L2VF_R3) ≤
      Filter.atTop.liminf (fun n => ν * b n) := by
    calc ∫ s in (0 : ℝ)..t, viscousFormSq_R3 ν (v s : L2VF_R3)
        = ν * ∫ s in (0 : ℝ)..t, viscousFormSq_R3 1 (v s : L2VF_R3) := hdiss_eq
      _ ≤ ν * Filter.atTop.liminf b := mul_le_mul_of_nonneg_left hdiss1 hν.le
      _ = Filter.atTop.liminf (fun n => ν * b n) := hν_mul_liminf
  -- ════ Superadditivity: liminf a + liminf (ν*b) ≤ liminf (a + ν*b) ≤ E ════
  have hbdd_below_a : IsBoundedUnder (· ≥ ·) atTop a :=
    isBoundedUnder_of_eventually_ge (a := 0) (Eventually.of_forall ha0)
  have hbdd_above_a : IsBoundedUnder (· ≤ ·) atTop a :=
    isBoundedUnder_of_eventually_le (a := E) (Eventually.of_forall haE)
  have hsuper :
      Filter.liminf a atTop + Filter.liminf (fun n => ν * b n) atTop ≤
      Filter.liminf (fun n => a n + ν * b n) atTop :=
    le_liminf_add hbdd_below_a hbdd_above_a hbdd_below_νb hcobdd_νb
  have habE : Filter.liminf (fun n => a n + ν * b n) atTop ≤ E := by
    have hboundedbelow : IsBoundedUnder (· ≥ ·) atTop (fun n => a n + ν * b n) :=
      isBoundedUnder_of_eventually_ge (a := 0)
        (Eventually.of_forall fun n => by linarith [ha0 n, mul_nonneg hν.le (hb0 n)])
    have h1 : Filter.liminf (fun n => a n + ν * b n) atTop ≤
        Filter.liminf (fun _ => E) atTop :=
      Filter.liminf_le_liminf
        (Eventually.of_forall fun n => hab n)
        hboundedbelow
        ((isBoundedUnder_of_eventually_le (a := E)
          (Eventually.of_forall fun _ => le_refl E)).isCoboundedUnder_ge)
    rwa [Filter.liminf_const] at h1
  linarith [hkin, hdiss, hsuper, habE]


/-- **The proved limit-passage existential for ℝ³** (replaces axiom `galerkin_limit_passage_R3`).

Produces a **good representative** `u : Time → L2Sigma_R3` of the Aubin–Lions limit
`alPkg.u` satisfying the five Leray–Hopf conjuncts:

1. **(a.e.-link)** `u t = alPkg.u t` for a.e. `t ∈ [0, T]`.
2. **(WeakFormNS)** `WeakFormNS ν T (r3Evolution 𝔊 F) u` — the weak Navier–Stokes
   equation holds for all admissible test data.
3. **(Energy inequality)** `½‖u(t)‖² + ∫₀ᵗ ν·V₁(u) ≤ ½‖u₀‖²` for all `t ∈ [0, T]`.
4. **(Initial trace)** `u(t) → u₀` strongly in L²_σ(ℝ³) as `t → 0⁺`.
5. **(Energy class)** a.e. `memH1VF_R3 (u t)` + integrable `viscousFormSq_R3 ν (u t)`.

The hypothesis `htest : R3TestApproxH1 𝔊` is the H¹-graph test-approximation property
proved for the concrete Schwartz Galerkin basis in `nonempty_schwartzGalerkinBasis_H1`
(PR-3 / `GalerkinBasisH1.lean`).  It enters through `weakFormNS_limit_passage` (PR-4)
to close the nonlinear limit. -/
theorem galerkin_limit_passage_R3
    (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T)
    (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n)
    (alPkg : AubinLionsPackage_R3 𝔊 F ν T u₀ galSeq)
    (htest : R3TestApproxH1 𝔊) :
    ∃ u : Time → L2Sigma_R3,
    (∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc 0 T)), u t = alPkg.u t) ∧
    WeakFormNS ν T (r3Evolution 𝔊 F) u ∧
    (∀ t, 0 ≤ t → t ≤ T →
      (1 / 2 : ℝ) * ‖(u t : L2VF_R3)‖ ^ 2 +
      ∫ s in (0 : ℝ)..t, viscousFormSq_R3 ν (u s : L2VF_R3) ≤
      (1 / 2 : ℝ) * ‖(u₀ : L2VF_R3)‖ ^ 2) ∧
    Filter.Tendsto
      (fun t => (u t : L2VF_R3))
      (nhdsWithin 0 (Set.Ici 0))
      (nhds (u₀ : L2VF_R3)) ∧
    ((∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc 0 T)), memH1VF_R3 (u t : L2VF_R3)) ∧
    IntervalIntegrable (fun s => viscousFormSq_R3 ν (u s : L2VF_R3))
      MeasureTheory.volume 0 T) := by
  -- ══ Step 1: construct the good representative v ══
  obtain ⟨v, hae, hweak, hbd, hv0, hlip⟩ :=
    exists_weak_representative_R3 𝔊 F ν hν T hT u₀ galSeq alPkg
  -- ══ Step 2: energy class for alPkg.u (and transfer to v) ══
  obtain ⟨hmemH1_u, hVν_ii, _⟩ :=
    viscous_lsc_under_strongL2 𝔊 F ν hν T hT u₀ galSeq alPkg
  -- integrability of ν-form for v, transferred from alPkg.u via a.e. equality
  have hIntv : IntervalIntegrable (fun s => viscousFormSq_R3 ν (v s : L2VF_R3))
      MeasureTheory.volume 0 T := by
    refine hVν_ii.congr_ae ?_
    have h1 : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) T)),
        v s = alPkg.u s := by
      rw [uIoc_of_le hT.le]
      exact ae_restrict_of_ae_restrict_of_subset Set.Ioc_subset_Icc_self hae
    filter_upwards [h1] with s hs
    -- goal: viscous_ν(alPkg.u s) = viscous_ν(v s)
    have hcoe : (alPkg.u s : L2VF_R3) = (v s : L2VF_R3) := congrArg _ hs.symm
    rw [hcoe]
  -- ══ Step 3: WeakFormNS — transfer from alPkg.u to v via a.e. equality ══
  -- Convert restricted a.e. to unrestricted form with membership (for integral_congr_ae)
  have haeIcc_v : ∀ᵐ t ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      t ∈ Set.Icc (0 : ℝ) T → v t = alPkg.u t :=
    (ae_restrict_iff' measurableSet_Icc).mp hae
  have hW : WeakFormNS ν T (r3Evolution 𝔊 F) v := by
    intro ψ hψcs hψsupp hψC1 w hw
    have hWu :=
      (weakFormNS_limit_passage 𝔊 F ν hν T hT u₀ galSeq alPkg htest) ψ hψcs hψsupp hψC1 w hw
    -- step 1: ∫ f(v) = ∫ f(alPkg.u) using a.e. equality v s = alPkg.u s
    have heq : ∫ t in (0:ℝ)..T,
            (-inner (𝕜:=ℝ) (v t) w * deriv ψ t +
              ψ t * (ν * (r3Evolution 𝔊 F).viscousForm (v t) w +
                (r3Evolution 𝔊 F).convForm (v t) (v t) w)) =
          ∫ t in (0:ℝ)..T,
            (-inner (𝕜:=ℝ) (alPkg.u t) w * deriv ψ t +
              ψ t * (ν * (r3Evolution 𝔊 F).viscousForm (alPkg.u t) w +
                (r3Evolution 𝔊 F).convForm (alPkg.u t) (alPkg.u t) w)) := by
      apply intervalIntegral.integral_congr_ae
      -- haeIcc_v : ∀ᵐ t ∂volume, t ∈ Icc 0 T → v t = alPkg.u t
      -- goal after apply: ∀ᵐ x ∂volume, x ∈ uIoc 0 T → integrand_v x = integrand_alPkg x
      filter_upwards [haeIcc_v] with x hx hxI
      have hxIcc : x ∈ Set.Icc (0 : ℝ) T := by
        rw [Set.uIoc_of_le hT.le] at hxI; exact ⟨hxI.1.le, hxI.2⟩
      rw [hx hxIcc]
    linarith [heq]
  -- ══ Step 4: energy class for v — a.e. H¹ from alPkg.u via a.e. equality ══
  have hmemH1_v : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc 0 T)), memH1VF_R3 (v t : L2VF_R3) := by
    filter_upwards [hmemH1_u, hae] with t hmem hveq
    -- hveq : v t = alPkg.u t; rw replaces v t → alPkg.u t in the goal
    rw [hveq]; exact hmem
  -- ══ Assemble the five conjuncts ══
  exact ⟨v, hae, hW,
    energy_ineq_of_representative_R3 𝔊 F ν hν T hT u₀ galSeq alPkg v hae hweak hIntv,
    strong_trace_of_props_R3 𝔊 T hT u₀ v hbd hv0 hlip,
    hmemH1_v, hIntv⟩

end LerayHopf
