/-
# LerayHopf.Torus.ViscousLimit — conjunct (4): energy-class discharge for `alPkg.u` on 𝕋³

**Purpose:** This file discharges the conjunct-(4) energy-class obligation for the
Aubin–Lions limit `alPkg.u`, namely:

- a.e. `memH1VF (alPkg.u t : L2VF)` with respect to `volume.restrict (Set.Icc 0 T)`, and
- `IntervalIntegrable (fun s => viscousFormSq ν (alPkg.u s : L2VF)) volume 0 T`.

This pair of facts is the hypothesis `h4` consumed by
`torus_galerkin_limit_passage_of_energyClass` (in `LerayHopf.Torus.TraceEnergy`), which
assembles the full 5-conjunct existential and thereby completes the removal of the
`galerkin_limit_passage` project axiom.

**Route (sketch for lean-prover):**
1. `alPkg.strong_convergence` gives `eLpNorm`-convergence-to-0 of the Galerkin subsequence
   to `alPkg.u` in L²(0,T; L²_σ); extract an a.e.-strongly-convergent subsequence.
2. Fatou-in-time on the honest `ENNReal`-valued `viscousEnn` (now public in
   `TorusTraceEnergy`) from the Galerkin energy identity gives the a.e. H¹ regularity
   and integrated dissipation bound via monotone-convergence / lim-inf argument.

**Axioms:** None.  This file is sorry-free.

NO import of `LerayHopf/Bochner/TimeSobolev*.lean`; no `W1pTime` witness is used.
-/

import LerayHopf.Torus.SolutionInterfaces
import LerayHopf.Torus.TraceEnergy

namespace LerayHopf

open MeasureTheory Filter Topology intervalIntegral

/-! ### Local helpers: band-limited finite sum + Galerkin viscous continuity -/

/-- For a band-limited field the `viscousFormSq` collapses to a finite `fourierBox` sum.
Avoids the private `stokes_boxSum` from `TorusTraceEnergy`. -/
private lemma viscousFormSq_bandlim (ν : ℝ) (n : ℕ) (u : L2VF)
    (hu : velocityProjection_n n u = u) :
    viscousFormSq ν u = ν * ∑ j : Fin 3, ∑ k ∈ fourierBox n,
        (2 * Real.pi) ^ 2 * (∑ i : Fin 3, (k i : ℝ) ^ 2) *
          ‖mFourierCoeff3 (L2VF_projComponentC j u) k‖ ^ 2 := by
  unfold viscousFormSq
  congr 1
  apply Finset.sum_congr rfl; intro j _
  apply tsum_eq_sum; intro k hk
  simp [coeff_zero_outside_box n u hu j k hk]

/-- Local re-proof of the private `galerkin_viscous_continuousOn` from `TorusTraceEnergy`,
using `viscousFormSq_bandlim` in place of the private `stokes_boxSum`. -/
private lemma galerkin_visc_cont (F : Torus3NSForms) (ν : ℝ) (u₀ : L2Sigma) (n : ℕ)
    (gs : GalerkinSolutionData F ν u₀ n) :
    ContinuousOn (fun s => viscousFormSq ν (gs.u s : L2VF)) (Set.Ici 0) := by
  have hcurve : ContinuousOn (fun s => (gs.u s : L2VF)) (Set.Ici 0) :=
    fun s hs => ((gs.u_hasDeriv s hs).continuousAt).continuousWithinAt
  simp_rw [fun s => viscousFormSq_bandlim ν n (gs.u s : L2VF) (gs.u_inVn s).symm]
  apply ContinuousOn.const_mul
  apply continuousOn_finsetSum Finset.univ; intro j _
  apply continuousOn_finsetSum (fourierBox n); intro k _
  apply ContinuousOn.const_mul
  apply ContinuousOn.pow; apply ContinuousOn.norm
  have heq : ∀ s, mFourierCoeff3 (L2VF_projComponentC j (gs.u s : L2VF)) k =
      fourierCoeffCLM k (L2VF_projComponentC j (gs.u s : L2VF)) :=
    fun s => (fourierCoeffCLM_apply k _).symm
  simp_rw [heq]
  exact ((fourierCoeffCLM k).continuous.comp
    (L2VF_projComponentC j).continuous).comp_continuousOn hcurve

/-! ### Local helper: `viscousFormSq` = `.toReal ∘ viscousEnn` when the ENNReal sum is finite -/

/-- When `viscousEnn ν u < ⊤`, the real dissipation form equals the `.toReal` of the
ENNReal version.  Used to transport AEMeasurability from `viscousEnn` to `viscousFormSq`. -/
private lemma viscousFormSq_eq_viscousEnn_toReal (ν : ℝ) (hν : 0 ≤ ν) (u : L2VF)
    (h : viscousEnn ν u < ⊤) : viscousFormSq ν u = (viscousEnn ν u).toReal := by
  -- Name the common per-mode real term for brevity
  set g : Fin 3 × (Fin 3 → ℤ) → ℝ := fun p =>
    ν * ((2 * Real.pi) ^ 2 * (∑ i : Fin 3, (p.2 i : ℝ) ^ 2) *
      ‖mFourierCoeff3 (L2VF_projComponentC p.1 u) p.2‖ ^ 2) with hgdef
  have hg0 : ∀ p, 0 ≤ g p := fun p => by simp only [hgdef]; positivity
  -- 1. Real series summable: lift from ENNReal finiteness
  have hgsumm : Summable g := by
    -- viscousEnn ν u = ∑' p, ENNReal.ofReal (g p) by definition of g and viscousEnn
    have hve_eq : viscousEnn ν u = ∑' p : Fin 3 × (Fin 3 → ℤ), ENNReal.ofReal (g p) := rfl
    exact (ENNReal.summable_toReal (hve_eq ▸ h.ne)).congr
      (fun p => ENNReal.toReal_ofReal (hg0 p))
  -- 2. (viscousEnn ν u).toReal = ∑' p, g p
  have hVEtoReal : (viscousEnn ν u).toReal = ∑' p, g p := by
    have hve_eq : viscousEnn ν u = ∑' p : Fin 3 × (Fin 3 → ℤ), ENNReal.ofReal (g p) := rfl
    rw [hve_eq, ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
    exact tsum_congr (fun p => ENNReal.toReal_ofReal (hg0 p))
  -- 3. ∑' p, g p = viscousFormSq ν u by rearranging the product tsum
  have hprod : ∑' p : Fin 3 × (Fin 3 → ℤ), g p = viscousFormSq ν u := by
    have hrow : ∀ j : Fin 3, Summable (fun k : Fin 3 → ℤ => g (j, k)) :=
      ((summable_prod_of_nonneg hg0).mp hgsumm).1
    rw [hgsumm.tsum_prod' hrow, tsum_fintype]
    -- g (j, k) = ν * ((2π)^2 * ∑i(ki)^2 * ‖coeff j k u‖^2) by definition
    simp_rw [show ∀ j k, g (j, k) = ν * ((2 * Real.pi) ^ 2 * (∑ i : Fin 3, (k i : ℝ) ^ 2) *
        ‖mFourierCoeff3 (L2VF_projComponentC j u) k‖ ^ 2) from fun _ _ => rfl,
      tsum_mul_left, ← Finset.mul_sum]
    rfl
  exact (hVEtoReal.trans hprod).symm

/-! ### Local helper: `memH1VF` from `viscousEnn` finiteness -/

/-- If `viscousEnn ν u < ⊤` (and `ν > 0`), then `u ∈ H¹` component-wise. -/
private lemma memH1VF_of_viscousEnn_lt_top (ν : ℝ) (hν : 0 < ν) (u : L2VF)
    (h : viscousEnn ν u < ⊤) : memH1VF u := by
  -- The per-mode contribution to viscousEnn
  set G : Fin 3 → (Fin 3 → ℤ) → ℝ := fun j k =>
    (2 * Real.pi) ^ 2 * (∑ i : Fin 3, (k i : ℝ) ^ 2) *
      ‖mFourierCoeff3 (L2VF_projComponentC j u) k‖ ^ 2 with hGdef
  have hG0 : ∀ j k, 0 ≤ G j k := fun j k => by positivity
  -- Rewrite viscousEnn in terms of G
  have hVEeq : viscousEnn ν u = ∑ j : Fin 3, ∑' k, ENNReal.ofReal (ν * G j k) := by
    unfold viscousEnn
    rw [ENNReal.tsum_prod', tsum_fintype]
  rw [hVEeq] at h
  -- Each per-j ENNReal sum is finite
  have hfin_j : ∀ j : Fin 3, ∑' k : Fin 3 → ℤ, ENNReal.ofReal (ν * G j k) < ⊤ := by
    intro j
    exact (Finset.single_le_sum (fun i _ => bot_le) (Finset.mem_univ j)).trans_lt h
  -- Factor out ν: ∑' k, ofReal (ν * G j k) = ofReal ν * ∑' k, ofReal (G j k)
  have hfactor : ∀ j : Fin 3, ∑' k : Fin 3 → ℤ, ENNReal.ofReal (ν * G j k) =
      ENNReal.ofReal ν * ∑' k, ENNReal.ofReal (G j k) := by
    intro j
    simp_rw [ENNReal.ofReal_mul hν.le]
    exact ENNReal.tsum_mul_left
  -- Each ∑' k, ofReal (G j k) is finite
  have hGfin_j : ∀ j : Fin 3, ∑' k : Fin 3 → ℤ, ENNReal.ofReal (G j k) < ⊤ := by
    intro j
    have hlt : ENNReal.ofReal ν * ∑' k : Fin 3 → ℤ, ENNReal.ofReal (G j k) < ⊤ := by
      rw [← hfactor j]; exact hfin_j j
    exact ENNReal.lt_top_of_mul_ne_top_right hlt.ne (ENNReal.ofReal_pos.mpr hν).ne'
  -- Hence G j is summable in ℝ
  have hGsumm_j : ∀ j : Fin 3, Summable (G j) := by
    intro j
    have := ENNReal.summable_toReal (hGfin_j j).ne
    refine this.congr (fun k => ?_)
    exact ENNReal.toReal_ofReal (hG0 j k)
  -- Now conclude memH1VF
  intro j
  unfold memH1Torus
  have hS1 : Summable (fun k : Fin 3 → ℤ =>
      ‖mFourierCoeff3 (L2VF_projComponentC j u) k‖ ^ 2) :=
    summable_norm_mFourierCoeff3_sq (L2VF_projComponentC j u)
  -- G j k = (2π)^2 * |k|^2 * ‖...‖^2, so from hGsumm_j: |k|^2 * ‖...‖^2 is summable
  have hS2 : Summable (fun k : Fin 3 → ℤ =>
      (∑ i : Fin 3, (k i : ℝ) ^ 2) * ‖mFourierCoeff3 (L2VF_projComponentC j u) k‖ ^ 2) := by
    have hpos : (0 : ℝ) < (2 * Real.pi) ^ 2 := by positivity
    have heqG : ∀ k, (2 * Real.pi) ^ 2 *
        ((∑ i : Fin 3, (k i : ℝ) ^ 2) * ‖mFourierCoeff3 (L2VF_projComponentC j u) k‖ ^ 2) =
        G j k := by intro k; simp [hGdef]; ring
    have hsG := (hGsumm_j j).congr fun k => (heqG k).symm
    exact (summable_mul_left_iff hpos.ne').mp hsG
  refine (hS1.add hS2).congr (fun k => ?_)
  ring

/-! ### Main theorem -/

/-- **Torus energy-class conjunct (4)** for the Aubin–Lions limit `alPkg.u`.

Given the full Galerkin-solution sequence and Aubin–Lions compactness package on 𝕋³,
the raw limit `alPkg.u` satisfies, for a.e. `t ∈ [0, T]`, `memH1VF (alPkg.u t : L2VF)`,
and the dissipation `viscousFormSq ν (alPkg.u s : L2VF)` is integrable on `[0, T]`.

This is the hypothesis `h4` of `torus_galerkin_limit_passage_of_energyClass`, which
plugging in here closes the `galerkin_limit_passage` removal. -/
theorem torus_energyClass_of_aubinLions (F : Torus3NSForms) (ν : ℝ) (hν : 0 < ν)
    (T : ℝ) (hT : 0 < T) (u₀ : L2Sigma)
    (galSeq : ∀ n, GalerkinSolutionData F ν u₀ n)
    (alPkg : AubinLionsPackage F ν T u₀ galSeq) :
    (∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc 0 T)),
        memH1VF (alPkg.u t : L2VF)) ∧
    IntervalIntegrable (fun s => viscousFormSq ν (alPkg.u s : L2VF))
      MeasureTheory.volume 0 T := by
  set μ : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) T) with hμ
  set φ := alPkg.φ
  -- ══════════════════════════════════════════════════════════════
  -- Step 1: extract a.e.-strong subsequence ρ from alPkg
  -- ══════════════════════════════════════════════════════════════
  -- AE strong measurability of each approximant curve
  have hfm : ∀ n, AEStronglyMeasurable (fun t => ((galSeq (φ n)).u t : L2VF)) μ := by
    intro n
    have hcont : ContinuousOn (fun t => ((galSeq (φ n)).u t : L2VF)) (Set.Icc 0 T) :=
      fun t ht => ((galSeq (φ n)).u_hasDeriv t ht.1).continuousAt.continuousWithinAt
    exact hcont.aestronglyMeasurable measurableSet_Icc
  -- Tendsto in measure from eLpNorm convergence
  have hmeas : TendstoInMeasure μ (fun n t => ((galSeq (φ n)).u t : L2VF)) atTop
      (fun t => (alPkg.u t : L2VF)) :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ENNReal) ≠ 0)
      hfm alPkg.u_aestronglyMeasurable alPkg.strong_convergence
  -- Extract a.e.-strong subsequence
  obtain ⟨ρ, hρ_mono, hρ_ae⟩ := hmeas.exists_seq_tendsto_ae
  -- ══════════════════════════════════════════════════════════════
  -- Step 2: AEMeasurability of viscousEnn ν ∘ alPkg.u on Ioc 0 T
  -- (proved via ENNReal.tsum on time domain — avoids MeasurableSpace L2VF)
  -- ══════════════════════════════════════════════════════════════
  -- AEStronglyMeasurable of alPkg.u on Ioc 0 T
  have haesm0 : AEStronglyMeasurable (fun t => (alPkg.u t : L2VF))
      (volume.restrict (Set.Ioc 0 T)) :=
    alPkg.u_aestronglyMeasurable.mono_set Set.Ioc_subset_Icc_self
  -- For each Fourier mode p = (j, k), the per-mode ENNReal term is AEMeasurable on time
  have hVEum : AEMeasurable (fun t => viscousEnn ν (alPkg.u t : L2VF))
      (volume.restrict (Set.Ioc 0 T)) := by
    -- Each summand (fun t => ENNReal.ofReal (ν * (2π)^2 * |k|^2 * ‖coeff p.1 p.2 (alPkg.u t)‖^2))
    -- is AEMeasurable via CLM composition.
    have hFpaem : ∀ p : Fin 3 × (Fin 3 → ℤ), AEMeasurable
        (fun t => ENNReal.ofReal (ν * ((2 * Real.pi) ^ 2 *
          (∑ i : Fin 3, (p.2 i : ℝ) ^ 2) *
          ‖mFourierCoeff3 (L2VF_projComponentC p.1 (alPkg.u t : L2VF)) p.2‖ ^ 2)))
        (volume.restrict (Set.Ioc 0 T)) := by
      intro ⟨j, k⟩
      apply ENNReal.measurable_ofReal.comp_aemeasurable
      apply AEMeasurable.const_mul
      apply AEMeasurable.const_mul
      apply AEMeasurable.pow_const
      apply AEStronglyMeasurable.aemeasurable
      apply AEStronglyMeasurable.norm
      exact (((fourierCoeffCLM k).continuous.comp
        (L2VF_projComponentC j).continuous).comp_aestronglyMeasurable haesm0).congr
        (Filter.Eventually.of_forall
          (fun t => fourierCoeffCLM_apply k (L2VF_projComponentC j (alPkg.u t : L2VF))))
    -- viscousEnn ν u = ∑' p, (per-mode ENNReal term)(u), so AEMeasurable.ennreal_tsum applies
    have hVEeq : ∀ t, viscousEnn ν (alPkg.u t : L2VF) =
        ∑' p : Fin 3 × (Fin 3 → ℤ), ENNReal.ofReal (ν * ((2 * Real.pi) ^ 2 *
          (∑ i : Fin 3, (p.2 i : ℝ) ^ 2) *
          ‖mFourierCoeff3 (L2VF_projComponentC p.1 (alPkg.u t : L2VF)) p.2‖ ^ 2)) :=
      fun t => rfl
    simp_rw [hVEeq]
    exact AEMeasurable.ennreal_tsum hFpaem
  -- ══════════════════════════════════════════════════════════════
  -- Step 3: Fatou – bound lintegral of viscousEnn on limit
  -- ══════════════════════════════════════════════════════════════
  -- Restrict a.e.-strong convergence to Ioc 0 T
  have hρ_ae_Ioc : ∀ᵐ t ∂(volume.restrict (Set.Ioc 0 T)),
      Tendsto (fun k => ((galSeq (φ (ρ k))).u t : L2VF)) atTop
        (𝓝 (alPkg.u t : L2VF)) :=
    ae_restrict_of_ae_restrict_of_subset Set.Ioc_subset_Icc_self hρ_ae
  -- A.e. lsc: viscousEnn ν (u t) ≤ liminf (viscousEnn ν (galSeq k .u t))
  have hae_lsc : ∀ᵐ t ∂(volume.restrict (Set.Ioc 0 T)),
      viscousEnn ν (alPkg.u t : L2VF) ≤
        Filter.liminf (fun k => viscousEnn ν ((galSeq (φ (ρ k))).u t : L2VF)) atTop := by
    filter_upwards [hρ_ae_Ioc] with t hconv
    exact viscousEnn_lsc ν (alPkg.u t : L2VF) _ hconv
  -- AEMeasurability of each approximant viscousEnn (via continuity)
  have hmeas_k : ∀ k, AEMeasurable
      (fun t => viscousEnn ν ((galSeq (φ (ρ k))).u t : L2VF))
      (volume.restrict (Set.Ioc 0 T)) := by
    intro k
    set n := φ (ρ k)
    -- viscousEnn ν ((galSeq n).u t) = ofReal (viscousFormSq) for all t
    have hVE : ∀ t, viscousEnn ν ((galSeq n).u t : L2VF) =
        ENNReal.ofReal (viscousFormSq ν ((galSeq n).u t : L2VF)) :=
      fun t => viscousEnn_eq_ofReal_of_bandlimited ν hν.le n _ ((galSeq n).u_inVn t).symm
    -- viscousFormSq ν ((galSeq n).u ·) is continuous on Ioc 0 T
    have hcont : ContinuousOn (fun s => viscousFormSq ν ((galSeq n).u s : L2VF)) (Set.Ioc 0 T) :=
      (galerkin_visc_cont F ν u₀ n (galSeq n)).mono (fun s hs => hs.1.le)
    exact (ENNReal.measurable_ofReal.comp_aemeasurable
      (hcont.aemeasurable measurableSet_Ioc)).congr
        (Filter.Eventually.of_forall (fun t => (hVE t).symm))
  -- Energy bound on each approximant: ∫⁻ in Ioc, viscousEnn ≤ ofReal (½ ‖u₀‖²)
  have hbound : ∀ k, ∫⁻ t in Set.Ioc 0 T, viscousEnn ν ((galSeq (φ (ρ k))).u t : L2VF) ≤
      ENNReal.ofReal ((1 / 2 : ℝ) * ‖(u₀ : L2VF)‖ ^ 2) := by
    intro k
    set n := φ (ρ k)
    have hVE : ∀ t, viscousEnn ν ((galSeq n).u t : L2VF) =
        ENNReal.ofReal (viscousFormSq ν ((galSeq n).u t : L2VF)) :=
      fun t => viscousEnn_eq_ofReal_of_bandlimited ν hν.le n _ ((galSeq n).u_inVn t).symm
    rw [lintegral_congr hVE]
    -- Continuity and integrability of viscousFormSq along (galSeq n).u
    have hcont : ContinuousOn (fun s => viscousFormSq ν ((galSeq n).u s : L2VF)) (Set.Icc 0 T) :=
      (galerkin_visc_cont F ν u₀ n (galSeq n)).mono (fun s hs => hs.1)
    have hintgbl : IntegrableOn (fun s => viscousFormSq ν ((galSeq n).u s : L2VF))
        (Set.Ioc 0 T) volume :=
      (hcont.intervalIntegrable_of_Icc hT.le).1
    have hnn : ∀ᵐ s ∂(volume.restrict (Set.Ioc 0 T)),
        0 ≤ viscousFormSq ν ((galSeq n).u s : L2VF) :=
      Filter.Eventually.of_forall fun s => viscousFormSq_nonneg hν.le _
    -- ofReal (∫ s in Ioc, viscousFormSq) = ∫⁻ s in Ioc, ofReal (viscousFormSq)
    rw [← ofReal_integral_eq_lintegral_ofReal hintgbl hnn]
    -- ∫ s in 0..T, viscousFormSq = ∫ s in Ioc 0 T, viscousFormSq
    rw [← intervalIntegral.integral_of_le hT.le]
    -- Energy bound from torus_galerkin_energy_le
    apply ENNReal.ofReal_le_ofReal
    linarith [torus_galerkin_energy_le F ν u₀ n (galSeq n) T hT.le,
              sq_nonneg ‖((galSeq n).u T : L2VF)‖]
  -- Fatou: ∫⁻ t, viscousEnn ν (alPkg.u t) ≤ liminf ... ≤ ofReal (½ ‖u₀‖²)
  have hFatou : ∫⁻ t in Set.Ioc 0 T, viscousEnn ν (alPkg.u t : L2VF) ≤
      ENNReal.ofReal ((1 / 2 : ℝ) * ‖(u₀ : L2VF)‖ ^ 2) := by
    calc ∫⁻ t in Set.Ioc 0 T, viscousEnn ν (alPkg.u t : L2VF)
        ≤ ∫⁻ t in Set.Ioc 0 T,
            Filter.liminf (fun k => viscousEnn ν ((galSeq (φ (ρ k))).u t : L2VF)) atTop :=
          lintegral_mono_ae hae_lsc
      _ ≤ Filter.liminf (fun k => ∫⁻ t in Set.Ioc 0 T,
              viscousEnn ν ((galSeq (φ (ρ k))).u t : L2VF)) atTop :=
          lintegral_liminf_le' hmeas_k
      _ ≤ ENNReal.ofReal ((1 / 2 : ℝ) * ‖(u₀ : L2VF)‖ ^ 2) :=
          (Filter.liminf_le_liminf (Filter.Eventually.of_forall hbound)).trans_eq
            (Filter.liminf_const _)
  -- ══════════════════════════════════════════════════════════════
  -- Step 4: a.e. finite viscousEnn on [0, T] (from Fatou)
  -- ══════════════════════════════════════════════════════════════
  have hfin_bound : ∫⁻ t in Set.Ioc 0 T, viscousEnn ν (alPkg.u t : L2VF) ≠ ⊤ :=
    (hFatou.trans_lt (ENNReal.ofReal_lt_top)).ne
  have hlt_top_Ioc : ∀ᵐ t ∂(volume.restrict (Set.Ioc 0 T)),
      viscousEnn ν (alPkg.u t : L2VF) < ⊤ :=
    ae_lt_top' hVEum hfin_bound
  -- Upgrade from Ioc to Icc (they agree a.e. since {0} is a null set)
  have hlt_top : ∀ᵐ t ∂(volume.restrict (Set.Icc 0 T)),
      viscousEnn ν (alPkg.u t : L2VF) < ⊤ := by
    rwa [← restrict_Ioc_eq_restrict_Icc]
  -- ══════════════════════════════════════════════════════════════
  -- Step 5: part (a) — a.e. memH1VF
  -- ══════════════════════════════════════════════════════════════
  have hpart_a : ∀ᵐ t ∂(volume.restrict (Set.Icc 0 T)), memH1VF (alPkg.u t : L2VF) := by
    filter_upwards [hlt_top] with t ht
    exact memH1VF_of_viscousEnn_lt_top ν hν (alPkg.u t : L2VF) ht
  -- ══════════════════════════════════════════════════════════════
  -- Step 6: part (b) — IntervalIntegrable
  -- ══════════════════════════════════════════════════════════════
  have hpart_b : IntervalIntegrable (fun s => viscousFormSq ν (alPkg.u s : L2VF))
      MeasureTheory.volume 0 T := by
    constructor
    · -- IntegrableOn on Ioc 0 T
      constructor
      · -- AEStronglyMeasurable on Ioc 0 T
        -- viscousFormSq ν (alPkg.u t) = (viscousEnn ν (alPkg.u t)).toReal a.e. (on hlt_top_Ioc)
        -- → AEMeasurable via hVEum.ennreal_toReal.congr
        have hFSQaem : AEMeasurable (fun t => viscousFormSq ν (alPkg.u t : L2VF))
            (volume.restrict (Set.Ioc 0 T)) :=
          hVEum.ennreal_toReal.congr
            (hlt_top_Ioc.mono (fun t ht =>
              (viscousFormSq_eq_viscousEnn_toReal ν hν.le (alPkg.u t : L2VF) ht).symm))
        exact hFSQaem.aestronglyMeasurable
      · -- HasFiniteIntegral on Ioc 0 T
        -- ‖viscousFormSq ν (alPkg.u t)‖₊ = ENNReal.ofReal (viscousFormSq ν ...)
        -- ≤ viscousEnn ν (alPkg.u t), and ∫⁻ viscousEnn < ⊤
        refine lt_of_le_of_lt (lintegral_mono_ae ?_) (hFatou.trans_lt ENNReal.ofReal_lt_top)
        filter_upwards with t
        calc ‖viscousFormSq ν (alPkg.u t : L2VF)‖ₑ
            = ENNReal.ofReal (viscousFormSq ν (alPkg.u t : L2VF)) :=
              Real.enorm_eq_ofReal (viscousFormSq_nonneg hν.le _)
          _ ≤ viscousEnn ν (alPkg.u t : L2VF) := ofReal_viscousFormSq_le ν hν.le _
    · -- IntegrableOn on Ioc T 0 = ∅ (since T > 0)
      rw [Set.Ioc_eq_empty (not_lt.mpr hT.le)]
      exact integrableOn_empty
  exact ⟨hpart_a, hpart_b⟩

end LerayHopf
