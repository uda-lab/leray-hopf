/-
# LerayHopf.TorusLimitPassage — conjunct 2: WeakFormNS limit passage on 𝕋³

**Milestone:** Torus issue #25, conjunct 2 (P1–P4).

This file proves `torus_weakFormNS_of_strongConvergence` (Torus conjunct 2), which
converts the strong L²(0,T;L²_σ) convergence from Aubin–Lions into a WeakFormNS
identity for the limit curve.  The key simplification on 𝕋³ (vs ℝ³) is that every
WeakFormNS test `w` is **already band-limited** (`IsGalerkinTest w = ∃ n₀, Pₙ₀ w = w`),
so the Galerkin ODE fires on `w` directly for all `n ≥ n₀` — no density step needed.

## Proof sketch (Temam III.3 for 𝕋³)

Fix an admissible pair `(ψ, w)`.

1. **`galerkin_ode_fires_on_test`** (sorry-free): `∃ n₀, ∀ n ≥ n₀, ∀ t ≥ 0`,
   `⟪u_n'(t), w⟫ + ν·stokesTestPairing(u_n(t), w) + F.b(u_n(t), u_n(t), w) = 0`.
   Proof: `IsGalerkinTest w` gives the projection level; `velocityProjection_n_eq_of_le`
   promotes it to all higher levels.

2. **IBP identity for u_n**: Multiplying the ODE by `ψ(t)` and integrating, then
   integrating by parts the time-derivative term (boundary-free since
   `tsupport ψ ⊆ Ioo 0 T` implies `ψ(0) = ψ(T) = 0`), gives the WeakFormNS identity
   for each Galerkin approximant.

3. **Limit passage** (ALLOW_SORRY: measurability of `alPkg.u` missing): the strong
   convergence `∫₀ᵀ ‖u_φ(n)(t) − u(t)‖² → 0` kills the error in each term.
   The blocker is that `AubinLionsPackage` lacks `u_aestronglyMeasurable` (present in
   `AubinLionsPackage_R3`), which is needed for the b-form dominator.

## Axioms

No new axioms.
-/

import LerayHopf.AxiomaticClosure
import LerayHopf.TorusConvectionExtension
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.InnerProductSpace.Calculus

namespace LerayHopf

open MeasureTheory Filter Topology intervalIntegral

/-! ### P1: galerkin_ode_fires_on_test (sorry-free) -/

/-- For a band-limited test `w` (IsGalerkinTest), the Galerkin ODE holds against `w`
for all Galerkin levels `n ≥ n₀` and all forward times `t ≥ 0`.

**Proof:** `IsGalerkinTest w` gives `n₀` with `Pₙ₀ w = w`.  By
`velocityProjection_n_eq_of_le`, `Pₙ w = w` for all `n ≥ n₀`.  The `u_ode` field of
`GalerkinSolutionData` then fires directly. -/
theorem galerkin_ode_fires_on_test (F : Torus3NSForms) (ν : ℝ) (u₀ : L2Sigma)
    (galSeq : ∀ n, GalerkinSolutionData F ν u₀ n) (w : L2Sigma) (hw : IsGalerkinTest w) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ t, 0 ≤ t →
      inner (𝕜 := ℝ) (deriv (fun s => ((galSeq n).u s : L2VF)) t) (w : L2VF)
        + ν * stokesTestPairing ((galSeq n).u t : L2VF) (w : L2VF)
        + F.b ((galSeq n).u t) ((galSeq n).u t) w = 0 := by
  obtain ⟨n₀, hn₀⟩ := hw
  refine ⟨n₀, fun n hn t ht => ?_⟩
  have hwn : velocityProjection_n n (w : L2VF) = (w : L2VF) :=
    TorusConvectionExtension.velocityProjection_n_eq_of_le hn (w : L2VF) hn₀
  exact (galSeq n).u_ode t ht w hwn.symm

/-! ### Boundary-condition helpers -/

/-- If `tsupport ψ ⊆ Ioo 0 T` then `ψ 0 = 0`. -/
private theorem psi_zero_of_tsupport_Ioo {ψ : ℝ → ℝ} {T : ℝ} (_hT : 0 < T)
    (hψsupp : tsupport ψ ⊆ Set.Ioo 0 T) : ψ 0 = 0 :=
  image_eq_zero_of_notMem_tsupport fun h => absurd (hψsupp h).1 (lt_irrefl 0)

/-- If `tsupport ψ ⊆ Ioo 0 T` then `ψ T = 0`. -/
private theorem psi_T_of_tsupport_Ioo {ψ : ℝ → ℝ} {T : ℝ} (_hT : 0 < T)
    (hψsupp : tsupport ψ ⊆ Set.Ioo 0 T) : ψ T = 0 :=
  image_eq_zero_of_notMem_tsupport fun h => absurd (hψsupp h).2 (lt_irrefl T)

/-! ### P3: IBP identity for the n-th Galerkin approximant -/

/-- For `n ≥ n₀`, the WeakFormNS integrand for `galSeq n` integrates to 0 on `[0, T]`.

**Proof:** ODE at each `t ≥ 0` (after projection promotion) × ψ, integrated.
IBP eliminates the time-derivative term using `ψ(0) = ψ(T) = 0`. -/
private theorem galerkin_weakFormNS_zero
    (F : Torus3NSForms) (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T) (u₀ : L2Sigma)
    (galSeq : ∀ n, GalerkinSolutionData F ν u₀ n)
    (ψ : ℝ → ℝ) (hψcs : HasCompactSupport ψ) (hψsupp : tsupport ψ ⊆ Set.Ioo 0 T)
    (hψC1 : ContDiff ℝ 1 ψ)
    (w : L2Sigma) (hw : IsGalerkinTest w)
    (n₀ : ℕ) (hn₀ : velocityProjection_n n₀ (w : L2VF) = (w : L2VF))
    (n : ℕ) (hn : n₀ ≤ n) :
    ∫ t in (0 : ℝ)..T,
      (-(inner (𝕜 := ℝ) ((galSeq n).u t : L2VF) (w : L2VF)) * deriv ψ t +
        ψ t * (ν * stokesTestPairing ((galSeq n).u t : L2VF) (w : L2VF) +
               F.b ((galSeq n).u t) ((galSeq n).u t) w)) = 0 := by
  set gs := galSeq n with hgs_def
  -- Promotion of projection level
  have hwn : velocityProjection_n n (w : L2VF) = (w : L2VF) :=
    TorusConvectionExtension.velocityProjection_n_eq_of_le hn (w : L2VF) hn₀
  -- ODE at each forward time
  have hode : ∀ t, 0 ≤ t →
      inner (𝕜 := ℝ) (deriv (fun s => (gs.u s : L2VF)) t) (w : L2VF) +
      ν * stokesTestPairing (gs.u t : L2VF) (w : L2VF) + F.b (gs.u t) (gs.u t) w = 0 :=
    fun t ht => gs.u_ode t ht w hwn.symm
  -- Boundary: ψ(0) = 0, ψ(T) = 0
  have hψ0 : ψ 0 = 0 := psi_zero_of_tsupport_Ioo hT hψsupp
  have hψT : ψ T = 0 := psi_T_of_tsupport_Ioo hT hψsupp
  -- ψ has HasDerivAt everywhere (C¹ → differentiable_one → HasDerivAt at the deriv value)
  have hψderiv : ∀ x, HasDerivAt ψ (deriv ψ x) x :=
    fun x => hψC1.differentiable_one.differentiableAt.hasDerivAt
  -- The inner product f(t) := ⟪gs.u t, w⟫ has HasDerivAt equal to ⟪deriv gs.u t, w⟫
  have hinner_deriv : ∀ t ∈ Set.uIcc (0 : ℝ) T,
      HasDerivAt (fun s => inner (𝕜 := ℝ) (gs.u s : L2VF) (w : L2VF))
        (inner (𝕜 := ℝ) (deriv (fun s => (gs.u s : L2VF)) t) (w : L2VF)) t := by
    simp only [Set.uIcc_of_le (le_of_lt hT), Set.mem_Icc]
    intro t ht
    have hda := (gs.u_hasDeriv t ht.1).inner (𝕜 := ℝ) (hasDerivAt_const t (w : L2VF))
    simp only [inner_zero_right, zero_add] at hda
    exact hda
  -- IntervalIntegrable of ψ' on [0, T] (C¹ ψ → deriv ψ continuous → integrable)
  have hψ'_intble : IntervalIntegrable (fun t => deriv ψ t) volume 0 T :=
    hψC1.continuous_deriv_one.intervalIntegrable 0 T
  -- Helper: continuity of the curve t ↦ (gs.u t : L2VF) from HasDerivAt
  have hcurve : ContinuousOn (fun t => (gs.u t : L2VF)) (Set.Icc 0 T) :=
    fun t ht => (gs.u_hasDeriv t ht.1).continuousAt.continuousWithinAt
  -- Helper: continuity of inner product t ↦ ⟪gs.u t, w⟫ via bounded linear functional
  -- (innerSL ℝ w maps u ↦ ⟪w, u⟫; use real_inner_comm to get ⟪u, w⟫)
  have hinner_cont : ContinuousOn
      (fun t => inner (𝕜 := ℝ) (gs.u t : L2VF) (w : L2VF)) (Set.Icc 0 T) :=
    ((innerSL ℝ (w : L2VF)).continuous.comp_continuousOn hcurve).congr
      (fun t _ => real_inner_comm _ _)
  -- Helper: stokesTestPairing at band-limited w reduces to a finite sum (fourierBox n₀)
  have hstokes_fin : ∀ v : L2VF, stokesTestPairing v (w : L2VF) =
      ∑ j : Fin 3, ∑ k ∈ fourierBox n₀,
        ((2 * Real.pi) ^ 2 * ∑ i : Fin 3, (k i : ℝ) ^ 2) *
        (mFourierCoeff3 (L2VF_projComponentC j v) k *
          starRingEnd ℂ (mFourierCoeff3 (L2VF_projComponentC j (w : L2VF)) k)).re := by
    intro v; unfold stokesTestPairing; congr 1; ext j
    apply tsum_eq_sum
    intro k hk
    simp [coeff_zero_outside_box n₀ (w : L2VF) hn₀ j k hk]
  -- Helper: continuity of stokesTestPairing(gs.u t, w) in t via CLM compositions
  have hstokes_cont : ContinuousOn
      (fun t => stokesTestPairing (gs.u t : L2VF) (w : L2VF)) (Set.Icc 0 T) := by
    simp_rw [hstokes_fin]
    apply continuousOn_finsetSum Finset.univ; intro j _
    apply continuousOn_finsetSum (fourierBox n₀); intro k _
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.comp Complex.continuous_re.continuousOn _ (Set.mapsTo_univ _ _)
    apply ContinuousOn.mul _ continuousOn_const
    have heq : (fun t => mFourierCoeff3 (L2VF_projComponentC j (gs.u t : L2VF)) k) =
        (fun t => fourierCoeffCLM k (L2VF_projComponentC j (gs.u t : L2VF))) := by
      ext t; simp only [fourierCoeffCLM_apply]
    rw [heq]
    exact ((fourierCoeffCLM k).continuous.comp
        (L2VF_projComponentC j).continuous).comp_continuousOn hcurve
  -- Helper: continuity of gs.u t as L2Sigma.
  -- The coercion L2Sigma → L2VF is an isometry (norms agree), hence inducing.
  have hcurve_sigma : ContinuousOn (fun t => gs.u t) (Set.Icc 0 T) := by
    have hiso : Isometry (fun x : L2Sigma => (x : L2VF)) := by
      rw [isometry_iff_dist_eq]
      intro x y
      simp only [dist_eq_norm, ← AddSubgroupClass.coe_sub, Submodule.coe_norm]
    exact hiso.isUniformInducing.isInducing.continuousOn_iff.mpr hcurve
  -- Helper: continuity of F.b(gs.u t, gs.u t, w) via bilinear CLM construction
  have hb_cont : ContinuousOn (fun t => F.b (gs.u t) (gs.u t) w) (Set.Icc 0 T) := by
    obtain ⟨Cb, hCb⟩ := F.b_bound w ⟨n₀, hn₀⟩
    let b_blin : L2Sigma →ₗ[ℝ] L2Sigma →ₗ[ℝ] ℝ :=
      LinearMap.mk₂ ℝ (fun u v => F.b u v w)
        (fun u u' v => F.b_add_1 u u' v w)
        (fun c u v => (F.b_smul_1 c u v w).trans (smul_eq_mul c _).symm)
        (fun u v v' => F.b_add_2 u v v' w)
        (fun c u v => (F.b_smul_2 c u v w).trans (smul_eq_mul c _).symm)
    have hb_norm : ∀ u v : L2Sigma, ‖b_blin u v‖ ≤ Cb * ‖u‖ * ‖v‖ := fun u v => by
      show ‖F.b u v w‖ ≤ Cb * ‖u‖ * ‖v‖
      simp only [Real.norm_eq_abs, Submodule.coe_norm]
      exact hCb u v
    let b_clm : L2Sigma →L[ℝ] L2Sigma →L[ℝ] ℝ := b_blin.mkContinuous₂ Cb hb_norm
    have hb_clm_eq : ∀ u v, b_clm u v = F.b u v w := fun u v => rfl
    have hpair_cont : ContinuousOn (fun t => (gs.u t, gs.u t)) (Set.Icc 0 T) :=
      hcurve_sigma.prodMk hcurve_sigma
    have h : ContinuousOn (fun t => b_clm (gs.u t) (gs.u t)) (Set.Icc 0 T) :=
      b_clm.continuous₂.comp_continuousOn hpair_cont
    exact h.congr (fun t _ => (hb_clm_eq (gs.u t) (gs.u t)).symm)
  -- Helper: inner(deriv gs.u t, w) is continuous on [0,T] (equals -(ν·stokes + b) by ODE)
  have h_A_cont : ContinuousOn
      (fun t => inner (𝕜 := ℝ) (deriv (fun s => (gs.u s : L2VF)) t) (w : L2VF))
      (Set.Icc 0 T) := by
    -- First build ContinuousOn for -(ν*stokes + F.b), typed explicitly so that congr fires
    have hcont : ContinuousOn
        (fun t : Time => -(ν * stokesTestPairing (gs.u t : L2VF) (w : L2VF) +
                           F.b (gs.u t) (gs.u t) w))
        (Set.Icc 0 T) := by
      apply ContinuousOn.neg
      exact (continuousOn_const.mul hstokes_cont).add hb_cont
    -- Pointwise equality -(ν*stokes + F.b) = inner(deriv u, w) from ODE
    exact hcont.congr (fun t ht => by
      have h := hode t ht.1
      linarith)
  -- IntervalIntegrable of ⟪deriv gs.u, w⟫ on [0,T]: follows from continuity above
  have hf'_intble : IntervalIntegrable
      (fun t => inner (𝕜 := ℝ) (deriv (fun s => (gs.u s : L2VF)) t) (w : L2VF))
      volume 0 T :=
    h_A_cont.intervalIntegrable_of_Icc (le_of_lt hT)
  -- IBP: ∫_0^T f(t)·ψ'(t) = f(T)·ψ(T) − f(0)·ψ(0) − ∫_0^T f'(t)·ψ(t)
  have hibp : ∫ t in (0 : ℝ)..T,
      inner (𝕜 := ℝ) (gs.u t : L2VF) (w : L2VF) * deriv ψ t =
      inner (𝕜 := ℝ) (gs.u T : L2VF) (w : L2VF) * ψ T -
      inner (𝕜 := ℝ) (gs.u 0 : L2VF) (w : L2VF) * ψ 0 -
      ∫ t in (0 : ℝ)..T,
        inner (𝕜 := ℝ) (deriv (fun s => (gs.u s : L2VF)) t) (w : L2VF) * ψ t :=
    integral_mul_deriv_eq_deriv_mul hinner_deriv (fun t _ => hψderiv t) hf'_intble hψ'_intble
  -- Boundary terms vanish: ψ(T) = 0 and ψ(0) = 0
  rw [hψT, mul_zero, hψ0, mul_zero, sub_zero, zero_sub] at hibp
  -- So: ∫_0^T inner u_n * ψ' = −∫_0^T inner (deriv u_n) * ψ
  -- Equivalently: ∫_0^T inner (deriv u_n) * ψ = −∫_0^T inner u_n * ψ'
  have hinner_eq : ∫ t in (0 : ℝ)..T,
      inner (𝕜 := ℝ) (deriv (fun s => (gs.u s : L2VF)) t) (w : L2VF) * ψ t =
      -(∫ t in (0 : ℝ)..T,
        inner (𝕜 := ℝ) (gs.u t : L2VF) (w : L2VF) * deriv ψ t) := by linarith [hibp]
  -- ODE integral: ∫_0^T ψ(t)·(ODE) dt = 0 since the ODE is 0 at each t ≥ 0
  have hode_int : ∫ t in (0 : ℝ)..T,
      ψ t * (inner (𝕜 := ℝ) (deriv (fun s => (gs.u s : L2VF)) t) (w : L2VF) +
             ν * stokesTestPairing (gs.u t : L2VF) (w : L2VF) +
             F.b (gs.u t) (gs.u t) w) = 0 := by
    have hzero : ∀ t ∈ Set.uIcc (0 : ℝ) T,
        ψ t * (inner (𝕜 := ℝ) (deriv (fun s => (gs.u s : L2VF)) t) (w : L2VF) +
               ν * stokesTestPairing (gs.u t : L2VF) (w : L2VF) +
               F.b (gs.u t) (gs.u t) w) = 0 := by
      simp only [Set.uIcc_of_le (le_of_lt hT), Set.mem_Icc]
      intro t ht
      rw [hode t ht.1, mul_zero]
    rw [intervalIntegral.integral_congr hzero]
    exact intervalIntegral.integral_zero
  -- Assemble: split hode_int and use IBP identity hinner_eq to get the WeakFormNS zero.
  -- Integrability of each component (continuous on [0,T] → integrable):
  have h_inner_ψ'_int : IntervalIntegrable
      (fun t => inner (𝕜 := ℝ) (gs.u t : L2VF) (w : L2VF) * deriv ψ t) volume 0 T :=
    (hinner_cont.mul hψC1.continuous_deriv_one.continuousOn).intervalIntegrable_of_Icc (le_of_lt hT)
  have h_ψ_BC_cont : ContinuousOn
      (fun t => ψ t * (ν * stokesTestPairing (gs.u t : L2VF) (w : L2VF) +
                       F.b (gs.u t) (gs.u t) w)) (Set.Icc 0 T) :=
    hψC1.continuous.continuousOn.mul ((continuousOn_const.mul hstokes_cont).add hb_cont)
  have h_ψ_BC_int : IntervalIntegrable
      (fun t => ψ t * (ν * stokesTestPairing (gs.u t : L2VF) (w : L2VF) +
                       F.b (gs.u t) (gs.u t) w)) volume 0 T :=
    h_ψ_BC_cont.intervalIntegrable_of_Icc (le_of_lt hT)
  have h_ψ_A_int : IntervalIntegrable
      (fun t => ψ t * inner (𝕜 := ℝ) (deriv (fun s => (gs.u s : L2VF)) t) (w : L2VF))
      volume 0 T :=
    (hψC1.continuous.continuousOn.mul h_A_cont).intervalIntegrable_of_Icc (le_of_lt hT)
  -- h_f: ∫ψ*inner' = -(∫ inner_u*ψ') by IBP identity hinner_eq
  have h_f : ∫ t in (0 : ℝ)..T,
      ψ t * inner (𝕜 := ℝ) (deriv (fun s => (gs.u s : L2VF)) t) (w : L2VF) =
      -(∫ t in (0 : ℝ)..T, inner (𝕜 := ℝ) (gs.u t : L2VF) (w : L2VF) * deriv ψ t) := by
    conv_lhs => arg 1; ext t; rw [mul_comm]
    exact hinner_eq
  -- Assembly: direct calc chain using integral linearity and IBP
  calc ∫ t in (0 : ℝ)..T,
          (-(inner (𝕜 := ℝ) (gs.u t : L2VF) (w : L2VF)) * deriv ψ t +
           ψ t * (ν * stokesTestPairing (gs.u t : L2VF) (w : L2VF) + F.b (gs.u t) (gs.u t) w))
      -- ring: -inner*ψ' = -(inner*ψ')
      = ∫ t in (0 : ℝ)..T,
            (-(inner (𝕜 := ℝ) (gs.u t : L2VF) (w : L2VF) * deriv ψ t) +
             ψ t * (ν * stokesTestPairing (gs.u t : L2VF) (w : L2VF) + F.b (gs.u t) (gs.u t) w)) :=
          intervalIntegral.integral_congr (fun t _ => by ring)
      -- split: ∫(A+B) = ∫A + ∫B
      _ = (∫ t in (0 : ℝ)..T,
              -(inner (𝕜 := ℝ) (gs.u t : L2VF) (w : L2VF) * deriv ψ t)) +
          ∫ t in (0 : ℝ)..T,
              ψ t * (ν * stokesTestPairing (gs.u t : L2VF) (w : L2VF) + F.b (gs.u t) (gs.u t) w) :=
          intervalIntegral.integral_add h_inner_ψ'_int.neg h_ψ_BC_int
      -- pull neg out: ∫-f = -(∫f)
      _ = -(∫ t in (0 : ℝ)..T,
              inner (𝕜 := ℝ) (gs.u t : L2VF) (w : L2VF) * deriv ψ t) +
          ∫ t in (0 : ℝ)..T,
              ψ t * (ν * stokesTestPairing (gs.u t : L2VF) (w : L2VF) + F.b (gs.u t) (gs.u t) w) := by
          rw [intervalIntegral.integral_neg]
      -- IBP: -(∫ inner*ψ') = ∫ ψ*inner'
      _ = (∫ t in (0 : ℝ)..T,
              ψ t * inner (𝕜 := ℝ) (deriv (fun s => (gs.u s : L2VF)) t) (w : L2VF)) +
          ∫ t in (0 : ℝ)..T,
              ψ t * (ν * stokesTestPairing (gs.u t : L2VF) (w : L2VF) + F.b (gs.u t) (gs.u t) w) := by
          rw [← h_f]
      -- combine: ∫A + ∫B = ∫(A+B)
      _ = ∫ t in (0 : ℝ)..T,
              (ψ t * inner (𝕜 := ℝ) (deriv (fun s => (gs.u s : L2VF)) t) (w : L2VF) +
               ψ t * (ν * stokesTestPairing (gs.u t : L2VF) (w : L2VF) + F.b (gs.u t) (gs.u t) w)) :=
          (intervalIntegral.integral_add h_ψ_A_int h_ψ_BC_int).symm
      -- ring: ψ*(A) + ψ*(B+C) = ψ*(A+B+C)
      _ = ∫ t in (0 : ℝ)..T,
              ψ t * (inner (𝕜 := ℝ) (deriv (fun s => (gs.u s : L2VF)) t) (w : L2VF) +
                     ν * stokesTestPairing (gs.u t : L2VF) (w : L2VF) + F.b (gs.u t) (gs.u t) w) :=
          intervalIntegral.integral_congr (fun t _ => by ring)
      -- ODE: integrand = 0 pointwise → integral = 0
      _ = 0 := hode_int

/-! ### P4: Main theorem — WeakFormNS limit passage -/

/-- **WeakFormNS limit passage on 𝕋³ (conjunct 2).**

The Aubin–Lions limit curve `alPkg.u` satisfies the distributional Navier–Stokes weak
equation `WeakFormNS ν T (torus3Evolution F) alPkg.u`.

**Density-free (key 𝕋³ advantage):** Every WeakFormNS test `w` satisfies
`IsGalerkinTest w = ∃ n₀, Pₙ₀ w = w`, so the Galerkin ODE fires directly for all
`n ≥ n₀` — no density / test-approximation step is needed.

**Remaining sorry (1 atom):** The limit passage for the b-form requires bounding
  `∫₀ᵀ |F.b(u t, u t, w) − F.b(u_n t, u_n t, w)| dt`
  `≤ C·(‖u t‖ + ‖u_n t‖)·‖u t − u_n t‖ dt`
  `≤ C·(‖u t − u_n t‖ + 2‖u₀‖)·‖u t − u_n t‖`.
Integrating: `C·∫₀ᵀ ‖diff‖² + 2‖u₀‖·C·∫₀ᵀ ‖diff‖ → 0` via Cauchy–Schwarz.
This needs `AEStronglyMeasurable (fun t => alPkg.u t : L2VF) (volume.restrict [0,T])`,
absent from `AubinLionsPackage` (unlike `AubinLionsPackage_R3.u_aestronglyMeasurable`).
**Fix:** Add `u_aestronglyMeasurable` field to `AubinLionsPackage` (lean-coder task). -/
theorem torus_weakFormNS_of_strongConvergence
    (F : Torus3NSForms) (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T) (u₀ : L2Sigma)
    (galSeq : ∀ n, GalerkinSolutionData F ν u₀ n)
    (alPkg : AubinLionsPackage F ν T u₀ galSeq) :
    WeakFormNS ν T (torus3Evolution F) alPkg.u := by
  intro ψ hψcs hψsupp hψC1 w hw
  -- (torus3Evolution F).H = L2Sigma definitionally (by field projection of torus3Evolution).
  -- Make the type of w explicit so downstream coercions to L2VF are found automatically.
  change L2Sigma at w
  obtain ⟨n₀, hn₀⟩ := hw
  -- For all N with alPkg.φ N ≥ n₀, galSeq (alPkg.φ N) satisfies the WeakFormNS = 0 identity
  have hgal_zero : ∀ N, n₀ ≤ alPkg.φ N →
      ∫ t in (0 : ℝ)..T,
        (-(inner (𝕜 := ℝ) ((galSeq (alPkg.φ N)).u t : L2VF) (w : L2VF)) * deriv ψ t +
          ψ t * (ν * stokesTestPairing ((galSeq (alPkg.φ N)).u t : L2VF) (w : L2VF) +
                 F.b ((galSeq (alPkg.φ N)).u t) ((galSeq (alPkg.φ N)).u t) w)) = 0 :=
    fun N hN => galerkin_weakFormNS_zero F ν hν T hT u₀ galSeq ψ hψcs hψsupp hψC1 w ⟨n₀, hn₀⟩ n₀ hn₀ (alPkg.φ N) hN
  -- The limit passage: send N → ∞ using strong_convergence.
  -- For the torus3Evolution: viscousForm = stokesTestPairing, convForm = F.b, isTest = IsGalerkinTest.
  -- The goal is: ∫_0^T (−⟪alPkg.u t, w⟫·ψ'(t) + ψ(t)·(ν·stokesTestPairing + F.b)) = 0.
  --
  -- Proof sketch of limit passage (blocked by missing u_aestronglyMeasurable):
  -- Let u_N := (galSeq (alPkg.φ N)).u. The WeakFormNS for u_N is 0 (hgal_zero).
  -- The difference WeakFormNS(u) − WeakFormNS(u_N) at each t is bounded by:
  --   |deriv ψ t| · ‖w‖ · ‖u t − u_N t‖          (inner product term)
  --   + |ψ t| · C_s · ‖u t − u_N t‖               (viscous term, b_bound for stokesTestPairing)
  --   + |ψ t| · C_b · (‖u t − u_N t‖² + 2‖u₀‖·‖u t − u_N t‖)   (nonlinear term)
  -- Integrating over [0, T] and using Cauchy–Schwarz:
  --   ∫₀ᵀ ‖u t − u_N t‖ dt ≤ √T · √(∫₀ᵀ ‖u t − u_N t‖²) → 0
  -- and ∫₀ᵀ ‖u t − u_N t‖² → 0 from strong_convergence. Both → 0 as N → ∞.
  -- This shows WeakFormNS(u) = lim WeakFormNS(u_N) = 0.
  -- Blocked: AubinLionsPackage.u lacks u_aestronglyMeasurable; without measurability of
  -- t ↦ u t, the integral ∫₀ᵀ ‖u t − u_N t‖ dt and ∫₀ᵀ ‖u t‖ · ‖diff‖ dt are
  -- not guaranteed to equal the Lebesgue integral (could be 0 by convention).
  -- Fix needed: add u_aestronglyMeasurable : AEStronglyMeasurable (fun t => alPkg.u t : L2VF)
  --   (volume.restrict (Set.Icc 0 T)) to AubinLionsPackage (lean-coder task).
  sorry -- ALLOW_SORRY: limit passage N→∞ for WeakFormNS on 𝕋³; structural reduction (IBP + ODE, hgal_zero) complete; real blocker = AubinLionsPackage.strong_convergence uses Bochner integral ∫‖d_N‖²→0 which equals 0 by convention when d_N ∉ L² (non-integrable), so cannot derive genuine L²-convergence (eLpNorm → 0) needed for Cauchy-Schwarz ∫‖d_N‖ ≤ √T·√(∫‖d_N‖²) and b-form domination; fix = add MemLp field or change strong_convergence to use eLpNorm in AubinLionsPackage (lean-coder task)

end LerayHopf
