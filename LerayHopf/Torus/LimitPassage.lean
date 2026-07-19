/-
# LerayHopf.Torus.LimitPassage — conjunct 2: WeakFormNS limit passage on 𝕋³

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

3. **Limit passage** (sorry-free): the eLpNorm strong convergence
   `alPkg.strong_convergence` kills the error in each term (linear/viscous via a
   Hölder bound on the finite measure `[0,T]`; convection via the bilinear split
   `b(u,u,w)−b(u_N,u_N,w) = b(u−u_N,u,w)+b(u_N,u−u_N,w)` and Cauchy–Schwarz),
   with `alPkg.u_aestronglyMeasurable` supplying measurability of the dominators.

## Axioms

No new axioms.
-/

import LerayHopf.Torus.SolutionInterfaces
import LerayHopf.Torus.ConvectionExtension
import LerayHopf.Torus.GalerkinODESolve
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.InnerProductSpace.Calculus

namespace LerayHopf

open MeasureTheory Filter Topology intervalIntegral
open scoped ENNReal

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

/-! ### Limit-passage helpers (bilinear split, viscous L²-bound, box-sum) -/

/-- Subtraction in the first slot of `F.b` (from additivity + `(-1)`-homogeneity). -/
private theorem Torus3NSForms.b_sub_1 (F : Torus3NSForms) (a b v z : L2Sigma) :
    F.b (a - b) v z = F.b a v z - F.b b v z := by
  rw [sub_eq_add_neg, F.b_add_1, show (-b : L2Sigma) = (-1 : ℝ) • b from
    (neg_one_smul ℝ b).symm, F.b_smul_1]; ring

/-- Subtraction in the second slot of `F.b`. -/
private theorem Torus3NSForms.b_sub_2 (F : Torus3NSForms) (u a b z : L2Sigma) :
    F.b u (a - b) z = F.b u a z - F.b u b z := by
  rw [sub_eq_add_neg, F.b_add_2, show (-b : L2Sigma) = (-1 : ℝ) • b from
    (neg_one_smul ℝ b).symm, F.b_smul_2]; ring

/-- `stokesTestPairing v w` as a finite `fourierBox n₀` sum, for band-limited `w`. -/
private theorem stokesTestPairing_eq_boxSum (n₀ : ℕ) (w : L2VF)
    (hn₀ : velocityProjection_n n₀ w = w) (v : L2VF) :
    stokesTestPairing v w =
      ∑ j : Fin 3, ∑ k ∈ fourierBox n₀,
        ((2 * Real.pi) ^ 2 * ∑ i : Fin 3, (k i : ℝ) ^ 2) *
          (mFourierCoeff3 (L2VF_projComponentC j v) k *
            starRingEnd ℂ (mFourierCoeff3 (L2VF_projComponentC j w) k)).re := by
  unfold stokesTestPairing; congr 1; ext j
  apply tsum_eq_sum
  intro k hk
  simp [coeff_zero_outside_box n₀ w hn₀ j k hk]

/-- **Viscous-form L²-bound at a band-limited test `w`:** `|stokesTestPairing v w| ≤ C · ‖v‖`.
The constant is a finite `fourierBox n₀` sum of Fourier-coefficient operator norms. -/
private theorem stokes_abs_le (n₀ : ℕ) (w : L2VF)
    (hn₀ : velocityProjection_n n₀ w = w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : L2VF, |stokesTestPairing v w| ≤ C * ‖v‖ := by
  classical
  refine ⟨∑ j : Fin 3, ∑ k ∈ fourierBox n₀,
      |(2 * Real.pi) ^ 2 * ∑ i : Fin 3, (k i : ℝ) ^ 2| *
        (‖fourierCoeffCLM k‖ * ‖L2VF_projComponentC j‖) *
        ‖mFourierCoeff3 (L2VF_projComponentC j w) k‖, ?_, ?_⟩
  · exact Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => by positivity
  · intro v
    rw [stokesTestPairing_eq_boxSum n₀ w hn₀ v]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun j _ => ?_
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun k _ => ?_
    set cjk : ℝ := (2 * Real.pi) ^ 2 * ∑ i : Fin 3, (k i : ℝ) ^ 2 with hcjk
    set cv : ℂ := mFourierCoeff3 (L2VF_projComponentC j v) k with hcv
    set cw : ℂ := mFourierCoeff3 (L2VF_projComponentC j w) k with hcw
    rw [abs_mul]
    have hre : |(cv * starRingEnd ℂ cw).re| ≤ ‖cv‖ * ‖cw‖ := by
      calc |(cv * starRingEnd ℂ cw).re| ≤ ‖cv * starRingEnd ℂ cw‖ := Complex.abs_re_le_norm _
        _ = ‖cv‖ * ‖cw‖ := by rw [norm_mul, RCLike.norm_conj]
    have hcvbd : ‖cv‖ ≤ ‖fourierCoeffCLM k‖ * ‖L2VF_projComponentC j‖ * ‖v‖ := by
      rw [hcv, ← fourierCoeffCLM_apply]
      calc ‖fourierCoeffCLM k (L2VF_projComponentC j v)‖
          ≤ ‖fourierCoeffCLM k‖ * ‖L2VF_projComponentC j v‖ := (fourierCoeffCLM k).le_opNorm _
        _ ≤ ‖fourierCoeffCLM k‖ * (‖L2VF_projComponentC j‖ * ‖v‖) := by
            gcongr; exact (L2VF_projComponentC j).le_opNorm _
        _ = ‖fourierCoeffCLM k‖ * ‖L2VF_projComponentC j‖ * ‖v‖ := by ring
    calc |cjk| * |(cv * starRingEnd ℂ cw).re|
        ≤ |cjk| * (‖cv‖ * ‖cw‖) := by gcongr
      _ ≤ |cjk| * ((‖fourierCoeffCLM k‖ * ‖L2VF_projComponentC j‖ * ‖v‖) * ‖cw‖) := by
          gcongr
      _ = |cjk| * (‖fourierCoeffCLM k‖ * ‖L2VF_projComponentC j‖) * ‖cw‖ * ‖v‖ := by ring

/-! ### P4: Main theorem — WeakFormNS limit passage -/

set_option maxHeartbeats 1000000 in
-- kept at the original 1000000 (issue #152): isolated `#count_heartbeats in` measurement
-- reported ~331 heartbeats, but sibling declarations elsewhere in this file family with
-- comparably low isolated measurements failed under the default budget in a real rebuild — no
-- reduction from the original value was attempted without a dedicated re-verification cycle.
/-- **WeakFormNS limit passage on 𝕋³ (conjunct 2).**

The Aubin–Lions limit curve `alPkg.u` satisfies the distributional Navier–Stokes weak
equation `WeakFormNS ν T (torus3Evolution F) alPkg.u`.

**Density-free (key 𝕋³ advantage):** Every WeakFormNS test `w` satisfies
`IsGalerkinTest w = ∃ n₀, Pₙ₀ w = w`, so the Galerkin ODE fires directly for all
`n ≥ n₀` — no density / test-approximation step is needed.

**Limit passage:** per-approximant WeakFormNS = 0 (IBP + ODE); the linear/viscous/
convection errors are killed by the eLpNorm strong convergence
`alPkg.strong_convergence` via Cauchy–Schwarz on `[0,T]`, using
`alPkg.u_aestronglyMeasurable` for the dominators. -/
theorem torus_weakFormNS_of_strongConvergence
    (F : Torus3NSForms) (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T) (u₀ : L2Sigma)
    (galSeq : ∀ n, GalerkinSolutionData F ν u₀ n)
    (alPkg : AubinLionsPackage F ν T u₀ galSeq) :
    WeakFormNS ν T (torus3Evolution F) alPkg.u := by
  intro ψ hψcs hψsupp hψC1 w hw
  -- (torus3Evolution F).H = L2Sigma definitionally (by field projection of torus3Evolution).
  change L2Sigma at w
  obtain ⟨n₀, hn₀⟩ := hw
  classical
  -- The band-limited-test WeakFormNS integrand, as a function of the curve `f`.
  set Gf : (ℝ → L2Sigma) → ℝ → ℝ := fun f t =>
    -(inner (𝕜 := ℝ) (f t : L2VF) (w : L2VF)) * deriv ψ t +
      ψ t * (ν * stokesTestPairing (f t : L2VF) (w : L2VF) + F.b (f t) (f t) w) with hGf
  -- Per-approximant WeakFormNS = 0 (IBP + ODE), for the band-limited test `w`.
  have hgal_zero : ∀ N, n₀ ≤ alPkg.φ N →
      ∫ t in (0 : ℝ)..T, Gf (fun s => (galSeq (alPkg.φ N)).u s) t = 0 :=
    fun N hN => galerkin_weakFormNS_zero F ν hν T hT u₀ galSeq ψ hψcs hψsupp hψC1 w
      ⟨n₀, hn₀⟩ n₀ hn₀ (alPkg.φ N) hN
  -- Finite Lebesgue measure on `[0,T]`.
  set μ : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) T) with hμdef
  haveI hμfin : IsFiniteMeasure μ := by
    rw [hμdef]
    exact ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc]; exact ENNReal.ofReal_lt_top⟩
  -- Bridge: interval integral over `[0,T]` equals the `μ`-integral.
  have hbridge : ∀ g : ℝ → ℝ, ∫ t in (0 : ℝ)..T, g t = ∫ t, g t ∂μ := by
    intro g
    rw [intervalIntegral.integral_of_le hT.le, hμdef, Measure.restrict_congr_set Ioc_ae_eq_Icc]
  -- Measurability of the limit curve (from the package field), as `L2VF` and as `L2Sigma`.
  have hu_aesm : AEStronglyMeasurable (fun t => (alPkg.u t : L2VF)) μ :=
    alPkg.u_aestronglyMeasurable
  have hsu_aesm : AEStronglyMeasurable (fun t => alPkg.u t) μ := by
    have hiso : Isometry (fun x : L2Sigma => (x : L2VF)) := by
      rw [isometry_iff_dist_eq]; intro x y
      simp only [dist_eq_norm, ← AddSubgroupClass.coe_sub, Submodule.coe_norm]
    exact hiso.isEmbedding.aestronglyMeasurable_comp_iff.1 hu_aesm
  -- Convection-form constant and the continuous bilinear representative `b_clm`.
  obtain ⟨Cbb, hCbb⟩ := F.b_bound w ⟨n₀, hn₀⟩
  set Cb' : ℝ := |Cbb| with hCb'def
  have hCb'0 : 0 ≤ Cb' := abs_nonneg _
  have hCb' : ∀ u v : L2Sigma, |F.b u v w| ≤ Cb' * ‖(u : L2VF)‖ * ‖(v : L2VF)‖ := by
    intro u v; refine (hCbb u v).trans ?_; gcongr; exact le_abs_self _
  set b_blin : L2Sigma →ₗ[ℝ] L2Sigma →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ (fun u v => F.b u v w) (fun u u' v => F.b_add_1 u u' v w)
      (fun c u v => (F.b_smul_1 c u v w).trans (smul_eq_mul c _).symm)
      (fun u v v' => F.b_add_2 u v v' w)
      (fun c u v => (F.b_smul_2 c u v w).trans (smul_eq_mul c _).symm) with hbblin
  have hbnorm : ∀ u v : L2Sigma, ‖b_blin u v‖ ≤ Cbb * ‖u‖ * ‖v‖ := fun u v => by
    show ‖F.b u v w‖ ≤ Cbb * ‖u‖ * ‖v‖
    simp only [Real.norm_eq_abs, Submodule.coe_norm]; exact hCbb u v
  set b_clm : L2Sigma →L[ℝ] L2Sigma →L[ℝ] ℝ := b_blin.mkContinuous₂ Cbb hbnorm with hbclm
  have hbclm_eq : ∀ u v : L2Sigma, b_clm u v = F.b u v w := fun u v => rfl
  -- Viscous-form L²-bound at `w`.
  obtain ⟨Cs, hCs0, hCs⟩ := stokes_abs_le n₀ (w : L2VF) hn₀
  -- Sup bounds for `ψ` and `ψ'` on `[0,T]`.
  obtain ⟨Mψ, hMψ⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    hψC1.continuous.continuousOn
  obtain ⟨Mψ', hMψ'⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    hψC1.continuous_deriv_one.continuousOn
  have hMψ0 : 0 ≤ Mψ := le_trans (norm_nonneg _) (hMψ 0 ⟨le_refl 0, hT.le⟩)
  have hMψ'0 : 0 ≤ Mψ' := le_trans (norm_nonneg _) (hMψ' 0 ⟨le_refl 0, hT.le⟩)
  -- Galerkin-curve continuity, uniform norm bound, measurability, `MemLp`.
  have hcont_uN : ∀ N, ContinuousOn (fun t => ((galSeq (alPkg.φ N)).u t : L2VF)) (Set.Icc 0 T) :=
    fun N t ht => ((galSeq (alPkg.φ N)).u_hasDeriv t ht.1).continuousAt.continuousWithinAt
  have hnorm_uN : ∀ N, ∀ t ∈ Set.Icc (0 : ℝ) T,
      ‖((galSeq (alPkg.φ N)).u t : L2VF)‖ ≤ ‖(u₀ : L2VF)‖ := by
    intro N t ht
    have hE := (galSeq (alPkg.φ N)).energy_bound t ht.1
    have hP := Torus.velocityProjection_n_norm_le (alPkg.φ N) (u₀ : L2VF)
    have h1 : ‖((galSeq (alPkg.φ N)).u t : L2VF)‖ ^ 2
        ≤ ‖velocityProjection_n (alPkg.φ N) (u₀ : L2VF)‖ ^ 2 := by linarith
    have h2 : ‖velocityProjection_n (alPkg.φ N) (u₀ : L2VF)‖ ^ 2 ≤ ‖(u₀ : L2VF)‖ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hP 2
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (by norm_num)).mp (h1.trans h2)
  have hAESM_uN : ∀ N, AEStronglyMeasurable (fun t => ((galSeq (alPkg.φ N)).u t : L2VF)) μ :=
    fun N => by rw [hμdef]; exact (hcont_uN N).aestronglyMeasurable measurableSet_Icc
  have hMemLp_uN : ∀ N, MemLp (fun t => ((galSeq (alPkg.φ N)).u t : L2VF)) 2 μ := fun N =>
    MemLp.of_bound (hAESM_uN N) ‖(u₀ : L2VF)‖ (by
      rw [hμdef]
      exact (ae_restrict_iff' measurableSet_Icc).mpr (ae_of_all _ fun t ht => hnorm_uN N t ht))
  -- The differences and their `eLpNorm` convergence (the eLpNorm strong-convergence field).
  set dN : ℕ → ℝ → L2VF := fun N t => ((galSeq (alPkg.φ N)).u t : L2VF) - (alPkg.u t : L2VF) with hdN
  have hdNval : ∀ N t, dN N t = ((galSeq (alPkg.φ N)).u t : L2VF) - (alPkg.u t : L2VF) := fun N t => rfl
  have hSC : Filter.Tendsto (fun N => eLpNorm (dN N) 2 μ) Filter.atTop (nhds 0) :=
    alPkg.strong_convergence
  set e : ℕ → ℝ := fun N => (eLpNorm (dN N) 2 μ).toReal with hedef
  have hE0 : Filter.Tendsto e Filter.atTop (nhds 0) := by
    have h := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).comp hSC
    simpa [hedef, Function.comp_def] using h
  have hAESM_dN : ∀ N, AEStronglyMeasurable (dN N) μ := fun N => (hAESM_uN N).sub hu_aesm
  have hev : ∀ᶠ N in Filter.atTop, eLpNorm (dN N) 2 μ < 1 :=
    hSC.eventually (Iio_mem_nhds (by norm_num))
  obtain ⟨N₀, hN₀lt⟩ := hev.exists
  have hMemLp_dN0 : MemLp (dN N₀) 2 μ := ⟨hAESM_dN N₀, lt_of_lt_of_le hN₀lt le_top⟩
  have hMemLp_uu : MemLp (fun t => (alPkg.u t : L2VF)) 2 μ := by
    have h : MemLp (fun t => ((galSeq (alPkg.φ N₀)).u t : L2VF) - dN N₀ t) 2 μ :=
      (hMemLp_uN N₀).sub hMemLp_dN0
    have hfun : (fun t => ((galSeq (alPkg.φ N₀)).u t : L2VF) - dN N₀ t)
        = fun t => (alPkg.u t : L2VF) := by funext t; rw [hdNval]; abel
    rwa [hfun] at h
  have hMemLp_dN : ∀ N, MemLp (dN N) 2 μ := fun N => (hMemLp_uN N).sub hMemLp_uu
  -- `‖f‖²` integrability from `MemLp _ 2`.
  have hsq_int : ∀ f : ℝ → L2VF, MemLp f 2 μ → Integrable (fun t => ‖f t‖ ^ 2) μ := by
    intro f hf
    have h := hf.integrable_norm_rpow (by norm_num) (by norm_num)
    refine h.congr (Filter.Eventually.of_forall fun t => ?_)
    have h2 : ((2 : ℝ≥0∞).toReal) = ((2 : ℕ) : ℝ) := by norm_num
    simp only [h2, Real.rpow_natCast]
  have hInt_uu_norm : Integrable (fun t => ‖(alPkg.u t : L2VF)‖) μ :=
    hMemLp_uu.norm.integrable one_le_two
  have hInt_uu_sq : Integrable (fun t => ‖(alPkg.u t : L2VF)‖ ^ 2) μ := hsq_int _ hMemLp_uu
  have hInt_dN_norm : ∀ N, Integrable (fun t => ‖dN N t‖) μ := fun N =>
    (hMemLp_dN N).norm.integrable one_le_two
  have hInt_dN_uu : ∀ N, Integrable (fun t => ‖dN N t‖ * ‖(alPkg.u t : L2VF)‖) μ := by
    intro N
    have hg : Integrable (fun t => ‖dN N t‖ ^ 2 + ‖(alPkg.u t : L2VF)‖ ^ 2) μ :=
      (hsq_int _ (hMemLp_dN N)).add hInt_uu_sq
    refine Integrable.mono' hg
      ((hMemLp_dN N).aestronglyMeasurable.norm.mul hMemLp_uu.aestronglyMeasurable.norm) ?_
    refine Filter.Eventually.of_forall fun t => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith [sq_nonneg (‖dN N t‖ - ‖(alPkg.u t : L2VF)‖), norm_nonneg (dN N t),
      norm_nonneg (alPkg.u t : L2VF)]
  -- Measurability of the viscous and convection terms for the limit curve.
  have hAESM_stokes : AEStronglyMeasurable
      (fun t => stokesTestPairing (alPkg.u t : L2VF) (w : L2VF)) μ := by
    have hfin : (fun t => stokesTestPairing (alPkg.u t : L2VF) (w : L2VF))
        = fun t => ∑ j : Fin 3, ∑ k ∈ fourierBox n₀,
            ((2 * Real.pi) ^ 2 * ∑ i : Fin 3, (k i : ℝ) ^ 2) *
            (mFourierCoeff3 (L2VF_projComponentC j (alPkg.u t : L2VF)) k *
              starRingEnd ℂ (mFourierCoeff3 (L2VF_projComponentC j (w : L2VF)) k)).re := by
      funext t; exact stokesTestPairing_eq_boxSum n₀ (w : L2VF) hn₀ _
    rw [hfin]
    refine Finset.aestronglyMeasurable_fun_sum _ fun j _ =>
      Finset.aestronglyMeasurable_fun_sum _ fun k _ => ?_
    have h1 : AEStronglyMeasurable
        (fun t => mFourierCoeff3 (L2VF_projComponentC j (alPkg.u t : L2VF)) k) μ := by
      have heq : (fun t => mFourierCoeff3 (L2VF_projComponentC j (alPkg.u t : L2VF)) k)
          = fun t => fourierCoeffCLM k (L2VF_projComponentC j (alPkg.u t : L2VF)) := by
        funext t; rw [fourierCoeffCLM_apply]
      rw [heq]
      exact ((fourierCoeffCLM k).continuous.comp
        (L2VF_projComponentC j).continuous).comp_aestronglyMeasurable hu_aesm
    exact aestronglyMeasurable_const.mul
      (Complex.continuous_re.comp_aestronglyMeasurable (h1.mul aestronglyMeasurable_const))
  have hAESM_b : AEStronglyMeasurable (fun t => F.b (alPkg.u t) (alPkg.u t) w) μ := by
    have h := b_clm.continuous₂.comp_aestronglyMeasurable (hsu_aesm.prodMk hsu_aesm)
    exact h.congr (Filter.Eventually.of_forall fun t => rfl)
  -- Integrability of the two WeakFormNS integrands (limit curve and approximants).
  have hAESM_inner : AEStronglyMeasurable
      (fun t => inner (𝕜 := ℝ) (alPkg.u t : L2VF) (w : L2VF)) μ := by
    have h := (innerSL ℝ (w : L2VF)).continuous.comp_aestronglyMeasurable hu_aesm
    refine h.congr (Filter.Eventually.of_forall fun t => ?_)
    simp only [innerSL_apply_apply]
    exact real_inner_comm _ _
  have hIntG_su : Integrable (fun t => Gf alPkg.u t) μ := by
    simp only [hGf]
    refine Integrable.add ?_ ?_
    · refine Integrable.mono' (g := fun t => ‖(w : L2VF)‖ * Mψ' * ‖(alPkg.u t : L2VF)‖)
        (hInt_uu_norm.const_mul _) (hAESM_inner.neg.mul hψC1.continuous_deriv_one.aestronglyMeasurable) ?_
      rw [hμdef]
      refine (ae_restrict_iff' measurableSet_Icc).mpr (ae_of_all _ fun t ht => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_neg]
      calc |inner (𝕜 := ℝ) (alPkg.u t : L2VF) (w : L2VF)| * |deriv ψ t|
          ≤ ‖(alPkg.u t : L2VF)‖ * ‖(w : L2VF)‖ * Mψ' :=
            mul_le_mul (abs_real_inner_le_norm _ _)
              (by rw [← Real.norm_eq_abs]; exact hMψ' t ht) (abs_nonneg _) (by positivity)
        _ = ‖(w : L2VF)‖ * Mψ' * ‖(alPkg.u t : L2VF)‖ := by ring
    · refine Integrable.mono'
        (g := fun t => Mψ * (ν * Cs * ‖(alPkg.u t : L2VF)‖) + Mψ * (Cb' * ‖(alPkg.u t : L2VF)‖ ^ 2))
        (((hInt_uu_norm.const_mul (ν * Cs)).const_mul Mψ).add
          ((hInt_uu_sq.const_mul Cb').const_mul Mψ))
        (hψC1.continuous.aestronglyMeasurable.mul
          ((aestronglyMeasurable_const.mul hAESM_stokes).add hAESM_b)) ?_
      rw [hμdef]
      refine (ae_restrict_iff' measurableSet_Icc).mpr (ae_of_all _ fun t ht => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      have hψb : |ψ t| ≤ Mψ := by rw [← Real.norm_eq_abs]; exact hMψ t ht
      calc |ψ t| * |ν * stokesTestPairing (alPkg.u t : L2VF) (w : L2VF)
              + F.b (alPkg.u t) (alPkg.u t) w|
          ≤ Mψ * (ν * Cs * ‖(alPkg.u t : L2VF)‖ + Cb' * ‖(alPkg.u t : L2VF)‖ ^ 2) := by
            refine mul_le_mul hψb ?_ (abs_nonneg _) hMψ0
            calc |ν * stokesTestPairing (alPkg.u t : L2VF) (w : L2VF)
                    + F.b (alPkg.u t) (alPkg.u t) w|
                ≤ |ν * stokesTestPairing (alPkg.u t : L2VF) (w : L2VF)|
                  + |F.b (alPkg.u t) (alPkg.u t) w| := abs_add_le _ _
              _ = ν * |stokesTestPairing (alPkg.u t : L2VF) (w : L2VF)|
                  + |F.b (alPkg.u t) (alPkg.u t) w| := by rw [abs_mul, abs_of_nonneg hν.le]
              _ ≤ ν * (Cs * ‖(alPkg.u t : L2VF)‖) + Cb' * ‖(alPkg.u t : L2VF)‖ ^ 2 := by
                  refine add_le_add (mul_le_mul_of_nonneg_left (hCs _) hν.le) ?_
                  calc |F.b (alPkg.u t) (alPkg.u t) w|
                      ≤ Cb' * ‖(alPkg.u t : L2VF)‖ * ‖(alPkg.u t : L2VF)‖ := hCb' _ _
                    _ = Cb' * ‖(alPkg.u t : L2VF)‖ ^ 2 := by ring
              _ = ν * Cs * ‖(alPkg.u t : L2VF)‖ + Cb' * ‖(alPkg.u t : L2VF)‖ ^ 2 := by ring
        _ = Mψ * (ν * Cs * ‖(alPkg.u t : L2VF)‖) + Mψ * (Cb' * ‖(alPkg.u t : L2VF)‖ ^ 2) := by ring
  have hcontG_sN : ∀ N, ContinuousOn
      (fun t => Gf (fun s => (galSeq (alPkg.φ N)).u s) t) (Set.Icc 0 T) := by
    intro N
    have hcurve := hcont_uN N
    have hinner_cont : ContinuousOn
        (fun t => inner (𝕜 := ℝ) ((galSeq (alPkg.φ N)).u t : L2VF) (w : L2VF)) (Set.Icc 0 T) :=
      ((innerSL ℝ (w : L2VF)).continuous.comp_continuousOn hcurve).congr
        (fun t _ => real_inner_comm _ _)
    have hstokes_cont : ContinuousOn
        (fun t => stokesTestPairing ((galSeq (alPkg.φ N)).u t : L2VF) (w : L2VF)) (Set.Icc 0 T) := by
      have hfin : (fun t => stokesTestPairing ((galSeq (alPkg.φ N)).u t : L2VF) (w : L2VF))
          = fun t => ∑ j : Fin 3, ∑ k ∈ fourierBox n₀,
              ((2 * Real.pi) ^ 2 * ∑ i : Fin 3, (k i : ℝ) ^ 2) *
              (mFourierCoeff3 (L2VF_projComponentC j ((galSeq (alPkg.φ N)).u t : L2VF)) k *
                starRingEnd ℂ (mFourierCoeff3 (L2VF_projComponentC j (w : L2VF)) k)).re := by
        funext t; exact stokesTestPairing_eq_boxSum n₀ (w : L2VF) hn₀ _
      rw [hfin]
      apply continuousOn_finsetSum Finset.univ; intro j _
      apply continuousOn_finsetSum (fourierBox n₀); intro k _
      apply ContinuousOn.mul continuousOn_const
      apply ContinuousOn.comp Complex.continuous_re.continuousOn _ (Set.mapsTo_univ _ _)
      apply ContinuousOn.mul _ continuousOn_const
      have heq : (fun t => mFourierCoeff3 (L2VF_projComponentC j ((galSeq (alPkg.φ N)).u t : L2VF)) k)
          = fun t => fourierCoeffCLM k (L2VF_projComponentC j ((galSeq (alPkg.φ N)).u t : L2VF)) := by
        funext t; rw [fourierCoeffCLM_apply]
      rw [heq]
      exact ((fourierCoeffCLM k).continuous.comp
        (L2VF_projComponentC j).continuous).comp_continuousOn hcurve
    have hcurve_sigma : ContinuousOn (fun t => (galSeq (alPkg.φ N)).u t) (Set.Icc 0 T) := by
      have hiso : Isometry (fun x : L2Sigma => (x : L2VF)) := by
        rw [isometry_iff_dist_eq]; intro x y
        simp only [dist_eq_norm, ← AddSubgroupClass.coe_sub, Submodule.coe_norm]
      exact hiso.isUniformInducing.isInducing.continuousOn_iff.mpr hcurve
    have hb_cont : ContinuousOn
        (fun t => F.b ((galSeq (alPkg.φ N)).u t) ((galSeq (alPkg.φ N)).u t) w) (Set.Icc 0 T) :=
      ((b_clm.continuous₂.comp_continuousOn (hcurve_sigma.prodMk hcurve_sigma)).congr
        (fun t _ => (hbclm_eq _ _).symm))
    simp only [hGf]
    exact (hinner_cont.neg.mul hψC1.continuous_deriv_one.continuousOn).add
      (hψC1.continuous.continuousOn.mul ((continuousOn_const.mul hstokes_cont).add hb_cont))
  have hIntG_sN : ∀ N, Integrable (fun t => Gf (fun s => (galSeq (alPkg.φ N)).u s) t) μ := fun N => by
    rw [hμdef]; exact (hcontG_sN N).integrableOn_Icc
  -- Constants and the pointwise dominator.
  set K1 : ℝ := Mψ' * ‖(w : L2VF)‖ + Mψ * ν * Cs + Mψ * Cb' * ‖(u₀ : L2VF)‖ with hK1
  set K2 : ℝ := Mψ * Cb' with hK2
  set Pbound : ℕ → ℝ → ℝ := fun N t => K1 * ‖dN N t‖ + K2 * (‖dN N t‖ * ‖(alPkg.u t : L2VF)‖)
    with hPbound
  set RHS : ℕ → ℝ := fun N =>
    K1 * (∫ t, ‖dN N t‖ ∂μ) + K2 * (∫ t, ‖dN N t‖ * ‖(alPkg.u t : L2VF)‖ ∂μ) with hRHSdef
  -- `e N = (∫ ‖dN N‖²)^{1/2}` and Hölder bounds.
  have he_eq : ∀ N, e N = (∫ t, ‖dN N t‖ ^ (2 : ℝ) ∂μ) ^ (2 : ℝ)⁻¹ := by
    intro N
    rw [hedef]; simp only
    rw [(hMemLp_dN N).eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num),
      ENNReal.toReal_ofReal (by positivity)]
    norm_num
  set euu : ℝ := (∫ t, ‖(alPkg.u t : L2VF)‖ ^ (2 : ℝ) ∂μ) ^ (2 : ℝ)⁻¹ with heuu
  set Sμ : ℝ := (∫ _t : ℝ, ‖(1 : ℝ)‖ ^ (2 : ℝ) ∂μ) ^ (2 : ℝ)⁻¹ with hSμ
  have hholderpq : (2 : ℝ).HolderConjugate 2 := Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hi_le : ∀ N, (∫ t, ‖dN N t‖ ∂μ) ≤ e N * Sμ := by
    intro N
    have h := integral_mul_norm_le_Lp_mul_Lq (μ := μ) hholderpq
      (f := fun t => ‖dN N t‖) (g := fun _ : ℝ => (1 : ℝ))
      (by rw [show ENNReal.ofReal (2 : ℝ) = 2 by norm_num]; exact (hMemLp_dN N).norm)
      (by rw [show ENNReal.ofReal (2 : ℝ) = 2 by norm_num]; exact memLp_const 1)
    simp only [Real.norm_eq_abs, norm_one, mul_one, one_div] at h
    rw [he_eq, hSμ]; simpa [one_div, Real.norm_eq_abs] using h
  have hj_le : ∀ N, (∫ t, ‖dN N t‖ * ‖(alPkg.u t : L2VF)‖ ∂μ) ≤ e N * euu := by
    intro N
    have h := integral_mul_norm_le_Lp_mul_Lq (μ := μ) hholderpq
      (f := fun t => dN N t) (g := fun t => (alPkg.u t : L2VF))
      (by rw [show ENNReal.ofReal (2 : ℝ) = 2 by norm_num]; exact hMemLp_dN N)
      (by rw [show ENNReal.ofReal (2 : ℝ) = 2 by norm_num]; exact hMemLp_uu)
    rw [he_eq, heuu]; simpa [one_div] using h
  have hi_nonneg : ∀ N, 0 ≤ (∫ t, ‖dN N t‖ ∂μ) := fun N => integral_nonneg fun t => norm_nonneg _
  have hj_nonneg : ∀ N, 0 ≤ (∫ t, ‖dN N t‖ * ‖(alPkg.u t : L2VF)‖ ∂μ) := fun N =>
    integral_nonneg fun t => by positivity
  have hi0 : Filter.Tendsto (fun N => ∫ t, ‖dN N t‖ ∂μ) Filter.atTop (nhds 0) :=
    squeeze_zero hi_nonneg hi_le (by simpa using hE0.mul_const Sμ)
  have hj0 : Filter.Tendsto (fun N => ∫ t, ‖dN N t‖ * ‖(alPkg.u t : L2VF)‖ ∂μ) Filter.atTop (nhds 0) :=
    squeeze_zero hj_nonneg hj_le (by simpa using hE0.mul_const euu)
  have hRHS0 : Filter.Tendsto RHS Filter.atTop (nhds 0) := by
    have := (hi0.const_mul K1).add (hj0.const_mul K2)
    simpa [hRHSdef] using this
  -- Pointwise dominator bound and its integral.
  have hK10 : 0 ≤ K1 := by
    rw [hK1]
    exact add_nonneg (add_nonneg (mul_nonneg hMψ'0 (norm_nonneg _))
      (mul_nonneg (mul_nonneg hMψ0 hν.le) hCs0)) (mul_nonneg (mul_nonneg hMψ0 hCb'0) (norm_nonneg _))
  have hK20 : 0 ≤ K2 := mul_nonneg hMψ0 hCb'0
  have hIntP : ∀ N, Integrable (Pbound N) μ := fun N => by
    rw [hPbound]; exact ((hInt_dN_norm N).const_mul K1).add ((hInt_dN_uu N).const_mul K2)
  have hPbound_split : ∀ N, ∫ t, Pbound N t ∂μ = RHS N := by
    intro N; rw [hPbound, hRHSdef]; simp only
    rw [integral_add ((hInt_dN_norm N).const_mul K1) ((hInt_dN_uu N).const_mul K2),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  have hdiff_le : ∀ N, (fun t => |Gf alPkg.u t - Gf (fun s => (galSeq (alPkg.φ N)).u s) t|)
      ≤ᵐ[μ] Pbound N := by
    intro N
    rw [hμdef]
    refine (ae_restrict_iff' measurableSet_Icc).mpr (ae_of_all _ fun t ht => ?_)
    -- rewrite the difference into linearised form
    have hinner_d : -(inner (𝕜 := ℝ) (alPkg.u t : L2VF) (w : L2VF))
          - -(inner (𝕜 := ℝ) ((galSeq (alPkg.φ N)).u t : L2VF) (w : L2VF))
        = inner (𝕜 := ℝ) (dN N t) (w : L2VF) := by
      rw [hdNval, inner_sub_left]; ring
    have hstokes_d : stokesTestPairing (alPkg.u t : L2VF) (w : L2VF)
          - stokesTestPairing ((galSeq (alPkg.φ N)).u t : L2VF) (w : L2VF)
        = stokesTestPairing ((alPkg.u t : L2VF) - ((galSeq (alPkg.φ N)).u t : L2VF)) (w : L2VF) := by
      have h := Torus.stokesTestPairing_add_left n₀ ((alPkg.u t : L2VF) - ((galSeq (alPkg.φ N)).u t : L2VF))
        ((galSeq (alPkg.φ N)).u t : L2VF) (w : L2VF) hn₀
      rw [sub_add_cancel] at h; linarith
    have hb_d : F.b (alPkg.u t) (alPkg.u t) w
          - F.b ((galSeq (alPkg.φ N)).u t) ((galSeq (alPkg.φ N)).u t) w
        = F.b (alPkg.u t - (galSeq (alPkg.φ N)).u t) (alPkg.u t) w
          + F.b ((galSeq (alPkg.φ N)).u t) (alPkg.u t - (galSeq (alPkg.φ N)).u t) w := by
      rw [F.b_sub_1, F.b_sub_2]; ring
    have hnδ : ‖((alPkg.u t - (galSeq (alPkg.φ N)).u t : L2Sigma) : L2VF)‖ = ‖dN N t‖ := by
      rw [AddSubgroupClass.coe_sub, hdNval, norm_sub_rev]
    have hnorm_su_sN : ‖(alPkg.u t : L2VF) - ((galSeq (alPkg.φ N)).u t : L2VF)‖ = ‖dN N t‖ := by
      rw [hdNval, norm_sub_rev]
    -- subterm bounds
    have hI1 : |inner (𝕜 := ℝ) (dN N t) (w : L2VF)| ≤ ‖dN N t‖ * ‖(w : L2VF)‖ :=
      abs_real_inner_le_norm _ _
    have hψ'b : |deriv ψ t| ≤ Mψ' := by rw [← Real.norm_eq_abs]; exact hMψ' t ht
    have hψb : |ψ t| ≤ Mψ := by rw [← Real.norm_eq_abs]; exact hMψ t ht
    have hSb : |stokesTestPairing ((alPkg.u t : L2VF) - ((galSeq (alPkg.φ N)).u t : L2VF)) (w : L2VF)|
        ≤ Cs * ‖dN N t‖ := by rw [← hnorm_su_sN]; exact hCs _
    have hB1 : |F.b (alPkg.u t - (galSeq (alPkg.φ N)).u t) (alPkg.u t) w|
        ≤ Cb' * ‖dN N t‖ * ‖(alPkg.u t : L2VF)‖ := by
      refine (hCb' _ _).trans (le_of_eq ?_); rw [hnδ]
    have hB2 : |F.b ((galSeq (alPkg.φ N)).u t) (alPkg.u t - (galSeq (alPkg.φ N)).u t) w|
        ≤ Cb' * ‖(u₀ : L2VF)‖ * ‖dN N t‖ := by
      refine (hCb' _ _).trans ?_; rw [hnδ]
      gcongr
      · exact hnorm_uN N t ht
    -- assemble
    have hcombine : Gf alPkg.u t - Gf (fun s => (galSeq (alPkg.φ N)).u s) t
        = inner (𝕜 := ℝ) (dN N t) (w : L2VF) * deriv ψ t
          + ψ t * (ν * stokesTestPairing ((alPkg.u t : L2VF) - ((galSeq (alPkg.φ N)).u t : L2VF)) (w : L2VF)
            + (F.b (alPkg.u t - (galSeq (alPkg.φ N)).u t) (alPkg.u t) w
               + F.b ((galSeq (alPkg.φ N)).u t) (alPkg.u t - (galSeq (alPkg.φ N)).u t) w)) := by
      simp only [hGf]; rw [← hinner_d, ← hstokes_d, ← hb_d]; ring
    show |Gf alPkg.u t - Gf (fun s => (galSeq (alPkg.φ N)).u s) t| ≤ Pbound N t
    rw [hcombine, hPbound]; simp only
    have hpiece1 : |inner (𝕜 := ℝ) (dN N t) (w : L2VF) * deriv ψ t|
        ≤ ‖dN N t‖ * ‖(w : L2VF)‖ * Mψ' := by
      rw [abs_mul]; exact mul_le_mul hI1 hψ'b (abs_nonneg _) (by positivity)
    have hpiece2 : |ψ t * (ν * stokesTestPairing ((alPkg.u t : L2VF)
          - ((galSeq (alPkg.φ N)).u t : L2VF)) (w : L2VF)
          + (F.b (alPkg.u t - (galSeq (alPkg.φ N)).u t) (alPkg.u t) w
             + F.b ((galSeq (alPkg.φ N)).u t) (alPkg.u t - (galSeq (alPkg.φ N)).u t) w))|
        ≤ Mψ * (ν * (Cs * ‖dN N t‖)
            + (Cb' * ‖dN N t‖ * ‖(alPkg.u t : L2VF)‖ + Cb' * ‖(u₀ : L2VF)‖ * ‖dN N t‖)) := by
      rw [abs_mul]
      refine mul_le_mul hψb ?_ (abs_nonneg _) hMψ0
      calc |ν * stokesTestPairing ((alPkg.u t : L2VF) - ((galSeq (alPkg.φ N)).u t : L2VF)) (w : L2VF)
              + (F.b (alPkg.u t - (galSeq (alPkg.φ N)).u t) (alPkg.u t) w
                 + F.b ((galSeq (alPkg.φ N)).u t) (alPkg.u t - (galSeq (alPkg.φ N)).u t) w)|
          ≤ |ν * stokesTestPairing ((alPkg.u t : L2VF) - ((galSeq (alPkg.φ N)).u t : L2VF)) (w : L2VF)|
            + |F.b (alPkg.u t - (galSeq (alPkg.φ N)).u t) (alPkg.u t) w
               + F.b ((galSeq (alPkg.φ N)).u t) (alPkg.u t - (galSeq (alPkg.φ N)).u t) w| := abs_add_le _ _
        _ ≤ ν * (Cs * ‖dN N t‖)
            + (Cb' * ‖dN N t‖ * ‖(alPkg.u t : L2VF)‖ + Cb' * ‖(u₀ : L2VF)‖ * ‖dN N t‖) := by
            refine add_le_add ?_ ((abs_add_le _ _).trans (add_le_add hB1 hB2))
            rw [abs_mul, abs_of_nonneg hν.le]
            exact mul_le_mul_of_nonneg_left hSb hν.le
    calc |inner (𝕜 := ℝ) (dN N t) (w : L2VF) * deriv ψ t
            + ψ t * (ν * stokesTestPairing ((alPkg.u t : L2VF) - ((galSeq (alPkg.φ N)).u t : L2VF)) (w : L2VF)
              + (F.b (alPkg.u t - (galSeq (alPkg.φ N)).u t) (alPkg.u t) w
                 + F.b ((galSeq (alPkg.φ N)).u t) (alPkg.u t - (galSeq (alPkg.φ N)).u t) w))|
        ≤ ‖dN N t‖ * ‖(w : L2VF)‖ * Mψ'
          + Mψ * (ν * (Cs * ‖dN N t‖)
              + (Cb' * ‖dN N t‖ * ‖(alPkg.u t : L2VF)‖ + Cb' * ‖(u₀ : L2VF)‖ * ‖dN N t‖)) :=
          (abs_add_le _ _).trans (add_le_add hpiece1 hpiece2)
      _ = K1 * ‖dN N t‖ + K2 * (‖dN N t‖ * ‖(alPkg.u t : L2VF)‖) := by rw [hK1, hK2]; ring
  -- The limit passage: `∫ Gf alPkg.u = 0`.
  have key : ∫ t in (0 : ℝ)..T, Gf alPkg.u t = 0 := by
    rw [hbridge]
    have hbound : ∀ N, |(∫ t, Gf alPkg.u t ∂μ) - ∫ t, Gf (fun s => (galSeq (alPkg.φ N)).u s) t ∂μ|
        ≤ RHS N := by
      intro N
      calc |(∫ t, Gf alPkg.u t ∂μ) - ∫ t, Gf (fun s => (galSeq (alPkg.φ N)).u s) t ∂μ|
          = |∫ t, (Gf alPkg.u t - Gf (fun s => (galSeq (alPkg.φ N)).u s) t) ∂μ| := by
            rw [integral_sub hIntG_su (hIntG_sN N)]
        _ ≤ ∫ t, |Gf alPkg.u t - Gf (fun s => (galSeq (alPkg.φ N)).u s) t| ∂μ := by
            have := norm_integral_le_integral_norm (μ := μ)
              (fun t => Gf alPkg.u t - Gf (fun s => (galSeq (alPkg.φ N)).u s) t)
            simpa [Real.norm_eq_abs] using this
        _ ≤ ∫ t, Pbound N t ∂μ :=
            integral_mono_ae ((hIntG_su.sub (hIntG_sN N)).abs) (hIntP N) (hdiff_le N)
        _ = RHS N := hPbound_split N
    have hzero : ∀ N, n₀ ≤ alPkg.φ N →
        ∫ t, Gf (fun s => (galSeq (alPkg.φ N)).u s) t ∂μ = 0 := by
      intro N hN; rw [← hbridge]; exact hgal_zero N hN
    have hle0 : |∫ t, Gf alPkg.u t ∂μ| ≤ 0 := by
      refine ge_of_tendsto hRHS0 ?_
      refine Filter.eventually_atTop.2 ⟨n₀, fun N hN => ?_⟩
      have hφ : n₀ ≤ alPkg.φ N := hN.trans alPkg.φ_mono.le_apply
      have hb := hbound N
      rw [hzero N hφ, sub_zero] at hb
      exact hb
    exact abs_nonpos_iff.mp hle0
  -- Convert the WeakFormNS goal to the `Gf` form via `Submodule.coe_inner`.
  refine Eq.trans ?_ key
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [hGf]
  rfl

end LerayHopf
