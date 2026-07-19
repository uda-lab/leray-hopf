/-
# LerayHopf.R3.GoodRepresentative — weakly-continuous representative on ℝ³

**Campaign node:** R3 galerkin_limit_passage_R3 removal, issue #4 PR-5.

This file constructs the **weakly-continuous ∀t representative** `v` of the Aubin–Lions
limit `alPkg.u` and provides the key structural lemmas feeding into the final assembly:

- `perTest_lipschitz_R3` — per-Galerkin-test equi-Lipschitz bound (Stokes negLap bound via
  `range_schwartz`, `b_bound` bound, level promotion via `mono_range`).
- `exists_weak_representative_R3` — the master ∀t-weak-limit construction (R3 port of the
  torus `exists_weak_representative`; uses per-ball convergence via `inner_tendsto_of_perball`
  instead of the torus's L2-strong subsequence).
- `weak_trace_inner_R3` — weak initial trace `⟪v(t), u₀⟫ → ‖u₀‖²` as `t → 0⁺`.
- `strong_trace_of_props_R3` — strong initial trace `v(t) → u₀` in L²_σ(ℝ³) as `t → 0⁺`.

## Route (R1 from issue #93 §1a)

No Lions–Magenes / `TimeSobolev` / `W1pTime`. The ∀t representative is built by the
classical Temam-III.3 equi-Lipschitz + dense-times-Cauchy + Riesz-in-submodule route,
exactly as proved for T³ in `TorusTraceEnergy.lean`.

R3 deltas vs. torus:
- A.e.-t weak convergence comes from `inner_tendsto_of_perball` (per-ball strong convergence);
  no further a.e.-subsequence extraction is needed.
- Level promotion uses `𝔊.mono_range` (`SolutionInterfaces.lean:207`).
- Per-test Stokes bound comes from `negLap` + `range_schwartz` + `stokesTestPairing_abs_le`.
- Density in `L2Sigma_R3` is `𝔊.tendsto_id`.

## Axioms

No new axioms.  All four scaffold `sorry` (PR-5) are discharged: the proofs are complete.
-/

import LerayHopf.Bochner.WeakLimitToolkit
import LerayHopf.R3.AubinLionsLimitPassage
import LerayHopf.R3.GalerkinTrilinearBound

namespace LerayHopf

open MeasureTheory Filter Topology

variable {𝔊 : R3GalerkinScheme} {F : R3NSForms 𝔊}
variable {ν : ℝ} {hν : 0 < ν} {T : ℝ} {hT : 0 < T}
variable {u₀ : L2Sigma_R3}
variable {galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n}

/-! ### Per-test equi-Lipschitz bound -/

/-- **Generic-bundle counterpart of `EnergyWeakLsc.galerkin_norm_le_u0`** (verbatim port): the
Galerkin state is `L²`-bounded by the initial datum, using only the generic `energy_bound` field
and `𝔊.norm_le` — no R3-specific (`viscous_curve_continuous`) enrichment is needed for this fact.

Kept local/private rather than reusing `galerkin_norm_le_u0` directly: that lemma is typed on the
concrete `GalerkinSolutionData_R3`, and `perTest_lipschitz_R3`'s narrowed (issue #135) `galSeq`
argument is generic — there is no `GalerkinSolutionData_R3 → Galerkin.SolutionData` direction to
project along, so the (already-verified) proof is ported instead of the statement being reused. -/
private theorem galerkin_norm_le_u0_generic (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (u₀ : L2Sigma_R3) (n : ℕ)
    (gs : Galerkin.SolutionData (r3Domain 𝔊) F.core ν u₀ n) {t : ℝ} (ht : 0 ≤ t) :
    ‖(gs.u t : L2VF_R3)‖ ≤ ‖(u₀ : L2VF_R3)‖ := by
  have hP : ‖𝔊.P n (u₀ : L2VF_R3)‖ ≤ ‖(u₀ : L2VF_R3)‖ := 𝔊.norm_le n (u₀ : L2VF_R3)
  have henergy := gs.energy_bound t ht
  have hsq : ‖(gs.u t : L2VF_R3)‖ ^ 2 ≤ ‖(u₀ : L2VF_R3)‖ ^ 2 := by
    have h2 : ‖𝔊.P n (u₀ : L2VF_R3)‖ ^ 2 ≤ ‖(u₀ : L2VF_R3)‖ ^ 2 := by
      have := mul_le_mul hP hP (norm_nonneg _) (norm_nonneg _)
      nlinarith [this]
    nlinarith [henergy, h2]
  exact le_of_sq_le_sq hsq (norm_nonneg _)

/-- The scalar test curve `t ↦ ⟪uₙ(t), w⟫` has derivative
`-(ν·stokesTestPairing_R3(uₙ t, w) + b(uₙ t, uₙ t, w))` at forward times, for tests fixed at
level `n` (from `u_hasDeriv` + `u_ode`).  R3 port of the torus `perTest_hasDerivAt`. -/
private theorem perTest_hasDerivAt_R3 (ν : ℝ) (u₀ : L2Sigma_R3) (n : ℕ)
    (gs : Galerkin.SolutionData (r3Domain 𝔊) F.core ν u₀ n) (w : L2Sigma_R3)
    (hwn : 𝔊.P n (w : L2VF_R3) = (w : L2VF_R3)) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt (fun s => inner (𝕜 := ℝ) ((gs.u s : L2VF_R3)) (w : L2VF_R3))
      (-(ν * stokesTestPairing_R3 (gs.u t : L2VF_R3) (w : L2VF_R3) + F.b (gs.u t) (gs.u t) w)) t := by
  have hda := (gs.u_hasDeriv t ht).inner (𝕜 := ℝ) (hasDerivAt_const t (w : L2VF_R3))
  simp only [inner_zero_right, zero_add] at hda
  have hode := gs.u_ode t ht w hwn.symm
  simp only [R3NSForms.core_b] at hode
  have hval : inner (𝕜 := ℝ) (deriv (fun s => (gs.u s : L2VF_R3)) t) (w : L2VF_R3)
      = -(ν * stokesTestPairing_R3 (gs.u t : L2VF_R3) (w : L2VF_R3) + F.b (gs.u t) (gs.u t) w) := by
    linarith
  rwa [hval] at hda

set_option maxHeartbeats 1000000 in
-- kept at the original 1000000 (issue #152): isolated `#count_heartbeats in` measurement
-- reported ~2360 heartbeats, but sibling declarations elsewhere in this file family with
-- comparably low isolated measurements failed under the default budget in a real rebuild — no
-- reduction from the original value was attempted without a dedicated re-verification cycle.
/-- **Per-Galerkin-test equi-Lipschitz bound** on ℝ³.  For a Galerkin test `w` at level `n₀`,
and any Galerkin level `n ≥ n₀`, the scalar pairing curve
`t ↦ ⟪uₙ(t), w⟫` is Lipschitz on `[0,∞)` with constant
`L(w) := ν·Cs(w)·‖u₀‖ + Cb(w)·‖u₀‖²`,
where `Cs(w)` comes from `stokesTestPairing_abs_le` via `range_schwartz` + negLap,
and `Cb(w)` from `F.b_bound`. -/
theorem perTest_lipschitz_R3
    (ν : ℝ) (hν : 0 < ν) (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, Galerkin.SolutionData (r3Domain 𝔊) F.core ν u₀ n)
    (w : L2Sigma_R3) (hw : IsSchwartzDivFree_R3 w) (n₀ : ℕ)
    (hn₀ : 𝔊.P n₀ (w : L2VF_R3) = (w : L2VF_R3)) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ n, n₀ ≤ n → ∀ s ∈ Set.Ici (0 : ℝ), ∀ t ∈ Set.Ici (0 : ℝ),
      |inner (𝕜 := ℝ) (((galSeq n).u t : L2VF_R3)) (w : L2VF_R3)
        - inner (𝕜 := ℝ) (((galSeq n).u s : L2VF_R3)) (w : L2VF_R3)| ≤ L * |t - s| := by
  classical
  obtain ⟨ψw, hψw⟩ := hw
  -- The Stokes functional at the fixed Schwartz test `w` is an inner product against a FIXED
  -- element `vElt` (negative-Laplacian reformulation + component adjoints).
  obtain ⟨E, hE⟩ : ∃ E : Fin 3 → Lp ℝ 2 (volume : Measure Domain3),
      ∀ x : L2VF_R3, stokesTestPairing_R3 x (w : L2VF_R3)
        = ∑ j : Fin 3, inner (𝕜 := ℝ) (L2VF_projComponent_R3 j x) (E j) :=
    ⟨_, fun x => stokesTestPairing_R3_eq_sum_inner_negLap x (w : L2VF_R3) ψw hψw⟩
  set vElt : L2VF_R3 := ∑ j : Fin 3, (L2VF_projComponent_R3 j).adjoint (E j) with hvElt
  have hstokes_inner : ∀ x : L2VF_R3,
      stokesTestPairing_R3 x (w : L2VF_R3) = inner (𝕜 := ℝ) vElt x := by
    intro x
    rw [hE x, hvElt, sum_inner]
    exact Finset.sum_congr rfl fun j _ => by
      rw [ContinuousLinearMap.adjoint_inner_left]; exact real_inner_comm _ _
  set Cs : ℝ := ‖vElt‖ with hCs
  have hCs0 : 0 ≤ Cs := norm_nonneg _
  have hCsbound : ∀ x : L2VF_R3, |stokesTestPairing_R3 x (w : L2VF_R3)| ≤ Cs * ‖x‖ := by
    intro x
    rw [hstokes_inner x, hCs]
    exact abs_real_inner_le_norm vElt x
  -- Convection-form bound constant (made nonnegative).
  obtain ⟨Cb, hCb⟩ := F.b_bound w ⟨ψw, hψw⟩
  set Cb' : ℝ := |Cb| with hCb'
  have hCb'0 : 0 ≤ Cb' := abs_nonneg _
  have hCb'bound : ∀ u v : L2Sigma_R3, |F.b u v w| ≤ Cb' * ‖(u : L2VF_R3)‖ * ‖(v : L2VF_R3)‖ :=
    fun u v => (hCb u v).trans (by gcongr; exact le_abs_self _)
  set L : ℝ := ν * Cs * ‖(u₀ : L2VF_R3)‖ + Cb' * ‖(u₀ : L2VF_R3)‖ ^ 2 with hLdef
  have hL0 : 0 ≤ L := by
    have h1 : 0 ≤ ν * Cs * ‖(u₀ : L2VF_R3)‖ :=
      mul_nonneg (mul_nonneg hν.le hCs0) (norm_nonneg _)
    have h2 : 0 ≤ Cb' * ‖(u₀ : L2VF_R3)‖ ^ 2 := mul_nonneg hCb'0 (sq_nonneg _)
    linarith
  refine ⟨L, hL0, fun n hn s hs t ht => ?_⟩
  set gs := galSeq n with hgs
  have hwn : 𝔊.P n (w : L2VF_R3) = (w : L2VF_R3) := 𝔊.mono_range n₀ n hn (w : L2VF_R3) hn₀
  -- uniform derivative bound on `[0, ∞)`
  have hbound : ∀ r ∈ Set.Ici (0 : ℝ),
      ‖-(ν * stokesTestPairing_R3 (gs.u r : L2VF_R3) (w : L2VF_R3) + F.b (gs.u r) (gs.u r) w)‖
        ≤ L := by
    intro r hr
    rw [Real.norm_eq_abs, abs_neg]
    have hnorm := galerkin_norm_le_u0_generic 𝔊 F ν u₀ n gs (Set.mem_Ici.mp hr)
    have h1 : |ν * stokesTestPairing_R3 (gs.u r : L2VF_R3) (w : L2VF_R3)|
        ≤ ν * Cs * ‖(u₀ : L2VF_R3)‖ := by
      rw [abs_mul, abs_of_pos hν, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ hν.le
      exact (hCsbound _).trans (mul_le_mul_of_nonneg_left hnorm hCs0)
    have h2 : |F.b (gs.u r) (gs.u r) w| ≤ Cb' * ‖(u₀ : L2VF_R3)‖ ^ 2 := by
      refine (hCb'bound (gs.u r) (gs.u r)).trans ?_
      have hn0 : 0 ≤ ‖(gs.u r : L2VF_R3)‖ := norm_nonneg _
      have hu0 : 0 ≤ ‖(u₀ : L2VF_R3)‖ := norm_nonneg _
      have hsq : ‖(gs.u r : L2VF_R3)‖ * ‖(gs.u r : L2VF_R3)‖
          ≤ ‖(u₀ : L2VF_R3)‖ * ‖(u₀ : L2VF_R3)‖ := mul_le_mul hnorm hnorm hn0 hu0
      calc Cb' * ‖(gs.u r : L2VF_R3)‖ * ‖(gs.u r : L2VF_R3)‖
          = Cb' * (‖(gs.u r : L2VF_R3)‖ * ‖(gs.u r : L2VF_R3)‖) := by ring
        _ ≤ Cb' * (‖(u₀ : L2VF_R3)‖ * ‖(u₀ : L2VF_R3)‖) := mul_le_mul_of_nonneg_left hsq hCb'0
        _ = Cb' * ‖(u₀ : L2VF_R3)‖ ^ 2 := by ring
    calc |ν * stokesTestPairing_R3 (gs.u r : L2VF_R3) (w : L2VF_R3) + F.b (gs.u r) (gs.u r) w|
        ≤ |ν * stokesTestPairing_R3 (gs.u r : L2VF_R3) (w : L2VF_R3)|
          + |F.b (gs.u r) (gs.u r) w| := abs_add_le _ _
      _ ≤ L := by rw [hLdef]; linarith
  -- MVT on the convex set `[0, ∞)`
  have hderiv : ∀ r ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt (fun s' => inner (𝕜 := ℝ) ((gs.u s' : L2VF_R3)) (w : L2VF_R3))
        (-(ν * stokesTestPairing_R3 (gs.u r : L2VF_R3) (w : L2VF_R3) + F.b (gs.u r) (gs.u r) w))
        (Set.Ici 0) r :=
    fun r hr => (perTest_hasDerivAt_R3 ν u₀ n gs w hwn r (Set.mem_Ici.mp hr)).hasDerivWithinAt
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
    (convex_Ici (0 : ℝ)) hs ht
  rwa [Real.norm_eq_abs, Real.norm_eq_abs] at hmvt

/-! ### The weakly-continuous good representative — S5 verbatim -/

set_option maxHeartbeats 1000000 in
-- kept at the original 1000000 (issue #152): isolated `#count_heartbeats in` measurement
-- reported ~3526 heartbeats, but sibling declarations elsewhere in this file family with
-- comparably low isolated measurements failed under the default budget in a real rebuild — no
-- reduction from the original value was attempted without a dedicated re-verification cycle.
/-- **Master construction: the ∀t-weakly-continuous representative** of the Aubin–Lions
limit on ℝ³.

Produces `v : Time → L2Sigma_R3` such that:
- (a.e.)      `v t = alPkg.u t` for a.e. `t ∈ [0, T]`.
- (∀t weak)  `⟪(galSeq (alPkg.φ n)).u t, z⟫ → ⟪v t, z⟫` for every `t ∈ [0, T]`, `z : L2VF_R3`.
- (∀t bound) `‖v t‖ ≤ ‖u₀‖` for every `t ∈ [0, T]`.
- (v 0)       `v 0 = u₀` (endpoint pinning via `u_initial` + `𝔊.tendsto_id`).
- (Lip)       `t ↦ ⟪v t, w⟫` is Lipschitz on `[0, T]` for every Galerkin test `w`.

This is the **verbatim S5 statement** from the feasibility spike
(`LerayHopf/Scratch/Issue4LimitPassageSpike.lean`). -/
theorem exists_weak_representative_R3
    (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T)
    (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n)
    (alPkg : AubinLionsPackage_R3 𝔊 F ν T u₀ galSeq) :
    ∃ v : Time → L2Sigma_R3,
      (∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)), v t = alPkg.u t) ∧
      (∀ t, t ∈ Set.Icc (0 : ℝ) T → ∀ z : L2VF_R3,
        Tendsto (fun n => inner (𝕜 := ℝ) (((galSeq (alPkg.φ n)).u t : L2VF_R3)) z) atTop
          (𝓝 (inner (𝕜 := ℝ) ((v t : L2VF_R3)) z))) ∧
      (∀ t, t ∈ Set.Icc (0 : ℝ) T → ‖(v t : L2VF_R3)‖ ≤ ‖(u₀ : L2VF_R3)‖) ∧
      v 0 = u₀ ∧
      (∀ w : L2Sigma_R3, IsGalerkinTest_R3 𝔊 w → ∃ L : ℝ, 0 ≤ L ∧
        ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc (0 : ℝ) T,
          |inner (𝕜 := ℝ) ((v t : L2VF_R3)) (w : L2VF_R3)
            - inner (𝕜 := ℝ) ((v s : L2VF_R3)) (w : L2VF_R3)| ≤ L * |t - s|) := by
  classical
  set c : ℕ → ℝ → L2VF_R3 := fun n t => ((galSeq (alPkg.φ n)).u t : L2VF_R3) with hcdef
  have hcmem : ∀ n t, c n t ∈ L2Sigma_R3 := fun n t => SetLike.coe_mem _
  have hcbd : ∀ n, ∀ t, 0 ≤ t → ‖c n t‖ ≤ ‖(u₀ : L2VF_R3)‖ :=
    fun n t ht => galerkin_norm_le_u0 𝔊 F ν u₀ (alPkg.φ n) (galSeq (alPkg.φ n)) ht
  have hlevel : ∀ n, n ≤ alPkg.φ n := fun n => alPkg.φ_mono.le_apply
  -- the a.e.-good set: per-ball (all nat radii) convergence to `alPkg.u t` + the kinetic bound.
  set S : Set ℝ := {t | (∀ k : ℕ, Tendsto (fun n => restrictToBall (k : ℝ) (c n t)) atTop
      (𝓝 (restrictToBall (k : ℝ) ((alPkg.u t : L2VF_R3))))) ∧
      ‖(alPkg.u t : L2VF_R3)‖ ≤ ‖(u₀ : L2VF_R3)‖} with hSdef
  have hS : ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)), t ∈ S := by
    have hperball_ae : ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ k : ℕ,
        Tendsto (fun n => restrictToBall (k : ℝ) (c n t)) atTop
          (𝓝 (restrictToBall (k : ℝ) ((alPkg.u t : L2VF_R3)))) :=
      ae_all_iff.2 (fun k => alPkg.strong_convergence_ae (k : ℝ))
    have hu_bound : ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
        ‖(alPkg.u t : L2VF_R3)‖ ≤ ‖(u₀ : L2VF_R3)‖ := by
      have hkin := kineticEnergy_lsc_bound 𝔊 F ν T u₀ galSeq alPkg
      filter_upwards [hkin] with t ht
      have h2 : ‖(alPkg.u t : L2VF_R3)‖ ^ 2 ≤ ‖(u₀ : L2VF_R3)‖ ^ 2 := by nlinarith [ht]
      nlinarith [norm_nonneg (alPkg.u t : L2VF_R3), norm_nonneg (u₀ : L2VF_R3), h2]
    filter_upwards [hperball_ae, hu_bound] with t h1 h2
    exact ⟨h1, h2⟩
  -- at any point of `S` (with `0 ≤ t`), the full sequence converges WEAKLY to `alPkg.u t`.
  have hweak_at_S : ∀ s ∈ S, 0 ≤ s → ∀ e : L2VF_R3,
      Tendsto (fun n => inner (𝕜 := ℝ) e (c n s)) atTop
        (𝓝 (inner (𝕜 := ℝ) e ((alPkg.u s : L2VF_R3)))) := by
    intro s hs hs0 e
    exact inner_tendsto_of_perball e (fun n => c n s) ((alPkg.u s : L2VF_R3))
      ‖(u₀ : L2VF_R3)‖ (norm_nonneg _) (fun n => hcbd n s hs0) hs.2 hs.1
  -- per-Galerkin-test Cauchy at EVERY `t ∈ [0, T]` (equi-Lipschitz + dense weak convergence).
  have hCauchy_test : ∀ (w : L2Sigma_R3), IsGalerkinTest_R3 𝔊 w → ∀ t, t ∈ Set.Icc (0 : ℝ) T →
      CauchySeq (fun n => inner (𝕜 := ℝ) (c n t) (w : L2VF_R3)) := by
    intro w hw t ht
    obtain ⟨n₀, hn₀⟩ := hw
    have hsdf : IsSchwartzDivFree_R3 w := by
      obtain ⟨ψ, hψ⟩ := 𝔊.range_schwartz n₀ (w : L2VF_R3)
      exact ⟨ψ, fun j => by rw [← hn₀]; exact hψ j⟩
    obtain ⟨L, hL0, hLip⟩ :=
      perTest_lipschitz_R3 ν hν u₀ (fun n => (galSeq n).toSolutionData) w hsdf n₀ hn₀
    refine cauchySeq_of_equiLipschitz_of_dense (T := T)
      (fun n s => inner (𝕜 := ℝ) (c n s) (w : L2VF_R3)) L hL0 n₀ ?_ S ?_ ?_ ht
    · intro n hn s hsI t' htI'
      exact hLip (alPkg.φ n) (le_trans hn (hlevel n))
        s (Set.Icc_subset_Ici_self hsI) t' (Set.Icc_subset_Ici_self htI')
    · intro u hu ε hε
      exact exists_mem_of_ae_full hT S hS hu hε
    · intro s hs'
      have hconv := hweak_at_S s hs'.1 hs'.2.1 (w : L2VF_R3)
      have hfun : (fun n => inner (𝕜 := ℝ) (c n s) (w : L2VF_R3))
          = fun n => inner (𝕜 := ℝ) (w : L2VF_R3) (c n s) := funext fun n => real_inner_comm _ _
      rw [hfun]; exact hconv.cauchySeq
  -- Cauchy for EVERY direction `z : L2VF_R3` (orthogonal split + Galerkin density).
  have hCauchy_all : ∀ t, t ∈ Set.Icc (0 : ℝ) T → ∀ z : L2VF_R3,
      CauchySeq (fun n => inner (𝕜 := ℝ) (c n t) z) := by
    intro t ht z
    set zσ : L2VF_R3 := L2Sigma_R3.starProjection z with hzσ
    have hzσmem : zσ ∈ L2Sigma_R3 := L2Sigma_R3.starProjection_apply_mem z
    have hsplit : ∀ n, inner (𝕜 := ℝ) (c n t) z = inner (𝕜 := ℝ) (c n t) zσ := by
      intro n
      have horth : z - zσ ∈ L2Sigma_R3ᗮ := L2Sigma_R3.sub_starProjection_mem_orthogonal z
      have h0 : inner (𝕜 := ℝ) (c n t) (z - zσ) = 0 :=
        (Submodule.mem_orthogonal L2Sigma_R3 _).mp horth _ (hcmem n t)
      rw [inner_sub_right] at h0
      linarith
    rw [show (fun n => inner (𝕜 := ℝ) (c n t) z)
        = fun n => inner (𝕜 := ℝ) (c n t) zσ from funext hsplit]
    refine cauchySeq_inner_extend (fun n => c n t) ‖(u₀ : L2VF_R3)‖
      (fun n => hcbd n t ht.1) zσ ?_
    intro ε hε
    obtain ⟨m, hm⟩ := Metric.tendsto_atTop.mp (𝔊.tendsto_id zσ hzσmem) ε hε
    have hdist := hm m (le_refl m)
    rw [dist_eq_norm] at hdist
    refine ⟨𝔊.P m zσ, by rwa [norm_sub_rev] at hdist, ?_⟩
    have hmem : 𝔊.P m zσ ∈ L2Sigma_R3 := 𝔊.preserves_sigma m zσ hzσmem
    have hfix : 𝔊.P m (𝔊.P m zσ) = 𝔊.P m zσ := 𝔊.idem m zσ
    exact hCauchy_test ⟨𝔊.P m zσ, hmem⟩ ⟨m, hfix⟩ t ht
  -- Riesz assembly inside the closed submodule `L2Sigma_R3`.
  have hex : ∀ t, t ∈ Set.Icc (0 : ℝ) T → ∃ y : L2VF_R3, y ∈ L2Sigma_R3 ∧
      ‖y‖ ≤ ‖(u₀ : L2VF_R3)‖ ∧
      ∀ z : L2VF_R3, Tendsto (fun n => inner (𝕜 := ℝ) (c n t) z) atTop
        (𝓝 (inner (𝕜 := ℝ) y z)) := fun t ht =>
    exists_weak_limit_in_submodule L2Sigma_R3 (fun n => c n t)
      (fun n => hcmem n t) ‖(u₀ : L2VF_R3)‖ (fun n => hcbd n t ht.1) (hCauchy_all t ht)
  choose! y hyK hybd hyconv using hex
  set v : Time → L2Sigma_R3 := fun t =>
    if ht : t ∈ Set.Icc (0 : ℝ) T then ⟨y t, hyK t ht⟩ else alPkg.u t with hvdef
  have hvcoe : ∀ t, t ∈ Set.Icc (0 : ℝ) T → (v t : L2VF_R3) = y t := by
    intro t ht
    simp only [hvdef]
    rw [dif_pos ht]
  -- everywhere weak convergence to `v`
  have hweak : ∀ t, t ∈ Set.Icc (0 : ℝ) T → ∀ z : L2VF_R3,
      Tendsto (fun n => inner (𝕜 := ℝ) (c n t) z) atTop
        (𝓝 (inner (𝕜 := ℝ) ((v t : L2VF_R3)) z)) := by
    intro t ht z
    rw [hvcoe t ht]
    exact hyconv t ht z
  -- a.e. agreement with the Aubin–Lions limit
  have hae : ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)), v t = alPkg.u t := by
    filter_upwards [hS, ae_restrict_mem measurableSet_Icc] with t htS htIcc
    refine Subtype.ext ?_
    refine ext_inner_right ℝ fun z => ?_
    have h1 : Tendsto (fun n => inner (𝕜 := ℝ) (c n t) z) atTop
        (𝓝 (inner (𝕜 := ℝ) ((v t : L2VF_R3)) z)) := hweak t htIcc z
    have h2 : Tendsto (fun n => inner (𝕜 := ℝ) (c n t) z) atTop
        (𝓝 (inner (𝕜 := ℝ) ((alPkg.u t : L2VF_R3)) z)) := by
      have hw := hweak_at_S t htS htIcc.1 z
      simpa only [real_inner_comm z] using hw
    exact tendsto_nhds_unique h1 h2
  -- endpoint pinning `v 0 = u₀`
  have h0Icc : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_refl 0, hT.le⟩
  have hv0 : v 0 = u₀ := by
    have hck0 : ∀ n, c n 0 = 𝔊.P (alPkg.φ n) (u₀ : L2VF_R3) := by
      intro n
      show ((galSeq (alPkg.φ n)).u 0 : L2VF_R3) = 𝔊.P (alPkg.φ n) (u₀ : L2VF_R3)
      rw [(galSeq (alPkg.φ n)).u_initial]
    have hP0 : Tendsto (fun n => c n 0) atTop (𝓝 (u₀ : L2VF_R3)) := by
      have h := (𝔊.tendsto_id (u₀ : L2VF_R3) u₀.2).comp alPkg.φ_mono.tendsto_atTop
      refine h.congr fun n => ?_
      exact (hck0 n).symm
    refine Subtype.ext ?_
    refine ext_inner_right ℝ fun z => ?_
    have h1 : Tendsto (fun n => inner (𝕜 := ℝ) (c n 0) z) atTop
        (𝓝 (inner (𝕜 := ℝ) ((v 0 : L2VF_R3)) z)) := hweak 0 h0Icc z
    have h2 : Tendsto (fun n => inner (𝕜 := ℝ) (c n 0) z) atTop
        (𝓝 (inner (𝕜 := ℝ) ((u₀ : L2VF_R3)) z)) := hP0.inner tendsto_const_nhds
    exact tendsto_nhds_unique h1 h2
  -- per-Galerkin-test Lipschitz continuity of `v`
  have hlip_v : ∀ w : L2Sigma_R3, IsGalerkinTest_R3 𝔊 w → ∃ L : ℝ, 0 ≤ L ∧
      ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc (0 : ℝ) T,
        |inner (𝕜 := ℝ) ((v t : L2VF_R3)) (w : L2VF_R3)
          - inner (𝕜 := ℝ) ((v s : L2VF_R3)) (w : L2VF_R3)| ≤ L * |t - s| := by
    intro w hw
    obtain ⟨n₀, hn₀⟩ := hw
    have hsdf : IsSchwartzDivFree_R3 w := by
      obtain ⟨ψ, hψ⟩ := 𝔊.range_schwartz n₀ (w : L2VF_R3)
      exact ⟨ψ, fun j => by rw [← hn₀]; exact hψ j⟩
    obtain ⟨L, hL0, hLip⟩ :=
      perTest_lipschitz_R3 ν hν u₀ (fun n => (galSeq n).toSolutionData) w hsdf n₀ hn₀
    refine ⟨L, hL0, fun s hsI t htI => ?_⟩
    have h1 : Tendsto (fun n => inner (𝕜 := ℝ) (c n t) (w : L2VF_R3)
        - inner (𝕜 := ℝ) (c n s) (w : L2VF_R3)) atTop
        (𝓝 (inner (𝕜 := ℝ) ((v t : L2VF_R3)) (w : L2VF_R3)
          - inner (𝕜 := ℝ) ((v s : L2VF_R3)) (w : L2VF_R3))) :=
      (hweak t htI (w : L2VF_R3)).sub (hweak s hsI (w : L2VF_R3))
    refine le_of_tendsto h1.abs ?_
    refine Filter.eventually_atTop.mpr ⟨n₀, fun n hn => ?_⟩
    exact hLip (alPkg.φ n) (le_trans hn (hlevel n))
      s (Set.Icc_subset_Ici_self hsI) t (Set.Icc_subset_Ici_self htI)
  exact ⟨v, hae, hweak, fun t ht => (hvcoe t ht) ▸ hybd t ht, hv0, hlip_v⟩

/-! ### Weak and strong initial traces -/

/-- **Weak initial trace against `u₀`** on ℝ³: `⟪v(t), u₀⟫ → ⟪u₀, u₀⟫` as `t → 0⁺`.

Port of `TorusTraceEnergy.lean:824` (`weak_trace_inner`) with `L2Sigma_R3` / `IsGalerkinTest_R3 𝔊`
/ `𝔊.tendsto_id` replacing the torus counterparts.  The ε/3 argument uses the per-Galerkin-test
Lipschitz continuity `hlip` and density of Galerkin tests via `𝔊.tendsto_id` at `u₀`. -/
theorem weak_trace_inner_R3
    (𝔊 : R3GalerkinScheme) (T : ℝ) (hT : 0 < T) (u₀ : L2Sigma_R3)
    (v : Time → L2Sigma_R3)
    (hbd : ∀ t, t ∈ Set.Icc (0 : ℝ) T → ‖(v t : L2VF_R3)‖ ≤ ‖(u₀ : L2VF_R3)‖)
    (hv0 : v 0 = u₀)
    (hlip : ∀ w : L2Sigma_R3, IsGalerkinTest_R3 𝔊 w → ∃ L : ℝ, 0 ≤ L ∧
      ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc (0 : ℝ) T,
        |inner (𝕜 := ℝ) ((v t : L2VF_R3)) (w : L2VF_R3)
          - inner (𝕜 := ℝ) ((v s : L2VF_R3)) (w : L2VF_R3)| ≤ L * |t - s|) :
    Tendsto (fun t => inner (𝕜 := ℝ) ((v t : L2VF_R3)) (u₀ : L2VF_R3))
      (nhdsWithin 0 (Set.Ici 0))
      (𝓝 (inner (𝕜 := ℝ) ((u₀ : L2VF_R3)) (u₀ : L2VF_R3))) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  set M : ℝ := ‖(u₀ : L2VF_R3)‖ with hMdef
  have hM0 : 0 ≤ M := norm_nonneg _
  -- Galerkin-test approximation of u₀ (density via `𝔊.tendsto_id`).
  obtain ⟨m, hm⟩ := Metric.tendsto_atTop.mp (𝔊.tendsto_id (u₀ : L2VF_R3) u₀.2)
    (ε / (4 * (M + 1))) (by positivity)
  have hdist := hm m (le_refl m)
  rw [dist_eq_norm] at hdist
  have hmem : 𝔊.P m (u₀ : L2VF_R3) ∈ L2Sigma_R3 := 𝔊.preserves_sigma m _ u₀.2
  set w : L2Sigma_R3 := ⟨𝔊.P m (u₀ : L2VF_R3), hmem⟩ with hwdef
  have hwtest : IsGalerkinTest_R3 𝔊 w := ⟨m, 𝔊.idem m _⟩
  obtain ⟨L, hL0, hLipw⟩ := hlip w hwtest
  refine ⟨min (ε / (4 * (L + 1))) T, lt_min (by positivity) hT, ?_⟩
  intro x hx hxd
  have hx0 : (0 : ℝ) ≤ x := hx
  have hxval : dist x 0 = x := by rw [Real.dist_eq, sub_zero, abs_of_nonneg hx0]
  have hxlt : x < ε / (4 * (L + 1)) := by
    rw [hxval] at hxd
    exact lt_of_lt_of_le hxd (min_le_left _ _)
  have hxT : x ∈ Set.Icc (0 : ℝ) T := by
    refine ⟨hx0, ?_⟩
    have := lt_of_lt_of_le (hxval ▸ hxd) (min_le_right (ε / (4 * (L + 1))) T)
    exact this.le
  have h0Icc : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_refl 0, hT.le⟩
  -- approximation bounds
  have hwnorm : ‖(u₀ : L2VF_R3) - (w : L2VF_R3)‖ < ε / (4 * (M + 1)) := by
    rw [hwdef]
    rw [norm_sub_rev] at hdist
    exact hdist
  have hquarter : ∀ t', t' ∈ Set.Icc (0 : ℝ) T →
      |inner (𝕜 := ℝ) ((v t' : L2VF_R3)) ((u₀ : L2VF_R3) - (w : L2VF_R3))| ≤ ε / 4 := by
    intro t' ht'
    have h1 : |inner (𝕜 := ℝ) ((v t' : L2VF_R3)) ((u₀ : L2VF_R3) - (w : L2VF_R3))|
        ≤ M * ‖(u₀ : L2VF_R3) - (w : L2VF_R3)‖ :=
      (abs_real_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_right (hbd t' ht') (norm_nonneg _))
    have h2 : M * ‖(u₀ : L2VF_R3) - (w : L2VF_R3)‖ ≤ M * (ε / (4 * (M + 1))) :=
      mul_le_mul_of_nonneg_left hwnorm.le hM0
    have h3 : M * (ε / (4 * (M + 1))) ≤ ε / 4 := by
      have heq : M * (ε / (4 * (M + 1))) = (M / (M + 1)) * (ε / 4) := by
        field_simp
      have hle1 : M / (M + 1) ≤ 1 := by
        rw [div_le_one (by linarith : (0 : ℝ) < M + 1)]
        linarith
      calc M * (ε / (4 * (M + 1))) = (M / (M + 1)) * (ε / 4) := heq
        _ ≤ 1 * (ε / 4) := mul_le_mul_of_nonneg_right hle1 (by positivity)
        _ = ε / 4 := one_mul _
    linarith
  -- Lipschitz bound at the test `w`
  have hLbound : |inner (𝕜 := ℝ) ((v x : L2VF_R3)) (w : L2VF_R3)
      - inner (𝕜 := ℝ) ((v 0 : L2VF_R3)) (w : L2VF_R3)| ≤ ε / 4 := by
    have h1 := hLipw 0 h0Icc x hxT
    rw [sub_zero, abs_of_nonneg hx0] at h1
    have h2 : L * x ≤ L * (ε / (4 * (L + 1))) := mul_le_mul_of_nonneg_left hxlt.le hL0
    have h3 : L * (ε / (4 * (L + 1))) ≤ ε / 4 := by
      have heq : L * (ε / (4 * (L + 1))) = (L / (L + 1)) * (ε / 4) := by
        field_simp
      have hle1 : L / (L + 1) ≤ 1 := by
        rw [div_le_one (by linarith : (0 : ℝ) < L + 1)]
        linarith
      calc L * (ε / (4 * (L + 1))) = (L / (L + 1)) * (ε / 4) := heq
        _ ≤ 1 * (ε / 4) := mul_le_mul_of_nonneg_right hle1 (by positivity)
        _ = ε / 4 := one_mul _
    linarith
  -- decomposition and assembly
  have hkey : inner (𝕜 := ℝ) ((v x : L2VF_R3)) (u₀ : L2VF_R3)
      - inner (𝕜 := ℝ) ((u₀ : L2VF_R3)) (u₀ : L2VF_R3)
      = inner (𝕜 := ℝ) ((v x : L2VF_R3)) ((u₀ : L2VF_R3) - (w : L2VF_R3))
        + (inner (𝕜 := ℝ) ((v x : L2VF_R3)) (w : L2VF_R3)
          - inner (𝕜 := ℝ) ((v 0 : L2VF_R3)) (w : L2VF_R3))
        - inner (𝕜 := ℝ) ((v 0 : L2VF_R3)) ((u₀ : L2VF_R3) - (w : L2VF_R3)) := by
    rw [hv0, inner_sub_right, inner_sub_right]
    ring
  rw [Real.dist_eq, hkey, hv0]
  have hq1 := hquarter x hxT
  have hq2 := hquarter 0 h0Icc
  rw [hv0] at hLbound hq2
  calc |inner (𝕜 := ℝ) ((v x : L2VF_R3)) ((u₀ : L2VF_R3) - (w : L2VF_R3))
        + (inner (𝕜 := ℝ) ((v x : L2VF_R3)) (w : L2VF_R3)
          - inner (𝕜 := ℝ) ((u₀ : L2VF_R3)) (w : L2VF_R3))
        - inner (𝕜 := ℝ) ((u₀ : L2VF_R3)) ((u₀ : L2VF_R3) - (w : L2VF_R3))|
      ≤ |inner (𝕜 := ℝ) ((v x : L2VF_R3)) ((u₀ : L2VF_R3) - (w : L2VF_R3))
        + (inner (𝕜 := ℝ) ((v x : L2VF_R3)) (w : L2VF_R3)
          - inner (𝕜 := ℝ) ((u₀ : L2VF_R3)) (w : L2VF_R3))|
        + |inner (𝕜 := ℝ) ((u₀ : L2VF_R3)) ((u₀ : L2VF_R3) - (w : L2VF_R3))| := abs_sub _ _
    _ ≤ |inner (𝕜 := ℝ) ((v x : L2VF_R3)) ((u₀ : L2VF_R3) - (w : L2VF_R3))|
        + |inner (𝕜 := ℝ) ((v x : L2VF_R3)) (w : L2VF_R3)
          - inner (𝕜 := ℝ) ((u₀ : L2VF_R3)) (w : L2VF_R3)|
        + |inner (𝕜 := ℝ) ((u₀ : L2VF_R3)) ((u₀ : L2VF_R3) - (w : L2VF_R3))| := by
        have := abs_add_le
          (inner (𝕜 := ℝ) ((v x : L2VF_R3)) ((u₀ : L2VF_R3) - (w : L2VF_R3)))
          (inner (𝕜 := ℝ) ((v x : L2VF_R3)) (w : L2VF_R3)
            - inner (𝕜 := ℝ) ((u₀ : L2VF_R3)) (w : L2VF_R3))
        linarith
    _ < ε := by linarith

/-- **Conjunct (4): strong initial trace** on ℝ³.

Port of `TorusTraceEnergy.lean:935` (`strong_trace_of_props`). The strategy is identical:
`weak_trace_inner_R3` gives `⟪v(t), u₀⟫ → ‖u₀‖²`; together with the uniform bound `‖v(t)‖ ≤ ‖u₀‖`
and the norm expansion `‖v(t) − u₀‖² = ‖v(t)‖² − 2⟪v(t), u₀⟫ + ‖u₀‖² ≤ 2‖u₀‖² − 2⟪v(t), u₀⟫ → 0`,
this yields strong `L²_σ(ℝ³)` convergence.  Density at `u₀` for `hlip` is `𝔊.tendsto_id`. -/
theorem strong_trace_of_props_R3
    (𝔊 : R3GalerkinScheme) (T : ℝ) (hT : 0 < T) (u₀ : L2Sigma_R3)
    (v : Time → L2Sigma_R3)
    (hbd : ∀ t, t ∈ Set.Icc (0 : ℝ) T → ‖(v t : L2VF_R3)‖ ≤ ‖(u₀ : L2VF_R3)‖)
    (hv0 : v 0 = u₀)
    (hlip : ∀ w : L2Sigma_R3, IsGalerkinTest_R3 𝔊 w → ∃ L : ℝ, 0 ≤ L ∧
      ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc (0 : ℝ) T,
        |inner (𝕜 := ℝ) ((v t : L2VF_R3)) (w : L2VF_R3)
          - inner (𝕜 := ℝ) ((v s : L2VF_R3)) (w : L2VF_R3)| ≤ L * |t - s|) :
    Tendsto (fun t => (v t : L2VF_R3)) (nhdsWithin 0 (Set.Ici 0)) (𝓝 (u₀ : L2VF_R3)) := by
  have hinner := weak_trace_inner_R3 𝔊 T hT u₀ v hbd hv0 hlip
  rw [Metric.tendsto_nhdsWithin_nhds] at hinner ⊢
  intro ε hε
  obtain ⟨δ₁, hδ₁, h₁⟩ := hinner (ε ^ 2 / 2) (by positivity)
  refine ⟨min δ₁ T, lt_min hδ₁ hT, ?_⟩
  intro x hx hxd
  have hx0 : (0 : ℝ) ≤ x := hx
  have hxδ₁ : dist x 0 < δ₁ := lt_of_lt_of_le hxd (min_le_left _ _)
  have hxT : x ∈ Set.Icc (0 : ℝ) T := by
    refine ⟨hx0, ?_⟩
    have h := lt_of_lt_of_le hxd (min_le_right δ₁ T)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hx0] at h
    exact h.le
  have hi := h₁ hx hxδ₁
  rw [Real.dist_eq] at hi
  have hself : inner (𝕜 := ℝ) ((u₀ : L2VF_R3)) ((u₀ : L2VF_R3)) = ‖(u₀ : L2VF_R3)‖ ^ 2 :=
    real_inner_self_eq_norm_sq _
  have hlow : ‖(u₀ : L2VF_R3)‖ ^ 2 - ε ^ 2 / 2
      < inner (𝕜 := ℝ) ((v x : L2VF_R3)) ((u₀ : L2VF_R3)) := by
    have habs := abs_lt.mp hi
    rw [hself] at habs
    linarith [habs.1]
  have hnormsq : ‖(v x : L2VF_R3) - (u₀ : L2VF_R3)‖ ^ 2
      = ‖(v x : L2VF_R3)‖ ^ 2 - 2 * inner (𝕜 := ℝ) ((v x : L2VF_R3)) ((u₀ : L2VF_R3))
        + ‖(u₀ : L2VF_R3)‖ ^ 2 := norm_sub_sq_real _ _
  have hbsq : ‖(v x : L2VF_R3)‖ ^ 2 ≤ ‖(u₀ : L2VF_R3)‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (hbd x hxT) 2
  have hsq : ‖(v x : L2VF_R3) - (u₀ : L2VF_R3)‖ ^ 2 < ε ^ 2 := by
    rw [hnormsq]
    linarith
  rw [dist_eq_norm]
  nlinarith [norm_nonneg ((v x : L2VF_R3) - (u₀ : L2VF_R3))]

end LerayHopf
