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
- Level promotion uses `𝔊.mono_range` (`AxiomaticClosure.lean:207`).
- Per-test Stokes bound comes from `negLap` + `range_schwartz` + `stokesTestPairing_abs_le`.
- Density in `L2Sigma_R3` is `𝔊.tendsto_id`.

## Axioms

No new axioms.  Scaffold `sorry` are marked `ALLOW_SORRY: scaffold`.
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

/-- **Per-Galerkin-test equi-Lipschitz bound** on ℝ³.  For a Galerkin test `w` at level `n₀`,
and any Galerkin level `n ≥ n₀`, the scalar pairing curve
`t ↦ ⟪uₙ(t), w⟫` is Lipschitz on `[0,∞)` with constant
`L(w) := ν·Cs(w)·‖u₀‖ + Cb(w)·‖u₀‖²`,
where `Cs(w)` comes from `stokesTestPairing_abs_le` via `range_schwartz` + negLap,
and `Cb(w)` from `F.b_bound`. -/
theorem perTest_lipschitz_R3
    (ν : ℝ) (hν : 0 < ν) (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n)
    (w : L2Sigma_R3) (hw : IsSchwartzDivFree_R3 w) (n₀ : ℕ)
    (hn₀ : 𝔊.P n₀ (w : L2VF_R3) = (w : L2VF_R3)) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ n, n₀ ≤ n → ∀ s ∈ Set.Ici (0 : ℝ), ∀ t ∈ Set.Ici (0 : ℝ),
      |inner (𝕜 := ℝ) (((galSeq n).u t : L2VF_R3)) (w : L2VF_R3)
        - inner (𝕜 := ℝ) (((galSeq n).u s : L2VF_R3)) (w : L2VF_R3)| ≤ L * |t - s| := by
  sorry -- ALLOW_SORRY: scaffold, proved in PR-5 (lean-prover)

/-! ### The weakly-continuous good representative — S5 verbatim -/

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
  sorry -- ALLOW_SORRY: scaffold, proved in PR-5 (lean-prover)

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
  sorry -- ALLOW_SORRY: scaffold, proved in PR-5 (lean-prover)

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
  sorry -- ALLOW_SORRY: scaffold, proved in PR-5 (lean-prover)

end LerayHopf
