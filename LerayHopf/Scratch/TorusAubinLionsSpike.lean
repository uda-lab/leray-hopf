-- SCRATCH: Phase-0 spike for the torus `aubin_lions` mode-wise campaign.
-- NOT for merge into the default build (not imported by `LerayHopf.lean`).
-- Purpose: pressure-test EVERY statement of docs/scratch/torus-aubinlions-modewise-plan.md
-- §2 (P0.1–P0.8) against the real interfaces, per doctrine D2 (all conjuncts).
-- Each `sorry` here is a scratch placeholder for a statement whose PROVABILITY is
-- argued in the plan doc; the spike's job is that the statements TYPECHECK as stated.
import LerayHopf.TorusGalerkinODESolve
-- T-AL-3 section: the merged T-AL-2 engine (`exists_uniform_subseq_of_lipschitz_family`),
-- imported so the composed-capstone WIRING is verified for real, not just statement-typed.
import LerayHopf.Bochner.ScalarEquicontinuity

open MeasureTheory Filter Topology Set

namespace LerayHopf
namespace Scratch

/-! ## P0.2 (S1) — stokes pairing bound for band-limited tests

`stokesTestPairing u w` (`AxiomaticClosure.lean:104`) is the mode sum
`∑_j ∑'_k (2π)²|k|² Re(û_j(k)·conj(ŵ_j(k)))`; for a Galerkin test `w` the `k`-sum is a
finite `fourierBox` sum (`coeff_zero_outside_box`), so finite Cauchy–Schwarz gives the
`C(w)·‖u‖` bound. -/

theorem stokesTestPairing_bound_of_galerkinTest (w : L2Sigma) (hw : IsGalerkinTest w) :
    ∃ C : ℝ, ∀ u : L2VF, |stokesTestPairing u (w : L2VF)| ≤ C * ‖u‖ := by
  sorry -- ALLOW_SORRY: scratch spike (Phase-0, torus-aubinlions-modewise-plan §2 P0.2)

/-! ## P0.1 (S2) — the countable band-limited div-free test family

Design (plan §1 Step B/C): a countable family of Galerkin tests that finitely SPANS each
finite-dimensional `velocitySpan N` (that is enough for the finite-dim weak→strong step
and for continuity of `t ↦ P_N (u t)`; an orthonormal basis is not required).
Density in `L2Sigma` then follows from `velocityProjection_n_tendsto` +
`velocityProjection_n_preserves_L2Sigma` (each `P_N u ∈ velocitySpan N`). -/

theorem exists_galerkin_test_family :
    ∃ w : ℕ → L2Sigma,
      (∀ m, IsGalerkinTest (w m)) ∧
      ∀ N : ℕ, ∃ s : Finset ℕ,
        velocitySpan N ≤ Submodule.span ℝ ((fun m => ((w m : L2Sigma) : L2VF)) '' ↑s) := by
  sorry -- ALLOW_SORRY: scratch spike (Phase-0, torus-aubinlions-modewise-plan §2 P0.1)

/-! ## P0.3 — equi-Lipschitz bound for the test pairings

From `u_ode` (fires for `n ≥ m` by `velocityProjection_n_eq_of_le`), `u_hasDeriv` +
`HasDerivAt.inner`, `energy_bound`, P0.2, and `Torus3NSForms.b_bound`. Forward-only
(`0 ≤ s ≤ t`), matching the solution data's time domain. -/

theorem galerkin_test_pairing_lipschitz
    (F : Torus3NSForms) (ν : ℝ) (hν : 0 < ν) (u₀ : L2Sigma)
    (galSeq : ∀ n, GalerkinSolutionData F ν u₀ n)
    (w : L2Sigma) (m : ℕ) (hw : velocityProjection_n m (w : L2VF) = (w : L2VF)) :
    ∃ L : ℝ, ∀ n, m ≤ n → ∀ s t : ℝ, 0 ≤ s → s ≤ t →
      |inner (𝕜 := ℝ) (((galSeq n).u t : L2VF)) ((w : L2VF)) -
        inner (𝕜 := ℝ) (((galSeq n).u s : L2VF)) ((w : L2VF))| ≤ L * (t - s) := by
  sorry -- ALLOW_SORRY: scratch spike (Phase-0, torus-aubinlions-modewise-plan §2 P0.3)

/-! ## P0.4 (S3) — the scalar compactness engine (domain-neutral)

GRADUATED to production: `LerayHopf.exists_uniform_subseq_of_lipschitz_family`,
proved sorry-free in `LerayHopf/Bochner/ScalarEquicontinuity.lean` (T-AL-2, PR #79,
merged 85079d4) with the eventual-Lipschitz `hlip` (codex P2 on PR #77) intact.
The Phase-0 placeholder that used to live here has been DELETED (codex P3 on PR #80):
keeping a same-name sorried twin inside `namespace Scratch` silently SHADOWED the
merged engine in the T-AL-3 capstone wiring below, so the spike's "wiring verified"
claim was anchored to the placeholder rather than the production interface.  The
capstone now calls the merged engine fully qualified (`_root_.LerayHopf.…`). -/

/-! ## P0.5 (S4) — Riesz limit curve from uniformly convergent test pairings

Conclusions: weak convergence at EVERY `t ∈ [0,T]` (against `L2Sigma` tests — the
`L2VF` upgrade goes through `lerayProjection` later), the `‖u₀‖`-ball bound, and strong
measurability (pointwise limit of the continuous finite-dimensional curves
`t ↦ P_N (u t)`, whose coordinates are uniform limits of continuous pairings). -/

theorem exists_weak_limit_curve
    (T : ℝ) (hT : 0 < T) (M : ℝ)
    (v : ℕ → ℝ → L2Sigma)
    (hb : ∀ n t, t ∈ Icc (0 : ℝ) T → ‖(v n t : L2VF)‖ ≤ M)
    (hcont : ∀ n, ContinuousOn (fun t => (v n t : L2VF)) (Icc (0 : ℝ) T))
    (w : ℕ → L2Sigma) (hwtest : ∀ m, IsGalerkinTest (w m))
    (hspan : ∀ N : ℕ, ∃ s : Finset ℕ,
      velocitySpan N ≤ Submodule.span ℝ ((fun m => ((w m : L2Sigma) : L2VF)) '' ↑s))
    (g : ℕ → ℝ → ℝ)
    (hconv : ∀ m, TendstoUniformlyOn
      (fun n t => inner (𝕜 := ℝ) ((v n t : L2VF)) ((w m : L2VF))) (g m) atTop
      (Icc (0 : ℝ) T)) :
    ∃ u : Time → L2Sigma,
      (∀ t ∈ Icc (0 : ℝ) T, ∀ z : L2Sigma,
        Tendsto (fun n => inner (𝕜 := ℝ) ((v n t : L2VF)) ((z : L2VF))) atTop
          (𝓝 (inner (𝕜 := ℝ) ((u t : L2VF)) ((z : L2VF))))) ∧
      (∀ t ∈ Icc (0 : ℝ) T, ‖(u t : L2VF)‖ ≤ M) ∧
      AEStronglyMeasurable (fun t => (u t : L2VF)) (volume.restrict (Icc (0 : ℝ) T)) := by
  sorry -- ALLOW_SORRY: scratch spike (Phase-0, torus-aubinlions-modewise-plan §2 P0.5)

/-! ## P0.6 — tail bounds -/

/-- (a) Vector tail identity: Pythagoras + componentwise
`L2C_norm_sub_fourierProjection_sq` through `L2VF_norm_sq_eq_sum_componentC`
(`TorusGalerkinODESolve.lean:898`, `LerayHopf.Torus` namespace) +
`velocityProjection_n_component_comm`. -/
theorem L2VF_norm_sub_velocityProjection_sq (N : ℕ) (u : L2VF) :
    ‖u - velocityProjection_n N u‖ ^ 2 =
      ∑ j : Fin 3, ∑' k : {k : Fin 3 → ℤ // k ∉ fourierBox N},
        ‖mFourierCoeff3 (L2VF_projComponentC j u) k‖ ^ 2 := by
  sorry -- ALLOW_SORRY: scratch spike (Phase-0, torus-aubinlions-modewise-plan §2 P0.6a)

/-- (b) H¹ domination of the tail, for H¹ fields (the Galerkin curves: `reg_mem`).
The `memH1VF` hypothesis supplies the summability that keeps `h1EnergySq`'s `tsum`
honest (no junk-0 collapse); the LIMIT curve does NOT get this lemma — it goes through
the ENNReal Fatou route (c). -/
theorem tail_sq_le_h1EnergySq_div (N : ℕ) (u : L2VF) (hu : memH1VF u) :
    ‖u - velocityProjection_n N u‖ ^ 2 ≤ h1EnergySq u / (1 + (N : ℝ) ^ 2) := by
  sorry -- ALLOW_SORRY: scratch spike (Phase-0, torus-aubinlions-modewise-plan §2 P0.6b)

/-- (b′) Integrability side condition to consume `reg_bound` soundly: for a Galerkin
curve (band-limited at level `n`), `t ↦ h1EnergySq (u_n t)` is continuous on `[0,∞)`
(finite `fourierBox` sum of squared moduli of continuous coefficient functions). -/
theorem h1EnergySq_continuousOn_galerkin
    (F : Torus3NSForms) (ν : ℝ) (u₀ : L2Sigma) (n : ℕ)
    (D : GalerkinSolutionData F ν u₀ n) :
    ContinuousOn (fun t => h1EnergySq ((D.u t : L2VF))) (Ici (0 : ℝ)) := by
  sorry -- ALLOW_SORRY: scratch spike (Phase-0, torus-aubinlions-modewise-plan §2 P0.6b')

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
  sorry -- ALLOW_SORRY: scratch spike (Phase-0, torus-aubinlions-modewise-plan §2 P0.6c)

/-! ## P0.8 — `∫₀ᵀ ‖·‖² → 0` ⇒ `eLpNorm → 0` conversion (field 4's exact shape) -/

theorem eLpNorm_tendsto_of_integral_sq_tendsto
    (T : ℝ) (hT : 0 < T) (M : ℝ) (f : ℕ → ℝ → L2VF)
    (hmeas : ∀ n, AEStronglyMeasurable (f n) (volume.restrict (Icc (0 : ℝ) T)))
    (hb : ∀ n t, t ∈ Icc (0 : ℝ) T → ‖f n t‖ ≤ M)
    (hint : Tendsto (fun n => ∫ t in (0 : ℝ)..T, ‖f n t‖ ^ 2) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (f n) 2 (volume.restrict (Icc (0 : ℝ) T))) atTop
      (𝓝 0) := by
  sorry -- ALLOW_SORRY: scratch spike (Phase-0, torus-aubinlions-modewise-plan §2 P0.8)

/-! ## P0.7 — the conclusion-shape dry run (ALL FIVE fields)

Binder list is byte-identical to `axiom aubin_lions` (`AxiomaticClosure.lean:376`),
including the `spatial` hypothesis (kept for a no-drama consumer rewire even though the
mode-wise proof does not use it). `Type`-valued, so a `noncomputable def`. -/

noncomputable def torusAubinLionsPackage_of_galSeq
    (F : Torus3NSForms) (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T)
    (u₀ : L2Sigma)
    (galSeq : ∀ n, GalerkinSolutionData F ν u₀ n)
    (spatial : ∀ (M : ℝ) (z : ℕ → L2VF),
      (∀ n, z n ∈ L2Sigma) →
      (∀ n, memH1VF (z n)) →
      (∀ n, h1EnergySq (z n) ≤ M ^ 2) →
      ∃ (ψ : ℕ → ℕ) (g : L2VF), StrictMono ψ ∧ g ∈ L2Sigma ∧
        Filter.Tendsto (fun n => z (ψ n)) Filter.atTop (nhds g)) :
    AubinLionsPackage F ν T u₀ galSeq := by
  sorry -- ALLOW_SORRY: scratch spike (Phase-0, torus-aubinlions-modewise-plan §2 P0.7)

/-! ## T-AL-3 statement freeze (Step A+B wiring; architect gate, 2026-07-03)

Frozen statements for the production file `LerayHopf/TorusModeCompactness.lean`
(plan §3 row T-AL-3).  P0.3 above (`galerkin_test_pairing_lipschitz`) is CONFIRMED
as-frozen: its `0 ≤ s → s ≤ t` time domain is exactly what the engine's `hlip`
needs (Icc-membership supplies `0 ≤ s`), and its `m ≤ n` cutoff is the engine's
eventual-`n₀` (flag d: do NOT strengthen to all-`n`).

The capstone `exists_galerkin_modewise_extraction` below carries a REAL wiring
body (engine application + choice packaging), so the T-AL-3 assembly is verified
end-to-end in this spike; only the three leaf lemmas (P0.3, P0.9a, P0.9b) remain
for `lean-prover` in the production PR. -/

/-- (P0.9a) Continuity export [architect flag (a)]: the Galerkin curve is
norm-continuous on `[0,∞)`.  From `u_hasDeriv`: each forward time `t ≥ 0` has a
genuine `HasDerivAt` (full-neighborhood), hence `ContinuousAt`, hence
`ContinuousOn` on `Ici 0` via `ContinuousAt.continuousWithinAt`.  P0.5's `hcont`
is the `.mono Icc_subset_Ici_self` restriction to `Icc 0 T`. -/
theorem galerkin_u_continuousOn
    (F : Torus3NSForms) (ν : ℝ) (u₀ : L2Sigma) (n : ℕ)
    (D : GalerkinSolutionData F ν u₀ n) :
    ContinuousOn (fun t => (D.u t : L2VF)) (Ici (0 : ℝ)) := by
  sorry -- ALLOW_SORRY: scratch spike (T-AL-3 statement freeze, P0.9a)

/-- (P0.9b) Ball-bound export [architect flag (c)]: uniform n-independent bound
`‖u_n(t)‖ ≤ ‖u₀‖` for forward times, from `energy_bound` +
`Torus.velocityProjection_n_norm_le`.  P0.5's `hb` instantiates
`M := ‖(u₀ : L2VF)‖`. -/
theorem galerkin_u_norm_le
    (F : Torus3NSForms) (ν : ℝ) (u₀ : L2Sigma) (n : ℕ)
    (D : GalerkinSolutionData F ν u₀ n) :
    ∀ t : ℝ, 0 ≤ t → ‖(D.u t : L2VF)‖ ≤ ‖(u₀ : L2VF)‖ := by
  sorry -- ALLOW_SORRY: scratch spike (T-AL-3 statement freeze, P0.9b)

/-- (P0.9c) T-AL-3 capstone [architect flags (b)+(d)]: ONE strictly monotone
extraction `φ` and ONE packaged limit function `g : ℕ → ℝ → ℝ` such that every
test pairing `t ↦ ⟪u_{φ(n)}(t), w m⟫` converges uniformly on `[0,T]` to `g m`.
The conclusion is in the reindexed single-`g` form that drops verbatim into
P0.5 `exists_weak_limit_curve`'s `hconv` with `v := fun n => (galSeq (φ n)).u`.

The body below is the REAL wiring (not a placeholder): Classical band-limit
cutoffs from `IsGalerkinTest`, P0.3 Lipschitz constants, `B m = ‖u₀‖·‖w m‖`
via P0.9b + Cauchy–Schwarz, then the T-AL-2 engine + `choose`. -/
theorem exists_galerkin_modewise_extraction
    (F : Torus3NSForms) (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T)
    (u₀ : L2Sigma) (galSeq : ∀ n, GalerkinSolutionData F ν u₀ n)
    (w : ℕ → L2Sigma) (hwtest : ∀ m, IsGalerkinTest (w m)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : ℕ → ℝ → ℝ, ∀ m,
      TendstoUniformlyOn
        (fun n t => inner (𝕜 := ℝ) (((galSeq (φ n)).u t : L2VF)) ((w m : L2VF)))
        (g m) atTop (Icc (0 : ℝ) T) := by
  classical
  -- Per-test band-limit cutoff from `IsGalerkinTest` (flag d: the engine's `n₀ m`).
  have hcut : ∀ m, velocityProjection_n (Classical.choose (hwtest m)) ((w m : L2Sigma) : L2VF)
      = ((w m : L2Sigma) : L2VF) := fun m => Classical.choose_spec (hwtest m)
  -- Per-test Lipschitz constants from P0.3 (fires for `n` past the cutoff).
  choose L hL using fun m =>
    galerkin_test_pairing_lipschitz F ν hν u₀ galSeq (w m) (Classical.choose (hwtest m)) (hcut m)
  -- The MERGED T-AL-2 engine over `f m n t := ⟪u_n(t), w m⟫` — fully qualified so the
  -- wiring is checked against the production interface, never a Scratch shadow
  -- (codex P3 on PR #80).
  obtain ⟨φ, hφ, hconv⟩ := _root_.LerayHopf.exists_uniform_subseq_of_lipschitz_family T hT
    (fun m n t => inner (𝕜 := ℝ) (((galSeq n).u t : L2VF)) ((w m : L2VF)))
    (fun m => ‖(u₀ : L2VF)‖ * ‖((w m : L2Sigma) : L2VF)‖) L
    (fun m n t ht =>
      -- uniform bound: Cauchy–Schwarz + P0.9b (forward time from `ht.1`)
      le_trans (abs_real_inner_le_norm _ _)
        (mul_le_mul_of_nonneg_right (galerkin_u_norm_le F ν u₀ n (galSeq n) t ht.1)
          (norm_nonneg _)))
    (fun m => ⟨Classical.choose (hwtest m), fun n hn s t hs ht hst =>
      hL m n hn s t hs.1 hst⟩)
  -- Package the per-`m` limits into a single function (flag b).
  choose g hg using hconv
  exact ⟨φ, hφ, g, hg⟩

end Scratch
end LerayHopf
