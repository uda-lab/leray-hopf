-- SCRATCH: Phase-0 spike for the torus `aubin_lions` mode-wise campaign.
-- NOT for merge into the default build (not imported by `LerayHopf.lean`).
-- Purpose: pressure-test EVERY statement of docs/scratch/torus-aubinlions-modewise-plan.md
-- §2 (P0.1–P0.8) against the real interfaces, per doctrine D2 (all conjuncts).
-- Each `sorry` here is a scratch placeholder for a statement whose PROVABILITY is
-- argued in the plan doc; the spike's job is that the statements TYPECHECK as stated.
--
-- GRADUATION POLICY (codex P3 on PR #80, generalized): once a spike statement lands
-- proved in production, its Scratch placeholder is DELETED here and replaced by a note.
-- A same-name sorried twin inside `namespace Scratch` silently SHADOWS the production
-- theorem in later wiring bodies, so keeping it would anchor "wiring verified" claims
-- to placeholders instead of the real interfaces.  Wiring bodies additionally call
-- production theorems fully qualified (`_root_.LerayHopf.…`) as a second guard.

-- Single import: `TorusModeCompactness` (T-AL-3, merged PR #80) transitively provides
-- everything the remaining statements and wiring need — `TorusGalerkinODESolve`
-- (GalerkinSolutionData, velocityProjection_n, Fourier layer), `TorusTestFamily`
-- (exists_galerkin_test_family), and `Bochner.ScalarEquicontinuity` (T-AL-2 engine).
import LerayHopf.TorusModeCompactness

open MeasureTheory Filter Topology Set

namespace LerayHopf
namespace Scratch

/-! ## GRADUATED sections (placeholders deleted; see graduation policy in the header)

* **P0.2 (S1)** `stokesTestPairing_bound_of_galerkinTest` — proved in
  `LerayHopf/TorusTestFamily.lean` (T-AL-1, PR #78, merged 7e77c79).
* **P0.1 (S2)** `exists_galerkin_test_family` — proved in
  `LerayHopf/TorusTestFamily.lean` (T-AL-1, PR #78, merged 7e77c79).
* **P0.4 (S3)** `exists_uniform_subseq_of_lipschitz_family` — proved in
  `LerayHopf/Bochner/ScalarEquicontinuity.lean` (T-AL-2, PR #79, merged 85079d4),
  eventual-Lipschitz `hlip` (codex P2 on PR #77) intact.
* **P0.3 + P0.9a/b/c (T-AL-3 freeze)** `galerkin_test_pairing_lipschitz`,
  `galerkin_u_continuousOn`, `galerkin_u_norm_le`, `exists_galerkin_modewise_extraction`
  — proved in `LerayHopf/TorusModeCompactness.lean` (T-AL-3, PR #80, merged e7c8a9c).
-/

/-! ## P0.5 (S4) — Riesz limit curve from uniformly convergent test pairings

Conclusions: weak convergence at EVERY `t ∈ [0,T]` (against `L2Sigma` tests — the
`L2VF` upgrade goes through `lerayProjection` later), the `‖u₀‖`-ball bound, and strong
measurability (pointwise limit of the continuous finite-dimensional curves
`t ↦ P_N (u t)`, whose coordinates are uniform limits of continuous pairings).

T-AL-4 GATE (architect, 2026-07-03): CONFIRMED AS-FROZEN — this is the production
Step-C statement, verbatim.  The instantiation with the merged T-AL-1/T-AL-3 outputs
type-composes; see the `exists_limit_curve_of_galSeq` wiring below. -/

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

/-! ## T-AL-4 statement freeze (Step C+D; architect gate, 2026-07-03)

Frozen statements for the production file `LerayHopf/TorusModeCompactness.lean`
(plan §3 row T-AL-4, the soundness-critical node).  Three production targets:

1. **P0.5 `exists_weak_limit_curve` (Step C)** — CONFIRMED AS-FROZEN, verbatim from
   Phase-0 (above).  Soundness audit at this gate:
   * ∀t-vs-a.e.: the weak-convergence conclusion is at EVERY `t ∈ Icc 0 T` — required
     (Step D's DCT needs pointwise convergence at each `t`); do NOT weaken to a.e.
   * `AEStronglyMeasurable` is honestly reachable: each `t ↦ ⟪u t, w m⟫ = g m t` is a
     uniform limit of continuous pairings, hence continuous; `t ↦ P_N (u t)` is then a
     continuous finite-dim curve (spanning finsets from `hspan` + `velocityProjection_n`
     CLM), and `u t = lim_N P_N (u t)` pointwise (`velocityProjection_n_tendsto`), so
     `u` is an a.e.- (in fact everywhere-) pointwise limit of continuous curves on
     `Icc 0 T` — `aestronglyMeasurable_of_tendsto_ae` shape.  Nothing smuggled.
   * Forward-only: every conclusion reads `u` on `Icc 0 T` only; `u : Time → L2Sigma`
     is junk outside `[0,T]` by design.
   * Measure: `volume.restrict (Icc (0:ℝ) T)` — matches the package field 5 verbatim.

2. **P0.10 Step D** (`integral_sq_proj_tendsto_zero_of_weak`): finite-dim strong part.
   Route (verified interfaces): `velocityProjection_n` is a CLM
   (`VelocityGalerkin.lean:86`); self-adjointness `velocityProjection_n_inner_symm` +
   `velocityProjection_n_inner_of_fixed` (`TorusProjectionAdjoint.lean:85,99`) turn
   weak convergence against `L2Sigma` tests into coordinate convergence on the
   finite-dimensional `velocitySpan N` (`velocitySpan_finiteDimensional`,
   `velocitySpan_le_sigma`); finite-dim Parseval gives
   `‖P_N(v n t) − P_N(u t)‖ → 0` at every `t ∈ Icc 0 T`, dominated by `(2M)²`; DCT in
   `t` (integrand AESM via the CLM composition; the interval integral reads only
   `Ioc 0 T ⊆ Icc 0 T`, so `u` is never read outside `[0,T]`).
   The interval-integral conclusion shape matches P0.8's `hint` input verbatim
   (Step F consumes it through the Pythagoras split).

3. **P0.11 capstone** (`exists_limit_curve_of_galSeq`): the single clean handle for
   T-AL-5/6 — extraction ∘ Step C ∘ Step D over `galSeq`, ball constant explicit
   (`M = ‖u₀‖`).  Weak convergence is stated against `L2Sigma` tests; the `L2VF`
   upgrade for the Step-E tail Fatou goes through `lerayProjection_isSymmetric` +
   `lerayProjection_fixes_divFree` (`Leray.lean:172,159` — verified present) and is
   T-AL-5's first lemma, NOT re-stated here.
   Package-field coverage check (all five): φ ✓, φ_mono ✓, u ✓,
   u_aestronglyMeasurable ✓ (conjunct 4, byte-matching measure), strong_convergence
   reachable = conjunct 5 (Step D, ∀N) + P0.6 tails (T-AL-5) + P0.8 (T-AL-6).

The capstone body below is the REAL wiring against the MERGED production theorems
(fully qualified), so the T-AL-4 assembly and the P0.5 instantiation are verified
end-to-end; the prover work in the production PR is exactly P0.5 and P0.10. -/

/-- (P0.10) Step D — finite-dim strong part.  Weak convergence at every `t ∈ [0,T]`
plus uniform ball bounds give strong convergence of the level-`N` projections in
`L²(0,T)`: coordinates against the finite-dimensional `velocitySpan N` converge
pointwise (projection self-adjointness), `‖P_N(v n t − u t)‖ ≤ 2M` dominates, DCT.
Conclusion shape = P0.8's `hint` input (interval integral over `0..T`). -/
theorem integral_sq_proj_tendsto_zero_of_weak
    (T : ℝ) (hT : 0 < T) (M : ℝ) (N : ℕ)
    (v : ℕ → ℝ → L2Sigma) (u : ℝ → L2Sigma)
    (hb : ∀ n t, t ∈ Icc (0 : ℝ) T → ‖(v n t : L2VF)‖ ≤ M)
    (hub : ∀ t ∈ Icc (0 : ℝ) T, ‖(u t : L2VF)‖ ≤ M)
    (hmeas_v : ∀ n, AEStronglyMeasurable (fun t => (v n t : L2VF))
      (volume.restrict (Icc (0 : ℝ) T)))
    (hmeas_u : AEStronglyMeasurable (fun t => (u t : L2VF))
      (volume.restrict (Icc (0 : ℝ) T)))
    (hweak : ∀ t ∈ Icc (0 : ℝ) T, ∀ z : L2Sigma,
      Tendsto (fun n => inner (𝕜 := ℝ) ((v n t : L2VF)) ((z : L2VF))) atTop
        (𝓝 (inner (𝕜 := ℝ) ((u t : L2VF)) ((z : L2VF))))) :
    Tendsto (fun n => ∫ t in (0 : ℝ)..T,
        ‖velocityProjection_n N ((v n t : L2VF)) -
          velocityProjection_n N ((u t : L2VF))‖ ^ 2)
      atTop (𝓝 0) := by
  sorry -- ALLOW_SORRY: scratch spike (T-AL-4 statement freeze, P0.10 Step D)

/-- (P0.11) T-AL-4 capstone: extraction + limit curve for `galSeq`, the clean handle
for T-AL-5/6.  Conjuncts: strict monotonicity, weak convergence at EVERY `t ∈ [0,T]`
against `L2Sigma` tests, the explicit `‖u₀‖`-ball bound, AE strong measurability
(package field 5, byte-matching measure), and the Step-D finite-dim strong part for
every level `N`.

The body is the REAL wiring against the merged T-AL-1/T-AL-3 production theorems
(fully qualified) + the sorried P0.5/P0.10 above — it verifies that the P0.5
instantiation with the production outputs type-composes exactly as claimed. -/
theorem exists_limit_curve_of_galSeq
    (F : Torus3NSForms) (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T)
    (u₀ : L2Sigma) (galSeq : ∀ n, GalerkinSolutionData F ν u₀ n) :
    ∃ (φ : ℕ → ℕ) (u : Time → L2Sigma), StrictMono φ ∧
      (∀ t ∈ Icc (0 : ℝ) T, ∀ z : L2Sigma,
        Tendsto (fun n => inner (𝕜 := ℝ) (((galSeq (φ n)).u t : L2VF)) ((z : L2VF)))
          atTop (𝓝 (inner (𝕜 := ℝ) ((u t : L2VF)) ((z : L2VF))))) ∧
      (∀ t ∈ Icc (0 : ℝ) T, ‖(u t : L2VF)‖ ≤ ‖(u₀ : L2VF)‖) ∧
      AEStronglyMeasurable (fun t => (u t : L2VF)) (volume.restrict (Icc (0 : ℝ) T)) ∧
      ∀ N : ℕ, Tendsto (fun n => ∫ t in (0 : ℝ)..T,
          ‖velocityProjection_n N (((galSeq (φ n)).u t : L2VF)) -
            velocityProjection_n N ((u t : L2VF))‖ ^ 2)
        atTop (𝓝 0) := by
  classical
  -- T-AL-1: the countable spanning Galerkin test family (production, fully qualified).
  obtain ⟨w, hwtest, hspan⟩ := _root_.LerayHopf.exists_galerkin_test_family
  -- T-AL-3: the mode-wise extraction over that family (production, fully qualified).
  obtain ⟨φ, hφ, g, hconv⟩ :=
    _root_.LerayHopf.exists_galerkin_modewise_extraction F ν hν T hT u₀ galSeq w hwtest
  -- T-AL-3 exports: ball bound (flag c) and continuity (flag a) for the reindexed curves.
  have hb : ∀ n t, t ∈ Icc (0 : ℝ) T → ‖((galSeq (φ n)).u t : L2VF)‖ ≤ ‖(u₀ : L2VF)‖ :=
    fun n t ht => _root_.LerayHopf.galerkin_u_norm_le F ν u₀ (φ n) (galSeq (φ n)) t ht.1
  have hcont : ∀ n, ContinuousOn (fun t => ((galSeq (φ n)).u t : L2VF)) (Icc (0 : ℝ) T) :=
    fun n => (_root_.LerayHopf.galerkin_u_continuousOn F ν u₀ (φ n) (galSeq (φ n))).mono
      Icc_subset_Ici_self
  -- Step C: P0.5 instantiated with the T-AL-3 outputs (the composition under test).
  obtain ⟨u, hweak, hub, hmeas⟩ := exists_weak_limit_curve T hT (‖(u₀ : L2VF)‖)
    (fun n => (galSeq (φ n)).u) hb hcont w hwtest hspan g hconv
  refine ⟨φ, u, hφ, hweak, hub, hmeas, fun N => ?_⟩
  -- Step D: P0.10 at level N (v-measurability from continuity on the compact Icc).
  exact integral_sq_proj_tendsto_zero_of_weak T hT (‖(u₀ : L2VF)‖) N
    (fun n => (galSeq (φ n)).u) u hb hub
    (fun n => (hcont n).aestronglyMeasurable measurableSet_Icc) hmeas hweak

end Scratch
end LerayHopf
