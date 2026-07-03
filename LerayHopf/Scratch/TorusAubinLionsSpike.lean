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

-- Single import: `TorusModeCompactness` (T-AL-3 PR #80 + T-AL-4 PR #85) transitively
-- provides everything the remaining statements and wiring need — `TorusGalerkinODESolve`
-- (GalerkinSolutionData, velocityProjection_n, Fourier layer, h1EnergySq/memH1VF),
-- `TorusTestFamily`, and `Bochner.ScalarEquicontinuity`.
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
* **P0.5 + P0.10 + P0.11 (T-AL-4 freeze)** `exists_weak_limit_curve`,
  `integral_sq_proj_tendsto_zero_of_weak`, `exists_limit_curve_of_galSeq`
  — proved in `LerayHopf/TorusModeCompactness.lean` (T-AL-4, PR #85, merged 3be04d5).
-/

/-! ## P0.6 — tail bounds (T-AL-5 leaves)

T-AL-5 GATE (architect, 2026-07-03): all four CONFIRMED AS-FROZEN, verbatim from
Phase-0.  Division of labor between (b) and (c) re-audited at this gate:

* the GALERKIN curves take route (b) — `reg_mem` supplies `memH1VF (u_n t)` at every
  `t` (all-`t` field, no forward restriction needed), so the `h1EnergySq` `tsum` is
  honestly summable and the real-valued domination is sound;
* the LIMIT curve does NOT get (b) — no `memH1VF (u t)` is available (and must NOT be
  smuggled in); it goes through the ENNReal Fatou route (c), where the mode sums are
  well-defined without any summability side condition. -/

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

/-! ## T-AL-5 statement freeze (Step E — tails; architect gate, 2026-07-03)

Frozen statements for the production T-AL-5 PR (recommended NEW file
`LerayHopf/TorusModeTail.lean`, importing `TorusModeCompactness`; `TorusModeCompactness`
is already ~600 lines).  Production targets: the four P0.6 leaves above
(CONFIRMED AS-FROZEN) + the four new statements below (P0.12–P0.15).

Design decisions at this gate:

* **Two composed lemmas, not one** (P0.14 Galerkin-side / P0.15 limit-side): Step F's
  Pythagoras split consumes them at DIFFERENT indices (P0.14 at every `φ n`, P0.15
  once), and P0.14 is also the Fatou input INSIDE P0.15's proof.
* **P0.12** is the `L2Sigma → L2VF` weak-convergence upgrade (the T-AL-4 pre-flag):
  it is what makes P0.6c's `hweak (∀ y : L2VF)` premise reachable from the capstone's
  `L2Sigma`-test conclusion.  Route (anchors re-verified in source):
  `x = lerayProjection x` for `x ∈ L2Sigma` (`lerayProjection_fixes_divFree`,
  `Leray.lean:159`), then `⟪x, y⟫ = ⟪lerayProjection x, y⟫ = ⟪x, lerayProjection y⟫`
  (`lerayProjection_isSymmetric`, `Leray.lean:172`), so the `L2Sigma` test
  `z := lerayProjection y` carries the limit.
* **P0.13** is the ENNReal bridge that makes P0.6c consumable against the REAL-valued
  integrals: `ofReal (‖v − P_N v‖²) =` the ENNReal tail mode sum.  Honesty: the real
  mode tail is genuinely summable for EVERY `v : L2VF` (it is a sub-family of the
  Parseval family — `summable_norm_mFourierCoeff3_sq`, `TorusGalerkinODESolve.lean:1007`
  — so P0.6a + the `ENNReal.ofReal`/`tsum` exchange close it); NO `memH1VF` needed
  here, the H¹ weight never enters.
* **P0.15 takes `hν : 0 < ν`** — used (beyond feeding P0.14) to know the RHS bound is
  nonnegative in the `ENNReal.toReal`/`ofReal` round-trip; P0.14 does NOT take it
  (its chain runs entirely through the `reg_bound` field, sign-blind).
* Forward-only + measure convention: both integrals are `∫ t in (0:ℝ)..T` (reading
  `Ioc 0 T` only, matching `reg_bound` and P0.8's `hint` input); P0.15's measurability
  hypothesis is on `volume.restrict (Icc (0:ℝ) T)`, byte-matching the T-AL-4 capstone
  output. -/

/-- (P0.12) Weak-convergence upgrade `L2Sigma` tests → all `L2VF` tests, via the Leray
projection: for div-free `v n, u`, testing against `y : L2VF` equals testing against
`lerayProjection y ∈ L2Sigma`.  Makes P0.6c's premise reachable from the T-AL-4
capstone's weak-convergence conjunct. -/
theorem tendsto_inner_L2VF_of_tendsto_inner_L2Sigma
    (v : ℕ → L2Sigma) (u : L2Sigma)
    (h : ∀ z : L2Sigma, Tendsto (fun n => inner (𝕜 := ℝ) ((v n : L2VF)) ((z : L2VF)))
      atTop (𝓝 (inner (𝕜 := ℝ) ((u : L2VF)) ((z : L2VF)))))
    (y : L2VF) :
    Tendsto (fun n => inner (𝕜 := ℝ) ((v n : L2VF)) y) atTop
      (𝓝 (inner (𝕜 := ℝ) ((u : L2VF)) y)) := by
  sorry -- ALLOW_SORRY: scratch spike (T-AL-5 statement freeze, P0.12)

/-- (P0.13) ENNReal bridge for the tail identity: valid for EVERY `v : L2VF` (the mode
tail is a sub-family of the always-summable Parseval family; no `memH1VF` needed).
Connects the real integrals of P0.14/P0.15 to P0.6c's ENNReal mode sums. -/
theorem ofReal_tail_sq_eq_tailEnn (N : ℕ) (v : L2VF) :
    ENNReal.ofReal (‖v - velocityProjection_n N v‖ ^ 2) =
      ∑ j : Fin 3, ∑' k : {k : Fin 3 → ℤ // k ∉ fourierBox N},
        ENNReal.ofReal (‖mFourierCoeff3 (L2VF_projComponentC j v) k‖ ^ 2) := by
  sorry -- ALLOW_SORRY: scratch spike (T-AL-5 statement freeze, P0.13)

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
  sorry -- ALLOW_SORRY: scratch spike (T-AL-5 statement freeze, P0.14)

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
    (hub : ∀ t ∈ Icc (0 : ℝ) T, ‖(u t : L2VF)‖ ≤ ‖(u₀ : L2VF)‖)
    (hmeas : AEStronglyMeasurable (fun t => (u t : L2VF))
      (volume.restrict (Icc (0 : ℝ) T)))
    (hweak : ∀ t ∈ Icc (0 : ℝ) T, ∀ z : L2Sigma,
      Tendsto (fun n => inner (𝕜 := ℝ) (((galSeq (φ n)).u t : L2VF)) ((z : L2VF)))
        atTop (𝓝 (inner (𝕜 := ℝ) ((u t : L2VF)) ((z : L2VF)))))
    (N : ℕ) :
    ∫ t in (0 : ℝ)..T,
        ‖(u t : L2VF) - velocityProjection_n N ((u t : L2VF))‖ ^ 2
      ≤ (T * ‖(u₀ : L2VF)‖ ^ 2 + ‖(u₀ : L2VF)‖ ^ 2 / (2 * ν)) / (1 + (N : ℝ) ^ 2) := by
  sorry -- ALLOW_SORRY: scratch spike (T-AL-5 statement freeze, P0.15)

/-- Boundary check (T-AL-5 → T-AL-6): REAL wiring, no sorry of its own.  Consumes the
MERGED production T-AL-4 capstone (fully qualified) + the sorried P0.14/P0.15 above and
produces exactly Step F's raw materials — the Step-D convergence, the n-uniform
Galerkin tail bound along `φ`, and the limit tail bound — verifying the hypothesis
shapes compose across the PR boundary. -/
example
    (F : Torus3NSForms) (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T)
    (u₀ : L2Sigma) (galSeq : ∀ n, GalerkinSolutionData F ν u₀ n) :
    ∃ (φ : ℕ → ℕ) (u : Time → L2Sigma), StrictMono φ ∧
      (∀ N : ℕ, Tendsto (fun n => ∫ t in (0 : ℝ)..T,
          ‖velocityProjection_n N (((galSeq (φ n)).u t : L2VF)) -
            velocityProjection_n N ((u t : L2VF))‖ ^ 2) atTop (𝓝 0)) ∧
      (∀ n N : ℕ, ∫ t in (0 : ℝ)..T,
          ‖((galSeq (φ n)).u t : L2VF) -
            velocityProjection_n N (((galSeq (φ n)).u t : L2VF))‖ ^ 2
        ≤ (T * ‖(u₀ : L2VF)‖ ^ 2 + ‖(u₀ : L2VF)‖ ^ 2 / (2 * ν)) / (1 + (N : ℝ) ^ 2)) ∧
      (∀ N : ℕ, ∫ t in (0 : ℝ)..T,
          ‖(u t : L2VF) - velocityProjection_n N ((u t : L2VF))‖ ^ 2
        ≤ (T * ‖(u₀ : L2VF)‖ ^ 2 + ‖(u₀ : L2VF)‖ ^ 2 / (2 * ν)) / (1 + (N : ℝ) ^ 2)) := by
  obtain ⟨φ, u, hφ, hweak, hub, hmeas, hD⟩ :=
    _root_.LerayHopf.exists_limit_curve_of_galSeq F ν hν T hT u₀ galSeq
  exact ⟨φ, u, hφ, hD,
    fun n N => integral_tail_sq_galerkin_le F ν u₀ (φ n) (galSeq (φ n)) T hT N,
    fun N => integral_tail_sq_limit_le F ν hν T hT u₀ galSeq φ u hub hmeas hweak N⟩

end Scratch
end LerayHopf
