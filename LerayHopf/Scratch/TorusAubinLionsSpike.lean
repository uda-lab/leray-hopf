-- SCRATCH: Phase-0 spike for the torus `aubin_lions` mode-wise campaign.
-- NOT for merge into the default build (not imported by `LerayHopf.lean`).
-- Purpose: pressure-test EVERY statement of docs/scratch/torus-aubinlions-modewise-plan.md
-- §2 (P0.1–P0.8) against the real interfaces, per doctrine D2 (all conjuncts).
-- Each `sorry` here is a scratch placeholder for a statement whose PROVABILITY is
-- argued in the plan doc; the spike's job is that the statements TYPECHECK as stated.
--
-- ANTI-SHADOWING RULES (codex P3 on PR #80 and AGAIN on PR #88 — same class twice;
-- these rules are now binding for every future gate, including T-AL-6):
--
-- 1. GRADUATION IS ATOMIC: the moment a spike statement lands proved in production,
--    its Scratch placeholder is DELETED here (replaced by a note) and every spike
--    caller of that name is re-pointed at `_root_.LerayHopf.<name>` — in the SAME
--    edit.  A same-name sorried twin inside `namespace Scratch` silently SHADOWS the
--    production theorem, so any wiring/boundary check that still calls it unqualified
--    is verifying against a placeholder while claiming to verify against production.
-- 2. WIRING BODIES QUALIFY PRODUCTION CALLS: every call intended to hit a merged
--    production theorem is written `_root_.LerayHopf.<name>`, never unqualified.
--    Unqualified calls are permitted ONLY for same-gate freeze placeholders that do
--    not yet exist in production — and rule 1 retires them at graduation.
-- 3. GRADUATION AUDIT: after each production merge, grep this file for every
--    graduated name; every remaining occurrence must be `_root_`-qualified or gone.

-- Single import: `TorusModeTail` (T-AL-5, PR #88) transitively provides the whole
-- campaign chain — `TorusModeCompactness` (T-AL-3 PR #80 + T-AL-4 PR #85), which
-- itself pulls `TorusGalerkinODESolve`, `TorusTestFamily`, and
-- `Bochner.ScalarEquicontinuity`.
import LerayHopf.TorusModeTail

open MeasureTheory Filter Topology Set

namespace LerayHopf
namespace Scratch

/-! ## GRADUATED sections (placeholders deleted; see anti-shadowing rules in header)

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
* **P0.6a/b/b′/c + P0.12–P0.15 (T-AL-5 freeze)** `L2VF_norm_sub_velocityProjection_sq`,
  `tail_sq_le_h1EnergySq_div`, `h1EnergySq_continuousOn_galerkin`, `tailEnn_lsc_of_weak`,
  `tendsto_inner_L2VF_of_tendsto_inner_L2Sigma`, `ofReal_tail_sq_eq_tailEnn`,
  `integral_tail_sq_galerkin_le`, `integral_tail_sq_limit_le`
  — proved in `LerayHopf/TorusModeTail.lean` (T-AL-5, PR #88).
-/

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

/-- Boundary check (T-AL-5 → T-AL-6): REAL wiring, fully `_root_`-qualified per the
anti-shadowing rules — with the T-AL-5 placeholders graduated and deleted, every call
below hits KERNEL-VERIFIED production (codex P3 on PR #88: the earlier version of this
example resolved `integral_tail_sq_*` to the same-name sorried Scratch placeholders).
Consumes the T-AL-4 capstone + the T-AL-5 tail lemmas and produces exactly Step F's
raw materials — the Step-D convergence, the n-uniform Galerkin tail bound along `φ`,
and the limit tail bound — verifying the hypothesis shapes compose across the PR
boundary against the real interfaces. -/
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
    fun n N =>
      _root_.LerayHopf.integral_tail_sq_galerkin_le F ν u₀ (φ n) (galSeq (φ n)) T hT N,
    fun N =>
      _root_.LerayHopf.integral_tail_sq_limit_le F ν hν T hT u₀ galSeq φ u hub hmeas
        hweak N⟩

end Scratch
end LerayHopf
