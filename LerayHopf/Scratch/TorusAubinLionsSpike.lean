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

/-! ## P0.8 — `∫₀ᵀ ‖·‖² → 0` ⇒ `eLpNorm → 0` conversion (field 4's exact shape)

T-AL-6 GATE (architect, 2026-07-04): CONFIRMED AS-FROZEN, verbatim from Phase-0.
Proof route: the #44/#47 `eLpNorm`↔`lintegral` bridge patterns (`MemLp` from the
`M`-bound + AESM on the finite measure; `eLpNorm`² = lintegral of `ofReal ‖·‖²`;
interval integral → set integral over `Ioc ⊆ Icc`, endpoint null). -/

theorem eLpNorm_tendsto_of_integral_sq_tendsto
    (T : ℝ) (hT : 0 < T) (M : ℝ) (f : ℕ → ℝ → L2VF)
    (hmeas : ∀ n, AEStronglyMeasurable (f n) (volume.restrict (Icc (0 : ℝ) T)))
    (hb : ∀ n t, t ∈ Icc (0 : ℝ) T → ‖f n t‖ ≤ M)
    (hint : Tendsto (fun n => ∫ t in (0 : ℝ)..T, ‖f n t‖ ^ 2) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (f n) 2 (volume.restrict (Icc (0 : ℝ) T))) atTop
      (𝓝 0) := by
  sorry -- ALLOW_SORRY: scratch spike (Phase-0, torus-aubinlions-modewise-plan §2 P0.8)

/-! ## T-AL-6 statement freeze (Step F assembly — the finish line; architect gate, 2026-07-04)

Production placement (acyclicity verified in source): NEW file
`LerayHopf/TorusAubinLionsAssembly.lean`, importing `LerayHopf.TorusModeTail`
(transitively: ModeCompactness → {GalerkinODESolve, TestFamily, ConvectionExtension,
ScalarEquicontinuity} → AxiomaticClosure, so `AubinLionsPackage` is in scope).  It
holds P0.8 + P0.16 + the P0.7 def.  Consumer rewire: `TorusGalerkinODECapstone.lean`
adds `import LerayHopf.TorusAubinLionsAssembly` and replaces the call at :80
`aubin_lions F ν hν T hT u₀ galSeq rellich_L2Sigma` by
`torusAubinLionsPackage_of_galSeq F ν hν T hT u₀ galSeq rellich_L2Sigma`
(same argument list — `spatial` still fed, now unused `_spatial`).  No cycle: none of
the Capstone's current imports (ConvectionExtension, GalerkinODESolve, TraceEnergy,
ViscousLimit) is downstream of ModeCompactness/ModeTail/Assembly.  Then DELETE
`axiom aubin_lions` from `AxiomaticClosure.lean` (+ its ALLOW_AXIOM marker and
assumptions-section entry), update the stale axiom mentions in
`TorusAxiomatic.lean:15` and the `TorusGalerkinODECapstone.lean` header comments,
pin `scripts/check-axioms-live.sh` torus → 0, STATUS.md banner.

Step-F decomposition: ONE new analytic leaf (P0.16, the split-convergence core) so
the P0.7 body is thin verified glue.  Step-F math inside P0.16: pointwise Pythagoras
`‖x‖² = ‖P_N x‖² + ‖x − P_N x‖²` (`velocityProjection_n_pythagoras`,
`TorusProjectionAdjoint.lean:136`, applied to `x := v_φn t − u t`, with
`P_N(v−u) = P_N v − P_N u` by CLM linearity and `tail(v−u) = tail v − tail u`);
`‖a−b‖² ≤ 2‖a‖² + 2‖b‖²` on the tail; integrate (integrands AESM + bounded on the
finite interval ⇒ interval-integrable); the two T-AL-5 tail bounds give
`∫‖tail(v_φn−u)‖² ≤ 4B/(1+N²)` with `B := T‖u₀‖² + ‖u₀‖²/(2ν) ≥ 0` (`hν`, `hT`);
Step-D (`hD`) kills the projected part; ε-squeeze over `N` (Archimedean `(N:ℝ)² → ∞`,
`∫ ≥ 0` from the nonneg integrand) closes `Tendsto … (𝓝 0)`.

ATOMIC-GRADUATION PLAN (anti-shadowing rule 1): the T-AL-6 production PR transcribes
P0.8/P0.16/P0.7 and, IN THE SAME PR, deletes this spike file entirely — after this
gate nothing remains frozen-only, the campaign's statement-pressure-testing purpose
is complete, and the plan doc + git history preserve the record.  (Alternative if the
orchestrator prefers a standing drift guard: keep only the `_root_`-qualified
boundary examples.  Default: delete.) -/

/-- (P0.16) Step F core — strong `L²(0,T; L²)` convergence of the extracted Galerkin
subsequence to the limit curve, from the Step-D projected convergence + the two
T-AL-5 tail bounds via the Pythagoras split and an ε-squeeze over the level `N`.
Conclusion shape = P0.8's `hint` input verbatim. -/
theorem integral_sq_sub_tendsto_zero_of_galSeq
    (F : Torus3NSForms) (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T)
    (u₀ : L2Sigma) (galSeq : ∀ n, GalerkinSolutionData F ν u₀ n)
    (φ : ℕ → ℕ) (u : Time → L2Sigma)
    (hub : ∀ t ∈ Icc (0 : ℝ) T, ‖(u t : L2VF)‖ ≤ ‖(u₀ : L2VF)‖)
    (hmeas : AEStronglyMeasurable (fun t => (u t : L2VF))
      (volume.restrict (Icc (0 : ℝ) T)))
    (hweak : ∀ t ∈ Icc (0 : ℝ) T, ∀ z : L2Sigma,
      Tendsto (fun n => inner (𝕜 := ℝ) (((galSeq (φ n)).u t : L2VF)) ((z : L2VF)))
        atTop (𝓝 (inner (𝕜 := ℝ) ((u t : L2VF)) ((z : L2VF)))))
    (hD : ∀ N : ℕ, Tendsto (fun n => ∫ t in (0 : ℝ)..T,
        ‖velocityProjection_n N (((galSeq (φ n)).u t : L2VF)) -
          velocityProjection_n N ((u t : L2VF))‖ ^ 2) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ t in (0 : ℝ)..T,
        ‖((galSeq (φ n)).u t : L2VF) - (u t : L2VF)‖ ^ 2) atTop (𝓝 0) := by
  sorry -- ALLOW_SORRY: scratch spike (T-AL-6 statement freeze, P0.16 Step F core)

/-! ## P0.7 — the REPLACEMENT def (ALL FIVE fields; the axiom-deletion target)

Binder list is byte-identical to `axiom aubin_lions` (`AxiomaticClosure.lean:376`) —
same types in the same order, so the consumer rewire is a pure name swap.  The
`spatial` binder is UNUSED by the mode-wise proof (renamed `_spatial`; the consumer
keeps feeding `rellich_L2Sigma` positionally).  `Type`-valued, so a `noncomputable
def`; the Prop→Type extraction from the T-AL-4 capstone's existential goes through
`Classical.choose` (∃ has no large elimination; the ∧ chain does).

The body below is the REAL Step-F assembly wiring — sorry-free modulo the two leaves
P0.8 and P0.16 (unqualified calls: same-gate freeze placeholders, per anti-shadowing
rule 2); all previously-merged production calls are `_root_`-qualified.  It verifies
ALL FIVE `AubinLionsPackage` field shapes against the real construction. -/

noncomputable def torusAubinLionsPackage_of_galSeq
    (F : Torus3NSForms) (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T)
    (u₀ : L2Sigma)
    (galSeq : ∀ n, GalerkinSolutionData F ν u₀ n)
    (_spatial : ∀ (M : ℝ) (z : ℕ → L2VF),
      (∀ n, z n ∈ L2Sigma) →
      (∀ n, memH1VF (z n)) →
      (∀ n, h1EnergySq (z n) ≤ M ^ 2) →
      ∃ (ψ : ℕ → ℕ) (g : L2VF), StrictMono ψ ∧ g ∈ L2Sigma ∧
        Filter.Tendsto (fun n => z (ψ n)) Filter.atTop (nhds g)) :
    AubinLionsPackage F ν T u₀ galSeq := by
  classical
  -- T-AL-4 capstone (production): the extraction φ, the limit curve u, and the four
  -- analytic conjuncts.  Type-valued goal ⇒ extract the ∃-witnesses by choice.
  have H := _root_.LerayHopf.exists_limit_curve_of_galSeq F ν hν T hT u₀ galSeq
  obtain ⟨hφ, hweak, hub, hmeas, hD⟩ := H.choose_spec.choose_spec
  -- Fields 1–3 and 5 are direct; field 4 (strong_convergence) is Step F.
  refine ⟨H.choose, hφ, H.choose_spec.choose, ?_, hmeas⟩
  -- Continuity of the reindexed Galerkin curves (production T-AL-3 export).
  have hcont : ∀ n, ContinuousOn
      (fun t => ((galSeq (H.choose n)).u t : L2VF)) (Icc (0 : ℝ) T) := fun n =>
    (_root_.LerayHopf.galerkin_u_continuousOn F ν u₀ (H.choose n)
      (galSeq (H.choose n))).mono Icc_subset_Ici_self
  -- Step F: split-convergence core (P0.16) → eLpNorm conversion (P0.8).
  exact eLpNorm_tendsto_of_integral_sq_tendsto T hT (2 * ‖(u₀ : L2VF)‖)
    (fun n t => ((galSeq (H.choose n)).u t : L2VF) - (H.choose_spec.choose t : L2VF))
    (fun n => ((hcont n).aestronglyMeasurable measurableSet_Icc).sub hmeas)
    (fun n t ht =>
      (norm_sub_le _ _).trans (by
        have h1 := _root_.LerayHopf.galerkin_u_norm_le F ν u₀ (H.choose n)
          (galSeq (H.choose n)) t ht.1
        have h2 := hub t ht
        linarith))
    (integral_sq_sub_tendsto_zero_of_galSeq F ν hν T hT u₀ galSeq
      H.choose H.choose_spec.choose hub hmeas hweak hD)

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
