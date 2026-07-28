-- Live axiom pin: `#print axioms` on the three pinned declarations.
--
-- Run via:
--   lake env lean scripts/print_axioms.lean
-- or pipe to stdin:
--   lean ... --stdin
--
-- Output is consumed by scripts/check-axioms-live.sh, which asserts the
-- exact expected axiom sets and fails CI on any deviation.
--
-- Pinned expected axiom sets (kernel axioms are the same for all):
--
--   exists_lerayHopf_torus3 — EXACTLY:
--     propext  Classical.choice  Quot.sound
--     (kernel-only capstone)
--
--   exists_lerayHopf_r3 — EXACTLY:
--     propext  Classical.choice  Quot.sound
--     (kernel-only capstone)
--
--   lower_bound_from_inverse_square_lifespan (Core representative) — EXACTLY:
--     propext  Classical.choice  Quot.sound  (no project axioms)
--
--   localCompactness_R3_of_ballCompact (Core R3 representative) — EXACTLY:
--     propext  Classical.choice  Quot.sound  (no project axioms)
--
-- Also prints (VISIBILITY ONLY, not gated — see check-axioms-live.sh's "Experimental
-- axiom profile" section, issue #158) the axiom sets of 5 of the 6 declarations behind
-- the `LerayHopf.Experimental` opt-in (the 6th, `timeConv_prod_integrable`, is `private`
-- and therefore not name-addressable from this separate script file at all — see its
-- statement card, docs/statement-cards/timeConv_prod_integrable.md, for why that is
-- expected and not a visibility gap: it is an internal helper, never public API). Each
-- printed declaration is expected to carry `sorryAx`; that is not a failure, it is the
-- point of the release-cone/Experimental split (issue #147). This makes the
-- sorryAx-carrying surface visible in release tooling without gating on it.

import LerayHopf.Torus.Capstone
import LerayHopf.R3Capstone
import LerayHopf.Core
import LerayHopf.Experimental
import LerayHopf.Galerkin.GlobalContract
import LerayHopf.Torus.KappaChainExit
import LerayHopf.Torus.DiagonalGalerkin

#print axioms LerayHopf.exists_lerayHopf_torus3
#print axioms LerayHopf.exists_lerayHopf_r3
#print axioms LerayHopf.lower_bound_from_inverse_square_lifespan
#print axioms LerayHopf.localCompactness_R3_of_ballCompact

-- Generic global contract layer (issue #195 P1) — interim live pins for the promoted
-- module while it has no live-pinned downstream capstone (see the P1→P4 window note in
-- check-axioms-live.sh and docs/scratch/global-diagonal-campaign.md §10.5 / Q3 ruling).
#print axioms LerayHopf.Galerkin.nonempty_lerayHopfSolution_iff_exists_isOn
#print axioms LerayHopf.Galerkin.globalLerayHopfSolution_nonempty_iff
#print axioms LerayHopf.Galerkin.GlobalLerayHopfSolution.toSolution_u
#print axioms LerayHopf.Galerkin.IsLerayHopfOn.mono
#print axioms LerayHopf.Galerkin.IsLerayHopfOn.congr_Icc

-- P2 (#201) κ-chain exit gate — the compiled acceptance artifact instantiation.
#print axioms LerayHopf.torus_kappaChain_exit

-- P3 (#202) diagonal machinery — the packaged weak-limit theorem plus the promoted
-- abstract diagonal API it consumes directly (the latter has no other release-cone
-- live pin, so it is pinned here to close the P3→P4 sorryAx blind window; architect
-- #202 §7 addition).
#print axioms LerayHopf.exists_diagonal_weakly_convergent_galSeq
#print axioms LerayHopf.Bochner.exists_diagonal_extraction

-- Experimental-module axiom profile (visibility only — see docs/statement-cards/).
#print axioms LerayHopf.Bochner.w1pTime_continuous_in_H
#print axioms LerayHopf.Bochner.isWeakTimeDeriv_primitive
#print axioms LerayHopf.Bochner.timeMollification_exists
#print axioms LerayHopf.Bochner.weakTimeDerivℝ_even_reflection
#print axioms LerayHopf.Bochner.w1pTime_lineExtension
