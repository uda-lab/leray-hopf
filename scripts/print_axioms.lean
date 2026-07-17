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

#print axioms LerayHopf.exists_lerayHopf_torus3
#print axioms LerayHopf.exists_lerayHopf_r3
#print axioms LerayHopf.lower_bound_from_inverse_square_lifespan
#print axioms LerayHopf.localCompactness_R3_of_ballCompact

-- Experimental-module axiom profile (visibility only — see docs/statement-cards/).
#print axioms LerayHopf.Bochner.w1pTime_continuous_in_H
#print axioms LerayHopf.Bochner.isWeakTimeDeriv_primitive
#print axioms LerayHopf.Bochner.timeMollification_exists
#print axioms LerayHopf.Bochner.weakTimeDerivℝ_even_reflection
#print axioms LerayHopf.Bochner.w1pTime_lineExtension
