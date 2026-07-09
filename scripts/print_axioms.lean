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

import LerayHopf.Torus.Capstone
import LerayHopf.R3Capstone
import LerayHopf.Core

#print axioms LerayHopf.exists_lerayHopf_torus3
#print axioms LerayHopf.exists_lerayHopf_r3
#print axioms LerayHopf.lower_bound_from_inverse_square_lifespan
#print axioms LerayHopf.localCompactness_R3_of_ballCompact
