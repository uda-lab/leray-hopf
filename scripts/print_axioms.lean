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
--   exists_lerayHopf_torus3_axiomatic — EXACTLY:
--     propext  Classical.choice  Quot.sound
--     LerayHopf.aubin_lions  LerayHopf.galerkin_limit_passage
--     LerayHopf.galerkin_ode_solution  LerayHopf.torus3_NSForms_exist
--
--   exists_lerayHopf_r3_axiomatic — EXACTLY:
--     propext  Classical.choice  Quot.sound
--     LerayHopf.aubin_lions_R3  LerayHopf.galerkin_limit_passage_R3
--     LerayHopf.galerkin_ode_solution_R3  LerayHopf.r3GalerkinScheme_exists
--     LerayHopf.r3_NSForms_exist  LerayHopf.spatial_compactness_R3
--
--   lower_bound_from_inverse_square_lifespan (Core representative) — EXACTLY:
--     propext  Classical.choice  Quot.sound  (no project axioms)
--
--   localCompactness_R3_of_ballCompact (Core R3 representative) — EXACTLY:
--     propext  Classical.choice  Quot.sound  (no project axioms)

import LerayHopf.TorusAxiomatic
import LerayHopf.R3Axiomatic
import LerayHopf.Core

#print axioms LerayHopf.exists_lerayHopf_torus3_axiomatic
#print axioms LerayHopf.exists_lerayHopf_r3_axiomatic
#print axioms LerayHopf.lower_bound_from_inverse_square_lifespan
#print axioms LerayHopf.localCompactness_R3_of_ballCompact
