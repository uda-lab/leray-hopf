/-
# LerayHopf

Root module for the Leray–Hopf weak-existence formalization project.

The mathematical scope — solution concept, existence statement, Galerkin compactness
package, energy skeleton — is specified in:

* `docs/milestone.md`            (roadmap)
* `docs/leray_hopf_lean_mvp_plan.md` (MVP design and file layout)

Those plan files are the source of truth for mathematical content. This module gathers
the structural spine (Milestone 1): the solution concept, the existence statement (still a
marked `sorry` target), the Galerkin compactness package, the structural implication
package ⟹ existence, and an abstract energy skeleton. PDE analysis is intentionally
packaged behind `Prop` placeholders and refined in later milestones.

Side branches (independent of the existence spine):
* `LerayHopf.BlowupLowerBound`  (Branch A) — algebraic blow-up lower bound, sorry-free.
* `LerayHopf.NonuniquenessStatement` (Branch B) — non-uniqueness proposition, scaffold only.

No claim is made that existence, regularity, uniqueness, or nonuniqueness of the
Navier–Stokes equations has been formalized.
-/

import LerayHopf.Basic
import LerayHopf.TorusDomain
import LerayHopf.FunctionSpaces
import LerayHopf.SobolevTorus
import LerayHopf.DivergenceFree
import LerayHopf.Leray
import LerayHopf.Statement
import LerayHopf.GalerkinPackage
import LerayHopf.ExistenceFromPackage
import LerayHopf.EnergySkeleton
import LerayHopf.BlowupLowerBound
import LerayHopf.NonuniquenessStatement
