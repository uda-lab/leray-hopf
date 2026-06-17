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
import LerayHopf.GalerkinProjection
import LerayHopf.RellichEmbedding
import LerayHopf.VelocityGalerkin
import LerayHopf.H1Sigma
import LerayHopf.EvolutionTriple
import LerayHopf.AxiomaticClosure
import LerayHopf.Statement
import LerayHopf.GalerkinPackage
import LerayHopf.ExistenceFromPackage
import LerayHopf.EnergySkeleton
import LerayHopf.EnergyEstimate
import LerayHopf.BlowupLowerBound
import LerayHopf.NonuniquenessStatement
import LerayHopf.R3.Domain
import LerayHopf.R3.DivergenceFree
import LerayHopf.R3.TrilinearEstimate
import LerayHopf.R3.Regularity
import LerayHopf.R3.AxiomaticClosure
import LerayHopf.R3.GalerkinScheme
import LerayHopf.R3.SchwartzDivFreeBasis
import LerayHopf.R3.GalerkinODE
import LerayHopf.R3.GalerkinODEExistence
import LerayHopf.R3.GalerkinODESolve
import LerayHopf.R3.SpatialCompactness
import LerayHopf.R3.FourierL2
import LerayHopf.R3.RellichBall
import LerayHopf.R3.AubinLionsLimitPassage
import LerayHopf.R3.CurlDensity
import LerayHopf.R3.FrechetKolmogorov
import LerayHopf.R3.ConvectionOperator
import LerayHopf.R3.ConvectionForm
import LerayHopf.Bochner.GelfandTriple
import LerayHopf.Bochner.TimeSobolev
