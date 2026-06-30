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

## Import surface structure (Wave-0 axiom-removal refactor)

The import surface is now split:
- `import LerayHopf.Core`            — axiom-free, sorryAx-free spatial/regularity layer
- `import LerayHopf.TorusAxiomatic`  — T³ axiomatic closure (4 project axioms)
- `import LerayHopf.R3Axiomatic`     — ℝ³ axiomatic closure (5 project axioms; `r3GalerkinScheme_exists` swapped for `curlSchwartzDense_holds`, issue #21)
- `import LerayHopf`                 — (this file) re-exports all three layers

Core work that does not require the axiomatic closures should use
`import LerayHopf.Core` to stay project-axiom-free.

No claim is made that existence, regularity, uniqueness, or nonuniqueness of the
Navier–Stokes equations has been formalized.
-/

-- Axiom-free core layer (no project axioms, no sorryAx)
import LerayHopf.Core

-- Torus-layer files not covered by Core (sorry-carrying, axiom-free)
import LerayHopf.RellichEmbedding
import LerayHopf.H1Sigma
import LerayHopf.EvolutionTriple
import LerayHopf.Statement
import LerayHopf.ExistenceFromPackage
import LerayHopf.EnergyEstimate

-- Axiomatic closure layers (project axioms live here)
import LerayHopf.TorusAxiomatic
import LerayHopf.R3Axiomatic

-- Torus H¹_σ submodule + Parseval scaffold (issue #53 PR-1)
import LerayHopf.TorusEnergyConvection

-- Torus determined-form scaffold (issue #53 PR-2: TorusConvectionExtension)
import LerayHopf.TorusConvectionExtension

-- Concrete T³ convection form (issue #22: removes torus3_NSForms_exist axiom)
import LerayHopf.TorusConvectionForm

-- T³ Galerkin ODE solver + capstone wiring (issue #24: removes galerkin_ode_solution axiom)
import LerayHopf.TorusGalerkinScheme
import LerayHopf.TorusGalerkinODESolve
import LerayHopf.TorusGalerkinODECapstone

-- R3 files not covered by Core (sorry-carrying or axiom-dependent)
import LerayHopf.R3.GalerkinScheme
import LerayHopf.R3.SchwartzDivFreeBasis
import LerayHopf.R3.GalerkinODE
import LerayHopf.R3.GalerkinODEExistence
import LerayHopf.R3.GalerkinODESolve
import LerayHopf.R3.GalerkinODECapstone
import LerayHopf.R3.ArzelaAscoliTime      -- issue #44: T0.1/T0.2 axioms + T1–T4 scaffold
import LerayHopf.R3.AubinLionsLimitPassage
import LerayHopf.R3.CurlDensity
import LerayHopf.R3.CurlDensityCapstone   -- issue #3: curlSchwartzDense_holds now a proved theorem
import LerayHopf.R3.FrechetKolmogorov
import LerayHopf.R3.ConvectionOperator
import LerayHopf.R3.ConvectionForm
import LerayHopf.R3.SobolevEmbedding
import LerayHopf.R3.EnergyClassConvection
import LerayHopf.R3.ConvectionExtension  -- PR-3: C0–C10 scaffold for full ConvectionGapOp construction
import LerayHopf.R3.TensorIntersection   -- issue #56: S⊗V ∩ V⊗S = S⊗S linear-algebra lemma

-- Bochner layer (sorry-carrying)
import LerayHopf.Bochner.GelfandTriple
import LerayHopf.Bochner.TimeSobolev
import LerayHopf.Bochner.TimeSobolevAC
import LerayHopf.Bochner.TimeConvolution
import LerayHopf.Bochner.TimeMollifierInterval
import LerayHopf.Bochner.TimeMollification
