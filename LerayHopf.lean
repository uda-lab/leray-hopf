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
- `import LerayHopf.Torus.Capstone` — T³ kernel-only capstone re-export
- `import LerayHopf.R3Capstone`     — ℝ³ kernel-only capstone re-export
- `import LerayHopf`                 — (this file) re-exports all three layers

Core work that does not require the capstone re-exports should use
`import LerayHopf.Core` to stay project-axiom-free.

No claim is made that existence, regularity, uniqueness, or nonuniqueness of the
Navier–Stokes equations has been formalized.
-/

-- Axiom-free core layer (no project axioms, no sorryAx)
import LerayHopf.Core

-- Torus-layer files not covered by Core (sorry-carrying, axiom-free)
import LerayHopf.Torus.RellichEmbedding
import LerayHopf.Torus.H1Sigma
import LerayHopf.EvolutionTriple
import LerayHopf.Statement
import LerayHopf.ExistenceFromPackage
import LerayHopf.EnergyEstimate

-- Capstone re-export layers
import LerayHopf.Torus.Capstone
import LerayHopf.R3Capstone

-- Torus H¹_σ submodule + Parseval scaffold (issue #53 PR-1)
import LerayHopf.Torus.EnergyConvection

-- Torus determined-form construction (issue #53: removes torusConvectionGap_exists axiom)
import LerayHopf.Torus.ConvectionExtension

-- Concrete T³ convection form (issue #22: removes torus3_NSForms_exist axiom)
import LerayHopf.Torus.ConvectionForm

-- T³ Galerkin ODE solver + capstone wiring (issue #24: removes galerkin_ode_solution axiom)
import LerayHopf.Torus.GalerkinScheme
-- T-AL-1 (#23): torus test family
import LerayHopf.Torus.TestFamily
import LerayHopf.Torus.GalerkinODESolve
import LerayHopf.Torus.GalerkinODECapstone

-- T³ WeakFormNS limit passage (issue #25 conjunct 2: density-free, band-limited tests)
import LerayHopf.Torus.LimitPassage

-- T³ trace + energy pillar (galerkin_limit_passage removal): Galerkin energy identity,
-- weakly-continuous good representative, ∀t energy inequality (conjunct 1), strong initial
-- trace (conjunct 3), and the capstone `torus_galerkin_limit_passage_of_energyClass`
-- (full 5-conjunct existential, conditional only on the energy-class conjunct 4 for alPkg.u)
import LerayHopf.Torus.TraceEnergy

-- T³ energy-class conjunct (4) scaffold: a.e. memH1VF + IntervalIntegrable dissipation
-- for alPkg.u, to be plugged into torus_galerkin_limit_passage_of_energyClass
import LerayHopf.Torus.ViscousLimit

-- T³ galerkin_limit_passage removal: orthogonality calculus for velocityProjection_n (PR-1)
import LerayHopf.Torus.ProjectionAdjoint

-- R3 files not covered by Core (sorry-carrying or axiom-dependent)
import LerayHopf.R3.GalerkinScheme
import LerayHopf.R3.SchwartzDivFreeBasis
import LerayHopf.R3.GalerkinODE
import LerayHopf.R3.GalerkinODEExistence
import LerayHopf.R3.GalerkinODESolve
import LerayHopf.R3.GalerkinODECapstone
import LerayHopf.R3.ArzelaAscoliTime      -- issue #44: spacetime precompactness frontier
import LerayHopf.R3.AubinLionsLimitPassage
import LerayHopf.R3.CurlDensity
import LerayHopf.R3.CurlDensityCapstone   -- issue #3: curlSchwartzDense_holds now a proved theorem
import LerayHopf.R3.GalerkinBasisH1       -- issue #4 PR-3: nonempty_schwartzGalerkinBasis_H1 (strengthened basis, scaffold)
import LerayHopf.R3.FrechetKolmogorov
import LerayHopf.R3.ConvectionOperator
import LerayHopf.R3.ConvectionForm
import LerayHopf.R3.SobolevEmbedding
import LerayHopf.R3.EnergyClassConvection
import LerayHopf.R3.ConvectionExtension  -- issue #56: determined-form ConvectionGapOp construction
import LerayHopf.R3.TensorIntersection   -- issue #56: S⊗V ∩ V⊗S = S⊗S linear-algebra lemma
import LerayHopf.R3.GalerkinCurveBounds  -- issue #46 PR-1: Galerkin curve/pairing library (File B)
import LerayHopf.R3.GalerkinTrilinearBound  -- issue #46 PR-2: Galerkin trilinear/energy-class bounds (File C)
import LerayHopf.R3.GalerkinTimeModulus  -- issue #46 PR-3: good-sampling + master uniform sampling-error bound (File D)
import LerayHopf.R3.SpacetimePrecompact  -- issue #46 PR-4: assembled LOCAL spacetime precompactness (File E)

-- Bochner layer (sorry-carrying)
import LerayHopf.Bochner.GelfandTriple
import LerayHopf.Bochner.TimeSobolev
import LerayHopf.Bochner.TimeSobolevAC
import LerayHopf.Bochner.TimeConvolution
import LerayHopf.Bochner.TimeMollifierInterval
import LerayHopf.Bochner.TimeMollification
import LerayHopf.Bochner.StepFunctionCompactness  -- issue #46 PR-1: generic step-curve Lp compactness (File A)
import LerayHopf.Bochner.ScalarEquicontinuity     -- T-AL-2 (#23): domain-neutral scalar equicontinuity engine
import LerayHopf.Bochner.WeakLimitToolkit         -- issue #4 PR-5: generic Hilbert weak-limit toolkit (hoisted from Torus/TraceEnergy)
import LerayHopf.Torus.ModeCompactness             -- T-AL-3 (#23): mode-wise extraction (equi-Lipschitz + engine assembly)
import LerayHopf.Torus.ModeTail                    -- T-AL-5 (#23): mode-wise tail bounds
import LerayHopf.Torus.AubinLionsAssembly          -- T-AL-6 (#23): aubin_lions replacement assembly
import LerayHopf.R3.GoodRepresentative            -- issue #4 PR-5: R3 weakly-continuous representative (scaffold)
import LerayHopf.R3.LimitPassage                  -- issue #4 PR-6: galerkin_limit_passage_R3 PROVED (zero project axioms)
