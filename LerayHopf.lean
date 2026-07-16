/-
# LerayHopf

Root module for the Leray–Hopf weak-existence formalization project.

## What is proved

Two capstone existence theorems, both **kernel-only** (`#print axioms` returns only
`propext` / `Classical.choice` / `Quot.sound` — zero project axioms, no `sorryAx`):

* `exists_lerayHopf_torus3` (𝕋³, the 3-torus) — `LerayHopf/Torus/GalerkinODECapstone.lean`
* `exists_lerayHopf_r3` (ℝ³, whole space — the original Leray 1934 target) —
  `LerayHopf/R3/GalerkinODECapstone.lean`

Import `LerayHopf.Torus.Capstone` (which pulls in `Torus/GalerkinODECapstone.lean`) or
`LerayHopf.R3Capstone` (which pulls in `R3/GalerkinODECapstone.lean`) to bring the
corresponding `exists_lerayHopf_*` theorem into scope; each capstone file's own
`SolutionInterfaces.lean` support layer provides the surrounding definitions
(`Torus3NSForms`/`R3NSForms`, assembly helpers) but does not itself export the
theorem. `LerayHopfSolutionFull(_R3)` is **proof-carrying**: its fields are actual
proofs of the weak Navier–Stokes equation (against separated-variable tests), the
energy inequality on `[0,T]`, a one-sided initial trace at `t → 0⁺`, and the energy
class (a.e.-in-time H¹ membership plus interval-integrable viscous dissipation — not
literal Bochner membership `u ∈ L²(0,T;H¹_σ)`) — not `Prop` placeholders. See
`README.md`'s claims table for the exact field-by-claim mapping.

No claim is made that regularity, uniqueness, or non-uniqueness of the
Navier–Stokes equations has been formalized.

## Layering

* `LerayHopf.Core` — the axiom-free, `sorryAx`-free spatial/regularity layer shared by
  both domains: the T³ and ℝ³ `L²_σ` spaces, Leray/Galerkin projections, and Fourier
  machinery. (The domain-neutral abstract layer — `EvolutionTriple.lean`'s
  `DissipativeEvolution`/`WeakFormNS` and `EnergyEstimate.lean`'s `AbstractEnergyLaw` —
  lives in separate top-level modules that `Core` does not import; reach them via
  `import LerayHopf` or by importing those files directly.) Work that does not need a
  capstone should `import LerayHopf.Core` to stay project-axiom-free.
* `LerayHopf.Torus.Capstone` — re-exports the full T³ capstone chain
  (`exists_lerayHopf_torus3`).
* `LerayHopf.R3Capstone` — re-exports the full ℝ³ capstone chain
  (`exists_lerayHopf_r3`).
* `LerayHopf` (this file) — re-exports all three layers, plus the remaining
  sorry-carrying support files (Bochner time theory, Galerkin ODE solvers, limit
  passage, etc.) needed to assemble both capstones.

Side branches (independent of the existence capstones):
* `LerayHopf.BlowupLowerBound`  (Branch A) — algebraic blow-up lower bound, sorry-free.

For the narrative status (axiom ledger, remaining `sorry` inventory, verification
commands) see `README.md` and `HANDOFF.md`; for the mathematical roadmap see
`docs/milestone.md` and `docs/ROADMAP.md`.

## Import surface structure (Wave-0 axiom-removal refactor)

The import surface is split:
- `import LerayHopf.Core`            — axiom-free, sorryAx-free spatial/regularity layer
- `import LerayHopf.Torus.Capstone` — T³ kernel-only capstone re-export
- `import LerayHopf.R3Capstone`     — ℝ³ kernel-only capstone re-export
- `import LerayHopf`                 — (this file) re-exports all three layers

Core work that does not require the capstone re-exports should use
`import LerayHopf.Core` to stay project-axiom-free.
-/

-- Axiom-free core layer (no project axioms, no sorryAx)
import LerayHopf.Core

-- Generic Galerkin layer (issue #112: domain-neutral dissipative-ODE + quadratic-field
-- construction, deduplicating the R3/Torus GalerkinODESolve CLM towers). Mathlib-only,
-- no consumers yet (PR-A scaffold; wiring lands in PR-B).
import LerayHopf.Galerkin.DissipativeODE
import LerayHopf.Galerkin.QuadraticField
-- Generic Galerkin bundle layer (issue #112 PR-C: domain-neutral Domain + solution bundles;
-- both SolutionInterfaces route through these as abbrevs/extends).
import LerayHopf.Galerkin.Domain
import LerayHopf.Galerkin.SolutionBundles

-- Torus-layer files not covered by Core (sorry-carrying, axiom-free)
import LerayHopf.Torus.RellichEmbedding
import LerayHopf.Torus.H1Sigma
import LerayHopf.EvolutionTriple
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
import LerayHopf.Analysis.TensorIntersection   -- issue #56: S⊗V ∩ V⊗S = S⊗S linear-algebra lemma
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
