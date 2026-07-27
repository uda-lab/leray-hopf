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
* `LerayHopf` (this file) — re-exports all three layers, plus the remaining support
  files (Bochner time theory, Galerkin ODE solvers, limit passage, etc.) needed to
  assemble both capstones. **Sorry-free, axiom-free release surface (issues #147, #151):**
  every module transitively imported from here is free of `sorry` and of
  `axiom`/`constant`/`opaque`/`unsafe`, marked or unmarked, and free of any
  `Scaffold`/`Placeholder`/`Stub`/`Draft` namespace — see `scripts/check-release-cone.sh`,
  which enforces this statically in CI with no marker escape.
* `LerayHopf.Experimental` — explicit **opt-in** for the incomplete Bochner time-layer
  work that does NOT live in the release cone (four modules, six `sorry`s total; see that
  file's docstring for the per-module inventory). Nothing under `LerayHopf` imports it.

Side branches (independent of the existence capstones):
* `LerayHopf.BlowupLowerBound`  (Branch A) — algebraic blow-up lower bound, sorry-free.

For the narrative status (axiom ledger, remaining `sorry` inventory, verification
commands) see `README.md` and `HANDOFF.md`. The original milestone plan and axiom-removal
roadmap (`docs/archive/milestone.md`, `docs/archive/ROADMAP.md`) are archived and historical
— both capstones are long past them, at 0 project axioms each.

## Import surface structure

The import surface is split:
- `import LerayHopf.Core`            — axiom-free, sorryAx-free spatial/regularity layer
- `import LerayHopf.Torus.Capstone` — T³ kernel-only capstone re-export
- `import LerayHopf.R3Capstone`     — ℝ³ kernel-only capstone re-export
- `import LerayHopf`                 — (this file) the complete release surface: both
  capstones plus all supporting layers, **sorry-free**
- `import LerayHopf.Experimental`   — explicit opt-in for incomplete Bochner time-layer
  work (`TimeSobolevAC`, `TimeMollification`, `TimeMollifierInterval`,
  `TimeSobolevExperimental`); not part of the release surface and not needed for either
  capstone

Core work that does not require the capstone re-exports should use
`import LerayHopf.Core` to stay project-axiom-free.
-/

-- Axiom-free core layer (no project axioms, no sorryAx)
import LerayHopf.Core

-- Generic Galerkin layer (issue #112: domain-neutral dissipative-ODE + quadratic-field
-- construction, deduplicating the R3/Torus GalerkinODESolve CLM towers); consumed by
-- R3/Torus GalerkinODESolve.lean and R3/GalerkinODEExistence.lean.
import LerayHopf.Galerkin.DissipativeODE
import LerayHopf.Galerkin.QuadraticField
-- Generic Galerkin bundle layer (issue #112: domain-neutral Domain + solution bundles;
-- both SolutionInterfaces route through these as abbrevs/extends).
import LerayHopf.Galerkin.Domain
import LerayHopf.Galerkin.SolutionBundles
import LerayHopf.Galerkin.GlobalContract

-- Torus-layer files not covered by Core, needed to assemble the capstone (sorry-free per
-- the release-cone guard; axiom-free — the former "sorry-carrying" label was stale since
-- these were discharged)
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
-- Torus test family (issue #23): countable spanning family of Galerkin test functions
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

-- R3 files not covered by Core, needed to assemble the capstone (sorry-free per the
-- release-cone guard; axiom-free — the former "sorry-carrying or axiom-dependent" label
-- was stale since these were discharged)
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

-- Bochner layer. Sorry-free in the root closure (issue #147): the incomplete Bochner
-- time-layer modules (TimeSobolevAC, TimeMollification, TimeMollifierInterval, and the
-- relocated w1pTime_continuous_in_H) live behind the explicit opt-in `LerayHopf.Experimental`
-- and are NOT imported here. `TimeSobolev` stays: it is sorry-free (its one former sorry,
-- w1pTime_continuous_in_H, was extracted to TimeSobolevExperimental.lean) and is needed
-- directly by R3/AubinLionsLimitPassage.lean and R3/EnergyWeakLsc.lean for kineticEnergy_lsc_transfer.
import LerayHopf.Bochner.GelfandTriple
import LerayHopf.Bochner.TimeSobolev
import LerayHopf.Bochner.TimeConvolution
import LerayHopf.Bochner.StepFunctionCompactness  -- issue #46 PR-1: generic step-curve Lp compactness (File A)
import LerayHopf.Bochner.ScalarEquicontinuity     -- issue #23: domain-neutral scalar equicontinuity engine
import LerayHopf.Bochner.WeakLimitToolkit         -- issue #4 PR-5: generic Hilbert weak-limit toolkit (hoisted from Torus/TraceEnergy)
import LerayHopf.Bochner.DiagonalExtraction       -- issue #202 P3: abstract diagonal-subsequence machinery (PDE-independent)
import LerayHopf.Torus.ModeCompactness             -- issue #23: mode-wise extraction (equi-Lipschitz + engine assembly)
import LerayHopf.Torus.ModeTail                    -- issue #23: mode-wise tail bounds
import LerayHopf.Torus.AubinLionsAssembly          -- issue #23: aubin_lions replacement assembly
import LerayHopf.Torus.KappaChainExit              -- issue #201 P2: κ-chain exit gate (P2ExitWitness + torus_kappaChain_exit)
import LerayHopf.Torus.DiagonalGalerkin            -- issue #202 P3: stage recursion + diagonal weak limit (exists_diagonal_weakly_convergent_galSeq)
import LerayHopf.R3.GoodRepresentative            -- issue #4 PR-5: R3 weakly-continuous representative (scaffold)
import LerayHopf.R3.LimitPassage                  -- issue #4 PR-6: galerkin_limit_passage_R3 PROVED (zero project axioms)
