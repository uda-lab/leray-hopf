# Architecture

A one-page module map of the ~80-file `LerayHopf/` tree, grouped by layer. For the
mathematical narrative see `docs/REPORT.md` / `docs/formalization-review-ja.md`; for the
axiom ledger see `HANDOFF.md` / `docs/STATUS.md`.

## Shared abstract layer (top-level, domain-neutral)

Reused unmodified by both 𝕋³ and ℝ³ — the key structural payoff of the design.

| File | Content |
|---|---|
| `LerayHopf/EvolutionTriple.lean` | `DissipativeEvolution` (pivot Hilbert space `H` + regularity functional + viscous/convection forms), `WeakFormNS`, `convForm_self_zero` |
| `LerayHopf/EnergyEstimate.lean` | `AbstractEnergyLaw`, the Galerkin energy identity, energy non-increase |
| `LerayHopf/EnergySkeleton.lean` | Abstract energy-inequality skeleton (scaffold-era, sorry-free) |
| `LerayHopf/Statement.lean` | The original scaffold target statement (`Scaffold.exists_lerayHopf_torus3_statement`) — kept as a marked-`sorry` historical placeholder, distinct from the real capstones |
| `LerayHopf/GalerkinPackage.lean`, `ExistenceFromPackage.lean` | Generic package ⟹ existence plumbing |
| `LerayHopf/BlowupLowerBound.lean`, `NonuniquenessStatement.lean` | Independent side branches (Branch A / B) |

## Bochner abstract time layer — `LerayHopf/Bochner/`

Gelfand-triple / Bochner-space-in-time infrastructure. Consumed by both domains'
Aubin–Lions and limit-passage arguments; carries the project's remaining marked
`sorry`s (Lions–Magenes-class walls; see `HANDOFF.md` §4 and `AGENTS.md`).

`GelfandTriple.lean`, `TimeSobolev.lean`, `TimeSobolevAC.lean`, `TimeConvolution.lean`,
`TimeMollifierInterval.lean`, `TimeMollification.lean`, `StepFunctionCompactness.lean`,
`ScalarEquicontinuity.lean`, `WeakLimitToolkit.lean`.

Imported by: `LerayHopf/R3/GoodRepresentative.lean`, `R3/SpacetimePrecompact.lean`,
`R3/AubinLionsLimitPassage.lean`, `Torus/ModeCompactness.lean`.

## Torus (𝕋³) lane — `LerayHopf/Torus/`

Spatial linear layer (axiom-free, sorry-free): `Basic.lean`, `Domain.lean`,
`FunctionSpaces.lean`, `SobolevTorus.lean`, `DivergenceFree.lean` (`L2Sigma`),
`Leray.lean` (`divSymbol`, Leray projection), `GalerkinProjection.lean`,
`VelocityGalerkin.lean`, `H1Sigma.lean` (`h1EnergySq`, `rellich_L2Sigma`),
`RellichEmbedding.lean` (the Fourier-tail Rellich crux, `rellich_seq_compact`).

Analytic frontier (formerly axiomatized, now proved): `ConvectionForm.lean`,
`ConvectionExtension.lean`, `EnergyConvection.lean`, `GalerkinScheme.lean`,
`GalerkinODESolve.lean`, `GalerkinODECapstone.lean` (**capstone**:
`exists_lerayHopf_torus3`), `TestFamily.lean`, `LimitPassage.lean`,
`TraceEnergy.lean`, `ViscousLimit.lean`, `ProjectionAdjoint.lean`,
`ModeCompactness.lean`, `ModeTail.lean`, `AubinLionsAssembly.lean`.

Interface + re-export: `SolutionInterfaces.lean` (support layer: `Torus3NSForms`,
`LerayHopfSolutionFull`, assembly helpers — the capstone itself now lives in
`GalerkinODECapstone.lean`), `Capstone.lean` (re-exports the full chain).

## ℝ³ lane — `LerayHopf/R3/`

Spatial linear layer (axiom-free, sorry-free): `Domain.lean`, `DivergenceFree.lean`
(`L2Sigma_R3`, weak-divergence × Schwartz test), `Regularity.lean` (`memH1VF_R3`,
`MemSobolev`), `FourierL2.lean`, `RellichBall.lean`, `SpatialCompactness.lean`,
`TrilinearEstimate.lean`, `CurlSchwartzConstruction.lean` (curl-of-Schwartz-potential
construction, `CurlSchwartzDense` — split out of `SchwartzDivFreeBasis.lean`, issue #113 PR-1).

Analytic frontier (formerly axiomatized, now proved): `GalerkinScheme.lean`,
`SchwartzDivFreeBasis.lean` (`r3GalerkinScheme_exists`), `GalerkinODE.lean`,
`GalerkinODEExistence.lean`, `GalerkinODESolve.lean`, `GalerkinODECapstone.lean`
(**capstone**: `exists_lerayHopf_r3`), `ArzelaAscoliTime.lean`,
`AubinLionsLimitPassage.lean`, `AubinLionsAssembly.lean`, `CurlDensity.lean`,
`CurlDensityCapstone.lean`, `CurlDensityH1.lean`, `GalerkinBasisH1.lean`,
`FrechetKolmogorov.lean`, `ConvectionOperator.lean`, `ConvectionForm.lean`,
`ConvectionExtension.lean`, `TensorIntersection.lean`, `SobolevEmbedding.lean`,
`H1SigmaDensity.lean` (`h1Sigma_dense_in_L2Sigma` — split out of `SobolevEmbedding.lean`,
issue #113 PR-1), `EnergyClassConvection.lean`, `GalerkinCurveBounds.lean`,
`GalerkinTrilinearBound.lean`, `GalerkinTimeModulus.lean`, `SpacetimePrecompact.lean`,
`GoodRepresentative.lean`, `LimitPassage.lean`, `WeightedFourierCommute.lean`.

Interface + re-export: `SolutionInterfaces.lean` (support layer: `R3NSForms`,
`LerayHopfSolutionFull_R3`, assembly helpers — capstone itself in
`GalerkinODECapstone.lean`); root-level `LerayHopf/R3Capstone.lean` (re-exports the
full chain).

## Shared spatial core — `LerayHopf/Core.lean`

Collects everything above that is **project-axiom-free and `sorryAx`-free**:
`Torus.Basic/Domain/FunctionSpaces/DivergenceFree/SobolevTorus/Leray/
GalerkinProjection/VelocityGalerkin`, `EnergySkeleton`, `GalerkinPackage`,
`NonuniquenessStatement`, `BlowupLowerBound`, and the ℝ³ spatial/Fourier sublayer
(`R3.Domain/DivergenceFree/Regularity/FourierL2/RellichBall/SpatialCompactness/
TrilinearEstimate`). `import LerayHopf.Core` gives this layer without pulling in
either capstone's support modules.

## Top-level assembly — `LerayHopf.lean`

Re-exports `LerayHopf.Core` + `Torus.Capstone` + `R3Capstone`, plus the remaining
sorry-carrying files needed to build both capstones end to end (Bochner layer, the
Torus/R3 analytic-frontier files listed above). See the module docstring in
`LerayHopf.lean` for the full import list and layering rationale.
