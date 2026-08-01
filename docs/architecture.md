# Architecture

A one-page module map of the ~95-file `LerayHopf/` tree, grouped by layer. For the
mathematical narrative see `docs/archive/REPORT.md` (historical) / `docs/formalization-review-ja.md`;
for the exact capstone claims see [`docs/claims-and-scope.md`](claims-and-scope.md);
for the axiom ledger see `HANDOFF.md` / `docs/STATUS.md`.

## Visual overview: code LOC treemap

![Lean source code treemap](assets/code-loc-treemap.svg)

Each rectangle is a Lean file — `LerayHopf.lean` itself, plus every file under
`LerayHopf/`; its area is proportional to **code LOC** — physical lines minus blank
lines and comment lines, as reported by [`cloc`](https://github.com/AlDanial/cloc).
Color marks the top-level module a file belongs to (`Torus/`, `R3/`, `Bochner/`,
`Analysis/`, `Galerkin/`, `Scratch/`, or the root-level group covering `LerayHopf.lean`
and the shared modules directly under `LerayHopf/`); the same group always maps to the
same color. Hovering a rectangle shows the full path and the code/comment/blank line
breakdown. Groups outside the generator's known-colour table — currently `Scratch/` —
are assigned from a fallback palette in first-seen path order, which keeps the
assignment deterministic and the whole figure within the Okabe–Ito colourblind-safe
set.

**This figure represents physical source size only.** It does not measure proof
difficulty, mathematical importance, or code quality, and it carries no weighting by
theorem/lemma count. Comment-heavy files (e.g. ones with long docstrings) are not
inflated: comment and blank lines are excluded from the area.

The SVG is static (no JavaScript) and reproducible: given the same Lean source tree,
regenerating it produces a byte-identical file. To regenerate:

```bash
cd tools/code-treemap
npm install   # installs the pinned cloc + d3-hierarchy versions, isolated from the Lake package
npm run build # writes ../../docs/assets/code-loc-treemap.svg and .json
```

`tools/code-treemap`'s `cloc` devDependency (the [AlDanial/cloc](https://github.com/AlDanial/cloc)
release published to npm) is GPL-2.0-licensed. It runs as an unmodified, separate
command-line tool invoked as a subprocess during measurement only — it is not linked
into, vendored into, or distributed as part of the repository's own Apache-2.0-licensed
code (Lean sources or otherwise); nothing from `cloc` ships in `docs/assets/code-loc-treemap.svg`
beyond the plain LOC counts it reports.

`npm run build` runs `cloc --by-file --json --quiet LerayHopf.lean LerayHopf` from the
repository root, then `tools/code-treemap/generate-code-loc-treemap.mjs` to lay out and
render the treemap with `d3-hierarchy`'s `treemapSquarify`. The companion
`docs/assets/code-loc-treemap.json` records the exact per-file `{path, code, comment,
blank}` data, the cloc version, and a `sourceDigest` — a sha256 hash computed only from
that per-file data, not from `git rev-parse HEAD` — so re-running the command against
the same Lean source tree reproduces the same digest regardless of which commit is
checked out or how many times the artifact itself has since been committed; the same
summary metadata (without the per-file list) is also embedded in the SVG's `<metadata>`
element.

This is a manually-updated snapshot, not a per-commit CI artifact — see
`tools/code-treemap/package.json` for the pinned tool versions and
[issue #191](https://github.com/uda-lab/leray-hopf/issues/191) for the update policy.

## Shared abstract layer (top-level, domain-neutral)

Reused unmodified by both 𝕋³ and ℝ³ — the key structural payoff of the design.

| File | Content |
|---|---|
| `LerayHopf/EvolutionTriple.lean` | `DissipativeEvolution` (pivot Hilbert space `H` + regularity functional + viscous/convection forms), `WeakFormNS`, `convForm_self_zero` |
| `LerayHopf/EnergyEstimate.lean` | `AbstractEnergyLaw`, the Galerkin energy identity, energy non-increase |
| `LerayHopf/EnergySkeleton.lean` | Abstract energy-inequality skeleton (scaffold-era, sorry-free) |
| `LerayHopf/BlowupLowerBound.lean` | Independent side branch (Branch A) |

## Generic Galerkin layer — `LerayHopf/Galerkin/`

Domain-neutral Galerkin-construction machinery factored out of code that used to be
duplicated (byte-for-byte in places) across the 𝕋³ and ℝ³ lanes (issue #112). Two
sub-tiers, in DAG order:

| File | Content |
|---|---|
| `DissipativeODE.lean` | Abstract dissipative-`C¹`-field forward-global ODE existence over any finite-dimensional real inner-product space `V`: the Picard–Lindelöf tiling/gluing argument, energy non-increase, solution uniqueness, and ambient-submodule transport (`coe_hasDerivAt`). Mathlib-only imports. |
| `QuadraticField.lean` | `FieldForms` — raw trilinear-convection + viscous form data on `V`, and the Riesz-representative Galerkin vector field it determines (`vectorField`, `vectorField_spec`, `forwardGlobalSolution_exists` via `DissipativeODE`). Imports only `DissipativeODE.lean` + mathlib. |
| `Domain.lean` | `Galerkin.Domain` — the ambient L² Hilbert space, closed divergence-free subspace, projector family, and the domain functionals (regularity predicate, Stokes pairing, dissipation, energy-bound integrand/RHS, test predicate) that parameterize the solution bundles; `NSFormCore` (the domain-neutral projection of the NS convection form) and `Domain.evolution : Domain → NSFormCore D → DissipativeEvolution`. Imports `EvolutionTriple.lean`. |
| `SolutionBundles.lean` | `Galerkin.SolutionData`, `Galerkin.LerayHopfSolution`, `Galerkin.CompactnessPackage`, and `Galerkin.exists_lerayHopf_from_package` — the generic proof-carrying solution structures both lanes' bundles specialize. Imports `Domain.lean`. |
| `GlobalContract.lean` | `Galerkin.IsLerayHopfOn` (the `Prop`-valued finite-horizon Leray–Hopf contract on a fixed curve — field-for-field twin of `LerayHopfSolution`), the round-trip equivalences, `Galerkin.GlobalLerayHopfSolution` (one curve valid at **every** `T > 0`, the literal `∃ u, ∀ T`), and the horizon-transfer lemmas `WeakFormNS.mono`/`WeakFormNS.congr_Icc`/`IsLerayHopfOn.mono`/`IsLerayHopfOn.congr_Icc`. Generic over `Galerkin.Domain`; both lanes instantiate. The global-in-time contract layer (issue #195, P1). Imports `SolutionBundles.lean`. |

`DissipativeODE.lean` and `QuadraticField.lean` have no `LerayHopf` consumers of their
own — they are pdelib-grade (see `docs/pdelib-staging.md`) and are reached only through
the per-lane `FieldForms` witnesses (`torusFieldForms` in `Torus/GalerkinODESolve.lean`,
`r3FieldForms` in `R3/GalerkinODEExistence.lean`) that replaced the two lanes' duplicated
CLM towers. `Domain.lean`/`SolutionBundles.lean` sit directly above `EvolutionTriple.lean`
and directly below both lanes' `SolutionInterfaces.lean`, which instantiate
`Galerkin.Domain` as `torusDomain` / `r3Domain 𝔊` and recover their existing bundle names
(`GalerkinSolutionData[_R3]`, `LerayHopfSolutionFull[_R3]`,
`GalerkinCompactnessPackageFull[_R3]`, `exists_lerayHopf_from_package_full[_R3]`) as
abbreviations of — for R3, an `extends`-extension of, carrying the R3-only finite-dim
enrichment field `viscous_curve_continuous` — the generic structures above. Every field
specializes definitionally to the current per-lane field, so constructor and projection
call sites are unchanged. `AubinLionsPackage` stays per-lane by design: the 𝕋³ and ℝ³
compactness statements genuinely differ (global vs. per-ball convergence), not just in
proof but in content (`docs/scratch/galerkin-domain-plan.md` §4 ruling (b)).

## Bochner abstract time layer — `LerayHopf/Bochner/`

Gelfand-triple / Bochner-space-in-time infrastructure. Consumed by both domains'
Aubin–Lions and limit-passage arguments; carries the project's remaining marked
`sorry`s (Lions–Magenes-class walls; see `HANDOFF.md` §4 and `AGENTS.md`). Since issue #147
the sorry-carrying files (`TimeSobolevAC.lean`, `TimeMollification.lean`,
`TimeMollifierInterval.lean`, `TimeSobolevExperimental.lean`) are reachable only via the
explicit opt-in `LerayHopf.Experimental`, not from root `import LerayHopf` — see the README's
"Import guide". `TimeSobolevExperimental.lean`'s `w1pTime_continuous_in_H` is restricted to
`p = q = 2`, not stated at the prior generic-`p,q` signature: issue #158 found that FALSE.

`GelfandTriple.lean`, `TimeSobolev.lean` (sorry-free), `TimeSobolevExperimental.lean`,
`TimeSobolevAC.lean`, `TimeConvolution.lean`, `TimeMollifierInterval.lean`,
`TimeMollification.lean`, `StepFunctionCompactness.lean`, `ScalarEquicontinuity.lean`,
`WeakLimitToolkit.lean`.

`DiagonalExtraction.lean` (sorry-free, PDE-independent) — the abstract nested-subsequence
diagonal machinery (`nestedComp`, `exists_diagonal_extraction`,
`tendsto_diag_of_tendsto_stage`): pure order theory over `ℕ → ℕ` extraction towers with no
PDE, domain, or Hilbert-space content, targeting an arbitrary limit filter. Issue #195 P3;
domain-neutral, so reusable by both lanes' global-in-time construction (consumed by the 𝕋³
lane's `Torus/DiagonalGalerkin.lean` and the ℝ³ lane's `R3/DiagonalGalerkin.lean`).

Imported by: `LerayHopf/R3/GoodRepresentative.lean`, `R3/SpacetimePrecompact.lean`,
`R3/AubinLionsLimitPassage.lean`, `R3/DiagonalGalerkin.lean`, `Torus/ModeCompactness.lean`,
`Torus/DiagonalGalerkin.lean`.

## Torus (𝕋³) lane — `LerayHopf/Torus/`

Spatial linear layer (axiom-free, sorry-free): `Basic.lean`, `Domain.lean`,
`FunctionSpaces.lean`, `SobolevTorus.lean`, `DivergenceFree.lean` (`L2Sigma`),
`Leray.lean` (`divSymbol`, Leray projection), `GalerkinProjection.lean`,
`VelocityGalerkin.lean`, `H1Sigma.lean` (`h1EnergySq`, `rellich_L2Sigma`),
`RellichEmbedding.lean` (the Fourier-tail Rellich crux, `rellich_seq_compact`).

Analytic frontier (formerly axiomatized, now proved): `ConvectionForm.lean`,
`ConvectionExtension.lean`, `EnergyConvection.lean`, `GalerkinScheme.lean`,
`GalerkinODESolve.lean` (hosts `torusFieldForms`, the `Galerkin.FieldForms` witness that
routes this lane's ODE vector field through `LerayHopf/Galerkin/QuadraticField.lean`),
`GalerkinODECapstone.lean` (**capstone**: `exists_lerayHopf_torus3`), `TestFamily.lean`,
`LimitPassage.lean`, `TraceEnergy.lean`, `ViscousLimit.lean`, `ProjectionAdjoint.lean`,
`ModeCompactness.lean`, `ModeTail.lean`, `AubinLionsAssembly.lean`.

Interface + re-export: `SolutionInterfaces.lean` (support layer: `Torus3NSForms`,
`torusDomain` and `Torus3NSForms.core` instantiating `LerayHopf/Galerkin/Domain.lean`,
`LerayHopfSolutionFull`, assembly helpers — the capstone itself now lives in
`GalerkinODECapstone.lean`), `Capstone.lean` (re-exports the full chain).

Global-in-time chain (𝕋³, issue #195): a diagonal-extraction chain downstream of the
finite-horizon `GalerkinODECapstone.lean` (`exists_lerayHopf_torus3`, unchanged) — all in
the release cone (`import LerayHopf`) and kernel-only (pinned by
`scripts/check-axioms-live.sh`):

- `DiagonalGalerkin.lean` (P3) — the torus diagonal weak-limit curve `W`:
  `exists_diagonal_weakly_convergent_galSeq` runs the stage recursion over the generic
  `Bochner/DiagonalExtraction.lean` machinery and returns one diagonal subsequence `δ`
  weakly convergent at every forward time, plus the separation lemma
  `L2Sigma_eq_of_forall_inner`.
- `KappaChainExit.lean` (P2) — the κ-generalized torus compactness chain threaded through
  the Aubin–Lions package, energy class, limit passage, and everywhere-weak representative
  pin at mode map `κ := δ`: `torus_kappaChain_exit` produces the per-horizon
  `P2ExitWitness`.
- `GlobalCapstone.lean` (**capstone**: `exists_global_lerayHopf_torus3`) — assembles a
  single curve `u : Time → L2Sigma` and one form bundle `F` for which the finite-horizon
  Leray–Hopf contract holds at **every** `T > 0` (global-in-time weak existence on
  `[0, ∞)`), by pinning every horizon's `P2ExitWitness` to the same diagonal `W` and
  transferring through the generic contract layer's `IsLerayHopfOn.congr_Icc`/`.mono`.

The generic contract layer it consumes is `LerayHopf/Galerkin/GlobalContract.lean` (P1)
and the abstract diagonal machinery is `LerayHopf/Bochner/DiagonalExtraction.lean` (P3) —
both domain-neutral and described in their own lanes above.

## ℝ³ lane — `LerayHopf/R3/`

Spatial linear layer (axiom-free, sorry-free): `Domain.lean`, `DivergenceFree.lean`
(`L2Sigma_R3`, weak-divergence × Schwartz test), `Regularity.lean` (`memH1VF_R3`,
`MemSobolev`), `FourierL2.lean`, `RellichBall.lean`, `SpatialCompactness.lean`,
`TrilinearEstimate.lean`, `CurlSchwartzConstruction.lean` (curl-of-Schwartz-potential
construction, `CurlSchwartzDense` — split out of `SchwartzDivFreeBasis.lean`, issue #113 PR-1).

Analytic frontier (formerly axiomatized, now proved): `GalerkinScheme.lean`,
`SchwartzDivFreeBasis.lean` (`r3GalerkinScheme_exists`), `GalerkinODE.lean`,
`GalerkinODEExistence.lean` (hosts `r3FieldForms`, the `Galerkin.FieldForms` witness that
routes this lane's ODE vector field through `LerayHopf/Galerkin/QuadraticField.lean`),
`GalerkinODESolve.lean`, `GalerkinODECapstone.lean`
(**capstone**: `exists_lerayHopf_r3`), `ArzelaAscoliTime.lean`,
`AubinLionsLimitPassage.lean` (Tier N/W/C — the `[0,T]`-window `weakFormNS`/`bForm` limit-passage
monoliths share a `RestrictAvgMeasure`-class bridge (`restrictAvgMeasure`,
`intervalIntegral_eq_restrictAvgMeasure_integral`, etc.) and are each split into named,
doc-stringed step lemmas — e.g. `weakFormNS_galerkinTest_uniform_dominator`,
`bForm_galerkin_crude_dominator_bound`, `weakFormNS_limit_G_integrable`,
`weakFormNS_limit_diff_bound` — issue #114 Tier 1 commit 3), `AubinLionsAssembly.lean`, `CurlDensity.lean`,
`CurlDensityCapstone.lean`, `CurlDensityH1.lean`, `GalerkinBasisH1.lean`,
`FrechetKolmogorov.lean`, `ConvectionOperator.lean`, `ConvectionForm.lean`,
`ConvectionExtension.lean`, `SobolevEmbedding.lean`,
`H1SigmaDensity.lean` (`h1Sigma_dense_in_L2Sigma` — split out of `SobolevEmbedding.lean`,
issue #113 PR-1), `EnergyClassConvection.lean`, `GalerkinCurveBounds.lean`,
`GalerkinTrilinearBound.lean`, `GalerkinTimeModulus.lean`, `SpacetimePrecompact.lean`,
`GoodRepresentative.lean`, `LimitPassage.lean`, `WeightedFourierCommute.lean`,
`StokesFourier.lean` (`stokesTestPairing_R3_eq_sum_inner_negLap`, the NS-specific
Plancherel–Laplacian reformulation of `stokesTestPairing_R3` as a weakly-continuous form —
split out of `CurlDensity.lean`, issue #113 PR-2), `EnergyWeakLsc.lean` (Tier E energy
inequality: `galerkin_norm_le_u0`/`kineticEnergy_lsc_bound` (kinetic-lsc half) and
`viscous_pointwise_lsc`/`viscous_lsc_under_strongL2` (viscous half, Fourier–Plancherel
weak-lsc route) — split out of `AubinLionsLimitPassage.lean`, issue #114 Tier 1 commit 1),
`SteklovAverages.lean` (`TimeCompactnessInput`, `spatialInput_R3_of_localRellich`, `steklovAvg`
and the Steklov interval-average building blocks, `galerkinSpaceTimeExtraction_R3` — split out
of `AubinLionsLimitPassage.lean`, issue #114 Tier 1 commit 2).

Interface + re-export: `SolutionInterfaces.lean` (support layer: `R3NSForms`,
`r3Domain`/`R3NSForms.core` instantiating `LerayHopf/Galerkin/Domain.lean`,
`GalerkinSolutionData_R3` extending `LerayHopf/Galerkin/SolutionBundles.lean`'s
`Galerkin.SolutionData` with the R3-only `viscous_curve_continuous` field,
`LerayHopfSolutionFull_R3`, assembly helpers — capstone itself in
`GalerkinODECapstone.lean`); root-level `LerayHopf/R3Capstone.lean` (re-exports the
full chain).

Global-in-time chain (ℝ³, issue #212): the diagonal-extraction chain downstream of the
finite-horizon `GalerkinODECapstone.lean` (`exists_lerayHopf_r3`, unchanged) — node-for-node
mirror of the merged 𝕋³ chain above, all in the release cone (`import LerayHopf`) and
kernel-only (pinned by `scripts/check-axioms-live.sh`). It consumes the same generic contract
layer (`LerayHopf/Galerkin/GlobalContract.lean`, P1) and abstract diagonal machinery
(`LerayHopf/Bochner/DiagonalExtraction.lean`, P3) as the torus lane:

- `DiagonalGalerkin.lean` (P3′, #216) — the ℝ³ diagonal weak-limit curve `W`:
  `exists_diagonal_weakly_convergent_galSeq_R3` runs the κ-generic stage recursion over the
  generic `Bochner/DiagonalExtraction.lean` machinery, and `exists_diag_coherent_representative_R3`
  promotes the spike-(a) coherence core against the packaged `(δ, W)` output (returning the
  per-horizon coherence handle P4′ consumes), plus the separation lemma
  `L2Sigma_R3_eq_of_forall_inner`.
- `KappaChainExit.lean` (P2′, #215) — the κ-generalized ℝ³ compactness chain threaded through
  the Aubin–Lions package, energy class, limit passage, and everywhere-weak representative pin
  at mode map `κ := δ`: `r3_kappaChain_exit` produces the per-horizon `R3KappaChainExitWitness`.
- `GlobalCapstone.lean` (statement layer P1′ #214; **capstone** P4′ #217:
  `exists_global_lerayHopf_r3`) — freezes the target `GlobalR3CapstoneStatement` and the easy
  direction `globalR3Capstone_implies_finite`, then assembles a single scheme `𝔊`, form bundle
  `F`, and ONE curve `u : Time → L2Sigma_R3` for which the finite-horizon Leray–Hopf contract
  holds at **every** `T > 0` (global-in-time weak existence on `[0, ∞)`), by pinning every
  horizon's `R3KappaChainExitWitness` to the same diagonal `W` and transferring through the
  generic contract layer's `IsLerayHopfOn.congr_Icc`/`.mono`.

## Generic analysis layer — `LerayHopf/Analysis/`

Domain-neutral analytic infrastructure with **zero Galerkin/solution-package imports** —
pure `Lp`/Fourier/Schwartz/tensor-algebra facts that happen to be needed by both the Torus and
ℝ³ analytic frontiers, extracted out of the lane-specific files that originally carried them
(issue #111, issue #113 PR-2). This is the layer earmarked as `pdelib` lift candidates (issue
#113 PR-4 tracks writing up the staging plan) — none of it depends on
`GalerkinScheme`/`SolutionInterfaces` (either lane), so any of it can migrate to a standalone
package without pulling the NS-specific solution machinery along.

| File | Content |
|---|---|
| `TensorEdgeGluing.lean` | Shared tensor/edge-gluing layer for the `(S⊗V)+(V⊗S)`-determined bilinear-form reconstruction (issue #111 PR-1) |
| `PlancherelKernels.lean` | Shared gradient–Fourier Plancherel kernels (issue #111 PR-2) |
| `BilinearExtension.lean` | Extend a bounded bilinear form off a dense submodule to the whole space (issue #111 PR-4) |
| `TensorIntersection.lean` | `S⊗V ∩ V⊗S = S⊗S` linear-algebra lemma. Relocated from `R3/` (issue #113 PR-2); namespace kept as `LerayHopf.R3.TensorIntersection` for name stability, so its path and namespace deliberately disagree — see the file's own docstring |
| `RealComplexLpBridge.lean` | Real-part CLM `L²(ℝ³;ℂ) → L²(ℝ³;ℝ)` and bounded real-multiplier `L²` infrastructure, extracted from `R3/EnergyClassConvection.lean` (issue #113 PR-2) |
| `SpectralWeakGradient.lean` | The spectral H¹ weak-gradient component `gradComp_of_memH1` and its IBP identity, extracted from `R3/EnergyClassConvection.lean` (issue #113 PR-2) |
| `LpInterpolation.lean` | `L²∩L⁶ ↪ L³` Hölder interpolation plus component `MemLp` facts, extracted from `R3/EnergyClassConvection.lean` (issue #113 PR-2) |
| `WeakLeibniz.lean` | H¹·H¹ weak Leibniz product rule via Schwartz approximation, extracted from `R3/EnergyClassConvection.lean` (issue #113 PR-2) |
| `FourierParseval.lean` | `schwartzC` complexification, the vector Parseval bridge, Hermitian-reality facts, and the du Bois-Reymond Hermitian/anti-Hermitian preimage machinery, extracted from `R3/CurlDensity.lean` (issue #113 PR-2) |
| `BoundedMultiplier.lean` | Bounded real-multiplier operator on `Lp ℂ 2 μ` (self-adjoint, `C`-Lipschitz, commutes with Bochner interval integration) over an arbitrary measure space, extracted from `R3/WeightedFourierCommute.lean` (issue #113 PR-4) |

## Shared spatial core — `LerayHopf/Core.lean`

Collects everything above that is **project-axiom-free** and `sorryAx`-free:
`Torus.Basic/Domain/FunctionSpaces/DivergenceFree/SobolevTorus/Leray/
GalerkinProjection/VelocityGalerkin`, `EnergySkeleton`,
`BlowupLowerBound`, and the ℝ³ spatial/Fourier sublayer
(`R3.Domain/DivergenceFree/Regularity/FourierL2/RellichBall/SpatialCompactness/
TrilinearEstimate`). `import LerayHopf.Core` gives this layer without pulling in
either capstone's support modules. (`LerayHopf/Galerkin/` is axiom-free and
sorry-free too, but is imported directly by the root `LerayHopf.lean`, not by `Core` —
see the next section.)

## Top-level assembly — `LerayHopf.lean`

Re-exports `LerayHopf.Core` + the generic `LerayHopf.Galerkin` layer (`DissipativeODE`,
`QuadraticField`, `Domain`, `SolutionBundles`) + `Torus.Capstone` + `R3Capstone`, plus the
remaining supporting files needed to build both capstones end to end (the sorry-free part of
the Bochner layer, the Torus/R3 analytic-frontier files listed above). Since issue #147 this
is a **sorry-free release surface**, and since issue #151 additionally **axiom-free and free
of placeholder namespaces**, statically enforced by `scripts/check-release-cone.sh`: the four
still-incomplete Bochner modules are NOT among these remaining files — they live behind the
explicit opt-in `LerayHopf.Experimental` instead (see the Bochner section above).
See the module docstring in `LerayHopf.lean` for the full import list and layering rationale.

## History and provenance

Both capstones are long past the design-and-roadmap stage; the following documents are
kept for provenance, not as current guidance: [`docs/archive/milestone.md`](archive/milestone.md),
[`docs/archive/leray_hopf_lean_mvp_plan.md`](archive/leray_hopf_lean_mvp_plan.md),
[`docs/archive/ROADMAP.md`](archive/ROADMAP.md), [`docs/archive/REPORT.md`](archive/REPORT.md).
