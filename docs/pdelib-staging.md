# pdelib staging inventory

`pdelib` is an external, more general PDE-analysis Lean library that this repository's
generic (non-Navier–Stokes-specific) content is a natural fit for. This document is
the tracking inventory for that eventual migration (issue #113 deliverable (5)): it
lists candidate files, states how ready each is to move **verbatim** or whether it
needs further generalization work first, and records the blockers for the rest.

This is a staging *list*, not a migration plan — no file listed here has moved, and
nothing in this repo depends on `pdelib` existing. Lift-readiness is judged purely by
whether the content is genuinely domain-neutral (no `Fin 3`/`Domain3`/torus-specific
facts, no dependence on the Galerkin/solution-package layers), not by any external
scheduling.

## Readiness categories

- **verbatim-ready** — no project-specific types or facts; could be copied into
  `pdelib` today with at most an import-path rename.
- **lift-ready** — domain-neutral after generalization work already done in this
  repo (i.e. the generalization is the PR that made it lift-ready, not remaining work).
- **reprove-class** — the *shape* of the result is domain-neutral and worth having in
  `pdelib`, but the current Lean proof is still typed against a concrete space here;
  moving it means genuinely reproving the abstract statement, not copying code.
- **do-not-generalize** — the result is inherently dimension- or domain-specific;
  listed here only so it isn't mistaken for an omission.
- **do-not-lift-retrofit** — a thin domain-specific instantiation whose only
  "generic" content is what already lives in the modules it wraps; building a
  general-purpose wrapper around it would be new `pdelib`-side work, not a retrofit
  of existing code.
- **needs-import-cleanup** — the module's own statements are domain-neutral, but it
  still imports one or more concrete `LerayHopf.R3.*` files; whether the cleanup is
  a mechanical re-point (the import supplies only type aliases the module could get
  more cheaply) or requires reproving a genuine R3-specific fact generically depends
  on the module — see the per-module breakdown below, do not assume it's always
  mechanical.

## Candidates

| File | Description | Lift-readiness | Blockers |
|---|---|---|---|
| `LerayHopf/Bochner/TimeSobolev.lean` | Lions–Magenes vector-valued time-Sobolev apparatus: `IsWeakTimeDeriv`, the abstract Gelfand-triple embedding `H ↪ V'`, `W1pTime`. | verbatim-ready (after issue #113 PR-4 commit 3, which deleted the dead `GelfandTriple.ιCLM` shim) | One pre-existing `ALLOW_SORRY` (`w1pTime_continuous_in_H`, line ~535 — a declared months-class Lions–Magenes good-representative residual); the statement is intact and the gap is tracked, not hidden. |
| `LerayHopf/Bochner/TimeSobolevAC.lean` | The absolutely-continuous-in-time good representative built on top of `TimeSobolev.lean`. | verbatim-ready | None found; imports only `TimeSobolev.lean` and mathlib. |
| `LerayHopf/Bochner/WeakLimitToolkit.lean` | Generic Hilbert-space weak-limit toolkit (no project imports at all). | verbatim-ready | None. |
| `LerayHopf/EvolutionTriple.lean` | `DissipativeEvolution` (abstract bundle: Hilbert space + regularity/viscous/convection forms) and `WeakFormNS` (the abstract weak-NS predicate). | verbatim-ready | Two dead imports (`LerayHopf.Torus.Basic`, `LerayHopf.EnergyEstimate`) are present but unused anywhere in the file body — trivial one-line cleanup before lift, not a mathematical blocker. **Settled interface-shape decision** (from the issue #113 PR-3 interface-hardening pass): a typeclass-parameterized alternative to the bundled-structure design was evaluated and rejected, since NS admits multiple non-canonical `DissipativeEvolution`/`GelfandTriple` instances on the same underlying space (e.g. different `isTest` predicates), which a global typeclass instance cannot represent; the bundled-structure-plus-`letI` idiom used throughout this file and `GelfandTriple.lean` is the correct mathlib-style fit and should carry over as-is. |
| `LerayHopf/Galerkin/DissipativeODE.lean` | Abstract dissipative-`C¹`-field forward-global finite-dimensional ODE existence (Picard–Lindelöf tiling/gluing, energy non-increase, solution uniqueness, ambient-submodule transport) over any `[FiniteDimensional ℝ V]` real inner-product space, extracted from the (formerly duplicated) 𝕋³/ℝ³ Galerkin ODE solvers (issue #112 PR-A). | verbatim-ready | Mathlib-only imports; zero project imports. |
| `LerayHopf/Galerkin/QuadraticField.lean` | `FieldForms` — generic trilinear-convection + viscous form data on a finite-dimensional real inner-product space, and the Riesz-representative Galerkin vector field it determines (`vectorField`, `forwardGlobalSolution_exists`); deduplicates the two lanes' CLM towers (issue #112 PR-A). | verbatim-ready | Imports mathlib plus `Galerkin.DissipativeODE` (itself mathlib-only, verbatim-ready above); no NS/domain/Galerkin-scheme content. |
| `LerayHopf/Galerkin/{Domain,SolutionBundles}.lean` | The evolution-PDE Galerkin-interface staging: `Galerkin.Domain` (ambient Hilbert space + closed subspace + projector family + domain functionals), `NSFormCore`, `Domain.evolution`, and the generic proof-carrying solution structures `Galerkin.SolutionData`/`LerayHopfSolution`/`CompactnessPackage` that both lanes' bundles specialize (issue #112 PR-C). | lift-ready (once `EvolutionTriple.lean` lifts) | Higher coupling than the two files above: imports `LerayHopf.EvolutionTriple`, so lift-readiness is contingent on that file's own (already verbatim-ready) migration; no independent blocker in these two files themselves. |
| `LerayHopf/Analysis/{BilinearExtension,BoundedMultiplier,TensorEdgeGluing,TensorIntersection}.lean` | Zero-project-import quarter of the generic analysis layer: no Galerkin/solution-package imports, and no `LerayHopf.R3.*` imports at all. `BoundedMultiplier.lean` (issue #113 PR-4 commit 2) is generic over an arbitrary measure space `{X} [MeasurableSpace X] (μ : Measure X)`; the other three were extracted generic in earlier PRs (issue #111 PR-1/PR-4, issue #113 PR-2). | verbatim-ready | None. |
| `LerayHopf/Analysis/{FourierParseval,LpInterpolation,PlancherelKernels,RealComplexLpBridge,SpectralWeakGradient,WeakLeibniz}.lean` | The other six analysis modules: no Galerkin/solution-package imports (the layer's standing invariant), but each still `import`s one or more concrete `LerayHopf.R3.*` files. | needs-import-cleanup | Heterogeneous — not uniformly mechanical, checked per module rather than assumed: `PlancherelKernels` (imports `R3.Domain`) and `RealComplexLpBridge` (imports `R3.Regularity`, but the only symbols it actually uses — `Domain3`, `L2C_R3` — are type aliases from `R3.Domain`, reachable through a heavier import than necessary) use nothing but `Domain3`/`L2C_R3`-class type aliases, so their cleanup really is a mechanical re-point. The other four are not: `SpectralWeakGradient` genuinely uses `R3.Regularity`'s `memH1VF_R3` predicate and its algebraic closure lemmas (a substantive H¹(ℝ³) membership definition, not a type alias); `FourierParseval` genuinely uses `R3.FourierL2.fourier_translate_eq` (a proved fact, not a type); `LpInterpolation` and `WeakLeibniz` both call `gns_L6_of_memH1_R3`/`gns_L6_schwartz` from `R3.SobolevEmbedding` — the same dimension-critical GNS embedding marked do-not-generalize elsewhere in this table, so these two cannot be made generic at all without first replacing that dependency with a genuinely `n`-generic Sobolev embedding, which does not currently exist in this repo. |
| `LerayHopf/R3/TrilinearEstimate.lean` | Concrete trilinear convection estimates for `convIntegralSchwartz` (Cauchy–Schwarz bounds, IBP antisymmetry under div-free). | lift-ready (private local-helper block only, after issue #113 PR-4 commit 1) | Only the private Schwartz-analysis helpers (`schwartzMul`, `schwartz_cauchy_schwarz`, `schwartz_trilinear_bound`, etc.) were generalized to `Fin n`/`EuclideanSpace ℝ (Fin n)`. The public Tier A/B/C theorems (`convIntegralSchwartz_*`) are inherently pinned to `Fin 3`/`Domain3` because they state facts about `convIntegralSchwartz` itself, which is a concrete `Domain3`-typed definition in `DivergenceFree.lean` — those stay R3-specific and are not lift candidates as stated. |
| `LerayHopf/R3/FrechetKolmogorov.lean` (abstract halves) | Fréchet–Kolmogorov L²-precompactness criterion; the equicontinuity/boundedness-implies-totally-bounded argument is classical general-metric-space analysis. | reprove-class | `totallyBounded_image_of_equicont_bdd` (and its neighbors) are stated and proved directly against `L2ballR3`/`Domain3`. Genericizing to an abstract metric/measure space is real analysis work (re-deriving the argument against an abstract translation/mollification setup), not a mechanical extraction — flagged, not attempted in this pass. |
| `gns_L6_of_memH1_R3` (`LerayHopf/R3/SobolevEmbedding.lean`) | Gagliardo–Nirenberg–Sobolev embedding `H¹(ℝ³) ↪ L⁶`. | do-not-generalize | The exponent 6 is dimension-critical (`2n/(n-2)` at `n=3`); there is no dimension-generic statement to lift — this belongs in `pdelib` only as a worked `n=3` instance, if at all. |
| `LerayHopf/Torus/SobolevTorus.lean` | Hand-built torus Sobolev space `H¹(𝕋³)` (mathlib currently lacks a torus Sobolev embedding). | reprove-class | Genuine mathlib gap-fill: the content is valuable as a `pdelib` contribution but is presently built directly against `LerayHopf.Torus.FunctionSpaces`'s `d=3` Fourier basis, so it would need reproving against a `d`-generic torus Fourier basis, not copying. |
| `LerayHopf/Torus/FunctionSpaces.lean` | Concrete `d=3` torus Fourier-mode machinery (`torus3_mFourierBasis`, `mFourierCoeff3`, Parseval identity). | do-not-lift-retrofit | Used pervasively (400+ call sites across 6 files in the T³ solution package) as a thin `d=3` instantiation. Deviation from a literal "generalize in place" reading of the issue: a `d`-generic wrapper around this content would be genuinely new `pdelib`-side work (reproving the Fourier-mode indexing and Parseval identity for general `d`), not a retrofit of what exists here — recorded so this file isn't mistaken for an oversight. |

## See also

[`docs/architecture.md`](architecture.md) documents the current module layering
(including the `Analysis/` generic layer) as it stands in this repository, independent
of the `pdelib` migration question addressed here.
