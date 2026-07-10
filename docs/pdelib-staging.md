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

## Candidates

| File | Description | Lift-readiness | Blockers |
|---|---|---|---|
| `LerayHopf/Bochner/TimeSobolev.lean` | Lions–Magenes vector-valued time-Sobolev apparatus: `IsWeakTimeDeriv`, the abstract Gelfand-triple embedding `H ↪ V'`, `W1pTime`. | verbatim-ready (after issue #113 PR-4 commit 3, which deleted the dead `GelfandTriple.ιCLM` shim) | One pre-existing `ALLOW_SORRY` (`w1pTime_continuous_in_H`, line ~535 — a declared months-class Lions–Magenes good-representative residual); the statement is intact and the gap is tracked, not hidden. |
| `LerayHopf/Bochner/TimeSobolevAC.lean` | The absolutely-continuous-in-time good representative built on top of `TimeSobolev.lean`. | verbatim-ready | None found; imports only `TimeSobolev.lean` and mathlib. |
| `LerayHopf/Bochner/WeakLimitToolkit.lean` | Generic Hilbert-space weak-limit toolkit (no project imports at all). | verbatim-ready | None. |
| `LerayHopf/EvolutionTriple.lean` | `DissipativeEvolution` (abstract bundle: Hilbert space + regularity/viscous/convection forms) and `WeakFormNS` (the abstract weak-NS predicate). | verbatim-ready | Two dead imports (`LerayHopf.Torus.Basic`, `LerayHopf.EnergyEstimate`) are present but unused anywhere in the file body — trivial one-line cleanup before lift, not a mathematical blocker. **Settled interface-shape decision** (from the issue #113 PR-3 interface-hardening pass): a typeclass-parameterized alternative to the bundled-structure design was evaluated and rejected, since NS admits multiple non-canonical `DissipativeEvolution`/`GelfandTriple` instances on the same underlying space (e.g. different `isTest` predicates), which a global typeclass instance cannot represent; the bundled-structure-plus-`letI` idiom used throughout this file and `GelfandTriple.lean` is the correct mathlib-style fit and should carry over as-is. |
| `LerayHopf/Analysis/*.lean` (10 modules: `BilinearExtension`, `BoundedMultiplier`, `FourierParseval`, `LpInterpolation`, `PlancherelKernels`, `RealComplexLpBridge`, `SpectralWeakGradient`, `TensorEdgeGluing`, `TensorIntersection`, `WeakLeibniz`) | The generic analysis layer: no Galerkin/solution-package imports by construction (a standing invariant of this directory). `BoundedMultiplier.lean` (issue #113 PR-4 commit 2) is generic over an arbitrary measure space `{X} [MeasurableSpace X] (μ : Measure X)`; the rest were extracted generic in earlier PRs. | verbatim-ready by construction | Six modules in this layer (`FourierParseval`, `LpInterpolation`, `PlancherelKernels`, `RealComplexLpBridge`, `SpectralWeakGradient`, `WeakLeibniz`) still `import` concrete `LerayHopf.R3.*` files (`FourierL2`, `SobolevEmbedding`, `Regularity`, or just `Domain` for the base `Domain3`/`L2VF_R3` types) for supporting lemmas even though their own statements are generic; a real lift needs those supporting facts re-derived or re-imported against the generic space too. `BilinearExtension`, `BoundedMultiplier`, `TensorEdgeGluing`, `TensorIntersection` have no such R3 import and are lift-ready with zero further work. |
| `LerayHopf/R3/TrilinearEstimate.lean` | Concrete trilinear convection estimates for `convIntegralSchwartz` (Cauchy–Schwarz bounds, IBP antisymmetry under div-free). | lift-ready (private local-helper block only, after issue #113 PR-4 commit 1) | Only the private Schwartz-analysis helpers (`schwartzMul`, `schwartz_cauchy_schwarz`, `schwartz_trilinear_bound`, etc.) were generalized to `Fin n`/`EuclideanSpace ℝ (Fin n)`. The public Tier A/B/C theorems (`convIntegralSchwartz_*`) are inherently pinned to `Fin 3`/`Domain3` because they state facts about `convIntegralSchwartz` itself, which is a concrete `Domain3`-typed definition in `DivergenceFree.lean` — those stay R3-specific and are not lift candidates as stated. |
| `LerayHopf/R3/FrechetKolmogorov.lean` (abstract halves) | Fréchet–Kolmogorov L²-precompactness criterion; the equicontinuity/boundedness-implies-totally-bounded argument is classical general-metric-space analysis. | reprove-class | `totallyBounded_image_of_equicont_bdd` (and its neighbors) are stated and proved directly against `L2ballR3`/`Domain3`. Genericizing to an abstract metric/measure space is real analysis work (re-deriving the argument against an abstract translation/mollification setup), not a mechanical extraction — flagged, not attempted in this pass. |
| `gns_L6_of_memH1_R3` (`LerayHopf/R3/SobolevEmbedding.lean`) | Gagliardo–Nirenberg–Sobolev embedding `H¹(ℝ³) ↪ L⁶`. | do-not-generalize | The exponent 6 is dimension-critical (`2n/(n-2)` at `n=3`); there is no dimension-generic statement to lift — this belongs in `pdelib` only as a worked `n=3` instance, if at all. |
| `LerayHopf/Torus/SobolevTorus.lean` | Hand-built torus Sobolev space `H¹(𝕋³)` (mathlib currently lacks a torus Sobolev embedding). | reprove-class | Genuine mathlib gap-fill: the content is valuable as a `pdelib` contribution but is presently built directly against `LerayHopf.Torus.FunctionSpaces`'s `d=3` Fourier basis, so it would need reproving against a `d`-generic torus Fourier basis, not copying. |
| `LerayHopf/Torus/FunctionSpaces.lean` | Concrete `d=3` torus Fourier-mode machinery (`torus3_mFourierBasis`, `mFourierCoeff3`, Parseval identity). | do-not-lift-retrofit | Used pervasively (400+ call sites across 6 files in the T³ solution package) as a thin `d=3` instantiation. Deviation from a literal "generalize in place" reading of the issue: a `d`-generic wrapper around this content would be genuinely new `pdelib`-side work (reproving the Fourier-mode indexing and Parseval identity for general `d`), not a retrofit of what exists here — recorded so this file isn't mistaken for an oversight. |

## See also

[`docs/architecture.md`](architecture.md) documents the current module layering
(including the `Analysis/` generic layer) as it stands in this repository, independent
of the `pdelib` migration question addressed here.
