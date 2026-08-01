# Leray–Hopf weak existence in Lean

[![Release-candidate build attestation](https://github.com/uda-lab/leray-hopf/actions/workflows/release-attestation.yml/badge.svg?event=workflow_dispatch)](https://github.com/uda-lab/leray-hopf/actions/workflows/release-attestation.yml)

> The badge links to on-demand build attestations for individual commits, not a
> per-commit CI signal — see [`docs/build-and-checks.md`](docs/build-and-checks.md)
> for what it does and does not certify.

A Lean 4 + mathlib formalization of **Leray–Hopf weak existence** for the
incompressible Navier–Stokes equations, on the periodic 3-torus 𝕋³ and on whole
space ℝ³. Each domain carries a finite-horizon capstone and a global-in-time
capstone — four machine-checked existence theorems in all — and every one of them
is **kernel-only**: `#print axioms` returns only the standard kernel axioms
(`propext`, `Classical.choice`, `Quot.sound`), with zero project axioms and no
`sorryAx`. This repository does **not** claim smoothness or higher regularity
beyond the stated energy-class properties, nor uniqueness or non-uniqueness of the
solutions it constructs.

**Start here:** [**uda-lab.github.io/leray-hopf-notes**](https://uda-lab.github.io/leray-hopf-notes/)
is an interactive, browsable companion to this repository — it presents the Lean
declarations, their dependency graph, Japanese-language mathematical exposition, and
per-declaration proof status.

## Explore the formalization

- **Interactive notes (Japanese exposition):** <https://uda-lab.github.io/leray-hopf-notes/>
- **Lean source:** [`LerayHopf/`](LerayHopf/)
- **Architecture / module map:** [`docs/architecture.md`](docs/architecture.md)
- **Exact claims and scope:** [`docs/claims-and-scope.md`](docs/claims-and-scope.md)
- **Citation:** [`CITATION.cff`](CITATION.cff)

## Main results

```lean
-- LerayHopf/Torus/GalerkinODECapstone.lean   (𝕋³)
theorem exists_lerayHopf_torus3 (u₀ : L2Sigma) (ν : ℝ) (hν : 0 < ν)
    (T : ℝ) (hT : 0 < T) :
    ∃ F : Torus3NSForms, Nonempty (LerayHopfSolutionFull F ν T u₀)

-- LerayHopf/R3/GalerkinODECapstone.lean      (ℝ³)
theorem exists_lerayHopf_r3 (u₀ : L2Sigma_R3) (ν : ℝ) (hν : 0 < ν)
    (T : ℝ) (hT : 0 < T) :
    ∃ (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊),
      Nonempty (LerayHopfSolutionFull_R3 𝔊 F ν T u₀)
```

```lean
-- LerayHopf/Torus/GlobalCapstone.lean   (𝕋³, global-in-time)
theorem exists_global_lerayHopf_torus3 (u₀ : L2Sigma) (ν : ℝ) (hν : 0 < ν) :
    ∃ F : Torus3NSForms, ∃ u : Time → L2Sigma, ∀ T : ℝ, 0 < T →
      Galerkin.IsLerayHopfOn torusDomain F.core ν T u₀ u

-- LerayHopf/R3/GlobalCapstone.lean      (ℝ³, global-in-time)
theorem exists_global_lerayHopf_r3 (u₀ : L2Sigma_R3) (ν : ℝ) (hν : 0 < ν) :
    ∃ (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊), ∃ u : Time → L2Sigma_R3,
      ∀ T : ℝ, 0 < T → Galerkin.IsLerayHopfOn (r3Domain 𝔊) F.core ν T u₀ u
```

For any divergence-free initial data `u₀` in `L²` and viscosity `ν > 0`, a
Leray–Hopf weak solution exists on `𝕋³` (unit-period torus) and on `ℝ³` alike, and it
is proof-carrying rather than merely asserted in prose. The curve is divergence-free
at the level of its type — it is valued in the closed divergence-free subspace `σ` —
and the `LerayHopfSolutionFull` structure returned by the finite-horizon capstones
carries five proof fields: the weak Navier–Stokes identity, the energy inequality, the
one-sided initial trace at `t → 0⁺`, the energy class (a.e.-in-time H¹ membership plus
integrable viscous dissipation), and time-measurability of the curve in ambient `L²`.

The finite-horizon capstones take the horizon `T > 0` as input and return a solution
on `[0, T]`. The global capstones instead fix a **single** curve `u : Time → L²_σ` and
one form bundle `F` (on ℝ³, also one Galerkin scheme `𝔊`), and assert the Prop-valued
contract `Galerkin.IsLerayHopfOn` — the field-for-field twin of that same structure,
with the curve taken as an argument rather than bundled as data — at **every** `T > 0`
simultaneously. That is global-in-time weak existence on `[0, ∞)`, not a family of
independently chosen finite-horizon witnesses. The same result in structure form is
`exists_globalLerayHopfSolutionFull_torus3` / `…_r3`, which return
`Nonempty (GlobalLerayHopfSolutionFull …)`.

The precise field-by-field statement of what each part of the solution structure
guarantees — and, just as importantly, what it does not — is
[`docs/claims-and-scope.md`](docs/claims-and-scope.md).

## Scope and limitations

- **No external force** — the homogeneous Navier–Stokes equation only.
- **Global in time, but weak solutions only** — the global capstones give one curve
  satisfying the Leray–Hopf contract at every `T > 0` simultaneously, i.e. on
  `[0, ∞)`; coherence across horizons is pointwise (`u t` is one curve), not an
  a.e. gluing. The energy relation is the **inequality**, not equality.
- **𝕋³ is the unit torus** (period 1 in each coordinate), with no periodicity
  assumption on ℝ³.
- **Separated-variable weak formulation**: test functions are `ψ(t)·w(x)`, not a
  general space-time test function.
- **No smoothness or higher regularity beyond the stated energy-class
  properties** (a.e.-in-time H¹ membership plus integrable viscous dissipation);
  **uniqueness and non-uniqueness are not claimed.**
- **`LerayHopf.Experimental`** isolates incomplete, opt-in additional work; it is not
  reachable from the release surface below and not needed by any of the capstones.

See [`docs/claims-and-scope.md`](docs/claims-and-scope.md) for the exact, field-level
version of every bullet above.

## Verification status

- `import LerayHopf` is the release surface: it is `sorry`-free and project-axiom-free,
  enforced in CI (`scripts/check-release-cone.sh`).
- Build/toolchain-exact verification of a specific release-candidate commit is done by
  manual attestation (the badge above); see
  [`docs/build-and-checks.md`](docs/build-and-checks.md).
- The badge itself does not expire, but the workflow artifact and run log behind it are
  retention-limited. Durable copies of that evidence are stored as
  [Release assets](https://github.com/uda-lab/leray-hopf/releases) (e.g.
  [`v0.1.0-rc1`](https://github.com/uda-lab/leray-hopf/releases/tag/v0.1.0-rc1)), which
  certify one exact SHA and are not subject to that Actions retention deadline — see
  "Durability caveat" in
  [`docs/build-and-checks.md`](docs/build-and-checks.md#durability-caveat).
- Incomplete additional work is isolated behind the explicit opt-in
  `import LerayHopf.Experimental`, never pulled in by `import LerayHopf`.

## Getting started

```lean
import LerayHopf
```

```bash
lake build
```

For the full import matrix (which import brings in what, and its exact
sorry/axiom status), the CI policy, and how to reproduce a release attestation, see
[`docs/build-and-checks.md`](docs/build-and-checks.md) and
[`docs/claims-and-scope.md`](docs/claims-and-scope.md).

## Repository map

The area of each rectangle is proportional to the number of non-comment,
non-blank lines (code LOC) in the corresponding Lean source file, covering
[`LerayHopf.lean`](LerayHopf.lean) and every file under [`LerayHopf/`](LerayHopf/);
color marks the top-level module a file belongs to.

[![Lean source code treemap](docs/assets/code-loc-treemap.svg)](docs/assets/code-loc-treemap.svg)

See [`docs/architecture.md`](docs/architecture.md#visual-overview-code-loc-treemap)
for the full-size figure, the measurement method, and how to regenerate it.

## Star History

[Star history for `uda-lab/leray-hopf`](https://www.star-history.com/#uda-lab/leray-hopf&Date)

> The inline chart embed was removed rather than left broken (issue #230 / #189): the
> authenticated embed's token no longer resolves, and Star History cannot serve this
> repository's star data anonymously either. See the runbook in
> [`docs/build-and-checks.md`](docs/build-and-checks.md#readme-star-history-embed-issue-189)
> for how to restore the embed. Star counts are not evidence of anything mathematical.

## Documentation, contributing, citation, license

- [`docs/architecture.md`](docs/architecture.md) — module map.
- [`docs/claims-and-scope.md`](docs/claims-and-scope.md) — exact claims table and
  import guide.
- [`docs/STATUS.md`](docs/STATUS.md) — axiom/`sorry` ledger and integrity backstop.
- [`docs/build-and-checks.md`](docs/build-and-checks.md) — build, discipline checks,
  CI policy, and the Star History embed runbook (diagnosis and restoration).
- [`CONTRIBUTING.md`](CONTRIBUTING.md) — build-cost policy, statement-changing PR
  review requirement, and issue/PR conventions.
- [`SECURITY.md`](SECURITY.md) — soundness issues, guard bypasses, and supply-chain
  concerns.
- [`CITATION.cff`](CITATION.cff) — citation metadata; cite via GitHub's "Cite this
  repository" or this file directly.
- [`LICENSE`](LICENSE) — Apache License 2.0. Copyright 2026 Tomoki Uda. The license
  covers the Lean formalization code and repository materials; it does not purport to
  license mathematical facts or theorems themselves.
