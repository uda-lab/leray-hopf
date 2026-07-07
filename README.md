# lean-pde

A Lean 4 + mathlib formalization of **Leray–Hopf weak existence** for the
incompressible Navier–Stokes equations, on the periodic 3-torus 𝕋³ and on whole
space ℝ³.

## What is actually proved

Two capstone existence theorems are proved and machine-checked, each **conditional on
an explicitly listed, finite set of analytic axioms** (plus the three standard kernel
axioms `propext` / `Classical.choice` / `Quot.sound`, and **no `sorryAx`**):

```lean
-- LerayHopf/TorusGalerkinODECapstone.lean   (𝕋³)
theorem exists_lerayHopf_torus3_axiomatic (u₀ : L2Sigma) (ν : ℝ) (hν : 0 < ν)
    (T : ℝ) (hT : 0 < T) :
    ∃ F : Torus3NSForms, Nonempty (LerayHopfSolutionFull F ν T u₀)

-- LerayHopf/R3/GalerkinODECapstone.lean      (ℝ³)
theorem exists_lerayHopf_r3_axiomatic (u₀ : L2Sigma_R3) (ν : ℝ) (hν : 0 < ν)
    (T : ℝ) (hT : 0 < T) :
    ∃ (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊),
      Nonempty (LerayHopfSolutionFull_R3 𝔊 F ν T u₀)
```

The current project-axiom frontier is **𝕋³ = 0 project axioms (unconditional), ℝ³ = 1 axiom**,
pinned exactly by `scripts/check-axioms-live.sh` (a CI gate that runs `#print axioms` and
fails on any unexpected or missing axiom, or any `sorryAx`):

- **𝕋³:** no project axioms — `#print axioms` returns kernel axioms only (`propext`,
  `Classical.choice`, `Quot.sound`). `aubin_lions` was REMOVED (issue #23, PR #89) and is
  now the proved `noncomputable def torusAubinLionsPackage_of_galSeq`
  (`LerayHopf/TorusAubinLionsAssembly.lean`) via the mode-wise spectral route.
- **ℝ³:** `galerkin_limit_passage_R3`

(The former 𝕋³ `galerkin_limit_passage` axiom was removed by PR #75 / issue #25 — it is
now proved via `torus_galerkin_limit_passage_of_energyClass` +
`torus_energyClass_of_aubinLions`. The former ℝ³ `galerkin_spacetime_precompact_R3`
axiom was DISCHARGED on 2026-07-04 (issue #46, PR-4) — it is now a theorem, assembled
sorry-free via File E `LerayHopf/R3/SpacetimePrecompact.lean`.)

Everything else in the Galerkin construction — the functional-analytic backbone, the
finite-dimensional ODE solver, spatial Rellich–Kondrachov compactness, the
Aubin–Lions-in-time diagonalization, Helmholtz/curl density (Fourier route), the
Mazur weak-limit closure, and the determined-form convection extensions — is
**proved sorry-free**, not assumed.

> **Honest scope.** The 𝕋³ capstone `exists_lerayHopf_torus3_axiomatic` is now
> **unconditional** (`#print axioms` returns kernel axioms only; `aubin_lions` was removed
> via the mode-wise spectral route, issue #23 / PR #89). The remaining ℝ³ axiom
> (`galerkin_limit_passage_R3`) is a genuine analytic fact that Mathlib currently lacks
> (Lions–Magenes/good-representative limit passage); the former Aubin–Lions–Simon
> spacetime-precompactness axiom is now a proved theorem (issue #46, PR-4). The convection
> forms are proof-carrying total trilinear extensions pinned to the genuine
> Schwartz/Galerkin test-class forms, with fixed-test continuity; they are not claims of
> a canonical continuous convection operator on all pure `L² × L² × L²` triples.
> No regularity, uniqueness, or non-uniqueness claim is made. The project's goal is to
> drive the ℝ³ axiom count to zero; the current frontier and remaining work are tracked
> in the open GitHub issues and [`docs/STATUS.md`](docs/STATUS.md).

Public summaries should cite the proof-carrying `LerayHopfSolutionFull` /
`LerayHopfSolutionFull_R3` structures and the `_axiomatic` capstones above. The older
generic `ExistsLerayHopf` / `LerayHopfSolution` layer is scaffold-only and should not
be described as a PDE existence theorem.

## Layout

- **Lean sources:** `LerayHopf/` — `R3/` (ℝ³), `Bochner/` (Gelfand-triple time theory),
  `Core/`, and the top-level `Torus*` / `*.lean` files (𝕋³ and shared infrastructure).
- **Mathematical scope / roadmap:** [`docs/milestone.md`](docs/milestone.md),
  [`docs/leray_hopf_lean_mvp_plan.md`](docs/leray_hopf_lean_mvp_plan.md),
  [`docs/ROADMAP.md`](docs/ROADMAP.md).
- **Current axiom ledger / integrity backstop:** [`docs/STATUS.md`](docs/STATUS.md).
- **References (SSoT):** [`docs/references/`](docs/references/).
- **Agent rules:** [`AGENTS.md`](AGENTS.md); roles + Codex review protocol:
  [`docs/agent-roles.md`](docs/agent-roles.md); build/checks:
  [`docs/build-and-checks.md`](docs/build-and-checks.md).

## Build and CI

```bash
lake build
bash scripts/agent-preflight.sh    # build + guardrail checks
```

CI (`.github/workflows/lean.yml`) builds the project and runs guardrail checks that
block overclaiming theorem names, unmarked `sorry`, and undeclared axioms, plus the
live axiom pin described above.

## License and citation

This repository is licensed under the Apache License 2.0; see [`LICENSE`](LICENSE).
The license covers the Lean formalization code and repository materials. It does not
purport to license mathematical facts or theorems themselves.

Citation metadata is provided in [`CITATION.cff`](CITATION.cff). If you use this
formalization, cite the repository using GitHub's "Cite this repository" metadata or
the `CITATION.cff` file.
