# lean-pde

A Lean 4 + mathlib formalization of **Leray–Hopf weak existence** for the
incompressible Navier–Stokes equations, on the periodic 3-torus 𝕋³ and on whole
space ℝ³.

## What is actually proved

Two capstone existence theorems are proved and machine-checked. Both are now
**kernel-only**: `#print axioms` returns only the standard kernel axioms
`propext` / `Classical.choice` / `Quot.sound`, with **zero project axioms** and
**no `sorryAx`**:

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

The current project-axiom frontier is **𝕋³ = 0 project axioms, ℝ³ = 0 project axioms**,
pinned exactly by `scripts/check-axioms-live.sh` (a CI gate that runs `#print axioms` and
fails on any unexpected or missing axiom, or any `sorryAx`):

- **𝕋³:** no project axioms — `#print axioms` returns kernel axioms only (`propext`,
  `Classical.choice`, `Quot.sound`).
- **ℝ³:** no project axioms — `#print axioms` returns kernel axioms only (`propext`,
  `Classical.choice`, `Quot.sound`).

Everything else in the Galerkin construction — the functional-analytic backbone, the
finite-dimensional ODE solver, spatial Rellich–Kondrachov compactness, the
Aubin–Lions-in-time diagonalization, Helmholtz/curl density (Fourier route), the
Mazur weak-limit closure, and the determined-form convection extensions — is
**proved sorry-free**, not assumed.

> **Honest scope.** The 𝕋³ and ℝ³ capstones are both **unconditional / kernel-only**
> (`#print axioms` returns only `propext`, `Classical.choice`, and `Quot.sound`).
> The limit-passage and compactness layers used by the capstones are proved theorems, not
> project axioms. The convection forms are proof-carrying total trilinear extensions pinned
> to the genuine
> Schwartz/Galerkin test-class forms, with fixed-test continuity; they are not claims of
> a canonical continuous convection operator on all pure `L² × L² × L²` triples.
> No regularity, uniqueness, or non-uniqueness claim is made. Residual marked `sorry`
> declarations outside the two capstone cones are tracked in [`docs/STATUS.md`](docs/STATUS.md).

Public summaries should cite the proof-carrying `LerayHopfSolutionFull` /
`LerayHopfSolutionFull_R3` structures and the capstones above. The older
generic `ExistsLerayHopf` / `LerayHopfSolution` layer is scaffold-only and should not
be described as a PDE existence theorem.

## Layout

- **Lean sources:** `LerayHopf/` — `R3/` (ℝ³), `Torus/` (𝕋³), `Bochner/` (Gelfand-triple
  time theory), and the top-level shared/abstract `*.lean` files. See
  [`docs/architecture.md`](docs/architecture.md) for a module map by layer, and
  [`docs/pdelib-staging.md`](docs/pdelib-staging.md) for the inventory of which
  generic-layer content is ready to lift into the external `pdelib` project.
- **Mathematical scope / roadmap:** [`docs/milestone.md`](docs/milestone.md),
  [`docs/leray_hopf_lean_mvp_plan.md`](docs/leray_hopf_lean_mvp_plan.md),
  [`docs/ROADMAP.md`](docs/ROADMAP.md).
- **Current axiom ledger / integrity backstop:** [`docs/STATUS.md`](docs/STATUS.md).
- **References (SSoT):** [`docs/references/`](docs/references/).
- **Agent rules:** [`AGENTS.md`](AGENTS.md); roles + Codex review protocol:
  [`docs/agent-roles.md`](docs/agent-roles.md); build/checks:
  [`docs/build-and-checks.md`](docs/build-and-checks.md).
- `docs/scratch/` holds internal agent working notes (route plans, per-round audit
  verdicts, design contracts) — not part of the curated documentation set above.

## Repository hygiene

- The `LerayHopf/` import DAG has **zero dead files**: every `.lean` file under
  `LerayHopf/` is reachable via at least one `import` statement.
- Doc-string coverage on public declarations is high throughout the tree.
- Exactly **7** remaining `sorry`s, every one same-line `-- ALLOW_SORRY:`-marked and
  none reachable from either capstone: `LerayHopf/Statement.lean:39` (an intentional
  scaffold placeholder, kept distinct from the real capstones by design) and six
  Lions–Magenes-class Bochner-time walls — `Bochner/TimeSobolev.lean:545`,
  `Bochner/TimeSobolevAC.lean:350`, `Bochner/TimeMollification.lean:196`,
  `Bochner/TimeMollifierInterval.lean:297,466,601`. Verify with
  `grep -rn 'sorry -- ALLOW_SORRY' LerayHopf/`.

## Build and CI

```bash
lake build
bash scripts/agent-preflight.sh    # build + guardrail checks
```

CI (`.github/workflows/lean.yml`) builds the project and runs guardrail checks that
block overclaiming theorem names, unmarked `sorry`, and undeclared axioms, plus the
live axiom pin described above.

## License and citation

Copyright 2026 Tomoki Uda.

This repository is licensed under the Apache License 2.0; see [`LICENSE`](LICENSE).
The license covers the Lean formalization code and repository materials. It does not
purport to license mathematical facts or theorems themselves.

Citation metadata is provided in [`CITATION.cff`](CITATION.cff). If you use this
formalization, cite the repository using GitHub's "Cite this repository" metadata or
the `CITATION.cff` file.
