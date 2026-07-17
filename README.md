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
`LerayHopfSolutionFull_R3` structures and the capstones above — **not** a paraphrase that
claims more than the fields below.

### Modeling scope

- **No external force.** The weak identity carried by `weak_eq` has no forcing term; this is
  the homogeneous Navier–Stokes equation only.
- **Finite time horizon, not global-in-time.** `T : ℝ` with `hT : 0 < T` is an input to the
  capstones: for each such `T` there is a solution on `[0, T]`. This is not a claim of a single
  solution simultaneously valid on `[0, ∞)`.
- **𝕋³ is the unit torus.** `Torus3 = (AddCircle 1)³` — period **1** in each coordinate (not
  `2π`), with the Fourier basis convention `e^{2πi k·x}`; see `LerayHopf/Torus/Domain.lean`.
  ℝ³ is whole space with no periodicity.
- **Separated-variable weak formulation.** `WeakFormNS` tests against `ψ(t) · w(x)` (a scalar
  temporal factor times a fixed spatial test vector `w` from the domain's Galerkin/Schwartz
  div-free test class), not a general space-time test function `φ(t, x)`. The relation to the
  standard space-time test formulation is **out of scope** — this repository neither proves
  nor assumes it; see `WeakFormNS`'s docstring in `LerayHopf/EvolutionTriple.lean`.

### Claims table (issue #146)

Every mathematical claim below is matched to the exact field/theorem that carries it, so that
no natural-language paraphrase can silently claim more than the type. `D` ranges over the
generic `Galerkin.Domain` (`torusDomain` or `r3Domain 𝔊`); `LerayHopfSolutionFull(_R3)` are
abbreviations for `Galerkin.LerayHopfSolution`.

| Natural-language claim | Field / theorem | What is actually guaranteed |
|---|---|---|
| The solution curve stays divergence-free | `LerayHopfSolution.u : Time → ↥D.σ` | Type-level: `u t` is valued in the closed divergence-free subspace `σ` for every `t`, by construction. |
| `u` solves the weak Navier–Stokes equation | `weak_eq : WeakFormNS ν T (D.evolution C) u` | Holds against separated-variable tests `ψ(t)·w(x)` (see "Modeling scope" above); no forcing term. |
| Energy inequality | `energy_ineq` | `½‖u(t)‖² + ∫₀ᵗ dissip(ν, u(s)) ds ≤ ½‖u₀‖²` for `t ∈ [0, T]` (not for all `t ≥ 0`). |
| Initial condition is attained | `initial_trace` | `u(t) → u₀` in the ambient-L² norm as `t → 0⁺` — a **one-sided trace at `t = 0` only**. This is *not* a claim of weak continuity on all of `[0, T]`. |
| a.e.-in-time H¹ regularity | `energy_class.1` | `∀ᵐ t ∈ [0, T], regMem (u t)` (a.e. H¹ membership). |
| Viscous dissipation is integrable | `energy_class.2` | `IntervalIntegrable (fun s => dissip ν (u s)) volume 0 T`. |
| `u ∈ L²(0,T;H¹_σ)` (literal Bochner space membership) | — **not a field** | **Not claimed.** `energy_class` gives a.e. pointwise H¹ membership plus integrable dissipation — not Bochner `MemLp` valued in `H¹` as a Banach space. The measurability field below is into the *ambient* L² space, not into H¹, so it does not upgrade the a.e. statement to a literal Bochner-space membership. |
| `u` is measurable as a function of time | `u_aestronglyMeasurable` | `AEStronglyMeasurable (fun t => (u t : D.X)) …` on `[0, T]`, valued in the **ambient L² Hilbert space** `D.X` (not H¹). |
| `u ∈ C_w([0,T]; L²_σ)` (weak continuity in time) | — **not a field** | **Not claimed as a public guarantee.** Only the one-sided trace at `t = 0` (`initial_trace`) is exposed as a field; general-`t` weak continuity is a deliberate non-inclusion — a definitional choice of this repository's public structure, not a proof gap (see `docs/formalization-review-ja.md` §4.2 for the internal-construction note). |
| Existence on 𝕋³ | `exists_lerayHopf_torus3` | For every `u₀ ∈ L²_σ`, `ν > 0`, `T > 0`: `∃ F, Nonempty (LerayHopfSolutionFull F ν T u₀)`. |
| Existence on ℝ³ | `exists_lerayHopf_r3` | For every `u₀ ∈ L²_σ(ℝ³)`, `ν > 0`, `T > 0`: `∃ 𝔊 F, Nonempty (LerayHopfSolutionFull_R3 𝔊 F ν T u₀)`. |
| Galerkin-level approximate solutions exist | `Galerkin.SolutionData` (per `n`) | An **intermediate** structure (per-`n` finite-dimensional Galerkin ODE data with uniform bounds) — not itself the final solution; consumed by `Galerkin.CompactnessPackage` / `exists_lerayHopf_from_package` on the way to `LerayHopfSolution`. |

Nothing above is a smoothness, uniqueness, or non-uniqueness claim.

## Import guide (issue #147)

`import LerayHopf` is the **complete release surface**: both capstones plus every
supporting layer, and it is **sorry-free** — statically enforced in CI by
`scripts/check-release-cone.sh`, which walks the transitive import closure of
`LerayHopf.lean` and fails if any file it reaches contains a `sorry`, marked or unmarked.
Narrower imports are also available for consumers who only need one piece:

| Import | Brings in | Status |
|---|---|---|
| `import LerayHopf.Core` | Axiom-free, `sorryAx`-free spatial/regularity layer shared by both domains (L²_σ spaces, Leray/Galerkin projections, Fourier machinery). | Sorry-free, axiom-free. |
| `import LerayHopf.Torus.Capstone` | The full 𝕋³ capstone chain, `exists_lerayHopf_torus3`. | Kernel-only (no project axioms, no `sorryAx`). |
| `import LerayHopf.R3Capstone` | The full ℝ³ capstone chain, `exists_lerayHopf_r3`. | Kernel-only (no project axioms, no `sorryAx`). |
| `import LerayHopf` | Everything above, plus the remaining supporting files needed to assemble both capstones (Bochner Gelfand-triple time theory used by the R3 limit-passage chain, Galerkin ODE solvers, etc.). | **Sorry-free** (issue #147). |
| `import LerayHopf.Experimental` | Explicit **opt-in** for incomplete Bochner time-layer work not needed by either capstone: `Bochner.TimeSobolevAC`, `Bochner.TimeMollification`, `Bochner.TimeMollifierInterval`, `Bochner.TimeSobolevExperimental`. | Contains all 6 remaining `sorry`s; see that file's docstring for the per-module inventory. |

Nothing reachable from `import LerayHopf` imports `LerayHopf.Experimental`, and nothing in
`LerayHopf.Experimental` is needed by either capstone — the split is enforced, not just
documented.

## Layout

- **Lean sources:** `LerayHopf/` — `R3/` (ℝ³), `Torus/` (𝕋³), `Bochner/` (Gelfand-triple
  time theory), and the top-level shared/abstract `*.lean` files. See
  [`docs/architecture.md`](docs/architecture.md) for a module map by layer, and
  [`docs/pdelib-staging.md`](docs/pdelib-staging.md) for the inventory of which
  generic-layer content is ready to lift into the external `pdelib` project.
- **Current axiom ledger / integrity backstop:** [`docs/STATUS.md`](docs/STATUS.md).
- **Historical design/roadmap docs** (both capstones are long past these; kept for
  provenance): [`docs/archive/milestone.md`](docs/archive/milestone.md),
  [`docs/archive/leray_hopf_lean_mvp_plan.md`](docs/archive/leray_hopf_lean_mvp_plan.md),
  [`docs/archive/ROADMAP.md`](docs/archive/ROADMAP.md),
  [`docs/archive/REPORT.md`](docs/archive/REPORT.md).
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
- Exactly **6** remaining `sorry`s, every one same-line `-- ALLOW_SORRY:`-marked, none
  reachable from either capstone, and — since issue #147 — none reachable from
  `import LerayHopf` at all (see "Import guide" above; enforced by
  `scripts/check-release-cone.sh`). All six are Lions–Magenes-class Bochner-time walls,
  gathered behind the explicit opt-in `LerayHopf.Experimental`:
  `Bochner/TimeSobolevExperimental.lean:57`, `Bochner/TimeSobolevAC.lean:322`,
  `Bochner/TimeMollification.lean:196`,
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
