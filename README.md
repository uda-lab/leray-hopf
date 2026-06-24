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

Each capstone currently rests on **3 project axioms**, pinned exactly by
`scripts/check-axioms-live.sh` (a CI gate that runs `#print axioms` and fails on any
unexpected or missing axiom, or any `sorryAx`):

- **𝕋³:** `aubin_lions`, `galerkin_limit_passage`, `torusConvectionGap_exists`
- **ℝ³:** `galerkin_spacetime_precompact_R3`, `galerkin_limit_passage_R3`, `r3_NSForms_exist`

Everything else in the Galerkin construction — the functional-analytic backbone, the
finite-dimensional ODE solver, spatial Rellich–Kondrachov compactness, the
Aubin–Lions-in-time diagonalization, Helmholtz/curl density (Fourier route), and the
Mazur weak-limit closure — is **proved sorry-free**, not assumed.

> **Honest scope.** This repository does **not** establish *unconditional* existence.
> The remaining axioms are genuine analytic facts that Mathlib currently lacks
> (Bochner Aubin–Lions–Simon compactness; the 3D trilinear/convection Sobolev estimate;
> Lions–Magenes good-representative limit passage). No regularity, uniqueness, or
> non-uniqueness claim is made. The project's goal is to drive the axiom count to zero;
> the current frontier and remaining work are tracked in the open GitHub issues and
> [`docs/STATUS.md`](docs/STATUS.md).

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
