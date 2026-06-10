# lean-pde

Scaffold for a future Lean 4 + mathlib formalization of **Leray–Hopf weak existence**
for the incompressible Navier–Stokes equations.

The current focus is **repository discipline and agent safety**, not mathematical
results. This repo sets up the build, CI, guardrails, and the agent role definitions
that later mathematical work will run under.

- Mathematical scope and roadmap live in [`docs/`](docs/) — `milestone.md` (roadmap)
  and `leray_hopf_lean_mvp_plan.md` (MVP design). Those plan files are the source of
  truth for what gets formalized.
- Agent rules: [`AGENTS.md`](AGENTS.md). Team roles and the Codex review protocol:
  [`docs/agent-roles.md`](docs/agent-roles.md).
- Build and checks: [`docs/build-and-checks.md`](docs/build-and-checks.md).

CI (`.github/workflows/lean.yml`) builds the project and runs guardrail checks that
block accidental overclaiming, unmarked `sorry`, and undeclared axioms.

> **No mathematical claim is made.** This repository does **not** establish existence,
> regularity, uniqueness, or nonuniqueness of Navier–Stokes solutions. It currently
> declares no theorems; the Lean library is an empty scaffold.
