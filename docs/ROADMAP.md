# ROADMAP — toward axiom-free Leray–Hopf (re-cut 2026-06-18)

Measured by the discipline that matters (lean-formalization-discipline): **progress = project
axioms actually removed from the capstone `exists_lerayHopf_r3` + shrinking isolated-hypothesis
debt**, never merged sibling files.

## Current capstone footprint

`#print axioms exists_lerayHopf_r3_axiomatic` = **2 project axioms + 3 kernel** (no sorryAx).
Live R3 axioms: `galerkin_spacetime_precompact_R3`, `galerkin_limit_passage_R3`.
Live T³ axioms: `aubin_lions`, `galerkin_limit_passage`, `torusConvectionGap_exists`.

**Removed so far (original 6 → current 2):**
- `spatial_compactness_R3` (#2) — Fréchet–Kolmogorov chain
- `galerkin_ode_solution_R3` (#10) — finite-dim ODE solver
- `aubin_lions_R3` → split → time content became `galerkinSpaceTimeExtraction_R3` → PROVED (#15/#44)
- `galerkin_weakLimit_R3` (#47) — strong ball-exhaustion + Mazur
- `r3GalerkinScheme_exists` (#21) — curl-density + Schwartz Galerkin basis
- `curlSchwartzDense_holds` (#3) — Fourier route
- `r3ConvectionGapOp_exists` (#56/PR #60) — determined-form BLT construction (`r3ConvectionGapOp_holds`)

The `check-axioms-live.sh` script is the canonical live pin.

## Endpoint

`exists_lerayHopf_r3` (and ideally `exists_lerayHopf_torus3`) with **0 project axioms**. That
requires discharging every pillar below — the full missing PDE sub-chapter of mathlib.

## Axiom → pillar dependency map (ℝ³)

| Axiom | Remaining pillar(s) to discharge | Proved-but-unwired chain |
|---|---|---|
| ~~`r3GalerkinScheme_exists`~~ **REMOVED (#21)** | **P-α** `CurlSchwartzDense` — DONE (issue #3 Fourier route) | P5 `…_of_basis` + D `…_of_curlDense` + A CurlDensity |
| ~~`spatial_compactness_R3`~~ **REMOVED (#2/PR #35)** | **P-β** Fréchet–Kolmogorov criterion + H¹⇒wtd-integrability — DONE, now a theorem | P3 reduction + B (T0b proved), wired in |
| ~~`galerkin_ode_solution_R3`~~ **REMOVED (#10)** | concrete scheme + concrete `F` + ODE existence — DONE (track 3 / #10) | ODE energy algebra + E Riesz + track 3 |
| ~~`r3ConvectionGapOp_exists`~~ **REMOVED (#56/PR #60)** | **P-γ** `(u·∇)v` weak-derivative convection operator on Lp — DONE (determined-form BLT construction) | R3-d Schwartz-level estimates + ConvectionExtension.lean C11 |
| ~~`aubin_lions_R3`~~ **REMOVED (#15)** → split → `galerkinSpaceTimeExtraction_R3` → **PROVED (#44)** | **P-δ** isolates to `galerkin_spacetime_precompact_R3` | P2 partial (spatial reuse + b-passage) |
| ~~`galerkin_weakLimit_R3`~~ **REMOVED (#47)** | strong ball-exhaustion + Mazur weak-closedness — PROVED | — |
| `galerkin_spacetime_precompact_R3` (**live**) | **P-δ** Bochner–Sobolev-in-time / Aubin–Lions–Simon spacetime precompactness | P2 partial |
| `galerkin_limit_passage_R3` (**live**) | **P-δ** (+ weak-time-deriv good representative; b-passage DONE) | P2 partial |

## The genuine missing-mathlib pillars (the real work units)

- ~~**P-α Helmholtz/curl density**~~ — **DONE** (#3/#21, `CurlSchwartzDense` proved via Fourier route).
- ~~**P-β Fréchet–Kolmogorov**~~ — **DONE** (#2/PR #35, FK chain wired into capstone).
- ~~**P-γ `(u·∇)v` operator on Lp**~~ — **DONE** (#56/PR #60, `r3ConvectionGapOp_holds` proved via
  determined-form BLT construction in `ConvectionExtension.lean`; `r3ConvectionGapOp_exists` removed).
- **P-δ Bochner–Sobolev-in-time** (`W^{1,p}(0,T;X)`, weak vector-valued time derivative,
  Aubin–Lions/Simon, measurable representatives), best built at the **abstract Gelfand-triple
  level** so it serves ℝ³ **and** T³ at once. *Largest — a sub-library (~6–10 person-months).*
- ~~P-ε finite-dim ODE global existence~~ — **DONE** (track 3, `finDimGlobalODE_exists`).

## Maximal parallel decomposition (independent development streams)

Each pillar is a NEW standalone file in a distinct math domain → developable in parallel.
Shared-foundation caveats noted; the existing `FourierL2.lean` already absorbs the common
L²-Fourier base for A/B/γ.

- ~~**Stream A — Helmholtz/curl density (P-α).**~~ **DONE (issue #3/#21)** — `CurlSchwartzDense` proved
  via Fourier route; `r3GalerkinScheme_exists` removed from capstone.
- ~~**Stream B — FK + integrability (P-β).**~~ **DONE (issue #2/PR #35)** — `spatial_compactness_R3`
  proved via FK chain; capstone wired.
- **Stream C — `(u·∇)v` on Lp (P-γ).** Build the genuine convection operator/form on all
  `L²_σ`, lifting R3-d's Schwartz estimates; construct a concrete `R3NSForms`. Mild shared
  weak-derivative base with A. **Unblocks capstone #4 (+ feeds `galerkin_ode_solution`'s F).**
  *Needs a fresh feasibility planner — never scoped.*
- **Stream D — Bochner–Sobolev-in-time (P-δ), abstract.** The Gelfand-triple time-Sobolev +
  Aubin–Lions library. Orthogonal (time direction). **Unblocks `aubin_lions`/`limit_passage`
  on BOTH ℝ³ and T³.** Highest leverage, largest.
- **(Stream T — T³ substantiation, optional/lower priority.** T³ is now at **3 axioms** (same as ℝ³);
  shares the abstract layer + Stream D.)

Parallel-safety: A/B/C/D are separate files, separate domains, no cross-stream data-flow; the
only shared read-only base is `FourierL2`. **All four can run concurrently.** The capstones
(below) are the sequential part.

## Capstone (wiring) stream — sequential, edits `AxiomaticClosure.lean`, gated

- **C0 (now): wire + merge track 3** — discharge `FinDimGlobalODE` (already proved); root-import
  `GalerkinODESolve`, final gate, merge. (Removes no axiom yet, but pays the parked-kernel debt
  and makes the ODE solution unconditional over `schemeOfBasis B`.)
- **C1: remove `r3GalerkinScheme_exists`** — **DONE (#21)** → curl-density + Schwartz Galerkin basis.
- **C2: remove `spatial_compactness_R3`** — **DONE (PR #35 / #2)** → Fréchet–Kolmogorov chain.
- **C0/track3: remove `galerkin_ode_solution_R3`** — **DONE (#10)** → finite-dim ODE solver; torus
  analogue also **DONE (#24)**.
- **aubin_lions_R3 → split → galerkinSpaceTimeExtraction_R3 → PROVED** — **DONE (#15/#44)** → isolates
  `galerkin_spacetime_precompact_R3` as the remaining time-compactness axiom.
- **`galerkin_weakLimit_R3` PROVED** — **DONE (#47)** → strong ball-exhaustion + Mazur.
- **C3: remove `r3ConvectionGapOp_exists`** — **DONE (#56/PR #60)** → determined-form BLT
  construction (`r3ConvectionGapOp_holds`); `ConvectionExtension.lean`; R3 3→2.
- **C4 (remaining): remove `galerkin_spacetime_precompact_R3` + `galerkin_limit_passage_R3`** once
  Stream D (Bochner-time / Aubin–Lions) lands → 2→0 (ℝ³ unconditional).
Each Ci edits the core and re-pins `#print axioms`; strictly sequential among themselves, but
interleavable with ongoing streams.

## Honest horizon (no over-promising)

- **Already achieved:** Streams A and B + C0/track3 + #47 + C3 completed → **6 → 2 axioms** (ℝ³).
- **Months-class sub-projects (remaining):** Stream D (Bochner-time / Aubin–Lions–Simon). It gates
  the remaining 2 axioms. Full axiom-free completion ⟺ D done = the multi-person-year mathlib
  PDE sub-chapter.
- Realistic dent of a sustained push from the current frontier: **2 → 0 axioms** (Stream D removes
  the time-compactness + limit-passage pair).
