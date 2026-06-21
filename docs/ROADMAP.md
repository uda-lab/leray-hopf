# ROADMAP — toward axiom-free Leray–Hopf (re-cut 2026-06-18)

Measured by the discipline that matters (lean-formalization-discipline): **progress = project
axioms actually removed from the capstone `exists_lerayHopf_r3` + shrinking isolated-hypothesis
debt**, never merged sibling files.

## Current capstone footprint

`#print axioms exists_lerayHopf_r3_axiomatic` = 5 project axioms + 3 kernel.
**Removed so far: 1** — `spatial_compactness_R3` (6→5, PR #35 / issue #2), wired in via the
sorry-free Fréchet–Kolmogorov chain. The remaining milestones to date (R3-d, P5, P3, P2, ODE,
D, E, FourierL2, forward-time fix, track 3) are proved *content* sitting beside the closure,
conditional on isolated hypotheses — none yet wired in.

## Endpoint

`exists_lerayHopf_r3` (and ideally `exists_lerayHopf_torus3`) with **0 project axioms**. That
requires discharging every pillar below — the full missing PDE sub-chapter of mathlib.

## Axiom → pillar dependency map (ℝ³)

| Axiom | Remaining pillar(s) to discharge | Proved-but-unwired chain |
|---|---|---|
| `r3GalerkinScheme_exists` | **P-α** `CurlSchwartzDense` (Helmholtz/curl density) | P5 `…_of_basis` + D `…_of_curlDense` |
| ~~`spatial_compactness_R3`~~ **REMOVED (PR #35)** | **P-β** Fréchet–Kolmogorov criterion + H¹⇒wtd-integrability — DONE, now a theorem | P3 reduction + B (T0b proved), wired in |
| `galerkin_ode_solution_R3` | concrete scheme (P-α) + concrete `F` (P-γ); ODE existence **DONE** (track 3) | ODE energy algebra + E Riesz + track 3 |
| `r3_NSForms_exist` | **P-γ** `(u·∇)v` weak-derivative convection operator on Lp | R3-d Schwartz-level estimates |
| `aubin_lions_R3` | **P-δ** Bochner–Sobolev-in-time / Aubin–Lions–Simon | P2 partial (spatial reuse + b-passage) |
| `galerkin_limit_passage_R3` | **P-δ** (+ weak-time-deriv good representative; b-passage DONE) | P2 partial |

## The genuine missing-mathlib pillars (the real work units)

- **P-α Helmholtz/curl density** → `CurlSchwartzDense`. Harmonic analysis. *Medium–large.*
- **P-β Fréchet–Kolmogorov** (mollification + Arzelà–Ascoli in L²) + the H¹⇒`‖ξ‖²`-integrability
  distribution-faithfulness lemma. *Large (FK is library-grade) + medium.*
- **P-γ `(u·∇)v` operator on Lp** (weak derivatives + divergence + IBP + 3D trilinear estimate,
  lifting R3-d to the operator level). *Large — deepest "new calculus." Not yet scoped.*
- **P-δ Bochner–Sobolev-in-time** (`W^{1,p}(0,T;X)`, weak vector-valued time derivative,
  Aubin–Lions/Simon, measurable representatives), best built at the **abstract Gelfand-triple
  level** so it serves ℝ³ **and** T³ at once. *Largest — a sub-library (~6–10 person-months).*
- ~~P-ε finite-dim ODE global existence~~ — **DONE** (track 3, `finDimGlobalODE_exists`).

## Maximal parallel decomposition (independent development streams)

Each pillar is a NEW standalone file in a distinct math domain → developable in parallel.
Shared-foundation caveats noted; the existing `FourierL2.lean` already absorbs the common
L²-Fourier base for A/B/γ.

- **Stream A — Helmholtz/curl density (P-α).** Prove `CurlSchwartzDense` via Fourier:
  `𝓕(curl ψ)=iξ×ψ̂` spans `ξ^⊥`; div-free ⟺ `ξ·û=0`; reduce to fiberwise transverse-spanning +
  density transfer. Reuses FourierL2 (read-only). **Unblocks capstone #1.**
- **Stream B — FK + integrability (P-β).** (b1) FK precompactness criterion (convolution
  approximate identity + Arzelà–Ascoli) → discharges `FrechetKolmogorovInput`; (b2) close
  `integrable_viscous_integrand_of_memH1` (B's lone sorry). **Unblocks capstone #2.**
- **Stream C — `(u·∇)v` on Lp (P-γ).** Build the genuine convection operator/form on all
  `L²_σ`, lifting R3-d's Schwartz estimates; construct a concrete `R3NSForms`. Mild shared
  weak-derivative base with A. **Unblocks capstone #4 (+ feeds `galerkin_ode_solution`'s F).**
  *Needs a fresh feasibility planner — never scoped.*
- **Stream D — Bochner–Sobolev-in-time (P-δ), abstract.** The Gelfand-triple time-Sobolev +
  Aubin–Lions library. Orthogonal (time direction). **Unblocks `aubin_lions`/`limit_passage`
  on BOTH ℝ³ and T³.** Highest leverage, largest.
- **(Stream T — T³ substantiation, optional/lower priority.** T³ has 4 axioms; spatial
  compactness already proved (Fourier tails); shares the abstract layer + Stream D.)

Parallel-safety: A/B/C/D are separate files, separate domains, no cross-stream data-flow; the
only shared read-only base is `FourierL2`. **All four can run concurrently.** The capstones
(below) are the sequential part.

## Capstone (wiring) stream — sequential, edits `AxiomaticClosure.lean`, gated

- **C0 (now): wire + merge track 3** — discharge `FinDimGlobalODE` (already proved); root-import
  `GalerkinODESolve`, final gate, merge. (Removes no axiom yet, but pays the parked-kernel debt
  and makes the ODE solution unconditional over `schemeOfBasis B`.)
- **C1: remove `r3GalerkinScheme_exists`** once Stream A lands → 6→5. (First real removal.)
- **C2: remove `spatial_compactness_R3`** — **DONE (PR #35 / issue #2)** → 6→5, via the
  sorry-free Fréchet–Kolmogorov chain
  (`localCompactness_R3_of_ballCompact ∘ localRellichInput_of_frechetKolmogorov ∘
  frechetKolmogorov_holds`).
- **C3: remove `r3_NSForms_exist`** once Stream C lands → 4→3; then, with C1+C3+track3 (concrete
  scheme + concrete F + ODE existence), **remove `galerkin_ode_solution_R3`** → 3→2.
- **C4: remove `aubin_lions_R3` + `galerkin_limit_passage_R3`** once Stream D lands → 2→0.
Each Ci edits the core and re-pins `#print axioms`; strictly sequential among themselves, but
interleavable with ongoing streams.

## Honest horizon (no over-promising)

- **Near-term reachable (real but bounded work):** Streams A and B → **first two axiom removals
  (6→4)**, plus C0. These are genuine harmonic analysis / standard-criterion builds.
- **Months-class sub-projects:** Stream C (`(u·∇)v`) and Stream D (Bochner-time). They gate the
  remaining four axioms. Full axiom-free completion ⟺ C **and** D done = the multi-person-year
  mathlib PDE sub-chapter.
- Realistic dent of a sustained push: **6 → ~3 or ~2 axioms** (A, B, then the ODE coupling once
  C lands), with C/D the deep walls documented as precise frontiers, not faked.
