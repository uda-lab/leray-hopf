# ROADMAP — toward axiom-free Leray–Hopf (re-cut 2026-06-18)

> **Archived (2026-07-17, issue #148).** This document is a completed campaign log: its stated
> endpoint — both capstones at 0 project axioms — was reached on 2026-07-05 (see the "Honest
> horizon" section below), and everything else here is PR/stream/task-codename archaeology from
> the removal campaign. For the current axiom status see `HANDOFF.md` / `README.md` / the live
> pin `scripts/check-axioms-live.sh`; for future-work direction see `HANDOFF.md` §6.

Measured by the discipline that matters (lean-formalization-discipline): **progress = project
axioms actually removed from the capstone `exists_lerayHopf_r3` + shrinking isolated-hypothesis
debt**, never merged sibling files.

## Current capstone footprint

`#print axioms exists_lerayHopf_r3` = **3 kernel axioms only** (no project axioms, no sorryAx) — **R³ UNCONDITIONAL**.
`#print axioms exists_lerayHopf_torus3` = **3 kernel axioms only** (no project axioms, no sorryAx) — **T³ UNCONDITIONAL**.
Live R3 axiom: none — `galerkin_limit_passage_R3` PROVED (issue #4, PR-6, 2026-07-05).
Live T³ axiom: none — `aubin_lions` REMOVED (issue #23, PR #89; now the proved def `torusAubinLionsPackage_of_galSeq`).

**Removed so far (R3: original 6 → current 0; T³: original 4 → current 0):**
- `spatial_compactness_R3` (#2) — Fréchet–Kolmogorov chain
- `galerkin_ode_solution_R3` (#10) — finite-dim ODE solver
- `aubin_lions_R3` → split → time content became `galerkinSpaceTimeExtraction_R3` → PROVED (#15/#44)
- `galerkin_weakLimit_R3` (#47) — strong ball-exhaustion + Mazur
- `r3GalerkinScheme_exists` (#21) — curl-density + Schwartz Galerkin basis
- `curlSchwartzDense_holds` (#3) — Fourier route
- `r3ConvectionGapOp_exists` (#56/PR #60) — determined-form BLT construction (`r3ConvectionGapOp_holds`)
- `torusConvectionGap_exists` (#53/PR #62) — determined-form torus construction (`torusConvectionGap_holds`)
- T³ `galerkin_limit_passage` (#25/PR #75) — proved via `torus_galerkin_limit_passage_of_energyClass`
  + `torus_energyClass_of_aubinLions`; T³ frontier 2 → 1
- T³ `aubin_lions` (#23/PR #89, 2026-07-04) — proved as `torusAubinLionsPackage_of_galSeq`
  (`LerayHopf/TorusAubinLionsAssembly.lean`) via mode-wise spectral route; T³ frontier 1 → 0
  (T³ now **unconditional**)
- `galerkin_spacetime_precompact_R3` (#46 PR-4, 2026-07-04) — axiom → theorem via the step-curve
  Aubin–Lions–Simon assembly (File E `LerayHopf/R3/SpacetimePrecompact.lean`,
  `galerkin_spacetime_precompact_of_goodSampling`); R3 frontier 2 → 1
- `galerkin_limit_passage_R3` (#4 PR-6, 2026-07-05) — PROVED as theorem in
  `LerayHopf/R3/LimitPassage.lean` (Fatou+liminf → ∀t energy ineq; `weakFormNS_limit_passage`
  → weak NS eq; `strong_trace_of_props_R3` → initial trace); R3 frontier 1 → **0**
  (R3 now **unconditional**)

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
| ~~`galerkin_spacetime_precompact_R3`~~ **REMOVED (#46 PR-4, 2026-07-04)** | **P-δ** LOCAL Aubin–Lions–Simon spacetime precompactness — DONE (step-curve route, File E `SpacetimePrecompact.lean`) | issue #46 PRs #74/#81/#86/PR-4, wired in |
| ~~`galerkin_limit_passage_R3`~~ **PROVED (#4 PR-6, 2026-07-05)** | **P-δ** complete — `LimitPassage.lean`; Option-A H¹-curl-approx route (`R3TestApproxH1`); R3 **1 → 0** | — |

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
- ~~**Stream C — `(u·∇)v` convection form (P-γ).**~~ **DONE (issue #56/PR #60)** —
  `r3ConvectionGapOp_exists` is removed by the determined-form BLT construction. The result is a
  proof-carrying total trilinear extension pinned to the Schwartz test-class form and continuous
  in the two solution slots at fixed Schwartz tests, not a canonical continuous pure-`L²³`
  operator.
- **Stream D — Bochner–Sobolev-in-time (P-δ), abstract.** The Gelfand-triple time-Sobolev +
  Aubin–Lions library. Orthogonal (time direction). **Unblocks the remaining ℝ³ axiom
  (`galerkin_limit_passage_R3`) via the Bochner/Simon route.** (The other half of the former
  ℝ³ pair, `galerkin_spacetime_precompact_R3`, was DISCHARGED by the issue #46 step-curve
  route on 2026-07-04 — not via Stream D.) Highest leverage, largest.
- ~~**Stream T — T³ `aubin_lions` removal (issue #23).**~~ **DONE (2026-07-04).** T³ is now
  **unconditional** (0 project axioms). The mode-wise spectral campaign (PR #76 replan)
  landed in 6 PRs: #77 (Phase-0 statement gate), #78 (T-AL-1 torus test family + Stokes
  pairing bound), #79 (T-AL-2 domain-neutral scalar equicontinuity engine), #80 (T-AL-3
  mode-wise Galerkin extraction), #85 (T-AL-4/5 Riesz limit curve + tail), #88 (T-AL-5
  tail assembly), #89 (T-AL-6 assembly + rewiring + axiom deletion). `aubin_lions` is now
  the proved `noncomputable def torusAubinLionsPackage_of_galSeq`
  (`LerayHopf/TorusAubinLionsAssembly.lean`); issue #23 closed.

Parallel-safety: the completed A/B/C files remain separate from the live D work; the only shared
read-only base is `FourierL2`. The remaining capstone work is sequential.

## Capstone (wiring) stream — sequential, edits `SolutionInterfaces.lean`, gated

- **C0 (now): wire + merge track 3** — discharge `FinDimGlobalODE` (already proved); root-import
  `GalerkinODESolve`, final gate, merge. (Removes no axiom yet, but pays the parked-kernel debt
  and makes the ODE solution unconditional over `schemeOfBasis B`.)
- **C1: remove `r3GalerkinScheme_exists`** — **DONE (#21)** → curl-density + Schwartz Galerkin basis.
- **C2: remove `spatial_compactness_R3`** — **DONE (PR #35 / #2)** → Fréchet–Kolmogorov chain.
- **C0/track3: remove `galerkin_ode_solution_R3`** — **DONE (#10)** → finite-dim ODE solver; torus
  analogue also **DONE (#24)**.
- **aubin_lions_R3 → split → galerkinSpaceTimeExtraction_R3 → PROVED** — **DONE (#15/#44)** → isolates
  `galerkin_spacetime_precompact_R3` as the remaining time-compactness axiom (since
  discharged — see C4a below).
- **`galerkin_weakLimit_R3` PROVED** — **DONE (#47)** → strong ball-exhaustion + Mazur.
- **C3: remove `r3ConvectionGapOp_exists`** — **DONE (#56/PR #60)** → determined-form BLT
  construction (`r3ConvectionGapOp_holds`); `ConvectionExtension.lean`; R3 3→2.
- **C4a: remove `galerkin_spacetime_precompact_R3`** — **DONE (#46 PR-4, 2026-07-04)** →
  step-curve LOCAL Aubin–Lions–Simon assembly (File E `SpacetimePrecompact.lean`); R3 2→1.
- **C4b: remove `galerkin_limit_passage_R3`** — **DONE (issue #4 PR-6, 2026-07-05)** →
  Option-A H¹-curl-approx route (`R3TestApproxH1`, `LimitPassage.lean`); R3 **1 → 0**;
  ℝ³ now **unconditional** (kernel-only).  Stream D was not required — the limit passage
  was closed via the H¹-curl approximation route independently of Bochner/Simon.
Each Ci edits the core and re-pins `#print axioms`; strictly sequential among themselves, but
interleavable with ongoing streams.

## Honest horizon (achieved — both capstones kernel-only)

- **Achieved:** Streams A + B + C0/track3 + #47 + C3 + #46 spacetime-precompactness + C4b →
  **6 → 0 axioms** (ℝ³ **unconditional**, 2026-07-05); on T³, #24 + #53 + #25 + #23 →
  **4 → 0 axioms** (T³ **unconditional**, 2026-07-04).
- **ℝ³ (0 axioms): DONE.** `galerkin_limit_passage_R3` proved (issue #4 PR-6, 2026-07-05)
  via the Option-A H¹-curl-approx route (`R3TestApproxH1`), NOT via Stream D / Bochner/Simon.
  `exists_lerayHopf_r3` is unconditional (kernel-only).
- **T³ (0 axioms): DONE.** `aubin_lions` removed (issue #23, PR #89, 2026-07-04) via
  the mode-wise spectral route; `exists_lerayHopf_torus3` is unconditional.
- **Full kernel-only completion: DONE** (both capstones, 2026-07-05).  `bash scripts/check-axioms-live.sh`
  is the canonical live pin.
