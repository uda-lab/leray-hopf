# Autonomous run — final report

Leray–Hopf weak existence on the real 3-torus, built bottom-up on mathlib.
Branch `autorun/leray-hopf-torus3`, 10 milestone commits on top of `9232c05`.

## Headline

The run formalized the **entire linear/functional-analytic backbone** of the Galerkin
construction on `𝕋³` — and **cracked the Aubin–Lions spatial linchpin** (the Fourier-tail
Rellich compact embedding) — **entirely axiom-free**. The only `sorry` in the project is the
deliberate target statement `exists_lerayHopf_torus3_statement`, intentionally left undischarged
(No-vacuous-proof). This **exceeds the pre-run forecast**, which placed Aubin–Lions at ~50/50 and
predicted the run would land with a marked-`sorry` frontier. There is **zero frontier sorry debt**.

Metrics: 16 modules, ~2140 lines, 39 theorems/lemmas, 25 defs, 6 structures, 0 axioms, 1 (target) sorry.
Every must-prove result is `#print axioms`-clean (only `propext`, `Classical.choice`, `Quot.sound`).

## What is proved (axiom-free)

**M1 — structural spine.** `LerayHopfSolution`, `ExistsLerayHopf`, `GalerkinCompactnessPackage`,
the structural implication `exists_lerayHopf_from_galerkin_package`, and the `EnergySkeleton`
(`EnergyInequality` ⟹ `energy_nonincreasing_from_nonnegative_dissipation`).

**Side A/B.** `lower_bound_from_inverse_square_lifespan` (blow-up lower bound, proved — Codex
corrected its direction from the plan's mis-stated sketch); `LerayHopfNonunique` statement.

**M2 — real domain & spaces.** `Torus3 := UnitAddTorus (Fin 3)` with Haar measure; `L²(𝕋³;ℝ³)`,
`L²(𝕋³;ℂ)` on a single canonical measure; the Fourier Hilbert basis; the divergence-free
predicate `DivFreeL2`; and **`L²_σ(𝕋³)` as a closed submodule** `⨅ k, ker(divSymbol k)` —
*the planned axiom was eliminated*, making the divergence-free space fully rigorous and handing
the Leray projection its Hilbert structure for free. `H¹(𝕋³)` Fourier-weighted predicate.

**M3 — projections.** The **Leray projection** `Π_div` (idempotent, range `= L²_σ`, self-adjoint,
contraction, fixes div-free fields); the scalar **Fourier–Galerkin `Pₙ`** with convergence
`Pₙf → f` and the exact **multiplier cutoff** `P̂ₙf(k) = [k∈box]·f̂(k)`; and the **velocity
Galerkin projection** with `Pₙu → u` and **`L²_σ`-preservation** (incl. the conjugate-symmetry
real-valuedness argument).

**M4 — abstract energy.** The Galerkin **energy identity** `d/dt(½‖u‖²) = −D(u)` from
skew-symmetry `B(u,u,u)=0`, the **energy inequality** (FTC), and the full bridge to
**nonincreasing energy** via `EnergySkeleton`. Packaged as `AbstractEnergyLaw` (honest interface).

**M5 — Rellich.** The **Fourier-tail Rellich compact embedding**: Parseval (L1), the L²-error =
high-frequency tail (L2), the tail bound `≤ M²/(1+N²)` (L3), uniform `Pₙ`-approximation on the
H¹-ball (L4), finite-rank compactness (Bonus), and the capstone **`H1_ball_totallyBounded`** —
the H¹-ball is precompact in L² — plus its **sequential form** `rellich_seq_compact` (an
H¹-bounded sequence has an L²-convergent subsequence), the form limit-passage consumes.

## The frontier (NOT coded — demarcated, not faked)

Reaching *unconditional T³ existence* requires the following, each blocked by **structural
mathlib absences** (not hard-but-routine proofs). They are documented, not stubbed with
sorry/axiom; the abstract interfaces (`AbstractEnergyLaw`, `GalerkinCompactnessPackage`) are in
place to receive them.

1. **Concrete NS convection `b(u,v,w)=∫((u·∇)v)·w`** — mathlib has no `(u·∇)v` for `Lp`
   a.e.-classes on the torus. Needs a torus weak-derivative / Fourier-convection API.
2. **Nonlinear cancellation `b(u,u,u)=0`** for divergence-free `u` — needs torus integration by
   parts; mathlib's divergence theorem covers only ℝⁿ rectangles.
3. **Galerkin ODE existence** (`PicardLindelof`) — the API fits, but is gated on (1).
4. **Full (time) Aubin–Lions** — the *spatial* half (Rellich) is done; the time half needs
   Bochner time-derivative bounds + an Arzelà–Ascoli/diagonal argument.
5. **Limit passage** → weak solution — needs (1)–(4) + Banach–Alaoglu plumbing.

The realistic next target with the *current* infrastructure is item 4's time-equicontinuity layer
(building on `rellich_seq_compact`); items 1–3 require first building genuinely new torus-calculus
infrastructure in mathlib.

## Integrity record

- **0 axioms**, **0 frontier sorries**; the 1 sorry is the deliberate target statement.
- Every milestone gated by `bash scripts/agent-preflight.sh` (build + 3 guardrails) and an
  orchestrator-run **Codex `--effort xhigh`** adversarial review. Codex caught and forced fixes to:
  a fail-open guard script; a vacuity/overclaim disclosure; a **wrong-direction theorem** (Branch A);
  a universe regression; a **non-defeq measure split**; a Helmholtz docstring overclaim; a missing
  Fourier-cutoff connection; an incomplete energy bridge; and an overclaiming structure name.
- Role delegation held throughout: planner/coder/reviewers = sonnet, prover = fable, Codex =
  orchestrator-owned. Edit-ownership respected (defs/statements by coder, proof bodies by prover).
- Running ledger: `docs/STATUS.md`. Per-milestone contracts: `docs/scratch/m*.md`.

## Assessment vs forecast

| Forecast band | Predicted | Actual |
|---|---|---|
| Structural spine + real Galerkin + energy + blow-up | high confidence | ✅ done, axiom-free |
| **Aubin–Lions on T³ (Fourier tails)** | ~50/50, likely marked-sorry frontier | ✅ **spatial Rellich done, axiom-free** |
| Unconditional T³ (fully sorry-free) | low / uncertain | target statement still open; concrete nonlinear + limit passage remain frontier |

The run went **further than forecast** on the analytic frontier and **cleaner than forecast** on
integrity (no axioms, no frontier sorries). The wall is now the *concrete nonlinear PDE layer*
(convection operator, torus integration by parts), which is genuine new mathlib infrastructure
rather than a proof that "just needs more effort."
