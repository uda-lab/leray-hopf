# Autonomous run — final report

> **Historical snapshot.** This report describes the original autonomous run (T³, branch
> `autorun/leray-hopf-torus3`) and is NOT updated to track the frontier. For the *current*
> axiom frontier and status see [`STATUS.md`](../STATUS.md), the repo [`README`](../../README.md),
> and the canonical live pin `scripts/check-axioms-live.sh`. As of 2026-07-05 BOTH capstones
> are **KERNEL-ONLY (0 project axioms)**:
> ℝ³ — `galerkin_limit_passage_R3` PROVED as a theorem (issue #4 PR-6, `LimitPassage.lean`);
> 𝕋³ — `aubin_lions` proved (issue #23, PR #89, `TorusAubinLionsAssembly.lean`).
> `#print axioms` for both = `[propext, Classical.choice, Quot.sound]`.
>
> **Also (2026-07-11, issue #112 PR-D):** the M1 scaffold files this report describes below
> (`GalerkinPackage.lean`, `ExistenceFromPackage.lean`, and their public names
> `GalerkinCompactnessPackage` / `exists_lerayHopf_from_galerkin_package`) have since been
> **deleted**, replaced by the generic `LerayHopf/Galerkin/` layer — see
> [`architecture.md`](../architecture.md) for the current module layout.

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

## M6 — sound minimal-axiom closure of T³ existence (post-run, strategic pivot)

After the axiom-free run reached the genuine analytic frontier, the strategy shifted (user
directive): **T³ is the warm-up, not the destination (R³ is)**. Rather than build the missing
torus-calculus tooling, the remaining T³ frontier was decomposed into **four minimal, true,
literature-referenced axioms**, closing the T³ existence theorem on an abstract framework built
for R³ reuse. Result:

```
exists_lerayHopf_torus3 (u₀ : L2Sigma) (ν > 0) (T > 0) :
    ∃ F : Torus3NSForms, Nonempty (LerayHopfSolutionFull F ν T u₀)     -- PROVED
```
`LerayHopfSolutionFull` is **proof-carrying**: weak NS equation (smooth/Galerkin div-free tests,
ν-scaled, compact support in (0,T)), the energy inequality on [0,T], the initial trace, and the
**energy class** `u ∈ L²(0,T;H¹_σ)`. `#print axioms` is now kernel-only
(`propext`/`Choice`/`Quot`), with **no project axioms** and **no `sorryAx`**.

**Historical note.** The earlier torus closure lived in
`LerayHopf/Torus/SolutionInterfaces.lean` and once bundled four project axioms:
`torus3_NSForms_exist`, `galerkin_ode_solution`, `aubin_lions`, and
`galerkin_limit_passage`. All four are now discharged; `b(u,u,u)=0` is a proved lemma.

**Integrity:** the axiom set survived an **8-round** Codex `--effort xhigh` adversarial audit
(→ approve) that forced fixes to a hidden inconsistency (under-specified forms), a false 3D bound,
an over-broad test space, sequence/interval faithfulness, the Stokes domain (∞ off H¹ ⇒
de-axiomatized to a concrete Fourier multiplier), the energy class, and measure-zero
representative invariance; plus a final assembly/faithfulness audit (→ approve). Foundational layer
(`H1Sigma.lean` incl. the proved `rellich_L2Sigma`; `EvolutionTriple.lean`) is **axiom-free**.

**R³-reuse note (honest):** the abstract `DissipativeEvolution`/`WeakFormNS` + the `AbstractEnergyLaw`
machinery are reusable; A1–A3 are currently stated *concretely* on T³ (the regularity-functional
resolution chosen for soundness), so the R³ instantiation re-states A1–A3 with R³ types reusing the
pattern, and needs its OWN spatial-compactness axiom (Rellich FAILS on ℝ³).

## R3 — whole-space ℝ³ Leray–Hopf weak existence (the real target, Leray 1934)

The abstract framework paid off: the ℝ³ pivot reused `DissipativeEvolution`/`WeakFormNS`/
`AbstractEnergyLaw` **unmodified**, and mathlib's ℝ³ harmonic analysis turned out rich enough to
build the spatial+regularity layer **axiom-free**.

```
exists_lerayHopf_r3 (u₀ : L2Sigma_R3) (ν > 0) (T > 0) :
    ∃ 𝔊 F, Nonempty (LerayHopfSolutionFull_R3 𝔊 F ν T u₀)     -- PROVED
```

**Built axiom-free** (`R3/Domain.lean`, `DivergenceFree.lean`, `Regularity.lean`):
`L2Sigma_R3 := ⨅ φ:𝓢, ker(divTestFunctional φ)` — the closed divergence-free subspace via **weak
divergence against Schwartz test functions** (avoiding the L²-Fourier-representative trap), the Leray
projection, `memH1VF_R3` via `TemperedDistribution.MemSobolev`, and `stokesTestPairing_R3`/
`viscousFormSq_R3` via the **L² Fourier isometry** `Lp.fourierTransformₗᵢ`, plus the genuine
convection integral `convIntegralSchwartz`.

**The 5 axioms** (was 6). Exactly the T³ four (`r3_NSForms_exist`, `galerkin_ode_solution_R3`,
`aubin_lions_R3`, `galerkin_limit_passage_R3`) **plus the one piece T³ proved but ℝ³ cannot
construct concretely**: `r3GalerkinScheme_exists` (the approximation projector — no finite-dim
Fourier truncation on ℝ³). The former sixth, `spatial_compactness_R3` (**local** Rellich
`H¹(B_R)↪↪L²(B_R)` — global Rellich *fails* on the unbounded domain), has now been **proved on ℝ³
and removed** (PR #35 / issue #2): it is a `theorem`, discharged via the sorry-free
Fréchet–Kolmogorov chain
(`localCompactness_R3_of_ballCompact ∘ localRellichInput_of_frechetKolmogorov ∘
frechetKolmogorov_holds`). That leaves a +1 honest cost of the whole space.

**Integrity.** Codex `--effort xhigh` axiom audit → approve in **2 rounds** (the 8-round T³ lessons
applied preemptively): it forced (i) a `range_schwartz` field to exclude the identity Galerkin scheme,
and (ii) reformulating compactness from *global* (false without tightness) to *local-on-balls* (true).
`#print axioms exists_lerayHopf_r3` = the 5 axioms + `propext`/`Choice`/`Quot`
(no `sorryAx`).

This is the project's headline result: **whole-space ℝ³ Leray–Hopf weak existence, closed modulo
five true, minimal, literature-referenced, Codex-audited axioms** (down from six — the first axiom
removal, `spatial_compactness_R3`, landed in PR #35), on a framework whose abstract core is
shared with the T³ proof.

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
