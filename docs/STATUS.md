# STATUS — autonomous run ledger

Running ledger for the autonomous build of Leray–Hopf weak existence on the real
3-torus. This file is the **integrity backstop and final report**: every `sorry` and
every `axiom` in the Lean sources is listed here with a reason, a reference, and a
plan to discharge it. Higher-level scope/posture: the approved plan and `docs/milestone.md`.

## Goal (authoritative)

Build the Leray–Hopf weak-existence formalization on the **real 3-torus**, bottom-up on
mathlib, as far as possible toward an **unconditional T³ existence theorem**
(`u₀ ∈ L²_σ(𝕋³) ⇒ ∃ Leray–Hopf weak solution`). Reduce anything not closable to a
**documented marked-`sorry` frontier** with exact statements. R³ is out of scope.

Roadmap: M1 spine ✅ → M2 real domain & function spaces → M3 Galerkin `Pₙ` + Leray `Π_div`
→ M4 finite-dim Galerkin ODE + energy identity → M5–7 compactness + Aubin–Lions on T³
(Fourier-tail Rellich, the crux) + limit passage ⇒ unconditional T³.

**Posture:** maximal depth, minimal axioms. Prove what mathlib supports; axiomatize only
the true frontier (each with `ALLOW_AXIOM` + reference + ledger entry); leave
provable-but-unfinished pieces as *marked* `sorry`, never as weakened/vacuous/renamed
statements.

**Method:** branch `autorun/leray-hopf-torus3`, 1 milestone = 1 commit gated by
`bash scripts/agent-preflight.sh` green. Strict role delegation to subagents
(planner/coder/reviewers = sonnet, prover = fable; read-only reviewers) under their
`.claude/agents/*.md` contracts; orchestrator owns Codex `--effort xhigh` calls and
maintains this ledger as the final report.

## Milestone status

| # | Milestone | State |
|---|---|---|
| M1 | Structural spine (Basic/Statement/GalerkinPackage/ExistenceFromPackage/EnergySkeleton) | in progress |
| Side A/B | Blow-up lower bound · nonuniqueness statement | done (pending commit) |
| M2 | Real domain & function spaces (Torus3, L²(T³), L²_σ, H¹, Bochner) | **done** (axiom-free) |
| M3 | Galerkin P_n + Leray Π_div (Fourier multipliers) | in progress (part 1 done) |
| M4 | Finite-dim Galerkin ODE + energy identity | pending |
| M5–7 | Compactness + Aubin–Lions on T³ + limit passage → unconditional T³ | pending |

## M2 design decisions (orchestrator, adopted)

- **0-A velocity codomain:** `VelocityValue := EuclideanSpace ℝ (Fin 3)` (physically faithful
  ℝ³ energy inner product). Fourier work uses component-wise ℝ↪ℂ embedding, made explicit.
- **0-B measure normalization:** probability/Haar (total mass 1), consistent with `mFourierBasis`
  (`AddCircleMulti` uses `haarAddCircle`). The `volume` vs `haarAddCircle` definitional match at
  `T = 1` is a known M2 friction point (planner D-06); to be verified by lean-coder.

## Axiom ledger

_Empty — and intentionally so._

The M2 plan tentatively proposed one axiom (`L2Sigma_eq_divFreeL2`, the closure-of-span ↔
Fourier-diagonal equivalence). **Eliminated** under the minimal-axiom posture: `L²_σ` is
defined *directly* as `⨅ k, ker (divSymbol k)` — the common kernel of the continuous
divergence-symbol functionals `divSymbol k : L²(𝕋³;ℝ³) →L[ℝ] ℂ`, `u ↦ ∑_j (k_j) û_j(k)`.
Membership then coincides with `DivFreeL2` *by construction* (no axiom), and `L²_σ` is a
closed submodule (intersection of closed kernels), giving its Hilbert structure and the
Leray orthogonal projection for free. The "closure of divergence-free Fourier modes"
description becomes an optional later *theorem*, not an assumption.

## Sorry frontier

_Empty._ Through M2 there is **zero** frontier debt: the only `sorry` in the tree is the
deliberate target statement `exists_lerayHopf_torus3_statement` (not counted as frontier —
see Notes). No axioms. Every M1–M2 must-prove target is sorry-free and `#print axioms`-clean.

Bochner time spaces `L²(0,T;X)` (planned M2 item) are deferred to M4/M5 where the Galerkin
solution actually lives in them; mathlib's Banach-valued `Lp` covers them when needed.

## Known scaffold caveats (disclosed, not hidden)

These are deliberate properties of the M1 scaffold, recorded so they are never mistaken
for proved mathematics. Each is discharged by the monotone refinement of placeholders.

- **`ExistsLerayHopf` is vacuous at M1.** `LerayHopfSolution`'s analytical fields are free
  `Prop` placeholders, so `ExistsLerayHopf Ω u₀` is structurally inhabited and is *not*
  yet a meaningful existence claim. `exists_lerayHopf_from_galerkin_package` is therefore a
  real but currently low-content implication (package ⟹ solution). The target
  `exists_lerayHopf_torus3_statement` is kept as a marked `sorry` and must **not** be
  discharged via a junk package. _Discharge:_ M2+ refines the `Prop` fields into real
  predicates (`WeakEquation`, `EnergyClass`, …) tied to the candidate field, `u₀`, `Ω`,
  after which the implication carries genuine analytical content.
- **`Torus3` is a fresh placeholder with the zero measure**, not the real torus. The zero
  measure is intentionally wrong-but-honest (signals "unrealized"). _Discharge:_ M2 realizes
  `Torus3 := UnitAddTorus 3` with Haar/volume measure.

## Codex adversarial-review log

- **M1 spine** (`/codex:adversarial-review --effort xhigh`, working tree): verdict
  *needs-attention*, 3 findings.
  - [high] no-sorry guard could fail open → **fixed**: `scripts/check-no-sorry.sh` rewritten
    to fail closed (single non-suppressed `awk`; scanner error ⇒ nonzero exit; verified by test).
  - [medium] `Torus3 := ℝ` leaked real-line semantics → **fixed**: fresh `PUnit`-backed
    placeholder with zero measure.
  - [high] structural theorem vacuous / `ExistsLerayHopf` overclaim risk → **disclosed** (see
    "Known scaffold caveats"); structural redesign deferred to M2+ refinement per the
    plan-authoritative interface. Not closable at M1 without real function spaces.
- **Side A/B** (`--effort xhigh`, working tree): verdict *needs-attention*, 2 findings.
  - [high] Branch A `lower_bound_from_inverse_square_lifespan` proved the *opposite* direction
    (an upper bound on `N`), overclaiming its name. The MVP-plan code sketch was itself
    inconsistent with Branch A's stated lower-bound intent. → **fixed**: statement flipped to
    the genuine lower bound (`C/N² ≤ T−t ⇒ 1/N ≤ √((T−t)/C)`, i.e. `N ≥ √(C/(T−t))`),
    reproved sorry-free by lean-prover.
  - [medium] Branch B `LerayHopfNonunique` froze initial data at universe 0 (non-monotone vs
    the `Type*` interface) → **fixed**: explicit `universe u v`, `Ω : Type u`, `u₀ : Type v`.
- **M2-part1 function spaces** (`--effort xhigh`, `FunctionSpaces.lean`/`TorusDomain.lean`):
  verdict *needs-attention*, 2 findings, both fixed.
  - [high] two non-defeq torus measures (`L2VF` on `volume`, `L2C`/basis on `haarTorus3`)
    would force measure-transport at every M3 boundary → **fixed**: unified all torus L²
    spaces on the single canonical `haarTorus3`; added proven bridge
    `volume_torus3_eq_haarTorus3`.
  - [medium] `mFourierCoeff3` doc claimed a global-`volume` integral while `L2C` is Haar-based
    (Parseval-divergence risk) → **fixed**: redefined `mFourierCoeff3 := torus3_mFourierBasis.repr`.
  - `IsProbabilityMeasure (volume : Measure UnitAddCircle)` instance confirmed sound/non-conflicting.
- **M2 `DivFreeL2`** (`--effort xhigh`, `DivergenceFree.lean`): verdict *approve*. Confirmed the
  Fourier characterization `∑_j k_j û_j(k)=0 ∀k` faithfully encodes `div u = 0` (2π/i
  normalization cancels in the `=0` condition), `compLpL` a.e. semantics correct, non-vacuous.
- **M2 `L2Sigma`** (`--effort xhigh`, `Leray.lean`): verdict *approve*. `⨅ k, ker(divSymbol k)`
  is the genuine divergence-free subspace by construction; closedness sound (continuous kernels
  + arbitrary closed intersection); axiom-free (`#print axioms`: only propext/Choice/Quot).
- **M3-part1 projections** (`--effort xhigh`, `Leray.lean`/`GalerkinProjection.lean`): verdict
  *needs-attention*, 2 findings, both fixed.
  - [medium] `lerayProjection` docstring overclaimed a Helmholtz gradient-kernel theorem not
    formalized → **fixed**: docstring states only the proved orthogonal-projection facts
    (kernel = `L2Sigma`ᗮ); Helmholtz identification flagged as future work.
  - [medium] `Pₙ` not connected to Fourier truncation → **fixed**: proved
    `fourierProjection_n_mFourierCoeff` (`P̂ₙf(k) = if k ∈ box then f̂(k) else 0`), the genuine
    Fourier-multiplier formula, sorry-free/axiom-clean. Leray projection (idempotent, range,
    self-adjoint, contraction, fixes div-free) + `Pₙ` convergence `Pₙf→f` all sorry-free.

## Notes

- `exists_lerayHopf_torus3_statement` is intentionally a marked `sorry` while the
  underlying definitions are placeholders (No-vacuous-proof rule). It is **not** counted
  as frontier debt; it is the target statement.
