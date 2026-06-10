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
| M2 | Real domain & function spaces (Torus3, L²(T³), L²_σ, H¹, Bochner) | pending |
| M3 | Galerkin P_n + Leray Π_div (Fourier multipliers) | pending |
| M4 | Finite-dim Galerkin ODE + energy identity | pending |
| M5–7 | Compactness + Aubin–Lions on T³ + limit passage → unconditional T³ | pending |

## Axiom ledger

_None yet._ Every entry must carry: same-line `-- ALLOW_AXIOM: <reason>`, a literature
reference, and the milestone that discharges it.

## Sorry frontier

_None yet._ Every entry must carry: same-line `-- ALLOW_SORRY: <blocker>`, the precise
statement it guards, and an attack note.

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

## Notes

- `exists_lerayHopf_torus3_statement` is intentionally a marked `sorry` while the
  underlying definitions are placeholders (No-vacuous-proof rule). It is **not** counted
  as frontier debt; it is the target statement.
