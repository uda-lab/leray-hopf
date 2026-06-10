# STATUS — autonomous run ledger

Running ledger for the autonomous build of Leray–Hopf weak existence on the real
3-torus. This file is the **integrity backstop and final report**: every `sorry` and
every `axiom` in the Lean sources is listed here with a reason, a reference, and a
plan to discharge it. Higher-level scope/posture: the approved plan and `docs/milestone.md`.

**Posture:** maximal depth, minimal axioms. Prove what mathlib supports; axiomatize only
the true frontier; leave provable-but-unfinished pieces as *marked* `sorry`, never as
weakened/vacuous statements.

**Branch:** `autorun/leray-hopf-torus3` · **target:** unconditional T³ existence.

## Milestone status

| # | Milestone | State |
|---|---|---|
| M1 | Structural spine (Basic/Statement/GalerkinPackage/ExistenceFromPackage/EnergySkeleton) | in progress |
| Side A/B | Blow-up lower bound · nonuniqueness statement | pending |
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

## Notes

- `exists_lerayHopf_torus3_statement` is intentionally a marked `sorry` while the
  underlying definitions are placeholders (No-vacuous-proof rule). It is **not** counted
  as frontier debt; it is the target statement.
