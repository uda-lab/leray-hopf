# Agent roles

The reusable agent team for this project. These roles are used across the whole
roadmap; each milestone re-runs the same division of labor. The durable definitions
live in [`.claude/agents/`](../.claude/agents/) as subagent files; this document is the
contract that ties them together.

Read `AGENTS.md` (hard rules), `docs/guardrails.md` (rationale), and
`docs/agent-protocol.md` (operational protocol) alongside this file.

## Roster and model assignment

Model assignment is fixed by purpose: **fable** owns route decisions and the hardest
proof construction, **Codex (GPT-5.x, effort `xhigh`)** is the external
mathematical/formal reviewer, and **sonnet** runs everything mechanical.

| Role | Form | Model | Edits | One-line contract |
|---|---|---|---|---|
| `lean-architect` | subagent / permanent teammate | **fable** | `docs/scratch/` + `LerayHopf/Scratch/` | Route decisions, feasibility spikes, campaign plans, exact target statements |
| `lean-planner` | subagent | sonnet | `docs/scratch/` only | Architect-approved campaign phase → dispatch-ready task contract |
| `lean-prover` | subagent | **fable** default; campaign tier table may set sonnet/opus per node | **proof bodies only** | Make fixed statements `sorry`-free |
| `lean-coder` | subagent | sonnet | structure/signatures/imports | Stand up files, statements (verbatim from the architect), scaffolding |
| `pr-reviewer` | subagent | sonnet | none (read-only) | In-house guardrail gate on the diff |
| `modularity-reviewer` | subagent | sonnet | none (read-only) | Architecture / dependency-direction review |
| `sot-researcher` | subagent | sonnet | `docs/references/` only | Verified SSoT reference list |
| `codex-reviewer` | **orchestrator protocol** (not a subagent) | **Codex GPT-5.x `xhigh`** | none (review-only) | External soundness review of statements & proofs |

**Division of intelligence:** `lean-architect` (fable) concentrates the expensive
reasoning into *artifacts* — campaign docs, spikes, frozen statements — so that the
runtime orchestration loop can be driven by a cheaper model without route judgment.
`lean-planner` does not make mathematical route decisions; it sequences within an
architect-approved campaign.

## Edit-ownership matrix

A single boundary keeps the guardrails enforceable. **Exactly one role owns each kind
of edit:**

| Artifact | Owner | Everyone else |
|---|---|---|
| Proof body (`:= by …`) | `lean-prover` | read-only |
| Theorem/def signature, structure, imports, lakefile | `lean-coder` | read-only |
| Planning docs (`docs/scratch/`) | `lean-planner` | read-only |
| Reference list (`docs/references/`) | `sot-researcher` | read-only |
| Lean sources (any) | `lean-prover` / `lean-coder` | reviewers & researcher never edit Lean |

This is what makes the No-theorem-renaming and No-statement-weakening rules real: the
`lean-prover` cannot change a statement (it only edits proof bodies), and reviewers
cannot "fix" code into compliance — they report, the owners remediate.

## Codex review protocol (orchestrator-only)

Codex is the external mathematical reviewer. **Worker subagents cannot invoke it** — in
Claude Code, slash commands are an orchestrator/UI capability, and a subagent cannot run
`/codex:*` as a command. So Codex review is mediated by the orchestrator:

1. A worker (prover/coder) that wants review **states a Codex review request in its report**:
   target file(s), scope, and focus (e.g. "is this statement weaker than the plan intends?").
2. The **orchestrator runs it**:
   ```
   /codex:adversarial-review --effort xhigh [--base <ref>] [focus …]
   ```
   `--effort xhigh` is fixed for this project. The Codex model follows the local
   `/codex:setup` configuration (GPT-5.x). `adversarial-review` challenges the design and
   assumptions, which is the right posture for proof statements; `/codex:review` is the
   lighter defect pass.
3. The orchestrator captures Codex's verbatim output and routes it back to the owning
   worker as remediation. A Codex finding of *unsound proof* or *statement weaker than
   intended* is **blocking**.

**When to request Codex review:** at every new or changed **definition / theorem statement**
(the statement is the contract), after any non-trivial **proof**, and before a **milestone PR**.

**Codex write-delegation** (handing an implementation/rescue task to Codex, not review) uses
the codex plugin's shipped `codex-rescue` subagent via `task`; the orchestrator spawns it.

> Why orchestrator-only and not a Codex-driving worker subagent: the codex runtime is
> reachable from `Bash` (the plugin's own `codex-rescue` proves it), but that path depends on
> plugin-scoped state (`${CLAUDE_PLUGIN_ROOT}`) that is not guaranteed inside an arbitrary
> `.claude/agents/*.md` context. Keeping Codex at the orchestrator boundary is the robust choice.

## How to run the team

These subagents are plain `.claude/agents/*.md` definitions, so they work two ways:

- **Within one session (default):** the orchestrator spawns them via the Agent tool by
  `name` (e.g. spawn `lean-planner`, then `lean-coder`, then `lean-prover`), fanning out
  read-only reviewers in parallel. Subagents cannot spawn other subagents, so the
  orchestrator sequences hand-offs and owns all Codex calls.
- **As an experimental Agent Team:** with `CLAUDE_CODE_EXPERIMENTAL_AGENT_TEAMS=1`, the same
  definitions can back independent teammate sessions. The role contracts and edit-ownership
  matrix above are identical in both modes.

### Typical campaign loop

0. `lean-architect` → feasibility spike (`LerayHopf/Scratch/`) + campaign plan
   (`docs/scratch/<campaign>.md`) with GO/NO-GO verdict, tier table, kill criteria.
   **No scaffold before GO.**
1. `lean-planner` → per-phase task contract from the campaign doc.
2. (optional) `sot-researcher` → references for the milestone.
3. `lean-coder` → files + statements (verbatim from the architect) + scaffolding.
4. Orchestrator → `/codex:adversarial-review --effort xhigh` on the new statements
   (the statement gate); routes findings **to the architect** if a statement is refuted.
5. `lean-prover` (model per the campaign tier table) → proofs for must-prove targets.
6. Orchestrator → Codex review of the proofs; routes findings.
7. `pr-reviewer` + `modularity-reviewer` (parallel) → guardrail + architecture gates.
8. Land the PR only when the LOCAL incremental build is green, reviewers pass, and Codex
   findings are resolved.

## Campaign doctrine (anti-failure-mode rules, binding on the orchestrator)

Distilled from this project's recorded failures (unsound thin-swaps #44/#46, the R3
conjunct-2 wall discovered mid-build behind PR #69, false-green build reports, worktree
collisions, premature fable shutdowns). These rules bind the ORCHESTRATOR most of all.

- **D1 — Statement-first.** No proof dispatch until the statement typechecks in place and
  has passed the codex statement gate. Statements are frozen by `lean-architect`; provers
  never edit them; the orchestrator never "fixes" one to unblock a lane.
- **D2 — Spike-first, all conjuncts.** Every axiom-removal campaign starts with an
  architect spike that states EVERY field/conjunct of the target's conclusion against the
  real interfaces. A spike that validates a subset is not a GO.
- **D3 — No route improvisation.** On any premise failure (a planned statement does not
  typecheck, a planned lemma turns out false or unprovable-from-interface, codex refutes
  a step), the orchestrator STOPS that lane and returns it to `lean-architect`. The
  orchestrator never invents an alternative mathematical route, never weakens, never
  re-scopes, never "tries one more thing" past the plan.
- **D4 — Tiering with explicit escalation.** The campaign doc's tier table decides each
  node's model. Escalate sonnet→opus→fable after a bounded stall (default: ~1.5h of
  thrash or 2 failed attempts), explicitly and with the failure evidence attached — never
  silently retry the same tier, never keep a stalled tier grinding (the 3.4h Sonnet
  thrash of #47 is the cautionary precedent).
- **D5 — Fable permanence.** `lean-architect` / fable provers are permanent teammates for
  the campaign's duration: never casually shut down, never given mechanical chores; give
  them sonnet chore subordinates instead (disjoint file ownership). Re-engage idle
  mid-work agents rather than terminate+redispatch.
- **D6 — One writer per file; sequenced handoffs.** Never dispatch a second agent onto a
  live agent's worktree/branch; commit+push+confirm-stopped before a fresh dispatch;
  never `git add -A` in a shared tree.
- **D7 — Trust builds, not reports.** A worker's "build green" claim is unverified until
  the orchestrator sees the local incremental build (or CI) pass itself. Sorry-free
  claims require `#print axioms` / `check-axioms-live.sh` evidence.
- **D8 — Build discipline.** Local INCREMENTAL builds only (flock-serialized, warm
  `.lake`); full/cold builds are forbidden on this host; do not offload the gate to CI
  (see `docs/build-and-checks.md` and the STATUS build policy).
