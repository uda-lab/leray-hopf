# Agent roles

The reusable agent team for this project. These roles are used across the whole
roadmap; each milestone re-runs the same division of labor. The durable definitions
live in [`.claude/agents/`](../.claude/agents/) as subagent files; this document is the
contract that ties them together.

Read `AGENTS.md` (hard rules), `docs/guardrails.md` (rationale), and
`docs/agent-protocol.md` (operational protocol) alongside this file.

## Roster and model assignment

Model assignment is fixed by purpose: **fable** drives proof construction, **Codex
(GPT-5.x, effort `xhigh`)** is the external mathematical/formal reviewer, and **sonnet**
runs everything else.

| Role | Form | Model | Edits | One-line contract |
|---|---|---|---|---|
| `lean-planner` | subagent | sonnet | `docs/scratch/` only | Milestone → ordered Lean task contract |
| `lean-prover` | subagent | **fable** | **proof bodies only** | Make fixed statements `sorry`-free |
| `lean-coder` | subagent | sonnet | structure/signatures/imports | Stand up files, statements, scaffolding |
| `pr-reviewer` | subagent | sonnet | none (read-only) | In-house guardrail gate on the diff |
| `modularity-reviewer` | subagent | sonnet | none (read-only) | Architecture / dependency-direction review |
| `sot-researcher` | subagent | sonnet | `docs/references/` only | Verified SSoT reference list |
| `codex-reviewer` | **orchestrator protocol** (not a subagent) | **Codex GPT-5.x `xhigh`** | none (review-only) | External soundness review of statements & proofs |

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

### Typical milestone loop

1. `lean-planner` → task contract in `docs/scratch/`.
2. (optional) `sot-researcher` → references for the milestone.
3. `lean-coder` → files + statements + scaffolding; requests Codex review of new statements.
4. Orchestrator → `/codex:adversarial-review --effort xhigh` on the new statements; routes findings.
5. `lean-prover` → proofs for must-prove targets; requests Codex review of non-trivial proofs.
6. Orchestrator → Codex review of the proofs; routes findings.
7. `pr-reviewer` + `modularity-reviewer` (parallel) → guardrail + architecture gates.
8. Land the PR only when build is green, reviewers pass, and Codex findings are resolved.
