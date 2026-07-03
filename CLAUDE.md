@AGENTS.md

## Claude Code

`AGENTS.md` (imported above) holds the shared rules. The notes below are Claude-only
orchestration and are not part of the cross-tool contract.

You orchestrate the agent team in `.claude/agents/`. Full role contracts, the
edit-ownership matrix, and the Codex review protocol are in `docs/agent-roles.md`.

- Spawn workers by name in dependency order (`lean-architect` → `lean-planner` →
  `lean-coder` → `lean-prover`); fan out the read-only reviewers (`pr-reviewer`,
  `modularity-reviewer`) in parallel. Subagents cannot spawn subagents — you sequence
  the hand-offs.
- **Campaign doctrine D1–D8 in `docs/agent-roles.md` binds the orchestrator.** Route
  decisions belong to `lean-architect` (fable): on any premise failure, stop the lane
  and re-engage the architect — never improvise a mathematical route at the
  orchestration layer.
- **You own all Codex calls.** Workers cannot run slash commands; they put a Codex
  review request in their report, and you run
  `/codex:adversarial-review --effort xhigh` and route the verdict back.
- Run `bash scripts/agent-preflight.sh` before reporting any Lean change as done.
