@AGENTS.md

## Claude Code

`AGENTS.md` (imported above) holds the shared rules. The notes below are Claude-only
orchestration and are not part of the cross-tool contract.

You orchestrate the agent team in `.claude/agents/`. Full role contracts, the
edit-ownership matrix, and the Codex review protocol are in `docs/agent-roles.md`.

- Spawn workers by name in dependency order (`lean-planner` → `lean-coder` →
  `lean-prover`); fan out the read-only reviewers (`pr-reviewer`,
  `modularity-reviewer`) in parallel. Subagents cannot spawn subagents — you sequence
  the hand-offs.
- **You own all Codex calls.** Workers cannot run slash commands; they put a Codex
  review request in their report, and you run
  `/codex:adversarial-review --effort xhigh` and route the verdict back.
- Run `bash scripts/agent-preflight.sh` before reporting any Lean change as done.
