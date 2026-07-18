<!-- Full contributor workflow: see CONTRIBUTING.md -->

## Summary

<!-- What changed and why. -->

Closes #<!-- issue number, or write `Refs #<n>` instead if this PR only partially addresses it -->

## Files changed / declarations added or renamed

## Remaining `sorry` (count + locations)

## New assumptions (`axiom`/`opaque`/`unsafe` added, with justification)

## Statement-changing PR? Natural-language translation review

<!-- Required whenever this PR adds or changes a public theorem/def statement. See
     CONTRIBUTING.md's "Statement-changing PRs" section and docs/statement-gates.md
     (semantic gate, blind review). Expected format: the literal type vs. the
     natural-language claim, checked independently — not a paraphrase that claims
     more than the type. -->

- [ ] N/A — no statement changed
- [ ] Reviewed: <!-- summarize the natural-language claim and how it was checked against the literal type -->

## Validation

<!-- Describe what you actually ran, proportionate to the change — see
     CONTRIBUTING.md's "Build-cost policy". There is no single mandatory gate
     imposed on every contributor; `agent-preflight.sh` is this project's internal
     agent-team tooling, not a required external-contributor step. Never report a
     build as green without having run it (docs/guardrails.md's "Build-first
     rule"). -->

- [ ] Docs/templates-only change (no scripts, workflows, or hooks touched) — no build applicable; the CI `guards` job is the relevant check
- [ ] Other non-Lean change (a `scripts/check-*.sh` guard, CI workflow, or git hook) — how you verified it:
- [ ] `.lean` / `lakefile.toml` / `lean-toolchain` changed — local build result:
- [ ] Full/cold `lake build`, if run (optional; stronger evidence when you have the resources for it):
- [ ] Discipline guards run and how (e.g. `agent-preflight.sh`, the `pre-push` hook, or individual `scripts/check-*.sh`):
