<!-- Full contributor workflow: see CONTRIBUTING.md -->

## Summary

<!-- What changed and why. -->

Closes #<!-- issue number, or write `Refs #<n>` instead if this PR only partially addresses it -->

## Files changed / declarations added or renamed

<!-- Per AGENTS.md "Every PR / handoff must report". -->

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

- [ ] `bash scripts/agent-preflight.sh` passed locally (incremental build + all discipline guards)
- [ ] For a change touching `.lean` / `lakefile` / `lean-toolchain`: the local build is green (do not report success otherwise — see AGENTS.md's "Build-first rule")
- [ ] No full/cold `lake build` was required for this review — see CONTRIBUTING.md's build-cost policy if you believe one is needed
