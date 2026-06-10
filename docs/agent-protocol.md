# Agent protocol

Operational protocol for AI agents working on this Lean formalization. Read
`AGENTS.md` first; this document expands the operational detail.

## 1. Mission

Formalize Leray–Hopf weak existence as scoped in `docs/milestone.md` and
`docs/leray_hopf_lean_mvp_plan.md`, advancing one small, reviewed, build-green step
at a time, without ever overstating what has been proved.

## 2. Source-of-truth hierarchy

When two sources conflict, the higher one wins:

1. The user's instruction in the current task.
2. The project plan files (`docs/milestone.md`, `docs/leray_hopf_lean_mvp_plan.md`).
3. `AGENTS.md`.
4. Existing Lean theorem statements already in the repository.
5. `README.md` and the rest of `docs/`.

If a higher source is silent, defer to the next; never invent scope that no source supports.

## 3. Allowed actions

- Add or complete proofs within your edit-ownership boundary (`docs/agent-roles.md`).
- Add small local lemmas, definitions, and files that the plan calls for.
- Introduce a packaged assumption *as a marked `axiom`* when the plan explicitly
  defers a result (e.g. compactness), recorded in the file's assumptions section.
- Refactor locally when it does not change any statement's meaning.

## 4. Forbidden actions

- Renaming, weakening, or vacuously discharging a theorem (see `AGENTS.md` rules 2–4).
- Adding `axiom`/`constant`/`opaque`/`unsafe` without a marker and assumptions entry.
- Encoding an analytical hypothesis into a name to make it look proved.
- Reporting success without a green `lake build`.
- Broad, unrequested refactors that touch unrelated files.

## 5. Proof-attempt protocol

1. Restate the goal and list the hypotheses you actually have.
2. Search mathlib for existing API before hand-rolling.
3. Prefer a chain of small named lemmas to one large tactic block.
4. Keep the statement fixed; only the proof term may change.
5. Re-run preflight; confirm no new `sorry`/axiom slipped in.

## 6. Failure protocol

If you cannot complete a proof:

- **Do not** patch around it by weakening the mathematics.
- **Do not** delete or strengthen-away a difficult hypothesis.
- **Do not** add an axiom silently to close the goal.
- **Do not** replace a definition with a placeholder unless the file is explicitly
  scaffold-only.
- Leave the statement intact, mark the gap with `-- ALLOW_SORRY: <reason>` or a
  `-- TODO:`, and **report the exact blocker** (the goal state and what API is missing).

## 7. Reporting protocol

End every task with the report block required by `AGENTS.md`: files changed,
names added, remaining `sorry`, new assumptions, and `lake build` status. When you
hand off, state the precise next action and any open blocker — no vague summaries.
