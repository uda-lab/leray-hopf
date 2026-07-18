# Contributing

This is a Lean 4 + mathlib formalization of Leray–Hopf weak existence for the
incompressible Navier–Stokes equations. It is currently maintained by a single owner
plus an AI agent team (`docs/agent-roles.md`); this document exists so an external
contributor can work here without reconstructing that context from issue history. It
points at the existing documentation rather than duplicating it.

## Before you start

Read, in this order:

1. [`AGENTS.md`](AGENTS.md) — hard rules (no theorem renaming, no unmarked `sorry`,
   no silent axioms, no vacuous proofs, …).
2. [`docs/guardrails.md`](docs/guardrails.md) — why those rules exist, and what CI
   enforces mechanically vs. what review enforces.
3. [`docs/build-and-checks.md`](docs/build-and-checks.md) — how to build and which
   checks to run.
4. [`docs/statement-gates.md`](docs/statement-gates.md) — how theorem *statements*
   (not just proofs) get reviewed. Read this once even if you are not touching a
   statement — it explains a class of bug this repository has actually shipped; see
   [`docs/postmortems/2026-07-w1ptime-false-statement.md`](docs/postmortems/2026-07-w1ptime-false-statement.md).

## Scope of contributions

This repository is still in its pre-release cleanup phase (tracked by the umbrella
[#145](https://github.com/uda-lab/leray-hopf/issues/145)); it is not yet actively
soliciting external contribution. Issues — bug reports, statement concerns, build
failures — are welcome at any time; see the templates below. For a substantial PR (a
new lemma, a new module, a route change), open an issue first and wait for triage
before investing the work: the edit-ownership matrix in
[`docs/agent-roles.md`](docs/agent-roles.md) reflects how proof/statement work is
currently divided, and an unsolicited large PR may not fit it.

## Build-cost policy

Do **not** run a full, cold `lake build` to prepare a PR — it is expensive, and this
repository's CI deliberately never runs one automatically. The gates are layered:

- **What you run locally, every time:** `bash scripts/agent-preflight.sh` — an
  incremental `lake build` plus every textual discipline guard. This is the
  mandatory gate, enforced by the `pre-push` git hook once activated
  (`git config core.hooksPath scripts/hooks`; see `docs/build-and-checks.md`).
- **What PR CI runs:** only the fast textual guards (the `guards` job in
  `.github/workflows/lean.yml`) — no Lean build at all. A green PR CI run is
  evidence for the axiom/naming/sorry guards, not for elaboration; see the "three
  gates" in `docs/statement-gates.md` for why that distinction matters.
- **What you do *not* need to produce:** a full/cold build or a release-candidate
  attestation. Those run manually, on demand, by the maintainer (`workflow_dispatch`
  on the `lean` workflow, and the separate `release-attestation` workflow); see
  `docs/build-and-checks.md`. Do not block a PR on producing one yourself.
- **Dependency updates:** bumping the pinned mathlib revision (`lake update`) is an
  explicit, maintainer-only task, not something to do as a side effect of an
  unrelated PR — `lake-manifest.json` is the reproducibility source of truth; see
  `docs/build-and-checks.md`.

## Statement-changing PRs: natural-language translation review

If your PR adds or changes the signature of a public theorem or definition (not just
its proof body), the PR description must include a natural-language paraphrase of
what the declaration actually claims, checked against its literal Lean type — not
copied from a docstring or an earlier claim. This is the semantic gate described in
[`docs/statement-gates.md`](docs/statement-gates.md): the elaboration and axiom gates
say nothing about whether a statement is *true* or matches its prose description,
and this repository has shipped a false generalization that passed both of those
gates (see the postmortem linked above). Follow the format already used by
[`README.md`](README.md)'s "Claims table" — one row per claim, matched to the exact
field/theorem that carries it. If the declaration is parametric in an exponent,
index, or dimension, check the edge values the hypotheses actually permit (the
adversarial-substitution rule in `docs/statement-gates.md`), not just the value you
had in mind. A declaration carrying a same-line `-- ALLOW_SORRY:` marker also needs a
statement card under `docs/statement-cards/`, enforced by
`scripts/check-statement-cards.sh`.

## Issue and PR conventions

- Title prefix `[P0]`–`[P3]` and, where applicable, `Parent: #<umbrella>` — see the
  priority table in [#145](https://github.com/uda-lab/leray-hopf/issues/145). This
  convention is specific to maintainer-tracked cleanup work; it is optional for a
  fresh external bug report.
- PR body: `Closes #<issue>` if the PR fully resolves it, `Refs #<issue>` if it is
  partial. Every PR / handoff should report what `AGENTS.md` asks for: files
  changed, theorem/def names added, remaining `sorry` (count + locations), new
  assumptions, and whether the local build passed.
- Use the issue templates under `.github/ISSUE_TEMPLATE/` (bug report,
  theorem-statement concern, build failure); blank issues are also allowed for
  anything that does not fit.

## Security and conduct documents

[`SECURITY.md`](SECURITY.md) exists but is intentionally narrow — this is a
formalization repository with no runtime attack surface or user data. A code of
conduct has not been added: there is no established enforcement process here (a
reporting contact, an escalation path), and adopting boilerplate text without one
would be exactly that — boilerplate without substance. Whether to adopt one, and who
the contact would be, is left as an open decision for the maintainer.
