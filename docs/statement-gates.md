# Statement gates: reviewing `sorry`/scaffold theorem statements

This document is the process this repo follows so a public `sorry` theorem's *statement* gets
reviewed as carefully as its *proof* eventually will. It exists because that review failed once:
see `docs/postmortems/2026-07-w1ptime-false-statement.md` for the full incident
(`LerayHopf.Bochner.w1pTime_continuous_in_H` carried a false generic-exponent claim, unproved,
for months, and both the source docstrings and the `lean-pde-notes` annotations repeated it with
increasing confidence). Read that postmortem once; this document is the checklist it produced.

## Three separate gates

A `sorry`-carrying public declaration passes through three gates that must be reported
**separately** — passing one is not evidence for the others:

1. **Elaboration gate.** The declaration type-checks. Evidence: an actual `lake build` (local,
   or the `lean` workflow's manual `full-build` / `release-attestation` dispatch) passing.
   **Not evidence:** a green PR CI run by itself — on pull requests, CI runs only the fast
   textual guards (`scripts/check-*.sh`), never `lake build` (see `docs/build-and-checks.md`);
   a PR being green says nothing about elaboration.
2. **Axiom gate.** The declaration introduces no undeclared `axiom`/`opaque`/`unsafe`, and its
   `sorry` is marked `-- ALLOW_SORRY: <reason>`. Evidence: `scripts/check-no-axiom.sh`,
   `scripts/check-axioms.sh`, `scripts/check-axioms-live.sh`.
3. **Semantic (statement-truth) gate.** The declaration, as literally typed, is actually a true
   mathematical statement — the thing this document is about. A green build and a clean axiom
   pin say nothing about this; `w1pTime_continuous_in_H` had both while being false.

## Statement cards

Every declaration that carries a same-line `-- ALLOW_SORRY:` marker (i.e. every scaffold
`sorry` `scripts/check-no-sorry.sh` allows) must have a statement card at
`docs/statement-cards/<declaration-name>.md`. `scripts/check-statement-cards.sh` enforces this
in CI — a marked `sorry` with no card fails the build. Use the existing cards under
`docs/statement-cards/` as templates; each covers:

- **Exact type.** The literal Lean signature, not a paraphrase. If the file elides
  instance/`letI` lines for readability, say so and point at the source.
- **Literature reference,** where the statement names or is clearly drawn from a specific
  external theorem: edition, theorem number, and page if available. If no such reference
  applies (the statement is an assembly of standard facts, not a named theorem), say that
  explicitly rather than leaving the field silently blank — a missing citation and a
  deliberately-absent one must be distinguishable.
- **Hypothesis mapping.** Every hypothesis, mapped to the role it plays in making the
  conclusion true. If a hypothesis exists only to block a smuggled assumption (a "no-smuggle"
  hypothesis, in this repo's vocabulary — see `docs/STATUS.md`'s Stream D entries for examples),
  say so.
- **Consumer / special case.** What actually calls this declaration, and at what
  specialization. If a proof plan exists only for a special case (e.g. fixed exponents), the
  public signature must be restricted to that special case — see "Special-case rule" below.
- **Boundary-case checklist** (below) — which cases were actually checked.
- **Gate separation** — a one-line status for each of the three gates above.

## Adversarial substitution (exponent-parametric theorems)

If a declaration is parametric in an exponent, index, or other numeric hypothesis (`p`, `q`,
`n`, a dimension, …), the reviewer must substitute the *edge* values the stated hypotheses
permit — not just the value the author had in mind — and check whether the conclusion still
holds. `w1pTime_continuous_in_H`'s `hpq : 1 ≤ p ∧ 1 ≤ q` permitted `p = q = 1`; nobody had tried
it. This is not optional for exponent-parametric theorems and should be recorded on the
statement card as part of the boundary-case checklist.

## Boundary-case checklist

Every statement card runs this checklist (mark each item REVIEWED, N/A with a one-line reason,
or OPEN):

- **Weighted `ℓ²` / spike counterexample class.** Does a weighted sequence-space construction
  with a spike concentrating at a point (or accumulating boundary) break the statement? This is
  the exact class that falsified `w1pTime_continuous_in_H`'s generic form.
- **Noncomplete target space.** Does the statement implicitly need completeness of a Banach/
  Hilbert space that isn't hypothesized?
- **Nonmeasurable perturbation.** Does the statement implicitly need measurability that isn't
  hypothesized (a null-set modification, an a.e.-vs-everywhere confusion)?
- Domain-specific edge cases as applicable (endpoint exponents, degenerate intervals, empty
  index sets, …) — add these to the card rather than silently skipping them.

## Special-case rule

If the only proof plan that has ever been worked out for a declaration is at a specific
parameter value (a "spike" or scoping decision), the **public signature must be restricted to
that value**, not left generic "for later". A generalization ships together with its own proof
(or its own statement card re-running the full checklist at the new generality) — never ahead of
one. This is the rule `w1pTime_continuous_in_H`'s fix applied: the only analyzed proof route was
`p = q = 2`, so the public declaration is now `W1pTime GT 2 2 T uV`, not a generic
`{p q} (hpq : 1 ≤ p ∧ 1 ≤ q)`.

## Review independence

- At least one reviewer must perform a **blind statement review**: read the Lean type and its
  cited literature independently, without first reading the author's or a prior reviewer's
  confidence-laden prose ("genuine form", "faithful", "kept intact", "gate-approved", …). Those
  phrases describe process, not mathematics, and must never substitute for checking the type
  against a citation.
- When statements are reviewed in a large batch (many scaffold declarations at once), separate
  the **coverage review** (did every declaration get a docstring, does the file build) from the
  **mathematical review** (is each individual statement, checked against literature/adversarial
  substitution, actually true). A single "reviewed" pass over a large batch is not a substitute
  for per-declaration mathematical review — this is exactly how the false statement survived a
  "4-round adversarial statement gate" that never checked its actual exponent hypotheses.

## Regression guard

`scripts/check-statement-cards.sh` (wired into CI alongside the other textual guards in
`.github/workflows/lean.yml`) enforces two things mechanically:

1. `w1pTime_continuous_in_H` stays pinned at `p = q = 2` — a generic `{p q}` reintroduction fails
   the build.
2. Every `ALLOW_SORRY`-marked declaration has a statement card.

These are necessary, not sufficient — the guard cannot check that a card's *content* is honest,
only that one exists and that this one specific regression hasn't recurred. The process above
(adversarial substitution, blind review, batch-review separation) is what actually prevents a
recurrence; the guard is a backstop for the one failure mode that already happened once.
