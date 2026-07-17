# Postmortem: `w1pTime_continuous_in_H`'s false generic statement (issue #158)

**Severity:** P0 — mathematical soundness of a public `sorry` specification.
**Status:** source-side fix merged (issues #147/#158, PR #162 + follow-ups); this document is
the permanent contributor-facing record. See `docs/statement-gates.md` for the process this
postmortem motivated.

## Summary

`LerayHopf.Bochner.w1pTime_continuous_in_H` is the "good representative" embedding a
Lions–Magenes-class argument is supposed to supply: given `u ∈ L^p(0,T;V)` with weak time
derivative `u' ∈ L^q(0,T;V')`, it claims a continuous-into-`H` a.e. representative exists. The
declaration carried this claim, unproved (`sorry`), at the generic hypothesis
`hpq : 1 ≤ p ∧ 1 ≤ q`. **That statement is false.** `1 ≤ p` and `1 ≤ q` are enough to make the
individual Bochner integrands defining `u` and `u'` integrable on a finite interval, but they do
not make the *dual pairing* `t ↦ ⟨u'(t), u(t)⟩_{V',V}` — which the standard proof route needs,
via Hölder — integrable. An explicit counterexample at `p = q = 1` (below) exhibits a pair
`(u, u')` satisfying every stated hypothesis with no `H`-continuous a.e. representative.

The only case ever actually analyzed in this repo (the issue #4 proof spike,
`docs/scratch/spike1-lions-magenes-verdict.md`) is `p = q = 2`, using Cauchy–Schwarz on
`L²(V') × L²(V)`. The fix restricts the declaration to exactly that case.

## The counterexample

Take `H = ℓ²` with a weighted Hilbert triple on the standard basis `eₙ`:

```
‖eₙ‖_V = 2ⁿ,   ‖eₙ‖_H = 1,   ‖eₙ‖_{V'} = 2⁻ⁿ
```

On pairwise-disjoint time intervals accumulating at `0`, place triangular spikes
`u(t) = φₙ(t) eₙ`, each of height `1` (in the `eₙ` direction) and width `δₙ = 4⁻ⁿ`. Then:

```
∑ₙ ‖u‖_{L¹(V),n} ≲ ∑ₙ 2ⁿ · 4⁻ⁿ = ∑ₙ 2⁻ⁿ < ∞
∑ₙ ‖u'‖_{L¹(V'),n} ≲ ∑ₙ 2⁻ⁿ < ∞     (each spike's total variation is O(1) in H, hence O(2⁻ⁿ) in V')
```

so `u ∈ L¹(0,T;V)` and `u' ∈ L¹(0,T;V')` — the hypotheses hold at `p = q = 1`. But the `H`-norm
of `u` peaks at `1` on each spike and is `0` between spikes, with the peaks accumulating at `0`;
no `H`-continuous a.e. representative can smooth over infinitely many order-`1` jumps
accumulating at a point. On each spike's interior, two continuous curves that agree a.e. must
agree everywhere, so a null-set modification cannot remove the peak either. `p = q = 1` directly
falsifies the statement as it was declared.

## Timeline

1. **Scaffold introduction** (commit `95571d3`): part of a 6-file, 4-stream scaffold of deferred
   theorems. `sorry` from the start; `hpq : 1 ≤ p ∧ 1 ≤ q` was already the stated hypothesis.
   Commit message and docstring recorded "genuine Lions–Magenes form", "statement kept intact",
   "4-round adversarial statement gate approved" — with no evidence any of those checks matched
   the named theorem's exact exponent hypotheses against a citation.
2. **Nearby defects fixed, this one carved out of scope:** real statement defects elsewhere in
   `TimeSobolev.lean` (limit measurability, non-complete-target Bochner collapse,
   `W1pTime.ofHValuedDeriv`'s `p, q < 1` integrability gap) were found and fixed. This
   declaration was set aside as a "months-class residual" / "separate frontier" — so the
   nearby gate's real successes lent unearned confidence to the one theorem nobody had actually
   audited.
3. **Proof analysis specialized silently:** the issue #4 Lions–Magenes spike that actually
   examined a proof route used `p = q = 2` throughout (the energy-pairing limit passage needs
   Cauchy–Schwarz on `L²(V') × L²(V)`). The public signature was never narrowed to match.
4. **Declared dead / off-critical-path** (commit `7bb9b27`): confirmed unused anywhere in the
   codebase, off both capstones' critical path — still described as "true, faithful" at the
   point its review priority was downgraded. Because neither capstone imports it, the
   kernel-only axiom pin stayed clean and could not detect the false public statement.
5. **Notes amplified the source's self-assessment:** `lean-pde-notes` PR #24 added it as
   generic-prose `tier: full`; PR #48 upgraded it to handwritten annotation. That review
   correctly fixed a notation error (`W^{1,p}(V)` → the actual `u ∈ L^p(V), u' ∈ L^q(V')` Lean
   type) but did not check `p, q` compatibility, and restated the false claim in more confident,
   more fluent prose — "the claim is preserved at its original strength" — while citing the same
   source docstring the source side was also trusting. Source and notes were not an independent
   double-check; they shared one unverified assumption.

## Root causes (antipatterns)

1. **Named-theorem anchoring** — trusting the name "Lions–Magenes" to supply the familiar
   `p = q = 2` hypotheses mentally, without checking the actual Lean binders.
2. **Accidental quantifier inflation** — generalizing a proved-only-at-`(2,2)` result to
   arbitrary `p, q` with no proof.
3. **Separate vs. joint integrability confusion** — `u ∈ L^p` and `u' ∈ L^q` individually does
   not make the dual pairing `⟨u', u⟩` integrable; that needs an explicit exponent-compatibility
   condition.
4. **`sorry`-green-build fallacy** — treating successful elaboration as evidence of a true
   statement.
5. **Honest-sorry ⇒ true-statement fallacy** — treating the honesty of marking something
   unproved as evidence the *statement* is correct.
6. **Special-case proof / general API mismatch** — the only proof plan ever developed was for
   `(2, 2)`; the public signature stayed generic.
7. **Dead-theorem rot** — no consumer meant lower proof priority, but the claim stayed live in
   the public namespace and in generated documentation regardless.
8. **Self-referential verification** — notes treated the (wrong) source docstring as an
   authoritative literature citation, so source and notes review looked independent but shared
   one unverified premise.
9. **Large-batch review dilution** — the theorem was one of ~61 annotations reviewed together;
   theorem-level literature matching for any single one was thin.
10. **Consensus without independence** — implementation, statement-gate review, and notes review
    all inherited the same confidence-laden prose; none independently searched for a
    counterexample.
11. **Claim laundering** — "genuine", "faithful", "gate-approved", "true" were repeated as
    process language, standing in for actual mathematical verification.

## What was fixed, and where

- **Signature correction** (issue #158, folded into PR #162 as part of the #147 extraction):
  `w1pTime_continuous_in_H` is now stated only at `p = q = 2` —
  `(W : W1pTime GT 2 2 T uV)`, no generic `p, q` binder — in
  `LerayHopf/Bochner/TimeSobolevExperimental.lean:71`. Pure signature narrowing on a still-`sorry`
  declaration: no proof content added or removed; zero live consumers existed anywhere in the
  codebase, so nothing else could break.
- **Docstring/status sync:** `TimeSobolevExperimental.lean`, `LerayHopf/Experimental.lean`,
  `TimeSobolev.lean`, `README.md`, `docs/STATUS.md`, `docs/architecture.md`,
  `docs/pdelib-staging.md`, `docs/references/mathlib-api-survey.md` all replaced the "genuine
  form / statement kept intact" framing with the restriction and an explanation of why the
  generic form was false. `docs/scratch/*` (internal working notes, not curated documentation
  per the README) were intentionally left as a historical record rather than rewritten.
- **Regression guard:** `scripts/check-statement-cards.sh` fails CI if
  `w1pTime_continuous_in_H` ever reverts to a generic `{p q}`-parametric signature, and requires
  every `ALLOW_SORRY`-marked declaration to carry a `docs/statement-cards/<name>.md` entry (see
  `docs/statement-gates.md`).
- **Statement cards:** all 6 current sorry sites now have a card under
  `docs/statement-cards/` — including the 5 declarations that were never false, so the ledger is
  complete rather than reactive to just the one incident.
- **Notes/site follow-up** (tracked separately in the `lean-pde-notes` release umbrella, not
  this repo): quarantining the false annotation, repinning to the corrected source SHA,
  separating `tier`/`proof_status`, surfacing `contains-sorry`/`invalid-statement` in the UI.

## Recurrence-prevention process (see `docs/statement-gates.md` for the full policy)

- A statement card is required for every public `sorry` theorem: exact type, literature
  reference with edition/theorem number where one exists, hypothesis-to-role mapping, consumer
  special case, and a boundary-case checklist.
- Exponent-parametric theorems require an adversarial-substitution check (try the extreme/edge
  exponents, not just the intended one) before merging.
- The boundary-case checklist itself — weighted `ℓ²` / spike, noncomplete target, nonmeasurable
  perturbation — is now a standing item on every statement card, not just this one.
- Special-case-only proof plans require special-case-only public signatures; generalizing ahead
  of the proof is the mistake this postmortem documents.
- Elaboration, axiom, and semantic (statement-truth) gates are reported separately — a passing
  build and a `sorryAx`-free axiom pin are evidence for the first two, never the third.
- At least one blind statement review (no prior confidence prose read) is required before a
  batch of scaffold statements is accepted.
- Large annotation batches separate coverage review from mathematical review; a single
  "reviewed" pass over many declarations is not a substitute for per-declaration literature
  matching.
