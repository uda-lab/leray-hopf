---
name: Theorem-statement concern
about: A declaration typechecks and has no stray axiom, but you believe what it literally says is false, mismatched with its prose, or ambiguous
title: "[statement] "
labels: bug
---

<!-- See docs/statement-gates.md for the three-gate framework (elaboration / axiom /
     semantic) this repository uses to review statements. This template is for the
     semantic gate. -->

## Declaration

- Name: `<fully-qualified name>`
- File / line:

## Concern

<!-- What is wrong: false as stated, overclaims relative to its docstring/README
     summary, silently narrower than the natural-language paraphrase, ambiguous
     quantifier scope, etc. -->

## Literal type

<!-- Paste the exact signature, not a paraphrase. If the file elides instance/`letI`
     lines for readability, say so. -->

## Suspected counterexample or boundary case (if applicable)

<!-- Per docs/statement-gates.md's adversarial-substitution rule: if the declaration
     is parametric in an exponent, index, dimension, etc., which edge value the
     stated hypotheses permit breaks it? -->

## Natural-language claim under review

<!-- Where this is stated in prose (README's Claims table, a docstring, other docs)
     and how that compares to the literal type above. -->
