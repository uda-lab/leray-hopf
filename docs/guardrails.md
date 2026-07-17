# Guardrails

Project-wide mathematical and engineering guardrails. Each rule states what it is,
why it matters, and what to do instead. CI enforces the mechanical ones
(`scripts/check-*.sh`); the rest are enforced by review (`pr-reviewer`, Codex).

## No-overclaim rule

- **What:** A declaration must not be named, documented, or summarized as a result it
  does not prove. Reserved terms (`millennium`, `global_regular`, `navier_stokes_solved`,
  `clay`, …) are blocked in declaration names by `check-theorem-names.sh`.
- **Why:** Readers and downstream proofs trust names and summaries. A misleading name is
  a silent false claim that can propagate.
- **Instead:** Name for what is actually proved. If it is only a statement, say so and
  mark it `-- ALLOW_NAME: statement only`.

## No-silent-axiom rule

- **What:** No `axiom`, `constant`, `opaque`, or `unsafe` without a same-line
  `-- ALLOW_AXIOM: <reason>` and an entry in the file's assumptions section.
- **Why:** Each one silently widens the trusted base; an unaudited axiom can make the
  whole development vacuously "provable".
- **Instead:** Package deferred analytical results as *explicitly marked* axioms with a
  documented intent, so the assumption ledger stays visible.

## No-sorry-creep rule

- **What:** No `sorry` without a same-line `-- ALLOW_SORRY: <reason>`.
- **Why:** Unmarked `sorry` accumulates and hides which proofs are real.
- **Instead:** Justify each gap in place, or finish the proof. Track allowed `sorry` as work.

## No-incomplete-in-release-cone rule

- **What:** No `sorry` — marked or unmarked — may be reachable from `import LerayHopf` (the
  root release surface). `scripts/check-release-cone.sh` walks the transitive import closure
  of `LerayHopf.lean` statically and fails on any `sorry` it finds there, with no
  `ALLOW_SORRY` exemption (unlike `check-no-sorry.sh`, which permits a justified `sorry`
  anywhere in the repo).
- **Why:** A justified, tracked `sorry` is still an incomplete proof; the public root import
  should not surface incomplete work even when each gap is individually accounted for.
- **Instead:** Move incomplete modules behind an explicit opt-in import, e.g.
  `LerayHopf.Experimental` (issue #147), and document what is incomplete in its docstring.

## No-vacuous-proof rule

- **What:** Do not replace a theorem's content with `True`, `Nonempty _`, or any trivially
  satisfiable proposition to make it "pass".
- **Why:** A vacuous statement compiles but proves nothing — the worst kind of green build.
- **Instead:** Keep the meaningful statement; if blocked, leave it with a marked gap and report.

## No-fallback-definition rule

- **What:** Do not swap a real definition for a placeholder to unblock a build, unless the
  file is explicitly marked scaffold-only.
- **Why:** Downstream lemmas then prove things about the placeholder, not the intended object.
- **Instead:** Refine definitions monotonically (placeholder → real), never silently regress.

## No-theorem-renaming rule

- **What:** Do not rename an existing theorem target unless explicitly instructed.
- **Why:** Names are the public interface; renames break references and obscure history.
- **Instead:** Keep the name; if a rename is truly needed, get explicit instruction and update callers.

## Small-PR rule

- **What:** Keep each change small and single-purpose; prefer many small lemmas/PRs.
- **Why:** Small diffs are reviewable, and Codex/PR review is only as good as the diff's focus.
- **Instead:** Split unrelated work; land the architectural spine before filling proofs.

## Build-first rule

- **What:** `lake build` must pass before and after a change; never report success otherwise.
- **Why:** A red build invalidates every other claim in the report.
- **Instead:** Run `scripts/agent-preflight.sh`; fix or revert until green, then report status honestly.
