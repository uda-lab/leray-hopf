# Security Policy

This repository is a Lean 4 + mathlib mathematical formalization. It has no running
service, no user data, and no network-facing component, so most of the usual
vulnerability-disclosure surface (the generic `SECURITY.md` template) does not apply
here.

## What to report here

- **A soundness issue** — a statement that typechecks but is false, overclaims, or is
  provable only via a hidden gap (an unmarked axiom, a silently narrowed hypothesis,
  …). This is the security-relevant failure mode for a formalization repository; see
  `docs/statement-gates.md` and
  `docs/postmortems/2026-07-w1ptime-false-statement.md` for a real incident. Report it
  with the "Theorem-statement concern" issue template, not as a generic bug.
- **A guard bypass** — a way to make `scripts/check-no-sorry.sh`,
  `scripts/check-no-axiom.sh`, `scripts/check-release-cone.sh`, or another discipline
  guard in `docs/guardrails.md` pass on code it is supposed to reject. Open an issue
  describing the bypass. There is currently no private disclosure channel for this
  repository — until one is established, report guard bypasses the same way as
  everything else, via a public issue.
- **Supply-chain concerns** — anything about the pinned mathlib revision
  (`lake-manifest.json`) or the CI workflow files (`.github/workflows/`) that looks
  tampered with or suspicious. Open an issue.

## What not to expect

There is no bug bounty, no CVE process, and no fixed response-time SLA — this is a
research-grade project maintained by a single owner and an AI agent team, not a
product with a security team.
