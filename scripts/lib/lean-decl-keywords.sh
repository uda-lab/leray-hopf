#!/usr/bin/env bash
# This file is SOURCED, never executed directly — the shebang above exists only
# to declare the target shell for shellcheck/editors, not as an entry point.
#
# Shared Lean 4 top-level declaration-command vocabulary (issue #151 PR #172
# review, round 2). `check-theorem-names.sh` and `check-release-cone.sh` each
# independently duplicated their own copy of "which keyword introduces a named
# declaration", and both copies missed `inductive` — exactly the drift a single
# shared source is meant to prevent. Any guard that needs "is this line a Lean
# declaration line, and if so what identifier does it introduce" should source
# this file (`. "$(dirname "${BASH_SOURCE[0]}")/lib/lean-decl-keywords.sh"`,
# path relative to the sourcing script) rather than hardcode its own list.
#
# `axiom`/`constant`/`opaque`/`unsafe` are deliberately NOT included: they
# widen the kernel's trusted base rather than merely introduce a name and are
# governed by the separate, dedicated axiom-class checks (`check-no-axiom.sh`,
# `check-axioms.sh`, and `check-release-cone.sh`'s own axiom scan) — folding
# them into this list would blur that distinction. `mutual` is not included
# either: a `mutual ... end` block's members are each introduced by their own
# ordinary keyword line (`def`/`theorem`/...), so the per-line scan already
# reaches them without special-casing the wrapping block. `example` is also
# excluded: in Lean 4 it is always anonymous and cannot carry a qualified name.
#
# Scoped to what this repository's policy actually needs to recognize (a pure
# mathematics formalization, not a metaprogramming/tactic-extension codebase):
# no `macro`/`syntax`/`elab`/`notation`. If a future PR introduces one of those
# as a real top-level declaration form, extend this list then.
LEAN_DECL_KEYWORDS='theorem|lemma|def|abbrev|instance|structure|class|inductive'
LEAN_DECL_MODIFIERS='private|protected|noncomputable|scoped|local|nonrec|partial'
