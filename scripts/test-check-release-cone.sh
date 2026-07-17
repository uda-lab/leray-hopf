#!/usr/bin/env bash
# Regression tests for scripts/check-release-cone.sh (issue #151).
#
# PR #172's review (owner + Codex, independently) caught a real bypass — the
# original namespace check matched only an UNqualified reserved namespace
# (`namespace Scaffold`), so `namespace LerayHopf.Scaffold` passed unflagged —
# plus a second bug: the axiom/namespace scans ran on raw lines instead of the
# comment-stripped text the sorry scan already used, so a code-like example
# inside a module docstring could trip them. A manual, uncommitted probe caught
# neither issue reliably. This script is the requested COMMITTED, EXECUTABLE
# regression coverage: it builds isolated fixture trees (never touching the real
# LerayHopf/ sources — see check-release-cone.sh's optional $1/$2 args) and
# asserts the guard's pass/fail verdict on each.
#
# FAIL-CLOSED: set -euo pipefail.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
GUARD="$ROOT/scripts/check-release-cone.sh"

if [ ! -x "$GUARD" ] && [ ! -r "$GUARD" ]; then
  echo "ERROR: '$GUARD' is missing or unreadable." >&2
  exit 1
fi

TMPBASE="$(mktemp -d)"
trap 'rm -rf "$TMPBASE"' EXIT

FAIL=0

# Builds a two-file fixture project (root LerayHopf.lean importing
# LerayHopf/Case.lean, the only file that varies per case) under
# $TMPBASE/<name>/, runs the guard against it, and asserts the guard's exit
# status matches $expect_pass (0 = guard must accept the fixture, 1 = guard must
# reject it). `$3` is passed as the file's body verbatim via a positional
# parameter (not eval/here-doc) so no case body can be mis-parsed as shell.
run_case() {
  name="$1"; expect_pass="$2"; body="$3"
  dir="$TMPBASE/$name"
  mkdir -p "$dir/LerayHopf"
  printf 'import LerayHopf.Case\n' > "$dir/LerayHopf.lean"
  printf '%s\n' "$body" > "$dir/LerayHopf/Case.lean"

  status=0
  out="$(bash "$GUARD" "$dir" "LerayHopf.lean" 2>&1)" || status=$?

  if [ "$expect_pass" = "0" ] && [ "$status" -ne 0 ]; then
    echo "FAIL [$name]: expected the guard to ACCEPT this fixture (no real violation), but it rejected it (exit $status):" >&2
    printf '%s\n' "$out" >&2
    FAIL=1
  elif [ "$expect_pass" != "0" ] && [ "$status" -eq 0 ]; then
    echo "FAIL [$name]: expected the guard to REJECT this fixture, but it accepted it:" >&2
    printf '%s\n' "$out" >&2
    FAIL=1
  else
    echo "OK [$name]"
  fi
}

# --- Cases the guard MUST reject ---

run_case "unqualified-namespace" 1 '
namespace Scaffold
theorem placeholderThm : True := trivial
end Scaffold
'

# The bypass reported in PR #172 review: a reserved word as a NON-FIRST
# component of a qualified namespace path.
run_case "qualified-namespace" 1 '
namespace LerayHopf.Scaffold
theorem placeholderThm : True := trivial
end LerayHopf.Scaffold
'

# Lean 4 allows declaring directly under a dotted name with no enclosing
# `namespace ... end` block at all.
run_case "qualified-declaration" 1 '
theorem LerayHopf.Scaffold.placeholderThm : True := trivial
'

# The round-2 bypass reported in PR #172 review: `inductive` was missing from
# the recognized declaration-keyword set, so a qualified `inductive` name under
# a reserved namespace passed unflagged even though `theorem`/`def`/etc. did not.
run_case "qualified-inductive-declaration" 1 '
inductive LerayHopf.Scaffold.Token where
  | mk
'

# `partial` is a real Lean 4 declaration modifier (`partial def`); confirms the
# centralized modifier vocabulary (lib/lean-decl-keywords.sh) is actually wired
# in, not just the keyword vocabulary.
run_case "partial-modifier-qualified-declaration" 1 '
partial def LerayHopf.Scaffold.loopForever (n : Nat) : Nat :=
  LerayHopf.Scaffold.loopForever (n + 1)
'

run_case "marked-axiom" 1 '
axiom fakeAxiom : True  -- ALLOW_AXIOM: intentionally marked; must still be rejected in-cone
'

run_case "unmarked-sorry" 1 '
theorem hasSorry : True := by sorry
'

# --- Cases the guard MUST accept ---

run_case "clean" 0 '
theorem realThm : True := trivial
'

# Regression case for the second PR #172 review bug: code-like text inside a
# block-comment docstring must not trip any of the three checks.
run_case "block-comment-non-violation" 0 '
/-
Documentation example only — none of the lines below are real code, so the
guard must NOT trip on any of them:
  axiom exampleAxiom : True
  namespace Scaffold
  sorry
-/
theorem realThm2 : True := trivial
'

if [ "$FAIL" -ne 0 ]; then
  echo "REGRESSION TEST FAILURE — see FAIL lines above." >&2
  exit 1
fi

echo "OK: all check-release-cone.sh regression cases behaved as expected."
