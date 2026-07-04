#!/usr/bin/env bash
# FAST STATIC PRE-FILTER for the axiom-leak gate.
#
# This script is a grep-based STRUCTURAL check — it is fast (no Lean compilation)
# but it only sees DIRECT imports of Core.lean, not transitive ones.
# It is a necessary-but-not-sufficient gate.
#
# The real backstop is `scripts/check-axioms-live.sh`, which runs
# `lake env lean scripts/print_axioms.lean` and asserts the EXACT axiom sets
# for both capstones and two Core representatives via `#print axioms`.
# That live job catches transitive leaks this static check cannot.
#
# Two-tier design:
#   check-axioms.sh      — fast static pre-filter (this file); fails on direct violations.
#   check-axioms-live.sh — live `#print axioms` pin; catches transitive leaks.
#   Together they are fail-closed.
#
# What this file checks:
#   1. Core.lean's direct imports do not include any axiomatic module.
#   2. Bare capstone names (without _axiomatic) are absent from Lean sources.
#   3. All axioms in axiomatic files carry ALLOW_AXIOM markers.
#
# FAIL-CLOSED: set -euo pipefail; any grep/awk failure aborts with nonzero status.

set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

FAIL=0

# Shared fail-closed enumeration of Lean sources (same shape as the sibling
# guards): `find` writes to a temp file and its exit status gates consumption.
# Prunes `.git`/`.lake` by basename at any depth and the anchored agent
# worktree path only — NOT any directory that merely happens to be named
# "worktrees" (that would be a path-based scan bypass).
list="$(mktemp)"
trap 'rm -f "$list"' EXIT
find . \( -name '.git' -o -name '.lake' -o -path './.claude/worktrees' \) -prune \
     -o -type f -name '*.lean' -print0 > "$list"

# ---------------------------------------------------------------------------
# Gate 1: Core.lean must not import any axiomatic module.
# ---------------------------------------------------------------------------
CORE="LerayHopf/Core.lean"
AXIOMATIC_MODULES=(
  "LerayHopf.AxiomaticClosure"
  "LerayHopf.R3.AxiomaticClosure"
  "LerayHopf.TorusAxiomatic"
  "LerayHopf.R3Axiomatic"
)

if [ ! -r "$CORE" ]; then
  echo "ERROR: '$CORE' is missing or unreadable — cannot audit the import boundary." >&2
  exit 1
fi

for mod in "${AXIOMATIC_MODULES[@]}"; do
  # Explicit grep status handling: 0 = violation, 1 = clean, >1 = scanner
  # failure (aborts). A bare `if grep -q` would conflate 1 and >1 because
  # `set -e` is suspended inside `if` conditions (fail-open).
  status=0
  grep -qE "^import[[:space:]]+${mod//./\\.}([[:space:]]|$)" "$CORE" || status=$?
  if [ "$status" -eq 0 ]; then
    echo "ERROR: $CORE imports axiomatic module '$mod'" >&2
    FAIL=1
  elif [ "$status" -gt 1 ]; then
    echo "ERROR: Core-import scan failed for '$mod' (grep exit $status)." >&2
    exit 1
  fi
done

# ---------------------------------------------------------------------------
# Gate 2: The axiom-dependent capstone theorems must end in _axiomatic.
#         Verify the old bare names are gone from the Lean sources.
# ---------------------------------------------------------------------------
BARE_NAMES=("exists_lerayHopf_torus3" "exists_lerayHopf_r3")

for name in "${BARE_NAMES[@]}"; do
  # Allow the name only when immediately followed by _axiomatic (i.e. as a prefix)
  # or when it appears inside a comment or the _axiomatic variant itself.
  # We want to catch bare `theorem exists_lerayHopf_torus3 ` declarations.
  # awk over the shared find list (xargs-batched): no match is exit 0, and any
  # tool failure makes the plain command substitution non-zero, which `set -e`
  # turns into an abort. (grep-through-xargs would conflate "no match" with
  # tool failure via xargs exit 123; a previous `grep -r --exclude-dir` form
  # both swallowed scanner errors and excluded ANY dir named "worktrees".)
  hits="$(xargs -0 awk -v name="$name" '
    $0 ~ ("(^|[[:space:]])(theorem|def|abbrev)[[:space:]]+" name "([[:space:]]|$|\\()") {
      printf "%s:%d:%s\n", FILENAME, FNR, $0
    }
  ' < "$list")"
  if [ -n "$hits" ]; then
    echo "ERROR: bare (non-_axiomatic) declaration '${name}' found in Lean sources." >&2
    echo "  Rename it to '${name}_axiomatic' as required by Issue #1 item 3." >&2
    printf '%s\n' "$hits" >&2
    FAIL=1
  fi
done

# ---------------------------------------------------------------------------
# Gate 3: Axiomatic modules must not introduce un-annotated axioms.
#         (Redundant with check-no-axiom.sh, but makes the intent explicit here.)
# ---------------------------------------------------------------------------
AXIOMATIC_FILES=(
  "LerayHopf/AxiomaticClosure.lean"
  "LerayHopf/R3/AxiomaticClosure.lean"
  "LerayHopf/TorusConvectionForm.lean"
)

for f in "${AXIOMATIC_FILES[@]}"; do
  if [ ! -f "$f" ]; then
    echo "ERROR: expected axiomatic file '$f' does not exist." >&2
    FAIL=1
    continue
  fi
  # All axiom/opaque/unsafe lines must carry ALLOW_AXIOM markers.
  # Single awk pass per file (plain command substitution): a read/tool
  # failure makes the assignment non-zero and `set -e` aborts the guard.
  # The previous `grep … 2>/dev/null || true` + here-string loop could
  # convert a tool failure or here-string temp-file failure into an empty
  # match set — a false "all annotated" audit result (fail-open).
  bad="$(awk '
    /^[[:space:]]*(@\[[^]]*\][[:space:]]*)*((private|protected|noncomputable|scoped|local)[[:space:]]+)*(axiom|constant|opaque|unsafe)[[:space:]]/ && !/ALLOW_AXIOM:/ {
      printf "%s:%d:%s\n", FILENAME, FNR, $0
    }
  ' "$f")"
  if [ -n "$bad" ]; then
    echo "ERROR: undocumented axiom/constant/opaque/unsafe in '$f':" >&2
    printf '%s\n' "$bad" >&2
    FAIL=1
  fi
done

# ---------------------------------------------------------------------------
# Report
# ---------------------------------------------------------------------------
if [ "$FAIL" -ne 0 ]; then
  echo "AXIOM GATE FAILED — see errors above." >&2
  exit 1
fi

echo "OK: axiom-leak gate passed."
echo "  Core.lean does not import axiomatic modules."
echo "  Capstone theorems carry _axiomatic suffix."
echo "  All axioms in axiomatic files are annotated ALLOW_AXIOM."
