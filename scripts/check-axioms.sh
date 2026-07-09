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
#   1. Core.lean's direct imports do not include any capstone-only module.
#   2. The public capstone declarations use the release names (no `_axiomatic` suffix).
#   3. All axioms in the solution-interface files carry ALLOW_AXIOM markers.
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
# Gate 1: Core.lean must not import any capstone-only module.
# ---------------------------------------------------------------------------
CORE="LerayHopf/Core.lean"
CAPSTONE_MODULES=(
  "LerayHopf.Torus.SolutionInterfaces"
  "LerayHopf.R3.SolutionInterfaces"
  "LerayHopf.Torus.Capstone"
  "LerayHopf.R3Capstone"
)

if [ ! -r "$CORE" ]; then
  echo "ERROR: '$CORE' is missing or unreadable — cannot audit the import boundary." >&2
  exit 1
fi

for mod in "${CAPSTONE_MODULES[@]}"; do
  # Explicit grep status handling: 0 = violation, 1 = clean, >1 = scanner
  # failure (aborts). A bare `if grep -q` would conflate 1 and >1 because
  # `set -e` is suspended inside `if` conditions (fail-open).
  status=0
  grep -qE "^import[[:space:]]+${mod//./\\.}([[:space:]]|$)" "$CORE" || status=$?
  if [ "$status" -eq 0 ]; then
    echo "ERROR: $CORE imports capstone-only module '$mod'" >&2
    FAIL=1
  elif [ "$status" -gt 1 ]; then
    echo "ERROR: Core-import scan failed for '$mod' (grep exit $status)." >&2
    exit 1
  fi
done

# ---------------------------------------------------------------------------
# Gate 2: The public capstone theorems must use the release names.
#         Verify the old `_axiomatic` declarations are gone from Lean sources.
# ---------------------------------------------------------------------------
OLD_NAMES=("exists_lerayHopf_torus3_axiomatic" "exists_lerayHopf_r3_axiomatic")

for name in "${OLD_NAMES[@]}"; do
  # We only care about live declarations, not prose comments.
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
    echo "ERROR: stale declaration '${name}' found in Lean sources." >&2
    echo "  Issue #108 retires the `_axiomatic` suffix from the public API." >&2
    printf '%s\n' "$hits" >&2
    FAIL=1
  fi
done

# ---------------------------------------------------------------------------
# Gate 3: Solution-interface modules must not introduce un-annotated axioms.
#         (Redundant with check-no-axiom.sh, but makes the intent explicit here.)
# ---------------------------------------------------------------------------
INTERFACE_FILES=(
  "LerayHopf/Torus/SolutionInterfaces.lean"
  "LerayHopf/R3/SolutionInterfaces.lean"
  "LerayHopf/Torus/ConvectionForm.lean"
)

for f in "${INTERFACE_FILES[@]}"; do
  if [ ! -f "$f" ]; then
    echo "ERROR: expected interface file '$f' does not exist." >&2
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
echo "  Core.lean does not import capstone-only modules."
echo "  Public capstone theorems use the release names."
echo "  All axioms in the interface files are annotated ALLOW_AXIOM."
