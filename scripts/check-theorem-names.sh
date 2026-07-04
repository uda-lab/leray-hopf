#!/usr/bin/env bash
# Fail when a declaration name overclaims a completed Navier–Stokes result.
#
# Naming a theorem after a result it does not prove is the most dangerous form of
# overclaiming: a reader trusts the name, not the proof. This check flags
# declaration lines whose name contains a reserved term (No-overclaim rule).
#
# An intentional, justified use may be marked on the same line:
#     theorem clay_problem_statement ... -- ALLOW_NAME: statement only, not a proof
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

# Reserved terms that must not appear in declaration names. Extend as needed.
TERMS='millennium|global_regular|smooth_global|navier_stokes_solved|clay|uniqueness_solved|regularity_solved'

# Enumerate Lean sources fail-closed: `find` writes to a temp file and its exit
# status is checked BEFORE the list is consumed (a bare process substitution
# would swallow traversal errors and let a partial scan report OK). `.git`/`.lake`
# are pruned by basename at any depth (worktrees vendor their own `.lake`,
# issue #84); agent worktrees are scanned by their own CI.
list="$(mktemp)"
trap 'rm -f "$list"' EXIT
find . \( -name '.git' -o -name '.lake' -o -path './.claude/worktrees' \) -prune \
     -o -type f -name '*.lean' -print0 > "$list"

if [ ! -s "$list" ]; then
  echo "OK: no Lean sources to scan."
  exit 0
fi

# Single awk scan over all sources, fed via NUL-safe xargs batching
# (ARG_MAX-safe). Match: declaration line (keyword optionally preceded by
# attributes/modifiers) containing a reserved term case-insensitively
# (tolower), without an ALLOW_NAME justification. No here-strings and no
# per-file grep: a failing awk/xargs in any batch makes the plain command
# substitution non-zero, which `set -e` turns into an abort (fail-closed).
violations="$(xargs -0 awk -v terms="$TERMS" '
  /^[[:space:]]*(@\[[^]]*\][[:space:]]*)*((private|protected|noncomputable|scoped|local|nonrec)[[:space:]]+)*(theorem|lemma|def|abbrev|instance|structure|class)[[:space:]]/ && !/ALLOW_NAME:/ && tolower($0) ~ terms {
    printf "%s:%d:%s\n", FILENAME, FNR, $0
  }
' < "$list")"

if [ -n "$violations" ]; then
  printf '%s\n' "$violations"
  echo "ERROR: overclaiming declaration name(s) found above." >&2
  echo "Rename to describe what is actually proved, or add '-- ALLOW_NAME: <reason>' if this is a bare statement." >&2
  exit 1
fi
echo "OK: no overclaiming declaration names in Lean sources."
