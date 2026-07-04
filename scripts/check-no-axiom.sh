#!/usr/bin/env bash
# Fail on undeclared trust-extending declarations in Lean sources:
#     axiom   constant   opaque   unsafe
#
# These widen the trusted base or hide content behind an irreducible term. They
# are permitted only when the declaration line carries a justification marker:
#     axiom aubin_lions_torus3 : ...  -- ALLOW_AXIOM: packaged compactness, Milestone 6
#
# Matching is anchored to declaration-leading keywords (optionally preceded by
# attributes/modifiers), so words inside comments, identifiers, or strings do not
# trip the check (No-silent-axiom rule).
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

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
# (ARG_MAX-safe). Match: declaration-leading keyword — optionally preceded by
# attributes/modifiers — whose line lacks an ALLOW_AXIOM marker. No
# here-strings and no per-file grep: a failing awk/xargs in any batch makes
# the plain command substitution non-zero, which `set -e` turns into an
# abort, so the guard fails closed.
violations="$(xargs -0 awk '
  /^[[:space:]]*(@\[[^]]*\][[:space:]]*)*((private|protected|noncomputable|scoped|local)[[:space:]]+)*(axiom|constant|opaque|unsafe)[[:space:]]/ && !/ALLOW_AXIOM:/ {
    printf "%s:%d:%s\n", FILENAME, FNR, $0
  }
' < "$list")"

if [ -n "$violations" ]; then
  printf '%s\n' "$violations"
  echo "ERROR: undeclared axiom/constant/opaque/unsafe found above." >&2
  echo "Add '-- ALLOW_AXIOM: <reason>' on the same line and record it in the file's assumptions section." >&2
  exit 1
fi
echo "OK: no undeclared axiom/constant/opaque/unsafe in Lean sources."
