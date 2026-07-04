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

# ^ [attrs]* [modifiers]* (keyword) <space>
pattern='^[[:space:]]*(@\[[^]]*\][[:space:]]*)*((private|protected|noncomputable|scoped|local)[[:space:]]+)*(axiom|constant|opaque|unsafe)[[:space:]]'

# Enumerate Lean sources fail-closed: `find` writes to a temp file and its exit
# status is checked BEFORE the list is consumed (a bare process substitution
# would swallow traversal errors and let a partial scan report OK). `.git`/`.lake`
# are pruned by basename at any depth (worktrees vendor their own `.lake`,
# issue #84); agent worktrees are scanned by their own CI.
list="$(mktemp)"
trap 'rm -f "$list"' EXIT
find . \( -name '.git' -o -name '.lake' -o -path './.claude/worktrees' \) -prune \
     -o -type f -name '*.lean' -print0 > "$list"

found=0
while IFS= read -r -d '' file; do
  # Distinguish grep "no match" (1) from tool/read failure (>1): only the
  # former may continue; anything else aborts the guard (fail-closed).
  status=0
  matches="$(grep -nE "$pattern" -- "$file")" || status=$?
  if [ "$status" -gt 1 ]; then
    echo "ERROR: scanner failed on '$file' (grep exit $status)." >&2
    exit 1
  fi
  [ -n "$matches" ] || continue
  while IFS= read -r match; do
    lineno="${match%%:*}"
    content="${match#*:}"
    case "$content" in
      *ALLOW_AXIOM:*) : ;; # documented assumption, skip
      *) printf '%s:%s:%s\n' "$file" "$lineno" "$content"; found=1 ;;
    esac
  done <<< "$matches"
done < "$list"

if [ "$found" -ne 0 ]; then
  echo "ERROR: undeclared axiom/constant/opaque/unsafe found above." >&2
  echo "Add '-- ALLOW_AXIOM: <reason>' on the same line and record it in the file's assumptions section." >&2
  exit 1
fi
echo "OK: no undeclared axiom/constant/opaque/unsafe in Lean sources."
