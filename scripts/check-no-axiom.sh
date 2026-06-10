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

found=0
while IFS= read -r -d '' file; do
  while IFS= read -r match; do
    lineno="${match%%:*}"
    content="${match#*:}"
    case "$content" in
      *ALLOW_AXIOM:*) : ;; # documented assumption, skip
      *) printf '%s:%s:%s\n' "$file" "$lineno" "$content"; found=1 ;;
    esac
  done < <(grep -nE "$pattern" -- "$file" 2>/dev/null || true)
done < <(find . -type f -name '*.lean' \
           -not -path './.lake/*' -not -path './.git/*' -print0)

if [ "$found" -ne 0 ]; then
  echo "ERROR: undeclared axiom/constant/opaque/unsafe found above." >&2
  echo "Add '-- ALLOW_AXIOM: <reason>' on the same line and record it in the file's assumptions section." >&2
  exit 1
fi
echo "OK: no undeclared axiom/constant/opaque/unsafe in Lean sources."
