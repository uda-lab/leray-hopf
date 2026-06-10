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

decl='^[[:space:]]*(@\[[^]]*\][[:space:]]*)*((private|protected|noncomputable|scoped|local|nonrec)[[:space:]]+)*(theorem|lemma|def|abbrev|instance|structure|class)[[:space:]]'

found=0
while IFS= read -r -d '' file; do
  while IFS= read -r match; do
    lineno="${match%%:*}"
    content="${match#*:}"
    case "$content" in
      *ALLOW_NAME:*) continue ;; # explicitly justified
    esac
    if printf '%s' "$content" | grep -qiE "$TERMS"; then
      printf '%s:%s:%s\n' "$file" "$lineno" "$content"
      found=1
    fi
  done < <(grep -nE "$decl" -- "$file" 2>/dev/null || true)
done < <(find . -type f -name '*.lean' \
           -not -path './.lake/*' -not -path './.git/*' -print0)

if [ "$found" -ne 0 ]; then
  echo "ERROR: overclaiming declaration name(s) found above." >&2
  echo "Rename to describe what is actually proved, or add '-- ALLOW_NAME: <reason>' if this is a bare statement." >&2
  exit 1
fi
echo "OK: no overclaiming declaration names in Lean sources."
