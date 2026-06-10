#!/usr/bin/env bash
# Fail if an unmarked `sorry` appears in *code* in Lean sources.
#
# A `sorry` is permitted only when its OWN line carries a justification marker:
#     theorem foo : P := by sorry  -- ALLOW_SORRY: scaffold, proved in Milestone D
#
# Per-line markers are deliberate: they force every incomplete proof to be
# justified in place, so `sorry` cannot accumulate silently (No-sorry-creep rule).
#
# Only a `sorry` token in actual code counts. The word may appear freely in
# documentation prose — line comments (`-- …`) and block comments (`/- … -/`,
# `/-! … -/`, nested) are stripped before matching, so "sorry-free" and
# "marked sorry" in a docstring do not trip the check. The ALLOW_SORRY marker,
# which lives in the trailing line comment, is still honored on real code lines.
#
# FAIL-CLOSED by design: the comment-aware scan is a single `awk` over all files
# with NO error suppression. `set -euo pipefail` makes any scanner or portability
# failure abort the script with a nonzero status, so a broken check can never
# report success.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

# Collect Lean sources (NUL-safe; survives spaces/newlines in paths).
files=()
while IFS= read -r -d '' f; do
  files+=("$f")
done < <(find . -type f -name '*.lean' \
           -not -path './.lake/*' -not -path './.git/*' -print0)

if [ "${#files[@]}" -eq 0 ]; then
  echo "OK: no Lean sources to scan."
  exit 0
fi

# Comment-aware scanner. Maintains block-comment nesting across lines (reset per
# file), strips line comments, and prints `file:line:content` for any code line
# whose CODE portion holds a whole-word `sorry` but whose full line lacks an
# ALLOW_SORRY marker. Any awk failure propagates (no `|| true`, no `2>/dev/null`),
# so the guard fails closed.
violations="$(awk '
  FNR == 1 { depth = 0 }
  {
    line = $0; code = ""; inLine = 0
    n = length(line); i = 1
    while (i <= n) {
      two = substr(line, i, 2)
      if (depth > 0) {
        if (two == "-/") { depth--; i += 2; continue }
        if (two == "/-") { depth++; i += 2; continue }
        i++; continue
      }
      if (inLine) { i++; continue }
      if (two == "--") { inLine = 1; i += 2; continue }
      if (two == "/-") { depth++; i += 2; continue }
      code = code substr(line, i, 1); i++
    }
    if (code ~ /(^|[^A-Za-z0-9_])sorry([^A-Za-z0-9_]|$)/ && line !~ /ALLOW_SORRY:/)
      printf "%s:%d:%s\n", FILENAME, FNR, line
  }
' "${files[@]}")"

if [ -n "$violations" ]; then
  printf '%s\n' "$violations" >&2
  echo "ERROR: unmarked 'sorry' found above." >&2
  echo "Add '-- ALLOW_SORRY: <reason>' on the same line to justify, or finish the proof." >&2
  exit 1
fi
echo "OK: no unmarked 'sorry' in Lean sources."
