#!/usr/bin/env bash
# Fail if an unmarked `sorry` appears in Lean sources.
#
# A `sorry` is permitted only when its OWN line carries a justification marker:
#     theorem foo : P := by sorry  -- ALLOW_SORRY: scaffold, proved in Milestone D
#
# Per-line markers are deliberate: they force every incomplete proof to be
# justified in place, so `sorry` cannot accumulate silently (No-sorry-creep rule).
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

found=0
while IFS= read -r -d '' file; do
  while IFS= read -r match; do
    lineno="${match%%:*}"
    content="${match#*:}"
    case "$content" in
      *ALLOW_SORRY:*) : ;; # justified in place, skip
      *) printf '%s:%s:%s\n' "$file" "$lineno" "$content"; found=1 ;;
    esac
  done < <(grep -nw 'sorry' -- "$file" 2>/dev/null || true)
done < <(find . -type f -name '*.lean' \
           -not -path './.lake/*' -not -path './.git/*' -print0)

if [ "$found" -ne 0 ]; then
  echo "ERROR: unmarked 'sorry' found above." >&2
  echo "Add '-- ALLOW_SORRY: <reason>' on the same line to justify, or finish the proof." >&2
  exit 1
fi
echo "OK: no unmarked 'sorry' in Lean sources."
