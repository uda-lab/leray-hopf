#!/usr/bin/env bash
# Strict release-cone guard (issue #147): the transitive import closure of the root
# `LerayHopf.lean` module — the release surface a plain `import LerayHopf` pulls in —
# must contain ZERO `sorry` tokens in code, marked or unmarked.
#
# This is intentionally STRICTER than `check-no-sorry.sh`: an `-- ALLOW_SORRY:`
# marker justifies a `sorry` existing in the repo at all, but a justified sorry
# still must not be reachable from the public root import. Incomplete work belongs
# behind an explicit opt-in import (`LerayHopf.Experimental`), never in the
# release cone.
#
# WITHOUT lake: the closure is computed by statically parsing `import LerayHopf.*`
# lines from source text (no `lake env`, no compilation). Non-project imports
# (`Mathlib.*`, etc.) are not project sources and are skipped — they cannot carry
# a project `sorry`.
#
# FAIL-CLOSED: set -euo pipefail; any parse/scan failure aborts nonzero, never
# reports success on a partial scan.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

ENTRY="LerayHopf.lean"
if [ ! -r "$ENTRY" ]; then
  echo "ERROR: root module '$ENTRY' is missing or unreadable — cannot compute the release cone." >&2
  exit 1
fi

# --- Step 1: compute the transitive import closure of $ENTRY, restricted to
# project modules (paths under LerayHopf/). BFS over a worklist; `seen` tracks
# visited files to break cycles and avoid rescanning. ---
worklist="$(mktemp)"
seen="$(mktemp)"
closure="$(mktemp)"
trap 'rm -f "$worklist" "$seen" "$closure"' EXIT

printf '%s\n' "$ENTRY" > "$worklist"

while [ -s "$worklist" ]; do
  next="$(mktemp)"
  while IFS= read -r file; do
    [ -z "$file" ] && continue
    grep -qxF "$file" "$seen" 2>/dev/null && continue
    printf '%s\n' "$file" >> "$seen"
    printf '%s\n' "$file" >> "$closure"

    if [ ! -r "$file" ]; then
      echo "ERROR: '$file' is imported into the release cone but missing/unreadable." >&2
      exit 1
    fi

    # Extract each `import LerayHopf.X.Y` line's module token, drop any trailing
    # line comment, translate dots to path separators, append `.lean`. Only
    # project-internal imports (module path starting with `LerayHopf.`) are
    # followed — anything else (Mathlib, Init, Std, ...) is not a project source
    # and cannot itself carry a project `sorry`.
    #
    # `grep` (not a here-string source) is captured into a variable rather than
    # piped into `while read`: under `pipefail`, a file with ZERO matching import
    # lines makes `grep` exit 1, and piping that straight into a loop would abort
    # the whole script via `set -e`. Capturing with `|| true` absorbs the no-match
    # case without masking a genuine downstream failure.
    matches="$(grep -E '^[[:space:]]*import[[:space:]]+LerayHopf\.' "$file" || true)"
    if [ -n "$matches" ]; then
      while IFS= read -r line; do
        mod="$(printf '%s\n' "$line" | sed -E 's/^[[:space:]]*import[[:space:]]+([A-Za-z0-9_.]+).*/\1/')"
        printf '%s\n' "${mod//./\/}.lean"
      done <<< "$matches" >> "$next"
    fi
  done < "$worklist"
  sort -u "$next" > "$worklist"
  rm -f "$next"
done

if [ ! -s "$closure" ]; then
  echo "ERROR: release cone is empty — closure computation produced no files." >&2
  exit 1
fi

sort -u "$closure" -o "$closure"

# --- Step 2: comment-aware `sorry` scan over exactly the closure files. Same
# block/line-comment stripper as check-no-sorry.sh, but with NO ALLOW_SORRY
# exemption: any code-level `sorry` token in the release cone is a violation,
# justified or not. ---
violations="$(xargs -0 awk '
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
    if (code ~ /(^|[^A-Za-z0-9_])sorry([^A-Za-z0-9_]|$)/)
      printf "%s:%d:%s\n", FILENAME, FNR, line
  }
' < <(tr '\n' '\0' < "$closure") 2>&1)"

file_count="$(wc -l < "$closure" | tr -d '[:space:]')"

if [ -n "$violations" ]; then
  printf '%s\n' "$violations" >&2
  echo "ERROR: 'sorry' found in the release cone (transitive import closure of $ENTRY)." >&2
  echo "The release surface (\`import LerayHopf\`) must be sorry-free. Move the offending" >&2
  echo "module(s) behind an explicit opt-in import (e.g. LerayHopf.Experimental) instead." >&2
  exit 1
fi

echo "OK: release cone is sorry-free ($file_count files transitively imported by $ENTRY)."
