#!/usr/bin/env bash
# Strict release-cone guard (issue #147; extended by issue #151): the transitive
# import closure of the root `LerayHopf.lean` module — the release surface a plain
# `import LerayHopf` pulls in — must contain:
#   1. ZERO `sorry` tokens in code, marked or unmarked (issue #147);
#   2. ZERO `axiom`/`constant`/`opaque`/`unsafe` declarations, marked or unmarked
#      (issue #151 — closes the gap where `check-no-axiom.sh` accepts any
#      `-- ALLOW_AXIOM:`-marked declaration anywhere in the repo, including inside
#      the release cone);
#   3. ZERO declarations under a reserved placeholder namespace (`Scaffold`,
#      `Placeholder`, `Stub`, `Draft`) (issue #151 — a fixed-name-term guard alone
#      cannot anticipate every vacuous-declaration name; the historical incident
#      this closes is `Scaffold.exists_lerayHopf_torus3_statement`, a bare-Prop
#      placeholder that WAS reachable from `import LerayHopf` before issue #144
#      deleted it outright. See `check-theorem-names.sh` for the complementary,
#      repo-wide, ALLOW_NAME-escapable reserved-term guard.)
#
# This is intentionally STRICTER than `check-no-sorry.sh` / `check-no-axiom.sh`: a
# same-line `-- ALLOW_SORRY:` / `-- ALLOW_AXIOM:` marker justifies the declaration
# existing in the repo at all, but a justified sorry/axiom still must not be
# reachable from the public root import — and unlike the reserved-term guard, the
# namespace check below has NO marker escape, because an incomplete-work namespace
# has no legitimate reason to be part of the release surface. Incomplete work
# belongs behind an explicit opt-in import (`LerayHopf.Experimental`), never in the
# release cone.
#
# WITHOUT lake: the closure is computed by statically parsing `import LerayHopf.*`
# lines from source text (no `lake env`, no compilation). Non-project imports
# (`Mathlib.*`, etc.) are not project sources and are skipped — they cannot carry
# a project `sorry`/`axiom`/namespace.
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
    # the whole script via `set -e`. Explicit status handling (matching the
    # house style in check-axioms.sh): 0 = matches found, 1 = no matches (fine,
    # not every file imports project modules), >1 = grep itself failed (a
    # scanner error, not "no results") and must abort, not be silently treated
    # as an empty closure contribution.
    status=0
    matches="$(grep -E '^[[:space:]]*import[[:space:]]+LerayHopf\.' "$file")" || status=$?
    if [ "$status" -gt 1 ]; then
      echo "ERROR: import scan failed for '$file' (grep exit $status)." >&2
      exit 1
    fi
    if [ "$status" -eq 0 ]; then
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
sorry_violations="$(xargs -0 awk '
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

# --- Step 3: axiom/constant/opaque/unsafe scan over exactly the closure files
# (issue #151). Same declaration-leading-keyword anchor as check-no-axiom.sh, but
# WITHOUT its `!/ALLOW_AXIOM:/` exemption: any such declaration in the release
# cone is a violation, justified or not. Anchoring to the declaration-leading
# keyword (not a bare token scan like the sorry check above) means occurrences in
# comments, identifiers, or strings do not trip the check — matching
# check-no-axiom.sh's own matching discipline. ---
axiom_violations="$(xargs -0 awk '
  /^[[:space:]]*(@\[[^]]*\][[:space:]]*)*((private|protected|noncomputable|scoped|local)[[:space:]]+)*(axiom|constant|opaque|unsafe)[[:space:]]/ {
    printf "%s:%d:%s\n", FILENAME, FNR, $0
  }
' < <(tr '\n' '\0' < "$closure"))"

# --- Step 4: reserved placeholder-namespace scan over exactly the closure files
# (issue #151). `namespace Scaffold`/`Placeholder`/`Stub`/`Draft` (case-insensitive)
# has no legitimate reason to be reachable from the release surface — this has NO
# marker escape (see file header). Matches `check-theorem-names.sh`'s declaration
# scan discipline (anchored, so prose mentions in docstrings/comments do not trip
# it). ---
namespace_violations="$(xargs -0 awk '
  tolower($0) ~ /^[[:space:]]*namespace[[:space:]]+(scaffold|placeholder|stub|draft)([[:space:]]|$)/ {
    printf "%s:%d:%s\n", FILENAME, FNR, $0
  }
' < <(tr '\n' '\0' < "$closure"))"

file_count="$(wc -l < "$closure" | tr -d '[:space:]')"
FAIL=0

if [ -n "$sorry_violations" ]; then
  printf '%s\n' "$sorry_violations" >&2
  echo "ERROR: 'sorry' found in the release cone (transitive import closure of $ENTRY)." >&2
  echo "The release surface (\`import LerayHopf\`) must be sorry-free. Move the offending" >&2
  echo "module(s) behind an explicit opt-in import (e.g. LerayHopf.Experimental) instead." >&2
  FAIL=1
fi

if [ -n "$axiom_violations" ]; then
  printf '%s\n' "$axiom_violations" >&2
  echo "ERROR: axiom/constant/opaque/unsafe found in the release cone (transitive import" >&2
  echo "closure of $ENTRY). The release surface must be project-axiom-free, even when the" >&2
  echo "declaration carries an -- ALLOW_AXIOM: marker. Move the offending module(s) behind" >&2
  echo "an explicit opt-in import (e.g. LerayHopf.Experimental) instead." >&2
  FAIL=1
fi

if [ -n "$namespace_violations" ]; then
  printf '%s\n' "$namespace_violations" >&2
  echo "ERROR: reserved placeholder namespace (Scaffold/Placeholder/Stub/Draft) found in" >&2
  echo "the release cone (transitive import closure of $ENTRY). Incomplete-work namespaces" >&2
  echo "must not be reachable from the release surface — rename the namespace or move the" >&2
  echo "module behind an explicit opt-in import (e.g. LerayHopf.Experimental) instead." >&2
  FAIL=1
fi

if [ "$FAIL" -ne 0 ]; then
  exit 1
fi

echo "OK: release cone is sorry-free, axiom-free, and free of reserved placeholder"
echo "namespaces ($file_count files transitively imported by $ENTRY)."
