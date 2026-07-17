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
#
# OPTIONAL ARGS (for scripts/test-check-release-cone.sh only — the normal `bash
# scripts/check-release-cone.sh` CI/local invocation takes none and is unaffected):
#   $1 — project root to scan (default: this script's parent directory)
#   $2 — entry module, relative to that root (default: LerayHopf.lean)
# This lets the regression-test harness point the exact same guard logic at an
# isolated fixture tree instead of the real repo.
set -euo pipefail

# The scanned root (below) is parameterizable for the test harness and may not
# be this script's own directory (a fixture tree has no scripts/lib/), so the
# shared keyword vocabulary is sourced from THIS script's real location, not
# from $ROOT.
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=lib/lean-decl-keywords.sh
. "$SCRIPT_DIR/lib/lean-decl-keywords.sh"

ROOT="${1:-$SCRIPT_DIR/..}"
ROOT="$(cd "$ROOT" && pwd)"
cd "$ROOT"

ENTRY="${2:-LerayHopf.lean}"
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

# --- Step 2: ONE comment-aware pass over exactly the closure files, computing the
# same block/line-comment-stripped `code` text per line (as check-no-sorry.sh) and
# testing it against all three checks below. A single pass (rather than one awk
# invocation per check) guarantees the sorry/axiom/namespace checks share
# identical comment-stripping — a prior version ran the axiom and namespace scans
# on raw, un-stripped lines, so a code-like example inside a module docstring
# could trip them despite the file header's claim that comments don't (PR #172
# review, issue #151). NONE of the three checks below have an `ALLOW_*` marker
# escape: a justified sorry/axiom/namespace-content elsewhere in the repo is
# still not permitted to be reachable from the release surface.
#
#   SORRY     — any `sorry` token in code (unchanged from the original #147 guard).
#   AXIOM     — any `axiom`/`constant`/`opaque`/`unsafe` declaration in code.
#   NAMESPACE — any `namespace <dotted-ident>` opener, OR any directly qualified
#     declaration using the vocabulary in lib/lean-decl-keywords.sh
#     (`theorem X.Y.foo ...`, `inductive X.Y.Foo ...`, ...), where a reserved
#     word (Scaffold/Placeholder/Stub/Draft) appears as ANY dot-separated
#     component — not only when it is the sole, unqualified identifier, and not
#     only for a subset of declaration keywords. Two rounds of PR #172 review
#     (issue #151) each caught a real gap here: round 1 — `namespace
#     LerayHopf.Scaffold` (a multi-component qualified form) passed unflagged
#     because only the sole/first component was checked; round 2 —
#     `inductive X.Scaffold.Foo` passed unflagged because the recognized
#     keyword set omitted `inductive`, which is why that set is now centralized
#     in lib/lean-decl-keywords.sh rather than hardcoded per-script. A bare
#     (non-dotted) declaration whose own name equals a reserved word — e.g.
#     `theorem Scaffold` with no `.` — is intentionally left to
#     `check-theorem-names.sh`'s repo-wide, `ALLOW_NAME`-escapable reserved-term
#     guard instead: it is a naming choice, not a declaration living under a
#     namespace.
scan="$(xargs -0 awk -v kw="$LEAN_DECL_KEYWORDS" -v mods="$LEAN_DECL_MODIFIERS" '
  BEGIN {
    declRegex     = "^[[:space:]]*(@\\[[^]]*\\][[:space:]]*)*((" mods ")[[:space:]]+)*(" kw ")[[:space:]]+"
    declIdentRegex = "(" kw ")[[:space:]]+[A-Za-z0-9_.]+"
    declStripRegex = "^(" kw ")[[:space:]]+"
  }
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
      printf "SORRY\t%s:%d:%s\n", FILENAME, FNR, line

    if (code ~ /^[[:space:]]*(@\[[^]]*\][[:space:]]*)*((private|protected|noncomputable|scoped|local)[[:space:]]+)*(axiom|constant|opaque|unsafe)[[:space:]]/)
      printf "AXIOM\t%s:%d:%s\n", FILENAME, FNR, line

    ident = ""
    if (match(code, /^[[:space:]]*namespace[[:space:]]+[A-Za-z0-9_.]+/) > 0) {
      stmt = substr(code, RSTART, RLENGTH)
      sub(/^[[:space:]]*namespace[[:space:]]+/, "", stmt)
      ident = stmt
    } else if (code ~ declRegex) {
      if (match(code, declIdentRegex) > 0) {
        stmt = substr(code, RSTART, RLENGTH)
        sub(declStripRegex, "", stmt)
        if (index(stmt, ".") > 0) ident = stmt
      }
    }
    if (ident != "") {
      m = split(ident, parts, ".")
      for (k = 1; k <= m; k++) {
        p = tolower(parts[k])
        if (p == "scaffold" || p == "placeholder" || p == "stub" || p == "draft") {
          printf "NAMESPACE\t%s:%d:%s\n", FILENAME, FNR, line
          break
        }
      }
    }
  }
' < <(tr '\n' '\0' < "$closure"))"

sorry_violations="$(printf '%s\n' "$scan" | grep '^SORRY' | cut -f2- || true)"
axiom_violations="$(printf '%s\n' "$scan" | grep '^AXIOM' | cut -f2- || true)"
namespace_violations="$(printf '%s\n' "$scan" | grep '^NAMESPACE' | cut -f2- || true)"

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
