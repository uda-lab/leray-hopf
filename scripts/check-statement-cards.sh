#!/usr/bin/env bash
# Statement-card regression guard (issue #158 recurrence-prevention process fix).
#
# Two invariants introduced after the `w1pTime_continuous_in_H` false-statement
# postmortem (docs/postmortems/2026-07-w1ptime-false-statement.md,
# docs/statement-gates.md):
#
#   (a) `LerayHopf.Bochner.w1pTime_continuous_in_H` must stay pinned at the one
#       case with an actual proof plan, `p = q = 2`. A generic `{p q}`-parametric
#       reintroduction is exactly the false statement issue #158 found (an
#       explicit weighted-`ℓ²` counterexample at `p = q = 1`) — this is a hard
#       regression guard, not a style preference.
#
#   (b) every declaration carrying a same-line `-- ALLOW_SORRY:` marker (i.e.
#       every scaffold `sorry` site `check-no-sorry.sh` allows) has a
#       corresponding statement card at `docs/statement-cards/<name>.md`. A
#       sorry-marked declaration with no card is exactly the "large-batch review
#       dilution" antipattern (issue #158 antipattern #9): statement review that
#       never produces a durable, per-declaration record.
#
# Comment-stripping for (b) mirrors check-no-sorry.sh's block/line-comment-aware
# scanner (nested `/- -/`, line `--`) so that docstring PROSE mentioning `sorry`
# and `ALLOW_SORRY:` (e.g. LerayHopf/Experimental.lean's inventory docstring)
# is not mistaken for a real code sorry.
#
# FAIL-CLOSED: set -euo pipefail. The two `grep_or_empty` calls below are the only
# place a command's nonzero exit is tolerated, and only for grep's own "no lines
# matched" status (1) — any other exit code (a real grep/awk failure) still
# propagates and aborts the script, so a broken scan can never silently report
# success.
set -euo pipefail

# grep that treats "no match" (exit 1) as an empty, successful result, but still
# aborts (via `set -e`) on any other nonzero exit (a real grep error).
grep_or_empty() {
  grep "$@" || { local rc=$?; [ "$rc" -eq 1 ]; }
}

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

FAIL=0

# ---------------------------------------------------------------------------
# Guard (a): w1pTime_continuous_in_H stays pinned at p = q = 2.
# ---------------------------------------------------------------------------
TARGET="LerayHopf/Bochner/TimeSobolevExperimental.lean"
if [ ! -r "$TARGET" ]; then
  echo "ERROR: '$TARGET' is missing — cannot check the w1pTime_continuous_in_H pin." >&2
  exit 1
fi

# Isolate the declaration's own signature block: from its `theorem` line up to
# the line that opens the proof body (`:=` or `:= by`). A generic reintroduction
# would add `{p q : ...}` binders and/or an `hpq` hypothesis to this signature.
decl_block="$(awk '
  /^theorem w1pTime_continuous_in_H/ { grab = 1 }
  grab { print; if ($0 ~ /:= *by *$/ || $0 ~ /:= *$/) exit }
' "$TARGET")"

if [ -z "$decl_block" ]; then
  echo "ERROR: declaration 'w1pTime_continuous_in_H' not found in '$TARGET'." >&2
  echo "  (Renamed, moved, or discharged without updating this guard? Update the guard" >&2
  echo "  together with docs/statement-cards/w1pTime_continuous_in_H.md if so.)" >&2
  FAIL=1
elif printf '%s\n' "$decl_block" | grep -Eq '\{p +q\b|hpq *:'; then
  echo "ERROR: 'w1pTime_continuous_in_H' appears to have reverted to a generic" >&2
  echo "  {p q}-parametric signature. Issue #158 found that FALSE at this generality" >&2
  echo "  (explicit weighted-l^2 counterexample at p = q = 1)." >&2
  echo "  See docs/postmortems/2026-07-w1ptime-false-statement.md before widening this." >&2
  FAIL=1
elif ! printf '%s\n' "$decl_block" | grep -q 'W1pTime GT 2 2 T'; then
  echo "ERROR: 'w1pTime_continuous_in_H' no longer visibly pins its W1pTime hypothesis to" >&2
  echo "  exponents 2 2. If this is an intentional, reviewed generalization with a proof" >&2
  echo "  plan, update this guard AND the statement card together" >&2
  echo "  (docs/statement-cards/w1pTime_continuous_in_H.md) per docs/statement-gates.md." >&2
  FAIL=1
else
  echo "OK: w1pTime_continuous_in_H is pinned at p = q = 2 (no generic {p q} reintroduced)."
fi

# ---------------------------------------------------------------------------
# Guard (b): every ALLOW_SORRY-marked declaration has a statement card.
# ---------------------------------------------------------------------------
list="$(mktemp)"
trap 'rm -f "$list"' EXIT
find . \( -name '.git' -o -name '.lake' -o -path './.claude/worktrees' \) -prune \
     -o -type f -name '*.lean' -print0 > "$list"

if [ ! -s "$list" ]; then
  echo "OK: no Lean sources to scan for statement cards."
else
  # Comment-aware scan (same block/line-comment stripping as check-no-sorry.sh):
  # tracks the most recently seen declaration name (`theorem`/`lemma`/`def`/
  # `abbrev`/`instance`/`structure`/`class` — the same keyword set
  # check-theorem-names.sh treats as declaration-introducing) in each file's
  # CODE portion, and reports that name whenever a later CODE-portion `sorry`
  # is found on a line also carrying an `ALLOW_SORRY:` marker.
  decls="$(xargs -0 awk '
    FNR == 1 { depth = 0; decl = "" }
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

      if (code ~ /^[[:space:]]*(private[[:space:]]+|protected[[:space:]]+|noncomputable[[:space:]]+|scoped[[:space:]]+|local[[:space:]]+|nonrec[[:space:]]+)*(theorem|lemma|def|abbrev|instance|structure|class)[[:space:]]+/) {
        rest = code
        sub(/^[[:space:]]*(private[[:space:]]+|protected[[:space:]]+|noncomputable[[:space:]]+|scoped[[:space:]]+|local[[:space:]]+|nonrec[[:space:]]+)*(theorem|lemma|def|abbrev|instance|structure|class)[[:space:]]+/, "", rest)
        match(rest, /^[^ \t(){}:]+/)
        # An anonymous declaration (e.g. instance : Foo := ..., where rest starts
        # with a colon) matches zero-length here. Reset decl to "" rather than
        # leaving the PRECEDING declaration name in place -- otherwise a later
        # sorry -- ALLOW_SORRY on this anonymous declaration would be silently
        # misattributed to whatever card the prior named declaration already has.
        if (RLENGTH > 0) decl = substr(rest, RSTART, RLENGTH)
        else decl = ""
      }

      if (code ~ /(^|[^A-Za-z0-9_])sorry([^A-Za-z0-9_]|$)/ && line ~ /ALLOW_SORRY:/) {
        if (decl == "") printf "%s:%d:NO-DECL-FOUND\n", FILENAME, FNR
        else printf "%s\n", decl
      }
    }
  ' < "$list" | sort -u)"

  no_decl="$(printf '%s\n' "$decls" | grep_or_empty ':NO-DECL-FOUND$')"
  if [ -n "$no_decl" ]; then
    printf '%s\n' "$no_decl" >&2
    echo "ERROR: found a code-level 'sorry -- ALLOW_SORRY:' with no attributable" >&2
    echo "  named declaration on the same file (either no preceding declaration at" >&2
    echo "  all, or it is an anonymous instance/def with no name). Give the" >&2
    echo "  declaration a name and add a statement card, or otherwise make it" >&2
    echo "  attributable before merging." >&2
    FAIL=1
  fi

  names="$(printf '%s\n' "$decls" | grep_or_empty -v ':NO-DECL-FOUND$' | sed '/^$/d')"
  missing=0
  if [ -n "$names" ]; then
    while IFS= read -r name; do
      card="docs/statement-cards/${name}.md"
      if [ ! -r "$card" ]; then
        echo "ERROR: declaration '${name}' carries an ALLOW_SORRY sorry but has no" >&2
        echo "  statement card at '${card}'. Add one (see docs/statement-gates.md for the" >&2
        echo "  required fields) before merging." >&2
        missing=1
      fi
    done <<< "$names"
  fi

  if [ "$missing" -ne 0 ]; then
    FAIL=1
  else
    echo "OK: every ALLOW_SORRY-marked declaration has a statement card ($(printf '%s\n' "$names" | sed '/^$/d' | wc -l | tr -d ' ') found)."
  fi
fi

if [ "$FAIL" -ne 0 ]; then
  echo "STATEMENT-CARD GUARD FAILED — see errors above." >&2
  exit 1
fi

echo "OK: statement-card guard passed."
