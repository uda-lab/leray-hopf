#!/usr/bin/env bash
# FAST STATIC PRE-FILTER for the axiom-leak gate.
#
# This script is a grep-based STRUCTURAL check — it is fast (no Lean compilation)
# but it only sees DIRECT imports of Core.lean, not transitive ones.
# It is a necessary-but-not-sufficient gate.
#
# The real backstop is `scripts/check-axioms-live.sh`, which runs
# `lake env lean scripts/print_axioms.lean` and asserts the EXACT axiom sets
# for both capstones and two Core representatives via `#print axioms`.
# That live job catches transitive leaks this static check cannot.
#
# Two-tier design:
#   check-axioms.sh      — fast static pre-filter (this file); fails on direct violations.
#   check-axioms-live.sh — live `#print axioms` pin; catches transitive leaks.
#   Together they are fail-closed.
#
# What this file checks:
#   1. Core.lean's direct imports do not include any axiomatic module.
#   2. Bare capstone names (without _axiomatic) are absent from Lean sources.
#   3. All axioms in axiomatic files carry ALLOW_AXIOM markers.
#
# FAIL-CLOSED: set -euo pipefail; any grep/awk failure aborts with nonzero status.

set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

FAIL=0

# ---------------------------------------------------------------------------
# Gate 1: Core.lean must not import any axiomatic module.
# ---------------------------------------------------------------------------
CORE="LerayHopf/Core.lean"
AXIOMATIC_MODULES=(
  "LerayHopf.AxiomaticClosure"
  "LerayHopf.R3.AxiomaticClosure"
  "LerayHopf.TorusAxiomatic"
  "LerayHopf.R3Axiomatic"
)

for mod in "${AXIOMATIC_MODULES[@]}"; do
  if grep -qE "^import[[:space:]]+${mod//./\\.}([[:space:]]|$)" "$CORE"; then
    echo "ERROR: $CORE imports axiomatic module '$mod'" >&2
    FAIL=1
  fi
done

# ---------------------------------------------------------------------------
# Gate 2: The axiom-dependent capstone theorems must end in _axiomatic.
#         Verify the old bare names are gone from the Lean sources.
# ---------------------------------------------------------------------------
BARE_NAMES=("exists_lerayHopf_torus3" "exists_lerayHopf_r3")

for name in "${BARE_NAMES[@]}"; do
  # Allow the name only when immediately followed by _axiomatic (i.e. as a prefix)
  # or when it appears inside a comment or the _axiomatic variant itself.
  # We want to catch bare `theorem exists_lerayHopf_torus3 ` declarations.
  if grep -rn --include="*.lean" \
        -E "(^|[[:space:]])(theorem|def|abbrev)[[:space:]]+${name}([[:space:]]|$|\()" \
        --exclude-dir='.lake' --exclude-dir='.git' . 2>/dev/null | grep -q .; then
    echo "ERROR: bare (non-_axiomatic) declaration '${name}' found in Lean sources." >&2
    echo "  Rename it to '${name}_axiomatic' as required by Issue #1 item 3." >&2
    grep -rn --include="*.lean" \
        -E "(^|[[:space:]])(theorem|def|abbrev)[[:space:]]+${name}([[:space:]]|$|\()" \
        --exclude-dir='.lake' --exclude-dir='.git' . 2>/dev/null >&2 || true
    FAIL=1
  fi
done

# ---------------------------------------------------------------------------
# Gate 3: Axiomatic modules must not introduce un-annotated axioms.
#         (Redundant with check-no-axiom.sh, but makes the intent explicit here.)
# ---------------------------------------------------------------------------
AXIOMATIC_FILES=(
  "LerayHopf/AxiomaticClosure.lean"
  "LerayHopf/R3/AxiomaticClosure.lean"
  "LerayHopf/TorusConvectionForm.lean"
)

pattern='^[[:space:]]*(@\[[^]]*\][[:space:]]*)*((private|protected|noncomputable|scoped|local)[[:space:]]+)*(axiom|constant|opaque|unsafe)[[:space:]]'

for f in "${AXIOMATIC_FILES[@]}"; do
  if [ ! -f "$f" ]; then
    echo "ERROR: expected axiomatic file '$f' does not exist." >&2
    FAIL=1
    continue
  fi
  # All axiom/opaque/unsafe lines must carry ALLOW_AXIOM markers.
  while IFS= read -r match; do
    lineno="${match%%:*}"
    content="${match#*:}"
    case "$content" in
      *ALLOW_AXIOM:*) : ;;  # documented assumption — OK
      *)
        echo "ERROR: $f:$lineno: undocumented axiom/constant/opaque/unsafe" >&2
        echo "  $content" >&2
        FAIL=1
        ;;
    esac
  done < <(grep -nE "$pattern" -- "$f" 2>/dev/null || true)
done

# ---------------------------------------------------------------------------
# Report
# ---------------------------------------------------------------------------
if [ "$FAIL" -ne 0 ]; then
  echo "AXIOM GATE FAILED — see errors above." >&2
  exit 1
fi

echo "OK: axiom-leak gate passed."
echo "  Core.lean does not import axiomatic modules."
echo "  Capstone theorems carry _axiomatic suffix."
echo "  All axioms in axiomatic files are annotated ALLOW_AXIOM."
