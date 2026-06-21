#!/usr/bin/env bash
# Live axiom pin: runs `#print axioms` via `lake env lean` and ASSERTS exact
# expected axiom sets for the two capstones and two Core representatives.
#
# This is the real backstop that `check-axioms.sh` cannot provide: it catches
# transitive leaks (e.g. a Core import developing a transitive dependency on an
# axiomatic module) that static import-list scanning misses.
#
# Expected axiom sets (kernel axioms shared by all):
#
#   exists_lerayHopf_torus3_axiomatic — exactly 7 axioms:
#     propext  Classical.choice  Quot.sound  (3 kernel)
#     LerayHopf.aubin_lions  LerayHopf.galerkin_limit_passage
#     LerayHopf.galerkin_ode_solution  LerayHopf.torus3_NSForms_exist  (4 project)
#
#   exists_lerayHopf_r3_axiomatic — exactly 8 axioms:
#     propext  Classical.choice  Quot.sound  (3 kernel)
#     LerayHopf.aubin_lions_R3  LerayHopf.galerkin_limit_passage_R3
#     LerayHopf.galerkin_ode_solution_R3  LerayHopf.curlSchwartzDense_holds
#     LerayHopf.r3_NSForms_exist  (5 project)
#     NOTE: spatial_compactness_R3 REMOVED (issue #2) — now a theorem via the FK chain.
#     NOTE: r3GalerkinScheme_exists REMOVED (issue #21) — now a theorem, SWAPPED for the
#           thinner curlSchwartzDense_holds density axiom; net R3 project axioms still 5.
#
#   lower_bound_from_inverse_square_lifespan (Core torus) — exactly 3 kernel axioms,
#     no project axioms, no sorryAx.
#
#   localCompactness_R3_of_ballCompact (Core R3) — exactly 3 kernel axioms,
#     no project axioms, no sorryAx.
#
# FAIL-CLOSED: any unexpected axiom OR any missing expected axiom → nonzero exit.

set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

export PATH="$HOME/.elan/bin:$PATH"

if ! command -v lake >/dev/null 2>&1; then
  echo "ERROR: 'lake' not found." >&2
  exit 1
fi

echo "==> Running live #print axioms pin..."

# Run print_axioms.lean and capture output.
# flock is used if available to avoid OOM from concurrent builds.
if command -v flock >/dev/null 2>&1; then
  OUTPUT="$(flock /tmp/lean-build.lock lake env lean "scripts/print_axioms.lean" 2>&1)"
else
  OUTPUT="$(lake env lean "scripts/print_axioms.lean" 2>&1)"
fi

echo "$OUTPUT"

FAIL=0

# ---------------------------------------------------------------------------
# Assertion helper: check that a given declaration's axiom line contains
# exactly the expected tokens and nothing else (modulo whitespace/newlines).
#
# Lean's `#print axioms` output for one decl is:
#   'Name' depends on axioms: [a1, a2, ...]   (possibly line-wrapped)
# We extract everything from the opening '[' to the closing ']'.
# ---------------------------------------------------------------------------
assert_axioms() {
  local decl="$1"   # bare declaration name (no quotes, no namespace)
  local expected="$2"  # space-separated list of expected axiom names (sorted)

  # Extract the axiom list for this declaration from the full output.
  # The block starts with "'LerayHopf.<decl>' depends on axioms: [" and ends at ']'.
  local block
  block="$(printf '%s\n' "$OUTPUT" \
    | awk "/depends on axioms: \[/{found=1; line=\"\"} found{line=line\$0\" \"} /\]/{if(found) print line; found=0}" \
    | grep -F "'LerayHopf.${decl}'" || true)"

  if [ -z "$block" ]; then
    echo "ERROR: no '#print axioms' output found for 'LerayHopf.${decl}'" >&2
    echo "  (Did the lean script fail to compile?)" >&2
    FAIL=1
    return
  fi

  # Extract the bracketed axiom list, strip punctuation, sort.
  local actual_sorted
  actual_sorted="$(printf '%s\n' "$block" \
    | grep -oE '\[.*\]' \
    | tr ',[]\n' '   \n' \
    | tr -s ' ' '\n' \
    | sed '/^$/d' \
    | sort)"

  local expected_sorted
  expected_sorted="$(printf '%s\n' $expected | sort)"

  if [ "$actual_sorted" != "$expected_sorted" ]; then
    echo "ERROR: axiom set mismatch for 'LerayHopf.${decl}'" >&2
    echo "  Expected: $(printf '%s\n' $expected | sort | tr '\n' ' ')" >&2
    echo "  Actual:   $(printf '%s\n' "$actual_sorted" | tr '\n' ' ')" >&2
    FAIL=1
  else
    echo "OK: LerayHopf.${decl} — axiom set matches pin."
  fi
}

# Also check that a declaration has NO sorryAx and NO project axioms.
assert_core_clean() {
  local decl="$1"

  local block
  block="$(printf '%s\n' "$OUTPUT" \
    | awk "/depends on axioms: \[/{found=1; line=\"\"} found{line=line\$0\" \"} /\]/{if(found) print line; found=0}" \
    | grep -F "'LerayHopf.${decl}'" || true)"

  if [ -z "$block" ]; then
    echo "ERROR: no '#print axioms' output found for 'LerayHopf.${decl}'" >&2
    FAIL=1
    return
  fi

  # Extract only the axiom list (between '[' and ']') to avoid matching
  # the declaration name itself in the project-axiom check.
  local axiom_list
  axiom_list="$(printf '%s\n' "$block" | grep -oE '\[.*\]')"

  if printf '%s\n' "$axiom_list" | grep -q "sorryAx"; then
    echo "ERROR: LerayHopf.${decl} has sorryAx — Core must be sorry-free." >&2
    echo "  Axiom list: $axiom_list" >&2
    FAIL=1
  elif printf '%s\n' "$axiom_list" | grep -q "LerayHopf\."; then
    echo "ERROR: LerayHopf.${decl} has project axioms — Core must be project-axiom-free." >&2
    echo "  Axiom list: $axiom_list" >&2
    FAIL=1
  else
    echo "OK: LerayHopf.${decl} — Core-clean (no project axioms, no sorryAx)."
  fi
}

# ---------------------------------------------------------------------------
# Pin 1: exists_lerayHopf_torus3_axiomatic
#   4 project axioms + 3 kernel = 7 total
# ---------------------------------------------------------------------------
assert_axioms "exists_lerayHopf_torus3_axiomatic" \
  "propext Classical.choice Quot.sound
   LerayHopf.aubin_lions LerayHopf.galerkin_limit_passage
   LerayHopf.galerkin_ode_solution LerayHopf.torus3_NSForms_exist"

# ---------------------------------------------------------------------------
# Pin 2: exists_lerayHopf_r3_axiomatic
#   5 project axioms + 3 kernel = 8 total
#   (spatial_compactness_R3 removed — issue #2 — now a theorem via the FK chain)
#   (r3GalerkinScheme_exists removed — issue #21 — now a theorem, SWAPPED for the
#    thinner curlSchwartzDense_holds density axiom; net R3 project axioms still 5)
# ---------------------------------------------------------------------------
assert_axioms "exists_lerayHopf_r3_axiomatic" \
  "propext Classical.choice Quot.sound
   LerayHopf.aubin_lions_R3 LerayHopf.galerkin_limit_passage_R3
   LerayHopf.galerkin_ode_solution_R3 LerayHopf.curlSchwartzDense_holds
   LerayHopf.r3_NSForms_exist"

# ---------------------------------------------------------------------------
# Pin 3: Core torus representative — no project axioms, no sorryAx
# ---------------------------------------------------------------------------
assert_core_clean "lower_bound_from_inverse_square_lifespan"

# ---------------------------------------------------------------------------
# Pin 4: Core R3 representative — no project axioms, no sorryAx
# ---------------------------------------------------------------------------
assert_core_clean "localCompactness_R3_of_ballCompact"

# ---------------------------------------------------------------------------
if [ "$FAIL" -ne 0 ]; then
  echo "AXIOM LIVE PIN FAILED — see errors above." >&2
  exit 1
fi

echo "AXIOM LIVE PIN OK — all 4 declarations match their pinned axiom sets."
