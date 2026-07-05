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
#   exists_lerayHopf_torus3_axiomatic — exactly 3 axioms:
#     propext  Classical.choice  Quot.sound  (3 kernel, 0 project)
#     NOTE: torus3_NSForms_exist REMOVED (issue #22) — Nonempty Torus3NSForms is now the theorem
#           torus3_NSForms_exists, routed through the TorusConvectionGap interface and the proved
#           Torus3NSForms_of_gap.
#     NOTE: galerkin_ode_solution REMOVED (issue #24) — discharged by routing the capstone through
#           the axiom-free galerkinSolutionData_torus (proved finite-dim Galerkin ODE over
#           velocitySpan n).
#     NOTE: torusConvectionGap_exists REMOVED (issue #53) — proved sorry-free as
#           torusConvectionGap_holds (determined-form construction, TorusConvectionExtension.lean);
#           re-exported as LerayHopf.torusConvectionGap_exists (theorem, not axiom).
#     NOTE: galerkin_limit_passage REMOVED — replaced by the proved theorems
#           torus_galerkin_limit_passage_of_energyClass + torus_energyClass_of_aubinLions,
#           assembled in TorusGalerkinODECapstone.lean (relocated to avoid import cycle).
#     NOTE: aubin_lions REMOVED (issue #23, T-AL-6 Stage C) — discharged by the proved def
#           torusAubinLionsPackage_of_galSeq (TorusAubinLionsAssembly.lean, mode-wise campaign).
#           Net 𝕋³ project axioms now 0.  THE TORUS IS KERNEL-ONLY.
#
#   exists_lerayHopf_r3_axiomatic — exactly 3 axioms (KERNEL-ONLY):
#     propext  Classical.choice  Quot.sound  (3 kernel)
#     NOTE: galerkin_limit_passage_R3 REMOVED (issue #4 PR-6) — proved as a theorem
#           in LerayHopf/R3/LimitPassage.lean.  R3 now kernel-only like 𝕋³.
#     NOTE: spatial_compactness_R3 REMOVED (issue #2) — now a theorem via the FK chain.
#     NOTE: r3GalerkinScheme_exists REMOVED (issue #21) — now a theorem, SWAPPED for the
#           thinner curlSchwartzDense_holds density axiom.
#     NOTE: galerkin_ode_solution_R3 REMOVED (issue #10) — discharged by routing the capstone
#           through the axiom-free galerkinSolutionData_unconditional over schemeOfBasis B.
#     NOTE: aubin_lions_R3 REMOVED (issue #15) — its spatial half PROVED (steklovAvg_spatial_extraction
#           chain); its time content SWAPPED for the single UNCONDITIONAL galerkinSpaceTimeExtraction_R3.
#     NOTE: galerkinSpaceTimeExtraction_R3 REMOVED (issue #44) — converted to a THEOREM; the
#           Aubin–Lions-in-time diagonalization is PROVED sorry-free (ArzelaAscoliTime.lean), and the
#           irreducible content is isolated into TWO strictly-thinner SOUND scheme-independent axioms:
#           galerkin_spacetime_precompact_R3 (refine-capable LOCAL Aubin–Lions–Simon spacetime
#           precompactness) and galerkin_weakLimit_R3 (a.e.-t per-ball limits ⇒ measurable weak limit
#           in L2Sigma_R3). The over-strong strong-L² time-modulus route (codex P1) is NOT used.
#           Net R3 project axioms 5.
#     NOTE: curlSchwartzDense_holds REMOVED (issue #3 / #21) — the Helmholtz/Weyl curl-density
#           is now PROVED sorry-free in CurlDensity.lean (curlSchwartzDense_provedRoute, Fourier
#           route). CurlDensityCapstone.lean rewires curlSchwartzDense_holds / nonempty_schwartzGalerkinBasis
#           / r3GalerkinScheme_exists to the proved theorem. Net R3 project axioms now 4.
#     NOTE: galerkin_weakLimit_R3 REMOVED (issue #47 PR-A) — converted to a THEOREM via the
#           strong ball-exhaustion + Mazur route (Cauchy diagonal +
#           exists_stronglyMeasurable_limit_of_tendsto_ae + WL-5). Does NOT use
#           L2VF_R3_weakSeqCompact_closedBall. Net R3 project axioms: 3 (4→3).
#     NOTE: L2VF_R3_weakSeqCompact_closedBall DELETED (issue #47 PR-A cleanup) — introduced as
#           a scaffold but never called by galerkin_weakLimit_R3's actual proof body. Removed as
#           dead code. Net R3 project axioms: 3.
#     NOTE: r3_NSForms_exist REORGANIZED (issue #48) — the named axiom is replaced by
#           r3ConvectionGapOp_exists (operator core: b/b_extends/b_multilinear/b_antisymm_gap/
#           b_cont_fixedTest) + proved theorem r3_NSForms_exists (via R3NSForms_of_gap).
#           Density (schwartz_dense) NOT assumed — proved via curlSchwartzDense_holds.
#           Note: b_cont_fixedTest ≡ b_bound (bounded/continuous-bilinear equivalence) so the
#           fixed-test bound was still assumed, not proved, at this stage.
#     NOTE: r3ConvectionGapOp_exists REMOVED (issue #56) — proved sorry-free as
#           r3ConvectionGapOp_holds by the determined-form BLT construction. Net R3 project axioms
#           now 2.
#     NOTE: galerkin_spacetime_precompact_R3 REMOVED (issue #46 PR-4, 2026-07-04) — converted to a
#           THEOREM in ArzelaAscoliTime.lean by delegation to
#           galerkin_spacetime_precompact_of_goodSampling (File E, SpacetimePrecompact.lean),
#           which assembles the LOCAL Aubin–Lions–Simon precompactness sorry-free from the
#           step-curve total-boundedness engine (n-uniform integrated sampling modulus + Rellich
#           ball-compactness). Net R3 project axioms now 1.
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
#   0 project axioms + 3 kernel = 3 total  (KERNEL-ONLY — issue #23 T-AL-6 finish line)
#   (galerkin_ode_solution removed, issue #24)
#   (torusConvectionGap_exists REMOVED, issue #53 — proved as torusConvectionGap_holds)
#   (galerkin_limit_passage REMOVED — proved via torus_galerkin_limit_passage_of_energyClass
#    + torus_energyClass_of_aubinLions, assembled in TorusGalerkinODECapstone.lean)
#   (aubin_lions REMOVED, issue #23 — proved as torusAubinLionsPackage_of_galSeq)
# ---------------------------------------------------------------------------
assert_axioms "exists_lerayHopf_torus3_axiomatic" \
  "propext Classical.choice Quot.sound"

# NOTE: r3ConvectionGapOp_exists REMOVED (issue #56) — proved sorry-free as r3ConvectionGapOp_holds
#   (determined-form convection operator, ConvectionExtension.lean C11). Net R3 project axioms now 2.
# ---------------------------------------------------------------------------
# Pin 2: exists_lerayHopf_r3_axiomatic
#   1 project axiom + 3 kernel = 4 total
#   (spatial_compactness_R3 removed — issue #2 — now a theorem via the FK chain)
#   (r3GalerkinScheme_exists removed — issue #21 — now a theorem, SWAPPED for the
#    thinner curlSchwartzDense_holds density axiom)
#   (galerkin_ode_solution_R3 removed — issue #10 — discharged via the axiom-free
#    galerkinSolutionData_unconditional over schemeOfBasis B)
#   (aubin_lions_R3 REMOVED — issue #15 — its spatial half PROVED via the
#    steklovAvg_spatial_extraction chain; its time content SWAPPED 1-for-1 for the single
#    UNCONDITIONAL axiom galerkinSpaceTimeExtraction_R3; net R3 axioms 4)
#   (galerkinSpaceTimeExtraction_R3 REMOVED — issue #44 — converted to a THEOREM: the
#    Aubin–Lions-in-time diagonalization (a.e.-t extraction via tendstoInMeasure +
#    Cantor diagonal over balls + measurability) is now PROVED sorry-free in
#    LerayHopf/R3/ArzelaAscoliTime.lean.  The irreducible content is isolated into TWO
#    strictly-thinner, SOUND, scheme-independent residual axioms:
#      - galerkin_spacetime_precompact_R3 (refine-capable LOCAL Aubin–Lions–Simon
#        spacetime precompactness in L²(0,T;L²(B_k)) — no tightness, no global-L², no
#        strong-norm time-equicontinuity; replaces the over-strong equicontinuity route
#        flagged by codex P1), and
#      - galerkin_weakLimit_R3 (a.e.-t per-ball limits ⇒ measurable weak limit in
#        L2Sigma_R3; Banach–Alaoglu + div-free weak-closedness, not in mathlib).
#    Net R3 project axioms 5; the over-strong strong-L² time-modulus axiom is NOT used.)
#   (curlSchwartzDense_holds REMOVED — issue #3 / #21 — proved sorry-free via the Fourier
#    route in LerayHopf/R3/CurlDensity.lean (curlSchwartzDense_provedRoute); wired in
#    CurlDensityCapstone.lean as a theorem. Net R3 project axioms now 4.)
#   (galerkin_weakLimit_R3 REMOVED — issue #47 PR-A — proved as a theorem via the strong
#    ball-exhaustion + Mazur route; L2VF_R3_weakSeqCompact_closedBall deleted as dead code.
#    Net R3 project axioms now 3.)
#   (galerkin_spacetime_precompact_R3 REMOVED — issue #46 PR-4 — converted to a theorem in
#    ArzelaAscoliTime.lean by delegation to galerkin_spacetime_precompact_of_goodSampling
#    (File E, SpacetimePrecompact.lean), assembled sorry-free from the step-curve
#    total-boundedness engine. Net R3 project axioms now 1.)
# ---------------------------------------------------------------------------
assert_axioms "exists_lerayHopf_r3_axiomatic" \
  "propext Classical.choice Quot.sound"

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

echo "AXIOM LIVE PIN OK — all 4 declarations match their pinned axiom sets (R3: 0 project axioms — KERNEL-ONLY, 𝕋³: 0 project axioms — KERNEL-ONLY)."
