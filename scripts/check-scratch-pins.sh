#!/usr/bin/env bash
# Fail-closed scratch evidence gate (issue #195; §10.5 of
# docs/scratch/global-diagonal-campaign.md, pass-3 G-2, hardened at pass-4 H-1,
# retargeted for the POST-P1 tree by #200): forced-fresh compilation + EXACT
# 14-declaration pin-set check.  Non-zero exit on build failure, stale/replayed
# target, missing or malformed pin, any axiom token outside the kernel trio, or any
# pin output beyond the enumerated set.
#
# The four remaining scratch targets are deliberately OUTSIDE the release cone (not
# imported by LerayHopf.lean), so agent-preflight.sh's default build does not rebuild
# them.  This checker rebuilds them from scratch and asserts their axiom hygiene.  The
# former GlobalContract (12 pins) was promoted into the release cone by #200 and is now
# covered there (plus the interim live pins in check-axioms-live.sh); it is no longer a
# scratch target here.
#
# WIRING: invoked UNWRAPPED from agent-preflight.sh and the lean.yml full-build job.
# It self-locks via `exec 9>/tmp/lean-build.lock; flock 9`; wrapping it in an outer
# flock on the same lock self-deadlocks the container-wide build lock.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

export PATH="$HOME/.elan/bin:$PATH"
log="$(mktemp)"
trap 'rm -f "$log"' EXIT

targets=(DiagonalExtraction KappaReindex GlobalContractTorus P2ExitContract)

# Take the container-wide build lock BEFORE the artifact deletion below and hold it
# through the build (PR #205 review: deleting outside the lock races a concurrent
# lock-holding lake process — it could remove artifacts that build just produced or
# is about to consume).  FD 9 keeps the same /tmp/lean-build.lock every other lean
# build in this container serializes on; it is released when the script exits.
exec 9>/tmp/lean-build.lock
flock 9

# Freshness: delete the four modules' build artifacts (.olean/.ilean/.hash/.trace).
# Lake cannot serve a stale artifact or replay a cached log for a module whose
# artifacts are missing — it must genuinely re-elaborate it, and only genuine
# re-elaboration prints "Built <module>" (a cache hit prints "Replayed <module>")
# and re-runs the #print axioms commands whose output is parsed below.  Upstream
# dependencies stay cached, so the cost is exactly the four scratch modules.
for t in "${targets[@]}"; do
  rm -f ".lake/build/lib/lean/LerayHopf/Scratch/$t".*
done

lake build \
  LerayHopf.Scratch.DiagonalExtraction \
  LerayHopf.Scratch.KappaReindex \
  LerayHopf.Scratch.GlobalContractTorus \
  LerayHopf.Scratch.P2ExitContract >"$log" 2>&1 \
  || { echo "BUILD FAILED"; tail -40 "$log"; exit 1; }
grep -q "Build completed successfully" "$log"

# Assertion: every target was BUILT in this run.  Cannot pass stale: the artifact
# deletion above forces a rebuild, and a replayed/skipped target would print
# "Replayed"/nothing instead of "Built" and fail here.
for t in "${targets[@]}"; do
  grep -q "Built LerayHopf\.Scratch\.$t" "$log" \
    || { echo "STALE TARGET: LerayHopf.Scratch.$t was not freshly compiled"; exit 1; }
done

# Join wrapped info lines (lake wraps long pin lines; continuations start with a
# space).  The per-declaration parser below is fail-closed against a bad join — a
# pin whose axiom bracket does not CLOSE on its joined line is reported MALFORMED and
# fails the gate, never silently dropped.
joined="$(tr '\n' '@' <"$log" | sed 's/@ / /g' | tr '@' '\n')"

# Exact pin set: the 13 declarations (of 14 total) that must pin to (a subset of) the
# kernel trio [propext, Classical.choice, Quot.sound].
# DiagonalExtraction (3) + KappaReindex (6) + GlobalContractTorus (1) +
# P2ExitContract (3).
pinned=(
  diagExtraction_strictMono
  exists_diagonal_extraction
  tendsto_diag_of_tendsto_stage
  exists_galerkin_modewise_extraction_kappa
  reindexed_family_second_extraction
  extendReindexedFamily_apply
  exists_galerkin_modewise_extraction_of_reindexed
  AubinLionsPackageKappa.effective_strictMono
  AubinLionsPackageKappa.extract_effective_strictMono
  globalTorusCapstone_implies_finite
  P2ExitWitness.pin_base
  P2ExitWitness.effective_strictMono
  P2ExitWitness.v_aestronglyMeasurable
)

fail=0
for d in "${pinned[@]}"; do
  line="$(printf '%s\n' "$joined" \
    | grep -F "'LerayHopf.Scratch195.$d' depends on axioms:" || true)"
  if [ -z "$line" ]; then echo "MISSING PIN: $d"; fail=1; continue; fi
  bracket="$(printf '%s\n' "$line" | sed -E 's/.*depends on axioms:[[:space:]]*//')"
  if ! printf '%s\n' "$bracket" | grep -qE '^\[[^][]*\]$'; then
    echo "MALFORMED PIN (bracket did not close on joined line): $d"; fail=1; continue
  fi
  if printf '%s\n' "$bracket" | sed -E 's/propext|Classical\.choice|Quot\.sound//g' \
      | grep -qE '[A-Za-z_]'; then
    echo "PIN VIOLATION: $line"; fail=1
  fi
done

# nestedComp_add (declaration 14) is axiom-free — assert its exact output POSITIVELY
# instead of letting it fall out of the 'depends on axioms' grep.
printf '%s\n' "$joined" \
  | grep -qF "'LerayHopf.Scratch195.nestedComp_add' does not depend on any axioms" \
  || { echo "MISSING AXIOM-FREE ASSERTION: nestedComp_add"; fail=1; }

# Exactness (both directions): total #print axioms outputs must be exactly 14 —
# a pin added to the sources without updating this checker fails the gate too.
total="$(printf '%s\n' "$joined" \
  | grep -cE "depends on axioms:|does not depend on any axioms" || true)"
[ "$total" -eq 14 ] || { echo "PIN COUNT MISMATCH: expected 14, observed $total"; fail=1; }

[ "$fail" -eq 0 ] || exit 1
echo "SCRATCH PIN CHECK OK (14/14: 13 kernel-trio pins + nestedComp_add axiom-free)"
