#!/usr/bin/env bash
# Fail-closed scratch evidence gate (issue #195; §10.5 of
# docs/scratch/global-diagonal-campaign.md, pass-3 G-2, hardened at pass-4 H-1,
# retargeted for the POST-P1 tree by #200; retargeted again for the POST-P3 tree by
# #202; retargeted again for the POST-P4 tree by #203; EXTENDED append-only at the
# #212 B0 gate with the two ℝ³-lane spike modules per the codex statement-gate
# finding 3, and again append-only at the #212 B0 pass-3 remediation with the
# exact-shape gate module KappaShapeGate per codex pass-3 finding 1 —
# docs/scratch/r3-global-diagonal-campaign.md §11): forced-fresh
# compilation + EXACT 18-declaration pin-set check.  Non-zero exit
# on build failure, stale/replayed
# target, missing or malformed pin, any axiom token outside the kernel trio, or any
# pin output beyond the enumerated set.
#
# The scratch targets are deliberately OUTSIDE the release cone (not
# imported by LerayHopf.lean), so agent-preflight.sh's default build does not rebuild
# them.  This checker rebuilds them from scratch and asserts their axiom hygiene.  The
# former GlobalContract (12 pins) was promoted into the release cone by #200 and is now
# covered there (plus the interim live pins in check-axioms-live.sh); it is no longer a
# scratch target here.  GlobalContractTorus (the P4 feasibility spike) was likewise
# promoted into the release cone by #203 (LerayHopf.Torus.GlobalCapstone) and DELETED
# as a scratch module; its single pin (globalTorusCapstone_implies_finite) is now a
# live pin in check-axioms-live.sh (pin 16).
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

targets=(KappaReindex P2ExitContract KappaShapeGate R3StageCoherence R3KappaSeed)

# Take the container-wide build lock BEFORE the artifact deletion below and hold it
# through the build (PR #205 review: deleting outside the lock races a concurrent
# lock-holding lake process — it could remove artifacts that build just produced or
# is about to consume).  FD 9 keeps the same /tmp/lean-build.lock every other lean
# build in this container serializes on; it is released when the script exits.
# flock is present on this container (util-linux); if absent (non-Linux dev host) we
# fall back to running without the lock — mirroring agent-preflight.sh's guard — rather
# than aborting the mandatory preflight in an environment it explicitly supports.
if command -v flock >/dev/null 2>&1; then
  exec 9>/tmp/lean-build.lock
  flock 9
else
  echo "WARNING: flock not found; running scratch-pin check without serialization lock." >&2
fi

# Freshness: delete the two modules' build artifacts (.olean/.ilean/.hash/.trace).
# Lake cannot serve a stale artifact or replay a cached log for a module whose
# artifacts are missing — it must genuinely re-elaborate it, and only genuine
# re-elaboration prints "Built <module>" (a cache hit prints "Replayed <module>")
# and re-runs the #print axioms commands whose output is parsed below.  Upstream
# dependencies stay cached, so the cost is exactly the two scratch modules.
for t in "${targets[@]}"; do
  rm -f ".lake/build/lib/lean/LerayHopf/Scratch/$t".*
done

lake build \
  LerayHopf.Scratch.KappaReindex \
  LerayHopf.Scratch.P2ExitContract \
  LerayHopf.Scratch.KappaShapeGate \
  LerayHopf.Scratch.R3StageCoherence \
  LerayHopf.Scratch.R3KappaSeed >"$log" 2>&1 \
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

# Exact pin set: the 18 declarations (all of them) that must pin to (a subset of) the
# kernel trio [propext, Classical.choice, Quot.sound].  FULLY-QUALIFIED names — the
# torus (#195) spikes live in LerayHopf.Scratch195, the ℝ³ (#212) spikes and the
# exact-shape gate probes in LerayHopf.Scratch212.
# KappaReindex (6) + P2ExitContract (3) + KappaShapeGate (4) + R3StageCoherence (3)
# + R3KappaSeed (2).
pinned=(
  LerayHopf.Scratch195.exists_galerkin_modewise_extraction_kappa
  LerayHopf.Scratch195.reindexed_family_second_extraction
  LerayHopf.Scratch195.extendReindexedFamily_apply
  LerayHopf.Scratch195.exists_galerkin_modewise_extraction_of_reindexed
  LerayHopf.Scratch195.AubinLionsPackageKappa.effective_strictMono
  LerayHopf.Scratch195.AubinLionsPackageKappa.extract_effective_strictMono
  LerayHopf.Scratch195.P2ExitWitness.pin_base
  LerayHopf.Scratch195.P2ExitWitness.effective_strictMono
  LerayHopf.Scratch195.P2ExitWitness.v_aestronglyMeasurable
  LerayHopf.Scratch212.packageShape_strong_convergence_effective
  LerayHopf.Scratch212.packageShape_effective_strictMono
  LerayHopf.Scratch212.packageShape_effective_le_apply
  LerayHopf.Scratch212.witnessShape_pin_dependent_family
  LerayHopf.Scratch212.L2Sigma_R3_eq_of_forall_inner
  LerayHopf.Scratch212.r3_representative_diag_coherence
  LerayHopf.Scratch212.r3_representatives_agree_on_overlap
  LerayHopf.Scratch212.diag_ae_subseq_seeded
  LerayHopf.Scratch212.spacetime_extraction_seeded
)

fail=0
for d in "${pinned[@]}"; do
  line="$(printf '%s\n' "$joined" \
    | grep -F "'$d' depends on axioms:" || true)"
  if [ -z "$line" ]; then echo "MISSING PIN: $d"; fail=1; continue; fi
  bracket="$(printf '%s\n' "$line" | sed -E 's/.*depends on axioms:[[:space:]]*//')"
  if ! printf '%s\n' "$bracket" | grep -qE '^\[[^][]*\]$'; then
    echo "MALFORMED PIN (bracket did not close on joined line): $d"; fail=1; continue
  fi
  # Compare each COMPLETE axiom token against the exact kernel trio.  A substring
  # strip is not fail-closed: a Unicode-only root name (e.g. ω) escapes an ASCII
  # grep, and a digit-extended name (e.g. Classical.choice2) survives the strip as
  # bare digits.  Split the bracketed, comma-separated list and match whole tokens.
  inner="$(printf '%s\n' "$bracket" | sed -E 's/^\[[[:space:]]*//; s/[[:space:]]*\]$//')"
  IFS=',' read -ra toks <<<"$inner" || true
  for tok in ${toks[@]+"${toks[@]}"}; do
    tok="$(printf '%s' "$tok" | sed -E 's/^[[:space:]]+//; s/[[:space:]]+$//')"
    [ -z "$tok" ] && continue
    case "$tok" in
      propext|Classical.choice|Quot.sound) ;;
      *) echo "PIN VIOLATION: $line"; fail=1; break ;;
    esac
  done
done

# Exactness (both directions): total #print axioms outputs must be exactly 18 —
# a pin added to the sources without updating this checker fails the gate too.
total="$(printf '%s\n' "$joined" \
  | grep -cE "depends on axioms:|does not depend on any axioms" || true)"
[ "$total" -eq 18 ] || { echo "PIN COUNT MISMATCH: expected 18, observed $total"; fail=1; }

[ "$fail" -eq 0 ] || exit 1
echo "SCRATCH PIN CHECK OK (18/18: 18 kernel-trio pins)"
