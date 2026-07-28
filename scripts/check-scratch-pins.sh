#!/usr/bin/env bash
# Fail-closed scratch evidence gate (issue #195; §10.5 of
# docs/scratch/global-diagonal-campaign.md, pass-3 G-2, hardened at pass-4 H-1,
# retargeted for the POST-P1 tree by #200; retargeted again for the POST-P3 tree by
# #202; retargeted again for the POST-P4 tree by #203; EXTENDED append-only at the
# #212 B0 gate with the two ℝ³-lane spike modules per the codex statement-gate
# finding 3; again append-only at the #212 B0 pass-3 remediation with the
# exact-shape gate module KappaShapeGate per codex pass-3 finding 1; at the
# pass-4 remediation with the full ℝ³ mirror shape gate R3ShapeGate; at the pass-5
# remediation with the production-coupling module R3ProductionCoupling; and REBUILT
# at the pass-6 remediation (codex pass-6 finding 1): the text-scanning manifest
# (regex over sources + `#print axioms` lines parsed from the lake build log) is
# RETIRED — text scanning cannot enumerate an elaborated environment, and the
# build-log pin channel was spoofable by command output.  Evidence now comes from
# ONE channel: scripts/scratch_manifest.lean enumerates every environment constant
# of every scratch target from the ELABORATED ENVIRONMENT and computes its axiom
# closure with `Lean.collectAxioms` (the machinery behind `#print axioms`).  This
# checker asserts, fail-closed:
#   * the manifest run exits 0, its sentinel block is exactly-once and well-formed,
#     and it reports zero VIOLATION lines (private/axiom/opaque/non-safe/initializer
#     declarations and any non-kernel-trio axiom are VIOLATIONs, enforced from the
#     environment where no surface spelling — Unicode names, anonymous instances,
#     macro-generated declarations, mutual/indented/modifier forms — can hide);
#   * the manifest's `surface` class equals the pinned 54-name enumeration EXACTLY
#     (both directions: an unpinned new declaration and a stale pin both fail);
#   * every enumerated constant's axiom list (surface, child, internal, codegen
#     constants alike — strictly more coverage than the retired per-pin scheme) is
#     a subset of the kernel trio [propext, Classical.choice, Quot.sound],
#     re-verified shell-side on top of the Lean-side check.
# The `#print axioms` footers in the scratch files remain as human-visible evidence
# but are NO LONGER parsed by anything.
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
manifest_out="$(mktemp)"
trap 'rm -f "$log" "$manifest_out"' EXIT

targets=(KappaReindex P2ExitContract KappaShapeGate R3ShapeGate R3StageCoherence R3KappaSeed R3ProductionCoupling)

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

# Freshness: delete the scratch modules' build artifacts (.olean/.ilean/.hash/.trace).
# Lake cannot serve a stale artifact or replay a cached log for a module whose
# artifacts are missing — it must genuinely re-elaborate it, and only genuine
# re-elaboration prints "Built <module>" (a cache hit prints "Replayed <module>").
# The environment manifest below then reads the freshly (re)written oleans.  Upstream
# dependencies stay cached, so the cost is exactly the scratch modules.
for t in "${targets[@]}"; do
  rm -f ".lake/build/lib/lean/LerayHopf/Scratch/$t".*
done

lake build \
  LerayHopf.Scratch.KappaReindex \
  LerayHopf.Scratch.P2ExitContract \
  LerayHopf.Scratch.KappaShapeGate \
  LerayHopf.Scratch.R3ShapeGate \
  LerayHopf.Scratch.R3StageCoherence \
  LerayHopf.Scratch.R3KappaSeed \
  LerayHopf.Scratch.R3ProductionCoupling >"$log" 2>&1 \
  || { echo "BUILD FAILED"; tail -40 "$log"; exit 1; }
grep -q "Build completed successfully" "$log"

# Assertion: every target was BUILT in this run.  Cannot pass stale: the artifact
# deletion above forces a rebuild, and a replayed/skipped target would print
# "Replayed"/nothing instead of "Built" and fail here.
for t in "${targets[@]}"; do
  grep -q "Built LerayHopf\.Scratch\.$t" "$log" \
    || { echo "STALE TARGET: LerayHopf.Scratch.$t was not freshly compiled"; exit 1; }
done

# Exact pinned SURFACE set: the 54 declarations (ALL user-written top-level
# declarations of every target; compiler-generated companions, internal auxiliaries,
# and codegen extras are classified separately by the manifest and axiom-checked
# there) whose axiom closures must stay within the kernel trio.  FULLY-QUALIFIED
# names — the torus (#195) spikes live in LerayHopf.Scratch195, the ℝ³ (#212)
# spikes, both shape-gate modules, and the production-coupling module in
# LerayHopf.Scratch212.
# KappaReindex (12) + P2ExitContract (4) + KappaShapeGate (4) + R3ShapeGate (18)
# + R3StageCoherence (3) + R3KappaSeed (2) + R3ProductionCoupling (11).
pinned=(
  LerayHopf.Scratch195.exists_galerkin_modewise_extraction_kappa
  LerayHopf.Scratch195.reindexed_family_second_extraction
  LerayHopf.Scratch195.AubinLionsPackageKappa
  LerayHopf.Scratch195.AubinLionsPackageKappa.ofId
  LerayHopf.Scratch195.AubinLionsPackageKappa.extract
  LerayHopf.Scratch195.extendReindexedFamily
  LerayHopf.Scratch195.extendReindexedFamily_apply
  LerayHopf.Scratch195.exists_galerkin_modewise_extraction_of_reindexed
  LerayHopf.Scratch195.AubinLionsPackageKappa.effective_strictMono
  LerayHopf.Scratch195.AubinLionsPackageKappa.effective_tendsto_atTop
  LerayHopf.Scratch195.AubinLionsPackageKappa.extract_φ
  LerayHopf.Scratch195.AubinLionsPackageKappa.extract_effective_strictMono
  LerayHopf.Scratch195.P2ExitWitness
  LerayHopf.Scratch195.P2ExitWitness.pin_base
  LerayHopf.Scratch195.P2ExitWitness.effective_strictMono
  LerayHopf.Scratch195.P2ExitWitness.v_aestronglyMeasurable
  LerayHopf.Scratch212.packageShape_strong_convergence_effective
  LerayHopf.Scratch212.packageShape_effective_strictMono
  LerayHopf.Scratch212.packageShape_effective_le_apply
  LerayHopf.Scratch212.witnessShape_pin_dependent_family
  LerayHopf.Scratch212.AubinLionsPackage_R3
  LerayHopf.Scratch212.AubinLionsPackage_R3.effective_strictMono
  LerayHopf.Scratch212.AubinLionsPackage_R3.effective_tendsto_atTop
  LerayHopf.Scratch212.r3PackageShape_strong_convergence_effective
  LerayHopf.Scratch212.r3PackageShape_strong_convergence_ae_effective
  LerayHopf.Scratch212.r3PackageShape_u_aestronglyMeasurable
  LerayHopf.Scratch212.r3PackageShape_effective_le_apply
  LerayHopf.Scratch212.R3LimitPassagePinConjunct
  LerayHopf.Scratch212.r3LimitPassagePinShape_effective
  LerayHopf.Scratch212.R3StrengthenedLimitPassageConclusion
  LerayHopf.Scratch212.r3StrengthenedConclusion_projects_pin
  LerayHopf.Scratch212.R3KappaChainExitWitness
  LerayHopf.Scratch212.r3WitnessShape_transport
  LerayHopf.Scratch212.r3WitnessShape_pin_dependent_family
  LerayHopf.Scratch212.r3WitnessShape_alPkg_effective_convergence
  LerayHopf.Scratch212.R3KappaChainExitWitness.effective_strictMono
  LerayHopf.Scratch212.R3KappaChainExitWitness.pin_base
  LerayHopf.Scratch212.R3KappaChainExitWitness.alPkg_convergence_dependent_family
  LerayHopf.Scratch212.L2Sigma_R3_eq_of_forall_inner
  LerayHopf.Scratch212.r3_representative_diag_coherence
  LerayHopf.Scratch212.r3_representatives_agree_on_overlap
  LerayHopf.Scratch212.diag_ae_subseq_seeded
  LerayHopf.Scratch212.spacetime_extraction_seeded
  LerayHopf.Scratch212.AubinLionsPackage_R3.ofProduction
  LerayHopf.Scratch212.AubinLionsPackage_R3.toProduction
  LerayHopf.Scratch212.r3LimitPassage_production_exact_shape
  LerayHopf.Scratch212.r3LimitPassagePin_production_source
  LerayHopf.Scratch212.r3Production_diag_ae_subseq_exact_shape
  LerayHopf.Scratch212.r3Production_u_lim_aestronglyMeasurable_exact_shape
  LerayHopf.Scratch212.r3Production_galerkinSpaceTimeExtraction_exact_shape
  LerayHopf.Scratch212.diag_ae_subseq_seeded_id_recovers_production
  LerayHopf.Scratch212.spacetime_extraction_seeded_id_recovers_production
  LerayHopf.Scratch212.diag_ae_subseq_seeded_free_kappa_exact_shape
  LerayHopf.Scratch212.spacetime_extraction_seeded_free_kappa_exact_shape
)

# ENVIRONMENT MANIFEST (pass-6 finding 1): the single evidence channel.  The Lean
# script imports the freshly built scratch targets, enumerates their constants from
# the elaborated environment, axiom-checks every one, and emits the sentinel block
# parsed below.  Nothing outside that block — build logs, module command output,
# comments — is ever consulted for evidence.
lake env lean scripts/scratch_manifest.lean >"$manifest_out" 2>&1 \
  || { echo "ENV MANIFEST FAILED (see VIOLATION lines / errors below):"
       grep -E '^VIOLATION\||error' "$manifest_out" | head -40; exit 1; }

# Sentinel discipline: exactly one START and one END line, END flagged OK, and the
# block between them must consist EXCLUSIVELY of DECL lines whose count matches the
# END line's self-reported count.  A spoofed block injected by import-time IO would
# duplicate the sentinels (the genuine block still prints) and fail here; truncated
# output fails the count; any stray line inside the block fails the grammar.
n_start="$(grep -c '^SCRATCH-MANIFEST-START$' "$manifest_out")" || true
n_end="$(grep -c '^SCRATCH-MANIFEST-END|' "$manifest_out")" || true
[ "$n_start" -eq 1 ] && [ "$n_end" -eq 1 ] \
  || { echo "MANIFEST SENTINEL VIOLATION: $n_start START / $n_end END lines (expected exactly 1 each)"; exit 1; }
if grep -q '^VIOLATION|' "$manifest_out"; then
  echo "MANIFEST VIOLATIONS:"; grep '^VIOLATION|' "$manifest_out"; exit 1
fi
end_line="$(grep '^SCRATCH-MANIFEST-END|' "$manifest_out")"
printf '%s\n' "$end_line" | grep -qE '^SCRATCH-MANIFEST-END\|[0-9]+\|OK$' \
  || { echo "MANIFEST END LINE MALFORMED OR NOT OK: $end_line"; exit 1; }
declared="$(printf '%s\n' "$end_line" | cut -d'|' -f2)"
block="$(awk '/^SCRATCH-MANIFEST-START$/{inblk=1; next} /^SCRATCH-MANIFEST-END\|/{inblk=0} inblk' "$manifest_out")"
n_decl="$(printf '%s\n' "$block" | grep -c '^DECL|' || true)"
n_lines="$(printf '%s\n' "$block" | grep -c . || true)"
[ "$n_decl" -eq "$declared" ] && [ "$n_lines" -eq "$declared" ] \
  || { echo "MANIFEST BLOCK MISMATCH: $n_decl DECL / $n_lines lines vs $declared declared"; exit 1; }

# SURFACE equality (both directions): the manifest's surface class must equal the
# pinned enumeration exactly.  A declaration added to a scratch target without a
# checker entry — whatever its spelling — appears here as an unexpected surface
# name; a pin for a deleted declaration appears as missing.
if ! diff <(printf '%s\n' "$block" | awk -F'|' '$1=="DECL" && $2=="surface" {print $3}' | sort -u) \
          <(printf '%s\n' "${pinned[@]}" | sort -u) >/dev/null; then
  echo "SURFACE MISMATCH (environment manifest vs pinned set):"
  diff <(printf '%s\n' "$block" | awk -F'|' '$1=="DECL" && $2=="surface" {print $3}' | sort -u) \
       <(printf '%s\n' "${pinned[@]}" | sort -u) || true
  exit 1
fi

# Kernel-trio re-verification, shell-side (defense in depth on top of the Lean-side
# check): every DECL line's axiom field — surface, child, internal, and codegen
# constants alike — must be `-` or a comma-joined subset of the exact trio.
if ! printf '%s\n' "$block" | awk -F'|' '
  $1=="DECL" {
    if ($5 == "-") next
    n = split($5, toks, ",")
    for (i = 1; i <= n; i++)
      if (toks[i] != "propext" && toks[i] != "Classical.choice" && toks[i] != "Quot.sound") {
        print "PIN VIOLATION: " $3 " depends on " toks[i]
        bad = 1
      }
  }
  END { exit bad }'; then
  exit 1
fi

echo "SCRATCH PIN CHECK OK (54/54 surface declarations, env-manifest of $declared constants, kernel-trio only)"
