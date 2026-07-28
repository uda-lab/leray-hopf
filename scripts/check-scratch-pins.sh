#!/usr/bin/env bash
# Fail-closed scratch evidence gate (issue #195; §10.5 of
# docs/scratch/global-diagonal-campaign.md, pass-3 G-2, hardened at pass-4 H-1,
# retargeted for the POST-P1/P3/P4 trees by #200/#202/#203; EXTENDED at the #212
# B0 gate — see docs/scratch/r3-global-diagonal-campaign.md §6 clause 4 and the
# §11.x disposition tables — through six codex adversarial rounds, and REBUILT at
# the pass-7 remediation (codex pass-7 findings 1–3) around a STATIC OLEAN READER:
#
#   * pass-1..5 history: regex source manifest + build-log `#print axioms` parsing
#     (retired at pass-6 — text scanning cannot enumerate an elaborated
#     environment, and the build-log pin channel was spoofable by command output);
#   * pass-6: scripts/scratch_manifest.lean imported the targets and enumerated
#     the ELABORATED environment (retired at pass-7 — importing a target EXECUTES
#     it: initializers and registered command elaborators from a malicious target
#     would run inside the manifest process and could fake the evidence block);
#   * pass-7 (current): scripts/scratch_reader.lean imports ONLY `Lean` and reads
#     the target .olean files as DATA (`Lean.readModuleData`) — no target-authored
#     code executes anywhere in the evidence path.  Axiom closures come from the
#     toolchain's own precomputed `exportedAxiomsExt` entries (the data behind
#     `#print axioms`), statement shapes are frozen via per-declaration type
#     hashes, and the free-κ guards' proof terms are checked to reference their
#     seeded theorems (DEPGUARD).  See the reader's header for the full trust
#     model and the documented residual boundary.
#
# WHAT THIS SCRIPT ASSERTS, FAIL-CLOSED:
#   * every scratch target was FRESHLY rebuilt in this run (artifacts deleted
#     first; a cache replay cannot pass);
#   * the collision-fixture self-test passes (hand-written declarations with
#     generated-/internal-looking names are enumerated by the static channel —
#     pass-7 finding 1's evasion class, demonstrated on a compiled fixture);
#   * the reader run exits 0, its sentinel block is exactly-once and well-formed,
#     with zero VIOLATION lines (private/axiom/opaque/unsafe/initializer
#     declarations, any non-kernel-trio axiom, any constant missing a
#     toolchain-computed axiom entry, any free-κ guard not referencing its seed);
#   * the TOTAL manifest — every constant of every target: class, name, kind,
#     type hash, axiom closure, plus the DEPGUARD lines — is byte-identical to
#     the frozen scripts/scratch-manifest.expected.  Classification labels are
#     display-only; a smuggled declaration fails this diff WHATEVER label it
#     gets, because it is a new line (pass-7 finding 1: total pinning, "default
#     to surface" made moot by pinning every class);
#   * redundantly, the manifest's `surface` class equals the pinned 54-name
#     enumeration exactly (both directions), and every axiom field is re-verified
#     shell-side against the kernel trio.
#
# TAMPER ORDERING: the reader, the fixture self-test, and the expected manifest
# are snapshotted to a private temp dir BEFORE `lake build` runs, because
# building the (untrusted, diff-reviewed) scratch sources executes elaboration-
# time code that could rewrite files in the repo.  The whole script body is a
# single `main` function invoked with `; exit` so a mid-run rewrite of this file
# cannot inject into the running shell.
#
# The scratch targets are deliberately OUTSIDE the release cone (not imported by
# LerayHopf.lean), so agent-preflight.sh's default build does not rebuild them.
# The `#print axioms` footers in the scratch files remain as human-visible
# evidence but are NOT parsed by anything.
#
# WIRING: invoked UNWRAPPED from agent-preflight.sh and the lean.yml full-build
# job.  It self-locks via `exec 9>/tmp/lean-build.lock; flock 9`; wrapping it in
# an outer flock on the same lock self-deadlocks the container-wide build lock.
set -euo pipefail

main() {

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

export PATH="$HOME/.elan/bin:$PATH"
log="$(mktemp)"
fixture_out="$(mktemp)"
manifest_out="$(mktemp)"
snap="$(mktemp -d)"
trap 'rm -f "$log" "$fixture_out" "$manifest_out"; rm -rf "$snap"' EXIT

targets=(KappaReindex P2ExitContract KappaShapeGate R3ShapeGate R3StageCoherence R3KappaSeed R3ProductionCoupling)

# SNAPSHOT the trusted gate inputs BEFORE any untrusted build step (see TAMPER
# ORDERING above).  Everything the evidence path executes or compares against
# after this point comes from $snap, not from the working tree.
cp scripts/scratch_reader.lean scripts/scratch_fixture_selftest.lean \
   scripts/scratch-manifest.expected "$snap"/

# Take the container-wide build lock BEFORE the artifact deletion below and hold
# it through the run (PR #205 review: deleting outside the lock races a
# concurrent lock-holding lake process).  flock is present on this container
# (util-linux); if absent (non-Linux dev host) fall back to running without the
# lock — mirroring agent-preflight.sh's guard.
if command -v flock >/dev/null 2>&1; then
  exec 9>/tmp/lean-build.lock
  flock 9
else
  echo "WARNING: flock not found; running scratch-pin check without serialization lock." >&2
fi

# Freshness: delete the scratch modules' (and fixture's) build artifacts.  Lake
# cannot serve a stale artifact for a module whose artifacts are missing — it
# must genuinely re-elaborate it, and only genuine re-elaboration prints
# "Built <module>".  The static reader below then reads the freshly written
# oleans.  Upstream dependencies stay cached.
for t in "${targets[@]}" GateFixture; do
  rm -f ".lake/build/lib/lean/LerayHopf/Scratch/$t".*
done

lake build \
  LerayHopf.Scratch.KappaReindex \
  LerayHopf.Scratch.P2ExitContract \
  LerayHopf.Scratch.KappaShapeGate \
  LerayHopf.Scratch.R3ShapeGate \
  LerayHopf.Scratch.R3StageCoherence \
  LerayHopf.Scratch.R3KappaSeed \
  LerayHopf.Scratch.R3ProductionCoupling \
  LerayHopf.Scratch.GateFixture >"$log" 2>&1 \
  || { echo "BUILD FAILED"; tail -40 "$log"; exit 1; }
grep -q "Build completed successfully" "$log"

# Assertion: every target was BUILT in this run.  Cannot pass stale: the
# artifact deletion above forces a rebuild, and a replayed/skipped target would
# print "Replayed"/nothing instead of "Built" and fail here.
for t in "${targets[@]}" GateFixture; do
  grep -q "Built LerayHopf\.Scratch\.$t" "$log" \
    || { echo "STALE TARGET: LerayHopf.Scratch.$t was not freshly compiled"; exit 1; }
done

# COLLISION-FIXTURE SELF-TEST (pass-7 finding 1): the static channel must
# enumerate hand-written declarations whose names collide with generated/internal
# patterns.  Run from the snapshot; requires the OK line and exit 0.
lake env lean "$snap/scratch_fixture_selftest.lean" >"$fixture_out" 2>&1 \
  || { echo "FIXTURE SELF-TEST FAILED:"; cat "$fixture_out"; exit 1; }
grep -q '^FIXTURE-SELFTEST-OK$' "$fixture_out" \
  || { echo "FIXTURE SELF-TEST DID NOT REPORT OK:"; cat "$fixture_out"; exit 1; }

# STATIC OLEAN READER (pass-7 finding 2): the single evidence channel.  Run from
# the snapshot; imports only `Lean`; reads the freshly built oleans as data.
lake env lean "$snap/scratch_reader.lean" >"$manifest_out" 2>&1 \
  || { echo "STATIC READER FAILED (see VIOLATION lines / errors below):"
       grep -E '^VIOLATION\||error' "$manifest_out" | head -40; exit 1; }

# Sentinel discipline: exactly one START and one END line, END flagged OK with
# self-reported DECL/DEPGUARD counts, and the block between them must consist
# EXCLUSIVELY of DECL/DEPGUARD lines matching those counts.
n_start="$(grep -c '^SCRATCH-MANIFEST-START$' "$manifest_out")" || true
n_end="$(grep -c '^SCRATCH-MANIFEST-END|' "$manifest_out")" || true
[ "$n_start" -eq 1 ] && [ "$n_end" -eq 1 ] \
  || { echo "MANIFEST SENTINEL VIOLATION: $n_start START / $n_end END lines (expected exactly 1 each)"; exit 1; }
if grep -q '^VIOLATION|' "$manifest_out"; then
  echo "MANIFEST VIOLATIONS:"; grep '^VIOLATION|' "$manifest_out"; exit 1
fi
end_line="$(grep '^SCRATCH-MANIFEST-END|' "$manifest_out")"
printf '%s\n' "$end_line" | grep -qE '^SCRATCH-MANIFEST-END\|[0-9]+\|[0-9]+\|OK$' \
  || { echo "MANIFEST END LINE MALFORMED OR NOT OK: $end_line"; exit 1; }
declared="$(printf '%s\n' "$end_line" | cut -d'|' -f2)"
declared_dep="$(printf '%s\n' "$end_line" | cut -d'|' -f3)"
block="$(awk '/^SCRATCH-MANIFEST-START$/{inblk=1; next} /^SCRATCH-MANIFEST-END\|/{inblk=0} inblk' "$manifest_out")"
n_decl="$(printf '%s\n' "$block" | grep -c '^DECL|' || true)"
n_dep="$(printf '%s\n' "$block" | grep -c '^DEPGUARD|' || true)"
n_lines="$(printf '%s\n' "$block" | grep -c . || true)"
[ "$n_decl" -eq "$declared" ] && [ "$n_dep" -eq "$declared_dep" ] && [ "$n_dep" -eq 2 ] \
  && [ "$n_lines" -eq $((declared + declared_dep)) ] \
  || { echo "MANIFEST BLOCK MISMATCH: $n_decl DECL / $n_dep DEPGUARD / $n_lines lines vs $declared+$declared_dep declared (DEPGUARD must be exactly 2)"; exit 1; }

# TOTAL MANIFEST EQUALITY (pass-7 finding 1 — the load-bearing check): the block
# must be byte-identical to the frozen expected manifest.  Every constant of
# every target is pinned — name, kind, statement type-hash, axiom closure —
# whatever class label it carries.  Any added, removed, renamed, restated, or
# re-axiomed declaration fails here.
if ! diff <(printf '%s\n' "$block") "$snap/scratch-manifest.expected" >/dev/null; then
  echo "TOTAL MANIFEST MISMATCH (static reader vs scripts/scratch-manifest.expected):"
  diff <(printf '%s\n' "$block") "$snap/scratch-manifest.expected" | head -60 || true
  exit 1
fi

# Redundant SURFACE equality (both directions) against the human-reviewed pinned
# enumeration — keeps the review-relevant surface list explicit in this script.
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
if ! diff <(printf '%s\n' "$block" | awk -F'|' '$1=="DECL" && $2=="surface" {print $3}' | sort -u) \
          <(printf '%s\n' "${pinned[@]}" | sort -u) >/dev/null; then
  echo "SURFACE MISMATCH (static manifest vs pinned set):"
  diff <(printf '%s\n' "$block" | awk -F'|' '$1=="DECL" && $2=="surface" {print $3}' | sort -u) \
       <(printf '%s\n' "${pinned[@]}" | sort -u) || true
  exit 1
fi

# Kernel-trio re-verification, shell-side (defense in depth on top of the
# Lean-side check): every DECL line's axiom field — surface, child, internal,
# and codegen constants alike — must be `-` or a comma-joined subset of the trio.
if ! printf '%s\n' "$block" | awk -F'|' '
  $1=="DECL" {
    if ($6 == "-") next
    n = split($6, toks, ",")
    for (i = 1; i <= n; i++)
      if (toks[i] != "propext" && toks[i] != "Classical.choice" && toks[i] != "Quot.sound") {
        print "PIN VIOLATION: " $3 " depends on " toks[i]
        bad = 1
      }
  }
  END { exit bad }'; then
  exit 1
fi

# DEPGUARD (pass-7 finding 3): each free-κ guard's proof term must reference its
# seeded theorem directly.  Also covered by the total-manifest diff; asserted
# explicitly here so a failure names the broken guard.  The sanctioned P2′
# re-point (campaign doc §6 clause 6 rule (δ)) updates the reader's depGuards
# pairs, these two lines, and the expected manifest in the SAME reviewed diff.
for want in \
  'DEPGUARD|LerayHopf.Scratch212.diag_ae_subseq_seeded_free_kappa_exact_shape|LerayHopf.Scratch212.diag_ae_subseq_seeded|direct' \
  'DEPGUARD|LerayHopf.Scratch212.spacetime_extraction_seeded_free_kappa_exact_shape|LerayHopf.Scratch212.spacetime_extraction_seeded|direct'; do
  printf '%s\n' "$block" | grep -qxF "$want" \
    || { echo "DEPGUARD MISSING: $want"; exit 1; }
done

echo "SCRATCH PIN CHECK OK (54/54 surface declarations; total static manifest of $declared constants byte-pinned, kernel-trio only; $n_dep/2 free-kappa depguards; collision fixture enumerated)"

}

main "$@"; exit "$?"
