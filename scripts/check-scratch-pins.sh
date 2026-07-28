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
#   * pass-7, hardened at pass-8 (current): scripts/scratch_reader.lean imports
#     ONLY `Lean` and reads the target .olean files as DATA
#     (`Lean.readModuleData`) — no target-authored code executes anywhere in the
#     evidence path.  Axiom closures come from the toolchain's own precomputed
#     `exportedAxiomsExt` entries (the data behind `#print axioms`; the single
#     marked decode is registered in the reader's ASSUMPTIONS A1–A4 — pass-8
#     finding 1).  Statements are frozen via per-declaration SHA-256 digests
#     over a canonical hash-consed serialization of levelParams + elaborated
#     type (pass-8 finding 2 retired the 32-bit-truncating `Expr.hash`;
#     pass-9 finding 1 rekeyed the serializer's memoization from
#     alpha-equivalence to exact structural equality, with per-run
#     discrimination fixtures), and every production-coupling probe's proof
#     term must have its pinned constant as the APPLICATION HEAD (pass-8
#     finding 3 retired mere getUsedConstants occurrence; pass-9 finding 2
#     extended the pins from the two free-κ guards to the full 11-entry
#     table, encoding production-head vs seed-head intent; pass-9 finding 3
#     added exact per-module bijection validation of the axiom entries;
#     pass-10 upgraded the destructuring probe's pin from direct reference to
#     a structural `exists-destruct` check — its proof term must BE an
#     Exists.casesOn application whose scrutinee is headed by the pinned
#     production existential, dead mentions rejected).  See
#     the reader's header for the full trust model and the documented residual
#     boundary.
#
# WHAT THIS SCRIPT ASSERTS, FAIL-CLOSED:
#   * every scratch target was FRESHLY rebuilt in this run (artifacts deleted
#     first; a cache replay cannot pass);
#   * the collision-fixture self-test passes (hand-written declarations with
#     generated-/internal-looking names are enumerated by the static channel —
#     pass-7 finding 1's evasion class, demonstrated on a compiled fixture);
#   * the reader run exits 0, its sentinel block is exactly-once and well-formed,
#     with zero VIOLATION lines (private/axiom/opaque/unsafe/initializer
#     declarations, any non-kernel-trio axiom, any axiom-entry bijection defect
#     — duplicate/unknown/missing/count, any coupling probe whose proof term
#     does not head on / structurally destructure its pinned constant, any
#     serializer fixture that fails to discriminate);
#   * the TOTAL manifest — every constant of every target: class, name, kind,
#     sha-256 statement digest, axiom closure, plus the DEPGUARD lines — is
#     byte-identical to the frozen scripts/scratch-manifest.expected.  Classification labels are
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
[ "$n_decl" -eq "$declared" ] && [ "$n_dep" -eq "$declared_dep" ] && [ "$n_dep" -eq 11 ] \
  && [ "$n_lines" -eq $((declared + declared_dep)) ] \
  || { echo "MANIFEST BLOCK MISMATCH: $n_decl DECL / $n_dep DEPGUARD / $n_lines lines vs $declared+$declared_dep declared (DEPGUARD must be exactly 11)"; exit 1; }

# SERIALIZER DISCRIMINATION FIXTURES (pass-9 finding 1): the reader must attest,
# per run, that each GateFixture pair is alpha-equivalent (Expr.eqv — the class
# the retired eqv-keyed memoization collapsed) yet canonically DISTINCT under
# the structural-keyed serializer.  Emitted before the START sentinel.
for want in \
  'FIXTURE-DIGEST|alpha-binder-name|eqv-equal-canonical-distinct' \
  'FIXTURE-DIGEST|binder-info|eqv-equal-canonical-distinct'; do
  grep -qxF "$want" "$manifest_out" \
    || { echo "SERIALIZER FIXTURE MISSING: $want"; exit 1; }
done

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

# Digest-field sanity, shell-side (defense in depth on top of the byte-diff):
# every real constant's digest must be exactly 64 lowercase-hex chars; `-` is
# reserved for codegen extras (which have no ConstantInfo).  length()-based —
# mawk does not support {n} interval regexes.
if ! printf '%s\n' "$block" | awk -F'|' '
  $1=="DECL" {
    if ($5 == "-") { if ($4 != "codegen") { print "DIGEST VIOLATION: " $3 " has no digest but is " $4; bad = 1 }; next }
    if (length($5) != 64 || $5 ~ /[^0-9a-f]/) { print "DIGEST VIOLATION: " $3 " malformed digest " $5; bad = 1 }
  }
  END { exit bad }'; then
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

# DEPGUARD (pass-7 finding 3; head semantics per pass-8 finding 3; extended to
# the FULL 11-pin production-coupling table per pass-9 finding 2): each probe's
# proof term — its own binders and inert mdata stripped — must have the pinned
# constant as its APPLICATION HEAD; the pin encodes production-head vs
# seed-head vs constructor-head intent, so a probe silently re-proved from the
# wrong side fails even with an identical statement digest.  The single
# `exists-destruct` pin (structural since pass-10; the pass-9 direct-reference
# `uses` mode also accepted dead mentions) is the documented destructuring
# probe (r3LimitPassagePin_production_source: obtain/exact over the production
# existential — its proof term must BE an Exists.casesOn application whose
# SCRUTINEE is headed by exists_weak_representative_R3, with direct reference
# retained as a secondary guard).  Also covered by the total-manifest diff; asserted explicitly
# here so a failure names the broken probe.  The sanctioned P2′ re-point
# (campaign doc §6 clause 6 rule (δ)) rewrites the reader's pin table, these
# lines, and the expected manifest in the SAME reviewed diff as the probe
# changes (deleted probes lose pins; free-κ guard heads swap to the κ-threaded
# production declarations; exact-shape probes keep their production heads).
for want in \
  'DEPGUARD|LerayHopf.Scratch212.AubinLionsPackage_R3.ofProduction|LerayHopf.Scratch212.AubinLionsPackage_R3.mk|head' \
  'DEPGUARD|LerayHopf.Scratch212.AubinLionsPackage_R3.toProduction|LerayHopf.AubinLionsPackage_R3.mk|head' \
  'DEPGUARD|LerayHopf.Scratch212.r3LimitPassage_production_exact_shape|LerayHopf.galerkin_limit_passage_R3|head' \
  'DEPGUARD|LerayHopf.Scratch212.r3LimitPassagePin_production_source|LerayHopf.exists_weak_representative_R3|exists-destruct' \
  'DEPGUARD|LerayHopf.Scratch212.r3Production_diag_ae_subseq_exact_shape|LerayHopf.diag_ae_subseq|head' \
  'DEPGUARD|LerayHopf.Scratch212.r3Production_u_lim_aestronglyMeasurable_exact_shape|LerayHopf.u_lim_aestronglyMeasurable|head' \
  'DEPGUARD|LerayHopf.Scratch212.r3Production_galerkinSpaceTimeExtraction_exact_shape|LerayHopf.galerkinSpaceTimeExtraction_R3|head' \
  'DEPGUARD|LerayHopf.Scratch212.diag_ae_subseq_seeded_id_recovers_production|LerayHopf.Scratch212.diag_ae_subseq_seeded|head' \
  'DEPGUARD|LerayHopf.Scratch212.spacetime_extraction_seeded_id_recovers_production|LerayHopf.Scratch212.spacetime_extraction_seeded|head' \
  'DEPGUARD|LerayHopf.Scratch212.diag_ae_subseq_seeded_free_kappa_exact_shape|LerayHopf.Scratch212.diag_ae_subseq_seeded|head' \
  'DEPGUARD|LerayHopf.Scratch212.spacetime_extraction_seeded_free_kappa_exact_shape|LerayHopf.Scratch212.spacetime_extraction_seeded|head'; do
  printf '%s\n' "$block" | grep -qxF "$want" \
    || { echo "DEPGUARD MISSING: $want"; exit 1; }
done

echo "SCRATCH PIN CHECK OK (54/54 surface declarations; total static manifest of $declared constants byte-pinned, statements sha256-frozen, kernel-trio only; $n_dep/11 coupling value-pins (10 head + 1 exists-destruct); collision + serializer fixtures verified)"

}

main "$@"; exit "$?"
