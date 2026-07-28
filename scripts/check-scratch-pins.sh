#!/usr/bin/env bash
# Fail-closed scratch evidence gate (issue #195; §10.5 of
# docs/scratch/global-diagonal-campaign.md, pass-3 G-2, hardened at pass-4 H-1,
# retargeted for the POST-P1 tree by #200; retargeted again for the POST-P3 tree by
# #202; retargeted again for the POST-P4 tree by #203; EXTENDED append-only at the
# #212 B0 gate with the two ℝ³-lane spike modules per the codex statement-gate
# finding 3; again append-only at the #212 B0 pass-3 remediation with the
# exact-shape gate module KappaShapeGate per codex pass-3 finding 1; and again at the
# pass-4 remediation with the full ℝ³ mirror shape gate R3ShapeGate (pass-4 finding 1)
# and the source-manifest equality check (pass-4 finding 3); and again at the pass-5
# remediation with the production-coupling module R3ProductionCoupling (pass-5
# findings 1+2) and the fail-closed source-discipline rejections (pass-5 finding 3) —
# docs/scratch/r3-global-diagonal-campaign.md §11): forced-fresh
# compilation + EXACT 52-declaration pin-set check + MANIFEST equality (every
# top-level declaration in every scratch target MUST carry a #print axioms pin —
# a new declaration added without a pin fails the gate).  Non-zero exit
# on build failure, stale/replayed
# target, missing or malformed pin, any axiom token outside the kernel trio, any
# pin output beyond the enumerated set, or any unpinned source declaration.
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

# Join wrapped info lines (lake wraps long pin lines; continuations start with a
# space).  The per-declaration parser below is fail-closed against a bad join — a
# pin whose axiom bracket does not CLOSE on its joined line is reported MALFORMED and
# fails the gate, never silently dropped.
joined="$(tr '\n' '@' <"$log" | sed 's/@ / /g' | tr '@' '\n')"

# Exact pin set: the 52 declarations (ALL top-level declarations of every target —
# pass-4 finding 3: completeness is asserted against a source-derived manifest below)
# that must pin to (a subset of) the kernel trio [propext, Classical.choice,
# Quot.sound].  FULLY-QUALIFIED names — the torus (#195) spikes live in
# LerayHopf.Scratch195, the ℝ³ (#212) spikes, both shape-gate modules, and the
# production-coupling module in LerayHopf.Scratch212.
# KappaReindex (12) + P2ExitContract (4) + KappaShapeGate (4) + R3ShapeGate (18)
# + R3StageCoherence (3) + R3KappaSeed (2) + R3ProductionCoupling (9).
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
)

# MANIFEST equality (pass-4 finding 3, fail-closed for UNPINNED declarations): derive
# the set of top-level declarations from the target SOURCES (keyword-led lines only;
# namespace prefix joined from the file's `namespace` lines) and require exact set
# equality with the pinned enumeration above.  A theorem/def/structure added to a
# scratch target without a matching pin line + checker entry fails HERE, before any
# axiom parsing.  (`example`/`variable`/`open` lines declare nothing pinnable and are
# intentionally not matched.)
# SOURCE DISCIPLINE (pass-5 finding 3, fail-closed): the manifest extractor below only
# understands top-level, unmodified declarations under a single namespace-nesting
# chain.  Rather than growing the regex to parse every Lean surface form, scratch
# targets REJECT outright anything the extractor cannot see — a false positive fails
# the gate loudly (reword the offending line); a false negative cannot occur for the
# rejected forms because they never reach the manifest:
#   (1) modifier-prefixed declarations (private/protected/scoped/local/nonrec/partial/
#       unsafe) and mutual blocks — the name would evade extraction (and a `private`
#       name cannot even be pinned by `#print axioms` from outside);
#   (2) `class`/`class inductive` at top level — not in the manifest keyword set;
#   (3) INDENTED declaration keywords — mutual/nested blocks evade the top-level
#       anchor;
#   (4) namespace-line irregularities: indented or dotted `namespace`, a `namespace`
#       after the first declaration, or namespace/`end` count imbalance — any of
#       these silently mis-qualifies every extracted name.
decl_kw='(theorem|lemma|def|abbrev|structure|inductive|instance|opaque|axiom|class)'
for t in "${targets[@]}"; do
  f="LerayHopf/Scratch/$t.lean"
  if grep -nE "^(@\[[^]]*\][[:space:]]*)?(noncomputable[[:space:]]+)?(private|protected|scoped|local|nonrec|partial|unsafe|mutual)([[:space:]]|$)" "$f"; then
    echo "SOURCE DISCIPLINE: modifier-prefixed/mutual declaration in $f (forbidden in scratch targets — not manifest-visible)"; exit 1
  fi
  if grep -nE '^class([[:space:]]|$)' "$f"; then
    echo "SOURCE DISCIPLINE: top-level class declaration in $f (forbidden in scratch targets — not in the manifest keyword set)"; exit 1
  fi
  if grep -nE "^[[:space:]]+(@\[[^]]*\][[:space:]]*)?(noncomputable[[:space:]]+)?${decl_kw}[[:space:]]+[A-Za-z_]" "$f"; then
    echo "SOURCE DISCIPLINE: indented declaration keyword in $f (forbidden in scratch targets — evades the top-level manifest anchor; reword if this is a comment)"; exit 1
  fi
  if grep -nE '^[[:space:]]+namespace([[:space:]]|$)|^namespace[[:space:]]+[A-Za-z0-9_]*\.' "$f"; then
    echo "SOURCE DISCIPLINE: indented or dotted namespace line in $f"; exit 1
  fi
  first_decl="$(grep -nE "^(@\[[^]]*\][[:space:]]*)?(noncomputable[[:space:]]+)?${decl_kw}[[:space:]]" "$f" | head -1 | cut -d: -f1)"
  last_ns="$(grep -nE '^namespace ' "$f" | tail -1 | cut -d: -f1)"
  [ -n "$first_decl" ] && [ -n "$last_ns" ] && [ "$last_ns" -lt "$first_decl" ] \
    || { echo "SOURCE DISCIPLINE: namespace line missing or not preceding the first declaration in $f"; exit 1; }
  n_ns="$(grep -cE '^namespace ' "$f")" || true
  n_end="$(grep -cE '^end([[:space:]]|$)' "$f")" || true
  [ "$n_ns" -eq "$n_end" ] \
    || { echo "SOURCE DISCIPLINE: namespace/end count imbalance in $f ($n_ns namespace vs $n_end end)"; exit 1; }
done

manifest="$(mktemp)"
trap 'rm -f "$log" "$manifest"' EXIT
for t in "${targets[@]}"; do
  f="LerayHopf/Scratch/$t.lean"
  ns="$(sed -nE 's/^namespace ([A-Za-z0-9_]+)[[:space:]]*$/\1/p' "$f" | paste -sd. -)"
  [ -n "$ns" ] || { echo "MANIFEST ERROR: no namespace lines found in $f"; exit 1; }
  sed -nE 's/^(@\[[^]]*\][[:space:]]*)?(noncomputable[[:space:]]+)?(theorem|lemma|def|abbrev|structure|inductive|instance|opaque|axiom)[[:space:]]+([^ :({⟨\[]+).*/\4/p' "$f" \
    | sed "s/^/$ns./" >>"$manifest"
done
if ! diff <(sort -u "$manifest") <(printf '%s\n' "${pinned[@]}" | sort -u) >/dev/null; then
  echo "MANIFEST MISMATCH (source declarations vs pinned set):"
  diff <(sort -u "$manifest") <(printf '%s\n' "${pinned[@]}" | sort -u) || true
  exit 1
fi

fail=0
for d in "${pinned[@]}"; do
  line="$(printf '%s\n' "$joined" \
    | grep -F "'$d' depends on axioms:" || true)"
  if [ -z "$line" ]; then
    # Structures/defs with no proof content print the axiom-free form; the empty
    # axiom set is trivially a subset of the kernel trio.
    if printf '%s\n' "$joined" | grep -qF "'$d' does not depend on any axioms"; then
      continue
    fi
    echo "MISSING PIN: $d"; fail=1; continue
  fi
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

# Exactness (both directions): total #print axioms outputs must be exactly 52 —
# a pin added to the sources without updating this checker fails the gate too.
total="$(printf '%s\n' "$joined" \
  | grep -cE "depends on axioms:|does not depend on any axioms" || true)"
[ "$total" -eq 52 ] || { echo "PIN COUNT MISMATCH: expected 52, observed $total"; fail=1; }

[ "$fail" -eq 0 ] || exit 1
echo "SCRATCH PIN CHECK OK (52/52: manifest-complete, kernel-trio only)"
