#!/usr/bin/env bash
# §4.1 defense-in-depth #2 / §6 clause 5 — automated stale-index audit.
#
# The κ-threading campaign (issue #212, P2′) parameterizes AubinLionsPackage_R3
# by an abstract shift `κ : ℕ → ℕ`, so every convergence fact must be consumed at
# the EFFECTIVE index `κ (φ n)`, never at the bare extraction index `φ n`.  This is
# a TYPE-level invariant (the package fields are typed at `galSeq (κ (φ n))`), and
# the exact-shape gate (§6 clause 3) asserts it mechanically.  This script is the
# residual-hygiene belt-and-suspenders on top of that assertion: a purely lexical
# fail-closed scan of the κ-generic production files that catches a stale index
# BEFORE it can typecheck (e.g. a future edit that reintroduces `alPkg.φ` at a
# total family, or derives a category-(iii) selection fact from bare `φ_mono`).
#
# It fails closed on:
#   (a) any application of a TOTAL family (`galSeq`, `base`, `fill`) at a bare
#       DOTTED extraction index — `galSeq (alPkg.φ`, `base (p.φ`, `fill (w.alPkg.φ`
#       and spacing variants.  The correct effective form nests κ:
#       `galSeq (κ (alPkg.φ n))`, whose open paren is followed by `κ`, not by the
#       package receiver, so it is (correctly) NOT matched.  Bare LOCAL `φ`
#       (non-dotted, e.g. `galSeq (φ n)` inside the pre-package diagonal-extraction
#       lemmas) is likewise not matched — the discipline binds the package
#       extraction `alPkg.φ`, not free extraction arguments upstream of it.
#   (b) bare-`φ` category-(iii) consumption sites: `.φ_mono` (and the
#       `.φ_mono.le_apply`-shaped bounds it subsumes) used anywhere except the
#       effective-map composition lemmas' own defining use, and `≤ <pkg>.φ`-shaped
#       bounds phrased at the bare extraction instead of the composed index.
#
# Allowlist: a matched line carrying a same-line `-- KAPPA_ID_SITE: <reason>`
# marker is exempt (mirrors the ALLOW_NAME / ALLOW_AXIOM mechanism).  Legitimate
# exemptions are the composition lemmas' defining `φ_mono` use (the single
# sanctioned category-(iii) source) and any genuine fixed-horizon `κ := id` site.
#
# Fail-loud, no build required (pure text scan).  Exit 0 = clean, 1 = violations.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

# The κ-generic production files: every module that consumes AubinLionsPackage_R3
# convergence data (or defines the package / exit witness) and must therefore
# phrase index selection at the effective index `κ (φ n)`.
FILES=(
  LerayHopf/R3/ArzelaAscoliTime.lean
  LerayHopf/R3/SteklovAverages.lean
  LerayHopf/R3/AubinLionsLimitPassage.lean
  LerayHopf/R3/SolutionInterfaces.lean
  LerayHopf/R3/EnergyWeakLsc.lean
  LerayHopf/R3/GoodRepresentative.lean
  LerayHopf/R3/LimitPassage.lean
  LerayHopf/R3/AubinLionsAssembly.lean
  LerayHopf/R3/KappaChainExit.lean
  LerayHopf/R3/DiagonalGalerkin.lean
  LerayHopf/R3/GlobalCapstone.lean
)

# Fail CLOSED on a missing audit input (codex #220 finding 2): if a κ-generic
# module is renamed, deleted, or misspelled here while its replacement still
# builds, a plain `grep file...` would exit 2 on the absent path — and the old
# `2>/dev/null || true` swallowed that into an empty hit set, printing "AUDIT OK"
# while silently skipping a required module.  Assert every input exists and is
# readable BEFORE scanning, so a dropped module trips the gate instead.
for f in "${FILES[@]}"; do
  if [ ! -f "$f" ] || [ ! -r "$f" ]; then
    echo "KAPPA EFFECTIVE-INDEX AUDIT FAILED — audit input missing/unreadable: $f" >&2
    echo "  A κ-generic module was renamed/deleted/misspelled. Update the FILES=()" >&2
    echo "  array in this script to match the current module layout." >&2
    exit 1
  fi
done

ALLOW='-- KAPPA_ID_SITE:'

# Identifier-chain receiver ending in `.φ` (extraction projection), where the
# trailing char after φ is NOT `_` (so `.φ_mono` is excluded from the extraction
# patterns and handled separately as category (iii)).
IDENT='[A-Za-z_][A-Za-z0-9_.'"'"']*'

# (a) total family at a bare dotted extraction index.
PAT_TOTAL="(galSeq|base|fill)[[:space:]]*\\([[:space:]]*${IDENT}\\.φ([^_]|\$)"
# (b1) bare φ_mono (subsumes `.φ_mono.le_apply`): category-(iii) source discipline.
PAT_PHIMONO='\.φ_mono'
# (b2) bound phrased at the bare dotted extraction rather than the composed index.
PAT_BOUND="≤[[:space:]]*${IDENT}\\.φ([^_]|\$)"

violations=0

report() {
  # $1 = human-readable pattern label, $2 = extended regex
  local label="$1" regex="$2" f matched found=0
  for f in "${FILES[@]}"; do
    # Codex #220 finding 1: when Lean wraps a forbidden form across lines (e.g.
    # `n ≤` then `alPkg.φ n`, or `galSeq (` then `alPkg.φ n)`), a line-oriented
    # grep never sees the two halves together, so `[[:space:]]*` cannot bridge
    # them and the violation slips through.  Scan each file as ONE NUL-delimited
    # record (`grep -z`): with no NUL bytes in Lean source the whole file is a
    # single record, so `[[:space:]]` (which includes `\n`) spans physical line
    # breaks.  `-o` emits just the matched text (NUL-separated) for the report;
    # `tr` renders it.  Allowlisted (`-- KAPPA_ID_SITE:`) lines are dropped
    # first — the marker is a same-line convention, so line-wise removal is
    # correct for every current exemption.  Line numbers are traded for
    # whole-file localization; when the gate fires a human inspects the file.
    if matched="$(grep -vF -e "$ALLOW" -- "$f" | grep -zoE -- "$regex" | tr '\0' '\n')"; then
      : # match found (pipeline exit 0)
    fi
    matched="$(printf '%s' "$matched" | sed '/^[[:space:]]*$/d')"
    if [ -n "$matched" ]; then
      echo "FAIL [$label]: $f"
      printf '%s\n' "$matched" | sed 's/^/  ⟶ /'
      found=1
    fi
  done
  if [ "$found" -ne 0 ]; then
    violations=$((violations + 1))
  fi
}

report "total-family @ bare extraction index (want κ (φ n), not φ n)" "$PAT_TOTAL"
report "bare φ_mono category-(iii) source (derive from effective_strictMono)" "$PAT_PHIMONO"
report "bound @ bare extraction index (want ≤ κ (φ n))" "$PAT_BOUND"

if [ "$violations" -ne 0 ]; then
  echo ""
  echo "KAPPA EFFECTIVE-INDEX AUDIT FAILED ($violations pattern class(es) tripped)."
  echo "Every AubinLionsPackage_R3 consumer must use the effective index κ (φ n);"
  echo "category-(iii) selection facts must derive from AubinLionsPackage_R3.effective_strictMono."
  echo "A legitimate fixed-horizon κ := id site (or the composition lemma's own"
  echo "defining φ_mono use) carries a same-line '-- KAPPA_ID_SITE: <reason>' marker."
  exit 1
fi

echo "KAPPA EFFECTIVE-INDEX AUDIT OK (${#FILES[@]} κ-generic files, no stale bare-index sites)."
