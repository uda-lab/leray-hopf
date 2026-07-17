# Statement card — `LerayHopf.Bochner.weakTimeDerivℝ_even_reflection`

See `docs/statement-gates.md` for the field template and process this card implements. The
filename matches the declaration name verbatim (including the `ℝ`), so
`scripts/check-statement-cards.sh` can look it up mechanically.

- **Location:** `LerayHopf/Bochner/TimeMollifierInterval.lean:466` (namespace
  `LerayHopf.Bochner`; Wall B1 of the S1 design, `docs/scratch/s1-walls-design.md` §2b).
- **Status:** `sorry`, `ALLOW_SORRY`. Outside both capstone cones and outside the release
  import cone. **Same months-class pillar as `w1pTime_continuous_in_H`** — see that card and
  the postmortem doc; this is not an independent difficulty, it shares the missing mathlib
  pillar (Bochner-valued 1D-Sobolev FTC / continuous-representative trace at `0`).

## Exact type

```
theorem weakTimeDerivℝ_even_reflection (u v : ℝ → X)
    (hu : LocallyIntegrable u (volume : Measure ℝ))
    (hv : LocallyIntegrable v (volume : Measure ℝ))
    (hwd : IsWeakTimeDerivℝ u v) :
    IsWeakTimeDerivℝ (fun t => u |t|) (fun t => Real.sign t • v |t|)
```

## Literature / mathematical content

Even reflection of a whole-line weak time derivative: if `v` is the weak derivative of `u` on
all of `ℝ`, then `u ∘ |·|` (the even reflection of `u`) has weak derivative
`Real.sign · (v ∘ |·|)`, with **no Dirac mass** at the reflection point `0`. This is the
standard "no jump if the trace agrees" fact from distribution theory — not a single named
textbook theorem; the genuine content is that reflection introduces no boundary Dirac term
precisely because there is no jump in the trace value at `0` (the two half-axis limits from `u`
must actually agree, which requires the trace to exist at all — the Bochner FTC pillar).

**Not exponent-parametric** — no `p, q` binders; the adversarial-substitution requirement does
not independently apply, but the underlying missing pillar is shared with the
exponent-parametric case that DID need it (`w1pTime_continuous_in_H`).

## Hypothesis mapping

| Lean hypothesis | Role |
|---|---|
| `u v : ℝ → X` | the whole-line curve and its claimed weak derivative. |
| `hu`, `hv : LocallyIntegrable` | needed so the Bochner integrals in `IsWeakTimeDerivℝ` are not junk, and so the half-axis split `∫_ℝ = ∫_{<0} + ∫_{>0}` is sound (Fubini/DCT needs at least local integrability). **Added during the corrected blocker analysis** — without these, a caller could assert the no-Dirac identity for arbitrary measurable curves, smuggling the circular trace assumption with no integrability control (a no-smuggle fix, analogous in spirit to the E1 measurability fix documented in `docs/STATUS.md`'s Stream D row). |
| `hwd : IsWeakTimeDerivℝ u v` | the whole-line weak-derivative hypothesis being reflected. |

## Consumer / special case

Feeds `w1pTime_lineExtension` (Wall B assembly, same file, blocked transitively on this
declaration) — an internal Stream-D dependency, not a release-surface consumer.

## Boundary-case checklist

- **Weighted `ℓ²` / spike:** N/A directly (no exponent parameter on this declaration), but the
  underlying blocker is the same trace/FTC pillar that the `p = q = 1` weighted-`ℓ²`
  counterexample exploits for `w1pTime_continuous_in_H` — a reader auditing this declaration
  should read that card and the postmortem together.
- **Noncomplete target:** `X` requires `[NormedAddCommGroup X] [NormedSpace ℝ X]` per the
  section variable at the top of the relevant block in `TimeMollifierInterval.lean`; consult
  the source for the exact completeness assumption in force at this declaration.
- **Nonmeasurable perturbation:** N/A — `hu`/`hv` already force local integrability, which
  implies (strong) measurability.

## Gate separation

- **Elaboration gate:** type-checks; only the proof body is `sorry`.
- **Axiom gate:** `sorry`/`sorryAx` only, no `axiom`/`opaque`.
- **Semantic gate:** this card. The declaration's own inline comment states "Statement is TRUE
  (a.e.-invariant; holds for the continuous representative), not weakened" — i.e. this is a
  genuinely true statement blocked on a missing proof pillar, not a suspected false statement
  like the original `w1pTime_continuous_in_H`. Flagged here for ledger completeness, and because
  any future attempt to "unblock" it by weakening `hwd` or dropping `hu`/`hv` should be treated
  as a semantic-gate event requiring review, not a routine strengthening.
