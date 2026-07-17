# Statement card — `LerayHopf.Bochner.timeMollification_exists`

See `docs/statement-gates.md` for the field template and process this card implements.

- **Location:** `LerayHopf/Bochner/TimeMollification.lean:196` (namespace `LerayHopf.Bochner`).
- **Status:** `sorry`, `ALLOW_SORRY`. Outside both capstone cones and outside the release
  import cone (`LerayHopf.Experimental` opt-in only). PR-F3 / SPIKE-1 S1 wall.

## Exact type

```
theorem timeMollification_exists (GT : GelfandTriple) (T : ℝ)
    (uV : ℝ → GT.V) (W : W1pTime GT 2 2 T uV) :
    Nonempty (TimeMollification GT T uV W)
```

## Literature / mathematical content

Existence of a smooth time-mollification of a `W1pTime`-element with **linked**
`L²(V)`/`L²(V')` convergence: `TimeMollification` bundles a family `uᵋ` with (i) `C¹` regularity,
(ii) `uᵋ → uV` in `L²(V)`, and (iii) the derivatives `(uᵋ)' → u'` in `L²(V')` — the two
convergences must come from the *same* mollifying family, not proved separately. Standard
approximation-theory content (Steklov/mollifier averaging), not a single named textbook theorem;
the genuinely missing mathlib pillar is an `eLpNorm`-level Young/Minkowski convolution bound for
Banach-valued curves plus the weak-`V'`-derivative commutation `(ρᵋ ⋆ ιu)' = ρᵋ ⋆ u'` — see the
file's own "Honest status" docstring section for the itemized gap.

**Not exponent-parametric beyond the fixed `W1pTime GT 2 2 T uV` input** (same `2, 2` pin as
`w1pTime_continuous_in_H`, inherited from its caller `lionsMagenes_energy_identity`'s contract,
not independently chosen here) — no adversarial-substitution requirement beyond what that card
already covers.

## Hypothesis mapping

| Lean hypothesis | Role |
|---|---|
| `GT : GelfandTriple` | supplies the ambient `V`, `H`, `V'` and embeddings. |
| `T : ℝ` (no positivity hypothesis in the signature) | the mollification interval endpoint; the construction is over `[0,T]`. |
| `uV : ℝ → GT.V` | the curve being mollified. |
| `W : W1pTime GT 2 2 T uV` | fixes `uV ∈ L²(0,T;V)` and its weak derivative `u' ∈ L²(0,T;V')`, at `p = q = 2`. |

## Consumer / special case

Feeds `lionsMagenes_energy_identity`'s intended proof route (the `TimeMollification` contract is
"fixed by the spike and consumed by" that construction, per the file's own docstring) — itself
also inside `LerayHopf.Experimental`, so this is an internal Stream-D dependency, not a
release-surface consumer.

## Boundary-case checklist

- **Weighted `ℓ²` / spike:** N/A directly — this is an existence-of-approximation claim at the
  fixed `p = q = 2` input, not an exponent-generality claim; the counterexample class that
  falsified `w1pTime_continuous_in_H`'s generic form does not apply here since no generic `p,q`
  is asserted.
- **Noncomplete target:** `GelfandTriple`'s `V`/`H` are Hilbert (complete) by construction.
- **Nonmeasurable perturbation:** N/A — `W1pTime` membership already forces the required
  integrability/measurability on `uV` and its weak derivative.

## Gate separation

- **Elaboration gate:** type-checks; only the proof body is `sorry`.
- **Axiom gate:** `sorry`/`sorryAx` only, no `axiom`/`opaque`.
- **Semantic gate:** this card.
