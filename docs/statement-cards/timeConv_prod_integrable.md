# Statement card — `LerayHopf.Bochner.timeConv_prod_integrable`

See `docs/statement-gates.md` for the field template and process this card implements.

- **Location:** `LerayHopf/Bochner/TimeMollifierInterval.lean:297` (namespace
  `LerayHopf.Bochner`, `private` helper).
- **Status:** `sorry`, `ALLOW_SORRY`. Outside both capstone cones and outside the release
  import cone. Explicitly marked **not soundness-critical** by its own docstring: it is a
  Fubini side-condition, not the commutation identity itself (which is proved unconditionally).

## Exact type

```
private theorem timeConv_prod_integrable {a ρ : ℝ → ℝ}
    (ha_cont : Continuous a) (ha_cs : HasCompactSupport a)
    (hρ : IsTimeMollifier ρ) {w : ℝ → X} (hw : LocallyIntegrable w (volume : Measure ℝ)) :
    Integrable (Function.uncurry fun t s => a t • ρ s • w (t - s))
      ((volume : Measure ℝ).prod (volume : Measure ℝ))
```

## Literature / mathematical content

A standard compact-box `L¹` estimate: the product integrand `(t,s) ↦ a(t)·ρ(s)·w(t−s)` is
integrable on `ℝ × ℝ` because it is supported in the compact set `tsupport a × tsupport ρ`
(after the change of variables) and bounded there by
`|ρ(s)|·‖a‖_∞·∫_{tsupport a − tsupport ρ} ‖w‖`. Elementary domination argument, not a named
theorem; no literature citation needed beyond "dominated convergence / compact-support bound".

## Hypothesis mapping

| Lean hypothesis | Role |
|---|---|
| `ha_cont : Continuous a` | needed for `a` to be a.e.-strongly-measurable and to have a well-defined `tsupport`. |
| `ha_cs : HasCompactSupport a` | the compactness that makes the outer `s`-integral finite. |
| `hρ : IsTimeMollifier ρ` | `ρ` is a compactly-supported, integrable mollifying kernel. |
| `hw : LocallyIntegrable w (volume : Measure ℝ)` | integrability of `w`, needed for the slice integrals to be well-defined (see `timeConv_slice_integrable`, the sibling proved lemma). |

## Consumer / special case

Internal `private` helper for `timeConvL2_weakDeriv_comm` (WALL A) in the same file; not exposed
outside `TimeMollifierInterval.lean`. WALL A's soundness-critical commutation identity is proved
unconditionally without depending on the *value* of this estimate — only its existence as a
Fubini side-condition (per the file's own docstring).

## Boundary-case checklist

- **Weighted `ℓ²` / spike:** N/A — this is a compact-support integrability bound with no
  exponent parameter; not in the class of statements the `p = q = 1` counterexample targets.
- **Noncomplete target:** `X` inherits `TimeMollifierInterval.lean`'s ambient normed-space
  section variable (complete, per the file's `[CompleteSpace X]` variable).
- **Nonmeasurable perturbation:** N/A — `hw` already supplies the needed measurability.

## Gate separation

- **Elaboration gate:** type-checks; only the proof body is `sorry`.
- **Axiom gate:** `sorry`/`sorryAx` only, no `axiom`/`opaque`.
- **Semantic gate:** this card. Marked explicitly non-soundness-critical by the surrounding
  code's own comments — flagged here for completeness (ledger completeness per issue #158),
  not because it is suspected of a statement defect.
