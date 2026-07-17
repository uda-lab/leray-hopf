# Statement card — `LerayHopf.Bochner.isWeakTimeDeriv_primitive`

See `docs/statement-gates.md` for the field template and process this card implements.

- **Location:** `LerayHopf/Bochner/TimeSobolevAC.lean:322` (namespace `LerayHopf.Bochner`).
- **Status:** `sorry`, `ALLOW_SORRY`. Outside both capstone cones and outside the release
  import cone (`LerayHopf.Experimental` opt-in only). Isolated as the single residual of the
  R1 (trace-free good-representative) layer — everything else in that layer is proved.

## Exact type

```
theorem isWeakTimeDeriv_primitive {T : ℝ} (hT : 0 < T) {v : ℝ → X}
    (hv : IntegrableOn v (Set.Icc 0 T) volume) :
    IsWeakTimeDeriv T (fun t => ∫ s in (0:ℝ)..t, v s) v
```

`X` is an arbitrary complete normed `ℝ`-vector space (`variable {X : Type*} [NormedAddCommGroup X]
[NormedSpace ℝ X] [CompleteSpace X]`), i.e. this is domain-neutral (serves both `V` and `V'`).

## Literature / mathematical content

The Bochner-valued distributional fundamental theorem of calculus: the Bochner primitive
`w(t) := ∫₀ᵗ v` of an interval-integrable curve `v` has `v` as its weak time derivative on
`(0,T)`. Not a named theorem in a specific textbook edition — this is the standard scalar FTC
(`intervalIntegral.integral_hasDerivAt` / `deriv_integral` family in mathlib) lifted to the
distributional/Bochner setting via a Fubini swap
(`∫ ψ'(t)·(∫₀ᵗ v) = ∫ v(s)·(ψ(T) − ψ(s)) = −∫ ψ(s)·v(s)` using the test function's `ψ(T) = 0`
boundary condition). mathlib has the Fubini swap
(`MeasureTheory.integral_integral_swap`) and the scalar FTC as separate pieces but not this
assembled interval form for a Banach-valued primitive.

**Not exponent-parametric** — no `p, q` binders, so the issue #158 adversarial-substitution
requirement does not apply to this declaration.

## Hypothesis mapping

| Lean hypothesis | Role |
|---|---|
| `hT : 0 < T` | nonempty interval, needed for `(0,T)` to be non-vacuous. |
| `hv : IntegrableOn v (Set.Icc 0 T) volume` | the only integrability assumed on `v`; forces the primitive `w` to be well-defined and the Fubini swap to be justified. |

Trace-free and non-circular by construction: no reflection, no boundary value of `v` is fed in
as a hypothesis (unlike `weakTimeDerivℝ_even_reflection`, which genuinely needs a trace and is
blocked on this declaration's sibling pillar, not this one).

## Consumer / special case

Feeds the R1 "trace-free good representative" layer in `TimeSobolevAC.lean`; not consumer-facing
from outside `LerayHopf.Experimental` (the whole file is opt-in, outside the release cone).

## Boundary-case checklist

- **Weighted `ℓ²` / spike:** N/A — this is a scalar-primitive FTC statement, not an
  exponent-compatibility claim; the `p = q = 1` counterexample class does not apply (no dual
  pairing appears in this statement).
- **Noncomplete target:** covered by `[CompleteSpace X]`, required for the Bochner integral to
  be well-defined at all.
- **Nonmeasurable perturbation:** N/A — `hv : IntegrableOn` already forces measurability.

## Gate separation

- **Elaboration gate:** type-checks; only the proof body is `sorry`.
- **Axiom gate:** `sorry`/`sorryAx` only, no `axiom`/`opaque`.
- **Semantic gate:** this card; no exponent-parametric surface to regress, so no dedicated
  `check-statement-cards.sh` signature guard beyond the blanket "card exists" check.
