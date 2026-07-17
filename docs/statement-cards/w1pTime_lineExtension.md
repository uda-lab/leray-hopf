# Statement card — `LerayHopf.Bochner.w1pTime_lineExtension`

See `docs/statement-gates.md` for the field template and process this card implements.

- **Location:** `LerayHopf/Bochner/TimeMollifierInterval.lean:601` (namespace
  `LerayHopf.Bochner`; Wall B assembly of the S1 design, `docs/scratch/s1-walls-design.md` §2d).
- **Status:** `sorry`, `ALLOW_SORRY`. Outside both capstone cones and outside the release
  import cone. **Blocked transitively on `weakTimeDerivℝ_even_reflection` (Wall B1)** — see that
  card; the glue pieces this declaration itself needs beyond B1
  (`isWeakTimeDerivℝ_smul_cutoff`, `isWeakTimeDerivℝ_comp_clm`) are already PROVED.

## Exact type

```
theorem w1pTime_lineExtension (GT : GelfandTriple) {T : ℝ} (hT : 0 < T)
    {uV : ℝ → GT.V} (W : W1pTime GT 2 2 T uV) :
    ∃ (ūV : ℝ → GT.V) (ū' : ℝ → GT.Vprime),
      ūV =ᵐ[volume.restrict (Set.Icc 0 T)] uV ∧
      MemLp ūV 2 (volume : Measure ℝ) ∧
      ū' =ᵐ[volume.restrict (Set.Icc 0 T)] W.u' ∧
      MemLp ū' 2 (volume : Measure ℝ) ∧
      IsWeakTimeDerivℝ (X := GT.Vprime) (fun t => GT.hToVprime (GT.ι (ūV t))) ū'
```

(`letI` instance lines eliding `V`/`H` norm/inner-product structure omitted; see the source.)

## Literature / mathematical content

The `W1pTime`-preserving whole-line extension of a curve on `[0,T]`: given `uV ∈ L²(0,T;V)` with
weak `V'`-derivative `W.u'`, produce a whole-line curve `ūV` agreeing with `uV` a.e. on `[0,T]`,
in `L²(V)`, whose (whole-line, `IsWeakTimeDerivℝ`) weak derivative `ū'` agrees with `W.u'` a.e.
on `[0,T]` and is in `L²(V')`. Standard Sobolev-extension technique (double even reflection at
both endpoints `× ` compact cutoff), not a single named theorem — the assembly step, not new
mathematical content beyond B1 + the two proved glue lemmas.

**Not exponent-parametric** — no independent `p, q` binders beyond the `W1pTime GT 2 2 T uV`
input inherited from the caller's contract.

## Hypothesis mapping

| Lean hypothesis | Role |
|---|---|
| `GT : GelfandTriple` | supplies `V`, `H`, `V'`/`Vprime` and the embeddings. |
| `hT : 0 < T` | nonempty interval. |
| `uV : ℝ → GT.V` | the curve to extend. |
| `W : W1pTime GT 2 2 T uV` | fixes `uV`'s `L²(V)` membership and its weak `V'`-derivative, at `p = q = 2`. |

## Consumer / special case

Assembles the extension used by the surrounding `TimeMollifierInterval` machinery (feeds the
whole-line mollification route back down to the interval `[0,T]`); an internal Stream-D
dependency, not a release-surface consumer.

## Boundary-case checklist

- **Weighted `ℓ²` / spike:** N/A directly, but inherits B1's blocker (same trace/FTC pillar the
  `p = q = 1` counterexample exploits for `w1pTime_continuous_in_H`).
- **Double-endpoint reflection (this declaration's own genuine wall, distinct from B1):** a
  single even reflection at `0` only controls `uV` on `[0,∞)`, but `W.mem_p` only supplies
  control on `[0,T]`; the correct extension reflects at BOTH `0` and `T` so the cutoff support
  stays within the controlled range. This is called out explicitly in the source docstring as
  "contained but non-trivial" — recorded here so it is not lost if B1 lands and this declaration
  is revisited.
- **Noncomplete target:** `GelfandTriple`'s `V`/`H` are Hilbert (complete) by construction.
- **Nonmeasurable perturbation:** N/A — `W1pTime` membership already forces the needed
  integrability/measurability.

## Gate separation

- **Elaboration gate:** type-checks; only the proof body is `sorry`.
- **Axiom gate:** `sorry`/`sorryAx` only, no `axiom`/`opaque`.
- **Semantic gate:** this card. Source docstring states "the statement ... is kept fully intact
  and no axiom is introduced" — a true, unweakened statement blocked on B1 plus its own
  double-endpoint bookkeeping, not a suspected false statement.
