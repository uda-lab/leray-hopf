/-
# LerayHopf.Bochner.TimeSobolevExperimental — the quarantined D1 embedding (issues #147, #158)

**Extracted from `TimeSobolev.lean`** so the release surface `import LerayHopf` stays
sorry-free (issue #147). This file holds exactly one declaration: `w1pTime_continuous_in_H`,
the Lions–Magenes good-representative embedding, **restricted to the `p = q = 2` case**
(issue #158 — see below).

Nothing in the release closure imports this file. `LerayHopf/Torus/TraceEnergy.lean` already
documented `w1pTime_continuous_in_H` as intentionally quarantined before this split (it names
no import of `TimeSobolev*.lean`); the two root-closure consumers of `TimeSobolev.lean`
(`R3/AubinLionsLimitPassage.lean`, `R3/EnergyWeakLsc.lean`) use only `kineticEnergy_lsc_transfer`
(Stage D2, declared after this theorem in the original file and structurally independent of it)
and are unaffected by this extraction. See `LerayHopf/Experimental.lean` for the aggregator
and the full list of what remains incomplete.

## Status (corrected by issue #158)

`w1pTime_continuous_in_H` — declared MONTHS-CLASS residual (contract §2 / §7); body deferred.

**The statement was corrected, not just relocated.** The prior generic-exponent form
(`{p q : ℝ≥0∞} (hpq : 1 ≤ p ∧ 1 ≤ q)`) is FALSE: issue #158 gives an explicit weighted-`ℓ²`
counterexample at `p = q = 1` — separate `L¹` integrability of `u` and `u'` does not make the
dual pairing `⟨u'(t), u(t)⟩` integrable, which the standard proof route needs (via Hölder,
typically a conjugate-exponent or reciprocal-exponent compatibility), and an `H`-continuous
a.e. representative need not exist. The only case ever actually analyzed (the issue #4
Lions–Magenes proof spike, using Cauchy–Schwarz on `L²(V') × L²(V)`) is `p = q = 2`, so this
declaration is now restricted to exactly that case — the minimal safe fix issue #158
recommends. A generic-exponent version, if ever wanted, needs its own exact exponent
compatibility condition and literature citation before being restated as public API; that is
out of scope here and tracked in #158 for the notes/site follow-up.

## Assumptions

No new `axiom`/`opaque`/`constant`.
-/

import LerayHopf.Bochner.TimeSobolev

namespace LerayHopf.Bochner

open MeasureTheory Filter Topology
open scoped ENNReal

/-- **Lions–Magenes good-representative embedding, `p = q = 2` case (issue #158).**
A `W^{1,2}(0,T;V) ∩ L^2(0,T;V')` element has a representative that is continuous into `H`:
there is `ũ : ℝ → H`, continuous on `[0,T]`, agreeing a.e. with the `H`-valued image curve
`t ↦ ι (uV t)`.

This is the deepest single theorem of Stream D — exactly the "weakly-continuous good
representative" that `galerkin_limit_passage*` defers — and it is a declared MONTHS-CLASS
residual. **Restricted to `p = q = 2`, the only case with an actual proof plan** (the issue #4
spike uses Cauchy–Schwarz on the dual pairing `⟨u', u⟩`, valid at `L²(V') × L²(V)`); the prior
generic-`p,q` form was FALSE (issue #158, explicit `p = q = 1` counterexample) and is not
restated here. Note this uses the FULL strength of the Gelfand triple: `u ∈ L²(·;V)` and
`u' ∈ L²(·;V')` (the genuine `V'`-valued derivative carried by `W`) together are meant to
yield continuity into the pivot `H` — the dual-pairing integrability that argument needs holds
at `p = q = 2` by Cauchy–Schwarz.

**Scaffold-only** (months-class, genuinely incomplete). -/
theorem w1pTime_continuous_in_H (GT : GelfandTriple) {T : ℝ} (hT : 0 < T)
    {uV : ℝ → GT.V} (W : W1pTime GT 2 2 T uV) :
    letI := GT.instNACG_V; letI := GT.instIPS_V;
    letI := GT.instNACG_H; letI := GT.instIPS_H;
    ∃ ũ : ℝ → GT.H, ContinuousOn ũ (Set.Icc 0 T) ∧
      ũ =ᵐ[volume.restrict (Set.Icc 0 T)] (fun t => GT.ι (uV t)) := by
  -- TODO: Lions–Magenes embedding `W^{1,2}(0,T;V) ∩ L^2(0,T;V') ↪ C([0,T];H)`.
  -- Missing mathlib pillar: vector-valued time-Sobolev / Bochner-time good-representative
  -- theory (the same pillar behind axiom `galerkin_limit_passage*`). MONTHS-CLASS residual,
  -- deferred (D1 embedding); see the file docstring "Status" section.
  sorry -- ALLOW_SORRY: D1 Lions–Magenes good-representative embedding, p=q=2 case (issue #158 correction) — declared MONTHS-CLASS residual (contract §2 / §7); body deferred.

end LerayHopf.Bochner
