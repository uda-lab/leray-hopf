/-
# LerayHopf.Bochner.TimeSobolevExperimental — the quarantined D1 embedding (issue #147)

**Extracted from `TimeSobolev.lean`** so the release surface `import LerayHopf` stays
sorry-free (issue #147). This file holds exactly one declaration: `w1pTime_continuous_in_H`,
the Lions–Magenes good-representative embedding `W^{1,p}(0,T;V) ∩ L^q(0,T;V') ↪ C([0,T];H)`.

Nothing in the release closure imports this file. `LerayHopf/Torus/TraceEnergy.lean` already
documented `w1pTime_continuous_in_H` as intentionally quarantined before this split (it names
no import of `TimeSobolev*.lean`); the two root-closure consumers of `TimeSobolev.lean`
(`R3/AubinLionsLimitPassage.lean`, `R3/EnergyWeakLsc.lean`) use only `kineticEnergy_lsc_transfer`
(Stage D2, declared after this theorem in the original file and structurally independent of it)
and are unaffected by this extraction. See `LerayHopf/Experimental.lean` for the aggregator
and the full list of what remains incomplete.

## Status

`w1pTime_continuous_in_H` — declared MONTHS-CLASS residual (contract §2 / §7); statement kept
intact, body deferred. This is the deepest single theorem of Stream D: the "weakly-continuous
good representative" that `galerkin_limit_passage*` defers, needing the vector-valued
time-Sobolev / Bochner-time good-representative pillar (missing from mathlib).

## Assumptions

No new `axiom`/`opaque`/`constant`.
-/

import LerayHopf.Bochner.TimeSobolev

namespace LerayHopf.Bochner

open MeasureTheory Filter Topology
open scoped ENNReal

/-- **Lions–Magenes good-representative embedding.** A `W^{1,p}(0,T;V) ∩ L^q(0,T;V')`
element has a representative that is continuous into `H`: there is `ũ : ℝ → H`, continuous
on `[0,T]`, agreeing a.e. with the `H`-valued image curve `t ↦ ι (uV t)`.

This is the deepest single theorem of Stream D — exactly the "weakly-continuous good
representative" that `galerkin_limit_passage*` defers — and it is a declared MONTHS-CLASS
residual. The statement is the genuine Lions–Magenes form (continuous, not merely
weakly-continuous; can be refined to `C_w` later) and is kept intact. Note this uses the
FULL strength of the Gelfand triple: `u ∈ L^p(·;V)` and `u' ∈ L^q(·;V')` (the genuine
`V'`-valued derivative carried by `W`) together yield continuity into the pivot `H`.

**Scaffold-only this cycle** (months-class). -/
theorem w1pTime_continuous_in_H (GT : GelfandTriple) {p q : ℝ≥0∞} {T : ℝ} (hT : 0 < T)
    (hpq : 1 ≤ p ∧ 1 ≤ q) {uV : ℝ → GT.V} (W : W1pTime GT p q T uV) :
    letI := GT.instNACG_V; letI := GT.instIPS_V;
    letI := GT.instNACG_H; letI := GT.instIPS_H;
    ∃ ũ : ℝ → GT.H, ContinuousOn ũ (Set.Icc 0 T) ∧
      ũ =ᵐ[volume.restrict (Set.Icc 0 T)] (fun t => GT.ι (uV t)) := by
  -- TODO: Lions–Magenes embedding `W^{1,p}(0,T;V) ∩ L^q(0,T;V') ↪ C([0,T];H)`.
  -- Missing mathlib pillar: vector-valued time-Sobolev / Bochner-time good-representative
  -- theory (the same pillar behind axiom `galerkin_limit_passage*`). MONTHS-CLASS residual,
  -- deferred this cycle per contract §2 (D1 embedding) / §7 DoD.
  sorry -- ALLOW_SORRY: D1 Lions–Magenes good-representative embedding — declared MONTHS-CLASS residual (contract §2 / §7); statement kept intact, body deferred.

end LerayHopf.Bochner
