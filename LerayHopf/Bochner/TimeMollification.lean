/-
# LerayHopf.Bochner.TimeMollification — Stream D / PR-F3 (the S1 pillar)

**Stream:** D (abstract Bochner–Sobolev-in-time / Gelfand triple). **Origin:** SPIKE-1
(`docs/scratch/spike1-lions-magenes-verdict.md`, `LerayHopf/Scratch/LionsMagenesSpike.lean`),
which isolated time-mollification with simultaneous `L²(0,T;V)` / `L²(0,T;V')` convergence
as the ONE genuine from-scratch pillar (S1) underpinning the Lions–Magenes energy identity
and hence `w1pTime_continuous_in_H`.

This file is domain-NEUTRAL: it speaks only about an abstract `GelfandTriple` `V ↪ H ↪ V'`
and a `W1pTime GT 2 2 T uV` element. It does NOT specialize to R3/torus and introduces no
import cycle into either domain closure.

## What this file provides

- `TimeMollification GT T uV W` — the bundled S1 data: smooth-in-time approximants `uᵋ`
  (indexed by `ℕ`), their `V`-valued strong derivatives `(uᵋ)'`, the `C¹` regularity, and the
  two `L²`-convergences `uᵋ → u` in `L²(0,T;V)` (the V-norm form per codex P1) and
  `hToVprime∘ι∘(uᵋ)' → u'` in `L²(0,T;V')`. (So the downstream
  `lionsMagenes_energy_identity` consumes exactly this interface.)
- `timeMollification_of_w1pTime` — the constructor producing a `TimeMollification` from the
  `W1pTime` data.

## Method (the spike's validated decomposition)

The standard Steklov/mollification proof:
- mollify in time, `uᵋ := ρᵋ ⋆ₜ u`, with `ρᵋ` a standard normalized bump; each `uᵋ` is `C¹`
  in `t` valued in `V` with strong derivative `ρᵋ' ⋆ₜ u` (`HasCompactSupport.hasDerivAt_convolution_right`);
- `eLpNorm (uᵋ − u) 2 → 0` via the dense-continuous approximation
  (`MeasureTheory.MemLp.exists_boundedContinuous_eLpNorm_sub_le`, vector-valued — the reason
  this is NOT an interpolation wall) + a Young-type `eLpNorm` bound for the time-convolution
  (`eLpNorm (ρᵋ ⋆ g) ≤ ‖ρᵋ‖₁ · eLpNorm g`) + `convolution_tendsto_right` (pointwise),
  combined by an ε/3 argument;
- the V'-valued derivative commutation `(ρᵋ ⋆ u)' = ρᵋ ⋆ u'` for the *weak* time derivative,
  transported through the repo's CLM machinery (`isWeakTimeDeriv_comp_clm`).

## Honest status (PR-F3)

The structure and the constructor's *wiring* (the assembly that turns the analytic cores into
a `TimeMollification`) are built here, together with the genuinely-provable domain helper
`weaklyRegular_volume_restrict_Icc`. The irreducible analytic core — for which mathlib has the
*pieces* but not the *assembled Banach-valued theorem*, exactly as SPIKE-1 sized — is isolated
as the single local lemma `timeMollification_exists` (the S1 existence claim: smooth
time-mollification with the two *linked* `L²(V)` / `L²(V')` convergences), carrying a precise
`-- ALLOW_SORRY: <blocker>` and a `-- TODO:`. No statement is weakened; no new `axiom`/`opaque`
is introduced. That single core IS the S1 wall the spike flagged as the "days-to-2-weeks"
from-scratch build; everything else (the domain regularity helper, the structure definition,
the constructor wiring) is built around it.

**Why the core is genuinely irreducible in one PR.** mathlib has NO `eLpNorm`/`MemLp`
convolution bound at all (verified against the live cache: `Mathlib/Analysis/Convolution.lean`
provides only the *pointwise* `dist_convolution_le` / `convolution_tendsto_right`; there is no
Young inequality at the `eLpNorm` level for Banach-valued curves, and no
`eLpNorm`-mollification-convergence lemma). Assembling it requires a from-scratch
Minkowski-integral-inequality / Young-for-convolutions build at the `eLpNorm` level PLUS the
weak-`V'`-derivative commutation `(ρᵋ ⋆ ιu)' = ρᵋ ⋆ u'` — exactly the SPIKE-1 S1 scope. This
file lands the wiring and isolates that core soundly rather than papering it over.

## Assumptions

No new `axiom`/`opaque`/`constant`. The single remaining gap (`timeMollification_exists`) is
marked `ALLOW_SORRY` with an exact blocker, NOT converted into an axiom and NOT papered over by
weakening the `TimeMollification` contract (which is fixed by the spike and consumed by
`lionsMagenes_energy_identity`).
-/

import LerayHopf.Bochner.TimeSobolev
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace LerayHopf.Bochner

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal Convolution

/-! ### The S1 data structure (lifted from SPIKE-1)

`TimeMollification` bundles the output of time-mollification of a `W1pTime` curve. It is
stated against the EXISTING `GelfandTriple` / `W1pTime` / `hToVprime` API so that the
downstream `lionsMagenes_energy_identity` (PR-F1) consumes it unchanged. -/

/-- **S1 data: a smooth time-mollification of a `W1pTime` curve** (domain-neutral).

Bundles what time-mollification `uᵋ := ρᵋ ⋆ₜ u` produces, as a sequence indexed by `n` (the
mollification index `ε = εₙ → 0`):
- each `uVeps n` is `C¹` in `t` valued in `V` (so `ι ∘ uVeps n` is `C¹` into `H`), with strong
  `V`-derivative `uVeps' n`;
- `uVeps n → uV` in `L²(0,T;V)` and `hToVprime ∘ ι ∘ uVeps' n → W.u'` in `L²(0,T;V')`.

These two `L²`-convergences are linked by differentiation (the derivative of the mollified
curve is the mollification of the derivative), which is exactly why independent `Lᵖ`-density
of `u` and `u'` does NOT suffice — they must come from the same mollification. -/
structure TimeMollification (GT : GelfandTriple) (T : ℝ) (uV : ℝ → GT.V)
    (W : W1pTime GT 2 2 T uV) where
  /-- The smooth-in-time approximants, valued in `V`. -/
  uVeps : ℕ → ℝ → GT.V
  /-- Their strong `V`-valued time derivatives. -/
  uVeps' : ℕ → ℝ → GT.V
  /-- Each approximant is `C¹` into `V` on the interior, with strong derivative `uVeps'`. -/
  hasDeriv : letI := GT.instNACG_V; letI := GT.instIPS_V;
    ∀ n, ∀ t ∈ Set.Ioo (0:ℝ) T, HasDerivAt (uVeps n) (uVeps' n t) t
  /-- Continuity of the V-valued approximant on `[0,T]`. -/
  cont : letI := GT.instNACG_V; letI := GT.instIPS_V;
    ∀ n, ContinuousOn (uVeps n) (Set.Icc 0 T)
  /-- Continuity of its V-derivative on `[0,T]`. -/
  cont' : letI := GT.instNACG_V; letI := GT.instIPS_V;
    ∀ n, ContinuousOn (uVeps' n) (Set.Icc 0 T)
  /-- `L²(0,T;V)` convergence of the approximant `uVeps n → uV` in the **V-norm**.

  Codex P1 fix: the Lions–Magenes energy-identity RHS is a `V'×V` dual pairing estimated by
  `‖φ‖_{V'}‖v‖_V`, so passing it to the limit needs `uVeps n → uV` in `L²(0,T;V)` (the V-norm),
  not merely in `L²(0,T;H)`. Since `V ↪ H` can be strict/compact, `L²(H)` convergence gives no
  `L²(V)` control. This `L²(V)` form is STRONGER and is what mollification actually delivers; it
  implies the old `L²(H)` form via the continuous embedding `‖ι v‖_H ≤ ‖ι‖·‖v‖_V`. -/
  conv_uV : letI := GT.instNACG_V; letI := GT.instIPS_V;
    Tendsto (fun n => eLpNorm
      (fun t => uVeps n t - uV t) 2 (volume.restrict (Set.Icc 0 T)))
      atTop (𝓝 0)
  /-- `L²(0,T;V')` convergence of the V'-image of the derivative to `W.u'`. -/
  conv_uV' : letI := GT.instNACG_V; letI := GT.instIPS_V;
    Tendsto (fun n => eLpNorm
      (fun t => GT.hToVprime (GT.ι (uVeps' n t)) - W.u' t) 2
      (volume.restrict (Set.Icc 0 T)))
      atTop (𝓝 0)

/-! ### Domain facts: the time interval carries a weakly-regular finite measure

The dense-continuous-in-`Lᵖ` approximation (`MemLp.exists_boundedContinuous_eLpNorm_sub_le`)
needs `[WeaklyRegular μ]`; the Young `eLpNorm` bound needs finiteness. Both hold for
`volume.restrict (Icc 0 T)`. -/

/-- `Icc 0 T` has finite Lebesgue measure, so the restricted measure is weakly regular
(`WeaklyRegular.restrict_of_measure_ne_top`). This is the regularity hypothesis consumed by the
vector-valued dense-continuous-in-`Lᵖ` lemma. -/
theorem weaklyRegular_volume_restrict_Icc (T : ℝ) :
    (volume.restrict (Set.Icc (0:ℝ) T)).WeaklyRegular := by
  have hfin : volume (Set.Icc (0:ℝ) T) ≠ ∞ := by
    rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  exact MeasureTheory.Measure.WeaklyRegular.restrict_of_measure_ne_top hfin

/-! ### The analytic core (the SPIKE-1 S1 wall)

mathlib has the *pieces* but not the assembled Banach-valued theorem. This is the genuine
from-scratch sub-build the spike sized as "days-to-2-weeks", isolated here as a single named
existence lemma so the structure/constructor assembly around it is fully wired; it carries a
precise `ALLOW_SORRY` blocker. No statement is weakened. -/

section AnalyticCores

variable {GT : GelfandTriple} {T : ℝ}

/-- **Analytic core (the SPIKE-1 S1 existence claim).**

This is the single from-scratch pillar: time-mollification of a `W1pTime` curve producing the
full `TimeMollification` data — the smooth approximants, their `V`-derivatives, the `C¹`
regularity, AND the two *linked* `L²`-convergences (in `V` for the curve, in `V'` for the
derivative). The two convergences are NOT independent: the derivative of the mollified curve is
the mollification of the (weak) derivative, which is the whole reason the linked structure is
the right object.

**SPIKE-1 wall (S1).** The standard Steklov/mollification construction is `uᵋ := ρᵋ ⋆ₜ u`:
- *Regularity* (`hasDeriv`/`cont`/`cont'`): from
  `HasCompactSupport.hasDerivAt_convolution_right` (the derivative falls on the smooth bump
  `ρᵋ`, so `(ρᵋ ⋆ u)' = ρᵋ' ⋆ u` is continuous) — mathlib HAS this.
- *`L²(V)` convergence* (`conv_uV`): mathlib HAS the vector-valued continuous-dense-in-`Lᵖ`
  lemma (`MemLp.exists_boundedContinuous_eLpNorm_sub_le`), the pointwise mollification
  convergence (`ContDiffBump.convolution_tendsto_right`), and the Young `eLpNorm` bound shape
  (`‖∫ h, ρ(h) • τ_h g‖ ≤ ‖g‖`, cf. the proved `FrechetKolmogorov.convL2_norm_le`), but NOT
  the assembled `eLpNorm (ρᵋ ⋆ g − g) → 0` theorem for Banach-valued curves — the ε/3 argument
  must be built.
- *`L²(V')` convergence* (`conv_uV'`): same `eLpNorm`-mollification convergence applied to
  `u'`, combined with the *weak-derivative commutation* `(ρᵋ ⋆ ιu)' = ρᵋ ⋆ u'` in `V'`
  (transported through `isWeakTimeDeriv_comp_clm` / `hToVprimeCLM`) so that the V'-image of the
  derivative `hToVprime (ι (ρᵋ' ⋆ u))` equals `ρᵋ ⋆ u'`, whose `eLpNorm`-convergence to `u'`
  is again core S1. mathlib packages the strong (`HasFDerivAt`) convolution-derivative but NOT
  the weak `V'`-valued commutation.

Both missing pieces are the SPIKE-1 "days-to-2-weeks" from-scratch sub-build. They are isolated
in this single existence lemma; the constructor below wires it into a `TimeMollification`. No
statement is weakened, no axiom introduced. -/
-- TODO (PR-F3 S1): build `uᵋ := ρᵋ ⋆ₜ u` and discharge the four field obligations:
--   (regularity) `HasCompactSupport.hasDerivAt_convolution_right` + bump `ContDiff`;
--   (conv_uV)  ε/3 from `MemLp.exists_boundedContinuous_eLpNorm_sub_le` (vector-valued,
--              `weaklyRegular_volume_restrict_Icc`) + Young `eLpNorm` bound +
--              `ContDiffBump.convolution_tendsto_right`;
--   (conv_uV') same `eLpNorm`-convergence on `u'` + weak-derivative commutation
--              `(ρᵋ ⋆ ιu)' = ρᵋ ⋆ u'` via `isWeakTimeDeriv_comp_clm` / `hToVprimeCLM`.
--   mathlib has every piece but not the assembled Banach-valued `eLpNorm`-mollification
--   theorem nor the weak-`V'`-derivative commutation (SPIKE-1 §S1).
theorem timeMollification_exists (GT : GelfandTriple) (T : ℝ)
    (uV : ℝ → GT.V) (W : W1pTime GT 2 2 T uV) :
    Nonempty (TimeMollification GT T uV W) := by
  sorry -- ALLOW_SORRY: PR-F3 S1 — production of the TimeMollification data (smooth time-mollification with LINKED L²(V)/L²(V') convergence, the V-norm form per codex P1). The from-scratch wall is the INTERVAL Steklov assembly: mathlib's whole-line tools (HasCompactSupport.hasDerivAt_convolution_right for the C¹ regularity, MemLp.exists_boundedContinuous_eLpNorm_sub_le for vector-valued continuous-density, ContDiffBump.convolution_tendsto_right for pointwise convergence, and the ‖∫‖≤∫‖·‖ Young shape proved at the Lp-element level in FrechetKolmogorov.convL2_norm_le) do NOT transport to [0,T] because time-translation does not preserve the interval and zero-extension injects boundary jumps into the weak V'-derivative; the genuine sub-build is (i) the interval-boundary Steklov construction giving approximants with the C¹ link uVeps'=(uVeps)' intact, (ii) the assembled eLpNorm-mollification convergence eLpNorm(ρᵋ⋆g−g)2→0 for a V/V'-valued curve, and (iii) the weak-V'-derivative commutation (ρᵋ⋆ιu)'=ρᵋ⋆u' via isWeakTimeDeriv_comp_clm/hToVprimeCLM. SPIKE-1 S1 wall (days-to-2-weeks, none of it assembled in mathlib).

end AnalyticCores

/-! ### The constructor

`timeMollification_of_w1pTime` produces a `TimeMollification` from the `W1pTime` data, by
choosing a representative of the S1 existence claim. This is the public entry point consumed by
PR-F1 (`lionsMagenes_energy_identity`). -/

/-- **Constructor: produce the time-mollification data from a `W1pTime` element.**

Given `W : W1pTime GT 2 2 T uV` (i.e. `uV ∈ L²(0,T;V)` with `V'`-valued weak derivative
`u' ∈ L²(0,T;V')`), construct the bundled `TimeMollification` data: the smooth-in-time
approximants `uᵋ := ρᵋ ⋆ₜ u`, their `V`-derivatives, the `C¹` regularity, and the two linked
`L²`-convergences. This is the producing form of the S1 pillar (the spike took the
`TimeMollification` as a hypothesis only to isolate S1 for sizing; here it is produced).

The body selects a representative of `timeMollification_exists` (the isolated S1 wall). -/
noncomputable def timeMollification_of_w1pTime (GT : GelfandTriple) (T : ℝ)
    (uV : ℝ → GT.V) (W : W1pTime GT 2 2 T uV) :
    TimeMollification GT T uV W :=
  (timeMollification_exists GT T uV W).some

end LerayHopf.Bochner
