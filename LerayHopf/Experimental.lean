/-
# LerayHopf.Experimental — incomplete Bochner time-layer work (issues #147, #158)

**Explicit opt-in.** `import LerayHopf` (the release surface) does NOT reach this file or
anything it imports; nothing in the release cone depends on it either. `import
LerayHopf.Experimental` is how a reader deliberately pulls in Stream D's still-incomplete
Bochner/Sobolev-in-time development. `scripts/check-release-cone.sh` fails CI if the release
cone (the transitive closure of `LerayHopf.lean`) ever picks up a `sorry` from here — see
`LerayHopf.lean`'s "Import surface structure" section.

## What is incomplete here (six `sorry`s across four modules)

- **`LerayHopf.Bochner.TimeSobolevExperimental`** — `w1pTime_continuous_in_H`, the
  Lions–Magenes good-representative embedding, **restricted to `p = q = 2`**
  (`W^{1,2}(0,T;V) ∩ L^2(0,T;V') ↪ C([0,T];H)`; issue #158). The prior generic-`p,q` form
  (`1 ≤ p ∧ 1 ≤ q`) was FALSE — issue #158 gives an explicit weighted-`ℓ²` counterexample at
  `p = q = 1` — so this is not merely a relocation but a statement correction: only the case
  with an actual proof plan (Cauchy–Schwarz on the dual pairing at `L²(V') × L²(V)`) is
  stated. Declared MONTHS-CLASS residual (contract §2 / §7): body deferred. This is the
  deepest single theorem of Stream D — the "weakly-continuous good representative" that
  `galerkin_limit_passage*` defers. Extracted from `TimeSobolev.lean` (which stays in the
  release cone, sorry-free) because nothing else in the closure depends on it.

- **`LerayHopf.Bochner.TimeSobolevAC`** — 1 `sorry`: the Bochner–Fubini distributional FTC for
  the primitive `w(t) = ∫₀ᵗ v`. The identity `∫ψ'(t)•(∫₀ᵗ v) = -∫ψ•v` is a Fubini swap that
  mathlib has the ingredients for (`integral_integral_swap`, the scalar FTC) but not this
  assembled interval form. Trace-free and non-circular (no reflection, no boundary value of `v`
  fed in); isolated as the single residual of the R1 (trace-free good-representative) layer.

- **`LerayHopf.Bochner.TimeMollification`** — 1 `sorry`: production of the `TimeMollification`
  data (smooth time-mollification with LINKED `L²(V)`/`L²(V')` convergence). The from-scratch
  wall is the INTERVAL Steklov assembly: mathlib's whole-line convolution/convergence tools do
  not transport to `[0,T]` because time-translation does not preserve the interval and
  zero-extension injects boundary jumps into the weak `V'`-derivative. SPIKE-1 S1 wall
  (estimated days-to-2-weeks; none of it assembled in mathlib).

- **`LerayHopf.Bochner.TimeMollifierInterval`** — 3 `sorry`s:
  1. A Fubini side-condition (compact-box L¹ bound) in the private helper
     `timeConv_prod_integrable` — a standard box estimate, not soundness-critical; the
     commutation identity itself is proved unconditionally.
  2. `weakTimeDerivℝ_even_reflection` (Wall B1) — the even-reflection no-Dirac identity.
     Genuine blocker: needs the Bochner-valued 1D-Sobolev FTC / continuous-representative
     (trace at `0`) pillar — the same months-class residual as `w1pTime_continuous_in_H`.
  3. `w1pTime_lineExtension` (Wall B assembly) — blocked transitively on (2): no sound
     reflected-derivative witness is constructible until B1 lands. The glue pieces (B2
     `isWeakTimeDerivℝ_smul_cutoff`, `isWeakTimeDerivℝ_comp_clm`) are proved.

All six carry a same-line `-- ALLOW_SORRY:` marker (see `scripts/check-no-sorry.sh`); this
file's job is to keep them out of the public release surface, not to relax that discipline.
-/

import LerayHopf.Bochner.TimeSobolevExperimental
import LerayHopf.Bochner.TimeSobolevAC
import LerayHopf.Bochner.TimeMollification
import LerayHopf.Bochner.TimeMollifierInterval
