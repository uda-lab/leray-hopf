# SPIKE-1 verdict — Lions–Magenes AC energy identity

**Scratch:** `LerayHopf/Scratch/LionsMagenesSpike.lean` (`-- SCRATCH`, not for merge).
**Build:** `flock /tmp/lean-build.lock lake build LerayHopf.Scratch.LionsMagenesSpike` → **green**
(2996 jobs, one walled `sorry` at line 209 + the `TimeMollification` data structure).

## VERDICT: **GO** (bounded build, not an interpolation wall)

The Lions–Magenes energy identity is provable from the **existing repo API + mathlib**, with one
genuine from-scratch sub-build (time-mollification with `Lᵖ`-norm convergence). It does **NOT**
require the full `[H,V']` real-interpolation theory built from scratch, and it needs **no extra
hypothesis** beyond what `W1pTime GT 2 2 T uV` already carries (no `AEStronglyMeasurable` gate —
`MemLp` in `W1pTime.mem_p/mem_q` already supplies measurability, unlike the D2 case).

The claim is provable as stated. The route below closes the AC + duality-pairing identity; the
continuous-in-`H` representative `w1pTime_continuous_in_H` then follows by FTC-1 on the AC scalar
plus a standard Cauchy-in-`H` argument (PR-F2, on top of this).

## What COMPILED sorry-free in the spike (against the real API)

1. **`dualPairing_hToVprime_eq_innerH`** — the S2 pairing kernel:
   `⟪hToVprime (ι w), v⟫_{V',V} = ⟪ι v, ι w⟫_H`. Closes by `hToVprime`'s definition +
   `InnerProductSpace.toDual_apply_apply` + `real_inner_comm`. This is the bridge that turns the
   `H`-stated smooth product rule into the `V'`–`V` form. **Fully proved.**
2. **`smooth_energy_identity`** — the S2 smooth-case FTC identity:
   `½‖f b‖²_H − ½‖f a‖²_H = ∫ₐᵇ ⟪f' t, f t⟫_H` for a `C¹`-into-`H` curve `f` with `H`-derivative
   `f'` (continuous `f, f'`). Closes by `HasDerivAt.inner` (the real product rule) +
   `real_inner_self_eq_norm_sq` + `intervalIntegral.integral_eq_sub_of_hasDerivAt`, with
   integrability from `continuous_inner.comp_continuousOn`. **Fully proved** — confirms S2 is
   mechanical mathlib calculus, NOT a wall.

## What is WALLED, and its precise scope

### S1 — time-mollification with simultaneous `L²(V)` / `L²(V')` convergence (the real wall)

Isolated as the `TimeMollification` data structure (the from-scratch existence claim). To produce
it one mollifies in time, `uᵋ := ρᵋ ⋆ₜ u`, and needs:
- each `uᵋ` is `C¹` in `t` valued in `V`, with strong derivative `(uᵋ)' = ρᵋ ⋆ₜ u'`
  (mollification commutes with the weak derivative — this is why independent `Lᵖ`-density of `u`
  and `u'` does NOT suffice; the two approximants must be linked by differentiation);
- `ι(uᵋ) → ι(u)` in `L²(0,T;H)` and `hToVprime(ι((uᵋ)')) → u'` in `L²(0,T;V')`.

**mathlib has the pieces but not the assembled theorem:**
- ✅ `MemLp.exists_boundedContinuous_eLpNorm_sub_le` / `boundedContinuousFunction_dense` —
  **continuous functions are dense in `Lᵖ(μ; E)` for any Banach `E`** (vector-valued, weakly-regular
  finite measure). This is the key enabler and the reason this is NOT an interpolation wall.
- ✅ convolution differentiation (`HasCompactSupport.hasFDerivAt_convolution_right`,
  `Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`) and `ContDiff` of a bump-convolution.
- ✅ `ContDiffBump` / `Normed` mollifier toolkit.
- ❌ **MISSING:** `Lᵖ`-NORM convergence of the mollified curve. `convolution_tendsto_right`
  (`Analysis/Convolution.lean:789`) gives only **pointwise** (`𝓝 z₀`) convergence, not
  `eLpNorm (uᵋ − u) p → 0`. There is no Banach-valued "mollification → identity in `Lᵖ`" lemma.
  The derivative-commutation `(uᵋ)' = (u')ᵋ` for the *weak* `V'`-valued derivative is also not
  packaged (mathlib's convolution-derivative lemmas are for strong/`HasFDerivAt` integrands).

**Scope of S1:** a real but **bounded** sub-build — **days-to-2-weeks**, NOT months and NOT an
interpolation theory. It is the metaplan's **PR-F3** ("mollification-in-time of `V`-valued curves;
density of `C¹` curves in `Lᵖ(0,T;V)`"). The honest decomposition:
  (a) `eLpNorm`-convergence of a time-convolution of an `Lᵖ(ℝ;E)` curve (Young's inequality for
      the convolution `eLpNorm` bound + the continuous-dense approximation already in mathlib);
  (b) `(ρᵋ ⋆ u)' = ρᵋ ⋆ u'` transported to the *weak* `V'`-derivative via
      `isWeakTimeDeriv_comp_clm`-style commutation (the repo already has the CLM-transport lemma).

### S3 — the limit passage (`lionsMagenes_energy_identity`, line 209 sorry)

Given S1, pass `n → ∞` in `smooth_energy_identity`. The walled step is the `L¹`-convergence of the
bilinear RHS `⟪(uᵋ)'(t), uᵋ(t)⟫` → `⟪u'(t), u(t)⟫`, a product of two factors converging in
*different* `L²` spaces (`V'` and `V`/`H`). Standard: Cauchy–Schwarz
`|⟪φ,v⟫| ≤ ‖φ‖_{V'}‖v‖_V` + the two `L²` convergences (`M.conv_uV`, `M.conv_uV'`) give `L¹`
convergence of the product; the endpoints converge via the continuous representative. **Bounded
mathlib work (days)** once S1 lands — no missing pillar, just Hölder + the repo's `MemLp` API.

## Refined PR-F1 / PR-F2 plan (GO path)

The metaplan's PHASE-1 sequencing holds, refined by this spike:

- **PR-F3 FIRST (promoted ahead of F1):** the time-mollification foundation — `eLpNorm`-convergent
  time-convolution of `Lᵖ(0,T;X)` curves + weak-derivative commutation. This is S1, the only real
  wall; everything else is wiring on top. Build in a new `Bochner/TimeMollification.lean`.
  *Sub-build (a)+(b) above; days-to-2-weeks.* Codex-review the `eLpNorm`-convergence statement.
- **PR-F1:** the AC energy identity (`lionsMagenes_energy_identity`, the spike's target lemma) as a
  real theorem — S2 (already proved in the spike) + S3 (Hölder limit passage) wired on PR-F3.
  Promote `smooth_energy_identity` and `dualPairing_hToVprime_eq_innerH` (both spike-proven) into
  `Bochner/TimeSobolevAC.lean`.
- **PR-F2:** `w1pTime_continuous_in_H` discharge — from PR-F1's AC scalar `t ↦ ½‖ι(u t)‖²_H`,
  build the continuous-in-`H` representative: the energy identity gives `‖ι(u s) − ι(u t)‖²_H`
  controlled by `∫ₛᵗ ⟪u',u⟫` → a Cauchy-in-`H` modulus → continuous representative a.e.-equal to
  `ι ∘ u`. No new pillar beyond PR-F1.

**No `[H,V']` interpolation sub-build is required up front.** The continuous-dense-in-`Lᵖ` lemma
(already in mathlib, vector-valued) replaces the interpolation route the metaplan flagged as the
contingency wall. The genuine cost is the `Lᵖ`-mollification convergence (S1/PR-F3), which is
bounded.

## Extra hypothesis needed?

**None.** `W1pTime GT 2 2 T uV` (with `mem_p : MemLp uV 2`, `mem_q : MemLp u' 2`,
`weakDeriv : IsWeakTimeDeriv …`) carries exactly the data the route consumes. The `MemLp` fields
already bundle `AEStronglyMeasurable`, so the D2 measurable-rep trap does not recur here. The spike
target took the `TimeMollification` as an explicit hypothesis ONLY to isolate the S1 wall for
sizing — it is to be *produced* (PR-F3), not assumed, in the real build.

## One-line summary for the orchestrator

**GO.** AC energy identity is a bounded build: S2 (smooth product rule + V'–V pairing) is already
**proved sorry-free** in the spike; the only real wall is S1 = `Lᵖ`-convergent time-mollification
of `V`/`V'`-valued curves (PR-F3, **days-to-2-weeks**, mathlib has continuous-dense-in-`Lᵖ` +
convolution-derivative but not the assembled `eLpNorm`-mollification lemma). **No `[H,V']`
interpolation needed; no extra hypothesis needed.** PR-F3 → PR-F1 → PR-F2 as refined above.
