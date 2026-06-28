# wkernel-route — sound, non-circular route to `w1pTime_continuous_in_H`

Target: `LerayHopf/Bochner/TimeSobolev.lean:534` `w1pTime_continuous_in_H`
(Lions–Magenes `W^{1,p}(0,T;V,V') ↪ C([0,T];H)`).

## DECISIVE CONSUMER VERDICT (settled — read this first)

**`w1pTime_continuous_in_H` is NOT on the critical path to the C-axiom removals.**
Traced the actual consumer chain: the standalone theorem is referenced ONLY in docstrings; it
is **applied nowhere**. The real C axioms are `galerkin_limit_passage_R3`
(`R3/AxiomaticClosure.lean:558`) and its torus twin. The axiom is applied to the **weak limit
`alPkg.u`** (`AubinLionsAssembly.lean:84`), a curve carrying ONLY `u_aestronglyMeasurable` — no
strong derivative, not even a `V'`-valued weak derivative. Its five conclusions are:

| conclusion | how it is obtained (sound route) | needs Lions–Magenes on the weak limit? |
|---|---|---|
| `WeakFormNS` (weak eq) | approximant `u_ode` integrated against test `ψ` (`tsupport ⊆ Ioo 0 T`, boundary-free) + `bForm_tendsto_of_strongL2` (already proved) | **NO** — `WeakFormNS` (`EvolutionTriple.lean:98`) is the distributional form; `tsupport ψ ⊆ Ioo 0 T` kills the boundary term, so no trace/continuity of `u` is used |
| energy inequality | weak-lsc of `‖·‖` applied to approximant `energy_bound` | **NO** — lsc inheritance |
| initial trace `u(t)→u₀` | approximant `u_initial` (`uₙ(0)=Pₙu₀`) + `𝔊.tendsto_id` + energy bound (Temam III.3) | **NO** — established through the weak form + energy estimate, not a continuous-in-H representative |
| energy class (a.e. H¹ + integ. viscous) | approximant `reg_mem`/`reg_bound` + convergence + lsc | **NO** — inheritance |

So the SOUND route to removing the C axioms is **(b) the strong-approximant structure**
(`GalerkinSolutionData_R3.u_hasDeriv`/`u_ode`/`energy_bound`/`reg_bound`), passed to the weak
limit by lsc + the proved nonlinear passage — **NOT (a) weak-limit Lions–Magenes FTC**. The
months-class Bochner weak-FTC / `w1pTime_continuous_in_H` is genuinely BYPASSED for the axiom
removals. This makes the limit-passage foundation **days-class (Temam III.3 wiring on existing
proved pieces), not months-class.** `w1pTime_continuous_in_H` stays a true, faithful, but
*off-critical-path* scaffold theorem; finishing its own proof (the route below) is independent of
the C-axiom campaign and need not block it.

(The strong-deriv reflection bypass the parallel prover found via `HasCompactSupport.integral_Ioi_deriv_eq`
is real, but it is moot for the axioms: the consumer is the WEAK LIMIT, which has no strong
derivative, so neither the reflection-strong route NOR the reflection-weak route is needed — the
limit-passage conclusions never require a continuous-in-H representative of the limit at all.)

---

## Below: the route to prove `w1pTime_continuous_in_H` ITSELF (off-critical-path, for completeness)

## The circularity, stated precisely

The committed reflection route (`TimeMollifierInterval.weakTimeDerivℝ_even_reflection`, B1)
extends a `W1pTime` curve to the whole line by even reflection so the whole-line Young/Fubini
mollification machinery applies. B1's "no Dirac at `0`" identity is provable ONLY through the
trace `u(0⁺)=u(0⁻)`, and that trace IS the continuous-in-`H` representative we are trying to
build. So reflection → mollification → energy-identity → continuous representative is circular.

The same applies to whole-line `timeConvL2_weakDeriv_comm` (WALL A): it consumes
`IsWeakTimeDerivℝ` over all of `ℝ`, which only B1 (i.e. the trace) can supply from interval data.

## Chosen route: V'-FTC primitive first, then upgrade to H (NO reflection)

Two independent facts, neither needing a trace:

**(R1) V'-continuous representative — cheap, trace-free, from mathlib FTC.**
`u' ∈ L²(0,T;V')` ⟹ `Integrable u'` on `Icc 0 T` (finite measure, `q≥1`). Define the V'-valued
primitive `w(t) := ∫ s in 0..t, W.u' s`. Then `w` is `ContinuousOn (Icc 0 T)` by
`intervalIntegral.continuousOn_primitive_interval` (Bochner-valued, in mathlib
`MeasureTheory/Integral/DominatedConvergence.lean:469`). By the weak-derivative uniqueness
`isWeakTimeDeriv_unique` (already sorry-free in TimeSobolev.lean) applied to `w'=u'` and the
embedded curve `t ↦ hToVprime (ι (uV t))`, the embedded curve `=ᵐ w + c` for a constant `c∈V'`,
so it has a `ContinuousOn (Icc 0 T)` representative INTO V'. **No reflection, no trace assumed —
the primitive's continuity is absolute continuity of the Bochner integral.**

**(R2) Upgrade V'-continuity to H-continuity — the genuine Lions–Magenes content.**
R1 gives a representative continuous into V'; the claim is continuity into the (smaller-normed,
larger) pivot H. This is the real theorem and is where the energy identity
`t ↦ ½‖ι(u t)‖²_H` AC, `d/dt = ⟨u', u⟩_{V',V}`, is needed. The sound mollification for this is
**INTERIOR** mollification on `[δ,T-δ]` (candidate b), NOT reflection:

- On any `[a,b] ⋐ (0,T)` mollify `uᵋ := ρᵋ ⋆ₜ u` with `supp ρᵋ ⊆ (-δ,δ)`, `δ < min(a, T-b)`.
  At interior `t∈[a,b]` the convolution reads `u` only on `(0,T)`, so the weak-derivative
  relation `IsWeakTimeDeriv T` (the interval predicate already carried by `W.weakDeriv`) suffices
  — NO whole-line predicate, NO reflection, NO boundary jump. `(uᵋ)' = ρᵋ ⋆ u'` holds as a strong
  V-derivative interior to `[a,b]` because the bump is smooth and supported away from `0,T`.
- The smooth product rule (`smooth_energy_identity`, spike-proved) + the V'–V pairing kernel
  (`dualPairing_hToVprime_eq_innerH`, spike-proved) give the energy identity for `uᵋ` on `[a,b]`;
  Hölder/`L²(V)`×`L²(V')` limit passage (S3) sends it to `u`. So `½‖ι(u·)‖²_H` is AC on every
  `[a,b]⋐(0,T)`, hence on `(0,T)`, with `d/dt = ⟨u',u⟩` integrable on `[0,T]`.
- AC of `½‖ι(u·)‖²_H` + R1's V'-continuity ⟹ H-continuity on the closed `[0,T]`: the H-norm
  `t↦‖ι(u t)‖_H` extends continuously to the endpoints (AC ⟹ uniformly continuous ⟹ Cauchy at
  `0⁺,T⁻`), and weak-in-H continuity (from V'-continuity + dense `ι(V)⊆H` + the uniform H-bound)
  plus norm-convergence ⟹ strong H-convergence (`‖xₙ-x‖²=‖xₙ‖²-2⟪xₙ,x⟫+‖x‖²→0`). This is the
  standard "weak + norm ⟹ strong" closure in a Hilbert space; it consumes only R1 + the AC norm,
  no trace.

**Why non-circular.** Interior mollification at `t∈[a,b]⋐(0,T)` only ever evaluates `u` inside
`(0,T)`, exactly where `W.weakDeriv : IsWeakTimeDeriv T …` already pins the `u`/`u'` relation.
The endpoint values `u(0),u(T)` are never fed INTO the mollification; they are OUTPUT by R1's
continuous primitive + the AC-extended norm. The trace is a conclusion, not a hypothesis — the
circular dependency of the reflection route is broken.

## Lemma inventory

From repo (sorry-free, reuse): `isWeakTimeDeriv_unique`, `isWeakTimeDeriv_comp_clm`,
`hToVprimeCLM`/`hToVprime` + `hToVprimeCLM_apply`, `W1pTime.ofHValuedDeriv` pattern,
`intervalIntegrable_smul_of_integrableOn_Icc`. From SPIKE-1 (to promote):
`dualPairing_hToVprime_eq_innerH`, `smooth_energy_identity`. From mathlib:
`intervalIntegral.continuousOn_primitive_interval` (R1), `HasDerivAt.inner` +
`intervalIntegral.integral_eq_sub_of_hasDerivAt` (smooth energy id),
`HasCompactSupport.hasDerivAt_convolution_right` (interior mollifier C¹).

From-scratch (the genuine residual, bounded): interior `eLpNorm`-mollification convergence on
`[a,b]` (Young bound `timeConvL2_norm_le` already proved + ε/3 with continuous-dense), and the
S3 Hölder limit passage. These are SUBSTANTIALLY SMALLER than the reflection S1 because no
boundary extension / no whole-line Fubini / no B1 trace lemma is needed.

## Build plan (this PR)

R1 is fully closeable now (mathlib FTC + repo uniqueness) → land it sorry-free as a named lemma
`w1pTime_continuous_in_Vprime`. R2's "weak+norm⟹strong" Hilbert closure is mathlib calculus →
land sorry-free. The residual interior-mollification energy-identity (the AC norm) is isolated
behind ONE precise ALLOW_SORRY (`w1pTime_energy_AC_interior`), strictly smaller than the
reflection wall and NON-circular. `w1pTime_continuous_in_H` is then assembled from R1 + the AC
norm + the Hilbert closure with no statement weakened.
