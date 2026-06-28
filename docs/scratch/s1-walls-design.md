# S1 walls — corrected-A signature + WALL B decomposition

Design note (no Lean edits). Drives: (coder) restructure of `timeConvL2_weakDeriv_comm`,
and (tiered provers) the WALL B sub-build. Source files:
`LerayHopf/Bochner/TimeMollifierInterval.lean`, `LerayHopf/Bochner/TimeSobolev.lean`,
`LerayHopf/Bochner/TimeConvolution.lean`.

---

## 0. The shared root cause

`IsWeakTimeDeriv T u v` (TimeSobolev.lean:107) is an **interval** predicate: it tests only
against `ψ` with `tsupport ψ ⊆ Ioo 0 T`, integrals over `0..T`. It pins the `u`/`v` relation
*only inside* `(0,T)`.

Convolution `(ρ ⋆[lsmul] u)(t) = ∫ s, ρ s • u (t−s)` is **non-local**: at an interior `t` it
reads `u(t−s)` for `s ∈ supp ρ` (both signs), i.e. values *outside* `(0,T)`. So the IBP/Fubini
identity for the convolution needs the `u`/`v` weak-deriv relation on a neighbourhood of
`[0,T]` — strictly more than `IsWeakTimeDeriv T u v` gives. WALL A as currently stated is
therefore not just hard but **unsound at its signature** (`u` can be redefined off `[0,T]`,
changing `ρ⋆u` near interior points while keeping `IsWeakTimeDeriv T u v`).

The fix is a **whole-line** weak-derivative predicate that both walls speak. WALL B's
even-reflection×cutoff extension naturally produces exactly that (compact support ⇒ global test
integrals converge), and WALL A consumes it soundly.

---

## 1. Corrected `timeConvL2_weakDeriv_comm` (coder task)

### 1a. New predicate (add to TimeSobolev.lean, coder)

```lean
/-- Whole-line weak (distributional) time derivative of a Banach-valued curve on all of `ℝ`.
Tests against every `C¹` compactly-supported scalar `ψ` (no interval constraint); the global
integrals converge because `ψ` has compact support. -/
def IsWeakTimeDerivℝ (u v : ℝ → X) : Prop :=
  ∀ ψ : ℝ → ℝ, HasCompactSupport ψ → ContDiff ℝ 1 ψ →
    (∫ t, deriv ψ t • u t) = - ∫ t, ψ t • v t
```

Same shape as `IsWeakTimeDeriv` but with `tsupport ψ ⊆ Ioo 0 T` dropped and `0..T` replaced by
`∫ ·` (whole line). The honest global distributional object.

### 1b. Corrected WALL A signature (PROVED, modulo the Fubini side-condition)

```lean
theorem timeConvL2_weakDeriv_comm {ρ : ℝ → ℝ} (hρ : IsTimeMollifier ρ)
    {u v : ℝ → X} (hu : LocallyIntegrable u volume) (hv : LocallyIntegrable v volume)
    (hwd : IsWeakTimeDerivℝ u v) :
    IsWeakTimeDerivℝ (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ] u)
      (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ] v)
```

The `{T : ℝ}` binder is dropped; conclusion is the global predicate. **Codex P1 incorporated:**
`IsWeakTimeDerivℝ` alone is too weak (Bochner integrals over a non-measurable `u` are junk and
Fubini is unsound), so `LocallyIntegrable u`/`LocallyIntegrable v` are added — the minimal honest
hypotheses for the box-Fubini, available downstream from the `W1pTime` `MemLp` fields after
reflection. Soundness restored: shifting a compactly-supported global `ψ` by `s` stays
compactly-supported and global, so `hwd (ψ(·+s))` is always applicable.

**Status:** the soundness-critical commutation identity (shift-substitution
`integral_add_right_eq_self` + `hwd (ψ(·+s))` + double Fubini `integral_integral_swap`) is PROVED
unconditionally. The two Fubini swaps need joint integrability of `(t,s) ↦ a(t) ρ(s) w(t−s)`
(`a ∈ {ψ', ψ}`), proved in the private helper `timeConv_prod_integrable`; its measurability +
`s`-slice integrability are PROVED, and only the standard compact-box L¹ bound on
`s ↦ ∫ t ‖a t • ρ s • w(t−s)‖` is isolated as a single non-soundness `ALLOW_SORRY`.

### 1c. Proof skeleton (prover, Opus) for the corrected statement

For test `ψ` (`HasCompactSupport`, `ContDiff ℝ 1`):
1. `∫ t, ψ'(t) • (ρ⋆u)(t) = ∫ t, ψ'(t) • ∫ s, ρ s • u(t−s)` — unfold `convolution_lsmul`.
2. Pull `ψ'(t)•` inside (`integral_smul`/linearity), then **Fubini**
   (`MeasureTheory.integral_integral_swap`) on `(t,s) ↦ ψ'(t) • ρ s • u(t−s)`. Joint
   integrability: integrand supported in `(supp ψ) × (supp ρ)` (compact×compact), bounded by
   `‖ψ'‖∞ · ρ s · ‖u(t−s)‖`, L¹ on that box (`u` L²-loc ⇒ L¹ on a bounded set).
3. Inner integral, fix `s`, substitute `r = t−s` (`integral_comp_sub_right` / measure-preserving
   shift): `∫ t, ψ'(t) • u(t−s) = ∫ r, ψ'(r+s) • u(r)`. With `χ_s := ψ(·+s)`: `χ_s` is `C¹`,
   compactly supported, and `deriv χ_s = ψ'(·+s)` (`deriv_comp_add_const`). So inner
   `= ∫ r, deriv χ_s r • u r = - ∫ r, χ_s r • v r` by `hwd χ_s` — **this is the step that was
   impossible at the old interval signature** and is now sound.
4. Fubini back + substitute again: `= - ∫ t, ψ(t) • ∫ s, ρ s • v(t−s) = - ∫ t, ψ(t) • (ρ⋆v)(t)`.

Each step is a named mathlib lemma; the only real work is the two Fubini integrability side-goals
(box argument) and the `deriv (ψ(·+s)) = (deriv ψ)(·+s)` rewrite. Tier: **Opus**, but contained
(≈1 file, days not months) **once 1a/1b land**.

### 1d. Downstream rethread

Whoever consumes `timeConvL2_weakDeriv_comm` (the `TimeMollification.lean` constructor) must now
feed it an `IsWeakTimeDerivℝ`, obtained from WALL B's extension (§2), not the raw `W1pTime`
`weakDeriv` field. So WALL B's conclusion must expose the **global** predicate (see §2a).

---

## 2. WALL B decomposition — `w1pTime_lineExtension`

From `W1pTime GT 2 2 T uV` (curve + `V'`-deriv on `[0,T]`) produce a whole-line `ūV`, `ū'` with
the three `=ᵐ`/`MemLp` properties **and** the no-endpoint-Dirac weak-deriv identity. The crux is
the last property. Decompose into a foundational predicate + three calculus lemmas + assembly.

### 2a. Sub-lemma B0 — the predicate to target (coder; trivial)

WALL B's `weakDeriv` conclusion should be stated with the **global** `IsWeakTimeDerivℝ` of §1a
(so it threads into corrected-A directly), specialized to the `V'`-valued curve
`t ↦ hToVprime (ι (ūV t))`. No new math — just use the §1a predicate in the signature.
Tier: **coder** (signature only).

### 2b. Sub-lemma B1 — even-reflection reflects the weak derivative with sign flip

```
Statement (model): for u,v with the right-half-line local weak-deriv relation, the even
reflection ũ t := u |t| has weak derivative ṽ t := sign t • v |t| across t = 0 — NO Dirac at 0,
because even reflection matches the trace u(0⁺)=u(0⁻).
```
- **CORRECTION (prover, after real effort).** The "elementary split + change of variables"
  proof sketched here is **INCOMPLETE**. The conclusion concerns the curve `u|·|`, which depends
  on `u` only on `[0,∞)`, whereas the hypothesis `IsWeakTimeDerivℝ u v` (or its interval form)
  mixes both half-axes. The only way to extract the half-axis no-jump identity from the whole-line
  predicate is through the **trace `u(0)`** — the boundary linking term — which is NOT available
  for a bare weak-derivative curve. It requires the Bochner-valued **1D-Sobolev FTC /
  continuous-representative pillar** (`u(t) = u(a) + ∫_a^t v`), exactly the months-class residual
  carried by `w1pTime_continuous_in_H` (`TimeSobolev.lean`). The "`ψ(0)·u(0)` opposite signs"
  cancellation is real but presupposes that trace.
- **Signature kept** (`weakTimeDerivℝ_even_reflection`, whole-line input → reflected whole-line
  output). The statement is TRUE (the predicate is a.e.-invariant in `u`, so it holds for the
  continuous representative), not weakened. Left as a precise `ALLOW_SORRY` blocked on the FTC
  pillar — NOT closeable by elementary distributional manipulation.
- **Tier: Opus** + the missing FTC pillar.

### 2c. Sub-lemma B2 — cutoff (product) rule for Banach-valued weak derivatives

```
Statement (CORRECTED, PROVED): for χ : ℝ → ℝ C¹ (cutoff), LocallyIntegrable u, LocallyIntegrable v
and IsWeakTimeDerivℝ u v,
IsWeakTimeDerivℝ (fun t => χ t • u t) (fun t => χ t • v t + deriv χ t • u t).
```
- **PROVED sorry-free.** Corrected signature: added `LocallyIntegrable u`/`LocallyIntegrable v`
  (codex P1 in spirit) — the `integral_add` split of `deriv(χψ)•u = (χ'ψ)•u + (χψ')•u` needs each
  summand integrable, which holds because each is `(continuous compactly-supported scalar) •
  (locally integrable curve)` via `LocallyIntegrable.integrable_smul_left_of_hasCompactSupport`.
  Proof: apply `hwd (χ·ψ)`, Leibniz `deriv(χψ)=χ'ψ+χψ'` (`deriv_mul`), regroup by additive-group
  algebra.
- **Tier: Sonnet → done (Opus closed it with the loc-integrability correction).**

### 2d. Sub-lemma B3 — the assembly: ūV := χ • (reflection of uV)

Reflect `uV` (and `u'`) off `[0,T]` to a full-line curve agreeing on `[0,T]` (B1 at both
endpoints `0` and `T` — apply B1 once at each end, or reflect-then-translate), then multiply by a
fixed cutoff `χ` supported in a bounded nbhd of `[0,T]`, `χ ≡ 1` on `[0,T]`
(`exists_contDiff_bump` / `exists_smooth_tsupport_subset`). Properties:
- `ūV =ᵐ uV` on `[0,T]`: `χ ≡ 1` and reflection = identity there (mechanical).
- `MemLp ūV 2 volume`: compact support + `MemLp` of pieces (reflection measure-preserving on each
  half; `MemLp.smul` by bounded `χ`).
- `ū' := χ • (reflected u') + χ' • (reflected ū)` (per B2); `χ' ≡ 0` on `[0,T]` ⇒ `ū' =ᵐ u'`
  there; `MemLp ū' 2` as above.
- no-jump weak-deriv: B2 applied to (B1's reflected pair) ⇒
  `IsWeakTimeDerivℝ (t ↦ hToVprime (ι (ūV t))) ū'`; `hToVprime∘ι` is a CLM, transport through it
  with the **global** analogue of `isWeakTimeDeriv_comp_clm` (§2e).
- **Tier: Opus** for the glue (B1/B2 + CLM transport + `MemLp` of reflected pieces); **Sonnet**
  for the three `=ᵐ`/`MemLp` bookkeeping properties if split out.

### 2e. Pre-req generalization

`isWeakTimeDeriv_comp_clm` (TimeSobolev.lean:328) is interval-typed; B3 needs the **global**
analogue `isWeakTimeDerivℝ_comp_clm` (same proof; the interval integrability hypotheses become
global-compact-support integrability, automatic since the integrands are compactly supported).
Tier: **Sonnet** (mechanical port).

---

## 3. Scope verdict (honest)

**WALL B is NOT a contained days-build as currently framed — it needs a small foundational
`IsWeakTimeDerivℝ` Bochner sub-layer first**, but that layer is *bounded* (one predicate + three
lemmas B1/B2 + two ports B0/2e), not months:

- The **foundation** (§1a predicate, §2e + B2 ports, B1) is the real cost. B1 (even-reflection
  no-Dirac) is the single genuinely-hard lemma — Opus, ~1–2 days of careful Banach distributional
  IBP. B2 and the ports are Sonnet-mechanical.
- Once the foundation exists, **WALL A becomes a contained Opus proof** (§1c box-Fubini), and
  **WALL B's assembly (§2d) is gluing** — days, not months.
- The original "months-class" tag was correct *for proving it inside the wrong (interval)
  signature with no foundation*. With the `IsWeakTimeDerivℝ` layer extracted, the honest estimate
  is **1 foundational Opus lemma (B1) + mechanical Sonnet ports + two contained Opus assemblies
  (A, B3)** — a bounded multi-PR build, not open-ended.

Recommended dispatch order:
1. coder: add `IsWeakTimeDerivℝ` (§1a), retype WALL A (§1b) + WALL B `weakDeriv` (§2a), port
   `isWeakTimeDerivℝ_comp_clm` signature (§2e).
2. Sonnet prover: B2 (§2c), the §2e port body, the §2d `=ᵐ`/`MemLp` bookkeeping.
3. Opus prover: B1 (§2b), then WALL A (§1c), then WALL B assembly (§2d glue).

No statement is weakened: `IsWeakTimeDerivℝ` is the *correct* (sound) hypothesis the convolution
commutation genuinely requires, supplied by the genuine extension — not a relaxation of the
conclusion.
