/-
# LerayHopf.Bochner.TimeSobolev — Stream D, Stages D1 + D2

**Stream:** D (abstract Bochner–Sobolev-in-time / Gelfand triple). **Contract:**
`docs/scratch/stream-d-bochner-time.md` (Stages D1, D2). **Status:** scaffold this cycle —
definitions + faithful theorem SIGNATURES; proof bodies deferred (lean-prover targets),
each carrying a precise `ALLOW_SORRY` / `TODO`.

This file is domain-neutral. It depends only on `LerayHopf.Bochner.GelfandTriple`
(itself depending only on `EvolutionTriple` + mathlib) and on mathlib's Bochner / `Lp` /
convergence-in-measure machinery. It does NOT import either `AxiomaticClosure.lean`, so it
introduces no import cycle and may be reused by both the T³ and ℝ³ capstones later.

## Stage D1 — vector-valued time-Sobolev objects

- `IsWeakTimeDeriv` — distributional (weak) time derivative of a Banach-valued curve, with
  the SAME test-function convention as `WeakFormNS` (`C¹`, compact support in `Ioo 0 T`).
- `isWeakTimeDeriv_unique` — a.e. uniqueness (must-prove; deferred body).
- `hasDerivAt_isWeakTimeDeriv` — a classical strong derivative is a weak time derivative
  (the entry point connecting Galerkin curves' `HasDerivAt` field to the weak API).
- `GelfandTriple.ιCLM` — the embedding `ι : V → H` bundled as a `ContinuousLinearMap`.
- `GelfandTriple.Vprime` — the continuous dual `V' := V →L[ℝ] ℝ` (`StrongDual ℝ V`).
- `GelfandTriple.hToVprime` — the canonical embedding `H → V'`, `h ↦ (v ↦ ⟪ι v, h⟫_H)`,
  i.e. the transpose of `ι` composed with the Riesz identification `H ≅ H'`.
- `W1pTime` — the abstract `W^{1,p}(0,T;V) ∩ {u' ∈ L^q(0,T;V')}` membership bundle. The
  time derivative is stored as a genuine `V'`-valued curve `u' ∈ L^q(0,T;V')` (Lions–Magenes
  / Gelfand-triple convention), NOT as an `H`-valued curve — requiring `u' ∈ H` would be
  strictly stronger and could exclude the actual Navier–Stokes weak time derivative.
- `W1pTime.ofHValuedDeriv` — the SEPARATE STRONGER specialization: an `H`-valued weak time
  derivative yields a `W1pTime` element (via the embedding `H ↪ V'`).
- `w1pTime_continuous_in_H` — Lions–Magenes good-representative embedding (months-class
  residual: scaffold-only with a precise TODO this cycle).

## Stage D2 — measurable representative primitive (KEY — unblocks P2's E1)

- `aeStronglyMeasurable_of_spaceTimeL2` — from L²-in-time convergence of an
  a.e.-strongly-measurable sequence of Banach-valued curves to a limit `g`, the limit `g`
  admits an a.e.-strongly-measurable representative AND an a.e.-convergent subsequence
  (via `TendstoInMeasure.exists_seq_tendsto_ae`). This conclusion is EXACTLY the
  time-measurability handle that `R3.AubinLionsLimitPassage.kineticEnergy_lsc_bound` (E1)
  names as its sole blocker.
- `kineticEnergy_lsc_transfer` — abstract norm-lsc transfer of a uniform pointwise bound to
  the L²-limit at a.e. time, GIVEN the measurable representative (the abstract core of E1).

## Assumptions

No new `axiom`/`opaque`/`constant`. Genuinely-missing inputs appear as explicit
hypotheses, never axioms.

## Scaffold ledger (this cycle)

Definitions (scaffold): `IsWeakTimeDeriv`, `GelfandTriple.ιCLM`, `GelfandTriple.Vprime`,
`GelfandTriple.hToVprime`, `W1pTime`.
Must-prove (body deferred — `ALLOW_SORRY`): `isWeakTimeDeriv_unique`,
`hasDerivAt_isWeakTimeDeriv`, `W1pTime.ofHValuedDeriv`, `aeStronglyMeasurable_of_spaceTimeL2`,
`kineticEnergy_lsc_transfer`.
Months-class residual (scaffold-only + `TODO`): `w1pTime_continuous_in_H`.
-/

import LerayHopf.Bochner.GelfandTriple
import Mathlib.Analysis.InnerProductSpace.Dual          -- Riesz `toDual` for `H ↪ V'`
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.LpSpace.Basic   -- MemLp / Lp (namesake of `W1pTime`)
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace LerayHopf.Bochner

open MeasureTheory Filter Topology
open scoped ENNReal

/-! ### Stage D1 — weak (distributional) time derivative -/

section WeakTimeDeriv

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- **Weak (distributional) time derivative** of a Banach-valued curve on `(0, T)`.

`v` is a weak time derivative of `u` on `(0, T)` iff for every scalar test function
`ψ : ℝ → ℝ` that is `C¹` with compact support contained in the open interval `Ioo 0 T`,

  `∫ t in 0..T, deriv ψ t • u t = - ∫ t in 0..T, ψ t • v t`   (Bochner integrals).

The compact-support-in-`Ioo 0 T` convention matches `WeakFormNS` exactly, so the two
distributional formulations compose without boundary terms. No boundary term is smuggled:
`ψ` vanishes (with all derivatives) at `0` and `T`, so the integration-by-parts identity
defining `v = u'` has no endpoint contribution. This is the genuine distributional
derivative, not a strong one. -/
def IsWeakTimeDeriv (T : ℝ) (u v : ℝ → X) : Prop :=
  ∀ ψ : ℝ → ℝ, HasCompactSupport ψ → tsupport ψ ⊆ Set.Ioo 0 T → ContDiff ℝ 1 ψ →
    (∫ t in (0 : ℝ)..T, deriv ψ t • u t) = - ∫ t in (0 : ℝ)..T, ψ t • v t

/-- **A.e. uniqueness of the weak time derivative.** If `v₁` and `v₂` are both weak time
derivatives of the same curve `u` on `(0, T)`, then they agree a.e. on `[0, T]`.

(Fundamental lemma of the calculus of variations / du Bois-Reymond for Bochner integrals.)

**Scaffold this cycle:** body deferred to lean-prover. -/
theorem isWeakTimeDeriv_unique {T : ℝ} (hT : 0 < T) {u v₁ v₂ : ℝ → X}
    (h₁ : IsWeakTimeDeriv T u v₁) (h₂ : IsWeakTimeDeriv T u v₂)
    (hv₁ : IntervalIntegrable v₁ volume 0 T) (hv₂ : IntervalIntegrable v₂ volume 0 T) :
    v₁ =ᵐ[volume.restrict (Set.Ioo 0 T)] v₂ := by
  -- From `h₁`, `h₂`: `∫ ψ • v₁ = ∫ ψ • v₂` for all admissible `ψ`, i.e. `∫ ψ • (v₁ - v₂) = 0`;
  -- du Bois-Reymond gives `v₁ = v₂` a.e. on `Ioo 0 T`.
  sorry -- ALLOW_SORRY: D1 weak-derivative a.e. uniqueness (lean-prover target). Fundamental lemma of calc. of variations for Bochner integrals; reachable from mathlib's Bochner machinery + density of `C¹_c(Ioo 0 T)`.

/-- **A classical (strong) derivative is a weak time derivative.** If `u` has strong
derivative `v` at every interior time `t ∈ Ioo 0 T` and both `u`, `v` are interval-integrable,
then `v` is the weak time derivative of `u` on `(0, T)`.

This is the entry point connecting a Galerkin curve's `HasDerivAt`/`u_hasDeriv` field to the
abstract weak-derivative API (integration by parts via
`intervalIntegral.integral_eq_sub_of_hasDerivAt`, boundary terms killed by `tsupport ⊆ Ioo`).

**Scaffold this cycle:** body deferred to lean-prover. -/
theorem hasDerivAt_isWeakTimeDeriv {T : ℝ} (hT : 0 < T) {u v : ℝ → X}
    (hu : ∀ t ∈ Set.Ioo (0 : ℝ) T, HasDerivAt u (v t) t)
    (hu_cont : ContinuousOn u (Set.Icc 0 T))
    (hv_cont : ContinuousOn v (Set.Icc 0 T)) :
    IsWeakTimeDeriv T u v := by
  -- IBP on `[0,T]`: `∫ ψ' • u = [ψ • u]₀ᵀ - ∫ ψ • u' = - ∫ ψ • v` since `ψ(0) = ψ(T) = 0`.
  sorry -- ALLOW_SORRY: D1 strong⇒weak time-derivative (lean-prover target). Bochner IBP via `intervalIntegral.integral_eq_sub_of_hasDerivAt`; boundary terms vanish because `tsupport ψ ⊆ Ioo 0 T`.

end WeakTimeDeriv

/-! ### Stage D1 — the continuous dual `V'` and the embedding `H ↪ V'` -/

namespace GelfandTriple

/-- The embedding `ι : V → H` bundled as a `ContinuousLinearMap`, using the `ι_linear`
and `ι_continuous` fields of the triple. -/
noncomputable def ιCLM (GT : GelfandTriple) :
    letI := GT.instNACG_V; letI := GT.instIPS_V; letI := GT.instNACG_H; letI := GT.instIPS_H;
    GT.V →L[ℝ] GT.H :=
  letI := GT.instNACG_V; letI := GT.instIPS_V; letI := GT.instNACG_H; letI := GT.instIPS_H
  { toLinearMap := IsLinearMap.mk' GT.ι GT.ι_linear
    cont := GT.ι_continuous }

/-- The **continuous dual** `V' := V →L[ℝ] ℝ` (= `StrongDual ℝ V`) of the regularity
space, the codomain of the Lions–Magenes time derivative `u' ∈ L^q(0,T;V')`. -/
abbrev Vprime (GT : GelfandTriple) : Type _ :=
  letI := GT.instNACG_V; letI := GT.instIPS_V;
  GT.V →L[ℝ] ℝ

/-- The **canonical embedding** `H ↪ V'`, sending `h ∈ H` to the functional
`v ↦ ⟪ι v, h⟫_H` on `V`. By real-symmetry of the inner product this equals
`(InnerProductSpace.toDual ℝ H h) ∘L ιCLM`, i.e. the transpose of `ι` composed with the
Riesz identification `H ≅ H'`. It is injective because `ι` has dense range
(`ι_denseRange`), which is exactly the Gelfand-triple defining property — but injectivity is
not needed to state `W1pTime`, so we keep this as the bare embedding. -/
noncomputable def hToVprime (GT : GelfandTriple) :
    letI := GT.instNACG_H; GT.H → GT.Vprime :=
  letI := GT.instNACG_V; letI := GT.instIPS_V
  letI := GT.instNACG_H; letI := GT.instIPS_H; letI := GT.instCS_H
  fun h => (InnerProductSpace.toDual ℝ GT.H h).comp GT.ιCLM

end GelfandTriple

/-! ### Stage D1 — abstract `W^{1,p}(0,T;V) ∩ {u' ∈ L^q(0,T;V')}` bundle -/

/-- **Abstract vector-valued time-Sobolev membership bundle** for a Gelfand triple.

`W1pTime GT p q T uV` bundles the data of `u ∈ L^p(0, T; V)` together with a weak time
derivative `u' ∈ L^q(0, T; V')`. The time derivative is stored as a genuine `V'`-valued
curve `u' : ℝ → V'` (the faithful Lions–Magenes / Gelfand-triple object): requiring the
derivative to live in the pivot space `H` would be strictly STRONGER and could exclude the
actual Navier–Stokes weak time derivative, which is only expected in `V'`. The `u`-side is
measured in `V` in the genuine **Bochner** sense (`u ∈ L^p(·;V)` is `MemLp uV p`: the
V-valued curve is a.e.-strongly-measurable with finite `eLpNorm`, controlling the curve
itself rather than only its scalar norm `t ↦ ‖u t‖_V`); weak differentiation is taken on the
`V'`-valued curve obtained by viewing `u` in `V'` through `ι` followed by `H ↪ V'`.

Fields:
- `u'` : the `V'`-valued weak time-derivative curve (Lions–Magenes `u' ∈ L^q(0,T;V')`);
- `mem_p` : `uV ∈ L^p(0,T;V)` in the **Bochner** sense — `MemLp uV p`, which bundles
  a.e.-strong-measurability of the V-valued curve `uV` with finite `eLpNorm` (NOT merely
  finiteness of the scalar norm `t ↦ ‖uV t‖`, which would not control measurability of `uV`);
- `mem_q` : `u' ∈ L^q(0,T;V')` (the genuine `V'`-valued time-derivative membership);
- `weakDeriv` : `u'` is the weak time derivative, in `V'`, of the curve `t ↦ (ι (uV t)) ∈ V'`
  (the embedding of `u` into `V'`), so the bundle is a genuine Sobolev-in-time element.

**Scaffold (definition) this cycle.** -/
structure W1pTime (GT : GelfandTriple) (p q : ℝ≥0∞) (T : ℝ)
    (uV : ℝ → GT.V) where
  /-- The `V'`-valued weak time-derivative curve (Lions–Magenes `u' ∈ L^q(0,T;V')`). -/
  u' : ℝ → GT.Vprime
  /-- `L^p(0,T;V)` membership in the genuine **Bochner** sense: the V-valued curve `uV` is
  `p`-integrable on `[0,T]`. `MemLp uV p μ` bundles `AEStronglyMeasurable uV μ` together with
  finite `eLpNorm uV p μ`, so it controls the V-valued curve itself — not merely its scalar
  norm `t ↦ ‖uV t‖` (which would not even assert measurability of `uV`). -/
  mem_p : letI := GT.instNACG_V; MemLp uV p (volume.restrict (Set.Icc 0 T))
  /-- `L^q(0,T;V')` membership of the genuine `V'`-valued weak derivative. -/
  mem_q : letI := GT.instNACG_V; letI := GT.instIPS_V;
    MemLp u' q (volume.restrict (Set.Icc 0 T))
  /-- `u'` is the weak time derivative, in `V'`, of the `V'`-image of `u`, namely
  `t ↦ hToVprime (ι (uV t))`. -/
  weakDeriv : letI := GT.instNACG_V; letI := GT.instIPS_V;
    IsWeakTimeDeriv (X := GT.Vprime) T (fun t => GT.hToVprime (GT.ι (uV t))) u'

/-- **Stronger `H`-valued-derivative specialization.** If a curve admits a weak time
derivative `u'H` valued in the pivot space `H` (a STRICTLY STRONGER condition than the
Lions–Magenes `u' ∈ V'` requirement), and that `H`-valued derivative is `L^q(0,T;H)`, then
the curve is a `W1pTime` element with `V'`-valued derivative `t ↦ hToVprime (u'H t)`.

This is the H-valued ⇒ V' embedding direction kept SEPARATE from the primary `W1pTime`
definition (per the Gelfand-triple discipline: the primary object lives in `V'`; the
`H`-valued version is a stronger input, not the contract).

**Must-prove (body deferred to lean-prover this cycle).** -/
theorem W1pTime.ofHValuedDeriv (GT : GelfandTriple) {p q : ℝ≥0∞} {T : ℝ}
    {uV : ℝ → GT.V}
    (u'H : letI := GT.instNACG_H; ℝ → GT.H)
    (mem_p : letI := GT.instNACG_V; MemLp uV p (volume.restrict (Set.Icc 0 T)))
    (mem_q : letI := GT.instNACG_H; MemLp u'H q (volume.restrict (Set.Icc 0 T)))
    (weakDeriv : letI := GT.instNACG_H; letI := GT.instIPS_H;
      IsWeakTimeDeriv (X := GT.H) T (fun t => GT.ι (uV t)) u'H) :
    Nonempty (W1pTime GT p q T uV) := by
  -- Post-compose everything with the continuous linear embedding `H ↪ V'`
  -- (`hToVprime`): `MemLp` is preserved by a CLM, and `IsWeakTimeDeriv` commutes with a
  -- continuous linear map (it preserves the IBP identity defining the weak derivative).
  sorry -- ALLOW_SORRY: D1 H-valued ⇒ V'-valued specialization (lean-prover target). Push `MemLp` and `IsWeakTimeDeriv` forward along the CLM `hToVprime : H →L V'`; uses `MemLp.comp_continuousLinearMap` and linearity of the weak-derivative IBP identity.

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
    letI := GT.instNACG_H;
    ∃ ũ : ℝ → GT.H, ContinuousOn ũ (Set.Icc 0 T) ∧
      ũ =ᵐ[volume.restrict (Set.Icc 0 T)] (fun t => GT.ι (uV t)) := by
  -- TODO: Lions–Magenes embedding `W^{1,p}(0,T;V) ∩ L^q(0,T;V') ↪ C([0,T];H)`.
  -- Missing mathlib pillar: vector-valued time-Sobolev / Bochner-time good-representative
  -- theory (the same pillar behind axiom `galerkin_limit_passage*`). MONTHS-CLASS residual,
  -- deferred this cycle per contract §2 (D1 embedding) / §7 DoD.
  sorry -- ALLOW_SORRY: D1 Lions–Magenes good-representative embedding — declared MONTHS-CLASS residual (contract §2 / §7); statement kept intact, body deferred.

/-! ### Stage D2 — measurable-representative primitive (KEY, unblocks P2's E1) -/

section MeasurableRep

variable {β : Type*} [NormedAddCommGroup β]

/-- **Measurable representative of a space-time L²-limit (D2 KEY PRIMITIVE).**

Setup (the abstract form of `AubinLionsPackage_R3`'s local space-time convergence): a
sequence `f : ℕ → ℝ → β` of curves, each a.e.-strongly-measurable in time w.r.t. a measure
`μ` on the time line, converges to a limit curve `g` in `L²(μ; β)` (i.e.
`eLpNorm (fun t => f n t - g t) 2 μ → 0`). Then:

1. `g` admits an **a.e.-strongly-measurable representative** w.r.t. `μ` (the joint
   `(t,x)`-measurability handle), and
2. there is a **subsequence** `φ` with `f (φ k) t → g t` for `μ`-a.e. `t`.

This is precisely the ingredient `R3.AubinLionsLimitPassage.kineticEnergy_lsc_bound` (E1)
names as its sole blocker: from the package's `∫₀ᵀ ∫_{B_k} ‖uₙ(t) − u(t)‖² dt → 0` (an
`eLpNorm`-to-0 statement with each `uₙ(·)` measurable in `t`), it yields both the time
measurability of the limit and an a.e.-in-`t` convergent subsequence, after which per-`t`
ball-exhaustion norm-lsc closes the kinetic bound. The conclusion is genuine
a.e.-strong-measurability + an a.e. (not merely in-measure) subsequence — no trivial
representative satisfies it because it is tied to the given `L²`-convergent sequence.

**Must-prove (body deferred to lean-prover this cycle).** Route:
`eLpNorm`-to-0 ⇒ `TendstoInMeasure` (`tendstoInMeasure_of_tendsto_eLpNorm`) ⇒
`TendstoInMeasure.exists_seq_tendsto_ae`; the limit's a.e.-strong-measurability follows from
`aestronglyMeasurable_of_tendsto_ae` on the a.e.-convergent subsequence. -/
theorem aeStronglyMeasurable_of_spaceTimeL2
    {μ : Measure ℝ} {f : ℕ → ℝ → β} {g : ℝ → β}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (hconv : Tendsto (fun n => eLpNorm (fun t => f n t - g t) 2 μ) atTop (𝓝 0)) :
    AEStronglyMeasurable g μ ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ t ∂μ, Tendsto (fun k => f (φ k) t) atTop (𝓝 (g t)) := by
  -- eLpNorm → 0  ⇒  TendstoInMeasure (mathlib: `tendstoInMeasure_of_tendsto_eLpNorm`);
  -- then `TendstoInMeasure.exists_seq_tendsto_ae` gives the a.e.-convergent subsequence,
  -- and `aestronglyMeasurable_of_tendsto_ae` upgrades the limit to a.e.-strongly-measurable.
  sorry -- ALLOW_SORRY: D2 KEY measurable-representative primitive (lean-prover target). Route: `tendstoInMeasure_of_tendsto_eLpNorm` → `TendstoInMeasure.exists_seq_tendsto_ae` → `aestronglyMeasurable_of_tendsto_ae`. This is the exact ingredient `kineticEnergy_lsc_bound` (E1) is blocked on.

end MeasurableRep

/-- **Abstract kinetic-energy lower-semicontinuity transfer (abstract core of E1).**

GIVEN the measurable representative from `aeStronglyMeasurable_of_spaceTimeL2`: if a sequence
`f n : ℝ → β` converges to `g` in `L²(μ)`, with a UNIFORM pointwise norm bound
`‖f n t‖ ≤ M` for `μ`-a.e. `t` and every `n`, then the limit inherits the bound at a.e.
time: `‖g t‖ ≤ M` for `μ`-a.e. `t`.

This is the domain-neutral norm-lsc step: extract the a.e.-convergent subsequence
(`aeStronglyMeasurable_of_spaceTimeL2`), then pass the uniform bound through the a.e. limit
by `le_of_tendsto` + lower-semicontinuity of the norm. The a.e.-in-`t` conclusion (NOT
`∀ t`) is the honest form — the value of `g` on a `μ`-null set is not pinned by `L²`
convergence (matching `kineticEnergy_lsc_bound`'s a.e. conclusion, no-smuggle).

**Must-prove (body deferred to lean-prover this cycle).** -/
theorem kineticEnergy_lsc_transfer {β : Type*} [NormedAddCommGroup β]
    {μ : Measure ℝ} {f : ℕ → ℝ → β} {g : ℝ → β} {M : ℝ}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (hconv : Tendsto (fun n => eLpNorm (fun t => f n t - g t) 2 μ) atTop (𝓝 0))
    (hbound : ∀ n, ∀ᵐ t ∂μ, ‖f n t‖ ≤ M) :
    ∀ᵐ t ∂μ, ‖g t‖ ≤ M := by
  -- Extract the a.e.-convergent subsequence via `aeStronglyMeasurable_of_spaceTimeL2`,
  -- then `‖g t‖ = lim ‖f (φ k) t‖ ≤ M` a.e. by `le_of_tendsto` + `Tendsto.norm`.
  sorry -- ALLOW_SORRY: D2 norm-lsc transfer (lean-prover target). Uses `aeStronglyMeasurable_of_spaceTimeL2` to get the a.e.-convergent subsequence, then `le_of_tendsto` on `‖f (φ k) t‖ → ‖g t‖`. This is the abstract core consumed by `kineticEnergy_lsc_bound` (E1).

end LerayHopf.Bochner
