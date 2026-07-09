/-
# LerayHopf.Bochner.TimeSobolev — Stream D, Stages D1 + D2

**Stream:** D (abstract Bochner–Sobolev-in-time / Gelfand triple). **Contract:**
`docs/scratch/stream-d-bochner-time.md` (Stages D1, D2). **Status:** scaffold this cycle —
definitions + faithful theorem SIGNATURES; proof bodies deferred (lean-prover targets),
each carrying a precise `ALLOW_SORRY` / `TODO`.

This file is domain-neutral. It depends only on `LerayHopf.Bochner.GelfandTriple`
(itself depending only on `EvolutionTriple` + mathlib) and on mathlib's Bochner / `Lp` /
convergence-in-measure machinery. It does NOT import either `SolutionInterfaces.lean`, so it
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
  a.e.-strongly-measurable sequence to an **a.e.-strongly-measurable** limit `g`, there is an
  a.e.-convergent subsequence (and `g`'s representative is returned). **Statement-gate fix
  (Lane-D):** the measurability of `g` is an explicit hypothesis `hg`, not a conclusion — without
  it the statement is FALSE (Vitali-set counterexample in the theorem docstring), since L²-limit
  measurability cannot be extracted from L²-convergence alone. **Proved sorry-free.**
- `kineticEnergy_lsc_transfer` — abstract norm-lsc transfer of a uniform pointwise bound to the
  L²-limit at a.e. time, given the same `hg`. **Proved sorry-free.**

## Assumptions

No new `axiom`/`opaque`/`constant`. Genuinely-missing inputs appear as explicit
hypotheses, never axioms.

## Scaffold ledger (this cycle)

Definitions (scaffold): `IsWeakTimeDeriv`, `GelfandTriple.ιCLM`, `GelfandTriple.Vprime`,
`GelfandTriple.hToVprime`, `W1pTime`.
**Proved this cycle (sorry-free):** `hasDerivAt_isWeakTimeDeriv` (strong⇒weak time derivative
via Bochner IBP), `aeStronglyMeasurable_of_spaceTimeL2` and `kineticEnergy_lsc_transfer` (both
after a statement-gate fix adding the isolated `hg : AEStronglyMeasurable g μ` hypothesis — the
prior hypothesis-free forms were FALSE; Vitali counterexamples kept in their docstrings),
`GelfandTriple.hToVprimeCLM` / `GelfandTriple.hToVprimeCLM_apply` (the embedding `H ↪ V'`
bundled as a genuine `H →L[ℝ] V'`, equal to `hToVprime` pointwise), and
`isWeakTimeDeriv_comp_clm` (transport of a weak time derivative through a CLM, given
interval-integrability of the Bochner integrands).
**Proved this cycle (sorry-free, issue #13-B):** `isWeakTimeDeriv_unique` — after adding the
  faithful `[CompleteSpace X]` guard (domain fix: without it `integral_of_not_completeSpace`
  collapses both `h₁`/`h₂` to `0 = -0`, admitting arbitrary `v₁,v₂`; identical to D2 precedent)
  and importing `Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff` (vector-valued du Bois-Reymond).
`W1pTime.ofHValuedDeriv` is **sorry-free this cycle**: under the domain guards `1 ≤ p` /
`1 ≤ q` (the Lions–Magenes space is only defined for exponents ≥ 1, so these are faithful
preconditions, not proof-strengthening), the two interval-integrability obligations are
discharged via `MemLp.integrable` on the finite measure combined with the private helper
`intervalIntegrable_smul_of_integrableOn_Icc` (bounded continuous test factor + support in
`Ioo 0 T`). The `1 ≤ p` / `1 ≤ q` signature guards (added commit c362d9b) are the minimal
honest domain restriction; the previous over-strength-flagged form (without those guards) was
corrected before the proof was attempted.
Months-class residual (scaffold-only + `TODO`): `w1pTime_continuous_in_H`.
-/

import LerayHopf.Bochner.GelfandTriple
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff -- du Bois-Reymond for Bochner integrals (IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero); needed by isWeakTimeDeriv_unique
import Mathlib.Analysis.InnerProductSpace.Dual          -- Riesz `toDual` for `H ↪ V'`
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.LpSpace.Basic   -- MemLp / Lp (namesake of `W1pTime`)
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

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

/-- **Whole-line weak (distributional) time derivative** of a Banach-valued curve on all of `ℝ`.

`v` is a whole-line weak time derivative of `u` iff for every scalar test function
`ψ : ℝ → ℝ` that is `C¹` with compact support (no interval constraint),

  `∫ t, deriv ψ t • u t = - ∫ t, ψ t • v t`   (global Bochner integrals).

The global integrals converge because `ψ` has compact support. This is the honest
distributional derivative on `ℝ` — strictly stronger than `IsWeakTimeDeriv T u v`, which
only tests `ψ` supported inside `(0, T)`. It is the correct hypothesis for whole-line
operations such as convolution (see `s1-walls-design.md` §1a): shifting a globally
compactly-supported test function by `s` stays compactly-supported and global, so
`hwd (ψ(· + s))` is always applicable, dissolving the Fubini obstruction present at
the old interval signature. -/
def IsWeakTimeDerivℝ (u v : ℝ → X) : Prop :=
  ∀ ψ : ℝ → ℝ, HasCompactSupport ψ → ContDiff ℝ 1 ψ →
    (∫ t, deriv ψ t • u t) = - ∫ t, ψ t • v t

/-- **A.e. uniqueness of the weak time derivative.** If `v₁` and `v₂` are both weak time
derivatives of the same curve `u` on `(0, T)`, then they agree a.e. on `[0, T]`.

(Fundamental lemma of the calculus of variations / du Bois-Reymond for Bochner integrals.)

**Proved this cycle** (sorry-free, issue #13-B): `[CompleteSpace X]` is the faithful domain fix
(see body comment); proof via `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`. -/
theorem isWeakTimeDeriv_unique [CompleteSpace X] {T : ℝ} (hT : 0 < T) {u v₁ v₂ : ℝ → X}
    (h₁ : IsWeakTimeDeriv T u v₁) (h₂ : IsWeakTimeDeriv T u v₂)
    (hv₁ : IntervalIntegrable v₁ volume 0 T) (hv₂ : IntervalIntegrable v₂ volume 0 T) :
    v₁ =ᵐ[volume.restrict (Set.Ioo 0 T)] v₂ := by
  -- [CompleteSpace X] is a faithful domain-of-definition fix (not proof-strengthening): without
  -- it Bochner integrals collapse to 0 (`integral_of_not_completeSpace`), making `h₁`/`h₂`
  -- trivial for arbitrary `v₁`,`v₂` — identical to the D2 `AEStronglyMeasurable` precedent.
  set w : ℝ → X := fun t => v₁ t - v₂ t with hw
  have hIoo : (0:ℝ) ≤ T := hT.le
  have hv₁Ioo : IntegrableOn v₁ (Set.Ioo 0 T) volume :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hIoo).mp hv₁
  have hv₂Ioo : IntegrableOn v₂ (Set.Ioo 0 T) volume :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hIoo).mp hv₂
  have hwIoo : IntegrableOn w (Set.Ioo 0 T) volume := by
    have h := hv₁Ioo.sub hv₂Ioo; rw [hw]; exact h
  have hwLoc : LocallyIntegrableOn w (Set.Ioo 0 T) volume := hwIoo.locallyIntegrableOn
  have key : ∀ g : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g →
      tsupport g ⊆ Set.Ioo 0 T → ∫ x, g x • w x ∂volume = 0 := by
    intro g hgsmooth hgcs hgsupp
    have hgC1 : ContDiff ℝ 1 g := hgsmooth.of_le (by norm_num)
    have hcompl : ∀ x, x ∉ Set.Ioo 0 T → g x • w x = 0 := by
      intro x hx
      have : g x = 0 := by
        by_contra hgx; exact hx (hgsupp (subset_tsupport g (by simpa using hgx)))
      simp [this]
    have hfull : ∫ x, g x • w x ∂volume = ∫ x in Set.Ioo 0 T, g x • w x ∂volume :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero hcompl).symm
    have hInterval : ∫ x in Set.Ioo 0 T, g x • w x ∂volume = ∫ t in (0:ℝ)..T, g t • w t := by
      rw [intervalIntegral.integral_of_le hIoo, integral_Ioc_eq_integral_Ioo]
    have e1 := h₁ g hgcs hgsupp hgC1
    have e2 := h₂ g hgcs hgsupp hgC1
    have heq : (∫ t in (0:ℝ)..T, g t • v₁ t) = ∫ t in (0:ℝ)..T, g t • v₂ t := by
      have : -(∫ t in (0:ℝ)..T, g t • v₁ t) = -∫ t in (0:ℝ)..T, g t • v₂ t := by
        rw [← e1, ← e2]
      simpa using this
    have hgcont : ContinuousOn g (Set.uIcc (0:ℝ) T) := hgC1.continuous.continuousOn
    have hi1 : IntervalIntegrable (fun t => g t • v₁ t) volume 0 T := hv₁.continuousOn_smul hgcont
    have hi2 : IntervalIntegrable (fun t => g t • v₂ t) volume 0 T := hv₂.continuousOn_smul hgcont
    have hwsplit : ∫ t in (0:ℝ)..T, g t • w t
        = (∫ t in (0:ℝ)..T, g t • v₁ t) - ∫ t in (0:ℝ)..T, g t • v₂ t := by
      rw [← intervalIntegral.integral_sub hi1 hi2]; congr 1; funext t; simp only [hw, smul_sub]
    rw [hfull, hInterval, hwsplit, heq, sub_self]
  have main : ∀ᵐ x ∂volume, x ∈ Set.Ioo 0 T → w x = 0 :=
    isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero hwLoc key
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioo]
  filter_upwards [main] with t ht hmem
  simpa [hw, sub_eq_zero] using ht hmem

/-- **A classical (strong) derivative is a weak time derivative.** If `u` has strong
derivative `v` at every interior time `t ∈ Ioo 0 T` and both `u`, `v` are interval-integrable,
then `v` is the weak time derivative of `u` on `(0, T)`.

This is the entry point connecting a Galerkin curve's `HasDerivAt`/`u_hasDeriv` field to the
abstract weak-derivative API (integration by parts via
`intervalIntegral.integral_smul_deriv_eq_deriv_smul_of_hasDerivAt`, boundary terms killed by
`tsupport ψ ⊆ Ioo 0 T`).

`CompleteSpace X` is required: the Bochner interval-integral integration-by-parts lemma
(`intervalIntegral.integral_smul_deriv_eq_deriv_smul_of_hasDerivAt`) needs the target space
complete. The intended consumers (Galerkin velocity curves in `L2VF_R3` / the pivot Hilbert
space `H`) are complete, so this is a faithful precondition, not a weakening.

**Proved this cycle** (sorry-free). -/
theorem hasDerivAt_isWeakTimeDeriv [CompleteSpace X] {T : ℝ} (hT : 0 < T) {u v : ℝ → X}
    (hu : ∀ t ∈ Set.Ioo (0 : ℝ) T, HasDerivAt u (v t) t)
    (hu_cont : ContinuousOn u (Set.Icc 0 T))
    (hv_cont : ContinuousOn v (Set.Icc 0 T)) :
    IsWeakTimeDeriv T u v := by
  -- IBP on `[0,T]`: `∫ ψ' • u = [ψ • u]₀ᵀ - ∫ ψ • u' = - ∫ ψ • v` since `ψ(0) = ψ(T) = 0`.
  intro ψ _hψcs hψsupp hψC1
  have hTle : (0 : ℝ) ≤ T := le_of_lt hT
  have huIcc : Set.uIcc (0 : ℝ) T = Set.Icc 0 T := Set.uIcc_of_le hTle
  have hmin : min (0 : ℝ) T = 0 := min_eq_left hTle
  have hmax : max (0 : ℝ) T = T := max_eq_right hTle
  -- `ψ` is continuous and differentiable; `deriv ψ` is continuous (ContDiff 1).
  have hψcont : Continuous ψ := hψC1.continuous
  have hψderiv : ∀ x : ℝ, HasDerivAt ψ (deriv ψ x) x := fun x =>
    (hψC1.differentiable one_ne_zero).differentiableAt.hasDerivAt
  have hderivψcont : Continuous (deriv ψ) := hψC1.continuous_deriv_one
  -- endpoint values of `ψ` vanish: `0, T ∉ tsupport ψ ⊆ Ioo 0 T`.
  have hψ0 : ψ 0 = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => (lt_irrefl (0 : ℝ)) (hψsupp h).1)
  have hψT : ψ T = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => (lt_irrefl T) (hψsupp h).2)
  -- IBP: `∫ ψ • v = ψ(T)•u(T) - ψ(0)•u(0) - ∫ (deriv ψ) • u`.
  have hibp := intervalIntegral.integral_smul_deriv_eq_deriv_smul_of_hasDerivAt
    (u := ψ) (v := u) (u' := deriv ψ) (v' := v) (a := (0 : ℝ)) (b := T)
    (by rw [huIcc]; exact hψcont.continuousOn)
    (by rw [huIcc]; exact hu_cont)
    (by rw [hmin, hmax]; exact fun x _ => hψderiv x)
    (by rw [hmin, hmax]; exact hu)
    (hderivψcont.intervalIntegrable 0 T)
    (by rw [← huIcc] at hv_cont; exact hv_cont.intervalIntegrable)
  -- substitute the vanishing endpoints (`ψ 0 = ψ T = 0`), killing the boundary term:
  -- `hibp : ∫ ψ • v = 0 • u T - 0 • u 0 - ∫ (deriv ψ) • u = - ∫ (deriv ψ) • u`.
  rw [hψ0, hψT] at hibp
  simp only [zero_smul, sub_zero, zero_sub] at hibp
  -- `hibp : ∫ ψ • v = - ∫ (deriv ψ) • u`; the goal is `∫ (deriv ψ) • u = - ∫ ψ • v`.
  rw [hibp, neg_neg]

end WeakTimeDeriv

/-! ### Stage D1 — the continuous dual `V'` and the embedding `H ↪ V'` -/

namespace GelfandTriple

/-- The embedding `ι : V →L[ℝ] H` as a `ContinuousLinearMap`. Now that `GelfandTriple.ι` is
itself a `ContinuousLinearMap`, this is a trivial alias for `GT.ι`. Kept for backward
compatibility with downstream call sites in this file. -/
noncomputable def ιCLM (GT : GelfandTriple) :
    letI := GT.instNACG_V; letI := GT.instIPS_V; letI := GT.instNACG_H; letI := GT.instIPS_H;
    GT.V →L[ℝ] GT.H :=
  letI := GT.instNACG_V; letI := GT.instIPS_V; letI := GT.instNACG_H; letI := GT.instIPS_H
  GT.ι

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
  fun h => (InnerProductSpace.toDual ℝ GT.H h).comp GT.ι

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
    letI := GT.instNACG_H; letI := GT.instIPS_H;
    IsWeakTimeDeriv (X := GT.Vprime) T (fun t => GT.hToVprime (GT.ι (uV t))) u'

/-- The canonical embedding `H ↪ V'` as a genuine `ContinuousLinearMap` (the bundled form
of `GelfandTriple.hToVprime`). It is the precomposition `g ↦ g ∘ ιCLM` (the honest ℝ-linear
`ContinuousLinearMap.compL … |>.flip ιCLM`) applied after the Riesz map `innerSL ℝ : H →L[ℝ]
(H →L[ℝ] ℝ)`. Over `ℝ` the inner product is genuinely bilinear, so `innerSL ℝ` is an honest
`H →L[ℝ] _` (its conjugate-linearity is trivial), and `hToVprimeCLM h = (innerSL ℝ h).comp
ιCLM = (toDual ℝ H h).comp ιCLM = hToVprime h` pointwise (see `hToVprimeCLM_apply`). -/
noncomputable def GelfandTriple.hToVprimeCLM (GT : GelfandTriple) :
    letI := GT.instNACG_V; letI := GT.instIPS_V;
    letI := GT.instNACG_H; letI := GT.instIPS_H; GT.H →L[ℝ] GT.Vprime :=
  letI := GT.instNACG_V; letI := GT.instIPS_V
  letI := GT.instNACG_H; letI := GT.instIPS_H; letI := GT.instCS_H
  ((ContinuousLinearMap.compL ℝ GT.V GT.H ℝ).flip GT.ι).comp
    (innerSL ℝ : GT.H →L[ℝ] (GT.H →L[ℝ] ℝ))

@[simp] theorem GelfandTriple.hToVprimeCLM_apply (GT : GelfandTriple) :
    letI := GT.instNACG_H;
    (h : GT.H) → GT.hToVprimeCLM h = GT.hToVprime h := by
  letI := GT.instNACG_V; letI := GT.instIPS_V
  letI := GT.instNACG_H; letI := GT.instIPS_H; letI := GT.instCS_H
  intro h
  -- Both sides equal `(v ↦ ⟪ι v, h⟫) ∈ V'`; reduce the bundled composition and compare on `V`.
  ext v
  simp only [GelfandTriple.hToVprimeCLM, GelfandTriple.hToVprime,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.compL_apply, coe_innerSL_apply, InnerProductSpace.toDual_apply_apply]

/-- **Transport of a weak time derivative through a continuous linear map.** If `v` is the
weak time derivative of `u` (an `X`-valued curve) and `L : X →L[ℝ] Y` is continuous linear,
then `L ∘ v` is the weak time derivative of `L ∘ u`, PROVIDED both Bochner integrands
`t ↦ deriv ψ t • u t` and `t ↦ ψ t • v t` are interval-integrable on `[0,T]` for every
admissible test function `ψ`. `L` commutes with the interval integral
(`ContinuousLinearMap.intervalIntegral_comp_comm`, which needs that integrability) and with
the scalar `smul` (`map_smul`), so it carries the defining IBP identity from `X` to `Y`. -/
theorem isWeakTimeDeriv_comp_clm {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    {T : ℝ} {u v : ℝ → X} (L : X →L[ℝ] Y)
    (hwd : IsWeakTimeDeriv (X := X) T u v)
    (hu_int : ∀ ψ : ℝ → ℝ, HasCompactSupport ψ → tsupport ψ ⊆ Set.Ioo 0 T → ContDiff ℝ 1 ψ →
      IntervalIntegrable (fun t => deriv ψ t • u t) volume 0 T)
    (hv_int : ∀ ψ : ℝ → ℝ, HasCompactSupport ψ → tsupport ψ ⊆ Set.Ioo 0 T → ContDiff ℝ 1 ψ →
      IntervalIntegrable (fun t => ψ t • v t) volume 0 T) :
    IsWeakTimeDeriv (X := Y) T (fun t => L (u t)) (fun t => L (v t)) := by
  intro ψ hψcs hψsupp hψC1
  -- The defining identity in `X`: `∫ deriv ψ • u = - ∫ ψ • v`.
  have hX := hwd ψ hψcs hψsupp hψC1
  -- Push `L` through both interval integrals; `L` is linear so `L (a • x) = a • L x`.
  have hLu : (∫ t in (0:ℝ)..T, deriv ψ t • L (u t))
      = L (∫ t in (0:ℝ)..T, deriv ψ t • u t) := by
    have := L.intervalIntegral_comp_comm (a := (0:ℝ)) (b := T) (μ := volume)
      (f := fun t => deriv ψ t • u t) (hu_int ψ hψcs hψsupp hψC1)
    simpa only [map_smul] using this
  have hLv : (∫ t in (0:ℝ)..T, ψ t • L (v t))
      = L (∫ t in (0:ℝ)..T, ψ t • v t) := by
    have := L.intervalIntegral_comp_comm (a := (0:ℝ)) (b := T) (μ := volume)
      (f := fun t => ψ t • v t) (hv_int ψ hψcs hψsupp hψC1)
    simpa only [map_smul] using this
  rw [hLu, hLv, hX, map_neg]

/-- **Transport of a whole-line weak time derivative through a continuous linear map.**
If `v` is the whole-line weak time derivative of `u` (an `X`-valued curve, `IsWeakTimeDerivℝ
u v`) and `L : X →L[ℝ] Y` is continuous linear, then `L ∘ v` is the whole-line weak time
derivative of `L ∘ u`.

The global integrals converge because the test `ψ` has compact support; `L` commutes with
the Bochner integral (`ContinuousLinearMap.integral_comp_comm`, which needs integrability —
automatic here: integrand `deriv ψ • u` is supported in `tsupport ψ` which is compact, so
integrability follows from continuity of the integrand on a compact domain) and with `smul`
(`map_smul`). This is the global analogue of `isWeakTimeDeriv_comp_clm` (§2e of the
`s1-walls-design.md`); the interval integrability side-conditions collapse because
compactness of `tsupport ψ` gives integrability for free.

Tier: **Sonnet** (mechanical port of `isWeakTimeDeriv_comp_clm`). -/
theorem isWeakTimeDerivℝ_comp_clm {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    {u v : ℝ → X} (L : X →L[ℝ] Y)
    (hwd : IsWeakTimeDerivℝ (X := X) u v)
    (hu_int : ∀ ψ : ℝ → ℝ, HasCompactSupport ψ → ContDiff ℝ 1 ψ →
      Integrable (fun t => deriv ψ t • u t) volume)
    (hv_int : ∀ ψ : ℝ → ℝ, HasCompactSupport ψ → ContDiff ℝ 1 ψ →
      Integrable (fun t => ψ t • v t) volume) :
    IsWeakTimeDerivℝ (X := Y) (fun t => L (u t)) (fun t => L (v t)) := by
  -- Port of `isWeakTimeDeriv_comp_clm` to the whole-line setting.
  -- For each test ψ: push L through both global integrals via `ContinuousLinearMap.integral_comp_comm`,
  -- use `map_smul` to commute L with scalar multiplication, then apply `hwd ψ`.
  intro ψ hψcs hψC1
  -- The defining identity in `X`: `∫ deriv ψ • u = - ∫ ψ • v`.
  have hX := hwd ψ hψcs hψC1
  -- Push `L` through the left integral: `∫ deriv ψ t • L (u t) = L (∫ deriv ψ t • u t)`.
  have hLu : (∫ t, deriv ψ t • L (u t)) = L (∫ t, deriv ψ t • u t) := by
    have hint := hu_int ψ hψcs hψC1
    have : (fun t => deriv ψ t • L (u t)) = (fun t => L (deriv ψ t • u t)) := by
      ext t; rw [L.map_smul]
    rw [this]
    exact L.integral_comp_comm hint
  -- Push `L` through the right integral: `∫ ψ t • L (v t) = L (∫ ψ t • v t)`.
  have hLv : (∫ t, ψ t • L (v t)) = L (∫ t, ψ t • v t) := by
    have hint := hv_int ψ hψcs hψC1
    have : (fun t => ψ t • L (v t)) = (fun t => L (ψ t • v t)) := by
      ext t; rw [L.map_smul]
    rw [this]
    exact L.integral_comp_comm hint
  rw [hLu, hLv, hX, L.map_neg]

/-- Helper for `W1pTime.ofHValuedDeriv`: a Bochner curve `g` integrable on `Icc 0 T`,
scalar-multiplied by a continuous, compactly-supported test factor `φ` whose support sits
inside `Ioo 0 T`, is interval-integrable on `0..T`. The test factor is bounded (continuous
with compact support), so the `smul` stays in `L¹`; for `T < 0` the support constraint forces
`φ = 0`. -/
private theorem intervalIntegrable_smul_of_integrableOn_Icc
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {T : ℝ} {g : ℝ → E} {φ : ℝ → ℝ}
    (hg : Integrable g (volume.restrict (Set.Icc 0 T)))
    (hφc : Continuous φ) (hφcs : HasCompactSupport φ)
    (hφsupp : tsupport φ ⊆ Set.Ioo 0 T) :
    IntervalIntegrable (fun t => φ t • g t) volume 0 T := by
  rcases le_or_gt 0 T with hT | hT
  · -- `Ι 0 T = Ioc 0 T ⊆ Icc 0 T`; the `smul` is integrable on `Icc 0 T` by boundedness of `φ`.
    obtain ⟨C, hC⟩ := hφc.bounded_above_of_compact_support hφcs
    have hint : Integrable (fun t => φ t • g t) (volume.restrict (Set.Icc 0 T)) :=
      hg.bdd_smul C hφc.aestronglyMeasurable (Filter.Eventually.of_forall hC)
    rw [intervalIntegrable_iff]
    have hsub : Set.uIoc 0 T ⊆ Set.Icc 0 T := by
      rw [Set.uIoc_of_le hT]; exact Set.Ioc_subset_Icc_self
    have hint' : IntegrableOn (fun t => φ t • g t) (Set.Icc 0 T) volume := hint
    exact hint'.mono_set hsub
  · -- `T < 0`: `Ioo 0 T = ∅`, so `tsupport φ = ∅` and `φ = 0`; the integrand vanishes.
    have hIoo : Set.Ioo 0 T = (∅ : Set ℝ) := Set.Ioo_eq_empty (by exact not_lt.2 hT.le)
    have hφ0 : φ = 0 := by
      funext t
      exact image_eq_zero_of_notMem_tsupport (fun ht => by
        have := hφsupp ht; rw [hIoo] at this; exact this.elim)
    subst hφ0
    simp only [Pi.zero_apply, zero_smul]
    exact IntervalIntegrable.zero (μ := volume) (a := (0:ℝ)) (b := T) (E := E)

/-- **Stronger `H`-valued-derivative specialization.** If a curve admits a weak time
derivative `u'H` valued in the pivot space `H` (a STRICTLY STRONGER condition than the
Lions–Magenes `u' ∈ V'` requirement), and that `H`-valued derivative is `L^q(0,T;H)`, then
the curve is a `W1pTime` element with `V'`-valued derivative `t ↦ hToVprime (u'H t)`.

This is the H-valued ⇒ V' embedding direction kept SEPARATE from the primary `W1pTime`
definition (per the Gelfand-triple discipline: the primary object lives in `V'`; the
`H`-valued version is a stronger input, not the contract).

**Proved this cycle** (sorry-free). Route: post-compose with `hToVprimeCLM`; `MemLp` carried
by `comp_memLp'`; weak-derivative identity transported by `isWeakTimeDeriv_comp_clm`;
both interval-integrability obligations discharged by `intervalIntegrable_smul_of_integrableOn_Icc`
using `MemLp.integrable` under the `1 ≤ p` / `1 ≤ q` guards. -/
-- Domain-of-definition guard: `W^{1,p}(0,T;·)` requires `1 ≤ p`; the V′-valued IBP identity
-- in `weakDeriv` is ill-defined without L¹ control (`MemLp _ p` on a finite measure only implies
-- integrability when `1 ≤ p`). Same for `q`. These are NOT proof-strengthening hypotheses but
-- honest domain restrictions stating where the Lions–Magenes space lives.
theorem W1pTime.ofHValuedDeriv (GT : GelfandTriple) {p q : ℝ≥0∞} {T : ℝ}
    {uV : ℝ → GT.V}
    (u'H : letI := GT.instNACG_H; ℝ → GT.H)
    (mem_p : letI := GT.instNACG_V; MemLp uV p (volume.restrict (Set.Icc 0 T)))
    (mem_q : letI := GT.instNACG_H; MemLp u'H q (volume.restrict (Set.Icc 0 T)))
    (hp : 1 ≤ p) (hq : 1 ≤ q)
    (weakDeriv : letI := GT.instNACG_V; letI := GT.instIPS_V;
      letI := GT.instNACG_H; letI := GT.instIPS_H;
      IsWeakTimeDeriv (X := GT.H) T (fun t => GT.ι (uV t)) u'H) :
    Nonempty (W1pTime GT p q T uV) := by
  letI := GT.instNACG_V; letI := GT.instIPS_V
  letI := GT.instNACG_H; letI := GT.instIPS_H; letI := GT.instCS_H
  letI := GT.instCS_V
  -- Post-compose everything with the continuous linear embedding `H ↪ V'` bundled as the CLM
  -- `hToVprimeCLM`. `MemLp` is preserved by a CLM (`comp_memLp'`); the weak-derivative IBP
  -- identity is carried through by `isWeakTimeDeriv_comp_clm`.
  set L : GT.H →L[ℝ] GT.Vprime := GT.hToVprimeCLM with hL
  -- `mem_q` for the `V'`-valued derivative `t ↦ hToVprime (u'H t) = L (u'H t)`.
  have hmem_q : MemLp (fun t => GT.hToVprime (u'H t)) q (volume.restrict (Set.Icc 0 T)) := by
    have := L.comp_memLp' (f := u'H) mem_q
    simpa only [Function.comp_def, hL, GelfandTriple.hToVprimeCLM_apply] using this
  -- `weakDeriv` for the `V'`-valued curve: transport the `H`-identity through `L`.
  have hwd : IsWeakTimeDeriv (X := GT.Vprime) T
      (fun t => GT.hToVprime (GT.ι (uV t))) (fun t => GT.hToVprime (u'H t)) := by
    have hbase := isWeakTimeDeriv_comp_clm (X := GT.H) (Y := GT.Vprime) (T := T)
      (u := fun t => GT.ι (uV t)) (v := u'H) L weakDeriv
      -- Interval-integrability of the two `H`-valued Bochner integrands. This is the GENUINE
      -- remaining input: `MemLp _ p` over the finite measure `volume.restrict (Icc 0 T)` does NOT
      -- imply `L¹`/interval-integrability for `p < 1`. The `1 ≤ p`/`1 ≤ q` domain guards (now
      -- available as `hp`/`hq`) are what make these obligations provable:
      -- `MemLp.mono_exponent` lowers to `MemLp 1` on the finite measure, and `deriv ψ` (resp. `ψ`),
      -- continuous with compact support in `Ioo 0 T`, is bounded, so the `smul` stays in `L¹`.
      (fun ψ hψcs hψsupp hψC1 => by
        -- Interval-integrability of `t ↦ deriv ψ t • ι (uV t)` on `[0,T]`.
        -- `MemLp uV p` (finite measure, `1 ≤ p`) ⇒ `Integrable (ι ∘ uV)`; `deriv ψ` is
        -- continuous, compactly supported in `Ioo 0 T`, hence bounded, so the `smul` is `L¹`.
        have hg : Integrable (fun t => GT.ι (uV t)) (volume.restrict (Set.Icc 0 T)) := by
          have h := (GT.ι.comp_memLp' mem_p).integrable hp
          simpa only [Function.comp_def, ContinuousLinearMap.coe_coe] using h
        exact intervalIntegrable_smul_of_integrableOn_Icc hg
          hψC1.continuous_deriv_one (HasCompactSupport.deriv hψcs)
          (tsupport_deriv_subset.trans hψsupp))
      (fun ψ hψcs hψsupp hψC1 => by
        -- Interval-integrability of `t ↦ ψ t • u'H t` on `[0,T]`.
        -- `MemLp u'H q` (finite measure, `1 ≤ q`) ⇒ `Integrable u'H`; `ψ` is continuous,
        -- compactly supported in `Ioo 0 T`, hence bounded, so the `smul` is `L¹`.
        have hg : Integrable u'H (volume.restrict (Set.Icc 0 T)) := mem_q.integrable hq
        exact intervalIntegrable_smul_of_integrableOn_Icc hg
          hψC1.continuous hψcs hψsupp)
    -- Rewrite `L = hToVprimeCLM` back to `hToVprime` on both curves.
    simpa only [hL, GelfandTriple.hToVprimeCLM_apply] using hbase
  exact ⟨{ u' := fun t => GT.hToVprime (u'H t)
           mem_p := mem_p
           mem_q := hmem_q
           weakDeriv := hwd }⟩

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

**Isolated missing pillar `hg : AEStronglyMeasurable g μ` (statement-gate fix, Lane-D
2026-06-20).** The earlier form WITHOUT this hypothesis was FALSE: μ = Lebesgue on `[0,1]`,
`f n = 0`, `g = 𝟙_V` for a non-measurable Vitali set `V` (inner measure `0`) gives
`eLpNorm (f n - g) 2 μ = eLpNorm g 2 μ = (∫⁻ ‖g‖²)^(1/2) = 0` (the `∫⁻` of a non-measurable
function is the *lower* Lebesgue integral, whose largest measurable minorant of `‖g‖²` is `0`
a.e.), so the convergence hypothesis held yet `g` was not a.e.-strongly-measurable. Measurability
of an L²-limit genuinely CANNOT be extracted from L²-convergence alone — every
`tendstoInMeasure_of_tendsto_eLpNorm*` mathlib lemma *requires* `AEStronglyMeasurable g` as an
INPUT. So `g`'s measurability is the genuine missing pillar; we isolate it as the explicit
hypothesis `hg` (no-smuggle: it asserts ONLY measurability of `g` — no subsequence, no limit
identification, no spatial content). The lemma's real content is then the a.e.-convergent
subsequence; the first conjunct is `hg` itself, kept in the conclusion so the lemma packages
"measurable representative + a.e. subsequence" for its E1-style consumer.

**Proved this cycle** (sorry-free). Route: `tendstoInMeasure_of_tendsto_eLpNorm` (needs `hg`)
⇒ `TendstoInMeasure.exists_seq_tendsto_ae`. -/
theorem aeStronglyMeasurable_of_spaceTimeL2
    {μ : Measure ℝ} {f : ℕ → ℝ → β} {g : ℝ → β}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (hg : AEStronglyMeasurable g μ)
    (hconv : Tendsto (fun n => eLpNorm (fun t => f n t - g t) 2 μ) atTop (𝓝 0)) :
    AEStronglyMeasurable g μ ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ t ∂μ, Tendsto (fun k => f (φ k) t) atTop (𝓝 (g t)) := by
  refine ⟨hg, ?_⟩
  -- `eLpNorm (f n - g) 2 μ → 0`: the pointwise sub `fun t => f n t - g t` IS the `Pi` sub
  -- `f n - g` (definitionally), so `hconv` already has the form the mathlib lemma consumes.
  have hconv' : Tendsto (fun n => eLpNorm (f n - g) 2 μ) atTop (𝓝 0) := hconv
  -- L²-convergence ⇒ convergence in measure (uses `hg`), then extract an a.e. subsequence.
  have htim : TendstoInMeasure μ f atTop g :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) hf hg hconv'
  exact htim.exists_seq_tendsto_ae

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

**Isolated missing pillar `hg : AEStronglyMeasurable g μ` (statement-gate fix, Lane-D
2026-06-20), exactly as in `aeStronglyMeasurable_of_spaceTimeL2`.** WITHOUT it the statement is
FALSE: μ = Lebesgue on `[0,1]`, `M = 1`, `f n = 0` (so `hbound` holds), `g = 2 · 𝟙_V` for a
non-measurable Vitali set `V` gives `eLpNorm (f n - g) 2 μ = eLpNorm g 2 μ = 0` (lower integral
of a non-measurable function) so `hconv` holds, yet `{t : ‖g t‖ > 1} = V` is not contained in any
null set (positive outer measure), so `∀ᵐ t, ‖g t‖ ≤ 1` FAILS. The norm bound on the limit
genuinely needs `g` measurable. No-smuggle: `hg` asserts only measurability of `g`.

**Proved this cycle** (sorry-free), given `hg`. -/
theorem kineticEnergy_lsc_transfer {β : Type*} [NormedAddCommGroup β]
    {μ : Measure ℝ} {f : ℕ → ℝ → β} {g : ℝ → β} {M : ℝ}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (hg : AEStronglyMeasurable g μ)
    (hconv : Tendsto (fun n => eLpNorm (fun t => f n t - g t) 2 μ) atTop (𝓝 0))
    (hbound : ∀ n, ∀ᵐ t ∂μ, ‖f n t‖ ≤ M) :
    ∀ᵐ t ∂μ, ‖g t‖ ≤ M := by
  -- Extract the a.e.-convergent subsequence `f (φ k) t → g t`.
  obtain ⟨_, φ, _hφ, hae⟩ := aeStronglyMeasurable_of_spaceTimeL2 hf hg hconv
  -- The uniform bound holds for all `n` simultaneously at a.e. `t` (`ae_all_iff`).
  have hbound_all : ∀ᵐ t ∂μ, ∀ k, ‖f (φ k) t‖ ≤ M :=
    (ae_all_iff.2 fun k => hbound (φ k))
  -- At a.e. `t`: `‖f (φ k) t‖ → ‖g t‖` and `‖f (φ k) t‖ ≤ M`, so `‖g t‖ ≤ M`.
  filter_upwards [hae, hbound_all] with t htlim htbd
  exact le_of_tendsto' htlim.norm htbd

end LerayHopf.Bochner
