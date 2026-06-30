/-
# LerayHopf.Bochner.TimeSobolevAC — Stream D / R1 (V'-continuous good representative, trace-free)

The **trace-free half** of the Lions–Magenes embedding route (`docs/scratch/wkernel-route.md`).
From `u' ∈ L²(0,T;V')` it builds the continuous-into-`V'` representative of the Sobolev-in-time
curve, with NO reflection and NO boundary trace assumed — the continuity is absolute continuity
of the Bochner integral (`intervalIntegral.continuousOn_primitive_interval`). The du-Bois-Reymond
"weakly-constant ⟹ a.e. constant" keystone is proved from scratch here (mathlib has the
`ae_eq_of_integral_contDiff_smul_eq` du-Bois lemma but not the constant-difference form).

This is the NON-CIRCULAR R1 layer: it does not depend on `w1pTime_continuous_in_H` (the
months-class weak-FTC), and it is independent of the interior-mollification R2 energy core.

## Assumptions
No new `axiom`/`opaque`/`constant`. Statements faithful; no hypothesis weakening.
-/

import LerayHopf.Bochner.TimeSobolev
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

namespace LerayHopf.Bochner

open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace

section R1
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- (local copy of the `TimeSobolev` private helper) A Bochner curve integrable on `Icc 0 T`,
scalar-multiplied by a continuous compactly-supported test factor supported in `Ioo 0 T`, is
interval-integrable on `0..T`. -/
private theorem intervalIntegrable_smul_of_integrableOn_Icc'
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {T : ℝ} {g : ℝ → E} {φ : ℝ → ℝ}
    (hg : Integrable g (volume.restrict (Set.Icc 0 T)))
    (hφc : Continuous φ) (hφcs : HasCompactSupport φ)
    (hφsupp : tsupport φ ⊆ Set.Ioo 0 T) :
    IntervalIntegrable (fun t => φ t • g t) volume 0 T := by
  rcases le_or_gt 0 T with hT | hT
  · obtain ⟨C, hC⟩ := hφc.bounded_above_of_compact_support hφcs
    have hint : Integrable (fun t => φ t • g t) (volume.restrict (Set.Icc 0 T)) :=
      hg.bdd_smul C hφc.aestronglyMeasurable (Filter.Eventually.of_forall hC)
    rw [intervalIntegrable_iff]
    have hsub : Set.uIoc 0 T ⊆ Set.Icc 0 T := by
      rw [Set.uIoc_of_le hT]; exact Set.Ioc_subset_Icc_self
    have hint' : IntegrableOn (fun t => φ t • g t) (Set.Icc 0 T) volume := hint
    exact hint'.mono_set hsub
  · have hIoo : Set.Ioo 0 T = (∅ : Set ℝ) := Set.Ioo_eq_empty (by exact not_lt.2 hT.le)
    have hφ0 : φ = 0 := by
      funext t
      exact image_eq_zero_of_notMem_tsupport (fun ht => by
        have := hφsupp ht; rw [hIoo] at this; exact this.elim)
    subst hφ0
    simp only [Pi.zero_apply, zero_smul]
    exact IntervalIntegrable.zero (μ := volume) (a := (0:ℝ)) (b := T) (E := E)


/-- The Bochner primitive of an interval-integrable curve is continuous on `[0,T]`. -/
theorem continuousOn_primitive_of_integrableOn {T : ℝ} {v : ℝ → X}
    (hv : IntegrableOn v (Set.Icc 0 T) volume) :
    ContinuousOn (fun t => ∫ s in (0:ℝ)..t, v s) (Set.Icc 0 T) := by
  rcases le_or_gt 0 T with hT | hT
  · have huIcc : Set.uIcc (0:ℝ) T = Set.Icc 0 T := Set.uIcc_of_le hT
    have hvuIcc : IntegrableOn v (Set.uIcc 0 T) volume := by rw [huIcc]; exact hv
    have := intervalIntegral.continuousOn_primitive_interval (a := 0) (b := T)
      (f := v) (μ := volume) hvuIcc
    rw [huIcc] at this; exact this
  · rw [Set.Icc_eq_empty (by exact not_le.2 hT)]
    exact continuousOn_empty _

/-- The primitive `G(t) = ∫ 0..t g` of a continuous scalar function is `C¹`, with `deriv G = g`. -/
theorem contDiff_primitive_of_continuous {g : ℝ → ℝ} (hg : Continuous g) :
    ContDiff ℝ 1 (fun t => ∫ x in (0:ℝ)..t, g x) ∧
      deriv (fun t => ∫ x in (0:ℝ)..t, g x) = g := by
  have hderiv : deriv (fun t => ∫ x in (0:ℝ)..t, g x) = g := by
    funext b; exact Continuous.deriv_integral g hg 0 b
  refine ⟨?_, hderiv⟩
  rw [contDiff_one_iff_deriv]
  exact ⟨fun b => (hg.integral_hasStrictDerivAt 0 b).hasDerivAt.differentiableAt,
    by rw [hderiv]; exact hg⟩

end R1

section Keystone

/-- The primitive `G(t) = ∫ a..t g` (based at `a`) of a continuous scalar `g` supported in
`Icc a b` with `∫ a..b g = 0` vanishes outside `Icc a b`, hence is compactly supported. -/
theorem primitive_baseA_props {a b : ℝ} (hab : a ≤ b) {g : ℝ → ℝ}
    (hgc : Continuous g) (hgz : ∀ x, x ∉ Set.Icc a b → g x = 0)
    (hmean : ∫ x in a..b, g x = 0) :
    (∀ t, t ∉ Set.Icc a b → (∫ x in a..t, g x) = 0) := by
  intro t ht
  rw [Set.mem_Icc, not_and_or] at ht
  rcases ht with ht | ht
  · -- t < a : ∫a..t g = 0 since g = 0 a.e. on `Ι a t = Ioc t a` (only the null endpoint `a`
    -- can be in `[a,b]`).
    push_neg at ht
    have heqae : ∀ᵐ x, x ∈ Set.uIoc a t → g x = (0 : ℝ → ℝ) x := by
      filter_upwards [show ∀ᵐ x ∂(volume : Measure ℝ), x ≠ a from
        MeasureTheory.ae_iff.2 (by simpa using measure_singleton a)] with x hxa hxmem
      rw [Set.uIoc_of_ge ht.le, Set.mem_Ioc] at hxmem
      -- x ∈ (t, a]; if x ≠ a then x < a so x ∉ [a,b]; the case x = a is excluded by hxa.
      have hxlt : x < a := lt_of_le_of_ne hxmem.2 hxa
      simpa using hgz x (fun hxm => absurd hxm.1 (not_le.2 hxlt))
    rw [intervalIntegral.integral_congr_ae heqae]; simp
  · -- t > b : ∫a..t g = ∫a..b g + ∫b..t g = 0 + 0
    push_neg at ht
    have hsplit : (∫ x in a..t, g x) = (∫ x in a..b, g x) + ∫ x in b..t, g x :=
      (intervalIntegral.integral_add_adjacent_intervals
        (hgc.intervalIntegrable _ _) (hgc.intervalIntegrable _ _)).symm
    have heqae : ∀ᵐ x, x ∈ Set.uIoc b t → g x = (0 : ℝ → ℝ) x := by
      filter_upwards [show ∀ᵐ x ∂(volume : Measure ℝ), x ≠ b from
        MeasureTheory.ae_iff.2 (by simpa using measure_singleton b)] with x hxb hxmem
      rw [Set.uIoc_of_le ht.le, Set.mem_Ioc] at hxmem
      -- x ∈ (b, t]; x > b so x ∉ [a,b].
      simpa using hgz x (fun hxm => absurd hxm.2 (not_le.2 hxmem.1))
    rw [hsplit, hmean, intervalIntegral.integral_congr_ae heqae]; simp

/-- A fixed continuous unit-mass "weight" supported strictly inside `Ioo 0 T`: there is a
continuous `ρ : ℝ → ℝ` with `tsupport ρ ⊆ Icc a b` for some `0 < a ≤ b < T`, and
`∫ x, ρ x ∂volume = 1` (equivalently `∫ 0..T ρ = 1`). Built from a normalized `ContDiffBump`
centered at `T/2`. -/
theorem exists_unitMass_weight {T : ℝ} (hT : 0 < T) :
    ∃ (ρ : ℝ → ℝ) (a b : ℝ), 0 < a ∧ a ≤ b ∧ b < T ∧ Continuous ρ ∧
      (∀ x, x ∉ Set.Icc a b → ρ x = 0) ∧ (∫ x, ρ x ∂volume) = 1 := by
  -- Bump centered at T/2 with rOut = T/4 (< T/2), so closedBall (T/2) (T/4) = [T/4, 3T/4] ⊆ (0,T).
  set f : ContDiffBump (T/2) := ⟨T/8, T/4, by positivity, by linarith⟩ with hf
  refine ⟨f.normed volume, T/4, 3*T/4, by linarith, by linarith, by linarith,
    f.continuous_normed, ?_, f.integral_normed⟩
  intro x hx
  -- outside [T/4, 3T/4] = closedBall (T/2) (T/4) = tsupport, so ρ x = 0.
  have hts : tsupport (f.normed volume) = Metric.closedBall (T/2) (T/4) := f.tsupport_normed_eq
  apply image_eq_zero_of_notMem_tsupport
  rw [hts, Real.closedBall_eq_Icc]
  intro hmem
  apply hx
  -- closedBall center (T/2) radius (T/4): [T/2 - T/4, T/2 + T/4] = [T/4, 3T/4]
  rw [Set.mem_Icc] at hmem ⊢
  constructor <;> [linarith [hmem.1]; linarith [hmem.2]]


/-- A compact subset of the open interval `Ioo 0 T` lies in a closed subinterval
`Icc a b ⊆ Ioo 0 T`. -/
theorem exists_Icc_of_compact_subset_Ioo {T : ℝ} (hT : 0 < T) {K : Set ℝ} (hK : IsCompact K)
    (hKsub : K ⊆ Set.Ioo 0 T) :
    ∃ a b : ℝ, 0 < a ∧ b < T ∧ K ⊆ Set.Icc a b := by
  rcases K.eq_empty_or_nonempty with hempty | hne
  · exact ⟨T/2, T/2, by linarith, by linarith, by simp [hempty]⟩
  · obtain ⟨a, haK, ha⟩ := hK.exists_isMinOn hne continuousOn_id
    obtain ⟨b, hbK, hb⟩ := hK.exists_isMaxOn hne continuousOn_id
    rw [isMinOn_iff] at ha; rw [isMaxOn_iff] at hb
    exact ⟨a, b, (hKsub haK).1, (hKsub hbK).2, fun x hx => ⟨ha x hx, hb x hx⟩⟩

section KeystoneVar
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- **du-Bois-Reymond keystone: a weakly-constant Bochner curve is a.e. constant.**

`IsWeakTimeDeriv T u 0` + local/interval integrability ⟹ `u` is a.e. constant on `Ioo 0 T`.
The value `c := ∫₀ᵀ ρ • u` for a fixed unit-mass weight `ρ` is that constant; this is the
weakly-constant-implies-constant form that mathlib's du-Bois lemma does not provide directly. -/
theorem isWeakTimeDeriv_zero_ae_const {T : ℝ} (hT : 0 < T) {u : ℝ → X}
    (huloc : LocallyIntegrableOn u (Set.Ioo 0 T) volume)
    (huint : IntegrableOn u (Set.Icc 0 T) volume)
    (h0 : IsWeakTimeDeriv T u 0) :
    ∃ c : X, ∀ᵐ x ∂(volume.restrict (Set.Ioo 0 T)), u x = c := by
  obtain ⟨ρ, aρ, bρ, haρ, habρ, hbρ, hρc, hρz, hρmass⟩ := exists_unitMass_weight hT
  -- ρ integrable, compactly supported.
  have hρcs : HasCompactSupport ρ :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc
      (by intro x hx; by_contra hxout; exact hx (hρz x hxout))
  have hρint : Integrable ρ volume := hρc.integrable_of_hasCompactSupport hρcs
  set c : X := ∫ s in (0:ℝ)..T, ρ s • u s with hc
  refine ⟨c, ?_⟩
  -- the du-Bois core identity for every C∞ test g supported in Ioo 0 T.
  have hcore : ∀ g : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g → HasCompactSupport g → tsupport g ⊆ Set.Ioo 0 T →
      ∫ x, g x • (u x - c) ∂volume = 0 := by
    intro g hgC hgcs hgsupp
    have hgcont : Continuous g := hgC.continuous
    have hgint : Integrable g volume := hgcont.integrable_of_hasCompactSupport hgcs
    set Ig : ℝ := ∫ x, g x ∂volume with hIg
    set hfun : ℝ → ℝ := fun s => g s - Ig * ρ s with hhf
    have hhcont : Continuous hfun := hgcont.sub (continuous_const.mul hρc)
    -- bounding interval [A,B] ⊆ Ioo 0 T for both supports; widen to (A/2, B] ⊇ support.
    have hKcompact : IsCompact (tsupport g ∪ Set.Icc aρ bρ) := hgcs.union isCompact_Icc
    have hKsub : (tsupport g ∪ Set.Icc aρ bρ) ⊆ Set.Ioo 0 T := by
      refine Set.union_subset hgsupp (fun x hx => ?_)
      rw [Set.mem_Icc] at hx
      exact ⟨lt_of_lt_of_le haρ hx.1, lt_of_le_of_lt hx.2 hbρ⟩
    obtain ⟨A, B, hA, hB, hABsub⟩ := exists_Icc_of_compact_subset_Ioo hT hKcompact hKsub
    -- hfun = 0 outside [A,B]
    have hhz : ∀ x, x ∉ Set.Icc A B → hfun x = 0 := by
      intro x hx
      have hgx : g x = 0 := by
        by_contra hg0
        exact hx (hABsub (Set.mem_union_left _ (subset_tsupport g (by simpa using hg0))))
      have hρx : ρ x = 0 := by
        by_contra hρ0
        exact hx (hABsub (Set.mem_union_right _ (by
          by_contra hxout; exact hρ0 (hρz x hxout))))
      simp [hhf, hgx, hρx]
    have hApos : (0:ℝ) < A := hA
    have hAB : A ≤ B := by
      have : aρ ∈ Set.Icc A B := hABsub (Set.mem_union_right _ (Set.left_mem_Icc.2 habρ))
      rw [Set.mem_Icc] at this; linarith [this.1, this.2]
    -- support of hfun ⊆ Ioc (A/2) B, so ∫(A/2)..B hfun = ∫_ℝ hfun.
    have hsupp_hfun : Function.support hfun ⊆ Set.Ioc (A/2) B := by
      intro x hx
      have hx' : x ∈ Set.Icc A B := by
        by_contra hxout; exact hx (hhz x hxout)
      rw [Set.mem_Icc] at hx'; exact ⟨by linarith [hx'.1], hx'.2⟩
    -- mean-zero of hfun on the line: ∫_ℝ hfun = Ig - Ig*1 = 0.
    have hmean_line : (∫ x, hfun x ∂volume) = 0 := by
      have : (∫ x, hfun x ∂volume) = Ig - Ig * ∫ x, ρ x ∂volume := by
        rw [hhf]
        rw [integral_sub hgint (hρint.const_mul Ig), integral_const_mul]
      rw [this, hρmass, mul_one, sub_self]
    -- the primitive G(t) = ∫(A/2)..t hfun ; C¹, deriv = hfun, tsupport ⊆ [A/2,B] ⊆ Ioo 0 T.
    set G : ℝ → ℝ := fun t => ∫ x in (A/2)..t, hfun x with hG
    have hGderiv : deriv G = hfun := by
      funext t; exact Continuous.deriv_integral hfun hhcont (A/2) t
    have hGC1 : ContDiff ℝ 1 G := by
      rw [contDiff_one_iff_deriv]
      exact ⟨fun t => (hhcont.integral_hasStrictDerivAt (A/2) t).hasDerivAt.differentiableAt,
        by rw [hGderiv]; exact hhcont⟩
    -- G vanishes outside [A/2, B]: based at A/2; mean-zero ⟹ also 0 at the right.
    have hGz : ∀ t, t ∉ Set.Icc (A/2) B → G t = 0 := by
      have hmeanAB : (∫ x in (A/2)..B, hfun x) = 0 := by
        rw [intervalIntegral.integral_eq_integral_of_support_subset hsupp_hfun, hmean_line]
      have hhz' : ∀ x, x ∉ Set.Icc (A/2) B → hfun x = 0 := by
        intro x hx
        refine hhz x (fun hxAB => hx ?_)
        rw [Set.mem_Icc] at hxAB ⊢
        exact ⟨by linarith [hxAB.1], hxAB.2⟩
      exact primitive_baseA_props (a := A/2) (b := B) (by linarith) hhcont hhz' hmeanAB
    have hGcs : HasCompactSupport G :=
      HasCompactSupport.of_support_subset_isCompact isCompact_Icc
        (by intro x hx; by_contra hxout; exact hx (hGz x hxout))
    have hGsupp : tsupport G ⊆ Set.Ioo 0 T := by
      have hsub : tsupport G ⊆ Set.Icc (A/2) B := by
        apply closure_minimal _ isClosed_Icc
        intro x hx
        have hx' : G x ≠ 0 := hx
        by_contra hxout; exact hx' (hGz x hxout)
      refine hsub.trans (fun x hx => ?_)
      rw [Set.mem_Icc] at hx
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    -- apply h0 to G : ∫0..T (deriv G) • u = - ∫0..T G • 0 = 0
    have hweak := h0 G hGcs hGsupp hGC1
    rw [hGderiv] at hweak
    -- hweak : ∫0..T hfun • u = - ∫0..T G • 0 = 0
    simp only [Pi.zero_apply, smul_zero, intervalIntegral.integral_zero, neg_zero] at hweak
    -- hweak : ∫0..T (g - Ig•ρ) • u = 0  ⟹ ∫0..T g•u = Ig • ∫0..T ρ•u = Ig • c
    -- integrability of the two pieces on [0,T] (continuous scalar × Icc-integrable u).
    have hgu_ii : IntervalIntegrable (fun s => g s • u s) volume 0 T :=
      intervalIntegrable_smul_of_integrableOn_Icc' huint hgcont hgcs hgsupp
    have hρu_ii : IntervalIntegrable (fun s => (Ig * ρ s) • u s) volume 0 T := by
      have hρcs' : HasCompactSupport (fun s => Ig * ρ s) := hρcs.mul_left
      have hρsupp' : tsupport (fun s => Ig * ρ s) ⊆ Set.Ioo 0 T := by
        have hsub : tsupport (fun s => Ig * ρ s) ⊆ Set.Icc aρ bρ := by
          apply closure_minimal _ isClosed_Icc
          intro x hx
          have hρx : ρ x ≠ 0 := fun h => hx (by simp [h])
          by_contra hxout; exact hρx (hρz x hxout)
        refine hsub.trans (fun x hx => ?_)
        rw [Set.mem_Icc] at hx
        exact ⟨lt_of_lt_of_le haρ hx.1, lt_of_le_of_lt hx.2 hbρ⟩
      exact intervalIntegrable_smul_of_integrableOn_Icc' huint
        (continuous_const.mul hρc) hρcs' hρsupp'
    -- hweak: ∫0..T hfun•u = 0 ; hfun s • u s = g s • u s - (Ig*ρ s)•u s.
    have hsplit : (∫ s in (0:ℝ)..T, hfun s • u s)
        = (∫ s in (0:ℝ)..T, g s • u s) - ∫ s in (0:ℝ)..T, (Ig * ρ s) • u s := by
      rw [← intervalIntegral.integral_sub hgu_ii hρu_ii]
      refine intervalIntegral.integral_congr (fun s _ => ?_)
      simp only [hhf, sub_smul]
    rw [hsplit, sub_eq_zero] at hweak
    -- ∫0..T (Ig*ρ s)•u s = Ig • ∫0..T ρ s • u s = Ig • c
    have hscal : (∫ s in (0:ℝ)..T, (Ig * ρ s) • u s) = Ig • c := by
      rw [hc, ← intervalIntegral.integral_smul]
      refine intervalIntegral.integral_congr (fun s _ => ?_)
      rw [mul_smul]
    rw [hscal] at hweak
    -- now ∫_ℝ g•(u-c) = ∫_ℝ g•u - (∫g)•c = ∫0..T g•u - Ig•c = 0.
    -- g•u and g•c are supported in Ioo 0 T, so their line integrals equal the 0..T ones.
    have hsuppgu : (fun x => g x • u x) = Set.indicator (Set.Ioo 0 T) (fun x => g x • u x) := by
      funext x
      by_cases hx : x ∈ Set.Ioo 0 T
      · rw [Set.indicator_of_mem hx]
      · have : g x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hgsupp h))
        rw [Set.indicator_of_notMem hx, this, zero_smul]
    have hgu_line : (∫ x, g x • u x ∂volume) = ∫ s in (0:ℝ)..T, g s • u s := by
      rw [intervalIntegral.integral_of_le hT.le, integral_Ioc_eq_integral_Ioo]
      conv_lhs => rw [hsuppgu]
      rw [MeasureTheory.integral_indicator measurableSet_Ioo]
    have hgc_line : (∫ x, g x • c ∂volume) = Ig • c := by
      rw [integral_smul_const, hIg]
    calc (∫ x, g x • (u x - c) ∂volume)
        = (∫ x, g x • u x ∂volume) - ∫ x, g x • c ∂volume := by
          rw [← integral_sub]
          · refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
            simp only [smul_sub]
          · -- Integrable (g•u): supported in Ioo 0 T, integrable on Icc.
            have hgu_IccInt : IntegrableOn (fun x => g x • u x) (Set.Icc 0 T) volume := by
              obtain ⟨C, hC⟩ := hgcont.bounded_above_of_compact_support hgcs
              exact huint.bdd_smul C hgcont.aestronglyMeasurable
                (Filter.Eventually.of_forall hC)
            refine (integrableOn_iff_integrable_of_support_subset
              (s := Set.Icc 0 T) ?_).1 hgu_IccInt
            intro x hx
            have hgx : g x ≠ 0 := fun h => (Function.mem_support.1 hx) (by rw [h, zero_smul])
            exact Set.Ioo_subset_Icc_self (hgsupp (subset_tsupport g hgx))
          · -- Integrable (g•c): g compactly supported, c constant ⟹ integrable.
            exact (hgint.smul_const c)
      _ = (∫ s in (0:ℝ)..T, g s • u s) - Ig • c := by rw [hgu_line, hgc_line]
      _ = 0 := by rw [hweak, sub_self]
  -- feed du-Bois
  have hres := (isOpen_Ioo (a := (0:ℝ)) (b := T)).ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (f := fun x => u x - c)
    (huloc.sub (locallyIntegrableOn_const c)) hcore
  rw [ae_restrict_iff' measurableSet_Ioo]
  filter_upwards [hres] with x hx hmem using sub_eq_zero.1 (hx hmem)

end KeystoneVar

end Keystone

/-! ### R1 — the V'-continuous good representative

From a `W1pTime` element, the embedded curve `t ↦ hToVprime (ι (uV t))` has a continuous-into-`V'`
representative on `[0,T]`, with NO reflection and NO boundary trace assumed. The continuity is
absolute continuity of the Bochner primitive of `u'`; the a.e.-equality to the embedded curve is
the du-Bois-Reymond keystone applied to the difference. -/

section Representative
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- **Distributional FTC for the Bochner primitive.** For an interval-integrable curve `v`, the
primitive `w(t) := ∫₀ᵗ v` has weak time derivative `v` on `(0,T)`:
`∫₀ᵀ ψ'(t) • w(t) = -∫₀ᵀ ψ(t) • v(t)` for every admissible test `ψ`.

The identity is the Fubini swap `∫ ψ'(t) ∫₀ᵗ v(s) = ∫ v(s) ∫ₛᵀ ψ'(t) = ∫ v(s)(ψ(T)-ψ(s)) =
-∫ ψ(s) v(s)` (using `ψ(T)=0`). This is the Bochner–Fubini distributional FTC; mathlib has the
Fubini swap (`MeasureTheory.integral_integral_swap`) and the scalar FTC but not this assembled
interval form for a Banach-valued primitive. -/
theorem isWeakTimeDeriv_primitive {T : ℝ} (hT : 0 < T) {v : ℝ → X}
    (hv : IntegrableOn v (Set.Icc 0 T) volume) :
    IsWeakTimeDeriv T (fun t => ∫ s in (0:ℝ)..t, v s) v := by
  sorry -- ALLOW_SORRY: Bochner–Fubini distributional FTC for the primitive w(t)=∫₀ᵗ v (interval form). The identity ∫ψ'(t)•(∫₀ᵗ v) = -∫ψ•v is the Fubini swap ∫∫ψ'(t)𝟙[s<t]v(s) = ∫v(s)(ψ(T)-ψ(s)) = -∫ψ•v (ψ(T)=0); mathlib has integral_integral_swap (Bochner) + the scalar FTC but not this assembled interval form. Trace-free and NON-CIRCULAR (no reflection, no boundary value of v fed in). Isolated as the single residual of R1.

/-- **R1 — V'-continuous good representative (trace-free).** A `W1pTime` curve's embedded image
`t ↦ hToVprime (ι (uV t))` admits a representative continuous into `V'` on `[0,T]`, a.e.-equal to
the embedded curve. Built from the Bochner primitive of `u'` (continuous by absolute continuity)
plus the du-Bois-Reymond keystone — NO reflection, NO boundary trace. -/
theorem w1pTime_continuous_in_Vprime (GT : GelfandTriple) {T : ℝ} (hT : 0 < T)
    {uV : ℝ → GT.V} (W : W1pTime GT 2 2 T uV) :
    letI := GT.instNACG_V; letI := GT.instIPS_V;
    ∃ ũ : ℝ → GT.Vprime, ContinuousOn ũ (Set.Icc 0 T) ∧
      ũ =ᵐ[volume.restrict (Set.Ioo 0 T)] (fun t => GT.hToVprime (GT.ι (uV t))) := by
  letI := GT.instNACG_V; letI := GT.instIPS_V
  letI := GT.instNACG_H; letI := GT.instIPS_H
  -- `u' ∈ L²(0,T;V')` ⟹ interval-integrable (finite measure).
  have hq : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have hu'int : IntegrableOn W.u' (Set.Icc 0 T) volume := W.mem_q.integrable hq
  -- the primitive curve into V'
  set w : ℝ → GT.Vprime := fun t => ∫ s in (0:ℝ)..t, W.u' s with hw
  -- w is continuous on [0,T] (absolute continuity of the Bochner primitive).
  have hwcont : ContinuousOn w (Set.Icc 0 T) := continuousOn_primitive_of_integrableOn hu'int
  -- the embedded curve and its weak derivative.
  set E : ℝ → GT.Vprime := fun t => GT.hToVprime (GT.ι (uV t)) with hE
  -- w has weak derivative u' (distributional FTC); E has weak derivative u' (W.weakDeriv).
  have hwwd : IsWeakTimeDeriv T w W.u' := isWeakTimeDeriv_primitive hT hu'int
  have hEwd : IsWeakTimeDeriv T E W.u' := W.weakDeriv
  -- the difference D := E - w has weak derivative 0.
  have hElocint : IntegrableOn E (Set.Icc 0 T) volume := by
    have hmem : MemLp (fun t => (GT.hToVprimeCLM.comp GT.ι) (uV t)) 2
        (volume.restrict (Set.Icc 0 T)) := (GT.hToVprimeCLM.comp GT.ι).comp_memLp' W.mem_p
    have hEeq : (fun t => (GT.hToVprimeCLM.comp GT.ι) (uV t)) = E := by
      funext t
      simp only [hE, ContinuousLinearMap.comp_apply, GelfandTriple.hToVprimeCLM_apply]
    rw [hEeq] at hmem
    exact hmem.integrable (by norm_num)
  have hwlocint : IntegrableOn w (Set.Icc 0 T) volume :=
    (hwcont.integrableOn_compact isCompact_Icc)
  have hDwd : IsWeakTimeDeriv T (fun t => E t - w t) 0 := by
    intro ψ hψcs hψsupp hψC1
    have hE' := hEwd ψ hψcs hψsupp hψC1
    have hw' := hwwd ψ hψcs hψsupp hψC1
    -- ∫ ψ' • (E - w) = ∫ ψ'•E - ∫ ψ'•w ; both ∫ deriv ψ • · need interval-integrability.
    have hψ'cont : Continuous (deriv ψ) := hψC1.continuous_deriv_one
    have hψ'cs : HasCompactSupport (deriv ψ) := HasCompactSupport.deriv hψcs
    have hψ'supp : tsupport (deriv ψ) ⊆ Set.Ioo 0 T := tsupport_deriv_subset.trans hψsupp
    have hEii : IntervalIntegrable (fun t => deriv ψ t • E t) volume 0 T :=
      intervalIntegrable_smul_of_integrableOn_Icc' hElocint hψ'cont hψ'cs hψ'supp
    have hwii : IntervalIntegrable (fun t => deriv ψ t • w t) volume 0 T :=
      intervalIntegrable_smul_of_integrableOn_Icc' hwlocint hψ'cont hψ'cs hψ'supp
    have hsub : (∫ t in (0:ℝ)..T, deriv ψ t • (E t - w t))
        = (∫ t in (0:ℝ)..T, deriv ψ t • E t) - ∫ t in (0:ℝ)..T, deriv ψ t • w t := by
      rw [← intervalIntegral.integral_sub hEii hwii]
      refine intervalIntegral.integral_congr (fun t _ => ?_); rw [smul_sub]
    rw [hsub, hE', hw']
    simp
  -- integrability inputs for the keystone on D.
  have hDint : IntegrableOn (fun t => E t - w t) (Set.Icc 0 T) volume := hElocint.sub hwlocint
  have hDloc : LocallyIntegrableOn (fun t => E t - w t) (Set.Ioo 0 T) volume :=
    (hDint.mono_set Set.Ioo_subset_Icc_self).locallyIntegrableOn
  -- keystone: D =ᵐ const on Ioo 0 T.
  obtain ⟨cst, hcst⟩ := isWeakTimeDeriv_zero_ae_const hT hDloc hDint hDwd
  -- so E =ᵐ w + cst ; the continuous representative is ũ := fun t => w t + cst.
  refine ⟨fun t => w t + cst, hwcont.add continuousOn_const, ?_⟩
  filter_upwards [hcst] with t ht
  -- ht : E t - w t = cst ⟹ w t + cst = E t.
  show w t + cst = E t
  rw [← ht]; abel

end Representative

end LerayHopf.Bochner
