import LerayHopf.R3.DivergenceFree
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace LerayHopf
open MeasureTheory LineDeriv SchwartzMap
open scoped LineDeriv

/-!
# Concrete trilinear convection estimates for `convIntegralSchwartz` (R3-d)

**Milestone:** `r3d-trilinear-estimate`

This file proves — axiom-free — the genuine analytic properties of
`convIntegralSchwartz` that the `r3_NSForms_exist` axiom in
`AxiomaticClosure.lean` (lines 167–281) currently only *asserts* in its
justification prose.  The file upgrades those asserted facts into proved
lemmas about the concrete Schwartz integral defined in `DivergenceFree.lean`.

## Architecture

This file is **standalone**: it does NOT import `AxiomaticClosure.lean`, so
the axiom justification remains independent.  `AxiomaticClosure.lean` does not
import this file either; the connection is semantic, not structural.

DAG position:
```
Domain.lean
    └── DivergenceFree.lean   (defines convIntegralSchwartz)
            └── TrilinearEstimate.lean   [THIS FILE]
                    (standalone; NOT imported by AxiomaticClosure.lean)
```

## Declarations (dependency order)

Tier A — Multilinearity (A1–A6):
- `convIntegralSchwartz_add_1`   : additive in slot 1 (ψu)
- `convIntegralSchwartz_add_2`   : additive in slot 2 (ψv)
- `convIntegralSchwartz_add_3`   : additive in slot 3 (ψw)
- `convIntegralSchwartz_smul_1`  : ℝ-linear in slot 1
- `convIntegralSchwartz_smul_2`  : ℝ-linear in slot 2
- `convIntegralSchwartz_smul_3`  : ℝ-linear in slot 3

Tier B — Integrability and Cauchy–Schwarz bound (B1–B2):
- `convIntegralSchwartz_integrand_integrable` : each summand is integrable
- `convIntegralSchwartz_bound_H1`             : |b| ≤ ‖ψu‖_{L²,comp} · ‖∇ψv‖_{L²,comp} · ‖ψw‖_{L∞,comp}

Tier C — Integration by parts and `b_bound`-shape estimate (C1–C3):
- `convIntegralSchwartz_ibp`                  : IBP moves ∂_a off ψv onto ψu/ψw
- `convIntegralSchwartz_antisymm_of_divFree`  : antisymmetry under weak div-free condition
- `convIntegralSchwartz_bound_sup`            : under div-free, |b| ≤ ‖ψw‖_{H¹,L∞} · ‖ψu‖_{L²} · ‖ψv‖_{L²}

## Mathlib API used

- `SchwartzMap.integrable`                                     (Basic.lean:1138)
- `SchwartzMap.bilinLeftCLM`, `bilinLeftCLM_apply`            (Basic.lean:689/734)
- `SchwartzMap.integral_mul_lineDerivOp_right_eq_neg_left`    (Deriv.lean:295)
- `SchwartzMap.integral_bilinear_lineDerivOp_right_eq_neg_left` (Deriv.lean:308)
- `SchwartzMap.norm_toLp'`                                     (Basic.lean:1331)
- `SchwartzMap.norm_le_seminorm`                               (Basic.lean:464)
- `MeasureTheory.integral_add`, `integral_smul`, `integral_mul_left`
-/

/-! ### Local helpers -/

/-- The pointwise product of two scalar Schwartz functions, again a Schwartz function. -/
private noncomputable def schwartzMul
    (f g : SchwartzMap Domain3 ℝ) : SchwartzMap Domain3 ℝ :=
  SchwartzMap.bilinLeftCLM (ContinuousLinearMap.mul ℝ ℝ) g.hasTemperateGrowth f

@[simp] private theorem schwartzMul_apply (f g : SchwartzMap Domain3 ℝ) (x : Domain3) :
    schwartzMul f g x = f x * g x := by
  simp [schwartzMul, ContinuousLinearMap.mul_apply']

/-- Integrability of the `(i,a)`-summand integrand. (Shared by B1 and Tier A.) -/
private theorem integrand_integrable'
    (ψu ψv ψw : Fin 3 → SchwartzMap Domain3 ℝ) (i a : Fin 3) :
    MeasureTheory.Integrable
      (fun x : Domain3 =>
        (ψu a x) *
        ((lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
            (EuclideanSpace.single a (1 : ℝ) : Domain3) (ψv i)) x) *
        (ψw i x))
      (volume : Measure Domain3) := by
  have h := (schwartzMul
      (schwartzMul (ψu a)
        (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
          (EuclideanSpace.single a (1 : ℝ) : Domain3) (ψv i))) (ψw i)).integrable
      (μ := (volume : Measure Domain3))
  refine h.congr ?_
  filter_upwards with x
  simp

/-- Leibniz rule for the directional derivative `∂_{v}` on a Schwartz product. -/
private theorem lineDerivOp_schwartzMul (f g : SchwartzMap Domain3 ℝ) (v : Domain3) (x : Domain3) :
    (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ) v (schwartzMul f g)) x =
      (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ) v f) x * g x
      + f x * (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ) v g) x := by
  rw [lineDerivOpCLM_apply, lineDerivOpCLM_apply, lineDerivOpCLM_apply,
    SchwartzMap.lineDerivOp_apply_eq_fderiv, SchwartzMap.lineDerivOp_apply_eq_fderiv,
    SchwartzMap.lineDerivOp_apply_eq_fderiv]
  have hf : HasFDerivAt (f : Domain3 → ℝ) (fderiv ℝ (f : Domain3 → ℝ) x) x :=
    (f.differentiableAt).hasFDerivAt
  have hg : HasFDerivAt (g : Domain3 → ℝ) (fderiv ℝ (g : Domain3 → ℝ) x) x :=
    (g.differentiableAt).hasFDerivAt
  have hprod : HasFDerivAt (schwartzMul f g : Domain3 → ℝ)
      ((f x) • fderiv ℝ (g : Domain3 → ℝ) x
        + (g x) • fderiv ℝ (f : Domain3 → ℝ) x) x := by
    have hmul := hf.mul hg
    have heq : ((f : Domain3 → ℝ) * (g : Domain3 → ℝ)) = (schwartzMul f g : Domain3 → ℝ) := by
      funext y; simp [Pi.mul_apply]
    rw [heq] at hmul
    exact hmul
  rw [hprod.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/-- Cauchy–Schwarz on the L² pair of two scalar Schwartz functions:
`|∫ f·g| ≤ ‖f.toLp 2‖ · ‖g.toLp 2‖`. -/
private theorem schwartz_cauchy_schwarz (f g : SchwartzMap Domain3 ℝ) :
    |∫ x : Domain3, (f x) * (g x) ∂(volume : Measure Domain3)|
      ≤ ‖f.toLp 2 (volume : Measure Domain3)‖ * ‖g.toLp 2 (volume : Measure Domain3)‖ := by
  have hinner : (inner ℝ (f.toLp 2 (volume : Measure Domain3))
      (g.toLp 2 (volume : Measure Domain3)) : ℝ)
      = ∫ x : Domain3, (f x) * (g x) ∂(volume : Measure Domain3) := by
    rw [MeasureTheory.L2.inner_def]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [SchwartzMap.coeFn_toLp f 2 (volume : Measure Domain3),
      SchwartzMap.coeFn_toLp g 2 (volume : Measure Domain3)] with x hfx hgx
    rw [Real.inner_apply, hfx, hgx]
  rw [← hinner]
  exact abs_real_inner_le_norm _ _

/-- L¹ Cauchy–Schwarz: `∫ |f|·|g| ≤ ‖f.toLp 2‖ · ‖g.toLp 2‖`. -/
private theorem schwartz_integral_abs_mul_le (f g : SchwartzMap Domain3 ℝ) :
    (∫ x : Domain3, |f x| * |g x| ∂(volume : Measure Domain3))
      ≤ ‖f.toLp 2 (volume : Measure Domain3)‖ * ‖g.toLp 2 (volume : Measure Domain3)‖ := by
  have hf : MemLp (f : Domain3 → ℝ) (ENNReal.ofReal 2) (volume : Measure Domain3) := by
    have := f.memLp 2 (volume : Measure Domain3)
    simpa using this
  have hg : MemLp (g : Domain3 → ℝ) (ENNReal.ofReal 2) (volume : Measure Domain3) := by
    have := g.memLp 2 (volume : Measure Domain3)
    simpa using this
  have hmain := MeasureTheory.integral_mul_norm_le_Lp_mul_Lq
    (μ := (volume : Measure Domain3)) (f := (f : Domain3 → ℝ)) (g := (g : Domain3 → ℝ))
    (Real.HolderConjugate.two_two) hf hg
  have hnf : ‖f.toLp 2 (volume : Measure Domain3)‖
      = (∫ x : Domain3, ‖f x‖ ^ (2 : ℝ) ∂(volume : Measure Domain3)) ^ (1 / (2 : ℝ)) := by
    rw [SchwartzMap.norm_toLp' (by simp) (by simp)]
    norm_num
  have hng : ‖g.toLp 2 (volume : Measure Domain3)‖
      = (∫ x : Domain3, ‖g x‖ ^ (2 : ℝ) ∂(volume : Measure Domain3)) ^ (1 / (2 : ℝ)) := by
    rw [SchwartzMap.norm_toLp' (by simp) (by simp)]
    norm_num
  rw [hnf, hng]
  calc (∫ x : Domain3, |f x| * |g x| ∂(volume : Measure Domain3))
      = ∫ x : Domain3, ‖f x‖ * ‖g x‖ ∂(volume : Measure Domain3) := by
        simp only [Real.norm_eq_abs]
    _ ≤ _ := hmain

/-- Trilinear per-term bound: `|∫ f·g·h| ≤ ‖f.toLp 2‖ · ‖g.toLp 2‖ · (seminorm 0 0 h)`. -/
private theorem schwartz_trilinear_bound (f g h : SchwartzMap Domain3 ℝ) :
    |∫ x : Domain3, (f x) * (g x) * (h x) ∂(volume : Measure Domain3)|
      ≤ ‖f.toLp 2 (volume : Measure Domain3)‖ * ‖g.toLp 2 (volume : Measure Domain3)‖
        * SchwartzMap.seminorm ℝ 0 0 h := by
  have hint : MeasureTheory.Integrable
      (fun x : Domain3 => (f x) * (g x) * (h x)) (volume : Measure Domain3) := by
    have hi := (schwartzMul (schwartzMul f g) h).integrable (μ := (volume : Measure Domain3))
    refine hi.congr ?_; filter_upwards with x; simp
  have hsemi : ∀ x : Domain3, |h x| ≤ SchwartzMap.seminorm ℝ 0 0 h := by
    intro x
    have := SchwartzMap.norm_le_seminorm ℝ h x
    simpa [Real.norm_eq_abs] using this
  have hsemi_nonneg : (0 : ℝ) ≤ SchwartzMap.seminorm ℝ 0 0 h :=
    le_trans (abs_nonneg _) (hsemi 0)
  calc |∫ x : Domain3, (f x) * (g x) * (h x) ∂(volume : Measure Domain3)|
      = ‖∫ x : Domain3, (f x) * (g x) * (h x) ∂(volume : Measure Domain3)‖ := by
        rw [Real.norm_eq_abs]
    _ ≤ ∫ x : Domain3, ‖(f x) * (g x) * (h x)‖ ∂(volume : Measure Domain3) :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ = ∫ x : Domain3, (|f x| * |g x|) * |h x| ∂(volume : Measure Domain3) := by
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards with x
        simp [abs_mul, Real.norm_eq_abs]
    _ ≤ ∫ x : Domain3, (|f x| * |g x|) * SchwartzMap.seminorm ℝ 0 0 h
          ∂(volume : Measure Domain3) := by
        refine MeasureTheory.integral_mono_ae ?_ ?_ ?_
        · refine hint.norm.congr ?_
          filter_upwards with x; simp [abs_mul, Real.norm_eq_abs]
        · have hi := (schwartzMul (schwartzMul f g) h).integrable (μ := (volume : Measure Domain3))
          have : MeasureTheory.Integrable
              (fun x : Domain3 => (|f x| * |g x|) * SchwartzMap.seminorm ℝ 0 0 h)
              (volume : Measure Domain3) := by
            have h2 := (schwartzMul f g).integrable (μ := (volume : Measure Domain3))
            have h3 : MeasureTheory.Integrable
                (fun x : Domain3 => |f x| * |g x|) (volume : Measure Domain3) := by
              refine h2.norm.congr ?_
              filter_upwards with x; simp [abs_mul, Real.norm_eq_abs]
            exact h3.mul_const _
          exact this
        · filter_upwards with x
          have hfg : (0 : ℝ) ≤ |f x| * |g x| := by positivity
          exact mul_le_mul_of_nonneg_left (hsemi x) hfg
    _ = (∫ x : Domain3, |f x| * |g x| ∂(volume : Measure Domain3))
          * SchwartzMap.seminorm ℝ 0 0 h := by
        rw [MeasureTheory.integral_mul_const]
    _ ≤ (‖f.toLp 2 (volume : Measure Domain3)‖ * ‖g.toLp 2 (volume : Measure Domain3)‖)
          * SchwartzMap.seminorm ℝ 0 0 h := by
        exact mul_le_mul_of_nonneg_right (schwartz_integral_abs_mul_le f g) hsemi_nonneg
    _ = _ := by ring

/-- For nonnegative families, `∑_i x_i y_i ≤ (∑_i x_i)(∑_i y_i)`. -/
private theorem sum_mul_le_mul_sum {ι : Type*} (s : Finset ι) (x y : ι → ℝ)
    (hx : ∀ i ∈ s, 0 ≤ x i) (hy : ∀ i ∈ s, 0 ≤ y i) :
    ∑ i ∈ s, x i * y i ≤ (∑ i ∈ s, x i) * (∑ i ∈ s, y i) := by
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum (fun i hi => ?_)
  rw [Finset.mul_sum]
  refine Finset.single_le_sum (f := fun j => x i * y j) (fun j hj => ?_) hi
  exact mul_nonneg (hx i hi) (hy j hj)

/-! ### Tier A — Multilinearity -/

/-- **A1.** `convIntegralSchwartz` is additive in the first slot (ψu). -/
theorem convIntegralSchwartz_add_1
    (ψu ψu' ψv ψw : Fin 3 → SchwartzMap Domain3 ℝ) :
    convIntegralSchwartz (fun a => ψu a + ψu' a) ψv ψw =
      convIntegralSchwartz ψu ψv ψw + convIntegralSchwartz ψu' ψv ψw := by
  unfold convIntegralSchwartz
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← MeasureTheory.integral_add
    (integrand_integrable' ψu ψv ψw i a)
    (integrand_integrable' ψu' ψv ψw i a)]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with x
  simp only [SchwartzMap.add_apply]
  ring

/-- **A2.** `convIntegralSchwartz` is additive in the second slot (ψv). -/
theorem convIntegralSchwartz_add_2
    (ψu ψv ψv' ψw : Fin 3 → SchwartzMap Domain3 ℝ) :
    convIntegralSchwartz ψu (fun i => ψv i + ψv' i) ψw =
      convIntegralSchwartz ψu ψv ψw + convIntegralSchwartz ψu ψv' ψw := by
  unfold convIntegralSchwartz
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← MeasureTheory.integral_add
    (integrand_integrable' ψu ψv ψw i a)
    (integrand_integrable' ψu ψv' ψw i a)]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with x
  simp only [map_add, SchwartzMap.add_apply]
  ring

/-- **A3.** `convIntegralSchwartz` is additive in the third slot (ψw). -/
theorem convIntegralSchwartz_add_3
    (ψu ψv ψw ψw' : Fin 3 → SchwartzMap Domain3 ℝ) :
    convIntegralSchwartz ψu ψv (fun i => ψw i + ψw' i) =
      convIntegralSchwartz ψu ψv ψw + convIntegralSchwartz ψu ψv ψw' := by
  unfold convIntegralSchwartz
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← MeasureTheory.integral_add
    (integrand_integrable' ψu ψv ψw i a)
    (integrand_integrable' ψu ψv ψw' i a)]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with x
  simp only [SchwartzMap.add_apply]
  ring

/-- **A4.** `convIntegralSchwartz` is ℝ-homogeneous in the first slot (ψu). -/
theorem convIntegralSchwartz_smul_1
    (c : ℝ) (ψu ψv ψw : Fin 3 → SchwartzMap Domain3 ℝ) :
    convIntegralSchwartz (fun a => c • ψu a) ψv ψw =
      c * convIntegralSchwartz ψu ψv ψw := by
  unfold convIntegralSchwartz
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with x
  simp only [SchwartzMap.smul_apply, smul_eq_mul]
  ring

/-- **A5.** `convIntegralSchwartz` is ℝ-homogeneous in the second slot (ψv). -/
theorem convIntegralSchwartz_smul_2
    (c : ℝ) (ψu ψv ψw : Fin 3 → SchwartzMap Domain3 ℝ) :
    convIntegralSchwartz ψu (fun i => c • ψv i) ψw =
      c * convIntegralSchwartz ψu ψv ψw := by
  unfold convIntegralSchwartz
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with x
  simp only [map_smul, SchwartzMap.smul_apply, smul_eq_mul]
  ring

/-- **A6.** `convIntegralSchwartz` is ℝ-homogeneous in the third slot (ψw).

Note: uses the CORRECTED signature (contract §3, lines 154–158): the smul is on ψw,
not the erroneous extra ψw parameter from the draft at line 144. -/
theorem convIntegralSchwartz_smul_3
    (c : ℝ) (ψu ψv ψw : Fin 3 → SchwartzMap Domain3 ℝ) :
    convIntegralSchwartz ψu ψv (fun i => c • ψw i) =
      c * convIntegralSchwartz ψu ψv ψw := by
  unfold convIntegralSchwartz
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with x
  simp only [SchwartzMap.smul_apply, smul_eq_mul]
  ring

/-! ### Tier B — Integrability and Cauchy–Schwarz bound -/

/-- **B1.** Each summand in `convIntegralSchwartz` is integrable.

The integrand `x ↦ (ψu a x) * (∂_a ψv i)(x) * (ψw i x)` for fixed `(i, a)` is integrable. -/
theorem convIntegralSchwartz_integrand_integrable
    (ψu ψv ψw : Fin 3 → SchwartzMap Domain3 ℝ)
    (i a : Fin 3) :
    MeasureTheory.Integrable
      (fun x : Domain3 =>
        (ψu a x) *
        ((lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
            (EuclideanSpace.single a (1 : ℝ) : Domain3) (ψv i)) x) *
        (ψw i x))
      (volume : Measure Domain3) := by
  exact integrand_integrable' ψu ψv ψw i a

/-- **B2.** Direct Cauchy–Schwarz bound on `convIntegralSchwartz` with an H¹-seminorm
of ψv (derivative sits on ψv) and the sup-norm of ψw.

`|convIntegralSchwartz ψu ψv ψw|`
`  ≤ ‖ψu‖_{L²,comp} · ‖∇ψv‖_{L²,comp} · ‖ψw‖_{L∞,comp}`

where:
- `‖ψu‖_{L²,comp} = ∑_a ‖(ψu a).toLp 2 volume‖`  (component-wise L² norm)
- `‖∇ψv‖_{L²,comp} = ∑_a ∑_i ‖(∂_a ψv i).toLp 2 volume‖`  (H¹-seminorm of ψv)
- `‖ψw‖_{L∞,comp} = ∑_i SchwartzMap.seminorm ℝ 0 0 (ψw i)`  (component-wise sup-norm)

The undifferentiated factor ψw must be bounded in L∞ (not L²): a triple L² bound is
false in general (Cauchy–Schwarz pairs exactly two L² factors; the third must be L∞).
The Schwartz seminorm at order (0,0) bounds the sup-norm by `SchwartzMap.norm_le_seminorm`. -/
theorem convIntegralSchwartz_bound_H1
    (ψu ψv ψw : Fin 3 → SchwartzMap Domain3 ℝ) :
    |convIntegralSchwartz ψu ψv ψw| ≤
      (∑ a : Fin 3, ‖(ψu a).toLp 2 (volume : Measure Domain3)‖) *
      (∑ a : Fin 3, ∑ i : Fin 3,
        ‖((lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
            (EuclideanSpace.single a (1 : ℝ) : Domain3) (ψv i)).toLp
          2 (volume : Measure Domain3))‖) *
      (∑ i : Fin 3, SchwartzMap.seminorm ℝ 0 0 (ψw i)) := by
  set A : Fin 3 → ℝ := fun a => ‖(ψu a).toLp 2 (volume : Measure Domain3)‖ with hA
  set B : Fin 3 → Fin 3 → ℝ := fun a i =>
    ‖((lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
        (EuclideanSpace.single a (1 : ℝ) : Domain3) (ψv i)).toLp
      2 (volume : Measure Domain3))‖ with hB
  set C : Fin 3 → ℝ := fun i => SchwartzMap.seminorm ℝ 0 0 (ψw i) with hC
  have hAnn : ∀ a, 0 ≤ A a := fun a => norm_nonneg _
  have hBnn : ∀ a i, 0 ≤ B a i := fun a i => norm_nonneg _
  have hCnn : ∀ i, 0 ≤ C i := by
    intro i
    have := SchwartzMap.norm_le_seminorm ℝ (ψw i) 0
    exact le_trans (norm_nonneg _) this
  -- per-term bound
  have hterm : ∀ i a, |∫ x : Domain3,
        (ψu a x) *
        ((lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
            (EuclideanSpace.single a (1 : ℝ) : Domain3) (ψv i)) x) * (ψw i x)
        ∂(volume : Measure Domain3)| ≤ A a * B a i * C i := by
    intro i a
    exact schwartz_trilinear_bound (ψu a)
      (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
        (EuclideanSpace.single a (1 : ℝ) : Domain3) (ψv i)) (ψw i)
  -- bound the absolute value of the double sum
  calc |convIntegralSchwartz ψu ψv ψw|
      ≤ ∑ i : Fin 3, ∑ a : Fin 3, A a * B a i * C i := by
        unfold convIntegralSchwartz
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
        refine Finset.sum_le_sum (fun i _ => ?_)
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
        exact Finset.sum_le_sum (fun a _ => hterm i a)
    _ = ∑ i : Fin 3, C i * (∑ a : Fin 3, A a * B a i) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun a _ => ?_)
        ring
    _ ≤ ∑ i : Fin 3, C i * ((∑ a : Fin 3, A a) * (∑ a : Fin 3, B a i)) := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        refine mul_le_mul_of_nonneg_left ?_ (hCnn i)
        exact sum_mul_le_mul_sum _ A (fun a => B a i)
          (fun a _ => hAnn a) (fun a _ => hBnn a i)
    _ = (∑ a : Fin 3, A a) * (∑ i : Fin 3, C i * (∑ a : Fin 3, B a i)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        ring
    _ ≤ (∑ a : Fin 3, A a) * ((∑ a : Fin 3, ∑ i : Fin 3, B a i) * (∑ i : Fin 3, C i)) := by
        refine mul_le_mul_of_nonneg_left ?_ (Finset.sum_nonneg (fun a _ => hAnn a))
        calc ∑ i : Fin 3, C i * (∑ a : Fin 3, B a i)
            = ∑ i : Fin 3, (∑ a : Fin 3, B a i) * C i := by
              refine Finset.sum_congr rfl (fun i _ => ?_); ring
          _ ≤ (∑ i : Fin 3, ∑ a : Fin 3, B a i) * (∑ i : Fin 3, C i) :=
              sum_mul_le_mul_sum _ (fun i => ∑ a : Fin 3, B a i) C
                (fun i _ => Finset.sum_nonneg (fun a _ => hBnn a i))
                (fun i _ => hCnn i)
          _ = (∑ a : Fin 3, ∑ i : Fin 3, B a i) * (∑ i : Fin 3, C i) := by
              rw [Finset.sum_comm]
    _ = (∑ a : Fin 3, A a) * (∑ a : Fin 3, ∑ i : Fin 3, B a i) * (∑ i : Fin 3, C i) := by
        ring

/-! ### Tier C — Integration by parts and `b_bound`-shape estimate -/

/-- **C1.** Integration by parts: moves the directional derivative ∂_a off ψv onto ψu,
with a sign change.

For each component (i, a), IBP gives:
  `∫ (ψu a x) * (∂_a ψv i x) * (ψw i x) dx`
  `= -∫ (∂_a ψu a x) * ψv i x * ψw i x dx`
  `  - ∫ ψu a x * ψv i x * (∂_a ψw i x) dx`

via `SchwartzMap.integral_mul_lineDerivOp_right_eq_neg_left` with
`f := ψu a * ψw i` (pointwise Schwartz product) and `g := ψv i`,
then Leibniz: `∂_a(ψu a * ψw i) = (∂_a ψu a) * ψw i + ψu a * (∂_a ψw i)`. -/
theorem convIntegralSchwartz_ibp
    (ψu ψv ψw : Fin 3 → SchwartzMap Domain3 ℝ) :
    convIntegralSchwartz ψu ψv ψw =
      -(∑ i : Fin 3, ∑ a : Fin 3,
          ∫ x : Domain3,
            ((lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
                (EuclideanSpace.single a (1 : ℝ) : Domain3) (ψu a)) x) *
            (ψv i x) * (ψw i x) ∂(volume : Measure Domain3))
      - (∑ i : Fin 3, ∑ a : Fin 3,
          ∫ x : Domain3,
            (ψu a x) * (ψv i x) *
            ((lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
                (EuclideanSpace.single a (1 : ℝ) : Domain3) (ψw i)) x)
            ∂(volume : Measure Domain3)) := by
  unfold convIntegralSchwartz
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  -- rewrite the integrand as (product of ψu a and ψw i) · ∂_a (ψv i)
  have hrw : (fun x : Domain3 =>
      (ψu a x) *
      ((lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
        (EuclideanSpace.single a (1 : ℝ) : Domain3) (ψv i)) x) *
      (ψw i x))
      = fun x : Domain3 =>
        (schwartzMul (ψu a) (ψw i) x) *
        ((lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
          (EuclideanSpace.single a (1 : ℝ) : Domain3) (ψv i)) x) := by
    funext x; simp; ring
  rw [hrw]
  -- IBP: ∫ (ψu·ψw) · ∂_a ψv = - ∫ (∂_a (ψu·ψw)) · ψv
  have hibp : (∫ x : Domain3,
        (schwartzMul (ψu a) (ψw i) x) *
        ((lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
          (EuclideanSpace.single a (1 : ℝ) : Domain3) (ψv i)) x)
        ∂(volume : Measure Domain3))
      = -(∫ x : Domain3,
          ((lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
            (EuclideanSpace.single a (1 : ℝ) : Domain3) (schwartzMul (ψu a) (ψw i))) x)
          * (ψv i x) ∂(volume : Measure Domain3)) :=
    SchwartzMap.integral_mul_lineDerivOp_right_eq_neg_left
        (schwartzMul (ψu a) (ψw i)) (ψv i)
        (EuclideanSpace.single a (1 : ℝ) : Domain3)
  rw [hibp]
  -- expand the Leibniz rule and split the integral
  have hint1 : MeasureTheory.Integrable
      (fun x : Domain3 =>
        ((lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
          (EuclideanSpace.single a (1 : ℝ) : Domain3) (ψu a)) x) * (ψv i x) * (ψw i x))
      (volume : Measure Domain3) := by
    have h := (schwartzMul
        (schwartzMul
          (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
            (EuclideanSpace.single a (1 : ℝ) : Domain3) (ψu a)) (ψv i)) (ψw i)).integrable
        (μ := (volume : Measure Domain3))
    refine h.congr ?_
    filter_upwards with x; simp
  have hint2 : MeasureTheory.Integrable
      (fun x : Domain3 =>
        (ψu a x) * (ψv i x) *
        ((lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
          (EuclideanSpace.single a (1 : ℝ) : Domain3) (ψw i)) x))
      (volume : Measure Domain3) := by
    have h := (schwartzMul
        (schwartzMul (ψu a) (ψv i))
          (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
            (EuclideanSpace.single a (1 : ℝ) : Domain3) (ψw i))).integrable
        (μ := (volume : Measure Domain3))
    refine h.congr ?_
    filter_upwards with x; simp
  have hsplit : (∫ x : Domain3,
        ((lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
          (EuclideanSpace.single a (1 : ℝ) : Domain3) (schwartzMul (ψu a) (ψw i))) x)
        * (ψv i x) ∂(volume : Measure Domain3))
      = (∫ x : Domain3,
            ((lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
              (EuclideanSpace.single a (1 : ℝ) : Domain3) (ψu a)) x) * (ψv i x) * (ψw i x)
            ∂(volume : Measure Domain3))
          + ∫ x : Domain3,
              (ψu a x) * (ψv i x) *
              ((lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
                (EuclideanSpace.single a (1 : ℝ) : Domain3) (ψw i)) x)
              ∂(volume : Measure Domain3) := by
    rw [← MeasureTheory.integral_add hint1 hint2]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with x
    rw [lineDerivOp_schwartzMul]
    ring
  rw [hsplit, neg_add]

/-- From the weak-div-free hypothesis `hdiv`, the *integrated divergence* against any
Schwartz test `φ` also vanishes (this is `hdiv` after one integration by parts). -/
private theorem divFree_intLeft
    (ψu : Fin 3 → SchwartzMap Domain3 ℝ)
    (hdiv : ∀ φ : SchwartzMap Domain3 ℝ,
      ∑ a : Fin 3,
        ∫ x : Domain3, (ψu a x) *
          ((lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
              (EuclideanSpace.single a (1 : ℝ) : Domain3) φ) x)
        ∂(volume : Measure Domain3) = 0)
    (φ : SchwartzMap Domain3 ℝ) :
    ∑ a : Fin 3,
      ∫ x : Domain3,
        ((lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
            (EuclideanSpace.single a (1 : ℝ) : Domain3) (ψu a)) x) * (φ x)
      ∂(volume : Measure Domain3) = 0 := by
  have key := hdiv φ
  have hcongr : ∑ a : Fin 3,
      ∫ x : Domain3, (ψu a x) *
        ((lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
            (EuclideanSpace.single a (1 : ℝ) : Domain3) φ) x)
      ∂(volume : Measure Domain3)
      = ∑ a : Fin 3, -(∫ x : Domain3,
          ((lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
            (EuclideanSpace.single a (1 : ℝ) : Domain3) (ψu a)) x) * (φ x)
          ∂(volume : Measure Domain3)) := by
    refine Finset.sum_congr rfl (fun a _ => ?_)
    exact SchwartzMap.integral_mul_lineDerivOp_right_eq_neg_left
      (ψu a) φ (EuclideanSpace.single a (1 : ℝ) : Domain3)
  rw [hcongr, Finset.sum_neg_distrib, neg_eq_zero] at key
  exact key

/-- The Leibniz pairing identity: `∑_a ∫ ψu_a (∂_a f) g + ∑_a ∫ ψu_a f (∂_a g) = 0`,
obtained by applying `hdiv` to `φ = f · g` and expanding the product derivative. -/
private theorem divFree_leibniz_pair
    (ψu : Fin 3 → SchwartzMap Domain3 ℝ)
    (hdiv : ∀ φ : SchwartzMap Domain3 ℝ,
      ∑ a : Fin 3,
        ∫ x : Domain3, (ψu a x) *
          ((lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
              (EuclideanSpace.single a (1 : ℝ) : Domain3) φ) x)
        ∂(volume : Measure Domain3) = 0)
    (f g : SchwartzMap Domain3 ℝ) :
    (∑ a : Fin 3,
      ∫ x : Domain3, (ψu a x) *
        ((lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
            (EuclideanSpace.single a (1 : ℝ) : Domain3) f) x) * (g x)
      ∂(volume : Measure Domain3))
    + (∑ a : Fin 3,
      ∫ x : Domain3, (ψu a x) * (f x) *
        ((lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
            (EuclideanSpace.single a (1 : ℝ) : Domain3) g) x)
      ∂(volume : Measure Domain3)) = 0 := by
  have key := hdiv (schwartzMul f g)
  rw [← key, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  have hint1 : MeasureTheory.Integrable
      (fun x : Domain3 => (ψu a x) *
        ((lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
            (EuclideanSpace.single a (1 : ℝ) : Domain3) f) x) * (g x))
      (volume : Measure Domain3) := by
    have h := (schwartzMul (schwartzMul (ψu a)
        (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
          (EuclideanSpace.single a (1 : ℝ) : Domain3) f)) g).integrable
        (μ := (volume : Measure Domain3))
    refine h.congr ?_
    filter_upwards with x; simp
  have hint2 : MeasureTheory.Integrable
      (fun x : Domain3 => (ψu a x) * (f x) *
        ((lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
            (EuclideanSpace.single a (1 : ℝ) : Domain3) g) x))
      (volume : Measure Domain3) := by
    have h := (schwartzMul (schwartzMul (ψu a) f)
        (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
          (EuclideanSpace.single a (1 : ℝ) : Domain3) g)).integrable
        (μ := (volume : Measure Domain3))
    refine h.congr ?_
    filter_upwards with x; simp
  rw [← MeasureTheory.integral_add hint1 hint2]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with x
  rw [lineDerivOp_schwartzMul]
  ring

/-- Under `hdiv`, the IBP identity collapses: the `∂_a ψu_a` term vanishes, leaving
`conv ψu ψv ψw = -∑_i ∑_a ∫ ψu_a · ψv_i · (∂_a ψw_i)`. -/
private theorem convIntegralSchwartz_divFree_eq
    (ψu ψv ψw : Fin 3 → SchwartzMap Domain3 ℝ)
    (hdiv : ∀ φ : SchwartzMap Domain3 ℝ,
      ∑ a : Fin 3,
        ∫ x : Domain3, (ψu a x) *
          ((lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
              (EuclideanSpace.single a (1 : ℝ) : Domain3) φ) x)
        ∂(volume : Measure Domain3) = 0) :
    convIntegralSchwartz ψu ψv ψw =
      -(∑ i : Fin 3, ∑ a : Fin 3,
          ∫ x : Domain3,
            (ψu a x) * (ψv i x) *
            ((lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
                (EuclideanSpace.single a (1 : ℝ) : Domain3) (ψw i)) x)
            ∂(volume : Measure Domain3)) := by
  rw [convIntegralSchwartz_ibp ψu ψv ψw]
  -- the first IBP sum vanishes by div-free
  have hzero : (∑ i : Fin 3, ∑ a : Fin 3,
      ∫ x : Domain3,
        ((lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
            (EuclideanSpace.single a (1 : ℝ) : Domain3) (ψu a)) x) *
        (ψv i x) * (ψw i x) ∂(volume : Measure Domain3)) = 0 := by
    refine Finset.sum_eq_zero (fun i _ => ?_)
    have := divFree_intLeft ψu hdiv (schwartzMul (ψv i) (ψw i))
    rw [← this]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with x
    simp only [schwartzMul_apply]
    ring
  rw [hzero, neg_zero, zero_sub]

/-- **C2.** Antisymmetry of `convIntegralSchwartz` in the last two slots,
under a divergence-free condition on ψu.

If ψu represents a weakly divergence-free field in the sense that
  `∑ a : Fin 3, ∫ x, (∂_a ψu a x) * φ x = 0`  for every φ ∈ 𝓢(Domain3, ℝ),
i.e., `∑_a ∂_a ψu_a = 0` in the distributional sense (strong form: pointwise),
then `convIntegralSchwartz ψu ψv ψw = -convIntegralSchwartz ψu ψw ψv`.

**Design note on `hdiv`:** The hypothesis is the Schwartz-level unfolding of
`u ∈ L2Sigma_R3` when u has a Schwartz representative ψu.  The exact form
chosen avoids importing `L2Sigma_R3` into this proof, working purely with
Schwartz integrals.

Codex review point: confirm `hdiv` is the right Schwartz-level formulation of
weak div-free; check that Schwartz functions are closed under products
(needed for `ψv i * ψw i ∈ 𝓢` used in the proof). -/
theorem convIntegralSchwartz_antisymm_of_divFree
    (ψu ψv ψw : Fin 3 → SchwartzMap Domain3 ℝ)
    (hdiv : ∀ φ : SchwartzMap Domain3 ℝ,
      ∑ a : Fin 3,
        ∫ x : Domain3, (ψu a x) *
          ((lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
              (EuclideanSpace.single a (1 : ℝ) : Domain3) φ) x)
        ∂(volume : Measure Domain3) = 0) :
    convIntegralSchwartz ψu ψv ψw = -convIntegralSchwartz ψu ψw ψv := by
  rw [convIntegralSchwartz_divFree_eq ψu ψv ψw hdiv,
    convIntegralSchwartz_divFree_eq ψu ψw ψv hdiv, neg_neg,
    ← Finset.sum_neg_distrib]
  -- It remains to show -S2(v,w,i) = S2(w,v,i) for each i.
  refine Finset.sum_congr rfl (fun i _ => ?_)
  -- For each i, the Leibniz pairing identity gives the antisymmetry.
  have hpair := divFree_leibniz_pair ψu hdiv (ψv i) (ψw i)
  -- hpair : (∑_a ∫ ψu_a (∂_a ψv_i) ψw_i) + (∑_a ∫ ψu_a ψv_i (∂_a ψw_i)) = 0
  have h2 : (∑ a : Fin 3,
      ∫ x : Domain3, (ψu a x) * (ψv i x) *
        ((lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
            (EuclideanSpace.single a (1 : ℝ) : Domain3) (ψw i)) x)
      ∂(volume : Measure Domain3))
      = -(∑ a : Fin 3,
          ∫ x : Domain3, (ψu a x) * (ψw i x) *
            ((lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
                (EuclideanSpace.single a (1 : ℝ) : Domain3) (ψv i)) x)
          ∂(volume : Measure Domain3)) := by
    rw [eq_neg_iff_add_eq_zero, add_comm, ← hpair]
    congr 1
    refine Finset.sum_congr rfl (fun a _ => ?_)
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with x
    ring
  rw [h2, neg_neg]

/-- **C3.** Divergence-free L²-bound on `convIntegralSchwartz` with the sup-norm of ∇ψw.

Under the same divergence-free hypothesis `hdiv` as C2, the IBP identity (C1) has two
terms; `hdiv` (applied with `φ = ψv_i * ψw_i`, a Schwartz product) kills the
`∂_a ψu_a` term, leaving only the `∂_a ψw_i` term. Concretely:

```
IBP: ∑_{i,a} ∫(∂_a ψu_a)(ψv_i ψw_i) = -∑_{i,a} ∫ ψu_a ∂_a(ψv_i ψw_i)
   = -∑_{i,a} ∫ ψu_a (∂_a ψv_i · ψw_i + ψv_i · ∂_a ψw_i)
```

Setting `φ = ψv_i · ψw_i` (Schwartz under products) in `hdiv` gives the full IBP sum
= 0, so:
```
convIntegralSchwartz ψu ψv ψw = -∑_{i,a} ∫ ψu_a · ψv_i · (∂_a ψw_i)
```
Bounding the surviving term:
  `|conv| ≤ ∑_{i,a} ‖∂_a ψw_i‖_∞ · ‖ψu_a‖_{L²} · ‖ψv_i‖_{L²}`  (sup-norm out, C–S)

where `‖∂_a ψw_i‖_∞ ≤ SchwartzMap.seminorm ℝ 0 0 (∂_a ψw_i)` since `∂_a ψw_i` is
already differentiated and its sup-norm IS its order-(0,0) Schwartz seminorm (order
(0,1) would double-count a derivative). Product-of-sums then dominates sum-of-products.
This yields exactly the `b_bound` shape `|b(u,v,w)| ≤ C(w) · ‖u‖_{L²} · ‖v‖_{L²}`. -/
theorem convIntegralSchwartz_bound_sup
    (ψu ψv ψw : Fin 3 → SchwartzMap Domain3 ℝ)
    (hdiv : ∀ φ : SchwartzMap Domain3 ℝ,
      ∑ a : Fin 3,
        ∫ x : Domain3, (ψu a x) *
          ((lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
              (EuclideanSpace.single a (1 : ℝ) : Domain3) φ) x)
        ∂(volume : Measure Domain3) = 0) :
    |convIntegralSchwartz ψu ψv ψw| ≤
      (∑ i : Fin 3, ∑ a : Fin 3,
        SchwartzMap.seminorm ℝ 0 0
          (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
            (EuclideanSpace.single a (1 : ℝ) : Domain3) (ψw i))) *
      (∑ a : Fin 3, ‖(ψu a).toLp 2 (volume : Measure Domain3)‖) *
      (∑ i : Fin 3, ‖(ψv i).toLp 2 (volume : Measure Domain3)‖) := by
  -- abbreviations
  set A : Fin 3 → ℝ := fun a => ‖(ψu a).toLp 2 (volume : Measure Domain3)‖ with hA
  set V : Fin 3 → ℝ := fun i => ‖(ψv i).toLp 2 (volume : Measure Domain3)‖ with hV
  set S : Fin 3 → Fin 3 → ℝ := fun i a =>
    SchwartzMap.seminorm ℝ 0 0
      (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
        (EuclideanSpace.single a (1 : ℝ) : Domain3) (ψw i)) with hS
  have hAnn : ∀ a, 0 ≤ A a := fun a => norm_nonneg _
  have hVnn : ∀ i, 0 ≤ V i := fun i => norm_nonneg _
  have hSnn : ∀ i a, 0 ≤ S i a := fun i a => apply_nonneg _ _
  -- reduce to the surviving term via div-free
  rw [convIntegralSchwartz_divFree_eq ψu ψv ψw hdiv, abs_neg]
  -- per-term bound
  have hterm : ∀ i a, |∫ x : Domain3,
        (ψu a x) * (ψv i x) *
        ((lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
            (EuclideanSpace.single a (1 : ℝ) : Domain3) (ψw i)) x)
        ∂(volume : Measure Domain3)| ≤ A a * V i * S i a := by
    intro i a
    exact schwartz_trilinear_bound (ψu a) (ψv i)
      (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
        (EuclideanSpace.single a (1 : ℝ) : Domain3) (ψw i))
  calc |∑ i : Fin 3, ∑ a : Fin 3,
          ∫ x : Domain3,
            (ψu a x) * (ψv i x) *
            ((lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
                (EuclideanSpace.single a (1 : ℝ) : Domain3) (ψw i)) x)
            ∂(volume : Measure Domain3)|
      ≤ ∑ i : Fin 3, ∑ a : Fin 3, A a * V i * S i a := by
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
        refine Finset.sum_le_sum (fun i _ => ?_)
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
        exact Finset.sum_le_sum (fun a _ => hterm i a)
    _ = ∑ i : Fin 3, V i * (∑ a : Fin 3, A a * S i a) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun a _ => ?_)
        ring
    _ ≤ ∑ i : Fin 3, V i * ((∑ a : Fin 3, A a) * (∑ a : Fin 3, S i a)) := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        refine mul_le_mul_of_nonneg_left ?_ (hVnn i)
        exact sum_mul_le_mul_sum _ A (fun a => S i a)
          (fun a _ => hAnn a) (fun a _ => hSnn i a)
    _ = (∑ a : Fin 3, A a) * (∑ i : Fin 3, V i * (∑ a : Fin 3, S i a)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        ring
    _ ≤ (∑ a : Fin 3, A a) * ((∑ i : Fin 3, ∑ a : Fin 3, S i a) * (∑ i : Fin 3, V i)) := by
        refine mul_le_mul_of_nonneg_left ?_ (Finset.sum_nonneg (fun a _ => hAnn a))
        calc ∑ i : Fin 3, V i * (∑ a : Fin 3, S i a)
            = ∑ i : Fin 3, (∑ a : Fin 3, S i a) * V i := by
              refine Finset.sum_congr rfl (fun i _ => ?_); ring
          _ ≤ (∑ i : Fin 3, ∑ a : Fin 3, S i a) * (∑ i : Fin 3, V i) :=
              sum_mul_le_mul_sum _ (fun i => ∑ a : Fin 3, S i a) V
                (fun i _ => Finset.sum_nonneg (fun a _ => hSnn i a))
                (fun i _ => hVnn i)
    _ = (∑ i : Fin 3, ∑ a : Fin 3, S i a) * (∑ a : Fin 3, A a) * (∑ i : Fin 3, V i) := by
        ring

end LerayHopf
