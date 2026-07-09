import LerayHopf.R3.TrilinearEstimate
import LerayHopf.R3.Regularity

/-!
# Tier S — Axiom-free partial convection form on the Schwartz-div-free class (ℝ³)

**Milestone / stream:** `stream-c-convection-operator` (Tier S).

This file lifts the R3-d Schwartz-level trilinear estimates
(`LerayHopf/R3/TrilinearEstimate.lean`) to the *operator level*: a genuine,
axiom-free convection functional defined on fields of `L2Sigma_R3` that carry a
component-wise Schwartz representative (the `IsSchwartzDivFree_R3` class).

It does **not** mention `R3NSForms` (that conditional assembly lives in the sibling
`LerayHopf/R3/ConvectionForm.lean`, which imports `SolutionInterfaces.lean`).

## Why a *partial* form, not a total one

The trilinear convection form `b(u,v,w) = ∫(u·∇)v·w` is **unbounded in pure
L²×L²×L² norms** (R3-d's bound `convIntegralSchwartz_bound_sup` needs an L∞ slot for
`∇w`). So `b` does **not** extend continuously from Schwartz triples to all of
`L²_σ × L²_σ × L²_σ` by density: there is no continuous-extension shortcut. The genuine
*total* operator requires the missing weak-`(u·∇)v` calculus on `Lp` (isolated as
`ConvectionGap` in `ConvectionForm.lean`). What is honestly available — and proved here
— is the convection functional on the Schwartz-representable class, transported from
R3-d through the `IsSchwartzDivFree_R3` witnesses.

## Declarations (dependency order)

- `convFormSchwartzWitness`     : the R3-d value on explicit Schwartz witnesses (a `def`).
- `convFormSchwartz_witness_wd` : well-definedness — equal `toLp` classes ⇒ equal value.
- `convFormSchwartz`            : the well-defined functional on the `IsSchwartzDivFree_R3`
                                   class (via `Exists.choose` + well-definedness).
- `convFormSchwartz_eq_witness` : `convFormSchwartz` agrees with any chosen witness.
- `convFormSchwartz_add_{1,2,3}`  : additivity in each slot (transport of R3-d A1–A3).
- `convFormSchwartz_smul_{1,2,3}` : ℝ-homogeneity in each slot (transport of R3-d A4–A6).
- `convFormSchwartz_antisymm`   : antisymmetry in the last two slots on the div-free class
                                   (transport of R3-d `convIntegralSchwartz_antisymm_of_divFree`).
- `convFormSchwartz_bound`      : the `b_bound` shape `|b u v w| ≤ C(w)·‖u‖·‖v‖`
                                   (transport of R3-d `convIntegralSchwartz_bound_sup`).

## Scaffold status

All proof bodies are discharged. **No new `axiom`/`opaque`/`constant`.**
-/

namespace LerayHopf
open MeasureTheory LineDeriv SchwartzMap

/-! ### S1 — The R3-d value on explicit Schwartz witnesses -/

/-- **S1.** The convection value `∫(u·∇)v·w` on *explicit* Schwartz component witnesses.

Given `u v w : L2Sigma_R3` together with component-wise Schwartz representatives
`ψu ψv ψw` (the data exposed by `IsSchwartzDivFree_R3`), this is just the genuine
`convIntegralSchwartz` of those representatives.  It is a thin wrapper recording the
intended dependency on the *fields* `u v w` (through their witnesses); the genuine
field-level functional `convFormSchwartz` below quotients out the choice of witness via
well-definedness (S2). -/
noncomputable def convFormSchwartzWitness
    (ψu ψv ψw : Fin 3 → SchwartzMap Domain3 ℝ) : ℝ :=
  convIntegralSchwartz ψu ψv ψw

/-! ### S2 — Well-definedness: equal `toLp` classes give equal value -/

/-- **S2.** Well-definedness of the convection value in the Schwartz witnesses.

If two Schwartz tuples represent the same `L²` classes component-wise (equal `toLp 2`),
then `convIntegralSchwartz` returns the same value.  This is the a.e.-class determinacy
of the Schwartz integral: each factor enters `convIntegralSchwartz` only through an
integral that is determined by the a.e. class of the factor, so equal `toLp 2` ⇒ equal
integrand a.e. ⇒ equal integral.  Needed because `IsSchwartzDivFree_R3` exposes *some*
witness, not a canonical one. -/
theorem convFormSchwartz_witness_wd
    (ψu ψu' ψv ψv' ψw ψw' : Fin 3 → SchwartzMap Domain3 ℝ)
    (hu : ∀ j : Fin 3, (ψu j).toLp 2 (volume : Measure Domain3)
            = (ψu' j).toLp 2 (volume : Measure Domain3))
    (hv : ∀ j : Fin 3, (ψv j).toLp 2 (volume : Measure Domain3)
            = (ψv' j).toLp 2 (volume : Measure Domain3))
    (hw : ∀ j : Fin 3, (ψw j).toLp 2 (volume : Measure Domain3)
            = (ψw' j).toLp 2 (volume : Measure Domain3)) :
    convIntegralSchwartz ψu ψv ψw = convIntegralSchwartz ψu' ψv' ψw' := by
  -- Equal toLp 2 classes → equal SchwartzMaps (toLp is injective on continuous functions)
  have hψu : ψu = ψu' := funext fun j =>
    SchwartzMap.injective_toLp 2 (volume : Measure Domain3) (hu j)
  have hψv : ψv = ψv' := funext fun j =>
    SchwartzMap.injective_toLp 2 (volume : Measure Domain3) (hv j)
  have hψw : ψw = ψw' := funext fun j =>
    SchwartzMap.injective_toLp 2 (volume : Measure Domain3) (hw j)
  rw [hψu, hψv, hψw]

/-! ### S3 — The field-level functional on the Schwartz-div-free class -/

/-- **S3.** The well-defined convection functional on the `IsSchwartzDivFree_R3` class.

Given `u v w : L2Sigma_R3` each carrying a Schwartz component representative
(`IsSchwartzDivFree_R3`), the value is `convIntegralSchwartz` of the *chosen* witnesses.
Independence of the choice is `convFormSchwartz_witness_wd` (S2): different witnesses for
the same field have equal `toLp 2` classes, hence equal value.  This is the genuine
field-level convection functional on a dense class of `L²_σ(ℝ³)`. -/
noncomputable def convFormSchwartz
    (u v w : L2Sigma_R3)
    (hu : IsSchwartzDivFree_R3 u) (hv : IsSchwartzDivFree_R3 v)
    (hw : IsSchwartzDivFree_R3 w) : ℝ :=
  convIntegralSchwartz hu.choose hv.choose hw.choose

/-- **S3'.** `convFormSchwartz` agrees with the value on *any* Schwartz witness tuple
representing the same fields.  This is the user-facing computation rule: it lets one
replace the (opaque) chosen witnesses by any explicit Schwartz representatives. -/
theorem convFormSchwartz_eq_witness
    (u v w : L2Sigma_R3)
    (hu : IsSchwartzDivFree_R3 u) (hv : IsSchwartzDivFree_R3 v)
    (hw : IsSchwartzDivFree_R3 w)
    (ψu ψv ψw : Fin 3 → SchwartzMap Domain3 ℝ)
    (hψu : ∀ j : Fin 3, L2VF_projComponent_R3 j (u : L2VF_R3)
            = (ψu j).toLp 2 (volume : Measure Domain3))
    (hψv : ∀ j : Fin 3, L2VF_projComponent_R3 j (v : L2VF_R3)
            = (ψv j).toLp 2 (volume : Measure Domain3))
    (hψw : ∀ j : Fin 3, L2VF_projComponent_R3 j (w : L2VF_R3)
            = (ψw j).toLp 2 (volume : Measure Domain3)) :
    convFormSchwartz u v w hu hv hw = convIntegralSchwartz ψu ψv ψw := by
  unfold convFormSchwartz
  -- hu.choose_spec j : L2VF_projComponent_R3 j u = (hu.choose j).toLp 2 volume
  -- Combined with hψu j, we get (hu.choose j).toLp 2 = (ψu j).toLp 2
  apply convFormSchwartz_witness_wd
  · intro j; rw [← hu.choose_spec j, hψu j]
  · intro j; rw [← hv.choose_spec j, hψv j]
  · intro j; rw [← hw.choose_spec j, hψw j]

/-! ### Helper: derive the Schwartz-level div-free predicate from L2Sigma_R3 membership -/

/-- Given `u ∈ L2Sigma_R3` with Schwartz witness `ψu` (from `IsSchwartzDivFree_R3 u`),
the component witnesses satisfy the Schwartz-level weak div-free predicate used in R3-d.
Public so the limit-passage layer can supply `hdiv` for `convIntegralSchwartz_divFree_eq`. -/
theorem schwartzDivFree_of_L2Sigma
    (u : L2Sigma_R3) (ψu : Fin 3 → SchwartzMap Domain3 ℝ)
    (hψu : ∀ j, L2VF_projComponent_R3 j (u : L2VF_R3)
        = (ψu j).toLp 2 (volume : Measure Domain3)) :
    ∀ φ : SchwartzMap Domain3 ℝ,
      ∑ a : Fin 3,
        ∫ x : Domain3, (ψu a x) *
          ((lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
              (EuclideanSpace.single a (1 : ℝ) : Domain3) φ) x)
          ∂(volume : Measure Domain3) = 0 := by
  intro φ
  -- u ∈ L2Sigma_R3 means divTestFunctional φ u = 0
  have hmem : divTestFunctional φ (u : L2VF_R3) = 0 :=
    LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp u.2 φ)
  -- Unfold divTestFunctional, substitute witnesses, and convert innerSL to inner
  simp only [divTestFunctional, ContinuousLinearMap.coe_sum', Finset.sum_apply,
             ContinuousLinearMap.coe_comp', Function.comp] at hmem
  simp_rw [hψu] at hmem
  simp only [innerSL_apply_apply] at hmem
  -- Convert each L2 inner product to a pointwise integral
  -- ⟪(∂_j φ).toLp 2, (ψu j).toLp 2⟫ = ∫ x, (∂_j φ x) * (ψu j x)
  have key : ∀ j : Fin 3,
      (inner ℝ ((lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
              (EuclideanSpace.single j (1 : ℝ) : Domain3) φ).toLp 2 (volume : Measure Domain3))
          ((ψu j).toLp 2 (volume : Measure Domain3)) : ℝ)
        = ∫ x : Domain3,
            (ψu j x) *
            ((lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
                (EuclideanSpace.single j (1 : ℝ) : Domain3) φ) x)
            ∂(volume : Measure Domain3) := by
    intro j
    rw [MeasureTheory.L2.inner_def]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards
      [SchwartzMap.coeFn_toLp
        (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
          (EuclideanSpace.single j (1 : ℝ) : Domain3) φ) 2 (volume : Measure Domain3),
       SchwartzMap.coeFn_toLp (ψu j) 2 (volume : Measure Domain3)] with x hφx hux
    rw [Real.inner_apply, hφx, hux]; ring
  simp_rw [key] at hmem
  exact hmem

/-! ### S4–S9 — Multilinearity (transport of R3-d A1–A6) -/

/-- **S4.** Additivity of `convFormSchwartz` in the first slot, on the div-free class. -/
theorem convFormSchwartz_add_1
    (u u' v w : L2Sigma_R3)
    (hu : IsSchwartzDivFree_R3 u) (hu' : IsSchwartzDivFree_R3 u')
    (huu' : IsSchwartzDivFree_R3 (u + u'))
    (hv : IsSchwartzDivFree_R3 v) (hw : IsSchwartzDivFree_R3 w) :
    convFormSchwartz (u + u') v w huu' hv hw
      = convFormSchwartz u v w hu hv hw + convFormSchwartz u' v w hu' hv hw := by
  -- Witnesses for u + u': the component maps are linear
  have huu'_wit : ∀ j : Fin 3,
      L2VF_projComponent_R3 j ((u + u' : L2Sigma_R3) : L2VF_R3)
        = ((hu.choose j + hu'.choose j).toLp 2 (volume : Measure Domain3)) := by
    intro j
    rw [Submodule.coe_add, map_add, hu.choose_spec j, hu'.choose_spec j]
    have hlin := ((SchwartzMap.toLpCLM ℝ ℝ 2 (volume : Measure Domain3)).map_add
                   (hu.choose j) (hu'.choose j))
    simp only [SchwartzMap.toLpCLM_apply] at hlin
    exact hlin.symm
  rw [convFormSchwartz_eq_witness (u + u') v w huu' hv hw
        (fun j => hu.choose j + hu'.choose j) hv.choose hw.choose
        huu'_wit hv.choose_spec hw.choose_spec,
      convFormSchwartz_eq_witness u v w hu hv hw
        hu.choose hv.choose hw.choose hu.choose_spec hv.choose_spec hw.choose_spec,
      convFormSchwartz_eq_witness u' v w hu' hv hw
        hu'.choose hv.choose hw.choose hu'.choose_spec hv.choose_spec hw.choose_spec]
  exact convIntegralSchwartz_add_1 hu.choose hu'.choose hv.choose hw.choose

/-- **S5.** Additivity of `convFormSchwartz` in the second slot, on the div-free class. -/
theorem convFormSchwartz_add_2
    (u v v' w : L2Sigma_R3)
    (hu : IsSchwartzDivFree_R3 u)
    (hv : IsSchwartzDivFree_R3 v) (hv' : IsSchwartzDivFree_R3 v')
    (hvv' : IsSchwartzDivFree_R3 (v + v'))
    (hw : IsSchwartzDivFree_R3 w) :
    convFormSchwartz u (v + v') w hu hvv' hw
      = convFormSchwartz u v w hu hv hw + convFormSchwartz u v' w hu hv' hw := by
  have hvv'_wit : ∀ j : Fin 3,
      L2VF_projComponent_R3 j ((v + v' : L2Sigma_R3) : L2VF_R3)
        = ((hv.choose j + hv'.choose j).toLp 2 (volume : Measure Domain3)) := by
    intro j
    rw [Submodule.coe_add, map_add, hv.choose_spec j, hv'.choose_spec j]
    have hlin := ((SchwartzMap.toLpCLM ℝ ℝ 2 (volume : Measure Domain3)).map_add
                   (hv.choose j) (hv'.choose j))
    simp only [SchwartzMap.toLpCLM_apply] at hlin
    exact hlin.symm
  rw [convFormSchwartz_eq_witness u (v + v') w hu hvv' hw
        hu.choose (fun j => hv.choose j + hv'.choose j) hw.choose
        hu.choose_spec hvv'_wit hw.choose_spec,
      convFormSchwartz_eq_witness u v w hu hv hw
        hu.choose hv.choose hw.choose hu.choose_spec hv.choose_spec hw.choose_spec,
      convFormSchwartz_eq_witness u v' w hu hv' hw
        hu.choose hv'.choose hw.choose hu.choose_spec hv'.choose_spec hw.choose_spec]
  exact convIntegralSchwartz_add_2 hu.choose hv.choose hv'.choose hw.choose

/-- **S6.** Additivity of `convFormSchwartz` in the third slot, on the div-free class. -/
theorem convFormSchwartz_add_3
    (u v w w' : L2Sigma_R3)
    (hu : IsSchwartzDivFree_R3 u) (hv : IsSchwartzDivFree_R3 v)
    (hw : IsSchwartzDivFree_R3 w) (hw' : IsSchwartzDivFree_R3 w')
    (hww' : IsSchwartzDivFree_R3 (w + w')) :
    convFormSchwartz u v (w + w') hu hv hww'
      = convFormSchwartz u v w hu hv hw + convFormSchwartz u v w' hu hv hw' := by
  have hww'_wit : ∀ j : Fin 3,
      L2VF_projComponent_R3 j ((w + w' : L2Sigma_R3) : L2VF_R3)
        = ((hw.choose j + hw'.choose j).toLp 2 (volume : Measure Domain3)) := by
    intro j
    rw [Submodule.coe_add, map_add, hw.choose_spec j, hw'.choose_spec j]
    have hlin := ((SchwartzMap.toLpCLM ℝ ℝ 2 (volume : Measure Domain3)).map_add
                   (hw.choose j) (hw'.choose j))
    simp only [SchwartzMap.toLpCLM_apply] at hlin
    exact hlin.symm
  rw [convFormSchwartz_eq_witness u v (w + w') hu hv hww'
        hu.choose hv.choose (fun j => hw.choose j + hw'.choose j)
        hu.choose_spec hv.choose_spec hww'_wit,
      convFormSchwartz_eq_witness u v w hu hv hw
        hu.choose hv.choose hw.choose hu.choose_spec hv.choose_spec hw.choose_spec,
      convFormSchwartz_eq_witness u v w' hu hv hw'
        hu.choose hv.choose hw'.choose hu.choose_spec hv.choose_spec hw'.choose_spec]
  exact convIntegralSchwartz_add_3 hu.choose hv.choose hw.choose hw'.choose

/-- **S7.** ℝ-homogeneity of `convFormSchwartz` in the first slot, on the div-free class. -/
theorem convFormSchwartz_smul_1
    (c : ℝ) (u v w : L2Sigma_R3)
    (hu : IsSchwartzDivFree_R3 u) (hcu : IsSchwartzDivFree_R3 (c • u))
    (hv : IsSchwartzDivFree_R3 v) (hw : IsSchwartzDivFree_R3 w) :
    convFormSchwartz (c • u) v w hcu hv hw = c * convFormSchwartz u v w hu hv hw := by
  have hcu_wit : ∀ j : Fin 3,
      L2VF_projComponent_R3 j ((c • u : L2Sigma_R3) : L2VF_R3)
        = ((c • hu.choose j).toLp 2 (volume : Measure Domain3)) := by
    intro j
    rw [Submodule.coe_smul, map_smul, hu.choose_spec j]
    have hlin := ((SchwartzMap.toLpCLM ℝ ℝ 2 (volume : Measure Domain3)).map_smul
                   c (hu.choose j))
    simp only [SchwartzMap.toLpCLM_apply] at hlin
    exact hlin.symm
  rw [convFormSchwartz_eq_witness (c • u) v w hcu hv hw
        (fun j => c • hu.choose j) hv.choose hw.choose
        hcu_wit hv.choose_spec hw.choose_spec,
      convFormSchwartz_eq_witness u v w hu hv hw
        hu.choose hv.choose hw.choose hu.choose_spec hv.choose_spec hw.choose_spec]
  exact convIntegralSchwartz_smul_1 c hu.choose hv.choose hw.choose

/-- **S8.** ℝ-homogeneity of `convFormSchwartz` in the second slot, on the div-free class. -/
theorem convFormSchwartz_smul_2
    (c : ℝ) (u v w : L2Sigma_R3)
    (hu : IsSchwartzDivFree_R3 u)
    (hv : IsSchwartzDivFree_R3 v) (hcv : IsSchwartzDivFree_R3 (c • v))
    (hw : IsSchwartzDivFree_R3 w) :
    convFormSchwartz u (c • v) w hu hcv hw = c * convFormSchwartz u v w hu hv hw := by
  have hcv_wit : ∀ j : Fin 3,
      L2VF_projComponent_R3 j ((c • v : L2Sigma_R3) : L2VF_R3)
        = ((c • hv.choose j).toLp 2 (volume : Measure Domain3)) := by
    intro j
    rw [Submodule.coe_smul, map_smul, hv.choose_spec j]
    have hlin := ((SchwartzMap.toLpCLM ℝ ℝ 2 (volume : Measure Domain3)).map_smul
                   c (hv.choose j))
    simp only [SchwartzMap.toLpCLM_apply] at hlin
    exact hlin.symm
  rw [convFormSchwartz_eq_witness u (c • v) w hu hcv hw
        hu.choose (fun j => c • hv.choose j) hw.choose
        hu.choose_spec hcv_wit hw.choose_spec,
      convFormSchwartz_eq_witness u v w hu hv hw
        hu.choose hv.choose hw.choose hu.choose_spec hv.choose_spec hw.choose_spec]
  exact convIntegralSchwartz_smul_2 c hu.choose hv.choose hw.choose

/-- **S9.** ℝ-homogeneity of `convFormSchwartz` in the third slot, on the div-free class. -/
theorem convFormSchwartz_smul_3
    (c : ℝ) (u v w : L2Sigma_R3)
    (hu : IsSchwartzDivFree_R3 u) (hv : IsSchwartzDivFree_R3 v)
    (hw : IsSchwartzDivFree_R3 w) (hcw : IsSchwartzDivFree_R3 (c • w)) :
    convFormSchwartz u v (c • w) hu hv hcw = c * convFormSchwartz u v w hu hv hw := by
  have hcw_wit : ∀ j : Fin 3,
      L2VF_projComponent_R3 j ((c • w : L2Sigma_R3) : L2VF_R3)
        = ((c • hw.choose j).toLp 2 (volume : Measure Domain3)) := by
    intro j
    rw [Submodule.coe_smul, map_smul, hw.choose_spec j]
    have hlin := ((SchwartzMap.toLpCLM ℝ ℝ 2 (volume : Measure Domain3)).map_smul
                   c (hw.choose j))
    simp only [SchwartzMap.toLpCLM_apply] at hlin
    exact hlin.symm
  rw [convFormSchwartz_eq_witness u v (c • w) hu hv hcw
        hu.choose hv.choose (fun j => c • hw.choose j)
        hu.choose_spec hv.choose_spec hcw_wit,
      convFormSchwartz_eq_witness u v w hu hv hw
        hu.choose hv.choose hw.choose hu.choose_spec hv.choose_spec hw.choose_spec]
  exact convIntegralSchwartz_smul_3 c hu.choose hv.choose hw.choose

/-! ### S10 — Antisymmetry on the div-free class -/

/-- **S10.** Antisymmetry of `convFormSchwartz` in the last two slots, on the div-free class.

`convFormSchwartz u v w = - convFormSchwartz u w v` for `u v w` in the
`IsSchwartzDivFree_R3` class.  This transports R3-d
`convIntegralSchwartz_antisymm_of_divFree`, whose hypothesis is the Schwartz-level
weak-div-free predicate `hdiv`.  That predicate is supplied from `u ∈ L2Sigma_R3`:
membership means `divTestFunctional φ u = 0` for every Schwartz `φ`, which unfolds (via
the chosen witness `hu.choose`) to exactly the `∑_a ∫ ψu_a (∂_a φ) = 0` shape of `hdiv`
(this is the L²-level counterpart of R3-d's `divFree_intLeft`). -/
theorem convFormSchwartz_antisymm
    (u v w : L2Sigma_R3)
    (hu : IsSchwartzDivFree_R3 u) (hv : IsSchwartzDivFree_R3 v)
    (hw : IsSchwartzDivFree_R3 w) :
    convFormSchwartz u v w hu hv hw = - convFormSchwartz u w v hu hw hv := by
  rw [convFormSchwartz_eq_witness u v w hu hv hw
        hu.choose hv.choose hw.choose
        hu.choose_spec hv.choose_spec hw.choose_spec,
      convFormSchwartz_eq_witness u w v hu hw hv
        hu.choose hw.choose hv.choose
        hu.choose_spec hw.choose_spec hv.choose_spec]
  exact convIntegralSchwartz_antisymm_of_divFree hu.choose hv.choose hw.choose
    (schwartzDivFree_of_L2Sigma u hu.choose hu.choose_spec)

/-! ### S11 — The `b_bound` shape on the div-free class -/

/-- **S11.** Smooth-test L²-bound for `convFormSchwartz`, on the div-free class.

For `w` in the `IsSchwartzDivFree_R3` class there is a constant `C` (depending on `w`)
with `|convFormSchwartz u v w| ≤ C · ‖u‖ · ‖v‖` for all div-free `u v`.  This is the
operator-level `b_bound` shape, transported from R3-d `convIntegralSchwartz_bound_sup`
(the divergence-free sup-bound, with `C = ∑_{i,a} ‖∂_a ψw_i‖_∞`) via the norm bookkeeping
that relates the component `toLp 2` norms to the `EuclideanSpace`-valued L² norm
`‖(u : L2VF_R3)‖`. -/
theorem convFormSchwartz_bound
    (w : L2Sigma_R3) (hw : IsSchwartzDivFree_R3 w) :
    ∃ C : ℝ, ∀ (u v : L2Sigma_R3)
      (hu : IsSchwartzDivFree_R3 u) (hv : IsSchwartzDivFree_R3 v),
      |convFormSchwartz u v w hu hv hw|
        ≤ C * ‖(u : L2VF_R3)‖ * ‖(v : L2VF_R3)‖ := by
  -- The constant: C_raw from R3-d bound_sup, times (3 * K)^2 from component-vs-full norm
  set C_raw : ℝ := ∑ i : Fin 3, ∑ a : Fin 3,
      SchwartzMap.seminorm ℝ 0 0
        (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
          (EuclideanSpace.single a (1 : ℝ) : Domain3) (hw.choose i)) with hC_raw_def
  -- K = max j, ‖L2VF_projComponent_R3 j‖ (finite, ≥ 0)
  set K : ℝ := Finset.sup' Finset.univ ⟨(0 : Fin 3), Finset.mem_univ _⟩
      (fun j : Fin 3 => ‖L2VF_projComponent_R3 j‖) with hK_def
  have hK_nn : (0 : ℝ) ≤ K := le_trans (norm_nonneg _)
      (Finset.le_sup' (fun j : Fin 3 => ‖L2VF_projComponent_R3 j‖) (Finset.mem_univ 0))
  refine ⟨C_raw * (3 * K) ^ 2, fun u v hu hv => ?_⟩
  rw [convFormSchwartz_eq_witness u v w hu hv hw
        hu.choose hv.choose hw.choose
        hu.choose_spec hv.choose_spec hw.choose_spec]
  -- Apply R3-d bound_sup, using the div-free condition of u
  have hu_hdiv := schwartzDivFree_of_L2Sigma u hu.choose hu.choose_spec
  have hbound := convIntegralSchwartz_bound_sup hu.choose hv.choose hw.choose hu_hdiv
  -- hbound: |conv| ≤ C_raw * (∑ a, ‖(hu.choose a).toLp 2‖) * (∑ i, ‖(hv.choose i).toLp 2‖)
  -- Use hu/hv spec to replace toLp norms with component CLM norms
  have hunit_u : ∀ j : Fin 3, ‖(hu.choose j).toLp 2 (volume : Measure Domain3)‖
      = ‖L2VF_projComponent_R3 j (u : L2VF_R3)‖ := fun j => by rw [← hu.choose_spec j]
  have hunit_v : ∀ j : Fin 3, ‖(hv.choose j).toLp 2 (volume : Measure Domain3)‖
      = ‖L2VF_projComponent_R3 j (v : L2VF_R3)‖ := fun j => by rw [← hv.choose_spec j]
  simp_rw [hunit_u, hunit_v] at hbound
  -- Each component norm ≤ K * full vector norm (operator norm bound)
  have hcomp_u : ∀ j : Fin 3, ‖L2VF_projComponent_R3 j (u : L2VF_R3)‖ ≤ K * ‖(u : L2VF_R3)‖ :=
    fun j => (L2VF_projComponent_R3 j).le_opNorm _ |>.trans
      (mul_le_mul_of_nonneg_right
        (Finset.le_sup' (fun j : Fin 3 => ‖L2VF_projComponent_R3 j‖) (Finset.mem_univ j))
        (norm_nonneg _))
  have hcomp_v : ∀ j : Fin 3, ‖L2VF_projComponent_R3 j (v : L2VF_R3)‖ ≤ K * ‖(v : L2VF_R3)‖ :=
    fun j => (L2VF_projComponent_R3 j).le_opNorm _ |>.trans
      (mul_le_mul_of_nonneg_right
        (Finset.le_sup' (fun j : Fin 3 => ‖L2VF_projComponent_R3 j‖) (Finset.mem_univ j))
        (norm_nonneg _))
  have hsum_u : ∑ j : Fin 3, ‖L2VF_projComponent_R3 j (u : L2VF_R3)‖ ≤ 3 * K * ‖(u : L2VF_R3)‖ :=
    (Finset.sum_le_sum fun j _ => hcomp_u j).trans_eq (by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring)
  have hsum_v : ∑ j : Fin 3, ‖L2VF_projComponent_R3 j (v : L2VF_R3)‖ ≤ 3 * K * ‖(v : L2VF_R3)‖ :=
    (Finset.sum_le_sum fun j _ => hcomp_v j).trans_eq (by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring)
  have hC_raw_nn : 0 ≤ C_raw := by
    apply Finset.sum_nonneg; intro i _; apply Finset.sum_nonneg; intro a _; exact apply_nonneg _ _
  calc |convIntegralSchwartz hu.choose hv.choose hw.choose|
      ≤ C_raw *
          (∑ a : Fin 3, ‖L2VF_projComponent_R3 a (u : L2VF_R3)‖) *
          (∑ i : Fin 3, ‖L2VF_projComponent_R3 i (v : L2VF_R3)‖) := hbound
    _ ≤ C_raw * (3 * K * ‖(u : L2VF_R3)‖) * (3 * K * ‖(v : L2VF_R3)‖) := by
          have hleft : C_raw * ∑ a : Fin 3, ‖L2VF_projComponent_R3 a (u : L2VF_R3)‖
              ≤ C_raw * (3 * K * ‖(u : L2VF_R3)‖) :=
            mul_le_mul_of_nonneg_left hsum_u hC_raw_nn
          exact mul_le_mul hleft hsum_v (by positivity) (by positivity)
    _ = C_raw * (3 * K) ^ 2 * ‖(u : L2VF_R3)‖ * ‖(v : L2VF_R3)‖ := by ring

end LerayHopf
