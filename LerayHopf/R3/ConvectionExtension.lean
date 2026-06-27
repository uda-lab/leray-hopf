import LerayHopf.R3.EnergyClassConvection
import LerayHopf.R3.ConvectionForm
import LerayHopf.R3.TensorIntersection
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.LinearAlgebra.LinearPMap
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Analysis.Normed.Operator.Extend

/-!
# ConvectionExtension — determined-form construction of the full `b` form (issue #56)

**File:** `LerayHopf/R3/ConvectionExtension.lean`

## What this file builds and why the construction changed

This file constructs the trilinear convection form
`convFormL2_def : L2Sigma_R3 → L2Sigma_R3 → L2Sigma_R3 → ℝ` together with all five
fields of `ConvectionGapOp`.

**Refuted predecessor.** An earlier scaffold defined
`convFormL2_def u v w := (BExt_slot3 u v w − BExt_slot3 u w v) / 2`, where `BExt_slot3`
was a *raw three-slot Hamel extension* of `convFormH1`.  Codex (PR #60) refuted that
object: with `w` fixed Schwartz, the swapped term `BExt_slot3 u w v` feeds the *varied*
slot-2 argument `v` into a **discontinuous Hamel index**, so `b_cont_fixedTest` (the 5th
field) is FALSE for that object.

**Determined-form replacement (this file).** For fixed `u`, we build an antisymmetric
bilinear form `β_u` on the genuinely *determined* submodule
`D := (𝒮 ⊗ L²_σ) + (L²_σ ⊗ 𝒮) ≤ L²_σ ⊗[ℝ] L²_σ`, where
`𝒮 := Submodule.span ℝ {x | IsSchwartzDivFree_R3 x}`:

- on `𝒮 ⊗ L²_σ` (slot-2 Schwartz): `(s, l) ↦ convFormH1 u s l` — defined for *all* `l`
  because the Schwartz slot-2 makes `convFormH1 u s ·` `L²`-bounded (B7);
- on `L²_σ ⊗ 𝒮` (slot-3 Schwartz): `(l, s) ↦ convFormH1 u l s = − convFormH1 u s l` (B6).

These two prescriptions agree on the overlap
`(𝒮 ⊗ L²_σ) ⊓ (L²_σ ⊗ 𝒮) = 𝒮 ⊗ 𝒮`
(`TensorIntersection.range_map_subtype_inf_range_map_subtype`, proved sorry-free),
where both equal `convFormH1 u s s'` via B6/the div-free identity.  So they glue to a
single `β_u : D →ₗ[ℝ] ℝ` (`LinearPMap.sup`).  We then Hamel-extend `β_u` off `D` to
`Bext_u : (L²_σ ⊗[ℝ] L²_σ) →ₗ[ℝ] ℝ` (`LinearMap.exists_extend`).

The whole tower is built linearly in `u` as well, giving a trilinear
`B : L²_σ →ₗ[ℝ] L²_σ →ₗ[ℝ] L²_σ →ₗ[ℝ] ℝ` and
`convFormL2_def u v w := Bext u (v ⊗ₜ w)`.

**Why `b_cont_fixedTest` is now TRUE (the determined payoff).** For Schwartz `w`,
`v ⊗ₜ w ∈ L²_σ ⊗ 𝒮 ⊆ D` for **all** `v`, so the value is the *determined* one,
`convFormL2_def u v w = − convFormH1 u w v` — a genuine B7-controlled quantity, NOT a
Hamel value.  Continuity in `(u, v)` is then exactly B7 (uniform-in-`u,v` bound at fixed
Schwartz `w`).  This is the precise place the refuted object failed.

## The five `ConvectionGapOp` fields

- `b`              := `convFormL2_def`.
- `b_extends`      — on Schwartz triples `b = convFormSchwartz`; B5 (`convFormH1_eq_convFormSchwartz`).
- `b_multilinear`  — the trilinear `Bext` tower.
- `b_antisymm_gap` — `β_u` is antisymmetric on `D` (B6), preserved by the Hamel extension.
- `b_cont_fixedTest` — the CRUX: B7 on the determined slice `L²_σ ⊗ 𝒮`.

## Status of proofs

Complete and `sorry`-free (issue #56, PR-4).  The determined-form construction is fully
discharged: the double-BLT extension `convBLT_fixedTest` and its `w`-linear / span-extended
form `convBLTspan`, the two `TensorProduct.lift` edge bilinears glued by `LinearPMap.sup`
over `detDomain = (𝒮⊗L²) + (L²⊗𝒮)`, the fixed left-inverse `gInv` giving the `u`-linear
`detExtend`, and the antisymmetrizer `A = (id − swap)/2` that makes `detExtend u`
antisymmetric for all `(v, w)`.  All five `ConvectionGapOp` fields — including the analytic
crux `b_cont_fixedTest` — are proved, so `r3ConvectionGapOp_holds` removes the capstone
`r3ConvectionGapOp_exists` assumption.  This file introduces no new `axiom`/`opaque`.

## Mathlib declarations consumed

- `TensorProduct.map`, `TensorProduct.mapIncl`, `TensorProduct.lift`, `TensorProduct.mk`
  (`LinearAlgebra/TensorProduct/{Basic,Map}.lean`) — the edge bilinears and `D`.
- `TensorIntersection.range_map_subtype_inf_range_map_subtype` — the overlap identity
  `(𝒮⊗L²) ⊓ (L²⊗𝒮) = 𝒮⊗𝒮` (PROVED, sorry-free, this repo).
- `LinearPMap.sup` / `LinearPMap.sup_apply` (`LinearAlgebra/LinearPMap.lean`) — glue the
  two edge prescriptions agreeing on the overlap.
- `LinearMap.exists_extend` (`LinearAlgebra/Basis/VectorSpace.lean:288`, needs
  `DivisionRing ℝ`) — Hamel-extend `β_u` off `D`.  Instance trap: `Classical.choose`
  yields `DivisionRing.toDivisionSemiring.toSemiring ℝ` vs `Real.semiring`; fix with
  `letI : Semiring ℝ := inferInstance`.
- `LinearMap.extendOfNorm` (`Analysis/Normed/Operator/Extend.lean:190`) — the B7-bounded
  `L²`-extension of `convFormH1 u s ·` on the Schwartz slot.
- B5 `convFormH1_eq_convFormSchwartz`, B6 `convFormH1_antisymm`,
  B7 `convFormH1_bound_Schwartz`, trilinearity `convFormH1_add/smul_{1,2,3}`
  (`EnergyClassConvection.lean`).
-/

open MeasureTheory TemperedDistribution SchwartzMap LineDeriv TensorProduct

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 4000000

namespace LerayHopf.R3.ConvectionExtension

/-! ### C0 — `H1Sigma'` (re-typing of H¹_σ inside `L2Sigma_R3`) -/

/-- **C0 `H1Sigma'` [proved sorry-free].** H¹_σ re-typed as a submodule of `L2Sigma_R3`:
`H1Sigma' := Submodule.comap L2Sigma_R3.subtype H1Sigma_R3`.

Membership: `u ∈ H1Sigma' ↔ (u : L2VF_R3) ∈ H1Sigma_R3`. -/
noncomputable def H1Sigma' : Submodule ℝ L2Sigma_R3 :=
  Submodule.comap L2Sigma_R3.subtype H1Sigma_R3

@[simp]
theorem mem_H1Sigma'_iff (u : L2Sigma_R3) :
    u ∈ H1Sigma' ↔ (u : L2VF_R3) ∈ H1Sigma_R3 :=
  Iff.rfl

theorem H1Sigma'_memH1 {u : L2Sigma_R3} (hu : u ∈ H1Sigma') :
    memH1VF_R3 (u : L2VF_R3) :=
  ((mem_H1Sigma'_iff u).mp hu).1

/-! ### C0b — `schwartzSpan` : the Schwartz-div-free span `𝒮` -/

/-- **C0b `schwartzSpan` (`𝒮`) [proved sorry-free].** The submodule of `L2Sigma_R3`
spanned by the Schwartz-div-free class — the smooth "edge" used in the determined
construction:

`𝒮 := Submodule.span ℝ {x : L2Sigma_R3 | IsSchwartzDivFree_R3 x}`. -/
noncomputable def schwartzSpan : Submodule ℝ L2Sigma_R3 :=
  Submodule.span ℝ {x : L2Sigma_R3 | IsSchwartzDivFree_R3 x}

theorem subset_schwartzSpan {x : L2Sigma_R3} (hx : IsSchwartzDivFree_R3 x) :
    x ∈ schwartzSpan :=
  Submodule.subset_span hx

/-- Helper: `IsSchwartzDivFree_R3 u → memH1VF_R3 (u : L2VF_R3)`.
Mirrors the private `memH1VF_R3_of_isSchwartzDivFree` in `SobolevEmbedding.lean`. -/
private theorem memH1VF_R3_of_schwartz {u : L2Sigma_R3}
    (hu : IsSchwartzDivFree_R3 u) : memH1VF_R3 (u : L2VF_R3) := by
  obtain ⟨ψ, hψ⟩ := hu
  intro j
  set φ : SchwartzMap Domain3 ℂ := (ψ j).postcompCLM (RCLike.ofRealCLM (K := ℂ)) with hφ
  -- The complex component equals `φ.toLp` as an `L²`-class.
  have hgeq : (L2VF_projComponentC_R3 j (u : L2VF_R3))
      = φ.toLp 2 (volume : Measure Domain3) := by
    apply MeasureTheory.Lp.ext_iff.mpr
    have hLHS : (⇑(L2VF_projComponentC_R3 j (u : L2VF_R3)) : Domain3 → ℂ)
        =ᵐ[volume] fun a => RCLike.ofRealCLM (K := ℂ) (L2VF_projComponent_R3 j (u : L2VF_R3) a) := by
      simpa [L2VF_projComponentC_R3] using
        (RCLike.ofRealCLM (K := ℂ)).coeFn_compLpL (L2VF_projComponent_R3 j (u : L2VF_R3))
    have hcomp : (⇑(L2VF_projComponent_R3 j (u : L2VF_R3)) : Domain3 → ℝ)
        =ᵐ[volume] ⇑(ψ j) := by
      rw [hψ j]; exact (ψ j).coeFn_toLp 2 (volume : Measure Domain3)
    have hRHS : (⇑(φ.toLp 2 (volume : Measure Domain3)) : Domain3 → ℂ) =ᵐ[volume] ⇑φ :=
      φ.coeFn_toLp 2 (volume : Measure Domain3)
    filter_upwards [hLHS, hcomp, hRHS] with a hL hc hR
    rw [hL, hc, hR, hφ, SchwartzMap.postcompCLM_apply]
  -- Schwartz ⊂ H¹: `((φ.toLp) : 𝓢') = (φ : 𝓢')` is in every Sobolev space.
  have hcoe : ((L2VF_projComponentC_R3 j (u : L2VF_R3)) : 𝓢'(Domain3, ℂ))
      = (φ : 𝓢'(Domain3, ℂ)) := by
    rw [hgeq]; exact MeasureTheory.Lp.toTemperedDistribution_toLp_eq φ
  rw [show (L2VF_projComponentC_R3 j (u : L2VF_R3) : 𝓢'(Domain3, ℂ))
      = (φ : 𝓢'(Domain3, ℂ)) from hcoe]
  exact φ.memSobolev

theorem schwartz_mem_H1Sigma' {u : L2Sigma_R3} (hu : IsSchwartzDivFree_R3 u) :
    u ∈ H1Sigma' :=
  (mem_H1Sigma'_iff u).mpr ⟨memH1VF_R3_of_schwartz hu, u.2⟩

/-! ### C2 — `convFormH1_bound_slot2_schwartz` (CRUX-FINAL bound, B7 ∘ B6) -/

/-- **C2 `convFormH1_bound_slot2_schwartz` [analytic must-prove — PR-4].**
For a fixed Schwartz `w`, `(u, v) ↦ convFormH1 u w v` is `‖u‖‖v‖`-bounded.

**Proof route (B7 ∘ B6, ~3 lines):** B6 (`convFormH1_antisymm`) gives
`convFormH1 u w v = − convFormH1 u v w`; `abs_neg` keeps the magnitude; B7
(`convFormH1_bound_Schwartz`) bounds `|convFormH1 u v w| ≤ C_w ‖u‖ ‖v‖`.  The varied slot
is `(u, v)` (L²-controlled); the Schwartz `w` is the fixed test slot after the B6 flip —
NO `‖∇w‖_∞`-in-the-rough-slot leakage. -/
theorem convFormH1_bound_slot2_schwartz
    (w : L2VF_R3) (hw_H1 : memH1VF_R3 w)
    (hw_sigma : w ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3))
    (hw_sch : IsSchwartzDivFree_R3 ⟨w, hw_sigma⟩) :
    ∃ C_w : ℝ, 0 ≤ C_w ∧
      ∀ (u v : L2VF_R3) (hu : memH1VF_R3 u) (hv : memH1VF_R3 v)
        (hu_sigma : u ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3))
        (hv_sigma : v ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3)),
        |convFormH1 u w v hu hw_H1 hv| ≤ C_w * ‖u‖ * ‖v‖ := by
  obtain ⟨C_w, hC_nonneg, hbound⟩ :=
    convFormH1_bound_Schwartz w hw_H1 hw_sigma hw_sch
  refine ⟨C_w, hC_nonneg, ?_⟩
  intro u v hu hv hu_sigma hv_sigma
  -- B6: convFormH1 u w v = -convFormH1 u v w; |·| is preserved by negation.
  rw [convFormH1_antisymm u w v hu hw_H1 hv hu_sigma hw_sigma hv_sigma, abs_neg]
  exact hbound u v hu hv hu_sigma hv_sigma

/-! ### C3 — `convDetSlot3` : the determined `L²`-slot bilinear on the Schwartz slice

For fixed `u` and a Schwartz test `w`, `convFormH1 u · w` is `L²`-bounded in its varied
arguments (B7), so it BLT-extends to a continuous bilinear form on all of
`L2Sigma_R3 × L2Sigma_R3`.  This is the genuine, determined value the construction reads
off on the slice `L²_σ ⊗ 𝒮` (and its B6-flip on `𝒮 ⊗ L²_σ`). -/

/-! #### C3 infrastructure — `H1Sigma'` density and the double-BLT helpers -/

/-- `H1Sigma'.subtype : H1Sigma' →ₗ[ℝ] L2Sigma_R3` has dense range
(`h1Sigma_dense_in_L2Sigma`). -/
theorem denseRange_H1Sigma'_subtype :
    DenseRange (H1Sigma'.subtype : H1Sigma' → L2Sigma_R3) := by
  rw [denseRange_iff_closure_range]
  rw [Set.eq_univ_iff_forall]
  intro u
  -- Every `u : L2Sigma_R3` is a sequential limit of `H1Sigma'` elements.
  obtain ⟨s, hs_h1, hs_lim⟩ := h1Sigma_dense_in_L2Sigma u
  refine mem_closure_of_tendsto hs_lim ?_
  refine Filter.Eventually.of_forall (fun n => ?_)
  exact ⟨⟨s n, (mem_H1Sigma'_iff (s n)).mpr ⟨hs_h1 n, (s n).2⟩⟩, rfl⟩

/-- The `L2VF_R3` representative of an `H1Sigma'` element. -/
private noncomputable def vfOf (u : H1Sigma') : L2VF_R3 := ((u : L2Sigma_R3) : L2VF_R3)

private theorem vfOf_mem (u : H1Sigma') : memH1VF_R3 (vfOf u) := H1Sigma'_memH1 u.2

private theorem vfOf_add (u u' : H1Sigma') : vfOf (u + u') = vfOf u + vfOf u' := by
  simp only [vfOf, Submodule.coe_add]

private theorem vfOf_smul (c : ℝ) (u : H1Sigma') : vfOf (c • u) = c • vfOf u := by
  simp only [vfOf, Submodule.coe_smul]

/-- The value of `convFormH1` on the `H1Sigma'` subtype, with the `H¹` proofs supplied. -/
private noncomputable def valH1
    (w : L2VF_R3) (hw_H1 : memH1VF_R3 w) (u v : H1Sigma') : ℝ :=
  convFormH1 (vfOf u) (vfOf v) w (vfOf_mem u) (vfOf_mem v) hw_H1

private theorem valH1_add_2
    (w : L2VF_R3) (hw_H1 : memH1VF_R3 w) (u v v' : H1Sigma') :
    valH1 w hw_H1 u (v + v') = valH1 w hw_H1 u v + valH1 w hw_H1 u v' := by
  unfold valH1
  exact convFormH1_add_2 (vfOf u) (vfOf v) (vfOf v') w
    (vfOf_mem u) (vfOf_mem v) (vfOf_mem v') hw_H1

private theorem valH1_smul_2
    (w : L2VF_R3) (hw_H1 : memH1VF_R3 w) (u : H1Sigma') (c : ℝ) (v : H1Sigma') :
    valH1 w hw_H1 u (c • v) = c * valH1 w hw_H1 u v := by
  unfold valH1
  exact convFormH1_smul_2 c (vfOf u) (vfOf v) w (vfOf_mem u) (vfOf_mem v) hw_H1

private theorem valH1_add_1
    (w : L2VF_R3) (hw_H1 : memH1VF_R3 w) (u u' v : H1Sigma') :
    valH1 w hw_H1 (u + u') v = valH1 w hw_H1 u v + valH1 w hw_H1 u' v := by
  unfold valH1
  exact convFormH1_add_1 (vfOf u) (vfOf u') (vfOf v) w
    (vfOf_mem u) (vfOf_mem u') (vfOf_mem v) hw_H1

private theorem valH1_smul_1
    (w : L2VF_R3) (hw_H1 : memH1VF_R3 w) (c : ℝ) (u v : H1Sigma') :
    valH1 w hw_H1 (c • u) v = c * valH1 w hw_H1 u v := by
  unfold valH1
  exact convFormH1_smul_1 c (vfOf u) (vfOf v) w (vfOf_mem u) (vfOf_mem v) hw_H1

/-- The inner linear functional `v ↦ convFormH1 u v w` on `H1Sigma'`, for fixed
H¹ `u` and Schwartz test `w`. -/
private noncomputable def innerLin
    (w : L2VF_R3) (hw_H1 : memH1VF_R3 w) (u : H1Sigma') : H1Sigma' →ₗ[ℝ] ℝ where
  toFun v := valH1 w hw_H1 u v
  map_add' v v' := valH1_add_2 w hw_H1 u v v'
  map_smul' c v := by simpa using valH1_smul_2 w hw_H1 u c v

/-- `H1Sigma'` carries the `L2VF_R3` norm: `‖u‖ = ‖vfOf u‖`. -/
private theorem norm_eq_vfOf (u : H1Sigma') : ‖u‖ = ‖vfOf u‖ := rfl

private theorem innerLin_add_1 (w : L2VF_R3) (hw_H1 : memH1VF_R3 w) (u u' : H1Sigma') :
    innerLin w hw_H1 (u + u') = innerLin w hw_H1 u + innerLin w hw_H1 u' := by
  refine LinearMap.ext (fun v => ?_)
  simp only [innerLin, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]
  exact valH1_add_1 w hw_H1 u u' v

private theorem innerLin_smul_1 (w : L2VF_R3) (hw_H1 : memH1VF_R3 w) (c : ℝ) (u : H1Sigma') :
    innerLin w hw_H1 (c • u) = c • innerLin w hw_H1 u := by
  refine LinearMap.ext (fun v => ?_)
  simp only [innerLin, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, smul_eq_mul]
  exact valH1_smul_1 w hw_H1 c u v

/-- The inner B7 bound at fixed `u`: `‖innerLin w u v‖ ≤ (C_w ‖u‖) ‖v‖`. -/
private theorem innerLin_bound
    (w : L2VF_R3) (hw_H1 : memH1VF_R3 w)
    (hw_sigma : w ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3))
    (hw_sch : IsSchwartzDivFree_R3 ⟨w, hw_sigma⟩)
    {C_w : ℝ}
    (hbound : ∀ (u v : L2VF_R3) (hu : memH1VF_R3 u) (hv : memH1VF_R3 v)
      (hu_sigma : u ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3))
      (hv_sigma : v ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3)),
      |convFormH1 u v w hu hv hw_H1| ≤ C_w * ‖u‖ * ‖v‖)
    (u v : H1Sigma') :
    ‖innerLin w hw_H1 u v‖ ≤ C_w * ‖u‖ * ‖v‖ := by
  have hu_sigma : (vfOf u) ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3) := (u : L2Sigma_R3).2
  have hv_sigma : (vfOf v) ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3) := (v : L2Sigma_R3).2
  have := hbound (vfOf u) (vfOf v) (vfOf_mem u) (vfOf_mem v) hu_sigma hv_sigma
  rw [Real.norm_eq_abs, norm_eq_vfOf u, norm_eq_vfOf v]
  exact this

/-- The dense `H1Sigma' → L2Sigma_R3` inclusion as a bare `LinearMap` (for `extendOfNorm`). -/
private noncomputable def eH1 : H1Sigma' →ₗ[ℝ] L2Sigma_R3 := H1Sigma'.subtype

private theorem denseRange_eH1 : DenseRange (eH1 : H1Sigma' → L2Sigma_R3) :=
  denseRange_H1Sigma'_subtype

private theorem eH1_norm (v : H1Sigma') : ‖eH1 v‖ = ‖v‖ := rfl

/-- Additivity of `extendOfNorm` along `eH1` (via uniqueness of the bounded extension). -/
private theorem extendOfNorm_eH1_add
    (f f' : H1Sigma' →ₗ[ℝ] ℝ) {C C' : ℝ}
    (hf : ∀ x, ‖f x‖ ≤ C * ‖eH1 x‖) (hf' : ∀ x, ‖f' x‖ ≤ C' * ‖eH1 x‖) :
    (f + f').extendOfNorm eH1 = f.extendOfNorm eH1 + f'.extendOfNorm eH1 := by
  refine LinearMap.extendOfNorm_unique denseRange_eH1 (C + C')
    (fun x => ?_) (f.extendOfNorm eH1 + f'.extendOfNorm eH1) ?_
  · calc ‖(f + f') x‖ = ‖f x + f' x‖ := rfl
      _ ≤ ‖f x‖ + ‖f' x‖ := norm_add_le _ _
      _ ≤ C * ‖eH1 x‖ + C' * ‖eH1 x‖ := add_le_add (hf x) (hf' x)
      _ = (C + C') * ‖eH1 x‖ := by ring
  · refine LinearMap.ext (fun x => ?_)
    simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.add_apply, LinearMap.add_apply,
      LinearMap.extendOfNorm_eq denseRange_eH1 ⟨C, hf⟩ x,
      LinearMap.extendOfNorm_eq denseRange_eH1 ⟨C', hf'⟩ x]

/-- Homogeneity of `extendOfNorm` along `eH1`. -/
private theorem extendOfNorm_eH1_smul
    (c : ℝ) (f : H1Sigma' →ₗ[ℝ] ℝ) {C : ℝ} (hf : ∀ x, ‖f x‖ ≤ C * ‖eH1 x‖) :
    (c • f).extendOfNorm eH1 = c • f.extendOfNorm eH1 := by
  refine LinearMap.extendOfNorm_unique denseRange_eH1 (|c| * C)
    (fun x => ?_) (c • f.extendOfNorm eH1) ?_
  · calc ‖(c • f) x‖ = |c| * ‖f x‖ := by
            simp [LinearMap.smul_apply, norm_smul, Real.norm_eq_abs]
      _ ≤ |c| * (C * ‖eH1 x‖) := by
            apply mul_le_mul_of_nonneg_left (hf x) (abs_nonneg c)
      _ = |c| * C * ‖eH1 x‖ := by ring
  · refine LinearMap.ext (fun x => ?_)
    simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.smul_apply, LinearMap.smul_apply, Pi.smul_apply,
      LinearMap.extendOfNorm_eq denseRange_eH1 ⟨C, hf⟩ x, smul_eq_mul]

/-- The chosen B7 constant for the fixed Schwartz `w`. -/
private noncomputable def cwConst
    (w : L2VF_R3) (hw_H1 : memH1VF_R3 w)
    (hw_sigma : w ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3))
    (hw_sch : IsSchwartzDivFree_R3 ⟨w, hw_sigma⟩) : ℝ :=
  (convFormH1_bound_Schwartz w hw_H1 hw_sigma hw_sch).choose

/-- The uniform B7 bound packaged in terms of `innerLin` and the constant `cwConst`. -/
private theorem innerLin_bound'
    (w : L2VF_R3) (hw_H1 : memH1VF_R3 w)
    (hw_sigma : w ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3))
    (hw_sch : IsSchwartzDivFree_R3 ⟨w, hw_sigma⟩)
    (u v : H1Sigma') :
    ‖innerLin w hw_H1 u v‖
      ≤ cwConst w hw_H1 hw_sigma hw_sch * ‖u‖ * ‖eH1 v‖ := by
  have hbound := (convFormH1_bound_Schwartz w hw_H1 hw_sigma hw_sch).choose_spec.2
  rw [eH1_norm]
  exact innerLin_bound w hw_H1 hw_sigma hw_sch hbound u v

/-- The inner extension `Φ u : L2Sigma_R3 →L ℝ` of `innerLin u` (slot-2 extension). -/
private noncomputable def convInnerCLM
    (w : L2VF_R3) (hw_H1 : memH1VF_R3 w)
    (hw_sigma : w ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3))
    (hw_sch : IsSchwartzDivFree_R3 ⟨w, hw_sigma⟩) (u : H1Sigma') :
    L2Sigma_R3 →L[ℝ] ℝ :=
  (innerLin w hw_H1 u).extendOfNorm eH1

private theorem convInnerCLM_add
    (w : L2VF_R3) (hw_H1 : memH1VF_R3 w)
    (hw_sigma : w ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3))
    (hw_sch : IsSchwartzDivFree_R3 ⟨w, hw_sigma⟩) (u u' : H1Sigma') :
    convInnerCLM w hw_H1 hw_sigma hw_sch (u + u')
      = convInnerCLM w hw_H1 hw_sigma hw_sch u + convInnerCLM w hw_H1 hw_sigma hw_sch u' := by
  unfold convInnerCLM
  rw [innerLin_add_1 w hw_H1 u u']
  exact extendOfNorm_eH1_add (innerLin w hw_H1 u) (innerLin w hw_H1 u')
    (fun v => innerLin_bound' w hw_H1 hw_sigma hw_sch u v)
    (fun v => innerLin_bound' w hw_H1 hw_sigma hw_sch u' v)

private theorem convInnerCLM_smul
    (w : L2VF_R3) (hw_H1 : memH1VF_R3 w)
    (hw_sigma : w ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3))
    (hw_sch : IsSchwartzDivFree_R3 ⟨w, hw_sigma⟩) (c : ℝ) (u : H1Sigma') :
    convInnerCLM w hw_H1 hw_sigma hw_sch (c • u)
      = c • convInnerCLM w hw_H1 hw_sigma hw_sch u := by
  unfold convInnerCLM
  rw [innerLin_smul_1 w hw_H1 c u]
  exact extendOfNorm_eH1_smul c (innerLin w hw_H1 u)
    (fun v => innerLin_bound' w hw_H1 hw_sigma hw_sch u v)

/-- The slot-2 inner extension is the genuine `convFormH1` value on H¹ arguments. -/
private theorem convInnerCLM_apply_eH1
    (w : L2VF_R3) (hw_H1 : memH1VF_R3 w)
    (hw_sigma : w ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3))
    (hw_sch : IsSchwartzDivFree_R3 ⟨w, hw_sigma⟩) (u v : H1Sigma') :
    convInnerCLM w hw_H1 hw_sigma hw_sch u (eH1 v) = valH1 w hw_H1 u v := by
  unfold convInnerCLM
  exact LinearMap.extendOfNorm_eq denseRange_eH1
    ⟨cwConst w hw_H1 hw_sigma hw_sch * ‖u‖,
      fun v => innerLin_bound' w hw_H1 hw_sigma hw_sch u v⟩ v

private theorem convInnerCLM_bound
    (w : L2VF_R3) (hw_H1 : memH1VF_R3 w)
    (hw_sigma : w ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3))
    (hw_sch : IsSchwartzDivFree_R3 ⟨w, hw_sigma⟩) (u : H1Sigma') :
    ‖convInnerCLM w hw_H1 hw_sigma hw_sch u‖
      ≤ cwConst w hw_H1 hw_sigma hw_sch * ‖eH1 u‖ := by
  rw [eH1_norm]
  have hCu : 0 ≤ cwConst w hw_H1 hw_sigma hw_sch * ‖u‖ :=
    mul_nonneg (convFormH1_bound_Schwartz w hw_H1 hw_sigma hw_sch).choose_spec.1 (norm_nonneg u)
  refine ContinuousLinearMap.opNorm_le_bound _ hCu (fun x => ?_)
  unfold convInnerCLM
  exact LinearMap.norm_extendOfNorm_apply_le denseRange_eH1 _
    (fun v => innerLin_bound' w hw_H1 hw_sigma hw_sch u v) x

/-- The slot-1 outer linear map `u ↦ Φ u`, before its `L²`-extension. -/
private noncomputable def convOuterLM
    (w : L2VF_R3) (hw_H1 : memH1VF_R3 w)
    (hw_sigma : w ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3))
    (hw_sch : IsSchwartzDivFree_R3 ⟨w, hw_sigma⟩) :
    H1Sigma' →ₗ[ℝ] (L2Sigma_R3 →L[ℝ] ℝ) where
  toFun u := convInnerCLM w hw_H1 hw_sigma hw_sch u
  map_add' u u' := convInnerCLM_add w hw_H1 hw_sigma hw_sch u u'
  map_smul' c u := convInnerCLM_smul w hw_H1 hw_sigma hw_sch c u

/-- The slot-1 outer map as a **continuous** linear map (bound `convInnerCLM_bound`). -/
private noncomputable def convOuterCLM
    (w : L2VF_R3) (hw_H1 : memH1VF_R3 w)
    (hw_sigma : w ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3))
    (hw_sch : IsSchwartzDivFree_R3 ⟨w, hw_sigma⟩) :
    H1Sigma' →L[ℝ] (L2Sigma_R3 →L[ℝ] ℝ) :=
  LinearMap.mkContinuous
    (E := H1Sigma') (F := (L2Sigma_R3 →L[ℝ] ℝ)) (𝕜 := ℝ)
    (convOuterLM w hw_H1 hw_sigma hw_sch)
    (cwConst w hw_H1 hw_sigma hw_sch)
    (fun u => by
      have h := convInnerCLM_bound w hw_H1 hw_sigma hw_sch u
      rw [eH1_norm] at h
      exact h)

private theorem convOuterCLM_apply
    (w : L2VF_R3) (hw_H1 : memH1VF_R3 w)
    (hw_sigma : w ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3))
    (hw_sch : IsSchwartzDivFree_R3 ⟨w, hw_sigma⟩) (u : H1Sigma') :
    convOuterCLM w hw_H1 hw_sigma hw_sch u = convInnerCLM w hw_H1 hw_sigma hw_sch u := by
  rw [convOuterCLM, LinearMap.mkContinuous_apply]
  rfl

/-- The continuous inclusion `H1Sigma' →L[ℝ] L2Sigma_R3`. -/
private noncomputable def eH1L : H1Sigma' →L[ℝ] L2Sigma_R3 := H1Sigma'.subtypeL

private theorem eH1L_apply (u : H1Sigma') : eH1L u = (u : L2Sigma_R3) := rfl

private theorem denseRange_eH1L : DenseRange (eH1L : H1Sigma' → L2Sigma_R3) :=
  denseRange_H1Sigma'_subtype

private theorem isUniformInducing_eH1L : IsUniformInducing (eH1L : H1Sigma' → L2Sigma_R3) :=
  (isUniformEmbedding_subtype_val (p := fun x => x ∈ H1Sigma')).isUniformInducing

/-- **C3 `convBLT_fixedTest` [PR-4 — PROVED].** Jointly continuous bilinear
`L2Sigma_R3 →L[ℝ] L2Sigma_R3 →L[ℝ] ℝ` extending `(u, v) ↦ convFormH1 u v w` for Schwartz
`w`: the slot-2 inner `extendOfNorm` packaged as `convOuterCLM`, then the slot-1
`ContinuousLinearMap.extend` along the dense `H1Sigma' ↪ L2Sigma_R3`. -/
noncomputable def convBLT_fixedTest
    (w : L2VF_R3) (hw_H1 : memH1VF_R3 w)
    (hw_sigma : w ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3))
    (hw_sch : IsSchwartzDivFree_R3 ⟨w, hw_sigma⟩) :
    L2Sigma_R3 →L[ℝ] L2Sigma_R3 →L[ℝ] ℝ :=
  (convOuterCLM w hw_H1 hw_sigma hw_sch).extend eH1L

/-- **The determined-value identity on the H¹ slice.** For H¹ `u, v` (as `H1Sigma'`
elements), `convBLT_fixedTest w u v` is the genuine `convFormH1 u v w`. -/
theorem convBLT_fixedTest_eH1
    (w : L2VF_R3) (hw_H1 : memH1VF_R3 w)
    (hw_sigma : w ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3))
    (hw_sch : IsSchwartzDivFree_R3 ⟨w, hw_sigma⟩) (u v : H1Sigma') :
    convBLT_fixedTest w hw_H1 hw_sigma hw_sch (eH1L u) (eH1L v) = valH1 w hw_H1 u v := by
  unfold convBLT_fixedTest
  rw [ContinuousLinearMap.extend_eq _ denseRange_eH1L isUniformInducing_eH1L u,
    convOuterCLM_apply w hw_H1 hw_sigma hw_sch u]
  -- `eH1L v = eH1 v` and `convInnerCLM u (eH1 v) = valH1 u v`.
  have hev : (eH1L v : L2Sigma_R3) = eH1 v := rfl
  rw [hev]
  exact convInnerCLM_apply_eH1 w hw_H1 hw_sigma hw_sch u v

/-! #### C3b — `w`-linearity of `convBLT_fixedTest`

The jointly continuous extension `convBLT_fixedTest w` is **linear in the fixed Schwartz
test `w`**.  Two such CLMs agreeing on the dense `H1Sigma' × H1Sigma'` square are equal
(`eqOn_closure₂'` over the dense range of `eH1L`), and on that square the value is the
genuine `convFormH1 u v w` which is additive/homogeneous in `w` (B4c `convFormH1_add_3`,
B4d `convFormH1_smul_3`).  This is the span-representation-independence content the
edge bilinear needs. -/

/-- Two continuous bilinear forms on `L2Sigma_R3` agreeing on the dense
`range eH1L × range eH1L` square are equal. -/
private theorem convBLT_ext_of_agree_eH1
    {B₁ B₂ : L2Sigma_R3 →L[ℝ] L2Sigma_R3 →L[ℝ] ℝ}
    (h : ∀ u v : H1Sigma', B₁ (eH1L u) (eH1L v) = B₂ (eH1L u) (eH1L v)) :
    B₁ = B₂ := by
  -- Reduce to equality of the underlying functions `L² × L² → ℝ`.
  have hfun : (fun a => fun b => B₁ a b) = (fun a => fun b => B₂ a b) := by
    have key : ∀ a ∈ closure (Set.range (eH1L : H1Sigma' → L2Sigma_R3)),
        ∀ b ∈ closure (Set.range (eH1L : H1Sigma' → L2Sigma_R3)),
        B₁ a b = B₂ a b := by
      refine eqOn_closure₂'
        (s := Set.range (eH1L : H1Sigma' → L2Sigma_R3))
        (t := Set.range (eH1L : H1Sigma' → L2Sigma_R3))
        (f := fun a b => B₁ a b) (g := fun a b => B₂ a b) ?_ ?_ ?_ ?_ ?_
      · rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩; exact h u v
      · intro a; exact (B₁ a).continuous
      · intro b; exact (B₁.flip b).continuous
      · intro a; exact (B₂ a).continuous
      · intro b; exact (B₂.flip b).continuous
    funext a b
    have hda : a ∈ closure (Set.range (eH1L : H1Sigma' → L2Sigma_R3)) :=
      denseRange_eH1L a
    have hdb : b ∈ closure (Set.range (eH1L : H1Sigma' → L2Sigma_R3)) :=
      denseRange_eH1L b
    exact key a hda b hdb
  ext a b
  exact congrFun (congrFun hfun a) b

/-- `convBLT_fixedTest` is **additive in the test `w`**: for two Schwartz tests `w, w'`,
`convBLT_fixedTest (w + w') = convBLT_fixedTest w + convBLT_fixedTest w'`. -/
private theorem convBLT_fixedTest_add_w
    (w w' : L2VF_R3)
    (hw_H1 : memH1VF_R3 w) (hw_sigma : w ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3))
    (hw_sch : IsSchwartzDivFree_R3 ⟨w, hw_sigma⟩)
    (hw'_H1 : memH1VF_R3 w') (hw'_sigma : w' ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3))
    (hw'_sch : IsSchwartzDivFree_R3 ⟨w', hw'_sigma⟩)
    (hsum_H1 : memH1VF_R3 (w + w'))
    (hsum_sigma : (w + w') ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3))
    (hsum_sch : IsSchwartzDivFree_R3 ⟨w + w', hsum_sigma⟩) :
    convBLT_fixedTest (w + w') hsum_H1 hsum_sigma hsum_sch
      = convBLT_fixedTest w hw_H1 hw_sigma hw_sch
        + convBLT_fixedTest w' hw'_H1 hw'_sigma hw'_sch := by
  refine convBLT_ext_of_agree_eH1 (fun u v => ?_)
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply,
    convBLT_fixedTest_eH1 (w + w') hsum_H1 hsum_sigma hsum_sch u v,
    convBLT_fixedTest_eH1 w hw_H1 hw_sigma hw_sch u v,
    convBLT_fixedTest_eH1 w' hw'_H1 hw'_sigma hw'_sch u v]
  -- `valH1 (w+w') = valH1 w + valH1 w'` is B4c `convFormH1_add_3`.
  unfold valH1
  exact convFormH1_add_3 (vfOf u) (vfOf v) w w' (vfOf_mem u) (vfOf_mem v) hw_H1 hw'_H1

/-- `convBLT_fixedTest` is **homogeneous in the test `w`**: for a Schwartz test `w` and
scalar `c`, `convBLT_fixedTest (c • w) = c • convBLT_fixedTest w`. -/
private theorem convBLT_fixedTest_smul_w
    (c : ℝ) (w : L2VF_R3)
    (hw_H1 : memH1VF_R3 w) (hw_sigma : w ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3))
    (hw_sch : IsSchwartzDivFree_R3 ⟨w, hw_sigma⟩)
    (hcw_H1 : memH1VF_R3 (c • w))
    (hcw_sigma : (c • w) ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3))
    (hcw_sch : IsSchwartzDivFree_R3 ⟨c • w, hcw_sigma⟩) :
    convBLT_fixedTest (c • w) hcw_H1 hcw_sigma hcw_sch
      = c • convBLT_fixedTest w hw_H1 hw_sigma hw_sch := by
  refine convBLT_ext_of_agree_eH1 (fun u v => ?_)
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply,
    convBLT_fixedTest_eH1 (c • w) hcw_H1 hcw_sigma hcw_sch u v,
    convBLT_fixedTest_eH1 w hw_H1 hw_sigma hw_sch u v]
  unfold valH1
  rw [smul_eq_mul]
  exact convFormH1_smul_3 c (vfOf u) (vfOf v) w (vfOf_mem u) (vfOf_mem v) hw_H1

/-! #### C3c — the **bounded** convBLT tower (for `schwartzSpan` test fields `w`)

The existing `convBLT_fixedTest` tower is hard-wired to a *single* `IsSchwartzDivFree_R3`
test via `convFormH1_bound_Schwartz`.  For the determined-edge construction we need the
same jointly continuous bilinear extension for an arbitrary `w ∈ schwartzSpan` (a finite
ℝ-combination of Schwartz-div-free fields), where the only input is an **explicit B7-type
bound** `|convFormH1 u v w| ≤ C ‖u‖ ‖v‖`.  We mirror the slot-2/slot-1 `extendOfNorm` /
`extend` tower, taking the bound `(C, hC, hbound)` as a hypothesis. -/

/-- The packaged uniform bound for `innerLin` in the bounded tower. -/
private theorem innerLin_bound_bdd
    (w : L2VF_R3) (hw_H1 : memH1VF_R3 w)
    {C : ℝ}
    (hbound : ∀ (u v : L2VF_R3) (hu : memH1VF_R3 u) (hv : memH1VF_R3 v)
      (hu_sigma : u ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3))
      (hv_sigma : v ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3)),
      |convFormH1 u v w hu hv hw_H1| ≤ C * ‖u‖ * ‖v‖)
    (u v : H1Sigma') :
    ‖innerLin w hw_H1 u v‖ ≤ C * ‖u‖ * ‖eH1 v‖ := by
  have hu_sigma : (vfOf u) ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3) := (u : L2Sigma_R3).2
  have hv_sigma : (vfOf v) ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3) := (v : L2Sigma_R3).2
  have := hbound (vfOf u) (vfOf v) (vfOf_mem u) (vfOf_mem v) hu_sigma hv_sigma
  rw [eH1_norm, Real.norm_eq_abs, norm_eq_vfOf u, norm_eq_vfOf v]
  exact this

/-- Bounded slot-2 inner extension `Φ_bdd u : L2Sigma_R3 →L ℝ`. -/
private noncomputable def convInnerCLMb
    (w : L2VF_R3) (hw_H1 : memH1VF_R3 w) (u : H1Sigma') :
    L2Sigma_R3 →L[ℝ] ℝ :=
  (innerLin w hw_H1 u).extendOfNorm eH1

private theorem convInnerCLMb_add
    (w : L2VF_R3) (hw_H1 : memH1VF_R3 w)
    {C : ℝ}
    (hbound : ∀ (u v : L2VF_R3) (hu : memH1VF_R3 u) (hv : memH1VF_R3 v)
      (hu_sigma : u ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3))
      (hv_sigma : v ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3)),
      |convFormH1 u v w hu hv hw_H1| ≤ C * ‖u‖ * ‖v‖)
    (u u' : H1Sigma') :
    convInnerCLMb w hw_H1 (u + u') = convInnerCLMb w hw_H1 u + convInnerCLMb w hw_H1 u' := by
  unfold convInnerCLMb
  rw [innerLin_add_1 w hw_H1 u u']
  exact extendOfNorm_eH1_add (innerLin w hw_H1 u) (innerLin w hw_H1 u')
    (fun v => innerLin_bound_bdd w hw_H1 hbound u v)
    (fun v => innerLin_bound_bdd w hw_H1 hbound u' v)

private theorem convInnerCLMb_smul
    (w : L2VF_R3) (hw_H1 : memH1VF_R3 w)
    {C : ℝ}
    (hbound : ∀ (u v : L2VF_R3) (hu : memH1VF_R3 u) (hv : memH1VF_R3 v)
      (hu_sigma : u ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3))
      (hv_sigma : v ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3)),
      |convFormH1 u v w hu hv hw_H1| ≤ C * ‖u‖ * ‖v‖)
    (c : ℝ) (u : H1Sigma') :
    convInnerCLMb w hw_H1 (c • u) = c • convInnerCLMb w hw_H1 u := by
  unfold convInnerCLMb
  rw [innerLin_smul_1 w hw_H1 c u]
  exact extendOfNorm_eH1_smul c (innerLin w hw_H1 u)
    (fun v => innerLin_bound_bdd w hw_H1 hbound u v)

private theorem convInnerCLMb_apply_eH1
    (w : L2VF_R3) (hw_H1 : memH1VF_R3 w)
    {C : ℝ}
    (hbound : ∀ (u v : L2VF_R3) (hu : memH1VF_R3 u) (hv : memH1VF_R3 v)
      (hu_sigma : u ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3))
      (hv_sigma : v ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3)),
      |convFormH1 u v w hu hv hw_H1| ≤ C * ‖u‖ * ‖v‖)
    (u v : H1Sigma') :
    convInnerCLMb w hw_H1 u (eH1 v) = valH1 w hw_H1 u v := by
  unfold convInnerCLMb
  exact LinearMap.extendOfNorm_eq denseRange_eH1
    ⟨C * ‖u‖, fun v => innerLin_bound_bdd w hw_H1 hbound u v⟩ v

private theorem convInnerCLMb_bound
    (w : L2VF_R3) (hw_H1 : memH1VF_R3 w)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ (u v : L2VF_R3) (hu : memH1VF_R3 u) (hv : memH1VF_R3 v)
      (hu_sigma : u ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3))
      (hv_sigma : v ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3)),
      |convFormH1 u v w hu hv hw_H1| ≤ C * ‖u‖ * ‖v‖)
    (u : H1Sigma') :
    ‖convInnerCLMb w hw_H1 u‖ ≤ C * ‖eH1 u‖ := by
  rw [eH1_norm]
  have hCu : 0 ≤ C * ‖u‖ := mul_nonneg hC (norm_nonneg u)
  refine ContinuousLinearMap.opNorm_le_bound _ hCu (fun x => ?_)
  unfold convInnerCLMb
  exact LinearMap.norm_extendOfNorm_apply_le denseRange_eH1 _
    (fun v => innerLin_bound_bdd w hw_H1 hbound u v) x

/-- Bounded slot-1 outer linear map. -/
private noncomputable def convOuterLMb
    (w : L2VF_R3) (hw_H1 : memH1VF_R3 w)
    {C : ℝ}
    (hbound : ∀ (u v : L2VF_R3) (hu : memH1VF_R3 u) (hv : memH1VF_R3 v)
      (hu_sigma : u ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3))
      (hv_sigma : v ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3)),
      |convFormH1 u v w hu hv hw_H1| ≤ C * ‖u‖ * ‖v‖) :
    H1Sigma' →ₗ[ℝ] (L2Sigma_R3 →L[ℝ] ℝ) where
  toFun u := convInnerCLMb w hw_H1 u
  map_add' u u' := convInnerCLMb_add w hw_H1 hbound u u'
  map_smul' c u := convInnerCLMb_smul w hw_H1 hbound c u

/-- Bounded slot-1 outer **continuous** linear map. -/
private noncomputable def convOuterCLMb
    (w : L2VF_R3) (hw_H1 : memH1VF_R3 w)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ (u v : L2VF_R3) (hu : memH1VF_R3 u) (hv : memH1VF_R3 v)
      (hu_sigma : u ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3))
      (hv_sigma : v ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3)),
      |convFormH1 u v w hu hv hw_H1| ≤ C * ‖u‖ * ‖v‖) :
    H1Sigma' →L[ℝ] (L2Sigma_R3 →L[ℝ] ℝ) :=
  LinearMap.mkContinuous
    (E := H1Sigma') (F := (L2Sigma_R3 →L[ℝ] ℝ)) (𝕜 := ℝ)
    (convOuterLMb w hw_H1 hbound) C
    (fun u => by
      have h := convInnerCLMb_bound w hw_H1 hC hbound u
      rw [eH1_norm] at h
      exact h)

private theorem convOuterCLMb_apply
    (w : L2VF_R3) (hw_H1 : memH1VF_R3 w)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ (u v : L2VF_R3) (hu : memH1VF_R3 u) (hv : memH1VF_R3 v)
      (hu_sigma : u ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3))
      (hv_sigma : v ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3)),
      |convFormH1 u v w hu hv hw_H1| ≤ C * ‖u‖ * ‖v‖)
    (u : H1Sigma') :
    convOuterCLMb w hw_H1 hC hbound u = convInnerCLMb w hw_H1 u := by
  rw [convOuterCLMb, LinearMap.mkContinuous_apply]
  rfl

/-- **Bounded jointly continuous bilinear extension `convBLTbdd`.** Same construction as
`convBLT_fixedTest`, but driven by an explicit B7-type bound rather than a single
`IsSchwartzDivFree_R3` witness, so it applies to any `w ∈ schwartzSpan`. -/
private noncomputable def convBLTbdd
    (w : L2VF_R3) (hw_H1 : memH1VF_R3 w)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ (u v : L2VF_R3) (hu : memH1VF_R3 u) (hv : memH1VF_R3 v)
      (hu_sigma : u ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3))
      (hv_sigma : v ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3)),
      |convFormH1 u v w hu hv hw_H1| ≤ C * ‖u‖ * ‖v‖) :
    L2Sigma_R3 →L[ℝ] L2Sigma_R3 →L[ℝ] ℝ :=
  (convOuterCLMb w hw_H1 hC hbound).extend eH1L

private theorem convBLTbdd_eH1
    (w : L2VF_R3) (hw_H1 : memH1VF_R3 w)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ (u v : L2VF_R3) (hu : memH1VF_R3 u) (hv : memH1VF_R3 v)
      (hu_sigma : u ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3))
      (hv_sigma : v ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3)),
      |convFormH1 u v w hu hv hw_H1| ≤ C * ‖u‖ * ‖v‖)
    (u v : H1Sigma') :
    convBLTbdd w hw_H1 hC hbound (eH1L u) (eH1L v) = valH1 w hw_H1 u v := by
  unfold convBLTbdd
  rw [ContinuousLinearMap.extend_eq _ denseRange_eH1L isUniformInducing_eH1L u,
    convOuterCLMb_apply w hw_H1 hC hbound u]
  have hev : (eH1L v : L2Sigma_R3) = eH1 v := rfl
  rw [hev]
  exact convInnerCLMb_apply_eH1 w hw_H1 hbound u v

/-- On a single Schwartz `w`, `convBLTbdd` (with the B7 bound) agrees with `convBLT_fixedTest`:
both are the unique continuous bilinear extension of the same `valH1`. -/
private theorem convBLTbdd_eq_convBLT_fixedTest
    (w : L2VF_R3) (hw_H1 : memH1VF_R3 w)
    (hw_sigma : w ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3))
    (hw_sch : IsSchwartzDivFree_R3 ⟨w, hw_sigma⟩)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ (u v : L2VF_R3) (hu : memH1VF_R3 u) (hv : memH1VF_R3 v)
      (hu_sigma : u ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3))
      (hv_sigma : v ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3)),
      |convFormH1 u v w hu hv hw_H1| ≤ C * ‖u‖ * ‖v‖) :
    convBLTbdd w hw_H1 hC hbound = convBLT_fixedTest w hw_H1 hw_sigma hw_sch := by
  refine convBLT_ext_of_agree_eH1 (fun u v => ?_)
  rw [convBLTbdd_eH1 w hw_H1 hC hbound u v,
    convBLT_fixedTest_eH1 w hw_H1 hw_sigma hw_sch u v]

/-! #### C3d — `schwartzSpan` is H¹, and `convFormH1` is B7-bounded on it

Every `s ∈ schwartzSpan` is a finite ℝ-combination of Schwartz-div-free fields, hence H¹
(`schwartzSpan ≤ H1Sigma'`), and `(u,v) ↦ convFormH1 u v s` is `L²`-bounded (the B7 bound
sums over the combination, `Submodule.span_induction`).  This makes `convBLTbdd` available
for `s`, giving the **determined edge value** for the construction. -/

/-- `schwartzSpan ≤ H1Sigma'`: span members are H¹. -/
theorem schwartzSpan_le_H1Sigma' : schwartzSpan ≤ H1Sigma' := by
  rw [schwartzSpan, Submodule.span_le]
  intro x hx
  exact schwartz_mem_H1Sigma' hx

/-- The H¹ representative proof for a `schwartzSpan` member. -/
theorem memH1VF_R3_of_mem_schwartzSpan {s : L2Sigma_R3} (hs : s ∈ schwartzSpan) :
    memH1VF_R3 (s : L2VF_R3) :=
  H1Sigma'_memH1 (schwartzSpan_le_H1Sigma' hs)

/-- **B7 bound for `schwartzSpan` members.** For `s ∈ schwartzSpan`, there is a constant
`C ≥ 0` with `|convFormH1 u v s| ≤ C ‖u‖ ‖v‖` for all H¹-σ `u, v`. -/
theorem convFormH1_bound_span {s : L2Sigma_R3} (hs : s ∈ schwartzSpan) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (hsH1 : memH1VF_R3 (s : L2VF_R3))
        (u v : L2VF_R3) (hu : memH1VF_R3 u) (hv : memH1VF_R3 v)
        (hu_sigma : u ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3))
        (hv_sigma : v ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3)),
        |convFormH1 u v (s : L2VF_R3) hu hv hsH1| ≤ C * ‖u‖ * ‖v‖ := by
  -- Predicate for span induction.
  set P : (x : L2Sigma_R3) → Prop := fun x =>
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (hxH1 : memH1VF_R3 (x : L2VF_R3))
        (u v : L2VF_R3) (hu : memH1VF_R3 u) (hv : memH1VF_R3 v)
        (hu_sigma : u ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3))
        (hv_sigma : v ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3)),
        |convFormH1 u v (x : L2VF_R3) hu hv hxH1| ≤ C * ‖u‖ * ‖v‖ with hP
  rw [schwartzSpan] at hs
  refine Submodule.span_induction (p := fun x _ => P x) ?_ ?_ ?_ ?_ hs
  · -- generators: single Schwartz-div-free. Use B7.
    intro x hx
    -- `x : L2Sigma_R3` with `IsSchwartzDivFree_R3 x`.
    obtain ⟨C, hC, hbound⟩ := convFormH1_bound_Schwartz (x : L2VF_R3)
      (memH1VF_R3_of_schwartz hx) x.2 (by simpa using hx)
    refine ⟨C, hC, fun hxH1 u v hu hv hu_sigma hv_sigma => ?_⟩
    exact hbound u v hu hv hu_sigma hv_sigma
  · -- zero
    refine ⟨0, le_rfl, fun hxH1 u v hu hv hu_sigma hv_sigma => ?_⟩
    have hval : convFormH1 u v ((0 : L2Sigma_R3) : L2VF_R3) hu hv hxH1 = 0 := by
      have hsmul := convFormH1_smul_3 (0 : ℝ) u v (0 : L2VF_R3) hu hv memH1VF_R3_zero
      rw [zero_mul] at hsmul
      rw [show convFormH1 u v ((0 : L2Sigma_R3) : L2VF_R3) hu hv hxH1
          = convFormH1 u v ((0 : ℝ) • (0 : L2VF_R3)) hu hv
              (memH1VF_R3_smul (0 : ℝ) memH1VF_R3_zero) from by congr 1 <;> simp]
      exact hsmul
    rw [hval]; simp
  · -- add
    rintro x y hx hy ⟨Cx, hCx, hbx⟩ ⟨Cy, hCy, hby⟩
    refine ⟨Cx + Cy, by positivity, fun hxyH1 u v hu hv hu_sigma hv_sigma => ?_⟩
    have hxH1 : memH1VF_R3 (x : L2VF_R3) := memH1VF_R3_of_mem_schwartzSpan (by rw [schwartzSpan]; exact hx)
    have hyH1 : memH1VF_R3 (y : L2VF_R3) := memH1VF_R3_of_mem_schwartzSpan (by rw [schwartzSpan]; exact hy)
    have hsplit : convFormH1 u v ((x + y : L2Sigma_R3) : L2VF_R3) hu hv hxyH1
        = convFormH1 u v (x : L2VF_R3) hu hv hxH1
          + convFormH1 u v (y : L2VF_R3) hu hv hyH1 := by
      have hcoe : ((x + y : L2Sigma_R3) : L2VF_R3) = (x : L2VF_R3) + (y : L2VF_R3) := by
        simp
      rw [show convFormH1 u v ((x + y : L2Sigma_R3) : L2VF_R3) hu hv hxyH1
          = convFormH1 u v ((x : L2VF_R3) + (y : L2VF_R3)) hu hv
              (memH1VF_R3_add hxH1 hyH1) from by congr 1 <;> simp,
        convFormH1_add_3 u v (x : L2VF_R3) (y : L2VF_R3) hu hv hxH1 hyH1]
    rw [hsplit]
    calc |convFormH1 u v (x : L2VF_R3) hu hv hxH1 + convFormH1 u v (y : L2VF_R3) hu hv hyH1|
        ≤ |convFormH1 u v (x : L2VF_R3) hu hv hxH1| + |convFormH1 u v (y : L2VF_R3) hu hv hyH1| :=
          abs_add_le _ _
      _ ≤ Cx * ‖u‖ * ‖v‖ + Cy * ‖u‖ * ‖v‖ :=
          add_le_add (hbx hxH1 u v hu hv hu_sigma hv_sigma) (hby hyH1 u v hu hv hu_sigma hv_sigma)
      _ = (Cx + Cy) * ‖u‖ * ‖v‖ := by ring
  · -- smul
    rintro a x hx ⟨Cx, hCx, hbx⟩
    refine ⟨|a| * Cx, by positivity, fun haxH1 u v hu hv hu_sigma hv_sigma => ?_⟩
    have hxH1 : memH1VF_R3 (x : L2VF_R3) := memH1VF_R3_of_mem_schwartzSpan (by rw [schwartzSpan]; exact hx)
    have hsmul : convFormH1 u v ((a • x : L2Sigma_R3) : L2VF_R3) hu hv haxH1
        = a * convFormH1 u v (x : L2VF_R3) hu hv hxH1 := by
      rw [show convFormH1 u v ((a • x : L2Sigma_R3) : L2VF_R3) hu hv haxH1
          = convFormH1 u v (a • (x : L2VF_R3)) hu hv
              (memH1VF_R3_smul a hxH1) from by congr 1 <;> simp,
        convFormH1_smul_3 a u v (x : L2VF_R3) hu hv hxH1]
    rw [hsmul, abs_mul]
    calc |a| * |convFormH1 u v (x : L2VF_R3) hu hv hxH1|
        ≤ |a| * (Cx * ‖u‖ * ‖v‖) :=
          mul_le_mul_of_nonneg_left (hbx hxH1 u v hu hv hu_sigma hv_sigma) (abs_nonneg a)
      _ = |a| * Cx * ‖u‖ * ‖v‖ := by ring

/-! #### C3e — `convBLTspan`: the jointly continuous bilinear for `s ∈ schwartzSpan`,
linear in `s`

For each `s ∈ schwartzSpan` we package its B7-span bound and run `convBLTbdd`, yielding a
jointly continuous bilinear `convBLTspan s : L² →L L² →L ℝ` extending `convFormH1 u v s`.
The map `s ↦ convBLTspan s` is **ℝ-linear** over `schwartzSpan` (same dense-agreement
argument as `convBLT_fixedTest_add_w`/`_smul_w`, with B4c/B4d slot-3 linearity of
`convFormH1`).  This is the determined slot-3 edge value. -/

/-- `convFormH1` only depends on the underlying third argument (proof-irrelevant in the
H¹ membership witness): if `w = w'` then the values agree. -/
private theorem convFormH1_eq_of_third_eq (u v w w' : L2VF_R3)
    (hw : memH1VF_R3 w) (hw' : memH1VF_R3 w')
    (hu : memH1VF_R3 u) (hv : memH1VF_R3 v) (h : w = w') :
    convFormH1 u v w hu hv hw = convFormH1 u v w' hu hv hw' := by
  subst h; rfl

/-- The chosen B7-span constant proof bundle for `s ∈ schwartzSpan`. -/
private theorem convBLTspan_bound_spec {s : L2Sigma_R3} (hs : s ∈ schwartzSpan) :
    0 ≤ (convFormH1_bound_span hs).choose ∧
      ∀ (u v : L2VF_R3) (hu : memH1VF_R3 u) (hv : memH1VF_R3 v)
        (hu_sigma : u ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3))
        (hv_sigma : v ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3)),
        |convFormH1 u v (s : L2VF_R3) hu hv (memH1VF_R3_of_mem_schwartzSpan hs)|
          ≤ (convFormH1_bound_span hs).choose * ‖u‖ * ‖v‖ := by
  refine ⟨(convFormH1_bound_span hs).choose_spec.1, fun u v hu hv hu_sigma hv_sigma => ?_⟩
  exact (convFormH1_bound_span hs).choose_spec.2
    (memH1VF_R3_of_mem_schwartzSpan hs) u v hu hv hu_sigma hv_sigma

/-- **`convBLTspan`.** The determined jointly continuous bilinear extension for a span
test field `s ∈ schwartzSpan`. -/
noncomputable def convBLTspan (s : schwartzSpan) :
    L2Sigma_R3 →L[ℝ] L2Sigma_R3 →L[ℝ] ℝ :=
  convBLTbdd (s : L2VF_R3) (memH1VF_R3_of_mem_schwartzSpan s.2)
    (convBLTspan_bound_spec s.2).1 (convBLTspan_bound_spec s.2).2

/-- `convBLTspan s` on the H¹ slice is the genuine `convFormH1`. -/
private theorem convBLTspan_eH1 (s : schwartzSpan) (u v : H1Sigma') :
    convBLTspan s (eH1L u) (eH1L v)
      = convFormH1 (vfOf u) (vfOf v) (s : L2VF_R3)
          (vfOf_mem u) (vfOf_mem v) (memH1VF_R3_of_mem_schwartzSpan s.2) := by
  unfold convBLTspan
  rw [convBLTbdd_eH1 (s : L2VF_R3) (memH1VF_R3_of_mem_schwartzSpan s.2)
    (convBLTspan_bound_spec s.2).1 (convBLTspan_bound_spec s.2).2 u v]
  rfl

/-- Coercion `schwartzSpan → L2VF_R3` of a sum splits. -/
private theorem schwartzSpan_coe_add (s s' : schwartzSpan) :
    ((s + s' : schwartzSpan) : L2VF_R3) = (s : L2VF_R3) + (s' : L2VF_R3) := by
  rfl

/-- Coercion `schwartzSpan → L2VF_R3` of a scalar multiple. -/
private theorem schwartzSpan_coe_smul (c : ℝ) (s : schwartzSpan) :
    ((c • s : schwartzSpan) : L2VF_R3) = c • (s : L2VF_R3) := by
  rfl

/-- On a single Schwartz `w`, `convBLTspan ⟨w, _⟩` agrees with `convBLT_fixedTest w`. -/
private theorem convBLTspan_eq_fixedTest
    (w : L2VF_R3) (hw_H1 : memH1VF_R3 w)
    (hw_sigma : w ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3))
    (hw_sch : IsSchwartzDivFree_R3 ⟨w, hw_sigma⟩)
    (hmem : (⟨w, hw_sigma⟩ : L2Sigma_R3) ∈ schwartzSpan) :
    convBLTspan ⟨⟨w, hw_sigma⟩, hmem⟩ = convBLT_fixedTest w hw_H1 hw_sigma hw_sch := by
  refine convBLT_ext_of_agree_eH1 (fun u v => ?_)
  rw [convBLTspan_eH1 ⟨⟨w, hw_sigma⟩, hmem⟩ u v,
    convBLT_fixedTest_eH1 w hw_H1 hw_sigma hw_sch u v]
  rfl

set_option maxHeartbeats 4000000 in
/-- `convBLTspan` is additive in `s`. -/
private theorem convBLTspan_add (s s' : schwartzSpan) :
    convBLTspan (s + s') = convBLTspan s + convBLTspan s' := by
  refine convBLT_ext_of_agree_eH1 (fun u v => ?_)
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply,
    convBLTspan_eH1 (s + s') u v, convBLTspan_eH1 s u v, convBLTspan_eH1 s' u v]
  -- B4c slot-3 additivity, modulo the (defeq) span coercion.
  have hcoe := schwartzSpan_coe_add s s'
  rw [convFormH1_eq_of_third_eq (vfOf u) (vfOf v) _ _
      (memH1VF_R3_of_mem_schwartzSpan (s + s').2)
      (memH1VF_R3_add (memH1VF_R3_of_mem_schwartzSpan s.2)
        (memH1VF_R3_of_mem_schwartzSpan s'.2)) (vfOf_mem u) (vfOf_mem v) hcoe,
    convFormH1_add_3 (vfOf u) (vfOf v) (s : L2VF_R3) (s' : L2VF_R3)
      (vfOf_mem u) (vfOf_mem v)
      (memH1VF_R3_of_mem_schwartzSpan s.2) (memH1VF_R3_of_mem_schwartzSpan s'.2)]

set_option maxHeartbeats 4000000 in
/-- `convBLTspan` is homogeneous in `s`. -/
private theorem convBLTspan_smul (c : ℝ) (s : schwartzSpan) :
    convBLTspan (c • s) = c • convBLTspan s := by
  refine convBLT_ext_of_agree_eH1 (fun u v => ?_)
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply,
    convBLTspan_eH1 (c • s) u v, convBLTspan_eH1 s u v, smul_eq_mul]
  have hcoe := schwartzSpan_coe_smul c s
  rw [convFormH1_eq_of_third_eq (vfOf u) (vfOf v) _ _
      (memH1VF_R3_of_mem_schwartzSpan (c • s).2)
      (memH1VF_R3_smul c (memH1VF_R3_of_mem_schwartzSpan s.2)) (vfOf_mem u) (vfOf_mem v) hcoe,
    convFormH1_smul_3 c (vfOf u) (vfOf v) (s : L2VF_R3)
      (vfOf_mem u) (vfOf_mem v) (memH1VF_R3_of_mem_schwartzSpan s.2)]

/-- `convBLTspan` packaged as an ℝ-linear map `schwartzSpan →ₗ (L² →L L² →L ℝ)`. -/
noncomputable def convBLTspanLin :
    schwartzSpan →ₗ[ℝ] (L2Sigma_R3 →L[ℝ] L2Sigma_R3 →L[ℝ] ℝ) where
  toFun := convBLTspan
  map_add' := convBLTspan_add
  map_smul' c s := by simpa using convBLTspan_smul c s

@[simp]
theorem convBLTspanLin_apply (s : schwartzSpan) : convBLTspanLin s = convBLTspan s := rfl

attribute [irreducible] convBLTspanLin

-- Past this point `convBLTspan` is treated opaquely: all downstream reasoning goes
-- through the lemma interface (`convBLTspan_eH1`, the `_tmul` lemmas, `_add`, `_smul`,
-- `_u_add`, `_u_smul`, `_overlap`).  Marking it irreducible avoids ruinous `isDefEq`
-- unfolding of the large extension tower during tensor/edge manipulations.
attribute [irreducible] convBLTspan

/-- `convBLTspan s` is additive in its first slot `u` (CLM linearity, isolated). -/
private theorem convBLTspan_u_add (s : schwartzSpan) (u u' : L2Sigma_R3) :
    convBLTspan s (u + u') = convBLTspan s u + convBLTspan s u' :=
  (convBLTspan s).map_add u u'

/-- `convBLTspan s` is homogeneous in its first slot `u`. -/
private theorem convBLTspan_u_smul (s : schwartzSpan) (c : ℝ) (u : L2Sigma_R3) :
    convBLTspan s (c • u) = c • convBLTspan s u :=
  (convBLTspan s).map_smul c u

/-! ### C4 — the two edge bilinears on the tensor product

`D := (𝒮 ⊗ L²_σ) + (L²_σ ⊗ 𝒮)`, realized as the supremum of the two tensor-map ranges
inside `L²_σ ⊗[ℝ] L²_σ`.  We name the two range-submodules and `D` itself here. -/

/-- The "slot-2 Schwartz" edge submodule `𝒮 ⊗ L²_σ ≤ L²_σ ⊗ L²_σ`. -/
noncomputable def edgeSlot2 : Submodule ℝ (TensorProduct ℝ L2Sigma_R3 L2Sigma_R3) :=
  LinearMap.range (TensorProduct.map schwartzSpan.subtype (LinearMap.id : L2Sigma_R3 →ₗ[ℝ] L2Sigma_R3))

/-- The "slot-3 Schwartz" edge submodule `L²_σ ⊗ 𝒮 ≤ L²_σ ⊗ L²_σ`. -/
noncomputable def edgeSlot3 : Submodule ℝ (TensorProduct ℝ L2Sigma_R3 L2Sigma_R3) :=
  LinearMap.range (TensorProduct.map (LinearMap.id : L2Sigma_R3 →ₗ[ℝ] L2Sigma_R3) schwartzSpan.subtype)

/-- **`D` (the determined domain).** `D := (𝒮 ⊗ L²_σ) + (L²_σ ⊗ 𝒮)`. -/
noncomputable def detDomain : Submodule ℝ (TensorProduct ℝ L2Sigma_R3 L2Sigma_R3) :=
  edgeSlot2 ⊔ edgeSlot3

/-- **The overlap identity (consumes the proved tensor-intersection lemma).**
`(𝒮 ⊗ L²_σ) ⊓ (L²_σ ⊗ 𝒮) = 𝒮 ⊗ 𝒮`, on whose image the two edge prescriptions agree.
This is `TensorIntersection.range_map_subtype_inf_range_map_subtype` specialized to
`S = schwartzSpan`. -/
theorem edge_inf_eq_schwartz_tensor :
    edgeSlot2 ⊓ edgeSlot3
      = LinearMap.range (TensorProduct.mapIncl schwartzSpan schwartzSpan) :=
  LerayHopf.R3.TensorIntersection.range_map_subtype_inf_range_map_subtype schwartzSpan

/-! ### C5 — the determined antisymmetric bilinear `β_u` on `D`, Hamel-extended

For fixed `u`, the two edge prescriptions are:

- on `𝒮 ⊗ L²_σ`: the bilinear `(s, l) ↦ convFormH1 u s l` (slot-2 Schwartz, B7-bounded in
  `l`), lifted by `TensorProduct.lift` to a `LinearMap` on `edgeSlot2`;
- on `L²_σ ⊗ 𝒮`: `(l, s) ↦ convFormH1 u l s = − convFormH1 u s l` (B6), lifted to a
  `LinearMap` on `edgeSlot3`.

They agree on `edgeSlot2 ⊓ edgeSlot3 = 𝒮 ⊗ 𝒮` (B6/div-free identity), so `LinearPMap.sup`
glues them to a single partial linear map on `detDomain = D`.  A fixed left inverse of
`detDomain.subtype` Hamel-extends to all of `L²_σ ⊗ L²_σ`; the whole tower is built
linearly in `u`. -/

/-! #### C5-a — evaluation functionals and the two edge bilinears -/

/-- The `ℝ`-linear evaluation `B ↦ B u v` on continuous bilinear forms. -/
private noncomputable def evalBil (u v : L2Sigma_R3) :
    (L2Sigma_R3 →L[ℝ] L2Sigma_R3 →L[ℝ] ℝ) →ₗ[ℝ] ℝ where
  toFun B := B u v
  map_add' B B' := by simp
  map_smul' c B := by simp

/-- The slot-3 determined value as a linear functional in the Schwartz factor:
`s ↦ convBLTspan s u v`. -/
private noncomputable def edge3Sval (u v : L2Sigma_R3) : schwartzSpan →ₗ[ℝ] ℝ :=
  (evalBil u v).comp convBLTspanLin

@[simp]
private theorem edge3Sval_apply (u v : L2Sigma_R3) (s : schwartzSpan) :
    edge3Sval u v s = convBLTspan s u v := by
  unfold edge3Sval
  rw [LinearMap.comp_apply, convBLTspanLin_apply]; rfl

/-- The slot-3 edge bilinear `b3 u : L²_σ →ₗ 𝒮 →ₗ ℝ`, `b3 u v s = convBLTspan s u v`. -/
private noncomputable def edge3Bil (u : L2Sigma_R3) :
    L2Sigma_R3 →ₗ[ℝ] schwartzSpan →ₗ[ℝ] ℝ where
  toFun v := edge3Sval u v
  map_add' v v' := by
    refine LinearMap.ext (fun s => ?_)
    simp [edge3Sval_apply, LinearMap.add_apply, map_add]
  map_smul' c v := by
    refine LinearMap.ext (fun s => ?_)
    simp [edge3Sval_apply, LinearMap.smul_apply, map_smul]

@[simp]
private theorem edge3Bil_apply (u v : L2Sigma_R3) (s : schwartzSpan) :
    edge3Bil u v s = convBLTspan s u v := by
  show edge3Sval u v s = convBLTspan s u v
  exact edge3Sval_apply u v s

/-- The slot-2 determined value as a linear functional in the rough factor:
`l ↦ -convBLTspan s u l` (i.e. `convFormH1 u s l`). -/
private noncomputable def edge2Lval (u : L2Sigma_R3) (s : schwartzSpan) :
    L2Sigma_R3 →ₗ[ℝ] ℝ :=
  -(convBLTspan s u).toLinearMap

@[simp]
private theorem edge2Lval_apply (u : L2Sigma_R3) (s : schwartzSpan) (l : L2Sigma_R3) :
    edge2Lval u s l = -(convBLTspan s u l) := rfl

/-- The slot-2 edge bilinear `b2 u : 𝒮 →ₗ L²_σ →ₗ ℝ`, `b2 u s l = -convBLTspan s u l`. -/
private noncomputable def edge2Bil (u : L2Sigma_R3) :
    schwartzSpan →ₗ[ℝ] L2Sigma_R3 →ₗ[ℝ] ℝ where
  toFun s := edge2Lval u s
  map_add' s s' := by
    refine LinearMap.ext (fun l => ?_)
    simp only [edge2Lval_apply, LinearMap.add_apply, convBLTspan_add,
      ContinuousLinearMap.add_apply, neg_add]
  map_smul' c s := by
    refine LinearMap.ext (fun l => ?_)
    simp only [edge2Lval_apply, LinearMap.smul_apply, convBLTspan_smul,
      ContinuousLinearMap.smul_apply, smul_eq_mul, RingHom.id_apply, mul_neg]

@[simp]
private theorem edge2Bil_apply (u : L2Sigma_R3) (s : schwartzSpan) (l : L2Sigma_R3) :
    edge2Bil u s l = -(convBLTspan s u l) := by
  show edge2Lval u s l = -(convBLTspan s u l)
  exact edge2Lval_apply u s l

/-- The slot-3 edge bilinear bundled **linearly in `u`**. -/
private noncomputable def edge3BilL :
    L2Sigma_R3 →ₗ[ℝ] (L2Sigma_R3 →ₗ[ℝ] schwartzSpan →ₗ[ℝ] ℝ) where
  toFun := edge3Bil
  map_add' u u' := by
    refine LinearMap.ext (fun v => LinearMap.ext (fun s => ?_))
    simp only [edge3Bil_apply, LinearMap.add_apply, convBLTspan_u_add, ContinuousLinearMap.add_apply]
  map_smul' c u := by
    refine LinearMap.ext (fun v => LinearMap.ext (fun s => ?_))
    simp only [edge3Bil_apply, LinearMap.smul_apply, RingHom.id_apply, convBLTspan_u_smul,
      ContinuousLinearMap.smul_apply, smul_eq_mul]

/-- The slot-2 edge bilinear bundled **linearly in `u`**. -/
private noncomputable def edge2BilL :
    L2Sigma_R3 →ₗ[ℝ] (schwartzSpan →ₗ[ℝ] L2Sigma_R3 →ₗ[ℝ] ℝ) where
  toFun := edge2Bil
  map_add' u u' := by
    refine LinearMap.ext (fun s => LinearMap.ext (fun l => ?_))
    simp only [edge2Bil_apply, LinearMap.add_apply, convBLTspan_u_add,
      ContinuousLinearMap.add_apply, neg_add]
  map_smul' c u := by
    refine LinearMap.ext (fun s => LinearMap.ext (fun l => ?_))
    simp only [edge2Bil_apply, LinearMap.smul_apply, RingHom.id_apply, convBLTspan_u_smul,
      ContinuousLinearMap.smul_apply, smul_eq_mul, mul_neg]

/-- The slot-3 lift `lift3 : L²_σ →ₗ ((L²_σ ⊗ 𝒮) →ₗ ℝ)` (linear in `u`). -/
private noncomputable def edge3LiftL :
    L2Sigma_R3 →ₗ[ℝ] (TensorProduct ℝ L2Sigma_R3 schwartzSpan →ₗ[ℝ] ℝ) :=
  (TensorProduct.uncurry (RingHom.id ℝ) L2Sigma_R3 schwartzSpan ℝ).comp edge3BilL

/-- The slot-2 lift `lift2 : L²_σ →ₗ ((𝒮 ⊗ L²_σ) →ₗ ℝ)` (linear in `u`). -/
private noncomputable def edge2LiftL :
    L2Sigma_R3 →ₗ[ℝ] (TensorProduct ℝ schwartzSpan L2Sigma_R3 →ₗ[ℝ] ℝ) :=
  (TensorProduct.uncurry (RingHom.id ℝ) schwartzSpan L2Sigma_R3 ℝ).comp edge2BilL

/-- The slot-3 lift `lift3 u : (L²_σ ⊗ 𝒮) →ₗ ℝ`. -/
private noncomputable def edge3Lift (u : L2Sigma_R3) :
    TensorProduct ℝ L2Sigma_R3 schwartzSpan →ₗ[ℝ] ℝ :=
  edge3LiftL u

/-- The slot-2 lift `lift2 u : (𝒮 ⊗ L²_σ) →ₗ ℝ`. -/
private noncomputable def edge2Lift (u : L2Sigma_R3) :
    TensorProduct ℝ schwartzSpan L2Sigma_R3 →ₗ[ℝ] ℝ :=
  edge2LiftL u

@[simp]
private theorem edge3Lift_tmul (u v : L2Sigma_R3) (s : schwartzSpan) :
    edge3Lift u (v ⊗ₜ[ℝ] s) = convBLTspan s u v := by
  show edge3LiftL u (v ⊗ₜ[ℝ] s) = convBLTspan s u v
  unfold edge3LiftL
  rw [LinearMap.comp_apply, TensorProduct.uncurry_apply]
  show edge3Bil u v s = convBLTspan s u v
  exact edge3Bil_apply u v s

@[simp]
private theorem edge2Lift_tmul (u : L2Sigma_R3) (s : schwartzSpan) (l : L2Sigma_R3) :
    edge2Lift u (s ⊗ₜ[ℝ] l) = -(convBLTspan s u l) := by
  show edge2LiftL u (s ⊗ₜ[ℝ] l) = -(convBLTspan s u l)
  unfold edge2LiftL
  rw [LinearMap.comp_apply, TensorProduct.uncurry_apply]
  show edge2Bil u s l = -(convBLTspan s u l)
  exact edge2Bil_apply u s l

private theorem edge3Lift_add (u u' : L2Sigma_R3) (z : TensorProduct ℝ L2Sigma_R3 schwartzSpan) :
    edge3Lift (u + u') z = edge3Lift u z + edge3Lift u' z := by
  show edge3LiftL (u + u') z = edge3LiftL u z + edge3LiftL u' z
  rw [map_add]; rfl

private theorem edge3Lift_smul (c : ℝ) (u : L2Sigma_R3)
    (z : TensorProduct ℝ L2Sigma_R3 schwartzSpan) :
    edge3Lift (c • u) z = c • edge3Lift u z := by
  show edge3LiftL (c • u) z = c • edge3LiftL u z
  rw [map_smul]; rfl

private theorem edge2Lift_add (u u' : L2Sigma_R3) (z : TensorProduct ℝ schwartzSpan L2Sigma_R3) :
    edge2Lift (u + u') z = edge2Lift u z + edge2Lift u' z := by
  show edge2LiftL (u + u') z = edge2LiftL u z + edge2LiftL u' z
  rw [map_add]; rfl

private theorem edge2Lift_smul (c : ℝ) (u : L2Sigma_R3)
    (z : TensorProduct ℝ schwartzSpan L2Sigma_R3) :
    edge2Lift (c • u) z = c • edge2Lift u z := by
  show edge2LiftL (c • u) z = c • edge2LiftL u z
  rw [map_smul]; rfl

attribute [irreducible] edge3Lift edge2Lift

/-! #### C5-b — `projS`, the left inverse of `schwartzSpan.subtype`, and the retractions -/

/-- A complement of `schwartzSpan` and its data. -/
private noncomputable def schwartzCompl : Submodule ℝ L2Sigma_R3 :=
  (schwartzSpan.exists_isCompl).choose

private theorem schwartzCompl_isCompl : IsCompl schwartzSpan schwartzCompl :=
  (schwartzSpan.exists_isCompl).choose_spec

/-- The projection `L²_σ →ₗ 𝒮` (left inverse of `schwartzSpan.subtype`). -/
private noncomputable def projS : L2Sigma_R3 →ₗ[ℝ] schwartzSpan :=
  schwartzSpan.projectionOnto schwartzCompl schwartzCompl_isCompl

@[simp]
private theorem projS_subtype (s : schwartzSpan) : projS (s : L2Sigma_R3) = s :=
  Submodule.projectionOnto_apply_left schwartzCompl_isCompl s

/-- `projS ∘ subtype = id` on `𝒮`. -/
private theorem projS_comp_subtype :
    projS.comp schwartzSpan.subtype = LinearMap.id := by
  refine LinearMap.ext (fun s => ?_)
  simp [projS_subtype]

/-- Slot-3 retraction `retr3 : (L²_σ ⊗ L²_σ) →ₗ (L²_σ ⊗ 𝒮)`. -/
private noncomputable def retr3 :
    TensorProduct ℝ L2Sigma_R3 L2Sigma_R3 →ₗ[ℝ] TensorProduct ℝ L2Sigma_R3 schwartzSpan :=
  TensorProduct.map LinearMap.id projS

/-- Slot-2 retraction `retr2 : (L²_σ ⊗ L²_σ) →ₗ (𝒮 ⊗ L²_σ)`. -/
private noncomputable def retr2 :
    TensorProduct ℝ L2Sigma_R3 L2Sigma_R3 →ₗ[ℝ] TensorProduct ℝ schwartzSpan L2Sigma_R3 :=
  TensorProduct.map projS LinearMap.id

/-- `retr3` inverts `map id subtype` on `L²_σ ⊗ 𝒮`. -/
private theorem retr3_map_id_subtype :
    retr3.comp (TensorProduct.map LinearMap.id schwartzSpan.subtype) = LinearMap.id := by
  unfold retr3
  rw [← TensorProduct.map_comp, LinearMap.id_comp, projS_comp_subtype, TensorProduct.map_id]

/-- `retr2` inverts `map subtype id` on `𝒮 ⊗ L²_σ`. -/
private theorem retr2_map_subtype_id :
    retr2.comp (TensorProduct.map schwartzSpan.subtype LinearMap.id) = LinearMap.id := by
  unfold retr2
  rw [← TensorProduct.map_comp, LinearMap.id_comp, projS_comp_subtype, TensorProduct.map_id]

/-! #### C5-c — the overlap agreement on `𝒮 ⊗ 𝒮` -/

/-- A `schwartzSpan` element re-typed in `H1Sigma'`. -/
private noncomputable def spanToH1 (s : schwartzSpan) : H1Sigma' :=
  ⟨(s : L2Sigma_R3), schwartzSpan_le_H1Sigma' s.2⟩

@[simp]
private theorem eH1L_spanToH1 (s : schwartzSpan) :
    eH1L (spanToH1 s) = (s : L2Sigma_R3) := rfl

private theorem vfOf_spanToH1 (s : schwartzSpan) : vfOf (spanToH1 s) = (s : L2VF_R3) := rfl

/-- `convBLTspan` on H¹ first slot and a span second slot is the genuine `convFormH1`. -/
private theorem convBLTspan_eH1_span (s : schwartzSpan) (a : H1Sigma') (s' : schwartzSpan) :
    convBLTspan s (eH1L a) (s' : L2Sigma_R3)
      = convFormH1 (vfOf a) (s' : L2VF_R3) (s : L2VF_R3)
          (vfOf_mem a) (memH1VF_R3_of_mem_schwartzSpan s'.2)
          (memH1VF_R3_of_mem_schwartzSpan s.2) := by
  have h := convBLTspan_eH1 s a (spanToH1 s')
  rw [eH1L_spanToH1] at h
  -- `vfOf (spanToH1 s') = (s' : L2VF_R3)` definitionally, so `h` closes the goal.
  exact h

/-- **Overlap agreement.** For `s, s' ∈ 𝒮` and any `u`,
`convBLTspan s' u (s : L²) = -convBLTspan s u (s' : L²)` (B6 antisymmetry, extended in `u`
by density). -/
private theorem convBLTspan_overlap (u : L2Sigma_R3) (s s' : schwartzSpan) :
    convBLTspan s' u (s : L2Sigma_R3) = -convBLTspan s u (s' : L2Sigma_R3) := by
  -- Both sides are continuous in `u`; agree on dense H¹.
  have hcont1 : Continuous fun a : L2Sigma_R3 => convBLTspan s' a (s : L2Sigma_R3) :=
    ((ContinuousLinearMap.apply ℝ ℝ (s : L2Sigma_R3)).continuous).comp
      (convBLTspan s').continuous
  have hcont2 : Continuous fun a : L2Sigma_R3 => -convBLTspan s a (s' : L2Sigma_R3) :=
    (((ContinuousLinearMap.apply ℝ ℝ (s' : L2Sigma_R3)).continuous).comp
      (convBLTspan s).continuous).neg
  have hagree : ∀ a : L2Sigma_R3, a ∈ Set.range (eH1L : H1Sigma' → L2Sigma_R3) →
      convBLTspan s' a (s : L2Sigma_R3) = -convBLTspan s a (s' : L2Sigma_R3) := by
    rintro _ ⟨a, rfl⟩
    rw [convBLTspan_eH1_span s' a s, convBLTspan_eH1_span s a s']
    -- B6: convFormH1 (vfOf a) s s' = -convFormH1 (vfOf a) s' s.
    rw [convFormH1_antisymm (vfOf a) (s : L2VF_R3) (s' : L2VF_R3)
      (vfOf_mem a) (memH1VF_R3_of_mem_schwartzSpan s.2)
      (memH1VF_R3_of_mem_schwartzSpan s'.2)
      (a : L2Sigma_R3).2 (s : L2Sigma_R3).2 (s' : L2Sigma_R3).2]
  exact congrFun (Continuous.ext_on denseRange_eH1L hcont1 hcont2 hagree) u

/-! #### C5-d — the edge functionals on the submodules and the glued map `Ψ u` -/

/-- The slot-3 edge functional on `edgeSlot3`: `Ψ3 u (T₃ y) = edge3Lift u y`. -/
private noncomputable def psi3 (u : L2Sigma_R3) : edgeSlot3 →ₗ[ℝ] ℝ :=
  (edge3Lift u).comp (retr3.comp edgeSlot3.subtype)

/-- The slot-2 edge functional on `edgeSlot2`: `Ψ2 u (T₂ y) = edge2Lift u y`. -/
private noncomputable def psi2 (u : L2Sigma_R3) : edgeSlot2 →ₗ[ℝ] ℝ :=
  (edge2Lift u).comp (retr2.comp edgeSlot2.subtype)

private theorem psi3_apply (u : L2Sigma_R3) (x : edgeSlot3) :
    psi3 u x = edge3Lift u (retr3 (x : TensorProduct ℝ L2Sigma_R3 L2Sigma_R3)) := rfl

private theorem psi2_apply (u : L2Sigma_R3) (x : edgeSlot2) :
    psi2 u x = edge2Lift u (retr2 (x : TensorProduct ℝ L2Sigma_R3 L2Sigma_R3)) := rfl

/-- `psi3` is additive in `u`. -/
private theorem psi3_add (u u' : L2Sigma_R3) (x : edgeSlot3) :
    psi3 (u + u') x = psi3 u x + psi3 u' x := by
  rw [psi3_apply, psi3_apply, psi3_apply]
  exact edge3Lift_add u u' (retr3 (x : TensorProduct ℝ L2Sigma_R3 L2Sigma_R3))

/-- `psi3` is homogeneous in `u`. -/
private theorem psi3_smul (c : ℝ) (u : L2Sigma_R3) (x : edgeSlot3) :
    psi3 (c • u) x = c • psi3 u x := by
  rw [psi3_apply, psi3_apply]
  exact edge3Lift_smul c u (retr3 (x : TensorProduct ℝ L2Sigma_R3 L2Sigma_R3))

/-- `psi2` is additive in `u`. -/
private theorem psi2_add (u u' : L2Sigma_R3) (x : edgeSlot2) :
    psi2 (u + u') x = psi2 u x + psi2 u' x := by
  rw [psi2_apply, psi2_apply, psi2_apply]
  exact edge2Lift_add u u' (retr2 (x : TensorProduct ℝ L2Sigma_R3 L2Sigma_R3))

/-- `psi2` is homogeneous in `u`. -/
private theorem psi2_smul (c : ℝ) (u : L2Sigma_R3) (x : edgeSlot2) :
    psi2 (c • u) x = c • psi2 u x := by
  rw [psi2_apply, psi2_apply]
  exact edge2Lift_smul c u (retr2 (x : TensorProduct ℝ L2Sigma_R3 L2Sigma_R3))

/-- The two edge functionals as `LinearPMap`s on `L²_σ ⊗ L²_σ`. -/
private noncomputable def pmap3 (u : L2Sigma_R3) :
    (TensorProduct ℝ L2Sigma_R3 L2Sigma_R3) →ₗ.[ℝ] ℝ :=
  ⟨edgeSlot3, psi3 u⟩

private noncomputable def pmap2 (u : L2Sigma_R3) :
    (TensorProduct ℝ L2Sigma_R3 L2Sigma_R3) →ₗ.[ℝ] ℝ :=
  ⟨edgeSlot2, psi2 u⟩

/-- The two edge prescriptions, composed with the retractions and `mapIncl`, are **equal
as linear maps** on `𝒮 ⊗ 𝒮` (`TensorProduct.ext'`, tmul case = overlap agreement). -/
private theorem edge_lift_agree_map (u : L2Sigma_R3) :
    (edge2Lift u).comp (retr2.comp (TensorProduct.mapIncl schwartzSpan schwartzSpan))
      = (edge3Lift u).comp (retr3.comp (TensorProduct.mapIncl schwartzSpan schwartzSpan)) := by
  refine TensorProduct.ext' (fun a b => ?_)
  simp only [LinearMap.comp_apply]
  rw [TensorProduct.mapIncl, TensorProduct.map_tmul]
  show edge2Lift u (retr2 ((a : L2Sigma_R3) ⊗ₜ[ℝ] (b : L2Sigma_R3)))
    = edge3Lift u (retr3 ((a : L2Sigma_R3) ⊗ₜ[ℝ] (b : L2Sigma_R3)))
  unfold retr2 retr3
  rw [TensorProduct.map_tmul, TensorProduct.map_tmul, LinearMap.id_apply,
    LinearMap.id_apply, projS_subtype, projS_subtype, edge2Lift_tmul, edge3Lift_tmul,
    convBLTspan_overlap u a b]

/-- The two edge prescriptions agree on the image of `𝒮 ⊗ 𝒮` under `mapIncl`. -/
private theorem edge_lift_agree (u : L2Sigma_R3)
    (z : TensorProduct ℝ schwartzSpan schwartzSpan) :
    edge2Lift u (retr2 (TensorProduct.mapIncl schwartzSpan schwartzSpan z))
      = edge3Lift u (retr3 (TensorProduct.mapIncl schwartzSpan schwartzSpan z)) := by
  have := LinearMap.congr_fun (edge_lift_agree_map u) z
  simpa only [LinearMap.comp_apply] using this

/-- **The sup-glue agreement.** `Ψ2 u` and `Ψ3 u` agree where their underlying tensors
coincide (necessarily in `𝒮 ⊗ 𝒮`). -/
private theorem psi_agree (u : L2Sigma_R3)
    (x : (pmap2 u).domain) (y : (pmap3 u).domain)
    (hxy : (x : TensorProduct ℝ L2Sigma_R3 L2Sigma_R3) = y) :
    (pmap2 u) x = (pmap3 u) y := by
  have hx2 : (x : TensorProduct ℝ L2Sigma_R3 L2Sigma_R3) ∈ edgeSlot2 := x.2
  have hy3 : (x : TensorProduct ℝ L2Sigma_R3 L2Sigma_R3) ∈ edgeSlot3 := hxy ▸ y.2
  have hmem : (x : TensorProduct ℝ L2Sigma_R3 L2Sigma_R3) ∈ edgeSlot2 ⊓ edgeSlot3 := ⟨hx2, hy3⟩
  rw [edge_inf_eq_schwartz_tensor] at hmem
  obtain ⟨z, hz⟩ := hmem
  show psi2 u x = psi3 u y
  rw [psi2_apply, psi3_apply]
  rw [show (y : TensorProduct ℝ L2Sigma_R3 L2Sigma_R3)
        = (x : TensorProduct ℝ L2Sigma_R3 L2Sigma_R3) from hxy.symm, ← hz]
  exact edge_lift_agree u z

/-- The glued determined functional on `D = detDomain` (via `LinearPMap.sup`). -/
private noncomputable def psiSup (u : L2Sigma_R3) :
    (TensorProduct ℝ L2Sigma_R3 L2Sigma_R3) →ₗ.[ℝ] ℝ :=
  (pmap2 u).sup (pmap3 u) (psi_agree u)

private theorem psiSup_domain (u : L2Sigma_R3) : (psiSup u).domain = detDomain := by
  unfold psiSup pmap2 pmap3 detDomain
  rw [LinearPMap.domain_sup]

/-! #### C5-e — `gInv`, a fixed left inverse of `detDomain.subtype` -/

/-- The left-inverse existence statement, with the `ℝ`-semiring instance pinned to
`Real.semiring` (avoids the `DivisionRing.toSemiring` mismatch from `Classical.choose`). -/
private theorem detDomain_exists_leftInverse :
    ∃ g : (TensorProduct ℝ L2Sigma_R3 L2Sigma_R3) →ₗ[ℝ] detDomain,
      g.comp detDomain.subtype = LinearMap.id := by
  letI : Semiring ℝ := inferInstance
  have h := LinearMap.exists_leftInverse_of_injective
    (K := ℝ) (V := detDomain) (V' := TensorProduct ℝ L2Sigma_R3 L2Sigma_R3)
    detDomain.subtype (Submodule.ker_subtype detDomain)
  exact h

private noncomputable def gInv :
    (TensorProduct ℝ L2Sigma_R3 L2Sigma_R3) →ₗ[ℝ] detDomain :=
  detDomain_exists_leftInverse.choose

private theorem gInv_subtype :
    gInv.comp detDomain.subtype = LinearMap.id :=
  detDomain_exists_leftInverse.choose_spec

private theorem gInv_eq_of_mem (x : TensorProduct ℝ L2Sigma_R3 L2Sigma_R3)
    (hx : x ∈ detDomain) : gInv x = (⟨x, hx⟩ : detDomain) :=
  LinearMap.congr_fun gInv_subtype ⟨x, hx⟩

private theorem gInv_apply_mem (x : TensorProduct ℝ L2Sigma_R3 L2Sigma_R3)
    (hx : x ∈ detDomain) : (gInv x : TensorProduct ℝ L2Sigma_R3 L2Sigma_R3) = x := by
  rw [gInv_eq_of_mem x hx]

/-! #### C5-f — `detExtend` and its `u`-linearity -/

/-- The glued functional re-typed on `detDomain` (value-preserving). -/
private noncomputable def psiD (u : L2Sigma_R3) : detDomain →ₗ[ℝ] ℝ :=
  (psiSup u).toFun.comp
    (LinearEquiv.ofEq _ _ (psiSup_domain u).symm).toLinearMap

/-- The membership `x ∈ (psiSup u).domain` coming from `x ∈ detDomain`. -/
private theorem mem_psiSup_domain (u : L2Sigma_R3)
    {x : TensorProduct ℝ L2Sigma_R3 L2Sigma_R3} (hxD : x ∈ detDomain) :
    x ∈ (psiSup u).domain := by
  rw [psiSup_domain]; exact hxD

/-- `psiD u ⟨x, hxD⟩` is the value of the glued partial map at `x`. -/
private theorem psiD_eq_psiSup (u : L2Sigma_R3)
    (x : TensorProduct ℝ L2Sigma_R3 L2Sigma_R3) (hxD : x ∈ detDomain) :
    psiD u ⟨x, hxD⟩ = (psiSup u) ⟨x, mem_psiSup_domain u hxD⟩ := by
  unfold psiD
  rfl

private theorem psiD_apply_mem (u : L2Sigma_R3)
    (x : TensorProduct ℝ L2Sigma_R3 L2Sigma_R3) (hx2 : x ∈ edgeSlot2) (hxD : x ∈ detDomain) :
    psiD u ⟨x, hxD⟩ = psi2 u ⟨x, hx2⟩ := by
  rw [psiD_eq_psiSup u x hxD]
  obtain ⟨hdom, hval⟩ := LinearPMap.left_le_sup (pmap2 u) (pmap3 u) (psi_agree u)
  have h2 := hval (x := ⟨x, hx2⟩) (y := ⟨x, mem_psiSup_domain u hxD⟩) rfl
  exact h2.symm

private theorem psiD_apply_mem3 (u : L2Sigma_R3)
    (x : TensorProduct ℝ L2Sigma_R3 L2Sigma_R3) (hx3 : x ∈ edgeSlot3) (hxD : x ∈ detDomain) :
    psiD u ⟨x, hxD⟩ = psi3 u ⟨x, hx3⟩ := by
  rw [psiD_eq_psiSup u x hxD]
  obtain ⟨hdom, hval⟩ := LinearPMap.right_le_sup (pmap2 u) (pmap3 u) (psi_agree u)
  have h3 := hval (x := ⟨x, hx3⟩) (y := ⟨x, mem_psiSup_domain u hxD⟩) rfl
  exact h3.symm

/-- The antisymmetrizer `A := (id − swap)/2` on `L²_σ ⊗ L²_σ`. -/
noncomputable def antisymmetrizer :
    TensorProduct ℝ L2Sigma_R3 L2Sigma_R3 →ₗ[ℝ] TensorProduct ℝ L2Sigma_R3 L2Sigma_R3 :=
  (2⁻¹ : ℝ) • (LinearMap.id - (TensorProduct.comm ℝ L2Sigma_R3 L2Sigma_R3).toLinearMap)

private theorem antisymmetrizer_tmul (v w : L2Sigma_R3) :
    antisymmetrizer (v ⊗ₜ[ℝ] w) = (2⁻¹ : ℝ) • (v ⊗ₜ[ℝ] w - w ⊗ₜ[ℝ] v) := by
  unfold antisymmetrizer
  simp [TensorProduct.comm_tmul]

/-- The antisymmetrizer is antisymmetric on simple tensors: `A (w ⊗ v) = − A (v ⊗ w)`. -/
private theorem antisymmetrizer_tmul_swap (v w : L2Sigma_R3) :
    antisymmetrizer (w ⊗ₜ[ℝ] v) = -antisymmetrizer (v ⊗ₜ[ℝ] w) := by
  rw [antisymmetrizer_tmul, antisymmetrizer_tmul,
    ← neg_sub ((v : L2Sigma_R3) ⊗ₜ[ℝ] w) (w ⊗ₜ[ℝ] v), smul_neg]

/-- `psiD` is additive in `u`. -/
private theorem psiD_add (u u' : L2Sigma_R3) :
    psiD (u + u') = psiD u + psiD u' := by
  refine LinearMap.ext (fun z => ?_)
  -- decompose z ∈ detDomain = edge2 ⊔ edge3 via span/sup; use additivity of psi2/psi3 in u.
  obtain ⟨x, hx2, y, hy3, hxy⟩ := Submodule.mem_sup.mp (by rw [← detDomain]; exact z.2)
  have hzval : (z : TensorProduct ℝ L2Sigma_R3 L2Sigma_R3) = x + y := hxy.symm
  -- evaluate each psiD at the decomposition using linearity of psiD and edge values.
  have hxD : x ∈ detDomain := Submodule.mem_sup_left hx2
  have hyD : y ∈ detDomain := Submodule.mem_sup_right hy3
  have hsplit : z = (⟨x, hxD⟩ : detDomain) + (⟨y, hyD⟩ : detDomain) := by
    apply Subtype.ext; simpa using hzval
  rw [hsplit]
  simp only [map_add, LinearMap.add_apply,
    psiD_apply_mem u x hx2 hxD, psiD_apply_mem u' x hx2 hxD, psiD_apply_mem (u + u') x hx2 hxD,
    psiD_apply_mem3 u y hy3 hyD, psiD_apply_mem3 u' y hy3 hyD, psiD_apply_mem3 (u + u') y hy3 hyD,
    psi2_add u u' ⟨x, hx2⟩, psi3_add u u' ⟨y, hy3⟩]

/-- `psiD` is homogeneous in `u`. -/
private theorem psiD_smul (c : ℝ) (u : L2Sigma_R3) :
    psiD (c • u) = c • psiD u := by
  refine LinearMap.ext (fun z => ?_)
  obtain ⟨x, hx2, y, hy3, hxy⟩ := Submodule.mem_sup.mp (by rw [← detDomain]; exact z.2)
  have hxD : x ∈ detDomain := Submodule.mem_sup_left hx2
  have hyD : y ∈ detDomain := Submodule.mem_sup_right hy3
  have hsplit : z = (⟨x, hxD⟩ : detDomain) + (⟨y, hyD⟩ : detDomain) := by
    apply Subtype.ext; simpa using hxy.symm
  rw [hsplit]
  simp only [map_add, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    psiD_apply_mem u x hx2 hxD, psiD_apply_mem (c • u) x hx2 hxD,
    psiD_apply_mem3 u y hy3 hyD, psiD_apply_mem3 (c • u) y hy3 hyD,
    psi2_smul c u ⟨x, hx2⟩, psi3_smul c u ⟨y, hy3⟩, mul_add]

/-- **C5 `detExtend` (`Bext`).** The determined form `b u v w := detExtend u (v ⊗ₜ w)`.
Built as `(psiD u) ∘ₗ gInv ∘ₗ A` where `A` is the antisymmetrizer
`(id − swap) / 2`; this makes `detExtend u` antisymmetric for **all** `(v, w)`, while on
the determined edge `D` it reads the glued value `psiD u` (`gInv` fixes `D`). -/
noncomputable def detExtend :
    L2Sigma_R3 →ₗ[ℝ] (TensorProduct ℝ L2Sigma_R3 L2Sigma_R3) →ₗ[ℝ] ℝ where
  toFun u := ((psiD u).comp gInv).comp antisymmetrizer
  map_add' u u' := by
    refine LinearMap.ext (fun z => ?_)
    simp only [LinearMap.comp_apply, LinearMap.add_apply]
    rw [psiD_add u u', LinearMap.add_apply]
  map_smul' c u := by
    refine LinearMap.ext (fun z => ?_)
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, RingHom.id_apply]
    rw [psiD_smul c u, LinearMap.smul_apply]

/-- `detExtend` is additive in `u` (isolated, applied at a tensor `z`). -/
private theorem detExtend_add (u u' : L2Sigma_R3)
    (z : TensorProduct ℝ L2Sigma_R3 L2Sigma_R3) :
    detExtend (u + u') z = detExtend u z + detExtend u' z := by
  rw [detExtend.map_add u u', LinearMap.add_apply]

/-- `detExtend` is homogeneous in `u` (isolated, applied at a tensor `z`). -/
private theorem detExtend_smul (c : ℝ) (u : L2Sigma_R3)
    (z : TensorProduct ℝ L2Sigma_R3 L2Sigma_R3) :
    detExtend (c • u) z = c • detExtend u z := by
  rw [detExtend.map_smul c u, LinearMap.smul_apply]

/-- For `s ∈ 𝒮`, `v ⊗ₜ (s:L²) ∈ edgeSlot3`. -/
private theorem tmul_mem_edgeSlot3 (v : L2Sigma_R3) (s : schwartzSpan) :
    (v : L2Sigma_R3) ⊗ₜ[ℝ] (s : L2Sigma_R3) ∈ edgeSlot3 :=
  ⟨v ⊗ₜ[ℝ] s, by rw [TensorProduct.map_tmul, LinearMap.id_apply, Submodule.coe_subtype]⟩

/-- For `s ∈ 𝒮`, `(s:L²) ⊗ₜ v ∈ edgeSlot2`. -/
private theorem tmul_mem_edgeSlot2 (s : schwartzSpan) (v : L2Sigma_R3) :
    (s : L2Sigma_R3) ⊗ₜ[ℝ] (v : L2Sigma_R3) ∈ edgeSlot2 :=
  ⟨s ⊗ₜ[ℝ] v, by rw [TensorProduct.map_tmul, LinearMap.id_apply, Submodule.coe_subtype]⟩

/-- `retr3 (v ⊗ (s:L²)) = v ⊗ s` for `s ∈ 𝒮`. -/
private theorem retr3_tmul_span (v : L2Sigma_R3) (s : schwartzSpan) :
    retr3 ((v : L2Sigma_R3) ⊗ₜ[ℝ] (s : L2Sigma_R3)) = v ⊗ₜ[ℝ] s := by
  unfold retr3
  rw [TensorProduct.map_tmul, LinearMap.id_apply, projS_subtype]

/-- `retr2 ((s:L²) ⊗ v) = s ⊗ v` for `s ∈ 𝒮`. -/
private theorem retr2_tmul_span (s : schwartzSpan) (v : L2Sigma_R3) :
    retr2 ((s : L2Sigma_R3) ⊗ₜ[ℝ] (v : L2Sigma_R3)) = s ⊗ₜ[ℝ] v := by
  unfold retr2
  rw [TensorProduct.map_tmul, LinearMap.id_apply, projS_subtype]

/-- The determined value of `psiD u` on the slot-3 edge `v ⊗ (s:L²)`. -/
private theorem psiD_edge3_value (u v : L2Sigma_R3) (s : schwartzSpan) :
    psiD u ⟨(v : L2Sigma_R3) ⊗ₜ[ℝ] (s : L2Sigma_R3),
        Submodule.mem_sup_right (tmul_mem_edgeSlot3 v s)⟩
      = convBLTspan s u v := by
  rw [psiD_apply_mem3 u _ (tmul_mem_edgeSlot3 v s) (Submodule.mem_sup_right (tmul_mem_edgeSlot3 v s)),
    psi3_apply]
  show edge3Lift u (retr3 ((v : L2Sigma_R3) ⊗ₜ[ℝ] (s : L2Sigma_R3))) = convBLTspan s u v
  rw [retr3_tmul_span v s, edge3Lift_tmul]

/-- The determined value of `psiD u` on the slot-2 edge `(s:L²) ⊗ v`. -/
private theorem psiD_edge2_value (u v : L2Sigma_R3) (s : schwartzSpan) :
    psiD u ⟨(s : L2Sigma_R3) ⊗ₜ[ℝ] (v : L2Sigma_R3),
        Submodule.mem_sup_left (tmul_mem_edgeSlot2 s v)⟩
      = -(convBLTspan s u v) := by
  rw [psiD_apply_mem u _ (tmul_mem_edgeSlot2 s v) (Submodule.mem_sup_left (tmul_mem_edgeSlot2 s v)),
    psi2_apply]
  show edge2Lift u (retr2 ((s : L2Sigma_R3) ⊗ₜ[ℝ] (v : L2Sigma_R3))) = -(convBLTspan s u v)
  rw [retr2_tmul_span s v, edge2Lift_tmul]

/-- **C5b `detExtend_on_edgeSlot3` [PR-4 — the determined identity].**
On the slot-3-Schwartz edge `L²_σ ⊗ 𝒮`, `detExtend u` is the genuine determined value:
for ALL `u, v` and any Schwartz `w`,
`detExtend u (v ⊗ₜ w) = convBLT_fixedTest w … u v`,
i.e. the value is the evaluation of the jointly continuous B7-bounded extension `Bw`
(C3), NOT a Hamel value.

This is the load-bearing identity for `b_cont_fixedTest`.  Both `v ⊗ₜ w ∈ edgeSlot3` and
`w ⊗ₜ v ∈ edgeSlot2` are in the determined domain `D`; `gInv` fixes `D` and the
antisymmetrizer combines the two determined edge values into the genuine
`convBLT_fixedTest w u v`. -/
theorem detExtend_on_edgeSlot3
    (u v : L2Sigma_R3) (w : L2VF_R3) (hw_H1 : memH1VF_R3 w)
    (hw_sigma : w ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3))
    (hw_sch : IsSchwartzDivFree_R3 ⟨w, hw_sigma⟩) :
    detExtend u ((v : L2Sigma_R3) ⊗ₜ[ℝ] (⟨w, hw_sigma⟩ : L2Sigma_R3))
      = convBLT_fixedTest w hw_H1 hw_sigma hw_sch u v := by
  -- `sw : schwartzSpan` is the Schwartz test as a span element.
  set sw : schwartzSpan := ⟨⟨w, hw_sigma⟩, subset_schwartzSpan hw_sch⟩ with hsw
  have hmem3 : (v : L2Sigma_R3) ⊗ₜ[ℝ] (⟨w, hw_sigma⟩ : L2Sigma_R3) ∈ detDomain :=
    Submodule.mem_sup_right (tmul_mem_edgeSlot3 v sw)
  have hmem2 : (⟨w, hw_sigma⟩ : L2Sigma_R3) ⊗ₜ[ℝ] (v : L2Sigma_R3) ∈ detDomain :=
    Submodule.mem_sup_left (tmul_mem_edgeSlot2 sw v)
  -- Expand detExtend via the antisymmetrizer and gInv on the two determined edges.
  show ((psiD u).comp gInv).comp antisymmetrizer
      ((v : L2Sigma_R3) ⊗ₜ[ℝ] (⟨w, hw_sigma⟩ : L2Sigma_R3))
    = convBLT_fixedTest w hw_H1 hw_sigma hw_sch u v
  rw [LinearMap.comp_apply, LinearMap.comp_apply, antisymmetrizer_tmul]
  -- Distribute `gInv` then `psiD u` over the antisymmetrized combination.
  rw [map_smul, map_sub, gInv_eq_of_mem _ hmem3, gInv_eq_of_mem _ hmem2,
    map_smul, map_sub, psiD_edge3_value u v sw, psiD_edge2_value u v sw]
  -- `2⁻¹ • (convBLTspan sw u v - (-convBLTspan sw u v)) = convBLTspan sw u v`.
  rw [sub_neg_eq_add, ← two_mul, smul_eq_mul, ← mul_assoc]
  norm_num
  -- Finally identify `convBLTspan sw` with `convBLT_fixedTest w`.
  rw [hsw, convBLTspan_eq_fixedTest w hw_H1 hw_sigma hw_sch (subset_schwartzSpan hw_sch)]

/-! ### C6 — `convFormL2_def` : the determined trilinear `b` -/

/-- **C6 `convFormL2_def` (`b`) [proved sorry-free given `detExtend`].** The determined
trilinear convection form:

`b u v w := detExtend u (v ⊗ₜ w)`.

- Linear in `w` (slot 3): `detExtend u` is a `LinearMap` and `(v ⊗ₜ ·)` is linear.
- Linear in `v` (slot 2): `(· ⊗ₜ w)` is linear.
- Linear in `u` (slot 1): `detExtend` is a `LinearMap` in `u`.
- Antisymmetric in `(v, w)`: `β_u` is antisymmetric on `D` (B6), preserved by the
  Hamel extension (C7).
- Extends `convFormSchwartz` on Schwartz triples (C8). -/
noncomputable def convFormL2_def (u v w : L2Sigma_R3) : ℝ :=
  detExtend u (v ⊗ₜ[ℝ] w)

@[simp]
theorem convFormL2_def_eq (u v w : L2Sigma_R3) :
    convFormL2_def u v w = detExtend u (v ⊗ₜ[ℝ] w) :=
  rfl

/-! ### C7 — `convFormL2_multilinear` -/

/-- **C7 `convFormL2_multilinear` [PR-4].** `∃ B trilinear, ∀ u v w, b u v w = B u v w`.

**Proof route:** the trilinear `B` is `detExtend` precomposed with `TensorProduct.mk`:
`B u := (detExtend u).compl₂ (TensorProduct.mk ℝ L2Sigma_R3 L2Sigma_R3)` — curry the
`v ⊗ₜ w` argument.  `b u v w = detExtend u (v ⊗ₜ w) = B u v w` by `rfl`. -/
theorem convFormL2_multilinear :
    ∃ B : L2Sigma_R3 →ₗ[ℝ] L2Sigma_R3 →ₗ[ℝ] L2Sigma_R3 →ₗ[ℝ] ℝ,
      ∀ (u v w : L2Sigma_R3), convFormL2_def u v w = B u v w := by
  refine ⟨{
    toFun := fun u =>
      LinearMap.compr₂ (TensorProduct.mk ℝ L2Sigma_R3 L2Sigma_R3) (detExtend u)
    map_add' := fun u u' => by
      refine LinearMap.ext (fun v => LinearMap.ext (fun w => ?_))
      simp only [LinearMap.add_apply, LinearMap.compr₂_apply, TensorProduct.mk_apply]
      exact detExtend_add u u' (v ⊗ₜ[ℝ] w)
    map_smul' := fun c u => by
      refine LinearMap.ext (fun v => LinearMap.ext (fun w => ?_))
      simp only [RingHom.id_apply, LinearMap.smul_apply, LinearMap.compr₂_apply,
        TensorProduct.mk_apply]
      exact detExtend_smul c u (v ⊗ₜ[ℝ] w) }, ?_⟩
  intro u v w
  rw [convFormL2_def_eq]
  rfl

/-! ### C8 — `convFormL2_antisymm` -/

/-- **C8 `convFormL2_antisymm` [PR-4].** `b u v w = − b u w v` for all `u v w`.

`β_u` is antisymmetric on `D` (`convFormH1 u v w = − convFormH1 u w v`, B6, on the dense
Schwartz edges; extended antisymmetrically by the Hamel extension).  The antisymmetry is
a property of the *determined* `β_u` on `D` and is carried to all `v, w` because both
`v ⊗ₜ w` and `w ⊗ₜ v` land in `D` whenever one of `v, w` is Schwartz — and the algebraic
antisymmetry of the Hamel extension is fixed by the antisymmetric construction of `β_u`. -/
theorem convFormL2_antisymm (u v w : L2Sigma_R3) :
    convFormL2_def u v w = -convFormL2_def u w v := by
  rw [convFormL2_def_eq, convFormL2_def_eq]
  -- `detExtend u = (psiD u ∘ gInv) ∘ antisymmetrizer`; `A (w⊗v) = -A (v⊗w)`.
  show ((psiD u).comp gInv).comp antisymmetrizer (v ⊗ₜ[ℝ] w)
    = -(((psiD u).comp gInv).comp antisymmetrizer (w ⊗ₜ[ℝ] v))
  rw [LinearMap.comp_apply, LinearMap.comp_apply (g := antisymmetrizer),
    antisymmetrizer_tmul_swap v w, map_neg, neg_neg]

/-! ### C9 — `convFormL2_extends` -/

/-- **C9 `convFormL2_extends` [PR-4].** On Schwartz triples, `b u v w = convFormSchwartz`.

**Proof:** all three of `u, v, w` are Schwartz ⇒ `v ⊗ₜ w ∈ 𝒮 ⊗ 𝒮 ⊆ D`, so `detExtend`
reads the determined value `convFormH1 u v w` (C5b on the H¹ slice / overlap agreement);
B5 (`convFormH1_eq_convFormSchwartz`) identifies it with `convFormSchwartz u v w`. -/
theorem convFormL2_extends
    (u v w : L2Sigma_R3)
    (hu : IsSchwartzDivFree_R3 u) (hv : IsSchwartzDivFree_R3 v)
    (hw : IsSchwartzDivFree_R3 w) :
    convFormL2_def u v w = convFormSchwartz u v w hu hv hw := by
  have hw_sigma : (w : L2VF_R3) ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3) := w.2
  have hw_H1 : memH1VF_R3 (w : L2VF_R3) := memH1VF_R3_of_schwartz hw
  have hwsch : IsSchwartzDivFree_R3 (⟨(w : L2VF_R3), hw_sigma⟩ : L2Sigma_R3) := by
    rwa [Subtype.coe_eta]
  -- `b u v w = detExtend u (v ⊗ₜ w) = convBLT_fixedTest w u v` (slot-3 edge), with
  -- `⟨(w:L2VF), hw_sigma⟩ = w` definitionally.
  have key := detExtend_on_edgeSlot3 u v (w : L2VF_R3) hw_H1 hw_sigma hwsch
  rw [Subtype.coe_eta] at key
  rw [convFormL2_def_eq, key]
  -- Evaluate the BLT at the H¹ (Schwartz) points `u, v`.
  have hu_mem : (u : L2Sigma_R3) ∈ H1Sigma' :=
    (mem_H1Sigma'_iff u).mpr ⟨memH1VF_R3_of_schwartz hu, u.2⟩
  have hv_mem : (v : L2Sigma_R3) ∈ H1Sigma' :=
    (mem_H1Sigma'_iff v).mpr ⟨memH1VF_R3_of_schwartz hv, v.2⟩
  have hbridge := convBLT_fixedTest_eH1 (w : L2VF_R3) hw_H1 hw_sigma hwsch
    ⟨u, hu_mem⟩ ⟨v, hv_mem⟩
  -- `eH1L ⟨u,_⟩ = u`, `eH1L ⟨v,_⟩ = v`.
  rw [show (eH1L ⟨u, hu_mem⟩ : L2Sigma_R3) = u from rfl,
    show (eH1L ⟨v, hv_mem⟩ : L2Sigma_R3) = v from rfl] at hbridge
  rw [hbridge]
  -- `valH1 = convFormH1 u v w`; B5 identifies with `convFormSchwartz`.
  show convFormH1 (u : L2VF_R3) (v : L2VF_R3) (w : L2VF_R3)
      (memH1VF_R3_of_schwartz hu) (memH1VF_R3_of_schwartz hv) hw_H1
    = convFormSchwartz u v w hu hv hw
  exact convFormH1_eq_convFormSchwartz u v w hu hv hw
    (memH1VF_R3_of_schwartz hu) (memH1VF_R3_of_schwartz hv) hw_H1

/-! ### C10 — `convFormL2_cont_fixedTest` (the CRUX 5th field) -/

/-- **C10 `convFormL2_cont_fixedTest` [CRUX 5th field — PR-4].** For Schwartz `w`,
`(u, v) ↦ b u v w` is jointly L²-continuous.

**Proof route (the determined payoff).** Fix Schwartz `w`.  For ALL `v`,
`v ⊗ₜ w ∈ edgeSlot3 = L²_σ ⊗ 𝒮 ⊆ D`, so by `detExtend_on_edgeSlot3` the value is the
*determined* `convFormH1 u v w` — NOT a Hamel value.  By C3 (`convBLT_fixedTest`), that
equals the evaluation of the jointly continuous bilinear `Bw` (the B7-bounded `L²`
extension), so `(u, v) ↦ b u v w = Bw u v` is continuous (`ContinuousLinearMap.continuous₂`).
This is exactly where the refuted raw-Hamel object failed: here the swapped slot never
puts a varied argument into a discontinuous Hamel index. -/
theorem convFormL2_cont_fixedTest
    (w : L2Sigma_R3) (hw : IsSchwartzDivFree_R3 w) :
    Continuous (fun p : L2Sigma_R3 × L2Sigma_R3 => convFormL2_def p.1 p.2 w) := by
  have hw_sigma : (w : L2VF_R3) ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3) := w.2
  have hw_H1 : memH1VF_R3 (w : L2VF_R3) := memH1VF_R3_of_schwartz hw
  have hwsch : IsSchwartzDivFree_R3 (⟨(w : L2VF_R3), hw_sigma⟩ : L2Sigma_R3) := by
    rwa [Subtype.coe_eta]
  -- On the determined slot-3 edge, `b u v w = convBLT_fixedTest w u v` for ALL `u, v`.
  have heq : (fun p : L2Sigma_R3 × L2Sigma_R3 => convFormL2_def p.1 p.2 w)
      = fun p => convBLT_fixedTest (w : L2VF_R3) hw_H1 hw_sigma hwsch p.1 p.2 := by
    funext p
    have key := detExtend_on_edgeSlot3 p.1 p.2 (w : L2VF_R3) hw_H1 hw_sigma hwsch
    rw [Subtype.coe_eta] at key
    rw [convFormL2_def_eq, key]
  rw [heq]
  -- The jointly continuous bilinear `convBLT_fixedTest w` evaluated at `(p.1, p.2)`.
  exact (convBLT_fixedTest (w : L2VF_R3) hw_H1 hw_sigma hwsch).isBoundedBilinearMap.continuous

/-! ### C11 — `r3ConvectionGapOp_holds` (assembled theorem; PR-5 re-exports as the axiom name) -/

/-- **C11 `r3ConvectionGapOp_holds` [assembled].**
`∀ 𝔊 : R3GalerkinScheme, Nonempty (ConvectionGapOp 𝔊)`.

THEOREM version of `axiom r3ConvectionGapOp_exists`.  PR-5 deletes the axiom and
re-exports this under the same name (Hard Rule #2).  Assembled from the five determined-form
fields:
- `b               := convFormL2_def` (C6)
- `b_extends       := convFormL2_extends` (C9)
- `b_multilinear   := convFormL2_multilinear` (C7)
- `b_antisymm_gap  := convFormL2_antisymm` (C8)
- `b_cont_fixedTest := convFormL2_cont_fixedTest` (C10). -/
theorem r3ConvectionGapOp_holds (𝔊 : R3GalerkinScheme) : Nonempty (ConvectionGapOp 𝔊) :=
  ⟨{ b              := convFormL2_def
     b_extends      := fun u v w hu hv hw => convFormL2_extends u v w hu hv hw
     b_multilinear  := convFormL2_multilinear
     b_antisymm_gap := convFormL2_antisymm
     b_cont_fixedTest := fun w hw => convFormL2_cont_fixedTest w hw }⟩

end LerayHopf.R3.ConvectionExtension
