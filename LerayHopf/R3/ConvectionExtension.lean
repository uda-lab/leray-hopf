import LerayHopf.R3.EnergyClassConvection
import LerayHopf.R3.ConvectionForm
import LerayHopf.R3.H1SigmaDensity  -- h1Sigma_dense_in_L2Sigma (issue #113 PR-1: split out of
  -- SobolevEmbedding.lean; was reached transitively via SobolevEmbedding, no longer)
import LerayHopf.R3.TensorIntersection
import LerayHopf.Analysis.TensorEdgeGluing
import LerayHopf.Analysis.BilinearExtension
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

- on `𝒮 ⊗ L²_σ` (slot-2 Schwartz): for fixed Schwartz `s`, the map `l ↦ b(u, s, l)` is
  realized as a bounded linear extension (`convBLTspan`/`edge2Lift`) from the H¹ slice to all
  of `L²_σ`; in the tensor picture this edge bilinear is lifted via `TensorProduct.lift`
  to a `LinearMap` on `edgeSlot2` (NOT the raw `convFormH1 u s l` outside its H¹ domain);
- on `L²_σ ⊗ 𝒮` (slot-3 Schwartz): `(l, s) ↦ convFormH1 u l s = − convFormH1 u s l` (B6),
  lifted to a `LinearMap` on `edgeSlot3`.

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

**C3 note (issue #111 PR-4).** `convBLT_fixedTest` (single fixed `IsSchwartzDivFree_R3` test)
and `convBLTspan` (arbitrary `s ∈ schwartzSpan`, an explicit B7-type bound as hypothesis) used
to each build their own copy of the same two-stage "extend a bounded bilinear form off the
dense `H1Sigma' ↪ L2Sigma_R3`" tower (`LinearMap.extendOfNorm` on slot 2 then
`ContinuousLinearMap.extend` on slot 1). That tower is now a single generic lemma,
`LerayHopf.BilinearExtension.extendBoundedBilinearOfDense` (`LerayHopf/Analysis/
BilinearExtension.lean`), and both `convBLT_fixedTest`/`convBLTspan` are thin instantiations
of it at `D := H1Sigma'`, differing only in the bound they supply. No public statement
changed.

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

/-- The inner B7 bound at fixed `u`: `|innerLin w u v| ≤ (C_w ‖u‖) ‖v‖`. Shared by both the
fixed-test and span-bounded `convBLT` towers (issue #111 PR-4): the bound's provenance
(a single `IsSchwartzDivFree_R3` witness vs. an arbitrary `hbound` hypothesis) is opaque to
this transport step, so it takes only the raw `L2VF_R3`-level bound as input. -/
private theorem innerLin_bound
    (w : L2VF_R3) (hw_H1 : memH1VF_R3 w)
    {C_w : ℝ}
    (hbound : ∀ (u v : L2VF_R3) (hu : memH1VF_R3 u) (hv : memH1VF_R3 v)
      (hu_sigma : u ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3))
      (hv_sigma : v ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3)),
      |convFormH1 u v w hu hv hw_H1| ≤ C_w * ‖u‖ * ‖v‖)
    (u v : H1Sigma') :
    |innerLin w hw_H1 u v| ≤ C_w * ‖u‖ * ‖v‖ := by
  have hu_sigma : (vfOf u) ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3) := (u : L2Sigma_R3).2
  have hv_sigma : (vfOf v) ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3) := (v : L2Sigma_R3).2
  have := hbound (vfOf u) (vfOf v) (vfOf_mem u) (vfOf_mem v) hu_sigma hv_sigma
  rwa [← norm_eq_vfOf u, ← norm_eq_vfOf v] at this

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

/-- The continuous inclusion `H1Sigma' →L[ℝ] L2Sigma_R3`. -/
private noncomputable def eH1L : H1Sigma' →L[ℝ] L2Sigma_R3 := H1Sigma'.subtypeL

private theorem eH1L_apply (u : H1Sigma') : eH1L u = (u : L2Sigma_R3) := rfl

/-- `eH1L` restated against `H1Sigma'.subtypeL`, so the generic module's `_apply`/
`eq_of_agree_dense` lemmas (stated via `D.subtypeL`) can be `rw`-ed to the `eH1L`-phrased
shape the rest of this file's proofs are written against. -/
private theorem H1Sigma'_subtypeL_eq_eH1L :
    (H1Sigma'.subtypeL : H1Sigma' → L2Sigma_R3) = eH1L := rfl

private theorem denseRange_eH1L : DenseRange (eH1L : H1Sigma' → L2Sigma_R3) :=
  denseRange_H1Sigma'_subtype

private theorem isUniformInducing_eH1L : IsUniformInducing (eH1L : H1Sigma' → L2Sigma_R3) :=
  (isUniformEmbedding_subtype_val (p := fun x => x ∈ H1Sigma')).isUniformInducing

/-- `innerLin w hw_H1`, bundled as a genuine bilinear `LinearMap` on `H1Sigma'` (linear in
both slots via `innerLin_add_1`/`innerLin_smul_1` and `innerLin`'s own `map_add'`/`map_smul'`).
The generic `LerayHopf.BilinearExtension.extendBoundedBilinearOfDense` needs its bilinear
input pre-bundled this way. -/
private noncomputable def innerLinL (w : L2VF_R3) (hw_H1 : memH1VF_R3 w) :
    H1Sigma' →ₗ[ℝ] (H1Sigma' →ₗ[ℝ] ℝ) where
  toFun u := innerLin w hw_H1 u
  map_add' u u' := innerLin_add_1 w hw_H1 u u'
  map_smul' c u := innerLin_smul_1 w hw_H1 c u

/-- **C3 `convBLT_fixedTest` [PR-4 — PROVED].** Jointly continuous bilinear
`L2Sigma_R3 →L[ℝ] L2Sigma_R3 →L[ℝ] ℝ` extending `(u, v) ↦ convFormH1 u v w` for Schwartz
`w`: the generic bounded-bilinear-extension tower (issue #111 PR-4,
`LerayHopf.BilinearExtension.extendBoundedBilinearOfDense`) instantiated at
`D := H1Sigma'`, `β := innerLinL w hw_H1`, with the B7 bound `convFormH1_bound_Schwartz`. -/
noncomputable def convBLT_fixedTest
    (w : L2VF_R3) (hw_H1 : memH1VF_R3 w)
    (hw_sigma : w ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3))
    (hw_sch : IsSchwartzDivFree_R3 ⟨w, hw_sigma⟩) :
    L2Sigma_R3 →L[ℝ] L2Sigma_R3 →L[ℝ] ℝ :=
  LerayHopf.BilinearExtension.extendBoundedBilinearOfDense H1Sigma' denseRange_eH1
    (innerLinL w hw_H1) (convFormH1_bound_Schwartz w hw_H1 hw_sigma hw_sch).choose_spec.1
    (fun u v => innerLin_bound w hw_H1
      (convFormH1_bound_Schwartz w hw_H1 hw_sigma hw_sch).choose_spec.2 u v)

/-- **The determined-value identity on the H¹ slice.** For H¹ `u, v` (as `H1Sigma'`
elements), `convBLT_fixedTest w u v` is the genuine `convFormH1 u v w`. -/
theorem convBLT_fixedTest_eH1
    (w : L2VF_R3) (hw_H1 : memH1VF_R3 w)
    (hw_sigma : w ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3))
    (hw_sch : IsSchwartzDivFree_R3 ⟨w, hw_sigma⟩) (u v : H1Sigma') :
    convBLT_fixedTest w hw_H1 hw_sigma hw_sch (eH1L u) (eH1L v) = valH1 w hw_H1 u v :=
  LerayHopf.BilinearExtension.extendBoundedBilinearOfDense_apply H1Sigma' denseRange_eH1
    (innerLinL w hw_H1) (convFormH1_bound_Schwartz w hw_H1 hw_sigma hw_sch).choose_spec.1
    (fun u v => innerLin_bound w hw_H1
      (convFormH1_bound_Schwartz w hw_H1 hw_sigma hw_sch).choose_spec.2 u v) u v

/-! #### C3b — `w`-linearity of `convBLT_fixedTest`

The jointly continuous extension `convBLT_fixedTest w` is **linear in the fixed Schwartz
test `w`**.  Two such CLMs agreeing on the dense `H1Sigma' × H1Sigma'` square are equal
(`LerayHopf.BilinearExtension.eq_of_agree_dense`), and on that square the value is the
genuine `convFormH1 u v w` which is additive/homogeneous in `w` (B4c `convFormH1_add_3`,
B4d `convFormH1_smul_3`).  This is the span-representation-independence content the
edge bilinear needs. -/


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
  refine LerayHopf.BilinearExtension.eq_of_agree_dense H1Sigma' denseRange_eH1 (fun u v => ?_)
  rw [H1Sigma'_subtypeL_eq_eH1L]
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
  refine LerayHopf.BilinearExtension.eq_of_agree_dense H1Sigma' denseRange_eH1 (fun u v => ?_)
  rw [H1Sigma'_subtypeL_eq_eH1L]
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply,
    convBLT_fixedTest_eH1 (c • w) hcw_H1 hcw_sigma hcw_sch u v,
    convBLT_fixedTest_eH1 w hw_H1 hw_sigma hw_sch u v]
  unfold valH1
  rw [smul_eq_mul]
  exact convFormH1_smul_3 c (vfOf u) (vfOf v) w (vfOf_mem u) (vfOf_mem v) hw_H1

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
test field `s ∈ schwartzSpan`: the same generic tower as `convBLT_fixedTest` (issue #111
PR-4), instantiated with the span bound `convBLTspan_bound_spec` instead of a single
`IsSchwartzDivFree_R3` witness. -/
noncomputable def convBLTspan (s : schwartzSpan) :
    L2Sigma_R3 →L[ℝ] L2Sigma_R3 →L[ℝ] ℝ :=
  LerayHopf.BilinearExtension.extendBoundedBilinearOfDense H1Sigma' denseRange_eH1
    (innerLinL (s : L2VF_R3) (memH1VF_R3_of_mem_schwartzSpan s.2))
    (convBLTspan_bound_spec s.2).1
    (fun u v => innerLin_bound (s : L2VF_R3) (memH1VF_R3_of_mem_schwartzSpan s.2)
      (convBLTspan_bound_spec s.2).2 u v)

/-- `convBLTspan s` on the H¹ slice is the genuine `convFormH1`. -/
private theorem convBLTspan_eH1 (s : schwartzSpan) (u v : H1Sigma') :
    convBLTspan s (eH1L u) (eH1L v)
      = convFormH1 (vfOf u) (vfOf v) (s : L2VF_R3)
          (vfOf_mem u) (vfOf_mem v) (memH1VF_R3_of_mem_schwartzSpan s.2) :=
  LerayHopf.BilinearExtension.extendBoundedBilinearOfDense_apply H1Sigma' denseRange_eH1
    (innerLinL (s : L2VF_R3) (memH1VF_R3_of_mem_schwartzSpan s.2))
    (convBLTspan_bound_spec s.2).1
    (fun u v => innerLin_bound (s : L2VF_R3) (memH1VF_R3_of_mem_schwartzSpan s.2)
      (convBLTspan_bound_spec s.2).2 u v) u v

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
  refine LerayHopf.BilinearExtension.eq_of_agree_dense H1Sigma' denseRange_eH1 (fun u v => ?_)
  rw [H1Sigma'_subtypeL_eq_eH1L]
  rw [convBLTspan_eH1 ⟨⟨w, hw_sigma⟩, hmem⟩ u v,
    convBLT_fixedTest_eH1 w hw_H1 hw_sigma hw_sch u v]
  rfl

set_option maxHeartbeats 4000000 in
/-- `convBLTspan` is additive in `s`. -/
private theorem convBLTspan_add (s s' : schwartzSpan) :
    convBLTspan (s + s') = convBLTspan s + convBLTspan s' := by
  refine LerayHopf.BilinearExtension.eq_of_agree_dense H1Sigma' denseRange_eH1 (fun u v => ?_)
  rw [H1Sigma'_subtypeL_eq_eH1L]
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
  refine LerayHopf.BilinearExtension.eq_of_agree_dense H1Sigma' denseRange_eH1 (fun u v => ?_)
  rw [H1Sigma'_subtypeL_eq_eH1L]
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

/-! #### C5-c — the overlap agreement on `𝒮 ⊗ 𝒮`

`convBLTspan_overlap` below supplies the `BLT_overlap` hypothesis for the shared
`LerayHopf.TensorEdgeGluing` instantiation (C4–C8, below). -/

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

/-- `convBLTspan_overlap` restated against the (irreducible) `convBLTspanLin` head symbol,
so it matches the `BLT_overlap` hypothesis shape `TensorEdgeGluing` expects verbatim. -/
private theorem convBLTspanLin_overlap (u : L2Sigma_R3) (s s' : schwartzSpan) :
    convBLTspanLin s' u (s : L2Sigma_R3) = -(convBLTspanLin s u (s' : L2Sigma_R3)) := by
  simp only [convBLTspanLin_apply]
  exact convBLTspan_overlap u s s'

/-! ### C4–C8 — the shared tensor/edge-gluing instantiation (issue #111 PR-1)

`edgeSlot2`/`edgeSlot3`/`detDomain`/`antisymmetrizer`/`detExtend` and the
`convFormL2_def`/`_def_eq`/`_multilinear`/`_antisymm` tower are the generic
`LerayHopf.TensorEdgeGluing` construction instantiated at
`(L2Sigma_R3, schwartzSpan, convBLTspanLin, convBLTspanLin_overlap)`. Public names/statements
are unchanged (Hard Rule #2); the previously ~650-line C4–C8 block now lives once in
`LerayHopf/Analysis/TensorEdgeGluing.lean`. -/

/-- The "slot-2 Schwartz" edge submodule `𝒮 ⊗ L²_σ ≤ L²_σ ⊗ L²_σ`. -/
noncomputable def edgeSlot2 : Submodule ℝ (TensorProduct ℝ L2Sigma_R3 L2Sigma_R3) :=
  LerayHopf.TensorEdgeGluing.edgeSlot2 schwartzSpan

/-- The "slot-3 Schwartz" edge submodule `L²_σ ⊗ 𝒮 ≤ L²_σ ⊗ L²_σ`. -/
noncomputable def edgeSlot3 : Submodule ℝ (TensorProduct ℝ L2Sigma_R3 L2Sigma_R3) :=
  LerayHopf.TensorEdgeGluing.edgeSlot3 schwartzSpan

/-- **`D` (the determined domain).** `D := (𝒮 ⊗ L²_σ) + (L²_σ ⊗ 𝒮)`. -/
noncomputable def detDomain : Submodule ℝ (TensorProduct ℝ L2Sigma_R3 L2Sigma_R3) :=
  LerayHopf.TensorEdgeGluing.detDomain schwartzSpan

/-- **The overlap identity (consumes the proved tensor-intersection lemma).**
`(𝒮 ⊗ L²_σ) ⊓ (L²_σ ⊗ 𝒮) = 𝒮 ⊗ 𝒮`, on whose image the two edge prescriptions agree.
This is `TensorIntersection.range_map_subtype_inf_range_map_subtype` specialized to
`S = schwartzSpan`, exactly as Torus's `edge_inf_eq_galerkin_tensor`. -/
theorem edge_inf_eq_schwartz_tensor :
    edgeSlot2 ⊓ edgeSlot3
      = LinearMap.range (TensorProduct.mapIncl schwartzSpan schwartzSpan) :=
  LerayHopf.R3.TensorIntersection.range_map_subtype_inf_range_map_subtype schwartzSpan

/-- The antisymmetrizer `A := (id − swap)/2` on `L²_σ ⊗ L²_σ`. -/
noncomputable def antisymmetrizer :
    TensorProduct ℝ L2Sigma_R3 L2Sigma_R3 →ₗ[ℝ] TensorProduct ℝ L2Sigma_R3 L2Sigma_R3 :=
  LerayHopf.TensorEdgeGluing.antisymmetrizer (X := L2Sigma_R3)

/-- **`detExtend` (`Bext`).** The determined form `b u v w := detExtend u (v ⊗ₜ w)`; see
`LerayHopf.TensorEdgeGluing.detExtend` for the construction. -/
noncomputable def detExtend :
    L2Sigma_R3 →ₗ[ℝ] (TensorProduct ℝ L2Sigma_R3 L2Sigma_R3) →ₗ[ℝ] ℝ :=
  LerayHopf.TensorEdgeGluing.detExtend schwartzSpan convBLTspanLin convBLTspanLin_overlap

/-- **`convFormL2_def` (`b`).** The determined trilinear convection form
`b u v w := detExtend u (v ⊗ₜ w)`. -/
noncomputable def convFormL2_def (u v w : L2Sigma_R3) : ℝ :=
  LerayHopf.TensorEdgeGluing.convFormL2_def schwartzSpan convBLTspanLin convBLTspanLin_overlap u v w

@[simp]
theorem convFormL2_def_eq (u v w : L2Sigma_R3) :
    convFormL2_def u v w = detExtend u (v ⊗ₜ[ℝ] w) :=
  LerayHopf.TensorEdgeGluing.convFormL2_def_eq schwartzSpan convBLTspanLin convBLTspanLin_overlap u v w

/-- `∃ B trilinear, ∀ u v w, b u v w = B u v w`. -/
theorem convFormL2_multilinear :
    ∃ B : L2Sigma_R3 →ₗ[ℝ] L2Sigma_R3 →ₗ[ℝ] L2Sigma_R3 →ₗ[ℝ] ℝ,
      ∀ (u v w : L2Sigma_R3), convFormL2_def u v w = B u v w :=
  LerayHopf.TensorEdgeGluing.convFormL2_multilinear schwartzSpan convBLTspanLin convBLTspanLin_overlap

/-- `b u v w = − b u w v` for all `u v w`. -/
theorem convFormL2_antisymm (u v w : L2Sigma_R3) :
    convFormL2_def u v w = -convFormL2_def u w v :=
  LerayHopf.TensorEdgeGluing.convFormL2_antisymm schwartzSpan convBLTspanLin convBLTspanLin_overlap u v w

/-- **C5b `detExtend_on_edgeSlot3` [the determined identity].**
On the slot-3-Schwartz edge `L²_σ ⊗ 𝒮`, `detExtend u` is the genuine determined value:
for ALL `u, v` and any Schwartz `w`, `detExtend u (v ⊗ₜ w) = convBLT_fixedTest w … u v`,
i.e. the value is the evaluation of the jointly continuous B7-bounded extension `Bw` (C3),
NOT a Hamel value. Derived from the generic `TensorEdgeGluing.detExtend_edge3_eq` (the
algebraic core) composed with `convBLTspan_eq_fixedTest` (the lane-specific bridge to `Bw`).
This is the load-bearing identity for `b_cont_fixedTest`. -/
theorem detExtend_on_edgeSlot3
    (u v : L2Sigma_R3) (w : L2VF_R3) (hw_H1 : memH1VF_R3 w)
    (hw_sigma : w ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3))
    (hw_sch : IsSchwartzDivFree_R3 ⟨w, hw_sigma⟩) :
    detExtend u ((v : L2Sigma_R3) ⊗ₜ[ℝ] (⟨w, hw_sigma⟩ : L2Sigma_R3))
      = convBLT_fixedTest w hw_H1 hw_sigma hw_sch u v := by
  have hmem : (⟨w, hw_sigma⟩ : L2Sigma_R3) ∈ schwartzSpan := subset_schwartzSpan hw_sch
  show LerayHopf.TensorEdgeGluing.detExtend schwartzSpan convBLTspanLin convBLTspanLin_overlap u
      ((v : L2Sigma_R3) ⊗ₜ[ℝ] (⟨w, hw_sigma⟩ : L2Sigma_R3))
    = convBLT_fixedTest w hw_H1 hw_sigma hw_sch u v
  rw [LerayHopf.TensorEdgeGluing.detExtend_edge3_eq schwartzSpan convBLTspanLin
      convBLTspanLin_overlap u v (⟨⟨w, hw_sigma⟩, hmem⟩ : schwartzSpan),
    convBLTspanLin_apply, convBLTspan_eq_fixedTest w hw_H1 hw_sigma hw_sch hmem]

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

/-! ### C11 — `r3ConvectionGapOp_holds` (assembled theorem) -/

/-- **C11 `r3ConvectionGapOp_holds` [assembled].**
`∀ 𝔊 : R3GalerkinScheme, Nonempty (ConvectionGapOp 𝔊)`.

Theorem replacing the former `r3ConvectionGapOp_exists` axiom.  The root namespace re-exports
this theorem under that compatibility name (Hard Rule #2).  Assembled from the five
determined-form fields:
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

namespace LerayHopf

/-- The ℝ³ weak-convection operator-gap exists — THEOREM (formerly `axiom r3ConvectionGapOp_exists`,
removed in issue #56). Re-exports the proved `ConvectionExtension.r3ConvectionGapOp_holds` under the
original public name (Hard Rule #2: no rename). Being a theorem, it does NOT appear in `#print axioms`,
so the capstone stays at 2 project axioms. -/
theorem r3ConvectionGapOp_exists (𝔊 : R3GalerkinScheme) : Nonempty (ConvectionGapOp 𝔊) :=
  LerayHopf.R3.ConvectionExtension.r3ConvectionGapOp_holds 𝔊

/-- The ℝ³ NS convection form exists — THEOREM (was axiom `r3ConvectionGapOp_exists`, issue #56),
now proved from `r3ConvectionGapOp_holds` (the sorry-free determined-form construction in
`ConvectionExtension.lean`) + proved density, via the sorry-free `R3NSForms_of_gap`.

Route: obtain `g : ConvectionGapOp 𝔊` from the proved theorem `r3ConvectionGapOp_holds`;
supply proved density (`convectionGap_schwartz_dense curlSchwartzDense_holds`) as
`schwartz_dense`; assemble a full `ConvectionGap 𝔊`; apply `R3NSForms_of_gap`.

The conclusion `Nonempty (R3NSForms 𝔊)` is IDENTICAL to what `r3_NSForms_exist` asserted —
no statement weakening.  The operator core is now PROVED sorry-free in this file
(`r3ConvectionGapOp_holds`, C11); no project axiom remains for the convection operator.
Mirrors the torus `torus3_NSForms_exists` (issue #22). -/
theorem r3_NSForms_exists (𝔊 : R3GalerkinScheme) : Nonempty (R3NSForms 𝔊) :=
  (r3ConvectionGapOp_exists 𝔊).elim fun g =>
    R3NSForms_of_gap 𝔊
      { b              := g.b
      , b_extends      := g.b_extends
      , b_multilinear  := g.b_multilinear
      , b_antisymm_gap := g.b_antisymm_gap
      , b_cont_fixedTest := g.b_cont_fixedTest
      , schwartz_dense := convectionGap_schwartz_dense curlSchwartzDense_holds }

end LerayHopf
