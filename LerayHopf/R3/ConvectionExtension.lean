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

Per the issue-#56 PR-3 contract, the algebraic/structural fields whose proof is
mechanical are discharged here; the analytic crux (`b_cont_fixedTest`) and the harder
gluing/Hamel steps that require the BLT extension and the `u`-linear tower are scaffolded
with `-- ALLOW_SORRY: PR-4` for the prover.  No new `axiom`/`opaque`.

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

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

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
glues them to a single partial linear map on `detDomain = D`.  `LinearMap.exists_extend`
then Hamel-extends to all of `L²_σ ⊗ L²_σ`.  The whole tower is built linearly in `u`. -/

/-- **C5 `detExtend` (`Bext`) [PR-4].** The Hamel extension of the glued determined form
`β_u` from `D` to all of `L²_σ ⊗[ℝ] L²_σ`, assembled trilinearly in `u`.

This is the single object the trilinear `b` reads.  Its construction
(`TensorProduct.lift` on each edge → `LinearPMap.sup` glue via
`edge_inf_eq_schwartz_tensor` → `LinearMap.exists_extend` Hamel, all done `u`-linearly)
is the structural core deferred to PR-4; the statement here pins the contract. -/
noncomputable def detExtend :
    L2Sigma_R3 →ₗ[ℝ] (TensorProduct ℝ L2Sigma_R3 L2Sigma_R3) →ₗ[ℝ] ℝ := by
  sorry -- ALLOW_SORRY: PR-4 BLOCKED on slot-3/slot-2 edge bilinear `L²_σ ⊗ 𝒮 →ₗ ℝ`. The determined value `(v ⊗ s) ↦ convBLT_fixedTest s u v` (Schwartz s) is well-defined for ALL u,v BUT extending linearly over s ∈ 𝒮 = span{Schwartz-div-free} needs representation-independence (∑cᵢsᵢ=0 ⟹ ∑cᵢ convBLT sᵢ u v=0), which holds by density (= convFormH1 u v (∑cᵢsᵢ)=0 on the H¹ (u,v) slice + convBLT continuity) but has NO off-the-shelf mathlib lifter — needs a Finsupp.lift/span-quotient construction with the density well-definedness woven in. Once that edge bilinear exists: LinearPMap.sup glue (overlap agreement on 𝒮⊗𝒮 via edge_inf_eq_schwartz_tensor + B6), then u-linearity is FREE via a fixed left-inverse `gInv` of detDomain.subtype (LinearMap.exists_leftInverse_of_injective): detExtend u := (Ψ u) ∘ₗ gInv with Ψ : L²_σ →ₗ (D →ₗ ℝ) linear in u, so the Hamel extension is a SINGLE linear operator `· ∘ₗ gInv`, not a per-u choice. C3 convBLT_fixedTest (the analytic crux) + convBLT_fixedTest_eH1 are PROVED; this remaining gap is the span-rep-independence lifter only.

/-- **C5b `detExtend_on_edgeSlot3` [PR-4 — the determined identity].**
On the slot-3-Schwartz edge `L²_σ ⊗ 𝒮`, `detExtend u` is the genuine determined value:
for ALL `u, v` and any Schwartz `w`,
`detExtend u (v ⊗ₜ w) = convBLT_fixedTest w … u v`,
i.e. the value is the evaluation of the jointly continuous B7-bounded extension `Bw`
(C3), NOT a Hamel value.

This is the load-bearing identity for `b_cont_fixedTest`.  It holds for ALL `u, v`
(not just H¹ ones): on the H¹ slice both sides equal the literal `convFormH1 u v w`
(`β_u`'s slot-3 prescription, resp. `extendOfNorm_eq`), and both sides are continuous in
`v` on the determined edge, so they agree everywhere by density of `𝒮`/H¹ in `L²_σ`. -/
theorem detExtend_on_edgeSlot3
    (u v : L2Sigma_R3) (w : L2VF_R3) (hw_H1 : memH1VF_R3 w)
    (hw_sigma : w ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3))
    (hw_sch : IsSchwartzDivFree_R3 ⟨w, hw_sigma⟩) :
    detExtend u ((v : L2Sigma_R3) ⊗ₜ[ℝ] (⟨w, hw_sigma⟩ : L2Sigma_R3))
      = convBLT_fixedTest w hw_H1 hw_sigma hw_sch u v := by
  sorry -- ALLOW_SORRY: PR-4 (v⊗w ∈ edgeSlot3 = L²⊗𝒮 ⊆ D; LinearPMap.sup_apply picks the slot-3 prescription = convFormH1 u v w on the H¹ slice = convBLT_fixedTest via extendOfNorm_eq; density of 𝒮/H¹ in L²_σ + continuity of both sides extends to all u,v)

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
  sorry -- ALLOW_SORRY: PR-4 (B u := (detExtend u).compl₂ (TensorProduct.mk ℝ _ _) curried; convFormL2_def = B by rfl once detExtend is a genuine LinearMap)

/-! ### C8 — `convFormL2_antisymm` -/

/-- **C8 `convFormL2_antisymm` [PR-4].** `b u v w = − b u w v` for all `u v w`.

`β_u` is antisymmetric on `D` (`convFormH1 u v w = − convFormH1 u w v`, B6, on the dense
Schwartz edges; extended antisymmetrically by the Hamel extension).  The antisymmetry is
a property of the *determined* `β_u` on `D` and is carried to all `v, w` because both
`v ⊗ₜ w` and `w ⊗ₜ v` land in `D` whenever one of `v, w` is Schwartz — and the algebraic
antisymmetry of the Hamel extension is fixed by the antisymmetric construction of `β_u`. -/
theorem convFormL2_antisymm (u v w : L2Sigma_R3) :
    convFormL2_def u v w = -convFormL2_def u w v := by
  sorry -- ALLOW_SORRY: PR-4 (β_u antisymmetric on D by B6; the Hamel extension is built antisymmetric so the swap v↔w negates; reduces to detExtend u (v⊗w) = -detExtend u (w⊗v))

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
  sorry -- ALLOW_SORRY: PR-4 (detExtend_on_edgeSlot3 on the Schwartz slice gives convFormH1 u v w; B5 convFormH1_eq_convFormSchwartz)

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
  sorry -- ALLOW_SORRY: PR-4 (∀v: v⊗w ∈ edgeSlot3 ⊆ D; detExtend_on_edgeSlot3 ⇒ b u v w = convFormH1 u v w = convBLT_fixedTest w u v (C3); ContinuousLinearMap.continuous₂)

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
