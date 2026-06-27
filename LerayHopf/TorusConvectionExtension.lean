import LerayHopf.TorusEnergyConvection
import LerayHopf.TorusConvectionForm
import LerayHopf.R3.TensorIntersection
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.LinearAlgebra.LinearPMap
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Analysis.Normed.Operator.Extend

/-!
# TorusConvectionExtension — determined-form construction of the full torus `b` form (torus #53)

**File:** `LerayHopf/TorusConvectionExtension.lean`

## What this file builds

This file constructs the scaffold for the trilinear convection form
`convFormL2_def : L2Sigma → L2Sigma → L2Sigma → ℝ` together with all seven
fields of `TorusConvectionGap`, mirroring `LerayHopf/R3/ConvectionExtension.lean`.

The construction uses the **determined-form** approach:
- The "edge" submodule is `galerkinTestSpan := Submodule.span ℝ {x : L2Sigma | IsGalerkinTest x}`,
  the span of Galerkin tests `𝒢`, replacing R3's `schwartzSpan`.
- The determined bilinear on each edge uses `convFormFourier` (the Fourier-side tsum form
  from `TorusEnergyConvection.lean`), which is summable on the Galerkin-test slice
  (`convSummand_summable`).
- The overlap identity `(𝒢 ⊗ L²) ∩ (L² ⊗ 𝒢) = 𝒢 ⊗ 𝒢` is discharged immediately by the
  generic `TensorIntersection.range_map_subtype_inf_range_map_subtype`.

## Declarations delivered

### Proved sorry-free
- `galerkinTestSpan` — the Galerkin-test span submodule `𝒢 ≤ L²_σ`
- `edgeSlot2`, `edgeSlot3`, `detDomain` — the two edge submodules and their sup
- `edge_inf_eq_galerkin_tensor` — `(𝒢 ⊗ L²) ⊓ (L² ⊗ 𝒢) = 𝒢 ⊗ 𝒢` (direct reuse)

### Scaffold (`:= by sorry -- ALLOW_SORRY`)
- `convBLTgalerkin` — the jointly continuous bilinear for a fixed Galerkin test `w`
- `convBLTgalerkinLin` — linearity of `convBLTgalerkin` in the test slot
- `antisymmetrizer` — `(id − swap)/2` on `L²_σ ⊗ L²_σ`
- `gInv` — left-inverse of `detDomain.subtype`
- `detExtend` — the determined extension `L²_σ →ₗ (L²_σ ⊗ L²_σ) →ₗ ℝ`
- `convFormL2_def` — the trilinear `b u v w := detExtend u (v ⊗ₜ w)`
- `torusConvectionGap_holds` — assembly theorem (7 fields, mostly scaffolded)

## Axiom status

No new `axiom`/`opaque`. All analytic obligations are scaffold `sorry`s with
`ALLOW_SORRY: PR-2 determined-form, prover discharges (torus #53)` markers.
-/

open MeasureTheory TensorProduct

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 4000000

namespace LerayHopf.TorusConvectionExtension

/-! ### T0 — `galerkinTestSpan` : the Galerkin-test span `𝒢` -/

/-- **`galerkinTestSpan` (`𝒢`) [proved sorry-free].** The submodule of `L2Sigma`
spanned by the Galerkin-test class — the smooth "edge" used in the determined
construction:

`𝒢 := Submodule.span ℝ {x : L2Sigma | IsGalerkinTest x}`. -/
noncomputable def galerkinTestSpan : Submodule ℝ L2Sigma :=
  Submodule.span ℝ {x : L2Sigma | IsGalerkinTest x}

theorem subset_galerkinTestSpan {x : L2Sigma} (hx : IsGalerkinTest x) :
    x ∈ galerkinTestSpan :=
  Submodule.subset_span hx

/-- Every `x ∈ galerkinTestSpan` is H¹ (Galerkin tests are H¹ by `galerkinTestSpan_subset_H1Sigma`,
and `H1SigmaTorus` is closed under span — the submodule closure follows by span_induction). -/
theorem galerkinTestSpan_le_H1SigmaTorus : galerkinTestSpan ≤ H1SigmaTorus := by
  rw [galerkinTestSpan, Submodule.span_le]
  intro x hx
  exact galerkinTestSpan_subset_H1Sigma hx

/-! ### T1 — the three edge submodules -/

/-- The "slot-2 Galerkin" edge submodule `𝒢 ⊗ L²_σ ≤ L²_σ ⊗ L²_σ`. -/
noncomputable def edgeSlot2 : Submodule ℝ (TensorProduct ℝ L2Sigma L2Sigma) :=
  LinearMap.range (TensorProduct.map galerkinTestSpan.subtype (LinearMap.id : L2Sigma →ₗ[ℝ] L2Sigma))

/-- The "slot-3 Galerkin" edge submodule `L²_σ ⊗ 𝒢 ≤ L²_σ ⊗ L²_σ`. -/
noncomputable def edgeSlot3 : Submodule ℝ (TensorProduct ℝ L2Sigma L2Sigma) :=
  LinearMap.range (TensorProduct.map (LinearMap.id : L2Sigma →ₗ[ℝ] L2Sigma) galerkinTestSpan.subtype)

/-- **`detDomain` — the determined domain `D`.** `D := (𝒢 ⊗ L²_σ) + (L²_σ ⊗ 𝒢)`. -/
noncomputable def detDomain : Submodule ℝ (TensorProduct ℝ L2Sigma L2Sigma) :=
  edgeSlot2 ⊔ edgeSlot3

/-- **`edge_inf_eq_galerkin_tensor` [proved sorry-free].** The overlap identity:
`(𝒢 ⊗ L²_σ) ⊓ (L²_σ ⊗ 𝒢) = 𝒢 ⊗ 𝒢`.

Direct reuse of the generic `TensorIntersection.range_map_subtype_inf_range_map_subtype`
instantiated at `S := galerkinTestSpan`, exactly as R3's `edge_inf_eq_schwartz_tensor`. -/
theorem edge_inf_eq_galerkin_tensor :
    edgeSlot2 ⊓ edgeSlot3
      = LinearMap.range (TensorProduct.mapIncl galerkinTestSpan galerkinTestSpan) :=
  LerayHopf.R3.TensorIntersection.range_map_subtype_inf_range_map_subtype galerkinTestSpan

/-! ### T2 — the edge bilinears from `convFormFourier` (scaffold)

For a fixed Galerkin test `w`, `convFormFourier u v w` is the determined value on the
Galerkin-test slice.  The two edge prescriptions mirror R3's `edge2Bil` / `edge3Bil`:

- on `𝒢 ⊗ L²_σ` (slot-2 Galerkin): `(s, l) ↦ -convFormFourier u s l`
  (antisymmetric of the slot-3 value, by `convFormFourier_antisymm_galerkinTest`);
- on `L²_σ ⊗ 𝒢` (slot-3 Galerkin): `(l, s) ↦ convFormFourier u l s`.

The analytic obligation (jointly continuous BLT extension off the Galerkin-test slice to
all of `L²_σ`) is the scaffold target for PR-2. -/

/-- **`convBLTgalerkin` [scaffold].** Jointly continuous bilinear form
`L2Sigma →L[ℝ] L2Sigma →L[ℝ] ℝ` extending `(u, v) ↦ convFormFourier u v w` for a
fixed Galerkin test `w : galerkinTestSpan`.

PR-2 prover obligation: construct the BLT extension via the H¹ density of Galerkin tests
and `convSummand_summable` / `galerkinConvection_bound`. -/
noncomputable def convBLTgalerkin (w : galerkinTestSpan) :
    L2Sigma →L[ℝ] L2Sigma →L[ℝ] ℝ := by
  sorry -- ALLOW_SORRY: PR-2 determined-form, prover discharges (torus #53)

/-- **`convBLTgalerkin_span_linear` [scaffold].** The map `w ↦ convBLTgalerkin w` is
ℝ-linear over `galerkinTestSpan`.

PR-2 prover obligation: prove linearity via the dense-agreement argument (same dense
Galerkin-test × Galerkin-test square), using `convFormFourier`'s linearity in the third slot. -/
noncomputable def convBLTgalerkinLin :
    galerkinTestSpan →ₗ[ℝ] (L2Sigma →L[ℝ] L2Sigma →L[ℝ] ℝ) where
  toFun := convBLTgalerkin
  map_add' s s' := by
    sorry -- ALLOW_SORRY: PR-2 determined-form, prover discharges (torus #53)
  map_smul' c s := by
    sorry -- ALLOW_SORRY: PR-2 determined-form, prover discharges (torus #53)

/-! ### T3 — the two edge `TensorProduct.lift` functionals (scaffold) -/

/-- The ℝ-linear evaluation `B ↦ B u v` on continuous bilinear forms (torus version). -/
private noncomputable def evalBil (u v : L2Sigma) :
    (L2Sigma →L[ℝ] L2Sigma →L[ℝ] ℝ) →ₗ[ℝ] ℝ where
  toFun B := B u v
  map_add' B B' := by simp
  map_smul' c B := by simp

/-- The slot-3 determined value as a linear functional in the Galerkin factor:
`s ↦ convBLTgalerkin s u v`. -/
private noncomputable def edge3Sval (u v : L2Sigma) : galerkinTestSpan →ₗ[ℝ] ℝ :=
  (evalBil u v).comp convBLTgalerkinLin

@[simp]
private theorem edge3Sval_apply (u v : L2Sigma) (s : galerkinTestSpan) :
    edge3Sval u v s = convBLTgalerkin s u v := by
  unfold edge3Sval
  rw [LinearMap.comp_apply]; rfl

/-- The slot-3 edge bilinear `b3 u : L²_σ →ₗ 𝒢 →ₗ ℝ`, `b3 u v s = convBLTgalerkin s u v`. -/
private noncomputable def edge3Bil (u : L2Sigma) :
    L2Sigma →ₗ[ℝ] galerkinTestSpan →ₗ[ℝ] ℝ where
  toFun v := edge3Sval u v
  map_add' v v' := by
    refine LinearMap.ext (fun s => ?_)
    simp only [edge3Sval_apply, LinearMap.add_apply, map_add]
  map_smul' c v := by
    refine LinearMap.ext (fun s => ?_)
    simp only [edge3Sval_apply, LinearMap.smul_apply, RingHom.id_apply, map_smul, smul_eq_mul]

@[simp]
private theorem edge3Bil_apply (u v : L2Sigma) (s : galerkinTestSpan) :
    edge3Bil u v s = convBLTgalerkin s u v := edge3Sval_apply u v s

/-- The slot-2 determined value as a linear functional:
`s ↦ -convBLTgalerkin s u l`. -/
private noncomputable def edge2Lval (u : L2Sigma) (s : galerkinTestSpan) :
    L2Sigma →ₗ[ℝ] ℝ :=
  -(convBLTgalerkin s u).toLinearMap

@[simp]
private theorem edge2Lval_apply (u : L2Sigma) (s : galerkinTestSpan) (l : L2Sigma) :
    edge2Lval u s l = -(convBLTgalerkin s u l) := rfl

/-- The slot-2 edge bilinear `b2 u : 𝒢 →ₗ L²_σ →ₗ ℝ`, `b2 u s l = -convBLTgalerkin s u l`. -/
private noncomputable def edge2Bil (u : L2Sigma) :
    galerkinTestSpan →ₗ[ℝ] L2Sigma →ₗ[ℝ] ℝ where
  toFun s := edge2Lval u s
  map_add' s s' := by
    refine LinearMap.ext (fun l => ?_)
    simp only [edge2Lval_apply, LinearMap.add_apply,
      show convBLTgalerkin (s + s') = convBLTgalerkin s + convBLTgalerkin s' from
        convBLTgalerkinLin.map_add s s',
      ContinuousLinearMap.add_apply, neg_add]
  map_smul' c s := by
    refine LinearMap.ext (fun l => ?_)
    simp only [edge2Lval_apply, LinearMap.smul_apply,
      show convBLTgalerkin (c • s) = c • convBLTgalerkin s from
        convBLTgalerkinLin.map_smul c s,
      ContinuousLinearMap.smul_apply, smul_eq_mul, RingHom.id_apply, mul_neg]

@[simp]
private theorem edge2Bil_apply (u : L2Sigma) (s : galerkinTestSpan) (l : L2Sigma) :
    edge2Bil u s l = -(convBLTgalerkin s u l) := edge2Lval_apply u s l

/-- The slot-3 edge bilinear bundled **linearly in `u`**. -/
private noncomputable def edge3BilL :
    L2Sigma →ₗ[ℝ] (L2Sigma →ₗ[ℝ] galerkinTestSpan →ₗ[ℝ] ℝ) where
  toFun := edge3Bil
  map_add' u u' := by
    refine LinearMap.ext (fun v => LinearMap.ext (fun s => ?_))
    simp only [edge3Bil_apply, LinearMap.add_apply,
      show convBLTgalerkin s (u + u') = convBLTgalerkin s u + convBLTgalerkin s u' from
        (convBLTgalerkin s).map_add u u',
      ContinuousLinearMap.add_apply]
  map_smul' c u := by
    refine LinearMap.ext (fun v => LinearMap.ext (fun s => ?_))
    simp only [edge3Bil_apply, LinearMap.smul_apply, RingHom.id_apply,
      show convBLTgalerkin s (c • u) = c • convBLTgalerkin s u from
        (convBLTgalerkin s).map_smul c u,
      ContinuousLinearMap.smul_apply, smul_eq_mul]

/-- The slot-2 edge bilinear bundled **linearly in `u`**. -/
private noncomputable def edge2BilL :
    L2Sigma →ₗ[ℝ] (galerkinTestSpan →ₗ[ℝ] L2Sigma →ₗ[ℝ] ℝ) where
  toFun := edge2Bil
  map_add' u u' := by
    refine LinearMap.ext (fun s => LinearMap.ext (fun l => ?_))
    simp only [edge2Bil_apply, LinearMap.add_apply,
      show convBLTgalerkin s (u + u') = convBLTgalerkin s u + convBLTgalerkin s u' from
        (convBLTgalerkin s).map_add u u',
      ContinuousLinearMap.add_apply, neg_add]
  map_smul' c u := by
    refine LinearMap.ext (fun s => LinearMap.ext (fun l => ?_))
    simp only [edge2Bil_apply, LinearMap.smul_apply, RingHom.id_apply,
      show convBLTgalerkin s (c • u) = c • convBLTgalerkin s u from
        (convBLTgalerkin s).map_smul c u,
      ContinuousLinearMap.smul_apply, smul_eq_mul, mul_neg]

/-- The slot-3 lift: `L²_σ →ₗ (L²_σ ⊗ 𝒢 →ₗ ℝ)`, linear in `u`. -/
private noncomputable def edge3LiftL :
    L2Sigma →ₗ[ℝ] (TensorProduct ℝ L2Sigma galerkinTestSpan →ₗ[ℝ] ℝ) :=
  (TensorProduct.uncurry (RingHom.id ℝ) L2Sigma galerkinTestSpan ℝ).comp edge3BilL

/-- The slot-2 lift: `L²_σ →ₗ (𝒢 ⊗ L²_σ →ₗ ℝ)`, linear in `u`. -/
private noncomputable def edge2LiftL :
    L2Sigma →ₗ[ℝ] (TensorProduct ℝ galerkinTestSpan L2Sigma →ₗ[ℝ] ℝ) :=
  (TensorProduct.uncurry (RingHom.id ℝ) galerkinTestSpan L2Sigma ℝ).comp edge2BilL

private noncomputable def edge3Lift (u : L2Sigma) :
    TensorProduct ℝ L2Sigma galerkinTestSpan →ₗ[ℝ] ℝ :=
  edge3LiftL u

private noncomputable def edge2Lift (u : L2Sigma) :
    TensorProduct ℝ galerkinTestSpan L2Sigma →ₗ[ℝ] ℝ :=
  edge2LiftL u

private theorem edge3Lift_tmul (u v : L2Sigma) (s : galerkinTestSpan) :
    edge3Lift u (v ⊗ₜ[ℝ] s) = convBLTgalerkin s u v := by
  show edge3LiftL u (v ⊗ₜ[ℝ] s) = convBLTgalerkin s u v
  unfold edge3LiftL
  rw [LinearMap.comp_apply, TensorProduct.uncurry_apply]
  show edge3Bil u v s = convBLTgalerkin s u v
  exact edge3Bil_apply u v s

private theorem edge2Lift_tmul (u : L2Sigma) (s : galerkinTestSpan) (l : L2Sigma) :
    edge2Lift u (s ⊗ₜ[ℝ] l) = -(convBLTgalerkin s u l) := by
  show edge2LiftL u (s ⊗ₜ[ℝ] l) = -(convBLTgalerkin s u l)
  unfold edge2LiftL
  rw [LinearMap.comp_apply, TensorProduct.uncurry_apply]
  show edge2Bil u s l = -(convBLTgalerkin s u l)
  exact edge2Bil_apply u s l

private theorem edge3Lift_add (u u' : L2Sigma) (z : TensorProduct ℝ L2Sigma galerkinTestSpan) :
    edge3Lift (u + u') z = edge3Lift u z + edge3Lift u' z := by
  show edge3LiftL (u + u') z = edge3LiftL u z + edge3LiftL u' z
  simp only [edge3LiftL, LinearMap.comp_apply]
  rw [map_add, map_add, LinearMap.add_apply]

private theorem edge3Lift_smul (c : ℝ) (u : L2Sigma)
    (z : TensorProduct ℝ L2Sigma galerkinTestSpan) :
    edge3Lift (c • u) z = c • edge3Lift u z := by
  show edge3LiftL (c • u) z = c • edge3LiftL u z
  simp only [edge3LiftL, LinearMap.comp_apply]
  rw [map_smul, map_smul, LinearMap.smul_apply]

private theorem edge2Lift_add (u u' : L2Sigma) (z : TensorProduct ℝ galerkinTestSpan L2Sigma) :
    edge2Lift (u + u') z = edge2Lift u z + edge2Lift u' z := by
  show edge2LiftL (u + u') z = edge2LiftL u z + edge2LiftL u' z
  simp only [edge2LiftL, LinearMap.comp_apply]
  rw [map_add, map_add, LinearMap.add_apply]

private theorem edge2Lift_smul (c : ℝ) (u : L2Sigma)
    (z : TensorProduct ℝ galerkinTestSpan L2Sigma) :
    edge2Lift (c • u) z = c • edge2Lift u z := by
  show edge2LiftL (c • u) z = c • edge2LiftL u z
  simp only [edge2LiftL, LinearMap.comp_apply]
  rw [map_smul, map_smul, LinearMap.smul_apply]

attribute [irreducible] edge3Lift edge2Lift

/-! ### T4 — the projection `projG`, retractions, and the overlap agreement (scaffold) -/

/-- A complement of `galerkinTestSpan` and the resulting data. -/
private noncomputable def galerkinCompl : Submodule ℝ L2Sigma :=
  (galerkinTestSpan.exists_isCompl).choose

private theorem galerkinCompl_isCompl : IsCompl galerkinTestSpan galerkinCompl :=
  (galerkinTestSpan.exists_isCompl).choose_spec

/-- The projection `L²_σ →ₗ 𝒢` (left inverse of `galerkinTestSpan.subtype`). -/
private noncomputable def projG : L2Sigma →ₗ[ℝ] galerkinTestSpan :=
  galerkinTestSpan.projectionOnto galerkinCompl galerkinCompl_isCompl

@[simp]
private theorem projG_subtype (s : galerkinTestSpan) : projG (s : L2Sigma) = s :=
  Submodule.projectionOnto_apply_left galerkinCompl_isCompl s

private theorem projG_comp_subtype :
    projG.comp galerkinTestSpan.subtype = LinearMap.id := by
  refine LinearMap.ext (fun s => ?_)
  simp [projG_subtype]

/-- Slot-3 retraction `retr3 : (L²_σ ⊗ L²_σ) →ₗ (L²_σ ⊗ 𝒢)`. -/
private noncomputable def retr3 :
    TensorProduct ℝ L2Sigma L2Sigma →ₗ[ℝ] TensorProduct ℝ L2Sigma galerkinTestSpan :=
  TensorProduct.map LinearMap.id projG

/-- Slot-2 retraction `retr2 : (L²_σ ⊗ L²_σ) →ₗ (𝒢 ⊗ L²_σ)`. -/
private noncomputable def retr2 :
    TensorProduct ℝ L2Sigma L2Sigma →ₗ[ℝ] TensorProduct ℝ galerkinTestSpan L2Sigma :=
  TensorProduct.map projG LinearMap.id

private theorem retr3_map_id_subtype :
    retr3.comp (TensorProduct.map LinearMap.id galerkinTestSpan.subtype) = LinearMap.id := by
  unfold retr3
  rw [← TensorProduct.map_comp, LinearMap.id_comp, projG_comp_subtype, TensorProduct.map_id]

private theorem retr2_map_subtype_id :
    retr2.comp (TensorProduct.map galerkinTestSpan.subtype LinearMap.id) = LinearMap.id := by
  unfold retr2
  rw [← TensorProduct.map_comp, LinearMap.id_comp, projG_comp_subtype, TensorProduct.map_id]

private theorem retr3_tmul_span (v : L2Sigma) (s : galerkinTestSpan) :
    retr3 ((v : L2Sigma) ⊗ₜ[ℝ] (s : L2Sigma)) = v ⊗ₜ[ℝ] s := by
  unfold retr3
  rw [TensorProduct.map_tmul, LinearMap.id_apply, projG_subtype]

private theorem retr2_tmul_span (s : galerkinTestSpan) (v : L2Sigma) :
    retr2 ((s : L2Sigma) ⊗ₜ[ℝ] (v : L2Sigma)) = s ⊗ₜ[ℝ] v := by
  unfold retr2
  rw [TensorProduct.map_tmul, LinearMap.id_apply, projG_subtype]

/-! #### T4b — overlap agreement on `𝒢 ⊗ 𝒢` (scaffold) -/

/-- **`convBLTgalerkin_overlap` [scaffold].** For `s, s' ∈ 𝒢` and any `u`,
`convBLTgalerkin s' u (s : L2Sigma) = -convBLTgalerkin s u (s' : L2Sigma)`.

This is the torus analog of `convBLTspan_overlap`, following from `convFormFourier_antisymm_galerkinTest`
extended to all `u` by density, exactly as R3. -/
private theorem convBLTgalerkin_overlap (u : L2Sigma) (s s' : galerkinTestSpan) :
    convBLTgalerkin s' u (s : L2Sigma) = -convBLTgalerkin s u (s' : L2Sigma) := by
  sorry -- ALLOW_SORRY: PR-2 determined-form, prover discharges (torus #53)

private theorem edge_lift_agree_map (u : L2Sigma) :
    (edge2Lift u).comp (retr2.comp (TensorProduct.mapIncl galerkinTestSpan galerkinTestSpan))
      = (edge3Lift u).comp (retr3.comp (TensorProduct.mapIncl galerkinTestSpan galerkinTestSpan)) := by
  refine TensorProduct.ext' (fun a b => ?_)
  simp only [LinearMap.comp_apply]
  rw [TensorProduct.mapIncl, TensorProduct.map_tmul]
  show edge2Lift u (retr2 ((a : L2Sigma) ⊗ₜ[ℝ] (b : L2Sigma)))
    = edge3Lift u (retr3 ((a : L2Sigma) ⊗ₜ[ℝ] (b : L2Sigma)))
  unfold retr2 retr3
  rw [TensorProduct.map_tmul, TensorProduct.map_tmul, LinearMap.id_apply,
    LinearMap.id_apply, projG_subtype, projG_subtype, edge2Lift_tmul, edge3Lift_tmul,
    convBLTgalerkin_overlap u a b]

private theorem edge_lift_agree (u : L2Sigma)
    (z : TensorProduct ℝ galerkinTestSpan galerkinTestSpan) :
    edge2Lift u (retr2 (TensorProduct.mapIncl galerkinTestSpan galerkinTestSpan z))
      = edge3Lift u (retr3 (TensorProduct.mapIncl galerkinTestSpan galerkinTestSpan z)) := by
  exact LinearMap.congr_fun (edge_lift_agree_map u) z

/-! ### T5 — the edge partial maps, the `LinearPMap.sup` glue, `gInv`, and `detExtend` -/

private noncomputable def psi3 (u : L2Sigma) : edgeSlot3 →ₗ[ℝ] ℝ :=
  (edge3Lift u).comp (retr3.comp edgeSlot3.subtype)

private noncomputable def psi2 (u : L2Sigma) : edgeSlot2 →ₗ[ℝ] ℝ :=
  (edge2Lift u).comp (retr2.comp edgeSlot2.subtype)

private theorem psi3_apply (u : L2Sigma) (x : edgeSlot3) :
    psi3 u x = edge3Lift u (retr3 (x : TensorProduct ℝ L2Sigma L2Sigma)) := rfl

private theorem psi2_apply (u : L2Sigma) (x : edgeSlot2) :
    psi2 u x = edge2Lift u (retr2 (x : TensorProduct ℝ L2Sigma L2Sigma)) := rfl

private theorem psi3_add (u u' : L2Sigma) (x : edgeSlot3) :
    psi3 (u + u') x = psi3 u x + psi3 u' x := by
  rw [psi3_apply, psi3_apply, psi3_apply]
  exact edge3Lift_add u u' (retr3 (x : TensorProduct ℝ L2Sigma L2Sigma))

private theorem psi3_smul (c : ℝ) (u : L2Sigma) (x : edgeSlot3) :
    psi3 (c • u) x = c • psi3 u x := by
  rw [psi3_apply, psi3_apply]
  exact edge3Lift_smul c u (retr3 (x : TensorProduct ℝ L2Sigma L2Sigma))

private theorem psi2_add (u u' : L2Sigma) (x : edgeSlot2) :
    psi2 (u + u') x = psi2 u x + psi2 u' x := by
  rw [psi2_apply, psi2_apply, psi2_apply]
  exact edge2Lift_add u u' (retr2 (x : TensorProduct ℝ L2Sigma L2Sigma))

private theorem psi2_smul (c : ℝ) (u : L2Sigma) (x : edgeSlot2) :
    psi2 (c • u) x = c • psi2 u x := by
  rw [psi2_apply, psi2_apply]
  exact edge2Lift_smul c u (retr2 (x : TensorProduct ℝ L2Sigma L2Sigma))

private noncomputable def pmap3 (u : L2Sigma) :
    (TensorProduct ℝ L2Sigma L2Sigma) →ₗ.[ℝ] ℝ :=
  ⟨edgeSlot3, psi3 u⟩

private noncomputable def pmap2 (u : L2Sigma) :
    (TensorProduct ℝ L2Sigma L2Sigma) →ₗ.[ℝ] ℝ :=
  ⟨edgeSlot2, psi2 u⟩

private theorem psi_agree (u : L2Sigma)
    (x : (pmap2 u).domain) (y : (pmap3 u).domain)
    (hxy : (x : TensorProduct ℝ L2Sigma L2Sigma) = y) :
    (pmap2 u) x = (pmap3 u) y := by
  have hx2 : (x : TensorProduct ℝ L2Sigma L2Sigma) ∈ edgeSlot2 := x.2
  have hy3 : (x : TensorProduct ℝ L2Sigma L2Sigma) ∈ edgeSlot3 := hxy ▸ y.2
  have hmem : (x : TensorProduct ℝ L2Sigma L2Sigma) ∈ edgeSlot2 ⊓ edgeSlot3 := ⟨hx2, hy3⟩
  rw [edge_inf_eq_galerkin_tensor] at hmem
  obtain ⟨z, hz⟩ := hmem
  show psi2 u x = psi3 u y
  rw [psi2_apply, psi3_apply]
  rw [show (y : TensorProduct ℝ L2Sigma L2Sigma)
        = (x : TensorProduct ℝ L2Sigma L2Sigma) from hxy.symm, ← hz]
  exact edge_lift_agree u z

private noncomputable def psiSup (u : L2Sigma) :
    (TensorProduct ℝ L2Sigma L2Sigma) →ₗ.[ℝ] ℝ :=
  (pmap2 u).sup (pmap3 u) (psi_agree u)

private theorem psiSup_domain (u : L2Sigma) : (psiSup u).domain = detDomain := by
  unfold psiSup pmap2 pmap3 detDomain
  rw [LinearPMap.domain_sup]

/-! #### T5b — `gInv`, the fixed left inverse of `detDomain.subtype` -/

/-- The left-inverse existence statement, with the `ℝ`-semiring instance pinned to
`Real.semiring` (avoids the `DivisionRing.toSemiring` mismatch from `Classical.choose`). -/
private theorem detDomain_exists_leftInverse :
    ∃ g : (TensorProduct ℝ L2Sigma L2Sigma) →ₗ[ℝ] detDomain,
      g.comp detDomain.subtype = LinearMap.id := by
  letI : Semiring ℝ := inferInstance
  have h := LinearMap.exists_leftInverse_of_injective
    (K := ℝ) (V := detDomain) (V' := TensorProduct ℝ L2Sigma L2Sigma)
    detDomain.subtype (Submodule.ker_subtype detDomain)
  exact h

private noncomputable def gInv :
    (TensorProduct ℝ L2Sigma L2Sigma) →ₗ[ℝ] detDomain :=
  detDomain_exists_leftInverse.choose

private theorem gInv_subtype :
    gInv.comp detDomain.subtype = LinearMap.id :=
  detDomain_exists_leftInverse.choose_spec

private theorem gInv_eq_of_mem (x : TensorProduct ℝ L2Sigma L2Sigma)
    (hx : x ∈ detDomain) : gInv x = (⟨x, hx⟩ : detDomain) :=
  LinearMap.congr_fun gInv_subtype ⟨x, hx⟩

private theorem gInv_apply_mem (x : TensorProduct ℝ L2Sigma L2Sigma)
    (hx : x ∈ detDomain) : (gInv x : TensorProduct ℝ L2Sigma L2Sigma) = x := by
  rw [gInv_eq_of_mem x hx]

/-! #### T5c — `psiD` and its `u`-linearity -/

private noncomputable def psiD (u : L2Sigma) : detDomain →ₗ[ℝ] ℝ :=
  (psiSup u).toFun.comp
    (LinearEquiv.ofEq _ _ (psiSup_domain u).symm).toLinearMap

private theorem mem_psiSup_domain (u : L2Sigma)
    {x : TensorProduct ℝ L2Sigma L2Sigma} (hxD : x ∈ detDomain) :
    x ∈ (psiSup u).domain := by
  rw [psiSup_domain]; exact hxD

private theorem psiD_eq_psiSup (u : L2Sigma)
    (x : TensorProduct ℝ L2Sigma L2Sigma) (hxD : x ∈ detDomain) :
    psiD u ⟨x, hxD⟩ = (psiSup u) ⟨x, mem_psiSup_domain u hxD⟩ := rfl

private theorem psiD_apply_mem (u : L2Sigma)
    (x : TensorProduct ℝ L2Sigma L2Sigma) (hx2 : x ∈ edgeSlot2) (hxD : x ∈ detDomain) :
    psiD u ⟨x, hxD⟩ = psi2 u ⟨x, hx2⟩ := by
  rw [psiD_eq_psiSup u x hxD]
  obtain ⟨hdom, hval⟩ := LinearPMap.left_le_sup (pmap2 u) (pmap3 u) (psi_agree u)
  have h2 := hval (x := ⟨x, hx2⟩) (y := ⟨x, mem_psiSup_domain u hxD⟩) rfl
  exact h2.symm

private theorem psiD_apply_mem3 (u : L2Sigma)
    (x : TensorProduct ℝ L2Sigma L2Sigma) (hx3 : x ∈ edgeSlot3) (hxD : x ∈ detDomain) :
    psiD u ⟨x, hxD⟩ = psi3 u ⟨x, hx3⟩ := by
  rw [psiD_eq_psiSup u x hxD]
  obtain ⟨hdom, hval⟩ := LinearPMap.right_le_sup (pmap2 u) (pmap3 u) (psi_agree u)
  have h3 := hval (x := ⟨x, hx3⟩) (y := ⟨x, mem_psiSup_domain u hxD⟩) rfl
  exact h3.symm

private theorem psiD_add (u u' : L2Sigma) :
    psiD (u + u') = psiD u + psiD u' := by
  refine LinearMap.ext (fun z => ?_)
  obtain ⟨x, hx2, y, hy3, hxy⟩ := Submodule.mem_sup.mp (by rw [← detDomain]; exact z.2)
  have hzval : (z : TensorProduct ℝ L2Sigma L2Sigma) = x + y := hxy.symm
  have hxD : x ∈ detDomain := Submodule.mem_sup_left hx2
  have hyD : y ∈ detDomain := Submodule.mem_sup_right hy3
  have hsplit : z = (⟨x, hxD⟩ : detDomain) + (⟨y, hyD⟩ : detDomain) := by
    apply Subtype.ext; simpa using hzval
  rw [hsplit]
  simp only [map_add, LinearMap.add_apply,
    psiD_apply_mem u x hx2 hxD, psiD_apply_mem u' x hx2 hxD, psiD_apply_mem (u + u') x hx2 hxD,
    psiD_apply_mem3 u y hy3 hyD, psiD_apply_mem3 u' y hy3 hyD, psiD_apply_mem3 (u + u') y hy3 hyD,
    psi2_add u u' ⟨x, hx2⟩, psi3_add u u' ⟨y, hy3⟩]

private theorem psiD_smul (c : ℝ) (u : L2Sigma) :
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

/-! ### T6 — `antisymmetrizer` and `detExtend` -/

/-- The antisymmetrizer `A := (id − swap)/2` on `L²_σ ⊗ L²_σ`. -/
noncomputable def antisymmetrizer :
    TensorProduct ℝ L2Sigma L2Sigma →ₗ[ℝ] TensorProduct ℝ L2Sigma L2Sigma :=
  (2⁻¹ : ℝ) • (LinearMap.id - (TensorProduct.comm ℝ L2Sigma L2Sigma).toLinearMap)

private theorem antisymmetrizer_tmul (v w : L2Sigma) :
    antisymmetrizer (v ⊗ₜ[ℝ] w) = (2⁻¹ : ℝ) • (v ⊗ₜ[ℝ] w - w ⊗ₜ[ℝ] v) := by
  unfold antisymmetrizer
  simp [TensorProduct.comm_tmul]

private theorem antisymmetrizer_tmul_swap (v w : L2Sigma) :
    antisymmetrizer (w ⊗ₜ[ℝ] v) = -antisymmetrizer (v ⊗ₜ[ℝ] w) := by
  rw [antisymmetrizer_tmul, antisymmetrizer_tmul,
    ← neg_sub ((v : L2Sigma) ⊗ₜ[ℝ] w) (w ⊗ₜ[ℝ] v), smul_neg]

/-- **`detExtend` [proved from `psiD` / `gInv` / `antisymmetrizer`].** The determined
extension `L²_σ →ₗ (L²_σ ⊗ L²_σ) →ₗ ℝ`.

`detExtend u := (psiD u ∘ gInv) ∘ antisymmetrizer`. -/
noncomputable def detExtend :
    L2Sigma →ₗ[ℝ] (TensorProduct ℝ L2Sigma L2Sigma) →ₗ[ℝ] ℝ where
  toFun u := ((psiD u).comp gInv).comp antisymmetrizer
  map_add' u u' := by
    refine LinearMap.ext (fun z => ?_)
    simp only [LinearMap.comp_apply, LinearMap.add_apply]
    rw [psiD_add u u', LinearMap.add_apply]
  map_smul' c u := by
    refine LinearMap.ext (fun z => ?_)
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, RingHom.id_apply]
    rw [psiD_smul c u, LinearMap.smul_apply]

private theorem detExtend_add (u u' : L2Sigma)
    (z : TensorProduct ℝ L2Sigma L2Sigma) :
    detExtend (u + u') z = detExtend u z + detExtend u' z := by
  rw [detExtend.map_add u u', LinearMap.add_apply]

private theorem detExtend_smul (c : ℝ) (u : L2Sigma)
    (z : TensorProduct ℝ L2Sigma L2Sigma) :
    detExtend (c • u) z = c • detExtend u z := by
  rw [detExtend.map_smul c u, LinearMap.smul_apply]

/-! ### T7 — membership and retraction lemmas for the `edgeSlot` simple tensors -/

private theorem tmul_mem_edgeSlot3 (v : L2Sigma) (s : galerkinTestSpan) :
    (v : L2Sigma) ⊗ₜ[ℝ] (s : L2Sigma) ∈ edgeSlot3 :=
  ⟨v ⊗ₜ[ℝ] s, by rw [TensorProduct.map_tmul, LinearMap.id_apply, Submodule.coe_subtype]⟩

private theorem tmul_mem_edgeSlot2 (s : galerkinTestSpan) (v : L2Sigma) :
    (s : L2Sigma) ⊗ₜ[ℝ] (v : L2Sigma) ∈ edgeSlot2 :=
  ⟨s ⊗ₜ[ℝ] v, by rw [TensorProduct.map_tmul, LinearMap.id_apply, Submodule.coe_subtype]⟩

private theorem psiD_edge3_value (u v : L2Sigma) (s : galerkinTestSpan) :
    psiD u ⟨(v : L2Sigma) ⊗ₜ[ℝ] (s : L2Sigma),
        Submodule.mem_sup_right (tmul_mem_edgeSlot3 v s)⟩
      = convBLTgalerkin s u v := by
  rw [psiD_apply_mem3 u _ (tmul_mem_edgeSlot3 v s) (Submodule.mem_sup_right (tmul_mem_edgeSlot3 v s)),
    psi3_apply]
  show edge3Lift u (retr3 ((v : L2Sigma) ⊗ₜ[ℝ] (s : L2Sigma))) = convBLTgalerkin s u v
  rw [retr3_tmul_span v s, edge3Lift_tmul]

private theorem psiD_edge2_value (u v : L2Sigma) (s : galerkinTestSpan) :
    psiD u ⟨(s : L2Sigma) ⊗ₜ[ℝ] (v : L2Sigma),
        Submodule.mem_sup_left (tmul_mem_edgeSlot2 s v)⟩
      = -(convBLTgalerkin s u v) := by
  rw [psiD_apply_mem u _ (tmul_mem_edgeSlot2 s v) (Submodule.mem_sup_left (tmul_mem_edgeSlot2 s v)),
    psi2_apply]
  show edge2Lift u (retr2 ((s : L2Sigma) ⊗ₜ[ℝ] (v : L2Sigma))) = -(convBLTgalerkin s u v)
  rw [retr2_tmul_span s v, edge2Lift_tmul]

/-! ### T8 — `convFormL2_def` and its properties -/

/-- **`convFormL2_def` (`b`) [proved given scaffold].** The determined trilinear convection
form:

`b u v w := detExtend u (v ⊗ₜ w)`. -/
noncomputable def convFormL2_def (u v w : L2Sigma) : ℝ :=
  detExtend u (v ⊗ₜ[ℝ] w)

@[simp]
theorem convFormL2_def_eq (u v w : L2Sigma) :
    convFormL2_def u v w = detExtend u (v ⊗ₜ[ℝ] w) :=
  rfl

/-- **`convFormL2_antisymm` [proved from `antisymmetrizer_tmul_swap`].**
`b u v w = − b u w v` for all `u v w`. -/
theorem convFormL2_antisymm (u v w : L2Sigma) :
    convFormL2_def u v w = -convFormL2_def u w v := by
  rw [convFormL2_def_eq, convFormL2_def_eq]
  show ((psiD u).comp gInv).comp antisymmetrizer (v ⊗ₜ[ℝ] w)
    = -(((psiD u).comp gInv).comp antisymmetrizer (w ⊗ₜ[ℝ] v))
  rw [LinearMap.comp_apply, LinearMap.comp_apply (g := antisymmetrizer),
    antisymmetrizer_tmul_swap v w, map_neg, neg_neg]

/-- **`convFormL2_multilinear` [proved from `detExtend` linearity].** There exists a genuine
ℝ-trilinear map `B` with `b u v w = B u v w`. -/
theorem convFormL2_multilinear :
    ∃ B : L2Sigma →ₗ[ℝ] L2Sigma →ₗ[ℝ] L2Sigma →ₗ[ℝ] ℝ,
      ∀ (u v w : L2Sigma), convFormL2_def u v w = B u v w := by
  refine ⟨{
    toFun := fun u =>
      LinearMap.compr₂ (TensorProduct.mk ℝ L2Sigma L2Sigma) (detExtend u)
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

/-- **`convFormL2_cont_fixedTest` [scaffold].** For a Galerkin test `w`,
`(u, v) ↦ b u v w` is jointly L²-continuous.

PR-2 prover obligation: use `detExtend_on_edgeSlot3` (the slot-3 edge determination)
to identify `b u v w = convBLTgalerkin w u v`, then continuity follows from the CLM structure. -/
theorem convFormL2_cont_fixedTest (w : L2Sigma) (hw : IsGalerkinTest w) :
    Continuous (fun p : L2Sigma × L2Sigma => convFormL2_def p.1 p.2 w) := by
  sorry -- ALLOW_SORRY: PR-2 determined-form, prover discharges (torus #53)

/-- **`convFormL2_bound_galerkinTest` [scaffold].** For Galerkin tests `u, v, w`,
`|b u v w| ≤ C(w) · ‖u‖ · ‖v‖` for some `C(w) ≥ 0`.

PR-2 prover obligation: transfer the bilinear bound from `convBLTgalerkin` (which
is built from `galerkinConvection_bound` / `convSummand_summable`). -/
theorem convFormL2_bound_galerkinTest (w : L2Sigma) (hw : IsGalerkinTest w) :
    ∃ C : ℝ, ∀ (u v : L2Sigma), IsGalerkinTest u → IsGalerkinTest v →
      |convFormL2_def u v w| ≤ C * ‖(u : L2VF)‖ * ‖(v : L2VF)‖ := by
  sorry -- ALLOW_SORRY: PR-2 determined-form, prover discharges (torus #53)

/-- **`convFormL2_galerkin_pin` [scaffold].** On Galerkin subspaces `Vₙ`,
`b` restricts to the finite box-truncated form `galerkinConvection n`.

PR-2 prover obligation: follow from `convFormFourier` matching `galerkinConvection` on
the finite box plus the determination identity on the Galerkin-test slice. -/
theorem convFormL2_galerkin_pin :
    ∀ (n : ℕ) (u v w : L2Sigma),
      velocityProjection_n n (u : L2VF) = (u : L2VF) →
      velocityProjection_n n (v : L2VF) = (v : L2VF) →
      velocityProjection_n n (w : L2VF) = (w : L2VF) →
      convFormL2_def u v w = galerkinConvection n (u : L2VF) (v : L2VF) (w : L2VF) := by
  sorry -- ALLOW_SORRY: PR-2 determined-form, prover discharges (torus #53)

/-- **`convFormL2_galerkinTest_dense` [proved sorry-free].** Every `u : L2Sigma` is an
L²-limit of Galerkin tests.

Proof: `velocityProjection_n n u → u` by `velocityProjection_n_tendsto`; each
`velocityProjection_n n u` is a Galerkin test by definition of `IsGalerkinTest`. -/
theorem convFormL2_galerkinTest_dense (u : L2Sigma) :
    ∃ s : ℕ → L2Sigma, (∀ n, IsGalerkinTest (s n)) ∧
      Filter.Tendsto s Filter.atTop (nhds u) := by
  -- The approximating sequence is the Galerkin projection of `u`, re-typed into `L2Sigma`
  -- (it is div-free by `velocityProjection_n_preserves_L2Sigma`).
  refine ⟨fun n => ⟨velocityProjection_n n (u : L2VF),
      velocityProjection_n_preserves_L2Sigma n (u : L2VF) u.2⟩, fun n => ?_, ?_⟩
  · -- `IsGalerkinTest`: the projection is fixed by `velocityProjection_n n` (idempotence).
    exact ⟨n, velocityProjection_n_idem n (u : L2VF)⟩
  · -- Convergence in `L2Sigma` ↔ convergence of the coercions in `L2VF`
    -- (`tendsto_subtype_rng`), which is `velocityProjection_n_tendsto`.
    rw [tendsto_subtype_rng]
    exact velocityProjection_n_tendsto (u : L2VF)

/-! ### T9 — `torusConvectionGap_holds` : assemble the 7 `TorusConvectionGap` fields -/

/-- **`torusConvectionGap_holds` [scaffold — 5 of 7 fields scaffold-sorry].** Assembly of
the `TorusConvectionGap` structure from the determined-form construction.

Proved sorry-free: `b_multilinear`, `b_antisymm_gap` (from `detExtend`).
Scaffold-sorry (PR-2 prover targets): `b_galerkin_pin`, `b_bound_test`, `b_cont_fixedTest`,
`galerkinTest_dense`. -/
theorem torusConvectionGap_holds : Nonempty TorusConvectionGap :=
  ⟨{ b              := convFormL2_def
     b_galerkin_pin  := convFormL2_galerkin_pin
     b_multilinear   := convFormL2_multilinear
     b_antisymm_gap  := convFormL2_antisymm
     b_bound_test    := convFormL2_bound_galerkinTest
     b_cont_fixedTest := convFormL2_cont_fixedTest
     galerkinTest_dense := convFormL2_galerkinTest_dense }⟩

end LerayHopf.TorusConvectionExtension

namespace LerayHopf

/-- **Torus weak-convection operator gap — proved via the determined form (torus #53).**
Re-exports `TorusConvectionExtension.torusConvectionGap_holds` as a proof of
`Nonempty TorusConvectionGap`, contributing to the discharge of `torusConvectionGap_exists`. -/
theorem torusConvectionGap_holds_thm : Nonempty TorusConvectionGap :=
  LerayHopf.TorusConvectionExtension.torusConvectionGap_holds

end LerayHopf
