import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.LinearAlgebra.LinearPMap
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Analysis.Normed.Operator.Basic
import LerayHopf.Analysis.TensorIntersection

/-!
# TensorEdgeGluing — shared tensor/edge-gluing layer (issue #111, PR-1)

**File:** `LerayHopf/Analysis/TensorEdgeGluing.lean`

## What this file is

The R3 and Torus convection-form constructions (`LerayHopf/R3/ConvectionExtension.lean`,
`LerayHopf/Torus/ConvectionExtension.lean`) each build a determined antisymmetric bilinear
form on `L²_σ ⊗ L²_σ` by gluing two "edge" prescriptions on `𝒮 ⊗ L²_σ` and `L²_σ ⊗ 𝒮` (for
R3's Schwartz span `𝒮`, Torus's Galerkin-test span `𝒢`) that agree on the overlap `𝒮 ⊗ 𝒮`.
That gluing machinery — tensor edge submodules, the `TensorProduct.lift`-based edge
bilinears, the retraction/left-inverse infrastructure, `LinearPMap.sup`, the antisymmetrizer,
and the resulting `detExtend`/`convFormL2_def` tower — is generic multilinear/Hamel-extension
glue over (a real normed space `X`, a "edge" submodule `EdgeSpan ≤ X`, and a bounded bilinear
map `BLTLin` linear over `EdgeSpan`).  It does not depend on anything Galerkin/NS-specific.
This file extracts that shared layer once; both lanes instantiate it (R3 at
`(L2Sigma_R3, schwartzSpan, convBLTspan_lin, convBLTspan_overlap)`, Torus at
`(L2Sigma, galerkinTestSpan, convBLTgalerkinLin, convBLTgalerkin_overlap)`).

## Parametrization

- `X` — a real normed space (`NormedAddCommGroup X`, `NormedSpace ℝ X`).
- `EdgeSpan : Submodule ℝ X` — the "edge" submodule (R3: `schwartzSpan`; Torus:
  `galerkinTestSpan`).
- `BLTLin : EdgeSpan →ₗ[ℝ] (X →L[ℝ] X →L[ℝ] ℝ)` — the jointly continuous bilinear
  extension, packaged linearly in the edge slot (R3: `convBLTspanLin`; Torus:
  `convBLTgalerkinLin`).
- `BLT_overlap` — the overlap-antisymmetry hypothesis
  `∀ u (s s' : EdgeSpan), BLTLin s' u (s : X) = -(BLTLin s u (s' : X))` (R3:
  `convBLTspan_overlap`; Torus: `convBLTgalerkin_overlap`).

`BLTLin` already bundles the linearities that the two per-lane files used to name
separately (`convBLTspan_add`/`_smul`/`_u_add`/`_u_smul`): additivity/homogeneity in the
edge slot is `BLTLin.map_add`/`BLTLin.map_smul`, additivity/homogeneity in the `X`-slots is
`(BLTLin s).map_add`/`(BLTLin s).map_smul` (each `BLTLin s` is already a
`ContinuousLinearMap`).  Only `BLT_overlap` needs to be supplied as a genuine hypothesis.

## What moved here vs what stays per-lane

Moved (this file, generic): the two tensor edge submodules `edgeSlot2`/`edgeSlot3`, the
determined domain `detDomain`, the `TensorProduct.lift`-based edge bilinears and their
`u`-linear bundles, the retraction/left-inverse infrastructure, the `LinearPMap.sup` glue
(`psi2`/`psi3`/`psiSup`/`psiD`), the fixed left inverse `gInv`, the antisymmetrizer, and the
resulting `detExtend`/`convFormL2_def` tower with its multilinearity/antisymmetry.

Stays per-lane: the construction of `BLTLin` itself (`convBLTspan`/`convBLTgalerkin`, built
from lane-specific H¹/Fourier analysis), the proof of `BLT_overlap`
(`convBLTspan_overlap`/`convBLTgalerkin_overlap`), the tensor-intersection identity's local
name (`edge_inf_eq_schwartz_tensor`/`edge_inf_eq_galerkin_tensor` — same content, inlined
here from `TensorIntersection` and re-exposed per lane under the lane's own name), and
`convFormL2_cont_fixedTest` (the CRUX 5th field: same statement, genuinely different proof
per lane — R3 routes through `detExtend_edge3_eq` + `convBLT_fixedTest`'s
`isBoundedBilinearMap.continuous`, Torus through `convBLTw`'s `continuous₂`).

## The new generic corollary

`detExtend_edge3_eq` packages the algebraic core both lanes' `convFormL2_cont_fixedTest`
proofs need: on the slot-3 edge, `detExtend u (v ⊗ₜ (w : X)) = BLTLin w u v` for ALL `u v` —
the determined value, not a Hamel value.  Each lane derives its old
`detExtend_on_edgeSlot3`/`convFormL2_def_eq_convValW` bridge lemma from this in one line.

## Mathlib declarations consumed

- `TensorProduct.map`, `TensorProduct.mapIncl`, `TensorProduct.lift`, `TensorProduct.mk`,
  `TensorProduct.uncurry` (`LinearAlgebra/TensorProduct/{Basic,Map}.lean`).
- `LerayHopf.R3.TensorIntersection.range_map_subtype_inf_range_map_subtype` — generic
  (`Field K`, `Module K V`) tensor-intersection identity `(S⊗V) ⊓ (V⊗S) = S⊗S`; consumed
  directly (not itself Galerkin/NS-specific).
- `LinearPMap.sup` / `LinearPMap.sup_apply`, `LinearPMap.left_le_sup`,
  `LinearPMap.right_le_sup` (`LinearAlgebra/LinearPMap.lean`).
- `Submodule.exists_isCompl`, `Submodule.projectionOnto` — a fixed algebraic complement of
  `EdgeSpan` and its projection (`LinearAlgebra/Basis/VectorSpace.lean`).
- `LinearMap.exists_leftInverse_of_injective` — the fixed left inverse `gInv` of
  `detDomain.subtype`.  Instance trap: `Classical.choose` yields
  `DivisionRing.toDivisionSemiring.toSemiring ℝ` vs `Real.semiring`; fixed with
  `letI : Semiring ℝ := inferInstance`.

`Mathlib.Analysis.Normed.Operator.Basic` is imported beyond the architect-specified three:
`NormedAddCommGroup`/`NormedSpace`/`ContinuousLinearMap` (hence the `X →L[ℝ] X →L[ℝ] ℝ`
type of `BLTLin`, and the `evalBil` functional) are defined in `Mathlib.Analysis.*`, not
under `Mathlib.LinearAlgebra.*`; without it the module parametrization does not parse.
-/

open TensorProduct

namespace LerayHopf.TensorEdgeGluing

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable (EdgeSpan : Submodule ℝ X)
variable (BLTLin : EdgeSpan →ₗ[ℝ] (X →L[ℝ] X →L[ℝ] ℝ))
variable (BLT_overlap : ∀ u : X, ∀ s s' : EdgeSpan, BLTLin s' u (s : X) = -(BLTLin s u (s' : X)))

/-! ### The two edge submodules and the determined domain -/

/-- The "slot-2 edge" submodule `EdgeSpan ⊗ X ≤ X ⊗ X`. -/
noncomputable def edgeSlot2 : Submodule ℝ (TensorProduct ℝ X X) :=
  LinearMap.range (TensorProduct.map EdgeSpan.subtype (LinearMap.id : X →ₗ[ℝ] X))

/-- The "slot-3 edge" submodule `X ⊗ EdgeSpan ≤ X ⊗ X`. -/
noncomputable def edgeSlot3 : Submodule ℝ (TensorProduct ℝ X X) :=
  LinearMap.range (TensorProduct.map (LinearMap.id : X →ₗ[ℝ] X) EdgeSpan.subtype)

/-- **The determined domain.** `detDomain := (EdgeSpan ⊗ X) + (X ⊗ EdgeSpan)`. -/
noncomputable def detDomain : Submodule ℝ (TensorProduct ℝ X X) :=
  edgeSlot2 EdgeSpan ⊔ edgeSlot3 EdgeSpan

/-! ### The evaluation functional and the two edge bilinears -/

/-- The `ℝ`-linear evaluation `B ↦ B u v` on continuous bilinear forms. -/
private noncomputable def evalBil (u v : X) :
    (X →L[ℝ] X →L[ℝ] ℝ) →ₗ[ℝ] ℝ where
  toFun B := B u v
  map_add' B B' := by simp
  map_smul' c B := by simp

/-- The slot-3 determined value as a linear functional in the edge factor:
`s ↦ BLTLin s u v`. -/
private noncomputable def edge3Sval (u v : X) : EdgeSpan →ₗ[ℝ] ℝ :=
  (evalBil u v).comp (BLTLin)

@[simp]
private theorem edge3Sval_apply (u v : X) (s : EdgeSpan) :
    edge3Sval EdgeSpan BLTLin u v s = BLTLin s u v := by
  unfold edge3Sval; rfl

/-- The slot-3 edge bilinear `b3 u : X →ₗ EdgeSpan →ₗ ℝ`, `b3 u v s = BLTLin s u v`. -/
private noncomputable def edge3Bil (u : X) :
    X →ₗ[ℝ] EdgeSpan →ₗ[ℝ] ℝ where
  toFun v := edge3Sval EdgeSpan BLTLin u v
  map_add' v v' := by
    refine LinearMap.ext (fun s => ?_)
    simp [edge3Sval_apply, LinearMap.add_apply, map_add]
  map_smul' c v := by
    refine LinearMap.ext (fun s => ?_)
    simp [edge3Sval_apply, LinearMap.smul_apply, map_smul]

@[simp]
private theorem edge3Bil_apply (u v : X) (s : EdgeSpan) :
    edge3Bil EdgeSpan BLTLin u v s = BLTLin s u v :=
  edge3Sval_apply EdgeSpan BLTLin u v s

/-- The slot-2 determined value as a linear functional in the rough factor:
`l ↦ -BLTLin s u l`. -/
private noncomputable def edge2Lval (u : X) (s : EdgeSpan) :
    X →ₗ[ℝ] ℝ :=
  -(BLTLin s u).toLinearMap

@[simp]
private theorem edge2Lval_apply (u : X) (s : EdgeSpan) (l : X) :
    edge2Lval EdgeSpan BLTLin u s l = -(BLTLin s u l) := rfl

/-- The slot-2 edge bilinear `b2 u : EdgeSpan →ₗ X →ₗ ℝ`, `b2 u s l = -BLTLin s u l`. -/
private noncomputable def edge2Bil (u : X) :
    EdgeSpan →ₗ[ℝ] X →ₗ[ℝ] ℝ where
  toFun s := edge2Lval EdgeSpan BLTLin u s
  map_add' s s' := by
    refine LinearMap.ext (fun l => ?_)
    have h : BLTLin (s + s') = BLTLin s + BLTLin s' := BLTLin.map_add s s'
    simp only [edge2Lval_apply, LinearMap.add_apply, h,
      ContinuousLinearMap.add_apply, neg_add]
  map_smul' c s := by
    refine LinearMap.ext (fun l => ?_)
    have h : BLTLin (c • s) = c • BLTLin s := BLTLin.map_smul c s
    simp only [edge2Lval_apply, LinearMap.smul_apply, h,
      ContinuousLinearMap.smul_apply, smul_eq_mul, RingHom.id_apply, mul_neg]

@[simp]
private theorem edge2Bil_apply (u : X) (s : EdgeSpan) (l : X) :
    edge2Bil EdgeSpan BLTLin u s l = -(BLTLin s u l) :=
  edge2Lval_apply EdgeSpan BLTLin u s l

/-- The slot-3 edge bilinear bundled **linearly in `u`**. -/
private noncomputable def edge3BilL :
    X →ₗ[ℝ] (X →ₗ[ℝ] EdgeSpan →ₗ[ℝ] ℝ) where
  toFun := edge3Bil EdgeSpan BLTLin
  map_add' u u' := by
    refine LinearMap.ext (fun v => LinearMap.ext (fun s => ?_))
    have h : BLTLin s (u + u') = BLTLin s u + BLTLin s u' := (BLTLin s).map_add u u'
    simp only [edge3Bil_apply, LinearMap.add_apply, h, ContinuousLinearMap.add_apply]
  map_smul' c u := by
    refine LinearMap.ext (fun v => LinearMap.ext (fun s => ?_))
    have h : BLTLin s (c • u) = c • BLTLin s u := (BLTLin s).map_smul c u
    simp only [edge3Bil_apply, LinearMap.smul_apply, RingHom.id_apply, h,
      ContinuousLinearMap.smul_apply, smul_eq_mul]

/-- The slot-2 edge bilinear bundled **linearly in `u`**. -/
private noncomputable def edge2BilL :
    X →ₗ[ℝ] (EdgeSpan →ₗ[ℝ] X →ₗ[ℝ] ℝ) where
  toFun := edge2Bil EdgeSpan BLTLin
  map_add' u u' := by
    refine LinearMap.ext (fun s => LinearMap.ext (fun l => ?_))
    have h : BLTLin s (u + u') = BLTLin s u + BLTLin s u' := (BLTLin s).map_add u u'
    simp only [edge2Bil_apply, LinearMap.add_apply, h,
      ContinuousLinearMap.add_apply, neg_add]
  map_smul' c u := by
    refine LinearMap.ext (fun s => LinearMap.ext (fun l => ?_))
    have h : BLTLin s (c • u) = c • BLTLin s u := (BLTLin s).map_smul c u
    simp only [edge2Bil_apply, LinearMap.smul_apply, RingHom.id_apply, h,
      ContinuousLinearMap.smul_apply, smul_eq_mul, mul_neg]

/-- The slot-3 lift `lift3 : X →ₗ ((X ⊗ EdgeSpan) →ₗ ℝ)` (linear in `u`). -/
private noncomputable def edge3LiftL :
    X →ₗ[ℝ] (TensorProduct ℝ X EdgeSpan →ₗ[ℝ] ℝ) :=
  (TensorProduct.uncurry (RingHom.id ℝ) X EdgeSpan ℝ).comp (edge3BilL EdgeSpan BLTLin)

/-- The slot-2 lift `lift2 : X →ₗ ((EdgeSpan ⊗ X) →ₗ ℝ)` (linear in `u`). -/
private noncomputable def edge2LiftL :
    X →ₗ[ℝ] (TensorProduct ℝ EdgeSpan X →ₗ[ℝ] ℝ) :=
  (TensorProduct.uncurry (RingHom.id ℝ) EdgeSpan X ℝ).comp (edge2BilL EdgeSpan BLTLin)

/-- The slot-3 lift `lift3 u : (X ⊗ EdgeSpan) →ₗ ℝ`. -/
private noncomputable def edge3Lift (u : X) :
    TensorProduct ℝ X EdgeSpan →ₗ[ℝ] ℝ :=
  edge3LiftL EdgeSpan BLTLin u

/-- The slot-2 lift `lift2 u : (EdgeSpan ⊗ X) →ₗ ℝ`. -/
private noncomputable def edge2Lift (u : X) :
    TensorProduct ℝ EdgeSpan X →ₗ[ℝ] ℝ :=
  edge2LiftL EdgeSpan BLTLin u

@[simp]
private theorem edge3Lift_tmul (u v : X) (s : EdgeSpan) :
    edge3Lift EdgeSpan BLTLin u (v ⊗ₜ[ℝ] s) = BLTLin s u v := by
  show edge3LiftL EdgeSpan BLTLin u (v ⊗ₜ[ℝ] s) = BLTLin s u v
  unfold edge3LiftL
  rw [LinearMap.comp_apply, TensorProduct.uncurry_apply]
  exact edge3Bil_apply EdgeSpan BLTLin u v s

@[simp]
private theorem edge2Lift_tmul (u : X) (s : EdgeSpan) (l : X) :
    edge2Lift EdgeSpan BLTLin u (s ⊗ₜ[ℝ] l) = -(BLTLin s u l) := by
  show edge2LiftL EdgeSpan BLTLin u (s ⊗ₜ[ℝ] l) = -(BLTLin s u l)
  unfold edge2LiftL
  rw [LinearMap.comp_apply, TensorProduct.uncurry_apply]
  exact edge2Bil_apply EdgeSpan BLTLin u s l

private theorem edge3Lift_add (u u' : X) (z : TensorProduct ℝ X EdgeSpan) :
    edge3Lift EdgeSpan BLTLin (u + u') z
      = edge3Lift EdgeSpan BLTLin u z + edge3Lift EdgeSpan BLTLin u' z := by
  show edge3LiftL EdgeSpan BLTLin (u + u') z
      = edge3LiftL EdgeSpan BLTLin u z + edge3LiftL EdgeSpan BLTLin u' z
  rw [map_add]; rfl

private theorem edge3Lift_smul (c : ℝ) (u : X)
    (z : TensorProduct ℝ X EdgeSpan) :
    edge3Lift EdgeSpan BLTLin (c • u) z = c • edge3Lift EdgeSpan BLTLin u z := by
  show edge3LiftL EdgeSpan BLTLin (c • u) z = c • edge3LiftL EdgeSpan BLTLin u z
  rw [map_smul]; rfl

private theorem edge2Lift_add (u u' : X) (z : TensorProduct ℝ EdgeSpan X) :
    edge2Lift EdgeSpan BLTLin (u + u') z
      = edge2Lift EdgeSpan BLTLin u z + edge2Lift EdgeSpan BLTLin u' z := by
  show edge2LiftL EdgeSpan BLTLin (u + u') z
      = edge2LiftL EdgeSpan BLTLin u z + edge2LiftL EdgeSpan BLTLin u' z
  rw [map_add]; rfl

private theorem edge2Lift_smul (c : ℝ) (u : X)
    (z : TensorProduct ℝ EdgeSpan X) :
    edge2Lift EdgeSpan BLTLin (c • u) z = c • edge2Lift EdgeSpan BLTLin u z := by
  show edge2LiftL EdgeSpan BLTLin (c • u) z = c • edge2LiftL EdgeSpan BLTLin u z
  rw [map_smul]; rfl

attribute [irreducible] edge3Lift edge2Lift

/-! ### A fixed algebraic complement of `EdgeSpan` and its projection -/

/-- A complement of `EdgeSpan` and its data. -/
private noncomputable def edgeCompl : Submodule ℝ X :=
  (EdgeSpan.exists_isCompl).choose

private theorem edgeCompl_isCompl : IsCompl EdgeSpan (edgeCompl EdgeSpan) :=
  (EdgeSpan.exists_isCompl).choose_spec

/-- The projection `X →ₗ EdgeSpan` (left inverse of `EdgeSpan.subtype`). -/
private noncomputable def projE : X →ₗ[ℝ] EdgeSpan :=
  EdgeSpan.projectionOnto (edgeCompl EdgeSpan) (edgeCompl_isCompl EdgeSpan)

@[simp]
private theorem projE_subtype (s : EdgeSpan) : projE EdgeSpan (s : X) = s :=
  Submodule.projectionOnto_apply_left (edgeCompl_isCompl EdgeSpan) s

private theorem projE_comp_subtype :
    (projE EdgeSpan).comp EdgeSpan.subtype = LinearMap.id := by
  refine LinearMap.ext (fun s => ?_)
  simp [projE_subtype]

/-- Slot-3 retraction `retr3 : (X ⊗ X) →ₗ (X ⊗ EdgeSpan)`. -/
private noncomputable def retr3 :
    TensorProduct ℝ X X →ₗ[ℝ] TensorProduct ℝ X EdgeSpan :=
  TensorProduct.map LinearMap.id (projE EdgeSpan)

/-- Slot-2 retraction `retr2 : (X ⊗ X) →ₗ (EdgeSpan ⊗ X)`. -/
private noncomputable def retr2 :
    TensorProduct ℝ X X →ₗ[ℝ] TensorProduct ℝ EdgeSpan X :=
  TensorProduct.map (projE EdgeSpan) LinearMap.id

/-- `retr3` inverts `map id subtype` on `X ⊗ EdgeSpan`. -/
private theorem retr3_map_id_subtype :
    (retr3 EdgeSpan).comp (TensorProduct.map LinearMap.id EdgeSpan.subtype) = LinearMap.id := by
  unfold retr3
  rw [← TensorProduct.map_comp, LinearMap.id_comp, projE_comp_subtype, TensorProduct.map_id]

/-- `retr2` inverts `map subtype id` on `EdgeSpan ⊗ X`. -/
private theorem retr2_map_subtype_id :
    (retr2 EdgeSpan).comp (TensorProduct.map EdgeSpan.subtype LinearMap.id) = LinearMap.id := by
  unfold retr2
  rw [← TensorProduct.map_comp, LinearMap.id_comp, projE_comp_subtype, TensorProduct.map_id]

/-! ### The overlap agreement and the glued map `Ψ u` -/

include BLT_overlap in
/-- The two edge prescriptions, composed with the retractions and `mapIncl`, are **equal
as linear maps** on `EdgeSpan ⊗ EdgeSpan` (`TensorProduct.ext'`, tmul case = `BLT_overlap`). -/
private theorem edge_lift_agree_map (u : X) :
    (edge2Lift EdgeSpan BLTLin u).comp
        ((retr2 EdgeSpan).comp (TensorProduct.mapIncl EdgeSpan EdgeSpan))
      = (edge3Lift EdgeSpan BLTLin u).comp
          ((retr3 EdgeSpan).comp (TensorProduct.mapIncl EdgeSpan EdgeSpan)) := by
  refine TensorProduct.ext' (fun a b => ?_)
  simp only [LinearMap.comp_apply]
  rw [TensorProduct.mapIncl, TensorProduct.map_tmul]
  show edge2Lift EdgeSpan BLTLin u (retr2 EdgeSpan ((a : X) ⊗ₜ[ℝ] (b : X)))
    = edge3Lift EdgeSpan BLTLin u (retr3 EdgeSpan ((a : X) ⊗ₜ[ℝ] (b : X)))
  unfold retr2 retr3
  rw [TensorProduct.map_tmul, TensorProduct.map_tmul, LinearMap.id_apply,
    LinearMap.id_apply, projE_subtype, projE_subtype, edge2Lift_tmul, edge3Lift_tmul,
    BLT_overlap u a b]

include BLT_overlap in
/-- The two edge prescriptions agree on the image of `EdgeSpan ⊗ EdgeSpan` under `mapIncl`. -/
private theorem edge_lift_agree (u : X)
    (z : TensorProduct ℝ EdgeSpan EdgeSpan) :
    edge2Lift EdgeSpan BLTLin u (retr2 EdgeSpan (TensorProduct.mapIncl EdgeSpan EdgeSpan z))
      = edge3Lift EdgeSpan BLTLin u (retr3 EdgeSpan (TensorProduct.mapIncl EdgeSpan EdgeSpan z)) := by
  have := LinearMap.congr_fun (edge_lift_agree_map EdgeSpan BLTLin BLT_overlap u) z
  simpa only [LinearMap.comp_apply] using this

/-- The slot-3 edge functional on `edgeSlot3`: `Ψ3 u (T₃ y) = edge3Lift u y`. -/
private noncomputable def psi3 (u : X) : edgeSlot3 EdgeSpan →ₗ[ℝ] ℝ :=
  (edge3Lift EdgeSpan BLTLin u).comp ((retr3 EdgeSpan).comp (edgeSlot3 EdgeSpan).subtype)

/-- The slot-2 edge functional on `edgeSlot2`: `Ψ2 u (T₂ y) = edge2Lift u y`. -/
private noncomputable def psi2 (u : X) : edgeSlot2 EdgeSpan →ₗ[ℝ] ℝ :=
  (edge2Lift EdgeSpan BLTLin u).comp ((retr2 EdgeSpan).comp (edgeSlot2 EdgeSpan).subtype)

private theorem psi3_apply (u : X) (x : edgeSlot3 EdgeSpan) :
    psi3 EdgeSpan BLTLin u x
      = edge3Lift EdgeSpan BLTLin u (retr3 EdgeSpan (x : TensorProduct ℝ X X)) := rfl

private theorem psi2_apply (u : X) (x : edgeSlot2 EdgeSpan) :
    psi2 EdgeSpan BLTLin u x
      = edge2Lift EdgeSpan BLTLin u (retr2 EdgeSpan (x : TensorProduct ℝ X X)) := rfl

private theorem psi3_add (u u' : X) (x : edgeSlot3 EdgeSpan) :
    psi3 EdgeSpan BLTLin (u + u') x = psi3 EdgeSpan BLTLin u x + psi3 EdgeSpan BLTLin u' x := by
  rw [psi3_apply, psi3_apply, psi3_apply]
  exact edge3Lift_add EdgeSpan BLTLin u u' (retr3 EdgeSpan (x : TensorProduct ℝ X X))

private theorem psi3_smul (c : ℝ) (u : X) (x : edgeSlot3 EdgeSpan) :
    psi3 EdgeSpan BLTLin (c • u) x = c • psi3 EdgeSpan BLTLin u x := by
  rw [psi3_apply, psi3_apply]
  exact edge3Lift_smul EdgeSpan BLTLin c u (retr3 EdgeSpan (x : TensorProduct ℝ X X))

private theorem psi2_add (u u' : X) (x : edgeSlot2 EdgeSpan) :
    psi2 EdgeSpan BLTLin (u + u') x = psi2 EdgeSpan BLTLin u x + psi2 EdgeSpan BLTLin u' x := by
  rw [psi2_apply, psi2_apply, psi2_apply]
  exact edge2Lift_add EdgeSpan BLTLin u u' (retr2 EdgeSpan (x : TensorProduct ℝ X X))

private theorem psi2_smul (c : ℝ) (u : X) (x : edgeSlot2 EdgeSpan) :
    psi2 EdgeSpan BLTLin (c • u) x = c • psi2 EdgeSpan BLTLin u x := by
  rw [psi2_apply, psi2_apply]
  exact edge2Lift_smul EdgeSpan BLTLin c u (retr2 EdgeSpan (x : TensorProduct ℝ X X))

/-- The two edge functionals as `LinearPMap`s on `X ⊗ X`. -/
private noncomputable def pmap3 (u : X) :
    (TensorProduct ℝ X X) →ₗ.[ℝ] ℝ :=
  ⟨edgeSlot3 EdgeSpan, psi3 EdgeSpan BLTLin u⟩

private noncomputable def pmap2 (u : X) :
    (TensorProduct ℝ X X) →ₗ.[ℝ] ℝ :=
  ⟨edgeSlot2 EdgeSpan, psi2 EdgeSpan BLTLin u⟩

include BLT_overlap in
/-- **The sup-glue agreement.** `Ψ2 u` and `Ψ3 u` agree where their underlying tensors
coincide (necessarily in `EdgeSpan ⊗ EdgeSpan`, via
`TensorIntersection.range_map_subtype_inf_range_map_subtype`). -/
private theorem psi_agree (u : X)
    (x : (pmap2 EdgeSpan BLTLin u).domain) (y : (pmap3 EdgeSpan BLTLin u).domain)
    (hxy : (x : TensorProduct ℝ X X) = y) :
    (pmap2 EdgeSpan BLTLin u) x = (pmap3 EdgeSpan BLTLin u) y := by
  have hx2 : (x : TensorProduct ℝ X X) ∈ edgeSlot2 EdgeSpan := x.2
  have hy3 : (x : TensorProduct ℝ X X) ∈ edgeSlot3 EdgeSpan := hxy ▸ y.2
  have hmem : (x : TensorProduct ℝ X X) ∈ edgeSlot2 EdgeSpan ⊓ edgeSlot3 EdgeSpan := ⟨hx2, hy3⟩
  rw [show edgeSlot2 EdgeSpan ⊓ edgeSlot3 EdgeSpan
        = LinearMap.range (TensorProduct.mapIncl EdgeSpan EdgeSpan) from
      LerayHopf.R3.TensorIntersection.range_map_subtype_inf_range_map_subtype EdgeSpan] at hmem
  obtain ⟨z, hz⟩ := hmem
  show psi2 EdgeSpan BLTLin u x = psi3 EdgeSpan BLTLin u y
  rw [psi2_apply, psi3_apply]
  rw [show (y : TensorProduct ℝ X X) = (x : TensorProduct ℝ X X) from hxy.symm, ← hz]
  exact edge_lift_agree EdgeSpan BLTLin BLT_overlap u z

/-- The glued determined functional on `D = detDomain` (via `LinearPMap.sup`). -/
private noncomputable def psiSup (u : X) :
    (TensorProduct ℝ X X) →ₗ.[ℝ] ℝ :=
  (pmap2 EdgeSpan BLTLin u).sup (pmap3 EdgeSpan BLTLin u) (psi_agree EdgeSpan BLTLin BLT_overlap u)

private theorem psiSup_domain (u : X) :
    (psiSup EdgeSpan BLTLin BLT_overlap u).domain = detDomain EdgeSpan := by
  unfold psiSup pmap2 pmap3 detDomain
  rw [LinearPMap.domain_sup]

/-! ### `gInv`, a fixed left inverse of `detDomain.subtype` -/

/-- The left-inverse existence statement, with the `ℝ`-semiring instance pinned to
`Real.semiring` (avoids the `DivisionRing.toSemiring` mismatch from `Classical.choose`). -/
private theorem detDomain_exists_leftInverse :
    ∃ g : (TensorProduct ℝ X X) →ₗ[ℝ] detDomain EdgeSpan,
      g.comp (detDomain EdgeSpan).subtype = LinearMap.id := by
  letI : Semiring ℝ := inferInstance
  have h := LinearMap.exists_leftInverse_of_injective
    (K := ℝ) (V := detDomain EdgeSpan) (V' := TensorProduct ℝ X X)
    (detDomain EdgeSpan).subtype (Submodule.ker_subtype (detDomain EdgeSpan))
  exact h

private noncomputable def gInv :
    (TensorProduct ℝ X X) →ₗ[ℝ] detDomain EdgeSpan :=
  (detDomain_exists_leftInverse EdgeSpan).choose

private theorem gInv_subtype :
    (gInv EdgeSpan).comp (detDomain EdgeSpan).subtype = LinearMap.id :=
  (detDomain_exists_leftInverse EdgeSpan).choose_spec

private theorem gInv_eq_of_mem (x : TensorProduct ℝ X X)
    (hx : x ∈ detDomain EdgeSpan) : gInv EdgeSpan x = (⟨x, hx⟩ : detDomain EdgeSpan) :=
  LinearMap.congr_fun (gInv_subtype EdgeSpan) ⟨x, hx⟩

private theorem gInv_apply_mem (x : TensorProduct ℝ X X)
    (hx : x ∈ detDomain EdgeSpan) : (gInv EdgeSpan x : TensorProduct ℝ X X) = x := by
  rw [gInv_eq_of_mem EdgeSpan x hx]

/-! ### `psiD` and its `u`-linearity -/

/-- The glued functional re-typed on `detDomain` (value-preserving). -/
private noncomputable def psiD (u : X) : detDomain EdgeSpan →ₗ[ℝ] ℝ :=
  (psiSup EdgeSpan BLTLin BLT_overlap u).toFun.comp
    (LinearEquiv.ofEq _ _ (psiSup_domain EdgeSpan BLTLin BLT_overlap u).symm).toLinearMap

private theorem mem_psiSup_domain (u : X)
    {x : TensorProduct ℝ X X} (hxD : x ∈ detDomain EdgeSpan) :
    x ∈ (psiSup EdgeSpan BLTLin BLT_overlap u).domain := by
  rw [psiSup_domain]; exact hxD

private theorem psiD_eq_psiSup (u : X)
    (x : TensorProduct ℝ X X) (hxD : x ∈ detDomain EdgeSpan) :
    psiD EdgeSpan BLTLin BLT_overlap u ⟨x, hxD⟩
      = (psiSup EdgeSpan BLTLin BLT_overlap u) ⟨x, mem_psiSup_domain EdgeSpan BLTLin BLT_overlap u hxD⟩ := by
  unfold psiD
  rfl

private theorem psiD_apply_mem (u : X)
    (x : TensorProduct ℝ X X) (hx2 : x ∈ edgeSlot2 EdgeSpan) (hxD : x ∈ detDomain EdgeSpan) :
    psiD EdgeSpan BLTLin BLT_overlap u ⟨x, hxD⟩ = psi2 EdgeSpan BLTLin u ⟨x, hx2⟩ := by
  rw [psiD_eq_psiSup EdgeSpan BLTLin BLT_overlap u x hxD]
  obtain ⟨hdom, hval⟩ :=
    LinearPMap.left_le_sup (pmap2 EdgeSpan BLTLin u) (pmap3 EdgeSpan BLTLin u)
      (psi_agree EdgeSpan BLTLin BLT_overlap u)
  have h2 := hval (x := ⟨x, hx2⟩)
    (y := ⟨x, mem_psiSup_domain EdgeSpan BLTLin BLT_overlap u hxD⟩) rfl
  exact h2.symm

private theorem psiD_apply_mem3 (u : X)
    (x : TensorProduct ℝ X X) (hx3 : x ∈ edgeSlot3 EdgeSpan) (hxD : x ∈ detDomain EdgeSpan) :
    psiD EdgeSpan BLTLin BLT_overlap u ⟨x, hxD⟩ = psi3 EdgeSpan BLTLin u ⟨x, hx3⟩ := by
  rw [psiD_eq_psiSup EdgeSpan BLTLin BLT_overlap u x hxD]
  obtain ⟨hdom, hval⟩ :=
    LinearPMap.right_le_sup (pmap2 EdgeSpan BLTLin u) (pmap3 EdgeSpan BLTLin u)
      (psi_agree EdgeSpan BLTLin BLT_overlap u)
  have h3 := hval (x := ⟨x, hx3⟩)
    (y := ⟨x, mem_psiSup_domain EdgeSpan BLTLin BLT_overlap u hxD⟩) rfl
  exact h3.symm

private theorem psiD_add (u u' : X) :
    psiD EdgeSpan BLTLin BLT_overlap (u + u')
      = psiD EdgeSpan BLTLin BLT_overlap u + psiD EdgeSpan BLTLin BLT_overlap u' := by
  refine LinearMap.ext (fun z => ?_)
  obtain ⟨x, hx2, y, hy3, hxy⟩ :=
    Submodule.mem_sup.mp (z.2 : (z : TensorProduct ℝ X X) ∈ edgeSlot2 EdgeSpan ⊔ edgeSlot3 EdgeSpan)
  have hzval : (z : TensorProduct ℝ X X) = x + y := hxy.symm
  have hxD : x ∈ detDomain EdgeSpan := Submodule.mem_sup_left hx2
  have hyD : y ∈ detDomain EdgeSpan := Submodule.mem_sup_right hy3
  have hsplit : z = (⟨x, hxD⟩ : detDomain EdgeSpan) + (⟨y, hyD⟩ : detDomain EdgeSpan) := by
    apply Subtype.ext; simpa using hzval
  rw [hsplit]
  simp only [map_add, LinearMap.add_apply,
    psiD_apply_mem EdgeSpan BLTLin BLT_overlap u x hx2 hxD,
    psiD_apply_mem EdgeSpan BLTLin BLT_overlap u' x hx2 hxD,
    psiD_apply_mem EdgeSpan BLTLin BLT_overlap (u + u') x hx2 hxD,
    psiD_apply_mem3 EdgeSpan BLTLin BLT_overlap u y hy3 hyD,
    psiD_apply_mem3 EdgeSpan BLTLin BLT_overlap u' y hy3 hyD,
    psiD_apply_mem3 EdgeSpan BLTLin BLT_overlap (u + u') y hy3 hyD,
    psi2_add EdgeSpan BLTLin u u' ⟨x, hx2⟩, psi3_add EdgeSpan BLTLin u u' ⟨y, hy3⟩]

private theorem psiD_smul (c : ℝ) (u : X) :
    psiD EdgeSpan BLTLin BLT_overlap (c • u) = c • psiD EdgeSpan BLTLin BLT_overlap u := by
  refine LinearMap.ext (fun z => ?_)
  obtain ⟨x, hx2, y, hy3, hxy⟩ :=
    Submodule.mem_sup.mp (z.2 : (z : TensorProduct ℝ X X) ∈ edgeSlot2 EdgeSpan ⊔ edgeSlot3 EdgeSpan)
  have hxD : x ∈ detDomain EdgeSpan := Submodule.mem_sup_left hx2
  have hyD : y ∈ detDomain EdgeSpan := Submodule.mem_sup_right hy3
  have hsplit : z = (⟨x, hxD⟩ : detDomain EdgeSpan) + (⟨y, hyD⟩ : detDomain EdgeSpan) := by
    apply Subtype.ext; simpa using hxy.symm
  rw [hsplit]
  simp only [map_add, LinearMap.smul_apply, smul_eq_mul,
    psiD_apply_mem EdgeSpan BLTLin BLT_overlap u x hx2 hxD,
    psiD_apply_mem EdgeSpan BLTLin BLT_overlap (c • u) x hx2 hxD,
    psiD_apply_mem3 EdgeSpan BLTLin BLT_overlap u y hy3 hyD,
    psiD_apply_mem3 EdgeSpan BLTLin BLT_overlap (c • u) y hy3 hyD,
    psi2_smul EdgeSpan BLTLin c u ⟨x, hx2⟩, psi3_smul EdgeSpan BLTLin c u ⟨y, hy3⟩]

/-! ### The antisymmetrizer and `detExtend` -/

/-- The antisymmetrizer `A := (id − swap)/2` on `X ⊗ X`. -/
noncomputable def antisymmetrizer :
    TensorProduct ℝ X X →ₗ[ℝ] TensorProduct ℝ X X :=
  (2⁻¹ : ℝ) • (LinearMap.id - (TensorProduct.comm ℝ X X).toLinearMap)

private theorem antisymmetrizer_tmul (v w : X) :
    antisymmetrizer (X := X) (v ⊗ₜ[ℝ] w) = (2⁻¹ : ℝ) • (v ⊗ₜ[ℝ] w - w ⊗ₜ[ℝ] v) := by
  unfold antisymmetrizer
  simp [TensorProduct.comm_tmul]

/-- The antisymmetrizer is antisymmetric on simple tensors: `A (w ⊗ v) = − A (v ⊗ w)`. -/
private theorem antisymmetrizer_tmul_swap (v w : X) :
    antisymmetrizer (X := X) (w ⊗ₜ[ℝ] v) = -antisymmetrizer (X := X) (v ⊗ₜ[ℝ] w) := by
  rw [antisymmetrizer_tmul, antisymmetrizer_tmul,
    ← neg_sub ((v : X) ⊗ₜ[ℝ] w) (w ⊗ₜ[ℝ] v), smul_neg]

/-- **`detExtend`.** The determined form `b u v w := detExtend u (v ⊗ₜ w)`.
Built as `(psiD u) ∘ₗ gInv ∘ₗ A` where `A` is the antisymmetrizer `(id − swap) / 2`; this
makes `detExtend u` antisymmetric for **all** `(v, w)`, while on the determined edge `D` it
reads the glued value `psiD u` (`gInv` fixes `D`). -/
noncomputable def detExtend :
    X →ₗ[ℝ] (TensorProduct ℝ X X) →ₗ[ℝ] ℝ where
  toFun u := ((psiD EdgeSpan BLTLin BLT_overlap u).comp (gInv EdgeSpan)).comp antisymmetrizer
  map_add' u u' := by
    refine LinearMap.ext (fun z => ?_)
    simp only [LinearMap.comp_apply, LinearMap.add_apply]
    rw [psiD_add EdgeSpan BLTLin BLT_overlap u u', LinearMap.add_apply]
  map_smul' c u := by
    refine LinearMap.ext (fun z => ?_)
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, RingHom.id_apply]
    rw [psiD_smul EdgeSpan BLTLin BLT_overlap c u, LinearMap.smul_apply]

private theorem detExtend_add (u u' : X)
    (z : TensorProduct ℝ X X) :
    detExtend EdgeSpan BLTLin BLT_overlap (u + u') z
      = detExtend EdgeSpan BLTLin BLT_overlap u z + detExtend EdgeSpan BLTLin BLT_overlap u' z := by
  rw [(detExtend EdgeSpan BLTLin BLT_overlap).map_add u u', LinearMap.add_apply]

private theorem detExtend_smul (c : ℝ) (u : X)
    (z : TensorProduct ℝ X X) :
    detExtend EdgeSpan BLTLin BLT_overlap (c • u) z = c • detExtend EdgeSpan BLTLin BLT_overlap u z := by
  rw [(detExtend EdgeSpan BLTLin BLT_overlap).map_smul c u, LinearMap.smul_apply]

/-! ### Membership/retraction lemmas for the `edgeSlot` simple tensors, and the determined
value of `psiD` on them -/

private theorem tmul_mem_edgeSlot3 (v : X) (s : EdgeSpan) :
    (v : X) ⊗ₜ[ℝ] (s : X) ∈ edgeSlot3 EdgeSpan :=
  ⟨v ⊗ₜ[ℝ] s, by rw [TensorProduct.map_tmul, LinearMap.id_apply, Submodule.coe_subtype]⟩

private theorem tmul_mem_edgeSlot2 (s : EdgeSpan) (v : X) :
    (s : X) ⊗ₜ[ℝ] (v : X) ∈ edgeSlot2 EdgeSpan :=
  ⟨s ⊗ₜ[ℝ] v, by rw [TensorProduct.map_tmul, LinearMap.id_apply, Submodule.coe_subtype]⟩

private theorem retr3_tmul_span (v : X) (s : EdgeSpan) :
    retr3 EdgeSpan ((v : X) ⊗ₜ[ℝ] (s : X)) = v ⊗ₜ[ℝ] s := by
  unfold retr3
  rw [TensorProduct.map_tmul, LinearMap.id_apply, projE_subtype]

private theorem retr2_tmul_span (s : EdgeSpan) (v : X) :
    retr2 EdgeSpan ((s : X) ⊗ₜ[ℝ] (v : X)) = s ⊗ₜ[ℝ] v := by
  unfold retr2
  rw [TensorProduct.map_tmul, LinearMap.id_apply, projE_subtype]

private theorem psiD_edge3_value (u v : X) (s : EdgeSpan) :
    psiD EdgeSpan BLTLin BLT_overlap u
        ⟨(v : X) ⊗ₜ[ℝ] (s : X), Submodule.mem_sup_right (tmul_mem_edgeSlot3 EdgeSpan v s)⟩
      = BLTLin s u v := by
  rw [psiD_apply_mem3 EdgeSpan BLTLin BLT_overlap u _
      (tmul_mem_edgeSlot3 EdgeSpan v s) (Submodule.mem_sup_right (tmul_mem_edgeSlot3 EdgeSpan v s)),
    psi3_apply]
  show edge3Lift EdgeSpan BLTLin u (retr3 EdgeSpan ((v : X) ⊗ₜ[ℝ] (s : X))) = BLTLin s u v
  rw [retr3_tmul_span EdgeSpan v s, edge3Lift_tmul]

private theorem psiD_edge2_value (u v : X) (s : EdgeSpan) :
    psiD EdgeSpan BLTLin BLT_overlap u
        ⟨(s : X) ⊗ₜ[ℝ] (v : X), Submodule.mem_sup_left (tmul_mem_edgeSlot2 EdgeSpan s v)⟩
      = -(BLTLin s u v) := by
  rw [psiD_apply_mem EdgeSpan BLTLin BLT_overlap u _
      (tmul_mem_edgeSlot2 EdgeSpan s v) (Submodule.mem_sup_left (tmul_mem_edgeSlot2 EdgeSpan s v)),
    psi2_apply]
  show edge2Lift EdgeSpan BLTLin u (retr2 EdgeSpan ((s : X) ⊗ₜ[ℝ] (v : X))) = -(BLTLin s u v)
  rw [retr2_tmul_span EdgeSpan s v, edge2Lift_tmul]

/-! ### `convFormL2_def` and its trilinearity/antisymmetry -/

/-- **`convFormL2_def` (`b`).** The determined trilinear convection form
`b u v w := detExtend u (v ⊗ₜ w)`. -/
noncomputable def convFormL2_def (u v w : X) : ℝ :=
  detExtend EdgeSpan BLTLin BLT_overlap u (v ⊗ₜ[ℝ] w)

/-- `convFormL2_def` unfolds to its defining tensor-edge-extension formula. -/
@[simp]
theorem convFormL2_def_eq (u v w : X) :
    convFormL2_def EdgeSpan BLTLin BLT_overlap u v w
      = detExtend EdgeSpan BLTLin BLT_overlap u (v ⊗ₜ[ℝ] w) :=
  rfl

/-- **`convFormL2_multilinear`.** `∃ B trilinear, ∀ u v w, b u v w = B u v w`. -/
theorem convFormL2_multilinear :
    ∃ B : X →ₗ[ℝ] X →ₗ[ℝ] X →ₗ[ℝ] ℝ,
      ∀ (u v w : X), convFormL2_def EdgeSpan BLTLin BLT_overlap u v w = B u v w := by
  refine ⟨{
    toFun := fun u =>
      LinearMap.compr₂ (TensorProduct.mk ℝ X X) (detExtend EdgeSpan BLTLin BLT_overlap u)
    map_add' := fun u u' => by
      refine LinearMap.ext (fun v => LinearMap.ext (fun w => ?_))
      simp only [LinearMap.add_apply, LinearMap.compr₂_apply, TensorProduct.mk_apply]
      exact detExtend_add EdgeSpan BLTLin BLT_overlap u u' (v ⊗ₜ[ℝ] w)
    map_smul' := fun c u => by
      refine LinearMap.ext (fun v => LinearMap.ext (fun w => ?_))
      simp only [RingHom.id_apply, LinearMap.smul_apply, LinearMap.compr₂_apply,
        TensorProduct.mk_apply]
      exact detExtend_smul EdgeSpan BLTLin BLT_overlap c u (v ⊗ₜ[ℝ] w) }, ?_⟩
  intro u v w
  rw [convFormL2_def_eq]
  rfl

/-- **`convFormL2_antisymm`.** `b u v w = − b u w v` for all `u v w`. -/
theorem convFormL2_antisymm (u v w : X) :
    convFormL2_def EdgeSpan BLTLin BLT_overlap u v w
      = -convFormL2_def EdgeSpan BLTLin BLT_overlap u w v := by
  rw [convFormL2_def_eq, convFormL2_def_eq]
  show ((psiD EdgeSpan BLTLin BLT_overlap u).comp (gInv EdgeSpan)).comp antisymmetrizer (v ⊗ₜ[ℝ] w)
    = -(((psiD EdgeSpan BLTLin BLT_overlap u).comp (gInv EdgeSpan)).comp antisymmetrizer (w ⊗ₜ[ℝ] v))
  rw [LinearMap.comp_apply, LinearMap.comp_apply (g := antisymmetrizer),
    antisymmetrizer_tmul_swap v w, map_neg, neg_neg]

/-- **`detExtend_edge3_eq` [new generic corollary].** On ALL `u v` and any edge test
`w : EdgeSpan`, `detExtend u (v ⊗ₜ (w : X)) = BLTLin w u v` — the *determined* value, not a
Hamel value. Both `v ⊗ₜ w ∈ edgeSlot3` and `w ⊗ₜ v ∈ edgeSlot2` lie in `detDomain`; `gInv`
fixes `detDomain` and the antisymmetrizer combines the two determined edge values into the
single `BLTLin w u v`. Each lane derives its `b_cont_fixedTest` bridge lemma from this in one
step (R3: compose with `convBLTspan_eq_fixedTest`; Torus: compose with `convBLTgalerkin_apply`). -/
theorem detExtend_edge3_eq (u v : X) (w : EdgeSpan) :
    detExtend EdgeSpan BLTLin BLT_overlap u ((v : X) ⊗ₜ[ℝ] (w : X)) = BLTLin w u v := by
  have hmem3 : (v : X) ⊗ₜ[ℝ] (w : X) ∈ detDomain EdgeSpan :=
    Submodule.mem_sup_right (tmul_mem_edgeSlot3 EdgeSpan v w)
  have hmem2 : (w : X) ⊗ₜ[ℝ] (v : X) ∈ detDomain EdgeSpan :=
    Submodule.mem_sup_left (tmul_mem_edgeSlot2 EdgeSpan w v)
  show ((psiD EdgeSpan BLTLin BLT_overlap u).comp (gInv EdgeSpan)).comp antisymmetrizer
      ((v : X) ⊗ₜ[ℝ] (w : X))
    = BLTLin w u v
  rw [LinearMap.comp_apply, LinearMap.comp_apply, antisymmetrizer_tmul]
  rw [map_smul, map_sub, gInv_eq_of_mem EdgeSpan _ hmem3, gInv_eq_of_mem EdgeSpan _ hmem2,
    map_smul, map_sub, psiD_edge3_value EdgeSpan BLTLin BLT_overlap u v w,
    psiD_edge2_value EdgeSpan BLTLin BLT_overlap u v w]
  rw [sub_neg_eq_add, ← two_mul, smul_eq_mul, ← mul_assoc]
  norm_num

end LerayHopf.TensorEdgeGluing
