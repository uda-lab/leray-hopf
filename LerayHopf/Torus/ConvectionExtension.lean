import LerayHopf.Torus.EnergyConvection
import LerayHopf.Torus.GalerkinScheme
import LerayHopf.Torus.ConvectionForm
import LerayHopf.R3.TensorIntersection
import LerayHopf.Analysis.TensorEdgeGluing
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.LinearAlgebra.LinearPMap
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Analysis.Normed.Operator.Extend

/-!
# TorusConvectionExtension — determined-form construction of the full torus `b` form (torus #53)

**File:** `LerayHopf/Torus/ConvectionExtension.lean`

## What this file builds

This file constructs the trilinear convection form
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

- `galerkinTestSpan` — the Galerkin-test span submodule `𝒢 ≤ L²_σ`
- `edgeSlot2`, `edgeSlot3`, `detDomain` — the two edge submodules and their sup
- `edge_inf_eq_galerkin_tensor` — `(𝒢 ⊗ L²) ⊓ (L² ⊗ 𝒢) = 𝒢 ⊗ 𝒢` (direct reuse)
- `convBLTgalerkin` — the jointly continuous bilinear for a fixed Galerkin test `w`
- `convBLTgalerkinLin` — linearity of `convBLTgalerkin` in the test slot
- `antisymmetrizer` — `(id − swap)/2` on `L²_σ ⊗ L²_σ`
- `detExtend` — the determined extension `L²_σ →ₗ (L²_σ ⊗ L²_σ) →ₗ ℝ` (`gInv`, the left-inverse
  of `detDomain.subtype` it is built from, is now private to `LerayHopf.TensorEdgeGluing`,
  issue #111 PR-1)
- `convFormL2_def` — the trilinear `b u v w := detExtend u (v ⊗ₜ w)`
- `torusConvectionGap_holds` — assembly theorem for all seven fields

## Axiom status

No new `axiom`/`opaque`.  The determined-form construction proves
`torusConvectionGap_holds`, so `LerayHopf.torusConvectionGap_exists` is a theorem and does not
appear in the capstone `#print axioms` output.  This is a pinned proof-carrying trilinear
extension with fixed-Galerkin-test continuity, not a canonical continuous pure-`L²³` operator.
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

/-! ### T1 — the three edge submodules

`edgeSlot2`/`edgeSlot3`/`detDomain` are the generic `LerayHopf.TensorEdgeGluing` submodules
instantiated at `EdgeSpan := galerkinTestSpan` (issue #111 PR-1). -/

/-- The "slot-2 Galerkin" edge submodule `𝒢 ⊗ L²_σ ≤ L²_σ ⊗ L²_σ`. -/
noncomputable def edgeSlot2 : Submodule ℝ (TensorProduct ℝ L2Sigma L2Sigma) :=
  LerayHopf.TensorEdgeGluing.edgeSlot2 galerkinTestSpan

/-- The "slot-3 Galerkin" edge submodule `L²_σ ⊗ 𝒢 ≤ L²_σ ⊗ L²_σ`. -/
noncomputable def edgeSlot3 : Submodule ℝ (TensorProduct ℝ L2Sigma L2Sigma) :=
  LerayHopf.TensorEdgeGluing.edgeSlot3 galerkinTestSpan

/-- **`detDomain` — the determined domain `D`.** `D := (𝒢 ⊗ L²_σ) + (L²_σ ⊗ 𝒢)`. -/
noncomputable def detDomain : Submodule ℝ (TensorProduct ℝ L2Sigma L2Sigma) :=
  LerayHopf.TensorEdgeGluing.detDomain galerkinTestSpan

/-- **`edge_inf_eq_galerkin_tensor` [proved sorry-free].** The overlap identity:
`(𝒢 ⊗ L²_σ) ⊓ (L²_σ ⊗ 𝒢) = 𝒢 ⊗ 𝒢`.

Direct reuse of the generic `TensorIntersection.range_map_subtype_inf_range_map_subtype`
instantiated at `S := galerkinTestSpan`, exactly as R3's `edge_inf_eq_schwartz_tensor`. -/
theorem edge_inf_eq_galerkin_tensor :
    edgeSlot2 ⊓ edgeSlot3
      = LinearMap.range (TensorProduct.mapIncl galerkinTestSpan galerkinTestSpan) :=
  LerayHopf.R3.TensorIntersection.range_map_subtype_inf_range_map_subtype galerkinTestSpan

/-! ### T2 — the edge bilinears from `convFormFourier`

For a fixed Galerkin test `w`, `convFormFourier u v w` is the determined value on the
Galerkin-test slice.  The two edge prescriptions mirror R3's `edge2Bil` / `edge3Bil`:

- on `𝒢 ⊗ L²_σ` (slot-2 Galerkin): `(s, l) ↦ -convFormFourier u s l`
  (antisymmetric of the slot-3 value, by `convFormFourier_antisymm_galerkinTest`);
- on `L²_σ ⊗ 𝒢` (slot-3 Galerkin): `(l, s) ↦ convFormFourier u l s`.

The jointly continuous BLT extension off the Galerkin-test slice to all of `L²_σ` is supplied
by the proved determined-form construction below. -/


/-! ### ENGINE: analytic core (folded from validated ScratchConv) -/

noncomputable def l2coeff (f : L2C) : ℝ :=
  (∑' k : Fin 3 → ℤ, ‖mFourierCoeff3 f k‖ ^ 2) ^ ((1:ℝ)/2)

lemma l2coeff_le (f : L2C) : l2coeff f ≤ ‖f‖ := by
  unfold l2coeff
  rw [← L2C_norm_sq_eq_tsum_coeff_sq, ← Real.rpow_natCast ‖f‖ 2, ← Real.rpow_mul (norm_nonneg _)]
  norm_num

lemma l2coeff_nonneg (f : L2C) : 0 ≤ l2coeff f := by
  unfold l2coeff; positivity

private def shiftEquiv (m : Fin 3 → ℤ) : (Fin 3 → ℤ) ≃ (Fin 3 → ℤ) where
  toFun k := -k - m
  invFun l := -l - m
  left_inv k := by funext j; simp [Pi.neg_apply, Pi.sub_apply]
  right_inv l := by funext j; simp [Pi.neg_apply, Pi.sub_apply]

lemma tsum_sq_shift (f : L2C) (m : Fin 3 → ℤ) :
    ∑' k : Fin 3 → ℤ, ‖mFourierCoeff3 f (-k - m)‖ ^ 2
      = ∑' l : Fin 3 → ℤ, ‖mFourierCoeff3 f l‖ ^ 2 := by
  rw [← Equiv.tsum_eq (shiftEquiv m) (fun l => ‖mFourierCoeff3 f l‖^2)]
  rfl

lemma summable_sq_shift (f : L2C) (m : Fin 3 → ℤ)
    (h : Summable (fun l : Fin 3 → ℤ => ‖mFourierCoeff3 f l‖ ^ 2)) :
    Summable (fun k : Fin 3 → ℤ => ‖mFourierCoeff3 f (-k - m)‖ ^ 2) := by
  rw [← (shiftEquiv m).summable_iff (f := fun l => ‖mFourierCoeff3 f l‖^2)] at h
  exact h

lemma cs_per_m (fU fV : L2C) (m : Fin 3 → ℤ)
    (hU : Summable (fun k : Fin 3 → ℤ => ‖mFourierCoeff3 fU k‖ ^ 2))
    (hV : Summable (fun l : Fin 3 → ℤ => ‖mFourierCoeff3 fV l‖ ^ 2)) :
    ∑' k : Fin 3 → ℤ, ‖mFourierCoeff3 fU k‖ * ‖mFourierCoeff3 fV (-k - m)‖
      ≤ l2coeff fU * l2coeff fV := by
  have hVshift := summable_sq_shift fV m hV
  -- bridge ^(2:ℕ) → ^(2:ℝ)
  have hU' : Summable (fun k : Fin 3 → ℤ => ‖mFourierCoeff3 fU k‖ ^ (2:ℝ)) := by
    refine hU.congr (fun k => ?_); rw [Real.rpow_two]
  have hVshift' : Summable (fun k : Fin 3 → ℤ => ‖mFourierCoeff3 fV (-k-m)‖ ^ (2:ℝ)) := by
    refine hVshift.congr (fun k => ?_); rw [Real.rpow_two]
  have hcs := Real.inner_le_Lp_mul_Lq_tsum_of_nonneg (Real.HolderConjugate.two_two)
    (f := fun k => ‖mFourierCoeff3 fU k‖) (g := fun k => ‖mFourierCoeff3 fV (-k-m)‖)
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) hU' hVshift'
  refine hcs.trans (le_of_eq ?_)
  unfold l2coeff
  have e1 : ∑' k : Fin 3 → ℤ, ‖mFourierCoeff3 fU k‖ ^ (2:ℝ)
      = ∑' k : Fin 3 → ℤ, ‖mFourierCoeff3 fU k‖ ^ 2 := tsum_congr (fun k => Real.rpow_two _)
  have e2 : ∑' k : Fin 3 → ℤ, ‖mFourierCoeff3 fV (-k-m)‖ ^ (2:ℝ)
      = ∑' l : Fin 3 → ℤ, ‖mFourierCoeff3 fV l‖ ^ 2 := by
    rw [tsum_congr (fun k => Real.rpow_two _), tsum_sq_shift fV m]
  rw [e1, e2]


-- local Parseval-summability
lemma summable_coeff_sq' (f : L2C) :
    Summable (fun k : Fin 3 → ℤ => ‖mFourierCoeff3 f k‖ ^ 2) := by
  have hmem : Memℓp (torus3_mFourierBasis.repr f) 2 := (torus3_mFourierBasis.repr f).2
  have hp : (0 : ℝ) < (2 : ENNReal).toReal := by norm_num
  have := (memℓp_gen_iff hp).mp hmem
  refine this.congr (fun k => ?_)
  rw [show ((2 : ENNReal).toReal) = (2 : ℝ) by norm_num, Real.rpow_two]
  rfl

noncomputable def convSummandW (u v w : L2VF) (i a : Fin 3) (k l : Fin 3 → ℤ) : ℂ :=
  mFourierCoeff3 (L2VF_projComponentC a u) k *
    ((2 * (Real.pi : ℂ) * Complex.I * (-((-(k + l)) a) : ℂ)) *
      (mFourierCoeff3 (L2VF_projComponentC i v) l *
        mFourierCoeff3 (L2VF_projComponentC i w) (-(k + l))))

private def reidxKM : (Fin 3 → ℤ) × (Fin 3 → ℤ) ≃ (Fin 3 → ℤ) × (Fin 3 → ℤ) where
  toFun kl := (kl.1, -(kl.1 + kl.2))
  invFun km := (km.1, -(km.1 + km.2))
  left_inv kl := Prod.ext rfl (by funext j; simp [Pi.neg_apply, Pi.add_apply])
  right_inv km := Prod.ext rfl (by funext j; simp [Pi.neg_apply, Pi.add_apply])

-- Reusable section summability: for fixed m, k ↦ U k * V(-k-m) is summable (CS p=q=2).
lemma sec_summable (U V : (Fin 3 → ℤ) → ℝ)
    (hUsq : Summable (fun k => U k ^ 2)) (hVsq : Summable (fun l => V l ^ 2))
    (hUnn : ∀ k, 0 ≤ U k) (hVnn : ∀ l, 0 ≤ V l) (m : Fin 3 → ℤ) :
    Summable (fun k : Fin 3 → ℤ => U k * V (-k - m)) := by
  have hVshift : Summable (fun k : Fin 3 → ℤ => V (-k - m) ^ 2) := by
    let e : (Fin 3 → ℤ) ≃ (Fin 3 → ℤ) :=
      { toFun := fun k => -k - m, invFun := fun l => -l - m
        left_inv := fun k => by funext j; simp [Pi.neg_apply, Pi.sub_apply]
        right_inv := fun l => by funext j; simp [Pi.neg_apply, Pi.sub_apply] }
    refine ((e.summable_iff (f := fun l => V l ^ 2)).mpr hVsq).congr (fun k => ?_)
    simp only [e, Equiv.coe_fn_mk, Function.comp]
  have hU' : Summable (fun k : Fin 3 → ℤ => U k ^ (2:ℝ)) := hUsq.congr (fun k => by rw [Real.rpow_two])
  have hV' : Summable (fun k : Fin 3 → ℤ => V (-k-m) ^ (2:ℝ)) :=
    hVshift.congr (fun k => by rw [Real.rpow_two])
  exact Real.summable_mul_of_Lp_Lq_of_nonneg Real.HolderConjugate.two_two
    (fun _ => hUnn _) (fun _ => hVnn _) hU' hV'

-- Abstract dominating-sum summability (no expensive coercions here)
set_option maxHeartbeats 1000000 in
lemma dom_summable (U V Wc : (Fin 3 → ℤ) → ℝ) (n : ℕ)
    (hUsq : Summable (fun k => U k ^ 2)) (hVsq : Summable (fun l => V l ^ 2))
    (hUnn : ∀ k, 0 ≤ U k) (hVnn : ∀ l, 0 ≤ V l) (hWnn : ∀ m, 0 ≤ Wc m)
    (hWsupp : ∀ m, m ∉ fourierBox n → Wc m = 0) :
    Summable (fun kl : (Fin 3 → ℤ) × (Fin 3 → ℤ) =>
      Wc (-(kl.1 + kl.2)) * (U kl.1 * V (-kl.1 - -(kl.1 + kl.2)))) := by
  classical
  have hsecS : ∀ m : Fin 3 → ℤ, Summable (fun k : Fin 3 → ℤ => U k * V (-k - m)) :=
    fun m => sec_summable U V hUsq hVsq hUnn hVnn m
  have hg : Summable (fun mk : (Fin 3 → ℤ) × (Fin 3 → ℤ) => Wc mk.1 * (U mk.2 * V (-mk.2 - mk.1))) := by
    rw [summable_prod_of_nonneg (fun mk => by have := hUnn mk.2; have := hVnn (-mk.2-mk.1); have := hWnn mk.1; positivity)]
    refine ⟨fun m => ((hsecS m).mul_left (Wc m)).congr (fun y => rfl), ?_⟩
    refine summable_of_ne_finset_zero (s := fourierBox n) (fun m hm => ?_)
    simp [tsum_mul_left, hWsupp m hm]
  let e : (Fin 3 → ℤ) × (Fin 3 → ℤ) ≃ (Fin 3 → ℤ) × (Fin 3 → ℤ) :=
    { toFun := fun kl => (-(kl.1 + kl.2), kl.1)
      invFun := fun mk => (mk.2, -(mk.2 + mk.1))
      left_inv := fun kl => Prod.ext rfl (by funext j; simp [Pi.neg_apply, Pi.add_apply])
      right_inv := fun mk => Prod.ext (by funext j; simp [Pi.neg_apply, Pi.add_apply]) rfl }
  refine ((e.summable_iff (f := fun mk => Wc mk.1 * (U mk.2 * V (-mk.2 - mk.1)))).mpr hg).congr
    (fun kl => ?_)
  simp only [e, Equiv.coe_fn_mk, Function.comp]


set_option maxHeartbeats 1000000 in
theorem convSummandW_norm_summable (u v : L2VF) (w : L2Sigma) (hw : IsGalerkinTest w) (i a : Fin 3) :
    Summable (fun kl : (Fin 3 → ℤ) × (Fin 3 → ℤ) =>
      ‖convSummandW u v (w : L2VF) i a kl.1 kl.2‖) := by
  classical
  obtain ⟨n, hn⟩ := hw
  have hWsupp : ∀ m : Fin 3 → ℤ, m ∉ fourierBox n →
      mFourierCoeff3 (L2VF_projComponentC i (w:L2VF)) m = 0 := by
    intro m hm
    have hcomm := velocityProjection_n_component_comm n (w:L2VF) i
    rw [hn] at hcomm
    conv_lhs => rw [hcomm]
    rw [ContinuousLinearMap.coe_restrictScalars', fourierProjection_n_mFourierCoeff, if_neg hm]
  -- bound on |m_a| on the support
  have hmbound : ∀ m : Fin 3 → ℤ, m ∈ fourierBox n → |(m a : ℝ)| ≤ (n : ℝ) := by
    intro m hm
    simp only [fourierBox, Fintype.mem_piFinset, Finset.mem_Icc] at hm
    obtain ⟨h1, h2⟩ := hm a
    rw [abs_le]; constructor
    · exact_mod_cast h1
    · exact_mod_cast h2
  set U : (Fin 3 → ℤ) → ℝ := fun k => ‖mFourierCoeff3 (L2VF_projComponentC a u) k‖
  set V : (Fin 3 → ℤ) → ℝ := fun l => ‖mFourierCoeff3 (L2VF_projComponentC i v) l‖
  set Wc : (Fin 3 → ℤ) → ℝ := fun m => ‖mFourierCoeff3 (L2VF_projComponentC i (w:L2VF)) m‖
  have hdom := dom_summable U V Wc n
    ((summable_coeff_sq' _).congr (fun k => rfl)) ((summable_coeff_sq' _).congr (fun l => rfl))
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    (fun m hm => by simp only [Wc, hWsupp m hm, norm_zero])
  refine Summable.of_nonneg_of_le (fun kl => norm_nonneg _) (fun kl => ?_)
    (hdom.mul_left (2 * Real.pi * (n : ℝ)))
  -- pointwise bound
  show ‖convSummandW u v (w:L2VF) i a kl.1 kl.2‖
    ≤ (2 * Real.pi * (n:ℝ)) * (Wc (-(kl.1 + kl.2)) * (U kl.1 * V (-kl.1 - -(kl.1 + kl.2))))
  have hl : (-kl.1 - -(kl.1 + kl.2)) = kl.2 := by funext j; simp [Pi.neg_apply, Pi.sub_apply, Pi.add_apply]
  rw [hl]
  -- compute the norm of convSummandW
  have hnorm : ‖convSummandW u v (w:L2VF) i a kl.1 kl.2‖
      = U kl.1 * (2 * Real.pi * |((-(kl.1 + kl.2)) a : ℝ)|) * V kl.2 * Wc (-(kl.1 + kl.2)) := by
    simp only [convSummandW, U, V, Wc, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Complex.norm_intCast, Real.norm_eq_abs, Complex.norm_ofNat, norm_neg]
    rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ Real.pi)]
    ring
  rw [hnorm]
  -- case on whether m = -(k+l) ∈ box n
  by_cases hm : (-(kl.1 + kl.2)) ∈ fourierBox n
  · have hmb := hmbound _ hm
    have hWnn : 0 ≤ Wc (-(kl.1+kl.2)) := norm_nonneg _
    have hUnn : 0 ≤ U kl.1 := norm_nonneg _
    have hVnn : 0 ≤ V kl.2 := norm_nonneg _
    have hpi : 0 ≤ Real.pi := Real.pi_pos.le
    have hkey : U kl.1 * (2 * Real.pi * |((-(kl.1 + kl.2)) a : ℝ)|) * V kl.2 * Wc (-(kl.1 + kl.2))
        = (2 * Real.pi) * (U kl.1 * V kl.2 * Wc (-(kl.1+kl.2))) * |((-(kl.1 + kl.2)) a : ℝ)| := by
      ring
    have hkey2 : (2 * Real.pi * (n:ℝ)) * (Wc (-(kl.1 + kl.2)) * (U kl.1 * V kl.2))
        = (2 * Real.pi) * (U kl.1 * V kl.2 * Wc (-(kl.1+kl.2))) * (n:ℝ) := by ring
    rw [hkey, hkey2]
    have hanonneg : 0 ≤ (2 * Real.pi) * (U kl.1 * V kl.2 * Wc (-(kl.1+kl.2))) := by positivity
    exact mul_le_mul_of_nonneg_left hmb hanonneg
  · have : Wc (-(kl.1 + kl.2)) = 0 := by simp only [Wc, hWsupp _ hm, norm_zero]
    rw [this]; simp


-- Abstract: the dominating tsum is bounded by (ℓ¹ mass of Wc over box) * l2(U-side) * l2(V-side).
set_option maxHeartbeats 1000000 in
lemma dom_tsum_le (fU fV : L2C) (Wc : (Fin 3 → ℤ) → ℝ) (n : ℕ)
    (hWnn : ∀ m, 0 ≤ Wc m) (hWsupp : ∀ m, m ∉ fourierBox n → Wc m = 0) :
    ∑' kl : (Fin 3 → ℤ) × (Fin 3 → ℤ),
        Wc (-(kl.1 + kl.2)) * (‖mFourierCoeff3 fU kl.1‖ * ‖mFourierCoeff3 fV (-kl.1 - -(kl.1 + kl.2))‖)
      ≤ (∑ m ∈ fourierBox n, Wc m) * (l2coeff fU * l2coeff fV) := by
  classical
  set U : (Fin 3 → ℤ) → ℝ := fun k => ‖mFourierCoeff3 fU k‖ with hUdef
  set V : (Fin 3 → ℤ) → ℝ := fun l => ‖mFourierCoeff3 fV l‖ with hVdef
  have hUsq : Summable (fun k => U k ^ 2) := (summable_coeff_sq' fU).congr (fun k => rfl)
  have hVsq : Summable (fun l => V l ^ 2) := (summable_coeff_sq' fV).congr (fun l => rfl)
  have hsum := dom_summable U V Wc n hUsq hVsq (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) hWnn hWsupp
  -- reindex to (m,k): factor through the (m,k) form, then sum over finite m.
  let e : (Fin 3 → ℤ) × (Fin 3 → ℤ) ≃ (Fin 3 → ℤ) × (Fin 3 → ℤ) :=
    { toFun := fun kl => (-(kl.1 + kl.2), kl.1)
      invFun := fun mk => (mk.2, -(mk.2 + mk.1))
      left_inv := fun kl => Prod.ext rfl (by funext j; simp [Pi.neg_apply, Pi.add_apply])
      right_inv := fun mk => Prod.ext (by funext j; simp [Pi.neg_apply, Pi.add_apply]) rfl }
  have hsumMK : Summable (fun mk : (Fin 3 → ℤ) × (Fin 3 → ℤ) => Wc mk.1 * (U mk.2 * V (-mk.2 - mk.1))) := by
    have := (e.summable_iff (f := fun mk => Wc mk.1 * (U mk.2 * V (-mk.2 - mk.1)))).symm
    rw [this]
    exact hsum.congr (fun kl => by simp only [e, Equiv.coe_fn_mk, Function.comp])
  -- rewrite LHS tsum as the (m,k) tsum
  have hLHS : ∑' kl : (Fin 3 → ℤ) × (Fin 3 → ℤ),
        Wc (-(kl.1 + kl.2)) * (U kl.1 * V (-kl.1 - -(kl.1 + kl.2)))
      = ∑' mk : (Fin 3 → ℤ) × (Fin 3 → ℤ), Wc mk.1 * (U mk.2 * V (-mk.2 - mk.1)) := by
    rw [← Equiv.tsum_eq e (fun mk => Wc mk.1 * (U mk.2 * V (-mk.2 - mk.1)))]
    refine tsum_congr (fun kl => ?_)
    simp only [e, Equiv.coe_fn_mk]
  rw [hLHS]
  -- now sum over m (finite support), inner over k = Wc m * ∑'_k U k V(-k-m) ≤ Wc m * l2 * l2
  have hsecS : ∀ m, Summable (fun k : Fin 3 → ℤ => U k * V (-k - m)) :=
    fun m => sec_summable U V hUsq hVsq (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) m
  rw [hsumMK.tsum_prod' (fun m => (hsecS m).mul_left (Wc m))]
  -- the m-tsum reduces to a finite sum over the box (Wc m = 0 outside)
  have hfin : ∑' m : Fin 3 → ℤ, ∑' k : Fin 3 → ℤ, Wc m * (U k * V (-k - m))
      = ∑ m ∈ fourierBox n, Wc m * (∑' k : Fin 3 → ℤ, U k * V (-k - m)) := by
    rw [tsum_eq_sum (s := fourierBox n) (fun m hm => by
      rw [tsum_mul_left, hWsupp m hm, zero_mul])]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [tsum_mul_left]
  rw [hfin, Finset.sum_mul]
  refine Finset.sum_le_sum (fun m _ => ?_)
  refine mul_le_mul_of_nonneg_left ?_ (hWnn m)
  exact cs_per_m fU fV m (summable_coeff_sq' fU) (summable_coeff_sq' fV)

-- the bilinear value
noncomputable def convValW (u v : L2VF) (w : L2Sigma) : ℝ :=
  ∑ i : Fin 3, ∑ a : Fin 3,
    (∑' kl : (Fin 3 → ℤ) × (Fin 3 → ℤ), convSummandW u v (w : L2VF) i a kl.1 kl.2).re

set_option maxHeartbeats 1000000 in
-- the C(w)·‖u‖·‖v‖ bound
theorem convValW_bound (w : L2Sigma) (hw : IsGalerkinTest w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u v : L2VF), |convValW u v w| ≤ C * ‖u‖ * ‖v‖ := by
  classical
  obtain ⟨n, hn⟩ := hw
  -- per-m ℓ¹ mass of w-coeffs over the box, summed over i, times 2πn, times proj norms
  set Cw : ℝ := ∑ i : Fin 3, ∑ a : Fin 3, (2 * Real.pi * (n:ℝ)) *
    (∑ m ∈ fourierBox n, ‖mFourierCoeff3 (L2VF_projComponentC i (w:L2VF)) m‖) *
    ‖L2VF_projComponentC a‖ * ‖L2VF_projComponentC i‖ with hCw
  -- w-support
  have hWsupp : ∀ (i : Fin 3) (m : Fin 3 → ℤ), m ∉ fourierBox n →
      mFourierCoeff3 (L2VF_projComponentC i (w:L2VF)) m = 0 := by
    intro i m hm
    have hcomm := velocityProjection_n_component_comm n (w:L2VF) i
    rw [hn] at hcomm
    conv_lhs => rw [hcomm]
    rw [ContinuousLinearMap.coe_restrictScalars', fourierProjection_n_mFourierCoeff, if_neg hm]
  refine ⟨Cw, ?_, fun u v => ?_⟩
  · rw [hCw]; positivity
  · -- per-(i,a) bound, then sum.  First: |convValW| ≤ ∑_i∑_a (per-term bound).
    rw [hCw]
    -- distribute the RHS sum: Cw * ‖u‖ * ‖v‖ = ∑_i ∑_a [term * ‖u‖ * ‖v‖]
    have hrhs : (∑ i : Fin 3, ∑ a : Fin 3, (2 * Real.pi * (n:ℝ)) *
          (∑ m ∈ fourierBox n, ‖mFourierCoeff3 (L2VF_projComponentC i (w:L2VF)) m‖) *
          ‖L2VF_projComponentC a‖ * ‖L2VF_projComponentC i‖) * ‖u‖ * ‖v‖
        = ∑ i : Fin 3, ∑ a : Fin 3, ((2 * Real.pi * (n:ℝ)) *
            (∑ m ∈ fourierBox n, ‖mFourierCoeff3 (L2VF_projComponentC i (w:L2VF)) m‖) *
            (‖L2VF_projComponentC a‖ * ‖u‖) * (‖L2VF_projComponentC i‖ * ‖v‖)) := by
      rw [Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      ring
    rw [hrhs]
    -- |convValW| ≤ ∑_i∑_a |(∑'.re)|
    unfold convValW
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine Finset.sum_le_sum (fun i _ => ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine Finset.sum_le_sum (fun a _ => ?_)
    -- |(∑'.re)| ≤ ∑'‖summand‖
    have hsumm := convSummandW_norm_summable u v w ⟨n, hn⟩ i a
    have hstep1 : |(∑' kl : (Fin 3 → ℤ) × (Fin 3 → ℤ),
          convSummandW u v (w:L2VF) i a kl.1 kl.2).re|
        ≤ ∑' kl : (Fin 3 → ℤ) × (Fin 3 → ℤ), ‖convSummandW u v (w:L2VF) i a kl.1 kl.2‖ := by
      refine (RCLike.abs_re_le_norm (K := ℂ) _).trans ?_
      exact norm_tsum_le_tsum_norm hsumm
    refine hstep1.trans ?_
    -- ∑'‖summand‖ ≤ 2πn · ∑'dom
    have hpt : ∀ kl : (Fin 3 → ℤ) × (Fin 3 → ℤ),
        ‖convSummandW u v (w:L2VF) i a kl.1 kl.2‖
          ≤ (2 * Real.pi * (n:ℝ)) *
            (‖mFourierCoeff3 (L2VF_projComponentC i (w:L2VF)) (-(kl.1 + kl.2))‖ *
              (‖mFourierCoeff3 (L2VF_projComponentC a u) kl.1‖ *
               ‖mFourierCoeff3 (L2VF_projComponentC i v) (-kl.1 - -(kl.1 + kl.2))‖)) := by
      intro kl
      have hl : (-kl.1 - -(kl.1 + kl.2)) = kl.2 := by
        funext j; simp [Pi.neg_apply, Pi.sub_apply, Pi.add_apply]
      rw [hl]
      have hnorm : ‖convSummandW u v (w:L2VF) i a kl.1 kl.2‖
          = ‖mFourierCoeff3 (L2VF_projComponentC a u) kl.1‖ *
              (2 * Real.pi * |((-(kl.1 + kl.2)) a : ℝ)|) *
              ‖mFourierCoeff3 (L2VF_projComponentC i v) kl.2‖ *
              ‖mFourierCoeff3 (L2VF_projComponentC i (w:L2VF)) (-(kl.1 + kl.2))‖ := by
        simp only [convSummandW, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
          Complex.norm_intCast, Real.norm_eq_abs, Complex.norm_ofNat, norm_neg]
        rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ Real.pi)]
        ring
      rw [hnorm]
      by_cases hm : (-(kl.1 + kl.2)) ∈ fourierBox n
      · have hmb : |((-(kl.1 + kl.2)) a : ℝ)| ≤ (n:ℝ) := by
          simp only [fourierBox, Fintype.mem_piFinset, Finset.mem_Icc] at hm
          obtain ⟨h1, h2⟩ := hm a
          rw [abs_le]; exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
        set P := ‖mFourierCoeff3 (L2VF_projComponentC a u) kl.1‖ *
          ‖mFourierCoeff3 (L2VF_projComponentC i v) kl.2‖ *
          ‖mFourierCoeff3 (L2VF_projComponentC i (w:L2VF)) (-(kl.1 + kl.2))‖ with hP
        have hPnn : 0 ≤ P := by rw [hP]; positivity
        have he1 : ‖mFourierCoeff3 (L2VF_projComponentC a u) kl.1‖ *
              (2 * Real.pi * |((-(kl.1 + kl.2)) a : ℝ)|) *
              ‖mFourierCoeff3 (L2VF_projComponentC i v) kl.2‖ *
              ‖mFourierCoeff3 (L2VF_projComponentC i (w:L2VF)) (-(kl.1 + kl.2))‖
            = (2 * Real.pi) * P * |((-(kl.1 + kl.2)) a : ℝ)| := by rw [hP]; ring
        have he2 : (2 * Real.pi * (n:ℝ)) *
              (‖mFourierCoeff3 (L2VF_projComponentC i (w:L2VF)) (-(kl.1 + kl.2))‖ *
                (‖mFourierCoeff3 (L2VF_projComponentC a u) kl.1‖ *
                 ‖mFourierCoeff3 (L2VF_projComponentC i v) kl.2‖))
            = (2 * Real.pi) * P * (n:ℝ) := by rw [hP]; ring
        rw [he1, he2]
        exact mul_le_mul_of_nonneg_left hmb (by positivity)
      · rw [hWsupp i _ hm]; simp
    have hdomle := dom_tsum_le (L2VF_projComponentC a u) (L2VF_projComponentC i v)
      (fun m => ‖mFourierCoeff3 (L2VF_projComponentC i (w:L2VF)) m‖) n
      (fun _ => norm_nonneg _) (fun m hm => by rw [hWsupp i m hm, norm_zero])
    -- ∑'‖summand‖ ≤ 2πn * ∑'dom ≤ 2πn * (box mass)*(l2*l2)
    have hdomsumm := dom_summable
      (fun k => ‖mFourierCoeff3 (L2VF_projComponentC a u) k‖)
      (fun l => ‖mFourierCoeff3 (L2VF_projComponentC i v) l‖)
      (fun m => ‖mFourierCoeff3 (L2VF_projComponentC i (w:L2VF)) m‖) n
      ((summable_coeff_sq' _).congr (fun k => rfl)) ((summable_coeff_sq' _).congr (fun l => rfl))
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
      (fun m hm => by rw [hWsupp i m hm, norm_zero])
    have hchain : ∑' kl : (Fin 3 → ℤ) × (Fin 3 → ℤ),
          ‖convSummandW u v (w:L2VF) i a kl.1 kl.2‖
        ≤ (2 * Real.pi * (n:ℝ)) * (∑' kl : (Fin 3 → ℤ) × (Fin 3 → ℤ),
            ‖mFourierCoeff3 (L2VF_projComponentC i (w:L2VF)) (-(kl.1 + kl.2))‖ *
              (‖mFourierCoeff3 (L2VF_projComponentC a u) kl.1‖ *
               ‖mFourierCoeff3 (L2VF_projComponentC i v) (-kl.1 - -(kl.1 + kl.2))‖)) := by
      rw [← tsum_mul_left]
      exact Summable.tsum_le_tsum hpt hsumm (hdomsumm.mul_left _)
    refine hchain.trans ?_
    -- bound the dom tsum by (box mass)*(l2*l2), and l2 ≤ ‖proj‖‖·‖
    have hmul : (2 * Real.pi * (n:ℝ)) *
        (∑' kl : (Fin 3 → ℤ) × (Fin 3 → ℤ),
          ‖mFourierCoeff3 (L2VF_projComponentC i (w:L2VF)) (-(kl.1 + kl.2))‖ *
            (‖mFourierCoeff3 (L2VF_projComponentC a u) kl.1‖ *
             ‖mFourierCoeff3 (L2VF_projComponentC i v) (-kl.1 - -(kl.1 + kl.2))‖))
        ≤ (2 * Real.pi * (n:ℝ)) *
          ((∑ m ∈ fourierBox n, ‖mFourierCoeff3 (L2VF_projComponentC i (w:L2VF)) m‖) *
            (l2coeff (L2VF_projComponentC a u) * l2coeff (L2VF_projComponentC i v))) := by
      refine mul_le_mul_of_nonneg_left hdomle (by positivity)
    refine hmul.trans ?_
    -- replace l2coeff by ‖proj‖‖·‖ and rearrange
    have hl2u : l2coeff (L2VF_projComponentC a u) ≤ ‖L2VF_projComponentC a‖ * ‖u‖ := by
      refine (l2coeff_le _).trans ?_
      exact (L2VF_projComponentC a).le_opNorm u
    have hl2v : l2coeff (L2VF_projComponentC i v) ≤ ‖L2VF_projComponentC i‖ * ‖v‖ := by
      refine (l2coeff_le _).trans ?_
      exact (L2VF_projComponentC i).le_opNorm v
    have hmassnn : 0 ≤ ∑ m ∈ fourierBox n, ‖mFourierCoeff3 (L2VF_projComponentC i (w:L2VF)) m‖ := by
      positivity
    calc (2 * Real.pi * (n:ℝ)) *
            ((∑ m ∈ fourierBox n, ‖mFourierCoeff3 (L2VF_projComponentC i (w:L2VF)) m‖) *
              (l2coeff (L2VF_projComponentC a u) * l2coeff (L2VF_projComponentC i v)))
        ≤ (2 * Real.pi * (n:ℝ)) *
            ((∑ m ∈ fourierBox n, ‖mFourierCoeff3 (L2VF_projComponentC i (w:L2VF)) m‖) *
              ((‖L2VF_projComponentC a‖ * ‖u‖) * (‖L2VF_projComponentC i‖ * ‖v‖))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          refine mul_le_mul_of_nonneg_left ?_ hmassnn
          exact mul_le_mul hl2u hl2v (l2coeff_nonneg _) (by positivity)
      _ = (2 * Real.pi * (n:ℝ)) *
            (∑ m ∈ fourierBox n, ‖mFourierCoeff3 (L2VF_projComponentC i (w:L2VF)) m‖) *
            (‖L2VF_projComponentC a‖ * ‖u‖) * (‖L2VF_projComponentC i‖ * ‖v‖) := by ring


-- coeff linearity helpers (local)
lemma coeff_proj_add (j : Fin 3) (u u' : L2VF) (k : Fin 3 → ℤ) :
    mFourierCoeff3 (L2VF_projComponentC j (u + u')) k
      = mFourierCoeff3 (L2VF_projComponentC j u) k + mFourierCoeff3 (L2VF_projComponentC j u') k := by
  rw [map_add]; simp only [mFourierCoeff3, map_add, lp.coeFn_add, Pi.add_apply]

lemma coeff_proj_smul (j : Fin 3) (c : ℝ) (u : L2VF) (k : Fin 3 → ℤ) :
    mFourierCoeff3 (L2VF_projComponentC j (c • u)) k
      = (c : ℂ) * mFourierCoeff3 (L2VF_projComponentC j u) k := by
  rw [map_smul, mFourierCoeff3, mFourierCoeff3, RCLike.real_smul_eq_coe_smul (K := ℂ), map_smul,
    lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  rfl

-- summability of complex summand (from norm-summability)
lemma convSummandW_summable (u v : L2VF) (w : L2Sigma) (hw : IsGalerkinTest w) (i a : Fin 3) :
    Summable (fun kl : (Fin 3 → ℤ) × (Fin 3 → ℤ) => convSummandW u v (w : L2VF) i a kl.1 kl.2) :=
  (convSummandW_norm_summable u v w hw i a).of_norm


-- Bilinearity of convValW in u and v, via tsum splitting on convSummandW.
private lemma convSummandW_add_u (w : L2Sigma) (u u' v : L2VF) (i a : Fin 3) (kl : (Fin 3 → ℤ) × (Fin 3 → ℤ)) :
    convSummandW (u + u') v (w:L2VF) i a kl.1 kl.2
      = convSummandW u v (w:L2VF) i a kl.1 kl.2 + convSummandW u' v (w:L2VF) i a kl.1 kl.2 := by
  simp only [convSummandW, coeff_proj_add]; ring

private lemma convSummandW_smul_u (w : L2Sigma) (c : ℝ) (u v : L2VF) (i a : Fin 3) (kl : (Fin 3 → ℤ) × (Fin 3 → ℤ)) :
    convSummandW (c • u) v (w:L2VF) i a kl.1 kl.2
      = (c : ℂ) * convSummandW u v (w:L2VF) i a kl.1 kl.2 := by
  simp only [convSummandW, coeff_proj_smul]; ring

private lemma convSummandW_add_v (w : L2Sigma) (u v v' : L2VF) (i a : Fin 3) (kl : (Fin 3 → ℤ) × (Fin 3 → ℤ)) :
    convSummandW u (v + v') (w:L2VF) i a kl.1 kl.2
      = convSummandW u v (w:L2VF) i a kl.1 kl.2 + convSummandW u v' (w:L2VF) i a kl.1 kl.2 := by
  simp only [convSummandW, coeff_proj_add]; ring

private lemma convSummandW_smul_v (w : L2Sigma) (c : ℝ) (u v : L2VF) (i a : Fin 3) (kl : (Fin 3 → ℤ) × (Fin 3 → ℤ)) :
    convSummandW u (c • v) (w:L2VF) i a kl.1 kl.2
      = (c : ℂ) * convSummandW u v (w:L2VF) i a kl.1 kl.2 := by
  simp only [convSummandW, coeff_proj_smul]; ring

lemma convValW_add_u (w : L2Sigma) (hw : IsGalerkinTest w) (u u' v : L2VF) :
    convValW (u + u') v w = convValW u v w + convValW u' v w := by
  unfold convValW
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← Complex.add_re]
  refine congrArg Complex.re ?_
  rw [tsum_congr (fun kl => convSummandW_add_u w u u' v i a kl),
    Summable.tsum_add (convSummandW_summable u v w hw i a) (convSummandW_summable u' v w hw i a)]

lemma convValW_smul_u (w : L2Sigma) (c : ℝ) (u v : L2VF) :
    convValW (c • u) v w = c * convValW u v w := by
  unfold convValW
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [tsum_congr (fun kl => convSummandW_smul_u w c u v i a kl),
    tsum_mul_left, Complex.re_ofReal_mul]

lemma convValW_add_v (w : L2Sigma) (hw : IsGalerkinTest w) (u v v' : L2VF) :
    convValW u (v + v') w = convValW u v w + convValW u v' w := by
  unfold convValW
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← Complex.add_re]
  refine congrArg Complex.re ?_
  rw [tsum_congr (fun kl => convSummandW_add_v w u v v' i a kl),
    Summable.tsum_add (convSummandW_summable u v w hw i a) (convSummandW_summable u v' w hw i a)]

lemma convValW_smul_v (w : L2Sigma) (c : ℝ) (u v : L2VF) :
    convValW u (c • v) w = c * convValW u v w := by
  unfold convValW
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [tsum_congr (fun kl => convSummandW_smul_v w c u v i a kl),
    tsum_mul_left, Complex.re_ofReal_mul]



-- The bilinear LinearMap on L2Sigma (precompose convValW with the L2Sigma ↪ L2VF coercion).
noncomputable def convBilL2Sigma (w : L2Sigma) (hw : IsGalerkinTest w) :
    L2Sigma →ₗ[ℝ] L2Sigma →ₗ[ℝ] ℝ where
  toFun u :=
    { toFun := fun v => convValW (u : L2VF) (v : L2VF) w
      map_add' := fun v v' => by
        rw [show ((v + v' : L2Sigma) : L2VF) = (v:L2VF) + (v':L2VF) from rfl]
        exact convValW_add_v w hw (u:L2VF) (v:L2VF) (v':L2VF)
      map_smul' := fun c v => by
        rw [show ((c • v : L2Sigma) : L2VF) = c • (v:L2VF) from rfl]
        simpa using convValW_smul_v w c (u:L2VF) (v:L2VF) }
  map_add' u u' := by
    refine LinearMap.ext (fun v => ?_)
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]
    rw [show ((u + u' : L2Sigma) : L2VF) = (u:L2VF) + (u':L2VF) from rfl]
    exact convValW_add_u w hw (u:L2VF) (u':L2VF) (v:L2VF)
  map_smul' c u := by
    refine LinearMap.ext (fun v => ?_)
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, RingHom.id_apply, smul_eq_mul]
    rw [show ((c • u : L2Sigma) : L2VF) = c • (u:L2VF) from rfl]
    exact convValW_smul_u w c (u:L2VF) (v:L2VF)

-- The continuous bilinear (the BLT, no extension needed — bounded on all of L²×L²).
noncomputable def convBLTw (w : L2Sigma) (hw : IsGalerkinTest w) :
    L2Sigma →L[ℝ] L2Sigma →L[ℝ] ℝ :=
  LinearMap.mkContinuous₂ (convBilL2Sigma w hw) (convValW_bound w hw).choose (by
    intro u v
    have hb := (convValW_bound w hw).choose_spec.2 (u:L2VF) (v:L2VF)
    rw [Real.norm_eq_abs]
    exact hb)

@[simp]
lemma convBLTw_apply (w : L2Sigma) (hw : IsGalerkinTest w) (u v : L2Sigma) :
    convBLTw w hw u v = convValW (u : L2VF) (v : L2VF) w := rfl


-- IBP on the Fourier side: for div-free u and Galerkin tests v,w, the w-gradient form
-- equals the v-gradient form convFormFourier (the genuine convection value).
set_option maxHeartbeats 1000000 in
theorem convValW_eq_convFormFourier (u : L2Sigma) (v w : L2Sigma)
    (hv : IsGalerkinTest v) (hw : IsGalerkinTest w) :
    convValW (u : L2VF) (v : L2VF) w = convFormFourier u v w := by
  classical
  have hdiv : DivFreeL2 (u : L2VF) := (mem_L2Sigma_iff _).mp u.2
  have hvH1 : memH1VF (v : L2VF) := (galerkinTestSpan_subset_H1Sigma hv).2
  unfold convValW convFormFourier
  refine Finset.sum_congr rfl (fun i _ => ?_)
  -- summability of both forms (per a)
  have hsummW : ∀ a : Fin 3, Summable (fun kl : (Fin 3 → ℤ) × (Fin 3 → ℤ) =>
      convSummandW (u:L2VF) (v:L2VF) (w:L2VF) i a kl.1 kl.2) :=
    fun a => convSummandW_summable (u:L2VF) (v:L2VF) w hw i a
  have hsummV : ∀ a : Fin 3, Summable (fun kl : (Fin 3 → ℤ) × (Fin 3 → ℤ) =>
      convSummand (u:L2VF) (v:L2VF) (w:L2VF) i a kl.1 kl.2) :=
    fun a => convSummand_summable (u:L2VF) (v:L2VF) hvH1 w hw i a
  -- ∑_a (tsumW).re = ∑_a (tsumV).re  ⟸  ∑_a tsumW = ∑_a tsumV (then take re)
  rw [← Complex.re_sum, ← Complex.re_sum]
  refine congrArg Complex.re ?_
  -- combine the a-sums into a single tsum each (finite a-sum of summables)
  rw [← (hasSum_sum (fun a (_ : a ∈ Finset.univ) => (hsummW a).hasSum)).tsum_eq,
      ← (hasSum_sum (fun a (_ : a ∈ Finset.univ) => (hsummV a).hasSum)).tsum_eq]
  refine tsum_congr (fun kl => ?_)
  -- per (k,l): ∑_a convSummandW = ∑_a convSummand  (difference is killed by div-free)
  have hkey : ∑ a : Fin 3, convSummand (u:L2VF) (v:L2VF) (w:L2VF) i a kl.1 kl.2
      - ∑ a : Fin 3, convSummandW (u:L2VF) (v:L2VF) (w:L2VF) i a kl.1 kl.2
      = -(((2 * (Real.pi : ℂ) * Complex.I) *
          (mFourierCoeff3 (L2VF_projComponentC i (v:L2VF)) kl.2 *
           mFourierCoeff3 (L2VF_projComponentC i (w:L2VF)) (-(kl.1 + kl.2)))) *
        (∑ a : Fin 3, (kl.1 a : ℂ) * mFourierCoeff3 (L2VF_projComponentC a (u:L2VF)) kl.1)) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    simp only [convSummand, convSummandW]
    have : ((-(kl.1 + kl.2)) a : ℂ) = -((kl.1 a : ℂ) + (kl.2 a : ℂ)) := by
      simp only [Pi.neg_apply, Pi.add_apply]; push_cast; ring
    rw [this]; ring
  have hzero : ∑ a : Fin 3, convSummand (u:L2VF) (v:L2VF) (w:L2VF) i a kl.1 kl.2
      - ∑ a : Fin 3, convSummandW (u:L2VF) (v:L2VF) (w:L2VF) i a kl.1 kl.2 = 0 := by
    rw [hkey, hdiv kl.1, mul_zero, neg_zero]
  exact (sub_eq_zero.mp hzero).symm


-- convFormFourier collapses to the finite galerkinConvection on Vₙ.
set_option maxHeartbeats 1000000 in
theorem convFormFourier_eq_galerkin (n : ℕ) (u v w : L2Sigma)
    (hu : velocityProjection_n n (u : L2VF) = (u : L2VF))
    (hv : velocityProjection_n n (v : L2VF) = (v : L2VF))
    (hvtest : IsGalerkinTest v) (hwtest : IsGalerkinTest w) :
    convFormFourier u v w = galerkinConvection n (u : L2VF) (v : L2VF) (w : L2VF) := by
  classical
  have hvH1 : memH1VF (v : L2VF) := (galerkinTestSpan_subset_H1Sigma hvtest).2
  unfold convFormFourier galerkinConvection
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  refine congrArg Complex.re ?_
  -- the tsum over ℤ³×ℤ³ collapses to the box×box double finite sum
  have hsumm := convSummand_summable (u:L2VF) (v:L2VF) hvH1 w hwtest i a
  -- coeff supports
  have hUsupp : ∀ k, k ∉ fourierBox n → mFourierCoeff3 (L2VF_projComponentC a (u:L2VF)) k = 0 := by
    intro k hk
    have hcomm := velocityProjection_n_component_comm n (u:L2VF) a
    rw [hu] at hcomm
    conv_lhs => rw [hcomm]
    rw [ContinuousLinearMap.coe_restrictScalars', fourierProjection_n_mFourierCoeff, if_neg hk]
  have hVsupp : ∀ l, l ∉ fourierBox n → mFourierCoeff3 (L2VF_projComponentC i (v:L2VF)) l = 0 := by
    intro l hl
    have hcomm := velocityProjection_n_component_comm n (v:L2VF) i
    rw [hv] at hcomm
    conv_lhs => rw [hcomm]
    rw [ContinuousLinearMap.coe_restrictScalars', fourierProjection_n_mFourierCoeff, if_neg hl]
  -- tsum over product = double finite sum over box×box
  rw [tsum_eq_sum (s := fourierBox n ×ˢ fourierBox n) (fun kl hkl => ?_)]
  · rw [Finset.sum_product]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rfl
  · -- summand is 0 outside box×box
    simp only [Finset.mem_product, not_and_or] at hkl
    rcases hkl with hk | hl
    · simp only [convSummand, hUsupp kl.1 hk, zero_mul]
    · simp only [convSummand, hVsupp kl.2 hl]; ring

-- w-slot additivity/homogeneity of convValW (needed for convBLTgalerkin's w-linearity).
private lemma convSummandW_add_w (u v w w' : L2VF) (i a : Fin 3) (kl : (Fin 3 → ℤ) × (Fin 3 → ℤ)) :
    convSummandW u v (w + w') i a kl.1 kl.2
      = convSummandW u v w i a kl.1 kl.2 + convSummandW u v w' i a kl.1 kl.2 := by
  simp only [convSummandW, coeff_proj_add]; ring

private lemma convSummandW_smul_w (c : ℝ) (u v w : L2VF) (i a : Fin 3) (kl : (Fin 3 → ℤ) × (Fin 3 → ℤ)) :
    convSummandW u v (c • w) i a kl.1 kl.2
      = (c : ℂ) * convSummandW u v w i a kl.1 kl.2 := by
  simp only [convSummandW, coeff_proj_smul]; ring

lemma convValW_add_w (u v : L2VF) (w w' : L2Sigma) (hw : IsGalerkinTest w) (hw' : IsGalerkinTest w') :
    convValW u v ((w + w' : L2Sigma)) = convValW u v w + convValW u v w' := by
  unfold convValW
  simp only [Submodule.coe_add]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← Complex.add_re]
  refine congrArg Complex.re ?_
  rw [tsum_congr (fun kl => convSummandW_add_w u v (w:L2VF) (w':L2VF) i a kl),
    Summable.tsum_add (convSummandW_summable u v w hw i a) (convSummandW_summable u v w' hw' i a)]

lemma convValW_smul_w (c : ℝ) (u v : L2VF) (w : L2Sigma) :
    convValW u v ((c • w : L2Sigma)) = c * convValW u v w := by
  unfold convValW
  simp only [Submodule.coe_smul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [tsum_congr (fun kl => convSummandW_smul_w c u v (w:L2VF) i a kl),
    tsum_mul_left, Complex.re_ofReal_mul]



/-! ### CLOSURE: galerkinTestSpan ⊆ IsGalerkinTest -/

lemma velocityProjection_n_eq_of_le {n m : ℕ} (hnm : n ≤ m) (u : L2VF)
    (hu : velocityProjection_n n u = u) : velocityProjection_n m u = u := by
  refine L2VF_ext_componentC_mFourierCoeff (fun j k => ?_)
  rw [velocityProjection_n_component_comm,
    ContinuousLinearMap.coe_restrictScalars', fourierProjection_n_mFourierCoeff]
  by_cases hk : k ∈ fourierBox m
  · rw [if_pos hk]
  · rw [if_neg hk]
    have hkn : k ∉ fourierBox n := fun hh => hk (fourierBox_monotone hnm hh)
    exact (coeff_zero_outside_box n u hu j k hkn).symm

lemma isGalerkinTest_add {u v : L2Sigma} (hu : IsGalerkinTest u) (hv : IsGalerkinTest v) :
    IsGalerkinTest (u + v) := by
  obtain ⟨n, hn⟩ := hu; obtain ⟨m, hm⟩ := hv
  exact ⟨max n m, by
    rw [show ((u + v : L2Sigma) : L2VF) = (u:L2VF) + (v:L2VF) from rfl, map_add,
      velocityProjection_n_eq_of_le (le_max_left n m) _ hn,
      velocityProjection_n_eq_of_le (le_max_right n m) _ hm]⟩

lemma isGalerkinTest_smul {u : L2Sigma} (c : ℝ) (hu : IsGalerkinTest u) :
    IsGalerkinTest (c • u) := by
  obtain ⟨n, hn⟩ := hu
  exact ⟨n, by rw [show ((c • u : L2Sigma) : L2VF) = c • (u:L2VF) from rfl, map_smul, hn]⟩

lemma isGalerkinTest_zero : IsGalerkinTest (0 : L2Sigma) :=
  ⟨0, by rw [show ((0 : L2Sigma) : L2VF) = 0 from rfl, map_zero]⟩

theorem mem_galerkinTestSpan_isTest {s : L2Sigma} (hs : s ∈ galerkinTestSpan) : IsGalerkinTest s :=
  Submodule.span_induction (p := fun x _ => IsGalerkinTest x)
    (fun x hx => hx) isGalerkinTest_zero
    (fun x y _ _ hx hy => isGalerkinTest_add hx hy)
    (fun c x _ hx => isGalerkinTest_smul c hx) hs

/-- **`convBLTgalerkin`.** Jointly continuous bilinear form
`L2Sigma →L[ℝ] L2Sigma →L[ℝ] ℝ` extending `(u, v) ↦ convFormFourier u v w` for a
fixed Galerkin test `w : galerkinTestSpan`.

Constructed by extending the Galerkin-test bound through the H¹/Galerkin-test slice. -/
noncomputable def convBLTgalerkin (w : galerkinTestSpan) :
    L2Sigma →L[ℝ] L2Sigma →L[ℝ] ℝ :=
  convBLTw (w : L2Sigma) (mem_galerkinTestSpan_isTest w.2)

@[simp] theorem convBLTgalerkin_apply (w : galerkinTestSpan) (u v : L2Sigma) :
    convBLTgalerkin w u v = convValW (u : L2VF) (v : L2VF) (w : L2Sigma) := rfl

/-- **`convBLTgalerkin_span_linear`.** The map `w ↦ convBLTgalerkin w` is
ℝ-linear over `galerkinTestSpan`.

Linearity follows by dense agreement on the Galerkin-test square, using `convFormFourier`'s
linearity in the third slot. -/
noncomputable def convBLTgalerkinLin :
    galerkinTestSpan →ₗ[ℝ] (L2Sigma →L[ℝ] L2Sigma →L[ℝ] ℝ) where
  toFun := convBLTgalerkin
  map_add' s s' := by
    refine ContinuousLinearMap.ext (fun u => ContinuousLinearMap.ext (fun v => ?_))
    simp only [convBLTgalerkin_apply, ContinuousLinearMap.add_apply]
    exact convValW_add_w (u:L2VF) (v:L2VF) (s:L2Sigma) (s':L2Sigma)
      (mem_galerkinTestSpan_isTest s.2) (mem_galerkinTestSpan_isTest s'.2)
  map_smul' c s := by
    refine ContinuousLinearMap.ext (fun u => ContinuousLinearMap.ext (fun v => ?_))
    simp only [convBLTgalerkin_apply, ContinuousLinearMap.smul_apply, RingHom.id_apply, smul_eq_mul]
    exact convValW_smul_w c (u:L2VF) (v:L2VF) (s:L2Sigma)

/-! #### T4b — overlap agreement on `𝒢 ⊗ 𝒢` -/

/-- **`convBLTgalerkin_overlap`.** For `s, s' ∈ 𝒢` and any `u`,
`convBLTgalerkin s' u (s : L2Sigma) = -convBLTgalerkin s u (s' : L2Sigma)`.

This is the torus analog of `convBLTspan_overlap`, following from `convFormFourier_antisymm_galerkinTest`
extended to all `u` by density, exactly as R3. -/
private theorem convBLTgalerkin_overlap (u : L2Sigma) (s s' : galerkinTestSpan) :
    convBLTgalerkin s' u (s : L2Sigma) = -convBLTgalerkin s u (s' : L2Sigma) := by
  have hs : IsGalerkinTest (s : L2Sigma) := mem_galerkinTestSpan_isTest s.2
  have hs' : IsGalerkinTest (s' : L2Sigma) := mem_galerkinTestSpan_isTest s'.2
  rw [convBLTgalerkin_apply, convBLTgalerkin_apply,
    convValW_eq_convFormFourier u (s : L2Sigma) (s' : L2Sigma) hs hs',
    convValW_eq_convFormFourier u (s' : L2Sigma) (s : L2Sigma) hs' hs,
    convFormFourier_antisymm_galerkinTest u (s : L2Sigma) (s' : L2Sigma) hs hs']

/-! ### T5–T8 — the shared tensor/edge-gluing instantiation (issue #111 PR-1)

`antisymmetrizer`/`detExtend` and the `convFormL2_def`/`_def_eq`/`_multilinear`/`_antisymm`
tower are the generic `LerayHopf.TensorEdgeGluing` construction instantiated at
`(L2Sigma, galerkinTestSpan, convBLTgalerkinLin, convBLTgalerkin_overlap)`. Public
names/statements are unchanged (Hard Rule #2); the previously ~550-line T3/T5–T8 block now
lives once in `LerayHopf/Analysis/TensorEdgeGluing.lean`. -/

/-- The antisymmetrizer `A := (id − swap)/2` on `L²_σ ⊗ L²_σ`. -/
noncomputable def antisymmetrizer :
    TensorProduct ℝ L2Sigma L2Sigma →ₗ[ℝ] TensorProduct ℝ L2Sigma L2Sigma :=
  LerayHopf.TensorEdgeGluing.antisymmetrizer (X := L2Sigma)

/-- **`detExtend` [proved from `psiD` / `gInv` / `antisymmetrizer`].** The determined
extension `L²_σ →ₗ (L²_σ ⊗ L²_σ) →ₗ ℝ`. -/
noncomputable def detExtend :
    L2Sigma →ₗ[ℝ] (TensorProduct ℝ L2Sigma L2Sigma) →ₗ[ℝ] ℝ :=
  LerayHopf.TensorEdgeGluing.detExtend galerkinTestSpan convBLTgalerkinLin convBLTgalerkin_overlap

/-- **`convFormL2_def` (`b`).** The determined trilinear convection
form: `b u v w := detExtend u (v ⊗ₜ w)`. -/
noncomputable def convFormL2_def (u v w : L2Sigma) : ℝ :=
  LerayHopf.TensorEdgeGluing.convFormL2_def galerkinTestSpan convBLTgalerkinLin
    convBLTgalerkin_overlap u v w

@[simp]
theorem convFormL2_def_eq (u v w : L2Sigma) :
    convFormL2_def u v w = detExtend u (v ⊗ₜ[ℝ] w) :=
  LerayHopf.TensorEdgeGluing.convFormL2_def_eq galerkinTestSpan convBLTgalerkinLin
    convBLTgalerkin_overlap u v w

/-- **`convFormL2_antisymm` [proved from `antisymmetrizer_tmul_swap`].**
`b u v w = − b u w v` for all `u v w`. -/
theorem convFormL2_antisymm (u v w : L2Sigma) :
    convFormL2_def u v w = -convFormL2_def u w v :=
  LerayHopf.TensorEdgeGluing.convFormL2_antisymm galerkinTestSpan convBLTgalerkinLin
    convBLTgalerkin_overlap u v w

/-- **`convFormL2_multilinear` [proved from `detExtend` linearity].** There exists a genuine
ℝ-trilinear map `B` with `b u v w = B u v w`. -/
theorem convFormL2_multilinear :
    ∃ B : L2Sigma →ₗ[ℝ] L2Sigma →ₗ[ℝ] L2Sigma →ₗ[ℝ] ℝ,
      ∀ (u v w : L2Sigma), convFormL2_def u v w = B u v w :=
  LerayHopf.TensorEdgeGluing.convFormL2_multilinear galerkinTestSpan convBLTgalerkinLin
    convBLTgalerkin_overlap

/-- **Bridge: on a Galerkin test `w`, the determined form equals the genuine bilinear.**
Derived from the generic `TensorEdgeGluing.detExtend_edge3_eq` (the algebraic core) composed
with `convBLTgalerkin_apply` (the lane-specific bridge to `convValW`). -/
theorem convFormL2_def_eq_convValW (u v w : L2Sigma) (hw : IsGalerkinTest w) :
    convFormL2_def u v w = convValW (u : L2VF) (v : L2VF) (w : L2Sigma) := by
  have hwspan : w ∈ galerkinTestSpan := subset_galerkinTestSpan hw
  let sw : galerkinTestSpan := ⟨w, hwspan⟩
  have hswcoe : (sw : L2Sigma) = w := rfl
  show LerayHopf.TensorEdgeGluing.detExtend galerkinTestSpan convBLTgalerkinLin
      convBLTgalerkin_overlap u ((v : L2Sigma) ⊗ₜ[ℝ] w)
    = convValW (u : L2VF) (v : L2VF) (w : L2Sigma)
  rw [← hswcoe,
    LerayHopf.TensorEdgeGluing.detExtend_edge3_eq galerkinTestSpan convBLTgalerkinLin
      convBLTgalerkin_overlap u v sw]
  show convBLTgalerkin sw u v = convValW (u : L2VF) (v : L2VF) (w : L2Sigma)
  rw [convBLTgalerkin_apply, hswcoe]

/-- **`convFormL2_cont_fixedTest` [proved].** For a Galerkin test `w`, `(u, v) ↦ b u v w` is
jointly L²-continuous: on the determined slice it equals `convBLTw w`, a `ContinuousLinearMap`. -/
theorem convFormL2_cont_fixedTest (w : L2Sigma) (hw : IsGalerkinTest w) :
    Continuous (fun p : L2Sigma × L2Sigma => convFormL2_def p.1 p.2 w) := by
  have heq : (fun p : L2Sigma × L2Sigma => convFormL2_def p.1 p.2 w)
      = (fun p : L2Sigma × L2Sigma => convBLTw w hw p.1 p.2) := by
    funext p
    rw [convFormL2_def_eq_convValW p.1 p.2 w hw, convBLTw_apply]
  rw [heq]
  exact (convBLTw w hw).continuous₂

/-- **`convFormL2_bound_galerkinTest`.** For Galerkin tests `u, v, w`,
`|b u v w| ≤ C(w) · ‖u‖ · ‖v‖` for some `C(w) ≥ 0`.

This transfers the bilinear bound from `convBLTgalerkin`, built from
`galerkinConvection_bound` / `convSummand_summable`. -/
theorem convFormL2_bound_galerkinTest (w : L2Sigma) (hw : IsGalerkinTest w) :
    ∃ C : ℝ, ∀ (u v : L2Sigma), IsGalerkinTest u → IsGalerkinTest v →
      |convFormL2_def u v w| ≤ C * ‖(u : L2VF)‖ * ‖(v : L2VF)‖ := by
  obtain ⟨C, _, hC⟩ := convValW_bound w hw
  refine ⟨C, fun u v _ _ => ?_⟩
  rw [convFormL2_def_eq_convValW u v w hw]
  exact hC (u : L2VF) (v : L2VF)

/-- **`convFormL2_galerkin_pin`.** On Galerkin subspaces `Vₙ`,
`b` restricts to the finite box-truncated form `galerkinConvection n`.

This follows from `convFormFourier` matching `galerkinConvection` on the finite box plus the
determination identity on the Galerkin-test slice. -/
theorem convFormL2_galerkin_pin :
    ∀ (n : ℕ) (u v w : L2Sigma),
      velocityProjection_n n (u : L2VF) = (u : L2VF) →
      velocityProjection_n n (v : L2VF) = (v : L2VF) →
      velocityProjection_n n (w : L2VF) = (w : L2VF) →
      convFormL2_def u v w = galerkinConvection n (u : L2VF) (v : L2VF) (w : L2VF) := by
  intro n u v w hu hv hw
  have hvtest : IsGalerkinTest v := ⟨n, hv⟩
  have hwtest : IsGalerkinTest w := ⟨n, hw⟩
  rw [convFormL2_def_eq_convValW u v w hwtest,
    convValW_eq_convFormFourier u v w hvtest hwtest,
    convFormFourier_eq_galerkin n u v w hu hv hvtest hwtest]

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

/-- **`torusConvectionGap_holds`.** Assembly of the `TorusConvectionGap` structure from the
determined-form construction.  All seven fields are supplied by the proved declarations above. -/
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
Re-exports `TorusConvectionExtension.torusConvectionGap_holds` under the original axiom name.
Being a theorem (not an axiom), it does NOT appear in `#print axioms` output. -/
theorem torusConvectionGap_exists : Nonempty TorusConvectionGap :=
  LerayHopf.TorusConvectionExtension.torusConvectionGap_holds

/-- **T³ NS forms exist — de-axiomatized via the proved operator (torus #53).**
Relocated here from `TorusConvectionForm.lean` (where it was routed through the now-proved
`torusConvectionGap_exists`).  `Torus3NSForms_of_gap` is available transitively via the
`TorusConvectionForm` import. -/
theorem torus3_NSForms_exists : Nonempty Torus3NSForms :=
  torusConvectionGap_exists.elim fun g => Torus3NSForms_of_gap g

end LerayHopf
