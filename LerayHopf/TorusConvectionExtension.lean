import LerayHopf.TorusEnergyConvection
import LerayHopf.TorusGalerkinScheme
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

/-- **`convBLTgalerkin` [scaffold].** Jointly continuous bilinear form
`L2Sigma →L[ℝ] L2Sigma →L[ℝ] ℝ` extending `(u, v) ↦ convFormFourier u v w` for a
fixed Galerkin test `w : galerkinTestSpan`.

PR-2 prover obligation: construct the BLT extension via the H¹ density of Galerkin tests
and `convSummand_summable` / `galerkinConvection_bound`. -/
noncomputable def convBLTgalerkin (w : galerkinTestSpan) :
    L2Sigma →L[ℝ] L2Sigma →L[ℝ] ℝ :=
  convBLTw (w : L2Sigma) (mem_galerkinTestSpan_isTest w.2)

@[simp] theorem convBLTgalerkin_apply (w : galerkinTestSpan) (u v : L2Sigma) :
    convBLTgalerkin w u v = convValW (u : L2VF) (v : L2VF) (w : L2Sigma) := rfl

/-- **`convBLTgalerkin_span_linear` [scaffold].** The map `w ↦ convBLTgalerkin w` is
ℝ-linear over `galerkinTestSpan`.

PR-2 prover obligation: prove linearity via the dense-agreement argument (same dense
Galerkin-test × Galerkin-test square), using `convFormFourier`'s linearity in the third slot. -/
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
  have hs : IsGalerkinTest (s : L2Sigma) := mem_galerkinTestSpan_isTest s.2
  have hs' : IsGalerkinTest (s' : L2Sigma) := mem_galerkinTestSpan_isTest s'.2
  rw [convBLTgalerkin_apply, convBLTgalerkin_apply,
    convValW_eq_convFormFourier u (s : L2Sigma) (s' : L2Sigma) hs hs',
    convValW_eq_convFormFourier u (s' : L2Sigma) (s : L2Sigma) hs' hs,
    convFormFourier_antisymm_galerkinTest u (s : L2Sigma) (s' : L2Sigma) hs hs']

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

/-- **Bridge: on a Galerkin test `w`, the determined form equals the genuine bilinear.** -/
theorem convFormL2_def_eq_convValW (u v w : L2Sigma) (hw : IsGalerkinTest w) :
    convFormL2_def u v w = convValW (u : L2VF) (v : L2VF) (w : L2Sigma) := by
  have hwspan : w ∈ galerkinTestSpan := subset_galerkinTestSpan hw
  let sw : galerkinTestSpan := ⟨w, hwspan⟩
  have hswcoe : (sw : L2Sigma) = w := rfl
  rw [convFormL2_def_eq]
  show (psiD u) (gInv (antisymmetrizer (v ⊗ₜ[ℝ] w))) = convValW (u:L2VF) (v:L2VF) w
  rw [antisymmetrizer_tmul, map_smul, map_sub, map_smul, map_sub]
  have hmem3 : (v : L2Sigma) ⊗ₜ[ℝ] (sw : L2Sigma) ∈ detDomain :=
    Submodule.mem_sup_right (tmul_mem_edgeSlot3 v sw)
  have hmem2 : (sw : L2Sigma) ⊗ₜ[ℝ] (v : L2Sigma) ∈ detDomain :=
    Submodule.mem_sup_left (tmul_mem_edgeSlot2 sw v)
  rw [hswcoe] at hmem3 hmem2
  rw [show gInv ((v:L2Sigma) ⊗ₜ[ℝ] w) = ⟨_, hmem3⟩ from gInv_eq_of_mem _ hmem3,
      show gInv (w ⊗ₜ[ℝ] (v:L2Sigma)) = ⟨_, hmem2⟩ from gInv_eq_of_mem _ hmem2]
  rw [show (⟨(v:L2Sigma) ⊗ₜ[ℝ] w, hmem3⟩ : detDomain)
        = ⟨(v:L2Sigma) ⊗ₜ[ℝ] (sw:L2Sigma), Submodule.mem_sup_right (tmul_mem_edgeSlot3 v sw)⟩ from rfl,
      show (⟨w ⊗ₜ[ℝ] (v:L2Sigma), hmem2⟩ : detDomain)
        = ⟨(sw:L2Sigma) ⊗ₜ[ℝ] (v:L2Sigma), Submodule.mem_sup_left (tmul_mem_edgeSlot2 sw v)⟩ from rfl,
      psiD_edge3_value u v sw, psiD_edge2_value u v sw]
  rw [convBLTgalerkin_apply, hswcoe]
  rw [sub_neg_eq_add]
  show (2⁻¹ : ℝ) • (convValW (u:L2VF) (v:L2VF) w + convValW (u:L2VF) (v:L2VF) w)
    = convValW (u:L2VF) (v:L2VF) w
  rw [smul_eq_mul]; ring

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

/-- **`convFormL2_bound_galerkinTest` [scaffold].** For Galerkin tests `u, v, w`,
`|b u v w| ≤ C(w) · ‖u‖ · ‖v‖` for some `C(w) ≥ 0`.

PR-2 prover obligation: transfer the bilinear bound from `convBLTgalerkin` (which
is built from `galerkinConvection_bound` / `convSummand_summable`). -/
theorem convFormL2_bound_galerkinTest (w : L2Sigma) (hw : IsGalerkinTest w) :
    ∃ C : ℝ, ∀ (u v : L2Sigma), IsGalerkinTest u → IsGalerkinTest v →
      |convFormL2_def u v w| ≤ C * ‖(u : L2VF)‖ * ‖(v : L2VF)‖ := by
  obtain ⟨C, _, hC⟩ := convValW_bound w hw
  refine ⟨C, fun u v _ _ => ?_⟩
  rw [convFormL2_def_eq_convValW u v w hw]
  exact hC (u : L2VF) (v : L2VF)

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
