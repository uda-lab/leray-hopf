import LerayHopf.R3.CurlDensity
import LerayHopf.R3.Regularity

namespace LerayHopf

open MeasureTheory SchwartzMap FourierTransform
open scoped Topology RealInnerProductSpace FourierTransform

/-!
# LerayHopf.R3.CurlDensityH1 — H¹ curl approximation at Schwartz div-free targets

**Campaign:** discharge `galerkin_limit_passage_R3` (issue #4, last project axiom).

This file contains the new analytic kernel `curl_approx_H1`: every Schwartz divergence-free
field `w ∈ L2Sigma_R3` is approximated in the `L² + viscousFormSq` (H¹ graph) seminorm by a
curl of a Schwartz potential `ψ : Fin 3 → 𝓢(ℝ³, ℝ)`.

**Proof route (Fourier low-frequency cutoff, issue #93 §1b / PR-2):**
1. `ŵ` is transverse (`mem_sigma_iff_fourier_transverse`, `CurlDensity.lean:952`, proved).
2. Set `ψ̂_δ(ξ) := χ_δ(ξ)·(ξ × ŵ(ξ))/(2πi‖ξ‖²)` with smooth radial cutoff `χ_δ`
   (`0` near `0`, `1` on `‖ξ‖ ≥ δ`).
3. `𝓕(curl ψ_δ) = χ_δ·ŵ` (BAC-CAB + transversality), so L² and weighted-L² (H¹) errors
   are `∫_{‖ξ‖≤δ}(1+W)|ŵ|² → 0`.
4. Symbol is Schwartz (smooth cutoff kills the singularity); realized via
   `FourierTransform.fourierCLE` and the Hermitian-reality machinery in `CurlDensity.lean`.

**Toolkit anchors (all verified in spike S7 of issue #93):**
- `FourierTransform.fourierCLE` — Fourier isomorphism on `SchwartzMap`
- `mem_sigma_iff_fourier_transverse` — `CurlDensity.lean:952`
- `curlSchwartzL2` — `SchwartzDivFreeBasis.lean:203`
- `viscousFormSq_R3` — `Regularity.lean:140`
-/

/-! ## Stage 1 — Yukawa-regularized Schwartz potential symbol

Given the Fourier transforms `ŵ = wh` of the (complexified) Schwartz components of a
divergence-free `w`, the exact vector potential symbol solving `curl ψ = w` is
`ψ̂_k(ξ) = -(2π i ‖ξ‖²)⁻¹ (ξ × ŵ)_k`, singular at `ξ = 0`.  We regularize by replacing
`‖ξ‖²` with `a² + ‖ξ‖²` (`a > 0`): the denominator is now bounded below by `a² > 0`, so the
multiplier `(a² + ‖ξ‖²)⁻¹` is smooth and of temperate growth (no cutoff needed), and the
resulting curl Fourier symbol is `‖ξ‖²/(a² + ‖ξ‖²) · ŵ`, which `→ ŵ` as `a → 0`. -/

/-- Local complexification of a real Schwartz map (the CurlDensity `schwartzC` is private). -/
private noncomputable def cxifyH1 (f : SchwartzMap Domain3 ℝ) : SchwartzMap Domain3 ℂ :=
  f.postcompCLM (RCLike.ofRealCLM (K := ℂ))

private theorem cxifyH1_apply (f : SchwartzMap Domain3 ℝ) (x : Domain3) :
    cxifyH1 f x = (f x : ℂ) := rfl

/-- The coordinate multiplier `ξ ↦ (ξ m : ℂ)` has temperate growth (it is a CLM). -/
private theorem hasTemperateGrowth_coordC (m : Fin 3) :
    Function.HasTemperateGrowth (fun ξ : Domain3 => ((ξ m : ℝ) : ℂ)) := by
  have hproj : Function.HasTemperateGrowth (fun ξ : Domain3 => (ξ m : ℝ)) := by
    have := (EuclideanSpace.proj (𝕜 := ℝ) m).hasTemperateGrowth
    simpa using this
  exact Complex.ofRealCLM.hasTemperateGrowth.comp hproj

/-- The Yukawa multiplier `ξ ↦ (a² + ‖ξ‖²)⁻¹`. -/
private noncomputable def yukawaMul (a : ℝ) : Domain3 → ℝ := fun ξ => (a ^ 2 + ‖ξ‖ ^ 2)⁻¹

/-- The Yukawa multiplier has temperate growth (`a > 0` makes the denominator smooth and
bounded below): `(a² + ‖ξ‖²)⁻¹ = a⁻² · (1 + ‖a⁻¹ • ξ‖²)^(-1)`. -/
private theorem hasTemperateGrowth_yukawaMul (a : ℝ) (ha : 0 < a) :
    Function.HasTemperateGrowth (yukawaMul a) := by
  have hane : a ≠ 0 := ne_of_gt ha
  have hinner : Function.HasTemperateGrowth (fun ξ : Domain3 => a⁻¹ • ξ) := by
    have h := ((a⁻¹ : ℝ) • ContinuousLinearMap.id ℝ Domain3).hasTemperateGrowth
    convert h using 1
    funext ξ; simp
  have houter : Function.HasTemperateGrowth (fun x : Domain3 => (1 + ‖x‖ ^ 2) ^ (-1 : ℝ)) :=
    Function.hasTemperateGrowth_one_add_norm_sq_rpow Domain3 (-1)
  have hcomp : Function.HasTemperateGrowth
      (fun ξ : Domain3 => (1 + ‖a⁻¹ • ξ‖ ^ 2) ^ (-1 : ℝ)) := by
    have := houter.comp hinner
    simpa only [Function.comp_def] using this
  have hprod : Function.HasTemperateGrowth
      (fun ξ : Domain3 => a⁻¹ ^ 2 * (1 + ‖a⁻¹ • ξ‖ ^ 2) ^ (-1 : ℝ)) :=
    (Function.HasTemperateGrowth.const (a⁻¹ ^ 2 : ℝ)).mul hcomp
  have heq : yukawaMul a = fun ξ : Domain3 => a⁻¹ ^ 2 * (1 + ‖a⁻¹ • ξ‖ ^ 2) ^ (-1 : ℝ) := by
    funext ξ
    have hnorm : ‖a⁻¹ • ξ‖ ^ 2 = a⁻¹ ^ 2 * ‖ξ‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ) < a⁻¹), mul_pow]
    rw [yukawaMul, Real.rpow_neg_one, hnorm]
    have h2 : (1:ℝ) + a⁻¹ ^ 2 * ‖ξ‖ ^ 2 ≠ 0 := by positivity
    have h3 : (a:ℝ) ^ 2 + ‖ξ‖ ^ 2 ≠ 0 := by positivity
    rw [eq_comm]
    field_simp
  rw [heq]; exact hprod

/-- The complex Schwartz-symbol multiplier `ξ ↦ -(2π i)⁻¹ (a² + ‖ξ‖²)⁻¹`. -/
private noncomputable def symbolMul (a : ℝ) : Domain3 → ℂ :=
  fun ξ => (-(2 * Real.pi * Complex.I)⁻¹) * ((yukawaMul a ξ : ℝ) : ℂ)

private theorem hasTemperateGrowth_symbolMul (a : ℝ) (ha : 0 < a) :
    Function.HasTemperateGrowth (symbolMul a) := by
  have hy : Function.HasTemperateGrowth (fun ξ : Domain3 => ((yukawaMul a ξ : ℝ) : ℂ)) :=
    Complex.ofRealCLM.hasTemperateGrowth.comp (hasTemperateGrowth_yukawaMul a ha)
  exact (Function.HasTemperateGrowth.const (-(2 * Real.pi * Complex.I)⁻¹)).mul hy

/-- The cross-product symbol `(ξ × ŵ)_k = ξ_{k+1} ŵ_{k+2} − ξ_{k+2} ŵ_{k+1}` as a Schwartz map. -/
private noncomputable def crossHatOf (wh : Fin 3 → SchwartzMap Domain3 ℂ) (k : Fin 3) :
    SchwartzMap Domain3 ℂ :=
  SchwartzMap.smulLeftCLM ℂ (fun ξ => ((ξ (k + 1) : ℝ) : ℂ)) (wh (k + 2))
    - SchwartzMap.smulLeftCLM ℂ (fun ξ => ((ξ (k + 2) : ℝ) : ℂ)) (wh (k + 1))

private theorem crossHatOf_apply (wh : Fin 3 → SchwartzMap Domain3 ℂ) (k : Fin 3) (ξ : Domain3) :
    crossHatOf wh k ξ
      = (ξ (k + 1) : ℂ) * wh (k + 2) ξ - (ξ (k + 2) : ℂ) * wh (k + 1) ξ := by
  rw [crossHatOf, SchwartzMap.sub_apply,
    SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_coordC (k + 1)),
    SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_coordC (k + 2))]
  simp [smul_eq_mul]

/-- The regularized potential symbol `ψ̂_k = symbolMul · (ξ × ŵ)_k` as a Schwartz map. -/
private noncomputable def symbolHatOf (a : ℝ) (ha : 0 < a) (wh : Fin 3 → SchwartzMap Domain3 ℂ)
    (k : Fin 3) : SchwartzMap Domain3 ℂ :=
  SchwartzMap.smulLeftCLM ℂ (symbolMul a) (crossHatOf wh k)

private theorem symbolHatOf_apply (a : ℝ) (ha : 0 < a) (wh : Fin 3 → SchwartzMap Domain3 ℂ)
    (k : Fin 3) (ξ : Domain3) :
    symbolHatOf a ha wh k ξ = symbolMul a ξ * crossHatOf wh k ξ := by
  rw [symbolHatOf, SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_symbolMul a ha)]
  rw [smul_eq_mul]

/-! ### Reality machinery (local re-proofs; the CurlDensity versions are private) -/

/-- **Fourier of a Hermitian Schwartz function is real-valued** (local copy of the private
`CurlDensity.fourier_hermitian_real`). -/
private theorem fourierH1_hermitian_real
    (g : SchwartzMap Domain3 ℂ)
    (hg : ∀ v : Domain3, g (-v) = (starRingEnd ℂ) (g v)) (ξ : Domain3) :
    (starRingEnd ℂ) ((𝓕 g : SchwartzMap Domain3 ℂ) ξ) = (𝓕 g : SchwartzMap Domain3 ℂ) ξ := by
  have hcoe : ((𝓕 g : SchwartzMap Domain3 ℂ) : Domain3 → ℂ) = 𝓕 ((g : Domain3 → ℂ)) :=
    SchwartzMap.fourier_coe g
  rw [show (𝓕 g : SchwartzMap Domain3 ℂ) ξ = 𝓕 ((g : Domain3 → ℂ)) ξ from congrFun hcoe ξ]
  rw [Real.fourier_eq, ← integral_conj]
  have hconj : (∫ v : Domain3, (starRingEnd ℂ) ((Real.fourierChar (-(inner ℝ v ξ : ℝ))) • g v)
        ∂(volume : Measure Domain3))
      = ∫ v : Domain3, (Real.fourierChar (-(inner ℝ (-v) ξ : ℝ))) • g (-v)
        ∂(volume : Measure Domain3) := by
    refine integral_congr_ae ?_
    filter_upwards with v
    simp only [Circle.smul_def, smul_eq_mul, inner_neg_left, map_mul, neg_neg]
    rw [hg v]
    rw [← Circle.coe_inv_eq_conj, ← AddChar.map_neg_eq_inv, neg_neg]
  rw [hconj]
  rw [integral_neg_eq_self (fun v => (Real.fourierChar (-(inner ℝ v ξ : ℝ))) • g v)
    (volume : Measure Domain3)]

/-- **Fourier of a complexified real Schwartz function is Hermitian** (local copy of the private
`CurlDensity.fourier_schwartzC_hermitian`). -/
private theorem fourierH1_cxify_hermitian (φ : SchwartzMap Domain3 ℝ) (ξ : Domain3) :
    (𝓕 (cxifyH1 φ) : SchwartzMap Domain3 ℂ) (-ξ)
      = (starRingEnd ℂ) ((𝓕 (cxifyH1 φ) : SchwartzMap Domain3 ℂ) ξ) := by
  have hcoe : ((𝓕 (cxifyH1 φ) : SchwartzMap Domain3 ℂ) : Domain3 → ℂ)
        = 𝓕 ((cxifyH1 φ : Domain3 → ℂ)) := SchwartzMap.fourier_coe (cxifyH1 φ)
  rw [show (𝓕 (cxifyH1 φ) : SchwartzMap Domain3 ℂ) (-ξ)
        = 𝓕 ((cxifyH1 φ : Domain3 → ℂ)) (-ξ) from congrFun hcoe (-ξ),
    show (𝓕 (cxifyH1 φ) : SchwartzMap Domain3 ℂ) ξ
        = 𝓕 ((cxifyH1 φ : Domain3 → ℂ)) ξ from congrFun hcoe ξ]
  rw [Real.fourier_eq, Real.fourier_eq, ← integral_conj]
  refine integral_congr_ae ?_
  filter_upwards with v
  simp only [Circle.smul_def, smul_eq_mul, inner_neg_right, map_mul, cxifyH1_apply,
    Complex.conj_ofReal, neg_neg]
  rw [← Circle.coe_inv_eq_conj, ← AddChar.map_neg_eq_inv, neg_neg]

/-! ### The real potential and its Fourier transform -/

/-- The Yukawa-regularized **real** vector potential `ψ_k = Re(𝓕⁻ ψ̂_k)`. -/
private noncomputable def potOf (a : ℝ) (ha : 0 < a) (wh : Fin 3 → SchwartzMap Domain3 ℂ)
    (hHerm : ∀ b : Fin 3, ∀ v : Domain3, wh b (-v) = (starRingEnd ℂ) (wh b v))
    (k : Fin 3) : SchwartzMap Domain3 ℝ :=
  (𝓕⁻ (symbolHatOf a ha wh k)).postcompCLM (RCLike.reCLM (K := ℂ))

/-- The potential symbol is Hermitian: `ψ̂_k(-ξ) = conj(ψ̂_k ξ)`. -/
private theorem symbolHatOf_hermitian (a : ℝ) (ha : 0 < a) (wh : Fin 3 → SchwartzMap Domain3 ℂ)
    (hHerm : ∀ b : Fin 3, ∀ v : Domain3, wh b (-v) = (starRingEnd ℂ) (wh b v)) (k : Fin 3)
    (ξ : Domain3) :
    symbolHatOf a ha wh k (-ξ) = (starRingEnd ℂ) (symbolHatOf a ha wh k ξ) := by
  rw [symbolHatOf_apply, symbolHatOf_apply, crossHatOf_apply, crossHatOf_apply]
  -- `symbolMul a` is anti-Hermitian (imaginary × even), the cross symbol is anti-Hermitian.
  have hyuk : yukawaMul a (-ξ) = yukawaMul a ξ := by
    rw [yukawaMul, yukawaMul, norm_neg]
  have hc2 : (starRingEnd ℂ) (2 * Real.pi * Complex.I) = -(2 * Real.pi * Complex.I) := by
    rw [map_mul, map_mul, Complex.conj_I, Complex.conj_ofReal,
      show ((2:ℂ)) = ((2:ℝ):ℂ) by norm_num, Complex.conj_ofReal]
    ring
  have hmul : symbolMul a (-ξ) = -(starRingEnd ℂ) (symbolMul a ξ) := by
    rw [symbolMul, symbolMul, hyuk, map_mul, map_neg, map_inv₀, hc2, Complex.conj_ofReal]
    ring
  rw [hmul]
  simp only [PiLp.neg_apply]
  rw [hHerm (k + 2) ξ, hHerm (k + 1) ξ]
  push_cast
  simp only [map_sub, map_mul, Complex.conj_ofReal, map_neg]
  ring

/-- The real potential's complexification equals `𝓕⁻ ψ̂_k` (since `ψ̂_k` is Hermitian). -/
private theorem cxify_potOf (a : ℝ) (ha : 0 < a) (wh : Fin 3 → SchwartzMap Domain3 ℂ)
    (hHerm : ∀ b : Fin 3, ∀ v : Domain3, wh b (-v) = (starRingEnd ℂ) (wh b v)) (k : Fin 3) :
    cxifyH1 (potOf a ha wh hHerm k) = 𝓕⁻ (symbolHatOf a ha wh k) := by
  have hΦreal : ∀ ξ : Domain3,
      (starRingEnd ℂ) ((𝓕⁻ (symbolHatOf a ha wh k)) ξ) = (𝓕⁻ (symbolHatOf a ha wh k)) ξ := by
    intro ξ
    have hcoeInv : ((𝓕⁻ (symbolHatOf a ha wh k) : SchwartzMap Domain3 ℂ) : Domain3 → ℂ)
        = 𝓕⁻ ((symbolHatOf a ha wh k : Domain3 → ℂ)) := SchwartzMap.fourierInv_coe _
    have hcoeF : ((𝓕 (symbolHatOf a ha wh k) : SchwartzMap Domain3 ℂ) : Domain3 → ℂ)
        = 𝓕 ((symbolHatOf a ha wh k : Domain3 → ℂ)) := SchwartzMap.fourier_coe _
    have hΦpt : (𝓕⁻ (symbolHatOf a ha wh k)) ξ
        = (𝓕 (symbolHatOf a ha wh k) : SchwartzMap Domain3 ℂ) (-ξ) := by
      have e1 : (𝓕⁻ (symbolHatOf a ha wh k)) ξ
          = 𝓕⁻ ((symbolHatOf a ha wh k : Domain3 → ℂ)) ξ := congrFun hcoeInv ξ
      rw [e1, Real.fourierInv_eq_fourier_neg, ← hcoeF]
    rw [hΦpt, fourierH1_hermitian_real (symbolHatOf a ha wh k)
      (symbolHatOf_hermitian a ha wh hHerm k)]
  apply SchwartzMap.ext
  intro ξ
  rw [cxifyH1, potOf, SchwartzMap.postcompCLM_apply, SchwartzMap.postcompCLM_apply,
    RCLike.ofRealCLM_apply, RCLike.reCLM_apply, RCLike.re_to_complex]
  have := hΦreal ξ
  rw [Complex.conj_eq_iff_re] at this
  exact this

/-- `𝓕(cxify ψ_k) = ψ̂_k`: the Fourier transform of the complexified real potential is the
regularized symbol. -/
private theorem fourier_cxify_potOf (a : ℝ) (ha : 0 < a) (wh : Fin 3 → SchwartzMap Domain3 ℂ)
    (hHerm : ∀ b : Fin 3, ∀ v : Domain3, wh b (-v) = (starRingEnd ℂ) (wh b v)) (k : Fin 3) :
    (𝓕 (cxifyH1 (potOf a ha wh hHerm k)) : SchwartzMap Domain3 ℂ) = symbolHatOf a ha wh k := by
  rw [cxify_potOf a ha wh hHerm k, fourier_fourierInv_eq]

/-! ## Stage 2 — the curl Fourier symbol `𝓕(curl ψ_a)_j = ‖ξ‖²/(a²+‖ξ‖²) · ŵ_j` -/

/-- `(cxify f).toLp` is the real-to-complex embedding of `f.toLp` (local copy of the private
`CurlDensity.toLp_schwartzC_eq`). -/
private theorem toLp_cxifyH1 (f : SchwartzMap Domain3 ℝ) :
    (cxifyH1 f).toLp 2 (volume : Measure Domain3)
      = (RCLike.ofRealCLM (K := ℂ)).compLpL 2 (volume : Measure Domain3)
          (f.toLp 2 (volume : Measure Domain3)) := by
  haveI : Fact ((1 : ENNReal) ≤ 2) := ⟨by norm_num⟩
  refine Lp.ext ?_
  filter_upwards [(cxifyH1 f).coeFn_toLp 2 (volume : Measure Domain3),
    (RCLike.ofRealCLM (K := ℂ)).coeFn_compLpL (f.toLp 2 (volume : Measure Domain3)),
    f.coeFn_toLp 2 (volume : Measure Domain3)] with x hx hc hf
  rw [hx, hc, hf, cxifyH1_apply, RCLike.ofRealCLM_apply]
  rfl

/-- `potentialComponentC ψ k` is the complex L²-class of the complexified potential. -/
private theorem potentialComponentC_cxifyH1 (ψ : Fin 3 → SchwartzMap Domain3 ℝ) (k : Fin 3) :
    potentialComponentC ψ k = (cxifyH1 (ψ k)).toLp 2 (volume : Measure Domain3) := by
  rw [potentialComponentC, toLp_cxifyH1]

/-- The Fourier transform of the `k`-th potential component (as an `L²`-class) is a.e. the
regularized symbol `ψ̂_k`. -/
private theorem fourier_potentialComponentC_potOf (a : ℝ) (ha : 0 < a)
    (wh : Fin 3 → SchwartzMap Domain3 ℂ)
    (hHerm : ∀ b : Fin 3, ∀ v : Domain3, wh b (-v) = (starRingEnd ℂ) (wh b v)) (k : Fin 3) :
    ((𝓕 (potentialComponentC (potOf a ha wh hHerm) k) : L2C_R3) : Domain3 → ℂ)
      =ᵐ[volume] ((symbolHatOf a ha wh k : SchwartzMap Domain3 ℂ) : Domain3 → ℂ) := by
  have h1 : (𝓕 (potentialComponentC (potOf a ha wh hHerm) k) : L2C_R3)
      = (𝓕 (cxifyH1 (potOf a ha wh hHerm k))).toLp 2 (volume : Measure Domain3) := by
    rw [potentialComponentC_cxifyH1]
    exact SchwartzMap.toLp_fourier_eq (cxifyH1 (potOf a ha wh hHerm k))
  rw [h1, fourier_cxify_potOf a ha wh hHerm k]
  exact (symbolHatOf a ha wh k).coeFn_toLp 2 (volume : Measure Domain3)

/-- `‖ξ‖² = ξ₀² + ξ₁² + ξ₂²` on `Domain3`. -/
private theorem norm_sq_eq_sum (ξ : Domain3) :
    ‖ξ‖ ^ 2 = ξ 0 ^ 2 + ξ 1 ^ 2 + ξ 2 ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_three]
  simp [Real.norm_eq_abs, sq_abs]

/-- **BAC-CAB in the cyclic `Fin 3` convention.**  Given transversality
`∑ ξ_i wh_i = 0`, the double cross `(ξ × (ξ × ŵ))_j = -‖ξ‖² ŵ_j`. -/
private theorem baccab (ξ : Domain3) (wh : Fin 3 → SchwartzMap Domain3 ℂ) (j : Fin 3)
    (htr : (ξ 0 : ℂ) * wh 0 ξ + (ξ 1 : ℂ) * wh 1 ξ + (ξ 2 : ℂ) * wh 2 ξ = 0) :
    (ξ (j + 1) : ℂ) * ((ξ (j + 2 + 1) : ℂ) * wh (j + 2 + 2) ξ
        - (ξ (j + 2 + 2) : ℂ) * wh (j + 2 + 1) ξ)
      - (ξ (j + 2) : ℂ) * ((ξ (j + 1 + 1) : ℂ) * wh (j + 1 + 2) ξ
        - (ξ (j + 1 + 2) : ℂ) * wh (j + 1 + 1) ξ)
      = -((ξ 0 : ℂ) ^ 2 + (ξ 1 : ℂ) ^ 2 + (ξ 2 : ℂ) ^ 2) * wh j ξ := by
  fin_cases j
  · simp only [Fin.isValue, Fin.reduceFinMk, Fin.reduceAdd]
    linear_combination (ξ 0 : ℂ) * htr
  · simp only [Fin.isValue, Fin.reduceFinMk, Fin.reduceAdd]
    linear_combination (ξ 1 : ℂ) * htr
  · simp only [Fin.isValue, Fin.reduceFinMk, Fin.reduceAdd]
    linear_combination (ξ 2 : ℂ) * htr

/-- The curl multiplier evaluated on the regularized potential symbol equals
`‖ξ‖²/(a²+‖ξ‖²) · ŵ_j`, using transversality of `ŵ` at `ξ`. -/
private theorem crossWithIξ_symbolHat_eq (a : ℝ) (ha : 0 < a)
    (wh : Fin 3 → SchwartzMap Domain3 ℂ) (ξ : Domain3) (j : Fin 3)
    (htr : ∑ i : Fin 3, (ξ i : ℂ) * wh i ξ = 0) :
    crossWithIξ ξ (fun k => symbolHatOf a ha wh k ξ) j
      = ((‖ξ‖ ^ 2 / (a ^ 2 + ‖ξ‖ ^ 2) : ℝ) : ℂ) * wh j ξ := by
  have hc : (2 * Real.pi * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have htr3 : (ξ 0 : ℂ) * wh 0 ξ + (ξ 1 : ℂ) * wh 1 ξ + (ξ 2 : ℂ) * wh 2 ξ = 0 := by
    rw [← Fin.sum_univ_three (fun i => (ξ i : ℂ) * wh i ξ)]; exact htr
  have hexp : crossWithIξ ξ (fun k => symbolHatOf a ha wh k ξ) j
      = (-(((a ^ 2 + ‖ξ‖ ^ 2)⁻¹ : ℝ) : ℂ)) *
        ((ξ (j + 1) : ℂ) * ((ξ (j + 2 + 1) : ℂ) * wh (j + 2 + 2) ξ
            - (ξ (j + 2 + 2) : ℂ) * wh (j + 2 + 1) ξ)
          - (ξ (j + 2) : ℂ) * ((ξ (j + 1 + 1) : ℂ) * wh (j + 1 + 2) ξ
            - (ξ (j + 1 + 2) : ℂ) * wh (j + 1 + 1) ξ)) := by
    simp only [crossWithIξ, symbolHatOf_apply, crossHatOf_apply, symbolMul, yukawaMul]
    field_simp
    ring
  rw [hexp, baccab ξ wh j htr3]
  have hnsC : ((‖ξ‖ ^ 2 : ℝ) : ℂ) = (ξ 0 : ℂ) ^ 2 + (ξ 1 : ℂ) ^ 2 + (ξ 2 : ℂ) ^ 2 := by
    rw [norm_sq_eq_sum]; push_cast; ring
  rw [← hnsC]
  push_cast [div_eq_mul_inv]
  ring

/-- **Stage 2 result.**  The `j`-th complex-component Fourier transform of the curl of the
regularized potential is a.e. `‖ξ‖²/(a²+‖ξ‖²) · ŵ_j`. -/
private theorem fourier_curl_potOf_ae (a : ℝ) (ha : 0 < a)
    (wh : Fin 3 → SchwartzMap Domain3 ℂ)
    (hHerm : ∀ b : Fin 3, ∀ v : Domain3, wh b (-v) = (starRingEnd ℂ) (wh b v))
    (htr : ∀ᵐ ξ ∂(volume : Measure Domain3), ∑ i : Fin 3, (ξ i : ℂ) * wh i ξ = 0) (j : Fin 3) :
    ((𝓕 (L2VF_projComponentC_R3 j (curlSchwartzL2 (potOf a ha wh hHerm))) : L2C_R3) : Domain3 → ℂ)
      =ᵐ[volume] fun ξ => ((‖ξ‖ ^ 2 / (a ^ 2 + ‖ξ‖ ^ 2) : ℝ) : ℂ) * wh j ξ := by
  have hcross := fourier_curlSchwartz_eq_cross (potOf a ha wh hHerm) j
  have hp0 := fourier_potentialComponentC_potOf a ha wh hHerm 0
  have hp1 := fourier_potentialComponentC_potOf a ha wh hHerm 1
  have hp2 := fourier_potentialComponentC_potOf a ha wh hHerm 2
  filter_upwards [hcross, hp0, hp1, hp2, htr] with ξ hx h0 h1 h2 htrξ
  rw [hx]
  have hpk : ∀ k : Fin 3, (𝓕 (potentialComponentC (potOf a ha wh hHerm) k) : L2C_R3) ξ
      = symbolHatOf a ha wh k ξ := by
    intro k; fin_cases k
    · exact h0
    · exact h1
    · exact h2
  simp only [hpk]
  exact crossWithIξ_symbolHat_eq a ha wh ξ j htrξ

/-! ## Stage 3 — Parseval error bridge and dominated convergence in the scale `a`

Local re-proofs of the private CurlDensity Parseval helpers, then the L² and viscous
error expressions in Fourier form and their `a → 0` limits. -/

/-- Complex inner product of two real-to-complex embeddings equals the cast of the real
inner product (local copy of the private `CurlDensity.complexInner_compLpL_ofReal`). -/
private theorem complexInner_compLpL_ofReal_H1
    (a b : Lp ℝ 2 (volume : Measure Domain3)) :
    (inner ℂ ((RCLike.ofRealCLM (K := ℂ)).compLpL 2 (volume : Measure Domain3) a)
        ((RCLike.ofRealCLM (K := ℂ)).compLpL 2 (volume : Measure Domain3) b) : ℂ)
      = ((inner ℝ a b : ℝ) : ℂ) := by
  have hreal : (inner ℝ a b : ℝ)
      = ∫ x, (a : Domain3 → ℝ) x * (b : Domain3 → ℝ) x ∂(volume : Measure Domain3) := by
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards with x
    rw [RCLike.inner_apply, conj_trivial]
    ring
  rw [MeasureTheory.L2.inner_def, hreal]
  calc (∫ x, (inner ℂ
        (((RCLike.ofRealCLM (K := ℂ)).compLpL 2 (volume : Measure Domain3) a : Domain3 → ℂ) x)
        (((RCLike.ofRealCLM (K := ℂ)).compLpL 2 (volume : Measure Domain3) b : Domain3 → ℂ) x) : ℂ)
          ∂(volume : Measure Domain3))
      = ∫ x, (((a : Domain3 → ℝ) x * (b : Domain3 → ℝ) x : ℝ) : ℂ)
          ∂(volume : Measure Domain3) := by
        refine integral_congr_ae ?_
        filter_upwards [(RCLike.ofRealCLM (K := ℂ)).coeFn_compLpL a,
          (RCLike.ofRealCLM (K := ℂ)).coeFn_compLpL b] with x hax hbx
        rw [hax, hbx]
        simp only [RCLike.ofRealCLM_apply, RCLike.inner_apply, RCLike.conj_ofReal]
        rw [mul_comm]
        norm_cast
    _ = ((∫ x, (a : Domain3 → ℝ) x * (b : Domain3 → ℝ) x ∂(volume : Measure Domain3) : ℝ) : ℂ) :=
        integral_ofReal

/-- The real inner product on `L2VF_R3` decomposes as a sum over the three components (local
copy of the private `CurlDensity.inner_L2VF_eq_sum_component`). -/
private theorem inner_L2VF_eq_sum_component_H1 (a b : L2VF_R3) :
    (inner ℝ a b : ℝ)
      = ∑ j : Fin 3, (inner ℝ (L2VF_projComponent_R3 j a) (L2VF_projComponent_R3 j b) : ℝ) := by
  have hcomp : ∀ j : Fin 3,
      (inner ℝ (L2VF_projComponent_R3 j a) (L2VF_projComponent_R3 j b) : ℝ)
        = ∫ x, (L2VF_projComponent_R3 j a : Domain3 → ℝ) x
            * (L2VF_projComponent_R3 j b : Domain3 → ℝ) x ∂(volume : Measure Domain3) := by
    intro j
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards with x
    simp only [RCLike.inner_apply, conj_trivial]; ring
  have hint : ∀ j : Fin 3, Integrable (fun x => (L2VF_projComponent_R3 j a : Domain3 → ℝ) x
      * (L2VF_projComponent_R3 j b : Domain3 → ℝ) x) (volume : Measure Domain3) := by
    intro j
    have hI := MeasureTheory.L2.integrable_inner (𝕜 := ℝ)
      (L2VF_projComponent_R3 j a) (L2VF_projComponent_R3 j b)
    refine hI.congr ?_
    filter_upwards with x
    simp only [RCLike.inner_apply, conj_trivial]; ring
  simp_rw [hcomp]
  rw [← integral_finsetSum _ (fun j _ => hint j), MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  have hcoe : ∀ᵐ x ∂(volume : Measure Domain3), ∀ j : Fin 3,
      (L2VF_projComponent_R3 j a : Domain3 → ℝ) x = (a : Domain3 → EuclideanSpace ℝ (Fin 3)) x j
        ∧ (L2VF_projComponent_R3 j b : Domain3 → ℝ) x
            = (b : Domain3 → EuclideanSpace ℝ (Fin 3)) x j := by
    rw [MeasureTheory.ae_all_iff]
    intro j
    filter_upwards [(EuclideanSpace.proj (𝕜 := ℝ) j).coeFn_compLpL a,
      (EuclideanSpace.proj (𝕜 := ℝ) j).coeFn_compLpL b] with x hax hbx
    exact ⟨hax, hbx⟩
  filter_upwards [hcoe] with x hx
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [RCLike.inner_apply, conj_trivial, (hx j).1, (hx j).2]
  ring

/-- **Vector Parseval bridge** (local copy of the private
`CurlDensity.inner_L2VF_eq_integral_sum_fourier`). -/
private theorem inner_L2VF_eq_integral_sum_fourier_H1 (a b : L2VF_R3) :
    ((inner ℝ a b : ℝ) : ℂ)
      = ∫ ξ : Domain3, ∑ j : Fin 3,
          (starRingEnd ℂ) ((𝓕 (L2VF_projComponentC_R3 j a) : L2C_R3) ξ)
            * (𝓕 (L2VF_projComponentC_R3 j b) : L2C_R3) ξ
        ∂(volume : Measure Domain3) := by
  have hcomp : ∀ j : Fin 3,
      ((inner ℝ (L2VF_projComponent_R3 j a) (L2VF_projComponent_R3 j b) : ℝ) : ℂ)
        = ∫ ξ : Domain3,
            (starRingEnd ℂ) ((𝓕 (L2VF_projComponentC_R3 j a) : L2C_R3) ξ)
              * (𝓕 (L2VF_projComponentC_R3 j b) : L2C_R3) ξ ∂(volume : Measure Domain3) := by
    intro j
    rw [← complexInner_compLpL_ofReal_H1 (L2VF_projComponent_R3 j a) (L2VF_projComponent_R3 j b)]
    rw [show (RCLike.ofRealCLM (K := ℂ)).compLpL 2 (volume : Measure Domain3)
            (L2VF_projComponent_R3 j a) = L2VF_projComponentC_R3 j a from
          (ContinuousLinearMap.comp_apply _ _ _).symm,
      show (RCLike.ofRealCLM (K := ℂ)).compLpL 2 (volume : Measure Domain3)
            (L2VF_projComponent_R3 j b) = L2VF_projComponentC_R3 j b from
          (ContinuousLinearMap.comp_apply _ _ _).symm]
    rw [← MeasureTheory.Lp.inner_fourier_eq, MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards with ξ
    simp only [RCLike.inner_apply]; ring
  have hint : ∀ j : Fin 3, Integrable
      (fun ξ : Domain3 => (starRingEnd ℂ) ((𝓕 (L2VF_projComponentC_R3 j a) : L2C_R3) ξ)
        * (𝓕 (L2VF_projComponentC_R3 j b) : L2C_R3) ξ) (volume : Measure Domain3) := by
    intro j
    have hI := MeasureTheory.L2.integrable_inner (𝕜 := ℂ)
      (𝓕 (L2VF_projComponentC_R3 j a)) (𝓕 (L2VF_projComponentC_R3 j b))
    refine hI.congr ?_
    filter_upwards with ξ
    simp only [RCLike.inner_apply]; ring
  rw [show ((inner ℝ a b : ℝ) : ℂ)
        = ((∑ j : Fin 3, (inner ℝ (L2VF_projComponent_R3 j a)
            (L2VF_projComponent_R3 j b) : ℝ) : ℝ) : ℂ) from by
          rw [inner_L2VF_eq_sum_component_H1]]
  push_cast
  rw [Finset.sum_congr rfl (fun j _ => hcomp j)]
  rw [integral_finsetSum _ (fun j _ => hint j)]

/-! ## Main theorem (spike S6 verbatim, production name `curl_approx_H1`) -/

/-- Every Schwartz divergence-free field `w ∈ L2Sigma_R3` can be approximated in the H¹
graph seminorm (`L²` norm + `viscousFormSq_R3 1`) by a curl `curlSchwartzL2 ψ` of a
Schwartz potential `ψ : Fin 3 → SchwartzMap Domain3 ℝ`.

This is the analytic kernel needed to discharge `R3TestApproxH1` for the strengthened
concrete Galerkin basis (issue #4 PR-3). Proof: Fourier low-frequency cutoff construction
(see module doc); filled by lean-prover (issue #4 PR-2). -/
theorem curl_approx_H1 (w : L2Sigma_R3) (hw : IsSchwartzDivFree_R3 w)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ ψ : Fin 3 → SchwartzMap Domain3 ℝ,
      ‖curlSchwartzL2 ψ - (w : L2VF_R3)‖ < ε ∧
      viscousFormSq_R3 1 (curlSchwartzL2 ψ - (w : L2VF_R3)) < ε := by
  sorry -- ALLOW_SORRY: scaffold (issue #4 PR-2 — lean-prover fills via Fourier low-freq cutoff)

end LerayHopf
