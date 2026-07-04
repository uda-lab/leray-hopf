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
