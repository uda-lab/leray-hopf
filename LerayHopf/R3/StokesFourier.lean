import LerayHopf.R3.FourierL2
import LerayHopf.Analysis.FourierParseval

namespace LerayHopf

open MeasureTheory SchwartzMap FourierTransform LineDeriv
open scoped Topology RealInnerProductSpace FourierTransform

/-!
# Stokes/viscous pairing as a fixed-Schwartz-field weak-continuous form

Extracted from `CurlDensity.lean` (issue #113 PR-2), NS-specific (not a generic `Analysis/`
module): the viscous test pairing `stokesTestPairing_R3 u w`, rewritten via Plancherel from a
gradient-weighted Fourier integral into a finite sum of `L²`-inner products of `u`'s components
against the FIXED negative-Laplacian Schwartz fields `-Δ wⱼ`. This exhibits
`stokesTestPairing_R3 (·) w` as a weakly-continuous functional in `u` — the form the
nonlinear-free viscous limit passage `B(uₙ,w) → B(u,w)` needs (consumed by
`AubinLionsLimitPassage.lean` since issue #113 PR-1).

## Declarations

- `negLapSchwartz` — the scalar negative Laplacian of a real Schwartz map (`private`, as on
  `main`)
- `fourier_schwartzC_negLap_apply` — the second-order Fourier symbol of `negLapSchwartz`
  (`private`)
- `viscousComponent_eq_inner_negLap` — per-component viscous pairing as an `L²`-inner product
  (`private`)
- `stokesTestPairing_R3_eq_sum_inner_negLap` — **the deliverable**: `stokesTestPairing_R3` as a
  finite sum of fixed-field `L²`-inner products (public, preserved qualified name — consumed by
  `AubinLionsLimitPassage.lean`)

## Assumptions

No `axiom`/`opaque`/`constant`/`unsafe` in this file.
-/

/-! ### Viscous Plancherel–Laplacian reformulation (conjunct-2 atom (a))

The viscous test pairing `stokesTestPairing_R3 u w` is the H¹/Dirichlet pairing
`∑ⱼ ∫ (2π)²‖ξ‖² Re[𝓕uⱼ·conj 𝓕wⱼ]`, which carries a gradient weight and is therefore NOT
L²-continuous in `u` as written.  Moving the weight `(2π)²‖ξ‖²` off `𝓕u` onto `𝓕w` (Plancherel)
turns it into an honest `L²`-inner pairing against the FIXED Schwartz field `-Δw`:
`stokesTestPairing_R3 u w = ∑ⱼ ⟪uⱼ, (-Δ wⱼ)⟫_{L²}`.  Since each `-Δ wⱼ` is a fixed `L²` element
(Schwartz), this exhibits `stokesTestPairing_R3 (·) w` as a finite sum of `L²`-WEAK-continuous
functionals — the form the limit passage `B(uₙ,w) → B(u,w)` needs (it passes against the fixed
`-Δ wⱼ` by weak convergence).  The Fourier symbol is the second-order analogue of
`fourier_schwartzC_lineDeriv_apply`, iterated along each coordinate axis. -/

/-- The scalar **negative Laplacian** of a real Schwartz map, `-Δ f = -∑ₐ ∂ₐ∂ₐ f`, as a Schwartz
map (so it carries a canonical `L²`-class `(negLapSchwartz f).toLp`). -/
private noncomputable def negLapSchwartz (f : SchwartzMap Domain3 ℝ) : SchwartzMap Domain3 ℝ :=
  - ∑ a : Fin 3, ∂_{(EuclideanSpace.single a (1 : ℝ) : Domain3)}
      (∂_{(EuclideanSpace.single a (1 : ℝ) : Domain3)} f)

/-- **Second-order Fourier symbol.** The Schwartz Fourier transform of the complexified
negative Laplacian is the weighted transform: `𝓕(schwartzC (-Δ f))(ξ) = (2π)²‖ξ‖² · 𝓕(schwartzC f)(ξ)`.
Proof: apply `fourier_schwartzC_lineDeriv_apply` twice per axis (the symbol of `∂ₐ∂ₐ` is
`(2π i ξₐ)² = -(2π)² ξₐ²`), sum over axes (`∑ₐ ξₐ² = ‖ξ‖²`), negate. -/
private theorem fourier_schwartzC_negLap_apply
    (f : SchwartzMap Domain3 ℝ) (ξ : Domain3) :
    (𝓕 (schwartzC (negLapSchwartz f)) : SchwartzMap Domain3 ℂ) ξ
      = ((2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 : ℝ) * (𝓕 (schwartzC f) : SchwartzMap Domain3 ℂ) ξ := by
  -- `schwartzC` and `𝓕` are additive; push them through the finite sum and the negation.
  have hsum : schwartzC (negLapSchwartz f)
      = - ∑ a : Fin 3, schwartzC (∂_{(EuclideanSpace.single a (1 : ℝ) : Domain3)}
          (∂_{(EuclideanSpace.single a (1 : ℝ) : Domain3)} f)) := by
    unfold negLapSchwartz schwartzC
    rw [map_neg, map_sum]
  rw [hsum]
  -- Fourier of `-∑` is `-∑` of Fouriers; evaluate at `ξ`.
  rw [show (𝓕 (- ∑ a : Fin 3, schwartzC (∂_{(EuclideanSpace.single a (1 : ℝ) : Domain3)}
        (∂_{(EuclideanSpace.single a (1 : ℝ) : Domain3)} f))) : SchwartzMap Domain3 ℂ)
      = - ∑ a : Fin 3, 𝓕 (schwartzC (∂_{(EuclideanSpace.single a (1 : ℝ) : Domain3)}
          (∂_{(EuclideanSpace.single a (1 : ℝ) : Domain3)} f))) from by
        rw [← SchwartzMap.fourierTransformCLM_apply (𝕜 := ℂ), map_neg, map_sum]
        simp_rw [SchwartzMap.fourierTransformCLM_apply]]
  rw [SchwartzMap.neg_apply, SchwartzMap.sum_apply]
  -- Per-axis second-order symbol: `𝓕(∂ₐ∂ₐ f)(ξ) = -(2π)² ξₐ² 𝓕f(ξ)`.
  have hper : ∀ a : Fin 3,
      (𝓕 (schwartzC (∂_{(EuclideanSpace.single a (1 : ℝ) : Domain3)}
          (∂_{(EuclideanSpace.single a (1 : ℝ) : Domain3)} f))) : SchwartzMap Domain3 ℂ) ξ
        = (-(2 * Real.pi) ^ 2 * (ξ a) ^ 2 : ℝ) * (𝓕 (schwartzC f) : SchwartzMap Domain3 ℂ) ξ := by
    intro a
    rw [fourier_schwartzC_lineDeriv_apply (∂_{(EuclideanSpace.single a (1 : ℝ) : Domain3)} f)
      (EuclideanSpace.single a (1 : ℝ) : Domain3) ξ,
      fourier_schwartzC_lineDeriv_apply f (EuclideanSpace.single a (1 : ℝ) : Domain3) ξ]
    -- `inner ℝ ξ (single a 1) = ξ a`
    rw [show (inner ℝ ξ (EuclideanSpace.single a (1 : ℝ) : Domain3) : ℝ) = ξ a from by
      rw [EuclideanSpace.inner_single_right]; simp]
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  simp_rw [hper]
  -- `-∑ₐ (-(2π)² ξₐ² · F) = (2π)² (∑ₐ ξₐ²) · F = (2π)² ‖ξ‖² · F`.
  -- First identify `‖ξ‖² = ∑ₐ ξₐ²` for `EuclideanSpace`.
  have hnorm : (‖ξ‖ ^ 2 : ℝ) = ∑ a : Fin 3, (ξ a) ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Real.norm_eq_abs, sq_abs]
  rw [hnorm]
  push_cast
  -- distribute the RHS product over the sum, then match term-by-term (both are `∑ₐ`).
  rw [show ((2 * (Real.pi : ℂ)) ^ 2 * ∑ a : Fin 3, ((ξ a : ℝ) : ℂ) ^ 2)
        * (𝓕 (schwartzC f) : SchwartzMap Domain3 ℂ) ξ
      = ∑ a : Fin 3, (2 * (Real.pi : ℂ)) ^ 2 * ((ξ a : ℝ) : ℂ) ^ 2
          * (𝓕 (schwartzC f) : SchwartzMap Domain3 ℂ) ξ from by
        rw [Finset.mul_sum, Finset.sum_mul]]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  ring

/-- **Per-component viscous Plancherel pairing.** For a Schwartz component witness `ψ` and a
field `u`, the `j`-th Fourier-weighted viscous integrand equals the real `L²`-inner product of
the `j`-th component of `u` against the negative-Laplacian Schwartz field:
`∫ξ (2π)²‖ξ‖² Re[ûⱼ·conj ŵⱼ] = ⟪uⱼ, (-Δ ψⱼ).toLp⟫`, where `ŵⱼ = 𝓕(schwartzC ψⱼ)`. -/
private theorem viscousComponent_eq_inner_negLap
    (ψ : Fin 3 → SchwartzMap Domain3 ℝ) (u : L2VF_R3) (j : Fin 3) :
    ∫ ξ : Domain3,
        (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 *
          ((𝓕 (L2VF_projComponentC_R3 j u) : L2C_R3) ξ *
            (starRingEnd ℂ) ((𝓕 (schwartzC (ψ j)) : SchwartzMap Domain3 ℂ) ξ)).re
        ∂(volume : Measure Domain3)
      = (inner ℝ (L2VF_projComponent_R3 j u)
          ((negLapSchwartz (ψ j)).toLp 2 (volume : Measure Domain3)) : ℝ) := by
  -- The real inner product, complexified and Planchereled, is the Fourier-side pairing
  -- `∫ conj(𝓕 negLapⱼ) · ûⱼ`.  We then identify `conj(𝓕 negLapⱼ) = (2π)²‖ξ‖² conj(ŵⱼ)`.
  have hpar : ((inner ℝ (L2VF_projComponent_R3 j u)
        ((negLapSchwartz (ψ j)).toLp 2 (volume : Measure Domain3)) : ℝ) : ℂ)
      = ∫ ξ : Domain3,
          (starRingEnd ℂ) ((𝓕 (L2VF_projComponentC_R3 j u) : L2C_R3) ξ)
            * (𝓕 ((schwartzC (negLapSchwartz (ψ j))).toLp 2 (volume : Measure Domain3)) : L2C_R3) ξ
          ∂(volume : Measure Domain3) := by
    rw [← complexInner_compLpL_ofReal (L2VF_projComponent_R3 j u)
        ((negLapSchwartz (ψ j)).toLp 2 (volume : Measure Domain3))]
    rw [show (RCLike.ofRealCLM (K := ℂ)).compLpL 2 (volume : Measure Domain3)
            (L2VF_projComponent_R3 j u) = L2VF_projComponentC_R3 j u from
          (ContinuousLinearMap.comp_apply _ _ _).symm,
      ← toLp_schwartzC_eq]
    rw [← MeasureTheory.Lp.inner_fourier_eq, MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards with ξ
    simp only [RCLike.inner_apply]; ring
  -- Replace `𝓕(schwartzC negLapⱼ)` by its symbol `(2π)²‖ξ‖² 𝓕(schwartzC ψⱼ)` (a.e.).
  have hsymb : ((𝓕 ((schwartzC (negLapSchwartz (ψ j))).toLp 2 (volume : Measure Domain3)) : L2C_R3)
        : Domain3 → ℂ)
      =ᵐ[volume] fun ξ =>
        ((2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 : ℝ) * (𝓕 (schwartzC (ψ j)) : SchwartzMap Domain3 ℂ) ξ := by
    rw [SchwartzMap.toLp_fourier_eq]
    filter_upwards [(𝓕 (schwartzC (negLapSchwartz (ψ j)))).coeFn_toLp 2 (volume : Measure Domain3)]
      with ξ hξ
    rw [hξ, fourier_schwartzC_negLap_apply]
  -- The Fourier-side pairing in `hpar` is real-valued (it equals `↑(inner …)`); take real parts.
  -- `inner = Re(∫ complex integrand) = ∫ Re(complex integrand)`, and the pointwise real part of the
  -- Fourier integrand equals the stokes integrand (real scalar weight + `Re[z] = Re[conj z]`).
  have hre : (inner ℝ (L2VF_projComponent_R3 j u)
        ((negLapSchwartz (ψ j)).toLp 2 (volume : Measure Domain3)) : ℝ)
      = RCLike.re (∫ ξ : Domain3,
          (starRingEnd ℂ) ((𝓕 (L2VF_projComponentC_R3 j u) : L2C_R3) ξ)
            * (𝓕 ((schwartzC (negLapSchwartz (ψ j))).toLp 2 (volume : Measure Domain3)) : L2C_R3) ξ
          ∂(volume : Measure Domain3)) := by
    rw [← hpar]; simp
  rw [hre]
  -- integrability of the (complex) Fourier-side integrand.
  have hInt : Integrable (fun ξ : Domain3 =>
      (starRingEnd ℂ) ((𝓕 (L2VF_projComponentC_R3 j u) : L2C_R3) ξ)
        * (𝓕 ((schwartzC (negLapSchwartz (ψ j))).toLp 2 (volume : Measure Domain3)) : L2C_R3) ξ)
      (volume : Measure Domain3) := by
    have hI := MeasureTheory.L2.integrable_inner (𝕜 := ℂ)
      (𝓕 (L2VF_projComponentC_R3 j u))
      (𝓕 ((schwartzC (negLapSchwartz (ψ j))).toLp 2 (volume : Measure Domain3)))
    refine hI.congr ?_
    filter_upwards with ξ
    simp only [RCLike.inner_apply]; ring
  rw [← integral_re hInt]
  refine integral_congr_ae ?_
  filter_upwards [hsymb] with ξ hξ
  rw [hξ]
  -- Goal: `(2π)²‖ξ‖² · Re[ûⱼ conj ŵⱼ] = RCLike.re(conj ûⱼ · ((2π)²‖ξ‖² ŵⱼ))`.
  -- `RCLike.re = Complex.re` here; pull the real scalar out and use `Re[z] = Re[conj z]`.
  show _ = Complex.re _
  rw [show (starRingEnd ℂ) ((𝓕 (L2VF_projComponentC_R3 j u) : L2C_R3) ξ)
        * (((2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 : ℝ) * (𝓕 (schwartzC (ψ j)) : SchwartzMap Domain3 ℂ) ξ)
      = (((2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ)
        * ((starRingEnd ℂ) ((𝓕 (L2VF_projComponentC_R3 j u) : L2C_R3) ξ)
            * (𝓕 (schwartzC (ψ j)) : SchwartzMap Domain3 ℂ) ξ) from by ring]
  rw [Complex.re_ofReal_mul]
  -- `Re[conj ûⱼ · ŵⱼ] = Re[ûⱼ · conj ŵⱼ]`.
  rw [show ((starRingEnd ℂ) ((𝓕 (L2VF_projComponentC_R3 j u) : L2C_R3) ξ)
          * (𝓕 (schwartzC (ψ j)) : SchwartzMap Domain3 ℂ) ξ).re
        = ((𝓕 (L2VF_projComponentC_R3 j u) : L2C_R3) ξ
            * (starRingEnd ℂ) ((𝓕 (schwartzC (ψ j)) : SchwartzMap Domain3 ℂ) ξ)).re from by
          rw [← Complex.conj_re ((starRingEnd ℂ) _ * _)]; simp [mul_comm]]


/-- **Viscous Plancherel–Laplacian reformulation (conjunct-2 atom (a)).**  For a Schwartz
divergence-free test `w` (witness `ψ`), the viscous test pairing is a finite sum of real
`L²`-inner products of the components of `u` against the FIXED negative-Laplacian Schwartz fields:
`stokesTestPairing_R3 u w = ∑ⱼ ⟪uⱼ, (-Δ ψⱼ).toLp⟫`.

Each summand `u ↦ ⟪L2VF_projComponent_R3 j u, (-Δ ψⱼ).toLp⟫` is `L²`-WEAK-continuous in `u`
(`L2VF_projComponent_R3 j` is a CLM, then the inner against a fixed element is weak-continuous),
so this exhibits `stokesTestPairing_R3 (·) w` as a weakly-continuous functional — the form the
nonlinear-free viscous limit passage `B(uₙ,w) → B(u,w)` consumes. -/
theorem stokesTestPairing_R3_eq_sum_inner_negLap
    (u w : L2VF_R3) (ψ : Fin 3 → SchwartzMap Domain3 ℝ)
    (hψ : ∀ j : Fin 3,
      L2VF_projComponent_R3 j w = (ψ j).toLp 2 (volume : Measure Domain3)) :
    stokesTestPairing_R3 u w
      = ∑ j : Fin 3, (inner ℝ (L2VF_projComponent_R3 j u)
          ((negLapSchwartz (ψ j)).toLp 2 (volume : Measure Domain3)) : ℝ) := by
  rw [stokesTestPairing_R3]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  -- identify `𝓕(L2VF_projComponentC_R3 j w) = 𝓕(schwartzC (ψ j))` (a.e.) via the witness `hψ`.
  have hwC : L2VF_projComponentC_R3 j w = (schwartzC (ψ j)).toLp 2 (volume : Measure Domain3) := by
    rw [L2VF_projComponentC_R3, ContinuousLinearMap.comp_apply, hψ j, ← toLp_schwartzC_eq]
  rw [hwC]
  -- now the integrand uses `𝓕((schwartzC ψⱼ).toLp)`; rewrite to `𝓕(schwartzC ψⱼ)` pointwise.
  rw [← viscousComponent_eq_inner_negLap ψ u j]
  refine integral_congr_ae ?_
  filter_upwards [show ((𝓕 ((schwartzC (ψ j)).toLp 2 (volume : Measure Domain3)) : L2C_R3)
        : Domain3 → ℂ)
      =ᵐ[volume] fun ξ => (𝓕 (schwartzC (ψ j)) : SchwartzMap Domain3 ℂ) ξ from by
      rw [SchwartzMap.toLp_fourier_eq]
      filter_upwards [(𝓕 (schwartzC (ψ j))).coeFn_toLp 2 (volume : Measure Domain3)] with ξ hξ
      rw [hξ]] with ξ hξ
  rw [hξ]


end LerayHopf
