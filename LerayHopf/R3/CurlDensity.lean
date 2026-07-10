import LerayHopf.R3.SchwartzDivFreeBasis
import LerayHopf.R3.FourierL2

namespace LerayHopf

open MeasureTheory SchwartzMap FourierTransform LineDeriv
open scoped Topology RealInnerProductSpace FourierTransform

/-!
# Stream A — discharging `CurlSchwartzDense` (Helmholtz / curl-density on ℝ³)

**Milestone:** `helmholtz-density` (Stream A: Helmholtz / curl density).

This file's single deliverable is

```
theorem curlSchwartzDense_provedRoute : CurlSchwartzDense
```

i.e. a PROOF of the isolated density frontier `CurlSchwartzDense`
(`LerayHopf/R3/SchwartzDivFreeBasis.lean`) — the aspirational discharge route that would
RETIRE the marked density `axiom curlSchwartzDense_holds` (issue #21).  Named distinctly to
avoid a clash (this file imports `SchwartzDivFreeBasis`, where that axiom lives):

```
CurlSchwartzDense :=
  (L2Sigma_R3 : Submodule ℝ L2VF_R3) ≤
    (Submodule.span ℝ (Set.range curlSchwartzL2)).topologicalClosure
```

Once proved, this upgrades `CurlSchwartzDense` from the marked axiom `curlSchwartzDense_holds`
(`SchwartzDivFreeBasis.lean`, the single density axiom kept after the issue-#21 swap) to a
theorem, eliminating the last R3 spatial axiom.  The capstone rewiring itself
(`r3GalerkinScheme_exists` now a discharged theorem, `curlSchwartzDense_holds` the thin
density axiom) was done in issue #21; **proving the density to retire that axiom is OUT OF
SCOPE here**; this file only works toward the density and edits nothing outside itself.

## The classical route (Helmholtz / Weyl, Fourier proof)

The statement says: every weakly-divergence-free `u ∈ L2Sigma_R3` lies in the L²-closure
of `span { curlSchwartzL2 ψ : ψ ∈ 𝓢(ℝ³,ℝ)³ }`.  The standard proof is on the Fourier side:

1. **Fourier symbol of curl** (`fourier_curlSchwartz_eq_cross`).  Under 𝓕, the curl of a
   Schwartz vector potential becomes a pointwise *cross product with `iξ`*:
   `𝓕(curl ψ)(ξ) = (2π i) ξ × ψ̂(ξ)`.  Hence the set of attainable Fourier symbols at a fixed
   `ξ` is `{ (2π i) ξ × a : a ∈ ℂ³ }` — the plane orthogonal to `ξ`.

2. **Spectral div-free characterization** (`mem_sigma_iff_fourier_transverse`).  A field
   `u ∈ L2Sigma_R3` iff its Fourier transform is a.e. *transverse*: `ξ · û(ξ) = 0` a.e.
   This is the Fourier form of `div u = 0`.

3. **Fiberwise transverse spanning** (`cross_iξ_spans_transverse`).  For `ξ ≠ 0`, the map
   `a ↦ iξ × a` from `ℂ³` onto `ξ^⊥` is surjective: `{ iξ × a } = ξ^⊥`.  So every transverse
   target symbol is, fiberwise, an achievable curl symbol.

4. **Density transfer** (`l2sigma_le_closure_span_curl`).  Combining (1)–(3) with Plancherel
   (𝓕 is an L² isometry; `FourierL2`) and the L² density of Schwartz potentials
   (`SchwartzMap.denseRange_toLpCLM`), the curl symbols are dense among transverse symbols,
   hence the curls are dense in `L2Sigma_R3`.  This yields exactly `CurlSchwartzDense`.

## Honest status (the analytic frontier this file isolates)

Steps (1)–(3) are PROVED: the curl Fourier multiplier (`fourier_curlSchwartz_eq_cross`), the
cross-product fiberwise spanning (`cross_iξ_spans_transverse`), the full Plancherel /
`divTestFunctional` pairing infrastructure, and the REVERSE spectral characterization
(`mem_sigma_of_transverse_ae`).  The `(P1)` Lp-level Hermitian reflection identity
(`fourier_ofReal_reflect_eq_conj`) is PROVED here, axiom-free.

`(P2)` — Schwartz surjectivity of `φ ↦ testSymbol φ` onto anti-Hermitian symbols
(`schwartz_antiHermitian_has_testSymbol_preimage`) — is now also PROVED, via the reality
lemma `fourier_hermitian_real` (`𝓕` of a Hermitian Schwartz function is real-valued) plus
`SchwartzMap.postcompCLM Complex.conjCLE` / `RCLike.reCLM` and `FourierInvPair`.  Consequently
the FORWARD spectral characterization `mem_sigma_iff_fourier_transverse` is PROVED in full (the
du-Bois-Reymond even/odd reduction `antiHermitianTest_integral_zero` +
`ae_eq_zero_of_integral_contDiff_smul_eq_zero`), discharging two of the three former sorrys.

The pinned mathlib provides the heavy L²-Fourier toolkit: `MeasureTheory.Lp.fourierTransformₗᵢ`
(with `Lp.inner_fourier_eq` Parseval, `Lp.norm_fourier_eq` Plancherel), the orthogonal-complement
density criterion (`Submodule.orthogonal_orthogonal_eq_closure`), the du-Bois-Reymond lemma
(`ae_eq_zero_of_integral_contDiff_smul_eq_zero`), and `Lp.compMeasurePreserving` +
`Measure.measurePreserving_neg`.  The *Helmholtz/Leray-specific* content absent from mathlib (no
`curl`/`divergence` operator, no Helmholtz decomposition, no `closure(span curl) = L²_σ`) is built
here from those primitives.

**This file is now `sorry`-free and axiom-free.**  The Step-4 density transfer is fully proved:

* `inner_L2VF_eq_integral_sum_fourier` — the *vector* Parseval bridge on `L2VF_R3`
  (`⟪u,w⟫ = ∫ ∑_j conj(û_j) ŵ_j`, the three-component sum of `Lp.inner_fourier_eq`);
* `orthogonalCurl_longitudinal_ae` — extraction of longitudinality of `ŵ` from `w ⊥ all curls`
  (`fourier_curlSchwartz_eq_cross` + `conj_cross_sum_eq` triple-product re-grouping + the
  Hermitian-test du-Bois-Reymond `ae_zero_of_hermitianTest`, whose Hermitian tests are realised via
  `schwartz_hermitian_has_fourier_preimage`);
* `transverse_longitudinal_cancel` — the pointwise transverse ⊥ longitudinal cancellation;
* `l2sigma_inner_orthogonalCurl_eq_zero` assembles these, and `l2sigma_le_closure_span_curl`
  closes the orthogonal-complement reduction via `Submodule.orthogonal_orthogonal_eq_closure`.

The TOP-LEVEL type stays exactly `CurlSchwartzDense` — a real discharge target, never weakened.

This file introduces **no** `axiom`/`opaque`/`constant`/`unsafe`.

## FourierL2 dependencies

The density-transfer skeleton (step 4) is designed to lean on the shared Fourier–L²
foundation `LerayHopf.R3.FourierL2`:

* `FourierL2.normSq_eq_integral_normSq_C` — Plancherel-style: L² norm-squared of a complex
  component as an integral of the pointwise squared norm (used to turn fiberwise approximation
  into L²-norm approximation);
* `FourierL2.fourierComponentC_ae_schwartz` — the Fourier transform of a Schwartz-rep
  component is a.e. a genuine Schwartz `𝓕` (the Schwartz↔Lp Fourier bridge feeding the curl
  symbol identity into the L² inner products);
* `FourierL2.viscousFormSq_R3_eq_integral_normSq_fourier` / `FourierL2.normSq_*` — the
  spectral bookkeeping (Plancherel weights) that the approximation estimate is phrased against.

(The curl Fourier-multiplier identity itself, `fourier_curlSchwartz_eq_cross`, is the new
symbol lemma this file would add on top of `FourierL2`.)
-/

/-! ### Step 1 — Fourier symbol of the curl: `𝓕(curl ψ) = (2π i) ξ × ψ̂` -/

/-- The pointwise cross product `(2π i) ξ × a` on `ℂ³`, written componentwise on `Fin 3`
with the cyclic index convention used by `curlSchwartz`:
`(crossWithIξ ξ a) i = (2π i) (ξ_{i+1} a_{i+2} − ξ_{i+2} a_{i+1})`.

This is the Fourier symbol of `curl`: applying `𝓕` to `(curl ψ)_i = ∂_{i+1}ψ_{i+2} −
∂_{i+2}ψ_{i+1}` turns each `∂_a` into multiplication by `2π i ξ_a`. -/
noncomputable def crossWithIξ (ξ : Domain3) (a : Fin 3 → ℂ) : Fin 3 → ℂ :=
  fun i =>
    (2 * Real.pi * Complex.I) *
      (((ξ (i + 1) : ℂ)) * a (i + 2) - ((ξ (i + 2) : ℂ)) * a (i + 1))

/-- The complex `L2C_R3` class of a real Schwartz POTENTIAL component `ψ k`: its `Lp ℝ`
class embedded into `Lp ℂ` through the real-to-complex coercion `RCLike.ofRealCLM`, lifted
to the `Lp` level by `compLpL`.

This is the SAME real→complex coercion used by `L2VF_projComponentC_R3`
(`Domain.lean`), so `potentialComponentC ψ k` is `L2VF_projComponentC_R3`-shaped: it is the
complex L²-class whose a.e. value is `ξ ↦ (ψ k ξ : ℂ)`.  It is the input whose Fourier
transform the curl multiplier acts on — the FOURIER TRANSFORM OF THE POTENTIAL, not of the
curl. -/
noncomputable def potentialComponentC (ψ : Fin 3 → SchwartzMap Domain3 ℝ) (k : Fin 3) :
    L2C_R3 :=
  (RCLike.ofRealCLM (K := ℂ)).compLpL 2 (volume : Measure Domain3)
    ((ψ k).toLp 2 (volume : Measure Domain3))

/-- Complexification of a real Schwartz map by post-composing with `ℝ →L[ℝ] ℂ`. -/
noncomputable def schwartzC (f : SchwartzMap Domain3 ℝ) : SchwartzMap Domain3 ℂ :=
  f.postcompCLM (RCLike.ofRealCLM (K := ℂ))

theorem schwartzC_apply (f : SchwartzMap Domain3 ℝ) (x : Domain3) :
    schwartzC f x = (f x : ℂ) := rfl

/-- The complex L²-class of a complexified real Schwartz map is the `compLpL`-embedding of the
real class — i.e. exactly `potentialComponentC`-shaped. -/
theorem toLp_schwartzC_eq (f : SchwartzMap Domain3 ℝ) :
    (schwartzC f).toLp 2 (volume : Measure Domain3)
      = (RCLike.ofRealCLM (K := ℂ)).compLpL 2 (volume : Measure Domain3)
          (f.toLp 2 (volume : Measure Domain3)) := by
  haveI : Fact ((1 : ENNReal) ≤ 2) := ⟨by norm_num⟩
  refine Lp.ext ?_
  filter_upwards [(schwartzC f).coeFn_toLp 2 (volume : Measure Domain3),
    (RCLike.ofRealCLM (K := ℂ)).coeFn_compLpL (f.toLp 2 (volume : Measure Domain3)),
    f.coeFn_toLp 2 (volume : Measure Domain3)] with x hx hc hf
  rw [hx, hc, hf, schwartzC_apply, RCLike.ofRealCLM_apply]
  rfl

/-- `potentialComponentC ψ k` is the complex L²-class of the complexified potential `schwartzC (ψ k)`. -/
private theorem potentialComponentC_eq (ψ : Fin 3 → SchwartzMap Domain3 ℝ) (k : Fin 3) :
    potentialComponentC ψ k = (schwartzC (ψ k)).toLp 2 (volume : Measure Domain3) := by
  rw [potentialComponentC, toLp_schwartzC_eq]

/-- Line derivative commutes with complexification: `∂_m (schwartzC f) = schwartzC (∂_m f)`. -/
private theorem lineDerivOp_schwartzC (f : SchwartzMap Domain3 ℝ) (m : Domain3) :
    (∂_{m} (schwartzC f)) = schwartzC (∂_{m} f) := by
  ext x
  rw [lineDerivOp_apply_eq_fderiv, schwartzC_apply, lineDerivOp_apply_eq_fderiv]
  -- `schwartzC f = ofRealCLM ∘ f`; push fderiv through the CLM
  have hcomp : ((schwartzC f : Domain3 → ℂ))
      = (RCLike.ofRealCLM (K := ℂ)) ∘ (f : Domain3 → ℝ) := by
    funext y; rw [schwartzC_apply]; rfl
  rw [hcomp]
  rw [fderiv_comp x (RCLike.ofRealCLM (K := ℂ)).differentiableAt
    (f.smooth 1).differentiable_one.differentiableAt]
  rw [(RCLike.ofRealCLM (K := ℂ)).fderiv]
  simp [ContinuousLinearMap.comp_apply]

/-- Pointwise Fourier symbol of the complexified line derivative: for a real Schwartz `f` and
direction `m`, the Schwartz Fourier transform of `schwartzC (∂_m f)` at `ξ` is
`(2π i)(inner ℝ ξ m)·𝓕(schwartzC f)(ξ)`.

This is `fourier_lineDerivOp_eq` applied to the complexified map `schwartzC f`, using
`lineDerivOp_schwartzC` to identify `schwartzC (∂_m f) = ∂_m (schwartzC f)`. -/
private theorem fourier_schwartzC_lineDeriv_apply
    (f : SchwartzMap Domain3 ℝ) (m : Domain3) (ξ : Domain3) :
    (𝓕 (schwartzC (∂_{m} f)) : SchwartzMap Domain3 ℂ) ξ
      = (2 * Real.pi * Complex.I) * ((inner ℝ ξ m : ℝ) : ℂ)
          * ((𝓕 (schwartzC f) : SchwartzMap Domain3 ℂ) ξ) := by
  have hC : schwartzC (∂_{m} f) = ∂_{m} (schwartzC f) := (lineDerivOp_schwartzC f m).symm
  rw [hC]
  have hg : (inner ℝ · m : Domain3 → ℝ).HasTemperateGrowth :=
    ((innerSL ℝ).flip m).hasTemperateGrowth
  have hkey := SchwartzMap.fourier_lineDerivOp_eq (schwartzC f) m
  rw [hkey]
  -- evaluate the RHS SchwartzMap at `ξ`
  rw [SchwartzMap.smul_apply, SchwartzMap.smulLeftCLM_apply_apply hg]
  rw [smul_eq_mul, Complex.real_smul]
  ring

/-- Schwartz-level curl Fourier multiplier (pointwise, everywhere).  The Schwartz Fourier
transform of the complexified curl component `schwartzC (curlSchwartz ψ j)` at `ξ` equals the
`j`-th cross-product symbol on the complexified potential Fourier transforms. -/
private theorem fourier_schwartzC_curl_apply
    (ψ : Fin 3 → SchwartzMap Domain3 ℝ) (j : Fin 3) (ξ : Domain3) :
    (𝓕 (schwartzC (curlSchwartz ψ j)) : SchwartzMap Domain3 ℂ) ξ
      = crossWithIξ ξ
          (fun k => (𝓕 (schwartzC (ψ k)) : SchwartzMap Domain3 ℂ) ξ) j := by
  -- expand the curl component as a difference of two complexified line derivatives
  have hcurl : schwartzC (curlSchwartz ψ j)
      = schwartzC (∂_{(EuclideanSpace.single (j + 1) (1 : ℝ) : Domain3)} (ψ (j + 2)))
        - schwartzC (∂_{(EuclideanSpace.single (j + 2) (1 : ℝ) : Domain3)} (ψ (j + 1))) := by
    unfold curlSchwartz schwartzC
    rw [map_sub, lineDerivOpCLM_apply, lineDerivOpCLM_apply]
  rw [hcurl]
  rw [show (𝓕 (schwartzC (∂_{(EuclideanSpace.single (j + 1) (1 : ℝ) : Domain3)} (ψ (j + 2)))
        - schwartzC (∂_{(EuclideanSpace.single (j + 2) (1 : ℝ) : Domain3)} (ψ (j + 1))))
          : SchwartzMap Domain3 ℂ)
        = 𝓕 (schwartzC (∂_{(EuclideanSpace.single (j + 1) (1 : ℝ) : Domain3)} (ψ (j + 2))))
          - 𝓕 (schwartzC (∂_{(EuclideanSpace.single (j + 2) (1 : ℝ) : Domain3)} (ψ (j + 1))))
        from by
          rw [← SchwartzMap.fourierTransformCLM_apply (𝕜 := ℂ), map_sub,
            SchwartzMap.fourierTransformCLM_apply, SchwartzMap.fourierTransformCLM_apply]]
  rw [SchwartzMap.sub_apply,
    fourier_schwartzC_lineDeriv_apply, fourier_schwartzC_lineDeriv_apply]
  -- rewrite the inner products `⟪ξ, e_a⟫ = ξ a`
  simp only [EuclideanSpace.inner_single_right, map_one, mul_one, RCLike.conj_to_real]
  simp only [crossWithIξ]
  push_cast
  ring

/-- **Step 1 (curl Fourier multiplier).**  The Fourier transform of the `j`-th component of
the curl of a Schwartz potential is, pointwise, the `j`-th component of the cross-product
symbol `(2π i) ξ × ψ̂(ξ)`, where `ψ̂` is the Fourier transform of the underlying POTENTIAL
components `ψ k` (NOT of the curl).

This is the genuine curl Fourier multiplier identity
`𝓕(curl ψ)_j(ξ) = (2π i) (ξ × ψ̂(ξ))_j`, obtained from the symbol identity
`𝓕(∂_a f)(ξ) = 2π i ξ_a · f̂(ξ)` applied to each of the two summands of `(curlSchwartz ψ)_j`
and assembled into the cross product `crossWithIξ`.  The LHS curl component is identified via
`curlSchwartzL2_projComponent`; the RHS vector is the Fourier transform of the potential
components `potentialComponentC ψ k` — so the statement is NOT circular.

Blocker: mathlib's `SchwartzMap` Fourier API has the derivative→multiplier identity in the
shape `𝓕 (∂ ψ) = (multiplier) • 𝓕 ψ`, but threading it through `lineDerivOpCLM`, the
`Lp`-level `𝓕` on components, and the cyclic-index assembly is real (non-mechanical) work that
belongs to `lean-prover`. -/
theorem fourier_curlSchwartz_eq_cross
    (ψ : Fin 3 → SchwartzMap Domain3 ℝ) (j : Fin 3) :
    ((𝓕 (L2VF_projComponentC_R3 j (curlSchwartzL2 ψ)) : L2C_R3) : Domain3 → ℂ)
      =ᵐ[volume] fun ξ =>
        crossWithIξ ξ
          (fun k => (𝓕 (potentialComponentC ψ k) : L2C_R3) ξ) j := by
  -- The `j`-th complex component of the curl class is the complexified curl Schwartz rep.
  have hLHScomp : L2VF_projComponentC_R3 j (curlSchwartzL2 ψ)
      = (schwartzC (curlSchwartz ψ j)).toLp 2 (volume : Measure Domain3) := by
    rw [L2VF_projComponentC_R3, ContinuousLinearMap.comp_apply, curlSchwartzL2_projComponent,
      ← toLp_schwartzC_eq]
  -- LHS coercion is a.e. the genuine Schwartz Fourier transform `𝓕 (schwartzC (curl ψ)_j)`.
  have hLHS := FourierL2.fourierComponentC_ae_schwartz j (curlSchwartzL2 ψ)
    (schwartzC (curlSchwartz ψ j)) hLHScomp
  -- For each potential component `k`, the coercion of `𝓕 (potentialComponentC ψ k)` is a.e.
  -- the genuine Schwartz Fourier transform `𝓕 (schwartzC (ψ k))`.
  have hpot : ∀ k : Fin 3,
      ((𝓕 (potentialComponentC ψ k) : L2C_R3) : Domain3 → ℂ)
        =ᵐ[volume] ((𝓕 (schwartzC (ψ k)) : SchwartzMap Domain3 ℂ) : Domain3 → ℂ) := by
    intro k
    have hF : (𝓕 (potentialComponentC ψ k) : L2C_R3)
        = (𝓕 (schwartzC (ψ k))).toLp 2 (volume : Measure Domain3) := by
      rw [potentialComponentC_eq]; exact SchwartzMap.toLp_fourier_eq (schwartzC (ψ k))
    rw [hF]
    exact (𝓕 (schwartzC (ψ k))).coeFn_toLp 2 (volume : Measure Domain3)
  -- assemble: a.e. all four component coercions agree with their Schwartz reps, then the
  -- everywhere pointwise identity `fourier_schwartzC_curl_apply` finishes.
  filter_upwards [hLHS, hpot 0, hpot 1, hpot 2] with ξ hx hx0 hx1 hx2
  rw [hx, fourier_schwartzC_curl_apply ψ j ξ]
  simp only [crossWithIξ]
  -- replace each potential-component coercion by its Schwartz value
  have hpotξ : ∀ k : Fin 3,
      (𝓕 (potentialComponentC ψ k) : L2C_R3) ξ
        = (𝓕 (schwartzC (ψ k)) : SchwartzMap Domain3 ℂ) ξ := by
    intro k; fin_cases k
    · exact hx0
    · exact hx1
    · exact hx2
  rw [hpotξ, hpotξ]

/-! ### Step 2 — spectral characterization of weak divergence-freeness -/

/-- **Fourier of a real function is Hermitian.**  For a real Schwartz `φ`, the Fourier
transform of its complexification satisfies `𝓕(schwartzC φ)(-ξ) = conj (𝓕(schwartzC φ)(ξ))`.

This is the conjugate symmetry of the Fourier transform of a (complexified) real function:
pushing `conj` through the integral defining `𝓕`, the unit-modulus character contributes
`conj(𝐞(-⟪v,ξ⟫)) = 𝐞(⟪v,ξ⟫) = 𝐞(-⟪v,-ξ⟫)`, while `conj` acts trivially on the real-valued
integrand `schwartzC φ`. -/
theorem fourier_schwartzC_hermitian (φ : SchwartzMap Domain3 ℝ) (ξ : Domain3) :
    (𝓕 (schwartzC φ) : SchwartzMap Domain3 ℂ) (-ξ)
      = (starRingEnd ℂ) ((𝓕 (schwartzC φ) : SchwartzMap Domain3 ℂ) ξ) := by
  -- Move to the underlying function `𝓕 (schwartzC φ : Domain3 → ℂ)`.
  have hcoe : ((𝓕 (schwartzC φ) : SchwartzMap Domain3 ℂ) : Domain3 → ℂ)
        = 𝓕 ((schwartzC φ : Domain3 → ℂ)) := SchwartzMap.fourier_coe (schwartzC φ)
  rw [show (𝓕 (schwartzC φ) : SchwartzMap Domain3 ℂ) (-ξ)
        = 𝓕 ((schwartzC φ : Domain3 → ℂ)) (-ξ) from congrFun hcoe (-ξ),
    show (𝓕 (schwartzC φ) : SchwartzMap Domain3 ℂ) ξ
        = 𝓕 ((schwartzC φ : Domain3 → ℂ)) ξ from congrFun hcoe ξ]
  -- RHS: push `conj` into the integral defining `𝓕 _ ξ`.
  rw [Real.fourier_eq, Real.fourier_eq, ← integral_conj]
  refine integral_congr_ae ?_
  filter_upwards with v
  -- Convert both `Circle` actions to complex multiplication.
  simp only [Circle.smul_def, smul_eq_mul, inner_neg_right, map_mul, schwartzC_apply,
    Complex.conj_ofReal, neg_neg]
  -- character: `(𝐞 (⟪v,ξ⟫) : ℂ) = conj ((𝐞 (-⟪v,ξ⟫) : ℂ))`
  rw [← Circle.coe_inv_eq_conj, ← AddChar.map_neg_eq_inv, neg_neg]

/-- The transverse (divergence-free) symbol condition at a point `ξ`: the complex Fourier
vector `û(ξ)` is orthogonal to `ξ`, `∑ j, ξ_j û_j(ξ) = 0`.  This is the Fourier form of the
pointwise constraint `ξ · û(ξ) = 0` characterizing `div u = 0`. -/
def IsTransverseAt (û : Fin 3 → ℂ) (ξ : Domain3) : Prop :=
  ∑ j : Fin 3, (ξ j : ℂ) * û j = 0

/-- The complex L²-inner product of the complexifications of two real Lp components equals the
cast of their real L²-inner product.  Both sides are the integral of the pointwise product. -/
theorem complexInner_compLpL_ofReal
    (a b : Lp ℝ 2 (volume : Measure Domain3)) :
    (inner ℂ ((RCLike.ofRealCLM (K := ℂ)).compLpL 2 (volume : Measure Domain3) a)
        ((RCLike.ofRealCLM (K := ℂ)).compLpL 2 (volume : Measure Domain3) b) : ℂ)
      = ((inner ℝ a b : ℝ) : ℂ) := by
  -- real inner as an integral of the pointwise product
  have hreal : (inner ℝ a b : ℝ)
      = ∫ x, (a : Domain3 → ℝ) x * (b : Domain3 → ℝ) x ∂(volume : Measure Domain3) := by
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards with x
    rw [RCLike.inner_apply, conj_trivial]
    ring
  -- complex inner as the integral of the cast of the pointwise product
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

/-- **Component decomposition of the `L2VF_R3` inner product.**  The real inner product on
`L2VF_R3 = L²(ℝ³; ℝ³)` is the sum over the three coordinates of the component inner products. -/
theorem inner_L2VF_eq_sum_component (a b : L2VF_R3) :
    (inner ℝ a b : ℝ)
      = ∑ j : Fin 3, (inner ℝ (L2VF_projComponent_R3 j a) (L2VF_projComponent_R3 j b) : ℝ) := by
  -- each component inner as an integral of the pointwise product
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
  -- a.e. each component coercion is the coordinate projection of `a x`, `b x`
  have hcoe : ∀ᵐ x ∂(volume : Measure Domain3), ∀ j : Fin 3,
      (L2VF_projComponent_R3 j a : Domain3 → ℝ) x = (a : Domain3 → EuclideanSpace ℝ (Fin 3)) x j
        ∧ (L2VF_projComponent_R3 j b : Domain3 → ℝ) x = (b : Domain3 → EuclideanSpace ℝ (Fin 3)) x j := by
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

/-- **Vector Parseval bridge.**  The (complexified) real inner product of two velocity fields
equals the integral of the three-component sum of Hermitian products of their complex component
Fourier transforms:
`⟪u, w⟫ = ∫ ∑_j conj(û_j(ξ)) · ŵ_j(ξ) dξ`, where `û_j = 𝓕 (L2VF_projComponentC_R3 j u)`.

Assembles `inner_L2VF_eq_sum_component` (vector → component inners), `complexInner_compLpL_ofReal`
(real → complex component inner), `Lp.inner_fourier_eq` (Plancherel per component), and the
finite-sum/integral swap. -/
theorem inner_L2VF_eq_integral_sum_fourier (a b : L2VF_R3) :
    ((inner ℝ a b : ℝ) : ℂ)
      = ∫ ξ : Domain3, ∑ j : Fin 3,
          (starRingEnd ℂ) ((𝓕 (L2VF_projComponentC_R3 j a) : L2C_R3) ξ)
            * (𝓕 (L2VF_projComponentC_R3 j b) : L2C_R3) ξ
        ∂(volume : Measure Domain3) := by
  -- component inner products, complexified and Planchereled
  have hcomp : ∀ j : Fin 3,
      ((inner ℝ (L2VF_projComponent_R3 j a) (L2VF_projComponent_R3 j b) : ℝ) : ℂ)
        = ∫ ξ : Domain3,
            (starRingEnd ℂ) ((𝓕 (L2VF_projComponentC_R3 j a) : L2C_R3) ξ)
              * (𝓕 (L2VF_projComponentC_R3 j b) : L2C_R3) ξ ∂(volume : Measure Domain3) := by
    intro j
    rw [← complexInner_compLpL_ofReal (L2VF_projComponent_R3 j a) (L2VF_projComponent_R3 j b)]
    -- the complexified component is `L2VF_projComponentC_R3 j`
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
  -- integrability of each Fourier-side component integrand
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
            (L2VF_projComponent_R3 j b) : ℝ) : ℝ) : ℂ) from by rw [inner_L2VF_eq_sum_component]]
  push_cast
  rw [Finset.sum_congr rfl (fun j _ => hcomp j)]
  rw [integral_finsetSum _ (fun j _ => hint j)]

/-- Per-component Plancherel pairing: the complex cast of the real L²-inner product
`⟪(∂_j φ).toLp, u_j⟫` equals the Fourier-side pairing
`∫ conj((2π i) ξ_j 𝓕(φ̂)(ξ)) û_j(ξ) dξ`, where `φ̂ = 𝓕 (schwartzC φ)` and
`û_j = 𝓕 (L2VF_projComponentC_R3 j u)`. -/
private theorem divComponent_eq_fourier_integral
    (φ : SchwartzMap Domain3 ℝ) (u : L2VF_R3) (j : Fin 3) :
    ((inner ℝ ((lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
          (EuclideanSpace.single j (1 : ℝ) : Domain3) φ).toLp 2 (volume : Measure Domain3))
        (L2VF_projComponent_R3 j u) : ℝ) : ℂ)
      = ∫ ξ : Domain3,
          (starRingEnd ℂ)
              ((2 * Real.pi * Complex.I) * ((ξ j : ℝ) : ℂ)
                * (𝓕 (schwartzC φ) : SchwartzMap Domain3 ℂ) ξ)
            * (𝓕 (L2VF_projComponentC_R3 j u) : L2C_R3) ξ
        ∂(volume : Measure Domain3) := by
  -- complexify the two real Lp factors
  set g : Lp ℝ 2 (volume : Measure Domain3) :=
    (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
      (EuclideanSpace.single j (1 : ℝ) : Domain3) φ).toLp 2 (volume : Measure Domain3) with hg
  rw [← complexInner_compLpL_ofReal g (L2VF_projComponent_R3 j u)]
  -- the complexified `g` is the toLp of `schwartzC (∂_j φ)`
  have hgC : (RCLike.ofRealCLM (K := ℂ)).compLpL 2 (volume : Measure Domain3) g
      = (schwartzC (∂_{(EuclideanSpace.single j (1 : ℝ) : Domain3)} φ)).toLp 2
          (volume : Measure Domain3) := by
    rw [hg, lineDerivOpCLM_apply, ← toLp_schwartzC_eq]
  -- the complexified component is `L2VF_projComponentC_R3 j u`
  have huC : (RCLike.ofRealCLM (K := ℂ)).compLpL 2 (volume : Measure Domain3)
        (L2VF_projComponent_R3 j u)
      = L2VF_projComponentC_R3 j u := by
    rw [L2VF_projComponentC_R3, ContinuousLinearMap.comp_apply]
  rw [hgC, huC]
  -- Plancherel: `⟪c₁, c₂⟫ = ⟪𝓕 c₁, 𝓕 c₂⟫`
  rw [← MeasureTheory.Lp.inner_fourier_eq]
  -- write the inner as an integral of the pointwise product
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  -- a.e. the Fourier of the Schwartz-rep factor is the Schwartz Fourier multiplier
  have hF1 : ((𝓕 ((schwartzC (∂_{(EuclideanSpace.single j (1 : ℝ) : Domain3)} φ)).toLp 2
          (volume : Measure Domain3)) : L2C_R3) : Domain3 → ℂ)
      =ᵐ[volume] fun ξ =>
        (2 * Real.pi * Complex.I) * ((ξ j : ℝ) : ℂ)
          * (𝓕 (schwartzC φ) : SchwartzMap Domain3 ℂ) ξ := by
    have h1 : (𝓕 ((schwartzC (∂_{(EuclideanSpace.single j (1 : ℝ) : Domain3)} φ)).toLp 2
            (volume : Measure Domain3)) : L2C_R3)
        = (𝓕 (schwartzC (∂_{(EuclideanSpace.single j (1 : ℝ) : Domain3)} φ))).toLp 2
            (volume : Measure Domain3) :=
      SchwartzMap.toLp_fourier_eq (schwartzC (∂_{(EuclideanSpace.single j (1 : ℝ) : Domain3)} φ))
    rw [h1]
    filter_upwards [(𝓕 (schwartzC (∂_{(EuclideanSpace.single j (1 : ℝ) : Domain3)} φ))).coeFn_toLp
      2 (volume : Measure Domain3)] with ξ hξ
    rw [hξ, fourier_schwartzC_lineDeriv_apply]
    -- `inner ℝ ξ (single j 1) = ξ j`
    rw [show (inner ℝ ξ (EuclideanSpace.single j (1 : ℝ) : Domain3) : ℝ) = ξ j from by
      rw [EuclideanSpace.inner_single_right]; simp]
  filter_upwards [hF1] with ξ hξ
  rw [RCLike.inner_apply, hξ, mul_comm]

/-- The transverse defect symbol of `u` at `ξ`: `T_u(ξ) = ∑_j ξ_j û_j(ξ)`.  `u ∈ L2Sigma_R3`
will be characterised by `T_u = 0` a.e. -/
private noncomputable def transverseDefect (u : L2VF_R3) (ξ : Domain3) : ℂ :=
  ∑ j : Fin 3, (ξ j : ℂ) * (𝓕 (L2VF_projComponentC_R3 j u) : L2C_R3) ξ

/-- The per-component integrand of `divComponent_eq_fourier_integral` is integrable: it is the
pointwise inner product of two `L²` Fourier transforms. -/
private theorem integrable_divComponent
    (φ : SchwartzMap Domain3 ℝ) (u : L2VF_R3) (j : Fin 3) :
    Integrable (fun ξ : Domain3 =>
        (starRingEnd ℂ)
            ((2 * Real.pi * Complex.I) * ((ξ j : ℝ) : ℂ)
              * (𝓕 (schwartzC φ) : SchwartzMap Domain3 ℂ) ξ)
          * (𝓕 (L2VF_projComponentC_R3 j u) : L2C_R3) ξ)
      (volume : Measure Domain3) := by
  -- it equals a.e. the L²-inner integrand `⟪𝓕 c₁, 𝓕 c₂⟫`
  set c₁ : L2C_R3 := 𝓕 ((schwartzC (∂_{(EuclideanSpace.single j (1 : ℝ) : Domain3)} φ)).toLp 2
      (volume : Measure Domain3)) with hc₁
  set c₂ : L2C_R3 := 𝓕 (L2VF_projComponentC_R3 j u) with hc₂
  have hint := MeasureTheory.L2.integrable_inner (𝕜 := ℂ) c₁ c₂
  refine hint.congr ?_
  -- a.e. the Fourier of the Schwartz-rep factor matches the multiplier symbol
  have hF1 : ((c₁ : L2C_R3) : Domain3 → ℂ)
      =ᵐ[volume] fun ξ =>
        (2 * Real.pi * Complex.I) * ((ξ j : ℝ) : ℂ)
          * (𝓕 (schwartzC φ) : SchwartzMap Domain3 ℂ) ξ := by
    rw [hc₁, SchwartzMap.toLp_fourier_eq]
    filter_upwards [(𝓕 (schwartzC (∂_{(EuclideanSpace.single j (1 : ℝ) : Domain3)} φ))).coeFn_toLp
      2 (volume : Measure Domain3)] with ξ hξ
    rw [hξ, fourier_schwartzC_lineDeriv_apply]
    rw [show (inner ℝ ξ (EuclideanSpace.single j (1 : ℝ) : Domain3) : ℝ) = ξ j from by
      rw [EuclideanSpace.inner_single_right]; simp]
  filter_upwards [hF1] with ξ hξ
  rw [RCLike.inner_apply, hξ, mul_comm]

/-- The transverse defect `T_u` is locally integrable: each `û_j ∈ L²` is integrable on every
compact set, the weight `ξ ↦ ξ_j` is continuous, and the finite sum stays locally integrable. -/
private theorem locallyIntegrable_transverseDefect (u : L2VF_R3) :
    LocallyIntegrable (transverseDefect u) (volume : Measure Domain3) := by
  rw [locallyIntegrable_iff]
  intro K hK
  unfold transverseDefect IntegrableOn
  -- the integrand is a finite sum over `j`
  refine integrable_finsetSum Finset.univ ?_
  intro j _
  -- `û_j` integrable on the compact (finite-measure) `K`
  have hmem : MemLp ((𝓕 (L2VF_projComponentC_R3 j u) : L2C_R3) : Domain3 → ℂ) 2
      (volume.restrict K) :=
    (Lp.memLp (𝓕 (L2VF_projComponentC_R3 j u))).restrict K
  haveI : IsFiniteMeasure ((volume : Measure Domain3).restrict K) :=
    ⟨by simpa using hK.measure_lt_top (μ := (volume : Measure Domain3))⟩
  have hintK : IntegrableOn ((𝓕 (L2VF_projComponentC_R3 j u) : L2C_R3) : Domain3 → ℂ) K
      (volume : Measure Domain3) := hmem.integrable (by norm_num)
  -- multiply by the continuous weight `ξ ↦ ξ_j`
  have hcont : ContinuousOn (fun ξ : Domain3 => (ξ j : ℂ)) K :=
    (Complex.continuous_ofReal.comp
      (EuclideanSpace.proj (𝕜 := ℝ) j).continuous).continuousOn
  exact hintK.continuousOn_mul hcont hK

/-- The whole weak-divergence functional, complexified, as a single Fourier-side integral
against the transverse defect:
`(divTestFunctional φ u : ℂ) = ∫ conj((2π i) 𝓕(φ̂)(ξ)) · T_u(ξ) dξ`. -/
private theorem divTestFunctional_eq_fourier_integral
    (φ : SchwartzMap Domain3 ℝ) (u : L2VF_R3) :
    ((divTestFunctional φ u : ℝ) : ℂ)
      = ∫ ξ : Domain3,
          (starRingEnd ℂ) ((2 * Real.pi * Complex.I)
              * (𝓕 (schwartzC φ) : SchwartzMap Domain3 ℂ) ξ)
            * transverseDefect u ξ
        ∂(volume : Measure Domain3) := by
  -- expand `divTestFunctional` as a finite sum of component pairings
  rw [divTestFunctional, ContinuousLinearMap.sum_apply, Complex.ofReal_sum]
  -- each summand is its Fourier integral
  have hterm : ∀ j : Fin 3,
      (((((innerSL ℝ ((lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
            (EuclideanSpace.single j (1 : ℝ) : Domain3) φ).toLp 2 (volume : Measure Domain3))).comp
          (L2VF_projComponent_R3 j)) u : ℝ)) : ℂ)
        = ∫ ξ : Domain3,
            (starRingEnd ℂ)
                ((2 * Real.pi * Complex.I) * ((ξ j : ℝ) : ℂ)
                  * (𝓕 (schwartzC φ) : SchwartzMap Domain3 ℂ) ξ)
              * (𝓕 (L2VF_projComponentC_R3 j u) : L2C_R3) ξ
          ∂(volume : Measure Domain3) := by
    intro j
    rw [ContinuousLinearMap.comp_apply, innerSL_apply_apply]
    exact divComponent_eq_fourier_integral φ u j
  rw [Finset.sum_congr rfl (fun j _ => hterm j)]
  -- swap sum and integral (each integrand integrable)
  rw [← integral_finsetSum _ (fun j _ => integrable_divComponent φ u j)]
  refine integral_congr_ae ?_
  filter_upwards with ξ
  -- pull out the common factor `conj(2πi φ̂)` and use `conj ξ_j = ξ_j`
  rw [transverseDefect, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro j _
  simp only [map_mul, Complex.conj_ofReal]
  ring

/-- Membership in `L2Sigma_R3` is exactly: every Schwartz weak-divergence test integral
vanishes.  Unfolds `L2Sigma_R3 = ⨅ φ, ker (divTestFunctional φ)` and feeds in the Fourier
form `divTestFunctional_eq_fourier_integral`. -/
private theorem mem_sigma_iff_fourier_integral_zero (u : L2VF_R3) :
    u ∈ L2Sigma_R3 ↔
      ∀ φ : SchwartzMap Domain3 ℝ,
        ∫ ξ : Domain3,
            (starRingEnd ℂ) ((2 * Real.pi * Complex.I)
                * (𝓕 (schwartzC φ) : SchwartzMap Domain3 ℂ) ξ)
              * transverseDefect u ξ
          ∂(volume : Measure Domain3) = 0 := by
  rw [L2Sigma_R3, Submodule.mem_iInf]
  constructor
  · intro h φ
    have hker : divTestFunctional φ u = 0 := by
      have := h φ; rwa [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at this
    have := divTestFunctional_eq_fourier_integral φ u
    rw [hker] at this
    simpa using this.symm
  · intro h φ
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
    have hfi := divTestFunctional_eq_fourier_integral φ u
    rw [h φ] at hfi
    exact_mod_cast hfi

/-- The goal's `EventuallyEq (… True)` form is `∀ᵐ ξ, transverseDefect u ξ = 0`. -/
private theorem transverse_ae_iff (u : L2VF_R3) :
    ((fun ξ =>
          IsTransverseAt
            (fun j => (𝓕 (L2VF_projComponentC_R3 j u) : L2C_R3) ξ) ξ)
        =ᵐ[volume] fun _ => True)
      ↔ (∀ᵐ ξ ∂(volume : Measure Domain3), transverseDefect u ξ = 0) := by
  constructor
  · intro h
    filter_upwards [h] with ξ hξ
    -- `hξ : IsTransverseAt … ξ = True`, so the proposition holds
    have : IsTransverseAt (fun j => (𝓕 (L2VF_projComponentC_R3 j u) : L2C_R3) ξ) ξ := by
      rw [hξ]; trivial
    simpa [transverseDefect, IsTransverseAt] using this
  · intro h
    filter_upwards [h] with ξ hξ
    -- turn `transverseDefect u ξ = 0` into `IsTransverseAt … = True`
    have : IsTransverseAt (fun j => (𝓕 (L2VF_projComponentC_R3 j u) : L2C_R3) ξ) ξ := by
      simpa [transverseDefect, IsTransverseAt] using hξ
    simp [this]

/-- The Fourier test symbol attached to a real Schwartz `φ` in the weak-divergence pairing:
`testSymbol φ ξ = conj((2π i)·𝓕(schwartzC φ)(ξ))`.  As `φ` ranges over all real Schwartz
functions this is exactly the available family of test symbols paired against the transverse
defect in `divTestFunctional_eq_fourier_integral` / `mem_sigma_iff_fourier_integral_zero`. -/
private noncomputable def testSymbol (φ : SchwartzMap Domain3 ℝ) (ξ : Domain3) : ℂ :=
  (starRingEnd ℂ)
    ((2 * Real.pi * Complex.I) * (𝓕 (schwartzC φ) : SchwartzMap Domain3 ℂ) ξ)

/-- **Anti-Hermitian symmetry of the available test symbols.**  For a real Schwartz `φ`, the
test symbol `testSymbol φ` is anti-Hermitian: `testSymbol φ (-ξ) = -conj(testSymbol φ ξ)`.

This is the structural constraint behind the Hermitian wall in the forward direction: every
test symbol obtainable from a *real* `φ` is anti-Hermitian, so the all-`g` hypothesis of
mathlib's `ae_eq_zero_of_integral_contDiff_smul_eq_zero` cannot be met by a single `φ`; an
even/odd reduction over this symmetry is required.  Proof: `fourier_schwartzC_hermitian`
gives `φ̂(-ξ) = conj(φ̂(ξ))`, and `conj((2πi)·) = -2πi·conj(·)` flips the sign of the
factor `2πi`. -/
private theorem testSymbol_antiHermitian (φ : SchwartzMap Domain3 ℝ) (ξ : Domain3) :
    testSymbol φ (-ξ) = -(starRingEnd ℂ) (testSymbol φ ξ) := by
  -- `conj(2πi) = -2πi`
  have hconj : (starRingEnd ℂ) (2 * Real.pi * Complex.I)
      = -(2 * Real.pi * Complex.I) := by
    rw [map_mul, map_mul, Complex.conj_I, Complex.conj_ofReal,
      show ((2 : ℂ)) = ((2 : ℝ) : ℂ) by norm_num, Complex.conj_ofReal]
    ring
  show (starRingEnd ℂ) ((2 * Real.pi * Complex.I) * (𝓕 (schwartzC φ) : _) (-ξ))
      = -(starRingEnd ℂ) ((starRingEnd ℂ) ((2 * Real.pi * Complex.I)
          * (𝓕 (schwartzC φ) : _) ξ))
  rw [fourier_schwartzC_hermitian φ ξ, Complex.conj_conj]
  rw [map_mul, hconj, Complex.conj_conj]
  ring

/-! #### (P1) Lp-level Hermitian reflection of the Fourier transform of a real component

The a.e. Hermitian symmetry of the L²-Fourier transform of a *complexified real* `Lp`
function: `(𝓕 (ofReal ∘ a))(-ξ) =ᵐ conj((𝓕 (ofReal ∘ a)) ξ)`.  This is the `(-·)` analogue
of `FourierL2.fourier_translate_eq`, proved by the same `DenseRange.induction_on` template over
the real Schwartz functions, with base case the already-proved Schwartz-level
`fourier_schwartzC_hermitian`.  The two sides are realised as honest `Lp` operations:
reflection `g ↦ g ∘ (-·)` (`Lp.compMeasurePreserving Neg.neg`, the measure-preserving negation
involution on `volume`) and conjugation `g ↦ conj ∘ g` (`Complex.conjCLE.compLpL`).

This discharges what was, in the forward direction below, the first of two named analytic
blockers (the `(P1)` reflection identity).  It is genuine analysis, axiom-free, no `sorry`. -/

/-- Base case of (P1): the reflected Fourier transform of a complexified real Schwartz rep
equals the conjugated one, as `Lp` elements.  Uses the Schwartz-level Hermitian identity
`fourier_schwartzC_hermitian` lifted through `toLp`. -/
private theorem reflect_fourier_schwartzC_eq_conj (φ : SchwartzMap Domain3 ℝ) :
    Lp.compMeasurePreserving (Neg.neg : Domain3 → Domain3)
        (Measure.measurePreserving_neg (volume : Measure Domain3))
        (𝓕 ((schwartzC φ).toLp 2 (volume : Measure Domain3)))
      = (Complex.conjCLE : ℂ →L[ℝ] ℂ).compLpL 2 (volume : Measure Domain3)
        (𝓕 ((schwartzC φ).toLp 2 (volume : Measure Domain3))) := by
  rw [SchwartzMap.toLp_fourier_eq]
  refine Lp.ext ?_
  have hL := Lp.coeFn_compMeasurePreserving
    ((𝓕 (schwartzC φ)).toLp 2 (volume : Measure Domain3))
    (Measure.measurePreserving_neg (volume : Measure Domain3))
  have hR := (Complex.conjCLE : ℂ →L[ℝ] ℂ).coeFn_compLpL
    ((𝓕 (schwartzC φ)).toLp 2 (volume : Measure Domain3))
  have hcoe := (𝓕 (schwartzC φ)).coeFn_toLp 2 (volume : Measure Domain3)
  have hcoeNeg : (fun ξ => ((𝓕 (schwartzC φ)).toLp 2 (volume : Measure Domain3) : Domain3 → ℂ) (-ξ))
      =ᵐ[volume] fun ξ => (𝓕 (schwartzC φ) : SchwartzMap Domain3 ℂ) (-ξ) :=
    (Measure.measurePreserving_neg
      (volume : Measure Domain3)).quasiMeasurePreserving.ae_eq hcoe
  filter_upwards [hL, hR, hcoe, hcoeNeg] with ξ hLξ hRξ hcξ hcNegξ
  rw [hLξ, hRξ, Function.comp_apply, hcNegξ, hcξ]
  rw [fourier_schwartzC_hermitian φ ξ]
  rfl

set_option maxHeartbeats 1000000 in
/-- **(P1) Lp-level Hermitian reflection.**  For a real `a : Lp ℝ 2`, the reflection of the
Fourier transform of its complexification equals the conjugation of that Fourier transform,
as elements of `L2C_R3`.  Density extension of `reflect_fourier_schwartzC_eq_conj` over the
real Schwartz functions (`SchwartzMap.denseRange_toLpCLM`). -/
private theorem fourier_ofReal_reflect_eq_conj
    (a : Lp ℝ 2 (volume : Measure Domain3)) :
    Lp.compMeasurePreserving (Neg.neg : Domain3 → Domain3)
        (Measure.measurePreserving_neg (volume : Measure Domain3))
        (𝓕 ((RCLike.ofRealCLM (K := ℂ)).compLpL 2 (volume : Measure Domain3) a))
      = (Complex.conjCLE : ℂ →L[ℝ] ℂ).compLpL 2 (volume : Measure Domain3)
        (𝓕 ((RCLike.ofRealCLM (K := ℂ)).compLpL 2 (volume : Measure Domain3) a)) := by
  let emb : Lp ℝ 2 (volume : Measure Domain3) → L2C_R3 := fun a =>
    (RCLike.ofRealCLM (K := ℂ)).compLpL 2 (volume : Measure Domain3) a
  let R : L2C_R3 → L2C_R3 := fun g =>
    Lp.compMeasurePreserving (Neg.neg : Domain3 → Domain3)
      (Measure.measurePreserving_neg (volume : Measure Domain3)) g
  have hRcont : Continuous R :=
    (Lp.compMeasurePreservingₗᵢ (E := ℂ) (p := 2) ℂ (Neg.neg : Domain3 → Domain3)
      (Measure.measurePreserving_neg (volume : Measure Domain3))).continuous
  have hembCont : Continuous emb :=
    ((RCLike.ofRealCLM (K := ℂ)).compLpL 2 (volume : Measure Domain3)).continuous
  refine DenseRange.induction_on
    (SchwartzMap.denseRange_toLpCLM (F := ℝ) (p := 2) ENNReal.ofNat_ne_top) a
    (p := fun a => R (𝓕 (emb a))
      = (Complex.conjCLE : ℂ →L[ℝ] ℂ).compLpL 2 (volume : Measure Domain3) (𝓕 (emb a)))
    ?_ ?_
  · refine isClosed_eq ?_ ?_
    · exact hRcont.comp (continuous_fourier.comp hembCont)
    · exact ((Complex.conjCLE : ℂ →L[ℝ] ℂ).compLpL 2 (volume : Measure Domain3)).continuous.comp
        (continuous_fourier.comp hembCont)
  · intro φ
    have hembφ : emb (SchwartzMap.toLpCLM ℝ ℝ 2 volume φ)
        = (schwartzC φ).toLp 2 (volume : Measure Domain3) := by
      show (RCLike.ofRealCLM (K := ℂ)).compLpL 2 (volume : Measure Domain3)
          (SchwartzMap.toLpCLM ℝ ℝ 2 volume φ)
        = (schwartzC φ).toLp 2 (volume : Measure Domain3)
      rw [SchwartzMap.toLpCLM_apply, ← toLp_schwartzC_eq]
    show R (𝓕 (emb (SchwartzMap.toLpCLM ℝ ℝ 2 volume φ)))
      = (Complex.conjCLE : ℂ →L[ℝ] ℂ).compLpL 2 (volume : Measure Domain3)
          (𝓕 (emb (SchwartzMap.toLpCLM ℝ ℝ 2 volume φ)))
    rw [hembφ]
    exact reflect_fourier_schwartzC_eq_conj φ

/-- **Reverse direction (a.e. transverse ⇒ weakly divergence-free).**  If the transverse
defect `T_u` vanishes a.e., then every Schwartz weak-divergence test integral vanishes, so
`u ∈ L2Sigma_R3`. -/
private theorem mem_sigma_of_transverse_ae (u : L2VF_R3)
    (h : ∀ᵐ ξ ∂(volume : Measure Domain3), transverseDefect u ξ = 0) :
    u ∈ L2Sigma_R3 := by
  rw [mem_sigma_iff_fourier_integral_zero]
  intro φ
  rw [show (0 : ℂ) = ∫ _ξ : Domain3, (0 : ℂ) ∂(volume : Measure Domain3) by simp]
  refine integral_congr_ae ?_
  filter_upwards [h] with ξ hξ
  rw [hξ, mul_zero]

/-! #### (P2) Schwartz Hermitian preimage — PROVED

This lemma (formerly the single analytic gap blocking the forward direction of
`mem_sigma_iff_fourier_transverse`) is now PROVED, axiom-free, via the reality lemma
`fourier_hermitian_real`.  The forward direction is consequently fully discharged.

Axiom removal wired in `CurlDensityCapstone.lean` (Route A, issue #3):
`curlSchwartzDense_provedRoute` here is the sorry-free, axiom-free proof; that file
re-anchors `curlSchwartzDense_holds` / `nonempty_schwartzGalerkinBasis` /
`r3GalerkinScheme_exists` to this proved theorem, eliminating the axiom. -/

/-- **Reality of the Fourier transform of a Hermitian Schwartz function.**  If
`g : 𝓢(ℝ³, ℂ)` is Hermitian (`g(-v) = conj(g(v))` for all `v`), then `𝓕 g` is real-valued:
`conj(𝓕 g ξ) = 𝓕 g ξ`.

Pointwise integral argument (mirrors `fourier_schwartzC_hermitian`): pushing `conj` into the
integral defining `𝓕 g ξ = ∫ 𝐞(-⟪v,ξ⟫) g v` turns the unit-modulus character into its
inverse `𝐞(⟪v,ξ⟫)` and conjugates the integrand to `g(-v)` (Hermitian); the substitution
`v ↦ -v` (negation is measure preserving) restores `∫ 𝐞(-⟪v,ξ⟫) g v = 𝓕 g ξ`. -/
theorem fourier_hermitian_real
    (g : SchwartzMap Domain3 ℂ)
    (hg : ∀ v : Domain3, g (-v) = (starRingEnd ℂ) (g v)) (ξ : Domain3) :
    (starRingEnd ℂ) ((𝓕 g : SchwartzMap Domain3 ℂ) ξ) = (𝓕 g : SchwartzMap Domain3 ℂ) ξ := by
  -- Move to the underlying function `𝓕 (g : Domain3 → ℂ)`.
  have hcoe : ((𝓕 g : SchwartzMap Domain3 ℂ) : Domain3 → ℂ) = 𝓕 ((g : Domain3 → ℂ)) :=
    SchwartzMap.fourier_coe g
  rw [show (𝓕 g : SchwartzMap Domain3 ℂ) ξ = 𝓕 ((g : Domain3 → ℂ)) ξ from congrFun hcoe ξ]
  -- LHS: push `conj` into the integral defining `𝓕 _ ξ`.
  rw [Real.fourier_eq, ← integral_conj]
  -- Conjugated integrand `conj(𝐞(-⟪v,ξ⟫) • g v) = 𝐞(⟪v,ξ⟫) • g(-v)`.
  have hconj : (∫ v : Domain3, (starRingEnd ℂ) ((Real.fourierChar (-(inner ℝ v ξ : ℝ))) • g v)
        ∂(volume : Measure Domain3))
      = ∫ v : Domain3, (Real.fourierChar (-(inner ℝ (-v) ξ : ℝ))) • g (-v)
        ∂(volume : Measure Domain3) := by
    refine integral_congr_ae ?_
    filter_upwards with v
    simp only [Circle.smul_def, smul_eq_mul, inner_neg_left, map_mul, neg_neg]
    rw [hg v]
    -- character: `conj((𝐞 (-⟪v,ξ⟫) : ℂ)) = (𝐞 (⟪v,ξ⟫) : ℂ)`
    rw [← Circle.coe_inv_eq_conj, ← AddChar.map_neg_eq_inv, neg_neg]
  rw [hconj]
  -- substitute `v ↦ -v`: `∫ F(-v) = ∫ F(v)`, recovering `𝓕 g ξ`.
  rw [integral_neg_eq_self (fun v => (Real.fourierChar (-(inner ℝ v ξ : ℝ))) • g v)
    (volume : Measure Domain3)]

/-- **(P2) Schwartz Hermitian preimage extraction (must-prove — item 11 in the plan).**

If `h : 𝓢(ℝ³, ℂ)` is anti-Hermitian in the sense `h(-ξ) = -conj(h(ξ))` (i.e. `h` is an
anti-Hermitian Schwartz symbol, exactly the kind produced by `testSymbol φ` for real `φ`),
then there exists `φ : 𝓢(ℝ³, ℝ)` such that `testSymbol φ = h`.

**Constructibility sketch** (no Mathlib PR needed — all primitives present):
- Let `g = (2πi)⁻¹ • h` (Hermitian: `g(-ξ) = conj(g(ξ))`).
- Let `Ψ : 𝓢(ℝ³, ℂ)` be the Schwartz inverse Fourier transform `𝓕⁻ g`
  (`FourierTransform.fourierCLE.symm` applied to `g`).
- Since `g` is Hermitian, `Ψ` is real-valued: use `fourier_ofReal_reflect_eq_conj` (proved,
  P1 above) to establish that `𝓕⁻ g` is real-valued, so `Im Ψ = 0`.
- Extract the real Schwartz function `φ := Ψ.postcompCLM reCLM`
  (via `SchwartzMap.postcompCLM (RCLike.reCLM : ℂ →L[ℝ] ℝ)`, which gives `φ ξ = Re(Ψ ξ)`).
- Verify `testSymbol φ = h`:
  `testSymbol φ ξ = conj((2πi) · 𝓕(schwartzC φ)(ξ))`.
  Since `Ψ` is real-valued, `schwartzC φ = schwartzC (Re Ψ) = Ψ` (as Schwartz maps).
  Then `𝓕(Ψ) = 𝓕(𝓕⁻ g) = g` by `FourierInvPair`, and `conj((2πi)·g) = h` by definition of `g`.

Key Mathlib decls: `SchwartzMap.postcompCLM`, `Complex.conjCLE`, `RCLike.reCLM`,
`FourierTransform.fourierCLE` (symm), `FourierInvPair`,
`fourier_ofReal_reflect_eq_conj` (item 9, proved above). -/
private theorem schwartz_antiHermitian_has_testSymbol_preimage
    (h : SchwartzMap Domain3 ℂ)
    (hH : ∀ ξ : Domain3, h (-ξ) = -(starRingEnd ℂ) (h ξ)) :
    ∃ φ : SchwartzMap Domain3 ℝ, testSymbol φ = h := by
  -- The factor `c = 2π i` and its (non-zero) inverse.
  set c : ℂ := 2 * Real.pi * Complex.I with hc
  have hcne : c ≠ 0 := by
    rw [hc]; simp [Real.pi_ne_zero, Complex.I_ne_zero]
  -- `conj c = -c`.
  have hconjc : (starRingEnd ℂ) c = -c := by
    rw [hc, map_mul, map_mul, Complex.conj_I, Complex.conj_ofReal,
      show ((2 : ℂ)) = ((2 : ℝ) : ℂ) by norm_num, Complex.conj_ofReal]
    ring
  -- `g := c⁻¹ • (conj ∘ h)`, a Schwartz map with `g ξ = c⁻¹ * conj (h ξ)`.
  set g : SchwartzMap Domain3 ℂ :=
    c⁻¹ • (h.postcompCLM (Complex.conjCLE : ℂ →L[ℝ] ℂ)) with hgdef
  have hg_apply : ∀ ξ : Domain3, g ξ = c⁻¹ * (starRingEnd ℂ) (h ξ) := by
    intro ξ
    rw [hgdef, SchwartzMap.smul_apply, SchwartzMap.postcompCLM_apply, smul_eq_mul]
    rfl
  -- `g` is Hermitian: `g (-ξ) = conj (g ξ)`.
  have hgHerm : ∀ ξ : Domain3, g (-ξ) = (starRingEnd ℂ) (g ξ) := by
    intro ξ
    rw [hg_apply, hg_apply, hH ξ, map_mul, Complex.conj_conj, map_neg, Complex.conj_conj,
      map_inv₀, hconjc]
    ring
  -- `Φ := 𝓕⁻ g`, the Schwartz inverse Fourier transform of `g`.
  set Φ : SchwartzMap Domain3 ℂ := 𝓕⁻ g with hΦdef
  -- `Φ` is real-valued: `conj (Φ ξ) = Φ ξ`.
  have hΦreal : ∀ ξ : Domain3, (starRingEnd ℂ) (Φ ξ) = Φ ξ := by
    intro ξ
    -- pointwise `𝓕⁻ g ξ = 𝓕 g (-ξ)`.
    have hcoeInv : (Φ : Domain3 → ℂ) = 𝓕⁻ ((g : Domain3 → ℂ)) := by
      rw [hΦdef]; exact SchwartzMap.fourierInv_coe g
    have hcoeF : ((𝓕 g : SchwartzMap Domain3 ℂ) : Domain3 → ℂ) = 𝓕 ((g : Domain3 → ℂ)) :=
      SchwartzMap.fourier_coe g
    have hΦpt : Φ ξ = (𝓕 g : SchwartzMap Domain3 ℂ) (-ξ) := by
      rw [show Φ ξ = (Φ : Domain3 → ℂ) ξ from rfl, hcoeInv,
        Real.fourierInv_eq_fourier_neg,
        show 𝓕 ((g : Domain3 → ℂ)) (-ξ) = ((𝓕 g : SchwartzMap Domain3 ℂ) : Domain3 → ℂ) (-ξ)
          from (congrFun hcoeF (-ξ)).symm]
    rw [hΦpt, fourier_hermitian_real g hgHerm]
  -- `φ := Re ∘ Φ` as a real Schwartz function.
  refine ⟨Φ.postcompCLM (RCLike.reCLM (K := ℂ)), ?_⟩
  -- `schwartzC φ = Φ` (since `Φ` is real-valued).
  have hschwartzCφ : schwartzC (Φ.postcompCLM (RCLike.reCLM (K := ℂ))) = Φ := by
    apply SchwartzMap.ext
    intro ξ
    rw [schwartzC_apply, SchwartzMap.postcompCLM_apply, RCLike.reCLM_apply]
    -- `(Re (Φ ξ) : ℂ) = Φ ξ` because `Φ ξ` is real (`conj = id`).
    have := hΦreal ξ
    rw [Complex.conj_eq_iff_re] at this
    rw [RCLike.re_to_complex]
    exact this
  -- `𝓕 (schwartzC φ) = 𝓕 Φ = 𝓕 (𝓕⁻ g) = g`.
  have hFourierφ : (𝓕 (schwartzC (Φ.postcompCLM (RCLike.reCLM (K := ℂ))))
      : SchwartzMap Domain3 ℂ) = g := by
    rw [hschwartzCφ, hΦdef, fourier_fourierInv_eq]
  -- Finish: `testSymbol φ ξ = conj (c · g ξ) = conj (conj (h ξ)) = h ξ`.
  funext ξ
  rw [testSymbol]
  rw [show (𝓕 (schwartzC (Φ.postcompCLM (RCLike.reCLM (K := ℂ)))) : SchwartzMap Domain3 ℂ) ξ
      = g ξ from congrFun (congrArg (fun (f : SchwartzMap Domain3 ℂ) => (f : Domain3 → ℂ))
        hFourierφ) ξ]
  rw [hg_apply ξ, ← mul_assoc, mul_inv_cancel₀ hcne, one_mul, Complex.conj_conj]

/-- **Anti-Hermitian test integral vanishing.**  If `u ∈ L2Sigma_R3`, then for every
*anti-Hermitian* Schwartz symbol `h` (`h(-ξ) = -conj(h ξ)`), the Fourier-side pairing
`∫ h(ξ) · T_u(ξ) dξ` vanishes.

This is `mem_sigma_iff_fourier_integral_zero` upgraded by `(P2)`: the available test symbols
`testSymbol φ` (`φ` real Schwartz) range over *all* anti-Hermitian Schwartz symbols
(`schwartz_antiHermitian_has_testSymbol_preimage`), so the vanishing of every `testSymbol`
pairing extends to every anti-Hermitian Schwartz pairing. -/
private theorem antiHermitianTest_integral_zero (u : L2VF_R3) (hmem : u ∈ L2Sigma_R3)
    (h : SchwartzMap Domain3 ℂ) (hH : ∀ ξ : Domain3, h (-ξ) = -(starRingEnd ℂ) (h ξ)) :
    ∫ ξ : Domain3, (h : Domain3 → ℂ) ξ * transverseDefect u ξ
        ∂(volume : Measure Domain3) = 0 := by
  obtain ⟨φ, hφ⟩ := schwartz_antiHermitian_has_testSymbol_preimage h hH
  have hzero := (mem_sigma_iff_fourier_integral_zero u).1 hmem φ
  -- the integrand `conj((2πi)·𝓕(schwartzC φ)) = testSymbol φ = h`.
  rw [← hzero]
  refine integral_congr_ae ?_
  filter_upwards with ξ
  rw [show (starRingEnd ℂ) ((2 * Real.pi * Complex.I)
        * (𝓕 (schwartzC φ) : SchwartzMap Domain3 ℂ) ξ) = testSymbol φ ξ from rfl,
    show testSymbol φ ξ = (h : Domain3 → ℂ) ξ from congrFun hφ ξ]

/-- **Step 2 (spectral div-free characterization).**  A field `u ∈ L2VF_R3` is weakly
divergence-free (`u ∈ L2Sigma_R3`) iff its Fourier transform is a.e. transverse:
`∑ j, ξ_j û_j(ξ) = 0` for a.e. `ξ`.

This is the Fourier transcription of `div u = 0`: pairing with `∂_j φ` and applying Plancherel
turns the weak-divergence functional `divTestFunctional` into the pairing of `∑_j ξ_j û_j(ξ)`
against the (dense set of) Schwartz `φ̂`.

Blocker: requires Plancherel for the `divTestFunctional` pairing plus the
fundamental lemma of the calculus of variations on the Fourier side (a transverse symbol that
pairs to zero against all Schwartz `φ̂` vanishes a.e.).  Genuine analysis; lean-prover target
on `FourierL2` (`normSq_eq_integral_normSq_C`, `fourierComponentC_ae_schwartz`). -/
theorem mem_sigma_iff_fourier_transverse (u : L2VF_R3) :
    u ∈ L2Sigma_R3 ↔
      (fun ξ =>
          IsTransverseAt
            (fun j => (𝓕 (L2VF_projComponentC_R3 j u) : L2C_R3) ξ) ξ)
        =ᵐ[volume] fun _ => True := by
  rw [transverse_ae_iff u]
  constructor
  · -- Forward (du-Bois-Reymond on the Fourier side): the hard analytic direction.
    intro hmem
    -- We have, from `hmem` and `mem_sigma_iff_fourier_integral_zero`:
    --   ∀ φ real Schwartz, ∫ conj((2πi)·𝓕(schwartzC φ)) · T_u = 0.
    -- `transverseDefect u` is locally integrable (`locallyIntegrable_transverseDefect`),
    -- and (by `fourier_schwartzC_hermitian`) the available test symbols
    --   { conj((2πi)·𝓕(schwartzC φ)) : φ real }
    -- are exactly the ANTI-HERMITIAN Schwartz symbols, while `T_u` is itself anti-Hermitian
    -- (`û_j` Hermitian as Fourier of a real component).  Testing an anti-Hermitian locally
    -- integrable function against all anti-Hermitian Schwartz symbols pins it a.e. to zero
    -- via the even/odd-part reduction to `ae_eq_zero_of_integral_contDiff_smul_eq_zero`.
    have hLI := locallyIntegrable_transverseDefect u
    -- du-Bois-Reymond: it suffices to test `T_u` against every real smooth compactly
    -- supported `g`.  Each such `g` splits as `2g = gE + gO` into (twice the) even/odd parts,
    -- whose complexifications (`i·gE`, `gO`) are anti-Hermitian Schwartz symbols handled by
    -- `antiHermitianTest_integral_zero`.
    refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hLI ?_
    intro g g_diff g_supp
    -- `g ∘ neg` is smooth and compactly supported.
    have hneg_diff : ContDiff ℝ (⊤ : ℕ∞) (fun ξ : Domain3 => g (-ξ)) :=
      g_diff.comp contDiff_neg
    have hneg_supp : HasCompactSupport (fun ξ : Domain3 => g (-ξ)) := by
      have := g_supp.comp_homeomorph (Homeomorph.neg Domain3)
      simpa [Function.comp_def] using this
    -- twice-even / twice-odd parts `gE = g + g∘neg`, `gO = g − g∘neg`.
    set gE : Domain3 → ℝ := fun ξ => g ξ + g (-ξ) with hgE
    set gO : Domain3 → ℝ := fun ξ => g ξ - g (-ξ) with hgO
    have hgE_diff : ContDiff ℝ (⊤ : ℕ∞) gE := g_diff.add hneg_diff
    have hgO_diff : ContDiff ℝ (⊤ : ℕ∞) gO := g_diff.sub hneg_diff
    have hgE_supp : HasCompactSupport gE := g_supp.add hneg_supp
    have hgO_supp : HasCompactSupport gO := g_supp.sub hneg_supp
    -- complexifications: `i·gE` (anti-Herm) and `gO` (anti-Herm).
    have hCE_diff : ContDiff ℝ (⊤ : ℕ∞) (fun ξ : Domain3 => Complex.I * (gE ξ : ℂ)) :=
      contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hgE_diff)
    have hCE_supp : HasCompactSupport (fun ξ : Domain3 => Complex.I * (gE ξ : ℂ)) :=
      (hgE_supp.comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero).mul_left
    have hCO_diff : ContDiff ℝ (⊤ : ℕ∞) (fun ξ : Domain3 => (gO ξ : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp hgO_diff
    have hCO_supp : HasCompactSupport (fun ξ : Domain3 => (gO ξ : ℂ)) :=
      hgO_supp.comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero
    -- as Schwartz maps (the coercion is definitionally the underlying function).
    set hE : SchwartzMap Domain3 ℂ := hCE_supp.toSchwartzMap hCE_diff with hhE
    set hO : SchwartzMap Domain3 ℂ := hCO_supp.toSchwartzMap hCO_diff with hhO
    have hE_coe : ∀ ξ : Domain3, hE ξ = Complex.I * (gE ξ : ℂ) := fun _ => rfl
    have hO_coe : ∀ ξ : Domain3, hO ξ = (gO ξ : ℂ) := fun _ => rfl
    -- anti-Hermitian conditions.
    have hE_aH : ∀ ξ : Domain3, hE (-ξ) = -(starRingEnd ℂ) (hE ξ) := by
      intro ξ
      rw [hE_coe, hE_coe]
      have heq : gE (-ξ) = gE ξ := by simp only [hgE, neg_neg]; ring
      rw [heq, map_mul, Complex.conj_I, Complex.conj_ofReal]; ring
    have hO_aH : ∀ ξ : Domain3, hO (-ξ) = -(starRingEnd ℂ) (hO ξ) := by
      intro ξ
      rw [hO_coe, hO_coe]
      have heq : gO (-ξ) = -gO ξ := by simp only [hgO, neg_neg]; ring
      rw [heq, Complex.conj_ofReal, Complex.ofReal_neg]
    -- the two anti-Hermitian pairings vanish.
    have hEZero := antiHermitianTest_integral_zero u hmem hE hE_aH
    have hOZero := antiHermitianTest_integral_zero u hmem hO hO_aH
    simp only [hE_coe, hO_coe] at hEZero hOZero
    -- integrability of the compactly-supported pieces against the locally integrable `T_u`.
    have hInt : ∀ k : Domain3 → ℝ, Continuous k → HasCompactSupport k →
        Integrable (fun ξ : Domain3 => (k ξ : ℂ) * transverseDefect u ξ)
          (volume : Measure Domain3) := by
      intro k hk_cont hk_supp
      have := hLI.integrable_smul_left_of_hasCompactSupport (𝕜 := ℂ)
        (g := fun ξ : Domain3 => (k ξ : ℂ))
        (Complex.continuous_ofReal.comp hk_cont)
        (hk_supp.comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero)
      simpa [smul_eq_mul] using this
    have hIntE := hInt gE hgE_diff.continuous hgE_supp
    have hIntO := hInt gO hgO_diff.continuous hgO_supp
    -- `∫ (gE:ℂ)·T_u = 0` (drop the `Complex.I` factor from `hEZero`).
    have hEZero' : ∫ ξ : Domain3, (gE ξ : ℂ) * transverseDefect u ξ
        ∂(volume : Measure Domain3) = 0 := by
      have hI : Complex.I * ∫ ξ : Domain3, (gE ξ : ℂ) * transverseDefect u ξ
          ∂(volume : Measure Domain3) = 0 := by
        rw [← integral_const_mul]
        simp_rw [← mul_assoc]
        exact hEZero
      exact (mul_eq_zero.1 hI).resolve_left Complex.I_ne_zero
    -- assemble: `∫ (g:ℂ)·T_u = (∫ (gE:ℂ)·T_u + ∫ (gO:ℂ)·T_u)/2 = 0`.
    have hsplit : ∀ ξ : Domain3,
        (g ξ : ℂ) * transverseDefect u ξ
          = (2 : ℂ)⁻¹ * ((gE ξ : ℂ) * transverseDefect u ξ
              + (gO ξ : ℂ) * transverseDefect u ξ) := by
      intro ξ
      simp only [hgE, hgO]
      push_cast
      ring
    calc ∫ ξ : Domain3, g ξ • transverseDefect u ξ ∂(volume : Measure Domain3)
        = ∫ ξ : Domain3, (2 : ℂ)⁻¹ * ((gE ξ : ℂ) * transverseDefect u ξ
            + (gO ξ : ℂ) * transverseDefect u ξ) ∂(volume : Measure Domain3) := by
          refine integral_congr_ae ?_
          filter_upwards with ξ
          rw [Complex.real_smul, hsplit ξ]
      _ = (2 : ℂ)⁻¹ * (∫ ξ : Domain3, ((gE ξ : ℂ) * transverseDefect u ξ
            + (gO ξ : ℂ) * transverseDefect u ξ) ∂(volume : Measure Domain3)) := by
          rw [integral_const_mul]
      _ = (2 : ℂ)⁻¹ * ((∫ ξ : Domain3, (gE ξ : ℂ) * transverseDefect u ξ
            ∂(volume : Measure Domain3))
            + ∫ ξ : Domain3, (gO ξ : ℂ) * transverseDefect u ξ
            ∂(volume : Measure Domain3)) := by
          rw [integral_add hIntE hIntO]
      _ = 0 := by rw [hEZero', hOZero]; ring
  · -- Reverse (a.e. transverse ⇒ weakly divergence-free): fully proved.
    intro htr
    exact mem_sigma_of_transverse_ae u htr

/-- **General du-Bois-Reymond against Hermitian Schwartz tests.**  A locally integrable
`f : ℝ³ → ℂ` that integrates to zero against every *Hermitian* Schwartz symbol
(`G(-ξ) = conj(G ξ)`) vanishes a.e.

Same even/odd reduction as the forward direction of `mem_sigma_iff_fourier_transverse`, but
the parity assignment is mirrored: for a real smooth compactly-supported test `g`, the
even part `gE = g + g∘neg` complexifies to a *Hermitian* symbol directly, while `i·gO`
(`gO = g − g∘neg`) is Hermitian; both feed the hypothesis, and `2g = gE + gO`. -/
private theorem ae_zero_of_hermitianTest
    (f : Domain3 → ℂ) (hf : LocallyIntegrable f (volume : Measure Domain3))
    (htest : ∀ G : SchwartzMap Domain3 ℂ, (∀ ξ : Domain3, G (-ξ) = (starRingEnd ℂ) (G ξ)) →
        ∫ ξ : Domain3, (G : Domain3 → ℂ) ξ * f ξ ∂(volume : Measure Domain3) = 0) :
    ∀ᵐ ξ ∂(volume : Measure Domain3), f ξ = 0 := by
  refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hf ?_
  intro g g_diff g_supp
  have hneg_diff : ContDiff ℝ (⊤ : ℕ∞) (fun ξ : Domain3 => g (-ξ)) :=
    g_diff.comp contDiff_neg
  have hneg_supp : HasCompactSupport (fun ξ : Domain3 => g (-ξ)) := by
    have := g_supp.comp_homeomorph (Homeomorph.neg Domain3)
    simpa [Function.comp_def] using this
  set gE : Domain3 → ℝ := fun ξ => g ξ + g (-ξ) with hgE
  set gO : Domain3 → ℝ := fun ξ => g ξ - g (-ξ) with hgO
  have hgE_diff : ContDiff ℝ (⊤ : ℕ∞) gE := g_diff.add hneg_diff
  have hgO_diff : ContDiff ℝ (⊤ : ℕ∞) gO := g_diff.sub hneg_diff
  have hgE_supp : HasCompactSupport gE := g_supp.add hneg_supp
  have hgO_supp : HasCompactSupport gO := g_supp.sub hneg_supp
  -- complexifications: `gE` (Hermitian) and `i·gO` (Hermitian).
  have hCE_diff : ContDiff ℝ (⊤ : ℕ∞) (fun ξ : Domain3 => (gE ξ : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hgE_diff
  have hCE_supp : HasCompactSupport (fun ξ : Domain3 => (gE ξ : ℂ)) :=
    hgE_supp.comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero
  have hCO_diff : ContDiff ℝ (⊤ : ℕ∞) (fun ξ : Domain3 => Complex.I * (gO ξ : ℂ)) :=
    contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hgO_diff)
  have hCO_supp : HasCompactSupport (fun ξ : Domain3 => Complex.I * (gO ξ : ℂ)) :=
    (hgO_supp.comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero).mul_left
  set hE : SchwartzMap Domain3 ℂ := hCE_supp.toSchwartzMap hCE_diff with hhE
  set hO : SchwartzMap Domain3 ℂ := hCO_supp.toSchwartzMap hCO_diff with hhO
  have hE_coe : ∀ ξ : Domain3, hE ξ = (gE ξ : ℂ) := fun _ => rfl
  have hO_coe : ∀ ξ : Domain3, hO ξ = Complex.I * (gO ξ : ℂ) := fun _ => rfl
  -- Hermitian conditions.
  have hE_H : ∀ ξ : Domain3, hE (-ξ) = (starRingEnd ℂ) (hE ξ) := by
    intro ξ
    rw [hE_coe, hE_coe]
    have heq : gE (-ξ) = gE ξ := by simp only [hgE, neg_neg]; ring
    rw [heq, Complex.conj_ofReal]
  have hO_H : ∀ ξ : Domain3, hO (-ξ) = (starRingEnd ℂ) (hO ξ) := by
    intro ξ
    rw [hO_coe, hO_coe]
    have heq : gO (-ξ) = -gO ξ := by simp only [hgO, neg_neg]; ring
    rw [heq, map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_neg]; ring
  have hEZero := htest hE hE_H
  have hOZero := htest hO hO_H
  simp only [hE_coe, hO_coe] at hEZero hOZero
  -- integrability of the compactly-supported pieces against the locally integrable `f`.
  have hInt : ∀ k : Domain3 → ℝ, Continuous k → HasCompactSupport k →
      Integrable (fun ξ : Domain3 => (k ξ : ℂ) * f ξ) (volume : Measure Domain3) := by
    intro k hk_cont hk_supp
    have := hf.integrable_smul_left_of_hasCompactSupport (𝕜 := ℂ)
      (g := fun ξ : Domain3 => (k ξ : ℂ))
      (Complex.continuous_ofReal.comp hk_cont)
      (hk_supp.comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero)
    simpa [smul_eq_mul] using this
  have hIntE := hInt gE hgE_diff.continuous hgE_supp
  have hIntO := hInt gO hgO_diff.continuous hgO_supp
  -- `∫ (gO:ℂ)·f = 0` (drop the `Complex.I` factor from `hOZero`).
  have hOZero' : ∫ ξ : Domain3, (gO ξ : ℂ) * f ξ ∂(volume : Measure Domain3) = 0 := by
    have hI : Complex.I * ∫ ξ : Domain3, (gO ξ : ℂ) * f ξ ∂(volume : Measure Domain3) = 0 := by
      rw [← integral_const_mul]
      simp_rw [← mul_assoc]
      exact hOZero
    exact (mul_eq_zero.1 hI).resolve_left Complex.I_ne_zero
  -- assemble: `∫ g•f = (∫ gE·f + ∫ gO·f)/2 = 0`.
  have hsplit : ∀ ξ : Domain3,
      (g ξ : ℂ) * f ξ
        = (2 : ℂ)⁻¹ * ((gE ξ : ℂ) * f ξ + (gO ξ : ℂ) * f ξ) := by
    intro ξ
    simp only [hgE, hgO]
    push_cast
    ring
  calc ∫ ξ : Domain3, g ξ • f ξ ∂(volume : Measure Domain3)
      = ∫ ξ : Domain3, (2 : ℂ)⁻¹ * ((gE ξ : ℂ) * f ξ + (gO ξ : ℂ) * f ξ)
          ∂(volume : Measure Domain3) := by
        refine integral_congr_ae ?_
        filter_upwards with ξ
        rw [Complex.real_smul, hsplit ξ]
    _ = (2 : ℂ)⁻¹ * (∫ ξ : Domain3, ((gE ξ : ℂ) * f ξ + (gO ξ : ℂ) * f ξ)
          ∂(volume : Measure Domain3)) := by rw [integral_const_mul]
    _ = (2 : ℂ)⁻¹ * ((∫ ξ : Domain3, (gE ξ : ℂ) * f ξ ∂(volume : Measure Domain3))
          + ∫ ξ : Domain3, (gO ξ : ℂ) * f ξ ∂(volume : Measure Domain3)) := by
        rw [integral_add hIntE hIntO]
    _ = 0 := by rw [hEZero, hOZero']; ring

/-- **Hermitian Schwartz preimage under `𝓕 ∘ schwartzC`.**  Every Hermitian Schwartz symbol
`G` (`G(-ξ) = conj(G ξ)`) is `𝓕 (schwartzC φ)` for some *real* Schwartz `φ`.  Same construction
as `schwartz_antiHermitian_has_testSymbol_preimage` (P2), minus the `testSymbol` wrapper:
`Φ = 𝓕⁻ G` is real-valued (`fourier_hermitian_real`), `φ = Re ∘ Φ`, and
`𝓕 (schwartzC φ) = 𝓕 (𝓕⁻ G) = G`. -/
private theorem schwartz_hermitian_has_fourier_preimage
    (G : SchwartzMap Domain3 ℂ) (hH : ∀ ξ : Domain3, G (-ξ) = (starRingEnd ℂ) (G ξ)) :
    ∃ φ : SchwartzMap Domain3 ℝ, (𝓕 (schwartzC φ) : SchwartzMap Domain3 ℂ) = G := by
  set Φ : SchwartzMap Domain3 ℂ := 𝓕⁻ G with hΦdef
  have hΦreal : ∀ ξ : Domain3, (starRingEnd ℂ) (Φ ξ) = Φ ξ := by
    intro ξ
    have hcoeInv : (Φ : Domain3 → ℂ) = 𝓕⁻ ((G : Domain3 → ℂ)) := by
      rw [hΦdef]; exact SchwartzMap.fourierInv_coe G
    have hcoeF : ((𝓕 G : SchwartzMap Domain3 ℂ) : Domain3 → ℂ) = 𝓕 ((G : Domain3 → ℂ)) :=
      SchwartzMap.fourier_coe G
    have hΦpt : Φ ξ = (𝓕 G : SchwartzMap Domain3 ℂ) (-ξ) := by
      rw [show Φ ξ = (Φ : Domain3 → ℂ) ξ from rfl, hcoeInv,
        Real.fourierInv_eq_fourier_neg,
        show 𝓕 ((G : Domain3 → ℂ)) (-ξ) = ((𝓕 G : SchwartzMap Domain3 ℂ) : Domain3 → ℂ) (-ξ)
          from (congrFun hcoeF (-ξ)).symm]
    rw [hΦpt, fourier_hermitian_real G hH]
  refine ⟨Φ.postcompCLM (RCLike.reCLM (K := ℂ)), ?_⟩
  have hschwartzCφ : schwartzC (Φ.postcompCLM (RCLike.reCLM (K := ℂ))) = Φ := by
    apply SchwartzMap.ext
    intro ξ
    rw [schwartzC_apply, SchwartzMap.postcompCLM_apply, RCLike.reCLM_apply]
    have := hΦreal ξ
    rw [Complex.conj_eq_iff_re] at this
    rw [RCLike.re_to_complex]
    exact this
  rw [hschwartzCφ, hΦdef, fourier_fourierInv_eq]

/-! ### Step 3 — fiberwise transverse spanning by curl symbols -/

/-- **Step 3 (fiberwise spanning).**  For `ξ ≠ 0`, every transverse target vector `b : ℂ³`
(i.e. `∑ j, ξ_j b_j = 0`) is realised as a curl symbol: there exists `a : ℂ³` with
`crossWithIξ ξ a = b`.  Equivalently, `{ (2π i) ξ × a : a } = ξ^⊥`.

This is pure (finite-dimensional) cross-product linear algebra: in ℝ³/ℂ³ the image of
`a ↦ ξ × a` is exactly the plane orthogonal to `ξ`, with explicit preimage
`a = (ξ × b) / (2π i ‖ξ‖²)` for transverse `b`.

Blocker: while finite-dimensional, the explicit cross-product/orthogonality computation in
`crossWithIξ`'s cyclic-index form is bookkeeping that lean-prover should carry; left as a
clean isolated lemma. -/
theorem cross_iξ_spans_transverse
    (ξ : Domain3) (hξ : ξ ≠ 0) (b : Fin 3 → ℂ)
    (hb : ∑ j : Fin 3, (ξ j : ℂ) * b j = 0) :
    ∃ a : Fin 3 → ℂ, crossWithIξ ξ a = b := by
  -- `N = ‖ξ‖²` (the real squared norm), positive since `ξ ≠ 0`.
  set N : ℝ := (ξ 0) ^ 2 + (ξ 1) ^ 2 + (ξ 2) ^ 2 with hN
  have hNpos : 0 < N := by
    have hex : ξ 0 ≠ 0 ∨ ξ 1 ≠ 0 ∨ ξ 2 ≠ 0 := by
      by_contra h
      push Not at h
      obtain ⟨h0, h1, h2⟩ := h
      exact hξ (by ext i; fin_cases i <;> simp [h0, h1, h2])
    have h0 : (0 : ℝ) ≤ (ξ 0) ^ 2 := sq_nonneg _
    have h1 : (0 : ℝ) ≤ (ξ 1) ^ 2 := sq_nonneg _
    have h2 : (0 : ℝ) ≤ (ξ 2) ^ 2 := sq_nonneg _
    rw [hN]
    rcases hex with h | h | h <;> nlinarith [sq_pos_of_ne_zero h]
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hNpos.ne'
  have hpiC : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hfac : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [hpiC, Complex.I_ne_zero]
  have hden : (2 * (Real.pi : ℂ) * Complex.I) * (N : ℂ) ≠ 0 := mul_ne_zero hfac hNC
  -- the cross product `c = ξ × b`, then the explicit preimage `a = -c / (2π i N)`.
  refine ⟨fun k =>
      -(((ξ (k + 1) : ℂ)) * b (k + 2) - ((ξ (k + 2) : ℂ)) * b (k + 1)) /
        ((2 * (Real.pi : ℂ) * Complex.I) * (N : ℂ)), ?_⟩
  -- transversality `∑ ξⱼ bⱼ = 0` written out on the three indices.
  have hb3 : (ξ 0 : ℂ) * b 0 + (ξ 1 : ℂ) * b 1 + (ξ 2 : ℂ) * b 2 = 0 := by
    have := hb
    rw [Fin.sum_univ_three] at this
    exact this
  -- `N` as a complex polynomial in the components.
  have hNcast : (N : ℂ) = (ξ 0 : ℂ) ^ 2 + (ξ 1 : ℂ) ^ 2 + (ξ 2 : ℂ) ^ 2 := by
    rw [hN]; push_cast; ring
  funext i
  -- target component value `(2π i)(ξ_{i+1} a_{i+2} − ξ_{i+2} a_{i+1}) = b i`
  simp only [crossWithIξ]
  fin_cases i <;> simp only [Fin.isValue, Fin.reduceFinMk, Fin.reduceAdd]
  · -- i = 0 : `ξ₂ c₁ − ξ₁ c₂ = N b₀`; substitute `N` then `linear_combination -ξ₀ · hb3`.
    rw [hNcast] at hNC ⊢
    field_simp
    linear_combination (-(ξ 0 : ℂ)) * hb3
  · rw [hNcast] at hNC ⊢
    field_simp
    linear_combination (-(ξ 1 : ℂ)) * hb3
  · rw [hNcast] at hNC ⊢
    field_simp
    linear_combination (-(ξ 2 : ℂ)) * hb3

/-- **Pointwise transverse ⊥ longitudinal cancellation.**  At a fixed `ξ ≠ 0`, if `û` is
transverse (`∑_j ξ_j û_j = 0`) and `ŵ` is longitudinal (`ŵ × ξ = 0`, written componentwise
`ŵ_{k+1} ξ_{k+2} − ŵ_{k+2} ξ_{k+1} = 0`), then the Hermitian pairing `∑_j conj(û_j) ŵ_j = 0`.

Pure ℂ³ linear algebra: `ŵ × ξ = 0 ⟹ ŵ ∥ ξ`, so `ξ_i · ∑_j conj(û_j) ŵ_j = ŵ_i · ∑_j conj(û_j) ξ_j`
and the right factor is `conj(∑_j ξ_j û_j) = 0`; pick `i` with `ξ_i ≠ 0`. -/
private theorem transverse_longitudinal_cancel
    (ξ : Domain3) (hξ : ξ ≠ 0) (û ŵ : Fin 3 → ℂ)
    (htrans : ∑ j : Fin 3, (ξ j : ℂ) * û j = 0)
    (hlong : ∀ k : Fin 3,
        ŵ (k + 1) * (ξ (k + 2) : ℂ) - ŵ (k + 2) * (ξ (k + 1) : ℂ) = 0) :
    ∑ j : Fin 3, (starRingEnd ℂ) (û j) * ŵ j = 0 := by
  -- transverse, conjugated: `∑_j conj(û_j) ξ_j = 0`.
  have hT : (starRingEnd ℂ) (û 0) * (ξ 0 : ℂ) + (starRingEnd ℂ) (û 1) * (ξ 1 : ℂ)
      + (starRingEnd ℂ) (û 2) * (ξ 2 : ℂ) = 0 := by
    have h := congrArg (starRingEnd ℂ) htrans
    rw [Fin.sum_univ_three, map_add, map_add, map_mul, map_mul, map_mul, map_zero,
      Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_ofReal] at h
    linear_combination h
  -- the three cross relations.
  have h0 := hlong 0
  have h1 := hlong 1
  have h2 := hlong 2
  simp only [Fin.isValue, Fin.reduceAdd] at h0 h1 h2
  -- some component of `ξ` is nonzero.
  have hex : (ξ 0 : ℂ) ≠ 0 ∨ (ξ 1 : ℂ) ≠ 0 ∨ (ξ 2 : ℂ) ≠ 0 := by
    by_contra h
    push Not at h
    obtain ⟨e0, e1, e2⟩ := h
    refine hξ ?_
    have r0 : ξ 0 = 0 := by exact_mod_cast e0
    have r1 : ξ 1 = 0 := by exact_mod_cast e1
    have r2 : ξ 2 = 0 := by exact_mod_cast e2
    ext i; fin_cases i <;> simp [r0, r1, r2]
  rw [Fin.sum_univ_three]
  rcases hex with hi | hi | hi
  · have key : (ξ 0 : ℂ) * ((starRingEnd ℂ) (û 0) * ŵ 0 + (starRingEnd ℂ) (û 1) * ŵ 1
        + (starRingEnd ℂ) (û 2) * ŵ 2) = 0 := by
      linear_combination ŵ 0 * hT - (starRingEnd ℂ) (û 1) * h2 + (starRingEnd ℂ) (û 2) * h1
    exact (mul_eq_zero.1 key).resolve_left hi
  · have key : (ξ 1 : ℂ) * ((starRingEnd ℂ) (û 0) * ŵ 0 + (starRingEnd ℂ) (û 1) * ŵ 1
        + (starRingEnd ℂ) (û 2) * ŵ 2) = 0 := by
      linear_combination ŵ 1 * hT + (starRingEnd ℂ) (û 0) * h2 - (starRingEnd ℂ) (û 2) * h0
    exact (mul_eq_zero.1 key).resolve_left hi
  · have key : (ξ 2 : ℂ) * ((starRingEnd ℂ) (û 0) * ŵ 0 + (starRingEnd ℂ) (û 1) * ŵ 1
        + (starRingEnd ℂ) (û 2) * ŵ 2) = 0 := by
      linear_combination ŵ 2 * hT - (starRingEnd ℂ) (û 0) * h1 + (starRingEnd ℂ) (û 1) * h0
    exact (mul_eq_zero.1 key).resolve_left hi

/-- **Conjugated curl-symbol pairing as a longitudinal pairing.**  The Hermitian pairing of the
conjugated curl symbol `conj(crossWithIξ ξ a)` with a vector `ŵ` re-groups (triple-product
symmetry, `ξ` real so `conj(2πi ξ) = −2πi ξ`) into `−2πi` times the pairing of `conj a` with the
cross field `ŵ × ξ`. -/
private theorem conj_cross_sum_eq (ξ : Domain3) (a ŵ : Fin 3 → ℂ) :
    ∑ j : Fin 3, (starRingEnd ℂ) (crossWithIξ ξ a j) * ŵ j
      = -(2 * Real.pi * Complex.I) * ∑ m : Fin 3,
          (starRingEnd ℂ) (a m)
            * (ŵ (m + 1) * (ξ (m + 2) : ℂ) - ŵ (m + 2) * (ξ (m + 1) : ℂ)) := by
  have hc : (starRingEnd ℂ) (2 * (Real.pi : ℂ) * Complex.I) = -(2 * Real.pi * Complex.I) := by
    rw [map_mul, map_mul, Complex.conj_I, Complex.conj_ofReal,
      show ((2 : ℂ)) = ((2 : ℝ) : ℂ) by norm_num, Complex.conj_ofReal]; ring
  simp only [crossWithIξ, map_mul, map_sub, Complex.conj_ofReal, hc]
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  simp only [Fin.isValue, Fin.reduceAdd]
  ring

set_option maxHeartbeats 1600000 in
/-- **Longitudinality of `ŵ` from orthogonality to all curls.**  If `w` is orthogonal to every
curl `curlSchwartzL2 ψ`, then its complex Fourier transform `ŵ` is longitudinal a.e.: the cross
field `ŵ × ξ` vanishes, here the `k`-th component
`ŵ_{k+1}(ξ) ξ_{k+2} − ŵ_{k+2}(ξ) ξ_{k+1} = 0` for a.e. `ξ`.

Proof: pairing `⟪curlSchwartzL2 ψ, w⟫ = 0` (Parseval bridge + curl symbol `fourier_curlSchwartz_eq_cross`
+ `conj_cross_sum_eq` triple-product re-grouping) gives, for a single-component potential
`ψ`, `∫ conj(𝓕(schwartzC φ)) · (ŵ × ξ)_k = 0` for every real `φ`.  By the
Hermitian-test du-Bois-Reymond lemma `ae_zero_of_hermitianTest` (whose Hermitian tests are realised
through `schwartz_hermitian_has_fourier_preimage`), `(ŵ × ξ)_k = 0` a.e. -/
private theorem orthogonalCurl_longitudinal_ae
    (w : L2VF_R3) (hw : w ∈ (Submodule.span ℝ (Set.range curlSchwartzL2))ᗮ) (k : Fin 3) :
    ∀ᵐ ξ ∂(volume : Measure Domain3),
      (𝓕 (L2VF_projComponentC_R3 (k + 1) w) : L2C_R3) ξ * (ξ (k + 2) : ℂ)
        - (𝓕 (L2VF_projComponentC_R3 (k + 2) w) : L2C_R3) ξ * (ξ (k + 1) : ℂ) = 0 := by
  set Wf : Domain3 → ℂ :=
    fun ξ => (𝓕 (L2VF_projComponentC_R3 (k + 1) w) : L2C_R3) ξ * (ξ (k + 2) : ℂ)
      - (𝓕 (L2VF_projComponentC_R3 (k + 2) w) : L2C_R3) ξ * (ξ (k + 1) : ℂ) with hWf
  -- continuity of the coordinate weights
  have hcont : ∀ i : Fin 3, ∀ K : Set Domain3,
      ContinuousOn (fun ξ : Domain3 => (ξ i : ℂ)) K := by
    intro i K
    exact (Complex.continuous_ofReal.comp (EuclideanSpace.proj (𝕜 := ℝ) i).continuous).continuousOn
  -- each component `ŵ j` is integrable on compacts
  have hmemK : ∀ (j : Fin 3) (K : Set Domain3), IsCompact K →
      IntegrableOn ((𝓕 (L2VF_projComponentC_R3 j w) : L2C_R3) : Domain3 → ℂ) K volume := by
    intro j K hK
    have hm : MemLp ((𝓕 (L2VF_projComponentC_R3 j w) : L2C_R3) : Domain3 → ℂ) 2
        (volume.restrict K) := (Lp.memLp (𝓕 (L2VF_projComponentC_R3 j w))).restrict K
    haveI : IsFiniteMeasure ((volume : Measure Domain3).restrict K) :=
      ⟨by simpa using hK.measure_lt_top (μ := (volume : Measure Domain3))⟩
    exact hm.integrable (by norm_num)
  -- `Wf` is locally integrable
  have hLI : LocallyIntegrable Wf (volume : Measure Domain3) := by
    rw [locallyIntegrable_iff]
    intro K hK
    refine IntegrableOn.sub ?_ ?_
    · exact (hmemK (k + 1) K hK).mul_continuousOn (hcont (k + 2) K) hK
    · exact (hmemK (k + 2) K hK).mul_continuousOn (hcont (k + 1) K) hK
  -- per-potential orthogonality: `∫ conj(𝓕(schwartzC φ)) Wf = 0`.
  have hcurlOrth : ∀ φ : SchwartzMap Domain3 ℝ,
      ∫ ξ : Domain3, (starRingEnd ℂ) ((𝓕 (schwartzC φ) : SchwartzMap Domain3 ℂ) ξ) * Wf ξ
        ∂(volume : Measure Domain3) = 0 := by
    intro φ
    set ψ : Fin 3 → SchwartzMap Domain3 ℝ := fun m => if m = k then φ else 0 with hψ
    have hmem : curlSchwartzL2 ψ ∈ Submodule.span ℝ (Set.range curlSchwartzL2) :=
      Submodule.subset_span (Set.mem_range_self ψ)
    have h0 : (inner ℝ (curlSchwartzL2 ψ) w : ℝ) = 0 :=
      (Submodule.mem_orthogonal _ w).1 hw (curlSchwartzL2 ψ) hmem
    have hbr := inner_L2VF_eq_integral_sum_fourier (curlSchwartzL2 ψ) w
    rw [h0, Complex.ofReal_zero] at hbr
    -- `𝓕(schwartzC 0) = 0`.
    have hsc0 : (𝓕 (schwartzC (0 : SchwartzMap Domain3 ℝ)) : SchwartzMap Domain3 ℂ) = 0 := by
      have : schwartzC (0 : SchwartzMap Domain3 ℝ) = 0 := by
        apply SchwartzMap.ext; intro ξ; rw [schwartzC_apply]; simp
      rw [this, ← SchwartzMap.fourierTransformCLM_apply (𝕜 := ℂ)]; exact map_zero _
    -- the per-potential a.e. identity `𝓕(potentialComponentC ψ m) =ᵐ 𝓕(schwartzC (ψ m))`.
    have hpot : ∀ m : Fin 3, ((𝓕 (potentialComponentC ψ m) : L2C_R3) : Domain3 → ℂ)
        =ᵐ[volume] fun ξ => (𝓕 (schwartzC (ψ m)) : SchwartzMap Domain3 ℂ) ξ := by
      intro m
      have hF : (𝓕 (potentialComponentC ψ m) : L2C_R3)
          = (𝓕 (schwartzC (ψ m))).toLp 2 (volume : Measure Domain3) := by
        rw [potentialComponentC_eq]; exact SchwartzMap.toLp_fourier_eq (schwartzC (ψ m))
      rw [hF]; exact (𝓕 (schwartzC (ψ m))).coeFn_toLp 2 (volume : Measure Domain3)
    -- the a.e. integrand identity: bridge integrand `= -(2πi)·(conj(𝓕(schwartzC φ))·Wf)`.
    have hae : (fun ξ => ∑ j : Fin 3,
          (starRingEnd ℂ) ((𝓕 (L2VF_projComponentC_R3 j (curlSchwartzL2 ψ)) : L2C_R3) ξ)
            * (𝓕 (L2VF_projComponentC_R3 j w) : L2C_R3) ξ)
        =ᵐ[volume] fun ξ => -(2 * Real.pi * Complex.I)
          * ((starRingEnd ℂ) ((𝓕 (schwartzC φ) : SchwartzMap Domain3 ℂ) ξ) * Wf ξ) := by
      have hcAll := MeasureTheory.ae_all_iff.2 (fun j : Fin 3 => fourier_curlSchwartz_eq_cross ψ j)
      have hpAll := MeasureTheory.ae_all_iff.2 hpot
      filter_upwards [hcAll, hpAll] with ξ hcξ hpξ
      -- rewrite the curl components, then re-group via `conj_cross_sum_eq`.
      have hstep1 : ∑ j : Fin 3,
            (starRingEnd ℂ) ((𝓕 (L2VF_projComponentC_R3 j (curlSchwartzL2 ψ)) : L2C_R3) ξ)
              * (𝓕 (L2VF_projComponentC_R3 j w) : L2C_R3) ξ
          = ∑ j : Fin 3,
            (starRingEnd ℂ) (crossWithIξ ξ
                (fun m => (𝓕 (potentialComponentC ψ m) : L2C_R3) ξ) j)
              * (𝓕 (L2VF_projComponentC_R3 j w) : L2C_R3) ξ :=
        Finset.sum_congr rfl (fun j _ => by rw [hcξ j])
      rw [hstep1, conj_cross_sum_eq ξ (fun m => (𝓕 (potentialComponentC ψ m) : L2C_R3) ξ)
        (fun j => (𝓕 (L2VF_projComponentC_R3 j w) : L2C_R3) ξ)]
      have hψk : ψ k = φ := by rw [hψ]; simp
      congr 1
      -- collapse the single-component sum at `m = k`.
      rw [Finset.sum_eq_single k]
      · -- main term: `m = k`, `ψ k = φ`, `Wfun_k = Wf ξ`.
        rw [hpξ k, hψk, hWf]
      · -- other terms vanish: `ψ m = 0` for `m ≠ k`.
        intro m _ hmk
        have hψm : ψ m = 0 := by rw [hψ]; simp [hmk]
        rw [hpξ m, hψm, hsc0]
        simp
      · intro h; exact absurd (Finset.mem_univ k) h
    -- assemble: `0 = -(2πi)·∫ conj(𝓕(schwartzC φ))·Wf`, hence the integral vanishes.
    rw [integral_congr_ae hae, integral_const_mul] at hbr
    have hfac : -(2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    exact (mul_eq_zero.1 hbr.symm).resolve_left hfac
  -- du-Bois-Reymond against Hermitian tests.
  refine ae_zero_of_hermitianTest Wf hLI ?_
  intro G hG
  -- realize `conj ∘ G` (Hermitian) as `𝓕 (schwartzC φ)`.
  have hG'H : ∀ ξ : Domain3, (G.postcompCLM (Complex.conjCLE : ℂ →L[ℝ] ℂ)) (-ξ)
      = (starRingEnd ℂ) ((G.postcompCLM (Complex.conjCLE : ℂ →L[ℝ] ℂ)) ξ) := by
    intro ξ
    simp only [SchwartzMap.postcompCLM_apply]
    show (starRingEnd ℂ) (G (-ξ)) = (starRingEnd ℂ) ((starRingEnd ℂ) (G ξ))
    rw [hG ξ]
  obtain ⟨φ, hφ⟩ := schwartz_hermitian_has_fourier_preimage
    (G.postcompCLM (Complex.conjCLE : ℂ →L[ℝ] ℂ)) hG'H
  have hco := hcurlOrth φ
  -- `conj (𝓕(schwartzC φ) ξ) = conj (conj (G ξ)) = G ξ`.
  have hGeq : ∀ ξ : Domain3,
      (starRingEnd ℂ) ((𝓕 (schwartzC φ) : SchwartzMap Domain3 ℂ) ξ) = (G : Domain3 → ℂ) ξ := by
    intro ξ
    rw [show (𝓕 (schwartzC φ) : SchwartzMap Domain3 ℂ) ξ
          = (G.postcompCLM (Complex.conjCLE : ℂ →L[ℝ] ℂ)) ξ from congrFun
            (congrArg (fun (f : SchwartzMap Domain3 ℂ) => (f : Domain3 → ℂ)) hφ) ξ]
    simp only [SchwartzMap.postcompCLM_apply]
    show (starRingEnd ℂ) ((starRingEnd ℂ) (G ξ)) = (G : Domain3 → ℂ) ξ
    rw [Complex.conj_conj]
  rw [show (fun ξ : Domain3 => (G : Domain3 → ℂ) ξ * Wf ξ)
        = fun ξ => (starRingEnd ℂ) ((𝓕 (schwartzC φ) : SchwartzMap Domain3 ℂ) ξ) * Wf ξ from by
      funext ξ; rw [hGeq ξ]]
  exact hco

/-! ### Step 4 — density transfer (the Helmholtz/Weyl analytic core) -/

/-- **Isolated analytic core of Step 4 (longitudinal ⊥ transverse).**  If `u` is weakly
divergence-free (`u ∈ L2Sigma_R3`, so `û` is transverse a.e. by the forward direction of
`mem_sigma_iff_fourier_transverse`) and `w` is orthogonal to every curl
(`w ∈ (span (range curlSchwartzL2))ᗮ`, which forces `ŵ` to be longitudinal a.e. — orthogonal
to the plane `ξ^⊥` swept out by the curl symbols, `cross_iξ_spans_transverse`), then `u ⊥ w`.

Pointwise on the Fourier side `⟪û(ξ), ŵ(ξ)⟫ = 0` (transverse ⊥ longitudinal,
`transverse_longitudinal_cancel`), and the vector Parseval bridge
`inner_L2VF_eq_integral_sum_fourier` lifts this to `⟪u, w⟫ = 0`.  Transversality of `û` is the
forward direction of `mem_sigma_iff_fourier_transverse`; longitudinality of `ŵ` is
`orthogonalCurl_longitudinal_ae`.  PROVED, `sorry`-free. -/
private theorem l2sigma_inner_orthogonalCurl_eq_zero
    (u : L2VF_R3) (hu : u ∈ L2Sigma_R3)
    (w : L2VF_R3) (hw : w ∈ (Submodule.span ℝ (Set.range curlSchwartzL2))ᗮ) :
    (inner ℝ u w : ℝ) = 0 := by
  -- `û` transverse a.e. (forward Step 2).
  have htransAe : ∀ᵐ ξ ∂(volume : Measure Domain3), transverseDefect u ξ = 0 :=
    (transverse_ae_iff u).1 ((mem_sigma_iff_fourier_transverse u).1 hu)
  -- `ŵ` longitudinal a.e. (all three cross components).
  have hl0 := orthogonalCurl_longitudinal_ae w hw 0
  have hl1 := orthogonalCurl_longitudinal_ae w hw 1
  have hl2 := orthogonalCurl_longitudinal_ae w hw 2
  -- `ξ ≠ 0` a.e. (`volume` has no atoms).
  have hne : ∀ᵐ ξ ∂(volume : Measure Domain3), ξ ≠ 0 := by
    rw [ae_iff]
    simp only [not_not, Set.setOf_eq_eq_singleton]
    exact measure_singleton 0
  -- the Parseval bridge integrand vanishes a.e. (transverse ⊥ longitudinal).
  have hint0 : ∫ ξ : Domain3, ∑ j : Fin 3,
      (starRingEnd ℂ) ((𝓕 (L2VF_projComponentC_R3 j u) : L2C_R3) ξ)
        * (𝓕 (L2VF_projComponentC_R3 j w) : L2C_R3) ξ ∂(volume : Measure Domain3) = 0 := by
    rw [show (0 : ℂ) = ∫ _ξ : Domain3, (0 : ℂ) ∂(volume : Measure Domain3) by simp]
    refine integral_congr_ae ?_
    filter_upwards [htransAe, hl0, hl1, hl2, hne] with ξ ht h0 h1 h2 hξ
    refine transverse_longitudinal_cancel ξ hξ
      (fun j => (𝓕 (L2VF_projComponentC_R3 j u) : L2C_R3) ξ)
      (fun j => (𝓕 (L2VF_projComponentC_R3 j w) : L2C_R3) ξ) ?_ ?_
    · simpa only [transverseDefect] using ht
    · intro k
      fin_cases k
      · exact h0
      · exact h1
      · exact h2
  -- conclude through the Parseval bridge.
  have hcast : ((inner ℝ u w : ℝ) : ℂ) = 0 := by
    rw [inner_L2VF_eq_integral_sum_fourier u w, hint0]
  exact_mod_cast hcast

/-- **Step 4 (density transfer).**  The full deliverable, stated as the closure containment.
Given a transverse field `u ∈ L2Sigma_R3` (Step 2), the fiberwise spanning (Steps 1+3) lets us
approximate `û` in L² by curl symbols `𝓕(curl ψ)`; transferring back through Plancherel places
`u` in the L²-closure of the span of curls.

Route (refined; no "measurable selection" needed).  The clean proof is the orthogonal-complement
density criterion, all pieces of which ARE in pinned mathlib:
`Submodule.orthogonal_orthogonal_eq_closure` reduces the goal to: every `v` orthogonal to all
`curlSchwartzL2 ψ` and lying in `L2Sigma_R3` is `0`.  By Parseval (`Lp.inner_fourier_eq`) plus the
curl symbol `iξ×ψ̂` (Step 1) and the fiberwise spanning (Step 3), `v ⊥ curls` forces `v̂` a.e.
*longitudinal* (parallel to `ξ`); `v ∈ L2Sigma_R3` forces `v̂` a.e. *transverse* (Step 2 forward);
the two meet only at `v̂ = 0`, whence `v = 0` by the L² Fourier isometry `Lp.fourierTransformₗᵢ`.

Status: PROVED, `sorry`-free.  The orthogonal-complement reduction below uses
`Submodule.orthogonal_orthogonal_eq_closure` and `Submodule.mem_orthogonal'` to reduce the goal to
the analytic core `l2sigma_inner_orthogonalCurl_eq_zero` (every `w ⊥ all curls` is orthogonal to
every `u ∈ L2Sigma_R3`), which is itself proved. -/
theorem l2sigma_le_closure_span_curl :
    (L2Sigma_R3 : Submodule ℝ L2VF_R3) ≤
      (Submodule.span ℝ (Set.range curlSchwartzL2)).topologicalClosure := by
  -- Orthogonal-complement criterion: `K.topologicalClosure = Kᗮᗮ`, so it suffices to show
  -- every `u ∈ L2Sigma_R3` lies in `Kᗮᗮ`, i.e. `u ⊥ w` for every `w ⊥ all curls`.
  set K : Submodule ℝ L2VF_R3 := Submodule.span ℝ (Set.range curlSchwartzL2) with hK
  rw [← K.orthogonal_orthogonal_eq_closure]
  intro u hu
  rw [Kᗮ.mem_orthogonal']
  -- the genuine analytic core, isolated as a precisely-stated sub-lemma below.
  intro w hw
  rw [hK] at hw
  exact l2sigma_inner_orthogonalCurl_eq_zero u hu w hw

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

/-! ### Deliverable -/

/-- **Deliverable.**  The density frontier holds: the L²-closure of the span of curls of
Schwartz vector potentials contains the whole weakly-divergence-free subspace `L2Sigma_R3`.

This is a complete, `sorry`-free, axiom-free PROOF of `CurlSchwartzDense` (no extra hypotheses).
The axiom `curlSchwartzDense_holds` is RETIRED: `CurlDensityCapstone.lean` (Route A, issue #3)
re-anchors all consumers to this theorem; `#print axioms exists_lerayHopf_r3` no
longer lists `curlSchwartzDense_holds` (R3 project axioms: 5 → 4). -/
theorem curlSchwartzDense_provedRoute : CurlSchwartzDense :=
  l2sigma_le_closure_span_curl

end LerayHopf
