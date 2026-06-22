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
(`fourier_ofReal_reflect_eq_conj`) — once feared to be addable only in `FourierL2` — is now
also PROVED here, axiom-free.

**Correction to an earlier (stale) assessment.**  The pinned mathlib DOES provide the
heavy L²-Fourier toolkit this density argument needs: `MeasureTheory.Lp.fourierTransformₗᵢ`
(the L² Fourier transform as a `LinearIsometryEquiv`, with `Lp.inner_fourier_eq` Parseval and
`Lp.norm_fourier_eq` Plancherel), the orthogonal-complement density criterion
(`Submodule.orthogonal_orthogonal_eq_closure` / `topologicalClosure_eq_top_iff`), the
du-Bois-Reymond lemma (`ae_eq_zero_of_integral_contDiff_smul_eq_zero`), and
`Lp.compMeasurePreserving` + `Measure.measurePreserving_neg`.  What mathlib still lacks is
narrowly the *Helmholtz/Leray-specific* content (no `curl`/`divergence` operator, no Helmholtz
decomposition, no `closure(span curl) = L²_σ`), which this file builds.  The two remaining
`sorry`s reduce to a SINGLE named missing sub-development:

* `(P2)` — Schwartz surjectivity of `φ ↦ testSymbol φ` onto anti-Hermitian symbols,
  equivalently: `𝓕⁻` of a Hermitian Schwartz function is the complexification of a *real*
  Schwartz function (Schwartz-space real-part extraction under Hermitian symmetry).  NOT in
  mathlib, but constructible (weeks-class) from `SchwartzMap.postcompCLM Complex.conjCLE`
  (Schwartz conjugation) + a real-valuedness argument + `Complex.reCLM` extraction.

The forward spectral characterization (`mem_sigma_iff_fourier_transverse`, forward) bottoms out
on `(P2)`; the density transfer (`l2sigma_le_closure_span_curl`) then follows from the
orthogonal-complement route above once that characterization is available.  Each obligation that
genuinely depends on `(P2)` is left as a `sorry` carrying an `ALLOW_SORRY` marker.  The TOP-LEVEL
type stays exactly `CurlSchwartzDense` — a real discharge target, never weakened.

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
private noncomputable def schwartzC (f : SchwartzMap Domain3 ℝ) : SchwartzMap Domain3 ℂ :=
  f.postcompCLM (RCLike.ofRealCLM (K := ℂ))

private theorem schwartzC_apply (f : SchwartzMap Domain3 ℝ) (x : Domain3) :
    schwartzC f x = (f x : ℂ) := rfl

/-- The complex L²-class of a complexified real Schwartz map is the `compLpL`-embedding of the
real class — i.e. exactly `potentialComponentC`-shaped. -/
private theorem toLp_schwartzC_eq (f : SchwartzMap Domain3 ℝ) :
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

/-! ### (P2) Schwartz Hermitian preimage — sole remaining sorry blocker

This lemma is the single analytic gap that blocks the two remaining `sorry`s in this file
(`mem_sigma_iff_fourier_transverse` forward direction and `l2sigma_le_closure_span_curl`).

**Removal plan for `axiom curlSchwartzDense_holds` (import-DAG note).**
`CurlDensity.lean` already imports `SchwartzDivFreeBasis.lean`, so once
`curlSchwartzDense_provedRoute` is sorry-free it CANNOT be used in-place to retire the axiom
— that would require `SchwartzDivFreeBasis` to import `CurlDensity`, creating a cycle.
The clean one-step route (owner-approved scope, issue #3):

  1. Prove P2 here → sorries in `mem_sigma_iff_fourier_transverse` and
     `l2sigma_le_closure_span_curl` discharge → `curlSchwartzDense_provedRoute` becomes sorry-free.
  2. In `SchwartzDivFreeBasis.lean`, replace
       `axiom curlSchwartzDense_holds : CurlSchwartzDense`
     with
       `theorem curlSchwartzDense_holds : CurlSchwartzDense := curlSchwartzDense_provedRoute`
     (The name is preserved so every downstream consumer — `nonempty_schwartzGalerkinBasis`,
      `r3GalerkinScheme_exists` — is unchanged.)
     This requires adding `import LerayHopf.R3.CurlDensity` to `SchwartzDivFreeBasis.lean`.
     DAG check: `CurlDensity` imports `SchwartzDivFreeBasis`, so the reverse import would be
     cyclic — FORBIDDEN.  Therefore step 2 must move the replacement into a NEW downstream
     file (`CurlDensityCapstone.lean`) that imports BOTH, or relocate
     `nonempty_schwartzGalerkinBasis` + `r3GalerkinScheme_exists` to such a file.

  **Recommended route (lean-coder follow-up after P2 is proved):**
  Create `LerayHopf/R3/CurlDensityCapstone.lean` that imports both `CurlDensity` and
  `SchwartzDivFreeBasis`, re-exports `nonempty_schwartzGalerkinBasis` and
  `r3GalerkinScheme_exists` routing through `curlSchwartzDense_provedRoute`, and removes the
  axiom body from `SchwartzDivFreeBasis.lean` (keeping only the `Prop` definition
  `CurlSchwartzDense` and the constructive content A1–C1).  The axiom line is then deleted.
  `#print axioms nonempty_schwartzGalerkinBasis` should show no `curlSchwartzDense_holds`.
-/

/-- **(P2) Schwartz Hermitian preimage extraction (must-prove — item 11 in the plan).**

If `h : 𝓢(ℝ³, ℂ)` is anti-Hermitian in the sense `h(-ξ) = -conj(h(ξ))` (i.e. `h` is an
anti-Hermitian Schwartz symbol, exactly the kind produced by `testSymbol φ` for real `φ`),
then there exists `φ : 𝓢(ℝ³, ℝ)` such that `testSymbol φ = h`.

**Constructibility sketch** (no Mathlib PR needed — all primitives present):
- Let `g = (2πi)⁻¹ • h` (Hermitian: `g(-ξ) = conj(g(ξ))`).
- Let `Ψ : 𝓢(ℝ³, ℂ)` be the Schwartz inverse Fourier transform `𝓕⁻ g`
  (`FourierTransform.fourierCLE.symm` applied to `g`).
- Since `g` is Hermitian, `Ψ` is real-valued: use `fourier_ofReal_reflect_eq_conj` (proved,
  P1 above) to establish `Ψ(-ξ) =ᵐ conj(Ψ(ξ))`, i.e. `Im Ψ = 0`.
- Extract the real Schwartz function `φ := (Re ∘ Ψ)` via
  `Ψ.postcompCLM (RCLike.reCLM : ℂ →L[ℝ] ℝ)` (`SchwartzMap.postcompCLM`).
- Verify `testSymbol φ = h`:
  `testSymbol φ ξ = conj((2πi) · 𝓕(schwartzC φ)(ξ))`.
  Since `Ψ` is real-valued, `schwartzC φ = schwartzC (Re Ψ) = Ψ`.
  Then `𝓕(Ψ) = 𝓕(𝓕⁻ g) = g` by `FourierInvPair`, and `conj((2πi)·g) = h` by definition.

Key Mathlib decls: `SchwartzMap.postcompCLM`, `Complex.conjCLE`, `RCLike.reCLM`,
`FourierTransform.fourierCLE` (symm), `FourierInvPair`, `fourier_ofReal_reflect_eq_conj` (item 9). -/
private theorem schwartz_antiHermitian_has_testSymbol_preimage
    (h : SchwartzMap Domain3 ℂ)
    (hH : ∀ ξ : Domain3, h (-ξ) = -(starRingEnd ℂ) (h ξ)) :
    ∃ φ : SchwartzMap Domain3 ℝ, testSymbol φ = h :=
  sorry -- ALLOW_SORRY: #3 (P2) schwartz_antiHermitian_has_testSymbol_preimage — Schwartz Hermitian real-extraction; constructible from postcompCLM conjCLE + reCLM + fourierCLE.symm + FourierInvPair + fourier_ofReal_reflect_eq_conj; NOT in mathlib; weeks-class; lean-prover target (issue #3)

/-! ### Step 2 — spectral characterization of weak divergence-freeness -/

/-- **Fourier of a real function is Hermitian.**  For a real Schwartz `φ`, the Fourier
transform of its complexification satisfies `𝓕(schwartzC φ)(-ξ) = conj (𝓕(schwartzC φ)(ξ))`.

This is the conjugate symmetry of the Fourier transform of a (complexified) real function:
pushing `conj` through the integral defining `𝓕`, the unit-modulus character contributes
`conj(𝐞(-⟪v,ξ⟫)) = 𝐞(⟪v,ξ⟫) = 𝐞(-⟪v,-ξ⟫)`, while `conj` acts trivially on the real-valued
integrand `schwartzC φ`. -/
private theorem fourier_schwartzC_hermitian (φ : SchwartzMap Domain3 ℝ) (ξ : Domain3) :
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
private theorem complexInner_compLpL_ofReal
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
    have _hLI := locallyIntegrable_transverseDefect u
    have _hzero := (mem_sigma_iff_fourier_integral_zero u).1 hmem
    -- The even/odd (Hermitian) reduction.  `T_u` is anti-Hermitian: by the now-PROVED
    -- `(P1)` reflection identity `fourier_ofReal_reflect_eq_conj`, each component satisfies
    -- `û_j(-ξ) =ᵐ conj(û_j(ξ))`, so with `(-ξ)_j = -ξ_j` we get `T_u(-ξ) =ᵐ -conj(T_u(ξ))` —
    -- i.e. `Re T_u` is odd and `Im T_u` is even.  The available test symbols `testSymbol φ`
    -- are exactly the anti-Hermitian Schwartz functions (`testSymbol_antiHermitian`), whose
    -- real parts are odd-real and imaginary parts even-real.  Choosing `φ` with
    -- `testSymbol φ = g_o` (odd) and another with `testSymbol φ = i·g_e` (even) would split
    -- `∫ g·T_u = ∫ g_o Re T_u + i∫ g_e Im T_u` into two vanishing pieces, feeding
    -- `ae_eq_zero_of_integral_contDiff_smul_eq_zero` (which IS in mathlib).
    --
    -- (P1) is DISCHARGED above (`fourier_ofReal_reflect_eq_conj`, axiom-free, no `sorry`).
    -- The single remaining blocker is:
    --   (P2) surjectivity of `φ ↦ testSymbol φ` onto every anti-Hermitian compactly-supported
    --        smooth symbol, which reduces to: `𝓕⁻` of a Hermitian Schwartz function is the
    --        complexification of a real Schwartz function (Schwartz-space real-part extraction
    --        under Hermitian symmetry).  NOT in mathlib; constructible (weeks-class) from
    --        `SchwartzMap.postcompCLM Complex.conjCLE` (Schwartz conjugation) + a real-valuedness
    --        argument + `Complex.reCLM` extraction — but not available today.  This is the lone
    --        surviving analytic frontier of the forward direction; the REVERSE is fully proved.
    sorry -- ALLOW_SORRY: #3 mem_sigma_iff_fourier_transverse forward — gated on P2 (`schwartz_antiHermitian_has_testSymbol_preimage`, stub above); proof uses P2 to supply odd/even Schwartz witnesses for the du-Bois-Reymond argument; lean-prover target (issue #3)
  · -- Reverse (a.e. transverse ⇒ weakly divergence-free): fully proved.
    intro htr
    exact mem_sigma_of_transverse_ae u htr

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

/-! ### Step 4 — density transfer (the Helmholtz/Weyl analytic core) -/

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

Blocker: this route consumes the FORWARD spectral characterization
`mem_sigma_iff_fourier_transverse` (transverse ⇒ membership and back), whose forward direction is
the lone `sorry` blocked on `(P2)` (Schwartz Hermitian real-extraction; see that lemma and the
file header).  So this density fact is NOT independently months-class — it reduces to `(P2)`.
Left as a `sorry` until `(P2)` lands. -/
theorem l2sigma_le_closure_span_curl :
    (L2Sigma_R3 : Submodule ℝ L2VF_R3) ≤
      (Submodule.span ℝ (Set.range curlSchwartzL2)).topologicalClosure := by
  sorry -- ALLOW_SORRY: #3 l2sigma_le_closure_span_curl — orthogonal-complement route (`Submodule.orthogonal_orthogonal_eq_closure` + `Lp.fourierTransformₗᵢ` Parseval + Steps 1–3) reduces to FORWARD `mem_sigma_iff_fourier_transverse`, itself blocked only on P2 (`schwartz_antiHermitian_has_testSymbol_preimage`, stub above). NOT independently months-class. lean-prover target once P2 lands (issue #3)

/-! ### Deliverable -/

/-- **Deliverable (discharge route for the issue-#21 axiom).**  The isolated density frontier
holds: the L²-closure of the span of curls of Schwartz vector potentials contains the whole
weakly-divergence-free subspace `L2Sigma_R3`.

This is the aspirational PROOF of `CurlSchwartzDense` (no extra hypotheses) that would RETIRE
the marked `axiom curlSchwartzDense_holds` (`SchwartzDivFreeBasis.lean`, issue #21): once
`l2sigma_le_closure_span_curl` is sorry-free, replacing the axiom body with this theorem
removes the last R3 spatial axiom.  It carries the same `sorry` as
`l2sigma_le_closure_span_curl` and is a LEAF (imported by nothing on the capstone path), so it
does NOT contaminate `exists_lerayHopf_r3_axiomatic`'s axiom set — that capstone routes through
the marked axiom, not this sorry-backed route.  Named distinctly from the axiom to avoid a
name clash (`SchwartzDivFreeBasis.curlSchwartzDense_holds` is the axiom this file imports). -/
theorem curlSchwartzDense_provedRoute : CurlSchwartzDense :=
  l2sigma_le_closure_span_curl

end LerayHopf
