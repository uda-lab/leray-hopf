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
theorem curlSchwartzDense_holds : CurlSchwartzDense
```

i.e. a PROOF of the isolated density frontier `CurlSchwartzDense`
(`LerayHopf/R3/SchwartzDivFreeBasis.lean`):

```
CurlSchwartzDense :=
  (L2Sigma_R3 : Submodule ℝ L2VF_R3) ≤
    (Submodule.span ℝ (Set.range curlSchwartzL2)).topologicalClosure
```

Once proved, this upgrades `CurlSchwartzDense` from a carried hypothesis to a theorem,
so the capstone can feed `schwartzGalerkinBasis_of_curlDense` an actual proof and remove
the axiom `r3GalerkinScheme_exists`. **That capstone rewiring is OUT OF SCOPE here**; this
file only proves the density and edits nothing outside itself.

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

Steps (1)–(3) are *finite-dimensional / symbolic* facts (cross-product linear algebra +
the Fourier symbol of a derivative) and are the right shape to be discharged against mathlib.
Step (4) — turning the fiberwise (a.e.) spanning into an actual L²-closure containment — is
the genuine Helmholtz/Weyl analytic content: it needs a measurable selection of Schwartz
potentials whose curl symbols approximate an arbitrary transverse `û` in L², which combines
Plancherel, the transverse decomposition, and L² density.  **mathlib has none of: a `curl`
multiplier, the Helmholtz decomposition, or a `closure(span curl) = L²_σ` theorem** (see
`docs/scratch/helmholtz-density.md` §4).  Each obligation that genuinely depends on this
missing pillar is left as a `sorry` carrying an `ALLOW_SORRY` marker naming the precise
blocker.  The TOP-LEVEL type stays exactly `CurlSchwartzDense` — this is a real discharge
target, never weakened, never given extra hypotheses.

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
  sorry -- ALLOW_SORRY: Fourier symbol of curl `𝓕(∂_a ψ) = 2π i ξ_a ψ̂` threaded through
  -- `lineDerivOpCLM`, the Lp-level component Fourier transform, and the cyclic-index
  -- assembly.  LHS curl component identified via `curlSchwartzL2_projComponent`; RHS is the
  -- cross symbol on the POTENTIAL Fourier transforms `potentialComponentC ψ k`.  Standard but
  -- non-mechanical; lean-prover target leaning on FourierL2's Schwartz↔Lp Fourier bridge
  -- (`fourierComponentC_ae_schwartz`).

/-! ### Step 2 — spectral characterization of weak divergence-freeness -/

/-- The transverse (divergence-free) symbol condition at a point `ξ`: the complex Fourier
vector `û(ξ)` is orthogonal to `ξ`, `∑ j, ξ_j û_j(ξ) = 0`.  This is the Fourier form of the
pointwise constraint `ξ · û(ξ) = 0` characterizing `div u = 0`. -/
def IsTransverseAt (û : Fin 3 → ℂ) (ξ : Domain3) : Prop :=
  ∑ j : Fin 3, (ξ j : ℂ) * û j = 0

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
  sorry -- ALLOW_SORRY: spectral characterization `div u = 0 ↔ ξ·û = 0 a.e.`  Needs
  -- Plancherel applied to `divTestFunctional` and the variational lemma on the Fourier
  -- side.  Not in mathlib (no Helmholtz/div symbol calculus); lean-prover target.

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

Blocker: this is the irreducible analytic pillar — promoting the *fiberwise* (a.e.) spanning to
an actual L²-closure containment requires a measurable selection of Schwartz potentials whose
curl symbols converge to `û` in L² (Plancherel + transverse decomposition + Schwartz L²
density `SchwartzMap.denseRange_toLpCLM`).  This is exactly the Helmholtz/Weyl density fact NOT
in mathlib (`docs/scratch/helmholtz-density.md` §4).  lean-prover target leaning on
`FourierL2.normSq_eq_integral_normSq_C` for the Plancherel approximation estimate. -/
theorem l2sigma_le_closure_span_curl :
    (L2Sigma_R3 : Submodule ℝ L2VF_R3) ≤
      (Submodule.span ℝ (Set.range curlSchwartzL2)).topologicalClosure := by
  sorry -- ALLOW_SORRY: Helmholtz/Weyl density core — fiberwise spanning (Steps 1–3) ⇒
  -- L²-closure containment via measurable selection of Schwartz potentials + Plancherel
  -- approximation.  THE missing analytic pillar; not in mathlib.  lean-prover target.

/-! ### Deliverable -/

/-- **Deliverable.**  The isolated density frontier holds: the L²-closure of the span of curls
of Schwartz vector potentials contains the whole weakly-divergence-free subspace `L2Sigma_R3`.

This is a PROOF of `CurlSchwartzDense` (no extra hypotheses), discharging the single classical
input carried by `schwartzGalerkinBasis_of_curlDense`.  It is `l2sigma_le_closure_span_curl`
repackaged at the exact `CurlSchwartzDense` type — `CurlSchwartzDense` unfolds definitionally to
that closure containment. -/
theorem curlSchwartzDense_holds : CurlSchwartzDense :=
  l2sigma_le_closure_span_curl

end LerayHopf
