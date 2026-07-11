import LerayHopf.Torus.FunctionSpaces
import Mathlib.Analysis.RCLike.Basic

open MeasureTheory

/-!
# Divergence-free velocity fields on the 3-torus

**M2 — D-08.**

This file defines the Fourier-coefficient infrastructure for extracting scalar components
from ℝ³-valued velocity fields, and uses it to state the divergence-free predicate
`DivFreeL2` for fields in `L²(𝕋³; ℝ³)`.

## Design choice (Design C)

`mFourierCoeff` in `AddCircleMulti` requires `NormedSpace ℂ E`.  The fiber type
`VelocityValue = EuclideanSpace ℝ (Fin 3)` is a real, not complex, normed space, so
Design V (single vector-valued Fourier coefficient) does not apply without additional
complexification infrastructure.

**Design C** is used instead:

1. For each component `j : Fin 3`, apply the continuous projection
   `EuclideanSpace.proj j : VelocityValue →L[ℝ] ℝ` to `u ∈ L2VF`, obtaining the
   `j`-th component as an element of `Lp ℝ 2 haarTorus3`.
2. Embed the real component into `L2C` via `RCLike.ofRealCLM : ℝ →L[ℝ] ℂ`, lifted to
   `Lp` by `ContinuousLinearMap.compLpL`.
3. Take the scalar Fourier coefficient using the existing `mFourierCoeff3`.

All lifts are purely definitional (no MemLp proof needed): `ContinuousLinearMap.compLpL`
packages the lift of a continuous linear map to `Lp` for free.

## Main definitions

- `L2VF_projComponent j`   : `L2VF →L[ℝ] Lp ℝ 2 haarTorus3` — `j`-th real component
- `L2VF_projComponentC j`  : `L2VF →L[ℝ] L2C` — `j`-th component embedded into ℂ
- `DivFreeL2`              : divergence-free predicate via Fourier characterisation
-/

namespace LerayHopf

/-! ### D-08 infrastructure: component projections -/

/-- Extract the `j`-th real component of a velocity field `u ∈ L²(𝕋³; ℝ³)` as an element of
`Lp ℝ 2 haarTorus3`.  Constructed by lifting the continuous projection
`EuclideanSpace.proj j : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ` to the `Lp` level via
`ContinuousLinearMap.compLpL`. -/
noncomputable def L2VF_projComponent (j : Fin 3) : L2VF →L[ℝ] Lp ℝ 2 haarTorus3 :=
  (EuclideanSpace.proj j (𝕜 := ℝ)).compLpL 2 haarTorus3

/-- Embed the `j`-th real component of a velocity field into the complex scalar `L²` space
`L2C = Lp ℂ 2 haarTorus3`.  Composed from the component projection and the real-to-complex
embedding `RCLike.ofRealCLM : ℝ →L[ℝ] ℂ`, both lifted to `Lp` via `compLpL`. -/
noncomputable def L2VF_projComponentC (j : Fin 3) : L2VF →L[ℝ] L2C :=
  (RCLike.ofRealCLM (K := ℂ)).compLpL 2 haarTorus3 ∘L L2VF_projComponent j

/-- Inject a scalar field `f ∈ Lp ℝ 2 haarTorus3` as the `j`-th component of a velocity field
in `L2VF = Lp (EuclideanSpace ℝ (Fin 3)) 2 haarTorus3`.

Concretely, `L2VF_injectComponent j f` is the a.e.-class of `x ↦ f(x) • eⱼ`,
where `eⱼ = EuclideanSpace.single j (1 : ℝ)` is the `j`-th standard basis vector.

**Construction:**
- `(ContinuousLinearMap.id ℝ ℝ).smulRight (EuclideanSpace.single j (1 : ℝ)) : ℝ →L[ℝ] VelocityValue`
  maps `r ↦ r • eⱼ`.
- `.compLpL 2 haarTorus3` lifts this CLM pointwise to `Lp ℝ 2 haarTorus3 →L[ℝ] L2VF`.

This is the pointwise-adjoint of `L2VF_projComponent j` in the sense that
`⟪L2VF_injectComponent j f, u⟫ = ⟪f, L2VF_projComponent j u⟫` for `f ∈ Lp ℝ 2` and `u ∈ L2VF`
(as a real inner product).

(Moved here from `VelocityGalerkin.lean`, issue #113 PR-1, next to its adjoint
`L2VF_projComponent`; same namespace, same statement.) -/
noncomputable def L2VF_injectComponent (j : Fin 3) : Lp ℝ 2 haarTorus3 →L[ℝ] L2VF :=
  ((ContinuousLinearMap.id ℝ ℝ).smulRight (EuclideanSpace.single j (1 : ℝ))).compLpL 2 haarTorus3

/-! ### Shared componentwise round-trip lemmas (issue #1 finding-6)

Centralised here, next to the operators they describe, to eliminate the near-verbatim
duplication previously carried independently in `H1Sigma.lean`, `VelocityGalerkin.lean`,
and `GalerkinScheme.lean`. -/

/-- Taking the real part undoes the complex embedding of a component. -/
theorem re_compLpL_projComponentC (j : Fin 3) (w : L2VF) :
    (RCLike.reCLM (K := ℂ)).compLpL 2 haarTorus3 (L2VF_projComponentC j w)
      = L2VF_projComponent j w := by
  refine MeasureTheory.Lp.ext ?_
  filter_upwards [ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := haarTorus3)
      (RCLike.reCLM (K := ℂ)) (L2VF_projComponentC j w),
    ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := haarTorus3)
      (RCLike.ofRealCLM (K := ℂ)) (L2VF_projComponent j w)] with x hx1 hx2
  rw [hx1, show L2VF_projComponentC j w
      = (RCLike.ofRealCLM (K := ℂ)).compLpL 2 haarTorus3 (L2VF_projComponent j w) from rfl,
    hx2]
  simp

/-- Pointwise (a.e.) description of a reassembled `j`-th component: injecting the `j`-th
real component back into `L2VF` agrees a.e. with the `j`-th coordinate projection scaled
by the standard basis vector `eⱼ`. -/
private theorem injectComponent_projComponent_ae (j : Fin 3) (w : L2VF) :
    L2VF_injectComponent j (L2VF_projComponent j w)
      =ᵐ[haarTorus3] fun x => w x j • EuclideanSpace.single j (1 : ℝ) := by
  simp only [L2VF_injectComponent, L2VF_projComponent]
  filter_upwards [ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := haarTorus3)
      ((ContinuousLinearMap.id ℝ ℝ).smulRight (EuclideanSpace.single j (1 : ℝ)))
      ((EuclideanSpace.proj j (𝕜 := ℝ)).compLpL 2 haarTorus3 w),
    ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := haarTorus3)
      (EuclideanSpace.proj j (𝕜 := ℝ)) w] with x hx1 hx2
  rw [hx1, hx2]
  simp

/-- The componentwise reassembly recovers a vector field: summing the injected
per-component projections over `j : Fin 3` reconstructs the original field. -/
theorem sum_inject_projComponent (w : L2VF) :
    ∑ j : Fin 3, L2VF_injectComponent j (L2VF_projComponent j w) = w := by
  refine MeasureTheory.Lp.ext ?_
  rw [Fin.sum_univ_three]
  filter_upwards [MeasureTheory.Lp.coeFn_add
      (L2VF_injectComponent 0 (L2VF_projComponent 0 w)
        + L2VF_injectComponent 1 (L2VF_projComponent 1 w))
      (L2VF_injectComponent 2 (L2VF_projComponent 2 w)),
    MeasureTheory.Lp.coeFn_add (L2VF_injectComponent 0 (L2VF_projComponent 0 w))
      (L2VF_injectComponent 1 (L2VF_projComponent 1 w)),
    injectComponent_projComponent_ae 0 w, injectComponent_projComponent_ae 1 w,
    injectComponent_projComponent_ae 2 w] with x hx1 hx2 hc0 hc1 hc2
  rw [hx1, Pi.add_apply, hx2, Pi.add_apply, hc0, hc1, hc2]
  have hsum := (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr (w x)
  simpa [Fin.sum_univ_three, EuclideanSpace.basisFun_apply,
    EuclideanSpace.basisFun_repr] using hsum

/-! ### D-08: Divergence-free predicate -/

/-- A velocity field `u ∈ L²(𝕋³; ℝ³)` is **divergence-free** (in the L² / Fourier sense) if
every wavenumber `k ∈ ℤ³` satisfies the orthogonality condition

  `∑ j : Fin 3, (k j : ℂ) * û_j(k) = 0`

where `û_j(k) = mFourierCoeff3 (L2VF_projComponentC j u) k ∈ ℂ` is the `k`-th scalar
Fourier coefficient of the `j`-th complex-embedded component of `u`.

This is the Fourier characterisation of `div u = 0` for L² vector fields on `𝕋³`:
in the Fourier domain, `div u = 0` iff `k · û(k) = ∑_j k_j û_j(k) = 0` for all `k`. -/
def DivFreeL2 (u : L2VF) : Prop :=
  ∀ k : Fin 3 → ℤ,
    ∑ j : Fin 3, (k j : ℂ) * mFourierCoeff3 (L2VF_projComponentC j u) k = 0

end LerayHopf
