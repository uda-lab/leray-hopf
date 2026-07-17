import LerayHopf.Torus.DivergenceFree
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Algebra.Module.Submodule.Lattice

open MeasureTheory

/-!
# L²_σ(𝕋³): the closed divergence-free subspace

**M2 — D-09.**

This file constructs `L²_σ(𝕋³)` as a closed submodule of `L2VF = L²(𝕋³; ℝ³)`,
without introducing any axiom.

## Design

The divergence-free condition `DivFreeL2 u` says that for every wavenumber
`k : Fin 3 → ℤ`, the functional

  `divSymbol k : L2VF →L[ℝ] ℂ`,   `u ↦ ∑ j, (k j : ℂ) * mFourierCoeff3 (L2VF_projComponentC j u) k`

vanishes.  Each `divSymbol k` is a **continuous** ℝ-linear functional (finite sum of
compositions of continuous linear maps scaled by complex constants), so its kernel is
a closed submodule.  `L²_σ` is the intersection of these kernels — an infimum of
Submodule(ℝ, L2VF), manifestly a closed submodule.

## Main definitions

- `fourierCoeffCLM k`   : `L2C →L[ℂ] ℂ` — `f ↦ ⟪torus3_mFourierBasis k, f⟫`
- `divSymbol k`         : `L2VF →L[ℝ] ℂ` — the `k`-th divergence symbol functional
- `L2Sigma`             : `Submodule ℝ L2VF` — the closed div-free subspace

## Main theorems (statements; proofs left for lean-prover)

- `fourierCoeffCLM_apply`   : `fourierCoeffCLM k f = mFourierCoeff3 f k`
- `divSymbol_apply`          : unfolds `divSymbol k u`
- `divFreeL2_iff_divSymbol`  : `DivFreeL2 u ↔ ∀ k, divSymbol k u = 0`
- `mem_L2Sigma_iff`          : `u ∈ L2Sigma ↔ DivFreeL2 u`
- `isClosed_L2Sigma`         : `IsClosed (L2Sigma : Set L2VF)`
-/

namespace LerayHopf

/-! ### D-09a: Continuous Fourier-coefficient functional -/

/-- The `k`-th Fourier-coefficient functional as a continuous ℂ-linear map `L2C →L[ℂ] ℂ`.

By `HilbertBasis.repr_apply_apply`, `torus3_mFourierBasis.repr f k = ⟪torus3_mFourierBasis k, f⟫`,
so this equals `mFourierCoeff3 f k`.  We define it via `innerSL` so that continuity is
automatic and the proof `fourierCoeffCLM_apply` is a one-line unfold. -/
noncomputable def fourierCoeffCLM (k : Fin 3 → ℤ) : L2C →L[ℂ] ℂ :=
  innerSL ℂ (torus3_mFourierBasis k)

/-! ### D-09b: Divergence-symbol CLM -/

/-- The divergence symbol at wavenumber `k`: a continuous ℝ-linear functional on `L2VF`.

  `divSymbol k u = ∑ j : Fin 3, (k j : ℂ) * mFourierCoeff3 (L2VF_projComponentC j u) k`

Constructed as a finite sum of ℝ-linear CLMs: for each `j`, we compose
  - `L2VF_projComponentC j : L2VF →L[ℝ] L2C`   (ℝ-linear projection + embedding)
  - `fourierCoeffCLM k : L2C →L[ℂ] ℂ`, restricted to ℝ-scalars
  - scaled by `(k j : ℂ)` via the `Module ℂ (L2VF →L[ℝ] ℂ)` instance.

`u ∈ L²_σ` iff `divSymbol k u = 0` for all `k`. -/
noncomputable def divSymbol (k : Fin 3 → ℤ) : L2VF →L[ℝ] ℂ :=
  ∑ j : Fin 3,
    (k j : ℂ) • ((fourierCoeffCLM k).restrictScalars ℝ ∘L L2VF_projComponentC j)

/-! ### D-09c: Bridge lemmas -/

/-- `fourierCoeffCLM k f = mFourierCoeff3 f k`.

Proof: `innerSL ℂ (torus3_mFourierBasis k) f = ⟪torus3_mFourierBasis k, f⟫`
by `innerSL_apply_apply`, and `torus3_mFourierBasis.repr_apply_apply` gives
`torus3_mFourierBasis.repr f k = ⟪torus3_mFourierBasis k, f⟫`. -/
theorem fourierCoeffCLM_apply (k : Fin 3 → ℤ) (f : L2C) :
    fourierCoeffCLM k f = mFourierCoeff3 f k := by
  simp only [fourierCoeffCLM, innerSL_apply_apply, mFourierCoeff3,
    HilbertBasis.repr_apply_apply]

/-- `divSymbol k u` unfolds to the Fourier divergence sum.

Proof: unfold `divSymbol`, use linearity of the CLM composition and `fourierCoeffCLM_apply`. -/
theorem divSymbol_apply (k : Fin 3 → ℤ) (u : L2VF) :
    divSymbol k u =
      ∑ j : Fin 3, (k j : ℂ) * mFourierCoeff3 (L2VF_projComponentC j u) k := by
  simp only [divSymbol, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
    fourierCoeffCLM_apply, smul_eq_mul]

/-- `DivFreeL2 u ↔ ∀ k, divSymbol k u = 0`. -/
theorem divFreeL2_iff_divSymbol (u : L2VF) :
    DivFreeL2 u ↔ ∀ k : Fin 3 → ℤ, divSymbol k u = 0 := by
  simp only [DivFreeL2, divSymbol_apply]

/-! ### D-09d: The closed divergence-free subspace L²_σ -/

/-- `L²_σ(𝕋³)`: the closed subspace of divergence-free L²(𝕋³; ℝ³) velocity fields.

Defined as the common kernel of the continuous divergence-symbol functionals
`divSymbol k : L2VF →L[ℝ] ℂ` over all wavenumbers `k : Fin 3 → ℤ`.
This is an infimum of submodules, hence a submodule.  Closedness follows because each
`divSymbol k` is continuous, so each kernel is closed (`ContinuousLinearMap.isClosed_ker`),
and an arbitrary intersection of closed sets is closed. -/
noncomputable def L2Sigma : Submodule ℝ L2VF :=
  ⨅ k : Fin 3 → ℤ, (divSymbol k).ker

/-- Membership in `L2Sigma` is equivalent to `DivFreeL2`. -/
theorem mem_L2Sigma_iff (u : L2VF) : u ∈ L2Sigma ↔ DivFreeL2 u := by
  simp only [L2Sigma, Submodule.mem_iInf, LinearMap.mem_ker, divFreeL2_iff_divSymbol,
    ContinuousLinearMap.coe_coe]

/-- `L2Sigma` is a closed subset of `L2VF`. -/
theorem isClosed_L2Sigma : IsClosed (L2Sigma : Set L2VF) := by
  simp only [L2Sigma, Submodule.coe_iInf]
  exact isClosed_iInter fun k => ContinuousLinearMap.isClosed_ker (divSymbol k)

/-! ### D-15/D-16: Completeness and orthogonal projection instance for L²_σ -/

/-- L²_σ(𝕋³) is complete: it is a closed subspace of the complete space L2VF.
Uses `IsClosed.completeSpace_coe` applied to `isClosed_L2Sigma`. -/
instance : CompleteSpace L2Sigma :=
  isClosed_L2Sigma.completeSpace_coe

/-- L²_σ(𝕋³) has an orthogonal projection from L2VF.
Follows from the `HasOrthogonalProjection.ofCompleteSpace` instance (priority 100) which
fires automatically once `CompleteSpace L2Sigma` is established (D-15). -/
instance : L2Sigma.HasOrthogonalProjection :=
  inferInstance

/-! ### D-18 through D-21b: Properties of the Leray projection (for lean-prover)

The Leray projection Π_div — the orthogonal projection of `L²(𝕋³;ℝ³)` onto the closed
divergence-free subspace `L2Sigma = L²_σ(𝕋³)` — enters everywhere below directly as
`L2Sigma.starProjection` (the mathlib star-projection of the closed submodule). -/

/-- The Leray projection (as L2VF → L2VF map) is idempotent: applying it twice
equals applying it once. Uses `Submodule.isIdempotentElem_starProjection`. -/
theorem lerayProjection_idempotent :
    IsIdempotentElem L2Sigma.starProjection :=
  L2Sigma.isIdempotentElem_starProjection

/-- The Leray projection fixes divergence-free fields: if `u ∈ L²_σ` then
`L2Sigma.starProjection u = u`. Uses `Submodule.starProjection_eq_self_iff`. -/
theorem lerayProjection_fixes_divFree (u : L2VF) (hu : u ∈ L2Sigma) :
    L2Sigma.starProjection u = u :=
  Submodule.starProjection_eq_self_iff.mpr hu

/-- The range of the Leray projection (as the L2VF → L2VF map) equals L²_σ.
Uses `Submodule.range_starProjection`. -/
theorem lerayProjection_range :
    L2Sigma.starProjection.range = L2Sigma :=
  L2Sigma.range_starProjection

/-- The Leray projection is self-adjoint (symmetric as a linear map on L2VF):
`inner (𝕜 := ℝ) (L2Sigma.starProjection u) v = inner (𝕜 := ℝ) u (L2Sigma.starProjection v)`.
Uses `Submodule.inner_starProjection_left_eq_right`. -/
theorem lerayProjection_isSymmetric (u v : L2VF) :
    inner (𝕜 := ℝ) (L2Sigma.starProjection u) v = inner (𝕜 := ℝ) u (L2Sigma.starProjection v) :=
  L2Sigma.inner_starProjection_left_eq_right u v

/-- The Leray projection has operator norm ≤ 1: `‖L2Sigma.starProjection‖ ≤ 1`.
Uses `Submodule.starProjection_norm_le`. -/
theorem lerayProjection_norm_le : ‖L2Sigma.starProjection‖ ≤ 1 :=
  L2Sigma.starProjection_norm_le

end LerayHopf
