import LerayHopf.R3.Domain
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Algebra.Module.Submodule.Lattice
-- WL-1: SeparableSpace L2VF_R3 — via Lp.SecondCountableTopology
--   (IsSeparable volume from CountablyGenerated+SFinite; SeparableSpace EuclideanSpace from SecondCountableTopology)
import Mathlib.MeasureTheory.Measure.SeparableMeasure
-- WL-4: L2Sigma_R3_weaklyClosed — Mazur: closed convex set is weakly closed
import Mathlib.Analysis.LocallyConvex.WeakSpace

open MeasureTheory LineDeriv Topology

/-!
# L²_σ(ℝ³): weak-divergence-free subspace on ℝ³

**R3-a — DivergenceFree.**

This file constructs the closed divergence-free subspace `L2Sigma_R3` of
`L2VF_R3 = L²(ℝ³; ℝ³)` using the **weak-divergence-against-Schwartz-tests**
formulation (as opposed to the Fourier-mode characterisation used on the torus).

## Design

The divergence-free condition for L² vector fields on ℝ³ in the weak/distributional
sense says that for every test function `φ : 𝓢(ℝ³, ℝ)` (Schwartz function),

  `∑ j, ∫ (u x j) * (∂_j φ)(x) dx = 0`

We realise this as a continuous ℝ-linear functional
`divTestFunctional φ : L2VF_R3 →L[ℝ] ℝ`
by expressing the sum as a finite sum of CLM compositions:

  for each `j`:
    1. Project `u ↦ u_j` via `L2VF_projComponent_R3 j : L2VF_R3 →L[ℝ] Lp ℝ 2 volume`.
    2. Take the L²-inner product with the L²-element `(∂_j φ).toLp 2 volume`,
       using `innerSL ℝ : Lp ℝ 2 volume →L⋆[ℝ] (Lp ℝ 2 volume →L[ℝ] ℝ)`.

The j-th partial derivative `∂_j φ` (in direction `EuclideanSpace.single j 1`) is a
Schwartz function produced by `lineDerivOpCLM ℝ 𝓢(Domain3, ℝ) (EuclideanSpace.single j 1)`,
which has type `𝓢(Domain3, ℝ) →L[ℝ] 𝓢(Domain3, ℝ)`.  We then embed via `toLp`.

## Main definitions

- `divTestFunctional φ`   : `L2VF_R3 →L[ℝ] ℝ` — weak divergence against φ
- `L2Sigma_R3`            : `Submodule ℝ L2VF_R3` — the closed div-free subspace
- `isClosed_L2Sigma_R3`   : `IsClosed (L2Sigma_R3 : Set L2VF_R3)`
- `lerayProjection_R3`    : `L2VF_R3 →L[ℝ] L2Sigma_R3` — the Leray projection
-/

namespace LerayHopf

-- Convenience abbreviation: the `Lp ℝ 2 volume` scalar space over Domain3.
private noncomputable abbrev ScalarL2 := Lp ℝ 2 (volume : Measure Domain3)

/-! ### Weak divergence functional -/

-- Note: `Fact (1 ≤ 2)` (for ENNReal) is provided by the global instance
-- `fact_one_le_two_ennreal` in `Data.ENNReal.Basic` (already in the import chain via
-- `MeasureTheory.Function.L2Space`).
-- `Measure.HasTemperateGrowth` for `volume : Measure Domain3` holds via
-- `IsAddHaarMeasure.instHasTemperateGrowth` (EuclideanSpace is FiniteDimensional and
-- `volume` is `IsAddHaarMeasure` from `measureSpaceOfInnerProductSpace`).

/-- The weak-divergence test functional against a Schwartz function `φ : 𝓢(ℝ³, ℝ)`.

  `divTestFunctional φ u = ∑ j : Fin 3, ⟪(∂_j φ).toLp 2 volume, u_j⟫`

where `u_j = L2VF_projComponent_R3 j u ∈ Lp ℝ 2 volume` is the j-th component of `u`
and `⟪g, ·⟫ = innerSL ℝ g` is the continuous real inner product functional.

This is a continuous ℝ-linear functional, being a finite sum of CLM compositions:

  `∑ j, (innerSL ℝ ((∂_j φ).toLp 2 volume)) ∘L (L2VF_projComponent_R3 j)` -/
noncomputable def divTestFunctional (φ : SchwartzMap Domain3 ℝ) : L2VF_R3 →L[ℝ] ℝ :=
  ∑ j : Fin 3,
    (innerSL ℝ ((lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
          (EuclideanSpace.single j (1 : ℝ) : Domain3) φ).toLp
        2 (volume : Measure Domain3))).comp
      (L2VF_projComponent_R3 j)

/-! ### The closed divergence-free subspace -/

/-- `L²_σ(ℝ³)`: the closed subspace of weakly-divergence-free L²(ℝ³; ℝ³) velocity fields.

Defined as the common kernel of the continuous test functionals
`divTestFunctional φ : L2VF_R3 →L[ℝ] ℝ` over all Schwartz test functions
`φ : 𝓢(ℝ³, ℝ)`.  This is an infimum of submodules (hence a submodule), and
closedness follows because each functional is continuous. -/
noncomputable def L2Sigma_R3 : Submodule ℝ L2VF_R3 :=
  ⨅ φ : SchwartzMap Domain3 ℝ, (divTestFunctional φ).ker

/-- `L2Sigma_R3` is a closed subset of `L2VF_R3`. -/
theorem isClosed_L2Sigma_R3 : IsClosed (L2Sigma_R3 : Set L2VF_R3) := by
  simp only [L2Sigma_R3, Submodule.coe_iInf]
  exact isClosed_iInter fun φ => ContinuousLinearMap.isClosed_ker (divTestFunctional φ)

/-! ### WL-1 — Separability of L2VF_R3 -/

/-- **WL-1.** `L2VF_R3 = Lp (EuclideanSpace ℝ (Fin 3)) 2 (volume : Measure Domain3)` is a
separable topological space.

**Proof route** (all via Mathlib instances):
1. `Domain3 = EuclideanSpace ℝ (Fin 3)` is a `BorelSpace` with `SecondCountableTopology`,
   so `CountablyGenerated Domain3` fires (`borelSpace_isSeparable_of_secondCountable`).
2. Lebesgue measure on ℝ³ is σ-finite, hence `SFinite (volume : Measure Domain3)`.
3. `MeasureTheory.IsSeparable (volume : Measure Domain3)` fires from steps 1–2
   via the instance `[CountablyGenerated X] [SFinite μ] : IsSeparable μ`.
4. `EuclideanSpace ℝ (Fin 3)` is finite-dimensional, hence has `SecondCountableTopology`,
   hence `SeparableSpace (EuclideanSpace ℝ (Fin 3))` by `SecondCountableTopology.to_separableSpace`.
5. `MeasureTheory.Lp.SecondCountableTopology [IsSeparable μ] [SeparableSpace E]` gives
   `SecondCountableTopology L2VF_R3`.
6. `SecondCountableTopology.to_separableSpace` gives `SeparableSpace L2VF_R3`. -/
theorem L2VF_R3_separable : TopologicalSpace.SeparableSpace L2VF_R3 := by
  sorry -- ALLOW_SORRY: #47 WL-1 — inferInstance chain via Lp.SecondCountableTopology; prover to verify instances fire

/-! ### WL-4 — Weak closedness of L2Sigma_R3 -/

/-- **WL-4.** `L2Sigma_R3` is closed in `WeakSpace ℝ L2VF_R3`.

**Proof route** (via Mazur's lemma, present in Mathlib as `Convex.toWeakSpace_closure`):
- `L2Sigma_R3` is a `Submodule ℝ L2VF_R3`, hence convex.
- `isClosed_L2Sigma_R3` gives strong closure.
- `Convex.toWeakSpace_closure` (Mazur's lemma) says that for a convex set `s`,
  `(toWeakSpace ℝ E) '' (closure s) = closure ((toWeakSpace ℝ E) '' s)`.
- Since `L2Sigma_R3` is already strongly closed, `(toWeakSpace ℝ L2VF_R3) '' L2Sigma_R3`
  is closed in `WeakSpace ℝ L2VF_R3`.
- As `toWeakSpace ℝ L2VF_R3` is a bijection, this translates to `IsClosed` of the
  image (which is identified with `L2Sigma_R3` via the linear equivalence). -/
theorem L2Sigma_R3_weaklyClosed :
    IsClosed ((toWeakSpace ℝ L2VF_R3) '' (L2Sigma_R3 : Set L2VF_R3)) := by
  sorry -- ALLOW_SORRY: #47 WL-4 — Mazur's lemma (Convex.toWeakSpace_closure) + isClosed_L2Sigma_R3; prover to fill

/-! ### Completeness and orthogonal projection -/

/-- L²_σ(ℝ³) is complete: it is a closed subspace of the complete space `L2VF_R3`. -/
instance : CompleteSpace L2Sigma_R3 :=
  isClosed_L2Sigma_R3.completeSpace_coe

/-- L²_σ(ℝ³) has an orthogonal projection from `L2VF_R3`.
Follows from `HasOrthogonalProjection.ofCompleteSpace` once `CompleteSpace L2Sigma_R3`
is established. -/
instance : L2Sigma_R3.HasOrthogonalProjection :=
  inferInstance

/-! ### Leray projection -/

/-- The Leray projection Π_σ : L2VF_R3 →L[ℝ] L2Sigma_R3.

The orthogonal projection of L²(ℝ³; ℝ³) onto the closed weakly-divergence-free subspace
`L2Sigma_R3 = L²_σ(ℝ³)`.  Its range is exactly `L2Sigma_R3` and its kernel is
`L2Sigma_R3`ᗮ (the space of L² gradients, by the Helmholtz decomposition — not
formalized here).

Defined as `L2Sigma_R3.orthogonalProjectionOnto`. -/
noncomputable def lerayProjection_R3 : L2VF_R3 →L[ℝ] L2Sigma_R3 :=
  L2Sigma_R3.orthogonalProjectionOnto

/-! ### Genuine Schwartz convection integral (non-vacuity pin) -/

/-- **The genuine Schwartz convection integral `∫(u·∇)v·w`.**

Concretely:
  `convIntegralSchwartz ψu ψv ψw = ∑ i : Fin 3, ∑ a : Fin 3,
    ∫ x, (ψu a x) * (∂_a ψv_i)(x) * (ψw i x) ∂volume`

where:
- `(ψu a) x` is the pointwise value of the Schwartz function `ψu a` at `x` (via `DFunLike`);
- `lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ) (EuclideanSpace.single a 1) (ψv i)` is the
  partial derivative `∂_a (ψv i)` as a Schwartz function (via `LineDeriv.lineDerivOpCLM`);
- the integral `∫ x, f x ∂volume` is a Bochner integral (unconditional: returns 0 on
  non-integrable integrands, but products of Schwartz functions are in L¹ so this is genuine).

This equals `∫ (u·∇)v·w` when `u_a = ψu a`, `v_i = ψv i`, `w_i = ψw i` component-wise.
It is **sorry-free and axiom-free** — the definition is purely analytic. -/
noncomputable def convIntegralSchwartz
    (ψu ψv ψw : Fin 3 → SchwartzMap Domain3 ℝ) : ℝ :=
  ∑ i : Fin 3, ∑ a : Fin 3,
    ∫ x : Domain3,
      (ψu a x) *
      (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
        (EuclideanSpace.single a (1 : ℝ) : Domain3) (ψv i)) x *
      (ψw i x)
    ∂(volume : Measure Domain3)

end LerayHopf
