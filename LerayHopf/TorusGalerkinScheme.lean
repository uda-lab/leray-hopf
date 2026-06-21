import LerayHopf.AxiomaticClosure
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

open MeasureTheory Filter Topology Submodule

/-!
# The finite-dimensional Galerkin subspace `Vₙ` on 𝕋³ (issue #24)

This file constructs the finite-dimensional real subspace `velocitySpan n ≤ L2VF` realizing
the range of the componentwise Galerkin projection `velocityProjection_n n`, together with the
`FiniteDimensional` / `CompleteSpace` / `HasOrthogonalProjection` instances and the bridge
lemmas connecting "`x ∈ velocitySpan n`" to "`velocityProjection_n n x = x`".  It is the torus
analog of `R3/GalerkinScheme.lean`'s S1–S6 layer (`galerkinSpan`, `galerkinP`, …), but built
**from** the existing `velocityProjection_n` (Route C, componentwise) rather than from a
`Fin n`-indexed Hilbert basis (the torus has no vector Hilbert basis).

## Design (Fallback A of the phase plan)

`velocitySpan n := LinearMap.range (velocityProjection_n n)`.  Idempotence of
`velocityProjection_n n` (proved here, `velocityProjection_n_idem`, componentwise from the
idempotence of the scalar `fourierProjection_n`) gives:
- `velocityP_fixes_span` : `v ∈ velocitySpan n → velocityProjection_n n v = v`;
- `mem_velocitySpan_of_fixed` : the converse (trivial: `x = velocityProjection_n n x` exhibits
  `x` as a value of the projector).
Finite-dimensionality follows because each complex component of a `velocitySpan n` element has
Fourier support inside the finite `fourierBox n`, so `velocitySpan n` embeds (via the three
components) into a finite-dimensional space; concretely we exhibit a surjection onto
`velocitySpan n` from the finite-dimensional `L2VF` quotient by using that the projector's range
is the image of the finite-rank projector.

## Main definitions and theorems

- `velocityProjection_n_idem`        : `Pₙ (Pₙ u) = Pₙ u`
- `velocitySpan n`                   : `Submodule ℝ L2VF`, the range of `velocityProjection_n n`
- `velocitySpan_finiteDimensional`   : finite-dim instance
- `velocitySpan_completeSpace`       : complete-space instance
- `velocitySpan_hasOrthogonalProjection`
- `velocitySpan_le_sigma`            : `velocitySpan n ≤ L2Sigma` (div-free containment)
- `velocitySpanToSigma`              : the embedding `velocitySpan n → L2Sigma`
- `velocityP_fixes_span`             : range ⊆ fixed points
- `mem_velocitySpan_of_fixed`        : fixed points ⊆ range
- `velocityP_initial_mem`            : `Pₙ u₀ ∈ velocitySpan n`
-/

namespace LerayHopf

/-! ### Idempotence of the velocity Galerkin projection

The componentwise projector inherits idempotence from the scalar `fourierProjection_n`
(a `starProjection`, hence idempotent).  We prove it via the Fourier-coefficient
characterisation: two elements of `L2VF` are equal iff all their complex components have equal
Fourier coefficients, and `velocityProjection_n_component_comm` reduces the `j`-th component to
`fourierProjection_n n`, which is idempotent by `fourierProjection_n_mFourierCoeff`. -/

/-- Two velocity fields are equal once all complex components have equal Fourier coefficients.

`L2VF_projComponentC j u` is `RCLike.ofRealCLM ∘ L2VF_projComponent j u`; equality of all complex
components forces equality of the real components (`ofRealCLM` injective at the `Lp` level), and a
velocity field is determined by its three real components. -/
private lemma L2VF_ext_componentC_mFourierCoeff {u v : L2VF}
    (h : ∀ (j : Fin 3) (k : Fin 3 → ℤ),
      mFourierCoeff3 (L2VF_projComponentC j u) k = mFourierCoeff3 (L2VF_projComponentC j v) k) :
    u = v := by
  -- First, equal Fourier coefficients ⇒ equal complex components.
  have hcompC : ∀ j : Fin 3, L2VF_projComponentC j u = L2VF_projComponentC j v := by
    intro j
    exact torus3_mFourierBasis.repr.injective (lp.ext (funext (h j)))
  -- Equal complex components ⇒ equal real components (ofRealCLM injective on Lp).
  have hcomp : ∀ j : Fin 3, L2VF_projComponent j u = L2VF_projComponent j v := by
    intro j
    have hjC := hcompC j
    -- `L2VF_projComponentC j = ofRealCLM.compLpL ∘ L2VF_projComponent j`.
    have hu : L2VF_projComponentC j u
        = (RCLike.ofRealCLM (K := ℂ)).compLpL 2 haarTorus3 (L2VF_projComponent j u) := rfl
    have hv : L2VF_projComponentC j v
        = (RCLike.ofRealCLM (K := ℂ)).compLpL 2 haarTorus3 (L2VF_projComponent j v) := rfl
    rw [hu, hv] at hjC
    refine MeasureTheory.Lp.ext ?_
    have h1 := ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := haarTorus3)
      (RCLike.ofRealCLM (K := ℂ)) (L2VF_projComponent j u)
    have h2 := ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := haarTorus3)
      (RCLike.ofRealCLM (K := ℂ)) (L2VF_projComponent j v)
    have hcoe : ⇑((RCLike.ofRealCLM (K := ℂ)).compLpL 2 haarTorus3 (L2VF_projComponent j u))
        =ᵐ[haarTorus3]
        ⇑((RCLike.ofRealCLM (K := ℂ)).compLpL 2 haarTorus3 (L2VF_projComponent j v)) := by
      rw [hjC]
    filter_upwards [h1, h2, hcoe] with x hx1 hx2 hxc
    have hcc : (RCLike.ofRealCLM (K := ℂ)) (L2VF_projComponent j u x)
        = (RCLike.ofRealCLM (K := ℂ)) (L2VF_projComponent j v x) := by
      rw [← hx1, ← hx2]; exact hxc
    have : ((L2VF_projComponent j u x : ℝ) : ℂ) = ((L2VF_projComponent j v x : ℝ) : ℂ) := by
      simpa using hcc
    exact_mod_cast this
  -- A velocity field is determined by its three real components: reassemble.
  have hreassemble : ∀ w : L2VF,
      ∑ j : Fin 3, L2VF_injectComponent j (L2VF_projComponent j w) = w := by
    intro w
    refine MeasureTheory.Lp.ext ?_
    have hcompae : ∀ j : Fin 3, L2VF_injectComponent j (L2VF_projComponent j w)
        =ᵐ[haarTorus3] fun x => w x j • EuclideanSpace.single j (1 : ℝ) := by
      intro j
      simp only [L2VF_injectComponent, L2VF_projComponent]
      filter_upwards [ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := haarTorus3)
          ((ContinuousLinearMap.id ℝ ℝ).smulRight (EuclideanSpace.single j (1 : ℝ)))
          ((EuclideanSpace.proj j (𝕜 := ℝ)).compLpL 2 haarTorus3 w),
        ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := haarTorus3)
          (EuclideanSpace.proj j (𝕜 := ℝ)) w] with x hx1 hx2
      rw [hx1, hx2]; simp
    rw [Fin.sum_univ_three]
    filter_upwards [MeasureTheory.Lp.coeFn_add
        (L2VF_injectComponent 0 (L2VF_projComponent 0 w)
          + L2VF_injectComponent 1 (L2VF_projComponent 1 w))
        (L2VF_injectComponent 2 (L2VF_projComponent 2 w)),
      MeasureTheory.Lp.coeFn_add (L2VF_injectComponent 0 (L2VF_projComponent 0 w))
        (L2VF_injectComponent 1 (L2VF_projComponent 1 w)),
      hcompae 0, hcompae 1, hcompae 2] with x hx1 hx2 hc0 hc1 hc2
    rw [hx1, Pi.add_apply, hx2, Pi.add_apply, hc0, hc1, hc2]
    have hsum := (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr (w x)
    simpa [Fin.sum_univ_three, EuclideanSpace.basisFun_apply,
      EuclideanSpace.basisFun_repr] using hsum
  calc u = ∑ j : Fin 3, L2VF_injectComponent j (L2VF_projComponent j u) := (hreassemble u).symm
    _ = ∑ j : Fin 3, L2VF_injectComponent j (L2VF_projComponent j v) := by
        refine Finset.sum_congr rfl ?_; intro j _; rw [hcomp j]
    _ = v := hreassemble v

/-- **Idempotence of the velocity Galerkin projection.**  `Pₙ (Pₙ u) = Pₙ u`.

Componentwise from `velocityProjection_n_component_comm` + idempotence of `fourierProjection_n`
(`fourierProjection_n_mFourierCoeff`: coefficients inside the box are preserved, outside killed,
so applying the cutoff twice is the cutoff). -/
theorem velocityProjection_n_idem (n : ℕ) (u : L2VF) :
    velocityProjection_n n (velocityProjection_n n u) = velocityProjection_n n u := by
  refine L2VF_ext_componentC_mFourierCoeff (fun j k => ?_)
  -- LHS: components of `Pₙ (Pₙ u)`; RHS: components of `Pₙ u`.
  rw [velocityProjection_n_component_comm]
  -- LHS now `mFourierCoeff3 (fourierProjection_n n (componentC j (Pₙ u))) k`.
  rw [show ((fourierProjection_n n).restrictScalars ℝ (L2VF_projComponentC j (velocityProjection_n n u)))
        = fourierProjection_n n (L2VF_projComponentC j (velocityProjection_n n u)) from rfl]
  rw [velocityProjection_n_component_comm]
  rw [show ((fourierProjection_n n).restrictScalars ℝ (L2VF_projComponentC j u))
        = fourierProjection_n n (L2VF_projComponentC j u) from rfl]
  -- Goal: `mFourierCoeff3 (Pₙ (Pₙ f)) k = mFourierCoeff3 (Pₙ f) k` with `f = componentC j u`.
  simp only [fourierProjection_n_mFourierCoeff]
  by_cases hk : k ∈ fourierBox n <;> simp [hk]

/-! ### The finite-dimensional velocity subspace `Vₙ` -/

/-- The `n`-th Galerkin subspace `Vₙ ≤ L2VF`: the image of the divergence-free subspace
`L2Sigma` under the componentwise projector `velocityProjection_n n`.

Mirrors `R3/GalerkinScheme.lean`'s `galerkinSpan B n` (the span of finitely many div-free basis
vectors), but built from the Route-C projector.  Taking the image of `L2Sigma` — rather than the
full range of `velocityProjection_n n` — is what makes `velocitySpan n ≤ L2Sigma` true:
`velocityProjection_n n` does NOT map an arbitrary field into `L2Sigma` (it only does so when the
argument is already divergence-free, `velocityProjection_n_preserves_L2Sigma`), so the honest
Galerkin subspace is `Pₙ '' L2Sigma`. -/
noncomputable def velocitySpan (n : ℕ) : Submodule ℝ L2VF :=
  Submodule.map (velocityProjection_n n).toLinearMap L2Sigma

/-- Membership in `velocitySpan n`: is the projection of some divergence-free field. -/
theorem mem_velocitySpan_iff (n : ℕ) (x : L2VF) :
    x ∈ velocitySpan n ↔ ∃ y ∈ L2Sigma, velocityProjection_n n y = x := by
  simp only [velocitySpan, Submodule.mem_map, ContinuousLinearMap.coe_coe]

/-! ### Bridge lemmas: `Vₙ` is the fixed-point set of `velocityProjection_n n` -/

/-- **Bridge (range ⊆ fixed points).** Every `v ∈ velocitySpan n` is fixed by the projector. -/
theorem velocityP_fixes_span (n : ℕ) (v : velocitySpan n) :
    velocityProjection_n n (v : L2VF) = (v : L2VF) := by
  obtain ⟨y, _, hy⟩ := (mem_velocitySpan_iff n (v : L2VF)).mp v.2
  rw [← hy, velocityProjection_n_idem]

/-- **Bridge (fixed points ⊆ range).** Any divergence-free `x` fixed by the projector lies in
`velocitySpan n`.  The `L2Sigma` hypothesis is exactly satisfied by the Galerkin test functions
in `u_ode` (typed `w : L2Sigma` with `velocityProjection_n n w = w`). -/
theorem mem_velocitySpan_of_fixed (n : ℕ) (x : L2VF) (hxσ : x ∈ L2Sigma)
    (hx : velocityProjection_n n x = x) : x ∈ velocitySpan n :=
  (mem_velocitySpan_iff n x).mpr ⟨x, hxσ, hx⟩

/-! ### Finite dimensionality and completeness -/

/-- The `j`-th complex component of a `velocitySpan n` element lies in `fourierSpan n`.

A `velocitySpan n` element `v` is fixed by `Pₙ`, so by `velocityProjection_n_component_comm` its
`j`-th component equals `fourierProjection_n n` of itself, hence lies in the projector's range,
which is `fourierSpan n`. -/
theorem componentC_mem_fourierSpan (n : ℕ) (v : velocitySpan n) (j : Fin 3) :
    L2VF_projComponentC j (v : L2VF) ∈ fourierSpan n := by
  have hfix : velocityProjection_n n (v : L2VF) = (v : L2VF) := velocityP_fixes_span n v
  have hcomp : L2VF_projComponentC j (v : L2VF)
      = fourierProjection_n n (L2VF_projComponentC j (v : L2VF)) := by
    conv_lhs => rw [← hfix]
    rw [velocityProjection_n_component_comm]
    rfl
  rw [hcomp, fourierProjection_n]
  exact Submodule.starProjection_apply_mem _ _

/-- `velocitySpan n` is finite-dimensional.

Each complex component of a `velocitySpan n` element lies in the finite-dimensional `fourierSpan n`
(`componentC_mem_fourierSpan`), and a velocity field is determined by its three complex components
(`L2VF_ext_componentC_mFourierCoeff`).  Hence the linear map sending `v` to its three components is
an **injection** `velocitySpan n ↪ (Fin 3 → fourierSpan n)` into a finite-dimensional space, so
`velocitySpan n` is finite-dimensional. -/
instance velocitySpan_finiteDimensional (n : ℕ) : FiniteDimensional ℝ (velocitySpan n) := by
  -- The componentwise embedding `velocitySpan n →ₗ[ℝ] (Fin 3 → fourierSpan n)`.
  letI : Module ℝ L2C := inferInstance
  set emb : velocitySpan n →ₗ[ℝ] (Fin 3 → fourierSpan n) :=
    { toFun := fun v j => ⟨L2VF_projComponentC j (v : L2VF), componentC_mem_fourierSpan n v j⟩
      map_add' := by
        intro v w; funext j; apply Subtype.ext
        show L2VF_projComponentC j ((v + w : velocitySpan n) : L2VF)
          = L2VF_projComponentC j (v : L2VF) + L2VF_projComponentC j (w : L2VF)
        rw [Submodule.coe_add, map_add]
      map_smul' := by
        intro c v; funext j; apply Subtype.ext
        show L2VF_projComponentC j ((c • v : velocitySpan n) : L2VF) = c • L2VF_projComponentC j (v : L2VF)
        rw [Submodule.coe_smul, map_smul] }
    with hemb
  -- `fourierSpan n` is finite-dim over ℂ, hence over ℝ (restriction of scalars).
  haveI : FiniteDimensional ℝ (fourierSpan n) :=
    FiniteDimensional.trans ℝ ℂ (fourierSpan n)
  haveI : FiniteDimensional ℝ (Fin 3 → fourierSpan n) := inferInstance
  have hinj : Function.Injective emb := by
    intro v w hvw
    apply Subtype.ext
    refine L2VF_ext_componentC_mFourierCoeff (fun j k => ?_)
    have hj : (emb v) j = (emb w) j := congrFun hvw j
    have : L2VF_projComponentC j (v : L2VF) = L2VF_projComponentC j (w : L2VF) :=
      congrArg Subtype.val hj
    rw [this]
  exact FiniteDimensional.of_injective emb hinj

/-- `velocitySpan n` is complete (finite-dimensional submodule of a normed space). -/
instance velocitySpan_completeSpace (n : ℕ) : CompleteSpace (velocitySpan n) :=
  (Submodule.complete_of_finiteDimensional (velocitySpan n)).completeSpace_coe

/-- `velocitySpan n` has an orthogonal projection (from completeness). -/
instance velocitySpan_hasOrthogonalProjection (n : ℕ) :
    (velocitySpan n).HasOrthogonalProjection :=
  inferInstance

/-! ### Divergence-free containment and the embedding into `L2Sigma` -/

/-- `velocitySpan n ≤ L2Sigma`: every element of the Galerkin subspace is divergence-free.

Immediate now that `velocitySpan n = Pₙ '' L2Sigma`: a value `v = Pₙ y` with `y ∈ L2Sigma` is
div-free by `velocityProjection_n_preserves_L2Sigma`. -/
theorem velocitySpan_le_sigma (n : ℕ) : velocitySpan n ≤ L2Sigma := by
  intro v hv
  obtain ⟨y, hyσ, hy⟩ := (mem_velocitySpan_iff n v).mp hv
  rw [← hy]
  exact velocityProjection_n_preserves_L2Sigma n y hyσ

/-- The `j`-th component coercion is the same data; helper to keep the `L2Sigma` membership. -/
theorem mem_sigma_of_mem_velocitySpan (n : ℕ) (v : velocitySpan n) : (v : L2VF) ∈ L2Sigma :=
  velocitySpan_le_sigma n v.2

/-- The embedding `velocitySpan n ↪ L2Sigma` (torus analog of `galerkinSpanToSigma`). -/
noncomputable def velocitySpanToSigma (n : ℕ) (v : velocitySpan n) : L2Sigma :=
  ⟨(v : L2VF), mem_sigma_of_mem_velocitySpan n v⟩

@[simp] theorem velocitySpanToSigma_coe (n : ℕ) (v : velocitySpan n) :
    (velocitySpanToSigma n v : L2VF) = (v : L2VF) := rfl

theorem velocitySpanToSigma_add (n : ℕ) (v w : velocitySpan n) :
    velocitySpanToSigma n (v + w) = velocitySpanToSigma n v + velocitySpanToSigma n w := by
  apply Subtype.ext; rfl

theorem velocitySpanToSigma_smul (n : ℕ) (c : ℝ) (v : velocitySpan n) :
    velocitySpanToSigma n (c • v) = c • velocitySpanToSigma n v := by
  apply Subtype.ext; rfl

/-! ### The initial datum lives in `Vₙ` -/

/-- `velocityProjection_n n u₀ ∈ velocitySpan n` (analog of `galerkinP_mem_span`). -/
theorem velocityP_initial_mem (n : ℕ) (u₀ : L2Sigma) :
    velocityProjection_n n (u₀ : L2VF) ∈ velocitySpan n :=
  (mem_velocitySpan_iff n _).mpr ⟨(u₀ : L2VF), u₀.2, rfl⟩

end LerayHopf
