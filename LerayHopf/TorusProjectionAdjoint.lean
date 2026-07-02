/-
# LerayHopf.TorusProjectionAdjoint — orthogonality calculus for `velocityProjection_n`

**Milestone:** torus `galerkin_limit_passage` removal campaign, PR-1 (kernel #2).

The Fourier–Galerkin velocity projection `Pₙ = velocityProjection_n n : L2VF →L[ℝ] L2VF`
is componentwise the complex orthogonal projection `fourierProjection_n n`
(a `starProjection`), so it is a genuine ℝ-orthogonal projection.  This file records the
orthogonality calculus that the good-representative construction
(`TorusTraceEnergy.lean`, PR-2) consumes:

- `L2VF_inner_eq_sum_componentC`        : ℝ-inner product as a sum of complex component inners
- `fourierProjection_n_inner_symm`      : self-adjointness of the scalar projection
- `velocityProjection_n_inner_symm`     : self-adjointness of the velocity projection
- `velocityProjection_n_inner_of_fixed` : `Pₙ w = w → ⟪Pₙ u, w⟫ = ⟪u, w⟫`
- `velocityProjection_n_comp_of_le`     : `n ≤ m → Pₙ (Pₘ u) = Pₙ u` (nested truncation)
- `velocityProjection_n_inner_sub_self` : `⟪Pₙ u, u − Pₙ u⟫ = 0`
- `velocityProjection_n_pythagoras`     : `‖Pₙ u‖² + ‖u − Pₙ u‖² = ‖u‖²`

## Axioms

No new axioms; everything reduces to mathlib's `starProjection` API and the
Fourier-coefficient characterisation of `L2VF`.
-/

import LerayHopf.TorusGalerkinODESolve

namespace LerayHopf

/-! ### The ℝ-inner product of `L2VF` through the complex components -/

/-- **Componentwise inner-product decomposition.**  The real `L2VF` inner product is the
sum over the three components of the real parts of the complex `L2C` inner products of the
complexified components.

Proof: polarize both sides — `⟪u,v⟫ = (‖u+v‖² − ‖u‖² − ‖v‖²)/2` over ℝ and
`re ⟪a,b⟫ = (‖a+b‖² − ‖a‖² − ‖b‖²)/2` over ℂ — and reduce to the proved norm
decomposition `Torus.L2VF_norm_sq_eq_sum_componentC` (three times), using additivity of
`L2VF_projComponentC j`. -/
theorem L2VF_inner_eq_sum_componentC (u v : L2VF) :
    inner (𝕜 := ℝ) u v =
      ∑ j : Fin 3,
        (inner (𝕜 := ℂ) (L2VF_projComponentC j u) (L2VF_projComponentC j v)).re := by
  -- Real polarization on the left.
  have hL : inner (𝕜 := ℝ) u v
      = (‖u + v‖ ^ 2 - ‖u‖ ^ 2 - ‖v‖ ^ 2) / 2 := by
    have h := norm_add_sq_real u v
    linarith
  -- Complex polarization (real part) on each summand of the right.
  have hR : ∀ j : Fin 3,
      (inner (𝕜 := ℂ) (L2VF_projComponentC j u) (L2VF_projComponentC j v)).re
        = (‖L2VF_projComponentC j u + L2VF_projComponentC j v‖ ^ 2
            - ‖L2VF_projComponentC j u‖ ^ 2 - ‖L2VF_projComponentC j v‖ ^ 2) / 2 := by
    intro j
    have h := norm_add_sq (𝕜 := ℂ)
      (L2VF_projComponentC j u) (L2VF_projComponentC j v)
    rw [RCLike.re_to_complex] at h
    linarith
  rw [hL]
  simp only [hR]
  rw [← Finset.sum_div]
  congr 1
  have hadd : ∀ j : Fin 3, L2VF_projComponentC j (u + v)
      = L2VF_projComponentC j u + L2VF_projComponentC j v := fun j => map_add _ u v
  rw [Torus.L2VF_norm_sq_eq_sum_componentC (u + v),
    Torus.L2VF_norm_sq_eq_sum_componentC u, Torus.L2VF_norm_sq_eq_sum_componentC v]
  simp only [hadd]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]

/-! ### Self-adjointness -/

/-- Self-adjointness of the scalar Fourier projection (a `starProjection`). -/
theorem fourierProjection_n_inner_symm (n : ℕ) (f g : L2C) :
    inner (𝕜 := ℂ) (fourierProjection_n n f) g
      = inner (𝕜 := ℂ) f (fourierProjection_n n g) :=
  Submodule.inner_starProjection_left_eq_right (fourierSpan n) f g

/-- **Self-adjointness of the velocity Galerkin projection:**
`⟪Pₙ u, v⟫ = ⟪u, Pₙ v⟫` in `L2VF`.

Proof: decompose the ℝ-inner product into complex component inners
(`L2VF_inner_eq_sum_componentC`); on each component `Pₙ` acts as the scalar
`fourierProjection_n n` (`velocityProjection_n_component_comm`), which is a
`starProjection`, hence self-adjoint. -/
theorem velocityProjection_n_inner_symm (n : ℕ) (u v : L2VF) :
    inner (𝕜 := ℝ) (velocityProjection_n n u) v
      = inner (𝕜 := ℝ) u (velocityProjection_n n v) := by
  rw [L2VF_inner_eq_sum_componentC, L2VF_inner_eq_sum_componentC]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [velocityProjection_n_component_comm n u j, velocityProjection_n_component_comm n v j]
  rw [show ((fourierProjection_n n).restrictScalars ℝ (L2VF_projComponentC j u))
      = fourierProjection_n n (L2VF_projComponentC j u) from rfl,
    show ((fourierProjection_n n).restrictScalars ℝ (L2VF_projComponentC j v))
      = fourierProjection_n n (L2VF_projComponentC j v) from rfl,
    fourierProjection_n_inner_symm]

/-- Pairing against a band-limited element passes through the projection:
if `Pₙ w = w` then `⟪Pₙ u, w⟫ = ⟪u, w⟫`. -/
theorem velocityProjection_n_inner_of_fixed (n : ℕ) (u : L2VF) {w : L2VF}
    (hw : velocityProjection_n n w = w) :
    inner (𝕜 := ℝ) (velocityProjection_n n u) w = inner (𝕜 := ℝ) u w := by
  rw [velocityProjection_n_inner_symm, hw]

/-! ### Nested truncation -/

/-- **Nested truncation:** for `n ≤ m`, `Pₙ (Pₘ u) = Pₙ u` (truncating to the smaller
box forgets the larger one).  Proof: Fourier-coefficient extensionality; both sides have
`j`-th component coefficient `1_{box n}(k) · ûⱼ(k)` since `fourierBox n ⊆ fourierBox m`. -/
theorem velocityProjection_n_comp_of_le {n m : ℕ} (hnm : n ≤ m) (u : L2VF) :
    velocityProjection_n n (velocityProjection_n m u) = velocityProjection_n n u := by
  refine L2VF_ext_componentC_mFourierCoeff (fun j k => ?_)
  rw [velocityProjection_n_component_comm n _ j, velocityProjection_n_component_comm n u j]
  rw [show ((fourierProjection_n n).restrictScalars ℝ
        (L2VF_projComponentC j (velocityProjection_n m u)))
      = fourierProjection_n n (L2VF_projComponentC j (velocityProjection_n m u)) from rfl,
    show ((fourierProjection_n n).restrictScalars ℝ (L2VF_projComponentC j u))
      = fourierProjection_n n (L2VF_projComponentC j u) from rfl]
  rw [fourierProjection_n_mFourierCoeff, fourierProjection_n_mFourierCoeff,
    velocityProjection_n_component_comm m u j,
    show ((fourierProjection_n m).restrictScalars ℝ (L2VF_projComponentC j u))
      = fourierProjection_n m (L2VF_projComponentC j u) from rfl,
    fourierProjection_n_mFourierCoeff]
  by_cases hk : k ∈ fourierBox n
  · rw [if_pos hk, if_pos hk, if_pos (fourierBox_monotone hnm hk)]
  · rw [if_neg hk, if_neg hk]

/-! ### Orthogonality of the truncation split and Pythagoras -/

/-- The projected part is orthogonal to the tail: `⟪Pₙ u, u − Pₙ u⟫ = 0`. -/
theorem velocityProjection_n_inner_sub_self (n : ℕ) (u : L2VF) :
    inner (𝕜 := ℝ) (velocityProjection_n n u) (u - velocityProjection_n n u) = 0 := by
  rw [velocityProjection_n_inner_symm, map_sub, velocityProjection_n_idem, sub_self,
    inner_zero_right]

/-- **Pythagoras for the truncation split:** `‖Pₙ u‖² + ‖u − Pₙ u‖² = ‖u‖²`. -/
theorem velocityProjection_n_pythagoras (n : ℕ) (u : L2VF) :
    ‖velocityProjection_n n u‖ ^ 2 + ‖u - velocityProjection_n n u‖ ^ 2 = ‖u‖ ^ 2 := by
  have hsplit : u = velocityProjection_n n u + (u - velocityProjection_n n u) := by abel
  have h := norm_add_sq_real (velocityProjection_n n u) (u - velocityProjection_n n u)
  rw [velocityProjection_n_inner_sub_self] at h
  calc ‖velocityProjection_n n u‖ ^ 2 + ‖u - velocityProjection_n n u‖ ^ 2
      = ‖velocityProjection_n n u + (u - velocityProjection_n n u)‖ ^ 2 := by
        rw [h]; ring
    _ = ‖u‖ ^ 2 := by rw [← hsplit]

end LerayHopf
