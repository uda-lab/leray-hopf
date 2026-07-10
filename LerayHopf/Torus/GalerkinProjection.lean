import LerayHopf.Torus.Leray
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.LinearAlgebra.Span.Defs

open MeasureTheory Submodule Filter Topology

/-!
# Scalar Galerkin (Fourier-truncation) projection on L²(𝕋³; ℂ)

**M3 — Group B: D-22 through D-30a.**

This file builds the finite-dimensional Galerkin projection `fourierProjection_n n : L2C →L[ℂ] L2C`
as the orthogonal projection onto the span of Fourier modes with ‖k‖_∞ ≤ n.

## Main definitions

- `fourierBox n`          : `Finset (Fin 3 → ℤ)` — the cube `{k | ∀ i, |k i| ≤ n}`.
- `fourierSpan n`         : `Submodule ℂ L2C` — span of `torus3_mFourierBasis k` for `k ∈ fourierBox n`.
- `fourierProjection_n n` : `L2C →L[ℂ] L2C` — orthogonal projection onto `fourierSpan n`.

## Main statements (for lean-prover)

- `fourierBox_monotone`         : `Monotone fourierBox`
- `fourierBox_exhausts`         : `∀ k, ∃ n, k ∈ fourierBox n`
- `fourierSpan_monotone`        : `Monotone fourierSpan`
- `fourierSpan_iSup_dense`      : `⊤ ≤ (⨆ n, fourierSpan n).topologicalClosure`
- `fourierProjection_n_tendsto` : `∀ f, Tendsto (fun n => fourierProjection_n n f) atTop (𝓝 f)`
-/

namespace LerayHopf

/-! ### D-22: The Galerkin truncation cube -/

/-- The finite set of wavenumbers `k : Fin 3 → ℤ` with `‖k‖_∞ ≤ n`:
the coordinate-aligned cube `[-n, n]³` in ℤ³.

`fourierBox n = {k | ∀ i, -(n : ℤ) ≤ k i ≤ n}` as a `Finset (Fin 3 → ℤ)`.
Membership is by `Fintype.mem_piFinset` + `Finset.mem_Icc`. -/
noncomputable def fourierBox (n : ℕ) : Finset (Fin 3 → ℤ) :=
  Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-(n : ℤ)) n)

/-! ### D-25: The finite-dimensional Fourier span -/

/-- The finite-dimensional subspace of `L2C` spanned by Fourier modes with
wavenumber in `fourierBox n`. -/
noncomputable def fourierSpan (n : ℕ) : Submodule ℂ L2C :=
  Submodule.span ℂ (torus3_mFourierBasis '' ↑(fourierBox n))

/-! ### D-26: FiniteDimensional instance for fourierSpan -/

/-- `fourierSpan n` is finite-dimensional: it is the span of the finite set
`torus3_mFourierBasis '' ↑(fourierBox n)`. Uses `FiniteDimensional.span_of_finite`. -/
instance fourierSpan_finiteDimensional (n : ℕ) : FiniteDimensional ℂ (fourierSpan n) :=
  FiniteDimensional.span_of_finite ℂ (Set.toFinite _)

/-! ### D-27: CompleteSpace instance for fourierSpan -/

/-- `fourierSpan n` is complete: a finite-dimensional submodule of a normed space
over a complete field is complete. Uses `Submodule.complete_of_finiteDimensional`
(returns `IsComplete`) converted to `CompleteSpace` via `IsComplete.completeSpace_coe`. -/
instance fourierSpan_completeSpace (n : ℕ) : CompleteSpace (fourierSpan n) :=
  (Submodule.complete_of_finiteDimensional (fourierSpan n)).completeSpace_coe

/-- `fourierSpan n` has an orthogonal projection from `L2C`.
Follows from `CompleteSpace (fourierSpan n)` via the priority-100 instance
`HasOrthogonalProjection.ofCompleteSpace`. -/
instance fourierSpan_hasOrthogonalProjection (n : ℕ) : (fourierSpan n).HasOrthogonalProjection :=
  inferInstance

/-! ### D-29: The n-th Galerkin projection -/

/-- The n-th Galerkin projection: the orthogonal projection of `L2C = L²(𝕋³; ℂ)` onto
the finite-dimensional subspace `fourierSpan n` spanned by Fourier modes with ‖k‖_∞ ≤ n.

Defined as `(fourierSpan n).starProjection : L2C →L[ℂ] L2C`, which is the composition of
`(fourierSpan n).orthogonalProjectionOnto : L2C →L[ℂ] fourierSpan n`
with `(fourierSpan n).subtypeL : fourierSpan n →L[ℂ] L2C`. -/
noncomputable def fourierProjection_n (n : ℕ) : L2C →L[ℂ] L2C :=
  (fourierSpan n).starProjection

/-! ### D-22/combinatorics: Monotonicity and exhaustion of fourierBox (for lean-prover) -/

/-- The Galerkin truncation cubes are monotone: if `m ≤ n` then `fourierBox m ⊆ fourierBox n`. -/
theorem fourierBox_monotone : Monotone fourierBox := by
  intro m n hmn k hk
  simp only [fourierBox, Fintype.mem_piFinset, Finset.mem_Icc] at *
  intro i
  obtain ⟨h1, h2⟩ := hk i
  exact ⟨by linarith [Int.ofNat_le.mpr hmn], by linarith [Int.ofNat_le.mpr hmn]⟩

/-- The fourierBox sets exhaust all of ℤ³: every wavenumber `k` lies in `fourierBox n`
for `n` large enough (namely `n = max_i |k i|`). -/
theorem fourierBox_exhausts : ∀ k : Fin 3 → ℤ, ∃ n : ℕ, k ∈ fourierBox n := by
  intro k
  use Finset.univ.sup (fun i => (k i).natAbs)
  simp only [fourierBox, Fintype.mem_piFinset, Finset.mem_Icc]
  intro i
  have hle : (k i).natAbs ≤ Finset.univ.sup (fun j => (k j).natAbs) :=
    Finset.le_sup (f := fun j => (k j).natAbs) (Finset.mem_univ i)
  constructor
  · have h1 : -(k i) ≤ ↑(-(k i)).natAbs := Int.le_natAbs
    rw [Int.natAbs_neg] at h1
    linarith [Int.ofNat_le.mpr hle]
  · linarith [Int.le_natAbs (a := k i), Int.ofNat_le.mpr hle]

/-! ### D-30a: Monotonicity of fourierSpan (for lean-prover) -/

/-- The Fourier span submodules are monotone: if `m ≤ n` then `fourierSpan m ≤ fourierSpan n`. -/
theorem fourierSpan_monotone : Monotone fourierSpan := by
  intro m n hmn
  apply Submodule.span_mono
  apply Set.image_mono
  exact_mod_cast fourierBox_monotone hmn

/-! ### D-28: Density of the iSup of fourierSpan (for lean-prover) -/

/-- The union of the finite Fourier span submodules is dense in `L2C = L²(𝕋³; ℂ)`:
`(⨆ n, fourierSpan n).topologicalClosure = ⊤`.

Proof outline:
1. `Set.range torus3_mFourierBasis ⊆ ⋃ n, torus3_mFourierBasis '' ↑(fourierBox n)`
   — every basis vector `torus3_mFourierBasis k` lies in `fourierSpan n` for
   `n := max_i |k i|` (by `fourierBox_exhausts`).
2. Hence `span ℂ (Set.range torus3_mFourierBasis) ≤ ⨆ n, fourierSpan n`
   (via `Submodule.span_mono` + `Submodule.iSup_span`).
3. `(⨆ n, fourierSpan n).topologicalClosure ≥ (span ℂ (Set.range torus3_mFourierBasis)).topologicalClosure = ⊤`
   (by `HilbertBasis.dense_span`).

Key mathlib lemmas:
- `HilbertBasis.dense_span` : `(span ℂ (Set.range b)).topologicalClosure = ⊤`
- `Submodule.iSup_span` : `⨆ i, span R (p i) = span R (⋃ i, p i)`
- `Submodule.topologicalClosure_mono` : monotone closure.
- `fourierBox_exhausts` for the index exhaustion. -/
theorem fourierSpan_iSup_dense :
    ⊤ ≤ (⨆ n : ℕ, fourierSpan n).topologicalClosure := by
  -- Step 1: every basis vector lies in some `torus3_mFourierBasis '' ↑(fourierBox n)`.
  have hsub : Set.range torus3_mFourierBasis ⊆
      ⋃ n : ℕ, torus3_mFourierBasis '' ↑(fourierBox n) := by
    rintro _ ⟨k, rfl⟩
    obtain ⟨n, hn⟩ := fourierBox_exhausts k
    exact Set.mem_iUnion.mpr ⟨n, Set.mem_image_of_mem _ hn⟩
  -- Step 2: hence the span of the basis range is below the iSup of the fourierSpans.
  have hspan : Submodule.span ℂ (Set.range torus3_mFourierBasis) ≤ ⨆ n : ℕ, fourierSpan n := by
    simp only [fourierSpan]
    rw [Submodule.iSup_span]
    exact Submodule.span_mono hsub
  -- Step 3: pass to topological closures, using density of the Hilbert basis span.
  calc ⊤ = (Submodule.span ℂ (Set.range torus3_mFourierBasis)).topologicalClosure :=
        torus3_mFourierBasis.dense_span.symm
    _ ≤ (⨆ n : ℕ, fourierSpan n).topologicalClosure :=
        Submodule.topologicalClosure_mono hspan

/-! ### Fourier-multiplier characterisation of fourierProjection_n (for lean-prover) -/

/-- `fourierProjection_n` is the Fourier cutoff: it preserves coefficients inside the box
and kills those outside. This is what makes it the genuine Galerkin/Fourier-truncation
projection (and is the tool for showing it preserves the divergence-free subspace).

Proof strategy for lean-prover:
The orthogonal projection `(fourierSpan n).starProjection f` onto a closed subspace `S`
is the unique element of `S` closest to `f`, and it satisfies the inner-product
characterisation `⟪g, P f⟫ = ⟪g, f⟫` for all `g ∈ S`, and `⟪g, P f⟫ = 0` for `g ∈ Sᗮ`.
Apply this with `g = torus3_mFourierBasis k` (a Hilbert basis vector):
- If `k ∈ fourierBox n`, then `torus3_mFourierBasis k ∈ fourierSpan n = S`,
  so `mFourierCoeff3 (P f) k = ⟪torus3_mFourierBasis k, P f⟫ = ⟪torus3_mFourierBasis k, f⟫
  = mFourierCoeff3 f k`.
- If `k ∉ fourierBox n`, then `torus3_mFourierBasis k ⊥ fourierSpan n` by
  orthonormality of the Hilbert basis (`HilbertBasis.orthonormal`), so
  `mFourierCoeff3 (P f) k = ⟪torus3_mFourierBasis k, P f⟫ = 0`.
Key mathlib lemmas: `Submodule.inner_orthogonalProjection_eq_of_mem`,
`Submodule.inner_orthogonalProjection_eq_zero_of_not_mem` (or the
`orthogonalProjection`/`starProjection` inner-product API),
`HilbertBasis.repr_apply_apply`, `HilbertBasis.orthonormal`. -/
theorem fourierProjection_n_mFourierCoeff (n : ℕ) (f : L2C) (k : Fin 3 → ℤ) :
    mFourierCoeff3 (fourierProjection_n n f) k =
      if k ∈ fourierBox n then mFourierCoeff3 f k else 0 := by
  -- Rewrite both coefficients as inner products against the basis vector, and move the
  -- projection onto the basis vector using self-adjointness of `starProjection`.
  simp only [mFourierCoeff3, HilbertBasis.repr_apply_apply, fourierProjection_n,
    ← Submodule.inner_starProjection_left_eq_right]
  by_cases hk : k ∈ fourierBox n
  · -- Inside the box: the basis vector lies in the span, so the projection fixes it.
    have hbk : torus3_mFourierBasis k ∈ fourierSpan n :=
      Submodule.subset_span (Set.mem_image_of_mem _ (Finset.mem_coe.mpr hk))
    rw [if_pos hk, Submodule.starProjection_eq_self_iff.mpr hbk]
  · -- Outside the box: the basis vector is orthogonal to the span, so it projects to 0.
    have hmem : torus3_mFourierBasis k ∈ (fourierSpan n)ᗮ := by
      have h1 : Submodule.span ℂ {torus3_mFourierBasis k} ⟂ fourierSpan n := by
        rw [fourierSpan, Submodule.isOrtho_span]
        rintro u hu v ⟨j, hj, rfl⟩
        rw [Set.mem_singleton_iff] at hu
        subst hu
        refine torus3_mFourierBasis.orthonormal.2 fun hkj => hk ?_
        rw [hkj]
        exact hj
      exact h1.le (Submodule.mem_span_singleton_self _)
    rw [if_neg hk, (Submodule.starProjection_apply_eq_zero_iff (fourierSpan n)).mpr hmem,
      inner_zero_left]

/-! ### D-30: Convergence of Galerkin projections (for lean-prover) -/

/-- The Galerkin projections `fourierProjection_n n f` converge to `f` in `L2C` as `n → ∞`.

Proof: apply `Submodule.starProjection_tendsto_self` with:
- `U = fourierSpan` (the monotone family, by `fourierSpan_monotone`),
- `[∀ n, (fourierSpan n).HasOrthogonalProjection]` (instance, from D-27),
- `fourierSpan_iSup_dense` (the density condition, D-28).

Key mathlib lemma:
`Submodule.starProjection_tendsto_self :
  Monotone U → (∀ t, (U t).HasOrthogonalProjection) → ⊤ ≤ (⨆ t, U t).topologicalClosure →
  Filter.Tendsto (fun t => (U t).starProjection x) atTop (𝓝 x)` -/
theorem fourierProjection_n_tendsto (f : L2C) :
    Filter.Tendsto (fun n => fourierProjection_n n f) atTop (nhds f) := by
  simp only [fourierProjection_n]
  exact Submodule.starProjection_tendsto_self fourierSpan fourierSpan_monotone f
    fourierSpan_iSup_dense

/-- The squared Fourier coefficients of any `f : L2C` are summable (from `lp` membership).

Hoisted here (from `GalerkinODESolve.lean`, issue #111 PR-5) so downstream files that need it
without the ODE-solver machinery (e.g. `EnergyConvection.lean`) can reach it via this file's
generic Galerkin-projection layer instead of each keeping its own restatement. -/
theorem summable_norm_mFourierCoeff3_sq (f : L2C) :
    Summable (fun k : Fin 3 → ℤ => ‖mFourierCoeff3 f k‖ ^ 2) := by
  have hmem : Memℓp (torus3_mFourierBasis.repr f) 2 := (torus3_mFourierBasis.repr f).2
  have hp : (0 : ℝ) < (2 : ENNReal).toReal := by norm_num
  have := (memℓp_gen_iff hp).mp hmem
  refine this.congr (fun k => ?_)
  rw [show ((2 : ENNReal).toReal) = (2 : ℝ) by norm_num, Real.rpow_two]
  rfl

end LerayHopf
