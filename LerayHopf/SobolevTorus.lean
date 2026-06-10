import LerayHopf.FunctionSpaces
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Sobolev space H¹(𝕋³; ℂ) — Fourier characterization

**M2 — D-11 (scaffold).**

This file defines membership in the order-1 Sobolev space H¹(𝕋³; ℂ) via the
Fourier-coefficient weight condition.  The definition is a `Prop`-valued predicate
on `L2C = Lp ℂ 2 haarTorus3`; no Hilbert-space structure or compact-embedding
result is proved here (those are M5–M6).

## Definition

A function `f ∈ L²(𝕋³; ℂ)` belongs to `H¹(𝕋³)` iff

  `∑_{k ∈ ℤ³} (1 + ‖k‖²) · |f̂(k)|² < ∞`,

where `f̂(k) = mFourierCoeff3 f k` is the k-th Fourier coefficient and
`‖k‖² = ∑_i (k_i : ℝ)²` is the squared Euclidean norm of the frequency vector.

## Note on mathlib's Sobolev API

`MeasureTheory.MemSobolev` / `TemperedDistribution` work on `ℝⁿ` and are not
available for compact tori.  This file builds the torus Sobolev predicate directly
from the Fourier characterization, which is the standard approach in PDE Lean
formalizations.
-/

namespace LerayHopf

/-! ### D-11: H¹(𝕋³; ℂ) membership predicate -/

/-- Membership in H¹(𝕋³; ℂ): a function `f ∈ L²(𝕋³; ℂ)` lies in the order-1 Sobolev space
iff its Fourier coefficients are square-summable against the weight `1 + ‖k‖²`:
`∑_k (1 + ∑_i (k_i)²) · ‖f̂(k)‖² < ∞`.

Scaffold (M2): mathlib has no torus Sobolev API (`TemperedDistribution.memSobolev` is ℝⁿ only),
so this is built from the Fourier characterization. The H¹-inner-product Hilbert structure and
the compact embedding H¹ ↪ L² (Rellich) are deferred to M5–M6. -/
noncomputable def memH1Torus (f : L2C) : Prop :=
  Summable (fun k : Fin 3 → ℤ =>
    (1 + ∑ i : Fin 3, (k i : ℝ) ^ 2) * ‖mFourierCoeff3 f k‖ ^ 2)

/-- The torus Sobolev space H¹(𝕋³; ℂ) as a subset of L²(𝕋³; ℂ). -/
def H1Torus : Set L2C := {f | memH1Torus f}

/-! ### Sanity check: the zero function lies in H¹(𝕋³) -/

/-- The zero function is in H¹(𝕋³; ℂ), confirming the predicate is non-vacuous. -/
theorem memH1Torus_zero : memH1Torus 0 := by
  show Summable fun k : Fin 3 → ℤ =>
      (1 + ∑ i : Fin 3, (k i : ℝ) ^ 2) * ‖mFourierCoeff3 (0 : L2C) k‖ ^ 2
  have heq : (fun k : Fin 3 → ℤ =>
      (1 + ∑ i : Fin 3, (k i : ℝ) ^ 2) * ‖mFourierCoeff3 (0 : L2C) k‖ ^ 2) =
      fun _ => (0 : ℝ) := by
    funext k
    simp [mFourierCoeff3, torus3_mFourierBasis, map_zero]
  rw [heq]
  exact summable_zero

end LerayHopf
