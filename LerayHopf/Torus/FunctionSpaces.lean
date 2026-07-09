import LerayHopf.Torus.Domain
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Analysis.Fourier.AddCircleMulti

open MeasureTheory

/-!
# Function spaces for the Leray–Hopf formalization

**M2 — D-04, D-05, D-06, D-07.**

This file defines the L² function spaces and the Fourier Hilbert basis that serve as the
analytical foundation for the Leray–Hopf weak-solution theory on the 3-torus.

## L² spaces

- `L2VF`  : `L²(𝕋³; ℝ³)` — Bochner L² space of ℝ³-valued velocity fields.
- `L2C`   : `L²(𝕋³; ℂ)` — complex scalar L² space, used for Fourier expansions.

## Single-measure design

All L² spaces use the single canonical measure `haarTorus3` defined in `TorusDomain.lean`,
equal to `Measure.pi (fun _ : Fin 3 => AddCircle.haarAddCircle)`.  This is the measure
under which `UnitAddTorus.mFourierBasis` is a Hilbert basis (via the local instance in
`AddCircleMulti` which sets `volume = haarAddCircle` on `UnitAddCircle`).  The global
`volume : Measure Torus3` equals `haarTorus3` propositionally; the bridge lemma
`volume_torus3_eq_haarTorus3` in `TorusDomain.lean` records this.
-/

namespace LerayHopf

/-! ### D-04: L²(𝕋³; ℝ³) -/

/-- L²(𝕋³; ℝ³) — the Bochner L² space of ℝ³-valued velocity fields on the 3-torus,
with respect to the canonical Haar product measure `haarTorus3`.

Used as the ambient space for velocity fields; instances `NormedAddCommGroup`,
`CompleteSpace`, and `InnerProductSpace ℝ` all fire from `Lp` + `L2.innerProductSpace`. -/
noncomputable abbrev L2VF := Lp VelocityValue 2 haarTorus3

-- D-04 instance checks (must typecheck, not named theorems):
noncomputable example : NormedAddCommGroup L2VF := inferInstance
noncomputable example : CompleteSpace L2VF := inferInstance
noncomputable example : InnerProductSpace ℝ L2VF := inferInstance

/-! ### D-05: L²(𝕋³; ℂ) -/

/-- L²(𝕋³; ℂ) — complex scalar L² space with respect to `haarTorus3`.

Used as the ambient space for scalar Fourier modes; velocity components embed here via
`Complex.ofReal` (the `IsROrC.ofReal` embedding).  Uses `haarTorus3` so that
`torus3_mFourierBasis := UnitAddTorus.mFourierBasis` typechecks without sorry: both
`L2C` and `mFourierBasis` use `Measure.pi (fun _ : Fin 3 => AddCircle.haarAddCircle)`. -/
noncomputable abbrev L2C := Lp ℂ 2 haarTorus3

-- D-05 instance checks (must typecheck, not named theorems):
noncomputable example : NormedAddCommGroup L2C := inferInstance
noncomputable example : CompleteSpace L2C := inferInstance
noncomputable example : InnerProductSpace ℂ L2C := inferInstance

/-! ### D-06: Fourier Hilbert basis for L²(𝕋³; ℂ) -/

/-- The ℤ³-indexed Fourier Hilbert basis for L²(𝕋³; ℂ).

This is `UnitAddTorus.mFourierBasis` instantiated at `d = Fin 3`.  The definition typechecks
without sorry because `L2C` uses `haarTorus3 = Measure.pi (fun _ : Fin 3 => AddCircle.haarAddCircle)`,
which is definitionally equal to the measure used by `mFourierBasis` in `AddCircleMulti`
(that file's local instance sets `volume = haarAddCircle` on `UnitAddCircle`, so
`volume` on `UnitAddTorus (Fin 3)` = `Measure.pi (fun _ => haarAddCircle)` = `haarTorus3`). -/
noncomputable def torus3_mFourierBasis : HilbertBasis (Fin 3 → ℤ) ℂ L2C :=
  UnitAddTorus.mFourierBasis

/-! ### D-07: Fourier coefficients for scalar L² functions -/

/-- The k-th Fourier coefficient of a ℂ-valued L²(𝕋³) function, as the `mFourierBasis`
representation coefficient.

`mFourierCoeff3 f k = torus3_mFourierBasis.repr f k`, where `repr` is the isometric
isomorphism from `L2C` to `ℓ²(ℤ³, ℂ)` given by the Hilbert basis. -/
noncomputable def mFourierCoeff3 (f : L2C) (k : Fin 3 → ℤ) : ℂ :=
  torus3_mFourierBasis.repr f k

/-! ### D-08: Parseval identity for L²(𝕋³; ℂ) -/

/-- **Parseval identity.** The squared L²-norm of `f ∈ L²(𝕋³; ℂ)` equals the sum of squared
absolute values of its Fourier coefficients.

Proof:
1. `torus3_mFourierBasis.repr` is a `LinearIsometryEquiv`, so
   `LinearIsometryEquiv.norm_map` gives `‖repr f‖ = ‖f‖`.
2. `repr f : ℓ²(ℤ³, ℂ)`.  `lp.norm_rpow_eq_tsum` at `p = 2` gives
   `‖repr f‖^2 = ∑' k, ‖(repr f) k‖^2`.
3. `mFourierCoeff3 f k = (torus3_mFourierBasis.repr f) k` by `rfl`.
Key mathlib lemmas: `LinearIsometryEquiv.norm_map`, `lp.norm_rpow_eq_tsum`. -/
theorem L2C_norm_sq_eq_tsum_coeff_sq (f : L2C) :
    ‖f‖ ^ 2 = ∑' k : Fin 3 → ℤ, ‖mFourierCoeff3 f k‖ ^ 2 := by
  have hp : 0 < (2 : ENNReal).toReal := by norm_num
  have h := lp.norm_rpow_eq_tsum hp (torus3_mFourierBasis.repr f)
  simp only [ENNReal.toReal_ofNat] at h
  have h2 : ∀ x : ℝ, x ^ (2 : ℝ) = x ^ (2 : ℕ) := fun x => by
    rw [← Real.rpow_natCast x 2]; norm_num
  simp only [h2] at h
  rw [← torus3_mFourierBasis.repr.norm_map f]
  exact h

end LerayHopf
