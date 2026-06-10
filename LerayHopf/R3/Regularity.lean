import LerayHopf.R3.DivergenceFree
import Mathlib.Analysis.Distribution.Sobolev
import Mathlib.Analysis.Fourier.LpSpace

open MeasureTheory FourierTransform TemperedDistribution
open scoped FourierTransform SchwartzMap

/-!
# ℝ³ regularity predicate, Sobolev H¹ membership, and viscous pairing

**R3-b — Regularity.**

This file builds five items for the ℝ³ Leray–Hopf theory:

1. `IsSchwartzDivFree_R3`     — Schwartz divergence-free test class (the subset of
   `L2Sigma_R3` that lifts to a component-wise Schwartz representative).

2. `memH1VF_R3`               — H¹ membership via `TemperedDistribution.MemSobolev 1 2`
   applied to the complex-valued component (coerced to `𝓢'(Domain3, ℂ)`).

3. `stokesTestPairing_R3`     — symmetric viscous pairing defined via the Fourier-integral
   formula (the ℝ³ analogue of the T³ `stokesTestPairing`).

4. `viscousFormSq_R3`         — viscous dissipation `ν‖∇u‖²` via the spectral formula.

5. `viscousFormSq_R3_nonneg`  — nonnegativity when `ν ≥ 0`.

## Design notes

### Item 1 — `IsSchwartzDivFree_R3`
Defined component-wise: `w` has a Schwartz representative iff each projected
component `L2VF_projComponent_R3 j w` equals `(ψ j).toLp 2 volume` for some scalar
Schwartz map `ψ j : 𝓢(Domain3, ℝ)`.

### Item 2 — `memH1VF_R3`
Uses the **complex-valued** component `L2VF_projComponentC_R3 j u : L2C_R3` which
coerces to `𝓢'(Domain3, ℂ)` via `Lp.instCoeDep`.  `MemSobolev 1 2` is then applied
in the Sobolev.lean `normed` section, which requires `[NormedSpace ℂ F]` — satisfied
for `F = ℂ`.  The real component `Lp ℝ 2 volume` would need a `[NormedSpace ℂ ℝ]`
instance (restriction of scalars) that mathlib does not provide as a bare instance, so
the complex route is the correct one.

### Items 3–5 — Fourier-integral definitions
`stokesTestPairing_R3` and `viscousFormSq_R3` are defined via the
**Bochner integral in the spectral domain**:

  `stokesTestPairing_R3 u w = ∑ j, ∫ ξ, (2π)² ‖ξ‖² · Re[(𝓕 uⱼ ξ) · conj(𝓕 wⱼ ξ)] dξ`

where `uⱼ = L2VF_projComponentC_R3 j u : L2C_R3` and `𝓕` is the `L2`-Fourier
transform `Lp.fourierTransformₗᵢ Domain3 ℂ` (via the `instFourierTransform`
typeclass instance, which gives `𝓕 : L2C_R3 → L2C_R3`).

`(𝓕 f) ξ` uses the `Lp.instCoeFun` pointwise coercion of the a.e. class.  Since
`Lp` integrals are defined as Bochner integrals (returning 0 on non-integrable
integrands), the definition is unconditional — the energy class is enforced
separately in R3-c.

The `(2π)²` factor matches the `e^{2πi ξ·x}` convention: `∂_xᵢ e^{2πi ξ·x}` contributes
`(2π ξᵢ)²`, so `∑ j ∫ (2π)² ‖ξ‖² |𝓕 uⱼ ξ|² dξ = ‖∇u‖²_{L²(ℝ³)}`.

## Main definitions

- `IsSchwartzDivFree_R3`    : Schwartz divergence-free test predicate on `L2Sigma_R3`
- `memH1VF_R3`              : H¹(ℝ³) membership via `MemSobolev 1 2` on components
- `stokesTestPairing_R3`    : symmetric viscous pairing via Fourier integral (sorry-free)
- `viscousFormSq_R3`        : ν‖∇u‖² via spectral Fourier integral (sorry-free)
- `viscousFormSq_R3_nonneg` : nonnegativity when ν ≥ 0
-/

namespace LerayHopf

/-! ### 1. Schwartz divergence-free test class -/

/-- A vector field `w ∈ L²_σ(ℝ³)` is a **Schwartz divergence-free test function** if each of
its real-valued components `L2VF_projComponent_R3 j (w : L2VF_R3)` is the `L²`-class of a scalar
Schwartz map.

Concretely: `∃ ψ : Fin 3 → 𝓢(Domain3, ℝ)`, `∀ j, L2VF_projComponent_R3 j w = (ψ j).toLp 2 volume`.

This is the component-wise version; it is equivalent (modulo a divergence-free check on `ψ`) to
having a single vector-valued Schwartz representative, but avoids the awkward vector-valued
`toLp` coercion. -/
def IsSchwartzDivFree_R3 (w : L2Sigma_R3) : Prop :=
  ∃ ψ : Fin 3 → SchwartzMap Domain3 ℝ,
    ∀ j : Fin 3,
      L2VF_projComponent_R3 j (w : L2VF_R3) =
        (ψ j).toLp 2 (volume : Measure Domain3)

/-! ### 2. H¹ membership via MemSobolev -/

/-- A velocity field `u ∈ L²(ℝ³; ℝ³)` has **H¹ regularity** if each complex-valued component
`L2VF_projComponentC_R3 j u : L2C_R3 = Lp ℂ 2 volume` lies in the Sobolev space `H^{1,2}(ℝ³; ℂ)`.

We use the **complex-valued** component projection `L2VF_projComponentC_R3 j` (rather than the
real-valued `L2VF_projComponent_R3 j`) because:
- `L2C_R3 = Lp ℂ 2 volume` carries a `CoeDep` instance to `𝓢'(Domain3, ℂ)`;
- `MemSobolev` requires `[NormedSpace ℂ F]`, which holds for `F = ℂ` but requires an extra
  restriction-of-scalars instance for `F = ℝ`.

The coercion `(f : 𝓢'(Domain3, ℂ))` for `f : L2C_R3` is via `Lp.instCoeDep`. -/
def memH1VF_R3 (u : L2VF_R3) : Prop :=
  ∀ j : Fin 3,
    TemperedDistribution.MemSobolev 1 2
      (L2VF_projComponentC_R3 j u : 𝓢'(Domain3, ℂ))

/-! ### 3–5. Viscous forms via Fourier integral -/

/-- The **viscous (Stokes) test-slot pairing** on `L²(ℝ³; ℝ³)`, defined via the Fourier
integral formula (the ℝ³ analogue of the T³ `stokesTestPairing`):

  `stokesTestPairing_R3 u w = ∑ j, ∫ ξ, (2π)² ‖ξ‖² · Re[(𝓕 uⱼ ξ) · conj(𝓕 wⱼ ξ)] dξ`

where `uⱼ = L2VF_projComponentC_R3 j u : L2C_R3` and `𝓕` is applied via the
`MeasureTheory.Lp.instFourierTransform` typeclass instance
(`Lp.fourierTransformₗᵢ Domain3 ℂ`).

The pointwise value `(𝓕 f) ξ` uses the `Lp.instCoeFun` a.e. representative coercion.
The integral is the Bochner integral on `Domain3` with the Lebesgue `volume` measure;
on non-integrable integrands it returns 0 (the standard mathlib convention).

This definition is **sorry-free**: no Fourier-multiplier operator or `smulLeftCLM`
apparatus is needed.  The diagonal recovers `viscousFormSq_R3 1 u`. -/
noncomputable def stokesTestPairing_R3 (u w : L2VF_R3) : ℝ :=
  ∑ j : Fin 3, ∫ ξ : Domain3,
    (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 *
      ((𝓕 (L2VF_projComponentC_R3 j u) : L2C_R3) ξ *
        (starRingEnd ℂ) ((𝓕 (L2VF_projComponentC_R3 j w) : L2C_R3) ξ)).re
    ∂(volume : Measure Domain3)

/-- The **viscous dissipation form** `ν * ‖∇u‖²_{L²}` defined via the spectral formula:

  `viscousFormSq_R3 ν u = ν * ∑ j, ∫ ξ, (2π)² ‖ξ‖² · ‖(𝓕 uⱼ) ξ‖² dξ`

This is the ℝ³ analogue of the T³ `viscousFormSq`, with the Fourier series replaced by
the continuous Fourier transform integral.  The `(2π)²` factor arises from the
`e^{2πi ξ·x}` convention.

The definition is unconditional (Bochner integral returns 0 for non-integrable
integrands); the H¹ energy class is enforced separately. -/
noncomputable def viscousFormSq_R3 (ν : ℝ) (u : L2VF_R3) : ℝ :=
  ν * ∑ j : Fin 3, ∫ ξ : Domain3,
    (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 * ‖(𝓕 (L2VF_projComponentC_R3 j u) : L2C_R3) ξ‖ ^ 2
    ∂(volume : Measure Domain3)

/-- The viscous dissipation form is nonneg when `ν ≥ 0`.

Proof: `mul_nonneg hν` reduces to the sum being nonneg; `Finset.sum_nonneg` reduces to
each integral being nonneg; `integral_nonneg` reduces to the pointwise integrand being
nonneg, which follows by `positivity` (product of squares and (2π)²). -/
theorem viscousFormSq_R3_nonneg {ν : ℝ} (hν : 0 ≤ ν) (u : L2VF_R3) :
    0 ≤ viscousFormSq_R3 ν u := by
  apply mul_nonneg hν
  apply Finset.sum_nonneg
  intro j _
  apply integral_nonneg
  intro ξ
  positivity

end LerayHopf
