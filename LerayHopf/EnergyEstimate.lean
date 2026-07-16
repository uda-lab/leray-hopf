import LerayHopf.EnergySkeleton
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Abstract energy-law framework (M4)

This file develops the abstract energy identity and inequality for a curve
`u : ℝ → H` in a real inner product space `H`, building on the abstract
`EnergyInequality` and `EnergyData` from `LerayHopf.EnergySkeleton`.

## Mathematical content

The key computation: if `u` satisfies the abstract energy law

  inner (u' t) (u t) + D (u t) + B (u t) (u t) (u t) = 0

with trilinear skew-symmetry `B w w w = 0`, then the skew-symmetric term
vanishes and `d/dt (half * norm u t ^ 2) = - D (u t)`.

Integrating gives the energy inequality, which is packaged as an
`EnergyInequality` instance (closing the loop to `EnergySkeleton`).

## Mathlib API map (for lean-prover)

The lean-prover will use the following confirmed mathlib lemmas:
- `HasDerivAt.norm_sq`   (Mathlib.Analysis.InnerProductSpace.Calculus):
    HasDerivAt f f' x → HasDerivAt (‖f ·‖²) (2 * ⟪f x, f'⟫) x
- `HasDerivAt.inner`    (Mathlib.Analysis.InnerProductSpace.Calculus):
    HasDerivAt f f' x → HasDerivAt g g' x →
      HasDerivAt (fun t => ⟪f t, g t⟫) (⟪f x, g'⟫ + ⟪f', g x⟫) x
- `intervalIntegral.integral_eq_sub_of_hasDerivAt`
    (Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus):
    FTC-2 for ℝ → E valued functions
- `intervalIntegral.integral_nonneg_of_forall`
    (Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic):
    `a ≤ b → (∀ u, 0 ≤ f u) → 0 ≤ ∫ u in a..b, f u`
- `energy_nonincreasing_from_nonnegative_dissipation` (LerayHopf.EnergySkeleton)
- `linarith`, `ring`    (built-in)

## Tier-2 frontier

The concrete Navier-Stokes realization — defining the convective trilinear form
`b(u,v,w) = integral over torus of inner ((u dot grad) v) w`, proving
`b(u,u,u) = 0` by integration by parts, and constructing the Galerkin ODE
(finite-dimensional projected ODE on `L²_σ(𝕋³)`, Picard–Lindelöf, concrete
nonlinear cancellation `b(u,u,u) = 0`) — requires infrastructure absent from
mathlib (torus divergence theorem, Lp-level gradient operators).
See `docs/scratch/m4-energy.md` Section 2 for details.

The theorems below state the abstract energy law directly as hypotheses on a
curve `u : ℝ → H`; they are the honest interface that any such concrete
construction must supply.

## Assumptions

No `axiom`, `constant`, `opaque`, or `unsafe` declarations are added.
All incomplete proof bodies carry `-- ALLOW_SORRY: <reason>`.
-/

open MeasureTheory

namespace LerayHopf

/-! The abstract Galerkin ODE law for a curve `u : ℝ → H` with dissipation `D : H → ℝ`
and trilinear form `B : H → H → H → ℝ` is:
`∀ t, HasDerivAt u (deriv u t) t ∧ inner (deriv u t) (u t) + D (u t) + B (u t) (u t) (u t) = 0`.
This is stated directly as a hypothesis in the theorems below rather than bundled into a
standalone structure, which would make the explicit `@` form verbose. -/

/-! ## Section 2: Abstract Galerkin energy identity -/

/-- **Abstract Galerkin energy identity.**

Given a curve `u : ℝ → H` in a real inner product space satisfying the abstract
Galerkin energy law (the inner-product form of the projected ODE), with trilinear
skew-symmetry `B w w w = 0` killing the nonlinear term, the kinetic energy
`(1/2) * ‖u(t)‖²` has derivative `- D(u(t))` at every `t`.

Proof sketch for lean-prover:
1. `HasDerivAt.norm_sq` applied to `(hODE t).1` gives
   `HasDerivAt (‖u ·‖²) (2 * ⟪u t, deriv u t⟫) t`.
2. The ODE law `(hODE t).2` gives
   `⟪deriv u t, u t⟫ = - D(u t) - B(u t)(u t)(u t)`.
3. `hB` gives `B(u t)(u t)(u t) = 0`, so `⟪deriv u t, u t⟫ = - D(u t)`.
4. Inner product symmetry: `⟪u t, deriv u t⟫ = ⟪deriv u t, u t⟫`
   (via `real_inner_comm` or `inner_comm`).
5. Scale by `1/2` using `HasDerivAt.inner` with the constant function `1/2`
   (since `HasDerivAt.const_mul` is outside the import closure of this file),
   then rewrite the resulting function and derivative value with `ring`. -/
theorem abstract_galerkin_energy_identity
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (u   : ℝ → H)
    (D   : H → ℝ)
    (B   : H → H → H → ℝ)
    (hB  : ∀ w : H, B w w w = 0)
    (hODE : ∀ t : ℝ,
        HasDerivAt u (deriv u t) t ∧
        inner (𝕜 := ℝ) (deriv u t) (u t) + D (u t) + B (u t) (u t) (u t) = 0)
    (t   : ℝ) :
    HasDerivAt (fun s => (1 / 2 : ℝ) * ‖u s‖ ^ 2) (- D (u t)) t := by
  obtain ⟨hderiv, hlaw⟩ := hODE t
  -- d/dt ‖u t‖² = 2 ⟪u t, u' t⟫  (HasDerivAt.norm_sq)
  have h1 : HasDerivAt (fun s => ‖u s‖ ^ 2)
      (2 * inner (𝕜 := ℝ) (u t) (deriv u t)) t := hderiv.norm_sq
  -- Scale by 1/2 via `HasDerivAt.inner` with the constant function `1/2`
  -- (`HasDerivAt.const_mul` is outside the import closure of this file).
  have h2' := (hasDerivAt_const t (1 / 2 : ℝ)).inner (𝕜 := ℝ) h1
  simp at h2'
  -- h2' : HasDerivAt (fun s => ‖u s‖ ^ 2 * 2⁻¹) (2 * ⟪u t, deriv u t⟫_ℝ * 2⁻¹) t
  have hfun : (fun s => ‖u s‖ ^ 2 * 2⁻¹) = fun s => (1 / 2 : ℝ) * ‖u s‖ ^ 2 := by
    funext s; ring
  -- identify the derivative value via the ODE law and skew-symmetry
  have hval : (2 : ℝ) * inner (𝕜 := ℝ) (u t) (deriv u t) * 2⁻¹ = - D (u t) := by
    have hB' := hB (u t)
    rw [real_inner_comm]
    linarith
  rw [hfun, hval] at h2'
  exact h2'

/-! ## Section 3: Abstract Galerkin energy inequality -/

/-- **Abstract Galerkin energy inequality.**

Integrating the energy identity over `[s, t]` via FTC-2 gives the energy
inequality: `(1/2) * ‖u(t)‖² + ∫_s^t D(u(τ)) dτ ≤ (1/2) * ‖u(s)‖²`.

The equality `d/dt (half * ‖u‖²) = - D(u)` from `abstract_galerkin_energy_identity`
makes the integral an equality; the `≤` form matches `EnergyInequality`.

Proof sketch for lean-prover:
1. Apply `intervalIntegral.integral_eq_sub_of_hasDerivAt` with
   `f := fun s => (1/2) * ‖u s‖²` and `f' := fun τ => - D(u τ)`, using
   `abstract_galerkin_energy_identity` for the `HasDerivAt` hypothesis.
   The integrability follows from `hint` and `IntervalIntegrable.neg`.
2. This gives `∫ τ in s..t, - D(u τ) = (1/2) * ‖u t‖² - (1/2) * ‖u s‖²`.
3. Rewrite via `intervalIntegral.integral_neg`:
   `- ∫ τ in s..t, D(u τ) = (1/2) * ‖u t‖² - (1/2) * ‖u s‖²`.
4. Rearrange with `linarith`. -/
theorem abstract_galerkin_energy_inequality
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (u   : ℝ → H)
    (D   : H → ℝ)
    (B   : H → H → H → ℝ)
    (hB  : ∀ w : H, B w w w = 0)
    (hODE : ∀ t : ℝ,
        HasDerivAt u (deriv u t) t ∧
        inner (𝕜 := ℝ) (deriv u t) (u t) + D (u t) + B (u t) (u t) (u t) = 0)
    (hint : ∀ a b : ℝ, IntervalIntegrable (fun τ => D (u τ)) volume a b)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    (1 / 2 : ℝ) * ‖u t‖ ^ 2 + ∫ τ in s..t, D (u τ) ≤ (1 / 2 : ℝ) * ‖u s‖ ^ 2 := by
  -- pointwise derivative of the energy, from the energy identity
  have hderiv : ∀ τ ∈ Set.uIcc s t,
      HasDerivAt (fun r => (1 / 2 : ℝ) * ‖u r‖ ^ 2) (- D (u τ)) τ :=
    fun τ _ => abstract_galerkin_energy_identity u D B hB hODE τ
  -- integrability of the (negated) dissipation
  have hint' : IntervalIntegrable (fun τ => - D (u τ)) volume s t := (hint s t).neg
  -- FTC-2: ∫ -D(u) = ½‖u t‖² - ½‖u s‖²
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint'
  rw [intervalIntegral.integral_neg] at hFTC
  -- `hs`, `hst` are not needed: FTC-2 already covers `uIcc s t`
  have _hs := hs
  have _hst := hst
  linarith

/-! ## Section 4: Connection to EnergySkeleton -/

/-- **Abstract Galerkin approximation satisfies `EnergyInequality`.**

Under the same hypotheses as `abstract_galerkin_energy_inequality`, the explicit
`EnergyData` with

    E t    := (1/2) * ‖u t‖²
    A s t  := ∫ τ in s..t, D(u τ)
    ν      := 1

satisfies the abstract `EnergyInequality` from `LerayHopf.EnergySkeleton`.

This closes the loop: `energy_nonincreasing_from_nonnegative_dissipation` then
gives `E t ≤ E s` for `0 ≤ s ≤ t`, provided `D ≥ 0`.

Proof sketch for lean-prover:
Unfold `EnergyInequality`, introduce `s t hs hst`, apply
`abstract_galerkin_energy_inequality`, and simplify `1 * A = A` via `one_mul`. -/
theorem abstract_galerkin_satisfies_EnergyInequality
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (u : ℝ → H)
    (D : H → ℝ)
    (B : H → H → H → ℝ)
    (hB  : ∀ w : H, B w w w = 0)
    (hODE : ∀ t : ℝ,
        HasDerivAt u (deriv u t) t ∧
        inner (𝕜 := ℝ) (deriv u t) (u t) + D (u t) + B (u t) (u t) (u t) = 0)
    (hint : ∀ a b : ℝ, IntervalIntegrable (fun τ => D (u τ)) volume a b) :
    EnergyInequality {
      E := fun t => (1 / 2 : ℝ) * ‖u t‖ ^ 2
      A := fun s t => ∫ τ in s..t, D (u τ)
      ν := 1
    } := by
  intro s t hs hst
  have h := abstract_galerkin_energy_inequality u D B hB hODE hint hs hst
  simp only [one_mul]
  linarith

/-! ## Section 5: Abstract dissipative-energy-law interface — AbstractEnergyLaw -/

/-- **Abstract dissipative-energy-law interface for an evolution problem on `H`.**

This is the ABSTRACT interface: a curve `u : ℝ → H` obeying a skew-symmetric
energy balance — it contains only an abstract scalar energy law (curve `u`,
dissipation `D`, skew form `B`, and the scalar balance `ode_law`).  It has NO
finite-dimensional approximation space, NO projection operator, NO initial datum,
and NO concrete Galerkin ODE.

A genuine Galerkin construction — finite-dimensional projected ODE on `L²_σ(𝕋³)`,
existence via Picard–Lindelöf, and concrete nonlinear cancellation `b(u,u,u) = 0`
from skew-symmetry of the convection form — is what WOULD supply such a law.
That construction requires torus convection/Stokes infrastructure absent from
mathlib (torus divergence theorem, Lp-level gradient operators, projected ODE
on `Pₙ(L²_σ)`) and is NOT done here.  This is a frontier item; see
`docs/STATUS.md` for current status.

This structure packages the hypotheses that any such concrete construction must
supply in order for the abstract energy framework (Sections 1-4) to apply. -/
structure AbstractEnergyLaw (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] where
  /-- The Galerkin solution curve. -/
  u   : ℝ → H
  /-- Pointwise dissipation form (e.g. `ν ‖∇u(t)‖²` at `u(t)`). -/
  D   : H → ℝ
  /-- Nonnegativity of dissipation. -/
  D_nonneg : ∀ w : H, 0 ≤ D w
  /-- Abstract trilinear form (the role of the convective nonlinearity). -/
  B   : H → H → H → ℝ
  /-- Skew-symmetry of the trilinear form on the diagonal. -/
  B_skew : ∀ w : H, B w w w = 0
  /-- `u` is differentiable with derivative `deriv u t` at every `t`. -/
  hasDeriv : ∀ t : ℝ, HasDerivAt u (deriv u t) t
  /-- Abstract inner-product form of the Galerkin ODE at each time `t`. -/
  ode_law : ∀ t : ℝ,
      inner (𝕜 := ℝ) (deriv u t) (u t) + D (u t) + B (u t) (u t) (u t) = 0
  /-- `D ∘ u` is interval integrable on every interval. -/
  D_intble : ∀ a b : ℝ, IntervalIntegrable (fun τ => D (u τ)) volume a b

/-! ## Section 6: Capstone — AbstractEnergyLaw satisfies EnergyInequality and bridges to EnergySkeleton -/

/-- **Capstone: every `AbstractEnergyLaw` satisfies `EnergyInequality`.**

Applies `abstract_galerkin_satisfies_EnergyInequality` to the fields of an
`AbstractEnergyLaw`, yielding `EnergyInequality` for
`E t = (1/2) * ‖u t‖²`, `A s t = ∫_s^t D(u τ) dτ`, `ν = 1`.

Together with `energy_nonincreasing_from_nonnegative_dissipation` and
`g.D_nonneg`, this gives `‖u t‖ ≤ ‖u s‖` for `0 ≤ s ≤ t` — the uniform
energy bound feeding the M5 compactness argument.

Proof sketch for lean-prover:
Apply `abstract_galerkin_satisfies_EnergyInequality` with
`hODE t := ⟨g.hasDeriv t, g.ode_law t⟩`, `hB := g.B_skew`,
`hint := g.D_intble`. -/
theorem AbstractEnergyLaw.energyInequality
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (g : AbstractEnergyLaw H) :
    EnergyInequality {
      E := fun t => (1 / 2 : ℝ) * ‖g.u t‖ ^ 2
      A := fun s t => ∫ τ in s..t, g.D (g.u τ)
      ν := 1
    } :=
  abstract_galerkin_satisfies_EnergyInequality g.u g.D g.B g.B_skew
    (fun t => ⟨g.hasDeriv t, g.ode_law t⟩) g.D_intble

/-- **Nonneg accumulated dissipation for `AbstractEnergyLaw`.**

The integral `∫ τ in s..t, g.D (g.u τ)` is nonneg for `0 ≤ s ≤ t`,
since `g.D_nonneg` gives pointwise nonnegativity.

Proof sketch for lean-prover:
Apply `intervalIntegral.integral_nonneg_of_forall` with `hab := hst` and
`hf := fun τ => g.D_nonneg (g.u τ)`. -/
theorem AbstractEnergyLaw.accumulatedDissipation_nonneg
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (g : AbstractEnergyLaw H) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    0 ≤ ∫ τ in s..t, g.D (g.u τ) := by
  -- `hs` is part of the stated interface (positivity of the start time) but is
  -- not needed for nonnegativity of the integral itself.
  have _hs := hs
  exact intervalIntegral.integral_nonneg_of_forall hst fun τ => g.D_nonneg (g.u τ)

/-- **Energy is nonincreasing for `AbstractEnergyLaw`.**

For `0 ≤ s ≤ t`, the kinetic energy satisfies
`(1/2) * ‖g.u t‖² ≤ (1/2) * ‖g.u s‖²`.

This follows from `energy_nonincreasing_from_nonnegative_dissipation` applied to
the `EnergyData` produced by `g.energyInequality`, using `ν = 1 ≥ 0` and
`accumulatedDissipation_nonneg`.

Proof sketch for lean-prover:
Let `ed := { E := fun t => (1/2) * ‖g.u t‖², A := fun s t => ∫ τ in s..t, g.D (g.u τ), ν := 1 }`.
Apply `energy_nonincreasing_from_nonnegative_dissipation ed g.energyInequality
  (by norm_num) (fun s t hs hst => g.accumulatedDissipation_nonneg hs hst) s t hs hst`. -/
theorem AbstractEnergyLaw.energy_nonincreasing
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (g : AbstractEnergyLaw H) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    (1 / 2 : ℝ) * ‖g.u t‖ ^ 2 ≤ (1 / 2 : ℝ) * ‖g.u s‖ ^ 2 := by
  exact energy_nonincreasing_from_nonnegative_dissipation
    { E := fun t => (1 / 2 : ℝ) * ‖g.u t‖ ^ 2
      A := fun s t => ∫ τ in s..t, g.D (g.u τ)
      ν := 1 }
    g.energyInequality (by norm_num)
    (fun s t hs hst => g.accumulatedDissipation_nonneg hs hst) s t hs hst

end LerayHopf
