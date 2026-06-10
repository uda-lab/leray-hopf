import LerayHopf.H1Sigma
import LerayHopf.EnergyEstimate
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open MeasureTheory Filter Topology

/-!
# Abstract dissipative evolution structure and weak NS formulation

**M6 — Commit 1 (foundational layer, zero axioms).**

This file defines the abstract `DissipativeEvolution` bundle — a lightweight real
Hilbert space equipped with regularity, viscous, and convection forms — and the
`WeakFormNS` predicate expressing the weak Navier–Stokes equation.

## Main definitions

- `DissipativeEvolution`  : abstract bundle `(H, reg, viscousForm, convForm)`
- `WeakFormNS ν T E u`    : the weak NS identity for a curve `u : Time → E.H`

## Main theorems

- `DissipativeEvolution.convForm_self_zero` : `E.convForm u u u = 0` (from antisymmetry)

## Assumptions

None beyond mathlib axioms; zero `axiom`/`opaque`/`unsafe` declarations.
-/

namespace LerayHopf

/-! ### Abstract dissipative evolution bundle -/

/-- An abstract **dissipative evolution** on a real Hilbert space.

Carries only what `WeakFormNS` and the energy law need:
- a complete real inner product space `H`,
- a nonneg regularity functional `reg : H → ℝ` (playing the role of ‖·‖²_{H¹}),
- a bilinear viscous form `viscousForm : H → H → ℝ`,
- a trilinear convection form `convForm : H → H → H → ℝ` satisfying antisymmetry.

Galerkin projection, compactness, and concrete T³ constructions are NOT in this
bundle (they belong in the assembly `AxiomaticClosure.lean`, Commit 2). -/
structure DissipativeEvolution where
  /-- The real Hilbert space of velocity fields. -/
  H : Type*
  /-- NormedAddCommGroup instance on `H`. -/
  instNACG : NormedAddCommGroup H
  /-- Real inner product space instance on `H`. -/
  instIPS : InnerProductSpace ℝ H
  /-- Completeness of `H`. -/
  instCS : CompleteSpace H
  /-- Regularity functional (e.g. H¹-norm squared); plays the role of ‖·‖²_{V}. -/
  reg : H → ℝ
  /-- Nonnegativity of the regularity functional. -/
  reg_nonneg : ∀ u, 0 ≤ reg u
  /-- Viscous bilinear form (e.g. ν times the H¹ inner product). -/
  viscousForm : H → H → ℝ
  /-- Convection trilinear form. -/
  convForm : H → H → H → ℝ
  /-- Antisymmetry of the convection form in the last two arguments:
  `b(u, v, w) = -b(u, w, v)`. -/
  convForm_antisymm : ∀ u v w, convForm u v w = - convForm u w v

/-! ### Derived lemma: convForm_self_zero -/

/-- **b(u, u, u) = 0** follows purely from antisymmetry.

Proof: `b(u, u, u) = -b(u, u, u)` by `convForm_antisymm u u u`, so `2 * b(u, u, u) = 0`,
hence `b(u, u, u) = 0`. -/
theorem DissipativeEvolution.convForm_self_zero
    (E : DissipativeEvolution) (u : E.H) :
    E.convForm u u u = 0 := by
  have h := E.convForm_antisymm u u u
  linarith

/-! ### Weak formulation of the Navier–Stokes equations -/

/-- The **weak Navier–Stokes equation** for a curve `u : Time → E.H`.

A curve `u` satisfies the weak NS equation on `(0, T)` with viscosity `ν` iff
for every test function `ψ : Time → ℝ` that is `C¹`, has compact support contained
in the open interval `(0, T)` (so boundary terms vanish), and for every spatial
test vector `w : E.H`, the following integral identity holds:

  `∫ t in 0..T, (-(⟪u t, w⟫_ℝ) * ψ'(t) + ψ(t) * (ν * E.viscousForm (u t) w + E.convForm (u t) (u t) w)) = 0`

The `tsupport ψ ⊆ Set.Ioo 0 T` condition ensures the test function vanishes at the
endpoints, so the integration-by-parts boundary terms are zero (fixing defect 2). -/
def WeakFormNS (ν T : ℝ) (E : DissipativeEvolution) (u : Time → E.H) : Prop :=
  letI := E.instNACG
  letI := E.instIPS
  ∀ (ψ : Time → ℝ), HasCompactSupport ψ → tsupport ψ ⊆ Set.Ioo 0 T →
    ContDiff ℝ 1 ψ →
  ∀ (w : E.H),
    ∫ t in (0 : ℝ)..T,
      (-(inner (𝕜 := ℝ) (u t) w) * deriv ψ t +
        ψ t * (ν * E.viscousForm (u t) w + E.convForm (u t) (u t) w)) = 0

end LerayHopf
