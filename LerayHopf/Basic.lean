import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory

/-!
# Basic objects for the Leray–Hopf formalization

**Scaffold only.** This file fixes the *types* the existence theory will talk about —
a placeholder domain, a placeholder spatial-field type, and the solution-concept record
`LerayHopfSolution` whose fields are `Prop` placeholders. No analytical content is
encoded yet; the fields are refined monotonically in later milestones.

Interface authority: `docs/leray_hopf_lean_mvp_plan.md` (Milestone A).
-/

namespace LerayHopf

/-- The time axis. -/
abbrev Time := ℝ

/-- Placeholder for the spatial 3-torus `𝕋³`.

A **fresh** named placeholder (not an alias of any analytic type) carrying a
deliberately trivial `MeasureSpace` instance — the indiscrete σ-algebra and the **zero**
measure — so downstream statements can quantify over a measured domain *without*
inheriting the identity, topology, or Lebesgue measure of some concrete space. The zero
measure is intentionally **not** the real Haar/volume measure: it signals "not realized
yet" rather than silently standing in for the wrong domain.
TODO(M2): realize as `UnitAddTorus 3` with its Haar/volume measure. -/
def Torus3 : Type := PUnit

noncomputable instance : MeasureSpace Torus3 where
  __ := (⊤ : MeasurableSpace Torus3)
  volume := 0

/-- Placeholder for a spatial field on a domain `Ω` (e.g. an element of `L²_σ(Ω)`).
Realized as a real function space in a later milestone. -/
structure SpatialField (Ω : Type*) where
  carrier : Type*
  dummy : True := by trivial

/-- The concept of a Leray–Hopf weak solution, as a record of the defining properties.

Skeletal by design: each analytical property is a `Prop` placeholder
(`weak_eq`, `divergence_free`, `energy_class`, `initial_trace`, `energy_inequality`),
to be replaced by its real meaning in later milestones. This gives existence theorems a
concrete target type without committing to the analysis prematurely. -/
structure LerayHopfSolution
    (Ω : Type*) [MeasureSpace Ω] (u₀ : Type*) where
  /-- The candidate velocity field as a function of time (placeholder carrier type). -/
  u : Time → Type
  /-- Holds the weak Navier–Stokes equation (placeholder). -/
  weak_eq : Prop
  /-- Holds the divergence-free condition (placeholder). -/
  divergence_free : Prop
  /-- Holds the energy-class membership `L∞_t L²_x ∩ L²_t H¹_x` (placeholder). -/
  energy_class : Prop
  /-- Holds the attainment of the initial datum (placeholder). -/
  initial_trace : Prop
  /-- Holds the energy inequality (placeholder). -/
  energy_inequality : Prop

end LerayHopf
