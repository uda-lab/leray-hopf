import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

open MeasureTheory

/-!
# Basic objects for the Leray–Hopf formalization

**Scaffold only.** This file fixes the *types* the existence theory will talk about —
the spatial 3-torus domain and the solution-concept
record `LerayHopfSolution` whose fields are `Prop` placeholders. The torus carries the
real product Haar (probability) measure; other analytical content is refined in later
milestones.

Interface authority: `docs/leray_hopf_lean_mvp_plan.md` (Milestone A/M2).
-/

namespace LerayHopf

/-- The time axis. -/
abbrev Time := ℝ

/-- The spatial 3-torus 𝕋³, realized as `UnitAddTorus (Fin 3)` = `Fin 3 → UnitAddCircle`,
with its product Haar (probability) measure.

`UnitAddCircle = AddCircle (1 : ℝ)` carries a `MeasureSpace` instance via
`AddCircle.measureSpace` (total mass 1), and the product measure on
`Fin 3 → UnitAddCircle` is provided by `MeasureTheory.MeasureSpace.pi`. -/
abbrev Torus3 := UnitAddTorus (Fin 3)

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
