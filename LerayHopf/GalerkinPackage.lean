import LerayHopf.Torus.Basic

open MeasureTheory

/-!
# Galerkin compactness package

**Scaffold only.** The MVP trick: instead of proving compactness and limit passage, we
*package their conclusions* as the fields of a structure. A `GalerkinCompactnessPackage`
asserts that a candidate limit exists together with every property needed to call it a
Leray–Hopf solution. Later milestones will construct such a package from the Galerkin
approximation; for now it is the explicit interface that isolates the hard analysis.

Field names follow `docs/leray_hopf_lean_mvp_plan.md` (Milestone C): the carrier is
`limit` (the candidate solution), not `approx`.
-/

namespace LerayHopf

/-- A package recording a candidate Leray–Hopf limit and all properties needed to
declare it a solution. Compactness and limit passage are not proved here — their
*conclusions* are stored as fields, to be supplied by a later construction. -/
structure GalerkinCompactnessPackage
    (Ω : Type*) [MeasureSpace Ω] (u₀ : Type*) where
  /-- The candidate limit velocity field (placeholder carrier type). -/
  limit : Time → Type
  /-- The limit satisfies the weak equation (placeholder). -/
  weak_eq_limit : Prop
  /-- The limit is divergence-free (placeholder). -/
  divergence_free_limit : Prop
  /-- The limit lies in the energy class (placeholder). -/
  energy_class_limit : Prop
  /-- The limit attains the initial datum (placeholder). -/
  initial_trace_limit : Prop
  /-- The limit satisfies the energy inequality (placeholder). -/
  energy_inequality_limit : Prop

end LerayHopf
