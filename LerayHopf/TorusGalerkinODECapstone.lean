import LerayHopf.TorusConvectionForm
import LerayHopf.TorusGalerkinODESolve

/-!
# LerayHopf.TorusGalerkinODECapstone — discharge `galerkin_ode_solution` (issue #24)

This file performs the capstone WIRING that removes the project axiom `galerkin_ode_solution`
from `exists_lerayHopf_torus3_axiomatic`.  It contains NO new mathematics: the finite-dimensional
torus Galerkin ODE is already solved unconditionally in `LerayHopf/TorusGalerkinODESolve.lean`
(`galerkinSolutionData_torus`).  Here we only assemble the per-`n` data into a Galerkin sequence
and feed it through the axiom-free package builder `build_galerkin_package_of_galSeq`.

Mirrors the ℝ³ template `LerayHopf/R3/GalerkinODECapstone.lean` (issue #10).

## Why this file exists (DAG position)

`AxiomaticClosure.lean` (where the axiom is declared and `build_galerkin_package_of_galSeq` lives)
is UPSTREAM of the torus solver chain (`TorusGalerkinScheme` → `TorusGalerkinODESolve` both import
`AxiomaticClosure`).  The capstone needs to see BOTH `torus3_NSForms_exists`
(`TorusConvectionForm`) AND the proved solver `galerkinSolutionData_torus`
(`TorusGalerkinODESolve`), so it lands here, downstream of both — the shallowest acyclic point.

## The axiom-set delta

Routing the capstone through `galSeq_of_torus` (axiom-free, the proved solver) instead of the
`galerkin_ode_solution` axiom drops EXACTLY that axiom from `exists_lerayHopf_torus3_axiomatic`'s
`#print axioms`.  After this change the capstone rests on the three remaining torus project axioms:
`torusConvectionGap_exists`, `aubin_lions`, `galerkin_limit_passage`.

## Declarations added

- `galSeq_of_torus`                  — the proved, axiom-free per-`n` Galerkin sequence
- `build_galerkin_package_of_torus`  — full package via the axiom-free builder
- `exists_lerayHopf_torus3_axiomatic` — main existence theorem (relocated from `TorusConvectionForm`)
-/

namespace LerayHopf

/-- **Concrete, axiom-free Galerkin sequence (issue #24).**  For a `Torus3NSForms` bundle `F`, the
per-`n` Galerkin solution data is supplied unconditionally by `galerkinSolutionData_torus` (which
rests on the proved forward-global finite-dim ODE solver `forwardGlobalSolution_exists`, NOT on
`galerkin_ode_solution`).

This is the drop-in replacement for the `fun n => galerkin_ode_solution F ν hν u₀ n` sequence used
inside `build_galerkin_package`: same type (`∀ n, GalerkinSolutionData F ν u₀ n`), no axiom. -/
noncomputable def galSeq_of_torus (F : Torus3NSForms) (ν : ℝ) (hν : 0 < ν) (u₀ : L2Sigma) :
    ∀ n, GalerkinSolutionData F ν u₀ n :=
  fun n => galerkinSolutionData_torus F ν hν u₀ n

/-- **Full Galerkin compactness package (issue #24).**  Assembles the proof-carrying
`GalerkinCompactnessPackageFull` by feeding the axiom-free `galSeq_of_torus` into the axiom-free
core builder `build_galerkin_package_of_galSeq` (A2 → A3).  Carries NO dependency on
`galerkin_ode_solution`. -/
noncomputable def build_galerkin_package_of_torus (F : Torus3NSForms) (ν : ℝ) (hν : 0 < ν)
    (T : ℝ) (hT : 0 < T) (u₀ : L2Sigma) :
    GalerkinCompactnessPackageFull F ν T u₀ :=
  build_galerkin_package_of_galSeq F ν hν T hT u₀ (galSeq_of_torus F ν hν u₀)

/-- **Main existence theorem (axiomatic) — rerouted through the proved solver (issue #24).**

For any `u₀ ∈ L²_σ`, `ν > 0`, `T > 0`, there exists a `Torus3NSForms` bundle `F` and a
Leray–Hopf solution `u` on `[0, T]`.

Relocated here from `LerayHopf/TorusConvectionForm.lean` (downstream of both the convection gap and
the proved torus Galerkin solver, no import cycle) so that the per-`n` Galerkin sequence is sourced
from the axiom-free `galerkinSolutionData_torus` (over the finite-dim `velocitySpan n`), discharging
`galerkin_ode_solution`.  The theorem name and statement are **byte-identical** to the original
(only the package builder swapped: `build_galerkin_package` → `build_galerkin_package_of_torus`).

The `_axiomatic` suffix advertises dependence on the THREE remaining torus project axioms
(`torusConvectionGap_exists`, `aubin_lions`, `galerkin_limit_passage`).  `galerkin_ode_solution` is
NO LONGER among them — discharged here (issue #24); see `LerayHopf/Core.lean` for the axiom-free
layer. -/
theorem exists_lerayHopf_torus3_axiomatic (u₀ : L2Sigma) (ν : ℝ) (hν : 0 < ν)
    (T : ℝ) (hT : 0 < T) :
    ∃ F : Torus3NSForms, Nonempty (LerayHopfSolutionFull F ν T u₀) := by
  obtain ⟨F⟩ := torus3_NSForms_exists
  exact ⟨F, exists_lerayHopf_from_package_full F ν T u₀
    (build_galerkin_package_of_torus F ν hν T hT u₀)⟩

end LerayHopf
