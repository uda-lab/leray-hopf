import LerayHopf.TorusAubinLionsAssembly
import LerayHopf.TorusConvectionExtension
import LerayHopf.TorusGalerkinODESolve
import LerayHopf.TorusTraceEnergy
import LerayHopf.TorusViscousLimit

/-!
# LerayHopf.TorusGalerkinODECapstone — discharge `galerkin_ode_solution` (issue #24)

This file performs the capstone WIRING that removes the project axiom `galerkin_ode_solution`
from `exists_lerayHopf_torus3_axiomatic`.  It contains NO new mathematics: the finite-dimensional
torus Galerkin ODE is already solved unconditionally in `LerayHopf/TorusGalerkinODESolve.lean`
(`galerkinSolutionData_torus`).  Here we only assemble the per-`n` data into a Galerkin sequence
and feed it through the axiom-free package builder `build_galerkin_package_of_galSeq`.

Mirrors the ℝ³ template `LerayHopf/R3/GalerkinODECapstone.lean` (issue #10).

## Why this file exists (DAG position)

`TorusAubinLionsAssembly.lean` (where `torusAubinLionsPackage_of_galSeq` is defined) is UPSTREAM
of the torus solver chain here via `TorusModeTail → TorusModeCompactness → AxiomaticClosure`.
The capstone needs to see BOTH `torus3_NSForms_exists` (`TorusConvectionForm`) AND the proved
solver `galerkinSolutionData_torus` (`TorusGalerkinODESolve`), so it lands here, downstream of
both — the shallowest acyclic point.  `build_galerkin_package_of_galSeq` also lives here
(relocated from `AxiomaticClosure.lean`) so it can call the proved limit-passage theorems in
`TorusTraceEnergy` and `TorusViscousLimit` without creating an import cycle.

## The axiom-set delta

Routing the capstone through `galSeq_of_torus` (axiom-free, the proved solver) instead of the
`galerkin_ode_solution` axiom drops EXACTLY that axiom from `exists_lerayHopf_torus3_axiomatic`'s
`#print axioms`.  After issue #53 / PR #62 proved `torusConvectionGap_exists`, and after this file replaces
the former `galerkin_limit_passage` axiom with the proved theorems
`torus_galerkin_limit_passage_of_energyClass` + `torus_energyClass_of_aubinLions`, the capstone
carries ZERO remaining torus project axioms: `aubin_lions` is REMOVED (issue #23, T-AL-6 Stage C).

## Declarations added

- `galSeq_of_torus`                  — the proved, axiom-free per-`n` Galerkin sequence
- `build_galerkin_package_of_galSeq` — core assembly A2 → proved limit passage (relocated from `AxiomaticClosure.lean`)
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
  fun n => Torus.galerkinSolutionData_torus F ν hν u₀ n

/-- **Assembly (axiom-free core, relocated from `AxiomaticClosure.lean`).**
Build a `GalerkinCompactnessPackageFull` from an EXPLICIT Galerkin sequence `galSeq`,
chaining A2 (with `rellich_L2Sigma`) → the proved limit passage.

This is the body of `build_galerkin_package` factored from Step 2 onward (issue #24): it takes
`galSeq` as a parameter instead of producing it via the `galerkin_ode_solution` axiom, so it
carries NO dependency on A1.  Relocated here from `AxiomaticClosure.lean` so that it can call
the proved theorems `torus_galerkin_limit_passage_of_energyClass` and
`torus_energyClass_of_aubinLions` (which are downstream of `AxiomaticClosure`; keeping this def
there would create an import cycle).

The steps are:
1. Apply `torusAubinLionsPackage_of_galSeq` (proved, replaces the former `aubin_lions` axiom)
   with `spatial := rellich_L2Sigma` to get the Aubin–Lions package.
2. Apply `torus_galerkin_limit_passage_of_energyClass` (proved) with the energy-class hypothesis
   supplied by `torus_energyClass_of_aubinLions` (proved), to get the weak equation + energy
   inequality + initial trace.  This replaces the former `galerkin_limit_passage` axiom (A3).
3. Pack into `GalerkinCompactnessPackageFull`. -/
noncomputable def build_galerkin_package_of_galSeq (F : Torus3NSForms) (ν : ℝ) (hν : 0 < ν)
    (T : ℝ) (hT : 0 < T) (u₀ : L2Sigma)
    (galSeq : ∀ n, GalerkinSolutionData F ν u₀ n) :
    GalerkinCompactnessPackageFull F ν T u₀ := by
  -- Step 1 (A2): Aubin–Lions, with the spatial half discharged by `rellich_L2Sigma`.
  have alPkg : AubinLionsPackage F ν T u₀ galSeq :=
    torusAubinLionsPackage_of_galSeq F ν hν T hT u₀ galSeq rellich_L2Sigma
  -- Step 2 (proved): limit passage via `torus_galerkin_limit_passage_of_energyClass`,
  -- with the energy-class hypothesis supplied by `torus_energyClass_of_aubinLions`.
  -- The goal is a `Type` (a structure), so the existential is unpacked with `Exists.choose`
  -- rather than `obtain` (which only eliminates into `Prop`).  The a.e.-link conjunct
  -- (`hspec.1`: `hex.choose t = alPkg.u t` a.e. on `[0,T]`) is RETAINED to transfer
  -- time-measurability from the Aubin–Lions limit to the good representative.
  have hex := torus_galerkin_limit_passage_of_energyClass F ν hν T hT u₀ galSeq alPkg
                (torus_energyClass_of_aubinLions F ν hν T hT u₀ galSeq alPkg)
  have hspec := hex.choose_spec
  -- Time-measurability of the good representative, inherited from `alPkg.u_aestronglyMeasurable`
  -- through the a.e.-link (coercion-congr on `L2Sigma → L2VF`).
  have hmeas : MeasureTheory.AEStronglyMeasurable (fun t => (hex.choose t : L2VF))
      (MeasureTheory.volume.restrict (Set.Icc 0 T)) := by
    refine alPkg.u_aestronglyMeasurable.congr ?_
    filter_upwards [hspec.1] with t ht
    exact congrArg _ ht.symm
  -- Step 3: pack into the proof-carrying structure.
  exact
    { limit := hex.choose
      weak_eq_limit := hspec.2.1
      energy_ineq_limit := hspec.2.2.1
      initial_trace_limit := hspec.2.2.2.1
      energy_class_limit := hspec.2.2.2.2
      u_aestronglyMeasurable_limit := hmeas }

/-- **Full Galerkin compactness package (issue #24).**  Assembles the proof-carrying
`GalerkinCompactnessPackageFull` by feeding the axiom-free `galSeq_of_torus` into the axiom-free
core builder `build_galerkin_package_of_galSeq` (A2 → proved limit passage).  Carries NO
dependency on `galerkin_ode_solution` or `galerkin_limit_passage`. -/
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

The `_axiomatic` suffix is now historical — all torus project axioms have been removed:
`aubin_lions` is DISCHARGED by `torusAubinLionsPackage_of_galSeq` (issue #23, T-AL-6);
`galerkin_ode_solution`, `torusConvectionGap_exists`, and `galerkin_limit_passage` were
discharged in issues #24, #53, and PR #88 respectively; see `LerayHopf/Core.lean` for
the axiom-free layer.  The `_axiomatic` name is preserved to avoid renaming the public API. -/
theorem exists_lerayHopf_torus3_axiomatic (u₀ : L2Sigma) (ν : ℝ) (hν : 0 < ν)
    (T : ℝ) (hT : 0 < T) :
    ∃ F : Torus3NSForms, Nonempty (LerayHopfSolutionFull F ν T u₀) := by
  obtain ⟨F⟩ := torus3_NSForms_exists
  exact ⟨F, exists_lerayHopf_from_package_full F ν T u₀
    (build_galerkin_package_of_torus F ν hν T hT u₀)⟩

end LerayHopf
