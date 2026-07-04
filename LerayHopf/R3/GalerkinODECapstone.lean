import LerayHopf.R3.CurlDensityCapstone   -- nonempty_schwartzGalerkinBasis (proved, issue #3 / #21)
import LerayHopf.R3.CurlDensityH1         -- curl_approx_H1 (issue #4 PR-2, H¹ curl-approx kernel)
import LerayHopf.R3.GalerkinODESolve
import LerayHopf.R3.AubinLionsAssembly   -- build_galerkin_package_R3_of_galSeq (relocated, issue #15)
import LerayHopf.R3.ConvectionExtension    -- r3_NSForms_exists (proved theorem, issue #56 rewire)

/-!
# LerayHopf.R3.GalerkinODECapstone — discharge `galerkin_ode_solution_R3` (issue #10)

This file performs the capstone WIRING that removes the project axiom
`galerkin_ode_solution_R3` from `exists_lerayHopf_r3_axiomatic`.  It contains NO new
mathematics: the finite-dimensional Galerkin ODE is already solved unconditionally over the
concrete scheme `schemeOfBasis B` in `LerayHopf/R3/GalerkinODESolve.lean`
(`galerkinSolutionData_unconditional`).  Here we only assemble the per-`n` data into a
Galerkin sequence and feed it through the axiom-free package builder.

## Why this file exists (DAG position)

It is the shallowest acyclic point that sees BOTH:
- `nonempty_schwartzGalerkinBasis` and `schemeOfBasis` (the concrete basis + scheme, from
  `SchwartzDivFreeBasis` / `GalerkinODEExistence`), and
- `galerkinSolutionData_unconditional` (the unconditional finite-dim solver, from
  `GalerkinODESolve`).

`AxiomaticClosure.lean` (where the axiom is declared and `build_galerkin_package_R3_of_galSeq`
lives) is UPSTREAM of `GalerkinODESolve`, so the wiring cannot go there without an import
cycle; it lands here, one level below `GalerkinODESolve`.

## The axiom-set delta

Routing the capstone through `galSeq_R3_of_basis` (axiom-free, concrete scheme) instead of
the `galerkin_ode_solution_R3` axiom drops EXACTLY that axiom from
`exists_lerayHopf_r3_axiomatic`'s `#print axioms`.  After issue #15 (which removed `aubin_lions_R3` — proving its spatial half and swapping its
time content 1-for-1 for the single strictly-thinner UNCONDITIONAL
`galerkinSpaceTimeExtraction_R3`), issue #48 (which reorganized the named axiom `r3_NSForms_exist`
into the operator-gap form `r3ConvectionGapOp_exists` + the proved theorem `r3_NSForms_exists`
via `R3NSForms_of_gap`), and issue #56 (which proved `r3ConvectionGapOp_exists` sorry-free as
`r3ConvectionGapOp_holds` via the determined-form construction in `ConvectionExtension.lean`),
the capstone rests on TWO project axioms: `galerkin_limit_passage_R3` and
`galerkin_spacetime_precompact_R3`.
`r3ConvectionGapOp_exists` is NO LONGER among them — PROVED (issue #56) as `r3ConvectionGapOp_holds`.

## Declarations added

- `galSeq_R3_of_basis`               — concrete, axiom-free Galerkin sequence over `schemeOfBasis B`
- `build_galerkin_package_R3_of_basis` — full package via the axiom-free builder
- `exists_lerayHopf_r3_axiomatic`    — main existence theorem (relocated from `SchwartzDivFreeBasis`)
-/

namespace LerayHopf

/-- **Concrete, axiom-free Galerkin sequence (issue #10).**  For the concrete scheme
`schemeOfBasis B` and an NS-forms bundle `F`, the per-`n` Galerkin solution data is supplied
unconditionally by `galerkinSolutionData_unconditional` (which rests on the proved finite-dim
ODE solver `finDimGlobalODE_exists`, NOT on `galerkin_ode_solution_R3`).

This is the drop-in replacement for the `fun n => galerkin_ode_solution_R3 𝔊 F ν hν u₀ n`
sequence used inside `build_galerkin_package_R3`: same type
(`∀ n, GalerkinSolutionData_R3 (schemeOfBasis B) F ν u₀ n`), no axiom. -/
noncomputable def galSeq_R3_of_basis (B : SchwartzGalerkinBasis)
    (F : R3NSForms (schemeOfBasis B)) (ν : ℝ) (hν : 0 < ν) (u₀ : L2Sigma_R3) :
    ∀ n, GalerkinSolutionData_R3 (schemeOfBasis B) F ν u₀ n :=
  fun n => galerkinSolutionData_unconditional B F ν hν u₀ n

/-- **Full Galerkin compactness package over the concrete scheme (issue #10).**  Assembles
the proof-carrying `GalerkinCompactnessPackageFull_R3` over `schemeOfBasis B` by feeding the
axiom-free `galSeq_R3_of_basis` into the axiom-free core builder
`build_galerkin_package_R3_of_galSeq` (AX-2 → AX-3).  Carries NO dependency on
`galerkin_ode_solution_R3`. -/
noncomputable def build_galerkin_package_R3_of_basis (B : SchwartzGalerkinBasis)
    (F : R3NSForms (schemeOfBasis B)) (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T)
    (u₀ : L2Sigma_R3) :
    GalerkinCompactnessPackageFull_R3 (schemeOfBasis B) F ν T u₀ :=
  build_galerkin_package_R3_of_galSeq (schemeOfBasis B) F ν hν T hT u₀
    (galSeq_R3_of_basis B F ν hν u₀)

/-- **Main existence theorem on ℝ³ (axiomatic).**  Relocated from
`LerayHopf/R3/SchwartzDivFreeBasis.lean` (issue #10) so that the per-`n` Galerkin sequence is
sourced from the axiom-free `galerkinSolutionData_unconditional` over the concrete scheme
`schemeOfBasis B`, discharging `galerkin_ode_solution_R3`.

For any `u₀ ∈ L²_σ(ℝ³)`, `ν > 0`, `T > 0`, there exist a Galerkin scheme `𝔊`, an NS-forms
bundle `F`, and a Leray–Hopf solution `u` on `[0, T]`.

The witness scheme is the CONCRETE `schemeOfBasis B`, with `B` drawn from
`nonempty_schwartzGalerkinBasis` (NOT from `r3GalerkinScheme_exists`, which would discard the
basis via `Nonempty.elim` and reintroduce the need for the per-scheme ODE axiom).

The name `_axiomatic` advertises that this result depends on the TWO remaining project axioms
(`galerkin_limit_passage_R3`, `galerkin_spacetime_precompact_R3`).
`galerkin_ode_solution_R3` is NO LONGER among them — discharged here (issue #10).
`aubin_lions_R3` is NO LONGER among them — removed (issue #15): its spatial half PROVED, its time
content swapped 1-for-1 for the single strictly-thinner UNCONDITIONAL `galerkinSpaceTimeExtraction_R3`
(its modulus absorbed here; the redundant prior-revision `timeCompactnessInput_R3` axiom is dropped).
`r3GalerkinScheme_exists` was discharged earlier (issue #21, `curlSchwartzDense_holds`);
`spatial_compactness_R3` earlier still (issue #2, FK chain).
`r3_NSForms_exist` is NO LONGER among them — replaced (issue #48, reorganization):
  the named axiom was replaced by `r3ConvectionGapOp_exists` (operator core, in `ConvectionForm.lean`)
  and the proved theorem `r3_NSForms_exists` (same conclusion, proved via `R3NSForms_of_gap`).
`r3ConvectionGapOp_exists` is NO LONGER among them — PROVED (issue #56) sorry-free as the
  theorem `r3ConvectionGapOp_holds` in `ConvectionExtension.lean` (determined-form construction);
  the operator core is now entirely axiom-free.  Net project axioms: 2. -/
theorem exists_lerayHopf_r3_axiomatic (u₀ : L2Sigma_R3) (ν : ℝ) (hν : 0 < ν)
    (T : ℝ) (hT : 0 < T) :
    ∃ (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊),
    Nonempty (LerayHopfSolutionFull_R3 𝔊 F ν T u₀) := by
  obtain ⟨B⟩ := nonempty_schwartzGalerkinBasis
  obtain ⟨F⟩ := r3_NSForms_exists (schemeOfBasis B)
  exact ⟨schemeOfBasis B, F, exists_lerayHopf_from_package_full_R3 (schemeOfBasis B) F ν T u₀
    (build_galerkin_package_R3_of_basis B F ν hν T hT u₀)⟩

end LerayHopf
