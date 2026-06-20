import LerayHopf.R3.AxiomaticClosure

/-!
# LerayHopf.R3Axiomatic — axiomatic closure for ℝ³

This module re-exports the full axiomatic closure of the ℝ³ Leray–Hopf
existence argument.  The capstone declaration is:

    `LerayHopf.exists_lerayHopf_r3_axiomatic`

which depends on six project axioms:
- `r3GalerkinScheme_exists` (AX-G): Galerkin projection family on L²_σ(ℝ³)
- `r3_NSForms_exist` (AX-4): ℝ³ NS convection form exists
- `galerkin_ode_solution_R3` (AX-2): Picard–Lindelöf on approximation subspace
- `spatial_compactness_R3` (AX-SC): LOCAL spatial compactness (local Rellich H¹(B_R)↪↪L²(B_R))
- `aubin_lions_R3` (AX-3): Aubin–Lions time compactness on ℝ³
- `galerkin_limit_passage_R3` (AX-4): limit passage to weak NS solution on ℝ³

Import this module ONLY when you need the axiom-dependent results.
For axiom-free work, use `import LerayHopf.Core`.
-/
