import LerayHopf.R3.SchwartzDivFreeBasis

/-!
# LerayHopf.R3Axiomatic — axiomatic closure for ℝ³

This module re-exports the full axiomatic closure of the ℝ³ Leray–Hopf
existence argument.  The capstone declaration is:

    `LerayHopf.exists_lerayHopf_r3_axiomatic`

which depends on five project axioms:
- `curlSchwartzDense_holds` (issue #21): Helmholtz/Weyl curl-density on L²_σ(ℝ³) — a single
  thin density `Prop`; it REPLACED the former 6-field `r3GalerkinScheme_exists` structure
  existential (now a discharged `theorem` resting on this density)
- `r3_NSForms_exist` (AX-4): ℝ³ NS convection form exists
- `galerkin_ode_solution_R3` (AX-2): Picard–Lindelöf on approximation subspace
- `aubin_lions_R3` (AX-3): Aubin–Lions time compactness on ℝ³
- `galerkin_limit_passage_R3` (AX-4): limit passage to weak NS solution on ℝ³

`r3GalerkinScheme_exists` (former AX-G) is NO LONGER an axiom — it is a proved `theorem`
(`LerayHopf/R3/SchwartzDivFreeBasis.lean`), assembled from the constructive witness chain and
the single marked density axiom `curlSchwartzDense_holds` (issue #21).  Importing
`SchwartzDivFreeBasis` (which transitively imports `AxiomaticClosure`) re-exports both the
discharged `r3GalerkinScheme_exists` and the relocated capstone.

`spatial_compactness_R3` (AX-SC): LOCAL spatial compactness (local Rellich
H¹(B_R)↪↪L²(B_R)) is NO LONGER an axiom — it was the former sixth project axiom and is
now a proved `theorem` (discharged via the sorry-free Fréchet–Kolmogorov chain,
PR #35 / issue #2).

Import this module ONLY when you need the axiom-dependent results.
For axiom-free work, use `import LerayHopf.Core`.
-/
