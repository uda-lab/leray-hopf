import LerayHopf.R3.GalerkinODECapstone

/-!
# LerayHopf.R3Axiomatic — axiomatic closure for ℝ³

This module re-exports the full axiomatic closure of the ℝ³ Leray–Hopf
existence argument.  The capstone declaration is:

    `LerayHopf.exists_lerayHopf_r3_axiomatic`

which depends on four project axioms:
- `curlSchwartzDense_holds` (issue #21): Helmholtz/Weyl curl-density on L²_σ(ℝ³) — a single
  thin density `Prop`; it REPLACED the former 6-field `r3GalerkinScheme_exists` structure
  existential (now a discharged `theorem` resting on this density)
- `r3_NSForms_exist` (AX-4): ℝ³ NS convection form exists
- `galerkinSpaceTimeExtraction_R3` (issue #15): the single UNCONDITIONAL, LOCAL Bochner-time
  compactness extraction — per-ball (`restrictToBall R`) a.e.-in-time L² convergence, NOT global
  (no tightness on ℝ³) — the 1-for-1 thin (genuinely weaker) replacement of `aubin_lions_R3`'s time
  content; it absorbs the time-equicontinuity modulus, so no separate `timeCompactnessInput_R3` axiom
  is needed; mathlib lacks Bochner Fréchet–Kolmogorov in L²(0,T;X)
- `galerkin_limit_passage_R3` (AX-4): limit passage to weak NS solution on ℝ³

`galerkin_ode_solution_R3` (former AX-2) is NO LONGER an axiom — it is discharged (issue #10)
by routing the capstone's per-`n` Galerkin sequence through the axiom-free
`galerkinSolutionData_unconditional` over the concrete scheme `schemeOfBasis B`
(`LerayHopf/R3/GalerkinODESolve.lean`).  The wiring lives in
`LerayHopf/R3/GalerkinODECapstone.lean`, which also hosts the relocated capstone.

`r3GalerkinScheme_exists` (former AX-G) is NO LONGER an axiom — it is a proved `theorem`
(`LerayHopf/R3/SchwartzDivFreeBasis.lean`), assembled from the constructive witness chain and
the single marked density axiom `curlSchwartzDense_holds` (issue #21).  Importing
`GalerkinODECapstone` (which transitively imports `SchwartzDivFreeBasis` and `AxiomaticClosure`)
re-exports the discharged `r3GalerkinScheme_exists` and the relocated capstone.

`spatial_compactness_R3` (AX-SC): LOCAL spatial compactness (local Rellich
H¹(B_R)↪↪L²(B_R)) is NO LONGER an axiom — it was the former sixth project axiom and is
now a proved `theorem` (discharged via the sorry-free Fréchet–Kolmogorov chain,
PR #35 / issue #2).

`aubin_lions_R3` (former AX-3): the full Aubin–Lions package axiom is NO LONGER an axiom —
removed (issue #15).  Its spatial half is genuinely PROVED axiom-free (the
`steklovAvg_spatial_extraction` chain over the FK-derived `LocalRellichInput`), and its time
content is SWAPPED 1-for-1 for the single strictly-thinner UNCONDITIONAL axiom
`galerkinSpaceTimeExtraction_R3` (which absorbs the time-equicontinuity modulus, so no separate
modulus axiom is needed; the redundant prior-revision `timeCompactnessInput_R3` axiom is dropped).
The package is assembled by the proved
constructor
`aubinLionsPackage_R3_of_timeCompactness` (`LerayHopf/R3/AubinLionsLimitPassage.lean`), wired
through the relocated builder in `LerayHopf/R3/AubinLionsAssembly.lean`.

Import this module ONLY when you need the axiom-dependent results.
For axiom-free work, use `import LerayHopf.Core`.
-/
