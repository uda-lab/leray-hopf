import LerayHopf.R3.GalerkinODECapstone

/-!
# LerayHopf.R3Capstone — capstone re-export for ℝ³

This module re-exports the full capstone chain of the ℝ³ Leray–Hopf
existence argument.  The capstone declaration is:

    `LerayHopf.exists_lerayHopf_r3`

which depends on **ZERO project axioms** — KERNEL-ONLY (`#print axioms` = `[propext, Classical.choice, Quot.sound]`).
Former project axioms now all discharged:
- `galerkin_spacetime_precompact_R3` (issue #46 PR-4): PROVED as theorem in `ArzelaAscoliTime.lean`
- `galerkin_limit_passage_R3` (issue #4 PR-6): PROVED as theorem in `LimitPassage.lean`

`r3ConvectionGapOp_exists` (former AX-4, issue #48) is NO LONGER an axiom — it is PROVED
sorry-free as the theorem `r3ConvectionGapOp_holds` in `ConvectionExtension.lean` (issue #56,
determined-form construction); all five `ConvectionGapOp` fields are discharged, including
`b_cont_fixedTest` which is now GENUINELY proved (not assumed) via the BLT extension on the
determined submodule `D = (𝒮 ⊗ L²_σ) + (L²_σ ⊗ 𝒮)`.  The proved theorem `r3_NSForms_exists`
(same conclusion, no statement weakening) is rerouted through `r3ConvectionGapOp_holds` in
`ConvectionExtension.lean`.  Mirrors torus `torusConvectionGap_exists` (issue #22).

`galerkin_ode_solution_R3` (former AX-2) is NO LONGER an axiom — it is discharged (issue #10)
by routing the capstone's per-`n` Galerkin sequence through the axiom-free
`galerkinSolutionData_unconditional` over the concrete scheme `schemeOfBasis B`
(`LerayHopf/R3/GalerkinODESolve.lean`).  The wiring lives in
`LerayHopf/R3/GalerkinODECapstone.lean`, which also hosts the relocated capstone.

`r3GalerkinScheme_exists` (former AX-G) is NO LONGER an axiom — it is a proved `theorem`
(`LerayHopf/R3/SchwartzDivFreeBasis.lean`), assembled from the constructive witness chain and
the proved theorem `curlSchwartzDense_holds` (issue #3 Fourier route, issue #21 wiring).
Importing `GalerkinODECapstone` (which transitively imports `SchwartzDivFreeBasis` and
`SolutionInterfaces`) re-exports the discharged `r3GalerkinScheme_exists` and the relocated capstone.

`spatial_compactness_R3` (AX-SC): LOCAL spatial compactness (local Rellich
H¹(B_R)↪↪L²(B_R)) is NO LONGER an axiom — it was the former sixth project axiom and is
now a proved `theorem` (discharged via the sorry-free Fréchet–Kolmogorov chain,
PR #35 / issue #2).

`aubin_lions_R3` (former AX-3): the full Aubin–Lions package axiom is NO LONGER an axiom —
removed (issue #15).  Its spatial half is genuinely PROVED axiom-free (the
`steklovAvg_spatial_extraction` chain over the FK-derived `LocalRellichInput`), and its time
content was initially replaced by the proved theorem `galerkinSpaceTimeExtraction_R3`
(subsequently PROVED via `u_lim_aestronglyMeasurable` in `ArzelaAscoliTime.lean`, issue #44;
the redundant prior-revision `timeCompactnessInput_R3` is dropped).
The package is assembled by the proved constructor
`aubinLionsPackage_R3_of_timeCompactness` (`LerayHopf/R3/AubinLionsLimitPassage.lean`), wired
through the relocated builder in `LerayHopf/R3/AubinLionsAssembly.lean`.

This module is KERNEL-ONLY (zero project axioms).  Import it whenever the full R³ capstone
chain (`exists_lerayHopf_r3`) is needed; `import LerayHopf.Core` suffices for work
that does not require the R³ capstone declarations.
-/
