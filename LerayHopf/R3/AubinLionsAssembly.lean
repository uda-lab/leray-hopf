import LerayHopf.R3.AubinLionsLimitPassage

/-!
# LerayHopf.R3.AubinLionsAssembly — package assembly through the proved Aubin–Lions constructor

This file holds the Galerkin compactness package builder
`build_galerkin_package_R3_of_galSeq`, RELOCATED here (issue #15) from `AxiomaticClosure.lean`.

## Why this file exists (DAG position)

The former `axiom aubin_lions_R3` (in `AxiomaticClosure.lean`) is REMOVED.  Its spatial half is
genuinely PROVED axiom-free (the `steklovAvg_spatial_extraction` chain), and its time half is
isolated as the strictly-thinner `galerkinSpaceTimeExtraction_R3`; the `AubinLionsPackage_R3` is
produced by `aubinLionsPackage_R3_of_timeCompactness`
(`LerayHopf/R3/AubinLionsLimitPassage.lean`).  That constructor imports `AxiomaticClosure`, so the
package builder that consumes it cannot live in `AxiomaticClosure` without an import cycle.  It
lands here, one level below `AubinLionsLimitPassage`, mirroring the #10/#24 capstone relocation.

## The axiom-set delta (issue #15)

* REMOVED: `aubin_lions_R3` (its spatial half PROVED, its time half isolated thinner).
* ADDED: `timeCompactnessInput_R3` — the isolated uniform-in-`n` L² time-equicontinuity modulus
  (`TimeCompactnessInput`) of the Galerkin curves, supplied to
  `aubinLionsPackage_R3_of_timeCompactness`.  The genuine Bochner-time extraction is
  `galerkinSpaceTimeExtraction_R3` (declared in `AubinLionsLimitPassage.lean`).

So the capstone `exists_lerayHopf_r3_axiomatic` swaps `aubin_lions_R3` →
`{ timeCompactnessInput_R3, galerkinSpaceTimeExtraction_R3 }` for the time-compactness layer, with
the spatial half now PROVED.

## Declarations added

- `timeCompactnessInput_R3`            — axiom: the n-uniform L² time-equicontinuity modulus
- `build_galerkin_package_R3_of_galSeq` — assembly (relocated): AubinLions package → AX-3
-/

namespace LerayHopf

open MeasureTheory

/-- **Axiom: uniform-in-`n` L² time-equicontinuity of the Galerkin curves** (the
`TimeCompactnessInput` modulus).  This is the isolated time-regularity input the proved
Aubin–Lions constructor `aubinLionsPackage_R3_of_timeCompactness` consumes: for every `ε > 0`
there is `δ > 0` such that for all `n` and all `s,t ∈ [0,T]` with `|s − t| < δ`,
`‖(galSeq n).u s − (galSeq n).u t‖ < ε`.

It is the standard `n`-uniform Bochner-time modulus of continuity of the Galerkin velocities on
`[0,T]` (from the `W^{1,p}(0,T;X)` estimate on the Galerkin time-derivative; mathlib lacks the
Bochner-Sobolev embedding that would prove it).  STRICTLY THINNER than the former `aubin_lions_R3`,
which bundled BOTH this time-equicontinuity AND the (now-proved) spatial compactness AND the whole
extraction; here the spatial half is proved and the extraction is `galerkinSpaceTimeExtraction_R3`.
Temam III.2.1. -/
axiom timeCompactnessInput_R3 -- ALLOW_AXIOM: n-uniform L² time-equicontinuity modulus of the Galerkin curves on [0,T] (TimeCompactnessInput); the Bochner-time modulus from the W^{1,p}(0,T;X) Galerkin time-derivative estimate (mathlib lacks the Bochner-Sobolev embedding); STRICTLY THINNER than the removed aubin_lions_R3 (spatial half now PROVED, extraction isolated as galerkinSpaceTimeExtraction_R3); Temam III.2.1
    (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (T : ℝ) (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n) :
    TimeCompactnessInput 𝔊 F ν T u₀ galSeq

/-! ### Assembly (relocated from `AxiomaticClosure.lean`, issue #15) -/

/-- **Assembly (proved Aubin–Lions core → AX-3).**  Build a `GalerkinCompactnessPackageFull_R3`
from an EXPLICIT Galerkin sequence `galSeq`, chaining the proved Aubin–Lions package
(`aubinLionsPackage_R3_of_timeCompactness`, with the spatial half supplied by the FK-derived
`LocalRellichInput` and the time modulus by `timeCompactnessInput_R3`) → AX-3 limit passage.

RELOCATED here from `AxiomaticClosure.lean` (issue #15): the former Step 1 applied the
`aubin_lions_R3` axiom; it now applies the proved constructor, so this builder sits downstream of
`AubinLionsLimitPassage`.  The name, signature, and produced structure are byte-identical to the
former `AxiomaticClosure` version, so the capstone (`build_galerkin_package_R3_of_basis`,
`GalerkinODECapstone.lean`) is unchanged except for seeing this definition through its import.

The steps are:
1. Apply `aubinLionsPackage_R3_of_timeCompactness` with the spatial half discharged by
   `localRellichInput_of_frechetKolmogorov frechetKolmogorov_holds` (the proved FK chain) and the
   time modulus by `timeCompactnessInput_R3`.
2. Apply `galerkin_limit_passage_R3` (AX-3) to obtain the weak equation + energy + trace.
3. Pack into `GalerkinCompactnessPackageFull_R3`. -/
noncomputable def build_galerkin_package_R3_of_galSeq (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T) (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n) :
    GalerkinCompactnessPackageFull_R3 𝔊 F ν T u₀ := by
  -- Step 1: the Aubin–Lions package, PROVED (spatial half = FK-derived `LocalRellichInput`,
  -- time half = the isolated `timeCompactnessInput_R3` modulus + `galerkinSpaceTimeExtraction_R3`).
  have alPkg : AubinLionsPackage_R3 𝔊 F ν T u₀ galSeq :=
    aubinLionsPackage_R3_of_timeCompactness 𝔊 F ν hν T hT u₀ galSeq
      (localRellichInput_of_frechetKolmogorov frechetKolmogorov_holds)
      (timeCompactnessInput_R3 𝔊 F ν T u₀ galSeq)
  -- Step 2 (AX-3): limit passage to the good representative.  The goal is a `Type`
  -- (a structure), so the existential is unpacked with `Exists.choose` rather than
  -- `obtain` (which only eliminates into `Prop`).  The a.e.-link conjunct
  -- (`hspec.1`) is intentionally discarded.
  have hex := galerkin_limit_passage_R3 𝔊 F ν hν T hT u₀ galSeq alPkg
  have hspec := hex.choose_spec
  -- Step 3: pack into the proof-carrying structure.
  exact
    { limit := hex.choose
      weak_eq_limit := hspec.2.1
      energy_ineq_limit := hspec.2.2.1
      initial_trace_limit := hspec.2.2.2.1
      energy_class_limit := hspec.2.2.2.2 }

end LerayHopf
