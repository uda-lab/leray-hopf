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
* ADDED: `galerkinSpaceTimeExtraction_R3` (declared in `AubinLionsLimitPassage.lean`) — the single
  UNCONDITIONAL Bochner-time compactness extraction, supplied to
  `aubinLionsPackage_R3_of_timeCompactness`.  The former separate `timeCompactnessInput_R3`
  modulus axiom has been REMOVED: its content is absorbed into the unconditional extraction axiom,
  so the time layer is exactly ONE axiom, not two.

So the capstone `exists_lerayHopf_r3_axiomatic` swaps `aubin_lions_R3` →
`galerkinSpaceTimeExtraction_R3` for the time-compactness layer (a 1-for-1 thin swap), with the
spatial half now PROVED.

## Declarations added

- `build_galerkin_package_R3_of_galSeq` — assembly (relocated): AubinLions package → AX-3
-/

namespace LerayHopf

open MeasureTheory

/-! ### Assembly (relocated from `AxiomaticClosure.lean`, issue #15)

NOTE (axiom collapse): the former `timeCompactnessInput_R3` axiom (the separate `n`-uniform L²
time-equicontinuity modulus) has been REMOVED.  Its content is now absorbed into the single
UNCONDITIONAL `galerkinSpaceTimeExtraction_R3` axiom (`AubinLionsLimitPassage.lean`), so the time
layer rests on exactly ONE axiom rather than two.  The proved constructor
`aubinLionsPackage_R3_of_timeCompactness` no longer takes a `TimeCompactnessInput` argument. -/

/-- **Assembly (proved Aubin–Lions core → AX-3).**  Build a `GalerkinCompactnessPackageFull_R3`
from an EXPLICIT Galerkin sequence `galSeq`, chaining the proved Aubin–Lions package
(`aubinLionsPackage_R3_of_timeCompactness`, with the spatial half supplied by the FK-derived
`LocalRellichInput` and the time half by the unconditional `galerkinSpaceTimeExtraction_R3`)
→ AX-3 limit passage.

RELOCATED here from `AxiomaticClosure.lean` (issue #15): the former Step 1 applied the
`aubin_lions_R3` axiom; it now applies the proved constructor, so this builder sits downstream of
`AubinLionsLimitPassage`.  The name, signature, and produced structure are byte-identical to the
former `AxiomaticClosure` version, so the capstone (`build_galerkin_package_R3_of_basis`,
`GalerkinODECapstone.lean`) is unchanged except for seeing this definition through its import.

The steps are:
1. Apply `aubinLionsPackage_R3_of_timeCompactness` with the spatial half discharged by
   `localRellichInput_of_frechetKolmogorov frechetKolmogorov_holds` (the proved FK chain); the time
   half is supplied unconditionally by `galerkinSpaceTimeExtraction_R3` inside that constructor.
2. Apply `galerkin_limit_passage_R3` (AX-3) to obtain the weak equation + energy + trace.
3. Pack into `GalerkinCompactnessPackageFull_R3`. -/
noncomputable def build_galerkin_package_R3_of_galSeq (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T) (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n) :
    GalerkinCompactnessPackageFull_R3 𝔊 F ν T u₀ := by
  -- Step 1: the Aubin–Lions package, PROVED (spatial half = FK-derived `LocalRellichInput`,
  -- time half = the single unconditional `galerkinSpaceTimeExtraction_R3`).
  have alPkg : AubinLionsPackage_R3 𝔊 F ν T u₀ galSeq :=
    aubinLionsPackage_R3_of_timeCompactness 𝔊 F ν hν T hT u₀ galSeq
      (localRellichInput_of_frechetKolmogorov frechetKolmogorov_holds)
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
