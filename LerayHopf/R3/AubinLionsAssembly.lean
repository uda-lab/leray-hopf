import LerayHopf.R3.AubinLionsLimitPassage
import LerayHopf.R3.LimitPassage

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
  UNCONDITIONAL, LOCAL Bochner-time compactness extraction (per-ball `restrictToBall R` a.e.-in-time
  L² convergence, not global), supplied to
  `aubinLionsPackage_R3_of_timeCompactness`.  Stating it unconditionally absorbs the
  time-equicontinuity modulus, so the time layer rests on exactly THIS ONE axiom; the redundant
  `timeCompactnessInput_R3` axiom from the prior revision of this PR (which only fed this extraction)
  is dropped.  `TimeCompactnessInput` remains a plain hypothesis *type*, never inherently an axiom.

So the capstone `exists_lerayHopf_r3_axiomatic` swaps `aubin_lions_R3` →
`galerkinSpaceTimeExtraction_R3` for the time-compactness layer (a 1-for-1 thin swap), with the
spatial half now PROVED.

## Declarations added

- `build_galerkin_package_R3_of_galSeq` — assembly (relocated): AubinLions package → AX-3
-/

namespace LerayHopf

open MeasureTheory

/-! ### Assembly (relocated from `AxiomaticClosure.lean`, issue #15)

NOTE (axiom collapse): the prior revision of this PR introduced a redundant
`timeCompactnessInput_R3` axiom (a separate `n`-uniform L² time-equicontinuity modulus); it has been
DROPPED.  Its content is now absorbed into the single UNCONDITIONAL extraction axiom
`galerkinSpaceTimeExtraction_R3` (`AubinLionsLimitPassage.lean`), so the time layer rests on exactly
ONE axiom.  The proved
constructor `aubinLionsPackage_R3_of_timeCompactness` no longer takes a `TimeCompactnessInput`
argument (that structure stays a plain hypothesis type, not an axiom). -/

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
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n)
    (htest : R3TestApproxH1 𝔊) :
    GalerkinCompactnessPackageFull_R3 𝔊 F ν T u₀ := by
  -- Step 1: the Aubin–Lions package, PROVED (spatial half = FK-derived `LocalRellichInput`,
  -- time half = the single unconditional `galerkinSpaceTimeExtraction_R3`).
  have alPkg : AubinLionsPackage_R3 𝔊 F ν T u₀ galSeq :=
    aubinLionsPackage_R3_of_timeCompactness 𝔊 F ν hν T hT u₀ galSeq
      (localRellichInput_of_frechetKolmogorov frechetKolmogorov_holds)
  -- Step 2 (AX-3 → proved theorem): limit passage to the good representative.
  -- The goal is a `Type` (a structure), so the existential is unpacked with
  -- `Exists.choose` rather than `obtain` (which only eliminates into `Prop`).
  -- The a.e.-link conjunct (`hspec.1`: `hex.choose t = alPkg.u t` a.e. on `[0,T]`) is
  -- RETAINED to transfer time-measurability from the Aubin–Lions limit to the representative.
  have hex := galerkin_limit_passage_R3 𝔊 F ν hν T hT u₀ galSeq alPkg htest
  have hspec := hex.choose_spec
  -- Time-measurability of the good representative, inherited from `alPkg.u_aestronglyMeasurable`
  -- through the a.e.-link (coercion-congr on `L2Sigma_R3 → L2VF_R3`, mirroring `LimitPassage`).
  have hmeas : AEStronglyMeasurable (fun t => (hex.choose t : L2VF_R3))
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

end LerayHopf
