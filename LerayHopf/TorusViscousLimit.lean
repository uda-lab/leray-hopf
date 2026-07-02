/-
# LerayHopf.TorusViscousLimit — conjunct (4): energy-class discharge for `alPkg.u` on 𝕋³

**Purpose:** This file discharges the conjunct-(4) energy-class obligation for the
Aubin–Lions limit `alPkg.u`, namely:

- a.e. `memH1VF (alPkg.u t : L2VF)` with respect to `volume.restrict (Set.Icc 0 T)`, and
- `IntervalIntegrable (fun s => viscousFormSq ν (alPkg.u s : L2VF)) volume 0 T`.

This pair of facts is the hypothesis `h4` consumed by
`torus_galerkin_limit_passage_of_energyClass` (in `LerayHopf.TorusTraceEnergy`), which
assembles the full 5-conjunct existential and thereby completes the removal of the
`galerkin_limit_passage` project axiom.

**Route (sketch for lean-prover):**
1. `alPkg.strong_convergence` gives `eLpNorm`-convergence-to-0 of the Galerkin subsequence
   to `alPkg.u` in L²(0,T; L²_σ); extract an a.e.-strongly-convergent subsequence.
2. Fatou-in-time on the honest `ENNReal`-valued `viscousEnn` (now public in
   `TorusTraceEnergy`) from the Galerkin energy identity gives the a.e. H¹ regularity
   and integrated dissipation bound via monotone-convergence / lim-inf argument.

**Axioms:** None.  The single `sorry` below is a scaffold placeholder.

NO import of `LerayHopf/Bochner/TimeSobolev*.lean`; no `W1pTime` witness is used.
-/

import LerayHopf.AxiomaticClosure
import LerayHopf.TorusTraceEnergy

namespace LerayHopf

open MeasureTheory Filter Topology intervalIntegral

/-- **Torus energy-class conjunct (4)** for the Aubin–Lions limit `alPkg.u`.

Given the full Galerkin-solution sequence and Aubin–Lions compactness package on 𝕋³,
the raw limit `alPkg.u` satisfies, for a.e. `t ∈ [0, T]`, `memH1VF (alPkg.u t : L2VF)`,
and the dissipation `viscousFormSq ν (alPkg.u s : L2VF)` is integrable on `[0, T]`.

This is the hypothesis `h4` of `torus_galerkin_limit_passage_of_energyClass`, which
plugging in here closes the `galerkin_limit_passage` removal. -/
theorem torus_energyClass_of_aubinLions (F : Torus3NSForms) (ν : ℝ) (hν : 0 < ν)
    (T : ℝ) (hT : 0 < T) (u₀ : L2Sigma)
    (galSeq : ∀ n, GalerkinSolutionData F ν u₀ n)
    (alPkg : AubinLionsPackage F ν T u₀ galSeq) :
    (∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc 0 T)),
        memH1VF (alPkg.u t : L2VF)) ∧
    IntervalIntegrable (fun s => viscousFormSq ν (alPkg.u s : L2VF))
      MeasureTheory.volume 0 T := by
  sorry -- ALLOW_SORRY: conjunct-(4) energy-class discharge for alPkg.u; proof by lean-prover via a.e.-strong-subsequence (from alPkg.strong_convergence eLpNorm→0) + reg_bound Fatou-in-time on the honest ENNReal viscousEnn; wired into torus_galerkin_limit_passage removal

end LerayHopf
