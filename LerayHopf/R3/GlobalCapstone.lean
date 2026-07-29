-- ℝ³ global-in-time Leray–Hopf capstone (issue #212, campaign phase P1′ / issue #214).
--
-- STATEMENT LAYER ONLY (P1′). This file freezes the ℝ³ global capstone TARGET and the
-- generic-structure abbrev, plus the machine-checked consistency witness tying the
-- global statement back to the existing finite-horizon capstone shape. The assembly
-- (`exists_global_lerayHopf_r3`, `exists_globalLerayHopfSolutionFull_r3`,
-- `globalR3Capstone`) is P4′ (#217) and FILLS this file later; nothing here proves the
-- hard direction.
--
-- Route (docs/scratch/r3-global-diagonal-campaign.md §2 Steps 1–5, P4′):
--   P3′ diagonal `(δ, W)`  →  per-horizon `R3KappaChainExitWitness` at `κ := δ` (P2′)
--   →  coherence `w.v = W` (from `z : L2VF_R3` tests, `L2Sigma_R3_eq_of_forall_inner`)
--   →  contract transfer via P1's `IsLerayHopfOn.congr_Icc` / `.mono`.
--
-- Mirrors the merged torus twin `LerayHopf/Torus/GlobalCapstone.lean` (issue #203):
-- `GlobalR3CapstoneStatement` + `globalR3Capstone_implies_finite` are the ℝ³ analogues
-- of `GlobalTorusCapstoneStatement` + `globalTorusCapstone_implies_finite`.
import LerayHopf.R3.SolutionInterfaces
import LerayHopf.Galerkin.GlobalContract

open MeasureTheory Filter Topology Set

namespace LerayHopf

/-! ### The frozen ℝ³ capstone statement (P1′; docs/scratch/r3-global-diagonal-campaign.md §2.1)

`GlobalR3CapstoneStatement` is a `Prop`-valued definition — proving it is the campaign
(phases P1′–P4′). Stating it makes the `∃ 𝔊, ∃ F, ∃ u, ∀ T > 0` literalness
machine-checked. `globalR3Capstone_implies_finite` is the machine-checked consistency
witness tying the global statement back to the existing finite-horizon capstone shape
(`exists_lerayHopf_r3`, `LerayHopf/R3/GalerkinODECapstone.lean:109`). -/

/-- **Frozen P4′ target** (docs/scratch/r3-global-diagonal-campaign.md §2.1): the ℝ³
global capstone. Quantifier prefix `∃ 𝔊, ∃ F, ∃ u, ∀ T` — one scheme, one form bundle,
and ONE curve serving every horizon (see §2.1 for the honest obligations α/β this carries
beyond the finite-horizon `∀ T, ∃ 𝔊 F, …` release capstone). -/
def GlobalR3CapstoneStatement : Prop := -- ALLOW_NAME: statement only (bare def : Prop, the frozen P4′ campaign target)
  ∀ (u₀ : L2Sigma_R3) (ν : ℝ), 0 < ν →
    ∃ (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊), ∃ u : Time → L2Sigma_R3,
      ∀ T : ℝ, 0 < T → Galerkin.IsLerayHopfOn (r3Domain 𝔊) F.core ν T u₀ u

/-! ### The generic global-solution structure, ℝ³-specialized (§2.1)

The `∃ 𝔊 F, Nonempty (GlobalLerayHopfSolutionFull_R3 …)` structure form of the capstone
packages the single curve into `Galerkin.GlobalLerayHopfSolution`. -/

/-- ℝ³ abbrev of the generic global structure (§2.1). -/
abbrev GlobalLerayHopfSolutionFull_R3 (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (u₀ : L2Sigma_R3) :=
  Galerkin.GlobalLerayHopfSolution (r3Domain 𝔊) F.core ν u₀

/-- Sanity direction (proved): the frozen global statement implies the EXISTING
finite-horizon capstone statement shape (`exists_lerayHopf_r3`,
`LerayHopf/R3/GalerkinODECapstone.lean:109`) at every horizon — so the campaign target is
genuinely a strengthening, never a side-grade. This is the easy direction (global ⇒
finite, via `ofIsOn`); nothing here is evidence for the hard direction (P3′/P4′). -/
theorem globalR3Capstone_implies_finite (hG : GlobalR3CapstoneStatement) : -- ALLOW_NAME: reserved term is the hypothesis Prop's name; the implication itself is fully proved below
    ∀ (u₀ : L2Sigma_R3) (ν : ℝ), 0 < ν → ∀ T : ℝ, 0 < T →
      ∃ (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊),
        Nonempty (LerayHopfSolutionFull_R3 𝔊 F ν T u₀) := by
  intro u₀ ν hν T hT
  obtain ⟨𝔊, F, u, hu⟩ := hG u₀ ν hν
  exact ⟨𝔊, F, ⟨Galerkin.LerayHopfSolution.ofIsOn (hu T hT)⟩⟩

end LerayHopf
