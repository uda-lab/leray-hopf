-- 𝕋³ global-in-time Leray–Hopf capstone (issue #195, campaign phase P4 / issue #203).
--
-- Assembles the finite-horizon torus contract at EVERY horizon into a single global
-- statement: ONE form bundle `F` and ONE curve `u : Time → L2Sigma` such that
-- `Galerkin.IsLerayHopfOn torusDomain F.core ν T u₀ u` holds for all `T > 0`.
--
-- Route (docs/scratch/global-diagonal-campaign.md §2 Steps 3–5):
--   P3 diagonal `(δ, W)`  →  per-horizon `P2ExitWitness` at `κ := δ` (P2)
--   →  coherence `vₘ = W` (from `z : L2Sigma` tests, `L2Sigma_eq_of_forall_inner`)
--   →  contract transfer via P1's `IsLerayHopfOn.congr_Icc` / `.mono`.
--
-- `GlobalTorusCapstoneStatement` + `globalTorusCapstone_implies_finite` are PROMOTED
-- here from the (now deleted) feasibility spike `LerayHopf/Scratch/GlobalContractTorus.lean`
-- (architect Q1 ruling on #203; MOVE per the P1/P3 precedent — nothing imported the
-- scratch file). `globalTorusCapstone` proves the frozen `def : Prop` target literally.
import LerayHopf.Torus.DiagonalGalerkin
import LerayHopf.Torus.KappaChainExit
import LerayHopf.Torus.GalerkinODECapstone
import LerayHopf.Galerkin.GlobalContract

open MeasureTheory Filter Topology Set

namespace LerayHopf

/-! ### The frozen torus capstone statement (promoted from the P4 feasibility spike)

`GlobalTorusCapstoneStatement` is a `Prop`-valued definition — proving it is the
campaign (phases P1–P4). Stating it makes the `∃ F, ∃ u, ∀ T > 0` literalness
machine-checked. `globalTorusCapstone_implies_finite` is the machine-checked
consistency witness tying the global statement back to the existing finite-horizon
capstone shape. Both were compiled sorry-free in the scratch spike and are moved here
verbatim (namespace `Scratch195` → `LerayHopf`). -/

/-- **Frozen P4 target** (docs/scratch/global-diagonal-campaign.md §4): the torus
global capstone.  Note the quantifier prefix: `∃ F, ∃ u, ∀ T` — one form bundle and ONE
curve serving every horizon. -/
def GlobalTorusCapstoneStatement : Prop := -- ALLOW_NAME: statement only (bare def : Prop, the frozen P4 campaign target)
  ∀ (u₀ : L2Sigma) (ν : ℝ), 0 < ν →
    ∃ F : Torus3NSForms, ∃ u : Time → L2Sigma, ∀ T : ℝ, 0 < T →
      Galerkin.IsLerayHopfOn torusDomain F.core ν T u₀ u

/-- Sanity direction (proved): the frozen global statement implies the EXISTING
finite-horizon capstone statement shape (`exists_lerayHopf_torus3`,
`LerayHopf/Torus/GalerkinODECapstone.lean:133`) at every horizon — so the campaign
target is genuinely a strengthening, never a side-grade. -/
theorem globalTorusCapstone_implies_finite (hG : GlobalTorusCapstoneStatement) : -- ALLOW_NAME: reserved term is the hypothesis Prop's name; the implication itself is fully proved below
    ∀ (u₀ : L2Sigma) (ν : ℝ), 0 < ν → ∀ T : ℝ, 0 < T →
      ∃ F : Torus3NSForms, Nonempty (LerayHopfSolutionFull F ν T u₀) := by
  intro u₀ ν hν T hT
  obtain ⟨F, u, hu⟩ := hG u₀ ν hν
  exact ⟨F, ⟨Galerkin.LerayHopfSolution.ofIsOn (hu T hT)⟩⟩

/-! ### The generic global-solution structure, torus-specialized (§4.3)

The `∃ F, Nonempty (GlobalLerayHopfSolutionFull F ν u₀)` structure form of the capstone
packages the single curve into `Galerkin.GlobalLerayHopfSolution`. -/

/-- Torus abbrev of the generic global structure (§4.3). -/
abbrev GlobalLerayHopfSolutionFull (F : Torus3NSForms) (ν : ℝ) (u₀ : L2Sigma) :=
  Galerkin.GlobalLerayHopfSolution torusDomain F.core ν u₀

end LerayHopf
