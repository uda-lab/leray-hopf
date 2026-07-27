-- SCRATCH — issue #195 feasibility spike (lean-architect). NOT production code.
-- Codex pass-2 finding F-B (import-cone separation): the torus instantiation of the
-- global contract, split OUT of Scratch/GlobalContract.lean so that the generic
-- contract layer compiles against `LerayHopf.Galerkin.SolutionBundles` alone while
-- this file adds only the torus lane (`LerayHopf.Torus.SolutionInterfaces`).
-- Compiling the pair proves the frozen P1 design is realizable as specified:
-- generic `LerayHopf/Galerkin/GlobalContract.lean` + torus-side capstone statement.
--
-- `GlobalTorusCapstoneStatement` is a bare `def : Prop` (proving it IS the campaign,
-- phases P1–P4); `globalTorusCapstone_implies_finite` is fully proved.
import LerayHopf.Scratch.GlobalContract
import LerayHopf.Torus.SolutionInterfaces

open MeasureTheory Filter Topology Set

namespace LerayHopf
namespace Scratch195

/-! ### The frozen torus capstone statements (P4 targets)

`Prop`-valued definitions, NOT theorems: proving them is the campaign (phases P1–P4).
Stating them here makes the `∃ u, ∀ T > 0` literalness machine-checked, which is what
the codex gate required of the design phase. -/

/-- **Frozen P4 target** (docs/scratch/global-diagonal-campaign.md §4): the torus
global capstone.  Note the quantifier prefix: `∃ F, ∃ u, ∀ T` — one form bundle and ONE
curve serving every horizon. -/
def GlobalTorusCapstoneStatement : Prop := -- ALLOW_NAME: statement only (bare def : Prop, the unproved P4 campaign target)
  ∀ (u₀ : L2Sigma) (ν : ℝ), 0 < ν →
    ∃ F : Torus3NSForms, ∃ u : Time → L2Sigma, ∀ T : ℝ, 0 < T →
      IsLerayHopfOn torusDomain F.core ν T u₀ u

/-- Sanity direction (proved): the frozen global statement implies the EXISTING
finite-horizon capstone statement shape (`exists_lerayHopf_torus3`,
`LerayHopf/Torus/GalerkinODECapstone.lean:133`) at every horizon — so the campaign
target is genuinely a strengthening, never a side-grade. -/
theorem globalTorusCapstone_implies_finite (hG : GlobalTorusCapstoneStatement) : -- ALLOW_NAME: reserved term is the hypothesis Prop's name; the implication itself is fully proved below, capstone remains unproved
    ∀ (u₀ : L2Sigma) (ν : ℝ), 0 < ν → ∀ T : ℝ, 0 < T →
      ∃ F : Torus3NSForms, Nonempty (LerayHopfSolutionFull F ν T u₀) := by
  intro u₀ ν hν T hT
  obtain ⟨F, u, hu⟩ := hG u₀ ν hν
  exact ⟨F, ⟨LerayHopfSolution.ofIsOn (hu T hT)⟩⟩

end Scratch195
end LerayHopf

-- Axiom pins (recorded in docs/scratch/global-diagonal-campaign.md §10; expected:
-- [propext, Classical.choice, Quot.sound] — no sorryAx, no project axioms).
#print axioms LerayHopf.Scratch195.globalTorusCapstone_implies_finite
