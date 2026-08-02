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

/-! ### The capstone assembly (§2 Steps 3–5)

One diagonal family end-to-end: fix `F`, `galSeq`, and the P3 diagonal `(δ, W)` ONCE;
every per-horizon `P2ExitWitness` runs at `κ := δ` over `fun k => galSeq (δ k)`, so the
Stage-4 pin and the P3 diagonal convergence are anchored to the same subsequence and
`tendsto_nhds_unique` identifies `w.v` with `W` on each window from `z : L2Sigma` tests
alone (`L2Sigma_eq_of_forall_inner`). -/

/-- **P4 capstone (§4.4).** -/
theorem exists_global_lerayHopf_torus3 (u₀ : L2Sigma) (ν : ℝ) (hν : 0 < ν) :
    ∃ F : Torus3NSForms, ∃ u : Time → L2Sigma, ∀ T : ℝ, 0 < T →
      Galerkin.IsLerayHopfOn torusDomain F.core ν T u₀ u := by
  -- Fixed once: the form bundle, the base Galerkin family, and the P3 diagonal.
  obtain ⟨F⟩ := torus3_NSForms_exists
  have galSeq : ∀ n, GalerkinSolutionData F ν u₀ n := galSeq_of_torus F ν hν u₀
  obtain ⟨δ, hδ, W, hW⟩ := exists_diagonal_weakly_convergent_galSeq F ν hν u₀ galSeq
  -- Per-horizon contract for the ONE curve `W` at every window `[0, (m:ℝ)+1]`.
  have hhor : ∀ m : ℕ, Galerkin.IsLerayHopfOn torusDomain F.core ν ((m : ℝ) + 1) u₀ W := by
    intro m
    have hTm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    -- Node A: the P2 exit witness over the diagonal-reindexed family.
    obtain ⟨w⟩ :=
      torus_kappaChain_exit F ν hν ((m : ℝ) + 1) hTm u₀ δ hδ (fun k => galSeq (δ k))
    -- Node B: the five-conjunct contract for the witness curve `w.v`
    -- (evolution / dissip / regMem specializations are definitional; AESM is
    -- recovered from the package limit along the a.e. link `w.v_ae`).
    have hisv : Galerkin.IsLerayHopfOn torusDomain F.core ν ((m : ℝ) + 1) u₀ w.v := by
      refine ⟨w.weak_eq, w.energy_ineq, w.initial_trace, w.energy_class_v, ?_⟩
      refine w.alPkg.u_aestronglyMeasurable.congr ?_
      filter_upwards [w.v_ae] with t ht
      exact congrArg _ ht.symm
    -- Node C: Step-4 coherence `w.v t = W t` on the window, from `z : L2Sigma`
    -- tests only — both are limits of the SAME diagonal pairing subsequence.
    have hcoh : ∀ t ∈ Set.Icc (0 : ℝ) ((m : ℝ) + 1), w.v t = W t := by
      intro t ht
      have hg : StrictMono (w.alPkg.φ ∘ w.ρ) := w.alPkg.φ_mono.comp w.ρ_mono
      apply L2Sigma_eq_of_forall_inner
      intro z
      have hWz := (hW m t ht z).comp hg.tendsto_atTop
      have hpz := w.pin t ht (z : L2VF)
      exact tendsto_nhds_unique hpz hWz
    -- Node D (per-horizon transfer): move the contract from `w.v` to `W`.
    exact hisv.congr_Icc hTm hcoh
  -- Node D (arbitrary horizon): restrict from the window `[0, ⌊T⌋₊+1] ⊇ [0, T]`.
  refine ⟨F, W, fun T hT => ?_⟩
  exact (hhor ⌊T⌋₊).mono hT (Nat.lt_floor_add_one T).le

/-- **P4 capstone, structure form (§4.4).** -/
theorem exists_globalLerayHopfSolutionFull_torus3 (u₀ : L2Sigma) (ν : ℝ) (hν : 0 < ν) :
    ∃ F : Torus3NSForms, Nonempty (GlobalLerayHopfSolutionFull F ν u₀) := by
  obtain ⟨F, u, hu⟩ := exists_global_lerayHopf_torus3 u₀ ν hν
  exact ⟨F, ⟨⟨u, hu⟩⟩⟩

/-- The frozen `def : Prop` target, proved (Q1 defeq fold). -/
theorem globalTorusCapstone : GlobalTorusCapstoneStatement := -- ALLOW_NAME: reserved term is the frozen target Prop's name; this declaration is its full proof (Q1 defeq fold, kernel-trio pin)
  fun u₀ ν hν => exists_global_lerayHopf_torus3 u₀ ν hν

end LerayHopf
