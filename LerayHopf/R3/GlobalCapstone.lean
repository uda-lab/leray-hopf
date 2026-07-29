-- ℝ³ global-in-time Leray–Hopf capstone (parent issue #212; P1′ statement layer #214,
-- P4′ proof assembly #217).
--
-- COMPLETE. This file carries both the frozen P1′ statement layer — the ℝ³ global capstone
-- TARGET `GlobalR3CapstoneStatement`, the generic-structure abbrev, and the machine-checked
-- consistency witness `globalR3Capstone_implies_finite` tying the global statement back to the
-- finite-horizon capstone shape — AND the P4′ (#217) proof assembly that discharges it:
-- `exists_global_lerayHopf_r3`, `exists_globalLerayHopfSolutionFull_r3`, and the frozen-target
-- fold `globalR3Capstone`. The result is global-in-time WEAK (Leray–Hopf) existence on ℝ³: one
-- scheme `𝔊`, one form bundle `F`, and ONE curve satisfying the finite-horizon contract at
-- every `T > 0` — no uniqueness, no smoothness/higher regularity beyond the stated energy
-- class. Kernel-trio only (pinned by scripts/check-axioms-live.sh; scope in docs/claims-and-scope.md).
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
import LerayHopf.R3.DiagonalGalerkin
import LerayHopf.R3.GalerkinODECapstone
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

/-! ### The capstone assembly (P4′; docs/scratch/r3-global-diagonal-campaign.md §2.2 Steps 1–5)

One diagonal family end-to-end: fix the scheme `𝔊 := schemeOfBasis B` (with `htest` from
`nonempty_schwartzGalerkinBasis_H1`), the form bundle `F` (from `r3_NSForms_exists`), the base
Galerkin family `galSeq := galSeq_R3_of_basis B F ν hν u₀`, and the P3′ diagonal + coherence
`(δ, W)` (from `exists_diag_coherent_representative_R3`) ALL ONCE — the concrete construction is
`T`-free, so one scheme/form/curve serves every horizon (§2.1 obligations α/β).  Every
per-horizon `R3KappaChainExitWitness` (P2′ `r3_kappaChain_exit`) runs at `κ := δ` over
`fun k => galSeq (δ k)`, so its Stage-4 pin (against `z : L2VF_R3`, along `w.alPkg.φ`) and the
P3′ diagonal convergence are anchored to the SAME subsequence; the promoted coherence core
identifies `w.v` with `W` on each window from `z : L2VF_R3` tests alone
(`exists_diag_coherent_representative_R3`, itself `L2Sigma_R3_eq_of_forall_inner`), and the
contract transfers via P1's `IsLerayHopfOn.congr_Icc` / `.mono`. -/

/-- **P4′ ℝ³ global capstone (§2.1).**  For any `u₀ ∈ L²_σ(ℝ³)` and `ν > 0` there is a single
scheme `𝔊`, form bundle `F`, and ONE curve `u : Time → L2Sigma_R3` satisfying the finite-horizon
Leray–Hopf contract `IsLerayHopfOn (r3Domain 𝔊) F.core ν T u₀ u` at EVERY horizon `T > 0`.
Node-for-node mirror of the merged torus twin `exists_global_lerayHopf_torus3`
(`LerayHopf/Torus/GlobalCapstone.lean:71`). -/
theorem exists_global_lerayHopf_r3 (u₀ : L2Sigma_R3) (ν : ℝ) (hν : 0 < ν) :
    ∃ (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊), ∃ u : Time → L2Sigma_R3,
      ∀ T : ℝ, 0 < T → Galerkin.IsLerayHopfOn (r3Domain 𝔊) F.core ν T u₀ u := by
  -- Fixed once: the concrete scheme + test data, the form bundle, the base Galerkin family,
  -- and the P3′ diagonal `(δ, W)` with its promoted coherence handle.
  obtain ⟨⟨B, htest⟩⟩ := nonempty_schwartzGalerkinBasis_H1
  obtain ⟨F⟩ := r3_NSForms_exists (schemeOfBasis B)
  have galSeq : ∀ n, GalerkinSolutionData_R3 (schemeOfBasis B) F ν u₀ n :=
    galSeq_R3_of_basis B F ν hν u₀
  obtain ⟨δ, hδ, W, hcoh⟩ :=
    exists_diag_coherent_representative_R3 (schemeOfBasis B) F ν hν u₀ galSeq
  -- Per-horizon contract for the ONE curve `W` at every window `[0, (m:ℝ)+1]`.
  have hhor : ∀ m : ℕ,
      Galerkin.IsLerayHopfOn (r3Domain (schemeOfBasis B)) F.core ν ((m : ℝ) + 1) u₀ W := by
    intro m
    have hTm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    -- Node A: the P2′ exit witness over the diagonal-reindexed family `fun k => galSeq (δ k)`.
    obtain ⟨w⟩ :=
      r3_kappaChain_exit (schemeOfBasis B) F ν hν ((m : ℝ) + 1) hTm u₀ galSeq htest δ hδ
        (fun k => galSeq (δ k))
    -- Node B: the five-conjunct contract for the witness curve `w.v` (evolution / dissip /
    -- regMem specializations are definitional via the `r3Domain_*` `rfl`-lemmas; AESM is
    -- recovered from the package limit along the a.e. link `w.v_ae`).
    have hisv : Galerkin.IsLerayHopfOn (r3Domain (schemeOfBasis B)) F.core ν
        ((m : ℝ) + 1) u₀ w.v := by
      refine ⟨w.weak_eq, w.energy_ineq, w.initial_trace, w.energy_class_v, ?_⟩
      refine w.alPkg.u_aestronglyMeasurable.congr ?_
      filter_upwards [w.v_ae] with t ht
      exact congrArg _ ht.symm
    -- Node C: Step-4 coherence `w.v t = W t` on the window, discharged by the P3′-promoted
    -- coherence handle applied to the exit-witness pin (against `z : L2VF_R3`, along `w.alPkg.φ`,
    -- a sub-extraction of the diagonal `δ`).
    have hcohm : ∀ t ∈ Set.Icc (0 : ℝ) ((m : ℝ) + 1), w.v t = W t :=
      hcoh m w.alPkg.φ w.alPkg.φ_mono w.v w.pin -- KAPPA_ID_SITE: `w.alPkg.φ_mono` is the exit witness's OWN raw extraction monotonicity, supplied as the `StrictMono σ` for the sub-extraction `σ := w.alPkg.φ` along which `w.pin` is ALSO stated (κ is already baked into `galSeq₁ := fun k => galSeq (δ k)`; the pin field pairs against `galSeq₁ (alPkg.φ k)` at the bare `alPkg.φ`, no effective composed index exists at this terminal layer) — pin and σ are the SAME extraction, so no staleness is possible; not a category-(iii) index-selection fact (mirrors DiagonalGalerkin.lean:68)
    -- Node D (per-horizon transfer): move the contract from `w.v` to `W`.
    exact hisv.congr_Icc hTm hcohm
  -- Node D (arbitrary horizon): restrict from the window `[0, ⌊T⌋₊+1] ⊇ [0, T]`.
  refine ⟨schemeOfBasis B, F, W, fun T hT => ?_⟩
  exact (hhor ⌊T⌋₊).mono hT (Nat.lt_floor_add_one T).le

/-- **P4′ ℝ³ global capstone, structure form (§2.1).**  Packages the single global curve into
`Galerkin.GlobalLerayHopfSolution`. -/
theorem exists_globalLerayHopfSolutionFull_r3 (u₀ : L2Sigma_R3) (ν : ℝ) (hν : 0 < ν) :
    ∃ (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊),
      Nonempty (GlobalLerayHopfSolutionFull_R3 𝔊 F ν u₀) := by
  obtain ⟨𝔊, F, u, hu⟩ := exists_global_lerayHopf_r3 u₀ ν hν
  exact ⟨𝔊, F, ⟨⟨u, hu⟩⟩⟩

/-- The frozen `def : Prop` target, proved (defeq fold of `exists_global_lerayHopf_r3`; kernel
trio only). -/
theorem globalR3Capstone : GlobalR3CapstoneStatement := -- ALLOW_NAME: reserved term is the frozen target Prop's name; this declaration is its full proof (defeq fold, kernel-trio pin)
  fun u₀ ν hν => exists_global_lerayHopf_r3 u₀ ν hν

end LerayHopf
