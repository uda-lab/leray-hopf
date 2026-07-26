-- SCRATCH — issue #195 feasibility spike (lean-architect). NOT production code.
-- Resolves the index-dependence obstacle of issue #195 at the API level, against the
-- REAL torus interfaces: the compactness entry point is generalized over a strictly
-- monotone Galerkin mode map `κ : ℕ → ℕ` (reindexed family = `galSeq ∘ κ`; subsequent
-- extraction = composition `κ ∘ φ`), and then *instantiated with a previously
-- extracted subsequence* — the exact `∀ k, GalerkinSolutionData F ν u₀ (φ k)` shape
-- the issue identifies as unusable by the current fixed-index builders.
--
-- Design decision demonstrated here (docs/scratch/global-diagonal-campaign.md, §4):
-- the generalized theorems keep the BASE sequence `galSeq : ∀ n, GalerkinSolutionData
-- F ν u₀ n` as a parameter and add `(κ, hκ : StrictMono κ)`, rather than abstracting
-- to a free-standing family `∀ k, GalerkinSolutionData F ν u₀ (κ k)`.  This way every
-- per-datum leaf (`galerkin_u_norm_le`, `galerkin_u_continuousOn`) and every
-- cutoff-quantified leaf (`galerkin_test_pairing_lipschitz`, `∀ n ≥ n₀` over base
-- indices) applies UNCHANGED — only the index argument moves from `φ n` to `κ (φ n)`.
-- All declarations below are fully proved (no sorry, no axioms).
import LerayHopf.Torus.ModeCompactness

open MeasureTheory Filter Topology Set

namespace LerayHopf
namespace Scratch195

/-- **κ-generalized mode-wise extraction** (the κ-version of the production
`exists_galerkin_modewise_extraction`, `ModeCompactness.lean:147`).  The input family
is the reindexed `galSeq ∘ κ` for an arbitrary strictly monotone mode map `κ`; the
conclusion extracts `φ` so that the effective mode map of the extracted family is the
composition `κ ∘ φ`.

Proof = the production body with the datum index threaded through `κ`:
- band-limit cutoffs and Lipschitz constants come from the UNCHANGED base-sequence
  leaf `galerkin_test_pairing_lipschitz` (its `∀ n, m ≤ n → …` form composes with
  reindexing: `m ≤ n ≤ κ n` via `StrictMono.le_apply`);
- the uniform bound is the UNCHANGED per-datum leaf `galerkin_u_norm_le` at index `κ n`;
- the scalar equicontinuity engine `exists_uniform_subseq_of_lipschitz_family` is
  index-agnostic. -/
theorem exists_galerkin_modewise_extraction_kappa
    (F : Torus3NSForms) (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T)
    (u₀ : L2Sigma) (galSeq : ∀ n, GalerkinSolutionData F ν u₀ n)
    (κ : ℕ → ℕ) (hκ : StrictMono κ)
    (w : ℕ → L2Sigma) (hwtest : ∀ m, IsGalerkinTest (w m)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : ℕ → ℝ → ℝ, ∀ m,
      TendstoUniformlyOn
        (fun n t => inner (𝕜 := ℝ) (((galSeq (κ (φ n))).u t : L2VF)) ((w m : L2VF)))
        (g m) atTop (Icc (0 : ℝ) T) := by
  classical
  -- Per-test band-limit cutoff from `IsGalerkinTest` (as in the production body).
  have hcut : ∀ m, velocityProjection_n (Classical.choose (hwtest m)) ((w m : L2Sigma) : L2VF)
      = ((w m : L2Sigma) : L2VF) := fun m => Classical.choose_spec (hwtest m)
  -- Per-test Lipschitz constants from the UNCHANGED base-sequence leaf; it fires for
  -- every base index past the cutoff, in particular for `κ n` when `cutoff ≤ n`.
  choose L hL using fun m =>
    galerkin_test_pairing_lipschitz F ν hν u₀ galSeq (w m) (Classical.choose (hwtest m)) (hcut m)
  -- The engine over `f m n t := ⟪u_{κ(n)}(t), w m⟫`.
  obtain ⟨φ, hφ, hconv⟩ := exists_uniform_subseq_of_lipschitz_family T hT
    (fun m n t => inner (𝕜 := ℝ) (((galSeq (κ n)).u t : L2VF)) ((w m : L2VF)))
    (fun m => ‖(u₀ : L2VF)‖ * ‖((w m : L2Sigma) : L2VF)‖) L
    (fun m n t ht =>
      le_trans (abs_real_inner_le_norm _ _)
        (mul_le_mul_of_nonneg_right (galerkin_u_norm_le F ν u₀ (κ n) (galSeq (κ n)) t ht.1)
          (norm_nonneg _)))
    (fun m => ⟨Classical.choose (hwtest m), fun n hn s t hs ht hst =>
      hL m (κ n) (le_trans hn hκ.le_apply) s t hs.1 hst⟩)
  choose g hg using hconv
  exact ⟨φ, hφ, g, hg⟩

/-- **Acceptance-criterion demo (issue #195):** the generalized compactness interface
is instantiated with a *previously extracted subsequence*.  Given any earlier
extraction `φ₁` (so the family at hand has the reindexed type
`∀ k, GalerkinSolutionData F ν u₀ (φ₁ k)` — the exact shape the current fixed-index
builders cannot consume), a second mode-wise extraction is performed on it, and the
two extractions compose to a single strictly monotone mode map `φ₁ ∘ φ₂`. -/
theorem reindexed_family_second_extraction
    (F : Torus3NSForms) (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T)
    (u₀ : L2Sigma) (galSeq : ∀ n, GalerkinSolutionData F ν u₀ n)
    (φ₁ : ℕ → ℕ) (hφ₁ : StrictMono φ₁)
    (w : ℕ → L2Sigma) (hwtest : ∀ m, IsGalerkinTest (w m)) :
    ∃ φ₂ : ℕ → ℕ, StrictMono φ₂ ∧ StrictMono (φ₁ ∘ φ₂) ∧ ∃ g : ℕ → ℝ → ℝ, ∀ m,
      TendstoUniformlyOn
        (fun k t => inner (𝕜 := ℝ) (((galSeq (φ₁ (φ₂ k))).u t : L2VF)) ((w m : L2VF)))
        (g m) atTop (Icc (0 : ℝ) T) := by
  obtain ⟨φ₂, hφ₂, g, hg⟩ :=
    exists_galerkin_modewise_extraction_kappa F ν hν T hT u₀ galSeq φ₁ hφ₁ w hwtest
  exact ⟨φ₂, hφ₂, hφ₁.comp hφ₂, g, hg⟩

/-- Shape-check for the Phase-P2 signature design: the `AubinLionsPackage` structure
parameterized by the base sequence AND a mode map `κ` (fields byte-identical to the
production structure except `galSeq (φ n)` ↦ `galSeq (κ (φ n))`). -/
structure AubinLionsPackageKappa (F : Torus3NSForms) (ν T : ℝ) (u₀ : L2Sigma)
    (galSeq : ∀ n, GalerkinSolutionData F ν u₀ n) (κ : ℕ → ℕ) where
  /-- The strictly monotone extraction index (positions within the κ-family). -/
  φ : ℕ → ℕ
  /-- Strict monotonicity of `φ`. -/
  φ_mono : StrictMono φ
  /-- The limit curve. -/
  u : Time → L2Sigma
  /-- Strong `L²(0,T; L²_σ)` convergence of the extracted κ-subsequence. -/
  strong_convergence :
    Filter.Tendsto
      (fun n => MeasureTheory.eLpNorm
        (fun t => ((galSeq (κ (φ n))).u t : L2VF) - (u t : L2VF))
        2 (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)))
      Filter.atTop (nhds 0)
  /-- AE strong measurability of the limit curve on `[0, T]`. -/
  u_aestronglyMeasurable :
    AEStronglyMeasurable (fun t => (u t : L2VF))
      (MeasureTheory.volume.restrict (Set.Icc 0 T))

/-- κ = id embedding: the production `AubinLionsPackage` is definitionally the
identity-mode-map instance (every field transfers verbatim), so existing consumers
keep working after the P2 rewiring. -/
def AubinLionsPackageKappa.ofId {F : Torus3NSForms} {ν T : ℝ} {u₀ : L2Sigma}
    {galSeq : ∀ n, GalerkinSolutionData F ν u₀ n}
    (p : AubinLionsPackage F ν T u₀ galSeq) :
    AubinLionsPackageKappa F ν T u₀ galSeq id where
  φ := p.φ
  φ_mono := p.φ_mono
  u := p.u
  strong_convergence := p.strong_convergence
  u_aestronglyMeasurable := p.u_aestronglyMeasurable

/-- Extraction closure at package level: a further strictly monotone extraction `ρ`
of the package's subsequence yields a package over the SAME mode map `κ` with
extraction `φ ∘ ρ` — strong convergence restricts to subsequences. -/
def AubinLionsPackageKappa.extract {F : Torus3NSForms} {ν T : ℝ} {u₀ : L2Sigma}
    {galSeq : ∀ n, GalerkinSolutionData F ν u₀ n} {κ : ℕ → ℕ}
    (p : AubinLionsPackageKappa F ν T u₀ galSeq κ)
    (ρ : ℕ → ℕ) (hρ : StrictMono ρ) :
    AubinLionsPackageKappa F ν T u₀ galSeq κ where
  φ := p.φ ∘ ρ
  φ_mono := p.φ_mono.comp hρ
  u := p.u
  strong_convergence := p.strong_convergence.comp hρ.tendsto_atTop
  u_aestronglyMeasurable := p.u_aestronglyMeasurable

end Scratch195
end LerayHopf
