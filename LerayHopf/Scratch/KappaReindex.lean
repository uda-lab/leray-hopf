-- SCRATCH — issue #195 feasibility spike (lean-architect). NOT production code.
-- Resolves the index-dependence obstacle of issue #195 at the API level, against the
-- REAL torus interfaces: the compactness entry point is generalized over a strictly
-- monotone Galerkin index map `κ : ℕ → ℕ` (reindexed family = `galSeq ∘ κ`; subsequent
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
import LerayHopf.Torus.GalerkinODECapstone

open MeasureTheory Filter Topology Set

namespace LerayHopf
namespace Scratch195

/-- **κ-generalized mode-wise extraction** (the κ-version of the production
`exists_galerkin_modewise_extraction`, `ModeCompactness.lean:147`).  The input family
is the reindexed `galSeq ∘ κ` for an arbitrary strictly monotone index map `κ`; the
conclusion extracts `φ` so that the composed index map of the extracted family is
`κ ∘ φ`.

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
two extractions compose to a single strictly monotone index map `φ₁ ∘ φ₂`. -/
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
parameterized by the base sequence AND an index map `κ` (fields byte-identical to the
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
    (p : AubinLionsPackage F ν T u₀ galSeq id) :
    AubinLionsPackageKappa F ν T u₀ galSeq id where
  φ := p.φ
  φ_mono := p.φ_mono
  u := p.u
  strong_convergence := p.strong_convergence
  u_aestronglyMeasurable := p.u_aestronglyMeasurable

/-- Extraction closure at package level: a further strictly monotone extraction `ρ`
of the package's subsequence yields a package over the SAME index map `κ` with
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

/-! ### Codex-gate remediation (finding 2): the LITERAL dependent family shape

`reindexed_family_second_extraction` above still consumes the base `galSeq` plus a map
`φ₁`.  The declarations below consume the literal previously-extracted family type
`∀ k, GalerkinSolutionData F ν u₀ (φ₁ k)` — the exact shape issue #195 names — by
embedding it into a full base family (off-subsequence indices are filled with the
canonical axiom-free `galSeq_of_torus` datum, which exists unconditionally because the
torus Galerkin ODE layer is total) and then reusing the κ-generalized entry point.
This derives the dependent shape FROM the base+κ design rather than re-proving it,
which is the design claim of §3 of the campaign doc made compiled. -/

open Classical in
/-- Embed a dependent reindexed family into a full base family: at `φ₁ k` take the
given datum, elsewhere the canonical `galSeq_of_torus` datum. -/
noncomputable def extendReindexedFamily
    (F : Torus3NSForms) (ν : ℝ) (hν : 0 < ν) (u₀ : L2Sigma)
    (φ₁ : ℕ → ℕ) (galSeq₁ : ∀ k, GalerkinSolutionData F ν u₀ (φ₁ k)) :
    ∀ n, GalerkinSolutionData F ν u₀ n := fun n =>
  if h : ∃ k, φ₁ k = n then (Classical.choose_spec h) ▸ galSeq₁ (Classical.choose h)
  else galSeq_of_torus F ν hν u₀ n

/-- On the subsequence, the embedding restores the given data on the nose (needs only
injectivity of `φ₁`). -/
theorem extendReindexedFamily_apply
    (F : Torus3NSForms) (ν : ℝ) (hν : 0 < ν) (u₀ : L2Sigma)
    (φ₁ : ℕ → ℕ) (hφ₁ : Function.Injective φ₁)
    (galSeq₁ : ∀ k, GalerkinSolutionData F ν u₀ (φ₁ k)) (k : ℕ) :
    extendReindexedFamily F ν hν u₀ φ₁ galSeq₁ (φ₁ k) = galSeq₁ k := by
  have hex : ∃ k', φ₁ k' = φ₁ k := ⟨k, rfl⟩
  have hkk : Classical.choose hex = k := hφ₁ (Classical.choose_spec hex)
  simp only [extendReindexedFamily, dif_pos hex]
  refine eq_of_heq ((eqRec_heq (Classical.choose_spec hex) _).trans ?_)
  rw [hkk]

/-- **Acceptance criterion, literal shape (codex finding 2):** the mode-wise extraction
consumes a previously extracted subsequence given as the DEPENDENT family
`galSeq₁ : ∀ k, GalerkinSolutionData F ν u₀ (φ₁ k)` — no base family in the
hypotheses.  Conclusion as in `reindexed_family_second_extraction`, now phrased
against `galSeq₁` itself. -/
theorem exists_galerkin_modewise_extraction_of_reindexed
    (F : Torus3NSForms) (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T)
    (u₀ : L2Sigma) (φ₁ : ℕ → ℕ) (hφ₁ : StrictMono φ₁)
    (galSeq₁ : ∀ k, GalerkinSolutionData F ν u₀ (φ₁ k))
    (w : ℕ → L2Sigma) (hwtest : ∀ m, IsGalerkinTest (w m)) :
    ∃ φ₂ : ℕ → ℕ, StrictMono φ₂ ∧ StrictMono (φ₁ ∘ φ₂) ∧ ∃ g : ℕ → ℝ → ℝ, ∀ m,
      TendstoUniformlyOn
        (fun k t => inner (𝕜 := ℝ) (((galSeq₁ (φ₂ k)).u t : L2VF)) ((w m : L2VF)))
        (g m) atTop (Icc (0 : ℝ) T) := by
  classical
  obtain ⟨φ₂, hφ₂, g, hg⟩ := exists_galerkin_modewise_extraction_kappa F ν hν T hT u₀
    (extendReindexedFamily F ν hν u₀ φ₁ galSeq₁) φ₁ hφ₁ w hwtest
  refine ⟨φ₂, hφ₂, hφ₁.comp hφ₂, g, fun m => ?_⟩
  have hfun : (fun k t => inner (𝕜 := ℝ)
        (((extendReindexedFamily F ν hν u₀ φ₁ galSeq₁ (φ₁ (φ₂ k))).u t : L2VF))
        ((w m : L2VF)))
      = fun k t => inner (𝕜 := ℝ) (((galSeq₁ (φ₂ k)).u t : L2VF)) ((w m : L2VF)) := by
    funext k t
    rw [extendReindexedFamily_apply F ν hν u₀ φ₁ hφ₁.injective galSeq₁ (φ₂ k)]
  exact hfun ▸ hg m

/-! ### Codex-gate remediation (finding 3): effective-map strictness/cofinality

The absolute mode index of the κ-package is `κ (p.φ n)`.  `hκ : StrictMono κ` stays a
SIDE hypothesis (not a structure field: the `κ = id` instance must remain
definitionally transparent for existing consumers, and Prop-fields would change the
constructor arity P2 wants byte-stable).  The lemmas below thread it through
composition, including through `extract`, so every consumer has the strict/cofinal
effective map on demand. -/

/-- The composed index map `κ ∘ φ` of a κ-package is strictly monotone. -/
theorem AubinLionsPackageKappa.effective_strictMono {F : Torus3NSForms} {ν T : ℝ}
    {u₀ : L2Sigma} {galSeq : ∀ n, GalerkinSolutionData F ν u₀ n} {κ : ℕ → ℕ}
    (p : AubinLionsPackageKappa F ν T u₀ galSeq κ) (hκ : StrictMono κ) :
    StrictMono (fun n => κ (p.φ n)) :=
  hκ.comp p.φ_mono

/-- The composed index map `κ ∘ φ` is cofinal (escapes to `atTop`) — the form in which
the eventual band-limit cutoffs (`n₀ ≤ κ (φ N)`) are discharged. -/
theorem AubinLionsPackageKappa.effective_tendsto_atTop {F : Torus3NSForms} {ν T : ℝ}
    {u₀ : L2Sigma} {galSeq : ∀ n, GalerkinSolutionData F ν u₀ n} {κ : ℕ → ℕ}
    (p : AubinLionsPackageKappa F ν T u₀ galSeq κ) (hκ : StrictMono κ) :
    Filter.Tendsto (fun n => κ (p.φ n)) Filter.atTop Filter.atTop :=
  (p.effective_strictMono hκ).tendsto_atTop

/-- `extract` composes the position map on the nose. -/
@[simp] theorem AubinLionsPackageKappa.extract_φ {F : Torus3NSForms} {ν T : ℝ}
    {u₀ : L2Sigma} {galSeq : ∀ n, GalerkinSolutionData F ν u₀ n} {κ : ℕ → ℕ}
    (p : AubinLionsPackageKappa F ν T u₀ galSeq κ) (ρ : ℕ → ℕ) (hρ : StrictMono ρ) :
    (p.extract ρ hρ).φ = p.φ ∘ ρ := rfl

/-- Strictness of the effective map survives package-level extraction. -/
theorem AubinLionsPackageKappa.extract_effective_strictMono {F : Torus3NSForms}
    {ν T : ℝ} {u₀ : L2Sigma} {galSeq : ∀ n, GalerkinSolutionData F ν u₀ n} {κ : ℕ → ℕ}
    (p : AubinLionsPackageKappa F ν T u₀ galSeq κ) (hκ : StrictMono κ)
    (ρ : ℕ → ℕ) (hρ : StrictMono ρ) :
    StrictMono (fun k => κ ((p.extract ρ hρ).φ k)) :=
  hκ.comp (p.φ_mono.comp hρ)

end Scratch195
end LerayHopf

-- Axiom pins (recorded in docs/scratch/global-diagonal-campaign.md §10; expected:
-- at most [propext, Classical.choice, Quot.sound] — no sorryAx, no project axioms).
-- COMPLETE enumeration of top-level declarations (#212 B0 pass-4 finding 3: the
-- checker now asserts source-manifest/pin-set equality, so every declaration in this
-- file must carry a pin).
#print axioms LerayHopf.Scratch195.exists_galerkin_modewise_extraction_kappa
#print axioms LerayHopf.Scratch195.reindexed_family_second_extraction
#print axioms LerayHopf.Scratch195.AubinLionsPackageKappa
#print axioms LerayHopf.Scratch195.AubinLionsPackageKappa.ofId
#print axioms LerayHopf.Scratch195.AubinLionsPackageKappa.extract
#print axioms LerayHopf.Scratch195.extendReindexedFamily
#print axioms LerayHopf.Scratch195.extendReindexedFamily_apply
#print axioms LerayHopf.Scratch195.exists_galerkin_modewise_extraction_of_reindexed
#print axioms LerayHopf.Scratch195.AubinLionsPackageKappa.effective_strictMono
#print axioms LerayHopf.Scratch195.AubinLionsPackageKappa.effective_tendsto_atTop
#print axioms LerayHopf.Scratch195.AubinLionsPackageKappa.extract_φ
#print axioms LerayHopf.Scratch195.AubinLionsPackageKappa.extract_effective_strictMono
