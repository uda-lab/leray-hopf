-- SCRATCH — issue #212 B0 production-coupling probes (codex statement-gate pass-5
-- findings 1+2; docs/scratch/r3-global-diagonal-campaign.md §4.1/§6 clause 6, §11.5).
-- NOT production code.
--
-- WHAT THIS FILE IS.  The round-4 mirror (`R3ShapeGate.lean`) freezes the P2′ design
-- and compiles it against the merged interfaces, but by itself it never APPLIES a
-- production declaration — production could drift (or stay bare-indexed) while the
-- mirror probes stay green (round-5 findings 1 and 2).  This module closes that gap
-- with probes that CONSUME the actual production declarations, compiled TODAY at the
-- κ-less production surface (the κ-threaded production layers do not exist until P2′):
--
--   * `AubinLionsPackage_R3.ofProduction` / `.toProduction` — bidirectional
--     field-by-field bridges between the production package and the frozen mirror at
--     `κ := id`.  `ofProduction` fails to compile if any mirror field is absent from or
--     type-drifted in production; `toProduction` fails if production grows a field the
--     mirror lacks.  Together: field-set + field-type equality, up to the single
--     designed change `galSeq (φ n)` ↦ `galSeq (κ (φ n))` (`id (φ n)` ≡ `φ n` defeq).
--   * `r3LimitPassage_production_exact_shape` — BARE APPLICATION of the actual
--     `galerkin_limit_passage_R3`, its current 5-conjunct conclusion restated verbatim.
--   * `r3LimitPassagePin_production_source` — consumes the actual
--     `exists_weak_representative_R3` (the declaration `galerkin_limit_passage_R3`
--     itself draws its representative from — the pin's production source) and lands its
--     weak-convergence conjunct in the frozen `R3LimitPassagePinConjunct` at
--     `κ := id` via the compiled `ofProduction` bridge: the pin conjunct is
--     production-DERIVABLE today, in frozen-Prop form, not just frozen prose.
--   * `r3Production_diag_ae_subseq_exact_shape` / `…_u_lim_aestronglyMeasurable_…` /
--     `…_galerkinSpaceTimeExtraction_…` — BARE APPLICATIONS of the actual sealed
--     layer-1/2 production declarations, conclusions restated verbatim (round-5
--     finding 2: production probing, counted separately from the standalone seeded
--     feasibility proofs in `R3KappaSeed.lean`).
--   * `diag_ae_subseq_seeded_id_recovers_production` /
--     `spacetime_extraction_seeded_id_recovers_production` — the SEEDED κ-generic
--     statements instantiated at `κ := id` prove the production conclusions verbatim:
--     the frozen κ-generalizations are conservative over today's production shapes.
--   * `diag_ae_subseq_seeded_free_kappa_exact_shape` /
--     `spacetime_extraction_seeded_free_kappa_exact_shape` — the seeded κ-generic
--     conclusions RESTATED VERBATIM with κ FREE, proved by direct application of the
--     seeded theorems at that free `κ`/`hκ` (round-6 finding 2).  The id-coherence
--     probes above would still elaborate if the seeded statements were ever weakened
--     to ignore `κ` while keeping an `id`-specializable form; for a FREE `κ`,
--     `galSeq (φ n)` does not unify with `galSeq (κ (φ n))`, so these two probes fail
--     to elaborate under any κ-dropping weakening.  Their conclusion texts are the
--     SAME frozen texts the P2′-only couplings below carry — compiled today.
--
-- P2′ RE-POINT LIFECYCLE (§6 clause 6; deviation = kill-criterion event):
--   * DELETED with the mirror: `ofProduction`, `toProduction`,
--     `r3LimitPassagePin_production_source` (the κ-less production package they bridge
--     ceases to exist once P2′ rewires it to the κ-form).
--   * STATEMENTS FROZEN, proof term gains `id strictMono_id` only: the three
--     layer-1/2 bare-application probes and `r3LimitPassage_production_exact_shape`…
--     EXCEPT that `r3LimitPassage_production_exact_shape` is REPLACED by the
--     strengthened coupling below — the ONE sanctioned statement replacement.
--   * ADDED at P2′ (texts frozen NOW; commented out because production lacks κ /
--     the pin conjunct today — that lack is precisely what they will detect):
--
--       theorem r3LimitPassage_strengthened_production_coupling
--           (… production argument list …) (κ : ℕ → ℕ) (hκ : StrictMono κ)
--           (p : AubinLionsPackage_R3 𝔊 F ν T u₀ galSeq κ) (htest : R3TestApproxH1 𝔊) :
--           R3StrengthenedLimitPassageConclusion 𝔊 F ν T u₀ galSeq κ p :=
--         galerkin_limit_passage_R3 … κ hκ p htest
--
--       theorem r3Production_diag_ae_subseq_kappa_coupling
--           (… production argument list …) (κ : ℕ → ℕ) (hκ : StrictMono κ) :
--           «the exact `diag_ae_subseq_seeded` conclusion» :=
--         diag_ae_subseq 𝔊 F ν hν T hT u₀ galSeq κ hκ
--
--       theorem r3Production_spacetime_extraction_kappa_coupling
--           (… production argument list …) (κ : ℕ → ℕ) (hκ : StrictMono κ) :
--           «the exact `spacetime_extraction_seeded` conclusion» :=
--         galerkinSpaceTimeExtraction_R3 𝔊 F ν hν T hT u₀ galSeq B κ hκ
--
--     (bare applications; only the production argument-list spelling is a P2′ freedom).
--   * REPLACED at P2′ by the two κ-generic couplings just above (δ, round-6
--     finding 2): `diag_ae_subseq_seeded_free_kappa_exact_shape` /
--     `spacetime_extraction_seeded_free_kappa_exact_shape` — conclusion texts frozen
--     VERBATIM; the only sanctioned change is the proof head swapping from the
--     scratch seeds to the κ-threaded production declarations (plus the coupling
--     names above).  Any other edit to those conclusion texts = kill-criterion event.
--     MACHINE-ENFORCED since pass-7 (round-7 finding 3; head semantics at
--     round-8 finding 3; extended to EVERY declaration of this module at
--     round-9 finding 2): the static gate reader (`scripts/scratch_reader.lean`)
--     carries an 11-entry proof-value pin table — each probe's PROOF TERM,
--     hypothesis binders stripped, must have its pinned constant as the
--     APPLICATION HEAD (`DEPGUARD|…|head`): the ACTUAL production declarations
--     for the four exact-shape probes, the SEEDS for the id-coherence and
--     free-κ probes, the `mk` constructors for the two bridges; the one
--     destructuring proof (`r3LimitPassagePin_production_source`) is pinned by
--     direct reference (`DEPGUARD|…|uses`) to `exists_weak_representative_R3`.
--     A probe silently re-proved from the wrong side (e.g. an exact-shape probe
--     re-proved from a seed at `id`) fails the gate even with an identical
--     statement digest and axiom closure.  The P2′ re-point must therefore
--     update, in the SAME reviewed diff: these proof heads, the reader's pin
--     table (deleted probes lose pins; free-κ guard heads swap to the
--     κ-threaded production declarations; exact-shape probes keep production
--     heads, their proofs gaining `id strictMono_id` only), the checker's
--     DEPGUARD assertion lines, and `scripts/scratch-manifest.expected` (which
--     also freezes every statement here by sha-256 canonical digest).
--     Forgetting any of the four breaks the gate loudly.
-- All declarations below are fully proved (no sorry, no axioms, no `by` beyond
-- destructuring — every probe is a bare application or field-by-field projection).
import LerayHopf.R3.LimitPassage
import LerayHopf.R3.SteklovAverages
import LerayHopf.Scratch.R3ShapeGate
import LerayHopf.Scratch.R3KappaSeed

open MeasureTheory Filter Topology Set

namespace LerayHopf
namespace Scratch212

/-! ### Mirror ↔ production package bridges (`κ := id`) -/

/-- **Production → mirror bridge.**  Every field of the frozen mirror package is the
corresponding field of the ACTUAL production `LerayHopf.AubinLionsPackage_R3`,
projected verbatim (`id (φ n)` unifies with `φ n` definitionally).  Compiles only
while the mirror's field set and field types match production's, up to the single
designed κ-insertion — production field drift breaks this bridge at B0, before P2′. -/
def AubinLionsPackage_R3.ofProduction
    {𝔊 : R3GalerkinScheme} {F : R3NSForms 𝔊} {ν T : ℝ} {u₀ : L2Sigma_R3}
    {galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n}
    (p : _root_.LerayHopf.AubinLionsPackage_R3 𝔊 F ν T u₀ galSeq) :
    AubinLionsPackage_R3 𝔊 F ν T u₀ galSeq id where
  φ := p.φ
  φ_mono := p.φ_mono
  u := p.u
  u_aestronglyMeasurable := p.u_aestronglyMeasurable
  strong_convergence := p.strong_convergence
  strong_convergence_ae := p.strong_convergence_ae

/-- **Mirror → production bridge** (converse direction): a mirror package at `κ := id`
rebuilds the production package field-by-field.  Compiles only while production has NO
field the mirror lacks — a field silently added to production (which consumers might
then take bare-indexed) breaks this bridge at B0. -/
def AubinLionsPackage_R3.toProduction
    {𝔊 : R3GalerkinScheme} {F : R3NSForms 𝔊} {ν T : ℝ} {u₀ : L2Sigma_R3}
    {galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n}
    (p : AubinLionsPackage_R3 𝔊 F ν T u₀ galSeq id) :
    _root_.LerayHopf.AubinLionsPackage_R3 𝔊 F ν T u₀ galSeq where
  φ := p.φ
  φ_mono := p.φ_mono
  u := p.u
  u_aestronglyMeasurable := p.u_aestronglyMeasurable
  strong_convergence := p.strong_convergence
  strong_convergence_ae := p.strong_convergence_ae

/-! ### Limit-passage production coupling (round-5 finding 1) -/

/-- **Production consumption probe** — bare application of the ACTUAL
`galerkin_limit_passage_R3`, its current 5-conjunct conclusion restated verbatim
(transcribed from `LerayHopf/R3/LimitPassage.lean`).  Detects any drift of the
production limit-passage surface between B0 and the P2′ strengthening.  At P2′ this
probe is REPLACED by `r3LimitPassage_strengthened_production_coupling` (frozen text in
the header above and §6) — the one sanctioned statement replacement. -/
theorem r3LimitPassage_production_exact_shape
    (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T)
    (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n)
    (alPkg : _root_.LerayHopf.AubinLionsPackage_R3 𝔊 F ν T u₀ galSeq)
    (htest : R3TestApproxH1 𝔊) :
    ∃ u : Time → L2Sigma_R3,
    (∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc 0 T)), u t = alPkg.u t) ∧
    WeakFormNS ν T (r3Evolution 𝔊 F) u ∧
    (∀ t, 0 ≤ t → t ≤ T →
      (1 / 2 : ℝ) * ‖(u t : L2VF_R3)‖ ^ 2 +
      ∫ s in (0 : ℝ)..t, viscousFormSq_R3 ν (u s : L2VF_R3) ≤
      (1 / 2 : ℝ) * ‖(u₀ : L2VF_R3)‖ ^ 2) ∧
    Filter.Tendsto
      (fun t => (u t : L2VF_R3))
      (nhdsWithin 0 (Set.Ici 0))
      (nhds (u₀ : L2VF_R3)) ∧
    ((∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc 0 T)), memH1VF_R3 (u t : L2VF_R3)) ∧
    IntervalIntegrable (fun s => viscousFormSq_R3 ν (u s : L2VF_R3))
      MeasureTheory.volume 0 T) :=
  galerkin_limit_passage_R3 𝔊 F ν hν T hT u₀ galSeq alPkg htest

/-- **Pin-source production coupling** — consumes the ACTUAL
`exists_weak_representative_R3` (the production declaration whose representative and
weak-convergence conjunct `galerkin_limit_passage_R3` assembles into its conclusion)
and PROJECTS its weak-convergence conjunct into the frozen `R3LimitPassagePinConjunct`
at `κ := id`, through the compiled `ofProduction` bridge.  This is the round-5
finding-1 obligation compilable today: the pin conjunct P2′ must append is derivable
from production machinery NOW, and lands in the frozen Prop by definitional
unfolding alone (no rewriting). -/
theorem r3LimitPassagePin_production_source
    (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T) (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n)
    (alPkg : _root_.LerayHopf.AubinLionsPackage_R3 𝔊 F ν T u₀ galSeq) :
    ∃ v : Time → L2Sigma_R3,
      R3LimitPassagePinConjunct 𝔊 F ν T u₀ galSeq id
        (AubinLionsPackage_R3.ofProduction alPkg) v := by
  obtain ⟨v, -, hweak, -, -, -⟩ :=
    exists_weak_representative_R3 𝔊 F ν hν T hT u₀ galSeq alPkg
  exact ⟨v, hweak⟩

/-! ### Layer-1/2 production coupling (round-5 finding 2) -/

/-- **Layer-1 production consumption probe** — bare application of the ACTUAL
`diag_ae_subseq` (`R3/ArzelaAscoliTime.lean`), conclusion restated verbatim.  At P2′
(κ-threaded production layer) the statement stays FROZEN and the proof term gains
`id strictMono_id`; the κ-generic coupling `r3Production_diag_ae_subseq_kappa_coupling`
(frozen text in the header) is added alongside. -/
theorem r3Production_diag_ae_subseq_exact_shape
    (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T) (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n) :
    ∃ (φ : ℕ → ℕ),
      StrictMono φ ∧
      ∀ k : ℕ, ∃ g_k : ℝ → L2ballR3 k,
        AEStronglyMeasurable g_k (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)) ∧
        ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)),
          Filter.Tendsto
            (fun n => restrictToBall k ((galSeq (φ n)).u t : L2VF_R3))
            Filter.atTop (nhds (g_k t)) :=
  diag_ae_subseq 𝔊 F ν hν T hT u₀ galSeq

/-- **Layer-2 production consumption probe** — bare application of the ACTUAL
`u_lim_aestronglyMeasurable` (`R3/ArzelaAscoliTime.lean`), conclusion restated
verbatim (`B : LocalRellichInput` is a category-(v) index-free ambient input). -/
theorem r3Production_u_lim_aestronglyMeasurable_exact_shape
    (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T) (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n)
    (B : LocalRellichInput) :
    ∃ (φ : ℕ → ℕ) (u : Time → L2Sigma_R3),
      StrictMono φ ∧
      AEStronglyMeasurable (fun t => (u t : L2VF_R3))
        (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)) ∧
      ∀ R : ℝ, ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)),
        Filter.Tendsto (fun n => restrictToBall R ((galSeq (φ n)).u t : L2VF_R3))
          Filter.atTop (nhds (restrictToBall R (u t : L2VF_R3))) :=
  u_lim_aestronglyMeasurable 𝔊 F ν hν T hT u₀ galSeq B

/-- **Layer-2 (sealed-surface) production consumption probe** — bare application of
the ACTUAL `galerkinSpaceTimeExtraction_R3` (`R3/SteklovAverages.lean`), conclusion
restated verbatim.  This is the named sealed-layer surface the P2′ κ-threading must
generalize (campaign doc §4 layer table). -/
theorem r3Production_galerkinSpaceTimeExtraction_exact_shape
    (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T)
    (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n)
    (B : LocalRellichInput) :
    ∃ (φ : ℕ → ℕ) (u : Time → L2Sigma_R3), StrictMono φ ∧
      AEStronglyMeasurable (fun t => (u t : L2VF_R3))
        (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)) ∧
      (∀ R : ℝ, ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)),
        Filter.Tendsto (fun n => restrictToBall R ((galSeq (φ n)).u t : L2VF_R3)) Filter.atTop
          (nhds (restrictToBall R (u t : L2VF_R3)))) :=
  galerkinSpaceTimeExtraction_R3 𝔊 F ν hν T hT u₀ galSeq B

/-- **Seed ↔ production coherence, layer 1** — the frozen κ-generic
`diag_ae_subseq_seeded` statement instantiated at `κ := id` proves the production
`diag_ae_subseq` conclusion VERBATIM (definitional `id`-collapse only): the seeded
generalization is conservative over today's production shape, so the P2′ κ-threading
is exactly the frozen seed statement, not a redesign. -/
theorem diag_ae_subseq_seeded_id_recovers_production
    (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T) (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n) :
    ∃ (φ : ℕ → ℕ),
      StrictMono φ ∧
      ∀ k : ℕ, ∃ g_k : ℝ → L2ballR3 k,
        AEStronglyMeasurable g_k (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)) ∧
        ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)),
          Filter.Tendsto
            (fun n => restrictToBall k ((galSeq (φ n)).u t : L2VF_R3))
            Filter.atTop (nhds (g_k t)) :=
  diag_ae_subseq_seeded 𝔊 F ν hν T hT u₀ galSeq id strictMono_id

/-- **Seed ↔ production coherence, layer 2** — `spacetime_extraction_seeded` at
`κ := id` proves the production `galerkinSpaceTimeExtraction_R3` conclusion
VERBATIM (same mechanism as layer 1). -/
theorem spacetime_extraction_seeded_id_recovers_production
    (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T) (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n) :
    ∃ (φ : ℕ → ℕ) (u : Time → L2Sigma_R3), StrictMono φ ∧
      AEStronglyMeasurable (fun t => (u t : L2VF_R3))
        (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)) ∧
      (∀ R : ℝ, ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)),
        Filter.Tendsto (fun n => restrictToBall R ((galSeq (φ n)).u t : L2VF_R3)) Filter.atTop
          (nhds (restrictToBall R (u t : L2VF_R3)))) :=
  spacetime_extraction_seeded 𝔊 F ν hν T hT u₀ galSeq id strictMono_id

/-! ### Seed free-κ statement guards (round-6 finding 2) -/

/-- **Free-κ statement guard, layer 1** — the `diag_ae_subseq_seeded` conclusion
RESTATED VERBATIM with `κ` FREE, proved by direct application of the seeded theorem
at that free `κ`/`hκ`.  Unlike the `κ := id` coherence probe above, this one cannot
survive a κ-dropping weakening of the seed: for free `κ`, a seeded conclusion in
which the datum index degenerated to `galSeq (φ n)` does not unify with the frozen
`galSeq (κ (φ n))` here.  At P2′ this probe is REPLACED by
`r3Production_diag_ae_subseq_kappa_coupling` (frozen text in the header): same
conclusion text, proof head swapped to the κ-threaded production `diag_ae_subseq`. -/
theorem diag_ae_subseq_seeded_free_kappa_exact_shape
    (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T) (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n)
    (κ : ℕ → ℕ) (hκ : StrictMono κ) :
    ∃ (φ : ℕ → ℕ),
      StrictMono φ ∧
      ∀ k : ℕ, ∃ g_k : ℝ → L2ballR3 k,
        AEStronglyMeasurable g_k (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)) ∧
        ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)),
          Filter.Tendsto
            (fun n => restrictToBall k ((galSeq (κ (φ n))).u t : L2VF_R3))
            Filter.atTop (nhds (g_k t)) :=
  diag_ae_subseq_seeded 𝔊 F ν hν T hT u₀ galSeq κ hκ

/-- **Free-κ statement guard, layer 2** — the `spacetime_extraction_seeded`
conclusion restated verbatim with `κ` FREE (same mechanism and P2′ replacement rule
as layer 1, with `r3Production_spacetime_extraction_kappa_coupling`). -/
theorem spacetime_extraction_seeded_free_kappa_exact_shape
    (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T) (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n)
    (κ : ℕ → ℕ) (hκ : StrictMono κ) :
    ∃ (φ : ℕ → ℕ) (u : Time → L2Sigma_R3), StrictMono φ ∧
      AEStronglyMeasurable (fun t => (u t : L2VF_R3))
        (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)) ∧
      (∀ R : ℝ, ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)),
        Filter.Tendsto
          (fun n => restrictToBall R ((galSeq (κ (φ n))).u t : L2VF_R3))
          Filter.atTop (nhds (restrictToBall R (u t : L2VF_R3)))) :=
  spacetime_extraction_seeded 𝔊 F ν hν T hT u₀ galSeq κ hκ

end Scratch212
end LerayHopf

-- Axiom pins (campaign doc §6 clauses 4/6, §7).  HUMAN-VISIBLE EVIDENCE ONLY since
-- pass-6: the gate no longer parses build-log text — scripts/check-scratch-pins.sh
-- enforces the totally pinned manifest (name/kind/statement-hash/axiom closure of
-- EVERY constant of this module, byte-diffed against
-- scripts/scratch-manifest.expected) and the kernel-trio bound via the STATIC
-- olean reader (scripts/scratch_reader.lean, pass-7 — reads the built olean as
-- data; executes nothing from this module).  Expected here and there: at most
-- [propext, Classical.choice, Quot.sound] — no sorryAx, no project axioms.
#print axioms LerayHopf.Scratch212.AubinLionsPackage_R3.ofProduction
#print axioms LerayHopf.Scratch212.AubinLionsPackage_R3.toProduction
#print axioms LerayHopf.Scratch212.r3LimitPassage_production_exact_shape
#print axioms LerayHopf.Scratch212.r3LimitPassagePin_production_source
#print axioms LerayHopf.Scratch212.r3Production_diag_ae_subseq_exact_shape
#print axioms LerayHopf.Scratch212.r3Production_u_lim_aestronglyMeasurable_exact_shape
#print axioms LerayHopf.Scratch212.r3Production_galerkinSpaceTimeExtraction_exact_shape
#print axioms LerayHopf.Scratch212.diag_ae_subseq_seeded_id_recovers_production
#print axioms LerayHopf.Scratch212.spacetime_extraction_seeded_id_recovers_production
#print axioms LerayHopf.Scratch212.diag_ae_subseq_seeded_free_kappa_exact_shape
#print axioms LerayHopf.Scratch212.spacetime_extraction_seeded_free_kappa_exact_shape
