-- SCRATCH — issue #195 feasibility spike (lean-architect). NOT production code.
-- Codex pass-3 finding G-1: the P2 exit gate must be a TYPED acceptance artifact, not
-- prose with a base-family loophole.  `P2ExitWitness` below is that artifact: the §5 P2
-- exit gate now reads "a compiled production theorem instantiating this structure's
-- shape", and the structure makes the loophole unrepresentable —
--
--   * the dependent family `galSeq₁ : ∀ k, GalerkinSolutionData F ν u₀ (φ₁ k)` is a
--     PARAMETER: a witness is a witness FOR that family, not for a family of the
--     implementation's choosing;
--   * a base family may appear, but ONLY through the mandatory `transport` field
--     `∀ k, base (φ₁ k) = galSeq₁ k` — a fresh/canonical family with no transport
--     proof cannot instantiate the structure;
--   * all four chain stages (Aubin–Lions package construction, energy class, weak-form
--     limit passage, representative pin) are fields over the SAME `base`/`alPkg`/`v`,
--     and the pin is phrased against `galSeq₁` ITSELF — the chain cannot silently
--     switch families between stages.
--
-- Field types are transcribed verbatim from the production conclusions they gate:
-- `torus_energyClass_of_aubinLions` (ViscousLimit.lean:168),
-- `torus_galerkin_limit_passage_of_energyClass` (TraceEnergy.lean:1150), and the
-- everywhere-weak pin of `exists_weak_representative` (TraceEnergy.lean:491), with
-- `galSeq (alPkg.φ (ρ k))` replaced by `galSeq₁ (alPkg.φ (ρ k))` — the dependent
-- family consumed literally.  The three theorems below are fully proved smoke tests
-- that the typed linkage is USABLE (transport transfers the pin to the base family;
-- effective strictness composes; AESM of the representative is derivable, closing the
-- one conclusion conjunct the production limit passage leaves implicit).
import LerayHopf.Scratch.KappaReindex

open MeasureTheory Filter Topology Set

namespace LerayHopf
namespace Scratch195

/-- **Typed P2 exit contract** (codex pass-3 G-1).  P2 is complete exactly when a
production theorem of the shape
`∀ F ν hν T hT u₀ φ₁ (hφ₁ : StrictMono φ₁) galSeq₁, Nonempty (P2ExitWitness F ν T u₀ φ₁ galSeq₁)`
is compiled (production names may differ; the FIELDS may not lose content).  Every
stage consumes the same family, and `transport` ties it to the given dependent one. -/
structure P2ExitWitness (F : Torus3NSForms) (ν T : ℝ) (u₀ : L2Sigma)
    (φ₁ : ℕ → ℕ) (galSeq₁ : ∀ k, GalerkinSolutionData F ν u₀ (φ₁ k)) where
  /-- The full base family the κ-generalized chain runs over (implementation vehicle —
  admissible ONLY because `transport` binds it to `galSeq₁`). -/
  base : ∀ n, GalerkinSolutionData F ν u₀ n
  /-- **Mandatory transport equality**: along `φ₁`, `base` IS the given dependent
  family.  This is the field that makes an unlinked fresh/canonical family
  unrepresentable. -/
  transport : ∀ k, base (φ₁ k) = galSeq₁ k
  /-- Stage 1 — Aubin–Lions package construction over `base` with effective mode map
  `κ := φ₁` (so every package datum is `base (φ₁ _) = galSeq₁ _`). -/
  alPkg : AubinLionsPackageKappa F ν T u₀ base φ₁
  /-- Stage 2 — energy class for the package curve (shape of
  `torus_energyClass_of_aubinLions`). -/
  energy_class_pkg :
    (∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)),
        memH1VF (alPkg.u t : L2VF)) ∧
      IntervalIntegrable (fun s => viscousFormSq ν (alPkg.u s : L2VF))
        MeasureTheory.volume 0 T
  /-- The good representative produced by limit passage. -/
  v : Time → L2Sigma
  /-- Representative is a.e.-linked to the package curve on `[0, T]`. -/
  v_ae : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)), v t = alPkg.u t
  /-- Stage 3 — weak-form limit passage for the representative (first conjunct of
  `torus_galerkin_limit_passage_of_energyClass`'s conclusion). -/
  weak_eq : WeakFormNS ν T (torus3Evolution F) v
  /-- Stage 3 — energy inequality (same conclusion, ∀t form). -/
  energy_ineq : ∀ t, 0 ≤ t → t ≤ T →
    (1 / 2 : ℝ) * ‖(v t : L2VF)‖ ^ 2 +
      ∫ s in (0 : ℝ)..t, viscousFormSq ν (v s : L2VF) ≤
    (1 / 2 : ℝ) * ‖(u₀ : L2VF)‖ ^ 2
  /-- Stage 3 — strong initial trace (same conclusion). -/
  initial_trace : Filter.Tendsto (fun t => (v t : L2VF))
    (nhdsWithin 0 (Set.Ici 0)) (nhds (u₀ : L2VF))
  /-- Stage 3 — energy class re-exported for the representative (same conclusion). -/
  energy_class_v :
    (∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)),
        memH1VF (v t : L2VF)) ∧
      IntervalIntegrable (fun s => viscousFormSq ν (v s : L2VF))
        MeasureTheory.volume 0 T
  /-- Stage 4 — the sub-extraction of the representative pin. -/
  ρ : ℕ → ℕ
  /-- Strict monotonicity of the sub-extraction. -/
  ρ_mono : StrictMono ρ
  /-- Stage 4 — **everywhere weak-convergence pin, phrased against `galSeq₁` ITSELF**
  (shape of `exists_weak_representative`'s pin conjunct, with the dependent family
  consumed literally): the P2 re-export that Step 4 overlap coherence consumes. -/
  pin : ∀ t, t ∈ Set.Icc (0 : ℝ) T → ∀ z : L2VF,
    Filter.Tendsto
      (fun k => inner (𝕜 := ℝ) (((galSeq₁ (alPkg.φ (ρ k))).u t : L2VF)) z)
      Filter.atTop (nhds (inner (𝕜 := ℝ) ((v t : L2VF)) z))

variable {F : Torus3NSForms} {ν T : ℝ} {u₀ : L2Sigma} {φ₁ : ℕ → ℕ}
  {galSeq₁ : ∀ k, GalerkinSolutionData F ν u₀ (φ₁ k)}

/-- Smoke test 1 (fully proved): `transport` genuinely transports — the pin transfers
to the base family by rewriting, so the two phrasings are interchangeable and the
chain's internal (base-phrased) convergence facts serve the dependent-family
consumers. -/
theorem P2ExitWitness.pin_base (w : P2ExitWitness F ν T u₀ φ₁ galSeq₁) :
    ∀ t, t ∈ Set.Icc (0 : ℝ) T → ∀ z : L2VF,
      Filter.Tendsto
        (fun k => inner (𝕜 := ℝ) (((w.base (φ₁ (w.alPkg.φ (w.ρ k)))).u t : L2VF)) z)
        Filter.atTop (nhds (inner (𝕜 := ℝ) ((w.v t : L2VF)) z)) := by
  intro t ht z
  simpa only [w.transport] using w.pin t ht z

/-- Smoke test 2 (fully proved): the witness's effective index map is strictly
monotone — the finding-3 composition lemmas apply to the artifact as-is. -/
theorem P2ExitWitness.effective_strictMono (hφ₁ : StrictMono φ₁)
    (w : P2ExitWitness F ν T u₀ φ₁ galSeq₁) :
    StrictMono (fun n => φ₁ (w.alPkg.φ n)) :=
  hφ₁.comp w.alPkg.φ_mono

/-- Smoke test 3 (fully proved): AESM of the representative — the one contract
conjunct the production limit passage leaves to its consumers — is derivable from the
witness fields alone (`v_ae` + the package's AESM), so the artifact is sufficient for
the P4 per-horizon assembly with no hidden extra input. -/
theorem P2ExitWitness.v_aestronglyMeasurable (w : P2ExitWitness F ν T u₀ φ₁ galSeq₁) :
    AEStronglyMeasurable (fun t => (w.v t : L2VF))
      (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)) := by
  refine w.alPkg.u_aestronglyMeasurable.congr ?_
  filter_upwards [w.v_ae] with t ht
  exact congrArg (fun x : L2Sigma => (x : L2VF)) ht.symm

end Scratch195
end LerayHopf

-- Axiom pins (recorded in docs/scratch/global-diagonal-campaign.md §10.5; expected:
-- at most [propext, Classical.choice, Quot.sound] — no sorryAx, no project axioms).
#print axioms LerayHopf.Scratch195.P2ExitWitness.pin_base
#print axioms LerayHopf.Scratch195.P2ExitWitness.effective_strictMono
#print axioms LerayHopf.Scratch195.P2ExitWitness.v_aestronglyMeasurable
