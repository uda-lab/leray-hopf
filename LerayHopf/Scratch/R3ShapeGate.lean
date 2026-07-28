-- SCRATCH — issue #212 B0 exact-shape gate, ℝ³ FULL-SURFACE twin (codex statement-gate
-- pass-4 finding 1; docs/scratch/r3-global-diagonal-campaign.md §4.1/§6 clause 6, §11.4).
-- NOT production code.
--
-- WHAT THIS FILE IS.  A compiled, checker-wired FROZEN MIRROR of the two κ-critical
-- production declarations P2′ must produce — the κ-parameterized `AubinLionsPackage_R3`
-- (BOTH ball-restricted convergence fields, transcribed byte-faithfully from the merged
-- `LerayHopf/R3/SolutionInterfaces.lean:550` structure with the single change
-- `galSeq (φ n)` ↦ `galSeq (κ (φ n))`) and the `R3KappaChainExitWitness` (the §6 frozen
-- shape) — plus exact-shape PROBES against them.  The mirror lives in the `Scratch212`
-- namespace under the production-intended UNQUALIFIED names, so:
--
--   * at B0 every probe elaborates against the mirror (this file compiles TODAY against
--     the real merged ℝ³ interfaces — every field type is real, not synthetic);
--   * at P2′ the re-point is mechanical: DELETE the mirror declarations from this file
--     and ADD `import LerayHopf.R3.KappaChainExit` — the probes' unqualified references
--     then resolve to the production declarations with ZERO changes to any probe or
--     smoke statement.  A probe that fails after the swap means the production shape
--     deviates from the frozen design: that is a kill-criterion event (back to the
--     architect), never a probe edit.
--
-- PROBE MECHANISM (as in KappaShapeGate.lean): each shape probe re-states a declaration
-- surface verbatim with the mode map `κ` (or the supplied extraction `φ₁`) a FREE
-- variable and proves it by the bare projection — no `by`, no rewriting.  For free `κ`,
-- `galSeq (p.φ n)` does not unify with `galSeq (κ (p.φ n))`, so a dummy-κ or bare-index
-- production declaration FAILS these probes at compile time.  The linkage SMOKES at the
-- end (marked) are additionally allowed `simp only [w.transport]` rewriting: they gate
-- USABILITY of the transport linkage, not declaration shape.
import LerayHopf.R3.SolutionInterfaces

open MeasureTheory Filter Topology Set

namespace LerayHopf
namespace Scratch212

/-- **Frozen design mirror** of the P2′ κ-parameterized package (production target:
`LerayHopf.AubinLionsPackage_R3` after the P2′ rewiring).  Parameters and fields are
byte-faithful to the merged production structure except `κ` (inserted after `galSeq`,
§4 layer 4) and the effective datum index `galSeq (κ (φ n))` in BOTH convergence
fields. -/
structure AubinLionsPackage_R3 (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν T : ℝ) (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n) (κ : ℕ → ℕ) where
  /-- The strictly monotone extraction index. -/
  φ : ℕ → ℕ
  /-- Strict monotonicity of `φ`. -/
  φ_mono : StrictMono φ
  /-- The limit curve. -/
  u : Time → L2Sigma_R3
  /-- Time-measurability of the limit curve (production field, unchanged). -/
  u_aestronglyMeasurable :
    AEStronglyMeasurable (fun t => (u t : L2VF_R3))
      (MeasureTheory.volume.restrict (Set.Icc 0 T))
  /-- LOCAL space-time convergence at the EFFECTIVE index (production field with
  `galSeq (φ n)` ↦ `galSeq (κ (φ n))`). -/
  strong_convergence : ∀ R : ℝ,
    Filter.Tendsto
      (fun n => MeasureTheory.eLpNorm
        (fun t => restrictToBall R ((galSeq (κ (φ n))).u t) - restrictToBall R (u t))
        2 (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)))
      Filter.atTop (nhds 0)
  /-- A.e.-in-t per-ball convergence at the EFFECTIVE index (production field with
  `galSeq (φ n)` ↦ `galSeq (κ (φ n))`). -/
  strong_convergence_ae : ∀ R : ℝ, ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc 0 T)),
    Filter.Tendsto (fun n => restrictToBall R ((galSeq (κ (φ n))).u t))
      Filter.atTop (nhds (restrictToBall R (u t)))

/-- Effective absolute mode map is strictly monotone (P2′ must export this lemma with
this statement; §4.1 primary-protection surface 1). -/
theorem AubinLionsPackage_R3.effective_strictMono {𝔊 : R3GalerkinScheme}
    {F : R3NSForms 𝔊} {ν T : ℝ} {u₀ : L2Sigma_R3}
    {galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n} {κ : ℕ → ℕ}
    (p : AubinLionsPackage_R3 𝔊 F ν T u₀ galSeq κ) (hκ : StrictMono κ) :
    StrictMono (fun n => κ (p.φ n)) :=
  hκ.comp p.φ_mono

/-- Effective absolute mode map is cofinal (companion export, torus parity). -/
theorem AubinLionsPackage_R3.effective_tendsto_atTop {𝔊 : R3GalerkinScheme}
    {F : R3NSForms 𝔊} {ν T : ℝ} {u₀ : L2Sigma_R3}
    {galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n} {κ : ℕ → ℕ}
    (p : AubinLionsPackage_R3 𝔊 F ν T u₀ galSeq κ) (hκ : StrictMono κ) :
    Filter.Tendsto (fun n => κ (p.φ n)) Filter.atTop Filter.atTop :=
  (p.effective_strictMono hκ).tendsto_atTop

/-! ### Package shape probes (bare projections, `κ` free) -/

/-- Probe (a₁) — `strong_convergence` is TYPED at the effective index. -/
theorem r3PackageShape_strong_convergence_effective
    (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊) (ν T : ℝ) (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n) (κ : ℕ → ℕ)
    (p : AubinLionsPackage_R3 𝔊 F ν T u₀ galSeq κ) : ∀ R : ℝ,
    Filter.Tendsto
      (fun n => MeasureTheory.eLpNorm
        (fun t => restrictToBall R ((galSeq (κ (p.φ n))).u t) - restrictToBall R (p.u t))
        2 (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)))
      Filter.atTop (nhds 0) :=
  p.strong_convergence

/-- Probe (a₂) — `strong_convergence_ae` is TYPED at the effective index. -/
theorem r3PackageShape_strong_convergence_ae_effective
    (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊) (ν T : ℝ) (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n) (κ : ℕ → ℕ)
    (p : AubinLionsPackage_R3 𝔊 F ν T u₀ galSeq κ) : ∀ R : ℝ,
    ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc 0 T)),
      Filter.Tendsto (fun n => restrictToBall R ((galSeq (κ (p.φ n))).u t))
        Filter.atTop (nhds (restrictToBall R (p.u t))) :=
  p.strong_convergence_ae

/-- Probe (a₃) — the limit-curve measurability surface is the package FIELD (category
(i): consumers take it from the package, not from a free-floating helper). -/
theorem r3PackageShape_u_aestronglyMeasurable
    (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊) (ν T : ℝ) (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n) (κ : ℕ → ℕ)
    (p : AubinLionsPackage_R3 𝔊 F ν T u₀ galSeq κ) :
    AEStronglyMeasurable (fun t => (p.u t : L2VF_R3))
      (MeasureTheory.volume.restrict (Set.Icc 0 T)) :=
  p.u_aestronglyMeasurable

/-- Probe (b) — extraction-dependent cofinality at the EFFECTIVE index (§4.1 category
(iii) coupling): the `hlevel`-style bound derived from the package's effective map
alone, never from bare `φ_mono`. -/
theorem r3PackageShape_effective_le_apply
    (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊) (ν T : ℝ) (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n) (κ : ℕ → ℕ) (hκ : StrictMono κ)
    (p : AubinLionsPackage_R3 𝔊 F ν T u₀ galSeq κ) :
    ∀ n, n ≤ κ (p.φ n) :=
  fun _ => (p.effective_strictMono hκ).le_apply

/-! ### Strengthened limit-passage pin conjunct (frozen shape + defeq probe) -/

/-- **Frozen shape** of the pin conjunct P2′ adds to `galerkin_limit_passage_R3`'s
conclusion (§4.1): everywhere-weak convergence of the EFFECTIVE-index sequence to the
good representative, along `alPkg.φ` directly (no `ρ`). -/
def R3LimitPassagePinConjunct (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν T : ℝ) (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n) (κ : ℕ → ℕ)
    (p : AubinLionsPackage_R3 𝔊 F ν T u₀ galSeq κ) (v : Time → L2Sigma_R3) : Prop :=
  ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ z : L2VF_R3,
    Filter.Tendsto
      (fun n => inner (𝕜 := ℝ) (((galSeq (κ (p.φ n))).u t : L2VF_R3)) z)
      Filter.atTop (nhds (inner (𝕜 := ℝ) ((v t : L2VF_R3)) z))

/-- Probe (c) — the frozen pin-conjunct Prop unfolds DEFINITIONALLY to the
effective-index everywhere-weak shape (bare `h`; P2′'s strengthened conclusion must be
stated as this Prop or definitionally equal to it). -/
theorem r3LimitPassagePinShape_effective (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν T : ℝ) (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n) (κ : ℕ → ℕ)
    (p : AubinLionsPackage_R3 𝔊 F ν T u₀ galSeq κ) (v : Time → L2Sigma_R3)
    (h : R3LimitPassagePinConjunct 𝔊 F ν T u₀ galSeq κ p v) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ z : L2VF_R3,
      Filter.Tendsto
        (fun n => inner (𝕜 := ℝ) (((galSeq (κ (p.φ n))).u t : L2VF_R3)) z)
        Filter.atTop (nhds (inner (𝕜 := ℝ) ((v t : L2VF_R3)) z)) :=
  h

/-! ### Exit witness mirror (§6 frozen shape) + witness shape probes -/

/-- **Frozen design mirror** of the P2′ exit witness (production target:
`R3KappaChainExitWitness` in `LerayHopf/R3/KappaChainExit.lean`).  The §6 shape
verbatim: dependent family parameter, mandatory `transport`, κ-package over `base`
with `κ := φ₁`, all chain stages over the SAME `base`/`alPkg`/`v`, pin against
`galSeq₁` ITSELF along `alPkg.φ` (no sub-extraction `ρ` — ℝ³ simplification). -/
structure R3KappaChainExitWitness (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν T : ℝ) (u₀ : L2Sigma_R3) (φ₁ : ℕ → ℕ)
    (galSeq₁ : ∀ k, GalerkinSolutionData_R3 𝔊 F ν u₀ (φ₁ k)) where
  /-- The full base family the κ-generalized chain runs over (implementation vehicle —
  admissible ONLY because `transport` binds it to `galSeq₁`). -/
  base : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n
  /-- Mandatory transport equality (family-linkage category (iv)): along `φ₁`, `base`
  IS the given dependent family. -/
  transport : ∀ k, base (φ₁ k) = galSeq₁ k
  /-- Aubin–Lions κ-package over `base` with effective mode map `κ := φ₁`. -/
  alPkg : AubinLionsPackage_R3 𝔊 F ν T u₀ base φ₁
  /-- Energy class for the package curve. -/
  energy_class_pkg :
    (∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)),
        memH1VF_R3 (alPkg.u t : L2VF_R3)) ∧
      IntervalIntegrable (fun s => viscousFormSq_R3 ν (alPkg.u s : L2VF_R3))
        MeasureTheory.volume 0 T
  /-- The good representative produced by limit passage. -/
  v : Time → L2Sigma_R3
  /-- Representative is a.e.-linked to the package curve on `[0, T]`. -/
  v_ae : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)), v t = alPkg.u t
  /-- Weak-form limit passage for the representative. -/
  weak_eq : WeakFormNS ν T (r3Evolution 𝔊 F) v
  /-- Energy inequality (∀t form). -/
  energy_ineq : ∀ t, 0 ≤ t → t ≤ T →
    (1 / 2 : ℝ) * ‖(v t : L2VF_R3)‖ ^ 2 +
      ∫ s in (0 : ℝ)..t, viscousFormSq_R3 ν (v s : L2VF_R3) ≤
    (1 / 2 : ℝ) * ‖(u₀ : L2VF_R3)‖ ^ 2
  /-- Strong initial trace. -/
  initial_trace : Filter.Tendsto (fun t => (v t : L2VF_R3))
    (nhdsWithin 0 (Set.Ici 0)) (nhds (u₀ : L2VF_R3))
  /-- Energy class re-exported for the representative. -/
  energy_class_v :
    (∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)),
        memH1VF_R3 (v t : L2VF_R3)) ∧
      IntervalIntegrable (fun s => viscousFormSq_R3 ν (v s : L2VF_R3))
        MeasureTheory.volume 0 T
  /-- Everywhere-weak pin, phrased against `galSeq₁` ITSELF, along `alPkg.φ` directly
  (the exact `hpin` shape of spike (a)'s `r3_representative_diag_coherence` with
  `δ := φ₁`, `σ := alPkg.φ` — §6 clause 2 coupling). -/
  pin : ∀ t, t ∈ Set.Icc (0 : ℝ) T → ∀ z : L2VF_R3,
    Filter.Tendsto
      (fun k => inner (𝕜 := ℝ) (((galSeq₁ (alPkg.φ k)).u t : L2VF_R3)) z)
      Filter.atTop (nhds (inner (𝕜 := ℝ) ((v t : L2VF_R3)) z))

variable {𝔊 : R3GalerkinScheme} {F : R3NSForms 𝔊} {ν T : ℝ} {u₀ : L2Sigma_R3}
  {φ₁ : ℕ → ℕ} {galSeq₁ : ∀ k, GalerkinSolutionData_R3 𝔊 F ν u₀ (φ₁ k)}

/-- Probe (d₁) — the transport surface: along `φ₁`, the base family IS the dependent
family (bare projection; family-linkage category (iv)). -/
theorem r3WitnessShape_transport (w : R3KappaChainExitWitness 𝔊 F ν T u₀ φ₁ galSeq₁) :
    ∀ k, w.base (φ₁ k) = galSeq₁ k :=
  w.transport

/-- Probe (d₂) — the pin surface: against `galSeq₁` ITSELF along `alPkg.φ` (bare
projection; a base-family or bare-index pin would not elaborate). -/
theorem r3WitnessShape_pin_dependent_family
    (w : R3KappaChainExitWitness 𝔊 F ν T u₀ φ₁ galSeq₁) :
    ∀ t, t ∈ Set.Icc (0 : ℝ) T → ∀ z : L2VF_R3,
      Filter.Tendsto
        (fun k => inner (𝕜 := ℝ) (((galSeq₁ (w.alPkg.φ k)).u t : L2VF_R3)) z)
        Filter.atTop (nhds (inner (𝕜 := ℝ) ((w.v t : L2VF_R3)) z)) :=
  w.pin

/-- Probe (d₃) — the witness's package is genuinely the `κ := φ₁` instantiation over
`base`: its convergence field is TYPED at `base (φ₁ (alPkg.φ n))` (bare projection —
the alPkg linkage is in the TYPE, not prose). -/
theorem r3WitnessShape_alPkg_effective_convergence
    (w : R3KappaChainExitWitness 𝔊 F ν T u₀ φ₁ galSeq₁) : ∀ R : ℝ,
    Filter.Tendsto
      (fun n => MeasureTheory.eLpNorm
        (fun t => restrictToBall R ((w.base (φ₁ (w.alPkg.φ n))).u t)
          - restrictToBall R (w.alPkg.u t))
        2 (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)))
      Filter.atTop (nhds 0) :=
  w.alPkg.strong_convergence

/-- Witness-level effective strictness (category (iii) at the witness instantiation). -/
theorem R3KappaChainExitWitness.effective_strictMono (hφ₁ : StrictMono φ₁)
    (w : R3KappaChainExitWitness 𝔊 F ν T u₀ φ₁ galSeq₁) :
    StrictMono (fun n => φ₁ (w.alPkg.φ n)) :=
  hφ₁.comp w.alPkg.φ_mono

/-! ### Linkage smokes (transport USABILITY — `simp only [w.transport]` allowed) -/

/-- Smoke (e₁) — `transport` genuinely transports: the pin transfers to the base
family, so base-phrased chain-internal facts serve the dependent-family consumers. -/
theorem R3KappaChainExitWitness.pin_base
    (w : R3KappaChainExitWitness 𝔊 F ν T u₀ φ₁ galSeq₁) :
    ∀ t, t ∈ Set.Icc (0 : ℝ) T → ∀ z : L2VF_R3,
      Filter.Tendsto
        (fun k => inner (𝕜 := ℝ) (((w.base (φ₁ (w.alPkg.φ k))).u t : L2VF_R3)) z)
        Filter.atTop (nhds (inner (𝕜 := ℝ) ((w.v t : L2VF_R3)) z)) := by
  intro t ht z
  simpa only [w.transport] using w.pin t ht z

/-- Smoke (e₂) — the package convergence transfers to the DEPENDENT family via
`transport`: the strong-convergence content is available phrased against `galSeq₁`. -/
theorem R3KappaChainExitWitness.alPkg_convergence_dependent_family
    (w : R3KappaChainExitWitness 𝔊 F ν T u₀ φ₁ galSeq₁) : ∀ R : ℝ,
    Filter.Tendsto
      (fun n => MeasureTheory.eLpNorm
        (fun t => restrictToBall R ((galSeq₁ (w.alPkg.φ n)).u t)
          - restrictToBall R (w.alPkg.u t))
        2 (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)))
      Filter.atTop (nhds 0) := by
  intro R
  simpa only [w.transport] using w.alPkg.strong_convergence R

end Scratch212
end LerayHopf

-- Axiom pins (campaign doc §6 clauses 4/6, §7; enforced by scripts/check-scratch-pins.sh
-- with source-manifest equality — EVERY top-level declaration is pinned; expected: at
-- most [propext, Classical.choice, Quot.sound] — no sorryAx, no project axioms).
#print axioms LerayHopf.Scratch212.AubinLionsPackage_R3
#print axioms LerayHopf.Scratch212.AubinLionsPackage_R3.effective_strictMono
#print axioms LerayHopf.Scratch212.AubinLionsPackage_R3.effective_tendsto_atTop
#print axioms LerayHopf.Scratch212.r3PackageShape_strong_convergence_effective
#print axioms LerayHopf.Scratch212.r3PackageShape_strong_convergence_ae_effective
#print axioms LerayHopf.Scratch212.r3PackageShape_u_aestronglyMeasurable
#print axioms LerayHopf.Scratch212.r3PackageShape_effective_le_apply
#print axioms LerayHopf.Scratch212.R3LimitPassagePinConjunct
#print axioms LerayHopf.Scratch212.r3LimitPassagePinShape_effective
#print axioms LerayHopf.Scratch212.R3KappaChainExitWitness
#print axioms LerayHopf.Scratch212.r3WitnessShape_transport
#print axioms LerayHopf.Scratch212.r3WitnessShape_pin_dependent_family
#print axioms LerayHopf.Scratch212.r3WitnessShape_alPkg_effective_convergence
#print axioms LerayHopf.Scratch212.R3KappaChainExitWitness.effective_strictMono
#print axioms LerayHopf.Scratch212.R3KappaChainExitWitness.pin_base
#print axioms LerayHopf.Scratch212.R3KappaChainExitWitness.alPkg_convergence_dependent_family
