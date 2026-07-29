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
--
-- P2′ RE-POINT (§6 clause 6): the four frozen mirror declarations
-- (`AubinLionsPackage_R3`, its two `effective_*` lemmas, `R3KappaChainExitWitness`) have
-- been DELETED and `import LerayHopf.R3.KappaChainExit` added; every probe/smoke below now
-- resolves its unqualified references to the ACTUAL production declarations
-- (`LerayHopf.AubinLionsPackage_R3` via `SolutionInterfaces`, `LerayHopf.R3KappaChainExitWitness`
-- via `KappaChainExit`) with ZERO probe-statement changes.  A probe that fails after this
-- re-point means the production shape deviates from the frozen design = kill-criterion event.
import LerayHopf.R3.SolutionInterfaces
import LerayHopf.R3.KappaChainExit

open MeasureTheory Filter Topology Set

namespace LerayHopf
namespace Scratch212

-- P2′ RE-POINT: `AubinLionsPackage_R3` mirror structure and its two `effective_*`
-- lemmas (`effective_strictMono`, `effective_tendsto_atTop`) DELETED here; the probes
-- below now resolve `AubinLionsPackage_R3` and `p.effective_strictMono` to the production
-- declarations in `LerayHopf.R3.SolutionInterfaces`.

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

/-! ### Strengthened limit-passage conclusion (frozen §6 clause-6 target, round-5
finding 1) + pin-projection probe -/

/-- **Frozen shape** of the FULL strengthened `galerkin_limit_passage_R3` conclusion
P2′ must produce: the merged production 5-conjunct good-representative existential
(transcribed byte-faithfully from `LerayHopf/R3/LimitPassage.lean`, `alPkg` ↦ `p`)
with the κ-pin conjunct `R3LimitPassagePinConjunct` APPENDED as the sixth conjunct.
§6 clause 6 requires the P2′ production theorem's conclusion to be stated as this Prop
(or definitionally equal to it), consumed by the bare-application coupling
`r3LimitPassage_strengthened_production_coupling` whose text is frozen in §6 and in
`R3ProductionCoupling.lean` — that coupling can compile only at P2′ (production's
conclusion lacks the pin conjunct today; the coupling detects exactly that). -/
def R3StrengthenedLimitPassageConclusion (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν T : ℝ) (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n) (κ : ℕ → ℕ)
    (p : AubinLionsPackage_R3 𝔊 F ν T u₀ galSeq κ) : Prop :=
  ∃ u : Time → L2Sigma_R3,
    (∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc 0 T)), u t = p.u t) ∧
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
      MeasureTheory.volume 0 T) ∧
    R3LimitPassagePinConjunct 𝔊 F ν T u₀ galSeq κ p u

/-- Probe (c₂) — the strengthened conclusion genuinely CONTAINS the frozen pin
conjunct as its sixth conjunct: projecting it out is pure destructuring (no
rewriting).  Survives the P2′ re-point unchanged (references only frozen shapes). -/
theorem r3StrengthenedConclusion_projects_pin (𝔊 : R3GalerkinScheme)
    (F : R3NSForms 𝔊) (ν T : ℝ) (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n) (κ : ℕ → ℕ)
    (p : AubinLionsPackage_R3 𝔊 F ν T u₀ galSeq κ)
    (h : R3StrengthenedLimitPassageConclusion 𝔊 F ν T u₀ galSeq κ p) :
    ∃ u : Time → L2Sigma_R3,
      R3LimitPassagePinConjunct 𝔊 F ν T u₀ galSeq κ p u := by
  obtain ⟨u, -, -, -, -, -, hpin⟩ := h
  exact ⟨u, hpin⟩

/-! ### Exit witness probes (production `R3KappaChainExitWitness` after re-point) -/

-- P2′ RE-POINT: `R3KappaChainExitWitness` mirror structure DELETED here; the probes and
-- smokes below now resolve `R3KappaChainExitWitness` to the production declaration in
-- `LerayHopf.R3.KappaChainExit` (imported above).

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

/-! ### §6 clause-3 nontrivial-seed smokes (`κ := Nat.succ`, full-path threading)

Unlike the probes/linkage-smokes above (which take a `w : R3KappaChainExitWitness`
hypothesis), these two theorems INSTANTIATE the production exit gate `r3_kappaChain_exit`
at the genuinely nontrivial seed `κ := Nat.succ` (`StrictMono`, provably `≠ id`), so they
thread the ENTIRE production path — package construction → viscous lsc → limit passage →
pin re-export → typed witness — at a nonidentity κ.  A dummy-κ or stale-index production
chain cannot instantiate them.  They are audit artifacts (Scratch212), not release code. -/

/-- **Smoke (f₁) — full-path threading + `transport` consumption to a base-family pin at the
COMPOSED effective index `w.alPkg.φ k + 1`** (`= Nat.succ (w.alPkg.φ k)`).  Runs the whole
production chain at `κ := Nat.succ`, then transports the dependent-family pin down to the
base family at the `+ 1`-shifted effective index.  A pin phrased at the bare `w.alPkg.φ k`
(dropping the `Nat.succ`) would not elaborate — this is the §4.1 defense-in-depth #1
staleness catch at a real `κ ≠ id`. -/
theorem r3KappaSuccSmoke_pin_base_succ
    (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊) (ν : ℝ) (hν : 0 < ν)
    (T : ℝ) (hT : 0 < T) (u₀ : L2Sigma_R3)
    (fill : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n)
    (htest : R3TestApproxH1 𝔊)
    (galSeq₁ : ∀ k, GalerkinSolutionData_R3 𝔊 F ν u₀ (Nat.succ k)) :
    ∃ w : R3KappaChainExitWitness 𝔊 F ν T u₀ Nat.succ galSeq₁,
      ∀ t, t ∈ Set.Icc (0 : ℝ) T → ∀ z : L2VF_R3,
        Filter.Tendsto
          (fun k => inner (𝕜 := ℝ) (((w.base (w.alPkg.φ k + 1)).u t : L2VF_R3)) z)
          Filter.atTop (nhds (inner (𝕜 := ℝ) ((w.v t : L2VF_R3)) z)) := by
  have hsucc : StrictMono Nat.succ := fun _ _ h => Nat.succ_lt_succ h
  obtain ⟨w⟩ :=
    r3_kappaChain_exit 𝔊 F ν hν T hT u₀ fill htest Nat.succ hsucc galSeq₁
  refine ⟨w, ?_⟩
  intro t ht z
  simpa only [← w.transport] using w.pin t ht z

/-- **Smoke (f₂) — category-(iii) exercise at `κ := Nat.succ`** (§4.1 pass-3 widening).
After threading the full path, apply the PRODUCTION selection helper
`perTest_lipschitz_R3` (the `GoodRepresentative`-side consumer of the `hlevel` growth
bound) at the effective index, feeding it the effective bound `∀ n, n ≤ w.alPkg.φ n + 1`
DERIVED from `effective_strictMono` (never from bare `φ_mono`).  This exercises the
extraction-dependent pairing itself at `κ ≠ id`, not only total-family applications. -/
theorem r3KappaSuccSmoke_categoryIII_effectiveBound
    (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊) (ν : ℝ) (hν : 0 < ν)
    (T : ℝ) (hT : 0 < T) (u₀ : L2Sigma_R3)
    (fill : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n)
    (htest : R3TestApproxH1 𝔊)
    (galSeq₁ : ∀ k, GalerkinSolutionData_R3 𝔊 F ν u₀ (Nat.succ k))
    (wt : L2Sigma_R3) (hwt : IsSchwartzDivFree_R3 wt) (n₀ : ℕ)
    (hn₀ : 𝔊.P n₀ (wt : L2VF_R3) = (wt : L2VF_R3)) :
    ∃ (w : R3KappaChainExitWitness 𝔊 F ν T u₀ Nat.succ galSeq₁) (L : ℝ), 0 ≤ L ∧
      ∀ n, n₀ ≤ n → ∀ s ∈ Set.Ici (0 : ℝ), ∀ t ∈ Set.Ici (0 : ℝ),
        |inner (𝕜 := ℝ) (((w.base (w.alPkg.φ n + 1)).u t : L2VF_R3)) (wt : L2VF_R3)
          - inner (𝕜 := ℝ) (((w.base (w.alPkg.φ n + 1)).u s : L2VF_R3)) (wt : L2VF_R3)|
          ≤ L * |t - s| := by
  have hsucc : StrictMono Nat.succ := fun _ _ h => Nat.succ_lt_succ h
  obtain ⟨w⟩ :=
    r3_kappaChain_exit 𝔊 F ν hν T hT u₀ fill htest Nat.succ hsucc galSeq₁
  -- effective bound from effective_strictMono at κ = Nat.succ (category (iii): NOT bare φ_mono)
  have hlevel : ∀ n, n ≤ w.alPkg.φ n + 1 :=
    fun n => (w.alPkg.effective_strictMono hsucc).le_apply
  obtain ⟨L, hL0, hLip⟩ :=
    perTest_lipschitz_R3 ν hν u₀ (fun n => (w.base n).toSolutionData) wt hwt n₀ hn₀
  refine ⟨w, L, hL0, ?_⟩
  intro n hn s hs t ht
  exact hLip (w.alPkg.φ n + 1) (le_trans hn (hlevel n)) s hs t ht

end Scratch212
end LerayHopf

-- Axiom pins (campaign doc §6 clauses 4/6, §7; enforced by scripts/check-scratch-pins.sh
-- with source-manifest equality — EVERY top-level declaration is pinned; expected: at
-- most [propext, Classical.choice, Quot.sound] — no sorryAx, no project axioms).
#print axioms LerayHopf.Scratch212.r3PackageShape_strong_convergence_effective
#print axioms LerayHopf.Scratch212.r3PackageShape_strong_convergence_ae_effective
#print axioms LerayHopf.Scratch212.r3PackageShape_u_aestronglyMeasurable
#print axioms LerayHopf.Scratch212.r3PackageShape_effective_le_apply
#print axioms LerayHopf.Scratch212.R3LimitPassagePinConjunct
#print axioms LerayHopf.Scratch212.r3LimitPassagePinShape_effective
#print axioms LerayHopf.Scratch212.R3StrengthenedLimitPassageConclusion
#print axioms LerayHopf.Scratch212.r3StrengthenedConclusion_projects_pin
#print axioms LerayHopf.Scratch212.r3WitnessShape_transport
#print axioms LerayHopf.Scratch212.r3WitnessShape_pin_dependent_family
#print axioms LerayHopf.Scratch212.r3WitnessShape_alPkg_effective_convergence
#print axioms LerayHopf.Scratch212.R3KappaChainExitWitness.effective_strictMono
#print axioms LerayHopf.Scratch212.R3KappaChainExitWitness.pin_base
#print axioms LerayHopf.Scratch212.R3KappaChainExitWitness.alPkg_convergence_dependent_family
#print axioms LerayHopf.Scratch212.r3KappaSuccSmoke_pin_base_succ
#print axioms LerayHopf.Scratch212.r3KappaSuccSmoke_categoryIII_effectiveBound
