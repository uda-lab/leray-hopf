/-
# P2′ (#215) exit gate — ℝ³ κ-chain acceptance artifact

This module promotes the issue #212 feasibility design to production: the dependent-family
embedding `extendReindexedFamily_R3` and the typed acceptance artifact
`R3KappaChainExitWitness`, together with the production theorem `r3_kappaChain_exit`
that instantiates it end-to-end.

Per the campaign doc §5/§6, P2′ is complete exactly when a production theorem of the shape

  `∀ 𝔊 F ν hν T hT u₀ fill htest φ₁ (hφ₁ : StrictMono φ₁) galSeq₁,
      Nonempty (R3KappaChainExitWitness 𝔊 F ν T u₀ φ₁ galSeq₁)`

is compiled.  `r3_kappaChain_exit` below is that theorem.  The witness runs the
κ-generalized compactness chain (`aubinLionsPackage_R3_of_timeCompactness` →
`viscous_lsc_under_strongL2` → `galerkin_limit_passage_R3`) over a base family with
outer index map `κ := φ₁`, and the mandatory `transport` field binds that base family
to the GIVEN dependent family `galSeq₁` — an unlinked fresh family cannot instantiate the
artifact.  The everywhere-weak pin is the final conjunct that P2′'s strengthening added to
`galerkin_limit_passage_R3`, re-exported here phrased against `galSeq₁` itself via `transport`.

**Torus deviation (argued, not silent):** `extendReindexedFamily_R3`'s off-subsequence filler
is a PARAMETER (`fill`) rather than a hardwired canonical family, because ℝ³'s total Galerkin
ODE layer exists over `schemeOfBasis B`, not over an abstract `𝔊`.  P4′ instantiates
`fill := galSeq` (the one fixed family), so no generality is lost and the `transport` field
still makes an unlinked implementation unrepresentable.
-/
import LerayHopf.R3.AubinLionsAssembly
import LerayHopf.R3.LimitPassage
import LerayHopf.R3.EnergyWeakLsc

open MeasureTheory Filter Topology Set

namespace LerayHopf

open Classical in
/-- Embed a dependent reindexed family
`galSeq₁ : ∀ k, GalerkinSolutionData_R3 𝔊 F ν u₀ (φ₁ k)` into a full base family: at `φ₁ k`
take the given datum, elsewhere the supplied filler datum `fill n` (a parameter — ℝ³'s total
ODE layer is scheme-specific, so the filler is not hardwired). -/
noncomputable def extendReindexedFamily_R3
    (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊) (ν : ℝ) (u₀ : L2Sigma_R3)
    (φ₁ : ℕ → ℕ) (galSeq₁ : ∀ k, GalerkinSolutionData_R3 𝔊 F ν u₀ (φ₁ k))
    (fill : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n) :
    ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n := fun n =>
  if h : ∃ k, φ₁ k = n then (Classical.choose_spec h) ▸ galSeq₁ (Classical.choose h)
  else fill n

/-- On the subsequence the embedding restores the given data on the nose (needs only
injectivity of `φ₁`). -/
theorem extendReindexedFamily_R3_apply
    (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊) (ν : ℝ) (u₀ : L2Sigma_R3)
    (φ₁ : ℕ → ℕ) (hφ₁ : Function.Injective φ₁)
    (galSeq₁ : ∀ k, GalerkinSolutionData_R3 𝔊 F ν u₀ (φ₁ k))
    (fill : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n) (k : ℕ) :
    extendReindexedFamily_R3 𝔊 F ν u₀ φ₁ galSeq₁ fill (φ₁ k) = galSeq₁ k := by
  have hex : ∃ k', φ₁ k' = φ₁ k := ⟨k, rfl⟩
  have hkk : Classical.choose hex = k := hφ₁ (Classical.choose_spec hex)
  simp only [extendReindexedFamily_R3, dif_pos hex]
  refine eq_of_heq ((eqRec_heq (Classical.choose_spec hex) _).trans ?_)
  rw [hkk]

/-- **Typed P2′ exit contract (production).**  A witness certifies that the κ-generalized ℝ³
compactness chain runs end-to-end over a base family bound (via `transport`) to the given
dependent family `galSeq₁`, with outer index map `κ := φ₁` — the index map selecting which
entries of the original Galerkin family are used, the package choosing its own extraction `φ`
internally so that convergence is stated along the composed index map `κ ∘ φ`.  Field types
are the production
conclusions of the chain stages; the pin is phrased against `galSeq₁` itself, along `alPkg.φ`
directly (ℝ³ simplification: `galerkin_limit_passage_R3` pins along `alPkg.φ` with no
sub-extraction `ρ` — the torus witness's `ρ`/`ρ_mono` fields are ABSENT by design). -/
structure R3KappaChainExitWitness (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν T : ℝ) (u₀ : L2Sigma_R3) (φ₁ : ℕ → ℕ)
    (galSeq₁ : ∀ k, GalerkinSolutionData_R3 𝔊 F ν u₀ (φ₁ k)) where
  /-- The full base family the κ-generalized chain runs over. -/
  base : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n
  /-- **Mandatory transport equality**: along `φ₁`, `base` IS the given dependent family. -/
  transport : ∀ k, base (φ₁ k) = galSeq₁ k
  /-- Aubin–Lions κ-package over `base` with outer index map `κ := φ₁`. -/
  alPkg : AubinLionsPackage_R3 𝔊 F ν T u₀ base φ₁
  /-- Energy class for the package curve. -/
  energy_class_pkg :
    (∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)), memH1VF_R3 (alPkg.u t : L2VF_R3)) ∧
      IntervalIntegrable (fun s => viscousFormSq_R3 ν (alPkg.u s : L2VF_R3)) volume 0 T
  /-- The good representative produced by limit passage. -/
  v : Time → L2Sigma_R3
  /-- Representative a.e.-linked to the package curve on `[0, T]`. -/
  v_ae : ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)), v t = alPkg.u t
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
    (∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)), memH1VF_R3 (v t : L2VF_R3)) ∧
      IntervalIntegrable (fun s => viscousFormSq_R3 ν (v s : L2VF_R3)) volume 0 T
  /-- **Everywhere-weak pin, phrased against `galSeq₁` ITSELF, along `alPkg.φ` directly.** -/
  pin : ∀ t, t ∈ Set.Icc (0 : ℝ) T → ∀ z : L2VF_R3,
    Filter.Tendsto
      (fun k => inner (𝕜 := ℝ) (((galSeq₁ (alPkg.φ k)).u t : L2VF_R3)) z)
      Filter.atTop (nhds (inner (𝕜 := ℝ) ((v t : L2VF_R3)) z))

/-- **P2′ (#215) exit gate.**  A `R3KappaChainExitWitness` exists for every dependent reindexed
family: embed it into a base family (`extendReindexedFamily_R3`), run the κ-generalized
compactness chain with `κ := φ₁`, and re-export the everywhere-weak pin against the dependent
family via `transport`.  This is the compiled production instantiation the §6 exit gate
requires. -/
theorem r3_kappaChain_exit (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T) (u₀ : L2Sigma_R3)
    (fill : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n)
    (htest : R3TestApproxH1 𝔊)
    (φ₁ : ℕ → ℕ) (hφ₁ : StrictMono φ₁)
    (galSeq₁ : ∀ k, GalerkinSolutionData_R3 𝔊 F ν u₀ (φ₁ k)) :
    Nonempty (R3KappaChainExitWitness 𝔊 F ν T u₀ φ₁ galSeq₁) := by
  classical
  set base := extendReindexedFamily_R3 𝔊 F ν u₀ φ₁ galSeq₁ fill with hbase
  have htrans : ∀ k, base (φ₁ k) = galSeq₁ k :=
    fun k => extendReindexedFamily_R3_apply 𝔊 F ν u₀ φ₁ hφ₁.injective galSeq₁ fill k
  have alPkg : AubinLionsPackage_R3 𝔊 F ν T u₀ base φ₁ :=
    aubinLionsPackage_R3_of_timeCompactness 𝔊 F ν hν T hT u₀ base
      (localRellichInput_of_frechetKolmogorov frechetKolmogorov_holds) φ₁ hφ₁
  obtain ⟨hmemH1_pkg, hInt_pkg, _⟩ :=
    viscous_lsc_under_strongL2 𝔊 F ν hν T hT u₀ base φ₁ hφ₁ alPkg
  obtain ⟨v, hv_ae, hweak_eq, henergy, htrace, hEC_v, hpin⟩ :=
    galerkin_limit_passage_R3 𝔊 F ν hν T hT u₀ base φ₁ hφ₁ alPkg htest
  exact ⟨{
    base := base
    transport := htrans
    alPkg := alPkg
    energy_class_pkg := ⟨hmemH1_pkg, hInt_pkg⟩
    v := v
    v_ae := hv_ae
    weak_eq := hweak_eq
    energy_ineq := henergy
    initial_trace := htrace
    energy_class_v := hEC_v
    pin := fun t ht z => by simpa only [htrans] using hpin t ht z }⟩

end LerayHopf
