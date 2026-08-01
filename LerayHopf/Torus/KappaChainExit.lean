/-
# P2 (#201) exit gate — κ-chain acceptance artifact

This module promotes the issue #195 feasibility spike
(`LerayHopf/Scratch/KappaReindex.lean`, `LerayHopf/Scratch/P2ExitContract.lean`)
to production: the dependent-family embedding `extendReindexedFamily` and the typed
acceptance artifact `P2ExitWitness`, together with the production theorem
`torus_kappaChain_exit` that instantiates it end-to-end.

Per the campaign doc §5 P2 exit gate (hardened at codex pass-3 G-1 into a typed
artifact), P2 is complete exactly when a production theorem of the shape

  `∀ F ν hν T hT u₀ φ₁ (hφ₁ : StrictMono φ₁) galSeq₁,
      Nonempty (P2ExitWitness F ν T u₀ φ₁ galSeq₁)`

is compiled.  `torus_kappaChain_exit` below is that theorem.  The witness runs the
κ-generalized compactness chain (`torusAubinLionsPackage_of_galSeq` →
`torus_energyClass_of_aubinLions` → `torus_galerkin_limit_passage_of_energyClass`)
over a base family with outer index map `κ := φ₁`, and the mandatory `transport`
field binds that base family to the GIVEN dependent family `galSeq₁` — an unlinked
fresh family cannot instantiate the artifact.  The everywhere-weak pin is the final
conjunct that P2's strengthening added to `torus_galerkin_limit_passage_of_energyClass`,
re-exported here phrased against `galSeq₁` itself via `transport`.
-/
import LerayHopf.Torus.AubinLionsAssembly
import LerayHopf.Torus.ViscousLimit
import LerayHopf.Torus.TraceEnergy
import LerayHopf.Torus.GalerkinODECapstone
import LerayHopf.Torus.H1Sigma

open MeasureTheory Filter Topology Set

namespace LerayHopf

open Classical in
/-- Embed a dependent reindexed family `galSeq₁ : ∀ k, GalerkinSolutionData F ν u₀ (φ₁ k)`
into a full base family: at `φ₁ k` take the given datum, elsewhere the canonical
axiom-free `galSeq_of_torus` datum (which exists unconditionally because the torus
Galerkin ODE layer is total). -/
noncomputable def extendReindexedFamily
    (F : Torus3NSForms) (ν : ℝ) (hν : 0 < ν) (u₀ : L2Sigma)
    (φ₁ : ℕ → ℕ) (galSeq₁ : ∀ k, GalerkinSolutionData F ν u₀ (φ₁ k)) :
    ∀ n, GalerkinSolutionData F ν u₀ n := fun n =>
  if h : ∃ k, φ₁ k = n then (Classical.choose_spec h) ▸ galSeq₁ (Classical.choose h)
  else galSeq_of_torus F ν hν u₀ n

/-- On the subsequence the embedding restores the given data on the nose (needs only
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

/-- **Typed P2 exit contract (production).**  A witness certifies that the
κ-generalized torus compactness chain runs end-to-end over a base family bound (via
`transport`) to the given dependent family `galSeq₁`, with outer index map
`κ := φ₁` — the index map selecting which entries of the original Galerkin family are
used, the package choosing its own extraction `φ` internally so that convergence is
stated along the composed index map `κ ∘ φ`.  Field types are the production conclusions
of the chain stages; the pin is phrased against `galSeq₁` itself. -/
structure P2ExitWitness (F : Torus3NSForms) (ν T : ℝ) (u₀ : L2Sigma)
    (φ₁ : ℕ → ℕ) (galSeq₁ : ∀ k, GalerkinSolutionData F ν u₀ (φ₁ k)) where
  /-- The full base family the κ-generalized chain runs over. -/
  base : ∀ n, GalerkinSolutionData F ν u₀ n
  /-- **Mandatory transport equality**: along `φ₁`, `base` IS the given dependent family. -/
  transport : ∀ k, base (φ₁ k) = galSeq₁ k
  /-- Stage 1 — Aubin–Lions package over `base` with outer index map `κ := φ₁`. -/
  alPkg : AubinLionsPackage F ν T u₀ base φ₁
  /-- Stage 2 — energy class for the package curve. -/
  energy_class_pkg :
    (∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)), memH1VF (alPkg.u t : L2VF)) ∧
      IntervalIntegrable (fun s => viscousFormSq ν (alPkg.u s : L2VF)) volume 0 T
  /-- The good representative produced by limit passage. -/
  v : Time → L2Sigma
  /-- Representative a.e.-linked to the package curve on `[0, T]`. -/
  v_ae : ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)), v t = alPkg.u t
  /-- Stage 3 — weak-form limit passage for the representative. -/
  weak_eq : WeakFormNS ν T (torus3Evolution F) v
  /-- Stage 3 — energy inequality (∀t form). -/
  energy_ineq : ∀ t, 0 ≤ t → t ≤ T →
    (1 / 2 : ℝ) * ‖(v t : L2VF)‖ ^ 2 +
      ∫ s in (0 : ℝ)..t, viscousFormSq ν (v s : L2VF) ≤
    (1 / 2 : ℝ) * ‖(u₀ : L2VF)‖ ^ 2
  /-- Stage 3 — strong initial trace. -/
  initial_trace : Filter.Tendsto (fun t => (v t : L2VF))
    (nhdsWithin 0 (Set.Ici 0)) (nhds (u₀ : L2VF))
  /-- Stage 3 — energy class re-exported for the representative. -/
  energy_class_v :
    (∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)), memH1VF (v t : L2VF)) ∧
      IntervalIntegrable (fun s => viscousFormSq ν (v s : L2VF)) volume 0 T
  /-- Stage 4 — the sub-extraction of the representative pin. -/
  ρ : ℕ → ℕ
  /-- Strict monotonicity of the sub-extraction. -/
  ρ_mono : StrictMono ρ
  /-- Stage 4 — **everywhere weak-convergence pin, phrased against `galSeq₁` ITSELF**. -/
  pin : ∀ t, t ∈ Set.Icc (0 : ℝ) T → ∀ z : L2VF,
    Filter.Tendsto
      (fun k => inner (𝕜 := ℝ) (((galSeq₁ (alPkg.φ (ρ k))).u t : L2VF)) z)
      Filter.atTop (nhds (inner (𝕜 := ℝ) ((v t : L2VF)) z))

/-- **P2 (#201) exit gate.**  A `P2ExitWitness` exists for every dependent reindexed
family: embed it into a base family (`extendReindexedFamily`), run the κ-generalized
compactness chain with `κ := φ₁`, and re-export the everywhere-weak pin against the
dependent family via `transport`.  This is the compiled production instantiation the
§5 P2 exit gate requires. -/
theorem torus_kappaChain_exit (F : Torus3NSForms) (ν : ℝ) (hν : 0 < ν)
    (T : ℝ) (hT : 0 < T) (u₀ : L2Sigma) (φ₁ : ℕ → ℕ) (hφ₁ : StrictMono φ₁)
    (galSeq₁ : ∀ k, GalerkinSolutionData F ν u₀ (φ₁ k)) :
    Nonempty (P2ExitWitness F ν T u₀ φ₁ galSeq₁) := by
  classical
  have htrans : ∀ k, extendReindexedFamily F ν hν u₀ φ₁ galSeq₁ (φ₁ k) = galSeq₁ k :=
    fun k => extendReindexedFamily_apply F ν hν u₀ φ₁ hφ₁.injective galSeq₁ k
  have alPkg : AubinLionsPackage F ν T u₀ (extendReindexedFamily F ν hν u₀ φ₁ galSeq₁) φ₁ :=
    torusAubinLionsPackage_of_galSeq F ν hν T hT u₀
      (extendReindexedFamily F ν hν u₀ φ₁ galSeq₁) φ₁ hφ₁ rellich_L2Sigma
  have hEC := torus_energyClass_of_aubinLions F ν hν T hT u₀
    (extendReindexedFamily F ν hν u₀ φ₁ galSeq₁) φ₁ hφ₁ alPkg
  obtain ⟨v, hv_ae, hweak_eq, henergy, htrace, hEC_v, ρ, hρ, hpin⟩ :=
    torus_galerkin_limit_passage_of_energyClass F ν hν T hT u₀
      (extendReindexedFamily F ν hν u₀ φ₁ galSeq₁) φ₁ hφ₁ alPkg hEC
  exact ⟨{
    base := extendReindexedFamily F ν hν u₀ φ₁ galSeq₁
    transport := htrans
    alPkg := alPkg
    energy_class_pkg := hEC
    v := v
    v_ae := hv_ae
    weak_eq := hweak_eq
    energy_ineq := henergy
    initial_trace := htrace
    energy_class_v := hEC_v
    ρ := ρ
    ρ_mono := hρ
    pin := fun t ht z => by simpa only [htrans] using hpin t ht z }⟩

end LerayHopf
