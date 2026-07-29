/-
# LerayHopf.R3.DiagonalGalerkin — ℝ³ stage recursion + diagonal weak limit (P3′, #216)

Assembles the per-horizon stage recursion `stageData_R3 m` (built from the ℝ³ stage handle
`exists_weakLimitCurve_R3_kappa` at horizon `T = (m:ℝ)+1`) and the abstract diagonal engine
`LerayHopf.Bochner.DiagonalExtraction` (reused VERBATIM — zero new order theory) into a
single diagonal subsequence `δ` and a global weak-limit curve `W` that converges weakly
(against the FULL ambient `L2VF_R3` tests) at every forward time — the packaged theorem
`exists_diagonal_weakly_convergent_galSeq_R3`.

Declaration-for-declaration mirror of the merged torus template
`LerayHopf/Torus/DiagonalGalerkin.lean` (issue #202 P3), with the ℝ³ substitutions from
`docs/scratch/r3-global-diagonal-campaign.md` §2.2 Steps 1–2.

**Stage handle (§2.2 Step 1).** `exists_weakLimitCurve_R3_kappa` composes two P2′ outputs:
the κ-generalized `aubinLionsPackage_R3_of_timeCompactness` (with the concrete, unconditional
FK-derived local Rellich input — so the handle needs `Rell` but NOT `htest`, there being no
`WeakFormNS` at stage level) followed by `exists_weak_representative_R3`.  The returned `φ`
is `alPkg.φ`; the pin runs along `κ ∘ alPkg.φ` directly (no torus-style sub-extraction `ρ`,
because `exists_weak_representative_R3` already pins along `alPkg.φ`).

**Invariant strength vs. torus.** The stage/diagonal invariant here tests over the FULL
`L2VF_R3` (not the torus `L2Sigma`), because `exists_weak_representative_R3`'s pin is already
full-space.  This is strictly stronger than the `L2Sigma_R3`-test form spike (a) needs, and
directly supplies the P4′ coherence step's `hW`.

The theorem is generic over an arbitrary base family `galSeq` (a parameter), never the
concrete `galSeq_R3_of_basis`; `GalerkinODECapstone` is deliberately not imported.

Scope note (P3′ vs P4′): this file's coherence is the STAGE-CURVE coherence
`stageData_R3_U_coherent : U a t = U b t`, proved from `z : L2Sigma_R3` tests only via
subspace separation (`L2Sigma_R3_eq_of_forall_inner`).  The representative coherence
`v t = W t` (which consumes the P4′ per-horizon exit-witness pin against `z : L2VF_R3`) is
promoted here as the coherence CORE `r3_representative_diag_coherence` and applied to the
diagonal output in `exists_diag_coherent_representative_R3` (§787–792 hW-coupling deliverable),
but the full P4′ contract assembly lives in `R3/GlobalCapstone.lean`.
-/
import LerayHopf.Bochner.DiagonalExtraction
import LerayHopf.R3.KappaChainExit

open MeasureTheory Filter Topology Set

namespace LerayHopf

/-- **Stage handle (§2.2 Step 1).** Composition of two P2′ outputs into a single weak-limit
curve: `aubinLionsPackage_R3_of_timeCompactness` (with the concrete FK-derived local Rellich
input) produces the Aubin–Lions package with effective mode map `κ`, then
`exists_weak_representative_R3` produces a curve `U` whose FULL-space weak pairings converge
at every `t ∈ [0,T]` along the effective index `κ ∘ alPkg.φ`.  The returned extraction is
`alPkg.φ` (κ threaded separately in the pin — torus-parity shape).  Needs `Rell` (supplied
internally, concrete and unconditional) but NOT `htest`. -/
theorem exists_weakLimitCurve_R3_kappa
    (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊) (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T)
    (u₀ : L2Sigma_R3) (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n)
    (κ : ℕ → ℕ) (hκ : StrictMono κ) :
    ∃ (φ : ℕ → ℕ) (U : Time → L2Sigma_R3), StrictMono φ ∧
      ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ z : L2VF_R3,
        Filter.Tendsto
          (fun n => inner (𝕜 := ℝ) (((galSeq (κ (φ n))).u t : L2VF_R3)) z)
          Filter.atTop
          (nhds (inner (𝕜 := ℝ) ((U t : L2VF_R3)) z)) := by
  classical
  have alPkg : AubinLionsPackage_R3 𝔊 F ν T u₀ galSeq κ :=
    aubinLionsPackage_R3_of_timeCompactness 𝔊 F ν hν T hT u₀ galSeq
      (localRellichInput_of_frechetKolmogorov frechetKolmogorov_holds) κ hκ
  obtain ⟨v, _hv_ae, hpin, _hbound, _hinit, _hlip⟩ :=
    exists_weak_representative_R3 𝔊 F ν hν T hT u₀ galSeq κ hκ alPkg
  exact ⟨alPkg.φ, v, alPkg.φ_mono, hpin⟩ -- KAPPA_ID_SITE: `alPkg.φ_mono` is the RETURNED raw extraction's own monotonicity (torus-parity handle shape, §2.2 Step 1: φ := alPkg.φ, κ threaded separately in the pin), not a category-(iii) index-selection fact

/-- Subspace separation on ℝ³: an `L2Sigma_R3` element is determined by its
`L2Sigma_R3`-tests (production promotion of spike (a)'s
`Scratch212.L2Sigma_R3_eq_of_forall_inner`, mirror of the torus
`L2Sigma_eq_of_forall_inner`, `Torus/DiagonalGalerkin.lean:45`).  Since `L2Sigma_R3` is a
submodule, `p - q` is again a valid test vector; pairing the hypothesis against it forces
`⟪p - q, p - q⟫ = 0`, hence `p = q`. -/
theorem L2Sigma_R3_eq_of_forall_inner (p q : L2Sigma_R3)
    (h : ∀ z : L2Sigma_R3,
        inner (𝕜 := ℝ) ((p : L2VF_R3)) ((z : L2VF_R3))
          = inner (𝕜 := ℝ) ((q : L2VF_R3)) ((z : L2VF_R3))) :
    p = q := by
  have hz := h (p - q)
  rw [Submodule.coe_sub] at hz
  have hself : inner (𝕜 := ℝ) ((p : L2VF_R3) - (q : L2VF_R3))
      ((p : L2VF_R3) - (q : L2VF_R3)) = 0 := by
    rw [inner_sub_left, hz, sub_self]
  have hd : (p : L2VF_R3) - (q : L2VF_R3) = 0 := by
    rwa [inner_self_eq_zero] at hself
  exact Subtype.ext (sub_eq_zero.mp hd)

/-- Per-stage recursion carrier: the fresh (relative) extraction `eStep`, the absolute
composed extraction `comp = nestedComp e m`, the stage-`m` weak limit curve `U`, and the
weak-convergence invariant on `Icc 0 (m+1)` along `comp`, tested over the FULL `L2VF_R3`. -/
structure StageData_R3 (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊) (ν : ℝ) (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n) (m : ℕ) where
  eStep : ℕ → ℕ
  eStep_mono : StrictMono eStep
  comp : ℕ → ℕ
  comp_mono : StrictMono comp
  U : Time → L2Sigma_R3
  conv : ∀ t ∈ Set.Icc (0 : ℝ) ((m : ℝ) + 1), ∀ z : L2VF_R3,
      Filter.Tendsto
        (fun j => inner (𝕜 := ℝ) (((galSeq (comp j)).u t : L2VF_R3)) z)
        Filter.atTop
        (nhds (inner (𝕜 := ℝ) ((U t : L2VF_R3)) z))

/-- Stage recursion (§2.2 Step 1): stage `m` applies the ℝ³ stage handle
`exists_weakLimitCurve_R3_kappa` at horizon `T = (m:ℝ)+1`, with `κ := id` at stage 0 and
`κ := (stageData_R3 m).comp` at stage `m+1`; the fresh extraction is recorded relatively
(`eStep`) and composed on the right into the absolute extraction (`comp`). -/
noncomputable def stageData_R3
    (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊) (ν : ℝ) (hν : 0 < ν) (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n) :
    (m : ℕ) → StageData_R3 𝔊 F ν u₀ galSeq m
  | 0 =>
    let h := exists_weakLimitCurve_R3_kappa 𝔊 F ν hν (((0 : ℕ) : ℝ) + 1) (by norm_num)
      u₀ galSeq id strictMono_id
    { eStep := h.choose
      eStep_mono := h.choose_spec.choose_spec.1
      comp := h.choose
      comp_mono := h.choose_spec.choose_spec.1
      U := h.choose_spec.choose
      conv := h.choose_spec.choose_spec.2 }
  | m + 1 =>
    let prev := stageData_R3 𝔊 F ν hν u₀ galSeq m
    let h := exists_weakLimitCurve_R3_kappa 𝔊 F ν hν (((m + 1 : ℕ) : ℝ) + 1) (by positivity)
      u₀ galSeq prev.comp prev.comp_mono
    { eStep := h.choose
      eStep_mono := h.choose_spec.choose_spec.1
      comp := prev.comp ∘ h.choose
      comp_mono := prev.comp_mono.comp h.choose_spec.choose_spec.1
      U := h.choose_spec.choose
      conv := h.choose_spec.choose_spec.2 }

/-- Coupling invariant: the absolute stage extraction of the recursion is exactly the
abstract nested composition of the per-stage relative extractions. -/
theorem stageData_R3_comp_eq_nestedComp
    (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊) (ν : ℝ) (hν : 0 < ν) (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n) (m : ℕ) :
    (stageData_R3 𝔊 F ν hν u₀ galSeq m).comp
      = LerayHopf.Bochner.nestedComp
          (fun k => (stageData_R3 𝔊 F ν hν u₀ galSeq k).eStep) m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [LerayHopf.Bochner.nestedComp_succ, ← ih]
    rfl

/-- Stage-to-diagonal limit transfer: at every time in the stage-`m` window, the weak
pairings converge along the single diagonal extraction to the stage-`m` limit. -/
theorem stageData_R3_diag_tendsto
    (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊) (ν : ℝ) (hν : 0 < ν) (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n) (m : ℕ)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) ((m : ℝ) + 1)) (z : L2VF_R3) :
    Filter.Tendsto
      (fun k => inner (𝕜 := ℝ)
        (((galSeq (LerayHopf.Bochner.diagExtraction
            (fun k => (stageData_R3 𝔊 F ν hν u₀ galSeq k).eStep) k)).u t : L2VF_R3)) z)
      Filter.atTop
      (nhds (inner (𝕜 := ℝ) (((stageData_R3 𝔊 F ν hν u₀ galSeq m).U t : L2VF_R3)) z)) := by
  have he : ∀ n, StrictMono ((fun k => (stageData_R3 𝔊 F ν hν u₀ galSeq k).eStep) n) :=
    fun n => (stageData_R3 𝔊 F ν hν u₀ galSeq n).eStep_mono
  have hstage : Filter.Tendsto
      (fun j => inner (𝕜 := ℝ)
        (((galSeq (LerayHopf.Bochner.nestedComp
            (fun k => (stageData_R3 𝔊 F ν hν u₀ galSeq k).eStep) m j)).u t : L2VF_R3)) z)
      Filter.atTop
      (nhds (inner (𝕜 := ℝ) (((stageData_R3 𝔊 F ν hν u₀ galSeq m).U t : L2VF_R3)) z)) := by
    have hconv := (stageData_R3 𝔊 F ν hν u₀ galSeq m).conv t ht z
    rwa [stageData_R3_comp_eq_nestedComp 𝔊 F ν hν u₀ galSeq m] at hconv
  exact LerayHopf.Bochner.tendsto_diag_of_tendsto_stage
    (f := fun n => inner (𝕜 := ℝ) (((galSeq n).u t : L2VF_R3)) z) he m hstage

/-- Overlap coherence of the stage limits, from `z : L2Sigma_R3` tests only: at any time
in both stage windows, the two stage limits agree, because both are limits of the SAME
diagonal pairing sequence and `L2Sigma_R3` tests separate `L2Sigma_R3` points. -/
theorem stageData_R3_U_coherent
    (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊) (ν : ℝ) (hν : 0 < ν) (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n) (a b : ℕ) (t : ℝ)
    (ha : t ∈ Set.Icc (0 : ℝ) ((a : ℝ) + 1))
    (hb : t ∈ Set.Icc (0 : ℝ) ((b : ℝ) + 1)) :
    (stageData_R3 𝔊 F ν hν u₀ galSeq a).U t
      = (stageData_R3 𝔊 F ν hν u₀ galSeq b).U t := by
  apply L2Sigma_R3_eq_of_forall_inner
  intro z
  exact tendsto_nhds_unique
    (stageData_R3_diag_tendsto 𝔊 F ν hν u₀ galSeq a t ha (z : L2VF_R3))
    (stageData_R3_diag_tendsto 𝔊 F ν hν u₀ galSeq b t hb (z : L2VF_R3))

/-- The global diagonal weak-limit curve: at time `t`, the limit of the first stage
whose window contains `t` (stage `⌊max t 0⌋`; the stage choice is immaterial by
`stageData_R3_U_coherent`). -/
noncomputable def diagWeakLimit_R3
    (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊) (ν : ℝ) (hν : 0 < ν) (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n) : Time → L2Sigma_R3 :=
  fun t => (stageData_R3 𝔊 F ν hν u₀ galSeq (Nat.floor (max t 0))).U t

/-- **P3′ packaged theorem:** one strictly monotone diagonal subsequence `δ` and one
global curve `W` such that the Galerkin weak pairings against every FULL-space `L2VF_R3`
test converge along `δ` to `W t` at every forward time (uniform window exhaustion in `m`). -/
theorem exists_diagonal_weakly_convergent_galSeq_R3
    (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊) (ν : ℝ) (hν : 0 < ν) (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n) :
    ∃ δ : ℕ → ℕ, StrictMono δ ∧ ∃ W : Time → L2Sigma_R3,
      ∀ m : ℕ, ∀ t ∈ Set.Icc (0 : ℝ) ((m : ℝ) + 1), ∀ z : L2VF_R3,
        Filter.Tendsto
          (fun k => inner (𝕜 := ℝ) (((galSeq (δ k)).u t : L2VF_R3)) z)
          Filter.atTop
          (nhds (inner (𝕜 := ℝ) (((W t) : L2VF_R3)) z)) := by
  refine ⟨LerayHopf.Bochner.diagExtraction
      (fun k => (stageData_R3 𝔊 F ν hν u₀ galSeq k).eStep),
    LerayHopf.Bochner.diagExtraction_strictMono
      (fun k => (stageData_R3 𝔊 F ν hν u₀ galSeq k).eStep_mono),
    diagWeakLimit_R3 𝔊 F ν hν u₀ galSeq, ?_⟩
  intro m t ht z
  have hta : t ∈ Set.Icc (0 : ℝ) ((Nat.floor (max t 0) : ℝ) + 1) := by
    refine ⟨ht.1, ?_⟩
    have hlt : max t 0 < (Nat.floor (max t 0) : ℝ) + 1 := Nat.lt_floor_add_one (max t 0)
    exact (le_max_left t 0).trans hlt.le
  have hcoh : (stageData_R3 𝔊 F ν hν u₀ galSeq m).U t
      = (stageData_R3 𝔊 F ν hν u₀ galSeq (Nat.floor (max t 0))).U t :=
    stageData_R3_U_coherent 𝔊 F ν hν u₀ galSeq m (Nat.floor (max t 0)) t ht hta
  have h := stageData_R3_diag_tendsto 𝔊 F ν hν u₀ galSeq m t ht z
  rw [hcoh] at h
  exact h

/-- **Coherence core (production promotion of spike (a)'s `r3_representative_diag_coherence`,
`Scratch/R3StageCoherence.lean:49`).**  The every-`t` overlap-coherence step against the ℝ³
types: if the diagonal pairings converge to `W t` at every `t` in the window (against
`L2Sigma_R3` tests — the stage/diagonal invariant `hW`), and a good representative `v`
carries the everywhere-weak pin along a sub-extraction `σ` of the diagonal (against all
`z : L2VF_R3` — the exact conjunct-2 shape of `exists_weak_representative_R3` after
κ-threading, i.e. the P4′ per-horizon exit-witness `pin`), then `v = W` POINTWISE on the
whole window.  No a.e.-in-`t` weakening anywhere. -/
theorem r3_representative_diag_coherence
    (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊) (ν : ℝ) (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n)
    (T : ℝ) (δ σ : ℕ → ℕ) (hσ : StrictMono σ)
    (W v : Time → L2Sigma_R3)
    (hW : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ z : L2Sigma_R3,
      Filter.Tendsto
        (fun k => inner (𝕜 := ℝ) (((galSeq (δ k)).u t : L2VF_R3)) ((z : L2VF_R3)))
        Filter.atTop (nhds (inner (𝕜 := ℝ) ((W t : L2VF_R3)) ((z : L2VF_R3)))))
    (hpin : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ z : L2VF_R3,
      Filter.Tendsto
        (fun k => inner (𝕜 := ℝ) (((galSeq (δ (σ k))).u t : L2VF_R3)) z)
        Filter.atTop (nhds (inner (𝕜 := ℝ) ((v t : L2VF_R3)) z))) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, v t = W t := by
  intro t ht
  apply L2Sigma_R3_eq_of_forall_inner
  intro z
  have hWz := (hW t ht z).comp hσ.tendsto_atTop
  have hpz := hpin t ht ((z : L2VF_R3))
  exact tendsto_nhds_unique hpz hWz

/-- **P3′ hW-coupling deliverable (§787–792).**  A compiled application of the promoted
coherence core `r3_representative_diag_coherence` to the ACTUAL stage/diagonal output of
`exists_diagonal_weakly_convergent_galSeq_R3`: the diagonal weak-limit `W` supplies EXACTLY
spike (a)'s `hW` hypothesis type at every horizon `Tₘ = (m:ℝ)+1` (the packaged `L2VF_R3`
invariant restricts to the `L2Sigma_R3`-test `hW` on the nose), so any good representative
`v` pinned along a sub-extraction `σ` of the diagonal (the P4′ per-horizon exit-witness pin
against `z : L2VF_R3`) agrees with `W` pointwise on `[0, Tₘ]`.  This certifies the stage side
of the P4′ coherence step compiles against the coherence lemma's exact input type; P4′
supplies `hpin` from the `R3KappaChainExitWitness`. -/
theorem exists_diag_coherent_representative_R3
    (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊) (ν : ℝ) (hν : 0 < ν) (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n) :
    ∃ δ : ℕ → ℕ, StrictMono δ ∧ ∃ W : Time → L2Sigma_R3,
      ∀ (m : ℕ) (σ : ℕ → ℕ), StrictMono σ → ∀ v : Time → L2Sigma_R3,
        (∀ t ∈ Set.Icc (0 : ℝ) ((m : ℝ) + 1), ∀ z : L2VF_R3,
          Filter.Tendsto
            (fun k => inner (𝕜 := ℝ) (((galSeq (δ (σ k))).u t : L2VF_R3)) z)
            Filter.atTop (nhds (inner (𝕜 := ℝ) ((v t : L2VF_R3)) z))) →
        ∀ t ∈ Set.Icc (0 : ℝ) ((m : ℝ) + 1), v t = W t := by
  obtain ⟨δ, hδ, W, hW⟩ := exists_diagonal_weakly_convergent_galSeq_R3 𝔊 F ν hν u₀ galSeq
  refine ⟨δ, hδ, W, ?_⟩
  intro m σ hσ v hpin
  refine r3_representative_diag_coherence 𝔊 F ν u₀ galSeq ((m : ℝ) + 1) δ σ hσ W v ?_ hpin
  intro t ht z
  exact hW m t ht (z : L2VF_R3)

end LerayHopf
