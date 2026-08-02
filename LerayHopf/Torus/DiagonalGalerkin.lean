/-
# LerayHopf.Torus.DiagonalGalerkin — stage recursion + diagonal weak limit (P3, #202)

Assembles the per-horizon stage recursion `stageData m` (built from the κ-generalized
Aubin–Lions handle `exists_limit_curve_of_galSeq` at horizon `T = (m:ℝ)+1`) and the
abstract diagonal engine `LerayHopf.Bochner.DiagonalExtraction` into a single diagonal
subsequence `δ` and a global weak-limit curve `W` that converges weakly (against
`L2Sigma` tests) at every forward time — the packaged theorem
`exists_diagonal_weakly_convergent_galSeq`.

The theorem is generic over an arbitrary base family `galSeq` (a parameter), never
`galSeq_of_torus`; `GalerkinODECapstone` is deliberately not imported.

Scope note (P3 vs P4): this file's coherence is the STAGE-CURVE coherence
`stageData_U_coherent : U a t = U b t`, proved from `z : L2Sigma` tests only via
subspace separation (`L2Sigma_eq_of_forall_inner`).  The representative coherence
`vₘ t = W t` (which consumes the P2 pin against `z : L2VF`) is P4 and lives elsewhere.
-/
import LerayHopf.Bochner.DiagonalExtraction
import LerayHopf.Torus.ModeCompactness

open MeasureTheory Filter Topology Set

namespace LerayHopf

/-- Per-stage recursion carrier: the fresh (relative) extraction `eStep`, the absolute
composed extraction `comp = nestedComp e m`, the stage-`m` weak limit curve `U`, and the
weak-convergence invariant on `Icc 0 (m+1)` along `comp`. -/
structure StageData (F : Torus3NSForms) (ν : ℝ) (u₀ : L2Sigma)
    (galSeq : ∀ n, GalerkinSolutionData F ν u₀ n) (m : ℕ) where
  eStep : ℕ → ℕ
  eStep_mono : StrictMono eStep
  comp : ℕ → ℕ
  comp_mono : StrictMono comp
  U : Time → L2Sigma
  conv : ∀ t ∈ Set.Icc (0 : ℝ) ((m : ℝ) + 1), ∀ z : L2Sigma,
      Filter.Tendsto
        (fun j => inner (𝕜 := ℝ) (((galSeq (comp j)).u t : L2VF)) ((z : L2VF)))
        Filter.atTop
        (nhds (inner (𝕜 := ℝ) ((U t : L2VF)) ((z : L2VF))))

/-- Subspace separation: an `L2Sigma` element is determined by its `L2Sigma`-tests.
Since `L2Sigma` is a submodule, `p - q` is again a valid test vector; pairing the
hypothesis against it forces `⟪p - q, p - q⟫ = 0`, hence `p = q`. -/
theorem L2Sigma_eq_of_forall_inner (p q : L2Sigma)
    (h : ∀ z : L2Sigma,
        inner (𝕜 := ℝ) ((p : L2VF)) ((z : L2VF))
          = inner (𝕜 := ℝ) ((q : L2VF)) ((z : L2VF))) :
    p = q := by
  have hz := h (p - q)
  rw [Submodule.coe_sub] at hz
  have hself : inner (𝕜 := ℝ) ((p : L2VF) - (q : L2VF)) ((p : L2VF) - (q : L2VF)) = 0 := by
    rw [inner_sub_left, hz, sub_self]
  have hd : (p : L2VF) - (q : L2VF) = 0 := by
    rwa [inner_self_eq_zero] at hself
  exact Subtype.ext (sub_eq_zero.mp hd)

/-- Stage recursion (corrected Step 1): stage `m` applies the κ-generalized handle
`exists_limit_curve_of_galSeq` at horizon `T = (m:ℝ)+1`, with `κ := id` at stage 0 and
`κ := (stageData m).comp` at stage `m+1`; the fresh extraction is recorded relatively
(`eStep`) and composed on the right into the absolute extraction (`comp`). -/
noncomputable def stageData
    (F : Torus3NSForms) (ν : ℝ) (hν : 0 < ν) (u₀ : L2Sigma)
    (galSeq : ∀ n, GalerkinSolutionData F ν u₀ n) :
    (m : ℕ) → StageData F ν u₀ galSeq m
  | 0 =>
    let h := exists_limit_curve_of_galSeq F ν hν (((0 : ℕ) : ℝ) + 1) (by norm_num)
      u₀ galSeq id strictMono_id
    { eStep := h.choose
      eStep_mono := h.choose_spec.choose_spec.1
      comp := h.choose
      comp_mono := h.choose_spec.choose_spec.1
      U := h.choose_spec.choose
      conv := h.choose_spec.choose_spec.2.1 }
  | m + 1 =>
    let prev := stageData F ν hν u₀ galSeq m
    let h := exists_limit_curve_of_galSeq F ν hν (((m + 1 : ℕ) : ℝ) + 1) (by positivity)
      u₀ galSeq prev.comp prev.comp_mono
    { eStep := h.choose
      eStep_mono := h.choose_spec.choose_spec.1
      comp := prev.comp ∘ h.choose
      comp_mono := prev.comp_mono.comp h.choose_spec.choose_spec.1
      U := h.choose_spec.choose
      conv := h.choose_spec.choose_spec.2.1 }

/-- Coupling invariant: the absolute stage extraction of the recursion is exactly the
abstract nested composition of the per-stage relative extractions. -/
theorem stageData_comp_eq_nestedComp
    (F : Torus3NSForms) (ν : ℝ) (hν : 0 < ν) (u₀ : L2Sigma)
    (galSeq : ∀ n, GalerkinSolutionData F ν u₀ n) (m : ℕ) :
    (stageData F ν hν u₀ galSeq m).comp
      = LerayHopf.Bochner.nestedComp (fun k => (stageData F ν hν u₀ galSeq k).eStep) m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [LerayHopf.Bochner.nestedComp_succ, ← ih]
    rfl

/-- Stage-to-diagonal limit transfer: at every time in the stage-`m` window, the weak
pairings converge along the single diagonal extraction to the stage-`m` limit. -/
theorem stageData_diag_tendsto
    (F : Torus3NSForms) (ν : ℝ) (hν : 0 < ν) (u₀ : L2Sigma)
    (galSeq : ∀ n, GalerkinSolutionData F ν u₀ n) (m : ℕ)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) ((m : ℝ) + 1)) (z : L2Sigma) :
    Filter.Tendsto
      (fun k => inner (𝕜 := ℝ)
        (((galSeq (LerayHopf.Bochner.diagExtraction
            (fun k => (stageData F ν hν u₀ galSeq k).eStep) k)).u t : L2VF)) ((z : L2VF)))
      Filter.atTop
      (nhds (inner (𝕜 := ℝ) (((stageData F ν hν u₀ galSeq m).U t : L2VF)) ((z : L2VF)))) := by
  have he : ∀ n, StrictMono ((fun k => (stageData F ν hν u₀ galSeq k).eStep) n) :=
    fun n => (stageData F ν hν u₀ galSeq n).eStep_mono
  have hstage : Filter.Tendsto
      (fun j => inner (𝕜 := ℝ)
        (((galSeq (LerayHopf.Bochner.nestedComp
            (fun k => (stageData F ν hν u₀ galSeq k).eStep) m j)).u t : L2VF)) ((z : L2VF)))
      Filter.atTop
      (nhds (inner (𝕜 := ℝ) (((stageData F ν hν u₀ galSeq m).U t : L2VF)) ((z : L2VF)))) := by
    have hconv := (stageData F ν hν u₀ galSeq m).conv t ht z
    rwa [stageData_comp_eq_nestedComp F ν hν u₀ galSeq m] at hconv
  exact LerayHopf.Bochner.tendsto_diag_of_tendsto_stage
    (f := fun n => inner (𝕜 := ℝ) (((galSeq n).u t : L2VF)) ((z : L2VF))) he m hstage

/-- Overlap coherence of the stage limits, from `z : L2Sigma` tests only: at any time
in both stage windows, the two stage limits agree, because both are limits of the SAME
diagonal pairing sequence and `L2Sigma` tests separate `L2Sigma` points. -/
theorem stageData_U_coherent
    (F : Torus3NSForms) (ν : ℝ) (hν : 0 < ν) (u₀ : L2Sigma)
    (galSeq : ∀ n, GalerkinSolutionData F ν u₀ n) (a b : ℕ) (t : ℝ)
    (ha : t ∈ Set.Icc (0 : ℝ) ((a : ℝ) + 1))
    (hb : t ∈ Set.Icc (0 : ℝ) ((b : ℝ) + 1)) :
    (stageData F ν hν u₀ galSeq a).U t = (stageData F ν hν u₀ galSeq b).U t := by
  apply L2Sigma_eq_of_forall_inner
  intro z
  exact tendsto_nhds_unique
    (stageData_diag_tendsto F ν hν u₀ galSeq a t ha z)
    (stageData_diag_tendsto F ν hν u₀ galSeq b t hb z)

/-- The global diagonal weak-limit curve: at time `t`, the limit of the first stage
whose window contains `t` (stage `⌊max t 0⌋`; the stage choice is immaterial by
`stageData_U_coherent`). -/
noncomputable def diagWeakLimit
    (F : Torus3NSForms) (ν : ℝ) (hν : 0 < ν) (u₀ : L2Sigma)
    (galSeq : ∀ n, GalerkinSolutionData F ν u₀ n) : Time → L2Sigma :=
  fun t => (stageData F ν hν u₀ galSeq (Nat.floor (max t 0))).U t

/-- **P3 packaged theorem:** one strictly monotone diagonal subsequence `δ` and one
global curve `W` such that the Galerkin weak pairings against every `L2Sigma` test
converge along `δ` to `W t` at every forward time (uniform window exhaustion in `m`). -/
theorem exists_diagonal_weakly_convergent_galSeq
    (F : Torus3NSForms) (ν : ℝ) (hν : 0 < ν) (u₀ : L2Sigma)
    (galSeq : ∀ n, GalerkinSolutionData F ν u₀ n) :
    ∃ δ : ℕ → ℕ, StrictMono δ ∧ ∃ W : Time → L2Sigma,
      ∀ m : ℕ, ∀ t ∈ Set.Icc (0 : ℝ) ((m : ℝ) + 1), ∀ z : L2Sigma,
        Filter.Tendsto
          (fun k => inner (𝕜 := ℝ) (((galSeq (δ k)).u t : L2VF)) ((z : L2VF)))
          Filter.atTop
          (nhds (inner (𝕜 := ℝ) (((W t) : L2VF)) ((z : L2VF)))) := by
  refine ⟨LerayHopf.Bochner.diagExtraction (fun k => (stageData F ν hν u₀ galSeq k).eStep),
    LerayHopf.Bochner.diagExtraction_strictMono
      (fun k => (stageData F ν hν u₀ galSeq k).eStep_mono),
    diagWeakLimit F ν hν u₀ galSeq, ?_⟩
  intro m t ht z
  have hta : t ∈ Set.Icc (0 : ℝ) ((Nat.floor (max t 0) : ℝ) + 1) := by
    refine ⟨ht.1, ?_⟩
    have hlt : max t 0 < (Nat.floor (max t 0) : ℝ) + 1 := Nat.lt_floor_add_one (max t 0)
    exact (le_max_left t 0).trans hlt.le
  have hcoh : (stageData F ν hν u₀ galSeq m).U t
      = (stageData F ν hν u₀ galSeq (Nat.floor (max t 0))).U t :=
    stageData_U_coherent F ν hν u₀ galSeq m (Nat.floor (max t 0)) t ht hta
  have h := stageData_diag_tendsto F ν hν u₀ galSeq m t ht z
  rw [hcoh] at h
  exact h

end LerayHopf
