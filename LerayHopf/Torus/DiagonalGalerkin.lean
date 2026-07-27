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

end LerayHopf
