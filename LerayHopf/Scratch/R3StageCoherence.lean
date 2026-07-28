-- SCRATCH — issue #212 B0 feasibility spike (lean-architect). NOT production code.
-- Spike (a) of the ℝ³ global-diagonal design gate: the every-t overlap-coherence step,
-- against the REAL ℝ³ interfaces.
--
-- The honest core of the P4′ Step-4 argument: a per-horizon good representative whose
-- everywhere-weak pin runs along a sub-extraction of the global diagonal agrees
-- POINTWISE (every `t` in the window, not a.e.) with the diagonal weak-limit curve —
-- and hence any two such representatives on nested windows agree on the overlap.
--
-- Why the per-ball structure of the ℝ³ compactness chain does NOT obstruct this:
-- the coherence argument consumes only (i) full-space weak pairings ⟪(galSeq i).u t, z⟫
-- against FIXED test vectors z (the shape `exists_weak_representative_R3` already
-- exports at every t, upgraded internally from per-ball data via
-- `inner_tendsto_of_perball`), and (ii) uniqueness of limits in ℝ plus separation of
-- `L2Sigma_R3` points by `L2Sigma_R3` tests. Neither ingredient mentions balls.
-- All declarations below are fully proved (no sorry, no axioms).
import LerayHopf.R3.SolutionInterfaces

open MeasureTheory Filter Topology Set

namespace LerayHopf
namespace Scratch212

/-- Subspace separation on ℝ³: an `L2Sigma_R3` element is determined by its
`L2Sigma_R3`-tests (mirror of the torus `L2Sigma_eq_of_forall_inner`,
`Torus/DiagonalGalerkin.lean:45`). Since `L2Sigma_R3` is a submodule, `p - q` is again
a valid test vector; pairing the hypothesis against it forces `⟪p - q, p - q⟫ = 0`. -/
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

/-- **Spike (a), core.** The every-t overlap-coherence step against the real ℝ³ types:
if the diagonal pairings converge to `W t` at every `t` in the window (against
`L2Sigma_R3` tests — the stage/diagonal invariant), and a good representative `v`
carries the everywhere-weak pin along a sub-extraction `σ` of the diagonal (against
all `z : L2VF_R3` — the exact conjunct-2 shape of `exists_weak_representative_R3`,
`R3/GoodRepresentative.lean:198`, with `σ := alPkg.φ` after κ-threading), then
`v = W` POINTWISE on the whole window. No a.e.-in-`t` weakening anywhere. -/
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
  -- the pin sequence is a sub-subsequence of the diagonal: compose the diagonal
  -- convergence with `σ → ∞`, then identify the two limits of the SAME ℝ-sequence.
  have hWz := (hW t ht z).comp hσ.tendsto_atTop
  have hpz := hpin t ht ((z : L2VF_R3))
  exact tendsto_nhds_unique hpz hWz

/-- **Spike (a), overlap form.** Two good representatives on nested windows
`[0, T₁] ⊆ [0, T₂]`, each pinned to a sub-extraction of the SAME diagonal, agree
pointwise on the smaller window — the shape the stage-`m` / stage-`m+1` overlap of
the ℝ³ stage recursion needs. -/
theorem r3_representatives_agree_on_overlap
    (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊) (ν : ℝ) (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n)
    (T₁ T₂ : ℝ) (hT : T₁ ≤ T₂) (δ σ₁ σ₂ : ℕ → ℕ)
    (hσ₁ : StrictMono σ₁) (hσ₂ : StrictMono σ₂)
    (W v₁ v₂ : Time → L2Sigma_R3)
    (hW : ∀ t ∈ Set.Icc (0 : ℝ) T₂, ∀ z : L2Sigma_R3,
      Filter.Tendsto
        (fun k => inner (𝕜 := ℝ) (((galSeq (δ k)).u t : L2VF_R3)) ((z : L2VF_R3)))
        Filter.atTop (nhds (inner (𝕜 := ℝ) ((W t : L2VF_R3)) ((z : L2VF_R3)))))
    (hpin₁ : ∀ t ∈ Set.Icc (0 : ℝ) T₁, ∀ z : L2VF_R3,
      Filter.Tendsto
        (fun k => inner (𝕜 := ℝ) (((galSeq (δ (σ₁ k))).u t : L2VF_R3)) z)
        Filter.atTop (nhds (inner (𝕜 := ℝ) ((v₁ t : L2VF_R3)) z)))
    (hpin₂ : ∀ t ∈ Set.Icc (0 : ℝ) T₂, ∀ z : L2VF_R3,
      Filter.Tendsto
        (fun k => inner (𝕜 := ℝ) (((galSeq (δ (σ₂ k))).u t : L2VF_R3)) z)
        Filter.atTop (nhds (inner (𝕜 := ℝ) ((v₂ t : L2VF_R3)) z))) :
    ∀ t ∈ Set.Icc (0 : ℝ) T₁, v₁ t = v₂ t := by
  intro t ht
  have hsub : Set.Icc (0 : ℝ) T₁ ⊆ Set.Icc (0 : ℝ) T₂ := Set.Icc_subset_Icc le_rfl hT
  have hW₁ : ∀ t ∈ Set.Icc (0 : ℝ) T₁, ∀ z : L2Sigma_R3,
      Filter.Tendsto
        (fun k => inner (𝕜 := ℝ) (((galSeq (δ k)).u t : L2VF_R3)) ((z : L2VF_R3)))
        Filter.atTop (nhds (inner (𝕜 := ℝ) ((W t : L2VF_R3)) ((z : L2VF_R3)))) :=
    fun t ht z => hW t (hsub ht) z
  have h₁ := r3_representative_diag_coherence 𝔊 F ν u₀ galSeq T₁ δ σ₁ hσ₁ W v₁ hW₁ hpin₁
  have h₂ := r3_representative_diag_coherence 𝔊 F ν u₀ galSeq T₂ δ σ₂ hσ₂ W v₂ hW hpin₂
  rw [h₁ t ht, h₂ t (hsub ht)]

end Scratch212
end LerayHopf

-- Axiom pins (evidence contract, campaign-doc B0 standard): kernel trio only.
#print axioms LerayHopf.Scratch212.L2Sigma_R3_eq_of_forall_inner
#print axioms LerayHopf.Scratch212.r3_representative_diag_coherence
#print axioms LerayHopf.Scratch212.r3_representatives_agree_on_overlap
