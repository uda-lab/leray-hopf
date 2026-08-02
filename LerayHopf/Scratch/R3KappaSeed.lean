-- SCRATCH — issue #212 B0 feasibility spike (lean-architect). NOT production code.
-- Spike (b) of the ℝ³ global-diagonal design gate: κ-threading feasibility through the
-- sealed wrapper layers of the ℝ³ compactness chain, against the REAL interfaces.
--
-- The ℝ³ chain's root primitive (`galerkin_spacetime_precompact_R3` /
-- `perBall_ae_subseq`) is already refine-capable (takes an arbitrary external strictly
-- monotone `ψ`), but `diag_ae_subseq` consumes it into an internally seeded per-ball
-- Cantor tower (`Φ 0 = id`) and does not re-expose the input. This spike compiles the
-- κ-seeded versions of the two deepest sealed layers:
--
--   1. `diag_ae_subseq_seeded` — the per-ball Cantor tower with an EXTERNAL seed
--      `κ` composed in by PRE-composition: every tower step feeds `κ ∘ Φ k` to the
--      refine-capable `perBall_ae_subseq`; the tower's internal factorization
--      (`nested_extraction_factor` over `Φ`/`ρ`) is untouched because `κ` only ever
--      applies OUTSIDE the tower maps, at datum-index positions. The conclusion is the
--      production conclusion with the effective index `κ (φ n)` — the exact "base + κ"
--      shape validated by the torus campaign (§3 of the #195 campaign doc).
--   2. `spacetime_extraction_seeded` — the next wrapper up
--      (`u_lim_aestronglyMeasurable` shape): the seeded tower's output composes with
--      the extraction-generic `galerkin_weakLimit_R3` (which needs NO change — it
--      already takes an arbitrary extraction) to produce the measurable limit curve
--      with per-ball a.e.-t convergence along `κ ∘ φ`.
--
-- Layers 3–4 (`galerkinSpaceTimeExtraction_R3`, `aubinLionsPackage_R3_of_timeCompactness`)
-- are delegating/assembling wrappers over exactly this output; their κ-forms are the
-- P2′ production content (campaign doc §5), guarded by the P2′ kill criterion.
-- All declarations below are fully proved (no sorry, no axioms).
import LerayHopf.R3.ArzelaAscoliTime

open MeasureTheory Filter Topology Set

namespace LerayHopf
namespace Scratch212

/-- **Spike (b), layer 1.** κ-seeded per-ball Cantor diagonal: the production
`diag_ae_subseq` (`R3/ArzelaAscoliTime.lean:839`) generalized over an external
strictly monotone seed `κ`, with the tower fed `κ ∘ Φ k` at every level and the
conclusion's effective datum index `κ (φ n)`. Instantiating `κ := id` recovers the
production statement shape. The proof is the production body with `κ` threaded
through the datum-index positions only. -/
theorem diag_ae_subseq_seeded
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
            Filter.atTop (nhds (g_k t)) := by
  classical
  -- Cumulative extraction tower, as in production, except each refine-capable step is
  -- applied to the κ-PRE-COMPOSED current subsequence `κ ∘ ψ`.
  let stepData : ∀ (k : ℕ) (ψ : ℕ → ℕ), StrictMono ψ →
      { ρ : ℕ → ℕ // StrictMono ρ ∧ ∃ g : ℝ → L2ballR3 k,
        AEStronglyMeasurable g (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)) ∧
        ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)), Filter.Tendsto
          (fun n => restrictToBall k ((galSeq (κ (ψ (ρ n)))).u t : L2VF_R3))
          Filter.atTop (nhds (g t)) } :=
    fun k ψ hψ =>
      let h := perBall_ae_subseq 𝔊 F ν hν T hT u₀ galSeq (κ ∘ ψ) (hκ.comp hψ) k
      ⟨h.choose, h.choose_spec.choose_spec.1,
        h.choose_spec.choose, h.choose_spec.choose_spec.2.1, h.choose_spec.choose_spec.2.2⟩
  -- Recursively build the cumulative extraction `Φ k`, with `Φ (k+1) = Φ k ∘ ρ k`.
  -- `κ` is NOT part of the tower maps — it stays outside, so the factorization
  -- machinery below is the production one verbatim.
  let rec_data : ℕ → { Φk : ℕ → ℕ // StrictMono Φk } := fun k => Nat.rec
    (⟨id, strictMono_id⟩)
    (fun j prev => ⟨prev.1 ∘ (stepData j prev.1 prev.2).1,
      prev.2.comp (stepData j prev.1 prev.2).2.1⟩) k
  let Φ : ℕ → ℕ → ℕ := fun k => (rec_data k).1
  let ρ : ℕ → ℕ → ℕ := fun k => (stepData k (rec_data k).1 (rec_data k).2).1
  have hΦmono : ∀ k, StrictMono (Φ k) := fun k => (rec_data k).2
  have hρmono : ∀ k, StrictMono (ρ k) := fun k =>
    (stepData k (rec_data k).1 (rec_data k).2).2.1
  have hstep : ∀ k, Φ (k + 1) = Φ k ∘ ρ k := fun k => rfl
  -- At each level `k`, the cumulative extraction `Φ (k+1)` converges on ball `k`
  -- (a.e.-t), with the effective datum index `κ (Φ (k+1) n)`.
  have hconv : ∀ k : ℕ, ∃ g : ℝ → L2ballR3 k,
      AEStronglyMeasurable g (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)) ∧
      ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)), Filter.Tendsto
        (fun n => restrictToBall k ((galSeq (κ (Φ (k + 1) n))).u t : L2VF_R3))
        Filter.atTop (nhds (g t)) := by
    intro k
    obtain ⟨g, hg_aesm, hg_ae⟩ := (stepData k (rec_data k).1 (rec_data k).2).2.2
    exact ⟨g, hg_aesm, hg_ae⟩
  -- The diagonal subsequence (production argument, unchanged: `κ` plays no role in
  -- the strict monotonicity of the tower or its factorization).
  refine ⟨fun n => Φ (n + 1) (n + 1), ?_, ?_⟩
  · intro a b hab
    have h1 : Φ (a + 1) (a + 1) < Φ (a + 1) (b + 1) := hΦmono (a + 1) (by omega)
    obtain ⟨R, hR, hReq⟩ :=
      nested_extraction_factor Φ ρ hρmono hstep (a + 1) (b + 1) (by omega)
    have h2 : Φ (a + 1) (b + 1) ≤ Φ (b + 1) (b + 1) := by
      rw [hReq]
      exact (hΦmono (a + 1)).monotone (hR.id_le (b + 1))
    exact lt_of_lt_of_le h1 h2
  · -- Per-ball a.e.-t convergence of the diagonal, along the κ-composed index.
    intro k
    obtain ⟨g, hg_aesm, hg_ae⟩ := hconv k
    refine ⟨g, hg_aesm, ?_⟩
    have hfact : ∀ n, k ≤ n → ∃ s : ℕ, n + 1 ≤ s ∧ Φ (n + 1) (n + 1) = Φ (k + 1) s := by
      intro n hn
      obtain ⟨R, hR, hReq⟩ :=
        nested_extraction_factor Φ ρ hρmono hstep (k + 1) (n + 1) (by omega)
      refine ⟨R (n + 1), hR.id_le (n + 1), ?_⟩
      rw [hReq]; rfl
    choose s hs_ge hs_eq using fun n (hn : k ≤ n) => hfact n hn
    set σ : ℕ → ℕ := fun n => if hn : k ≤ n then s n hn else n + 1 with hσ
    have hσ_ge : ∀ n, k ≤ n → n + 1 ≤ σ n := by
      intro n hn; simp only [hσ, dif_pos hn]; exact hs_ge n hn
    have hσ_eq : ∀ n, k ≤ n → Φ (n + 1) (n + 1) = Φ (k + 1) (σ n) := by
      intro n hn; simp only [hσ, dif_pos hn]; exact hs_eq n hn
    have hσ_top : Filter.Tendsto σ Filter.atTop Filter.atTop := by
      refine tendsto_atTop_mono' Filter.atTop ?_ tendsto_id
      filter_upwards [eventually_ge_atTop k] with n hn
      show n ≤ σ n
      exact le_trans (Nat.le_succ n) (hσ_ge n hn)
    filter_upwards [hg_ae] with t ht
    have hcomp := ht.comp hσ_top
    refine hcomp.congr' ?_
    filter_upwards [eventually_ge_atTop k] with n hn
    simp only [Function.comp_apply]
    -- rewrite under `κ`: the tower factorization is applied INSIDE the seed.
    rw [hσ_eq n hn]

/-- **Spike (b), layer 2.** The seeded tower composes with the next sealed wrapper:
`galerkin_weakLimit_R3` is already extraction-generic, so passing it `κ ∘ φ` (strict
monotonicity by `hκ.comp hφ`) yields the `u_lim_aestronglyMeasurable` /
`galerkinSpaceTimeExtraction_R3` conclusion shape with effective index `κ (φ n)` —
demonstrating that the external seed survives the layer that assembles the measurable
limit curve, with NO change to `galerkin_weakLimit_R3` itself. -/
theorem spacetime_extraction_seeded
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
          Filter.atTop (nhds (restrictToBall R (u t : L2VF_R3)))) := by
  obtain ⟨φ, hφ, hk⟩ := diag_ae_subseq_seeded 𝔊 F ν hν T hT u₀ galSeq κ hκ
  obtain ⟨u, hmeas, hconv⟩ :=
    galerkin_weakLimit_R3 𝔊 F ν u₀ (fun n => (galSeq n).toSolutionData)
      (κ ∘ φ) (hκ.comp hφ) T hT hk
  exact ⟨φ, u, hφ, hmeas, hconv⟩

end Scratch212
end LerayHopf

-- Axiom pins (evidence contract, campaign-doc B0 standard): kernel trio only.
#print axioms LerayHopf.Scratch212.diag_ae_subseq_seeded
#print axioms LerayHopf.Scratch212.spacetime_extraction_seeded
