/-
# LerayHopf.R3.ArzelaAscoliTime — Issue #44 (SOUND restructure)

**Goal (issue #44):** Replace the axiom `galerkinSpaceTimeExtraction_R3` with a proof
built from two SOUND thin axioms plus Mathlib-reachable plumbing lemmas.

**Codex P1 soundness fix (2026-06-22):** The original T0.1 axiom
`galerkin_equicontinuity_from_ODE` was UNSOUND: the Galerkin ODE controls the time
derivative only in a dual/V* norm; finite-dimensional norm-equivalence constants are NOT
uniform in `n`; the convection term cannot be bounded in L² dual norm from the H¹ energy
alone. That axiom has been DELETED.

The sound route uses the L²-IN-TIME Bochner norm convergence (Aubin–Lions–Simon), not
pointwise-in-time strong equicontinuity. The Mathlib extraction chain is:
  eLpNorm → 0  (axiom A per ball)
  ⟹ `tendstoInMeasure_of_tendsto_eLpNorm`  (Mathlib)
  ⟹ `TendstoInMeasure.exists_seq_tendsto_ae`  (Mathlib)
  ⟹ per-ball a.e.-in-time subsequence convergence
  ⟹ diagonalize over `R : ℕ`
  ⟹ feed into axiom B to get `u : Time → L2Sigma_R3`

**Architecture (import-cycle safety):**
  R3.SpatialCompactness  ← (LocalRellichInput, L2ballR3, restrictToBall)
  R3.AxiomaticClosure    ← (GalerkinSolutionData_R3)
  R3.ArzelaAscoliTime    [THIS FILE]   ← depends on both above
  R3.AubinLionsLimitPassage            ← imports this file

## Declarations (dependency order)

### Group A — Two sound residual axioms

- `galerkin_spacetime_precompact_R3`  (axiom A)  — Aubin–Lions–Simon L²-in-time precompactness
- `galerkin_weakLimit_R3`             (axiom B)  — Banach–Alaoglu + div-free weak limit

### Local plumbing helpers (proved)

- `norm_restrictToBall_sub_le`        — 1-Lipschitz of ball restriction on differences
- `continuous_restrictToBall'`        — continuity of `restrictToBall R`
- `restrictToBall_sub_norm_mono`      — monotonicity of ball restriction norm in R

### New provable plumbing (sorries for lean-prover)

- `perBall_ae_subseq`    — from axiom A: a.e.-t convergent subseq on a single ball
- `diag_ae_subseq`       — diagonalize `perBall_ae_subseq` over `R : ℕ`

### T4 — Assembly

- `u_lim_aestronglyMeasurable`   — calls diag_ae_subseq + axiom B

## Assumptions (new axioms introduced here)

1. `galerkin_spacetime_precompact_R3` — ALLOW_AXIOM: LOCAL Aubin–Lions–Simon spacetime
   precompactness on ℝ³ — for each ball radius `k : ℕ`, the per-ball Galerkin curve sequence
   has a subsequence converging to zero in the L²(0,T; L²(B_k)) Bochner norm. SOUND/LOCAL: no
   tightness, no strong-norm pointwise equicontinuity, no global-L² claim (strictly weaker than
   a pointwise time-modulus). Mathlib lacks the Bochner-valued Aubin–Lions/Fréchet–Kolmogorov
   theorem in L²(0,T;X); scheme-independent; reusable for torus #23.

2. `galerkin_weakLimit_R3` — ALLOW_AXIOM: per-ball-L²-a.e.-t-convergent bounded Galerkin
   subsequence has a measurable weak limit `u : Time → L2Sigma_R3`; requires Banach–Alaoglu
   (bounded sequence weakly relatively compact in reflexive Hilbert space L2VF_R3) + weak-
   closedness of L2Sigma_R3 (divergence-free kernel of a bounded operator is weakly closed) —
   both standard functional analysis, not formalized in Mathlib; reusable for torus #23.
-/

import LerayHopf.R3.AxiomaticClosure   -- GalerkinSolutionData_R3, R3GalerkinScheme, R3NSForms
import LerayHopf.R3.SpatialCompactness -- LocalRellichInput, L2ballR3, restrictToBall

-- tendstoInMeasure_of_tendsto_eLpNorm, TendstoInMeasure.exists_seq_tendsto_ae
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
-- aestronglyMeasurable_of_tendsto_ae
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
-- IsCompact.isSeqCompact, IsSeqCompact.subseq_of_frequently_in
import Mathlib.Topology.Sequences

namespace LerayHopf

open MeasureTheory Filter Topology Metric

/-! ### Group A — Two sound residual axioms -/

/-- **Axiom A — LOCAL Aubin–Lions–Simon spacetime precompactness on ℝ³.**

For each ball radius `k : ℕ` (natural number, for the diagonalization), there is a
strictly-monotone subsequence `φ_k : ℕ → ℕ` and a measurable limit curve
`g_k : ℝ → L2ballR3 k` such that the Bochner L²-in-time norm of the difference
`restrictToBall k ((galSeq (φ_k n)).u t) - g_k t` converges to `0` as `n → ∞`.

**Mathematical content:** This is the Aubin–Lions–Simon compactness theorem in
`L²(0,T; L²(B_k))`: uniform bounds on `‖u_n(t)‖_{L²}` (energy bound, `galerkin_norm_le_u0`)
and on `∫₀ᵀ ‖∇u_n(t)‖²_{L²} dt` (regularity bound, `reg_bound`) plus the ODE structure
imply L²-in-time precompactness in L²(B_k). The L²-in-time norm topology is the natural
one for this bound — it does NOT require pointwise-in-time control of the derivative.

**Soundness:** This axiom is STRICTLY WEAKER than the deleted `galerkin_equicontinuity_from_ODE`:
it asserts only L²-in-time convergence, NOT pointwise-in-time strong-norm equicontinuity.
The strong-norm time modulus was UNSOUND (n-uniform dual-norm bound on B(u_n,u_n) is not
derivable from L²-energy alone). The present L²-in-time statement is TRUE and derivable from
the Aubin–Lions–Simon theorem (Temam III.2.1; Simon 1987), which Mathlib lacks. -/
axiom galerkin_spacetime_precompact_R3 -- ALLOW_AXIOM: LOCAL Aubin–Lions–Simon spacetime precompactness on ℝ³ — for each ball radius k:ℕ, the per-ball Galerkin curve sequence has a subsequence converging to zero in the L²(0,T;L²(B_k)) Bochner norm (eLpNorm of the difference → 0). SOUND/LOCAL: no tightness, no pointwise-in-time strong equicontinuity, no global-L² claim. Mathlib lacks Bochner-valued Aubin–Lions/Fréchet–Kolmogorov in L²(0,T;X); scheme-independent; reusable for torus #23.
    (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T) (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n)
    (k : ℕ) :
    ∃ (φ_k : ℕ → ℕ) (g_k : ℝ → L2ballR3 k), StrictMono φ_k ∧
      AEStronglyMeasurable g_k (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)) ∧
      Filter.Tendsto
        (fun n => eLpNorm
          (fun t => restrictToBall k ((galSeq (φ_k n)).u t : L2VF_R3) - g_k t)
          2 (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)))
        Filter.atTop (nhds 0)

/-- **Axiom B — Measurable weak limit in `L2Sigma_R3` from per-ball a.e.-t convergence.**

Given a strictly-monotone subsequence `φ` such that for every `k : ℕ` and for a.e. `t ∈ [0,T]`
the ball-k-restricted Galerkin states converge in `L2ballR3 k`, there exists a measurable limit
curve `u : Time → L2Sigma_R3` such that:
- `u` is `AEStronglyMeasurable` on `[0,T]`, and
- for every `R : ℝ`, for a.e. `t ∈ [0,T]`, `restrictToBall R ((galSeq (φ n)).u t) → restrictToBall R (u t)`.

**Mathematical content (same as before, hypothesis now a.e. instead of every-t):**
The per-ball a.e. convergence + uniform L² bound imply weak convergence in L2VF_R3 for a.e. t.
The weak limit inherits div-free (closed subspace = weakly closed). The a.e. hypothesis is
STRICTLY WEAKER than the previous `∀ t ∈ Icc, ∃ g_R` and matches what `diag_ae_subseq` delivers.

**Gap in Mathlib:** Banach–Alaoglu (reflexive Hilbert space, bounded ⇒ weakly compact) and
weak-closedness of `L2Sigma_R3 = ker(div)` (closed subspace ⇒ weakly closed) are standard but
not formalized in Mathlib at the required interface. -/
axiom galerkin_weakLimit_R3 -- ALLOW_AXIOM: per-ball-L²-a.e.-t-convergent bounded Galerkin subsequence has measurable weak limit in L2Sigma_R3; requires Banach–Alaoglu (bounded ball weakly compact in reflexive Hilbert space L2VF_R3) + weak-closedness of L2Sigma_R3 (divergence-free is weakly closed); both standard functional analysis, not formalized in Mathlib; reusable for torus #23
    (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊) (ν : ℝ) (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n) (φ : ℕ → ℕ)
    (hφ : StrictMono φ)
    (T : ℝ) (hT : 0 < T)
    -- Hypothesis: for each integer radius k, there EXISTS a measurable per-ball limit g_k such
    -- that the Galerkin subsequence converges to g_k a.e. in t.
    -- This is WEAKER than the prior every-t version: matches what diag_ae_subseq delivers.
    (hball : ∀ k : ℕ, ∃ g_k : ℝ → L2ballR3 k,
      AEStronglyMeasurable g_k (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)) ∧
      ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)),
        Filter.Tendsto (fun n => restrictToBall k ((galSeq (φ n)).u t : L2VF_R3))
          Filter.atTop (nhds (g_k t))) :
    ∃ u : Time → L2Sigma_R3,
      AEStronglyMeasurable (fun t => (u t : L2VF_R3))
        (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)) ∧
      ∀ R : ℝ, ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)),
        Filter.Tendsto (fun n => restrictToBall R ((galSeq (φ n)).u t : L2VF_R3))
          Filter.atTop (nhds (restrictToBall R (u t : L2VF_R3)))

/-! ### Local plumbing helpers -/

/-- `restrictToBall R` is 1-Lipschitz on differences: the ball-restricted difference has L²-norm
bounded by the global difference. -/
private theorem norm_restrictToBall_sub_le (R : ℝ) (u v : L2VF_R3) :
    ‖restrictToBall R u - restrictToBall R v‖ ≤ ‖u - v‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  have hle : volume.restrict (Metric.closedBall (0 : Domain3) R) ≤ (volume : Measure Domain3) :=
    Measure.restrict_le_self
  have hcongR : ⇑(restrictToBall R u - restrictToBall R v)
      =ᵐ[volume.restrict (Metric.closedBall (0 : Domain3) R)]
        (fun x => (u x : EuclideanSpace ℝ (Fin 3)) - (v x : EuclideanSpace ℝ (Fin 3))) := by
    have hsub := Lp.coeFn_sub (restrictToBall R u) (restrictToBall R v)
    have hu : ⇑(restrictToBall R u)
        =ᵐ[volume.restrict (Metric.closedBall (0 : Domain3) R)]
          (u : Domain3 → EuclideanSpace ℝ (Fin 3)) := MemLp.coeFn_toLp _
    have hv : ⇑(restrictToBall R v)
        =ᵐ[volume.restrict (Metric.closedBall (0 : Domain3) R)]
          (v : Domain3 → EuclideanSpace ℝ (Fin 3)) := MemLp.coeFn_toLp _
    filter_upwards [hsub, hu, hv] with x hx hxu hxv
    simp only [hx, Pi.sub_apply, hxu, hxv]
  have hcongG : ⇑(u - v)
      =ᵐ[(volume : Measure Domain3)]
        (fun x => (u x : EuclideanSpace ℝ (Fin 3)) - (v x : EuclideanSpace ℝ (Fin 3))) :=
    Lp.coeFn_sub u v
  rw [eLpNorm_congr_ae hcongR, eLpNorm_congr_ae hcongG]
  refine ENNReal.toReal_mono ?_ (eLpNorm_mono_measure _ hle)
  rw [← eLpNorm_congr_ae hcongG]
  exact (Lp.memLp (u - v)).2.ne

/-- `restrictToBall R : L2VF_R3 → L2ballR3 R` is continuous (it is 1-Lipschitz). -/
private theorem continuous_restrictToBall' (R : ℝ) :
    Continuous (fun w : L2VF_R3 => restrictToBall R w) := by
  refine Metric.continuous_iff.2 fun w ε hε => ⟨ε, hε, fun w' hw' => ?_⟩
  calc dist (restrictToBall R w') (restrictToBall R w)
      = ‖restrictToBall R w' - restrictToBall R w‖ := dist_eq_norm _ _
    _ ≤ ‖w' - w‖ := norm_restrictToBall_sub_le R w' w
    _ = dist w' w := (dist_eq_norm _ _).symm
    _ < ε := hw'

/-- Ball restriction norm is monotone in the radius: `‖·‖_{L²(B_R)} ≤ ‖·‖_{L²(B_k)}` when
`R ≤ k`, because `B_R ⊆ B_k`. -/
private theorem restrictToBall_sub_norm_mono (R k : ℝ) (hRk : R ≤ k) (w w' : L2VF_R3) :
    ‖restrictToBall R w - restrictToBall R w'‖ ≤ ‖restrictToBall k w - restrictToBall k w'‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  have hsub : Metric.closedBall (0 : Domain3) R ⊆ Metric.closedBall (0 : Domain3) k :=
    Metric.closedBall_subset_closedBall hRk
  have hle : volume.restrict (Metric.closedBall (0 : Domain3) R)
      ≤ volume.restrict (Metric.closedBall (0 : Domain3) k) :=
    Measure.restrict_mono hsub le_rfl
  have hcongR : ⇑(restrictToBall R w - restrictToBall R w')
      =ᵐ[volume.restrict (Metric.closedBall (0 : Domain3) R)]
        (fun x => (w x : EuclideanSpace ℝ (Fin 3)) - (w' x : EuclideanSpace ℝ (Fin 3))) := by
    have hsub2 := Lp.coeFn_sub (restrictToBall R w) (restrictToBall R w')
    have hu : ⇑(restrictToBall R w)
        =ᵐ[volume.restrict (Metric.closedBall (0 : Domain3) R)]
          (w : Domain3 → EuclideanSpace ℝ (Fin 3)) := MemLp.coeFn_toLp _
    have hv : ⇑(restrictToBall R w')
        =ᵐ[volume.restrict (Metric.closedBall (0 : Domain3) R)]
          (w' : Domain3 → EuclideanSpace ℝ (Fin 3)) := MemLp.coeFn_toLp _
    filter_upwards [hsub2, hu, hv] with x hx hxu hxv
    simp only [hx, Pi.sub_apply, hxu, hxv]
  have hcongK : ⇑(restrictToBall k w - restrictToBall k w')
      =ᵐ[volume.restrict (Metric.closedBall (0 : Domain3) k)]
        (fun x => (w x : EuclideanSpace ℝ (Fin 3)) - (w' x : EuclideanSpace ℝ (Fin 3))) := by
    have hsub2 := Lp.coeFn_sub (restrictToBall k w) (restrictToBall k w')
    have hu : ⇑(restrictToBall k w)
        =ᵐ[volume.restrict (Metric.closedBall (0 : Domain3) k)]
          (w : Domain3 → EuclideanSpace ℝ (Fin 3)) := MemLp.coeFn_toLp _
    have hv : ⇑(restrictToBall k w')
        =ᵐ[volume.restrict (Metric.closedBall (0 : Domain3) k)]
          (w' : Domain3 → EuclideanSpace ℝ (Fin 3)) := MemLp.coeFn_toLp _
    filter_upwards [hsub2, hu, hv] with x hx hxu hxv
    simp only [hx, Pi.sub_apply, hxu, hxv]
  rw [eLpNorm_congr_ae hcongR, eLpNorm_congr_ae hcongK]
  refine ENNReal.toReal_mono ?_ (eLpNorm_mono_measure _ hle)
  rw [← eLpNorm_congr_ae hcongK]
  exact (Lp.memLp (restrictToBall k w - restrictToBall k w')).2.ne

/-! ### Per-ball a.e. subsequence extraction -/

/-- **`perBall_ae_subseq` — From L²-in-time Bochner convergence, extract a further
subsequence converging a.e. in `t` in the `L2ballR3 k` norm.**

**Proof route (for lean-prover):**
1. Axiom A gives `φ_k` and `g_k` with `eLpNorm (fun t => f_n t - g_k t) 2 μ → 0`.
2. Each function `fun t => restrictToBall k ((galSeq (φ_k n)).u t) - g_k t` is
   `AEStronglyMeasurable` on `[0,T]` (difference of AESM functions, since the Galerkin curve is
   continuous hence measurable, and `g_k` is AESM from the axiom's conclusion).
3. Apply `MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm` (Mathlib: `ConvergenceInMeasure`,
   with `p = 2 ≠ 0`, `hp_ne_top = by norm_num`, `hf = AEStronglyMeasurable_of_each_n`,
   `hg = hg_k_aesm`) to get `TendstoInMeasure μ (fun n t => ...) atTop (g_k)`.
4. Apply `TendstoInMeasure.exists_seq_tendsto_ae` to get a further strictly-monotone
   `ρ_k : ℕ → ℕ` and a.e.-t convergence of the composed subsequence. -/
theorem perBall_ae_subseq
    (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T) (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n)
    (k : ℕ) :
    ∃ (φ : ℕ → ℕ) (g_k : ℝ → L2ballR3 k),
      StrictMono φ ∧
      AEStronglyMeasurable g_k (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)) ∧
      ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)),
        Filter.Tendsto
          (fun n => restrictToBall k ((galSeq (φ n)).u t : L2VF_R3))
          Filter.atTop (nhds (g_k t)) := by
  -- Step 1: Axiom A gives L²-in-time Bochner convergence for some subsequence φ₀.
  obtain ⟨φ₀, g_k, hφ₀, hg_aesm, heLp⟩ :=
    galerkin_spacetime_precompact_R3 𝔊 F ν hν T hT u₀ galSeq k
  -- Step 2: each ball-restricted Galerkin curve is a.e.-strongly-measurable on `[0,T]`
  -- (the curve is continuous on `Ici 0` via `u_hasDeriv`, restrictToBall is continuous).
  have hf_aesm : ∀ n, AEStronglyMeasurable
      (fun t => restrictToBall (k : ℝ) ((galSeq (φ₀ n)).u t : L2VF_R3))
      (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)) := by
    intro n
    have hcurve : ContinuousOn (fun t => ((galSeq (φ₀ n)).u t : L2VF_R3)) (Set.Ici 0) :=
      fun t ht => (((galSeq (φ₀ n)).u_hasDeriv t ht).continuousAt.continuousWithinAt)
    have hcurve_aesm : AEStronglyMeasurable (fun t => ((galSeq (φ₀ n)).u t : L2VF_R3))
        (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)) :=
      (hcurve.mono Set.Icc_subset_Ici_self).aestronglyMeasurable measurableSet_Icc
    exact (continuous_restrictToBall' (k : ℝ)).comp_aestronglyMeasurable hcurve_aesm
  -- Step 3: L²-in-time convergence ⇒ convergence in measure.
  have hTIM : TendstoInMeasure (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T))
      (fun n t => restrictToBall (k : ℝ) ((galSeq (φ₀ n)).u t : L2VF_R3)) atTop g_k :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) hf_aesm hg_aesm heLp
  -- Step 4: a.e.-t convergent further subsequence `ρ`; final subsequence is `φ₀ ∘ ρ`.
  obtain ⟨ρ, hρ, hae⟩ := hTIM.exists_seq_tendsto_ae
  refine ⟨φ₀ ∘ ρ, g_k, hφ₀.comp hρ, hg_aesm, ?_⟩
  filter_upwards [hae] with t ht
  exact ht

/-- **`diag_ae_subseq` — Diagonal subsequence converging a.e. in `t` for ALL ball radii `k : ℕ`.**

From `perBall_ae_subseq` applied at each radius `k`, construct a single strictly-monotone
subsequence `φ : ℕ → ℕ` such that for every `k : ℕ` and a.e. `t ∈ [0,T]`,
`restrictToBall k ((galSeq (φ n)).u t) → g_k t` in `L2ballR3 k`.

**Proof route (for lean-prover):**
The standard Cantor diagonal argument:
1. By induction, build a tower `φ_0, φ_1, φ_2, …` with:
   - `φ_0` from `perBall_ae_subseq` at `k = 0`,
   - `φ_{k+1}` from `perBall_ae_subseq` applied to the reindexed Galerkin sequence
     `n ↦ galSeq (φ_k n)` at radius `k+1` (giving a further subsequence `ρ_{k+1}` with
     `φ_{k+1} = φ_k ∘ ρ_{k+1}`).
2. The diagonal `φ n := φ_n n` (where `φ_n` is the `n`-th level of the tower) is strictly
   monotone (standard argument: each level is strictly monotone and refines the previous).
3. For each fixed `k`, for all `n ≥ k`, `φ n = φ_k (something ≥ n)`, so the diagonal is
   eventually a subsequence of `φ_k`. Therefore for a.e. `t`, convergence of `φ_k` carries
   over to convergence of the diagonal subsequence at the same a.e. full-measure set for level `k`.
4. The full-measure set for the diagonal is `⋂_{k : ℕ} S_k` where each `S_k` has full measure;
   a countable intersection of full-measure sets in a finite measure space has full measure. -/
theorem diag_ae_subseq
    (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T) (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n) :
    ∃ (φ : ℕ → ℕ),
      StrictMono φ ∧
      ∀ k : ℕ, ∃ g_k : ℝ → L2ballR3 k,
        AEStronglyMeasurable g_k (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)) ∧
        ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)),
          Filter.Tendsto
            (fun n => restrictToBall k ((galSeq (φ n)).u t : L2VF_R3))
            Filter.atTop (nhds (g_k t)) := by
  sorry -- ALLOW_SORRY: #44 diag_ae_subseq — proof route: Cantor diagonal on perBall_ae_subseq; build tower inductively (φ_0 from k=0, φ_{k+1} = φ_k ∘ ρ_{k+1} where ρ_{k+1} is the subseq given by perBall_ae_subseq applied to galSeq ∘ φ_k at k+1); diagonal φ n = φ_n n is StrictMono by the standard argument (each φ_k is StrictMono and the tower is nested); for each fixed k, the diagonal is eventually a subsequence of φ_k (for n ≥ k), so the a.e.-t convergence for φ_k transfers to the diagonal (subsequence of a convergent sequence converges to the same limit); the a.e. set for the diagonal is countable intersection of full-measure sets, which has full measure (finite measure space; use MeasureTheory.ae_all_iff.mpr + Filter.Eventually.mono).

/-! ### T4 — Assembly: measurable limit curve -/

/-- **`u_lim_aestronglyMeasurable` — The assembled limit curve `u : Time → L2Sigma_R3` exists,
is AE strongly measurable, and the diagonal Galerkin subsequence converges per-ball a.e.-t.**

Combines:
- `diag_ae_subseq` (new): diagonal subsequence + per-ball a.e.-t convergence for all `k : ℕ`,
- monotone ball-norm extension from ℕ to ℝ (via `restrictToBall_sub_norm_mono`),
- axiom B (`galerkin_weakLimit_R3`): assembles the measurable limit `u : Time → L2Sigma_R3`.

The output has the SAME type as `galerkinSpaceTimeExtraction_R3` requires. -/
theorem u_lim_aestronglyMeasurable
    (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T) (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n)
    (B : LocalRellichInput) :
    ∃ (φ : ℕ → ℕ) (u : Time → L2Sigma_R3),
      StrictMono φ ∧
      AEStronglyMeasurable (fun t => (u t : L2VF_R3))
        (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)) ∧
      ∀ R : ℝ, ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)),
        Filter.Tendsto (fun n => restrictToBall R ((galSeq (φ n)).u t : L2VF_R3))
          Filter.atTop (nhds (restrictToBall R (u t : L2VF_R3))) := by
  -- Step 1: diagonal subsequence φ with per-ball (ℕ-radius) a.e.-t convergence.
  obtain ⟨φ, hφ, hk⟩ := diag_ae_subseq 𝔊 F ν hν T hT u₀ galSeq
  -- Step 2: Package the ℕ-radius a.e.-t convergence into the form axiom B needs.
  -- `hk k` gives `∃ g_k, AEStronglyMeasurable g_k ∧ ∀ᵐ t, Tendsto (...) (nhds (g_k t))`.
  -- Axiom B's `hball` wants exactly this shape: `∀ k : ℕ, ∃ g_k, AESM ∧ ∀ᵐ t, Tendsto`.
  have hball : ∀ k : ℕ, ∃ g_k : ℝ → L2ballR3 k,
      AEStronglyMeasurable g_k (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)) ∧
      ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)),
        Filter.Tendsto (fun n => restrictToBall k ((galSeq (φ n)).u t : L2VF_R3))
          Filter.atTop (nhds (g_k t)) :=
    hk
  -- Step 3: Apply axiom B.
  obtain ⟨u, hmeas, hconv⟩ := galerkin_weakLimit_R3 𝔊 F ν u₀ galSeq φ hφ T hT hball
  exact ⟨φ, u, hφ, hmeas, hconv⟩

end LerayHopf
