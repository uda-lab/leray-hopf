/-
# LerayHopf.R3.ArzelaAscoliTime — Issue #44 (SOUND restructure) + #47 PR-A cleanup

**Goal (issue #44):** Replace the axiom `galerkinSpaceTimeExtraction_R3` with a proof
built from two SOUND thin axioms plus Mathlib-reachable plumbing lemmas.

**Issue #47 PR-A (cleanup):** `galerkin_weakLimit_R3` was converted from axiom → THEOREM via a
strong ball-exhaustion + Mazur route (Cauchy diagonal + `exists_stronglyMeasurable_limit_of_tendsto_ae`).
It does NOT use `L2VF_R3_weakSeqCompact_closedBall` (the thin Banach–Alaoglu axiom introduced as a
scaffold in PR-A round 1). That axiom has been DELETED as unused dead code; `weakLimit_aestronglyMeasurable`
(WL-6, an orphan sorry with no capstone-path consumer) has also been deleted.

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
  ⟹ Cauchy diagonal + `exists_stronglyMeasurable_limit_of_tendsto_ae` for STRONG limit
  ⟹ Mazur (WL-5) to confirm limit is in L2Sigma_R3

**Architecture (import-cycle safety):**
  R3.SpatialCompactness  ← (LocalRellichInput, L2ballR3, restrictToBall)
  R3.SolutionInterfaces    ← (GalerkinSolutionData_R3)
  R3.ArzelaAscoliTime    [THIS FILE]   ← depends on both above
  R3.AubinLionsLimitPassage            ← imports this file

## Declarations (dependency order)

### Group A — Local Aubin–Lions–Simon precompactness (THEOREM)

- `galerkin_spacetime_precompact_R3`  — Aubin–Lions–Simon L²-in-time precompactness; converted
    from `axiom` to `theorem` (issue #46 PR-4), discharged by File E
    (`galerkin_spacetime_precompact_of_goodSampling`).

### Local plumbing helpers (proved)

- `norm_restrictToBall_sub_le`        — 1-Lipschitz of ball restriction on differences
- `continuous_restrictToBall'`        — continuity of `restrictToBall R`
- `restrictToBall_sub_norm_mono`      — monotonicity of ball restriction norm in R

### Proved lemmas (no sorry)

- `weakLimit_mem_L2Sigma_R3` (WL-5)  — Mazur: weak limits of L2Sigma_R3 sequences stay in L2Sigma_R3
- `galerkin_weakLimit_R3`             — THEOREM (converted from axiom): per-ball a.e.-t limits
                                        ⇒ measurable weak limit in L2Sigma_R3; proved via Cauchy diagonal
                                        + `exists_stronglyMeasurable_limit_of_tendsto_ae` + WL-5.

### Sorried lemmas (for lean-prover)

- `perBall_ae_subseq`    — from axiom A: a.e.-t convergent subseq on a single ball
- `diag_ae_subseq`       — diagonalize `perBall_ae_subseq` over `R : ℕ`

### T4 — Assembly

- `u_lim_aestronglyMeasurable`   — calls diag_ae_subseq + galerkin_weakLimit_R3

## Assumptions (axioms introduced here — issue #46 PR-4 after discharge)

This file now introduces **ZERO axioms**.

The former residual axiom `galerkin_spacetime_precompact_R3` (REFINE-CAPABLE LOCAL Aubin–Lions–
Simon spacetime precompactness on ℝ³) was DISCHARGED on 2026-07-04 (issue #46 PR-4): it is now a
`theorem` proved by delegation to `galerkin_spacetime_precompact_of_goodSampling` (File E,
`LerayHopf/R3/SpacetimePrecompact.lean`), which assembles it sorry-free from the step-curve
total-boundedness engine (the `n`-uniform integrated sampling modulus + Rellich ball-compactness).

Net R3 project axioms from this file: 0.
The remaining R3 project axiom is `galerkin_limit_passage_R3` (from `SolutionInterfaces`).
-/

import LerayHopf.R3.SolutionInterfaces   -- GalerkinSolutionData_R3, R3GalerkinScheme, R3NSForms
import LerayHopf.R3.SpatialCompactness -- LocalRellichInput, L2ballR3, restrictToBall
import LerayHopf.R3.DivergenceFree     -- L2VF_R3_separable, L2Sigma_R3_weaklyClosed (WL-1, WL-4)
-- E2 galerkin_spacetime_precompact_of_goodSampling — discharges galerkin_spacetime_precompact_R3
-- (issue #46 PR-4). SpacetimePrecompact sits STRICTLY UPSTREAM: it does NOT import this file,
-- so there is no import cycle (gate-checked: no transitive edge back to ArzelaAscoliTime).
import LerayHopf.R3.SpacetimePrecompact

-- tendstoInMeasure_of_tendsto_eLpNorm, TendstoInMeasure.exists_seq_tendsto_ae
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
-- aestronglyMeasurable_of_tendsto_ae
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
-- toWeakSpace, WeakSpace (for WL-5 weakLimit_mem_L2Sigma_R3 + the weak-convergence step in galerkin_weakLimit_R3)
import Mathlib.Analysis.LocallyConvex.WeakSpace
-- InnerProductSpace.toDual_symm_apply (Riesz representation, for WL-5 weak-convergence proof in galerkin_weakLimit_R3)
import Mathlib.Analysis.InnerProductSpace.Dual
-- aecover_closedBall, AECover.integral_tendsto_of_countably_generated (for ball exhaustion MCT)
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

namespace LerayHopf

open MeasureTheory Filter Topology Metric

/-! ### Group A — Local Aubin–Lions–Simon precompactness and abstract FA primitives -/

/-- **`galerkin_spacetime_precompact_R3` — LOCAL Aubin–Lions–Simon spacetime precompactness on
ℝ³ (REFINE-CAPABLE).**  [issue #46 PR-4: converted from `axiom` to `theorem`, discharged by
`galerkin_spacetime_precompact_of_goodSampling` (File E, `SpacetimePrecompact.lean`).]

For every input subsequence `ψ : ℕ → ℕ` (strictly monotone) and every ball radius `k : ℕ`,
there is a FURTHER strictly-monotone `ρ : ℕ → ℕ` and a measurable limit curve
`g_k : ℝ → L2ballR3 k` such that the Bochner L²-in-time norm of the difference
`restrictToBall k ((galSeq (ψ (ρ n))).u t) - g_k t` converges to `0` as `n → ∞`.

**Why refine-capable?** The Cantor-diagonal construction in `diag_ae_subseq` builds the tower
`φ_0 = ρ_0`, `φ_{k+1} = φ_k ∘ ρ_{k+1}` inductively, where at each step we extract a FURTHER
subsequence of the CURRENT one. This requires applying the compactness result to the composition
`galSeq ∘ φ_k` — but `galSeq n : GalerkinSolutionData_R3 … n` has the level `n` baked into
its dependent type, making reindexing `n ↦ galSeq (φ_k n)` type-incorrect as a new `galSeq`.
The refine-capable form avoids reindexing by keeping `galSeq` fixed and instead taking the
current subsequence `ψ = φ_k` as input, returning a further `ρ` such that `φ_k ∘ ρ` is the
next level.

**Soundness:** Any subsequence of a sequence satisfying the hypotheses of the Aubin–Lions–Simon
theorem also satisfies the same hypotheses (the energy bound `galerkin_norm_le_u0` and
`reg_bound` are uniform in `n`, so they hold uniformly along any `ψ`). Hence the conclusion
holds for every input `ψ`.

**Mathematical content:** Aubin–Lions–Simon compactness theorem in `L²(0,T; L²(B_k))`.
SOUND/LOCAL: no tightness, no pointwise-in-time equicontinuity, no global-L² claim.
Mathlib lacks the Bochner-valued Aubin–Lions/Fréchet–Kolmogorov theorem in L²(0,T;X); the
concrete route (step-curve total-boundedness via the `n`-uniform integrated sampling modulus +
Rellich ball-compactness) is assembled sorry-free in `SpacetimePrecompact.lean`.

**Proof:** delegated to `galerkin_spacetime_precompact_of_goodSampling` (E2), which has the
BYTE-IDENTICAL statement. -/
theorem galerkin_spacetime_precompact_R3
    (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T) (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n)
    (ψ : ℕ → ℕ) (hψ : StrictMono ψ) (k : ℕ) :
    ∃ (ρ : ℕ → ℕ) (g_k : ℝ → L2ballR3 k), StrictMono ρ ∧
      AEStronglyMeasurable g_k (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)) ∧
      Filter.Tendsto
        (fun n => eLpNorm
          (fun t => restrictToBall k ((galSeq (ψ (ρ n))).u t : L2VF_R3) - g_k t)
          2 (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)))
        Filter.atTop (nhds 0) :=
  galerkin_spacetime_precompact_of_goodSampling 𝔊 F ν hν T hT u₀ galSeq ψ hψ k

/-- **WL-5 — Weak limits of sequences in `L2Sigma_R3` remain in `L2Sigma_R3`.**

If `vₙ : L2VF_R3` with `vₙ ∈ L2Sigma_R3` for all `n`, and `vₙ` converges weakly to `v : L2VF_R3`
in `WeakSpace ℝ L2VF_R3`, then `v ∈ L2Sigma_R3`.

**Proof route:** From `L2Sigma_R3_weaklyClosed` (WL-4, proved in `DivergenceFree.lean` via Mazur)
and the sequential characterization of closed sets (limit of a sequence in a closed set lies
in the closed set). Since `IsClosed ((toWeakSpace ℝ L2VF_R3) '' L2Sigma_R3)` and the sequence
of images converges to `(toWeakSpace ℝ L2VF_R3) v`, the limit lies in the image, hence
`v ∈ L2Sigma_R3`. -/
theorem weakLimit_mem_L2Sigma_R3
    (v : L2VF_R3) (vn : ℕ → L2VF_R3)
    (hmem : ∀ n, vn n ∈ L2Sigma_R3)
    (htend : Filter.Tendsto (fun n => (toWeakSpace ℝ L2VF_R3) (vn n))
        Filter.atTop (𝓝 ((toWeakSpace ℝ L2VF_R3) v))) :
    v ∈ L2Sigma_R3 := by
  -- WL-4: the weak image of L2Sigma_R3 is closed in `WeakSpace ℝ L2VF_R3`.
  have hclose : IsClosed ((toWeakSpace ℝ L2VF_R3) '' (L2Sigma_R3 : Set L2VF_R3)) :=
    L2Sigma_R3_weaklyClosed
  -- The sequence `toWeakSpace ℝ L2VF_R3 (vn n)` lies in the closed set.
  have hmem' : ∀ n, (toWeakSpace ℝ L2VF_R3) (vn n) ∈
      (toWeakSpace ℝ L2VF_R3) '' (L2Sigma_R3 : Set L2VF_R3) :=
    fun n => Set.mem_image_of_mem _ (hmem n)
  -- By `IsClosed.mem_of_tendsto`, the limit lies in the closed set.
  have hlimit_mem : (toWeakSpace ℝ L2VF_R3) v ∈
      (toWeakSpace ℝ L2VF_R3) '' (L2Sigma_R3 : Set L2VF_R3) :=
    hclose.mem_of_tendsto htend (Filter.Eventually.of_forall hmem')
  -- Extract the preimage: there exists `w ∈ L2Sigma_R3` with `toWeakSpace ℝ L2VF_R3 w = toWeakSpace ℝ L2VF_R3 v`.
  obtain ⟨w, hwmem, hwv⟩ := hlimit_mem
  -- `toWeakSpace` is injective, so `w = v`, hence `v ∈ L2Sigma_R3`.
  have heq : w = v := (toWeakSpace ℝ L2VF_R3).injective hwv
  rwa [← heq]

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

set_option maxHeartbeats 1000000 in
/-- **`galerkin_weakLimit_R3` — Measurable weak limit in `L2Sigma_R3` from per-ball a.e.-t
convergence.**  [#47: converted from `axiom` to `theorem`]

Given a strictly-monotone subsequence `φ` such that for every `k : ℕ` and for a.e. `t ∈ [0,T]`
the ball-k-restricted Galerkin states converge in `L2ballR3 k`, there exists a measurable limit
curve `u : Time → L2Sigma_R3` such that:
- `u` is `AEStronglyMeasurable` on `[0,T]`, and
- for every `R : ℝ`, for a.e. `t ∈ [0,T]`, `restrictToBall R ((galSeq (φ n)).u t) → restrictToBall R (u t)`.

**Proof (#47 PR-A — sorry-free):** Uses a STRONG ball-exhaustion + Mazur route:
Cauchy diagonal over the liftG-extended per-ball limits (sections A–K), computes
the strong limit via `exists_stronglyMeasurable_limit_of_tendsto_ae` (section L),
confirms membership in `L2Sigma_R3` via `weakLimit_mem_L2Sigma_R3` (WL-5, Mazur),
and establishes per-R a.e.-t convergence by norm monotonicity (sections M–O).
This route does NOT use `L2VF_R3_weakSeqCompact_closedBall` (that axiom is DELETED).

**SAME signature as the former axiom:** all downstream consumers (`u_lim_aestronglyMeasurable`,
`AubinLionsLimitPassage`, the capstone) continue to see this by the SAME name and type. -/
theorem galerkin_weakLimit_R3
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
          Filter.atTop (nhds (restrictToBall R (u t : L2VF_R3))) := by
  -- ======== PROOF OF galerkin_weakLimit_R3 ========
  set μ := MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T) with hμ_def
  -- (0) Extract per-ball limit functions g_k : ℝ → L2ballR3 k
  choose gk hgk_aesm hgk_conv using hball
  -- (A) Define extension-by-zero: liftG k : L2ballR3 k → L2VF_R3
  let Bk : ℕ → Set Domain3 := fun k => Metric.closedBall 0 (↑k : ℝ)
  have hBkms : ∀ k, MeasurableSet (Bk k) := fun _ => measurableSet_closedBall
  let liftG : ∀ k : ℕ, L2ballR3 k → L2VF_R3 := fun k f =>
    MemLp.toLp ((Bk k).indicator (f : Domain3 → EuclideanSpace ℝ (Fin 3)))
      ((memLp_indicator_iff_restrict (hBkms k)).mpr (Lp.memLp f))
  -- coeFn of liftG ae-equals the indicator
  have hlG_coe : ∀ (k : ℕ) (f : L2ballR3 (↑k : ℝ)),
      ⇑(liftG k f) =ᵐ[volume] (Bk k).indicator ↑f :=
    fun k f => MemLp.coeFn_toLp _
  -- liftG is an isometry: ‖liftG k f‖ = ‖f‖
  have hlG_norm : ∀ (k : ℕ) (f : L2ballR3 (↑k : ℝ)), ‖liftG k f‖ = ‖f‖ := by
    intro k f
    rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (hlG_coe k f),
        eLpNorm_indicator_eq_eLpNorm_restrict (hBkms k)]
  -- liftG k preserves differences: ‖liftG k f' - liftG k f‖ = ‖f' - f‖
  have hlG_norm_diff : ∀ (k : ℕ) (f f' : L2ballR3 (↑k : ℝ)), ‖liftG k f' - liftG k f‖ = ‖f' - f‖ := by
    intro k f f'
    have hlin : liftG k f' - liftG k f = liftG k (f' - f) := by
      apply Lp.ext
      -- ae equality (under volume, the base measure for L2VF_R3) of the coercions
      have hsub_ball : ∀ᵐ a ∂volume, a ∈ Bk k →
          ⇑(f' - f) a = (f' : Domain3 → EuclideanSpace ℝ (Fin 3)) a
              - (f : Domain3 → EuclideanSpace ℝ (Fin 3)) a := by
        rw [← ae_restrict_iff' (hBkms k)]
        filter_upwards [Lp.coeFn_sub f' f] with a ha
        simpa only [Pi.sub_apply] using ha
      filter_upwards [hlG_coe k (f' - f), hlG_coe k f', hlG_coe k f,
          Lp.coeFn_sub (liftG k f') (liftG k f), hsub_ball] with a h1 h2 h3 h4 h6
      -- h4: ⇑(liftG k f' - liftG k f) a = ⇑(liftG k f') a - ⇑(liftG k f) a
      rw [h4, Pi.sub_apply, h2, h3, h1]
      -- Both sides: indicator Bk_k (f' a) - indicator Bk_k (f a) vs indicator Bk_k ((f' - f) a)
      by_cases h : a ∈ Bk k
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, Set.indicator_of_mem h, h6 h]
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h,
            Set.indicator_of_notMem h, sub_zero]
    rw [hlin, hlG_norm]
  -- liftG k is continuous (1-Lipschitz from the norm identity)
  have hlG_cont : ∀ k, Continuous (liftG k) := by
    intro k
    refine Metric.continuous_iff.2 fun f ε hε => ⟨ε, hε, fun f' hff' => ?_⟩
    simp only [dist_eq_norm] at hff' ⊢
    rw [hlG_norm_diff]
    exact hff'
  -- (B) Inner product adjoint: ⟪liftG k f, w⟫_ℝ = ⟪f, restrictToBall k w⟫_ℝ
  have hinner_adj : ∀ (k : ℕ) (f : L2ballR3 (↑k : ℝ)) (w : L2VF_R3),
      @inner ℝ L2VF_R3 _ (liftG k f) w =
        @inner ℝ (L2ballR3 k) _ f (restrictToBall (↑k : ℝ) w) := by
    intro k f w
    simp only [MeasureTheory.L2.inner_def]
    -- LHS = ∫ a, ⟪indicator Bk_k ↑f a, w a⟫ ∂vol (using hlG_coe)
    have hlhs : (fun a => @inner ℝ (EuclideanSpace ℝ (Fin 3)) _ ((liftG k f : Domain3 → _) a)
        ((w : Domain3 → _) a)) =ᵐ[volume]
        (fun a => (Bk k).indicator (fun a => @inner ℝ (EuclideanSpace ℝ (Fin 3)) _ ((f : Domain3 → _) a)
          ((w : Domain3 → _) a)) a) := by
      filter_upwards [hlG_coe k f] with a ha
      rw [ha]
      by_cases h : a ∈ Bk k
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, inner_zero_left]
    rw [integral_congr_ae hlhs, integral_indicator (hBkms k)]
    -- RHS: ∫ a in Bk k, ⟪↑f a, ↑w a⟫ → ∫ a in Bk k, ⟪↑f a, ↑(restrictToBall k w) a⟫
    apply setIntegral_congr_ae (hBkms k)
    rw [← ae_restrict_iff' (hBkms k)]
    filter_upwards [MemLp.coeFn_toLp ((Lp.memLp w).restrict (Bk k))] with a ha
    have ha' : (restrictToBall (↑k : ℝ) w : Domain3 → EuclideanSpace ℝ (Fin 3)) a
        = (w : Domain3 → EuclideanSpace ℝ (Fin 3)) a := ha
    rw [ha']
  -- (C) Pythagorean identity: ‖h - liftG k (restrictToBall k h)‖^2 = ‖h‖^2 - ‖restrictToBall k h‖^2
  have hpyth : ∀ (h : L2VF_R3) (k : ℕ),
      ‖h - liftG k (restrictToBall (↑k : ℝ) h)‖^2 = ‖h‖^2 - ‖restrictToBall (↑k : ℝ) h‖^2 := by
    intro h k
    rw [norm_sub_sq_real, hlG_norm, real_inner_comm, hinner_adj, real_inner_self_eq_norm_sq]
    ring
  -- (D) ‖restrictToBall k h‖^2 tends to ‖h‖^2 (ball exhaustion via MCT)
  have hnorm_sq_tend : ∀ (h : L2VF_R3),
      Tendsto (fun k : ℕ => ‖restrictToBall (↑k : ℝ) h‖^2) atTop (nhds (‖h‖^2)) := by
    intro h
    -- Connect ‖·‖^2 to ∫ ‖·‖^2 via inner product
    have norm_sq_as_int : ∀ (μ' : Measure Domain3) (f : Lp (EuclideanSpace ℝ (Fin 3)) 2 μ'),
        ‖f‖^2 = ∫ a, ‖(f : Domain3 → EuclideanSpace ℝ (Fin 3)) a‖^2 ∂μ' := by
      intro μ' f
      rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
      exact integral_congr_ae (Filter.Eventually.of_forall fun a => real_inner_self_eq_norm_sq _)
    rw [norm_sq_as_int volume h]
    have hpt : ∀ k : ℕ, ‖restrictToBall (↑k : ℝ) h‖^2
        = ∫ a, ‖(restrictToBall (↑k : ℝ) h : Domain3 → EuclideanSpace ℝ (Fin 3)) a‖^2
            ∂(volume.restrict (Bk k)) :=
      fun k => norm_sq_as_int (volume.restrict (Bk k)) (restrictToBall (↑k : ℝ) h)
    simp_rw [hpt]
    -- ∫ ‖(restrictToBall k h) a‖^2 ∂(vol.restrict Bk k) = ∫ a in Bk k, ‖h a‖^2 ∂vol
    have hcong : ∀ k : ℕ,
        ∫ a, ‖(restrictToBall (↑k : ℝ) h : Domain3 → EuclideanSpace ℝ (Fin 3)) a‖^2
            ∂(volume.restrict (Bk k)) =
          ∫ a in Bk k, ‖(h : Domain3 → EuclideanSpace ℝ (Fin 3)) a‖^2 ∂volume := by
      intro k
      apply setIntegral_congr_ae (hBkms k)
      rw [← ae_restrict_iff' (hBkms k)]
      filter_upwards [MemLp.coeFn_toLp ((Lp.memLp h).restrict (Bk k))] with a ha
      have ha' : (restrictToBall (↑k : ℝ) h : Domain3 → EuclideanSpace ℝ (Fin 3)) a
          = (h : Domain3 → EuclideanSpace ℝ (Fin 3)) a := ha
      rw [ha']
    simp_rw [hcong]
    -- Ball exhaustion: ∫ a in Bk k, ‖h a‖^2 ∂vol → ∫ ‖h a‖^2 ∂vol
    apply (aecover_closedBall (tendsto_natCast_atTop_atTop (R := ℝ))).integral_tendsto_of_countably_generated
    -- Integrable ‖h x‖^2
    exact (MeasureTheory.L2.integrable_inner h h).congr
      (Filter.Eventually.of_forall fun a => real_inner_self_eq_norm_sq _)
  -- (E) Tail goes to zero: ‖h - liftG k (restrictToBall k h)‖^2 → 0
  have htail : ∀ (e : L2VF_R3),
      Tendsto (fun k : ℕ => ‖e - liftG k (restrictToBall (↑k : ℝ) e)‖^2) atTop (nhds 0) := by
    intro e
    simp_rw [hpyth e]
    rw [show (0 : ℝ) = ‖e‖^2 - ‖e‖^2 from (sub_self _).symm]
    exact Tendsto.sub tendsto_const_nhds (hnorm_sq_tend e)
  -- (F) Consistency: restrictToBall j (liftG k (w)) = restrictToBall j w for all w : L2VF_R3, j ≤ k
  have hlG_restrict_comp : ∀ j k : ℕ, j ≤ k → ∀ w : L2VF_R3,
      restrictToBall (↑j : ℝ) (liftG k (restrictToBall (↑k : ℝ) w)) =
        restrictToBall (↑j : ℝ) w := by
    intro j k hjk w
    apply Lp.ext
    have hBjBk : Bk j ⊆ Bk k :=
      Metric.closedBall_subset_closedBall (Nat.cast_le.mpr hjk)
    have hle_jk : volume.restrict (Bk j) ≤ volume.restrict (Bk k) :=
      Measure.restrict_mono hBjBk le_rfl
    have hle_j : volume.restrict (Bk j) ≤ (volume : Measure Domain3) :=
      Measure.restrict_le_self
    filter_upwards [MemLp.coeFn_toLp ((Lp.memLp (liftG k (restrictToBall (↑k : ℝ) w))).restrict (Bk j)),
        ae_mono hle_j (hlG_coe k (restrictToBall (↑k : ℝ) w)),
        ae_restrict_of_forall_mem (hBkms j) (fun x hx => Set.indicator_of_mem (hBjBk hx)
          (restrictToBall (↑k : ℝ) w : Domain3 → EuclideanSpace ℝ (Fin 3))),
        ae_mono hle_jk (MemLp.coeFn_toLp ((Lp.memLp w).restrict (Bk k))),
        MemLp.coeFn_toLp ((Lp.memLp w).restrict (Bk j))] with a h1 h2 h3 h4 h5
    simp only [restrictToBall] at *
    rw [h1, h2, h3, h4, ← h5]
  -- (G) Per-ball consistency of limits: restrictToBall j (liftG k (gk k t)) = gk j t (a.e. t, j ≤ k)
  have hgk_consist : ∀ j k : ℕ, j ≤ k → ∀ᵐ t ∂μ,
      restrictToBall (↑j : ℝ) (liftG k (gk k t)) = gk j t := by
    intro j k hjk
    filter_upwards [hgk_conv j, hgk_conv k] with t htj htk
    have hcomp : Tendsto
        (fun n => restrictToBall (↑j : ℝ) (liftG k (restrictToBall (↑k : ℝ) ((galSeq (φ n)).u t : L2VF_R3))))
        atTop (nhds (restrictToBall (↑j : ℝ) (liftG k (gk k t)))) :=
      ((continuous_restrictToBall' (↑j : ℝ)).comp (hlG_cont k)).continuousAt.tendsto.comp htk
    have heq : ∀ n, restrictToBall (↑j : ℝ) (liftG k (restrictToBall (↑k : ℝ) ((galSeq (φ n)).u t : L2VF_R3)))
        = restrictToBall (↑j : ℝ) ((galSeq (φ n)).u t : L2VF_R3) :=
      fun n => hlG_restrict_comp j k hjk ((galSeq (φ n)).u t : L2VF_R3)
    exact (tendsto_nhds_unique htj (hcomp.congr heq)).symm
  -- (H) Energy bound: ‖gk k t‖ ≤ ‖u₀‖ a.e. (from Galerkin energy bound)
  have hgalerkin_bound : ∀ n (t : ℝ), 0 ≤ t → ‖((galSeq (φ n)).u t : L2VF_R3)‖ ≤ ‖(u₀ : L2VF_R3)‖ := by
    intro n t ht
    have heb := (galSeq (φ n)).energy_bound t ht
    have hnl := 𝔊.norm_le (φ n) (u₀ : L2VF_R3)
    -- From heb: ‖u t‖² ≤ ‖P u₀‖²; from hnl: ‖P u₀‖² ≤ ‖u₀‖²; combine then take roots.
    have hsq : ‖((galSeq (φ n)).u t : L2VF_R3)‖ ^ 2 ≤ ‖(u₀ : L2VF_R3)‖ ^ 2 := by
      have h1 : ‖((galSeq (φ n)).u t : L2VF_R3)‖ ^ 2 ≤ ‖𝔊.P (φ n) (u₀ : L2VF_R3)‖ ^ 2 := by
        linarith
      have h2 : ‖𝔊.P (φ n) (u₀ : L2VF_R3)‖ ^ 2 ≤ ‖(u₀ : L2VF_R3)‖ ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hnl 2
      linarith
    exact le_of_pow_le_pow_left₀ (by norm_num) (norm_nonneg _) hsq
  have ht_nonneg : ∀ᵐ t ∂μ, 0 ≤ t :=
    ae_restrict_of_forall_mem measurableSet_Icc (fun t ht => ht.1)
  -- Helper: restriction decreases norm
  have hrestrict_norm_le : ∀ (R : ℝ) (u : L2VF_R3), ‖restrictToBall R u‖ ≤ ‖u‖ := by
    intro R u
    rw [Lp.norm_def, Lp.norm_def]
    apply ENNReal.toReal_mono ((Lp.memLp u).2.ne)
    simp only [restrictToBall]
    rw [eLpNorm_congr_ae (MemLp.coeFn_toLp ((Lp.memLp u).restrict (Metric.closedBall 0 R)))]
    exact eLpNorm_mono_measure _ Measure.restrict_le_self
  have hgk_bound : ∀ k : ℕ, ∀ᵐ t ∂μ, ‖gk k t‖ ≤ ‖(u₀ : L2VF_R3)‖ := fun k => by
    filter_upwards [hgk_conv k, ht_nonneg] with t ht ht0
    exact le_of_tendsto' ht.norm (fun n =>
      (hrestrict_norm_le (↑k : ℝ) ((galSeq (φ n)).u t : L2VF_R3)).trans
        (hgalerkin_bound n t ht0))
  -- (I) Norm monotone: ‖gk j t‖ ≤ ‖gk k t‖ for j ≤ k, a.e. t
  have hgk_norm_mono : ∀ j k : ℕ, j ≤ k → ∀ᵐ t ∂μ, ‖gk j t‖ ≤ ‖gk k t‖ := by
    intro j k hjk
    filter_upwards [hgk_consist j k hjk] with t ht
    calc ‖gk j t‖ = ‖restrictToBall (↑j : ℝ) (liftG k (gk k t))‖ := by rw [ht]
      _ ≤ ‖liftG k (gk k t)‖ := hrestrict_norm_le _ _
      _ = ‖gk k t‖ := hlG_norm k (gk k t)
  -- (J) AESM of liftG k ∘ gk k
  have hliftG_aesm : ∀ k : ℕ, AEStronglyMeasurable (fun t => liftG k (gk k t)) μ :=
    fun k => (hlG_cont k).comp_aestronglyMeasurable (hgk_aesm k)
  -- (K) Gather all ae consistency events into a single ae event
  have hall_consist : ∀ᵐ t ∂μ, ∀ p : ℕ × ℕ, p.1 ≤ p.2 →
      restrictToBall (↑p.1 : ℝ) (liftG p.2 (gk p.2 t)) = gk p.1 t := by
    rw [ae_all_iff]
    intro ⟨j, k⟩
    simp only
    rcases le_or_gt j k with hjk | hlt
    · filter_upwards [hgk_consist j k hjk] with t ht; intro _; exact ht
    · exact Filter.Eventually.of_forall (fun _ h => absurd h (Nat.not_le.mpr hlt))
  have hall_norm_mono : ∀ᵐ t ∂μ, ∀ p : ℕ × ℕ, p.1 ≤ p.2 →
      ‖gk p.1 t‖ ≤ ‖gk p.2 t‖ := by
    rw [ae_all_iff]
    intro ⟨j, k⟩
    simp only
    rcases le_or_gt j k with hjk | hlt
    · filter_upwards [hgk_norm_mono j k hjk] with t ht; intro _; exact ht
    · exact Filter.Eventually.of_forall (fun _ h => absurd h (Nat.not_le.mpr hlt))
  have hall_bound : ∀ᵐ t ∂μ, ∀ k : ℕ, ‖gk k t‖ ≤ ‖(u₀ : L2VF_R3)‖ :=
    ae_all_iff.mpr hgk_bound
  -- (K) Cauchy: liftG k (gk k t) is Cauchy for a.e. t
  have hcauchy : ∀ᵐ t ∂μ, CauchySeq (fun k => liftG k (gk k t)) := by
    filter_upwards [hall_consist, hall_norm_mono, hall_bound] with t hcons hmono hbdd
    -- ‖gk k t‖^2 is non-decreasing and bounded above, hence converges
    have hmono_sq : Monotone (fun k => ‖gk k t‖^2) := fun j k hjk =>
      pow_le_pow_left₀ (norm_nonneg _) (hmono ⟨j, k⟩ hjk) 2
    have hbdd_sq : BddAbove (Set.range (fun k => ‖gk k t‖^2)) :=
      ⟨‖(u₀ : L2VF_R3)‖^2, Set.forall_mem_range.mpr
        (fun k => pow_le_pow_left₀ (norm_nonneg _) (hbdd k) 2)⟩
    obtain ⟨L, hL⟩ := Real.tendsto_of_bddAbove_monotone hbdd_sq hmono_sq
    -- Use Metric.cauchySeq_iff': for ε > 0, find N such that ∀ n ≥ N, ‖u n - u N‖ < ε
    rw [Metric.cauchySeq_iff']
    intro ε hε
    -- ‖gk n t‖^2 ≤ L for all n
    have hle_L : ∀ n, ‖gk n t‖^2 ≤ L := fun n => hmono_sq.ge_of_tendsto hL n
    -- Find N such that L - ‖gk N t‖^2 < ε^2
    have hLN : Tendsto (fun n => L - ‖gk n t‖^2) atTop (nhds 0) := by
      have h : Tendsto (fun n => L - ‖gk n t‖^2) atTop (nhds (L - L)) :=
        tendsto_const_nhds.sub hL
      simp only [sub_self] at h; exact h
    rw [Metric.tendsto_atTop] at hLN
    obtain ⟨N, hN⟩ := hLN (ε^2) (by positivity)
    refine ⟨N, fun n hn => ?_⟩
    rw [dist_eq_norm]
    -- Pythagorean: ‖liftG n (gk n t) - liftG N (gk N t)‖^2 = ‖gk n t‖^2 - ‖gk N t‖^2
    have hcons_t : restrictToBall (↑N : ℝ) (liftG n (gk n t)) = gk N t :=
      hcons ⟨N, n⟩ hn
    have hpyth_t : ‖liftG n (gk n t) - liftG N (gk N t)‖^2 =
        ‖gk n t‖^2 - ‖gk N t‖^2 := by
      calc ‖liftG n (gk n t) - liftG N (gk N t)‖^2
          = ‖liftG n (gk n t) - liftG N (restrictToBall (↑N : ℝ) (liftG n (gk n t)))‖^2 := by
              rw [hcons_t]
        _ = ‖liftG n (gk n t)‖^2 - ‖restrictToBall (↑N : ℝ) (liftG n (gk n t))‖^2 :=
              hpyth (liftG n (gk n t)) N
        _ = ‖gk n t‖^2 - ‖gk N t‖^2 := by rw [hlG_norm, hcons_t]
    -- The norm difference is < ε^2
    have hdiff : ‖gk n t‖^2 - ‖gk N t‖^2 < ε^2 := by
      have hN_gap := hN N le_rfl
      simp only [Real.dist_eq] at hN_gap
      have hN_le_L : ‖gk N t‖^2 ≤ L := hle_L N
      have hn_le_L : ‖gk n t‖^2 ≤ L := hle_L n
      rw [abs_of_nonneg (by linarith)] at hN_gap
      linarith
    -- Conclude: ‖liftG n - liftG N‖ < ε
    have hsq : ‖liftG n (gk n t) - liftG N (gk N t)‖^2 < ε^2 := hpyth_t ▸ hdiff
    have := abs_lt_of_sq_lt_sq hsq hε.le
    rwa [abs_of_nonneg (norm_nonneg _)] at this
  -- (L) Construct the limit function via exists_stronglyMeasurable_limit_of_tendsto_ae
  have hlim_exists : ∀ᵐ t ∂μ, ∃ l : L2VF_R3, Tendsto (fun k => liftG k (gk k t)) atTop (nhds l) :=
    hcauchy.mono fun t ht => cauchySeq_tendsto_of_complete ht
  obtain ⟨u_func, hu_func_sm, hu_func_tendsto⟩ :=
    exists_stronglyMeasurable_limit_of_tendsto_ae (fun k => hliftG_aesm k) hlim_exists
  -- (M) Consistency of limit with gk: restrictToBall k (u_func t) = gk k t, a.e.
  have hconsist_ulim : ∀ k : ℕ, ∀ᵐ t ∂μ, restrictToBall (↑k : ℝ) (u_func t) = gk k t := by
    intro k
    filter_upwards [hu_func_tendsto, hall_consist] with t ht_lim hcons
    -- Use uniqueness: restrictToBall k (liftG j (gk j t)) → restrictToBall k (u_func t)
    -- and for j ≥ k: restrictToBall k (liftG j (gk j t)) = gk k t (const)
    have htend1 : Tendsto (fun j => restrictToBall (↑k : ℝ) (liftG j (gk j t)))
        atTop (nhds (restrictToBall (↑k : ℝ) (u_func t))) :=
      (continuous_restrictToBall' (↑k : ℝ)).continuousAt.tendsto.comp ht_lim
    have hev : (fun _ : ℕ => gk k t)
        =ᶠ[atTop] (fun j => restrictToBall (↑k : ℝ) (liftG j (gk j t))) := by
      filter_upwards [Filter.eventually_ge_atTop k] with j hj
      exact (hcons ⟨k, j⟩ hj).symm
    have htend2 : Tendsto (fun j => restrictToBall (↑k : ℝ) (liftG j (gk j t)))
        atTop (nhds (gk k t)) :=
      Filter.Tendsto.congr' hev (tendsto_const_nhds (x := gk k t))
    exact tendsto_nhds_unique htend1 htend2
  -- (N) Norm bound on u_func: ‖u_func t‖ ≤ ‖u₀‖ a.e.
  have hu_func_bound : ∀ᵐ t ∂μ, ‖u_func t‖ ≤ ‖(u₀ : L2VF_R3)‖ := by
    filter_upwards [hu_func_tendsto, hall_bound] with t ht_lim hbdd
    exact le_of_tendsto' (ht_lim.norm.congr (fun k => hlG_norm k (gk k t))) hbdd
  -- (O) Per-R convergence: restrictToBall R (galSeq (φ n).u t) → restrictToBall R (u_func t), a.e.
  have hperR : ∀ R : ℝ, ∀ᵐ t ∂μ,
      Tendsto (fun n => restrictToBall R ((galSeq (φ n)).u t : L2VF_R3))
        atTop (nhds (restrictToBall R (u_func t))) := by
    intro R
    -- Choose integer k₀ ≥ R
    obtain ⟨k₀, hk₀⟩ := exists_nat_gt R
    filter_upwards [hgk_conv k₀, hconsist_ulim k₀] with t htk₀ hconsk₀
    -- ‖restrictToBall R (galSeq (φ n).u t) - restrictToBall R (u_func t)‖
    -- ≤ ‖restrictToBall k₀ (galSeq (φ n).u t) - restrictToBall k₀ (u_func t)‖
    -- = ‖restrictToBall k₀ (galSeq (φ n).u t) - gk k₀ t‖ (from hconsk₀)
    rw [Metric.tendsto_atTop]
    intro ε hε
    rw [Metric.tendsto_atTop] at htk₀
    obtain ⟨N, hN⟩ := htk₀ ε hε
    refine ⟨N, fun n hn => ?_⟩
    calc dist (restrictToBall R ((galSeq (φ n)).u t : L2VF_R3)) (restrictToBall R (u_func t))
        = ‖restrictToBall R ((galSeq (φ n)).u t : L2VF_R3) - restrictToBall R (u_func t)‖ :=
              dist_eq_norm _ _
      _ ≤ ‖restrictToBall (↑k₀ : ℝ) ((galSeq (φ n)).u t : L2VF_R3) -
              restrictToBall (↑k₀ : ℝ) (u_func t)‖ :=
              restrictToBall_sub_norm_mono R (↑k₀) hk₀.le _ _
      _ = ‖restrictToBall (↑k₀ : ℝ) ((galSeq (φ n)).u t : L2VF_R3) - gk k₀ t‖ := by
              rw [← hconsk₀]
      _ = dist (restrictToBall (↑k₀ : ℝ) ((galSeq (φ n)).u t : L2VF_R3)) (gk k₀ t) :=
              (dist_eq_norm _ _).symm
      _ < ε := hN n hn
  -- (P) Weak convergence of galSeq (φ n).u t → u_func t in L2VF_R3 (a.e.), via ε/3
  -- Collect all needed ae events at once
  have hall_gk_conv : ∀ᵐ t ∂μ, ∀ k : ℕ,
      Tendsto (fun n => restrictToBall (↑k : ℝ) ((galSeq (φ n)).u t : L2VF_R3))
        atTop (nhds (gk k t)) :=
    ae_all_iff.mpr hgk_conv
  have hall_cul : ∀ᵐ t ∂μ, ∀ k : ℕ, restrictToBall (↑k : ℝ) (u_func t) = gk k t :=
    ae_all_iff.mpr hconsist_ulim
  -- For each fixed e_L : L2VF_R3, ‖e_L - liftG k (restrictToBall k e_L)‖ → 0
  have htail_norm : ∀ (e : L2VF_R3),
      Tendsto (fun k : ℕ => ‖e - liftG k (restrictToBall (↑k : ℝ) e)‖) atTop (nhds 0) := by
    intro e
    have h2 := htail e
    have : Tendsto (fun k => Real.sqrt (‖e - liftG k (restrictToBall (↑k : ℝ) e)‖^2))
        atTop (nhds (Real.sqrt 0)) := h2.sqrt
    simp only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] at this
    exact this
  -- The weak convergence at ae t
  have hweak : ∀ᵐ t ∂μ, Tendsto (fun n => toWeakSpace ℝ L2VF_R3 ((galSeq (φ n)).u t : L2VF_R3))
      atTop (nhds (toWeakSpace ℝ L2VF_R3 (u_func t))) := by
    filter_upwards [hall_gk_conv, hall_cul, hall_bound, ht_nonneg, hu_func_tendsto] with t hgk_t hcul_t hbdd hnn ht_lim
    -- At fixed t, prove weak convergence.  `WeakSpace ℝ E = WeakBilin (topDualPairing ℝ E).flip`,
    -- whose defining bilinear form `.flip` is injective because the dual separates points.
    have hBinj : Function.Injective ((topDualPairing ℝ L2VF_R3).flip) :=
      separatingDual_iff_injective.mp inferInstance
    -- `WeakSpace ℝ L2VF_R3` is *definitionally* `WeakBilin (topDualPairing ℝ L2VF_R3).flip`;
    -- apply the abstract tendsto-iff as a term (it type-checks by defeq of the two synonyms).
    refine (WeakBilin.tendsto_iff_forall_eval_tendsto
      (B := (topDualPairing ℝ L2VF_R3).flip) hBinj).mpr ?_
    intro L
    -- Riesz: L = ⟪e_L, ·⟫
    set e_L := (InnerProductSpace.toDual ℝ L2VF_R3).symm L
    have hL_inner : ∀ x, L x = @inner ℝ L2VF_R3 _ e_L x := fun x =>
      (InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := L2VF_R3) (x := x) (y := L)).symm
    -- ε/3 argument
    rw [Metric.tendsto_atTop]
    intro ε hε
    -- C is a uniform bound
    have hC_gal : ∀ n, ‖((galSeq (φ n)).u t : L2VF_R3)‖ ≤ ‖(u₀ : L2VF_R3)‖ :=
      fun n => hgalerkin_bound n t hnn
    have hC_ufunc : ‖u_func t‖ ≤ ‖(u₀ : L2VF_R3)‖ :=
      le_of_tendsto' (ht_lim.norm.congr (fun k => hlG_norm k (gk k t))) hbdd
    -- ε/3 argument.  Let `M := ‖u₀‖ + 1 > 0` bound both the Galerkin states and `u_func t`.
    set M : ℝ := ‖(u₀ : L2VF_R3)‖ + 1 with hM_def
    have hM_pos : 0 < M := by positivity
    have hC_gal' : ∀ n, ‖((galSeq (φ n)).u t : L2VF_R3)‖ ≤ M := fun n => by
      have := hC_gal n; simp only [hM_def]; linarith
    have hC_ufunc' : ‖u_func t‖ ≤ M := by simp only [hM_def]; linarith [hC_ufunc]
    -- Choose `k₀` so the tail `‖e_L - liftG k₀ (restrictToBall k₀ e_L)‖ < ε/(3M)`.
    have htail_e := htail_norm e_L
    rw [Metric.tendsto_atTop] at htail_e
    obtain ⟨k₀, hk₀⟩ := htail_e (ε / (3 * M)) (by positivity)
    have hk₀ := hk₀ k₀ le_rfl
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at hk₀
    -- The good approximant `e' := liftG k₀ (restrictToBall k₀ e_L)` and its tail norm.
    set e' : L2VF_R3 := liftG k₀ (restrictToBall (↑k₀ : ℝ) e_L) with he'_def
    -- Adjoint identity: ⟪e', x⟫ = ⟪restrictToBall k₀ e_L, restrictToBall k₀ x⟫.
    have hadj : ∀ x : L2VF_R3, @inner ℝ L2VF_R3 _ e' x
        = @inner ℝ (L2ballR3 k₀) _ (restrictToBall (↑k₀ : ℝ) e_L) (restrictToBall (↑k₀ : ℝ) x) :=
      fun x => hinner_adj k₀ (restrictToBall (↑k₀ : ℝ) e_L) x
    -- Tail estimate: |⟪e_L - e', x⟫| ≤ ‖e_L - e'‖ ‖x‖ < (ε/(3M)) ‖x‖.
    have htail_est : ∀ x : L2VF_R3, ‖x‖ ≤ M →
        |@inner ℝ L2VF_R3 _ e_L x - @inner ℝ L2VF_R3 _ e' x| < ε / 3 := by
      intro x hx
      have hsub : @inner ℝ L2VF_R3 _ e_L x - @inner ℝ L2VF_R3 _ e' x
          = @inner ℝ L2VF_R3 _ (e_L - e') x := by
        rw [inner_sub_left]
      rw [hsub]
      have heq : (ε / (3 * M)) * M = ε / 3 := by field_simp
      calc |@inner ℝ L2VF_R3 _ (e_L - e') x|
          ≤ ‖e_L - e'‖ * ‖x‖ := abs_real_inner_le_norm _ _
        _ ≤ ‖e_L - e'‖ * M := by
              apply mul_le_mul_of_nonneg_left hx (norm_nonneg _)
        _ < (ε / (3 * M)) * M := by
              apply mul_lt_mul_of_pos_right hk₀ hM_pos
        _ = ε / 3 := heq
    -- Middle-term convergence: ⟪e', galSeq (φ n).u t⟫ → ⟪e', u_func t⟫.
    have hmid_tend : Tendsto (fun n => @inner ℝ L2VF_R3 _ e' ((galSeq (φ n)).u t : L2VF_R3))
        atTop (nhds (@inner ℝ L2VF_R3 _ e' (u_func t))) := by
      -- Rewrite via the adjoint identity into a fixed-radius inner product.
      have hrw : (fun n => @inner ℝ L2VF_R3 _ e' ((galSeq (φ n)).u t : L2VF_R3))
          = fun n => @inner ℝ (L2ballR3 k₀) _ (restrictToBall (↑k₀ : ℝ) e_L)
              (restrictToBall (↑k₀ : ℝ) ((galSeq (φ n)).u t : L2VF_R3)) := by
        funext n; exact hadj _
      rw [hrw]
      -- Target value: ⟪e', u_func t⟫ = ⟪restrictToBall k₀ e_L, gk k₀ t⟫ via hcul_t.
      have htarget : @inner ℝ L2VF_R3 _ e' (u_func t)
          = @inner ℝ (L2ballR3 k₀) _ (restrictToBall (↑k₀ : ℝ) e_L) (gk k₀ t) := by
        rw [hadj, hcul_t k₀]
      rw [htarget]
      -- inner is continuous in the right argument; compose with hgk_t k₀.
      exact ((continuous_const.inner continuous_id).continuousAt.tendsto.comp (hgk_t k₀))
    -- Combine: pick N from the middle convergence, bound by ε/3 + ε/3 + ε/3.
    rw [Metric.tendsto_atTop] at hmid_tend
    obtain ⟨N, hN⟩ := hmid_tend (ε / 3) (by positivity)
    refine ⟨N, fun n hn => ?_⟩
    simp only [LinearMap.flip_apply, topDualPairing_apply, hL_inner]
    rw [Real.dist_eq]
    -- triangle: |⟪e_L,gal⟫ - ⟪e_L,u⟫| ≤ tail(gal) + |⟪e',gal⟫-⟪e',u⟫| + tail(u)
    have hsplit : @inner ℝ L2VF_R3 _ e_L ((galSeq (φ n)).u t : L2VF_R3)
          - @inner ℝ L2VF_R3 _ e_L (u_func t)
        = (@inner ℝ L2VF_R3 _ e_L ((galSeq (φ n)).u t : L2VF_R3)
              - @inner ℝ L2VF_R3 _ e' ((galSeq (φ n)).u t : L2VF_R3))
          + (@inner ℝ L2VF_R3 _ e' ((galSeq (φ n)).u t : L2VF_R3)
              - @inner ℝ L2VF_R3 _ e' (u_func t))
          + (@inner ℝ L2VF_R3 _ e' (u_func t) - @inner ℝ L2VF_R3 _ e_L (u_func t)) := by ring
    have hgal := htail_est _ (hC_gal' n)
    have hufu := htail_est _ hC_ufunc'
    have hmidN := hN n hn
    rw [Real.dist_eq] at hmidN
    calc |@inner ℝ L2VF_R3 _ e_L ((galSeq (φ n)).u t : L2VF_R3)
              - @inner ℝ L2VF_R3 _ e_L (u_func t)|
        = |(@inner ℝ L2VF_R3 _ e_L ((galSeq (φ n)).u t : L2VF_R3)
              - @inner ℝ L2VF_R3 _ e' ((galSeq (φ n)).u t : L2VF_R3))
          + (@inner ℝ L2VF_R3 _ e' ((galSeq (φ n)).u t : L2VF_R3)
              - @inner ℝ L2VF_R3 _ e' (u_func t))
          + (@inner ℝ L2VF_R3 _ e' (u_func t)
              - @inner ℝ L2VF_R3 _ e_L (u_func t))| := by rw [hsplit]
      _ ≤ |@inner ℝ L2VF_R3 _ e_L ((galSeq (φ n)).u t : L2VF_R3)
              - @inner ℝ L2VF_R3 _ e' ((galSeq (φ n)).u t : L2VF_R3)|
          + |@inner ℝ L2VF_R3 _ e' ((galSeq (φ n)).u t : L2VF_R3)
              - @inner ℝ L2VF_R3 _ e' (u_func t)|
          + |@inner ℝ L2VF_R3 _ e' (u_func t)
              - @inner ℝ L2VF_R3 _ e_L (u_func t)| :=
            (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ < ε / 3 + ε / 3 + ε / 3 := by
            have hufu' : |@inner ℝ L2VF_R3 _ e' (u_func t)
                - @inner ℝ L2VF_R3 _ e_L (u_func t)| < ε / 3 := by
              rw [abs_sub_comm]; exact hufu
            exact add_lt_add (add_lt_add hgal hmidN) hufu'
      _ = ε := by ring
  -- (Q) L2Sigma membership of u_func t a.e.
  have hu_func_mem : ∀ᵐ t ∂μ, u_func t ∈ L2Sigma_R3 := by
    filter_upwards [hweak] with t hwt
    apply weakLimit_mem_L2Sigma_R3 (u_func t) (fun n => (galSeq (φ n)).u t : ℕ → L2VF_R3)
    · intro n; exact Submodule.coe_mem _
    · exact hwt
  -- (R) Build u : Time → L2Sigma_R3 and prove the result
  classical
  let u : Time → L2Sigma_R3 := fun t =>
    if h : u_func t ∈ L2Sigma_R3 then ⟨u_func t, h⟩ else ⟨0, Submodule.zero_mem _⟩
  have hu_coe : ∀ᵐ t ∂μ, (u t : L2VF_R3) = u_func t := by
    filter_upwards [hu_func_mem] with t ht
    simp [u, dif_pos ht]
  refine ⟨u, ?_, ?_⟩
  · exact hu_func_sm.aestronglyMeasurable.congr (Filter.EventuallyEq.symm hu_coe)
  · intro R
    filter_upwards [hperR R, hu_coe] with t htR hcoe
    rw [hcoe]; exact htR

/-! ### Per-ball a.e. subsequence extraction -/

/-- **`perBall_ae_subseq` — From L²-in-time Bochner convergence (refine-capable),
extract a FURTHER subsequence converging a.e. in `t` in the `L2ballR3 k` norm.**

Given an input subsequence `ψ`, applies refine-capable axiom A to get `ρ` (further
subsequence of `ψ`) with eLpNorm → 0 along `ψ ∘ ρ`, then converts to a.e.-t convergence
via `tendstoInMeasure_of_tendsto_eLpNorm` + `TendstoInMeasure.exists_seq_tendsto_ae`.

**Proof route (for lean-prover):**
1. Apply refine-capable axiom A with input `ψ` at radius `k` to get `ρ₀` and `g_k` with
   `eLpNorm (fun t => restrictToBall k ((galSeq (ψ (ρ₀ n))).u t) - g_k t) 2 μ → 0`.
2. Each `fun t => restrictToBall k ((galSeq (ψ (ρ₀ n))).u t) - g_k t` is AESM on `[0,T]`
   (Galerkin curve continuous on Ici 0 via `u_hasDeriv`, composed with continuous
   `restrictToBall`, minus AESM `g_k`).
3. Apply `MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm` (p=2, hp_ne_zero=by norm_num)
   to get `TendstoInMeasure μ (fun n t => restrictToBall k ((galSeq (ψ (ρ₀ n))).u t)) atTop g_k`.
4. Apply `TendstoInMeasure.exists_seq_tendsto_ae` to get FURTHER `σ : ℕ → ℕ` StrictMono
   with a.e.-t convergence of `ψ ∘ ρ₀ ∘ σ`.
5. Set the output `ρ := ρ₀ ∘ σ` (StrictMono by composition); conclusion uses `ψ (ρ n) = ψ (ρ₀ (σ n))`. -/
theorem perBall_ae_subseq
    (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T) (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n)
    (ψ : ℕ → ℕ) (hψ : StrictMono ψ) (k : ℕ) :
    ∃ (ρ : ℕ → ℕ) (g_k : ℝ → L2ballR3 k),
      StrictMono ρ ∧
      AEStronglyMeasurable g_k (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)) ∧
      ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)),
        Filter.Tendsto
          (fun n => restrictToBall k ((galSeq (ψ (ρ n))).u t : L2VF_R3))
          Filter.atTop (nhds (g_k t)) := by
  -- Step 1: refine-capable axiom A with input `ψ` at radius `k` gives `ρ₀` and `g_k` with
  -- L²-in-time Bochner convergence along `ψ ∘ ρ₀`.
  obtain ⟨ρ₀, g_k, hρ₀, hg_aesm, heLp⟩ :=
    galerkin_spacetime_precompact_R3 𝔊 F ν hν T hT u₀ galSeq ψ hψ k
  -- Step 2: each ball-restricted Galerkin curve is a.e.-strongly-measurable on `[0,T]`.
  have hf_aesm : ∀ n, AEStronglyMeasurable
      (fun t => restrictToBall (k : ℝ) ((galSeq (ψ (ρ₀ n))).u t : L2VF_R3))
      (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)) := by
    intro n
    have hcurve : ContinuousOn (fun t => ((galSeq (ψ (ρ₀ n))).u t : L2VF_R3)) (Set.Ici 0) :=
      fun t ht => (((galSeq (ψ (ρ₀ n))).u_hasDeriv t ht).continuousAt.continuousWithinAt)
    have hcurve_aesm : AEStronglyMeasurable (fun t => ((galSeq (ψ (ρ₀ n))).u t : L2VF_R3))
        (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)) :=
      (hcurve.mono Set.Icc_subset_Ici_self).aestronglyMeasurable measurableSet_Icc
    exact (continuous_restrictToBall' (k : ℝ)).comp_aestronglyMeasurable hcurve_aesm
  -- Step 3: L²-in-time convergence ⇒ convergence in measure.
  have hTIM : TendstoInMeasure (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T))
      (fun n t => restrictToBall (k : ℝ) ((galSeq (ψ (ρ₀ n))).u t : L2VF_R3)) atTop g_k :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) hf_aesm hg_aesm heLp
  -- Step 4: a.e.-t convergent further subsequence `σ`; output subsequence is `ρ₀ ∘ σ`.
  obtain ⟨σ, hσ, hae⟩ := hTIM.exists_seq_tendsto_ae
  refine ⟨ρ₀ ∘ σ, g_k, hρ₀.comp hσ, hg_aesm, ?_⟩
  filter_upwards [hae] with t ht
  exact ht

/-- **`diag_ae_subseq` — Diagonal subsequence converging a.e. in `t` for ALL ball radii `k : ℕ`.**

From refine-capable `perBall_ae_subseq`, construct by induction a Cantor tower
`φ_0, φ_1, φ_2, …` where `φ_0 = id` and `φ_{k+1} = φ_k ∘ ρ_{k+1}` with `ρ_{k+1}` from
`perBall_ae_subseq (ψ := φ_k)` at radius `k+1`. The diagonal `φ n := φ_n n` is a single
strictly-monotone subsequence converging for every ball radius k : ℕ and a.e. t.

**Proof route (for lean-prover):**
1. Base: `φ_0 = id` (StrictMono). Apply `perBall_ae_subseq id strictMono_id 0` to get `ρ_0`,
   `g_0`, and a.e.-t convergence. Set `φ_1 = ρ_0`.
2. Inductive step: given `φ_k` StrictMono converging on balls `0..k`, apply
   `perBall_ae_subseq φ_k hφ_k (k+1)` to get `ρ_{k+1}` StrictMono with a.e.-t convergence
   of `fun n => restrictToBall (k+1) ((galSeq (φ_k (ρ_{k+1} n))).u t)`. Set `φ_{k+1} = φ_k ∘ ρ_{k+1}`.
3. Diagonal: `φ n := φ_n n`. StrictMono: `φ_{n+1} (n+1) = φ_n (ρ_n (n+1)) > φ_n n = φ n`
   since `ρ_n (n+1) > n` and `φ_n` StrictMono (standard Cantor argument).
4. For fixed `k`, for `n ≥ k`, `φ n` is a value in the range of `φ_k`, so the a.e.-t
   convergence for `φ_k` (established at step k of the tower) transfers.
5. A.e. set: `⋂_{k : ℕ} S_k` is full measure by `MeasureTheory.ae_all_iff.mpr` (each `S_k`
   has full measure). -/
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
  classical
  -- Cumulative extraction tower: `stepData k ψ hψ` = the refine-capable `perBall_ae_subseq` at
  -- radius `k` with input subsequence `ψ`, packaged as a subtype carrying the further `ρ`, its
  -- strict-monotonicity, and the radius-`k` limit `g` + a.e.-t convergence along `ψ ∘ ρ`.
  let stepData : ∀ (k : ℕ) (ψ : ℕ → ℕ), StrictMono ψ →
      { ρ : ℕ → ℕ // StrictMono ρ ∧ ∃ g : ℝ → L2ballR3 k,
        AEStronglyMeasurable g (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)) ∧
        ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)), Filter.Tendsto
          (fun n => restrictToBall k ((galSeq (ψ (ρ n))).u t : L2VF_R3))
          Filter.atTop (nhds (g t)) } :=
    fun k ψ hψ =>
      let h := perBall_ae_subseq 𝔊 F ν hν T hT u₀ galSeq ψ hψ k
      ⟨h.choose, h.choose_spec.choose_spec.1,
        h.choose_spec.choose, h.choose_spec.choose_spec.2.1, h.choose_spec.choose_spec.2.2⟩
  -- Recursively build the cumulative extraction `Φ k`, with `Φ (k+1) = Φ k ∘ ρ k`.
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
  -- At each level `k`, the cumulative extraction `Φ (k+1)` converges on ball `k` (a.e.-t).
  have hconv : ∀ k : ℕ, ∃ g : ℝ → L2ballR3 k,
      AEStronglyMeasurable g (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)) ∧
      ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)), Filter.Tendsto
        (fun n => restrictToBall k ((galSeq (Φ (k + 1) n)).u t : L2VF_R3))
        Filter.atTop (nhds (g t)) := by
    intro k
    obtain ⟨g, hg_aesm, hg_ae⟩ := (stepData k (rec_data k).1 (rec_data k).2).2.2
    exact ⟨g, hg_aesm, hg_ae⟩
  -- The diagonal subsequence.
  refine ⟨fun n => Φ (n + 1) (n + 1), ?_, ?_⟩
  · -- StrictMono of the diagonal.
    intro a b hab
    have h1 : Φ (a + 1) (a + 1) < Φ (a + 1) (b + 1) := hΦmono (a + 1) (by omega)
    obtain ⟨R, hR, hReq⟩ :=
      nested_extraction_factor Φ ρ hρmono hstep (a + 1) (b + 1) (by omega)
    have h2 : Φ (a + 1) (b + 1) ≤ Φ (b + 1) (b + 1) := by
      rw [hReq]
      exact (hΦmono (a + 1)).monotone (hR.id_le (b + 1))
    exact lt_of_lt_of_le h1 h2
  · -- Per-ball a.e.-t convergence of the diagonal.
    intro k
    obtain ⟨g, hg_aesm, hg_ae⟩ := hconv k
    refine ⟨g, hg_aesm, ?_⟩
    -- For `n ≥ k`, factor `Φ (n+1) = Φ (k+1) ∘ R` with `R` strictly monotone; the diagonal at
    -- radius `k` is then a subsequence of the level-`k` convergent sequence.
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
    rw [hσ_eq n hn]

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
