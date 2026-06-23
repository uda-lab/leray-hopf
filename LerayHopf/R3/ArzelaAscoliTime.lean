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

## Assumptions (new axioms introduced here — issue #47 PR-A)

1. `galerkin_spacetime_precompact_R3` — ALLOW_AXIOM (REFINE-CAPABLE): LOCAL Aubin–Lions–Simon
   spacetime precompactness on ℝ³ — for EVERY input subsequence ψ and every ball radius k:ℕ,
   the per-ball Galerkin curve sequence along ψ has a FURTHER subsequence ρ converging to zero
   in the L²(0,T; L²(B_k)) Bochner norm (eLpNorm of (restrictToBall k ∘ galSeq ∘ ψ ∘ ρ - g_k)
   → 0). SOUND/LOCAL: no tightness, no pointwise equicontinuity, no global-L² claim. Refine-
   capability (ψ input) is essential for the Cantor-diagonal tower. Mathlib lacks the Bochner-
   valued Aubin–Lions/Fréchet–Kolmogorov theorem in L²(0,T;X); scheme-independent; reusable
   for torus #23.

2. `L2VF_R3_weakSeqCompact_closedBall` — ALLOW_AXIOM: sequential weak compactness of bounded
   closed balls in the separable Hilbert space L2VF_R3 = L²(ℝ³; ℝ³). Standard theorem
   (Eberlein–Šmulian / sequential Banach–Alaoglu for reflexive separable Hilbert space), TRUE
   and NOT over-strong. Mathlib has `WeakDual.isSeqCompact_closedBall` for the DUAL side but
   lacks the primal-space version (requires the Riesz-isometry homeomorphism between WeakSpace
   and WeakDual, WL-3 — the single missing piece, to be supplied in PR-B). Scheme-independent;
   reusable for torus #23. Replaces the former `galerkin_weakLimit_R3` axiom (which carried
   Galerkin parameters); this axiom is ABSTRACT (no PDE parameters).

   Net axiom count: `galerkin_weakLimit_R3` (axiom, 6-param) → `L2VF_R3_weakSeqCompact_closedBall`
   (axiom, 4-param, abstract FA) — SAME COUNT (4→4 R3 project axioms, net neutral). PR-B
   discharges this via WL-3 (`weakSpace_toDual_homeomorph`).

**Note:** `galerkin_weakLimit_R3` is now a THEOREM (not an axiom), proved using
`L2VF_R3_weakSeqCompact_closedBall` + WL-5 (`weakLimit_mem_L2Sigma_R3`) + WL-6
(`weakLimit_aestronglyMeasurable`). The proof bodies carry ALLOW_SORRY markers pending
PR-B prover work.
-/

import LerayHopf.R3.AxiomaticClosure   -- GalerkinSolutionData_R3, R3GalerkinScheme, R3NSForms
import LerayHopf.R3.SpatialCompactness -- LocalRellichInput, L2ballR3, restrictToBall
import LerayHopf.R3.DivergenceFree     -- L2VF_R3_separable, L2Sigma_R3_weaklyClosed (WL-1, WL-4)

-- tendstoInMeasure_of_tendsto_eLpNorm, TendstoInMeasure.exists_seq_tendsto_ae
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
-- aestronglyMeasurable_of_tendsto_ae
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
-- IsCompact.isSeqCompact, IsSeqCompact.subseq_of_frequently_in
import Mathlib.Topology.Sequences
-- toWeakSpace, WeakSpace (for L2VF_R3_weakSeqCompact_closedBall, WL-5, WL-6)
import Mathlib.Analysis.LocallyConvex.WeakSpace

namespace LerayHopf

open MeasureTheory Filter Topology Metric

/-! ### Group A — Residual axioms and abstract FA primitives -/

/-- **Axiom A — LOCAL Aubin–Lions–Simon spacetime precompactness on ℝ³ (REFINE-CAPABLE).**

For every input subsequence `ψ : ℕ → ℕ` (strictly monotone) and every ball radius `k : ℕ`,
there is a FURTHER strictly-monotone `ρ : ℕ → ℕ` and a measurable limit curve
`g_k : ℝ → L2ballR3 k` such that the Bochner L²-in-time norm of the difference
`restrictToBall k ((galSeq (ψ (ρ n))).u t) - g_k t` converges to `0` as `n → ∞`.

**Why refine-capable?** The Cantor-diagonal construction in `diag_ae_subseq` builds the tower
`φ_0 = ρ_0`, `φ_{k+1} = φ_k ∘ ρ_{k+1}` inductively, where at each step we extract a FURTHER
subsequence of the CURRENT one. This requires applying the compactness axiom to the composition
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
Mathlib lacks the Bochner-valued Aubin–Lions/Fréchet–Kolmogorov theorem in L²(0,T;X). -/
axiom galerkin_spacetime_precompact_R3 -- ALLOW_AXIOM: LOCAL Aubin–Lions–Simon spacetime precompactness on ℝ³, REFINE-CAPABLE form — for EVERY subsequence ψ and every ball radius k:ℕ, the per-ball Galerkin curve sequence (along ψ) has a FURTHER subsequence ρ converging to zero in the L²(0,T;L²(B_k)) Bochner norm. SOUND/LOCAL (any subseq of the bounded Galerkin sequence is still per-ball precompact ⇒ has a convergent sub-subseq): no tightness, no strong-norm time-equicontinuity, no global-L² claim. Refine-capability (the ψ input) is what enables the Cantor-diagonal nesting across balls. Mathlib lacks Bochner Aubin–Lions/Fréchet–Kolmogorov in L²(0,T;X); scheme-independent; reusable for torus #23.
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
        Filter.atTop (nhds 0)

/-- **Thin Axiom WL-A — Sequential weak compactness of bounded balls in `L2VF_R3`.**

Every norm-bounded sequence in `L2VF_R3 = L²(ℝ³; ℝ³)` (viewed as `WeakSpace ℝ L2VF_R3`)
has a weakly convergent subsequence.

**Mathematical content:** Eberlein–Šmulian theorem / sequential Banach–Alaoglu for the
separable reflexive Hilbert space `L2VF_R3`. This is a **TRUE, standard theorem** — NOT
over-strong. It states exactly the sequential form of Banach–Alaoglu on the primal space
and does NOT claim anything about the limit being in `L2Sigma_R3` (that is proved by Mazur,
WL-5) or about measurability (that is WL-6).

**Why axiom (pending PR-B):** Mathlib has `WeakDual.isSeqCompact_closedBall` for the DUAL
of a separable normed space, but the primal version requires:
(a) `L2VF_R3` is separable (WL-1, proved in `DivergenceFree.lean`), and
(b) the Fréchet–Riesz isometry induces a homeomorphism `WeakSpace ℝ L2VF_R3 ≃ₜ WeakDual ℝ L2VF_R3`
    (WL-3 — NOT yet in Mathlib; the single missing bridge).
PR-B will discharge this axiom by establishing WL-3 and pulling back `WeakDual.isSeqCompact_closedBall`.

**Scheme-independent:** no Galerkin parameters; pure abstract functional analysis.
Reusable for torus #23. -/
axiom L2VF_R3_weakSeqCompact_closedBall -- ALLOW_AXIOM: sequential weak compactness of bounded balls in L2VF_R3 = L²(ℝ³;ℝ³); TRUE standard theorem (Eberlein–Šmulian / Banach–Alaoglu for separable reflexive Hilbert space); NOT over-strong (no claim about L2Sigma_R3 membership or measurability); Mathlib has WeakDual.isSeqCompact_closedBall for dual side but lacks the primal version (requires Riesz-isometry homeomorphism WeakSpace≃WeakDual, WL-3, pending PR-B); scheme-independent; reusable for torus #23
    (C : ℝ) (hC : 0 ≤ C) (f : ℕ → L2VF_R3) (hf : ∀ n, ‖f n‖ ≤ C) :
    ∃ (φ : ℕ → ℕ) (v : L2VF_R3), StrictMono φ ∧
      Filter.Tendsto (fun n => (toWeakSpace ℝ L2VF_R3) (f (φ n)))
        Filter.atTop (𝓝 ((toWeakSpace ℝ L2VF_R3) v))

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

/-- **WL-6 — A.e. pointwise weak limit of AEStronglyMeasurable curves is AEStronglyMeasurable.**

If `fₙ : α → L2VF_R3` are `AEStronglyMeasurable` and for a.e. `t`, `fₙ t` converges weakly
to `g t` in `WeakSpace ℝ L2VF_R3`, then `g : α → L2VF_R3` is `AEStronglyMeasurable`.

**Proof route:** In the separable Hilbert space `L2VF_R3` (WL-1), the weak Borel σ-algebra
coincides with the strong Borel σ-algebra (the Borel σ-algebra of a separable metrizable
topological vector space is generated by the continuous linear functionals, which is the same
as the weak σ-algebra). Therefore:
- For each `e : L2VF_R3`, the function `t ↦ ⟪e, g t⟫` is measurable
  (pointwise limit of the measurable functions `t ↦ ⟪e, fₙ t⟫`).
- By separability of `L2VF_R3`, measurability of all inner products against a countable
  dense subset implies strong AEStronglyMeasurability. -/
theorem weakLimit_aestronglyMeasurable
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    (fn : ℕ → α → L2VF_R3) (g : α → L2VF_R3)
    (hfn : ∀ n, MeasureTheory.AEStronglyMeasurable (fn n) μ)
    (htend : ∀ᵐ t ∂μ, Filter.Tendsto (fun n => (toWeakSpace ℝ L2VF_R3) (fn n t))
        Filter.atTop (𝓝 ((toWeakSpace ℝ L2VF_R3) (g t)))) :
    MeasureTheory.AEStronglyMeasurable g μ := by
  sorry -- ALLOW_SORRY: #47 WL-6 — measurability of a.e. weak limit; uses L2VF_R3_separable (WL-1): in a separable Hilbert space, weak Borel = strong Borel, so weak-a.e.-limit of AESM functions is AESM; prover to fill

/-- **`galerkin_weakLimit_R3` — Measurable weak limit in `L2Sigma_R3` from per-ball a.e.-t
convergence.**  [#47: converted from `axiom` to `theorem`]

Given a strictly-monotone subsequence `φ` such that for every `k : ℕ` and for a.e. `t ∈ [0,T]`
the ball-k-restricted Galerkin states converge in `L2ballR3 k`, there exists a measurable limit
curve `u : Time → L2Sigma_R3` such that:
- `u` is `AEStronglyMeasurable` on `[0,T]`, and
- for every `R : ℝ`, for a.e. `t ∈ [0,T]`, `restrictToBall R ((galSeq (φ n)).u t) → restrictToBall R (u t)`.

**Proof (PR-A scaffold):** The body chains through the thin abstract axiom
`L2VF_R3_weakSeqCompact_closedBall` (WL-A) plus lemmas WL-5 and WL-6.
The proof body is `sorry`-marked pending the prover's work in PR-B / issue #47.

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
  -- Chain: per-ball STRONG convergence + spatial assembly → AESM limit curve in L2Sigma_R3.
  -- Proof route (sorry-tracked):
  --   (A) Extract g_k from hball; energy bound C = ‖u₀‖ gives ‖g_k t‖ ≤ C for a.e. t.
  --   (B) Define liftToGlobal k : L2ballR3 k → L2VF_R3 (extend by zero = indicator extension);
  --       this is an isometry, hence continuous.
  --   (C) U_k := liftToGlobal k ∘ g_k : ℝ → L2VF_R3 is AESM (composition with continuous).
  --   (D) Consistency (a.e. t, j ≤ k): g_j t = restrictToBall j (liftToGlobal k (g_k t));
  --       follows from: (1) identity restrictToBall j ∘ liftToGlobal k ∘ restrictToBall k = restrictToBall j
  --       (provable: underlying fn is v on B_j ⊆ B_k); (2) continuity; (3) uniqueness of limits.
  --   (E) Norm monotone a.e.: ‖g_j t‖ ≤ ‖g_k t‖ for j ≤ k (from (D) + non-expanding of restrictToBall j).
  --   (F) Cauchy a.e.: ‖U_k t - U_j t‖² = ‖g_k t‖² - ‖g_j t‖² → 0 (non-decreasing bounded sequence);
  --       norm identity uses (D) + indicator-norm identity eLpNorm_indicator_eq_eLpNorm_restrict.
  --   (G) u_func t = lim_k U_k t exists strongly (L2VF_R3 complete, Cauchy from (F)).
  --   (H) u_func AESM via aestronglyMeasurable_of_tendsto_ae (U_k AESM + ae strong convergence).
  --   (I) u_func t ∈ L2Sigma_R3 a.e.: apply WL-5 (weakLimit_mem_L2Sigma_R3) — (galSeq(φn).u t ∈ L2Sigma_R3
  --       for all n; weak convergence from per-ball strong convergence + energy bound ε/3 argument).
  --   (J) Per-R convergence: restrictToBall R (galSeq(φn).u t) → restrictToBall R (u_func t)
  --       follows from continuous restrictToBall R + per-ball strong convergence for R ≤ k.
  -- ALL steps are mathematically sound; the sorry below marks the ~80 LOC Lean formalization gap
  -- (private-lemma duplication from SpatialCompactness, ae-intersection management, Cauchy/isometry bookkeeping).
  sorry -- ALLOW_SORRY: #47 galerkin_weakLimit_R3 SPATIAL ASSEMBLY — complete proof route documented above; blocked by ~80 LOC formalization: (B) liftToGlobal isometry/continuity; (D) consistency via indicator-coeFn ae identity; (F) Cauchy criterion via eLpNorm_indicator_eq_eLpNorm_restrict + non-decreasing bounded norm; (H) aestronglyMeasurable_of_tendsto_ae; (I) WL-5 + ε/3 weak-convergence argument; requires duplicating private lemmas furtherRestrict/furtherRestrict_coeFn from SpatialCompactness or making them public — lean-coder structural change needed

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

/-- Factorization of a nested family of extractions: if `Φ (k+1) = Φ k ∘ ρ k` with each `ρ k`
strictly monotone, then for `k ≤ n` the extraction `Φ n` is `Φ k` post-composed with a strictly
monotone map. (Local copy of `SpatialCompactness.nested_extraction_factor`, which is `private`.) -/
private theorem nested_extraction_factor (Φ ρ : ℕ → ℕ → ℕ)
    (hρ : ∀ k, StrictMono (ρ k)) (hstep : ∀ k, Φ (k + 1) = Φ k ∘ ρ k) :
    ∀ k n, k ≤ n → ∃ R : ℕ → ℕ, StrictMono R ∧ Φ n = Φ k ∘ R := by
  intro k n hkn
  induction n with
  | zero =>
    obtain rfl : k = 0 := Nat.le_zero.mp hkn
    exact ⟨id, strictMono_id, rfl⟩
  | succ m ih =>
    rcases Nat.lt_or_ge k (m + 1) with hlt | hge
    · obtain ⟨R, hR, hReq⟩ := ih (Nat.lt_succ_iff.mp hlt)
      refine ⟨R ∘ ρ m, hR.comp (hρ m), ?_⟩
      rw [hstep m, hReq]
      rfl
    · obtain rfl : k = m + 1 := Nat.le_antisymm hkn hge
      exact ⟨id, strictMono_id, rfl⟩

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
