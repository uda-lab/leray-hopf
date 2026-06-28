import LerayHopf.GalerkinProjection
import LerayHopf.SobolevTorus
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Normed.Lp.lpSpace

open MeasureTheory Submodule Filter Topology

/-!
# Fourier-tail Rellich compact embedding H¹(𝕋³; ℂ) ↪ L²(𝕋³; ℂ)

**M5 — Rellich compact embedding via Fourier tails (Strategy B).**

Plan document: `docs/scratch/m5-rellich.md`.

We work entirely with `f : L2C`, the predicate `memH1Torus f` (Summability of the weighted
Fourier-coefficient sum), and an explicit real bound `∑' k, (1 + ‖k‖²) * ‖f̂(k)‖² ≤ M²`.
No H¹ normed-space structure is built here (deferred to a later milestone).

## Main results (lemma chain L1 → L2 → L3 → L4 → Bonus → L5)

- `L2C_norm_sq_eq_tsum_coeff_sq`       (L1) : Parseval identity `‖f‖² = ∑' k, ‖f̂(k)‖²`
                                              (proved in `LerayHopf.FunctionSpaces`, available here).
- `L2C_norm_sub_fourierProjection_sq`  (L2) : `‖f - P_N f‖² = ∑_{k ∉ box} ‖f̂(k)‖²`.
- `H1_tail_bound`                      (L3) : tail bound `∑_{k ∉ box} ‖f̂(k)‖² ≤ M²/(1+N²)`.
- `H1_ball_uniform_L2_approx`          (L4) : uniform L²-approximation on the H¹-ball.
- `fourierProjection_n_isCompactOperator` (Bonus) : `P_N` is compact (finite-rank).
- `H1_ball_totallyBounded`             (L5) : the H¹-ball is totally bounded in L² (Rellich).

## Assumptions

None beyond mathlib axioms. No `sorry` is present without an `-- ALLOW_SORRY` marker.
-/

namespace LerayHopf

/-! ### L1: Parseval — `‖f‖² = ∑' k, ‖f̂(k)‖²`

`L2C_norm_sq_eq_tsum_coeff_sq` is proved in `LerayHopf.FunctionSpaces` (upstream) and
is available here via the transitive import chain
`RellichEmbedding → GalerkinProjection → Leray → DivergenceFree → FunctionSpaces`. -/

/-! ### L2: Tail-norm identity — `‖f - P_N f‖² = ∑_{k ∉ fourierBox N} ‖f̂(k)‖²` -/

/-- **L2 (Tail-norm identity).** The squared L²-norm of the Galerkin residual equals the sum
of squared Fourier coefficients over the complement of the truncation box.

Proof route for lean-prover:
1. `map_sub` on `torus3_mFourierBasis.repr` gives
   `mFourierCoeff3 (f - P_N f) k = mFourierCoeff3 f k - mFourierCoeff3 (P_N f) k`.
2. `fourierProjection_n_mFourierCoeff` gives
   `mFourierCoeff3 (P_N f) k = if k ∈ fourierBox N then mFourierCoeff3 f k else 0`.
3. Hence `mFourierCoeff3 (f - P_N f) k = if k ∈ fourierBox N then 0 else mFourierCoeff3 f k`.
4. Apply L1 to `f - P_N f`; the in-box terms contribute zero to the tsum.
   Use `Summable.sum_add_tsum_subtype_compl` (or split via indicator) to restrict
   the sum to `{k // k ∉ fourierBox N}`.
Key mathlib lemmas: `map_sub`, `fourierProjection_n_mFourierCoeff` (this project),
`L2C_norm_sq_eq_tsum_coeff_sq` (L1 above), `Summable.sum_add_tsum_subtype_compl`. -/
theorem L2C_norm_sub_fourierProjection_sq (N : ℕ) (f : L2C) :
    ‖f - fourierProjection_n N f‖ ^ 2 =
      ∑' k : {k : Fin 3 → ℤ // k ∉ fourierBox N}, ‖mFourierCoeff3 f k‖ ^ 2 := by
  have hcoeff : ∀ k : Fin 3 → ℤ, mFourierCoeff3 (f - fourierProjection_n N f) k =
      if k ∈ fourierBox N then 0 else mFourierCoeff3 f k := by
    intro k
    have hsub : mFourierCoeff3 (f - fourierProjection_n N f) k =
        mFourierCoeff3 f k - mFourierCoeff3 (fourierProjection_n N f) k := by
      simp only [mFourierCoeff3, map_sub, lp.coeFn_sub, Pi.sub_apply]
    rw [hsub, fourierProjection_n_mFourierCoeff]
    by_cases hk : k ∈ fourierBox N <;> simp [hk]
  rw [L2C_norm_sq_eq_tsum_coeff_sq]
  have hsupp : Function.support
      (fun k : Fin 3 → ℤ => ‖mFourierCoeff3 (f - fourierProjection_n N f) k‖ ^ 2)
      ⊆ {k : Fin 3 → ℤ | k ∉ fourierBox N} := by
    intro k hk
    simp only [Function.mem_support, ne_eq] at hk
    simp only [Set.mem_setOf_eq]
    intro hmem
    exact hk (by rw [hcoeff k, if_pos hmem, norm_zero]; norm_num)
  rw [← tsum_subtype_eq_of_support_subset hsupp]
  exact tsum_congr fun k => by rw [hcoeff k, if_neg k.2]

/-! ### L3: Tail bound — `∑_{k ∉ fourierBox N} ‖f̂(k)‖² ≤ M²/(1+N²)` -/

/-- **L3 (Tail bound).** For `f` with H¹-energy bounded by `M²`, the Fourier energy outside
the box `fourierBox N` is at most `M² / (1 + N²)`.

Mathematical argument: for `k ∉ fourierBox N` there exists `i` with `|k i| > N`, so
`(k i : ℝ)² > N²`, hence `1 + ∑ᵢ (kᵢ)² ≥ 1 + N²`.  Multiplying by `‖f̂(k)‖²` and summing,
`(1 + N²) * ∑_{k ∉ box} ‖f̂k‖² ≤ ∑_{k ∉ box} (1 + ‖k‖²) * ‖f̂k‖² ≤ ∑_k (1 + ‖k‖²) * ‖f̂k‖² ≤ M²`.
Divide by `(1 + N²)`.

Proof route for lean-prover:
1. Show `∀ k ∉ fourierBox N, (1 + (N : ℝ)^2) ≤ 1 + ∑ i, (k i : ℝ)^2`.
   Negation of `fourierBox` membership gives `∃ i, N < |k i|`, hence `(k i : ℝ)^2 > N^2`.
   Key: `Int.cast_lt`, `abs_lt`, `sq_lt_sq'`.
2. Multiply the pointwise weight inequality by `‖f̂k‖^2` and sum over `{k ∉ box}`.
3. Use `Summable.tsum_le_tsum` for both monotonicity steps.
4. Divide by `(1 + N^2)` (positive since `0 ≤ N`).
Key mathlib lemmas: `Summable.tsum_le_tsum`, `tsum_subtype` style, `Int.cast_lt`, `sq_lt_sq`. -/
theorem H1_tail_bound (N : ℕ) (f : L2C)
    (hH1 : Summable (fun k : Fin 3 → ℤ =>
        (1 + ∑ i : Fin 3, (k i : ℝ) ^ 2) * ‖mFourierCoeff3 f k‖ ^ 2))
    (M : ℝ)
    (hM : ∑' k : Fin 3 → ℤ, (1 + ∑ i : Fin 3, (k i : ℝ) ^ 2) * ‖mFourierCoeff3 f k‖ ^ 2 ≤ M ^ 2) :
    ∑' k : {k : Fin 3 → ℤ // k ∉ fourierBox N}, ‖mFourierCoeff3 f k‖ ^ 2
      ≤ M ^ 2 / (1 + (N : ℝ) ^ 2) := by
  -- Abbreviations: `w` is the H¹ weight, `g` the squared coefficient.
  set w : (Fin 3 → ℤ) → ℝ := fun k => 1 + ∑ i : Fin 3, (k i : ℝ) ^ 2 with hw_def
  set g : (Fin 3 → ℤ) → ℝ := fun k => ‖mFourierCoeff3 f k‖ ^ 2 with hg_def
  have hg_nonneg : ∀ k, 0 ≤ g k := fun k => by positivity
  have hw_one : ∀ k, (1 : ℝ) ≤ w k :=
    fun k => le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => sq_nonneg _)
  have hwg_nonneg : ∀ k, 0 ≤ w k * g k :=
    fun k => mul_nonneg (zero_le_one.trans (hw_one k)) (hg_nonneg k)
  -- `g` is summable by comparison with the weighted sum.
  have hg_sum : Summable g :=
    hH1.of_nonneg_of_le hg_nonneg fun k => le_mul_of_one_le_left (hg_nonneg k) (hw_one k)
  -- Pointwise weight bound outside the box: `1 + N² ≤ w k`.
  have hweight : ∀ k : Fin 3 → ℤ, k ∉ fourierBox N → 1 + (N : ℝ) ^ 2 ≤ w k := by
    intro k hk
    simp only [fourierBox, Fintype.mem_piFinset, Finset.mem_Icc, not_forall, not_and_or,
      not_le] at hk
    obtain ⟨i, hi⟩ := hk
    have hsq : (N : ℝ) ^ 2 ≤ (k i : ℝ) ^ 2 := by
      have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
      rcases hi with h | h
      · have : (k i : ℝ) < -(N : ℝ) := by exact_mod_cast h
        nlinarith
      · have : (N : ℝ) < (k i : ℝ) := by exact_mod_cast h
        nlinarith
    have hsum : (k i : ℝ) ^ 2 ≤ ∑ j : Fin 3, (k j : ℝ) ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg ((k j : ℝ))) (Finset.mem_univ i)
    simp only [hw_def]
    linarith
  -- Summability on the complement subtype.
  have hsub_g : Summable (fun k : {k : Fin 3 → ℤ // k ∉ fourierBox N} => g k.1) :=
    hg_sum.subtype _
  have hsub_wg : Summable (fun k : {k : Fin 3 → ℤ // k ∉ fourierBox N} => w k.1 * g k.1) :=
    hH1.subtype _
  -- Step 1: (1 + N²) * tail ≤ weighted tail.
  have step1 : (1 + (N : ℝ) ^ 2) * ∑' k : {k : Fin 3 → ℤ // k ∉ fourierBox N}, g k.1
      ≤ ∑' k : {k : Fin 3 → ℤ // k ∉ fourierBox N}, w k.1 * g k.1 := by
    rw [← tsum_mul_left]
    exact Summable.tsum_le_tsum
      (fun k => mul_le_mul_of_nonneg_right (hweight k.1 k.2) (hg_nonneg k.1))
      (hsub_g.mul_left _) hsub_wg
  -- Step 2: weighted tail ≤ full weighted sum ≤ M².
  have step2 : ∑' k : {k : Fin 3 → ℤ // k ∉ fourierBox N}, w k.1 * g k.1
      ≤ ∑' k : Fin 3 → ℤ, w k * g k :=
    Summable.tsum_subtype_le _ _ hwg_nonneg hH1
  have hpos : (0 : ℝ) < 1 + (N : ℝ) ^ 2 := by positivity
  rw [le_div_iff₀ hpos, mul_comm]
  calc (1 + (N : ℝ) ^ 2) * ∑' k : {k : Fin 3 → ℤ // k ∉ fourierBox N}, g k.1
      ≤ ∑' k : {k : Fin 3 → ℤ // k ∉ fourierBox N}, w k.1 * g k.1 := step1
    _ ≤ ∑' k : Fin 3 → ℤ, w k * g k := step2
    _ ≤ M ^ 2 := hM

/-! ### L4: Uniform L²-approximation on the H¹-ball -/

/-- **L4 (Uniform approximation).** On any H¹-bounded set, the Galerkin projections converge
uniformly in L²: for any `ε > 0` there exists `N` such that every `f` with H¹-energy ≤ `M²`
satisfies `‖f - P_N f‖ ≤ ε`.

Proof route for lean-prover:
1. From L2 + L3: `‖f - P_N f‖^2 ≤ M^2 / (1 + N^2)`.
2. Choose `N` with `M / Real.sqrt (1 + N^2) ≤ ε`, equivalently `1 + N^2 ≥ (M/ε)^2`.
   (Exists by `Nat.exists_pow_le_of_le_one` or `exists_nat_gt` applied to `(M/ε)^2 - 1`.)
3. Apply `Real.sqrt_le_sqrt` and `Real.sqrt_sq` to pass from `‖f - P_N f‖^2` to `‖f - P_N f‖`.
Key mathlib lemmas: `L2C_norm_sub_fourierProjection_sq` (L2), `H1_tail_bound` (L3),
`Real.sqrt_le_sqrt`, `Real.sqrt_sq_eq_abs`, `exists_nat_gt`. -/
theorem H1_ball_uniform_L2_approx (M : ℝ) (hM0 : 0 ≤ M) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ f : L2C,
      memH1Torus f →
      (∑' k : Fin 3 → ℤ, (1 + ∑ i : Fin 3, (k i : ℝ) ^ 2) * ‖mFourierCoeff3 f k‖ ^ 2 ≤ M ^ 2) →
      ‖f - fourierProjection_n N f‖ ≤ ε := by
  obtain ⟨N, hN⟩ := exists_nat_gt (M ^ 2 / ε ^ 2)
  refine ⟨N, fun f hf hbound => ?_⟩
  have hkey : ‖f - fourierProjection_n N f‖ ^ 2 ≤ M ^ 2 / (1 + (N : ℝ) ^ 2) := by
    rw [L2C_norm_sub_fourierProjection_sq]
    exact H1_tail_bound N f hf M hbound
  have hle : M ^ 2 / (1 + (N : ℝ) ^ 2) ≤ ε ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    have h2 : M ^ 2 < (N : ℝ) * ε ^ 2 := by
      rwa [div_lt_iff₀ (by positivity)] at hN
    nlinarith [sq_nonneg ((N : ℝ) - 1), sq_nonneg ε, Nat.cast_nonneg (α := ℝ) N]
  have hsq : ‖f - fourierProjection_n N f‖ ^ 2 ≤ ε ^ 2 := hkey.trans hle
  have hs := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hε.le] at hs

/-! ### Bonus: `fourierProjection_n N` is a compact operator -/

/-- **Bonus (finite-rank ⟹ compact).** The Galerkin projection `fourierProjection_n N` is a
compact operator on `L2C`.

Proof route for lean-prover (sorry-free, ~5 lines):
1. `fourierProjection_n N = (fourierSpan N).starProjection
     = (fourierSpan N).subtypeL ∘ (fourierSpan N).orthogonalProjectionOnto`.
2. `fourierSpan N` is `FiniteDimensional ℂ` (instance `fourierSpan_finiteDimensional`).
3. Hence `fourierSpan N` is `ProperSpace` via `RCLike.properSpace_submodule`.
4. `ProperSpace` implies `LocallyCompactSpace` (instance `locallyCompact_of_proper`).
5. `isCompactOperator_of_locallyCompactSpace_dom` applies to
   `(fourierSpan N).orthogonalProjectionOnto : L2C →L[ℂ] ↥(fourierSpan N)`.
6. `IsCompactOperator.clm_comp` with `(fourierSpan N).subtypeL` gives the result.
Key mathlib lemmas: `isCompactOperator_of_locallyCompactSpace_dom`, `IsCompactOperator.clm_comp`,
`RCLike.properSpace_submodule`, `Submodule.starProjection`. -/
theorem fourierProjection_n_isCompactOperator (N : ℕ) :
    IsCompactOperator (fourierProjection_n N : L2C →L[ℂ] L2C) := by
  -- `P_N = subtypeL ∘ orthogonalProjectionOnto`; the middle space `fourierSpan N` is
  -- finite-dimensional, hence proper, hence locally compact.
  have h : IsCompactOperator ((fourierSpan N).orthogonalProjectionOnto : L2C →L[ℂ] fourierSpan N) :=
    isCompactOperator_of_locallyCompactSpace_dom _
  have hcomp := h.clm_comp (fourierSpan N).subtypeL
  simpa only [fourierProjection_n, Submodule.starProjection, ContinuousLinearMap.coe_comp']
    using hcomp

/-! ### L5: The Rellich compact embedding — H¹-ball is `TotallyBounded` in L² -/

/-- **L5 (Rellich compact embedding).** The set of `f ∈ L²(𝕋³; ℂ)` satisfying the H¹
predicate and the explicit energy bound `∑' k, (1 + ‖k‖²) * ‖f̂(k)‖² ≤ M²` is
totally bounded in the L² topology.  This is the Rellich compact embedding
`H¹(𝕋³; ℂ) ↪ L²(𝕋³; ℂ)` (precompactness of bounded sets).

Proof route for lean-prover (apply `Metric.totallyBounded_iff`; for each `ε > 0`):
1. Use L4 to pick `N` with `‖f - P_N f‖ ≤ ε/2` for all `f` in the H¹-ball.
2. The image `P_N '' H1-ball` lies in `fourierSpan N` and is bounded
   (`‖P_N f‖ ≤ ‖f‖ ≤ M` from norm contraction of the orthogonal projection and the
   weight ≥ 1 bound giving `‖f‖_L2 ≤ M` from L1 + H1 bound).
3. `fourierSpan N` is `ProperSpace` (finite-dimensional), hence `LocallyCompactSpace`.
   Bounded sets in `LocallyCompactSpace` normed spaces have compact closure
   (`isCompact_iff_isClosed_bounded` or `ProperSpace` directly).
4. `closure (P_N '' H1-ball)` is compact in `fourierSpan N ↪ L2C`.
5. `IsCompact.totallyBounded` gives total boundedness; extract a finite `ε/2`-net `t`.
6. For any `f` in the H¹-ball, pick `y ∈ t` with `‖P_N f - y‖ ≤ ε/2`;
   triangle inequality yields `‖f - y‖ ≤ ε`.

The construction of the finite ε-net from compactness is the hardest step; a targeted
sorry is pre-authorized there if the chaining of `Metric.totallyBounded_iff` with
`IsCompact.totallyBounded` proves awkward.

Key mathlib lemmas:
- `Metric.totallyBounded_iff`   (`Mathlib.Topology.MetricSpace.Pseudo.Basic`)
- `IsCompact.totallyBounded`    (`Mathlib.Topology.UniformSpace.Cauchy`)
- `RCLike.properSpace_submodule` + `locallyCompact_of_proper`
- `H1_ball_uniform_L2_approx` (L4 above)
- `L2C_norm_sq_eq_tsum_coeff_sq` (L1, for ‖f‖_L2 ≤ M from H1 bound) -/
theorem H1_ball_totallyBounded (M : ℝ) :
    TotallyBounded {f : L2C | memH1Torus f ∧
      ∑' k : Fin 3 → ℤ, (1 + ∑ i : Fin 3, (k i : ℝ) ^ 2) * ‖mFourierCoeff3 f k‖ ^ 2 ≤ M ^ 2} := by
  rw [Metric.totallyBounded_iff]
  intro ε hε
  -- Step 1: choose `N` from L4 so that `‖f - P_N f‖ ≤ ε/2` on the H¹-ball of radius `|M|`.
  obtain ⟨N, hN⟩ := H1_ball_uniform_L2_approx |M| (abs_nonneg M) (ε / 2) (by positivity)
  -- Every `f` in the ball is L²-bounded by `|M|` (weight ≥ 1 + Parseval).
  have hL2 : ∀ f : L2C, memH1Torus f →
      (∑' k : Fin 3 → ℤ, (1 + ∑ i : Fin 3, (k i : ℝ) ^ 2) * ‖mFourierCoeff3 f k‖ ^ 2 ≤ M ^ 2) →
      ‖f‖ ≤ |M| := by
    intro f hf hbound
    have hg_nonneg : ∀ k : Fin 3 → ℤ, 0 ≤ ‖mFourierCoeff3 f k‖ ^ 2 := fun k => by positivity
    have hle : ∀ k : Fin 3 → ℤ, ‖mFourierCoeff3 f k‖ ^ 2 ≤
        (1 + ∑ i : Fin 3, (k i : ℝ) ^ 2) * ‖mFourierCoeff3 f k‖ ^ 2 :=
      fun k => le_mul_of_one_le_left (hg_nonneg k)
        (le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => sq_nonneg _))
    have hg_sum : Summable (fun k : Fin 3 → ℤ => ‖mFourierCoeff3 f k‖ ^ 2) :=
      hf.of_nonneg_of_le hg_nonneg hle
    have hsq : ‖f‖ ^ 2 ≤ M ^ 2 := by
      rw [L2C_norm_sq_eq_tsum_coeff_sq]
      exact (Summable.tsum_le_tsum hle hg_sum hf).trans hbound
    have hs := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq_eq_abs] at hs
  -- Step 2: the compact target — image in `L2C` of the closed `|M|`-ball of the
  -- finite-dimensional (hence proper) subspace `fourierSpan N`.
  have hK : IsCompact (((fourierSpan N).subtypeL : fourierSpan N →L[ℂ] L2C) ''
      Metric.closedBall 0 |M|) :=
    (isCompact_closedBall (0 : fourierSpan N) |M|).image (fourierSpan N).subtypeL.continuous
  -- Step 3: extract a finite (ε/2)-net `t` of the compact target.
  obtain ⟨t, htfin, htcov⟩ :=
    Metric.totallyBounded_iff.mp hK.totallyBounded (ε / 2) (by positivity)
  refine ⟨t, htfin, fun f hf => ?_⟩
  obtain ⟨hf1, hf2⟩ := hf
  -- Step 4: `P_N f` lies in the compact target (membership + contraction + L² bound).
  have hPmem : fourierProjection_n N f ∈
      ((fourierSpan N).subtypeL : fourierSpan N →L[ℂ] L2C) '' Metric.closedBall 0 |M| := by
    refine ⟨⟨fourierProjection_n N f, (fourierSpan N).starProjection_apply_mem f⟩, ?_, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right, Submodule.coe_norm]
    exact le_trans ((fourierSpan N).norm_starProjection_apply_le f) (hL2 f hf1 hf2)
  -- Step 5: ε-net chaining via the triangle inequality.
  obtain ⟨y, hyt, hy⟩ := Set.mem_iUnion₂.mp (htcov hPmem)
  refine Set.mem_iUnion₂.mpr ⟨y, hyt, ?_⟩
  rw [Metric.mem_ball] at hy ⊢
  have h1 : dist f (fourierProjection_n N f) ≤ ε / 2 := by
    rw [dist_eq_norm]
    exact hN f hf1 (by rw [sq_abs]; exact hf2)
  calc dist f y ≤ dist f (fourierProjection_n N f) + dist (fourierProjection_n N f) y :=
        dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add_of_le_of_lt h1 hy
    _ = ε := by ring

/-! ### Rellich sequential form — bounded-in-H¹ sequences have L²-convergent subsequences -/

/-- **Rellich (sequential form).** Any sequence bounded in `H¹(𝕋³)` has an `L²(𝕋³)`-convergent
subsequence.  This is the form used in the Aubin–Lions / Galerkin limit-passage argument.

Proof strategy for lean-prover:
1. Let `S := {f : L2C | memH1Torus f ∧ ∑' k, (1 + ∑ i, (k i : ℝ)^2) * ‖f̂(k)‖² ≤ M²}`.
2. `S` is totally bounded: `H1_ball_totallyBounded M`.
3. `closure S` is totally bounded: `TotallyBounded.closure`.
4. `closure S` is closed, hence complete in the `CompleteSpace L2C`:
   `IsClosed.isComplete (isClosed_closure)`.
5. `closure S` is compact:
   `TotallyBounded.isCompact_of_isComplete (TotallyBounded.closure _) (isClosed_closure.isComplete)`.
6. Each `u n ∈ S ⊆ closure S` (by `subset_closure`).
7. Apply `IsCompact.tendsto_subseq` (exact mathlib name, in `Mathlib.Topology.Sequences`):
   given `hs : IsCompact (closure S)` and `hx : ∀ n, u n ∈ closure S`, it returns
   `∃ a ∈ closure S, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (u ∘ φ) atTop (𝓝 a)`.
   Destructure to get `φ`, `g`, and the `Tendsto` (the `Tendsto (u ∘ φ)` goal matches
   `Filter.Tendsto (fun n => u (φ n))` by `Function.comp`).

Key mathlib lemmas (grep-verified to exist):
- `H1_ball_totallyBounded`              (this file, L5)
- `TotallyBounded.closure`              (`Mathlib.Topology.UniformSpace.Cauchy`, line 560)
- `IsClosed.isComplete`                 (`Mathlib.Topology.UniformSpace.Cauchy`, line 447)
- `isClosed_closure`                    (`Mathlib.Topology.Closure`)
- `TotallyBounded.isCompact_of_isComplete` (`Mathlib.Topology.UniformSpace.Cauchy`, line 745)
- `subset_closure`                      (`Mathlib.Topology.Closure`)
- `IsCompact.tendsto_subseq`            (`Mathlib.Topology.Sequences`, line 298)
-/
theorem rellich_seq_compact (M : ℝ) (u : ℕ → L2C)
    (hu : ∀ n, memH1Torus (u n) ∧
      ∑' k : Fin 3 → ℤ, (1 + ∑ i : Fin 3, (k i : ℝ) ^ 2) * ‖mFourierCoeff3 (u n) k‖ ^ 2 ≤ M ^ 2) :
    ∃ (φ : ℕ → ℕ) (g : L2C), StrictMono φ ∧
      Filter.Tendsto (fun n => u (φ n)) Filter.atTop (nhds g) := by
  -- The closed H¹-ball's closure is totally bounded and complete, hence compact.
  have hcompact : IsCompact (closure {f : L2C | memH1Torus f ∧
      ∑' k : Fin 3 → ℤ, (1 + ∑ i : Fin 3, (k i : ℝ) ^ 2) * ‖mFourierCoeff3 f k‖ ^ 2 ≤ M ^ 2}) :=
    (H1_ball_totallyBounded M).closure.isCompact_of_isComplete isClosed_closure.isComplete
  -- Each `u n` lies in the ball, hence in its closure.
  have hmem : ∀ n, u n ∈ closure {f : L2C | memH1Torus f ∧
      ∑' k : Fin 3 → ℤ, (1 + ∑ i : Fin 3, (k i : ℝ) ^ 2) * ‖mFourierCoeff3 f k‖ ^ 2 ≤ M ^ 2} :=
    fun n => subset_closure (hu n)
  -- Extract a convergent subsequence by sequential compactness.
  obtain ⟨g, -, φ, hmono, htend⟩ := hcompact.tendsto_subseq hmem
  exact ⟨φ, g, hmono, htend⟩

end LerayHopf
