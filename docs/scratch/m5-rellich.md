# M5 Rellich: Fourier-tail compact embedding H¹(𝕋³) ↪ L²(𝕋³)

**Contract path:** `docs/scratch/m5-rellich.md`
**Role:** lean-planner scope document for the Rellich compact embedding on 𝕋³.
**Status:** planning (pre-implementation).
**Feeds:** M5 (Torus Fourier API), M6 (Compactness Axioms), M8 (Aubin–Lions).

---

## 0. Context and goal

The Aubin–Lions compactness argument for Navier–Stokes on 𝕋³ needs the
Rellich compact embedding `H¹(𝕋³; ℂ) ↪ L²(𝕋³; ℂ)`.  In the current
codebase:

- `L2C := Lp ℂ 2 haarTorus3` — the ambient L² space.
- `memH1Torus f := Summable (fun k => (1 + ∑ᵢ (kᵢ : ℝ)²) * ‖mFourierCoeff3 f k‖²)` — the H¹ predicate on `L2C`.
- `H1Torus := {f : L2C | memH1Torus f}` — the Sobolev set.
- `mFourierCoeff3 f k = torus3_mFourierBasis.repr f k` — exact definition; `repr : L2C ≃ₗᵢ[ℂ] ℓ²(ℤ³, ℂ)` is a linear isometry equivalence.
- `fourierBox N`, `fourierProjection_n N : L2C →L[ℂ] L2C` — Galerkin truncation to `‖k‖_∞ ≤ N`.
- `fourierProjection_n_mFourierCoeff` — proved: `(P_N f)^(k) = if k ∈ fourierBox N then f̂(k) else 0`.
- `fourierProjection_n_tendsto` — proved: `∀ f, P_N f →[atTop] f` in L²-norm.
- `fourierSpan_finiteDimensional n` — proved instance: `FiniteDimensional ℂ (fourierSpan n)`.

The goal here is the **quantitative Fourier-tail Rellich theorem** — a
precise provability classification of each ingredient, and an honest
verdict on what closes sorry-free in a single lean-coder + lean-prover run.

---

## 1. Phrasing decision: explicit-bound hypothesis vs H¹-norm space

Two strategies for the main precompactness statement (item 5):

**Strategy A (build H¹ normed space):** Define `H1Torus` as an actual
`NormedAddCommGroup` / `InnerProductSpace`, equip it with the H¹ inner
product `⟨f,g⟩_{H¹} = ∑_k (1+‖k‖²) f̂(k) conj(ĝ(k))`, and state the
compact embedding as `IsCompactOperator (inclusion : H1Torus →L[ℂ] L2C)`.
This would allow `isCompactOperator_of_tendsto` directly (since P_N ∘ i
are compact and converge to i in the H¹→L² operator norm).

**Strategy B (explicit-bound hypothesis):** Work entirely with
`f : L2C`, `memH1Torus f`, and a bound
`hM : ∑' k, (1 + ‖k‖²) * ‖mFourierCoeff3 f k‖² ≤ M²` (quantified).
State the main result as:

```lean
theorem H1_ball_totallyBounded (M : ℝ) (hM : 0 < M) :
    TotallyBounded {f : L2C | memH1Torus f ∧
      ∑' k, (1 + ∑ i, (k i : ℝ)^2) * ‖mFourierCoeff3 f k‖^2 ≤ M^2}
```

**Recommendation: Strategy B for this run.**

Rationale: Strategy A requires first building `H1Torus` as a Hilbert space
(inner product, completeness proof, norm equivalence, showing the H¹-norm
dominates the L²-norm, etc.) — substantial new infrastructure with potential
sorry-debt of its own.  Strategy B needs none of that: every step is a
computation on `mFourierCoeff3` coefficients and `Summable` / `tsum`
inequalities, all handled by existing mathlib.  The TotallyBounded form is
mathematically equivalent and is exactly the statement needed for
Aubin–Lions (the H¹-ball in L² is precompact).  Strategy A can be layered
on top later if the H¹ normed-space infrastructure is otherwise built.

---

## 2. Ordered lemma list

### L1. Parseval: `‖f‖_{L²}² = ∑' k, ‖mFourierCoeff3 f k‖²`

**Status:** PROVABLE (routine, ~10 lines).

**Exact statement:**
```lean
theorem L2C_norm_sq_eq_tsum_coeff_sq (f : L2C) :
    ‖f‖^2 = ∑' k : Fin 3 → ℤ, ‖mFourierCoeff3 f k‖^2
```

**Proof route:**
1. `torus3_mFourierBasis.repr` is a `LinearIsometryEquiv`, so
   `LinearIsometryEquiv.norm_map` gives `‖repr f‖ = ‖f‖`.
2. `repr f : ℓ²(ℤ³, ℂ) = lp (fun _ => ℂ) 2 haarTorus3`.
   `lp.norm_rpow_eq_tsum (hp : 0 < 2) (repr f)` gives
   `‖repr f‖^2 = ∑' k, ‖(repr f) k‖^2`.
3. `mFourierCoeff3 f k = (torus3_mFourierBasis.repr f) k` by definition.

Key mathlib lemmas:
- `LinearIsometryEquiv.norm_map` (in `Mathlib.Analysis.Normed.Operator.LinearIsometry`)
- `lp.norm_rpow_eq_tsum` (in `Mathlib.Analysis.Normed.Lp.LpSpace`, line 461)

**Dependency:** none beyond existing imports.

---

### L2. Tail norm identity: `‖f - P_N f‖² = ∑_{k ∉ fourierBox N} ‖f̂(k)‖²`

**Status:** PROVABLE (moderate difficulty, ~20–30 lines).

**Exact statement:**
```lean
theorem L2C_norm_sub_fourierProjection_sq (N : ℕ) (f : L2C) :
    ‖f - fourierProjection_n N f‖^2 =
      ∑' k : {k : Fin 3 → ℤ // k ∉ fourierBox N}, ‖mFourierCoeff3 f k‖^2
```

**Proof route:**
1. `mFourierCoeff3 (f - P_N f) k = mFourierCoeff3 f k - mFourierCoeff3 (P_N f) k`
   (linearity of `repr`; `map_sub`).
2. `fourierProjection_n_mFourierCoeff` (already proved) gives
   `mFourierCoeff3 (P_N f) k = if k ∈ fourierBox N then mFourierCoeff3 f k else 0`.
3. So `mFourierCoeff3 (f - P_N f) k = if k ∈ fourierBox N then 0 else mFourierCoeff3 f k`.
4. Apply L1 to `f - P_N f`, restrict the tsum to the complement of `fourierBox N`
   (the terms inside are zero).  Use `tsum_eq_tsum_of_ne_zero_bij` or split via
   `tsum_subtype` on the complement.

Key mathlib lemmas:
- `map_sub` (linearity of `repr`)
- `fourierProjection_n_mFourierCoeff` (already proved in this project)
- `L1` above
- `tsum_subtype` to restrict sum to `{k // k ∉ fourierBox N}`
- `tsum_eq_zero_of_not_summable` or pointwise-zero simp

**Friction point:** The tsum-on-complement manipulation requires care; the
`tsum` over a subtype vs the original index type needs `Summable.comp_injective`
or `tsum_subtype`.  This is standard but may take 10–15 extra lines.

---

### L3. Tail bound: `∑_{k ∉ fourierBox N} ‖f̂(k)‖² ≤ M²/(1+N²)`

**Status:** PROVABLE (routine arithmetic on `tsum`, ~20 lines).

**Exact statement:**
```lean
theorem H1_tail_bound (N : ℕ) (f : L2C)
    (hH1 : Summable (fun k : Fin 3 → ℤ => (1 + ∑ i, (k i : ℝ)^2) * ‖mFourierCoeff3 f k‖^2))
    (M : ℝ) (hM : ∑' k : Fin 3 → ℤ, (1 + ∑ i, (k i : ℝ)^2) * ‖mFourierCoeff3 f k‖^2 ≤ M^2) :
    ∑' k : {k : Fin 3 → ℤ // k ∉ fourierBox N}, ‖mFourierCoeff3 f.val k‖^2
      ≤ M^2 / (1 + (N : ℝ)^2)
```

**Mathematical argument:**
For `k ∉ fourierBox N`, there exists `i` with `|k_i| > N`, so `(k_i)² > N²`,
hence `1 + ‖k‖² ≥ 1 + N²`. Therefore:
```
(1 + N²) * ∑_{k ∉ box} ‖f̂k‖² ≤ ∑_{k ∉ box} (1+‖k‖²) * ‖f̂k‖² ≤ ∑_k (1+‖k‖²) * ‖f̂k‖² ≤ M².
```
Divide by `1 + N²`.

**Proof route:**
1. Show `∀ k ∉ fourierBox N, (1 + (N : ℝ)^2) ≤ 1 + ∑ i, (k i : ℝ)^2`.
   (Since `k ∉ fourierBox N` means `∃ i, N < |k i|`, so `(k i : ℝ)^2 > N^2`.)
   Key: `fourierBox` is `Fintype.piFinset (fun _ => Finset.Icc (-(n:ℤ)) n)`;
   negation gives `∃ i, ¬(-(N:ℤ) ≤ k i ∧ k i ≤ N)`.
2. Multiply both sides of the pointwise weight inequality by `‖f̂k‖^2` and sum.
3. Use `Summable.tsum_le_tsum` (additive translate of `Multipliable.tprod_le_tprod`,
   in `Mathlib.Topology.Algebra.InfiniteSum.Order` via `@[to_additive (attr := gcongr)]`)
   to get `(1+N²) * ∑_{k ∉ box} ‖f̂k‖² ≤ ∑_k (1+‖k‖²) * ‖f̂k‖²`.
4. Use `tsum_subtype` + monotonicity to bound the tail by the full sum.
5. Divide.

Key mathlib lemmas:
- `Summable.tsum_le_tsum` — `(h : ∀ i, f i ≤ g i) → Summable f → Summable g → ∑' f ≤ ∑' g`
  (generated by `@[to_additive]` from `Multipliable.tprod_le_tprod` in `InfiniteSum/Order.lean`)
- `tsum_subtype` to restrict sums
- Integer arithmetic to extract the `∃ i, |k i| > N` from `k ∉ fourierBox N`

**Potential friction:** The ℤ → ℝ cast arithmetic for the inequality
`∃ i, |k i| > N → (k i : ℝ)^2 > N^2` needs `Int.cast_lt`, `sq_lt_sq'`, etc.
Manageable but not trivial.

---

### L4. Uniform approximation on the H¹-ball

**Status:** PROVABLE (combines L2 + L3, ~10 lines).

**Exact statement:**
```lean
theorem H1_ball_uniform_L2_approx (M : ℝ) (hM : 0 < M) :
    ∀ ε > 0, ∃ N : ℕ, ∀ f : L2C,
      (memH1Torus f) →
      (∑' k : Fin 3 → ℤ, (1 + ∑ i, (k i : ℝ)^2) * ‖mFourierCoeff3 f k‖^2 ≤ M^2) →
      ‖f - fourierProjection_n N f‖ ≤ ε
```

**Proof route:**
1. From L2 + L3: `‖f - P_N f‖^2 ≤ M^2 / (1 + N^2)`.
2. Take `N` large enough that `M / Real.sqrt (1 + N^2) ≤ ε`
   (i.e., `N ≥ Real.sqrt (M^2/ε^2 - 1)`).
3. Apply `Real.sqrt_le_sqrt` and `Real.sqrt_sq`.

Key mathlib lemmas:
- L2, L3 above
- `Real.sqrt_le_sqrt`, `Real.sqrt_sq_eq_abs`, `sq_le_sq'` for passing between `‖f - P_N f‖` and its square

---

### L5. The compact embedding: H¹-ball is `TotallyBounded` in L²

**Status:** PROVABLE-WITH-EFFORT (requires more plumbing; honest classification
below).  Recommended disposition: **attempt sorry-free; if stuck at TotallyBounded
plumbing, mark with `-- ALLOW_SORRY: TotallyBounded ε-net construction`**.

**Exact statement:**
```lean
theorem H1_ball_totallyBounded (M : ℝ) (hM : 0 < M) :
    TotallyBounded {f : L2C | memH1Torus f ∧
      ∑' k : Fin 3 → ℤ, (1 + ∑ i, (k i : ℝ)^2) * ‖mFourierCoeff3 f k‖^2 ≤ M^2}
```

**Mathematical proof route:**

Apply `Metric.totallyBounded_iff` (in `Mathlib.Topology.MetricSpace.Pseudo.Basic`,
line 95): it suffices to show `∀ ε > 0, ∃ t : Set L2C, t.Finite ∧ H1-ball ⊆ ⋃ y ∈ t, ball y ε`.

For given ε > 0:
1. Pick `N` from L4 with `M / √(1+N²) ≤ ε/2`.
2. Let `S_N := {P_N f | f ∈ H1-ball}` = image of H1-ball under `fourierProjection_n N`.
3. `S_N ⊆ fourierSpan N` (since `P_N f ∈ fourierSpan N` by construction).
4. `S_N` is bounded: `‖P_N f‖ ≤ ‖f‖ ≤ M` (P_N is a contraction on L2C, and
   `‖f‖_L2 ≤ ‖f‖_H1 ≤ M` from the weight ≥ 1 bound).
5. `fourierSpan N` is `ProperSpace` (from `fourierSpan_finiteDimensional N`
   → `RCLike.properSpace_submodule` in `Mathlib.Analysis.RCLike.Lemmas`).
6. In a `ProperSpace`, closed bounded sets are compact
   (`isCompact_iff_isClosed_bounded`, `Mathlib.Topology.MetricSpace.Bounded`).
7. So `closure S_N` is compact in `fourierSpan N`, hence compact in L2C.
8. Compact ⟹ TotallyBounded: pick an ε/2-net `{y₁,...,yₖ}` in `S_N`.
9. For any `f` in the H1-ball: `‖f - P_N f‖ ≤ ε/2` (step 1, L4);
   pick `yⱼ` in the ε/2-net with `‖P_N f - yⱼ‖ ≤ ε/2`;
   triangle inequality gives `‖f - yⱼ‖ ≤ ε`.
10. `t = {y₁,...,yₖ}` is the required finite ε-net.

**Mathlib API needed:**

| Step | Lemma | File |
|---|---|---|
| 3 | `(fourierSpan N).starProjection_mem` or equiv | standard subspace projection |
| 4 | operator norm ≤ 1 for orthogonal projections; weight ≥ 1 for ‖f‖_L2 ≤ ‖f‖_H1 | `Submodule.norm_starProjection_le`, basic weight bound |
| 5–6 | `RCLike.properSpace_submodule`, `isCompact_iff_isClosed_bounded` | `Mathlib.Analysis.RCLike.Lemmas`, `Mathlib.Topology.MetricSpace.Bounded` |
| 7 | `IsCompact.totallyBounded` | standard |
| 8 | `Metric.totallyBounded_iff` (iff finite ε-cover) | `Mathlib.Topology.MetricSpace.Pseudo.Basic` |
| 9 | L4 above; triangle inequality | local |
| `P_N` contraction | `ContinuousLinearMap.norm_starProjection_le` or `‖P_N f‖ ≤ ‖f‖` | `Submodule.norm_starProjection_le` — need to verify this lemma name |

**Honest difficulty assessment:**

The MATHEMATICAL argument is complete and sound.  The Lean difficulty is in
steps 4 and 8–9:

- **Step 4** (`‖P_N f‖ ≤ ‖f‖`): orthogonal projections are contractions.  Mathlib has
  `orthogonalProjectionOnto_norm_le` (or similar) but the exact name for
  `(fourierSpan N).starProjection` needs verification.  The `starProjection` is
  defined as `subtypeL ∘ orthogonalProjectionOnto`, and `orthogonalProjectionOnto`
  has norm ≤ 1.  This step should be findable/provable in 10–15 lines.

- **Step 4** (`‖f‖_L2 ≤ ‖f‖_H1`): from the H1 bound and the weight `1 + ‖k‖² ≥ 1`:
  `∑' k, ‖f̂k‖² ≤ ∑' k, (1+‖k‖²) * ‖f̂k‖² ≤ M²`, so `‖f‖_L2 ≤ M`.  Routine with
  `Summable.tsum_le_tsum`.

- **Step 8–9** (constructing the finite ε-net from a compact set): mathlib's
  `IsCompact.totallyBounded` gives total boundedness; extracting an *explicit* finite
  ε-net for the ε-net argument requires going through
  `TotallyBounded.isCompact_of_isClosed` and `IsCompact.elim_nhds_subsets` or
  `Metric.totallyBounded_iff.mp hTB ε hε` to get the finite set `t`.  This is
  standard but requires chaining 3–5 API calls.  Not hard, but takes care.

**Overall verdict for L5:** This is **provable-with-effort** in mathlib.
There is no true mathematical gap — every piece has API.  The work is in
correct lemma lookup and chaining, estimated at 60–100 tactic lines for L5 alone.

**Recommendation:** Lean-prover should attempt L5 sorry-free.  If blocked
specifically at "constructing the finite ε-net from compactness of
`closure (P_N '' H1-ball)`", mark that sub-goal with:
```lean
-- ALLOW_SORRY: ε-net extraction from compact P_N-image; L4 + Heine-Borel give TotallyBounded;
--              blocked on chaining Metric.totallyBounded_iff with IsCompact.totallyBounded.
```
This isolates the frontier precisely without weakening the mathematical content.

---

## 3. `IsCompactOperator` route (alternative to TotallyBounded, for Strategy A)

If `H1Torus` is eventually built as a normed space, the compact embedding
can be stated as:

```lean
theorem H1_inclusion_isCompactOperator :
    IsCompactOperator (inclusion : H1Torus →L[ℂ] L2C)
```

**Route:**
1. For each `N`, define `finiteRankApprox N := (fourierProjection_n N).comp inclusion`.
2. `finiteRankApprox N` is compact: its range is in `fourierSpan N` (finite-dim,
   hence `LocallyCompactSpace`), and
   `isCompactOperator_of_locallyCompactSpace_dom` (mathlib) applies — here "dom"
   means the codomain is locally compact.
   Formally: `fourierProjection_n N : L2C →L[ℂ] L2C` factors as
   `subtypeL ∘ orthogonalProjectionOnto : L2C →L[ℂ] ↥(fourierSpan N) →L[ℂ] L2C`
   with `↥(fourierSpan N)` locally compact ← `isCompactOperator_of_locallyCompactSpace_dom`.
3. `finiteRankApprox N → inclusion` in the H1→L2 operator norm (from L4).
4. `isCompactOperator_of_tendsto` (mathlib) closes: compact limit of compact operators
   is compact, IF convergence is in the **operator norm topology on ContinuousLinearMap**.

**Critical note on step 3:** `fourierProjection_n_tendsto` is *pointwise* convergence
in L², NOT operator-norm convergence of `fourierProjection_n` as operators L2C→L2C.
The operator norm of `id - P_N` as L2C→L2C is 1 for all N (the projection complement
has norm 1); it does NOT converge to 0.  The relevant convergence is in the H1→L2
operator norm:
```
‖id - P_N‖_{H1→L2} = sup_{‖f‖_{H1} ≤ 1} ‖f - P_N f‖_L2 ≤ 1/√(1+N²) → 0.
```
This requires the H1-norm structure on the domain.  So Strategy A DOES add
mathematical content (the H1 operator norm), not just infrastructure.

**Verdict for the IsCompactOperator route:** Deferred to a run where `H1Torus`
is a full normed space.  For this run, Strategy B (TotallyBounded) is the right
target.

---

## 4. Compact operator status of `fourierProjection_n N`

Even without the H1-norm structure, a useful standalone lemma is:

```lean
theorem fourierProjection_n_isCompactOperator (N : ℕ) :
    IsCompactOperator (fourierProjection_n N : L2C →L[ℂ] L2C)
```

**Route (fully provable, ~20 lines):**
1. `fourierProjection_n N = (fourierSpan N).subtypeL ∘ (fourierSpan N).orthogonalProjectionOnto`.
2. `isCompactOperator_of_locallyCompactSpace_dom` applied to
   `(fourierSpan N).orthogonalProjectionOnto : L2C →L[ℂ] ↥(fourierSpan N)`:
   the codomain `↥(fourierSpan N)` is `LocallyCompactSpace` because
   `fourierSpan_finiteDimensional N` → `RCLike.properSpace_submodule` → `locallyCompact_of_proper`.
3. Then `IsCompactOperator.clm_comp h_compact (fourierSpan N).subtypeL` gives
   the compact operator conclusion.

This lemma is a useful standalone result for M5 regardless of L5's outcome, and
is fully sorry-free.

---

## 5. Ordered worklist for lean-coder and lean-prover

| # | Lemma | Owner | Provable? | Est. lines |
|---|---|---|---|---|
| L1 | `L2C_norm_sq_eq_tsum_coeff_sq` | lean-prover | Yes, routine | 15 |
| L2 | `L2C_norm_sub_fourierProjection_sq` | lean-prover | Yes, moderate | 30 |
| L3 | `H1_tail_bound` | lean-prover | Yes, routine arithmetic | 25 |
| L4 | `H1_ball_uniform_L2_approx` | lean-prover | Yes (from L2+L3) | 15 |
| L5 | `H1_ball_totallyBounded` | lean-prover | Provable-with-effort; allow precise sorry if stuck | 80–120 |
| Bonus | `fourierProjection_n_isCompactOperator` | lean-prover | Yes, routine | 20 |

**File:** `LerayHopf/RellichEmbedding.lean`

**Imports needed:**
```lean
import LerayHopf.Torus.GalerkinProjection
import LerayHopf.Torus.SobolevTorus
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Normed.Lp.LpSpace
```

---

## 6. Verdict: what closes sorry-free in this run?

| Item | Verdict |
|---|---|
| L1 Parseval | **Sorry-free.** Pure isometry + lp norm formula. |
| L2 Tail-norm identity | **Sorry-free.** Linear algebra + tsum manipulation. |
| L3 Tail bound | **Sorry-free.** tsum monotonicity + integer arithmetic. |
| L4 Uniform approximation | **Sorry-free.** Combination of L2+L3. |
| L5 TotallyBounded H¹-ball | **Attempt sorry-free; precise sorry allowed at ε-net extraction.** |
| Bonus compact projections | **Sorry-free.** |
| H1 normed space structure | **Not in scope.** Deferred to a later run. |
| IsCompactOperator on inclusion | **Not in scope** (requires H1 normed space). |
| Aubin–Lions | **Not in scope** (M8 frontier; requires Bochner/weak convergence). |

The quantitative core (L1–L4) is **fully provable sorry-free** and constitutes the
provable heart of Rellich.  L5 is the harder wrapper, provable in principle but
with a potential sorry at the ε-net extraction step if mathlib's `TotallyBounded`
API proves awkward.  Even with that sorry, the `-- ALLOW_SORRY` marker will be
pinned to the exact ε-net step, not to the mathematical argument itself.

---

## 7. Mathematical integrity notes

- **No sorry-free theorem weakens the statement.** Each `Hᵢ` is proved for `f :
  L2C` with `memH1Torus f` and an explicit real bound on the H¹ sum — not for a
  trivially satisfied predicate.
- **The tail bound is the quantitative core**: it does NOT use any axiom beyond
  `Summable.tsum_le_tsum` and integer arithmetic.
- **The compact embedding (L5) does NOT need Aubin–Lions** as input; it IS one
  of the inputs Aubin–Lions will use.  The dependency is:
  `L1–L4 → L5 → (M6 compactness axiom discharge) → M8 Aubin–Lions`.
- The `fourierProjection_n_isCompactOperator` bonus strengthens the M3 Galerkin
  API without requiring any new infrastructure.

---

## 8. Recommended first lean-coder task

**Create `LerayHopf/RellichEmbedding.lean`** with:
1. Module docstring citing this plan.
2. Statements (with bodies left for lean-prover) in order L1 → L2 → L3 → L4 →
   `fourierProjection_n_isCompactOperator` → L5.
3. All `sorry`s marked `-- ALLOW_SORRY: <reason>` per AGENTS.md rule 7.
4. Lean-prover then fills bodies in order.

The lean-prover should prioritize L1–L4 + Bonus (all routine), then attempt L5.
L5 is the only item where a marked sorry is pre-authorized.
