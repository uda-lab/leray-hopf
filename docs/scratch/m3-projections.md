# M3 Task Contract: Galerkin Projection Pₙ + Leray Projection Π_div

**Milestone:** M3 — "Galerkin projection Pₙ + Leray projection Π_div (Fourier multipliers)"
**Scope:** `milestone.md` M5 territory, building directly on M2 deliverables.
**Planner:** lean-planner · 2026-06-10
**Status of M2:** done (axiom-free). M1 spine in progress but does not block M3.

---

## 0. What M2 already provides (the starting point)

The following are axiom-free and in the tree:

| M2 item | Location | Type |
|---|---|---|
| `L2VF` | `FunctionSpaces.lean` | `abbrev L2VF := Lp VelocityValue 2 haarTorus3` |
| `L2C` | `FunctionSpaces.lean` | `abbrev L2C := Lp ℂ 2 haarTorus3` |
| `torus3_mFourierBasis` | `FunctionSpaces.lean` | `HilbertBasis (Fin 3 → ℤ) ℂ L2C` |
| `mFourierCoeff3` | `FunctionSpaces.lean` | `L2C → (Fin 3 → ℤ) → ℂ` (= `torus3_mFourierBasis.repr f k`) |
| `L2VF_projComponentC j` | `DivergenceFree.lean` | `L2VF →L[ℝ] L2C` |
| `DivFreeL2` | `DivergenceFree.lean` | `Prop`-valued predicate on `L2VF` |
| `divSymbol k` | `Leray.lean` | `L2VF →L[ℝ] ℂ` |
| `L2Sigma` | `Leray.lean` | `Submodule ℝ L2VF` (= `⨅ k, ker (divSymbol k)`) |
| `mem_L2Sigma_iff` | `Leray.lean` | `u ∈ L2Sigma ↔ DivFreeL2 u` |
| `isClosed_L2Sigma` | `Leray.lean` | `IsClosed (L2Sigma : Set L2VF)` |
| `memH1Torus`, `H1Torus` | `SobolevTorus.lean` | membership predicate + set in `L2C` |

Key instances that hold automatically on `L2VF` (all from mathlib, verified in M2):
`InnerProductSpace ℝ L2VF`, `CompleteSpace L2VF`.

---

## 1. Decision points for the orchestrator (resolve before coding)

### Decision 1-A — Galerkin truncation norm: ‖k‖_∞ vs ‖k‖₂

Two natural truncation sets for wavenumber `k : Fin 3 → ℤ`:

**(a) ‖k‖_∞ ≤ n:** `∀ i, |k i| ≤ n`.
Finset: `Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-n : ℤ) n)`.
Clean `Finset (Fin 3 → ℤ)` construction. `Fintype.mem_piFinset` gives membership. The set is the coordinate-aligned cube `[-n,n]³`. Standard in Fourier–Galerkin PDE literature.

**(b) ‖k‖₂² ≤ n²:** `∑ i, (k i)² ≤ n²`.
Finset: `Finset.filter (fun k => ∑ i, (k i)^2 ≤ n^2) (Fintype.piFinset (fun _ => Finset.Icc (-n : ℤ) n))`.
Rotationally symmetric but slightly harder to work with in `Finset` combinatorics.

**Recommendation: use ‖k‖_∞.** The cube gives a `Fintype` via `Fintype.piFinset` immediately without a filter step. The convergence proof (D-14) needs the truncation sets to be `Finset.atTop`-cofinal, which is easier to verify for the cube. ‖k‖_∞ and ‖k‖₂ give the same limit (both exhaust ℤ³), so neither is analytically stronger.

**Orchestrator must confirm one of:** (a) ‖k‖_∞ cube (recommended), (b) ‖k‖₂ ball, (c) other.

### Decision 1-B — Galerkin projection domain: on L2C first, then lift to L2VF

Two routes for `Pₙ`:

**(Route C)** Define `fourierProjection_n n : L2C →L[ℂ] L2C` using `torus3_mFourierBasis`. Then define the velocity-field version `velocityProjection_n n : L2VF →L[ℝ] L2VF` componentwise via `L2VF_projComponentC`.

**(Route V)** Define `Pₙ` directly on `L2VF` using a basis for `L2VF`. This requires constructing a vector-valued Hilbert basis from `torus3_mFourierBasis` via the `EuclideanSpace ℝ (Fin 3)` structure — a non-trivial construction (the tensor product of a Hilbert basis with an orthonormal basis of `VelocityValue`).

**Recommendation: Route C.** Route V needs an additional tensor-product-of-Hilbert-bases result that is not directly in mathlib. Route C keeps the Fourier work on `L2C` where the machinery already exists and lifts componentwise — exactly as `divSymbol` did in M2. The convergence proof on `L2C` (D-14) lifts to `L2VF` by applying it to each component.

**Orchestrator must confirm one of:** (a) Route C component-wise (recommended), (b) Route V direct on L2VF.

---

## 2. File layout

```text
LerayHopf/
  Leray.lean         ← EDIT: add lerayProjection + properties (D-16 through D-21)
  GalerkinProjection.lean  ← NEW: fourierProjection_n + velocityProjection_n + convergence (D-22 through D-30)
```

`Leray.lean` already imports `DivergenceFree.lean`; the new declarations append after `isClosed_L2Sigma`. No structural change to the import chain is needed.

`GalerkinProjection.lean` imports `Leray.lean` (which transitively imports everything from M2).

---

## 3. Declaration list, ordered by dependency

### Group A: Leray projection Π_div (in `Leray.lean`)

**D-15 · `L2Sigma.completeSpace`** — follows-from-mathlib (instance, no proof body needed)

```lean
/-- L²_σ(𝕋³) is complete: it is a closed submodule of the complete space L2VF. -/
instance : CompleteSpace L2Sigma :=
  isClosed_L2Sigma.completeSpace_coe
```

Mathlib path (grep-verified):
- `isClosed_L2Sigma : IsClosed (L2Sigma : Set L2VF)` — already in `Leray.lean`
- `IsClosed.completeSpace_coe [CompleteSpace α] [IsClosed s] : CompleteSpace s`
  — `Mathlib/Topology/UniformSpace/UniformEmbedding.lean:320`
- `CompleteSpace L2VF` — from `Lp.instCompleteSpace` (in M2)

Tag: **follows-from-mathlib** (one-line instance declaration). No sorry.

---

**D-16 · `L2Sigma.hasOrthogonalProjection`** — follows-from-mathlib (instance, no proof body needed)

```lean
/-- L²_σ(𝕋³) has an orthogonal projection from L2VF. -/
instance : L2Sigma.HasOrthogonalProjection :=
  HasOrthogonalProjection.ofCompleteSpace L2Sigma
```

Mathlib path (grep-verified):
- `HasOrthogonalProjection.ofCompleteSpace [CompleteSpace K] : K.HasOrthogonalProjection`
  — `Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean:53`
  (instance with priority 100; will fire from `L2Sigma.completeSpace`)

In practice both D-15 and D-16 may be discharged by a single `inferInstance` call once the `IsClosed` + `CompleteSpace L2VF` chain is in scope. The coder may combine them as one `example : L2Sigma.HasOrthogonalProjection := inferInstance`.

Tag: **follows-from-mathlib**. No sorry.

---

**D-17 · `lerayProjection`** — must-prove (definition + type ascription)

```lean
/-- The Leray projection Π_div : L2VF →L[ℝ] L2Sigma.
The orthogonal projection onto the closed divergence-free subspace L²_σ(𝕋³).
This is the Leray–Hodge projection; its range is exactly L²_σ. -/
noncomputable def lerayProjection : L2VF →L[ℝ] L2Sigma :=
  L2Sigma.orthogonalProjectionOnto
```

Exact mathlib name (grep-verified):
`Submodule.orthogonalProjectionOnto : E →L[𝕜] K` (given `[K.HasOrthogonalProjection]`)
— `Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean:143`

Note: `orthogonalProjection` (the old name) is deprecated since 2026-05-05 in favour of
`orthogonalProjectionOnto`. Use the new name.

The coercion `L2VF →L[ℝ] L2VF` version (for PDE use) is `L2Sigma.subtypeL ∘L lerayProjection`,
or equivalently `L2Sigma.starProjection : L2VF →L[ℝ] L2VF`. Both are available from mathlib.

Tag: **must-prove** (definition must elaborate). No sorry if D-15/D-16 are instances.

---

**D-18 · `lerayProjection_idempotent`** — follows-from-mathlib

```lean
/-- The Leray projection is idempotent: applying it twice equals applying it once. -/
theorem lerayProjection_idempotent :
    IsIdempotentElem L2Sigma.starProjection :=
  L2Sigma.isIdempotentElem_starProjection
```

Mathlib path (grep-verified):
`Submodule.isIdempotentElem_starProjection : IsIdempotentElem K.starProjection`
— `Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean:287`

The `starProjection` version (mapping `L2VF → L2VF`) is more useful for ODE purposes. The `orthogonalProjectionOnto` version maps into the subtype `L2Sigma`; they are related by `subtypeL`.

Tag: **follows-from-mathlib** (one-liner).

---

**D-19 · `lerayProjection_fixes_divFree`** — follows-from-mathlib

```lean
/-- The Leray projection fixes divergence-free fields: Π_div u = u ↔ u ∈ L²_σ. -/
theorem lerayProjection_fixes_divFree (u : L2VF) :
    L2Sigma.starProjection u = u ↔ u ∈ L2Sigma :=
  L2Sigma.starProjection_eq_self_iff
```

Mathlib path (grep-verified):
`Submodule.starProjection_eq_self_iff : K.starProjection v = v ↔ v ∈ K`
— `Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean:279`

Tag: **follows-from-mathlib** (one-liner).

---

**D-20 · `lerayProjection_range`** — follows-from-mathlib

```lean
/-- The range of the Leray projection (as E → E map) is L²_σ. -/
theorem lerayProjection_range :
    L2Sigma.starProjection.range = L2Sigma :=
  L2Sigma.range_starProjection
```

Mathlib path (grep-verified):
`Submodule.range_starProjection : U.starProjection.range = U`
— `Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean:291`

Tag: **follows-from-mathlib** (one-liner).

---

**D-21 · `lerayProjection_isSymmetric`** — follows-from-mathlib

```lean
/-- The Leray projection is self-adjoint (symmetric as a linear map on L2VF). -/
theorem lerayProjection_isSymmetric :
    L2Sigma.starProjection.IsSymmetric :=
  L2Sigma.starProjection_isSymmetric
```

Mathlib path (grep-verified):
`Submodule.starProjection_isSymmetric [K.HasOrthogonalProjection] : K.starProjection.IsSymmetric`
— `Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean:645`

The full self-adjointness `IsSelfAdjoint` follows from `U.starProjection_isSymmetric.isSelfAdjoint`
via `Mathlib/Analysis/InnerProductSpace/Adjoint.lean:375`. Include if needed for M4.

Tag: **follows-from-mathlib** (one-liner).

**D-21b · `lerayProjection_norm_le`** — follows-from-mathlib

```lean
/-- The Leray projection has operator norm ≤ 1. -/
theorem lerayProjection_norm_le : ‖L2Sigma.starProjection‖ ≤ 1 :=
  L2Sigma.starProjection_norm_le
```

Mathlib path (grep-verified):
`Submodule.starProjection_norm_le : ‖K.starProjection‖ ≤ 1`
— `Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean:374`

Tag: **follows-from-mathlib** (one-liner).

---

### Group B: Galerkin projection Pₙ (new file `GalerkinProjection.lean`)

**D-22 · `fourierBox`** — must-prove (small definition)

```lean
/-- The finite set of wavenumbers k ∈ ℤ³ with ‖k‖_∞ ≤ n (the Galerkin truncation cube).
    `fourierBox n = {k : Fin 3 → ℤ | ∀ i, |k i| ≤ n}` as a `Finset`. -/
def fourierBox (n : ℕ) : Finset (Fin 3 → ℤ) :=
  Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-(n : ℤ)) n)
```

Mathlib paths (grep-verified):
- `Fintype.piFinset : (∀ a, Finset (δ a)) → Finset (∀ a, δ a)`
  — `Mathlib/Data/Fintype/Pi.lean:33`
- `Fintype.mem_piFinset : f ∈ piFinset t ↔ ∀ a, f a ∈ t a`
  — `Mathlib/Data/Fintype/Pi.lean:37`
- `Finset.Icc (a b : ℤ)` is a `Finset ℤ` by `instLocallyFiniteOrder`
  — `Mathlib/Data/Int/Interval.lean:29`

Tag: **must-prove** (computable definition; typecheck must succeed). No sorry.

---

**D-23 · `fourierBox_monotone`** — must-prove (small)

```lean
theorem fourierBox_monotone : Monotone fourierBox := by
  intro m n hmn k hk
  simp only [fourierBox, Fintype.mem_piFinset, Finset.mem_Icc] at *
  intro i
  exact ⟨Int.neg_le_neg (Int.ofNat_le.mpr hmn) |>.trans (hk i).1,
         (hk i).2.trans (Int.ofNat_le.mpr hmn)⟩
```

Needed to apply `starProjection_tendsto_self` (D-29).

Tag: **must-prove** (small). No sorry.

---

**D-24 · `fourierBox_exhausts`** — must-prove (small)

```lean
/-- The union of fourierBox n over all n is all of (Fin 3 → ℤ). -/
theorem fourierBox_exhausts : ∀ k : Fin 3 → ℤ, ∃ n : ℕ, k ∈ fourierBox n := by
  intro k
  use (Finset.univ.sup (fun i => (k i).natAbs))
  simp [fourierBox, Fintype.mem_piFinset, Finset.mem_Icc, Int.le_natAbs]
  -- for each i, -(max over i of |k i|) ≤ k i ≤ max over i of |k i|
  intro i
  constructor
  · exact Int.neg_le_of_natAbs_le (Finset.le_sup (f := fun i => (k i).natAbs) (Finset.mem_univ i))
  · exact Int.le_natAbs.trans (Int.ofNat_le.mpr (Finset.le_sup (Finset.mem_univ i)))
```

This is needed to verify that `⨆ n, fourierSpan n` is dense in `L2C` (D-28).

Tag: **must-prove** (small, may need a few lemmas about `Int.natAbs`). No sorry.

---

**D-25 · `fourierSpan`** — scaffold-only

```lean
/-- The finite-dimensional subspace of L²(𝕋³;ℂ) spanned by Fourier modes with
    wavenumber in fourierBox n. -/
noncomputable def fourierSpan (n : ℕ) : Submodule ℂ L2C :=
  Submodule.span ℂ (Set.range (fun k : fourierBox n => torus3_mFourierBasis k.val))
```

Alternative: `Submodule.span ℂ ((torus3_mFourierBasis ∘ Subtype.val) '' Set.univ)` for `k : fourierBox n`.

Tag: **scaffold-only** (definition must compile; no properties proved here except instance checks).

---

**D-26 · `fourierSpan_finiteDimensional`** — follows-from-mathlib

```lean
instance (n : ℕ) : FiniteDimensional ℂ (fourierSpan n) :=
  -- span of a Finset-indexed set is FiniteDimensional
  FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
```

Mathlib path (grep-verified):
`FiniteDimensional.span_of_finite {A : Set V} (hA : Set.Finite A) : FiniteDimensional K (span K A)`
— `Mathlib/LinearAlgebra/FiniteDimensional/Defs.lean:200`

`Set.finite_range _` applies since `fourierBox n` is a `Fintype`.

Tag: **follows-from-mathlib** (one-liner). No sorry.

---

**D-27 · `fourierSpan_completeSpace`** — follows-from-mathlib (instance)

```lean
instance (n : ℕ) : CompleteSpace (fourierSpan n) :=
  Submodule.complete_of_finiteDimensional (fourierSpan n)
```

Mathlib path (grep-verified):
`Submodule.complete_of_finiteDimensional [FiniteDimensional 𝕜 s] : CompleteSpace s`
— `Mathlib/Topology/Algebra/Module/FiniteDimension.lean:519`

Transitively uses `FiniteDimensional.complete` which uses `completeSpace_coe_iff_isComplete`.

Tag: **follows-from-mathlib** (one-liner).

---

**D-28 · `fourierSpan_iSup_dense`** — must-prove (mathematical content; medium difficulty)

```lean
/-- The union of the Fourier span submodules is dense in L²(𝕋³; ℂ).
    This is what allows the convergence D-29. -/
theorem fourierSpan_iSup_dense :
    ⊤ ≤ (⨆ n : ℕ, fourierSpan n).topologicalClosure := by
  -- The Hilbert basis vectors span a dense set (HilbertBasis.dense_span).
  -- Each basis vector torus3_mFourierBasis k belongs to fourierSpan n for n sufficiently large
  -- (by fourierBox_exhausts). Hence the iSup contains all basis vectors,
  -- and its closure is ⊤ (by HilbertBasis.dense_span).
  sorry -- ALLOW_SORRY: needs HilbertBasis.dense_span + fourierBox_exhausts; medium difficulty
```

Mathlib lemmas needed:
- `HilbertBasis.dense_span (b : HilbertBasis ι 𝕜 E) : Dense (span 𝕜 (Set.range b) : Set E)`
  — `Mathlib/Analysis/InnerProductSpace/l2Space.lean:444`
- `Submodule.topologicalClosure_mono` or `le_iSup_of_le` to chain submodule inclusions.

The argument: every basis vector `torus3_mFourierBasis k` lies in `fourierSpan n` for
`n ≥ max_i |k_i|` (by `fourierBox_exhausts`). Hence every basis vector lies in `⨆ n, fourierSpan n`.
Since the basis spans densely (by `dense_span`), the closure is `⊤`.

This is a genuine proof — not hard, but requires connecting `HilbertBasis.dense_span` to the
increasing `iSup`. The prover should use `HilbertBasis.dense_span` + monotone `iSup` + the
`Set.range ⊆ ⨆ fourierSpan` inclusion.

**Gap:** The `Submodule.span_iUnion` / `iSup_span_eq` lemma connecting
`⨆ n, span (image of fourierBox n)` to `span (⋃ n, image of fourierBox n)` needs to be
checked. Mathlib has `Submodule.span_iUnion` but the direction needed here is
`span (⋃ i, s i) = ⨆ i, span (s i)` — confirmed in `Submodule.span_iUnion`.

Tag: **must-prove** with marked sorry until D-23/D-24 are finalized. Medium difficulty. Flag for Codex review.

---

**D-29 · `fourierProjection_n`** — must-prove (definition)

```lean
/-- The n-th Galerkin projection: the orthogonal projection of L²(𝕋³; ℂ)
    onto the finite-dimensional subspace `fourierSpan n`. -/
noncomputable def fourierProjection_n (n : ℕ) : L2C →L[ℂ] L2C :=
  (fourierSpan n).subtypeL ∘L (fourierSpan n).orthogonalProjectionOnto
```

This uses `(fourierSpan n).orthogonalProjectionOnto : L2C →L[ℂ] fourierSpan n`
(available since `fourierSpan n` has `HasOrthogonalProjection` from D-27 + D-16's pattern)
composed with `(fourierSpan n).subtypeL : fourierSpan n →L[ℂ] L2C`.

Equivalently, `(fourierSpan n).starProjection`.

**Alternative explicit sum formula** (equivalent, useful for computation):

```lean
noncomputable def fourierProjection_n_sum (n : ℕ) (f : L2C) : L2C :=
  ∑ k ∈ fourierBox n, torus3_mFourierBasis.repr f k • torus3_mFourierBasis k
```

This is the explicit partial sum, with the same value by `HilbertBasis.hasSum_repr`.
The projection version is cleaner for properties; the sum version is cleaner for estimates.
The coder should define the projection version and prove the sum formula as a lemma.

Tag: **must-prove** (definition). No sorry once D-25–D-27 are in place.

---

**D-30 · `fourierProjection_n_tendsto`** — must-prove (D-14 from M2 contract, now in scope)

```lean
/-- The Galerkin projections Pₙ converge to the identity in L²(𝕋³; ℂ). -/
theorem fourierProjection_n_tendsto (f : L2C) :
    Filter.Tendsto (fun n => fourierProjection_n n f) Filter.atTop (nhds f) := by
  -- Use starProjection_tendsto_self applied to U n = fourierSpan n.
  -- Hypotheses needed:
  --   (i)  Monotone fourierSpan  (from D-23)
  --   (ii) ∀ n, (fourierSpan n).HasOrthogonalProjection  (from D-27)
  --   (iii) ⊤ ≤ (⨆ n, fourierSpan n).topologicalClosure  (from D-28)
  apply Submodule.starProjection_tendsto_self
  · exact fourierSpan_monotone     -- need D-30a
  · exact fourierSpan_iSup_dense   -- D-28
```

Mathlib lemma (grep-verified):
`Submodule.starProjection_tendsto_self {U : ι → Submodule 𝕜 E} [∀ t, (U t).HasOrthogonalProjection]
    (hU : Monotone U) (x : E) (hU' : ⊤ ≤ (⨆ t, U t).topologicalClosure) :
    Filter.Tendsto (fun t => (U t).starProjection x) atTop (𝓝 x)`
— `Mathlib/Analysis/InnerProductSpace/Projection/Submodule.lean:146`

This is the primary convergence engine. The three hypotheses are:
- (i) `fourierSpan_monotone` (new lemma, easy from `fourierBox_monotone`),
- (ii) `[∀ n, (fourierSpan n).HasOrthogonalProjection]` (instance, from D-27),
- (iii) `fourierSpan_iSup_dense` (D-28, the only non-trivial one).

Tag: **must-prove** with marked sorry until D-28 is proved. Once D-28 is done, this should
be nearly immediate (applying `starProjection_tendsto_self`).

**Subsidiary D-30a · `fourierSpan_monotone`** — must-prove (small)

```lean
theorem fourierSpan_monotone : Monotone (fun n => fourierSpan n) := by
  intro m n hmn
  apply Submodule.span_mono
  apply Set.image_subset_image
  intro k hk
  simp only [fourierBox, Fintype.mem_piFinset, Finset.mem_Icc] at *
  intro i; exact ⟨(Int.ofNat_le.mpr (Nat.le_of_lt_succ (Nat.lt_succ_of_le hmn))).neg_left.trans (hk i).1,
                  (hk i).2.trans (Int.ofNat_le.mpr hmn)⟩
```

(Exact proof will be worked out by lean-coder/prover; sketch is correct.)

Tag: **must-prove** (small, ~5 lines). No sorry.

---

### Group C: Velocity-field Galerkin projection on L2VF

**D-31 · `velocityProjection_n`** — must-prove (definition)

```lean
/-- The n-th Galerkin projection on L²(𝕋³; ℝ³), acting componentwise.
    Each real component is embedded into L2C, projected by fourierProjection_n,
    and the result is reassembled. -/
noncomputable def velocityProjection_n (n : ℕ) : L2VF →L[ℝ] L2VF :=
  sorry -- ALLOW_SORRY: componentwise reassembly needs L2VF component reconstruction CLM
```

The construction: `v ↦ ∑ j : Fin 3, Re(fourierProjection_n n (L2VF_projComponentC j v)) • eⱼ`
where `eⱼ` is the `j`-th standard basis vector in `VelocityValue`.
This requires a CLM `Lp ℝ 2 haarTorus3 →L[ℝ] L2VF` for each component (the adjoint of `L2VF_projComponent j`).

**Gap analysis:** The "inject a scalar L² function into the j-th component of L2VF" CLM requires
constructing `(·, 0, 0)` etc. as continuous linear maps at the `Lp` level. This is analogous to
`L2VF_projComponentC` (already built in M2) but in reverse. It is buildable via
`ContinuousLinearMap.compLpL` with the injection `ℝ → EuclideanSpace ℝ (Fin 3)` for coordinate j.
The injection map for coordinate j is `EuclideanSpace.single j (1 : ℝ) : ℝ → EuclideanSpace ℝ (Fin 3)`,
concretely `x ↦ EuclideanSpace.single j x`.

This is genuine work (~15 lines). Mark with `-- ALLOW_SORRY: componentwise injection CLM`.

Tag: **must-prove** with marked sorry. Medium difficulty. Codex review recommended on statement.

---

**D-32 · `velocityProjection_n_tendsto`** — must-prove

```lean
/-- The velocity Galerkin projections converge to the identity in L²(𝕋³; ℝ³). -/
theorem velocityProjection_n_tendsto (u : L2VF) :
    Filter.Tendsto (fun n => velocityProjection_n n u) Filter.atTop (nhds u) := by
  sorry -- ALLOW_SORRY: follows from fourierProjection_n_tendsto componentwise; D-30 + D-31 needed
```

Once D-30 and D-31 are sorry-free, this follows from the componentwise convergence argument.

Tag: **must-prove** with marked sorry until D-30/D-31 done.

---

### Group D: Pₙ preserves L²_σ (needed for M4 Galerkin ODE setup)

**D-33 · `velocityProjection_preserves_L2Sigma`** — must-prove (the key compatibility lemma)

```lean
/-- The Galerkin projection Pₙ maps L²_σ(𝕋³) into itself: if u is divergence-free,
    so is Pₙ u. -/
theorem velocityProjection_preserves_L2Sigma (n : ℕ) (u : L2VF) (hu : u ∈ L2Sigma) :
    velocityProjection_n n u ∈ L2Sigma := by
  sorry -- ALLOW_SORRY: needs characterization of Pₙ via Fourier modes + mem_L2Sigma_iff
```

**Mathematical argument:** `u ∈ L2Sigma ↔ DivFreeL2 u ↔ ∀ k, ∑ j (k j : ℂ) * û_j(k) = 0`.
`Pₙ u` has Fourier coefficients `(P̂ₙu)_j(k) = û_j(k)` for `‖k‖_∞ ≤ n` and `0` otherwise.
The div-free condition for `Pₙ u` is then `∀ k, ∑ j (k j : ℂ) * (P̂ₙu)_j(k) = 0`, which holds
because: for `k ∈ fourierBox n` this equals `∑ j (k j : ℂ) * û_j(k) = 0` (from `DivFreeL2 u`);
for `k ∉ fourierBox n` it equals `0 = 0`.

**Gap:** Proving that `mFourierCoeff3 (L2VF_projComponentC j (velocityProjection_n n u)) k`
equals `mFourierCoeff3 (L2VF_projComponentC j u) k` for `k ∈ fourierBox n` and `0` otherwise.
This requires showing that `fourierProjection_n n` commutes with component extraction — i.e., that
`L2VF_projComponentC j ∘L velocityProjection_n n = fourierProjection_n n ∘L L2VF_projComponentC j`
(by the componentwise definition of `velocityProjection_n`).
This commutativity is true by design of D-31 but needs to be proved explicitly.

**Difficulty:** Medium. Requires the explicit sum formula for `fourierProjection_n_sum` and the
Fourier coefficient linearity. Not hard once D-29/D-31 have good API, but non-trivial.

Tag: **must-prove** with marked sorry. Flag for Codex review.

---

**D-34 · `velocityProjection_leray_commute`** — follows-from-D-33 + starProjection API

```lean
/-- The Galerkin and Leray projections commute:
    Π_div ∘ Pₙ = Pₙ ∘ Π_div = Pₙ ↾ L²_σ. -/
theorem velocityProjection_leray_commute (n : ℕ) :
    L2Sigma.starProjection ∘L velocityProjection_n n =
      velocityProjection_n n ∘L L2Sigma.starProjection := by
  sorry -- ALLOW_SORRY: follows from D-33 + starProjection_comp_starProjection_of_le; medium
```

Mathematical content: Let `Vₙ = image of velocityProjection_n n` and `Σ = L2Sigma`. Since `Pₙ`
maps `Σ → Σ∩Vₙ` (by D-33 and `Pₙ² = Pₙ`), the commutation follows from the general identity
for projections onto nested subspaces. Alternatively: both sides act as `Pₙ` on `L2Sigma` and as
`0` on `L2Sigma^⊥` (for the left side) or the same (for the right side) — requires care.

**Honest assessment:** This is somewhat subtle. If the Galerkin space `Vₙ` is not itself
contained in `L2Sigma` (it might contain non-div-free modes), the commutation is not obvious.
The correct statement for M4's ODE needs `Pₙ` restricted to `L2Sigma`, i.e. the projection onto
`Vₙ ∩ L2Sigma`. This is the **Galerkin + Leray projection** used in the classical proof.

**Recommendation for the orchestrator:** For M4, it suffices to define the restricted projection
`gallerkinLerayProjection_n n : L2Sigma →L[ℝ] (Vₙ ∩ L2Sigma)` directly, rather than proving
commutativity abstractly. The commutativity can be deferred. Mark D-34 with `-- TODO:` describing
this decision point and record it in STATUS.md.

Tag: **must-prove** with marked sorry. Decision point: whether to prove commutativity or define
the restricted projection directly. Flag for orchestrator decision.

---

## 4. Dependency graph

```
M2 (isClosed_L2Sigma, torus3_mFourierBasis, L2VF_projComponentC)
  │
  ├─ D-15 (CompleteSpace L2Sigma)
  │    └─ D-16 (HasOrthogonalProjection L2Sigma)
  │         └─ D-17 (lerayProjection definition)
  │              ├─ D-18 (idempotent)           [all follow-from-mathlib]
  │              ├─ D-19 (fixes div-free)
  │              ├─ D-20 (range = L2Sigma)
  │              ├─ D-21 (self-adjoint)
  │              └─ D-21b (norm ≤ 1)
  │
  └─ D-22 (fourierBox)
       ├─ D-23 (fourierBox_monotone)
       ├─ D-24 (fourierBox_exhausts)
       └─ D-25 (fourierSpan)
            ├─ D-26 (FiniteDimensional)
            ├─ D-27 (CompleteSpace)
            ├─ D-28 (dense iSup)  ← D-23 + D-24 + HilbertBasis.dense_span
            │    └─ D-30a (fourierSpan_monotone)
            │         └─ D-29 (fourierProjection_n definition)
            │              └─ D-30 (fourierProjection_n_tendsto)  ← D-28 + D-29 + D-30a
            └─ D-31 (velocityProjection_n)
                 ├─ D-32 (velocityProjection_n_tendsto)  ← D-30 + D-31
                 └─ D-33 (preserves L2Sigma)
                      └─ D-34 (Pₙ ∘ Π_div commutation)
```

Parallelism: Group A (D-15 through D-21b) and Group B/C up to D-27 can proceed in parallel
once M2 is confirmed built. D-28 is the critical path item.

---

## 5. Verified mathlib blocks

| Item | Mathlib path | Status |
|---|---|---|
| `IsClosed.completeSpace_coe` | `Topology/UniformSpace/UniformEmbedding.lean:320` | **grep-verified** |
| `HasOrthogonalProjection.ofCompleteSpace` | `Analysis/InnerProductSpace/Projection/Basic.lean:53` | **grep-verified** |
| `Submodule.orthogonalProjectionOnto` | `Analysis/InnerProductSpace/Projection/Basic.lean:143` | **grep-verified** |
| `Submodule.starProjection` | `Analysis/InnerProductSpace/Projection/Basic.lean:185` | **grep-verified** |
| `Submodule.isIdempotentElem_starProjection` | `Analysis/InnerProductSpace/Projection/Basic.lean:287` | **grep-verified** |
| `Submodule.starProjection_eq_self_iff` | `Analysis/InnerProductSpace/Projection/Basic.lean:279` | **grep-verified** |
| `Submodule.range_starProjection` | `Analysis/InnerProductSpace/Projection/Basic.lean:291` | **grep-verified** |
| `Submodule.starProjection_isSymmetric` | `Analysis/InnerProductSpace/Projection/Basic.lean:645` | **grep-verified** |
| `Submodule.starProjection_norm_le` | `Analysis/InnerProductSpace/Projection/Basic.lean:374` | **grep-verified** |
| `Submodule.starProjection_tendsto_self` | `Analysis/InnerProductSpace/Projection/Submodule.lean:146` | **grep-verified** |
| `HilbertBasis.dense_span` | `Analysis/InnerProductSpace/l2Space.lean:444` | **grep-verified** |
| `HilbertBasis.hasSum_repr` | `Analysis/InnerProductSpace/l2Space.lean:440` | **grep-verified** |
| `FiniteDimensional.span_of_finite` | `LinearAlgebra/FiniteDimensional/Defs.lean:200` | **grep-verified** |
| `Submodule.complete_of_finiteDimensional` | `Topology/Algebra/Module/FiniteDimension.lean:519` | **grep-verified** |
| `Fintype.piFinset` | `Data/Fintype/Pi.lean:33` | **grep-verified** |
| `instLocallyFiniteOrder` for ℤ | `Data/Int/Interval.lean:29` | **grep-verified** |
| `orthogonalProjection` (old name) deprecated 2026-05-05 | `Projection/Basic.lean:172` | **grep-verified — use `orthogonalProjectionOnto`** |

---

## 6. Gaps to build (not in mathlib)

| Gap | Severity | Plan |
|---|---|---|
| `fourierBox`, `fourierBox_monotone`, `fourierBox_exhausts` | Must build | Small; ℤ-interval arithmetic |
| `fourierSpan` as submodule of `L2C` | Must build | ~5 lines, uses `Submodule.span` |
| `fourierSpan_iSup_dense` (D-28) | Must prove | Medium; uses `HilbertBasis.dense_span` + `span_iUnion` |
| `fourierProjection_n` definition (D-29) | Must build | ~3 lines once D-25–D-27 done |
| Componentwise injection CLM `ℝ →_Lp_j VelocityValue` | Must build | ~10 lines; needed for D-31 |
| `velocityProjection_n` (D-31) componentwise reassembly | Must build | ~10 lines |
| `velocityProjection_preserves_L2Sigma` (D-33) | Must prove | Medium; Fourier arithmetic |
| `velocityProjection_leray_commute` (D-34) | Decision point | See §3 Group D note |

No analytic axioms are needed for M3. All gaps are structural/computational, not
research-level PDE mathematics. The only genuine proof obligation is D-28 (density of
the iSup), which is a Fourier-analytic fact that follows entirely from `HilbertBasis.dense_span`
once the index set exhaustion (D-24) is established.

---

## 7. Sorry frontier for M3

| ID | Location | Content | Blocker |
|---|---|---|---|
| S-M3-01 | `GalerkinProjection.lean`, D-28 | `fourierSpan_iSup_dense` | D-23 + D-24 + `HilbertBasis.dense_span` + `span_iUnion` |
| S-M3-02 | `GalerkinProjection.lean`, D-30 | `fourierProjection_n_tendsto` | D-28 (S-M3-01) |
| S-M3-03 | `GalerkinProjection.lean`, D-31 | `velocityProjection_n` body | componentwise injection CLM |
| S-M3-04 | `GalerkinProjection.lean`, D-32 | `velocityProjection_n_tendsto` | D-30 + D-31 |
| S-M3-05 | `GalerkinProjection.lean`, D-33 | `velocityProjection_preserves_L2Sigma` | D-29 + D-31 + Fourier coefficient computation |
| S-M3-06 | `GalerkinProjection.lean`, D-34 | `velocityProjection_leray_commute` | orchestrator decision on formulation |

All must carry `-- ALLOW_SORRY: <blocker>` and be added to STATUS.md by lean-coder.

---

## 8. Codex adversarial-review points

The following should receive `/codex:adversarial-review --effort xhigh` before proofs are
attempted:

1. **D-17 (`lerayProjection`)** — confirm that `L2Sigma.orthogonalProjectionOnto` elaborates
   with the correct `𝕜 = ℝ` (not `ℂ`), and that the deprecation of `orthogonalProjection` does
   not cause silent use of the old name.
2. **D-28 (`fourierSpan_iSup_dense`)** — adversarially check that the proof sketch (density of
   Hilbert basis ⟹ dense iSup of finite spans) is sound and does not require an additional
   technical lemma.
3. **D-33 (`velocityProjection_preserves_L2Sigma`)** — validate the statement and the informal
   proof that Fourier truncation of a div-free field is div-free.
4. **D-31 (`velocityProjection_n`)** — validate that the componentwise construction gives a
   genuine CLM (i.e. that the reassembly is continuous and linear).

---

## 9. Axiom ledger for M3

**Zero new axioms required.** All M3 content is provable from mathlib + M2 foundations.
D-28 requires a genuine proof (or marked sorry), not an axiom.

---

## 10. Definition of done for M3

M3 is done when:

1. `lake build` passes.
2. `lerayProjection : L2VF →L[ℝ] L2Sigma` compiles without sorry.
3. D-18 through D-21b (properties of `lerayProjection`) are sorry-free.
4. `fourierBox` and `fourierProjection_n` compile without sorry.
5. `fourierProjection_n_tendsto` is either sorry-free or has a marked sorry with precise blocker.
6. `velocityProjection_n` compiles (sorry or no sorry per S-M3-03 status).
7. `velocityProjection_preserves_L2Sigma` is stated with a marked sorry and precise blocker.
8. All sorry entries are marked and entered in STATUS.md.
9. Orchestrator runs Codex review on items 1–4 of §8 above.
10. `lean-planner` updates STATUS.md milestone row M3 to `done`.

---

## 11. Recommended first task for lean-coder

**Task 1 (lean-coder, `Leray.lean` edit):** Add D-15 and D-16 as `instance` declarations
at the end of `Leray.lean`. Both should be one-liners that `inferInstance` discharges or
near-one-liners. Then add D-17 (`lerayProjection` definition). Run `lake build`. If all
three compile without sorry, add D-18 through D-21b as one-liners. This is ~15 lines total
and should be the easiest block of M3.

**Task 2 (lean-coder, new `GalerkinProjection.lean`):** Write D-22 (`fourierBox`) and
D-23/D-24 (monotone + exhaustion). These are pure combinatorial lemmas over `ℤ` and
should be sorry-free. Then write D-25 (`fourierSpan`) and D-26/D-27 (FiniteDimensional +
CompleteSpace instances). These unblock D-28.

**Tasks 1 and 2 can proceed in parallel.**

---

## 12. Decision summary for orchestrator

| Decision | Recommendation | Status |
|---|---|---|
| 1-A: truncation norm (‖k‖_∞ vs ‖k‖₂) | ‖k‖_∞ cube (`fourierBox`) | **pending orchestrator confirmation** |
| 1-B: projection domain (L2C first vs L2VF direct) | Route C (componentwise on L2C) | **pending orchestrator confirmation** |
| D-34: commutativity vs restricted projection | Define `galerkinLerayProjection_n` directly; defer commutativity | **pending orchestrator decision** |
| D-31 componentwise injection CLM | Must build; ~10 lines via `EuclideanSpace.single` | flagged, no blocker |
