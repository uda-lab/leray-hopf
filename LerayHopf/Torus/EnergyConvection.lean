import LerayHopf.Torus.SolutionInterfaces
import LerayHopf.Torus.GalerkinScheme  -- coeff_zero_outside_box (issue #111 PR-5)
-- SolutionInterfaces import justification: provides `IsGalerkinTest`, `galerkinConvection`,
--   `L2Sigma`, `L2VF`, `L2C`, `mFourierCoeff3`, `velocityProjection_n`, and
--   transitively `H1Sigma.lean` (`memH1VF`, `memH1Sigma`, `memH1Torus`) and
--   `FunctionSpaces.lean` (`L2C_norm_sq_eq_tsum_coeff_sq` for the ℓ²-Cauchy–Schwarz bound).

open MeasureTheory Filter Topology

/-!
# Torus H¹_σ submodule — packaging + Parseval support (torus issue #53)

**Scope (torus #53):** Stand up the torus div-free H¹ submodule `H1SigmaTorus`
as a `Submodule ℝ L2Sigma`, state the membership characterisation, and provide the
two analytic bridge lemmas used by the determined-form construction:

- **`gradPairingSummable`** — the Parseval triple sum is summable when the MIDDLE slot
  `v` is H¹ (derivative sits on `v`); Claim-1a from the PR-0 spike.
- **`galerkinTestSpan_subset_H1Sigma`** — every Galerkin test lies in `H1SigmaTorus`
  (finite Fourier support ⟹ weighted sum is finite).

## Dependency note

This file sits **above** `TorusConvectionForm.lean` in the DAG; it does NOT import it.
`TorusConvectionForm.lean` imports this module to build the proved
`theorem torusConvectionGap_exists`.

## Declarations

- `memH1VF_zero`                   — `memH1VF 0` (proved, sorry-free)
- `memH1VF_add`                    — `memH1VF` closed under addition (proved, sorry-free)
- `memH1VF_smul`                   — `memH1VF` closed under real scalar multiplication
                                     (proved, sorry-free)
- `H1SigmaTorus`                   — `Submodule ℝ L2Sigma` with carrier `{u | memH1Sigma u}`
                                     (proved, sorry-free via the three closure lemmas above)
- `mem_H1SigmaTorus_iff`           — membership characterisation (proved, sorry-free)
- `gradPairingSummable`            — Parseval summability with H¹ on middle slot
- `galerkinTestSpan_subset_H1Sigma`— Galerkin tests ⊆ H¹_σ

## Assumptions

None — this file introduces no `axiom`/`opaque`. The Parseval and Galerkin-test bridge lemmas
are proved and feed the BLT construction.
-/

namespace LerayHopf

/-! ### Closure lemmas for `memH1VF` under the vector-space operations -/

/-! These three lemmas mirror `memH1VF_R3_zero/add/smul` from
`LerayHopf/R3/EnergyClassConvection.lean` (B1b/B1c/B1a), but use only the
Fourier-weight `Summable` predicate directly (no Sobolev API).

`memH1VF u = ∀ j, memH1Torus (L2VF_projComponentC j u)`, and
`memH1Torus f = Summable (fun k => (1 + ∑ i, (k i : ℝ)^2) * ‖mFourierCoeff3 f k‖^2)`. -/

/-- The zero velocity field satisfies `memH1VF`: each component is 0, so the
weighted Fourier sum is identically 0 (summable). -/
theorem memH1VF_zero : memH1VF (0 : L2VF) := fun j => by
  rw [show L2VF_projComponentC j (0 : L2VF) = 0 from map_zero _]
  exact memH1Torus_zero

-- `mFourierCoeff3` distributivity.
-- `set_option maxHeartbeats` raised because unfolding the `lp` coercion in `whnf`
-- exceeds the default 200000 limit.
-- Both `mFourierCoeff3_add` and `mFourierCoeff3_smul_eq` require increasing heartbeats
-- because unfolding the `lp` coercion through `FunLike` and `Subtype.val` triggers
-- expensive `whnf` reduction beyond the default 200000 limit.
-- issue #152: was `maxHeartbeats 0` (unlimited); 4000000 is sufficient, confirmed by a
-- targeted `lake build LerayHopf.Torus.EnergyConvection` (~3m wall clock on the CI host).
set_option maxHeartbeats 4000000 in
private lemma mFourierCoeff3_add (f g : L2C) (k : Fin 3 → ℤ) :
    mFourierCoeff3 (f + g) k = mFourierCoeff3 f k + mFourierCoeff3 g k := by
  simp only [mFourierCoeff3, map_add, lp.coeFn_add, Pi.add_apply]

set_option maxHeartbeats 4000000 in
/-- Helper: `mFourierCoeff3 (c • f) k = (c : ℂ) * mFourierCoeff3 f k`.

Follows the same `rw` chain as `TorusConvectionForm.lean` (lines 88–93). -/
private lemma mFourierCoeff3_smul_eq (c : ℝ) (f : L2C) (k : Fin 3 → ℤ) :
    mFourierCoeff3 (c • f) k = (c : ℂ) * mFourierCoeff3 f k := by
  -- Unfold `mFourierCoeff3` on both sides, convert real smul to complex smul, unpack lp coercion.
  rw [mFourierCoeff3, mFourierCoeff3, RCLike.real_smul_eq_coe_smul (K := ℂ), map_smul,
      lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  rfl

set_option maxHeartbeats 4000000 in
/-- Helper: the norm of a Fourier coefficient of `f + g` is bounded by the sum of norms. -/
private lemma mFourierCoeff3_norm_add_le (f g : L2C) (k : Fin 3 → ℤ) :
    ‖mFourierCoeff3 (f + g) k‖ ≤ ‖mFourierCoeff3 f k‖ + ‖mFourierCoeff3 g k‖ := by
  rw [mFourierCoeff3_add]; exact norm_add_le _ _

set_option maxHeartbeats 4000000 in
/-- Helper: `‖mFourierCoeff3 (c • f) k‖ = |c| * ‖mFourierCoeff3 f k‖`. -/
private lemma mFourierCoeff3_norm_smul (c : ℝ) (f : L2C) (k : Fin 3 → ℤ) :
    ‖mFourierCoeff3 (c • f) k‖ = |c| * ‖mFourierCoeff3 f k‖ := by
  rw [mFourierCoeff3_smul_eq, norm_mul, Complex.norm_real, Real.norm_eq_abs]

set_option maxHeartbeats 4000000 in
/-- `memH1VF` is closed under addition: if `u` and `v` are H¹, so is `u + v`.

Key: `‖(f̂+ĝ)(k)‖² ≤ 2(‖f̂(k)‖² + ‖ĝ(k)‖²)` (parallelogram / Cauchy–Schwarz), so
the weighted sum for `u + v` is dominated term-wise by the H¹ sums for `u` and `v`. -/
theorem memH1VF_add {u v : L2VF} (hu : memH1VF u) (hv : memH1VF v) :
    memH1VF (u + v) := fun j => by
  rw [show L2VF_projComponentC j (u + v) =
      L2VF_projComponentC j u + L2VF_projComponentC j v from map_add _ u v]
  unfold memH1Torus
  have hf := hu j; have hg := hv j
  unfold memH1Torus at hf hg
  -- Summable upper bound: 2 * (weight(k) * ‖f̂(k)‖² + weight(k) * ‖ĝ(k)‖²)
  -- `Summable.const_smul 2 hf` gives `2 •` which equals `2 *` for ℝ; use `.congr` to convert.
  have hbound : Summable (fun k : Fin 3 → ℤ =>
      2 * ((1 + ∑ i : Fin 3, (k i : ℝ) ^ 2) * ‖mFourierCoeff3 (L2VF_projComponentC j u) k‖ ^ 2) +
      2 * ((1 + ∑ i : Fin 3, (k i : ℝ) ^ 2) * ‖mFourierCoeff3 (L2VF_projComponentC j v) k‖ ^ 2)) :=
    (hf.const_smul (2 : ℝ) |>.add (hg.const_smul (2 : ℝ))).congr (fun k => by ring)
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) hbound
  have hk : (0 : ℝ) ≤ 1 + ∑ i : Fin 3, (k i : ℝ) ^ 2 := by positivity
  -- ‖(f+g)(k)‖ ≤ ‖f(k)‖ + ‖g(k)‖, so ‖(f+g)(k)‖² ≤ 2‖f(k)‖² + 2‖g(k)‖²
  have hadd := mFourierCoeff3_norm_add_le (L2VF_projComponentC j u) (L2VF_projComponentC j v) k
  have hf_nn := norm_nonneg (mFourierCoeff3 (L2VF_projComponentC j u) k)
  have hg_nn := norm_nonneg (mFourierCoeff3 (L2VF_projComponentC j v) k)
  have hineq : ‖mFourierCoeff3 (L2VF_projComponentC j u + L2VF_projComponentC j v) k‖ ^ 2 ≤
      2 * ‖mFourierCoeff3 (L2VF_projComponentC j u) k‖ ^ 2 +
      2 * ‖mFourierCoeff3 (L2VF_projComponentC j v) k‖ ^ 2 := by
    -- ‖a+b‖ ≤ ‖a‖ + ‖b‖, so ‖a+b‖² ≤ (‖a‖+‖b‖)² ≤ 2‖a‖² + 2‖b‖² (AM-GM: (‖a‖-‖b‖)² ≥ 0)
    set A := ‖mFourierCoeff3 (L2VF_projComponentC j u) k‖
    set B := ‖mFourierCoeff3 (L2VF_projComponentC j v) k‖
    set C := ‖mFourierCoeff3 (L2VF_projComponentC j u + L2VF_projComponentC j v) k‖
    -- hadd : C ≤ A + B; hf_nn : 0 ≤ A; hg_nn : 0 ≤ B
    -- We need C² ≤ 2A² + 2B²
    -- From C ≤ A + B and C ≥ 0: C² ≤ (A+B)² = A² + 2AB + B² ≤ 2A² + 2B² (since 2AB ≤ A² + B²)
    have hC : 0 ≤ C := norm_nonneg _
    have hle : C ^ 2 ≤ (A + B) ^ 2 := by nlinarith
    nlinarith [sq_nonneg (A - B)]
  nlinarith [mul_le_mul_of_nonneg_left hineq hk,
             mul_nonneg hk (sq_nonneg (‖mFourierCoeff3 (L2VF_projComponentC j u) k‖)),
             mul_nonneg hk (sq_nonneg (‖mFourierCoeff3 (L2VF_projComponentC j v) k‖))]

set_option maxHeartbeats 4000000 in
/-- `memH1VF` is closed under real scalar multiplication: if `u` is H¹ and `c : ℝ`,
then `c • u` is H¹.

Key: `‖mFourierCoeff3 (c • f) k‖ = |c| · ‖mFourierCoeff3 f k‖` (by linearity + norm_smul),
so the weighted sum for `c • u` equals `c²` times the weighted sum for `u`. -/
theorem memH1VF_smul (c : ℝ) {u : L2VF} (hu : memH1VF u) :
    memH1VF (c • u) := fun j => by
  rw [show L2VF_projComponentC j (c • u) =
      c • L2VF_projComponentC j u from map_smul _ c u]
  unfold memH1Torus
  have hf := hu j
  unfold memH1Torus at hf
  -- The weighted sum for `c • f` = c² × the weighted sum for `f`.
  -- Upper bound: c² * weight(k) * ‖f̂(k)‖² (actually an equality)
  -- `const_smul (c^2)` gives `(c^2) •` = `(c^2) *` in ℝ; use `.congr` to rewrite.
  have hbound2 : Summable (fun k : Fin 3 → ℤ =>
      c ^ 2 * ((1 + ∑ i : Fin 3, (k i : ℝ) ^ 2) * ‖mFourierCoeff3 (L2VF_projComponentC j u) k‖ ^ 2)) :=
    (hf.const_smul (c ^ 2)).congr (fun k => by ring)
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) hbound2
  -- Use ‖mFourierCoeff3 (c • f) k‖ = |c| * ‖mFourierCoeff3 f k‖
  have hnorm := mFourierCoeff3_norm_smul c (L2VF_projComponentC j u) k
  have hk : (0 : ℝ) ≤ 1 + ∑ i : Fin 3, (k i : ℝ) ^ 2 := by positivity
  rw [hnorm]
  -- Goal: (1+w) * (|c| * ‖f(k)‖)^2 ≤ c^2 * ((1+w) * ‖f(k)‖^2)
  -- Since |c|^2 = c^2, these are equal.
  set N := ‖mFourierCoeff3 (L2VF_projComponentC j u) k‖
  have hsq : |c| ^ 2 = c ^ 2 := sq_abs c
  nlinarith [abs_nonneg c, sq_nonneg N, mul_nonneg hk (sq_nonneg N),
             sq_nonneg (|c| * N), sq_abs c]

/-! ### Fourier support of Galerkin-box elements -/

/-! ### The H¹_σ submodule of `L2Sigma` -/

/-- **`H1SigmaTorus` — the div-free H¹ submodule of `L2Sigma`.**

The carrier is `{u : L2Sigma | memH1Sigma (u : L2VF)}`.  Since every `u : L2Sigma`
already satisfies the div-free condition, membership reduces to `memH1VF (u : L2VF)`.

Mirrors `H1Sigma'` from `R3/ConvectionExtension.lean` but for the torus, using the
predicates `memH1VF` / `memH1Sigma` from `H1Sigma.lean` directly.
Closure proofs use `memH1VF_zero/add/smul` above. -/
def H1SigmaTorus : Submodule ℝ L2Sigma where
  carrier := {u | memH1Sigma (u : L2VF)}
  add_mem' {_ _} hu hv :=
    ⟨L2Sigma.add_mem hu.1 hv.1,
     memH1VF_add hu.2 hv.2⟩
  zero_mem' :=
    ⟨L2Sigma.zero_mem, memH1VF_zero⟩
  smul_mem' c _ hu :=
    ⟨L2Sigma.smul_mem c hu.1,
     memH1VF_smul c hu.2⟩

/-- Membership characterisation for `H1SigmaTorus`:
`u ∈ H1SigmaTorus ↔ u ∈ L2Sigma ∧ memH1VF (u : L2VF)`. -/
@[simp]
theorem mem_H1SigmaTorus_iff (u : L2Sigma) :
    u ∈ H1SigmaTorus ↔ memH1Sigma (u : L2VF) :=
  Iff.rfl

/-! ### ℓ² / weighted-ℓ² summability of Fourier coefficients (local helpers) -/

/-- The H¹-gradient-weighted squared coefficients are summable for an H¹ component:
`∑_l (∑ᵢ (lᵢ)²) · ‖v̂(l)‖² < ∞`.  Dominated by the full H¹ weight `(1 + ∑ᵢ(lᵢ)²)`. -/
private theorem summable_grad_weight_sq {f : L2C} (hf : memH1Torus f) :
    Summable (fun l : Fin 3 → ℤ => (∑ i : Fin 3, (l i : ℝ) ^ 2) * ‖mFourierCoeff3 f l‖ ^ 2) := by
  refine hf.of_nonneg_of_le (fun l => by positivity) (fun l => ?_)
  have hge : (∑ i : Fin 3, (l i : ℝ) ^ 2) ≤ 1 + ∑ i : Fin 3, (l i : ℝ) ^ 2 := by linarith
  exact mul_le_mul_of_nonneg_right hge (by positivity)

/-! ### Analytic bridge lemmas used by the determined-form construction -/

/-! #### Parseval triple-sum summability — Claim 1a (derivative on MIDDLE slot) -/

/-- The per-`(i,a)` Fourier convection summand at lattice point `(k, l)`, before taking the
real part.  Sums (over `(i, a)` and the lattice) to the convection form value. -/
noncomputable def convSummand (u v w : L2VF) (i a : Fin 3) (k l : Fin 3 → ℤ) : ℂ :=
  mFourierCoeff3 (L2VF_projComponentC a u) k *
    ((2 * (Real.pi : ℂ) * Complex.I * (l a : ℂ)) *
      (mFourierCoeff3 (L2VF_projComponentC i v) l *
        mFourierCoeff3 (L2VF_projComponentC i w) (-(k + l))))

set_option maxHeartbeats 1000000 in
-- kept at the original 1000000 (issue #152): isolated `#count_heartbeats in` measurement
-- reported only ~540 heartbeats, but a real sequential build with the override removed
-- times out at `whnf` under the 200000 default — the isolated figure undercounts this
-- declaration's true cost, so no further reduction attempted here.
/-- **Norm-summability of the convection summand on the H¹/Galerkin-test locus.**

For `u : L2VF`, `v : L2VF` with `memH1VF v` (H¹ on the MIDDLE / gradient slot), and a Galerkin
test `w`, the summand norm `‖convSummand u v w i a (k,l)‖` is summable over the lattice.

Anti-diagonal AM-GM: `‖û_a(k)‖·2π|lₐ|·‖v̂_i(l)‖ ≤ π(‖û_a(k)‖² + (lₐ)²‖v̂_i(l)‖²)`, dominated
(after the reindexings `(k,l)↦(k,-(k+l))` and `(k,l)↦(l,-(k+l))`) by products of
`ℓ²(û)` / weighted-`ℓ²(∇v)` (from `memH1VF v`) with the finite-support `ℓ¹(ŵ)`.

**Corresponds to:** `convSummand_summable_of_h1_test` in the PR-0 spike. -/
theorem convSummand_norm_summable (u : L2VF) (v : L2VF) (hv : memH1VF v)
    (w : L2Sigma) (hw : IsGalerkinTest w) (i a : Fin 3) :
    Summable (fun kl : (Fin 3 → ℤ) × (Fin 3 → ℤ) =>
      ‖convSummand u v (w : L2VF) i a kl.1 kl.2‖) := by
  classical
  -- Abbreviations (definitional) for the three coefficient families.
  let U : (Fin 3 → ℤ) → ℂ := fun k => mFourierCoeff3 (L2VF_projComponentC a u) k
  let V : (Fin 3 → ℤ) → ℂ := fun l => mFourierCoeff3 (L2VF_projComponentC i v) l
  let Wc : (Fin 3 → ℤ) → ℂ := fun m => mFourierCoeff3 (L2VF_projComponentC i (w : L2VF)) m
  -- `‖Wc(·)‖` is finitely supported (Galerkin test ⟹ `w ∈ Vₙ`).
  obtain ⟨n, hn⟩ := hw
  have hWsupp : ∀ m : Fin 3 → ℤ, m ∉ fourierBox n → Wc m = 0 := by
    intro m hm; exact coeff_zero_outside_box n (w : L2VF) hn i m hm
  have hWsumm : Summable (fun m : Fin 3 → ℤ => ‖Wc m‖) :=
    summable_of_ne_finset_zero (s := fourierBox n)
      (fun m hm => by rw [hWsupp m hm, norm_zero])
  have hUsq : Summable (fun k : Fin 3 → ℤ => ‖U k‖ ^ 2) := Torus.summable_norm_mFourierCoeff3_sq _
  have hVw : Summable (fun l : Fin 3 → ℤ => (∑ j : Fin 3, (l j : ℝ) ^ 2) * ‖V l‖ ^ 2) :=
    summable_grad_weight_sq (hv i)
  -- The dominating sum `G kl := π · ‖Wc m‖ · (‖U k‖² + (lₐ)² ‖V l‖²)`, `m = -(k+l)`, is summable.
  have hGsum : Summable (fun kl : (Fin 3 → ℤ) × (Fin 3 → ℤ) =>
      Real.pi * (‖Wc (-(kl.1 + kl.2))‖ *
        (‖U kl.1‖ ^ 2 + (kl.2 a : ℝ) ^ 2 * ‖V kl.2‖ ^ 2))) := by
    apply Summable.mul_left
    have hsplit : (fun kl : (Fin 3 → ℤ) × (Fin 3 → ℤ) =>
          ‖Wc (-(kl.1 + kl.2))‖ * (‖U kl.1‖ ^ 2 + (kl.2 a : ℝ) ^ 2 * ‖V kl.2‖ ^ 2))
        = (fun kl => ‖Wc (-(kl.1 + kl.2))‖ * ‖U kl.1‖ ^ 2)
          + (fun kl => ‖Wc (-(kl.1 + kl.2))‖ * ((kl.2 a : ℝ) ^ 2 * ‖V kl.2‖ ^ 2)) := by
      funext kl; simp only [Pi.add_apply]; ring
    rw [hsplit]
    refine Summable.add ?_ ?_
    · -- Reindex `(k,l) ↦ (k, -(k+l))`; then product `‖U k‖² · ‖Wc m‖`.
      let e : (Fin 3 → ℤ) × (Fin 3 → ℤ) ≃ (Fin 3 → ℤ) × (Fin 3 → ℤ) :=
        { toFun := fun kl => (kl.1, -(kl.1 + kl.2))
          invFun := fun km => (km.1, -(km.1 + km.2))
          left_inv := fun kl => Prod.ext rfl (by funext j; simp [Pi.neg_apply, Pi.add_apply])
          right_inv := fun km => Prod.ext rfl (by funext j; simp [Pi.neg_apply, Pi.add_apply]) }
      have hprod : Summable (fun km : (Fin 3 → ℤ) × (Fin 3 → ℤ) => ‖U km.1‖ ^ 2 * ‖Wc km.2‖) :=
        hUsq.mul_of_nonneg hWsumm (fun _ => by positivity) (fun _ => norm_nonneg _)
      refine ((Equiv.summable_iff e).mpr hprod).congr (fun kl => ?_)
      simp only [e, Equiv.coe_fn_mk, Function.comp]
      ring
    · -- Reindex `(k,l) ↦ (l, -(k+l))`; then product `((lₐ)²‖V l‖²) · ‖Wc m‖`.
      let e : (Fin 3 → ℤ) × (Fin 3 → ℤ) ≃ (Fin 3 → ℤ) × (Fin 3 → ℤ) :=
        { toFun := fun kl => (kl.2, -(kl.1 + kl.2))
          invFun := fun lm => (-(lm.1 + lm.2), lm.1)
          left_inv := fun kl => Prod.ext (by funext j; simp [Pi.neg_apply, Pi.add_apply]) rfl
          right_inv := fun lm => Prod.ext rfl (by funext j; simp [Pi.neg_apply, Pi.add_apply]) }
      -- For the `(lₐ)²‖V l‖²` factor: dominated by the H¹ weight `(∑ⱼ(lⱼ)²)‖V l‖²`.
      have hVa : Summable (fun l : Fin 3 → ℤ => (l a : ℝ) ^ 2 * ‖V l‖ ^ 2) := by
        refine hVw.of_nonneg_of_le (fun l => by positivity) (fun l => ?_)
        have hle : (l a : ℝ) ^ 2 ≤ ∑ j : Fin 3, (l j : ℝ) ^ 2 :=
          Finset.single_le_sum (f := fun j => (l j : ℝ) ^ 2)
            (fun j _ => by positivity) (Finset.mem_univ a)
        exact mul_le_mul_of_nonneg_right hle (by positivity)
      have hprod : Summable (fun lm : (Fin 3 → ℤ) × (Fin 3 → ℤ) =>
          ((lm.1 a : ℝ) ^ 2 * ‖V lm.1‖ ^ 2) * ‖Wc lm.2‖) :=
        hVa.mul_of_nonneg hWsumm (fun _ => by positivity) (fun _ => norm_nonneg _)
      refine ((Equiv.summable_iff e).mpr hprod).congr (fun kl => ?_)
      simp only [e, Equiv.coe_fn_mk, Function.comp]
      ring
  -- Dominate `‖convSummand‖` by `G`.
  refine Summable.of_nonneg_of_le (fun kl => norm_nonneg _) (fun kl => ?_) hGsum
  show ‖U kl.1 * ((2 * (Real.pi : ℂ) * Complex.I * (kl.2 a : ℂ)) *
      (V kl.2 * Wc (-(kl.1 + kl.2))))‖
    ≤ Real.pi * (‖Wc (-(kl.1 + kl.2))‖ * (‖U kl.1‖ ^ 2 + (kl.2 a : ℝ) ^ 2 * ‖V kl.2‖ ^ 2))
  -- `‖z‖ = ‖U‖·(2π|lₐ|)·‖V‖·‖Wc‖`.
  have hnormeq : ‖(U kl.1 * ((2 * (Real.pi : ℂ) * Complex.I * (kl.2 a : ℂ)) *
        (V kl.2 * Wc (-(kl.1 + kl.2)))))‖
      = ‖U kl.1‖ * ((2 * Real.pi) * |(kl.2 a : ℝ)|) * ‖V kl.2‖ * ‖Wc (-(kl.1 + kl.2))‖ := by
    simp only [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_intCast,
      Real.norm_eq_abs, Complex.norm_ofNat]
    rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ Real.pi)]
    ring
  rw [hnormeq]
  -- AM-GM: `‖U‖·(2π|lₐ|)·‖V‖·‖Wc‖ ≤ π‖Wc‖(‖U‖² + (lₐ)²‖V‖²)`.
  have hamgm : ‖U kl.1‖ * (|(kl.2 a : ℝ)| * ‖V kl.2‖)
      ≤ (‖U kl.1‖ ^ 2 + (kl.2 a : ℝ) ^ 2 * ‖V kl.2‖ ^ 2) / 2 := by
    nlinarith [sq_nonneg (‖U kl.1‖ - |(kl.2 a : ℝ)| * ‖V kl.2‖), norm_nonneg (U kl.1),
      norm_nonneg (V kl.2), abs_nonneg (kl.2 a : ℝ), sq_abs (kl.2 a : ℝ),
      mul_nonneg (abs_nonneg (kl.2 a : ℝ)) (norm_nonneg (V kl.2))]
  have hWnn : (0:ℝ) ≤ ‖Wc (-(kl.1 + kl.2))‖ := norm_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hamgm
    (by positivity : (0:ℝ) ≤ (2 * Real.pi) * ‖Wc (-(kl.1 + kl.2))‖), Real.pi_pos, hWnn,
    norm_nonneg (U kl.1), norm_nonneg (V kl.2)]

/-- Complex summability of the convection summand on the H¹/Galerkin-test locus
(from `convSummand_norm_summable` via `Summable.of_norm`). -/
theorem convSummand_summable (u : L2VF) (v : L2VF) (hv : memH1VF v)
    (w : L2Sigma) (hw : IsGalerkinTest w) (i a : Fin 3) :
    Summable (fun kl : (Fin 3 → ℤ) × (Fin 3 → ℤ) =>
      convSummand u v (w : L2VF) i a kl.1 kl.2) :=
  (convSummand_norm_summable u v hv w hw i a).of_norm

set_option maxHeartbeats 1000000 in
-- kept at the original 1000000 (issue #152): isolated `#count_heartbeats in` measurement
-- reported ~936 heartbeats; given the sibling declaration `convSummand_norm_summable` in this
-- same file measured similarly low yet failed under the default budget in a real rebuild, no
-- removal was attempted here without a dedicated re-verification cycle.
/-- **`gradPairingSummable` (torus #53).**

For `u : L2VF`, `v : L2VF` with `memH1VF v` (H¹ on the MIDDLE / gradient slot),
and `w : L2Sigma` a Galerkin test, the Parseval convection summand

  `(k, l) ↦ (û_a(k) · (2πi lₐ) · v̂_i(l) · ŵ_i(-(k+l))).re`

is summable over `(Fin 3 → ℤ) × (Fin 3 → ℤ)` for each fixed `(i, a) : Fin 3 × Fin 3`.

**Why the H¹ condition is on `v` (NOT symmetric):** The weight `(2πi lₐ)` is the
Fourier multiplier for `∂_a v`.  Writing `α(k) = |û_a(k)|`, `β(l) = |lₐ| · |v̂_i(l)|`,
`γ(m) = |ŵ_i(m)|`, the double sum is a convolution-diagonal bound.  Since `w` is a
Galerkin test (finite support), `γ` is finitely supported ⟹ anti-diagonal collapse
gives summability from `α ∈ ℓ²`, `β ∈ ℓ²` (the `ℓ²·ℓ²·ℓ¹_finite` product).  Three
arbitrary L² slots do NOT suffice.

**Corresponds to:** `convSummand_summable_of_h1_test` in the PR-0 spike.

Proof: `Complex.reCLM`-image of `convSummand_summable` (the complex-summable workhorse). -/
theorem gradPairingSummable (u : L2VF) (v : L2VF) (hv : memH1VF v)
    (w : L2Sigma) (hw : IsGalerkinTest w) (i a : Fin 3) :
    Summable (fun kl : (Fin 3 → ℤ) × (Fin 3 → ℤ) =>
      (mFourierCoeff3 (L2VF_projComponentC a u) kl.1 *
       ((2 * (Real.pi : ℂ) * Complex.I * (kl.2 a : ℂ)) *
        (mFourierCoeff3 (L2VF_projComponentC i v) kl.2 *
         mFourierCoeff3 (L2VF_projComponentC i (w : L2VF)) (-(kl.1 + kl.2))))).re) :=
  (convSummand_summable u v hv w hw i a).map Complex.reCLM Complex.reCLM.continuous

/-! #### Galerkin tests are in H¹_σ -/

/-- **`galerkinTestSpan_subset_H1Sigma` (torus #53).**

Every Galerkin test `w : L2Sigma` (i.e., `IsGalerkinTest w`, so `w ∈ Vₙ` for some `n`)
lies in `H1SigmaTorus`.

**Proof sketch (for PR-2):** By `IsGalerkinTest`, get `n` with `velocityProjection_n n w = w`.
Then `coeff_zero_outside_box` gives `mFourierCoeff3 (L2VF_projComponentC j w) k = 0` for
`k ∉ fourierBox n`.  The weighted H¹ sum `∑_k weight(k) * ‖ŵ_j(k)‖²` reduces to a
finite sum over `fourierBox n`, which is summable. -/
theorem galerkinTestSpan_subset_H1Sigma {w : L2Sigma} (hw : IsGalerkinTest w) :
    w ∈ H1SigmaTorus := by
  rw [mem_H1SigmaTorus_iff]
  refine ⟨w.2, fun j => ?_⟩
  -- `w` lies in the Galerkin box `Vₙ`.
  obtain ⟨n, hn⟩ := hw
  -- The H¹-weight sum is supported on `fourierBox n`: the coefficient vanishes outside the box.
  refine summable_of_ne_finset_zero (s := fourierBox n) (fun k hk => ?_)
  rw [coeff_zero_outside_box n (w : L2VF) hn j k hk, norm_zero]
  ring

/-! ### The total Fourier convection form `convFormFourier`

`convFormFourier u v w` is the lattice-`tsum` extension of the finite box form
`galerkinConvection n`.  It is **total** on `L²_σ × L²_σ × L²_σ` via the mathlib
`tsum`-junk convention (value `0` off the summable locus), and **agrees with the genuine
convection value exactly on the H¹/Galerkin-test locus** where `gradPairingSummable`
guarantees convergence.

This is the torus analog of R3's `convFormH1` (the genuine convection form on the H¹ slice),
but built directly on the Fourier side — so its antisymmetry reduces to the divergence-free
identity `∑ₐ kₐûₐ(k) = 0` (no spatial integration by parts, no Leibniz product rule).

NOTE: this is **not yet** wired as the `TorusConvectionGap.b` field — the total `b`
demands a genuine trilinear `LinearMap` (the `b_multilinear` field), which the raw `tsum`
does not provide off the summable locus.  The determined-form construction (mirror of
`R3/ConvectionExtension.lean`) reads `convFormFourier` off only on the determined H¹ slice,
where it is convergent and genuinely multilinear.  The lemmas below (`_antisymm_h1`,
`_bound_galerkinTest`) are the analytic inputs that construction consumes. -/

/-- The **total Fourier convection form** on `L²_σ(𝕋³)`: the lattice `tsum` extension of
`galerkinConvection`.  Total via the `tsum`-junk convention; genuine on the H¹/Galerkin-test
locus (`gradPairingSummable`). -/
noncomputable def convFormFourier (u v w : L2Sigma) : ℝ :=
  ∑ i : Fin 3, ∑ a : Fin 3,
    (∑' kl : (Fin 3 → ℤ) × (Fin 3 → ℤ), convSummand (u : L2VF) (v : L2VF) (w : L2VF) i a kl.1 kl.2).re

/-! ### Antisymmetry on the Galerkin-test overlap (Claim 2 — div-free identity, no IBP) -/

/-- A Galerkin test is H¹: finite Fourier support ⟹ every Sobolev norm finite. -/
private theorem memH1VF_of_galerkinTest {w : L2Sigma} (hw : IsGalerkinTest w) :
    memH1VF (w : L2VF) := (galerkinTestSpan_subset_H1Sigma hw).2

/-- The full-lattice involution `(k, l) ↦ (k, -(k + l))` on the product index set, used for
the antisymmetry reindex.  Unlike the box-truncated `galerkinConvection_antisymm` (which needs
`v, w ∈ Vₙ` because `box × box` is not `σ`-invariant), the **full** lattice IS invariant, so the
reindex is an unconditional `Equiv`. -/
private def latticeInvol : (Fin 3 → ℤ) × (Fin 3 → ℤ) ≃ (Fin 3 → ℤ) × (Fin 3 → ℤ) where
  toFun kl := (kl.1, -(kl.1 + kl.2))
  invFun km := (km.1, -(km.1 + km.2))
  left_inv kl := Prod.ext rfl (by funext j; simp [Pi.neg_apply, Pi.add_apply])
  right_inv km := Prod.ext rfl (by funext j; simp [Pi.neg_apply, Pi.add_apply])

set_option maxHeartbeats 1000000 in
-- kept at the original 1000000 (issue #152): isolated `#count_heartbeats in` measurement
-- reported ~314 heartbeats; given the sibling declaration `convSummand_norm_summable` in this
-- same file measured similarly low yet failed under the default budget in a real rebuild, no
-- removal was attempted here without a dedicated re-verification cycle.
/-- **Antisymmetry of `convFormFourier` on the Galerkin-test overlap.**

For `u : L²_σ` divergence-free and `v, w` both Galerkin tests (the `𝒢 ⊗ 𝒢` overlap of the
determined-form construction):
`convFormFourier u v w = - convFormFourier u w v`.

This is the genuine Faedo–Galerkin convection antisymmetry, proved **on the Fourier side**
without integration by parts: per `(i, a)`, the two complex lattice sums `A` (with `v` in the
middle) and `A'` (with `w` in the middle) combine, the involution `latticeInvol` (full-lattice,
no box truncation) reindexes `A'`, and the factor `(lₐ + (-(k+l))ₐ) = -kₐ` is annihilated by the
divergence-free identity `∑ₐ kₐ ûₐ(k) = 0`.  Both orientations are summable because `v, w` are
Galerkin tests (`convSummand_summable`). -/
theorem convFormFourier_antisymm_galerkinTest (u : L2Sigma) (v w : L2Sigma)
    (hv : IsGalerkinTest v) (hw : IsGalerkinTest w) :
    convFormFourier u v w = -convFormFourier u w v := by
  classical
  have hdiv : DivFreeL2 (u : L2VF) := (mem_L2Sigma_iff _).mp u.2
  have hvH1 : memH1VF (v : L2VF) := memH1VF_of_galerkinTest hv
  have hwH1 : memH1VF (w : L2VF) := memH1VF_of_galerkinTest hw
  rw [convFormFourier, convFormFourier, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  -- Work with the `∑ a` kept together (the div-free identity needs the `a`-sum).
  -- Summability of both orientations, for every `a` (`v, w` Galerkin tests).
  have hsummA : ∀ a : Fin 3, Summable (fun kl : (Fin 3 → ℤ) × (Fin 3 → ℤ) =>
      convSummand (u : L2VF) (v : L2VF) (w : L2VF) i a kl.1 kl.2) :=
    fun a => convSummand_summable (u : L2VF) (v : L2VF) hvH1 w hw i a
  have hsummA' : ∀ a : Fin 3, Summable (fun kl : (Fin 3 → ℤ) × (Fin 3 → ℤ) =>
      convSummand (u : L2VF) (w : L2VF) (v : L2VF) i a kl.1 kl.2) :=
    fun a => convSummand_summable (u : L2VF) (w : L2VF) hwH1 v hv i a
  -- Reindex each `A'ₐ` by the full-lattice involution `(k,l) ↦ (k,-(k+l))`.
  have hsummA'rei : ∀ a : Fin 3, Summable (fun kl : (Fin 3 → ℤ) × (Fin 3 → ℤ) =>
      convSummand (u : L2VF) (w : L2VF) (v : L2VF) i a kl.1 (-(kl.1 + kl.2))) := by
    intro a
    have := (Equiv.summable_iff latticeInvol).mpr (hsummA' a)
    refine this.congr (fun kl => ?_)
    simp only [latticeInvol, Equiv.coe_fn_mk, Function.comp]
  have hA'rei : ∀ a : Fin 3,
      (∑' kl : (Fin 3 → ℤ) × (Fin 3 → ℤ),
        convSummand (u : L2VF) (w : L2VF) (v : L2VF) i a kl.1 kl.2)
      = ∑' kl : (Fin 3 → ℤ) × (Fin 3 → ℤ),
        convSummand (u : L2VF) (w : L2VF) (v : L2VF) i a kl.1 (-(kl.1 + kl.2)) := by
    intro a; rw [← Equiv.tsum_eq latticeInvol]; rfl
  -- Goal: `∑ a, (∑'kl S_v).re = -∑ a, (∑'kl S_w).re`.  Reduce to `∑ a, (∑'kl S_v + ∑'kl S_w).re = 0`.
  rw [eq_neg_iff_add_eq_zero, ← Finset.sum_add_distrib]
  rw [show (∑ a : Fin 3,
        ((∑' kl : (Fin 3 → ℤ) × (Fin 3 → ℤ),
            convSummand (u : L2VF) (v : L2VF) (w : L2VF) i a kl.1 kl.2).re
          + (∑' kl : (Fin 3 → ℤ) × (Fin 3 → ℤ),
            convSummand (u : L2VF) (w : L2VF) (v : L2VF) i a kl.1 kl.2).re))
      = (∑ a : Fin 3,
          ((∑' kl : (Fin 3 → ℤ) × (Fin 3 → ℤ),
            convSummand (u : L2VF) (v : L2VF) (w : L2VF) i a kl.1 kl.2)
          + (∑' kl : (Fin 3 → ℤ) × (Fin 3 → ℤ),
            convSummand (u : L2VF) (w : L2VF) (v : L2VF) i a kl.1 kl.2))).re from by
    rw [Complex.re_sum]; refine Finset.sum_congr rfl (fun a _ => ?_); rw [Complex.add_re]]
  rw [← Complex.zero_re]
  refine congrArg Complex.re ?_
  -- Per `a`: combine the two reindexed tsums into one (`Summable.tsum_add`).
  have hcombine : ∀ a : Fin 3,
      (∑' kl : (Fin 3 → ℤ) × (Fin 3 → ℤ),
          convSummand (u : L2VF) (v : L2VF) (w : L2VF) i a kl.1 kl.2)
        + (∑' kl : (Fin 3 → ℤ) × (Fin 3 → ℤ),
          convSummand (u : L2VF) (w : L2VF) (v : L2VF) i a kl.1 kl.2)
      = ∑' kl : (Fin 3 → ℤ) × (Fin 3 → ℤ),
          (2 * (Real.pi : ℂ) * Complex.I) * (-(kl.1 a : ℂ)) *
            (mFourierCoeff3 (L2VF_projComponentC a (u : L2VF)) kl.1 *
              (mFourierCoeff3 (L2VF_projComponentC i (v : L2VF)) kl.2 *
               mFourierCoeff3 (L2VF_projComponentC i (w : L2VF)) (-(kl.1 + kl.2)))) := by
    intro a
    rw [hA'rei a, ← Summable.tsum_add (hsummA a) (hsummA'rei a)]
    refine tsum_congr (fun kl => ?_)
    -- Inner argument `-(k + -(k+l)) = l` (the involution is self-inverse).
    have harg : -(kl.1 + -(kl.1 + kl.2)) = kl.2 := by funext j; simp [Pi.neg_apply, Pi.add_apply]
    have hka : ((-(kl.1 + kl.2)) a : ℂ) = -(kl.1 a : ℂ) - (kl.2 a : ℂ) := by
      simp [Pi.neg_apply, Pi.add_apply]; push_cast; ring
    simp only [convSummand, harg]
    rw [hka]
    ring
  rw [Finset.sum_congr rfl (fun a _ => hcombine a)]
  -- Swap `∑ a` inside the tsum (each combined family is summable), then per-`(k,l)`.
  have hGsumm : ∀ a : Fin 3, Summable (fun kl : (Fin 3 → ℤ) × (Fin 3 → ℤ) =>
      (2 * (Real.pi : ℂ) * Complex.I) * (-(kl.1 a : ℂ)) *
        (mFourierCoeff3 (L2VF_projComponentC a (u : L2VF)) kl.1 *
          (mFourierCoeff3 (L2VF_projComponentC i (v : L2VF)) kl.2 *
           mFourierCoeff3 (L2VF_projComponentC i (w : L2VF)) (-(kl.1 + kl.2))))) := by
    intro a
    have hsum := (hsummA a).add (hsummA'rei a)
    refine hsum.congr (fun kl => ?_)
    have harg : -(kl.1 + -(kl.1 + kl.2)) = kl.2 := by funext j; simp [Pi.neg_apply, Pi.add_apply]
    have hka : ((-(kl.1 + kl.2)) a : ℂ) = -(kl.1 a : ℂ) - (kl.2 a : ℂ) := by
      simp [Pi.neg_apply, Pi.add_apply]; push_cast; ring
    simp only [convSummand, harg]
    rw [hka]; ring
  rw [← (hasSum_sum (fun a (_ : a ∈ Finset.univ) => (hGsumm a).hasSum)).tsum_eq]
  -- Each lattice term `∑ₐ G_a kl = 0` by the divergence-free identity; so the tsum is `tsum 0 = 0`.
  rw [show (fun kl : (Fin 3 → ℤ) × (Fin 3 → ℤ) => ∑ a : Fin 3,
        (2 * (Real.pi : ℂ) * Complex.I) * (-(kl.1 a : ℂ)) *
          (mFourierCoeff3 (L2VF_projComponentC a (u : L2VF)) kl.1 *
            (mFourierCoeff3 (L2VF_projComponentC i (v : L2VF)) kl.2 *
             mFourierCoeff3 (L2VF_projComponentC i (w : L2VF)) (-(kl.1 + kl.2)))))
      = fun _ => (0 : ℂ) from funext (fun kl => ?_), tsum_zero]
  -- `∑ a, (2πi)(-kₐ)ûₐ(k)·(common) = (2πi)·(common)·(-∑ₐ kₐûₐ(k)) = 0`.
  have hfac : ∑ a : Fin 3, (2 * (Real.pi : ℂ) * Complex.I) * (-(kl.1 a : ℂ)) *
        (mFourierCoeff3 (L2VF_projComponentC a (u : L2VF)) kl.1 *
          (mFourierCoeff3 (L2VF_projComponentC i (v : L2VF)) kl.2 *
           mFourierCoeff3 (L2VF_projComponentC i (w : L2VF)) (-(kl.1 + kl.2))))
      = -((2 * (Real.pi : ℂ) * Complex.I) *
          (mFourierCoeff3 (L2VF_projComponentC i (v : L2VF)) kl.2 *
           mFourierCoeff3 (L2VF_projComponentC i (w : L2VF)) (-(kl.1 + kl.2)))) *
          (∑ a : Fin 3, (kl.1 a : ℂ) * mFourierCoeff3 (L2VF_projComponentC a (u : L2VF)) kl.1) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    ring
  rw [hfac, hdiv kl.1, mul_zero]

end LerayHopf
