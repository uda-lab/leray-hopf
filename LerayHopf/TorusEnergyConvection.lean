import LerayHopf.AxiomaticClosure
-- AxiomaticClosure import justification: provides `IsGalerkinTest`, `galerkinConvection`,
--   `L2Sigma`, `L2VF`, `L2C`, `mFourierCoeff3`, `velocityProjection_n`, and
--   transitively `H1Sigma.lean` (`memH1VF`, `memH1Sigma`, `memH1Torus`).

open MeasureTheory Filter Topology

/-!
# Torus H¹_σ submodule — packaging + Parseval scaffold (PR-1, torus issue #53)

**Scope (PR-1, torus #53):** Stand up the torus div-free H¹ submodule `H1SigmaTorus`
as a `Submodule ℝ L2Sigma`, state the membership characterisation, and scaffold the
two analytic targets that PR-2 will prove:

- **`gradPairingSummable`** — the Parseval triple sum is summable when the MIDDLE slot
  `v` is H¹ (derivative sits on `v`); Claim-1a from the PR-0 spike.
- **`galerkinTestSpan_subset_H1Sigma`** — every Galerkin test lies in `H1SigmaTorus`
  (finite Fourier support ⟹ weighted sum is finite).

## Dependency note

This file sits **above** `TorusConvectionForm.lean` in the DAG; it does NOT import it.
`TorusConvectionForm.lean` will import this module (in PR-6) to build the proved
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
                                     (scaffold sorry, PR-2 target)
- `galerkinTestSpan_subset_H1Sigma`— Galerkin tests ⊆ H¹_σ (scaffold sorry, PR-2 target)

## Assumptions

None — this file introduces no `axiom`/`opaque`. The two scaffold `sorry`s are
analytic content deferred to `lean-prover` in PR-2.
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
set_option maxHeartbeats 0 in
private lemma mFourierCoeff3_add (f g : L2C) (k : Fin 3 → ℤ) :
    mFourierCoeff3 (f + g) k = mFourierCoeff3 f k + mFourierCoeff3 g k := by
  simp only [mFourierCoeff3, map_add, lp.coeFn_add, Pi.add_apply]

set_option maxHeartbeats 0 in
/-- Helper: `mFourierCoeff3 (c • f) k = (c : ℂ) * mFourierCoeff3 f k`.

Follows the same `rw` chain as `TorusConvectionForm.lean` (lines 88–93). -/
private lemma mFourierCoeff3_smul_eq (c : ℝ) (f : L2C) (k : Fin 3 → ℤ) :
    mFourierCoeff3 (c • f) k = (c : ℂ) * mFourierCoeff3 f k := by
  -- Unfold `mFourierCoeff3` on both sides, convert real smul to complex smul, unpack lp coercion.
  rw [mFourierCoeff3, mFourierCoeff3, RCLike.real_smul_eq_coe_smul (K := ℂ), map_smul,
      lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  rfl

set_option maxHeartbeats 0 in
/-- Helper: the norm of a Fourier coefficient of `f + g` is bounded by the sum of norms. -/
private lemma mFourierCoeff3_norm_add_le (f g : L2C) (k : Fin 3 → ℤ) :
    ‖mFourierCoeff3 (f + g) k‖ ≤ ‖mFourierCoeff3 f k‖ + ‖mFourierCoeff3 g k‖ := by
  rw [mFourierCoeff3_add]; exact norm_add_le _ _

set_option maxHeartbeats 0 in
/-- Helper: `‖mFourierCoeff3 (c • f) k‖ = |c| * ‖mFourierCoeff3 f k‖`. -/
private lemma mFourierCoeff3_norm_smul (c : ℝ) (f : L2C) (k : Fin 3 → ℤ) :
    ‖mFourierCoeff3 (c • f) k‖ = |c| * ‖mFourierCoeff3 f k‖ := by
  rw [mFourierCoeff3_smul_eq, norm_mul, Complex.norm_real, Real.norm_eq_abs]

set_option maxHeartbeats 0 in
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

set_option maxHeartbeats 0 in
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

/-! ### PR-2 analytic targets (scaffold — proved in PR-2) -/

/-! #### Parseval triple-sum summability — Claim 1a (derivative on MIDDLE slot) -/

/-- **`gradPairingSummable` [scaffold, proved in PR-2, torus #53].**

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

**Corresponds to:** `convSummand_summable_of_h1_test` in the PR-0 spike. -/
theorem gradPairingSummable (u : L2VF) (v : L2VF) (hv : memH1VF v)
    (w : L2Sigma) (hw : IsGalerkinTest w) (i a : Fin 3) :
    Summable (fun kl : (Fin 3 → ℤ) × (Fin 3 → ℤ) =>
      (mFourierCoeff3 (L2VF_projComponentC a u) kl.1 *
       ((2 * (Real.pi : ℂ) * Complex.I * (kl.2 a : ℂ)) *
        (mFourierCoeff3 (L2VF_projComponentC i v) kl.2 *
         mFourierCoeff3 (L2VF_projComponentC i (w : L2VF)) (-(kl.1 + kl.2))))).re) := by
  sorry -- ALLOW_SORRY: PR-1 scaffold, discharged in PR-2 (torus #53); anti-diagonal ℓ² Cauchy–Schwarz with finite support of `w` (Galerkin test) and H¹ weight on `v`

/-! #### Galerkin tests are in H¹_σ -/

/-- **`galerkinTestSpan_subset_H1Sigma` [scaffold, proved in PR-2, torus #53].**

Every Galerkin test `w : L2Sigma` (i.e., `IsGalerkinTest w`, so `w ∈ Vₙ` for some `n`)
lies in `H1SigmaTorus`.

**Proof sketch (for PR-2):** By `IsGalerkinTest`, get `n` with `velocityProjection_n n w = w`.
Then `coeff_zero_outside_box` gives `mFourierCoeff3 (L2VF_projComponentC j w) k = 0` for
`k ∉ fourierBox n`.  The weighted H¹ sum `∑_k weight(k) * ‖ŵ_j(k)‖²` reduces to a
finite sum over `fourierBox n`, which is summable. -/
theorem galerkinTestSpan_subset_H1Sigma {w : L2Sigma} (hw : IsGalerkinTest w) :
    w ∈ H1SigmaTorus := by
  sorry -- ALLOW_SORRY: PR-1 scaffold, discharged in PR-2 (torus #53); finite Fourier support via coeff_zero_outside_box; weighted sum = finite sum over fourierBox n

end LerayHopf
