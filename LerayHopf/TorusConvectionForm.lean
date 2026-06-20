import LerayHopf.AxiomaticClosure

open MeasureTheory Filter Topology Complex

/-!
# Finite-sum algebraic lemmas for the T³ Galerkin convection form (issue #22)

**Issue #22 — begin axiom removal for `torus3_NSForms_exist`.**

## What this file does and does not do

This file proves **all six trilinearity lemmas** for `galerkinConvection n` (finite sums
over `fourierBox n`) and proves the key helper `coeff_zero_outside_box` (Fourier support
of `Vₙ`-elements).

It does NOT build a total `b : L2Sigma → L2Sigma → L2Sigma → ℝ` extending
`galerkinConvection` to all of `L²_σ`, because:

1. A naive tsum extension `∑' k ∑' l ...` places the derivative weight `(2πi lₐ)` on the
   raw-L² `v̂(l)` slot.  For general `v ∈ L²_σ`, the product `|lₐ| · |v̂(l)|` need not be
   ℓ²-summable (that requires `v ∈ H¹`).  Young's inequality gives ℓ²∗ℓ²→ℓ^∞, NOT ℓ¹,
   so the double series can diverge.  The `tsum` would return junk (0), and trilinearity
   would not hold.

2. A "dif on IsGalerkinTest" definition breaks antisymmetry: `b_torus u v w` (test=w)
   and `b_torus u w v` (test=v) have mismatched logic when only one of v,w is a test fn.

## The genuine remaining gap

The full `Torus3NSForms` witness requires:
- **Antisymmetry** `galerkinConvection n u v w = -galerkinConvection n u w v` for `u ∈ Vₙ`
  (finite-sum torus IBP: index bijection `l ↦ -(k+l)` + `DivFreeL2 u` cancellation).
  This is an honest algebraic finite-sum computation in Lean — no convergence needed.
- **Extension to all of L²_σ**: a total trilinear form extending `galerkinConvection` is
  needed for the remaining fields over arbitrary L²_σ arguments; this is the genuine
  Mathlib-absent operator gap (weak `(u·∇)v` on Lp).

Until `galerkinConvection n`'s antisymmetry is proved and the extension is built,
the axiom `torus3_NSForms_exist` deliberately remains in `AxiomaticClosure.lean`.

## Declarations added (all sorry-free except two)

### Sorry-free
- `coeff_zero_outside_box` — Fourier coeff of `Vₙ` elements vanishes outside `fourierBox n`
- `galerkinConvection_add_1/2/3` — additivity in each slot (Finset.sum_add_distrib)
- `galerkinConvection_smul_1/2/3` — ℝ-homogeneity in each slot (Finset.mul_sum + cast)

### Honest sorries (2)
- `galerkinConvection_antisymm` — antisymmetry of `galerkinConvection n` for `u ∈ Vₙ`;
  requires Finset.sum_bij with bijection `l ↦ -(k+l)` on `fourierBox n` + DivFreeL2;
  no convergence needed, purely algebraic.
- `galerkinConvection_bound` — Cauchy–Schwarz bound for fixed-`n` sum; needs Parseval
  (available in this project as `L2C_norm_sq_eq_tsum_coeff_sq`) + finite CS inequality.

## Axiom status

Zero new axioms.  `torus3_NSForms_exist` kept.
-/

namespace LerayHopf

/-! ### Helper: linearity of `mFourierCoeff3 (L2VF_projComponentC j ·)` -/

/-- Additivity: `û_j(u + u', k) = û_j(u, k) + û_j(u', k)`. -/
private lemma mFourierCoeff3_projComponentC_add (j : Fin 3) (u u' : L2VF)
    (k : Fin 3 → ℤ) :
    mFourierCoeff3 (L2VF_projComponentC j (u + u')) k =
      mFourierCoeff3 (L2VF_projComponentC j u) k +
      mFourierCoeff3 (L2VF_projComponentC j u') k := by
  simp [mFourierCoeff3, map_add]

/-- ℝ-homogeneity: `û_j(c • u, k) = (c : ℂ) * û_j(u, k)`. -/
private lemma mFourierCoeff3_projComponentC_smul (j : Fin 3) (c : ℝ) (u : L2VF)
    (k : Fin 3 → ℤ) :
    mFourierCoeff3 (L2VF_projComponentC j (c • u)) k =
      (c : ℂ) * mFourierCoeff3 (L2VF_projComponentC j u) k := by
  simp [mFourierCoeff3, map_smul, smul_eq_mul]

/-! ### Galerkin support: coefficients vanish outside the box -/

/-- If `u ∈ Vₙ` (i.e. `velocityProjection_n n u = u`), then the `j`-th Fourier
coefficient of `u` vanishes for `k ∉ fourierBox n`.

Proof: `velocityProjection_n_component_comm` says
`L2VF_projComponentC j (velocityProjection_n n u) = fourierProjection_n n (L2VF_projComponentC j u)`,
and `fourierProjection_n_mFourierCoeff` says the coefficient is 0 outside the box. -/
lemma coeff_zero_outside_box (n : ℕ) (u : L2VF)
    (hu : velocityProjection_n n u = u) (j : Fin 3) (k : Fin 3 → ℤ)
    (hk : k ∉ fourierBox n) :
    mFourierCoeff3 (L2VF_projComponentC j u) k = 0 := by
  have hcomm := velocityProjection_n_component_comm n u j
  rw [hu] at hcomm
  rw [← hcomm, fourierProjection_n_mFourierCoeff, if_neg hk]

/-! ### Trilinearity of `galerkinConvection n` — all sorry-free (finite Finset sums) -/

/-- `galerkinConvection n` is additive in the first slot. -/
theorem galerkinConvection_add_1 (n : ℕ) (u u' v w : L2VF) :
    galerkinConvection n (u + u') v w =
      galerkinConvection n u v w + galerkinConvection n u' v w := by
  simp only [galerkinConvection, mFourierCoeff3_projComponentC_add, add_mul,
    Complex.add_re, Finset.sum_add_distrib]

/-- `galerkinConvection n` is additive in the second slot. -/
theorem galerkinConvection_add_2 (n : ℕ) (u v v' w : L2VF) :
    galerkinConvection n u (v + v') w =
      galerkinConvection n u v w + galerkinConvection n u v' w := by
  simp only [galerkinConvection, mFourierCoeff3_projComponentC_add]
  -- After simp: summand has `(v̂_i(l) + v̂'_i(l)) * ŵ_i(-(k+l))` = `v̂*ŵ + v̂'*ŵ`.
  conv_lhs =>
    arg 1; ext i; arg 1; ext a; arg 2; ext k; arg 2; ext l
    rw [show mFourierCoeff3 (L2VF_projComponentC a u) k *
        ((2 * (↑Real.pi : ℂ) * I * ↑(l a)) *
          ((mFourierCoeff3 (L2VF_projComponentC i v) l +
            mFourierCoeff3 (L2VF_projComponentC i v') l) *
           mFourierCoeff3 (L2VF_projComponentC i w) (-(k + l)))) =
        mFourierCoeff3 (L2VF_projComponentC a u) k *
          ((2 * (↑Real.pi : ℂ) * I * ↑(l a)) *
            (mFourierCoeff3 (L2VF_projComponentC i v) l *
             mFourierCoeff3 (L2VF_projComponentC i w) (-(k + l)))) +
        mFourierCoeff3 (L2VF_projComponentC a u) k *
          ((2 * (↑Real.pi : ℂ) * I * ↑(l a)) *
            (mFourierCoeff3 (L2VF_projComponentC i v') l *
             mFourierCoeff3 (L2VF_projComponentC i w) (-(k + l)))) by ring]
  simp only [Complex.add_re, Finset.sum_add_distrib]

/-- `galerkinConvection n` is additive in the third slot. -/
theorem galerkinConvection_add_3 (n : ℕ) (u v w w' : L2VF) :
    galerkinConvection n u v (w + w') =
      galerkinConvection n u v w + galerkinConvection n u v w' := by
  simp only [galerkinConvection, mFourierCoeff3_projComponentC_add]
  conv_lhs =>
    arg 1; ext i; arg 1; ext a; arg 2; ext k; arg 2; ext l
    rw [show mFourierCoeff3 (L2VF_projComponentC a u) k *
        ((2 * (↑Real.pi : ℂ) * I * ↑(l a)) *
          (mFourierCoeff3 (L2VF_projComponentC i v) l *
           (mFourierCoeff3 (L2VF_projComponentC i w) (-(k + l)) +
            mFourierCoeff3 (L2VF_projComponentC i w') (-(k + l))))) =
        mFourierCoeff3 (L2VF_projComponentC a u) k *
          ((2 * (↑Real.pi : ℂ) * I * ↑(l a)) *
            (mFourierCoeff3 (L2VF_projComponentC i v) l *
             mFourierCoeff3 (L2VF_projComponentC i w) (-(k + l)))) +
        mFourierCoeff3 (L2VF_projComponentC a u) k *
          ((2 * (↑Real.pi : ℂ) * I * ↑(l a)) *
            (mFourierCoeff3 (L2VF_projComponentC i v) l *
             mFourierCoeff3 (L2VF_projComponentC i w') (-(k + l)))) by ring]
  simp only [Complex.add_re, Finset.sum_add_distrib]

/-- Key: `Re[(c : ℂ) * z] = c * Re[z]` for `c : ℝ`. -/
private lemma re_ofReal_mul (c : ℝ) (z : ℂ) : ((c : ℂ) * z).re = c * z.re := by
  simp [Complex.mul_re, ofReal_re, ofReal_im]

/-- `galerkinConvection n` is ℝ-homogeneous in the first slot.

Proof: `mFourierCoeff3_projComponentC_smul` turns `û_a(c • u, k)` into `(c : ℂ) * û_a(u, k)`.
The scalar `(c : ℂ)` is then the outermost factor in each summand (it multiplies the
entire product since it's the first factor), so `Re[(c : ℂ) * z] = c * Re[z]` and
`Finset.mul_sum` pull `c` outside all four nested sums. -/
theorem galerkinConvection_smul_1 (n : ℕ) (c : ℝ) (u v w : L2VF) :
    galerkinConvection n (c • u) v w = c * galerkinConvection n u v w := by
  simp only [galerkinConvection, mFourierCoeff3_projComponentC_smul]
  -- After simp: each summand is `Re[(c : ℂ) * û_a(k) * (...)]`
  -- = `Re[(c : ℂ) * (û_a(k) * (...))]` = `c * Re[û_a(k) * (...)]`
  conv_lhs =>
    arg 1; ext i; arg 1; ext a; arg 2; ext k; arg 2; ext l
    rw [show ((c : ℂ) * mFourierCoeff3 (L2VF_projComponentC a u) k) *
        ((2 * (↑Real.pi : ℂ) * I * ↑(l a)) *
          (mFourierCoeff3 (L2VF_projComponentC i v) l *
           mFourierCoeff3 (L2VF_projComponentC i w) (-(k + l)))) =
        (c : ℂ) * (mFourierCoeff3 (L2VF_projComponentC a u) k *
          ((2 * (↑Real.pi : ℂ) * I * ↑(l a)) *
          (mFourierCoeff3 (L2VF_projComponentC i v) l *
           mFourierCoeff3 (L2VF_projComponentC i w) (-(k + l))))) by ring,
      re_ofReal_mul]
  simp only [Finset.mul_sum]

/-- `galerkinConvection n` is ℝ-homogeneous in the second slot. -/
theorem galerkinConvection_smul_2 (n : ℕ) (c : ℝ) (u v w : L2VF) :
    galerkinConvection n u (c • v) w = c * galerkinConvection n u v w := by
  simp only [galerkinConvection, mFourierCoeff3_projComponentC_smul]
  conv_lhs =>
    arg 1; ext i; arg 1; ext a; arg 2; ext k; arg 2; ext l
    rw [show mFourierCoeff3 (L2VF_projComponentC a u) k *
        ((2 * (↑Real.pi : ℂ) * I * ↑(l a)) *
          ((c : ℂ) * mFourierCoeff3 (L2VF_projComponentC i v) l *
           mFourierCoeff3 (L2VF_projComponentC i w) (-(k + l)))) =
        (c : ℂ) * (mFourierCoeff3 (L2VF_projComponentC a u) k *
          ((2 * (↑Real.pi : ℂ) * I * ↑(l a)) *
          (mFourierCoeff3 (L2VF_projComponentC i v) l *
           mFourierCoeff3 (L2VF_projComponentC i w) (-(k + l))))) by ring,
      re_ofReal_mul]
  simp only [Finset.mul_sum]

/-- `galerkinConvection n` is ℝ-homogeneous in the third slot. -/
theorem galerkinConvection_smul_3 (n : ℕ) (c : ℝ) (u v w : L2VF) :
    galerkinConvection n u v (c • w) = c * galerkinConvection n u v w := by
  simp only [galerkinConvection, mFourierCoeff3_projComponentC_smul]
  conv_lhs =>
    arg 1; ext i; arg 1; ext a; arg 2; ext k; arg 2; ext l
    rw [show mFourierCoeff3 (L2VF_projComponentC a u) k *
        ((2 * (↑Real.pi : ℂ) * I * ↑(l a)) *
          (mFourierCoeff3 (L2VF_projComponentC i v) l *
           ((c : ℂ) * mFourierCoeff3 (L2VF_projComponentC i w) (-(k + l))))) =
        (c : ℂ) * (mFourierCoeff3 (L2VF_projComponentC a u) k *
          ((2 * (↑Real.pi : ℂ) * I * ↑(l a)) *
          (mFourierCoeff3 (L2VF_projComponentC i v) l *
           mFourierCoeff3 (L2VF_projComponentC i w) (-(k + l))))) by ring,
      re_ofReal_mul]
  simp only [Finset.mul_sum]

/-! ### Antisymmetry of `galerkinConvection n` — the remaining honest sorry -/

/-- **Antisymmetry:** `galerkinConvection n u v w = -galerkinConvection n u w v`
when `u ∈ Vₙ` (divergence-free, finite Fourier support).

This is a finite-sum torus integration-by-parts identity:
  `galerkinConvection n u v w + galerkinConvection n u w v`
  `= ∑ i,a ∑_{k,l ∈ fourierBox n} Re[ û_a(k) · (2πi lₐ) · (v̂_i(l)·ŵ_i(-(k+l)) + ŵ_i(l)·v̂_i(-(k+l))) ]`

After the index substitution `l ↦ -(k+l)` in the second sum (valid since `neg_mem_fourierBox`
ensures the image is still in `fourierBox n`), the sum collapses to a combination
involving `∑_a (k+l)_a · û_a(k+l) = 0` by `DivFreeL2 u` (`u.2 : u ∈ L2Sigma`).

**Exact Lean gap:** Apply `Finset.sum_bij` with bijection `l ↦ -(k+l)` on `fourierBox n`
(bijective by `neg_mem_fourierBox` + injectivity), then collect the `∑_a` term and apply
`mem_L2Sigma_iff.mp u.2` at `k = k + l` to get `∑_a (k+l)_a * û_a(k+l) = 0`.
This is purely algebraic — no convergence or summability needed.

Note: the hypothesis `hu` is NOT needed for well-formedness (the formula makes sense
for all `u : L2Sigma`); it is needed to guarantee `û_a(k) = 0` for `k ∉ fourierBox n`
when establishing the identity via the finite-sum IBP at box level `n`. For the
ACTUAL antisymmetry proof (valid for all `u : L2Sigma`, not just `u ∈ Vₙ`), the
argument uses only `DivFreeL2 u` (available as `u.2` via `mem_L2Sigma_iff`), not `hu`. -/
theorem galerkinConvection_antisymm (n : ℕ) (u : L2Sigma) (v w : L2VF) :
    galerkinConvection n (u : L2VF) v w = -galerkinConvection n (u : L2VF) w v := by
  -- TODO: apply Finset.sum_bij with bijection (k, l) ↦ (k, -(k+l)) on fourierBox n × fourierBox n.
  -- The bijection is well-defined because neg_mem_fourierBox shows -(k+l) ∈ fourierBox n when k,l ∈ fourierBox n.
  -- After substitution, the `lₐ` factor in the second sum becomes `-(k+l)_a = -(k_a + l_a)`.
  -- The sum becomes ∑ l [û_a(k) * (2πi l_a) * v̂_i(l) * ŵ_i(-(k+l))
  --                      + û_a(k) * 2πi*(-(k+l)_a) * ŵ_i(-(k+l)) * v̂_i(l)]
  --   = ∑ l û_a(k) * (2πi) * (l_a - (k_a + l_a)) * v̂_i(l) * ŵ_i(-(k+l))
  --   = ∑ l û_a(k) * (-2πi k_a) * v̂_i(l) * ŵ_i(-(k+l))
  -- Then summing over a: ∑_a (-2πi k_a) * û_a(k) * [∑_l v̂_i(l) * ŵ_i(-(k+l))]
  -- = (-2πi) * [∑_a k_a * û_a(k)] * [∑_l v̂_i(l) * ŵ_i(-(k+l))]
  -- = 0 by DivFreeL2 u (∑_a k_a * û_a(k) = 0 for all k, from u.2 via mem_L2Sigma_iff).
  -- (Actually the sum is over k, and for each k the inner ∑_a k_a û_a(k) = 0.)
  sorry -- ALLOW_SORRY: galerkinConvection antisymmetry; finite-sum torus IBP; exact gap: Finset.sum_bij with l ↦ -(k+l) on fourierBox n (valid by neg_mem_fourierBox) + DivFreeL2 u from u.2 (mem_L2Sigma_iff); purely algebraic, no convergence; lean-prover target

/-! ### L² bound for `galerkinConvection n` at fixed `n` — honest sorry -/

/-- **Bilinear L² bound** for the finite Galerkin convection form.

For fixed `n` and `w : L2VF` with `velocityProjection_n n w = w`, the map
`(u, v) ↦ galerkinConvection n u v w` is a bilinear form in `(u, v)` with
an explicit L² bound `|galerkinConvection n u v w| ≤ C(n,w) · ‖u‖_{L²} · ‖v‖_{L²}`.

**Proof sketch (no convergence needed):**

`galerkinConvection n u v w = ∑ i ∑ a ∑_{k ∈ fourierBox n} ∑_{l ∈ fourierBox n}
   Re [ û_a(k) · (2πi lₐ) · v̂_i(l) · ŵ_i(-(k+l)) ]`

Fix i, a, and consider the bilinear form `(u, v) ↦ ∑_{k,l} û_a(k) · A(l,w) · v̂_i(l)`
where `A(l, w) = Re[(2πi lₐ) · ŵ_i(-(k+l))]`.  This is a finite sum of terms each of
which is bounded by `|û_a(k)| · C(k,l,n,w) · |v̂_i(l)|` where `C` is finite.
By Parseval (`L2C_norm_sq_eq_tsum_coeff_sq` from `RellichEmbedding.lean`) and
Cauchy–Schwarz on ℓ²(fourierBox n):

  `|∑_{k,l ∈ fourierBox n} û_a(k) * A(k,l,w) * v̂_i(l)|
   ≤ (∑_{k,l} |A(k,l,w)|²)^{1/2} * ‖(û_a(k))_{k ∈ fourierBox n}‖_ℓ² * ‖(v̂_i(l))_{l ∈ fourierBox n}‖_ℓ²
   ≤ C(n,w) · ‖u‖_{L²} · ‖v‖_{L²}`

where `C(n,w) = (card fourierBox n)^{1/2} * ∑_{l ∈ fourierBox n} ∑_a (2π |lₐ|) * |ŵ_a(l)|` is finite.

**Exact Lean gap:** Apply `Finset.inner_mul_le_norm_mul_iff` (Cauchy–Schwarz on `Finset`)
and then bound via `L2C_norm_sq_eq_tsum_coeff_sq`.  The key inequality
`∑_{k ∈ fourierBox n} |û_a(k)|² ≤ ∑' k |û_a(k)|² = ‖L2VF_projComponentC a u‖²`
is Parseval (available via `L2C_norm_sq_eq_tsum_coeff_sq` from `RellichEmbedding.lean`).
No convergence hypothesis; everything is finite. -/
theorem galerkinConvection_bound (n : ℕ) (w : L2VF)
    (hw : velocityProjection_n n w = w) :
    ∃ C : ℝ, ∀ (u v : L2VF), |galerkinConvection n u v w| ≤ C * ‖u‖ * ‖v‖ := by
  sorry -- ALLOW_SORRY: bilinear L² bound for galerkinConvection n; Cauchy–Schwarz on Finset + Parseval (L2C_norm_sq_eq_tsum_coeff_sq from RellichEmbedding.lean); no convergence needed; lean-prover target

end LerayHopf
