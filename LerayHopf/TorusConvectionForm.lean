import LerayHopf.AxiomaticClosure

open MeasureTheory Filter Topology Complex

/-!
# Finite-sum algebraic lemmas for the T³ Galerkin convection form (issue #22)

**Issue #22 — begin axiom removal for `torus3_NSForms_exist`.**

## What this file does and does not do

This file proves the **trilinearity** (additivity + ℝ-homogeneity in each slot) and an
explicit **bilinear L² bound** for `galerkinConvection n` (finite sums over `fourierBox n`),
plus the helper `coeff_zero_outside_box` (Fourier support of `Vₙ`-elements).

It does NOT build a total `b : L2Sigma → L2Sigma → L2Sigma → ℝ` extending
`galerkinConvection` to all of `L²_σ`: a total trilinear form extending the box-truncated
form is the genuine Mathlib-absent operator gap (weak `(u·∇)v` on Lp), out of scope here.

## The genuine remaining gaps

- **Antisymmetry** `galerkinConvection n u v w = -galerkinConvection n u w v` is the standard
  Galerkin convection antisymmetry — but it holds only when the **test slots `v, w` lie in
  `Vₙ`** (finite Fourier support), not for arbitrary `v, w : L2VF`.  The box truncation
  `box × box` is not invariant under the involution `(k,l) ↦ (k,-(k+l))` that the IBP
  reindexing needs (`neg_mem_fourierBox` only covers `k ↦ -k`); finite support of `u` alone
  does NOT rescue it.  See `galerkinConvection_antisymm` for the full analysis: as currently
  stated (arbitrary `v, w`) it is FALSE, and discharging it needs a signature change
  (add `velocityProjection_n n v = v`, `velocityProjection_n n w = w` — owner: lean-coder).
- **Extension to all of L²_σ**: the total `(u·∇)v` operator on `Lp` (Mathlib-absent).

Until antisymmetry (restated over `Vₙ`) is proved and the extension is built, the axiom
`torus3_NSForms_exist` deliberately remains in `AxiomaticClosure.lean`.

## Declarations added

### Sorry-free
- `coeff_zero_outside_box` — Fourier coeff of `Vₙ` elements vanishes outside `fourierBox n`
- `norm_mFourierCoeff3_le` — single Fourier coefficient ≤ L² norm (Bessel/`lp` bound)
- `galerkinConvection_add_1/2/3` — additivity in each slot (`Finset.sum_add_distrib`)
- `galerkinConvection_smul_1/2/3` — ℝ-homogeneity in each slot (`Finset.mul_sum` + cast)
- `galerkinConvection_bound` — explicit bilinear L² bound (triangle inequality + Bessel +
  operator-norm bound; no convergence, finite sums only)

### Honest sorry (1)
- `galerkinConvection_antisymm` — FALSE as stated (arbitrary `v, w`); see its docstring.
  Requires a signature change to `v, w ∈ Vₙ` before it can be proved.

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
  rw [map_smul, mFourierCoeff3, mFourierCoeff3]
  -- The ℝ-smul on `L2C` is the ℂ-smul by `(c : ℂ)` (scalar tower); then `repr` is
  -- ℂ-linear so `map_smul` pulls it out; `lp.coeFn_smul` + `Pi.smul_apply` + `smul_eq_mul` finish.
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ), map_smul, lp.coeFn_smul, Pi.smul_apply,
    smul_eq_mul]
  rfl

/-- A single Fourier coefficient is bounded by the `L²` norm (Bessel/`lp` bound):
`‖û(k)‖ ≤ ‖f‖`. -/
private lemma norm_mFourierCoeff3_le (f : L2C) (k : Fin 3 → ℤ) :
    ‖mFourierCoeff3 f k‖ ≤ ‖f‖ := by
  have h := lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0)
    (torus3_mFourierBasis.repr f) k
  rwa [torus3_mFourierBasis.repr.norm_map f] at h

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
  -- Rewrite the coefficient's argument to the `restrictScalars`-wrapped projection (`conv` so
  -- the forward rewrite fires exactly once on the argument inside `mFourierCoeff3`), unfold the
  -- `restrictScalars` coe, then `fourierProjection_n_mFourierCoeff` + `if_neg`.
  conv_lhs => rw [hcomm]
  rw [ContinuousLinearMap.coe_restrictScalars', fourierProjection_n_mFourierCoeff, if_neg hk]

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
  -- Distribute `(v̂_i(l) + v̂'_i(l)) * ŵ_i(-(k+l))` and pull the `+` out through every sum
  -- level, then split the real part of the complex sum.
  simp only [add_mul, mul_add, Finset.sum_add_distrib, Complex.add_re]

/-- `galerkinConvection n` is additive in the third slot. -/
theorem galerkinConvection_add_3 (n : ℕ) (u v w w' : L2VF) :
    galerkinConvection n u v (w + w') =
      galerkinConvection n u v w + galerkinConvection n u v w' := by
  simp only [galerkinConvection, mFourierCoeff3_projComponentC_add]
  -- Distribute `ŵ_i(-(k+l)) + ŵ'_i(-(k+l))` and pull the `+` out through every sum level.
  simp only [mul_add, Finset.sum_add_distrib, Complex.add_re]

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
  -- Factor `(c : ℂ)` to the front of every summand (`Finset.sum_congr` + `ring`), pull it
  -- out of all four sums (`← Finset.mul_sum`), then `Re[(c:ℂ)·z] = c·Re[z]`.
  rw [show (∑ i : Fin 3, ∑ a : Fin 3, ∑ k ∈ fourierBox n, ∑ l ∈ fourierBox n,
        ((c : ℂ) * mFourierCoeff3 (L2VF_projComponentC a u) k) *
          ((2 * (↑Real.pi : ℂ) * I * ↑(l a)) *
            (mFourierCoeff3 (L2VF_projComponentC i v) l *
             mFourierCoeff3 (L2VF_projComponentC i w) (-(k + l))))) =
        (c : ℂ) * ∑ i : Fin 3, ∑ a : Fin 3, ∑ k ∈ fourierBox n, ∑ l ∈ fourierBox n,
          mFourierCoeff3 (L2VF_projComponentC a u) k *
            ((2 * (↑Real.pi : ℂ) * I * ↑(l a)) *
              (mFourierCoeff3 (L2VF_projComponentC i v) l *
               mFourierCoeff3 (L2VF_projComponentC i w) (-(k + l)))) from ?_,
      re_ofReal_mul]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ =>
    Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

/-- `galerkinConvection n` is ℝ-homogeneous in the second slot. -/
theorem galerkinConvection_smul_2 (n : ℕ) (c : ℝ) (u v w : L2VF) :
    galerkinConvection n u (c • v) w = c * galerkinConvection n u v w := by
  simp only [galerkinConvection, mFourierCoeff3_projComponentC_smul]
  rw [show (∑ i : Fin 3, ∑ a : Fin 3, ∑ k ∈ fourierBox n, ∑ l ∈ fourierBox n,
        mFourierCoeff3 (L2VF_projComponentC a u) k *
          ((2 * (↑Real.pi : ℂ) * I * ↑(l a)) *
            ((c : ℂ) * mFourierCoeff3 (L2VF_projComponentC i v) l *
             mFourierCoeff3 (L2VF_projComponentC i w) (-(k + l))))) =
        (c : ℂ) * ∑ i : Fin 3, ∑ a : Fin 3, ∑ k ∈ fourierBox n, ∑ l ∈ fourierBox n,
          mFourierCoeff3 (L2VF_projComponentC a u) k *
            ((2 * (↑Real.pi : ℂ) * I * ↑(l a)) *
              (mFourierCoeff3 (L2VF_projComponentC i v) l *
               mFourierCoeff3 (L2VF_projComponentC i w) (-(k + l)))) from ?_,
      re_ofReal_mul]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ =>
    Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

/-- `galerkinConvection n` is ℝ-homogeneous in the third slot. -/
theorem galerkinConvection_smul_3 (n : ℕ) (c : ℝ) (u v w : L2VF) :
    galerkinConvection n u v (c • w) = c * galerkinConvection n u v w := by
  simp only [galerkinConvection, mFourierCoeff3_projComponentC_smul]
  rw [show (∑ i : Fin 3, ∑ a : Fin 3, ∑ k ∈ fourierBox n, ∑ l ∈ fourierBox n,
        mFourierCoeff3 (L2VF_projComponentC a u) k *
          ((2 * (↑Real.pi : ℂ) * I * ↑(l a)) *
            (mFourierCoeff3 (L2VF_projComponentC i v) l *
             ((c : ℂ) * mFourierCoeff3 (L2VF_projComponentC i w) (-(k + l)))))) =
        (c : ℂ) * ∑ i : Fin 3, ∑ a : Fin 3, ∑ k ∈ fourierBox n, ∑ l ∈ fourierBox n,
          mFourierCoeff3 (L2VF_projComponentC a u) k *
            ((2 * (↑Real.pi : ℂ) * I * ↑(l a)) *
              (mFourierCoeff3 (L2VF_projComponentC i v) l *
               mFourierCoeff3 (L2VF_projComponentC i w) (-(k + l)))) from ?_,
      re_ofReal_mul]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ =>
    Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

/-! ### Antisymmetry of `galerkinConvection n` — the remaining honest sorry -/

/-- **Antisymmetry (NOT provable as currently stated — needs `v, w ∈ Vₙ`):**
`galerkinConvection n u v w = -galerkinConvection n u w v` for div-free `u`.

**Why the prior route is invalid AND the statement itself is too strong.**
Write the antisymmetry target as
  `galerkinConvection n u v w + galerkinConvection n u w v`
  `= (∑ i,a ∑_{k,l ∈ box} û_a(k) · (2πi lₐ) · (v̂_i(l)·ŵ_i(-(k+l)) + ŵ_i(l)·v̂_i(-(k+l)))).re`.

The full-lattice convection form `∑_{k+l+m=0} û_a(k)·(2πi lₐ)·v̂_i(l)·ŵ_i(m)` is antisymmetric
because the constraint set `{k+l+m=0}` is symmetric under the swap `l ↔ m`, and the relabel
turns `lₐ` into `lₐ+mₐ = -kₐ`, which `∑_a kₐ û_a(k) = 0` (`DivFreeL2 u`) kills.

The box-truncated form replaces `m` by `-(k+l)` with `k,l ∈ box` but leaves `m = -(k+l)`
**unrestricted** (it ranges over `[-2n,2n]³`).  The truncation index set `box × box` is
therefore **NOT invariant** under the involution `(k,l) ↦ (k, -(k+l))` that antisymmetry
requires: `neg_mem_fourierBox` only proves `-k ∈ box ↔ k ∈ box`, not `-(k+l) ∈ box`, and in
general `-(k+l) ∉ box` for `k,l ∈ box` (e.g. `k=(1,0,0), l=(1,1,0) ⇒ -(k+l)=(-2,-1,0) ∉ box`
for `n=1`).  Hence the `l ↔ m` reindexing that drives the IBP cancellation is invalid here,
and finite Fourier support of `u` does NOT rescue it (it only extends the `k`-sum to ℤ³; the
`l`-sum stays truncated to `box`, so the form remains asymmetric in `(l, m)`).

The identity becomes true once `v, w ∈ Vₙ` (`velocityProjection_n n v = v`, likewise `w`):
then `v̂_i, ŵ_i` vanish outside `box`, the `l`-sum and the `m = -(k+l)` argument both become
effectively full-lattice, and the `l ↔ m` reindex closes (cf. Temam II.§1, RRS §3.2 — the
standard Galerkin antisymmetry is over test functions in `Vₙ`).

**Blocker (signature, owner = lean-coder):** the conclusion needs the two added hypotheses
`velocityProjection_n n v = v` and `velocityProjection_n n w = w`.  With those, the proof is
the full-lattice IBP reindex + `DivFreeL2 u`.  As written (arbitrary `v w : L2VF`) the
statement is false, so no honest proof exists at this signature. -/
theorem galerkinConvection_antisymm (n : ℕ) (u : L2Sigma) (v w : L2VF) :
    galerkinConvection n (u : L2VF) v w = -galerkinConvection n (u : L2VF) w v := by
  sorry -- ALLOW_SORRY: FALSE AS STATED — box-truncated convection form is NOT antisymmetric for arbitrary v,w; box×box is not invariant under (k,l)↦(k,-(k+l)) (neg_mem_fourierBox covers only k↦-k); finite support of u does not rescue (l-sum stays truncated). Provable only after lean-coder adds hypotheses `velocityProjection_n n v = v` and `velocityProjection_n n w = w`; then full-lattice l↔m IBP reindex + DivFreeL2 u closes. Not a false-blocker: statement genuinely needs v,w∈Vₙ.

/-! ### L² bound for `galerkinConvection n` at fixed `n` -/

/-- **Bilinear L² bound** for the finite Galerkin convection form.

For fixed `n` and `w : L2VF`, the map `(u, v) ↦ galerkinConvection n u v w` is a bilinear
form in `(u, v)` with an explicit L² bound
`|galerkinConvection n u v w| ≤ C · ‖u‖_{L²} · ‖v‖_{L²}`.

**Proof (no convergence needed — everything is a finite Finset sum):**

`galerkinConvection n u v w = (∑ i ∑ a ∑_{k ∈ box} ∑_{l ∈ box}
   û_a(k) · (2πi lₐ) · v̂_i(l) · ŵ_i(-(k+l))).re`.

Since `|z.re| ≤ ‖z‖` (`abs_re_le_norm`) and the norm of a finite sum is bounded by the sum
of norms (`norm_sum_le`), it suffices to bound each summand norm:
`‖û_a(k)·(2πi lₐ)·v̂_i(l)·ŵ_i(-(k+l))‖
   ≤ (‖projₐ‖·‖u‖)·‖2πi lₐ‖·(‖projᵢ‖·‖v‖)·‖ŵ_i(-(k+l))‖`,
using `norm_mFourierCoeff3_le` (single coefficient ≤ L² norm) and `‖proj_j x‖ ≤ ‖proj_j‖·‖x‖`
(`ContinuousLinearMap.le_opNorm`).  Summing the `‖u‖·‖v‖`-free factors over the finite box
gives the constant `C`.  The hypothesis `hw` (finite support of `w`) is not needed for the
bound — the constant uses the actual coefficients `‖ŵ_i(-(k+l))‖` directly. -/
theorem galerkinConvection_bound (n : ℕ) (w : L2VF)
    (hw : velocityProjection_n n w = w) :
    ∃ C : ℝ, ∀ (u v : L2VF), |galerkinConvection n u v w| ≤ C * ‖u‖ * ‖v‖ := by
  -- The `‖u‖·‖v‖`-free per-summand factor.
  classical
  set D : Fin 3 → Fin 3 → (Fin 3 → ℤ) → (Fin 3 → ℤ) → ℝ :=
    fun i a k l => ‖L2VF_projComponentC a‖ * ‖(2 * (Real.pi : ℂ) * Complex.I * (l a : ℂ))‖ *
      ‖L2VF_projComponentC i‖ * ‖mFourierCoeff3 (L2VF_projComponentC i w) (-(k + l))‖ with hD
  refine ⟨∑ i : Fin 3, ∑ a : Fin 3, ∑ k ∈ fourierBox n, ∑ l ∈ fourierBox n, D i a k l,
    fun u v => ?_⟩
  rw [galerkinConvection]
  -- `|Re(Σ)| ≤ ‖Σ‖ ≤ ∑ ‖summand‖`.
  refine (abs_re_le_norm _).trans ?_
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_le_sum fun a _ => ?_
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_le_sum fun k _ => ?_
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_le_sum fun l _ => ?_
  -- Bound one summand norm by `D i a k l * ‖u‖ * ‖v‖`.
  rw [hD]
  -- Split the summand norm into the four factors, keeping the `‖2πIlₐ‖` block intact: two
  -- generic splits peel off `‖ûₐ(k)‖` and `‖2πIlₐ‖`, then a targeted split on `v̂ᵢ(l)·ŵᵢ`.
  rw [norm_mul, norm_mul,
    norm_mul (mFourierCoeff3 (L2VF_projComponentC i v) l)
      (mFourierCoeff3 (L2VF_projComponentC i w) (-(k + l)))]
  have hu : ‖mFourierCoeff3 (L2VF_projComponentC a u) k‖ ≤ ‖L2VF_projComponentC a‖ * ‖u‖ :=
    le_trans (norm_mFourierCoeff3_le (L2VF_projComponentC a u) k)
      ((L2VF_projComponentC a).le_opNorm u)
  have hv : ‖mFourierCoeff3 (L2VF_projComponentC i v) l‖ ≤ ‖L2VF_projComponentC i‖ * ‖v‖ :=
    le_trans (norm_mFourierCoeff3_le (L2VF_projComponentC i v) l)
      ((L2VF_projComponentC i).le_opNorm v)
  have huv : ‖mFourierCoeff3 (L2VF_projComponentC a u) k‖ *
      (‖2 * (Real.pi : ℂ) * Complex.I * (l a : ℂ)‖ *
        (‖mFourierCoeff3 (L2VF_projComponentC i v) l‖ *
          ‖mFourierCoeff3 (L2VF_projComponentC i w) (-(k + l))‖))
      ≤ (‖L2VF_projComponentC a‖ * ‖u‖) *
        (‖2 * (Real.pi : ℂ) * Complex.I * (l a : ℂ)‖ *
          ((‖L2VF_projComponentC i‖ * ‖v‖) *
            ‖mFourierCoeff3 (L2VF_projComponentC i w) (-(k + l))‖)) := by
    gcongr
  refine huv.trans (le_of_eq ?_)
  ring

end LerayHopf
