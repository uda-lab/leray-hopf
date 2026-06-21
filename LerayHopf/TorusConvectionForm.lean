import LerayHopf.AxiomaticClosure

open MeasureTheory Filter Topology Complex

/-!
# Finite-sum algebraic lemmas for the T³ Galerkin convection form (issue #22)

**Issue #22 — begin axiom removal for `torus3_NSForms_exist`.**

## What this file does and does not do

This file proves the **trilinearity** (additivity + ℝ-homogeneity in each slot), an
explicit **bilinear L² bound**, and the **Galerkin antisymmetry over `Vₙ`** for
`galerkinConvection n` (finite sums over `fourierBox n`), plus the helper
`coeff_zero_outside_box` (Fourier support of `Vₙ`-elements).  **The file is sorry-free.**

It does NOT build a total `b : L2Sigma → L2Sigma → L2Sigma → ℝ` extending
`galerkinConvection` to all of `L²_σ`: a total trilinear form extending the box-truncated
form is the genuine Mathlib-absent operator gap (weak `(u·∇)v` on Lp), out of scope here.

## Antisymmetry — proved over the Galerkin subspace `Vₙ`

`galerkinConvection n u v w = -galerkinConvection n u w v` is the standard Galerkin convection
antisymmetry.  It holds when the **test slots `v, w` lie in `Vₙ`** (finite Fourier support,
`velocityProjection_n n v = v` and `velocityProjection_n n w = w`) — and `galerkinConvection_antisymm`
proves exactly that.  For arbitrary `v, w : L2VF` the box-truncated form is genuinely NOT
antisymmetric (`box × box` is not invariant under `(k,l) ↦ (k,-(k+l))`; `neg_mem_fourierBox`
covers only `k ↦ -k`), so the two `Vₙ` hypotheses are necessary, not a convenience.

This `Vₙ` antisymmetry is the faithful piece of the unrestricted `Torus3NSForms.b_antisymm`
field: that field is witnessed by the genuine non-truncated `∫ (u·∇)v·w` convection form and
matched to this finite-box form via `b_galerkin`.  The remaining axiom `torus3_NSForms_exist`
in `AxiomaticClosure.lean` is kept (the total `(u·∇)v` operator on `Lp` is Mathlib-absent), but
no longer rests on any unproved antisymmetry over `Vₙ`.

## Declarations added (all sorry-free)

- `coeff_zero_outside_box` — Fourier coeff of `Vₙ` elements vanishes outside `fourierBox n`
- `norm_mFourierCoeff3_le` — single Fourier coefficient ≤ L² norm (Bessel/`lp` bound)
- `galerkinConvection_add_1/2/3` — additivity in each slot (`Finset.sum_add_distrib`)
- `galerkinConvection_smul_1/2/3` — ℝ-homogeneity in each slot (`Finset.mul_sum` + cast)
- `galerkinConvection_bound` — explicit bilinear L² bound (triangle inequality + Bessel +
  operator-norm bound; no convergence, finite sums only)
- `neg_add_involutive` — the involution identity `-(k + -(k + l)) = l` for the antisymmetry reindex
- `galerkinConvection_antisymm` — Galerkin antisymmetry over `Vₙ` (`v, w ∈ Vₙ`, `u` div-free):
  per-`k` restriction to the `σ_k`-invariant set `C_k`, involution reindex `l ↦ -(k+l)`, and the
  divergence-free identity `∑_a kₐ ûₐ(k) = 0` close the cancellation (Temam II.§1, RRS §3.2)

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

/-! ### Antisymmetry of `galerkinConvection n` — over the Galerkin subspace `Vₙ` -/

/-- The involution `σ_k : l ↦ -(k+l)` on the symmetric index set `C_k` used in the antisymmetry
reindex.  On `C_k := (fourierBox n).filter (fun l => -(k+l) ∈ fourierBox n)` it is a
self-inverse bijection (an involution): `σ_k (σ_k l) = l` and `σ_k` maps `C_k` to itself. -/
private lemma neg_add_involutive (k l : Fin 3 → ℤ) : -(k + -(k + l)) = l := by
  funext i; simp [Pi.neg_apply]

/-- **Antisymmetry of the Galerkin convection form over the test subspace `Vₙ`.**

For `u ∈ L²_σ` (divergence-free) and test slots `v, w ∈ Vₙ` (finite Fourier support,
`velocityProjection_n n v = v`, `velocityProjection_n n w = w`):
`galerkinConvection n u v w = -galerkinConvection n u w v`.

This is the standard Faedo–Galerkin convection antisymmetry (Temam II.§1, RRS §3.2): it is the
faithful, truthful piece of the unrestricted `Torus3NSForms.b_antisymm` field, which is
witnessed by the genuine non-truncated `∫ (u·∇)v·w` convection form and matched to this
finite-box form via `b_galerkin`.

**Why `v, w ∈ Vₙ` is required.** The box-truncated form leaves `m = -(k+l)` unrestricted, so
the raw index set `box × box` is NOT invariant under the involution `(k,l) ↦ (k,-(k+l))` that
antisymmetry needs (`neg_mem_fourierBox` covers only `k ↦ -k`).  Finite support of `u` alone
does not rescue it.  Under `hv, hw`, the coefficients `v̂_i, ŵ_i` vanish outside `box`
(`coeff_zero_outside_box`), so every nonzero summand has `l ∈ box` AND `-(k+l) ∈ box`; both
sums collapse to the `σ_k`-invariant set `C_k`, where the `l ↔ -(k+l)` reindex is a genuine
involution.  The cancellation `lₐ + (-(k+l))ₐ = -kₐ` is then killed by `∑_a kₐ û_a(k) = 0`
(`DivFreeL2 u`). -/
theorem galerkinConvection_antisymm (n : ℕ) (u : L2Sigma) (v w : L2VF)
    (hv : velocityProjection_n n v = v) (hw : velocityProjection_n n w = w) :
    galerkinConvection n (u : L2VF) v w = -galerkinConvection n (u : L2VF) w v := by
  classical
  -- Divergence-free condition on `u`.
  have hdiv : DivFreeL2 (u : L2VF) := (mem_L2Sigma_iff _).mp u.2
  -- Abbreviations for the three coefficient families.
  set U : Fin 3 → (Fin 3 → ℤ) → ℂ :=
    fun a k => mFourierCoeff3 (L2VF_projComponentC a (u : L2VF)) k with hU
  set V : Fin 3 → (Fin 3 → ℤ) → ℂ :=
    fun i l => mFourierCoeff3 (L2VF_projComponentC i v) l with hV
  set W : Fin 3 → (Fin 3 → ℤ) → ℂ :=
    fun i l => mFourierCoeff3 (L2VF_projComponentC i w) l with hW
  -- Support facts from `hv`, `hw` (coefficients vanish outside the box).
  have hVsupp : ∀ (i : Fin 3) (l : Fin 3 → ℤ), l ∉ fourierBox n → V i l = 0 := by
    intro i l hl; exact coeff_zero_outside_box n v hv i l hl
  have hWsupp : ∀ (i : Fin 3) (l : Fin 3 → ℤ), l ∉ fourierBox n → W i l = 0 := by
    intro i l hl; exact coeff_zero_outside_box n w hw i l hl
  -- The two complex sums (before taking `Re`).
  set A : ℂ := ∑ i : Fin 3, ∑ a : Fin 3, ∑ k ∈ fourierBox n, ∑ l ∈ fourierBox n,
      U a k * ((2 * (Real.pi : ℂ) * Complex.I * (l a : ℂ)) * (V i l * W i (-(k + l)))) with hA
  set A' : ℂ := ∑ i : Fin 3, ∑ a : Fin 3, ∑ k ∈ fourierBox n, ∑ l ∈ fourierBox n,
      U a k * ((2 * (Real.pi : ℂ) * Complex.I * (l a : ℂ)) * (W i l * V i (-(k + l)))) with hA'
  -- Reduce to: the complex sums add to zero.
  suffices hsum : A + A' = 0 by
    have hre : A.re = -A'.re := by
      have := congrArg Complex.re hsum
      simpa [Complex.add_re] using eq_neg_of_add_eq_zero_left this
    rw [galerkinConvection, galerkinConvection]
    exact hre
  -- The two-factor `2π i` constant.
  set c : ℂ := 2 * (Real.pi : ℂ) * Complex.I with hc
  -- The symmetric (σ_k-invariant) inner index set.
  set Cset : (Fin 3 → ℤ) → Finset (Fin 3 → ℤ) :=
    fun k => (fourierBox n).filter (fun l => -(k + l) ∈ fourierBox n) with hCset
  -- σ_k maps `Cset k` to itself (involution).
  have hmem_C : ∀ (k l : Fin 3 → ℤ), l ∈ Cset k → -(k + l) ∈ Cset k := by
    intro k l hl
    rw [hCset, Finset.mem_filter] at hl ⊢
    refine ⟨hl.2, ?_⟩
    rw [neg_add_involutive]; exact hl.1
  -- The reindexed-and-combined per-`(i,a,k)` block, summed over `a`, vanishes.
  -- Step 1: rewrite `A + A'` as a single triple sum of per-`(i,a,k)` blocks.
  have key : A + A' = ∑ i : Fin 3, ∑ a : Fin 3, ∑ k ∈ fourierBox n,
      ∑ l ∈ Cset k, c * (-(k a : ℂ)) * U a k * (V i l * W i (-(k + l))) := by
    rw [hA, hA', ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    -- Restrict both `l`-sums from the box to `Cset k` (zero outside).
    have hPrestr : ∑ l ∈ fourierBox n,
          U a k * (c * (l a : ℂ) * (V i l * W i (-(k + l)))) =
        ∑ l ∈ Cset k, U a k * (c * (l a : ℂ) * (V i l * W i (-(k + l)))) := by
      refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
      intro l hl hlC
      have : -(k + l) ∉ fourierBox n := by
        simp only [hCset, Finset.mem_filter, not_and] at hlC; exact hlC hl
      rw [hWsupp i _ this]; ring
    have hQrestr : ∑ l ∈ fourierBox n,
          U a k * (c * (l a : ℂ) * (W i l * V i (-(k + l)))) =
        ∑ l ∈ Cset k, U a k * (c * (l a : ℂ) * (W i l * V i (-(k + l)))) := by
      refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
      intro l hl hlC
      have : -(k + l) ∉ fourierBox n := by
        simp only [hCset, Finset.mem_filter, not_and] at hlC; exact hlC hl
      rw [hVsupp i _ this]; ring
    -- Reindex the `Q`-sum over `Cset k` by the involution `σ_k`.
    have hQrei : ∑ l ∈ Cset k, U a k * (c * (l a : ℂ) * (W i l * V i (-(k + l)))) =
        ∑ l ∈ Cset k, U a k * (c * ((-(k + l)) a : ℂ) * (W i (-(k + l)) * V i l)) := by
      refine Finset.sum_nbij' (fun l => -(k + l)) (fun l => -(k + l)) ?_ ?_ ?_ ?_ ?_
      · intro l hl; exact hmem_C k l hl
      · intro l hl; exact hmem_C k l hl
      · intro l _; rw [neg_add_involutive]
      · intro l _; rw [neg_add_involutive]
      · intro l _; rw [neg_add_involutive]
    -- Combine the `c·l_a` and `c·(-(k+l))_a` terms into `c·(-k_a)`.
    rw [hPrestr, hQrestr, hQrei, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    have hka : ((-(k + l)) a : ℂ) = -(k a : ℂ) - (l a : ℂ) := by
      simp [Pi.neg_apply, Pi.add_apply]; push_cast; ring
    rw [hka]; ring
  -- Now sum over `a` and kill via divergence-freeness.
  rw [key]
  refine Finset.sum_eq_zero fun i _ => ?_
  -- Move `∑_a` to the innermost position (swap past `∑_k` then `∑_l`).
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun l _ => ?_
  -- Factor the `a`-independent part out and apply the divergence-free identity.
  have hfac : ∑ a : Fin 3, c * (-(k a : ℂ)) * U a k * (V i l * W i (-(k + l)))
      = -(c * (V i l * W i (-(k + l)))) *
          (∑ a : Fin 3, (k a : ℂ) * U a k) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  rw [hfac, hdiv k, mul_zero]

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
