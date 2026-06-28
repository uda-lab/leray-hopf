import LerayHopf.AxiomaticClosure

open MeasureTheory Filter Topology Complex

/-!
# Finite-sum algebraic lemmas for the T³ Galerkin convection form (issue #22)

**Issue #22 — axiom removal for `torus3_NSForms_exist` (COMPLETE in this file).**

## What this file does

This file proves the **trilinearity** (additivity + ℝ-homogeneity in each slot), an
explicit **bilinear L² bound**, the **Galerkin antisymmetry over `Vₙ`**, and the
**box-level independence** (`galerkinConvection_level_step`/`_stable`) for
`galerkinConvection n` (finite sums over `fourierBox n`), plus the helper
`coeff_zero_outside_box` (Fourier support of `Vₙ`-elements).

It then isolates the genuine Mathlib-absent operator gap — the weak `(u·∇)v` extension of the
box-truncated form to all of `L²_σ` — into the single named hypothesis `TorusConvectionGap`, and
**proves `Torus3NSForms_of_gap : TorusConvectionGap → Nonempty Torus3NSForms` sorry-free**.  This
de-axiomatizes `torus3_NSForms_exist`: that fat axiom is **removed** (from `AxiomaticClosure.lean`)
and replaced by the strictly-thinner gap axiom `torusConvectionGap_exists` (:below), through which
the relocated capstone `exists_lerayHopf_torus3_axiomatic` is rerouted.  All trilinear / bound /
Galerkin-pin content is now sorry-free theorem content, not axiomatic.  **The file is sorry-free**
apart from the single marked gap axiom.  Mirrors the merged ℝ³ template
`LerayHopf/R3/ConvectionForm.lean` (`ConvectionGap` / `R3NSForms_of_gap`).

## Antisymmetry — proved over the Galerkin subspace `Vₙ`

`galerkinConvection n u v w = -galerkinConvection n u w v` is the standard Galerkin convection
antisymmetry.  It holds when the **test slots `v, w` lie in `Vₙ`** (finite Fourier support,
`velocityProjection_n n v = v` and `velocityProjection_n n w = w`) — and `galerkinConvection_antisymm`
proves exactly that.  For arbitrary `v, w : L2VF` the box-truncated form is genuinely NOT
antisymmetric (`box × box` is not invariant under `(k,l) ↦ (k,-(k+l))`; `neg_mem_fourierBox`
covers only `k ↦ -k`), so the two `Vₙ` hypotheses are necessary, not a convenience.

This `Vₙ` antisymmetry is the faithful piece of the unrestricted `Torus3NSForms.b_antisymm`
field: that field is derived (in `Torus3NSForms_of_gap`) from the gap field `b_antisymm_gap`, and
the non-truncated form is matched to this finite-box form via `b_galerkin` ← `b_galerkin_pin`.
The unrestricted antisymmetry over arbitrary `L²_σ` (which the box-truncated form does NOT satisfy)
is the honest residual carried by the thin gap axiom `torusConvectionGap_exists`; the fat axiom
`torus3_NSForms_exist` has been **removed**.

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
- `galerkinConvection_level_step`/`galerkinConvection_level_stable` — box-level independence of
  `galerkinConvection` once the box bounds the supports (well-posedness of the Galerkin pin)
- `TorusConvectionGap` — the isolated weak-convection-operator gap (mirror of ℝ³ `ConvectionGap`)
- `Torus3NSForms_of_gap` — sorry-free `TorusConvectionGap → Nonempty Torus3NSForms`
- `torus3_NSForms_exists` — theorem replacing the removed fat axiom, via the thin gap
- `exists_lerayHopf_torus3_axiomatic` — relocated capstone, rerouted through the thin gap

## Axiom status

One new thin axiom, `torusConvectionGap_exists` (the isolated torus weak-convection-operator
frontier: smooth-test bound / torus IBP that Mathlib lacks).  The fat `torus3_NSForms_exist` is
**removed**; all trilinear / bound / Galerkin-pin content is now sorry-free theorem content via
`Torus3NSForms_of_gap`.
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

/-! ### Level stability of `galerkinConvection` (independence of the box once it bounds supports) -/

set_option maxHeartbeats 1000000 in
/-- **Level stability (monotone step).**  If all three slots lie in `Vₘ`
(`velocityProjection_n m · = ·`) and `m ≤ n`, then truncating at the larger box `n` gives the
same value as truncating at `m`:
`galerkinConvection n u v w = galerkinConvection m u v w`.

Proof: `fourierBox m ⊆ fourierBox n` (`fourierBox_monotone`).  In the level-`n` sum, the `k`-sum
restricts to `fourierBox m` because the leading factor `û_a(k)` vanishes for `k ∉ fourierBox m`
(`coeff_zero_outside_box m u hu`), and the `l`-sum restricts to `fourierBox m` because the factor
`v̂_i(l)` vanishes for `l ∉ fourierBox m` (`coeff_zero_outside_box m v hv`).  The remaining
`fourierBox m × fourierBox m` sum is exactly `galerkinConvection m u v w`; the `w`-coefficient is
unchanged. -/
theorem galerkinConvection_level_step (m n : ℕ) (hmn : m ≤ n) (u v w : L2VF)
    (hu : velocityProjection_n m u = u) (hv : velocityProjection_n m v = v) :
    galerkinConvection n u v w = galerkinConvection m u v w := by
  classical
  have hsub : fourierBox m ⊆ fourierBox n := fourierBox_monotone hmn
  rw [galerkinConvection, galerkinConvection]
  refine congrArg Complex.re ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun a _ => ?_
  -- Restrict the outer `k`-sum from `fourierBox n` down to `fourierBox m`: the leading factor
  -- `û_a(k)` vanishes for `k ∉ fourierBox m`, so each dropped inner `l`-sum is zero.
  refine (Finset.sum_subset hsub ?_).symm.trans ?_
  · intro k _ hknotm
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [coeff_zero_outside_box m u hu a k hknotm, zero_mul]
  -- For each kept `k ∈ fourierBox m`, restrict the inner `l`-sum from `fourierBox n` to
  -- `fourierBox m`: the factor `v̂_i(l)` vanishes for `l ∉ fourierBox m`.
  refine Finset.sum_congr rfl fun k _ => ?_
  refine (Finset.sum_subset hsub ?_).symm
  intro l _ hlnotm
  rw [coeff_zero_outside_box m v hv i l hlnotm]
  ring

/-- **Level stability (general, symmetric form).**  If all three slots lie in `Vₘ` *and* in `Vₙ`,
then `galerkinConvection m u v w = galerkinConvection n u v w`.  Both truncations equal the
truncation at `max m n` (each is the larger box for the other), so they agree.

This is the consistency fact that makes a single total `b` pinned to `galerkinConvection` on every
`Vₙ` (the `Torus3NSForms.b_galerkin` shape, quantified over `n`) well-posed: the pinned value does
not depend on which box `n` is used, as long as it bounds the supports. -/
theorem galerkinConvection_level_stable (m n : ℕ) (u v w : L2VF)
    (hum : velocityProjection_n m u = u) (hvm : velocityProjection_n m v = v)
    (hun : velocityProjection_n n u = u) (hvn : velocityProjection_n n v = v) :
    galerkinConvection m u v w = galerkinConvection n u v w := by
  have hmle : m ≤ max m n := le_max_left m n
  have hnle : n ≤ max m n := le_max_right m n
  rw [← galerkinConvection_level_step m (max m n) hmle u v w hum hvm,
      ← galerkinConvection_level_step n (max m n) hnle u v w hun hvn]

/-! ### The isolated torus convection gap and the conditional concrete `Torus3NSForms` (issue #22)

This section mirrors the merged ℝ³ template `LerayHopf/R3/ConvectionForm.lean`
(`ConvectionGap` + `R3NSForms_of_gap`).  It isolates the genuine Mathlib-absent pillar behind
the project axiom `torus3_NSForms_exist` into a single named hypothesis `TorusConvectionGap`,
and proves the conditional `TorusConvectionGap → Nonempty Torus3NSForms` **sorry-free**, so that
the residual axiom shrinks from the fat structure-existence `torus3_NSForms_exist` to the thin
`torusConvectionGap_exists` below — the trilinear algebra, the L²-bound transfer, and the
Galerkin pin all become *theorem* content via `Torus3NSForms_of_gap`. -/

/-- **The isolated torus convection gap — the weak-convection-operator extension.**

`TorusConvectionGap` isolates the *genuine* Mathlib-absent pillar behind `torus3_NSForms_exist`:
the extension of the finite, proven box-truncated form `galerkinConvection` to a *total* operator
on `L²_σ(𝕋³)` with the analytic structure of `(u·∇)v`.  Mirrors ℝ³ `ConvectionGap`.

What is genuinely missing — and what this structure carries:

- `b`              — a total candidate convection form on all of `L²_σ(𝕋³)`;
- `b_galerkin_pin` — `b` *restricts* to the finite `galerkinConvection n` on Galerkin
                     subspaces `Vₙ` (the operator-extension content + the non-vacuity pin;
                     this is exactly the `Torus3NSForms.b_galerkin` shape, and the value is
                     well-posed across levels by `galerkinConvection_level_stable`);
- `b_multilinear` — `b` is realised by a genuine `ℝ`-trilinear-map tower
                     `B : L²_σ →ₗ[ℝ] L²_σ →ₗ[ℝ] L²_σ →ₗ[ℝ] ℝ` with `b u v w = B u v w`;
                     yields `b_add_{1,2,3}` / `b_smul_{1,2,3}` over arbitrary `L²_σ` from
                     `map_add` / `map_smul`, with **no continuity, no density**;
- `b_antisymm_gap`— antisymmetry in the last two slots over **arbitrary** `L²_σ`
                     (`b u v w = - b u w v`), the honest residual of the missing IBP /
                     divergence-theorem operator (`galerkinConvection_antisymm` proves only the
                     `Vₙ`-restricted version, so the unrestricted statement is genuinely part of
                     the frontier);
- `b_bound_test`  — the **smooth-test L² bound on the Galerkin-test diagonal**:
                     `|b u v w| ≤ C(w)·‖u‖·‖v‖` for `u, v, w` Galerkin tests, with `C` depending
                     only on `w`.  This is the genuine smooth-test estimate `|b| ≤ ‖∇w‖_∞‖u‖‖v‖`;
                     `galerkinConvection_bound n` proves a finite-level version with an
                     `n`-dependent constant, so the *uniform* (level-independent) constant here is
                     the analytic content the box-truncated bound does not supply;
- `b_cont_fixedTest` — joint L²-continuity of `(u,v) ↦ b u v w` at a **fixed Galerkin test** `w`
                     (the genuine bilinear continuity that transports `b_bound_test` to all
                     `u, v : L²_σ`);
- `galerkinTest_dense` — density of the Galerkin-test class in `L²_σ(𝕋³)` (TRUE by
                     `velocityProjection_n_tendsto`; carried as a field, mirroring ℝ³
                     `ConvectionGap.schwartz_dense`).

This is a **hypothesis** (data + Prop fields), **not** an `axiom`, and it never enters a theorem
*name*; the resulting `Torus3NSForms_of_gap` is explicitly conditional.

**No-smuggle audit.**  `TorusConvectionGap`
- contains **no** `Torus3NSForms` field and **no** `Nonempty Torus3NSForms` field;
- does **not** carry the trilinear `b_add_*` / `b_smul_*` / the full unrestricted `b_bound` ready
  made — those are *derived* in `Torus3NSForms_of_gap` (`b_add_*`/`b_smul_*` ← `b_multilinear`;
  the full `b_bound` over arbitrary `u, v` ← `b_bound_test` + `b_cont_fixedTest` +
  `galerkinTest_dense`);
- carries no `WeakFormNS`, energy-inequality, or solution content. -/
structure TorusConvectionGap where
  /-- The **total** candidate convection form on all of `L²_σ(𝕋³)`. -/
  b : L2Sigma → L2Sigma → L2Sigma → ℝ
  /-- **Operator-extension property + non-vacuity pin (the frontier).** On every Galerkin
  subspace `Vₙ`, `b` restricts to the finite box-truncated form `galerkinConvection n`.  This is
  exactly the `Torus3NSForms.b_galerkin` shape; the value is independent of the level `n` once it
  bounds the supports (`galerkinConvection_level_stable`), so the pin is well-posed.  It excludes
  `b = 0` since `galerkinConvection` is generically nonzero. -/
  b_galerkin_pin : ∀ (n : ℕ) (u v w : L2Sigma),
    velocityProjection_n n (u : L2VF) = (u : L2VF) →
    velocityProjection_n n (v : L2VF) = (v : L2VF) →
    velocityProjection_n n (w : L2VF) = (w : L2VF) →
    b u v w = galerkinConvection n (u : L2VF) (v : L2VF) (w : L2VF)
  /-- **Algebraic trilinear structure over arbitrary `L²_σ`.** `b` is realised by a genuine
  `ℝ`-trilinear-map tower `B` with `b u v w = B u v w`.  Yields `b_add_{1,2,3}` and
  `b_smul_{1,2,3}` directly from `B`'s `map_add` / `map_smul`. -/
  b_multilinear :
    ∃ B : L2Sigma →ₗ[ℝ] L2Sigma →ₗ[ℝ] L2Sigma →ₗ[ℝ] ℝ,
      ∀ (u v w : L2Sigma), b u v w = B u v w
  /-- **Antisymmetry in the last two slots over arbitrary `L²_σ`.** `b u v w = - b u w v` for all
  `u v w`.  The honest residual of the missing weak-`(u·∇)v` / IBP operator (`galerkinConvection`
  is antisymmetric only over `Vₙ`). -/
  b_antisymm_gap : ∀ (u v w : L2Sigma), b u v w = - b u w v
  /-- **Smooth-test L² bound on the Galerkin-test diagonal.** For Galerkin tests `u, v, w`,
  `|b u v w| ≤ C(w)·‖u‖·‖v‖` with `C` depending only on `w`.  The genuine smooth-test estimate;
  `galerkinConvection_bound n` gives only the finite-level (`n`-dependent constant) version. -/
  b_bound_test : ∀ (w : L2Sigma), IsGalerkinTest w →
    ∃ C : ℝ, ∀ (u v : L2Sigma), IsGalerkinTest u → IsGalerkinTest v →
      |b u v w| ≤ C * ‖(u : L2VF)‖ * ‖(v : L2VF)‖
  /-- **Joint L²-continuity of `(u,v) ↦ b u v w` at a fixed Galerkin test `w`.** The genuine
  bilinear continuity that, with `galerkinTest_dense`, transports `b_bound_test` to all
  `u, v : L²_σ`. -/
  b_cont_fixedTest : ∀ (w : L2Sigma), IsGalerkinTest w →
    Continuous (fun p : L2Sigma × L2Sigma => b p.1 p.2 w)
  /-- **Density of the Galerkin-test class in `L²_σ(𝕋³)`.** Every `L²_σ` field is an L²-limit of
  Galerkin tests.  TRUE by `velocityProjection_n_tendsto`; carried as a field (mirroring ℝ³
  `ConvectionGap.schwartz_dense`). -/
  galerkinTest_dense : ∀ (u : L2Sigma),
    ∃ s : ℕ → L2Sigma, (∀ n, IsGalerkinTest (s n)) ∧
      Filter.Tendsto s Filter.atTop (nhds u)

/-- **The conditional concrete `Torus3NSForms` — a genuine derivation (issue #22).**

Given the isolated `TorusConvectionGap`, a genuine `Torus3NSForms` exists, **sorry-free**.  Each
`Torus3NSForms` field is obtained as follows (mirroring ℝ³ `R3NSForms_of_gap`):

- `b_add_{1,2,3}` — from `g.b_multilinear`: rewrite `g.b _ _ _ = B _ _ _`, close by `B`'s
                  `map_add`.  Works for *arbitrary* `u v w : L²_σ`, no continuity/density;
- `b_smul_{1,2,3}` — same, via `B`'s `map_smul`;
- `b_antisymm`  — directly from `g.b_antisymm_gap`;
- `b_bound`     — from `g.b_bound_test` (fixed constant `C(w)` on the test diagonal) +
                  `g.b_cont_fixedTest` + `g.galerkinTest_dense`, via the `le_of_tendsto_of_tendsto`
                  limiting argument (the box-truncated `galerkinConvection_bound` is *not* used
                  here: its constant is `n`-dependent, whereas `b_bound` needs a single `C(w)`);
- `b_galerkin`  — directly from `g.b_galerkin_pin`.

So `TorusConvectionGap` does **not** hand over the quantitative `Torus3NSForms` content ready-made:
the unrestricted bound is derived from the test-diagonal bound through fixed-test continuity and
density; only the algebraic trilinear/antisymmetry content is asserted, as the honest residual of
the missing weak operator.  Non-vacuity flows through `g.b_galerkin_pin` (excludes `b = 0`). -/
theorem Torus3NSForms_of_gap (g : TorusConvectionGap) : Nonempty Torus3NSForms := by
  obtain ⟨B, hB⟩ := g.b_multilinear
  refine ⟨{ b := g.b
          , b_antisymm := ?b_antisymm
          , b_add_1 := ?b_add_1
          , b_add_2 := ?b_add_2
          , b_add_3 := ?b_add_3
          , b_smul_1 := ?b_smul_1
          , b_smul_2 := ?b_smul_2
          , b_smul_3 := ?b_smul_3
          , b_bound := ?b_bound
          , b_galerkin := ?b_galerkin }⟩
  case b_antisymm =>
    exact g.b_antisymm_gap
  case b_add_1 =>
    intro u u' v w
    simp only [hB, map_add, LinearMap.add_apply]
  case b_add_2 =>
    intro u v v' w
    simp only [hB, map_add, LinearMap.add_apply]
  case b_add_3 =>
    intro u v w w'
    simp only [hB, map_add]
  case b_smul_1 =>
    intro c u v w
    simp only [hB, map_smul, LinearMap.smul_apply, smul_eq_mul]
  case b_smul_2 =>
    intro c u v w
    simp only [hB, map_smul, LinearMap.smul_apply, smul_eq_mul]
  case b_smul_3 =>
    intro c u v w
    simp only [hB, map_smul, smul_eq_mul]
  case b_bound =>
    -- Derive the unrestricted L² bound from the test-diagonal bound + fixed-test continuity
    -- + density (the box-truncated `galerkinConvection_bound` is NOT used — its constant is
    -- level-dependent; here we need a single `C(w)`).
    intro w hw
    obtain ⟨C, hC⟩ := g.b_bound_test w hw
    refine ⟨C, fun u v => ?_⟩
    -- Approximate `u, v` by Galerkin-test sequences.
    obtain ⟨su, hsu_test, hsu_lim⟩ := g.galerkinTest_dense u
    obtain ⟨sv, hsv_test, hsv_lim⟩ := g.galerkinTest_dense v
    have hcont := g.b_cont_fixedTest w hw
    -- The bound holds on each diagonal term.
    have hbound_seq : ∀ n : ℕ,
        |g.b (su n) (sv n) w| ≤ C * ‖(su n : L2VF)‖ * ‖(sv n : L2VF)‖ :=
      fun n => hC (su n) (sv n) (hsu_test n) (hsv_test n)
    -- Diagonal sequence converges in the product topology.
    have hlim_pair : Filter.Tendsto (fun n => (su n, sv n)) Filter.atTop (nhds (u, v)) :=
      (Prod.tendsto_iff _ _).mpr ⟨hsu_lim, hsv_lim⟩
    -- `b (su n) (sv n) w → b u v w` by continuity.
    have hlim_b : Filter.Tendsto (fun n => g.b (su n) (sv n) w)
        Filter.atTop (nhds (g.b u v w)) :=
      (hcont.tendsto (u, v)).comp hlim_pair
    -- Norms converge.
    have hlim_norm_u : Filter.Tendsto (fun n => ‖(su n : L2VF)‖) Filter.atTop
        (nhds ‖(u : L2VF)‖) :=
      (continuous_norm.tendsto _).comp ((continuous_subtype_val.tendsto _).comp hsu_lim)
    have hlim_norm_v : Filter.Tendsto (fun n => ‖(sv n : L2VF)‖) Filter.atTop
        (nhds ‖(v : L2VF)‖) :=
      (continuous_norm.tendsto _).comp ((continuous_subtype_val.tendsto _).comp hsv_lim)
    have hlim_rhs : Filter.Tendsto (fun n => C * ‖(su n : L2VF)‖ * ‖(sv n : L2VF)‖)
        Filter.atTop (nhds (C * ‖(u : L2VF)‖ * ‖(v : L2VF)‖)) :=
      ((tendsto_const_nhds.mul hlim_norm_u).mul hlim_norm_v)
    -- Pass the bound to the limit.
    apply le_of_tendsto_of_tendsto
      ((continuous_abs.tendsto _).comp hlim_b)
      hlim_rhs
    exact Filter.Eventually.of_forall (fun n => hbound_seq n)
  case b_galerkin =>
    exact g.b_galerkin_pin

/-! ### Remarks on `torusConvectionGap_exists` and `torus3_NSForms_exists` (issues #22 and #53) -/

/-! **`torusConvectionGap_exists` is now a PROVED THEOREM** (issue #53), no longer an axiom.
The determined-form construction in `LerayHopf/TorusConvectionExtension.lean`
(`torusConvectionGap_holds`, sorry-free) establishes `Nonempty TorusConvectionGap`.
`LerayHopf.torusConvectionGap_exists` and `LerayHopf.torus3_NSForms_exists` are both theorems
declared in `TorusConvectionExtension.lean`; they are visible here transitively via the import
`LerayHopf.TorusConvectionExtension` (added to `TorusGalerkinODECapstone`). -/

/-! **Main existence theorem on 𝕋³ (axiomatic) — RELOCATED (issue #24).**

`exists_lerayHopf_torus3_axiomatic` now lives in `LerayHopf/TorusGalerkinODECapstone.lean`,
downstream of this file.  The relocation is forced by the issue-#24 discharge of
`galerkin_ode_solution`: the capstone sources its per-`n` Galerkin sequence from the axiom-free
`galerkinSolutionData_torus` (`TorusGalerkinODESolve.lean`) over the finite-dim `velocitySpan n`.
That ODE chain imports this file, so the capstone must sit below it in the DAG to stay acyclic.
The building blocks it uses (`torus3_NSForms_exists`, `build_galerkin_package_of_galSeq`,
`exists_lerayHopf_from_package_full`) remain defined upstream and are visible downstream through the
import.  See `LerayHopf/Core.lean` for the axiom-free layer; `LerayHopf/TorusAxiomatic.lean`
re-exports the relocated capstone. -/

end LerayHopf
