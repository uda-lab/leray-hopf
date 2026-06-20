import LerayHopf.AxiomaticClosure
import Mathlib.Topology.Algebra.InfiniteSum.Basic

open MeasureTheory Filter Topology Complex

/-!
# Concrete T³ convection form and `Nonempty Torus3NSForms`

**Issue #22 — removal of `torus3_NSForms_exist`.**

This file constructs a concrete witness `torusNSFormsWitness : Torus3NSForms` by
defining the trilinear convection form `b_torus : L2Sigma → L2Sigma → L2Sigma → ℝ`
as the infinite Fourier-coefficient sum (convolution-structure-constant form):

  `b_torus u v w = ∑ i, ∑ a, ∑' k, ∑' l, Re [ û_a(k) · (2πi lₐ) · v̂ᵢ(l) · ŵᵢ(-(k+l)) ]`

This is the infinite-series extension of `galerkinConvection n` to all wavenumbers.
When `u, v, w ∈ Vₙ` (Galerkin subspace with support in `fourierBox n`), the tsums
reduce to the finite sums of `galerkinConvection n`, giving the `b_galerkin` field.

## Fields of `Torus3NSForms` — proved vs sorried

**Proved (definitional / algebraic):**
- `b_galerkin` — `b_torus` agrees with `galerkinConvection n` on `Vₙ`

**Scaffolded (honest sorries — lean-prover targets):**
- `b_add_1`, `b_add_2`, `b_add_3` — additivity in each slot
  (need absolute summability of the double tsum to exchange `tsum` and `add`)
- `b_smul_1`, `b_smul_2`, `b_smul_3` — ℝ-homogeneity in each slot
  (same summability gate; each `simp_rw [map_smul]` step is mechanical once admitted)
- `b_antisymm` — antisymmetry `b u v w = -b u w v`
  (Fourier IBP + divergence-free; see analytic frontier below)
- `b_bound` — smooth-test L² bound `|b u v w| ≤ C(w)‖u‖‖v‖` for `IsGalerkinTest w`
  (requires Young's convolution for ℤ³; see analytic frontier below)

## Analytic frontier

### Antisymmetry (gap `b_antisymm`)

The identity `b(u,v,w) = -b(u,w,v)` is the Fourier-space expression of torus IBP:
  `∫_{𝕋³} (u·∇)v · w = -∫_{𝕋³} (u·∇)w · v`
Proof sketch: substitute `m = -(k+l)` in the `∑' l` index, use symmetry
`∑_a (k+l)_a · û_a(k) = 0` (from `DivFreeL2 u`, the Fourier div-free condition).
**Blocked by:** Mathlib lacks (1) a proof that the double tsum `∑' k ∑' l ...` is
absolutely summable for `u, v, w ∈ L²_σ` (needs ℓ² * ℓ² → ℓ¹ Young convolution for
ℤ³), and (2) a torus integration-by-parts operator for `(u·∇)v` on L²(𝕋³).

### Smooth-test bound (gap `b_bound`)

For `IsGalerkinTest w` (i.e. `w ∈ Vₙ` for some `n`), the sum over `l` is finite
(support in `fourierBox n`), and the bound becomes:
  `|b_torus u v w| ≤ (∑_{l ∈ fourierBox n} ∑_a |2π l_a ŵ_a(l)|) · ‖û‖_{ℓ²} · ‖v̂‖_{ℓ²}`
where the Cauchy–Schwarz inequality on ℓ² gives ‖û‖_{ℓ²} = ‖u‖_{L²}.
**Blocked by:** (A) `b_antisymm` not yet proved (would reduce to bounding `b(u,w,v)`
via `‖∇w‖_{L∞}`), and (B) the Cauchy–Schwarz/Young step on the infinite sum over `k`
(needs a convolution bound `ℓ²(ℤ³) * ℓ¹(ℤ³) ↪ ℓ²(ℤ³)`, which is not in Mathlib for
ℤ³).

## Zero new axioms

No `axiom`, `opaque`, `constant`, or `unsafe` is introduced. Every gap is an honest
`-- ALLOW_SORRY:` with the exact Mathlib-gap description above.

## Relation to `torus3_NSForms_exist`

`torus3_NSForms_nonempty` below proves `Nonempty Torus3NSForms` from `torusNSFormsWitness`,
and is a sorry-carrying (but non-axiomatic) replacement for the axiom
`torus3_NSForms_exist` in `AxiomaticClosure.lean`.  Once all sorries in this file are
discharged, the axiom can be removed and replaced by this theorem.
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

/-- If `u ∈ Vₙ` (i.e. `velocityProjection_n n u = u`), then the `j`-th Fourier
coefficient of `u` vanishes for `k ∉ fourierBox n`. -/
private lemma coeff_zero_outside_box (n : ℕ) (u : L2VF)
    (hu : velocityProjection_n n u = u) (j : Fin 3) (k : Fin 3 → ℤ)
    (hk : k ∉ fourierBox n) :
    mFourierCoeff3 (L2VF_projComponentC j u) k = 0 := by
  have hcomm := velocityProjection_n_component_comm n u j
  rw [hu] at hcomm
  rw [← hcomm, fourierProjection_n_mFourierCoeff, if_neg hk]

/-! ### Definition of the concrete T³ convection form -/

/-- The **infinite Fourier convolution trilinear form**: the T³ convection form
`b(u,v,w) = ∫_{𝕋³} ((u·∇)v)·w` expressed as a double tsum over all wavenumbers.

This extends `galerkinConvection n` to all of `L²_σ`: the definition replaces the
finite `Finset.sum` over `fourierBox n` in `galerkinConvection` with `∑'` over all
of `Fin 3 → ℤ`. When `u, v, w ∈ Vₙ`, the terms outside `fourierBox n` vanish and
the tsum reduces to the Finset sum (see `b_torus_galerkin`). -/
noncomputable def b_torus (u v w : L2Sigma) : ℝ :=
  ∑ i : Fin 3, ∑ a : Fin 3,
    ∑' (k : Fin 3 → ℤ), ∑' (l : Fin 3 → ℤ),
      ((mFourierCoeff3 (L2VF_projComponentC a (u : L2VF)) k) *
       ((2 * (Real.pi : ℂ) * I * (l a : ℂ)) *
       (mFourierCoeff3 (L2VF_projComponentC i (v : L2VF)) l *
        mFourierCoeff3 (L2VF_projComponentC i (w : L2VF)) (-(k + l))))).re

/-! ### Trilinearity in each slot -/

/-- `b_torus` is additive in the first slot. -/
theorem b_torus_add_1 (u u' v w : L2Sigma) :
    b_torus (u + u') v w = b_torus u v w + b_torus u' v w := by
  simp only [b_torus, mFourierCoeff3_projComponentC_add, add_mul,
    Complex.add_re]
  -- Need: `tsum` commutes with addition; requires summability of each series.
  -- For u, u' ∈ L², the series `∑' k, ∑' l, (û_a(k) * ... ).re` must be absolutely
  -- summable — this is the same Young-convolution gap as `b_torus_antisymm`.
  sorry -- ALLOW_SORRY: trilinearity slot 1; tsum + add commutation needs absolute summability (Young convolution ℤ³); lean-prover target; same gap as b_antisymm

/-- `b_torus` is ℝ-homogeneous in the first slot. -/
theorem b_torus_smul_1 (c : ℝ) (u v w : L2Sigma) :
    b_torus (c • u) v w = c * b_torus u v w := by
  simp only [b_torus, mFourierCoeff3_projComponentC_smul]
  sorry -- ALLOW_SORRY: trilinearity slot 1 scalar; tsum_mul_left needs summability; lean-prover target

/-- `b_torus` is additive in the second slot. -/
theorem b_torus_add_2 (u v v' w : L2Sigma) :
    b_torus u (v + v') w = b_torus u v w + b_torus u v' w := by
  simp only [b_torus, mFourierCoeff3_projComponentC_add]
  sorry -- ALLOW_SORRY: trilinearity slot 2; tsum + add commutation needs absolute summability; lean-prover target

/-- `b_torus` is ℝ-homogeneous in the second slot. -/
theorem b_torus_smul_2 (c : ℝ) (u v w : L2Sigma) :
    b_torus u (c • v) w = c * b_torus u v w := by
  simp only [b_torus, mFourierCoeff3_projComponentC_smul]
  sorry -- ALLOW_SORRY: trilinearity slot 2 scalar; needs summability; lean-prover target

/-- `b_torus` is additive in the third slot. -/
theorem b_torus_add_3 (u v w w' : L2Sigma) :
    b_torus u v (w + w') = b_torus u v w + b_torus u v w' := by
  simp only [b_torus, mFourierCoeff3_projComponentC_add]
  sorry -- ALLOW_SORRY: trilinearity slot 3; same summability gap; lean-prover target

/-- `b_torus` is ℝ-homogeneous in the third slot. -/
theorem b_torus_smul_3 (c : ℝ) (u v w : L2Sigma) :
    b_torus u v (c • w) = c * b_torus u v w := by
  simp only [b_torus, mFourierCoeff3_projComponentC_smul]
  sorry -- ALLOW_SORRY: trilinearity slot 3 scalar; needs summability; lean-prover target

/-! ### Antisymmetry — analytic frontier -/

/-- **Antisymmetry `b_torus u v w = -b_torus u w v`.**

The torus IBP identity `∫(u·∇)v·w = -∫(u·∇)w·v` (for div-free `u`) translates
in Fourier space to a signed index swap `l ↦ -(k+l)` combined with the
divergence-free condition `∑_a (l_a) û_a(k) = 0`.

**Analytic frontier:**

(1) *Absolute summability of the double series.* The argument requires rearranging
`∑' k ∑' l f(k,l)` by the bijection `(k,l) ↦ (k, -(k+l))`. This is valid only when
the double series is absolutely summable.  Absolute summability of
  `∑' k ∑' l |û_a(k)| · |l_a| · |v̂_i(l)| · |ŵ_i(-(k+l))|`
is a Young-type convolution inequality for `ℤ³`: if `(û_a(k))_k ∈ ℓ²` and
`(l_a · v̂_i(l))_l ∈ ℓ²` (true when `v ∈ H¹`) then their convolution is in `ℓ¹`
(Young's `ℓ² * ℓ² ↪ ℓ¹`). Mathlib does not yet have this for `ℤ³` with the
required explicit constants.

(2) *Divergence-free cancellation.* After the index swap, the sum over `a` of
`û_a(k) · (k+l)_a` equals zero by `DivFreeL2 u` (the Fourier divergence-free
condition). Translating `DivFreeL2` (which states `∑_j (m_j : ℂ) * û_j(m) = 0`
for all `m`) requires identifying `m = k + l` correctly. This step is algebraic
once (1) is resolved and Lean can rearrange the series.

References: Temam II.§1, §2; Constantin–Foias §1.4. -/
theorem b_torus_antisymm (u v w : L2Sigma) :
    b_torus u v w = -b_torus u w v := by
  -- TODO: prove absolute summability of the double tsum (Young's ℓ²*ℓ² ↪ ℓ¹ for ℤ³,
  --   currently absent from Mathlib for the 3-torus in this generality).
  -- TODO: apply the bijection `(k, l) ↦ (k, -(k+l))` under the tsum to swap v and w slots.
  -- TODO: use `DivFreeL2 u` (i.e., `∑_a (m a : ℂ) * mFourierCoeff3 (L2VF_projComponentC a u) m = 0`
  --   for `m = k + l`) to cancel the remaining term.
  sorry -- ALLOW_SORRY: antisymmetry of b_torus; blocked by (1) missing Young ℓ²*ℓ² ↪ ℓ¹ for ℤ³ in Mathlib; (2) missing torus IBP / DivFreeL2 tsum rearrangement; Temam II.§1

/-! ### Smooth-test convection bound — analytic frontier -/

/-- **Smooth-test L² bound:** for Galerkin test functions `w`, the convection form is
L²-bounded: `|b_torus u v w| ≤ C(w) · ‖u‖_{L²} · ‖v‖_{L²}`.

When `IsGalerkinTest w` (i.e. `w ∈ Vₙ` for some `n`), the `l`-sum in `b_torus` is
a finite sum over `fourierBox n` (since `ŵ_i(l) = 0` for `l ∉ fourierBox n`).
Then:
  `|b_torus u v w| = |∑ i ∑ a ∑' k ∑_{l ∈ fourierBox n} ...|`
The remaining `∑' k` is a convolution of `(û_a(k))_k ∈ ℓ²(ℤ³)` with the fixed
sequence `(ŵ_i(-(k+l)))_{k}` (also in `ℓ²` since `w ∈ L²`), with the derivative
prefactor `|2π l_a| · |v̂_i(l)|` playing the role of a weight (finite since `l ∈ fourierBox n`).
Cauchy–Schwarz then gives `|∑' k (â(k)) · (b̂(k))| ≤ ‖a‖_{ℓ²} · ‖b‖_{ℓ²}`.

**Analytic frontier:**

Gap (A): `b_torus_antisymm` is not yet proved. The standard route uses antisymmetry:
  `b(u,v,w) = -b(u,w,v)`, then bounds `|b(u,w,v)| ≤ ‖∇w‖_{L∞}‖u‖_{L²}‖v‖_{L²}`.

Gap (B): The direct Cauchy–Schwarz route needs `‖(∑_{l ∈ box} ... )‖_{ℓ²(k)} < ∞` —
  an `ℓ¹ * ℓ² ↪ ℓ²` convolution estimate (Young's inequality for `ℤ³` sequences
  in Mathlib; the specific required form `NNNorm.continuous_sum_convolution` is absent).

References: Temam II.§1; Ladyzhenskaya §2.2. -/
theorem b_torus_bound (w : L2Sigma) (hw : IsGalerkinTest w) :
    ∃ C : ℝ, ∀ (u v : L2Sigma), |b_torus u v w| ≤ C * ‖(u : L2VF)‖ * ‖(v : L2VF)‖ := by
  -- TODO (Gap A): prove b_torus_antisymm, then use ‖∇w‖_{L∞} < ∞ for trig polynomials
  --   (w ∈ Vₙ implies w is a finite Fourier sum, hence C∞).
  -- TODO (Gap B direct): obtain n s.t. `velocityProjection_n n (w : L2VF) = w`;
  --   the l-sum reduces to `l ∈ fourierBox n`; bound `|∑' k ...)| ≤ ‖û(·)‖_{ℓ²} · ‖M_w(·)‖_{ℓ²}`
  --   where `M_w(k) = ∑_{l ∈ box} (2π l_a) ŵ_i(l) v̂_i(k-(-l))` is in ℓ² by v ∈ L².
  -- Explicit constant: C = ∑_{l ∈ fourierBox n} ∑_i ∑_a (2π |l_a|) · |ŵ_i(-(k+l))| · (Finset.card (fourierBox n)).
  sorry -- ALLOW_SORRY: smooth-test L² bound; blocked by (A) b_torus_antisymm + (B) missing Young's ℓ¹*ℓ² ↪ ℓ² for ℤ³ sequences in Mathlib; TRUE for IsGalerkinTest w; Temam II.§1

/-! ### Galerkin pin: `b_torus` agrees with `galerkinConvection` on `Vₙ` -/

/-- **Galerkin pin:** `b_torus u v w = galerkinConvection n u v w` when
`u, v, w` all lie in the Galerkin subspace `Vₙ`.

**Proof:** The tsums `∑' k : Fin 3 → ℤ` and `∑' l : Fin 3 → ℤ` have support confined
to `fourierBox n` (for `u`'s contribution in `k`, `v`'s in `l`), so they reduce
to the finite Finset sums in `galerkinConvection n`. Specifically:
- `û_a(k) = 0` for `k ∉ fourierBox n` (by `coeff_zero_outside_box` applied to `u` and `hu`),
- `v̂_i(l) = 0` for `l ∉ fourierBox n` (by `coeff_zero_outside_box` applied to `v` and `hv`),
so the entire summand vanishes when `k ∉ fourierBox n` or `l ∉ fourierBox n`. -/
theorem b_torus_galerkin (n : ℕ) (u v w : L2Sigma)
    (hu : velocityProjection_n n (u : L2VF) = (u : L2VF))
    (hv : velocityProjection_n n (v : L2VF) = (v : L2VF))
    (hw : velocityProjection_n n (w : L2VF) = (w : L2VF)) :
    b_torus u v w = galerkinConvection n (u : L2VF) (v : L2VF) (w : L2VF) := by
  simp only [b_torus, galerkinConvection]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro a _
  -- Fourier coefficients of u (resp. v) vanish outside fourierBox n.
  have hucoeff : ∀ k : Fin 3 → ℤ, k ∉ fourierBox n →
      mFourierCoeff3 (L2VF_projComponentC a (u : L2VF)) k = 0 :=
    coeff_zero_outside_box n (u : L2VF) hu a
  have hvcoeff : ∀ l : Fin 3 → ℤ, l ∉ fourierBox n →
      mFourierCoeff3 (L2VF_projComponentC i (v : L2VF)) l = 0 :=
    coeff_zero_outside_box n (v : L2VF) hv i
  -- Let f k l = Re[ û_a(k) * (2πi l_a) * v̂_i(l) * ŵ_i(-(k+l)) ].
  -- When k ∉ fourierBox n, û_a(k) = 0, so f k l = 0 for all l.
  -- Hence ∑' k, ∑' l, f k l = ∑ k ∈ fourierBox n, ∑' l, f k l
  --                           = ∑ k ∈ fourierBox n, ∑ l ∈ fourierBox n, f k l.
  -- Step 1: reduce the inner tsum over l to a Finset sum (v̂_i(l) = 0 for l ∉ fourierBox n).
  have hinner : ∀ k : Fin 3 → ℤ,
      ∑' (l : Fin 3 → ℤ), ((mFourierCoeff3 (L2VF_projComponentC a (u : L2VF)) k) *
       ((2 * (Real.pi : ℂ) * I * (l a : ℂ)) *
       (mFourierCoeff3 (L2VF_projComponentC i (v : L2VF)) l *
        mFourierCoeff3 (L2VF_projComponentC i (w : L2VF)) (-(k + l))))).re =
      ∑ l ∈ fourierBox n, ((mFourierCoeff3 (L2VF_projComponentC a (u : L2VF)) k) *
       ((2 * (Real.pi : ℂ) * I * (l a : ℂ)) *
       (mFourierCoeff3 (L2VF_projComponentC i (v : L2VF)) l *
        mFourierCoeff3 (L2VF_projComponentC i (w : L2VF)) (-(k + l))))).re := by
    intro k
    apply tsum_eq_sum
    intro l hl
    simp [hvcoeff l hl]
  -- Step 2: reduce the outer tsum over k to a Finset sum (û_a(k) = 0 for k ∉ fourierBox n).
  simp_rw [hinner]
  apply tsum_eq_sum
  intro k hk
  simp [hucoeff k hk]

/-! ### Assembly: concrete witness for `Torus3NSForms` -/

/-- The concrete T³ Navier–Stokes forms bundle, using `b_torus` as the convection form.

**Proved:** `b_galerkin` (definitional Galerkin pin).
**Scaffolded (honest sorries):** all other fields — trilinearity (6 sorries),
  `b_antisymm` (1 sorry), `b_bound` (1 sorry). Total: 8 sorry in this structure.
**No new axiom is introduced.** -/
noncomputable def torusNSFormsWitness : Torus3NSForms where
  b := b_torus
  b_antisymm := b_torus_antisymm
  b_add_1 := b_torus_add_1
  b_add_2 := b_torus_add_2
  b_add_3 := b_torus_add_3
  b_smul_1 := b_torus_smul_1
  b_smul_2 := b_torus_smul_2
  b_smul_3 := b_torus_smul_3
  b_bound := b_torus_bound
  b_galerkin := b_torus_galerkin

/-- **`Nonempty Torus3NSForms`** via the concrete witness `torusNSFormsWitness`.

This is the sorry-carrying (but non-axiomatic) replacement for the axiom
`torus3_NSForms_exist` in `AxiomaticClosure.lean`.  Once the 8 sorries in this file
(6 trilinearity + `b_antisymm` + `b_bound`) are all discharged, the axiom
`torus3_NSForms_exist` can be deleted and replaced by this theorem.

Until then, both coexist with equal mathematical content but this version uses honest
sorries (lean-prover targets) rather than an axiom. -/
theorem torus3_NSForms_nonempty : Nonempty Torus3NSForms :=
  ⟨torusNSFormsWitness⟩

end LerayHopf
