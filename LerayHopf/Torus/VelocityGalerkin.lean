import LerayHopf.Torus.GalerkinProjection
import LerayHopf.Torus.Leray  -- L2Sigma, DivFreeL2 (issue #113 PR-1: no longer transitive via GalerkinProjection)
import Mathlib.Analysis.RCLike.Basic

open MeasureTheory Filter Topology

/-!
# Velocity-field Galerkin projection (Route C, componentwise)

**M3/M4 — Group C/D: D-31 through D-33.**

This file constructs the Galerkin projection `velocityProjection_n n : L2VF →L[ℝ] L2VF`
and proves the divergence-free preservation theorem D-33.

## Route C design

There is no vector Hilbert basis on the torus in Mathlib, so the velocity Galerkin
projection is built **componentwise** (Route C):

1. **Extract** the `j`-th complex component of `u ∈ L2VF` via
   `L2VF_projComponentC j : L2VF →L[ℝ] L2C`.
2. **Project** the complex scalar field via `fourierProjection_n n : L2C →L[ℂ] L2C`
   (restricted to `ℝ`-scalars).
3. **Take the real part** via `(RCLike.reCLM (K := ℂ)).compLpL 2 haarTorus3 : L2C →L[ℝ] Lp ℝ 2 haarTorus3`.
4. **Inject** back into the `j`-th component of `L2VF` via
   `L2VF_injectComponent j : Lp ℝ 2 haarTorus3 →L[ℝ] L2VF`.
5. **Sum** over `j : Fin 3`.

**Key invariant:** Since `L2VF_projComponentC j u = ofRealCLM ∘ (L2VF_projComponent j u)` is
a real-valued function embedded in `L2C`, and `fourierBox n` is symmetric (`k ∈ fourierBox n ↔ -k ∈ fourierBox n`), the projection `fourierProjection_n n (L2VF_projComponentC j u)` is again real-valued
(i.e., lies in the range of `ofRealCLM`). Hence `Re(P_n(uj_ℂ)) = P_n(uj_ℝ)` as Lp functions.
This real-valuedness is established by `conjL2C_fourierProjection` (bridge lemma D-32b), and is
used in the proof of `velocityProjection_n_component_comm`.

## Main definitions

- `velocityProjection_n n`              : `L2VF →L[ℝ] L2VF` — componentwise Galerkin projection

`L2VF_injectComponent j : Lp ℝ 2 haarTorus3 →L[ℝ] L2VF` (used below in step 4) lives in
`DivergenceFree.lean` next to its adjoint `L2VF_projComponent` (moved there, issue #113 PR-1),
reached here via the `Leray` import.

## Main theorems

- `velocityProjection_n_component_comm` : bridge lemma — component extraction commutes with projection
- `velocityProjection_n_preserves_L2Sigma` : D-33 — div-free preservation
- `velocityProjection_n_tendsto`          : D-32 — convergence to the identity in `L2VF`
-/

namespace LerayHopf

/-! ### D-31: Velocity-field Galerkin projection -/

/-- The `n`-th Galerkin projection on `L2VF = L²(𝕋³; ℝ³)`, acting **componentwise**.

Each component `j : Fin 3` is processed independently:
1. Extract the `j`-th complex component: `L2VF_projComponentC j u : L2C`.
2. Apply the scalar Fourier projection: `fourierProjection_n n (·) : L2C →L[ℂ] L2C`.
3. Take the real part: `(RCLike.reCLM).compLpL 2 haarTorus3 : L2C →L[ℝ] Lp ℝ 2 haarTorus3`.
4. Inject into the `j`-th component slot: `L2VF_injectComponent j : Lp ℝ 2 haarTorus3 →L[ℝ] L2VF`.

The `j`-th summand is a composition of ℝ-linear CLMs, hence ℝ-linear and continuous.
The sum over `j : Fin 3` (finite) is again a CLM.

**Design note:** `fourierProjection_n n : L2C →L[ℂ] L2C` is `.restrictScalars ℝ`-ed at each
summand to produce an ℝ-linear CLM.  The real-part step (`reCLM.compLpL`) is not a mere
round-trip: it is justified by the real-valuedness preservation fact proved in
`conjL2C_fourierProjection` (the box `fourierBox n` is symmetric under `k ↦ -k`), and
`velocityProjection_n_component_comm` records that component extraction commutes with the
full projection. -/
noncomputable def velocityProjection_n (n : ℕ) : L2VF →L[ℝ] L2VF :=
  ∑ j : Fin 3,
    L2VF_injectComponent j ∘L
    (RCLike.reCLM (K := ℂ)).compLpL 2 haarTorus3 ∘L
    (fourierProjection_n n).restrictScalars ℝ ∘L
    L2VF_projComponentC j

/-! ### Proof infrastructure for the bridge lemma (lean-prover helpers)

The private helpers below are proof-layer infrastructure only; the theorem targets
D-32/D-32b/D-33 keep their statements byte-identical.  Mathematical content:

1. Component projection ∘ injection is the identity (resp. zero) on the matching
   (resp. mismatched) slot, at the `Lp` level.
2. `fourierProjection_n` preserves real-valuedness, because `fourierBox n` is symmetric
   under `k ↦ -k` and real-embedded functions have conjugate-symmetric Fourier
   coefficients.  Real-valuedness is expressed as being fixed by the conjugation
   operator `conjL2C` (the `compLpL`-lift of `Complex.conjCLE`). -/

open scoped ComplexConjugate

/-- Real-component projection composed with component injection: identity on the matching
slot, zero otherwise. -/
private lemma projComponent_injectComponent (i j : Fin 3) (f : Lp ℝ 2 haarTorus3) :
    L2VF_projComponent i (L2VF_injectComponent j f) = if i = j then f else 0 := by
  simp only [L2VF_projComponent, L2VF_injectComponent]
  have h1 := ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := haarTorus3)
    ((ContinuousLinearMap.id ℝ ℝ).smulRight (EuclideanSpace.single j (1 : ℝ))) f
  have h2 := ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := haarTorus3)
    (EuclideanSpace.proj i (𝕜 := ℝ))
    (((ContinuousLinearMap.id ℝ ℝ).smulRight
      (EuclideanSpace.single j (1 : ℝ))).compLpL 2 haarTorus3 f)
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    refine MeasureTheory.Lp.ext ?_
    filter_upwards [h1, h2] with x hx1 hx2
    rw [hx2, hx1]
    simp
  · rw [if_neg hij]
    refine MeasureTheory.Lp.ext ?_
    filter_upwards [h1, h2, MeasureTheory.Lp.coeFn_zero (E := ℝ) (p := 2) (μ := haarTorus3)]
      with x hx1 hx2 hx0
    rw [hx2, hx1, hx0]
    simp [hij]

/-- Complex-component projection composed with component injection: the real-to-complex
embedding on the matching slot, zero otherwise. -/
private lemma projComponentC_injectComponent (i j : Fin 3) (f : Lp ℝ 2 haarTorus3) :
    L2VF_projComponentC i (L2VF_injectComponent j f) =
      if i = j then (RCLike.ofRealCLM (K := ℂ)).compLpL 2 haarTorus3 f else 0 := by
  have hunfold : L2VF_projComponentC i (L2VF_injectComponent j f)
      = (RCLike.ofRealCLM (K := ℂ)).compLpL 2 haarTorus3
          (L2VF_projComponent i (L2VF_injectComponent j f)) := rfl
  rw [hunfold, projComponent_injectComponent]
  split_ifs with h
  · rfl
  · exact map_zero _

/-- Complex conjugation on `L2C`, as an `ℝ`-linear CLM (the `compLpL`-lift of
`Complex.conjCLE`).  Proof-layer helper: `conjL2C f = f` expresses that `f` is
(a.e.) real-valued. -/
private noncomputable def conjL2C : L2C →L[ℝ] L2C :=
  ((Complex.conjCLE : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ).compLpL 2 haarTorus3

private lemma coeFn_conjL2C (f : L2C) :
    conjL2C f =ᵐ[haarTorus3] fun x => conj (f x) := by
  show ((Complex.conjCLE : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ).compLpL 2 haarTorus3 f
      =ᵐ[haarTorus3] fun x => conj (f x)
  filter_upwards [ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := haarTorus3)
    ((Complex.conjCLE : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) f] with x hx
  rw [hx]
  simp

/-- Real-embedded functions are fixed by `conjL2C`. -/
private lemma conjL2C_ofRealLp (g : Lp ℝ 2 haarTorus3) :
    conjL2C ((RCLike.ofRealCLM (K := ℂ)).compLpL 2 haarTorus3 g)
      = (RCLike.ofRealCLM (K := ℂ)).compLpL 2 haarTorus3 g := by
  refine MeasureTheory.Lp.ext ?_
  filter_upwards [coeFn_conjL2C ((RCLike.ofRealCLM (K := ℂ)).compLpL 2 haarTorus3 g),
    ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := haarTorus3)
      (RCLike.ofRealCLM (K := ℂ)) g] with x hx1 hx2
  rw [hx1, hx2]
  simp

/-- The complex-embedded component of a velocity field is fixed by `conjL2C`. -/
private lemma conjL2C_projComponentC (j : Fin 3) (u : L2VF) :
    conjL2C (L2VF_projComponentC j u) = L2VF_projComponentC j u :=
  conjL2C_ofRealLp (L2VF_projComponent j u)

/-- Two elements of `L2C` with the same Fourier coefficients are equal
(`torus3_mFourierBasis.repr` is injective). -/
private lemma L2C_ext_mFourierCoeff3 {f g : L2C}
    (h : ∀ k, mFourierCoeff3 f k = mFourierCoeff3 g k) : f = g :=
  torus3_mFourierBasis.repr.injective (lp.ext (funext h))

/-- The Fourier coefficient as a concrete integral against `haarTorus3`
(definitional transport of `UnitAddTorus.mFourierBasis_repr`). -/
private lemma mFourierCoeff3_integral (f : L2C) (k : Fin 3 → ℤ) :
    mFourierCoeff3 f k = ∫ t, UnitAddTorus.mFourier (-k) t • f t ∂haarTorus3 :=
  UnitAddTorus.mFourierBasis_repr (d := Fin 3) f k

/-- Conjugation reflects Fourier coefficients: `(conj f)^(k) = conj (f^(-k))`. -/
private lemma mFourierCoeff3_conjL2C (f : L2C) (k : Fin 3 → ℤ) :
    mFourierCoeff3 (conjL2C f) k = conj (mFourierCoeff3 f (-k)) := by
  rw [mFourierCoeff3_integral, mFourierCoeff3_integral, ← integral_conj]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_conjL2C f] with x hx
  rw [hx, neg_neg, smul_eq_mul, smul_eq_mul, map_mul, ← UnitAddTorus.mFourier_neg]

/-- The truncation cube is symmetric under `k ↦ -k`. -/
private lemma neg_mem_fourierBox {n : ℕ} {k : Fin 3 → ℤ} :
    -k ∈ fourierBox n ↔ k ∈ fourierBox n := by
  simp only [fourierBox, Fintype.mem_piFinset, Finset.mem_Icc, Pi.neg_apply]
  constructor <;> intro h i <;> (have hi := h i; omega)

/-- **Key real-valuedness fact:** `fourierProjection_n` preserves the fixed points of
`conjL2C` (a.e. real-valued functions), because the box is `k ↦ -k` symmetric and
conjugation reflects Fourier coefficients. -/
private lemma conjL2C_fourierProjection (n : ℕ) (f : L2C) (hf : conjL2C f = f) :
    conjL2C (fourierProjection_n n f) = fourierProjection_n n f := by
  apply L2C_ext_mFourierCoeff3
  intro k
  rw [mFourierCoeff3_conjL2C, fourierProjection_n_mFourierCoeff,
    fourierProjection_n_mFourierCoeff]
  by_cases hk : k ∈ fourierBox n
  · rw [if_pos (neg_mem_fourierBox.mpr hk), if_pos hk, ← mFourierCoeff3_conjL2C, hf]
  · rw [if_neg (fun hmem => hk (neg_mem_fourierBox.mp hmem)), if_neg hk, map_zero]

/-- On fixed points of `conjL2C`, re-embedding the real part is the identity. -/
private lemma ofRealLp_reLp_eq_self {h : L2C} (hc : conjL2C h = h) :
    (RCLike.ofRealCLM (K := ℂ)).compLpL 2 haarTorus3
      ((RCLike.reCLM (K := ℂ)).compLpL 2 haarTorus3 h) = h := by
  have hae : ∀ᵐ x ∂haarTorus3, conj (h x) = h x := by
    have h1 := coeFn_conjL2C h
    rw [hc] at h1
    filter_upwards [h1] with x hx
    exact hx.symm
  refine MeasureTheory.Lp.ext ?_
  filter_upwards [hae,
    ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := haarTorus3) (RCLike.reCLM (K := ℂ)) h,
    ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := haarTorus3) (RCLike.ofRealCLM (K := ℂ))
      ((RCLike.reCLM (K := ℂ)).compLpL 2 haarTorus3 h)] with x hx1 hx2 hx3
  rw [hx3, hx2]
  have hre := Complex.conj_eq_iff_re.mp hx1
  simpa using hre

/-! ### Bridge lemma: component extraction commutes with projection -/

/-- **Bridge lemma (D-32b):** The `j`-th complex component of `velocityProjection_n n u`
equals `fourierProjection_n n` applied to the `j`-th complex component of `u`.

That is, the componentwise construction satisfies:
```
L2VF_projComponentC j (velocityProjection_n n u) =
    (fourierProjection_n n).restrictScalars ℝ (L2VF_projComponentC j u)
```

**Proof outline:**

Step 1 — Unfold `velocityProjection_n n u` as `∑ j', L2VF_injectComponent j' (Re(P_n(uj'_ℂ)))`.

Step 2 — Apply `L2VF_projComponentC j` (which is `ofRealCLM ∘ EuclideanSpace.proj j`, lifted to Lp):
  - Linearity of `L2VF_projComponentC j` passes it through the sum.
  - For `j' ≠ j`: `L2VF_projComponentC j (L2VF_injectComponent j' f) = 0`
    because the `j'`-th component has zero content in the `j`-th slot.
  - For `j' = j`: `L2VF_projComponentC j (L2VF_injectComponent j f) = ofRealCLM.compLpL f`
    because `proj j (r • single j 1) = r`.

Step 3 — Hence `L2VF_projComponentC j (velocityProjection_n n u) = ofRealCLM.compLpL (Re(P_n(uj_ℂ)))`.

Step 4 — Real-valuedness: since `uj_ℂ = L2VF_projComponentC j u` is in the range of
  `ofRealCLM.compLpL` (it equals `ofRealCLM.compLpL (L2VF_projComponent j u)`), and
  `fourierBox n` is closed under `k ↦ -k` (symmetric cube), we have
  `Re(P_n(ofReal(f))) = ofReal(P_n_ℝ(f))` where `P_n_ℝ` is the real-domain projection.
  This shows `ofRealCLM (Re(P_n(uj_ℂ))) = P_n(uj_ℂ)`.

Key lemmas used: `projComponentC_injectComponent`, `conjL2C_fourierProjection`,
`ofRealLp_reLp_eq_self`, `fourierProjection_n_mFourierCoeff`. -/
theorem velocityProjection_n_component_comm (n : ℕ) (u : L2VF) (j : Fin 3) :
    L2VF_projComponentC j (velocityProjection_n n u) =
      (fourierProjection_n n).restrictScalars ℝ (L2VF_projComponentC j u) := by
  -- Step 1–3: collapse the componentwise sum to the `j`-th summand.
  have hsum : L2VF_projComponentC j (velocityProjection_n n u)
      = (RCLike.ofRealCLM (K := ℂ)).compLpL 2 haarTorus3
          ((RCLike.reCLM (K := ℂ)).compLpL 2 haarTorus3
            (fourierProjection_n n (L2VF_projComponentC j u))) := by
    have hunfold : velocityProjection_n n u
        = ∑ j' : Fin 3, L2VF_injectComponent j'
            ((RCLike.reCLM (K := ℂ)).compLpL 2 haarTorus3
              (fourierProjection_n n (L2VF_projComponentC j' u))) := by
      simp only [velocityProjection_n, ContinuousLinearMap.sum_apply,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars']
    rw [hunfold, map_sum, Finset.sum_eq_single_of_mem j (Finset.mem_univ j)
      (fun b _ hb => by rw [projComponentC_injectComponent, if_neg (Ne.symm hb)]),
      projComponentC_injectComponent, if_pos rfl]
  -- Step 4: real-valuedness of the projected component kills the `Re`-round-trip.
  rw [hsum, ofRealLp_reLp_eq_self
    (conjL2C_fourierProjection n _ (conjL2C_projComponentC j u))]
  rfl

/-! ### D-33: Galerkin projection preserves L²_σ -/

/-- **D-33 — Div-free preservation:** If `u ∈ L²_σ(𝕋³)` (i.e., `u` is divergence-free),
then the Galerkin projection `velocityProjection_n n u` is also in `L²_σ(𝕋³)`.

In other words, the Fourier truncation `Pₙ` maps the divergence-free subspace into itself.

**Proof outline:**

By `mem_L2Sigma_iff`, we need `DivFreeL2 (velocityProjection_n n u)`, i.e.,
for every `k : Fin 3 → ℤ`:
  `∑ j : Fin 3, (k j : ℂ) * mFourierCoeff3 (L2VF_projComponentC j (velocityProjection_n n u)) k = 0`.

Step 1 — Apply `velocityProjection_n_component_comm`:
  `mFourierCoeff3 (L2VF_projComponentC j (velocityProjection_n n u)) k`
  `= mFourierCoeff3 ((fourierProjection_n n).restrictScalars ℝ (L2VF_projComponentC j u)) k`.

Step 2 — Apply `fourierProjection_n_mFourierCoeff` (from `GalerkinProjection.lean`):
  `mFourierCoeff3 (fourierProjection_n n f) k = if k ∈ fourierBox n then mFourierCoeff3 f k else 0`.

Step 3 — Combine: the sum becomes
  `∑ j, (k j : ℂ) * (if k ∈ fourierBox n then mFourierCoeff3 (L2VF_projComponentC j u) k else 0)`
  `= if k ∈ fourierBox n then ∑ j, (k j : ℂ) * mFourierCoeff3 (L2VF_projComponentC j u) k else 0`.

Step 4 — For `k ∈ fourierBox n`: the inner sum equals `0` by `(mem_L2Sigma_iff u).mp hu` applied at `k`
  (using `DivFreeL2 u`).
Step 5 — For `k ∉ fourierBox n`: the expression is `0` directly.

Key lemmas used: `velocityProjection_n_component_comm`, `fourierProjection_n_mFourierCoeff`,
`mem_L2Sigma_iff`, `DivFreeL2` (definition). -/
theorem velocityProjection_n_preserves_L2Sigma (n : ℕ) (u : L2VF) (hu : u ∈ L2Sigma) :
    velocityProjection_n n u ∈ L2Sigma := by
  rw [mem_L2Sigma_iff] at hu ⊢
  intro k
  have hcoeff : ∀ j : Fin 3,
      mFourierCoeff3 (L2VF_projComponentC j (velocityProjection_n n u)) k
        = if k ∈ fourierBox n then mFourierCoeff3 (L2VF_projComponentC j u) k else 0 := by
    intro j
    rw [velocityProjection_n_component_comm]
    exact fourierProjection_n_mFourierCoeff n (L2VF_projComponentC j u) k
  simp only [hcoeff]
  by_cases hk : k ∈ fourierBox n
  · simp only [if_pos hk]
    exact hu k
  · simp only [if_neg hk, mul_zero, Finset.sum_const_zero]

/-! ### D-32: Convergence of velocity Galerkin projections -/

/-- The velocity Galerkin projections converge to the identity in `L2VF = L²(𝕋³; ℝ³)`.

**Proof outline:**

For each component `j`, `L2VF_projComponentC j (velocityProjection_n n u) → L2VF_projComponentC j u`
in `L2C` follows from `fourierProjection_n_tendsto` (D-30) applied to `L2VF_projComponentC j u`
and the bridge lemma `velocityProjection_n_component_comm`.

The convergence `velocityProjection_n n u → u` in `L2VF` then follows from convergence in each
component via `tendsto_finsetSum`, using the componentwise decomposition
`∑ j, L2VF_injectComponent j (L2VF_projComponent j u) = u`.

Key lemmas used: `velocityProjection_n_component_comm`, `fourierProjection_n_tendsto`,
`tendsto_finsetSum`. -/
theorem velocityProjection_n_tendsto (u : L2VF) :
    Filter.Tendsto (fun n => velocityProjection_n n u) Filter.atTop (nhds u) := by
  classical
  -- Taking the real part undoes the complex embedding of a component.
  have hre : ∀ j : Fin 3,
      (RCLike.reCLM (K := ℂ)).compLpL 2 haarTorus3 (L2VF_projComponentC j u)
        = L2VF_projComponent j u := by
    intro j
    refine MeasureTheory.Lp.ext ?_
    filter_upwards [ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := haarTorus3)
        (RCLike.reCLM (K := ℂ)) (L2VF_projComponentC j u),
      ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := haarTorus3)
        (RCLike.ofRealCLM (K := ℂ)) (L2VF_projComponent j u)] with x hx1 hx2
    rw [hx1, show L2VF_projComponentC j u
        = (RCLike.ofRealCLM (K := ℂ)).compLpL 2 haarTorus3 (L2VF_projComponent j u) from rfl,
      hx2]
    simp
  -- Pointwise (a.e.) description of the reassembled `j`-th component.
  have hcomp : ∀ j : Fin 3, L2VF_injectComponent j (L2VF_projComponent j u)
      =ᵐ[haarTorus3] fun x => u x j • EuclideanSpace.single j (1 : ℝ) := by
    intro j
    simp only [L2VF_injectComponent, L2VF_projComponent]
    filter_upwards [ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := haarTorus3)
        ((ContinuousLinearMap.id ℝ ℝ).smulRight (EuclideanSpace.single j (1 : ℝ)))
        ((EuclideanSpace.proj j (𝕜 := ℝ)).compLpL 2 haarTorus3 u),
      ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := haarTorus3)
        (EuclideanSpace.proj j (𝕜 := ℝ)) u] with x hx1 hx2
    rw [hx1, hx2]
    simp
  -- The componentwise reassembly recovers `u`.
  have hdecomp : ∑ j : Fin 3, L2VF_injectComponent j (L2VF_projComponent j u) = u := by
    refine MeasureTheory.Lp.ext ?_
    rw [Fin.sum_univ_three]
    filter_upwards [MeasureTheory.Lp.coeFn_add
        (L2VF_injectComponent 0 (L2VF_projComponent 0 u)
          + L2VF_injectComponent 1 (L2VF_projComponent 1 u))
        (L2VF_injectComponent 2 (L2VF_projComponent 2 u)),
      MeasureTheory.Lp.coeFn_add (L2VF_injectComponent 0 (L2VF_projComponent 0 u))
        (L2VF_injectComponent 1 (L2VF_projComponent 1 u)),
      hcomp 0, hcomp 1, hcomp 2] with x hx1 hx2 hc0 hc1 hc2
    rw [hx1, Pi.add_apply, hx2, Pi.add_apply, hc0, hc1, hc2]
    have hsum := (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr (u x)
    simpa [Fin.sum_univ_three, EuclideanSpace.basisFun_apply,
      EuclideanSpace.basisFun_repr] using hsum
  -- Each summand converges, by D-30 and continuity of the reassembly.
  have hterm : ∀ j ∈ (Finset.univ : Finset (Fin 3)),
      Filter.Tendsto (fun n : ℕ => L2VF_injectComponent j
          ((RCLike.reCLM (K := ℂ)).compLpL 2 haarTorus3
            (fourierProjection_n n (L2VF_projComponentC j u))))
        Filter.atTop (nhds (L2VF_injectComponent j (L2VF_projComponent j u))) := by
    intro j _
    have h1 := fourierProjection_n_tendsto (L2VF_projComponentC j u)
    have h2 : Continuous fun v : L2C =>
        L2VF_injectComponent j ((RCLike.reCLM (K := ℂ)).compLpL 2 haarTorus3 v) :=
      (L2VF_injectComponent j).continuous.comp
        ((RCLike.reCLM (K := ℂ)).compLpL 2 haarTorus3).continuous
    have h3 := (h2.tendsto (L2VF_projComponentC j u)).comp h1
    simpa [Function.comp_def, hre j] using h3
  have hsum := tendsto_finsetSum (Finset.univ : Finset (Fin 3)) hterm
  rw [hdecomp] at hsum
  refine hsum.congr fun n => ?_
  simp only [velocityProjection_n, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars']

end LerayHopf
