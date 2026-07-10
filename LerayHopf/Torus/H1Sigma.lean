import LerayHopf.Torus.Leray  -- L2Sigma, isClosed_L2Sigma (+ DivergenceFree transitively:
  -- L2VF_projComponent(C), L2VF_injectComponent) — issue #113 PR-1: no longer via VelocityGalerkin
import LerayHopf.Torus.SobolevTorus
import LerayHopf.Torus.RellichEmbedding

open MeasureTheory Filter Topology

/-!
# H¹_σ energy functionals and Rellich compactness for divergence-free fields

**M6 — Commit 1 (foundational layer, zero axioms).**

This file defines the H¹ energy functional on `L2VF = L²(𝕋³; ℝ³)` via Fourier
coefficients, the viscous dissipation form with the correct `(2π)²` weight, the
H¹ membership predicates, and the Rellich compactness theorem for divergence-free
sequences bounded in H¹.

## Main definitions

- `h1EnergySq u`        : ∑ⱼ ∑'ₖ (1 + ∑ᵢ (kᵢ)²) ‖ûⱼ(k)‖² (H¹ energy squared)
- `memH1VF u`           : u has finite H¹ energy component-wise
- `memH1Sigma u`        : u ∈ L²_σ and memH1VF u
- `viscousFormSq ν u`   : ν * ∑ⱼ ∑'ₖ (2π)² (∑ᵢ (kᵢ)²) ‖ûⱼ(k)‖² (viscous dissipation)

## Main theorems

- `h1EnergySq_nonneg`       : 0 ≤ h1EnergySq u
- `viscousFormSq_nonneg`    : 0 ≤ ν → 0 ≤ viscousFormSq ν u
- `rellich_L2Sigma`         : Rellich compactness for H¹-bounded div-free sequences (prover target)

## Assumptions

None beyond mathlib axioms.
-/

namespace LerayHopf

/-! ### H¹ energy functional -/

/-- The squared H¹ energy of a velocity field `u ∈ L2VF`, defined componentwise via
Fourier coefficients:

  `h1EnergySq u = ∑ j : Fin 3, ∑' k : Fin 3 → ℤ, (1 + ∑ i, (k i : ℝ)²) * ‖ûⱼ(k)‖²`

where `ûⱼ(k) = mFourierCoeff3 (L2VF_projComponentC j u) k`.

This is the natural H¹(𝕋³; ℝ³) energy: the `(1 + ∑ᵢ kᵢ²)` weight is the standard
Sobolev weight at order 1. -/
noncomputable def h1EnergySq (u : L2VF) : ℝ :=
  ∑ j : Fin 3, ∑' k : Fin 3 → ℤ,
    (1 + ∑ i : Fin 3, (k i : ℝ) ^ 2) * ‖mFourierCoeff3 (L2VF_projComponentC j u) k‖ ^ 2

/-- The H¹ energy is nonneg: each summand is a product of nonneg factors. -/
theorem h1EnergySq_nonneg (u : L2VF) : 0 ≤ h1EnergySq u := by
  apply Finset.sum_nonneg
  intro j _
  apply tsum_nonneg
  intro k
  positivity

/-! ### H¹ membership predicates -/

/-- A velocity field `u ∈ L2VF` has finite H¹ energy component-wise:
  each scalar component `L2VF_projComponentC j u` lies in `H¹(𝕋³; ℂ)` (i.e., the
  H¹-weight Fourier sum is summable). -/
def memH1VF (u : L2VF) : Prop :=
  ∀ j : Fin 3, memH1Torus (L2VF_projComponentC j u)

/-- A velocity field `u ∈ L2VF` lies in `H¹_σ`: it is divergence-free (`u ∈ L2Sigma`)
and has finite H¹ energy component-wise (`memH1VF u`). -/
def memH1Sigma (u : L2VF) : Prop :=
  u ∈ L2Sigma ∧ memH1VF u

/-! ### Viscous dissipation form -/

/-- The viscous dissipation form `ν * ∑ⱼ ∑'ₖ (2π)² (∑ᵢ kᵢ²) ‖ûⱼ(k)‖²`.

The `(2π)²` factor is load-bearing: it arises from `|∂_xᵢ e^{2πi k·x}|² = (2π kᵢ)²`,
so this equals `ν * ‖∇u‖²_{L²}` (the true gradient energy on `𝕋³` with the
`e^{2πi k·x}` normalization convention). -/
noncomputable def viscousFormSq (ν : ℝ) (u : L2VF) : ℝ :=
  ν * ∑ j : Fin 3, ∑' k : Fin 3 → ℤ,
    (2 * Real.pi) ^ 2 * (∑ i : Fin 3, (k i : ℝ) ^ 2) *
      ‖mFourierCoeff3 (L2VF_projComponentC j u) k‖ ^ 2

/-- The viscous dissipation form is nonneg when `ν ≥ 0`. -/
theorem viscousFormSq_nonneg {ν : ℝ} (hν : 0 ≤ ν) (u : L2VF) :
    0 ≤ viscousFormSq ν u := by
  apply mul_nonneg hν
  apply Finset.sum_nonneg
  intro j _
  apply tsum_nonneg
  intro k
  positivity

/-! ### Rellich compactness for divergence-free H¹-bounded sequences -/

/-- Each single-component H¹ Fourier sum is dominated by the full `h1EnergySq`:
the energy is a sum of nonneg per-component sums. -/
private theorem h1EnergySq_component_le (j : Fin 3) (w : L2VF) :
    ∑' k : Fin 3 → ℤ, (1 + ∑ i : Fin 3, (k i : ℝ) ^ 2) *
        ‖mFourierCoeff3 (L2VF_projComponentC j w) k‖ ^ 2 ≤ h1EnergySq w :=
  Finset.single_le_sum
    (f := fun j' : Fin 3 => ∑' k : Fin 3 → ℤ, (1 + ∑ i : Fin 3, (k i : ℝ) ^ 2) *
      ‖mFourierCoeff3 (L2VF_projComponentC j' w) k‖ ^ 2)
    (fun j' _ => tsum_nonneg fun k => by positivity) (Finset.mem_univ j)

/-- Taking the real part undoes the complex embedding of a component
(cf. `velocityProjection_n_tendsto`). -/
private theorem re_compLpL_projComponentC (j : Fin 3) (w : L2VF) :
    (RCLike.reCLM (K := ℂ)).compLpL 2 haarTorus3 (L2VF_projComponentC j w)
      = L2VF_projComponent j w := by
  refine MeasureTheory.Lp.ext ?_
  filter_upwards [ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := haarTorus3)
      (RCLike.reCLM (K := ℂ)) (L2VF_projComponentC j w),
    ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := haarTorus3)
      (RCLike.ofRealCLM (K := ℂ)) (L2VF_projComponent j w)] with x hx1 hx2
  rw [hx1, show L2VF_projComponentC j w
      = (RCLike.ofRealCLM (K := ℂ)).compLpL 2 haarTorus3 (L2VF_projComponent j w) from rfl,
    hx2]
  simp

/-- The componentwise reassembly recovers a vector field
(cf. `velocityProjection_n_tendsto`). -/
private theorem sum_inject_projComponent (w : L2VF) :
    ∑ j : Fin 3, L2VF_injectComponent j (L2VF_projComponent j w) = w := by
  -- Pointwise (a.e.) description of the reassembled `j`-th component.
  have hcomp : ∀ j : Fin 3, L2VF_injectComponent j (L2VF_projComponent j w)
      =ᵐ[haarTorus3] fun x => w x j • EuclideanSpace.single j (1 : ℝ) := by
    intro j
    simp only [L2VF_injectComponent, L2VF_projComponent]
    filter_upwards [ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := haarTorus3)
        ((ContinuousLinearMap.id ℝ ℝ).smulRight (EuclideanSpace.single j (1 : ℝ)))
        ((EuclideanSpace.proj j (𝕜 := ℝ)).compLpL 2 haarTorus3 w),
      ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := haarTorus3)
        (EuclideanSpace.proj j (𝕜 := ℝ)) w] with x hx1 hx2
    rw [hx1, hx2]
    simp
  refine MeasureTheory.Lp.ext ?_
  rw [Fin.sum_univ_three]
  filter_upwards [MeasureTheory.Lp.coeFn_add
      (L2VF_injectComponent 0 (L2VF_projComponent 0 w)
        + L2VF_injectComponent 1 (L2VF_projComponent 1 w))
      (L2VF_injectComponent 2 (L2VF_projComponent 2 w)),
    MeasureTheory.Lp.coeFn_add (L2VF_injectComponent 0 (L2VF_projComponent 0 w))
      (L2VF_injectComponent 1 (L2VF_projComponent 1 w)),
    hcomp 0, hcomp 1, hcomp 2] with x hx1 hx2 hc0 hc1 hc2
  rw [hx1, Pi.add_apply, hx2, Pi.add_apply, hc0, hc1, hc2]
  have hsum := (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr (w x)
  simpa [Fin.sum_univ_three, EuclideanSpace.basisFun_apply,
    EuclideanSpace.basisFun_repr] using hsum

/-- **Rellich compactness for L²_σ.**

Any sequence `u : ℕ → L2VF` of divergence-free velocity fields bounded in H¹
has a subsequence converging in `L2VF`.

More precisely: if each `u n ∈ L2Sigma`, each component satisfies `memH1VF (u n)`,
and `h1EnergySq (u n) ≤ M²` for all `n`, then there exist a strictly monotone
extraction `φ : ℕ → ℕ` and a limit `g ∈ L2Sigma` such that
`u (φ n) → g` in `L2VF`.

Proof strategy (prover target):
- Apply `rellich_seq_compact` componentwise (j = 0, 1, 2) to extract convergent
  subsequences in `L2C`, using `hH1` (summability) and `hbound` (energy bound).
- Combine via diagonal extraction to get a single subsequence converging in all
  components.
- Reconstruct the limit in `L2VF` from the componentwise limits.
- Use `velocityProjection_n_preserves_L2Sigma` / `mem_L2Sigma_iff` to verify
  the limit is divergence-free. -/
theorem rellich_L2Sigma (M : ℝ) (u : ℕ → L2VF)
    (hmem : ∀ n, u n ∈ L2Sigma)
    (hH1 : ∀ n, memH1VF (u n))
    (hbound : ∀ n, h1EnergySq (u n) ≤ M ^ 2) :
    ∃ (φ : ℕ → ℕ) (g : L2VF), StrictMono φ ∧ g ∈ L2Sigma ∧
      Filter.Tendsto (fun n => u (φ n)) Filter.atTop (nhds g) := by
  classical
  -- Step A: each component of each `u n` satisfies the `rellich_seq_compact` hypothesis.
  have hcomp_hyp : ∀ (j : Fin 3) (n : ℕ), memH1Torus (L2VF_projComponentC j (u n)) ∧
      ∑' k : Fin 3 → ℤ, (1 + ∑ i : Fin 3, (k i : ℝ) ^ 2) *
        ‖mFourierCoeff3 (L2VF_projComponentC j (u n)) k‖ ^ 2 ≤ M ^ 2 :=
    fun j n => ⟨hH1 n j, (h1EnergySq_component_le j (u n)).trans (hbound n)⟩
  -- Step B: diagonal extraction — three nested applications of `rellich_seq_compact`.
  obtain ⟨φ₀, g₀, hφ₀, ht₀⟩ := rellich_seq_compact M
    (fun n => L2VF_projComponentC 0 (u n)) (fun n => hcomp_hyp 0 n)
  obtain ⟨φ₁, g₁, hφ₁, ht₁⟩ := rellich_seq_compact M
    (fun n => L2VF_projComponentC 1 (u (φ₀ n))) (fun n => hcomp_hyp 1 (φ₀ n))
  obtain ⟨φ₂, g₂, hφ₂, ht₂⟩ := rellich_seq_compact M
    (fun n => L2VF_projComponentC 2 (u (φ₀ (φ₁ n)))) (fun n => hcomp_hyp 2 (φ₀ (φ₁ n)))
  have hφ_mono : StrictMono fun n => φ₀ (φ₁ (φ₂ n)) := hφ₀.comp (hφ₁.comp hφ₂)
  -- All three components converge along the diagonal subsequence.
  have htC : ∀ j : Fin 3,
      Filter.Tendsto (fun n => L2VF_projComponentC j (u (φ₀ (φ₁ (φ₂ n)))))
        Filter.atTop (nhds (![g₀, g₁, g₂] j)) := by
    intro j
    fin_cases j
    · simpa [Function.comp_def] using ht₀.comp ((hφ₁.comp hφ₂).tendsto_atTop)
    · simpa [Function.comp_def] using ht₁.comp hφ₂.tendsto_atTop
    · simpa using ht₂
  -- Steps C–D: pass to the real components, reassemble, and identify the limit.
  have hterm : ∀ j ∈ (Finset.univ : Finset (Fin 3)),
      Filter.Tendsto (fun n : ℕ =>
          L2VF_injectComponent j (L2VF_projComponent j (u (φ₀ (φ₁ (φ₂ n))))))
        Filter.atTop (nhds (L2VF_injectComponent j
          ((RCLike.reCLM (K := ℂ)).compLpL 2 haarTorus3 (![g₀, g₁, g₂] j)))) := by
    intro j _
    have h2 : Continuous fun v : L2C =>
        L2VF_injectComponent j ((RCLike.reCLM (K := ℂ)).compLpL 2 haarTorus3 v) :=
      (L2VF_injectComponent j).continuous.comp
        ((RCLike.reCLM (K := ℂ)).compLpL 2 haarTorus3).continuous
    have h3 := (h2.tendsto (![g₀, g₁, g₂] j)).comp (htC j)
    simpa [Function.comp_def, re_compLpL_projComponentC] using h3
  have hsum := tendsto_finsetSum (Finset.univ : Finset (Fin 3)) hterm
  have hg_tend : Filter.Tendsto (fun n => u (φ₀ (φ₁ (φ₂ n)))) Filter.atTop
      (nhds (∑ j : Fin 3, L2VF_injectComponent j
        ((RCLike.reCLM (K := ℂ)).compLpL 2 haarTorus3 (![g₀, g₁, g₂] j)))) :=
    hsum.congr fun n => sum_inject_projComponent (u (φ₀ (φ₁ (φ₂ n))))
  -- Step E: the limit is divergence-free because `L2Sigma` is closed.
  have hg_mem : (∑ j : Fin 3, L2VF_injectComponent j
      ((RCLike.reCLM (K := ℂ)).compLpL 2 haarTorus3 (![g₀, g₁, g₂] j))) ∈ L2Sigma :=
    isClosed_L2Sigma.mem_of_tendsto hg_tend
      (Filter.Eventually.of_forall fun n => hmem (φ₀ (φ₁ (φ₂ n))))
  exact ⟨fun n => φ₀ (φ₁ (φ₂ n)), _, hφ_mono, hg_mem, hg_tend⟩

end LerayHopf
