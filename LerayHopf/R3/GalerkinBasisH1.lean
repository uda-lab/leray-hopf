import LerayHopf.R3.GalerkinODEExistence   -- SchwartzGalerkinBasis, schemeOfBasis (+ SolutionInterfaces transitively → R3TestApproxH1)
import LerayHopf.R3.CurlDensityH1          -- curl_approx_H1 (H¹ Fourier low-cut kernel, issue #4 PR-2)
import LerayHopf.R3.CurlDensityCapstone    -- curlSchwartzDense_holds (proved density, for dense_span)
import LerayHopf.R3.GalerkinCurveBounds    -- weightedFourierComponent_sub, viscousFormSq_eq_sum_normSq_wFC
import LerayHopf.R3.EnergyClassConvection  -- memH1VF_R3_add / memH1VF_R3_smul (H¹ closure under ±)

/-!
# Strengthened Galerkin basis: H¹ test approximation (scaffold, issue #4 PR-3)

This file contains the discharge statement for `R3TestApproxH1` at the *concrete*
`schemeOfBasis B` level: there exists a `SchwartzGalerkinBasis` whose induced scheme
satisfies the H¹(graph-norm) test-approximation property.

## Why this file exists (issue #93 §1b, route R2)

The abstract limit-passage theorem (`galerkin_limit_passage_R3` replacement) carries a
threaded hypothesis `htest : R3TestApproxH1 𝔊`.  The capstone chain
(`GalerkinODECapstone.lean` → `R3Capstone.lean`) must supply a concrete witness.

`nonempty_schwartzGalerkinBasis` (proved in `CurlDensityCapstone.lean`) gives an L²-dense
basis; the strengthened version here requires H¹(graph-norm) density as well, which is
discharged via the Fourier low-cut construction of `curl_approx_H1`.

## Proof (PROVED — issue #4 PR-3)

1. `curl_approx_H1` (`CurlDensityH1.lean`) gives: for any `w : L2Sigma_R3` with
   `IsSchwartzDivFree_R3 w` and `ε > 0`, there exists `ψ : Fin 3 → SchwartzMap ...`
   with `‖curlSchwartzL2 ψ - w‖ < ε` and `viscousFormSq_R3 1 (curlSchwartzL2 ψ - w) < ε`.
2. `exists_graphDenseSeq` (this file) enumerates a countable Schwartz-potential family `ψ`
   whose curl fields are H¹-graph-dense in the whole curl class.  The graph norm is realized
   as the product-space distance on `L2VF_R3 × (Fin 3 → L2C_R3)` via the weighted Fourier
   components (`weightedFourierComponent`, whose ℓ²-mass is `viscousFormSq_R3 1`); the product
   space is separable, so a countable dense subset exists.  The same family keeps
   `dense_span` (H¹-dense ⇒ L²-dense in the curl class, then `curlSchwartzDense_holds`).
3. `R3TestApproxH1 (schemeOfBasis B)`: each basis element `curlSchwartzL2 (ψ k)` is a Galerkin
   test (fixed by the `(k+1)`-th prefix-span projector) and Schwartz-div-free; the triangle
   inequality on the two seminorms (2 in the L² slot, `(a+b)² ≤ 2a²+2b²` in the viscous slot)
   turns steps 1–2 into a single Galerkin test within `ε` of `w` in both seminorms.

## Status

`nonempty_schwartzGalerkinBasis_H1` is PROVED (sorry-free, no new axiom): the Codex G3 gate
target is discharged.
-/

namespace LerayHopf

open MeasureTheory TopologicalSpace TemperedDistribution SchwartzMap
open scoped Topology

/-! ### Separability of the H¹ graph space `L2VF_R3 × (Fin 3 → L2C_R3)` -/

/-- `L2C_R3 = L²(ℝ³; ℂ)` is second-countable (needs the `Fact ((2:ℝ≥0∞) ≠ ⊤)` for the ℂ-Lp
instance), hence separable. -/
instance instSecondCountable_L2C_R3 : SecondCountableTopology L2C_R3 :=
  haveI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  Lp.SecondCountableTopology

/-- The H¹ graph space `L2VF_R3 × (Fin 3 → L2C_R3)` is separable: it is a finite product of
second-countable spaces (`L2VF_R3` via `instSeparableSpace_L2VF_R3`'s underlying
second-countability, each `L2C_R3` factor via `instSecondCountable_L2C_R3`). -/
instance instSeparableSpace_graphSpace :
    SeparableSpace (L2VF_R3 × (Fin 3 → L2C_R3)) := by
  haveI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  haveI : SecondCountableTopology L2VF_R3 := Lp.SecondCountableTopology
  exact SecondCountableTopology.to_separableSpace

/-! ### H¹ membership of Schwartz-component fields -/

/-- `H¹` is closed under subtraction (via `memH1VF_R3_add` + `memH1VF_R3_smul (-1)`). -/
private theorem memH1VF_R3_sub {u v : L2VF_R3} (hu : memH1VF_R3 u) (hv : memH1VF_R3 v) :
    memH1VF_R3 (u - v) := by
  have h : u - v = u + (-1 : ℝ) • v := by rw [neg_one_smul, sub_eq_add_neg]
  rw [h]; exact memH1VF_R3_add hu (memH1VF_R3_smul (-1) hv)

/-- Every curl field `curlSchwartzL2 θ` is `H¹` (its components are Schwartz, A3). -/
private theorem memH1VF_R3_curl (θ : Fin 3 → SchwartzMap Domain3 ℝ) :
    memH1VF_R3 (curlSchwartzL2 θ) :=
  memH1VF_R3_of_schwartz_components _ (curlSchwartz_isSchwartz θ)

/-! ### The H¹-graph-dense countable curl family -/

/-- The graph embedding of a Schwartz potential: its curl field together with the vector of
weighted Fourier components (√W · 𝓕(curl)ⱼ).  The product-space distance between two such
points controls BOTH the `L²` error and the viscous seminorm error `viscousFormSq_R3 1`. -/
private noncomputable def graphEmbed (θ : Fin 3 → SchwartzMap Domain3 ℝ) :
    L2VF_R3 × (Fin 3 → L2C_R3) :=
  (curlSchwartzL2 θ, fun j => weightedFourierComponent (curlSchwartzL2 θ) (memH1VF_R3_curl θ) j)

/-- **Separability thinning (H¹ graph norm).**  From separability of the graph space, extract a
single ℕ-enumeration of Schwartz potentials `ψ` whose curl fields (i) have `L2Sigma_R3`-dense
prefix spans and (ii) are H¹-graph-dense in the whole curl family: every `curlSchwartzL2 θ` is
approximated, simultaneously in `L²` and in each weighted Fourier component, by some
`curlSchwartzL2 (ψ k)`. -/
private theorem exists_graphDenseSeq :
    ∃ ψ : ℕ → (Fin 3 → SchwartzMap Domain3 ℝ),
      ((L2Sigma_R3 : Submodule ℝ L2VF_R3) ≤
        (⨆ n : ℕ, Submodule.span ℝ
          (Set.range (fun k : Fin n => curlSchwartzL2 (ψ (k : ℕ))))).topologicalClosure)
      ∧ (∀ (θ : Fin 3 → SchwartzMap Domain3 ℝ) (ρ : ℝ), 0 < ρ →
          ∃ k : ℕ, ‖curlSchwartzL2 (ψ k) - curlSchwartzL2 θ‖ < ρ ∧
            ∀ j : Fin 3,
              ‖weightedFourierComponent (curlSchwartzL2 (ψ k)) (memH1VF_R3_curl (ψ k)) j
                - weightedFourierComponent (curlSchwartzL2 θ) (memH1VF_R3_curl θ) j‖ < ρ) := by
  set S : Set (L2VF_R3 × (Fin 3 → L2C_R3)) := Set.range graphEmbed with hS
  have hSsep : IsSeparable S :=
    (isSeparable_univ_iff.2 inferInstance).mono (Set.subset_univ S)
  obtain ⟨t, hts, htc, hst⟩ := hSsep.exists_countable_dense_subset
  have hSne : S.Nonempty := Set.range_nonempty _
  have htne : t.Nonempty := by
    rcases hSne with ⟨x, hx⟩
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    subst hempty
    simp only [closure_empty, Set.subset_empty_iff] at hst
    rw [hst] at hx
    exact absurd hx (by simp)
  obtain ⟨g, rfl⟩ := htc.exists_eq_range htne
  -- extract a potential for each enumerated graph point
  have hmem : ∀ k, g k ∈ S := fun k => hts ⟨k, rfl⟩
  choose ψ hψ using hmem
  -- `graphEmbed (ψ k) = g k`, so first/second coordinates are pinned
  have hψ1 : ∀ k, curlSchwartzL2 (ψ k) = (g k).1 := fun k => congrArg Prod.fst (hψ k)
  refine ⟨ψ, ?_, ?_⟩
  · -- dense_span: `range curlSchwartzL2 ⊆ closure(range (curlSchwartzL2 ∘ ψ))`, then A + density
    have hsup : (⨆ n : ℕ, Submodule.span ℝ
          (Set.range (fun k : Fin n => curlSchwartzL2 (ψ (k : ℕ)))))
        = Submodule.span ℝ (Set.range (fun k => curlSchwartzL2 (ψ k))) :=
      iSup_prefixSpan_eq_span_range (fun k => curlSchwartzL2 (ψ k))
    rw [hsup]
    refine le_trans curlSchwartzDense_holds ?_
    refine Submodule.topologicalClosure_minimal _ ?_
      (Submodule.isClosed_topologicalClosure _)
    rw [Submodule.span_le]
    rintro x ⟨θ, rfl⟩
    -- `curlSchwartzL2 θ = π₁ (graphEmbed θ) ∈ π₁(closure(range g)) ⊆ closure(range (π₁∘g))`
    have hin : graphEmbed θ ∈ closure (Set.range g) := hst ⟨θ, rfl⟩
    have hfst : curlSchwartzL2 θ ∈ closure (Set.range (fun k => (g k).1)) := by
      have := image_closure_subset_closure_image (f := Prod.fst) continuous_fst
        (s := Set.range g) ⟨graphEmbed θ, hin, rfl⟩
      rwa [← Set.range_comp] at this
    have hrange : Set.range (fun k => (g k).1) = Set.range (fun k => curlSchwartzL2 (ψ k)) := by
      simp only [hψ1]
    rw [hrange] at hfst
    rw [Submodule.topologicalClosure_coe]
    exact closure_mono Submodule.subset_span hfst
  · -- graph-approx: closure gives a `g k` near `graphEmbed θ`; read off both coordinates
    intro θ ρ hρ
    have hin : graphEmbed θ ∈ closure (Set.range g) := hst ⟨θ, rfl⟩
    rw [Metric.mem_closure_iff] at hin
    obtain ⟨y, ⟨k, rfl⟩, hdist⟩ := hin ρ hρ
    rw [← hψ k, Prod.dist_eq, max_lt_iff] at hdist
    refine ⟨k, ?_, ?_⟩
    · have h1 := hdist.1
      simp only [graphEmbed] at h1
      rw [dist_eq_norm, norm_sub_rev] at h1
      exact h1
    · intro j
      have h2 := (dist_pi_lt_iff hρ).1 hdist.2 j
      simp only [graphEmbed] at h2
      rw [dist_eq_norm, norm_sub_rev] at h2
      exact h2

/-! ### Deliverable -/

/-- There exists a `SchwartzGalerkinBasis` whose induced Galerkin scheme satisfies
the H¹(graph-norm) test-approximation property `R3TestApproxH1`.

This is the strengthened counterpart of `nonempty_schwartzGalerkinBasis`
(`CurlDensityCapstone.lean`): the basis produced here witnesses not only L²-density of
its Galerkin span (the existing `SchwartzGalerkinBasis.dense_span` field) but also
H¹(graph-norm) approximation of every Schwartz divergence-free test by Galerkin tests of
the induced scheme.

The proof discharges `R3TestApproxH1` for the concrete `schemeOfBasis B` via
`curl_approx_H1` (Fourier low-cut kernel) and the separability of `L2VF_R3`.
The capstone chain (`GalerkinODECapstone.lean`, PR-6) will use the subtype witness
`⟨B, htest⟩` to thread `htest : R3TestApproxH1 (schemeOfBasis B)` into the assembly. -/
theorem nonempty_schwartzGalerkinBasis_H1 :
    Nonempty {B : SchwartzGalerkinBasis // R3TestApproxH1 (schemeOfBasis B)} := by
  obtain ⟨ψ, hdense, hgraph⟩ := exists_graphDenseSeq
  -- The strengthened basis: enumerate the H¹-graph-dense curl family.
  let B : SchwartzGalerkinBasis :=
    { e := fun k => curlSchwartzL2 (ψ k)
      e_schwartz := fun k => curlSchwartz_isSchwartz (ψ k)
      e_mem_sigma := fun k => curlSchwartzL2_mem_sigma (ψ k)
      dense_span := hdense }
  refine ⟨B, ?_⟩
  intro w hw ε hε
  -- (1) H¹ curl approximation of `w` within `ε/4` in both seminorms.
  obtain ⟨θ, hθL2, hθV⟩ := curl_approx_H1 w hw (ε / 4) (by positivity)
  -- (2) graph-density: pick a basis curl field within `ρ := min 1 (ε/24)` of `curl θ`.
  set ρ : ℝ := min 1 (ε / 24) with hρdef
  have hρpos : 0 < ρ := lt_min one_pos (by positivity)
  have hρ1 : ρ ≤ 1 := min_le_left _ _
  have hρe : ρ ≤ ε / 24 := min_le_right _ _
  obtain ⟨k, hkL2, hkW⟩ := hgraph θ ρ hρpos
  set wv : L2VF_R3 := (w : L2VF_R3) with hwv
  -- witness: `v = curl (ψ k)`, a basis element hence a Galerkin test, and Schwartz-div-free.
  refine ⟨⟨curlSchwartzL2 (ψ k), curlSchwartzL2_mem_sigma (ψ k)⟩, ?_, ?_, ?_, ?_⟩
  · -- IsGalerkinTest_R3: fixed by the `(k+1)`-th projector (it is `B.e k ∈ galerkinSpan B (k+1)`).
    refine ⟨k + 1, ?_⟩
    have hmem : curlSchwartzL2 (ψ k) ∈ galerkinSpan B (k + 1) :=
      Submodule.subset_span ⟨⟨k, Nat.lt_succ_self k⟩, rfl⟩
    show (schemeOfBasis B).P (k + 1) (curlSchwartzL2 (ψ k)) = curlSchwartzL2 (ψ k)
    rw [schemeOfBasis_P, galerkinP]
    exact Submodule.starProjection_eq_self_iff.mpr hmem
  · -- IsSchwartzDivFree_R3
    exact curlSchwartz_isSchwartz (ψ k)
  · -- L² error `< ε`
    show ‖curlSchwartzL2 (ψ k) - wv‖ < ε
    have hle : ‖curlSchwartzL2 (ψ k) - wv‖
        ≤ ‖curlSchwartzL2 (ψ k) - curlSchwartzL2 θ‖ + ‖curlSchwartzL2 θ - wv‖ := by
      have heq : curlSchwartzL2 (ψ k) - wv
          = (curlSchwartzL2 (ψ k) - curlSchwartzL2 θ) + (curlSchwartzL2 θ - wv) := by abel
      rw [heq]; exact norm_add_le _ _
    have : ‖curlSchwartzL2 (ψ k) - wv‖ < ρ + ε / 4 :=
      lt_of_le_of_lt hle (add_lt_add hkL2 hθL2)
    linarith
  · -- viscous error `< ε`, via wFC decomposition + `(a+b)² ≤ 2a²+2b²`
    show viscousFormSq_R3 1 (curlSchwartzL2 (ψ k) - wv) < ε
    have hwH1 : memH1VF_R3 wv := memH1VF_R3_of_schwartz_components wv hw
    have hkH1 : memH1VF_R3 (curlSchwartzL2 (ψ k)) := memH1VF_R3_curl (ψ k)
    have hθH1 : memH1VF_R3 (curlSchwartzL2 θ) := memH1VF_R3_curl θ
    have hdH1 : memH1VF_R3 (curlSchwartzL2 (ψ k) - wv) := memH1VF_R3_sub hkH1 hwH1
    have hθwH1 : memH1VF_R3 (curlSchwartzL2 θ - wv) := memH1VF_R3_sub hθH1 hwH1
    rw [viscousFormSq_eq_sum_normSq_wFC _ hdH1]
    -- per-component bound
    have hbound : ∀ j : Fin 3,
        ‖weightedFourierComponent (curlSchwartzL2 (ψ k) - wv) hdH1 j‖ ^ 2
        ≤ 2 * ρ ^ 2 + 2 * ‖weightedFourierComponent (curlSchwartzL2 θ - wv) hθwH1 j‖ ^ 2 := by
      intro j
      set A := weightedFourierComponent (curlSchwartzL2 (ψ k)) hkH1 j
        - weightedFourierComponent (curlSchwartzL2 θ) hθH1 j with hA
      set Bj := weightedFourierComponent (curlSchwartzL2 θ - wv) hθwH1 j with hBj
      have hdec : weightedFourierComponent (curlSchwartzL2 (ψ k) - wv) hdH1 j = A + Bj := by
        rw [hA, hBj,
          weightedFourierComponent_sub (curlSchwartzL2 (ψ k)) wv hkH1 hwH1 hdH1 j,
          weightedFourierComponent_sub (curlSchwartzL2 θ) wv hθH1 hwH1 hθwH1 j]
        abel
      have hAnorm : ‖A‖ < ρ := hkW j
      have htri : ‖A + Bj‖ ≤ ‖A‖ + ‖Bj‖ := norm_add_le _ _
      rw [hdec]
      nlinarith [htri, norm_nonneg A, norm_nonneg Bj, norm_nonneg (A + Bj),
        sq_nonneg (‖A‖ - ‖Bj‖), hAnorm, hρpos]
    -- sum the per-component bounds
    have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hbound j)
    have hconst : ∑ _j : Fin 3, (2 * ρ ^ 2 +
          2 * ‖weightedFourierComponent (curlSchwartzL2 θ - wv) hθwH1 _j‖ ^ 2)
        = 6 * ρ ^ 2 + 2 * viscousFormSq_R3 1 (curlSchwartzL2 θ - wv) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        viscousFormSq_eq_sum_normSq_wFC _ hθwH1, Finset.mul_sum]
      simp only [nsmul_eq_mul, Nat.cast_ofNat]
      ring
    rw [hconst] at hsum
    -- `ρ² ≤ ρ ≤ ε/24` ⇒ `6ρ² ≤ ε/4`; `2·V₁(curlθ-w) < ε/2`
    have hρsq : ρ ^ 2 ≤ ρ := by nlinarith [hρpos, hρ1]
    nlinarith [hsum, hθV, hρsq, hρe, hρpos]

end LerayHopf
