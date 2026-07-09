/-
# LerayHopf.R3.GalerkinCurveBounds — Issue #46 PR-1 (File B)

**Goal:** The Galerkin curve / pairing library feeding the "good-sampling" Simon
compactness route that discharges the axiom `galerkin_spacetime_precompact_R3`
(plan: `docs/scratch/issue46-spacetime-precompact-plan.md`, §3 File B): L²- and
H¹-continuity of the Galerkin curve, the uniform energy bound `‖u(t)‖ ≤ ‖u₀‖`,
weighted-Fourier linearity and the `V₁`-as-sum identity, the stokes Cauchy–Schwarz
bound, the scalar energy identity along the curve, and the Schwartz representation
of Galerkin states.

Everything here sits strictly UPSTREAM of `ArzelaAscoliTime.lean` and does NOT
import `ArzelaAscoliTime`, `AubinLionsLimitPassage`, `ConvectionForm`, or any torus
file (plan constraint 1).

**Fresh-build note (plan §2):** B1/B2/B5 are NEW public lemmas re-deriving facts
whose only existing versions are `private` in `AubinLionsLimitPassage.lean`
(`galerkin_curve_continuous`, `galerkin_norm_le_u0`, `viscousFormSq_curve_continuousOn`)
or inline in `ArzelaAscoliTime.lean` (section (H) of `galerkin_weakLimit_R3`).
No existing declaration is moved, renamed, or edited.

**B4 decision:** the fact `V₁ u = ∑ j, ‖weightedFourierComponent u hu j‖²` is NOT
currently public anywhere — `WeightedFourierCommute.lean` states it only in its
header prose, and provides the per-component `norm_weightedFourierComponent_sq`
plus `FourierL2.viscousFormSq_R3_eq_integral_normSq_fourier` (F7).  So B4 is stated
here as the thin wrapper summing those two public lemmas.

**B9 deferral:** `galerkin_pairing_FTC` (plan task B9) is DEFERRED to PR-2 (File C),
because its proof needs the b-integrand continuity C6 for the interval-integrability
of the right-hand side; per plan §3 (B9 note) and §5 (PR-1 slice) it is NOT stated
in this PR.  The helper `stokesTestPairing_eq_sum_inner_wFC` (the weight-split
bilinear expansion B9 will use for the stokes term) IS stated here, against the
actual `stokesTestPairing_R3` definition (`Regularity.lean:123`).

## Declarations (dependency order)

- `galerkinCurve_continuousOn`          : B1 — L²-continuity of `t ↦ u(t)` on `Ici 0`
- `galerkinCurve_norm_le_u0`            : B2 — `‖u(t)‖ ≤ ‖u₀‖` for `t ≥ 0`
- `weightedFourierComponent_sub`        : B3 — wFC linearity on differences
- `viscousFormSq_eq_sum_normSq_wFC`     : B4 — `V₁ u = ∑ j, ‖wFC u hu j‖²` (thin wrapper)
- `galerkin_viscous_curve_continuousOn` : B5 — continuity of `s ↦ V₁(u s)` on `Ici 0`
- `galerkin_curve_H1_continuousOn`      : B6 — H¹-continuity: `V₁(u s − u s₀) → 0` as `s → s₀` in `Ici 0`
- `stokesTestPairing_eq_sum_inner_wFC`  : helper — stokes pairing = ∑ⱼ Re⟪wFC w, wFC u⟫ (for B7/B9)
- `stokesTestPairing_abs_le`            : B7 — `|stokes(u,w)| ≤ √V₁(u)·√V₁(w)` (weighted Cauchy–Schwarz)
- `galerkinCurve_energy_identity`       : B8 — `½‖u(b)‖² − ½‖u(a)‖² = −∫ₐᵇ V_ν(u σ)` (integrated form; the plan's working name `galerkin_energy_identity` is taken by the differential-form lemma in `GalerkinODE.lean`)
- `galerkinState_schwartzRep`           : B10 — Schwartz component representatives of Galerkin states

Dependency edges: B3, B4 → B5, B6; B5 → B8; B6, B7 (+ C6 in PR-2) → B9 (PR-2);
B1, B2, B10 independent.

## Assumptions

No axioms are introduced by this file (`axiom` count: 0), and the file is
`sorry`-free (0 `sorry`): all PR-1 scaffold placeholders (B1–B8, B10, incl. the
Codex-approved B7) have been discharged by `lean-prover`.
-/

import LerayHopf.R3.SolutionInterfaces       -- GalerkinSolutionData_R3, R3GalerkinScheme, R3NSForms, weightedFourierComponent
import LerayHopf.R3.FourierL2              -- viscousFormSq_R3_eq_integral_normSq_fourier (F7, for B4)
import LerayHopf.R3.RellichBall            -- integrable_viscous_integrand_of_memH1 (for B7's Cauchy–Schwarz)
-- Deviation from the plan's import table (recorded per task instruction): B6's proof needs
-- memH1VF_R3 closed under subtraction, i.e. the public `memH1VF_R3_add`/`memH1VF_R3_smul`
-- (plan §3 B3 references them), which live in `EnergyClassConvection.lean`.
import LerayHopf.R3.EnergyClassConvection  -- memH1VF_R3_add, memH1VF_R3_smul (sub-closure for B6)

namespace LerayHopf

open MeasureTheory Filter Topology

variable {𝔊 : R3GalerkinScheme} {F : R3NSForms 𝔊} {ν : ℝ} {u₀ : L2Sigma_R3} {n : ℕ}

/-! ### B1/B2 — L²-continuity and the uniform energy bound of the Galerkin curve -/

/-- **B1.** The Galerkin solution curve is continuous (into `L²`) on forward time:
`ContinuousOn (fun t => (gs.u t : L2VF_R3)) (Ici 0)`, from the `u_hasDeriv` field.

Fresh public mirror of the `private` `galerkin_curve_continuous` in
`AubinLionsLimitPassage.lean` (plan §2 fresh-build note). -/
theorem galerkinCurve_continuousOn (gs : GalerkinSolutionData_R3 𝔊 F ν u₀ n) :
    ContinuousOn (fun t => (gs.u t : L2VF_R3)) (Set.Ici 0) :=
  fun t ht => (gs.u_hasDeriv t ht).continuousAt.continuousWithinAt

/-- **B2.** The n-uniform energy bound along the curve: `‖u(t)‖ ≤ ‖u₀‖` for all `t ≥ 0`
(from `energy_bound` + `𝔊.norm_le`).

Fresh public mirror of the inline computation in `ArzelaAscoliTime.lean`, section (H) of
`galerkin_weakLimit_R3` (plan §2 fresh-build note). -/
theorem galerkinCurve_norm_le_u0 (gs : GalerkinSolutionData_R3 𝔊 F ν u₀ n) :
    ∀ t, 0 ≤ t → ‖(gs.u t : L2VF_R3)‖ ≤ ‖(u₀ : L2VF_R3)‖ := by
  intro t ht
  have hP : ‖𝔊.P n (u₀ : L2VF_R3)‖ ≤ ‖(u₀ : L2VF_R3)‖ := 𝔊.norm_le n (u₀ : L2VF_R3)
  have henergy := gs.energy_bound t ht
  -- `½‖uₙ t‖² ≤ ½‖P n u₀‖² ≤ ½‖u₀‖²`, so `‖uₙ t‖² ≤ ‖u₀‖²`, hence `‖uₙ t‖ ≤ ‖u₀‖`.
  have hsq : ‖(gs.u t : L2VF_R3)‖ ^ 2 ≤ ‖(u₀ : L2VF_R3)‖ ^ 2 := by
    have h2 : ‖𝔊.P n (u₀ : L2VF_R3)‖ ^ 2 ≤ ‖(u₀ : L2VF_R3)‖ ^ 2 := by
      have := mul_le_mul hP hP (norm_nonneg _) (norm_nonneg _)
      nlinarith [this]
    nlinarith [henergy, h2]
  exact le_of_sq_le_sq hsq (norm_nonneg _)

/-! ### B3/B4 — weighted-Fourier linearity and the `V₁`-as-sum identity -/

/-- **B3.** Linearity of the weighted Fourier component on differences: complements the
public `weightedFourierComponent_add`/`weightedFourierComponent_smul`
(`WeightedFourierCommute.lean`).  Proof route: `Lp.ext` on the defining a.e.
representative `√W • 𝓕(projⱼ ·)`. -/
theorem weightedFourierComponent_sub (u v : L2VF_R3) (hu : memH1VF_R3 u)
    (hv : memH1VF_R3 v) (huv : memH1VF_R3 (u - v)) (j : Fin 3) :
    weightedFourierComponent (u - v) huv j
      = weightedFourierComponent u hu j - weightedFourierComponent v hv j := by
  apply Lp.ext
  have hFeq : (FourierTransform.fourier (L2VF_projComponentC_R3 j (u - v)) : L2C_R3)
      = (FourierTransform.fourier (L2VF_projComponentC_R3 j u) : L2C_R3)
        - FourierTransform.fourier (L2VF_projComponentC_R3 j v) := by
    rw [map_sub (L2VF_projComponentC_R3 j), sub_eq_add_neg,
      ← neg_one_smul ℂ (L2VF_projComponentC_R3 j v : L2C_R3),
      FourierTransform.fourier_add, FourierTransform.fourier_smul, neg_one_smul,
      ← sub_eq_add_neg]
  have hfeq : ((FourierTransform.fourier (L2VF_projComponentC_R3 j (u - v)) : L2C_R3)
        : Domain3 → ℂ)
      =ᵐ[volume] fun ξ =>
        (FourierTransform.fourier (L2VF_projComponentC_R3 j u) : L2C_R3) ξ
          - (FourierTransform.fourier (L2VF_projComponentC_R3 j v) : L2C_R3) ξ := by
    rw [hFeq]
    exact Lp.coeFn_sub _ _
  filter_upwards [weightedFourierComponent_coeFn (u - v) huv j,
    Lp.coeFn_sub (weightedFourierComponent u hu j) (weightedFourierComponent v hv j),
    weightedFourierComponent_coeFn u hu j, weightedFourierComponent_coeFn v hv j, hfeq]
    with ξ h1 h2 h3 h4 h5
  rw [h1, h2, Pi.sub_apply, h3, h4, h5, smul_sub]

/-- **B4.** The Dirichlet-energy functional at `ν = 1` is the squared `ℓ²`-mass of the
weighted Fourier components:
`viscousFormSq_R3 1 u = ∑ j, ‖weightedFourierComponent u hu j‖²`.

Thin wrapper: sum the public per-component `norm_weightedFourierComponent_sq`
(`WeightedFourierCommute.lean:114`) over `j` and identify the total with
`viscousFormSq_R3_eq_integral_normSq_fourier` (F7, `FourierL2.lean:350`).  Stated here
because no public summed form exists (the identity appears only in
`WeightedFourierCommute.lean`'s header prose). -/
theorem viscousFormSq_eq_sum_normSq_wFC (u : L2VF_R3) (hu : memH1VF_R3 u) :
    viscousFormSq_R3 1 u = ∑ j : Fin 3, ‖weightedFourierComponent u hu j‖ ^ 2 := by
  rw [FourierL2.viscousFormSq_R3_eq_integral_normSq_fourier]
  exact Finset.sum_congr rfl fun j _ => (norm_weightedFourierComponent_sq u hu j).symm

/-! ### B5/B6 — continuity of the viscous functional and H¹-continuity along the curve -/

/-- **B5.** Continuity of the Dirichlet energy along the Galerkin curve:
`s ↦ viscousFormSq_R3 1 (u s)` is continuous on `Ici 0`, from the
`viscous_curve_continuous` field (continuity of each `s ↦ wFC (u s) j`) + B4.

Fresh public mirror of the `private` `viscousFormSq_curve_continuousOn` in
`AubinLionsLimitPassage.lean` (plan §2 fresh-build note). -/
theorem galerkin_viscous_curve_continuousOn (gs : GalerkinSolutionData_R3 𝔊 F ν u₀ n) :
    ContinuousOn (fun s => viscousFormSq_R3 1 (gs.u s : L2VF_R3)) (Set.Ici 0) := by
  have heq : ∀ s, viscousFormSq_R3 1 (gs.u s : L2VF_R3)
      = ∑ j : Fin 3, ‖weightedFourierComponent (gs.u s : L2VF_R3) (gs.reg_mem s) j‖ ^ 2 :=
    fun s => viscousFormSq_eq_sum_normSq_wFC _ (gs.reg_mem s)
  refine ContinuousOn.congr ?_ fun s _ => heq s
  exact continuousOn_finsetSum _ fun j _ => (gs.viscous_curve_continuous j).norm.pow 2

/-- **B6.** H¹-continuity of the Galerkin curve: the Dirichlet energy of the increment
vanishes as `s → s₀` within forward time,
`V₁ (u s − u s₀) → 0` as `s → s₀` in `Ici 0`.

Route: B3 + B4 turn `V₁ (u s − u s₀)` into `∑ j, ‖wFC (u s) j − wFC (u s₀) j‖²`
(memH1 of the difference via `memH1VF_R3_add`/`memH1VF_R3_smul`), which tends to `0` by
the `viscous_curve_continuous` field.  This is the H¹-continuity consumed by C6 (PR-2). -/
theorem galerkin_curve_H1_continuousOn (gs : GalerkinSolutionData_R3 𝔊 F ν u₀ n)
    (s₀ : ℝ) (hs₀ : 0 ≤ s₀) :
    Filter.Tendsto
      (fun s => viscousFormSq_R3 1 ((gs.u s : L2VF_R3) - (gs.u s₀ : L2VF_R3)))
      (nhdsWithin s₀ (Set.Ici 0)) (nhds 0) := by
  -- memH1 is closed under subtraction (`u − v = u + (−1) • v`)
  have hsub : ∀ s : ℝ, memH1VF_R3 ((gs.u s : L2VF_R3) - (gs.u s₀ : L2VF_R3)) := by
    intro s
    have h := memH1VF_R3_add (gs.reg_mem s) (memH1VF_R3_smul (-1 : ℝ) (gs.reg_mem s₀))
    rwa [neg_one_smul, ← sub_eq_add_neg] at h
  -- rewrite the Dirichlet energy of the increment via B3 + B4
  have heq : ∀ s : ℝ, viscousFormSq_R3 1 ((gs.u s : L2VF_R3) - (gs.u s₀ : L2VF_R3))
      = ∑ j : Fin 3,
          ‖weightedFourierComponent (gs.u s : L2VF_R3) (gs.reg_mem s) j
            - weightedFourierComponent (gs.u s₀ : L2VF_R3) (gs.reg_mem s₀) j‖ ^ 2 := by
    intro s
    rw [viscousFormSq_eq_sum_normSq_wFC _ (hsub s)]
    exact Finset.sum_congr rfl fun j _ => by
      rw [weightedFourierComponent_sub (gs.u s : L2VF_R3) (gs.u s₀ : L2VF_R3)
        (gs.reg_mem s) (gs.reg_mem s₀) (hsub s) j]
  -- each weighted-Fourier increment tends to 0 by the `viscous_curve_continuous` field
  have hlim : Filter.Tendsto
      (fun s => ∑ j : Fin 3,
        ‖weightedFourierComponent (gs.u s : L2VF_R3) (gs.reg_mem s) j
          - weightedFourierComponent (gs.u s₀ : L2VF_R3) (gs.reg_mem s₀) j‖ ^ 2)
      (nhdsWithin s₀ (Set.Ici 0)) (nhds 0) := by
    have h0 : (0 : ℝ) = ∑ _j : Fin 3, (0 : ℝ) := by simp
    rw [h0]
    refine tendsto_finsetSum _ fun j _ => ?_
    have hc : Filter.Tendsto
        (fun s => weightedFourierComponent (gs.u s : L2VF_R3) (gs.reg_mem s) j)
        (nhdsWithin s₀ (Set.Ici 0))
        (nhds (weightedFourierComponent (gs.u s₀ : L2VF_R3) (gs.reg_mem s₀) j)) :=
      gs.viscous_curve_continuous j s₀ hs₀
    simpa using ((hc.sub (tendsto_const_nhds
      (x := weightedFourierComponent (gs.u s₀ : L2VF_R3) (gs.reg_mem s₀) j))).norm.pow 2)
  exact hlim.congr fun s => (heq s).symm

/-! ### B7 — stokes pairing: bilinear expansion and Cauchy–Schwarz -/

/-- **Helper (for B7 here and B9 in PR-2).** Weight-split bilinear expansion of the stokes
pairing: `stokesTestPairing_R3 u w = ∑ j, Re ⟪wFC w j, wFC u j⟫_ℂ`.

Unfolding: `stokesTestPairing_R3 u w = ∑ j ∫ (2π)²‖ξ‖² · Re[𝓕uⱼ · conj(𝓕wⱼ)]`
(`Regularity.lean:123`), and with the mathlib `L²(ℂ)` inner product
(conjugate-linear in the FIRST slot) `⟪wFC w j, wFC u j⟫ = ∫ conj(√W·𝓕wⱼ) · (√W·𝓕uⱼ)
= ∫ W · conj(𝓕wⱼ) · 𝓕uⱼ`, whose real part matches the stokes integrand. -/
theorem stokesTestPairing_eq_sum_inner_wFC (u w : L2VF_R3)
    (hu : memH1VF_R3 u) (hw : memH1VF_R3 w) :
    stokesTestPairing_R3 u w
      = ∑ j : Fin 3,
          (inner (𝕜 := ℂ) (weightedFourierComponent w hw j)
            (weightedFourierComponent u hu j)).re := by
  unfold stokesTestPairing_R3
  refine Finset.sum_congr rfl fun j _ => ?_
  -- pointwise a.e.: the weighted stokes integrand is the real part of the `L²(ℂ)` inner
  -- integrand of the two weighted Fourier components
  have hpt : (fun ξ : Domain3 => (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 *
        ((FourierTransform.fourier (L2VF_projComponentC_R3 j u) : L2C_R3) ξ *
          (starRingEnd ℂ)
            ((FourierTransform.fourier (L2VF_projComponentC_R3 j w) : L2C_R3) ξ)).re)
      =ᵐ[volume] fun ξ =>
        (inner (𝕜 := ℂ) ((weightedFourierComponent w hw j : Domain3 → ℂ) ξ)
          ((weightedFourierComponent u hu j : Domain3 → ℂ) ξ)).re := by
    filter_upwards [weightedFourierComponent_coeFn w hw j,
      weightedFourierComponent_coeFn u hu j] with ξ hw' hu'
    rw [hw', hu', RCLike.inner_apply]
    -- the ℂ inner product is conjugate-linear in the FIRST slot: `⟪x, y⟫ = y * conj x`
    simp only [smul_eq_mul, map_mul, Complex.conj_ofReal]
    have hsw : sqrtViscousWeight ξ ^ 2 = (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 := by
      rw [sqrtViscousWeight_sq]; rfl
    rw [show ((sqrtViscousWeight ξ : ℂ) *
          (FourierTransform.fourier (L2VF_projComponentC_R3 j u) : L2C_R3) ξ) *
        ((sqrtViscousWeight ξ : ℂ) * (starRingEnd ℂ)
          ((FourierTransform.fourier (L2VF_projComponentC_R3 j w) : L2C_R3) ξ))
        = ((sqrtViscousWeight ξ ^ 2 : ℝ) : ℂ) *
          ((FourierTransform.fourier (L2VF_projComponentC_R3 j u) : L2C_R3) ξ *
            (starRingEnd ℂ)
              ((FourierTransform.fourier (L2VF_projComponentC_R3 j w) : L2C_R3) ξ))
      from by push_cast; ring]
    rw [Complex.re_ofReal_mul, hsw]
  calc ∫ ξ : Domain3, (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 *
        ((FourierTransform.fourier (L2VF_projComponentC_R3 j u) : L2C_R3) ξ *
          (starRingEnd ℂ)
            ((FourierTransform.fourier (L2VF_projComponentC_R3 j w) : L2C_R3) ξ)).re
        ∂(volume : Measure Domain3)
      = ∫ ξ : Domain3,
          (inner (𝕜 := ℂ) ((weightedFourierComponent w hw j : Domain3 → ℂ) ξ)
            ((weightedFourierComponent u hu j : Domain3 → ℂ) ξ)).re
          ∂(volume : Measure Domain3) := integral_congr_ae hpt
    _ = (inner (𝕜 := ℂ) (weightedFourierComponent w hw j)
          (weightedFourierComponent u hu j)).re := by
        rw [MeasureTheory.L2.inner_def (𝕜 := ℂ) (weightedFourierComponent w hw j)
          (weightedFourierComponent u hu j)]
        exact integral_re (MeasureTheory.L2.integrable_inner (𝕜 := ℂ)
          (weightedFourierComponent w hw j) (weightedFourierComponent u hu j))

/-- **B7 (Codex-gated statement).** Weighted-Fourier Cauchy–Schwarz for the stokes pairing:
for H¹ fields `u, w`,
`|stokesTestPairing_R3 u w| ≤ √(V₁ u) · √(V₁ w)` where `V₁ := viscousFormSq_R3 1`.

Route (plan §3 B7): componentwise Cauchy–Schwarz on the weighted L² integrands via
`stokesTestPairing_eq_sum_inner_wFC` (integrability from the public
`integrable_viscous_integrand_of_memH1`, `RellichBall.lean:400`), then the finite-sum
Cauchy–Schwarz `∑ aⱼbⱼ ≤ √(∑aⱼ²)·√(∑bⱼ²)` and B4 to reassemble `V₁`. -/
theorem stokesTestPairing_abs_le (u w : L2VF_R3)
    (hu : memH1VF_R3 u) (hw : memH1VF_R3 w) :
    |stokesTestPairing_R3 u w|
      ≤ Real.sqrt (viscousFormSq_R3 1 u) * Real.sqrt (viscousFormSq_R3 1 w) := by
  rw [stokesTestPairing_eq_sum_inner_wFC u w hu hw,
    viscousFormSq_eq_sum_normSq_wFC u hu, viscousFormSq_eq_sum_normSq_wFC w hw]
  -- componentwise: `|Re ⟪wFC w j, wFC u j⟫| ≤ ‖wFC u j‖ · ‖wFC w j‖` (Cauchy–Schwarz in L²(ℂ))
  have habs : |∑ j : Fin 3, (inner (𝕜 := ℂ) (weightedFourierComponent w hw j)
        (weightedFourierComponent u hu j)).re|
      ≤ ∑ j : Fin 3, ‖weightedFourierComponent u hu j‖ * ‖weightedFourierComponent w hw j‖ := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    refine (Complex.abs_re_le_norm _).trans ?_
    have h2 := norm_inner_le_norm (𝕜 := ℂ)
      (weightedFourierComponent w hw j) (weightedFourierComponent u hu j)
    rw [mul_comm] at h2
    exact h2
  refine habs.trans ?_
  -- finite-sum Cauchy–Schwarz: `∑ aⱼbⱼ ≤ √(∑ aⱼ²) · √(∑ bⱼ²)`
  refine le_of_sq_le_sq ?_ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _

/-! ### B8 — the scalar energy identity along the Galerkin curve -/

/-- Local helper (fresh copy of `stokesTestPairing_R3_diag`, `GalerkinODE.lean:175`, which
sits DOWNSTREAM of this file's import set): on the diagonal the viscous pairing is the
dissipation, `stokesTestPairing_R3 u u = viscousFormSq_R3 1 u`. -/
private theorem stokesTestPairing_R3_diag_local (u : L2VF_R3) :
    stokesTestPairing_R3 u u = viscousFormSq_R3 1 u := by
  unfold stokesTestPairing_R3 viscousFormSq_R3
  rw [one_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only
  congr 1
  rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

/-- Local helper (fresh copy of `viscousFormSq_R3_eq_smul`, `GalerkinODE.lean:166`, mul
form): the viscous dissipation scales linearly in `ν`. -/
private theorem viscousFormSq_R3_smul_local (ν : ℝ) (u : L2VF_R3) :
    viscousFormSq_R3 ν u = ν * viscousFormSq_R3 1 u := by
  unfold viscousFormSq_R3
  ring

/-- Local helper (integrand of B8; fresh `GalerkinSolutionData_R3`-level copy of the
differential-form `galerkin_energy_identity`, `GalerkinODE.lean:191`, which is stated on
`GalerkinODEInput` and sits DOWNSTREAM of this file's import set): along the Galerkin
curve, `s ↦ ½‖u(s)‖²` has forward derivative `−viscousFormSq_R3 ν (u t)` at every
`t ≥ 0`. -/
private theorem galerkinCurve_halfNormSq_hasDerivAt (gs : GalerkinSolutionData_R3 𝔊 F ν u₀ n)
    (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt (fun s => (1 / 2 : ℝ) * ‖(gs.u s : L2VF_R3)‖ ^ 2)
      (- viscousFormSq_R3 ν (gs.u t : L2VF_R3)) t := by
  set u' := deriv (fun s => (gs.u s : L2VF_R3)) t
  -- the ODE tested at `w := gs.u t` (admissible by `u_inVn`), convection killed by
  -- `b_self_zero`, stokes term collapsed to the dissipation on the diagonal
  have hode := gs.u_ode t ht (gs.u t) (gs.u_inVn t)
  rw [R3NSForms.b_self_zero F (gs.u t), add_zero, stokesTestPairing_R3_diag_local] at hode
  -- derivative of `s ↦ ⟪u s, u s⟫`
  have hinner :
      HasDerivAt (fun s => inner (𝕜 := ℝ) (gs.u s : L2VF_R3) (gs.u s : L2VF_R3))
        (inner (𝕜 := ℝ) (gs.u t : L2VF_R3) u' + inner (𝕜 := ℝ) u' (gs.u t : L2VF_R3)) t :=
    (gs.u_hasDeriv t ht).inner ℝ (gs.u_hasDeriv t ht)
  have hfun : (fun s => (1 / 2 : ℝ) * ‖(gs.u s : L2VF_R3)‖ ^ 2)
      = fun s => (1 / 2 : ℝ) * inner (𝕜 := ℝ) (gs.u s : L2VF_R3) (gs.u s : L2VF_R3) := by
    funext s
    rw [real_inner_self_eq_norm_sq]
  rw [hfun]
  have hval : (1 / 2 : ℝ) *
      (inner (𝕜 := ℝ) (gs.u t : L2VF_R3) u' + inner (𝕜 := ℝ) u' (gs.u t : L2VF_R3))
      = - viscousFormSq_R3 ν (gs.u t : L2VF_R3) := by
    have hcomm : inner (𝕜 := ℝ) (gs.u t : L2VF_R3) u' = inner (𝕜 := ℝ) u' (gs.u t : L2VF_R3) :=
      real_inner_comm _ _
    rw [hcomm, viscousFormSq_R3_smul_local ν]
    linarith [hode]
  rw [← hval]
  exact hinner.const_mul (1 / 2 : ℝ)

/-- **B8.** INTEGRATED energy identity along the Galerkin curve: for `0 ≤ a ≤ b`,
`½‖u(b)‖² − ½‖u(a)‖² = −∫ₐᵇ viscousFormSq_R3 ν (u σ) dσ`.

Named `galerkinCurve_energy_identity` (the plan's working name `galerkin_energy_identity`
is already taken by the DIFFERENTIAL-form lemma on `GalerkinODEInput` in
`GalerkinODE.lean:191`, which this integrates; content unchanged).

Route (plan §3 B8): `HasDerivAt (fun σ => ½‖u σ‖²) ⟪u'(σ), u σ⟫ σ` (inner-product calculus
on `u_hasDeriv`), the ODE field `u_ode` tested at `w := gs.u σ` (admissible by `u_inVn`),
`F.b_self_zero` to kill the convection term, then
`intervalIntegral.integral_eq_sub_of_hasDerivAt` with the continuous derivative
`σ ↦ −viscousFormSq_R3 ν (u σ)` (continuity from B5, rescaled by `ν`). -/
theorem galerkinCurve_energy_identity (gs : GalerkinSolutionData_R3 𝔊 F ν u₀ n) :
    ∀ a b : ℝ, 0 ≤ a → a ≤ b →
      (1 / 2 : ℝ) * ‖(gs.u b : L2VF_R3)‖ ^ 2 - (1 / 2 : ℝ) * ‖(gs.u a : L2VF_R3)‖ ^ 2
        = - ∫ σ in a..b, viscousFormSq_R3 ν (gs.u σ : L2VF_R3) := by
  intro a b ha hab
  have huIcc : Set.uIcc a b ⊆ Set.Ici (0 : ℝ) := by
    rw [Set.uIcc_of_le hab]
    exact fun x hx => le_trans ha hx.1
  -- the pointwise (differential-form) energy identity along the curve
  have hderiv : ∀ σ ∈ Set.uIcc a b,
      HasDerivAt (fun s => (1 / 2 : ℝ) * ‖(gs.u s : L2VF_R3)‖ ^ 2)
        (- viscousFormSq_R3 ν (gs.u σ : L2VF_R3)) σ :=
    fun σ hσ => galerkinCurve_halfNormSq_hasDerivAt gs σ (huIcc hσ)
  -- the derivative is continuous on the cell (B5 rescaled by `ν`), hence integrable
  have hcont : ContinuousOn (fun σ => - viscousFormSq_R3 ν (gs.u σ : L2VF_R3))
      (Set.uIcc a b) := by
    have h1 : ContinuousOn (fun σ => ν * viscousFormSq_R3 1 (gs.u σ : L2VF_R3))
        (Set.uIcc a b) :=
      continuousOn_const.mul ((galerkin_viscous_curve_continuousOn gs).mono huIcc)
    exact (h1.congr fun σ _ => viscousFormSq_R3_smul_local ν _).neg
  have hint : IntervalIntegrable (fun σ => - viscousFormSq_R3 ν (gs.u σ : L2VF_R3))
      volume a b := hcont.intervalIntegrable
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [intervalIntegral.integral_neg] at hFTC
  linarith [hFTC]

/-! ### B9 — DEFERRED to PR-2 (File C)

`galerkin_pairing_FTC` (plan task B9) needs the continuity of the b-integrand along the
curve (C6) for the interval-integrability hypothesis of its FTC step, so per the plan's
B9 note and the PR-1 slice (§5) it is stated and proved in PR-2, keeping the name
`galerkin_pairing_FTC`.  Nothing here is weakened: B9 was never part of this file's
contract. -/

/-! ### B10 — Schwartz representation of Galerkin states -/

/-- **B10 (plumbing).** Every Galerkin state has componentwise Schwartz representatives:
`∃ ψ : Fin 3 → 𝓢(Domain3, ℝ), ∀ j, projⱼ (u t) = (ψ j).toLp 2 volume`.

From `𝔊.range_schwartz n` applied at `𝔊.P n (gs.u t)`, transported through `u_inVn`
(`(gs.u t : L2VF_R3) = 𝔊.P n (gs.u t)`).  Feeds the `F.b_galerkin` pin and the
GNS/trilinear chain (C2–C5, PR-2). -/
theorem galerkinState_schwartzRep (gs : GalerkinSolutionData_R3 𝔊 F ν u₀ n) (t : Time) :
    ∃ ψ : Fin 3 → SchwartzMap Domain3 ℝ,
      ∀ j : Fin 3,
        L2VF_projComponent_R3 j (gs.u t : L2VF_R3)
          = (ψ j).toLp 2 (volume : Measure Domain3) := by
  obtain ⟨ψ, hψ⟩ := 𝔊.range_schwartz n (gs.u t : L2VF_R3)
  refine ⟨ψ, fun j => ?_⟩
  rw [gs.u_inVn t]
  exact hψ j

end LerayHopf
