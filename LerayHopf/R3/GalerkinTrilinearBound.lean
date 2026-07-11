/-
# LerayHopf.R3.GalerkinTrilinearBound — Issue #46 PR-2 (File C)

**Goal:** The trilinear / energy-class estimate library feeding the "good-sampling"
Simon compactness route that discharges the axiom `galerkin_spacetime_precompact_R3`
(plan: `docs/scratch/issue46-spacetime-precompact-plan.md`, §3 File C).  This file turns
the Schwartz representation of Galerkin states (B10, PR-1) into:

- the gradient-energy Plancherel identity (`V₁` as a sum of component ∂-`L²` masses),
- the componentwise `L⁶` and `L³` energy-class bounds,
- the `n`-uniform trilinear convection bound on `convIntegralSchwartz`, pushed to the
  abstract form `F.b` on Galerkin states,
- the continuity of the `b`-integrand along the Galerkin curve, and
- the pairing FTC (B9, deferred here from PR-1) that consumes it.

The load-bearing structural claim of C4/C5 is the **`n`-independence of the constant**:
in both, the existential `∃ C_b ≥ 0` sits OUTSIDE every quantifier over the fields and
the Galerkin level, so the constant cannot secretly depend on them.

## Plan §3 File C mapping

- `sum_gradSq_eq_viscousFormSq_of_schwartzRep`  : C1 — `∑_{i,a} ‖∂_a ψ_i‖²_{L²} = V₁ v`
- `eLpNorm_six_le_of_schwartzRep`               : C2 — `‖ψ_i‖_{L⁶} ≤ C₆·√(V₁ v)`
- `schwartz_trilinear_bound_L326_energy`        : C4 helper, public — the `(3,2,6)`-Hölder
  per-term trilinear bound `|∫ f·g·h| ≤ ‖f‖_{L³}·‖g‖_{L²}·‖h‖_{L⁶}` for a scalar Schwartz
  triple; a reusable fact independent of the Galerkin context, made citable this cycle
- `convIntegralSchwartz_bound_energy`           : C4 — energy-class trilinear bound (`∃ C_b` outside)
- `bForm_galerkin_abs_le`                       : C5 — same bound for `F.b` on level-`n` states
- `galerkin_bForm_curve_continuousOn`           : C6 — `b`-integrand continuous along the curve
- `galerkin_pairing_FTC`                        : B9 — pairing FTC (deferred from PR-1)

Dependency edges (plan): C1 → C2 → C4; C3 → C4 → C5 → C6; B10 → C5; B6 → C6;
B6, B7, C6 → B9.

**Post-#111-PR-2 note (supersedes the original "risk R8" note about re-derived facts):**
C1/C2/C4 used to re-derive, byte-for-byte, facts whose only existing versions were `private`
(`eLpNorm_three_le_interp`, `normSq_toLp_two`/`normSq_lineDeriv_toLp`,
`opNorm_le_sqrt_sum_sq_local`/`fderiv_apply_single_eq_lineDeriv`/`eLpNorm_fderiv_le_sum_lineDeriv`
— the byte-for-byte `_C`/`_C2`/`_pub`-suffixed re-derivations this file used to carry). Those
six declarations are gone; C1/C2/C4 now call the shared PUBLIC versions in
`LerayHopf.Analysis.PlancherelKernels` (issue #111 PR-2) directly. No remaining declaration
in this file is renamed, weakened, or edited relative to before.

**B9 landing note:** `galerkin_pairing_FTC` (plan task B9) was DEFERRED from PR-1
(`GalerkinCurveBounds.lean` header + "B9 — DEFERRED" section) because its FTC step needs
the interval-integrability of the `b`-integrand, i.e. C6, which lives here.  It lands in
this file keeping the name `galerkin_pairing_FTC` (plan §3 B9 note authorizes the move).

## Assumptions

No axioms are introduced by this file (`axiom` count: 0), and the file is `sorry`-free
(0 `sorry`): C1–C6 and B9 are all discharged.  C5 (`bForm_galerkin_abs_le`), C6
(`galerkin_bForm_curve_continuousOn`), and B9 (`galerkin_pairing_FTC`) were completed in
the PR-2 prover slice, reusing the C1–C4 private helper library.
-/

import LerayHopf.R3.GalerkinCurveBounds     -- B6, B10, GalerkinSolutionData_R3, R3NSForms, viscousFormSq_R3, stokesTestPairing_R3
import LerayHopf.R3.TrilinearEstimate       -- convIntegralSchwartz, lineDerivOpCLM, convIntegralSchwartz_bound_H1 (C4 template)
import LerayHopf.Analysis.PlancherelKernels -- the shared Plancherel-kernel quartet + eLpNorm_three_le_interp (issue #111 PR-2)
import LerayHopf.R3.GalerkinODE             -- galerkinCurve_reg_mem (issue #111 PR-5)

namespace LerayHopf

open MeasureTheory Filter Topology LineDeriv
open scoped LineDeriv

variable {𝔊 : R3GalerkinScheme} {F : R3NSForms 𝔊} {ν : ℝ} {u₀ : L2Sigma_R3} {n : ℕ}

/-! ### C1 — gradient-energy Plancherel identity for Schwartz representatives -/

open scoped FourierTransform in
/-- **C1 per-component.** For a single component `i` with real Schwartz representative `ψi`
(`L2VF_projComponent_R3 i v = ψi.toLp 2`), the sum over directions of the component partial-
derivative `L²`-masses equals the `i`-th viscous Fourier integrand. -/
private theorem component_gradSq_eq (v : L2VF_R3) (i : Fin 3) (ψi : SchwartzMap Domain3 ℝ)
    (hψi : L2VF_projComponent_R3 i v = ψi.toLp 2 (volume : Measure Domain3)) :
    ∑ a : Fin 3,
        ‖((lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
            (EuclideanSpace.single a (1 : ℝ) : Domain3) ψi).toLp
          2 (volume : Measure Domain3))‖ ^ 2
      = ∫ ξ : Domain3, (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 *
          ‖(𝓕 (L2VF_projComponentC_R3 i v) : L2C_R3) ξ‖ ^ 2 ∂(volume : Measure Domain3) := by
  classical
  set φ : SchwartzMap Domain3 ℂ := ψi.postcompCLM Complex.ofRealCLM with hφdef
  -- Coercion of `φ`: it is the complexification `x ↦ (ψi x : ℂ)`.
  have hφcoe : ∀ x, (φ : Domain3 → ℂ) x = ((ψi x : ℝ) : ℂ) := by
    intro x; simp [hφdef, SchwartzMap.postcompCLM_apply, Complex.ofRealCLM_apply]
  -- Line-derivative commutes with complexification: `(∂_m φ) x = ↑((∂_m ψi) x)`.
  have hcomm : ∀ (m x : Domain3), (∂_{m} φ) x = (((∂_{m} ψi) x : ℝ) : ℂ) := by
    intro m x
    have h1 : (∂_{m} φ) x = fderiv ℝ (⇑φ) x m := SchwartzMap.lineDerivOp_apply_eq_fderiv m φ x
    have h2 : (∂_{m} ψi) x = fderiv ℝ (⇑ψi) x m := SchwartzMap.lineDerivOp_apply_eq_fderiv m ψi x
    rw [h1, h2]
    have hHF : HasFDerivAt (⇑φ) (Complex.ofRealCLM.comp (fderiv ℝ (⇑ψi) x)) x :=
      (Complex.ofRealCLM.hasFDerivAt).comp x (ψi.differentiableAt.hasFDerivAt)
    rw [hHF.fderiv, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply]
  -- `L2VF_projComponentC_R3 i v = φ.toLp 2`.
  have hFeq : L2VF_projComponentC_R3 i v = φ.toLp 2 (volume : Measure Domain3) := by
    apply Lp.ext
    have h1 : (L2VF_projComponentC_R3 i v : Domain3 → ℂ)
        =ᵐ[volume] fun x => (RCLike.ofRealCLM (K := ℂ)) ((L2VF_projComponent_R3 i v : Domain3 → ℝ) x) :=
      ContinuousLinearMap.coeFn_compLpL (RCLike.ofRealCLM (K := ℂ)) (L2VF_projComponent_R3 i v)
    have h2 : (L2VF_projComponent_R3 i v : Domain3 → ℝ) =ᵐ[volume] ⇑ψi := by
      rw [hψi]; exact ψi.coeFn_toLp 2 (volume : Measure Domain3)
    filter_upwards [h1, h2, φ.coeFn_toLp 2 (volume : Measure Domain3)] with x hx1 hx2 hx3
    rw [hx1, hx2, hx3, hφcoe x]
    simp [RCLike.ofRealCLM_apply]
  -- Replace `𝓕 (projC_i v)` by the Schwartz `𝓕 φ` in the target integral (F6).
  have hAE := FourierL2.fourierComponentC_ae_schwartz i v φ hFeq
  have hRHS : (∫ ξ : Domain3, (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 *
        ‖(𝓕 (L2VF_projComponentC_R3 i v) : L2C_R3) ξ‖ ^ 2 ∂(volume : Measure Domain3))
      = ∫ ξ : Domain3, (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 * ‖(𝓕 φ) ξ‖ ^ 2
          ∂(volume : Measure Domain3) := by
    refine integral_congr_ae ?_
    filter_upwards [hAE] with ξ hξ
    rw [hξ]
  rw [hRHS]
  -- Split `‖ξ‖² = ∑ a ⟨ξ, e_a⟩²` inside the integral.
  have hsplit : (∫ ξ : Domain3, (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 * ‖(𝓕 φ) ξ‖ ^ 2
        ∂(volume : Measure Domain3))
      = ∑ a : Fin 3, ∫ ξ : Domain3,
          (2 * Real.pi) ^ 2 * (inner ℝ ξ (EuclideanSpace.single a (1 : ℝ) : Domain3)) ^ 2
            * ‖(𝓕 φ) ξ‖ ^ 2 ∂(volume : Measure Domain3) := by
    have hintP : ∀ a : Fin 3, Integrable
        (fun ξ : Domain3 => (2 * Real.pi) ^ 2
          * (inner ℝ ξ (EuclideanSpace.single a (1 : ℝ) : Domain3)) ^ 2 * ‖(𝓕 φ) ξ‖ ^ 2)
        (volume : Measure Domain3) := by
      intro a
      have hFR : Integrable
          (fun ξ : Domain3 => ‖(𝓕 (∂_{(EuclideanSpace.single a (1 : ℝ) : Domain3)} φ)) ξ‖ ^ 2)
          (volume : Measure Domain3) :=
        (memLp_two_iff_integrable_sq_norm
          ((𝓕 (∂_{(EuclideanSpace.single a (1 : ℝ) : Domain3)} φ)).continuous.aestronglyMeasurable)).mp
          ((𝓕 (∂_{(EuclideanSpace.single a (1 : ℝ) : Domain3)} φ)).memLp 2 (volume : Measure Domain3))
      refine hFR.congr ?_
      filter_upwards with ξ
      have hg : (inner ℝ · (EuclideanSpace.single a (1 : ℝ) : Domain3) : Domain3 → ℝ).HasTemperateGrowth :=
        ((innerSL ℝ).flip (EuclideanSpace.single a (1 : ℝ))).hasTemperateGrowth
      have hpt : (𝓕 (∂_{(EuclideanSpace.single a (1 : ℝ) : Domain3)} φ)) ξ
          = (2 * Real.pi * Complex.I)
              * (inner ℝ ξ (EuclideanSpace.single a (1 : ℝ) : Domain3) : ℝ) * (𝓕 φ) ξ := by
        rw [SchwartzMap.fourier_lineDerivOp_eq φ _, SchwartzMap.smul_apply,
          SchwartzMap.smulLeftCLM_apply_apply hg]
        simp only [smul_eq_mul, Complex.real_smul]; ring
      rw [hpt, norm_mul, norm_mul, mul_pow, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      have hI : ‖(2 * Real.pi * Complex.I)‖ = 2 * Real.pi := by
        rw [show (2 * Real.pi * Complex.I) = ((2 * Real.pi : ℝ) : ℂ) * Complex.I by push_cast; ring]
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (by positivity)]
      rw [hI]
    rw [← integral_finset_sum _ (fun a _ => hintP a)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    have hnorm : ‖ξ‖ ^ 2 = ∑ a : Fin 3, (ξ a) ^ 2 := by
      rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [Real.norm_eq_abs, sq_abs]
    have hinner : ∑ a : Fin 3, (inner ℝ ξ (EuclideanSpace.single a (1 : ℝ) : Domain3)) ^ 2
        = ‖ξ‖ ^ 2 := by
      rw [hnorm]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [EuclideanSpace.inner_single_right]
      simp
    calc (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 * ‖(𝓕 φ) ξ‖ ^ 2
        = (2 * Real.pi) ^ 2
            * (∑ a : Fin 3, (inner ℝ ξ (EuclideanSpace.single a (1 : ℝ) : Domain3)) ^ 2)
            * ‖(𝓕 φ) ξ‖ ^ 2 := by rw [hinner]
      _ = ∑ a : Fin 3, (2 * Real.pi) ^ 2
            * (inner ℝ ξ (EuclideanSpace.single a (1 : ℝ) : Domain3)) ^ 2 * ‖(𝓕 φ) ξ‖ ^ 2 := by
          rw [Finset.mul_sum, Finset.sum_mul]
  rw [hsplit]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← PlancherelKernels.normSq_lineDeriv_toLp φ (EuclideanSpace.single a (1 : ℝ))]
  rw [SchwartzMap.norm_toLp, SchwartzMap.norm_toLp]
  congr 2
  refine eLpNorm_congr_norm_ae (Filter.Eventually.of_forall fun x => ?_)
  rw [lineDerivOpCLM_apply, hcomm (EuclideanSpace.single a (1 : ℝ)) x, Complex.norm_real,
    Real.norm_eq_abs]

/-- **C1 (mathlib-gap risk R1).** The Dirichlet energy at `ν = 1` equals the total squared
`L²`-mass of the component partial derivatives of the Schwartz representatives:
`∑_i ∑_a ‖∂_a (ψ i)‖²_{L²} = viscousFormSq_R3 1 v` for any `v : L2VF_R3` whose components
are represented by `ψ` (as delivered by `galerkinState_schwartzRep`, B10).

Route (plan §3 C1): derivative-Fourier Plancherel `‖∂_a ψ_i‖²_{L²} = ∫ (2π)² ξ_a² ‖𝓕ψ_i‖²`
per component (template: private `normSq_lineDeriv_toLp`, `SobolevEmbedding.lean:243`;
rebuilt fresh), summed over `a` using `∑_a ξ_a² = ‖ξ‖²`, then over `i` to reassemble
`viscousFormSq_R3 1 v`.  The plan permits the `≤` form downstream; the equality is stated
here (prover may downgrade to `≤` if the equality fights — record it if so). -/
theorem sum_gradSq_eq_viscousFormSq_of_schwartzRep
    (v : L2VF_R3) (ψ : Fin 3 → SchwartzMap Domain3 ℝ)
    (hψ : ∀ j : Fin 3,
      L2VF_projComponent_R3 j v = (ψ j).toLp 2 (volume : Measure Domain3)) :
    ∑ i : Fin 3, ∑ a : Fin 3,
        ‖((lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
            (EuclideanSpace.single a (1 : ℝ) : Domain3) (ψ i)).toLp
          2 (volume : Measure Domain3))‖ ^ 2
      = viscousFormSq_R3 1 v := by
  rw [FourierL2.viscousFormSq_R3_eq_integral_normSq_fourier v]
  exact Finset.sum_congr rfl (fun i _ => component_gradSq_eq v i (ψ i) (hψ i))

/-- Line-derivative commutes with the complexification `postcompCLM ofRealCLM`:
`(∂_m (ψi ∘ ↑)) x = ↑((∂_m ψi) x)`. -/
private theorem lineDeriv_postcomp_apply (ψi : SchwartzMap Domain3 ℝ) (m x : Domain3) :
    (∂_{m} (ψi.postcompCLM Complex.ofRealCLM)) x = (((∂_{m} ψi) x : ℝ) : ℂ) := by
  have h1 : (∂_{m} (ψi.postcompCLM Complex.ofRealCLM)) x
      = fderiv ℝ (⇑(ψi.postcompCLM Complex.ofRealCLM)) x m :=
    SchwartzMap.lineDerivOp_apply_eq_fderiv m _ x
  have h2 : (∂_{m} ψi) x = fderiv ℝ (⇑ψi) x m := SchwartzMap.lineDerivOp_apply_eq_fderiv m ψi x
  rw [h1, h2]
  have hHF : HasFDerivAt (⇑(ψi.postcompCLM Complex.ofRealCLM))
      (Complex.ofRealCLM.comp (fderiv ℝ (⇑ψi) x)) x :=
    (Complex.ofRealCLM.hasFDerivAt).comp x (ψi.differentiableAt.hasFDerivAt)
  rw [hHF.fderiv, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply]

/-! ### C2 — componentwise `L⁶` energy-class bound -/

/-- **C2.** Componentwise `L⁶` bound in terms of the Dirichlet energy: there is an absolute
coefficient `C₆ ≥ 0` (independent of `v`, `ψ`, and the component `i`) with
`eLpNorm (ψ i) 6 ≤ ENNReal.ofReal (C₆ · √(V₁ v))` for every Schwartz representative `ψ`
of `v` and every component `i`.

The `∃ C₆` sits OUTSIDE the quantifiers over `v`, `ψ`, `i`, so the constant is genuinely
absolute (Gagliardo–Nirenberg–Sobolev has no field dependence).

Route (plan §3 C2): `gns_L6_schwartz` (public GNS on `Domain3`; complex- or real-valued
variant, whichever typechecks) bounding `‖ψ_i‖₆` by `eLpNorm (fderiv ψ_i) 2`, bridged to
`∑_a ‖∂_a ψ_i‖²` (template: private `eLpNorm_fderiv_le_sum_lineDeriv`,
`EnergyClassConvection.lean:1174`; rebuilt fresh), then C1 to reach `√(V₁ v)`. -/
theorem eLpNorm_six_le_of_schwartzRep :
    ∃ C₆ : ℝ, 0 ≤ C₆ ∧
      ∀ (v : L2VF_R3) (ψ : Fin 3 → SchwartzMap Domain3 ℝ),
        (∀ j : Fin 3,
          L2VF_projComponent_R3 j v = (ψ j).toLp 2 (volume : Measure Domain3)) →
        ∀ i : Fin 3,
          eLpNorm ((ψ i : Domain3 → ℝ)) 6 (volume : Measure Domain3)
            ≤ ENNReal.ofReal (C₆ * Real.sqrt (viscousFormSq_R3 1 v)) := by
  classical
  refine ⟨(SNormLESNormFDerivOfEqConst ℂ (volume : Measure Domain3) 2 : ℝ) * Real.sqrt 3,
    by positivity, ?_⟩
  intro v ψ hψ i
  set φ : SchwartzMap Domain3 ℂ := (ψ i).postcompCLM Complex.ofRealCLM with hφdef
  -- (1) `‖ψ i‖₆ = ‖φ‖₆` (complexification is norm-preserving).
  have h6eq : eLpNorm ((ψ i : Domain3 → ℝ)) 6 (volume : Measure Domain3)
      = eLpNorm ((φ : Domain3 → ℂ)) 6 (volume : Measure Domain3) := by
    refine eLpNorm_congr_norm_ae (Filter.Eventually.of_forall fun x => ?_)
    rw [hφdef, SchwartzMap.postcompCLM_apply, Complex.ofRealCLM_apply, Complex.norm_real]
  rw [h6eq]
  -- (2) GNS and gradient → sum-of-lineDerivs.
  refine (gns_L6_schwartz φ).trans ?_
  refine (mul_le_mul_left' (PlancherelKernels.eLpNorm_fderiv_le_sum_lineDeriv φ) _).trans ?_
  -- (3) Identify each directional `L²` mass with `‖(∂_a ψ i).toLp‖`.
  have hcell : ∀ a : Fin 3,
      eLpNorm (fun x => (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℂ)
          (EuclideanSpace.single a (1 : ℝ)) φ) x) 2 (volume : Measure Domain3)
      = ENNReal.ofReal ‖(lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
          (EuclideanSpace.single a (1 : ℝ)) (ψ i)).toLp 2 (volume : Measure Domain3)‖ := by
    intro a
    have hcong : eLpNorm (fun x => (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℂ)
          (EuclideanSpace.single a (1 : ℝ)) φ) x) 2 (volume : Measure Domain3)
        = eLpNorm (fun x => (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
          (EuclideanSpace.single a (1 : ℝ)) (ψ i)) x) 2 (volume : Measure Domain3) := by
      refine eLpNorm_congr_norm_ae (Filter.Eventually.of_forall fun x => ?_)
      rw [lineDerivOpCLM_apply, lineDerivOpCLM_apply, hφdef,
        lineDeriv_postcomp_apply (ψ i) (EuclideanSpace.single a (1 : ℝ)) x, Complex.norm_real,
        Real.norm_eq_abs]
    rw [hcong, SchwartzMap.norm_toLp,
      ENNReal.ofReal_toReal (SchwartzMap.eLpNorm_lt_top _ 2 (volume : Measure Domain3)).ne]
  have hsum_eq : (∑ a : Fin 3, eLpNorm (fun x => (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℂ)
        (EuclideanSpace.single a (1 : ℝ)) φ) x) 2 (volume : Measure Domain3))
      = ENNReal.ofReal (∑ a : Fin 3, ‖(lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
          (EuclideanSpace.single a (1 : ℝ)) (ψ i)).toLp 2 (volume : Measure Domain3)‖) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun a _ => norm_nonneg _)]
    exact Finset.sum_congr rfl (fun a _ => hcell a)
  rw [hsum_eq]
  -- (4) Real bound: `∑_a ‖(∂_a ψ i).toLp‖ ≤ √3 · √(V₁ v)`.
  set x : Fin 3 → ℝ := fun a => ‖(lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
    (EuclideanSpace.single a (1 : ℝ)) (ψ i)).toLp 2 (volume : Measure Domain3)‖ with hx
  have hxsq_le : ∑ a : Fin 3, x a ^ 2 ≤ viscousFormSq_R3 1 v := by
    rw [← sum_gradSq_eq_viscousFormSq_of_schwartzRep v ψ hψ]
    exact Finset.single_le_sum
      (f := fun i' => ∑ a : Fin 3, ‖(lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
        (EuclideanSpace.single a (1 : ℝ)) (ψ i')).toLp 2 (volume : Measure Domain3)‖ ^ 2)
      (fun i' _ => Finset.sum_nonneg (fun a _ => sq_nonneg _)) (Finset.mem_univ i)
  have hnn : (0 : ℝ) ≤ ∑ a : Fin 3, x a := Finset.sum_nonneg (fun a _ => norm_nonneg _)
  have hcs : (∑ a : Fin 3, x a) ^ 2 ≤ (3 : ℝ) * ∑ a : Fin 3, x a ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 3)) x (fun _ => (1 : ℝ))
    simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_ofNat] at h
    linarith
  have hle : ∑ a : Fin 3, x a ≤ Real.sqrt 3 * Real.sqrt (viscousFormSq_R3 1 v) := by
    have h3V : (∑ a : Fin 3, x a) ^ 2 ≤ 3 * viscousFormSq_R3 1 v :=
      hcs.trans (by gcongr)
    calc ∑ a : Fin 3, x a = Real.sqrt ((∑ a : Fin 3, x a) ^ 2) := (Real.sqrt_sq hnn).symm
      _ ≤ Real.sqrt (3 * viscousFormSq_R3 1 v) := Real.sqrt_le_sqrt h3V
      _ = Real.sqrt 3 * Real.sqrt (viscousFormSq_R3 1 v) :=
          Real.sqrt_mul (by norm_num) _
  -- (5) Assemble in ENNReal.
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left hle (by positivity)


/-- Local scalar Schwartz product used in the C4 Hölder estimate. -/
private noncomputable def schwartzMul_energy
    (f g : SchwartzMap Domain3 ℝ) : SchwartzMap Domain3 ℝ :=
  SchwartzMap.bilinLeftCLM (ContinuousLinearMap.mul ℝ ℝ) g.hasTemperateGrowth f

@[simp] private theorem schwartzMul_energy_apply (f g : SchwartzMap Domain3 ℝ) (x : Domain3) :
    schwartzMul_energy f g x = f x * g x := by
  simp [schwartzMul_energy, ContinuousLinearMap.mul_apply']

/-- L¹ Cauchy-Schwarz for two scalar Schwartz functions. -/
private theorem schwartz_integral_abs_mul_le_energy (f g : SchwartzMap Domain3 ℝ) :
    (∫ x : Domain3, |f x| * |g x| ∂(volume : Measure Domain3))
      ≤ ‖f.toLp 2 (volume : Measure Domain3)‖ * ‖g.toLp 2 (volume : Measure Domain3)‖ := by
  have hf : MemLp (f : Domain3 → ℝ) (ENNReal.ofReal 2) (volume : Measure Domain3) := by
    have := f.memLp 2 (volume : Measure Domain3)
    simpa using this
  have hg : MemLp (g : Domain3 → ℝ) (ENNReal.ofReal 2) (volume : Measure Domain3) := by
    have := g.memLp 2 (volume : Measure Domain3)
    simpa using this
  have hmain := MeasureTheory.integral_mul_norm_le_Lp_mul_Lq
    (μ := (volume : Measure Domain3)) (f := (f : Domain3 → ℝ)) (g := (g : Domain3 → ℝ))
    (Real.HolderConjugate.two_two) hf hg
  have hnf : ‖f.toLp 2 (volume : Measure Domain3)‖
      = (∫ x : Domain3, ‖f x‖ ^ (2 : ℝ) ∂(volume : Measure Domain3)) ^ (1 / (2 : ℝ)) := by
    rw [SchwartzMap.norm_toLp' (by simp) (by simp)]
    norm_num
  have hng : ‖g.toLp 2 (volume : Measure Domain3)‖
      = (∫ x : Domain3, ‖g x‖ ^ (2 : ℝ) ∂(volume : Measure Domain3)) ^ (1 / (2 : ℝ)) := by
    rw [SchwartzMap.norm_toLp' (by simp) (by simp)]
    norm_num
  rw [hnf, hng]
  calc (∫ x : Domain3, |f x| * |g x| ∂(volume : Measure Domain3))
      = ∫ x : Domain3, ‖f x‖ * ‖g x‖ ∂(volume : Measure Domain3) := by
        simp only [Real.norm_eq_abs]
    _ ≤ _ := hmain

/-- The `(3,6) -> 2` Hölder step for a product of two Schwartz factors. -/
private theorem schwartz_mul_L2_norm_le_L3_L6_energy (f h : SchwartzMap Domain3 ℝ) :
    ‖(schwartzMul_energy f h).toLp 2 (volume : Measure Domain3)‖
      ≤ (eLpNorm (f : Domain3 → ℝ) 3 (volume : Measure Domain3)).toReal
        * (eLpNorm (h : Domain3 → ℝ) 6 (volume : Measure Domain3)).toReal := by
  haveI : ENNReal.HolderTriple 3 6 2 := by
    have h : Real.HolderTriple (3 : ℝ) (6 : ℝ) (2 : ℝ) := by constructor <;> norm_num
    simpa only [ENNReal.ofReal_ofNat] using h.ennrealOfReal
  have hholder : eLpNorm (fun x : Domain3 => f x * h x) 2 (volume : Measure Domain3)
      ≤ eLpNorm (f : Domain3 → ℝ) 3 (volume : Measure Domain3)
        * eLpNorm (h : Domain3 → ℝ) 6 (volume : Measure Domain3) := by
    have := MeasureTheory.eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm (p := (3 : ENNReal))
      (q := (6 : ENNReal)) (r := (2 : ENNReal))
      (μ := (volume : Measure Domain3))
      f.continuous.aestronglyMeasurable h.continuous.aestronglyMeasurable
      (fun a b : ℝ => a * b) 1
      (Filter.Eventually.of_forall fun x => by
        simp only [nnnorm_mul, one_mul]
        exact le_refl _)
    simpa only [ENNReal.coe_one, one_mul] using this
  rw [SchwartzMap.norm_toLp, ← ENNReal.toReal_mul]
  refine ENNReal.toReal_mono ?_ ?_
  · exact ENNReal.mul_ne_top (SchwartzMap.eLpNorm_lt_top f 3 (volume : Measure Domain3)).ne
      (SchwartzMap.eLpNorm_lt_top h 6 (volume : Measure Domain3)).ne
  · refine (eLpNorm_congr_norm_ae (Filter.Eventually.of_forall fun x => ?_)).le.trans hholder
    simp [schwartzMul_energy]

/-- **`(3,2,6)`-Hölder trilinear bound for a scalar Schwartz triple.**
`|∫ f·g·h| ≤ ‖f‖_{L³}·‖g‖_{L²}·‖h‖_{L⁶}`, split via `(3,6) → 2` Hölder on `f·h` then
Cauchy–Schwarz against `g`. This is the capstone of the C4 trilinear-bound machinery in this
file — the two helpers it consumes (`schwartz_integral_abs_mul_le_energy`,
`schwartz_mul_L2_norm_le_L3_L6_energy`) are small and file-local, but this per-term bound is
a genuinely reusable fact independent of the Galerkin-specific context (`convIntegralSchwartz_bound_energy`)
that consumes it below, so it is public. -/
theorem schwartz_trilinear_bound_L326_energy (f g h : SchwartzMap Domain3 ℝ) :
    |∫ x : Domain3, (f x) * (g x) * (h x) ∂(volume : Measure Domain3)|
      ≤ (eLpNorm (f : Domain3 → ℝ) 3 (volume : Measure Domain3)).toReal
        * ‖g.toLp 2 (volume : Measure Domain3)‖
        * (eLpNorm (h : Domain3 → ℝ) 6 (volume : Measure Domain3)).toReal := by
  have hint : Integrable
      (fun x : Domain3 => (f x) * (g x) * (h x)) (volume : Measure Domain3) := by
    have hi := (schwartzMul_energy (schwartzMul_energy f g) h).integrable
      (μ := (volume : Measure Domain3))
    refine hi.congr ?_
    filter_upwards with x
    simp [mul_assoc]
  calc |∫ x : Domain3, (f x) * (g x) * (h x) ∂(volume : Measure Domain3)|
      = ‖∫ x : Domain3, (f x) * (g x) * (h x) ∂(volume : Measure Domain3)‖ := by
        rw [Real.norm_eq_abs]
    _ ≤ ∫ x : Domain3, ‖(f x) * (g x) * (h x)‖ ∂(volume : Measure Domain3) :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ = ∫ x : Domain3, |(schwartzMul_energy f h) x| * |g x| ∂(volume : Measure Domain3) := by
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards with x
        simp [abs_mul, Real.norm_eq_abs, mul_left_comm, mul_comm]
    _ ≤ ‖(schwartzMul_energy f h).toLp 2 (volume : Measure Domain3)‖
        * ‖g.toLp 2 (volume : Measure Domain3)‖ :=
        schwartz_integral_abs_mul_le_energy (schwartzMul_energy f h) g
    _ ≤ ((eLpNorm (f : Domain3 → ℝ) 3 (volume : Measure Domain3)).toReal
        * (eLpNorm (h : Domain3 → ℝ) 6 (volume : Measure Domain3)).toReal)
        * ‖g.toLp 2 (volume : Measure Domain3)‖ := by
        exact mul_le_mul_of_nonneg_right (schwartz_mul_L2_norm_le_L3_L6_energy f h)
          (norm_nonneg _)
    _ = (eLpNorm (f : Domain3 → ℝ) 3 (volume : Measure Domain3)).toReal
        * ‖g.toLp 2 (volume : Measure Domain3)‖
        * (eLpNorm (h : Domain3 → ℝ) 6 (volume : Measure Domain3)).toReal := by ring

/-- The lifted Euclidean component projection is norm-nonincreasing on `L²`. -/
private theorem L2VF_projComponent_R3_norm_le_energy (j : Fin 3) (u : L2VF_R3) :
    ‖L2VF_projComponent_R3 j u‖ ≤ ‖u‖ := by
  apply MeasureTheory.Lp.norm_le_norm_of_ae_le
  filter_upwards [show (L2VF_projComponent_R3 j u : Domain3 → ℝ)
      =ᵐ[volume] fun x => (EuclideanSpace.proj (𝕜 := ℝ) j) (u x) by
        simpa [L2VF_projComponent_R3] using
          (EuclideanSpace.proj (𝕜 := ℝ) j).coeFn_compLpL (p := 2)
            (μ := (volume : Measure Domain3)) u] with x hx
  rw [hx]
  simpa [EuclideanSpace.coe_proj] using
    (PiLp.norm_apply_le ((u : Domain3 → EuclideanSpace ℝ (Fin 3)) x) j)

private theorem rpow_const_sqrt_quarter_energy {C V : ℝ} (hC : 0 ≤ C) (hV : 0 ≤ V) :
    (C * Real.sqrt V) ^ (1 / 2 : ℝ) = Real.sqrt C * V ^ (1 / 4 : ℝ) := by
  rw [Real.mul_rpow hC (Real.sqrt_nonneg _)]
  rw [← Real.sqrt_eq_rpow C]
  rw [Real.sqrt_eq_rpow V]
  rw [← Real.rpow_mul hV]
  norm_num

private theorem eLpNorm_six_toReal_le_energy
    (C₆ : ℝ) (hC₆0 : 0 ≤ C₆)
    (hC₆ : ∀ (v : L2VF_R3) (ψ : Fin 3 → SchwartzMap Domain3 ℝ),
        (∀ j : Fin 3,
          L2VF_projComponent_R3 j v = (ψ j).toLp 2 (volume : Measure Domain3)) →
        ∀ i : Fin 3,
          eLpNorm ((ψ i : Domain3 → ℝ)) 6 (volume : Measure Domain3)
            ≤ ENNReal.ofReal (C₆ * Real.sqrt (viscousFormSq_R3 1 v)))
    (v : L2VF_R3) (ψ : Fin 3 → SchwartzMap Domain3 ℝ)
    (hψ : ∀ j : Fin 3,
      L2VF_projComponent_R3 j v = (ψ j).toLp 2 (volume : Measure Domain3))
    (i : Fin 3) :
    (eLpNorm ((ψ i : Domain3 → ℝ)) 6 (volume : Measure Domain3)).toReal
      ≤ C₆ * Real.sqrt (viscousFormSq_R3 1 v) := by
  have hnon : 0 ≤ C₆ * Real.sqrt (viscousFormSq_R3 1 v) :=
    mul_nonneg hC₆0 (Real.sqrt_nonneg _)
  have hle := hC₆ v ψ hψ i
  have hreal := ENNReal.toReal_mono (by simp) hle
  rwa [ENNReal.toReal_ofReal hnon] at hreal

private theorem lineDeriv_toLp_norm_le_sqrt_viscous_energy
    (v : L2VF_R3) (ψ : Fin 3 → SchwartzMap Domain3 ℝ)
    (hψ : ∀ j : Fin 3,
      L2VF_projComponent_R3 j v = (ψ j).toLp 2 (volume : Measure Domain3))
    (i a : Fin 3) :
    ‖((lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
        (EuclideanSpace.single a (1 : ℝ) : Domain3) (ψ i)).toLp
      2 (volume : Measure Domain3))‖
      ≤ Real.sqrt (viscousFormSq_R3 1 v) := by
  set B : ℝ := ‖((lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
        (EuclideanSpace.single a (1 : ℝ) : Domain3) (ψ i)).toLp
      2 (volume : Measure Domain3))‖ with hB
  have hBsq_le : B ^ 2 ≤ viscousFormSq_R3 1 v := by
    rw [← sum_gradSq_eq_viscousFormSq_of_schwartzRep v ψ hψ]
    have hinner : B ^ 2 ≤ ∑ a' : Fin 3,
        ‖((lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
            (EuclideanSpace.single a' (1 : ℝ) : Domain3) (ψ i)).toLp
          2 (volume : Measure Domain3))‖ ^ 2 := by
      rw [hB]
      exact Finset.single_le_sum
        (f := fun a' : Fin 3 => ‖((lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
            (EuclideanSpace.single a' (1 : ℝ) : Domain3) (ψ i)).toLp
          2 (volume : Measure Domain3))‖ ^ 2)
        (fun a' _ => sq_nonneg _) (Finset.mem_univ a)
    exact hinner.trans <|
      Finset.single_le_sum
        (f := fun i' : Fin 3 => ∑ a' : Fin 3,
          ‖((lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
              (EuclideanSpace.single a' (1 : ℝ) : Domain3) (ψ i')).toLp
            2 (volume : Measure Domain3))‖ ^ 2)
        (fun i' _ => Finset.sum_nonneg (fun a' _ => sq_nonneg _)) (Finset.mem_univ i)
  calc B = Real.sqrt (B ^ 2) := (Real.sqrt_sq (by rw [hB]; exact norm_nonneg _)).symm
    _ ≤ Real.sqrt (viscousFormSq_R3 1 v) := Real.sqrt_le_sqrt hBsq_le

private theorem eLpNorm_three_component_toReal_le_energy
    (C₆ : ℝ) (hC₆0 : 0 ≤ C₆)
    (hC₆ : ∀ (v : L2VF_R3) (ψ : Fin 3 → SchwartzMap Domain3 ℝ),
        (∀ j : Fin 3,
          L2VF_projComponent_R3 j v = (ψ j).toLp 2 (volume : Measure Domain3)) →
        ∀ i : Fin 3,
          eLpNorm ((ψ i : Domain3 → ℝ)) 6 (volume : Measure Domain3)
            ≤ ENNReal.ofReal (C₆ * Real.sqrt (viscousFormSq_R3 1 v)))
    (u : L2VF_R3) (ψ : Fin 3 → SchwartzMap Domain3 ℝ)
    (hψ : ∀ j : Fin 3,
      L2VF_projComponent_R3 j u = (ψ j).toLp 2 (volume : Measure Domain3))
    (a : Fin 3) :
    (eLpNorm ((ψ a : Domain3 → ℝ)) 3 (volume : Measure Domain3)).toReal
      ≤ Real.sqrt C₆ * ‖u‖ ^ (1 / 2 : ℝ) * (viscousFormSq_R3 1 u) ^ (1 / 4 : ℝ) := by
  have h2 : MemLp ((ψ a : Domain3 → ℝ)) 2 (volume : Measure Domain3) := by
    simpa using (ψ a).memLp 2 (volume : Measure Domain3)
  have h6 : MemLp ((ψ a : Domain3 → ℝ)) 6 (volume : Measure Domain3) := by
    simpa using (ψ a).memLp 6 (volume : Measure Domain3)
  have hinterp := PlancherelKernels.eLpNorm_three_le_interp ((ψ a : Domain3 → ℝ)) h2 h6
  have hfin_rhs : ((eLpNorm ((ψ a : Domain3 → ℝ)) 2 (volume : Measure Domain3)) ^ (1 / 2 : ℝ)
        * (eLpNorm ((ψ a : Domain3 → ℝ)) 6 (volume : Measure Domain3)) ^ (1 / 2 : ℝ)) ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · exact (ENNReal.rpow_lt_top_of_nonneg (by norm_num)
        (SchwartzMap.eLpNorm_lt_top (ψ a) 2 (volume : Measure Domain3)).ne).ne
    · exact (ENNReal.rpow_lt_top_of_nonneg (by norm_num)
        (SchwartzMap.eLpNorm_lt_top (ψ a) 6 (volume : Measure Domain3)).ne).ne
  have hreal := ENNReal.toReal_mono hfin_rhs hinterp
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow] at hreal
  rw [← (SchwartzMap.norm_toLp (f := ψ a) (p := (2 : ENNReal))
    (μ := (volume : Measure Domain3)))] at hreal
  have hL2 : ‖(ψ a).toLp 2 (volume : Measure Domain3)‖ ≤ ‖u‖ := by
    rw [← hψ a]
    exact L2VF_projComponent_R3_norm_le_energy a u
  have hL6 := eLpNorm_six_toReal_le_energy C₆ hC₆0 hC₆ u ψ hψ a
  have hu_nn : 0 ≤ ‖u‖ := norm_nonneg _
  have hV_nn : 0 ≤ viscousFormSq_R3 1 u := viscousFormSq_R3_nonneg zero_le_one u
  calc (eLpNorm ((ψ a : Domain3 → ℝ)) 3 (volume : Measure Domain3)).toReal
      ≤ ‖(ψ a).toLp 2 (volume : Measure Domain3)‖ ^ (1 / 2 : ℝ)
          * (eLpNorm ((ψ a : Domain3 → ℝ)) 6 (volume : Measure Domain3)).toReal ^ (1 / 2 : ℝ) := hreal
    _ ≤ ‖u‖ ^ (1 / 2 : ℝ) * (C₆ * Real.sqrt (viscousFormSq_R3 1 u)) ^ (1 / 2 : ℝ) := by
        exact mul_le_mul
          (Real.rpow_le_rpow (norm_nonneg _) hL2 (by norm_num))
          (Real.rpow_le_rpow (ENNReal.toReal_nonneg) hL6 (by norm_num))
          (Real.rpow_nonneg ENNReal.toReal_nonneg _)
          (Real.rpow_nonneg hu_nn _)
    _ = Real.sqrt C₆ * ‖u‖ ^ (1 / 2 : ℝ) * (viscousFormSq_R3 1 u) ^ (1 / 4 : ℝ) := by
        rw [rpow_const_sqrt_quarter_energy hC₆0 hV_nn]
        ring

/-- **C4 (Codex-gated statement).** Energy-class bound on the Schwartz convection integral:
there is an absolute constant `C_b ≥ 0` such that for ALL triples of `L²`-fields `u v w`
with Schwartz representatives `ψu ψv ψw` (componentwise `toLp` equalities),
`|convIntegralSchwartz ψu ψv ψw|
    ≤ C_b · ‖u‖^{1/2} · (V₁ u)^{1/4} · √(V₁ v) · √(V₁ w)`.

The `∃ C_b` sits OUTSIDE the quantifiers over `u, v, w, ψu, ψv, ψw`, making the
field-independence (hence the eventual `n`-independence in C5) structurally evident.

Route (plan §3 C4): per-`(i,a)` Hölder with exponents `(3,2,6)` on `∫ u_a (∂_a v_i) w_i`,
then `‖u_a‖₃ ≤ ‖u_a‖₂^{1/2}‖u_a‖₆^{1/2}` (C3), `‖u_a‖₆, ‖w_i‖₆ ≤ C₆√V₁` (C2),
`‖∂_a v_i‖₂ ≤ √(V₁ v)` (C1), and finite-sum aggregation (pattern of
`convIntegralSchwartz_bound_H1`).  Interpolating `‖u‖₂` and `√(V₁ u)` yields the
`‖u‖^{1/2}(V₁ u)^{1/4}` factor. -/
theorem convIntegralSchwartz_bound_energy :
    ∃ C_b : ℝ, 0 ≤ C_b ∧
      ∀ (u v w : L2VF_R3) (ψu ψv ψw : Fin 3 → SchwartzMap Domain3 ℝ),
        (∀ j : Fin 3,
          L2VF_projComponent_R3 j u = (ψu j).toLp 2 (volume : Measure Domain3)) →
        (∀ j : Fin 3,
          L2VF_projComponent_R3 j v = (ψv j).toLp 2 (volume : Measure Domain3)) →
        (∀ j : Fin 3,
          L2VF_projComponent_R3 j w = (ψw j).toLp 2 (volume : Measure Domain3)) →
        |convIntegralSchwartz ψu ψv ψw|
          ≤ C_b * ‖u‖ ^ (1 / 2 : ℝ) * (viscousFormSq_R3 1 u) ^ (1 / 4 : ℝ)
              * Real.sqrt (viscousFormSq_R3 1 v) * Real.sqrt (viscousFormSq_R3 1 w) := by
  classical
  obtain ⟨C₆, hC₆0, hC₆⟩ := eLpNorm_six_le_of_schwartzRep
  refine ⟨9 * (Real.sqrt C₆ * C₆), ?_, ?_⟩
  · exact mul_nonneg (by norm_num) (mul_nonneg (Real.sqrt_nonneg _) hC₆0)
  intro u v w ψu ψv ψw hψu hψv hψw
  set D : ℝ := Real.sqrt C₆ * C₆ * ‖u‖ ^ (1 / 2 : ℝ)
    * (viscousFormSq_R3 1 u) ^ (1 / 4 : ℝ)
    * Real.sqrt (viscousFormSq_R3 1 v) * Real.sqrt (viscousFormSq_R3 1 w) with hD
  have hterm : ∀ i a : Fin 3,
      |∫ x : Domain3,
        (ψu a x) *
        ((lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
            (EuclideanSpace.single a (1 : ℝ) : Domain3) (ψv i)) x) *
        (ψw i x) ∂(volume : Measure Domain3)| ≤ D := by
    intro i a
    set dg : SchwartzMap Domain3 ℝ := lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
      (EuclideanSpace.single a (1 : ℝ) : Domain3) (ψv i) with hdg
    have hbase := schwartz_trilinear_bound_L326_energy (ψu a) dg (ψw i)
    rw [hdg] at hbase
    have hu3 := eLpNorm_three_component_toReal_le_energy C₆ hC₆0 hC₆ u ψu hψu a
    have hv2 := lineDeriv_toLp_norm_le_sqrt_viscous_energy v ψv hψv i a
    have hw6 := eLpNorm_six_toReal_le_energy C₆ hC₆0 hC₆ w ψw hψw i
    have hu3_rhs_nonneg : 0 ≤ Real.sqrt C₆ * ‖u‖ ^ (1 / 2 : ℝ)
        * (viscousFormSq_R3 1 u) ^ (1 / 4 : ℝ) := by
      exact mul_nonneg
        (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _))
        (Real.rpow_nonneg (viscousFormSq_R3_nonneg zero_le_one u) _)
    have hAB : (eLpNorm ((ψu a : Domain3 → ℝ)) 3 (volume : Measure Domain3)).toReal
        * ‖((lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
            (EuclideanSpace.single a (1 : ℝ) : Domain3) (ψv i)).toLp
          2 (volume : Measure Domain3))‖
        ≤ (Real.sqrt C₆ * ‖u‖ ^ (1 / 2 : ℝ)
            * (viscousFormSq_R3 1 u) ^ (1 / 4 : ℝ))
          * Real.sqrt (viscousFormSq_R3 1 v) := by
      exact mul_le_mul hu3 hv2 (norm_nonneg _) hu3_rhs_nonneg
    have hABC : (eLpNorm ((ψu a : Domain3 → ℝ)) 3 (volume : Measure Domain3)).toReal
        * ‖((lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
            (EuclideanSpace.single a (1 : ℝ) : Domain3) (ψv i)).toLp
          2 (volume : Measure Domain3))‖
        * (eLpNorm ((ψw i : Domain3 → ℝ)) 6 (volume : Measure Domain3)).toReal
        ≤ ((Real.sqrt C₆ * ‖u‖ ^ (1 / 2 : ℝ)
            * (viscousFormSq_R3 1 u) ^ (1 / 4 : ℝ))
          * Real.sqrt (viscousFormSq_R3 1 v))
          * (C₆ * Real.sqrt (viscousFormSq_R3 1 w)) := by
      exact mul_le_mul hAB hw6 ENNReal.toReal_nonneg
        (mul_nonneg hu3_rhs_nonneg (Real.sqrt_nonneg _))
    exact hbase.trans <| hABC.trans_eq (by rw [hD]; ring)
  calc |convIntegralSchwartz ψu ψv ψw|
      ≤ ∑ i : Fin 3, ∑ a : Fin 3, D := by
        unfold convIntegralSchwartz
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
        refine Finset.sum_le_sum (fun i _ => ?_)
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
        exact Finset.sum_le_sum (fun a _ => hterm i a)
    _ = 9 * D := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
    _ = (9 * (Real.sqrt C₆ * C₆)) * ‖u‖ ^ (1 / 2 : ℝ)
          * (viscousFormSq_R3 1 u) ^ (1 / 4 : ℝ)
          * Real.sqrt (viscousFormSq_R3 1 v) * Real.sqrt (viscousFormSq_R3 1 w) := by
        rw [hD]
        ring

/-! ### C5 — `n`-uniform trilinear bound for the abstract form `F.b` -/

/-- **C5 (Codex-gated statement — `n`-uniformity is the load-bearing claim).** The abstract
convection form `F.b` obeys the same energy-class bound as `convIntegralSchwartz`, uniformly
over the Galerkin level `n`: for the ambient scheme `𝔊` and forms `F` there is a constant
`C_b ≥ 0` (obtained from C4's absolute constant) such that for ALL levels `n` and ALL level-`n` states `u v w : L2Sigma_R3`
(`(u:L2VF_R3) = 𝔊.P n u`, likewise `v`, `w`),
`|F.b u v w| ≤ C_b · ‖u‖^{1/2} · (V₁ u)^{1/4} · √(V₁ v) · √(V₁ w)`.

The `∃ C_b` sits OUTSIDE the quantifier over `n` and the states, so the constant is
provably `n`-independent — the property the good-sampling compactness argument needs.

Route (plan §3 C5): B10 Schwartz representations of `u, v, w`, the `F.b_galerkin` pin to
`convIntegralSchwartz`, and C4. -/
theorem bForm_galerkin_abs_le :
    ∃ C_b : ℝ, 0 ≤ C_b ∧
      ∀ (n : ℕ) (u v w : L2Sigma_R3),
        (u : L2VF_R3) = 𝔊.P n (u : L2VF_R3) →
        (v : L2VF_R3) = 𝔊.P n (v : L2VF_R3) →
        (w : L2VF_R3) = 𝔊.P n (w : L2VF_R3) →
        |F.b u v w|
          ≤ C_b * ‖(u : L2VF_R3)‖ ^ (1 / 2 : ℝ)
              * (viscousFormSq_R3 1 (u : L2VF_R3)) ^ (1 / 4 : ℝ)
              * Real.sqrt (viscousFormSq_R3 1 (v : L2VF_R3))
              * Real.sqrt (viscousFormSq_R3 1 (w : L2VF_R3)) := by
  classical
  obtain ⟨C_b, hC_b0, hC_b⟩ := convIntegralSchwartz_bound_energy
  refine ⟨C_b, hC_b0, ?_⟩
  intro n u v w hu hv hw
  -- Schwartz representatives of the level-`n` states, transported through the projection pin.
  obtain ⟨ψu, hψu⟩ := 𝔊.range_schwartz n (u : L2VF_R3)
  obtain ⟨ψv, hψv⟩ := 𝔊.range_schwartz n (v : L2VF_R3)
  obtain ⟨ψw, hψw⟩ := 𝔊.range_schwartz n (w : L2VF_R3)
  have hψu' : ∀ j : Fin 3,
      L2VF_projComponent_R3 j (u : L2VF_R3) = (ψu j).toLp 2 (volume : Measure Domain3) := by
    intro j; rw [hu]; exact hψu j
  have hψv' : ∀ j : Fin 3,
      L2VF_projComponent_R3 j (v : L2VF_R3) = (ψv j).toLp 2 (volume : Measure Domain3) := by
    intro j; rw [hv]; exact hψv j
  have hψw' : ∀ j : Fin 3,
      L2VF_projComponent_R3 j (w : L2VF_R3) = (ψw j).toLp 2 (volume : Measure Domain3) := by
    intro j; rw [hw]; exact hψw j
  -- The `F.b_galerkin` pin identifies `F.b` with `convIntegralSchwartz`, then C4 applies.
  rw [F.b_galerkin ψu ψv ψw u v w hψu' hψv' hψw']
  exact hC_b (u : L2VF_R3) (v : L2VF_R3) (w : L2VF_R3) ψu ψv ψw hψu' hψv' hψw'

/-! ### C6 helpers — bilinearity on differences, level-`n` closure, rpow continuity -/

/-- Additivity/homogeneity in the FIRST slot specialize to subtraction. -/
private theorem bForm_sub_1 (F : R3NSForms 𝔊) (u u' v w : L2Sigma_R3) :
    F.b (u - u') v w = F.b u v w - F.b u' v w := by
  rw [sub_eq_add_neg u u', ← neg_one_smul ℝ u', F.b_add_1, F.b_smul_1]; ring

/-- Additivity/homogeneity in the SECOND slot specialize to subtraction. -/
private theorem bForm_sub_2 (F : R3NSForms 𝔊) (u v v' w : L2Sigma_R3) :
    F.b u (v - v') w = F.b u v w - F.b u v' w := by
  rw [sub_eq_add_neg v v', ← neg_one_smul ℝ v', F.b_add_2, F.b_smul_2]; ring

/-- The diagonal increment of `b` splits into two one-sided differences. -/
private theorem bForm_diag_increment (F : R3NSForms 𝔊) (x y w : L2Sigma_R3) :
    F.b x x w - F.b y y w = F.b (x - y) x w + F.b y (x - y) w := by
  rw [bForm_sub_1 F x y x w, bForm_sub_2 F y x y w]; ring

/-- Level-`n` states are closed under subtraction: `𝔊.P n` is linear, so the difference of
two curve values stays fixed by `𝔊.P n`. -/
private theorem galerkinCurve_sub_inVn (gs : GalerkinSolutionData_R3 𝔊 F ν u₀ n) (σ σ' : ℝ) :
    ((gs.u σ - gs.u σ' : L2Sigma_R3) : L2VF_R3)
      = 𝔊.P n ((gs.u σ - gs.u σ' : L2Sigma_R3) : L2VF_R3) := by
  rw [Submodule.coe_sub, map_sub, ← gs.u_inVn σ, ← gs.u_inVn σ']

/-- If `f → 0` and `p > 0`, then `f ^ p → 0` (real rpow, base approaching `0` from nonneg). -/
private theorem tendsto_rpow_of_tendsto_zero {α : Type*} {l : Filter α} {f : α → ℝ}
    {p : ℝ} (hp : 0 < p) (hf : Filter.Tendsto f l (nhds 0)) :
    Filter.Tendsto (fun x => (f x) ^ p) l (nhds 0) := by
  have hc : ContinuousAt (fun x : ℝ => x ^ p) 0 :=
    Real.continuousAt_rpow_const 0 p (Or.inr hp.le)
  have hcomp := (hc.tendsto).comp hf
  simpa [Function.comp_def, Real.zero_rpow hp.ne'] using hcomp

/-! ### C6 — continuity of the `b`-integrand along the Galerkin curve -/

/-- **C6.** For a fixed level-`n` test `w`, the diagonal convection integrand along the
Galerkin curve, `σ ↦ F.b (gs.u σ) (gs.u σ) w`, is continuous on forward time `Ici 0`.

Route (plan §3 C6): multilinearity (`b_add_*`) splits the increment into two terms each
controlled by C5 with one slot `= gs.u σ − gs.u σ₀` (still level-`n`), and B6
(H¹-continuity of the Galerkin curve, `galerkin_curve_H1_continuousOn`) drives them to `0`.
Primary (strong) form stated per task; the plan's weaker `IntervalIntegrable` fallback
(`galerkin_bForm_intervalIntegrable`) remains available if the fractional-power ε–δ fights.
This is the interval-integrability input consumed by B9. -/
theorem galerkin_bForm_curve_continuousOn (gs : GalerkinSolutionData_R3 𝔊 F ν u₀ n)
    (w : L2Sigma_R3) (hw : (w : L2VF_R3) = 𝔊.P n (w : L2VF_R3)) :
    ContinuousOn (fun σ => F.b (gs.u σ) (gs.u σ) w) (Set.Ici 0) := by
  obtain ⟨C_b, _hC_b0, hC_b⟩ := bForm_galerkin_abs_le (𝔊 := 𝔊) (F := F)
  intro σ₀ hσ₀
  have hσ₀0 : 0 ≤ σ₀ := hσ₀
  -- coercion of the L2Sigma difference commutes with subtraction in L2VF
  have hcoe : ∀ σ : ℝ, ((gs.u σ - gs.u σ₀ : L2Sigma_R3) : L2VF_R3)
      = (gs.u σ : L2VF_R3) - (gs.u σ₀ : L2VF_R3) := by
    intro σ; rw [Submodule.coe_sub]
  -- B1: L²-continuity of the curve at σ₀
  have hcont_u : Filter.Tendsto (fun σ => (gs.u σ : L2VF_R3))
      (nhdsWithin σ₀ (Set.Ici 0)) (nhds (gs.u σ₀ : L2VF_R3)) :=
    (galerkinCurve_continuousOn gs) σ₀ hσ₀
  -- ‖u σ − u σ₀‖ → 0
  have hnorm_d : Filter.Tendsto
      (fun σ => ‖((gs.u σ - gs.u σ₀ : L2Sigma_R3) : L2VF_R3)‖)
      (nhdsWithin σ₀ (Set.Ici 0)) (nhds 0) := by
    have hsub : Filter.Tendsto (fun σ => (gs.u σ : L2VF_R3) - (gs.u σ₀ : L2VF_R3))
        (nhdsWithin σ₀ (Set.Ici 0)) (nhds 0) := by
      simpa using hcont_u.sub (tendsto_const_nhds (x := (gs.u σ₀ : L2VF_R3)))
    have hnorm0 : Filter.Tendsto (fun σ => ‖(gs.u σ : L2VF_R3) - (gs.u σ₀ : L2VF_R3)‖)
        (nhdsWithin σ₀ (Set.Ici 0)) (nhds 0) := by simpa using hsub.norm
    exact hnorm0.congr (fun σ => by rw [hcoe σ])
  -- B6: V₁(u σ − u σ₀) → 0
  have hVd : Filter.Tendsto
      (fun σ => viscousFormSq_R3 1 ((gs.u σ - gs.u σ₀ : L2Sigma_R3) : L2VF_R3))
      (nhdsWithin σ₀ (Set.Ici 0)) (nhds 0) := by
    exact (galerkin_curve_H1_continuousOn gs σ₀ hσ₀0).congr (fun σ => by rw [hcoe σ])
  -- B5: V₁(u σ) → V₁(u σ₀)
  have hVu : Filter.Tendsto (fun σ => viscousFormSq_R3 1 (gs.u σ : L2VF_R3))
      (nhdsWithin σ₀ (Set.Ici 0)) (nhds (viscousFormSq_R3 1 (gs.u σ₀ : L2VF_R3))) :=
    (galerkin_viscous_curve_continuousOn gs) σ₀ hσ₀
  -- fractional-power limits at 0
  have h1 : Filter.Tendsto
      (fun σ => ‖((gs.u σ - gs.u σ₀ : L2Sigma_R3) : L2VF_R3)‖ ^ (1 / 2 : ℝ))
      (nhdsWithin σ₀ (Set.Ici 0)) (nhds 0) :=
    tendsto_rpow_of_tendsto_zero (by norm_num) hnorm_d
  have h2 : Filter.Tendsto
      (fun σ => (viscousFormSq_R3 1 ((gs.u σ - gs.u σ₀ : L2Sigma_R3) : L2VF_R3)) ^ (1 / 4 : ℝ))
      (nhdsWithin σ₀ (Set.Ici 0)) (nhds 0) :=
    tendsto_rpow_of_tendsto_zero (by norm_num) hVd
  have h3 : Filter.Tendsto (fun σ => Real.sqrt (viscousFormSq_R3 1 (gs.u σ : L2VF_R3)))
      (nhdsWithin σ₀ (Set.Ici 0)) (nhds (Real.sqrt (viscousFormSq_R3 1 (gs.u σ₀ : L2VF_R3)))) :=
    hVu.sqrt
  have h4 : Filter.Tendsto
      (fun σ => Real.sqrt (viscousFormSq_R3 1 ((gs.u σ - gs.u σ₀ : L2Sigma_R3) : L2VF_R3)))
      (nhdsWithin σ₀ (Set.Ici 0)) (nhds 0) := by
    simpa [Real.sqrt_zero] using hVd.sqrt
  -- the two C5 bound terms each tend to 0
  have hterm1 : Filter.Tendsto (fun σ =>
      C_b * ‖((gs.u σ - gs.u σ₀ : L2Sigma_R3) : L2VF_R3)‖ ^ (1 / 2 : ℝ)
        * (viscousFormSq_R3 1 ((gs.u σ - gs.u σ₀ : L2Sigma_R3) : L2VF_R3)) ^ (1 / 4 : ℝ)
        * Real.sqrt (viscousFormSq_R3 1 (gs.u σ : L2VF_R3))
        * Real.sqrt (viscousFormSq_R3 1 (w : L2VF_R3)))
      (nhdsWithin σ₀ (Set.Ici 0)) (nhds 0) := by
    have hmul := ((((tendsto_const_nhds (x := C_b)).mul h1).mul h2).mul h3).mul
      (tendsto_const_nhds (x := Real.sqrt (viscousFormSq_R3 1 (w : L2VF_R3))))
    simpa using hmul
  have hterm2 : Filter.Tendsto (fun σ =>
      C_b * ‖(gs.u σ₀ : L2VF_R3)‖ ^ (1 / 2 : ℝ)
        * (viscousFormSq_R3 1 (gs.u σ₀ : L2VF_R3)) ^ (1 / 4 : ℝ)
        * Real.sqrt (viscousFormSq_R3 1 ((gs.u σ - gs.u σ₀ : L2Sigma_R3) : L2VF_R3))
        * Real.sqrt (viscousFormSq_R3 1 (w : L2VF_R3)))
      (nhdsWithin σ₀ (Set.Ici 0)) (nhds 0) := by
    have hmul := ((((tendsto_const_nhds (x := C_b)).mul
        (tendsto_const_nhds (x := ‖(gs.u σ₀ : L2VF_R3)‖ ^ (1 / 2 : ℝ)))).mul
        (tendsto_const_nhds (x := (viscousFormSq_R3 1 (gs.u σ₀ : L2VF_R3)) ^ (1 / 4 : ℝ)))).mul
        h4).mul
      (tendsto_const_nhds (x := Real.sqrt (viscousFormSq_R3 1 (w : L2VF_R3))))
    simpa using hmul
  -- the sum of the two bound terms tends to 0
  have hbtend := hterm1.add hterm2
  rw [add_zero] at hbtend
  -- squeeze the increment to 0, then reassemble
  have key : Filter.Tendsto
      (fun σ => F.b (gs.u σ) (gs.u σ) w - F.b (gs.u σ₀) (gs.u σ₀) w)
      (nhdsWithin σ₀ (Set.Ici 0)) (nhds 0) := by
    refine squeeze_zero_norm (fun σ => ?_) hbtend
    rw [Real.norm_eq_abs, bForm_diag_increment F (gs.u σ) (gs.u σ₀) w]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · exact hC_b n (gs.u σ - gs.u σ₀) (gs.u σ) w
        (galerkinCurve_sub_inVn gs σ σ₀) (gs.u_inVn σ) hw
    · exact hC_b n (gs.u σ₀) (gs.u σ - gs.u σ₀) w
        (gs.u_inVn σ₀) (galerkinCurve_sub_inVn gs σ σ₀) hw
  have h2 := key.add (tendsto_const_nhds (x := F.b (gs.u σ₀) (gs.u σ₀) w))
  rw [zero_add] at h2
  exact h2.congr (fun σ => by ring)

/-! ### B9 — pairing FTC (deferred here from PR-1) -/

/-- **B9 (Codex-gated statement; deferred from PR-1).** The weak-form pairing FTC along the
Galerkin curve: for a level-`n` test `w` (`(w:L2VF_R3) = 𝔊.P n w`) and `0 ≤ a ≤ b`,
`⟪u(b) − u(a), w⟫ = ∫ σ in a..b, (−ν · stokes(u σ, w) − b(u σ, u σ, w))`.

Route (plan §3 B9): scalar FTC on `g σ := ⟪u σ, w⟫` whose derivative is given by the ODE
field; interval-integrability of the RHS from continuity — the stokes term via
`viscous_curve_continuous` + `stokesTestPairing_eq_sum_inner_wFC`, and the `b` term via C6
(`galerkin_bForm_curve_continuousOn`).  Named `galerkin_pairing_FTC` per the plan's B9
note authorizing the move to File C. -/
theorem galerkin_pairing_FTC (gs : GalerkinSolutionData_R3 𝔊 F ν u₀ n)
    (w : L2Sigma_R3) (hw : (w : L2VF_R3) = 𝔊.P n (w : L2VF_R3))
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    inner (𝕜 := ℝ) ((gs.u b : L2VF_R3) - (gs.u a : L2VF_R3)) (w : L2VF_R3)
      = ∫ σ in a..b,
          (-ν * stokesTestPairing_R3 (gs.u σ : L2VF_R3) (w : L2VF_R3)
            - F.b (gs.u σ) (gs.u σ) w) := by
  -- the cell `[a,b]` lies in forward time
  have huIcc : Set.uIcc a b ⊆ Set.Ici (0 : ℝ) := by
    rw [Set.uIcc_of_le hab]; exact fun x hx => le_trans ha hx.1
  -- `w` is H¹ (a level-`n` state has Schwartz representatives)
  have hwmem : memH1VF_R3 (w : L2VF_R3) := galerkinCurve_reg_mem 𝔊 n (w : L2VF_R3) hw
  -- scalar FTC on `g σ = ⟪u σ, w⟫`; the derivative is the ODE right-hand side tested at `w`
  have hderiv : ∀ σ ∈ Set.uIcc a b,
      HasDerivAt (fun s => inner (𝕜 := ℝ) (gs.u s : L2VF_R3) (w : L2VF_R3))
        (-ν * stokesTestPairing_R3 (gs.u σ : L2VF_R3) (w : L2VF_R3)
          - F.b (gs.u σ) (gs.u σ) w) σ := by
    intro σ hσ
    have hσ0 : 0 ≤ σ := huIcc hσ
    have hbase : HasDerivAt (fun s => inner (𝕜 := ℝ) (gs.u s : L2VF_R3) (w : L2VF_R3))
        (inner (𝕜 := ℝ) (gs.u σ : L2VF_R3) (0 : L2VF_R3)
          + inner (𝕜 := ℝ) (deriv (fun s => (gs.u s : L2VF_R3)) σ) (w : L2VF_R3)) σ :=
      (gs.u_hasDeriv σ hσ0).inner ℝ (hasDerivAt_const σ (w : L2VF_R3))
    have hval : inner (𝕜 := ℝ) (gs.u σ : L2VF_R3) (0 : L2VF_R3)
        + inner (𝕜 := ℝ) (deriv (fun s => (gs.u s : L2VF_R3)) σ) (w : L2VF_R3)
        = -ν * stokesTestPairing_R3 (gs.u σ : L2VF_R3) (w : L2VF_R3)
          - F.b (gs.u σ) (gs.u σ) w := by
      rw [inner_zero_right, zero_add, neg_mul]
      have hode := gs.u_ode σ hσ0 w hw
      simp only [r3Domain_stokes, R3NSForms.core_b] at hode
      linarith [hode]
    rw [hval] at hbase
    exact hbase
  -- interval-integrability of the RHS via continuity (stokes term + `b` term)
  have hstokes_cont : ContinuousOn
      (fun σ => stokesTestPairing_R3 (gs.u σ : L2VF_R3) (w : L2VF_R3)) (Set.uIcc a b) := by
    have heq : ∀ σ, stokesTestPairing_R3 (gs.u σ : L2VF_R3) (w : L2VF_R3)
        = ∑ j : Fin 3, (inner (𝕜 := ℂ)
            (weightedFourierComponent (w : L2VF_R3) hwmem j)
            (weightedFourierComponent (gs.u σ : L2VF_R3) (gs.reg_mem σ) j)).re :=
      fun σ => stokesTestPairing_eq_sum_inner_wFC (gs.u σ : L2VF_R3) (w : L2VF_R3)
        (gs.reg_mem σ) hwmem
    refine ContinuousOn.congr ?_ (fun σ _ => heq σ)
    refine continuousOn_finsetSum _ (fun j _ => ?_)
    have hj : ContinuousOn
        (fun σ => weightedFourierComponent (gs.u σ : L2VF_R3) (gs.reg_mem σ) j)
        (Set.uIcc a b) := (gs.viscous_curve_continuous j).mono huIcc
    have hinner : ContinuousOn
        (fun σ => inner (𝕜 := ℂ)
          (weightedFourierComponent (w : L2VF_R3) hwmem j)
          (weightedFourierComponent (gs.u σ : L2VF_R3) (gs.reg_mem σ) j)) (Set.uIcc a b) :=
      continuousOn_const.inner hj
    exact Complex.continuous_re.comp_continuousOn hinner
  have hRHS_cont : ContinuousOn (fun σ =>
      -ν * stokesTestPairing_R3 (gs.u σ : L2VF_R3) (w : L2VF_R3) - F.b (gs.u σ) (gs.u σ) w)
      (Set.uIcc a b) := by
    have h1 : ContinuousOn
        (fun σ => -ν * stokesTestPairing_R3 (gs.u σ : L2VF_R3) (w : L2VF_R3)) (Set.uIcc a b) :=
      continuousOn_const.mul hstokes_cont
    have h2 : ContinuousOn (fun σ => F.b (gs.u σ) (gs.u σ) w) (Set.uIcc a b) :=
      (galerkin_bForm_curve_continuousOn gs w hw).mono huIcc
    exact h1.sub h2
  have hint : IntervalIntegrable
      (fun σ => -ν * stokesTestPairing_R3 (gs.u σ : L2VF_R3) (w : L2VF_R3)
        - F.b (gs.u σ) (gs.u σ) w) volume a b :=
    hRHS_cont.intervalIntegrable
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [inner_sub_left]
  exact hFTC.symm

end LerayHopf
