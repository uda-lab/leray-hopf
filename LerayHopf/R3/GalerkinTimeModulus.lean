/-
# LerayHopf.R3.GalerkinTimeModulus — Issue #46 PR-3 (File D)

**Goal:** The time-modulus / good-sampling layer of the Simon compactness route that
discharges the axiom `galerkin_spacetime_precompact_R3`
(plan: `docs/scratch/issue46-spacetime-precompact-plan.md`, §3 File D).  Given the
energy-class trilinear bound (File C, C5) and the Galerkin curve library (File B), this
file turns per-cell dual-norm control into the single **`n`-uniform, integrated**
sampling-error bound consumed by the assembly step (File E).

- `exists_goodSample` (D1): on a compact interval a continuous nonneg integrand has a
  point at or below its average (min ≤ average), giving the per-cell sample.
- `galerkin_cell_error_bound` (D2): on a single mesh cell `[a, a+δ]`, the cell
  `L²`-error integral is bounded by an energy part plus a pairing part, each expressed
  through cell integrals of `V`-powers, with the good-sample factor `√(2δ⁻¹ν⁻¹E₀)`.
- `galerkin_sampling_error_bound` (D3, MASTER): a constant `C_mod ≥ 0` — a function of
  `‖u₀‖, ν, T, C_b` ONLY, standing OUTSIDE every quantifier over the Galerkin level `n`
  and the mesh count `m` — such that, on the uniform mesh of size `m`, there exist sample
  times with the total (summed-over-cells) `L²`-error bounded by `C_mod · √δ`.

The load-bearing structural claim of D3 is that `C_mod` is `n`- and `m`-independent: the
existential `∃ C_mod` sits OUTSIDE both `∀ n` and `∀ m`, and D3 is an INTEGRATED (summed)
modulus — no pointwise-in-time strong modulus is ever asserted (plan §1 guardrail-4).  The
`n`-uniform C5 constant `C_b` and its bound are taken as EXPLICIT hypotheses precisely so
that this `n`-uniformity is structurally evident.

## Plan §3 File D mapping

- `exists_goodSample`               : D1 — min ≤ average on a compact interval (generic)
- `galerkin_cell_error_bound`       : D2 — per-cell `L²`-error bound (energy + pairing parts)
- `galerkin_sampling_error_bound`   : D3 — MASTER `n`-uniform integrated sampling-error bound

Notation (plan §3): `V₁ v := viscousFormSq_R3 1 v`, `V_ν v := viscousFormSq_R3 ν v`,
`E₀ := (1/2)·‖(u₀ : L2VF_R3)‖²`.  These are inlined here (no global `def`).

Dependency edges (plan): D1 → D3; B2, B5, B7, B8, B9, C5 → D2 → D3.

## Assumptions

No axioms are introduced by this file (`axiom` count: 0).  D1, D2, D3 are fully proved
(`sorry` count: 0) with their real intended statements; no statement is weakened, renamed,
or made vacuous.  The D3 master proof carries a raised `maxHeartbeats` budget (the
`Real.sqrt`/`rpow` bookkeeping over the mesh is elaboration-heavy; plan risk R6).
-/

import LerayHopf.R3.GalerkinTrilinearBound     -- C5 `bForm_galerkin_abs_le`, GalerkinSolutionData_R3, R3NSForms, viscousFormSq_R3
import LerayHopf.R3.GalerkinCurveBounds        -- B2/B5/B7/B8/B9 curve library (energy identity, pairing FTC, stokes CS)

namespace LerayHopf

open MeasureTheory

variable {𝔊 : R3GalerkinScheme} {F : R3NSForms 𝔊}

/-! ### D1 — good sample: min ≤ average on a compact interval (generic) -/

/-- **D1.** On a compact interval `[a, b]` (`a < b`), a continuous nonnegative integrand
has a point whose value is at or below its average: there is `τ ∈ [a, b]` with
`f τ ≤ (b − a)⁻¹ · ∫ₐᵇ f`.

Generic (no Galerkin context).  Route (plan §3 D1): min-value ≤ average, via
`IsCompact.exists_isMinOn` on `[a, b]` and monotonicity of the interval integral
(`intervalIntegral.integral_mono_on`) against the constant `f τ_min`. -/
theorem exists_goodSample {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Set.Icc a b))
    (hnn : ∀ σ ∈ Set.Icc a b, 0 ≤ f σ) :
    ∃ τ ∈ Set.Icc a b, f τ ≤ (b - a)⁻¹ * ∫ σ in a..b, f σ := by
  have hne : (Set.Icc a b).Nonempty := Set.nonempty_Icc.mpr hab.le
  obtain ⟨τ, hτ, hmin⟩ := isCompact_Icc.exists_isMinOn hne hf
  refine ⟨τ, hτ, ?_⟩
  have hmin' : ∀ x ∈ Set.Icc a b, f τ ≤ f x := isMinOn_iff.mp hmin
  have hfii : IntervalIntegrable f volume a b := hf.intervalIntegrable_of_Icc hab.le
  have hmono : ∫ _σ in a..b, f τ ≤ ∫ σ in a..b, f σ :=
    intervalIntegral.integral_mono_on hab.le intervalIntegrable_const hfii hmin'
  rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
  have hba : 0 < b - a := by linarith
  have hid : (b - a)⁻¹ * ((b - a) * f τ) = f τ := by
    rw [← mul_assoc, inv_mul_cancel₀ hba.ne', one_mul]
  calc f τ = (b - a)⁻¹ * ((b - a) * f τ) := hid.symm
    _ ≤ (b - a)⁻¹ * ∫ σ in a..b, f σ := mul_le_mul_of_nonneg_left hmono (by positivity)

/-! ### D2 helpers -/

/-- Local scaling helper (fresh copy, `GalerkinODE.lean:166` is downstream of the import
set here): the viscous dissipation scales linearly in `ν`. -/
private theorem viscousFormSq_R3_smul' (ν : ℝ) (u : L2VF_R3) :
    viscousFormSq_R3 ν u = ν * viscousFormSq_R3 1 u := by
  unfold viscousFormSq_R3; ring

/-- Continuity along the Galerkin curve of the stokes pairing against a FIXED H¹ test `w`.
Fresh mirror of the `hstokes_cont` step inside `galerkin_pairing_FTC`. -/
private theorem galerkin_stokes_curve_continuousOn {ν : ℝ} {u₀ : L2Sigma_R3} {n : ℕ}
    (gs : GalerkinSolutionData_R3 𝔊 F ν u₀ n) (w : L2VF_R3) (hw : memH1VF_R3 w) :
    ContinuousOn (fun σ => stokesTestPairing_R3 (gs.u σ : L2VF_R3) w) (Set.Ici 0) := by
  have heq : ∀ σ, stokesTestPairing_R3 (gs.u σ : L2VF_R3) w
      = ∑ j : Fin 3, (inner (𝕜 := ℂ)
          (weightedFourierComponent w hw j)
          (weightedFourierComponent (gs.u σ : L2VF_R3) (gs.reg_mem σ) j)).re :=
    fun σ => stokesTestPairing_eq_sum_inner_wFC (gs.u σ : L2VF_R3) w (gs.reg_mem σ) hw
  refine ContinuousOn.congr ?_ (fun σ _ => heq σ)
  refine continuousOn_finsetSum _ (fun j _ => ?_)
  exact Complex.continuous_re.comp_continuousOn
    (continuousOn_const.inner (gs.viscous_curve_continuous j))

/-- Generic bound: the interval integral of `R` over any subinterval `[x, y] ⊆ [a, b]` is
absolutely bounded by the integral of a nonnegative continuous dominating function `bd`
over the whole interval `[a, b]`, whenever `|R| ≤ bd` pointwise on `[a, b]`. -/
private theorem abs_intervalIntegral_le_of_le_abs {R bd : ℝ → ℝ} {a b x y : ℝ}
    (hab : a ≤ b) (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc a b)
    (hRc : ContinuousOn R (Set.Icc a b)) (hbdc : ContinuousOn bd (Set.Icc a b))
    (hle : ∀ σ ∈ Set.Icc a b, |R σ| ≤ bd σ) :
    |∫ σ in x..y, R σ| ≤ ∫ σ in a..b, bd σ := by
  have hbdnn : ∀ σ ∈ Set.Icc a b, 0 ≤ bd σ := fun σ hσ => (abs_nonneg _).trans (hle σ hσ)
  have hbd_ae : 0 ≤ᵐ[volume.restrict (Set.Ioc a b)] bd :=
    (ae_restrict_iff' measurableSet_Ioc).mpr
      (ae_of_all _ (fun σ hσ => hbdnn σ (Set.Ioc_subset_Icc_self hσ)))
  have hbd_ii : IntervalIntegrable bd volume a b := hbdc.intervalIntegrable_of_Icc hab
  rcases le_total x y with hxy | hyx
  · have hsub : Set.Icc x y ⊆ Set.Icc a b := Set.Icc_subset_Icc hx.1 hy.2
    calc |∫ σ in x..y, R σ|
        ≤ ∫ σ in x..y, |R σ| := intervalIntegral.abs_integral_le_integral_abs hxy
      _ ≤ ∫ σ in x..y, bd σ :=
          intervalIntegral.integral_mono_on hxy
            ((continuous_abs.comp_continuousOn (hRc.mono hsub)).intervalIntegrable_of_Icc hxy)
            ((hbdc.mono hsub).intervalIntegrable_of_Icc hxy) (fun σ hσ => hle σ (hsub hσ))
      _ ≤ ∫ σ in a..b, bd σ :=
          intervalIntegral.integral_mono_interval hx.1 hxy hy.2 hbd_ae hbd_ii
  · have hsub : Set.Icc y x ⊆ Set.Icc a b := Set.Icc_subset_Icc hy.1 hx.2
    rw [intervalIntegral.integral_symm y x, abs_neg]
    calc |∫ σ in y..x, R σ|
        ≤ ∫ σ in y..x, |R σ| := intervalIntegral.abs_integral_le_integral_abs hyx
      _ ≤ ∫ σ in y..x, bd σ :=
          intervalIntegral.integral_mono_on hyx
            ((continuous_abs.comp_continuousOn (hRc.mono hsub)).intervalIntegrable_of_Icc hyx)
            ((hbdc.mono hsub).intervalIntegrable_of_Icc hyx) (fun σ hσ => hle σ (hsub hσ))
      _ ≤ ∫ σ in a..b, bd σ :=
          intervalIntegral.integral_mono_interval hy.1 hyx hx.2 hbd_ae hbd_ii

/-! ### D2 — per-cell `L²`-error bound (energy part + pairing part) -/

/-- **D2.** Per-cell sampling error on the mesh cell `[a, a+δ]` (`0 < δ`, `0 ≤ a`) with a
good sample `τ ∈ [a, a+δ]` satisfying the good-sample Dirichlet bound
`V₁ (u τ) ≤ 2·δ⁻¹·ν⁻¹·E₀` (`E₀ = ½‖u₀‖²`).  The cell `L²`-error integral splits as

`‖u t − u τ‖² = (‖u t‖² − ‖u τ‖²) − 2⟪u t − u τ, u τ⟫`,

whose energy part is controlled by the integrated energy identity (B8) and whose pairing
part is controlled by the pairing FTC (B9) with the fixed test `w := u τ`, the stokes
Cauchy–Schwarz bound (B7), and the energy-class trilinear bound (C5).  Concretely:

`∫ t in a..(a+δ), ‖u t − u τ‖²
   ≤ 2·δ·(∫ σ in a..(a+δ), V_ν (u σ))
     + 2·δ·√(2·δ⁻¹·ν⁻¹·E₀) · ∫ σ in a..(a+δ),
         (ν·√(V₁ (u σ)) + C_b·‖u₀‖^{1/2}·(V₁ (u σ))^{3/4})`.

The C5 constant `C_b ≥ 0` and its bound `hC_b` are taken as EXPLICIT hypotheses (rather
than obtained internally from `bForm_galerkin_abs_le`) so that D2 — and the master bound
D3 built from it — stays visibly `n`-uniform: `C_b` cannot depend on the level `n`.

Consumes B2, B5, B7, B8, B9, C5. -/
theorem galerkin_cell_error_bound
    (ν : ℝ) (hν : 0 < ν) (u₀ : L2Sigma_R3) (n : ℕ)
    (gs : GalerkinSolutionData_R3 𝔊 F ν u₀ n)
    (C_b : ℝ) (hC_b0 : 0 ≤ C_b)
    (hC_b : ∀ (n : ℕ) (u v w : L2Sigma_R3),
        (u : L2VF_R3) = 𝔊.P n (u : L2VF_R3) →
        (v : L2VF_R3) = 𝔊.P n (v : L2VF_R3) →
        (w : L2VF_R3) = 𝔊.P n (w : L2VF_R3) →
        |F.b u v w|
          ≤ C_b * ‖(u : L2VF_R3)‖ ^ (1 / 2 : ℝ)
              * (viscousFormSq_R3 1 (u : L2VF_R3)) ^ (1 / 4 : ℝ)
              * Real.sqrt (viscousFormSq_R3 1 (v : L2VF_R3))
              * Real.sqrt (viscousFormSq_R3 1 (w : L2VF_R3)))
    (a δ : ℝ) (ha : 0 ≤ a) (hδ : 0 < δ)
    (τ : ℝ) (hτ : τ ∈ Set.Icc a (a + δ))
    (hτV : viscousFormSq_R3 1 (gs.u τ : L2VF_R3)
        ≤ 2 * δ⁻¹ * ν⁻¹ * ((1 / 2 : ℝ) * ‖(u₀ : L2VF_R3)‖ ^ 2)) :
    ∫ t in a..(a + δ), ‖(gs.u t : L2VF_R3) - (gs.u τ : L2VF_R3)‖ ^ 2
      ≤ 2 * δ * (∫ σ in a..(a + δ), viscousFormSq_R3 ν (gs.u σ : L2VF_R3))
        + 2 * δ * Real.sqrt (2 * δ⁻¹ * ν⁻¹ * ((1 / 2 : ℝ) * ‖(u₀ : L2VF_R3)‖ ^ 2))
            * ∫ σ in a..(a + δ),
                (ν * Real.sqrt (viscousFormSq_R3 1 (gs.u σ : L2VF_R3))
                  + C_b * ‖(u₀ : L2VF_R3)‖ ^ (1 / 2 : ℝ)
                      * (viscousFormSq_R3 1 (gs.u σ : L2VF_R3)) ^ (3 / 4 : ℝ)) := by
  -- cell geometry
  have haδ : a ≤ a + δ := by linarith
  have hcell : Set.Icc a (a + δ) ⊆ Set.Ici (0 : ℝ) := fun x hx => le_trans ha hx.1
  -- continuity of the L²-curve on the cell
  have hu_cont : ContinuousOn (fun s => (gs.u s : L2VF_R3)) (Set.Icc a (a + δ)) :=
    (galerkinCurve_continuousOn gs).mono hcell
  -- continuity of `V₁` on the cell
  have hV1_cont : ContinuousOn (fun σ => viscousFormSq_R3 1 (gs.u σ : L2VF_R3))
      (Set.Icc a (a + δ)) := (galerkin_viscous_curve_continuousOn gs).mono hcell
  -- `V_ν` = ν·V₁: continuity, nonnegativity, integrability on the cell
  have hVν_nn : ∀ σ, 0 ≤ viscousFormSq_R3 ν (gs.u σ : L2VF_R3) :=
    fun σ => viscousFormSq_R3_nonneg hν.le _
  have hVν_cont : ContinuousOn (fun σ => viscousFormSq_R3 ν (gs.u σ : L2VF_R3))
      (Set.Icc a (a + δ)) :=
    (continuousOn_const.mul hV1_cont).congr (fun σ _ => viscousFormSq_R3_smul' ν _)
  have hVν_ii : IntervalIntegrable (fun σ => viscousFormSq_R3 ν (gs.u σ : L2VF_R3))
      volume a (a + δ) := hVν_cont.intervalIntegrable_of_Icc haδ
  have hVν_ae : 0 ≤ᵐ[volume.restrict (Set.Ioc a (a + δ))]
      (fun σ => viscousFormSq_R3 ν (gs.u σ : L2VF_R3)) := ae_of_all _ (fun σ => hVν_nn σ)
  -- the good-sample energy identities relative to `a`
  have hE_τ := galerkinCurve_energy_identity gs a τ ha hτ.1
  have h0τ : 0 ≤ ∫ σ in a..τ, viscousFormSq_R3 ν (gs.u σ : L2VF_R3) :=
    intervalIntegral.integral_nonneg hτ.1 (fun σ _ => hVν_nn σ)
  have hτa : (∫ σ in a..τ, viscousFormSq_R3 ν (gs.u σ : L2VF_R3))
      ≤ ∫ σ in a..(a + δ), viscousFormSq_R3 ν (gs.u σ : L2VF_R3) :=
    intervalIntegral.integral_mono_interval (le_refl a) hτ.1 hτ.2 hVν_ae hVν_ii
  -- ENERGY PART: `|‖u t‖² − ‖u τ‖²| ≤ 2 ∫ V_ν`
  have hEbd : ∀ t ∈ Set.Icc a (a + δ),
      |‖(gs.u t : L2VF_R3)‖ ^ 2 - ‖(gs.u τ : L2VF_R3)‖ ^ 2|
        ≤ 2 * ∫ σ in a..(a + δ), viscousFormSq_R3 ν (gs.u σ : L2VF_R3) := by
    intro t ht
    have hE_t := galerkinCurve_energy_identity gs a t ha ht.1
    have h0t : 0 ≤ ∫ σ in a..t, viscousFormSq_R3 ν (gs.u σ : L2VF_R3) :=
      intervalIntegral.integral_nonneg ht.1 (fun σ _ => hVν_nn σ)
    have hta : (∫ σ in a..t, viscousFormSq_R3 ν (gs.u σ : L2VF_R3))
        ≤ ∫ σ in a..(a + δ), viscousFormSq_R3 ν (gs.u σ : L2VF_R3) :=
      intervalIntegral.integral_mono_interval (le_refl a) ht.1 ht.2 hVν_ae hVν_ii
    rw [abs_le]
    constructor <;> nlinarith [hE_t, hE_τ, h0t, hta, h0τ, hτa]
  -- PAIRING PART: identify `⟪u t − u τ, u τ⟫` with `∫_τ^t R` (both orders)
  have hR_cont : ContinuousOn
      (fun σ => -ν * stokesTestPairing_R3 (gs.u σ : L2VF_R3) (gs.u τ : L2VF_R3)
        - F.b (gs.u σ) (gs.u σ) (gs.u τ)) (Set.Icc a (a + δ)) := by
    have hst_c : ContinuousOn
        (fun σ => stokesTestPairing_R3 (gs.u σ : L2VF_R3) (gs.u τ : L2VF_R3))
        (Set.Icc a (a + δ)) :=
      (galerkin_stokes_curve_continuousOn gs (gs.u τ : L2VF_R3) (gs.reg_mem τ)).mono hcell
    have hb_c : ContinuousOn (fun σ => F.b (gs.u σ) (gs.u σ) (gs.u τ)) (Set.Icc a (a + δ)) :=
      (galerkin_bForm_curve_continuousOn gs (gs.u τ) (gs.u_inVn τ)).mono hcell
    exact (continuousOn_const.mul hst_c).sub hb_c
  have hbd_cont : ContinuousOn
      (fun σ => Real.sqrt (viscousFormSq_R3 1 (gs.u τ : L2VF_R3))
        * (ν * Real.sqrt (viscousFormSq_R3 1 (gs.u σ : L2VF_R3))
          + C_b * ‖(u₀ : L2VF_R3)‖ ^ (1 / 2 : ℝ)
              * (viscousFormSq_R3 1 (gs.u σ : L2VF_R3)) ^ (3 / 4 : ℝ)))
      (Set.Icc a (a + δ)) :=
    continuousOn_const.mul ((continuousOn_const.mul hV1_cont.sqrt).add
      (continuousOn_const.mul (hV1_cont.rpow_const (fun σ _ => Or.inr (by norm_num)))))
  -- pointwise domination `|R σ| ≤ bd σ`
  have hRle : ∀ σ ∈ Set.Icc a (a + δ),
      |(-ν * stokesTestPairing_R3 (gs.u σ : L2VF_R3) (gs.u τ : L2VF_R3)
          - F.b (gs.u σ) (gs.u σ) (gs.u τ))|
        ≤ Real.sqrt (viscousFormSq_R3 1 (gs.u τ : L2VF_R3))
            * (ν * Real.sqrt (viscousFormSq_R3 1 (gs.u σ : L2VF_R3))
              + C_b * ‖(u₀ : L2VF_R3)‖ ^ (1 / 2 : ℝ)
                  * (viscousFormSq_R3 1 (gs.u σ : L2VF_R3)) ^ (3 / 4 : ℝ)) := by
    intro σ hσ
    have hσ0 : (0 : ℝ) ≤ σ := hcell hσ
    have hV1σ_nn : 0 ≤ viscousFormSq_R3 1 (gs.u σ : L2VF_R3) := viscousFormSq_R3_nonneg zero_le_one _
    have hst := stokesTestPairing_abs_le (gs.u σ : L2VF_R3) (gs.u τ : L2VF_R3)
      (gs.reg_mem σ) (gs.reg_mem τ)
    have hb := hC_b n (gs.u σ) (gs.u σ) (gs.u τ) (gs.u_inVn σ) (gs.u_inVn σ) (gs.u_inVn τ)
    have hnorm : ‖(gs.u σ : L2VF_R3)‖ ^ (1 / 2 : ℝ) ≤ ‖(u₀ : L2VF_R3)‖ ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow (norm_nonneg _) (galerkinCurve_norm_le_u0 gs σ hσ0) (by norm_num)
    have hpow : (viscousFormSq_R3 1 (gs.u σ : L2VF_R3)) ^ (1 / 4 : ℝ)
        * Real.sqrt (viscousFormSq_R3 1 (gs.u σ : L2VF_R3))
        = (viscousFormSq_R3 1 (gs.u σ : L2VF_R3)) ^ (3 / 4 : ℝ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add' hV1σ_nn (by norm_num)]; norm_num
    have hp34_nn : 0 ≤ (viscousFormSq_R3 1 (gs.u σ : L2VF_R3)) ^ (3 / 4 : ℝ) :=
      Real.rpow_nonneg hV1σ_nn _
    have hs2_nn : 0 ≤ Real.sqrt (viscousFormSq_R3 1 (gs.u τ : L2VF_R3)) := Real.sqrt_nonneg _
    calc |(-ν * stokesTestPairing_R3 (gs.u σ : L2VF_R3) (gs.u τ : L2VF_R3)
            - F.b (gs.u σ) (gs.u σ) (gs.u τ))|
        = |ν * stokesTestPairing_R3 (gs.u σ : L2VF_R3) (gs.u τ : L2VF_R3)
            + F.b (gs.u σ) (gs.u σ) (gs.u τ)| := by
          rw [show (-ν * stokesTestPairing_R3 (gs.u σ : L2VF_R3) (gs.u τ : L2VF_R3)
                - F.b (gs.u σ) (gs.u σ) (gs.u τ))
              = -(ν * stokesTestPairing_R3 (gs.u σ : L2VF_R3) (gs.u τ : L2VF_R3)
                + F.b (gs.u σ) (gs.u σ) (gs.u τ)) from by ring, abs_neg]
      _ ≤ |ν * stokesTestPairing_R3 (gs.u σ : L2VF_R3) (gs.u τ : L2VF_R3)|
            + |F.b (gs.u σ) (gs.u σ) (gs.u τ)| := by
          simpa only [Real.norm_eq_abs] using norm_add_le
            (ν * stokesTestPairing_R3 (gs.u σ : L2VF_R3) (gs.u τ : L2VF_R3))
            (F.b (gs.u σ) (gs.u σ) (gs.u τ))
      _ = ν * |stokesTestPairing_R3 (gs.u σ : L2VF_R3) (gs.u τ : L2VF_R3)|
            + |F.b (gs.u σ) (gs.u σ) (gs.u τ)| := by rw [abs_mul, abs_of_pos hν]
      _ ≤ ν * (Real.sqrt (viscousFormSq_R3 1 (gs.u σ : L2VF_R3))
              * Real.sqrt (viscousFormSq_R3 1 (gs.u τ : L2VF_R3)))
            + C_b * ‖(u₀ : L2VF_R3)‖ ^ (1 / 2 : ℝ)
                * (viscousFormSq_R3 1 (gs.u σ : L2VF_R3)) ^ (3 / 4 : ℝ)
                * Real.sqrt (viscousFormSq_R3 1 (gs.u τ : L2VF_R3)) := by
          refine add_le_add (mul_le_mul_of_nonneg_left hst hν.le) ?_
          calc |F.b (gs.u σ) (gs.u σ) (gs.u τ)|
              ≤ C_b * ‖(gs.u σ : L2VF_R3)‖ ^ (1 / 2 : ℝ)
                  * (viscousFormSq_R3 1 (gs.u σ : L2VF_R3)) ^ (1 / 4 : ℝ)
                  * Real.sqrt (viscousFormSq_R3 1 (gs.u σ : L2VF_R3))
                  * Real.sqrt (viscousFormSq_R3 1 (gs.u τ : L2VF_R3)) := hb
            _ = C_b * ‖(gs.u σ : L2VF_R3)‖ ^ (1 / 2 : ℝ)
                  * (viscousFormSq_R3 1 (gs.u σ : L2VF_R3)) ^ (3 / 4 : ℝ)
                  * Real.sqrt (viscousFormSq_R3 1 (gs.u τ : L2VF_R3)) := by
                rw [← hpow]; ring
            _ ≤ C_b * ‖(u₀ : L2VF_R3)‖ ^ (1 / 2 : ℝ)
                  * (viscousFormSq_R3 1 (gs.u σ : L2VF_R3)) ^ (3 / 4 : ℝ)
                  * Real.sqrt (viscousFormSq_R3 1 (gs.u τ : L2VF_R3)) := by
                have h1 : C_b * ‖(gs.u σ : L2VF_R3)‖ ^ (1 / 2 : ℝ)
                    ≤ C_b * ‖(u₀ : L2VF_R3)‖ ^ (1 / 2 : ℝ) :=
                  mul_le_mul_of_nonneg_left hnorm hC_b0
                calc C_b * ‖(gs.u σ : L2VF_R3)‖ ^ (1 / 2 : ℝ)
                      * (viscousFormSq_R3 1 (gs.u σ : L2VF_R3)) ^ (3 / 4 : ℝ)
                      * Real.sqrt (viscousFormSq_R3 1 (gs.u τ : L2VF_R3))
                    = (C_b * ‖(gs.u σ : L2VF_R3)‖ ^ (1 / 2 : ℝ))
                      * ((viscousFormSq_R3 1 (gs.u σ : L2VF_R3)) ^ (3 / 4 : ℝ)
                        * Real.sqrt (viscousFormSq_R3 1 (gs.u τ : L2VF_R3))) := by ring
                  _ ≤ (C_b * ‖(u₀ : L2VF_R3)‖ ^ (1 / 2 : ℝ))
                      * ((viscousFormSq_R3 1 (gs.u σ : L2VF_R3)) ^ (3 / 4 : ℝ)
                        * Real.sqrt (viscousFormSq_R3 1 (gs.u τ : L2VF_R3))) :=
                    mul_le_mul_of_nonneg_right h1 (mul_nonneg hp34_nn hs2_nn)
                  _ = C_b * ‖(u₀ : L2VF_R3)‖ ^ (1 / 2 : ℝ)
                      * (viscousFormSq_R3 1 (gs.u σ : L2VF_R3)) ^ (3 / 4 : ℝ)
                      * Real.sqrt (viscousFormSq_R3 1 (gs.u τ : L2VF_R3)) := by ring
      _ = Real.sqrt (viscousFormSq_R3 1 (gs.u τ : L2VF_R3))
            * (ν * Real.sqrt (viscousFormSq_R3 1 (gs.u σ : L2VF_R3))
              + C_b * ‖(u₀ : L2VF_R3)‖ ^ (1 / 2 : ℝ)
                  * (viscousFormSq_R3 1 (gs.u σ : L2VF_R3)) ^ (3 / 4 : ℝ)) := by ring
  -- identify the pairing with an interval integral of `R`, bound it by `∫ bd`
  have hpair_eq : ∀ t ∈ Set.Icc a (a + δ),
      inner (𝕜 := ℝ) ((gs.u t : L2VF_R3) - (gs.u τ : L2VF_R3)) (gs.u τ : L2VF_R3)
        = ∫ σ in τ..t, (-ν * stokesTestPairing_R3 (gs.u σ : L2VF_R3) (gs.u τ : L2VF_R3)
            - F.b (gs.u σ) (gs.u σ) (gs.u τ)) := by
    intro t ht
    have ht0 : (0 : ℝ) ≤ t := hcell ht
    have hτ0 : (0 : ℝ) ≤ τ := hcell hτ
    rcases le_total τ t with h | h
    · exact galerkin_pairing_FTC gs (gs.u τ) (gs.u_inVn τ) τ t hτ0 h
    · have h9 := galerkin_pairing_FTC gs (gs.u τ) (gs.u_inVn τ) t τ ht0 h
      rw [show ((gs.u t : L2VF_R3) - (gs.u τ : L2VF_R3))
            = -((gs.u τ : L2VF_R3) - (gs.u t : L2VF_R3)) from (neg_sub _ _).symm,
        inner_neg_left, h9, intervalIntegral.integral_symm t τ]
  have hpair_bd : ∀ t ∈ Set.Icc a (a + δ),
      |inner (𝕜 := ℝ) ((gs.u t : L2VF_R3) - (gs.u τ : L2VF_R3)) (gs.u τ : L2VF_R3)|
        ≤ ∫ σ in a..(a + δ),
            Real.sqrt (viscousFormSq_R3 1 (gs.u τ : L2VF_R3))
              * (ν * Real.sqrt (viscousFormSq_R3 1 (gs.u σ : L2VF_R3))
                + C_b * ‖(u₀ : L2VF_R3)‖ ^ (1 / 2 : ℝ)
                    * (viscousFormSq_R3 1 (gs.u σ : L2VF_R3)) ^ (3 / 4 : ℝ)) := by
    intro t ht
    rw [hpair_eq t ht]
    exact abs_intervalIntegral_le_of_le_abs haδ hτ ht hR_cont hbd_cont hRle
  -- POINTWISE bound on the L²-error integrand by a constant
  have hgle : ∀ t ∈ Set.Icc a (a + δ),
      ‖(gs.u t : L2VF_R3) - (gs.u τ : L2VF_R3)‖ ^ 2
        ≤ 2 * (∫ σ in a..(a + δ), viscousFormSq_R3 ν (gs.u σ : L2VF_R3))
          + 2 * ∫ σ in a..(a + δ),
              Real.sqrt (viscousFormSq_R3 1 (gs.u τ : L2VF_R3))
                * (ν * Real.sqrt (viscousFormSq_R3 1 (gs.u σ : L2VF_R3))
                  + C_b * ‖(u₀ : L2VF_R3)‖ ^ (1 / 2 : ℝ)
                      * (viscousFormSq_R3 1 (gs.u σ : L2VF_R3)) ^ (3 / 4 : ℝ)) := by
    intro t ht
    have hpol : ‖(gs.u t : L2VF_R3) - (gs.u τ : L2VF_R3)‖ ^ 2
        = ‖(gs.u t : L2VF_R3)‖ ^ 2 - ‖(gs.u τ : L2VF_R3)‖ ^ 2
          - 2 * inner (𝕜 := ℝ) ((gs.u t : L2VF_R3) - (gs.u τ : L2VF_R3)) (gs.u τ : L2VF_R3) := by
      have h1 := norm_sub_sq_real (gs.u t : L2VF_R3) (gs.u τ : L2VF_R3)
      have h2 : inner (𝕜 := ℝ) ((gs.u t : L2VF_R3) - (gs.u τ : L2VF_R3)) (gs.u τ : L2VF_R3)
          = inner (𝕜 := ℝ) (gs.u t : L2VF_R3) (gs.u τ : L2VF_R3)
            - ‖(gs.u τ : L2VF_R3)‖ ^ 2 := by
        rw [inner_sub_left, real_inner_self_eq_norm_sq]
      rw [h1, h2]; ring
    rw [hpol]
    have hE := (le_abs_self _).trans (hEbd t ht)
    have hP := hpair_bd t ht
    have hPneg := neg_abs_le
      (inner (𝕜 := ℝ) ((gs.u t : L2VF_R3) - (gs.u τ : L2VF_R3)) (gs.u τ : L2VF_R3))
    linarith [hE, hP, hPneg]
  -- integrate the pointwise bound and rescale the pairing factor
  have hg_cont : ContinuousOn (fun t => ‖(gs.u t : L2VF_R3) - (gs.u τ : L2VF_R3)‖ ^ 2)
      (Set.Icc a (a + δ)) := (hu_cont.sub continuousOn_const).norm.pow 2
  have hconst_ii : IntervalIntegrable (fun _ : ℝ =>
      2 * (∫ σ in a..(a + δ), viscousFormSq_R3 ν (gs.u σ : L2VF_R3))
        + 2 * ∫ σ in a..(a + δ),
            Real.sqrt (viscousFormSq_R3 1 (gs.u τ : L2VF_R3))
              * (ν * Real.sqrt (viscousFormSq_R3 1 (gs.u σ : L2VF_R3))
                + C_b * ‖(u₀ : L2VF_R3)‖ ^ (1 / 2 : ℝ)
                    * (viscousFormSq_R3 1 (gs.u σ : L2VF_R3)) ^ (3 / 4 : ℝ)))
      volume a (a + δ) := intervalIntegrable_const
  have hstep1 := intervalIntegral.integral_mono_on haδ
    (hg_cont.intervalIntegrable_of_Icc haδ) hconst_ii hgle
  rw [intervalIntegral.integral_const, smul_eq_mul, add_sub_cancel_left] at hstep1
  have hexp : δ * (2 * (∫ σ in a..(a + δ), viscousFormSq_R3 ν (gs.u σ : L2VF_R3))
        + 2 * ∫ σ in a..(a + δ),
            Real.sqrt (viscousFormSq_R3 1 (gs.u τ : L2VF_R3))
              * (ν * Real.sqrt (viscousFormSq_R3 1 (gs.u σ : L2VF_R3))
                + C_b * ‖(u₀ : L2VF_R3)‖ ^ (1 / 2 : ℝ)
                    * (viscousFormSq_R3 1 (gs.u σ : L2VF_R3)) ^ (3 / 4 : ℝ)))
      = 2 * δ * (∫ σ in a..(a + δ), viscousFormSq_R3 ν (gs.u σ : L2VF_R3))
        + 2 * δ * ∫ σ in a..(a + δ),
            Real.sqrt (viscousFormSq_R3 1 (gs.u τ : L2VF_R3))
              * (ν * Real.sqrt (viscousFormSq_R3 1 (gs.u σ : L2VF_R3))
                + C_b * ‖(u₀ : L2VF_R3)‖ ^ (1 / 2 : ℝ)
                    * (viscousFormSq_R3 1 (gs.u σ : L2VF_R3)) ^ (3 / 4 : ℝ)) := by ring
  rw [hexp] at hstep1
  -- the pairing integral factors through the constant `√(V₁ (u τ))`
  have hbdJ : (∫ σ in a..(a + δ),
        Real.sqrt (viscousFormSq_R3 1 (gs.u τ : L2VF_R3))
          * (ν * Real.sqrt (viscousFormSq_R3 1 (gs.u σ : L2VF_R3))
            + C_b * ‖(u₀ : L2VF_R3)‖ ^ (1 / 2 : ℝ)
                * (viscousFormSq_R3 1 (gs.u σ : L2VF_R3)) ^ (3 / 4 : ℝ)))
      = Real.sqrt (viscousFormSq_R3 1 (gs.u τ : L2VF_R3))
        * ∫ σ in a..(a + δ), (ν * Real.sqrt (viscousFormSq_R3 1 (gs.u σ : L2VF_R3))
            + C_b * ‖(u₀ : L2VF_R3)‖ ^ (1 / 2 : ℝ)
                * (viscousFormSq_R3 1 (gs.u σ : L2VF_R3)) ^ (3 / 4 : ℝ)) :=
    intervalIntegral.integral_const_mul _ _
  have hJ_nn : 0 ≤ ∫ σ in a..(a + δ), (ν * Real.sqrt (viscousFormSq_R3 1 (gs.u σ : L2VF_R3))
        + C_b * ‖(u₀ : L2VF_R3)‖ ^ (1 / 2 : ℝ)
            * (viscousFormSq_R3 1 (gs.u σ : L2VF_R3)) ^ (3 / 4 : ℝ)) := by
    refine intervalIntegral.integral_nonneg haδ (fun σ _ => ?_)
    have hV1σ_nn : 0 ≤ viscousFormSq_R3 1 (gs.u σ : L2VF_R3) := viscousFormSq_R3_nonneg zero_le_one _
    exact add_nonneg (mul_nonneg hν.le (Real.sqrt_nonneg _))
      (mul_nonneg (mul_nonneg hC_b0 (Real.rpow_nonneg (norm_nonneg _) _))
        (Real.rpow_nonneg hV1σ_nn _))
  have hsqle : Real.sqrt (viscousFormSq_R3 1 (gs.u τ : L2VF_R3))
      ≤ Real.sqrt (2 * δ⁻¹ * ν⁻¹ * ((1 / 2 : ℝ) * ‖(u₀ : L2VF_R3)‖ ^ 2)) :=
    Real.sqrt_le_sqrt hτV
  have hfin2 : 2 * δ * (∫ σ in a..(a + δ),
        Real.sqrt (viscousFormSq_R3 1 (gs.u τ : L2VF_R3))
          * (ν * Real.sqrt (viscousFormSq_R3 1 (gs.u σ : L2VF_R3))
            + C_b * ‖(u₀ : L2VF_R3)‖ ^ (1 / 2 : ℝ)
                * (viscousFormSq_R3 1 (gs.u σ : L2VF_R3)) ^ (3 / 4 : ℝ)))
      ≤ 2 * δ * Real.sqrt (2 * δ⁻¹ * ν⁻¹ * ((1 / 2 : ℝ) * ‖(u₀ : L2VF_R3)‖ ^ 2))
          * ∫ σ in a..(a + δ), (ν * Real.sqrt (viscousFormSq_R3 1 (gs.u σ : L2VF_R3))
              + C_b * ‖(u₀ : L2VF_R3)‖ ^ (1 / 2 : ℝ)
                  * (viscousFormSq_R3 1 (gs.u σ : L2VF_R3)) ^ (3 / 4 : ℝ)) := by
    rw [hbdJ]
    have h2δ : 0 ≤ 2 * δ := by linarith
    calc 2 * δ * (Real.sqrt (viscousFormSq_R3 1 (gs.u τ : L2VF_R3))
            * ∫ σ in a..(a + δ), (ν * Real.sqrt (viscousFormSq_R3 1 (gs.u σ : L2VF_R3))
                + C_b * ‖(u₀ : L2VF_R3)‖ ^ (1 / 2 : ℝ)
                    * (viscousFormSq_R3 1 (gs.u σ : L2VF_R3)) ^ (3 / 4 : ℝ)))
        = (2 * δ * Real.sqrt (viscousFormSq_R3 1 (gs.u τ : L2VF_R3)))
          * ∫ σ in a..(a + δ), (ν * Real.sqrt (viscousFormSq_R3 1 (gs.u σ : L2VF_R3))
              + C_b * ‖(u₀ : L2VF_R3)‖ ^ (1 / 2 : ℝ)
                  * (viscousFormSq_R3 1 (gs.u σ : L2VF_R3)) ^ (3 / 4 : ℝ)) := by ring
      _ ≤ (2 * δ * Real.sqrt (2 * δ⁻¹ * ν⁻¹ * ((1 / 2 : ℝ) * ‖(u₀ : L2VF_R3)‖ ^ 2)))
          * ∫ σ in a..(a + δ), (ν * Real.sqrt (viscousFormSq_R3 1 (gs.u σ : L2VF_R3))
              + C_b * ‖(u₀ : L2VF_R3)‖ ^ (1 / 2 : ℝ)
                  * (viscousFormSq_R3 1 (gs.u σ : L2VF_R3)) ^ (3 / 4 : ℝ)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsqle h2δ) hJ_nn
      _ = 2 * δ * Real.sqrt (2 * δ⁻¹ * ν⁻¹ * ((1 / 2 : ℝ) * ‖(u₀ : L2VF_R3)‖ ^ 2))
          * ∫ σ in a..(a + δ), (ν * Real.sqrt (viscousFormSq_R3 1 (gs.u σ : L2VF_R3))
              + C_b * ‖(u₀ : L2VF_R3)‖ ^ (1 / 2 : ℝ)
                  * (viscousFormSq_R3 1 (gs.u σ : L2VF_R3)) ^ (3 / 4 : ℝ)) := by ring
  linarith [hstep1, hfin2]

/-! ### D3 helper — a time-Hölder bound against the constant `1` -/

/-- **Time-Hölder helper.** For a continuous nonnegative integrand `h` on `[0, T]`
(`0 < T`) and an exponent `0 < r < 1`, the integral of `hʳ` is controlled by a power of the
length times a power of the integral:
`∫₀ᵀ hʳ ≤ T^(1-r) · (∫₀ᵀ h)ʳ`.

This is Hölder's inequality against the constant `1` with conjugate exponents
`p = (1-r)⁻¹`, `q = r⁻¹` (so `1/p = 1-r`, `1/q = r`).  Specialized at `r = 1/2` it gives the
`√`-Cauchy–Schwarz bound, and at `r = 3/4` the `^{3/4}`-Hölder bound consumed by D3. -/
private theorem intervalIntegral_rpow_le_of_nonneg {h : ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (hhc : ContinuousOn h (Set.Icc 0 T)) (hhnn : ∀ σ ∈ Set.Icc 0 T, 0 ≤ h σ)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    ∫ σ in (0:ℝ)..T, (h σ) ^ r ≤ T ^ (1 - r) * (∫ σ in (0:ℝ)..T, h σ) ^ r := by
  have hr0' : r ≠ 0 := ne_of_gt hr0
  have h1r : (0 : ℝ) < 1 - r := by linarith
  have hhc' : ContinuousOn h (Set.Ioc (0:ℝ) T) := hhc.mono Set.Ioc_subset_Icc_self
  -- Hölder conjugate exponents
  have hpq : ((1 - r)⁻¹).HolderConjugate r⁻¹ := by
    have := Real.HolderConjugate.inv_one_sub_inv (a := 1 - r) h1r (by linarith)
    simpa using this
  -- maximum of `h` on the compact cell gives an `Lᵍ` bound for `hʳ`
  obtain ⟨xM, hxM, hmax⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr hT.le) hhc
  have hmax' : ∀ x ∈ Set.Icc (0:ℝ) T, h x ≤ h xM := isMaxOn_iff.mp hmax
  -- measurability and `MemLp` inputs
  have hmeas : AEStronglyMeasurable (fun σ => (h σ) ^ r)
      (volume.restrict (Set.Ioc (0:ℝ) T)) :=
    (hhc'.rpow_const (fun σ _ => Or.inr hr0.le)).aestronglyMeasurable measurableSet_Ioc
  have hFmem : MemLp (fun _ : ℝ => (1:ℝ)) (ENNReal.ofReal (1 - r)⁻¹)
      (volume.restrict (Set.Ioc (0:ℝ) T)) := memLp_const 1
  have hGmem : MemLp (fun σ => (h σ) ^ r) (ENNReal.ofReal r⁻¹)
      (volume.restrict (Set.Ioc (0:ℝ) T)) := by
    refine MemLp.of_bound hmeas ((h xM) ^ r) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with σ hσ
    have hσ' : σ ∈ Set.Icc (0:ℝ) T := Set.Ioc_subset_Icc_self hσ
    have hhσ : 0 ≤ h σ := hhnn σ hσ'
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hhσ r)]
    exact Real.rpow_le_rpow hhσ (hmax' σ hσ') hr0.le
  have hf_nn : 0 ≤ᵐ[volume.restrict (Set.Ioc (0:ℝ) T)] (fun _ : ℝ => (1:ℝ)) :=
    ae_of_all _ (fun _ => zero_le_one)
  have hg_nn : 0 ≤ᵐ[volume.restrict (Set.Ioc (0:ℝ) T)] (fun σ => (h σ) ^ r) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with σ hσ
    exact Real.rpow_nonneg (hhnn σ (Set.Ioc_subset_Icc_self hσ)) r
  have key := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := volume.restrict (Set.Ioc (0:ℝ) T)) hpq hf_nn hg_nn hFmem hGmem
  simp only [one_mul, Real.one_rpow] at key
  -- convert the three integrals back to interval integrals and simplify exponents
  have hLHS : (∫ σ, (h σ) ^ r ∂(volume.restrict (Set.Ioc (0:ℝ) T)))
      = ∫ σ in (0:ℝ)..T, (h σ) ^ r := (intervalIntegral.integral_of_le hT.le).symm
  have e1 : (∫ _σ : ℝ, (1:ℝ) ∂(volume.restrict (Set.Ioc (0:ℝ) T))) = T := by
    rw [integral_const, smul_eq_mul, mul_one, measureReal_restrict_apply_univ,
      Real.volume_real_Ioc_of_le hT.le]; ring
  have e2 : (∫ σ, ((h σ) ^ r) ^ r⁻¹ ∂(volume.restrict (Set.Ioc (0:ℝ) T)))
      = ∫ σ in (0:ℝ)..T, h σ := by
    have hpt : (fun σ => ((h σ) ^ r) ^ r⁻¹)
        =ᵐ[volume.restrict (Set.Ioc (0:ℝ) T)] (fun σ => h σ) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with σ hσ
      have hhσ : 0 ≤ h σ := hhnn σ (Set.Ioc_subset_Icc_self hσ)
      rw [← Real.rpow_mul hhσ, mul_inv_cancel₀ hr0', Real.rpow_one]
    rw [integral_congr_ae hpt]
    exact (intervalIntegral.integral_of_le hT.le).symm
  rw [hLHS, e1, e2, show (1:ℝ) / (1 - r)⁻¹ = 1 - r from by rw [one_div, inv_inv],
    show (1:ℝ) / r⁻¹ = r from by rw [one_div, inv_inv]] at key
  exact key

/-! ### D3 — MASTER `n`-uniform integrated sampling-error bound -/

set_option maxHeartbeats 1600000 in
/-- **D3 (MASTER).** The `n`-uniform integrated sampling-error
bound.  There is a constant `C_mod ≥ 0` — a function of `‖u₀‖, ν, T, C_b` ONLY, standing
OUTSIDE every quantifier over the Galerkin level `n`, the Galerkin data `gs`, and the mesh
count `m` — such that for every level `n`, every Galerkin solution `gs` at that level, and
every mesh count `m > 0`, with `δ := T/m`, there exist sample times `τ : Fin m → ℝ` with

* `τ i ∈ [i·δ, (i+1)·δ]` (each sample lives in its cell),
* `V₁ (u (τ i)) ≤ 2·δ⁻¹·ν⁻¹·E₀` (the good-sample Dirichlet bound, `E₀ = ½‖u₀‖²`), and
* `∑ i, ∫ t in (i·δ)..((i+1)·δ), ‖u t − u (τ i)‖² ≤ C_mod · √δ`.

The conclusion is an INTEGRATED (summed-over-cells) modulus — no pointwise-in-time strong
modulus is asserted (plan §1 guardrail-4).  The critical structural claims are that the
existential `∃ C_mod` sits OUTSIDE `∀ n`, `∀ gs`, and `∀ m` (so `C_mod` is `n`- and
`m`-independent), and that the mesh is the FIXED uniform mesh of size `m`.  The C5 constant
`C_b ≥ 0` and its bound `hC_b` are taken as EXPLICIT hypotheses so that this `n`-uniformity
is structurally evident (`C_mod` is built from `C_b`, `‖u₀‖`, `ν`, `T` alone).

Route (plan §3 D3): D1 per cell (choice per `(n,i)` is classical), D2 per cell, sum with
`intervalIntegral.sum_integral_adjacent_intervals`, then time-Hölder
(`∫₀ᵀ √V₁ ≤ √T·√(∫V₁)`, `∫₀ᵀ V₁^{3/4} ≤ T^{1/4}·(∫V₁)^{3/4}`) with `reg_bound`. -/
theorem galerkin_sampling_error_bound
    (ν T : ℝ) (hν : 0 < ν) (hT : 0 < T) (u₀ : L2Sigma_R3)
    (C_b : ℝ) (hC_b0 : 0 ≤ C_b)
    (hC_b : ∀ (n : ℕ) (u v w : L2Sigma_R3),
        (u : L2VF_R3) = 𝔊.P n (u : L2VF_R3) →
        (v : L2VF_R3) = 𝔊.P n (v : L2VF_R3) →
        (w : L2VF_R3) = 𝔊.P n (w : L2VF_R3) →
        |F.b u v w|
          ≤ C_b * ‖(u : L2VF_R3)‖ ^ (1 / 2 : ℝ)
              * (viscousFormSq_R3 1 (u : L2VF_R3)) ^ (1 / 4 : ℝ)
              * Real.sqrt (viscousFormSq_R3 1 (v : L2VF_R3))
              * Real.sqrt (viscousFormSq_R3 1 (w : L2VF_R3))) :
    ∃ C_mod : ℝ, 0 ≤ C_mod ∧
      ∀ (n : ℕ) (gs : GalerkinSolutionData_R3 𝔊 F ν u₀ n) (m : ℕ), 0 < m →
        ∃ τ : Fin m → ℝ,
          (∀ i : Fin m,
            τ i ∈ Set.Icc ((i : ℕ) * (T / (m : ℝ))) (((i : ℕ) + 1) * (T / (m : ℝ)))) ∧
          (∀ i : Fin m,
            viscousFormSq_R3 1 (gs.u (τ i) : L2VF_R3)
              ≤ 2 * (T / (m : ℝ))⁻¹ * ν⁻¹ * ((1 / 2 : ℝ) * ‖(u₀ : L2VF_R3)‖ ^ 2)) ∧
          ∑ i : Fin m,
              ∫ t in ((i : ℕ) * (T / (m : ℝ)))..(((i : ℕ) + 1) * (T / (m : ℝ))),
                ‖(gs.u t : L2VF_R3) - (gs.u (τ i) : L2VF_R3)‖ ^ 2
            ≤ C_mod * Real.sqrt (T / (m : ℝ)) := by
  -- the master constant, built from `‖u₀‖, ν, T, C_b` alone
  have hE0nn : 0 ≤ (1 / 2 : ℝ) * ‖(u₀ : L2VF_R3)‖ ^ 2 := by positivity
  have hAnn0 : 0 ≤ ν⁻¹ * ((1 / 2 : ℝ) * ‖(u₀ : L2VF_R3)‖ ^ 2) :=
    mul_nonneg (inv_nonneg.mpr hν.le) hE0nn
  have hCmod_nn : 0 ≤ Real.sqrt T * ‖(u₀ : L2VF_R3)‖ ^ 2
      + 2 * Real.sqrt 2 * Real.sqrt (ν⁻¹ * ((1 / 2 : ℝ) * ‖(u₀ : L2VF_R3)‖ ^ 2))
        * (ν * T ^ (1 / 2 : ℝ) * (ν⁻¹ * ((1 / 2 : ℝ) * ‖(u₀ : L2VF_R3)‖ ^ 2)) ^ (1 / 2 : ℝ)
          + C_b * ‖(u₀ : L2VF_R3)‖ ^ (1 / 2 : ℝ) * T ^ (1 / 4 : ℝ)
              * (ν⁻¹ * ((1 / 2 : ℝ) * ‖(u₀ : L2VF_R3)‖ ^ 2)) ^ (3 / 4 : ℝ)) := by
    have hJ0 : 0 ≤ ν * T ^ (1 / 2 : ℝ) * (ν⁻¹ * ((1 / 2 : ℝ) * ‖(u₀ : L2VF_R3)‖ ^ 2)) ^ (1 / 2 : ℝ)
        + C_b * ‖(u₀ : L2VF_R3)‖ ^ (1 / 2 : ℝ) * T ^ (1 / 4 : ℝ)
            * (ν⁻¹ * ((1 / 2 : ℝ) * ‖(u₀ : L2VF_R3)‖ ^ 2)) ^ (3 / 4 : ℝ) := by
      refine add_nonneg (mul_nonneg (mul_nonneg hν.le (Real.rpow_nonneg hT.le _))
        (Real.rpow_nonneg hAnn0 _)) ?_
      exact mul_nonneg (mul_nonneg (mul_nonneg hC_b0 (Real.rpow_nonneg (norm_nonneg _) _))
        (Real.rpow_nonneg hT.le _)) (Real.rpow_nonneg hAnn0 _)
    refine add_nonneg (by positivity) ?_
    exact mul_nonneg (mul_nonneg (by positivity) (Real.sqrt_nonneg _)) hJ0
  refine ⟨_, hCmod_nn, ?_⟩
  intro n gs m hm
  set δ := T / (m : ℝ) with hδdef
  set A := ν⁻¹ * ((1 / 2 : ℝ) * ‖(u₀ : L2VF_R3)‖ ^ 2) with hAdef
  -- basic facts about the mesh
  have hmne : (m : ℝ) ≠ 0 := by positivity
  have hδ0 : 0 < δ := by rw [hδdef]; exact div_pos hT (by exact_mod_cast hm)
  have hmδT : (m : ℝ) * δ = T := by rw [hδdef]; field_simp
  have hδT : δ ≤ T := by rw [hδdef]; exact div_le_self hT.le (by exact_mod_cast hm)
  have hAnn : 0 ≤ A := hAnn0
  -- curve facts on `[0,T]`
  have hV1nn : ∀ σ, 0 ≤ viscousFormSq_R3 1 (gs.u σ : L2VF_R3) :=
    fun σ => viscousFormSq_R3_nonneg zero_le_one _
  have hIci : Set.Icc (0:ℝ) T ⊆ Set.Ici (0:ℝ) := fun x hx => hx.1
  have hV1c0T : ContinuousOn (fun σ => viscousFormSq_R3 1 (gs.u σ : L2VF_R3)) (Set.Icc 0 T) :=
    (galerkin_viscous_curve_continuousOn gs).mono hIci
  have hV1ii0T : IntervalIntegrable (fun σ => viscousFormSq_R3 1 (gs.u σ : L2VF_R3)) volume 0 T :=
    hV1c0T.intervalIntegrable_of_Icc hT.le
  have hV1_ae : 0 ≤ᵐ[volume.restrict (Set.Ioc (0:ℝ) T)]
      (fun σ => viscousFormSq_R3 1 (gs.u σ : L2VF_R3)) := ae_of_all _ (fun σ => hV1nn σ)
  -- `∫₀ᵀ V₁ ≤ A` from `reg_bound` (ν-scaled)
  have hintVν : (∫ t in (0:ℝ)..T, viscousFormSq_R3 ν (gs.u t : L2VF_R3))
      = ν * ∫ t in (0:ℝ)..T, viscousFormSq_R3 1 (gs.u t : L2VF_R3) := by
    simp_rw [viscousFormSq_R3_smul' ν]
    exact intervalIntegral.integral_const_mul ν _
  have hV1int_le : (∫ t in (0:ℝ)..T, viscousFormSq_R3 1 (gs.u t : L2VF_R3)) ≤ A := by
    have hh := gs.reg_bound T hT
    rw [hintVν] at hh
    calc (∫ t in (0:ℝ)..T, viscousFormSq_R3 1 (gs.u t : L2VF_R3))
        = ν⁻¹ * (ν * ∫ t in (0:ℝ)..T, viscousFormSq_R3 1 (gs.u t : L2VF_R3)) := by
          rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hν), one_mul]
      _ ≤ ν⁻¹ * ((1 / 2 : ℝ) * ‖(u₀ : L2VF_R3)‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hν.le)
  have hint_V1_nn : 0 ≤ ∫ t in (0:ℝ)..T, viscousFormSq_R3 1 (gs.u t : L2VF_R3) :=
    intervalIntegral.integral_nonneg hT.le (fun σ _ => hV1nn σ)
  -- STEP 1: per-cell good samples via D1
  have hgs : ∀ i : Fin m, ∃ τi ∈ Set.Icc (((i : ℕ) : ℝ) * δ) ((((i : ℕ) : ℝ) + 1) * δ),
      viscousFormSq_R3 1 (gs.u τi : L2VF_R3)
        ≤ δ⁻¹ * ∫ σ in (((i : ℕ) : ℝ) * δ)..((((i : ℕ) : ℝ) + 1) * δ),
            viscousFormSq_R3 1 (gs.u σ : L2VF_R3) := by
    intro i
    have hlt : ((i : ℕ) : ℝ) * δ < (((i : ℕ) : ℝ) + 1) * δ := by
      have e : (((i : ℕ) : ℝ) + 1) * δ = ((i : ℕ) : ℝ) * δ + δ := by ring
      rw [e]; linarith [hδ0]
    have hsub : Set.Icc (((i : ℕ) : ℝ) * δ) ((((i : ℕ) : ℝ) + 1) * δ) ⊆ Set.Ici (0:ℝ) :=
      fun x hx => le_trans (mul_nonneg (Nat.cast_nonneg _) hδ0.le) hx.1
    have hcont : ContinuousOn (fun σ => viscousFormSq_R3 1 (gs.u σ : L2VF_R3))
        (Set.Icc (((i : ℕ) : ℝ) * δ) ((((i : ℕ) : ℝ) + 1) * δ)) :=
      (galerkin_viscous_curve_continuousOn gs).mono hsub
    obtain ⟨τi, hmem, hbd⟩ := exists_goodSample hlt hcont
      (fun σ _ => viscousFormSq_R3_nonneg zero_le_one _)
    exact ⟨τi, hmem, by rwa [show (((i : ℕ) : ℝ) + 1) * δ - ((i : ℕ) : ℝ) * δ = δ from by ring] at hbd⟩
  choose τ hτmem hτbd using hgs
  -- STEP 2: the good-sample Dirichlet bound (2nd conjunct)
  have hcell_le : ∀ i : Fin m,
      (∫ σ in (((i : ℕ) : ℝ) * δ)..((((i : ℕ) : ℝ) + 1) * δ), viscousFormSq_R3 1 (gs.u σ : L2VF_R3))
        ≤ ∫ σ in (0:ℝ)..T, viscousFormSq_R3 1 (gs.u σ : L2VF_R3) := by
    intro i
    have hle1 : (0:ℝ) ≤ ((i : ℕ) : ℝ) * δ := mul_nonneg (Nat.cast_nonneg _) hδ0.le
    have hle2 : ((i : ℕ) : ℝ) * δ ≤ (((i : ℕ) : ℝ) + 1) * δ := by
      have e : (((i : ℕ) : ℝ) + 1) * δ = ((i : ℕ) : ℝ) * δ + δ := by ring
      rw [e]; linarith [hδ0]
    have hle3 : (((i : ℕ) : ℝ) + 1) * δ ≤ T := by
      rw [← hmδT]
      apply mul_le_mul_of_nonneg_right _ hδ0.le
      exact_mod_cast Nat.succ_le_of_lt i.isLt
    exact intervalIntegral.integral_mono_interval hle1 hle2 hle3 hV1_ae hV1ii0T
  have hgood : ∀ i : Fin m, viscousFormSq_R3 1 (gs.u (τ i) : L2VF_R3)
      ≤ 2 * δ⁻¹ * ν⁻¹ * ((1 / 2 : ℝ) * ‖(u₀ : L2VF_R3)‖ ^ 2) := by
    intro i
    have hδinv : 0 ≤ δ⁻¹ := inv_nonneg.mpr hδ0.le
    have hchain : viscousFormSq_R3 1 (gs.u (τ i) : L2VF_R3) ≤ δ⁻¹ * A := by
      refine le_trans (hτbd i) ?_
      exact mul_le_mul_of_nonneg_left (le_trans (hcell_le i) hV1int_le) hδinv
    have hprod : 0 ≤ δ⁻¹ * A := mul_nonneg hδinv hAnn
    calc viscousFormSq_R3 1 (gs.u (τ i) : L2VF_R3) ≤ δ⁻¹ * A := hchain
      _ ≤ 2 * δ⁻¹ * ν⁻¹ * ((1 / 2 : ℝ) * ‖(u₀ : L2VF_R3)‖ ^ 2) := by rw [hAdef]; nlinarith [hprod, hAnn, hδinv]
  refine ⟨τ, hτmem, hgood, ?_⟩
  -- STEP 3: per-cell D2 bound
  have hD2 : ∀ i : Fin m,
      (∫ t in (((i : ℕ) : ℝ) * δ)..((((i : ℕ) : ℝ) + 1) * δ),
          ‖(gs.u t : L2VF_R3) - (gs.u (τ i) : L2VF_R3)‖ ^ 2)
        ≤ 2 * δ * (∫ σ in (((i : ℕ) : ℝ) * δ)..((((i : ℕ) : ℝ) + 1) * δ),
              viscousFormSq_R3 ν (gs.u σ : L2VF_R3))
          + 2 * δ * Real.sqrt (2 * δ⁻¹ * ν⁻¹ * ((1 / 2 : ℝ) * ‖(u₀ : L2VF_R3)‖ ^ 2))
              * ∫ σ in (((i : ℕ) : ℝ) * δ)..((((i : ℕ) : ℝ) + 1) * δ),
                  (ν * Real.sqrt (viscousFormSq_R3 1 (gs.u σ : L2VF_R3))
                    + C_b * ‖(u₀ : L2VF_R3)‖ ^ (1 / 2 : ℝ)
                        * (viscousFormSq_R3 1 (gs.u σ : L2VF_R3)) ^ (3 / 4 : ℝ)) := by
    intro i
    have hai : (0:ℝ) ≤ ((i : ℕ) : ℝ) * δ := mul_nonneg (Nat.cast_nonneg _) hδ0.le
    have hmemi : τ i ∈ Set.Icc (((i : ℕ) : ℝ) * δ) (((i : ℕ) : ℝ) * δ + δ) := by
      have := hτmem i
      rwa [show (((i : ℕ) : ℝ) + 1) * δ = ((i : ℕ) : ℝ) * δ + δ from by ring] at this
    have hcell := galerkin_cell_error_bound ν hν u₀ n gs C_b hC_b0 hC_b (((i : ℕ) : ℝ) * δ) δ
      hai hδ0 (τ i) hmemi (hgood i)
    rwa [show ((i : ℕ) : ℝ) * δ + δ = (((i : ℕ) : ℝ) + 1) * δ from by ring] at hcell
  -- STEP 4: telescope the fixed-integrand cell sums
  have htele : ∀ (f : ℝ → ℝ), ContinuousOn f (Set.Icc 0 T) →
      (∑ i : Fin m, ∫ σ in (((i : ℕ) : ℝ) * δ)..((((i : ℕ) : ℝ) + 1) * δ), f σ)
        = ∫ σ in (0:ℝ)..T, f σ := by
    intro f hf
    have key : (∑ k ∈ Finset.range m,
        ∫ σ in ((fun j : ℕ => (j : ℝ) * δ) k)..((fun j : ℕ => (j : ℝ) * δ) (k + 1)), f σ)
        = ∫ σ in ((fun j : ℕ => (j : ℝ) * δ) 0)..((fun j : ℕ => (j : ℝ) * δ) m), f σ := by
      refine intervalIntegral.sum_integral_adjacent_intervals (fun k hk => ?_)
      have hle : (k : ℝ) * δ ≤ ((k + 1 : ℕ) : ℝ) * δ := by
        have : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ k
        nlinarith [hδ0]
      have hsub : Set.Icc ((k : ℝ) * δ) (((k + 1 : ℕ) : ℝ) * δ) ⊆ Set.Icc 0 T := by
        refine Set.Icc_subset_Icc (mul_nonneg (Nat.cast_nonneg _) hδ0.le) ?_
        rw [← hmδT]
        apply mul_le_mul_of_nonneg_right _ hδ0.le
        exact_mod_cast Nat.succ_le_of_lt hk
      exact (hf.mono hsub).intervalIntegrable_of_Icc hle
    simp only [Nat.cast_zero, zero_mul, Nat.cast_add, Nat.cast_one] at key
    rw [hmδT] at key
    rw [Fin.sum_univ_eq_sum_range (fun k => ∫ σ in ((k : ℝ) * δ)..(((k : ℝ) + 1) * δ), f σ) m]
    exact key
  have hVνc0T : ContinuousOn (fun σ => viscousFormSq_R3 ν (gs.u σ : L2VF_R3)) (Set.Icc 0 T) :=
    (continuousOn_const.mul hV1c0T).congr (fun σ _ => viscousFormSq_R3_smul' ν _)
  have hconvc0T : ContinuousOn
      (fun σ => ν * Real.sqrt (viscousFormSq_R3 1 (gs.u σ : L2VF_R3))
        + C_b * ‖(u₀ : L2VF_R3)‖ ^ (1 / 2 : ℝ)
            * (viscousFormSq_R3 1 (gs.u σ : L2VF_R3)) ^ (3 / 4 : ℝ)) (Set.Icc 0 T) :=
    (continuousOn_const.mul hV1c0T.sqrt).add
      (continuousOn_const.mul (hV1c0T.rpow_const (fun σ _ => Or.inr (by norm_num))))
  -- STEP 5: sum the per-cell bounds
  have hsum_le : (∑ i : Fin m, ∫ t in (((i : ℕ) : ℝ) * δ)..((((i : ℕ) : ℝ) + 1) * δ),
        ‖(gs.u t : L2VF_R3) - (gs.u (τ i) : L2VF_R3)‖ ^ 2)
      ≤ 2 * δ * (∫ σ in (0:ℝ)..T, viscousFormSq_R3 ν (gs.u σ : L2VF_R3))
        + 2 * δ * Real.sqrt (2 * δ⁻¹ * ν⁻¹ * ((1 / 2 : ℝ) * ‖(u₀ : L2VF_R3)‖ ^ 2))
            * ∫ σ in (0:ℝ)..T, (ν * Real.sqrt (viscousFormSq_R3 1 (gs.u σ : L2VF_R3))
                + C_b * ‖(u₀ : L2VF_R3)‖ ^ (1 / 2 : ℝ)
                    * (viscousFormSq_R3 1 (gs.u σ : L2VF_R3)) ^ (3 / 4 : ℝ)) := by
    have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hD2 i)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      htele (fun σ => viscousFormSq_R3 ν (gs.u σ : L2VF_R3)) hVνc0T,
      htele (fun σ => ν * Real.sqrt (viscousFormSq_R3 1 (gs.u σ : L2VF_R3))
        + C_b * ‖(u₀ : L2VF_R3)‖ ^ (1 / 2 : ℝ)
            * (viscousFormSq_R3 1 (gs.u σ : L2VF_R3)) ^ (3 / 4 : ℝ)) hconvc0T] at h
    exact h
  -- STEP 6: the two closed-form bounds
  have hEbound : 2 * δ * (∫ σ in (0:ℝ)..T, viscousFormSq_R3 ν (gs.u σ : L2VF_R3))
      ≤ (Real.sqrt T * ‖(u₀ : L2VF_R3)‖ ^ 2) * Real.sqrt δ := by
    have hregb := gs.reg_bound T hT
    have hδleT : Real.sqrt δ ≤ Real.sqrt T := Real.sqrt_le_sqrt hδT
    have hδself : Real.sqrt δ * Real.sqrt δ = δ := Real.mul_self_sqrt hδ0.le
    have hnorm2 : 0 ≤ ‖(u₀ : L2VF_R3)‖ ^ 2 := sq_nonneg _
    calc 2 * δ * (∫ σ in (0:ℝ)..T, viscousFormSq_R3 ν (gs.u σ : L2VF_R3))
        ≤ 2 * δ * ((1 / 2 : ℝ) * ‖(u₀ : L2VF_R3)‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hregb (by linarith [hδ0])
      _ = (Real.sqrt δ * Real.sqrt δ) * ‖(u₀ : L2VF_R3)‖ ^ 2 := by rw [hδself]; ring
      _ ≤ (Real.sqrt T * Real.sqrt δ) * ‖(u₀ : L2VF_R3)‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hδleT (Real.sqrt_nonneg _)) hnorm2
      _ = (Real.sqrt T * ‖(u₀ : L2VF_R3)‖ ^ 2) * Real.sqrt δ := by ring
  -- time-Hölder bound on the convection integral
  have hsqrt_int : (∫ σ in (0:ℝ)..T, Real.sqrt (viscousFormSq_R3 1 (gs.u σ : L2VF_R3)))
      ≤ T ^ (1 / 2 : ℝ) * (∫ σ in (0:ℝ)..T, viscousFormSq_R3 1 (gs.u σ : L2VF_R3)) ^ (1 / 2 : ℝ) := by
    have hlem := intervalIntegral_rpow_le_of_nonneg hT hV1c0T (fun σ _ => hV1nn σ)
      (r := 1 / 2) (by norm_num) (by norm_num)
    rw [show (1:ℝ) - 1 / 2 = 1 / 2 from by norm_num] at hlem
    simp_rw [Real.sqrt_eq_rpow]
    exact hlem
  have h34_int : (∫ σ in (0:ℝ)..T, (viscousFormSq_R3 1 (gs.u σ : L2VF_R3)) ^ (3 / 4 : ℝ))
      ≤ T ^ (1 / 4 : ℝ) * (∫ σ in (0:ℝ)..T, viscousFormSq_R3 1 (gs.u σ : L2VF_R3)) ^ (3 / 4 : ℝ) := by
    have hlem := intervalIntegral_rpow_le_of_nonneg hT hV1c0T (fun σ _ => hV1nn σ)
      (r := 3 / 4) (by norm_num) (by norm_num)
    rwa [show (1:ℝ) - 3 / 4 = 1 / 4 from by norm_num] at hlem
  have hconv_le : (∫ σ in (0:ℝ)..T, (ν * Real.sqrt (viscousFormSq_R3 1 (gs.u σ : L2VF_R3))
        + C_b * ‖(u₀ : L2VF_R3)‖ ^ (1 / 2 : ℝ)
            * (viscousFormSq_R3 1 (gs.u σ : L2VF_R3)) ^ (3 / 4 : ℝ)))
      ≤ ν * T ^ (1 / 2 : ℝ) * A ^ (1 / 2 : ℝ)
        + C_b * ‖(u₀ : L2VF_R3)‖ ^ (1 / 2 : ℝ) * T ^ (1 / 4 : ℝ) * A ^ (3 / 4 : ℝ) := by
    have hII1 : IntervalIntegrable
        (fun σ => ν * Real.sqrt (viscousFormSq_R3 1 (gs.u σ : L2VF_R3))) volume 0 T :=
      (continuousOn_const.mul hV1c0T.sqrt).intervalIntegrable_of_Icc hT.le
    have hII2 : IntervalIntegrable
        (fun σ => C_b * ‖(u₀ : L2VF_R3)‖ ^ (1 / 2 : ℝ)
          * (viscousFormSq_R3 1 (gs.u σ : L2VF_R3)) ^ (3 / 4 : ℝ)) volume 0 T :=
      (continuousOn_const.mul (hV1c0T.rpow_const (fun σ _ => Or.inr (by norm_num)))).intervalIntegrable_of_Icc hT.le
    rw [intervalIntegral.integral_add hII1 hII2,
      intervalIntegral.integral_const_mul ν (fun σ => Real.sqrt (viscousFormSq_R3 1 (gs.u σ : L2VF_R3))),
      intervalIntegral.integral_const_mul (C_b * ‖(u₀ : L2VF_R3)‖ ^ (1 / 2 : ℝ))
        (fun σ => (viscousFormSq_R3 1 (gs.u σ : L2VF_R3)) ^ (3 / 4 : ℝ))]
    have hAhalf : (∫ σ in (0:ℝ)..T, viscousFormSq_R3 1 (gs.u σ : L2VF_R3)) ^ (1 / 2 : ℝ)
        ≤ A ^ (1 / 2 : ℝ) := Real.rpow_le_rpow hint_V1_nn hV1int_le (by norm_num)
    have hA34 : (∫ σ in (0:ℝ)..T, viscousFormSq_R3 1 (gs.u σ : L2VF_R3)) ^ (3 / 4 : ℝ)
        ≤ A ^ (3 / 4 : ℝ) := Real.rpow_le_rpow hint_V1_nn hV1int_le (by norm_num)
    have hb1 : ν * (∫ σ in (0:ℝ)..T, Real.sqrt (viscousFormSq_R3 1 (gs.u σ : L2VF_R3)))
        ≤ ν * T ^ (1 / 2 : ℝ) * A ^ (1 / 2 : ℝ) := by
      calc ν * (∫ σ in (0:ℝ)..T, Real.sqrt (viscousFormSq_R3 1 (gs.u σ : L2VF_R3)))
          ≤ ν * (T ^ (1 / 2 : ℝ) * (∫ σ in (0:ℝ)..T, viscousFormSq_R3 1 (gs.u σ : L2VF_R3)) ^ (1 / 2 : ℝ)) :=
            mul_le_mul_of_nonneg_left hsqrt_int hν.le
        _ ≤ ν * (T ^ (1 / 2 : ℝ) * A ^ (1 / 2 : ℝ)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hAhalf (Real.rpow_nonneg hT.le _)) hν.le
        _ = ν * T ^ (1 / 2 : ℝ) * A ^ (1 / 2 : ℝ) := by ring
    have hb2 : (C_b * ‖(u₀ : L2VF_R3)‖ ^ (1 / 2 : ℝ))
          * (∫ σ in (0:ℝ)..T, (viscousFormSq_R3 1 (gs.u σ : L2VF_R3)) ^ (3 / 4 : ℝ))
        ≤ C_b * ‖(u₀ : L2VF_R3)‖ ^ (1 / 2 : ℝ) * T ^ (1 / 4 : ℝ) * A ^ (3 / 4 : ℝ) := by
      have hc0 : 0 ≤ C_b * ‖(u₀ : L2VF_R3)‖ ^ (1 / 2 : ℝ) :=
        mul_nonneg hC_b0 (Real.rpow_nonneg (norm_nonneg _) _)
      calc (C_b * ‖(u₀ : L2VF_R3)‖ ^ (1 / 2 : ℝ))
            * (∫ σ in (0:ℝ)..T, (viscousFormSq_R3 1 (gs.u σ : L2VF_R3)) ^ (3 / 4 : ℝ))
          ≤ (C_b * ‖(u₀ : L2VF_R3)‖ ^ (1 / 2 : ℝ))
            * (T ^ (1 / 4 : ℝ) * (∫ σ in (0:ℝ)..T, viscousFormSq_R3 1 (gs.u σ : L2VF_R3)) ^ (3 / 4 : ℝ)) :=
            mul_le_mul_of_nonneg_left h34_int hc0
        _ ≤ (C_b * ‖(u₀ : L2VF_R3)‖ ^ (1 / 2 : ℝ)) * (T ^ (1 / 4 : ℝ) * A ^ (3 / 4 : ℝ)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hA34 (Real.rpow_nonneg hT.le _)) hc0
        _ = C_b * ‖(u₀ : L2VF_R3)‖ ^ (1 / 2 : ℝ) * T ^ (1 / 4 : ℝ) * A ^ (3 / 4 : ℝ) := by ring
    linarith [hb1, hb2]
  -- the pairing factor `2δ√(2δ⁻¹ν⁻¹E₀) = 2√2·√A·√δ`
  have hsf_eq : 2 * δ * Real.sqrt (2 * δ⁻¹ * ν⁻¹ * ((1 / 2 : ℝ) * ‖(u₀ : L2VF_R3)‖ ^ 2))
      = 2 * Real.sqrt 2 * Real.sqrt A * Real.sqrt δ := by
    have hds : δ * (Real.sqrt δ)⁻¹ = Real.sqrt δ := by rw [← div_eq_mul_inv]; exact Real.div_sqrt
    rw [show 2 * δ⁻¹ * ν⁻¹ * ((1 / 2 : ℝ) * ‖(u₀ : L2VF_R3)‖ ^ 2) = 2 * A * δ⁻¹ from by rw [hAdef]; ring,
      Real.sqrt_mul (by linarith [hAnn] : (0:ℝ) ≤ 2 * A), Real.sqrt_inv,
      Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2) A]
    rw [show 2 * δ * (Real.sqrt 2 * Real.sqrt A * (Real.sqrt δ)⁻¹)
        = 2 * Real.sqrt 2 * Real.sqrt A * (δ * (Real.sqrt δ)⁻¹) from by ring, hds]
  have hPbound : 2 * δ * Real.sqrt (2 * δ⁻¹ * ν⁻¹ * ((1 / 2 : ℝ) * ‖(u₀ : L2VF_R3)‖ ^ 2))
        * (∫ σ in (0:ℝ)..T, (ν * Real.sqrt (viscousFormSq_R3 1 (gs.u σ : L2VF_R3))
            + C_b * ‖(u₀ : L2VF_R3)‖ ^ (1 / 2 : ℝ)
                * (viscousFormSq_R3 1 (gs.u σ : L2VF_R3)) ^ (3 / 4 : ℝ)))
      ≤ (2 * Real.sqrt 2 * Real.sqrt A
          * (ν * T ^ (1 / 2 : ℝ) * A ^ (1 / 2 : ℝ)
            + C_b * ‖(u₀ : L2VF_R3)‖ ^ (1 / 2 : ℝ) * T ^ (1 / 4 : ℝ) * A ^ (3 / 4 : ℝ)))
          * Real.sqrt δ := by
    rw [hsf_eq]
    calc (2 * Real.sqrt 2 * Real.sqrt A * Real.sqrt δ)
          * (∫ σ in (0:ℝ)..T, (ν * Real.sqrt (viscousFormSq_R3 1 (gs.u σ : L2VF_R3))
              + C_b * ‖(u₀ : L2VF_R3)‖ ^ (1 / 2 : ℝ)
                  * (viscousFormSq_R3 1 (gs.u σ : L2VF_R3)) ^ (3 / 4 : ℝ)))
        = (2 * Real.sqrt 2 * Real.sqrt A)
          * (Real.sqrt δ * (∫ σ in (0:ℝ)..T, (ν * Real.sqrt (viscousFormSq_R3 1 (gs.u σ : L2VF_R3))
              + C_b * ‖(u₀ : L2VF_R3)‖ ^ (1 / 2 : ℝ)
                  * (viscousFormSq_R3 1 (gs.u σ : L2VF_R3)) ^ (3 / 4 : ℝ)))) := by ring
      _ ≤ (2 * Real.sqrt 2 * Real.sqrt A)
          * (Real.sqrt δ * (ν * T ^ (1 / 2 : ℝ) * A ^ (1 / 2 : ℝ)
              + C_b * ‖(u₀ : L2VF_R3)‖ ^ (1 / 2 : ℝ) * T ^ (1 / 4 : ℝ) * A ^ (3 / 4 : ℝ))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hconv_le (Real.sqrt_nonneg _)) (by positivity)
      _ = (2 * Real.sqrt 2 * Real.sqrt A
            * (ν * T ^ (1 / 2 : ℝ) * A ^ (1 / 2 : ℝ)
              + C_b * ‖(u₀ : L2VF_R3)‖ ^ (1 / 2 : ℝ) * T ^ (1 / 4 : ℝ) * A ^ (3 / 4 : ℝ)))
            * Real.sqrt δ := by ring
  -- STEP 7: assemble
  refine le_trans hsum_le ?_
  calc 2 * δ * (∫ σ in (0:ℝ)..T, viscousFormSq_R3 ν (gs.u σ : L2VF_R3))
        + 2 * δ * Real.sqrt (2 * δ⁻¹ * ν⁻¹ * ((1 / 2 : ℝ) * ‖(u₀ : L2VF_R3)‖ ^ 2))
            * ∫ σ in (0:ℝ)..T, (ν * Real.sqrt (viscousFormSq_R3 1 (gs.u σ : L2VF_R3))
                + C_b * ‖(u₀ : L2VF_R3)‖ ^ (1 / 2 : ℝ)
                    * (viscousFormSq_R3 1 (gs.u σ : L2VF_R3)) ^ (3 / 4 : ℝ))
      ≤ (Real.sqrt T * ‖(u₀ : L2VF_R3)‖ ^ 2) * Real.sqrt δ
        + (2 * Real.sqrt 2 * Real.sqrt A
            * (ν * T ^ (1 / 2 : ℝ) * A ^ (1 / 2 : ℝ)
              + C_b * ‖(u₀ : L2VF_R3)‖ ^ (1 / 2 : ℝ) * T ^ (1 / 4 : ℝ) * A ^ (3 / 4 : ℝ)))
            * Real.sqrt δ := add_le_add hEbound hPbound
    _ = (Real.sqrt T * ‖(u₀ : L2VF_R3)‖ ^ 2
          + 2 * Real.sqrt 2 * Real.sqrt A
            * (ν * T ^ (1 / 2 : ℝ) * A ^ (1 / 2 : ℝ)
              + C_b * ‖(u₀ : L2VF_R3)‖ ^ (1 / 2 : ℝ) * T ^ (1 / 4 : ℝ) * A ^ (3 / 4 : ℝ)))
          * Real.sqrt δ := by ring

end LerayHopf
