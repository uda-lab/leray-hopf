import LerayHopf.R3.Regularity
import LerayHopf.R3.WeightedFourierCommute  -- mulBdd (issue #113 PR-1: explicit — the B6-export
  -- section uses it, previously reached only transitively via the now-dropped ConvectionForm
  -- → SolutionInterfaces import)
import LerayHopf.Analysis.PlancherelKernels
-- PlancherelKernels import justification: the four gradient–Fourier Plancherel kernels
-- (`opNorm_le_sqrt_sum_sq`, `normSq_toLp_two`, `normSq_lineDeriv_toLp`,
-- `integral_normSq_fderiv_le`) used by A3 below moved there (issue #111 PR-2) so they can
-- be shared with `EnergyClassConvection.lean`/`GalerkinTrilinearBound.lean`.
-- A4 (`h1Sigma_dense_in_L2Sigma`, needing ConvectionForm's density theorem) moved to
-- `H1SigmaDensity.lean` (issue #113 PR-1) — this file no longer imports ConvectionForm.
import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
import Mathlib.MeasureTheory.Function.Holder
-- Holder import justification: `ContinuousLinearMap.holderL` and the
-- `ENNReal.HolderTriple` typeclass are defined here; the A1 instances and
-- downstream B3b (EnergyClassConvection.lean) require them.

open MeasureTheory TemperedDistribution SchwartzMap

/-!
# GNS Sobolev embedding H¹(ℝ³) ↪ L⁶(ℝ³) — infrastructure for PR-1

**File:** `LerayHopf/R3/SobolevEmbedding.lean`

**Scope (PR-1, rows A1–A4 of the convection-operator construction, issue #56).**

This file provides the Sobolev embedding infrastructure needed by the
`EnergyClassConvection.lean` energy-class convection form (PR-2) and the
`ConvectionExtension.lean` Hamel extension (PR-3).

## Mathematical content

The key fact is the **Gagliardo–Nirenberg–Sobolev (GNS) inequality** on ℝ³: for
`1 ≤ p < n = 3`, the critical exponent satisfies

  `(p')⁻¹ = p⁻¹ - n⁻¹  ==>  eLpNorm u p' ≤ C * eLpNorm (fderiv u) p`

In dimension 3 with `p = 2`, the Sobolev conjugate is `p' = 6`:

  `(6)⁻¹ = (2)⁻¹ - (3)⁻¹  ==>  H¹(ℝ³; F) ↪ L⁶(ℝ³; F)`.

## Declarations

- **A1** `instHolderTriple_6_3_2` — `ENNReal.HolderTriple 6 3 2` instance
  (the pairwise Hölder triple `1/6 + 1/3 = 1/2` used in B3b's integrability chain).
  Also provides `Fact (1 ≤ (6 : ENNReal))` and `Fact (1 ≤ (3 : ENNReal))`.
  NOTE: The plan's `(6,2,3)` notation referred to the Hölder EXPONENTS for three factors
  (`1/6+1/2+1/3=1`), not a single `ENNReal.HolderTriple` predicate (which is pairwise).
  **Scaffold-only: proved by `norm_num`/`ennrealOfReal`; not a must-prove analysis target.**

- **A2** `gns_L6_cc1_R3` — thin GNS wrapper for `ContDiff ℝ 1 u` + `HasCompactSupport u`:
  `eLpNorm u 6 volume ≤ C * eLpNorm (fderiv ℝ u) 2 volume`.
  Directly wraps `MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq` at `p = 2`, `n = 3`.
  **Must-prove (A2), body `-- ALLOW_SORRY: PR-1 must-prove (A2), prover pass`.**

- **A3** `gns_L6_of_memH1_R3` — extension of A2 to `MemSobolev 1 2` (no compact support):
  for `f : L2C_R3` with `TemperedDistribution.MemSobolev 1 2`, `MemLp (⇑f) 6 volume`.
  Route: GNS-for-Schwartz (smooth-cutoff truncation to Cc¹ + A2 + Fatou) → weighted-Fourier
  gradient control (the `integral_normSq_fderiv_le` Plancherel kernel) → Fourier-domain Schwartz
  `H¹`-approximant `φₙ = 𝓕⁻¹(smulLeftCLM (1+‖ξ‖²)^(-1/2) ηₙ)` → Fatou. **PROVED sorry-free.**

- **A4** `h1Sigma_dense_in_L2Sigma` — MOVED to `H1SigmaDensity.lean` (issue #113 PR-1): it is
  the only declaration in this file's original scope that needs `ConvectionForm.lean`
  (`schwartzDivFree_dense_of_curlDense`/`curlSchwartzDense_holds`), so it now lives with that
  import in its own file, downstream of this one.

## Mathlib decls consumed

| Decl | File | Used by |
|---|---|---|
| `MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq` | `FunctionalSpaces/SobolevInequality.lean:600` | A2 |
| `MeasureTheory.SNormLESNormFDerivOfEqConst` | `FunctionalSpaces/SobolevInequality.lean:587` | A2 |
| `ENNReal.HolderTriple` | `Data/ENNReal/Holder.lean:42` | A1 |
| `TemperedDistribution.MemSobolev` | `Analysis/Distribution/Sobolev.lean:149` | A3 |
| `SchwartzMap.denseRange_toLpCLM` | `Analysis/Distribution/SchwartzSpace/Basic.lean:1379` | A3 |
| `SchwartzMap.memSobolev` | `Analysis/Distribution/Sobolev.lean:201` | A4 |

## Assumptions

None — this file introduces no `axiom`/`opaque`.

**Status (prover pass):** A2 (`gns_L6_cc1_R3`) and A3 (`gns_L6_of_memH1_R3`) are both PROVED
sorry-free (A3 depends only on `propext`/`Classical.choice`/`Quot.sound` — no `sorryAx`, no
project axiom). A4 (`h1Sigma_dense_in_L2Sigma`, also PROVED sorry-free) is in
`H1SigmaDensity.lean`. A3 is assembled from:
- the four Plancherel kernels (`PlancherelKernels.opNorm_le_sqrt_sum_sq`,
  `PlancherelKernels.normSq_toLp_two`, `PlancherelKernels.normSq_lineDeriv_toLp`,
  `PlancherelKernels.integral_normSq_fderiv_le` — moved to `LerayHopf/Analysis/PlancherelKernels.lean`,
  issue #111 PR-2, so `EnergyClassConvection.lean`/`GalerkinTrilinearBound.lean` can share them),
  giving the gradient↔Fourier control `∫ ‖fderiv φ x‖² ≤ (2π)² ∫ ‖ξ‖² ‖𝓕 φ ξ‖²` for Schwartz `φ`;
- a smooth radial cutoff `cutoff R x = χ((1/R)•x)` (`ContDiffBump`, `rIn=1`, `rOut=2`) with the
  hand-proved `O(1/R)` gradient bound `‖∇(cutoff R)‖_∞ ≤ K/R` (mathlib's `ContDiffBump` exposes
  no such bound, so it is built here);
- `gns_L6_schwartz`: GNS for Schwartz `φ` (no compact support) via truncating `φ` to
  `cutoff R • φ` (which is Cc¹), applying A2, and passing `R → ∞` through
  `Lp.eLpNorm_lim_le_liminf_eLpNorm` (the local Fatou — transitively available, no extra import);
- `eLpNorm_fderiv_le_weighted` + `integrable_one_add_normSq_schwartz`: the weighted-Fourier
  gradient bound `eLpNorm (fderiv φ) 2 ≤ ofReal (2π·√(∫(1+‖ξ‖²)‖𝓕φ‖²))`;
- `fourier_ae_eq_wInv_smul`: the scalar H¹⇒weighted-L² extraction `⇑(𝓕 f) =ᵐ wInv • f'`
  (adapting `RellichBall.memH1_weightedL2_integrable_R`'s du-Bois-Reymond a.e. step);
- the Fourier-domain Schwartz `H¹`-approximant `φₙ = 𝓕⁻¹(smulLeftCLM (1+‖ξ‖²)^(-1/2) ηₙ)` with
  `ηₙ.toLp → f'`, giving a uniform L⁶ bound `eLpNorm φₙ 6 ≤ C·2π·M` and `φₙ.toLp → f` in L²
  (Fourier isometry + the bounded multiplier `mulBdd wInv`);
- the final Fatou `Lp.eLpNorm_le_of_ae_tendsto` along an a.e.-convergent subsequence.
-/

namespace LerayHopf

/-! ### A1 — Hölder triple `(6, 2, 3)` and `Fact` instances -/

/-- **A1 [scaffold].** The Hölder triple `(6, 3, 2)` in `ENNReal`:
`6⁻¹ + 3⁻¹ = 2⁻¹` in `ℝ≥0∞`, i.e. `1/6 + 1/3 = 1/2`.

This is one of two pairwise instances needed to prove integrability of a triple product
`u · ∂v · w` with `u ∈ L⁶`, `∂v ∈ L²`, `w ∈ L³` (where `1/6 + 1/2 + 1/3 = 1`):
- **This instance** `HolderTriple 6 3 2`: combine `u ∈ L⁶` and `w ∈ L³` to get
  `u·w ∈ L²` (since `1/6 + 1/3 = 1/2`).
- Then use `HolderConjugate 2 2` (already in mathlib as `instTwoTwo`) to combine
  `u·w ∈ L²` and `∂v ∈ L²` to get `u·∂v·w ∈ L¹`.

NOTE: The plan's description `(6,2,3)` with `1/6+1/2+1/3=1` referred to the TRIPLE
of exponents appearing in Hölder's inequality for three factors, NOT to an `ENNReal.HolderTriple`
instance (which is a PAIRWISE predicate: `p⁻¹ + q⁻¹ = r⁻¹`). The correct pairwise
instance for the B3b chain is `HolderTriple 6 3 2` (`1/6 + 1/3 = 1/2`).

Used by B3b (`convFormH1_integrable`) in `EnergyClassConvection.lean`. -/
instance instHolderTriple_6_3_2 : ENNReal.HolderTriple 6 3 2 := by
  -- Use Real.HolderTriple.ennrealOfReal: if 6⁻¹ + 3⁻¹ = 2⁻¹ in ℝ, lift to ENNReal.
  -- Real.HolderTriple 6 3 2 has three fields: inv_add_inv_eq_inv, left_pos, right_pos.
  have h : Real.HolderTriple (6 : ℝ) (3 : ℝ) (2 : ℝ) := by
    constructor <;> norm_num
  have := h.ennrealOfReal
  -- ENNReal.ofReal 6 = 6, ENNReal.ofReal 3 = 3, ENNReal.ofReal 2 = 2 as ENNReal literals
  simpa using this

/-- **A1 [scaffold].** `Fact (1 ≤ (6 : ENNReal))` — needed for `Lp` APIs at `p = 6`. -/
instance instFact_one_le_six_ennreal : Fact ((1 : ENNReal) ≤ 6) :=
  ⟨by norm_num⟩

/-- **A1 [scaffold].** `Fact (1 ≤ (3 : ENNReal))` — needed for `Lp` APIs at `p = 3`. -/
instance instFact_one_le_three_ennreal : Fact ((1 : ENNReal) ≤ 3) :=
  ⟨by norm_num⟩

/-! ### A2 — GNS inequality for Cc¹ functions on ℝ³ -/

/-- **A2 `gns_L6_cc1_R3` [must-prove].**
The Gagliardo–Nirenberg–Sobolev inequality for `C¹` compactly-supported functions on ℝ³
with values in a finite-dimensional normed real vector space `F`.

`eLpNorm u 6 volume ≤ C * eLpNorm (fderiv ℝ u) 2 volume`

where `C := SNormLESNormFDerivOfEqConst F (volume : Measure Domain3) 2` is the
mathlib GNS constant (independent of `u`, depending only on `F` and the measure on ℝ³).

**Proof plan (for prover pass):** Direct application of
`MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq` at:
- `E := Domain3` (`FiniteDimensional ℝ`, `finrank ℝ Domain3 = 3`)
- `p := (2 : NNReal)`, `p' := (6 : NNReal)` in the NNReal signature
- `hp' : (6 : ℝ)⁻¹ = (2 : ℝ)⁻¹ - (3 : ℝ)⁻¹` (= `1/6 = 1/2 - 1/3`, by `norm_num`)
- `hp : 1 ≤ (2 : NNReal)` (by `norm_num`)
- `hn : 0 < finrank ℝ Domain3` (= `0 < 3`)

The μ in `eLpNorm_le_eLpNorm_fderiv_of_eq` is any `IsAddHaarMeasure`, satisfied by
`volume : Measure Domain3` via `measureSpaceOfInnerProductSpace`. -/
theorem gns_L6_cc1_R3 {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F]
    {u : Domain3 → F} (hu : ContDiff ℝ 1 u) (h2u : HasCompactSupport u) :
    eLpNorm u 6 (volume : Measure Domain3) ≤
      SNormLESNormFDerivOfEqConst F (volume : Measure Domain3) 2 *
        eLpNorm (fderiv ℝ u) 2 (volume : Measure Domain3) := by
  -- `finrank ℝ Domain3 = 3`.
  have hfr : (Module.finrank ℝ Domain3) = 3 := by
    simp [Domain3, finrank_euclideanSpace, Fintype.card_fin]
  -- Apply mathlib GNS at `p = 2`, `p' = 6`, `n = finrank ℝ Domain3 = 3`.
  have hp : (1 : NNReal) ≤ 2 := by norm_num
  have hn : 0 < Module.finrank ℝ Domain3 := by rw [hfr]; norm_num
  have hp' : ((6 : NNReal) : ℝ)⁻¹ = ((2 : NNReal) : ℝ)⁻¹ - (Module.finrank ℝ Domain3 : ℝ)⁻¹ := by
    rw [hfr]; push_cast; norm_num
  have h := MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq
    (μ := (volume : Measure Domain3)) (F := F) hu h2u hp hn hp'
  -- Reconcile `((6 : NNReal) : ℝ≥0∞) = (6 : ℝ≥0∞)` and `((2 : NNReal) : ℝ≥0∞) = (2 : ℝ≥0∞)`.
  simpa using h

-- The gradient–Fourier Plancherel kernels moved to `LerayHopf.Analysis.PlancherelKernels`
-- (issue #111 PR-2) used to open the Fourier/LineDeriv notation this file's remaining A3/A4
-- content (below) also relies on (`𝓕`, `∂_{m}`) — re-opened here so the rest of the file is
-- unaffected by the move.
open FourierTransform
open scoped Real LineDeriv RealInnerProductSpace FourierTransform

/-! ### A3 infrastructure — smooth radial cutoff with `O(1/R)` gradient

Mathlib's GNS variants all require `HasCompactSupport`, while `MemSobolev 1 2` is defined via
Fourier multipliers (no compact support). To bridge, we truncate a Schwartz function `φ` by a
smooth radial cutoff `cutoff R x := χ ((1/R) • x)`, where `χ` is a fixed `ContDiffBump` equal to
`1` on `closedBall 0 1` and supported in `closedBall 0 2`. The cutoff has gradient norm
`≤ K / R` (`K := ‖fderiv χ‖_∞`), which `→ 0` as `R → ∞`; this is exactly the `O(1/R)`
gradient bound mathlib's `ContDiffBump` does not expose directly. -/

/-- The fixed smooth bump on `Domain3`: center `0`, `rIn = 1`, `rOut = 2`. -/
private noncomputable def cutoffBump : ContDiffBump (0 : Domain3) := ⟨1, 2, one_pos, by norm_num⟩

private theorem cutoffBump_contDiff : ContDiff ℝ (⊤ : ℕ∞) (cutoffBump : Domain3 → ℝ) :=
  cutoffBump.contDiff

private theorem cutoffBump_differentiable : Differentiable ℝ (cutoffBump : Domain3 → ℝ) :=
  (cutoffBump.contDiff (n := ⊤)).differentiable (by norm_num)

/-- `K := ‖fderiv χ‖_∞`, the (finite) sup of the bump's gradient norm: `fderiv χ` is continuous
with compact support, hence bounded. -/
private theorem cutoffBump_fderiv_bounded :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : Domain3, ‖fderiv ℝ (cutoffBump : Domain3 → ℝ) x‖ ≤ K := by
  have hcont : Continuous (fun x => fderiv ℝ (cutoffBump : Domain3 → ℝ) x) :=
    (cutoffBump_contDiff.fderiv_right (m := 0) (by norm_num)).continuous
  have hsupp : HasCompactSupport (fun x => fderiv ℝ (cutoffBump : Domain3 → ℝ) x) :=
    cutoffBump.hasCompactSupport.fderiv ℝ
  obtain ⟨K, hK⟩ := hsupp.exists_bound_of_continuous hcont
  refine ⟨max K 0, le_max_right _ _, fun x => (hK x).trans (le_max_left _ _)⟩

/-- The scaling operator `(1/R) • id` on `Domain3`, used to express `cutoff R = χ ∘ ((1/R)•·)`. -/
private noncomputable def scaleCLM (R : ℝ) : Domain3 →L[ℝ] Domain3 :=
  (1 / R) • ContinuousLinearMap.id ℝ Domain3

private theorem scaleCLM_apply (R : ℝ) (x : Domain3) : scaleCLM R x = (1 / R) • x := by
  simp [scaleCLM]

private theorem norm_scaleCLM_le (R : ℝ) (hR : 0 < R) : ‖scaleCLM R‖ ≤ 1 / R := by
  rw [scaleCLM, norm_smul, ContinuousLinearMap.norm_id, mul_one, norm_div, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos hR, abs_one]

/-- The smooth radial cutoff at scale `R`: `cutoff R x = χ ((1/R) • x)`. -/
private noncomputable def cutoff (R : ℝ) : Domain3 → ℝ :=
  fun x => (cutoffBump : Domain3 → ℝ) ((1 / R) • x)

private theorem cutoff_contDiff (R : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (cutoff R) := by
  have : cutoff R = (cutoffBump : Domain3 → ℝ) ∘ (fun y => scaleCLM R y) := by
    funext y; simp [cutoff, scaleCLM]
  rw [this]
  exact cutoffBump_contDiff.comp (scaleCLM R).contDiff

private theorem cutoff_nonneg (R : ℝ) (x : Domain3) : 0 ≤ cutoff R x := cutoffBump.nonneg

private theorem cutoff_le_one (R : ℝ) (x : Domain3) : cutoff R x ≤ 1 := cutoffBump.le_one

private theorem abs_cutoff_le_one (R : ℝ) (x : Domain3) : |cutoff R x| ≤ 1 := by
  rw [abs_of_nonneg (cutoff_nonneg R x)]; exact cutoff_le_one R x

/-- `fderiv` of the scaled cutoff via the chain rule. -/
private theorem fderiv_cutoff (R : ℝ) (x : Domain3) :
    fderiv ℝ (cutoff R) x
      = (fderiv ℝ (cutoffBump : Domain3 → ℝ) ((1 / R) • x)).comp (scaleCLM R) := by
  have hcomp : cutoff R = (cutoffBump : Domain3 → ℝ) ∘ (fun y => scaleCLM R y) := by
    funext y; simp [cutoff, scaleCLM]
  rw [hcomp, fderiv_comp _ cutoffBump_differentiable.differentiableAt (scaleCLM R).differentiableAt]
  have hs : scaleCLM R x = (1 / R) • x := scaleCLM_apply R x
  rw [hs, (scaleCLM R).fderiv]

/-- The `O(1/R)` gradient bound: `‖fderiv (cutoff R) x‖ ≤ K / R`. -/
private theorem norm_fderiv_cutoff_le (R : ℝ) (hR : 0 < R) (K : ℝ)
    (hK : ∀ x : Domain3, ‖fderiv ℝ (cutoffBump : Domain3 → ℝ) x‖ ≤ K) (x : Domain3) :
    ‖fderiv ℝ (cutoff R) x‖ ≤ K / R := by
  rw [fderiv_cutoff R x]
  have hKnn : (0 : ℝ) ≤ K := le_trans (norm_nonneg _) (hK ((1 / R) • x))
  calc ‖(fderiv ℝ (cutoffBump : Domain3 → ℝ) ((1 / R) • x)).comp (scaleCLM R)‖
      ≤ ‖fderiv ℝ (cutoffBump : Domain3 → ℝ) ((1 / R) • x)‖ * ‖scaleCLM R‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ K * (1 / R) := by
        gcongr
        · exact hK _
        · exact norm_scaleCLM_le R hR
    _ = K / R := by ring

/-- `cutoff R x = 1` whenever `‖x‖ ≤ R` (then `(1/R)•x ∈ closedBall 0 1`). -/
private theorem cutoff_eq_one_of_norm_le (R : ℝ) (hR : 0 < R) (x : Domain3) (hx : ‖x‖ ≤ R) :
    cutoff R x = 1 := by
  apply cutoffBump.one_of_mem_closedBall
  rw [Metric.mem_closedBall, dist_zero_right, norm_smul]
  have hnorm : ‖(1 / R : ℝ)‖ = 1 / R := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [hnorm]
  show 1 / R * ‖x‖ ≤ 1
  rw [div_mul_eq_mul_div, one_mul, div_le_one hR]
  exact hx

/-- For fixed `x`, the cutoff truncations converge to `1` (eventually equal to `1` along
`R = n → ∞`). -/
private theorem cutoff_tendsto_one (x : Domain3) :
    Filter.Tendsto (fun n : ℕ => cutoff (n + 1 : ℝ) x * (1 : ℂ)) Filter.atTop
      (nhds (1 : ℂ)) := by
  have hev : ∀ᶠ n : ℕ in Filter.atTop, cutoff (n + 1 : ℝ) x * (1 : ℂ) = 1 := by
    obtain ⟨N, hN⟩ := exists_nat_ge ‖x‖
    refine Filter.eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
    have hRpos : (0 : ℝ) < n + 1 := by positivity
    have hxle : ‖x‖ ≤ (n + 1 : ℝ) := by
      calc ‖x‖ ≤ (N : ℝ) := hN
        _ ≤ (n : ℝ) := by exact_mod_cast hn
        _ ≤ (n + 1 : ℝ) := by linarith
    rw [cutoff_eq_one_of_norm_le (n + 1 : ℝ) hRpos x hxle]
    simp
  exact Filter.Tendsto.congr' (Filter.EventuallyEq.symm hev) (tendsto_const_nhds (x := (1 : ℂ)))

/-! ### A3 infrastructure — GNS inequality for Schwartz functions

Combining the cutoff with A2 (`gns_L6_cc1_R3`) and Fatou (`Lp.eLpNorm_le_of_ae_tendsto`):
truncating a Schwartz `φ` to `cutoff R • φ` (which is `Cc¹`), applying A2, and letting `R → ∞`
gives the GNS inequality `eLpNorm φ 6 ≤ C · eLpNorm (fderiv φ) 2` for Schwartz `φ` — without
the compact-support hypothesis. The `O(1/R)` gradient term vanishes in the limit. -/

/-- The truncated Schwartz function `cutoff R • φ`, which is `ContDiff ℝ 1` and `HasCompactSupport`
(supported in `closedBall 0 (2R)`), hence eligible for A2. -/
private theorem truncated_contDiff (R : ℝ) (φ : SchwartzMap Domain3 ℂ) :
    ContDiff ℝ 1 (fun x => cutoff R x • (φ x)) := by
  have h1 : ContDiff ℝ (1 : ℕ∞) (cutoff R) :=
    (cutoff_contDiff R).of_le (by exact_mod_cast le_top)
  have h2 : ContDiff ℝ (1 : ℕ∞) (φ : Domain3 → ℂ) := φ.smooth 1
  have : ContDiff ℝ (1 : ℕ∞) (fun x => cutoff R x • (φ x)) := ContDiff.smul h1 h2
  exact_mod_cast this

private theorem truncated_hasCompactSupport (R : ℝ) (hR : 0 < R) (φ : SchwartzMap Domain3 ℂ) :
    HasCompactSupport (fun x => cutoff R x • (φ x)) := by
  -- Support of cutoff R ⊆ closedBall 0 (2R): cutoff R x = χ((1/R)x) is supported where
  -- ‖(1/R)x‖ ≤ rOut = 2, i.e. ‖x‖ ≤ 2R.
  have hcutoff_supp : HasCompactSupport (cutoff R) := by
    apply HasCompactSupport.intro (isCompact_closedBall (0 : Domain3) (2 * R))
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at hx
    show cutoff R x = 0
    apply cutoffBump.zero_of_le_dist
    rw [dist_zero_right, norm_smul]
    have hnorm : ‖(1 / R : ℝ)‖ = 1 / R := by
      rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [hnorm]
    show (2 : ℝ) ≤ 1 / R * ‖x‖
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hR]
    linarith
  exact hcutoff_supp.smul_right

/-- Pointwise gradient bound for the truncation:
`‖fderiv (cutoff R • φ) x‖ ≤ ‖fderiv φ x‖ + (K/R)·‖φ x‖`. -/
private theorem norm_fderiv_truncated_le (R : ℝ) (hR : 0 < R) (φ : SchwartzMap Domain3 ℂ)
    (K : ℝ) (hK : ∀ x : Domain3, ‖fderiv ℝ (cutoffBump : Domain3 → ℝ) x‖ ≤ K) (x : Domain3) :
    ‖fderiv ℝ (fun y => cutoff R y • (φ y)) x‖ ≤ ‖fderiv ℝ (φ : Domain3 → ℂ) x‖ + (K / R) * ‖φ x‖ := by
  have hχd : DifferentiableAt ℝ (cutoff R) x :=
    ((cutoff_contDiff R).differentiable (by norm_num)).differentiableAt
  have hφd : DifferentiableAt ℝ (φ : Domain3 → ℂ) x :=
    ((φ.smooth 1).differentiable (by norm_num)).differentiableAt
  have hsmul : (fun y => cutoff R y • (φ y)) = (cutoff R • (φ : Domain3 → ℂ)) := by
    funext y; rfl
  rw [hsmul, fderiv_smul hχd hφd]
  calc ‖cutoff R x • fderiv ℝ (φ : Domain3 → ℂ) x + (fderiv ℝ (cutoff R) x).smulRight (φ x)‖
      ≤ ‖cutoff R x • fderiv ℝ (φ : Domain3 → ℂ) x‖ + ‖(fderiv ℝ (cutoff R) x).smulRight (φ x)‖ :=
        norm_add_le _ _
    _ ≤ ‖fderiv ℝ (φ : Domain3 → ℂ) x‖ + (K / R) * ‖φ x‖ := by
        gcongr
        · rw [norm_smul, Real.norm_eq_abs]
          calc |cutoff R x| * ‖fderiv ℝ (φ : Domain3 → ℂ) x‖
              ≤ 1 * ‖fderiv ℝ (φ : Domain3 → ℂ) x‖ :=
                mul_le_mul_of_nonneg_right (abs_cutoff_le_one R x) (norm_nonneg _)
            _ = ‖fderiv ℝ (φ : Domain3 → ℂ) x‖ := one_mul _
        · calc ‖(fderiv ℝ (cutoff R) x).smulRight (φ x)‖
              = ‖fderiv ℝ (cutoff R) x‖ * ‖φ x‖ :=
                ContinuousLinearMap.norm_smulRight_apply _ _
            _ ≤ (K / R) * ‖φ x‖ :=
                mul_le_mul_of_nonneg_right (norm_fderiv_cutoff_le R hR K hK x) (norm_nonneg _)

/-- `eLpNorm` gradient bound for the truncation, in `ℝ≥0∞`:
`eLpNorm (fderiv (cutoff R • φ)) 2 ≤ eLpNorm (fderiv φ) 2 + ofReal (K/R) · eLpNorm φ 2`. -/
private theorem eLpNorm_fderiv_truncated_le (R : ℝ) (hR : 0 < R) (φ : SchwartzMap Domain3 ℂ)
    (K : ℝ) (hKnn : 0 ≤ K) (hK : ∀ x : Domain3, ‖fderiv ℝ (cutoffBump : Domain3 → ℝ) x‖ ≤ K) :
    eLpNorm (fderiv ℝ (fun y => cutoff R y • (φ y))) 2 (volume : Measure Domain3) ≤
      eLpNorm (fderiv ℝ (φ : Domain3 → ℂ)) 2 (volume : Measure Domain3) +
        ENNReal.ofReal (K / R) *
          eLpNorm (φ : Domain3 → ℂ) 2 (volume : Measure Domain3) := by
  -- pointwise bound ‖fderiv gₙ x‖ ≤ ‖fderiv φ x‖ + (K/R)·‖φ x‖ = ‖a x‖ + ‖b x‖ with
  -- a x := fderiv φ x and b x := (K/R) • φ x.
  set a : Domain3 → (Domain3 →L[ℝ] ℂ) := fun x => fderiv ℝ (φ : Domain3 → ℂ) x with ha
  set b : Domain3 → ℂ := fun x => (K / R) • (φ x) with hb
  have hptwise : ∀ x, ‖fderiv ℝ (fun y => cutoff R y • (φ y)) x‖ ≤ ‖a x‖ + ‖b x‖ := by
    intro x
    have h := norm_fderiv_truncated_le R hR φ K hK x
    refine h.trans (le_of_eq ?_)
    rw [hb]
    simp only [ha, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ K / R)]
  calc eLpNorm (fderiv ℝ (fun y => cutoff R y • (φ y))) 2 (volume : Measure Domain3)
      ≤ eLpNorm (fun x => ‖a x‖ + ‖b x‖) 2 (volume : Measure Domain3) :=
        eLpNorm_mono_ae_real (Filter.Eventually.of_forall hptwise)
    _ ≤ eLpNorm (fun x => ‖a x‖) 2 (volume : Measure Domain3)
          + eLpNorm (fun x => ‖b x‖) 2 (volume : Measure Domain3) := by
        refine eLpNorm_add_le ?_ ?_ (by norm_num)
        · exact (continuous_norm.comp_aestronglyMeasurable
            (SchwartzMap.fderivCLM ℝ Domain3 ℂ φ).continuous.aestronglyMeasurable)
        · exact (continuous_norm.comp_aestronglyMeasurable
            (by fun_prop : Continuous b).aestronglyMeasurable)
    _ = eLpNorm (fderiv ℝ (φ : Domain3 → ℂ)) 2 (volume : Measure Domain3)
          + ENNReal.ofReal (K / R) * eLpNorm (φ : Domain3 → ℂ) 2 (volume : Measure Domain3) := by
        rw [eLpNorm_norm, eLpNorm_norm, ha]
        congr 1
        rw [show b = (K / R) • (φ : Domain3 → ℂ) from rfl, eLpNorm_const_smul]
        congr 1
        rw [Real.enorm_eq_ofReal (div_nonneg hKnn hR.le)]

/-- **GNS for Schwartz functions** (no compact support):
`eLpNorm φ 6 ≤ C · eLpNorm (fderiv φ) 2`. Exported (non-`private`) so the energy-class
convection development can obtain a uniform `L⁶` bound on `H¹` Schwartz approximants. -/
theorem gns_L6_schwartz (φ : SchwartzMap Domain3 ℂ) :
    eLpNorm (φ : Domain3 → ℂ) 6 (volume : Measure Domain3) ≤
      SNormLESNormFDerivOfEqConst ℂ (volume : Measure Domain3) 2 *
        eLpNorm (fderiv ℝ (φ : Domain3 → ℂ)) 2 (volume : Measure Domain3) := by
  classical
  obtain ⟨K, hKnn, hK⟩ := cutoffBump_fderiv_bounded
  set C : ENNReal := (SNormLESNormFDerivOfEqConst ℂ (volume : Measure Domain3) 2 : ENNReal) with hC
  set Mg : ENNReal := eLpNorm (fderiv ℝ (φ : Domain3 → ℂ)) 2 (volume : Measure Domain3) with hMg
  set Mφ : ENNReal := eLpNorm (φ : Domain3 → ℂ) 2 (volume : Measure Domain3) with hMφ
  have hMφ_top : Mφ ≠ ⊤ := (φ.memLp 2 (volume : Measure Domain3)).eLpNorm_lt_top.ne
  -- The truncated approximants `gₙ x := cutoff (n+1) x • φ x`.
  set g : ℕ → Domain3 → ℂ := fun n x => cutoff (n + 1 : ℝ) x • (φ x) with hg
  have hRpos : ∀ n : ℕ, (0 : ℝ) < (n + 1 : ℝ) := fun n => by positivity
  -- A2 bound on each truncation: eLpNorm gₙ 6 ≤ C · eLpNorm (fderiv gₙ) 2.
  have hA2 : ∀ n, eLpNorm (g n) 6 (volume : Measure Domain3) ≤
      C * eLpNorm (fderiv ℝ (g n)) 2 (volume : Measure Domain3) := by
    intro n
    exact gns_L6_cc1_R3 (truncated_contDiff (n + 1 : ℝ) φ)
      (truncated_hasCompactSupport (n + 1 : ℝ) (hRpos n) φ)
  -- Gradient bound: eLpNorm (fderiv gₙ) 2 ≤ Mg + ofReal (K/(n+1)) · Mφ.
  have hgrad : ∀ n, eLpNorm (fderiv ℝ (g n)) 2 (volume : Measure Domain3) ≤
      Mg + ENNReal.ofReal (K / (n + 1 : ℝ)) * Mφ := fun n =>
    eLpNorm_fderiv_truncated_le (n + 1 : ℝ) (hRpos n) φ K hKnn hK
  -- Combined eventual bound: eLpNorm gₙ 6 ≤ bₙ := C·(Mg + ofReal(K/(n+1))·Mφ).
  set bdd : ℕ → ENNReal := fun n => C * (Mg + ENNReal.ofReal (K / (n + 1 : ℝ)) * Mφ) with hbdd
  have hbound : ∀ n, eLpNorm (g n) 6 (volume : Measure Domain3) ≤ bdd n := by
    intro n
    refine (hA2 n).trans ?_
    show C * eLpNorm (fderiv ℝ (g n)) 2 (volume : Measure Domain3)
      ≤ C * (Mg + ENNReal.ofReal (K / (n + 1 : ℝ)) * Mφ)
    exact mul_le_mul_left' (hgrad n) C
  -- a.e. (everywhere) convergence gₙ x → φ x.
  have htend : ∀ᵐ x ∂(volume : Measure Domain3),
      Filter.Tendsto (fun n => g n x) Filter.atTop (nhds ((φ : Domain3 → ℂ) x)) := by
    refine Filter.Eventually.of_forall (fun x => ?_)
    have h1 := cutoff_tendsto_one x
    have hc : Filter.Tendsto (fun n : ℕ => (cutoff (n + 1 : ℝ) x : ℝ)) Filter.atTop (nhds 1) := by
      have : Filter.Tendsto (fun n : ℕ => (cutoff (n + 1 : ℝ) x : ℂ)) Filter.atTop (nhds 1) := by
        simpa using h1
      exact_mod_cast (Complex.continuous_re.tendsto 1).comp this |>.congr (fun n => by simp)
    have h2 : Filter.Tendsto (fun n : ℕ => g n x) Filter.atTop (nhds ((1 : ℝ) • (φ x))) := by
      simp only [hg]
      exact hc.smul tendsto_const_nhds
    simpa using h2
  -- measurability of each gₙ
  have hmeas : ∀ n, AEStronglyMeasurable (g n) (volume : Measure Domain3) :=
    fun n => ((truncated_contDiff (n + 1 : ℝ) φ).continuous).aestronglyMeasurable
  -- Fatou: eLpNorm φ 6 ≤ liminf (eLpNorm gₙ 6) ≤ liminf bdd.
  have hfatou : eLpNorm (φ : Domain3 → ℂ) 6 (volume : Measure Domain3) ≤
      Filter.atTop.liminf (fun n => eLpNorm (g n) 6 (volume : Measure Domain3)) :=
    MeasureTheory.Lp.eLpNorm_lim_le_liminf_eLpNorm hmeas _ htend
  -- bdd n → C · Mg, so liminf bdd = C · Mg.
  have htend_bdd : Filter.Tendsto bdd Filter.atTop (nhds (C * Mg)) := by
    have hinner : Filter.Tendsto
        (fun n : ℕ => Mg + ENNReal.ofReal (K / (n + 1 : ℝ)) * Mφ) Filter.atTop (nhds (Mg + 0)) := by
      refine Filter.Tendsto.const_add Mg ?_
      have hvanish : Filter.Tendsto (fun n : ℕ => ENNReal.ofReal (K / (n + 1 : ℝ)))
          Filter.atTop (nhds 0) := by
        have hr : Filter.Tendsto (fun n : ℕ => K / (n + 1 : ℝ)) Filter.atTop (nhds 0) := by
          have h0 : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
              Filter.atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
          have hcm := h0.const_mul K
          have heq : (fun n : ℕ => K * ((1 : ℝ) / ((n : ℝ) + 1)))
              = fun n : ℕ => K / (n + 1 : ℝ) := by
            funext n; rw [mul_one_div]
          rw [heq, mul_zero] at hcm
          exact hcm
        have := (ENNReal.continuous_ofReal.tendsto 0).comp hr
        rw [ENNReal.ofReal_zero] at this
        exact this.congr (fun n => rfl)
      have := ENNReal.Tendsto.mul_const hvanish (Or.inr hMφ_top)
      rw [zero_mul] at this
      exact this
    have hCtop : C ≠ ⊤ := by rw [hC]; exact ENNReal.coe_ne_top
    have hcm : Filter.Tendsto (fun n : ℕ => C * (Mg + ENNReal.ofReal (K / (n + 1 : ℝ)) * Mφ))
        Filter.atTop (nhds (C * (Mg + 0))) :=
      ENNReal.Tendsto.const_mul hinner (Or.inr hCtop)
    rw [add_zero] at hcm
    exact hcm
  have hliminf_bdd : Filter.atTop.liminf bdd = C * Mg := htend_bdd.liminf_eq
  -- liminf (eLpNorm gₙ 6) ≤ liminf bdd = C · Mg.
  have hliminf_le : Filter.atTop.liminf (fun n => eLpNorm (g n) 6 (volume : Measure Domain3))
      ≤ Filter.atTop.liminf bdd :=
    Filter.liminf_le_liminf (Filter.Eventually.of_forall hbound)
  calc eLpNorm (φ : Domain3 → ℂ) 6 (volume : Measure Domain3)
      ≤ Filter.atTop.liminf (fun n => eLpNorm (g n) 6 (volume : Measure Domain3)) := hfatou
    _ ≤ Filter.atTop.liminf bdd := hliminf_le
    _ = C * Mg := hliminf_bdd

/-! ### A3 infrastructure — `eLpNorm`/integral bridge and the Bessel weight -/

/-- `(eLpNorm v 2)² = ofReal (∫ ‖v x‖²)` for `MemLp v 2`. -/
private theorem eLpNorm_two_sq_eq_integral {ι : Type*} [NormedAddCommGroup ι] (v : Domain3 → ι)
    (hv : MemLp v 2 (volume : Measure Domain3)) :
    eLpNorm v 2 (volume : Measure Domain3) ^ 2
      = ENNReal.ofReal (∫ x, ‖v x‖ ^ 2 ∂(volume : Measure Domain3)) := by
  have hint : Integrable (fun x => ‖v x‖ ^ 2) (volume : Measure Domain3) :=
    (memLp_two_iff_integrable_sq_norm hv.1).mp hv
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat]
  rw [← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
  norm_num
  rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall (fun x => by positivity))]
  congr 1
  ext x
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]

/-- If `MemLp v 2` and `∫ ‖v‖² ≤ A`, then `eLpNorm v 2 ≤ ofReal (√A)`. -/
private theorem eLpNorm_two_le_sqrt {ι : Type*} [NormedAddCommGroup ι] (v : Domain3 → ι)
    (hv : MemLp v 2 (volume : Measure Domain3)) (A : ℝ) (hA : 0 ≤ A)
    (hle : ∫ x, ‖v x‖ ^ 2 ∂(volume : Measure Domain3) ≤ A) :
    eLpNorm v 2 (volume : Measure Domain3) ≤ ENNReal.ofReal (Real.sqrt A) := by
  have hsq := eLpNorm_two_sq_eq_integral v hv
  have h1 : eLpNorm v 2 (volume : Measure Domain3) ^ 2 ≤ ENNReal.ofReal (Real.sqrt A) ^ 2 := by
    rw [hsq, ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt hA]
    exact ENNReal.ofReal_le_ofReal hle
  by_contra hc
  rw [not_le] at hc
  exact absurd h1 (not_le.mpr (by gcongr))

/-- The Bessel weight `wPos ξ = (1 + ‖ξ‖²)^(1/2)` (order `s = 1`). -/
private noncomputable def wPos (ξ : Domain3) : ℝ := (1 + ‖ξ‖ ^ 2) ^ ((1 : ℝ) / 2)

/-- The inverse Bessel weight `wInv ξ = (1 + ‖ξ‖²)^(-1/2)`. -/
private noncomputable def wInv (ξ : Domain3) : ℝ := (1 + ‖ξ‖ ^ 2) ^ (-(1 : ℝ) / 2)

private theorem wPos_sq_mul_wInv_sq (ξ : Domain3) : (wPos ξ) ^ 2 * (wInv ξ) ^ 2 = 1 := by
  rw [wPos, wInv, ← Real.rpow_natCast _ 2,
    ← Real.rpow_natCast ((1 + ‖ξ‖ ^ 2) ^ (-(1 : ℝ) / 2)) 2,
    ← Real.rpow_mul (by positivity), ← Real.rpow_mul (by positivity),
    ← Real.rpow_add (by positivity)]
  norm_num

private theorem abs_wInv_le_one (ξ : Domain3) : |wInv ξ| ≤ 1 := by
  rw [wInv, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  exact Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [norm_nonneg ξ]) (by norm_num)

private theorem wPos_sq (ξ : Domain3) : (wPos ξ) ^ 2 = 1 + ‖ξ‖ ^ 2 := by
  rw [wPos, ← Real.rpow_natCast _ 2, ← Real.rpow_mul (by positivity)]
  norm_num

private theorem hasTemperateGrowth_wInv : Function.HasTemperateGrowth wInv :=
  Function.hasTemperateGrowth_one_add_norm_sq_rpow Domain3 (-(1 : ℝ) / 2)

private theorem memLp_top_ofReal_wInv :
    MemLp (fun ξ : Domain3 => ((wInv ξ : ℝ) : ℂ)) ⊤ (volume : Measure Domain3) := by
  refine memLp_top_of_bound ?_ 1 (Filter.Eventually.of_forall fun ξ => ?_)
  · exact (Complex.continuous_ofReal.comp
      hasTemperateGrowth_wInv.1.continuous).aestronglyMeasurable
  · rw [Complex.norm_real]; exact (le_of_eq (Real.norm_eq_abs _)).trans (abs_wInv_le_one ξ)

/-- `(1 + ‖ξ‖²)·‖g ξ‖²` is integrable for a Schwartz `g` (Schwartz decay dominates the quadratic
weight): dominated by `C·((1+‖ξ‖²)·‖g ξ‖)` where `C := ‖g‖_∞`. -/
private theorem integrable_one_add_normSq_schwartz (g : SchwartzMap Domain3 ℂ) :
    Integrable (fun ξ : Domain3 => (1 + ‖ξ‖ ^ 2) * ‖g ξ‖ ^ 2) (volume : Measure Domain3) := by
  set C : ℝ := SchwartzMap.seminorm ℂ 0 0 g with hCdef
  have hC : ∀ ξ, ‖g ξ‖ ≤ C := fun ξ => SchwartzMap.norm_le_seminorm ℂ g ξ
  have hdom : Integrable (fun ξ : Domain3 => C * ((1 + ‖ξ‖ ^ 2) * ‖g ξ‖))
      (volume : Measure Domain3) := by
    have h0 := g.integrable_pow_mul (volume : Measure Domain3) 0
    have h2 := g.integrable_pow_mul (volume : Measure Domain3) 2
    have hsum : Integrable (fun ξ : Domain3 => (1 + ‖ξ‖ ^ 2) * ‖g ξ‖) (volume : Measure Domain3) := by
      refine (h0.add h2).congr ?_
      filter_upwards with ξ
      simp only [Pi.add_apply, pow_zero, one_mul]; ring
    exact hsum.const_mul C
  refine hdom.mono' (Continuous.aestronglyMeasurable (by fun_prop))
    (Filter.Eventually.of_forall fun ξ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc (1 + ‖ξ‖ ^ 2) * ‖g ξ‖ ^ 2 = ‖g ξ‖ * ((1 + ‖ξ‖ ^ 2) * ‖g ξ‖) := by ring
    _ ≤ C * ((1 + ‖ξ‖ ^ 2) * ‖g ξ‖) :=
        mul_le_mul_of_nonneg_right (hC ξ) (by positivity)

/-- Gradient → weighted-Fourier bound for Schwartz `φ`:
`eLpNorm (fderiv φ) 2 ≤ ofReal (2π · √(∫ (1+‖ξ‖²)‖𝓕φ ξ‖²))`. Combines the proved Plancherel
kernel `integral_normSq_fderiv_le` (`∫‖fderiv φ‖² ≤ (2π)²∫‖ξ‖²‖𝓕φ‖²`) with `‖ξ‖² ≤ 1+‖ξ‖²`. -/
private theorem eLpNorm_fderiv_le_weighted (φ : SchwartzMap Domain3 ℂ) :
    eLpNorm (fderiv ℝ (φ : Domain3 → ℂ)) 2 (volume : Measure Domain3) ≤
      ENNReal.ofReal (2 * Real.pi *
        Real.sqrt (∫ ξ : Domain3, (1 + ‖ξ‖ ^ 2) * ‖(𝓕 φ) ξ‖ ^ 2 ∂(volume : Measure Domain3))) := by
  set W : ℝ := ∫ ξ : Domain3, (1 + ‖ξ‖ ^ 2) * ‖(𝓕 φ) ξ‖ ^ 2 ∂(volume : Measure Domain3) with hW
  have hWnn : 0 ≤ W := by
    rw [hW]; exact integral_nonneg (fun ξ => by positivity)
  have hmemLp : MemLp (fderiv ℝ (φ : Domain3 → ℂ)) 2 (volume : Measure Domain3) :=
    (SchwartzMap.fderivCLM ℝ Domain3 ℂ φ).memLp 2 (volume : Measure Domain3)
  -- A := (2π)²·W, eLpNorm ≤ ofReal(√A) = ofReal(2π√W).
  have hWint : Integrable (fun ξ : Domain3 => (1 + ‖ξ‖ ^ 2) * ‖(𝓕 φ) ξ‖ ^ 2)
      (volume : Measure Domain3) := integrable_one_add_normSq_schwartz (𝓕 φ)
  have hbound : ∫ x : Domain3, ‖fderiv ℝ (φ : Domain3 → ℂ) x‖ ^ 2 ∂(volume : Measure Domain3)
      ≤ (2 * Real.pi) ^ 2 * W := by
    refine (PlancherelKernels.integral_normSq_fderiv_le φ).trans ?_
    rw [hW, ← integral_const_mul]
    refine integral_mono ?_ (hWint.const_mul _) (fun ξ => ?_)
    · -- ∫ (2π)²‖ξ‖²‖𝓕φ‖² integrable
      have : Integrable (fun ξ : Domain3 => (1 + ‖ξ‖ ^ 2) * ‖(𝓕 φ) ξ‖ ^ 2 -
          ‖(𝓕 φ) ξ‖ ^ 2) (volume : Measure Domain3) := by
        refine hWint.sub ?_
        have := integrable_one_add_normSq_schwartz (𝓕 φ)
        exact (memLp_two_iff_integrable_sq_norm
          (𝓕 φ).continuous.aestronglyMeasurable).mp ((𝓕 φ).memLp 2 _)
      refine (this.const_mul ((2 * Real.pi) ^ 2)).congr ?_
      filter_upwards with ξ; ring
    · -- pointwise (2π)²‖ξ‖²‖𝓕φ‖² ≤ (2π)²(1+‖ξ‖²)‖𝓕φ‖²
      have : ‖ξ‖ ^ 2 ≤ 1 + ‖ξ‖ ^ 2 := by linarith
      have h2pi : (0:ℝ) ≤ (2 * Real.pi) ^ 2 := by positivity
      nlinarith [norm_nonneg ((𝓕 φ) ξ), sq_nonneg ‖(𝓕 φ) ξ‖, this]
  have hle := eLpNorm_two_le_sqrt (fderiv ℝ (φ : Domain3 → ℂ)) hmemLp ((2 * Real.pi) ^ 2 * W)
    (by positivity) hbound
  refine hle.trans (le_of_eq ?_)
  rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]

/-- The complex Bessel weight `wPosC ξ = (1 + ‖ξ‖²)^(1/2)` of order `1`. -/
private noncomputable def wPosC (ξ : Domain3) : ℂ := (((1 + ‖ξ‖ ^ 2) ^ ((1 : ℝ) / 2) : ℝ) : ℂ)

private theorem wPosC_eq_smulLeftCLM_weight :
    (fun x : Domain3 => (((1 + ‖x‖ ^ 2) ^ ((1 : ℝ) / 2) : ℝ) : ℂ)) = wPosC := rfl

private theorem hasTemperateGrowth_wPosC : Function.HasTemperateGrowth wPosC := by
  have hr : Function.HasTemperateGrowth (fun ξ : Domain3 => (1 + ‖ξ‖ ^ 2) ^ ((1 : ℝ) / 2)) :=
    Function.hasTemperateGrowth_one_add_norm_sq_rpow Domain3 ((1 : ℝ) / 2)
  exact (Complex.ofRealCLM.hasTemperateGrowth).comp hr

private theorem continuous_wPosC : Continuous wPosC := hasTemperateGrowth_wPosC.1.continuous

private theorem locallyIntegrable_wPosC_smul (g : L2C_R3) :
    LocallyIntegrable (fun ξ : Domain3 => wPosC ξ • (g : Domain3 → ℂ) ξ)
      (volume : Measure Domain3) := by
  intro x
  refine ⟨Metric.closedBall x 1, Metric.closedBall_mem_nhds x one_pos, ?_⟩
  have hK : IsCompact (Metric.closedBall x 1) := isCompact_closedBall x 1
  have hg_int : IntegrableOn (g : Domain3 → ℂ) (Metric.closedBall x 1) volume :=
    ((Lp.memLp g).locallyIntegrable (by norm_num)).integrableOn_isCompact hK
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (continuous_wPosC.continuousOn)
  have hmul : IntegrableOn (fun ξ => wPosC ξ * (g : Domain3 → ℂ) ξ)
      (Metric.closedBall x 1) volume := by
    refine hg_int.bdd_mul (c := C) ?_ ?_
    · exact (continuous_wPosC.aestronglyMeasurable).restrict
    · exact ae_restrict_of_forall_mem measurableSet_closedBall (fun y hy => hC y hy)
  simpa only [smul_eq_mul] using hmul

/-- **A3 weighted-Fourier extraction.** For `f` in the Sobolev space, the L²-Fourier transform
`𝓕 f` is a.e. equal to `wInv • f'`, where `f'` is the Sobolev (weighted) representative,
`smulLeftCLM ℂ wPos (𝓕 f) = f'`. This is the scalar adaptation of
`RellichBall.memH1_weightedL2_integrable_R`'s a.e. extraction. -/
private theorem fourier_ae_eq_wInv_smul (f : L2C_R3)
    (f' : L2C_R3)
    (hf' : TemperedDistribution.smulLeftCLM ℂ wPosC
        ((𝓕 f : L2C_R3) : TemperedDistribution Domain3 ℂ) = (f' : 𝓢'(Domain3, ℂ))) :
    ⇑(𝓕 f : L2C_R3) =ᵐ[volume] fun ξ => (wInv ξ : ℂ) • (f' : Domain3 → ℂ) ξ := by
  classical
  -- Step 1: wPosC • 𝓕f =ᵐ f' (from the distribution pairing, via du-Bois-Reymond).
  have hlhs_li : LocallyIntegrable
      (fun ξ : Domain3 => wPosC ξ • ((𝓕 f : L2C_R3) : Domain3 → ℂ) ξ)
      (volume : Measure Domain3) := locallyIntegrable_wPosC_smul (𝓕 f)
  have hrhs_li : LocallyIntegrable (f' : Domain3 → ℂ) (volume : Measure Domain3) :=
    (Lp.memLp f').locallyIntegrable (by norm_num)
  have hae : (fun ξ : Domain3 => wPosC ξ • ((𝓕 f : L2C_R3) : Domain3 → ℂ) ξ)
      =ᵐ[volume] (f' : Domain3 → ℂ) := by
    refine ae_eq_of_integral_contDiff_smul_eq hlhs_li hrhs_li ?_
    intro g g_smooth g_cpt
    have hg_supp : HasCompactSupport (Complex.ofRealCLM ∘ g) := g_cpt.comp_left rfl
    have hg_diff := Complex.ofRealCLM.contDiff.comp g_smooth
    set φ : SchwartzMap Domain3 ℂ := hg_supp.toSchwartzMap hg_diff with hφ
    have hφ_coe : (φ : Domain3 → ℂ) = fun x => ((g x : ℝ) : ℂ) := rfl
    have hpair : TemperedDistribution.smulLeftCLM ℂ wPosC
          ((𝓕 f : L2C_R3) : TemperedDistribution Domain3 ℂ) φ
        = ((f' : TemperedDistribution Domain3 ℂ) φ) := by rw [hf']
    rw [TemperedDistribution.smulLeftCLM_apply_apply,
        MeasureTheory.Lp.toTemperedDistribution_apply,
        MeasureTheory.Lp.toTemperedDistribution_apply] at hpair
    rw [show (fun x => (g x : ℝ) • (wPosC x • ((𝓕 f : L2C_R3) : Domain3 → ℂ) x))
          = fun x => ((SchwartzMap.smulLeftCLM ℂ wPosC φ) x)
              • ((𝓕 f : L2C_R3) : Domain3 → ℂ) x from ?_,
        show (fun x => (g x : ℝ) • (f' : Domain3 → ℂ) x)
          = fun x => (φ x) • (f' : Domain3 → ℂ) x from ?_]
    · exact hpair
    · funext x
      show (g x : ℝ) • (f' : Domain3 → ℂ) x = (φ x) • (f' : Domain3 → ℂ) x
      rw [hφ_coe]; simp only [Complex.real_smul, smul_eq_mul]
    · funext x
      show (g x : ℝ) • (wPosC x • ((𝓕 f : L2C_R3) : Domain3 → ℂ) x)
          = ((SchwartzMap.smulLeftCLM ℂ wPosC φ) x) • ((𝓕 f : L2C_R3) : Domain3 → ℂ) x
      rw [SchwartzMap.smulLeftCLM_apply_apply hasTemperateGrowth_wPosC, hφ_coe]
      simp only [Complex.real_smul, smul_eq_mul]; ring
  -- Step 2: multiply both sides by wInv; wInv·wPos = 1.
  filter_upwards [hae] with ξ hξ
  have hwprod : (wInv ξ : ℂ) * wPosC ξ = 1 := by
    rw [wInv, wPosC, ← Complex.ofReal_mul,
      ← Real.rpow_add (by positivity : (0:ℝ) < 1 + ‖ξ‖ ^ 2)]
    norm_num
  calc ⇑(𝓕 f : L2C_R3) ξ
      = (wInv ξ : ℂ) • (wPosC ξ • ((𝓕 f : L2C_R3) : Domain3 → ℂ) ξ) := by
        rw [smul_smul, hwprod, one_smul]
    _ = (wInv ξ : ℂ) • (f' : Domain3 → ℂ) ξ := by rw [hξ]

/-- **Value-convergence step.**  A direction-independent Schwartz sequence `φ n :=
𝓕⁻ (smulLeftCLM wInv (η n))`, built from a Schwartz approximant `η n → f'` of the Sobolev
representative `f'` of `f`, converges to `f` itself in L² (verbatim A3 Steps 0–2 + 6). Also
exposes `η`, `f'`, and the pointwise Fourier formula for `φ` in terms of `η`, since consumers
(the gradient-convergence step below, and `gns_L6_of_memH1_R3`) need all three — not just the
abstract `φ n.toLp → f` fact. -/
private theorem schwartz_seq_valueConv_of_memSobolev (f : L2C_R3)
    (hf : MemSobolev 1 2 (f : 𝓢'(Domain3, ℂ))) :
    ∃ (η : ℕ → SchwartzMap Domain3 ℂ) (f' : L2C_R3) (φ : ℕ → SchwartzMap Domain3 ℂ),
      Filter.Tendsto (fun n => (η n).toLp 2 (volume : Measure Domain3))
        Filter.atTop (nhds f') ∧
      (∀ n ξ, (𝓕 (φ n)) ξ = (wInv ξ : ℂ) • (η n) ξ) ∧
      Filter.Tendsto (fun n => (φ n).toLp 2 (volume : Measure Domain3))
        Filter.atTop (nhds f) := by
  classical
  -- Step 0: extract the Sobolev (weighted) representative `f'` of `f`, exactly as A3.
  obtain ⟨f', hf'raw⟩ :=
    TemperedDistribution.memSobolev_iff_exists_smulLeftCLM_fourier.mp hf
  have hf' : TemperedDistribution.smulLeftCLM ℂ wPosC
      ((𝓕 f : L2C_R3) : TemperedDistribution Domain3 ℂ) = (f' : 𝓢'(Domain3, ℂ)) := by
    rw [wPosC_eq_smulLeftCLM_weight] at hf'raw
    rw [← hf'raw]
    congr 1
    exact (MeasureTheory.Lp.fourier_toTemperedDistribution_eq f).symm
  have hFf_ae : ⇑(𝓕 f : L2C_R3) =ᵐ[volume] fun ξ => (wInv ξ : ℂ) • (f' : Domain3 → ℂ) ξ :=
    fourier_ae_eq_wInv_smul f f' hf'
  -- The bounded multiplier `wInv` (m-independent).
  have hwInv_mem := memLp_top_ofReal_wInv
  -- Step 1: a Schwartz sequence `η n` with `(η n).toLp 2 → f'` in L² (verbatim from A3).
  obtain ⟨η, hη⟩ : ∃ η : ℕ → SchwartzMap Domain3 ℂ,
      Filter.Tendsto (fun n => (η n).toLp 2 (volume : Measure Domain3)) Filter.atTop (nhds f') := by
    have hdr : DenseRange (SchwartzMap.toLpCLM ℝ ℂ (2 : ENNReal) (volume : Measure Domain3)) :=
      SchwartzMap.denseRange_toLpCLM (F := ℂ) ENNReal.ofNat_ne_top
    have hmem : f' ∈ closure (Set.range
        (SchwartzMap.toLpCLM ℝ ℂ (2 : ENNReal) (volume : Measure Domain3))) := hdr f'
    rw [mem_closure_iff_seq_limit] at hmem
    obtain ⟨v, hv_range, hv⟩ := hmem
    choose ψ hψ using hv_range
    refine ⟨ψ, ?_⟩
    have hveq : (fun n => (ψ n).toLp 2 (volume : Measure Domain3)) = v := by funext n; exact hψ n
    rw [hveq]; exact hv
  -- Step 2: the Schwartz approximants `φ n := 𝓕⁻ (smulLeftCLM wInv (η n))` (verbatim from A3).
  set φ : ℕ → SchwartzMap Domain3 ℂ :=
    fun n => 𝓕⁻ (SchwartzMap.smulLeftCLM ℂ wInv (η n)) with hφdef
  have hFφ : ∀ n, (𝓕 (φ n)) = SchwartzMap.smulLeftCLM ℂ wInv (η n) := fun n =>
    FourierTransform.fourier_fourierInv_eq _
  have hFφ_pt : ∀ n ξ, (𝓕 (φ n)) ξ = (wInv ξ : ℂ) • (η n) ξ := by
    intro n ξ
    rw [hFφ n, SchwartzMap.smulLeftCLM_apply_apply hasTemperateGrowth_wInv]
    simp [Complex.real_smul]
  -- a.e. coeFn of `𝓕 ((φ n).toLp)`.
  have hcoeFφ : ∀ n, ⇑(𝓕 ((φ n).toLp 2 (volume : Measure Domain3)) : L2C_R3)
      =ᵐ[volume] fun ξ => (wInv ξ : ℂ) • ((η n).toLp 2 (volume : Measure Domain3) : Domain3 → ℂ) ξ := by
    intro n
    rw [SchwartzMap.toLp_fourier_eq]
    filter_upwards [(𝓕 (φ n)).coeFn_toLp 2 (volume : Measure Domain3),
      (η n).coeFn_toLp 2 (volume : Measure Domain3)] with ξ h1 h2
    rw [h1, hFφ_pt n ξ, h2]
  -- `𝓕 f = mulBdd wInv f'` and `𝓕 ((φ n).toLp) = mulBdd wInv ((η n).toLp)` (verbatim from A3).
  have hFf_mulBdd : (𝓕 f : L2C_R3) = mulBdd wInv hwInv_mem f' := by
    apply Lp.ext
    filter_upwards [hFf_ae, mulBdd_coeFn wInv hwInv_mem f'] with ξ h1 h2
    rw [h1, h2]
  have hFφn_mulBdd : ∀ n, (𝓕 ((φ n).toLp 2 (volume : Measure Domain3)) : L2C_R3)
      = mulBdd wInv hwInv_mem ((η n).toLp 2 (volume : Measure Domain3)) := by
    intro n
    apply Lp.ext
    filter_upwards [hcoeFφ n,
      mulBdd_coeFn wInv hwInv_mem ((η n).toLp 2 (volume : Measure Domain3))] with ξ h1 h2
    rw [h1, h2]
  -- VALUE CONVERGENCE: `φ n.toLp → f` (verbatim from A3 Step 6).
  have hnorm_le : ∀ n, ‖(φ n).toLp 2 (volume : Measure Domain3) - f‖
      ≤ ‖(η n).toLp 2 (volume : Measure Domain3) - f'‖ := by
    intro n
    have hiso : ‖(φ n).toLp 2 (volume : Measure Domain3) - f‖
        = ‖(𝓕 ((φ n).toLp 2 (volume : Measure Domain3)) : L2C_R3) - (𝓕 f : L2C_R3)‖ := by
      rw [← MeasureTheory.Lp.norm_fourier_eq
        ((φ n).toLp 2 (volume : Measure Domain3) - f)]
      congr 1
      rw [show (𝓕 ((φ n).toLp 2 (volume : Measure Domain3) - f) : L2C_R3)
          = (Lp.fourierTransformₗᵢ Domain3 ℂ) ((φ n).toLp 2 (volume : Measure Domain3) - f) from rfl,
        map_sub]
      rfl
    rw [hiso, hFφn_mulBdd n, hFf_mulBdd, ← mulBdd_sub wInv hwInv_mem]
    refine (norm_mulBdd_le wInv hwInv_mem (zero_le_one) (fun ξ => abs_wInv_le_one ξ) _).trans ?_
    rw [one_mul]
  have htoLp : Filter.Tendsto (fun n => (φ n).toLp 2 (volume : Measure Domain3))
      Filter.atTop (nhds f) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have hd : Filter.Tendsto (fun n => ‖(η n).toLp 2 (volume : Measure Domain3) - f'‖)
        Filter.atTop (nhds 0) := by
      have hdist := tendsto_iff_dist_tendsto_zero.mp hη
      simpa only [dist_eq_norm] using hdist
    refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) hd
    rw [dist_eq_norm]; exact hnorm_le n
  exact ⟨η, f', φ, hη, hFφ_pt, htoLp⟩

/-! ### A3 — H¹(ℝ³; ℂ) ↪ L⁶(ℝ³; ℂ) for `MemSobolev 1 2` -/

/-- **A3 `gns_L6_of_memH1_R3` [PROVED sorry-free].**
If a complex-valued `L²(ℝ³; ℂ)` function `f` lies in the Sobolev space `H^{1,2}(ℝ³; ℂ)`
(i.e. `TemperedDistribution.MemSobolev 1 2 (f : 𝓢'(Domain3, ℂ))` via the
`Lp.instCoeDep` coercion in `TemperedDistribution.lean:178`), then `f ∈ L⁶(ℝ³; ℂ)`.

Conclusion: `MemLp (⇑f) 6 (volume : Measure Domain3)`, where `⇑f : Domain3 → ℂ` is the
a.e. representative of `f : L2C_R3 = Lp ℂ 2 (volume : Measure Domain3)`.

**Proof.**
1. Extract the Sobolev representative `f' ∈ L²` with `smulLeftCLM (1+‖·‖²)^(1/2) (𝓕 f) = f'`,
   giving `⇑(𝓕 f) =ᵐ wInv • f'` (`fourier_ae_eq_wInv_smul`).
2. Take a Schwartz sequence `ηₙ.toLp 2 → f'` (`denseRange_toLpCLM`) and set the Schwartz
   approximants `φₙ := 𝓕⁻¹(smulLeftCLM wInv ηₙ)`, so `𝓕 φₙ ξ = wInv ξ • ηₙ ξ` and
   `∫(1+‖ξ‖²)‖𝓕φₙ‖² = ‖ηₙ.toLp‖²`.
3. `gns_L6_schwartz` + `eLpNorm_fderiv_le_weighted` give `eLpNorm φₙ 6 ≤ C·2π·‖ηₙ.toLp‖`,
   uniformly `≤ C·2π·M` with `M := ‖f'‖+1` (since `‖ηₙ.toLp‖ → ‖f'‖`).
4. `φₙ.toLp → f` in L² (Fourier isometry + the bounded multiplier `mulBdd wInv`); extract an
   a.e.-convergent subsequence and apply Fatou (`Lp.eLpNorm_le_of_ae_tendsto`) to get
   `eLpNorm ⇑f 6 ≤ C·2π·M < ∞`, hence `MemLp (⇑f) 6`. -/
theorem gns_L6_of_memH1_R3
    (f : L2C_R3)
    (hf : MemSobolev 1 2 (f : 𝓢'(Domain3, ℂ))) :
    MemLp (⇑f) 6 (volume : Measure Domain3) := by
  classical
  -- Steps 0-2 (extract the Sobolev representative `f'`, a Schwartz sequence `η → f'`, the
  -- Schwartz approximants `φ n := 𝓕⁻ (smulLeftCLM wInv (η n))`) plus the L²-value-convergence
  -- `φ n.toLp → f` are IDENTICAL to `schwartz_seq_valueConv_of_memSobolev`'s construction
  -- (shared by `schwartz_h1_gradConv_aux`); reuse it rather than re-deriving both here.
  obtain ⟨η, f', φ, hη, hFφ_pt, htoLp⟩ := schwartz_seq_valueConv_of_memSobolev f hf
  -- The constants.
  set C : ENNReal := (SNormLESNormFDerivOfEqConst ℂ (volume : Measure Domain3) 2 : ENNReal) with hCdef
  set M : ℝ := ‖f'‖ + 1 with hMdef
  have hMpos : 0 ≤ M := by positivity
  -- Step 3: weighted-Fourier integral of `φ n` equals `‖(η n).toLp‖²`.
  have hWeighted : ∀ n,
      ∫ ξ : Domain3, (1 + ‖ξ‖ ^ 2) * ‖(𝓕 (φ n)) ξ‖ ^ 2 ∂(volume : Measure Domain3)
        = ‖(η n).toLp 2 (volume : Measure Domain3)‖ ^ 2 := by
    intro n
    rw [PlancherelKernels.normSq_toLp_two (η n)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    simp only []
    rw [hFφ_pt n ξ, norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs]
    have hwsq : |wInv ξ| ^ 2 = (1 + ‖ξ‖ ^ 2)⁻¹ := by
      rw [wInv, sq_abs, ← Real.rpow_natCast _ 2, ← Real.rpow_mul (by positivity)]
      norm_num
      rw [Real.rpow_neg (by positivity), Real.rpow_one]
    rw [hwsq]; field_simp
  -- Step 4: `eLpNorm (φ n) 6 ≤ ofReal (C.toReal · 2π · ‖(η n).toLp‖)`. We package the whole
  -- constant `C · ofReal (2π · ‖(η n).toLp‖)` and bound it eventually by a uniform constant.
  set Bdd : ENNReal := C * ENNReal.ofReal (2 * Real.pi * M) with hBdd
  have hL6 : ∀ n, eLpNorm (φ n : Domain3 → ℂ) 6 (volume : Measure Domain3)
      ≤ C * ENNReal.ofReal (2 * Real.pi * ‖(η n).toLp 2 (volume : Measure Domain3)‖) := by
    intro n
    refine (gns_L6_schwartz (φ n)).trans ?_
    have hgrad := eLpNorm_fderiv_le_weighted (φ n)
    rw [hWeighted n, Real.sqrt_sq (norm_nonneg _)] at hgrad
    exact mul_le_mul_left' hgrad C
  -- Step 5: `‖(η n).toLp‖ → ‖f'‖`, hence eventually `eLpNorm (φ n) 6 ≤ Bdd`.
  have hnorm_tend : Filter.Tendsto (fun n => ‖(η n).toLp 2 (volume : Measure Domain3)‖)
      Filter.atTop (nhds ‖f'‖) := (continuous_norm.tendsto f').comp hη
  have hev_le : ∀ᶠ n in Filter.atTop,
      eLpNorm (φ n : Domain3 → ℂ) 6 (volume : Measure Domain3) ≤ Bdd := by
    have hev : ∀ᶠ n in Filter.atTop, ‖(η n).toLp 2 (volume : Measure Domain3)‖ ≤ M := by
      have := hnorm_tend.eventually_le_const (show ‖f'‖ < M by rw [hMdef]; linarith)
      exact this
    filter_upwards [hev] with n hn
    refine (hL6 n).trans ?_
    rw [hBdd]
    refine mul_le_mul_left' (ENNReal.ofReal_le_ofReal ?_) C
    have hnn : 0 ≤ ‖(η n).toLp 2 (volume : Measure Domain3)‖ := norm_nonneg _
    nlinarith [Real.pi_pos, hn, hnn]
  -- Step 6: `φ n . toLp → f` in L² (`htoLp`, from the reused value-convergence step above),
  -- so an a.e.-convergent subsequence exists.
  have hL2conv : Filter.Tendsto
      (fun n => eLpNorm (⇑((φ n).toLp 2 (volume : Measure Domain3)) - ⇑f) 2
        (volume : Measure Domain3)) Filter.atTop (nhds 0) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'
      (fun n => (φ n).toLp 2 (volume : Measure Domain3)) f).mp htoLp
  -- a.e.-convergent subsequence.
  obtain ⟨ns, hns_mono, hns_ae⟩ :
      ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ ξ ∂(volume : Measure Domain3),
        Filter.Tendsto (fun i => (⇑((φ (ns i)).toLp 2 (volume : Measure Domain3))) ξ)
          Filter.atTop (nhds ((f : Domain3 → ℂ) ξ)) := by
    have htim : TendstoInMeasure (volume : Measure Domain3)
        (fun n => ⇑((φ n).toLp 2 (volume : Measure Domain3))) Filter.atTop (f : Domain3 → ℂ) := by
      refine MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num)
        (fun n => Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _) ?_
      refine hL2conv.congr (fun n => ?_)
      rfl
    exact htim.exists_seq_tendsto_ae
  -- The eventual bound transports to the subsequence.
  have hev_le_sub : ∀ᶠ i in Filter.atTop,
      eLpNorm (⇑((φ (ns i)).toLp 2 (volume : Measure Domain3))) 6 (volume : Measure Domain3)
        ≤ Bdd := by
    have htend_ns : Filter.Tendsto ns Filter.atTop Filter.atTop := hns_mono.tendsto_atTop
    filter_upwards [htend_ns.eventually hev_le] with i hi
    exact (eLpNorm_congr_ae ((φ (ns i)).coeFn_toLp 2 (volume : Measure Domain3))).le.trans hi
  -- Step 7: Fatou along the subsequence gives `eLpNorm ⇑f 6 ≤ Bdd < ∞`, hence `MemLp`.
  have hfatou : eLpNorm (⇑f) 6 (volume : Measure Domain3) ≤ Bdd :=
    MeasureTheory.Lp.eLpNorm_le_of_ae_tendsto
      (u := Filter.atTop) (f := fun i => ⇑((φ (ns i)).toLp 2 (volume : Measure Domain3)))
      hev_le_sub (fun i => Lp.aestronglyMeasurable _) hns_ae
  refine ⟨Lp.aestronglyMeasurable f, ?_⟩
  refine lt_of_le_of_lt hfatou ?_
  rw [hBdd]
  exact ENNReal.mul_lt_top (by rw [hCdef]; exact ENNReal.coe_lt_top) ENNReal.ofReal_lt_top

/-! ### A4 — density of H¹_σ(ℝ³) in L²_σ(ℝ³) -/

/-- **A4 helper.** If a complex `L²`-class `g : L2C_R3` is the `toLp` of a Schwartz function
`φ : 𝓢(Domain3, ℂ)`, then it lies in the Sobolev space `H^{1,2}` as a tempered distribution.

This is the "Schwartz ⊂ H¹" bridge: `((φ.toLp 2 volume) : 𝓢') = (φ : 𝓢')` by
`Lp.toTemperedDistribution_toLp_eq`, and every Schwartz function is in every Sobolev space by
`SchwartzMap.memSobolev`. -/
private theorem memSobolev_of_eq_schwartz_toLp
    (g : L2C_R3) (φ : SchwartzMap Domain3 ℂ)
    (hg : g = φ.toLp 2 (volume : Measure Domain3)) :
    MemSobolev 1 2 (g : 𝓢'(Domain3, ℂ)) := by
  have hcoe : (g : 𝓢'(Domain3, ℂ)) = (φ : 𝓢'(Domain3, ℂ)) := by
    rw [hg]
    exact MeasureTheory.Lp.toTemperedDistribution_toLp_eq φ
  rw [hcoe]
  exact φ.memSobolev

/-- **A4 helper, component-witness form.** A field with Schwartz component representatives
has `H¹` regularity (`memH1VF_R3`) — the same argument as `memH1VF_R3_of_isSchwartzDivFree`,
but stated on the raw component witness (no `L2Sigma_R3`/div-free wrapper): the divergence-free
hypothesis is never used in the proof, only the Schwartz-component data.

Each real component is `(ψ j).toLp 2 volume` for a Schwartz `ψ j : 𝓢(Domain3, ℝ)`; the
complex component projection `L2VF_projComponentC_R3 j` then equals `toLp` of the postcomposed
Schwartz function `(ψ j).postcompCLM RCLike.ofRealCLM : 𝓢(Domain3, ℂ)`, and
`memSobolev_of_eq_schwartz_toLp` finishes. -/
theorem memH1VF_R3_of_schwartz_components (u : L2VF_R3)
    (h : ∃ φ : Fin 3 → SchwartzMap Domain3 ℝ, ∀ j : Fin 3,
        L2VF_projComponent_R3 j u = (φ j).toLp 2 (volume : Measure Domain3)) :
    memH1VF_R3 u := by
  obtain ⟨ψ, hψ⟩ := h
  intro j
  -- The ℂ-valued Schwartz function for component `j`.
  set φ : SchwartzMap Domain3 ℂ := (ψ j).postcompCLM (RCLike.ofRealCLM (K := ℂ)) with hφ
  refine memSobolev_of_eq_schwartz_toLp _ φ ?_
  -- Both sides are `L²`-classes; compare a.e. representatives.
  apply MeasureTheory.Lp.ext_iff.mpr
  -- `⇑(L2VF_projComponentC_R3 j u) =ᵐ ofReal ∘ ⇑(L2VF_projComponent_R3 j u) =ᵐ ofReal ∘ ψ j`.
  have hLHS : (⇑(L2VF_projComponentC_R3 j u) : Domain3 → ℂ)
      =ᵐ[volume] fun a => RCLike.ofRealCLM (K := ℂ) (L2VF_projComponent_R3 j u a) := by
    simpa [L2VF_projComponentC_R3] using
      (RCLike.ofRealCLM (K := ℂ)).coeFn_compLpL (L2VF_projComponent_R3 j u)
  have hcomp : (⇑(L2VF_projComponent_R3 j u) : Domain3 → ℝ)
      =ᵐ[volume] ⇑(ψ j) := by
    rw [hψ j]; exact (ψ j).coeFn_toLp 2 (volume : Measure Domain3)
  have hRHS : (⇑(φ.toLp 2 (volume : Measure Domain3)) : Domain3 → ℂ) =ᵐ[volume] ⇑φ :=
    φ.coeFn_toLp 2 (volume : Measure Domain3)
  filter_upwards [hLHS, hcomp, hRHS] with a hL hc hR
  rw [hL, hc, hR, hφ, SchwartzMap.postcompCLM_apply]

/-- **A4 helper.** Every `IsSchwartzDivFree_R3` field has `H¹` regularity (`memH1VF_R3`).

A thin corollary of `memH1VF_R3_of_schwartz_components`: `IsSchwartzDivFree_R3 v` unfolds to
exactly the component-witness hypothesis at `u := (v : L2VF_R3)` (the divergence-free content
of `v : L2Sigma_R3` is not used). -/
theorem memH1VF_R3_of_isSchwartzDivFree
    {v : L2Sigma_R3} (hv : IsSchwartzDivFree_R3 v) :
    memH1VF_R3 (v : L2VF_R3) :=
  memH1VF_R3_of_schwartz_components (v : L2VF_R3) hv

/-! ### B6 export — Schwartz `H¹`-approximants with gradient convergence

This lemma packages the A3 approximant machinery as a public fact for use in
`EnergyClassConvection.lean` (PR-2, B6a/B6/B7). It exposes that every `MemSobolev 1 2`
element of `L2C_R3` admits Schwartz approximants converging simultaneously in L² to the
function AND to its L² weak directional derivative.

**No import cycle:** `SobolevEmbedding.lean` does NOT import `EnergyClassConvection.lean`;
the statement uses only types available here (`L2C_R3`, `SchwartzMap`, `lineDerivOpCLM`,
`MemSobolev`, `TemperedDistribution.lineDerivOp`/`memSobolev_zero_iff`) and the A3
private machinery already in this file. -/

/-! **B6 export: `schwartz_h1_gradConv`.**
For `f : L2C_R3` in the `H^{1,2}` Sobolev space and any direction `m : Domain3`,
there exists an L² weak directional derivative `g : L2C_R3` of `f` in direction `m`
(i.e. `∂_m (f : 𝓢') = (g : 𝓢')` as tempered distributions) and a Schwartz sequence
`φ : ℕ → SchwartzMap Domain3 ℂ` such that:
- `φₙ.toLp 2 → f` in L² (Schwartz approximation of `f`), and
- `(∂_m φₙ).toLp 2 → g` in L² (gradient convergence to the weak derivative).

This makes the `private` A3 Fourier-approximant `φₙ = 𝓕⁻¹(smulLeftCLM wInv ηₙ)` and the
`mulBdd wInv` multiplier publicly available for the B6a IBP argument in
`EnergyClassConvection.lean`, which needs to pass from Schwartz IBP to H¹ IBP via approximation.

**Proof plan (for prover pass):** The A3 proof of `gns_L6_of_memH1_R3` already builds the
Schwartz sequence `φₙ = 𝓕⁻¹(smulLeftCLM wInv ηₙ)` with `φₙ.toLp 2 → f` (Step 6 of A3).
For gradient convergence: `∂_m φₙ = 𝓕⁻¹(smulLeftCLM wInv (∂_m ηₙ))` (Fourier–lineDeriv
commutation), and `(∂_m ηₙ).toLp → ∂_m f'` via `lineDerivOpCLM`-continuity + `hη`;
then `mulBdd wInv` is a bounded multiplier sending `∂_m f'` to `g = mulBdd wInv (∂_m f')`,
which is the L² representative of `∂_m (f : 𝓢')` by the spectral identity
`TemperedDistribution.smulLeftCLM` + `fourier_ae_eq_wInv_smul`.  Alternatively, use
`(hf.lineDerivOp).memSobolev_zero_iff.mp` directly to extract `g` then build `φₙ` via
`denseRange_toLpCLM` applied to `g`, verifying gradient convergence via Fourier isometry. -/

/-- **Brick-1 helper.** The bounded Fourier multiplier `mLD m ξ := 2π·⟨ξ,m⟩·wInv ξ` for the
weak directional derivative in direction `m`. Its modulus is bounded by `2π‖m‖`
(`|2π⟨ξ,m⟩|·wInv ξ ≤ 2π‖m‖` since `|⟨ξ,m⟩| ≤ ‖ξ‖‖m‖` and `‖ξ‖·wInv ξ ≤ 1`). -/
private noncomputable def mLD (m : Domain3) (ξ : Domain3) : ℝ :=
  2 * Real.pi * (inner ℝ ξ m : ℝ) * wInv ξ

/-- The line-derivative multiplier is bounded by `2π‖m‖`. -/
private theorem abs_mLD_le (m : Domain3) (ξ : Domain3) : |mLD m ξ| ≤ 2 * Real.pi * ‖m‖ := by
  have hwInv_nonneg : 0 ≤ wInv ξ := Real.rpow_nonneg (by positivity) _
  -- ‖ξ‖ · wInv ξ ≤ 1, equivalently ‖ξ‖² · wInv ξ² ≤ 1.
  have hnorm_wInv : ‖ξ‖ * wInv ξ ≤ 1 := by
    have hwInvsq : (wInv ξ) ^ 2 = (1 + ‖ξ‖ ^ 2)⁻¹ := by
      rw [wInv, ← Real.rpow_natCast _ 2, ← Real.rpow_mul (by positivity)]
      norm_num
      rw [Real.rpow_neg (by positivity), Real.rpow_one]
    have hsq : (‖ξ‖ * wInv ξ) ^ 2 ≤ 1 := by
      rw [mul_pow, hwInvsq, mul_inv_le_iff₀ (by positivity), one_mul]
      nlinarith [norm_nonneg ξ]
    nlinarith [mul_nonneg (norm_nonneg ξ) hwInv_nonneg, hsq]
  show |2 * Real.pi * (inner ℝ ξ m : ℝ) * wInv ξ| ≤ 2 * Real.pi * ‖m‖
  calc |2 * Real.pi * (inner ℝ ξ m : ℝ) * wInv ξ|
      = (2 * Real.pi) * (|(inner ℝ ξ m : ℝ)| * wInv ξ) := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * Real.pi),
          abs_of_nonneg hwInv_nonneg, mul_assoc]
    _ ≤ (2 * Real.pi) * ((‖ξ‖ * ‖m‖) * wInv ξ) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine mul_le_mul_of_nonneg_right ?_ hwInv_nonneg
        exact (abs_real_inner_le_norm ξ m)
    _ = (2 * Real.pi) * (‖m‖ * (‖ξ‖ * wInv ξ)) := by ring
    _ ≤ (2 * Real.pi) * (‖m‖ * 1) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_left hnorm_wInv (norm_nonneg _)
    _ = 2 * Real.pi * ‖m‖ := by ring

/-- The line-derivative multiplier has temperate growth (product of the polynomial-growth
inner-product factor and the temperate `wInv`). -/
private theorem hasTemperateGrowth_mLD (m : Domain3) : Function.HasTemperateGrowth (mLD m) := by
  have hinner : Function.HasTemperateGrowth (fun ξ : Domain3 => (inner ℝ ξ m : ℝ)) :=
    ((innerSL ℝ).flip m).hasTemperateGrowth
  have hconst : Function.HasTemperateGrowth (fun _ : Domain3 => 2 * Real.pi) :=
    Function.HasTemperateGrowth.const _
  have h1 : Function.HasTemperateGrowth
      (fun ξ : Domain3 => 2 * Real.pi * (inner ℝ ξ m : ℝ)) :=
    hconst.mul hinner
  have h2 := h1.mul hasTemperateGrowth_wInv
  exact h2

/-- The complexified line-derivative multiplier is bounded in `L^∞`. -/
private theorem memLp_top_ofReal_mLD (m : Domain3) :
    MemLp (fun ξ : Domain3 => ((mLD m ξ : ℝ) : ℂ)) ⊤ (volume : Measure Domain3) := by
  refine memLp_top_of_bound ?_ (2 * Real.pi * ‖m‖)
    (Filter.Eventually.of_forall fun ξ => ?_)
  · exact (Complex.continuous_ofReal.comp
      (hasTemperateGrowth_mLD m).1.continuous).aestronglyMeasurable
  · rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_mLD_le m ξ

/-! ### Shared engine for Brick-1 (`schwartz_h1_gradConv` and its multi-direction export)

The `φₙ = 𝓕⁻¹(smulLeftCLM wInv ηₙ)` construction is `m`-independent, so a SINGLE Schwartz
sequence gives value-L² convergence to `f` (`schwartz_seq_valueConv_of_memSobolev`, defined
above the A3 section so `gns_L6_of_memH1_R3` can reuse it too) together with, for EVERY
direction `m`, L² convergence of `(∂_{m} φₙ).toLp` to the weak derivative `∂_m (f : 𝓢')`
(`schwartz_gradConv_of_valueConv`, below). Both public exports of `schwartz_h1_gradConv_aux`
peel off the appropriate piece. -/

/-- **Gradient-convergence step (per direction `m`).**  Given the value-convergent Schwartz
sequence `φ` from the previous step (exposed via `η`/`f'`/the pointwise Fourier formula
`hFφ_pt`), the `m`-directional derivatives `(∂_m φ n).toLp` converge in L² to a limit `g`
that agrees with the weak derivative `∂_m (f : 𝓢')`. -/
private theorem schwartz_gradConv_of_valueConv (f : L2C_R3)
    (η : ℕ → SchwartzMap Domain3 ℂ) (f' : L2C_R3) (φ : ℕ → SchwartzMap Domain3 ℂ)
    (hη : Filter.Tendsto (fun n => (η n).toLp 2 (volume : Measure Domain3))
      Filter.atTop (nhds f'))
    (hFφ_pt : ∀ n ξ, (𝓕 (φ n)) ξ = (wInv ξ : ℂ) • (η n) ξ)
    (htoLp : Filter.Tendsto (fun n => (φ n).toLp 2 (volume : Measure Domain3))
      Filter.atTop (nhds f))
    (m : Domain3) :
    ∃ (g : L2C_R3) (_ : (∂_{m} (f : 𝓢'(Domain3, ℂ))) = (g : 𝓢'(Domain3, ℂ))),
      Filter.Tendsto
        (fun n => (∂_{m} (φ n)).toLp 2 (volume : Measure Domain3))
        Filter.atTop (nhds g) := by
  -- The line-derivative multiplier `mLD m` (m-dependent).
  have hmLD_mem := memLp_top_ofReal_mLD m
  -- THE LIMIT `g := 𝓕⁻¹(Complex.I • mulBdd mLD f')` (in the L² Fourier notation).
  set g : L2C_R3 := (𝓕⁻ (Complex.I • mulBdd (mLD m) hmLD_mem f') : L2C_R3) with hgdef
  -- `𝓕 g = Complex.I • mulBdd mLD f'`.
  have hFg : (𝓕 g : L2C_R3) = Complex.I • mulBdd (mLD m) hmLD_mem f' := by
    rw [hgdef]
    exact FourierTransform.fourier_fourierInv_eq _
  -- `𝓕 ((∂_m φ n).toLp) = Complex.I • mulBdd mLD ((η n).toLp)`.
  have hFgrad : ∀ n, (𝓕 ((∂_{m} (φ n)).toLp 2 (volume : Measure Domain3)) : L2C_R3)
      = Complex.I • mulBdd (mLD m) hmLD_mem ((η n).toLp 2 (volume : Measure Domain3)) := by
    intro n
    apply Lp.ext
    rw [SchwartzMap.toLp_fourier_eq]
    have hg : (inner ℝ · m : Domain3 → ℝ).HasTemperateGrowth :=
      ((innerSL ℝ).flip m).hasTemperateGrowth
    filter_upwards [(𝓕 (∂_{m} (φ n))).coeFn_toLp 2 (volume : Measure Domain3),
      Lp.coeFn_smul Complex.I (mulBdd (mLD m) hmLD_mem ((η n).toLp 2 (volume : Measure Domain3))),
      mulBdd_coeFn (mLD m) hmLD_mem ((η n).toLp 2 (volume : Measure Domain3)),
      (η n).coeFn_toLp 2 (volume : Measure Domain3)] with ξ h1 h2 h3 h4
    rw [h1, h2, Pi.smul_apply, h3]
    -- pointwise: 𝓕(∂_m φ) ξ = 2πi⟨ξ,m⟩·wInv ξ·ηₙ ξ = I • (mLD ξ • ηₙ ξ).
    have hpt : (𝓕 (∂_{m} (φ n))) ξ = (2 * Real.pi * Complex.I) * (inner ℝ ξ m : ℝ) * (𝓕 (φ n)) ξ := by
      rw [fourier_lineDerivOp_eq (φ n) m, SchwartzMap.smul_apply,
        SchwartzMap.smulLeftCLM_apply_apply hg]
      simp only [smul_eq_mul, Complex.real_smul]; ring
    rw [hpt, hFφ_pt n ξ, h4]
    simp only [mLD, smul_eq_mul, Complex.real_smul]
    push_cast; ring
  -- GRADIENT CONVERGENCE: `(∂_m φ n).toLp → g` via Fourier isometry + continuity of mulBdd.
  have hgradtend : Filter.Tendsto
      (fun n => (∂_{m} (φ n)).toLp 2 (volume : Measure Domain3))
      Filter.atTop (nhds g) := by
    -- It suffices (Fourier isometry) to show `𝓕((∂_m φ n).toLp) → 𝓕 g`.
    have hFcont : Filter.Tendsto
        (fun n => (𝓕 ((∂_{m} (φ n)).toLp 2 (volume : Measure Domain3)) : L2C_R3))
        Filter.atTop (nhds (𝓕 g : L2C_R3)) := by
      simp_rw [hFgrad, hFg]
      -- `mulBdd mLD ((η n).toLp) → mulBdd mLD f'`, then smul by I.
      have hmul : Filter.Tendsto
          (fun n => mulBdd (mLD m) hmLD_mem ((η n).toLp 2 (volume : Measure Domain3)))
          Filter.atTop (nhds (mulBdd (mLD m) hmLD_mem f')) :=
        ((continuous_mulBdd (mLD m) hmLD_mem (by positivity)
          (fun ξ => abs_mLD_le m ξ)).tendsto f').comp hη
      exact (continuous_const_smul Complex.I).continuousAt.tendsto.comp hmul
    -- Transport back through the inverse Fourier transform (continuous on L²).
    have hback : Filter.Tendsto
        (fun n => (𝓕⁻ (𝓕 ((∂_{m} (φ n)).toLp 2 (volume : Measure Domain3)) : L2C_R3) : L2C_R3))
        Filter.atTop (nhds (𝓕⁻ (𝓕 g : L2C_R3) : L2C_R3)) :=
      ((FourierTransform.continuous_fourierInv (E := L2C_R3)).tendsto _).comp hFcont
    -- `𝓕⁻(𝓕 x) = x` for both the sequence and the limit.
    simp only [FourierTransform.fourierInv_fourier_eq] at hback
    exact hback
  -- `hg : ∂_m (f : 𝓢') = (g : 𝓢')` by UNIQUENESS of limits in the Hausdorff space `𝓢'`.
  -- Both `∂_m (φₙ.toLp : 𝓢')` (→ `∂_m (f:𝓢')`) and `((∂_m φₙ).toLp : 𝓢')` (→ `(g:𝓢')`)
  -- are the same 𝓢'-valued sequence (Schwartz `lineDerivOp`↔`toTemperedDistribution` commute).
  have hg : (∂_{m} (f : 𝓢'(Domain3, ℂ))) = (g : 𝓢'(Domain3, ℂ)) := by
    -- The continuous embedding `L² → 𝓢'`.
    set ι : L2C_R3 →L[ℂ] 𝓢'(Domain3, ℂ) :=
      MeasureTheory.Lp.toTemperedDistributionCLM ℂ (volume : Measure Domain3) 2 with hι
    have hι_apply : ∀ x : L2C_R3, ι x = (x : 𝓢'(Domain3, ℂ)) := fun x =>
      MeasureTheory.Lp.toTemperedDistributionCLM_apply x
    -- Continuous map `L² → 𝓢', x ↦ ∂_m (x : 𝓢')`.
    set D : L2C_R3 →L[ℂ] 𝓢'(Domain3, ℂ) :=
      (LineDeriv.lineDerivOpCLM ℂ 𝓢'(Domain3, ℂ) m) ∘L ι with hD
    -- `(∂_m φₙ).toLp : 𝓢'  →  (g : 𝓢')`.
    have hgrad𝓢' : Filter.Tendsto
        (fun n => ((∂_{m} (φ n)).toLp 2 (volume : Measure Domain3) : 𝓢'(Domain3, ℂ)))
        Filter.atTop (nhds (g : 𝓢'(Domain3, ℂ))) := by
      have := (ι.continuous.tendsto g).comp hgradtend
      simp only [Function.comp, hι_apply] at this
      exact this
    -- `D (φₙ.toLp) = ∂_m (φₙ.toLp : 𝓢')  →  ∂_m (f : 𝓢') = D f`.
    have hDf : Filter.Tendsto (fun n => D ((φ n).toLp 2 (volume : Measure Domain3)))
        Filter.atTop (nhds (D f)) := (D.continuous.tendsto f).comp htoLp
    -- For each n: `D (φₙ.toLp) = ((∂_m φₙ).toLp : 𝓢')`.
    have hDeq : ∀ n, D ((φ n).toLp 2 (volume : Measure Domain3))
        = ((∂_{m} (φ n)).toLp 2 (volume : Measure Domain3) : 𝓢'(Domain3, ℂ)) := by
      intro n
      rw [hD]
      simp only [ContinuousLinearMap.comp_apply, hι_apply, LineDeriv.lineDerivOpCLM_apply]
      -- ∂_m (φₙ.toLp : 𝓢') = ((∂_m φₙ).toLp : 𝓢') via Schwartz commute.
      rw [MeasureTheory.Lp.toTemperedDistribution_toLp_eq (φ n),
        TemperedDistribution.lineDerivOp_toTemperedDistributionCLM_eq,
        ← MeasureTheory.Lp.toTemperedDistribution_toLp_eq (p := (2 : ENNReal)) (∂_{m} (φ n))]
    -- `D f = ∂_m (f : 𝓢')`.
    have hDf_eq : D f = (∂_{m} (f : 𝓢'(Domain3, ℂ))) := by
      rw [hD]; simp only [ContinuousLinearMap.comp_apply, hι_apply, LineDeriv.lineDerivOpCLM_apply]
    -- Both sequences agree, so their limits agree (𝓢' is T2).
    rw [hDf_eq] at hDf
    have hgrad𝓢'' : Filter.Tendsto
        (fun n => D ((φ n).toLp 2 (volume : Measure Domain3)))
        Filter.atTop (nhds (g : 𝓢'(Domain3, ℂ))) := by
      refine hgrad𝓢'.congr (fun n => ?_); exact (hDeq n).symm
    exact tendsto_nhds_unique hDf hgrad𝓢''
  exact ⟨g, hg, hgradtend⟩

/-- Assembly: the value-convergence step feeds its witnesses into the gradient-convergence
step for every direction `m`. -/
private theorem schwartz_h1_gradConv_aux (f : L2C_R3)
    (hf : MemSobolev 1 2 (f : 𝓢'(Domain3, ℂ))) :
    ∃ φ : ℕ → SchwartzMap Domain3 ℂ,
      Filter.Tendsto (fun n => (φ n).toLp 2 (volume : Measure Domain3))
          Filter.atTop (nhds f) ∧
      ∀ m : Domain3, ∃ (g : L2C_R3)
          (_ : (∂_{m} (f : 𝓢'(Domain3, ℂ))) = (g : 𝓢'(Domain3, ℂ))),
        Filter.Tendsto
          (fun n => (∂_{m} (φ n)).toLp 2 (volume : Measure Domain3))
          Filter.atTop (nhds g) := by
  classical
  obtain ⟨η, f', φ, hη, hFφ_pt, htoLp⟩ := schwartz_seq_valueConv_of_memSobolev f hf
  exact ⟨φ, htoLp, fun m => schwartz_gradConv_of_valueConv f η f' φ hη hFφ_pt htoLp m⟩

/-- **Brick-1 (per-direction).** For `f : L2C_R3` in `H^{1,2}` and a fixed direction `m`, there
is a Schwartz sequence converging in L² to `f` whose `m`-directional derivatives converge in L²
to the weak derivative `∂_m (f : 𝓢')`. Derived from the `m`-uniform engine
`schwartz_h1_gradConv_aux`. -/
theorem schwartz_h1_gradConv (f : L2C_R3) (m : Domain3)
    (hf : MemSobolev 1 2 (f : 𝓢'(Domain3, ℂ))) :
    ∃ (g : L2C_R3)
      (_hg : (∂_{m} (f : 𝓢'(Domain3, ℂ))) = (g : 𝓢'(Domain3, ℂ)))
      (φ : ℕ → SchwartzMap Domain3 ℂ),
      Filter.Tendsto (fun n => (φ n).toLp 2 (volume : Measure Domain3))
          Filter.atTop (nhds f) ∧
      Filter.Tendsto
          (fun n => (∂_{m} (φ n)).toLp 2 (volume : Measure Domain3))
          Filter.atTop (nhds g) := by
  obtain ⟨φ, htoLp, hm⟩ := schwartz_h1_gradConv_aux f hf
  obtain ⟨g, hg, hgradtend⟩ := hm m
  exact ⟨g, hg, φ, htoLp, hgradtend⟩

/-! **B6 export: `schwartz_h1_gradConv_multi`.**
For `f : L2C_R3` in the `H^{1,2}` Sobolev space, there exists a SINGLE Schwartz sequence
`φ : ℕ → SchwartzMap Domain3 ℂ` that simultaneously:
- converges in L² to `f` (value convergence), and
- for EVERY direction `m : Domain3`, the sequence of directional derivatives `(∂_{m} φₙ).toLp 2`
  converges in L² to the weak derivative `∂_m (f : 𝓢')`.

The outer `∃ φ` and inner `∀ m` ordering is the key distinction from `schwartz_h1_gradConv`,
which provides only a per-direction sequence (one per `m`). Here the SAME sequence works for all
directions simultaneously (the `φₙ = 𝓕⁻¹(smulLeftCLM wInv ηₙ)` construction is m-independent).

**Proof plan (prover pass):** Take the same `φₙ = 𝓕⁻¹(smulLeftCLM wInv ηₙ)` built in
`schwartz_h1_gradConv`. The value convergence `φₙ.toLp → f` is identical. For each `m`,
the gradient convergence `(∂_{m} φₙ).toLp → g` and the identity `∂_m (f : 𝓢') = (g : 𝓢')`
follow from the same multiplier argument as in `schwartz_h1_gradConv` — the construction of `φₙ`
never depended on `m`, so the conclusion holds for all `m` uniformly. -/
/-- **B6 export.** A single Schwartz sequence converges in `L²` to `f ∈ H^{1,2}` and,
simultaneously for every direction `m`, has directional-derivative sequence converging in `L²`
to the weak derivative `∂_m f` — the multi-directional strengthening of `schwartz_h1_gradConv`
(see the section note above for the construction). -/
theorem schwartz_h1_gradConv_multi (f : L2C_R3)
    (hf : MemSobolev 1 2 (f : 𝓢'(Domain3, ℂ))) :
    ∃ φ : ℕ → SchwartzMap Domain3 ℂ,
      Filter.Tendsto (fun n => (φ n).toLp 2 (volume : Measure Domain3))
          Filter.atTop (nhds f) ∧
      ∀ m : Domain3, ∃ (g : L2C_R3)
          (_hg : (∂_{m} (f : 𝓢'(Domain3, ℂ))) = (g : 𝓢'(Domain3, ℂ))),
        Filter.Tendsto
          (fun n => (∂_{m} (φ n)).toLp 2 (volume : Measure Domain3))
          Filter.atTop (nhds g) := by
  exact schwartz_h1_gradConv_aux f hf

/-! ### Public H¹ membership from finite weighted-Fourier integrand

This lemma exposes the bridge from the **pointwise viscous spectral integrand**
`∫⁻ (2π)²‖ξ‖²‖𝓕(projⱼ w) ξ‖²` being finite (for each component `j`) to
`memH1VF_R3 w`, making the private Bessel-weight machinery available to callers
(in particular `AubinLionsLimitPassage.lean`) without duplicating the ~100 LOC
du-Bois-Reymond / `smulLeftCLM` construction.

The hypothesis is the unfolded definition of `viscousLintegrand_j j w` in
`AubinLionsLimitPassage.lean`; callers `rw [viscousLintegrand_j]` to expose it. -/

/-- **H¹ membership from finite weighted-Fourier integral.**
If for each component `j : Fin 3` the lower Lebesgue integral
`∫⁻ ξ, (2π)²‖ξ‖² ‖𝓕(projⱼ w) ξ‖² dξ` is finite, then `w` lies in `H¹(ℝ³; ℝ³)`,
i.e. `memH1VF_R3 w`.

**Proof plan (for prover pass):**
For each `j`, finiteness of the lintegral gives `MemLp (fun ξ => wPosC ξ • (𝓕(projⱼ w) ξ)) 2`:
- `‖wPosC ξ‖² · ‖𝓕(projⱼ w) ξ‖² = (1+‖ξ‖²) · ‖𝓕(projⱼ w) ξ‖²`
  `≤ ‖𝓕(projⱼ w) ξ‖² + (1/(2π)²) · (2π)²‖ξ‖²‖𝓕(projⱼ w) ξ‖²`,
  so `∫⁻ ‖wPosC ξ • (𝓕(projⱼ w) ξ)‖² < ∞` by the hypothesis plus `𝓕(projⱼ w) ∈ L²`.
- `MemLp ... 2` gives via `ae_eq_of_integral_contDiff_smul_eq` + `locallyIntegrable_wPosC_smul`
  that `smulLeftCLM ℂ wPosC (𝓕 (projⱼ w)) = f'` for some `f' ∈ L²` (the `wPosC_eq_smulLeftCLM_weight`
  reconciliation as in `gns_L6_of_memH1_R3`).
- Apply `memSobolev_iff_exists_smulLeftCLM_fourier.mpr` to conclude `MemSobolev 1 2 (projⱼ w)`.
- Universally quantify over `j` to obtain `memH1VF_R3 w`. -/
theorem memSobolev_of_finite_weightedFourier_R3 (w : L2VF_R3)
    (h : ∀ j : Fin 3,
      ∫⁻ ξ : Domain3, ENNReal.ofReal ((2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 *
        ‖(𝓕 (L2VF_projComponentC_R3 j w) : L2C_R3) ξ‖ ^ 2)
        ∂(volume : Measure Domain3) < ⊤) :
    memH1VF_R3 w := by
  classical
  intro j
  set g : L2C_R3 := (𝓕 (L2VF_projComponentC_R3 j w) : L2C_R3) with hg
  -- Step 1: `wPosC • g ∈ MemLp 2`.  `‖wPosC ξ • g ξ‖² = (1+‖ξ‖²)‖g ξ‖²
  --   = ‖g ξ‖² + (1/(2π)²)·(2π)²‖ξ‖²‖g ξ‖²`, both `lintegral`-finite (`g ∈ L²` + hypothesis).
  have hmemLp : MemLp (fun ξ : Domain3 => wPosC ξ • (g : Domain3 → ℂ) ξ) 2
      (volume : Measure Domain3) := by
    have haesm : AEStronglyMeasurable (fun ξ : Domain3 => wPosC ξ • (g : Domain3 → ℂ) ξ)
        (volume : Measure Domain3) :=
      (continuous_wPosC.aestronglyMeasurable).smul (Lp.aestronglyMeasurable g)
    refine (memLp_two_iff_integrable_sq_norm haesm).mpr ?_
    -- `‖wPosC ξ • g ξ‖² = (1+‖ξ‖²)‖g ξ‖²`.
    have hpt : ∀ ξ, ‖wPosC ξ • (g : Domain3 → ℂ) ξ‖ ^ 2 = (1 + ‖ξ‖ ^ 2) * ‖(g : Domain3 → ℂ) ξ‖ ^ 2 := by
      intro ξ
      rw [norm_smul, mul_pow]
      congr 1
      rw [wPosC, Complex.norm_real, Real.norm_eq_abs, sq_abs,
        ← Real.rpow_natCast _ 2, ← Real.rpow_mul (by positivity)]
      norm_num
    -- integrability via the two pieces.
    have hg_sq : Integrable (fun ξ : Domain3 => ‖(g : Domain3 → ℂ) ξ‖ ^ 2) volume :=
      (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable g)).mp (Lp.memLp g)
    -- the scaled weighted integrand `(2π)²‖ξ‖²‖g‖²` is `lintegral`-finite (hypothesis) + nonneg ⟹ integrable.
    have hscaled_int : Integrable
        (fun ξ : Domain3 => (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 * ‖(g : Domain3 → ℂ) ξ‖ ^ 2) volume := by
      have hjle := h j
      rw [← hg] at hjle
      refine ⟨((continuous_const.mul (continuous_norm.pow 2)).aemeasurable.mul
        ((Lp.aestronglyMeasurable g).aemeasurable.norm.pow_const 2)).aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (fun ξ => by positivity))]
      exact hjle
    have hweighted_int : Integrable (fun ξ : Domain3 => ‖ξ‖ ^ 2 * ‖(g : Domain3 → ℂ) ξ‖ ^ 2) volume := by
      have := hscaled_int.const_mul ((2 * Real.pi) ^ 2)⁻¹
      refine this.congr ?_
      filter_upwards with ξ
      rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
    -- assemble: `(1+‖ξ‖²)‖g‖² = ‖g‖² + ‖ξ‖²‖g‖²`.
    refine (hg_sq.add hweighted_int).congr ?_
    filter_upwards with ξ
    simp only [Pi.add_apply, hpt ξ]; ring
  -- Step 2: build the Sobolev representative `f' := toLp (wPosC • g)`.
  set f' : L2C_R3 := hmemLp.toLp _ with hf'
  -- Step 3: `smulLeftCLM ℂ wPosC (𝓕 …) = (f' : 𝓢')` (du-Bois-Reymond is unnecessary: pair equality).
  rw [TemperedDistribution.memSobolev_iff_exists_smulLeftCLM_fourier]
  refine ⟨f', ?_⟩
  -- reconcile the weight `(1+‖·‖²)^(1/2)` with `wPosC`, and `𝓕 (toTempDist (proj w)) = toTempDist g`.
  rw [wPosC_eq_smulLeftCLM_weight, MeasureTheory.Lp.fourier_toTemperedDistribution_eq
    (L2VF_projComponentC_R3 j w), ← hg]
  -- the two distributions agree: both pair as `∫ (smulLeftCLM_S φ) · g` resp `∫ φ · (wPosC•g)`.
  ext φ
  rw [TemperedDistribution.smulLeftCLM_apply_apply, MeasureTheory.Lp.toTemperedDistribution_apply,
    MeasureTheory.Lp.toTemperedDistribution_apply]
  refine integral_congr_ae ?_
  filter_upwards [hmemLp.coeFn_toLp] with ξ hξ
  show (SchwartzMap.smulLeftCLM ℂ wPosC φ) ξ • (g : Domain3 → ℂ) ξ
      = (φ ξ) • (f' : Domain3 → ℂ) ξ
  rw [SchwartzMap.smulLeftCLM_apply_apply hasTemperateGrowth_wPosC, hξ]
  simp only [smul_smul, smul_eq_mul]
  ring

end LerayHopf
