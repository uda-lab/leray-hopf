import LerayHopf.R3.Regularity
import LerayHopf.R3.ConvectionForm
-- ConvectionForm import justification (A4): provides the proved density theorem
-- `schwartzDivFree_dense_of_curlDense` and (transitively, via `CurlDensityCapstone`)
-- `curlSchwartzDense_holds`, both required by `h1Sigma_dense_in_L2Sigma`.
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
  Proof plan: approximate by Schwartz → truncate to Cc¹ → apply A2 → dominated convergence.
  **Must-prove (A3), body `-- ALLOW_SORRY: PR-1 must-prove (A3), prover pass`.**

- **A4** `h1Sigma_dense_in_L2Sigma` — elements of `L2Sigma_R3` satisfying `memH1VF_R3`
  are dense in `L2Sigma_R3`.
  Proof plan: Schwartz ⊂ H¹ + `schwartzDivFree_dense_of_curlDense` + `curlSchwartzDense_holds`.
  **Must-prove (A4), body `-- ALLOW_SORRY: PR-1 must-prove (A4), prover pass`.**

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

**Status (prover pass):** A2 (`gns_L6_cc1_R3`) and A4 (`h1Sigma_dense_in_L2Sigma`) are
PROVED sorry-free. A3 (`gns_L6_of_memH1_R3`) retains its `-- ALLOW_SORRY` body, but its
**analytic core is now proved sorry-free** in the four `private` kernels preceding A3
(`opNorm_le_sqrt_sum_sq`, `normSq_toLp_two`, `normSq_lineDeriv_toLp`,
`integral_normSq_fderiv_le`), which establish the gradient↔Fourier Plancherel control
`∫ ‖fderiv φ x‖² ≤ (2π)² ∫ ‖ξ‖² ‖𝓕 φ ξ‖²` for Schwartz `φ : 𝓢(ℝ³, ℂ)`. What remains for A3
is the *assembly*: (i) scalar H¹⇒weighted-L² for `f` (a direct adaptation of the PROVED
`RellichBall.memH1_weightedL2_integrable_R`); (ii) GNS-for-Schwartz via smooth-cutoff
truncation to Cc¹ + A2 + DCT — blocked on mathlib's `ContDiffBump` exposing no gradient-norm
bound, so an explicit radial cutoff with hand-proved `‖∇χ_R‖_∞ = O(1/R)` is required;
(iii) the Schwartz `H¹`-approximating sequence via the Fourier construction
`φₙ = 𝓕⁻¹(smulLeftCLM (1+‖ξ‖²)^(-1/2) ηₙ)`; (iv) a local Fatou replicating
`MeasureTheory.eLpNorm_lim_le_liminf_eLpNorm` from the transitively-available
`lintegral_liminf_le`. The mathlib obstacle is that every GNS variant in
`SobolevInequality.lean` requires `HasCompactSupport`, and `MemSobolev 1 2` is defined purely
via Fourier multipliers — so the compactly-supported approximant with controlled gradient
must be built by hand.
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

/-! ### A3 infrastructure — Schwartz gradient↔Fourier Plancherel kernels

These four `private` lemmas establish the **gradient–Fourier Plancherel control** for a
complex-valued Schwartz function `φ : 𝓢(ℝ³, ℂ)`, the analytic heart of the GNS embedding:

  `∫ ‖fderiv ℝ φ x‖² dx ≤ (2π)² ∫ ‖ξ‖² ‖𝓕 φ ξ‖² dξ`.

The chain is:
- `opNorm_le_sqrt_sum_sq`  — the operator norm of a real-linear functional `L : ℝ³ →L[ℝ] ℂ`
  is bounded by the Euclidean (Hilbert–Schmidt) norm `√(∑ⱼ ‖L eⱼ‖²)` of its gradient covector
  (Cauchy–Schwarz; **the `≤` direction — the reverse equality is FALSE for ℂ-codomain**).
- `normSq_toLp_two`        — `‖g.toLp 2‖² = ∫ ‖g ξ‖²` for Schwartz `g` (via `inner_toL2_toL2_eq`).
- `normSq_lineDeriv_toLp`  — per-direction Schwartz Plancherel:
  `‖(∂_{m}φ).toLp 2‖² = ∫ (2π)² ⟨ξ,m⟩² ‖𝓕 φ ξ‖²` (via `fourier_lineDerivOp_eq` + Plancherel).
- `integral_normSq_fderiv_le` — integrate the HS bound and sum over the standard basis
  (`∑ⱼ ⟨ξ,eⱼ⟩² = ‖ξ‖²`) to get the displayed inequality. -/

open FourierTransform
open scoped Real LineDeriv RealInnerProductSpace FourierTransform

/-- **A3 kernel.** Operator norm of a real-linear functional `L : Domain3 →L[ℝ] ℂ` is bounded
by the Euclidean norm `√(∑ᵢ ‖L (b i)‖²)` of its gradient covector, for any orthonormal basis `b`.
This is the Hilbert–Schmidt bound `‖L‖_op ≤ ‖L‖_HS`; the reverse inequality is false for a
ℂ-valued (rank-2) codomain, so only `≤` holds — which is the direction the GNS upper bound needs. -/
private theorem opNorm_le_sqrt_sum_sq {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ Domain3) (L : Domain3 →L[ℝ] ℂ) :
    ‖L‖ ≤ Real.sqrt (∑ i, ‖L (b i)‖ ^ 2) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro v
  have hn1 : (0:ℝ) ≤ ∑ i, ⟪b i, v⟫ ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hv : L v = ∑ i, ⟪b i, v⟫ • L (b i) := by
    conv_lhs => rw [← b.sum_repr' v]
    rw [map_sum]; simp [map_smul]
  rw [hv, mul_comm]
  calc ‖∑ i, ⟪b i, v⟫ • L (b i)‖
      ≤ ∑ i, ‖⟪b i, v⟫ • L (b i)‖ := norm_sum_le _ _
    _ = ∑ i, |⟪b i, v⟫| * ‖L (b i)‖ := by simp [norm_smul, Real.norm_eq_abs]
    _ ≤ Real.sqrt ((∑ i, ⟪b i, v⟫ ^ 2) * (∑ i, ‖L (b i)‖ ^ 2)) := by
        apply Real.le_sqrt_of_sq_le
        calc (∑ i, |⟪b i, v⟫| * ‖L (b i)‖) ^ 2
            ≤ (∑ i, |⟪b i, v⟫| ^ 2) * (∑ i, ‖L (b i)‖ ^ 2) := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
          _ = (∑ i, ⟪b i, v⟫ ^ 2) * (∑ i, ‖L (b i)‖ ^ 2) := by simp [sq_abs]
    _ = ‖v‖ * Real.sqrt (∑ i, ‖L (b i)‖ ^ 2) := by
        rw [Real.sqrt_mul hn1]
        congr 1
        have hvn : ∑ i, ⟪b i, v⟫ ^ 2 = ‖v‖ ^ 2 := by
          have := b.sum_sq_norm_inner_right v
          simpa [Real.norm_eq_abs, sq_abs] using this
        rw [hvn, Real.sqrt_sq (norm_nonneg _)]

/-- **A3 kernel.** For a Schwartz `g : 𝓢(ℝ³, ℂ)`, the squared `L²`-class norm is the integral of
the pointwise squared norm: `‖g.toLp 2‖² = ∫ ‖g ξ‖²`. (Via `SchwartzMap.inner_toL2_toL2_eq`.) -/
private theorem normSq_toLp_two (g : SchwartzMap Domain3 ℂ) :
    ‖g.toLp 2 (volume : Measure Domain3)‖ ^ 2
      = ∫ ξ : Domain3, ‖g ξ‖ ^ 2 ∂(volume : Measure Domain3) := by
  have hII : inner ℂ (g.toLp 2 (volume : Measure Domain3)) (g.toLp 2 (volume : Measure Domain3))
      = ∫ x, inner ℂ (g x) (g x) ∂(volume : Measure Domain3) := SchwartzMap.inner_toL2_toL2_eq g g _
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), hII, ← integral_re]
  · refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    show RCLike.re (inner ℂ (g ξ) (g ξ)) = ‖g ξ‖ ^ 2
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  · refine (L2.integrable_inner (g.toLp 2 (volume:Measure Domain3))
      (g.toLp 2 (volume:Measure Domain3))).congr ?_
    filter_upwards [g.coeFn_toLp 2 (volume:Measure Domain3)] with x hx; rw [hx]

/-- **A3 kernel.** Per-direction Schwartz Plancherel: for `φ : 𝓢(ℝ³, ℂ)` and a direction `m`,
`‖(∂_{m}φ).toLp 2‖² = ∫ (2π)² ⟨ξ,m⟩² ‖𝓕 φ ξ‖²`. Uses `fourier_lineDerivOp_eq`
(`𝓕(∂_{m}φ) = 2πi⟨·,m⟩ 𝓕 φ`) + Plancherel (`norm_fourier_toL2_eq`) + `normSq_toLp_two`. -/
private theorem normSq_lineDeriv_toLp (φ : SchwartzMap Domain3 ℂ) (m : Domain3) :
    ‖(∂_{m} φ).toLp 2 (volume : Measure Domain3)‖ ^ 2
      = ∫ ξ : Domain3, (2 * Real.pi) ^ 2 * (inner ℝ ξ m) ^ 2 * ‖(𝓕 φ) ξ‖ ^ 2
        ∂(volume : Measure Domain3) := by
  rw [← norm_fourier_toL2_eq, normSq_toLp_two]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  show ‖(𝓕 (∂_{m} φ)) ξ‖ ^ 2 = (2 * Real.pi) ^ 2 * (inner ℝ ξ m) ^ 2 * ‖(𝓕 φ) ξ‖ ^ 2
  have hg : (inner ℝ · m : Domain3 → ℝ).HasTemperateGrowth :=
    ((innerSL ℝ).flip m).hasTemperateGrowth
  have hpt : (𝓕 (∂_{m} φ)) ξ = (2 * Real.pi * Complex.I) * (inner ℝ ξ m : ℝ) * (𝓕 φ) ξ := by
    rw [fourier_lineDerivOp_eq φ m, SchwartzMap.smul_apply, SchwartzMap.smulLeftCLM_apply_apply hg]
    simp only [smul_eq_mul, Complex.real_smul]; ring
  rw [hpt, norm_mul, norm_mul, mul_pow, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hI : ‖(2 * Real.pi * Complex.I)‖ = 2 * Real.pi := by
    rw [show (2 * Real.pi * Complex.I) = ((2 * Real.pi : ℝ) : ℂ) * Complex.I by push_cast; ring]
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
  rw [hI]

/-- **A3 kernel.** Integrated gradient–Fourier bound for Schwartz `φ`:
`∫ ‖fderiv ℝ φ x‖² ≤ (2π)² ∫ ‖ξ‖² ‖𝓕 φ ξ‖²`.  Combine the pointwise HS bound
(`opNorm_le_sqrt_sum_sq`, squared) with the summed per-direction Plancherel
(`normSq_lineDeriv_toLp`) over the standard basis (`∑ᵢ ⟨ξ,eᵢ⟩² = ‖ξ‖²`). -/
private theorem integral_normSq_fderiv_le (φ : SchwartzMap Domain3 ℂ) :
    ∫ x : Domain3, ‖fderiv ℝ φ x‖ ^ 2 ∂(volume : Measure Domain3)
      ≤ ∫ ξ : Domain3, (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 * ‖(𝓕 φ) ξ‖ ^ 2 ∂(volume : Measure Domain3) := by
  set b := stdOrthonormalBasis ℝ Domain3 with hb
  have hptwise : ∀ x : Domain3,
      ‖fderiv ℝ φ x‖ ^ 2 ≤ ∑ i, ‖(∂_{b i} φ) x‖ ^ 2 := by
    intro x
    have h := opNorm_le_sqrt_sum_sq b (fderiv ℝ (φ : Domain3 → ℂ) x)
    have hsum_nonneg : (0:ℝ) ≤ ∑ i, ‖(fderiv ℝ (φ:Domain3→ℂ) x) (b i)‖ ^ 2 :=
      Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have heq : (∑ i, ‖(fderiv ℝ (φ:Domain3→ℂ) x) (b i)‖ ^ 2) = ∑ i, ‖(∂_{b i} φ) x‖ ^ 2 := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv]
    have hle : ‖fderiv ℝ (φ:Domain3→ℂ) x‖ ^ 2 ≤ ∑ i, ‖(fderiv ℝ (φ:Domain3→ℂ) x) (b i)‖ ^ 2 := by
      calc ‖fderiv ℝ (φ:Domain3→ℂ) x‖ ^ 2
          ≤ (Real.sqrt (∑ i, ‖(fderiv ℝ (φ:Domain3→ℂ) x) (b i)‖ ^ 2)) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) h 2
        _ = ∑ i, ‖(fderiv ℝ (φ:Domain3→ℂ) x) (b i)‖ ^ 2 := Real.sq_sqrt hsum_nonneg
    rw [heq] at hle
    exact hle
  have hintL : Integrable (fun x : Domain3 => ‖fderiv ℝ (φ:Domain3→ℂ) x‖ ^ 2)
      (volume : Measure Domain3) :=
    (memLp_two_iff_integrable_sq_norm
      ((SchwartzMap.fderivCLM ℝ Domain3 ℂ φ).continuous.aestronglyMeasurable)).mp
      ((SchwartzMap.fderivCLM ℝ Domain3 ℂ φ).memLp 2 (volume:Measure Domain3))
  have hintR : ∀ i, Integrable (fun x : Domain3 => ‖(∂_{b i} φ) x‖ ^ 2)
      (volume : Measure Domain3) := fun i =>
    (memLp_two_iff_integrable_sq_norm ((∂_{b i} φ).continuous.aestronglyMeasurable)).mp
      ((∂_{b i} φ).memLp 2 (volume:Measure Domain3))
  have hsumint : Integrable (fun x : Domain3 => ∑ i, ‖(∂_{b i} φ) x‖ ^ 2)
      (volume : Measure Domain3) := integrable_finset_sum _ (fun i _ => hintR i)
  have hstep1 : ∫ x : Domain3, ‖fderiv ℝ (φ:Domain3→ℂ) x‖ ^ 2 ∂(volume : Measure Domain3)
      ≤ ∫ x : Domain3, ∑ i, ‖(∂_{b i} φ) x‖ ^ 2 ∂(volume : Measure Domain3) :=
    integral_mono hintL hsumint hptwise
  have hstep2 : ∫ x : Domain3, ∑ i, ‖(∂_{b i} φ) x‖ ^ 2 ∂(volume : Measure Domain3)
      = ∫ ξ : Domain3, (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 * ‖(𝓕 φ) ξ‖ ^ 2 ∂(volume : Measure Domain3) := by
    rw [integral_finset_sum _ (fun i _ => hintR i)]
    have hperdir : ∀ i, ∫ x : Domain3, ‖(∂_{b i} φ) x‖ ^ 2 ∂(volume : Measure Domain3)
        = ∫ ξ : Domain3, (2 * Real.pi)^2 * (inner ℝ ξ (b i))^2 * ‖(𝓕 φ) ξ‖^2
          ∂(volume:Measure Domain3) := by
      intro i
      rw [← normSq_toLp_two (∂_{b i} φ), normSq_lineDeriv_toLp]
    simp_rw [hperdir]
    have hintP : ∀ i, Integrable
        (fun ξ : Domain3 => (2 * Real.pi)^2 * (inner ℝ ξ (b i))^2 * ‖(𝓕 φ) ξ‖^2)
        (volume : Measure Domain3) := by
      intro i
      have hFR : Integrable (fun ξ : Domain3 => ‖(𝓕 (∂_{b i} φ)) ξ‖^2)
          (volume : Measure Domain3) :=
        (memLp_two_iff_integrable_sq_norm
          ((𝓕 (∂_{b i} φ)).continuous.aestronglyMeasurable)).mp
          ((𝓕 (∂_{b i} φ)).memLp 2 (volume:Measure Domain3))
      refine hFR.congr ?_
      filter_upwards with ξ
      have hg : (inner ℝ · (b i) : Domain3 → ℝ).HasTemperateGrowth :=
        ((innerSL ℝ).flip (b i)).hasTemperateGrowth
      have hpt : (𝓕 (∂_{b i} φ)) ξ
          = (2 * Real.pi * Complex.I) * (inner ℝ ξ (b i) : ℝ) * (𝓕 φ) ξ := by
        rw [fourier_lineDerivOp_eq φ (b i), SchwartzMap.smul_apply, SchwartzMap.smulLeftCLM_apply_apply hg]
        simp only [smul_eq_mul, Complex.real_smul]; ring
      rw [hpt, norm_mul, norm_mul, mul_pow, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      have hI : ‖(2 * Real.pi * Complex.I)‖ = 2 * Real.pi := by
        rw [show (2 * Real.pi * Complex.I) = ((2 * Real.pi : ℝ) : ℂ) * Complex.I by push_cast; ring]
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (by positivity)]
      rw [hI]
    rw [← integral_finset_sum _ (fun i _ => hintP i)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    have hinner : ∑ i, (inner ℝ ξ (b i))^2 = ‖ξ‖^2 := by
      have := b.sum_sq_norm_inner_right ξ
      simp_rw [real_inner_comm] at this ⊢
      simpa [Real.norm_eq_abs, sq_abs] using this
    calc ∑ i, (2 * Real.pi)^2 * (inner ℝ ξ (b i))^2 * ‖(𝓕 φ) ξ‖^2
        = ((2 * Real.pi)^2 * ‖(𝓕 φ) ξ‖^2) * ∑ i, (inner ℝ ξ (b i))^2 := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => by ring)
      _ = (2 * Real.pi)^2 * ‖ξ‖^2 * ‖(𝓕 φ) ξ‖^2 := by rw [hinner]; ring
  rw [hstep2] at hstep1
  exact hstep1

/-! ### A3 — H¹(ℝ³; ℂ) ↪ L⁶(ℝ³; ℂ) for `MemSobolev 1 2` -/

/-- **A3 `gns_L6_of_memH1_R3` [must-prove — CODEX REVIEW REQUIRED before proving].**
If a complex-valued `L²(ℝ³; ℂ)` function `f` lies in the Sobolev space `H^{1,2}(ℝ³; ℂ)`
(i.e. `TemperedDistribution.MemSobolev 1 2 (f : 𝓢'(Domain3, ℂ))` via the
`Lp.instCoeDep` coercion in `TemperedDistribution.lean:178`), then `f ∈ L⁶(ℝ³; ℂ)`.

Conclusion: `MemLp (⇑f) 6 (volume : Measure Domain3)`, where `⇑f : Domain3 → ℂ` is the
a.e. representative of `f : L2C_R3 = Lp ℂ 2 (volume : Measure Domain3)`.

**Proof plan (for prover pass):**
1. Schwartz functions are dense in `L²(ℝ³; ℂ)` by `SchwartzMap.denseRange_toLpCLM`.
2. Each Schwartz function `φ : 𝓢(Domain3, ℂ)` is smooth and compactly supported after
   a bump-function truncation (`HasCompactSupport` + `ContDiff ℝ 1`).
3. Apply A2 (`gns_L6_cc1_R3`) to the truncated approximants → L⁶ norm bounds uniform in f.
4. Dominated convergence / lower-semicontinuity of `eLpNorm _ 6 volume` closes. -/
theorem gns_L6_of_memH1_R3
    (f : L2C_R3)
    (hf : MemSobolev 1 2 (f : 𝓢'(Domain3, ℂ))) :
    MemLp (⇑f) 6 (volume : Measure Domain3) := by
  sorry -- ALLOW_SORRY: PR-1 must-prove (A3). Analytic CORE proved sorry-free (the four `integral_normSq_fderiv_le`-chain kernels above: gradient↔Fourier Plancherel `∫‖fderiv φ‖² ≤ (2π)²∫‖ξ‖²‖φ̂‖²`). Remaining assembly NOT yet built sorry-free: (1) scalar H¹⇒weighted-L² for f [direct adaptation of the PROVED RellichBall.memH1_weightedL2_integrable_R, replacing the projected component by f]; (2) GNS-for-Schwartz `eLpNorm φ 6 ≤ C·eLpNorm(fderiv φ) 2` via smooth-cutoff truncation to Cc¹ + A2 + DCT — BLOCKER: mathlib's `ContDiffBump` exposes no gradient-norm bound (`‖fderiv χ_R‖`), so an explicit radial cutoff with hand-proved `‖∇χ_R‖_∞ = O(1/R)` must be constructed; (3) Schwartz φₙ→f in L² with `∫‖ξ‖²‖φ̂ₙ‖²` bounded via φₙ=𝓕⁻¹(smulLeftCLM (1+‖ξ‖²)^(-1/2) ηₙ), ηₙ→(1+‖ξ‖²)^(1/2)𝓕f in L² [construction typechecks]; (4) Fatou: replicate `MeasureTheory.eLpNorm_lim_le_liminf_eLpNorm` locally via the transitively-available `lintegral_liminf_le` (LpSpace/Complete.lean not imported here).

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

/-- **A4 helper.** Every `IsSchwartzDivFree_R3` field has `H¹` regularity (`memH1VF_R3`).

Each real component is `(ψ j).toLp 2 volume` for a Schwartz `ψ j : 𝓢(Domain3, ℝ)`; the
complex component projection `L2VF_projComponentC_R3 j` then equals `toLp` of the postcomposed
Schwartz function `(ψ j).postcompCLM RCLike.ofRealCLM : 𝓢(Domain3, ℂ)`, and
`memSobolev_of_eq_schwartz_toLp` finishes. -/
private theorem memH1VF_R3_of_isSchwartzDivFree
    {v : L2Sigma_R3} (hv : IsSchwartzDivFree_R3 v) :
    memH1VF_R3 (v : L2VF_R3) := by
  obtain ⟨ψ, hψ⟩ := hv
  intro j
  -- The ℂ-valued Schwartz function for component `j`.
  set φ : SchwartzMap Domain3 ℂ := (ψ j).postcompCLM (RCLike.ofRealCLM (K := ℂ)) with hφ
  refine memSobolev_of_eq_schwartz_toLp _ φ ?_
  -- Both sides are `L²`-classes; compare a.e. representatives.
  apply MeasureTheory.Lp.ext_iff.mpr
  -- `⇑(L2VF_projComponentC_R3 j v) =ᵐ ofReal ∘ ⇑(L2VF_projComponent_R3 j v) =ᵐ ofReal ∘ ψ j`.
  have hLHS : (⇑(L2VF_projComponentC_R3 j (v : L2VF_R3)) : Domain3 → ℂ)
      =ᵐ[volume] fun a => RCLike.ofRealCLM (K := ℂ) (L2VF_projComponent_R3 j (v : L2VF_R3) a) := by
    simpa [L2VF_projComponentC_R3] using
      (RCLike.ofRealCLM (K := ℂ)).coeFn_compLpL (L2VF_projComponent_R3 j (v : L2VF_R3))
  have hcomp : (⇑(L2VF_projComponent_R3 j (v : L2VF_R3)) : Domain3 → ℝ)
      =ᵐ[volume] ⇑(ψ j) := by
    rw [hψ j]; exact (ψ j).coeFn_toLp 2 (volume : Measure Domain3)
  have hRHS : (⇑(φ.toLp 2 (volume : Measure Domain3)) : Domain3 → ℂ) =ᵐ[volume] ⇑φ :=
    φ.coeFn_toLp 2 (volume : Measure Domain3)
  filter_upwards [hLHS, hcomp, hRHS] with a hL hc hR
  rw [hL, hc, hR, hφ, SchwartzMap.postcompCLM_apply]

/-- **A4 `h1Sigma_dense_in_L2Sigma` [must-prove].**
The `H¹` divergence-free velocity fields (those satisfying `memH1VF_R3`) are **dense** in
`L2Sigma_R3`.

For every `u ∈ L2Sigma_R3`, there is a sequence `s : ℕ → L2Sigma_R3` with
`∀ n, memH1VF_R3 (s n : L2VF_R3)` and `Filter.Tendsto s atTop (nhds u)`.

**Proof plan (for prover pass):**
1. Every Schwartz function is in all Sobolev spaces: `SchwartzMap.memSobolev` gives
   `MemSobolev 1 2 (φ.toLp 2 volume : 𝓢'(...))` for any `φ : 𝓢(Domain3, ℂ)`.
2. Hence `IsSchwartzDivFree_R3 v ⟹ memH1VF_R3 (v : L2VF_R3)` (each component
   is a Schwartz `L²`-class, hence H¹ via `SchwartzMap.memSobolev`).
3. `schwartzDivFree_dense_of_curlDense curlSchwartzDense_holds` (proved in `ConvectionForm.lean:594`
   and `CurlDensityCapstone.lean`) gives density of `IsSchwartzDivFree_R3` in `L2Sigma_R3`.
4. Combine (2)+(3): H¹_σ ⊇ Schwartz_σ which is dense → H¹_σ is dense. -/
theorem h1Sigma_dense_in_L2Sigma (u : L2Sigma_R3) :
    ∃ s : ℕ → L2Sigma_R3,
      (∀ n, memH1VF_R3 (s n : L2VF_R3)) ∧
        Filter.Tendsto s Filter.atTop (nhds u) := by
  obtain ⟨s, hsdiv, hstendsto⟩ :=
    schwartzDivFree_dense_of_curlDense curlSchwartzDense_holds u
  exact ⟨s, fun n => memH1VF_R3_of_isSchwartzDivFree (hsdiv n), hstendsto⟩

end LerayHopf
