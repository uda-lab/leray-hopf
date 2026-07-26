import LerayHopf.R3.SobolevEmbedding
import LerayHopf.R3.ConvectionOperator
import LerayHopf.Analysis.PlancherelKernels
import LerayHopf.Analysis.RealComplexLpBridge  -- reLp/mulRBdd family (issue #113 PR-2: extracted,
  -- generic real/complex Lp infrastructure)
import LerayHopf.Analysis.SpectralWeakGradient  -- gradComp_of_memH1 family (issue #113 PR-2:
  -- extracted, generic H¹ weak-gradient infrastructure)
import LerayHopf.Analysis.LpInterpolation  -- L2L6_inter_mem_L3 + component MemLp facts
  -- (issue #113 PR-2: extracted, generic Hölder-interpolation infrastructure)
import LerayHopf.Analysis.WeakLeibniz  -- h1Leibniz2(_H1test) family (issue #113 PR-2: extracted,
  -- generic H¹·H¹ weak-Leibniz-via-Schwartz-approximation infrastructure)
-- SobolevEmbedding.lean import justification: provides A1 (HolderTriple instances),
--   A3 (gns_L6_of_memH1_R3: H¹↪L⁶), A4 (h1Sigma_dense_in_L2Sigma),
--   and transitively Regularity.lean (memH1VF_R3, IsSchwartzDivFree_R3).
-- ConvectionOperator.lean import justification: provides convFormSchwartz,
--   convFormSchwartz_antisymm, convFormSchwartz_eq_witness (used by B5).
-- PlancherelKernels import justification: `eLpNorm_three_le_interp` and
--   `eLpNorm_fderiv_le_sum_lineDeriv` moved there (issue #111 PR-2); already transitively
--   available via SobolevEmbedding but imported directly per dependency discipline.

import Mathlib.Analysis.Distribution.Sobolev
-- Sobolev.lean import justification: MemSobolev.add, MemSobolev.smul,
--   memSobolev_fun_zero, MemSobolev.lineDerivOp (needed for B1, B2).

open MeasureTheory TemperedDistribution SchwartzMap LineDeriv

/-!
# Energy-class convection form on H¹_σ (PR-2, issue #56)

**File:** `LerayHopf/R3/EnergyClassConvection.lean`

**Scope (PR-2, rows B1–B7 of the convection-operator construction, issue #56).**

This file constructs the genuine energy-class trilinear convection form

  `convFormH1 u v w = ∑_{i,a} ∫ (uₐ)(∂ₐvᵢ)(wᵢ)`

on `H¹_σ(ℝ³)`, defined as the submodule `H1Sigma_R3 ≤ L2VF_R3` of elements satisfying
`memH1VF_R3`. The form is proved integrable (B3b via Sobolev embedding A3 + Hölder),
trilinear, agrees with `convFormSchwartz` on Schwartz triples (B5), is antisymmetric in
slots 2,3 (B6 via IBP + weak div-free), and satisfies the L²-norm bound
`|convFormH1 u v w| ≤ C_w * ‖u‖₂ * ‖v‖₂` for fixed Schwartz `w` (B7 via B6).

## Declarations

- **B1** `H1Sigma_R3` — the H¹_σ submodule of `L2VF_R3`.
- **B1a** `memH1VF_R3_add` — `memH1VF_R3 u → memH1VF_R3 v → memH1VF_R3 (u + v)`.
- **B1b** `memH1VF_R3_smul` — `memH1VF_R3 u → memH1VF_R3 (c • u)`.
- **B1c** `memH1VF_R3_zero` — `memH1VF_R3 0`.
- **B2** `gradComp_of_memH1` — the spectral L² weak-gradient component representative.
- **B2a** `gradComponent_weakDeriv` — IBP identity for the weak gradient.
- **B3a** `L2L6_inter_mem_L3` — `MemLp f 2 ∧ MemLp f 6 → MemLp f 3` (log-convexity / Hölder).
- **B3b** `convFormH1_integrable` — integrability of the `uₐ·(∂ₐvᵢ)·wᵢ` integrand.
- **B4** `convFormH1` — the energy-class convection form (noncomputable def).
- **B4a** `convFormH1_add_1` — linearity in slot 1.
- **B4b** `convFormH1_add_2` — linearity in slot 2.
- **B4c** `convFormH1_add_3` — linearity in slot 3.
- **B4d** `convFormH1_smul_1`, `_2`, `_3` — ℝ-homogeneity in each slot.
- **B5** `convFormH1_eq_convFormSchwartz` — agreement with `convFormSchwartz` on Schwartz triples.
- **B6a** `convFormH1_ibp` — IBP for the H¹ weak derivative in convFormH1.
- **B6b** `convFormH1_divFree` — weak div-free identity used in the antisymmetry proof.
- **B6** `convFormH1_antisymm` — `convFormH1 u v w = -convFormH1 u w v`.
- **B7** `convFormH1_bound_Schwartz` — `|convFormH1 u v w| ≤ C_w * ‖u‖₂ * ‖v‖₂` for Schwartz `w`.

## Mathlib decls consumed

| Decl | File | Used by |
|---|---|---|
| `TemperedDistribution.MemSobolev.add` | `Distribution/Sobolev.lean:157` | B1a |
| `TemperedDistribution.MemSobolev.smul` | `Distribution/Sobolev.lean:180` | B1b |
| `TemperedDistribution.memSobolev_fun_zero` | `Distribution/Sobolev.lean:189` | B1c |
| `TemperedDistribution.MemSobolev.lineDerivOp` | `Distribution/Sobolev.lean:220` | B2 |
| `TemperedDistribution.memSobolev_zero_iff` | `Distribution/Sobolev.lean:153` | B2 |
| `MeasureTheory.eLpNorm'_le_eLpNorm'_mul_eLpNorm'` | `LpSeminorm/CompareExp.lean:206` | B3a |
| `ContinuousLinearMap.memLp_of_bilin` | `Function/Holder.lean:47` | B3b |
| `LerayHopf.gns_L6_of_memH1_R3` | `SobolevEmbedding.lean:875` | B3b |
| `LerayHopf.instHolderTriple_6_3_2` | `SobolevEmbedding.lean:118` | B3b |
| `LerayHopf.convFormSchwartz_antisymm` | `ConvectionOperator.lean` | B5 |

## ⚠️ Plan notes vs. mathlib reality

- The plan §5 says `eLpNorm_le_eLpNorm_pow_mul_eLpNorm` for B3a. **This name does NOT
  exist in mathlib.** The correct lemma is `MeasureTheory.eLpNorm'_le_eLpNorm'_mul_eLpNorm'`
  (in `LpSeminorm/CompareExp.lean:206`) — or equivalently via `HolderTriple` instances and
  `eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm`. The prover pass must use these instead.
- `MemSobolev.smul` takes `c : ℂ`, not `c : ℝ`. For real scalar multiplication in B1b,
  coerce `c : ℝ` to `(c : ℂ)` and verify the tempered-distribution equality.

## Assumptions

None — this file introduces no `axiom`/`opaque`. All sorry bodies are
`-- ALLOW_SORRY: PR-2 must-prove (Bx)`.

## Scaffold status

B1, B2 (`gradComponent_weakDeriv`), B3a, B3b, B4 (all six trilinearity lemmas), B5
(`convFormH1_eq_convFormSchwartz`) and B6b (`convFormH1_divFree`) are proved sorry-free.

The **H¹·H¹ weak Leibniz product rule** `∂ₐ(f·g) = (∂ₐf)g + f(∂ₐg)` (tested against a Schwartz
function) — the stated remaining Brick — is now PROVED sorry-free as the `private` lemma
`h1Leibniz2`, via the supporting infrastructure built in this file:
- `reLp`/`mulRBdd`/`tendsto_mulRBdd`/`tendsto_integral_mul_mul` — the L²-inner-product limit engine;
- `prodS`/`lineDerivOp_prodS`/`schwartzLeibniz2` — the classical Schwartz Leibniz IBP;
- `reS`/`lineDerivOp_reS`/`reSchwartz_approx` — real-Schwartz approximants from `schwartz_h1_gradConv`
  with simultaneous L²-value and one-direction L²-gradient convergence.

Three targets remain marked `-- ALLOW_SORRY`:

- **B6a** (`convFormH1_ibp`), **B6** (`convFormH1_antisymm`), **B7** (`convFormH1_bound_Schwartz`)
  — all reduce (via `h1Leibniz2` + B6b) to the **H¹-test extension**: extending the Schwartz-test
  Leibniz/div-free identities to an H¹ test (the un-differentiated middle factor `vᵢ`). The single
  open analytic sub-step is the **L³-convergence** of the single-direction Schwartz approximants:
  the RHS term `∫(∂ₐuₐ·wᵢ)·vₙ` pairs `L^{3/2} = L²·L⁶` against `vₙ`, so it needs `vₙ → vᵢ` in `L³`,
  while `schwartz_h1_gradConv` (single direction) yields only L²-value + one-direction-L²-gradient
  convergence. L³-convergence follows from a uniform L⁶ bound (`‖ψₙ‖₆ ≤ C‖∇ψₙ‖₂` via GNS/A3, needing
  the FULL gradient of a single approximant sequence) + interpolation `‖h‖₃ ≤ ‖h‖₂^{1/2}‖h‖₆^{1/2}`.
  The full-gradient control requires a multi-direction variant of the `schwartz_h1_gradConv` export
  (one `φₙ` converging in every direction) — a `lean-coder` signature change. After that, B6a/B6/B7
  close mechanically from `h1Leibniz2`, B6b, and the interpolation.
-/

namespace LerayHopf

/-! ### B1 — The H¹_σ submodule of `L2VF_R3`

`memH1VF_R3_add`/`memH1VF_R3_smul`/`memH1VF_R3_zero` (formerly B1a/B1b/B1c here) now live in
`R3/Regularity.lean` (issue #113 PR-2) — needed there since `Analysis/SpectralWeakGradient.lean`
(upstream of this file) references the first two in `gradComp_of_memH1_add`/`_smul`'s statements. -/

/-! #### B1 — The submodule itself -/

/-- **B1 `H1Sigma_R3` [proved sorry-free].** The H¹_σ submodule of `L2VF_R3`:
elements of `L²(ℝ³; ℝ³)` that satisfy BOTH the H¹ regularity condition `memH1VF_R3`
AND the divergence-free condition (`u ∈ L2Sigma_R3`).

Concretely:
  `H1Sigma_R3 = {u : L2VF_R3 | memH1VF_R3 u ∧ u ∈ L2Sigma_R3}`

This is the correct `H¹_σ(ℝ³)` space: H¹ vector fields that are divergence-free in the
weak sense. The div-free condition is required by downstream consumers
(PR-3 Hamel extension, `b_antisymm` slot hypotheses in `convFormH1_antisymm`/B6/B7).

Submodule closure proofs:
- `add_mem'`: `memH1VF_R3_add` for the H¹ conjunct; `Submodule.add_mem` for the σ conjunct.
- `zero_mem'`: `memH1VF_R3_zero` for H¹; `Submodule.zero_mem` for σ.
- `smul_mem'`: `memH1VF_R3_smul` for H¹; `Submodule.smul_mem` for σ. -/
def H1Sigma_R3 : Submodule ℝ L2VF_R3 where
  carrier := {u | memH1VF_R3 u ∧ u ∈ L2Sigma_R3}
  add_mem' hu hv :=
    ⟨memH1VF_R3_add hu.1 hv.1, L2Sigma_R3.add_mem hu.2 hv.2⟩
  zero_mem' :=
    ⟨memH1VF_R3_zero, L2Sigma_R3.zero_mem⟩
  smul_mem' c _ hu :=
    ⟨memH1VF_R3_smul c hu.1, L2Sigma_R3.smul_mem c hu.2⟩

/-! ### B3a — `L²∩L⁶↪L³` interpolation

`L2L6_inter_mem_L3` and the component `MemLp` facts (`memLp_six/two/three_componentRe`,
`memLp_two_gradRe`) now live in `Analysis/LpInterpolation.lean` (issue #113 PR-2): pure
Hölder/log-convexity infrastructure, no convection-specific content. -/

/-! ### B3b — Integrability of the convection integrand -/

/-- **B3b `convFormH1_integrable` [must-prove].** For `u, v, w ∈ H1Sigma_R3`, the
integrand `(ψu a x) * (∂ₐ ψv i)(x) * (ψw i x)` appearing in `convFormH1` is integrable.

More precisely: for `u, v, w : L2VF_R3` with `memH1VF_R3 u`, `memH1VF_R3 v`,
`memH1VF_R3 w` and directions `i a : Fin 3`, the function

  `x ↦ (L2VF_projComponentC_R3 a u x).re * (gradComp_of_memH1 v hv a i x).re * (L2VF_projComponentC_R3 i w x).re`

is integrable (as a real-valued function).

**Proof route (for prover):**
1. A3 (`gns_L6_of_memH1_R3`) gives `uₐ ∈ L⁶` and `wᵢ ∈ L⁶` (via each Sobolev component).
2. B3a gives `wᵢ ∈ L³` (from `wᵢ ∈ L² ∩ L⁶`; L² follows from Lp membership at exponent 2).
3. `gradComp_of_memH1 v hv a i ∈ L²` (the L² representative from B2).
4. Hölder with `1/6 + 1/2 + 1/3 = 1`: `uₐ ∈ L⁶`, `∂ₐvᵢ ∈ L²`, `wᵢ ∈ L³` →
   use `instHolderTriple_6_3_2` (A1) + `ContinuousLinearMap.memLp_of_bilin` twice to
   form the triple product in L¹. -/
theorem convFormH1_integrable (u v w : L2VF_R3)
    (hu : memH1VF_R3 u) (hv : memH1VF_R3 v) (hw : memH1VF_R3 w)
    (i a : Fin 3) :
    MeasureTheory.Integrable
      (fun x : Domain3 =>
        (L2VF_projComponentC_R3 a u x).re *
        (gradComp_of_memH1 v hv a i x).re *
        (L2VF_projComponentC_R3 i w x).re)
      (volume : Measure Domain3) := by
  -- uₐ.re ∈ L⁶, wᵢ.re ∈ L³, gradᵥ.re ∈ L².
  have hu6 : MemLp (fun x => (L2VF_projComponentC_R3 a u x).re) 6 (volume : Measure Domain3) :=
    memLp_six_componentRe u hu a
  have hw3 : MemLp (fun x => (L2VF_projComponentC_R3 i w x).re) 3 (volume : Measure Domain3) :=
    memLp_three_componentRe w hw i
  have hg2 : MemLp (fun x => (gradComp_of_memH1 v hv a i x).re) 2 (volume : Measure Domain3) :=
    memLp_two_gradRe v hv a i
  -- uₐ·wᵢ ∈ L² (HolderTriple 6 3 2), then ·gradᵥ ∈ L¹ (HolderTriple 2 2 1).
  haveI : ENNReal.HolderTriple 6 3 2 := instHolderTriple_6_3_2
  have huw : MemLp (fun x => (L2VF_projComponentC_R3 a u x).re *
      (L2VF_projComponentC_R3 i w x).re) 2 (volume : Measure Domain3) :=
    hw3.mul (p := 6) (q := 3) (r := 2) hu6
  have htriple : MemLp (fun x => (gradComp_of_memH1 v hv a i x).re *
      ((L2VF_projComponentC_R3 a u x).re * (L2VF_projComponentC_R3 i w x).re)) 1
      (volume : Measure Domain3) := huw.mul (p := 2) (q := 2) (r := 1) hg2
  rw [memLp_one_iff_integrable] at htriple
  refine htriple.congr ?_
  filter_upwards with x; ring

/-! ### B4 — The energy-class convection form `convFormH1` -/

/-- **B4 `convFormH1` [must-prove def + trilinearity].** The energy-class trilinear
convection form on `H¹_σ(ℝ³)`:

  `convFormH1 u v w hu hv hw = ∑_{i : Fin 3} ∑_{a : Fin 3} ∫ (uₐ)(∂ₐvᵢ)(wᵢ) dx`

where:
- `uₐ = L2VF_projComponentC_R3 a u` (a-th component of u, in L²(ℝ³; ℂ)),
- `∂ₐvᵢ = gradComp_of_memH1 v hv a i` (the L² weak partial derivative),
- `wᵢ = L2VF_projComponentC_R3 i w` (i-th component of w).

The sign matches `convIntegralSchwartz` (positive sum), agreeing with `convFormSchwartz` on
Schwartz triples (B5). The integrability of each summand is B3b.
The definition is noncomputable (Bochner integral). -/
noncomputable def convFormH1 (u v w : L2VF_R3)
    (_hu : memH1VF_R3 u) (hv : memH1VF_R3 v) (_hw : memH1VF_R3 w) : ℝ :=
  ∑ i : Fin 3, ∑ a : Fin 3,
    ∫ x : Domain3,
      (L2VF_projComponentC_R3 a u x).re *
      (gradComp_of_memH1 v hv a i x).re *
      (L2VF_projComponentC_R3 i w x).re
    ∂(volume : Measure Domain3)

/-- A.e. pointwise additivity of the real component of `componentC` under field addition. -/
private theorem componentRe_add_ae (u u' : L2VF_R3) (j : Fin 3) :
    (fun x => (L2VF_projComponentC_R3 j (u + u') x).re)
      =ᵐ[volume] fun x => (L2VF_projComponentC_R3 j u x).re
        + (L2VF_projComponentC_R3 j u' x).re := by
  have h := MeasureTheory.Lp.coeFn_add (L2VF_projComponentC_R3 j u) (L2VF_projComponentC_R3 j u')
  rw [map_add]
  filter_upwards [h] with x hx
  rw [hx]; simp [Complex.add_re]

/-- A.e. pointwise homogeneity of the real component of `componentC` under field smul. -/
private theorem componentRe_smul_ae (c : ℝ) (u : L2VF_R3) (j : Fin 3) :
    (fun x => (L2VF_projComponentC_R3 j (c • u) x).re)
      =ᵐ[volume] fun x => c * (L2VF_projComponentC_R3 j u x).re := by
  rw [map_smul]
  have h := MeasureTheory.Lp.coeFn_smul c (L2VF_projComponentC_R3 j u)
  filter_upwards [h] with x hx
  rw [hx]; simp [Complex.real_smul]

/-- A.e. pointwise additivity of the real part of the weak gradient under field addition. -/
private theorem gradRe_add_ae (v v' : L2VF_R3) (hv : memH1VF_R3 v) (hv' : memH1VF_R3 v')
    (a i : Fin 3) :
    (fun x => (gradComp_of_memH1 (v + v') (memH1VF_R3_add hv hv') a i x).re)
      =ᵐ[volume] fun x => (gradComp_of_memH1 v hv a i x).re
        + (gradComp_of_memH1 v' hv' a i x).re := by
  have heq := gradComp_of_memH1_add v v' hv hv' a i
  have h := MeasureTheory.Lp.coeFn_add (gradComp_of_memH1 v hv a i) (gradComp_of_memH1 v' hv' a i)
  filter_upwards [h] with x hx
  rw [heq, hx]; simp [Complex.add_re]

/-- A.e. pointwise homogeneity of the real part of the weak gradient under field smul. -/
private theorem gradRe_smul_ae (c : ℝ) (v : L2VF_R3) (hv : memH1VF_R3 v) (a i : Fin 3) :
    (fun x => (gradComp_of_memH1 (c • v) (memH1VF_R3_smul c hv) a i x).re)
      =ᵐ[volume] fun x => c * (gradComp_of_memH1 v hv a i x).re := by
  have heq := gradComp_of_memH1_smul c v hv a i
  have h := MeasureTheory.Lp.coeFn_smul (c : ℂ) (gradComp_of_memH1 v hv a i)
  filter_upwards [h] with x hx
  rw [heq, hx]; simp

/-- **Scaffold.** The `∑ i, ∑ a, ∫ Φ` structure common to `convFormH1_add_1/2/3`: if the
`(i,a)`-integrand `Φ i a` splits a.e. as a sum `Φ₁ i a + Φ₂ i a` of two integrable pieces, the
double-sum-of-integrals splits the same way. Each of the three `convFormH1_add_k` proofs differs
only in which factor of the triple product `Φ` is the one that splits (supplied via `hsplit`);
this lemma carries the shared `Finset.sum_add_distrib` (×2) / `integral_congr_ae` /
`integral_add` bookkeeping. -/
private theorem sum_sum_integral_add_of_ae
    (Φ Φ₁ Φ₂ : Fin 3 → Fin 3 → Domain3 → ℝ)
    (hint₁ : ∀ i a, MeasureTheory.Integrable (Φ₁ i a) (volume : Measure Domain3))
    (hint₂ : ∀ i a, MeasureTheory.Integrable (Φ₂ i a) (volume : Measure Domain3))
    (hsplit : ∀ i a, Φ i a =ᵐ[volume] fun x => Φ₁ i a x + Φ₂ i a x) :
    (∑ i : Fin 3, ∑ a : Fin 3, ∫ x, Φ i a x ∂(volume : Measure Domain3))
      = (∑ i : Fin 3, ∑ a : Fin 3, ∫ x, Φ₁ i a x ∂(volume : Measure Domain3))
        + ∑ i : Fin 3, ∑ a : Fin 3, ∫ x, Φ₂ i a x ∂(volume : Measure Domain3) := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [MeasureTheory.integral_congr_ae (hsplit i a),
    MeasureTheory.integral_add (hint₁ i a) (hint₂ i a)]

/-- **Scaffold.** The `∑ i, ∑ a, ∫ Φ` structure common to `convFormH1_smul_1/2/3`: if the
`(i,a)`-integrand `Φ i a` is a.e. `c` times a base integrand `Φ₀ i a`, the double-sum-of-integrals
pulls out the constant `c` the same way. Mirrors `sum_sum_integral_add_of_ae`. -/
private theorem sum_sum_integral_const_mul_of_ae (c : ℝ)
    (Φ Φ₀ : Fin 3 → Fin 3 → Domain3 → ℝ)
    (hsplit : ∀ i a, Φ i a =ᵐ[volume] fun x => c * Φ₀ i a x) :
    (∑ i : Fin 3, ∑ a : Fin 3, ∫ x, Φ i a x ∂(volume : Measure Domain3))
      = c * ∑ i : Fin 3, ∑ a : Fin 3, ∫ x, Φ₀ i a x ∂(volume : Measure Domain3) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [MeasureTheory.integral_congr_ae (hsplit i a), MeasureTheory.integral_const_mul]

/-- **B4a `convFormH1_add_1` [must-prove].** `convFormH1` is additive in slot 1:
`convFormH1 (u + u') v w (add hu hu') hv hw = convFormH1 u v w hu hv hw + convFormH1 u' v w hu' hv hw`. -/
theorem convFormH1_add_1 (u u' v w : L2VF_R3)
    (hu : memH1VF_R3 u) (hu' : memH1VF_R3 u')
    (hv : memH1VF_R3 v) (hw : memH1VF_R3 w) :
    convFormH1 (u + u') v w (memH1VF_R3_add hu hu') hv hw =
    convFormH1 u v w hu hv hw + convFormH1 u' v w hu' hv hw := by
  unfold convFormH1
  refine sum_sum_integral_add_of_ae _ _ _
    (convFormH1_integrable u v w hu hv hw) (convFormH1_integrable u' v w hu' hv hw) fun i a => ?_
  filter_upwards [componentRe_add_ae u u' a] with x hx
  rw [hx]; ring

/-- **B4b `convFormH1_add_2` [must-prove].** `convFormH1` is additive in slot 2:
`convFormH1 u (v + v') w hu (add hv hv') hw = convFormH1 u v w hu hv hw + convFormH1 u v' w hu hv' hw`. -/
theorem convFormH1_add_2 (u v v' w : L2VF_R3)
    (hu : memH1VF_R3 u) (hv : memH1VF_R3 v) (hv' : memH1VF_R3 v')
    (hw : memH1VF_R3 w) :
    convFormH1 u (v + v') w hu (memH1VF_R3_add hv hv') hw =
    convFormH1 u v w hu hv hw + convFormH1 u v' w hu hv' hw := by
  unfold convFormH1
  refine sum_sum_integral_add_of_ae _ _ _
    (convFormH1_integrable u v w hu hv hw) (convFormH1_integrable u v' w hu hv' hw) fun i a => ?_
  filter_upwards [gradRe_add_ae v v' hv hv' a i] with x hx
  rw [hx]; ring

/-- **B4c `convFormH1_add_3` [must-prove].** `convFormH1` is additive in slot 3. -/
theorem convFormH1_add_3 (u v w w' : L2VF_R3)
    (hu : memH1VF_R3 u) (hv : memH1VF_R3 v)
    (hw : memH1VF_R3 w) (hw' : memH1VF_R3 w') :
    convFormH1 u v (w + w') hu hv (memH1VF_R3_add hw hw') =
    convFormH1 u v w hu hv hw + convFormH1 u v w' hu hv hw' := by
  unfold convFormH1
  refine sum_sum_integral_add_of_ae _ _ _
    (convFormH1_integrable u v w hu hv hw) (convFormH1_integrable u v w' hu hv hw') fun i a => ?_
  filter_upwards [componentRe_add_ae w w' i] with x hx
  rw [hx]; ring

/-- **B4d-1 `convFormH1_smul_1` [must-prove].** `convFormH1` is ℝ-homogeneous in slot 1. -/
theorem convFormH1_smul_1 (c : ℝ) (u v w : L2VF_R3)
    (hu : memH1VF_R3 u) (hv : memH1VF_R3 v) (hw : memH1VF_R3 w) :
    convFormH1 (c • u) v w (memH1VF_R3_smul c hu) hv hw =
    c * convFormH1 u v w hu hv hw := by
  unfold convFormH1
  refine sum_sum_integral_const_mul_of_ae c _ _ fun i a => ?_
  filter_upwards [componentRe_smul_ae c u a] with x hx
  rw [hx]; ring

/-- **B4d-2 `convFormH1_smul_2` [must-prove].** `convFormH1` is ℝ-homogeneous in slot 2. -/
theorem convFormH1_smul_2 (c : ℝ) (u v w : L2VF_R3)
    (hu : memH1VF_R3 u) (hv : memH1VF_R3 v) (hw : memH1VF_R3 w) :
    convFormH1 u (c • v) w hu (memH1VF_R3_smul c hv) hw =
    c * convFormH1 u v w hu hv hw := by
  unfold convFormH1
  refine sum_sum_integral_const_mul_of_ae c _ _ fun i a => ?_
  filter_upwards [gradRe_smul_ae c v hv a i] with x hx
  rw [hx]; ring

/-- **B4d-3 `convFormH1_smul_3` [must-prove].** `convFormH1` is ℝ-homogeneous in slot 3. -/
theorem convFormH1_smul_3 (c : ℝ) (u v w : L2VF_R3)
    (hu : memH1VF_R3 u) (hv : memH1VF_R3 v) (hw : memH1VF_R3 w) :
    convFormH1 u v (c • w) hu hv (memH1VF_R3_smul c hw) =
    c * convFormH1 u v w hu hv hw := by
  unfold convFormH1
  refine sum_sum_integral_const_mul_of_ae c _ _ fun i a => ?_
  filter_upwards [componentRe_smul_ae c w i] with x hx
  rw [hx]; ring

/-! ### B5 — Agreement with `convFormSchwartz` on Schwartz triples -/

/-- If the j-th real component of `v` is a Schwartz class `(ψ).toLp 2`, then the complex
component embeds as the complexified Schwartz class `(cxify ψ).toLp 2`. -/
private theorem componentC_eq_cxify_toLp (v : L2VF_R3) (ψ : SchwartzMap Domain3 ℝ) (j : Fin 3)
    (hψ : L2VF_projComponent_R3 j v = ψ.toLp 2 (volume : Measure Domain3)) :
    L2VF_projComponentC_R3 j v = (cxify ψ).toLp 2 (volume : Measure Domain3) := by
  have hcoe : (⇑(L2VF_projComponentC_R3 j v) : Domain3 → ℂ)
      =ᵐ[volume] fun x => (((L2VF_projComponent_R3 j v) x : ℝ) : ℂ) := by
    rw [L2VF_projComponentC_R3]
    filter_upwards [ContinuousLinearMap.coeFn_compLpL
      (RCLike.ofRealCLM (K := ℂ)) (L2VF_projComponent_R3 j v)] with x hx
    simpa using hx
  -- a.e. coeFn of the real component = ψ (via hψ : componentReal = ψ.toLp).
  have hψcoe : (⇑(L2VF_projComponent_R3 j v) : Domain3 → ℝ) =ᵐ[volume] fun x => ψ x := by
    rw [hψ]; exact (ψ).coeFn_toLp 2 (volume : Measure Domain3)
  apply MeasureTheory.Lp.ext
  filter_upwards [hcoe, (cxify ψ).coeFn_toLp 2 (volume : Measure Domain3), hψcoe]
    with x hx hcx hψx
  rw [hx, hcx, hψx, cxify_apply]

/-- For a Schwartz-class field component, the weak gradient `gradComp_of_memH1` equals the
complexified classical line derivative `(cxify (∂ₐ ψ)).toLp 2`. -/
private theorem gradComp_schwartz_eq (v : L2VF_R3) (hv : memH1VF_R3 v)
    (ψ : SchwartzMap Domain3 ℝ) (a i : Fin 3)
    (hψ : L2VF_projComponent_R3 i v = ψ.toLp 2 (volume : Measure Domain3)) :
    gradComp_of_memH1 v hv a i
      = (cxify ((lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
          (EuclideanSpace.single a (1 : ℝ) : Domain3)) ψ)).toLp 2 (volume : Measure Domain3) := by
  apply L2C_eq_of_toTempered_eq
  rw [← gradComp_of_memH1_spec]
  -- (componentC i v : 𝓢') = ((cxify ψ).toLp : 𝓢') = toTemperedCLM (cxify ψ).
  rw [componentC_eq_cxify_toLp v ψ i hψ, MeasureTheory.Lp.toTemperedDistribution_toLp_eq,
    MeasureTheory.Lp.toTemperedDistribution_toLp_eq,
    TemperedDistribution.lineDerivOp_toTemperedDistributionCLM_eq]
  congr 1
  have := lineDerivOp_cxify (EuclideanSpace.single a (1 : ℝ) : Domain3) ψ
  rw [LineDeriv.lineDerivOpCLM_apply] at this
  exact this



/-- **B5 `convFormH1_eq_convFormSchwartz` [must-prove].** For `u, v, w : L2Sigma_R3` each
satisfying `IsSchwartzDivFree_R3` (which implies `memH1VF_R3 u/v/w` via
`SchwartzMap.memSobolev`), `convFormH1` agrees with `convFormSchwartz`:

  `convFormH1 (u : L2VF_R3) (v : L2VF_R3) (w : L2VF_R3) hu hv hw =
     convFormSchwartz u v w hus hvs hws`

**Proof route (for prover):**
1. The Schwartz witnesses for `hus`/`hvs`/`hws` give component functions `ψu, ψv, ψw`.
2. For `ψv i`, `SchwartzMap.memSobolev` gives `MemSobolev 1 2 (ψv i).toLp 2` which
   means `gradComp_of_memH1 v hv a i` is the L²-representative of `∂_{eₐ}(ψv i).toLp 2`.
3. For a Schwartz function, the distributional derivative equals the classical derivative:
   `∂_{eₐ} (ψv i).toLp = (lineDerivOpCLM … (ψv i)).toLp`.
4. Hence the integral in `convFormH1` equals the integral in `convIntegralSchwartz`.
5. Conclude via `convFormSchwartz_eq_witness`. -/
theorem convFormH1_eq_convFormSchwartz
    (u v w : L2Sigma_R3)
    (hus : IsSchwartzDivFree_R3 u) (hvs : IsSchwartzDivFree_R3 v)
    (hws : IsSchwartzDivFree_R3 w)
    (hu : memH1VF_R3 (u : L2VF_R3)) (hv : memH1VF_R3 (v : L2VF_R3))
    (hw : memH1VF_R3 (w : L2VF_R3)) :
    convFormH1 (u : L2VF_R3) (v : L2VF_R3) (w : L2VF_R3) hu hv hw =
    convFormSchwartz u v w hus hvs hws := by
  -- Use the chosen Schwartz witnesses.
  obtain ⟨ψu, hψu⟩ := hus
  obtain ⟨ψv, hψv⟩ := hvs
  obtain ⟨ψw, hψw⟩ := hws
  rw [convFormSchwartz_eq_witness u v w ⟨ψu, hψu⟩ ⟨ψv, hψv⟩ ⟨ψw, hψw⟩ ψu ψv ψw hψu hψv hψw]
  -- a.e. identification of each convFormH1 integrand with the convIntegralSchwartz integrand.
  have hsummand : ∀ i a : Fin 3,
      ∫ x : Domain3, (L2VF_projComponentC_R3 a (u : L2VF_R3) x).re *
          (gradComp_of_memH1 (v : L2VF_R3) hv a i x).re *
          (L2VF_projComponentC_R3 i (w : L2VF_R3) x).re ∂(volume : Measure Domain3)
        = ∫ x : Domain3, (ψu a x) *
          ((lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
            (EuclideanSpace.single a (1 : ℝ) : Domain3)) (ψv i)) x * (ψw i x)
          ∂(volume : Measure Domain3) := by
    intro i a
    refine MeasureTheory.integral_congr_ae ?_
    -- componentRe = ψ a.e.; gradRe = ∂ₐ ψv_i a.e.
    have huae : (fun x => (L2VF_projComponentC_R3 a (u : L2VF_R3) x).re) =ᵐ[volume]
        fun x => ψu a x := by
      rw [componentC_eq_cxify_toLp (u : L2VF_R3) (ψu a) a (hψu a)]
      filter_upwards [(cxify (ψu a)).coeFn_toLp 2 (volume : Measure Domain3)] with x hx
      rw [hx, cxify_apply, Complex.ofReal_re]
    have hwae : (fun x => (L2VF_projComponentC_R3 i (w : L2VF_R3) x).re) =ᵐ[volume]
        fun x => ψw i x := by
      rw [componentC_eq_cxify_toLp (w : L2VF_R3) (ψw i) i (hψw i)]
      filter_upwards [(cxify (ψw i)).coeFn_toLp 2 (volume : Measure Domain3)] with x hx
      rw [hx, cxify_apply, Complex.ofReal_re]
    have hgae : (fun x => (gradComp_of_memH1 (v : L2VF_R3) hv a i x).re) =ᵐ[volume]
        fun x => ((lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
            (EuclideanSpace.single a (1 : ℝ) : Domain3)) (ψv i)) x := by
      rw [gradComp_schwartz_eq (v : L2VF_R3) hv (ψv i) a i (hψv i)]
      filter_upwards [(cxify ((lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
        (EuclideanSpace.single a (1 : ℝ) : Domain3)) (ψv i))).coeFn_toLp 2
        (volume : Measure Domain3)] with x hx
      rw [hx, cxify_apply, Complex.ofReal_re]
    filter_upwards [huae, hwae, hgae] with x hux hwx hgx
    rw [hux, hwx, hgx]
  -- Sum the (i,a) identities. Both convFormH1 and convIntegralSchwartz are positive sums;
  -- after simp_rw the goal is definitionally equal.
  unfold convFormH1 convIntegralSchwartz
  simp_rw [hsummand]

/-! ### B6 IBP infrastructure

The H¹·H¹ weak-Leibniz-via-Schwartz-approximation machinery (prodS, reS, reSchwartz_L3_approx,
reSchwartz_approx, h1Leibniz2, h1Leibniz2_H1test, and their supporting lemmas) now lives in
`Analysis/WeakLeibniz.lean` (issue #113 PR-2): pure H¹/Schwartz-approximation infrastructure,
no convection-specific content. -/

/-! ### B6 — Antisymmetry in slots 2,3 -/

/-- **B6a `convFormH1_ibp` [must-prove].** Integration by parts for `convFormH1`:
moving the derivative from slot 2 to slots 1 and 3 using the weak IBP identity B2.

With the positive-sum definition `convFormH1 u v w = ∑_{i,a} ∫ uₐ·∂ₐvᵢ·wᵢ`, IBP via the
Leibniz product rule `∂ₐ(vᵢ) = ∂ₐ(vᵢ·1)` gives:
  `∫ uₐ·(∂ₐvᵢ)·wᵢ = -∫ (∂ₐuₐ)·vᵢ·wᵢ - ∫ uₐ·vᵢ·(∂ₐwᵢ)`

so that `convFormH1 u v w = -∑_{i,a} ∫ (∂ₐuₐ · vᵢ · wᵢ) - ∑_{i,a} ∫ (uₐ · vᵢ · ∂ₐwᵢ)`.
After IBP, the div-free condition kills the first sum via B6b. -/
theorem convFormH1_ibp (u v w : L2VF_R3)
    (hu : memH1VF_R3 u) (hv : memH1VF_R3 v) (hw : memH1VF_R3 w)
    (_hu_sigma : (u : L2VF_R3) ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3))
    (_hw_sigma : (w : L2VF_R3) ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3)) :
    convFormH1 u v w hu hv hw =
    -(∑ i : Fin 3, ∑ a : Fin 3,
      ∫ x : Domain3,
        (gradComp_of_memH1 u hu a a x).re *
        (L2VF_projComponentC_R3 i v x).re *
        (L2VF_projComponentC_R3 i w x).re
      ∂(volume : Measure Domain3)) -
    ∑ i : Fin 3, ∑ a : Fin 3,
      ∫ x : Domain3,
        (L2VF_projComponentC_R3 a u x).re *
        (L2VF_projComponentC_R3 i v x).re *
        (gradComp_of_memH1 w hw a i x).re
      ∂(volume : Measure Domain3) := by
  classical
  -- Per-(i,a) IBP identity from the H¹-test weak Leibniz rule.
  have hpia : ∀ i a : Fin 3,
      ∫ x : Domain3, (L2VF_projComponentC_R3 a u x).re *
        (gradComp_of_memH1 v hv a i x).re * (L2VF_projComponentC_R3 i w x).re
        ∂(volume : Measure Domain3)
      = -(∫ x : Domain3, (gradComp_of_memH1 u hu a a x).re *
            (L2VF_projComponentC_R3 i v x).re * (L2VF_projComponentC_R3 i w x).re
            ∂(volume : Measure Domain3))
        - ∫ x : Domain3, (L2VF_projComponentC_R3 a u x).re *
            (L2VF_projComponentC_R3 i v x).re * (gradComp_of_memH1 w hw a i x).re
            ∂(volume : Measure Domain3) := by
    intro i a
    have hL := h1Leibniz2_H1test (L2VF_projComponentC_R3 a u) (L2VF_projComponentC_R3 i w)
      (gradComp_of_memH1 u hu a a) (gradComp_of_memH1 w hw a i)
      (L2VF_projComponentC_R3 i v) (gradComp_of_memH1 v hv a i) a
      (hu a) (hw i)
      (gradComp_of_memH1_spec u hu a a) (gradComp_of_memH1_spec w hw a i)
      (hv i) (gradComp_of_memH1_spec v hv a i)
      (memLp_six_componentRe u hu a) (memLp_three_componentRe u hu a)
      (memLp_six_componentRe w hw i)
    -- Reorder the LHS integrand `uₐ·wᵢ·(∂ₐvᵢ)` to match `uₐ·(∂ₐvᵢ)·wᵢ`.
    rw [show (∫ x : Domain3, (L2VF_projComponentC_R3 a u x).re *
          (gradComp_of_memH1 v hv a i x).re * (L2VF_projComponentC_R3 i w x).re
          ∂(volume : Measure Domain3))
        = ∫ x : Domain3, (L2VF_projComponentC_R3 a u x).re * (L2VF_projComponentC_R3 i w x).re
          * (gradComp_of_memH1 v hv a i x).re ∂(volume : Measure Domain3) from
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)]
    rw [hL]
    -- Split the RHS sum-integral; the two coefficient products are each integrable (Hölder).
    -- `(∂ₐuₐ).re·wᵢ.re ∈ L^{3/2}` (L²·L⁶), times `vᵢ.re ∈ L³` ⇒ L¹.
    haveI hHT263 : ENNReal.HolderTriple 6 2 (3/2) := by
      have h : Real.HolderTriple (6 : ℝ) (2 : ℝ) (3/2 : ℝ) := by constructor <;> norm_num
      have h2 := h.ennrealOfReal
      have e32 : ENNReal.ofReal (3 / 2 : ℝ) = (3 / 2 : ENNReal) := by
        rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp
      simpa only [ENNReal.ofReal_ofNat, e32] using h2
    haveI hHT3321 : ENNReal.HolderTriple (3/2) 3 1 := by
      have h : Real.HolderTriple (3/2 : ℝ) (3 : ℝ) (1 : ℝ) := by constructor <;> norm_num
      have h2 := h.ennrealOfReal
      have e32 : ENNReal.ofReal (3 / 2 : ℝ) = (3 / 2 : ENNReal) := by
        rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp
      simpa only [ENNReal.ofReal_ofNat, ENNReal.ofReal_one, e32] using h2
    have hcoeff1 : MemLp (fun x => (gradComp_of_memH1 u hu a a x).re
        * (L2VF_projComponentC_R3 i w x).re) (3/2) (volume : Measure Domain3) :=
      MeasureTheory.MemLp.ae_eq (Filter.Eventually.of_forall fun x => by simp [Pi.mul_apply, mul_comm])
        ((memLp_two_gradRe u hu a a).mul (p := 6) (q := 2) (r := 3/2)
          (memLp_six_componentRe w hw i))
    have hcoeff2 : MemLp (fun x => (L2VF_projComponentC_R3 a u x).re
        * (gradComp_of_memH1 w hw a i x).re) (3/2) (volume : Measure Domain3) :=
      MeasureTheory.MemLp.ae_eq (Filter.Eventually.of_forall fun x => by simp [Pi.mul_apply, mul_comm])
        ((memLp_two_gradRe w hw a i).mul (p := 6) (q := 2) (r := 3/2)
          (memLp_six_componentRe u hu a))
    have hint1 : MeasureTheory.Integrable
        (fun x => (gradComp_of_memH1 u hu a a x).re * (L2VF_projComponentC_R3 i v x).re
          * (L2VF_projComponentC_R3 i w x).re) (volume : Measure Domain3) := by
      have := (memLp_three_componentRe v hv i).mul (p := 3/2) (q := 3) (r := 1) hcoeff1
      rw [memLp_one_iff_integrable] at this
      refine this.congr ?_; filter_upwards with x; simp only [Pi.mul_apply]; ring
    have hint2 : MeasureTheory.Integrable
        (fun x => (L2VF_projComponentC_R3 a u x).re * (L2VF_projComponentC_R3 i v x).re
          * (gradComp_of_memH1 w hw a i x).re) (volume : Measure Domain3) := by
      have := (memLp_three_componentRe v hv i).mul (p := 3/2) (q := 3) (r := 1) hcoeff2
      rw [memLp_one_iff_integrable] at this
      refine this.congr ?_; filter_upwards with x; simp only [Pi.mul_apply]; ring
    -- `∫((∂ₐuₐ·wᵢ) + (uₐ·∂ₐwᵢ))·vᵢ = ∫(∂ₐuₐ)·vᵢ·wᵢ + ∫uₐ·vᵢ·(∂ₐwᵢ)`.
    rw [show (∫ x : Domain3, ((gradComp_of_memH1 u hu a a x).re * (L2VF_projComponentC_R3 i w x).re
          + (L2VF_projComponentC_R3 a u x).re * (gradComp_of_memH1 w hw a i x).re)
          * (L2VF_projComponentC_R3 i v x).re ∂(volume : Measure Domain3))
        = (∫ x : Domain3, (gradComp_of_memH1 u hu a a x).re * (L2VF_projComponentC_R3 i v x).re
            * (L2VF_projComponentC_R3 i w x).re ∂(volume : Measure Domain3))
          + ∫ x : Domain3, (L2VF_projComponentC_R3 a u x).re * (L2VF_projComponentC_R3 i v x).re
            * (gradComp_of_memH1 w hw a i x).re ∂(volume : Measure Domain3) from by
        rw [← MeasureTheory.integral_add hint1 hint2]
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        ring]
    ring
  -- Sum the per-(i,a) identity and distribute the sums.
  rw [convFormH1]
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun a _ => hpia i a))]
  simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib]

/-- **B6b `convFormH1_divFree` [must-prove].** The weak div-free identity for `H¹_σ` elements:
for `u ∈ L2Sigma_R3 ∩ H1Sigma_R3`, the weak divergence vanishes:

  `∑ a : Fin 3, ∫ x, (gradComp_of_memH1 u hu a a x).re * φ(x) dx = 0`

for any `v, w` in L² (as a consequence, `∑_a (∂_a uₐ) = 0` in the weak sense).

**Proof route:** `u ∈ L2Sigma_R3` means `divTestFunctional φ u = 0` for all Schwartz `φ`.
The weak derivative `gradComp_of_memH1 u hu a a` is the L² representative of `∂_{eₐ} uₐ`.
Summing over `a` and using the B2 IBP identity gives the weak div-free condition. -/
theorem convFormH1_divFree (u : L2VF_R3) (hu : memH1VF_R3 u)
    (hu_sigma : (u : L2VF_R3) ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3))
    (φ : SchwartzMap Domain3 ℝ) :
    ∑ a : Fin 3,
      ∫ x : Domain3,
        (gradComp_of_memH1 u hu a a x).re * (φ x)
      ∂(volume : Measure Domain3) = 0 := by
  -- u ∈ L2Sigma_R3 ⟹ divTestFunctional φ u = 0.
  have hdiv : divTestFunctional φ (u : L2VF_R3) = 0 :=
    LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp hu_sigma φ)
  -- Unfold: ∑ⱼ ⟪(∂ⱼφ).toLp, uⱼ⟫ = 0, and rewrite each inner product as an integral.
  simp only [divTestFunctional, ContinuousLinearMap.coe_sum', Finset.sum_apply,
    ContinuousLinearMap.coe_comp', Function.comp, innerSL_apply_apply] at hdiv
  -- Each inner ⟪(∂ₐφ).toLp, uₐ⟫ = ∫ (∂ₐφ x) · uₐ.re x  (real L²-inner as a pointwise integral).
  have hinner : ∀ a : Fin 3,
      (inner ℝ ((lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
            (EuclideanSpace.single a (1 : ℝ) : Domain3) φ).toLp 2 (volume : Measure Domain3))
          (L2VF_projComponent_R3 a (u : L2VF_R3)) : ℝ)
        = ∫ x : Domain3, (L2VF_projComponentC_R3 a u x).re *
            ((lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
              (EuclideanSpace.single a (1 : ℝ) : Domain3) φ) x)
            ∂(volume : Measure Domain3) := by
    intro a
    rw [MeasureTheory.L2.inner_def]
    refine MeasureTheory.integral_congr_ae ?_
    have hcomp : (⇑(L2VF_projComponentC_R3 a u) : Domain3 → ℂ) =ᵐ[volume]
        fun x => (((L2VF_projComponent_R3 a u) x : ℝ) : ℂ) := by
      rw [L2VF_projComponentC_R3]
      filter_upwards [ContinuousLinearMap.coeFn_compLpL
        (RCLike.ofRealCLM (K := ℂ)) (L2VF_projComponent_R3 a u)] with x hx
      simpa using hx
    filter_upwards [(lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
        (EuclideanSpace.single a (1 : ℝ) : Domain3) φ).coeFn_toLp 2 (volume : Measure Domain3),
      hcomp] with x hφx hux
    rw [Real.inner_apply, hφx, hux, Complex.ofReal_re]; ring
  simp_rw [hinner] at hdiv
  -- ∑ₐ ∫ gradComp_aa.re·φ = -∑ₐ ∫ uₐ.re·∂ₐφ = -0 = 0.
  have hB2 : ∀ a : Fin 3,
      ∫ x : Domain3, (gradComp_of_memH1 u hu a a x).re * (φ x) ∂(volume : Measure Domain3)
        = -∫ x : Domain3, (L2VF_projComponentC_R3 a u x).re *
            ((lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
              (EuclideanSpace.single a (1 : ℝ) : Domain3) φ) x)
            ∂(volume : Measure Domain3) := by
    intro a
    have := gradComponent_weakDeriv u hu a a φ
    linarith [this]
  rw [Finset.sum_congr rfl (fun a _ => hB2 a), Finset.sum_neg_distrib, hdiv, neg_zero]

/-- **H¹-test div-free.** The weak divergence of an `H¹_σ` element vanishes against ANY real
`L²` test `θ` (not just Schwartz): `∑ₐ ∫ (∂ₐuₐ).re·θ = 0`. Extended from `convFormH1_divFree`
(Schwartz tests) by `L²` density and continuity of the real `L²` inner product. -/
private theorem divFree_L2test (u : L2VF_R3) (hu : memH1VF_R3 u)
    (hu_sigma : (u : L2VF_R3) ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3))
    (θ : Lp ℝ 2 (volume : Measure Domain3)) :
    ∑ a : Fin 3, ∫ x : Domain3, (gradComp_of_memH1 u hu a a x).re * (θ x)
      ∂(volume : Measure Domain3) = 0 := by
  classical
  -- Express each summand as a real `L²` inner product `⟨reLp (∂ₐuₐ), θ⟩`.
  have hinner : ∀ (a : Fin 3) (η : Lp ℝ 2 (volume : Measure Domain3)),
      ∫ x : Domain3, (gradComp_of_memH1 u hu a a x).re * (η x) ∂(volume : Measure Domain3)
        = (inner ℝ (reLp (gradComp_of_memH1 u hu a a)) η : ℝ) := by
    intro a η
    rw [MeasureTheory.L2.inner_def]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [reLp_coeFn (gradComp_of_memH1 u hu a a)] with x hx
    rw [RCLike.inner_apply, conj_trivial, hx, mul_comm]
  -- The continuous functional `η ↦ ∑ₐ ⟨reLp (∂ₐuₐ), η⟩` vanishes on the dense Schwartz range.
  set G : Lp ℝ 2 (volume : Measure Domain3) →L[ℝ] ℝ :=
    ∑ a : Fin 3, innerSL ℝ (reLp (gradComp_of_memH1 u hu a a)) with hG
  have hGapply : ∀ η : Lp ℝ 2 (volume : Measure Domain3),
      G η = ∑ a : Fin 3, ∫ x : Domain3, (gradComp_of_memH1 u hu a a x).re * (η x)
        ∂(volume : Measure Domain3) := by
    intro η
    rw [hG, ContinuousLinearMap.coe_sum', Finset.sum_apply]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [innerSL_apply_apply, hinner a η]
  -- On Schwartz tests, `G (φ.toLp) = 0` (convFormH1_divFree).
  have hGzero_schwartz : ∀ φ : SchwartzMap Domain3 ℝ,
      G (φ.toLp 2 (volume : Measure Domain3)) = 0 := by
    intro φ
    rw [hGapply]
    have heq : ∀ a : Fin 3,
        ∫ x : Domain3, (gradComp_of_memH1 u hu a a x).re
          * ((φ.toLp 2 (volume : Measure Domain3)) x) ∂(volume : Measure Domain3)
          = ∫ x : Domain3, (gradComp_of_memH1 u hu a a x).re * (φ x)
          ∂(volume : Measure Domain3) := by
      intro a
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [φ.coeFn_toLp 2 (volume : Measure Domain3)] with x hx
      rw [hx]
    rw [Finset.sum_congr rfl (fun a _ => heq a)]
    exact convFormH1_divFree u hu hu_sigma φ
  -- `G = 0` on the dense Schwartz range, hence `G θ = 0`.
  have hGzero : G θ = 0 := by
    have hdr : DenseRange (SchwartzMap.toLpCLM ℝ ℝ (2 : ENNReal) (volume : Measure Domain3)) :=
      SchwartzMap.denseRange_toLpCLM (F := ℝ) ENNReal.ofNat_ne_top
    have hcont : Continuous (fun η => G η) := G.continuous
    refine (hdr.induction_on θ (isClosed_eq hcont continuous_const) ?_)
    intro φ
    exact hGzero_schwartz φ
  rw [← hGapply θ]; exact hGzero

/-- **B6 `convFormH1_antisymm` [must-prove].** `convFormH1` is antisymmetric in slots 2,3:

  `convFormH1 u v w hu hv hw = -convFormH1 u w v hu hw hv`

for `u, v, w ∈ H1Sigma_R3` with `u, v, w ∈ L2Sigma_R3`.

**Proof route:**
1. Apply B6a (IBP) to `convFormH1 u v w`: gives `= -(∑∑∫ ∂uₐ·vᵢ·wᵢ) - ∑∑∫ uₐ·vᵢ·∂wᵢ`.
2. The first term vanishes by B6b (div-free of u kills `∑_a ∂_a uₐ`).
   So `convFormH1 u v w = -∑_{i,a} ∫ uₐ · vᵢ · ∂ₐwᵢ`.
3. Similarly `convFormH1 u w v = -∑_{i,a} ∫ uₐ · wᵢ · ∂ₐvᵢ`.
4. Note `∑_{i,a} ∫ uₐ · vᵢ · ∂ₐwᵢ = -convFormH1 u w v`
   (because `convFormH1 u w v = ∑_{i,a} ∫ uₐ · ∂ₐwᵢ · vᵢ` before IBP, and after IBP equals
   `-∑∑∫ uₐ·wᵢ·∂ₐvᵢ` ... actually the symmetric argument gives `b(u,v,w) + b(u,w,v) = 0`).
   Concretely: B6a on `convFormH1 u v w` after div-free gives `-∑∑∫ uₐ·vᵢ·∂wᵢ`;
   and B6a on `convFormH1 u w v` after div-free gives `-∑∑∫ uₐ·wᵢ·∂vᵢ = -convFormH1 u v w`
   (by B6a + div-free), establishing `convFormH1 u v w = -convFormH1 u w v`. -/
theorem convFormH1_antisymm (u v w : L2VF_R3)
    (hu : memH1VF_R3 u) (hv : memH1VF_R3 v) (hw : memH1VF_R3 w)
    (hu_sigma : (u : L2VF_R3) ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3))
    (_hv_sigma : (v : L2VF_R3) ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3))
    (hw_sigma : (w : L2VF_R3) ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3)) :
    convFormH1 u v w hu hv hw = -convFormH1 u w v hu hw hv := by
  classical
  -- B6a (IBP): convFormH1 u v w = -(S1) - S2.
  rw [convFormH1_ibp u v w hu hv hw hu_sigma hw_sigma]
  -- S1 = ∑ᵢ ∑ₐ ∫(∂ₐuₐ)·vᵢ·wᵢ = 0 (div-free of u against the H¹ test vᵢ·wᵢ ∈ L²).
  have hS1 : (∑ i : Fin 3, ∑ a : Fin 3,
      ∫ x : Domain3, (gradComp_of_memH1 u hu a a x).re *
        (L2VF_projComponentC_R3 i v x).re * (L2VF_projComponentC_R3 i w x).re
        ∂(volume : Measure Domain3)) = 0 := by
    refine Finset.sum_eq_zero (fun i _ => ?_)
    -- For fixed i, the test `θᵢ = vᵢ.re·wᵢ.re ∈ L²` (L³·L⁶).
    haveI hHT362 : ENNReal.HolderTriple 6 3 2 := instHolderTriple_6_3_2
    have hθmem : MemLp (fun x => (L2VF_projComponentC_R3 i v x).re
        * (L2VF_projComponentC_R3 i w x).re) 2 (volume : Measure Domain3) :=
      MeasureTheory.MemLp.ae_eq
        (Filter.Eventually.of_forall fun x => by rw [Pi.mul_apply, mul_comm])
        ((memLp_three_componentRe v hv i).mul (p := 6) (q := 3) (r := 2)
          (memLp_six_componentRe w hw i))
    have hdf := divFree_L2test u hu hu_sigma hθmem.toLp
    -- rewrite the integrand using the L² test coeFn.
    refine Eq.trans (Finset.sum_congr rfl (fun a _ => ?_)) hdf
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hθmem.coeFn_toLp] with x hx
    rw [hx, ← mul_assoc]
  rw [hS1, neg_zero, zero_sub]
  -- Remaining: -∑ᵢ∑ₐ∫uₐ·vᵢ·(∂ₐwᵢ) = -convFormH1 u w v, i.e. the sum equals convFormH1 u w v.
  rw [neg_inj, convFormH1]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun a _ => ?_))
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  ring

/-! ### B7 — L²-norm bound for fixed Schwartz test (CODEX CORRECTION route) -/

/-- **B7 `convFormH1_bound_Schwartz` [must-prove — CODEX CORRECTION].** For fixed Schwartz
`w ∈ H1Sigma_R3`, there exists a constant `C_w ≥ 0` (depending only on `w` via `‖∇w‖_{L^∞}`)
such that for ALL `u, v ∈ H1Sigma_R3`:

  `|convFormH1 u v w hu hv hw_H1| ≤ C_w * ‖(u : L2VF_R3)‖ * ‖(v : L2VF_R3)‖`

The quantifier order is `∃ C_w, ∀ u v`, making `C_w` uniform in `u, v`.

**⚠️ CODEX CORRECTION (PR-1 #58 review, P1):** The original statement had `u,v` before `∃ C_w`,
allowing `C_w` to depend on `u,v` (nearly vacuous). The corrected statement quantifies `u,v`
universally *inside* after `∃ C_w`.

Route:
1. By B6 antisymmetry: `convFormH1 u v w = -convFormH1 u w v = +convFormH1_moveDeriv u v w`
   where `convFormH1_moveDeriv u v w = ∑_{i,a} ∫ uₐ · ∂ₐwᵢ · vᵢ`
   (derivative moved onto `w` via IBP).
2. Estimate: `|∑_{i,a} ∫ uₐ · ∂ₐwᵢ · vᵢ| ≤ ∑_{i,a} ‖∂ₐwᵢ‖_∞ · ‖uₐ‖_{L²} · ‖vᵢ‖_{L²}`
   (Cauchy–Schwarz: `|∫ f·g| ≤ ‖f‖_{L²}‖g‖_{L²}` with `f = uₐ`, `g = ∂ₐwᵢ · vᵢ`).
3. Since `w` is Schwartz, `‖∂ₐwᵢ‖_∞ < ∞`; set `C_w := ∑_{i,a} ‖∂ₐwᵢ‖_∞·‖projₐ‖·‖projᵢ‖`.
4. Use `‖uₐ‖_{L²} ≤ ‖projₐ‖·‖u‖_{L²}` and `‖vᵢ‖_{L²} ≤ ‖projᵢ‖·‖v‖_{L²}`.

**Note:** A3/GNS is NOT needed for B7 (per CODEX CORRECTION). The L²-bound is achieved
by moving ∂ onto the Schwartz test, not by invoking GNS on u,v. The `C_w` is finite
because w is Schwartz (all derivatives are in L^∞). -/
theorem convFormH1_bound_Schwartz (w : L2VF_R3)
    (hw_H1 : memH1VF_R3 w)
    (hw_sigma : (w : L2VF_R3) ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3))
    (hw_sch : IsSchwartzDivFree_R3 ⟨w, hw_sigma⟩) :
    ∃ C_w : ℝ, 0 ≤ C_w ∧
      ∀ (u v : L2VF_R3) (hu : memH1VF_R3 u) (hv : memH1VF_R3 v)
        (_hu_sigma : (u : L2VF_R3) ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3))
        (_hv_sigma : (v : L2VF_R3) ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3)),
        |convFormH1 u v w hu hv hw_H1| ≤ C_w * ‖(u : L2VF_R3)‖ * ‖(v : L2VF_R3)‖ := by
  classical
  -- `w` is Schwartz: `wᵢ.re = ψᵢ` a.e. for Schwartz `ψ`.
  obtain ⟨ψ, hψ⟩ := hw_sch
  -- The weak gradient `∂ₐwᵢ` equals the (Schwartz) classical derivative `∂ₐψᵢ` in `L²`.
  have hgrad_schwartz : ∀ a i : Fin 3,
      gradComp_of_memH1 w hw_H1 a i
        = (∂_{EuclideanSpace.single a (1 : ℝ)} (cxify (ψ i))).toLp 2 (volume : Measure Domain3) := by
    intro a i
    -- `wᵢ = (cxify ψᵢ).toLp`.
    have hwi : L2VF_projComponentC_R3 i w = (cxify (ψ i)).toLp 2 (volume : Measure Domain3) := by
      have hcomp : L2VF_projComponentC_R3 i w
          = (RCLike.ofRealCLM (K := ℂ)).compLpL 2 (volume : Measure Domain3)
              (L2VF_projComponent_R3 i w) := rfl
      rw [hcomp, hψ i]
      apply Lp.ext
      filter_upwards [ContinuousLinearMap.coeFn_compLpL (RCLike.ofRealCLM (K := ℂ))
          ((ψ i).toLp 2 (volume : Measure Domain3)),
        (ψ i).coeFn_toLp 2 (volume : Measure Domain3),
        (cxify (ψ i)).coeFn_toLp 2 (volume : Measure Domain3)] with x h1 h2 h3
      rw [h1, h2, h3, cxify_apply]; rfl
    -- spec: `∂ₐ(wᵢ:𝓢') = (gradComp:𝓢')`; and `∂ₐ((cxify ψᵢ).toLp:𝓢') = ((∂ₐcxify ψᵢ).toLp:𝓢')`.
    have hspec := gradComp_of_memH1_spec w hw_H1 a i
    rw [hwi] at hspec
    refine L2C_eq_of_toTempered_eq ?_
    rw [← hspec, MeasureTheory.Lp.toTemperedDistribution_toLp_eq (cxify (ψ i)),
      TemperedDistribution.lineDerivOp_toTemperedDistributionCLM_eq,
      ← MeasureTheory.Lp.toTemperedDistribution_toLp_eq (p := (2 : ENNReal))
        (∂_{EuclideanSpace.single a (1 : ℝ)} (cxify (ψ i)))]
  -- L^∞ membership of the real gradient `(∂ₐwᵢ).re` (it is a.e. a Schwartz function).
  have hgrad_bdd : ∀ a i : Fin 3,
      MemLp (fun x => (gradComp_of_memH1 w hw_H1 a i x).re) ⊤ (volume : Measure Domain3) := by
    intro a i
    set χ : SchwartzMap Domain3 ℂ := ∂_{EuclideanSpace.single a (1 : ℝ)} (cxify (ψ i)) with hχ
    have hmem : MemLp (fun x => (χ x).re) ⊤ (volume : Measure Domain3) :=
      ((χ.memLp ⊤ (volume : Measure Domain3)).re)
    refine hmem.ae_eq ?_
    filter_upwards [(by rw [hgrad_schwartz a i] :
        (gradComp_of_memH1 w hw_H1 a i : Domain3 → ℂ)
          =ᵐ[volume] ⇑(χ.toLp 2 (volume : Measure Domain3))),
      χ.coeFn_toLp 2 (volume : Measure Domain3)] with x hx hx2
    rw [hx, hx2]
  -- Define C_w from w alone: sum of per-(a,i) L^∞-gradient × projector-norm products.
  set Kw : Fin 3 → Fin 3 → ℝ := fun a i =>
    (eLpNorm (fun x => (gradComp_of_memH1 w hw_H1 a i x).re) ⊤ (volume : Measure Domain3)).toReal
      * ‖L2VF_projComponentC_R3 a‖ * ‖L2VF_projComponentC_R3 i‖ with hKw
  have hKw_nonneg : ∀ a i, 0 ≤ Kw a i := by
    intro a i; rw [hKw]; positivity
  -- Provide C_w and prove nonnegativity; then universally quantify over u, v.
  refine ⟨∑ i : Fin 3, ∑ a : Fin 3, Kw a i, ?_, ?_⟩
  · exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun a _ => hKw_nonneg a i))
  -- Now prove the bound for arbitrary u, v.
  intro u v hu hv hu_sigma hv_sigma
  -- per-(i,a) bound: |∫ uₐ.re·(∂ₐwᵢ).re·vᵢ.re| ≤ Kᵢₐ·‖u‖·‖v‖.
  have hterm : ∀ i a : Fin 3,
      |∫ x : Domain3, (L2VF_projComponentC_R3 a u x).re *
        (gradComp_of_memH1 w hw_H1 a i x).re * (L2VF_projComponentC_R3 i v x).re
        ∂(volume : Measure Domain3)|
      ≤ Kw a i * ‖(u : L2VF_R3)‖ * ‖(v : L2VF_R3)‖ := by
    intro i a
    set hh := hgrad_bdd a i with hhdef
    -- `∫ uₐ.re·gradComp.re·vᵢ.re = ⟨reLp uₐ, mulRBdd gradComp.re (reLp vᵢ)⟩`.
    have hint_eq : ∫ x : Domain3, (L2VF_projComponentC_R3 a u x).re *
          (gradComp_of_memH1 w hw_H1 a i x).re * (L2VF_projComponentC_R3 i v x).re
          ∂(volume : Measure Domain3)
        = (inner ℝ (reLp (L2VF_projComponentC_R3 a u))
            (mulRBdd (fun x => (gradComp_of_memH1 w hw_H1 a i x).re) hh
              (reLp (L2VF_projComponentC_R3 i v))) : ℝ) := by
      rw [← integral_mul_mul_eq_inner (fun x => (gradComp_of_memH1 w hw_H1 a i x).re) hh
        (reLp (L2VF_projComponentC_R3 a u)) (reLp (L2VF_projComponentC_R3 i v))]
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [reLp_coeFn (L2VF_projComponentC_R3 a u),
        reLp_coeFn (L2VF_projComponentC_R3 i v)] with x h1 h2
      rw [h1, h2]; ring
    rw [hint_eq]
    -- Cauchy–Schwarz + multiplier bound + component contraction.
    set Mw : ℝ := (eLpNorm (fun x => (gradComp_of_memH1 w hw_H1 a i x).re) ⊤
      (volume : Measure Domain3)).toReal with hMw
    have hMw_nonneg : 0 ≤ Mw := by rw [hMw]; exact ENNReal.toReal_nonneg
    refine (abs_real_inner_le_norm _ _).trans ?_
    have hmul_le : ‖mulRBdd (fun x => (gradComp_of_memH1 w hw_H1 a i x).re) hh
        (reLp (L2VF_projComponentC_R3 i v))‖ ≤ Mw * ‖reLp (L2VF_projComponentC_R3 i v)‖ :=
      norm_mulRBdd_le _ hh _
    have hua : ‖reLp (L2VF_projComponentC_R3 a u)‖ ≤ ‖L2VF_projComponentC_R3 a‖ * ‖(u : L2VF_R3)‖ :=
      (norm_reLp_le _).trans ((L2VF_projComponentC_R3 a).le_opNorm (u : L2VF_R3))
    have hvi : ‖reLp (L2VF_projComponentC_R3 i v)‖ ≤ ‖L2VF_projComponentC_R3 i‖ * ‖(v : L2VF_R3)‖ :=
      (norm_reLp_le _).trans ((L2VF_projComponentC_R3 i).le_opNorm (v : L2VF_R3))
    calc ‖reLp (L2VF_projComponentC_R3 a u)‖
          * ‖mulRBdd (fun x => (gradComp_of_memH1 w hw_H1 a i x).re) hh
              (reLp (L2VF_projComponentC_R3 i v))‖
        ≤ (‖L2VF_projComponentC_R3 a‖ * ‖(u : L2VF_R3)‖)
            * (Mw * (‖L2VF_projComponentC_R3 i‖ * ‖(v : L2VF_R3)‖)) := by
          refine mul_le_mul hua (hmul_le.trans ?_) (norm_nonneg _) (by positivity)
          exact mul_le_mul_of_nonneg_left hvi hMw_nonneg
      _ = Kw a i * ‖(u : L2VF_R3)‖ * ‖(v : L2VF_R3)‖ := by rw [hKw]; ring
  -- `convFormH1 u v w = -convFormH1 u w v = -∑ᵢ∑ₐ ∫ uₐ·vᵢ·(∂ₐwᵢ)`.
  rw [convFormH1_antisymm u v w hu hv hw_H1 hu_sigma hv_sigma hw_sigma, abs_neg, convFormH1]
  -- `|∑ᵢ∑ₐ Tᵢₐ| ≤ ∑ᵢ∑ₐ |Tᵢₐ| ≤ ∑ᵢ∑ₐ Kw·‖u‖·‖v‖`.
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_le_sum (fun i _ => ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_le_sum (fun a _ => ?_)
  exact hterm i a

end LerayHopf
