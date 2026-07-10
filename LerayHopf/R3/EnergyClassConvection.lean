import LerayHopf.R3.SobolevEmbedding
import LerayHopf.R3.ConvectionOperator
import LerayHopf.Analysis.PlancherelKernels
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

/-! ### B1 — The H¹_σ submodule of `L2VF_R3` -/

/-! #### B1a — `memH1VF_R3` is closed under addition -/

/-- **B1a.** If `u, v ∈ L2VF_R3` both satisfy `memH1VF_R3`, then so does `u + v`.

Proof: `L2VF_projComponentC_R3 j` is ℝ-linear, so the j-th component of `u + v` equals
the sum of the j-th components of `u` and `v`. Then `MemSobolev.add` closes the goal. -/
theorem memH1VF_R3_add {u v : L2VF_R3} (hu : memH1VF_R3 u) (hv : memH1VF_R3 v) :
    memH1VF_R3 (u + v) := by
  intro j
  -- L2VF_projComponentC_R3 j is ℝ-linear, so map_add applies.
  have hadd : L2VF_projComponentC_R3 j (u + v) =
      L2VF_projComponentC_R3 j u + L2VF_projComponentC_R3 j v :=
    map_add _ u v
  -- The coercion Lp F p μ → 𝓢'(E, F) is additive via Lp.toTemperedDistributionCLM.map_add'.
  -- Concretely: (f + g : Lp) as 𝓢' = (f : 𝓢') + (g : 𝓢').
  have hcoe_add : (L2VF_projComponentC_R3 j (u + v) : 𝓢'(Domain3, ℂ)) =
      (L2VF_projComponentC_R3 j u : 𝓢'(Domain3, ℂ)) +
      (L2VF_projComponentC_R3 j v : 𝓢'(Domain3, ℂ)) := by
    -- (f + g : Lp) maps to (f : 𝓢') + (g : 𝓢') via the additive map Lp.toTemperedDistribution.
    simp only [hadd]
    exact (MeasureTheory.Lp.toTemperedDistributionCLM ℂ (volume : Measure Domain3) 2).map_add
      (L2VF_projComponentC_R3 j u) (L2VF_projComponentC_R3 j v)
  rw [hcoe_add]
  exact (hu j).add (hv j)

/-! #### B1b — `memH1VF_R3` is closed under real scalar multiplication -/

/-- **B1b.** If `u ∈ L2VF_R3` satisfies `memH1VF_R3 u`, then so does `c • u` for any `c : ℝ`.

Proof: `L2VF_projComponentC_R3 j (c • u) = c • L2VF_projComponentC_R3 j u` (ℝ-linearity).
The Lp coercion `(c • f : Lp ℂ 2 μ) = (c : ℂ) • f` as tempered distributions
(since `c` acts via real scalar multiplication, which equals complex multiplication by `c`).
Then `MemSobolev.smul (c : ℂ)` closes the goal. -/
theorem memH1VF_R3_smul {u : L2VF_R3} (c : ℝ) (hu : memH1VF_R3 u) :
    memH1VF_R3 (c • u) := by
  intro j
  have hsmul : L2VF_projComponentC_R3 j (c • u) = c • L2VF_projComponentC_R3 j u :=
    map_smul _ c u
  -- We need (c • f : Lp ℂ 2) as 𝓢' = (c : ℂ) • (f : 𝓢').
  -- Lp.toTemperedDistributionCLM is ℂ-linear; the ℝ-scalar action on Lp ℂ 2 satisfies
  -- c • f = (c : ℂ) • f (since ℂ is an ℝ-algebra and ℝ-action = complex multiplication by c).
  -- We need (c • f : Lp ℂ 2) as 𝓢' = (c : ℂ) • (f : 𝓢').
  -- Lp.toTemperedDistributionCLM is ℂ-linear. For c : ℝ acting on Lp ℂ 2,
  -- the ℝ-scalar action satisfies c • f = (c : ℂ) • f (real scalar = complex multiplication by c ↑ ℂ).
  -- Concretely, Lp.toTemperedDistribution (c • f) = (c : ℂ) • Lp.toTemperedDistribution f.
  rw [show (L2VF_projComponentC_R3 j (c • u) : 𝓢'(Domain3, ℂ)) =
        (c : ℂ) • (L2VF_projComponentC_R3 j u : 𝓢'(Domain3, ℂ)) from by
    rw [hsmul]
    -- The coercion Lp F p μ → 𝓢' satisfies: (r • f : Lp ℂ 2) ↦ (r : ℂ) • (f : 𝓢').
    -- Use that the CLM map_smul gives this.
    have := (MeasureTheory.Lp.toTemperedDistributionCLM ℂ (volume : Measure Domain3) 2).map_smul
      (c : ℂ) (L2VF_projComponentC_R3 j u)
    simp only [MeasureTheory.Lp.toTemperedDistributionCLM_apply] at this
    -- After applying the CLM map_smul, we have:
    -- this : Lp.toTemperedDistribution ((c : ℂ) • f) = (c : ℂ) • Lp.toTemperedDistribution f
    -- Goal: Lp.toTemperedDistribution (c • f) = (c : ℂ) • Lp.toTemperedDistribution f
    -- Here c • f (ℝ-scalar) = (c : ℂ) • f (ℂ-scalar) as Lp elements.
    rw [← algebraMap_smul ℂ c (L2VF_projComponentC_R3 j u)]
    exact this]
  exact (hu j).smul (c : ℂ)

/-! #### B1c — `memH1VF_R3` holds for the zero element -/

/-- **B1c.** `memH1VF_R3 (0 : L2VF_R3)`.

Proof: the j-th component of `0` is `0`, and `memSobolev_fun_zero` gives `MemSobolev 1 2 0`. -/
theorem memH1VF_R3_zero : memH1VF_R3 (0 : L2VF_R3) := by
  intro j
  -- L2VF_projComponentC_R3 j 0 = 0 (CLM preserves zero).
  have hzero : L2VF_projComponentC_R3 j (0 : L2VF_R3) = 0 := map_zero _
  have hcoe_zero : (L2VF_projComponentC_R3 j (0 : L2VF_R3) : 𝓢'(Domain3, ℂ)) = 0 := by
    rw [hzero]
    exact (MeasureTheory.Lp.toTemperedDistributionCLM ℂ (volume : Measure Domain3) 2).map_zero
  rw [hcoe_zero]
  -- memSobolev_fun_zero : MemSobolev s p (0 : 𝓢'(E, F)) for any s, p.
  exact TemperedDistribution.memSobolev_fun_zero Domain3 ℂ 1 2

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

/-! ### Helpers — complexification of real Schwartz tests -/

/-- Complexification of a real Schwartz map: post-compose with `ofRealCLM : ℝ →L[ℝ] ℂ`. -/
private noncomputable def cxify (φ : SchwartzMap Domain3 ℝ) : SchwartzMap Domain3 ℂ :=
  φ.postcompCLM (RCLike.ofRealCLM (K := ℂ))

@[simp] private theorem cxify_apply (φ : SchwartzMap Domain3 ℝ) (x : Domain3) :
    cxify φ x = ((φ x : ℝ) : ℂ) := by
  simp [cxify, SchwartzMap.postcompCLM_apply]

/-- Complexification commutes with the line derivative: `∂_{m}(cxify φ) = cxify (∂_{m} φ)`.
Both sides agree pointwise: `lineDeriv` commutes with the `ℝ`-linear map `ofRealCLM`. -/
private theorem lineDerivOp_cxify (m : Domain3) (φ : SchwartzMap Domain3 ℝ) :
    (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℂ) m) (cxify φ)
      = cxify ((lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ) m) φ) := by
  apply SchwartzMap.ext
  intro x
  rw [LineDeriv.lineDerivOpCLM_apply, LineDeriv.lineDerivOpCLM_apply,
    SchwartzMap.lineDerivOp_apply, cxify_apply, SchwartzMap.lineDerivOp_apply]
  -- Goal: lineDeriv ℝ (cxify φ) x m = ofReal (lineDeriv ℝ φ x m)
  have hL : HasLineDerivAt ℝ (fun y => φ y) (lineDeriv ℝ (fun y => φ y) x m) x m :=
    (φ.differentiableAt.lineDifferentiableAt).hasLineDerivAt
  have hcx : (fun y => cxify φ y) = fun y => RCLike.ofRealCLM (K := ℂ) (φ y) :=
    funext fun y => by rw [cxify_apply]; rfl
  have hLcx : HasLineDerivAt ℝ (fun y => cxify φ y)
      (RCLike.ofRealCLM (K := ℂ) (lineDeriv ℝ (fun y => φ y) x m)) x m := by
    rw [hcx]
    exact (RCLike.ofRealCLM (K := ℂ)).hasFDerivAt.comp_hasDerivAt _ hL
  rw [hLcx.lineDeriv]
  rfl

/-! ### B2 — Spectral weak-gradient component and IBP identity -/

/-- **B2 helper `gradComp_of_memH1`** — the spectral L² weak-derivative representative.

For `u : L2VF_R3` with `memH1VF_R3 u`, the j-th Sobolev component satisfies
`MemSobolev 1 2 (L2VF_projComponentC_R3 j u)`. Applying `MemSobolev.lineDerivOp` at
`m = EuclideanSpace.single a 1` yields `MemSobolev 0 2 (∂_{eₐ} (L2VF_projComponentC_R3 j u))`,
and `memSobolev_zero_iff` gives an `L²` representative.

`gradComp_of_memH1 u hu a j` is the L²(ℝ³; ℂ) representative of the weak
directional derivative `∂_{eₐ}` of the j-th component of `u`. -/
noncomputable def gradComp_of_memH1 (u : L2VF_R3) (hu : memH1VF_R3 u) (a j : Fin 3) :
    L2C_R3 :=
  -- MemSobolev 1 2 on j-th component → MemSobolev (1-1) 2 on the directional derivative.
  -- Note: MemSobolev.lineDerivOp gives MemSobolev (s-1) 2; here s = 1 so we get (1-1) = 0.
  have hderiv : TemperedDistribution.MemSobolev 0 2
      (∂_{EuclideanSpace.single a (1 : ℝ)} (L2VF_projComponentC_R3 j u : 𝓢'(Domain3, ℂ))) := by
    have h := (hu j).lineDerivOp (m := EuclideanSpace.single a (1 : ℝ))
    -- h : MemSobolev (1 - 1) 2 ...  but 1 - 1 = 0 in ℝ.
    norm_num at h
    exact h
  -- MemSobolev 0 2 ↔ ∃ f' : L2C_R3, f = f' — extract the L² representative.
  (TemperedDistribution.memSobolev_zero_iff.mp hderiv).choose

/-- The defining spectral identity of `gradComp_of_memH1`: as a tempered distribution it is the
line derivative `∂_{eₐ}` of the j-th complex component of `u`. -/
theorem gradComp_of_memH1_spec (u : L2VF_R3) (hu : memH1VF_R3 u) (a j : Fin 3) :
    (∂_{EuclideanSpace.single a (1 : ℝ)}
        (L2VF_projComponentC_R3 j u : 𝓢'(Domain3, ℂ)))
      = (gradComp_of_memH1 u hu a j : 𝓢'(Domain3, ℂ)) := by
  have hderiv : TemperedDistribution.MemSobolev 0 2
      (∂_{EuclideanSpace.single a (1 : ℝ)} (L2VF_projComponentC_R3 j u : 𝓢'(Domain3, ℂ))) := by
    have h := (hu j).lineDerivOp (m := EuclideanSpace.single a (1 : ℝ)); norm_num at h; exact h
  exact (TemperedDistribution.memSobolev_zero_iff.mp hderiv).choose_spec

/-- **B2 `gradComponent_weakDeriv` [must-prove].** The spectral weak-derivative L²
representative satisfies the integration-by-parts identity: for any Schwartz test function
`φ : 𝓢(Domain3, ℝ)`,

  `∫ (L2VF_projComponentC_R3 j u x).re * (∂ₐ φ)(x) dx =
    -∫ (gradComp_of_memH1 u hu a j x).re * φ(x) dx`

This is the weak (distributional) definition of `∂ₐ`, transported from the Schwartz
tempered-distribution IBP through the Lp coercion.

**Proof route (for prover):** unfold `gradComp_of_memH1`, use
`TemperedDistribution.memSobolev_zero_iff.mp (hu j).lineDerivOp` to get the representative;
the IBP identity follows from the definition of the distributional derivative as the
adjoint of `∂ₐ` under the Fourier pairing, combined with the `Lp.toTemperedDistributionCLM`
coercion and the classical Schwartz IBP
`SchwartzMap.integral_mul_lineDerivOp_right_eq_neg_left` on the L² level. -/
theorem gradComponent_weakDeriv (u : L2VF_R3) (hu : memH1VF_R3 u) (a j : Fin 3)
    (φ : SchwartzMap Domain3 ℝ) :
    ∫ x : Domain3,
      (L2VF_projComponentC_R3 j u x).re *
        (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
          (EuclideanSpace.single a (1 : ℝ) : Domain3) φ) x
      ∂(volume : Measure Domain3) =
    -∫ x : Domain3,
      (gradComp_of_memH1 u hu a j x).re * (φ x)
      ∂(volume : Measure Domain3) := by
  classical
  set m : Domain3 := EuclideanSpace.single a (1 : ℝ) with hm
  set uC : L2C_R3 := L2VF_projComponentC_R3 j u with huC
  set gC : L2C_R3 := gradComp_of_memH1 u hu a j with hgC
  -- The defining spectral identity: ∂_{m}(uC : 𝓢') = (gC : 𝓢').
  have hspec : (∂_{m} (uC : 𝓢'(Domain3, ℂ))) = (gC : 𝓢'(Domain3, ℂ)) :=
    gradComp_of_memH1_spec u hu a j
  -- Pair both sides against the complex test g := cxify φ.
  set g : SchwartzMap Domain3 ℂ := cxify φ with hg
  have hpair : (∂_{m} (uC : 𝓢'(Domain3, ℂ))) g = (gC : 𝓢'(Domain3, ℂ)) g :=
    congrArg (fun (T : 𝓢'(Domain3, ℂ)) => T g) hspec
  -- LHS pairing: ∂_{m}(uC) g = uC (-∂_{m} g) = -∫ (∂_{m} g x) • uC x.
  rw [TemperedDistribution.lineDerivOp_apply_apply] at hpair
  rw [MeasureTheory.Lp.toTemperedDistribution_apply,
      MeasureTheory.Lp.toTemperedDistribution_apply] at hpair
  -- Simplify -∂_{m} g = -(cxify (∂_{m} φ)).
  have hng : (- ∂_{m} g) = - cxify ((lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ) m) φ) := by
    have := lineDerivOp_cxify m φ
    rw [LineDeriv.lineDerivOpCLM_apply] at this
    rw [hg, this]
  rw [hng] at hpair
  -- a.e. pointwise identity for `uC`: uC x = ofReal (realComp x), where realComp = proj j (u x).
  set dphi : SchwartzMap Domain3 ℝ := (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ) m) φ with hdphi
  -- coeFn of uC: it is the complex embedding of the real component.
  have huC_ae : (fun x => (uC x)) =ᵐ[volume]
      fun x => (((L2VF_projComponent_R3 j u) x : ℝ) : ℂ) := by
    have h1 : (uC : Domain3 → ℂ) =ᵐ[volume]
        fun x => (RCLike.ofRealCLM (K := ℂ)) ((L2VF_projComponent_R3 j u) x) := by
      rw [huC, L2VF_projComponentC_R3]
      exact ContinuousLinearMap.coeFn_compLpL _ _
    filter_upwards [h1] with x hx
    simpa using hx
  -- The pairing equality, with the explicit complex integrands.
  -- LHS integrand: (-(cxify dphi) x) • uC x = ofReal (-(dphi x) * realComp x).
  have hLHS : (fun x => (- cxify dphi) x • uC x) =ᵐ[volume]
      fun x => ((-(dphi x) * ((L2VF_projComponent_R3 j u) x) : ℝ) : ℂ) := by
    filter_upwards [huC_ae] with x hx
    simp only [SchwartzMap.neg_apply, cxify_apply, hx, smul_eq_mul]
    push_cast; ring
  -- RHS integrand: g x • gC x = ofReal (φ x) * gC x.
  have hRHS : (fun x => g x • gC x) =ᵐ[volume]
      fun x => ((φ x : ℝ) : ℂ) * gC x := by
    filter_upwards with x
    simp only [hg, cxify_apply, smul_eq_mul]
  rw [MeasureTheory.integral_congr_ae hLHS, MeasureTheory.integral_congr_ae hRHS] at hpair
  -- RHS integrability: cxify φ ∈ L², gC ∈ L², product ∈ L¹.
  have hint_RHS : Integrable (fun x => ((φ x : ℝ) : ℂ) * gC x) (volume : Measure Domain3) := by
    have hmemφ : MemLp (fun x => ((φ x : ℝ) : ℂ)) 2 (volume : Measure Domain3) :=
      MemLp.ae_eq (by filter_upwards with x; rw [cxify_apply])
        ((cxify φ).memLp 2 (volume : Measure Domain3))
    have hmemg : MemLp (fun x => gC x) 2 (volume : Measure Domain3) := Lp.memLp gC
    have := hmemg.mul hmemφ (p := 2) (q := 2) (r := 1)
    exact (memLp_one_iff_integrable.mp this)
  -- Take real parts of hpair (an equality of complex numbers).
  have hpair_re := congrArg Complex.re hpair
  conv_lhs at hpair_re => rw [integral_complex_ofReal, Complex.ofReal_re]
  -- Convert the RHS real-part-of-integral into integral-of-real-part.
  have hRHS_re : (∫ x : Domain3, ((φ x : ℝ) : ℂ) * gC x).re
      = ∫ x : Domain3, (φ x) * (gC x).re := by
    rw [← RCLike.re_to_complex, ← integral_re hint_RHS]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show (((φ x : ℝ) : ℂ) * gC x).re = (φ x) * (gC x).re
    rw [Complex.re_ofReal_mul]
  rw [hRHS_re] at hpair_re
  -- hpair_re : ∫ -(dphi x)·realComp x = ∫ φ x · (gC x).re.
  -- Goal: ∫ (uC x).re · (dphi x) = -∫ (gC x).re · φ x.
  -- Rewrite the goal's LHS integrand (uC x).re = realComp x (a.e.), and the dphi.
  have hgoal_lhs : (fun x => (uC x).re * (dphi x))
      =ᵐ[volume] fun x => (dphi x) * ((L2VF_projComponent_R3 j u) x) := by
    filter_upwards [huC_ae] with x hx
    rw [hx, Complex.ofReal_re]; ring
  rw [MeasureTheory.integral_congr_ae hgoal_lhs]
  -- Now goal: ∫ dphi·realComp = -∫ (gC x).re · φ x.
  -- hpair_re : ∫ (-dphi x)·realComp x = ∫ φ x · (gC x).re.
  have hL : ∫ x : Domain3, (dphi x) * ((L2VF_projComponent_R3 j u) x)
      = -∫ x : Domain3, (-dphi x) * ((L2VF_projComponent_R3 j u) x) := by
    rw [← MeasureTheory.integral_neg]; congr 1; funext x; ring
  have hR : ∫ x : Domain3, (gC x).re * (φ x)
      = ∫ x : Domain3, (φ x) * (gC x).re := by
    congr 1; funext x; ring
  rw [hL, hpair_re, hR]

/-- Injectivity of the `Lp → 𝓢'` embedding: equal tempered distributions ⟹ equal `Lp` elements. -/
private theorem L2C_eq_of_toTempered_eq {f g : L2C_R3}
    (h : (f : 𝓢'(Domain3, ℂ)) = (g : 𝓢'(Domain3, ℂ))) : f = g := by
  have hker := MeasureTheory.Lp.ker_toTemperedDistributionCLM_eq_bot
    (F := ℂ) (μ := (volume : Measure Domain3)) (p := 2)
  have : (MeasureTheory.Lp.toTemperedDistributionCLM ℂ (volume : Measure Domain3) 2) (f - g) = 0 := by
    rw [map_sub]
    simp only [MeasureTheory.Lp.toTemperedDistributionCLM_apply]
    rw [sub_eq_zero]; exact h
  have hmem : (f - g) ∈ (MeasureTheory.Lp.toTemperedDistributionCLM
      ℂ (volume : Measure Domain3) 2).ker := this
  rw [hker] at hmem
  rw [Submodule.mem_bot] at hmem
  exact sub_eq_zero.mp hmem

/-- The weak gradient component is additive in the field: `gradComp(v+v') = gradComp v + gradComp v'`. -/
theorem gradComp_of_memH1_add (v v' : L2VF_R3) (hv : memH1VF_R3 v) (hv' : memH1VF_R3 v')
    (a i : Fin 3) :
    gradComp_of_memH1 (v + v') (memH1VF_R3_add hv hv') a i
      = gradComp_of_memH1 v hv a i + gradComp_of_memH1 v' hv' a i := by
  apply L2C_eq_of_toTempered_eq
  rw [← gradComp_of_memH1_spec]
  -- ∂_{eₐ}((v+v')ᵢC) = ∂_{eₐ}(vᵢC) + ∂_{eₐ}(v'ᵢC)
  have hcomp : (L2VF_projComponentC_R3 i (v + v') : 𝓢'(Domain3, ℂ))
      = (L2VF_projComponentC_R3 i v : 𝓢'(Domain3, ℂ))
        + (L2VF_projComponentC_R3 i v' : 𝓢'(Domain3, ℂ)) := by
    rw [map_add]
    exact (MeasureTheory.Lp.toTemperedDistributionCLM ℂ (volume : Measure Domain3) 2).map_add _ _
  rw [hcomp, lineDerivOp_add]
  rw [gradComp_of_memH1_spec v hv a i, gradComp_of_memH1_spec v' hv' a i]
  exact ((MeasureTheory.Lp.toTemperedDistributionCLM ℂ (volume : Measure Domain3) 2).map_add _ _).symm

/-- The weak gradient component is ℝ-homogeneous in the field: `gradComp(c•v) = c • gradComp v`. -/
theorem gradComp_of_memH1_smul (c : ℝ) (v : L2VF_R3) (hv : memH1VF_R3 v) (a i : Fin 3) :
    gradComp_of_memH1 (c • v) (memH1VF_R3_smul c hv) a i
      = (c : ℂ) • gradComp_of_memH1 v hv a i := by
  apply L2C_eq_of_toTempered_eq
  rw [← gradComp_of_memH1_spec]
  have hcomp : (L2VF_projComponentC_R3 i (c • v) : 𝓢'(Domain3, ℂ))
      = (c : ℂ) • (L2VF_projComponentC_R3 i v : 𝓢'(Domain3, ℂ)) := by
    rw [map_smul]
    have := (MeasureTheory.Lp.toTemperedDistributionCLM ℂ (volume : Measure Domain3) 2).map_smul
      (c : ℂ) (L2VF_projComponentC_R3 i v)
    simp only [MeasureTheory.Lp.toTemperedDistributionCLM_apply] at this
    rw [← algebraMap_smul ℂ c (L2VF_projComponentC_R3 i v)]; exact this
  rw [hcomp, lineDerivOp_smul, gradComp_of_memH1_spec v hv a i]
  have := (MeasureTheory.Lp.toTemperedDistributionCLM ℂ (volume : Measure Domain3) 2).map_smul
    (c : ℂ) (gradComp_of_memH1 v hv a i)
  simp only [MeasureTheory.Lp.toTemperedDistributionCLM_apply] at this
  exact this.symm

/-! ### B3a — `L²∩L⁶↪L³` interpolation -/

/-- **B3a `L2L6_inter_mem_L3` [must-prove].** If `f : Domain3 → F` satisfies
both `MemLp f 2 volume` and `MemLp f 6 volume`, then `MemLp f 3 volume`.

This is the Lp log-convexity / Hölder interpolation at exponent `3` between `2` and `6`:
`1/3 = θ/2 + (1-θ)/6` with `θ = 2/3`; equivalently, `‖f‖_{L³} ≤ ‖f‖_{L²}^{2/3} · ‖f‖_{L⁶}^{1/3}`.

**Proof route (for prover):** Apply `MeasureTheory.eLpNorm'_le_eLpNorm'_mul_eLpNorm'`
(mathlib `LpSeminorm/CompareExp.lean:206`) with `r = 3`, `p = 6`, `q = 2`:
  `‖f‖_{L³} = ‖f·f^0‖_{L³} ≤ ‖f‖_{L⁶} · ‖1‖_{L²}` — but this is not the right split.

Actually the correct interpolation is via Hölder with pointwise `|f|^(1/3)·|f|^(2/3)`:
split `f = f · 1` and use the `HolderTriple (6 : ENNReal) (2 : ENNReal) (3 : ENNReal)`
instance together with `eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm` from
`LpSeminorm/CompareExp.lean:229`. The instance `HolderTriple 6 2 3` follows from
`1/6 + 1/2 = 2/3` — wait, that's `HolderTriple 6 2 (3/2)` not `3`. Let me reconsider:

The interpolation `L²∩L⁶↪L³` holds by Hölder with:
`∫|f|³ = ∫|f|^(3/2) · |f|^(3/2) ≤ (∫|f|²)^(3/4) · (∫|f|⁶)^(1/4)` (Cauchy–Schwarz)
giving `‖f‖_{L³}³ ≤ ‖f‖_{L²}^(3/2) · ‖f‖_{L⁶}^(3/2)`, so `‖f‖_{L³} ≤ ‖f‖_{L²}^{1/2} · ‖f‖_{L⁶}^{1/2}`.
Or equivalently `eLpNorm f 3 ≤ (eLpNorm f 2)^(1/2) · (eLpNorm f 6)^(1/2)`.

⚠️ NOTE for prover: The plan cites `eLpNorm_le_eLpNorm_pow_mul_eLpNorm` which does NOT exist
in mathlib. Use `MeasureTheory.eLpNorm'_le_eLpNorm'_mul_eLpNorm'` (with the A1 instances)
or the Cauchy–Schwarz approach above via `MeasureTheory.inner_mul_le_norm_mul_norm`. -/
theorem L2L6_inter_mem_L3 {F : Type*} [NormedAddCommGroup F] (f : Domain3 → F)
    (h2 : MemLp f 2 (volume : Measure Domain3))
    (h6 : MemLp f 6 (volume : Measure Domain3)) :
    MemLp f 3 (volume : Measure Domain3) := by
  -- Work with the real-valued norm function `g x = ‖f x‖`.
  set g : Domain3 → ℝ := fun x => ‖f x‖ with hg
  have hg2 : MemLp g 2 (volume : Measure Domain3) := h2.norm
  have hg6 : MemLp g 6 (volume : Measure Domain3) := h6.norm
  -- `g * g ∈ L^{3/2}` by Hölder with `1/6 + 1/2 = 2/3 = 1/(3/2)`.
  haveI : ENNReal.HolderTriple 6 2 (3 / 2) := by
    have h : Real.HolderTriple (6 : ℝ) (2 : ℝ) (3 / 2 : ℝ) := by
      constructor <;> norm_num
    have h2 := h.ennrealOfReal
    have e32 : ENNReal.ofReal (3 / 2 : ℝ) = (3 / 2 : ENNReal) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp
    simp only [ENNReal.ofReal_ofNat, e32] at h2
    exact h2
  have hgg : MemLp (g * g) (3 / 2) (volume : Measure Domain3) := hg6.mul hg2
  -- Identify `g * g` with `fun x => ‖f x‖ ^ (2 : ℝ)` and use `eLpNorm_norm_rpow`.
  have hsm : AEStronglyMeasurable f (volume : Measure Domain3) := h2.aestronglyMeasurable
  refine ⟨hsm, ?_⟩
  -- `eLpNorm f 3 < ∞` from `(eLpNorm f 3) ^ 2 = eLpNorm (fun x => ‖f x‖ ^ 2) (3/2) < ∞`.
  have hpow : (fun x => ‖f x‖ ^ (2 : ℝ)) = (g * g) := by
    funext x; simp [hg, Pi.mul_apply, Real.rpow_natCast, sq]
  have hkey : eLpNorm (fun x => ‖f x‖ ^ (2 : ℝ)) (3 / 2) (volume : Measure Domain3)
      = eLpNorm f ((3 / 2) * ENNReal.ofReal 2) (volume : Measure Domain3) ^ (2 : ℝ) :=
    eLpNorm_norm_rpow f (by norm_num)
  have h32 : ((3 : ENNReal) / 2) * ENNReal.ofReal 2 = 3 := by
    rw [show ENNReal.ofReal 2 = (2 : ENNReal) by norm_num [ENNReal.ofReal]]
    rw [ENNReal.div_mul_cancel] <;> norm_num
  rw [hpow, h32] at hkey
  -- `eLpNorm (g*g) (3/2) < ∞`, so `(eLpNorm f 3)^2 < ∞`, hence `eLpNorm f 3 < ∞`.
  have hfin : eLpNorm f 3 (volume : Measure Domain3) ^ (2 : ℝ) < ⊤ := by
    rw [← hkey]; exact hgg.eLpNorm_lt_top
  by_contra hcon
  rw [not_lt, top_le_iff] at hcon
  rw [hcon] at hfin
  simp at hfin

/-! ### B3b — Integrability of the convection integrand -/

/-- The real part of the j-th complex component of `u ∈ H¹_σ` lies in `L⁶` (via A3 / GNS). -/
private theorem memLp_six_componentRe (u : L2VF_R3) (hu : memH1VF_R3 u) (j : Fin 3) :
    MemLp (fun x => (L2VF_projComponentC_R3 j u x).re) 6 (volume : Measure Domain3) :=
  (gns_L6_of_memH1_R3 _ (hu j)).re

/-- The real part of the j-th complex component of `u ∈ L²` lies in `L²`. -/
private theorem memLp_two_componentRe (u : L2VF_R3) (j : Fin 3) :
    MemLp (fun x => (L2VF_projComponentC_R3 j u x).re) 2 (volume : Measure Domain3) :=
  (Lp.memLp (L2VF_projComponentC_R3 j u)).re

/-- The real part of the j-th complex component of `u ∈ H¹_σ` lies in `L³` (interpolation). -/
private theorem memLp_three_componentRe (u : L2VF_R3) (hu : memH1VF_R3 u) (j : Fin 3) :
    MemLp (fun x => (L2VF_projComponentC_R3 j u x).re) 3 (volume : Measure Domain3) :=
  L2L6_inter_mem_L3 _ (memLp_two_componentRe u j) (memLp_six_componentRe u hu j)

/-- The real part of the weak gradient component `gradComp_of_memH1` lies in `L²`. -/
private theorem memLp_two_gradRe (v : L2VF_R3) (hv : memH1VF_R3 v) (a i : Fin 3) :
    MemLp (fun x => (gradComp_of_memH1 v hv a i x).re) 2 (volume : Measure Domain3) :=
  (Lp.memLp (gradComp_of_memH1 v hv a i)).re

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
    (hu : memH1VF_R3 u) (hv : memH1VF_R3 v) (hw : memH1VF_R3 w) : ℝ :=
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
  rw [hx]; simp [Complex.real_smul, Complex.re_ofReal_mul]

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
  rw [heq, hx]; simp [Complex.re_ofReal_mul]

/-- **B4a `convFormH1_add_1` [must-prove].** `convFormH1` is additive in slot 1:
`convFormH1 (u + u') v w (add hu hu') hv hw = convFormH1 u v w hu hv hw + convFormH1 u' v w hu' hv hw`. -/
theorem convFormH1_add_1 (u u' v w : L2VF_R3)
    (hu : memH1VF_R3 u) (hu' : memH1VF_R3 u')
    (hv : memH1VF_R3 v) (hw : memH1VF_R3 w) :
    convFormH1 (u + u') v w (memH1VF_R3_add hu hu') hv hw =
    convFormH1 u v w hu hv hw + convFormH1 u' v w hu' hv hw := by
  unfold convFormH1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  -- The (i,a) integrand for (u+u') splits as the sum of the integrands for u and u'.
  have hsplit : (fun x => (L2VF_projComponentC_R3 a (u + u') x).re *
        (gradComp_of_memH1 v hv a i x).re * (L2VF_projComponentC_R3 i w x).re)
      =ᵐ[volume] fun x => ((L2VF_projComponentC_R3 a u x).re *
          (gradComp_of_memH1 v hv a i x).re * (L2VF_projComponentC_R3 i w x).re)
        + ((L2VF_projComponentC_R3 a u' x).re *
          (gradComp_of_memH1 v hv a i x).re * (L2VF_projComponentC_R3 i w x).re) := by
    filter_upwards [componentRe_add_ae u u' a] with x hx
    rw [hx]; ring
  rw [MeasureTheory.integral_congr_ae hsplit,
    MeasureTheory.integral_add (convFormH1_integrable u v w hu hv hw i a)
      (convFormH1_integrable u' v w hu' hv hw i a)]

/-- **B4b `convFormH1_add_2` [must-prove].** `convFormH1` is additive in slot 2:
`convFormH1 u (v + v') w hu (add hv hv') hw = convFormH1 u v w hu hv hw + convFormH1 u v' w hu hv' hw`. -/
theorem convFormH1_add_2 (u v v' w : L2VF_R3)
    (hu : memH1VF_R3 u) (hv : memH1VF_R3 v) (hv' : memH1VF_R3 v')
    (hw : memH1VF_R3 w) :
    convFormH1 u (v + v') w hu (memH1VF_R3_add hv hv') hw =
    convFormH1 u v w hu hv hw + convFormH1 u v' w hu hv' hw := by
  unfold convFormH1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hsplit : (fun x => (L2VF_projComponentC_R3 a u x).re *
        (gradComp_of_memH1 (v + v') (memH1VF_R3_add hv hv') a i x).re *
        (L2VF_projComponentC_R3 i w x).re)
      =ᵐ[volume] fun x => ((L2VF_projComponentC_R3 a u x).re *
          (gradComp_of_memH1 v hv a i x).re * (L2VF_projComponentC_R3 i w x).re)
        + ((L2VF_projComponentC_R3 a u x).re *
          (gradComp_of_memH1 v' hv' a i x).re * (L2VF_projComponentC_R3 i w x).re) := by
    filter_upwards [gradRe_add_ae v v' hv hv' a i] with x hx
    rw [hx]; ring
  rw [MeasureTheory.integral_congr_ae hsplit,
    MeasureTheory.integral_add (convFormH1_integrable u v w hu hv hw i a)
      (convFormH1_integrable u v' w hu hv' hw i a)]

/-- **B4c `convFormH1_add_3` [must-prove].** `convFormH1` is additive in slot 3. -/
theorem convFormH1_add_3 (u v w w' : L2VF_R3)
    (hu : memH1VF_R3 u) (hv : memH1VF_R3 v)
    (hw : memH1VF_R3 w) (hw' : memH1VF_R3 w') :
    convFormH1 u v (w + w') hu hv (memH1VF_R3_add hw hw') =
    convFormH1 u v w hu hv hw + convFormH1 u v w' hu hv hw' := by
  unfold convFormH1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hsplit : (fun x => (L2VF_projComponentC_R3 a u x).re *
        (gradComp_of_memH1 v hv a i x).re * (L2VF_projComponentC_R3 i (w + w') x).re)
      =ᵐ[volume] fun x => ((L2VF_projComponentC_R3 a u x).re *
          (gradComp_of_memH1 v hv a i x).re * (L2VF_projComponentC_R3 i w x).re)
        + ((L2VF_projComponentC_R3 a u x).re *
          (gradComp_of_memH1 v hv a i x).re * (L2VF_projComponentC_R3 i w' x).re) := by
    filter_upwards [componentRe_add_ae w w' i] with x hx
    rw [hx]; ring
  rw [MeasureTheory.integral_congr_ae hsplit,
    MeasureTheory.integral_add (convFormH1_integrable u v w hu hv hw i a)
      (convFormH1_integrable u v w' hu hv hw' i a)]

/-- **B4d-1 `convFormH1_smul_1` [must-prove].** `convFormH1` is ℝ-homogeneous in slot 1. -/
theorem convFormH1_smul_1 (c : ℝ) (u v w : L2VF_R3)
    (hu : memH1VF_R3 u) (hv : memH1VF_R3 v) (hw : memH1VF_R3 w) :
    convFormH1 (c • u) v w (memH1VF_R3_smul c hu) hv hw =
    c * convFormH1 u v w hu hv hw := by
  unfold convFormH1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hsplit : (fun x => (L2VF_projComponentC_R3 a (c • u) x).re *
        (gradComp_of_memH1 v hv a i x).re * (L2VF_projComponentC_R3 i w x).re)
      =ᵐ[volume] fun x => c * ((L2VF_projComponentC_R3 a u x).re *
          (gradComp_of_memH1 v hv a i x).re * (L2VF_projComponentC_R3 i w x).re) := by
    filter_upwards [componentRe_smul_ae c u a] with x hx
    rw [hx]; ring
  rw [MeasureTheory.integral_congr_ae hsplit, MeasureTheory.integral_const_mul _ _]

/-- **B4d-2 `convFormH1_smul_2` [must-prove].** `convFormH1` is ℝ-homogeneous in slot 2. -/
theorem convFormH1_smul_2 (c : ℝ) (u v w : L2VF_R3)
    (hu : memH1VF_R3 u) (hv : memH1VF_R3 v) (hw : memH1VF_R3 w) :
    convFormH1 u (c • v) w hu (memH1VF_R3_smul c hv) hw =
    c * convFormH1 u v w hu hv hw := by
  unfold convFormH1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hsplit : (fun x => (L2VF_projComponentC_R3 a u x).re *
        (gradComp_of_memH1 (c • v) (memH1VF_R3_smul c hv) a i x).re *
        (L2VF_projComponentC_R3 i w x).re)
      =ᵐ[volume] fun x => c * ((L2VF_projComponentC_R3 a u x).re *
          (gradComp_of_memH1 v hv a i x).re * (L2VF_projComponentC_R3 i w x).re) := by
    filter_upwards [gradRe_smul_ae c v hv a i] with x hx
    rw [hx]; ring
  rw [MeasureTheory.integral_congr_ae hsplit, MeasureTheory.integral_const_mul _ _]

/-- **B4d-3 `convFormH1_smul_3` [must-prove].** `convFormH1` is ℝ-homogeneous in slot 3. -/
theorem convFormH1_smul_3 (c : ℝ) (u v w : L2VF_R3)
    (hu : memH1VF_R3 u) (hv : memH1VF_R3 v) (hw : memH1VF_R3 w) :
    convFormH1 u v (c • w) hu hv (memH1VF_R3_smul c hw) =
    c * convFormH1 u v w hu hv hw := by
  unfold convFormH1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hsplit : (fun x => (L2VF_projComponentC_R3 a u x).re *
        (gradComp_of_memH1 v hv a i x).re * (L2VF_projComponentC_R3 i (c • w) x).re)
      =ᵐ[volume] fun x => c * ((L2VF_projComponentC_R3 a u x).re *
          (gradComp_of_memH1 v hv a i x).re * (L2VF_projComponentC_R3 i w x).re) := by
    filter_upwards [componentRe_smul_ae c w i] with x hx
    rw [hx]; ring
  rw [MeasureTheory.integral_congr_ae hsplit, MeasureTheory.integral_const_mul _ _]

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

/-! ### B6 IBP infrastructure — H¹·H¹ weak Leibniz via Schwartz approximation

The B6a integration-by-parts identity needs the distributional Leibniz rule
`∂ₐ(f·g) = (∂ₐf)·g + f·(∂ₐg)` for two H¹ factors, tested against a Schwartz function.
Mathlib has no such two-H¹-factor product rule, so we build it here by
smooth-approximation: approximate both `f` and `g` (with their weak derivatives) by Schwartz
sequences via `schwartz_h1_gradConv`, apply the classical Schwartz IBP
`SchwartzMap.integral_bilinear_lineDerivOp_right_eq_neg_left`, and pass to the L²-limit.

The limit passage rests on a single clean fact: if `aₙ → a` and `bₙ → b` in `L²(ℝ³)` and
`h` is essentially bounded, then `∫ aₙ·bₙ·h → ∫ a·b·h`, proved by writing the integral as
the real `L²` inner product `⟪aₙ, (h·bₙ)⟫` and using joint continuity of `inner`. -/

/-- The real-part map `L²(ℝ³;ℂ) → L²(ℝ³;ℝ)` as a continuous linear map (via `Complex.reCLM`). -/
private noncomputable def reLp : L2C_R3 →L[ℝ] Lp ℝ 2 (volume : Measure Domain3) :=
  Complex.reCLM.compLpL 2 (volume : Measure Domain3)

private theorem reLp_coeFn (f : L2C_R3) :
    (reLp f : Domain3 → ℝ) =ᵐ[volume] fun x => (f x).re := by
  filter_upwards [ContinuousLinearMap.coeFn_compLpL Complex.reCLM f] with x hx
  rw [reLp]; rw [hx]; rfl

/-- The real-part map contracts the `L²` norm: `‖reLp f‖ ≤ ‖f‖`. -/
private theorem norm_reLp_le (f : L2C_R3) : ‖reLp f‖ ≤ ‖f‖ := by
  have hcoe : (reLp f : Domain3 → ℝ) =ᵐ[volume] fun x => (f x).re := reLp_coeFn f
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae hcoe]
  refine ENNReal.toReal_mono (by finiteness) ?_
  refine eLpNorm_mono_ae (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]
  exact Complex.abs_re_le_norm (f x)

/-- Multiplication of a real `L²` element by an essentially bounded real function, landing in
`L²`. Built directly (not as a CLM) — we only need its `coeFn` and an `L²`-Lipschitz bound. -/
private noncomputable def mulRBdd (h : Domain3 → ℝ)
    (hh : MemLp h ⊤ (volume : Measure Domain3)) (a : Lp ℝ 2 (volume : Measure Domain3)) :
    Lp ℝ 2 (volume : Measure Domain3) :=
  (((Lp.memLp a).smul (p := ⊤) (q := 2) (r := 2) hh)).toLp

private theorem mulRBdd_coeFn (h : Domain3 → ℝ)
    (hh : MemLp h ⊤ (volume : Measure Domain3)) (a : Lp ℝ 2 (volume : Measure Domain3)) :
    (mulRBdd h hh a : Domain3 → ℝ) =ᵐ[volume] fun x => h x * a x := by
  filter_upwards [MemLp.coeFn_toLp (((Lp.memLp a).smul (p := ⊤) (q := 2) (r := 2) hh))]
    with x hx
  rw [mulRBdd]; rw [hx]; rfl

/-- `mulRBdd` is additive (used to express the difference of two multiplier images). -/
private theorem mulRBdd_sub (h : Domain3 → ℝ)
    (hh : MemLp h ⊤ (volume : Measure Domain3)) (a b : Lp ℝ 2 (volume : Measure Domain3)) :
    mulRBdd h hh a - mulRBdd h hh b = mulRBdd h hh (a - b) := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub (mulRBdd h hh a) (mulRBdd h hh b), mulRBdd_coeFn h hh a,
    mulRBdd_coeFn h hh b, mulRBdd_coeFn h hh (a - b), Lp.coeFn_sub a b] with x h1 h2 h3 h4 h5
  rw [h1, Pi.sub_apply, h2, h3, h4, h5, Pi.sub_apply, mul_sub]

/-- `L²`-norm bound for the multiplier: `‖mulRBdd h c‖ ≤ ‖h‖_∞ · ‖c‖`. -/
private theorem norm_mulRBdd_le (h : Domain3 → ℝ)
    (hh : MemLp h ⊤ (volume : Measure Domain3)) (c : Lp ℝ 2 (volume : Measure Domain3)) :
    ‖mulRBdd h hh c‖ ≤ (eLpNorm h ⊤ (volume : Measure Domain3)).toReal * ‖c‖ := by
  have hnorm : ‖mulRBdd h hh c‖
      = (eLpNorm (h • (c : Domain3 → ℝ)) 2 (volume : Measure Domain3)).toReal :=
    Lp.norm_toLp _ _
  have hcnorm : ‖c‖ = (eLpNorm c 2 (volume : Measure Domain3)).toReal := Lp.norm_def c
  rw [hnorm, hcnorm, ← ENNReal.toReal_mul]
  refine ENNReal.toReal_mono
    (ENNReal.mul_ne_top hh.eLpNorm_lt_top.ne (Lp.memLp c).eLpNorm_lt_top.ne) ?_
  exact eLpNorm_smul_le_mul_eLpNorm (Lp.aestronglyMeasurable _) hh.aestronglyMeasurable

/-- The bounded multiplier sends an `L²`-convergent sequence to an `L²`-convergent sequence. -/
private theorem tendsto_mulRBdd (h : Domain3 → ℝ)
    (hh : MemLp h ⊤ (volume : Measure Domain3))
    {a : ℕ → Lp ℝ 2 (volume : Measure Domain3)} {a₀ : Lp ℝ 2 (volume : Measure Domain3)}
    (ha : Filter.Tendsto a Filter.atTop (nhds a₀)) :
    Filter.Tendsto (fun n => mulRBdd h hh (a n)) Filter.atTop (nhds (mulRBdd h hh a₀)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero] at ha ⊢
  set C : ℝ := (eLpNorm h ⊤ (volume : Measure Domain3)).toReal with hC
  have hbound : ∀ n, ‖mulRBdd h hh (a n) - mulRBdd h hh a₀‖ ≤ C * ‖a n - a₀‖ := by
    intro n; rw [mulRBdd_sub]; exact norm_mulRBdd_le h hh (a n - a₀)
  refine squeeze_zero (fun n => norm_nonneg _) hbound ?_
  simpa using ha.const_mul C

/-- The integral `∫ a·b·h` over `ℝ³` for real `L²` elements `a, b` and bounded `h` equals the
real `L²` inner product `⟪a, mulRBdd h b⟫`. -/
private theorem integral_mul_mul_eq_inner (h : Domain3 → ℝ)
    (hh : MemLp h ⊤ (volume : Measure Domain3))
    (a b : Lp ℝ 2 (volume : Measure Domain3)) :
    ∫ x : Domain3, (a x) * (b x) * (h x) ∂(volume : Measure Domain3)
      = (inner ℝ a (mulRBdd h hh b) : ℝ) := by
  rw [MeasureTheory.L2.inner_def]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [mulRBdd_coeFn h hh b] with x hx
  rw [RCLike.inner_apply, hx, conj_trivial]; ring

/-- **Core limit lemma.** If `aₙ → a` and `bₙ → b` in `L²(ℝ³;ℝ)` and `h` is essentially bounded,
then `∫ aₙ·bₙ·h → ∫ a·b·h`. (Real `L²` inner product is jointly continuous.) -/
private theorem tendsto_integral_mul_mul (h : Domain3 → ℝ)
    (hh : MemLp h ⊤ (volume : Measure Domain3))
    {a b : ℕ → Lp ℝ 2 (volume : Measure Domain3)}
    {a₀ b₀ : Lp ℝ 2 (volume : Measure Domain3)}
    (ha : Filter.Tendsto a Filter.atTop (nhds a₀))
    (hb : Filter.Tendsto b Filter.atTop (nhds b₀)) :
    Filter.Tendsto (fun n => ∫ x : Domain3, (a n x) * (b n x) * (h x) ∂(volume : Measure Domain3))
      Filter.atTop (nhds (∫ x : Domain3, (a₀ x) * (b₀ x) * (h x) ∂(volume : Measure Domain3))) := by
  have heq : (fun n => ∫ x : Domain3, (a n x) * (b n x) * (h x) ∂(volume : Measure Domain3))
      = fun n => (inner ℝ (a n) (mulRBdd h hh (b n)) : ℝ) := by
    funext n; exact integral_mul_mul_eq_inner h hh (a n) (b n)
  rw [heq, integral_mul_mul_eq_inner h hh a₀ b₀]
  exact ha.inner (tendsto_mulRBdd h hh hb)

/-! #### Schwartz-level Leibniz product rule -/

/-- The pointwise product of two real Schwartz functions, as a Schwartz function. -/
private noncomputable def prodS (f g : SchwartzMap Domain3 ℝ) : SchwartzMap Domain3 ℝ :=
  SchwartzMap.bilinLeftCLM (ContinuousLinearMap.mul ℝ ℝ) g.hasTemperateGrowth f

private theorem prodS_apply (f g : SchwartzMap Domain3 ℝ) (x : Domain3) :
    (prodS f g) x = f x * g x := by
  simp [prodS, SchwartzMap.bilinLeftCLM_apply]

/-- Classical Leibniz rule for the directional derivative of a Schwartz product. -/
private theorem lineDerivOp_prodS (f g : SchwartzMap Domain3 ℝ) (v x : Domain3) :
    (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ) v (prodS f g)) x
      = (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ) v f) x * g x
        + f x * (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ) v g) x := by
  simp only [LineDeriv.lineDerivOpCLM_apply]
  have hf : HasDerivAt (fun t : ℝ => f (x + t • v)) ((fderiv ℝ (⇑f) x) v) 0 :=
    (SchwartzMap.hasFDerivAt f x).hasLineDerivAt v
  have hg : HasDerivAt (fun t : ℝ => g (x + t • v)) ((fderiv ℝ (⇑g) x) v) 0 :=
    (SchwartzMap.hasFDerivAt g x).hasLineDerivAt v
  have hmul := hf.mul hg
  rw [zero_smul, add_zero] at hmul
  have hfun : ((fun t : ℝ => f (x + t • v)) * fun t : ℝ => g (x + t • v))
      = fun t : ℝ => (prodS f g) (x + t • v) := by funext t; rw [prodS_apply]; rfl
  rw [hfun] at hmul
  have hline : HasLineDerivAt ℝ (⇑(prodS f g))
      ((fderiv ℝ (⇑f) x) v * g x + f x * (fderiv ℝ (⇑g) x) v) x v := hmul
  rw [lineDerivOp_apply, hline.lineDeriv, lineDerivOp_apply, lineDerivOp_apply,
    (SchwartzMap.hasFDerivAt f x).hasLineDerivAt v |>.lineDeriv,
    (SchwartzMap.hasFDerivAt g x).hasLineDerivAt v |>.lineDeriv]

/-- **Schwartz-level Leibniz IBP.** For real Schwartz `f, g, φ` and direction `eₐ`:
`∫ f·g·(∂ₐφ) = -∫ (∂ₐf·g + f·∂ₐg)·φ`. -/
private theorem schwartzLeibniz2 (f g φ : SchwartzMap Domain3 ℝ) (a : Fin 3) :
    ∫ x : Domain3, (f x) * (g x)
        * (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ) (EuclideanSpace.single a (1 : ℝ)) φ) x
        ∂(volume : Measure Domain3)
      = -∫ x : Domain3,
          ((lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ) (EuclideanSpace.single a (1 : ℝ)) f) x * g x
            + f x * (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ) (EuclideanSpace.single a (1 : ℝ)) g) x)
          * (φ x) ∂(volume : Measure Domain3) := by
  set m : Domain3 := EuclideanSpace.single a (1 : ℝ) with hm
  -- Schwartz IBP for the product `prodS f g` against `φ`.
  have hibp := SchwartzMap.integral_bilinear_lineDerivOp_right_eq_neg_left
    (μ := (volume : Measure Domain3)) (prodS f g) φ (ContinuousLinearMap.mul ℝ ℝ) m
  simp only [ContinuousLinearMap.mul_apply',
    ← LineDeriv.lineDerivOpCLM_apply (R := ℝ) (E := SchwartzMap Domain3 ℝ)] at hibp
  -- `hibp : ∫ (prodS f g)·∂ₘφ = -∫ ∂ₘ(prodS f g)·φ`. Rewrite both integrands.
  rw [show (fun x => (prodS f g) x * (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ) m φ) x)
        = fun x => (f x) * (g x) * (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ) m φ) x by
        funext x; rw [prodS_apply],
      show (fun x => (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ) m (prodS f g)) x * (φ x))
        = fun x => ((lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ) m f) x * g x
            + f x * (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ) m g) x) * (φ x) by
        funext x; rw [lineDerivOp_prodS]] at hibp
  exact hibp

/-! #### Real-part of a complex Schwartz function, as a real Schwartz function -/

/-- The real part of a complex Schwartz function, as a real Schwartz function (post-composition
with `Complex.reCLM`). -/
private noncomputable def reS (φ : SchwartzMap Domain3 ℂ) : SchwartzMap Domain3 ℝ :=
  φ.postcompCLM Complex.reCLM

private theorem reS_apply (φ : SchwartzMap Domain3 ℂ) (x : Domain3) : (reS φ) x = (φ x).re := by
  rw [reS, SchwartzMap.postcompCLM_apply]; rfl

/-- The directional derivative of the real part is the real part of the directional derivative. -/
private theorem lineDerivOp_reS (φ : SchwartzMap Domain3 ℂ) (m x : Domain3) :
    (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ) m (reS φ)) x
      = ((lineDerivOpCLM ℝ (SchwartzMap Domain3 ℂ) m φ) x).re := by
  simp only [LineDeriv.lineDerivOpCLM_apply, lineDerivOp_apply]
  have hφ : HasDerivAt (fun t : ℝ => φ (x + t • m)) ((fderiv ℝ (⇑φ) x) m) 0 :=
    (SchwartzMap.hasFDerivAt φ x).hasLineDerivAt m
  have hcomp := Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 hφ
  simp only [Function.comp_def] at hcomp
  have hfun : (fun t : ℝ => Complex.reCLM (φ (x + t • m))) = fun t : ℝ => (reS φ) (x + t • m) := by
    funext t; rw [reS_apply]; rfl
  rw [hfun] at hcomp
  have hl : HasLineDerivAt ℝ (⇑(reS φ)) (Complex.reCLM ((fderiv ℝ (⇑φ) x) m)) x m := hcomp
  rw [hl.lineDeriv, (SchwartzMap.hasFDerivAt φ x).hasLineDerivAt m |>.lineDeriv]; rfl

/-- The real `L²` class of `reS φ` is the real part `reLp` of the complex `L²` class of `φ`. -/
private theorem reS_toLp_eq_reLp (φ : SchwartzMap Domain3 ℂ) :
    (reS φ).toLp 2 (volume : Measure Domain3)
      = reLp (φ.toLp 2 (volume : Measure Domain3)) := by
  apply Lp.ext
  filter_upwards [(reS φ).coeFn_toLp 2 (volume : Measure Domain3),
    reLp_coeFn (φ.toLp 2 (volume : Measure Domain3)),
    φ.coeFn_toLp 2 (volume : Measure Domain3)] with x h1 h2 h3
  rw [h1, h2, h3, reS_apply]

/-! #### L³-convergence of the multi-direction Schwartz approximants

For the H¹-test extension of the weak Leibniz rule we need the un-differentiated test factor's
Schwartz approximants to converge in `L³`, not just `L²`. This is obtained from a uniform `L⁶`
bound on the (multi-direction) Schwartz sequence — itself a consequence of GNS
(`gns_L6_schwartz`: `‖φ‖₆ ≤ C·‖∇φ‖₂`) plus an `L²∩L⁶ ↪ L³` interpolation. The `L⁶`-Cauchy
property follows because the full gradient of the difference sequence tends to `0` in `L²`. -/

/-- `reS (φ - ψ) x = (reS φ) x - (reS ψ) x` pointwise. -/
private theorem reS_sub_apply (φ ψ : SchwartzMap Domain3 ℂ) (x : Domain3) :
    (reS (φ - ψ)) x = (reS φ) x - (reS ψ) x := by
  rw [reS_apply, reS_apply, reS_apply, SchwartzMap.sub_apply, Complex.sub_re]

/-- **L³ approximation of the un-differentiated `H¹` test factor.**
For `h : L2C_R3` in `H^{1,2}` and direction `eₐ` with weak `eₐ`-derivative `(hG : 𝓢')`, there is
a real Schwartz sequence `ψₙ` (the real parts of the multi-direction Brick-1 sequence) that
converges to `reLp h` in `L²`, whose `eₐ`-derivatives converge to `reLp hGval` in `L²`, **and**
which converges to `h.re` in `L³`. The `L³` convergence uses the uniform `L⁶` (GNS) bound on the
full gradient together with the `L²∩L⁶ ↪ L³` interpolation. -/
private theorem reSchwartz_L3_approx (h hGval : L2C_R3) (a : Fin 3)
    (hh : MemSobolev 1 2 (h : 𝓢'(Domain3, ℂ)))
    (hG : (∂_{EuclideanSpace.single a (1 : ℝ)} (h : 𝓢'(Domain3, ℂ))) = (hGval : 𝓢'(Domain3, ℂ))) :
    ∃ ψ : ℕ → SchwartzMap Domain3 ℝ,
      Filter.Tendsto (fun n => (ψ n).toLp 2 (volume : Measure Domain3))
          Filter.atTop (nhds (reLp h)) ∧
      Filter.Tendsto (fun n =>
          (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ) (EuclideanSpace.single a (1 : ℝ)) (ψ n)).toLp 2
            (volume : Measure Domain3))
          Filter.atTop (nhds (reLp hGval)) ∧
      ∃ Φ : Lp ℝ 3 (volume : Measure Domain3),
        (⇑Φ =ᵐ[volume] fun x => (h x).re) ∧
        Filter.Tendsto (fun n => (ψ n).toLp 3 (volume : Measure Domain3))
          Filter.atTop (nhds Φ) := by
  classical
  -- Multi-direction Brick-1 sequence φₙ.
  obtain ⟨φ, hφval, hφgrad⟩ := schwartz_h1_gradConv_multi h hh
  -- Direction-a gradient limit gₐ with ∂ₐ(h:𝓢')=(gₐ:𝓢'); identify gₐ = hGval.
  obtain ⟨ga, hga_spec, hφga0⟩ := hφgrad (EuclideanSpace.single a (1 : ℝ))
  have hga_eq : ga = hGval := L2C_eq_of_toTempered_eq (by rw [← hga_spec, hG])
  have hφga : Filter.Tendsto
      (fun n => (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℂ)
        (EuclideanSpace.single a (1 : ℝ)) (φ n)).toLp 2 (volume : Measure Domain3))
      Filter.atTop (nhds hGval) := by rw [← hga_eq]; exact hφga0
  set ψ : ℕ → SchwartzMap Domain3 ℝ := fun n => reS (φ n) with hψdef
  -- (1) value L²: (ψₙ).toLp 2 = reLp (φₙ.toLp 2) → reLp h.
  have hval2 : Filter.Tendsto (fun n => (ψ n).toLp 2 (volume : Measure Domain3))
      Filter.atTop (nhds (reLp h)) := by
    have heq : (fun n => (ψ n).toLp 2 (volume : Measure Domain3))
        = fun n => reLp (φ n |>.toLp 2 (volume : Measure Domain3)) := by
      funext n; rw [hψdef]; exact reS_toLp_eq_reLp (φ n)
    rw [heq]; exact (reLp.continuous.tendsto h).comp hφval
  -- (2) gradient L² (direction a): (∂ₐψₙ).toLp 2 = reLp ((∂ₐφₙ).toLp 2) → reLp hGval.
  have hgrad2 : Filter.Tendsto (fun n =>
      (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ) (EuclideanSpace.single a (1 : ℝ)) (ψ n)).toLp 2
        (volume : Measure Domain3)) Filter.atTop (nhds (reLp hGval)) := by
    have heq : (fun n =>
        (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ) (EuclideanSpace.single a (1 : ℝ)) (ψ n)).toLp
          2 (volume : Measure Domain3))
        = fun n => reLp ((lineDerivOpCLM ℝ (SchwartzMap Domain3 ℂ)
            (EuclideanSpace.single a (1 : ℝ)) (φ n)).toLp 2 (volume : Measure Domain3)) := by
      funext n
      apply Lp.ext
      filter_upwards [(lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
          (EuclideanSpace.single a (1 : ℝ)) (ψ n)).coeFn_toLp 2 (volume : Measure Domain3),
        reLp_coeFn ((lineDerivOpCLM ℝ (SchwartzMap Domain3 ℂ)
          (EuclideanSpace.single a (1 : ℝ)) (φ n)).toLp 2 (volume : Measure Domain3)),
        (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℂ)
          (EuclideanSpace.single a (1 : ℝ)) (φ n)).coeFn_toLp 2 (volume : Measure Domain3)]
        with x h1 h2 h3
      rw [h1, h2, h3, hψdef, lineDerivOp_reS]
    rw [heq]; exact (reLp.continuous.tendsto hGval).comp hφga
  refine ⟨ψ, hval2, hgrad2, ?_⟩
  -- (3) L³ convergence, via interpolation `‖g‖₃ ≤ ‖g‖₂^{1/2}·‖g‖₆^{1/2}` applied to `ψₙ - h.re`,
  -- using value-L²-convergence (→0) and a uniform `L⁶` bound (GNS on the full gradient).
  -- `h.re ∈ L⁶` (A3/GNS) and `h.re ∈ L²` (Lp membership).
  have hh6 : MemLp (fun x => (h x).re) 6 (volume : Measure Domain3) :=
    (gns_L6_of_memH1_R3 h hh).re
  have hh2 : MemLp (fun x => (h x).re) 2 (volume : Measure Domain3) := (Lp.memLp h).re
  -- `h.re ∈ L³` (interpolation).
  have hh3 : MemLp (fun x => (h x).re) 3 (volume : Measure Domain3) := L2L6_inter_mem_L3 _ hh2 hh6
  set Φ : Lp ℝ 3 (volume : Measure Domain3) := hh3.toLp with hΦdef
  have hΦae : (⇑Φ : Domain3 → ℝ) =ᵐ[volume] fun x => (h x).re := hh3.coeFn_toLp
  refine ⟨Φ, hΦae, ?_⟩
  -- Uniform `L⁶` bound on `ψₙ`: `eLpNorm ψₙ 6 ≤ C` for all `n`.
  -- Each gradient direction `i`: `eLpNorm (∂ᵢφₙ) 2 = ‖(∂ᵢφₙ).toLp 2‖ₑ` is bounded (convergent).
  obtain ⟨C6, hC6_ne_top, hC6⟩ : ∃ C6 : ENNReal, C6 ≠ ⊤ ∧
      ∀ n, eLpNorm ((ψ n) : Domain3 → ℝ) 6 (volume : Measure Domain3) ≤ C6 := by
    -- bound on `eLpNorm (φₙ) 6 ≤ Cgns · ∑ᵢ eLpNorm (∂ᵢφₙ) 2`.
    set Cgns : ENNReal := (SNormLESNormFDerivOfEqConst ℂ (volume : Measure Domain3) 2 : ENNReal)
      with hCgns
    -- each `eLpNorm (∂ᵢφₙ) 2` is bounded: the sequence `(∂ᵢφₙ).toLp 2` converges, hence is bounded.
    have hbdd_i : ∀ i : Fin 3, ∃ Bi : ENNReal, Bi ≠ ⊤ ∧ ∀ n,
        eLpNorm (fun x => (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℂ)
          (EuclideanSpace.single i (1 : ℝ)) (φ n)) x) 2 (volume : Measure Domain3) ≤ Bi := by
      intro i
      obtain ⟨gi, _, hφgi⟩ := hφgrad (EuclideanSpace.single i (1 : ℝ))
      -- the convergent sequence `(∂ᵢφₙ).toLp 2` is bounded in norm.
      obtain ⟨Ri, _, hRi⟩ := (Metric.isBounded_range_of_tendsto _ hφgi).subset_closedBall_lt 0 0
      refine ⟨ENNReal.ofReal Ri, ENNReal.ofReal_ne_top, fun n => ?_⟩
      have hnorm : eLpNorm (fun x => (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℂ)
          (EuclideanSpace.single i (1 : ℝ)) (φ n)) x) 2 (volume : Measure Domain3)
          = ‖(lineDerivOpCLM ℝ (SchwartzMap Domain3 ℂ)
            (EuclideanSpace.single i (1 : ℝ)) (φ n)).toLp 2 (volume : Measure Domain3)‖ₑ := by
        rw [Lp.enorm_def]
        exact (eLpNorm_congr_ae ((lineDerivOpCLM ℝ (SchwartzMap Domain3 ℂ)
          (EuclideanSpace.single i (1 : ℝ)) (φ n)).coeFn_toLp 2 (volume : Measure Domain3)).symm)
      rw [hnorm]
      have hmem : (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℂ)
          (EuclideanSpace.single i (1 : ℝ)) (φ n)).toLp 2 (volume : Measure Domain3)
          ∈ Metric.closedBall (0 : Lp ℂ 2 (volume : Measure Domain3)) Ri :=
        hRi (Set.mem_range_self n)
      rw [Metric.mem_closedBall, dist_zero_right] at hmem
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal hmem
    choose B hBfin hB using hbdd_i
    refine ⟨Cgns * ∑ i : Fin 3, B i, ?_, fun n => ?_⟩
    · refine ENNReal.mul_ne_top (by rw [hCgns]; exact ENNReal.coe_ne_top) ?_
      exact ENNReal.sum_ne_top.mpr (fun i _ => hBfin i)
    -- `eLpNorm (reS φₙ) 6 ≤ eLpNorm φₙ 6 ≤ Cgns · ∑ᵢ eLpNorm (∂ᵢφₙ) 2 ≤ Cgns · ∑ᵢ Bᵢ`.
    have hre6 : eLpNorm ((ψ n) : Domain3 → ℝ) 6 (volume : Measure Domain3)
        ≤ eLpNorm ((φ n) : Domain3 → ℂ) 6 (volume : Measure Domain3) := by
      refine eLpNorm_mono_ae (Filter.Eventually.of_forall fun x => ?_)
      have : ((ψ n) x : ℝ) = (φ n x).re := by rw [hψdef, reS_apply]
      rw [Real.norm_eq_abs, this]
      exact Complex.abs_re_le_norm _
    refine hre6.trans ((gns_L6_schwartz (φ n)).trans ?_)
    rw [← hCgns]
    refine mul_le_mul_left' ?_ Cgns
    refine (PlancherelKernels.eLpNorm_fderiv_le_sum_lineDeriv (φ n)).trans ?_
    exact Finset.sum_le_sum (fun i _ => hB i n)
  -- C6 and ‖h.re‖₆ are finite, so the L⁶ bound `D6` is finite.
  have hh6_top : eLpNorm (fun x => (h x).re) 6 (volume : Measure Domain3) ≠ ⊤ :=
    hh6.eLpNorm_lt_top.ne
  -- L⁶-norm of `ψₙ - h.re` is bounded: `≤ C6 + ‖h.re‖₆ =: D6`.
  set D6 : ENNReal := C6 + eLpNorm (fun x => (h x).re) 6 (volume : Measure Domain3) with hD6
  have hD6_ne_top : D6 ≠ ⊤ := by rw [hD6]; exact ENNReal.add_ne_top.mpr ⟨hC6_ne_top, hh6_top⟩
  have hbnd6 : ∀ n, eLpNorm (fun x => (ψ n) x - (h x).re) 6 (volume : Measure Domain3) ≤ D6 := by
    intro n
    refine (eLpNorm_sub_le ((SchwartzMap.continuous _).aestronglyMeasurable)
      hh6.aestronglyMeasurable (by norm_num)).trans ?_
    rw [hD6]; exact add_le_add (hC6 n) (le_refl _)
  -- L²-norm of `ψₙ - h.re` → 0 (from value-L² convergence).
  have h2to0 : Filter.Tendsto
      (fun n => eLpNorm (fun x => (ψ n) x - (h x).re) 2 (volume : Measure Domain3))
      Filter.atTop (nhds 0) := by
    have heq : ∀ n, eLpNorm (fun x => (ψ n) x - (h x).re) 2 (volume : Measure Domain3)
        = ENNReal.ofReal ‖(ψ n).toLp 2 (volume : Measure Domain3) - reLp h‖ := by
      intro n
      rw [ofReal_norm, Lp.enorm_def]
      refine (eLpNorm_congr_ae ?_)
      filter_upwards [Lp.coeFn_sub ((ψ n).toLp 2 (volume : Measure Domain3)) (reLp h),
        (ψ n).coeFn_toLp 2 (volume : Measure Domain3), reLp_coeFn h] with x hx h1 h2
      simp only [hx, Pi.sub_apply, h1, h2]
    rw [show (fun n => eLpNorm (fun x => (ψ n) x - (h x).re) 2 (volume : Measure Domain3))
        = fun n => ENNReal.ofReal ‖(ψ n).toLp 2 (volume : Measure Domain3) - reLp h‖ from funext heq]
    have hd : Filter.Tendsto
        (fun n => ‖(ψ n).toLp 2 (volume : Measure Domain3) - reLp h‖) Filter.atTop (nhds 0) :=
      tendsto_iff_norm_sub_tendsto_zero.mp hval2
    have := ENNReal.tendsto_ofReal hd
    rwa [ENNReal.ofReal_zero] at this
  -- Interpolation bound: `eLpNorm (ψₙ - h.re) 3 ≤ (eLpNorm (ψₙ-h.re) 2)^{1/2}·D6^{1/2}`.
  have hinterp : ∀ n, eLpNorm (fun x => (ψ n) x - (h x).re) 3 (volume : Measure Domain3)
      ≤ (eLpNorm (fun x => (ψ n) x - (h x).re) 2 (volume : Measure Domain3)) ^ (1/2 : ℝ)
        * D6 ^ (1/2 : ℝ) := by
    intro n
    have hmem2 : MemLp (fun x => (ψ n) x - (h x).re) 2 (volume : Measure Domain3) :=
      ((ψ n).memLp 2 (volume : Measure Domain3)).sub hh2
    have hmem6 : MemLp (fun x => (ψ n) x - (h x).re) 6 (volume : Measure Domain3) :=
      ((ψ n).memLp 6 (volume : Measure Domain3)).sub hh6
    refine (PlancherelKernels.eLpNorm_three_le_interp _ hmem2 hmem6).trans ?_
    gcongr
    exact hbnd6 n
  -- Squeeze: RHS → 0^{1/2}·D6^{1/2} = 0.
  have h3to0 : Filter.Tendsto
      (fun n => eLpNorm (fun x => (ψ n) x - (h x).re) 3 (volume : Measure Domain3))
      Filter.atTop (nhds 0) := by
    have hrhs : Filter.Tendsto
        (fun n => (eLpNorm (fun x => (ψ n) x - (h x).re) 2 (volume : Measure Domain3)) ^ (1/2 : ℝ)
          * D6 ^ (1/2 : ℝ)) Filter.atTop (nhds 0) := by
      have h1 : Filter.Tendsto
          (fun n => (eLpNorm (fun x => (ψ n) x - (h x).re) 2 (volume : Measure Domain3)) ^ (1/2 : ℝ))
          Filter.atTop (nhds 0) := by
        have := h2to0.ennrpow_const (1/2 : ℝ)
        rwa [ENNReal.zero_rpow_of_pos (by norm_num)] at this
      have hD6_pow_top : D6 ^ (1/2 : ℝ) ≠ ⊤ :=
        ENNReal.rpow_ne_top_of_nonneg (by norm_num) hD6_ne_top
      have := ENNReal.Tendsto.mul_const h1 (Or.inr hD6_pow_top)
      rwa [zero_mul] at this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hrhs
      (fun n => bot_le) hinterp
  -- `eLpNorm (ψₙ - h.re) 3 → 0` ⇒ `(ψₙ).toLp 3 → Φ` in `Lp ℝ 3`.
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have heqnorm : ∀ n, ‖(ψ n).toLp 3 (volume : Measure Domain3) - Φ‖
      = (eLpNorm (fun x => (ψ n) x - (h x).re) 3 (volume : Measure Domain3)).toReal := by
    intro n
    rw [Lp.norm_def]
    congr 1
    refine eLpNorm_congr_ae ?_
    filter_upwards [Lp.coeFn_sub ((ψ n).toLp 3 (volume : Measure Domain3)) Φ,
      (ψ n).coeFn_toLp 3 (volume : Measure Domain3), hΦae] with x hx h1 h2
    simp only [hx, Pi.sub_apply, h1, h2]
  rw [show (fun n => ‖(ψ n).toLp 3 (volume : Measure Domain3) - Φ‖)
      = fun n => (eLpNorm (fun x => (ψ n) x - (h x).re) 3 (volume : Measure Domain3)).toReal
      from funext heqnorm]
  have := (ENNReal.tendsto_toReal (by simp : (0:ENNReal) ≠ ⊤)).comp h3to0
  rwa [ENNReal.toReal_zero] at this

/-- **Per-component Schwartz approximation with real-part gradient convergence.**
For `f : L2C_R3` in `H^{1,2}` and direction `eₐ` whose weak derivative distribution equals
`(g : 𝓢')`, there is a real Schwartz sequence `ψₙ` with `(ψₙ).toLp → reLp f` and
`(∂ₐψₙ).toLp → reLp g` in `Lp ℝ 2`. -/
private theorem reSchwartz_approx (f g : L2C_R3) (a : Fin 3)
    (hf : MemSobolev 1 2 (f : 𝓢'(Domain3, ℂ)))
    (hg : (∂_{EuclideanSpace.single a (1 : ℝ)} (f : 𝓢'(Domain3, ℂ))) = (g : 𝓢'(Domain3, ℂ))) :
    ∃ ψ : ℕ → SchwartzMap Domain3 ℝ,
      Filter.Tendsto (fun n => (ψ n).toLp 2 (volume : Measure Domain3))
          Filter.atTop (nhds (reLp f)) ∧
      Filter.Tendsto (fun n =>
          (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ) (EuclideanSpace.single a (1 : ℝ)) (ψ n)).toLp 2
            (volume : Measure Domain3))
          Filter.atTop (nhds (reLp g)) := by
  obtain ⟨g', hg', φ, hφf, hφg⟩ := schwartz_h1_gradConv f (EuclideanSpace.single a (1 : ℝ)) hf
  -- g' and g are both L² representatives of the same distribution `∂ₐ(f:𝓢')`, hence equal.
  have hgg' : g' = g := L2C_eq_of_toTempered_eq (by rw [← hg', hg])
  subst hgg'
  refine ⟨fun n => reS (φ n), ?_, ?_⟩
  · -- (reS φₙ).toLp = reLp (φₙ.toLp) → reLp f.
    have heq : (fun n => (reS (φ n)).toLp 2 (volume : Measure Domain3))
        = fun n => reLp (φ n |>.toLp 2 (volume : Measure Domain3)) := by
      funext n; exact reS_toLp_eq_reLp (φ n)
    rw [heq]; exact (reLp.continuous.tendsto f).comp hφf
  · -- (∂ₐ(reS φₙ)).toLp = reLp ((∂ₐφₙ).toLp) → reLp g'.
    have heq : (fun n =>
        (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ) (EuclideanSpace.single a (1 : ℝ)) (reS (φ n))).toLp
          2 (volume : Measure Domain3))
        = fun n => reLp ((lineDerivOpCLM ℝ (SchwartzMap Domain3 ℂ)
            (EuclideanSpace.single a (1 : ℝ)) (φ n)).toLp 2 (volume : Measure Domain3)) := by
      funext n
      apply Lp.ext
      filter_upwards [(lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
          (EuclideanSpace.single a (1 : ℝ)) (reS (φ n))).coeFn_toLp 2 (volume : Measure Domain3),
        reLp_coeFn ((lineDerivOpCLM ℝ (SchwartzMap Domain3 ℂ)
          (EuclideanSpace.single a (1 : ℝ)) (φ n)).toLp 2 (volume : Measure Domain3)),
        (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℂ)
          (EuclideanSpace.single a (1 : ℝ)) (φ n)).coeFn_toLp 2 (volume : Measure Domain3)]
        with x h1 h2 h3
      rw [h1, h2, h3, lineDerivOp_reS]
    rw [heq]
    -- ∂ₐ in ℂ corresponds via toLp to `∂_{eₐ}(φₙ)`; hφg : (∂ₐφₙ).toLp → g'.
    have hφg' : Filter.Tendsto (fun n =>
        (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℂ) (EuclideanSpace.single a (1 : ℝ)) (φ n)).toLp 2
          (volume : Measure Domain3)) Filter.atTop (nhds g') := hφg
    exact (reLp.continuous.tendsto g').comp hφg'

/-! #### H¹·H¹ weak Leibniz product rule (the analytic heart of B6a) -/

/-- Integrability of a triple product of real Schwartz functions. -/
private theorem Schwartz_mul_mul_integrable (ψ ψ' φ : SchwartzMap Domain3 ℝ) :
    MeasureTheory.Integrable (fun x => (ψ x) * (ψ' x) * (φ x)) (volume : Measure Domain3) := by
  have := (SchwartzMap.bilinLeftCLM (ContinuousLinearMap.mul ℝ ℝ) φ.hasTemperateGrowth
    (SchwartzMap.bilinLeftCLM (ContinuousLinearMap.mul ℝ ℝ) ψ'.hasTemperateGrowth ψ)).integrable
    (μ := (volume : Measure Domain3))
  refine this.congr ?_
  filter_upwards with x
  simp only [SchwartzMap.bilinLeftCLM_apply, ContinuousLinearMap.mul_apply']

/-- Integrability of `(f.re)·(g.re)·φ` for `f, g : L2C_R3` and a real Schwartz test `φ`
(Hölder `L²·L²·L^∞`). -/
private theorem reInt_integrable (f g : L2C_R3) (φ : SchwartzMap Domain3 ℝ) :
    MeasureTheory.Integrable (fun x => (f x).re * (g x).re * (φ x)) (volume : Measure Domain3) := by
  have hfre : MemLp (fun x => (f x).re) 2 (volume : Measure Domain3) := (Lp.memLp f).re
  have hgre : MemLp (fun x => (g x).re) 2 (volume : Measure Domain3) := (Lp.memLp g).re
  have hφ : MemLp (fun x => φ x) ⊤ (volume : Measure Domain3) := φ.memLp_top (volume : Measure Domain3)
  have hfg : MemLp (fun x => (f x).re * (g x).re) 1 (volume : Measure Domain3) :=
    hgre.mul (p := 2) (q := 2) (r := 1) hfre
  have hp := hfg.mul (p := ⊤) (q := 1) (r := 1) hφ
  rw [memLp_one_iff_integrable] at hp
  refine hp.congr ?_
  filter_upwards with x
  simp only [Pi.mul_apply]; ring

/-- For a real Schwartz `ψ` and an essentially bounded `h`, the integral of `ψ·ψ'·h` (Schwartz
values) equals the same integral with the `L²`-classes of `ψ, ψ'` (a.e. equal to `ψ, ψ'`). -/
private theorem integral_schwartz_eq_toLp (ψ ψ' : SchwartzMap Domain3 ℝ) (h : Domain3 → ℝ) :
    ∫ x : Domain3, (ψ x) * (ψ' x) * (h x) ∂(volume : Measure Domain3)
      = ∫ x : Domain3, ((ψ.toLp 2 (volume : Measure Domain3)) x)
          * ((ψ'.toLp 2 (volume : Measure Domain3)) x) * (h x) ∂(volume : Measure Domain3) := by
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [ψ.coeFn_toLp 2 (volume : Measure Domain3),
    ψ'.coeFn_toLp 2 (volume : Measure Domain3)] with x hx hx'
  rw [hx, hx']

/-- **H¹·H¹ weak Leibniz.** For `f, g : L2C_R3` in `H^{1,2}` with weak `eₐ`-derivatives
`fG, gG` (i.e. `∂ₐ(f:𝓢') = (fG:𝓢')`, `∂ₐ(g:𝓢') = (gG:𝓢')`), and any real Schwartz `φ`:

  `∫ (f.re)·(g.re)·(∂ₐφ) = -∫ ((fG.re)·(g.re) + (f.re)·(gG.re))·φ`.

Proved by approximating `f, g, fG, gG` by Schwartz sequences (`reSchwartz_approx`), applying
the classical Schwartz Leibniz IBP (`schwartzLeibniz2`), and passing to the `L²` limit
(`tendsto_integral_mul_mul`). -/
private theorem h1Leibniz2 (f g fG gG : L2C_R3) (a : Fin 3)
    (hf : MemSobolev 1 2 (f : 𝓢'(Domain3, ℂ)))
    (hg : MemSobolev 1 2 (g : 𝓢'(Domain3, ℂ)))
    (hfG : (∂_{EuclideanSpace.single a (1 : ℝ)} (f : 𝓢'(Domain3, ℂ))) = (fG : 𝓢'(Domain3, ℂ)))
    (hgG : (∂_{EuclideanSpace.single a (1 : ℝ)} (g : 𝓢'(Domain3, ℂ))) = (gG : 𝓢'(Domain3, ℂ)))
    (φ : SchwartzMap Domain3 ℝ) :
    ∫ x : Domain3, (f x).re * (g x).re
        * (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ) (EuclideanSpace.single a (1 : ℝ)) φ) x
        ∂(volume : Measure Domain3)
      = -∫ x : Domain3,
          ((fG x).re * (g x).re + (f x).re * (gG x).re) * (φ x)
          ∂(volume : Measure Domain3) := by
  classical
  set m : Domain3 := EuclideanSpace.single a (1 : ℝ) with hm
  -- Schwartz approximants for f and g.
  obtain ⟨ψf, hψf_val, hψf_grad⟩ := reSchwartz_approx f fG a hf hfG
  obtain ⟨ψg, hψg_val, hψg_grad⟩ := reSchwartz_approx g gG a hg hgG
  -- Essential boundedness of the test functions `∂ₐφ` and `φ`.
  have hdφ_bdd : MemLp (fun x => (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ) m φ) x) ⊤
      (volume : Measure Domain3) :=
    (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ) m φ).memLp_top (volume : Measure Domain3)
  have hφ_bdd : MemLp (fun x => φ x) ⊤ (volume : Measure Domain3) :=
    φ.memLp_top (volume : Measure Domain3)
  -- The three convergent integral sequences (LHS and the two RHS terms).
  set LHS : ℕ → ℝ := fun n => ∫ x : Domain3, ((ψf n).toLp 2 (volume : Measure Domain3) x)
      * ((ψg n).toLp 2 (volume : Measure Domain3) x)
      * (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ) m φ) x ∂(volume : Measure Domain3) with hLHSdef
  set R1 : ℕ → ℝ := fun n => ∫ x : Domain3,
      ((lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ) m (ψf n)).toLp 2 (volume : Measure Domain3) x)
        * ((ψg n).toLp 2 (volume : Measure Domain3) x) * (φ x) ∂(volume : Measure Domain3)
    with hR1def
  set R2 : ℕ → ℝ := fun n => ∫ x : Domain3, ((ψf n).toLp 2 (volume : Measure Domain3) x)
      * ((lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ) m (ψg n)).toLp 2 (volume : Measure Domain3) x)
        * (φ x) ∂(volume : Measure Domain3) with hR2def
  -- Per-n Schwartz Leibniz identity: `LHS n = -(R1 n + R2 n)`.
  have hper : ∀ n, LHS n = -(R1 n + R2 n) := by
    intro n
    have hL := schwartzLeibniz2 (ψf n) (ψg n) φ a
    rw [← hm] at hL
    rw [hLHSdef, hR1def, hR2def]
    simp only
    rw [← integral_schwartz_eq_toLp (ψf n) (ψg n),
      ← integral_schwartz_eq_toLp (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ) m (ψf n)) (ψg n) φ,
      ← integral_schwartz_eq_toLp (ψf n) (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ) m (ψg n)) φ]
    rw [hL]
    rw [← MeasureTheory.integral_add (Schwartz_mul_mul_integrable _ _ φ)
      (Schwartz_mul_mul_integrable _ _ φ)]
    refine congrArg Neg.neg (MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_))
    intro x; ring
  -- Limits of each sequence (rewriting the limit point via `reLp_coeFn`).
  have hLHS : Filter.Tendsto LHS Filter.atTop (nhds (∫ x : Domain3, (f x).re * (g x).re
      * (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ) m φ) x ∂(volume : Measure Domain3))) := by
    have h := tendsto_integral_mul_mul _ hdφ_bdd hψf_val hψg_val
    refine h.mono_right (le_of_eq (congrArg nhds (MeasureTheory.integral_congr_ae ?_)))
    filter_upwards [reLp_coeFn f, reLp_coeFn g] with x hxf hxg; rw [hxf, hxg]
  have hR1 : Filter.Tendsto R1 Filter.atTop (nhds (∫ x : Domain3, (fG x).re * (g x).re * (φ x)
      ∂(volume : Measure Domain3))) := by
    have h := tendsto_integral_mul_mul _ hφ_bdd hψf_grad hψg_val
    refine h.mono_right (le_of_eq (congrArg nhds (MeasureTheory.integral_congr_ae ?_)))
    filter_upwards [reLp_coeFn fG, reLp_coeFn g] with x hxf hxg; rw [hxf, hxg]
  have hR2 : Filter.Tendsto R2 Filter.atTop (nhds (∫ x : Domain3, (f x).re * (gG x).re * (φ x)
      ∂(volume : Measure Domain3))) := by
    have h := tendsto_integral_mul_mul _ hφ_bdd hψf_val hψg_grad
    refine h.mono_right (le_of_eq (congrArg nhds (MeasureTheory.integral_congr_ae ?_)))
    filter_upwards [reLp_coeFn f, reLp_coeFn gG] with x hxf hxg; rw [hxf, hxg]
  -- Uniqueness of the limit: LHS limit = -(R1 limit + R2 limit).
  have huniq := tendsto_nhds_unique hLHS ((hR1.add hR2).neg.congr (fun n => (hper n).symm))
  rw [huniq, ← MeasureTheory.integral_add (reInt_integrable fG g φ) (reInt_integrable f gG φ)]
  refine congrArg Neg.neg (MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_))
  intro x; ring

/-! #### Hölder integral pairing limit (for the H¹-test extension) -/

/-- The real `L^p × L^q → ℝ` pairing `(c, k) ↦ ∫ c·k` (for Hölder-conjugate `p q`) is continuous
in `k`; hence `kₙ → k₀` in `Lp q` gives `∫ c·kₙ → ∫ c·k₀`. -/
private theorem tendsto_integral_pairing {p q : ENNReal} [ENNReal.HolderConjugate p q]
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (c : Lp ℝ p (volume : Measure Domain3)) {k : ℕ → Lp ℝ q (volume : Measure Domain3)}
    {k₀ : Lp ℝ q (volume : Measure Domain3)}
    (hk : Filter.Tendsto k Filter.atTop (nhds k₀)) :
    Filter.Tendsto
      (fun n => ∫ x : Domain3, (c x) * (k n x) ∂(volume : Measure Domain3))
      Filter.atTop (nhds (∫ x : Domain3, (c x) * (k₀ x) ∂(volume : Measure Domain3))) := by
  set B : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.mul ℝ ℝ with hB
  have hpair : ∀ a : Lp ℝ q (volume : Measure Domain3),
      (B.lpPairing (volume : Measure Domain3) p q c a)
        = ∫ x : Domain3, (c x) * (a x) ∂(volume : Measure Domain3) := by
    intro a
    rw [ContinuousLinearMap.lpPairing_eq_integral]
    rfl
  have hcont : Filter.Tendsto (fun n => B.lpPairing (volume : Measure Domain3) p q c (k n))
      Filter.atTop (nhds (B.lpPairing (volume : Measure Domain3) p q c k₀)) :=
    ((B.lpPairing (volume : Measure Domain3) p q c).continuous.tendsto k₀).comp hk
  simpa only [hpair] using hcont

/-- **H¹-test weak Leibniz.** Same as `h1Leibniz2`, but the test factor is an `H¹` function `vt`
(with weak `eₐ`-derivative `vtG`) rather than a Schwartz function. The un-differentiated test is
paired in `L³` (its multi-direction Schwartz approximants converge in `L³` via
`reSchwartz_L3_approx`); the differentiated test in `L²`. -/
private theorem h1Leibniz2_H1test (f g fG gG vt vtG : L2C_R3) (a : Fin 3)
    (hf : MemSobolev 1 2 (f : 𝓢'(Domain3, ℂ)))
    (hg : MemSobolev 1 2 (g : 𝓢'(Domain3, ℂ)))
    (hfG : (∂_{EuclideanSpace.single a (1 : ℝ)} (f : 𝓢'(Domain3, ℂ))) = (fG : 𝓢'(Domain3, ℂ)))
    (hgG : (∂_{EuclideanSpace.single a (1 : ℝ)} (g : 𝓢'(Domain3, ℂ))) = (gG : 𝓢'(Domain3, ℂ)))
    (hvt : MemSobolev 1 2 (vt : 𝓢'(Domain3, ℂ)))
    (hvtG : (∂_{EuclideanSpace.single a (1 : ℝ)} (vt : 𝓢'(Domain3, ℂ))) = (vtG : 𝓢'(Domain3, ℂ)))
    (hf6 : MemLp (fun x => (f x).re) 6 (volume : Measure Domain3))
    (hf3 : MemLp (fun x => (f x).re) 3 (volume : Measure Domain3))
    (hg6 : MemLp (fun x => (g x).re) 6 (volume : Measure Domain3)) :
    ∫ x : Domain3, (f x).re * (g x).re * (vtG x).re ∂(volume : Measure Domain3)
      = -∫ x : Domain3,
          ((fG x).re * (g x).re + (f x).re * (gG x).re) * (vt x).re
          ∂(volume : Measure Domain3) := by
  classical
  set m : Domain3 := EuclideanSpace.single a (1 : ℝ) with hm
  -- L³ approximation of the test factor `vt`.
  obtain ⟨ψ, hψ_val, hψ_grad, Φ, hΦae, hψ3⟩ := reSchwartz_L3_approx vt vtG a hvt hvtG
  -- Membership facts for the coefficient functions.
  have hfre2 : MemLp (fun x => (f x).re) 2 (volume : Measure Domain3) := (Lp.memLp f).re
  have hgre2 : MemLp (fun x => (g x).re) 2 (volume : Measure Domain3) := (Lp.memLp g).re
  have hfGre2 : MemLp (fun x => (fG x).re) 2 (volume : Measure Domain3) := (Lp.memLp fG).re
  have hgGre2 : MemLp (fun x => (gG x).re) 2 (volume : Measure Domain3) := (Lp.memLp gG).re
  -- Coefficient `cLHS = f.re·g.re ∈ L²` (via L³·L⁶).
  haveI hHT362 : ENNReal.HolderTriple 6 3 2 := instHolderTriple_6_3_2
  have hcLHS_mem : MemLp (fun x => (f x).re * (g x).re) 2 (volume : Measure Domain3) :=
    MeasureTheory.MemLp.ae_eq (Filter.Eventually.of_forall fun x => by simp [Pi.mul_apply, mul_comm])
      (hf3.mul (p := 6) (q := 3) (r := 2) hg6)
  set cLHS : Lp ℝ 2 (volume : Measure Domain3) := hcLHS_mem.toLp with hcLHS
  -- Coefficients `cR1 = fG.re·g.re`, `cR2 = f.re·gG.re ∈ L^{3/2}` (via L²·L⁶).
  haveI hHT263 : ENNReal.HolderTriple 6 2 (3/2) := by
    have h : Real.HolderTriple (6 : ℝ) (2 : ℝ) (3/2 : ℝ) := by constructor <;> norm_num
    have h2 := h.ennrealOfReal
    have e32 : ENNReal.ofReal (3 / 2 : ℝ) = (3 / 2 : ENNReal) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp
    simpa only [ENNReal.ofReal_ofNat, e32] using h2
  haveI hHT263' : ENNReal.HolderTriple 2 6 (3/2) := by
    have h : Real.HolderTriple (2 : ℝ) (6 : ℝ) (3/2 : ℝ) := by constructor <;> norm_num
    have h2 := h.ennrealOfReal
    have e32 : ENNReal.ofReal (3 / 2 : ℝ) = (3 / 2 : ENNReal) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp
    simpa only [ENNReal.ofReal_ofNat, e32] using h2
  have hcR1_mem : MemLp (fun x => (fG x).re * (g x).re) (3/2) (volume : Measure Domain3) :=
    MeasureTheory.MemLp.ae_eq (Filter.Eventually.of_forall fun x => by simp [Pi.mul_apply, mul_comm])
      (hfGre2.mul (p := 6) (q := 2) (r := 3/2) hg6)
  have hcR2_mem : MemLp (fun x => (f x).re * (gG x).re) (3/2) (volume : Measure Domain3) :=
    MeasureTheory.MemLp.ae_eq (Filter.Eventually.of_forall fun x => by simp [Pi.mul_apply, mul_comm])
      (hf6.mul (p := 2) (q := 6) (r := 3/2) hgGre2)
  set cR1 : Lp ℝ (3/2) (volume : Measure Domain3) := hcR1_mem.toLp with hcR1
  set cR2 : Lp ℝ (3/2) (volume : Measure Domain3) := hcR2_mem.toLp with hcR2
  haveI : Fact ((1 : ENNReal) ≤ 3/2) := ⟨by
    rw [ENNReal.le_div_iff_mul_le (by norm_num) (by norm_num)]; norm_num⟩
  haveI : Fact ((1 : ENNReal) ≤ 3) := ⟨by norm_num⟩
  haveI : Fact ((1 : ENNReal) ≤ 2) := ⟨by norm_num⟩
  haveI hHC23 : ENNReal.HolderConjugate (3/2 : ENNReal) 3 := by
    have h : Real.HolderTriple (3/2 : ℝ) (3 : ℝ) (1 : ℝ) := by constructor <;> norm_num
    have h2 := h.ennrealOfReal
    have e32 : ENNReal.ofReal (3 / 2 : ℝ) = (3 / 2 : ENNReal) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp
    simpa only [ENNReal.ofReal_ofNat, ENNReal.ofReal_one, e32] using h2
  haveI hHC22 : ENNReal.HolderConjugate (2 : ENNReal) 2 := ⟨by
    rw [inv_one]; exact ENNReal.inv_two_add_inv_two⟩
  -- Per-n Schwartz Leibniz identity (Schwartz test `ψ n`).
  have hper : ∀ n,
      ∫ x : Domain3, (f x).re * (g x).re
        * (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ) m (ψ n)) x ∂(volume : Measure Domain3)
      = -∫ x : Domain3,
          ((fG x).re * (g x).re + (f x).re * (gG x).re) * (ψ n) x
          ∂(volume : Measure Domain3) :=
    fun n => h1Leibniz2 f g fG gG a hf hg hfG hgG (ψ n)
  -- LHS limit: `∫ (f.re·g.re)·(∂ₐψₙ) → ∫ (f.re·g.re)·(vtG.re)` (pairing 2,2).
  have hLHS : Filter.Tendsto
      (fun n => ∫ x : Domain3, (f x).re * (g x).re
        * (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ) m (ψ n)) x ∂(volume : Measure Domain3))
      Filter.atTop (nhds (∫ x : Domain3, (f x).re * (g x).re * (vtG x).re
        ∂(volume : Measure Domain3))) := by
    have hpair := tendsto_integral_pairing (p := 2) (q := 2) cLHS hψ_grad
    -- rewrite the pairing integrals to match.
    have hkn : ∀ n, ∫ x : Domain3, (cLHS x)
        * ((lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ) m (ψ n)).toLp 2 (volume : Measure Domain3)) x
          ∂(volume : Measure Domain3)
        = ∫ x : Domain3, (f x).re * (g x).re
          * (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ) m (ψ n)) x ∂(volume : Measure Domain3) := by
      intro n
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [hcLHS_mem.coeFn_toLp,
        (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ) m (ψ n)).coeFn_toLp 2 (volume : Measure Domain3)]
        with x hcx hkx
      rw [hcx, hkx]
    have hk0 : ∫ x : Domain3, (cLHS x) * ((reLp vtG) x) ∂(volume : Measure Domain3)
        = ∫ x : Domain3, (f x).re * (g x).re * (vtG x).re ∂(volume : Measure Domain3) := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [hcLHS_mem.coeFn_toLp, reLp_coeFn vtG] with x hcx hkx
      rw [hcx, hkx]
    rw [← hk0]
    refine hpair.congr (fun n => hkn n)
  -- RHS limit: `∫ (fG.re·g.re + f.re·gG.re)·ψₙ → ∫(...)·vt.re` (pairing 3/2,3), split in two.
  have hRHS : Filter.Tendsto
      (fun n => ∫ x : Domain3, ((fG x).re * (g x).re + (f x).re * (gG x).re) * (ψ n) x
        ∂(volume : Measure Domain3))
      Filter.atTop (nhds (∫ x : Domain3,
        ((fG x).re * (g x).re + (f x).re * (gG x).re) * (vt x).re ∂(volume : Measure Domain3))) := by
    have hp1 := tendsto_integral_pairing (p := 3/2) (q := 3) cR1 hψ3
    have hp2 := tendsto_integral_pairing (p := 3/2) (q := 3) cR2 hψ3
    -- Rewrite each pairing to the component integrals.
    have hr1n : ∀ n, ∫ x : Domain3, (cR1 x) * ((ψ n).toLp 3 (volume : Measure Domain3) x)
          ∂(volume : Measure Domain3)
        = ∫ x : Domain3, (fG x).re * (g x).re * (ψ n) x ∂(volume : Measure Domain3) := by
      intro n
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [hcR1_mem.coeFn_toLp, (ψ n).coeFn_toLp 3 (volume : Measure Domain3)]
        with x hcx hkx
      rw [hcx, hkx]
    have hr2n : ∀ n, ∫ x : Domain3, (cR2 x) * ((ψ n).toLp 3 (volume : Measure Domain3) x)
          ∂(volume : Measure Domain3)
        = ∫ x : Domain3, (f x).re * (gG x).re * (ψ n) x ∂(volume : Measure Domain3) := by
      intro n
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [hcR2_mem.coeFn_toLp, (ψ n).coeFn_toLp 3 (volume : Measure Domain3)]
        with x hcx hkx
      rw [hcx, hkx]
    have hr1lim : ∫ x : Domain3, (cR1 x) * (Φ x) ∂(volume : Measure Domain3)
        = ∫ x : Domain3, (fG x).re * (g x).re * (vt x).re ∂(volume : Measure Domain3) := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [hcR1_mem.coeFn_toLp, hΦae] with x hcx hkx
      rw [hcx, hkx]
    have hr2lim : ∫ x : Domain3, (cR2 x) * (Φ x) ∂(volume : Measure Domain3)
        = ∫ x : Domain3, (f x).re * (gG x).re * (vt x).re ∂(volume : Measure Domain3) := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [hcR2_mem.coeFn_toLp, hΦae] with x hcx hkx
      rw [hcx, hkx]
    -- Integrability for splitting the sum-integral.
    haveI hHT3321 : ENNReal.HolderTriple (3/2) 3 1 := by
      have h : Real.HolderTriple (3/2 : ℝ) (3 : ℝ) (1 : ℝ) := by constructor <;> norm_num
      have h2 := h.ennrealOfReal
      have e32 : ENNReal.ofReal (3 / 2 : ℝ) = (3 / 2 : ENNReal) := by
        rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp
      simpa only [ENNReal.ofReal_ofNat, ENNReal.ofReal_one, e32] using h2
    have hint1 : ∀ n, MeasureTheory.Integrable
        (fun x => (fG x).re * (g x).re * (ψ n) x) (volume : Measure Domain3) := by
      intro n
      have := ((ψ n).memLp 3 (volume : Measure Domain3)).mul (p := 3/2) (q := 3) (r := 1) hcR1_mem
      rw [memLp_one_iff_integrable] at this
      refine this.congr ?_
      filter_upwards with x
      simp only [Pi.mul_apply]
    have hint2 : ∀ n, MeasureTheory.Integrable
        (fun x => (f x).re * (gG x).re * (ψ n) x) (volume : Measure Domain3) := by
      intro n
      have := ((ψ n).memLp 3 (volume : Measure Domain3)).mul (p := 3/2) (q := 3) (r := 1) hcR2_mem
      rw [memLp_one_iff_integrable] at this
      refine this.congr ?_
      filter_upwards with x
      simp only [Pi.mul_apply]
    -- Combine: the n-integral = R1ₙ + R2ₙ, with limit hr1lim + hr2lim.
    have hsplit : ∀ n, ∫ x : Domain3, ((fG x).re * (g x).re + (f x).re * (gG x).re) * (ψ n) x
        ∂(volume : Measure Domain3)
        = (∫ x : Domain3, (fG x).re * (g x).re * (ψ n) x ∂(volume : Measure Domain3))
          + ∫ x : Domain3, (f x).re * (gG x).re * (ψ n) x ∂(volume : Measure Domain3) := by
      intro n
      rw [← MeasureTheory.integral_add (hint1 n) (hint2 n)]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      ring
    -- integrability of the two limit coefficients against `vt.re`.
    have hvt_re3 : MemLp (fun x => (vt x).re) 3 (volume : Measure Domain3) :=
      L2L6_inter_mem_L3 _ (Lp.memLp vt).re ((gns_L6_of_memH1_R3 vt hvt).re)
    have hintlim1 : MeasureTheory.Integrable
        (fun x => (fG x).re * (g x).re * (vt x).re) (volume : Measure Domain3) := by
      have := ((hvt_re3).mul (p := 3/2) (q := 3) (r := 1) hcR1_mem)
      rw [memLp_one_iff_integrable] at this
      refine this.congr ?_; filter_upwards with x; simp only [Pi.mul_apply]
    have hintlim2 : MeasureTheory.Integrable
        (fun x => (f x).re * (gG x).re * (vt x).re) (volume : Measure Domain3) := by
      have := ((hvt_re3).mul (p := 3/2) (q := 3) (r := 1) hcR2_mem)
      rw [memLp_one_iff_integrable] at this
      refine this.congr ?_; filter_upwards with x; simp only [Pi.mul_apply]
    have hcomb := ((hp1.congr hr1n).add (hp2.congr hr2n))
    rw [hr1lim, hr2lim, ← MeasureTheory.integral_add hintlim1 hintlim2] at hcomb
    have hcomb2 : Filter.Tendsto
        (fun n => ∫ x : Domain3, ((fG x).re * (g x).re + (f x).re * (gG x).re) * (ψ n) x
          ∂(volume : Measure Domain3)) Filter.atTop
        (nhds (∫ x : Domain3, ((fG x).re * (g x).re * (vt x).re
          + (f x).re * (gG x).re * (vt x).re) ∂(volume : Measure Domain3))) :=
      hcomb.congr (fun n => (hsplit n).symm)
    refine hcomb2.mono_right (le_of_eq (congrArg nhds ?_))
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    ring
  -- Equate the two limits.
  have hlim : (∫ x : Domain3, (f x).re * (g x).re * (vtG x).re ∂(volume : Measure Domain3))
      = -(∫ x : Domain3, ((fG x).re * (g x).re + (f x).re * (gG x).re) * (vt x).re
          ∂(volume : Measure Domain3)) := by
    refine tendsto_nhds_unique hLHS ?_
    exact (hRHS.neg).congr (fun n => (hper n).symm)
  exact hlim

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
    (hu_sigma : (u : L2VF_R3) ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3))
    (hw_sigma : (w : L2VF_R3) ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3)) :
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

set_option maxHeartbeats 1000000 in
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
    (hv_sigma : (v : L2VF_R3) ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3))
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
        (hu_sigma : (u : L2VF_R3) ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3))
        (hv_sigma : (v : L2VF_R3) ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3)),
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
