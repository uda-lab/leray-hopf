import LerayHopf.R3.SobolevEmbedding
import LerayHopf.R3.ConvectionOperator
-- SobolevEmbedding.lean import justification: provides A1 (HolderTriple instances),
--   A3 (gns_L6_of_memH1_R3: H¹↪L⁶), A4 (h1Sigma_dense_in_L2Sigma),
--   and transitively Regularity.lean (memH1VF_R3, IsSchwartzDivFree_R3).
-- ConvectionOperator.lean import justification: provides convFormSchwartz,
--   convFormSchwartz_antisymm, convFormSchwartz_eq_witness (used by B5).

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
Three targets remain marked `-- ALLOW_SORRY`:

- **B6a** (`convFormH1_ibp`), **B6** (`convFormH1_antisymm`), **B7** (`convFormH1_bound_Schwartz`)
  — gated on the weak Leibniz product rule `∂ₐ(uₐ·wᵢ) = (∂ₐuₐ)wᵢ + uₐ(∂ₐwᵢ)` (a distributional
  identity for **two** H¹ factors), which is absent from mathlib (only the Schwartz×Schwartz IBP
  `integral_bilinear_lineDerivOp_right_eq_neg_left` and no smooth-multiplier-×-distribution
  Leibniz exist) and is a substantial analytic development (mollification + H¹-limit + L⁶·L²·L³
  Hölder). B6 ⇒ B7 (CODEX route), and B6 ⇒ B6a. The PR-2 Brick-1 export
  `LerayHopf.schwartz_h1_gradConv` (SobolevEmbedding.lean, simultaneous L² value- and
  gradient-convergence of Schwartz approximants; axiom-clean) is now landed and is the smoothing
  tool the eventual B6a proof will use; the remaining gap is exactly the Leibniz lemma itself.
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
elements of `L²(ℝ³; ℝ³)` that satisfy the H¹ regularity condition `memH1VF_R3`.

This is a genuine `Submodule ℝ L2VF_R3`, with:
- closure under addition: B1a (`memH1VF_R3_add`);
- closure under ℝ-scalar multiplication: B1b (`memH1VF_R3_smul`);
- zero member: B1c (`memH1VF_R3_zero`).

Used by B2–B7 to quantify over `H¹_σ` elements. -/
def H1Sigma_R3 : Submodule ℝ L2VF_R3 where
  carrier := {u | memH1VF_R3 u}
  add_mem' {u v} hu hv := memH1VF_R3_add hu hv
  zero_mem' := memH1VF_R3_zero
  smul_mem' c {u} hu := memH1VF_R3_smul c hu

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
  sorry -- ALLOW_SORRY: PR-2 (B6a) BLOCKED on the H¹·H¹ weak Leibniz product rule ∂ₐ(uₐ·wᵢ)=(∂ₐuₐ)wᵢ+uₐ(∂ₐwᵢ) as a distributional identity for two H¹ factors (uₐ, wᵢ). Mathlib has NO weak-derivative product rule for an H¹·H¹ product (only the Schwartz `integral_bilinear_lineDerivOp_right_eq_neg_left` for two Schwartz factors); the smooth-multiplier × distribution Leibniz (`lineDerivOp` ∘ `smulLeftCLM`) is also absent. Sound discharge needs a from-scratch mollification development (smooth-approx uₐ,wᵢ via Brick-1 `schwartz_h1_gradConv`, classical Leibniz, then H¹-limit + L⁶·L²·L³ Hölder continuity). Brick-1 (schwartz_h1_gradConv) is now available and axiom-clean; the remaining gap is exactly this Leibniz lemma.

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
  sorry -- ALLOW_SORRY: PR-2 (B6) DEPENDS ON B6a; transitively blocked on the same H¹·H¹ weak Leibniz product rule (see convFormH1_ibp). Given B6a + B6b (proved), B6 closes by reindexing and the div-free cancellation of ∑ₐ(∂ₐuₐ)vᵢwᵢ; the only missing pillar is B6a.

/-! ### B7 — L²-norm bound for fixed Schwartz test (CODEX CORRECTION route) -/

/-- **B7 `convFormH1_bound_Schwartz` [must-prove — CODEX CORRECTION].** For `u, v ∈ H1Sigma_R3`
(with `u, v, w ∈ L2Sigma_R3`) and fixed Schwartz `w` (`IsSchwartzDivFree_R3 w`):

  `|convFormH1 u v w hu hv hw_H1| ≤ C_w * ‖(u : L2VF_R3)‖ * ‖(v : L2VF_R3)‖`

where `C_w` depends only on the Schwartz seminorms of `w` (specifically `‖∇w‖_{L^∞}`).

**⚠️ CODEX CORRECTION (PR-1 #58 review):** The bound in L²-norms `‖u‖₂ · ‖v‖₂` follows
via **B6 (antisymmetry/IBP): move the derivative onto the fixed Schwartz test w**.

Route:
1. By B6 antisymmetry: `convFormH1 u v w = -convFormH1 u w v = +convFormH1_moveDeriv u v w`
   where `convFormH1_moveDeriv u v w = ∑_{i,a} ∫ uₐ · ∂ₐwᵢ · vᵢ`
   (derivative moved onto `w` via IBP).
2. Estimate: `|∑_{i,a} ∫ uₐ · ∂ₐwᵢ · vᵢ| ≤ ∑_{i,a} ‖∂ₐwᵢ‖_∞ · ‖uₐ‖_{L²} · ‖vᵢ‖_{L²}`
   (Cauchy–Schwarz: `|∫ f·g| ≤ ‖f‖_{L²}‖g‖_{L²}` with `f = uₐ`, `g = ∂ₐwᵢ · vᵢ`).
3. Since `w` is Schwartz, `‖∂ₐwᵢ‖_∞ < ∞`; set `C_w := ∑_{i,a} ‖∂ₐwᵢ‖_∞ · 3 · 3`.
4. Use `‖uₐ‖_{L²} ≤ ‖u‖_{L²}` and `‖vᵢ‖_{L²} ≤ ‖v‖_{L²}` (component projections are
   contractions: `‖L2VF_projComponent_R3 j‖ ≤ 1`).

**Note:** A3/GNS is NOT needed for B7 (per CODEX CORRECTION). The L²-bound is achieved
by moving ∂ onto the Schwartz test, not by invoking GNS on u,v. The `C_w` is finite
because w is Schwartz (all derivatives are in L^∞). -/
theorem convFormH1_bound_Schwartz (u v w : L2VF_R3)
    (hu : memH1VF_R3 u) (hv : memH1VF_R3 v) (hw_H1 : memH1VF_R3 w)
    (hu_sigma : (u : L2VF_R3) ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3))
    (hv_sigma : (v : L2VF_R3) ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3))
    (hw_sigma : (w : L2VF_R3) ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3))
    (hw_sch : IsSchwartzDivFree_R3 ⟨w, hw_sigma⟩) :
    ∃ C_w : ℝ, 0 ≤ C_w ∧
      |convFormH1 u v w hu hv hw_H1| ≤ C_w * ‖(u : L2VF_R3)‖ * ‖(v : L2VF_R3)‖ := by
  sorry -- ALLOW_SORRY: PR-2 (B7) DEPENDS ON B6 (and hence B6a). The L²·L² bound REQUIRES moving the derivative off v onto the Schwartz test w (antisymmetry/IBP): a direct estimate only yields C_w·‖u‖₂·‖v‖_{H¹} (the ∂ₐvᵢ factor is bounded by ‖v‖_{H¹}, not ‖v‖₂), so the ‖v‖₂ conclusion genuinely needs B6. Transitively blocked on the same H¹·H¹ weak Leibniz pillar (see convFormH1_ibp).

end LerayHopf
