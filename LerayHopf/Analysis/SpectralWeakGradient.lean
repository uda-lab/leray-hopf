import LerayHopf.R3.Regularity
import Mathlib.Analysis.Distribution.Sobolev
-- Sobolev.lean import justification: MemSobolev.add, MemSobolev.smul, MemSobolev.lineDerivOp,
--   used to extract the spectral L² weak-derivative representative below.

namespace LerayHopf

open MeasureTheory TemperedDistribution SchwartzMap LineDeriv

/-!
# Spectral weak-gradient component and its integration-by-parts identity

Generic H¹(ℝ³) infrastructure extracted from `EnergyClassConvection.lean` (issue #113 PR-2):
for `u : L2VF_R3` with `memH1VF_R3 u`, `gradComp_of_memH1 u hu a j` is the `L²(ℝ³;ℂ)`
representative of the weak directional derivative `∂_{eₐ}` of the `j`-th complex component of
`u`, extracted from `TemperedDistribution.MemSobolev` via `MemSobolev.lineDerivOp` +
`memSobolev_zero_iff`. `gradComponent_weakDeriv` is the integration-by-parts identity relating
it to the classical Schwartz IBP; `gradComp_of_memH1_add`/`_smul` are its linearity in the field
argument. None of this is convection-specific — it is pure H¹/Sobolev machinery.

## Declarations

- `cxify`, `cxify_apply`, `lineDerivOp_cxify` — complexification of a real Schwartz map and its
  commutation with the line derivative. Kept public (not `private` as on `main`): the B3a/B6
  content still left in `EnergyClassConvection.lean` (pending issue #113 PR-2 commits 4-5)
  references them by name.
- `gradComp_of_memH1`, `gradComp_of_memH1_spec` — the spectral L² weak-derivative representative
  and its defining tempered-distribution identity
- `gradComponent_weakDeriv` — the classical IBP identity against a Schwartz test
- `L2C_eq_of_toTempered_eq` — injectivity of the `Lp → 𝓢'` embedding. Also kept public for the
  same cross-file-reference reason as `cxify` above.
- `gradComp_of_memH1_add`, `gradComp_of_memH1_smul` — linearity of `gradComp_of_memH1` in the
  field argument

All public names/statements preserved from `EnergyClassConvection.lean`.

## Assumptions

No `axiom`/`opaque`/`constant`/`unsafe` in this file.
-/

/-! ### Helpers — complexification of real Schwartz tests -/

/-- Complexification of a real Schwartz map: post-compose with `ofRealCLM : ℝ →L[ℝ] ℂ`. -/
noncomputable def cxify (φ : SchwartzMap Domain3 ℝ) : SchwartzMap Domain3 ℂ :=
  φ.postcompCLM (RCLike.ofRealCLM (K := ℂ))

/-- The complexification `cxify φ` evaluates pointwise as the real-to-complex coercion of
`φ`. -/
@[simp] theorem cxify_apply (φ : SchwartzMap Domain3 ℝ) (x : Domain3) :
    cxify φ x = ((φ x : ℝ) : ℂ) := by
  simp [cxify, SchwartzMap.postcompCLM_apply]

/-- Complexification commutes with the line derivative: `∂_{m}(cxify φ) = cxify (∂_{m} φ)`.
Both sides agree pointwise: `lineDeriv` commutes with the `ℝ`-linear map `ofRealCLM`. -/
theorem lineDerivOp_cxify (m : Domain3) (φ : SchwartzMap Domain3 ℝ) :
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
theorem L2C_eq_of_toTempered_eq {f g : L2C_R3}
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

end LerayHopf
