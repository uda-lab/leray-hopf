import LerayHopf.R3.GalerkinODEExistence
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.ODE.ExistUnique  -- issue #111 PR-3: the pinned mathlib now has this
  -- file (it did not when the local wrappers below were written); it directly provides
  -- IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt,
  -- ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt, and
  -- ODE_solution_unique_of_mem_Icc_{right,left,''} with identical statements.
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-!
# Forward-global existence of the finite-dim Galerkin ODE on ℝ³ (Pillar E, R-global)

**Milestone:** `findim-global-ode` (Pillar E — the last frontier of milestone E).

This file **constructs** a term `Nonempty (FinDimGlobalODE B F ν u₀ n)` — UNCONDITIONALLY,
discharging the residual R-global hypothesis isolated in `GalerkinODEExistence.lean`. Combined
with the already-proved `galerkinODEInput_of_basis`, the Galerkin ODE solution becomes
unconditional over the concrete scheme `schemeOfBasis B`.

## HONEST scope (forward time)

The deliverable proves **FORWARD-time global existence** of the autonomous finite-dim Galerkin
ODE `c' = G_n(c)` on `V_n := galerkinSpan B n`:

* the vector field `G_n := galerkinODE_vectorField B F ν n` is `C¹` (indeed smooth) on the
  finite-dimensional `V_n` — it is quadratic-plus-linear, and on a finite-dim space every
  multilinear map is continuous and every continuous bilinear map is `ContDiff` (C1);
* along any local solution the energy `½‖c t‖²` is non-increasing (the dissipation identity
  `d/dt ½‖c‖² = −ν·viscousFormSq_R3 1 (c t) ≤ 0`, A1/A2), giving the forward a-priori bound
  `‖c t‖ ≤ ‖c 0‖` (A3);
* hence the solution stays in the fixed a-priori ball `closedBall 0 R`, `R := ‖galerkinP B n u₀‖`,
  where the **uniform** local-existence time of mathlib's
  `ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt` applies; tiling
  `[0,∞)` with that uniform time and gluing via `ODE_solution_unique_of_mem_Icc` yields a
  forward-global solution (G1).

This is **exactly** what `FinDimGlobalODE` now requires: after the forward-time refactor of that
structure (`c_hasDeriv`/`ode` quantified `∀ t, 0 ≤ t →`), the deliverable D is constructible from
G1 with no residual hypothesis. The two-sided `∀ t : ℝ` requirement no longer exists, so there is
**no backward-time smuggling**: backward-time confinement (which the energy bound does NOT supply,
see `docs/scratch/findim-global-ode.md` §1.4) is simply not needed.

## DAG (no cycle)

`SolutionInterfaces → GalerkinODE → GalerkinODEExistence → GalerkinODESolve [THIS FILE]` and
`GalerkinScheme → GalerkinODEExistence`. This file is imported by no other `LerayHopf` module
(one-directional DAG, like the existing siblings); root `LerayHopf.lean` adds it after the
`import LerayHopf.R3.GalerkinODEExistence` line (deferred — done by the root consolidation step).

## Import justification

* `Mathlib.Analysis.ODE.PicardLindelof` — `IsPicardLindelof.of_contDiffAt_one` and the uniform
  local-existence time used by G1's tiling; also transitively re-exports the `ExistUnique` lemmas.
* `Mathlib.Analysis.ODE.Gronwall` — `ODE_solution_unique_of_mem_Icc` (gluing of overlapping
  tiles), via the `ExistUnique` re-export.
* `Mathlib.Analysis.Calculus.ContDiff.FiniteDimension` — `contDiff_clm_apply_iff` and finite-dim
  auto-continuity used by C1 (the `C¹`-field lemma).

## Assumptions / axioms

**Zero** new `axiom`/`opaque`/`constant`/`unsafe`. The only non-permanent markers are the
`ALLOW_SORRY` scaffold placeholders below, each a `lean-prover` target for the
`findim-global-ode` milestone.
-/

namespace LerayHopf

open MeasureTheory Metric Set
open MeasureTheory FourierTransform
open scoped Topology InnerProductSpace FourierTransform SchwartzMap NNReal

/-! ## C1 — the Galerkin field is `C¹` on the finite-dim `V_n`

`galerkinODE_vectorField B F ν n` is the Riesz representative of the functional
`w ↦ −ν·stokes(u,w) − b(u,u,w)`, which is linear-plus-quadratic in `u`. On the
finite-dimensional `V_n := galerkinSpan B n` every multilinear map is continuous and every
continuous bilinear map is `ContDiff ℝ ⊤`, so the field is `C¹`. The helper defs split it into a
continuous-linear part (the `−ν·stokes` term) and a continuous-bilinear part (the `b` term).
-/

/-- The Riesz inverse as a `ContinuousLinearMap` `(V_n →L[ℝ] ℝ) →L[ℝ] V_n`. -/
private noncomputable def rieszSymmCLM (B : SchwartzGalerkinBasis) (n : ℕ) :
    (galerkinSpan B n →L[ℝ] ℝ) →L[ℝ] galerkinSpan B n :=
  (InnerProductSpace.toDual ℝ (galerkinSpan B n)).symm.toContinuousLinearMap

@[simp] private theorem rieszSymmCLM_apply (B : SchwartzGalerkinBasis) (n : ℕ)
    (φ : galerkinSpan B n →L[ℝ] ℝ) :
    rieszSymmCLM B n φ = (InnerProductSpace.toDual ℝ (galerkinSpan B n)).symm φ := rfl

/-! ### Bilinear `b`-part, built level by level on the finite-dim `V_n` -/

/-- Inner functional (slot 3): `w ↦ -b(σu, σu', σw)`, linear in `w` by `b_add_3`/`b_smul_3`. -/
private noncomputable def bInner (B : SchwartzGalerkinBasis) (F : R3NSForms (schemeOfBasis B))
    (n : ℕ) (u u' : galerkinSpan B n) : galerkinSpan B n →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => - F.b (galerkinSpanToSigma B n u) (galerkinSpanToSigma B n u')
          (galerkinSpanToSigma B n w)
      map_add' := by
        intro w w'
        rw [galerkinSpanToSigma_add, F.b_add_3]; ring
      map_smul' := by
        intro c w
        rw [galerkinSpanToSigma_smul, F.b_smul_3]
        simp only [RingHom.id_apply, smul_eq_mul]; ring }

@[simp] private theorem bInner_apply (B : SchwartzGalerkinBasis) (F : R3NSForms (schemeOfBasis B))
    (n : ℕ) (u u' w : galerkinSpan B n) :
    bInner B F n u u' w = - F.b (galerkinSpanToSigma B n u) (galerkinSpanToSigma B n u')
      (galerkinSpanToSigma B n w) := rfl

/-- Middle map (slot 2): `u' ↦ bInner u u'`, linear in `u'` by `b_add_2`/`b_smul_2`. -/
private noncomputable def bMid (B : SchwartzGalerkinBasis) (F : R3NSForms (schemeOfBasis B))
    (n : ℕ) (u : galerkinSpan B n) : galerkinSpan B n →L[ℝ] galerkinSpan B n →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun u' => bInner B F n u u'
      map_add' := by
        intro u' u''
        ext w
        simp only [ContinuousLinearMap.add_apply, bInner_apply, galerkinSpanToSigma_add,
          F.b_add_2]; ring
      map_smul' := by
        intro c u'
        ext w
        simp only [RingHom.id_apply, ContinuousLinearMap.smul_apply, bInner_apply,
          galerkinSpanToSigma_smul, F.b_smul_2, smul_eq_mul]; ring }

@[simp] private theorem bMid_apply (B : SchwartzGalerkinBasis) (F : R3NSForms (schemeOfBasis B))
    (n : ℕ) (u u' : galerkinSpan B n) :
    bMid B F n u u' = bInner B F n u u' := rfl

/-- Outer map (slot 1): `u ↦ bMid u`, linear in `u` by `b_add_1`/`b_smul_1`. -/
private noncomputable def bOut (B : SchwartzGalerkinBasis) (F : R3NSForms (schemeOfBasis B))
    (n : ℕ) : galerkinSpan B n →L[ℝ] galerkinSpan B n →L[ℝ] galerkinSpan B n →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun u => bMid B F n u
      map_add' := by
        intro u u''
        ext u' w
        simp only [ContinuousLinearMap.add_apply, bMid_apply, bInner_apply,
          galerkinSpanToSigma_add, F.b_add_1]; ring
      map_smul' := by
        intro c u
        ext u' w
        simp only [RingHom.id_apply, ContinuousLinearMap.smul_apply, bMid_apply, bInner_apply,
          galerkinSpanToSigma_smul, F.b_smul_1, smul_eq_mul]; ring }

@[simp] private theorem bOut_apply (B : SchwartzGalerkinBasis) (F : R3NSForms (schemeOfBasis B))
    (n : ℕ) (u : galerkinSpan B n) :
    bOut B F n u = bMid B F n u := rfl

/-- **Helper (C1).** The bilinear part of the Galerkin field: the continuous-bilinear map
`V_n × V_n → V_n` representing the quadratic `b`-term `(u, u') ↦ (toDual).symm (w ↦ −b(u,u',w))`,
so that the field is `u ↦ Bil(u,u) + Lin u`. Built level by level (`bInner`/`bMid`/`bOut`) from
`F.b`'s multilinearity (`b_add_*`/`b_smul_*`) with finite-dim auto-continuity at each level, then
post-composed with the Riesz inverse CLM. -/
noncomputable def galerkinODE_bilinearPart
    (B : SchwartzGalerkinBasis) (F : R3NSForms (schemeOfBasis B)) (ν : ℝ) (n : ℕ) :
    galerkinSpan B n →L[ℝ] galerkinSpan B n →L[ℝ] galerkinSpan B n :=
  (ContinuousLinearMap.compL ℝ (galerkinSpan B n) (galerkinSpan B n →L[ℝ] ℝ)
      (galerkinSpan B n) (rieszSymmCLM B n)).comp (bOut B F n)

@[simp] private theorem galerkinODE_bilinearPart_apply
    (B : SchwartzGalerkinBasis) (F : R3NSForms (schemeOfBasis B)) (ν : ℝ) (n : ℕ)
    (u u' : galerkinSpan B n) :
    galerkinODE_bilinearPart B F ν n u u'
      = rieszSymmCLM B n (bInner B F n u u') := rfl

/-! ### Linear `−ν·stokes`-part -/

/-- Inner functional: `w ↦ -ν·stokes(σu, σw)`, linear in `w` by the stokes right-slot
linearity (`stokesTestPairing_R3_add_right`/`_smul_right`). -/
private noncomputable def stokesInner (B : SchwartzGalerkinBasis) (ν : ℝ) (n : ℕ)
    (u : galerkinSpan B n) : galerkinSpan B n →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => - ν * stokesTestPairing_R3 (u : L2VF_R3) (w : L2VF_R3)
      map_add' := by
        intro w w'
        rw [show ((w + w' : galerkinSpan B n) : L2VF_R3)
            = ((w : galerkinSpan B n) + (w' : galerkinSpan B n) : galerkinSpan B n) from rfl,
          stokesTestPairing_R3_add_right]; ring
      map_smul' := by
        intro c w
        rw [show ((c • w : galerkinSpan B n) : L2VF_R3)
            = ((c • w : galerkinSpan B n) : galerkinSpan B n) from rfl,
          stokesTestPairing_R3_smul_right]
        simp only [RingHom.id_apply, smul_eq_mul]; ring }

@[simp] private theorem stokesInner_apply (B : SchwartzGalerkinBasis) (ν : ℝ) (n : ℕ)
    (u w : galerkinSpan B n) :
    stokesInner B ν n u w = - ν * stokesTestPairing_R3 (u : L2VF_R3) (w : L2VF_R3) := rfl

/-- Stokes is symmetric on `V_n` span elements: the integrand `Re[(𝓕 uⱼ)·conj(𝓕 wⱼ)]` equals
`Re[(𝓕 wⱼ)·conj(𝓕 uⱼ)]` pointwise, so the whole pairing is symmetric (no integrability needed). -/
private theorem stokesTestPairing_R3_symm (u w : L2VF_R3) :
    stokesTestPairing_R3 u w = stokesTestPairing_R3 w u := by
  unfold stokesTestPairing_R3
  refine Finset.sum_congr rfl (fun j _ => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall (fun ξ => ?_))
  -- It suffices to equate the `.re` factors.
  have hre : ((𝓕 (L2VF_projComponentC_R3 j u) : L2C_R3) ξ *
        (starRingEnd ℂ) ((𝓕 (L2VF_projComponentC_R3 j w) : L2C_R3) ξ)).re
      = ((𝓕 (L2VF_projComponentC_R3 j w) : L2C_R3) ξ *
          (starRingEnd ℂ) ((𝓕 (L2VF_projComponentC_R3 j u) : L2C_R3) ξ)).re := by
    rw [← Complex.conj_re ((𝓕 (L2VF_projComponentC_R3 j w) : L2C_R3) ξ *
        (starRingEnd ℂ) ((𝓕 (L2VF_projComponentC_R3 j u) : L2C_R3) ξ))]
    congr 1
    rw [map_mul, Complex.conj_conj]
    ring
  exact congrArg (fun r => (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 * r) hre

/-- Left-additivity of `−ν·stokes(·, w)` on span elements, via right-additivity + symmetry. -/
private theorem stokesInner_add (B : SchwartzGalerkinBasis) (ν : ℝ) (n : ℕ)
    (u u' w : galerkinSpan B n) :
    stokesTestPairing_R3 ((u + u' : galerkinSpan B n) : L2VF_R3) (w : L2VF_R3)
      = stokesTestPairing_R3 (u : L2VF_R3) (w : L2VF_R3)
        + stokesTestPairing_R3 (u' : L2VF_R3) (w : L2VF_R3) := by
  rw [stokesTestPairing_R3_symm ((u + u' : galerkinSpan B n) : L2VF_R3),
    show ((u + u' : galerkinSpan B n) : L2VF_R3)
      = ((u : galerkinSpan B n) + (u' : galerkinSpan B n) : galerkinSpan B n) from rfl,
    stokesTestPairing_R3_add_right, stokesTestPairing_R3_symm (w : L2VF_R3) (u : L2VF_R3),
    stokesTestPairing_R3_symm (w : L2VF_R3) (u' : L2VF_R3)]

/-- Left-homogeneity of `−ν·stokes(·, w)` on span elements, via right-homogeneity + symmetry. -/
private theorem stokesInner_smul (B : SchwartzGalerkinBasis) (ν : ℝ) (n : ℕ)
    (c : ℝ) (u w : galerkinSpan B n) :
    stokesTestPairing_R3 ((c • u : galerkinSpan B n) : L2VF_R3) (w : L2VF_R3)
      = c * stokesTestPairing_R3 (u : L2VF_R3) (w : L2VF_R3) := by
  rw [stokesTestPairing_R3_symm ((c • u : galerkinSpan B n) : L2VF_R3),
    show ((c • u : galerkinSpan B n) : L2VF_R3)
      = ((c • u : galerkinSpan B n) : galerkinSpan B n) from rfl,
    stokesTestPairing_R3_smul_right, stokesTestPairing_R3_symm (w : L2VF_R3) (u : L2VF_R3)]

/-- Outer map: `u ↦ stokesInner u`, linear in `u` by left-linearity of stokes. -/
private noncomputable def stokesOut (B : SchwartzGalerkinBasis) (ν : ℝ) (n : ℕ) :
    galerkinSpan B n →L[ℝ] galerkinSpan B n →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun u => stokesInner B ν n u
      map_add' := by
        intro u u'
        ext w
        simp only [ContinuousLinearMap.add_apply, stokesInner_apply]
        rw [stokesInner_add B ν n u u' w]; ring
      map_smul' := by
        intro c u
        ext w
        simp only [RingHom.id_apply, ContinuousLinearMap.smul_apply, stokesInner_apply,
          smul_eq_mul]
        rw [stokesInner_smul B ν n c u w]; ring }

@[simp] private theorem stokesOut_apply (B : SchwartzGalerkinBasis) (ν : ℝ) (n : ℕ)
    (u : galerkinSpan B n) :
    stokesOut B ν n u = stokesInner B ν n u := rfl

/-- **Helper (C1).** The linear part of the Galerkin field: the continuous-linear map
`V_n → V_n` representing `u ↦ (toDual).symm (w ↦ −ν·stokes(u,w))`, the Riesz inverse of the
`stokesOut`-functional. -/
noncomputable def galerkinODE_linearPart
    (B : SchwartzGalerkinBasis) (F : R3NSForms (schemeOfBasis B)) (ν : ℝ) (n : ℕ) :
    galerkinSpan B n →L[ℝ] galerkinSpan B n :=
  (rieszSymmCLM B n).comp (stokesOut B ν n)

@[simp] private theorem galerkinODE_linearPart_apply
    (B : SchwartzGalerkinBasis) (F : R3NSForms (schemeOfBasis B)) (ν : ℝ) (n : ℕ)
    (u : galerkinSpan B n) :
    galerkinODE_linearPart B F ν n u = rieszSymmCLM B n (stokesInner B ν n u) := rfl

set_option maxHeartbeats 2000000 in
/-- The Galerkin field equals `Bil(u,u) + Lin u`, by Riesz injectivity (test against all `w`). -/
private theorem galerkinODE_vectorField_eq_parts
    (B : SchwartzGalerkinBasis) (F : R3NSForms (schemeOfBasis B)) (ν : ℝ) (n : ℕ)
    (u : galerkinSpan B n) :
    galerkinODE_vectorField B F ν n u
      = galerkinODE_bilinearPart B F ν n u u + galerkinODE_linearPart B F ν n u := by
  -- Both sides are determined by their inner products against every `w ∈ V_n` (R2).
  refine ext_inner_right ℝ (fun w => ?_)
  -- LHS coordinate via R2 (transported to the ambient inner product).
  have hLHS : inner (𝕜 := ℝ) (galerkinODE_vectorField B F ν n u) w
      = - ν * stokesTestPairing_R3 (u : L2VF_R3) (w : L2VF_R3)
        - F.b (galerkinSpanToSigma B n u) (galerkinSpanToSigma B n u)
              (galerkinSpanToSigma B n w) := by
    rw [Submodule.coe_inner (galerkinSpan B n) (galerkinODE_vectorField B F ν n u) w]
    exact galerkinODE_vectorField_spec B F ν n u w
  -- RHS coordinate: split the sum, each Riesz term recovers its functional value.
  have hbil : inner (𝕜 := ℝ) (galerkinODE_bilinearPart B F ν n u u) w
      = - F.b (galerkinSpanToSigma B n u) (galerkinSpanToSigma B n u)
          (galerkinSpanToSigma B n w) := by
    rw [galerkinODE_bilinearPart_apply, rieszSymmCLM_apply,
      InnerProductSpace.toDual_symm_apply, bInner_apply]
  have hlin : inner (𝕜 := ℝ) (galerkinODE_linearPart B F ν n u) w
      = - ν * stokesTestPairing_R3 (u : L2VF_R3) (w : L2VF_R3) := by
    rw [galerkinODE_linearPart_apply, rieszSymmCLM_apply,
      InnerProductSpace.toDual_symm_apply, stokesInner_apply]
  rw [hLHS, inner_add_left, hbil, hlin]
  ring

/-- **C1 (the enabler, MUST-PROVE).** The Galerkin field `G_n` is `C¹` (indeed smooth) on the
finite-dim `V_n`: it is `Bil(u,u) + Lin u`, a quadratic-plus-linear map of `u`. The diagonal
`u ↦ Bil(u,u)` is `ContDiff` (`Bil.contDiff.clm_apply contDiff_id`), the linear part is
`ContinuousLinearMap.contDiff`, and their sum is `ContDiff`. Finite-dim auto-continuity supplied
all continuity in `bInner`/`bMid`/`bOut`/`stokesInner`/`stokesOut`; no continuity hypothesis on
`b` is needed. -/
theorem galerkinODE_vectorField_contDiff
    (B : SchwartzGalerkinBasis) (F : R3NSForms (schemeOfBasis B)) (ν : ℝ) (n : ℕ) :
    ContDiff ℝ 1 (galerkinODE_vectorField B F ν n) := by
  have hfun : galerkinODE_vectorField B F ν n
      = fun u => galerkinODE_bilinearPart B F ν n u u + galerkinODE_linearPart B F ν n u := by
    funext u; exact galerkinODE_vectorField_eq_parts B F ν n u
  rw [hfun]
  have hbil : ContDiff ℝ 1 (fun u => galerkinODE_bilinearPart B F ν n u u) :=
    (galerkinODE_bilinearPart B F ν n).contDiff.clm_apply contDiff_id
  have hlin : ContDiff ℝ 1 (fun u => galerkinODE_linearPart B F ν n u) :=
    (galerkinODE_linearPart B F ν n).contDiff
  exact hbil.add hlin

/-! ## A1 — the dissipation identity at a point -/

/-- **A1 (MUST-PROVE).** `⟪v, G_n v⟫ = −ν · viscousFormSq_R3 1 v ≤ 0` for `v ∈ V_n` (the
dissipation identity at a point), from R2 + `b_self_zero` + `stokesTestPairing_R3_diag`.

Proof sketch: apply `galerkinODE_vectorField_spec B F ν n v v` (testing `G_n v` against `v`),
then `R3NSForms.b_self_zero` kills the `b`-term and `stokesTestPairing_R3_diag` turns the stokes
term into `viscousFormSq_R3 1 v`; the result `−ν·viscousFormSq_R3 1 v ≤ 0` follows from
`viscousFormSq_R3_nonneg` and `mul_nonneg hν.le`. (Use `real_inner_comm` to align slots with R2.) -/
theorem galerkinField_inner_self_nonpos
    (B : SchwartzGalerkinBasis) (F : R3NSForms (schemeOfBasis B)) (ν : ℝ) (n : ℕ) (hν : 0 < ν)
    (v : galerkinSpan B n) :
    inner (𝕜 := ℝ) (v : L2VF_R3) (galerkinODE_vectorField B F ν n v : L2VF_R3) ≤ 0 := by
  have hval : inner (𝕜 := ℝ) (v : L2VF_R3) (galerkinODE_vectorField B F ν n v : L2VF_R3)
      = - ν * viscousFormSq_R3 1 (v : L2VF_R3) := by
    rw [real_inner_comm]
    have hspec := galerkinODE_vectorField_spec B F ν n v v
    rw [hspec, R3NSForms.b_self_zero F (galerkinSpanToSigma B n v), sub_zero,
      stokesTestPairing_R3_diag]
  rw [hval, neg_mul]
  exact neg_nonpos.mpr (mul_nonneg hν.le (viscousFormSq_R3_nonneg zero_le_one _))

/-! ## A2 — the local energy identity (forward) -/

/-- **A2 (MUST-PROVE).** Along ANY (local) solution `c` of `c' = G_n(c)` (here `c : ℝ → V_n` with
`HasDerivAt` at `t` into the ambient `L2VF_R3`), the energy `½‖c t‖²` has derivative
`−ν·viscousFormSq_R3 1 (c t) ≤ 0`. Local analogue of `galerkin_energy_identity`.

Proof sketch (mirror `galerkin_energy_identity`, `GalerkinODE.lean:185`, but local): rewrite
`½‖c s‖²` as `½⟪c s, c s⟫` via `real_inner_self_eq_norm_sq`; differentiate via `hc.inner ℝ hc`
giving `½(⟪c t, c'⟫ + ⟪c', c t⟫)`; with `c' = G_n (c t)`, `real_inner_comm` + A1's exact-value
form (`⟪c t, G_n (c t)⟫ = −ν·viscousFormSq_R3 1 (c t)`) collapse it to
`−ν·viscousFormSq_R3 1 (c t)`. -/
theorem energy_hasDerivAt_of_localSolution
    (B : SchwartzGalerkinBasis) (F : R3NSForms (schemeOfBasis B)) (ν : ℝ) (n : ℕ)
    (c : ℝ → galerkinSpan B n) (t : ℝ)
    (hc : HasDerivAt (fun s => (c s : L2VF_R3))
      (galerkinODE_vectorField B F ν n (c t) : L2VF_R3) t) :
    HasDerivAt (fun s => (1 / 2 : ℝ) * ‖(c s : L2VF_R3)‖ ^ 2)
      (- ν * viscousFormSq_R3 1 (c t : L2VF_R3)) t := by
  -- The exact dissipation value: `⟪c t, G_n (c t)⟫ = -ν·viscousFormSq_R3 1 (c t)`.
  have hinnerval : inner (𝕜 := ℝ) (c t : L2VF_R3) (galerkinODE_vectorField B F ν n (c t) : L2VF_R3)
      = - ν * viscousFormSq_R3 1 (c t : L2VF_R3) := by
    rw [real_inner_comm]
    have hspec := galerkinODE_vectorField_spec B F ν n (c t) (c t)
    rw [hspec, R3NSForms.b_self_zero F (galerkinSpanToSigma B n (c t)), sub_zero,
      stokesTestPairing_R3_diag]
  -- Differentiate `s ↦ ⟪c s, c s⟫`.
  have hinner :
      HasDerivAt (fun s => inner (𝕜 := ℝ) (c s : L2VF_R3) (c s : L2VF_R3))
        (inner (𝕜 := ℝ) (c t : L2VF_R3)
            (galerkinODE_vectorField B F ν n (c t) : L2VF_R3)
          + inner (𝕜 := ℝ) (galerkinODE_vectorField B F ν n (c t) : L2VF_R3)
              (c t : L2VF_R3)) t :=
    hc.inner ℝ hc
  -- Rewrite `½‖c s‖²` as `½⟪c s, c s⟫`.
  have hfun : (fun s => (1 / 2 : ℝ) * ‖(c s : L2VF_R3)‖ ^ 2)
      = fun s => (1 / 2 : ℝ) * inner (𝕜 := ℝ) (c s : L2VF_R3) (c s : L2VF_R3) := by
    funext s; rw [real_inner_self_eq_norm_sq]
  rw [hfun]
  have hval : (1 / 2 : ℝ) *
      (inner (𝕜 := ℝ) (c t : L2VF_R3) (galerkinODE_vectorField B F ν n (c t) : L2VF_R3)
        + inner (𝕜 := ℝ) (galerkinODE_vectorField B F ν n (c t) : L2VF_R3) (c t : L2VF_R3))
      = - ν * viscousFormSq_R3 1 (c t : L2VF_R3) := by
    have hcomm : inner (𝕜 := ℝ) (galerkinODE_vectorField B F ν n (c t) : L2VF_R3) (c t : L2VF_R3)
        = inner (𝕜 := ℝ) (c t : L2VF_R3) (galerkinODE_vectorField B F ν n (c t) : L2VF_R3) :=
      real_inner_comm _ _
    rw [hcomm, hinnerval]
    ring
  rw [← hval]
  exact hinner.const_mul (1 / 2 : ℝ)

/-! ## A3 — the forward a-priori energy bound -/

/-- **A3 (MUST-PROVE).** Any forward local solution on `[0, T]` stays in the ball
`‖c t‖ ≤ ‖c 0‖`.

Proof sketch: from A2, `t ↦ ½‖c t‖²` has nonpositive derivative `−ν·viscousFormSq_R3 1 (c t)`
on `Icc 0 T` (`viscousFormSq_R3_nonneg`, `mul_nonneg hν.le`), hence is `AntitoneOn (Icc 0 T)`
(`Convex`/`MeanValue` antitone-from-nonpositive-derivative); so `½‖c t‖² ≤ ½‖c 0‖²` for
`t ∈ Icc 0 T`, giving `‖c t‖ ≤ ‖c 0‖` after clearing the `½` and taking square roots
(`sq_le_sq'`/`abs_le_abs` + `norm_nonneg`). -/
theorem norm_le_of_forwardSolution
    (B : SchwartzGalerkinBasis) (F : R3NSForms (schemeOfBasis B)) (ν : ℝ) (n : ℕ) (hν : 0 < ν)
    (c : ℝ → galerkinSpan B n) {T : ℝ} (hT : 0 ≤ T)
    (hsol : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt (fun s => (c s : L2VF_R3))
      (galerkinODE_vectorField B F ν n (c t) : L2VF_R3) t) :
    ∀ t ∈ Icc (0 : ℝ) T, ‖(c t : L2VF_R3)‖ ≤ ‖(c 0 : L2VF_R3)‖ := by
  set E : ℝ → ℝ := fun s => (1 / 2 : ℝ) * ‖(c s : L2VF_R3)‖ ^ 2 with hE
  -- At every point of `Icc 0 T` the energy has the dissipative derivative (from A2 + the solution).
  have hderiv : ∀ s ∈ Icc (0 : ℝ) T,
      HasDerivAt E (- ν * viscousFormSq_R3 1 (c s : L2VF_R3)) s := fun s hs =>
    energy_hasDerivAt_of_localSolution B F ν n c s (hsol s hs)
  -- The energy is `AntitoneOn (Icc 0 T)`: continuous + differentiable with nonpositive derivative.
  have hAnti : AntitoneOn E (Icc (0 : ℝ) T) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 T) ?_ ?_ ?_
    · exact fun s hs => (hderiv s hs).continuousAt.continuousWithinAt
    · intro s hs
      have hs' : s ∈ Icc (0 : ℝ) T := interior_subset hs
      exact (hderiv s hs').differentiableAt.differentiableWithinAt
    · intro s hs
      have hs' : s ∈ Icc (0 : ℝ) T := interior_subset hs
      rw [(hderiv s hs').deriv]
      have : 0 ≤ ν * viscousFormSq_R3 1 (c s : L2VF_R3) :=
        mul_nonneg hν.le (viscousFormSq_R3_nonneg zero_le_one _)
      rw [neg_mul]; linarith
  -- From `AntitoneOn`, `E t ≤ E 0`, then clear `½` and take square roots.
  intro t ht
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_refl 0, hT⟩
  have hle : E t ≤ E 0 := hAnti h0 ht ht.1
  have hsq : ‖(c t : L2VF_R3)‖ ^ 2 ≤ ‖(c 0 : L2VF_R3)‖ ^ 2 := by
    simp only [hE] at hle; linarith
  have := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at this

/-! ## G1 — forward-global existence by tiling/continuation (the core)

The largest single proof. Pre-factored into helper statements: a uniform local-existence time
on the a-priori ball, a single-step extension, and splice-agreement of overlapping local
solutions.
-/

/-- **Helper (G1, uniform-`δ`).** From C1 (the field is `C¹` on `V_n`) and compactness of the
a-priori ball `closedBall (0 : V_n) R`, there is a single uniform local-existence time `δ > 0`
valid from every center in the ball: for each `x₀ ∈ closedBall 0 R` there is a local solution on
`(t₀ − δ, t₀ + δ)` starting at `x₀` at `t₀`, for every `t₀` (autonomy ⟹ time-uniform).

Proof sketch: apply `ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt`
(uniform `ε` over a ball around each point) at each `x₀`, cover the compact `closedBall 0 R` by
finitely many such balls (`isCompact_closedBall`), and take `δ := min` of the finitely many `ε`s.
The field's `ContDiffAt` at every point is `galerkinODE_vectorField_contDiff …|>.contDiffAt`. -/
theorem galerkinField_uniform_local_time
    (B : SchwartzGalerkinBasis) (F : R3NSForms (schemeOfBasis B)) (ν : ℝ) (n : ℕ) (R : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x₀ ∈ closedBall (0 : galerkinSpan B n) R, ∀ t₀ : ℝ,
      ∃ α : ℝ → galerkinSpan B n, α t₀ = x₀ ∧
        ∀ t ∈ Ioo (t₀ - δ) (t₀ + δ),
          HasDerivAt α (galerkinODE_vectorField B F ν n (α t)) t := by
  set g := galerkinODE_vectorField B F ν n with hg
  have hcd : ∀ x : galerkinSpan B n, ContDiffAt ℝ 1 g x := fun x =>
    (galerkinODE_vectorField_contDiff B F ν n).contDiffAt
  -- Step 1: uniform `δ` at `t₀ = 0` via compactness of the a-priori ball.
  -- For each center `y` get an `r,ε`-neighborhood with solutions for all starts in `closedBall y r`.
  have hloc : ∀ y : galerkinSpan B n, ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ),
      ∀ x ∈ closedBall y r, ∃ α : ℝ → galerkinSpan B n, α 0 = x ∧
        ∀ t ∈ Ioo (0 - ε) (0 + ε), HasDerivAt α (g (α t)) t := fun y =>
    (hcd y).exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt 0
  choose r hr ε hε Hsol using hloc
  -- The open balls `ball y (r y)` cover the compact a-priori ball.
  have hcover : closedBall (0 : galerkinSpan B n) R ⊆ ⋃ y, ball y (r y) := by
    intro x _
    exact mem_iUnion.mpr ⟨x, mem_ball_self (hr x)⟩
  obtain ⟨I, hI⟩ := (isCompact_closedBall (0 : galerkinSpan B n) R).elim_finite_subcover
    (fun y => ball y (r y)) (fun y => isOpen_ball) hcover
  -- δ := min of the finitely many ε's over the subcover (or 1 if the cover is empty).
  rcases I.eq_empty_or_nonempty with hIemp | hIne
  · -- Empty subcover ⟹ the ball is empty; `δ := 1` vacuously works (no `x₀` exists).
    refine ⟨1, one_pos, fun x₀ hx₀ t₀ => ?_⟩
    rw [hIemp] at hI
    simp only [Finset.notMem_empty, iUnion_of_empty, iUnion_empty,
      subset_empty_iff] at hI
    exact absurd (hI ▸ hx₀) (Set.notMem_empty x₀)
  · refine ⟨I.inf' hIne ε, ?_, fun x₀ hx₀ t₀ => ?_⟩
    · -- positivity of the finite min
      rw [Finset.lt_inf'_iff]
      exact fun y _ => hε y
    · set δ := I.inf' hIne ε with hδ
      -- `x₀` lies in some `ball y (r y)` with `y ∈ I`.
      have hx₀' : x₀ ∈ ⋃ y ∈ I, ball y (r y) := hI hx₀
      rw [mem_iUnion₂] at hx₀'
      obtain ⟨y, hyI, hxy⟩ := hx₀'
      have hxmem : x₀ ∈ closedBall y (r y) := ball_subset_closedBall hxy
      obtain ⟨α, hα0, hαsol⟩ := Hsol y x₀ hxmem
      -- Translate the `t₀ = 0` solution to start at `t₀`.
      refine ⟨fun t => α (t - t₀), by simp only [sub_self]; exact hα0, fun t ht => ?_⟩
      have hδε : δ ≤ ε y := Finset.inf'_le _ hyI
      have htmem : t - t₀ ∈ Ioo (0 - ε y) (0 + ε y) := by
        rw [mem_Ioo] at ht ⊢
        refine ⟨by rw [zero_sub]; linarith [ht.1], by rw [zero_add]; linarith [ht.2]⟩
      have hd := hαsol (t - t₀) htmem
      -- Chain rule: `(fun t => α (t - t₀))' = α'(t - t₀)`.
      have hsub : HasDerivAt (fun t : ℝ => t - t₀) 1 t := (hasDerivAt_id t).sub_const t₀
      have hcomp := hd.scomp t hsub
      simp only [one_smul, Function.comp_def] at hcomp
      exact hcomp

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
/-- **Helper (G1, splice-agreement).** Two local solutions of the autonomous field on overlapping
closed intervals that agree at one common point agree on the whole overlap.

Proof sketch: local Lipschitz of `G_n` on the relevant ball (from C1 /
`ContDiff.lipschitzOnWith`) feeds `ODE_solution_unique_of_mem_Icc`, giving uniqueness on the
overlap, so the two pieces coincide there. -/
theorem galerkinField_solution_agree
    (B : SchwartzGalerkinBasis) (F : R3NSForms (schemeOfBasis B)) (ν : ℝ) (n : ℕ)
    (α β : ℝ → galerkinSpan B n) {a b t₀ : ℝ} (hab : a ≤ b) (ht₀ : t₀ ∈ Icc a b)
    (hαβ : α t₀ = β t₀)
    (hα : ∀ t ∈ Icc a b, HasDerivAt α (galerkinODE_vectorField B F ν n (α t)) t)
    (hβ : ∀ t ∈ Icc a b, HasDerivAt β (galerkinODE_vectorField B F ν n (β t)) t) :
    ∀ t ∈ Icc a b, α t = β t := by
  set g := galerkinODE_vectorField B F ν n with hg
  -- Continuity of both trajectories on the compact `Icc a b`.
  have hαc : ContinuousOn α (Icc a b) := fun t ht => (hα t ht).continuousAt.continuousWithinAt
  have hβc : ContinuousOn β (Icc a b) := fun t ht => (hβ t ht).continuousAt.continuousWithinAt
  -- A radius `M` confining both trajectories on `Icc a b`.
  obtain ⟨Mα, hMα⟩ := (((isCompact_Icc).image_of_continuousOn hαc).image continuous_norm).bddAbove
  obtain ⟨Mβ, hMβ⟩ := (((isCompact_Icc).image_of_continuousOn hβc).image continuous_norm).bddAbove
  set M : ℝ := max (max Mα Mβ) 0 with hMdef
  have hM0 : 0 ≤ M := le_max_right _ _
  have hαM : ∀ t ∈ Icc a b, α t ∈ closedBall (0 : galerkinSpan B n) M := by
    intro t ht
    rw [mem_closedBall, dist_zero_right]
    refine le_trans (hMα ⟨α t, ⟨t, ht, rfl⟩, rfl⟩) ?_
    exact le_trans (le_max_left Mα Mβ) (le_max_left _ _)
  have hβM : ∀ t ∈ Icc a b, β t ∈ closedBall (0 : galerkinSpan B n) M := by
    intro t ht
    rw [mem_closedBall, dist_zero_right]
    refine le_trans (hMβ ⟨β t, ⟨t, ht, rfl⟩, rfl⟩) ?_
    exact le_trans (le_max_right Mα Mβ) (le_max_left _ _)
  -- `g` is Lipschitz on the convex compact ball `closedBall 0 M` (`C¹` ⟹ Lipschitz on compacts).
  have hgcd : ContDiff ℝ 1 g := galerkinODE_vectorField_contDiff B F ν n
  obtain ⟨K, hlip⟩ := (hgcd.contDiffOn (s := closedBall (0 : galerkinSpan B n) M)).exists_lipschitzOnWith
    one_ne_zero (convex_closedBall _ _) (isCompact_closedBall _ _)
  -- Apply two-sided uniqueness, splitting `Icc a b = Icc a t₀ ∪ Icc t₀ b`.
  -- Backward half: `Icc a t₀` with initial time `t₀` (right endpoint).
  have hbwd : EqOn α β (Icc a t₀) := by
    have hsub : Icc a t₀ ⊆ Icc a b := Icc_subset_Icc_right ht₀.2
    refine ODE_solution_unique_of_mem_Icc_left (a := a) (b := t₀) (K := K)
      (s := fun _ => closedBall (0 : galerkinSpan B n) M)
      (fun t' _ => hlip) (hαc.mono hsub)
      (fun t' ht' => (hα t' (hsub ⟨ht'.1.le, ht'.2⟩)).hasDerivWithinAt)
      (fun t' ht' => hαM t' (hsub ⟨ht'.1.le, ht'.2⟩))
      (hβc.mono hsub)
      (fun t' ht' => (hβ t' (hsub ⟨ht'.1.le, ht'.2⟩)).hasDerivWithinAt)
      (fun t' ht' => hβM t' (hsub ⟨ht'.1.le, ht'.2⟩)) hαβ
  -- Forward half: `Icc t₀ b` with initial time `t₀` (left endpoint).
  have hfwd : EqOn α β (Icc t₀ b) := by
    have hsub : Icc t₀ b ⊆ Icc a b := Icc_subset_Icc_left ht₀.1
    refine ODE_solution_unique_of_mem_Icc_right (a := t₀) (b := b) (K := K)
      (s := fun _ => closedBall (0 : galerkinSpan B n) M)
      (fun t' _ => hlip) (hαc.mono hsub)
      (fun t' ht' => (hα t' (hsub ⟨ht'.1, ht'.2.le⟩)).hasDerivWithinAt)
      (fun t' ht' => hαM t' (hsub ⟨ht'.1, ht'.2.le⟩))
      (hβc.mono hsub)
      (fun t' ht' => (hβ t' (hsub ⟨ht'.1, ht'.2.le⟩)).hasDerivWithinAt)
      (fun t' ht' => hβM t' (hsub ⟨ht'.1, ht'.2.le⟩)) hαβ
  -- Combine.
  intro t ht
  rcases le_total t t₀ with hle | hle
  · exact hbwd ⟨ht.1, hle⟩
  · exact hfwd ⟨hle, ht.2⟩

/-! ### G1 — forward-global existence by tiling (helpers, then the core) -/

/-- Transport an intrinsic `HasDerivAt` in `V_n` to the ambient `L2VF_R3` curve. -/
private theorem solve_hasDerivAt_ambient
    (B : SchwartzGalerkinBasis) (F : R3NSForms (schemeOfBasis B)) (ν : ℝ) (n : ℕ)
    (c : ℝ → galerkinSpan B n) (t : ℝ)
    (h : HasDerivAt c (galerkinODE_vectorField B F ν n (c t)) t) :
    HasDerivAt (fun s => (c s : L2VF_R3))
      (galerkinODE_vectorField B F ν n (c t) : L2VF_R3) t := by
  have hl : HasFDerivAt (Submodule.subtypeL (galerkinSpan B n))
      (Submodule.subtypeL (galerkinSpan B n)) (c t) :=
    (Submodule.subtypeL (galerkinSpan B n)).hasFDerivAt
  have hcomp := hl.comp_hasDerivAt t h
  simpa [Function.comp_def, Submodule.subtypeL_apply] using hcomp

set_option maxHeartbeats 1600000 in
/-- Tiling induction: a forward solution exists on `[0, k·δ]` for every `k`, started at `x₀`,
provided `δ` is the uniform local time on `closedBall 0 R` and `R = ‖x₀‖`. -/
private theorem solve_exists_on_step
    (B : SchwartzGalerkinBasis) (F : R3NSForms (schemeOfBasis B)) (ν : ℝ) (hν : 0 < ν) (n : ℕ)
    (x₀ : galerkinSpan B n) {δ : ℝ} (hδ : 0 < δ)
    (huniform : ∀ y ∈ closedBall (0 : galerkinSpan B n) ‖x₀‖, ∀ t₀ : ℝ,
      ∃ α : ℝ → galerkinSpan B n, α t₀ = y ∧
        ∀ t ∈ Ioo (t₀ - δ) (t₀ + δ),
          HasDerivAt α (galerkinODE_vectorField B F ν n (α t)) t) :
    ∀ k : ℕ, ∃ c : ℝ → galerkinSpan B n, c 0 = x₀ ∧
      ∀ t ∈ Icc (0 : ℝ) (k * (δ / 2)),
        HasDerivAt c (galerkinODE_vectorField B F ν n (c t)) t := by
  set g := galerkinODE_vectorField B F ν n with hg
  set R := ‖x₀‖ with hR
  have hs2 : (0 : ℝ) < δ / 2 := by positivity
  intro k
  induction k with
  | zero =>
    -- Base: a genuine local solution from `x₀` at time `0` (constant won't have deriv `g x₀`).
    have hx₀mem : x₀ ∈ closedBall (0 : galerkinSpan B n) R := by
      rw [mem_closedBall, dist_zero_right, hR]
    obtain ⟨α, hα0, hαsol⟩ := huniform x₀ hx₀mem 0
    refine ⟨α, hα0, fun t ht => ?_⟩
    simp only [Nat.cast_zero, zero_mul] at ht
    have hts : t = 0 := le_antisymm ht.2 ht.1
    subst hts
    exact hαsol 0 ⟨by linarith, by linarith⟩
  | succ k ih =>
    obtain ⟨c, hc0, hcsol⟩ := ih
    -- The endpoint `c (k·δ/2)` lies in the a-priori ball (energy bound A3).
    have hkδ0 : (0 : ℝ) ≤ k * (δ / 2) := by positivity
    have hcsol_amb : ∀ t ∈ Icc (0 : ℝ) (k * (δ / 2)),
        HasDerivAt (fun s => (c s : L2VF_R3)) (g (c t) : L2VF_R3) t :=
      fun t ht => solve_hasDerivAt_ambient B F ν n c t (hcsol t ht)
    have hbound := norm_le_of_forwardSolution B F ν n hν c hkδ0 hcsol_amb
      (k * (δ / 2)) ⟨hkδ0, le_rfl⟩
    have hc0amb : (c 0 : L2VF_R3) = (x₀ : L2VF_R3) := by rw [hc0]
    have hckmem : c (k * (δ / 2)) ∈ closedBall (0 : galerkinSpan B n) R := by
      rw [mem_closedBall, dist_zero_right, hR]
      have h1 : ‖(c (k * (δ / 2)) : L2VF_R3)‖ ≤ ‖(x₀ : L2VF_R3)‖ := by rw [← hc0amb]; exact hbound
      rw [Submodule.norm_coe, Submodule.norm_coe] at h1
      exact h1
    -- Local solution from that endpoint at time `k·δ/2` (width `δ`, covers `[k·δ/2, (k+1)·δ/2]`).
    obtain ⟨α, hα0, hαsol⟩ := huniform (c (k * (δ / 2))) hckmem (k * (δ / 2))
    -- Glue: `c` on `[0, k·δ/2]`, `α` on `[k·δ/2, (k+1)·δ/2]`.
    refine ⟨fun t => if t ≤ k * (δ / 2) then c t else α t, ?_, fun t ht => ?_⟩
    · simp only [show (0 : ℝ) ≤ k * (δ / 2) from hkδ0, if_pos]; exact hc0
    · -- locate `t`
      rcases lt_trichotomy t (k * (δ / 2)) with hlt | heq | hgt
      · -- `t < k·δ/2`: use `c`.
        have hmem : t ∈ Icc (0 : ℝ) (k * (δ / 2)) := ⟨ht.1, le_of_lt hlt⟩
        have hev : (fun t => if t ≤ k * (δ / 2) then c t else α t) =ᶠ[nhds t] c := by
          filter_upwards [Iio_mem_nhds hlt] with s hs
          simp only [if_pos (le_of_lt (mem_Iio.mp hs))]
        rw [hev.hasDerivAt_iff]
        simp only [if_pos (le_of_lt hlt)]
        exact hcsol t hmem
      · -- `t = k·δ/2`: glue point. Work at the center `m := k·δ/2`.
        set m : ℝ := k * (δ / 2) with hm
        rw [heq]
        have hval : α m = c m := hα0
        have hpw_t : (if m ≤ m then c m else α m) = c m := by rw [if_pos le_rfl]
        have hleft : HasDerivWithinAt (fun s => if s ≤ m then c s else α s)
            (g (c m)) (Iic m) m := by
          refine (hcsol m ⟨by rw [← heq]; exact ht.1, le_rfl⟩).hasDerivWithinAt.congr_of_mem
            (fun s hs => ?_) (mem_Iic.mpr le_rfl)
          simp only [if_pos (mem_Iic.mp hs)]
        have htmem : m ∈ Ioo (m - δ) (m + δ) := ⟨by linarith, by linarith⟩
        have hαt : HasDerivAt α (g (α m)) m := hαsol m htmem
        have hright : HasDerivWithinAt (fun s => if s ≤ m then c s else α s)
            (g (c m)) (Ici m) m := by
          have hαdw : HasDerivWithinAt α (g (c m)) (Ici m) m := by
            rw [← hval]; exact hαt.hasDerivWithinAt
          refine hαdw.congr_of_mem (fun s hs => ?_) (mem_Ici.mpr le_rfl)
          rcases eq_or_lt_of_le (mem_Ici.mp hs) with hse | hslt
          · simp only [← hse, if_pos le_rfl]; exact hval.symm
          · simp only [if_neg (not_le.mpr hslt)]
        have hunion := hleft.union hright
        rw [Iic_union_Ici, hasDerivWithinAt_univ] at hunion
        show HasDerivAt (fun s => if s ≤ m then c s else α s)
          (g (if m ≤ m then c m else α m)) m
        rw [hpw_t]
        exact hunion
      · -- `t > k·δ/2`: use `α` (within `Ioo (k·δ/2 - δ) (k·δ/2 + δ)` since `t ≤ (k+1)·δ/2`).
        have hub : t ≤ (k + 1 : ℝ) * (δ / 2) := by
          have h2 := ht.2; push_cast at h2 ⊢; linarith
        have htmem : t ∈ Ioo (k * (δ / 2) - δ) (k * (δ / 2) + δ) := by
          refine ⟨by linarith, ?_⟩
          -- `t ≤ (k+1)·δ/2 = k·δ/2 + δ/2 < k·δ/2 + δ`.
          have : (k + 1 : ℝ) * (δ / 2) = k * (δ / 2) + δ / 2 := by ring
          have hδ2 : δ / 2 < δ := by linarith
          linarith [hub, this]
        have hev : (fun s => if s ≤ k * (δ / 2) then c s else α s) =ᶠ[nhds t] α := by
          filter_upwards [Ioi_mem_nhds hgt] with s hs
          simp only [if_neg (not_le.mpr (mem_Ioi.mp hs))]
        rw [hev.hasDerivAt_iff]
        show HasDerivAt α (g (if t ≤ k * (δ / 2) then c t else α t)) t
        rw [if_neg (not_le.mpr hgt)]
        exact hαsol t htmem

set_option maxHeartbeats 800000 in
/-- **G1 (THE core, MUST-PROVE).** Forward-global existence: there is `c : ℝ → V_n` with
`c 0 = galerkinP B n u₀ (∈ V_n)` and `∀ t ≥ 0, HasDerivAt (↑∘c) (G_n (c t)) t`. Built by tiling
`[0,∞)` with the uniform local-existence time on the fixed a-priori ball (`solve_exists_on_step`),
gluing grid curves by uniqueness (`galerkinField_solution_agree`). -/
theorem forwardGlobalSolution_exists
    (B : SchwartzGalerkinBasis) (F : R3NSForms (schemeOfBasis B)) (ν : ℝ) (hν : 0 < ν)
    (u₀ : L2Sigma_R3) (n : ℕ) :
    ∃ c : ℝ → galerkinSpan B n,
      (c 0 : L2VF_R3) = galerkinP B n (u₀ : L2VF_R3) ∧
      ∀ t, 0 ≤ t → HasDerivAt (fun s => (c s : L2VF_R3))
        (galerkinODE_vectorField B F ν n (c t) : L2VF_R3) t := by
  classical
  set g := galerkinODE_vectorField B F ν n with hg
  -- The initial value, intrinsically in `V_n`.
  have hx₀mem : galerkinP B n (u₀ : L2VF_R3) ∈ galerkinSpan B n := galerkinP_mem_span B n _
  set x₀ : galerkinSpan B n := ⟨galerkinP B n (u₀ : L2VF_R3), hx₀mem⟩ with hx₀
  set R := ‖x₀‖ with hR
  -- Uniform local time on the a-priori ball.
  obtain ⟨δ, hδ, huniform⟩ := galerkinField_uniform_local_time B F ν n R
  -- Per-step existence (advance step `δ/2`, solution width `δ`).
  have hstep := solve_exists_on_step B F ν hν n x₀ hδ huniform
  set s2 : ℝ := δ / 2 with hs2def
  have hs2 : (0 : ℝ) < s2 := by rw [hs2def]; positivity
  -- For each `k`, choose a curve on `[0, k·δ/2]`.
  choose ck hck0 hcksol using hstep
  -- Define `c t` using a large enough step index.
  set N : ℝ → ℕ := fun t => ⌊t / s2⌋₊ + 1 with hN
  set c : ℝ → galerkinSpan B n := fun t => ck (N t) t with hc
  -- Strict bound: `t < N t · δ/2` for all `t`.
  have hltN : ∀ t : ℝ, t < N t * s2 := by
    intro t
    rcases lt_or_ge t 0 with ht0 | ht0
    · -- `t < 0 < N t · δ/2` since `N t ≥ 1`.
      have hN1 : (1 : ℝ) ≤ (N t : ℝ) := by
        rw [hN]; push_cast; have := Nat.zero_le (⌊t / s2⌋₊); push_cast; linarith
      have hpos : (0 : ℝ) < N t * s2 := mul_pos (by linarith) hs2
      linarith
    · have hlt : t / s2 < (⌊t / s2⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one (t / s2)
      have heq2 : t = (t / s2) * s2 := by field_simp
      have hmul := mul_lt_mul_of_pos_right hlt hs2
      rw [← heq2] at hmul
      rw [hN]; push_cast
      exact hmul
  have hmemN : ∀ t, 0 ≤ t → t ∈ Icc (0 : ℝ) (N t * s2) := fun t ht => ⟨ht, le_of_lt (hltN t)⟩
  -- Agreement: any two grid curves agree on the common `Icc 0 (min …)` (they share value at 0).
  have hagree : ∀ j k : ℕ, ∀ t ∈ Icc (0 : ℝ) (min (j * s2) (k * s2)), ck j t = ck k t := by
    intro j k t ht
    have hjk : (0 : ℝ) ≤ min (j * s2) (k * s2) := le_min (by positivity) (by positivity)
    refine galerkinField_solution_agree B F ν n (ck j) (ck k) hjk ⟨le_refl 0, hjk⟩
      (by rw [hck0 j, hck0 k]) ?_ ?_ t ht
    · intro u hu
      exact hcksol j u ⟨hu.1, le_trans hu.2 (min_le_left _ _)⟩
    · intro u hu
      exact hcksol k u ⟨hu.1, le_trans hu.2 (min_le_right _ _)⟩
  refine ⟨c, ?_, ?_⟩
  · -- `c 0 = x₀`.
    show (ck (N 0) 0 : L2VF_R3) = galerkinP B n (u₀ : L2VF_R3)
    rw [hck0 (N 0)]
  · intro t ht
    -- `ck (N t)` solves at `t`; transport to the ambient curve.
    have hsol := hcksol (N t) t (hmemN t ht)
    have hsol_amb := solve_hasDerivAt_ambient B F ν n (ck (N t)) t hsol
    -- `N u = 1` for every `u < δ/2` (in particular all `u ≤ 0`).
    have hN1 : ∀ u : ℝ, u < s2 → N u = 1 := by
      intro u hu
      show ⌊u / s2⌋₊ + 1 = 1
      have hfloor : ⌊u / s2⌋₊ = 0 := by
        apply Nat.floor_eq_zero.mpr
        rw [div_lt_one hs2]; exact hu
      rw [hfloor]
    -- `(fun s => (c s : L2VF)) =ᶠ[nhds t] (fun u => (ck (N t) u : L2VF))`.
    have hev : (fun s => (c s : L2VF_R3)) =ᶠ[nhds t]
        (fun u => (ck (N t) u : L2VF_R3)) := by
      rcases eq_or_lt_of_le ht with ht0 | ht0
      · -- `t = 0`: on `Iio (δ/2)`, `N u = 1 = N 0`.
        rw [← ht0]
        have hVnhds : Iio s2 ∈ nhds (0 : ℝ) := Iio_mem_nhds hs2
        filter_upwards [hVnhds] with u hu
        show (ck (N u) u : L2VF_R3) = (ck (N 0) u : L2VF_R3)
        rw [hN1 u hu, hN1 0 hs2]
      · -- `t > 0`: on `Iio (N t · δ/2) ∩ Ioi 0`, agreement applies (`u > 0`).
        have hVnhds : Iio (N t * s2) ∩ Ioi 0 ∈ nhds t :=
          Filter.inter_mem (Iio_mem_nhds (hltN t)) (Ioi_mem_nhds ht0)
        filter_upwards [hVnhds] with u hu
        show (ck (N u) u : L2VF_R3) = (ck (N t) u : L2VF_R3)
        have humem : u ∈ Icc (0 : ℝ) (min (N u * s2) (N t * s2)) :=
          ⟨le_of_lt (mem_Ioi.mp hu.2), le_min (le_of_lt (hltN u)) (le_of_lt (mem_Iio.mp hu.1))⟩
        rw [hagree (N u) (N t) u humem]
    -- Conclude via the eventual equality; `c t = ck (N t) t` definitionally.
    have hgoal : HasDerivAt (fun s => (ck (N t) s : L2VF_R3))
        (galerkinODE_vectorField B F ν n (c t) : L2VF_R3) t := by
      have hct : (c t : galerkinSpan B n) = ck (N t) t := rfl
      rw [show (galerkinODE_vectorField B F ν n (c t) : L2VF_R3)
          = (galerkinODE_vectorField B F ν n (ck (N t) t) : L2VF_R3) from by rw [hct]]
      exact hsol_amb
    exact (hev.hasDerivAt_iff).mpr hgoal


/-! ## D — the deliverable (UNCONDITIONAL) -/

/-- **Deliverable (Pillar E, R-global, MUST-PROVE).** A forward-global solution of the autonomous
finite-dim Galerkin ODE exists — discharging the last frontier behind `galerkin_ode_solution_R3`
over the concrete scheme `schemeOfBasis B`. **UNCONDITIONAL**: `FinDimGlobalODE` is now a
forward-time structure (`c_hasDeriv`/`ode` quantified `∀ t, 0 ≤ t →`), so the forward-global
solution G1 supplies it with no residual hypothesis.

Proof sketch: from `forwardGlobalSolution_exists` obtain `c` and its two properties; package the
four `FinDimGlobalODE` fields — `c := c`; `c_initial :=` G1's first conjunct;
`c_hasDeriv t ht :=` rewrite G1's explicit-derivative `HasDerivAt` through `HasDerivAt.deriv`
(`(hc t ht).hasDerivAt` form / `HasDerivAt.deriv`); `ode t ht :=` G1's second conjunct rewritten
through `HasDerivAt.deriv`. -/
theorem finDimGlobalODE_exists
    (B : SchwartzGalerkinBasis) (F : R3NSForms (schemeOfBasis B)) (ν : ℝ) (hν : 0 < ν)
    (u₀ : L2Sigma_R3) (n : ℕ) :
    Nonempty (FinDimGlobalODE B F ν u₀ n) := by
  obtain ⟨c, hc0, hd⟩ := forwardGlobalSolution_exists B F ν hν u₀ n
  refine ⟨{ c := c, c_initial := hc0, c_hasDeriv := ?_, ode := ?_ }⟩
  · intro t ht
    have hderiv : deriv (fun s => (c s : L2VF_R3)) t
        = (galerkinODE_vectorField B F ν n (c t) : L2VF_R3) := (hd t ht).deriv
    rw [hderiv]
    exact hd t ht
  · intro t ht
    exact (hd t ht).deriv

/-! ## D' — optional: unconditional Galerkin solution data over `schemeOfBasis B` -/

/-- **Optional (D', thin).** The UNCONDITIONAL Galerkin solution data over `schemeOfBasis B`,
combining the deliverable D with the existing `galerkinSolutionData_of_basis`
(`GalerkinODEExistence.lean`). Lands the headline "unconditional over `schemeOfBasis B`" payoff.

Proof sketch: feed `(finDimGlobalODE_exists B F ν hν u₀ n).some` into
`galerkinSolutionData_of_basis B F ν hν u₀ n`. -/
noncomputable def galerkinSolutionData_unconditional
    (B : SchwartzGalerkinBasis) (F : R3NSForms (schemeOfBasis B)) (ν : ℝ) (hν : 0 < ν)
    (u₀ : L2Sigma_R3) (n : ℕ) :
    GalerkinSolutionData_R3 (schemeOfBasis B) F ν u₀ n :=
  galerkinSolutionData_of_basis B F ν hν u₀ n (finDimGlobalODE_exists B F ν hν u₀ n).some

end LerayHopf
