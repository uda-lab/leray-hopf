-- SCRATCH — feasibility spike for issue #4 (galerkin_limit_passage_R3 discharge).
-- NOT production code.  Every `sorry` here is a statement-elaboration probe, not a
-- proof obligation.  See docs/scratch/issue4-limit-passage-plan.md.
--
-- Probes (spike rule: every conjunct of the target, against the real interfaces):
--   S1  SecondCountableTopology / SeparableSpace for L2VF_R3 (instance synthesis)
--   S2  R3TestApproxH1 — the new H¹ test-approximation Prop (statement elaborates)
--   S3  the FULL replacement theorem statement (all 5 conjuncts, verbatim conclusion
--       of the axiom `galerkin_limit_passage_R3`, + the one new `htest` binder)
--   S4  W1 — Galerkin-test weak identity for the Aubin–Lions limit curve
--   S5  the good-representative existential (R3 port of torus
--       `exists_weak_representative`'s conclusion shape)
--   S6  H¹ curl-approximation at Schwartz div-free targets (the new analytic kernel)
--   S7  anchor resolution: fourierTransformCLE, mem_sigma_iff_fourier_transverse,
--       galerkinCurve_energy_identity, bForm_galerkin_abs_le, stokesTestPairing_abs_le
import LerayHopf.R3.AubinLionsLimitPassage
import LerayHopf.R3.GalerkinCurveBounds
import LerayHopf.R3.GalerkinTrilinearBound
import LerayHopf.R3.CurlDensity
import Mathlib.MeasureTheory.Measure.SeparableMeasure

open MeasureTheory Filter Topology

namespace LerayHopf
namespace Scratch4

/-! ### S1 — separability of the ambient L² space (needed for the countable
H¹-dense curl family in the strengthened basis). -/

-- `Lp.SecondCountableTopology [IsSeparable μ] [SeparableSpace E]`;
-- `IsSeparable volume` from `[CountablyGenerated Domain3] [SFinite volume]`.
example : SecondCountableTopology L2VF_R3 := inferInstance
example : TopologicalSpace.SeparableSpace L2VF_R3 := inferInstance
example : TopologicalSpace.SeparableSpace ℂ := inferInstance
example : SecondCountableTopology (Lp ℂ 2 (volume : Measure Domain3)) := by
  haveI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  exact Lp.SecondCountableTopology

/-! ### S2 — the new Prop: H¹(graph-norm) approximation of canonical Schwartz
div-free tests by Galerkin tests of the scheme.  This is the hypothesis that the
abstract limit-passage theorem will carry (threaded, NOT a structure field), and
that the strengthened concrete basis discharges. -/

/-- Every canonical Schwartz divergence-free test is approximated, in the
`L² + viscousFormSq` graph seminorm, by Galerkin test fields of the scheme `𝔊`. -/
def R3TestApproxH1 (𝔊 : R3GalerkinScheme) : Prop :=
  ∀ w : L2Sigma_R3, IsSchwartzDivFree_R3 w →
    ∀ ε : ℝ, 0 < ε →
      ∃ v : L2Sigma_R3, IsGalerkinTest_R3 𝔊 v ∧ IsSchwartzDivFree_R3 v ∧
        ‖(v : L2VF_R3) - (w : L2VF_R3)‖ < ε ∧
        viscousFormSq_R3 1 ((v : L2VF_R3) - (w : L2VF_R3)) < ε

/-! ### S3 — the replacement theorem, FULL statement.  Conclusion is byte-identical
to `galerkin_limit_passage_R3` (AxiomaticClosure.lean:574); the only delta is the
`htest` binder. -/

theorem galerkin_limit_passage_R3_spike
    (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T)
    (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n)
    (alPkg : AubinLionsPackage_R3 𝔊 F ν T u₀ galSeq)
    (htest : R3TestApproxH1 𝔊) :
    ∃ u : Time → L2Sigma_R3,
    (∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc 0 T)), u t = alPkg.u t) ∧
    WeakFormNS ν T (r3Evolution 𝔊 F) u ∧
    (∀ t, 0 ≤ t → t ≤ T →
      (1 / 2 : ℝ) * ‖(u t : L2VF_R3)‖ ^ 2 +
      ∫ s in (0 : ℝ)..t, viscousFormSq_R3 ν (u s : L2VF_R3) ≤
      (1 / 2 : ℝ) * ‖(u₀ : L2VF_R3)‖ ^ 2) ∧
    Filter.Tendsto
      (fun t => (u t : L2VF_R3))
      (nhdsWithin 0 (Set.Ici 0))
      (nhds (u₀ : L2VF_R3)) ∧
    ((∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc 0 T)), memH1VF_R3 (u t : L2VF_R3)) ∧
    IntervalIntegrable (fun s => viscousFormSq_R3 ν (u s : L2VF_R3))
      MeasureTheory.volume 0 T) := by
  sorry -- ALLOW_SORRY: scratch — statement-elaboration probe only (issue #4 spike)

/-! ### S4 — W1: the weak identity for the Aubin–Lions limit against a FIXED
Galerkin test (n→∞ only; no test approximation).  This is the torus
`torus_weakFormNS_of_strongConvergence` shape restricted to the Galerkin class. -/

theorem weakFormNS_galerkinTest_spike
    (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T)
    (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n)
    (alPkg : AubinLionsPackage_R3 𝔊 F ν T u₀ galSeq)
    (w : L2Sigma_R3) (hw : IsGalerkinTest_R3 𝔊 w)
    (ψ : Time → ℝ) (hψcs : HasCompactSupport ψ)
    (hψsupp : tsupport ψ ⊆ Set.Ioo 0 T) (hψC1 : ContDiff ℝ 1 ψ) :
    ∫ t in (0 : ℝ)..T,
      (-(inner (𝕜 := ℝ) ((alPkg.u t : L2VF_R3)) (w : L2VF_R3)) * deriv ψ t +
        ψ t * (ν * stokesTestPairing_R3 (alPkg.u t : L2VF_R3) (w : L2VF_R3) +
          F.b (alPkg.u t) (alPkg.u t) w)) = 0 := by
  sorry -- ALLOW_SORRY: scratch — statement-elaboration probe only (issue #4 spike)

/-! ### S5 — the good-representative existential (R3 port of the torus
`exists_weak_representative` conclusion; feeds conjuncts 1, 3, 4 and the a.e. link). -/

theorem exists_weak_representative_spike
    (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T)
    (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n)
    (alPkg : AubinLionsPackage_R3 𝔊 F ν T u₀ galSeq) :
    ∃ v : Time → L2Sigma_R3,
      (∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)), v t = alPkg.u t) ∧
      (∀ t, t ∈ Set.Icc (0 : ℝ) T → ∀ z : L2VF_R3,
        Tendsto (fun n => inner (𝕜 := ℝ) (((galSeq (alPkg.φ n)).u t : L2VF_R3)) z) atTop
          (𝓝 (inner (𝕜 := ℝ) ((v t : L2VF_R3)) z))) ∧
      (∀ t, t ∈ Set.Icc (0 : ℝ) T → ‖(v t : L2VF_R3)‖ ≤ ‖(u₀ : L2VF_R3)‖) ∧
      v 0 = u₀ ∧
      (∀ w : L2Sigma_R3, IsGalerkinTest_R3 𝔊 w → ∃ L : ℝ, 0 ≤ L ∧
        ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc (0 : ℝ) T,
          |inner (𝕜 := ℝ) ((v t : L2VF_R3)) (w : L2VF_R3)
            - inner (𝕜 := ℝ) ((v s : L2VF_R3)) (w : L2VF_R3)| ≤ L * |t - s|) := by
  sorry -- ALLOW_SORRY: scratch — statement-elaboration probe only (issue #4 spike)

/-! ### S6 — the new analytic kernel: H¹(graph-norm) curl approximation at
Schwartz divergence-free targets (Fourier low-frequency-cutoff construction). -/

theorem curl_approx_H1_spike (w : L2Sigma_R3) (hw : IsSchwartzDivFree_R3 w)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ ψ : Fin 3 → SchwartzMap Domain3 ℝ,
      ‖curlSchwartzL2 ψ - (w : L2VF_R3)‖ < ε ∧
      viscousFormSq_R3 1 (curlSchwartzL2 ψ - (w : L2VF_R3)) < ε := by
  sorry -- ALLOW_SORRY: scratch — statement-elaboration probe only (issue #4 spike)

/-! ### S7 — anchor resolution (these must elaborate against the real interfaces;
failures here mean the plan's reuse map is wrong). -/

-- Fourier CLE on Schwartz maps (for the cutoff-potential construction).
-- (`SchwartzMap.fourierTransformCLE` is deprecated in the pinned mathlib; the live
-- name is `FourierTransform.fourierCLE`.)
noncomputable example :
    SchwartzMap Domain3 ℂ ≃L[ℂ] SchwartzMap Domain3 ℂ :=
  FourierTransform.fourierCLE ℂ (SchwartzMap Domain3 ℂ)

-- Spectral div-free characterization (CurlDensity, proved).
example (u : L2VF_R3) := mem_sigma_iff_fourier_transverse u

-- B8 integrated energy identity (GalerkinCurveBounds, proved) — per-n combined
-- energy inequality feeds the ∀t energy conjunct.
example (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊) (ν : ℝ) (u₀ : L2Sigma_R3) (n : ℕ)
    (gs : GalerkinSolutionData_R3 𝔊 F ν u₀ n) :=
  galerkinCurve_energy_identity gs

-- C5 n-uniform trilinear energy bound (GalerkinTrilinearBound, proved) — the
-- W2 nonlinear test-slot continuity dominator.
example (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊) := bForm_galerkin_abs_le (𝔊 := 𝔊) (F := F)

-- C4 energy trilinear bound on arbitrary Schwartz-rep fields (third slot √visc factor).
example := convIntegralSchwartz_bound_energy

-- Viscous Cauchy–Schwarz in the H¹ seminorm (W2 viscous test-slot continuity).
example (u w : L2VF_R3) (hu : memH1VF_R3 u) (hw : memH1VF_R3 w) :=
  stokesTestPairing_abs_le u w hu hw

-- Plancherel–Laplacian viscous reformulation (W1 viscous n→∞ passage).
example (u w : L2VF_R3) (ψ : Fin 3 → SchwartzMap Domain3 ℝ)
    (hψ : ∀ j : Fin 3,
      L2VF_projComponent_R3 j w = (ψ j).toLp 2 (volume : Measure Domain3)) :=
  stokesTestPairing_R3_eq_sum_inner_negLap u w ψ hψ

-- Energy-class + integrated viscous lsc for the limit curve (conjunct 5, proved).
example (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T) (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n)
    (alPkg : AubinLionsPackage_R3 𝔊 F ν T u₀ galSeq) :=
  viscous_lsc_under_strongL2 𝔊 F ν hν T hT u₀ galSeq alPkg

end Scratch4
end LerayHopf
