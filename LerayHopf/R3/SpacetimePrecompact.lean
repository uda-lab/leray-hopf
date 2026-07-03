/-
# LerayHopf.R3.SpacetimePrecompact — Issue #46 PR-4 (File E)

**Goal:** The assembly layer of the Simon compactness route that discharges the axiom
`galerkin_spacetime_precompact_R3` (plan: `docs/scratch/issue46-spacetime-precompact-plan.md`,
§3 File E).  Given the generic step-curve `Lp` compactness (File A), the Galerkin curve
library (File B), the energy-class trilinear bound (File C), and the master `n`-uniform
integrated sampling-error modulus (File D, D3), this file assembles the LOCAL
Aubin–Lions–Simon spacetime precompactness statement — the exact proposition currently
held as the axiom `galerkin_spacetime_precompact_R3` in `ArzelaAscoliTime.lean`.

This file sits STRICTLY UPSTREAM of `ArzelaAscoliTime.lean`: it does NOT import it.  The
axiom→theorem conversion (E3) happens later in `ArzelaAscoliTime.lean` itself, by
`import`-ing this module and delegating to `galerkin_spacetime_precompact_of_goodSampling`;
this keeps the import graph acyclic.

- `restrictToBall_comp_curve_memLp` (E1): the ball-restricted Galerkin curve
  `t ↦ restrictToBall k (u t)` is `MemLp 2` on `[0, T]` (continuity via B1 +
  1-Lipschitz ball restriction on a compact interval).
- `galerkin_spacetime_precompact_of_goodSampling` (E2): the LOCAL Aubin–Lions–Simon
  precompactness conclusion.  Its statement is **binder-for-binder identical** to the
  residual `galerkin_spacetime_precompact_R3` (`ArzelaAscoliTime.lean`) — only the name
  differs; no hypothesis is dropped, no conclusion narrowed.

## Plan §3 File E mapping

- `restrictToBall_comp_curve_memLp`                : E1 — `MemLp 2` of the ball-restricted curve
- `galerkin_spacetime_precompact_of_goodSampling`  : E2 — assembled LOCAL precompactness (≡ axiom body)

Dependency edges (plan): A6, A4, A5 + D3 + E1 → E2 → E3 (in `ArzelaAscoliTime.lean`).

## Assumptions

No axioms are introduced by this file (`axiom` count: 0).  This is the PR-4 SCAFFOLD:
E1 and E2 carry their real intended statements with proof bodies deferred to `lean-prover`
(`sorry` count: 2, each marked `-- ALLOW_SORRY: PR-4 scaffold, proof by lean-prover`).  No
statement is weakened, renamed, or made vacuous; E2's statement is byte-identical to the
residual it will discharge.
-/

import LerayHopf.R3.GalerkinTimeModulus        -- D3 galerkin_sampling_error_bound; transitively AxiomaticClosure (GalerkinSolutionData_R3, R3GalerkinScheme, R3NSForms, L2Sigma_R3), FrechetKolmogorov/RellichBall (frechetKolmogorov_holds, localRellichInput_of_frechetKolmogorov)
import LerayHopf.R3.GalerkinCurveBounds        -- B1 galerkinCurve_continuousOn, B2 galerkin_norm_le_u0 (curve continuity + energy bound for E1/E2)
import LerayHopf.R3.SpatialCompactness         -- L2ballR3, restrictToBall, LocalRellichInput.ballCompact (mirrors ArzelaAscoliTime's source of the ball-restriction primitives)
import LerayHopf.Bochner.StepFunctionCompactness  -- A4 isCompact_stepCurve_toLp, A5 totallyBounded_of_uniform_approx', A6 exists_subseq_tendsto_eLpNorm_of_totallyBounded (step-curve compactness engine for E2)

namespace LerayHopf

open MeasureTheory Filter Topology

/-! ### E1 — `MemLp 2` of the ball-restricted Galerkin curve -/

/-- **E1.** The ball-restricted Galerkin solution curve `t ↦ restrictToBall k (u t)` is
`MemLp 2` on the compact interval `[0, T]` (with the restricted Lebesgue measure).

Route (plan §3 E1): `t ↦ (gs.u t : L2VF_R3)` is continuous on `Ici 0` (B1
`galerkinCurve_continuousOn`), and `restrictToBall k` is 1-Lipschitz, so the composition is
continuous on `[0, T]`; a continuous curve into a normed space is `MemLp 2` on a finite
interval. -/
theorem restrictToBall_comp_curve_memLp
    (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T) (u₀ : L2Sigma_R3) (n : ℕ)
    (gs : GalerkinSolutionData_R3 𝔊 F ν u₀ n) (k : ℕ) :
    MemLp (fun t => restrictToBall k ((gs.u t : L2VF_R3))) 2
      (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)) := by
  sorry -- ALLOW_SORRY: PR-4 scaffold, proof by lean-prover

/-! ### E2 — assembled LOCAL Aubin–Lions–Simon spacetime precompactness -/

/-- **E2.** LOCAL Aubin–Lions–Simon spacetime precompactness on ℝ³ (refine-capable form).

For every input subsequence `ψ` (strictly monotone) and every ball radius `k : ℕ`, there is
a further strictly-monotone `ρ` and a measurable limit curve `g_k : ℝ → L2ballR3 k` such
that the Bochner `L²`-in-time norm of `restrictToBall k ((galSeq (ψ (ρ n))).u t) - g_k t`
tends to `0`.

The statement is **binder-for-binder identical** to the axiom
`galerkin_spacetime_precompact_R3` in `ArzelaAscoliTime.lean` — only the name differs.  This
is the theorem that will discharge that axiom (E3).

Route (plan §3 E2): fix `ψ, k`; the family `t ↦ restrictToBall k ((galSeq (ψ n)).u t)` is
`MemLp` by E1; its `toLp` range is totally bounded (D3's `n`-uniform integrated sampling
modulus places each sample slice in the compact `LocalRellichInput.ballCompact`, A4 gives a
compact step-curve set, A5 transfers total-boundedness); A6 extracts the convergent
subsequence. -/
theorem galerkin_spacetime_precompact_of_goodSampling
    (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T) (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n)
    (ψ : ℕ → ℕ) (hψ : StrictMono ψ) (k : ℕ) :
    ∃ (ρ : ℕ → ℕ) (g_k : ℝ → L2ballR3 k), StrictMono ρ ∧
      AEStronglyMeasurable g_k (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)) ∧
      Filter.Tendsto
        (fun n => eLpNorm
          (fun t => restrictToBall k ((galSeq (ψ (ρ n))).u t : L2VF_R3) - g_k t)
          2 (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)))
        Filter.atTop (nhds 0) := by
  sorry -- ALLOW_SORRY: PR-4 scaffold, proof by lean-prover

end LerayHopf
