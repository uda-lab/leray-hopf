import LerayHopf.R3.GalerkinODEExistence   -- SchwartzGalerkinBasis, schemeOfBasis (+ AxiomaticClosure transitively → R3TestApproxH1)
import LerayHopf.R3.CurlDensityH1          -- curl_approx_H1 (H¹ Fourier low-cut kernel, issue #4 PR-2)

/-!
# Strengthened Galerkin basis: H¹ test approximation (scaffold, issue #4 PR-3)

This file contains the discharge statement for `R3TestApproxH1` at the *concrete*
`schemeOfBasis B` level: there exists a `SchwartzGalerkinBasis` whose induced scheme
satisfies the H¹(graph-norm) test-approximation property.

## Why this file exists (issue #93 §1b, route R2)

The abstract limit-passage theorem (`galerkin_limit_passage_R3` replacement) carries a
threaded hypothesis `htest : R3TestApproxH1 𝔊`.  The capstone chain
(`GalerkinODECapstone.lean` → `R3Axiomatic.lean`) must supply a concrete witness.

`nonempty_schwartzGalerkinBasis` (proved in `CurlDensityCapstone.lean`) gives an L²-dense
basis; the strengthened version here requires H¹(graph-norm) density as well, which is
discharged via the Fourier low-cut construction of `curl_approx_H1`.

## Proof sketch (for the lean-prover filling this sorry)

1. `curl_approx_H1` (`CurlDensityH1.lean`) gives: for any `w : L2Sigma_R3` with
   `IsSchwartzDivFree_R3 w` and `ε > 0`, there exists `ψ : Fin 3 → SchwartzMap ...`
   with `‖curlSchwartzL2 ψ - w‖ < ε` and `viscousFormSq_R3 1 (curlSchwartzL2 ψ - w) < ε`.
2. A `SchwartzGalerkinBasis` `B` that enumerates a countable H¹-graph-dense family inside
   `range curlSchwartzL2` (using separability of `L2VF_R3`) satisfies:
   for any `w` as above, the Galerkin projection `galerkinP B N w → w` in H¹ eventually.
3. Hence `R3TestApproxH1 (schemeOfBasis B)` holds for such `B`.

## Scaffold status

Both declarations carry `ALLOW_SORRY`: the proof body is left for `lean-prover`.
The statement `nonempty_schwartzGalerkinBasis_H1` is the Codex G3 gate target
(run by the orchestrator before the prover is dispatched).
-/

namespace LerayHopf

open MeasureTheory

/-- There exists a `SchwartzGalerkinBasis` whose induced Galerkin scheme satisfies
the H¹(graph-norm) test-approximation property `R3TestApproxH1`.

This is the strengthened counterpart of `nonempty_schwartzGalerkinBasis`
(`CurlDensityCapstone.lean`): the basis produced here witnesses not only L²-density of
its Galerkin span (the existing `SchwartzGalerkinBasis.dense_span` field) but also
H¹(graph-norm) approximation of every Schwartz divergence-free test by Galerkin tests of
the induced scheme.

The proof discharges `R3TestApproxH1` for the concrete `schemeOfBasis B` via
`curl_approx_H1` (Fourier low-cut kernel) and the separability of `L2VF_R3`.
The capstone chain (`GalerkinODECapstone.lean`, PR-6) will use the subtype witness
`⟨B, htest⟩` to thread `htest : R3TestApproxH1 (schemeOfBasis B)` into the assembly. -/
theorem nonempty_schwartzGalerkinBasis_H1 :
    Nonempty {B : SchwartzGalerkinBasis // R3TestApproxH1 (schemeOfBasis B)} := by
  sorry -- ALLOW_SORRY: scaffold, proved in issue #4 PR-3 — lean-prover fills (see proof sketch above)

end LerayHopf
