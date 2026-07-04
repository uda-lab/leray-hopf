import LerayHopf.R3.CurlDensity
import LerayHopf.R3.Regularity

namespace LerayHopf

open MeasureTheory FourierTransform

/-!
# LerayHopf.R3.CurlDensityH1 — H¹ curl approximation at Schwartz div-free targets

**Campaign:** discharge `galerkin_limit_passage_R3` (issue #4, last project axiom).

This file contains the new analytic kernel `curl_approx_H1`: every Schwartz divergence-free
field `w ∈ L2Sigma_R3` is approximated in the `L² + viscousFormSq` (H¹ graph) seminorm by a
curl of a Schwartz potential `ψ : Fin 3 → 𝓢(ℝ³, ℝ)`.

**Proof route (Fourier low-frequency cutoff, issue #93 §1b / PR-2):**
1. `ŵ` is transverse (`mem_sigma_iff_fourier_transverse`, `CurlDensity.lean:952`, proved).
2. Set `ψ̂_δ(ξ) := χ_δ(ξ)·(ξ × ŵ(ξ))/(2πi‖ξ‖²)` with smooth radial cutoff `χ_δ`
   (`0` near `0`, `1` on `‖ξ‖ ≥ δ`).
3. `𝓕(curl ψ_δ) = χ_δ·ŵ` (BAC-CAB + transversality), so L² and weighted-L² (H¹) errors
   are `∫_{‖ξ‖≤δ}(1+W)|ŵ|² → 0`.
4. Symbol is Schwartz (smooth cutoff kills the singularity); realized via
   `FourierTransform.fourierCLE` and the Hermitian-reality machinery in `CurlDensity.lean`.

**Toolkit anchors (all verified in spike S7 of issue #93):**
- `FourierTransform.fourierCLE` — Fourier isomorphism on `SchwartzMap`
- `mem_sigma_iff_fourier_transverse` — `CurlDensity.lean:952`
- `curlSchwartzL2` — `SchwartzDivFreeBasis.lean:203`
- `viscousFormSq_R3` — `Regularity.lean:140`
-/

/-! ## Main theorem (spike S6 verbatim, production name `curl_approx_H1`) -/

/-- Every Schwartz divergence-free field `w ∈ L2Sigma_R3` can be approximated in the H¹
graph seminorm (`L²` norm + `viscousFormSq_R3 1`) by a curl `curlSchwartzL2 ψ` of a
Schwartz potential `ψ : Fin 3 → SchwartzMap Domain3 ℝ`.

This is the analytic kernel needed to discharge `R3TestApproxH1` for the strengthened
concrete Galerkin basis (issue #4 PR-3). Proof: Fourier low-frequency cutoff construction
(see module doc); filled by lean-prover (issue #4 PR-2). -/
theorem curl_approx_H1 (w : L2Sigma_R3) (hw : IsSchwartzDivFree_R3 w)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ ψ : Fin 3 → SchwartzMap Domain3 ℝ,
      ‖curlSchwartzL2 ψ - (w : L2VF_R3)‖ < ε ∧
      viscousFormSq_R3 1 (curlSchwartzL2 ψ - (w : L2VF_R3)) < ε := by
  sorry -- ALLOW_SORRY: scaffold (issue #4 PR-2 — lean-prover fills via Fourier low-freq cutoff)

end LerayHopf
