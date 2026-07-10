import LerayHopf.R3.SobolevEmbedding
import LerayHopf.R3.ConvectionForm

namespace LerayHopf
open MeasureTheory

/-!
# H¹_σ density in L²_σ(ℝ³) (A4)

Split out of `SobolevEmbedding.lean` (issue #113 PR-1): `h1Sigma_dense_in_L2Sigma` is the only
declaration of that file's original scope that needs `ConvectionForm.lean`'s proved density
theorem `schwartzDivFree_dense_of_curlDense` (and, transitively via `CurlDensityCapstone.lean`,
`curlSchwartzDense_holds`). Living here keeps `SobolevEmbedding.lean` free of the
`ConvectionForm` import for its other (unrelated) consumers.

## Declarations

- **A4** `h1Sigma_dense_in_L2Sigma` — elements of `L2Sigma_R3` satisfying `memH1VF_R3`
  are dense in `L2Sigma_R3`.
  Proof plan: Schwartz ⊂ H¹ + `schwartzDivFree_dense_of_curlDense` + `curlSchwartzDense_holds`.

## Assumptions

None — this file introduces no `axiom`/`opaque`. PROVED sorry-free (depends only on
`propext`/`Classical.choice`/`Quot.sound`).
-/

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
