import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-!
# Generic dissipative finite-dimensional ODE: forward-global existence (issue #112)

**Campaign:** `docs/scratch/galerkin-domain-plan.md` §3.1 (PR-A). This file promotes the
feasibility spike `LerayHopf/Scratch/GalerkinDomainSpike.lean` to a production module:
the abstract dissipative-`C¹`-field forward-tiling/gluing argument, proved ONCE over any
finite-dimensional real inner-product space `V` and any field `g : V → V`, rather than
twice (once per lane) as it currently sits duplicated in `LerayHopf/R3/GalerkinODESolve.lean`
and `LerayHopf/Torus/GalerkinODESolve.lean`. PR-B (issue #112 lane rewiring) will re-derive
each lane's `forwardGlobalSolution_exists` as a corollary of `forwardGlobalSolution_exists`
below, instantiated via `coe_hasDerivAt` for the ambient-submodule transport step.

Mathlib-only imports (pdelib-grade layer — flagged in `docs/pdelib-staging.md`); this file
imports no `LerayHopf` module and is consumed by nothing in `LerayHopf` yet (PR-A has no
consumers by design; wiring happens in PR-B).

The five imports mirror `LerayHopf/R3/GalerkinODESolve.lean`'s import list: the mathlib
lemmas consumed by the proof bodies below (`ContDiffAt.exists_forall_mem_closedBall_
exists_eq_forall_mem_Ioo_hasDerivAt`, `ODE_solution_unique_of_mem_Icc_{left,right}`,
finite-dimensional compactness of closed balls) live in exactly these files.

## Scaffold status

Every proof body below is `sorry`-scaffolded (PR-A, coder pass); the bodies are direct
ports of `LerayHopf/Scratch/GalerkinDomainSpike.lean`'s `AbstractODE` section (spike
compiled clean, see plan §2/§9) and are filled by `lean-prover` in the PR-A prover pass.
Statements are FROZEN by the architect (plan §3.1) and must not be altered.
-/

namespace LerayHopf.Galerkin

open Metric Set

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- Energy derivative along a solution of `c' = g c`: `d/dt ½‖c t‖² = ⟪c t, g (c t)⟫`. -/
theorem energy_hasDerivAt_of_solution (g : V → V) (c : ℝ → V) (t : ℝ)
    (hc : HasDerivAt c (g (c t)) t) :
    HasDerivAt (fun s => (1 / 2 : ℝ) * ‖c s‖ ^ 2) (inner (𝕜 := ℝ) (c t) (g (c t))) t := by
  sorry -- ALLOW_SORRY: PR-A scaffold, prover fills (issue #112)

/-- A-priori bound: any forward solution of a dissipative field stays in the initial ball. -/
theorem norm_le_of_forwardSolution_of_dissipative (g : V → V)
    (hdiss : ∀ v : V, inner (𝕜 := ℝ) v (g v) ≤ (0 : ℝ))
    (c : ℝ → V) {T : ℝ} (hT : 0 ≤ T)
    (hsol : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt c (g (c t)) t) :
    ∀ t ∈ Icc (0 : ℝ) T, ‖c t‖ ≤ ‖c 0‖ := by
  sorry -- ALLOW_SORRY: PR-A scaffold, prover fills (issue #112)

/-- Uniform local-existence time on a ball: a single `δ` works for every start point in
`closedBall 0 R` and every start time `t₀`. -/
theorem uniform_local_time (g : V → V) (hg : ContDiff ℝ 1 g) (R : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x₀ ∈ closedBall (0 : V) R, ∀ t₀ : ℝ,
      ∃ α : ℝ → V, α t₀ = x₀ ∧
        ∀ t ∈ Ioo (t₀ - δ) (t₀ + δ), HasDerivAt α (g (α t)) t := by
  sorry -- ALLOW_SORRY: PR-A scaffold, prover fills (issue #112)

set_option maxHeartbeats 1600000 in
/-- Tiling induction: a forward solution exists on `[0, k·δ/2]` for every `k`, given a
uniform local-existence time `δ` on the a-priori ball around `x₀`. -/
private theorem solve_exists_on_step (g : V → V)
    (hdiss : ∀ v : V, inner (𝕜 := ℝ) v (g v) ≤ (0 : ℝ))
    (x₀ : V) {δ : ℝ} (hδ : 0 < δ)
    (huniform : ∀ y ∈ closedBall (0 : V) ‖x₀‖, ∀ t₀ : ℝ,
      ∃ α : ℝ → V, α t₀ = y ∧
        ∀ t ∈ Ioo (t₀ - δ) (t₀ + δ), HasDerivAt α (g (α t)) t) :
    ∀ k : ℕ, ∃ c : ℝ → V, c 0 = x₀ ∧
      ∀ t ∈ Icc (0 : ℝ) (k * (δ / 2)), HasDerivAt c (g (c t)) t := by
  sorry -- ALLOW_SORRY: PR-A scaffold, prover fills (issue #112)

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
/-- Splice uniqueness: two local solutions agreeing at one point agree on the whole
overlap interval. -/
theorem solution_agree (g : V → V) (hg : ContDiff ℝ 1 g)
    (α β : ℝ → V) {a b t₀ : ℝ} (hab : a ≤ b) (ht₀ : t₀ ∈ Icc a b)
    (hαβ : α t₀ = β t₀)
    (hα : ∀ t ∈ Icc a b, HasDerivAt α (g (α t)) t)
    (hβ : ∀ t ∈ Icc a b, HasDerivAt β (g (β t)) t) :
    ∀ t ∈ Icc a b, α t = β t := by
  sorry -- ALLOW_SORRY: PR-A scaffold, prover fills (issue #112)

set_option maxHeartbeats 800000 in
/-- **Forward-global existence** for a dissipative `C¹` field on a finite-dimensional real
inner-product space, by tiling `[0,∞)` with the uniform local-existence time on the
a-priori ball and gluing by uniqueness. This is the abstract core that both lanes'
`forwardGlobalSolution_exists` will specialize to (PR-B). -/
theorem forwardGlobalSolution_exists (g : V → V) (hg : ContDiff ℝ 1 g)
    (hdiss : ∀ v : V, inner (𝕜 := ℝ) v (g v) ≤ (0 : ℝ)) (x₀ : V) :
    ∃ c : ℝ → V, c 0 = x₀ ∧ ∀ t, 0 ≤ t → HasDerivAt c (g (c t)) t := by
  sorry -- ALLOW_SORRY: PR-A scaffold, prover fills (issue #112)

/-- Generic ambient transport: an intrinsic `HasDerivAt` in a submodule lifts to a
`HasDerivAt` of the coerced ambient curve. This is the generic form of both lanes'
private `solve_hasDerivAt_ambient` transport steps. -/
theorem coe_hasDerivAt {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (W : Submodule ℝ H) (c : ℝ → W) (v : W) (t : ℝ) (h : HasDerivAt c v t) :
    HasDerivAt (fun s => (c s : H)) (v : H) t := by
  sorry -- ALLOW_SORRY: PR-A scaffold, prover fills (issue #112)

end LerayHopf.Galerkin
