/-
# LerayHopf.R3.GalerkinTimeModulus — Issue #46 PR-3 (File D)

**Goal:** The time-modulus / good-sampling layer of the Simon compactness route that
discharges the axiom `galerkin_spacetime_precompact_R3`
(plan: `docs/scratch/issue46-spacetime-precompact-plan.md`, §3 File D).  Given the
energy-class trilinear bound (File C, C5) and the Galerkin curve library (File B), this
file turns per-cell dual-norm control into the single **`n`-uniform, integrated**
sampling-error bound consumed by the assembly step (File E).

- `exists_goodSample` (D1): on a compact interval a continuous nonneg integrand has a
  point at or below its average (min ≤ average), giving the per-cell sample.
- `galerkin_cell_error_bound` (D2): on a single mesh cell `[a, a+δ]`, the cell
  `L²`-error integral is bounded by an energy part plus a pairing part, each expressed
  through cell integrals of `V`-powers, with the good-sample factor `√(2δ⁻¹ν⁻¹E₀)`.
- `galerkin_sampling_error_bound` (D3, MASTER): a constant `C_mod ≥ 0` — a function of
  `‖u₀‖, ν, T, C_b` ONLY, standing OUTSIDE every quantifier over the Galerkin level `n`
  and the mesh count `m` — such that, on the uniform mesh of size `m`, there exist sample
  times with the total (summed-over-cells) `L²`-error bounded by `C_mod · √δ`.

The load-bearing structural claim of D3 is that `C_mod` is `n`- and `m`-independent: the
existential `∃ C_mod` sits OUTSIDE both `∀ n` and `∀ m`, and D3 is an INTEGRATED (summed)
modulus — no pointwise-in-time strong modulus is ever asserted (plan §1 guardrail-4).  The
`n`-uniform C5 constant `C_b` and its bound are taken as EXPLICIT hypotheses precisely so
that this `n`-uniformity is structurally evident.

## Plan §3 File D mapping

- `exists_goodSample`               : D1 — min ≤ average on a compact interval (generic)
- `galerkin_cell_error_bound`       : D2 — per-cell `L²`-error bound (energy + pairing parts)
- `galerkin_sampling_error_bound`   : D3 — MASTER `n`-uniform integrated sampling-error bound

Notation (plan §3): `V₁ v := viscousFormSq_R3 1 v`, `V_ν v := viscousFormSq_R3 ν v`,
`E₀ := (1/2)·‖(u₀ : L2VF_R3)‖²`.  These are inlined here (no global `def`).

Dependency edges (plan): D1 → D3; B2, B5, B7, B8, B9, C5 → D2 → D3.

## Assumptions

No axioms are introduced by this file (`axiom` count: 0).  This is the **PR-3 scaffold**:
D1, D2, D3 are stated with their real intended statements and carry `-- ALLOW_SORRY: PR-3
scaffold` placeholder bodies (3 marked `sorry`), to be discharged by `lean-prover` in the
PR-3 prover slice.  No statement is weakened, renamed, or made vacuous.
-/

import LerayHopf.R3.GalerkinTrilinearBound     -- C5 `bForm_galerkin_abs_le`, GalerkinSolutionData_R3, R3NSForms, viscousFormSq_R3
import LerayHopf.R3.GalerkinCurveBounds        -- B2/B5/B7/B8/B9 curve library (energy identity, pairing FTC, stokes CS)

namespace LerayHopf

open MeasureTheory

variable {𝔊 : R3GalerkinScheme} {F : R3NSForms 𝔊}

/-! ### D1 — good sample: min ≤ average on a compact interval (generic) -/

/-- **D1.** On a compact interval `[a, b]` (`a < b`), a continuous nonnegative integrand
has a point whose value is at or below its average: there is `τ ∈ [a, b]` with
`f τ ≤ (b − a)⁻¹ · ∫ₐᵇ f`.

Generic (no Galerkin context).  Route (plan §3 D1): min-value ≤ average, via
`IsCompact.exists_isMinOn` on `[a, b]` and monotonicity of the interval integral
(`intervalIntegral.integral_mono_on`) against the constant `f τ_min`. -/
theorem exists_goodSample {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Set.Icc a b))
    (hnn : ∀ σ ∈ Set.Icc a b, 0 ≤ f σ) :
    ∃ τ ∈ Set.Icc a b, f τ ≤ (b - a)⁻¹ * ∫ σ in a..b, f σ := by
  sorry -- ALLOW_SORRY: PR-3 scaffold, proof by lean-prover

/-! ### D2 — per-cell `L²`-error bound (energy part + pairing part) -/

/-- **D2.** Per-cell sampling error on the mesh cell `[a, a+δ]` (`0 < δ`, `0 ≤ a`) with a
good sample `τ ∈ [a, a+δ]` satisfying the good-sample Dirichlet bound
`V₁ (u τ) ≤ 2·δ⁻¹·ν⁻¹·E₀` (`E₀ = ½‖u₀‖²`).  The cell `L²`-error integral splits as

`‖u t − u τ‖² = (‖u t‖² − ‖u τ‖²) − 2⟪u t − u τ, u τ⟫`,

whose energy part is controlled by the integrated energy identity (B8) and whose pairing
part is controlled by the pairing FTC (B9) with the fixed test `w := u τ`, the stokes
Cauchy–Schwarz bound (B7), and the energy-class trilinear bound (C5).  Concretely:

`∫ t in a..(a+δ), ‖u t − u τ‖²
   ≤ 2·δ·(∫ σ in a..(a+δ), V_ν (u σ))
     + 2·δ·√(2·δ⁻¹·ν⁻¹·E₀) · ∫ σ in a..(a+δ),
         (ν·√(V₁ (u σ)) + C_b·‖u₀‖^{1/2}·(V₁ (u σ))^{3/4})`.

The C5 constant `C_b ≥ 0` and its bound `hC_b` are taken as EXPLICIT hypotheses (rather
than obtained internally from `bForm_galerkin_abs_le`) so that D2 — and the master bound
D3 built from it — stays visibly `n`-uniform: `C_b` cannot depend on the level `n`.

Consumes B2, B5, B7, B8, B9, C5. -/
theorem galerkin_cell_error_bound
    (ν : ℝ) (hν : 0 < ν) (u₀ : L2Sigma_R3) (n : ℕ)
    (gs : GalerkinSolutionData_R3 𝔊 F ν u₀ n)
    (C_b : ℝ) (hC_b0 : 0 ≤ C_b)
    (hC_b : ∀ (n : ℕ) (u v w : L2Sigma_R3),
        (u : L2VF_R3) = 𝔊.P n (u : L2VF_R3) →
        (v : L2VF_R3) = 𝔊.P n (v : L2VF_R3) →
        (w : L2VF_R3) = 𝔊.P n (w : L2VF_R3) →
        |F.b u v w|
          ≤ C_b * ‖(u : L2VF_R3)‖ ^ (1 / 2 : ℝ)
              * (viscousFormSq_R3 1 (u : L2VF_R3)) ^ (1 / 4 : ℝ)
              * Real.sqrt (viscousFormSq_R3 1 (v : L2VF_R3))
              * Real.sqrt (viscousFormSq_R3 1 (w : L2VF_R3)))
    (a δ : ℝ) (ha : 0 ≤ a) (hδ : 0 < δ)
    (τ : ℝ) (hτ : τ ∈ Set.Icc a (a + δ))
    (hτV : viscousFormSq_R3 1 (gs.u τ : L2VF_R3)
        ≤ 2 * δ⁻¹ * ν⁻¹ * ((1 / 2 : ℝ) * ‖(u₀ : L2VF_R3)‖ ^ 2)) :
    ∫ t in a..(a + δ), ‖(gs.u t : L2VF_R3) - (gs.u τ : L2VF_R3)‖ ^ 2
      ≤ 2 * δ * (∫ σ in a..(a + δ), viscousFormSq_R3 ν (gs.u σ : L2VF_R3))
        + 2 * δ * Real.sqrt (2 * δ⁻¹ * ν⁻¹ * ((1 / 2 : ℝ) * ‖(u₀ : L2VF_R3)‖ ^ 2))
            * ∫ σ in a..(a + δ),
                (ν * Real.sqrt (viscousFormSq_R3 1 (gs.u σ : L2VF_R3))
                  + C_b * ‖(u₀ : L2VF_R3)‖ ^ (1 / 2 : ℝ)
                      * (viscousFormSq_R3 1 (gs.u σ : L2VF_R3)) ^ (3 / 4 : ℝ)) := by
  sorry -- ALLOW_SORRY: PR-3 scaffold, proof by lean-prover

/-! ### D3 — MASTER `n`-uniform integrated sampling-error bound -/

/-- **D3 (MASTER; Codex-gated statement).** The `n`-uniform integrated sampling-error
bound.  There is a constant `C_mod ≥ 0` — a function of `‖u₀‖, ν, T, C_b` ONLY, standing
OUTSIDE every quantifier over the Galerkin level `n`, the Galerkin data `gs`, and the mesh
count `m` — such that for every level `n`, every Galerkin solution `gs` at that level, and
every mesh count `m > 0`, with `δ := T/m`, there exist sample times `τ : Fin m → ℝ` with

* `τ i ∈ [i·δ, (i+1)·δ]` (each sample lives in its cell),
* `V₁ (u (τ i)) ≤ 2·δ⁻¹·ν⁻¹·E₀` (the good-sample Dirichlet bound, `E₀ = ½‖u₀‖²`), and
* `∑ i, ∫ t in (i·δ)..((i+1)·δ), ‖u t − u (τ i)‖² ≤ C_mod · √δ`.

The conclusion is an INTEGRATED (summed-over-cells) modulus — no pointwise-in-time strong
modulus is asserted (plan §1 guardrail-4).  The critical structural claims are that the
existential `∃ C_mod` sits OUTSIDE `∀ n`, `∀ gs`, and `∀ m` (so `C_mod` is `n`- and
`m`-independent), and that the mesh is the FIXED uniform mesh of size `m`.  The C5 constant
`C_b ≥ 0` and its bound `hC_b` are taken as EXPLICIT hypotheses so that this `n`-uniformity
is structurally evident (`C_mod` is built from `C_b`, `‖u₀‖`, `ν`, `T` alone).

Route (plan §3 D3): D1 per cell (choice per `(n,i)` is classical), D2 per cell, sum with
`intervalIntegral.sum_integral_adjacent_intervals`, then time-Hölder
(`∫₀ᵀ √V₁ ≤ √T·√(∫V₁)`, `∫₀ᵀ V₁^{3/4} ≤ T^{1/4}·(∫V₁)^{3/4}`) with `reg_bound`. -/
theorem galerkin_sampling_error_bound
    (ν T : ℝ) (hν : 0 < ν) (hT : 0 < T) (u₀ : L2Sigma_R3)
    (C_b : ℝ) (hC_b0 : 0 ≤ C_b)
    (hC_b : ∀ (n : ℕ) (u v w : L2Sigma_R3),
        (u : L2VF_R3) = 𝔊.P n (u : L2VF_R3) →
        (v : L2VF_R3) = 𝔊.P n (v : L2VF_R3) →
        (w : L2VF_R3) = 𝔊.P n (w : L2VF_R3) →
        |F.b u v w|
          ≤ C_b * ‖(u : L2VF_R3)‖ ^ (1 / 2 : ℝ)
              * (viscousFormSq_R3 1 (u : L2VF_R3)) ^ (1 / 4 : ℝ)
              * Real.sqrt (viscousFormSq_R3 1 (v : L2VF_R3))
              * Real.sqrt (viscousFormSq_R3 1 (w : L2VF_R3))) :
    ∃ C_mod : ℝ, 0 ≤ C_mod ∧
      ∀ (n : ℕ) (gs : GalerkinSolutionData_R3 𝔊 F ν u₀ n) (m : ℕ), 0 < m →
        ∃ τ : Fin m → ℝ,
          (∀ i : Fin m,
            τ i ∈ Set.Icc ((i : ℕ) * (T / (m : ℝ))) (((i : ℕ) + 1) * (T / (m : ℝ)))) ∧
          (∀ i : Fin m,
            viscousFormSq_R3 1 (gs.u (τ i) : L2VF_R3)
              ≤ 2 * (T / (m : ℝ))⁻¹ * ν⁻¹ * ((1 / 2 : ℝ) * ‖(u₀ : L2VF_R3)‖ ^ 2)) ∧
          ∑ i : Fin m,
              ∫ t in ((i : ℕ) * (T / (m : ℝ)))..(((i : ℕ) + 1) * (T / (m : ℝ))),
                ‖(gs.u t : L2VF_R3) - (gs.u (τ i) : L2VF_R3)‖ ^ 2
            ≤ C_mod * Real.sqrt (T / (m : ℝ)) := by
  sorry -- ALLOW_SORRY: PR-3 scaffold, proof by lean-prover

end LerayHopf
