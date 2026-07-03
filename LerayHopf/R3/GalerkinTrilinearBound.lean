/-
# LerayHopf.R3.GalerkinTrilinearBound — Issue #46 PR-2 (File C)

**Goal:** The trilinear / energy-class estimate library feeding the "good-sampling"
Simon compactness route that discharges the axiom `galerkin_spacetime_precompact_R3`
(plan: `docs/scratch/issue46-spacetime-precompact-plan.md`, §3 File C).  This file turns
the Schwartz representation of Galerkin states (B10, PR-1) into:

- the gradient-energy Plancherel identity (`V₁` as a sum of component ∂-`L²` masses),
- the componentwise `L⁶` and `L³` energy-class bounds,
- the `n`-uniform trilinear convection bound on `convIntegralSchwartz`, pushed to the
  abstract form `F.b` on Galerkin states,
- the continuity of the `b`-integrand along the Galerkin curve, and
- the pairing FTC (B9, deferred here from PR-1) that consumes it.

The load-bearing structural claim of C4/C5 is the **`n`-independence of the constant**:
in both, the existential `∃ C_b ≥ 0` sits OUTSIDE every quantifier over the fields and
the Galerkin level, so the constant cannot secretly depend on them.

## Plan §3 File C mapping

- `sum_gradSq_eq_viscousFormSq_of_schwartzRep`  : C1 — `∑_{i,a} ‖∂_a ψ_i‖²_{L²} = V₁ v`
- `eLpNorm_six_le_of_schwartzRep`               : C2 — `‖ψ_i‖_{L⁶} ≤ C₆·√(V₁ v)`
- `eLpNorm_three_le_interp_pub`                 : C3 — `‖f‖₃ ≤ ‖f‖₂^{1/2}·‖f‖₆^{1/2}` (public)
- `convIntegralSchwartz_bound_energy`           : C4 — energy-class trilinear bound (`∃ C_b` outside)
- `bForm_galerkin_abs_le`                       : C5 — same bound for `F.b` on level-`n` states
- `galerkin_bForm_curve_continuousOn`           : C6 — `b`-integrand continuous along the curve
- `galerkin_pairing_FTC`                        : B9 — pairing FTC (deferred from PR-1)

Dependency edges (plan): C1 → C2 → C4; C3 → C4 → C5 → C6; B10 → C5; B6 → C6;
B6, B7, C6 → B9.

**Fresh-build note (plan §2, risk R8):** C2/C3/C4 re-derive facts whose only existing
versions are `private` (`eLpNorm_three_le_interp`, `EnergyClassConvection.lean:510`;
`normSq_lineDeriv_toLp`, `SobolevEmbedding.lean:243`;
`eLpNorm_fderiv_le_sum_lineDeriv`, `EnergyClassConvection.lean:1174`).  `eLpNorm_three_le_interp_pub`
is a fresh PUBLIC copy of the private `eLpNorm_three_le_interp`; the original is neither
moved nor de-privatized.  No existing declaration is renamed, weakened, or edited.

**B9 landing note:** `galerkin_pairing_FTC` (plan task B9) was DEFERRED from PR-1
(`GalerkinCurveBounds.lean` header + "B9 — DEFERRED" section) because its FTC step needs
the interval-integrability of the `b`-integrand, i.e. C6, which lives here.  It lands in
this file keeping the name `galerkin_pairing_FTC` (plan §3 B9 note authorizes the move).

## Assumptions

No axioms are introduced by this file (`axiom` count: 0).  All proof bodies are
PR-2 scaffold placeholders (`sorry`, each `ALLOW_SORRY`-marked); the statement gate
precedes the proofs, which are discharged by `lean-prover` in a later slice of PR-2.
-/

import LerayHopf.R3.GalerkinCurveBounds     -- B6, B10, GalerkinSolutionData_R3, R3NSForms, viscousFormSq_R3, stokesTestPairing_R3
import LerayHopf.R3.TrilinearEstimate       -- convIntegralSchwartz, lineDerivOpCLM, convIntegralSchwartz_bound_H1 (C4 template)

namespace LerayHopf

open MeasureTheory Filter Topology LineDeriv
open scoped LineDeriv

variable {𝔊 : R3GalerkinScheme} {F : R3NSForms 𝔊} {ν : ℝ} {u₀ : L2Sigma_R3} {n : ℕ}

/-! ### C1 — gradient-energy Plancherel identity for Schwartz representatives -/

/-- **C1 (mathlib-gap risk R1).** The Dirichlet energy at `ν = 1` equals the total squared
`L²`-mass of the component partial derivatives of the Schwartz representatives:
`∑_i ∑_a ‖∂_a (ψ i)‖²_{L²} = viscousFormSq_R3 1 v` for any `v : L2VF_R3` whose components
are represented by `ψ` (as delivered by `galerkinState_schwartzRep`, B10).

Route (plan §3 C1): derivative-Fourier Plancherel `‖∂_a ψ_i‖²_{L²} = ∫ (2π)² ξ_a² ‖𝓕ψ_i‖²`
per component (template: private `normSq_lineDeriv_toLp`, `SobolevEmbedding.lean:243`;
rebuilt fresh), summed over `a` using `∑_a ξ_a² = ‖ξ‖²`, then over `i` to reassemble
`viscousFormSq_R3 1 v`.  The plan permits the `≤` form downstream; the equality is stated
here (prover may downgrade to `≤` if the equality fights — record it if so). -/
theorem sum_gradSq_eq_viscousFormSq_of_schwartzRep
    (v : L2VF_R3) (ψ : Fin 3 → SchwartzMap Domain3 ℝ)
    (hψ : ∀ j : Fin 3,
      L2VF_projComponent_R3 j v = (ψ j).toLp 2 (volume : Measure Domain3)) :
    ∑ i : Fin 3, ∑ a : Fin 3,
        ‖((lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
            (EuclideanSpace.single a (1 : ℝ) : Domain3) (ψ i)).toLp
          2 (volume : Measure Domain3))‖ ^ 2
      = viscousFormSq_R3 1 v := by
  sorry -- ALLOW_SORRY: PR-2 scaffold; statement gate precedes proof (this PR)

/-! ### C2 — componentwise `L⁶` energy-class bound -/

/-- **C2.** Componentwise `L⁶` bound in terms of the Dirichlet energy: there is an absolute
coefficient `C₆ ≥ 0` (independent of `v`, `ψ`, and the component `i`) with
`eLpNorm (ψ i) 6 ≤ ENNReal.ofReal (C₆ · √(V₁ v))` for every Schwartz representative `ψ`
of `v` and every component `i`.

The `∃ C₆` sits OUTSIDE the quantifiers over `v`, `ψ`, `i`, so the constant is genuinely
absolute (Gagliardo–Nirenberg–Sobolev has no field dependence).

Route (plan §3 C2): `gns_L6_schwartz` (public GNS on `Domain3`; complex- or real-valued
variant, whichever typechecks) bounding `‖ψ_i‖₆` by `eLpNorm (fderiv ψ_i) 2`, bridged to
`∑_a ‖∂_a ψ_i‖²` (template: private `eLpNorm_fderiv_le_sum_lineDeriv`,
`EnergyClassConvection.lean:1174`; rebuilt fresh), then C1 to reach `√(V₁ v)`. -/
theorem eLpNorm_six_le_of_schwartzRep :
    ∃ C₆ : ℝ, 0 ≤ C₆ ∧
      ∀ (v : L2VF_R3) (ψ : Fin 3 → SchwartzMap Domain3 ℝ),
        (∀ j : Fin 3,
          L2VF_projComponent_R3 j v = (ψ j).toLp 2 (volume : Measure Domain3)) →
        ∀ i : Fin 3,
          eLpNorm ((ψ i : Domain3 → ℝ)) 6 (volume : Measure Domain3)
            ≤ ENNReal.ofReal (C₆ * Real.sqrt (viscousFormSq_R3 1 v)) := by
  sorry -- ALLOW_SORRY: PR-2 scaffold; statement gate precedes proof (this PR)

/-! ### C3 — public `L²∩L⁶` interpolation at exponent 3 -/

/-- **C3.** Quantitative `L²∩L⁶` interpolation at exponent `3`:
`eLpNorm f 3 ≤ (eLpNorm f 2)^{1/2} · (eLpNorm f 6)^{1/2}` for `f : Domain3 → G`.

Fresh PUBLIC copy of the `private` `eLpNorm_three_le_interp` (`EnergyClassConvection.lean:510`);
the original is neither moved nor de-privatized.  Proof route unchanged from the original:
the square route `(eLpNorm f 3)² = eLpNorm (‖f‖²) (3/2) ≤ eLpNorm ‖f‖ 6 · eLpNorm ‖f‖ 2`
(Hölder with `1/6 + 1/2 = 2/3`). -/
theorem eLpNorm_three_le_interp_pub {G : Type*} [NormedAddCommGroup G] (f : Domain3 → G)
    (h2 : MemLp f 2 (volume : Measure Domain3))
    (h6 : MemLp f 6 (volume : Measure Domain3)) :
    eLpNorm f 3 (volume : Measure Domain3)
      ≤ (eLpNorm f 2 (volume : Measure Domain3)) ^ (1 / 2 : ℝ)
        * (eLpNorm f 6 (volume : Measure Domain3)) ^ (1 / 2 : ℝ) := by
  sorry -- ALLOW_SORRY: PR-2 scaffold; statement gate precedes proof (this PR)

/-! ### C4 — energy-class trilinear bound on `convIntegralSchwartz` -/

/-- **C4 (Codex-gated statement).** Energy-class bound on the Schwartz convection integral:
there is an absolute constant `C_b ≥ 0` such that for ALL triples of `L²`-fields `u v w`
with Schwartz representatives `ψu ψv ψw` (componentwise `toLp` equalities),
`|convIntegralSchwartz ψu ψv ψw|
    ≤ C_b · ‖u‖^{1/2} · (V₁ u)^{1/4} · √(V₁ v) · √(V₁ w)`.

The `∃ C_b` sits OUTSIDE the quantifiers over `u, v, w, ψu, ψv, ψw`, making the
field-independence (hence the eventual `n`-independence in C5) structurally evident.

Route (plan §3 C4): per-`(i,a)` Hölder with exponents `(3,2,6)` on `∫ u_a (∂_a v_i) w_i`,
then `‖u_a‖₃ ≤ ‖u_a‖₂^{1/2}‖u_a‖₆^{1/2}` (C3), `‖u_a‖₆, ‖w_i‖₆ ≤ C₆√V₁` (C2),
`‖∂_a v_i‖₂ ≤ √(V₁ v)` (C1), and finite-sum aggregation (pattern of
`convIntegralSchwartz_bound_H1`).  Interpolating `‖u‖₂` and `√(V₁ u)` yields the
`‖u‖^{1/2}(V₁ u)^{1/4}` factor. -/
theorem convIntegralSchwartz_bound_energy :
    ∃ C_b : ℝ, 0 ≤ C_b ∧
      ∀ (u v w : L2VF_R3) (ψu ψv ψw : Fin 3 → SchwartzMap Domain3 ℝ),
        (∀ j : Fin 3,
          L2VF_projComponent_R3 j u = (ψu j).toLp 2 (volume : Measure Domain3)) →
        (∀ j : Fin 3,
          L2VF_projComponent_R3 j v = (ψv j).toLp 2 (volume : Measure Domain3)) →
        (∀ j : Fin 3,
          L2VF_projComponent_R3 j w = (ψw j).toLp 2 (volume : Measure Domain3)) →
        |convIntegralSchwartz ψu ψv ψw|
          ≤ C_b * ‖u‖ ^ (1 / 2 : ℝ) * (viscousFormSq_R3 1 u) ^ (1 / 4 : ℝ)
              * Real.sqrt (viscousFormSq_R3 1 v) * Real.sqrt (viscousFormSq_R3 1 w) := by
  sorry -- ALLOW_SORRY: PR-2 scaffold; statement gate precedes proof (this PR)

/-! ### C5 — `n`-uniform trilinear bound for the abstract form `F.b` -/

/-- **C5 (Codex-gated statement — `n`-uniformity is the load-bearing claim).** The abstract
convection form `F.b` obeys the same energy-class bound as `convIntegralSchwartz`, uniformly
over the Galerkin level `n`: there is an absolute constant `C_b ≥ 0` (the same one as C4)
such that for ALL levels `n` and ALL level-`n` states `u v w : L2Sigma_R3`
(`(u:L2VF_R3) = 𝔊.P n u`, likewise `v`, `w`),
`|F.b u v w| ≤ C_b · ‖u‖^{1/2} · (V₁ u)^{1/4} · √(V₁ v) · √(V₁ w)`.

The `∃ C_b` sits OUTSIDE the quantifier over `n` and the states, so the constant is
provably `n`-independent — the property the good-sampling compactness argument needs.

Route (plan §3 C5): B10 Schwartz representations of `u, v, w`, the `F.b_galerkin` pin to
`convIntegralSchwartz`, and C4. -/
theorem bForm_galerkin_abs_le :
    ∃ C_b : ℝ, 0 ≤ C_b ∧
      ∀ (n : ℕ) (u v w : L2Sigma_R3),
        (u : L2VF_R3) = 𝔊.P n (u : L2VF_R3) →
        (v : L2VF_R3) = 𝔊.P n (v : L2VF_R3) →
        (w : L2VF_R3) = 𝔊.P n (w : L2VF_R3) →
        |F.b u v w|
          ≤ C_b * ‖(u : L2VF_R3)‖ ^ (1 / 2 : ℝ)
              * (viscousFormSq_R3 1 (u : L2VF_R3)) ^ (1 / 4 : ℝ)
              * Real.sqrt (viscousFormSq_R3 1 (v : L2VF_R3))
              * Real.sqrt (viscousFormSq_R3 1 (w : L2VF_R3)) := by
  sorry -- ALLOW_SORRY: PR-2 scaffold; statement gate precedes proof (this PR)

/-! ### C6 — continuity of the `b`-integrand along the Galerkin curve -/

/-- **C6.** For a fixed level-`n` test `w`, the diagonal convection integrand along the
Galerkin curve, `σ ↦ F.b (gs.u σ) (gs.u σ) w`, is continuous on forward time `Ici 0`.

Route (plan §3 C6): multilinearity (`b_add_*`) splits the increment into two terms each
controlled by C5 with one slot `= gs.u σ − gs.u σ₀` (still level-`n`), and B6
(H¹-continuity of the Galerkin curve, `galerkin_curve_H1_continuousOn`) drives them to `0`.
Primary (strong) form stated per task; the plan's weaker `IntervalIntegrable` fallback
(`galerkin_bForm_intervalIntegrable`) remains available if the fractional-power ε–δ fights.
This is the interval-integrability input consumed by B9. -/
theorem galerkin_bForm_curve_continuousOn (gs : GalerkinSolutionData_R3 𝔊 F ν u₀ n)
    (w : L2Sigma_R3) (hw : (w : L2VF_R3) = 𝔊.P n (w : L2VF_R3)) :
    ContinuousOn (fun σ => F.b (gs.u σ) (gs.u σ) w) (Set.Ici 0) := by
  sorry -- ALLOW_SORRY: PR-2 scaffold; statement gate precedes proof (this PR)

/-! ### B9 — pairing FTC (deferred here from PR-1) -/

/-- **B9 (Codex-gated statement; deferred from PR-1).** The weak-form pairing FTC along the
Galerkin curve: for a level-`n` test `w` (`(w:L2VF_R3) = 𝔊.P n w`) and `0 ≤ a ≤ b`,
`⟪u(b) − u(a), w⟫ = ∫ σ in a..b, (−ν · stokes(u σ, w) − b(u σ, u σ, w))`.

Route (plan §3 B9): scalar FTC on `g σ := ⟪u σ, w⟫` whose derivative is given by the ODE
field; interval-integrability of the RHS from continuity — the stokes term via
`viscous_curve_continuous` + `stokesTestPairing_eq_sum_inner_wFC`, and the `b` term via C6
(`galerkin_bForm_curve_continuousOn`).  Named `galerkin_pairing_FTC` per the plan's B9
note authorizing the move to File C. -/
theorem galerkin_pairing_FTC (gs : GalerkinSolutionData_R3 𝔊 F ν u₀ n)
    (w : L2Sigma_R3) (hw : (w : L2VF_R3) = 𝔊.P n (w : L2VF_R3))
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    inner (𝕜 := ℝ) ((gs.u b : L2VF_R3) - (gs.u a : L2VF_R3)) (w : L2VF_R3)
      = ∫ σ in a..b,
          (-ν * stokesTestPairing_R3 (gs.u σ : L2VF_R3) (w : L2VF_R3)
            - F.b (gs.u σ) (gs.u σ) w) := by
  sorry -- ALLOW_SORRY: PR-2 scaffold; statement gate precedes proof (this PR)

end LerayHopf
