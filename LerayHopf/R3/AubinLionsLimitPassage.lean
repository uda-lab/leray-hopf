/-
# LerayHopf.R3.AubinLionsLimitPassage — milestone P2 (Aubin–Lions reduction + reusable analytic core)

**Milestone:** `p2-aubin-lions` (honest PARTIAL substantiation; contract
`docs/scratch/p2-aubin-lions.md`, ADDENDUM "Scope refinement" governs the scope below).

This module IMPORTS `R3.SolutionInterfaces` (justified — it *produces* `AubinLionsPackage_R3`
and *consumes* `GalerkinSolutionData_R3`, both of which live in `SolutionInterfaces.lean` with
no lighter exposing module). This is the single heavy import; unlike P3 (`R3.SpatialCompactness`,
deliberately standalone) it is unavoidable here. It also reuses P3
(`localCompactness_R3_of_ballCompact`, `LocalRellichInput`) and R3-d's `b`-bound analytic core
(via `F.b_bound` in `R3.TrilinearEstimate`'s downstream `R3NSForms`).

**Refined scope (ADDENDUM — supersedes §3 Tier P / §9 where they conflict; UPDATED post-#15):**
P2 targets the **Aubin–Lions reduction** (spatial+time ⇒ package) plus **two reusable analytic
lemmas**. As of issue #15 the centerpiece reduction `aubinLionsPackage_R3_of_timeCompactness` (C2)
is **closed sorry-free**: its spatial half is PROVED axiom-free, and the single irreducible
Bochner-time a.e.-L² extraction is isolated as ONE marked axiom `galerkinSpaceTimeExtraction_R3`
(the content mathlib's absent `W^{1,p}(0,T;X)` / vector-valued weak time derivative / Aubin–Lions
theory would supply). The deliverables are otherwise proved axiom-free.

**PROVED, axiom-free (no `sorryAx`):**

* `spatialInput_R3_of_localRellich` (S1) — the `spatial` half, discharged by reusing P3.
* `bForm_tendsto_of_strongL2` (N1) — nonlinear `b`-term passage under strong L² (the R3-d payoff).
* private Steklov building blocks for the (still-open) C2 reduction:
  `galerkin_curve_continuous`, `steklovAvg` (def), `steklovAvg_norm_le_u0` (uniform L² bound),
  `steklovAvg_approx` (time-modulus average↔curve estimate), and `galerkin_norm_le_u0`.

* `kineticEnergy_lsc_bound` (E1) — #14-P discharge, now `sorry`-FREE (issue #31). The full
  norm-lsc-transfer + ball-exhaustion proof (`Bochner.kineticEnergy_lsc_transfer`, `continuous_restrictToBall`,
  `norm_restrictToBall_le`, `normSq_restrictToBall_eq_setIntegral`,
  `tendsto_normSq_restrictToBall`), wired through the #14-C
  `u_aestronglyMeasurable` field and `galerkin_norm_le_u0`. The former residual `MemLp`-gap `sorry`
  (time-integrability of a Bochner-form integrand) is DISCHARGED by the issue #31 strengthening of
  `AubinLionsPackage_R3.strong_convergence` to its faithful `eLpNorm`-form: the field now supplies
  the time-`L²` convergence directly, so `hconv` is exactly `strong_convergence R`.

**CLOSED (issue #15) — C2 is sorry-free:**

* `aubinLionsPackage_R3_of_timeCompactness` (C2) — the centerpiece Aubin–Lions assembly. Its
  spatial half is PROVED axiom-free (the `steklovAvg_spatial_extraction` chain over the FK-derived
  `LocalRellichInput`); every package field is then assembled axiom-free from the conclusion of the
  single isolated extraction axiom `galerkinSpaceTimeExtraction_R3`. The constructor no longer takes
  a `TimeCompactnessInput` argument — that modulus is absorbed into the (now unconditional)
  extraction axiom (see issue #15 collapse). The `TimeCompactnessInput` structure and the
  `galerkin_curves_equicontinuous` helper are retained as legacy/unused scaffolding (referenced only
  in docs), kept for the eventual discharge of the extraction axiom.

**Documented residual frontier (the limit-passage half stays capstone upstream):** the limit-passage
conclusions (b) `WeakFormNS`, (d) initial trace, and (e) energy class require the absent
vector-valued weak time-derivative / `W^{1,p}(0,T;X)` theory and are carried by the upstream
`galerkin_limit_passage_R3` axiom (not by this file). Bundling them into a `GoodRepresentativeInput`
hypothesis would re-assert the conclusions (smuggling), so per the ADDENDUM we DROP that and
`galerkinLimitPassage_R3_of_goodRep`. P2 does NOT itself produce the full `galerkin_limit_passage_R3`
conclusion (this mirrors R3-d, which proved `b`-form lemmas without producing `Nonempty R3NSForms`).

**Axioms backing this file (issue #44):** `galerkinSpaceTimeExtraction_R3` is a PROVED `theorem`
(no sorry in its body) delegating to `u_lim_aestronglyMeasurable` in `ArzelaAscoliTime.lean`.
The two residual axioms live in `ArzelaAscoliTime.lean`:
- `galerkin_spacetime_precompact_R3` — refine-capable local Aubin–Lions–Simon spacetime
  precompactness (L²-in-time Bochner convergence on balls; Mathlib lacks this)
- `galerkin_weakLimit_R3` — Banach–Alaoglu + div-free weak limit in `L2Sigma_R3`
  (Mathlib lacks weak compactness in Hilbert + weak-closedness of div-free subspace)
Note: `galerkin_equicontinuity_from_ODE` (T0.1) was DELETED as UNSOUND (see `ArzelaAscoliTime.lean`).
No `opaque`/`constant`/`unsafe`. The honest isolated hypotheses (P3's `LocalRellichInput`,
R3-d's `hdiv`, P5's `SchwartzGalerkinBasis.dense_span`) remain explicit *arguments*, not axioms.

Target axiom this milestone discharges (issue #15): `aubin_lions_R3` is REMOVED — its spatial half
PROVED, its time content swapped 1-for-1 for the strictly-thinner `galerkinSpaceTimeExtraction_R3`.
-/

-- Import-cycle audit (REQUIRED — Hard rule 10). Verified against the actual import lines:
--   * `R3.SolutionInterfaces` imports ONLY `EvolutionTriple`, `R3.Regularity`, and a mathlib
--     interval-integral module — it does NOT import this file, `R3.SpatialCompactness`, or
--     `R3.TrilinearEstimate`. So importing it here is acyclic.
--   * `R3.SpatialCompactness` imports `R3.Regularity` + mathlib (standalone); `R3.TrilinearEstimate`
--     imports `R3.DivergenceFree` + mathlib (leaf). Importing both here adds no cycle.
--   * This file is a LEAF (nothing imports it). It is the unique place that may reference
--     `AubinLionsPackage_R3` AND reuse P3 — neither of those modules can reference the other.
import LerayHopf.R3.SolutionInterfaces     -- AubinLionsPackage_R3, GalerkinSolutionData_R3, r3Evolution, R3NSForms
import LerayHopf.R3.SpatialCompactness   -- localCompactness_R3_of_ballCompact, LocalRellichInput
import LerayHopf.R3.ArzelaAscoliTime     -- issue #44: T0.1/T0.2 axioms + T1–T4 Arzelà–Ascoli chain + u_lim_aestronglyMeasurable
import LerayHopf.R3.TrilinearEstimate    -- b-bound analytic core (downstream of R3NSForms.b_bound)
import LerayHopf.R3.ViscousWeakLsc       -- Tier E (kinetic + viscous halves): galerkin_norm_le_u0,
                                          -- galerkin_curve_continuous, kineticEnergy_lsc_bound,
                                          -- viscous_pointwise_lsc, viscous_lsc_under_strongL2,
                                          -- inner_tendsto_of_perball, weak_tendsto_of_inner_tendsto, and friends
                                          -- (issue #114 Tier 1 commit 1 split; also re-exposes FourierL2/WeightedFourierCommute)
import LerayHopf.R3.SteklovAverages      -- Tier H/S/C-prep: TimeCompactnessInput,
                                          -- spatialInput_R3_of_localRellich, steklovAvg and the
                                          -- Steklov interval-average building blocks,
                                          -- galerkinSpaceTimeExtraction_R3 (issue #114 Tier 1 commit 2)
import LerayHopf.R3.FourierL2            -- 𝓕, L2C_R3, viscousFormSq_R3_eq_integral_normSq_fourier (F7 spectral exposure for the viscous/H¹ Steklov Jensen bound)
import LerayHopf.R3.WeightedFourierCommute -- mulBdd bounded-multiplier commute + truncated weight (closes the viscous/H¹ Steklov Jensen gate)
import LerayHopf.R3.GalerkinODE          -- galerkinCurve_reg_mem (H¹ regularity of any curve in the Galerkin subspace)
import LerayHopf.R3.SobolevEmbedding     -- memSobolev_of_finite_weightedFourier_R3 (H¹ from finite weighted-Fourier integral; the memH1 conjunct of viscous_pointwise_lsc)
import LerayHopf.R3.ConvectionForm       -- fb_tendsto_of_perball, isSchwartzDivFree_add, and
  -- (transitively via CurlDensityCapstone) stokesTestPairing_R3_eq_sum_inner_negLap (issue #113
  -- PR-1: explicit — was reached only via SobolevEmbedding's now-dropped ConvectionForm import)
import LerayHopf.Bochner.TimeSobolev     -- Bochner.kineticEnergy_lsc_transfer (issue #111 PR-3; verified acyclic)
import Mathlib.MeasureTheory.Integral.Bochner.Set   -- set/interval integrals over balls
import Mathlib.MeasureTheory.Function.UnifTight      -- UnifTight + tendsto_Lp_of_tendsto_ae (Vitali) for the C2 dominated-Lp passage
import Mathlib.MeasureTheory.Function.UniformIntegrable -- UnifIntegrable + unifIntegrable_of for the C2 dominated-Lp passage

namespace LerayHopf

open MeasureTheory Filter Topology Metric
open scoped FourierTransform   -- `𝓕` notation for the viscous/H¹ Steklov spectral Jensen bound

-- Tier H (the isolated TimeCompactnessInput structure) and Tier S
-- (spatialInput_R3_of_localRellich) moved verbatim to `R3.SteklovAverages` (issue #114 Tier 1
-- commit 2), alongside Tier C-prep below -- both are used only by Tier C-prep's private
-- helpers, nowhere else in this file or the repo. Imported above.

/-! ### Tier N — nonlinear `b`-term passage (the reusable analytic core, R3-d payoff) -/

/-- **Nonlinear convection term passes to the limit under strong L² convergence.**

For a fixed Schwartz div-free test `w`, if `uₙ → u` and `vₙ → v` strongly in L²(ℝ³) with a
uniform bound, then `F.b uₙ vₙ w → F.b u v w`. This is the analytic payoff of R3-d's
`b_bound` (bilinear L²-continuity of `b` in its first two slots for Schwartz tests). -/
theorem bForm_tendsto_of_strongL2 (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (w : L2Sigma_R3) (hw : IsSchwartzDivFree_R3 w)
    (uSeq vSeq : ℕ → L2Sigma_R3) (u v : L2Sigma_R3)
    (hu : Tendsto (fun n => ((uSeq n : L2VF_R3))) atTop (𝓝 (u : L2VF_R3)))
    (hv : Tendsto (fun n => ((vSeq n : L2VF_R3))) atTop (𝓝 (v : L2VF_R3))) :
    Tendsto (fun n => F.b (uSeq n) (vSeq n) w) atTop (𝓝 (F.b u v w)) := by
  -- Obtain the bilinear L²-bound constant `C` for the fixed Schwartz test `w`.
  obtain ⟨C, hC⟩ := F.b_bound w hw
  -- Algebraic decomposition (bilinearity in slots 1,2):
  --   b uₙ vₙ w - b u v w = b (uₙ - u) vₙ w + b u (vₙ - v) w.
  have hdecomp : ∀ n,
      F.b (uSeq n) (vSeq n) w - F.b u v w
        = F.b (uSeq n - u) (vSeq n) w + F.b u (vSeq n - v) w := by
    intro n
    have e1 : F.b (uSeq n) (vSeq n) w
        = F.b (uSeq n - u) (vSeq n) w + F.b u (vSeq n) w := by
      have := F.b_add_1 (uSeq n - u) u (vSeq n) w
      simpa [sub_add_cancel] using this
    have e2 : F.b u (vSeq n) w
        = F.b u (vSeq n - v) w + F.b u v w := by
      have := F.b_add_2 u (vSeq n - v) v w
      simpa [sub_add_cancel] using this
    rw [e1, e2]; ring
  -- Pointwise bound on the difference via `b_bound` applied to each summand.
  have hbound : ∀ n,
      |F.b (uSeq n) (vSeq n) w - F.b u v w|
        ≤ C * ‖((uSeq n : L2VF_R3)) - (u : L2VF_R3)‖ * ‖(vSeq n : L2VF_R3)‖
          + C * ‖(u : L2VF_R3)‖ * ‖((vSeq n : L2VF_R3)) - (v : L2VF_R3)‖ := by
    intro n
    rw [hdecomp n]
    calc |F.b (uSeq n - u) (vSeq n) w + F.b u (vSeq n - v) w|
        ≤ |F.b (uSeq n - u) (vSeq n) w| + |F.b u (vSeq n - v) w| := abs_add_le _ _
      _ ≤ C * ‖((uSeq n - u : L2Sigma_R3) : L2VF_R3)‖ * ‖(vSeq n : L2VF_R3)‖
            + C * ‖(u : L2VF_R3)‖ * ‖((vSeq n - v : L2Sigma_R3) : L2VF_R3)‖ :=
          add_le_add (hC _ _) (hC _ _)
      _ = C * ‖((uSeq n : L2VF_R3)) - (u : L2VF_R3)‖ * ‖(vSeq n : L2VF_R3)‖
            + C * ‖(u : L2VF_R3)‖ * ‖((vSeq n : L2VF_R3)) - (v : L2VF_R3)‖ := by
          rw [AddSubgroupClass.coe_sub, AddSubgroupClass.coe_sub]
  -- The upper bound sequence tends to 0.
  have hu' : Tendsto (fun n => ‖((uSeq n : L2VF_R3)) - (u : L2VF_R3)‖) atTop (𝓝 0) := by
    have hsub : Tendsto (fun n => ((uSeq n : L2VF_R3)) - (u : L2VF_R3)) atTop (𝓝 0) := by
      have := hu.sub (tendsto_const_nhds (x := (u : L2VF_R3)))
      simpa using this
    simpa using hsub.norm
  have hv' : Tendsto (fun n => ‖((vSeq n : L2VF_R3)) - (v : L2VF_R3)‖) atTop (𝓝 0) := by
    have hsub : Tendsto (fun n => ((vSeq n : L2VF_R3)) - (v : L2VF_R3)) atTop (𝓝 0) := by
      have := hv.sub (tendsto_const_nhds (x := (v : L2VF_R3)))
      simpa using this
    simpa using hsub.norm
  have hvnorm : Tendsto (fun n => ‖(vSeq n : L2VF_R3)‖) atTop (𝓝 ‖(v : L2VF_R3)‖) := hv.norm
  have hUpper :
      Tendsto (fun n =>
        C * ‖((uSeq n : L2VF_R3)) - (u : L2VF_R3)‖ * ‖(vSeq n : L2VF_R3)‖
          + C * ‖(u : L2VF_R3)‖ * ‖((vSeq n : L2VF_R3)) - (v : L2VF_R3)‖)
        atTop (𝓝 0) := by
    have t1 : Tendsto (fun n =>
        C * ‖((uSeq n : L2VF_R3)) - (u : L2VF_R3)‖ * ‖(vSeq n : L2VF_R3)‖)
        atTop (𝓝 (C * 0 * ‖(v : L2VF_R3)‖)) :=
      ((tendsto_const_nhds.mul hu').mul hvnorm)
    have t2 : Tendsto (fun n =>
        C * ‖(u : L2VF_R3)‖ * ‖((vSeq n : L2VF_R3)) - (v : L2VF_R3)‖)
        atTop (𝓝 (C * ‖(u : L2VF_R3)‖ * 0)) :=
      (tendsto_const_nhds.mul hv')
    have := t1.add t2
    simpa using this
  -- Squeeze the absolute value of the difference to 0, then conclude.
  have hdiff : Tendsto (fun n => F.b (uSeq n) (vSeq n) w - F.b u v w) atTop (𝓝 0) := by
    refine (tendsto_zero_iff_abs_tendsto_zero _).mpr ?_
    exact squeeze_zero (fun n => abs_nonneg _) hbound hUpper
  have := hdiff.add (tendsto_const_nhds (x := F.b u v w))
  simpa using this

-- Tier E — energy inequality (kinetic-lsc half: galerkin_norm_le_u0, galerkin_curve_continuous,
-- kineticEnergy_lsc_bound) and Tier E-prep, plus Tier E (viscous half), all moved verbatim to
-- `R3.ViscousWeakLsc` (issue #114 Tier 1 commit 1). The kinetic-half content moved WITH the
-- viscous half despite the section label, not because of topic but because the viscous-half
-- theorems (`viscous_pointwise_lsc`, `viscous_lsc_under_strongL2`,
-- `liminf_viscousFormSq_lt_top_ae`) call `galerkin_norm_le_u0`/`kineticEnergy_lsc_bound`
-- directly, and this file (which also needs both pervasively elsewhere below) cannot import
-- `R3.ViscousWeakLsc` back without a cycle if they stayed here. Imported above.

-- Tier C-prep — Steklov interval-average building blocks for the Aubin–Lions route — moved
-- verbatim to `R3.SteklovAverages` (issue #114 Tier 1 commit 2), together with its Tier H/Tier S
-- prerequisites. Imported above.

/-! ### Tier W — WeakFormNS limit passage (conjunct 2 of `galerkin_limit_passage_R3`)

This is the `WeakFormNS` conjunct of the limit-passage axiom, isolated as a named lemma so the
axiom's second component can be discharged independently of conjuncts 0/1/3/4.  The target is
exactly `WeakFormNS ν T (r3Evolution 𝔊 F) alPkg.u` — byte-identical to the `weak_eq_limit`
field of `GalerkinCompactnessPackageFull_R3` (and to `hspec.2.1` in `build_galerkin_package_R3`
once the good representative is taken to be `alPkg.u`, conjunct 0 = `EventuallyEq.refl`).

PROOF SKELETON (Temam III.3).  Fix an admissible test `ψ ⊗ w` (`ψ : Time → ℝ` C¹ with
`tsupport ψ ⊆ Ioo 0 T`, `w` Schwartz divergence-free).  For each Galerkin level `N` and each
`n ≥ N` the approximant ODE `u_ode` (`SolutionInterfaces.lean:387`) holds against the Galerkin
test `𝔊.P N w` (a fixed point of `𝔊.P n` for `n ≥ N`).  Multiplying by `ψ(t)`, integrating over
`[0,T]`, and integrating the time-derivative term by parts (boundary-free because
`tsupport ψ ⊆ Ioo 0 T`) yields, for the approximant `uₙ`,
`∫₀ᵀ (-⟪uₙ t, 𝔊.P N w⟫ ψ'(t) + ψ(t)(ν·B(uₙ t, 𝔊.P N w) + b(uₙ t, uₙ t, 𝔊.P N w))) = 0`.
Passing `n→∞` (linear terms by the weak-L² convergence bridge `inner_tendsto_of_perball`; the
nonlinear term by `bForm_tendsto_of_strongL2`) and then `N→∞` (Galerkin test density) gives the
weak form for `alPkg.u` against `ψ ⊗ w`.

PROOF DETAIL (this conjunct is PROVED in `weakFormNS_limit_passage`).  After the structural
reduction (time-IBP + dominated convergence in time, both in hand) three atoms were identified.
Each rests on already-proved pieces — none is a strong-compactness wall.  For reference:
(i) the VISCOUS-form equality passage `B(uₙ t, w) → B(u t, w)`.  `stokesTestPairing_R3` is the
H¹/Dirichlet pairing `∑ⱼ∫ (2π)²‖ξ‖² Re[𝓕uⱼ·conj 𝓕wⱼ]` (`Regularity.lean:123`), not L²-continuous in
`u` as written.  PROVABLE route (Plancherel onto the test): `(2π)²‖ξ‖² 𝓕wⱼ = 𝓕((-Δ)wⱼ)` for Schwartz
`wⱼ`, so by Parseval (`Lp.inner_fourier_eq` / `(Lp.fourierTransformₗᵢ _ _).inner_map_map`) the
pairing equals `⟨u, lapVF w⟩_{L²}` with the FIXED element `lapVF w := -Δw ∈ L²` (Schwartz).  This is
the exact second-order analogue of the already-proved first-order
`divComponent_eq_fourier_integral` (`CurlDensity.lean:460`, which moves a single `∂ⱼ` onto a Schwartz
test via `lineDerivOpCLM`/`schwartzC`/`toLp_schwartzC_eq`).  Once reformulated, it passes by the
full-space WEAK convergence already available (`weak_tendsto_of_inner_tendsto`/`inner_tendsto_of_perball`
against the fixed `lapVF w`).  Atom = the 2nd-order Plancherel–Laplacian reformulation lemma.
(ii) the NONLINEAR passage `b(uₙ t, uₙ t, w) → b(u t, u t, w)` at a.e. `t`.  NOT a full-space
strong-compactness gap: `w` is Schwartz (rapid decay), so the ball-tail ε/3 split
(per-ball strong-L² via `strong_convergence_ae` on `‖x‖≤R` + the `b`-Schwartz-tail bound for
`‖x‖>R`) reduces it — mirroring the `inner_tendsto_of_perball` ball/tail pattern.  Atom = the
trilinear Schwartz-tail bound for `F.b`/`convIntegralSchwartz` (the `‖x‖>R` remainder controlled by
`w`'s decay), currently absent from `TrilinearEstimate`.
(iii) the Galerkin→Schwartz test DENSITY extension (`u_ode` holds only for `𝔊.P n w = w`; pass the
`N`-th identity then `N→∞` via `𝔊.tendsto_id`).
All three stand on already-proved pieces; the structural reduction (time-IBP + dominated convergence
in time) is in hand. -/

/-- **Stokes-pairing continuity along a Galerkin curve.**  For a Galerkin test `w` with a Schwartz
witness `ψw`, `t ↦ stokesTestPairing_R3 (gs.u t) w` is continuous on forward time `Ici 0`.

The negative-Laplacian reformulation `stokesTestPairing_R3_eq_sum_inner_negLap` exhibits the pairing
as a finite sum of `L²`-inner products of the (CLM) component projections of the curve against FIXED
Schwartz elements, so continuity is `(component CLM ∘ curve).inner const`. -/
private theorem stokes_curve_continuousOn_R3
    {𝔊 : R3GalerkinScheme} {F : R3NSForms 𝔊} {ν : ℝ} {u₀ : L2Sigma_R3} {n : ℕ}
    (gs : GalerkinSolutionData_R3 𝔊 F ν u₀ n) (w : L2Sigma_R3)
    (ψw : Fin 3 → SchwartzMap Domain3 ℝ)
    (hψw : ∀ j : Fin 3,
      L2VF_projComponent_R3 j (w : L2VF_R3) = (ψw j).toLp 2 (volume : Measure Domain3)) :
    ContinuousOn (fun s => stokesTestPairing_R3 (gs.u s : L2VF_R3) (w : L2VF_R3)) (Set.Ici 0) := by
  have hcurve : ContinuousOn (fun s => (gs.u s : L2VF_R3)) (Set.Ici 0) :=
    galerkin_curve_continuous 𝔊 F ν u₀ n gs
  simp only [stokesTestPairing_R3_eq_sum_inner_negLap _ (w : L2VF_R3) ψw hψw]
  refine continuousOn_finsetSum _ (fun j _ => ?_)
  exact ((L2VF_projComponent_R3 j).continuous.comp_continuousOn hcurve).inner continuousOn_const

/-- **Convection-form continuity along a Galerkin curve** (Schwartz-test form).  For any
Schwartz-div-free test `w`, `t ↦ F.b (gs.u t) (gs.u t) w` is continuous on forward time `Ici 0`.

Unlike `galerkin_bForm_curve_continuousOn`, this does NOT require `w` to be fixed by `𝔊.P n`; it
builds the jointly-continuous bilinear form `(u,v) ↦ b u v w` directly from `b_bound` (as a
`mkContinuous₂` CLM) and composes with the `L²`-continuous curve. -/
private theorem bForm_curve_continuousOn_of_schwartz
    {𝔊 : R3GalerkinScheme} {F : R3NSForms 𝔊} {ν : ℝ} {u₀ : L2Sigma_R3} {n : ℕ}
    (gs : GalerkinSolutionData_R3 𝔊 F ν u₀ n) (w : L2Sigma_R3) (hw : IsSchwartzDivFree_R3 w) :
    ContinuousOn (fun s => F.b (gs.u s) (gs.u s) w) (Set.Ici 0) := by
  obtain ⟨Cb, hCb⟩ := F.b_bound w hw
  let b_blin : L2Sigma_R3 →ₗ[ℝ] L2Sigma_R3 →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ (fun u v => F.b u v w)
      (fun u u' v => F.b_add_1 u u' v w)
      (fun c u v => (F.b_smul_1 c u v w).trans (smul_eq_mul c _).symm)
      (fun u v v' => F.b_add_2 u v v' w)
      (fun c u v => (F.b_smul_2 c u v w).trans (smul_eq_mul c _).symm)
  have hb_norm : ∀ u v : L2Sigma_R3, ‖b_blin u v‖ ≤ |Cb| * ‖u‖ * ‖v‖ := fun u v => by
    show ‖F.b u v w‖ ≤ |Cb| * ‖u‖ * ‖v‖
    rw [Real.norm_eq_abs]
    calc |F.b u v w| ≤ Cb * ‖(u : L2VF_R3)‖ * ‖(v : L2VF_R3)‖ := hCb u v
      _ ≤ |Cb| * ‖(u : L2VF_R3)‖ * ‖(v : L2VF_R3)‖ := by gcongr; exact le_abs_self _
      _ = |Cb| * ‖u‖ * ‖v‖ := by rw [Submodule.coe_norm, Submodule.coe_norm]
  let b_clm : L2Sigma_R3 →L[ℝ] L2Sigma_R3 →L[ℝ] ℝ := b_blin.mkContinuous₂ |Cb| hb_norm
  have hcurve_sigma : ContinuousOn (fun s => gs.u s) (Set.Ici 0) := by
    have hiso : Isometry (fun x : L2Sigma_R3 => (x : L2VF_R3)) := by
      rw [isometry_iff_dist_eq]; intro x y
      simp only [dist_eq_norm, ← AddSubgroupClass.coe_sub, Submodule.coe_norm]
    exact hiso.isUniformInducing.isInducing.continuousOn_iff.mpr
      (galerkin_curve_continuous 𝔊 F ν u₀ n gs)
  exact (b_clm.continuous₂.comp_continuousOn (hcurve_sigma.prodMk hcurve_sigma)).congr
    (fun s _ => rfl)

/-- **Weak-form integrand continuity along a Galerkin curve.**  For a Schwartz-div-free test `w`
and a `C¹` weight `ψ`, the WeakFormNS integrand `t ↦ -⟪uₙ t, w⟫ ψ'(t) + ψ(t)(ν stokes + b)` is
continuous on forward time `Ici 0`.  Assembled from `stokes_curve_continuousOn_R3`,
`bForm_curve_continuousOn_of_schwartz`, and inner-product continuity. -/
private theorem weakFormNS_integrand_continuousOn_R3
    {𝔊 : R3GalerkinScheme} {F : R3NSForms 𝔊} {ν : ℝ} {u₀ : L2Sigma_R3} {n : ℕ}
    (gs : GalerkinSolutionData_R3 𝔊 F ν u₀ n) (w : L2Sigma_R3) (hw : IsSchwartzDivFree_R3 w)
    (ψ : Time → ℝ) (hψC1 : ContDiff ℝ 1 ψ) :
    ContinuousOn (fun t =>
        -(inner (𝕜 := ℝ) (gs.u t : L2VF_R3) (w : L2VF_R3)) * deriv ψ t +
          ψ t * (ν * stokesTestPairing_R3 (gs.u t : L2VF_R3) (w : L2VF_R3) +
            F.b (gs.u t) (gs.u t) w)) (Set.Ici 0) := by
  obtain ⟨ψw, hψw⟩ := hw
  have hcurve : ContinuousOn (fun s => (gs.u s : L2VF_R3)) (Set.Ici 0) :=
    galerkin_curve_continuous 𝔊 F ν u₀ n gs
  have hinner : ContinuousOn (fun s => inner (𝕜 := ℝ) (gs.u s : L2VF_R3) (w : L2VF_R3))
      (Set.Ici 0) := hcurve.inner continuousOn_const
  have hstokes := stokes_curve_continuousOn_R3 gs w ψw hψw
  have hb := bForm_curve_continuousOn_of_schwartz gs w ⟨ψw, hψw⟩
  exact (hinner.neg.mul hψC1.continuous_deriv_one.continuousOn).add
    (hψC1.continuous.continuousOn.mul ((continuousOn_const.mul hstokes).add hb))

set_option maxHeartbeats 800000 in
/-- **Per-level WeakFormNS identity.**  For a Galerkin level `n` and a test `w` fixed by `𝔊.P n`,
the level-`n` approximant integrand integrates to `0` over `[0,T]`.

Time-IBP via the product-rule FTC on `h(t) := ⟪uₙ t, w⟫ ψ(t)`: the integrand equals `-h'(t)` (using
the ODE field `u_ode` to rewrite `ν stokes + b = -⟪uₙ'(t), w⟫`), and the boundary terms vanish since
`tsupport ψ ⊆ Ioo 0 T`.  Mirrors the T³ `galerkin_weakFormNS_zero`. -/
private theorem galerkin_weakFormNS_zero_R3
    {𝔊 : R3GalerkinScheme} {F : R3NSForms 𝔊} {ν : ℝ} {u₀ : L2Sigma_R3} {n : ℕ}
    (T : ℝ) (hT : 0 < T)
    (gs : GalerkinSolutionData_R3 𝔊 F ν u₀ n) (w : L2Sigma_R3)
    (hw : (w : L2VF_R3) = 𝔊.P n (w : L2VF_R3))
    (ψ : Time → ℝ) (hψsupp : tsupport ψ ⊆ Set.Ioo 0 T) (hψC1 : ContDiff ℝ 1 ψ) :
    ∫ t in (0 : ℝ)..T,
      (-(inner (𝕜 := ℝ) (gs.u t : L2VF_R3) (w : L2VF_R3)) * deriv ψ t +
        ψ t * (ν * stokesTestPairing_R3 (gs.u t : L2VF_R3) (w : L2VF_R3) +
          F.b (gs.u t) (gs.u t) w)) = 0 := by
  -- Schwartz witness of `w` (from the range-Schwartz field at the fixing level `n`).
  have hsdf : IsSchwartzDivFree_R3 w := by
    obtain ⟨ψw, hψw⟩ := 𝔊.range_schwartz n (w : L2VF_R3)
    exact ⟨ψw, fun j => by rw [hw]; exact hψw j⟩
  obtain ⟨ψw, hψw⟩ := hsdf
  -- Boundary values vanish.
  have hψ0 : ψ 0 = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => absurd (hψsupp h).1 (lt_irrefl 0))
  have hψT : ψ T = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => absurd (hψsupp h).2 (lt_irrefl T))
  -- ODE at forward times, and `ψ` is everywhere differentiable.
  have hode : ∀ t, 0 ≤ t →
      inner (𝕜 := ℝ) (deriv (fun s => (gs.u s : L2VF_R3)) t) (w : L2VF_R3) +
        ν * stokesTestPairing_R3 (gs.u t : L2VF_R3) (w : L2VF_R3) + F.b (gs.u t) (gs.u t) w = 0 :=
    fun t ht => gs.u_ode t ht w hw
  have hψderiv : ∀ x, HasDerivAt ψ (deriv ψ x) x :=
    fun x => hψC1.differentiable_one.differentiableAt.hasDerivAt
  -- Product rule for `h(t) = ⟪uₙ t, w⟫ ψ(t)` on forward time.
  have hprod : ∀ t ∈ Set.uIcc (0 : ℝ) T,
      HasDerivAt (fun s => inner (𝕜 := ℝ) (gs.u s : L2VF_R3) (w : L2VF_R3) * ψ s)
        (inner (𝕜 := ℝ) (deriv (fun s => (gs.u s : L2VF_R3)) t) (w : L2VF_R3) * ψ t +
          inner (𝕜 := ℝ) (gs.u t : L2VF_R3) (w : L2VF_R3) * deriv ψ t) t := by
    intro t ht
    rw [Set.uIcc_of_le hT.le, Set.mem_Icc] at ht
    have hinner : HasDerivAt (fun s => inner (𝕜 := ℝ) (gs.u s : L2VF_R3) (w : L2VF_R3))
        (inner (𝕜 := ℝ) (deriv (fun s => (gs.u s : L2VF_R3)) t) (w : L2VF_R3)) t := by
      have hda := (gs.u_hasDeriv t ht.1).inner (𝕜 := ℝ) (hasDerivAt_const t (w : L2VF_R3))
      simpa only [inner_zero_right, add_zero, zero_add] using hda
    exact hinner.mul (hψderiv t)
  -- The integrand equals `-h'(t)` on `[0,T]` (via the ODE).
  have hcongr : Set.EqOn
      (fun t => -(inner (𝕜 := ℝ) (gs.u t : L2VF_R3) (w : L2VF_R3)) * deriv ψ t +
        ψ t * (ν * stokesTestPairing_R3 (gs.u t : L2VF_R3) (w : L2VF_R3) +
          F.b (gs.u t) (gs.u t) w))
      (fun t => -(inner (𝕜 := ℝ) (deriv (fun s => (gs.u s : L2VF_R3)) t) (w : L2VF_R3) * ψ t +
        inner (𝕜 := ℝ) (gs.u t : L2VF_R3) (w : L2VF_R3) * deriv ψ t))
      (Set.uIcc (0 : ℝ) T) := by
    intro t ht
    rw [Set.uIcc_of_le hT.le, Set.mem_Icc] at ht
    have hns : ν * stokesTestPairing_R3 (gs.u t : L2VF_R3) (w : L2VF_R3) + F.b (gs.u t) (gs.u t) w
        = -(inner (𝕜 := ℝ) (deriv (fun s => (gs.u s : L2VF_R3)) t) (w : L2VF_R3)) := by
      have h := hode t ht.1; linarith
    simp only []; rw [hns]; ring
  -- Interval integrability of `h'` via continuity.
  have hAcont : ContinuousOn
      (fun t => inner (𝕜 := ℝ) (deriv (fun s => (gs.u s : L2VF_R3)) t) (w : L2VF_R3))
      (Set.Icc 0 T) := by
    have hst := (stokes_curve_continuousOn_R3 gs w ψw hψw).mono (Set.Icc_subset_Ici_self : Set.Icc (0:ℝ) T ⊆ Set.Ici 0)
    have hb := (bForm_curve_continuousOn_of_schwartz gs w ⟨ψw, hψw⟩).mono (Set.Icc_subset_Ici_self : Set.Icc (0:ℝ) T ⊆ Set.Ici 0)
    have hrhs : ContinuousOn
        (fun t => -(ν * stokesTestPairing_R3 (gs.u t : L2VF_R3) (w : L2VF_R3) +
          F.b (gs.u t) (gs.u t) w)) (Set.Icc 0 T) :=
      ((continuousOn_const.mul hst).add hb).neg
    refine hrhs.congr (fun t ht => ?_)
    have h := hode t ht.1; linarith
  have hinner_cont : ContinuousOn (fun t => inner (𝕜 := ℝ) (gs.u t : L2VF_R3) (w : L2VF_R3))
      (Set.Icc 0 T) :=
    ((galerkin_curve_continuous 𝔊 F ν u₀ n gs).inner continuousOn_const).mono (Set.Icc_subset_Ici_self : Set.Icc (0:ℝ) T ⊆ Set.Ici 0)
  have hh'_ii : IntervalIntegrable
      (fun t => inner (𝕜 := ℝ) (deriv (fun s => (gs.u s : L2VF_R3)) t) (w : L2VF_R3) * ψ t +
        inner (𝕜 := ℝ) (gs.u t : L2VF_R3) (w : L2VF_R3) * deriv ψ t) volume 0 T :=
    ((hAcont.mul hψC1.continuous.continuousOn).add
      (hinner_cont.mul hψC1.continuous_deriv_one.continuousOn)).intervalIntegrable_of_Icc hT.le
  -- FTC: `∫ h' = h T - h 0`, boundary terms vanish.
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hprod hh'_ii
  rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_neg, hFTC, hψ0, hψT]
  ring

/-! ### Shared `[0,T]`-window bridge, factored out of the three `weakFormNS`/`bForm` monoliths
below (each of which independently `set μ := volume.restrict (Set.Icc 0 T)` and re-derived the
same interval-integral ↔ measure-integral interchange facts). -/

/-- The restricted measure `volume.restrict (Set.Icc 0 T)` used by every `[0,T]`-window
argument in this file. -/
private noncomputable def restrictAvgMeasure (T : ℝ) : Measure ℝ :=
  volume.restrict (Set.Icc (0 : ℝ) T)

private theorem isFiniteMeasure_restrictAvgMeasure (T : ℝ) :
    IsFiniteMeasure (restrictAvgMeasure T) := by
  refine isFiniteMeasure_restrict.2 ?_
  rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top

/-- The interval integral over `[0,T]` equals the `restrictAvgMeasure T`-integral. -/
private theorem intervalIntegral_eq_restrictAvgMeasure_integral (T : ℝ) (hT : 0 ≤ T) (g : ℝ → ℝ) :
    ∫ t in (0 : ℝ)..T, g t = ∫ t, g t ∂(restrictAvgMeasure T) := by
  rw [intervalIntegral.integral_of_le hT, restrictAvgMeasure,
    Measure.restrict_congr_set Ioc_ae_eq_Icc]

private theorem restrictAvgMeasure_univ_toReal (T : ℝ) (hT : 0 < T) :
    ((restrictAvgMeasure T) Set.univ).toReal = T := by
  rw [restrictAvgMeasure, Measure.restrict_apply_univ, Real.volume_Icc,
    ENNReal.toReal_ofReal (by linarith)]
  ring

private theorem ae_zero_le_of_restrictAvgMeasure (T : ℝ) :
    ∀ᵐ t ∂(restrictAvgMeasure T), (0 : ℝ) ≤ t := by
  refine ae_restrict_of_forall_mem measurableSet_Icc fun t ht => ht.1

private theorem ae_mem_Icc_of_restrictAvgMeasure (T : ℝ) :
    ∀ᵐ t ∂(restrictAvgMeasure T), t ∈ Set.Icc (0 : ℝ) T :=
  ae_restrict_mem measurableSet_Icc

/-- **Continuity + uniform dominator bound for the W1 approximant integrand.** Steps (1)+(2) of
`weakFormNS_galerkinTest_limit`: each level-`n` approximant integrand is continuous on `[0,T]`,
and its norm is bounded by the `n`-independent constant `M‖w‖Mψ' + Mψ(ν‖vElt‖M + Cb'M²)`
(triangle inequality against the uniform Galerkin `H`-bound `galerkin_norm_le_u0`, the fixed
Stokes-pairing Riesz vector `vElt`, and the convection-form bound `Cb'`). -/
private theorem weakFormNS_galerkinTest_uniform_dominator
    (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊) (ν : ℝ) (hν : 0 < ν) (T : ℝ)
    (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n)
    (alPkg : AubinLionsPackage_R3 𝔊 F ν T u₀ galSeq)
    (w : L2Sigma_R3)
    (ψ : Time → ℝ) (hψC1 : ContDiff ℝ 1 ψ)
    (ψw : Fin 3 → SchwartzMap Domain3 ℝ)
    (hψw : ∀ j : Fin 3, L2VF_projComponent_R3 j (w : L2VF_R3)
      = (ψw j).toLp 2 (volume : Measure Domain3))
    (vElt : L2VF_R3)
    (hstokes_inner : ∀ x : L2VF_R3,
      stokesTestPairing_R3 x (w : L2VF_R3) = inner (𝕜 := ℝ) vElt x)
    (Cb' : ℝ) (hCb'0 : 0 ≤ Cb')
    (hbbound : ∀ u v : L2Sigma_R3, |F.b u v w| ≤ Cb' * ‖(u : L2VF_R3)‖ * ‖(v : L2VF_R3)‖)
    (Mψ Mψ' : ℝ) (hMψ0 : 0 ≤ Mψ)
    (hMψb : ∀ t ∈ Set.Icc (0 : ℝ) T, |ψ t| ≤ Mψ)
    (hMψ'b : ∀ t ∈ Set.Icc (0 : ℝ) T, |deriv ψ t| ≤ Mψ') :
    (∀ n, ContinuousOn (fun t : ℝ =>
        -(inner (𝕜 := ℝ) ((galSeq (alPkg.φ n)).u t : L2VF_R3) (w : L2VF_R3)) * deriv ψ t +
          ψ t * (ν * stokesTestPairing_R3 ((galSeq (alPkg.φ n)).u t : L2VF_R3) (w : L2VF_R3) +
            F.b ((galSeq (alPkg.φ n)).u t) ((galSeq (alPkg.φ n)).u t) w))
        (Set.Icc (0 : ℝ) T)) ∧
    (∀ n, ∀ᵐ t ∂(restrictAvgMeasure T), ‖
        -(inner (𝕜 := ℝ) ((galSeq (alPkg.φ n)).u t : L2VF_R3) (w : L2VF_R3)) * deriv ψ t +
          ψ t * (ν * stokesTestPairing_R3 ((galSeq (alPkg.φ n)).u t : L2VF_R3) (w : L2VF_R3) +
            F.b ((galSeq (alPkg.φ n)).u t) ((galSeq (alPkg.φ n)).u t) w)‖
      ≤ ‖(u₀ : L2VF_R3)‖ * ‖(w : L2VF_R3)‖ * Mψ'
        + Mψ * (ν * ‖vElt‖ * ‖(u₀ : L2VF_R3)‖ + Cb' * ‖(u₀ : L2VF_R3)‖ * ‖(u₀ : L2VF_R3)‖)) := by
  set M : ℝ := ‖(u₀ : L2VF_R3)‖ with hMdef
  have hM0 : 0 ≤ M := norm_nonneg _
  set Fseq : ℕ → ℝ → ℝ := fun n t =>
    -(inner (𝕜 := ℝ) ((galSeq (alPkg.φ n)).u t : L2VF_R3) (w : L2VF_R3)) * deriv ψ t +
      ψ t * (ν * stokesTestPairing_R3 ((galSeq (alPkg.φ n)).u t : L2VF_R3) (w : L2VF_R3) +
        F.b ((galSeq (alPkg.φ n)).u t) ((galSeq (alPkg.φ n)).u t) w) with hFseq
  set D : ℝ := M * ‖(w : L2VF_R3)‖ * Mψ' + Mψ * (ν * ‖vElt‖ * M + Cb' * M * M) with hD
  refine ⟨fun n => ?_, fun n => ?_⟩
  · have hc := (weakFormNS_integrand_continuousOn_R3 (galSeq (alPkg.φ n)) w ⟨ψw, hψw⟩ ψ hψC1).mono
      (Set.Icc_subset_Ici_self : Set.Icc (0:ℝ) T ⊆ Set.Ici 0)
    simpa only [hFseq] using hc
  · have hae_ge := ae_zero_le_of_restrictAvgMeasure T
    have hae_Icc := ae_mem_Icc_of_restrictAvgMeasure T
    filter_upwards [hae_ge, hae_Icc] with t htg htIcc
    have hUn : ‖((galSeq (alPkg.φ n)).u t : L2VF_R3)‖ ≤ M := by
      rw [hMdef]; exact galerkin_norm_le_u0 𝔊 F ν u₀ (alPkg.φ n) (galSeq (alPkg.φ n)) htg
    have hψb : |ψ t| ≤ Mψ := hMψb t htIcc
    have hψ'b : |deriv ψ t| ≤ Mψ' := hMψ'b t htIcc
    have hinb : |inner (𝕜 := ℝ) ((galSeq (alPkg.φ n)).u t : L2VF_R3) (w : L2VF_R3)|
        ≤ M * ‖(w : L2VF_R3)‖ := (abs_real_inner_le_norm _ _).trans (by gcongr)
    have hstok : |stokesTestPairing_R3 ((galSeq (alPkg.φ n)).u t : L2VF_R3) (w : L2VF_R3)|
        ≤ ‖vElt‖ * M := by
      rw [hstokes_inner]; exact (abs_real_inner_le_norm _ _).trans (by gcongr)
    have hbb : |F.b ((galSeq (alPkg.φ n)).u t) ((galSeq (alPkg.φ n)).u t) w| ≤ Cb' * M * M := by
      refine (hbbound _ _).trans ?_; gcongr
    show ‖Fseq n t‖ ≤ D
    rw [hFseq, Real.norm_eq_abs]
    calc |(-(inner (𝕜 := ℝ) ((galSeq (alPkg.φ n)).u t : L2VF_R3) (w : L2VF_R3))) * deriv ψ t +
            ψ t * (ν * stokesTestPairing_R3 ((galSeq (alPkg.φ n)).u t : L2VF_R3) (w : L2VF_R3) +
              F.b ((galSeq (alPkg.φ n)).u t) ((galSeq (alPkg.φ n)).u t) w)|
        ≤ |(-(inner (𝕜 := ℝ) ((galSeq (alPkg.φ n)).u t : L2VF_R3) (w : L2VF_R3))) * deriv ψ t|
          + |ψ t * (ν * stokesTestPairing_R3 ((galSeq (alPkg.φ n)).u t : L2VF_R3) (w : L2VF_R3) +
              F.b ((galSeq (alPkg.φ n)).u t) ((galSeq (alPkg.φ n)).u t) w)| := abs_add_le _ _
      _ ≤ M * ‖(w : L2VF_R3)‖ * Mψ' + Mψ * (ν * ‖vElt‖ * M + Cb' * M * M) := by
          refine add_le_add ?_ ?_
          · rw [abs_mul, abs_neg]
            exact mul_le_mul hinb hψ'b (abs_nonneg _) (mul_nonneg hM0 (norm_nonneg _))
          · rw [abs_mul]
            refine mul_le_mul hψb ?_ (abs_nonneg _) hMψ0
            calc |ν * stokesTestPairing_R3 ((galSeq (alPkg.φ n)).u t : L2VF_R3) (w : L2VF_R3) +
                    F.b ((galSeq (alPkg.φ n)).u t) ((galSeq (alPkg.φ n)).u t) w|
                ≤ |ν * stokesTestPairing_R3 ((galSeq (alPkg.φ n)).u t : L2VF_R3) (w : L2VF_R3)|
                  + |F.b ((galSeq (alPkg.φ n)).u t) ((galSeq (alPkg.φ n)).u t) w| := abs_add_le _ _
              _ = ν * |stokesTestPairing_R3 ((galSeq (alPkg.φ n)).u t : L2VF_R3) (w : L2VF_R3)|
                  + |F.b ((galSeq (alPkg.φ n)).u t) ((galSeq (alPkg.φ n)).u t) w| := by
                    rw [abs_mul, abs_of_nonneg hν.le]
              _ ≤ ν * (‖vElt‖ * M) + Cb' * M * M :=
                    add_le_add (mul_le_mul_of_nonneg_left hstok hν.le) hbb
              _ = ν * ‖vElt‖ * M + Cb' * M * M := by ring
      _ = D := by rw [hD]

set_option maxHeartbeats 1600000 in
/-- **W1: weak identity for the Aubin–Lions limit against a FIXED Galerkin test** (n→∞).

For a test `w` that is already a Galerkin test of the scheme `𝔊` (i.e. `𝔊.P N w = w` for
some level `N`), the limit curve `alPkg.u` satisfies the distributional Navier–Stokes integral
identity against `ψ ⊗ w`.

This is the first stage (W1) of the two-stage proof of `weakFormNS_limit_passage`:
- W1 (this lemma): n→∞ for FIXED Galerkin tests — no test approximation needed.
- W2 (PR-4, `weakFormNS_limit_passage` with `R3TestApproxH1` binder): extend to all Schwartz
  div-free tests via H¹-approximation.

Statement is VERBATIM from spike S4 (`weakFormNS_galerkinTest_spike`, issue #93 appendix). -/
theorem weakFormNS_galerkinTest_limit
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
  classical
  obtain ⟨m, hm⟩ := hw
  -- Global Schwartz witness of the Galerkin test `w`.
  have hsdf : IsSchwartzDivFree_R3 w := by
    obtain ⟨ψ, hψ⟩ := 𝔊.range_schwartz m (w : L2VF_R3)
    exact ⟨ψ, fun j => by rw [← hm]; exact hψ j⟩
  obtain ⟨ψw, hψw⟩ := hsdf
  set M : ℝ := ‖(u₀ : L2VF_R3)‖ with hMdef
  have hM0 : 0 ≤ M := norm_nonneg _
  -- The Stokes functional as an inner product against a FIXED element `vElt`.
  obtain ⟨E, hE⟩ : ∃ E : Fin 3 → Lp ℝ 2 (volume : Measure Domain3),
      ∀ x : L2VF_R3, stokesTestPairing_R3 x (w : L2VF_R3)
        = ∑ j : Fin 3, inner (𝕜 := ℝ) (L2VF_projComponent_R3 j x) (E j) :=
    ⟨_, fun x => stokesTestPairing_R3_eq_sum_inner_negLap x (w : L2VF_R3) ψw hψw⟩
  set vElt : L2VF_R3 :=
    ∑ j : Fin 3, (L2VF_projComponent_R3 j).adjoint (E j) with hvElt
  have hstokes_inner : ∀ x : L2VF_R3,
      stokesTestPairing_R3 x (w : L2VF_R3) = inner (𝕜 := ℝ) vElt x := by
    intro x
    rw [hE x, hvElt, sum_inner]
    exact Finset.sum_congr rfl fun j _ => by
      rw [ContinuousLinearMap.adjoint_inner_left]; exact real_inner_comm _ _
  -- Convection-form bound constant (made nonnegative).
  obtain ⟨Cb, hCb⟩ := F.b_bound w ⟨ψw, hψw⟩
  set Cb' : ℝ := |Cb| with hCb'def
  have hCb'0 : 0 ≤ Cb' := abs_nonneg _
  have hbbound : ∀ u v : L2Sigma_R3,
      |F.b u v w| ≤ Cb' * ‖(u : L2VF_R3)‖ * ‖(v : L2VF_R3)‖ := fun u v =>
    (hCb u v).trans (by gcongr; exact le_abs_self _)
  -- Sup bounds for `ψ`, `ψ'` on `[0,T]`.
  obtain ⟨Mψ, hMψ⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    hψC1.continuous.continuousOn
  obtain ⟨Mψ', hMψ'⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    hψC1.continuous_deriv_one.continuousOn
  have hMψ0 : 0 ≤ Mψ := le_trans (norm_nonneg _) (hMψ 0 ⟨le_refl 0, hT.le⟩)
  have hMψb : ∀ t ∈ Set.Icc (0 : ℝ) T, |ψ t| ≤ Mψ := fun t htIcc => by
    rw [← Real.norm_eq_abs]; exact hMψ t htIcc
  have hMψ'b : ∀ t ∈ Set.Icc (0 : ℝ) T, |deriv ψ t| ≤ Mψ' := fun t htIcc => by
    rw [← Real.norm_eq_abs]; exact hMψ' t htIcc
  -- Finite time measure and interval/measure bridge (shared `RestrictAvgIntegralBridge`).
  haveI hμfin : IsFiniteMeasure (restrictAvgMeasure T) := isFiniteMeasure_restrictAvgMeasure T
  -- Approximant and limit integrands.
  set Fseq : ℕ → ℝ → ℝ := fun n t =>
    -(inner (𝕜 := ℝ) ((galSeq (alPkg.φ n)).u t : L2VF_R3) (w : L2VF_R3)) * deriv ψ t +
      ψ t * (ν * stokesTestPairing_R3 ((galSeq (alPkg.φ n)).u t : L2VF_R3) (w : L2VF_R3) +
        F.b ((galSeq (alPkg.φ n)).u t) ((galSeq (alPkg.φ n)).u t) w) with hFseq
  set flim : ℝ → ℝ := fun t =>
    -(inner (𝕜 := ℝ) (alPkg.u t : L2VF_R3) (w : L2VF_R3)) * deriv ψ t +
      ψ t * (ν * stokesTestPairing_R3 (alPkg.u t : L2VF_R3) (w : L2VF_R3) +
        F.b (alPkg.u t) (alPkg.u t) w) with hflim
  -- Constant dominator.
  set D : ℝ := M * ‖(w : L2VF_R3)‖ * Mψ' + Mψ * (ν * ‖vElt‖ * M + Cb' * M * M) with hD
  -- (1)+(2) Continuity + uniform dominator bound, via the extracted step.
  obtain ⟨hcontFseq, hbound⟩ := weakFormNS_galerkinTest_uniform_dominator 𝔊 F ν hν T u₀
    galSeq alPkg w ψ hψC1 ψw hψw vElt hstokes_inner Cb' hCb'0 hbbound Mψ Mψ' hMψ0 hMψb hMψ'b
  have hmeasFseq : ∀ n, AEStronglyMeasurable (Fseq n) (restrictAvgMeasure T) := fun n =>
    (hcontFseq n).aestronglyMeasurable measurableSet_Icc
  have hDint : Integrable (fun _ : ℝ => D) (restrictAvgMeasure T) := integrable_const _
  -- (3) Pointwise a.e.-t convergence of the integrands.
  have hae_ge := ae_zero_le_of_restrictAvgMeasure T
  have hballconv : ∀ᵐ t ∂(restrictAvgMeasure T), ∀ k : ℕ,
      Filter.Tendsto (fun n => restrictToBall (k : ℝ) ((galSeq (alPkg.φ n)).u t : L2VF_R3))
        Filter.atTop (nhds (restrictToBall (k : ℝ) (alPkg.u t : L2VF_R3))) :=
    ae_all_iff.2 fun k => alPkg.strong_convergence_ae k
  have hnormlim : ∀ᵐ t ∂(restrictAvgMeasure T), ‖(alPkg.u t : L2VF_R3)‖ ≤ M := by
    filter_upwards [kineticEnergy_lsc_bound 𝔊 F ν T u₀ galSeq alPkg] with t ht
    have hsq : ‖(alPkg.u t : L2VF_R3)‖ ^ 2 ≤ M ^ 2 := by rw [hMdef]; nlinarith [ht]
    exact le_of_sq_le_sq hsq hM0
  have hpt : ∀ᵐ t ∂(restrictAvgMeasure T),
      Filter.Tendsto (fun n => Fseq n t) Filter.atTop (nhds (flim t)) := by
    filter_upwards [hballconv, hnormlim, hae_ge] with t hball hnorm htg
    have hbd : ∀ n, ‖((galSeq (alPkg.φ n)).u t : L2VF_R3)‖ ≤ M := fun n => by
      rw [hMdef]; exact galerkin_norm_le_u0 𝔊 F ν u₀ (alPkg.φ n) (galSeq (alPkg.φ n)) htg
    have hlin : Filter.Tendsto
        (fun n => inner (𝕜 := ℝ) ((galSeq (alPkg.φ n)).u t : L2VF_R3) (w : L2VF_R3))
        Filter.atTop (nhds (inner (𝕜 := ℝ) (alPkg.u t : L2VF_R3) (w : L2VF_R3))) := by
      have h := inner_tendsto_of_perball (w : L2VF_R3)
        (fun n => ((galSeq (alPkg.φ n)).u t : L2VF_R3)) (alPkg.u t : L2VF_R3) M hM0 hbd hnorm hball
      simpa only [real_inner_comm (w : L2VF_R3)] using h
    have hstk : Filter.Tendsto
        (fun n => stokesTestPairing_R3 ((galSeq (alPkg.φ n)).u t : L2VF_R3) (w : L2VF_R3))
        Filter.atTop (nhds (stokesTestPairing_R3 (alPkg.u t : L2VF_R3) (w : L2VF_R3))) := by
      simp only [hstokes_inner]
      exact inner_tendsto_of_perball vElt
        (fun n => ((galSeq (alPkg.φ n)).u t : L2VF_R3)) (alPkg.u t : L2VF_R3) M hM0 hbd hnorm hball
    have hnl : Filter.Tendsto (fun n => F.b ((galSeq (alPkg.φ n)).u t) ((galSeq (alPkg.φ n)).u t) w)
        Filter.atTop (nhds (F.b (alPkg.u t) (alPkg.u t) w)) :=
      fb_tendsto_of_perball F w ⟨ψw, hψw⟩ (fun n => (galSeq (alPkg.φ n)).u t) (alPkg.u t)
        M hM0 hbd hnorm hball
    simp only [hFseq, hflim]
    exact (hlin.neg.mul_const (deriv ψ t)).add
      (((hstk.const_mul ν).add hnl).const_mul (ψ t))
  -- (4) Dominated convergence: approximant integrals converge to the limit integral.
  have hlim := tendsto_integral_of_dominated_convergence (fun _ => D) hmeasFseq hDint hbound hpt
  -- (5) The approximant integrals are eventually `0` (per-level IBP identity).
  have hzero_ev : ∀ᶠ n in Filter.atTop, ∫ t, Fseq n t ∂(restrictAvgMeasure T) = 0 := by
    filter_upwards [Filter.eventually_ge_atTop m] with n hn
    have hproj : (w : L2VF_R3) = 𝔊.P (alPkg.φ n) (w : L2VF_R3) :=
      (𝔊.mono_range m (alPkg.φ n) (le_trans hn alPkg.φ_mono.le_apply) (w : L2VF_R3) hm).symm
    rw [← intervalIntegral_eq_restrictAvgMeasure_integral T hT.le (Fseq n)]; simp only [hFseq]
    exact galerkin_weakFormNS_zero_R3 T hT (galSeq (alPkg.φ n)) w hproj ψ hψsupp hψC1
  have hlim0 : Filter.Tendsto (fun n => ∫ t, Fseq n t ∂(restrictAvgMeasure T)) Filter.atTop (nhds 0) :=
    Filter.Tendsto.congr' (hzero_ev.mono fun n h => h.symm) tendsto_const_nhds
  have hflim0 : ∫ t, flim t ∂(restrictAvgMeasure T) = 0 := tendsto_nhds_unique hlim hlim0
  rw [intervalIntegral_eq_restrictAvgMeasure_integral T hT.le flim]; exact hflim0

/-! ### W2 helper lemmas (PR-4, issue #4): extend W1 from Galerkin tests to Schwartz tests -/

/-- Elementary bound `√y ≤ 1 + y` for `y ≥ 0` (used to dominate `√V₁` by the integrable
`1 + V₁`). -/
private theorem sqrt_le_one_add_self_R3 (y : ℝ) (hy : 0 ≤ y) : Real.sqrt y ≤ 1 + y := by
  have hle : y ≤ (1 + y) ^ 2 := by nlinarith [sq_nonneg y]
  calc Real.sqrt y ≤ Real.sqrt ((1 + y) ^ 2) := Real.sqrt_le_sqrt hle
    _ = |1 + y| := Real.sqrt_sq_eq_abs _
    _ = 1 + y := abs_of_nonneg (by linarith)

/-- Elementary bound `y^{1/4}·√y = y^{3/4} ≤ 1 + y` for `y ≥ 0` (used to dominate the
Ladyzhenskaya factor `V₁^{1/4}·√V₁` by the integrable `1 + V₁`). -/
private theorem rpow_quarter_mul_sqrt_le_R3 (y : ℝ) (hy0 : 0 ≤ y) :
    y ^ (1 / 4 : ℝ) * Real.sqrt y ≤ 1 + y := by
  rcases eq_or_lt_of_le hy0 with h | h
  · rw [← h]; simp
  · have hcomb : y ^ (1 / 4 : ℝ) * Real.sqrt y = y ^ (3 / 4 : ℝ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add h]; norm_num
    rw [hcomb]
    rcases le_total y 1 with hle | hge
    · have : y ^ (3 / 4 : ℝ) ≤ 1 := Real.rpow_le_one hy0 hle (by norm_num)
      linarith
    · have : y ^ (3 / 4 : ℝ) ≤ y ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hge (by norm_num)
      rw [Real.rpow_one] at this; linarith

/-- `IsSchwartzDivFree_R3` is closed under subtraction (add + `(-1)`-smul). -/
private theorem isSchwartzDivFree_R3_sub (u v : L2Sigma_R3)
    (hu : IsSchwartzDivFree_R3 u) (hv : IsSchwartzDivFree_R3 v) :
    IsSchwartzDivFree_R3 (u - v) := by
  rw [sub_eq_add_neg, ← neg_one_smul ℝ v]
  exact isSchwartzDivFree_add u _ hu (isSchwartzDivFree_smul (-1) v hv)

/-- `memH1VF_R3` is closed under subtraction (add + `(-1)`-smul; public mirror of the
`private` `GalerkinBasisH1.memH1VF_R3_sub`). -/
private theorem memH1VF_R3_sub_local {u v : L2VF_R3} (hu : memH1VF_R3 u) (hv : memH1VF_R3 v) :
    memH1VF_R3 (u - v) := by
  rw [sub_eq_add_neg, ← neg_one_smul ℝ v]
  exact memH1VF_R3_add hu (memH1VF_R3_smul (-1) hv)

/-- Right-slot subtraction-linearity of the viscous pairing on `H¹` fields, via the
weighted-Fourier representation (`stokesTestPairing_eq_sum_inner_wFC` +
`weightedFourierComponent_sub`). -/
private theorem stokesTestPairing_R3_sub_right (u a b : L2VF_R3)
    (hu : memH1VF_R3 u) (ha : memH1VF_R3 a) (hb : memH1VF_R3 b) :
    stokesTestPairing_R3 u (a - b)
      = stokesTestPairing_R3 u a - stokesTestPairing_R3 u b := by
  have hab : memH1VF_R3 (a - b) := memH1VF_R3_sub_local ha hb
  rw [stokesTestPairing_eq_sum_inner_wFC u (a - b) hu hab,
    stokesTestPairing_eq_sum_inner_wFC u a hu ha,
    stokesTestPairing_eq_sum_inner_wFC u b hu hb, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [weightedFourierComponent_sub a b ha hb hab j, inner_sub_left, Complex.sub_re]

/-- Third-slot subtraction-linearity of the convection form (from `b_add_3`/`b_smul_3`). -/
private theorem bForm_R3_sub_3 {𝔊 : R3GalerkinScheme} (F : R3NSForms 𝔊) (u v a b : L2Sigma_R3) :
    F.b u v (a - b) = F.b u v a - F.b u v b := by
  rw [sub_eq_add_neg a b, ← neg_one_smul ℝ b, F.b_add_3, F.b_smul_3]; ring

/-- **Uniform integrable crude dominator for `b(uₙ,uₙ,z)`.** Given the per-level pointwise
crude Ladyzhenskaya bound `|b(uₙt,uₙt,z)| ≤ C_b√M(1+V₁(uₙt))S`, the a.e.-norm form of that
bound, its nonnegativity and integrability, and its `n`-uniform time-integral cap by `K·S`
(via `reg_bound`) all follow. This packages the steps consumed twice by `bForm_limit_convection_bound`'s Fatou argument (`hlint_n`: `ofReal_integral_eq_lintegral_ofReal` needs both
the a.e. bound and the dominator's own nonnegativity/integrability/integral cap). -/
private theorem bForm_galerkin_crude_dominator_bound
    (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊) (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T)
    (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n)
    (alPkg : AubinLionsPackage_R3 𝔊 F ν T u₀ galSeq)
    (z : L2Sigma_R3) (C_b : ℝ) (hC_b0 : 0 ≤ C_b)
    (hFb_crude_pt : ∀ n t, 0 ≤ t →
      |F.b ((galSeq (alPkg.φ n)).u t) ((galSeq (alPkg.φ n)).u t) z|
        ≤ C_b * Real.sqrt ‖(u₀ : L2VF_R3)‖
            * (1 + viscousFormSq_R3 1 ((galSeq (alPkg.φ n)).u t : L2VF_R3))
            * Real.sqrt (viscousFormSq_R3 1 (z : L2VF_R3))) :
    (∀ n, ∀ᵐ t ∂(restrictAvgMeasure T),
        ‖F.b ((galSeq (alPkg.φ n)).u t) ((galSeq (alPkg.φ n)).u t) z‖
          ≤ C_b * Real.sqrt ‖(u₀ : L2VF_R3)‖
              * (1 + viscousFormSq_R3 1 ((galSeq (alPkg.φ n)).u t : L2VF_R3))
              * Real.sqrt (viscousFormSq_R3 1 (z : L2VF_R3))) ∧
    (∀ n t, 0 ≤ C_b * Real.sqrt ‖(u₀ : L2VF_R3)‖
        * (1 + viscousFormSq_R3 1 ((galSeq (alPkg.φ n)).u t : L2VF_R3))
        * Real.sqrt (viscousFormSq_R3 1 (z : L2VF_R3))) ∧
    (∀ n, Integrable (fun t => C_b * Real.sqrt ‖(u₀ : L2VF_R3)‖
        * (1 + viscousFormSq_R3 1 ((galSeq (alPkg.φ n)).u t : L2VF_R3))
        * Real.sqrt (viscousFormSq_R3 1 (z : L2VF_R3))) (restrictAvgMeasure T)) ∧
    (∀ n, ∫ t, C_b * Real.sqrt ‖(u₀ : L2VF_R3)‖
        * (1 + viscousFormSq_R3 1 ((galSeq (alPkg.φ n)).u t : L2VF_R3))
        * Real.sqrt (viscousFormSq_R3 1 (z : L2VF_R3)) ∂(restrictAvgMeasure T)
        ≤ (C_b * Real.sqrt ‖(u₀ : L2VF_R3)‖
            * (T + ν⁻¹ * ((1 / 2 : ℝ) * ‖(u₀ : L2VF_R3)‖ ^ 2)))
          * Real.sqrt (viscousFormSq_R3 1 (z : L2VF_R3))) := by
  haveI : IsFiniteMeasure (restrictAvgMeasure T) := isFiniteMeasure_restrictAvgMeasure T
  set M : ℝ := ‖(u₀ : L2VF_R3)‖ with hMdef
  set S : ℝ := Real.sqrt (viscousFormSq_R3 1 (z : L2VF_R3)) with hS
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hae_ge := ae_zero_le_of_restrictAvgMeasure T
  have hFb_crude : ∀ n, ∀ᵐ t ∂(restrictAvgMeasure T),
      ‖F.b ((galSeq (alPkg.φ n)).u t) ((galSeq (alPkg.φ n)).u t) z‖
        ≤ C_b * Real.sqrt M
            * (1 + viscousFormSq_R3 1 ((galSeq (alPkg.φ n)).u t : L2VF_R3)) * S := by
    intro n; filter_upwards [hae_ge] with t htg
    rw [Real.norm_eq_abs]; exact hFb_crude_pt n t htg
  have hV1_int : ∀ n,
      Integrable (fun t => viscousFormSq_R3 1 ((galSeq (alPkg.φ n)).u t : L2VF_R3))
        (restrictAvgMeasure T) := by
    intro n
    exact ((galerkin_viscous_curve_continuousOn (galSeq (alPkg.φ n))).mono
      Set.Icc_subset_Ici_self).integrableOn_Icc
  have hGcrude_nonneg : ∀ n t, 0 ≤ C_b * Real.sqrt M
      * (1 + viscousFormSq_R3 1 ((galSeq (alPkg.φ n)).u t : L2VF_R3)) * S := by
    intro n t
    refine mul_nonneg (mul_nonneg (mul_nonneg hC_b0 (Real.sqrt_nonneg _)) ?_) hS0
    have := viscousFormSq_R3_nonneg zero_le_one ((galSeq (alPkg.φ n)).u t : L2VF_R3)
    linarith
  have hGcrude_int : ∀ n, Integrable (fun t => C_b * Real.sqrt M
      * (1 + viscousFormSq_R3 1 ((galSeq (alPkg.φ n)).u t : L2VF_R3)) * S)
      (restrictAvgMeasure T) := by
    intro n
    exact (((integrable_const (1 : ℝ)).add (hV1_int n)).const_mul (C_b * Real.sqrt M)).mul_const S
  have hV1_reg : ∀ n, ∫ t, viscousFormSq_R3 1 ((galSeq (alPkg.φ n)).u t : L2VF_R3)
        ∂(restrictAvgMeasure T)
      ≤ ν⁻¹ * ((1 / 2 : ℝ) * M ^ 2) := by
    intro n
    have hrb := (galSeq (alPkg.φ n)).reg_bound T hT
    have hscale : ∀ s, viscousFormSq_R3 ν ((galSeq (alPkg.φ n)).u s : L2VF_R3)
        = ν * viscousFormSq_R3 1 ((galSeq (alPkg.φ n)).u s : L2VF_R3) := by
      intro s; rw [viscousFormSq_R3_eq_smul, smul_eq_mul]
    rw [intervalIntegral.integral_congr (g := fun s => ν * viscousFormSq_R3 1
        ((galSeq (alPkg.φ n)).u s : L2VF_R3)) (fun s _ => hscale s),
      intervalIntegral.integral_const_mul,
      intervalIntegral_eq_restrictAvgMeasure_integral T hT.le] at hrb
    rw [hMdef]; rwa [le_inv_mul_iff₀ hν]
  have hMuUniv : ((restrictAvgMeasure T) Set.univ).toReal = T := restrictAvgMeasure_univ_toReal T hT
  have hGcrude_int_bound : ∀ n, ∫ t, C_b * Real.sqrt M
      * (1 + viscousFormSq_R3 1 ((galSeq (alPkg.φ n)).u t : L2VF_R3)) * S ∂(restrictAvgMeasure T)
      ≤ (C_b * Real.sqrt M * (T + ν⁻¹ * ((1 / 2 : ℝ) * M ^ 2))) * S := by
    intro n
    have heq : ∫ t, C_b * Real.sqrt M
        * (1 + viscousFormSq_R3 1 ((galSeq (alPkg.φ n)).u t : L2VF_R3)) * S ∂(restrictAvgMeasure T)
        = C_b * Real.sqrt M * S
            * (∫ t, (1 + viscousFormSq_R3 1 ((galSeq (alPkg.φ n)).u t : L2VF_R3))
                ∂(restrictAvgMeasure T)) := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      ring
    rw [heq]
    have hintadd : ∫ t, (1 + viscousFormSq_R3 1 ((galSeq (alPkg.φ n)).u t : L2VF_R3))
          ∂(restrictAvgMeasure T)
        = T + ∫ t, viscousFormSq_R3 1 ((galSeq (alPkg.φ n)).u t : L2VF_R3)
            ∂(restrictAvgMeasure T) := by
      rw [integral_add (integrable_const 1) (hV1_int n), integral_const, measureReal_def,
        hMuUniv, smul_eq_mul, mul_one]
    rw [hintadd]
    have hnn : (0 : ℝ) ≤ C_b * Real.sqrt M * S :=
      mul_nonneg (mul_nonneg hC_b0 (Real.sqrt_nonneg _)) hS0
    have hcap := hV1_reg n
    calc C_b * Real.sqrt M * S
            * (T + ∫ t, viscousFormSq_R3 1 ((galSeq (alPkg.φ n)).u t : L2VF_R3)
                ∂(restrictAvgMeasure T))
        ≤ C_b * Real.sqrt M * S * (T + ν⁻¹ * ((1 / 2 : ℝ) * M ^ 2)) := by
          refine mul_le_mul_of_nonneg_left ?_ hnn
          linarith [hcap]
      _ = (C_b * Real.sqrt M * (T + ν⁻¹ * ((1 / 2 : ℝ) * M ^ 2))) * S := by ring
  exact ⟨hFb_crude, hGcrude_nonneg, hGcrude_int, hGcrude_int_bound⟩

/-- **W2 nonlinear-limit convection bound (PR-4).** For any Schwartz divergence-free test
`z`, the limit-curve convection functional `t ↦ F.b (u t) (u t) z` is integrable on `[0,T]`
and its `L¹`-norm is controlled by `√(V₁ z)`, with a `z`-uniform constant `K`.

The bound descends from the Galerkin curves via `fb_tendsto_of_perball` + Fatou-in-time
(`lintegral_liminf_le'`): each approximant obeys the Ladyzhenskaya energy bound
`|b(uₙ,uₙ,z)| ≤ C_b‖uₙ‖^{1/2}(V₁ uₙ)^{3/4}√(V₁ z)` (`convIntegralSchwartz_bound_energy` +
`F.b_galerkin`), whose time integral is `n`-uniformly `≤ K·√(V₁ z)` after the crude
`‖uₙ‖^{1/2}(V₁ uₙ)^{3/4} ≤ √‖u₀‖·(1 + V₁ uₙ)` domination and `reg_bound`. -/
private theorem bForm_limit_convection_bound
    (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T)
    (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n)
    (alPkg : AubinLionsPackage_R3 𝔊 F ν T u₀ galSeq) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z : L2Sigma_R3, IsSchwartzDivFree_R3 z →
      Integrable (fun t => F.b (alPkg.u t) (alPkg.u t) z)
          (volume.restrict (Set.Icc (0 : ℝ) T)) ∧
      ∫ t, ‖F.b (alPkg.u t) (alPkg.u t) z‖ ∂(volume.restrict (Set.Icc (0 : ℝ) T))
          ≤ K * Real.sqrt (viscousFormSq_R3 1 (z : L2VF_R3)) := by
  classical
  set μ : Measure ℝ := restrictAvgMeasure T with hμ
  haveI hμfin : IsFiniteMeasure μ := by rw [hμ]; exact isFiniteMeasure_restrictAvgMeasure T
  set M : ℝ := ‖(u₀ : L2VF_R3)‖ with hMdef
  have hM0 : 0 ≤ M := norm_nonneg _
  have hbridge : ∀ g : ℝ → ℝ, ∫ t in (0 : ℝ)..T, g t = ∫ t, g t ∂μ := fun g => by
    rw [hμ]; exact intervalIntegral_eq_restrictAvgMeasure_integral T hT.le g
  have hae_ge : ∀ᵐ t ∂μ, (0 : ℝ) ≤ t := by rw [hμ]; exact ae_zero_le_of_restrictAvgMeasure T
  obtain ⟨C_b, hC_b0, hC_b⟩ := convIntegralSchwartz_bound_energy
  set K : ℝ := C_b * Real.sqrt M * (T + ν⁻¹ * ((1 / 2 : ℝ) * M ^ 2)) with hKdef
  have hK0 : 0 ≤ K := by
    rw [hKdef]
    refine mul_nonneg (mul_nonneg hC_b0 (Real.sqrt_nonneg _)) ?_
    exact add_nonneg hT.le (mul_nonneg (inv_nonneg.2 hν.le) (by positivity))
  refine ⟨K, hK0, ?_⟩
  intro z hz
  obtain ⟨ψz, hψz⟩ := hz
  set S : ℝ := Real.sqrt (viscousFormSq_R3 1 (z : L2VF_R3)) with hS
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  -- a.e.-in-time facts about the limit curve.
  have hballconv : ∀ᵐ t ∂μ, ∀ k : ℕ,
      Filter.Tendsto (fun n => restrictToBall (k : ℝ) ((galSeq (alPkg.φ n)).u t : L2VF_R3))
        Filter.atTop (nhds (restrictToBall (k : ℝ) (alPkg.u t : L2VF_R3))) := by
    rw [hμ]; exact ae_all_iff.2 fun k => alPkg.strong_convergence_ae k
  have hnorm_ulim : ∀ᵐ t ∂μ, ‖(alPkg.u t : L2VF_R3)‖ ≤ M := by
    rw [hμ]
    filter_upwards [kineticEnergy_lsc_bound 𝔊 F ν T u₀ galSeq alPkg] with t ht
    have hsq : ‖(alPkg.u t : L2VF_R3)‖ ^ 2 ≤ M ^ 2 := by rw [hMdef]; nlinarith [ht]
    exact le_of_sq_le_sq hsq hM0
  have haetend : ∀ᵐ t ∂μ, Filter.Tendsto
      (fun n => F.b ((galSeq (alPkg.φ n)).u t) ((galSeq (alPkg.φ n)).u t) z) Filter.atTop
      (nhds (F.b (alPkg.u t) (alPkg.u t) z)) := by
    filter_upwards [hae_ge, hnorm_ulim, hballconv] with t htg hnorm hball
    have hbd : ∀ n, ‖((galSeq (alPkg.φ n)).u t : L2VF_R3)‖ ≤ M := fun n => by
      rw [hMdef]; exact galerkin_norm_le_u0 𝔊 F ν u₀ (alPkg.φ n) (galSeq (alPkg.φ n)) htg
    exact fb_tendsto_of_perball F z ⟨ψz, hψz⟩ (fun n => (galSeq (alPkg.φ n)).u t) (alPkg.u t)
      M hM0 hbd hnorm hball
  -- Per-level crude bound `|b(uₙ,uₙ,z)| ≤ C_b·√M·(1 + V₁ uₙ)·S` on forward time.
  have hFb_crude_pt : ∀ n t, 0 ≤ t →
      |F.b ((galSeq (alPkg.φ n)).u t) ((galSeq (alPkg.φ n)).u t) z|
        ≤ C_b * Real.sqrt M
            * (1 + viscousFormSq_R3 1 ((galSeq (alPkg.φ n)).u t : L2VF_R3)) * S := by
    intro n t ht
    obtain ⟨ψu, hψu0⟩ := 𝔊.range_schwartz (alPkg.φ n) ((galSeq (alPkg.φ n)).u t : L2VF_R3)
    have hψu : ∀ j : Fin 3, L2VF_projComponent_R3 j ((galSeq (alPkg.φ n)).u t : L2VF_R3)
        = (ψu j).toLp 2 (volume : Measure Domain3) := by
      intro j; rw [(galSeq (alPkg.φ n)).u_inVn t]; exact hψu0 j
    have hmix : |F.b ((galSeq (alPkg.φ n)).u t) ((galSeq (alPkg.φ n)).u t) z|
        ≤ C_b * ‖((galSeq (alPkg.φ n)).u t : L2VF_R3)‖ ^ (1 / 2 : ℝ)
            * (viscousFormSq_R3 1 ((galSeq (alPkg.φ n)).u t : L2VF_R3)) ^ (1 / 4 : ℝ)
            * Real.sqrt (viscousFormSq_R3 1 ((galSeq (alPkg.φ n)).u t : L2VF_R3)) * S := by
      rw [F.b_galerkin ψu ψu ψz ((galSeq (alPkg.φ n)).u t) ((galSeq (alPkg.φ n)).u t) z
        hψu hψu hψz]
      exact hC_b _ _ _ ψu ψu ψz hψu hψu hψz
    refine hmix.trans ?_
    set V : ℝ := viscousFormSq_R3 1 ((galSeq (alPkg.φ n)).u t : L2VF_R3) with hV
    have hV0 : 0 ≤ V := viscousFormSq_R3_nonneg zero_le_one _
    have h1 : ‖((galSeq (alPkg.φ n)).u t : L2VF_R3)‖ ^ (1 / 2 : ℝ) ≤ Real.sqrt M := by
      rw [Real.sqrt_eq_rpow]
      refine Real.rpow_le_rpow (norm_nonneg _) ?_ (by norm_num)
      rw [hMdef]; exact galerkin_norm_le_u0 𝔊 F ν u₀ (alPkg.φ n) (galSeq (alPkg.φ n)) ht
    have h2 : V ^ (1 / 4 : ℝ) * Real.sqrt V ≤ 1 + V := rpow_quarter_mul_sqrt_le_R3 V hV0
    calc C_b * ‖((galSeq (alPkg.φ n)).u t : L2VF_R3)‖ ^ (1 / 2 : ℝ)
            * V ^ (1 / 4 : ℝ) * Real.sqrt V * S
        = (C_b * S)
            * (‖((galSeq (alPkg.φ n)).u t : L2VF_R3)‖ ^ (1 / 2 : ℝ) * (V ^ (1 / 4 : ℝ) * Real.sqrt V)) := by
          ring
      _ ≤ (C_b * S) * (Real.sqrt M * (1 + V)) := by
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC_b0 hS0)
          exact mul_le_mul h1 h2 (mul_nonneg (Real.rpow_nonneg hV0 _) (Real.sqrt_nonneg _))
            (Real.sqrt_nonneg _)
      _ = C_b * Real.sqrt M * (1 + V) * S := by ring
  -- Integrability/nonnegativity/`n`-uniform integral cap for the crude dominator, via the
  -- shared step lemma (both are consumed twice below: once for `hlint_n`'s Fatou setup, once
  -- for the final `K·S` cap).
  obtain ⟨hFb_crude, hGcrude_nonneg, hGcrude_int, hGcrude_int_bound⟩ :=
    bForm_galerkin_crude_dominator_bound 𝔊 F ν hν T hT u₀ galSeq alPkg z C_b hC_b0 hFb_crude_pt
  -- Measurability of the approximant and limit integrands.
  have hFb_meas_n : ∀ n, AEStronglyMeasurable
      (fun t => F.b ((galSeq (alPkg.φ n)).u t) ((galSeq (alPkg.φ n)).u t) z) μ := by
    intro n; rw [hμ]
    exact ((bForm_curve_continuousOn_of_schwartz (galSeq (alPkg.φ n)) z ⟨ψz, hψz⟩).mono
      Set.Icc_subset_Ici_self).aestronglyMeasurable measurableSet_Icc
  have hFb_meas : AEStronglyMeasurable (fun t => F.b (alPkg.u t) (alPkg.u t) z) μ :=
    aestronglyMeasurable_of_tendsto_ae Filter.atTop hFb_meas_n haetend
  -- Per-`n` `ENNReal` cap.
  have hlint_n : ∀ n,
      ∫⁻ t, ENNReal.ofReal ‖F.b ((galSeq (alPkg.φ n)).u t) ((galSeq (alPkg.φ n)).u t) z‖ ∂μ
        ≤ ENNReal.ofReal (K * S) := by
    intro n
    calc ∫⁻ t, ENNReal.ofReal ‖F.b ((galSeq (alPkg.φ n)).u t) ((galSeq (alPkg.φ n)).u t) z‖ ∂μ
        ≤ ∫⁻ t, ENNReal.ofReal (C_b * Real.sqrt M
            * (1 + viscousFormSq_R3 1 ((galSeq (alPkg.φ n)).u t : L2VF_R3)) * S) ∂μ := by
          refine lintegral_mono_ae ?_
          filter_upwards [hFb_crude n] with t ht
          exact ENNReal.ofReal_le_ofReal ht
      _ = ENNReal.ofReal (∫ t, C_b * Real.sqrt M
            * (1 + viscousFormSq_R3 1 ((galSeq (alPkg.φ n)).u t : L2VF_R3)) * S ∂μ) :=
          (ofReal_integral_eq_lintegral_ofReal (hGcrude_int n)
            (Filter.Eventually.of_forall (hGcrude_nonneg n))).symm
      _ ≤ ENNReal.ofReal (K * S) := ENNReal.ofReal_le_ofReal (hGcrude_int_bound n)
  -- Fatou passage to the limit curve.
  have hlim_lint : ∫⁻ t, ENNReal.ofReal ‖F.b (alPkg.u t) (alPkg.u t) z‖ ∂μ
      ≤ ENNReal.ofReal (K * S) := by
    calc ∫⁻ t, ENNReal.ofReal ‖F.b (alPkg.u t) (alPkg.u t) z‖ ∂μ
        = ∫⁻ t, Filter.atTop.liminf
            (fun n => ENNReal.ofReal ‖F.b ((galSeq (alPkg.φ n)).u t)
              ((galSeq (alPkg.φ n)).u t) z‖) ∂μ := by
          refine lintegral_congr_ae ?_
          filter_upwards [haetend] with t ht
          have htn : Filter.Tendsto
              (fun n => ENNReal.ofReal ‖F.b ((galSeq (alPkg.φ n)).u t)
                ((galSeq (alPkg.φ n)).u t) z‖) Filter.atTop
              (nhds (ENNReal.ofReal ‖F.b (alPkg.u t) (alPkg.u t) z‖)) :=
            (ENNReal.continuous_ofReal.tendsto _).comp ht.norm
          exact htn.liminf_eq.symm
      _ ≤ Filter.atTop.liminf (fun n => ∫⁻ t,
            ENNReal.ofReal ‖F.b ((galSeq (alPkg.φ n)).u t) ((galSeq (alPkg.φ n)).u t) z‖ ∂μ) :=
          lintegral_liminf_le' (fun n => (hFb_meas_n n).norm.aemeasurable.ennreal_ofReal)
      _ ≤ ENNReal.ofReal (K * S) := by
          refine le_trans liminf_le_limsup ?_
          exact limsup_le_of_le isCobounded_le_of_bot (Filter.Eventually.of_forall hlint_n)
  -- Integrability of the norm (hence of `F.b`) and the real-integral bound.
  have hNormInt : Integrable (fun t => ‖F.b (alPkg.u t) (alPkg.u t) z‖) μ := by
    refine ⟨hFb_meas.norm, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun t => norm_nonneg _)]
    exact lt_of_le_of_lt hlim_lint ENNReal.ofReal_lt_top
  have hInt : Integrable (fun t => F.b (alPkg.u t) (alPkg.u t) z) μ :=
    (integrable_norm_iff hFb_meas).mp hNormInt
  refine ⟨hInt, ?_⟩
  have hofeq : ENNReal.ofReal (∫ t, ‖F.b (alPkg.u t) (alPkg.u t) z‖ ∂μ)
      = ∫⁻ t, ENNReal.ofReal ‖F.b (alPkg.u t) (alPkg.u t) z‖ ∂μ :=
    ofReal_integral_eq_lintegral_ofReal hNormInt
      (Filter.Eventually.of_forall fun t => norm_nonneg _)
  have hnnKS : (0 : ℝ) ≤ K * S := mul_nonneg hK0 hS0
  have := hofeq ▸ hlim_lint
  rwa [ENNReal.ofReal_le_ofReal_iff hnnKS] at this

/-- **Integrability of the abstract weak-form integrand `G y` (W2 step 1).** For any Schwartz
divergence-free test `y`, the integrand
`t ↦ -⟪u t, y⟫·ψ'(t) + ψ(t)·(ν·stokesTestPairing_R3 (u t) y + F.b (u t) (u t) y)`
is integrable on `[0,T]`: the kinetic term is dominated by `M‖y‖Mψ'` (via `hnorm_ulim`), and the
viscous+convection term is a bounded (`|ψ| ≤ Mψ`) multiple of an integrable sum — the viscous half
via the fixed Riesz vector `vElt` with `stokesTestPairing_R3 x y = ⟪vElt, x⟫`, the convection half
via `hKb` (`bForm_limit_convection_bound`). -/
private theorem weakFormNS_limit_G_integrable
    (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊) (ν : ℝ) (T : ℝ)
    (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n)
    (alPkg : AubinLionsPackage_R3 𝔊 F ν T u₀ galSeq)
    (ψ : ℝ → ℝ) (hψC1 : ContDiff ℝ 1 ψ)
    (M Mψ Mψ' : ℝ) (hMψ0 : 0 ≤ Mψ) (hMψ'0 : 0 ≤ Mψ')
    (hMψ : ∀ t ∈ Set.Icc (0 : ℝ) T, ‖ψ t‖ ≤ Mψ)
    (hMψ' : ∀ t ∈ Set.Icc (0 : ℝ) T, ‖deriv ψ t‖ ≤ Mψ')
    (hu_meas : AEStronglyMeasurable (fun t => (alPkg.u t : L2VF_R3)) (restrictAvgMeasure T))
    (hnorm_ulim : ∀ᵐ t ∂(restrictAvgMeasure T), ‖(alPkg.u t : L2VF_R3)‖ ≤ M)
    (hae_Icc : ∀ᵐ t ∂(restrictAvgMeasure T), t ∈ Set.Icc (0 : ℝ) T)
    (Kb : ℝ)
    (hKb : ∀ z : L2Sigma_R3, IsSchwartzDivFree_R3 z →
      Integrable (fun t => F.b (alPkg.u t) (alPkg.u t) z) (restrictAvgMeasure T) ∧
      ∫ t, ‖F.b (alPkg.u t) (alPkg.u t) z‖ ∂(restrictAvgMeasure T)
          ≤ Kb * Real.sqrt (viscousFormSq_R3 1 (z : L2VF_R3))) :
    ∀ y : L2Sigma_R3, IsSchwartzDivFree_R3 y →
      Integrable (fun t => -(inner (𝕜 := ℝ) (alPkg.u t : L2VF_R3) (y : L2VF_R3)) * deriv ψ t
        + ψ t * (ν * stokesTestPairing_R3 (alPkg.u t : L2VF_R3) (y : L2VF_R3)
          + F.b (alPkg.u t) (alPkg.u t) y)) (restrictAvgMeasure T) := by
  haveI : IsFiniteMeasure (restrictAvgMeasure T) := isFiniteMeasure_restrictAvgMeasure T
  intro y hy
  obtain ⟨ψy, hψy⟩ := hy
  -- Fixed viscous Riesz vector: `stokesTestPairing_R3 x y = ⟪vElt, x⟫`.
  obtain ⟨E, hE⟩ : ∃ E : Fin 3 → Lp ℝ 2 (volume : Measure Domain3),
      ∀ x : L2VF_R3, stokesTestPairing_R3 x (y : L2VF_R3)
        = ∑ j : Fin 3, inner (𝕜 := ℝ) (L2VF_projComponent_R3 j x) (E j) :=
    ⟨_, fun x => stokesTestPairing_R3_eq_sum_inner_negLap x (y : L2VF_R3) ψy hψy⟩
  set vElt : L2VF_R3 := ∑ j : Fin 3, (L2VF_projComponent_R3 j).adjoint (E j) with hvElt
  have hstok_inner : ∀ x : L2VF_R3,
      stokesTestPairing_R3 x (y : L2VF_R3) = inner (𝕜 := ℝ) vElt x := by
    intro x
    rw [hE x, hvElt, sum_inner]
    exact Finset.sum_congr rfl fun j _ => by
      rw [ContinuousLinearMap.adjoint_inner_left]; exact real_inner_comm _ _
  have hi1 : Integrable
      (fun t => -(inner (𝕜 := ℝ) (alPkg.u t : L2VF_R3) (y : L2VF_R3)) * deriv ψ t)
        (restrictAvgMeasure T) := by
    refine Integrable.mono' (g := fun _ => M * ‖(y : L2VF_R3)‖ * Mψ') (integrable_const _)
      (((hu_meas.inner aestronglyMeasurable_const).neg).mul
        hψC1.continuous_deriv_one.aestronglyMeasurable) ?_
    filter_upwards [hnorm_ulim, hae_Icc] with t hn htI
    rw [Real.norm_eq_abs, abs_mul, abs_neg]
    have hψ'b : |deriv ψ t| ≤ Mψ' := by rw [← Real.norm_eq_abs]; exact hMψ' t htI
    calc |inner (𝕜 := ℝ) (alPkg.u t : L2VF_R3) (y : L2VF_R3)| * |deriv ψ t|
        ≤ (‖(alPkg.u t : L2VF_R3)‖ * ‖(y : L2VF_R3)‖) * Mψ' :=
          mul_le_mul (abs_real_inner_le_norm _ _) hψ'b (abs_nonneg _)
            (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ ≤ M * ‖(y : L2VF_R3)‖ * Mψ' := by gcongr
  have hinner_v_int : Integrable (fun t => inner (𝕜 := ℝ) vElt (alPkg.u t : L2VF_R3))
      (restrictAvgMeasure T) := by
    refine Integrable.mono' (integrable_const (‖vElt‖ * M))
      (aestronglyMeasurable_const.inner hu_meas) ?_
    filter_upwards [hnorm_ulim] with t hn
    rw [Real.norm_eq_abs]
    exact (abs_real_inner_le_norm _ _).trans (by gcongr)
  have hrest : Integrable (fun t => ψ t * (ν * stokesTestPairing_R3 (alPkg.u t : L2VF_R3)
      (y : L2VF_R3) + F.b (alPkg.u t) (alPkg.u t) y)) (restrictAvgMeasure T) := by
    refine Integrable.bdd_mul (c := Mψ) ?_ hψC1.continuous.aestronglyMeasurable ?_
    · simp_rw [hstok_inner]
      exact (hinner_v_int.const_mul ν).add (hKb y ⟨ψy, hψy⟩).1
    · filter_upwards [hae_Icc] with t htI
      exact hMψ t htI
  exact hi1.add hrest

/-- **The `Φ`-difference bound `|Φ(z)| ≤ A‖z‖ + B√V₁(z)` (W2 step 2).** For any Schwartz
divergence-free test `z`, the weak-form functional `Φ(z) = ∫₀ᵀ G z` is controlled by
`A := M·Mψ'·T` on the kinetic slot (`abs_real_inner_le_norm`) and `B := Mψ·ν·(T+ν⁻¹·½M²) + Mψ·Kb`
on the viscous+convection slot (`stokesTestPairing_abs_le` + `hKb`), via the pointwise a.e. norm
bound on `G z t` integrated against the dominating function. This is the difference-bound step
consumed by the vanishing-squeeze argument (`hRHS0`/`hmain`) in `weakFormNS_limit_passage`. -/
private theorem weakFormNS_limit_diff_bound
    (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊) (ν : ℝ) (hν : 0 < ν) (T : ℝ)
    (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n)
    (alPkg : AubinLionsPackage_R3 𝔊 F ν T u₀ galSeq)
    (ψ : ℝ → ℝ) (M Mψ Mψ' : ℝ) (hMψ0 : 0 ≤ Mψ) (hMψ'0 : 0 ≤ Mψ')
    (hMψ : ∀ t ∈ Set.Icc (0 : ℝ) T, ‖ψ t‖ ≤ Mψ)
    (hMψ' : ∀ t ∈ Set.Icc (0 : ℝ) T, ‖deriv ψ t‖ ≤ Mψ')
    (hnorm_ulim : ∀ᵐ t ∂(restrictAvgMeasure T), ‖(alPkg.u t : L2VF_R3)‖ ≤ M)
    (hmemH1_u : ∀ᵐ t ∂(restrictAvgMeasure T), memH1VF_R3 (alPkg.u t : L2VF_R3))
    (hae_Icc : ∀ᵐ t ∂(restrictAvgMeasure T), t ∈ Set.Icc (0 : ℝ) T)
    (hMuUniv : ((restrictAvgMeasure T) Set.univ).toReal = T)
    (hsqrtV1u_int : Integrable
      (fun t => Real.sqrt (viscousFormSq_R3 1 (alPkg.u t : L2VF_R3))) (restrictAvgMeasure T))
    (hsqrtV1u_bound : ∫ t, Real.sqrt (viscousFormSq_R3 1 (alPkg.u t : L2VF_R3))
        ∂(restrictAvgMeasure T) ≤ T + ν⁻¹ * ((1 / 2 : ℝ) * M ^ 2))
    (Kb : ℝ)
    (hKb : ∀ z : L2Sigma_R3, IsSchwartzDivFree_R3 z →
      Integrable (fun t => F.b (alPkg.u t) (alPkg.u t) z) (restrictAvgMeasure T) ∧
      ∫ t, ‖F.b (alPkg.u t) (alPkg.u t) z‖ ∂(restrictAvgMeasure T)
          ≤ Kb * Real.sqrt (viscousFormSq_R3 1 (z : L2VF_R3)))
    (hGint : ∀ y : L2Sigma_R3, IsSchwartzDivFree_R3 y →
      Integrable (fun t => -(inner (𝕜 := ℝ) (alPkg.u t : L2VF_R3) (y : L2VF_R3)) * deriv ψ t
        + ψ t * (ν * stokesTestPairing_R3 (alPkg.u t : L2VF_R3) (y : L2VF_R3)
          + F.b (alPkg.u t) (alPkg.u t) y)) (restrictAvgMeasure T)) :
    ∀ z : L2Sigma_R3, IsSchwartzDivFree_R3 z →
      |∫ t, (-(inner (𝕜 := ℝ) (alPkg.u t : L2VF_R3) (z : L2VF_R3)) * deriv ψ t
          + ψ t * (ν * stokesTestPairing_R3 (alPkg.u t : L2VF_R3) (z : L2VF_R3)
            + F.b (alPkg.u t) (alPkg.u t) z)) ∂(restrictAvgMeasure T)|
        ≤ (M * Mψ' * T) * ‖(z : L2VF_R3)‖
          + (Mψ * ν * (T + ν⁻¹ * ((1 / 2 : ℝ) * M ^ 2)) + Mψ * Kb)
              * Real.sqrt (viscousFormSq_R3 1 (z : L2VF_R3)) := by
  haveI : IsFiniteMeasure (restrictAvgMeasure T) := isFiniteMeasure_restrictAvgMeasure T
  intro z hz
  obtain ⟨ψz, hψz⟩ := hz
  have hzH1 : memH1VF_R3 (z : L2VF_R3) := memH1VF_R3_of_isSchwartzDivFree ⟨ψz, hψz⟩
  set S : ℝ := Real.sqrt (viscousFormSq_R3 1 (z : L2VF_R3)) with hS
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hGz_int := hGint z ⟨ψz, hψz⟩
  have hb_int : Integrable (fun t => F.b (alPkg.u t) (alPkg.u t) z) (restrictAvgMeasure T) :=
    (hKb z ⟨ψz, hψz⟩).1
  -- Pointwise a.e. bound on the integrand norm.
  have hDbound : ∀ᵐ t ∂(restrictAvgMeasure T),
      ‖-(inner (𝕜 := ℝ) (alPkg.u t : L2VF_R3) (z : L2VF_R3)) * deriv ψ t
          + ψ t * (ν * stokesTestPairing_R3 (alPkg.u t : L2VF_R3) (z : L2VF_R3)
            + F.b (alPkg.u t) (alPkg.u t) z)‖
        ≤ M * ‖(z : L2VF_R3)‖ * Mψ'
          + Mψ * ν * (Real.sqrt (viscousFormSq_R3 1 (alPkg.u t : L2VF_R3)) * S)
          + Mψ * ‖F.b (alPkg.u t) (alPkg.u t) z‖ := by
    filter_upwards [hnorm_ulim, hmemH1_u, hae_Icc] with t hn hmemu htI
    have hψb : |ψ t| ≤ Mψ := by rw [← Real.norm_eq_abs]; exact hMψ t htI
    have hψ'b : |deriv ψ t| ≤ Mψ' := by rw [← Real.norm_eq_abs]; exact hMψ' t htI
    have hkin : ‖-(inner (𝕜 := ℝ) (alPkg.u t : L2VF_R3) (z : L2VF_R3)) * deriv ψ t‖
        ≤ M * ‖(z : L2VF_R3)‖ * Mψ' := by
      rw [Real.norm_eq_abs, abs_mul, abs_neg]
      calc |inner (𝕜 := ℝ) (alPkg.u t : L2VF_R3) (z : L2VF_R3)| * |deriv ψ t|
          ≤ (‖(alPkg.u t : L2VF_R3)‖ * ‖(z : L2VF_R3)‖) * Mψ' :=
            mul_le_mul (abs_real_inner_le_norm _ _) hψ'b (abs_nonneg _)
              (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        _ ≤ M * ‖(z : L2VF_R3)‖ * Mψ' := by gcongr
    have hstok_le : |stokesTestPairing_R3 (alPkg.u t : L2VF_R3) (z : L2VF_R3)|
        ≤ Real.sqrt (viscousFormSq_R3 1 (alPkg.u t : L2VF_R3)) * S :=
      stokesTestPairing_abs_le (alPkg.u t : L2VF_R3) (z : L2VF_R3) hmemu hzH1
    have hrest_le : ‖ψ t * (ν * stokesTestPairing_R3 (alPkg.u t : L2VF_R3) (z : L2VF_R3)
        + F.b (alPkg.u t) (alPkg.u t) z)‖
        ≤ Mψ * ν * (Real.sqrt (viscousFormSq_R3 1 (alPkg.u t : L2VF_R3)) * S)
          + Mψ * ‖F.b (alPkg.u t) (alPkg.u t) z‖ := by
      rw [Real.norm_eq_abs, abs_mul]
      calc |ψ t| * |ν * stokesTestPairing_R3 (alPkg.u t : L2VF_R3) (z : L2VF_R3)
              + F.b (alPkg.u t) (alPkg.u t) z|
          ≤ Mψ * (ν * (Real.sqrt (viscousFormSq_R3 1 (alPkg.u t : L2VF_R3)) * S)
              + ‖F.b (alPkg.u t) (alPkg.u t) z‖) := by
            refine mul_le_mul hψb ?_ (abs_nonneg _) hMψ0
            refine (abs_add_le _ _).trans ?_
            rw [abs_mul, abs_of_nonneg hν.le, Real.norm_eq_abs]
            exact add_le_add (mul_le_mul_of_nonneg_left hstok_le hν.le) le_rfl
        _ = Mψ * ν * (Real.sqrt (viscousFormSq_R3 1 (alPkg.u t : L2VF_R3)) * S)
              + Mψ * ‖F.b (alPkg.u t) (alPkg.u t) z‖ := by ring
    calc ‖-(inner (𝕜 := ℝ) (alPkg.u t : L2VF_R3) (z : L2VF_R3)) * deriv ψ t
            + ψ t * (ν * stokesTestPairing_R3 (alPkg.u t : L2VF_R3) (z : L2VF_R3)
              + F.b (alPkg.u t) (alPkg.u t) z)‖
        ≤ ‖-(inner (𝕜 := ℝ) (alPkg.u t : L2VF_R3) (z : L2VF_R3)) * deriv ψ t‖
          + ‖ψ t * (ν * stokesTestPairing_R3 (alPkg.u t : L2VF_R3) (z : L2VF_R3)
              + F.b (alPkg.u t) (alPkg.u t) z)‖ := norm_add_le _ _
      _ ≤ M * ‖(z : L2VF_R3)‖ * Mψ'
            + Mψ * ν * (Real.sqrt (viscousFormSq_R3 1 (alPkg.u t : L2VF_R3)) * S)
            + Mψ * ‖F.b (alPkg.u t) (alPkg.u t) z‖ := by
          have := add_le_add hkin hrest_le; linarith
  -- The dominating function is integrable, with a closed-form integral bound.
  have hDom_int : Integrable (fun t => M * ‖(z : L2VF_R3)‖ * Mψ'
      + Mψ * ν * (Real.sqrt (viscousFormSq_R3 1 (alPkg.u t : L2VF_R3)) * S)
      + Mψ * ‖F.b (alPkg.u t) (alPkg.u t) z‖) (restrictAvgMeasure T) := by
    refine ((integrable_const _).add ?_).add (hb_int.norm.const_mul Mψ)
    exact (hsqrtV1u_int.mul_const S).const_mul (Mψ * ν)
  have hmid_int : Integrable (fun t => Mψ * ν
      * (Real.sqrt (viscousFormSq_R3 1 (alPkg.u t : L2VF_R3)) * S)) (restrictAvgMeasure T) :=
    (hsqrtV1u_int.mul_const S).const_mul (Mψ * ν)
  have hconv_int : Integrable (fun t => Mψ * ‖F.b (alPkg.u t) (alPkg.u t) z‖)
      (restrictAvgMeasure T) := hb_int.norm.const_mul Mψ
  have hsplit1 : ∫ t, (M * ‖(z : L2VF_R3)‖ * Mψ'
        + Mψ * ν * (Real.sqrt (viscousFormSq_R3 1 (alPkg.u t : L2VF_R3)) * S)
        + Mψ * ‖F.b (alPkg.u t) (alPkg.u t) z‖) ∂(restrictAvgMeasure T)
      = (∫ t, (M * ‖(z : L2VF_R3)‖ * Mψ'
          + Mψ * ν * (Real.sqrt (viscousFormSq_R3 1 (alPkg.u t : L2VF_R3)) * S))
            ∂(restrictAvgMeasure T))
        + (∫ t, Mψ * ‖F.b (alPkg.u t) (alPkg.u t) z‖ ∂(restrictAvgMeasure T)) :=
    integral_add ((integrable_const (M * ‖(z : L2VF_R3)‖ * Mψ')).add hmid_int) hconv_int
  have hsplit2 : ∫ t, (M * ‖(z : L2VF_R3)‖ * Mψ'
        + Mψ * ν * (Real.sqrt (viscousFormSq_R3 1 (alPkg.u t : L2VF_R3)) * S))
          ∂(restrictAvgMeasure T)
      = (∫ t, (M * ‖(z : L2VF_R3)‖ * Mψ' : ℝ) ∂(restrictAvgMeasure T))
        + (∫ t, Mψ * ν * (Real.sqrt (viscousFormSq_R3 1 (alPkg.u t : L2VF_R3)) * S)
            ∂(restrictAvgMeasure T)) :=
    integral_add (integrable_const (M * ‖(z : L2VF_R3)‖ * Mψ')) hmid_int
  have e1 : ∫ t, (M * ‖(z : L2VF_R3)‖ * Mψ' : ℝ) ∂(restrictAvgMeasure T)
      = M * ‖(z : L2VF_R3)‖ * Mψ' * T := by
    rw [integral_const, measureReal_def, hMuUniv, smul_eq_mul, mul_comm]
  have e2 : ∫ t, Mψ * ν * (Real.sqrt (viscousFormSq_R3 1 (alPkg.u t : L2VF_R3)) * S)
        ∂(restrictAvgMeasure T)
      = Mψ * ν * ((∫ t, Real.sqrt (viscousFormSq_R3 1 (alPkg.u t : L2VF_R3))
          ∂(restrictAvgMeasure T)) * S) := by
    rw [integral_const_mul, integral_mul_const]
  have e3 : ∫ t, Mψ * ‖F.b (alPkg.u t) (alPkg.u t) z‖ ∂(restrictAvgMeasure T)
      = Mψ * (∫ t, ‖F.b (alPkg.u t) (alPkg.u t) z‖ ∂(restrictAvgMeasure T)) :=
    integral_const_mul _ _
  calc |∫ t, (-(inner (𝕜 := ℝ) (alPkg.u t : L2VF_R3) (z : L2VF_R3)) * deriv ψ t
          + ψ t * (ν * stokesTestPairing_R3 (alPkg.u t : L2VF_R3) (z : L2VF_R3)
            + F.b (alPkg.u t) (alPkg.u t) z)) ∂(restrictAvgMeasure T)|
      = ‖∫ t, (-(inner (𝕜 := ℝ) (alPkg.u t : L2VF_R3) (z : L2VF_R3)) * deriv ψ t
          + ψ t * (ν * stokesTestPairing_R3 (alPkg.u t : L2VF_R3) (z : L2VF_R3)
            + F.b (alPkg.u t) (alPkg.u t) z)) ∂(restrictAvgMeasure T)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ t, ‖-(inner (𝕜 := ℝ) (alPkg.u t : L2VF_R3) (z : L2VF_R3)) * deriv ψ t
          + ψ t * (ν * stokesTestPairing_R3 (alPkg.u t : L2VF_R3) (z : L2VF_R3)
            + F.b (alPkg.u t) (alPkg.u t) z)‖ ∂(restrictAvgMeasure T) :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ t, (M * ‖(z : L2VF_R3)‖ * Mψ'
          + Mψ * ν * (Real.sqrt (viscousFormSq_R3 1 (alPkg.u t : L2VF_R3)) * S)
          + Mψ * ‖F.b (alPkg.u t) (alPkg.u t) z‖) ∂(restrictAvgMeasure T) :=
        integral_mono_ae hGz_int.norm hDom_int hDbound
    _ ≤ (M * Mψ' * T) * ‖(z : L2VF_R3)‖
          + (Mψ * ν * (T + ν⁻¹ * ((1 / 2 : ℝ) * M ^ 2)) + Mψ * Kb) * S := by
        rw [hsplit1, hsplit2, e1, e2, e3]
        have hb2 := (hKb z ⟨ψz, hψz⟩).2
        have hqv : Mψ * ν * ((∫ t, Real.sqrt (viscousFormSq_R3 1 (alPkg.u t : L2VF_R3))
              ∂(restrictAvgMeasure T)) * S)
            ≤ Mψ * ν * ((T + ν⁻¹ * ((1 / 2 : ℝ) * M ^ 2)) * S) := by
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hMψ0 hν.le)
          exact mul_le_mul_of_nonneg_right hsqrtV1u_bound hS0
        have hqc : Mψ * (∫ t, ‖F.b (alPkg.u t) (alPkg.u t) z‖ ∂(restrictAvgMeasure T))
            ≤ Mψ * (Kb * S) := mul_le_mul_of_nonneg_left hb2 hMψ0
        nlinarith [hqv, hqc, hMψ0, hν.le, hS0]

set_option maxHeartbeats 400000 in
/-- **WeakFormNS limit passage (conjunct 2 of `galerkin_limit_passage_R3`).**

The Aubin–Lions limit curve `alPkg.u` satisfies the distributional Navier–Stokes weak equation
`WeakFormNS ν T (r3Evolution 𝔊 F) alPkg.u`.  This is exactly the second conjunct of the
`galerkin_limit_passage_R3` axiom (taking the good representative `u := alPkg.u`), and the
`weak_eq_limit` field of `GalerkinCompactnessPackageFull_R3`.

The W2 test-extension proof (issue #4 PR-4) threads `htest : R3TestApproxH1 𝔊` to approximate
the arbitrary Schwartz test by Galerkin tests in the `L² + √V₁` graph seminorm, then squeezes
the difference of the weak-form functionals via `bForm_limit_convection_bound` (nonlinear),
`stokesTestPairing_abs_le` (viscous), and `abs_real_inner_le_norm` (kinetic). -/
theorem weakFormNS_limit_passage
    (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T)
    (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n)
    (alPkg : AubinLionsPackage_R3 𝔊 F ν T u₀ galSeq)
    (htest : R3TestApproxH1 𝔊) : -- (htest used in proof, PR-4)
    WeakFormNS ν T (r3Evolution 𝔊 F) alPkg.u := by
  -- Unfold `WeakFormNS` (the `r3Evolution` evolution: `viscousForm = stokesTestPairing_R3`,
  -- `convForm = F.b`, `isTest = IsSchwartzDivFree_R3`).  Intro the admissible test data.
  intro ψ hψcs hψsupp hψC1 w hw
  -- `hw : IsSchwartzDivFree_R3 w` (the `r3Evolution.isTest` field).  The integrand to be shown to
  -- integrate to `0` over `[0,T]` is, with the `r3Evolution` fields substituted,
  --   `-(⟪alPkg.u t, w⟫) · ψ'(t) + ψ(t) · (ν · stokesTestPairing_R3 (alPkg.u t) w
  --       + F.b (alPkg.u t) (alPkg.u t) w)`.
  -- Strategy (W2): the abstract test functional `Φ(y) := ∫₀ᵀ [integrand with test y]` vanishes on
  -- every Galerkin test (`weakFormNS_galerkinTest_limit`, W1).  By right-linearity of the three
  -- slots, `Φ(w) = Φ(vₖ) + Φ(w - vₖ) = Φ(w - vₖ)` for any Galerkin test `vₖ`, and `htest` supplies
  -- `vₖ` with `‖vₖ - w‖ + √V₁(vₖ - w) → 0`.  The difference `|Φ(w - vₖ)|` is bounded by
  -- `A‖vₖ - w‖ + B√V₁(vₖ - w)` (kinetic via `abs_real_inner_le_norm`, viscous via
  -- `stokesTestPairing_abs_le`, nonlinear via `bForm_limit_convection_bound`), so `Φ(w) = 0`.
  classical
  set μ : Measure ℝ := restrictAvgMeasure T with hμ
  haveI hμfin : IsFiniteMeasure μ := by rw [hμ]; exact isFiniteMeasure_restrictAvgMeasure T
  have hbridge : ∀ g : ℝ → ℝ, ∫ t in (0 : ℝ)..T, g t = ∫ t, g t ∂μ := fun g => by
    rw [hμ]; exact intervalIntegral_eq_restrictAvgMeasure_integral T hT.le g
  have hMuUniv : (μ Set.univ).toReal = T := by rw [hμ]; exact restrictAvgMeasure_univ_toReal T hT
  set M : ℝ := ‖(u₀ : L2VF_R3)‖ with hMdef
  have hM0 : 0 ≤ M := norm_nonneg _
  obtain ⟨Mψ, hMψ⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    hψC1.continuous.continuousOn
  obtain ⟨Mψ', hMψ'⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    hψC1.continuous_deriv_one.continuousOn
  have hMψ0 : 0 ≤ Mψ := le_trans (norm_nonneg _) (hMψ 0 ⟨le_refl 0, hT.le⟩)
  have hMψ'0 : 0 ≤ Mψ' := le_trans (norm_nonneg _) (hMψ' 0 ⟨le_refl 0, hT.le⟩)
  -- Measurability and a.e.-in-time facts about the limit curve.
  have hu_meas : AEStronglyMeasurable (fun t => (alPkg.u t : L2VF_R3)) μ := by
    rw [hμ]; exact alPkg.u_aestronglyMeasurable
  have hae_Icc : ∀ᵐ t ∂μ, t ∈ Set.Icc (0 : ℝ) T := by rw [hμ]; exact ae_restrict_mem measurableSet_Icc
  have hnorm_ulim : ∀ᵐ t ∂μ, ‖(alPkg.u t : L2VF_R3)‖ ≤ M := by
    rw [hμ]
    filter_upwards [kineticEnergy_lsc_bound 𝔊 F ν T u₀ galSeq alPkg] with t ht
    have hsq : ‖(alPkg.u t : L2VF_R3)‖ ^ 2 ≤ M ^ 2 := by rw [hMdef]; nlinarith [ht]
    exact le_of_sq_le_sq hsq hM0
  obtain ⟨hmemH1_u, hVν_ii, hVν_bound⟩ := viscous_lsc_under_strongL2 𝔊 F ν hν T hT u₀ galSeq alPkg
  obtain ⟨Kb, hKb0, hKb⟩ := bForm_limit_convection_bound 𝔊 F ν hν T hT u₀ galSeq alPkg
  -- `V₁(u ·)` is integrable on `[0,T]` and its integral is `≤ ν⁻¹·½‖u₀‖²`; hence so is `√V₁(u ·)`.
  have hVν_int : Integrable (fun t => viscousFormSq_R3 ν (alPkg.u t : L2VF_R3)) μ := by
    have h := (intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).mp hVν_ii
    show Integrable (fun t => viscousFormSq_R3 ν (alPkg.u t : L2VF_R3))
      (volume.restrict (Set.Icc (0 : ℝ) T))
    rw [Measure.restrict_congr_set Ioc_ae_eq_Icc.symm]; exact h
  have hV1u_int : Integrable (fun t => viscousFormSq_R3 1 (alPkg.u t : L2VF_R3)) μ := by
    have h2 : Integrable (fun t => ν⁻¹ * viscousFormSq_R3 ν (alPkg.u t : L2VF_R3)) μ :=
      hVν_int.const_mul _
    refine h2.congr (Filter.Eventually.of_forall fun t => ?_)
    show ν⁻¹ * viscousFormSq_R3 ν (alPkg.u t : L2VF_R3) = viscousFormSq_R3 1 (alPkg.u t : L2VF_R3)
    rw [viscousFormSq_R3_eq_smul, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hν.ne', one_mul]
  have hV1u_intbound : ∫ t, viscousFormSq_R3 1 (alPkg.u t : L2VF_R3) ∂μ
      ≤ ν⁻¹ * ((1 / 2 : ℝ) * M ^ 2) := by
    have hb := hVν_bound
    rw [intervalIntegral.integral_congr (g := fun s => ν * viscousFormSq_R3 1
        (alPkg.u s : L2VF_R3)) (fun s _ => by rw [viscousFormSq_R3_eq_smul, smul_eq_mul]),
      intervalIntegral.integral_const_mul, hbridge] at hb
    rw [hMdef]; rwa [le_inv_mul_iff₀ hν]
  have hsqrtV1u_meas : AEStronglyMeasurable
      (fun t => Real.sqrt (viscousFormSq_R3 1 (alPkg.u t : L2VF_R3))) μ :=
    Real.continuous_sqrt.comp_aestronglyMeasurable
      (viscousFormSq_aestronglyMeasurable_of_memH1 alPkg hmemH1_u)
  have hsqrtV1u_int : Integrable
      (fun t => Real.sqrt (viscousFormSq_R3 1 (alPkg.u t : L2VF_R3))) μ := by
    refine Integrable.mono' ((integrable_const (1 : ℝ)).add hV1u_int) hsqrtV1u_meas ?_
    filter_upwards with t
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact sqrt_le_one_add_self_R3 _ (viscousFormSq_R3_nonneg zero_le_one _)
  have hsqrtV1u_bound : ∫ t, Real.sqrt (viscousFormSq_R3 1 (alPkg.u t : L2VF_R3)) ∂μ
      ≤ T + ν⁻¹ * ((1 / 2 : ℝ) * M ^ 2) := by
    calc ∫ t, Real.sqrt (viscousFormSq_R3 1 (alPkg.u t : L2VF_R3)) ∂μ
        ≤ ∫ t, (1 + viscousFormSq_R3 1 (alPkg.u t : L2VF_R3)) ∂μ :=
          integral_mono_ae hsqrtV1u_int ((integrable_const 1).add hV1u_int)
            (Filter.Eventually.of_forall fun t =>
              sqrt_le_one_add_self_R3 _ (viscousFormSq_R3_nonneg zero_le_one _))
      _ = T + ∫ t, viscousFormSq_R3 1 (alPkg.u t : L2VF_R3) ∂μ := by
          rw [integral_add (integrable_const 1) hV1u_int, integral_const, measureReal_def,
            hMuUniv, smul_eq_mul, mul_one]
      _ ≤ T + ν⁻¹ * ((1 / 2 : ℝ) * M ^ 2) := by linarith [hV1u_intbound]
  -- The abstract weak-form integrand as a function of the test slot `y`.
  set G : L2Sigma_R3 → ℝ → ℝ := fun y t =>
    -(inner (𝕜 := ℝ) (alPkg.u t : L2VF_R3) (y : L2VF_R3)) * deriv ψ t
      + ψ t * (ν * stokesTestPairing_R3 (alPkg.u t : L2VF_R3) (y : L2VF_R3)
        + F.b (alPkg.u t) (alPkg.u t) y) with hG
  -- Integrability of `G y` for any Schwartz div-free test `y`.
  have hGint : ∀ y : L2Sigma_R3, IsSchwartzDivFree_R3 y → Integrable (G y) μ := by
    have := weakFormNS_limit_G_integrable 𝔊 F ν T u₀ galSeq alPkg ψ hψC1 M Mψ Mψ' hMψ0 hMψ'0
      hMψ hMψ' hu_meas hnorm_ulim hae_Icc Kb hKb
    intro y hy; rw [hG]; exact this y hy
  -- Galerkin tests: `Φ(v) = 0` (W1, converted to the `μ`-integral).
  have hΦgal : ∀ v : L2Sigma_R3, IsGalerkinTest_R3 𝔊 v → ∫ t, G v t ∂μ = 0 := by
    intro v hv
    rw [← hbridge (G v)]
    exact weakFormNS_galerkinTest_limit 𝔊 F ν hν T hT u₀ galSeq alPkg v hv ψ hψcs hψsupp hψC1
  have hwH1 : memH1VF_R3 (w : L2VF_R3) := memH1VF_R3_of_isSchwartzDivFree hw
  -- Right-slot additivity: `G v t = G w t + G (v - w) t` at a.e. `t` (where `u t ∈ H¹`).
  have hGsub_pt : ∀ v : L2Sigma_R3, IsSchwartzDivFree_R3 v → ∀ t,
      memH1VF_R3 (alPkg.u t : L2VF_R3) → G v t - G w t = G (v - w) t := by
    intro v hv t hmemu
    have hvH1 : memH1VF_R3 (v : L2VF_R3) := memH1VF_R3_of_isSchwartzDivFree hv
    simp only [hG]
    have hcoe : ((v - w : L2Sigma_R3) : L2VF_R3) = (v : L2VF_R3) - (w : L2VF_R3) := by
      rw [Submodule.coe_sub]
    rw [hcoe, inner_sub_right,
      stokesTestPairing_R3_sub_right (alPkg.u t : L2VF_R3) (v : L2VF_R3) (w : L2VF_R3) hmemu hvH1 hwH1,
      bForm_R3_sub_3 F (alPkg.u t) (alPkg.u t) v w]
    ring
  -- The difference bound `|Φ(z)| ≤ A‖z‖ + B√V₁(z)`.
  set A : ℝ := M * Mψ' * T with hAdef
  set B : ℝ := Mψ * ν * (T + ν⁻¹ * ((1 / 2 : ℝ) * M ^ 2)) + Mψ * Kb with hBdef
  have hA0 : 0 ≤ A := by rw [hAdef]; positivity
  have hB0 : 0 ≤ B := by
    rw [hBdef]
    refine add_nonneg (mul_nonneg (mul_nonneg hMψ0 hν.le) ?_) (mul_nonneg hMψ0 hKb0)
    exact add_nonneg hT.le (mul_nonneg (inv_nonneg.2 hν.le) (by positivity))
  have hDiffBound : ∀ z : L2Sigma_R3, IsSchwartzDivFree_R3 z →
      |∫ t, G z t ∂μ| ≤ A * ‖(z : L2VF_R3)‖ + B * Real.sqrt (viscousFormSq_R3 1 (z : L2VF_R3)) := by
    have hdb := weakFormNS_limit_diff_bound 𝔊 F ν hν T u₀ galSeq alPkg ψ M Mψ Mψ' hMψ0 hMψ'0
      hMψ hMψ' hnorm_ulim hmemH1_u hae_Icc hMuUniv hsqrtV1u_int hsqrtV1u_bound Kb hKb hGint
    intro z hz; rw [hG]; exact hdb z hz
  -- The vanishing bound sequence.
  have hRHS0 : Filter.Tendsto (fun k : ℕ => A * (1 / (k + 1)) + B * Real.sqrt (1 / (k + 1)))
      Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun k : ℕ => (1 : ℝ) / (k + 1)) Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hA : Filter.Tendsto (fun k : ℕ => A * (1 / (k + 1))) Filter.atTop (nhds 0) := by
      have := h1.const_mul A; rwa [mul_zero] at this
    have hB : Filter.Tendsto (fun k : ℕ => B * Real.sqrt (1 / (k + 1))) Filter.atTop (nhds 0) := by
      have h2 : Filter.Tendsto (fun k : ℕ => Real.sqrt (1 / (k + 1))) Filter.atTop (nhds 0) := by
        have hc : Filter.Tendsto (fun k : ℕ => Real.sqrt (1 / (k + 1))) Filter.atTop
            (nhds (Real.sqrt 0)) := (Real.continuous_sqrt.tendsto 0).comp h1
        rwa [Real.sqrt_zero] at hc
      have := h2.const_mul B; rwa [mul_zero] at this
    have := hA.add hB; rwa [add_zero] at this
  -- Conclude `Φ(w) = 0` by squeezing the difference bound.
  have hmain : ∫ t, G w t ∂μ = 0 := by
    have hle0 : |∫ t, G w t ∂μ| ≤ 0 := by
      refine ge_of_tendsto hRHS0 (Filter.eventually_atTop.2 ⟨0, fun k _ => ?_⟩)
      obtain ⟨v, hv_gal, hv_sdf, hv_norm, hv_visc⟩ :=
        htest w hw (1 / (k + 1)) (by positivity)
      have hsplit : ∫ t, G v t ∂μ = ∫ t, G w t ∂μ + ∫ t, G (v - w) t ∂μ := by
        rw [← integral_add (hGint w hw) (hGint (v - w) (isSchwartzDivFree_R3_sub v w hv_sdf hw))]
        refine integral_congr_ae ?_
        filter_upwards [hmemH1_u] with t hmemu
        have := hGsub_pt v hv_sdf t hmemu
        linarith [this]
      have hGw_eq : ∫ t, G w t ∂μ = -(∫ t, G (v - w) t ∂μ) := by
        rw [hΦgal v hv_gal] at hsplit; linarith
      rw [hGw_eq, abs_neg]
      refine (hDiffBound (v - w) (isSchwartzDivFree_R3_sub v w hv_sdf hw)).trans ?_
      have hnormle : ‖((v - w : L2Sigma_R3) : L2VF_R3)‖ ≤ 1 / (k + 1) := by
        rw [Submodule.coe_sub]; exact hv_norm.le
      have hviscle : viscousFormSq_R3 1 ((v - w : L2Sigma_R3) : L2VF_R3) ≤ 1 / (k + 1) := by
        rw [Submodule.coe_sub]; exact hv_visc.le
      have hsqrtle : Real.sqrt (viscousFormSq_R3 1 ((v - w : L2Sigma_R3) : L2VF_R3))
          ≤ Real.sqrt (1 / (k + 1)) := Real.sqrt_le_sqrt hviscle
      exact add_le_add (mul_le_mul_of_nonneg_left hnormle hA0)
        (mul_le_mul_of_nonneg_left hsqrtle hB0)
    exact abs_nonpos_iff.mp hle0
  -- Convert the `WeakFormNS` goal (`L2Sigma` inner) to the `G`-form and finish.
  rw [← hbridge (G w)] at hmain
  refine Eq.trans ?_ hmain
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [hG, Submodule.coe_inner]

/-! ### Tier C — combination: spatial + time ⇒ `AubinLionsPackage_R3` (the centerpiece) -/

set_option maxHeartbeats 800000 in
/-- **Aubin–Lions package on ℝ³ from the isolated time-compactness input (CLOSED).**

Produces `aubin_lions_R3`'s conclusion (`AubinLionsPackage_R3`), conditional on P3's local
spatial compactness (via `LocalRellichInput`).  The time-compactness extraction is supplied
UNCONDITIONALLY by `galerkinSpaceTimeExtraction_R3` (no separate `TimeCompactnessInput` modulus
hypothesis — it is absorbed into that single axiom).  The conclusion type is exactly
`AubinLionsPackage_R3 𝔊 F ν T u₀ galSeq` (matching the `aubin_lions_R3` binder list,
`SolutionInterfaces.lean:444–460`).

ASSEMBLY: the genuine spatial half is PROVED axiom-free (the `steklovAvg_spatial_extraction`
chain). The single irreducible LOCAL Bochner-time compactness extraction (one subsequence `φ` + a
measurable limit curve `u` with per-ball `restrictToBall R` a.e.-in-time `L²` convergence) is
supplied by `galerkinSpaceTimeExtraction_R3` (theorem, issue #44, proved; resting on the two
thinner axioms `galerkin_spacetime_precompact_R3` + `galerkin_weakLimit_R3` — local, no tightness,
no global-`L²` claim, genuinely weaker/thinner than `aubin_lions_R3`). From that
extraction this constructor assembles every field axiom-free:
* `φ`, `φ_mono`, `u` — directly from the extraction;
* `u_aestronglyMeasurable` — the extraction's measurability conjunct;
* `strong_convergence` — for each ball `R`, the extraction already delivers the per-ball
  ball-restricted differences converging to `0` a.e. in `t`, dominated by the constant
  `2‖u₀‖` on the finite window `[0,T]` (via `galerkin_norm_le_u0`); dominated convergence in `L²`
  (`tendsto_Lp_of_tendsto_ae`) gives the `eLpNorm`-in-time convergence.

This is a `noncomputable def` (not a `theorem`) because `AubinLionsPackage_R3` is a `Type`
(a data-carrying structure), not a `Prop` — mirroring the `aubin_lions_R3` axiom shape. -/
noncomputable def aubinLionsPackage_R3_of_timeCompactness
    (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T)
    (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n)
    (B : LocalRellichInput) :
    AubinLionsPackage_R3 𝔊 F ν T u₀ galSeq := by
  classical
  -- The isolated LOCAL Bochner-time extraction: one subsequence `φ` + a measurable limit curve `u`
  -- with per-ball (`restrictToBall R`) a.e.-in-time `L²` convergence.
  -- The axiom is a `Prop`-existential but the goal `AubinLionsPackage_R3` is a `Type` (a
  -- structure), so the existential witnesses are extracted via `Exists.choose`/`.choose_spec`
  -- (large elimination through `Classical.choice`) rather than `obtain`/`cases`.
  have hex := galerkinSpaceTimeExtraction_R3 𝔊 F ν hν T hT u₀ galSeq B
  set φ : ℕ → ℕ := hex.choose
  set u : Time → L2Sigma_R3 := hex.choose_spec.choose
  have hφ : StrictMono φ := hex.choose_spec.choose_spec.1
  have hmeas : AEStronglyMeasurable (fun t => (u t : L2VF_R3))
      (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)) :=
    hex.choose_spec.choose_spec.2.1
  -- LOCAL (per-ball) a.e.-in-time convergence: for each radius `R`, the ball restrictions
  -- `restrictToBall R (uₙ t)` converge to `restrictToBall R (u t)` a.e. in `t`.  This is the
  -- honest content available on ℝ³ — only local compactness (no tightness), so NO global
  -- `L2VF_R3`-norm a.e. convergence is claimed.
  have hae : ∀ R : ℝ, ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)),
      Filter.Tendsto (fun n => restrictToBall R ((galSeq (φ n)).u t : L2VF_R3)) Filter.atTop
        (nhds (restrictToBall R (u t : L2VF_R3))) :=
    hex.choose_spec.choose_spec.2.2
  refine
    { φ := φ
      φ_mono := hφ
      u := u
      u_aestronglyMeasurable := hmeas
      strong_convergence := ?_
      strong_convergence_ae := hae }
  -- `strong_convergence`: for each ball `R`, the ball-restricted differences converge to `0`
  -- in `L²(0,T)` by dominated convergence (constant dominator `2‖u₀‖` on the finite window).
  intro R
  set μ : Measure ℝ := MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T) with hμ
  haveI : IsFiniteMeasure μ := by
    rw [hμ]; exact ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc]; exact ENNReal.ofReal_lt_top⟩
  -- the two ball-restricted curves, as functions of time
  set fSeq : ℕ → ℝ → L2ballR3 R :=
    fun n t => restrictToBall R ((galSeq (φ n)).u t : L2VF_R3) with hfSeq
  set g : ℝ → L2ballR3 R := fun t => restrictToBall R (u t : L2VF_R3) with hg
  -- continuity (hence strong-measurability) of each `fSeq n` on `Ici 0 ⊇ Icc 0 T`
  have hcont_curve : ∀ m : ℕ, ContinuousOn (fun t => ((galSeq m).u t : L2VF_R3)) (Set.Ici 0) :=
    fun m => galerkin_curve_continuous 𝔊 F ν u₀ m (galSeq m)
  have hAESM_f : ∀ n, AEStronglyMeasurable (fSeq n) μ := by
    intro n
    rw [hμ]
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Icc
    refine (continuous_restrictToBall R).comp_continuousOn ?_
    exact (hcont_curve (φ n)).mono (by intro t ht; exact ht.1)
  -- `g` is a.e.-strongly-measurable (restrictToBall continuous ∘ measurable `u`)
  have hAESM_g : AEStronglyMeasurable g μ :=
    (continuous_restrictToBall R).comp_aestronglyMeasurable hmeas
  -- a.e.-in-`t` convergence of the ball restrictions — this is exactly the axiom's per-ball
  -- conjunct at radius `R` (`fSeq n t = restrictToBall R (uₙ t)`, `g t = restrictToBall R (u t)`).
  have hae_ball : ∀ᵐ t ∂μ, Filter.Tendsto (fun n => fSeq n t) Filter.atTop (nhds (g t)) := by
    rw [hμ, hfSeq, hg]; exact hae R
  -- uniform pointwise bound `‖fSeq n t‖ ≤ ‖u₀‖` on `[0,T]`
  have hbound : ∀ n, ∀ᵐ t ∂μ, ‖fSeq n t‖ ≤ ‖(u₀ : L2VF_R3)‖ := by
    intro n
    rw [hμ]
    refine (ae_restrict_iff' measurableSet_Icc).mpr (ae_of_all _ (fun t ht => ?_))
    refine le_trans (norm_restrictToBall_le R _) ?_
    exact galerkin_norm_le_u0 𝔊 F ν u₀ (φ n) (galSeq (φ n)) ht.1
  -- `g ∈ MemLp 2 μ`: a.e.-bounded by the constant `‖u₀‖` on the finite measure.
  have hMemLp_g : MemLp g 2 μ := by
    -- `‖g t‖ ≤ ‖u₀‖` a.e. by norm-lsc through the per-ball a.e. limit `hae_ball`: `g t` is the
    -- limit of `fSeq n t` and each `‖fSeq n t‖ ≤ ‖u₀‖` (`hbound`).  No global `‖u t‖`-bound is
    -- used, so this works directly from the LOCAL per-ball convergence.
    have hgbd : ∀ᵐ t ∂μ, ‖g t‖ ≤ ‖(u₀ : L2VF_R3)‖ := by
      filter_upwards [hae_ball, ae_all_iff.mpr hbound] with t ht hbnd_t
      exact le_of_tendsto' ht.norm hbnd_t
    exact MemLp.of_bound hAESM_g _ hgbd
  -- `UnifIntegrable fSeq 2 μ`: from the uniform a.e. bound ‖fSeq n t‖ ≤ ‖u₀‖.
  -- For each ε > 0, pick δ so that for small-measure sets s, the indicator eLpNorm ≤ ε.
  -- Since ‖fSeq n t‖ ≤ ‖u₀‖ a.e., the indicator over s has eLpNorm ≤ ‖u₀‖ · μ(s)^(1/2)
  -- (Cauchy–Schwarz / eLpNorm_le_of_ae_bound), which is small when μ(s) is small.
  have hui : MeasureTheory.UnifIntegrable fSeq 2 μ := by
    intro ε hε
    -- bound on indicator eLpNorm from a.e. pointwise bound
    -- `eLpNorm (s.indicator (fSeq n)) 2 μ ≤ eLpNorm_le_of_ae_bound (‖u₀‖) + ...`
    -- Use MemLp.eLpNorm_indicator_le on the constant function ‖u₀‖ ∈ MemLp 2 μ
    -- then show the indicator eLpNorm is ≤ that of the constant.
    have hC_memLp : MemLp (fun _ : ℝ => ‖(u₀ : L2VF_R3)‖) 2 μ := memLp_const _
    obtain ⟨δ, hδpos, hδ⟩ := hC_memLp.eLpNorm_indicator_le one_le_two (by norm_num) hε
    refine ⟨δ, hδpos, fun n s hs hμs => ?_⟩
    -- bound eLpNorm (s.indicator (fSeq n)) ≤ eLpNorm (s.indicator (fun _ => ‖u₀‖))
    have hle : eLpNorm (s.indicator (fSeq n)) 2 μ
        ≤ eLpNorm (s.indicator (fun _ : ℝ => ‖(u₀ : L2VF_R3)‖)) 2 μ := by
      apply eLpNorm_mono_ae
      filter_upwards [hbound n] with t ht
      simp only [Set.indicator_apply]
      split_ifs
      · simpa using ht
      · simp
    exact le_trans hle (hδ s hs hμs)
  -- `UnifTight fSeq 2 μ`: on a finite measure, take s = univ (sᶜ = ∅, indicator = 0).
  have hut : MeasureTheory.UnifTight fSeq 2 μ := by
    intro ε _hε
    refine ⟨Set.univ, ?_, fun n => ?_⟩
    · exact measure_ne_top μ Set.univ
    · simp
  have := MeasureTheory.tendsto_Lp_of_tendsto_ae (μ := μ) (p := 2) one_le_two
    (by norm_num) hAESM_f hMemLp_g hui hut hae_ball
  -- convert `eLpNorm (fSeq n - g)` to the goal's pointwise-difference form
  refine this.congr (fun n => ?_)
  congr 1

end LerayHopf
