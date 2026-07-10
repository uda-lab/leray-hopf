/-
# LerayHopf.R3.ViscousWeakLsc — Tier E: energy inequality (kinetic + viscous halves)

**Split off `R3.AubinLionsLimitPassage.lean` (issue #114 Tier 1, commit 1).** Verbatim move of
the former "Tier E" super-section: "Tier E — energy inequality" (kinetic-lsc half),
"Tier E-prep — ball-restriction plumbing", and "Tier E (viscous half)" (module docstring lines
~230–1249 as of the split); no statement, proof, or namespace changed — only the file location
(and one visibility change, see below). Module paths are not yet a stable public API pre-release
(issue #109 set the precedent of clean moves without shims), so no compatibility alias is kept.

**Why the kinetic half moved too, despite the plan's boundary being just the viscous half:**
the viscous-half theorems (`viscous_pointwise_lsc`, `viscous_lsc_under_strongL2`,
`liminf_viscousFormSq_lt_top_ae`) call `galerkin_norm_le_u0` and `kineticEnergy_lsc_bound`
directly — both defined in the kinetic-half section. `AubinLionsLimitPassage.lean` also needs
both pervasively elsewhere (well beyond the moved viscous section), so leaving them behind would
force `AubinLionsLimitPassage.lean` to import this file while this file also needed to import
`AubinLionsLimitPassage.lean` back — a cycle. Moving the whole "Tier E" super-section here
(kinetic half included) is the only clean fix; `AubinLionsLimitPassage.lean` gets both back via
`import LerayHopf.R3.ViscousWeakLsc`.

**One visibility change:** `viscousFormSq_aestronglyMeasurable_of_memH1` was `private`
in the source file but is called from `AubinLionsLimitPassage.lean`'s remainder — made public
here (its statement is unchanged).

This file discharges the pointwise viscous lsc wall via the **Fourier–Plancherel** route,
entirely inside `L²` (a bundled Hilbert space here), avoiding any H¹ Hilbert type, sequential
Banach–Alaoglu, or convex-functional weak-lsc. The chain: full-sequence weak-L² convergence
`uₙ(t) ⇀ u(t)` a.e. `t` (from `strong_convergence_ae` + the ball-tail ε/3 argument) ⟹ push through
the bounded truncated Fourier multiplier (a CLM) ⟹ norm-weak-lsc of the L²-norm (inner-product
trick) ⟹ MCT in the truncation level recovers the full Dirichlet seminorm ⟹ `viscous_pointwise_lsc`
/ `viscous_lsc_under_strongL2`, the deliverables consumed by `AubinLionsLimitPassage.lean`.

## Assumptions

No `axiom`/`opaque`/`constant`/`unsafe` in this file.
-/

import LerayHopf.R3.SolutionInterfaces   -- R3GalerkinScheme, R3NSForms, GalerkinSolutionData_R3,
                                          -- AubinLionsPackage_R3 (theorem-signature types;
                                          -- unavoidable per the split audit)
import LerayHopf.R3.SpatialCompactness   -- restrictToBall, L2ballR3, continuous_restrictToBall,
                                          -- norm_restrictToBall_le, tendsto_normSq_restrictToBall
import LerayHopf.R3.GalerkinODE          -- viscousFormSq_R3_eq_smul
import LerayHopf.R3.FourierL2            -- 𝓕, L2C_R3, viscousFormSq_R3_eq_integral_normSq_fourier
import LerayHopf.R3.WeightedFourierCommute -- mulBdd bounded-multiplier commute + truncated weight
import LerayHopf.R3.SobolevEmbedding     -- memSobolev_of_finite_weightedFourier_R3 (H¹ from finite
                                          -- weighted-Fourier integral; the memH1 conjunct)
import LerayHopf.Bochner.TimeSobolev     -- Bochner.kineticEnergy_lsc_transfer

namespace LerayHopf

open MeasureTheory Filter Topology
open scoped FourierTransform

/-! ### Tier E — energy inequality (the reachable kinetic-lsc half of conclusion (c)) -/

/-- **Galerkin-side uniform energy bound (provable core of E1).** For every `n` and every
`t ≥ 0`, the Galerkin state is L²-bounded by the initial datum: `‖(galSeq n).u t‖ ≤ ‖u₀‖`.

Proof: `energy_bound` gives `½‖uₙ t‖² ≤ ½‖𝔊.P n u₀‖²`; `𝔊.norm_le` gives
`‖𝔊.P n u₀‖ ≤ ‖u₀‖`; combine. This is the side of E1 that needs no time-measurability. -/
theorem galerkin_norm_le_u0 (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (u₀ : L2Sigma_R3) (n : ℕ)
    (gs : GalerkinSolutionData_R3 𝔊 F ν u₀ n) {t : ℝ} (ht : 0 ≤ t) :
    ‖(gs.u t : L2VF_R3)‖ ≤ ‖(u₀ : L2VF_R3)‖ := by
  have hP : ‖𝔊.P n (u₀ : L2VF_R3)‖ ≤ ‖(u₀ : L2VF_R3)‖ := 𝔊.norm_le n (u₀ : L2VF_R3)
  have henergy := gs.energy_bound t ht
  -- `½‖uₙ t‖² ≤ ½‖P n u₀‖² ≤ ½‖u₀‖²`, so `‖uₙ t‖² ≤ ‖u₀‖²`, hence `‖uₙ t‖ ≤ ‖u₀‖`.
  have hsq : ‖(gs.u t : L2VF_R3)‖ ^ 2 ≤ ‖(u₀ : L2VF_R3)‖ ^ 2 := by
    have h2 : ‖𝔊.P n (u₀ : L2VF_R3)‖ ^ 2 ≤ ‖(u₀ : L2VF_R3)‖ ^ 2 := by
      have := mul_le_mul hP hP (norm_nonneg _) (norm_nonneg _)
      nlinarith [this]
    nlinarith [henergy, h2]
  exact le_of_sq_le_sq hsq (norm_nonneg _)

/-- The Galerkin velocity curve `t ↦ ((galSeq n).u t : L2VF_R3)` is continuous on **forward**
time `Set.Ici 0` (it is even differentiable there by `u_hasDeriv`).

Forward-only: `u_hasDeriv` now guarantees differentiability only for `t ≥ 0` (the curve is a
physical Galerkin solution, confined only on forward time).  Everything downstream uses the
curve only on `[0,T] ⊆ Ici 0`, so forward continuity suffices. -/
theorem galerkin_curve_continuous (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (u₀ : L2Sigma_R3) (n : ℕ)
    (gs : GalerkinSolutionData_R3 𝔊 F ν u₀ n) :
    ContinuousOn (fun s => (gs.u s : L2VF_R3)) (Set.Ici 0) :=
  fun t ht => (gs.u_hasDeriv t ht).continuousAt.continuousWithinAt

-- `eLpNorm_two_eq_ofReal_sqrt` (was private here) moved to
-- `LerayHopf.Analysis.PlancherelKernels` (issue #111 PR-2); no call site in this file
-- currently uses it (the docstring above mentioning it in the E1 proof route predates a
-- later refactor of that route), so no rewiring is needed beyond the deletion.

-- `kineticEnergyLscTransfer` (was a private re-derivation of
-- `Bochner.TimeSobolev.kineticEnergy_lsc_transfer`, same statement, different internal proof
-- route) is gone; this file now imports `Bochner.TimeSobolev` directly and uses the shared
-- version (issue #111 PR-3, verified acyclic:
-- TimeSobolev's transitive imports are GelfandTriple → EvolutionTriple → Torus.Basic/EnergyEstimate
-- + mathlib, none of which reach this file or its importers).

/-! ### Tier E-prep — ball-restriction plumbing for the a.e.-`t` norm-lsc transfer

The ball-restriction analysis the E1 transfer needs — `restrictToBall R` is `1`-Lipschitz
(hence continuous, so it transports time-measurability), its squared norm is the ball
set-integral of `‖·‖²`, and that ball set-integral increases to the full L²(ℝ³) norm-squared
as the radius exhausts `ℝ³` — now lives in `R3.SpatialCompactness` as public lemmas
(`restrictToBall_zero`, `restrictToBall_sub`, `restrictToBall_dist_le`,
`continuous_restrictToBall`, `normSq_restrictToBall_eq_setIntegral`,
`tendsto_normSq_restrictToBall`; issue #111 PR-3), imported here rather than re-derived. -/

/-- Lower-semicontinuity of the kinetic energy under the (local strong) L² limit, combined
with the uniform Galerkin energy bound, gives `½‖u t‖² ≤ ½‖u₀‖²` at the limit, A.E. IN TIME.

Honesty (no-smuggle, Codex Gate-1): the conclusion is A.E.-in-`t` over `[0,T]`, NOT `∀ t`.
`AubinLionsPackage_R3` supplies LOCAL space-time integral convergence, and (as of #14-C) also
`u_aestronglyMeasurable` (time-measurability of `t ↦ u t`). The measurability field enables
the a.e.-`t` norm-lsc transfer (E1 lean-prover target, #14-P). A `∀ t` bound would still
smuggle the GOOD-REPRESENTATIVE (pointwise-in-time) content — strong time-measurability is NOT
a pointwise representative. The a.e.-in-time bound is the honest derivable form; promoting it
to `∀ t` requires the good-representative frontier (weak-time-continuity / trace), which this
package deliberately does not carry. -/
theorem kineticEnergy_lsc_bound (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν T : ℝ) (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n)
    (alPkg : AubinLionsPackage_R3 𝔊 F ν T u₀ galSeq) :
    ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      (1 / 2 : ℝ) * ‖(alPkg.u t : L2VF_R3)‖ ^ 2 ≤ (1 / 2 : ℝ) * ‖(u₀ : L2VF_R3)‖ ^ 2 := by
  -- PROVABLE CORE (no time-measurability needed): the uniform Galerkin energy bound,
  -- `‖(galSeq n).u t‖ ≤ ‖u₀‖` for every `n` and `t ≥ 0` (`galerkin_norm_le_u0`). This is the
  -- only side of the kinetic-lsc inequality reachable from the data alone.
  have hgal : ∀ (n : ℕ) {t : ℝ}, 0 ≤ t →
      ‖((galSeq n).u t : L2VF_R3)‖ ≤ ‖(u₀ : L2VF_R3)‖ :=
    fun n {t} ht => galerkin_norm_le_u0 𝔊 F ν u₀ n (galSeq n) ht
  -- Degenerate window `T < 0`: `Icc 0 T = ∅`, so the a.e.-statement is vacuous.
  by_cases hT : 0 ≤ T
  · -- The time measure `μ = volume.restrict (Icc 0 T)` is finite (`Icc 0 T` bounded).
    set μ : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) T) with hμ
    haveI hμfin : IsFiniteMeasure μ := by
      rw [hμ]; refine isFiniteMeasure_restrict.2 ?_
      rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
    -- a.e. `t ∈ Icc 0 T`, in particular `0 ≤ t`.
    have hμ_ge : ∀ᵐ t ∂μ, 0 ≤ t := by
      rw [hμ]; refine ae_restrict_of_forall_mem measurableSet_Icc ?_; intro t ht; exact ht.1
    -- ════ For each integer radius `k`: the limit's ball restriction is L²-bounded by ‖u₀‖. ════
    -- This is the `Bochner.kineticEnergy_lsc_transfer` (norm-lsc) step, applied in `β = L2ballR3 k`, with
    --   f n := t ↦ restrictToBall k ((galSeq (alPkg.φ n)).u t),   g := t ↦ restrictToBall k (u t).
    have hperBall : ∀ k : ℕ,
        ∀ᵐ t ∂μ, ‖restrictToBall (k : ℝ) (alPkg.u t)‖ ≤ ‖(u₀ : L2VF_R3)‖ := by
      intro k
      set R : ℝ := (k : ℝ) with hR
      set f : ℕ → ℝ → L2ballR3 R :=
        fun n t => restrictToBall R ((galSeq (alPkg.φ n)).u t) with hf
      set g : ℝ → L2ballR3 R := fun t => restrictToBall R (alPkg.u t) with hg
      -- (1) `g` is a.e.-strongly measurable: `restrictToBall R` continuous ∘ `u` measurable.
      have hg_meas : AEStronglyMeasurable g μ := by
        simp only [hg]
        exact (continuous_restrictToBall R).comp_aestronglyMeasurable
          (by rw [hμ]; exact alPkg.u_aestronglyMeasurable)
      -- (2) each `f n` is a.e.-strongly measurable: galerkin curve continuous on `Ici 0 ⊇ Icc 0 T`.
      have hf_meas : ∀ n, AEStronglyMeasurable (f n) μ := by
        intro n
        have hcurve : ContinuousOn
            (fun t => ((galSeq (alPkg.φ n)).u t : L2VF_R3)) (Set.Icc (0 : ℝ) T) :=
          (galerkin_curve_continuous 𝔊 F ν u₀ (alPkg.φ n) (galSeq (alPkg.φ n))).mono
            (by intro t ht; exact ht.1)
        have hcurve_meas : AEStronglyMeasurable
            (fun t => ((galSeq (alPkg.φ n)).u t : L2VF_R3)) μ := by
          rw [hμ]; exact hcurve.aestronglyMeasurable measurableSet_Icc
        simp only [hf]
        exact (continuous_restrictToBall R).comp_aestronglyMeasurable hcurve_meas
      -- (3) the uniform a.e. bound `‖f n t‖ ≤ ‖u₀‖` (restriction ≤ global, then `hgal`).
      have hf_bound : ∀ n, ∀ᵐ t ∂μ, ‖f n t‖ ≤ ‖(u₀ : L2VF_R3)‖ := by
        intro n
        filter_upwards [hμ_ge] with t ht
        simp only [hf]
        calc ‖restrictToBall R ((galSeq (alPkg.φ n)).u t)‖
            ≤ ‖((galSeq (alPkg.φ n)).u t : L2VF_R3)‖ :=
              norm_restrictToBall_le R ((galSeq (alPkg.φ n)).u t)
          _ ≤ ‖(u₀ : L2VF_R3)‖ := hgal (alPkg.φ n) ht
      -- (4) the L²-in-time convergence `eLpNorm (f n - g) 2 μ → 0`. With `strong_convergence` now
      -- in its faithful `eLpNorm`-form (issue #31), this is EXACTLY the package field at radius
      -- `R = k`: `f n t = restrictToBall R ((galSeq (alPkg.φ n)).u t)` and
      -- `g t = restrictToBall R (alPkg.u t)`, and `μ = volume.restrict (Icc 0 T)`, so the field's
      -- conclusion is definitionally `hconv`.  This DISCHARGES the former `MemLp g`-gap `sorry`
      -- (the Bochner-form residual): the faithful field supplies the time-`L²` convergence directly,
      -- no time-integrability of a junk-`0`-collapsible integrand is needed.
      have hconv : Tendsto (fun n => eLpNorm (fun t => f n t - g t) 2 μ) atTop (𝓝 0) := by
        simpa only [hf, hg, hμ, hR] using alPkg.strong_convergence R
      -- (5) assemble: `kineticEnergy_lsc_transfer` gives the a.e. ball-restricted bound.
      exact Bochner.kineticEnergy_lsc_transfer hf_meas hg_meas hconv hf_bound
    -- ════ Combine over all radii `k`, then exhaust `R → ∞` to recover the full L²(ℝ³) bound. ════
    have hallBall : ∀ᵐ t ∂μ, ∀ k : ℕ,
        ‖restrictToBall (k : ℝ) (alPkg.u t)‖ ≤ ‖(u₀ : L2VF_R3)‖ :=
      ae_all_iff.2 hperBall
    filter_upwards [hallBall] with t ht
    -- `‖u t‖² = lim_k ‖restrictToBall k (u t)‖² ≤ ‖u₀‖²`, hence the kinetic bound.
    have hlim := tendsto_normSq_restrictToBall (alPkg.u t)
    have hboundSq : ∀ k : ℕ, ‖restrictToBall (k : ℝ) (alPkg.u t)‖ ^ 2 ≤ ‖(u₀ : L2VF_R3)‖ ^ 2 :=
      fun k => by
        have := ht k
        nlinarith [norm_nonneg (restrictToBall (k : ℝ) (alPkg.u t)), norm_nonneg (u₀ : L2VF_R3)]
    have huSq : ‖(alPkg.u t : L2VF_R3)‖ ^ 2 ≤ ‖(u₀ : L2VF_R3)‖ ^ 2 :=
      le_of_tendsto' hlim hboundSq
    nlinarith [huSq]
  · -- `T < 0`: the restricted measure is zero, so every a.e. statement holds.
    have hz : volume.restrict (Set.Icc (0 : ℝ) T) = 0 := by
      rw [Set.Icc_eq_empty hT, Measure.restrict_empty]
    rw [hz]
    simp

/-! ### Tier E (viscous half) — weak lower-semicontinuity of the dissipation

The pointwise viscous lsc wall is discharged via the **Fourier–Plancherel** route, entirely inside
`L²` (a bundled Hilbert space here), avoiding any H¹ Hilbert type, sequential Banach–Alaoglu, or
convex-functional weak-lsc.  The chain: full-sequence weak-L² convergence `uₙ(t) ⇀ u(t)` a.e. `t`
(from `strong_convergence_ae` + the ball-tail ε/3 argument) ⟹ push through the bounded truncated
Fourier multiplier (a CLM) ⟹ norm-weak-lsc of the L²-norm (inner-product trick) ⟹ MCT in the
truncation level recovers the full Dirichlet seminorm. -/

/-- The viscous-form curve `s ↦ viscousFormSq_R3 1 (gs.u s)` is continuous on `Ici 0`
(`= ∑_j ‖weightedFourierComponent (u s) j‖²`, a sum of norm² of the continuous weighted-Fourier
curves — the `viscous_curve_continuous` field). -/
theorem viscousFormSq_curve_continuousOn (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (u₀ : L2Sigma_R3) (n : ℕ) (gs : GalerkinSolutionData_R3 𝔊 F ν u₀ n) :
    ContinuousOn (fun s => viscousFormSq_R3 1 (gs.u s : L2VF_R3)) (Set.Ici (0 : ℝ)) := by
  have heq : ∀ s, viscousFormSq_R3 1 (gs.u s : L2VF_R3)
      = ∑ j : Fin 3, ‖weightedFourierComponent (gs.u s : L2VF_R3) (gs.reg_mem s) j‖ ^ 2 := by
    intro s
    rw [FourierL2.viscousFormSq_R3_eq_integral_normSq_fourier]
    exact Finset.sum_congr rfl
      (fun j _ => (norm_weightedFourierComponent_sq (gs.u s : L2VF_R3) (gs.reg_mem s) j).symm)
  refine ContinuousOn.congr ?_ (fun s _ => heq s)
  exact continuousOn_finsetSum _ (fun j _ => ((gs.viscous_curve_continuous j).norm.pow 2))

/-- **Norm lower-semicontinuity from a single inner-product convergence.** On a real
inner-product space, if `‖gₙ‖ ≤ M` and `⟪g, gₙ⟫ → ‖g‖²`, then `‖g‖ ≤ liminf ‖gₙ‖`.

This is the inner-product-trick form of weak-lsc of the norm: `‖g‖² = lim ⟪g, gₙ⟫ ≤ ‖g‖ · liminf ‖gₙ‖`
(Cauchy–Schwarz + `Monotone.map_liminf_of_continuousAt` to commute the nonneg scalar `‖g‖` with
`liminf`), then divide by `‖g‖`.  No Mazur, no subsequence extraction. -/
theorem norm_le_liminf_of_inner_tendsto {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (g : E) (gn : ℕ → E) (M : ℝ) (hM : ∀ n, ‖gn n‖ ≤ M)
    (hinner : Tendsto (fun n => @inner ℝ E _ g (gn n)) atTop (nhds (‖g‖ ^ 2))) :
    ‖g‖ ≤ Filter.liminf (fun n => ‖gn n‖) atTop := by
  have hbddAbove : Filter.IsBoundedUnder (· ≤ ·) atTop (fun n => ‖gn n‖) :=
    Filter.isBoundedUnder_of_eventually_le (a := M) (Filter.Eventually.of_forall hM)
  have hbddBelow : Filter.IsBoundedUnder (· ≥ ·) atTop (fun n => ‖gn n‖) :=
    Filter.isBoundedUnder_of_eventually_ge (a := 0)
      (Filter.Eventually.of_forall (fun n => norm_nonneg _))
  have hcobdd : Filter.IsCoboundedUnder (· ≥ ·) atTop (fun n => ‖gn n‖) :=
    hbddAbove.isCoboundedUnder_ge
  by_cases hg0 : g = 0
  · rw [hg0, norm_zero]
    exact Filter.le_liminf_of_le hcobdd (Filter.Eventually.of_forall (fun n => norm_nonneg _))
  have hgpos : (0:ℝ) < ‖g‖ := norm_pos_iff.mpr hg0
  have hlim_eq : Filter.liminf (fun n => @inner ℝ E _ g (gn n)) atTop = ‖g‖ ^ 2 :=
    hinner.liminf_eq
  have hconst : (‖g‖ * Filter.liminf (fun n => ‖gn n‖) atTop)
      = Filter.liminf (fun n => ‖g‖ * ‖gn n‖) atTop := by
    have hmono : Monotone (fun x : ℝ => ‖g‖ * x) := fun a b hab =>
      mul_le_mul_of_nonneg_left hab (norm_nonneg _)
    exact hmono.map_liminf_of_continuousAt (fun n => ‖gn n‖)
      (Continuous.continuousAt (by continuity)) hcobdd hbddBelow
  have hbddAbove2 : Filter.IsBoundedUnder (· ≤ ·) atTop (fun n => ‖g‖ * ‖gn n‖) :=
    Filter.isBoundedUnder_of_eventually_le (a := ‖g‖ * M)
      (Filter.Eventually.of_forall (fun n => mul_le_mul_of_nonneg_left (hM n) (norm_nonneg _)))
  have hbddBelow_inner : Filter.IsBoundedUnder (· ≥ ·) atTop (fun n => @inner ℝ E _ g (gn n)) :=
    hinner.isBoundedUnder_ge
  have hmono2 : Filter.liminf (fun n => @inner ℝ E _ g (gn n)) atTop
      ≤ Filter.liminf (fun n => ‖g‖ * ‖gn n‖) atTop :=
    Filter.liminf_le_liminf (Filter.Eventually.of_forall (fun n => real_inner_le_norm g (gn n)))
      hbddBelow_inner hbddAbove2.isCoboundedUnder_ge
  rw [hlim_eq, ← hconst, pow_two] at hmono2
  exact le_of_mul_le_mul_left hmono2 hgpos

/-- **Norm weak-lsc (`toWeakSpace` form).** If `gₙ ⇀ g` weakly in `WeakSpace ℝ E` and `‖gₙ‖ ≤ M`,
then `‖g‖ ≤ liminf ‖gₙ‖`.  (Extract the inner-product convergence `⟪g, gₙ⟫ → ‖g‖²` from the weak
limit — eval against the Riesz dual of `g` — then apply `norm_le_liminf_of_inner_tendsto`.) -/
private theorem norm_le_liminf_of_weak {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (g : E) (gn : ℕ → E) (M : ℝ) (hM : ∀ n, ‖gn n‖ ≤ M)
    (hw : Tendsto (fun n => toWeakSpace ℝ E (gn n)) atTop (nhds (toWeakSpace ℝ E g))) :
    ‖g‖ ≤ Filter.liminf (fun n => ‖gn n‖) atTop := by
  have hBinj : Function.Injective ((topDualPairing ℝ E).flip) :=
    separatingDual_iff_injective.mp inferInstance
  have hev := (WeakBilin.tendsto_iff_forall_eval_tendsto
    (B := (topDualPairing ℝ E).flip) hBinj).mp hw ((InnerProductSpace.toDual ℝ E) g)
  have hinner : Tendsto (fun n => @inner ℝ E _ g (gn n)) atTop (nhds (@inner ℝ E _ g g)) := hev
  rw [real_inner_self_eq_norm_sq] at hinner
  exact norm_le_liminf_of_inner_tendsto g gn M hM hinner

/-- **Squared-norm weak-lsc (`toWeakSpace` form).** From `gₙ ⇀ g` and `‖gₙ‖ ≤ M`,
`‖g‖² ≤ liminf ‖gₙ‖²`.  Squaring `‖g‖ ≤ liminf ‖gₙ‖` via the continuous monotone `Real.sqrt`
(`‖gₙ‖ = √(‖gₙ‖²)`, so `liminf ‖gₙ‖ = √(liminf ‖gₙ‖²)`). -/
private theorem normSq_le_liminf_of_weak {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (g : E) (gn : ℕ → E) (M : ℝ) (hM : ∀ n, ‖gn n‖ ≤ M)
    (hw : Tendsto (fun n => toWeakSpace ℝ E (gn n)) atTop (nhds (toWeakSpace ℝ E g))) :
    ‖g‖ ^ 2 ≤ Filter.liminf (fun n => ‖gn n‖ ^ 2) atTop := by
  have hnorm := norm_le_liminf_of_weak g gn M hM hw
  have hbddAbove2 : Filter.IsBoundedUnder (· ≤ ·) atTop (fun n => ‖gn n‖ ^ 2) :=
    Filter.isBoundedUnder_of_eventually_le (a := M ^ 2)
      (Filter.Eventually.of_forall (fun n =>
        pow_le_pow_left₀ (norm_nonneg _) (hM n) 2))
  have hbddBelow2 : Filter.IsBoundedUnder (· ≥ ·) atTop (fun n => ‖gn n‖ ^ 2) :=
    Filter.isBoundedUnder_of_eventually_ge (a := 0)
      (Filter.Eventually.of_forall (fun n => by positivity))
  -- `liminf ‖gₙ‖ = √(liminf ‖gₙ‖²)`: `Real.sqrt` is monotone-continuous and `‖gₙ‖ = √(‖gₙ‖²)`.
  have hsqrt_eq : Filter.liminf (fun n => ‖gn n‖) atTop
      = Real.sqrt (Filter.liminf (fun n => ‖gn n‖ ^ 2) atTop) := by
    have hmonoSqrt : Monotone Real.sqrt := fun a b h => Real.sqrt_le_sqrt h
    have hmap := hmonoSqrt.map_liminf_of_continuousAt (fun n => ‖gn n‖ ^ 2)
      (Real.continuous_sqrt.continuousAt) hbddAbove2.isCoboundedUnder_ge hbddBelow2
    rw [hmap]
    apply Filter.liminf_congr
    exact Filter.Eventually.of_forall (fun n => by
      rw [Function.comp_apply, Real.sqrt_sq (norm_nonneg _)])
  rw [hsqrt_eq] at hnorm
  have hL_nonneg : 0 ≤ Filter.liminf (fun n => ‖gn n‖ ^ 2) atTop :=
    Filter.le_liminf_of_le hbddAbove2.isCoboundedUnder_ge
      (Filter.Eventually.of_forall (fun n => by positivity))
  calc ‖g‖ ^ 2 ≤ (Real.sqrt (Filter.liminf (fun n => ‖gn n‖ ^ 2) atTop)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ = Filter.liminf (fun n => ‖gn n‖ ^ 2) atTop := Real.sq_sqrt hL_nonneg

/-- **An ℝ-CLM pushes weak convergence.** If `gₙ ⇀ g` in `WeakSpace ℝ E`, then `S gₙ ⇀ S g` in
`WeakSpace ℝ F`, for any `S : E →L[ℝ] F`.  (Each dual `L` of `F` pulls back to the dual `L ∘L S`
of `E`, against which the source weak convergence holds.) -/
private theorem clm_pushes_weak {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (S : E →L[ℝ] F) {gn : ℕ → E} {g : E}
    (hw : Tendsto (fun n => toWeakSpace ℝ E (gn n)) atTop (nhds (toWeakSpace ℝ E g))) :
    Tendsto (fun n => toWeakSpace ℝ F (S (gn n))) atTop (nhds (toWeakSpace ℝ F (S g))) := by
  have hBinjE : Function.Injective ((topDualPairing ℝ E).flip) :=
    separatingDual_iff_injective.mp inferInstance
  have hBinjF : Function.Injective ((topDualPairing ℝ F).flip) :=
    separatingDual_iff_injective.mp inferInstance
  refine (WeakBilin.tendsto_iff_forall_eval_tendsto
    (B := (topDualPairing ℝ F).flip) hBinjF).mpr ?_
  intro L
  exact (WeakBilin.tendsto_iff_forall_eval_tendsto
    (B := (topDualPairing ℝ E).flip) hBinjE).mp hw (L ∘L S)

/-- The bounded Fourier-component CLM `𝓕 ∘ projⱼ : L²VF → L²C` (as an ℝ-CLM). -/
private noncomputable def fourierProjCLM (j : Fin 3) : L2VF_R3 →L[ℝ] L2C_R3 :=
  (((Lp.fourierTransformₗᵢ Domain3 ℂ).toLinearIsometry.toContinuousLinearMap).restrictScalars ℝ)
    ∘L L2VF_projComponentC_R3 j

private theorem fourierProjCLM_apply (j : Fin 3) (u : L2VF_R3) :
    fourierProjCLM j u = (𝓕 (L2VF_projComponentC_R3 j u) : L2C_R3) := rfl

/-- The bounded truncated-weight multiplier `mulBdd m` (for `|m| ≤ C`) as an ℝ-CLM on `L²C`. -/
private noncomputable def mulBddCLM (m : Domain3 → ℝ)
    (hmem : MemLp (fun ξ : Domain3 => (m ξ : ℂ)) ⊤ (volume : Measure Domain3))
    {C : ℝ} (hC : 0 ≤ C) (hmle : ∀ ξ, |m ξ| ≤ C) : L2C_R3 →L[ℝ] L2C_R3 where
  toFun := fun g => mulBdd m hmem g
  map_add' := mulBdd_add m hmem
  map_smul' := by intro r g; simpa using mulBdd_smul m hmem r g
  cont := continuous_mulBdd m hmem hC hmle

private theorem mulBddCLM_apply (m : Domain3 → ℝ)
    (hmem : MemLp (fun ξ : Domain3 => (m ξ : ℂ)) ⊤ (volume : Measure Domain3))
    {C : ℝ} (hC : 0 ≤ C) (hmle : ∀ ξ, |m ξ| ≤ C) (g : L2C_R3) :
    mulBddCLM m hmem hC hmle g = mulBdd m hmem g := rfl

-- The `tailVF`/`norm_tailVF_le`/`inner_eq_ball_add_tail`/`tendsto_norm_tailVF_zero` quartet
-- this lemma builds on now lives in `R3.SpatialCompactness` (issue #111 PR-3); imported here.

/-- **Cauchy–Schwarz tail bound** (uniform in the second argument's global norm). -/
private theorem abs_tail_inner_le' (R : ℝ) (v w : L2VF_R3) :
    |(inner ℝ (tailVF R v) (tailVF R w) : ℝ)| ≤ ‖tailVF R v‖ * ‖w‖ :=
  le_trans (abs_real_inner_le_norm _ _)
    (mul_le_mul_of_nonneg_left (norm_tailVF_le R w) (norm_nonneg _))

/-- **Fixed-test-vector weak convergence at a.e. `t`.** From per-ball a.e.-`t` convergence
`restrictToBall R (uₙ t) → restrictToBall R (u t)` (all `R`) plus the uniform `L²` bounds
`‖uₙ t‖ ≤ M`, `‖u t‖ ≤ M`, the inner products against any fixed `e` converge:
`⟪e, uₙ t⟫ → ⟪e, u t⟫`.  Ball/tail ε/3 split: the ball part converges (`restrictToBall` strong),
the tails are bounded by `‖tail e‖ · M → 0`. -/
theorem inner_tendsto_of_perball
    (e : L2VF_R3) (un : ℕ → L2VF_R3) (u : L2VF_R3) (M : ℝ) (hM0 : 0 ≤ M)
    (hbd : ∀ n, ‖un n‖ ≤ M) (hbu : ‖u‖ ≤ M)
    (hperball : ∀ k : ℕ, Tendsto (fun n => restrictToBall (k : ℝ) (un n)) atTop
      (nhds (restrictToBall (k : ℝ) u))) :
    Tendsto (fun n => (inner ℝ e (un n) : ℝ)) atTop (nhds (inner ℝ e u : ℝ)) := by
  refine Metric.tendsto_atTop.2 (fun ε hε => ?_)
  set C : ℝ := M + ‖e‖ + 1 with hC
  have hCpos : 0 < C := by positivity
  obtain ⟨k0, hk0⟩ := (Metric.tendsto_atTop.1 (tendsto_norm_tailVF_zero e)) (ε / (3 * C))
    (by positivity)
  have htk : ‖tailVF (k0 : ℝ) e‖ < ε / (3 * C) := by
    have := hk0 k0 le_rfl; rwa [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at this
  have htk_nonneg : 0 ≤ ‖tailVF (k0 : ℝ) e‖ := norm_nonneg _
  have hballconv : Tendsto
      (fun n => (inner ℝ (restrictToBall (k0:ℝ) e) (restrictToBall (k0:ℝ) (un n)) : ℝ))
      atTop (nhds (inner ℝ (restrictToBall (k0:ℝ) e) (restrictToBall (k0:ℝ) u) : ℝ)) :=
    (tendsto_const_nhds).inner (hperball k0)
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hballconv) (ε / 3) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq, inner_eq_ball_add_tail (k0:ℝ) e (un n), inner_eq_ball_add_tail (k0:ℝ) e u]
  have hbM : ‖tailVF (k0:ℝ) e‖ * M < ε / 3 := by
    calc ‖tailVF (k0:ℝ) e‖ * M ≤ ‖tailVF (k0:ℝ) e‖ * C := by
            apply mul_le_mul_of_nonneg_left _ htk_nonneg; rw [hC]; linarith [norm_nonneg e]
      _ < (ε / (3 * C)) * C := mul_lt_mul_of_pos_right htk hCpos
      _ = ε / 3 := by field_simp
  have htn := lt_of_le_of_lt (le_trans (abs_tail_inner_le' (k0:ℝ) e (un n))
    (mul_le_mul_of_nonneg_left (hbd n) htk_nonneg)) hbM
  have htu := lt_of_le_of_lt (le_trans (abs_tail_inner_le' (k0:ℝ) e u)
    (mul_le_mul_of_nonneg_left hbu htk_nonneg)) hbM
  have hballn := hN n hn; rw [Real.dist_eq] at hballn
  set B1 := (inner ℝ (restrictToBall (k0:ℝ) e) (restrictToBall (k0:ℝ) (un n)) : ℝ)
  set T1 := (inner ℝ (tailVF (k0:ℝ) e) (tailVF (k0:ℝ) (un n)) : ℝ)
  set B2 := (inner ℝ (restrictToBall (k0:ℝ) e) (restrictToBall (k0:ℝ) u) : ℝ)
  set T2 := (inner ℝ (tailVF (k0:ℝ) e) (tailVF (k0:ℝ) u) : ℝ)
  rw [abs_lt] at hballn ⊢
  rw [abs_lt] at htn htu
  constructor <;> linarith [hballn.1, hballn.2, htn.1, htn.2, htu.1, htu.2]

/-- **Fixed-test-vector convergence ⟹ weak convergence** in `WeakSpace ℝ L2VF_R3`.  If
`⟪e, uₙ⟫ → ⟪e, u⟫` for every `e` (Riesz: every dual), then `uₙ ⇀ u`. -/
theorem weak_tendsto_of_inner_tendsto
    (un : ℕ → L2VF_R3) (u : L2VF_R3)
    (hfix : ∀ e : L2VF_R3,
      Tendsto (fun n => (inner ℝ e (un n) : ℝ)) atTop (nhds (inner ℝ e u : ℝ))) :
    Tendsto (fun n => toWeakSpace ℝ L2VF_R3 (un n)) atTop (nhds (toWeakSpace ℝ L2VF_R3 u)) := by
  have hBinj : Function.Injective ((topDualPairing ℝ L2VF_R3).flip) :=
    separatingDual_iff_injective.mp inferInstance
  refine (WeakBilin.tendsto_iff_forall_eval_tendsto
    (B := (topDualPairing ℝ L2VF_R3).flip) hBinj).mpr ?_
  intro L
  set e := (InnerProductSpace.toDual ℝ L2VF_R3).symm L with he
  have hL : ∀ x : L2VF_R3, L x = @inner ℝ L2VF_R3 _ e x :=
    fun x => (InnerProductSpace.toDual_symm_apply).symm
  have : Tendsto (fun n => L (un n)) atTop (nhds (L u)) := by
    simp only [hL]; exact hfix e
  exact this

/-- The `j`-th viscous spectral integrand `∫ (2π)²‖ξ‖² ‖𝓕(projⱼ w)‖²` (the `j`-summand of
`viscousFormSq_R3 1 w`). -/
private noncomputable def viscousIntegrand_j (j : Fin 3) (w : L2VF_R3) : ℝ :=
  ∫ ξ : Domain3, (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 *
    ‖(𝓕 (L2VF_projComponentC_R3 j w) : L2C_R3) ξ‖ ^ 2 ∂(volume : Measure Domain3)

private theorem viscousIntegrand_j_nonneg (j : Fin 3) (w : L2VF_R3) :
    0 ≤ viscousIntegrand_j j w :=
  integral_nonneg (fun ξ => by positivity)

private theorem viscousFormSq_eq_sum_integrand (w : L2VF_R3) :
    viscousFormSq_R3 1 w = ∑ j : Fin 3, viscousIntegrand_j j w :=
  FourierL2.viscousFormSq_R3_eq_integral_normSq_fourier w

/-- The `j`-th viscous integrand as a lower Lebesgue integral (ENNReal), which carries the
spectral seminorm with NO integrability/`H¹` precondition (the junk-`0` of the Bochner form
is avoided): `viscousLintegrand_j j w = ∫⁻ ofReal ((2π)²‖ξ‖² ‖𝓕(projⱼ w)‖²)`. -/
private noncomputable def viscousLintegrand_j (j : Fin 3) (w : L2VF_R3) : ENNReal :=
  ∫⁻ ξ : Domain3, ENNReal.ofReal ((2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 *
    ‖(𝓕 (L2VF_projComponentC_R3 j w) : L2C_R3) ξ‖ ^ 2) ∂(volume : Measure Domain3)

/-- `ofReal (∫ f) ≤ ∫⁻ ofReal f` for the (nonneg) viscous integrand — no integrability needed
(if non-integrable the Bochner integral is `0`). -/
private theorem ofReal_viscousIntegrand_le_lintegrand (j : Fin 3) (w : L2VF_R3) :
    ENNReal.ofReal (viscousIntegrand_j j w) ≤ viscousLintegrand_j j w := by
  rw [viscousIntegrand_j, viscousLintegrand_j]
  by_cases hint : Integrable (fun ξ : Domain3 => (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 *
      ‖(𝓕 (L2VF_projComponentC_R3 j w) : L2C_R3) ξ‖ ^ 2) volume
  · rw [ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall (fun ξ => by positivity))]
  · rw [integral_undef hint, ENNReal.ofReal_zero]; exact bot_le

/-- Two-term superadditivity of `liminf` in `ENNReal`: `liminf u + liminf v ≤ liminf (u+v)`.
Proved via the `⨆ n, ⨅ i, ·(i+n)` form (`liminf_eq_iSup_iInf_of_nat'`) and ENNReal's
`add_iInf`/`iInf_add` + `iSup` monotonicity; avoids the absent `le_liminf_add` import. -/
private theorem add_liminf_le_liminf_add (u v : ℕ → ENNReal) :
    Filter.atTop.liminf u + Filter.atTop.liminf v ≤ Filter.atTop.liminf (fun n => u n + v n) := by
  rw [Filter.liminf_eq_iSup_iInf_of_nat', Filter.liminf_eq_iSup_iInf_of_nat',
    Filter.liminf_eq_iSup_iInf_of_nat']
  -- `(⨆n ⨅i u(i+n)) + (⨆n ⨅i v(i+n)) ≤ ⨆n ⨅i (u(i+n)+v(i+n))`.
  -- The iInf-tails are monotone in `n`, so for any `n₁,n₂` use `n := max n₁ n₂`.
  refine ENNReal.iSup_add_iSup_le (fun n₁ n₂ => ?_)
  refine le_iSup_of_le (max n₁ n₂) ?_
  refine le_iInf (fun i => ?_)
  -- `(⨅i u(i+n₁)) + (⨅i v(i+n₂)) ≤ u(i+max) + v(i+max)`, then `≤ ⨅i (u+v)(i+max)`.
  have hu : (⨅ k : ℕ, u (k + n₁)) ≤ u (i + max n₁ n₂) := by
    refine le_trans (iInf_le _ (i + (max n₁ n₂ - n₁))) (le_of_eq ?_)
    congr 1; omega
  have hv : (⨅ k : ℕ, v (k + n₂)) ≤ v (i + max n₁ n₂) := by
    refine le_trans (iInf_le _ (i + (max n₁ n₂ - n₂))) (le_of_eq ?_)
    congr 1; omega
  exact add_le_add hu hv

/-- Superadditivity of `liminf` over a `Finset` (in `ENNReal`): `∑ liminf ≤ liminf ∑`. -/
private theorem sum_liminf_le_liminf_sum {α : Type*} (s : Finset α) (f : α → ℕ → ENNReal) :
    (∑ a ∈ s, Filter.atTop.liminf (fun n => f a n))
      ≤ Filter.atTop.liminf (fun n => ∑ a ∈ s, f a n) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    calc Filter.atTop.liminf (fun n => f a n) + ∑ x ∈ s, Filter.atTop.liminf (fun n => f x n)
        ≤ Filter.atTop.liminf (fun n => f a n) + Filter.atTop.liminf (fun n => ∑ x ∈ s, f x n) := by
          gcongr
      _ ≤ Filter.atTop.liminf (fun n => f a n + ∑ x ∈ s, f x n) :=
          add_liminf_le_liminf_add _ _
      _ = Filter.atTop.liminf (fun n => ∑ x ∈ insert a s, f x n) := by
          apply Filter.liminf_congr
          refine Filter.Eventually.of_forall (fun n => ?_)
          rw [Finset.sum_insert ha]

/-- The truncated multiplier norm² (a real, always-finite quantity) lower-bounds the `j`-th
viscous lower Lebesgue integral: `ofReal ‖mulBdd (min(√W,k)) (𝓕 projⱼ w)‖² ≤ viscousLintegrand_j`.
No `H¹` hypothesis — the truncated integrand is `≤` the full weight pointwise and both are
nonneg, so `lintegral_mono` closes it. -/
private theorem mulBddTrunc_integrable (k : ℕ) (g : L2C_R3) :
    Integrable (fun ξ : Domain3 => (sqrtViscousWeightTrunc k ξ) ^ 2 * ‖(g : Domain3 → ℂ) ξ‖ ^ 2)
      volume := by
  have hgsq : Integrable (fun ξ : Domain3 => ‖(g : Domain3 → ℂ) ξ‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable g)).mp (Lp.memLp g)
  refine Integrable.mono' (hgsq.const_mul ((k : ℝ) ^ 2))
    (((continuous_sqrtViscousWeightTrunc k).pow 2).aestronglyMeasurable.mul
      ((Lp.aestronglyMeasurable g).norm.pow 2))
    (Filter.Eventually.of_forall (fun ξ => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hk2 : (sqrtViscousWeightTrunc k ξ) ^ 2 ≤ (k : ℝ) ^ 2 := by
    rw [← sq_abs (sqrtViscousWeightTrunc k ξ)]
    exact pow_le_pow_left₀ (abs_nonneg _) (sqrtViscousWeightTrunc_abs_le k ξ) 2
  exact mul_le_mul_of_nonneg_right hk2 (by positivity)

private theorem ofReal_norm_mulBddTrunc_sq_le_lintegrand (k : ℕ) (j : Fin 3) (w : L2VF_R3) :
    ENNReal.ofReal (‖mulBdd (sqrtViscousWeightTrunc k) (memLp_top_sqrtViscousWeightTrunc k)
        (𝓕 (L2VF_projComponentC_R3 j w) : L2C_R3)‖ ^ 2) ≤ viscousLintegrand_j j w := by
  set Fj : L2C_R3 := (𝓕 (L2VF_projComponentC_R3 j w) : L2C_R3) with hFj
  rw [norm_mulBdd_sq _ _ Fj, viscousLintegrand_j,
    ofReal_integral_eq_lintegral_ofReal (mulBddTrunc_integrable k Fj)
      (Filter.Eventually.of_forall (fun ξ => by positivity))]
  refine lintegral_mono (fun ξ => ?_)
  apply ENNReal.ofReal_le_ofReal
  have hwsq : (sqrtViscousWeightTrunc k ξ) ^ 2 ≤ (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 := by
    have h1 : sqrtViscousWeightTrunc k ξ ≤ sqrtViscousWeight ξ := min_le_left _ _
    have h2 : (sqrtViscousWeightTrunc k ξ) ^ 2 ≤ (sqrtViscousWeight ξ) ^ 2 :=
      pow_le_pow_left₀ (sqrtViscousWeightTrunc_nonneg _ _) h1 2
    rwa [sqrtViscousWeight_sq, viscousWeight] at h2
  exact mul_le_mul_of_nonneg_right hwsq (by positivity)

/-- **MCT in the truncation level.** The truncated multiplier norms² increase to the `j`-th
viscous lower Lebesgue integral: `⨆ k, ofReal ‖mulBdd_k (𝓕 projⱼ w)‖² = viscousLintegrand_j j w`. -/
private theorem iSup_ofReal_norm_mulBddTrunc_sq (j : Fin 3) (w : L2VF_R3) :
    (⨆ k : ℕ, ENNReal.ofReal (‖mulBdd (sqrtViscousWeightTrunc k)
        (memLp_top_sqrtViscousWeightTrunc k) (𝓕 (L2VF_projComponentC_R3 j w) : L2C_R3)‖ ^ 2))
      = viscousLintegrand_j j w := by
  set Fj : L2C_R3 := (𝓕 (L2VF_projComponentC_R3 j w) : L2C_R3) with hFj
  -- Each term: ofReal ‖mulBdd_k Fj‖² = ∫⁻ ofReal ((min(√W,k))² ‖Fj‖²) (integrable ⟹ ofReal-lintegral).
  have hterm : ∀ k : ℕ,
      ENNReal.ofReal (‖mulBdd (sqrtViscousWeightTrunc k) (memLp_top_sqrtViscousWeightTrunc k) Fj‖ ^ 2)
      = ∫⁻ ξ, ENNReal.ofReal ((sqrtViscousWeightTrunc k ξ) ^ 2 * ‖(Fj : Domain3 → ℂ) ξ‖ ^ 2)
          ∂volume := by
    intro k
    rw [norm_mulBdd_sq _ _ Fj]
    exact ofReal_integral_eq_lintegral_ofReal (mulBddTrunc_integrable k Fj)
      (Filter.Eventually.of_forall (fun ξ => by positivity))
  simp_rw [hterm, viscousLintegrand_j]
  -- monotonicity of the truncated weight squared in `k` (used repeatedly).
  have hmono_w : ∀ ξ : Domain3, Monotone (fun k : ℕ => (sqrtViscousWeightTrunc k ξ) ^ 2) := by
    intro ξ a b hab
    exact pow_le_pow_left₀ (sqrtViscousWeightTrunc_nonneg _ _)
      (by simp only [sqrtViscousWeightTrunc]; exact min_le_min_left _ (by exact_mod_cast hab)) 2
  -- MCT: `⨆ k ∫⁻ gk = ∫⁻ ⨆ k gk`, and pointwise `⨆ k gk = ofReal (W ‖Fj‖²)`.
  rw [← lintegral_iSup]
  · refine lintegral_congr (fun ξ => ?_)
    -- pointwise: `⨆ k, ofReal ((min(√W,k))² ‖Fj‖²) = ofReal ((2π)²‖ξ‖² ‖Fj‖²)`.
    have hwtend : Tendsto (fun k : ℕ => (sqrtViscousWeightTrunc k ξ) ^ 2 * ‖(Fj:Domain3→ℂ) ξ‖ ^ 2)
        atTop (nhds ((2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 * ‖(Fj:Domain3→ℂ) ξ‖ ^ 2)) := by
      have h1 := (tendsto_sqrtViscousWeightTrunc ξ).pow 2
      have h2 := h1.mul_const (‖(Fj:Domain3→ℂ) ξ‖ ^ 2)
      rwa [show sqrtViscousWeight ξ ^ 2 = (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 by
        rw [sqrtViscousWeight_sq, viscousWeight]] at h2
    have hmono2 : Monotone (fun k : ℕ =>
        ENNReal.ofReal ((sqrtViscousWeightTrunc k ξ) ^ 2 * ‖(Fj:Domain3→ℂ) ξ‖ ^ 2)) := by
      intro a b hab
      exact ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (hmono_w ξ hab) (by positivity))
    exact tendsto_nhds_unique (tendsto_atTop_iSup hmono2) (ENNReal.tendsto_ofReal hwtend)
  · intro k
    exact (ENNReal.measurable_ofReal.comp
      (((continuous_sqrtViscousWeightTrunc k).pow 2).measurable.mul
        ((Lp.stronglyMeasurable Fj).measurable.norm.pow_const 2)))
  · intro a b hab
    refine fun ξ => ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (hmono_w ξ hab) (by positivity))

/-- For an `H¹` field `w`, the truncated multiplier norm² is `≤` the (genuinely-integrable) `j`-th
viscous integrand: `‖mulBdd (min(√W,k)) (𝓕 projⱼ w)‖² ≤ viscousIntegrand_j j w`.  (The full weight
integrand is integrable because `w ∈ H¹` — `integrable_viscous_integrand_of_memH1`.) -/
private theorem norm_mulBddTrunc_sq_le_integrand_of_memH1 (k : ℕ) (j : Fin 3) (w : L2VF_R3)
    (hw : memH1VF_R3 w) :
    ‖mulBdd (sqrtViscousWeightTrunc k) (memLp_top_sqrtViscousWeightTrunc k)
        (𝓕 (L2VF_projComponentC_R3 j w) : L2C_R3)‖ ^ 2 ≤ viscousIntegrand_j j w := by
  set Fj : L2C_R3 := (𝓕 (L2VF_projComponentC_R3 j w) : L2C_R3) with hFj
  rw [norm_mulBdd_sq _ _ Fj, viscousIntegrand_j]
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall (fun ξ => by positivity))
    (integrable_viscous_integrand_of_memH1 w hw j) (Filter.Eventually.of_forall (fun ξ => ?_))
  have hwsq : (sqrtViscousWeightTrunc k ξ) ^ 2 ≤ (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 := by
    have h1 : sqrtViscousWeightTrunc k ξ ≤ sqrtViscousWeight ξ := min_le_left _ _
    have h2 : (sqrtViscousWeightTrunc k ξ) ^ 2 ≤ (sqrtViscousWeight ξ) ^ 2 :=
      pow_le_pow_left₀ (sqrtViscousWeightTrunc_nonneg _ _) h1 2
    rwa [sqrtViscousWeight_sq, viscousWeight] at h2
  exact mul_le_mul_of_nonneg_right hwsq (by positivity)

/-- **Per-component pointwise viscous lsc.** Given full-sequence weak-L² convergence
`uₙ ⇀ u` and the uniform `L²` bound, with each approximant `H¹`, the `j`-th viscous lower Lebesgue
integral of the limit is dominated by the `liminf` of the approximants' (Bochner) `j`-integrands:
`viscousLintegrand_j j u ≤ liminf_n ofReal (viscousIntegrand_j j uₙ)`.

Chain (per truncation `k`): push `uₙ ⇀ u` through the bounded CLM `mulBdd_k ∘ 𝓕 ∘ projⱼ`, apply
norm-weak-lsc, square, bound by the approximant integrand (truncated ≤ full, `H¹`); then take the
supremum over `k` (MCT) to recover the full lower Lebesgue integrand of the limit. -/
private theorem viscousLintegrand_le_liminf_of_weak (j : Fin 3)
    (un : ℕ → L2VF_R3) (u : L2VF_R3) (M : ℝ) (hM0 : 0 ≤ M)
    (hbd : ∀ n, ‖un n‖ ≤ M) (hH1 : ∀ n, memH1VF_R3 (un n))
    (hweak : Tendsto (fun n => toWeakSpace ℝ L2VF_R3 (un n)) atTop
      (nhds (toWeakSpace ℝ L2VF_R3 u))) :
    viscousLintegrand_j j u
      ≤ Filter.atTop.liminf (fun n => ENNReal.ofReal (viscousIntegrand_j j (un n))) := by
  -- per truncation `k`: the `ENNReal` bound on the limit's truncated multiplier norm².
  have hk : ∀ k : ℕ,
      ENNReal.ofReal (‖mulBdd (sqrtViscousWeightTrunc k) (memLp_top_sqrtViscousWeightTrunc k)
          (𝓕 (L2VF_projComponentC_R3 j u) : L2C_R3)‖ ^ 2)
        ≤ Filter.atTop.liminf (fun n => ENNReal.ofReal (viscousIntegrand_j j (un n))) := by
    intro k
    -- the bounded CLM `S := mulBdd_k ∘ 𝓕 ∘ projⱼ`, in `L²C` (over ℝ).
    set hCk : ∀ ξ, |sqrtViscousWeightTrunc k ξ| ≤ (k : ℝ) := sqrtViscousWeightTrunc_abs_le k with hCkdef
    set S : L2VF_R3 →L[ℝ] L2C_R3 :=
      (mulBddCLM (sqrtViscousWeightTrunc k) (memLp_top_sqrtViscousWeightTrunc k)
        (Nat.cast_nonneg k) hCk) ∘L fourierProjCLM j with hS
    have hSapply : ∀ w : L2VF_R3, S w = mulBdd (sqrtViscousWeightTrunc k)
        (memLp_top_sqrtViscousWeightTrunc k) (𝓕 (L2VF_projComponentC_R3 j w) : L2C_R3) :=
      fun w => rfl
    -- squared-norm weak-lsc, pushed through the CLM `S`.
    have hsq_lsc : ‖S u‖ ^ 2 ≤ Filter.liminf (fun n => ‖S (un n)‖ ^ 2) atTop :=
      normSq_le_liminf_of_weak (S u) (fun n => S (un n)) (‖S‖ * M) (fun n =>
        le_trans (S.le_opNorm _) (mul_le_mul_of_nonneg_left (hbd n) (norm_nonneg _)))
        (clm_pushes_weak S hweak)
    -- approximant side: `‖S (uₙ)‖² ≤ viscousIntegrand_j j uₙ` (truncated ≤ full, `H¹`).
    have happrox : ∀ n, ‖S (un n)‖ ^ 2 ≤ viscousIntegrand_j j (un n) := by
      intro n; rw [hSapply]
      exact norm_mulBddTrunc_sq_le_integrand_of_memH1 k j (un n) (hH1 n)
    -- bounded-above for `S uₙ` (so its squared-norm liminf transports to `ENNReal` cleanly).
    have hSbddAbove : Filter.IsBoundedUnder (· ≤ ·) atTop (fun n => ‖S (un n)‖ ^ 2) :=
      Filter.isBoundedUnder_of_eventually_le (a := (‖S‖ * M) ^ 2)
        (Filter.Eventually.of_forall (fun n =>
          pow_le_pow_left₀ (norm_nonneg _)
            (le_trans (S.le_opNorm _) (mul_le_mul_of_nonneg_left (hbd n) (norm_nonneg _))) 2))
    have hSbddBelow : Filter.IsBoundedUnder (· ≥ ·) atTop (fun n => ‖S (un n)‖ ^ 2) :=
      Filter.isBoundedUnder_of_eventually_ge (a := 0)
        (Filter.Eventually.of_forall (fun n => by positivity))
    -- `ofReal (‖S u‖²) ≤ ofReal (liminf ‖S uₙ‖²) = liminf (ofReal ‖S uₙ‖²)` (bounded-above ⟹ map-liminf).
    have hofReal_eq : ENNReal.ofReal (Filter.liminf (fun n => ‖S (un n)‖ ^ 2) atTop)
        = Filter.liminf (fun n => ENNReal.ofReal (‖S (un n)‖ ^ 2)) atTop :=
      ENNReal.ofReal_mono.map_liminf_of_continuousAt _ ENNReal.continuous_ofReal.continuousAt
        hSbddAbove.isCoboundedUnder_ge hSbddBelow
    rw [← hSapply u]
    calc ENNReal.ofReal (‖S u‖ ^ 2)
        ≤ ENNReal.ofReal (Filter.liminf (fun n => ‖S (un n)‖ ^ 2) atTop) :=
          ENNReal.ofReal_le_ofReal hsq_lsc
      _ = Filter.liminf (fun n => ENNReal.ofReal (‖S (un n)‖ ^ 2)) atTop := hofReal_eq
      _ ≤ Filter.atTop.liminf (fun n => ENNReal.ofReal (viscousIntegrand_j j (un n))) :=
          Filter.liminf_le_liminf (Filter.Eventually.of_forall
            (fun n => ENNReal.ofReal_le_ofReal (happrox n)))
  -- assemble via MCT-sup in `k`.
  calc viscousLintegrand_j j u
      = ⨆ k : ℕ, ENNReal.ofReal (‖mulBdd (sqrtViscousWeightTrunc k)
          (memLp_top_sqrtViscousWeightTrunc k) (𝓕 (L2VF_projComponentC_R3 j u) : L2C_R3)‖ ^ 2) :=
        (iSup_ofReal_norm_mulBddTrunc_sq j u).symm
    _ ≤ Filter.atTop.liminf (fun n => ENNReal.ofReal (viscousIntegrand_j j (un n))) :=
        iSup_le hk

/-- **A.e. finiteness of the approximant-`liminf` viscous form.** From `reg_bound`
(`∫₀ᵀ viscousFormSq_R3 ν (uₙ) ≤ ½‖u₀‖²`, `n`-uniform) and Fatou-in-time, the `liminf` of the
approximants' viscous forms is finite at a.e. `t`.  No `H¹`/measurability of the LIMIT is used —
only the continuous (hence measurable) approximant curves. -/
private theorem liminf_viscousFormSq_lt_top_ae (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T) (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n)
    (alPkg : AubinLionsPackage_R3 𝔊 F ν T u₀ galSeq) :
    ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Filter.atTop.liminf
        (fun n => ENNReal.ofReal (viscousFormSq_R3 1 ((galSeq (alPkg.φ n)).u t : L2VF_R3))) < ⊤ := by
  set μ : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) T) with hμ
  set gn : ℕ → ℝ → ℝ :=
    fun n t => viscousFormSq_R3 1 ((galSeq (alPkg.φ n)).u t : L2VF_R3) with hgn
  have hgn_nonneg : ∀ n t, 0 ≤ gn n t := fun n t => viscousFormSq_R3_nonneg (by norm_num) _
  have hgn_cont : ∀ n, ContinuousOn (gn n) (Set.Ici (0 : ℝ)) :=
    fun n => viscousFormSq_curve_continuousOn 𝔊 F ν u₀ (alPkg.φ n) (galSeq (alPkg.φ n))
  have hgn_meas : ∀ n, AEMeasurable (fun t => ENNReal.ofReal (gn n t)) μ := by
    intro n; rw [hμ]
    exact ((ContinuousOn.aemeasurable ((hgn_cont n).mono (fun t ht => ht.1))
      measurableSet_Icc)).ennreal_ofReal
  -- `reg_bound` gives `∫₀ᵀ gn n ≤ ν⁻¹·½‖u₀‖²` (rescale the `ν`-form).
  have hgn_int : ∀ n, ∫ s in (0 : ℝ)..T, gn n s ≤ ν⁻¹ * ((1 / 2 : ℝ) * ‖(u₀ : L2VF_R3)‖ ^ 2) := by
    intro n
    have hrb := (galSeq (alPkg.φ n)).reg_bound T hT
    have hscale : ∀ s, viscousFormSq_R3 ν ((galSeq (alPkg.φ n)).u s : L2VF_R3) = ν * gn n s :=
      fun s => by rw [hgn, viscousFormSq_R3_eq_smul, smul_eq_mul]
    rw [intervalIntegral.integral_congr (g := fun s => ν * gn n s) (fun s _ => hscale s),
      intervalIntegral.integral_const_mul] at hrb
    rw [le_inv_mul_iff₀ hν]; exact hrb
  -- `∫⁻ ofReal (gn n) = ofReal (∫_{Icc} gn n) ≤ ofReal (ν⁻¹·½‖u₀‖²)`.
  have hGn_cap : ∀ n, ∫⁻ t, ENNReal.ofReal (gn n t) ∂μ
      ≤ ENNReal.ofReal (ν⁻¹ * ((1 / 2 : ℝ) * ‖(u₀ : L2VF_R3)‖ ^ 2)) := by
    intro n
    have hint : IntegrableOn (gn n) (Set.Icc (0 : ℝ) T) volume :=
      ContinuousOn.integrableOn_Icc ((hgn_cont n).mono (fun t ht => ht.1))
    have heq : ∫⁻ t, ENNReal.ofReal (gn n t) ∂μ
        = ENNReal.ofReal (∫ t in Set.Icc (0 : ℝ) T, gn n t ∂volume) := by
      rw [hμ, ← ofReal_integral_eq_lintegral_ofReal hint
        (Filter.Eventually.of_forall (fun t => hgn_nonneg n t))]
    rw [heq]
    refine ENNReal.ofReal_le_ofReal ?_
    have hni := hgn_int n
    rwa [intervalIntegral.integral_of_le hT.le, ← MeasureTheory.integral_Icc_eq_integral_Ioc] at hni
  -- a measurable representative of each `ofReal (gn n)`, and the a.e.-eq liminf.
  set Gn : ℕ → ℝ → ENNReal := fun n => (hgn_meas n).mk with hGndef
  have hGn_meas' : ∀ n, Measurable (Gn n) := fun n => (hgn_meas n).measurable_mk
  have hGn_ae : ∀ n, (fun t => ENNReal.ofReal (gn n t)) =ᵐ[μ] Gn n :=
    fun n => (hgn_meas n).ae_eq_mk
  have hliminf_ae : (fun t => Filter.atTop.liminf (fun n => ENNReal.ofReal (gn n t)))
      =ᵐ[μ] (fun t => Filter.atTop.liminf (fun n => Gn n t)) := by
    have hall : ∀ᵐ t ∂μ, ∀ n, ENNReal.ofReal (gn n t) = Gn n t := ae_all_iff.2 hGn_ae
    filter_upwards [hall] with t ht
    exact Filter.liminf_congr (Filter.Eventually.of_forall (fun n => ht n))
  -- Fatou: `∫⁻ liminf (ofReal gn) ≤ liminf ∫⁻ (ofReal gn) ≤ ofReal(…) < ∞`.
  have hfatou : ∫⁻ t, Filter.atTop.liminf (fun n => ENNReal.ofReal (gn n t)) ∂μ
      ≤ ENNReal.ofReal (ν⁻¹ * ((1 / 2 : ℝ) * ‖(u₀ : L2VF_R3)‖ ^ 2)) := by
    refine le_trans (lintegral_liminf_le' hgn_meas) ?_
    refine le_trans liminf_le_limsup ?_
    exact limsup_le_of_le isCobounded_le_of_bot (Filter.Eventually.of_forall hGn_cap)
  have hlt : ∫⁻ t, Filter.atTop.liminf (fun n => Gn n t) ∂μ < ⊤ := by
    rw [← lintegral_congr_ae hliminf_ae]; exact lt_of_le_of_lt hfatou ENNReal.ofReal_lt_top
  have hae_fin : ∀ᵐ t ∂μ, Filter.atTop.liminf (fun n => Gn n t) < ⊤ :=
    ae_lt_top (Measurable.liminf hGn_meas') hlt.ne
  filter_upwards [hae_fin, hliminf_ae] with t hfin hcong
  rw [hcong]; exact hfin

/-- For an `H¹` field, the (Bochner) `j`-th viscous integrand equals the `toReal` of its lower
Lebesgue counterpart: `viscousIntegrand_j j w = (viscousLintegrand_j j w).toReal`.  (On `H¹` the
integrand is integrable, so `ofReal (∫ ·) = ∫⁻ ofReal ·`.) -/
private theorem viscousIntegrand_eq_lintegrand_toReal (j : Fin 3) (w : L2VF_R3)
    (hw : memH1VF_R3 w) :
    viscousIntegrand_j j w = (viscousLintegrand_j j w).toReal := by
  rw [viscousIntegrand_j, viscousLintegrand_j,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_viscous_integrand_of_memH1 w hw j)
      (Filter.Eventually.of_forall (fun ξ => by positivity)),
    ENNReal.toReal_ofReal (integral_nonneg (fun ξ => by positivity))]

/-- **Time-measurability of `t ↦ viscousFormSq_R3 1 (alPkg.u t)`** under a.e. `H¹` membership.
On the (a.e.) `H¹` set the viscous form is `∑ⱼ (viscousLintegrand_j j (u t)).toReal`, and
`viscousLintegrand_j j (u t) = ⨆ₖ ofReal ‖mulBdd_k (𝓕 projⱼ (u t))‖²` (MCT) is a countable
supremum of `AEStronglyMeasurable`-in-`t` functions (continuous CLM ∘ measurable `u`), hence
`AEMeasurable`; `.toReal` and the finite sum preserve measurability.

Public (not `private`, unlike its file-local siblings): consumed by `AubinLionsLimitPassage.lean`
across the file split (issue #114 Tier 1 commit 1). -/
theorem viscousFormSq_aestronglyMeasurable_of_memH1
    {𝔊 : R3GalerkinScheme} {F : R3NSForms 𝔊} {ν T : ℝ} {u₀ : L2Sigma_R3}
    {galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n}
    (alPkg : AubinLionsPackage_R3 𝔊 F ν T u₀ galSeq)
    (hmemH1 : ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)), memH1VF_R3 (alPkg.u t : L2VF_R3)) :
    AEStronglyMeasurable (fun t => viscousFormSq_R3 1 (alPkg.u t : L2VF_R3))
      (volume.restrict (Set.Icc (0 : ℝ) T)) := by
  set μ : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) T) with hμ
  set u : ℝ → L2VF_R3 := fun t => (alPkg.u t : L2VF_R3) with hu
  have hu_meas : AEStronglyMeasurable u μ := by rw [hμ, hu]; exact alPkg.u_aestronglyMeasurable
  -- for each `k j`, `t ↦ ‖mulBdd_k (𝓕 projⱼ (u t))‖²` is AEStronglyMeasurable (CLM ∘ measurable).
  have hmk : ∀ (k : ℕ) (j : Fin 3),
      AEStronglyMeasurable (fun t => ‖mulBdd (sqrtViscousWeightTrunc k)
        (memLp_top_sqrtViscousWeightTrunc k) (𝓕 (L2VF_projComponentC_R3 j (u t)) : L2C_R3)‖ ^ 2) μ := by
    intro k j
    set S : L2VF_R3 →L[ℝ] L2C_R3 :=
      (mulBddCLM (sqrtViscousWeightTrunc k) (memLp_top_sqrtViscousWeightTrunc k)
        (Nat.cast_nonneg k) (sqrtViscousWeightTrunc_abs_le k)) ∘L fourierProjCLM j with hS
    refine ((S.continuous.comp_aestronglyMeasurable hu_meas).norm.pow 2).congr ?_
    exact Filter.Eventually.of_forall (fun t => rfl)
  -- `t ↦ viscousLintegrand_j j (u t) = ⨆ₖ ofReal ‖mulBdd_k …‖²` is AEMeasurable.
  have hlin_meas : ∀ j : Fin 3, AEMeasurable (fun t => viscousLintegrand_j j (u t)) μ := by
    intro j
    have hsup : (fun t => viscousLintegrand_j j (u t))
        = fun t => ⨆ k : ℕ, ENNReal.ofReal (‖mulBdd (sqrtViscousWeightTrunc k)
            (memLp_top_sqrtViscousWeightTrunc k)
            (𝓕 (L2VF_projComponentC_R3 j (u t)) : L2C_R3)‖ ^ 2) := by
      funext t; exact (iSup_ofReal_norm_mulBddTrunc_sq j (u t)).symm
    rw [hsup]
    exact AEMeasurable.iSup (fun k => (hmk k j).aemeasurable.ennreal_ofReal)
  -- `t ↦ viscousFormSq(u t)` =ᵐ `∑ⱼ (viscousLintegrand_j j (u t)).toReal`, which is AEMeasurable.
  have heq : (fun t => viscousFormSq_R3 1 (u t))
      =ᵐ[μ] fun t => ∑ j : Fin 3, (viscousLintegrand_j j (u t)).toReal := by
    filter_upwards [hmemH1] with t hmem
    show viscousFormSq_R3 1 (u t) = ∑ j : Fin 3, (viscousLintegrand_j j (u t)).toReal
    rw [viscousFormSq_eq_sum_integrand]
    exact Finset.sum_congr rfl (fun j _ => viscousIntegrand_eq_lintegrand_toReal j (u t) hmem)
  refine AEStronglyMeasurable.congr ?_ heq.symm
  refine (Finset.aemeasurable_sum Finset.univ (fun j _ => (hlin_meas j).ennreal_toReal)).aestronglyMeasurable

/-- **Pointwise weak-H¹ lower semicontinuity of the viscous seminorm** (the genuine analytic
content of the (b)-route's energy/energy-class conclusions) — PROVED `sorry`-free.

At a.e. time `t ∈ [0, T]` the strong-L²(-on-balls) Galerkin limit `alPkg.u t` lies in `H¹` and
its viscous (Dirichlet) seminorm is dominated by the `liminf` of the approximants':

```
memH1VF_R3 (alPkg.u t) ∧
ofReal (viscousFormSq_R3 1 (alPkg.u t)) ≤ liminf_n ofReal (viscousFormSq_R3 1 ((galSeq (alPkg.φ n)).u t))
```

together with time-measurability of the limit's viscous form (needed to feed Fatou downstream).

**Proof route — Fourier–Plancherel, entirely in `L²`** (no H¹ Hilbert-space type, no sequential
Banach–Alaoglu, no convex-functional weak-lsc). The viscous form `viscousFormSq_R3 1 w =
∑ⱼ ∫ (2π)²‖ξ‖² ‖𝓕(projⱼ w) ξ‖²` is the global Fourier Dirichlet seminorm: not continuous, only
weakly lower-semicontinuous, under strong-L². The chain:
* **Full-sequence weak-L²** `uₙ(t) ⇀ u(t)` a.e. `t`, from `alPkg.strong_convergence_ae` (per-ball
  a.e.-`t` strong convergence) + the ball-tail ε/3 argument against the uniform `‖uₙ t‖ ≤ ‖u₀‖`
  (`inner_tendsto_of_perball` / `weak_tendsto_of_inner_tendsto`). The full-sequence form is what
  the frozen `liminf` over `n` requires — supplied by the package's a.e.-`t` field, not a
  measure-subsequence.
* **Bounded-multiplier push**: for each truncation `k`, `mulBdd (min(√W,k)) ∘ 𝓕 ∘ projⱼ` is an
  ℝ-CLM (`mulBddCLM`/`fourierProjCLM`), so `clm_pushes_weak` transports the weak convergence; then
  squared norm-weak-lsc (`normSq_le_liminf_of_weak`, the inner-product trick `‖g‖² = lim⟪g,gₙ⟫`).
* **Truncated ≤ full + MCT in `k`** (`iSup_ofReal_norm_mulBddTrunc_sq`, `lintegral_iSup`) recovers
  the full Dirichlet integrand; sum over `j` by `ENNReal` `liminf`-superadditivity. The `memH1`
  conjunct follows from the finite weighted-Fourier integral (`reg_bound`+Fatou finiteness in
  `liminf_viscousFormSq_lt_top_ae`) via `memSobolev_of_finite_weightedFourier_R3`; time-measurability
  via `viscousFormSq_aestronglyMeasurable_of_memH1`.

`0 < ν` is load-bearing: the approximants' H¹ seminorm is controlled only through `reg_bound`'s
`ν`-weighted bound, so the `memH1` conjunct genuinely fails for `ν ≤ 0`. The *integrated* bound
(`∫₀ᵀ viscous(u) ≤ ½‖u₀‖²`) is assembled from this via Fatou-in-time + `reg_bound` in
`viscous_lsc_under_strongL2`. Temam III.3 / Lemarié-Rieusset §6. -/
theorem viscous_pointwise_lsc (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν T : ℝ) (hν : 0 < ν) (hT : 0 < T) (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n)
    (alPkg : AubinLionsPackage_R3 𝔊 F ν T u₀ galSeq) :
    (AEStronglyMeasurable
        (fun t => viscousFormSq_R3 1 (alPkg.u t : L2VF_R3))
        (volume.restrict (Set.Icc (0 : ℝ) T))) ∧
    (∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      memH1VF_R3 (alPkg.u t : L2VF_R3) ∧
      ENNReal.ofReal (viscousFormSq_R3 1 (alPkg.u t : L2VF_R3)) ≤
        Filter.atTop.liminf
          (fun n => ENNReal.ofReal (viscousFormSq_R3 1 ((galSeq (alPkg.φ n)).u t : L2VF_R3)))) := by
  -- ════ FOURIER–PLANCHEREL ROUTE (full-sequence, in `L²`; no H¹ Hilbert type, no Banach–Alaoglu). ════
  classical
  set μ : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) T) with hμ
  -- abbreviations for the limit / approximant curves.
  set u : ℝ → L2VF_R3 := fun t => (alPkg.u t : L2VF_R3) with hu
  set un : ℕ → ℝ → L2VF_R3 := fun n t => ((galSeq (alPkg.φ n)).u t : L2VF_R3) with hun
  -- (A) full-sequence weak-L² convergence `uₙ(t) ⇀ u(t)` at a.e. `t`, from `strong_convergence_ae`
  -- (per-ball a.e.-`t` convergence) + the ball-tail ε/3 argument, against the uniform `‖·‖ ≤ ‖u₀‖`.
  -- Only NAT radii are needed (the ball-tail argument uses one integer radius per ε), so the
  -- a.e.-`t` exceptional set unions over a COUNTABLE family.
  have hperball_ae : ∀ᵐ t ∂μ, ∀ k : ℕ,
      Tendsto (fun n => restrictToBall (k : ℝ) (un n t)) atTop
        (nhds (restrictToBall (k : ℝ) (u t))) :=
    ae_all_iff.2 (fun k => alPkg.strong_convergence_ae (k : ℝ))
  -- a.e.-`t`: `t ∈ Icc 0 T` (so `0 ≤ t`), giving the uniform Galerkin bound.
  have ht_nonneg : ∀ᵐ t ∂μ, (0 : ℝ) ≤ t :=
    ae_restrict_of_forall_mem measurableSet_Icc (fun t ht => ht.1)
  -- (B) the kinetic-lsc limit bound `‖u t‖ ≤ ‖u₀‖` a.e. (recover from `kineticEnergy_lsc_bound`).
  have hu_bound : ∀ᵐ t ∂μ, ‖u t‖ ≤ ‖(u₀ : L2VF_R3)‖ := by
    have hkin := kineticEnergy_lsc_bound 𝔊 F ν T u₀ galSeq alPkg
    filter_upwards [hkin] with t ht
    have h2 : ‖(alPkg.u t : L2VF_R3)‖ ^ 2 ≤ ‖(u₀ : L2VF_R3)‖ ^ 2 := by nlinarith [ht]
    nlinarith [norm_nonneg (alPkg.u t : L2VF_R3), norm_nonneg (u₀ : L2VF_R3), h2]
  -- weak convergence at a.e. `t`.
  have hweak : ∀ᵐ t ∂μ,
      Tendsto (fun n => toWeakSpace ℝ L2VF_R3 (un n t)) atTop (nhds (toWeakSpace ℝ L2VF_R3 (u t))) := by
    filter_upwards [hperball_ae, ht_nonneg, hu_bound] with t hpb ht0 hub
    refine weak_tendsto_of_inner_tendsto (un · t) (u t) (fun e => ?_)
    exact inner_tendsto_of_perball e (un · t) (u t) ‖(u₀ : L2VF_R3)‖ (norm_nonneg _)
      (fun n => by rw [hun]; exact galerkin_norm_le_u0 𝔊 F ν u₀ (alPkg.φ n) (galSeq (alPkg.φ n)) ht0)
      hub hpb
  -- approximants are `H¹` (`reg_mem`).
  have hH1 : ∀ n (t : ℝ), memH1VF_R3 (un n t) := fun n t => (galSeq (alPkg.φ n)).reg_mem t
  -- (C) the per-component viscous lsc bound, applied at each `j`, at a.e. `t`.
  have hlsc_j : ∀ᵐ t ∂μ, ∀ j : Fin 3,
      viscousLintegrand_j j (u t)
        ≤ Filter.atTop.liminf (fun n => ENNReal.ofReal (viscousIntegrand_j j (un n t))) := by
    filter_upwards [hweak, ht_nonneg] with t hwt ht0
    intro j
    exact viscousLintegrand_le_liminf_of_weak j (un · t) (u t) ‖(u₀ : L2VF_R3)‖ (norm_nonneg _)
      (fun n => by rw [hun]; exact galerkin_norm_le_u0 𝔊 F ν u₀ (alPkg.φ n) (galSeq (alPkg.φ n)) ht0)
      (fun n => hH1 n t) hwt
  -- (D) finiteness of the limit's per-component lower-Lebesgue integrand at a.e. `t`
  -- (`viscousLintegrand_j j (u t) ≤ liminf_n ofReal viscousFormSq(uₙ t) < ∞`), via `reg_bound`+Fatou.
  have hfin_lt : ∀ᵐ t ∂μ,
      Filter.atTop.liminf (fun n => ENNReal.ofReal (viscousFormSq_R3 1 (un n t))) < ⊤ := by
    rw [hμ, hun]; exact liminf_viscousFormSq_lt_top_ae 𝔊 F ν hν T hT u₀ galSeq alPkg
  have hLintegrand_lt : ∀ᵐ t ∂μ, ∀ j : Fin 3, viscousLintegrand_j j (u t) < ⊤ := by
    filter_upwards [hlsc_j, hfin_lt] with t ht hfin
    intro j
    refine lt_of_le_of_lt (le_trans (ht j) ?_) hfin
    refine Filter.liminf_le_liminf (Filter.Eventually.of_forall (fun n => ?_))
    rw [viscousFormSq_eq_sum_integrand,
      ENNReal.ofReal_sum_of_nonneg (fun i _ => viscousIntegrand_j_nonneg i (un n t))]
    exact Finset.single_le_sum
      (fun i _ => (bot_le : (⊥ : ENNReal) ≤ ENNReal.ofReal (viscousIntegrand_j i (un n t))))
      (Finset.mem_univ j)
  -- (E) `memH1VF_R3 (u t)` at a.e. `t`, from the finite weighted-Fourier integrals (the bridge).
  have hmemH1 : ∀ᵐ t ∂μ, memH1VF_R3 (u t) := by
    filter_upwards [hLintegrand_lt] with t hfin
    exact memSobolev_of_finite_weightedFourier_R3 (u t) (fun j => hfin j)
  refine ⟨?_, ?_⟩
  · -- measurability conjunct: on the (a.e.) `H¹` set, `viscousFormSq(u t) = ∑ⱼ (⨆ₖ ‖mulBdd_k‖²)`,
    -- a measurable function of `t` (sup of the continuous-CLM-composed AEStronglyMeasurable `u`).
    exact viscousFormSq_aestronglyMeasurable_of_memH1 alPkg hmemH1
  · filter_upwards [hlsc_j, hmemH1] with t ht hmem
    refine ⟨hmem, ?_⟩
    · -- the spectral lsc bound, summed over `j` (the PROVEN analytic core).
      rw [viscousFormSq_eq_sum_integrand,
        ENNReal.ofReal_sum_of_nonneg (fun j _ => viscousIntegrand_j_nonneg j (u t))]
      calc ∑ j : Fin 3, ENNReal.ofReal (viscousIntegrand_j j (u t))
          ≤ ∑ j : Fin 3, viscousLintegrand_j j (u t) :=
            Finset.sum_le_sum (fun j _ => ofReal_viscousIntegrand_le_lintegrand j (u t))
        _ ≤ ∑ j : Fin 3, Filter.atTop.liminf
              (fun n => ENNReal.ofReal (viscousIntegrand_j j (un n t))) :=
            Finset.sum_le_sum (fun j _ => ht j)
        _ ≤ Filter.atTop.liminf
              (fun n => ∑ j : Fin 3, ENNReal.ofReal (viscousIntegrand_j j (un n t))) :=
            sum_liminf_le_liminf_sum Finset.univ _
        _ = Filter.atTop.liminf
              (fun n => ENNReal.ofReal (viscousFormSq_R3 1 (un n t))) := by
            apply Filter.liminf_congr
            refine Filter.Eventually.of_forall (fun n => ?_)
            rw [viscousFormSq_eq_sum_integrand, ENNReal.ofReal_sum_of_nonneg
              (fun j _ => viscousIntegrand_j_nonneg j (un n t))]

/-- **Integrated viscous lower-semicontinuity bound + energy-class membership (the load-bearing
new lemma of the (b)-route).** Shared by conclusion 1 (energy inequality) and conclusion 4
(energy class) of `galerkin_limit_passage_R3`.

From the n-uniform Galerkin regularity bound (`reg_bound`: `∫₀ᵀ viscousFormSq_R3 ν (uₙ) ≤ ½‖u₀‖²`)
and the strong-L²(-on-balls) convergence to the Aubin–Lions limit `alPkg.u`, the limit lies in
the Leray–Hopf energy class with a dissipation budget no larger than the approximants':

```
(∀ᵐ t, memH1VF_R3 (alPkg.u t)) ∧
IntervalIntegrable (fun s => viscousFormSq_R3 ν (alPkg.u s)) volume 0 T ∧
∫₀ᵀ viscousFormSq_R3 ν (alPkg.u s) ≤ ½‖u₀‖²
```

The mechanism is **weak lower-semicontinuity of the viscous (Dirichlet) seminorm** under the
strong-L² limit. The genuinely-new analytic content — the *pointwise* weak-H¹ lsc — is isolated
in `viscous_pointwise_lsc`; this lemma assembles the integrated bound and the energy-class
membership from it **axiom-free**, by Fatou's lemma in time (`lintegral_liminf_le`) against the
`liminf` of the approximant dissipations, which `reg_bound` caps by `½‖u₀‖²`. -/
theorem viscous_lsc_under_strongL2 (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T) (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n)
    (alPkg : AubinLionsPackage_R3 𝔊 F ν T u₀ galSeq) :
    (∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)), memH1VF_R3 (alPkg.u t : L2VF_R3)) ∧
    IntervalIntegrable (fun s => viscousFormSq_R3 ν (alPkg.u s : L2VF_R3)) volume 0 T ∧
    ∫ s in (0 : ℝ)..T, viscousFormSq_R3 ν (alPkg.u s : L2VF_R3) ≤
      (1 / 2 : ℝ) * ‖(u₀ : L2VF_R3)‖ ^ 2 := by
  classical
  set μ : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) T) with hμ
  haveI hμfin : IsFiniteMeasure μ := by
    rw [hμ]; refine isFiniteMeasure_restrict.2 ?_
    rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  -- The pointwise weak-H¹ lsc (proved via the Fourier–Plancherel route) + measurability of the
  -- limit's viscous form.
  obtain ⟨hmeas_u, hptwise⟩ := viscous_pointwise_lsc 𝔊 F ν T hν hT u₀ galSeq alPkg
  -- Abbreviations for the `ν = 1` viscous forms (scaling by `ν` is folded in at the end).
  set g : ℝ → ℝ := fun t => viscousFormSq_R3 1 (alPkg.u t : L2VF_R3) with hg
  set gn : ℕ → ℝ → ℝ :=
    fun n t => viscousFormSq_R3 1 ((galSeq (alPkg.φ n)).u t : L2VF_R3) with hgn
  -- Nonnegativity of every viscous form (`ν = 1 ≥ 0`).
  have hg_nonneg : ∀ t, 0 ≤ g t := fun t => viscousFormSq_R3_nonneg (by norm_num) _
  have hgn_nonneg : ∀ n t, 0 ≤ gn n t := fun n t => viscousFormSq_R3_nonneg (by norm_num) _
  -- (1) a.e. `H¹` membership of the limit — directly the first pointwise conjunct.
  have hmem : ∀ᵐ t ∂μ, memH1VF_R3 (alPkg.u t : L2VF_R3) := by
    rw [hμ]; filter_upwards [hptwise] with t ht; exact ht.1
  -- (2) the pointwise `ENNReal` bound `ofReal (g t) ≤ liminf_n ofReal (gn n t)` a.e.
  have hGbound : ∀ᵐ t ∂μ,
      ENNReal.ofReal (g t) ≤ Filter.atTop.liminf (fun n => ENNReal.ofReal (gn n t)) := by
    rw [hμ]; filter_upwards [hptwise] with t ht; exact ht.2
  -- ════ Approximant-side: each `gn n` is continuous on `Ici 0 ⊇ Icc 0 T`, hence
  -- a.e.-measurable and interval-integrable on `[0,T]`, with `∫₀ᵀ ν·gn n ≤ ½‖u₀‖²` (`reg_bound`). ════
  have hgn_cont : ∀ n, ContinuousOn (gn n) (Set.Ici (0 : ℝ)) :=
    fun n => viscousFormSq_curve_continuousOn 𝔊 F ν u₀ (alPkg.φ n) (galSeq (alPkg.φ n))
  have hgn_meas : ∀ n, AEMeasurable (gn n) μ := by
    intro n
    rw [hμ]
    refine (ContinuousOn.aemeasurable ((hgn_cont n).mono ?_) measurableSet_Icc)
    intro t ht; exact ht.1
  have hgn_int : ∀ n, ∫ s in (0 : ℝ)..T, gn n s ≤ ν⁻¹ * ((1 / 2 : ℝ) * ‖(u₀ : L2VF_R3)‖ ^ 2) := by
    intro n
    have hrb := (galSeq (alPkg.φ n)).reg_bound T hT
    -- `reg_bound` is in `ν`-form; rescale to the `ν = 1` integrand.
    have hscale : ∀ s, viscousFormSq_R3 ν ((galSeq (alPkg.φ n)).u s : L2VF_R3)
        = ν * gn n s := by
      intro s; rw [hgn, viscousFormSq_R3_eq_smul, smul_eq_mul]
    rw [intervalIntegral.integral_congr (g := fun s => ν * gn n s) (fun s _ => hscale s),
      intervalIntegral.integral_const_mul] at hrb
    rw [le_inv_mul_iff₀ hν]; exact hrb
  -- ════ Fatou in time: `∫⁻ ofReal g ≤ liminf_n ∫⁻ ofReal (gn n) ≤ ν⁻¹·½‖u₀‖² < ∞`. ════
  -- Measurability of the `ENNReal`-lifted integrands.
  have hg_aem : AEMeasurable g μ := by
    rw [hg]; exact hmeas_u.aemeasurable
  have hGn_meas : ∀ n, AEMeasurable (fun t => ENNReal.ofReal (gn n t)) μ :=
    fun n => (hgn_meas n).ennreal_ofReal
  -- The lintegral Fatou bound.
  have hlin_fatou : ∫⁻ t, ENNReal.ofReal (g t) ∂μ
      ≤ Filter.atTop.liminf (fun n => ∫⁻ t, ENNReal.ofReal (gn n t) ∂μ) := by
    calc ∫⁻ t, ENNReal.ofReal (g t) ∂μ
        ≤ ∫⁻ t, Filter.atTop.liminf (fun n => ENNReal.ofReal (gn n t)) ∂μ :=
          lintegral_mono_ae hGbound
      _ ≤ Filter.atTop.liminf (fun n => ∫⁻ t, ENNReal.ofReal (gn n t) ∂μ) :=
          lintegral_liminf_le' hGn_meas
  -- Each approximant lintegral equals its (nonneg) Bochner interval integral, capped by reg_bound.
  have hGn_eq : ∀ n,
      ∫⁻ t, ENNReal.ofReal (gn n t) ∂μ
        = ENNReal.ofReal (∫ s in (0 : ℝ)..T, gn n s) := by
    intro n
    have hint : IntegrableOn (gn n) (Set.Icc (0 : ℝ) T) volume := by
      refine (ContinuousOn.integrableOn_Icc ((hgn_cont n).mono ?_))
      intro t ht; exact ht.1
    rw [hμ, ← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall (fun t => hgn_nonneg n t))]
    rw [intervalIntegral.integral_of_le hT.le,
      ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  -- Bound each approximant lintegral by the n-uniform constant.
  have hGn_cap : ∀ n,
      ∫⁻ t, ENNReal.ofReal (gn n t) ∂μ
        ≤ ENNReal.ofReal (ν⁻¹ * ((1 / 2 : ℝ) * ‖(u₀ : L2VF_R3)‖ ^ 2)) := by
    intro n; rw [hGn_eq n]; exact ENNReal.ofReal_le_ofReal (hgn_int n)
  have hliminf_cap :
      Filter.atTop.liminf (fun n => ∫⁻ t, ENNReal.ofReal (gn n t) ∂μ)
        ≤ ENNReal.ofReal (ν⁻¹ * ((1 / 2 : ℝ) * ‖(u₀ : L2VF_R3)‖ ^ 2)) := by
    refine le_trans liminf_le_limsup ?_
    exact limsup_le_of_le isCobounded_le_of_bot (Filter.Eventually.of_forall hGn_cap)
  have hlin_cap : ∫⁻ t, ENNReal.ofReal (g t) ∂μ
      ≤ ENNReal.ofReal (ν⁻¹ * ((1 / 2 : ℝ) * ‖(u₀ : L2VF_R3)‖ ^ 2)) :=
    le_trans hlin_fatou hliminf_cap
  -- ════ From the finite lintegral: integrability of `g` and the real integral bound. ════
  have hg_int_lt : ∫⁻ t, ENNReal.ofReal (g t) ∂μ < ⊤ :=
    lt_of_le_of_lt hlin_cap ENNReal.ofReal_lt_top
  have hg_integrable : Integrable g μ := by
    refine ⟨hmeas_u, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hg_nonneg)]
    exact hg_int_lt
  -- The real integral of `g` over `Icc 0 T`, via `ofReal`-lintegral identity.
  have hg_int_eq : ENNReal.ofReal (∫ t, g t ∂μ) = ∫⁻ t, ENNReal.ofReal (g t) ∂μ :=
    ofReal_integral_eq_lintegral_ofReal hg_integrable (Filter.Eventually.of_forall hg_nonneg)
  have hg_int_bound : ∫ t, g t ∂μ ≤ ν⁻¹ * ((1 / 2 : ℝ) * ‖(u₀ : L2VF_R3)‖ ^ 2) := by
    have hnn : (0 : ℝ) ≤ ν⁻¹ * ((1 / 2 : ℝ) * ‖(u₀ : L2VF_R3)‖ ^ 2) := by positivity
    have := hg_int_eq ▸ hlin_cap
    rwa [ENNReal.ofReal_le_ofReal_iff hnn] at this
  -- Translate `μ`-integral back to the `intervalIntegral` over `[0,T]`.
  have hg_interval : IntervalIntegrable g volume 0 T := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le]
    have hIcc : IntegrableOn g (Set.Icc (0 : ℝ) T) volume := by
      rw [IntegrableOn, ← hμ]; exact hg_integrable
    exact hIcc.mono_set Set.Ioc_subset_Icc_self
  have hg_interval_eq : ∫ s in (0 : ℝ)..T, g s = ∫ t, g t ∂μ := by
    rw [hμ, intervalIntegral.integral_of_le hT.le, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  -- ════ Assemble the three conclusions (rescaling `ν = 1` ⟹ `ν`). ════
  refine ⟨hmem, ?_, ?_⟩
  · -- IntervalIntegrable of the `ν`-form: constant-multiple of the `ν = 1` form.
    have hscale : (fun s => viscousFormSq_R3 ν (alPkg.u s : L2VF_R3)) = fun s => ν * g s := by
      funext s; rw [hg, viscousFormSq_R3_eq_smul, smul_eq_mul]
    rw [hscale]; exact hg_interval.const_mul ν
  · -- The `ν`-form integral bound: `∫ ν·g = ν·∫ g ≤ ν·(ν⁻¹·½‖u₀‖²) = ½‖u₀‖²`.
    have hscale : ∀ s, viscousFormSq_R3 ν (alPkg.u s : L2VF_R3) = ν * g s := by
      intro s; rw [hg, viscousFormSq_R3_eq_smul, smul_eq_mul]
    rw [intervalIntegral.integral_congr (g := fun s => ν * g s) (fun s _ => hscale s),
      intervalIntegral.integral_const_mul, hg_interval_eq]
    calc ν * ∫ t, g t ∂μ
        ≤ ν * (ν⁻¹ * ((1 / 2 : ℝ) * ‖(u₀ : L2VF_R3)‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left hg_int_bound hν.le
      _ = (1 / 2 : ℝ) * ‖(u₀ : L2VF_R3)‖ ^ 2 := by
          rw [← mul_assoc, mul_inv_cancel₀ hν.ne', one_mul]


end LerayHopf
