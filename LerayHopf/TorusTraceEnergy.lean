/-
# LerayHopf.TorusTraceEnergy — conjuncts 1 + 3: energy inequality and initial trace on 𝕋³

**Milestone:** Torus `galerkin_limit_passage` removal, coupled pillar (1) + (3).

This file constructs the **weakly-continuous-into-H representative** `u` of the
Aubin–Lions limit `alPkg.u` and proves, for that single representative:

- **(1) pointwise `∀t` energy inequality:** for `t ∈ [0, T]`,
  `½‖u t‖² + ∫₀ᵗ viscousFormSq ν (u s) ds ≤ ½‖u₀‖²`;
- **(3) strong initial trace:** `Tendsto (fun t => (u t : L2VF)) (𝓝[≥] 0) (𝓝 u₀)`.

Neither conjunct is null-set-invariant, so they genuinely fail for the raw `alPkg.u`
(pinned only a.e.); both ride on the same representative — a null-set redefinition
repairing one breaks the other.  This is the torus twin of the R3 trace-route spike
(`docs/scratch/trace-route-spike.md`, branch `lane-limitpassage-p0-spike`, verdict GO).

## Route (kernel-free; no Bochner time-Sobolev, no `W1pTime` witness)

1. **Per-test uniform derivative bound.**  For a band-limited test `w`
   (`velocityProjection_n n₀ w = w`) and every Galerkin level `n ≥ n₀`, the scalar
   curve `t ↦ ⟪uₙ t, w⟫` has derivative `-(ν·stokesTestPairing(uₙ t, w) + b(uₙ t, uₙ t, w))`
   (from `u_hasDeriv`/`u_ode` via `velocityProjection_n_eq_of_le`), bounded on `[0, T]`
   by `L(w) := ν·Cs(w)·‖u₀‖ + Cb(w)·‖u₀‖²` uniformly in `n` — the torus advantage:
   the R3 scheme-nesting blocker is `velocityProjection_n_eq_of_le` here, and
   `F.b_bound` fires on `IsGalerkinTest` directly.
2. **A.e.-strong subsequence.**  `alPkg.strong_convergence` (eLpNorm) →
   `tendstoInMeasure_of_tendsto_eLpNorm` → `TendstoInMeasure.exists_seq_tendsto_ae`:
   a sub-subsequence converging strongly in `L2VF` at a.e. `t ∈ [0, T]`.
3. **Everywhere per-test convergence.**  The equi-Lipschitz family `t ↦ ⟪uₖ t, w⟫`
   converges on the full-measure (hence dense) a.e. set, so it is Cauchy at *every*
   `t ∈ [0, T]`; the endpoint value is pinned by `u_initial` + `velocityProjection_n_tendsto`
   (`⟪uₖ 0, w⟫ = ⟪P_{n_k} u₀, w⟫ → ⟪u₀, w⟫`).
4. **Riesz assembly.**  For each `t ∈ [0, T]`, `z ↦ lim_k ⟪uₖ t, z⟫` is a bounded linear
   functional (Galerkin-test density in `L2Sigma` + orthogonal complement + `‖uₖ t‖ ≤ ‖u₀‖`);
   `InnerProductSpace.toDual.symm` gives `u t ∈ L2VF`, membership in `L2Sigma` by the
   orthogonal-projection argument (`isClosed_L2Sigma`).  `u` is weakly continuous on `[0, T]`,
   `u 0 = u₀`, and `u = alPkg.u` a.e. (weak limit = strong limit on the a.e. set).
5. **Galerkin energy identity** (from the abstract `GalerkinSolutionData` fields):
   `½‖uₙ t‖² + ∫₀ᵗ viscousFormSq ν (uₙ s) ds = ½‖Pₙ u₀‖² ≤ ½‖u₀‖²`
   (FTC-2 on `[0, t]` + `stokesTestPairing_diag` + `b_self_zero` + `velocityProjection_n_norm_le`).
6. **Conjunct (1).**  Kinetic term: norm weak-lsc at every `t` (inner-product liminf).
   Dissipation term: spatial lower-semicontinuity of the viscous ENNReal sum under strong
   `L2VF` convergence at a.e. `s`, then Fatou in `s` (shared viscous-lsc engine),
   then liminf superadditivity against the identity of step 5.
7. **Conjunct (3).**  Weak trace at `0⁺` (steps 3–4) + `limsup_{t→0⁺} ‖u t‖ ≤ ‖u₀‖`
   (conjunct 1) + norm weak-lsc → `‖u t‖ → ‖u₀‖` → strong via `norm_sub_sq_real`.

## Trap guards (from the R3 spike)

- NO `W1pTime … 2 2` witness for the limit (false in 3D); NO import of
  `LerayHopf/Bochner/TimeSobolev*.lean` (`w1pTime_continuous_in_H` stays quarantined).
- All statements use the forward-only `0 ≤ t → t ≤ T` window, matching `u_hasDeriv`/`u_ode`.

## Axioms

No new axioms.
-/

import LerayHopf.TorusLimitPassage
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

namespace LerayHopf

open MeasureTheory Filter Topology intervalIntegral
open scoped ENNReal

/-! ### Foundation: viscous-form scaling -/

/-- `viscousFormSq ν u = ν * viscousFormSq 1 u`: the `ν`-weighted viscous form is the
`ν`-scale of the unweighted one (both are `ν * Σ` by definition). -/
theorem viscousFormSq_eq_mul (ν : ℝ) (u : L2VF) :
    viscousFormSq ν u = ν * viscousFormSq 1 u := by
  unfold viscousFormSq
  ring

/-! ### Foundation: band-limited viscous pairing (box-sum form and L²-bound)

Private clones of `TorusLimitPassage`'s `stokesTestPairing_eq_boxSum` / `stokes_abs_le`
(those are `private` there; one writer per file, so we re-prove locally). -/

/-- `stokesTestPairing v w` as a finite `fourierBox n₀` sum, for band-limited `w`. -/
private theorem stokes_boxSum (n₀ : ℕ) (w : L2VF)
    (hn₀ : velocityProjection_n n₀ w = w) (v : L2VF) :
    stokesTestPairing v w =
      ∑ j : Fin 3, ∑ k ∈ fourierBox n₀,
        ((2 * Real.pi) ^ 2 * ∑ i : Fin 3, (k i : ℝ) ^ 2) *
          (mFourierCoeff3 (L2VF_projComponentC j v) k *
            starRingEnd ℂ (mFourierCoeff3 (L2VF_projComponentC j w) k)).re := by
  unfold stokesTestPairing; congr 1; ext j
  apply tsum_eq_sum
  intro k hk
  simp [coeff_zero_outside_box n₀ w hn₀ j k hk]

/-- **Viscous-form L²-bound at a band-limited test `w`:** `|stokesTestPairing v w| ≤ C · ‖v‖`. -/
private theorem stokes_abs_le' (n₀ : ℕ) (w : L2VF)
    (hn₀ : velocityProjection_n n₀ w = w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : L2VF, |stokesTestPairing v w| ≤ C * ‖v‖ := by
  classical
  refine ⟨∑ j : Fin 3, ∑ k ∈ fourierBox n₀,
      |(2 * Real.pi) ^ 2 * ∑ i : Fin 3, (k i : ℝ) ^ 2| *
        (‖fourierCoeffCLM k‖ * ‖L2VF_projComponentC j‖) *
        ‖mFourierCoeff3 (L2VF_projComponentC j w) k‖, ?_, ?_⟩
  · exact Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => by positivity
  · intro v
    rw [stokes_boxSum n₀ w hn₀ v]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun j _ => ?_
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun k _ => ?_
    set cjk : ℝ := (2 * Real.pi) ^ 2 * ∑ i : Fin 3, (k i : ℝ) ^ 2 with hcjk
    set cv : ℂ := mFourierCoeff3 (L2VF_projComponentC j v) k with hcv
    set cw : ℂ := mFourierCoeff3 (L2VF_projComponentC j w) k with hcw
    rw [abs_mul]
    have hre : |(cv * starRingEnd ℂ cw).re| ≤ ‖cv‖ * ‖cw‖ := by
      calc |(cv * starRingEnd ℂ cw).re| ≤ ‖cv * starRingEnd ℂ cw‖ := Complex.abs_re_le_norm _
        _ = ‖cv‖ * ‖cw‖ := by rw [norm_mul, RCLike.norm_conj]
    have hcvbd : ‖cv‖ ≤ ‖fourierCoeffCLM k‖ * ‖L2VF_projComponentC j‖ * ‖v‖ := by
      rw [hcv, ← fourierCoeffCLM_apply]
      calc ‖fourierCoeffCLM k (L2VF_projComponentC j v)‖
          ≤ ‖fourierCoeffCLM k‖ * ‖L2VF_projComponentC j v‖ := (fourierCoeffCLM k).le_opNorm _
        _ ≤ ‖fourierCoeffCLM k‖ * (‖L2VF_projComponentC j‖ * ‖v‖) := by
            gcongr; exact (L2VF_projComponentC j).le_opNorm _
        _ = ‖fourierCoeffCLM k‖ * ‖L2VF_projComponentC j‖ * ‖v‖ := by ring
    calc |cjk| * |(cv * starRingEnd ℂ cw).re|
        ≤ |cjk| * (‖cv‖ * ‖cw‖) := by gcongr
      _ ≤ |cjk| * ((‖fourierCoeffCLM k‖ * ‖L2VF_projComponentC j‖ * ‖v‖) * ‖cw‖) := by
          gcongr
      _ = |cjk| * (‖fourierCoeffCLM k‖ * ‖L2VF_projComponentC j‖) * ‖cw‖ * ‖v‖ := by ring

/-! ### Foundation: uniform Galerkin norm bound -/

/-- **Uniform Galerkin H-bound:** `‖uₙ(t)‖ ≤ ‖u₀‖` for all `t ≥ 0` (from `energy_bound` +
non-expansiveness of the projection).  Torus analogue of R3's `galerkin_norm_le_u0`. -/
theorem torus_galerkin_norm_le_u0 (F : Torus3NSForms) (ν : ℝ) (u₀ : L2Sigma) (n : ℕ)
    (gs : GalerkinSolutionData F ν u₀ n) (t : ℝ) (ht : 0 ≤ t) :
    ‖(gs.u t : L2VF)‖ ≤ ‖(u₀ : L2VF)‖ := by
  have hE := gs.energy_bound t ht
  have hP := Torus.velocityProjection_n_norm_le n (u₀ : L2VF)
  have h1 : ‖(gs.u t : L2VF)‖ ^ 2 ≤ ‖velocityProjection_n n (u₀ : L2VF)‖ ^ 2 := by linarith
  have h2 : ‖velocityProjection_n n (u₀ : L2VF)‖ ^ 2 ≤ ‖(u₀ : L2VF)‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hP 2
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (by norm_num)).mp (h1.trans h2)

/-! ### Step 5: Galerkin energy identity (forward-only, from abstract fields)

The existing `abstract_galerkin_energy_inequality` requires the ODE law at ALL `t : ℝ`;
`GalerkinSolutionData` supplies it forward-only (`0 ≤ t`), so we derive the identity
directly on `[0, t]`. -/

/-- Continuity of the Galerkin curve on `[0, ∞)` (from `u_hasDeriv`). -/
private theorem galerkin_curve_continuousOn (F : Torus3NSForms) (ν : ℝ) (u₀ : L2Sigma) (n : ℕ)
    (gs : GalerkinSolutionData F ν u₀ n) :
    ContinuousOn (fun s => (gs.u s : L2VF)) (Set.Ici 0) :=
  fun s hs => ((gs.u_hasDeriv s hs).continuousAt).continuousWithinAt

/-- Continuity of the viscous dissipation along the Galerkin curve on `[0, ∞)`:
band-limited (level `n`) curves make `viscousFormSq` a finite box sum. -/
private theorem galerkin_viscous_continuousOn (F : Torus3NSForms) (ν : ℝ) (u₀ : L2Sigma) (n : ℕ)
    (gs : GalerkinSolutionData F ν u₀ n) :
    ContinuousOn (fun s => viscousFormSq ν (gs.u s : L2VF)) (Set.Ici 0) := by
  have hcurve := galerkin_curve_continuousOn F ν u₀ n gs
  have hfin : ∀ s : ℝ, viscousFormSq ν (gs.u s : L2VF) =
      ν * ∑ j : Fin 3, ∑ k ∈ fourierBox n,
        ((2 * Real.pi) ^ 2 * ∑ i : Fin 3, (k i : ℝ) ^ 2) *
          (mFourierCoeff3 (L2VF_projComponentC j (gs.u s : L2VF)) k *
            starRingEnd ℂ (mFourierCoeff3 (L2VF_projComponentC j (gs.u s : L2VF)) k)).re := by
    intro s
    rw [viscousFormSq_eq_mul, ← stokesTestPairing_diag,
      stokes_boxSum n (gs.u s : L2VF) (gs.u_inVn s).symm]
  simp only [hfin]
  refine continuousOn_const.mul ?_
  apply continuousOn_finsetSum Finset.univ; intro j _
  apply continuousOn_finsetSum (fourierBox n); intro k _
  refine continuousOn_const.mul ?_
  have hcoeff : ContinuousOn
      (fun s => mFourierCoeff3 (L2VF_projComponentC j (gs.u s : L2VF)) k) (Set.Ici 0) := by
    have heq : (fun s => mFourierCoeff3 (L2VF_projComponentC j (gs.u s : L2VF)) k)
        = fun s => fourierCoeffCLM k (L2VF_projComponentC j (gs.u s : L2VF)) := by
      funext s; rw [fourierCoeffCLM_apply]
    rw [heq]
    exact ((fourierCoeffCLM k).continuous.comp
      (L2VF_projComponentC j).continuous).comp_continuousOn hcurve
  have hconj : ContinuousOn
      (fun s => starRingEnd ℂ (mFourierCoeff3 (L2VF_projComponentC j (gs.u s : L2VF)) k))
      (Set.Ici 0) :=
    (Complex.conjCLE.continuous.comp_continuousOn hcoeff)
  exact Complex.continuous_re.comp_continuousOn (hcoeff.mul hconj)

/-- **Galerkin energy identity (forward-only):** for `t ≥ 0`,
`½‖uₙ(t)‖² + ∫₀ᵗ viscousFormSq ν (uₙ(s)) ds = ½‖Pₙ u₀‖²`.

Derivation: `u_ode` tested against `w := uₙ(t)` itself (admissible by `u_inVn`),
`b(u,u,u) = 0` (`b_self_zero`), the Stokes diagonal (`stokesTestPairing_diag`), and FTC-2. -/
theorem torus_galerkin_energy_identity (F : Torus3NSForms) (ν : ℝ) (u₀ : L2Sigma) (n : ℕ)
    (gs : GalerkinSolutionData F ν u₀ n) (t : ℝ) (ht : 0 ≤ t) :
    (1 / 2 : ℝ) * ‖(gs.u t : L2VF)‖ ^ 2 +
      ∫ s in (0 : ℝ)..t, viscousFormSq ν (gs.u s : L2VF) =
    (1 / 2 : ℝ) * ‖velocityProjection_n n (u₀ : L2VF)‖ ^ 2 := by
  -- The energy `E(s) := ½‖uₙ(s)‖²` has derivative `-viscousFormSq ν (uₙ(s))` at each `s ≥ 0`.
  have hE : ∀ s ∈ Set.uIcc (0 : ℝ) t,
      HasDerivAt (fun r => (1 / 2 : ℝ) * ‖(gs.u r : L2VF)‖ ^ 2)
        (-(viscousFormSq ν (gs.u s : L2VF))) s := by
    rw [Set.uIcc_of_le ht]
    intro s hs
    have hs0 : (0 : ℝ) ≤ s := hs.1
    have hd := gs.u_hasDeriv s hs0
    have hn2 : HasDerivAt (fun r => ‖(gs.u r : L2VF)‖ ^ 2)
        (2 * inner (𝕜 := ℝ) (gs.u s : L2VF) (deriv (fun r => (gs.u r : L2VF)) s)) s :=
      hd.norm_sq
    -- Scale by ½ via `.inner` with the constant curve (as in `abstract_galerkin_energy_identity`).
    have h2' := (hasDerivAt_const s (1 / 2 : ℝ)).inner (𝕜 := ℝ) hn2
    simp at h2'
    have hfun : (fun r => ‖(gs.u r : L2VF)‖ ^ 2 * 2⁻¹)
        = fun r => (1 / 2 : ℝ) * ‖(gs.u r : L2VF)‖ ^ 2 := by
      funext r; ring
    -- Identify the derivative value via the ODE at test `w := uₙ(s)`.
    have hode := gs.u_ode s hs0 (gs.u s) (gs.u_inVn s)
    have hb := F.b_self_zero (gs.u s)
    have hdiag : stokesTestPairing (gs.u s : L2VF) (gs.u s : L2VF)
        = viscousFormSq 1 (gs.u s : L2VF) := stokesTestPairing_diag _
    have hval : (2 : ℝ) * inner (𝕜 := ℝ) (gs.u s : L2VF)
          (deriv (fun r => (gs.u r : L2VF)) s) * 2⁻¹
        = -(viscousFormSq ν (gs.u s : L2VF)) := by
      have hcomm : inner (𝕜 := ℝ) (gs.u s : L2VF) (deriv (fun r => (gs.u r : L2VF)) s)
          = inner (𝕜 := ℝ) (deriv (fun r => (gs.u r : L2VF)) s) (gs.u s : L2VF) :=
        real_inner_comm _ _
      rw [hdiag, hb] at hode
      rw [viscousFormSq_eq_mul, hcomm]
      linarith
    rw [hfun, hval] at h2'
    exact h2'
  -- Interval integrability of the dissipation (continuous on `[0, t] ⊆ [0, ∞)`).
  have hInt : IntervalIntegrable (fun s => viscousFormSq ν (gs.u s : L2VF)) volume 0 t := by
    have hcont : ContinuousOn (fun s => viscousFormSq ν (gs.u s : L2VF)) (Set.Icc 0 t) :=
      (galerkin_viscous_continuousOn F ν u₀ n gs).mono
        (fun s hs => hs.1)
    exact hcont.intervalIntegrable_of_Icc ht
  -- FTC-2 on `[0, t]`.
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun r => (1 / 2 : ℝ) * ‖(gs.u r : L2VF)‖ ^ 2)
    (f' := fun s => -(viscousFormSq ν (gs.u s : L2VF))) hE hInt.neg
  rw [intervalIntegral.integral_neg] at hFTC
  -- Initial value: `uₙ(0) = Pₙ u₀`.
  have h0 : (gs.u 0 : L2VF) = velocityProjection_n n (u₀ : L2VF) := by
    rw [gs.u_initial]
  rw [h0] at hFTC
  linarith

/-- **Galerkin energy inequality against `‖u₀‖`:** for `t ≥ 0`,
`½‖uₙ(t)‖² + ∫₀ᵗ viscousFormSq ν (uₙ(s)) ds ≤ ½‖u₀‖²`. -/
theorem torus_galerkin_energy_le (F : Torus3NSForms) (ν : ℝ) (u₀ : L2Sigma) (n : ℕ)
    (gs : GalerkinSolutionData F ν u₀ n) (t : ℝ) (ht : 0 ≤ t) :
    (1 / 2 : ℝ) * ‖(gs.u t : L2VF)‖ ^ 2 +
      ∫ s in (0 : ℝ)..t, viscousFormSq ν (gs.u s : L2VF) ≤
    (1 / 2 : ℝ) * ‖(u₀ : L2VF)‖ ^ 2 := by
  rw [torus_galerkin_energy_identity F ν u₀ n gs t ht]
  have hP := Torus.velocityProjection_n_norm_le n (u₀ : L2VF)
  have := pow_le_pow_left₀ (norm_nonneg _) hP 2
  linarith

end LerayHopf
