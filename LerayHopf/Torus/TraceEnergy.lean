/-
# LerayHopf.Torus.TraceEnergy — conjuncts 1 + 3: energy inequality and initial trace on 𝕋³

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

import LerayHopf.Torus.LimitPassage
import LerayHopf.Bochner.WeakLimitToolkit
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Topology.Algebra.Order.LiminfLimsup

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
    rw [viscousFormSq_eq_mul, ← Torus.stokesTestPairing_diag,
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
    simp only [Torus3NSForms.core_b] at hode
    have hb := F.b_self_zero (gs.u s)
    have hdiag : stokesTestPairing (gs.u s : L2VF) (gs.u s : L2VF)
        = viscousFormSq 1 (gs.u s : L2VF) := Torus.stokesTestPairing_diag _
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

/-! ### Step 1: per-test scalar derivative and uniform Lipschitz bound -/

/-- The scalar test curve `t ↦ ⟪uₙ(t), w⟫` has derivative
`-(ν·stokesTestPairing(uₙ t, w) + b(uₙ t, uₙ t, w))` at forward times, for tests fixed at
level `n` (from `u_hasDeriv` + `u_ode`). -/
private theorem perTest_hasDerivAt (F : Torus3NSForms) (ν : ℝ) (u₀ : L2Sigma) (n : ℕ)
    (gs : GalerkinSolutionData F ν u₀ n) (w : L2Sigma)
    (hwn : velocityProjection_n n (w : L2VF) = (w : L2VF)) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt (fun s => inner (𝕜 := ℝ) ((gs.u s : L2VF)) (w : L2VF))
      (-(ν * stokesTestPairing (gs.u t : L2VF) (w : L2VF) + F.b (gs.u t) (gs.u t) w)) t := by
  have hda := (gs.u_hasDeriv t ht).inner (𝕜 := ℝ) (hasDerivAt_const t (w : L2VF))
  simp only [inner_zero_right, zero_add] at hda
  have hode := gs.u_ode t ht w hwn.symm
  simp only [Torus3NSForms.core_b] at hode
  have hval : inner (𝕜 := ℝ) (deriv (fun s => (gs.u s : L2VF)) t) (w : L2VF)
      = -(ν * stokesTestPairing (gs.u t : L2VF) (w : L2VF) + F.b (gs.u t) (gs.u t) w) := by
    linarith
  rwa [hval] at hda

/-- **Per-test uniform Lipschitz bound** (uniform in the Galerkin level `n ≥ n₀`): for a
test `w` fixed at level `n₀`, all Galerkin scalar curves at levels `n ≥ n₀` are
`L(w)`-Lipschitz on `[0, ∞)`, with `L(w) = ν·Cs(w)·‖u₀‖ + Cb(w)·‖u₀‖²` independent of `n`.
This is the torus form of R3-spike obligation 2; the level-promotion is
`velocityProjection_n_eq_of_le` (the R3 nesting blocker is absent here). -/
private theorem perTest_lipschitz (F : Torus3NSForms) (ν : ℝ) (hν : 0 < ν) (u₀ : L2Sigma)
    (galSeq : ∀ n, GalerkinSolutionData F ν u₀ n) (w : L2Sigma) (n₀ : ℕ)
    (hn₀ : velocityProjection_n n₀ (w : L2VF) = (w : L2VF)) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ n, n₀ ≤ n → ∀ s ∈ Set.Ici (0 : ℝ), ∀ t ∈ Set.Ici (0 : ℝ),
      |inner (𝕜 := ℝ) (((galSeq n).u t : L2VF)) (w : L2VF)
        - inner (𝕜 := ℝ) (((galSeq n).u s : L2VF)) (w : L2VF)| ≤ L * |t - s| := by
  obtain ⟨Cs, hCs0, hCs⟩ := stokes_abs_le' n₀ (w : L2VF) hn₀
  obtain ⟨Cb, hCb⟩ := F.b_bound w ⟨n₀, hn₀⟩
  set Cb' : ℝ := |Cb| with hCb'
  have hCb'0 : 0 ≤ Cb' := abs_nonneg _
  have hCb'bound : ∀ u v : L2Sigma, |F.b u v w| ≤ Cb' * ‖(u : L2VF)‖ * ‖(v : L2VF)‖ := by
    intro u v
    refine (hCb u v).trans ?_
    have h1 := le_abs_self Cb
    nlinarith [norm_nonneg (u : L2VF), norm_nonneg (v : L2VF),
      mul_nonneg (norm_nonneg (u : L2VF)) (norm_nonneg (v : L2VF))]
  set L : ℝ := ν * Cs * ‖(u₀ : L2VF)‖ + Cb' * ‖(u₀ : L2VF)‖ ^ 2 with hLdef
  have hL0 : 0 ≤ L := by
    have h1 : 0 ≤ ν * Cs * ‖(u₀ : L2VF)‖ :=
      mul_nonneg (mul_nonneg hν.le hCs0) (norm_nonneg _)
    have h2 : 0 ≤ Cb' * ‖(u₀ : L2VF)‖ ^ 2 := mul_nonneg hCb'0 (sq_nonneg _)
    linarith
  refine ⟨L, hL0, fun n hn s hs t ht => ?_⟩
  set gs := galSeq n with hgs
  have hwn : velocityProjection_n n (w : L2VF) = (w : L2VF) :=
    TorusConvectionExtension.velocityProjection_n_eq_of_le hn (w : L2VF) hn₀
  -- uniform derivative bound on `[0, ∞)`
  have hbound : ∀ r ∈ Set.Ici (0 : ℝ),
      ‖-(ν * stokesTestPairing (gs.u r : L2VF) (w : L2VF) + F.b (gs.u r) (gs.u r) w)‖
        ≤ L := by
    intro r hr
    rw [Real.norm_eq_abs, abs_neg]
    have hnorm := torus_galerkin_norm_le_u0 F ν u₀ n gs r hr
    have h1 : |ν * stokesTestPairing (gs.u r : L2VF) (w : L2VF)|
        ≤ ν * Cs * ‖(u₀ : L2VF)‖ := by
      rw [abs_mul, abs_of_pos hν, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ hν.le
      exact (hCs _).trans (mul_le_mul_of_nonneg_left hnorm hCs0)
    have h2 : |F.b (gs.u r) (gs.u r) w| ≤ Cb' * ‖(u₀ : L2VF)‖ ^ 2 := by
      refine (hCb'bound (gs.u r) (gs.u r)).trans ?_
      have hn0 : 0 ≤ ‖(gs.u r : L2VF)‖ := norm_nonneg _
      have hu0 : 0 ≤ ‖(u₀ : L2VF)‖ := norm_nonneg _
      have hsq : ‖(gs.u r : L2VF)‖ * ‖(gs.u r : L2VF)‖
          ≤ ‖(u₀ : L2VF)‖ * ‖(u₀ : L2VF)‖ := mul_le_mul hnorm hnorm hn0 hu0
      calc Cb' * ‖(gs.u r : L2VF)‖ * ‖(gs.u r : L2VF)‖
          = Cb' * (‖(gs.u r : L2VF)‖ * ‖(gs.u r : L2VF)‖) := by ring
        _ ≤ Cb' * (‖(u₀ : L2VF)‖ * ‖(u₀ : L2VF)‖) := mul_le_mul_of_nonneg_left hsq hCb'0
        _ = Cb' * ‖(u₀ : L2VF)‖ ^ 2 := by ring
    calc |ν * stokesTestPairing (gs.u r : L2VF) (w : L2VF) + F.b (gs.u r) (gs.u r) w|
        ≤ |ν * stokesTestPairing (gs.u r : L2VF) (w : L2VF)|
          + |F.b (gs.u r) (gs.u r) w| := abs_add_le _ _
      _ ≤ L := by rw [hLdef]; linarith
  -- MVT on the convex set `[0, ∞)`
  have hderiv : ∀ r ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt (fun s' => inner (𝕜 := ℝ) ((gs.u s' : L2VF)) (w : L2VF))
        (-(ν * stokesTestPairing (gs.u r : L2VF) (w : L2VF) + F.b (gs.u r) (gs.u r) w))
        (Set.Ici 0) r :=
    fun r hr => (perTest_hasDerivAt F ν u₀ n gs w hwn r hr).hasDerivWithinAt
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
    (convex_Ici (0 : ℝ)) hs ht
  rwa [Real.norm_eq_abs, Real.norm_eq_abs] at hmvt

/-! ### Step 2: a.e.-strong subsequence from the eLpNorm convergence -/

/-- **A.e.-strong subsequence:** the eLpNorm strong convergence of the Aubin–Lions package
yields a further subsequence whose curves converge strongly in `L2VF` at a.e. `t ∈ [0, T]`
(`tendstoInMeasure_of_tendsto_eLpNorm` + `TendstoInMeasure.exists_seq_tendsto_ae`). -/
private theorem exists_ae_strong_subseq (F : Torus3NSForms) (ν : ℝ) (T : ℝ) (_hT : 0 < T)
    (u₀ : L2Sigma) (galSeq : ∀ n, GalerkinSolutionData F ν u₀ n)
    (κ : ℕ → ℕ) (_hκ : StrictMono κ)
    (alPkg : AubinLionsPackage F ν T u₀ galSeq κ) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧
      ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
        Tendsto (fun k => ((galSeq (κ (alPkg.φ (ρ k)))).u t : L2VF)) atTop
          (𝓝 (alPkg.u t : L2VF)) := by
  set μ : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) T) with hμ
  set f : ℕ → ℝ → L2VF := fun N t => ((galSeq (κ (alPkg.φ N))).u t : L2VF) with hfdef
  set g : ℝ → L2VF := fun t => (alPkg.u t : L2VF) with hgdef
  have hfm : ∀ N, AEStronglyMeasurable (f N) μ := by
    intro N
    have hcont : ContinuousOn (f N) (Set.Icc 0 T) := fun t ht =>
      (((galSeq (κ (alPkg.φ N))).u_hasDeriv t ht.1).continuousAt).continuousWithinAt
    rw [hμ]
    exact hcont.aestronglyMeasurable measurableSet_Icc
  have hgm : AEStronglyMeasurable g μ := by
    rw [hμ, hgdef]
    exact alPkg.u_aestronglyMeasurable
  have hconv : Tendsto (fun N => eLpNorm (f N - g) 2 μ) atTop (𝓝 0) :=
    alPkg.strong_convergence
  have hmeas : TendstoInMeasure μ f atTop g :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0) hfm hgm hconv
  obtain ⟨ns, hns, hae⟩ := hmeas.exists_seq_tendsto_ae
  exact ⟨ns, hns, hae⟩

/-! ### Steps 3–4: the weakly-continuous good representative -/

/-- **Step: per-Galerkin-test Cauchy at every `t`.**  The equi-Lipschitz bound
(`perTest_lipschitz`) plus Cauchy-ness on the a.e.-good set `S` (density argument via
`cauchySeq_of_equiLipschitz_of_dense`) gives Cauchy-ness of the scalar test curve
`⟪cₖ(t), w⟫` at EVERY `t ∈ [0, T]`, not just a.e. -/
private theorem galerkinTest_cauchySeq_of_aeStrong
    (F : Torus3NSForms) (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T) (u₀ : L2Sigma)
    (galSeq : ∀ n, GalerkinSolutionData F ν u₀ n)
    (κ : ℕ → ℕ) (_hκ : StrictMono κ)
    (alPkg : AubinLionsPackage F ν T u₀ galSeq κ) (ρ : ℕ → ℕ)
    (hlevel : ∀ k, k ≤ κ (alPkg.φ (ρ k)))
    (S : Set ℝ) (hS : ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)), t ∈ S)
    (hSmem : ∀ s ∈ S, Tendsto (fun k => ((galSeq (κ (alPkg.φ (ρ k)))).u s : L2VF)) atTop
      (𝓝 (alPkg.u s : L2VF))) :
    ∀ (w : L2Sigma), IsGalerkinTest w → ∀ t, t ∈ Set.Icc (0 : ℝ) T →
      CauchySeq (fun k => inner (𝕜 := ℝ) (((galSeq (κ (alPkg.φ (ρ k)))).u t : L2VF)) (w : L2VF)) := by
  set c : ℕ → ℝ → L2VF := fun k t => ((galSeq (κ (alPkg.φ (ρ k)))).u t : L2VF) with hcdef
  intro w hw t ht
  obtain ⟨n₀, hn₀⟩ := hw
  obtain ⟨L, hL0, hLip⟩ := perTest_lipschitz F ν hν u₀ galSeq w n₀ hn₀
  refine cauchySeq_of_equiLipschitz_of_dense (T := T)
    (fun k s => inner (𝕜 := ℝ) (c k s) (w : L2VF)) L hL0 n₀ ?_ S ?_ ?_ ht
  · intro k hk s hsI t' htI'
    exact hLip (κ (alPkg.φ (ρ k))) (le_trans hk (hlevel k))
      s (Set.Icc_subset_Ici_self hsI) t' (Set.Icc_subset_Ici_self htI')
  · intro u hu ε hε
    exact exists_mem_of_ae_full hT S hS hu hε
  · intro s hs'
    have hstrong : Tendsto (fun k => c k s) atTop (𝓝 (alPkg.u s : L2VF)) := hSmem s hs'.1
    exact (hstrong.inner tendsto_const_nhds).cauchySeq

/-- **Step: Cauchy in every direction.**  Orthogonal split `z = zσ + (z − zσ)` (with
`z − zσ ∈ L2Sigmaᗮ` killing the non-`L2Sigma` part against the sequence, which lives in
`L2Sigma`) plus density of the Galerkin tests in `L2Sigma` (`velocityProjection_n_tendsto`)
extends the per-test Cauchy-ness (previous step) to `CauchySeq` against every `z : L2VF`. -/
private theorem allDirections_cauchySeq_of_galerkinTest
    (F : Torus3NSForms) (ν : ℝ) (u₀ : L2Sigma)
    (galSeq : ∀ n, GalerkinSolutionData F ν u₀ n) (κ : ℕ → ℕ) (_hκ : StrictMono κ) {T : ℝ}
    (alPkg : AubinLionsPackage F ν T u₀ galSeq κ) (ρ : ℕ → ℕ)
    (hbd : ∀ k, ∀ t ∈ Set.Icc (0 : ℝ) T,
      ‖((galSeq (κ (alPkg.φ (ρ k)))).u t : L2VF)‖ ≤ ‖(u₀ : L2VF)‖)
    (hCauchy_test : ∀ (w : L2Sigma), IsGalerkinTest w → ∀ t, t ∈ Set.Icc (0 : ℝ) T →
      CauchySeq (fun k => inner (𝕜 := ℝ) (((galSeq (κ (alPkg.φ (ρ k)))).u t : L2VF)) (w : L2VF))) :
    ∀ t, t ∈ Set.Icc (0 : ℝ) T → ∀ z : L2VF,
      CauchySeq (fun k => inner (𝕜 := ℝ) (((galSeq (κ (alPkg.φ (ρ k)))).u t : L2VF)) z) := by
  set c : ℕ → ℝ → L2VF := fun k t => ((galSeq (κ (alPkg.φ (ρ k)))).u t : L2VF) with hcdef
  intro t ht z
  -- kill the `L2Sigmaᗮ` part: `⟪cₖ(t), z⟫ = ⟪cₖ(t), Pσ z⟫`
  set zσ : L2VF := L2Sigma.starProjection z with hzσ
  have hzσmem : zσ ∈ L2Sigma := L2Sigma.starProjection_apply_mem z
  have hsplit : ∀ k, inner (𝕜 := ℝ) (c k t) z = inner (𝕜 := ℝ) (c k t) zσ := by
    intro k
    have horth : z - zσ ∈ L2Sigmaᗮ := L2Sigma.sub_starProjection_mem_orthogonal z
    have h0 : inner (𝕜 := ℝ) (c k t) (z - zσ) = 0 :=
      (Submodule.mem_orthogonal L2Sigma _).mp horth _ (SetLike.coe_mem _)
    rw [inner_sub_right] at h0
    linarith
  rw [show (fun k => inner (𝕜 := ℝ) (c k t) z)
      = fun k => inner (𝕜 := ℝ) (c k t) zσ from funext hsplit]
  -- approximate `zσ ∈ L2Sigma` by band-limited tests `Pₘ zσ`
  refine cauchySeq_inner_extend (fun k => c k t) ‖(u₀ : L2VF)‖ (fun k => hbd k t ht) zσ ?_
  intro ε hε
  obtain ⟨m, hm⟩ := Metric.tendsto_atTop.mp (velocityProjection_n_tendsto zσ) ε hε
  have hdist := hm m (le_refl m)
  rw [dist_eq_norm] at hdist
  refine ⟨velocityProjection_n m zσ, by rwa [norm_sub_rev] at hdist, ?_⟩
  have hmem : velocityProjection_n m zσ ∈ L2Sigma :=
    velocityProjection_n_preserves_L2Sigma m zσ hzσmem
  have hfix : velocityProjection_n m (velocityProjection_n m zσ)
      = velocityProjection_n m zσ := velocityProjection_n_idem m zσ
  exact hCauchy_test ⟨velocityProjection_n m zσ, hmem⟩ ⟨m, hfix⟩ t ht

/-- **Step: Riesz assembly of the weak limit.**  A thin wrapper around the generic
`exists_weak_limit_in_submodule` (Cauchy in every direction ⇒ a weak limit inside the closed
submodule `L2Sigma`), specialized to the Galerkin approximant sequence at a fixed `t`. -/
private theorem weakLimit_of_allDirections_cauchySeq
    (F : Torus3NSForms) (ν : ℝ) (u₀ : L2Sigma)
    (galSeq : ∀ n, GalerkinSolutionData F ν u₀ n) (κ : ℕ → ℕ) (_hκ : StrictMono κ) {T : ℝ}
    (alPkg : AubinLionsPackage F ν T u₀ galSeq κ) (ρ : ℕ → ℕ)
    (hbd : ∀ k, ∀ t ∈ Set.Icc (0 : ℝ) T,
      ‖((galSeq (κ (alPkg.φ (ρ k)))).u t : L2VF)‖ ≤ ‖(u₀ : L2VF)‖)
    (hCauchy_all : ∀ t, t ∈ Set.Icc (0 : ℝ) T → ∀ z : L2VF,
      CauchySeq (fun k => inner (𝕜 := ℝ) (((galSeq (κ (alPkg.φ (ρ k)))).u t : L2VF)) z)) :
    ∀ t, t ∈ Set.Icc (0 : ℝ) T → ∃ y : L2VF, y ∈ L2Sigma ∧
      ‖y‖ ≤ ‖(u₀ : L2VF)‖ ∧
      ∀ z : L2VF, Tendsto (fun k => inner (𝕜 := ℝ) (((galSeq (κ (alPkg.φ (ρ k)))).u t : L2VF)) z)
        atTop (𝓝 (inner (𝕜 := ℝ) y z)) := fun t ht =>
  exists_weak_limit_in_submodule L2Sigma (fun k => ((galSeq (κ (alPkg.φ (ρ k)))).u t : L2VF))
    (fun _k => SetLike.coe_mem _) ‖(u₀ : L2VF)‖ (fun k => hbd k t ht) (hCauchy_all t ht)

/-- **Master construction: the weakly-continuous representative** of the Aubin–Lions limit.

Produces a curve `v : Time → L2Sigma` and a sub-subsequence `ρ` (of the Aubin–Lions
subsequence `φ`) such that, writing `cₖ := galSeq (φ (ρ k))`:

- (i)   `v = alPkg.u` a.e. on `[0, T]`,
- (ii)  `cₖ(t) → alPkg.u(t)` strongly in `L2VF` at a.e. `t ∈ [0, T]`,
- (iii) `⟪cₖ(t), z⟫ → ⟪v(t), z⟫` for **every** `t ∈ [0, T]` and every `z : L2VF`,
- (iv)  `‖v(t)‖ ≤ ‖u₀‖` for every `t ∈ [0, T]`,
- (v)   `v 0 = u₀` (endpoint pinning via `u_initial` + `velocityProjection_n_tendsto`),
- (vi)  `t ↦ ⟪v(t), w⟫` is Lipschitz on `[0, T]` for every Galerkin test `w`.

Construction: a.e.-strong subsequence (step 2) → per-test everywhere-Cauchy via
equi-Lipschitz + density (steps 1, 3) → extension to all `z` by `L2Sigmaᗮ`-orthogonality
and Galerkin-test density → Riesz assembly inside the closed submodule `L2Sigma` (step 4),
via the three named steps `galerkinTest_cauchySeq_of_aeStrong`,
`allDirections_cauchySeq_of_galerkinTest`, `weakLimit_of_allDirections_cauchySeq`. -/
private theorem exists_weak_representative (F : Torus3NSForms) (ν : ℝ) (hν : 0 < ν)
    (T : ℝ) (hT : 0 < T) (u₀ : L2Sigma)
    (galSeq : ∀ n, GalerkinSolutionData F ν u₀ n)
    (κ : ℕ → ℕ) (hκ : StrictMono κ)
    (alPkg : AubinLionsPackage F ν T u₀ galSeq κ) :
    ∃ (v : Time → L2Sigma) (ρ : ℕ → ℕ), StrictMono ρ ∧
      (∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)), v t = alPkg.u t) ∧
      (∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
        Tendsto (fun k => ((galSeq (κ (alPkg.φ (ρ k)))).u t : L2VF)) atTop
          (𝓝 (alPkg.u t : L2VF))) ∧
      (∀ t, t ∈ Set.Icc (0 : ℝ) T → ∀ z : L2VF,
        Tendsto (fun k => inner (𝕜 := ℝ) (((galSeq (κ (alPkg.φ (ρ k)))).u t : L2VF)) z) atTop
          (𝓝 (inner (𝕜 := ℝ) ((v t : L2VF)) z))) ∧
      (∀ t, t ∈ Set.Icc (0 : ℝ) T → ‖(v t : L2VF)‖ ≤ ‖(u₀ : L2VF)‖) ∧
      v 0 = u₀ ∧
      (∀ w : L2Sigma, IsGalerkinTest w → ∃ L : ℝ, 0 ≤ L ∧
        ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc (0 : ℝ) T,
          |inner (𝕜 := ℝ) ((v t : L2VF)) (w : L2VF)
            - inner (𝕜 := ℝ) ((v s : L2VF)) (w : L2VF)| ≤ L * |t - s|) := by
  classical
  obtain ⟨ρ, hρ, hae_strong⟩ := exists_ae_strong_subseq F ν T hT u₀ galSeq κ hκ alPkg
  set c : ℕ → ℝ → L2VF := fun k t => ((galSeq (κ (alPkg.φ (ρ k)))).u t : L2VF) with hcdef
  -- index growth: the Galerkin level of the k-th curve is ≥ k
  have hlevel : ∀ k, k ≤ κ (alPkg.φ (ρ k)) := fun k =>
    le_trans (le_trans hρ.le_apply alPkg.φ_mono.le_apply) hκ.le_apply
  -- uniform H-bound
  have hbd : ∀ k, ∀ t ∈ Set.Icc (0 : ℝ) T, ‖c k t‖ ≤ ‖(u₀ : L2VF)‖ := fun k t ht =>
    torus_galerkin_norm_le_u0 F ν u₀ _ _ t ht.1
  -- the a.e.-good (strong convergence) set
  set S : Set ℝ := {t | Tendsto (fun k => c k t) atTop (𝓝 (alPkg.u t : L2VF))} with hSdef
  have hS : ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)), t ∈ S := hae_strong
  -- three named steps: per-test Cauchy → all-directions Cauchy → Riesz limit
  have hCauchy_test := galerkinTest_cauchySeq_of_aeStrong F ν hν T hT u₀ galSeq κ hκ alPkg ρ
    hlevel S hS (fun s hs => hs)
  have hCauchy_all :=
    allDirections_cauchySeq_of_galerkinTest F ν u₀ galSeq κ hκ alPkg ρ hbd hCauchy_test
  have hex := weakLimit_of_allDirections_cauchySeq F ν u₀ galSeq κ hκ alPkg ρ hbd hCauchy_all
  choose! y hyK hybd hyconv using hex
  set v : Time → L2Sigma := fun t =>
    if ht : t ∈ Set.Icc (0 : ℝ) T then ⟨y t, hyK t ht⟩ else alPkg.u t with hvdef
  have hvcoe : ∀ t, t ∈ Set.Icc (0 : ℝ) T → (v t : L2VF) = y t := by
    intro t ht
    simp only [hvdef]
    rw [dif_pos ht]
  -- conclusion (iii): everywhere weak convergence to v
  have hweak : ∀ t, t ∈ Set.Icc (0 : ℝ) T → ∀ z : L2VF,
      Tendsto (fun k => inner (𝕜 := ℝ) (c k t) z) atTop
        (𝓝 (inner (𝕜 := ℝ) ((v t : L2VF)) z)) := by
    intro t ht z
    rw [hvcoe t ht]
    exact hyconv t ht z
  -- conclusion (i): a.e. agreement with the Aubin–Lions limit
  have hae : ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)), v t = alPkg.u t := by
    filter_upwards [hae_strong, ae_restrict_mem measurableSet_Icc] with t htS htIcc
    refine Subtype.ext ?_
    refine ext_inner_right ℝ fun z => ?_
    have h1 : Tendsto (fun k => inner (𝕜 := ℝ) (c k t) z) atTop
        (𝓝 (inner (𝕜 := ℝ) ((v t : L2VF)) z)) := hweak t htIcc z
    have h2 : Tendsto (fun k => inner (𝕜 := ℝ) (c k t) z) atTop
        (𝓝 (inner (𝕜 := ℝ) ((alPkg.u t : L2VF)) z)) :=
      htS.inner tendsto_const_nhds
    exact tendsto_nhds_unique h1 h2
  -- conclusion (v): endpoint pinning `v 0 = u₀`
  have h0Icc : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_refl 0, hT.le⟩
  have hv0 : v 0 = u₀ := by
    have hck0 : ∀ k, c k 0 = velocityProjection_n (κ (alPkg.φ (ρ k))) (u₀ : L2VF) := by
      intro k
      show ((galSeq (κ (alPkg.φ (ρ k)))).u 0 : L2VF) = _
      rw [(galSeq (κ (alPkg.φ (ρ k)))).u_initial]
    have hmono : StrictMono (fun k => κ (alPkg.φ (ρ k))) := hκ.comp (alPkg.φ_mono.comp hρ)
    have hP0 : Tendsto (fun k => c k 0) atTop (𝓝 (u₀ : L2VF)) := by
      have h := (velocityProjection_n_tendsto (u₀ : L2VF)).comp hmono.tendsto_atTop
      refine h.congr fun k => ?_
      exact (hck0 k).symm
    refine Subtype.ext ?_
    refine ext_inner_right ℝ fun z => ?_
    have h1 : Tendsto (fun k => inner (𝕜 := ℝ) (c k 0) z) atTop
        (𝓝 (inner (𝕜 := ℝ) ((v 0 : L2VF)) z)) := hweak 0 h0Icc z
    have h2 : Tendsto (fun k => inner (𝕜 := ℝ) (c k 0) z) atTop
        (𝓝 (inner (𝕜 := ℝ) ((u₀ : L2VF)) z)) :=
      hP0.inner tendsto_const_nhds
    exact tendsto_nhds_unique h1 h2
  -- conclusion (vi): per-Galerkin-test Lipschitz continuity of v
  have hlip_v : ∀ w : L2Sigma, IsGalerkinTest w → ∃ L : ℝ, 0 ≤ L ∧
      ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc (0 : ℝ) T,
        |inner (𝕜 := ℝ) ((v t : L2VF)) (w : L2VF)
          - inner (𝕜 := ℝ) ((v s : L2VF)) (w : L2VF)| ≤ L * |t - s| := by
    intro w hw
    obtain ⟨n₀, hn₀⟩ := hw
    obtain ⟨L, hL0, hLip⟩ := perTest_lipschitz F ν hν u₀ galSeq w n₀ hn₀
    refine ⟨L, hL0, fun s hsI t htI => ?_⟩
    have h1 : Tendsto (fun k => inner (𝕜 := ℝ) (c k t) (w : L2VF)
        - inner (𝕜 := ℝ) (c k s) (w : L2VF)) atTop
        (𝓝 (inner (𝕜 := ℝ) ((v t : L2VF)) (w : L2VF)
          - inner (𝕜 := ℝ) ((v s : L2VF)) (w : L2VF))) :=
      (hweak t htI (w : L2VF)).sub (hweak s hsI (w : L2VF))
    refine le_of_tendsto h1.abs ?_
    refine Filter.eventually_atTop.mpr ⟨n₀, fun k hk => ?_⟩
    exact hLip (κ (alPkg.φ (ρ k))) (le_trans hk (hlevel k))
      s (Set.Icc_subset_Ici_self hsI) t (Set.Icc_subset_Ici_self htI)
  exact ⟨v, ρ, hρ, hae, hae_strong, hweak, fun t ht => (hvcoe t ht) ▸ hybd t ht, hv0, hlip_v⟩

/-! ### Conjunct (3): strong initial trace -/

/-- **Textbook step (upper bound yields liminf coboundedness).**  A real sequence that is bounded
above by a constant is `liminf`-cobounded from below along `atTop`.

Separated out because it is pure filter bookkeeping: no Navier–Stokes content enters, only the
existence of a uniform upper bound. The lemma does not assume nonnegativity; that hypothesis
lives on the sister `liminf_nonneg_atTop_of_nonneg_of_le`. -/
private theorem isCoboundedUnder_ge_atTop_of_le {b : ℕ → ℝ} {C : ℝ} (hbC : ∀ k, b k ≤ C) :
    Filter.IsCoboundedUnder (· ≥ ·) atTop b :=
  (Filter.isBoundedUnder_of_eventually_le (a := C)
    (Filter.Eventually.of_forall hbC)).isCoboundedUnder_ge

/-- **Textbook step (nonnegativity passes to the liminf).**  A nonnegative real sequence that is
also bounded above has nonnegative `liminf` along `atTop`.

The upper bound `hbC` is not decoration: `Filter.le_liminf_of_le` requires
`Filter.IsCoboundedUnder (· ≥ ·)` (upper coboundedness), which `hbC` supplies via
`isCoboundedUnder_ge_atTop_of_le`. Without that side-condition an unbounded-above sequence's
`liminf` is not controlled by the pointwise lower bound, so both hypotheses are load-bearing. In
`dissipation_liminf_le_of_aeTendsto` the sequence is the Galerkin dissipation integrals, whose
uniform upper bound is the Galerkin energy inequality. -/
private theorem liminf_nonneg_atTop_of_nonneg_of_le {b : ℕ → ℝ} {C : ℝ}
    (hb0 : ∀ k, 0 ≤ b k) (hbC : ∀ k, b k ≤ C) :
    0 ≤ Filter.liminf b atTop :=
  Filter.le_liminf_of_le (isCoboundedUnder_ge_atTop_of_le hbC)
    (Filter.Eventually.of_forall hb0)

/-- **Textbook step (ε/4 budget against an unknown constant).**  For a nonnegative constant `c`
and a nonnegative budget `ε`,

  `c · (ε / (4 (c + 1))) ≤ ε / 4`.

The `+1` keeps the denominator non-degenerate at `c = 0` and bounds the constant by the
denominator, `c ≤ c + 1`; that non-strict step is what the proof uses to land on `ε / 4`.

Used twice in `weak_trace_inner` with two different unknown constants — the `H`-bound `M` of the
initial datum and the Lipschitz constant `L` of the chosen Galerkin test — so that each of the
three ε/4 pieces of the trace estimate can be budgeted before its constant is known. Compare
`mul_div_two_mul_add_one_lt` in `LerayHopf/R3/FrechetKolmogorov.lean`, the `ε/2` sibling of this
step. -/
private theorem mul_div_four_mul_add_one_le (c ε : ℝ) (hc : 0 ≤ c) (hε : 0 ≤ ε) :
    c * (ε / (4 * (c + 1))) ≤ ε / 4 := by
  have hc1 : (0 : ℝ) < c + 1 := by linarith
  have heq : c * (ε / (4 * (c + 1))) = (c / (c + 1)) * (ε / 4) := by field_simp
  have hle1 : c / (c + 1) ≤ 1 := by
    rw [div_le_one hc1]; linarith
  calc c * (ε / (4 * (c + 1))) = (c / (c + 1)) * (ε / 4) := heq
    _ ≤ 1 * (ε / 4) := mul_le_mul_of_nonneg_right hle1 (by linarith)
    _ = ε / 4 := one_mul _

/-- **Weak initial trace against `u₀`:** `⟪v(t), u₀⟫ → ⟪u₀, u₀⟫` as `t → 0⁺`, from the
per-Galerkin-test Lipschitz continuity, the endpoint value `v 0 = u₀`, band-limited
approximation of `u₀`, and the uniform `H`-bound (ε/3 argument). -/
private theorem weak_trace_inner (T : ℝ) (hT : 0 < T) (u₀ : L2Sigma) (v : Time → L2Sigma)
    (hbd : ∀ t, t ∈ Set.Icc (0 : ℝ) T → ‖(v t : L2VF)‖ ≤ ‖(u₀ : L2VF)‖)
    (hv0 : v 0 = u₀)
    (hlip : ∀ w : L2Sigma, IsGalerkinTest w → ∃ L : ℝ, 0 ≤ L ∧
      ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc (0 : ℝ) T,
        |inner (𝕜 := ℝ) ((v t : L2VF)) (w : L2VF)
          - inner (𝕜 := ℝ) ((v s : L2VF)) (w : L2VF)| ≤ L * |t - s|) :
    Tendsto (fun t => inner (𝕜 := ℝ) ((v t : L2VF)) (u₀ : L2VF))
      (nhdsWithin 0 (Set.Ici 0))
      (𝓝 (inner (𝕜 := ℝ) ((u₀ : L2VF)) (u₀ : L2VF))) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  set M : ℝ := ‖(u₀ : L2VF)‖ with hMdef
  have hM0 : 0 ≤ M := norm_nonneg _
  -- band-limited approximation of u₀
  obtain ⟨m, hm⟩ := Metric.tendsto_atTop.mp (velocityProjection_n_tendsto (u₀ : L2VF))
    (ε / (4 * (M + 1))) (by positivity)
  have hdist := hm m (le_refl m)
  rw [dist_eq_norm] at hdist
  have hmem : velocityProjection_n m (u₀ : L2VF) ∈ L2Sigma :=
    velocityProjection_n_preserves_L2Sigma m _ (SetLike.coe_mem u₀)
  set w : L2Sigma := ⟨velocityProjection_n m (u₀ : L2VF), hmem⟩ with hwdef
  have hwtest : IsGalerkinTest w := ⟨m, velocityProjection_n_idem m _⟩
  obtain ⟨L, hL0, hLipw⟩ := hlip w hwtest
  refine ⟨min (ε / (4 * (L + 1))) T, lt_min (by positivity) hT, ?_⟩
  intro x hx hxd
  have hx0 : (0 : ℝ) ≤ x := hx
  have hxval : dist x 0 = x := by rw [Real.dist_eq, sub_zero, abs_of_nonneg hx0]
  have hxlt : x < ε / (4 * (L + 1)) := by
    rw [hxval] at hxd
    exact lt_of_lt_of_le hxd (min_le_left _ _)
  have hxT : x ∈ Set.Icc (0 : ℝ) T := by
    refine ⟨hx0, ?_⟩
    have := lt_of_lt_of_le (hxval ▸ hxd) (min_le_right (ε / (4 * (L + 1))) T)
    exact this.le
  have h0Icc : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_refl 0, hT.le⟩
  -- approximation bounds
  have hwnorm : ‖(u₀ : L2VF) - (w : L2VF)‖ < ε / (4 * (M + 1)) := by
    rw [hwdef]
    rw [norm_sub_rev] at hdist
    exact hdist
  have hquarter : ∀ t', t' ∈ Set.Icc (0 : ℝ) T →
      |inner (𝕜 := ℝ) ((v t' : L2VF)) ((u₀ : L2VF) - (w : L2VF))| ≤ ε / 4 := by
    intro t' ht'
    have h1 : |inner (𝕜 := ℝ) ((v t' : L2VF)) ((u₀ : L2VF) - (w : L2VF))|
        ≤ M * ‖(u₀ : L2VF) - (w : L2VF)‖ :=
      (abs_real_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_right (hbd t' ht') (norm_nonneg _))
    have h2 : M * ‖(u₀ : L2VF) - (w : L2VF)‖ ≤ M * (ε / (4 * (M + 1))) :=
      mul_le_mul_of_nonneg_left hwnorm.le hM0
    have h3 : M * (ε / (4 * (M + 1))) ≤ ε / 4 :=
      mul_div_four_mul_add_one_le M ε hM0 hε.le
    linarith
  -- Lipschitz bound at the test w
  have hLbound : |inner (𝕜 := ℝ) ((v x : L2VF)) (w : L2VF)
      - inner (𝕜 := ℝ) ((v 0 : L2VF)) (w : L2VF)| ≤ ε / 4 := by
    have h1 := hLipw 0 h0Icc x hxT
    rw [sub_zero, abs_of_nonneg hx0] at h1
    have h2 : L * x ≤ L * (ε / (4 * (L + 1))) := mul_le_mul_of_nonneg_left hxlt.le hL0
    have h3 : L * (ε / (4 * (L + 1))) ≤ ε / 4 :=
      mul_div_four_mul_add_one_le L ε hL0 hε.le
    linarith
  -- decomposition and assembly
  have hkey : inner (𝕜 := ℝ) ((v x : L2VF)) (u₀ : L2VF)
      - inner (𝕜 := ℝ) ((u₀ : L2VF)) (u₀ : L2VF)
      = inner (𝕜 := ℝ) ((v x : L2VF)) ((u₀ : L2VF) - (w : L2VF))
        + (inner (𝕜 := ℝ) ((v x : L2VF)) (w : L2VF)
          - inner (𝕜 := ℝ) ((v 0 : L2VF)) (w : L2VF))
        - inner (𝕜 := ℝ) ((v 0 : L2VF)) ((u₀ : L2VF) - (w : L2VF)) := by
    rw [hv0, inner_sub_right, inner_sub_right]
    ring
  rw [Real.dist_eq, hkey, hv0]
  have hq1 := hquarter x hxT
  have hq2 := hquarter 0 h0Icc
  rw [hv0] at hLbound hq2
  calc |inner (𝕜 := ℝ) ((v x : L2VF)) ((u₀ : L2VF) - (w : L2VF))
        + (inner (𝕜 := ℝ) ((v x : L2VF)) (w : L2VF)
          - inner (𝕜 := ℝ) ((u₀ : L2VF)) (w : L2VF))
        - inner (𝕜 := ℝ) ((u₀ : L2VF)) ((u₀ : L2VF) - (w : L2VF))|
      ≤ |inner (𝕜 := ℝ) ((v x : L2VF)) ((u₀ : L2VF) - (w : L2VF))
        + (inner (𝕜 := ℝ) ((v x : L2VF)) (w : L2VF)
          - inner (𝕜 := ℝ) ((u₀ : L2VF)) (w : L2VF))|
        + |inner (𝕜 := ℝ) ((u₀ : L2VF)) ((u₀ : L2VF) - (w : L2VF))| := abs_sub _ _
    _ ≤ |inner (𝕜 := ℝ) ((v x : L2VF)) ((u₀ : L2VF) - (w : L2VF))|
        + |inner (𝕜 := ℝ) ((v x : L2VF)) (w : L2VF)
          - inner (𝕜 := ℝ) ((u₀ : L2VF)) (w : L2VF)|
        + |inner (𝕜 := ℝ) ((u₀ : L2VF)) ((u₀ : L2VF) - (w : L2VF))| := by
        have := abs_add_le
          (inner (𝕜 := ℝ) ((v x : L2VF)) ((u₀ : L2VF) - (w : L2VF)))
          (inner (𝕜 := ℝ) ((v x : L2VF)) (w : L2VF)
            - inner (𝕜 := ℝ) ((u₀ : L2VF)) (w : L2VF))
        linarith
    _ < ε := by linarith

/-- **Conjunct (3): strong initial trace.**  The weakly-continuous representative attains
`u₀` strongly at `0⁺`: weak trace (above) + the uniform bound `‖v(t)‖ ≤ ‖u₀‖` + the
norm-expansion `‖v(t) − u₀‖² = ‖v(t)‖² − 2⟪v(t), u₀⟫ + ‖u₀‖² ≤ 2‖u₀‖² − 2⟪v(t), u₀⟫ → 0`. -/
private theorem strong_trace_of_props (T : ℝ) (hT : 0 < T) (u₀ : L2Sigma)
    (v : Time → L2Sigma)
    (hbd : ∀ t, t ∈ Set.Icc (0 : ℝ) T → ‖(v t : L2VF)‖ ≤ ‖(u₀ : L2VF)‖)
    (hv0 : v 0 = u₀)
    (hlip : ∀ w : L2Sigma, IsGalerkinTest w → ∃ L : ℝ, 0 ≤ L ∧
      ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc (0 : ℝ) T,
        |inner (𝕜 := ℝ) ((v t : L2VF)) (w : L2VF)
          - inner (𝕜 := ℝ) ((v s : L2VF)) (w : L2VF)| ≤ L * |t - s|) :
    Tendsto (fun t => (v t : L2VF)) (nhdsWithin 0 (Set.Ici 0)) (𝓝 (u₀ : L2VF)) := by
  have hinner := weak_trace_inner T hT u₀ v hbd hv0 hlip
  rw [Metric.tendsto_nhdsWithin_nhds] at hinner ⊢
  intro ε hε
  obtain ⟨δ₁, hδ₁, h₁⟩ := hinner (ε ^ 2 / 2) (by positivity)
  refine ⟨min δ₁ T, lt_min hδ₁ hT, ?_⟩
  intro x hx hxd
  have hx0 : (0 : ℝ) ≤ x := hx
  have hxδ₁ : dist x 0 < δ₁ := lt_of_lt_of_le hxd (min_le_left _ _)
  have hxT : x ∈ Set.Icc (0 : ℝ) T := by
    refine ⟨hx0, ?_⟩
    have h := lt_of_lt_of_le hxd (min_le_right δ₁ T)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hx0] at h
    exact h.le
  have hi := h₁ hx hxδ₁
  rw [Real.dist_eq] at hi
  have hself : inner (𝕜 := ℝ) ((u₀ : L2VF)) ((u₀ : L2VF)) = ‖(u₀ : L2VF)‖ ^ 2 :=
    real_inner_self_eq_norm_sq _
  have hlow : ‖(u₀ : L2VF)‖ ^ 2 - ε ^ 2 / 2
      < inner (𝕜 := ℝ) ((v x : L2VF)) ((u₀ : L2VF)) := by
    have habs := abs_lt.mp hi
    rw [hself] at habs
    linarith [habs.1]
  have hnormsq : ‖(v x : L2VF) - (u₀ : L2VF)‖ ^ 2
      = ‖(v x : L2VF)‖ ^ 2 - 2 * inner (𝕜 := ℝ) ((v x : L2VF)) ((u₀ : L2VF))
        + ‖(u₀ : L2VF)‖ ^ 2 := norm_sub_sq_real _ _
  have hbsq : ‖(v x : L2VF)‖ ^ 2 ≤ ‖(u₀ : L2VF)‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (hbd x hxT) 2
  have hsq : ‖(v x : L2VF) - (u₀ : L2VF)‖ ^ 2 < ε ^ 2 := by
    rw [hnormsq]
    linarith
  rw [dist_eq_norm]
  nlinarith [norm_nonneg ((v x : L2VF) - (u₀ : L2VF))]

/-! ### Conjunct (1): viscous ENNReal machinery (junk-free lower semicontinuity) -/

/-- The **honest ENNReal viscous sum** (no real-tsum junk-`0` collapse off `H¹`):
`∑'_{(j,k)} ofReal (ν · (2π)² |k|² ‖ûⱼ(k)‖²)` over the product index. -/
noncomputable def viscousEnn (ν : ℝ) (u : L2VF) : ℝ≥0∞ :=
  ∑' p : Fin 3 × (Fin 3 → ℤ),
    ENNReal.ofReal (ν * ((2 * Real.pi) ^ 2 * (∑ i : Fin 3, (p.2 i : ℝ) ^ 2) *
      ‖mFourierCoeff3 (L2VF_projComponentC p.1 u) p.2‖ ^ 2))

/-- The real viscous form is dominated by the honest ENNReal sum (equality on the
summable set; the junk-`0` collapse only helps the inequality). -/
theorem ofReal_viscousFormSq_le (ν : ℝ) (hν : 0 ≤ ν) (u : L2VF) :
    ENNReal.ofReal (viscousFormSq ν u) ≤ viscousEnn ν u := by
  classical
  set g : Fin 3 → (Fin 3 → ℤ) → ℝ := fun j k =>
    (2 * Real.pi) ^ 2 * (∑ i : Fin 3, (k i : ℝ) ^ 2) *
      ‖mFourierCoeff3 (L2VF_projComponentC j u) k‖ ^ 2 with hgdef
  have hg0 : ∀ j k, 0 ≤ g j k := fun j k => by positivity
  have hEnn : viscousEnn ν u
      = ∑ j : Fin 3, ∑' k : Fin 3 → ℤ, ENNReal.ofReal (ν * g j k) := by
    unfold viscousEnn
    rw [ENNReal.tsum_prod', tsum_fintype]
  have hLHS : viscousFormSq ν u = ∑ j : Fin 3, ν * ∑' k : Fin 3 → ℤ, g j k := by
    unfold viscousFormSq
    rw [Finset.mul_sum]
  rw [hLHS, hEnn]
  have hsum0 : ∀ j ∈ (Finset.univ : Finset (Fin 3)), 0 ≤ ν * ∑' k, g j k := fun j _ =>
    mul_nonneg hν (tsum_nonneg (hg0 j))
  rw [ENNReal.ofReal_sum_of_nonneg hsum0]
  refine Finset.sum_le_sum fun j _ => ?_
  by_cases hs : Summable (g j)
  · have hs' : Summable (fun k => ν * g j k) := hs.mul_left ν
    have hmul : ν * ∑' k, g j k = ∑' k, ν * g j k := tsum_mul_left.symm
    rw [hmul, ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg hν (hg0 j k)) hs']
  · rw [tsum_eq_zero_of_not_summable hs, mul_zero, ENNReal.ofReal_zero]
    exact zero_le

/-- For a band-limited field the honest ENNReal sum EQUALS `ofReal` of the real viscous
form: both collapse to the same finite `fourierBox` sum. -/
theorem viscousEnn_eq_ofReal_of_bandlimited (ν : ℝ) (hν : 0 ≤ ν) (n : ℕ) (u : L2VF)
    (hu : velocityProjection_n n u = u) :
    viscousEnn ν u = ENNReal.ofReal (viscousFormSq ν u) := by
  classical
  set g : Fin 3 → (Fin 3 → ℤ) → ℝ := fun j k =>
    (2 * Real.pi) ^ 2 * (∑ i : Fin 3, (k i : ℝ) ^ 2) *
      ‖mFourierCoeff3 (L2VF_projComponentC j u) k‖ ^ 2 with hgdef
  have hg0 : ∀ j k, 0 ≤ g j k := fun j k => by positivity
  have hzero : ∀ (j : Fin 3) (k : Fin 3 → ℤ), k ∉ fourierBox n → g j k = 0 := by
    intro j k hk
    simp only [hgdef]
    rw [coeff_zero_outside_box n u hu j k hk]
    simp
  -- LHS: product tsum collapses to the product finset
  have hL : viscousEnn ν u
      = ∑ p ∈ ((Finset.univ : Finset (Fin 3)) ×ˢ fourierBox n),
          ENNReal.ofReal (ν * g p.1 p.2) := by
    unfold viscousEnn
    apply tsum_eq_sum
    intro p hp
    have hk : p.2 ∉ fourierBox n := by
      intro hmem
      exact hp (Finset.mem_product.mpr ⟨Finset.mem_univ _, hmem⟩)
    have : g p.1 p.2 = 0 := hzero p.1 p.2 hk
    simp only [hgdef] at this
    rw [this, mul_zero, ENNReal.ofReal_zero]
  -- RHS: per-j tsum collapses to the box sum
  have hR : viscousFormSq ν u = ν * ∑ j : Fin 3, ∑ k ∈ fourierBox n, g j k := by
    unfold viscousFormSq
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    exact tsum_eq_sum fun k hk => hzero j k hk
  rw [hL, hR]
  -- distribute ν and ofReal through the finite sums
  have hstep : ν * ∑ j : Fin 3, ∑ k ∈ fourierBox n, g j k
      = ∑ j : Fin 3, ∑ k ∈ fourierBox n, ν * g j k := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => Finset.mul_sum _ _ _
  rw [hstep, ENNReal.ofReal_sum_of_nonneg
    (fun j _ => Finset.sum_nonneg fun k _ => mul_nonneg hν (hg0 j k))]
  rw [Finset.sum_product]
  exact Finset.sum_congr rfl fun j _ =>
    (ENNReal.ofReal_sum_of_nonneg fun k _ => mul_nonneg hν (hg0 j k)).symm

/-- **Spatial lower semicontinuity of the honest viscous sum** under strong `L2VF`
convergence: per-coefficient continuity + finite-subsum exhaustion (`tsum = ⨆ Finset`). -/
theorem viscousEnn_lsc (ν : ℝ) (v : L2VF) (vk : ℕ → L2VF)
    (hconv : Tendsto vk atTop (𝓝 v)) :
    viscousEnn ν v ≤ Filter.liminf (fun k => viscousEnn ν (vk k)) atTop := by
  classical
  set G : Fin 3 × (Fin 3 → ℤ) → L2VF → ℝ≥0∞ := fun p x =>
    ENNReal.ofReal (ν * ((2 * Real.pi) ^ 2 * (∑ i : Fin 3, (p.2 i : ℝ) ^ 2) *
      ‖mFourierCoeff3 (L2VF_projComponentC p.1 x) p.2‖ ^ 2)) with hGdef
  have hunfold : ∀ x : L2VF, viscousEnn ν x = ∑' p, G p x := fun x => rfl
  rw [hunfold, ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  -- each term is continuous in the field
  have hGcont : ∀ p : Fin 3 × (Fin 3 → ℤ), Continuous (G p) := by
    intro p
    have h1 : Continuous (fun x : L2VF =>
        mFourierCoeff3 (L2VF_projComponentC p.1 x) p.2) := by
      have heq : (fun x : L2VF => mFourierCoeff3 (L2VF_projComponentC p.1 x) p.2)
          = fun x => fourierCoeffCLM p.2 (L2VF_projComponentC p.1 x) := by
        funext x
        rw [fourierCoeffCLM_apply]
      rw [heq]
      exact (fourierCoeffCLM p.2).continuous.comp (L2VF_projComponentC p.1).continuous
    have h2 : Continuous (fun x : L2VF =>
        ν * ((2 * Real.pi) ^ 2 * (∑ i : Fin 3, (p.2 i : ℝ) ^ 2) *
          ‖mFourierCoeff3 (L2VF_projComponentC p.1 x) p.2‖ ^ 2)) :=
      continuous_const.mul (continuous_const.mul ((h1.norm).pow 2))
    exact ENNReal.continuous_ofReal.comp h2
  have hsum : Tendsto (fun k => ∑ p ∈ s, G p (vk k)) atTop (𝓝 (∑ p ∈ s, G p v)) :=
    tendsto_finsetSum s fun p _ => ((hGcont p).tendsto v).comp hconv
  have hle : ∀ k, ∑ p ∈ s, G p (vk k) ≤ viscousEnn ν (vk k) := fun k => by
    rw [hunfold]
    exact ENNReal.sum_le_tsum s
  calc ∑ p ∈ s, G p v
      = Filter.liminf (fun k => ∑ p ∈ s, G p (vk k)) atTop := hsum.liminf_eq.symm
    _ ≤ Filter.liminf (fun k => viscousEnn ν (vk k)) atTop :=
        Filter.liminf_le_liminf (Filter.Eventually.of_forall hle)

/-! ### Conjunct (1): the pointwise-in-time energy inequality -/

/-- **Kinetic-energy step.**  Squared-norm weak-lower-semicontinuity of the Galerkin
approximants at a fixed time `t`: the weak limit's kinetic energy at `t` is bounded by the
`liminf` of the approximants' kinetic energies, via `normSq_le_liminf_of_inner_tendsto`
against the uniform Galerkin `H`-bound `torus_galerkin_norm_le_u0`. -/
private theorem kineticEnergy_liminf_le_of_weakTendsto
    (F : Torus3NSForms) (ν : ℝ) (u₀ : L2Sigma)
    (galSeq : ∀ n, GalerkinSolutionData F ν u₀ n)
    (κ : ℕ → ℕ) (_hκ : StrictMono κ)
    {T : ℝ} (alPkg : AubinLionsPackage F ν T u₀ galSeq κ)
    (ρ : ℕ → ℕ) (v : Time → L2Sigma) (t : ℝ) (ht0 : 0 ≤ t) (htIcc : t ∈ Set.Icc (0 : ℝ) T)
    (hweak : ∀ s, s ∈ Set.Icc (0 : ℝ) T → ∀ z : L2VF,
      Tendsto (fun k => inner (𝕜 := ℝ) (((galSeq (κ (alPkg.φ (ρ k)))).u s : L2VF)) z) atTop
        (𝓝 (inner (𝕜 := ℝ) ((v s : L2VF)) z))) :
    (1 / 2 : ℝ) * ‖(v t : L2VF)‖ ^ 2 ≤
      Filter.liminf (fun k => (1 / 2 : ℝ) * ‖((galSeq (κ (alPkg.φ (ρ k)))).u t : L2VF)‖ ^ 2)
        atTop := by
  set c : ℕ → ℝ → L2VF := fun k s => ((galSeq (κ (alPkg.φ (ρ k)))).u s : L2VF) with hcdef
  set a : ℕ → ℝ := fun k => (1 / 2 : ℝ) * ‖c k t‖ ^ 2 with hadef
  have hkin_normSq : ‖(v t : L2VF)‖ ^ 2
      ≤ Filter.liminf (fun k => ‖c k t‖ ^ 2) atTop := by
    refine normSq_le_liminf_of_inner_tendsto ((v t : L2VF)) (fun k => c k t)
      ‖(u₀ : L2VF)‖ (fun k => torus_galerkin_norm_le_u0 F ν u₀ _ _ t ht0) ?_
    have h := hweak t htIcc ((v t : L2VF))
    rwa [real_inner_self_eq_norm_sq] at h
  have hbdd_above_n : Filter.IsBoundedUnder (· ≤ ·) atTop (fun k => ‖c k t‖ ^ 2) :=
    Filter.isBoundedUnder_of_eventually_le (a := ‖(u₀ : L2VF)‖ ^ 2)
      (Filter.Eventually.of_forall fun k =>
        pow_le_pow_left₀ (norm_nonneg _) (torus_galerkin_norm_le_u0 F ν u₀ _ _ t ht0) 2)
  have hbdd_below_n : Filter.IsBoundedUnder (· ≥ ·) atTop (fun k => ‖c k t‖ ^ 2) :=
    Filter.isBoundedUnder_of_eventually_ge (a := 0)
      (Filter.Eventually.of_forall fun k => by positivity)
  have hmono : Monotone (fun r : ℝ => (1 / 2 : ℝ) * r) := fun x y hxy => by linarith
  have hmap := hmono.map_liminf_of_continuousAt (fun k => ‖c k t‖ ^ 2)
    (continuous_const.mul continuous_id).continuousAt
    hbdd_above_n.isCoboundedUnder_ge hbdd_below_n
  have hmap' : (1 / 2 : ℝ) * Filter.liminf (fun k => ‖c k t‖ ^ 2) atTop
      = Filter.liminf a atTop := hmap
  calc (1 / 2 : ℝ) * ‖(v t : L2VF)‖ ^ 2
      ≤ (1 / 2 : ℝ) * Filter.liminf (fun k => ‖c k t‖ ^ 2) atTop := by
        linarith [hkin_normSq]
    _ = Filter.liminf a atTop := hmap'

/-- **Dissipation step.**  A.e. spatial lower-semicontinuity of the viscous form
(`viscousEnn_lsc`) plus Fatou's lemma bounds the weak limit's dissipation integral on
`[0, t]` by the `liminf` of the Galerkin approximants' dissipation integrals. -/
private theorem dissipation_liminf_le_of_aeTendsto
    (F : Torus3NSForms) (ν : ℝ) (hν : 0 < ν) (u₀ : L2Sigma)
    (galSeq : ∀ n, GalerkinSolutionData F ν u₀ n)
    (κ : ℕ → ℕ) (_hκ : StrictMono κ)
    {T : ℝ} (alPkg : AubinLionsPackage F ν T u₀ galSeq κ)
    (ρ : ℕ → ℕ) (v : Time → L2Sigma) (t : ℝ) (ht0 : 0 ≤ t) (htT : t ≤ T)
    (hae : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), v s = alPkg.u s)
    (hae_strong : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Tendsto (fun k => ((galSeq (κ (alPkg.φ (ρ k)))).u s : L2VF)) atTop
        (𝓝 (alPkg.u s : L2VF)))
    (hInt : IntervalIntegrable (fun s => viscousFormSq ν (v s : L2VF)) volume 0 T) :
    ∫ s in (0 : ℝ)..t, viscousFormSq ν (v s : L2VF)
      ≤ Filter.liminf
          (fun k => ∫ s in (0 : ℝ)..t, viscousFormSq ν (((galSeq (κ (alPkg.φ (ρ k)))).u s : L2VF)))
          atTop := by
  set c : ℕ → ℝ → L2VF := fun k s => ((galSeq (κ (alPkg.φ (ρ k)))).u s : L2VF) with hcdef
  set b : ℕ → ℝ := fun k => ∫ s in (0 : ℝ)..t, viscousFormSq ν (c k s) with hbdef
  have hb0 : ∀ k, 0 ≤ b k := fun k =>
    intervalIntegral.integral_nonneg ht0 fun s _ => viscousFormSq_nonneg hν.le _
  have hbdd_below_b : Filter.IsBoundedUnder (· ≥ ·) atTop b :=
    Filter.isBoundedUnder_of_eventually_ge (a := 0)
      (Filter.Eventually.of_forall hb0)
  -- uniform upper bound on the approximants' dissipation: the Galerkin energy inequality.
  have hbE : ∀ k, b k ≤ (1 / 2 : ℝ) * ‖(u₀ : L2VF)‖ ^ 2 := fun k => by
    have h := torus_galerkin_energy_le F ν u₀ _ (galSeq (κ (alPkg.φ (ρ k)))) t ht0
    have h0 : (0 : ℝ) ≤ (1 / 2 : ℝ) * ‖((galSeq (κ (alPkg.φ (ρ k)))).u t : L2VF)‖ ^ 2 := by
      positivity
    linarith [h, h0]
  have hcobdd_b : Filter.IsCoboundedUnder (· ≥ ·) atTop b :=
    isCoboundedUnder_ge_atTop_of_le hbE
  have hliminfb0 : 0 ≤ Filter.liminf b atTop :=
    liminf_nonneg_atTop_of_nonneg_of_le hb0 hbE
  -- restrict the [0, T] integrability hypothesis to [0, t]
  have hIntt : IntervalIntegrable (fun s => viscousFormSq ν (v s : L2VF)) volume 0 t :=
    hInt.mono_set (Set.uIcc_subset_uIcc Set.left_mem_uIcc
      (by rw [Set.uIcc_of_le (ht0.trans htT)]; exact Set.mem_Icc.mpr ⟨ht0, htT⟩))
  have hfIntOn : MeasureTheory.IntegrableOn
      (fun s => viscousFormSq ν (v s : L2VF)) (Set.Ioc 0 t) volume := hIntt.1
  -- real integral of the limit as a lintegral
  have hreal : ∫ s in (0 : ℝ)..t, viscousFormSq ν (v s : L2VF)
      = (∫⁻ s in Set.Ioc (0 : ℝ) t,
          ENNReal.ofReal (viscousFormSq ν (v s : L2VF))).toReal := by
    rw [intervalIntegral.integral_of_le ht0]
    exact integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun s => viscousFormSq_nonneg hν.le _)
      hfIntOn.aestronglyMeasurable
  -- transfer the a.e. facts to [0, t]
  have hsub : Set.Ioc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T := fun s hs =>
    ⟨hs.1.le, hs.2.trans htT⟩
  have hae' : ∀ᵐ s ∂(volume.restrict (Set.Ioc (0 : ℝ) t)), v s = alPkg.u s :=
    ae_restrict_of_ae_restrict_of_subset hsub hae
  have hstr' : ∀ᵐ s ∂(volume.restrict (Set.Ioc (0 : ℝ) t)),
      Tendsto (fun k => c k s) atTop (𝓝 (alPkg.u s : L2VF)) :=
    ae_restrict_of_ae_restrict_of_subset hsub hae_strong
  -- a.e. pointwise lsc chain
  have hae_lsc : ∀ᵐ s ∂(volume.restrict (Set.Ioc (0 : ℝ) t)),
      ENNReal.ofReal (viscousFormSq ν (v s : L2VF))
        ≤ Filter.liminf (fun k => ENNReal.ofReal (viscousFormSq ν (c k s))) atTop := by
    filter_upwards [hae', hstr'] with s hveq hconv
    have hpt : ∀ k, viscousEnn ν (c k s)
        = ENNReal.ofReal (viscousFormSq ν (c k s)) := fun k =>
      viscousEnn_eq_ofReal_of_bandlimited ν hν.le (κ (alPkg.φ (ρ k))) (c k s)
        ((galSeq (κ (alPkg.φ (ρ k)))).u_inVn s).symm
    calc ENNReal.ofReal (viscousFormSq ν (v s : L2VF))
        = ENNReal.ofReal (viscousFormSq ν (alPkg.u s : L2VF)) := by rw [hveq]
      _ ≤ viscousEnn ν (alPkg.u s : L2VF) := ofReal_viscousFormSq_le ν hν.le _
      _ ≤ Filter.liminf (fun k => viscousEnn ν (c k s)) atTop :=
          viscousEnn_lsc ν _ _ hconv
      _ = Filter.liminf (fun k => ENNReal.ofReal (viscousFormSq ν (c k s))) atTop := by
          congr 1
          funext k
          exact hpt k
  -- measurability of the approximant integrands
  have hmeas_k : ∀ k, AEMeasurable
      (fun s => ENNReal.ofReal (viscousFormSq ν (c k s)))
      (volume.restrict (Set.Ioc (0 : ℝ) t)) := by
    intro k
    have hcont : ContinuousOn (fun s => viscousFormSq ν (c k s)) (Set.Ioc 0 t) :=
      (galerkin_viscous_continuousOn F ν u₀ _ (galSeq (κ (alPkg.φ (ρ k))))).mono
        fun s hs => hs.1.le
    exact ENNReal.measurable_ofReal.comp_aemeasurable
      (hcont.aemeasurable measurableSet_Ioc)
  -- Fatou
  have hFatou : ∫⁻ s in Set.Ioc (0 : ℝ) t,
      ENNReal.ofReal (viscousFormSq ν (v s : L2VF))
      ≤ Filter.liminf (fun k => ∫⁻ s in Set.Ioc (0 : ℝ) t,
          ENNReal.ofReal (viscousFormSq ν (c k s))) atTop :=
    le_trans (MeasureTheory.lintegral_mono_ae hae_lsc)
      (MeasureTheory.lintegral_liminf_le' hmeas_k)
  -- approximant lintegrals are ofReal of the real integrals
  have hbk_eq : ∀ k, ∫⁻ s in Set.Ioc (0 : ℝ) t,
      ENNReal.ofReal (viscousFormSq ν (c k s)) = ENNReal.ofReal (b k) := by
    intro k
    have hcont : ContinuousOn (fun s => viscousFormSq ν (c k s)) (Set.Icc 0 t) :=
      (galerkin_viscous_continuousOn F ν u₀ _ (galSeq (κ (alPkg.φ (ρ k))))).mono
        fun s hs => hs.1
    have hint : MeasureTheory.IntegrableOn (fun s => viscousFormSq ν (c k s))
        (Set.Ioc 0 t) volume := (hcont.intervalIntegrable_of_Icc ht0).1
    have h1 : b k = (∫⁻ s in Set.Ioc (0 : ℝ) t,
        ENNReal.ofReal (viscousFormSq ν (c k s))).toReal := by
      rw [hbdef]
      simp only
      rw [intervalIntegral.integral_of_le ht0]
      exact integral_eq_lintegral_of_nonneg_ae
        (Filter.Eventually.of_forall fun s => viscousFormSq_nonneg hν.le _)
        hint.aestronglyMeasurable
    have h2 : ∫⁻ s in Set.Ioc (0 : ℝ) t,
        ENNReal.ofReal (viscousFormSq ν (c k s)) < ⊤ := hint.lintegral_lt_top
    rw [h1, ENNReal.ofReal_toReal h2.ne]
  -- ofReal commutes with the (bounded) real liminf
  have hcomm : Filter.liminf (fun k => ENNReal.ofReal (b k)) atTop
      = ENNReal.ofReal (Filter.liminf b atTop) := by
    have hmono : Monotone ENNReal.ofReal := fun x y h => ENNReal.ofReal_le_ofReal h
    exact (hmono.map_liminf_of_continuousAt b
      ENNReal.continuous_ofReal.continuousAt hcobdd_b hbdd_below_b).symm
  have hchain : ∫⁻ s in Set.Ioc (0 : ℝ) t,
      ENNReal.ofReal (viscousFormSq ν (v s : L2VF))
      ≤ ENNReal.ofReal (Filter.liminf b atTop) := by
    rw [← hcomm]
    refine hFatou.trans (le_of_eq ?_)
    congr 1
    funext k
    exact hbk_eq k
  calc ∫ s in (0 : ℝ)..t, viscousFormSq ν (v s : L2VF)
      = (∫⁻ s in Set.Ioc (0 : ℝ) t,
          ENNReal.ofReal (viscousFormSq ν (v s : L2VF))).toReal := hreal
    _ ≤ (ENNReal.ofReal (Filter.liminf b atTop)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hchain
    _ = Filter.liminf b atTop := ENNReal.toReal_ofReal hliminfb0

/-- **Energy-budget assembly step.**  Fully generic real-sequence lemma: liminf
superadditivity (`le_liminf_add`) combined with the per-index energy budget `a k + b k ≤ E`
turns a `liminf`-bound on each of two terms into a bound on their sum.  Consumes only
`hab`/`ha0`/`hb0`/`haE`/`hbE` (the per-approximant energy inequality and its consequences)
and `hkin`/`hdiss` (the two `liminf` bounds from the kinetic and dissipation steps) — no
Galerkin/Torus-specific data. -/
private theorem energyBudget_liminf_assembly (a b : ℕ → ℝ) (E X Y : ℝ)
    (hab : ∀ k, a k + b k ≤ E) (ha0 : ∀ k, 0 ≤ a k) (hb0 : ∀ k, 0 ≤ b k)
    (haE : ∀ k, a k ≤ E) (hbE : ∀ k, b k ≤ E)
    (hkin : X ≤ Filter.liminf a atTop) (hdiss : Y ≤ Filter.liminf b atTop) :
    X + Y ≤ E := by
  have hbdd_above_a : Filter.IsBoundedUnder (· ≤ ·) atTop a :=
    Filter.isBoundedUnder_of_eventually_le (a := E) (Filter.Eventually.of_forall haE)
  have hbdd_below_a : Filter.IsBoundedUnder (· ≥ ·) atTop a :=
    Filter.isBoundedUnder_of_eventually_ge (a := 0) (Filter.Eventually.of_forall ha0)
  have hbdd_below_b : Filter.IsBoundedUnder (· ≥ ·) atTop b :=
    Filter.isBoundedUnder_of_eventually_ge (a := 0) (Filter.Eventually.of_forall hb0)
  have hcobdd_b : Filter.IsCoboundedUnder (· ≥ ·) atTop b :=
    (Filter.isBoundedUnder_of_eventually_le (a := E)
      (Filter.Eventually.of_forall hbE)).isCoboundedUnder_ge
  have hsuper : Filter.liminf a atTop + Filter.liminf b atTop
      ≤ Filter.liminf (a + b) atTop :=
    le_liminf_add hbdd_below_a hbdd_above_a hbdd_below_b hcobdd_b
  have habE : Filter.liminf (a + b) atTop ≤ E := by
    have hboundedbelow : Filter.IsBoundedUnder (· ≥ ·) atTop (a + b) :=
      Filter.isBoundedUnder_of_eventually_ge (a := 0)
        (Filter.Eventually.of_forall fun k => by
          have := ha0 k
          have := hb0 k
          simp only [Pi.add_apply]
          linarith)
    have h1 : Filter.liminf (a + b) atTop ≤ Filter.liminf (fun _ => E) atTop :=
      Filter.liminf_le_liminf
        (Filter.Eventually.of_forall fun k => by
          have := hab k
          simp only [Pi.add_apply]
          linarith)
        hboundedbelow
        ((Filter.isBoundedUnder_of_eventually_le (a := E)
          (Filter.Eventually.of_forall fun _ => le_refl E)).isCoboundedUnder_ge)
    rwa [Filter.liminf_const] at h1
  linarith [hkin, hdiss, hsuper, habE]

/-- **Conjunct (1): `∀t` energy inequality for the good representative.**
Kinetic term by squared-norm weak-lsc at every `t`; dissipation term by the a.e.
spatial lsc of `viscousEnn` + Fatou in time; combined against the Galerkin energy
identity via liminf superadditivity.

The hypothesis `hInt` (integrable dissipation of `v` on `[0, T]`) keeps this statement
honest — without it the real interval integral would junk-collapse to `0` in the
non-integrable regime and the inequality would hold vacuously there (Codex P2 finding).
The capstone discharges `hInt` from the energy-class conjunct (4) via a.e.-invariance.

Setup + three named steps (`kineticEnergy_liminf_le_of_weakTendsto`,
`dissipation_liminf_le_of_aeTendsto`, `energyBudget_liminf_assembly`) + assembly. -/
private theorem energy_ineq_of_representative (F : Torus3NSForms) (ν : ℝ) (hν : 0 < ν)
    (T : ℝ) (_hT : 0 < T) (u₀ : L2Sigma)
    (galSeq : ∀ n, GalerkinSolutionData F ν u₀ n)
    (κ : ℕ → ℕ) (hκ : StrictMono κ)
    (alPkg : AubinLionsPackage F ν T u₀ galSeq κ)
    (v : Time → L2Sigma) (ρ : ℕ → ℕ)
    (hae : ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)), v t = alPkg.u t)
    (hae_strong : ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Tendsto (fun k => ((galSeq (κ (alPkg.φ (ρ k)))).u t : L2VF)) atTop
        (𝓝 (alPkg.u t : L2VF)))
    (hweak : ∀ t, t ∈ Set.Icc (0 : ℝ) T → ∀ z : L2VF,
      Tendsto (fun k => inner (𝕜 := ℝ) (((galSeq (κ (alPkg.φ (ρ k)))).u t : L2VF)) z) atTop
        (𝓝 (inner (𝕜 := ℝ) ((v t : L2VF)) z)))
    (hInt : IntervalIntegrable (fun s => viscousFormSq ν (v s : L2VF))
      MeasureTheory.volume 0 T) :
    ∀ t, 0 ≤ t → t ≤ T →
      (1 / 2 : ℝ) * ‖(v t : L2VF)‖ ^ 2 +
        ∫ s in (0 : ℝ)..t, viscousFormSq ν (v s : L2VF) ≤
      (1 / 2 : ℝ) * ‖(u₀ : L2VF)‖ ^ 2 := by
  intro t ht0 htT
  have htIcc : t ∈ Set.Icc (0 : ℝ) T := ⟨ht0, htT⟩
  set c : ℕ → ℝ → L2VF := fun k s => ((galSeq (κ (alPkg.φ (ρ k)))).u s : L2VF) with hcdef
  set E : ℝ := (1 / 2 : ℝ) * ‖(u₀ : L2VF)‖ ^ 2 with hEdef
  set a : ℕ → ℝ := fun k => (1 / 2 : ℝ) * ‖c k t‖ ^ 2 with hadef
  set b : ℕ → ℝ := fun k => ∫ s in (0 : ℝ)..t, viscousFormSq ν (c k s) with hbdef
  -- per-approximant energy inequality
  have hab : ∀ k, a k + b k ≤ E := fun k =>
    torus_galerkin_energy_le F ν u₀ _ (galSeq (κ (alPkg.φ (ρ k)))) t ht0
  have ha0 : ∀ k, 0 ≤ a k := fun k => by positivity
  have hb0 : ∀ k, 0 ≤ b k := fun k =>
    intervalIntegral.integral_nonneg ht0 fun s _ => viscousFormSq_nonneg hν.le _
  have haE : ∀ k, a k ≤ E := fun k => by linarith [hab k, hb0 k]
  have hbE : ∀ k, b k ≤ E := fun k => by linarith [hab k, ha0 k]
  have hkin : (1 / 2 : ℝ) * ‖(v t : L2VF)‖ ^ 2 ≤ Filter.liminf a atTop :=
    kineticEnergy_liminf_le_of_weakTendsto F ν u₀ galSeq κ hκ alPkg ρ v t ht0 htIcc hweak
  have hdiss : ∫ s in (0 : ℝ)..t, viscousFormSq ν (v s : L2VF) ≤ Filter.liminf b atTop :=
    dissipation_liminf_le_of_aeTendsto F ν hν u₀ galSeq κ hκ alPkg ρ v t ht0 htT hae hae_strong hInt
  exact energyBudget_liminf_assembly a b E _ _ hab ha0 hb0 haE hbE hkin hdiss


/-! ### Assembly: the good-representative existential -/

/-- **Torus limit passage — the good-representative existential**, matching the conclusion
of the project axiom `galerkin_limit_passage` byte-for-byte, PROVED from the trace+energy
pillar, GIVEN the energy-class conjunct (4) for the raw Aubin–Lions limit `alPkg.u`
(a.e. `memH1VF` + integrable dissipation on `[0, T]`; supplied by the separate
viscous-limit development).  Conjuncts (0)/(1)/(3) are produced by the weakly-continuous
representative construction of this file; conjunct (2) transfers from
`torus_weakFormNS_of_strongConvergence` through the a.e.-equality (the WeakFormNS
integrals only see a.e. values); conjunct (4) transfers from `h4` the same way. -/
theorem torus_galerkin_limit_passage_of_energyClass
    (F : Torus3NSForms) (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T)
    (u₀ : L2Sigma)
    (galSeq : ∀ n, GalerkinSolutionData F ν u₀ n)
    (κ : ℕ → ℕ) (hκ : StrictMono κ)
    (alPkg : AubinLionsPackage F ν T u₀ galSeq κ)
    (h4 : (∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc 0 T)),
        memH1VF (alPkg.u t : L2VF)) ∧
      IntervalIntegrable (fun s => viscousFormSq ν (alPkg.u s : L2VF))
        MeasureTheory.volume 0 T) :
    ∃ u : Time → L2Sigma,
    (∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc 0 T)), u t = alPkg.u t) ∧
    WeakFormNS ν T (torus3Evolution F) u ∧
    (∀ t, 0 ≤ t → t ≤ T →
      (1 / 2 : ℝ) * ‖(u t : L2VF)‖ ^ 2 +
      ∫ s in (0 : ℝ)..t, viscousFormSq ν (u s : L2VF) ≤
      (1 / 2 : ℝ) * ‖(u₀ : L2VF)‖ ^ 2) ∧
    Filter.Tendsto
      (fun t => (u t : L2VF))
      (nhdsWithin 0 (Set.Ici 0))
      (nhds (u₀ : L2VF)) ∧
    ((∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc 0 T)), memH1VF (u t : L2VF)) ∧
    IntervalIntegrable (fun s => viscousFormSq ν (u s : L2VF))
      MeasureTheory.volume 0 T) ∧
    (∃ ρ : ℕ → ℕ, StrictMono ρ ∧
      ∀ t, t ∈ Set.Icc (0 : ℝ) T → ∀ z : L2VF,
        Filter.Tendsto
          (fun k => inner (𝕜 := ℝ) (((galSeq (κ (alPkg.φ (ρ k)))).u t : L2VF)) z)
          Filter.atTop (nhds (inner (𝕜 := ℝ) ((u t : L2VF)) z))) := by
  obtain ⟨v, ρ, hρ, hae, hae_strong, hweak, hbd, hv0, hlip⟩ :=
    exists_weak_representative F ν hν T hT u₀ galSeq κ hκ alPkg
  have haeIcc : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.Icc (0 : ℝ) T → v t = alPkg.u t :=
    (ae_restrict_iff' measurableSet_Icc).mp hae
  -- integrable dissipation for the representative, transferred from h4 (a.e.-invariance)
  have hIntv : IntervalIntegrable (fun s => viscousFormSq ν (v s : L2VF))
      MeasureTheory.volume 0 T := by
    refine h4.2.congr_ae ?_
    have h1 : ∀ᵐ s ∂(volume.restrict (Set.uIoc (0 : ℝ) T)), v s = alPkg.u s := by
      rw [Set.uIoc_of_le hT.le]
      exact ae_restrict_of_ae_restrict_of_subset Set.Ioc_subset_Icc_self hae
    filter_upwards [h1] with s hs
    rw [hs]
  refine ⟨v, hae, ?_, ?_, ?_, ⟨?_, hIntv⟩, ρ, hρ, hweak⟩
  · -- conjunct (2): WeakFormNS transfer through the a.e.-equality
    have hW : WeakFormNS ν T (torus3Evolution F) alPkg.u :=
      torus_weakFormNS_of_strongConvergence F ν hν T hT u₀ galSeq κ hκ alPkg
    intro ψ hψcs hψsupp hψC1 w hw
    have h := hW ψ hψcs hψsupp hψC1 w hw
    refine Eq.trans (intervalIntegral.integral_congr_ae ?_) h
    filter_upwards [haeIcc] with x hx hxI
    have hxIcc : x ∈ Set.Icc (0 : ℝ) T := by
      rw [Set.uIoc_of_le hT.le] at hxI
      exact ⟨hxI.1.le, hxI.2⟩
    rw [hx hxIcc]
  · -- conjunct (1): ∀t energy inequality
    exact energy_ineq_of_representative F ν hν T hT u₀ galSeq κ hκ alPkg v ρ
      hae hae_strong hweak hIntv
  · -- conjunct (3): strong initial trace
    exact strong_trace_of_props T hT u₀ v hbd hv0 hlip
  · -- conjunct (4a): a.e. memH1VF, transferred
    filter_upwards [h4.1, hae] with t hmem hveq
    rw [hveq]
    exact hmem

end LerayHopf
