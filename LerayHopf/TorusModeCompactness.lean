/-
# LerayHopf.TorusModeCompactness

T-AL-3 node (torus `aubin_lions` mode-wise campaign, issue #23):
mode-wise Galerkin extraction — equi-Lipschitz test pairings + T-AL-2 engine assembly.

Plan reference: `docs/scratch/torus-aubinlions-modewise-plan.md` §3 row T-AL-3.

Statements frozen by architect gate 2026-07-03 (spike `LerayHopf/Scratch/TorusAubinLionsSpike.lean`,
T-AL-3 section, commit bb02ea7).  Three leaf lemmas (P0.3, P0.9a, P0.9b) are now discharged
(`lean-prover`); the capstone wiring (P0.9c, `exists_galerkin_modewise_extraction`) is the
architect-verified glue body.  Every term is sorry-free.

Assumptions: none (no project axioms, no opaque/unsafe; all leaves proved).
-/
import LerayHopf.TorusGalerkinODESolve    -- GalerkinSolutionData, velocityProjection_n_norm_le, IsGalerkinTest
import LerayHopf.TorusTestFamily          -- P0.3 leaf: stokesTestPairing_bound_of_galerkinTest
import LerayHopf.TorusConvectionExtension -- P0.3 leaf: velocityProjection_n_eq_of_le (level promotion m ≤ n)
import LerayHopf.Bochner.ScalarEquicontinuity  -- T-AL-2 engine: exists_uniform_subseq_of_lipschitz_family

open MeasureTheory Filter Topology Set

namespace LerayHopf

/-- Private helper (shared by P0.3 and P0.9b): the uniform `n`-independent H-bound
`‖u_n(t)‖ ≤ ‖u₀‖` for forward times, from `energy_bound` +
`Torus.velocityProjection_n_norm_le`.  Mirrors `torus_galerkin_norm_le_u0`. -/
private theorem galerkin_norm_le_u0_aux
    (F : Torus3NSForms) (ν : ℝ) (u₀ : L2Sigma) (n : ℕ)
    (D : GalerkinSolutionData F ν u₀ n) (t : ℝ) (ht : 0 ≤ t) :
    ‖(D.u t : L2VF)‖ ≤ ‖(u₀ : L2VF)‖ := by
  have hE := D.energy_bound t ht
  have hP := Torus.velocityProjection_n_norm_le n (u₀ : L2VF)
  have h1 : ‖(D.u t : L2VF)‖ ^ 2 ≤ ‖velocityProjection_n n (u₀ : L2VF)‖ ^ 2 := by linarith
  have h2 : ‖velocityProjection_n n (u₀ : L2VF)‖ ^ 2 ≤ ‖(u₀ : L2VF)‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hP 2
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (by norm_num)).mp (h1.trans h2)

/-- (P0.3) Equi-Lipschitz bound for test pairings [T-AL-3 leaf].

From `u_ode` (fires for `n ≥ m` by `velocityProjection_n_eq_of_le`), `u_hasDeriv` +
`HasDerivAt.inner`, `energy_bound`, the stokes-pairing bound, and `Torus3NSForms.b_bound`.
Forward-only (`0 ≤ s ≤ t`), matching the solution data's time domain.  The `m ≤ n` cutoff is
the T-AL-2 engine's eventual-`n₀` (architect flag d: do NOT strengthen to all-`n`). -/
theorem galerkin_test_pairing_lipschitz
    (F : Torus3NSForms) (ν : ℝ) (hν : 0 < ν) (u₀ : L2Sigma)
    (galSeq : ∀ n, GalerkinSolutionData F ν u₀ n)
    (w : L2Sigma) (m : ℕ) (hw : velocityProjection_n m (w : L2VF) = (w : L2VF)) :
    ∃ L : ℝ, ∀ n, m ≤ n → ∀ s t : ℝ, 0 ≤ s → s ≤ t →
      |inner (𝕜 := ℝ) (((galSeq n).u t : L2VF)) ((w : L2VF)) -
        inner (𝕜 := ℝ) (((galSeq n).u s : L2VF)) ((w : L2VF))| ≤ L * (t - s) := by
  classical
  -- Viscous-pairing L²-bound at the band-limited test `w` (P0.2); clamp the constant `≥ 0`.
  obtain ⟨Cs0, hCs⟩ := stokesTestPairing_bound_of_galerkinTest w ⟨m, hw⟩
  set Cs : ℝ := max Cs0 0 with hCsdef
  have hCs0 : 0 ≤ Cs := le_max_right _ _
  have hCsbd : ∀ u : L2VF, |stokesTestPairing u (w : L2VF)| ≤ Cs * ‖u‖ := fun u =>
    (hCs u).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  -- Convection L²-bound at the Galerkin test `w` (`b_bound`); clamp the constant `≥ 0`.
  obtain ⟨Cb, hCb⟩ := F.b_bound w ⟨m, hw⟩
  set Cb' : ℝ := |Cb| with hCb'
  have hCb'0 : 0 ≤ Cb' := abs_nonneg _
  have hCb'bound : ∀ u v : L2Sigma, |F.b u v w| ≤ Cb' * ‖(u : L2VF)‖ * ‖(v : L2VF)‖ := by
    intro u v
    refine (hCb u v).trans ?_
    nlinarith [le_abs_self Cb, norm_nonneg (u : L2VF), norm_nonneg (v : L2VF),
      mul_nonneg (norm_nonneg (u : L2VF)) (norm_nonneg (v : L2VF))]
  -- Uniform Lipschitz constant, independent of `n` and `t`.
  set L : ℝ := ν * Cs * ‖(u₀ : L2VF)‖ + Cb' * ‖(u₀ : L2VF)‖ ^ 2 with hLdef
  refine ⟨L, fun n hn s t hs hst => ?_⟩
  set gs := galSeq n with hgs
  -- Promote the level-`m` cutoff to level `n ≥ m`, so `u_ode` fires at level `n`.
  have hwn : velocityProjection_n n (w : L2VF) = (w : L2VF) :=
    TorusConvectionExtension.velocityProjection_n_eq_of_le hn (w : L2VF) hw
  -- Scalar derivative `d/dt ⟪u_n(t), w⟫ = -(ν·stokes + b)` at each forward `r` (within `Ici 0`).
  have hderiv : ∀ r ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt (fun s' => inner (𝕜 := ℝ) ((gs.u s' : L2VF)) (w : L2VF))
        (-(ν * stokesTestPairing (gs.u r : L2VF) (w : L2VF) + F.b (gs.u r) (gs.u r) w))
        (Set.Ici 0) r := by
    intro r hr
    have hda := (gs.u_hasDeriv r hr).inner (𝕜 := ℝ) (hasDerivAt_const r (w : L2VF))
    simp only [inner_zero_right, zero_add] at hda
    have hode := gs.u_ode r hr w hwn.symm
    have hval : inner (𝕜 := ℝ) (deriv (fun s' => (gs.u s' : L2VF)) r) (w : L2VF)
        = -(ν * stokesTestPairing (gs.u r : L2VF) (w : L2VF) + F.b (gs.u r) (gs.u r) w) := by
      linarith
    rw [hval] at hda
    exact hda.hasDerivWithinAt
  -- Uniform derivative bound `‖·‖ ≤ L` on `Ici 0` (Cauchy–Schwarz-free: the two form bounds).
  have hbound : ∀ r ∈ Set.Ici (0 : ℝ),
      ‖-(ν * stokesTestPairing (gs.u r : L2VF) (w : L2VF) + F.b (gs.u r) (gs.u r) w)‖ ≤ L := by
    intro r hr
    rw [Real.norm_eq_abs, abs_neg]
    have hnorm : ‖(gs.u r : L2VF)‖ ≤ ‖(u₀ : L2VF)‖ :=
      galerkin_norm_le_u0_aux F ν u₀ n gs r hr
    have h1 : |ν * stokesTestPairing (gs.u r : L2VF) (w : L2VF)| ≤ ν * Cs * ‖(u₀ : L2VF)‖ := by
      rw [abs_mul, abs_of_pos hν, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ hν.le
      exact (hCsbd _).trans (mul_le_mul_of_nonneg_left hnorm hCs0)
    have h2 : |F.b (gs.u r) (gs.u r) w| ≤ Cb' * ‖(u₀ : L2VF)‖ ^ 2 := by
      refine (hCb'bound (gs.u r) (gs.u r)).trans ?_
      have hsq : ‖(gs.u r : L2VF)‖ * ‖(gs.u r : L2VF)‖
          ≤ ‖(u₀ : L2VF)‖ * ‖(u₀ : L2VF)‖ :=
        mul_le_mul hnorm hnorm (norm_nonneg _) (norm_nonneg _)
      calc Cb' * ‖(gs.u r : L2VF)‖ * ‖(gs.u r : L2VF)‖
          = Cb' * (‖(gs.u r : L2VF)‖ * ‖(gs.u r : L2VF)‖) := by ring
        _ ≤ Cb' * (‖(u₀ : L2VF)‖ * ‖(u₀ : L2VF)‖) := mul_le_mul_of_nonneg_left hsq hCb'0
        _ = Cb' * ‖(u₀ : L2VF)‖ ^ 2 := by ring
    calc |ν * stokesTestPairing (gs.u r : L2VF) (w : L2VF) + F.b (gs.u r) (gs.u r) w|
        ≤ |ν * stokesTestPairing (gs.u r : L2VF) (w : L2VF)|
          + |F.b (gs.u r) (gs.u r) w| := abs_add_le _ _
      _ ≤ L := by rw [hLdef]; linarith
  -- Mean-value inequality on the convex set `Ici 0`.
  have hsI : s ∈ Set.Ici (0 : ℝ) := hs
  have htI : t ∈ Set.Ici (0 : ℝ) := le_trans hs hst
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
    (convex_Ici (0 : ℝ)) hsI htI
  rwa [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (show (0 : ℝ) ≤ t - s by linarith)] at hmvt

/-- (P0.9a) Continuity export [T-AL-3 leaf, architect flag (a)]: the Galerkin curve is
norm-continuous on `[0,∞)`.  From `u_hasDeriv`: each forward time `t ≥ 0` has a
genuine `HasDerivAt` (full-neighborhood), hence `ContinuousAt`, hence
`ContinuousOn` on `Ici 0` via `ContinuousAt.continuousWithinAt`.  P0.5's `hcont`
is the `.mono Icc_subset_Ici_self` restriction to `Icc 0 T`. -/
theorem galerkin_u_continuousOn
    (F : Torus3NSForms) (ν : ℝ) (u₀ : L2Sigma) (n : ℕ)
    (D : GalerkinSolutionData F ν u₀ n) :
    ContinuousOn (fun t => (D.u t : L2VF)) (Ici (0 : ℝ)) :=
  fun s hs => ((D.u_hasDeriv s hs).continuousAt).continuousWithinAt

/-- (P0.9b) Ball-bound export [T-AL-3 leaf, architect flag (c)]: uniform n-independent bound
`‖u_n(t)‖ ≤ ‖u₀‖` for forward times, from `energy_bound` +
`Torus.velocityProjection_n_norm_le`.  P0.5's `hb` instantiates
`M := ‖(u₀ : L2VF)‖`. -/
theorem galerkin_u_norm_le
    (F : Torus3NSForms) (ν : ℝ) (u₀ : L2Sigma) (n : ℕ)
    (D : GalerkinSolutionData F ν u₀ n) :
    ∀ t : ℝ, 0 ≤ t → ‖(D.u t : L2VF)‖ ≤ ‖(u₀ : L2VF)‖ :=
  galerkin_norm_le_u0_aux F ν u₀ n D

/-- (P0.9c) T-AL-3 capstone [architect flags (b)+(d)]: ONE strictly monotone
extraction `φ` and ONE packaged limit function `g : ℕ → ℝ → ℝ` such that every
test pairing `t ↦ ⟪u_{φ(n)}(t), w m⟫` converges uniformly on `[0,T]` to `g m`.
The conclusion is in the reindexed single-`g` form that drops verbatim into
P0.5 `exists_weak_limit_curve`'s `hconv` with `v := fun n => (galSeq (φ n)).u`.

The body is the architect-verified wiring (not a sorry): Classical band-limit
cutoffs from `IsGalerkinTest`, P0.3 Lipschitz constants, `B m = ‖u₀‖·‖w m‖`
via P0.9b + Cauchy–Schwarz, then the T-AL-2 engine + `choose`. -/
theorem exists_galerkin_modewise_extraction
    (F : Torus3NSForms) (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T)
    (u₀ : L2Sigma) (galSeq : ∀ n, GalerkinSolutionData F ν u₀ n)
    (w : ℕ → L2Sigma) (hwtest : ∀ m, IsGalerkinTest (w m)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : ℕ → ℝ → ℝ, ∀ m,
      TendstoUniformlyOn
        (fun n t => inner (𝕜 := ℝ) (((galSeq (φ n)).u t : L2VF)) ((w m : L2VF)))
        (g m) atTop (Icc (0 : ℝ) T) := by
  classical
  -- Per-test band-limit cutoff from `IsGalerkinTest` (flag d: the engine's `n₀ m`).
  have hcut : ∀ m, velocityProjection_n (Classical.choose (hwtest m)) ((w m : L2Sigma) : L2VF)
      = ((w m : L2Sigma) : L2VF) := fun m => Classical.choose_spec (hwtest m)
  -- Per-test Lipschitz constants from P0.3 (fires for `n` past the cutoff).
  choose L hL using fun m =>
    galerkin_test_pairing_lipschitz F ν hν u₀ galSeq (w m) (Classical.choose (hwtest m)) (hcut m)
  -- The T-AL-2 engine over `f m n t := ⟪u_n(t), w m⟫`.
  obtain ⟨φ, hφ, hconv⟩ := exists_uniform_subseq_of_lipschitz_family T hT
    (fun m n t => inner (𝕜 := ℝ) (((galSeq n).u t : L2VF)) ((w m : L2VF)))
    (fun m => ‖(u₀ : L2VF)‖ * ‖((w m : L2Sigma) : L2VF)‖) L
    (fun m n t ht =>
      -- uniform bound: Cauchy–Schwarz + P0.9b (forward time from `ht.1`)
      le_trans (abs_real_inner_le_norm _ _)
        (mul_le_mul_of_nonneg_right (galerkin_u_norm_le F ν u₀ n (galSeq n) t ht.1)
          (norm_nonneg _)))
    (fun m => ⟨Classical.choose (hwtest m), fun n hn s t hs ht hst =>
      hL m n hn s t hs.1 hst⟩)
  -- Package the per-`m` limits into a single function (flag b).
  choose g hg using hconv
  exact ⟨φ, hφ, g, hg⟩

end LerayHopf
