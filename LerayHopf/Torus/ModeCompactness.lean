/-
# LerayHopf.Torus.ModeCompactness

Mode-wise Galerkin extraction (issue #23, torus `aubin_lions` removal): equi-Lipschitz test
pairings plus the scalar equicontinuity engine of `Bochner/ScalarEquicontinuity.lean`, assembled
into the capstone wiring `exists_galerkin_modewise_extraction`. Every term is sorry-free.

Assumptions: none (no project axioms, no opaque/unsafe; all leaves proved).
-/
import LerayHopf.Torus.GalerkinODESolve    -- GalerkinSolutionData, velocityProjection_n_norm_le, IsGalerkinTest
import LerayHopf.Torus.ProjectionAdjoint   -- velocity-projection orthogonality calculus (self-adjointness at fixed points)
import LerayHopf.Torus.TestFamily          -- P0.3 leaf: stokesTestPairing_bound_of_galerkinTest
import LerayHopf.Torus.ConvectionExtension -- P0.3 leaf: velocityProjection_n_eq_of_le (level promotion m ≤ n)
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
    simp only [torusDomain_stokes, Torus3NSForms.core_b] at hode
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

/-! ## Riesz limit curve and finite-dim strong convergence (issue #23)

All lemmas below are sorry-free. -/

/-- Private helper (shared by P0.5 and P0.10): on a divergence-free input the level-`N`
Fourier–Galerkin truncation is the orthonormal-coordinate expansion over the
finite-dimensional `velocitySpan N`, with plain `L2VF`-pairing coefficients.

`Pₙ x ∈ velocitySpan N` (`velocityP_initial_mem`), so `Pₙ x = ∑ᵢ ⟪bᵢ, Pₙ x⟫ • bᵢ`
(`OrthonormalBasis.sum_repr'`); the coefficient collapses to `⟪x, bᵢ⟫` by
self-adjointness at the fixed point `bᵢ` (`velocityProjection_n_inner_of_fixed`,
`velocityP_fixes_span`). -/
private theorem velocityProjection_eq_sum_inner (N : ℕ) (x : L2Sigma) :
    velocityProjection_n N (x : L2VF)
      = ∑ i, inner (𝕜 := ℝ) ((x : L2VF))
            ((stdOrthonormalBasis ℝ (velocitySpan N) i : L2VF))
          • ((stdOrthonormalBasis ℝ (velocitySpan N) i : L2VF)) := by
  classical
  set b := stdOrthonormalBasis ℝ (velocitySpan N) with hbdef
  set q : velocitySpan N := ⟨velocityProjection_n N (x : L2VF), velocityP_initial_mem N x⟩
    with hqdef
  -- The coordinates against the basis are plain pairings of `x` itself.
  have hcoef : ∀ i, inner (𝕜 := ℝ) (b i) q
      = inner (𝕜 := ℝ) ((x : L2VF)) ((b i : L2VF)) := by
    intro i
    rw [Submodule.coe_inner]
    show inner (𝕜 := ℝ) ((b i : L2VF)) (velocityProjection_n N (x : L2VF)) = _
    rw [real_inner_comm,
      velocityProjection_n_inner_of_fixed N (x : L2VF) (velocityP_fixes_span N (b i))]
  have hexp : ∑ i, inner (𝕜 := ℝ) (b i) q • b i = q := b.sum_repr' q
  calc velocityProjection_n N (x : L2VF)
      = ((q : velocitySpan N) : L2VF) := rfl
    _ = ((∑ i, inner (𝕜 := ℝ) (b i) q • b i : velocitySpan N) : L2VF) := by rw [hexp]
    _ = ∑ i, inner (𝕜 := ℝ) (b i) q • ((b i : L2VF)) := by
        rw [AddSubmonoidClass.coe_finsetSum]
        exact Finset.sum_congr rfl fun i _ => rfl
    _ = ∑ i, inner (𝕜 := ℝ) ((x : L2VF)) ((b i : L2VF)) • ((b i : L2VF)) :=
        Finset.sum_congr rfl fun i _ => by rw [hcoef i]

/-- Riesz limit curve from uniformly convergent test pairings.

Conclusions: weak convergence at EVERY `t ∈ [0,T]` (against `L2Sigma` tests), the
`M`-ball bound, and AE strong measurability. -/
theorem exists_weak_limit_curve
    (T : ℝ) (hT : 0 < T) (M : ℝ)
    (v : ℕ → ℝ → L2Sigma)
    (hb : ∀ n t, t ∈ Icc (0 : ℝ) T → ‖(v n t : L2VF)‖ ≤ M)
    (hcont : ∀ n, ContinuousOn (fun t => (v n t : L2VF)) (Icc (0 : ℝ) T))
    (w : ℕ → L2Sigma) (hwtest : ∀ m, IsGalerkinTest (w m))
    (hspan : ∀ N : ℕ, ∃ s : Finset ℕ,
      velocitySpan N ≤ Submodule.span ℝ ((fun m => ((w m : L2Sigma) : L2VF)) '' ↑s))
    (g : ℕ → ℝ → ℝ)
    (hconv : ∀ m, TendstoUniformlyOn
      (fun n t => inner (𝕜 := ℝ) ((v n t : L2VF)) ((w m : L2VF))) (g m) atTop
      (Icc (0 : ℝ) T)) :
    ∃ u : Time → L2Sigma,
      (∀ t ∈ Icc (0 : ℝ) T, ∀ z : L2Sigma,
        Tendsto (fun n => inner (𝕜 := ℝ) ((v n t : L2VF)) ((z : L2VF))) atTop
          (𝓝 (inner (𝕜 := ℝ) ((u t : L2VF)) ((z : L2VF))))) ∧
      (∀ t ∈ Icc (0 : ℝ) T, ‖(u t : L2VF)‖ ≤ M) ∧
      AEStronglyMeasurable (fun t => (u t : L2VF)) (volume.restrict (Icc (0 : ℝ) T)) := by
  classical
  have hM : 0 ≤ M := le_trans (norm_nonneg _) (hb 0 0 ⟨le_refl 0, hT.le⟩)
  -- Every Galerkin subspace sits inside the span of the full test family.
  have hspan_all : ∀ N : ℕ, velocitySpan N
      ≤ Submodule.span ℝ (Set.range fun m => ((w m : L2Sigma) : L2VF)) := by
    intro N
    obtain ⟨s, hs⟩ := hspan N
    exact hs.trans (Submodule.span_mono (Set.image_subset_range _ _))
  -- (C-1) The pairing sequence converges for tests in the span of the family.
  have hconv_span : ∀ t ∈ Icc (0 : ℝ) T, ∀ z : L2VF,
      z ∈ Submodule.span ℝ (Set.range fun m => ((w m : L2Sigma) : L2VF)) →
      ∃ l : ℝ, Tendsto (fun n => inner (𝕜 := ℝ) ((v n t : L2VF)) z) atTop (𝓝 l) := by
    intro t ht z hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨m, rfl⟩ := hx
      exact ⟨g m t, (hconv m).tendsto_at ht⟩
    | zero =>
      exact ⟨0, by simp only [inner_zero_right]; exact tendsto_const_nhds⟩
    | add x y hx hy ihx ihy =>
      obtain ⟨lx, hlx⟩ := ihx
      obtain ⟨ly, hly⟩ := ihy
      exact ⟨lx + ly, by simpa [inner_add_right] using hlx.add hly⟩
    | smul c x hx ihx =>
      obtain ⟨lx, hlx⟩ := ihx
      exact ⟨c * lx, by simpa [real_inner_smul_right] using hlx.const_mul c⟩
  -- (C-2) ε/3-extension along `velocityProjection_n_tendsto`: convergence for every
  -- divergence-free test (the pairing sequence is Cauchy, uniformly in the `M`-ball).
  have hconv_sigma : ∀ t ∈ Icc (0 : ℝ) T, ∀ z : L2Sigma,
      ∃ l : ℝ, Tendsto (fun n => inner (𝕜 := ℝ) ((v n t : L2VF)) ((z : L2VF))) atTop
        (𝓝 l) := by
    intro t ht z
    refine cauchySeq_tendsto_of_complete ?_
    rw [Metric.cauchySeq_iff]
    intro ε hε
    have hM1 : (0 : ℝ) < M + 1 := by linarith
    -- Band-limited approximation of `z` within `ε / (4 (M + 1))`.
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (velocityProjection_n_tendsto (z : L2VF))
      (ε / (4 * (M + 1))) (by positivity)
    have hδ : ‖(z : L2VF) - velocityProjection_n N (z : L2VF)‖ < ε / (4 * (M + 1)) := by
      have h := hN N le_rfl
      rwa [dist_eq_norm, norm_sub_rev] at h
    -- The approximation lies in `velocitySpan N`, so its pairing sequence converges.
    obtain ⟨l, hl⟩ := hconv_span t ht _ (hspan_all N (velocityP_initial_mem N z))
    obtain ⟨n₀, hn₀⟩ := Metric.tendsto_atTop.mp hl (ε / 4) (by positivity)
    refine ⟨n₀, fun a ha b hb' => ?_⟩
    -- Uniform-ball tail estimate off the band-limited approximation.
    have key : ∀ n, |inner (𝕜 := ℝ) ((v n t : L2VF)) ((z : L2VF))
        - inner (𝕜 := ℝ) ((v n t : L2VF)) (velocityProjection_n N (z : L2VF))| < ε / 4 := by
      intro n
      rw [← inner_sub_right]
      refine lt_of_le_of_lt (abs_real_inner_le_norm _ _) ?_
      have h1 : ‖(v n t : L2VF)‖ * ‖(z : L2VF) - velocityProjection_n N (z : L2VF)‖
          ≤ (M + 1) * ‖(z : L2VF) - velocityProjection_n N (z : L2VF)‖ :=
        mul_le_mul_of_nonneg_right (le_trans (hb n t ht) (by linarith)) (norm_nonneg _)
      have h2 : (M + 1) * ‖(z : L2VF) - velocityProjection_n N (z : L2VF)‖
          < (M + 1) * (ε / (4 * (M + 1))) := mul_lt_mul_of_pos_left hδ hM1
      have h3 : (M + 1) * (ε / (4 * (M + 1))) = ε / 4 := by
        field_simp
      linarith
    have hya := hn₀ a ha
    have hyb := hn₀ b hb'
    rw [Real.dist_eq] at hya hyb ⊢
    have ka := key a
    have kb := key b
    have t1 := abs_sub_le (inner (𝕜 := ℝ) ((v a t : L2VF)) ((z : L2VF)))
      (inner (𝕜 := ℝ) ((v a t : L2VF)) (velocityProjection_n N (z : L2VF)))
      (inner (𝕜 := ℝ) ((v b t : L2VF)) ((z : L2VF)))
    have t2 := abs_sub_le (inner (𝕜 := ℝ) ((v a t : L2VF)) (velocityProjection_n N (z : L2VF)))
      (inner (𝕜 := ℝ) ((v b t : L2VF)) (velocityProjection_n N (z : L2VF)))
      (inner (𝕜 := ℝ) ((v b t : L2VF)) ((z : L2VF)))
    have t3 := abs_sub_le (inner (𝕜 := ℝ) ((v a t : L2VF)) (velocityProjection_n N (z : L2VF)))
      l (inner (𝕜 := ℝ) ((v b t : L2VF)) (velocityProjection_n N (z : L2VF)))
    have e1 := abs_sub_comm (inner (𝕜 := ℝ) ((v b t : L2VF)) (velocityProjection_n N (z : L2VF)))
      (inner (𝕜 := ℝ) ((v b t : L2VF)) ((z : L2VF)))
    have e2 := abs_sub_comm l (inner (𝕜 := ℝ) ((v b t : L2VF)) (velocityProjection_n N (z : L2VF)))
    linarith
  -- (C-3) Fréchet–Riesz at each time: the limit functional is linear and `M`-bounded,
  -- so it is represented by an element `u t` of the `M`-ball of `L2Sigma`.
  have key : ∀ t : ℝ, ∃ ut : L2Sigma,
      (t ∈ Icc (0 : ℝ) T → ∀ z : L2Sigma,
        Tendsto (fun n => inner (𝕜 := ℝ) ((v n t : L2VF)) ((z : L2VF))) atTop
          (𝓝 (inner (𝕜 := ℝ) ((ut : L2VF)) ((z : L2VF))))) ∧
      (t ∈ Icc (0 : ℝ) T → ‖(ut : L2VF)‖ ≤ M) := by
    intro t
    by_cases ht : t ∈ Icc (0 : ℝ) T
    · choose l hl using hconv_sigma t ht
      have hadd : ∀ z₁ z₂ : L2Sigma, l (z₁ + z₂) = l z₁ + l z₂ := by
        intro z₁ z₂
        refine tendsto_nhds_unique (hl (z₁ + z₂)) ?_
        simpa [Submodule.coe_add, inner_add_right] using (hl z₁).add (hl z₂)
      have hsmul : ∀ (c : ℝ) (z : L2Sigma), l (c • z) = c * l z := by
        intro c z
        refine tendsto_nhds_unique (hl (c • z)) ?_
        simpa [Submodule.coe_smul, real_inner_smul_right] using (hl z).const_mul c
      have hbound : ∀ z : L2Sigma, ‖l z‖ ≤ M * ‖z‖ := by
        intro z
        rw [Real.norm_eq_abs]
        refine le_of_tendsto (hl z).abs (Eventually.of_forall fun n => ?_)
        exact (abs_real_inner_le_norm _ _).trans
          (mul_le_mul_of_nonneg_right (hb n t ht) (norm_nonneg _))
      let Llin : L2Sigma →ₗ[ℝ] ℝ :=
        { toFun := l
          map_add' := hadd
          map_smul' := fun c z => by simpa using hsmul c z }
      have hLbound : ∀ z : L2Sigma, ‖Llin z‖ ≤ M * ‖z‖ := hbound
      let Lc : L2Sigma →L[ℝ] ℝ := LinearMap.mkContinuous Llin M hLbound
      refine ⟨(InnerProductSpace.toDual ℝ L2Sigma).symm Lc, fun _ z => ?_, fun _ => ?_⟩
      · have hval : inner (𝕜 := ℝ)
            ((InnerProductSpace.toDual ℝ L2Sigma).symm Lc) z = Lc z :=
          InnerProductSpace.toDual_symm_apply
        have hcoe : inner (𝕜 := ℝ)
            ((((InnerProductSpace.toDual ℝ L2Sigma).symm Lc : L2Sigma) : L2VF)) ((z : L2VF))
            = Lc z := by
          rw [← Submodule.coe_inner]; exact hval
        rw [hcoe]
        exact hl z
      · have h1 : ‖(InnerProductSpace.toDual ℝ L2Sigma).symm Lc‖ = ‖Lc‖ :=
          (InnerProductSpace.toDual ℝ L2Sigma).symm.norm_map Lc
        have h2 : ‖Lc‖ ≤ M := LinearMap.mkContinuous_norm_le Llin hM hLbound
        show ‖(((InnerProductSpace.toDual ℝ L2Sigma).symm Lc : L2Sigma) : L2VF)‖ ≤ M
        rw [Submodule.norm_coe, h1]
        exact h2
    · exact ⟨0, fun ht' => absurd ht' ht, fun ht' => absurd ht' ht⟩
  choose u hu using key
  have hweak : ∀ t ∈ Icc (0 : ℝ) T, ∀ z : L2Sigma,
      Tendsto (fun n => inner (𝕜 := ℝ) ((v n t : L2VF)) ((z : L2VF))) atTop
        (𝓝 (inner (𝕜 := ℝ) ((u t : L2VF)) ((z : L2VF)))) := fun t ht => (hu t).1 ht
  -- (C-4) Measurability, by a GENUINE ∀t-pointwise route: the pairings of `u` against
  -- the test family agree with the continuous uniform limits `g m` on `[0, T]` …
  have hgcont : ∀ m, ContinuousOn (g m) (Icc (0 : ℝ) T) := fun m =>
    (hconv m).continuousOn (Frequently.of_forall fun n =>
      (hcont n).inner continuousOn_const)
  have hpair : ∀ m, ∀ t ∈ Icc (0 : ℝ) T,
      inner (𝕜 := ℝ) ((u t : L2VF)) ((w m : L2VF)) = g m t := fun m t ht =>
    tendsto_nhds_unique (hweak t ht (w m)) ((hconv m).tendsto_at ht)
  -- … hence `u` pairs continuously against everything in the span of the family …
  have hspan_cont : ∀ z : L2VF,
      z ∈ Submodule.span ℝ (Set.range fun m => ((w m : L2Sigma) : L2VF)) →
      ContinuousOn (fun t => inner (𝕜 := ℝ) ((u t : L2VF)) z) (Icc (0 : ℝ) T) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨m, rfl⟩ := hx
      exact (hgcont m).congr fun t ht => hpair m t ht
    | zero =>
      simp only [inner_zero_right]; exact continuousOn_const
    | add x y hx hy ihx ihy =>
      refine (ihx.add ihy).congr fun s _ => ?_
      simp [inner_add_right]
    | smul c x hx ihx =>
      refine (ihx.const_smul c).congr fun s _ => ?_
      simp [real_inner_smul_right]
  -- … so each finite-dimensional projection of `u` is continuous on `[0, T]` …
  have hPcont : ∀ N : ℕ,
      ContinuousOn (fun t => velocityProjection_n N ((u t : L2VF))) (Icc (0 : ℝ) T) := by
    intro N
    have hexp : (fun t => velocityProjection_n N ((u t : L2VF)))
        = fun t => ∑ i, inner (𝕜 := ℝ) ((u t : L2VF))
              ((stdOrthonormalBasis ℝ (velocitySpan N) i : L2VF))
            • ((stdOrthonormalBasis ℝ (velocitySpan N) i : L2VF)) :=
      funext fun t => velocityProjection_eq_sum_inner N (u t)
    rw [hexp]
    refine continuousOn_finsetSum _ fun i _ => ?_
    exact (hspan_cont _
      (hspan_all N (stdOrthonormalBasis ℝ (velocitySpan N) i).2)).smul continuousOn_const
  -- … and `u` is the EVERYWHERE-pointwise limit of those projections
  -- (`velocityProjection_n_tendsto`, at every `t`, no a.e. weakening).
  have hmeas : AEStronglyMeasurable (fun t => (u t : L2VF))
      (volume.restrict (Icc (0 : ℝ) T)) :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun N => (hPcont N).aestronglyMeasurable measurableSet_Icc)
      (Eventually.of_forall fun t => velocityProjection_n_tendsto ((u t : L2VF)))
  exact ⟨u, hweak, fun t ht => (hu t).2 ht, hmeas⟩

/-- (P0.10) Step D — finite-dim strong part.  Weak convergence at every `t ∈ [0,T]`
plus uniform ball bounds give strong convergence of the level-`N` projections in
`L²(0,T)`: coordinates against the finite-dimensional `velocitySpan N` converge
pointwise (projection self-adjointness), `‖P_N(v n t − u t)‖ ≤ 2M` dominates, DCT.
Conclusion shape = P0.8's `hint` input (interval integral over `0..T`). -/
theorem integral_sq_proj_tendsto_zero_of_weak
    (T : ℝ) (hT : 0 < T) (M : ℝ) (N : ℕ)
    (v : ℕ → ℝ → L2Sigma) (u : ℝ → L2Sigma)
    (hb : ∀ n t, t ∈ Icc (0 : ℝ) T → ‖(v n t : L2VF)‖ ≤ M)
    (hub : ∀ t ∈ Icc (0 : ℝ) T, ‖(u t : L2VF)‖ ≤ M)
    (hmeas_v : ∀ n, AEStronglyMeasurable (fun t => (v n t : L2VF))
      (volume.restrict (Icc (0 : ℝ) T)))
    (hmeas_u : AEStronglyMeasurable (fun t => (u t : L2VF))
      (volume.restrict (Icc (0 : ℝ) T)))
    (hweak : ∀ t ∈ Icc (0 : ℝ) T, ∀ z : L2Sigma,
      Tendsto (fun n => inner (𝕜 := ℝ) ((v n t : L2VF)) ((z : L2VF))) atTop
        (𝓝 (inner (𝕜 := ℝ) ((u t : L2VF)) ((z : L2VF))))) :
    Tendsto (fun n => ∫ t in (0 : ℝ)..T,
        ‖velocityProjection_n N ((v n t : L2VF)) -
          velocityProjection_n N ((u t : L2VF))‖ ^ 2)
      atTop (𝓝 0) := by
  classical
  have hM : 0 ≤ M := le_trans (norm_nonneg _) (hb 0 0 ⟨le_refl 0, hT.le⟩)
  -- (D-1) Pointwise in `t`: the level-`N` projections converge strongly, since their
  -- finitely many orthonormal coordinates are weak pairings (self-adjointness).
  have hpt : ∀ t ∈ Icc (0 : ℝ) T,
      Tendsto (fun n => ‖velocityProjection_n N ((v n t : L2VF)) -
        velocityProjection_n N ((u t : L2VF))‖ ^ 2) atTop (𝓝 0) := by
    intro t ht
    have hP : Tendsto (fun n => velocityProjection_n N ((v n t : L2VF))) atTop
        (𝓝 (velocityProjection_n N ((u t : L2VF)))) := by
      have hexp : ∀ x : L2Sigma, velocityProjection_n N (x : L2VF)
          = ∑ i, inner (𝕜 := ℝ) ((x : L2VF))
                ((stdOrthonormalBasis ℝ (velocitySpan N) i : L2VF))
              • ((stdOrthonormalBasis ℝ (velocitySpan N) i : L2VF)) :=
        velocityProjection_eq_sum_inner N
      simp only [hexp]
      refine tendsto_finsetSum _ fun i _ => ?_
      exact (hweak t ht ⟨((stdOrthonormalBasis ℝ (velocitySpan N) i : L2VF)),
        velocitySpan_le_sigma N (stdOrthonormalBasis ℝ (velocitySpan N) i).2⟩).smul_const _
    have h0 : Tendsto (fun n => velocityProjection_n N ((v n t : L2VF)) -
        velocityProjection_n N ((u t : L2VF))) atTop (𝓝 0) := by
      have hc : Tendsto (fun _ : ℕ => velocityProjection_n N ((u t : L2VF))) atTop
          (𝓝 (velocityProjection_n N ((u t : L2VF)))) := tendsto_const_nhds
      simpa using hP.sub hc
    simpa using h0.norm.pow 2
  -- (D-2) Dominated convergence on the finite interval, with constant bound `(2M)²`.
  have hsub : Set.uIoc (0 : ℝ) T ⊆ Icc (0 : ℝ) T := by
    rw [Set.uIoc_of_le hT.le]; exact Set.Ioc_subset_Icc_self
  have hres : volume.restrict (Set.uIoc (0 : ℝ) T) ≤ volume.restrict (Icc (0 : ℝ) T) :=
    Measure.restrict_mono hsub le_rfl
  have hFmeas : ∀ n : ℕ, AEStronglyMeasurable
      (fun t => ‖velocityProjection_n N ((v n t : L2VF)) -
        velocityProjection_n N ((u t : L2VF))‖ ^ 2)
      (volume.restrict (Set.uIoc (0 : ℝ) T)) := by
    intro n
    have h1 : AEStronglyMeasurable (fun t => velocityProjection_n N ((v n t : L2VF)))
        (volume.restrict (Icc (0 : ℝ) T)) :=
      (velocityProjection_n N).continuous.comp_aestronglyMeasurable (hmeas_v n)
    have h2 : AEStronglyMeasurable (fun t => velocityProjection_n N ((u t : L2VF)))
        (volume.restrict (Icc (0 : ℝ) T)) :=
      (velocityProjection_n N).continuous.comp_aestronglyMeasurable hmeas_u
    exact ((continuous_pow 2).comp_aestronglyMeasurable (h1.sub h2).norm).mono_measure hres
  have hFbound : ∀ n : ℕ, ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.uIoc (0 : ℝ) T →
      ‖‖velocityProjection_n N ((v n t : L2VF)) -
        velocityProjection_n N ((u t : L2VF))‖ ^ 2‖ ≤ (2 * M) ^ 2 := by
    intro n
    refine Eventually.of_forall fun t htI => ?_
    have ht : t ∈ Icc (0 : ℝ) T := hsub htI
    have h1 : ‖velocityProjection_n N ((v n t : L2VF))‖ ≤ M :=
      (Torus.velocityProjection_n_norm_le N _).trans (hb n t ht)
    have h2 : ‖velocityProjection_n N ((u t : L2VF))‖ ≤ M :=
      (Torus.velocityProjection_n_norm_le N _).trans (hub t ht)
    have h3 : ‖velocityProjection_n N ((v n t : L2VF)) -
        velocityProjection_n N ((u t : L2VF))‖ ≤ 2 * M :=
      (norm_sub_le _ _).trans (by linarith)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) h3 2
  have hlim : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.uIoc (0 : ℝ) T →
      Tendsto (fun n => ‖velocityProjection_n N ((v n t : L2VF)) -
        velocityProjection_n N ((u t : L2VF))‖ ^ 2) atTop (𝓝 ((fun _ => (0 : ℝ)) t)) :=
    Eventually.of_forall fun t htI => hpt t (hsub htI)
  have hdct := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (μ := volume) (a := 0) (b := T) (f := fun _ => (0 : ℝ))
    (F := fun n t => ‖velocityProjection_n N ((v n t : L2VF)) -
      velocityProjection_n N ((u t : L2VF))‖ ^ 2)
    (fun _ => (2 * M) ^ 2)
    (Eventually.of_forall hFmeas)
    (Eventually.of_forall hFbound)
    intervalIntegrable_const
    hlim
  simpa using hdct

/-- (P0.11) T-AL-4 capstone: extraction + limit curve for `galSeq`, the clean handle
for T-AL-5/6.  Conjuncts: strict monotonicity, weak convergence at EVERY `t ∈ [0,T]`
against `L2Sigma` tests, the explicit `‖u₀‖`-ball bound, AE strong measurability
(package field 5, byte-matching measure), and the Step-D finite-dim strong part for
every level `N`.

The body is the REAL wiring against the merged T-AL-1/T-AL-3 production theorems
(fully qualified) + the sorried P0.5/P0.10 above — it verifies that the P0.5
instantiation with the production outputs type-composes exactly as claimed. -/
theorem exists_limit_curve_of_galSeq
    (F : Torus3NSForms) (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T)
    (u₀ : L2Sigma) (galSeq : ∀ n, GalerkinSolutionData F ν u₀ n) :
    ∃ (φ : ℕ → ℕ) (u : Time → L2Sigma), StrictMono φ ∧
      (∀ t ∈ Icc (0 : ℝ) T, ∀ z : L2Sigma,
        Tendsto (fun n => inner (𝕜 := ℝ) (((galSeq (φ n)).u t : L2VF)) ((z : L2VF)))
          atTop (𝓝 (inner (𝕜 := ℝ) ((u t : L2VF)) ((z : L2VF))))) ∧
      (∀ t ∈ Icc (0 : ℝ) T, ‖(u t : L2VF)‖ ≤ ‖(u₀ : L2VF)‖) ∧
      AEStronglyMeasurable (fun t => (u t : L2VF)) (volume.restrict (Icc (0 : ℝ) T)) ∧
      ∀ N : ℕ, Tendsto (fun n => ∫ t in (0 : ℝ)..T,
          ‖velocityProjection_n N (((galSeq (φ n)).u t : L2VF)) -
            velocityProjection_n N ((u t : L2VF))‖ ^ 2)
        atTop (𝓝 0) := by
  classical
  -- T-AL-1: the countable spanning Galerkin test family (production, fully qualified).
  obtain ⟨w, hwtest, hspan⟩ := _root_.LerayHopf.exists_galerkin_test_family
  -- T-AL-3: the mode-wise extraction over that family (production, fully qualified).
  obtain ⟨φ, hφ, g, hconv⟩ :=
    _root_.LerayHopf.exists_galerkin_modewise_extraction F ν hν T hT u₀ galSeq w hwtest
  -- T-AL-3 exports: ball bound (flag c) and continuity (flag a) for the reindexed curves.
  have hb : ∀ n t, t ∈ Icc (0 : ℝ) T → ‖((galSeq (φ n)).u t : L2VF)‖ ≤ ‖(u₀ : L2VF)‖ :=
    fun n t ht => _root_.LerayHopf.galerkin_u_norm_le F ν u₀ (φ n) (galSeq (φ n)) t ht.1
  have hcont : ∀ n, ContinuousOn (fun t => ((galSeq (φ n)).u t : L2VF)) (Icc (0 : ℝ) T) :=
    fun n => (_root_.LerayHopf.galerkin_u_continuousOn F ν u₀ (φ n) (galSeq (φ n))).mono
      Icc_subset_Ici_self
  -- Step C: P0.5 instantiated with the T-AL-3 outputs (the composition under test).
  obtain ⟨u, hweak, hub, hmeas⟩ := exists_weak_limit_curve T hT (‖(u₀ : L2VF)‖)
    (fun n => (galSeq (φ n)).u) hb hcont w hwtest hspan g hconv
  refine ⟨φ, u, hφ, hweak, hub, hmeas, fun N => ?_⟩
  -- Step D: P0.10 at level N (v-measurability from continuity on the compact Icc).
  exact integral_sq_proj_tendsto_zero_of_weak T hT (‖(u₀ : L2VF)‖) N
    (fun n => (galSeq (φ n)).u) u hb hub
    (fun n => (hcont n).aestronglyMeasurable measurableSet_Icc) hmeas hweak

end LerayHopf
