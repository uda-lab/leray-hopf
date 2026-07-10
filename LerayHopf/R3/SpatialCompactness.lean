import LerayHopf.R3.Regularity            -- L2VF_R3, L2Sigma_R3, memH1VF_R3, viscousFormSq_R3, Domain3
import Mathlib.Topology.Sequences          -- IsCompact.tendsto_subseq
import Mathlib.MeasureTheory.Function.L2Space      -- L2 norm² = ∫ ‖·‖²
import Mathlib.MeasureTheory.Integral.Bochner.Set  -- setIntegral, restrict-measure integrals

namespace LerayHopf
open MeasureTheory Filter Topology Metric

/-!
# LOCAL spatial compactness on ℝ³ — axiom-free reduction (P3)

**Milestone:** `p3-spatial-compactness`

This file substantiates — axiom-free and (once `lean-prover` fills the bodies)
sorry-free — the analytic content of the `spatial_compactness_R3` axiom in
`SolutionInterfaces.lean:378–389`.  It *reproduces* that axiom's exact conclusion
shape from ONE clean isolated hypothesis, `LocalRellichInput`, which captures the
genuine analytic frontier.

## Architecture (standalone)

This file is **standalone**: it does **not** import `R3.SolutionInterfaces.lean`, and is
**not** imported by it.  The connection to the axiom is *semantic* (the deliverable's
conclusion is byte-identical to the axiom body, plus a `(B : LocalRellichInput)` binder),
exactly as R3-d (`TrilinearEstimate.lean`) and P5 (`GalerkinScheme.lean`) did.  It does
NOT remove the axiom; it is a sibling proved lemma.

The single isolated frontier is `LocalRellichInput.ballCompact`: the LOCAL compact
embedding `H¹(B_R) ↪↪ L²(B_R)` (Leray 1934; Lemarié-Rieusset §6), which mathlib lacks (no
Rellich–Kondrachov, no compact-embedding API, no Fréchet–Kolmogorov).  **This milestone
proves the reduction AROUND that embedding — the diagonal extraction over growing balls,
the limit assembly, and the divergence-free closure — NOT the embedding itself.**

DAG position:
```
R3/Domain.lean
    └── R3/DivergenceFree.lean
            └── R3/Regularity.lean   (memH1VF_R3, viscousFormSq_R3)
                    └── R3/SpatialCompactness.lean   [THIS FILE]
                            (standalone; NOT importing R3/SolutionInterfaces.lean)
```
Sibling of `R3/SolutionInterfaces.lean`, not a dependency of it.  Added to root `LerayHopf.lean`.

## Declarations (dependency order)

- `LocalRellichInput`                              : isolated analytic frontier (one field, `ballCompact`)
- `L2ballR3`                                       : D0a — L²(B_R) over the restricted measure
- `restrictToBall`                                 : D0b — restriction map `L2VF_R3 → L2ballR3 R`
- `setIntegral_normSq_eq_dist_sq_restrictToBall`   : D0c — bridge: ball ∫‖·‖² = L²(B_R) dist²
- `exists_subseq_tendsto_on_ball`                  : D1 — per-ball subsequence extraction
- `exists_subseq_tendsto_on_all_balls`             : D2 — diagonal over expanding balls
- `ballLimits_are_consistent`                      : D3a — per-ball limits are mutually consistent
- `ballLimit_global_mem_L2Sigma`                   : D3b — assembled global limit is div-free
- `localCompactness_R3_of_ballCompact`             : D4 — DELIVERABLE (≡ `spatial_compactness_R3`)

## Assumptions

Zero new `axiom`/`opaque`/`constant`.  The genuine frontier is carried by the **hypothesis**
`LocalRellichInput` (an explicit argument), exactly as R3-d's `hdiv` and P5's
`SchwartzGalerkinBasis.dense_span`.  A hypothesis is not an axiom.
-/

/-! ### Tier 0 — restriction plumbing -/

/-- **D0a.** L²(B_R): the Lp space over the volume measure restricted to the closed ball
of radius `R`.  This is the carrier that supplies a usable metric for
`IsCompact.tendsto_subseq`. -/
noncomputable abbrev L2ballR3 (R : ℝ) :=
  Lp (EuclideanSpace ℝ (Fin 3)) 2 (volume.restrict (Metric.closedBall (0 : Domain3) R))

/-- **D0b.** Restriction of an L²(ℝ³) velocity field to the ball `B_R`, as an element of
`L2ballR3 R`.

Goes through the underlying a.e.-function: `MemLp.restrict (Lp.memLp w)` gives
`MemLp (w : Domain3 → _) 2 (volume.restrict (closedBall 0 R))`, and `MemLp.toLp` packages it.
(Restriction is not measure-preserving, so `Lp.compMeasurePreserving` is not applicable —
G1.) -/
noncomputable def restrictToBall (R : ℝ) (w : L2VF_R3) : L2ballR3 R :=
  MemLp.toLp (w : Domain3 → EuclideanSpace ℝ (Fin 3))
    ((Lp.memLp w).restrict (Metric.closedBall (0 : Domain3) R))

/-- Isolated analytic frontier: LOCAL compact embedding `H¹(B_R) ↪↪ L²(B_R)`.

For every radius `R` and every uniform bound `M`, the image under restriction-to-`B_R`
of the L²/H¹-bounded div-free family is contained in a COMPACT subset of `L²(B_R)`.

This is the unconditional local Rellich theorem (Leray 1934; Lemarié-Rieusset §6). It is
NOT provable in current mathlib (no Rellich / compact embedding / Fréchet–Kolmogorov).

Honesty (no-smuggle): the hypothesis speaks ONLY ball-by-ball and ONLY supplies
precompactness of a SET in a SINGLE L²(B_R); it provides NEITHER a subsequence, NOR a
limit, NOR cross-ball coherence, NOR div-freeness. All of those are derived axiom-free in
the reduction below. -/
structure LocalRellichInput where
  ballCompact : ∀ (M : ℝ) (R : ℝ),
    ∃ K : Set (L2ballR3 R), IsCompact K ∧
      ∀ (w : L2VF_R3), w ∈ L2Sigma_R3 → memH1VF_R3 w →
        ‖w‖ ≤ M → viscousFormSq_R3 1 w ≤ M ^ 2 →
        restrictToBall R w ∈ K

/-- L²-norm-squared as an integral of the pointwise squared norm, for an element of an
`L²` space over a real inner-product target. -/
theorem normSq_eq_integral_normSq {μ : Measure Domain3}
    (h : Lp (EuclideanSpace ℝ (Fin 3)) 2 μ) :
    ‖h‖ ^ 2 = ∫ x, ‖(h x : EuclideanSpace ℝ (Fin 3))‖ ^ 2 ∂μ := by
  have hre : ‖h‖ ^ 2 = (inner ℝ h h : ℝ) := by
    have := norm_sq_eq_re_inner (𝕜 := ℝ) h
    simpa using this
  rw [hre, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards with x
  exact real_inner_self_eq_norm_sq _

/-- **D0c.** The ball set-integral of the squared difference equals the squared
L²(B_R)-distance of the two restrictions. This is the bridge between the conclusion's
set-integral shape and the metric in which `IsCompact.tendsto_subseq` produces convergence. -/
theorem setIntegral_normSq_eq_dist_sq_restrictToBall (R : ℝ) (u v : L2VF_R3) :
    ∫ x in Metric.closedBall (0 : Domain3) R,
      ‖(u x : EuclideanSpace ℝ (Fin 3)) - (v x : EuclideanSpace ℝ (Fin 3))‖ ^ 2
      ∂(volume : Measure Domain3)
    = dist (restrictToBall R u) (restrictToBall R v) ^ 2 := by
  set μ : Measure Domain3 := volume.restrict (Metric.closedBall (0 : Domain3) R) with hμ
  rw [dist_eq_norm, normSq_eq_integral_normSq (restrictToBall R u - restrictToBall R v)]
  -- the integral over `volume.restrict ball` is the set integral over the ball
  show ∫ x in Metric.closedBall (0 : Domain3) R,
      ‖(u x : EuclideanSpace ℝ (Fin 3)) - (v x : EuclideanSpace ℝ (Fin 3))‖ ^ 2 ∂volume
    = ∫ x,
      ‖((restrictToBall R u - restrictToBall R v) x : EuclideanSpace ℝ (Fin 3))‖ ^ 2 ∂μ
  rw [hμ]
  refine integral_congr_ae ?_
  have hsub : ⇑(restrictToBall R u - restrictToBall R v)
      =ᵐ[μ] (fun x => (restrictToBall R u) x - (restrictToBall R v) x) :=
    Lp.coeFn_sub _ _
  have hu : ⇑(restrictToBall R u) =ᵐ[μ] (u : Domain3 → EuclideanSpace ℝ (Fin 3)) :=
    MemLp.coeFn_toLp _
  have hv : ⇑(restrictToBall R v) =ᵐ[μ] (v : Domain3 → EuclideanSpace ℝ (Fin 3)) :=
    MemLp.coeFn_toLp _
  filter_upwards [hsub, hu, hv] with x hxsub hxu hxv
  rw [hxsub, hxu, hxv]

/-! ### Tier 1 — per-ball subsequence extraction -/

/-- **D1.** From the isolated per-ball precompactness, any admissible sequence has a
subsequence whose ball-restrictions converge in L²(B_R). -/
theorem exists_subseq_tendsto_on_ball (B : LocalRellichInput) (M R : ℝ)
    (z : ℕ → L2VF_R3) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hmem : ∀ n, z n ∈ L2Sigma_R3) (hH1 : ∀ n, memH1VF_R3 (z n))
    (hbd : ∀ n, ‖z n‖ ≤ M) (hvf : ∀ n, viscousFormSq_R3 1 (z n) ≤ M ^ 2) :
    ∃ (ρ : ℕ → ℕ) (g : L2ballR3 R), StrictMono ρ ∧
      Tendsto (fun n => restrictToBall R (z (φ (ρ n)))) atTop (𝓝 g) := by
  obtain ⟨K, hK, hKmem⟩ := B.ballCompact M R
  have hmemK : ∀ n, restrictToBall R (z (φ n)) ∈ K := fun n =>
    hKmem (z (φ n)) (hmem (φ n)) (hH1 (φ n)) (hbd (φ n)) (hvf (φ n))
  obtain ⟨g, _, ρ, hρ, htend⟩ := hK.tendsto_subseq hmemK
  exact ⟨ρ, g, hρ, by simpa [Function.comp_def] using htend⟩

/-! ### Tier 2 — diagonal over expanding balls (structural core) -/

/-- Factorization of a nested family of extractions: if `Φ (k+1) = Φ k ∘ ρ k` with each
`ρ k` strictly monotone, then for `k ≤ n` the extraction `Φ n` is `Φ k` post-composed with a
strictly monotone map. -/
private theorem nested_extraction_factor (Φ ρ : ℕ → ℕ → ℕ)
    (hρ : ∀ k, StrictMono (ρ k)) (hstep : ∀ k, Φ (k + 1) = Φ k ∘ ρ k) :
    ∀ k n, k ≤ n → ∃ R : ℕ → ℕ, StrictMono R ∧ Φ n = Φ k ∘ R := by
  intro k n hkn
  induction n with
  | zero =>
    obtain rfl : k = 0 := Nat.le_zero.mp hkn
    exact ⟨id, strictMono_id, rfl⟩
  | succ m ih =>
    rcases Nat.lt_or_ge k (m + 1) with hlt | hge
    · obtain ⟨R, hR, hReq⟩ := ih (Nat.lt_succ_iff.mp hlt)
      refine ⟨R ∘ ρ m, hR.comp (hρ m), ?_⟩
      rw [hstep m, hReq]
      rfl
    · obtain rfl : k = m + 1 := Nat.le_antisymm hkn hge
      exact ⟨id, strictMono_id, rfl⟩

/-- **D2.** Diagonal extraction over the radii R = 1, 2, 3, …: a SINGLE strictly monotone
subsequence whose ball-restrictions converge in L²(B_k) for every natural k (hence,
by monotonicity of balls, for every real R). -/
theorem exists_subseq_tendsto_on_all_balls (B : LocalRellichInput) (M : ℝ)
    (z : ℕ → L2VF_R3)
    (hmem : ∀ n, z n ∈ L2Sigma_R3) (hH1 : ∀ n, memH1VF_R3 (z n))
    (hbd : ∀ n, ‖z n‖ ≤ M) (hvf : ∀ n, viscousFormSq_R3 1 (z n) ≤ M ^ 2) :
    ∃ (ψ : ℕ → ℕ), StrictMono ψ ∧
      ∀ k : ℕ, ∃ g : L2ballR3 (k : ℝ),
        Tendsto (fun n => restrictToBall (k : ℝ) (z (ψ n))) atTop (𝓝 g) := by
  classical
  -- Cumulative extraction data: `Φ k` is the level-`k` cumulative extraction, `ρ k` the
  -- one-step refinement (D1 applied at radius `k` to the previously-extracted sequence).
  -- We build `Φ`, `ρ` recursively so that `Φ (k+1) = Φ k ∘ ρ k` and the ball-`k`
  -- restrictions of `z ∘ Φ (k+1)` converge.
  -- Step function: given a cumulative extraction `φ` (with proof of StrictMono), produce the
  -- D1 refinement at radius `k` plus the convergence witness.
  let stepData : ∀ (k : ℕ) (φ : ℕ → ℕ), StrictMono φ →
      { ρ : ℕ → ℕ // StrictMono ρ ∧ ∃ g : L2ballR3 (k : ℝ),
        Tendsto (fun n => restrictToBall (k : ℝ) (z (φ (ρ n)))) atTop (𝓝 g) } :=
    fun k φ hφ =>
      let h := exists_subseq_tendsto_on_ball B M (k : ℝ) z φ hφ hmem hH1 hbd hvf
      ⟨h.choose, h.choose_spec.choose_spec.1,
        h.choose_spec.choose, h.choose_spec.choose_spec.2⟩
  -- Recursively assemble `Φ : ℕ → ℕ → ℕ` and the proofs.
  let rec_data : ℕ → { Φk : ℕ → ℕ // StrictMono Φk } := fun k => Nat.rec
    (⟨id, strictMono_id⟩)
    (fun j prev => ⟨prev.1 ∘ (stepData j prev.1 prev.2).1,
      prev.2.comp (stepData j prev.1 prev.2).2.1⟩) k
  let Φ : ℕ → ℕ → ℕ := fun k => (rec_data k).1
  let ρ : ℕ → ℕ → ℕ := fun k => (stepData k (rec_data k).1 (rec_data k).2).1
  have hΦmono : ∀ k, StrictMono (Φ k) := fun k => (rec_data k).2
  have hρmono : ∀ k, StrictMono (ρ k) := fun k =>
    (stepData k (rec_data k).1 (rec_data k).2).2.1
  have hstep : ∀ k, Φ (k + 1) = Φ k ∘ ρ k := fun k => rfl
  have hconv : ∀ k : ℕ, ∃ g : L2ballR3 (k : ℝ),
      Tendsto (fun n => restrictToBall (k : ℝ) (z (Φ (k + 1) n))) atTop (𝓝 g) := by
    intro k
    obtain ⟨g, hg⟩ := (stepData k (rec_data k).1 (rec_data k).2).2.2
    exact ⟨g, hg⟩
  -- The diagonal subsequence.
  refine ⟨fun n => Φ (n + 1) (n + 1), ?_, ?_⟩
  · -- StrictMono of the diagonal.
    intro a b hab
    have h1 : Φ (a + 1) (a + 1) < Φ (a + 1) (b + 1) :=
      hΦmono (a + 1) (by omega)
    -- `Φ (a+1)` is a prefix-factor of `Φ (b+1)` since `a+1 ≤ b+1`.
    obtain ⟨R, hR, hReq⟩ :=
      nested_extraction_factor Φ ρ hρmono hstep (a + 1) (b + 1) (by omega)
    have h2 : Φ (a + 1) (b + 1) ≤ Φ (b + 1) (b + 1) := by
      rw [hReq]
      exact (hΦmono (a + 1)).monotone (hR.id_le (b + 1))
    exact lt_of_lt_of_le h1 h2
  · -- Ball-`k` convergence of the diagonal.
    intro k
    obtain ⟨g, hg⟩ := hconv k
    refine ⟨g, ?_⟩
    -- For `n ≥ k`, factor `Φ (n+1) = Φ (k+1) ∘ R n` with `R n` strictly monotone.
    -- Define `σ n` so that the diagonal value equals `Φ (k+1) (σ n)` with `σ n ≥ n`.
    have hfact : ∀ n, k ≤ n → ∃ s : ℕ, n + 1 ≤ s ∧ Φ (n + 1) (n + 1) = Φ (k + 1) s := by
      intro n hn
      obtain ⟨R, hR, hReq⟩ :=
        nested_extraction_factor Φ ρ hρmono hstep (k + 1) (n + 1) (by omega)
      refine ⟨R (n + 1), hR.id_le (n + 1), ?_⟩
      rw [hReq]; rfl
    -- Choose `σ : ℕ → ℕ` realizing the factorization for `n ≥ k`.
    choose s hs_ge hs_eq using fun n (hn : k ≤ n) => hfact n hn
    set σ : ℕ → ℕ := fun n => if hn : k ≤ n then s n hn else n + 1 with hσ
    have hσ_ge : ∀ n, k ≤ n → n + 1 ≤ σ n := by
      intro n hn; simp only [hσ, dif_pos hn]; exact hs_ge n hn
    have hσ_eq : ∀ n, k ≤ n → Φ (n + 1) (n + 1) = Φ (k + 1) (σ n) := by
      intro n hn; simp only [hσ, dif_pos hn]; exact hs_eq n hn
    -- The diagonal agrees eventually with `(restrictToBall k ∘ z ∘ Φ (k+1)) ∘ σ`.
    have hσ_top : Tendsto σ atTop atTop := by
      refine tendsto_atTop_mono' atTop ?_ tendsto_id
      filter_upwards [eventually_ge_atTop k] with n hn
      show n ≤ σ n
      exact le_trans (Nat.le_succ n) (hσ_ge n hn)
    have hcomp := hg.comp hσ_top
    refine hcomp.congr' ?_
    filter_upwards [eventually_ge_atTop k] with n hn
    simp only [Function.comp_apply]
    rw [hσ_eq n hn]

/-! ### Tier 3 — limit assembly + div-free closure -/

/-- Further restriction of an `L²(B_k)` element to a smaller ball `B_R` (`R ≤ k`), through the
underlying a.e. function.  This is well-defined because `volume.restrict (B_R) ≤
volume.restrict (B_k)`. -/
private noncomputable def furtherRestrict (R k : ℝ) (h : (R : ℝ) ≤ k)
    (w : L2ballR3 k) : L2ballR3 R :=
  MemLp.toLp (w : Domain3 → EuclideanSpace ℝ (Fin 3))
    (by
      have hsub : Metric.closedBall (0 : Domain3) R ⊆ Metric.closedBall (0 : Domain3) k :=
        Metric.closedBall_subset_closedBall h
      have hle : volume.restrict (Metric.closedBall (0 : Domain3) R)
          ≤ volume.restrict (Metric.closedBall (0 : Domain3) k) :=
        Measure.restrict_mono hsub le_rfl
      exact (Lp.memLp w).mono_measure hle)

/-- The further-restriction's underlying function agrees a.e. (on `B_R`) with the original. -/
private theorem furtherRestrict_coeFn (R k : ℝ) (h : R ≤ k) (w : L2ballR3 k) :
    (furtherRestrict R k h w : Domain3 → EuclideanSpace ℝ (Fin 3))
      =ᵐ[volume.restrict (Metric.closedBall (0 : Domain3) R)]
        (w : Domain3 → EuclideanSpace ℝ (Fin 3)) :=
  MemLp.coeFn_toLp _

/-- Further restriction is distance-nonincreasing, hence continuous. -/
private theorem furtherRestrict_dist_le (R k : ℝ) (h : R ≤ k) (w w' : L2ballR3 k) :
    dist (furtherRestrict R k h w) (furtherRestrict R k h w') ≤ dist w w' := by
  have hsub : Metric.closedBall (0 : Domain3) R ⊆ Metric.closedBall (0 : Domain3) k :=
    Metric.closedBall_subset_closedBall h
  have hle : volume.restrict (Metric.closedBall (0 : Domain3) R)
      ≤ volume.restrict (Metric.closedBall (0 : Domain3) k) :=
    Measure.restrict_mono hsub le_rfl
  rw [Lp.dist_def, Lp.dist_def]
  have hcong : ⇑(furtherRestrict R k h w) - ⇑(furtherRestrict R k h w')
      =ᵐ[volume.restrict (Metric.closedBall (0 : Domain3) R)]
        (fun x => (w x : EuclideanSpace ℝ (Fin 3)) - (w' x : EuclideanSpace ℝ (Fin 3))) := by
    filter_upwards [furtherRestrict_coeFn R k h w, furtherRestrict_coeFn R k h w'] with x hx hx'
    simp [hx, hx']
  rw [eLpNorm_congr_ae hcong]
  set F : Domain3 → EuclideanSpace ℝ (Fin 3) :=
    fun x => (w x : EuclideanSpace ℝ (Fin 3)) - (w' x : EuclideanSpace ℝ (Fin 3)) with hF
  have hcong2 : (⇑w - ⇑w')
      =ᵐ[volume.restrict (Metric.closedBall (0 : Domain3) k)] F :=
    Filter.Eventually.of_forall (fun _ => rfl)
  rw [eLpNorm_congr_ae hcong2]
  have hfin : eLpNorm F 2 (volume.restrict (Metric.closedBall (0 : Domain3) k)) ≠ ⊤ := by
    rw [← eLpNorm_congr_ae hcong2]
    rw [← eLpNorm_congr_ae (Lp.coeFn_sub w w')]
    exact (Lp.memLp (w - w')).2.ne
  exact ENNReal.toReal_mono hfin (eLpNorm_mono_measure F hle)

/-- Continuity of further restriction. -/
private theorem furtherRestrict_continuous (R k : ℝ) (h : R ≤ k) :
    Continuous (furtherRestrict R k h) := by
  refine Metric.continuous_iff.2 fun w ε hε => ⟨ε, hε, fun w' hw' => ?_⟩
  calc dist (furtherRestrict R k h w') (furtherRestrict R k h w)
      ≤ dist w' w := furtherRestrict_dist_le R k h w' w
    _ < ε := hw'

/-- Composition: further-restricting a ball-`k` restriction gives the ball-`R` restriction. -/
private theorem furtherRestrict_restrictToBall (R k : ℝ) (h : R ≤ k) (w : L2VF_R3) :
    furtherRestrict R k h (restrictToBall k w) = restrictToBall R w := by
  apply Lp.ext
  have h1 := furtherRestrict_coeFn R k h (restrictToBall k w)
  have hsub : Metric.closedBall (0 : Domain3) R ⊆ Metric.closedBall (0 : Domain3) k :=
    Metric.closedBall_subset_closedBall h
  have hk : ⇑(restrictToBall k w) =ᵐ[volume.restrict (Metric.closedBall (0 : Domain3) k)]
      (w : Domain3 → EuclideanSpace ℝ (Fin 3)) := MemLp.coeFn_toLp _
  have hkR : ⇑(restrictToBall k w) =ᵐ[volume.restrict (Metric.closedBall (0 : Domain3) R)]
      (w : Domain3 → EuclideanSpace ℝ (Fin 3)) :=
    ae_mono (Measure.restrict_mono hsub le_rfl) hk
  have hRw : ⇑(restrictToBall R w) =ᵐ[volume.restrict (Metric.closedBall (0 : Domain3) R)]
      (w : Domain3 → EuclideanSpace ℝ (Fin 3)) := MemLp.coeFn_toLp _
  filter_upwards [h1, hkR, hRw] with x hx hxk hxR
  rw [hx, hxk, ← hxR]

/-- Restriction to a ball does not increase the L²-norm. -/
theorem norm_restrictToBall_le (R : ℝ) (w : L2VF_R3) :
    ‖restrictToBall R w‖ ≤ ‖w‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  have hle : volume.restrict (Metric.closedBall (0 : Domain3) R) ≤ (volume : Measure Domain3) :=
    Measure.restrict_le_self
  have hcong : ⇑(restrictToBall R w)
      =ᵐ[volume.restrict (Metric.closedBall (0 : Domain3) R)]
        (w : Domain3 → EuclideanSpace ℝ (Fin 3)) := MemLp.coeFn_toLp _
  rw [eLpNorm_congr_ae hcong]
  exact ENNReal.toReal_mono (Lp.memLp w).2.ne (eLpNorm_mono_measure _ hle)

/-- `restrictToBall R` sends `0` to `0`. -/
theorem restrictToBall_zero (R : ℝ) : restrictToBall R (0 : L2VF_R3) = 0 := by
  apply Lp.ext
  have h1 : ⇑(restrictToBall R (0 : L2VF_R3))
      =ᵐ[volume.restrict (Metric.closedBall (0 : Domain3) R)]
        ((0 : L2VF_R3) : Domain3 → EuclideanSpace ℝ (Fin 3)) := MemLp.coeFn_toLp _
  have h0 : ((0 : L2VF_R3) : Domain3 → EuclideanSpace ℝ (Fin 3))
      =ᵐ[volume.restrict (Metric.closedBall (0 : Domain3) R)] (0 : Domain3 → _) :=
    (Lp.coeFn_zero (E := EuclideanSpace ℝ (Fin 3)) (p := 2) (μ := volume)).restrict
  have hz0 : ⇑(0 : L2ballR3 R)
      =ᵐ[volume.restrict (Metric.closedBall (0 : Domain3) R)] (0 : Domain3 → _) :=
    Lp.coeFn_zero (E := EuclideanSpace ℝ (Fin 3)) (p := 2)
      (μ := volume.restrict (Metric.closedBall (0 : Domain3) R))
  filter_upwards [h1, h0, hz0] with x hx hx0 hxz
  simp only [hx, hx0, hxz, Pi.zero_apply]

/-- `restrictToBall R (u - v) = restrictToBall R u - restrictToBall R v`. -/
theorem restrictToBall_sub (R : ℝ) (u v : L2VF_R3) :
    restrictToBall R (u - v) = restrictToBall R u - restrictToBall R v := by
  apply Lp.ext
  filter_upwards [
    MemLp.coeFn_toLp ((Lp.memLp (u - v)).restrict (Metric.closedBall (0 : Domain3) R)),
    MemLp.coeFn_toLp ((Lp.memLp u).restrict (Metric.closedBall (0 : Domain3) R)),
    MemLp.coeFn_toLp ((Lp.memLp v).restrict (Metric.closedBall (0 : Domain3) R)),
    Lp.coeFn_sub (restrictToBall R u) (restrictToBall R v),
    ae_mono Measure.restrict_le_self (Lp.coeFn_sub u v)] with x h1 h2 h3 h4 h5
  -- Bridge definitional equality: restrictToBall R w = MemLp.toLp ↑↑w ... by def
  have eq1 : (↑↑(restrictToBall R (u - v)) : Domain3 → EuclideanSpace ℝ (Fin 3)) x =
      (↑↑(u - v) : Domain3 → EuclideanSpace ℝ (Fin 3)) x := h1
  have eq2 : (↑↑(restrictToBall R u) : Domain3 → EuclideanSpace ℝ (Fin 3)) x =
      (↑↑u : Domain3 → EuclideanSpace ℝ (Fin 3)) x := h2
  have eq3 : (↑↑(restrictToBall R v) : Domain3 → EuclideanSpace ℝ (Fin 3)) x =
      (↑↑v : Domain3 → EuclideanSpace ℝ (Fin 3)) x := h3
  rw [eq1, h5]
  simp only [h4, Pi.sub_apply, eq2, eq3]

/-- `restrictToBall R` is `1`-Lipschitz on `L2VF_R3`. Used to obtain continuity, hence
time-measurability transport. -/
theorem restrictToBall_dist_le (R : ℝ) (u v : L2VF_R3) :
    dist (restrictToBall R u) (restrictToBall R v) ≤ dist u v := by
  rw [dist_eq_norm, dist_eq_norm, Lp.norm_def, Lp.norm_def]
  have hle : volume.restrict (Metric.closedBall (0 : Domain3) R) ≤ (volume : Measure Domain3) :=
    Measure.restrict_le_self
  -- The underlying function of `restrictToBall R u - restrictToBall R v` agrees a.e. (on `B_R`)
  -- with `u - v`'s underlying function.
  have hcongR : ⇑(restrictToBall R u - restrictToBall R v)
      =ᵐ[volume.restrict (Metric.closedBall (0 : Domain3) R)]
        (fun x => (u x : EuclideanSpace ℝ (Fin 3)) - (v x : EuclideanSpace ℝ (Fin 3))) := by
    have hsub := Lp.coeFn_sub (restrictToBall R u) (restrictToBall R v)
    have hu : ⇑(restrictToBall R u)
        =ᵐ[volume.restrict (Metric.closedBall (0 : Domain3) R)]
          (u : Domain3 → EuclideanSpace ℝ (Fin 3)) := MemLp.coeFn_toLp _
    have hv : ⇑(restrictToBall R v)
        =ᵐ[volume.restrict (Metric.closedBall (0 : Domain3) R)]
          (v : Domain3 → EuclideanSpace ℝ (Fin 3)) := MemLp.coeFn_toLp _
    filter_upwards [hsub, hu, hv] with x hx hxu hxv
    simp only [hx, Pi.sub_apply, hxu, hxv]
  have hcongG : ⇑(u - v)
      =ᵐ[(volume : Measure Domain3)]
        (fun x => (u x : EuclideanSpace ℝ (Fin 3)) - (v x : EuclideanSpace ℝ (Fin 3))) :=
    Lp.coeFn_sub u v
  rw [eLpNorm_congr_ae hcongR, eLpNorm_congr_ae hcongG]
  refine ENNReal.toReal_mono ?_ (eLpNorm_mono_measure _ hle)
  rw [← eLpNorm_congr_ae hcongG]
  exact (Lp.memLp (u - v)).2.ne

/-- Continuity of `restrictToBall R : L2VF_R3 → L2ballR3 R` (it is `1`-Lipschitz). -/
theorem continuous_restrictToBall (R : ℝ) :
    Continuous (fun w : L2VF_R3 => restrictToBall R w) := by
  refine Metric.continuous_iff.2 fun w ε hε => ⟨ε, hε, fun w' hw' => ?_⟩
  calc dist (restrictToBall R w') (restrictToBall R w)
      ≤ dist w' w := restrictToBall_dist_le R w' w
    _ < ε := hw'

/-- The squared L²(B_R)-norm of `restrictToBall R w` equals the ball set-integral of `‖w·‖²`. -/
theorem normSq_restrictToBall_eq_setIntegral (R : ℝ) (w : L2VF_R3) :
    ‖restrictToBall R w‖ ^ 2
      = ∫ x in Metric.closedBall (0 : Domain3) R,
          ‖(w x : EuclideanSpace ℝ (Fin 3))‖ ^ 2 ∂(volume : Measure Domain3) := by
  -- Use the bridge with `v = 0`: `restrictToBall R 0 = 0`, so the ball integral of `‖w - 0‖²`
  -- equals `dist (restrictToBall R w) 0 ^ 2 = ‖restrictToBall R w‖²`.
  have hbridge := setIntegral_normSq_eq_dist_sq_restrictToBall R w 0
  rw [restrictToBall_zero, dist_zero_right] at hbridge
  -- Rewrite the integrand: `w x - (0 : L2VF_R3) x = w x` a.e.
  rw [← hbridge]
  refine setIntegral_congr_ae measurableSet_closedBall ?_
  have h0 : ((0 : L2VF_R3) : Domain3 → EuclideanSpace ℝ (Fin 3)) =ᵐ[volume] (0 : Domain3 → _) :=
    Lp.coeFn_zero (E := EuclideanSpace ℝ (Fin 3)) (p := 2) (μ := volume)
  filter_upwards [h0] with x hx _
  rw [hx]; simp

/-- **Ball exhaustion of the L²(ℝ³) norm.** The squared L²(B_k)-norm of `restrictToBall k w`
increases to `‖w‖²` as the integer radius `k → ∞` (the balls exhaust `ℝ³`). -/
theorem tendsto_normSq_restrictToBall (w : L2VF_R3) :
    Tendsto (fun k : ℕ => ‖restrictToBall (k : ℝ) w‖ ^ 2) atTop (𝓝 (‖w‖ ^ 2)) := by
  -- The integrand `x ↦ ‖w x‖²`.
  set F : Domain3 → ℝ := fun x => ‖(w x : EuclideanSpace ℝ (Fin 3))‖ ^ 2 with hF
  -- Integrability of `F` over `ℝ³`: `‖w‖² = ∫ F`, and `F` is the pointwise square norm of an L²
  -- function, hence integrable (`MemLp.integrable_norm_rpow`-style; here directly via `L2`).
  have hInt : Integrable F (volume : Measure Domain3) := by
    have hmem : MemLp (w : Domain3 → EuclideanSpace ℝ (Fin 3)) 2 volume := Lp.memLp w
    have hr := hmem.integrable_norm_rpow (by norm_num) (by norm_num)
    refine hr.congr ?_
    filter_upwards with x
    simp only [hF, show (2 : ENNReal).toReal = (2 : ℝ) by norm_num, Real.rpow_two]
  -- Each ball term is the set-integral of `F`.
  have hterm : ∀ k : ℕ, ‖restrictToBall (k : ℝ) w‖ ^ 2
      = ∫ x in Metric.closedBall (0 : Domain3) (k : ℝ), F x ∂volume :=
    fun k => normSq_restrictToBall_eq_setIntegral (k : ℝ) w
  -- The full norm is `∫ F`.
  have hfull : ‖w‖ ^ 2 = ∫ x, F x ∂volume := by
    have := normSq_eq_integral_normSq (μ := (volume : Measure Domain3)) w
    simpa [hF] using this
  -- Monotone ball exhaustion of the set-integral.
  have hcov : (⋃ k : ℕ, Metric.closedBall (0 : Domain3) (k : ℝ)) = Set.univ :=
    Metric.iUnion_closedBall_nat 0
  have hmono : Monotone (fun k : ℕ => Metric.closedBall (0 : Domain3) (k : ℝ)) :=
    fun a b hab => Metric.closedBall_subset_closedBall (by exact_mod_cast hab)
  have hIntOn : IntegrableOn F (⋃ k : ℕ, Metric.closedBall (0 : Domain3) (k : ℝ)) volume := by
    rw [hcov, integrableOn_univ]; exact hInt
  have htends :=
    tendsto_setIntegral_of_monotone
      (fun k => measurableSet_closedBall) hmono hIntOn
  rw [hcov] at htends
  simp only [Measure.restrict_univ] at htends
  rw [hfull]
  simpa only [hterm] using htends

/-- If a global L² function `g` agrees a.e. (on `B_k`) with a ball-`k` limit `gk`, and the
ball-`k` restrictions of a sequence converge to `gk`, then for every real `R ≤ k` the
ball-`R` restrictions converge to `restrictToBall R g`. -/
private theorem tendsto_restrictToBall_of_ballLimit
    (z : ℕ → L2VF_R3) (g : L2VF_R3) (R k : ℝ) (hRk : R ≤ k)
    (gk : L2ballR3 k)
    (hgk_ae : (gk : Domain3 → EuclideanSpace ℝ (Fin 3))
      =ᵐ[volume.restrict (Metric.closedBall (0 : Domain3) k)]
        (g : Domain3 → EuclideanSpace ℝ (Fin 3)))
    (htk : Tendsto (fun n => restrictToBall k (z n)) atTop (𝓝 gk)) :
    Tendsto (fun n => restrictToBall R (z n)) atTop (𝓝 (restrictToBall R g)) := by
  -- `furtherRestrict R k` is continuous, so it preserves the limit.
  have hcont := (furtherRestrict_continuous R k hRk).tendsto gk
  have hcomp := hcont.comp htk
  simp only [Function.comp_def] at hcomp
  -- The composed sequence is exactly `restrictToBall R (z n)`.
  have hseq : (fun n => furtherRestrict R k hRk (restrictToBall k (z n)))
      = fun n => restrictToBall R (z n) :=
    funext fun n => furtherRestrict_restrictToBall R k hRk (z n)
  -- And `furtherRestrict R k gk = restrictToBall R g`.
  have hlim : furtherRestrict R k hRk gk = restrictToBall R g := by
    apply Lp.ext
    have h1 := furtherRestrict_coeFn R k hRk gk
    have hsub : Metric.closedBall (0 : Domain3) R ⊆ Metric.closedBall (0 : Domain3) k :=
      Metric.closedBall_subset_closedBall hRk
    have hmono := Measure.restrict_mono hsub (le_refl (volume : Measure Domain3))
    have hgkR : (gk : Domain3 → EuclideanSpace ℝ (Fin 3))
        =ᵐ[volume.restrict (Metric.closedBall (0 : Domain3) R)]
          (g : Domain3 → EuclideanSpace ℝ (Fin 3)) := ae_mono hmono hgk_ae
    have hRg : ⇑(restrictToBall R g)
        =ᵐ[volume.restrict (Metric.closedBall (0 : Domain3) R)]
          (g : Domain3 → EuclideanSpace ℝ (Fin 3)) := MemLp.coeFn_toLp _
    filter_upwards [h1, hgkR, hRg] with x hx hxgk hxg
    rw [hx, hxgk, ← hxg]
  rw [hseq] at hcomp
  rw [hlim] at hcomp
  exact hcomp

/-- **Ball exhaustion for the Lebesgue integral.** The set-lintegral of a function over the
closed ball `B_k` increases to the full-space lintegral as `k → ∞`, because the balls
exhaust `ℝ³`. -/
private theorem tendsto_setLIntegral_closedBall (f : Domain3 → ENNReal) (hf : Measurable f) :
    Tendsto (fun k : ℕ => ∫⁻ x in Metric.closedBall (0 : Domain3) (k : ℝ), f x ∂volume)
      atTop (𝓝 (∫⁻ x, f x ∂volume)) := by
  have hcov : ⋃ k : ℕ, Metric.closedBall (0 : Domain3) (k : ℝ) = Set.univ :=
    Metric.iUnion_closedBall_nat 0
  have hmeas : ∀ k : ℕ, MeasurableSet (Metric.closedBall (0 : Domain3) (k : ℝ)) :=
    fun k => measurableSet_closedBall
  -- rewrite each set-lintegral as a full lintegral of an indicator
  have hrw : ∀ k : ℕ, (∫⁻ x in Metric.closedBall (0 : Domain3) (k : ℝ), f x ∂volume)
      = ∫⁻ x, (Metric.closedBall (0 : Domain3) (k : ℝ)).indicator f x ∂volume := fun k =>
    (lintegral_indicator (hmeas k) f).symm
  simp only [hrw]
  -- and the full lintegral as the indicator of `univ`
  have hfull : (∫⁻ x, f x ∂volume)
      = ∫⁻ x, (fun x => ⨆ k : ℕ, (Metric.closedBall (0 : Domain3) (k : ℝ)).indicator f x) x
        ∂volume := by
    refine lintegral_congr fun x => ?_
    have hx : x ∈ ⋃ k : ℕ, Metric.closedBall (0 : Domain3) (k : ℝ) := by
      rw [hcov]; trivial
    obtain ⟨k₀, hk₀⟩ := Set.mem_iUnion.mp hx
    refine le_antisymm ?_ ?_
    · refine le_iSup_of_le k₀ ?_
      rw [Set.indicator_of_mem hk₀]
    · refine iSup_le fun k => ?_
      exact Set.indicator_le_self _ f x
  rw [hfull]
  refine lintegral_tendsto_of_tendsto_of_monotone
    (fun k => ((hf.indicator (hmeas k)).aemeasurable)) ?_ ?_
  · refine Filter.Eventually.of_forall fun x a b hab => ?_
    have hsub : Metric.closedBall (0 : Domain3) (a : ℝ)
        ⊆ Metric.closedBall (0 : Domain3) (b : ℝ) :=
      Metric.closedBall_subset_closedBall (by exact_mod_cast hab)
    show (Metric.closedBall (0 : Domain3) (a : ℝ)).indicator f x
      ≤ (Metric.closedBall (0 : Domain3) (b : ℝ)).indicator f x
    by_cases ha : x ∈ Metric.closedBall (0 : Domain3) (a : ℝ)
    · rw [Set.indicator_of_mem ha, Set.indicator_of_mem (hsub ha)]
    · rw [Set.indicator_of_notMem ha]; exact bot_le
  · refine Filter.Eventually.of_forall fun x => ?_
    have hx : x ∈ ⋃ k : ℕ, Metric.closedBall (0 : Domain3) (k : ℝ) := by
      rw [hcov]; trivial
    obtain ⟨k₀, hk₀⟩ := Set.mem_iUnion.mp hx
    -- eventually the indicator equals `f x`, so the sequence converges to the sup `f x`
    have hval : ⨆ k : ℕ, (Metric.closedBall (0 : Domain3) (k : ℝ)).indicator f x = f x := by
      refine le_antisymm (iSup_le fun k => Set.indicator_le_self _ f x) ?_
      exact le_iSup_of_le k₀ (by rw [Set.indicator_of_mem hk₀])
    rw [hval]
    refine tendsto_atTop_of_eventually_const (i₀ := k₀) fun k hk => ?_
    have hmem : x ∈ Metric.closedBall (0 : Domain3) (k : ℝ) :=
      Metric.closedBall_subset_closedBall (by exact_mod_cast hk) hk₀
    rw [Set.indicator_of_mem hmem]

/-- **D3a.** The per-ball limits from D2 are mutually consistent: the limit on B_k agrees
a.e. on B_j (j ≤ k) with the limit on B_j (both are L² limits of the same subsequence's
restrictions, and restriction B_k → B_j is continuous). Used to assemble a single global g. -/
theorem ballLimits_are_consistent (B : LocalRellichInput) (M : ℝ)
    (z : ℕ → L2VF_R3)
    (hmem : ∀ n, z n ∈ L2Sigma_R3) (hH1 : ∀ n, memH1VF_R3 (z n))
    (hbd : ∀ n, ‖z n‖ ≤ M) (hvf : ∀ n, viscousFormSq_R3 1 (z n) ≤ M ^ 2)
    (ψ : ℕ → ℕ) (hψ : StrictMono ψ)
    (g : ∀ k : ℕ, L2ballR3 (k : ℝ))
    (hg : ∀ k : ℕ, Tendsto (fun n => restrictToBall (k : ℝ) (z (ψ n))) atTop (𝓝 (g k))) :
    ∃ g₀ : Domain3 → EuclideanSpace ℝ (Fin 3), MemLp g₀ 2 (volume : Measure Domain3) ∧
      ∀ k : ℕ, (g k : Domain3 → EuclideanSpace ℝ (Fin 3))
        =ᵐ[volume.restrict (Metric.closedBall (0 : Domain3) (k : ℝ))] g₀ := by
  classical
  -- Abbreviation for the ball and its restricted measure.
  set ball : ℕ → Set Domain3 := fun k => Metric.closedBall (0 : Domain3) (k : ℝ) with hball
  -- (A) Uniform L²-norm bound on each ball-limit: `‖g k‖ ≤ M`.
  have hMnonneg : 0 ≤ M := le_trans (norm_nonneg _) (hbd 0)
  have hnorm_le : ∀ k : ℕ, ‖g k‖ ≤ M := by
    intro k
    have hbound_seq : ∀ n, ‖restrictToBall (k : ℝ) (z (ψ n))‖ ≤ M := fun n =>
      le_trans (norm_restrictToBall_le (k : ℝ) (z (ψ n))) (hbd (ψ n))
    have hnt : Tendsto (fun n => ‖restrictToBall (k : ℝ) (z (ψ n))‖) atTop (𝓝 ‖g k‖) :=
      (continuous_norm.tendsto (g k)).comp (hg k)
    exact le_of_tendsto' hnt hbound_seq
  -- (B) Consistency: for `j ≤ k`, the further-restriction of `g k` equals `g j`.
  have hcons_fr : ∀ (j k : ℕ) (hjk : (j : ℝ) ≤ (k : ℝ)),
      furtherRestrict (j : ℝ) (k : ℝ) hjk (g k) = g j := by
    intro j k hjk
    -- `furtherRestrict j k` is continuous and maps the `B_k` limit to a `B_j` limit.
    have hcont := (furtherRestrict_continuous (j : ℝ) (k : ℝ) hjk).tendsto (g k)
    have hcomp := hcont.comp (hg k)
    simp only [Function.comp_def] at hcomp
    have hseq : (fun n => furtherRestrict (j : ℝ) (k : ℝ) hjk
        (restrictToBall (k : ℝ) (z (ψ n))))
        = fun n => restrictToBall (j : ℝ) (z (ψ n)) :=
      funext fun n => furtherRestrict_restrictToBall (j : ℝ) (k : ℝ) hjk (z (ψ n))
    rw [hseq] at hcomp
    exact tendsto_nhds_unique hcomp (hg j)
  -- (C) Consistency at the a.e.-function level: `g j =ᵐ g k` on `B_j` for `j ≤ k`.
  have hcons_ae : ∀ (j k : ℕ), j ≤ k →
      (g j : Domain3 → EuclideanSpace ℝ (Fin 3))
        =ᵐ[volume.restrict (ball j)] (g k : Domain3 → EuclideanSpace ℝ (Fin 3)) := by
    intro j k hjk
    have hjkR : (j : ℝ) ≤ (k : ℝ) := by exact_mod_cast hjk
    have heq := hcons_fr j k hjkR
    have hfr_coe := furtherRestrict_coeFn (j : ℝ) (k : ℝ) hjkR (g k)
    -- `g j = furtherRestrict j k (g k)` as Lp elements, so a.e. equal; combine with coeFn.
    have hgj : (g j : Domain3 → EuclideanSpace ℝ (Fin 3))
        =ᵐ[volume.restrict (ball j)]
          (furtherRestrict (j : ℝ) (k : ℝ) hjkR (g k) : Domain3 → EuclideanSpace ℝ (Fin 3)) := by
      rw [heq]
    filter_upwards [hgj, hfr_coe] with x hx hfx
    rw [hx, hfx]
  -- (D) The global index function `c x = ⌈dist x 0⌉₊` and the induced partition into annuli.
  set c : Domain3 → ℕ := fun x => ⌈dist x (0 : Domain3)⌉₊ with hc
  -- `x ∈ B_k ↔ c x ≤ k`.
  have hmem_ball_iff : ∀ (x : Domain3) (k : ℕ), x ∈ ball k ↔ c x ≤ k := by
    intro x k
    simp only [hball, hc, Metric.mem_closedBall, Nat.ceil_le]
  -- measurability of `c`: preimages of points are measurable annuli.
  have hcmeas : Measurable c := by
    refine measurable_to_countable' fun k => ?_
    -- `{c = k} = {c ≤ k} \ {c ≤ k-1}` (with `{c ≤ k} = B_k`), both measurable.
    have hset : (c ⁻¹' {k}) = ball k \ (⋃ j ∈ Finset.range k, ball j) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_diff, Set.mem_iUnion,
        Finset.mem_range, not_exists, hmem_ball_iff]
      constructor
      · rintro rfl
        exact ⟨le_rfl, fun j hj => by omega⟩
      · rintro ⟨hck, hlt⟩
        by_contra hne
        have hlt' : c x < k := lt_of_le_of_ne hck hne
        exact hlt (c x) hlt' le_rfl
    rw [hset]
    exact (measurableSet_closedBall).diff
      (MeasurableSet.biUnion (Finset.range k).countable_toSet
        (fun j _ => measurableSet_closedBall))
  -- The global a.e. function: pick the ball-limit indexed by `c x = ⌈‖x‖⌉₊`.
  set g₀ : Domain3 → EuclideanSpace ℝ (Fin 3) :=
    fun x => (g (c x) : Domain3 → EuclideanSpace ℝ (Fin 3)) x with hg₀def
  -- (E) `g₀ =ᵐ g k` on `B_k`: decompose `B_k` into the finitely many slices `{c = j}` (j ≤ k);
  -- on each slice `g₀ = g j =ᵐ g k` by consistency.
  have hagree : ∀ k : ℕ, (g k : Domain3 → EuclideanSpace ℝ (Fin 3))
      =ᵐ[volume.restrict (ball k)] g₀ := by
    intro k
    -- It suffices to show the symmetric difference is null; we prove a.e. agreement by slicing.
    -- For each `j ≤ k`, the consistency `g j =ᵐ g k` holds on `B_j ⊇ {c = j}`.
    -- Restrict each consistency to the slice and combine over `j = 0 … k`.
    have hslice : ∀ j : ℕ, j ≤ k →
        (g₀) =ᵐ[volume.restrict (ball k ∩ {x | c x = j})]
          (g k : Domain3 → EuclideanSpace ℝ (Fin 3)) := by
      intro j hjk
      -- on `{c = j}`, `g₀ x = g j x`.
      have hslice_sub : (ball k ∩ {x | c x = j}) ⊆ ball j := by
        intro x hx
        rw [hmem_ball_iff]; exact le_of_eq hx.2
      have hmono : volume.restrict (ball k ∩ {x | c x = j}) ≤ volume.restrict (ball j) :=
        Measure.restrict_mono hslice_sub le_rfl
      -- `g j =ᵐ g k` on the slice (from consistency on `B_j`).
      have hjk_ae : (g j : Domain3 → EuclideanSpace ℝ (Fin 3))
          =ᵐ[volume.restrict (ball k ∩ {x | c x = j})]
            (g k : Domain3 → EuclideanSpace ℝ (Fin 3)) := ae_mono hmono (hcons_ae j k hjk)
      -- `g₀ x = g j x` on `{c = j}`.
      have hg0j : (g₀) =ᵐ[volume.restrict (ball k ∩ {x | c x = j})]
          (g j : Domain3 → EuclideanSpace ℝ (Fin 3)) := by
        refine ae_restrict_of_forall_mem (by
          exact (measurableSet_closedBall).inter (hcmeas (measurableSet_singleton j))) ?_
        intro x hx
        simp only [hg₀def]
        rw [hx.2]
      exact hg0j.trans hjk_ae
    -- Combine the slices: `B_k = ⋃_{j ≤ k} (B_k ∩ {c = j})`.
    have hcover : ball k = ⋃ j ∈ Finset.range (k + 1), (ball k ∩ {x | c x = j}) := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq, Finset.mem_range]
      constructor
      · intro hx
        exact ⟨c x, by have := (hmem_ball_iff x k).1 hx; omega, hx, rfl⟩
      · rintro ⟨j, _, hx, _⟩; exact hx
    -- a.e. agreement on a finite union from a.e. agreement on each piece.
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_closedBall]
    have hpieces : ∀ j ∈ Finset.range (k + 1),
        ∀ᵐ x ∂volume, x ∈ (ball k ∩ {x | c x = j}) →
          (g k : Domain3 → EuclideanSpace ℝ (Fin 3)) x = g₀ x := by
      intro j hj
      have hmeasj : MeasurableSet (ball k ∩ {x | c x = j}) :=
        (measurableSet_closedBall).inter (hcmeas (measurableSet_singleton j))
      have := (hslice j (by simp only [Finset.mem_range] at hj; omega)).symm
      rw [Filter.EventuallyEq, ae_restrict_iff' hmeasj] at this
      exact this
    have hall := (ae_ball_iff (Finset.range (k + 1)).countable_toSet).2
      (fun j hj => hpieces j hj)
    filter_upwards [hall] with x hx hxk
    have hxmem : x ∈ ⋃ j ∈ Finset.range (k + 1), (ball k ∩ {x | c x = j}) := by
      rw [← hcover]; exact hxk
    rw [Set.mem_iUnion₂] at hxmem
    obtain ⟨j, hj, hxj⟩ := hxmem
    exact hx j hj hxj
  -- AEStronglyMeasurable of `g₀` as the everywhere-pointwise limit of finite indicator sums.
  have hg₀_meas : AEStronglyMeasurable g₀ (volume : Measure Domain3) := by
    -- `h N x := g (min (c x) N) x`; finite sum of slice-indicators, AESM; `h N → g₀` pointwise.
    set h : ℕ → Domain3 → EuclideanSpace ℝ (Fin 3) :=
      fun N x => (g (min (c x) N) : Domain3 → EuclideanSpace ℝ (Fin 3)) x with hhdef
    have hh_meas : ∀ N, AEStronglyMeasurable (h N) (volume : Measure Domain3) := by
      intro N
      -- `h N = ∑_{j=0}^{N} {x | min (c x) N = j}.indicator (g j)`.
      have heq : h N = fun x => ∑ j ∈ Finset.range (N + 1),
          {y : Domain3 | min (c y) N = j}.indicator
            (fun y => (g j : Domain3 → EuclideanSpace ℝ (Fin 3)) y) x := by
        funext x
        rw [Finset.sum_eq_single (min (c x) N)]
        · rw [Set.indicator_of_mem (by simp)]
        · intro j _ hj
          rw [Set.indicator_of_notMem (by simp only [Set.mem_setOf_eq]; exact fun h => hj h.symm)]
        · intro hmem
          exact absurd (Finset.mem_range.2 (Nat.lt_succ_of_le (min_le_right _ _))) hmem
      rw [heq]
      refine Finset.aestronglyMeasurable_fun_sum _ (fun j _ => ?_)
      refine AEStronglyMeasurable.indicator
        ((Lp.stronglyMeasurable (g j)).aestronglyMeasurable) ?_
      exact (hcmeas.min measurable_const) (measurableSet_singleton j)
    refine aestronglyMeasurable_of_tendsto_ae atTop hh_meas ?_
    refine Filter.Eventually.of_forall fun x => ?_
    -- For `N ≥ c x`, `h N x = g (c x) x = g₀ x`.
    refine tendsto_atTop_of_eventually_const (i₀ := c x) fun N hN => ?_
    show (g (min (c x) N) : Domain3 → EuclideanSpace ℝ (Fin 3)) x
      = (g (c x) : Domain3 → EuclideanSpace ℝ (Fin 3)) x
    rw [min_eq_left hN]
  -- (F) MemLp of `g₀`: `∫⁻ ‖g₀‖ₑ² = lim_k ∫⁻_{B_k} ‖g₀‖ₑ² ≤ M²`, via ball exhaustion.
  refine ⟨g₀, ⟨hg₀_meas, ?_⟩, hagree⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)]
  -- The integrand exponent `p2 = (2 : ENNReal).toReal = 2`.
  set p2 : ℝ := (2 : ENNReal).toReal with hp2
  have hp2_eq : p2 = 2 := by simp [hp2]
  set F : Domain3 → ENNReal := fun x => ‖g₀ x‖ₑ ^ p2 with hF
  -- `F` is measurable (g₀ is AESM ⇒ enorm is AEMeasurable; promote to a measurable version
  -- and use the a.e.-equality; but the exhaustion lemma needs a measurable representative).
  obtain ⟨g₀', hg₀'_meas, hg₀'_ae⟩ := hg₀_meas
  set F' : Domain3 → ENNReal := fun x => ‖g₀' x‖ₑ ^ p2 with hF'
  have hF'_meas : Measurable F' := (hg₀'_meas.enorm).pow_const _
  have hFF' : F =ᵐ[volume] F' := by
    filter_upwards [hg₀'_ae] with x hx; simp only [hF, hF', hx]
  -- Each ball-lintegral of `F` is `≤ M²`.
  have hball_bd : ∀ k : ℕ,
      (∫⁻ x in ball k, F' x ∂volume) ≤ ENNReal.ofReal (M ^ 2) := by
    intro k
    -- replace `F'` by `F` (a.e.) then by `‖g k‖ₑ²` (a.e. on `B_k`).
    have h1 : (∫⁻ x in ball k, F' x ∂volume) = ∫⁻ x in ball k, F x ∂volume :=
      lintegral_congr_ae (ae_restrict_of_ae hFF'.symm)
    rw [h1]
    have h2 : (∫⁻ x in ball k, F x ∂volume)
        = ∫⁻ x in ball k, ‖(g k : Domain3 → EuclideanSpace ℝ (Fin 3)) x‖ₑ ^ p2 ∂volume := by
      refine lintegral_congr_ae ?_
      filter_upwards [(hagree k).symm] with x hx
      simp only [hF, hx]
    rw [h2]
    -- The set-lintegral over `B_k` is the lintegral over the restricted measure.
    have hset_eq : (∫⁻ x in ball k, ‖(g k : Domain3 → EuclideanSpace ℝ (Fin 3)) x‖ₑ ^ p2
          ∂volume)
        = ∫⁻ x, ‖(g k : Domain3 → EuclideanSpace ℝ (Fin 3)) x‖ₑ ^ p2
          ∂(volume.restrict (ball k)) := rfl
    rw [hset_eq]
    -- this equals `(eLpNorm (g k) 2 (restrict B_k))^p2`.
    have h3 : (∫⁻ x, ‖(g k : Domain3 → EuclideanSpace ℝ (Fin 3)) x‖ₑ ^ p2
          ∂(volume.restrict (ball k)))
        = eLpNorm (g k : Domain3 → EuclideanSpace ℝ (Fin 3)) 2
            (volume.restrict (ball k)) ^ p2 := by
      rw [eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num), ← hp2,
        ← ENNReal.rpow_mul]
      rw [show (1 / p2 * p2) = 1 by rw [hp2_eq]; norm_num, ENNReal.rpow_one]
    rw [h3]
    -- `eLpNorm (g k) 2 (restrict B_k) = ‖g k‖ ≤ M`.
    have h4 : eLpNorm (g k : Domain3 → EuclideanSpace ℝ (Fin 3)) 2
        (volume.restrict (ball k)) = ENNReal.ofReal ‖g k‖ := by
      rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top (g k))]
    rw [h4, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by rw [hp2_eq]; norm_num)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hgkM := hnorm_le k
    have : ‖g k‖ ^ p2 = ‖g k‖ ^ (2 : ℕ) := by
      rw [hp2_eq]; rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    rw [this]
    nlinarith [norm_nonneg (g k)]
  -- The full lintegral of `F'` is the limit of the ball-lintegrals (exhaustion), hence `≤ M²`.
  have hlim := tendsto_setLIntegral_closedBall F' hF'_meas
  have hfull_le : (∫⁻ x, F' x ∂volume) ≤ ENNReal.ofReal (M ^ 2) :=
    le_of_tendsto' hlim (fun k => hball_bd k)
  have hF_full : (∫⁻ x, F x ∂volume) = ∫⁻ x, F' x ∂volume := lintegral_congr_ae hFF'
  show (∫⁻ a, F a ∂volume) < ⊤
  rw [hF_full]
  exact lt_of_le_of_lt hfull_le ENNReal.ofReal_lt_top

/-! ### G5 helper lemmas — global div-free closure from local L² convergence

The `divTestFunctional φ w = ∑ j, ⟪(∂_j φ).toLp, projComponent_j w⟫_{L²(ℝ³)}` is a GLOBAL
L² inner product, but ball-restriction convergence is only LOCAL.  We close the gap with an
ε/3 ball-truncation, packaging `divTestFunctional φ` as a single global L²-vector inner
product `⟪gradVF φ, w⟫_{L2VF_R3}` against the gradient vector field `gradVF φ`. -/

/-- The **gradient vector field** of a Schwartz test `φ`, as an element of `L2VF_R3`:
`gradVF φ x = ∑ j, (∂_j φ)(x) • e_j = ∇φ(x)`.  Built by lifting each scalar component
`(∂_j φ).toLp` along `toSpanSingleton ℝ (e_j)`. -/
private noncomputable def gradVF (φ : SchwartzMap Domain3 ℝ) : L2VF_R3 :=
  ∑ j : Fin 3,
    (ContinuousLinearMap.toSpanSingleton ℝ
        (EuclideanSpace.single j (1 : ℝ) : EuclideanSpace ℝ (Fin 3))).compLp
      ((LineDeriv.lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
          (EuclideanSpace.single j (1 : ℝ) : Domain3) φ).toLp
        2 (volume : Measure Domain3))

/-- The j-th scalar component `(∂_j φ).toLp` used throughout. -/
private noncomputable def dphiLp (φ : SchwartzMap Domain3 ℝ) (j : Fin 3) :
    Lp ℝ 2 (volume : Measure Domain3) :=
  (LineDeriv.lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
      (EuclideanSpace.single j (1 : ℝ) : Domain3) φ).toLp 2 (volume : Measure Domain3)

/-- The coercion of a finite sum of `Lp` elements is a.e. the pointwise finite sum. -/
private theorem Lp_coeFn_finsetSum {ι : Type*} {E : Type*}
    [NormedAddCommGroup E] {μ : Measure Domain3} {p : ENNReal}
    (s : Finset ι) (F : ι → Lp E p μ) :
    (⇑(∑ i ∈ s, F i) : Domain3 → E) =ᵐ[μ] fun x => ∑ i ∈ s, (F i x) := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty]
    filter_upwards [Lp.coeFn_zero (E := E) (p := p) (μ := μ)] with x hx
    rw [hx]; rfl
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    filter_upwards [Lp.coeFn_add (F a) (∑ i ∈ s, F i), ih] with x hx hix
    rw [hx]
    simp only [Pi.add_apply, hix, Finset.sum_insert ha]

/-- Pointwise (a.e.) value of `gradVF φ`: `gradVF φ x = ∑ j, (∂_j φ)(x) • e_j`. -/
private theorem gradVF_coeFn (φ : SchwartzMap Domain3 ℝ) :
    (gradVF φ : Domain3 → EuclideanSpace ℝ (Fin 3))
      =ᵐ[volume] fun x => ∑ j : Fin 3,
        (dphiLp φ j x) • (EuclideanSpace.single j (1 : ℝ) : EuclideanSpace ℝ (Fin 3)) := by
  classical
  -- `gradVF φ` is a finite sum of `compLp` lifts.
  have hsum := Lp_coeFn_finsetSum (Finset.univ : Finset (Fin 3))
    (fun j => (ContinuousLinearMap.toSpanSingleton ℝ
        (EuclideanSpace.single j (1 : ℝ) : EuclideanSpace ℝ (Fin 3))).compLp (dphiLp φ j))
  -- For each `j`, the j-th summand's coercion is a.e. `(dphiLp φ j x) • e_j`.
  have hcomp : ∀ j : Fin 3,
      (⇑((ContinuousLinearMap.toSpanSingleton ℝ
          (EuclideanSpace.single j (1 : ℝ) : EuclideanSpace ℝ (Fin 3))).compLp (dphiLp φ j)))
        =ᵐ[volume] fun x =>
          (dphiLp φ j x) • (EuclideanSpace.single j (1 : ℝ) : EuclideanSpace ℝ (Fin 3)) := by
    intro j
    filter_upwards [(ContinuousLinearMap.toSpanSingleton ℝ
        (EuclideanSpace.single j (1 : ℝ) : EuclideanSpace ℝ (Fin 3))).coeFn_compLp
        (dphiLp φ j)] with x hx
    rw [hx, ContinuousLinearMap.toSpanSingleton_apply]
  -- Combine: `gradVF φ = ∑ j (compLp …)` (defeq), then push the a.e. sum identity.
  have hgrad : (gradVF φ : Domain3 → EuclideanSpace ℝ (Fin 3))
      =ᵐ[volume] fun x => ∑ j : Fin 3,
        ((ContinuousLinearMap.toSpanSingleton ℝ
          (EuclideanSpace.single j (1 : ℝ) : EuclideanSpace ℝ (Fin 3))).compLp (dphiLp φ j)) x := by
    exact hsum
  refine hgrad.trans ?_
  -- now replace each summand pointwise via `hcomp`
  have hall := ae_all_iff.2 hcomp
  filter_upwards [hall] with x hx
  exact Finset.sum_congr rfl (fun j _ => hx j)

/-- Each scalar summand `⟪dphiLp φ j, projComp_j w⟫` equals the integral
`∫ x, (dphiLp φ j x) * (w x) j`. -/
private theorem dphi_inner_eq_integral (φ : SchwartzMap Domain3 ℝ) (j : Fin 3) (w : L2VF_R3) :
    (inner ℝ (dphiLp φ j) (L2VF_projComponent_R3 j w) : ℝ)
      = ∫ x, (dphiLp φ j x) * ((w x : EuclideanSpace ℝ (Fin 3)) j) ∂volume := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [(EuclideanSpace.proj (𝕜 := ℝ) j).coeFn_compLpL (p := 2)
    (μ := (volume : Measure Domain3)) w] with x hx
  -- real inner product of scalars is multiplication; and `projComp_j w x = (w x) j`.
  show (inner ℝ (dphiLp φ j x) ((L2VF_projComponent_R3 j w) x) : ℝ) = _
  rw [show ((L2VF_projComponent_R3 j w) x) = (EuclideanSpace.proj (𝕜 := ℝ) j) (w x) from hx]
  rw [RCLike.inner_apply', conj_trivial]
  rfl

/-- Integrability of each scalar summand `x ↦ (dphiLp φ j x) * (w x) j`. -/
private theorem dphi_integrable (φ : SchwartzMap Domain3 ℝ) (j : Fin 3) (w : L2VF_R3) :
    Integrable (fun x => (dphiLp φ j x) * ((w x : EuclideanSpace ℝ (Fin 3)) j)) volume := by
  have hint := MeasureTheory.L2.integrable_inner (𝕜 := ℝ)
    (dphiLp φ j) (L2VF_projComponent_R3 j w)
  refine hint.congr ?_
  filter_upwards [(EuclideanSpace.proj (𝕜 := ℝ) j).coeFn_compLpL (p := 2)
    (μ := (volume : Measure Domain3)) w] with x hx
  show (inner ℝ (dphiLp φ j x) ((L2VF_projComponent_R3 j w) x) : ℝ) = _
  rw [show ((L2VF_projComponent_R3 j w) x) = (EuclideanSpace.proj (𝕜 := ℝ) j) (w x) from hx]
  rw [RCLike.inner_apply', conj_trivial]
  rfl

/-- The weak-divergence functional is the global L²-vector inner product against `gradVF φ`. -/
private theorem divTestFunctional_eq_inner (φ : SchwartzMap Domain3 ℝ) (w : L2VF_R3) :
    divTestFunctional φ w = (inner ℝ (gradVF φ) w : ℝ) := by
  classical
  -- LHS: `divTestFunctional φ w = ∑ j, ⟪dphiLp φ j, projComp_j w⟫ = ∑ j, ∫ (dphiLp φ j)·(w·)_j`.
  have hLHS : divTestFunctional φ w
      = ∑ j : Fin 3, ∫ x, (dphiLp φ j x) * ((w x : EuclideanSpace ℝ (Fin 3)) j) ∂volume := by
    rw [divTestFunctional, ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [ContinuousLinearMap.comp_apply, innerSL_apply_apply]
    exact dphi_inner_eq_integral φ j w
  -- RHS: `⟪gradVF φ, w⟫ = ∫ ⟪gradVF φ x, w x⟫ = ∫ ∑ j (dphiLp φ j x)·(w x)_j`.
  have hRHS : (inner ℝ (gradVF φ) w : ℝ)
      = ∫ x, ∑ j : Fin 3, (dphiLp φ j x) * ((w x : EuclideanSpace ℝ (Fin 3)) j) ∂volume := by
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [gradVF_coeFn φ] with x hx
    rw [show (gradVF φ x) = ∑ j : Fin 3,
        (dphiLp φ j x) • (EuclideanSpace.single j (1 : ℝ) : EuclideanSpace ℝ (Fin 3)) from hx]
    rw [sum_inner]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [real_inner_smul_left, EuclideanSpace.inner_single_left, conj_trivial, one_mul]
  rw [hLHS, hRHS, integral_finset_sum]
  intro j _
  exact dphi_integrable φ j w

/-- L²(B_Rᶜ): the carrier for the tail part of the truncation. -/
private noncomputable abbrev L2tailR3 (R : ℝ) :=
  Lp (EuclideanSpace ℝ (Fin 3)) 2 (volume.restrict (Metric.closedBall (0 : Domain3) R)ᶜ)

/-- Restriction of an L²(ℝ³) field to the tail `B_Rᶜ`, as an element of `L2tailR3 R`. -/
noncomputable def tailVF (R : ℝ) (w : L2VF_R3) : L2tailR3 R :=
  MemLp.toLp (w : Domain3 → EuclideanSpace ℝ (Fin 3))
    ((Lp.memLp w).restrict (Metric.closedBall (0 : Domain3) R)ᶜ)

/-- The tail restriction does not increase the L²-norm. -/
theorem norm_tailVF_le (R : ℝ) (w : L2VF_R3) : ‖tailVF R w‖ ≤ ‖w‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  have hle : volume.restrict (Metric.closedBall (0 : Domain3) R)ᶜ ≤ (volume : Measure Domain3) :=
    Measure.restrict_le_self
  have hcong : ⇑(tailVF R w)
      =ᵐ[volume.restrict (Metric.closedBall (0 : Domain3) R)ᶜ]
        (w : Domain3 → EuclideanSpace ℝ (Fin 3)) := MemLp.coeFn_toLp _
  rw [eLpNorm_congr_ae hcong]
  exact ENNReal.toReal_mono (Lp.memLp w).2.ne (eLpNorm_mono_measure _ hle)

/-- **Ball/tail split** of the global L²-vector inner product:
`⟪v, w⟫ = ⟪restrictToBall R v, restrictToBall R w⟫ + ⟪tailVF R v, tailVF R w⟫`. -/
theorem inner_eq_ball_add_tail (R : ℝ) (v w : L2VF_R3) :
    (inner ℝ v w : ℝ)
      = (inner ℝ (restrictToBall R v) (restrictToBall R w) : ℝ)
        + (inner ℝ (tailVF R v) (tailVF R w) : ℝ) := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  -- the integrand for the ball/tail inner products agrees a.e. with `⟪v x, w x⟫`.
  have hball : (∫ x, (inner ℝ ((restrictToBall R v) x) ((restrictToBall R w) x) : ℝ)
        ∂(volume.restrict (Metric.closedBall (0 : Domain3) R)))
      = ∫ x in Metric.closedBall (0 : Domain3) R,
          (inner ℝ (v x : EuclideanSpace ℝ (Fin 3)) (w x : EuclideanSpace ℝ (Fin 3)) : ℝ)
          ∂volume := by
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp (μ := volume.restrict (Metric.closedBall (0 : Domain3) R))
        ((Lp.memLp v).restrict (Metric.closedBall (0 : Domain3) R)),
      MemLp.coeFn_toLp (μ := volume.restrict (Metric.closedBall (0 : Domain3) R))
        ((Lp.memLp w).restrict (Metric.closedBall (0 : Domain3) R))] with x hxv hxw
    show (inner ℝ ((restrictToBall R v) x) ((restrictToBall R w) x) : ℝ) = _
    rw [show ((restrictToBall R v) x) = (v x : EuclideanSpace ℝ (Fin 3)) from hxv,
      show ((restrictToBall R w) x) = (w x : EuclideanSpace ℝ (Fin 3)) from hxw]
  have htail : (∫ x, (inner ℝ ((tailVF R v) x) ((tailVF R w) x) : ℝ)
        ∂(volume.restrict (Metric.closedBall (0 : Domain3) R)ᶜ))
      = ∫ x in (Metric.closedBall (0 : Domain3) R)ᶜ,
          (inner ℝ (v x : EuclideanSpace ℝ (Fin 3)) (w x : EuclideanSpace ℝ (Fin 3)) : ℝ)
          ∂volume := by
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp (μ := volume.restrict (Metric.closedBall (0 : Domain3) R)ᶜ)
        ((Lp.memLp v).restrict (Metric.closedBall (0 : Domain3) R)ᶜ),
      MemLp.coeFn_toLp (μ := volume.restrict (Metric.closedBall (0 : Domain3) R)ᶜ)
        ((Lp.memLp w).restrict (Metric.closedBall (0 : Domain3) R)ᶜ)] with x hxv hxw
    show (inner ℝ ((tailVF R v) x) ((tailVF R w) x) : ℝ) = _
    rw [show ((tailVF R v) x) = (v x : EuclideanSpace ℝ (Fin 3)) from hxv,
      show ((tailVF R w) x) = (w x : EuclideanSpace ℝ (Fin 3)) from hxw]
  rw [hball, htail]
  exact (integral_add_compl measurableSet_closedBall
    (MeasureTheory.L2.integrable_inner (𝕜 := ℝ) v w)).symm

/-- **Cauchy–Schwarz tail bound** (uniform in the second argument's global norm). -/
private theorem abs_tail_inner_le (R : ℝ) (v w : L2VF_R3) :
    |(inner ℝ (tailVF R v) (tailVF R w) : ℝ)| ≤ ‖tailVF R v‖ * ‖w‖ := by
  calc |(inner ℝ (tailVF R v) (tailVF R w) : ℝ)|
      ≤ ‖tailVF R v‖ * ‖tailVF R w‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖tailVF R v‖ * ‖w‖ := by
        apply mul_le_mul_of_nonneg_left (norm_tailVF_le R w) (norm_nonneg _)

/-- **Tail-vanishing** of a fixed L² field: `‖tailVF R v‖ → 0` as `R → ∞`.

Proved via dominated/monotone convergence: `eLpNorm v 2 (B_Rᶜ-restricted)`'s square is the
set-lintegral over `B_Rᶜ` of `‖v ·‖ₑ²`, which decreases to the lintegral over `⋂_R B_Rᶜ = ∅`,
hence to `0`.  We obtain it from the ball-exhaustion `tendsto_setLIntegral_closedBall`: the
ball part increases to the full (finite) integral, so the complement part tends to `0`. -/
theorem tendsto_norm_tailVF_zero (v : L2VF_R3) :
    Tendsto (fun k : ℕ => ‖tailVF (k : ℝ) v‖) atTop (𝓝 0) := by
  classical
  set p2 : ℝ := (2 : ENNReal).toReal with hp2
  have hp2_eq : p2 = 2 := by simp [hp2]
  have hp2_pos : 0 < p2 := by rw [hp2_eq]; norm_num
  -- A measurable representative `v'` of `v` (a.e. equal under `volume`).
  obtain ⟨v', hv'_meas, hv'_ae⟩ := (Lp.memLp v).1
  set H : Domain3 → ENNReal := fun x => ‖v' x‖ₑ ^ p2 with hH
  have hH_meas : Measurable H := (hv'_meas.enorm).pow_const _
  -- `v =ᵐ v'` ⇒ `‖v·‖ₑ^p2 =ᵐ H`.
  have hHv : (fun x => ‖(v : Domain3 → EuclideanSpace ℝ (Fin 3)) x‖ₑ ^ p2) =ᵐ[volume] H := by
    filter_upwards [hv'_ae] with x hx; simp only [hH, hx]
  -- Full lintegral is finite (since `v ∈ L²`).
  have hI_lt : (∫⁻ x, H x ∂volume) < ⊤ := by
    have hfin := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      (p := (2 : ENNReal)) (by norm_num) (by norm_num)).1 (Lp.memLp v).2
    rw [← hp2] at hfin
    rwa [lintegral_congr_ae hHv.symm]
  set I : ENNReal := ∫⁻ x, H x ∂volume with hI
  -- Ball lintegrals of `H` increase to `I`; hence tail lintegrals tend to `0`.
  have hball := tendsto_setLIntegral_closedBall H hH_meas
  -- `Tk := ∫⁻_{B_kᶜ} H = I - (∫⁻_{B_k} H)`.
  have hTk_eq : ∀ k : ℕ,
      (∫⁻ x in (Metric.closedBall (0 : Domain3) (k : ℝ))ᶜ, H x ∂volume)
        = I - ∫⁻ x in Metric.closedBall (0 : Domain3) (k : ℝ), H x ∂volume := by
    intro k
    have hbk_fin : (∫⁻ x in Metric.closedBall (0 : Domain3) (k : ℝ), H x ∂volume) ≠ ⊤ := by
      refine ne_top_of_le_ne_top hI_lt.ne ?_
      exact setLIntegral_le_lintegral _ _
    rw [setLIntegral_compl measurableSet_closedBall hbk_fin]
  have hTk_tendsto : Tendsto
      (fun k : ℕ => ∫⁻ x in (Metric.closedBall (0 : Domain3) (k : ℝ))ᶜ, H x ∂volume)
      atTop (𝓝 0) := by
    have hsub : Tendsto
        (fun k : ℕ => I - ∫⁻ x in Metric.closedBall (0 : Domain3) (k : ℝ), H x ∂volume)
        atTop (𝓝 (I - I)) :=
      ENNReal.Tendsto.sub tendsto_const_nhds hball (Or.inl hI_lt.ne)
    rw [tsub_self] at hsub
    exact (tendsto_congr hTk_eq).2 hsub
  -- `eLpNorm (tail of v) 2 volume = (Tk)^(1/p2)` (after a.e.-replacing `v` by `v'`).
  have heLp_eq : ∀ k : ℕ,
      eLpNorm v 2 (volume.restrict (Metric.closedBall (0 : Domain3) (k : ℝ))ᶜ)
        = (∫⁻ x in (Metric.closedBall (0 : Domain3) (k : ℝ))ᶜ, H x ∂volume) ^ (1 / p2) := by
    intro k
    rw [eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num), ← hp2]
    congr 1
    refine lintegral_congr_ae (ae_restrict_of_ae hHv)
  -- Convert the ENNReal tail to its `toReal` and conclude the real limit.
  have hnorm_eq : ∀ k : ℕ, ‖tailVF (k : ℝ) v‖
      = ((∫⁻ x in (Metric.closedBall (0 : Domain3) (k : ℝ))ᶜ, H x ∂volume) ^ (1 / p2)).toReal := by
    intro k
    rw [tailVF, MeasureTheory.Lp.norm_toLp, heLp_eq k]
  rw [tendsto_congr hnorm_eq]
  -- `(Tk)^(1/p2) → 0^(1/p2) = 0` in ENNReal, then `.toReal → 0`.
  have hrpow : Tendsto
      (fun k : ℕ => (∫⁻ x in (Metric.closedBall (0 : Domain3) (k : ℝ))ᶜ, H x ∂volume) ^ (1 / p2))
      atTop (𝓝 (0 : ENNReal)) := by
    have hcont : Continuous (fun t : ENNReal => t ^ (1 / p2)) :=
      ENNReal.continuous_rpow_const
    have hz : (0 : ENNReal) ^ (1 / p2) = 0 :=
      ENNReal.zero_rpow_of_pos (by positivity : (0:ℝ) < 1 / p2)
    have := (hcont.tendsto 0).comp hTk_tendsto
    rw [hz] at this
    simpa [Function.comp_def] using this
  have := (ENNReal.tendsto_toReal (a := (0 : ENNReal)) (by simp)).comp hrpow
  simpa [Function.comp_def] using this

/-- **D3b.** The assembled global limit `g` lies in `L2Sigma_R3` (weakly divergence-free). -/
theorem ballLimit_global_mem_L2Sigma (B : LocalRellichInput) (M : ℝ)
    (z : ℕ → L2VF_R3)
    (hmem : ∀ n, z n ∈ L2Sigma_R3) (hH1 : ∀ n, memH1VF_R3 (z n))
    (hbd : ∀ n, ‖z n‖ ≤ M) (hvf : ∀ n, viscousFormSq_R3 1 (z n) ≤ M ^ 2)
    (ψ : ℕ → ℕ) (hψ : StrictMono ψ) (g : L2VF_R3)
    (hg : ∀ R : ℝ, Tendsto (fun n => restrictToBall R (z (ψ n))) atTop
      (𝓝 (restrictToBall R g))) :
    g ∈ L2Sigma_R3 := by
  -- Reduce membership in the common kernel to: each `divTestFunctional φ g = 0`.
  rw [L2Sigma_R3, Submodule.mem_iInf]
  intro φ
  rw [LinearMap.mem_ker]
  -- Each `z (ψ n) ∈ L2Sigma_R3`, so `divTestFunctional φ (z (ψ n)) = 0`.
  have hzero : ∀ n, divTestFunctional φ (z (ψ n)) = 0 := by
    intro n
    have := hmem (ψ n)
    rw [L2Sigma_R3, Submodule.mem_iInf] at this
    exact (LinearMap.mem_ker).1 (this φ)
  -- It suffices to show `divTestFunctional φ (z (ψ n)) → divTestFunctional φ g`; the limit of
  -- the constant-zero sequence is then `divTestFunctional φ g = 0` by uniqueness of limits.
  have htend : Tendsto (fun n => divTestFunctional φ (z (ψ n))) atTop
      (𝓝 (divTestFunctional φ g)) := by
    -- G5 closed: ε/3 ball-truncation of the global L²-vector inner product `⟪gradVF φ, ·⟫`.
    set v : L2VF_R3 := gradVF φ with hv
    have hMnonneg : 0 ≤ M := le_trans (norm_nonneg _) (hbd 0)
    -- Rewrite the functional as the global inner product against `v = gradVF φ`.
    have hfun : ∀ w : L2VF_R3, divTestFunctional φ w = (inner ℝ v w : ℝ) :=
      fun w => divTestFunctional_eq_inner φ w
    simp only [hfun]
    -- The ball-part inner products converge (fixed R), for every real `R`.
    have hballconv : ∀ R : ℝ, Tendsto
        (fun n => (inner ℝ (restrictToBall R v) (restrictToBall R (z (ψ n))) : ℝ))
        atTop (𝓝 (inner ℝ (restrictToBall R v) (restrictToBall R g) : ℝ)) :=
      fun R => (tendsto_const_nhds).inner (hg R)
    -- ε/3 argument.
    refine Metric.tendsto_atTop.2 (fun ε hε => ?_)
    -- choose a natural radius `k` so both tails are `< ε/3` uniformly.
    have htail0 := tendsto_norm_tailVF_zero v
    -- target tail-norm threshold: `δ := ε / (3 * (M + ‖g‖ + 1))`.
    set C : ℝ := M + ‖g‖ + 1 with hC
    have hCpos : 0 < C := by positivity
    have hδpos : 0 < ε / (3 * C) := by positivity
    obtain ⟨k0, hk0⟩ := (Metric.tendsto_atTop.1 htail0) (ε / (3 * C)) hδpos
    -- `‖tailVF k v‖ < ε/(3C)` for `k ≥ k0`; fix `k := k0`.
    have htk : ‖tailVF (k0 : ℝ) v‖ < ε / (3 * C) := by
      have := hk0 k0 le_rfl
      rwa [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at this
    have htk_nonneg : 0 ≤ ‖tailVF (k0 : ℝ) v‖ := norm_nonneg _
    -- tail bounds, uniform: `|T_R(z(ψn))| ≤ ‖tail v‖·M` and `|T_R(g)| ≤ ‖tail v‖·‖g‖`.
    have htail_zn : ∀ n,
        |(inner ℝ (tailVF (k0 : ℝ) v) (tailVF (k0 : ℝ) (z (ψ n))) : ℝ)|
          ≤ ‖tailVF (k0 : ℝ) v‖ * M := fun n =>
      le_trans (abs_tail_inner_le (k0 : ℝ) v (z (ψ n)))
        (mul_le_mul_of_nonneg_left (hbd (ψ n)) htk_nonneg)
    have htail_g : |(inner ℝ (tailVF (k0 : ℝ) v) (tailVF (k0 : ℝ) g) : ℝ)|
          ≤ ‖tailVF (k0 : ℝ) v‖ * ‖g‖ :=
      abs_tail_inner_le (k0 : ℝ) v g
    -- the ball part converges, so pick `N` making the ball difference `< ε/3`.
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 (hballconv (k0 : ℝ))) (ε / 3) (by positivity)
    refine ⟨N, fun n hn => ?_⟩
    -- split both `⟪v, z(ψn)⟫` and `⟪v, g⟫` into ball + tail.
    rw [Real.dist_eq]
    rw [inner_eq_ball_add_tail (k0 : ℝ) v (z (ψ n)), inner_eq_ball_add_tail (k0 : ℝ) v g]
    -- the ball difference bound.
    have hballn := hN n hn
    rw [Real.dist_eq] at hballn
    -- algebra: |(B₁+T₁)-(B₂+T₂)| ≤ |B₁-B₂| + |T₁| + |T₂|.
    have hbM : ‖tailVF (k0 : ℝ) v‖ * M < ε / 3 := by
      calc ‖tailVF (k0 : ℝ) v‖ * M ≤ ‖tailVF (k0 : ℝ) v‖ * C := by
              apply mul_le_mul_of_nonneg_left _ htk_nonneg; rw [hC]; linarith [norm_nonneg g]
        _ < (ε / (3 * C)) * C := by apply mul_lt_mul_of_pos_right htk hCpos
        _ = ε / 3 := by field_simp
    have hbg : ‖tailVF (k0 : ℝ) v‖ * ‖g‖ < ε / 3 := by
      calc ‖tailVF (k0 : ℝ) v‖ * ‖g‖ ≤ ‖tailVF (k0 : ℝ) v‖ * C := by
              apply mul_le_mul_of_nonneg_left _ htk_nonneg; rw [hC]; linarith [norm_nonneg g]
        _ < (ε / (3 * C)) * C := by apply mul_lt_mul_of_pos_right htk hCpos
        _ = ε / 3 := by field_simp
    have htn := lt_of_le_of_lt (htail_zn n) hbM
    have htg := lt_of_le_of_lt htail_g hbg
    -- Name the four scalar pieces; the triangle inequality + the three bounds finish.
    set B1 : ℝ := inner ℝ (restrictToBall (k0 : ℝ) v) (restrictToBall (k0 : ℝ) (z (ψ n))) with hB1
    set T1 : ℝ := inner ℝ (tailVF (k0 : ℝ) v) (tailVF (k0 : ℝ) (z (ψ n))) with hT1
    set B2 : ℝ := inner ℝ (restrictToBall (k0 : ℝ) v) (restrictToBall (k0 : ℝ) g) with hB2
    set T2 : ℝ := inner ℝ (tailVF (k0 : ℝ) v) (tailVF (k0 : ℝ) g) with hT2
    have hb1b2 : |B1 - B2| < ε / 3 := hballn
    have hT1' : |T1| < ε / 3 := htn
    have hT2' : |T2| < ε / 3 := htg
    rw [abs_lt] at hb1b2 hT1' hT2' ⊢
    constructor <;> linarith [hb1b2.1, hb1b2.2, hT1'.1, hT1'.2, hT2'.1, hT2'.2]
  have h0 : Tendsto (fun n => divTestFunctional φ (z (ψ n))) atTop (𝓝 0) := by
    simp only [hzero]; exact tendsto_const_nhds
  exact tendsto_nhds_unique htend h0

/-! ### Tier 4 — final packaging (the deliverable) -/

/-- **LOCAL spatial compactness on ℝ³, from the isolated local-Rellich input.**

Reproduces the exact conclusion of `spatial_compactness_R3` (SolutionInterfaces.lean:378–389)
axiom-free, conditional only on `LocalRellichInput` (the unconditional local compact
embedding H¹(B_R) ↪↪ L²(B_R), which mathlib lacks). -/
theorem localCompactness_R3_of_ballCompact (B : LocalRellichInput) :
    ∀ (M : ℝ) (z : ℕ → L2VF_R3),
    (∀ n, z n ∈ L2Sigma_R3) →
    (∀ n, memH1VF_R3 (z n)) →
    (∀ n, ‖z n‖ ≤ M) →
    (∀ n, viscousFormSq_R3 1 (z n) ≤ M ^ 2) →
    ∃ (ψ : ℕ → ℕ) (g : L2VF_R3), StrictMono ψ ∧ g ∈ L2Sigma_R3 ∧
      ∀ R : ℝ, Filter.Tendsto
        (fun n => ∫ x in Metric.closedBall (0 : Domain3) R,
          ‖((z (ψ n)) x : EuclideanSpace ℝ (Fin 3)) - (g x : EuclideanSpace ℝ (Fin 3))‖ ^ 2
          ∂(volume : Measure Domain3))
        Filter.atTop (nhds 0) := by
  classical
  intro M z hmem hH1 hbd hvf
  -- D2: a single subsequence with ball-`k` limits for every natural `k`.
  obtain ⟨ψ, hψ, hball⟩ :=
    exists_subseq_tendsto_on_all_balls B M z hmem hH1 hbd hvf
  -- Package the ball-`k` limits as a family and the convergence.
  choose gk hgk using hball
  -- D3a: glue the consistent ball-limits into a single global a.e. function `g₀`.
  obtain ⟨g₀, hg₀mem, hg₀ae⟩ :=
    ballLimits_are_consistent B M z hmem hH1 hbd hvf ψ hψ gk hgk
  -- The global limit `g := g₀.toLp`.
  set g : L2VF_R3 := hg₀mem.toLp with hgdef
  have hg_coe : ⇑g =ᵐ[volume] g₀ := MemLp.coeFn_toLp _
  -- For every real `R`, the ball-`R` restrictions converge to `restrictToBall R g`.
  have hconvR : ∀ R : ℝ,
      Tendsto (fun n => restrictToBall R (z (ψ n))) atTop (𝓝 (restrictToBall R g)) := by
    intro R
    -- pick a natural `k ≥ R`.
    obtain ⟨k, hk⟩ := exists_nat_ge R
    -- the ball-`k` limit `gk k` agrees a.e. on `B_k` with `g`.
    have hgk_ae : (gk k : Domain3 → EuclideanSpace ℝ (Fin 3))
        =ᵐ[volume.restrict (Metric.closedBall (0 : Domain3) (k : ℝ))]
          (g : Domain3 → EuclideanSpace ℝ (Fin 3)) := by
      have hg_coe_R : ⇑g =ᵐ[volume.restrict (Metric.closedBall (0 : Domain3) (k : ℝ))] g₀ :=
        ae_restrict_of_ae hg_coe
      filter_upwards [hg₀ae k, hg_coe_R] with x hx hxg
      rw [hx, ← hxg]
    exact tendsto_restrictToBall_of_ballLimit (fun n => z (ψ n)) g R (k : ℝ) hk
      (gk k) hgk_ae (hgk k)
  -- D3b: the global limit is divergence-free.
  have hg_mem : g ∈ L2Sigma_R3 :=
    ballLimit_global_mem_L2Sigma B M z hmem hH1 hbd hvf ψ hψ g hconvR
  refine ⟨ψ, g, hψ, hg_mem, ?_⟩
  intro R
  -- Convert the metric convergence at radius `R` to the set-integral via D0c.
  have hdist : Tendsto (fun n => dist (restrictToBall R (z (ψ n))) (restrictToBall R g))
      atTop (𝓝 0) := by
    have hc : Tendsto (fun _ : ℕ => restrictToBall R g) atTop (𝓝 (restrictToBall R g)) :=
      tendsto_const_nhds
    have := (hconvR R).dist hc
    simpa using this
  have hsq : Tendsto (fun n =>
      dist (restrictToBall R (z (ψ n))) (restrictToBall R g) ^ 2) atTop (𝓝 0) := by
    have hc : Tendsto (fun t : ℝ => t ^ 2) (𝓝 (0 : ℝ)) (𝓝 0) := by
      have := (continuous_pow 2).tendsto (0 : ℝ)
      simpa using this
    have := hc.comp hdist
    simpa [Function.comp_def] using this
  refine hsq.congr fun n => ?_
  exact (setIntegral_normSq_eq_dist_sq_restrictToBall R (z (ψ n)) g).symm

end LerayHopf
