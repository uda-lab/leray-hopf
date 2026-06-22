/-
# LerayHopf.R3.ArzelaAscoliTime — Issue #44 scaffold

**Goal (issue #44):** Replace the axiom `galerkinSpaceTimeExtraction_R3` with a proof built
from two thinner axioms (T0.1, T0.2) plus the Arzelà–Ascoli / diagonalization chain (T1–T4).
This file houses the two residual axioms and the intermediate lemmas; the consumer
`AubinLionsLimitPassage.lean` calls back into these lemmas to assemble T5.1.

**Architecture (import-cycle safety):**
  R3.SpatialCompactness   (LocalRellichInput, L2ballR3, restrictToBall)
        └── R3.AxiomaticClosure  (GalerkinSolutionData_R3)
                └── R3.AubinLionsLimitPassage  (imports this file)
                        ← R3.ArzelaAscoliTime  [THIS FILE]
This file imports only `R3.AxiomaticClosure` and `R3.SpatialCompactness`, which avoids
cycles; `AubinLionsLimitPassage` then imports both this file and the above.

## Declarations (dependency order, matching contract §5)

### Group T0 — two thin residual axioms (replace the single fat axiom)

- `galerkin_equicontinuity_from_ODE`  (T0.1)  axiom — ODE equicontinuity
- `galerkin_weakLimit_R3`             (T0.2)  axiom — Banach–Alaoglu + div-free weak limit

### Group T1 — equicontinuity transfer (from T0.1)

- `galerkin_curves_equicont_unconditional`       (T1.1)  must-prove
- `galerkin_curves_in_boundedContinuousFunctions`(T1.2)  must-prove

### Group T2 — per-ball Arzelà–Ascoli (from T1 + LocalRellichInput)

- `galSeq_ball_pointwisePrecompact`   (T2.1)  must-prove
- `galSeq_ball_equicont`              (T2.2)  must-prove
- `perBallSubseq_exists`              (T2.3)  must-prove

### Group T3 — diagonal subsequence

- `perBallSubseq_tower`               (T3.1)  must-prove
- `diagonalSubseq_exists`             (T3.2)  must-prove

### Group T4 — gluing + measurability

- `perBallLimit_measurable`           (T4.1)  must-prove
- `u_lim_aestronglyMeasurable`        (T4.2)  must-prove

## Assumptions (new axioms, per AGENTS.md "Every PR must report")

1. `galerkin_equicontinuity_from_ODE` — ALLOW_AXIOM: uniform time modulus of Galerkin curves
   from ODE; requires n-uniform dual-norm bound on B(u_n,u_n) in V*, which needs Sobolev
   trilinear estimate (Temam III.2.3) not exposed by R3NSForms.b; TRUE and scheme-independent;
   dischargeable once R3NSForms is strengthened with b_dual_norm_bound.

2. `galerkin_weakLimit_R3` — ALLOW_AXIOM: per-ball-L²-convergent bounded sequence has weak
   limit in L2Sigma_R3; requires Banach–Alaoglu (bounded ball weakly compact in reflexive space)
   + weak-closedness of L2Sigma_R3 (divergence-free is weakly closed) — both standard functional
   analysis, not formalized in Mathlib; reusable for torus variant.
-/

import LerayHopf.R3.AxiomaticClosure   -- GalerkinSolutionData_R3, R3GalerkinScheme, R3NSForms
import LerayHopf.R3.SpatialCompactness -- LocalRellichInput, L2ballR3, restrictToBall, norm_restrictToBall_le'

-- Equicontinuity bridge (Metric.equicontinuous_of_continuity_modulus)
import Mathlib.Topology.MetricSpace.Equicontinuity
-- BoundedContinuousFunction.arzela_ascoli₂
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
-- IsCompact.isSeqCompact, IsSeqCompact.subseq_of_frequently_in
import Mathlib.Topology.Sequences
-- aestronglyMeasurable_of_tendsto_ae
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable

namespace LerayHopf

open MeasureTheory Filter Topology Metric BoundedContinuousFunction

/-! ### Group T0 — Two thin residual axioms -/

/-- **T0.1 — Uniform time equicontinuity of Galerkin curves (from ODE structure).**

For every `ε > 0` there exists `δ > 0` (depending only on `ν`, `u₀`, `T`) such that
uniformly in `n` and in `s, t ∈ [0,T]` with `|s − t| < δ`,
`‖(galSeq n).u s − (galSeq n).u t‖_{L²} < ε`.

**Mathematical content:** Follows from Bochner-FTC applied to `u_hasDeriv`, with derivative
bounded by `‖u'_n(r)‖ ≤ ν ‖Au_n(r)‖_{V*} + ‖B(u_n(r), u_n(r))‖_{V*}`.  The viscous part is
controlled by `reg_bound` (L²-in-time H¹) via Cauchy–Schwarz; the convection part requires an
n-uniform dual-norm bound `|F.b(u,u,w)| ≤ C ‖u‖_{H¹}² ‖w‖` (Temam III.2.3 / 3D Sobolev
trilinear estimate) that `R3NSForms.b` does NOT currently expose.

**Thinness:** This axiom isolates ONLY the ODE equicontinuity modulus.  It carries NO
subsequence, NO limit, NO spatial compactness. -/
axiom galerkin_equicontinuity_from_ODE -- ALLOW_AXIOM: uniform time modulus of Galerkin curves from ODE; requires n-uniform dual-norm bound on B(u_n,u_n) in V*, which needs Sobolev trilinear estimate (Temam III.2.3) not exposed by R3NSForms.b; TRUE and scheme-independent; dischargeable once R3NSForms is strengthened with b_dual_norm_bound
    (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T) (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ (n : ℕ) (s t : ℝ),
      s ∈ Set.Icc (0 : ℝ) T → t ∈ Set.Icc (0 : ℝ) T → |s - t| < δ →
      ‖((galSeq n).u s : L2VF_R3) - ((galSeq n).u t : L2VF_R3)‖ < ε

/-- **T0.2 — Weak limit in `L2Sigma_R3` from per-ball L² convergence (Banach–Alaoglu).**

Given a strictly-monotone subsequence `φ` such that for every ball radius `R : ℝ` and every
`t ∈ [0,T]` the ball-restricted Galerkin states converge (i.e., `∃ g_R`, the sequence
`restrictToBall R ((galSeq (φ n)).u t)` converges to `g_R` in `L2ballR3 R`), there exists a
measurable limit curve `u : Time → L2Sigma_R3` such that:
- `u` is `AEStronglyMeasurable` on `[0,T]` (as an `L2VF_R3`-valued curve), and
- for every `R : ℝ`, for a.e. `t ∈ [0,T]`, the ball-restricted Galerkin states converge to
  `restrictToBall R (u t : L2VF_R3)`.

**Mathematical content:** The per-ball strong convergence + uniform L² bound `‖(galSeq n).u t‖ ≤ ‖u₀‖`
imply weak convergence in the Hilbert space `L2VF_R3` at each `t` (local strong → global weak).
The weak limit inherits the divergence-free constraint `L2Sigma_R3` because `L2Sigma_R3 = ker(div)`
is a CLOSED subspace, hence WEAKLY CLOSED.  Measurability follows from
`aestronglyMeasurable_of_tendsto_ae` applied to the per-ball a.e. convergent sequence.

**Gap in Mathlib:** Banach–Alaoglu for Hilbert spaces (`IsReflexive` + bounded net has weakly
convergent subnet) and weak-closedness of `L2Sigma_R3` (= closed subspace of a Hilbert space)
are both standard but not currently formalized at the required interface level in Mathlib. -/
axiom galerkin_weakLimit_R3 -- ALLOW_AXIOM: per-ball-L²-convergent bounded sequence has weak limit in L2Sigma_R3; requires Banach–Alaoglu (bounded ball weakly compact in reflexive space) + weak-closedness of L2Sigma_R3 (divergence-free is weakly closed) — both standard functional analysis, not formalized in Mathlib; reusable for torus variant
    (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊) (ν : ℝ) (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n) (φ : ℕ → ℕ)
    (hφ : StrictMono φ)
    (T : ℝ) (hT : 0 < T)
    (hball : ∀ R : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T, ∃ g_R : L2ballR3 R,
      Filter.Tendsto (fun n => restrictToBall R ((galSeq (φ n)).u t : L2VF_R3))
        Filter.atTop (nhds g_R)) :
    ∃ u : Time → L2Sigma_R3,
      AEStronglyMeasurable (fun t => (u t : L2VF_R3))
        (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)) ∧
      ∀ R : ℝ, ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)),
        Filter.Tendsto (fun n => restrictToBall R ((galSeq (φ n)).u t : L2VF_R3))
          Filter.atTop (nhds (restrictToBall R (u t : L2VF_R3)))

/-! ### Local plumbing for the ball restriction (1-Lipschitz + continuity)

The corresponding helpers in `AubinLionsLimitPassage.lean` (`restrictToBall_dist_le`,
`norm_restrictToBall_le'`, `continuous_restrictToBall`) are `private` and live downstream of this
file, so we reprove the small facts we need here. -/

/-- `restrictToBall R` is `1`-Lipschitz on differences: the ball-restricted difference has L²-norm
bounded by the global difference. Local copy (the P3 / passage versions are `private`). -/
private theorem norm_restrictToBall_sub_le (R : ℝ) (u v : L2VF_R3) :
    ‖restrictToBall R u - restrictToBall R v‖ ≤ ‖u - v‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  have hle : volume.restrict (Metric.closedBall (0 : Domain3) R) ≤ (volume : Measure Domain3) :=
    Measure.restrict_le_self
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

/-- `restrictToBall R : L2VF_R3 → L2ballR3 R` is continuous (it is `1`-Lipschitz). -/
private theorem continuous_restrictToBall' (R : ℝ) :
    Continuous (fun w : L2VF_R3 => restrictToBall R w) := by
  refine Metric.continuous_iff.2 fun w ε hε => ⟨ε, hε, fun w' hw' => ?_⟩
  calc dist (restrictToBall R w') (restrictToBall R w)
      = ‖restrictToBall R w' - restrictToBall R w‖ := dist_eq_norm _ _
    _ ≤ ‖w' - w‖ := norm_restrictToBall_sub_le R w' w
    _ = dist w' w := (dist_eq_norm _ _).symm
    _ < ε := hw'

/-- Restriction to a smaller ball `B_R` is distance-nonincreasing relative to the larger ball
`B_k` (`R ≤ k`): the difference's `L²(B_R)`-norm is bounded by its `L²(B_k)`-norm, because the
integrand is nonnegative and `B_R ⊆ B_k`. Local copy of the content of P3's
`furtherRestrict_dist_le` (which is `private`). -/
private theorem restrictToBall_sub_norm_mono (R k : ℝ) (hRk : R ≤ k) (w w' : L2VF_R3) :
    ‖restrictToBall R w - restrictToBall R w'‖ ≤ ‖restrictToBall k w - restrictToBall k w'‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  have hsub : Metric.closedBall (0 : Domain3) R ⊆ Metric.closedBall (0 : Domain3) k :=
    Metric.closedBall_subset_closedBall hRk
  have hle : volume.restrict (Metric.closedBall (0 : Domain3) R)
      ≤ volume.restrict (Metric.closedBall (0 : Domain3) k) :=
    Measure.restrict_mono hsub le_rfl
  have hcongR : ⇑(restrictToBall R w - restrictToBall R w')
      =ᵐ[volume.restrict (Metric.closedBall (0 : Domain3) R)]
        (fun x => (w x : EuclideanSpace ℝ (Fin 3)) - (w' x : EuclideanSpace ℝ (Fin 3))) := by
    have hsub2 := Lp.coeFn_sub (restrictToBall R w) (restrictToBall R w')
    have hu : ⇑(restrictToBall R w)
        =ᵐ[volume.restrict (Metric.closedBall (0 : Domain3) R)]
          (w : Domain3 → EuclideanSpace ℝ (Fin 3)) := MemLp.coeFn_toLp _
    have hv : ⇑(restrictToBall R w')
        =ᵐ[volume.restrict (Metric.closedBall (0 : Domain3) R)]
          (w' : Domain3 → EuclideanSpace ℝ (Fin 3)) := MemLp.coeFn_toLp _
    filter_upwards [hsub2, hu, hv] with x hx hxu hxv
    simp only [hx, Pi.sub_apply, hxu, hxv]
  have hcongK : ⇑(restrictToBall k w - restrictToBall k w')
      =ᵐ[volume.restrict (Metric.closedBall (0 : Domain3) k)]
        (fun x => (w x : EuclideanSpace ℝ (Fin 3)) - (w' x : EuclideanSpace ℝ (Fin 3))) := by
    have hsub2 := Lp.coeFn_sub (restrictToBall k w) (restrictToBall k w')
    have hu : ⇑(restrictToBall k w)
        =ᵐ[volume.restrict (Metric.closedBall (0 : Domain3) k)]
          (w : Domain3 → EuclideanSpace ℝ (Fin 3)) := MemLp.coeFn_toLp _
    have hv : ⇑(restrictToBall k w')
        =ᵐ[volume.restrict (Metric.closedBall (0 : Domain3) k)]
          (w' : Domain3 → EuclideanSpace ℝ (Fin 3)) := MemLp.coeFn_toLp _
    filter_upwards [hsub2, hu, hv] with x hx hxu hxv
    simp only [hx, Pi.sub_apply, hxu, hxv]
  rw [eLpNorm_congr_ae hcongR, eLpNorm_congr_ae hcongK]
  refine ENNReal.toReal_mono ?_ (eLpNorm_mono_measure _ hle)
  rw [← eLpNorm_congr_ae hcongK]
  exact (Lp.memLp (restrictToBall k w - restrictToBall k w')).2.ne

/-! ### Group T1 — Equicontinuity transfer -/

/-- **T1.1 — Unconditional uniform equicontinuity on the ball restriction.**

Given `galerkin_equicontinuity_from_ODE` (T0.1), the composite family
`(n, t) ↦ restrictToBall R ((galSeq n).u t)` is uniformly equicontinuous on `[0,T]`
for every fixed `R : ℝ`.

**Proof:** `norm_restrictToBall_le'` gives `‖restrictToBall R u - restrictToBall R v‖ ≤ ‖u - v‖`
(1-Lipschitz), so the modulus from T0.1 transfers directly.  Then
`Metric.equicontinuous_of_continuity_modulus` packages the global modulus into
`Equicontinuous`. -/
theorem galerkin_curves_equicont_unconditional
    (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T) (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n)
    (R : ℝ) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ (n : ℕ) (s t : ℝ),
      s ∈ Set.Icc (0 : ℝ) T → t ∈ Set.Icc (0 : ℝ) T → |s - t| < δ →
      ‖restrictToBall R ((galSeq n).u s : L2VF_R3) -
        restrictToBall R ((galSeq n).u t : L2VF_R3)‖ < ε := by
  intro ε hε
  obtain ⟨δ, hδ, hmod⟩ := galerkin_equicontinuity_from_ODE 𝔊 F ν hν T hT u₀ galSeq ε hε
  refine ⟨δ, hδ, fun n s t hs ht hst => ?_⟩
  calc ‖restrictToBall R ((galSeq n).u s : L2VF_R3) -
          restrictToBall R ((galSeq n).u t : L2VF_R3)‖
      ≤ ‖((galSeq n).u s : L2VF_R3) - ((galSeq n).u t : L2VF_R3)‖ :=
        norm_restrictToBall_sub_le R _ _
    _ < ε := hmod n s t hs ht hst

/-- **T1.2 — Packaging Galerkin ball-curves as bounded continuous functions.**

For each `n : ℕ`, the map `t ↦ restrictToBall R ((galSeq n).u t)` restricted to `[0,T]`
defines a bounded continuous function `[0,T] →ᵇ L2ballR3 R`.

**Proof:** Continuity follows from `galerkin_curve_continuous` + `continuous_restrictToBall`.
Boundedness follows from `galerkin_norm_le_u0` + `norm_restrictToBall_le'`. -/
theorem galerkin_curves_in_boundedContinuousFunctions
    (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T) (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n)
    (R : ℝ) (n : ℕ) :
    ∃ f : Set.Icc (0 : ℝ) T →ᵇ L2ballR3 R,
      ∀ t : Set.Icc (0 : ℝ) T,
        f t = restrictToBall R ((galSeq n).u (t : ℝ) : L2VF_R3) := by
  -- The Galerkin curve is continuous on `Ici 0` (it is differentiable there).
  have hIci : ContinuousOn (fun s => ((galSeq n).u s : L2VF_R3)) (Set.Ici 0) :=
    fun t ht => (((galSeq n).u_hasDeriv t ht).continuousAt.continuousWithinAt)
  have hIcc : ContinuousOn (fun s => ((galSeq n).u s : L2VF_R3)) (Set.Icc (0 : ℝ) T) :=
    hIci.mono Set.Icc_subset_Ici_self
  -- As a continuous map on the compact subtype `↥(Icc 0 T)`, composed with `restrictToBall R`.
  let F0 : C(Set.Icc (0 : ℝ) T, L2ballR3 R) :=
    ⟨fun t => restrictToBall R ((galSeq n).u (t : ℝ) : L2VF_R3),
      (continuous_restrictToBall' R).comp hIcc.restrict⟩
  refine ⟨BoundedContinuousFunction.mkOfCompact F0, fun t => rfl⟩

/-! ### Group T2 — Per-ball Arzelà–Ascoli -/

/-- **T2.1 — Pointwise precompactness of ball restrictions at each time.**

For fixed `R : ℝ` and `t ∈ [0,T]`, the set
`{restrictToBall R ((galSeq n).u t) | n : ℕ}` is precompact in `L2ballR3 R`.

**Proof sketch:** Use `LocalRellichInput.ballCompact` with the Steklov-average bridge:
the Steklov averages satisfy the pointwise H¹ bound (via `viscousFormSq_steklovAvg_uniform_bound`),
so their restrictions lie in a compact set `K_R`.  By equicontinuity (T0.1) + continuity,
the raw-curve values `restrictToBall R ((galSeq n).u t)` are within `ε/3` of the corresponding
Steklov averages (for small `δ`), so they also lie in a neighborhood of `K_R`, giving
precompactness.  (2/3-ε argument.) -/
theorem galSeq_ball_pointwisePrecompact
    (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T) (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n)
    (B : LocalRellichInput)
    (R : ℝ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ∃ K : Set (L2ballR3 R), IsCompact K ∧
      ∀ n : ℕ, restrictToBall R ((galSeq n).u t : L2VF_R3) ∈ K := by
  sorry -- ALLOW_SORRY: #44 galSeq_ball_pointwisePrecompact, to be discharged by lean-prover

/-- **T2.2 — Ball-restricted family is equicontinuous on `[0,T]`.**

The family `n ↦ (t ↦ restrictToBall R ((galSeq n).u t))` is equicontinuous on `[0,T]`,
inheriting the modulus from T1.1 via the 1-Lipschitz property of `restrictToBall`. -/
theorem galSeq_ball_equicont
    (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T) (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n)
    (R : ℝ) :
    Equicontinuous (fun n => fun t : Set.Icc (0 : ℝ) T =>
      restrictToBall R ((galSeq n).u (t : ℝ) : L2VF_R3)) := by
  intro x₀
  rw [Metric.equicontinuousAt_iff]
  intro ε hε
  obtain ⟨δ, hδ, hmod⟩ :=
    galerkin_curves_equicont_unconditional 𝔊 F ν hν T hT u₀ galSeq R ε hε
  refine ⟨δ, hδ, fun x hx n => ?_⟩
  rw [dist_eq_norm]
  rw [Subtype.dist_eq, Real.dist_eq] at hx
  exact hmod n (x₀ : ℝ) (x : ℝ) x₀.2 x.2 (by rwa [abs_sub_comm] at hx)

/-- **T2.3 — Per-ball subsequence existence (Arzelà–Ascoli).**

For each fixed `R : ℝ`, there exists a strictly-monotone `φ_R : ℕ → ℕ` and a continuous
function `f_R : ℝ → L2ballR3 R` such that
`restrictToBall R ((galSeq (φ_R n)).u t)` converges to `f_R t` for every `t ∈ [0,T]`.

**Proof route:** Apply `BoundedContinuousFunction.arzela_ascoli₂` to:
- compact domain: `Set.Icc 0 T` (compact via `isCompact_Icc`),
- compact range-container: `K_R` from T2.1 (IsCompact),
- equicontinuity: from T2.2 (`galSeq_ball_equicont`).
Extract subsequence via `IsCompact.isSeqCompact` + `IsSeqCompact.subseq_of_frequently_in`. -/
theorem perBallSubseq_exists
    (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T) (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n)
    (B : LocalRellichInput)
    (R : ℝ) :
    ∃ (φ_R : ℕ → ℕ) (f_R : ℝ → L2ballR3 R),
      StrictMono φ_R ∧
      ContinuousOn f_R (Set.Icc (0 : ℝ) T) ∧
      ∀ t ∈ Set.Icc (0 : ℝ) T,
        Filter.Tendsto
          (fun n => restrictToBall R ((galSeq (φ_R n)).u t : L2VF_R3))
          Filter.atTop (nhds (f_R t)) := by
  sorry -- ALLOW_SORRY: #44 perBallSubseq_exists, to be discharged by lean-prover

/-! ### Group T3 — Diagonal subsequence -/

/-- **T3.1 — Tower construction: each `φ_{R+1}` is a subsequence of `φ_R`.**

Given the per-ball subsequences from T2.3, construct inductively a tower
`φ_0, φ_1, φ_2, ...` where `φ_{k+1}` is a refinement of `φ_k` (i.e., the composition
`φ_{k+1}` extracts a subsequence of `φ_k`'s output), and the limit curve `f_{k+1}` at
radius `k+1` is consistent with ball-convergence under `φ_{k+1}`.

**Proof route:** Induction using `perBallSubseq_exists` applied to the reindexed sequence
`n ↦ galSeq (φ_k n)`. -/
theorem perBallSubseq_tower
    (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T) (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n)
    (B : LocalRellichInput) :
    ∃ (tower : ℕ → ℕ → ℕ),
      (∀ k, StrictMono (tower k)) ∧
      (∀ k, ∀ n, ∃ m, tower (k + 1) n = tower k m) ∧
      (∀ k : ℕ, ∃ f_k : ℝ → L2ballR3 k,
        ∀ t ∈ Set.Icc (0 : ℝ) T,
          Filter.Tendsto
            (fun n => restrictToBall k ((galSeq (tower k n)).u t : L2VF_R3))
            Filter.atTop (nhds (f_k t))) := by
  sorry -- ALLOW_SORRY: #44 perBallSubseq_tower, to be discharged by lean-prover

/-- **T3.2 — Diagonal subsequence: converges for ALL ball radii simultaneously.**

From the tower (T3.1), the diagonal sequence `φ n := tower n n` is strictly monotone and
for every `k : ℕ` and every `t ∈ [0,T]`, the ball-restricted states at radius `k` converge:
`restrictToBall k ((galSeq (φ n)).u t) → limits k t` as `n → ∞`.

This gives convergence on every ball by the eventual-subsequence argument (for `n ≥ k`,
`φ n = tower n n` is a subsequence of `tower k`, so convergence at level `k` propagates). -/
theorem diagonalSubseq_exists
    (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T) (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n)
    (B : LocalRellichInput) :
    ∃ (φ : ℕ → ℕ),
      StrictMono φ ∧
      ∀ k : ℕ, ∃ f_k : ℝ → L2ballR3 k,
        ContinuousOn f_k (Set.Icc (0 : ℝ) T) ∧
        ∀ t ∈ Set.Icc (0 : ℝ) T,
          Filter.Tendsto
            (fun n => restrictToBall k ((galSeq (φ n)).u t : L2VF_R3))
            Filter.atTop (nhds (f_k t)) := by
  sorry -- ALLOW_SORRY: #44 diagonalSubseq_exists, to be discharged by lean-prover

/-! ### Group T4 — Gluing + measurability -/

/-- **T4.1 — Per-ball limit curve is strongly measurable.**

For each `k : ℕ`, the limit curve `limits k : ℝ → L2ballR3 k` (from T3.2) is
`AEStronglyMeasurable` on `[0,T]`.

**Proof:** The limit curve is continuous on `[0,T]` (from T3.2), hence strongly measurable
via `ContinuousOn.aestronglyMeasurable measurableSet_Icc`. -/
theorem perBallLimit_measurable
    (k : ℕ)
    (f_k : ℝ → L2ballR3 k)
    (T : ℝ)
    (hf_k_cont : ContinuousOn f_k (Set.Icc (0 : ℝ) T)) :
    AEStronglyMeasurable f_k
      (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)) :=
  hf_k_cont.aestronglyMeasurable measurableSet_Icc

/-- **T4.2 — The assembled limit curve `u : Time → L2Sigma_R3` is AE strongly measurable.**

Combines T0.2 (`galerkin_weakLimit_R3`) with the pointwise per-ball convergence from T3.2
to produce the measurable limit curve `u`.

**Proof:** T3.2 provides the diagonal subsequence `φ` and the per-ball limit curves, giving
for each `R : ℝ` and each `t ∈ [0,T]` the convergence `restrictToBall R ((galSeq (φ n)).u t) → g_R(t)`.
Apply T0.2 to get the `u : Time → L2Sigma_R3` with the `AEStronglyMeasurable` conclusion. -/
theorem u_lim_aestronglyMeasurable
    (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T) (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n)
    (B : LocalRellichInput) :
    ∃ (φ : ℕ → ℕ) (u : Time → L2Sigma_R3),
      StrictMono φ ∧
      AEStronglyMeasurable (fun t => (u t : L2VF_R3))
        (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)) ∧
      ∀ R : ℝ, ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)),
        Filter.Tendsto (fun n => restrictToBall R ((galSeq (φ n)).u t : L2VF_R3))
          Filter.atTop (nhds (restrictToBall R (u t : L2VF_R3))) := by
  -- The diagonal subsequence converges per-ball-radius-`k` (over `ℕ`) at every `t ∈ [0,T]`.
  obtain ⟨φ, hφ, hk⟩ := diagonalSubseq_exists 𝔊 F ν hν T hT u₀ galSeq B
  -- Promote ℕ-radius convergence to ℝ-radius convergence (existence of a per-ball limit), which
  -- is the hypothesis `galerkin_weakLimit_R3` (T0.2) consumes.  For real `R`, the ball-`R`
  -- restriction is a `1`-Lipschitz contraction of the convergent ball-`⌈R⌉₊` sequence, hence
  -- Cauchy, hence convergent in the complete space `L2ballR3 R`.
  have hball : ∀ R : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T, ∃ g_R : L2ballR3 R,
      Filter.Tendsto (fun n => restrictToBall R ((galSeq (φ n)).u t : L2VF_R3))
        Filter.atTop (nhds g_R) := by
    intro R t ht
    set k : ℕ := ⌈R⌉₊ with hk_def
    have hRk : R ≤ (k : ℝ) := Nat.le_ceil R
    obtain ⟨f_k, _hf_cont, hf_conv⟩ := hk k
    -- ball-`k` convergence ⇒ Cauchy.
    have hbCauchy : CauchySeq
        (fun n => restrictToBall (k : ℝ) ((galSeq (φ n)).u t : L2VF_R3)) :=
      (hf_conv t ht).cauchySeq
    -- ball-`R` sequence is Cauchy by the contraction bound.
    have haCauchy : CauchySeq
        (fun n => restrictToBall R ((galSeq (φ n)).u t : L2VF_R3)) := by
      rw [Metric.cauchySeq_iff] at hbCauchy ⊢
      intro ε hε
      obtain ⟨N, hN⟩ := hbCauchy ε hε
      refine ⟨N, fun m hm n hn => ?_⟩
      calc dist (restrictToBall R ((galSeq (φ m)).u t : L2VF_R3))
              (restrictToBall R ((galSeq (φ n)).u t : L2VF_R3))
          = ‖restrictToBall R ((galSeq (φ m)).u t : L2VF_R3)
              - restrictToBall R ((galSeq (φ n)).u t : L2VF_R3)‖ := dist_eq_norm _ _
        _ ≤ ‖restrictToBall (k : ℝ) ((galSeq (φ m)).u t : L2VF_R3)
              - restrictToBall (k : ℝ) ((galSeq (φ n)).u t : L2VF_R3)‖ :=
            restrictToBall_sub_norm_mono R (k : ℝ) hRk _ _
        _ = dist (restrictToBall (k : ℝ) ((galSeq (φ m)).u t : L2VF_R3))
              (restrictToBall (k : ℝ) ((galSeq (φ n)).u t : L2VF_R3)) := (dist_eq_norm _ _).symm
        _ < ε := hN m hm n hn
    obtain ⟨g, hg⟩ := cauchySeq_tendsto_of_complete haCauchy
    exact ⟨g, hg⟩
  -- Apply T0.2 (`galerkin_weakLimit_R3`) to obtain the measurable limit curve.
  obtain ⟨u, hmeas, hconv⟩ :=
    galerkin_weakLimit_R3 𝔊 F ν u₀ galSeq φ hφ T hT hball
  exact ⟨φ, u, hφ, hmeas, hconv⟩

end LerayHopf
