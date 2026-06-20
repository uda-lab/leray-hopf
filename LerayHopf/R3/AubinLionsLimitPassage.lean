/-
# LerayHopf.R3.AubinLionsLimitPassage — milestone P2 (Aubin–Lions reduction + reusable analytic core)

**Milestone:** `p2-aubin-lions` (honest PARTIAL substantiation; contract
`docs/scratch/p2-aubin-lions.md`, ADDENDUM "Scope refinement" governs the scope below).

This module IMPORTS `R3.AxiomaticClosure` (justified — it *produces* `AubinLionsPackage_R3`
and *consumes* `GalerkinSolutionData_R3`, both of which live in `AxiomaticClosure.lean` with
no lighter exposing module). This is the single heavy import; unlike P3 (`R3.SpatialCompactness`,
deliberately standalone) it is unavoidable here. It also reuses P3
(`localCompactness_R3_of_ballCompact`, `LocalRellichInput`) and R3-d's `b`-bound analytic core
(via `F.b_bound` in `R3.TrilinearEstimate`'s downstream `R3NSForms`).

**Refined scope (ADDENDUM — supersedes §3 Tier P / §9 where they conflict):** P2 targets the
**Aubin–Lions reduction** (spatial+time ⇒ package) plus **two reusable analytic lemmas**,
conditional only on the single isolated frontier hypothesis `TimeCompactnessInput` (the honest
uniform-in-`n` L² time modulus that mathlib's absent `W^{1,p}(0,T;X)` / vector-valued weak time
derivative / Aubin–Lions theory would supply). This is an **HONEST PARTIAL milestone**: part of
the deliverables are proved axiom-free, two are still open (`sorry` with truthful TODOs).

**PROVED, axiom-free (no `sorryAx`):**

* `spatialInput_R3_of_localRellich` (S1) — the `spatial` half, discharged by reusing P3.
* `bForm_tendsto_of_strongL2` (N1) — nonlinear `b`-term passage under strong L² (the R3-d payoff).
* private Steklov building blocks for the (still-open) C2 reduction:
  `galerkin_curve_continuous`, `steklovAvg` (def), `steklovAvg_norm_le_u0` (uniform L² bound),
  `steklovAvg_approx` (time-modulus average↔curve estimate), and `galerkin_norm_le_u0`.

**OPEN / PARTIAL (currently `sorry` with truthful TODO — NOT impossible, NOT unsound):**

* `kineticEnergy_lsc_bound` (E1, ~line 256) — the blocker (time-measurability of the package's
  limit `u`) is now supplied by the new `u_aestronglyMeasurable` field added in #14-C; the
  provable core uniform bound `hgal` is discharged via `galerkin_norm_le_u0`. Discharge of the
  full body is #14-P (lean-prover target). See the in-body TODO.
* `aubinLionsPackage_R3_of_timeCompactness` (C2, ~line 417) — the centerpiece Aubin–Lions
  assembly via the viable Steklov interval-averaging route. The building blocks above are proved;
  the REMAINING work is an OPEN ENGINEERING target: δ-mesh diagonalization + H¹/Jensen bound on
  the interval average + Bochner-average measurability. See the in-body TODO.

**Documented residual frontier (NOT reconstructed here, axioms retained):** the limit-passage
conclusions (b) `WeakFormNS`, (d) initial trace, and (e) energy class require the absent
vector-valued weak time-derivative / `W^{1,p}(0,T;X)` theory. Bundling them into a
`GoodRepresentativeInput` hypothesis would re-assert the conclusions (smuggling), so per the
ADDENDUM we DROP that and `galerkinLimitPassage_R3_of_goodRep`. P2 does NOT claim to produce the
full `galerkin_limit_passage_R3` conclusion (this mirrors R3-d, which proved `b`-form lemmas
without producing `Nonempty R3NSForms`).

**Zero new `axiom`/`opaque`/`constant`.** Honest isolated hypotheses: `TimeCompactnessInput` is an
explicit *argument* (not an axiom) — the intended time-frontier feeding the still-open C2 reduction,
exactly as P3's `LocalRellichInput`, R3-d's `hdiv`, P5's `SchwartzGalerkinBasis.dense_span`. It is
NOT the only non-proved item: E1 and C2 remain open `sorry`s as described above.

Target axioms this milestone partially substantiates (NOT removed):
`aubin_lions_R3` (`AxiomaticClosure.lean:444–460`, package `406–428`).
-/

-- Import-cycle audit (REQUIRED — Hard rule 10). Verified against the actual import lines:
--   * `R3.AxiomaticClosure` imports ONLY `EvolutionTriple`, `R3.Regularity`, and a mathlib
--     interval-integral module — it does NOT import this file, `R3.SpatialCompactness`, or
--     `R3.TrilinearEstimate`. So importing it here is acyclic.
--   * `R3.SpatialCompactness` imports `R3.Regularity` + mathlib (standalone); `R3.TrilinearEstimate`
--     imports `R3.DivergenceFree` + mathlib (leaf). Importing both here adds no cycle.
--   * This file is a LEAF (nothing imports it). It is the unique place that may reference
--     `AubinLionsPackage_R3` AND reuse P3 — neither of those modules can reference the other.
import LerayHopf.R3.AxiomaticClosure     -- AubinLionsPackage_R3, GalerkinSolutionData_R3, r3Evolution, R3NSForms
import LerayHopf.R3.SpatialCompactness   -- localCompactness_R3_of_ballCompact, LocalRellichInput
import LerayHopf.R3.TrilinearEstimate    -- b-bound analytic core (downstream of R3NSForms.b_bound)
import Mathlib.MeasureTheory.Integral.Bochner.Set   -- set/interval integrals over balls

namespace LerayHopf

open MeasureTheory Filter Topology Metric

/-! ### Tier H — the isolated time-frontier hypothesis (for the still-open C2) -/

/-- Isolated analytic frontier: UNIFORM time-equicontinuity in L² of the Galerkin curves.

For every error `ε > 0`, there is a shift bound `δ > 0` such that, uniformly in `n` and in
`s, t ∈ [0,T]` with `|s - t| < δ`, the L² distance of the Galerkin states is `< ε`:
    `‖(galSeq n).u s - (galSeq n).u t‖_{L²(ℝ³)} < ε`.

This is the L²-modulus content of the Bochner–Sobolev bound `‖uₙ‖_{W^{1,?}(0,T;X)} ≤ C`,
which is derivable IN PRINCIPLE from `GalerkinSolutionData_R3.u_hasDeriv` + the energy/
regularity bounds, but whose vector-valued-Sobolev packaging mathlib LACKS (no
`W^{1,p}(0,T;X)`, no weak time derivative, no Aubin–Lions lemma).

Honesty (no-smuggle): this field speaks ONLY about the GIVEN Galerkin sequence's
self-equicontinuity in time; it supplies NEITHER a subsequence, NOR a limit, NOR any
space-time convergence, NOR any spatial compactness (that is P3's job). It is a uniform
modulus of continuity, nothing more. -/
structure TimeCompactnessInput (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν T : ℝ) (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n) where
  /-- Uniform-in-`n` L² modulus of time continuity of the Galerkin curves on `[0,T]`. -/
  uniform_time_modulus : ∀ ε : ℝ, 0 < ε →
    ∃ δ : ℝ, 0 < δ ∧ ∀ (n : ℕ) (s t : Time),
      s ∈ Set.Icc (0 : ℝ) T → t ∈ Set.Icc (0 : ℝ) T → |s - t| < δ →
      ‖((galSeq n).u s : L2VF_R3) - ((galSeq n).u t : L2VF_R3)‖ < ε

/-! ### Tier S — discharge the spatial input via P3 -/

/-- The `spatial` hypothesis required by the Aubin–Lions combination is exactly P3's
`localCompactness_R3_of_ballCompact`. Supplying P3's isolated input discharges it.

This type is the `aubin_lions_R3` `spatial` binder verbatim (`AxiomaticClosure.lean:449–459`). -/
theorem spatialInput_R3_of_localRellich (B : LocalRellichInput) :
    ∀ (M : ℝ) (z : ℕ → L2VF_R3),
      (∀ n, z n ∈ L2Sigma_R3) → (∀ n, memH1VF_R3 (z n)) →
      (∀ n, ‖z n‖ ≤ M) → (∀ n, viscousFormSq_R3 1 (z n) ≤ M ^ 2) →
      ∃ (ψ : ℕ → ℕ) (g : L2VF_R3), StrictMono ψ ∧ g ∈ L2Sigma_R3 ∧
        ∀ R : ℝ, Filter.Tendsto
          (fun n => ∫ x in Metric.closedBall (0 : Domain3) R,
            ‖((z (ψ n)) x : EuclideanSpace ℝ (Fin 3)) - (g x : EuclideanSpace ℝ (Fin 3))‖ ^ 2
            ∂(volume : Measure Domain3))
          Filter.atTop (nhds 0) := by
  -- Reuse of P3's local Rellich compactness; the type is the `aubin_lions_R3` `spatial`
  -- binder verbatim, so this gives the combination lemma a clean spatial argument.
  exact localCompactness_R3_of_ballCompact B

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

/-! ### Tier E — energy inequality (the reachable kinetic-lsc half of conclusion (c)) -/

/-- **Galerkin-side uniform energy bound (provable core of E1).** For every `n` and every
`t ≥ 0`, the Galerkin state is L²-bounded by the initial datum: `‖(galSeq n).u t‖ ≤ ‖u₀‖`.

Proof: `energy_bound` gives `½‖uₙ t‖² ≤ ½‖𝔊.P n u₀‖²`; `𝔊.norm_le` gives
`‖𝔊.P n u₀‖ ≤ ‖u₀‖`; combine. This is the side of E1 that needs no time-measurability. -/
private theorem galerkin_norm_le_u0 (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
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
  -- The remaining step — transferring `hgal` to the LIMIT `alPkg.u` at a.e. time — is the
  -- genuine blocker, and it is IRREDUCIBLE FROM THE PACKAGE ALONE for a precise, structural
  -- reason (verified from several angles, not a giving-up):
  --
  --   The norm-lsc transfer needs, for a.e. `t` and each ball radius `k`, an extraction
  --   `restrictToBall k ((galSeq (φ m)).u t) → restrictToBall k (alPkg.u t)` in `L²(B_k)`,
  --   obtained from `∫₀ᵀ (∫_{B_k} ‖(galSeq (φ n)).u t − alPkg.u t‖²) dt → 0` by extracting an
  --   a.e.-`t` subsequence of the INNER integral `g_n(t) := ∫_{B_k} ‖(galSeq (φ n)).u t − …‖²`.
  --   That a.e.-`t` extraction (`TendstoInMeasure.exists_seq_tendsto_ae` /
  --   `tendstoInMeasure_of_tendsto_eLpNorm`) REQUIRES `g_n` to be (a.e.-strongly) MEASURABLE in
  --   `t`, equivalently joint `(t,x)`-measurability of the integrand, equivalently time-
  --   measurability of `alPkg.u`.
  --
  --   **UPDATE (#14-C):** `AubinLionsPackage_R3` NOW carries the `u_aestronglyMeasurable` field
  --   (`AEStronglyMeasurable (fun t => (alPkg.u t : L2VF_R3)) ...`), added as the green-lit #14-C
  --   struct field. This is the minimal time-regularity field that unblocks the a.e.-`t` extraction:
  --   `alPkg.u_aestronglyMeasurable` gives measurability of `t ↦ alPkg.u t`, so
  --   `TendstoInMeasure.exists_seq_tendsto_ae` can now be applied to `g_n(t) = ∫_{B_k} ‖…‖²`.
  --
  -- TODO(E1, minimal): a.e.-`t` kinetic-lsc transfer of `hgal` to `alPkg.u`. The ONLY missing
  -- step is wiring `alPkg.u_aestronglyMeasurable` into the `TendstoInMeasure.exists_seq_tendsto_ae`
  -- + per-`t` ball-exhaustion norm-lsc argument. With the new field supplied, this is an
  -- engineering discharge target for lean-prover (#14-P). Dischargeable via D2 primitive
  -- `aeStronglyMeasurable_of_spaceTimeL2` (Bochner/TimeSobolev.lean).
  sorry -- ALLOW_SORRY: P2 lean-prover target (E1) — minimal residual: `alPkg.u_aestronglyMeasurable` (#14-C field) now supplies the needed handle; discharge path = TendstoInMeasure.exists_seq_tendsto_ae + per-t ball-exhaustion norm-lsc; provable core `hgal` discharged via galerkin_norm_le_u0

/-! ### Tier C-prep — Steklov interval-average building blocks for the Aubin–Lions route

These `private` helpers are the genuine, axiom-free sub-lemmas of the Steklov
interval-averaging route to C2 (the real Aubin–Lions argument). They are proved here
independently of the final assembly so that the route's reusable pieces are landed even
while the full space-time diagonalization remains open (see the C2 TODO). -/

/-- The Galerkin velocity curve `t ↦ ((galSeq n).u t : L2VF_R3)` is continuous on **forward**
time `Set.Ici 0` (it is even differentiable there by `u_hasDeriv`).

Forward-only: `u_hasDeriv` now guarantees differentiability only for `t ≥ 0` (the curve is a
physical Galerkin solution, confined only on forward time).  Everything downstream uses the
curve only on `[0,T] ⊆ Ici 0`, so forward continuity suffices. -/
private theorem galerkin_curve_continuous (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (u₀ : L2Sigma_R3) (n : ℕ)
    (gs : GalerkinSolutionData_R3 𝔊 F ν u₀ n) :
    ContinuousOn (fun s => (gs.u s : L2VF_R3)) (Set.Ici 0) :=
  fun t ht => (gs.u_hasDeriv t ht).continuousAt.continuousWithinAt

/-- **Steklov interval-average of a Galerkin curve.** For mesh `δ` and base time `t`,
`steklovAvg gs δ t := δ⁻¹ • ∫_{t}^{t+δ} (gs.u s : L2VF_R3) ds` (Bochner interval integral
in `L2VF_R3`). For `δ > 0` this is the average of the curve over `[t, t+δ]`. -/
private noncomputable def steklovAvg (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (u₀ : L2Sigma_R3) (n : ℕ)
    (gs : GalerkinSolutionData_R3 𝔊 F ν u₀ n) (δ t : ℝ) : L2VF_R3 :=
  δ⁻¹ • ∫ s in t..(t + δ), (gs.u s : L2VF_R3)

/-- **L² uniform bound on the Steklov average.** For `0 < δ` and `0 ≤ t`, the averaged
state is bounded by `‖u₀‖`, uniformly in `n` and `t`.  This is the average of a curve all
of whose values satisfy `‖(gs.u s)‖ ≤ ‖u₀‖` (via `galerkin_norm_le_u0`). -/
private theorem steklovAvg_norm_le_u0 (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (u₀ : L2Sigma_R3) (n : ℕ)
    (gs : GalerkinSolutionData_R3 𝔊 F ν u₀ n) {δ t : ℝ} (hδ : 0 < δ) (ht : 0 ≤ t) :
    ‖steklovAvg 𝔊 F ν u₀ n gs δ t‖ ≤ ‖(u₀ : L2VF_R3)‖ := by
  -- Bound the integral by `δ · ‖u₀‖` using the pointwise norm bound, then divide by δ.
  have hle : t ≤ t + δ := by linarith
  -- pointwise bound on `Ι t (t+δ)`: every `s` there is `≥ t ≥ 0`, so `galerkin_norm_le_u0`.
  have hbd : ‖∫ s in t..(t + δ), (gs.u s : L2VF_R3)‖ ≤ ‖(u₀ : L2VF_R3)‖ * δ := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := t) (b := t + δ) (C := ‖(u₀ : L2VF_R3)‖)
      (f := fun s => (gs.u s : L2VF_R3)) ?_
    · -- `|(t+δ) - t| = δ`
      have hsub : |(t + δ) - t| = δ := by rw [show (t + δ) - t = δ by ring, abs_of_pos hδ]
      rwa [hsub] at this
    · intro s hs
      -- `s ∈ Ι t (t+δ)` ⊆ `[t, t+δ]`, so `s ≥ t ≥ 0`.
      have hs' : s ∈ Set.uIoc t (t + δ) := hs
      rw [Set.uIoc_of_le hle] at hs'
      exact galerkin_norm_le_u0 𝔊 F ν u₀ n gs (le_trans ht (le_of_lt hs'.1))
  -- combine
  rw [steklovAvg, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hδ]
  rw [inv_mul_le_iff₀ hδ]
  calc ‖∫ s in t..(t + δ), (gs.u s : L2VF_R3)‖
      ≤ ‖(u₀ : L2VF_R3)‖ * δ := hbd
    _ = δ * ‖(u₀ : L2VF_R3)‖ := mul_comm _ _

/-- **Steklov average approximates the original curve.** If, on the window
`[t, t+δ]`, the curve varies by less than `ε` in L², then
`‖(gs.u t) − steklovAvg δ t‖ ≤ ε`.  This is the key step-3 estimate of the Steklov route.

The window-variation hypothesis `hmod` is the *intended consumer* of
`Htime.uniform_time_modulus`, but ONLY when the whole window stays in `[0,T]`: that modulus
controls pairs with both times in `[0,T]`, so it supplies `hmod` uniformly in `n,t` exactly for
`t, t+δ ∈ [0,T]` (i.e. `t ≤ T-δ`). For `t` in the boundary strip `(T-δ, T]` the forward window
exits `[0,T]` and the modulus does NOT supply `hmod`; that strip needs separate handling (see the
C2 route TODO). This lemma itself only requires `hmod` on `uIoc t (t+δ)` and is agnostic to its
source. -/
private theorem steklovAvg_approx (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (u₀ : L2Sigma_R3) (n : ℕ)
    (gs : GalerkinSolutionData_R3 𝔊 F ν u₀ n) {δ t ε : ℝ} (hδ : 0 < δ) (ht : 0 ≤ t)
    (hmod : ∀ s ∈ Set.uIoc t (t + δ), ‖(gs.u t : L2VF_R3) - (gs.u s : L2VF_R3)‖ ≤ ε) :
    ‖(gs.u t : L2VF_R3) - steklovAvg 𝔊 F ν u₀ n gs δ t‖ ≤ ε := by
  have hle : t ≤ t + δ := by linarith
  -- forward continuity of the curve on `Ici 0` ⊇ the window `[t, t+δ]` (since `0 ≤ t`)
  have hcont : ContinuousOn (fun s => (gs.u s : L2VF_R3)) (Set.Ici 0) :=
    galerkin_curve_continuous 𝔊 F ν u₀ n gs
  have hwin : Set.uIcc t (t + δ) ⊆ Set.Ici (0 : ℝ) := by
    rw [Set.uIcc_of_le hle]
    intro s hs; exact le_trans ht hs.1
  have hint : IntervalIntegrable (fun s => (gs.u s : L2VF_R3)) volume t (t + δ) :=
    (hcont.mono hwin).intervalIntegrable
  -- write `gs.u t = δ⁻¹ • ∫ (gs.u t)` (constant integral), then subtract under the integral.
  have hconst : (gs.u t : L2VF_R3) = δ⁻¹ • ∫ _s in t..(t + δ), (gs.u t : L2VF_R3) := by
    rw [intervalIntegral.integral_const, smul_smul]
    rw [show (t + δ) - t = δ by ring, inv_mul_cancel₀ (ne_of_gt hδ), one_smul]
  rw [hconst, steklovAvg, ← smul_sub,
    ← intervalIntegral.integral_sub (intervalIntegrable_const) hint]
  rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hδ, inv_mul_le_iff₀ hδ]
  calc ‖∫ s in t..(t + δ), ((gs.u t : L2VF_R3) - (gs.u s : L2VF_R3))‖
      ≤ ε * |(t + δ) - t| := by
        refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
        intro s hs; exact hmod s hs
    _ = ε * δ := by rw [show (t + δ) - t = δ by ring, abs_of_pos hδ]
    _ = δ * ε := by ring

/-! ### Tier C — combination: spatial + time ⇒ `AubinLionsPackage_R3` (the centerpiece) -/

/-- **Aubin–Lions package on ℝ³ from the isolated time-compactness input (OPEN — `sorry`).**

TARGET/INTENT: produce `aubin_lions_R3`'s conclusion (`AubinLionsPackage_R3`) axiom-free,
conditional on (i) P3's local spatial compactness (via `LocalRellichInput`) and (ii) the isolated
uniform time-equicontinuity `TimeCompactnessInput`. The conclusion type is exactly
`AubinLionsPackage_R3 𝔊 F ν T u₀ galSeq` (matching the `aubin_lions_R3` binder list,
`AxiomaticClosure.lean:444–460`).

CURRENT STATUS: this is NOT yet substantiated — the body is `sorry` (C2). The Steklov
interval-averaging route is viable and its reusable helpers (`steklovAvg`, `steklovAvg_norm_le_u0`,
`steklovAvg_approx`, `galerkin_curve_continuous`) are proved axiom-free; the final assembly
(H¹/Jensen bound on the average + Bochner-average measurability + δ-mesh diagonalization) is the
OPEN engineering TODO below. The statement/hypotheses are kept intact (Hard rule 8).

This is a `noncomputable def` (not a `theorem`) because `AubinLionsPackage_R3` is a `Type`
(a data-carrying structure), not a `Prop` — mirroring the `aubin_lions_R3` axiom shape. -/
noncomputable def aubinLionsPackage_R3_of_timeCompactness
    (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T)
    (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n)
    (B : LocalRellichInput)
    (Htime : TimeCompactnessInput 𝔊 F ν T u₀ galSeq) :
    AubinLionsPackage_R3 𝔊 F ν T u₀ galSeq := by
  -- Proof sketch: assemble the `strong_convergence` field (local space-time L²(0,T;L²(B_R)) on
  -- every ball) by:
  --   1. apply `spatialInput_R3_of_localRellich B` to extract, at a dense set of sample times, a
  --      common subsequence `φ` with ball-restricted spatial convergence (diagonal-over-balls is
  --      already inside P3);
  --   2. use `Htime.uniform_time_modulus` to upgrade convergence at sample times to space-time
  --      L²(0,T;L²(B_R)) convergence (equicontinuity-in-time ⇒ the time-integral of the spatial
  --      error is controlled by the sample-time error + the modulus) — the Arzelà–Ascoli-in-time
  --      ε/3 step (NOT mathlib's abstract `ArzelaAscoli.*`; prove directly via a `δ`-mesh, gating
  --      note G2);
  --   3. package `φ`, the limit curve `u`, and the `strong_convergence` `Tendsto`.
  --
  -- PROVABLE CORE (no missing pillar): the uniform, POINTWISE-in-`t` L² bound
  -- `‖(galSeq n).u t‖ ≤ ‖u₀‖` (all `n`, `t ≥ 0`) is available via `galerkin_norm_le_u0`.
  have _hL2bound : ∀ (n : ℕ) {t : ℝ}, 0 ≤ t →
      ‖((galSeq n).u t : L2VF_R3)‖ ≤ ‖(u₀ : L2VF_R3)‖ :=
    fun n {t} ht => galerkin_norm_le_u0 𝔊 F ν u₀ n (galSeq n) ht
  -- WHICH ROUTE IS CORRECT (Codex xhigh adjudication): the *pointwise-sample* shortcut — pick a
  -- common sample time `tₖ`, hope for an `n`-uniform pointwise H¹ bound
  -- `viscousFormSq_R3 1 ((galSeq n).u tₖ) ≤ M²` and apply P3 to the raw states — does NOT work:
  -- the data only gives the TIME-INTEGRATED `reg_bound T`
  -- (`∫₀ᵀ viscousFormSq_R3 ν ((galSeq n).u t) dt ≤ C`, `C` `n`-independent), and by Markov the
  -- per-`n` bad sets `{t : viscous_n t > M²}` move with `n`, so no single dense/positive-measure
  -- sample set carries an `n`-uniform pointwise H¹ bound. That observation rules out ONLY the
  -- pointwise-sample shortcut; it does NOT make C2 mathematically impossible.
  --
  -- THE VIABLE ROUTE (Codex xhigh: the Steklov interval-averaging argument IS the right one and is
  -- viable here): replace pointwise samples by interval averages `steklovAvg gs δ t` (defined and
  -- analyzed above). Concretely:
  --   1. Control the raw curves by their interval averages via the time modulus:
  --      `‖(gs.u t) − steklovAvg gs δ t‖ ≤ ε` (`steklovAvg_approx`, fed by
  --      `Htime.uniform_time_modulus`); the averages are also `‖·‖ ≤ ‖u₀‖` uniformly
  --      (`steklovAvg_norm_le_u0`).
  --      BOUNDARY CAVEAT (not yet handled — see TODO below): `steklovAvg_approx` needs the modulus
  --      on the whole window `[t, t+δ]`, but `Htime.uniform_time_modulus` only controls pairs with
  --      BOTH times in `[0,T]`. So this forward-average control is uniform in `n,t` ONLY for
  --      `t ≤ T-δ`, where `[t, t+δ] ⊆ [0,T]`. For `t` in the boundary strip `(T-δ, T]` the forward
  --      window exits `[0,T]` and the hypothesis gives nothing; that strip needs SEPARATE handling
  --      (e.g. a direct boundary-strip estimate, or clipped/backward Steklov averages over
  --      `[t-δ, t]` whose windows stay inside `[0,T]`). This is part of the open assembly below,
  --      not a solved point.
  --   2. Bound the averages' H¹ seminorm by JENSEN from the INTEGRATED `reg_bound`:
  --      `viscousFormSq_R3 1 (steklovAvg gs δ t) ≤ δ⁻¹ ∫_{t}^{t+δ} viscousFormSq_R3 1 (gs.u s) ds`,
  --      which is finite and `n`-UNIFORM on each fixed δ-window — so the averaged states DO carry
  --      the `n`-uniform pointwise H¹ bound P3 needs (this is what the raw pointwise samples lacked).
  --   3. Apply P3 (`spatialInput_R3_of_localRellich B`) to the averaged states at the (finitely
  --      many, per δ-mesh) window base-points to extract a common ball-restricted spatial limit.
  --   4. Diagonalize over a refining δ-mesh (δ → 0): step 1 makes the average→raw error vanish,
  --      step 3 gives spatial convergence of the averages, and the outer interval-integral
  --      `∫₀ᵀ ∫_{B_R} ‖uₙ − u‖² → 0` follows by the ε/3 split (raw↔avg, avg-spatial, mesh).
  --
  -- STATUS: the reusable building blocks of this route are PROVED above and axiom-free —
  -- `galerkin_curve_continuous`, `steklovAvg` (def), `steklovAvg_norm_le_u0` (uniform L² bound),
  -- and `steklovAvg_approx` (time-modulus average↔curve estimate). What REMAINS is an OPEN
  -- ENGINEERING assembly, not a mathematical impossibility:
  --   • the H¹/Jensen bound on the average (step 2): `viscousFormSq_R3 1 (steklovAvg …) ≤
  --     δ⁻¹ ∫ viscousFormSq_R3 1 (gs.u s)` — Jensen for the convex viscous form under the Bochner
  --     average (needs the Bochner-average ↔ pointwise-form interchange);
  --   • Bochner-average measurability / joint `(t,x)`-measurability of the assembled limit for the
  --     outer interval-integral passage (step 4);
  --   • the BOUNDARY STRIP `(T-δ, T]` (step 1): the forward window `[t, t+δ]` leaves `[0,T]` there,
  --     so `Htime.uniform_time_modulus` (both times in `[0,T]`) does not feed `steklovAvg_approx`;
  --     handle it by a separate boundary-strip estimate or by clipped/backward averages over
  --     `[t-δ, t] ⊆ [0,T]`;
  --   • the full space-time δ-mesh diagonalization wiring (steps 3–4).
  -- TODO(C2): complete the Steklov interval-averaging Aubin–Lions assembly (steps 2–4 above) into
  -- the `AubinLionsPackage_R3` `strong_convergence` field. This is reachable from `galSeq` + `Htime`
  -- + P3 via the proved Steklov helpers; it is an engineering target, NOT blocked by a missing
  -- mathlib pillar. Statement/hypotheses kept intact (Hard rule 8); deferred this cycle.
  --
  -- TODO(E1-scaffold): the new `u_aestronglyMeasurable` field (added in #14-C) is also covered
  -- by this sorry. Its discharge path: use `aeStronglyMeasurable_of_spaceTimeL2` (the D2
  -- primitive in `Bochner/TimeSobolev.lean`) applied to the Steklov-assembled limit curve once
  -- C2 is resolved. See `#14-P` (#14-P E1 measurability target).
  sorry -- ALLOW_SORRY: #14-P E1 measurability + C2 centerpiece — this sorry covers: (1) `u_aestronglyMeasurable` (new #14-C field): discharged via D2 primitive aeStronglyMeasurable_of_spaceTimeL2 once C2 is resolved; (2) `strong_convergence` (C2): Steklov interval-averaging route viable, helpers proved, remaining = H¹ Jensen bound + Bochner-avg measurability + δ-mesh diagonalization

end LerayHopf
