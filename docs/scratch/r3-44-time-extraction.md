# Task Contract: Issue #44 — Prove `galerkinSpaceTimeExtraction_R3`

**Branch:** `lane-r3-44`  
**File to edit:** `LerayHopf/R3/AubinLionsLimitPassage.lean`  
**Planner:** lean-planner (2026-06-22)  
**Goal:** Replace the single remaining R3 time-compactness axiom
`galerkinSpaceTimeExtraction_R3` (line ~1390) with a proof, producing a sorry-free
and axiom-free (modulo kernel axioms) R3 Aubin–Lions chain.

---

## 1  Source-of-truth cross-references

- Target axiom full signature: `AubinLionsLimitPassage.lean` lines 1390–1402.
- Axiom doc-comment (the authoritative mathematical description): lines 1348–1389.
- Already-proved atoms in the same file (axiom-free):
  - `steklovAvg_spatial_extraction` (~line 1301): per-sample-time LOCAL spatial extraction
    from `LocalRellichInput`.
  - `galerkin_curves_equicontinuous` (~line 1339): thin wrapper over
    `TimeCompactnessInput.uniform_time_modulus` — CONDITIONAL on `TimeCompactnessInput`.
  - `galerkin_norm_le_u0` (~line 226): uniform-in-n L²-bound `‖uₙ(t)‖ ≤ ‖u₀‖` for `t ≥ 0`.
  - `galerkin_curve_continuous` (~line 246): `ContinuousOn (fun s => (gs.u s : L2VF_R3)) (Ici 0)`.
  - `restrictToBall` (`SpatialCompactness.lean:78`): 1-Lipschitz restriction to `L2ballR3 R`.
  - `continuous_restrictToBall`: continuity of `restrictToBall R` (used in `aubinLionsPackage_R3_of_timeCompactness`).
- `GalerkinSolutionData_R3` fields used:
  - `u_hasDeriv t ht`: `HasDerivAt (fun s => (u s : L2VF_R3)) (deriv ...) t` for `0 ≤ t`.
  - `u_ode t ht w hw`: ODE identity — RHS = `ν * stokesTestPairing_R3 (u t) w + F.b (u t) (u t) w`.
  - `energy_bound t ht`: `½‖u t‖² ≤ ½‖P_n u₀‖²`.
  - `reg_bound T hT`: `∫₀ᵀ viscousFormSq_R3 ν (u t) dt ≤ ½‖u₀‖²`.
- Plan reference: `docs/leray_hopf_lean_mvp_plan.md` Milestone 8 (Aubin–Lions axiom removal).

---

## 2  Mathematical analysis of the proof skeleton

### Sub-lemma 1: Equicontinuity-from-ODE (unconditional)

**Claim:** Given `galSeq` with `GalerkinSolutionData_R3`, there exist `C : ℝ` and `ω : ℝ → ℝ`
with `ω δ → 0` as `δ → 0` such that for all `n`, `s, t ∈ [0,T]`,
`‖(galSeq n).u s - (galSeq n).u t‖ ≤ ω(|s-t|)`, with `C` depending only on `ν`, `u₀`, `T`.

**Proof route (Bochner FTC):**

From `u_hasDeriv`, the Galerkin curve is differentiable at all `t ≥ 0`, so by
`intervalIntegral.integral_eq_sub_of_hasDerivAt` (Mathlib: `Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus`) we get:

```
(u n s : L2VF_R3) - (u n t : L2VF_R3) = ∫ r in t..s, deriv (fun r => (u n r : L2VF_R3)) r dr
```

Then `‖u n s - u n t‖ ≤ ∫_{t}^{s} ‖u'_n(r)‖ dr` by `intervalIntegral.norm_integral_le_integral_norm`.

**The key gap:** We need `‖u'_n(r)‖` to be bounded uniformly in `n`. From `u_ode`:

```
inner (u'_n r) w + ν * stokesTestPairing_R3 (u_n r) w + F.b (u_n r) (u_n r) w = 0
```

for all `w ∈ Vₙ` with `P n w = w`. So `u'_n(r) = -ν * A u_n(r) - B(u_n(r), u_n(r))` in `Vₙ*`,
where `A` is the Stokes operator and `B` is the convection term.

To bound `‖u'_n(r)‖_{L²}`, the inner-product identity gives:
`‖u'_n r‖ ≤ ν * ‖A u_n r‖_{V*} + ‖B(u_n r, u_n r)‖_{V*}`

**Critical Mathlib survey:**

- `stokesTestPairing_R3 u w ≤ C * ‖u‖_{H¹} * ‖w‖`: The Stokes pairing is bilinear and bounded.
  The H¹-norm of `u_n r` is controlled by `viscousFormSq_R3 1 (u_n r) ≤ ...` but integrating
  the H¹-bound over `[0,T]` gives an `L²`-in-time bound, not a pointwise bound.

**The actual obstruction:** On a finite-dimensional subspace `Vₙ`, the `L²`-norm and `H¹`-norm
are equivalent (all norms equivalent on finite-dimensional spaces), so `‖u'_n(r)‖` IS bounded
uniformly on `[0,T]` for fixed `n`. But the bound depends on `n` through the norm-equivalence
constant of `Vₙ`. We need an `n`-UNIFORM bound.

An `n`-uniform bound on `‖u'_n(r)‖` in `L²` follows from the ODE if we have a bound of the form
`‖u'_n(r)‖ ≤ C(‖u_n(r)‖, ‖viscousFormSq(u_n(r))‖)` with `C` independent of `n`. Specifically:

- `‖ν A u_n(r)‖_{V*} ≤ C * sqrt(viscousFormSq_R3 ν (u_n r))` — bounded by the H¹-seminorm.
  This is the `V* norm = H^{-1}` estimate: `|⟨Au,w⟩| = |stokesTestPairing(u,w)| ≤ ‖u‖_{H¹} * ‖w‖_{H¹}`,
  so `‖Au‖_{V*} ≤ ‖u‖_{H¹}`. Hence `∫‖Au_n‖_{V*} ≤ (∫ viscousFormSq)^{1/2} * T^{1/2}` by Cauchy–Schwarz.

- `‖B(u_n, u_n)‖_{V*}`: From `u_ode`, `B(u_n, u_n)` acts on test vectors in `Vₙ`. For the
  trilinear form `F.b`, a quantitative bound `|F.b(u,u,w)| ≤ C ‖u‖_{H¹} * ‖u‖ * ‖w‖` would
  give `‖B(u_n, u_n)‖_{V*} ≤ C ‖u_n‖_{H¹} * ‖u_n‖`. But `R3NSForms` does NOT expose a
  pointwise bound `b_bound` — it gives only the Schwartz decay form. The `ConvectionGap`
  design shows `b_cont_fixedTest` is the available handle, which is bilinear in the first two
  slots at fixed Schwartz `w`. This does NOT give a pointwise-in-t dual norm bound for general `w ∈ Vₙ`.

**Conclusion for Sub-lemma 1:** A CLEAN, n-uniform, pointwise-in-t Hölder bound
`‖u_n(s) - u_n(t)‖ ≤ C * |s-t|^{1/2}` following purely from the available fields in
`GalerkinSolutionData_R3` and `R3NSForms` is NOT derivable without additional bounds on
`‖B(u_n, u_n)‖_{V*}` that are not present in the current axiomatic interface.

The `reg_bound` field gives `∫₀ᵀ viscousFormSq_R3 ν (u_n t) dt ≤ ½‖u₀‖²` (L²-in-time H¹ bound),
which via Cauchy–Schwarz controls `∫‖Au_n‖_{V*} dt`. But for `B(u_n, u_n)` we need a quantitative
pointwise H¹ → L∞ embedding (Sobolev) or an explicit trilinear bound with H¹-norm — the abstract
`R3NSForms.b` does not carry this.

**Verdict for Sub-lemma 1:** This is the single irreducible abstract primitive. The equicontinuity
from the ODE is mathematically true but requires:
(a) a bound `|F.b(u, u, w)| ≤ C * ‖u‖_{H¹}² * ‖w‖` (the 3D Sobolev trilinear estimate
    with BOTH first factors in H¹), and
(b) the dual-norm identity `‖u'_n‖ = sup_{‖w‖≤1} |⟨u'_n, w⟩|` for `w` ranging over `Vₙ`,

neither of which is currently part of `GalerkinSolutionData_R3` or `R3NSForms`.

The THINNEST residual axiom that would close this is:

```lean
-- The uniform equicontinuity modulus of the Galerkin curves,
-- stated in terms of available data (energy bound + reg_bound), SCHEME-INDEPENDENT.
axiom galerkin_equicontinuity_from_ODE
    (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T) (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ (n : ℕ) (s t : ℝ),
      s ∈ Set.Icc (0 : ℝ) T → t ∈ Set.Icc (0 : ℝ) T → |s - t| < δ →
      ‖((galSeq n).u s : L2VF_R3) - ((galSeq n).u t : L2VF_R3)‖ < ε
```

This is STRICTLY THINNER than `galerkinSpaceTimeExtraction_R3` (it gives only the
equicontinuity modulus, not the diagonalized subsequence + measurable limit + a.e. convergence).
It is SCHEME-INDEPENDENT (depends only on `GalerkinSolutionData_R3` fields) and REUSABLE for
the torus #23 if the torus `GalerkinSolutionData` carries analogous fields.

### Sub-lemma 2: Per-ball Arzelà–Ascoli (finite-time, fixed radius R)

**Claim:** Fix `R > 0`. Given:
- uniform equicontinuity: `∀ n s t`, `s,t ∈ [0,T]`, `|s-t| < δ → ‖u_n(s) - u_n(t)‖ < ε`
  (from Sub-lemma 1),
- pointwise precompactness: for each dense set of times `{t_k}`, the set
  `{restrictToBall R (u_n t_k) | n : ℕ}` is precompact in `L2ballR3 R` (from `LocalRellichInput`
  via `steklovAvg_spatial_extraction` applied at each `t_k`),

then there exists a strictly-monotone `φ_R : ℕ → ℕ` and a continuous `f_R : [0,T] → L2ballR3 R`
such that `restrictToBall R ((galSeq (φ_R n)).u t) → f_R t` uniformly in `t ∈ [0,T]`.

**Mathlib route:**

The relevant Mathlib result is `BoundedContinuousFunction.arzela_ascoli` (and variants
`arzela_ascoli₁`, `arzela_ascoli₂`) in
`Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli`. These work for:
- compact domain (here `[0,T]` ✓, after rescaling),
- equicontinuous family of functions into a pseudometric space (need the modulus ✓),
- relatively compact range at each point (pointwise precompactness ✓ from spatial extraction).

**Assessment:** `arzela_ascoli₂` applies: it gives `IsCompact (closure A)` for the set `A` of
functions. From `IsCompact` in the first-countable metric space `(α →ᵇ L2ballR3 R)`, applying
`IsCompact.isSeqCompact` → `IsSeqCompact.subseq_of_frequently_in` extracts the subsequence.

**Gap:** The equicontinuity must be stated in the form `Equicontinuous ((↑) : A → α → β)` for
the bounded-continuous-function type. The Mathlib bridge is
`Metric.equicontinuous_of_continuity_modulus` which takes a global modulus and produces
`Equicontinuous`. This fits exactly if Sub-lemma 1 is available.

**Classification: [Mathlib-provable]** — `BoundedContinuousFunction.arzela_ascoli₂` +
`IsCompact.isSeqCompact` + `IsSeqCompact.subseq_of_frequently_in` +
`Metric.equicontinuous_of_continuity_modulus`.

**Remaining interface gap:** The set `A` must consist of `α →ᵇ L2ballR3 R` (bounded continuous
functions from `[0,T]` into `L2ballR3 R`). The curves `t ↦ restrictToBall R ((galSeq n).u t)`
are continuous on `[0,T]` (by `galerkin_curve_continuous` + `continuous_restrictToBall`) and
bounded (by `galerkin_norm_le_u0` + `norm_restrictToBall_le'`). Packaging these into the
`BoundedContinuousFunction` type adds glue lemmas but no new axioms.

### Sub-lemma 3: Pointwise precompactness at dense times

**Claim:** For each `t ∈ [0,T]`, the set `{restrictToBall R ((galSeq n).u t) | n : ℕ}` is
precompact in `L2ballR3 R`.

**Proof route:** Apply `steklovAvg_spatial_extraction` with δ → 0: by continuity in time (from
`galerkin_curve_continuous`), the average `steklovAvg (galSeq n) δ t → (galSeq n).u t` as δ → 0,
uniformly in n (from equicontinuity). Precompactness of the averages (proved by spatial
extraction at fixed δ) transfers to precompactness of the pointwise values by a 1/2-ε argument.

Alternatively: use `LocalRellichInput.ballCompact` directly — it gives a compact `K ⊆ L2ballR3 R`
containing `restrictToBall R ((galSeq n).u t)` for all `n`, given uniform L²+H¹ bounds. The
uniform L² bound `‖(galSeq n).u t‖ ≤ ‖u₀‖` is `galerkin_norm_le_u0`. The uniform H¹ bound
(uniform viscousFormSq) is NOT available pointwise (only L²-in-time via `reg_bound`). However,
`LocalRellichInput.ballCompact` is stated with `viscousFormSq_R3 1 w ≤ M²`, which requires a
pointwise H¹ bound, not just an integral one.

**The pointwise H¹ bound gap:** The `reg_bound` field gives `∫₀ᵀ viscousFormSq_R3 ν (u_n t) dt ≤ ½‖u₀‖²`.
This does NOT give a pointwise bound `viscousFormSq_R3 1 (u_n t) ≤ M²` for all `t`. Such a
pointwise bound is unavailable from `GalerkinSolutionData_R3` without the ODE energy identity
(not just the integrated bound). However, `steklovAvg_spatial_extraction` works around this: the
Steklov averages DO satisfy the pointwise H¹ bound (via `viscousFormSq_steklovAvg_uniform_bound`)
because the average absorbs the integral.

**Route:** Use continuity + equicontinuity to pass precompactness from the Steklov averages at
dense times to all times. This requires Sub-lemma 1 (equicontinuity) and is then
[Mathlib-provable] by a standard 1/3-ε argument (precompactness is preserved under uniform limits,
and `IsCompact` is sequentially compact in metric spaces).

**Classification: [Mathlib-provable given Sub-lemma 1]** — via `LocalRellichInput.ballCompact` +
equicontinuity (Sub-lemma 1) + Steklov-average bridge.

### Sub-lemma 4: Diagonal subsequence extraction over all R = 1, 2, 3, ...

**Claim:** From a sequence of per-ball subsequences `φ_1, φ_2, φ_3, ...` (each `φ_R` working for
ball radius `R`, `φ_{R+1}` a subsequence of `φ_R`), extract a single diagonal subsequence `φ`
such that `restrictToBall R (galSeq (φ n)).u t) → f_R(t)` for all `R` and a.e. `t ∈ [0,T]`.

**Mathlib route:**

The diagonal argument is purely combinatorial. Mathlib has:
- `IsCompact.tendsto_subseq` (`Mathlib.Topology.Sequences`): from compactness, extract convergent subsequence.
- The iterated extraction and diagonal argument must be built by hand, composing subsequences.
  There is no `Nat.diagonal_subseq` in Mathlib, but the construction is:
  `φ := fun n => φ_n n` where `φ_n` is the `n`-th level of a tower of subsequences.

This is entirely [Mathlib-provable] using `Function.comp`, `StrictMono.comp`, and elementary
natural-number arithmetic. The Lean proof will need a `Nat.rec`-style tower construction.

**The a.e.-in-time step:** The diagonal subsequence converges uniformly on `[0,T]` for each `R`,
hence converges EVERYWHERE (not just a.e.) in `t`. So there is no measurability issue at this
stage: convergence is pointwise for all `t`.

**Classification: [Mathlib-provable]** — elementary subsequence tower, no new Mathlib API needed.

### Sub-lemma 5: Assembling the limit curve `u : Time → L2Sigma_R3` and measurability

**Claim:** From the per-ball limits `f_R : [0,T] → L2ballR3 R` (consistent for different R:
`restrictToBall R₁ ∘ embed = restrictToBall R₂ ∘ embed` when `R₁ ≤ R₂`), assemble a single
`u_lim : Time → L2Sigma_R3` with `restrictToBall R (u_lim t : L2VF_R3) = f_R(t)` for all `R`.

**Two routes:**

**Route A (Banach–Alaoglu weak limit):** The sequence `(galSeq (φ n)).u t` is bounded in `L2VF_R3`
(by `galerkin_norm_le_u0`) so it has a weakly convergent subsequence in the Hilbert space `L2VF_R3`.
The weak limit `u_lim(t)` belongs to `L2Sigma_R3` (div-free: closed subspace, weak limit stays in it).
The ball restrictions of the weak limit agree with the strong limits `f_R(t)` (since strong
convergence on each ball implies weak convergence, hence the weak limit restriction matches `f_R`).

Mathlib status: `WeakDual.alaoglu_of_isLinearMap` / Banach–Alaoglu exists in some form in
Mathlib (see `Mathlib.Topology.Algebra.Module.WeakDual`), but applying it to extract a weakly
convergent subsequence from a bounded sequence in a Hilbert space requires `IsReflexive` and
separability. `L2VF_R3` is an `L²` space over a separable space, so it IS separable and reflexive,
but this is not exposed in the current codebase.

**Route B (direct gluing from per-ball limits):** Define `u_lim(t)` as follows: at each `t`, the
sequence `galSeq (φ n)).u t` converges in `L2ballR3 R` for each `R`. In `L2VF_R3` (which has the
"local convergence" topology), the limit is determined by its ball restrictions. Formally, by
`L²(ℝ³)` local convergence characterization (Riesz representation + exhaustion), a sequence that
converges locally in every `L²(B_R)` AND is bounded in `L²(ℝ³)` converges weakly in `L²(ℝ³)`.
This recovers Route A.

**The genuine Mathlib gap in Sub-lemma 5:** Neither route is directly available in Mathlib without:
1. A result identifying the weak limit from the per-ball strong limits (requires knowing that the
   sequence is bounded + per-ball strong convergence implies global weak convergence in `L2VF_R3`).
   This is a standard result but not formalized in Mathlib.
2. Preservation of the `L2Sigma_R3` (div-free) constraint under weak limits (closed convex set
   in Hilbert space, hence weakly closed — `IsClosed.isSeqClosed` for the weak topology).

**The div-free constraint:** `L2Sigma_R3` is defined as a `Subtype` (a `Set`). Weak closedness
of `L2Sigma_R3` would follow from the fact that `L2Sigma_R3 = ker(div)` in a distributional sense,
with `ker(div)` being a closed subspace (hence weakly closed). This is not in Mathlib.

**Measurability:** Once `u_lim : Time → L2Sigma_R3` is defined, measurability follows from
`aestronglyMeasurable_of_tendsto_ae` (Mathlib:
`Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable`, line 692–706): the
sequence `t ↦ restrictToBall R ((galSeq (φ n)).u t)` converges for a.e. `t` (here uniformly,
so everywhere) to `f_R(t)`, and each term is strongly measurable (continuous → measurable).
So `f_R` is strongly measurable. Extending to `u_lim` via the ball-gluing is then measurable
if the gluing is done through the weak limit (pointwise weak limit of measurables is measurable
in separable Hilbert spaces, via the same `aestronglyMeasurable_of_tendsto_ae`).

**Classification: [genuine gap → thinnest residual axiom]** — the gluing step requires:
  - bounded + per-ball-L² convergent → weakly convergent in `L2VF_R3`, and
  - weak limit in `L2Sigma_R3` (weakly closed subspace).

### Sub-lemma 6: Per-ball a.e.-convergence conclusion

**Claim:** From the diagonal uniform-in-t convergence `restrictToBall R ((galSeq (φ n)).u t) → f_R(t)`
for ALL `t ∈ [0,T]`, deduce a.e.-in-t convergence as required by the axiom's conclusion
`∀ᵐ t ∂ volume.restrict (Icc 0 T), Tendsto ...`.

**Route:** Uniform convergence implies everywhere convergence implies a.e. convergence. So this
is trivial: `Filter.Tendsto.of_forall` or `ae_of_all`. **Classification: [Mathlib-provable].**

---

## 3  The thinnest genuine residual axiom

After the analysis above, there are exactly TWO abstract facts not derivable from the current
axiomatic interface:

**(A) Equicontinuity from ODE (Sub-lemma 1):** The `n`-uniform time modulus for the Galerkin
curves, from `reg_bound` (L²-in-time H¹) + the trilinear form structure of `u_ode`.

**(B) Gluing + weak limit (Sub-lemma 5):** Assembling a single L2VF_R3-valued (and L2Sigma_R3-valued)
limit curve from the per-ball strong limits, using boundedness + local convergence → global weak
convergence in a Hilbert space, with preservation of div-free.

**Can these be combined into one axiom?** Yes. The CLEANEST formulation that absorbs both is a
single general abstract Arzelà–Ascoli-in-time lemma:

```lean
/-- Abstract local-time compactness extraction: Arzelà–Ascoli diagonalization.

Given a sequence of continuous curves `f : ℕ → [0,T] → H` into a Hilbert space `H` with:
(EC)  uniform equicontinuity: ∀ ε > 0 ∃ δ > 0 ∀ n s t, |s-t| < δ → ‖f n s - f n t‖ < ε
(PC)  pointwise precompactness in `K ⊆ H` compact: for each dense `{tₖ}`, `{f n tₖ | n}` is precompact
(BDD) boundedness: ∀ n t, ‖f n t‖ ≤ C

the sequence has a strictly-monotone subsequence `φ` and limit curve `g : [0,T] → H` (continuous)
such that `f (φ n) t → g t` pointwise (even uniformly) in `t ∈ [0,T]`. -/
axiom abstractArzelaAscoli_time  -- ALLOW_AXIOM: ...
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (C T : ℝ) (hT : 0 < T)
    (f : ℕ → ℝ → H) (hcont : ∀ n, ContinuousOn (f n) (Set.Icc 0 T))
    (hbdd : ∀ n t, t ∈ Set.Icc 0 T → ‖f n t‖ ≤ C)
    (hEC : ∀ ε > 0, ∃ δ > 0, ∀ n s t, s ∈ Set.Icc 0 T → t ∈ Set.Icc 0 T →
      |s - t| < δ → ‖f n s - f n t‖ < ε)
    (hPC : ∀ t ∈ Set.Icc 0 T, ∃ K : Set H, IsCompact K ∧ ∀ n, f n t ∈ K) :
    ∃ (φ : ℕ → ℕ) (g : ℝ → H), StrictMono φ ∧
      ContinuousOn g (Set.Icc 0 T) ∧
      ∀ t ∈ Set.Icc 0 T, Filter.Tendsto (fun n => f (φ n) t) Filter.atTop (nhds (g t))
```

This is REUSABLE for the torus (issue #23) and is the standard Arzelà–Ascoli diagonalization.
Its Lean proof requires the diagonal argument (combinatorially doable) + the Arzelà–Ascoli
theorem (`BoundedContinuousFunction.arzela_ascoli` in Mathlib) for fixed ball radius. The
honest assessment is this is HARD but MECHANICALLY POSSIBLE in Lean with the current Mathlib.

The second gap (gluing per-ball limits into a single `L2VF_R3`/`L2Sigma_R3` element) is a
SEPARATE abstract statement:

```lean
/-- Bounded-plus-per-ball-L²-convergent implies weakly convergent in L2VF_R3. -/
axiom perBallConvergence_implies_weakLimit  -- ALLOW_AXIOM: ...
    {u : ℕ → L2VF_R3} {C : ℝ} (hbdd : ∀ n, ‖u n‖ ≤ C)
    {g : ∀ R : ℝ, L2ballR3 R}
    (hconv : ∀ R, Filter.Tendsto (fun n => restrictToBall R (u n)) Filter.atTop (nhds (g R))) :
    ∃ u_lim : L2VF_R3,
      (∀ R, restrictToBall R u_lim = g R) ∧
      Filter.Tendsto (fun n => u n) Filter.atTop (nhds[weakTopology] u_lim)
```

However, this per-time-point weak convergence is not what the target axiom actually needs.
The target axiom requires `∀ R, ∀ᵐ t, Tendsto (restrictToBall R ∘ uₙ∘φ) atTop (nhds (restrictToBall R (u t)))`.
If Sub-lemma 2 gives UNIFORM (hence pointwise-for-all-t) convergence on each ball, the a.e.
conclusion is automatic. The limit `u : Time → L2Sigma_R3` can be DEFINED as the pointwise weak
limit (choosing for each `t` a limit using `Classical.choice` from the bounded sequence), and
then div-free must be checked — which brings back the weak-closedness gap.

---

## 4  FULL REMOVAL verdict

**FULL REMOVAL of `galerkinSpaceTimeExtraction_R3` in a single PR is NOT reachable without:**

1. Proving `galerkin_equicontinuity_from_ODE` (unconditional time modulus from ODE data), which
   requires a bound on `‖B(u_n, u_n)‖_{V*}` not currently in `R3NSForms` or `GalerkinSolutionData_R3`.

2. Proving the abstract Arzelà–Ascoli diagonalization over a Hilbert space on `[0,T]` (hard,
   but purely in Mathlib topology / compactness API).

3. Proving weak-closedness of `L2Sigma_R3` to assemble the limit curve's div-free property.

**GENUINE CONTENT REDUCTION is reachable** in a single PR by:

Split `galerkinSpaceTimeExtraction_R3` into TWO thinner axioms:
- `galerkin_equicontinuity_from_ODE` (the ODE-equicontinuity half), and
- `abstractArzelaAscoli_diag_R3` (the Arzelà–Ascoli diagonalization + gluing half),

where the SECOND axiom's proof is begun in the same PR (the diagonal subsequence over compact
metric spaces via `BoundedContinuousFunction.arzela_ascoli` is within reach), leaving only the
ODE trilinear estimate and the weak-limit gluing as residual axioms.

**Recommended route for #44 (maximum genuine content):**

PR #44 should:
1. Add `galerkin_equicontinuity_from_ODE` as a thin axiom (absorbing only the ODE content),
   with the exact signature above, `-- ALLOW_AXIOM: uniform time modulus from Galerkin ODE; requires
   b-trilinear dual norm bound (3D Sobolev) not exposed in R3NSForms`.
2. PROVE the Arzelà–Ascoli diagonalization sub-lemmas (Sub-lemmas 2, 3, 4, 6) using the new
   axiom + existing Mathlib API, producing a sorry-free proof from `galerkin_equicontinuity_from_ODE`
   + `LocalRellichInput` to the diagonalized subsequence + pointwise per-ball convergence.
3. PROVE the limit curve measurability using `aestronglyMeasurable_of_tendsto_ae` (Mathlib decl
   confirmed at `AEStronglyMeasurable.lean:692`).
4. For the gluing (Sub-lemma 5), add `galerkin_weakLimit_R3` as a second thin axiom:

```lean
axiom galerkin_weakLimit_R3  -- ALLOW_AXIOM: bounded + per-ball L²-convergent → weakly convergent in L2Sigma_R3; requires Banach–Alaoglu + weak-closedness of L2Sigma_R3 (div-free, closed subspace), neither formalized in Mathlib
    (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊) (ν : ℝ) (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n) (φ : ℕ → ℕ)
    (hφ : StrictMono φ)
    (T : ℝ) (hT : 0 < T)
    (hball : ∀ R : ℝ, ∀ t ∈ Set.Icc (0:ℝ) T, ∃ g_R : L2ballR3 R,
      Filter.Tendsto (fun n => restrictToBall R ((galSeq (φ n)).u t : L2VF_R3))
        Filter.atTop (nhds g_R)) :
    ∃ u : Time → L2Sigma_R3,
      AEStronglyMeasurable (fun t => (u t : L2VF_R3))
        (MeasureTheory.volume.restrict (Set.Icc (0:ℝ) T)) ∧
      ∀ R : ℝ, ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0:ℝ) T)),
        Filter.Tendsto (fun n => restrictToBall R ((galSeq (φ n)).u t : L2VF_R3))
          Filter.atTop (nhds (restrictToBall R (u t : L2VF_R3)))
```

5. Prove `galerkinSpaceTimeExtraction_R3` as a THEOREM from `galerkin_equicontinuity_from_ODE`
   + the Arzelà–Ascoli diagonalization proof + `galerkin_weakLimit_R3`.

This strategy:
- Replaces ONE axiom (`galerkinSpaceTimeExtraction_R3`) with TWO thinner, scheme-independent axioms.
- Proves everything else (Arzelà–Ascoli, diagonalization, measurability) sorry-free.
- The two residual axioms correspond to DISTINCT mathematical gaps:
  `galerkin_equicontinuity_from_ODE` ← ODE dual-norm bound (PDE analysis);
  `galerkin_weakLimit_R3` ← Banach–Alaoglu + div-free weak closedness (functional analysis).

---

## 5  Ordered declaration list (for `AubinLionsLimitPassage.lean`)

All new declarations live in the same file as the target axiom (or in a new helper file
`LerayHopf/R3/ArzelaAscoliTime.lean` for portability).

### Group T0: New thin axioms (replace the single fat axiom)

| # | Name | Kind | Status |
|---|------|------|--------|
| T0.1 | `galerkin_equicontinuity_from_ODE` | `axiom` | residual — must carry `ALLOW_AXIOM` |
| T0.2 | `galerkin_weakLimit_R3` | `axiom` | residual — must carry `ALLOW_AXIOM` |

### Group T1: Equicontinuity transfer (depend on T0.1)

| # | Name | Informal signature | Status |
|---|------|--------------------|--------|
| T1.1 | `galerkin_curves_equicont_unconditional` | `(𝔊 F ν hν T hT u₀ galSeq) → UniformEquicontinuous (fun n t => restrictToBall R ((galSeq n).u t))` on `[0,T]` | **must-prove** |
| T1.2 | `galerkin_curves_in_boundedContinuousFunctions` | package each `n ↦ BCF([0,T], L2ballR3 R)` | **must-prove** |

### Group T2: Per-ball Arzelà–Ascoli (depend on T1, `LocalRellichInput`)

| # | Name | Informal signature | Status |
|---|------|--------------------|--------|
| T2.1 | `galSeq_ball_pointwisePrecompact` | for fixed `R`, `t ∈ [0,T]`: `{restrictToBall R (galSeq n).u t | n}` is precompact in `L2ballR3 R` | **must-prove** |
| T2.2 | `galSeq_ball_equicont` | equicontinuity of the family on `[0,T]` in `L2ballR3 R` (from T1.1 + 1-Lipschitz of `restrictToBall`) | **must-prove** |
| T2.3 | `perBallSubseq_exists` | `∃ (φ_R : ℕ → ℕ) (f_R : ℝ → L2ballR3 R), StrictMono φ_R ∧ ContinuousOn f_R (Icc 0 T) ∧ ∀ t ∈ Icc 0 T, Tendsto (fun n => restrictToBall R ((galSeq (φ_R n)).u t)) atTop (nhds (f_R t))` | **must-prove** |

### Group T3: Diagonal subsequence (depend on T2.3)

| # | Name | Informal signature | Status |
|---|------|--------------------|--------|
| T3.1 | `perBallSubseq_tower` | inductive construction: `φ_{R+1}` is a subsequence of `φ_R` | **must-prove** |
| T3.2 | `diagonalSubseq_exists` | `∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ R : ℕ, ∀ t ∈ Icc 0 T, Tendsto (fun n => restrictToBall R ((galSeq (φ n)).u t)) atTop (nhds (f_R t))` | **must-prove** |

### Group T4: Gluing + measurability (depend on T0.2, T3.2)

| # | Name | Informal signature | Status |
|---|------|--------------------|--------|
| T4.1 | `perBallLimit_measurable` | `f_R` (the per-ball limit curve) is strongly measurable on `[0,T]` (from continuous) | **must-prove** |
| T4.2 | `u_lim_aestronglyMeasurable` | the assembled `u : Time → L2Sigma_R3` is `AEStronglyMeasurable` (from `T0.2` + `aestronglyMeasurable_of_tendsto_ae`) | **must-prove** |

### Group T5: Main theorem — replace axiom

| # | Name | Informal signature | Status |
|---|------|--------------------|--------|
| T5.1 | `galerkinSpaceTimeExtraction_R3` (as `theorem`) | exact current axiom signature, proved from `T0.1 + T0.2 + T1–T4` | **must-prove** |

---

## 6  Dependency graph

```
T0.1 (axiom: equicontinuity from ODE)
  └─ T1.1 (uniform equicont on L2ballR3 R)
       └─ T2.2 (equicont for ball family)
            └─ T2.3 (per-ball subseq, via arzela_ascoli₂)
                 └─ T3.1 (tower construction)
                      └─ T3.2 (diagonal subseq)
                           └─ T4.1 (limit measurable)
                           └─ T5.1 (main theorem, also needs T0.2)

T0.2 (axiom: weak limit in L2Sigma_R3)
  └─ T4.2 (u_lim AEStronglyMeasurable)
       └─ T5.1

T2.1 (pointwise precompactness from LocalRellichInput)
  └─ T2.3 (feeds arzela_ascoli₂'s range-precompactness hypothesis)

galerkin_norm_le_u0 (existing) → T1.2 (BCF packaging) → T2.3
galerkin_curve_continuous (existing) → T1.2
continuous_restrictToBall (existing) → T2.2
LocalRellichInput (existing) → T2.1
```

---

## 7  Assumptions to package as marked axioms

**New axioms introduced by this PR (2 total):**

1. `galerkin_equicontinuity_from_ODE` — `-- ALLOW_AXIOM: uniform time modulus of Galerkin curves from ODE; requires n-uniform dual-norm bound on B(u_n, u_n) in V*, which needs Sobolev trilinear estimate (Temam III.2.3) not exposed by R3NSForms.b; TRUE and scheme-independent; dischargeable once R3NSForms is strengthened with b_dual_norm_bound`

2. `galerkin_weakLimit_R3` — `-- ALLOW_AXIOM: per-ball-L²-convergent bounded sequence has weak limit in L2Sigma_R3; requires Banach–Alaoglu (bounded ball weakly compact in reflexive space) + weak-closedness of L2Sigma_R3 (divergence-free is weakly closed) — both standard functional analysis, not formalized in Mathlib; reusable for torus variant`

**Axiom removed by this PR:**

- `galerkinSpaceTimeExtraction_R3` — converted to `theorem`, proved from the two new axioms above.

**Net axiom balance:** -1 + 2 = +1 additional axiom, but the two new ones are:
(a) mathematically cleaner (one isolates ODE dual-norm, one isolates Banach–Alaoglu + div-free);
(b) scheme-independent and reusable;
(c) each strictly thinner than the original fat axiom.

---

## 8  Codex adversarial-review points

The following new statements should receive `/codex:adversarial-review` before proofs are attempted:

1. **`galerkin_equicontinuity_from_ODE`** — verify the statement is exactly what the ODE gives
   (is the modulus `ω(δ) = C√δ` or different? does forward-only `u_hasDeriv` cause issues at `t = 0`?).

2. **`galerkin_weakLimit_R3`** — verify the conclusion is exactly what the axiom downstream needs
   (does the `∀ R` quantifier over `ℝ` or `ℕ` suffice? does the `AEStronglyMeasurable` conclusion
   follow from the hypothesis as stated, or does it need to be strengthened?).

3. **`galerkinSpaceTimeExtraction_R3` as a theorem** — verify the proof sketch above actually
   composes (in particular: the forward-only differentiability in `u_hasDeriv` limits FTC to
   `[s,t] ⊆ [0,T]`; `ContinuousOn` on `Ici 0` is sufficient for `arzela_ascoli` on `Icc 0 T`).

4. **`perBallSubseq_exists` (T2.3)** — verify the pointwise-precompactness hypothesis feeds
   `arzela_ascoli₂` correctly (the Mathlib theorem requires `CompactSpace β` or an explicit
   compact `s : Set β`; `LocalRellichInput.ballCompact` gives the latter form, but needs the
   H¹ uniform bound which is only available at Steklov-average times, not raw-curve times).
   This is the HARDEST sub-lemma and should be reviewed before coding.

---

## 9  Definition of done for milestone #44

The milestone is DONE when:

1. `galerkinSpaceTimeExtraction_R3` is declared as `theorem` (not `axiom`), sorry-free,
   proved from `galerkin_equicontinuity_from_ODE` and `galerkin_weakLimit_R3`.

2. The axiom `galerkinSpaceTimeExtraction_R3` (with its `ALLOW_AXIOM` marker) is REMOVED from
   `AubinLionsLimitPassage.lean`.

3. The two replacement axioms `galerkin_equicontinuity_from_ODE` and `galerkin_weakLimit_R3`
   carry `ALLOW_AXIOM` markers with precise justification text matching this contract.

4. All intermediate lemmas (T1–T5) are sorry-free.

5. `lake build` passes with no new `sorryAx` in the axiom set of
   `galerkinSpaceTimeExtraction_R3`.

6. `aubinLionsPackage_R3_of_timeCompactness` still compiles unchanged (its interface is not
   modified by this PR).

Partial win (if full removal is too large for one PR): stop after T3.2 is proved, delivering
the diagonal subsequence as a sorry-free lemma, and keep the conversion of the axiom to a
theorem for a follow-up PR (#45).

---

## 10  Hardest sub-lemma and API survey requirements

**Hardest sub-lemma: T2.3 (`perBallSubseq_exists`)**

This requires feeding `BoundedContinuousFunction.arzela_ascoli₂` with:
(a) compact domain `[0,T]` — OK via `isCompact_Icc`.
(b) compact `s : Set (L2ballR3 R)` containing all `f n x` — this is `LocalRellichInput.ballCompact`,
    but it requires uniform `viscousFormSq_R3 1 w ≤ M²` pointwise at every `t`, not just in L²-average.
    The raw Galerkin curves do NOT have this — only the Steklov averages do.

**Resolution for T2.3:** The `steklovAvg_spatial_extraction` already handles the spatial
precompactness via the Steklov average, not the raw curve. The equicontinuity (Sub-lemma 1) +
Steklov spatial precompactness → raw-curve spatial precompactness at each `t` is the key chain
that must be made explicit. This requires:

```
∀ ε, ∃ δ, ∀ n, ‖restrictToBall R ((galSeq n).u t) - steklovAvg(galSeq n)(δ/2)(t)‖ < ε/3
```
(controlled by the equicontinuity modulus), plus the Steklov spatial precompactness at `t` gives
a finite ε/3-net. This is a 2/3-ε argument, done without new Mathlib but with ~30 lines of tactic.

**Mathlib API surveys needed before coding:**

1. `BoundedContinuousFunction.arzela_ascoli₂` — verify it applies here; check what
   `CompactSpace` instances are needed for `L2ballR3 R` as a metric space.

2. `Metric.equicontinuous_of_continuity_modulus` — verify the bridge from the modulus bound
   (from `galerkin_equicontinuity_from_ODE` + `norm_restrictToBall_le'`) to
   `Equicontinuous ((↑) : A → [0,T] → L2ballR3 R)`.

3. `IsCompact.isSeqCompact` + `IsSeqCompact.subseq_of_frequently_in` — confirm these are
   available in the version of Mathlib pinned by this project.

4. `aestronglyMeasurable_of_tendsto_ae` (confirmed: `AEStronglyMeasurable.lean:692`) — verify
   the precise hypotheses (needs `PseudoMetrizableSpace β`; `L2ballR3 R` is a metric space, ✓).

---

## 11  Summary

**Recommended first task for `lean-coder`:**

Write the two thin replacement axioms `galerkin_equicontinuity_from_ODE` and
`galerkin_weakLimit_R3` with their `ALLOW_AXIOM` markers, request Codex adversarial review on
both statements, and then proceed to prove T1.1 (equicontinuity transfer to ball restrictions,
using `norm_restrictToBall_le'` + the modulus from the new axiom + `Metric.equicontinuous_of_continuity_modulus`).

The lean-coder should NOT attempt T2.3 until T1 is sorry-free and the Codex review on T2.3's
design (the 2/3-ε precompactness bridge) has been completed.
