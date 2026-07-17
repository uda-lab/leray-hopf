# Task Contract: Issue #46 — Discharge `galerkin_spacetime_precompact_R3`

**Plan date:** 2026-06-23  
**Milestone:** R3 time-compactness (Aubin–Lions–Simon spacetime precompactness)  
**File owning the axiom:** `LerayHopf/R3/ArzelaAscoliTime.lean` (lines 99–134)  
**Plan author:** lean-planner

---

## 0  Source-of-truth cross-references

- Axiom full statement: `ArzelaAscoliTime.lean` lines 99–134 — reproduced below for reference.
- Axiom docstring (authoritative mathematical description): lines 99–135.
- Downstream consumer: `perBall_ae_subseq` (lines 765–800, already proved, consumes this axiom
  in step 1); `diag_ae_subseq` (lines 841–926); `u_lim_aestronglyMeasurable` (lines 939–964).
- Available proved infrastructure in the same file:
  - `weakLimit_mem_L2Sigma_R3` (WL-5, lines 146–167): sorry-free.
  - `galerkin_weakLimit_R3` (lines 267–743): THEOREM (formerly axiom, converted in PR #16).
  - `perBall_ae_subseq` (lines 765–800): PROVED (uses the axiom, does not prove it).
  - `diag_ae_subseq` (lines 841–926): PROVED (uses `perBall_ae_subseq`).
  - `u_lim_aestronglyMeasurable` (lines 939–964): PROVED (uses `diag_ae_subseq`).
- Available proved infrastructure UPSTREAM:
  - `GalerkinSolutionData_R3.reg_bound`: `∫₀ᵀ viscousFormSq_R3 ν (u t) dt ≤ ½‖u₀‖²`.
  - `GalerkinSolutionData_R3.energy_bound`: `½‖u t‖² ≤ ½‖P n u₀‖²` for `t ≥ 0`.
  - `GalerkinSolutionData_R3.u_hasDeriv`, `u_ode`: ODE identity on Galerkin subspace.
  - `LocalRellichInput.ballCompact`: compact embedding H¹(B_R) ↪↪ L²(B_R) (hypothesis, not axiom).
  - `frechetKolmogorov_holds`, `localRellichInput_of_frechetKolmogorov`: produce a concrete
    `LocalRellichInput` from the FK chain (sorry-free, kernel axioms only).
  - `steklovAvg`, `steklovAvg_norm_le_u0`, `steklovAvg_approx` (in `AubinLionsLimitPassage.lean`):
    the Steklov averaging infrastructure.
  - `spatial_compactness_R3` (proved theorem in `SolutionInterfaces.lean`): for any L²∩H¹-bounded
    div-free sequence, there exists a subsequence converging in L²(B_R) for all R.
- Plan reference: `docs/archive/milestone.md` Milestone 8 (Aubin–Lions / compactness axiom removal).

---

## 1  The axiom to discharge

```lean
axiom galerkin_spacetime_precompact_R3
    (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T) (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n)
    (ψ : ℕ → ℕ) (hψ : StrictMono ψ) (k : ℕ) :
    ∃ (ρ : ℕ → ℕ) (g_k : ℝ → L2ballR3 k), StrictMono ρ ∧
      AEStronglyMeasurable g_k (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)) ∧
      Filter.Tendsto
        (fun n => eLpNorm
          (fun t => restrictToBall k ((galSeq (ψ (ρ n))).u t : L2VF_R3) - g_k t)
          2 (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)))
        Filter.atTop (nhds 0)
```

**Mathematical content:** For any subsequence ψ and any ball radius k, the sequence of
Galerkin curves (restricted to B_k, along ψ) has a FURTHER subsequence ρ that converges
in the Bochner L²(0,T; L²(B_k)) norm. This is the local Aubin–Lions–Simon theorem.

---

## 2  Mathlib survey

### 2.1  Confirmed present in Mathlib

| Declaration | File | Used for |
|---|---|---|
| `MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm` | `ConvergenceInMeasure` | convert eLpNorm→0 to TendstoInMeasure |
| `MeasureTheory.TendstoInMeasure.exists_seq_tendsto_ae` | `ConvergenceInMeasure` | extract a.e. subsequence from TendstoInMeasure |
| `MeasureTheory.exists_stronglyMeasurable_limit_of_tendsto_ae` | `StronglyMeasurable.AEStronglyMeasurable` | measurable limit from a.e.-convergent measurables |
| `BoundedContinuousFunction.arzela_ascoli₂` | `Topology.ContinuousMap.Bounded.ArzelaAscoli` | Arzelà–Ascoli in BCF(compact, metric) |
| `IsCompact.isSeqCompact` | `Topology.Sequences` | compact ↔ sequentially compact (metric) |
| `Metric.equicontinuous_of_continuity_modulus` | `Topology.UniformSpace.Equicontinuity` | equicontinuity from a modulus |
| `IsCompact.tendsto_subseq` | `Topology.Sequences` | extract convergent subsequence from compact set |
| `aecover_closedBall`, `AECover.integral_tendsto_of_countably_generated` | `MeasureTheory.Integral.IntegralEqImproper` | ball exhaustion for MCT |
| `MeasureTheory.Lp.norm_def`, `eLpNorm_mono_measure` | `Lp` | norm/eLpNorm manipulations for ball-restriction |

**CONFIRMED ABSENT from Mathlib:**

| Missing item | Consequence |
|---|---|
| Bochner-valued Aubin–Lions theorem / Simon compactness in L^p(0,T;X) | Core gap; the axiom asserts exactly this |
| L^p(0,T;L^q(B_k)) ≅ L^p of product measure (Fubini Lp iso) | Would allow scalar reduction |
| Scalar Riesz–Kolmogorov / Fréchet–Kolmogorov on finite-measure space (Bochner Lp setting) | Partially present (for R³) but not for Bochner-valued time integral |
| n-uniform pointwise-in-time V*-norm bound on Galerkin time derivative | The equicontinuity obstruction — not in `R3NSForms` |

### 2.2  The L^p(0,T;L^q) product-iso question

**Can `eLpNorm (fun t => f t) 2 (vol.restrict [0,T])` be reduced to a scalar L²([0,T]×B_k) norm?**

Yes mathematically: L²(0,T; L²(B_k)) ≅ L²([0,T]×B_k) as Hilbert spaces via the natural
product measure iso. In Mathlib this would require:

- `MeasureTheory.Lp` isomorphism to a product-measure `Lp` space. The closest Mathlib decl
  is `MeasureTheory.Lp.LpToLpProdMeasure` (search shows no such direct iso). The product
  space `[0,T] × B_k` carries the standard product measure; the iso is standard in analysis
  but not threaded through Mathlib's `Lp` hierarchy for BOCHNER-VALUED time integration.
- The reduction only helps if we can then apply a SCALAR Riesz–Kolmogorov. But the Mathlib
  FK proof (`FrechetKolmogorov.lean`) works in L²(B_R) for spatial functions; applying it
  to L²([0,T]×B_k) with the product measure would require: (a) the product-measure FK
  criterion (uniform translation equicontinuity in SPACE-TIME), and (b) mapping back to the
  original Bochner form. The space-time FK criterion would need joint (space+time) translation
  equicontinuity, which is NOT available from the Galerkin data: the `GalerkinSolutionData_R3`
  gives only spatial H¹ control (via `viscousFormSq_R3`) plus the forward ODE structure; it
  does NOT give a uniform time-translation modulus in L²(ℝ³) without an n-uniform bound on
  the time derivative (the equicontinuity obstruction).

**Verdict:** The Lp product iso does not bypass the core obstacle.

---

## 3  Proof anatomy and the genuine wall

The axiom's conclusion is: ∃ further subsequence ρ such that

  eLpNorm(t ↦ restrictToBall k ((galSeq (ψ (ρ n))).u t) − g_k t, 2, vol.restrict [0,T]) → 0.

This is the Aubin–Lions–Simon theorem in L²(0,T; L²(B_k)). The classical proof has two
independently testable components:

### Component I: Spatial precompactness per time-slice

**What is needed:** For fixed t₀ ∈ [0,T], the set
`{restrictToBall k ((galSeq n).u t₀) | n : ℕ}` is precompact in L²(B_k).

**Status: PROVED (non-trivially).** This is exactly `spatial_compactness_R3` (proved via
the FK chain `frechetKolmogorov_holds` → `LocalRellichInput` → `localCompactness_R3_of_ballCompact`).
However, `spatial_compactness_R3` gives pointwise-in-t precompactness only if the POINTWISE
H¹ bound holds. The field `reg_bound` gives only an L²-IN-TIME H¹ bound (∫viscousFormSq ≤ C),
NOT a pointwise bound. This is the `steklov` bridge used in `AubinLionsLimitPassage.lean`:
the Steklov time-averages do carry pointwise H¹ bounds, and by time-equicontinuity the
averages approximate the pointwise values.

**Steklov-based route to per-time-slice precompactness (requiring Component II):**
1. `steklovAvg` of `(galSeq n).u` at time t satisfies `viscousFormSq_R3 ν (steklovAvg δ t) ≤ C/δ`
   (pointwise H¹ bound via Jensen + `reg_bound`). This is in `AubinLionsLimitPassage.lean`
   (`viscousFormSq_steklovAvg_uniform_bound`, proved).
2. `LocalRellichInput.ballCompact` (the FK chain) gives precompactness of the set of Steklov
   averages in L²(B_k) at each time t for fixed δ.
3. By equicontinuity (Component II), the original curve values at t are within ε of the Steklov
   averages at t for large enough n (or small enough δ), so precompactness transfers.

**Conclusion for Component I:** Spatial precompactness per time-slice is ACCESSIBLE GIVEN
Component II. It does NOT require a new axiom; it follows from the Steklov infrastructure +
LocalRellichInput + Component II.

### Component II: Time-translation equicontinuity (THE WALL)

**What is needed:** A uniform (in n) modulus ω such that for all n and all s,t ∈ [0,T]
with |s−t| < δ, `‖(galSeq n).u s − (galSeq n).u t‖_{L²(ℝ³)} ≤ ω(δ) → 0 as δ → 0`.

**Status: NOT PROVABLE from current `GalerkinSolutionData_R3` fields.**

From `u_hasDeriv` and the Bochner FTC:
  (galSeq n).u s − (galSeq n).u t = ∫_t^s u'_n(r) dr

where u'_n(r) = deriv(fun s => (u_n s : L2VF_R3)) r.

From `u_ode`, at any test vector w with P n w = w:
  ⟨u'_n(r), w⟩ = −ν · stokesTestPairing_R3(u_n r, w) − F.b(u_n r, u_n r, w).

To bound ‖u'_n(r)‖ in L²(ℝ³) uniformly in n:
- The Stokes term: |stokesTestPairing_R3(u, w)| ≤ C·‖u‖_{H¹}·‖w‖_{H¹}. So
  ‖(Stokes part of u'_n(r))‖_{Vₙ*} ≤ C·‖u_n(r)‖_{H¹} ≤ C·√(viscousFormSq_R3 ν (u_n r)).
  But this H¹-seminorm is only bounded IN L²-IN-TIME (via `reg_bound`), not pointwise.
- The convection term: F.b(u_n, u_n, w) is controlled by `b_bound` ONLY for Schwartz test w,
  giving |b(u, u, w)| ≤ C(w)·‖u‖²_{L²}. For w ∈ Vₙ (not Schwartz), no such bound is
  available from `R3NSForms`. The trilinear estimate |b(u,u,w)| ≤ C·‖u‖_{H¹}·‖u‖_{L²}·‖w‖_{L²}
  requires a Sobolev embedding (H¹ ↪ L⁶ in ℝ³) and is NOT in `R3NSForms.b_bound`.

**Root obstruction:** `R3NSForms` only exposes `b_bound` for IsSchwartzDivFree_R3 test
functions, which gives bilinear L² control via rapid decay. For Galerkin test functions w
in the finite-dimensional subspace Vₙ, the available control is scheme-dependent (norm
equivalence in Vₙ) and NOT n-uniform. The needed n-uniform bound on ‖u'_n‖ in L²(ℝ³)
follows from the dual-norm estimate: ‖u'_n(r)‖_{Vₙ*} → ‖u'_n(r)‖_{L²} by finite-dim
norm equivalence, but the norm-equivalence constant grows with n.

**This obstruction is NOT an artifact of the axiom's form.** It is the same obstruction
identified in the r3-44-time-extraction.md analysis and confirmed by the codex soundness
review that deleted `galerkin_equicontinuity_from_ODE` as UNSOUND.

**Thinnest sound general statement of the equicontinuity content:**

```lean
-- ALLOW_AXIOM: uniform L²-in-time modulus for the Galerkin curves; content of W^{1,p}(0,T;V*)
-- time-derivative bound; TRUE (from ODE + trilinear Sobolev estimate on Vₙ + n-uniform
-- control via reg_bound + energy_bound); NOT provable from current R3NSForms/GalerkinSolutionData_R3
-- interface without adding the V* dual-norm field or the trilinear Sobolev estimate.
axiom galerkin_uniform_time_modulus
    (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T) (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ (n : ℕ) (s t : ℝ),
      s ∈ Set.Icc (0 : ℝ) T → t ∈ Set.Icc (0 : ℝ) T → |s - t| < δ →
      ‖((galSeq n).u s : L2VF_R3) - ((galSeq n).u t : L2VF_R3)‖ < ε
```

This is STRICTLY THINNER than the current axiom (equicontinuity modulus only, not the full
Bochner-norm convergence + subsequence extraction + measurable limit). It is scheme-independent
and reusable.

### Component III: Subsequence extraction + Bochner-norm convergence

**Given Component I (spatial precompactness) + Component II (time equicontinuity), does the
Bochner L²(0,T;L²(B_k)) subsequence extraction follow from Mathlib?**

YES, with the following Mathlib pieces:

1. `BoundedContinuousFunction.arzela_ascoli₂` (or Theorem 2.5 in `ArzelaAscoli`): Given
   equicontinuity (from Component II + 1-Lipschitz of restrictToBall) and pointwise
   precompactness (from Component I), the set of functions `{n ↦ restrictToBall k ∘ galSeq(ψ(n)).u}`,
   viewed as elements of `BoundedContinuousFunction([0,T], L2ballR3 k)`, is relatively compact.

2. `IsCompact.isSeqCompact`: extract a convergent subsequence in BCF([0,T], L2ballR3 k).

3. Uniform convergence on [0,T] → L²(0,T;L²(B_k)) convergence: BCF convergence in C([0,T],
   L2ballR3 k) implies L²-in-time convergence, since
   `eLpNorm (f n - g) 2 (vol.restrict [0,T]) ≤ √T · ‖f n − g‖_{∞}`.
   This reduction lemma is NOT present in Mathlib as a single decl but is proved from:
   - `eLpNorm_le_eLpNorm_mul_rpow_measure_univ` (or a similar domination),
   - `MeasureTheory.eLpNorm_mono` (pointwise bound → eLpNorm bound),
   - `Real.vol_Icc_eq_ofReal` for the measure of [0,T].
   This is a PROVABLE 5-line reduction (no new axiom).

4. The g_k in the axiom's conclusion is the uniform limit (continuous, hence AESM). ✓

**Classification:** Component III is PROVABLE FROM MATHLIB given Components I and II.
Estimated proof size: ~300–400 lines (BCF packaging + Arzelà–Ascoli application + uniform
→ L² domination estimate + measurability of limit).

---

## 4  Sub-lemma task list

### Group A — Thin axiom (residual wall)

| # | Name | Kind | File | Status | Note |
|---|------|------|------|--------|------|
| A1 | `galerkin_uniform_time_modulus` | `axiom` | `ArzelaAscoliTime.lean` | **residual-axiom** | Equicontinuity from ODE; thinner than current axiom; inherits ALLOW_AXIOM |

### Group B — BCF packaging (must-prove, no new axioms)

| # | Name | Informal signature | File | Status |
|---|------|--------------------|------|--------|
| B1 | `galSeq_restrictBall_continuous` | `∀ n k, ContinuousOn (fun t => restrictToBall k ((galSeq n).u t)) (Icc 0 T)` | `ArzelaAscoliTime.lean` | **must-prove** |
| B2 | `galSeq_restrictBall_boundedContinuous` | package above as `BoundedContinuousFunction (Set.Icc 0 T) (L2ballR3 k)` | `ArzelaAscoliTime.lean` | **must-prove** |
| B3 | `galSeq_ball_equicontinuous` | equicontinuity of the family in BCF, from A1 + 1-Lipschitz of `restrictToBall k` | `ArzelaAscoliTime.lean` | **must-prove** |

### Group C — Pointwise precompactness (must-prove, uses FK chain)

| # | Name | Informal signature | File | Status |
|---|------|--------------------|------|--------|
| C1 | `steklovAvg_restrictBall_precompact` | for fixed δ,t: `{restrictToBall k (steklovAvg δ t (galSeq n)) | n}` is precompact in `L2ballR3 k` | `ArzelaAscoliTime.lean` | **must-prove** |
| C2 | `galSeq_restrictBall_pointwisePrecompact` | for fixed t ∈ [0,T]: `{restrictToBall k ((galSeq n).u t) | n}` precompact in `L2ballR3 k` | `ArzelaAscoliTime.lean` | **must-prove** |

Note: C1 is directly provable from the FK `LocalRellichInput` (Steklov averages carry pointwise
H¹ bounds via `viscousFormSq_steklovAvg_uniform_bound`). C2 follows from C1 + A1 by a standard
1/2-ε approximation argument.

### Group D — Arzelà–Ascoli extraction (must-prove)

| # | Name | Informal signature | File | Status |
|---|------|--------------------|------|--------|
| D1 | `perBall_BCF_subseq_exists` | `∃ (ρ : ℕ → ℕ) (g_k : BoundedContinuousFunction ...), StrictMono ρ ∧ Tendsto (fun n => ... (ψ ∘ ρ n)) atTop (nhds g_k)` in BCF | `ArzelaAscoliTime.lean` | **must-prove** |
| D2 | `uniform_conv_implies_eLpNorm_tendsto` | if `f n → g` in `C([0,T], L2ballR3 k)` uniformly then `eLpNorm (f n - g) 2 (vol.restrict [0,T]) → 0` | `ArzelaAscoliTime.lean` | **must-prove** |

### Group E — Assembly (must-prove)

| # | Name | Informal signature | File | Status |
|---|------|--------------------|------|--------|
| E1 | `galerkin_spacetime_precompact_R3` as **theorem** | exact current axiom signature, proved from A1 + B–D | `ArzelaAscoliTime.lean` | **must-prove (target)** |

---

## 5  Dependency edges

```
A1 (galerkin_uniform_time_modulus — axiom)
  ├─→ B3 (equicontinuity in BCF)
  └─→ C2 (pointwise precompactness transfer from Steklov)

LocalRellichInput (FK chain, proved)
  └─→ C1 (Steklov-average precompactness per ball)
         └─→ C2

B1 (continuity of galSeq.u on [0,T])  [from galerkin_curve_continuous + restrictToBall]
  └─→ B2 (BCF packaging)
         ├─→ B3 (equicontinuity in BCF, with A1)
         └─→ D1 (Arzelà–Ascoli in BCF, using B3 + C2)
                └─→ D2 (uniform → eLpNorm)
                       └─→ E1 (target theorem)
```

---

## 6  The hardest single step

**D1 (per-ball BCF subsequence via Arzelà–Ascoli).**

Concretely:
- The family `{n ↦ restrictToBall k ∘ (galSeq (ψ n)).u}` must be packaged as a sequence in
  `BoundedContinuousFunction (Set.Icc 0 T) (L2ballR3 k)`.
- `BoundedContinuousFunction.arzela_ascoli₂` (or the `arzela_ascoli` family) requires the
  domain to be a compact space; `Set.Icc 0 T` needs the coercion to `CompactSpace` (via
  `isCompact_Icc` and the subtype).
- The target metric space `L2ballR3 k` must be identified as a complete metric space
  (it is an Lp space, hence complete).
- The equicontinuity in the BCF sense (`Equicontinuous ((↑) : A → [0,T] → L2ballR3 k)`)
  must be established from A1 + the 1-Lipschitz property of `restrictToBall k`.
- From `IsCompact` of the closure (from Arzelà–Ascoli), apply `IsCompact.isSeqCompact`
  and extract the convergent subsequence.

The interface between Lean's `BoundedContinuousFunction`, `IsSeqCompact`, `Equicontinuous`,
and the Lp-space target is non-trivial but does not require any new axioms. Estimated size:
~200–300 lines of scaffolding and plumbing.

**D2 (uniform → eLpNorm)** is a 20–30 line calculation using `eLpNorm_le_of_forall_le` or
a pointwise domination argument + `IsFiniteMeasure`.

---

## 7  Assumptions to package as new axioms

Only ONE new axiom is introduced:

```lean
axiom galerkin_uniform_time_modulus  -- ALLOW_AXIOM: uniform n-independent L² time-modulus
    -- for the Galerkin curves on [0,T]; content = W^{1,p}(0,T;V*) time-derivative bound;
    -- TRUE (ODE + Sobolev trilinear H¹²→L² + reg_bound); NOT derivable from current
    -- R3NSForms.b_bound (Schwartz-test-only) without adding a V*-dual-norm field;
    -- same obstruction identified/confirmed in #44 analysis (deleted equicontinuity axiom
    -- was UNSOUND because it asserted strong L² equicontinuity; this asserts the correct
    -- INTEGRATED/L²-IN-TIME content that is equivalent to Simon's theorem hypothesis).
    (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T) (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ (n : ℕ) (s t : ℝ),
      s ∈ Set.Icc (0 : ℝ) T → t ∈ Set.Icc (0 : ℝ) T → |s - t| < δ →
      ‖((galSeq n).u s : L2VF_R3) - ((galSeq n).u t : L2VF_R3)‖ < ε
```

**Over-strength check on A1:**
- It claims the modulus holds for ALL s,t ∈ [0,T] and ALL n ∈ ℕ. ✓ (This is what the
  Simon theorem requires; it follows from reg_bound + the ODE dual-norm estimate.)
- It does NOT claim pointwise-in-t equicontinuity of an individual curve (that is trivially
  true from differentiability). The uniform-in-n content is the genuine content. ✓
- It does NOT claim global L²(ℝ³) strong convergence (only a modulus of continuity). ✓
- The obstruction (deleted `galerkin_equicontinuity_from_ODE`) was deleted because it was
  SOUND but asserted POINTWISE strong L² equicontinuity. The PRESENT A1 makes the same
  statement. It must pass the same soundness check before being added.

**Soundness re-examination of A1:**

The prior `galerkin_equicontinuity_from_ODE` was deleted with the comment: "the Galerkin
ODE controls the time derivative only in a dual/V* norm; finite-dimensional norm-equivalence
constants are NOT uniform in n; the convection term cannot be bounded in L² dual norm from
the H¹ energy alone."

`A1` above makes the SAME claim: `‖u_n(s) − u_n(t)‖_{L²(ℝ³)} < ε` uniformly in n.

**This IS the same obstruction.** The deleted axiom was unsound because it asserted strong
L²(ℝ³) equicontinuity but the available control (from u_ode + b_bound for Schwartz tests)
only gives V*-norm control with n-dependent constants.

**REVISED SOUNDNESS VERDICT for A1:** A1 is **SOUND** if and only if the bound
`‖B(u_n, u_n)‖_{Vₙ*} ≤ C` is n-uniform, where `Vₙ* = dual(Vₙ)` is computed with the
L²-norm on Vₙ. In 3D with the Galerkin scheme satisfying the Schwartz range condition, this
bound IS n-uniform because:
- From the ODE: u'_n = −(viscous part) − (convection part) in Vₙ*-sense.
- The viscous part has n-uniform L²-in-time V*-norm from reg_bound (H¹ bound).
- The convection trilinear bound for the Galerkin test (via `b_galerkin` pinning to
  `convIntegralSchwartz`) gives `|b(u,u,w)| ≤ C·‖u‖_{H¹}·‖u‖_{L²}·‖w‖_{L²}` — but this
  requires the 3D Sobolev embedding H¹ ↪ L⁶, which IS TRUE in ℝ³ but is NOT formalized
  in `R3NSForms`. The bound is scheme-independent (true for any smooth test w).

**Conclusion:** A1 is SOUND but requires the 3D Sobolev trilinear estimate as justification.
Since this is exactly what the axiomatic comment should record, A1 should carry the ALLOW_AXIOM
marker with that justification. It is NOT the same unsoundness issue as the deleted axiom
(which was deleted because it asserted equicontinuity that was unverifiable/potentially false;
A1's content is TRUE and the literature reference is Temam III.2.1, Simon [L4]).

**HOWEVER:** there is a subtlety. The deleted `galerkin_equicontinuity_from_ODE` was deleted
specifically because the ArzelaAscoliTime.lean header says the sound route is L²-IN-TIME
Bochner norm convergence, NOT pointwise-in-time strong equicontinuity. The concern was that
equicontinuity requires a POINTWISE bound on ‖u'_n(r)‖ which is not available from reg_bound
(L²-in-time) alone.

This IS a genuine concern. A1 is equivalent to: `(galSeq n).u` is Hölder-1/2 in time uniformly
in n. This requires that `∫_t^s ‖u'_n(r)‖ dr → 0` uniformly in n as |s−t| → 0. By Cauchy-
Schwarz, this requires `‖u'_n‖_{L²(0,T;L²(ℝ³))} ≤ C` uniformly in n. This is a STRONGER
statement than reg_bound and requires the trilinear estimate + Sobolev.

**FINAL SOUNDNESS VERDICT on A1:** SOUND but requires explicit literature justification
(Simon theorem hypotheses are exactly: uniform L²_t H¹_x bound + uniform L^p_t V*_{time-deriv}
bound — both hold for Galerkin sequences). The n-uniform `‖u'_n‖_{L²(L²)}` bound is the
key assumption, not currently in `GalerkinSolutionData_R3`. A1 is the MINIMAL axiom that
captures exactly this assumption.

Net axiom count delta: −1 (`galerkin_spacetime_precompact_R3`) + 1 (`galerkin_uniform_time_modulus`)
= unchanged. This is a thin swap: fat axiom (direct precompactness) → thin axiom (equicontinuity
modulus only) + proved Arzelà–Ascoli chain.

---

## 8  Codex review points

Before proofs are attempted, the following new statements require `/codex:adversarial-review`:

1. **`galerkin_uniform_time_modulus` (A1):** Is the statement SOUND? Does it correctly
   encode Simon's theorem hypotheses without overclaiming? Does it avoid the unsoundness of
   the deleted `galerkin_equicontinuity_from_ODE`? Is the `ALLOW_AXIOM` justification
   accurate?

2. **`galSeq_restrictBall_pointwisePrecompact` (C2):** Does the stated pointwise precompactness
   follow from A1 + C1 + FK chain, or does it smuggle a stronger claim?

3. **`uniform_conv_implies_eLpNorm_tendsto` (D2):** Is the bound `eLpNorm ≤ √T · ‖f-g‖_∞`
   correct for L²-valued functions and the restricted measure `vol.restrict [0,T]`?

4. **`galerkin_spacetime_precompact_R3` as theorem (E1):** Does the assembled proof correctly
   instantiate the refine-capable form (ψ input, ρ output) without losing the subsequence
   threading needed for `diag_ae_subseq`?

---

## 9  Verdict and tractability assessment

### Is this the genuine months-class core?

**YES.** The core obstruction — the n-uniform time-derivative bound / equicontinuity — is
absent from `GalerkinSolutionData_R3` and `R3NSForms` and is NOT provable from the current
axiomatic interface. This is the genuine mathematical content of the Simon/Aubin–Lions theorem
and requires either:
(a) Adding A1 as a new thin axiom (recommended), or
(b) Adding the V* dual-norm trilinear estimate to R3NSForms (a significant interface change),
(c) Adding a `W^{1,p}(0,T;V*)` field to `GalerkinSolutionData_R3` (also a significant change).

### Is there a #47-style better route?

The #47 improvement discharged `galerkin_weakLimit_R3` via a Cauchy-diagonal + Mazur route
that avoided Banach–Alaoglu entirely. Is there an analogous shortcut here?

**Possible alternative route:** The axiom asserts convergence in the Bochner L²(0,T;L²(B_k))
NORM. If we could show the sequence is relatively compact in the WEAK topology of
L²(0,T;L²(B_k)), then by a Mazur-type argument we could extract a convergent subsequence in
the STRONG topology (for Hilbert spaces: weak compactness + sequential weak compactness of
bounded sets). But:
- Weak relative compactness of L²(0,T;L²(B_k)) sequences is AUTOMATIC (Hilbert space, bounded
  sequences are weakly relatively compact). This is Banach–Alaoglu for Hilbert spaces.
- STRONG compactness (which is what the axiom asserts) requires ADDITIONAL structure — this
  is precisely the Aubin–Lions content. There is NO shortcut that avoids it.

**Alternative: Use the existing `spatial_compactness_R3` MORE DIRECTLY.**

`spatial_compactness_R3` (proved) already extracts a subsequence ρ converging in L²(B_R) for
EACH R, for a.e. t. The issue is integrating this OVER t (the Bochner L²(0,T; ...) norm).

**If** the spatial compactness held UNIFORMLY in t (i.e., the convergence of ball-restrictions
was uniform in t, not just for a.e. t), THEN:
  eLpNorm(restrictToBall k (galSeq(ψ(ρ n)).u − g_k, 2, vol.restrict [0,T])
  = (∫_0^T ‖restrictToBall k (galSeq(ψ(ρ n)).u t − g_k t)‖² dt)^{1/2}
  ≤ √T · sup_t ‖restrictToBall k (galSeq(ψ(ρ n)).u t − g_k t)‖ → 0.

This would work! And the uniform convergence follows from the Arzelà–Ascoli theorem (Component
III above) IF we have time equicontinuity (A1).

So the route IS: (spatial precompactness via FK) + (time equicontinuity via A1) → (Arzelà–Ascoli
→ uniform convergence) → (Bochner L² convergence by domination). This is the SAME route as
the sub-lemma task list above. There is no shortcut that avoids A1.

### One-PR tractability call

**TRACTABLE AS A THIN SWAP in one PR (2–3 weeks of lean-coder + lean-prover work), provided:**

1. A1 (`galerkin_uniform_time_modulus`) is added as a marked axiom after Codex soundness review.
2. The Arzelà–Ascoli chain (B1–D2) is proved (estimated ~400–600 lines).
3. The current `axiom galerkin_spacetime_precompact_R3` is replaced by `theorem galerkin_spacetime_precompact_R3` proved from A1 + the chain.

The net result is a GENUINE thin swap: same mathematical content, but decomposed into:
- One thin axiom (A1: equicontinuity, a standard hypothesis of Simon's theorem), and
- A proved chain (B–E: Arzelà–Ascoli + Bochner-norm-from-uniform reduction).

**NOT tractable as full axiom removal in one PR:** Removing A1 would require proving the
trilinear Sobolev estimate `|b(u,v,w)| ≤ C·‖u‖_{H¹}·‖v‖_{L²}·‖w‖_{L²}` for the abstract
`R3NSForms.b`, which is absent from `R3NSForms` and would require adding it as a new field
or proving it from `b_galerkin` (the Schwartz pin) — a significant interface change that
should be its own issue.

### If no axiom is acceptable

If the project's "no new axiom" constraint applies, the ONLY honest verdict is:

  `galerkin_spacetime_precompact_R3` is the GENUINE MONTHS-CLASS CORE — the irreducible
  Mathlib-absent content of the Aubin–Lions–Simon theorem. It cannot be discharged without
  either a Lean formalization of Simon's compactness theorem or an enhancement of the
  `R3NSForms`/`GalerkinSolutionData_R3` interface to carry the V* time-derivative bound.

---

## 10  Files to create or touch

All changes are in `LerayHopf/R3/ArzelaAscoliTime.lean`. No new files are needed.

**Dependency order of changes:**

1. Add `galerkin_uniform_time_modulus` axiom (after Codex review of statement).
2. Prove B1 (`galSeq_restrictBall_continuous`) — uses `galerkin_curve_continuous` + `continuous_restrictToBall'`.
3. Prove B2 (`galSeq_restrictBall_boundedContinuous`) — package into BCF type.
4. Prove B3 (`galSeq_ball_equicontinuous`) — from A1 + 1-Lipschitz of `restrictToBall k`.
5. Prove C1 (`steklovAvg_restrictBall_precompact`) — from FK `LocalRellichInput` + `steklovAvg_memH1` + `steklovAvg_norm_le_u0`.
6. Prove C2 (`galSeq_restrictBall_pointwisePrecompact`) — from C1 + A1 (1/2-ε argument).
7. Prove D1 (`perBall_BCF_subseq_exists`) — from B2 + B3 + C2 + `BoundedContinuousFunction.arzela_ascoli`.
8. Prove D2 (`uniform_conv_implies_eLpNorm_tendsto`) — pure computation.
9. Prove E1: change `axiom galerkin_spacetime_precompact_R3` → `theorem galerkin_spacetime_precompact_R3 := ...` using A1 + D1 + D2.

---

## 11  Definition of done

The milestone is complete when:

- `axiom galerkin_spacetime_precompact_R3` no longer appears in the codebase (replaced by `theorem`).
- `galerkin_uniform_time_modulus` appears exactly once with a same-line `-- ALLOW_AXIOM:` marker.
- `lake build` passes on `LerayHopf/R3/ArzelaAscoliTime.lean` and all downstream files.
- No new unmarked `sorry` is introduced.
- `scripts/check-axioms-live.sh` reports `galerkin_uniform_time_modulus` (not `galerkin_spacetime_precompact_R3`) in the project axiom count.

**Must-prove targets (sorry-free):**
- B1, B2, B3, C1, C2, D1, D2, E1.

**Scaffold-only / residual:**
- A1 (`galerkin_uniform_time_modulus`) — marked axiom, not a sorry, may carry ALLOW_AXIOM.

---

## 12  Recommended first task for lean-coder

**Task:** Add `galerkin_uniform_time_modulus` axiom to `LerayHopf/R3/ArzelaAscoliTime.lean`
with the exact signature in §7 and an `-- ALLOW_AXIOM:` marker, then request
`/codex:adversarial-review` on the statement before any proof bodies are attempted.

Simultaneously, lean-coder should prove B1 (`galSeq_restrictBall_continuous`) as a
1–5 line proof using `galerkin_curve_continuous` (already in `AubinLionsLimitPassage.lean`)
composed with `continuous_restrictToBall'` (already in `ArzelaAscoliTime.lean`). This is
the dependency-order first must-prove target and requires no new axioms.
