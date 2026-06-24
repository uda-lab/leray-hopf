# Task Contract: Issue #46 — Sound Route to `galerkin_spacetime_precompact_R3`

**Plan date:** 2026-06-23
**Author:** lean-planner (sound-route resope)
**Supersedes:** `docs/scratch/r46-precompact-plan.md` (prior plan proposed an UNSOUND thin swap)
**Status of prior plan:** REJECTED — see §1.

---

## 0 Current repo state (origin/main 9ac0f34)

`galerkin_spacetime_precompact_R3` is a live axiom in
`LerayHopf/R3/ArzelaAscoliTime.lean` (lines 99–134).

Its consumers in the same file are:
- `perBall_ae_subseq` (lines 765–800, **PROVED**, uses the axiom, does not prove it)
- `diag_ae_subseq` (lines 841–926, **PROVED**, calls `perBall_ae_subseq`)
- `u_lim_aestronglyMeasurable` (lines 939–964, **PROVED**, calls `diag_ae_subseq`)

`galerkinSpaceTimeExtraction_R3` in `AubinLionsLimitPassage.lean` (line 1400) is already a
**PROVED theorem** (issue #44), assembled from the axiom via the above proved chain. So
discharging the axiom directly discharges the whole stack.

---

## 1 Why the prior plan (`r46-precompact-plan.md`) is UNSOUND

The prior plan proposed `galerkin_uniform_time_modulus` as the replacement thin axiom:

```lean
axiom galerkin_uniform_time_modulus ... :
  ∀ ε, 0 < ε → ∃ δ, 0 < δ ∧ ∀ (n : ℕ) (s t : ℝ),
    s ∈ Icc 0 T → t ∈ Icc 0 T → |s - t| < δ →
    ‖((galSeq n).u s : L2VF_R3) - ((galSeq n).u t : L2VF_R3)‖ < ε
```

This is POINTWISE strong-L²(ℝ³) equicontinuity, uniform in n. The prior plan itself noted
(§7, "Revised Soundness Verdict") that this requires `‖u'_n‖_{L²(0,T;L²(ℝ³))} ≤ C`
uniformly in n — a bound from `u_ode` that requires the 3D Sobolev trilinear estimate
`|b(u,u,w)| ≤ C·‖u‖_{H¹}·‖u‖_{L²}·‖w‖_{L²}` not available from `R3NSForms.b_bound`
(which is Schwartz-test only). The prior plan then says this is the "same obstruction" that
caused `galerkin_equicontinuity_from_ODE` to be deleted as UNSOUND (per the Codex P1
soundness fix described in the file header at line 11–17).

Concretely: pointwise-in-time L²(ℝ³) equicontinuity requires a POINTWISE bound on
`‖u'_n(r)‖_{L²}`. The ODE gives only a DUAL NORM bound in V*_n with n-dependent
norm-equivalence constants (L²-vs-V* equivalence on V_n grows with n). This is NOT
n-uniformly bounded in L²(ℝ³) from the available data.

**The prior axiom A1 asserts exactly what the deleted unsound axiom asserted, renamed.**
DO NOT propose it.

---

## 2 What the SOUND Simon-theorem hypothesis actually is

The classical Simon (1986) / Aubin–Lions theorem has two n-uniform hypotheses:

**H1 (spatial):** The sequence is uniformly bounded in L²(0,T; V), where V ↪↪ H is compact.
In our case: `∫₀ᵀ viscousFormSq_R3 ν (u_n t) dt ≤ ½‖u₀‖²` (this is `reg_bound`, PROVED).

**H2 (time, integrated):** The INTEGRATED time-translation modulus goes to zero uniformly:
`∫₀^{T−h} ‖τ_h u_n − u_n‖²_{H} dt → 0` as `h → 0`, uniformly in n.

In our setting, H becomes L²_loc(ℝ³) (or L²(B_k)), and τ_h is time-translation.
This is the INTEGRATED (L²-in-time) modulus, NOT pointwise.

**Why H2 is SOUND for the Galerkin sequence:** The standard derivation is:
- From `u_hasDeriv`: τ_h u_n(t) − u_n(t) = ∫_t^{t+h} u'_n(r) dr (Bochner FTC).
- Squaring and integrating over t:
  `∫₀^{T-h} ‖τ_h u_n(t) − u_n(t)‖²_{V*} dt ≤ h · ∫₀^T ‖u'_n(r)‖²_{V*} dr`.
- From `u_ode` + `reg_bound` + `energy_bound`, the dual-norm bound
  `∫₀^T ‖u'_n(r)‖²_{V*} dr ≤ C` holds uniformly in n — the key: here V* is the DUAL of V
  (NOT the L²-norm), so the trilinear Sobolev embedding is NOT needed.
  The Stokes term gives `‖(Stokes u'_n)‖_{V*} ≤ C · ‖u_n‖_V` (bounded by `reg_bound`).
  The convection term `|b(u,u,w)| ≤ C · ‖u‖_V · ‖u‖_{L²} · ‖w‖_V` (3D GN), which gives
  `‖B(u,u)‖_{V*} ≤ C · ‖u‖_V · ‖u‖_{L²}` — n-uniform by `reg_bound` + `energy_bound`.
- The H2 norm is then in H = L²(B_k) (not V*), but the ball restriction is compact
  (Rellich), so local V*-equicontinuity → local L²(B_k)-equicontinuity via Rellich.

**BUT**: even this route requires the trilinear estimate `|b(u,u,w)| ≤ C ‖u‖_V ‖u‖_{L²} ‖w‖_V`
for `w ∈ V_n`, which is a 3D Sobolev embedding fact NOT in `R3NSForms.b_bound`.

**The integrated hypothesis IS weaker than pointwise**, but the PROOF of even the integrated
modulus from current `GalerkinSolutionData_R3` data hits the same trilinear Sobolev wall.

---

## 3 Sound decomposition decision

### Option A: Abstract integrated-modulus axiom (integrated Simon hypothesis)

State the INTEGRATED time-translation modulus as an abstract axiom:

```lean
-- ALLOW_AXIOM: integrated time-translation modulus for Galerkin curves on B_k;
-- content = Simon (1986) Theorem 1 hypothesis (H2); TRUE for Galerkin NS
-- via ODE dual-norm estimate + Rellich; NOT provable from current R3NSForms.b_bound.
axiom galerkin_integrated_time_modulus
    (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T) (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n) (k : ℕ) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ (n : ℕ) (h : ℝ), 0 < h → h < δ →
      eLpNorm
        (fun t => restrictToBall k ((galSeq n).u (t + h) : L2VF_R3) -
                  restrictToBall k ((galSeq n).u t     : L2VF_R3))
        2 (volume.restrict (Set.Icc (0 : ℝ) (T - h))) < ENNReal.ofReal ε
```

This is the CORRECT Simon hypothesis H2. It is:
- SOUND: the integrated modulus IS true for Galerkin NS (standard, Temam III.2.1, Simon §3).
- WEAKER than `galerkin_spacetime_precompact_R3` (it is only a hypothesis of Simon, not its conclusion).
- NOT the pointwise modulus (the quantifier is `eLpNorm ... 2 (vol.restrict [0,T-h])`, not `∀ s t`).

Then prove that Option A + the Mathlib Arzelà–Ascoli / Simon chain → the current axiom.

### Genuine reduction vs. axiom reshuffling — HONEST VERDICT

**This is AXIOM RESHUFFLING, not genuine reduction.**

Argument:
1. `galerkin_spacetime_precompact_R3` asserts: ∃ ρ, ρ-subsequence converges in L²(0,T;L²(B_k)).
2. Option A asserts: for all n, the L²(0,T−h;L²(B_k)) norm of τ_h u_n − u_n → 0 as h → 0.
3. To derive (1) from (2), you need Simon's theorem: (H1 spatial bound) + (H2 time modulus) → precompact in L²(0,T;L²(B_k)). This theorem is ABSENT from Mathlib.

Without Simon's theorem in Mathlib, the "proof" of (1) from (2) would require axiomatizing Simon's theorem itself, producing a SECOND new axiom. The total axiom count would be:
- Remove: `galerkin_spacetime_precompact_R3` (1)
- Add: `galerkin_integrated_time_modulus` (1) + abstract Simon's theorem (1) = 2

Net: +1 axiom. This is axiom reshuffling into a WORSE position.

**The only genuine reduction route is Simon's theorem in Lean — see §4.**

### Option B: Status quo — one clean axiom remains

The CURRENT axiom `galerkin_spacetime_precompact_R3` is already:
- Abstract and scheme-independent (takes `𝔊`, `F` as parameters).
- Local (per-ball, no global L²(ℝ³) claim).
- Refine-capable (takes input subsequence ψ).
- Correctly labelled with `ALLOW_AXIOM` and full mathematical justification.
- Reusable for torus #23.

It IS the cleanest single-axiom statement of the Simon-theorem conclusion for this project.
The prior plan's alternative splitting into A1 + Arzelà–Ascoli was viable only if the
integrated modulus were itself easier to prove from Mathlib — and it is not (same trilinear
Sobolev wall).

---

## 4 Simon's theorem: Mathlib building blocks and size estimate

**Theorem to build (Simon 1986, J. London Math. Soc.):**
Let B ↪ X be compact, B ↪ Y continuous. If {f_n} is bounded in L^p(0,T;B) and the
integrated time-translation modulus in L^p(0,T;Y) → 0 uniformly, then {f_n} is
precompact in L^p(0,T;X).

For the project: B = H¹(B_k), X = L²(B_k), Y = L^{4/3}(B_k) (or V* via duality).

**Mathlib building blocks actually present:**

| Mathlib decl | Location | Role in Simon |
|---|---|---|
| `MeasureTheory.Lp.isSeqCompact_closedBall_of_isUniformlyIntegrable` | `Mathlib.MeasureTheory.Function.UniformIntegrable` | If equiintegrable + tight → Lp precompact. Closest Mathlib result, but: (a) requires tightness (measure-finite domain: [0,T] qualifies), (b) works for scalar p-integrable functions, NOT Bochner-valued; (c) the hypothesis is equiintegrability (Dunford–Pettis), not time-translation modulus. |
| `MeasureTheory.ArzelaAscoli` / `BoundedContinuousFunction.arzela_ascoli₂` | `Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli` | Arzelà–Ascoli in BCF(compact, metric); can give uniform convergence on [0,T] if curves are continuous and equicontinuous. Would require the pointwise equicontinuity (UNSOUND for us). |
| `Metric.totallyBounded_iff`, `IsCompact.isSeqCompact` | `Mathlib.Topology.MetricSpace.Basic` | Extract subsequence from totally bounded / compact set. |
| `MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm` | `Mathlib.MeasureTheory.Function.ConvergenceInMeasure` | eLpNorm → 0 implies convergence in measure. Used in the current `perBall_ae_subseq` (already proved). |
| `MeasureTheory.TendstoInMeasure.exists_seq_tendsto_ae` | `Mathlib.MeasureTheory.Function.ConvergenceInMeasure` | Already used in `perBall_ae_subseq`. |
| `MeasureTheory.exists_stronglyMeasurable_limit_of_tendsto_ae` | `Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable` | Already used in `galerkin_weakLimit_R3`. |

**What is ABSENT from Mathlib (as of 2026-06-23):**

1. **Bochner-valued Aubin–Lions / Simon compactness in L^p(0,T;X)** — no direct analogue.
2. **Riesz–Kolmogorov / Fréchet–Kolmogorov in L^p(0,T;X) Bochner** — the project has FK for
   spatial L²(ℝ³) functions (`FrechetKolmogorovInput`, `frechetKolmogorov_holds`), but not for
   the TIME direction in Bochner spaces.
3. **L²(0,T;L²(B_k)) ≅ L²([0,T]×B_k) product iso** — no Lean proof of this Bochner-product iso.
4. **Dual-space pairing for Gelfand triple V ↪ H ↪ V*** in Mathlib adequate for the time
   derivative bound — partial only (`GelfandTriple.lean` in this project is bespoke).

**Size estimate for a Lean Simon's theorem proof:**

Building a genuine sorry-free Simon's theorem in Lean requires:
- (S1) Product measure / Fubini for L²(0,T;L²(B_k)) ↔ L²([0,T]×B_k): ~200 lines.
- (S2) An FK / Riesz–Kolmogorov result for L²(product measure, [0,T]×B_k): requires
  BOTH spatial (already have) AND time translation control. The time-translation modulus
  (H2) must be threaded into the product-space FK argument: ~300-400 lines.
- (S3) Compactness conclusion: totally bounded → compact → sequentially compact → subsequence:
  already available via `IsCompact.isSeqCompact` chain once totallyboundedness is proved: ~100 lines.
- (S4) Connecting the abstract theorem to the Galerkin data (proving H1 from `reg_bound`,
  proving H2 from `u_ode` + trilinear Sobolev): the trilinear Sobolev estimate
  `|b(u,u,w)| ≤ C ‖u‖_{H¹} ‖u‖_{L²} ‖w‖_{H¹}` is not in `R3NSForms.b_bound`; adding it
  as a new `R3NSForms` field or proving it from `b_galerkin` (Schwartz pin) is substantial
  (~200-400 lines depending on approach, plus an interface decision).

**Total estimated size:** 800–1100 lines across 3–4 new files.
**Timeline:** 2–4 months of focused lean-prover work (multiple PRs).
**This is NOT weeks-bounded in a single PR.**

The irreducible core is S2 (time-direction FK on product measure) — this requires genuinely
new analysis not present in Mathlib. S4 requires a new `R3NSForms` interface field. Both are
non-trivial Lean formalization research efforts.

---

## 5 Smallest genuinely-provable first step (one bounded PR)

The smallest sorry-free contribution that advances toward eventual discharge of
`galerkin_spacetime_precompact_R3` without being axiom-reshuffling is:

**PR-46-A: Add `R3NSForms.trilinear_sobolev_bound` as a new marked axiom and prove H2 from it.**

```lean
-- This field would be added to R3NSForms, OR as a separate axiom:
-- ALLOW_AXIOM: 3D trilinear Sobolev bound; content = H¹(ℝ³) ↪ L⁶(ℝ³) + Hölder;
-- TRUE (3D Sobolev embedding, standard); NOT provable from current R3NSForms.b_bound.
axiom r3_trilinear_sobolev
    (F : R3NSForms 𝔊) (u v w : L2VF_R3)
    (hu : MemH1 u) (hv : MemH1 v) (hw : MemH1 w) :
    |F.b u v w| ≤ C * ‖u‖_{H¹} * ‖v‖_{L²} * ‖w‖_{H¹}
```

Then prove:

```lean
-- Name: galerkin_dual_time_deriv_bound
-- Informal: ∫₀ᵀ ‖u'_n(t)‖²_{V*} dt ≤ C(ν, ‖u₀‖)   uniformly in n
-- Proof: from u_ode + u_hasDeriv + trilinear_sobolev + reg_bound + energy_bound.
-- File: LerayHopf/R3/GalerkinTimeDeriv.lean (new, ~100 lines)
theorem galerkin_dual_time_deriv_bound
    (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T) (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n) (n : ℕ) :
    eLpNorm (fun t => r3_time_deriv 𝔊 F ν u₀ galSeq n t) 2
      (volume.restrict (Set.Icc 0 T)) ≤ C n ∧ ∃ C₀, ∀ n, C n ≤ C₀
```

This is a GENUINE reduction: it isolates the one missing trilinear estimate as a thin
Sobolev axiom (provable from the 3D Sobolev embedding, which IS a Mathlib frontier but a
cleaner and more reusable one), and from it derives the concrete H²(dual) time-derivative
bound on the Galerkin sequence. This PR would:
- Add one thin Sobolev axiom (scheme-independent, reusable).
- Prove the Galerkin dual-norm time-derivative bound sorry-free.
- NOT discharge `galerkin_spacetime_precompact_R3` (that requires Simon's theorem).
- Advance the plan toward eventual discharge by closing the first gap in the H2 proof.

**Estimated size:** ~150 lines in one new file. **Bounded and completable in one PR.**

However, even this step does NOT reduce the current axiom count (it adds a new axiom for
trilinear Sobolev, then proves a lemma from it). It advances the PLAN but not the count.

---

## 6 Genuine-reduction verdict

**Blunt assessment:** There is NO route in the current Mathlib that allows discharging
`galerkin_spacetime_precompact_R3` without either:

(a) Formalizing Simon's compactness theorem in Lean (800–1100 lines, 2–4 months, multiple PRs),
    which itself requires a time-direction FK result absent from Mathlib, OR

(b) Extending `R3NSForms` with the 3D trilinear Sobolev bound AND then formalizing
    the integrated modulus calculation AND Simon's theorem (same end state as (a) with
    a preparatory PR for the Sobolev bound).

**Any "thin swap" that replaces the current axiom with an "integrated time-translation modulus"
axiom plus an "abstract Simon theorem" axiom is reshuffling: 1 axiom → 2 axioms.**

The current single axiom `galerkin_spacetime_precompact_R3` IS the minimal, cleanest, most
abstract statement of what Mathlib cannot supply. It is already:
- Scheme-independent.
- Local (per ball).
- Refine-capable (correct form for Cantor diagonalization).
- Correctly ALLOW_AXIOM marked with full justification.
- Reusable for torus #23 (per the file header docstring).

The right project-level decision is: **leave the axiom as-is** and track Simon's theorem as
a separate long-horizon Mathlib contribution issue, NOT a thin swap within issue #46.

---

## 7 Definition of done for issue #46 (honest scope)

Issue #46 (`galerkin_spacetime_precompact_R3`) is the **genuine months-class core** of the
Bochner Aubin–Lions machinery. Its discharge requires:

**Phase 1 (preparatory, multiple PRs):**
- P1-A: Add `r3_trilinear_sobolev` as a marked axiom; prove `galerkin_dual_time_deriv_bound`.
- P1-B: State and prove `galerkin_integrated_time_modulus` from P1-A data (derives H2 in V*-norm then lifts to L²(B_k) via Rellich).
- P1-C: Formalize the product-measure FK for L²([0,T]×B_k) — the time-direction component.

**Phase 2 (Simon's theorem):**
- P2-A: Abstract Simon's theorem in Lean: (H1 spatial) + (H2 integrated modulus) → precompact in L^p(0,T;X).
- P2-B: Apply Simon's theorem to the Galerkin sequence to discharge `galerkin_spacetime_precompact_R3`.

Total: 5 PRs minimum, 2–4 months estimated. Each phase is a prerequisite for the next.

**The milestone is done when:**
- `axiom galerkin_spacetime_precompact_R3` no longer appears in the codebase.
- `#check @galerkin_spacetime_precompact_R3` returns a `theorem` (not `axiom`).
- No new `axiom` or `opaque` in the discharged files beyond those introduced in P1-A/P1-B
  (and those must each carry `ALLOW_AXIOM` markers).
- `lake build` passes on the full `LerayHopf` namespace.

---

## 8 Codex review point (if any PR is opened)

Any PR that modifies `galerkin_spacetime_precompact_R3` or introduces a replacement axiom
MUST pass `/codex:adversarial-review --effort xhigh` on the statement BEFORE proof bodies
are attempted. The specific check: does the new statement avoid asserting strong-L²(ℝ³)
pointwise equicontinuity? (The deleted `galerkin_equicontinuity_from_ODE` test case.)

---

## 9 Recommended first task for lean-coder

**Do NOT open a PR that proposes `galerkin_uniform_time_modulus` (the prior plan's A1).**

If the project wants to make any progress on issue #46 within a single PR:

**Recommended PR:** `GalerkinTimeDeriv.lean` — add `r3_trilinear_sobolev` as a marked axiom,
define `r3_time_deriv_functional` (the Galerkin time-derivative as a V*-valued measurable
function), and prove `galerkin_dual_time_deriv_bound` (the n-uniform V*-norm bound from
`u_ode` + `r3_trilinear_sobolev` + `reg_bound` + `energy_bound`).

This:
- Is a GENUINE sorry-free proof (real proved content given the Sobolev axiom).
- Is the first link in the chain toward H2 and Simon.
- Keeps the current `galerkin_spacetime_precompact_R3` axiom INTACT (no unsound swap).
- Is bounded to ~150 lines in one PR.
- Must first pass Codex review on the `r3_trilinear_sobolev` statement.

**Alternatively, if no new axiom is acceptable:** close issue #46 as "long-horizon / requires
upstream Mathlib formalization of Simon's compactness theorem" and track as a separate research
issue. This is the honest timeline call.
