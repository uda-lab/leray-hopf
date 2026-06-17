# Task Contract — P2: Aubin–Lions time compactness + nonlinear limit passage (PARTIAL, axiom-free reduction)

> # ⚠ AUTHORITATIVE SHIPPED STATE (2026-06-17) — READ THIS; IT OVERRIDES EVERYTHING BELOW
> P2 shipped as an **honest PARTIAL**. This banner + §8 are the single active source of truth.
> **All of §0–§7 and §9 below are HISTORICAL PRE-SHIPMENT PLANNING written assuming C2/E1 would
> close; they are SUPERSEDED and must NOT be read as the delivered state.** In particular the
> "read-first"/feasibility/lean-prover-split/recommended-task text below over-optimistically
> describes `aubinLionsPackage_R3_of_timeCompactness` (C2), `kineticEnergy_lsc_bound` (E1), the
> dropped `GoodRepresentativeInput`/`galStates_admissible`/`galerkinLimitPassage_R3_of_goodRep`,
> and "only non-proved input is `TimeCompactnessInput`" — all of that is OBSOLETE.
>
> **Actual shipped state (authoritative):**
> - **PROVED, sorry-free, `#print axioms` = `[propext, Classical.choice, Quot.sound]`:**
>   `spatialInput_R3_of_localRellich` (S1), `bForm_tendsto_of_strongL2` (N1), and the private
>   Steklov building blocks (`galerkin_curve_continuous`, `steklovAvg`, `steklovAvg_norm_le_u0`,
>   `steklovAvg_approx`, `galerkin_norm_le_u0`).
> - **OPEN (`sorry` + truthful `-- TODO:`):** `kineticEnergy_lsc_bound` (E1) — statement was
>   **corrected** at the Codex gate from the smuggling `∀ t` pointwise form to the honest
>   `∀ᵐ t` a.e. form (NOT byte-intact), still open (package lacks time-measurability of `u`);
>   `aubinLionsPackage_R3_of_timeCompactness` (C2) — statement **byte-intact**, open; the
>   pointwise-sample route is unsound but the **Steklov averaging route is viable** (open
>   engineering: δ-mesh diagonalization + H¹-Jensen on the average + Bochner-average
>   measurability + boundary strip `(T−δ,T]`).
> - **DROPPED** (never shipped): `GoodRepresentativeInput`, `galerkinLimitPassage_R3_of_goodRep`,
>   `galStates_admissible` (see ADDENDUM).
> - Zero new axioms; `AxiomaticClosure.lean` not edited; `exists_lerayHopf_r3` unchanged
>   (6 project + 3 kernel, no `sorryAx`); preflight green.
>
> See §8 (rewritten) and the ADDENDUM for details. Everything between here and §8 is archival.

**Milestone:** `p2-aubin-lions`
**File deliverable:** `LerayHopf/R3/AubinLionsLimitPassage.lean` (new, standalone)
**Branch:** `autorun/p2-aubin-lions`
**Plan reference:** `/Users/uda/.claude/plans/p2-p3-witty-rain.md` (P2 section, lines 88–123);
target axioms `aubin_lions_R3` (`AxiomaticClosure.lean:444–460`, package `406–428`) and
`galerkin_limit_passage_R3` (`AxiomaticClosure.lean:482–501`).
**Models to mirror:** `LerayHopf/R3/SpatialCompactness.lean` (P3 — standalone, isolated
`structure` hypothesis, diagonal-over-balls, `#print-axioms`-clean), `LerayHopf/R3/GalerkinScheme.lean`
(P5 — bundled-structure frontier), `LerayHopf/R3/TrilinearEstimate.lean` (R3-d — `b`-bound under L²).

---

## 0. Scope decision (honest partial — read first)

This milestone is an explicitly **PARTIAL** substantiation, fixed by the approved plan:
prove the *reduction/combination* axiom-free and isolate the **Bochner-time-compactness**
frontier as ONE clean hypothesis; name precise `-- TODO:`s for genuinely irreducible gaps.
We do NOT remove either axiom; we add sibling proved lemmas in a new standalone file,
exactly as P3/P5/R3-d did. The connection to the axioms is **semantic** (the deliverables'
conclusions match the axiom bodies up to the added hypothesis binders).

**What becomes a proved lemma (axiom-free):**
- the **combination** "P3 local spatial compactness + an isolated time-equicontinuity
  hypothesis ⇒ `AubinLionsPackage_R3`" (the `strong_convergence` field), via an
  Arzelà–Ascoli-in-time / diagonal-over-balls argument;
- the discharge of the `spatial` input of `aubin_lions_R3` by **reusing P3's
  `localCompactness_R3_of_ballCompact`** (modulo P3's own `LocalRellichInput`);
- of the 5 `galerkin_limit_passage_R3` conclusions: the **energy inequality (by lsc)** and
  the **nonlinear `b`-term passage under strong L² convergence** (using `b_bound`).

**What stays an isolated `structure` hypothesis (not an axiom):**
- `TimeCompactnessInput` — uniform time modulus / equicontinuity in L² of the Galerkin
  curves (the vector-valued-Sobolev packaging mathlib lacks);
- `GoodRepresentativeInput` — the weak-time-derivative / a.e.-good-representative selection
  feeding the WeakFormNS test-pairing identity (mathlib lacks `W^{1,p}(0,T;X)` and the
  Lions–Magenes trace/representative theory).

**What stays a precise `-- TODO:` (genuinely irreducible this cycle):** see §3 Tier L and §8.

---

## 1. Feasibility verdict (per axiom's content)

### 1.1 `aubin_lions_R3` (→ `AubinLionsPackage_R3`)

**Verdict: HIGHLY REACHABLE as a reduction.** The package has only one non-trivial field,
`strong_convergence` (LOCAL space-time L²(0,T; L²(B_R)) convergence on every ball). The
spatial half is already factored out as the `spatial` hypothesis whose type is **byte-identical**
to P3's `localCompactness_R3_of_ballCompact` conclusion (verified against
`AxiomaticClosure.lean:449–459` vs `SpatialCompactness.lean:1044–1055`). So:

- The **spatial input is dischargeable concretely** by P3 (modulo P3's `LocalRellichInput`).
- The remaining gap is *purely the time direction*: upgrading per-(a.e.)-time spatial
  compactness to space-time strong compactness. mathlib has **no** `W^{1,p}(0,T;X)`, **no**
  vector-valued weak time derivative, and **no** Aubin–Lions lemma (confirmed by grep:
  `Mathlib/Topology/UniformSpace/Ascoli.lean` provides only abstract `ArzelaAscoli.*`
  compactness-of-closure results phrased via uniform structures / `isClosedEmbedding`,
  not a Bochner time-compactness theorem). This is the genuine frontier → `TimeCompactnessInput`.

**Bottom line:** the combination lemma producing `AubinLionsPackage_R3` from `galSeq` +
`TimeCompactnessInput` (+ P3 spatial, itself from P3's `LocalRellichInput`) is provable
axiom-free. The single honest non-proved input is the time equicontinuity.

### 1.2 `galerkin_limit_passage_R3` (5 conclusions)

**Verdict: PARTIALLY REACHABLE.** Conclusion-by-conclusion:

| # | Conclusion | Verdict | Route |
|---|---|---|---|
| (a) | a.e.-equality `u =ᵐ alPkg.u` on `Icc 0 T` | REACHABLE (trivial) | take `u := alPkg.u`, then `=ᵐ` is `ae_eq_refl`. |
| (b) | `WeakFormNS ν T (r3Evolution 𝔊 F) u` | **NOT reachable axiom-free** | needs the weak-time-derivative identity `∫ -⟪u,w⟫ψ' + ψ(ν·visc + b) = 0` recovered as the limit of the Galerkin ODE `u_ode`; the time-derivative-to-test-function transfer (IBP in time against `ψ`) is exactly the missing `W^{1,p}(0,T;X)` machinery. Isolate via `GoodRepresentativeInput.weakForm`. The `b`-term *passage* (limit of `F.b (uₙ) (uₙ) w → F.b u u w` under strong L²) IS provable via `b_bound` and feeds this — see Tier N. |
| (c) | energy inequality on `[0,T]` (by lsc) | REACHABLE | `galSeq n` carries `energy_bound` (`AxiomaticClosure.lean:343`) and `reg_bound` (`:349`); lower-semicontinuity of the L² norm under (weak/strong) limit + Fatou for the dissipation integral. The norm-lsc piece is provable from strong L² convergence on balls + uniform bound; the dissipation-Fatou piece needs the limit's energy class. Partly reachable; the dissipation lsc requires `GoodRepresentativeInput.energyClass`. See Tier E. |
| (d) | initial trace `u t → u₀` as `t→0⁺` | **NOT reachable axiom-free** | needs strong-in-time continuity at 0 of the limit, again Bochner-time machinery + `𝔊.tendsto_id`. Isolate via `GoodRepresentativeInput.initialTrace`. |
| (e) | energy class (a.e. `memH1VF_R3` + integrable `viscousFormSq_R3 ν`) | **NOT reachable axiom-free** | the limit's H¹ regularity / dissipation integrability is the weak-L²(0,T;H¹) lower-closure, missing in mathlib. Isolate via `GoodRepresentativeInput.energyClass`. |

**Bottom line:** the genuinely-provable, axiom-free pieces of limit passage are: (a) the
representative choice, (c-partial) the kinetic-energy-lsc half, and the **nonlinear `b`-term
passage lemma** (Tier N) that is the *reusable analytic core* `b_bound` enables. Conclusions
(b), (d), (e) and the dissipation-lsc half of (c) require the absent weak-time-derivative /
weak-L²(0,T;H¹) theory and are isolated into `GoodRepresentativeInput` fields (NOT axioms),
each with explicit Codex no-smuggle sign-off. Where even an honest hypothesis would be
indistinguishable from re-asserting the conclusion, we leave a precise `-- TODO:` (§8).

---

## 2. New file: `LerayHopf/R3/AubinLionsLimitPassage.lean`

### 2.1 Imports

```lean
import LerayHopf.R3.AxiomaticClosure     -- AubinLionsPackage_R3, GalerkinSolutionData_R3, r3Evolution, R3NSForms
import LerayHopf.R3.SpatialCompactness   -- localCompactness_R3_of_ballCompact, LocalRellichInput, restrictToBall, L2ballR3
import LerayHopf.R3.TrilinearEstimate    -- b-bound analytic core (convIntegralSchwartz_bound_*)
import Mathlib.MeasureTheory.Integral.Bochner.Set   -- set/interval integrals over balls
```

**Import-cycle audit (REQUIRED, Hard rule 10):**
- `R3.AxiomaticClosure` does **NOT** import this file, `R3.SpatialCompactness`, or
  `R3.TrilinearEstimate` (verified: `AxiomaticClosure.lean` imports `R3.Regularity` and
  `R3.GalerkinScheme` only; `SpatialCompactness.lean` is standalone, not imported by
  `AxiomaticClosure`). So importing `R3.AxiomaticClosure` here is acyclic.
- `R3.SpatialCompactness` is standalone (imports `R3.Regularity` + mathlib), and
  `R3.TrilinearEstimate` is a leaf under `R3.Domain`/`R3.DivergenceFree`. Importing both
  here adds no cycle.
- **This file is a leaf** (nothing imports it). It is the right place to reference
  `AubinLionsPackage_R3` AND reuse P3 — neither of which can reference the other.

Unlike P3 (which deliberately avoided importing `AxiomaticClosure` to stay maximally
standalone), P2 **must** import `R3.AxiomaticClosure` because its deliverables *produce*
`AubinLionsPackage_R3` and *consume* `GalerkinSolutionData_R3` — these live in
`AxiomaticClosure.lean` and there is no lighter module exposing them. This is a justified
heavy import (the only one).

### 2.2 Namespace / opens

```lean
namespace LerayHopf
open MeasureTheory Filter Topology Metric
```

### 2.3 Root build inclusion (REQUIRED — P5 lesson)

Add `import LerayHopf.R3.AubinLionsLimitPassage` to `LerayHopf.lean` (after the
`R3.SpatialCompactness` line, currently `LerayHopf.lean:51`). **lean-coder owns this edit.**

---

## 3. Declarations in dependency order

Naming: snake-case, mathematically descriptive, **no overclaim** (Hard rule 6 / No-overclaim).
The combination theorem name must NOT claim "Aubin–Lions" outright (it is conditional on the
isolated input); use `aubinLionsPackage_R3_of_timeCompactness` style.

### Tier H — the isolated time frontier hypothesis (coder)

**H1. `TimeCompactnessInput`** — scaffold-only (structure; the isolated frontier)

The minimal honest shape: a **uniform-in-`n` L² modulus of time-continuity** of the Galerkin
curves, at the granularity the combination consumes. The combination needs, per ball `R` and
per ε, a single time-shift modulus `δ` valid for ALL `n` simultaneously. The honest minimal
field:

```lean
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
  uniform_time_modulus : ∀ ε : ℝ, 0 < ε →
    ∃ δ : ℝ, 0 < δ ∧ ∀ (n : ℕ) (s t : Time),
      s ∈ Set.Icc (0 : ℝ) T → t ∈ Set.Icc (0 : ℝ) T → |s - t| < δ →
      ‖((galSeq n).u s : L2VF_R3) - ((galSeq n).u t : L2VF_R3)‖ < ε
```

Role: coder (structure + field signature only). No proof.
**No-smuggle audit (Codex Gate 1, the single most important):** confirm the field contains
NO subsequence index, NO limit curve `u`, NO `Tendsto`, NO ball-restricted space-time
integral, NO div-free conclusion, NO spatial compactness. It is a same-sequence uniform
time modulus, period. (Mirrors P5 `dense_span` / P3 `ballCompact` honesty review.)

### Tier S — discharge the spatial input via P3 (prover)

**S1. `spatialInput_R3_of_localRellich`** — must-prove (thin reuse wrapper)

```lean
/-- The `spatial` hypothesis required by the Aubin–Lions combination is exactly P3's
`localCompactness_R3_of_ballCompact`. Supplying P3's isolated input discharges it. -/
theorem spatialInput_R3_of_localRellich (B : LocalRellichInput) :
    ∀ (M : ℝ) (z : ℕ → L2VF_R3),
      (∀ n, z n ∈ L2Sigma_R3) → (∀ n, memH1VF_R3 (z n)) →
      (∀ n, ‖z n‖ ≤ M) → (∀ n, viscousFormSq_R3 1 (z n) ≤ M ^ 2) →
      ∃ (ψ : ℕ → ℕ) (g : L2VF_R3), StrictMono ψ ∧ g ∈ L2Sigma_R3 ∧
        ∀ R : ℝ, Filter.Tendsto
          (fun n => ∫ x in Metric.closedBall (0 : Domain3) R,
            ‖((z (ψ n)) x : EuclideanSpace ℝ (Fin 3)) - (g x : EuclideanSpace ℝ (Fin 3))‖ ^ 2
            ∂(volume : Measure Domain3))
          Filter.atTop (nhds 0)
```

Role: prover. Body: `exact localCompactness_R3_of_ballCompact B`. (One line — its purpose is
to make the reuse explicit and to give the combination lemma a clean spatial argument whose
type is the `aubin_lions_R3` `spatial` binder verbatim.)
Dep: `localCompactness_R3_of_ballCompact` (P3, `SpatialCompactness.lean:1044`).

### Tier C — combination: spatial + time ⇒ `AubinLionsPackage_R3` (prover; the core)

This is the heart of the milestone. It produces `AubinLionsPackage_R3.strong_convergence`.

**C1. `applyForall` plumbing — `galStates_admissible`** — must-prove (helper)

The Galerkin states `t ↦ (galSeq n).u t` are admissible inputs to the spatial compactness:
at each fixed time they satisfy the L²/H¹/viscous bounds. Package the per-time uniform bounds
from `energy_bound`, `reg_mem`, and a viscous bound derived from `reg_bound` (note: `reg_bound`
is a *time-integral* bound; the spatial compactness needs a *pointwise* `viscousFormSq ≤ M²`
bound, which is NOT directly available pointwise — see **gating note G1**).

```lean
/-- At a.e. fixed time, the Galerkin states are uniformly L²/H¹-bounded admissible inputs. -/
theorem galStates_admissible (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν T : ℝ) (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n) :
    ∀ t, (∀ n, ((galSeq n).u t : L2VF_R3) ∈ L2Sigma_R3) ∧
         (∀ n, memH1VF_R3 ((galSeq n).u t : L2VF_R3)) ∧
         (∀ n, ‖((galSeq n).u t : L2VF_R3)‖ ≤ ‖(u₀ : L2VF_R3)‖)
```

Role: prover. Sketch: membership in `L2Sigma_R3` is `((galSeq n).u t).2`; `memH1VF_R3` is
`(galSeq n).reg_mem t`; the L²-bound comes from `energy_bound` (for `t ≥ 0`) plus
`‖𝔊.P n u₀‖ ≤ ‖u₀‖` (projection is norm-nonincreasing — confirm `𝔊` carries this;
see G2). Take `M := ‖u₀‖`.
**Gating note G1 (the real obstruction to a fully-pointwise spatial application):** the
spatial compactness `localCompactness_R3_of_ballCompact` requires `viscousFormSq_R3 1 (z n) ≤ M²`
*pointwise in `n`* for a FIXED sequence. Applying it at a fixed time `t` to `z n := (galSeq n).u t`
needs a *time-pointwise* viscous bound `viscousFormSq_R3 1 ((galSeq n).u t) ≤ M²`, which the
data only provides in *time-integrated* form (`reg_bound`). The honest resolution is that the
combination does NOT apply spatial compactness at a single time; it applies it after a
**time-discretization / Aubin–Lions slicing** that the `TimeCompactnessInput` modulus enables
(equicontinuity reduces space-time compactness to compactness at finitely many sample times,
where the integrated bound gives an a.e. pointwise bound on a positive-measure set). This is
the genuine combinatorial content and is where the proof is non-trivial — flag prominently for
Codex Gate 2. If a fully rigorous slicing proof cannot be closed this cycle (likely — it is
the Aubin–Lions argument itself), the combination collapses to needing the time hypothesis to
carry slightly more (a per-sample-time viscous bound), OR a precise `-- TODO:` (§8). **The
planner's honest expectation: C2 below is at the edge of feasibility; see §3 Tier-C realism.**

**C2. `aubinLionsPackage_R3_of_timeCompactness`** — must-prove (THE combination deliverable)

```lean
/-- **Aubin–Lions package on ℝ³ from the isolated time-compactness input.**

Reproduces `aubin_lions_R3`'s conclusion (`AubinLionsPackage_R3`) axiom-free, conditional on
(i) P3's local spatial compactness (via `LocalRellichInput`) and (ii) the isolated uniform
time-equicontinuity `TimeCompactnessInput`. -/
theorem aubinLionsPackage_R3_of_timeCompactness
    (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T)
    (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n)
    (B : LocalRellichInput)
    (Htime : TimeCompactnessInput 𝔊 F ν T u₀ galSeq) :
    AubinLionsPackage_R3 𝔊 F ν T u₀ galSeq
```

Role: prover. The `strong_convergence` field (local space-time L²(0,T;L²(B_R)) on every ball)
is assembled by:
1. apply `spatialInput_R3_of_localRellich B` to extract, at a dense set of sample times, a
   common subsequence `φ` with ball-restricted spatial convergence (P3 gives per-fixed-sequence
   ball convergence; the diagonal-over-balls is already inside P3);
2. use `Htime.uniform_time_modulus` to upgrade convergence at sample times to convergence in
   space-time L²(0,T;L²(B_R)) (equicontinuity-in-time ⇒ the time-integral of the spatial
   error is controlled by the sample-time error + the modulus). This is the
   Arzelà–Ascoli-in-time step.
3. package `φ`, the limit curve `u`, and the `strong_convergence` `Tendsto`.

**Gating note G2 (mathlib reality check for the time-Ascoli step):** mathlib's
`ArzelaAscoli.*` (`Mathlib/Topology/UniformSpace/Ascoli.lean:418–496`) is phrased via uniform
structures and `isClosedEmbedding`/`compactSpace_of_*`; it is NOT a turn-key "equicontinuous +
pointwise-precompact ⇒ uniformly convergent subsequence" over `[0,T]→L²`. The prover should
**not** force the abstract Ascoli API; instead prove the space-time convergence DIRECTLY by an
ε/3 argument: partition `[0,T]` into `δ`-mesh sample times (from `Htime`), use P3 spatial
convergence at each (finitely many) sample, and the modulus to fill the gaps, then dominated/
bounded convergence for the time-integral. This is elementary but ~100–150 lines.

**Tier-C realism (planner's honest assessment):** C2 is the milestone's hardest provable
target and genuinely couples G1 (pointwise viscous bound at sample times) with G2 (the
ε/3 time-mesh argument). It is the actual Aubin–Lions reduction. There are two acceptable
outcomes per Hard rule 8:
  (i) **Full success:** C2 lands sorry-free with the two isolated hypotheses (`B`, `Htime`).
      This is the target.
  (ii) **Honest partial:** if the G1 sample-time pointwise viscous bound cannot be rigorously
      extracted from the integrated `reg_bound` (a real measure-theoretic subtlety: integrated
      bound ⇏ pointwise bound everywhere), then EITHER strengthen `TimeCompactnessInput` with a
      minimal extra field `sampleTime_viscous_bound` (a uniform pointwise viscous bound on a
      cofinite/dense sample set — Codex no-smuggle sign-off REQUIRED), OR leave C2's body with a
      precise `-- TODO: Aubin–Lions time-mesh: integrated reg_bound ⇏ pointwise viscous bound at
      sample times; needs a positive-measure selection lemma` and ship the rest. Do NOT weaken
      the `strong_convergence` conclusion shape.

### Tier N — nonlinear `b`-term passage (prover; the reusable analytic core)

**N1. `bForm_tendsto_of_strongL2`** — must-prove (the `b_bound` payoff)

```lean
/-- **Nonlinear convection term passes to the limit under strong L² convergence.**

For a fixed Schwartz div-free test `w`, if `uₙ → u` and `vₙ → v` strongly in L²(ℝ³) with a
uniform bound, then `F.b uₙ vₙ w → F.b u v w`. This is the analytic payoff of R3-d's
`b_bound` (bilinear L²-continuity of `b` in its first two slots for Schwartz tests). -/
theorem bForm_tendsto_of_strongL2 (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (w : L2Sigma_R3) (hw : IsSchwartzDivFree_R3 w)
    (uSeq vSeq : ℕ → L2Sigma_R3) (u v : L2Sigma_R3)
    (hu : Tendsto (fun n => ((uSeq n : L2VF_R3))) atTop (𝓝 (u : L2VF_R3)))
    (hv : Tendsto (fun n => ((vSeq n : L2VF_R3))) atTop (𝓝 (v : L2VF_R3))) :
    Tendsto (fun n => F.b (uSeq n) (vSeq n) w) atTop (𝓝 (F.b u v w))
```

Role: prover. Sketch: bilinearity (`b_add_*`, `b_smul_*`) + `b_bound w hw` gives
`|b uₙ vₙ w − b u v w| ≤ |b (uₙ−u) vₙ w| + |b u (vₙ−v) w| ≤ C(‖uₙ−u‖‖vₙ‖ + ‖u‖‖vₙ−v‖)`,
and `‖vₙ‖` is bounded (convergent ⇒ bounded), so the RHS → 0. **Fully axiom-free, uses only
the `R3NSForms` structure fields.** This is the most cleanly-reachable genuine analytic lemma
in the milestone and the concrete substantiation of "strong L² kills the nonlinear error".
Dep: `F.b_bound`, `F.b_add_1/2`, `F.b_smul_*` (`AxiomaticClosure.lean:207–229`),
`Tendsto`-bounded helpers.
**Note:** this is *global* strong L² convergence on its hypotheses; the `strong_convergence`
from C2 is *local* (ball-restricted). Bridging local→global for `b` uses the Schwartz rapid
decay of `w` (tail control), exactly the ε/3 tail argument P3 used for div-free closure
(`SpatialCompactness.lean:1000–1035`). If the time-integrated, local-to-global bridge proves
heavy, state N1 in the **global** form above (clean, reachable) and leave the local→global +
time-integral assembly into WeakFormNS as the isolated `GoodRepresentativeInput.weakForm`
hypothesis (so N1 remains a sorry-free reusable lemma even if (b) is not closed).

### Tier E — energy inequality (lsc half, prover)

**E1. `kineticEnergy_lsc_bound`** — OPEN (the reachable half of conclusion (c))

> **STATEMENT CORRECTED at the Codex statement gate (NOT byte-intact vs the original below).**
> The original pointwise target (`∀ t, 0 ≤ t → t ≤ T → …`, struck through below) was flagged
> by Codex as SMUGGLING: it asserts pointwise-in-time representative control of `alPkg.u t`
> that `AubinLionsPackage_R3` does not carry (the package gives only space-time local
> convergence; `alPkg.u` has no time-measurability field, and changing it on a null set leaves
> the package intact). Per Codex's recommendation the conclusion was WEAKENED to the honest
> **a.e.-in-time** form. E1 remains OPEN (`sorry`) even in the a.e. form — see §8.

Shipped (a.e.-corrected) signature:
```lean
/-- a.e.-in-time kinetic-energy bound at the Aubin–Lions limit (honest form; the original
pointwise form was smuggling per the Codex statement gate). OPEN: blocked because the package
carries no time-measurability for its limit `u`. -/
theorem kineticEnergy_lsc_bound (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν T : ℝ) (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n)
    (alPkg : AubinLionsPackage_R3 𝔊 F ν T u₀ galSeq) :
    ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      (1 / 2 : ℝ) * ‖(alPkg.u t : L2VF_R3)‖ ^ 2 ≤ (1 / 2 : ℝ) * ‖(u₀ : L2VF_R3)‖ ^ 2
```
Original pointwise target (SUPERSEDED — was smuggling, do not restore): the conclusion
~~`∀ t, 0 ≤ t → t ≤ T → ½‖alPkg.u t‖² ≤ ½‖u₀‖²`~~.

Role: prover. Sketch: each Galerkin state has `½‖uₙ t‖² ≤ ½‖𝔊.P n u₀‖² ≤ ½‖u₀‖²`
(`energy_bound` + projection bound); norm-lsc under the limit (local strong → a.e. → Fatou on
the full norm, OR weak-lower-semicontinuity of the norm) preserves the `≤`.
**Gating note G3:** the limit `alPkg.u` is only known to be a LOCAL space-time L² limit; the
*pointwise-in-time* kinetic-energy bound needs the limit at (a.e.) fixed time to be a weak/
strong L² limit of `uₙ t`. This is available a.e. via the `strong_convergence` field
(extract a.e.-time subsequence). The dissipation-integral half of conclusion (c)
(`+ ∫ viscousFormSq ≤ …`) requires the limit's energy class (conclusion (e)) and is therefore
**NOT** included here; it is folded into `GoodRepresentativeInput`. E1 delivers ONLY the
kinetic half, which is the honest reachable piece.

### Tier G — the residual good-representative hypothesis (coder)

**G1struct. `GoodRepresentativeInput`** — scaffold-only (structure; the second isolated frontier)

Bundles the limit-passage conclusions that require the absent weak-time-derivative /
weak-L²(0,T;H¹) theory. Each field is an honest *hypothesis about the Aubin–Lions limit*,
NOT a re-statement disguised as proof. Codex Gate 1 must sign off that these are genuine
analytic inputs (the missing Bochner-Sobolev pillars), not smuggled conclusions.

```lean
/-- Isolated residual frontier for limit passage: the weak-time-derivative / good-representative
content that mathlib's missing `W^{1,p}(0,T;X)` theory would supply. Each field corresponds to
a limit-passage conclusion NOT reachable axiom-free this cycle. -/
structure GoodRepresentativeInput (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν T : ℝ) (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n)
    (alPkg : AubinLionsPackage_R3 𝔊 F ν T u₀ galSeq) where
  /-- The limit satisfies the weak NS identity (weak-time-derivative limit of the Galerkin ODE;
  the b-term passage Tier N is the provable ingredient, the time-IBP is the missing piece). -/
  weakForm : WeakFormNS ν T (r3Evolution 𝔊 F) alPkg.u
  /-- Strong-in-time attainment of the initial datum (Bochner-time continuity at 0). -/
  initialTrace : Filter.Tendsto (fun t => (alPkg.u t : L2VF_R3))
    (nhdsWithin 0 (Set.Ici 0)) (nhds (u₀ : L2VF_R3))
  /-- Energy class: a.e. H¹ + integrable dissipation (weak-L²(0,T;H¹) lower-closure). -/
  energyClass :
    (∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc 0 T)), memH1VF_R3 (alPkg.u t : L2VF_R3)) ∧
    IntervalIntegrable (fun s => viscousFormSq_R3 ν (alPkg.u s : L2VF_R3))
      MeasureTheory.volume 0 T
  /-- Dissipation contribution to the energy inequality (lsc of the dissipation integral;
  the kinetic half is the proved `kineticEnergy_lsc_bound`). -/
  dissipationBound : ∀ t, 0 ≤ t → t ≤ T →
    (1 / 2 : ℝ) * ‖(alPkg.u t : L2VF_R3)‖ ^ 2 +
      ∫ s in (0 : ℝ)..t, viscousFormSq_R3 ν (alPkg.u s : L2VF_R3) ≤
    (1 / 2 : ℝ) * ‖(u₀ : L2VF_R3)‖ ^ 2
```

Role: coder. No proof.
**No-smuggle audit (Codex Gate 1):** these fields ARE close to the conclusion shapes by
necessity — that is honest (they are exactly the pieces mathlib cannot supply). The audit must
confirm: (1) they are presented as *hypotheses* (structure fields consumed as an argument),
NOT proved; (2) the file does NOT claim them as theorems; (3) the milestone's STATUS note and
the lemma docstrings explicitly state they are the isolated Bochner-time frontier; (4) the
*provable* pieces (Tier N b-passage, E1 kinetic-lsc) are genuinely proved and feed these,
proving the isolation is non-trivial. **If Codex judges that any field is so close to the
conclusion that bundling it adds nothing over the existing axiom, downgrade it to a precise
`-- TODO:` in the assembly lemma instead (see §8).**

### Tier P — limit-passage assembly (prover)

**P1. `galerkinLimitPassage_R3_of_goodRep`** — must-prove (assembly, conditional)

```lean
/-- **Galerkin limit passage on ℝ³ from the residual good-representative input.**

Reproduces `galerkin_limit_passage_R3`'s conclusion axiom-free, conditional on the isolated
`GoodRepresentativeInput`. The PROVED ingredients (a.e.-refl representative, kinetic-energy
lsc `kineticEnergy_lsc_bound`, b-term passage `bForm_tendsto_of_strongL2`) are assembled with
the isolated weak-time-derivative fields. -/
theorem galerkinLimitPassage_R3_of_goodRep
    (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T)
    (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n)
    (alPkg : AubinLionsPackage_R3 𝔊 F ν T u₀ galSeq)
    (G : GoodRepresentativeInput 𝔊 F ν T u₀ galSeq alPkg) :
    ∃ u : Time → L2Sigma_R3,
      (∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc 0 T)), u t = alPkg.u t) ∧
      WeakFormNS ν T (r3Evolution 𝔊 F) u ∧
      (∀ t, 0 ≤ t → t ≤ T →
        (1 / 2 : ℝ) * ‖(u t : L2VF_R3)‖ ^ 2 +
          ∫ s in (0 : ℝ)..t, viscousFormSq_R3 ν (u s : L2VF_R3) ≤
        (1 / 2 : ℝ) * ‖(u₀ : L2VF_R3)‖ ^ 2) ∧
      Filter.Tendsto (fun t => (u t : L2VF_R3)) (nhdsWithin 0 (Set.Ici 0)) (nhds (u₀ : L2VF_R3)) ∧
      ((∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc 0 T)), memH1VF_R3 (u t : L2VF_R3)) ∧
       IntervalIntegrable (fun s => viscousFormSq_R3 ν (u s : L2VF_R3))
         MeasureTheory.volume 0 T)
```

Role: prover. Body: `refine ⟨alPkg.u, ae_eq_refl _, G.weakForm, G.dissipationBound,
G.initialTrace, G.energyClass⟩`. The non-trivial content is in (i) Tier N / E being genuinely
proved and (ii) Codex confirming `GoodRepresentativeInput` is honest. The assembly itself is
mechanical — that is the point: the analytic value is in N1/E1, the isolation in the structure.
**The statement is byte-identical (modulo the added `G` binder) to `galerkin_limit_passage_R3`
(`AxiomaticClosure.lean:488–501`).** lean-coder: copy it from there and prepend the `G` binder.

### Tier L — irreducible-gap markers (only if needed)

If, per §3 Tier-C realism (ii) or the Codex Gate-1 verdict on `GoodRepresentativeInput`, a
field is judged a smuggled conclusion, replace it with a precise `-- TODO:` in the consuming
lemma naming the exact missing pillar (see §8 for the candidate messages). Do NOT weaken any
conclusion shape (Hard rule 3/8).

---

## 4. Module DAG position

```
R3/Domain.lean
  └── R3/DivergenceFree.lean ──┬── R3/TrilinearEstimate.lean ─────────────┐
                               └── R3/Regularity.lean                      │
                                     ├── R3/AxiomaticClosure.lean ─────────┤
                                     └── R3/SpatialCompactness.lean ───────┤
                                                                           ▼
                                              R3/AubinLionsLimitPassage.lean  [NEW — this PR, LEAF]
```
A leaf module importing `R3.AxiomaticClosure`, `R3.SpatialCompactness`, `R3.TrilinearEstimate`.
**No cycle:** none of those three import this file (verified §2.1). Added to root `LerayHopf.lean`.

---

## 5. Assumptions section (axioms)

**Zero new `axiom`/`opaque`/`constant`.** The two genuine frontiers are carried by the
**hypotheses** `TimeCompactnessInput` and `GoodRepresentativeInput` (explicit arguments),
exactly as P3's `LocalRellichInput`, R3-d's `hdiv`, P5's `SchwartzGalerkinBasis.dense_span`.
No `-- ALLOW_AXIOM` markers; no assumptions-section entry (a hypothesis is not an axiom).
Any residual genuinely-irreducible step is a `-- ALLOW_SORRY: <reason>` marked `-- TODO:`
(§8) inside an otherwise-intact statement, NOT an axiom and NOT a weakened conclusion.

---

## 6. Codex review points (orchestrator-run `/codex:adversarial-review --effort xhigh`)

**Gate 1 — statement block (BEFORE proofs), focus on no-smuggle (THE critical gate):**
- `TimeCompactnessInput.uniform_time_modulus`: apply the §3-H1 no-smuggle checklist — it must
  be a same-sequence uniform time modulus with NO subsequence/limit/Tendsto/spatial-compactness/
  div-free content. This is the milestone's single most important honesty check.
- `GoodRepresentativeInput` fields: confirm each is a genuine missing-pillar hypothesis ABOUT
  the limit, presented as a consumed argument, not a proved theorem; confirm the milestone
  honestly labels them the Bochner-time frontier; and CRITICALLY confirm the proved Tier N
  (`bForm_tendsto_of_strongL2`) and Tier E (`kineticEnergy_lsc_bound`) make the isolation
  non-trivial (i.e. we are NOT just re-bundling the whole axiom). If a field adds nothing over
  the axiom, instruct downgrade to `-- TODO:`.
- `aubinLionsPackage_R3_of_timeCompactness` and `galerkinLimitPassage_R3_of_goodRep`: confirm
  conclusions byte-identical to `aubin_lions_R3` / `galerkin_limit_passage_R3` bodies plus the
  added hypothesis binders — no hidden weakening (Hard rule 3).
- `spatialInput_R3_of_localRellich`: confirm its type is the `aubin_lions_R3` `spatial` binder
  verbatim and it is discharged purely by P3.

**Gate 2 — the combination proof (C2 / G1 / G2) and b-passage (N1):**
- Is the Aubin–Lions time-mesh ε/3 argument (C2) mathematically valid, and does G1
  (integrated `reg_bound` ⇒ usable sample-time viscous bound) hold or need the documented
  extra field? Scrutinize the integrated-⇏-pointwise subtlety.
- Does `bForm_tendsto_of_strongL2` (N1) correctly use only bilinearity + `b_bound`, with the
  `‖vₙ‖`-bounded step justified? Is the local→global tail bridge (if attempted) sound?
- Does `kineticEnergy_lsc_bound` (E1) legitimately get the pointwise-in-time bound from the
  local space-time limit (a.e.-time subsequence + norm-lsc)?

**Gate 3 — final, after proofs:**
- `#print axioms` on EACH proved lemma (`spatialInput_R3_of_localRellich`, `galStates_admissible`,
  `bForm_tendsto_of_strongL2`, `kineticEnergy_lsc_bound`, and `aubinLionsPackage_R3_of_timeCompactness`
  / `galerkinLimitPassage_R3_of_goodRep` if landed) shows only `[propext, Classical.choice,
  Quot.sound]` — NO `sorryAx` (TODO-blocked lemmas, if any, are reported separately with their
  marked sorry).
- `#print axioms exists_lerayHopf_r3` unchanged (6 project + 3 kernel axioms, no `sorryAx`);
  `AxiomaticClosure.lean` NOT edited.

---

## 7. lean-coder vs lean-prover split

**lean-coder** (file skeleton, imports, signatures, root-build edit):
- Create `LerayHopf/R3/AubinLionsLimitPassage.lean`: imports (§2.1, with the cycle-audit
  comment), namespace/opens (§2.2), module doc referencing `AxiomaticClosure.lean:444–501`,
  `SpatialCompactness.lean`, `TrilinearEstimate.lean`, and the plan.
- `TimeCompactnessInput` (H1) and `GoodRepresentativeInput` (G1struct) structures.
- All theorem signatures: `spatialInput_R3_of_localRellich` (S1), `galStates_admissible` (C1),
  `aubinLionsPackage_R3_of_timeCompactness` (C2), `bForm_tendsto_of_strongL2` (N1),
  `kineticEnergy_lsc_bound` (E1), `galerkinLimitPassage_R3_of_goodRep` (P1) — each with
  `:= by sorry -- ALLOW_SORRY: scaffold pending lean-prover` and an inline `-- Proof sketch:`
  comment from §3.
- Edit `LerayHopf.lean`: add `import LerayHopf.R3.AubinLionsLimitPassage` (§2.3).
- No proof bodies. Report all declaration names for Gate 1.

**lean-prover** (proof bodies, in dependency order):
1. S1 (`spatialInput_R3_of_localRellich`) — one-liner reuse of P3. Easiest; do first.
2. N1 (`bForm_tendsto_of_strongL2`) — self-contained b-bound payoff; high-value, reachable.
3. C1 (`galStates_admissible`) — uniform per-time bounds.
4. E1 (`kineticEnergy_lsc_bound`) — kinetic-energy lsc.
5. P1 (`galerkinLimitPassage_R3_of_goodRep`) — mechanical assembly (needs G1struct, N1, E1).
6. C2 (`aubinLionsPackage_R3_of_timeCompactness`) — the hard combination; attempt LAST, with
   the Tier-C realism fallback (§3) in hand. If blocked, leave precise `-- TODO:` (§8).

---

## 8. Definition of done

> **STATUS: SHIPPED AS HONEST PARTIAL (2026-06-17).** The checklist below is rewritten to
> match what was actually merged. The ADDENDUM (§ after §9) and this section SUPERSEDE the
> optimistic must-prove framing in §1.1/§3/§7/§9 (which assumed C2/E1 would close). C2 and E1
> are OPEN `sorry` targets, not delivered — by explicit user decision to merge the partial.

Shipped state (all verified):
- [x] `LerayHopf/R3/AubinLionsLimitPassage.lean` compiles (`lake build` green).
- [x] `import LerayHopf.R3.AubinLionsLimitPassage` present in `LerayHopf.lean` (root build guards it).
- [x] **PROVED, sorry-free, `#print axioms` = `[propext, Classical.choice, Quot.sound]`:**
      `spatialInput_R3_of_localRellich` (S1, reuses P3), `bForm_tendsto_of_strongL2` (N1,
      the R3-d b-bound payoff), and the private Steklov building blocks
      (`galerkin_curve_continuous`, `steklovAvg`, `steklovAvg_norm_le_u0`, `steklovAvg_approx`,
      `galerkin_norm_le_u0`). (`galStates_admissible` and `galerkinLimitPassage_R3_of_goodRep`
      were DROPPED — see ADDENDUM; `GoodRepresentativeInput` was dropped as smuggling.)
- [x] **OPEN — carries `sorry` + truthful `-- TODO:` (no smuggling, no new axiom/hypothesis):**
      - `kineticEnergy_lsc_bound` (E1) — **statement was CORRECTED (NOT byte-intact)** at the
        Codex statement gate: the original `∀ t` pointwise form was smuggling (claims
        pointwise-time representative control the package lacks), so it was weakened to the
        honest **a.e.-in-time** form (§3 Tier E). Even in the a.e. form it is OPEN/`sorry` —
        blocked because `AubinLionsPackage_R3` carries no time-measurability for its limit `u`
        (needs vector-valued Bochner-time / measurable-representative theory, absent in mathlib).
      - `aubinLionsPackage_R3_of_timeCompactness` (C2, the full Aubin–Lions assembly) — the
        pointwise-sample shortcut is unsound, but the **Steklov interval-averaging route is
        VIABLE** (Codex-confirmed, NOT impossible). Remaining open engineering: δ-mesh
        diagonalization, the H¹/Jensen bound on the Steklov average, Bochner-average
        measurability, and the boundary strip `(T−δ, T]` (forward window exits `[0,T]`;
        needs a boundary-strip estimate or clipped/backward averages). Building blocks proved.
- [x] Zero new `axiom`/`opaque`/`constant`. Isolated hypothesis: `TimeCompactnessInput`
      (the intended time-frontier for the still-open C2) — NOT the only non-proved item
      (E1/C2 are also open).
- [x] `#print axioms exists_lerayHopf_r3` unchanged (6 project + 3 kernel, no `sorryAx`);
      `AxiomaticClosure.lean` NOT edited.
- [x] `bash scripts/agent-preflight.sh` green (the two open sorries carry `ALLOW_SORRY`).
- [x] Codex `--effort xhigh`: Gate 1 (no-smuggle on `TimeCompactnessInput`) approve;
      final-gate honesty sweeps applied (header/Tier-H/C2-docstring/boundary all corrected).
- [x] STATUS.md P2 row added (honest partial).

**Next milestone (if C2 is pursued):** complete the Steklov δ-mesh Aubin–Lions assembly
(the named open pieces above), then E1 once a time-measurable representative is available.

---

## 9. Recommended first task for lean-coder

Create `LerayHopf/R3/AubinLionsLimitPassage.lean` with the full skeleton: imports (§2.1 with
the cycle-audit comment), namespace/opens, module doc, the two isolated structures
`TimeCompactnessInput` and `GoodRepresentativeInput`, and the six theorem signatures (S1, C1,
C2, N1, E1, P1) — each with a marked `sorry` placeholder and a `-- Proof sketch:` comment from
§3 — and add the root-build import to `LerayHopf.lean`. No proof bodies. Report file path + all
declaration names so the orchestrator can run the **Gate 1 Codex no-smuggle review on
`TimeCompactnessInput` and `GoodRepresentativeInput` (blocking)** before lean-prover starts.

---

## ADDENDUM — Scope refinement (orchestrator, pre-scaffold)

After reviewing §1.2: reconstructing the FULL `galerkin_limit_passage_R3` conclusion via a
`GoodRepresentativeInput` hypothesis bundling `weakForm`/`initialTrace`/`energyClass` is
**smuggling** (those fields re-assert conclusions (b)/(d)/(e)) — the would-be deliverable
`galerkinLimitPassage_R3_of_goodRep` would be a vacuous unpacking. We do NOT ship that.

**Refined P2 scope (honest, supersedes §3 Tier P / §9 where they conflict):**
- **DROP** `GoodRepresentativeInput` and `galerkinLimitPassage_R3_of_goodRep`.
- **KEEP & PROVE axiom-free:**
  1. `spatialInput_R3_of_localRellich` — reuse P3's `localCompactness_R3_of_ballCompact`.
  2. `TimeCompactnessInput` (honest hypothesis: uniform-in-n L² time-modulus; no
     subsequence/limit/strong_convergence content).
  3. `aubinLionsPackage_R3_of_timeCompactness` — produce `AubinLionsPackage_R3` from
     `galSeq` + `TimeCompactnessInput` + P3 spatial (the genuine Aubin–Lions reduction; the
     real centerpiece). `strong_convergence` via Arzelà–Ascoli-in-time + diagonal over balls.
  4. `bForm_tendsto_of_strongL2` — nonlinear b-term passage under strong L² (the R3-d
     `b_bound` payoff), a reusable standalone analytic lemma.
  5. `kineticEnergy_lsc_bound` — kinetic-energy lower-semicontinuity, standalone.
- **RESIDUAL FRONTIER (documented, NOT reconstructed, axiom retained):** limit-passage
  conclusions (b) WeakFormNS, (d) initial trace, (e) energy class need vector-valued weak
  time-derivative / `W^{1,p}(0,T;X)` theory absent in mathlib. P2 substantiates the AL
  reduction + the reusable analytic core; it does NOT claim to produce the full
  `galerkin_limit_passage_R3` conclusion. This mirrors R3-d (proved b-form lemmas without
  producing `Nonempty R3NSForms`).

This keeps P2 honest: real reduction + real reusable lemmas, zero smuggling, axiom retained.
