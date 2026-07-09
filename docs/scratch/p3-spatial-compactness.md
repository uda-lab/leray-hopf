# Task Contract — P3: LOCAL Rellich–Kondrachov on ℝ³ (axiom-free reduction)

**Milestone:** `p3-spatial-compactness`
**File deliverable:** `LerayHopf/R3/SpatialCompactness.lean` (new, standalone)
**Branch:** `autorun/p3-spatial-compactness`
**Plan reference:** `/Users/uda/.claude/plans/p2-p3-witty-rain.md` (P3 section, lines 43–84);
target axiom `spatial_compactness_R3` in `LerayHopf/R3/SolutionInterfaces.lean:378–389`.
**Models to mirror:** `LerayHopf/H1Sigma.lean:rellich_L2Sigma` (diagonal extraction +
`isClosed.mem_of_tendsto` for div-free closure); `LerayHopf/RellichEmbedding.lean`
(`IsCompact.tendsto_subseq` strategy).

---

## 0. Goal and scope

Reproduce the **exact conclusion shape** of the `spatial_compactness_R3` axiom, axiom-free
and sorry-free, from ONE clean isolated hypothesis that captures the genuine analytic
frontier (the LOCAL compact embedding `H¹(B_R) ↪↪ L²(B_R)`, which mathlib lacks).

This does **not** remove the axiom. We add a sibling proved lemma in a new standalone file
(`SolutionInterfaces.lean` is **not** edited and **not** imported here). The connection is
semantic, exactly as R3-d (`TrilinearEstimate.lean`) and P5 (`GalerkinScheme.lean`) did.

Target conclusion (verbatim from `SolutionInterfaces.lean:378–389`):

```lean
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
      Filter.atTop (nhds 0)
```

---

## 1. Design decision — the isolated frontier hypothesis

### 1.1 What is genuinely missing in mathlib

Confirmed by grep of `.lake/packages/mathlib/`:

- **Present and load-bearing:** `IsCompact.tendsto_subseq` (`Mathlib/Topology/Sequences.lean:298`),
  `TotallyBounded.isCompact_of_isComplete` (`Mathlib/Topology/UniformSpace/Cauchy.lean:744`),
  `Metric.closedBall`, `MeasureTheory.volume.restrict`, set-integral lemmas, and the L²
  bridge `MeasureTheory.L2.norm_sq_eq_re_inner` / `integral_inner_eq_sq_eLpNorm`
  (`Mathlib/MeasureTheory/Function/L2Space.lean:142,157`) which gives
  `‖f‖² = ∫ ‖f x‖² ∂μ` for `f : α →₂[μ] E`.
- **Absent:** Rellich–Kondrachov, any compact-embedding API, Fréchet–Kolmogorov
  (L²-modulus → precompactness). The global Fourier-multiplier route is also blocked
  (no `H^s(ℝ³)` multiplier compactness). These are precisely what the isolated hypothesis
  must carry.

### 1.2 Chosen shape: per-ball precompactness via the restricted-measure L² space

The cleanest object for "restrict to a ball in L²" that carries a usable **metric** (needed
for `IsCompact.tendsto_subseq`) is the Lp space over the restricted measure:

```lean
abbrev L2ballR3 (R : ℝ) :=
  Lp (EuclideanSpace ℝ (Fin 3)) 2 (volume.restrict (Metric.closedBall (0 : Domain3) R))
```

We need a **restriction map** `L2VF_R3 → L2ballR3 R`. Mathlib's `Lp.toLp_restrict` style
is awkward; the robust route is to go through the underlying a.e.-function:
`MeasureTheory.MemLp.restrict` gives `MemLp f 2 (volume.restrict s)` from `MemLp f 2 volume`,
and `MemLp.toLp` packages it. Bundle this as a definition `restrictToBall R : L2VF_R3 → L2ballR3 R`
(NOT necessarily a CLM — a bare function suffices since we only need its values along a
sequence and the squared-distance identity). See gating note G1.

**The isolated hypothesis** (preferred form — per-ball precompactness of the H¹-bounded family,
phrased so it cannot smuggle the global conclusion):

```lean
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
```

**Why a `structure` (cf. P5 `SchwartzGalerkinBasis`) rather than a bare `∀`/`∃` (cf. R3-d
`hdiv`):** there is exactly one field, so either is fine, but a named `structure` (a) gives the
frontier a citable name in `STATUS.md` and `#print axioms` discussions, (b) leaves room for a
second field if Codex finds the single field insufficient (e.g. a measurability side-condition),
and (c) matches the established P5 pattern. The deliverable takes `(B : LocalRellichInput)` as
its sole non-data argument.

### 1.3 Rejected alternative: Fréchet–Kolmogorov modulus

Candidate (b) — a uniform L²-translation modulus `∫_{B_R} ‖z(·+h) − z(·)‖² → 0` as `h→0` —
was evaluated and **rejected for this cycle**: mathlib has **no** Fréchet–Kolmogorov theorem
(modulus → precompactness), so we would still need to *prove* "uniform modulus + uniform L²
bound ⇒ totally bounded in L²(B_R)" by hand (mollification + Arzelà–Ascoli on a compact ball),
which is a substantial analytic development and re-derives half of Rellich. The precompactness
form (1.2) isolates the frontier at exactly the boundary mathlib can consume
(`IsCompact.tendsto_subseq`), with the smallest provable reduction. We note (b) as the more
"elementary-looking" but strictly harder-to-discharge option for a future cycle.

### 1.4 No-smuggle audit checklist (for the Codex statement gate)

The hypothesis must NOT contain any of: a subsequence index `ψ`; a limit `g`; the word
`Tendsto`; quantification over all `R` *jointly with* a single shared extraction; any
div-free conclusion about a limit. It supplies a compact SET per single ball, nothing more.
Confirm each of these is absent. (This mirrors the P5 `dense_span` honesty review.)

---

## 2. New file: `LerayHopf/R3/SpatialCompactness.lean`

### 2.1 Imports

```lean
import LerayHopf.R3.Regularity            -- L2VF_R3, L2Sigma_R3, memH1VF_R3, viscousFormSq_R3, Domain3
import Mathlib.Topology.Sequences          -- IsCompact.tendsto_subseq
import Mathlib.MeasureTheory.Function.L2Space      -- L2 norm² = ∫ ‖·‖²
import Mathlib.MeasureTheory.Integral.Bochner.Set  -- setIntegral, restrict-measure integrals
```

`R3.Regularity` transitively supplies `R3.DivergenceFree`, `R3.Domain`, and the
`memH1VF_R3` / `viscousFormSq_R3` definitions. Do **not** import `R3.AxiomaticClosure`.
Justify any heavier import per Hard rule 10.

### 2.2 Namespace / opens

```lean
namespace LerayHopf
open MeasureTheory Filter Topology Metric
```

### 2.3 Root build inclusion (REQUIRED — P5 lesson)

Add `import LerayHopf.R3.SpatialCompactness` to `LerayHopf.lean` (after the
`R3.GalerkinScheme` line). Without this the default `lake build`/preflight does not guard
the file. **lean-coder owns this edit.**

---

## 3. Declarations in dependency order

Naming convention: snake-case, mathematically descriptive, no overclaim term (Hard rule 6).
The reduction theorem name must NOT claim "Rellich" outright (it is conditional on the input);
use `localCompactness_R3_of_ballCompact` style.

### Tier 0 — restriction plumbing (coder skeleton; prover proofs)

**D0a. `L2ballR3`** — scaffold-only (abbrev, no proof)
```lean
noncomputable abbrev L2ballR3 (R : ℝ) :=
  Lp (EuclideanSpace ℝ (Fin 3)) 2 (volume.restrict (Metric.closedBall (0 : Domain3) R))
```
Role: coder. No proof.

**D0b. `restrictToBall`** — must-prove (definition + the MemLp obligation)
```lean
noncomputable def restrictToBall (R : ℝ) (w : L2VF_R3) : L2ballR3 R
```
Role: coder writes signature; prover fills the `MemLp.restrict … |>.toLp` body.
Deps: `MeasureTheory.MemLp.restrict`, `Lp.memLp`, `MemLp.toLp`.
Gating note **G1**: if `MemLp.restrict` + `toLp` does not give a clean `L2ballR3` element
(e.g. defeq friction between `volume.restrict` and the abbrev), fall back to
`Lp.compMeasurePreserving` is NOT applicable (restriction is not measure-preserving); instead
use the a.e.-function `(w : Domain3 → _)` and `MemLp.restrict (Lp.memLp w)`. This API is
confirmed present.

**D0c. `setIntegral_normSq_eq_dist_sq_restrictToBall`** — must-prove (the bridge lemma)
```lean
/-- The ball set-integral of the squared difference equals the squared L²(B_R)-distance
of the two restrictions. This is the bridge between the conclusion's set-integral shape
and the metric in which `IsCompact.tendsto_subseq` produces convergence. -/
theorem setIntegral_normSq_eq_dist_sq_restrictToBall (R : ℝ) (u v : L2VF_R3) :
    ∫ x in Metric.closedBall (0 : Domain3) R,
      ‖(u x : EuclideanSpace ℝ (Fin 3)) - (v x : EuclideanSpace ℝ (Fin 3))‖ ^ 2
      ∂(volume : Measure Domain3)
    = dist (restrictToBall R u) (restrictToBall R v) ^ 2
```
Role: prover.
Proof sketch: `dist f g = ‖f - g‖` in `Lp`; for `L²` (`p = 2`),
`‖h‖² = ∫ ‖h x‖² ∂μ` via `MeasureTheory.L2.norm_sq_eq_re_inner` /
`integral_inner_eq_sq_eLpNorm` (confirmed `L2Space.lean:142,157`); then
`∫ … ∂(volume.restrict s) = ∫ x in s, … ∂volume` via
`MeasureTheory.integral_restrict` / `setIntegral` defn; and `(restrictToBall R u) x =ᵐ u x`
on the ball so the integrands agree a.e. (use `MemLp.coeFn_toLp`,
`Measure.restrict` a.e.-eq).
Gating note **G2**: the exact L²-norm-squared-as-integral lemma name may be
`MeasureTheory.L2.norm_sq_eq` or be reached through `integral_inner_eq_sq_eLpNorm` +
`Lp.norm_def`; the prover should pick whichever typechecks. The mathematics is standard;
flag for Codex if the chosen lemma needs an `Integrable`/`MemLp` side-goal.

### Tier 1 — per-ball subsequence extraction (prover)

**D1. `exists_subseq_tendsto_on_ball`** — must-prove
```lean
/-- From the isolated per-ball precompactness, any admissible sequence has a subsequence
whose ball-restrictions converge in L²(B_R). -/
theorem exists_subseq_tendsto_on_ball (B : LocalRellichInput) (M R : ℝ)
    (z : ℕ → L2VF_R3) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hmem : ∀ n, z n ∈ L2Sigma_R3) (hH1 : ∀ n, memH1VF_R3 (z n))
    (hbd : ∀ n, ‖z n‖ ≤ M) (hvf : ∀ n, viscousFormSq_R3 1 (z n) ≤ M ^ 2) :
    ∃ (ρ : ℕ → ℕ) (g : L2ballR3 R), StrictMono ρ ∧
      Tendsto (fun n => restrictToBall R (z (φ (ρ n)))) atTop (𝓝 g)
```
Role: prover.
Proof sketch: from `B.ballCompact M R` get compact `K` with
`restrictToBall R (z (φ n)) ∈ K` for all `n` (membership transfers along `φ` since each
`z (φ n)` is admissible). Apply `IsCompact.tendsto_subseq K hK (fun n => …)` to obtain
`g ∈ K`, a strictly monotone `ρ`, and the convergence. Note: `IsCompact.tendsto_subseq`
returns the extraction; package as `ρ`.
Deps: `IsCompact.tendsto_subseq` (`Topology/Sequences.lean:298`).
(Taking `φ` as an argument lets the diagonal step in D2 feed already-extracted sequences.)

### Tier 2 — diagonal over expanding balls (prover; the structural core)

**D2. `exists_subseq_tendsto_on_all_balls`** — must-prove
```lean
/-- Diagonal extraction over the radii R = 1, 2, 3, …: a SINGLE strictly monotone
subsequence whose ball-restrictions converge in L²(B_k) for every natural k (hence,
by monotonicity of balls, for every real R). -/
theorem exists_subseq_tendsto_on_all_balls (B : LocalRellichInput) (M : ℝ)
    (z : ℕ → L2VF_R3)
    (hmem : ∀ n, z n ∈ L2Sigma_R3) (hH1 : ∀ n, memH1VF_R3 (z n))
    (hbd : ∀ n, ‖z n‖ ≤ M) (hvf : ∀ n, viscousFormSq_R3 1 (z n) ≤ M ^ 2) :
    ∃ (ψ : ℕ → ℕ), StrictMono ψ ∧
      ∀ k : ℕ, ∃ g : L2ballR3 (k : ℝ),
        Tendsto (fun n => restrictToBall (k : ℝ) (z (ψ n))) atTop (𝓝 g)
```
Role: prover. This is the analogue of the 3-component diagonal in
`H1Sigma.lean:rellich_L2Sigma` lines 183–189, but over countably many radii instead of 3.
Proof sketch: build a sequence of nested extractions `φ_0 ⊇ φ_1 ⊇ …` where `φ_{k}` refines
`φ_{k-1}` and makes ball-`k` converge (each step is D1 applied to the previously-extracted
sequence). Then take the **diagonal** `ψ n := (φ_0 ∘ φ_1 ∘ … ∘ φ_n) n`, equivalently realized
with `Nat.rec` / a `StrictMono` diagonal combinator.
Gating note **G3 (the main structural risk):** mathlib has no single packaged "diagonal
extraction over countably many subsequences" lemma in a directly-usable form for this setup.
Two routes:
  (i) **Hand-rolled diagonal** via `Nat.rec` defining the family of extractions, then prove
      `StrictMono` of the diagonal and that each tail of the diagonal is a subsequence of
      `φ_k` (so ball-`k` convergence is inherited by `Tendsto.comp` + `tendsto_atTop` of the
      tail). This is standard but ~40–80 lines of careful index bookkeeping.
  (ii) Search mathlib for an extraction-of-extractions helper
      (`extraction_forall_of_eventually`, `Filter`-based diagonal). If a clean one exists,
      prefer it; otherwise route (i).
If route (i) proves too heavy to land this cycle, the honest fallback (Hard rule 8) is to
leave D2 with intact statement and a precise `-- TODO: countable diagonal extraction over
radii; mathlib lacks a packaged combinator` and STOP (do NOT weaken). But: the expectation
is route (i) is feasible — it is the same construction as the 3-fold diagonal in
`rellich_L2Sigma`, merely countably indexed. Codex should review the chosen route.

### Tier 3 — limit assembly + div-free closure (prover)

**D3a. `ballLimits_are_consistent`** — must-prove (helper)
```lean
/-- The per-ball limits from D2 are mutually consistent: the limit on B_k agrees a.e.
on B_j (j ≤ k) with the limit on B_j (both are L² limits of the same subsequence's
restrictions, and restriction B_k → B_j is continuous). Used to assemble a single global g. -/
```
Role: prover. Sketch: restriction `L2ballR3 k → L2ballR3 j` (for `j ≤ k`) is continuous;
apply it to the convergent sequence on `B_k`; uniqueness of L² limits gives agreement with
the `B_j` limit a.e. on `B_j`.
Gating note **G4:** assembling a single GLOBAL `g : L2VF_R3` from consistent ball-limits
requires a "glue local L² functions into a global L² function" step. Two routes:
  (i) **Glue via a.e. functions:** define `g₀ : Domain3 → EuclideanSpace ℝ (Fin 3)` by
      `g₀ x := (limit on B_{⌈‖x‖⌉}) x`; show `MemLp g₀ 2 volume` from the uniform L²-bound
      `‖z n‖ ≤ M` (Fatou / `MemLp` of an a.e.-pointwise limit with uniform L²-norm bound),
      then `g := g₀.toLp`.
  (ii) If gluing is too heavy, RESTRUCTURE D2 to converge in the **global** `L2VF_R3` directly:
      uniform `‖z n‖ ≤ M` gives the global sequence lives in a closed ball of `L2VF_R3`;
      but that ball is NOT norm-compact (infinite-dim), so global `IsCompact.tendsto_subseq`
      does NOT apply — route (ii) does not work without weak compactness (different topology).
      Therefore **route (i) is the intended path.**
Codex review focus: confirm the Fatou/`MemLp`-of-a.e.-limit step does not silently need
*strong* global convergence (which we do NOT have — we only have local strong convergence).
The global `g` is built as an a.e. object; only LOCAL convergence to it is claimed. This is
exactly what the axiom's conclusion asserts (per-ball L² convergence, NOT global).

**D3b. `ballLimit_global_mem_L2Sigma`** — must-prove
```lean
/-- The assembled global limit g lies in L2Sigma_R3 (weakly divergence-free). -/
```
Role: prover. Mirror `rellich_L2Sigma`'s `isClosed_L2Sigma.mem_of_tendsto`
(`H1Sigma.lean:218–221`) using `isClosed_L2Sigma_R3` (`R3/DivergenceFree.lean:89`).
Gating note **G5:** `isClosed.mem_of_tendsto` needs convergence `z (ψ n) → g` in the
**global** `L2VF_R3` topology, but we only have LOCAL convergence. Div-freeness is a
GLOBAL property tested against Schwartz functions. Resolution: each `divTestFunctional φ`
has a Schwartz `φ` with rapid decay, so its action factors through any ball up to an
arbitrarily small tail controlled by the uniform `‖z n‖ ≤ M` bound. Concretely show
`divTestFunctional φ g = lim divTestFunctional φ (z (ψ n)) = 0`:
  - split `divTestFunctional φ` into ball-`R` part + tail;
  - tail ≤ `‖z(ψ n) − g‖_{B_R^c}` × (Schwartz tail seminorm of `φ`), → 0 as `R → ∞`
    uniformly in `n` by the uniform L²-bound and Schwartz decay;
  - ball part → 0 by D2 local convergence;
  - each `divTestFunctional φ (z (ψ n)) = 0` since `z (ψ n) ∈ L2Sigma_R3`.
This is the one genuinely delicate analytic step that uses BOTH local convergence and the
uniform bound; it is **provable** but is the most likely place to need a small extra lemma.
Codex must review this argument's statement and the tail estimate carefully.
If the tail estimate cannot be closed cleanly this cycle, the honest fallback is to add a
SECOND field to `LocalRellichInput` — e.g. `limit_divFree : (the assembled g is div-free)` —
ONLY as a last resort and with explicit Codex sign-off that it does not smuggle the
conclusion. Prefer proving G5 outright.

### Tier 4 — final packaging (prover)

**D4. `localCompactness_R3_of_ballCompact`** — must-prove (THE DELIVERABLE)
```lean
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
        Filter.atTop (nhds 0)
```
Role: prover. Assembles D2 (`ψ`), D3a/D3b (`g`, `g ∈ L2Sigma_R3`), and converts per-ball
metric convergence (D2) to the set-integral form via D0c bridge. For a general real `R`:
pick `k ≥ R` with `closedBall 0 R ⊆ closedBall 0 k`, reduce the `R`-integral to the `k`-limit
(set-integral monotone in domain is NOT directly used; instead use D0c at radius `R` together
with `restrictToBall R (z (ψ n)) → restrictToBall R g`, which follows from D2 at any `k ≥ R`
by continuity of further restriction `L2ballR3 k → L2ballR3 R`). Conclude
`dist (restrictToBall R (z (ψ n))) (restrictToBall R g) ^ 2 → 0` and rewrite via D0c.

**The deliverable's statement must be byte-identical (modulo bound variable names) to the
`spatial_compactness_R3` axiom body.** lean-coder: copy it from `SolutionInterfaces.lean:379–389`
and prepend `(B : LocalRellichInput)`.

---

## 4. Module DAG position

```
R3/Domain.lean
  └── R3/DivergenceFree.lean
        └── R3/Regularity.lean   (memH1VF_R3, viscousFormSq_R3)
              └── R3/SpatialCompactness.lean   [NEW — this PR]
                    (standalone; NOT importing R3/SolutionInterfaces.lean)
```
Sibling of `R3/SolutionInterfaces.lean`, not a dependency of it. Added to root `LerayHopf.lean`.

---

## 5. Assumptions section (axioms)

**Zero new `axiom`/`opaque`/`constant`.** The genuine frontier is carried by the
**hypothesis** `LocalRellichInput` (an explicit argument), exactly as R3-d's `hdiv` and P5's
`SchwartzGalerkinBasis.dense_span`. No `-- ALLOW_AXIOM` markers are added; no entry to any
assumptions section is needed (a hypothesis is not an axiom).

If, and only if, G5 (div-free of the limit) cannot be closed, a SECOND field on
`LocalRellichInput` may be added — still not an axiom — but only with Codex sign-off per §6.

---

## 6. Codex review points (orchestrator-run `/codex:adversarial-review --effort xhigh`)

**Gate 1 — statement block (BEFORE any proof bodies), focus on no-smuggle:**
- `LocalRellichInput.ballCompact`: does it smuggle the conclusion? Apply the §1.4 checklist
  (no `ψ`, no `g`, no `Tendsto`, no joint-over-`R` extraction, no div-free limit). This is the
  single most important gate (mirrors P5 `dense_span` honesty review).
- `localCompactness_R3_of_ballCompact`: confirm its conclusion is byte-identical to
  `spatial_compactness_R3` (SolutionInterfaces.lean:378–389) plus the `(B : LocalRellichInput)`
  binder — no hidden weakening (Hard rule 3).
- `restrictToBall` / `L2ballR3`: is the restricted-measure L² object the right carrier, and
  does D0c's bridge equation typecheck (set-integral = squared restricted-L²-distance)?

**Gate 2 — D2 diagonal route (G3) and D3a/D3b assembly (G4, G5):**
- Is the countable diagonal (route i) the intended construction, and is StrictMono-of-diagonal
  + subsequence-inheritance stated correctly?
- D3b/G5 tail estimate: does the argument legitimately derive GLOBAL div-freeness from LOCAL
  convergence + the uniform L²-bound + Schwartz decay, without needing global strong
  convergence we do not have? This is the subtle correctness point.

**Gate 3 — final, after proofs:** `#print axioms localCompactness_R3_of_ballCompact` clean
(only `propext, Classical.choice, Quot.sound`; NO `sorryAx`); `exists_lerayHopf_r3` axiom set
unchanged.

---

## 7. lean-coder vs lean-prover split

**lean-coder** (file skeleton, imports, signatures, root-build edit):
- Create `LerayHopf/R3/SpatialCompactness.lean`: imports (§2.1), namespace/opens (§2.2),
  module doc referencing `SolutionInterfaces.lean:378–389` and the plan.
- `LocalRellichInput` structure (§1.2), `L2ballR3` (D0a), `restrictToBall` signature (D0b),
  and all theorem signatures D0c, D1, D2, D3a, D3b, D4 each carrying
  `:= by sorry -- ALLOW_SORRY: scaffold pending lean-prover` (and `restrictToBall := sorry`),
  with inline `-- Proof sketch:` comments from §3.
- Edit `LerayHopf.lean`: add `import LerayHopf.R3.SpatialCompactness` (§2.3).
- No proof bodies. Report all declaration names for Gate 1.

**lean-prover** (proof bodies, in dependency order):
1. D0b (`restrictToBall`), then D0c (bridge) — foundation.
2. D1 (per-ball extraction) — needs D0a only.
3. D2 (diagonal) — needs D1.
4. D3a, D3b (assembly + div-free) — need D2, D0c.
5. D4 (deliverable) — needs all.

---

## 8. Definition of done

- [ ] `LerayHopf/R3/SpatialCompactness.lean` compiles.
- [ ] `import LerayHopf.R3.SpatialCompactness` present in `LerayHopf.lean` (root build guards it).
- [ ] `localCompactness_R3_of_ballCompact` and all helpers (D0c, D1, D2, D3a, D3b, D4) sorry-free.
- [ ] Zero new `axiom`/`opaque`/`constant`. The only non-proved input is the
      `LocalRellichInput` hypothesis.
- [ ] `#print axioms localCompactness_R3_of_ballCompact` shows only
      `[propext, Classical.choice, Quot.sound]` — no `sorryAx`.
- [ ] `#print axioms exists_lerayHopf_r3` unchanged (6 project + 3 kernel axioms, no `sorryAx`);
      `SolutionInterfaces.lean` not edited.
- [ ] `bash scripts/agent-preflight.sh` green.
- [ ] Codex Gates 1, 2, 3 → approve.

**Honest partial fallback** (Hard rule 8, if G3 or G5 blocks this cycle): leave the blocked
declaration's statement intact with a precise `-- TODO: <exact blocker>` and ship the rest
sorry-free; do NOT weaken any statement. Report the exact blocker to the orchestrator.

---

## 9. Recommended first task for lean-coder

Create `LerayHopf/R3/SpatialCompactness.lean` with the full skeleton: imports (§2.1),
namespace/opens, module doc, the `LocalRellichInput` structure, `L2ballR3` abbrev,
`restrictToBall` signature, and the six theorem signatures (D0c, D1, D2, D3a, D3b, D4) — each
with a marked `sorry` placeholder and a `-- Proof sketch:` comment — and add the root-build
import to `LerayHopf.lean`. No proof bodies. Report file path + all declaration names so the
orchestrator can run the Gate 1 Codex statement/no-smuggle review before lean-prover starts.
