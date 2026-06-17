# Task Contract — Pillar B: LOCAL Rellich–Kondrachov on a ball `H¹(B_R) ↪↪ L²(B_R)`

**Track:** Pillar B (parallel with Helmholtz density + ODE continuation — stay in lane).
**Milestone slug:** `rellich-balls`
**File deliverable:** `LerayHopf/R3/RellichBall.lean` (NEW, standalone sibling).
**Hard constraint:** do NOT edit `LerayHopf/R3/AxiomaticClosure.lean` (axiom removal is a later
sequential capstone), do NOT edit `LerayHopf/R3/SpatialCompactness.lean`. Planner writes docs only.
**Target consumed:** the field `LocalRellichInput.ballCompact`
(`LerayHopf/R3/SpatialCompactness.lean:94-99`).

---

## 0. Goal

Prove, axiom-free, the analytic content of `LocalRellichInput.ballCompact`, i.e. CONSTRUCT a
`LocalRellichInput`:

```lean
theorem localRellichInput_R3 : LocalRellichInput
```

(or `Nonempty LocalRellichInput` / a named term `localRellichInput_R3 : LocalRellichInput`).
Concretely, for every `M R : ℝ` produce a compact `K ⊆ L2ballR3 R` containing
`restrictToBall R w` for every `w : L2VF_R3` with `w ∈ L2Sigma_R3`, `memH1VF_R3 w`,
`‖w‖ ≤ M`, `viscousFormSq_R3 1 w ≤ M^2`.

If proven, this makes `spatial_compactness_R3` a genuine theorem (the first full axiom removal)
— but THAT wiring is the later capstone, NOT this milestone. This milestone produces the
constructor in a standalone sibling file only.

---

## 1. FEASIBILITY VERDICT (read this first — be honest, P2 taught us not to over-promise)

**Verdict: FEASIBLE-WITH-A-SINGLE-NAMED-ISOLATED-HYPOTHESIS (one irreducible analytic
sub-frontier remains), NOT fully axiom-free this cycle.** The reduction AROUND the frontier
(see §3) is genuinely provable in mathlib; the remaining frontier is strictly SMALLER than
`ballCompact` and is named explicitly below (no smuggling). A fully axiom-free
`localRellichInput_R3` is **NOT achievable this cycle** without building one of two substantial
missing analytic developments. Details and grep evidence follow.

### 1.1 What mathlib has (grep-confirmed in `.lake/packages/mathlib/`)

- `IsCompact.tendsto_subseq`, `TotallyBounded.isCompact_of_isComplete` (Topology/Sequences,
  UniformSpace/Cauchy) — present (already used by P3's consumer).
- **Plancherel / L²-Fourier isometry**: `Lp.fourierTransformₗᵢ` and the `𝓕 : L2C_R3 → L2C_R3`
  instance — present (`Analysis/Fourier/LpSpace.lean`). This is what `viscousFormSq_R3` is
  built on.
- **Sobolev spectral characterization**: `TemperedDistribution.memSobolev_iff_exists_smulLeftCLM_fourier`
  (`Analysis/Distribution/Sobolev.lean:218`): `MemSobolev 1 2 f ↔ ∃ f' : Lp, smulLeftCLM
  (fun ξ ↦ (1+‖ξ‖²)^(1/2)) (𝓕 f) = f'`. So `memH1VF_R3 w` exactly says each component's
  `(1+‖ξ‖²)^{1/2}·𝓕 w_j ∈ L²`, i.e. global `H¹(ℝ³)` membership. The `viscousFormSq_R3 1 w ≤ M²`
  bound is `∑_j ∫ (2π)²‖ξ‖²|𝓕 w_j|² ≤ M²`, i.e. `‖∇w‖²_{L²(ℝ³)} ≤ M²` (global gradient L²-bound).
- **Arzelà–Ascoli**: present but only in abstract `UniformOnFun`/`EquicontinuousOn` form
  (`Topology/UniformSpace/Ascoli.lean`); NO turnkey "`C(K)`-bounded+equicontinuous ⇒ precompact"
  for our use without nontrivial plumbing.
- **Convolution / mollifiers**: `ContDiffBump`, `MeasureTheory.convolution`,
  convolution-is-`ContDiff` (`Analysis/Calculus/ContDiff/Convolution.lean`) — present, but NO
  "‖f⋆φ_ε − f‖_{L²} → 0" + "‖∇(f⋆φ_ε)‖ ≤ ‖∇f‖" Sobolev-mollification API.

### 1.2 What mathlib LACKS (grep-confirmed absent)

- **Rellich–Kondrachov / compact Sobolev embedding**: ABSENT (grep `Rellich|Kondrachov|compact
  embedding` → no analytic hit; only Gromov–Hausdorff / order-theoretic "compact").
- **Fréchet–Kolmogorov / Riesz L² compactness criterion**: ABSENT (grep `Kolmogorov|Frechet` →
  only probability `Kolmogorov.lean`). There is NO theorem "bounded + uniform L²-translation
  modulus + tight ⇒ precompact in L²".
- **L²-translation-continuity estimate `‖τ_h f − f‖_{L²} ≤ |h|·‖∇f‖_{L²}`**: ABSENT as a named
  lemma (grep `translation`/`translate` in Lp → only `TranslationNumber`, `LpSeminorm/Defs`
  unrelated). Not even `Continuous (h ↦ τ_h f)` in Lp is packaged conveniently.

### 1.3 The two honest routes to the FULL theorem, and why neither lands this cycle

**Route A — Fréchet–Kolmogorov from the gradient bound.**
Precompactness in L²(B_R) ⟺ bounded + uniform-L²-equicontinuous (translation modulus → 0) +
tight (automatic on a fixed ball). The translation modulus would come from
`‖τ_h w − w‖_{L²(ℝ³)} ≤ |h|·‖∇w‖_{L²(ℝ³)} ≤ |h|·M`. This estimate IS true and IS derivable
from the spectral form (`viscousFormSq_R3`) via Plancherel:
`‖τ_h w − w‖²_{L²} = ∫|e^{2πi h·ξ}−1|²|𝓕 w(ξ)|² dξ ≤ ∫ (2π|h||ξ|)²|𝓕 w|² = |h|²‖∇w‖²` (using
`|e^{iθ}−1| ≤ |θ|`). Cost to BUILD in Lean:
  (a) the Plancherel translation identity for the L²-Fourier transform (Fourier of a translate
      = modulation; `𝓕(τ_h w)(ξ) = e^{-2πi h·ξ}𝓕 w(ξ)`) — mathlib has this for Schwartz/`𝓕`
      on functions but bridging to the `Lp.fourierTransformₗᵢ` a.e. class needs work;
  (b) the pointwise `|e^{iθ}−1| ≤ |θ|` bound under the integral — easy;
  (c) **the missing Fréchet–Kolmogorov theorem itself** (modulus ⇒ total boundedness) — this is
      the genuinely large piece: it requires mollification + a covering/finite-net argument.
  Estimate: (c) alone is a multi-hundred-line analytic development re-deriving half of Rellich.
  **Not landable this cycle.**

**Route B — Mollification + Arzelà–Ascoli on the compact ball.**
Mollify each `w` to `w⋆φ_ε ∈ C^∞`, get a uniform sup-bound + equicontinuity on `B_R` from the
H¹ bound (Morrey-type / gradient control), apply Arzelà–Ascoli for `C(B̄_R)`-precompactness,
then push to L²(B_R) and let `ε → 0` controlled by the translation modulus. Cost: mathlib's
Arzelà–Ascoli is abstract-`UniformOnFun`; the Sobolev-mollification estimates
(`‖w⋆φ_ε‖_∞`, equicontinuity from `‖∇w‖_{L²}` in 3D, the `ε`-diagonal) are ALL unbuilt.
**Strictly harder than Route A; not landable this cycle.**

**Conclusion:** the crux the task asked about — "does the global-Fourier H¹ bound cleanly give
the ball-L² translation modulus?" — answer: **the modulus itself (Route A step a+b) is clean and
provable; but the modulus ⇒ precompactness implication (Fréchet–Kolmogorov, step c) is the real
wall, and mathlib has none of it.** The global-Fourier bound is exactly the right input; the gap
is the compactness *criterion*, not the estimate.

---

## 2. DELIVERABLE STRATEGY (no-smuggle): isolate ONE smaller frontier, prove the rest

Mirror the P3/P5/R3-d discipline: carry the irreducible analytic gap in ONE named, citable,
honestly-scoped hypothesis that is STRICTLY SMALLER than `ballCompact`, and prove everything
around it axiom-free. The smaller frontier we isolate is **the Fréchet–Kolmogorov precompactness
criterion on a ball**, phrased so it CANNOT smuggle Rellich (it knows nothing about Sobolev,
gradients, or the velocity family — only the abstract "uniform L²-translation modulus + bound ⇒
precompact" implication that mathlib lacks).

This makes the milestone deliver: **`localRellichInput_R3` is reduced to the abstract
Fréchet–Kolmogorov criterion** — and the genuinely Navier–Stokes-specific work (the gradient
bound ⇒ translation modulus, via Plancherel on `viscousFormSq_R3`) is proved axiom-free. That is
real progress: it converts the bespoke `ballCompact` frontier into a STANDARD, domain-agnostic,
well-known mathlib-gap lemma (Fréchet–Kolmogorov) that can later be PR'd to mathlib itself.

### 2.1 The isolated frontier hypothesis (smaller than `ballCompact`)

```lean
/-- Isolated analytic frontier: the **Fréchet–Kolmogorov (Riesz) L²-precompactness criterion**
on a fixed ball. A family of L²(B_R) elements that is uniformly bounded and has a uniform
L²-translation modulus vanishing as the shift → 0 is contained in a compact set.

This is the ONE thing mathlib lacks (no Fréchet–Kolmogorov). It is purely a statement about
abstract L² families and translation; it knows NOTHING about Sobolev spaces, gradients, the
velocity family, or divergence-freeness — all of which are supplied/derived in the reduction.
Strictly weaker/smaller than `LocalRellichInput.ballCompact`: it does not mention `H¹`,
`viscousFormSq`, `L2Sigma`, or the embedding; it is the standard compactness *criterion*, not
the embedding. -/
structure FrechetKolmogorovInput where
  precompact_of_uniform_modulus : ∀ (R C : ℝ) (S : Set (L2ballR3 R)),
    (∀ f ∈ S, ‖f‖ ≤ C) →
    (∀ ε > 0, ∃ δ > 0, ∀ f ∈ S, ∀ h : Domain3, ‖h‖ < δ →
        (translation modulus of f over B_R by h) < ε) →
    ∃ K : Set (L2ballR3 R), IsCompact K ∧ S ⊆ K
```

NOTE on the "translation modulus" slot: it must be stated against the GLOBAL field's L²-norm of
`τ_h w − w` restricted to (a slightly enlarged) ball, NOT against an in-ball translation (which
runs off the domain). lean-coder + Codex must fix the EXACT modulus expression so it is (i)
well-typed on `L2ballR3 R`, (ii) genuinely implied by the gradient bound (§3.2), (iii)
genuinely sufficient for precompactness (the abstract FK theorem). The recommended concrete
modulus is the global one and the family `S` is indexed via the underlying `L2VF_R3` field; see
G-MOD below. This is the single most delicate STATEMENT-design point — Codex Gate 1 must lock it.

**No-smuggle audit (Codex Gate 1):** `FrechetKolmogorovInput` must contain NONE of:
`memH1VF_R3`, `viscousFormSq_R3`, `L2Sigma_R3`, `∇`, the word `Sobolev`, the velocity sequence,
a subsequence, a limit. It is a pure abstract-L²-compactness criterion. If it mentions any
Navier–Stokes object, it has smuggled the embedding — reject.

### 2.2 Alternative framings to weigh at Gate 1 (let Codex pick)

- (i) **`FrechetKolmogorovInput` as above** (RECOMMENDED): isolates the standard mathlib gap;
  maximizes axiom-free content (we prove the modulus from the gradient bound).
- (ii) A bare `axiom frechetKolmogorov_L2ball` with `-- ALLOW_AXIOM` + assumptions-section entry,
  if a hypothesis-threading proves too heavy. Less preferred (an axiom vs a hypothesis), but
  acceptable per Hard rule 5 IF marked. Use ONLY if (i) creates intractable typeclass friction.
- (iii) Keep `LocalRellichInput.ballCompact` itself as the frontier and deliver NOTHING new
  here — REJECTED: that is what P3 already did; this milestone must SHRINK the frontier.

The whole point of the milestone is to move the frontier from "Rellich embedding" (i) to
"Fréchet–Kolmogorov criterion", proving the Navier–Stokes-specific bridge in between.

---

## 3. DECLARATIONS in dependency order

Namespace `LerayHopf`, `open MeasureTheory Filter Topology Metric`. No overclaim term in names
(Hard rule 6): the constructor is named `localRellichInput_of_frechetKolmogorov`, NOT
`localRellich` outright (it is conditional on the isolated input).

### Tier 0 — translation plumbing (coder signatures; prover bodies)

**T0a. `shift` / `translate_L2VF`** — must-prove
`noncomputable def translate_L2VF (h : Domain3) (w : L2VF_R3) : L2VF_R3` — the L² translation
`τ_h w (x) = w (x − h)`, as an Lp element (via measure-preserving `Lp.compMeasurePreserving`
with the translation map, which IS measure-preserving for Lebesgue — unlike `restrictToBall`).
Role: coder signature, prover body. Dep: `MeasurePreserving` of `(· + h)` / `Measure.map_add_right`.
Codex check: confirm `Lp.compMeasurePreserving` applies (translation preserves `volume`).

**T0b. `norm_translate_sub_le_grad`** — must-prove (THE Navier–Stokes-specific core, axiom-free)
```lean
/-- L²-translation modulus controlled by the spectral gradient form (Plancherel):
`‖τ_h w − w‖²_{L²(ℝ³)} ≤ ‖h‖² · viscousFormSq_R3 1 w`. -/
theorem normSq_translate_sub_le_viscousFormSq (h : Domain3) (w : L2VF_R3)
    (hw : memH1VF_R3 w) :
    ‖translate_L2VF h w - w‖ ^ 2 ≤ ‖h‖ ^ 2 * viscousFormSq_R3 1 w
```
Role: prover. Proof sketch: Plancherel (`Lp.fourierTransformₗᵢ` is an isometry) componentwise;
`𝓕(τ_h w_j)(ξ) = e^{-2πi h·ξ} 𝓕 w_j(ξ)` (Fourier-of-translate = modulation, mathlib has the
function-level statement — bridge to the Lp class); then pointwise
`|e^{-2πi h·ξ} − 1|² ≤ (2π)²‖h‖²‖ξ‖²` (from `|e^{iθ}−1| ≤ |θ|` and Cauchy–Schwarz `|h·ξ| ≤
‖h‖‖ξ‖`); integrate and recognize `∑_j ∫ (2π)²‖ξ‖²|𝓕 w_j|² = viscousFormSq_R3 1 w`.
Gating note **G-PLANCHEREL (main risk in this tier):** bridging the function-level
"Fourier-of-translate = modulation" to the `Lp.fourierTransformₗᵢ` a.e. representative used in
`viscousFormSq_R3` is nontrivial (the `(𝓕 (...) : L2C_R3) ξ` coercion). If the bridge is too
heavy, fall back to deriving the modulus on a DENSE Schwartz subset and extending by continuity —
but that needs Helmholtz/Schwartz-density (PARALLEL track; do NOT depend on it). If neither
lands, leave T0b with intact statement + precise `-- TODO:` and STOP (Hard rule 8). Codex Gate 2
must review whether the Lp-Fourier translation identity is reachable.

**T0c. `uniform_modulus_of_viscousBound`** — must-prove (axiom-free, easy given T0b)
```lean
/-- Uniform translation modulus for the admissible family: from `viscousFormSq_R3 1 w ≤ M²`,
`‖τ_h w − w‖ ≤ ‖h‖·M` uniformly. Supplies the modulus hypothesis of `FrechetKolmogorovInput`. -/
theorem norm_translate_sub_le_of_viscousBound (M : ℝ) (h : Domain3) (w : L2VF_R3)
    (hw : memH1VF_R3 w) (hvf : viscousFormSq_R3 1 w ≤ M ^ 2) :
    ‖translate_L2VF h w - w‖ ≤ ‖h‖ * M
```
Role: prover. From T0b + `viscousFormSq_R3_nonneg` + `Real.sqrt` monotonicity / `nlinarith`.

### Tier 1 — assemble the modulus into the FK-criterion input

**T1a. `restrictToBall_translate_modulus`** — must-prove (bridge to `L2ballR3`)
Relate `‖translate_L2VF h w − w‖` (global) to the ball modulus expression appearing in
`FrechetKolmogorovInput` (whatever exact form Gate 1 fixes; see G-MOD). `restrictToBall` is
norm-nonincreasing (`norm_restrictToBall_le` already exists in SpatialCompactness.lean — but we
cannot import bodies; re-prove a local copy or import the file as a sibling READ-ONLY? — see
DEP note below). Role: prover.

**T1b. `admissible_family_uniform_bound`** — must-prove
The set `S_{M,R} := {restrictToBall R w | w admissible}` is uniformly `‖·‖ ≤ M` (each
restriction does not increase the norm, and `‖w‖ ≤ M`). Role: prover. Trivial given the
norm-nonincreasing restriction lemma.

### Tier 2 — DELIVERABLE

**T2. `localRellichInput_of_frechetKolmogorov`** — must-prove (THE DELIVERABLE)
```lean
/-- **LOCAL Rellich input on ℝ³, from the abstract Fréchet–Kolmogorov criterion.**
Constructs a `LocalRellichInput` (the per-ball precompactness of the H¹-bounded div-free family)
from `FrechetKolmogorovInput`. The Navier–Stokes-specific content (gradient bound ⇒ uniform
translation modulus, via Plancherel on `viscousFormSq_R3`) is proved axiom-free here; only the
domain-agnostic FK precompactness criterion is assumed. -/
theorem localRellichInput_of_frechetKolmogorov (FK : FrechetKolmogorovInput) :
    LocalRellichInput
```
Role: prover. For each `M R`, set `S := {restrictToBall R w | w admissible}`; supply T1b (bound)
and T0c→T1a (uniform modulus) to `FK.precompact_of_uniform_modulus`; obtain compact `K ⊇ S`;
package as the `ballCompact` field. Conclusion must reproduce `LocalRellichInput.ballCompact`
exactly (the `K`/`IsCompact K`/membership shape).

**Optional capstone (NOT this milestone — note only):** once `FrechetKolmogorovInput` is itself
discharged (future mathlib FK PR or a dedicated `frechet-kolmogorov` milestone), `Nonempty
LocalRellichInput` follows, and a SEPARATE sequential PR can rewrite `spatial_compactness_R3`
from `axiom` to `theorem`. Out of scope here. Do NOT touch `AxiomaticClosure.lean`.

---

## 4. DEPENDENCY NOTE — reusing SpatialCompactness plumbing

`L2ballR3`, `restrictToBall`, `norm_restrictToBall_le`, `setIntegral_normSq_eq_dist_sq_restrictToBall`
already exist in `LerayHopf/R3/SpatialCompactness.lean`. `RellichBall.lean` should
`import LerayHopf.R3.SpatialCompactness` (it is a sibling that BUILDS ON the P3 plumbing — this
is allowed; the prohibition is only against editing it and against importing/editing
`AxiomaticClosure.lean`). This avoids re-proving `restrictToBall` lemmas. Confirm at Gate 1 that
importing SpatialCompactness (not AxiomaticClosure) keeps the new deliverable's `#print axioms`
clean.

DAG position:
```
R3/Regularity.lean
  └── R3/SpatialCompactness.lean   (L2ballR3, restrictToBall, LocalRellichInput) [P3, existing]
        └── R3/RellichBall.lean    [NEW — this milestone; imports SpatialCompactness, NOT AxiomaticClosure]
```
Add `import LerayHopf.R3.RellichBall` to root `LerayHopf.lean` (coder owns this edit).

---

## 5. CODER vs PROVER split

**lean-coder** (skeleton, imports, signatures, root build):
- Create `LerayHopf/R3/RellichBall.lean`: imports (`LerayHopf.R3.SpatialCompactness`,
  `Mathlib.Analysis.Fourier.LpSpace`, plus translation/measure-preserving imports), namespace,
  module doc referencing this contract + `SpatialCompactness.lean:94-99`.
- `FrechetKolmogorovInput` structure (§2.1 — with the EXACT modulus slot Gate 1 locks).
- Signatures for T0a, T0b, T0c, T1a, T1b, T2, each `:= by sorry -- ALLOW_SORRY: scaffold pending
  lean-prover` (T0a's `def` body as `sorry` too), with `-- Proof sketch:` comments from §3.
- Add `import LerayHopf.R3.RellichBall` to `LerayHopf.lean`.
- No proof bodies. Report all declaration names + the EXACT modulus expression for Gate 1.

**lean-prover** (bodies, dependency order):
1. T0a (`translate_L2VF`) — measure-preserving Lp comp.
2. T0b (`normSq_translate_sub_le_viscousFormSq`) — Plancherel core (HARDEST; G-PLANCHEREL).
3. T0c — algebraic consequence of T0b.
4. T1a, T1b — restriction/modulus bridges.
5. T2 (deliverable) — assemble into the `FK` criterion.

---

## 6. CODEX REVIEW POINTS (orchestrator-run `/codex:adversarial-review --effort xhigh`)

**Gate 1 — statement block (BEFORE proofs), no-smuggle + modulus design:**
- `FrechetKolmogorovInput`: apply §2.1 no-smuggle checklist (no `H¹`/`viscousFormSq`/`L2Sigma`/
  `∇`/`Sobolev`/subsequence/limit). Confirm it is STRICTLY SMALLER than `ballCompact` and is the
  standard domain-agnostic FK criterion. THE single most important gate.
- The EXACT translation-modulus expression (G-MOD): is it (i) well-typed, (ii) implied by the
  gradient bound (T0c), (iii) sufficient for FK precompactness? Lock the wording here.
- `localRellichInput_of_frechetKolmogorov`: confirm its conclusion is `LocalRellichInput`
  verbatim (the `ballCompact` shape), no hidden weakening (Hard rule 3).

**Gate 2 — Plancherel core (T0b, G-PLANCHEREL):**
- Is `𝓕(τ_h w) = modulation` reachable for the `Lp.fourierTransformₗᵢ` class used in
  `viscousFormSq_R3`? Is `|e^{iθ}−1| ≤ |θ|` integrated correctly, and does the result equal
  `viscousFormSq_R3 1 w` (the `(2π)²‖ξ‖²` factor matching)?
- Confirm T0a's translation is measure-preserving (so `Lp.compMeasurePreserving` is valid),
  unlike `restrictToBall`.

**Gate 3 — after proofs:** `#print axioms localRellichInput_of_frechetKolmogorov` clean
(`propext, Classical.choice, Quot.sound`; NO `sorryAx`); `#print axioms exists_lerayHopf_r3`
UNCHANGED (AxiomaticClosure not touched); preflight green.

---

## 7. DEFINITION OF DONE

- [ ] `LerayHopf/R3/RellichBall.lean` compiles; `import LerayHopf.R3.RellichBall` in root.
- [ ] `localRellichInput_of_frechetKolmogorov : FrechetKolmogorovInput → LocalRellichInput`
      sorry-free.
- [ ] T0b (`normSq_translate_sub_le_viscousFormSq`), T0c, T1a, T1b sorry-free (the axiom-free
      Navier–Stokes-specific bridge).
- [ ] Zero new `axiom`/`opaque`/`constant` (frontier carried by `FrechetKolmogorovInput`
      hypothesis). If route (ii) §2.2 is forced, ONE marked `axiom frechetKolmogorov_L2ball`
      with `-- ALLOW_AXIOM` + assumptions-section entry, Codex-approved.
- [ ] `#print axioms localRellichInput_of_frechetKolmogorov` no `sorryAx`.
- [ ] `AxiomaticClosure.lean` NOT edited; `exists_lerayHopf_r3` axiom set unchanged.
- [ ] `bash scripts/agent-preflight.sh` green. Codex Gates 1, 2, 3 approve.

**Honest partial fallback (Hard rule 8):** if G-PLANCHEREL (T0b) blocks this cycle, leave T0b's
statement intact with `-- TODO: Lp-Fourier translation identity (𝓕(τ_h w)=modulation) bridge`
and ship the FK-input structure + T2 reduction (conditional on T0c as a hypothesis instead)
sorry-free where possible; do NOT weaken any statement. Report the exact blocker.

---

## 8. RECOMMENDED FIRST TASK FOR lean-coder

Create `LerayHopf/R3/RellichBall.lean` with: imports (`LerayHopf.R3.SpatialCompactness`,
`Mathlib.Analysis.Fourier.LpSpace`, translation/measure-preserving imports), namespace/opens,
module doc, the `FrechetKolmogorovInput` structure (proposing a CONCRETE translation-modulus
expression for Gate 1 to lock), and the six signatures (T0a, T0b, T0c, T1a, T1b, T2) each with a
marked `sorry` and a `-- Proof sketch:` comment, plus the root-build import. No proof bodies.
Report file path, all declaration names, and the exact modulus expression so the orchestrator can
run Gate 1 (no-smuggle + modulus design) before lean-prover starts.
