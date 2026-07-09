# Task contract — Shared Fourier–L² foundation + consumers for Pillars B & D

**Milestone id:** `fourier-foundation-bd`
**Planner lane:** Fourier / L² + mollification analysis (parallel sibling planner owns
FinDimGlobalODE — do NOT touch ODE / Galerkin-time files).
**Scope authority:** `HANDOFF.md` (real project state), `docs/guardrails.md`, `AGENTS.md`.
The `docs/*plan*.md` MVP files describe an earlier spine; the live targets are the R3
pillars named below. This contract sequences only Fourier/L²/mollification work.

This contract plans a **shared Fourier–L² foundation file** plus the two consumers that
finish (as far as honestly possible this cycle) Pillar B (`normSq_translate_sub_le_viscousFormSq`,
the sole `sorry` of `RellichBall.lean`) and Pillar D (`CurlSchwartzDense`, the sole frontier
of `SchwartzDivFreeBasis.lean`). Sequencing: **foundation first**, then B and D in parallel.

---

## 0. Grep-backed reality check (what mathlib has / lacks)

All paths under `.lake/packages/mathlib/`.

**HAVE (reusable):**
- `MeasureTheory.Lp.fourierTransformₗᵢ : Lp E F 2 ≃ₗᵢ[ℂ] Lp E F 2`, with
  `Lp.norm_fourier_eq` (Plancherel `‖𝓕 f‖ = ‖f‖`) and `Lp.inner_fourier_eq`
  (`Analysis/Fourier/LpSpace.lean:49,88,92`).
- `SchwartzMap.toLp_fourier_eq : 𝓕 (f.toLp 2) = (𝓕 f).toLp 2` — the Schwartz↔Lp Fourier
  bridge (`LpSpace.lean:98`). **E's prover already used this** in
  `GalerkinODEExistence.lean:185` (`galerkinSpan_fourier_ae`). Generalize that pattern.
- `SchwartzMap.denseRange_toLpCLM (hp : p ≠ ⊤)` (`SchwartzSpace/Basic.lean:1379`) +
  `DenseRange.induction_on` — the extension-by-density engine. mathlib's own
  `Lp.fourier_toTemperedDistribution_eq` (`LpSpace.lean:125`) is the **template** for any
  "identity on Lp proved by Schwartz density".
- `VectorFourier.fourierIntegral_comp_add_right` (`FourierTransform.lean:107`) and the
  scalar alias (`:358`): the **raw-integral** translation→modulation identity
  `𝓕(f ∘ (·+v₀)) w = e(L v₀ w) • 𝓕 f w`. Phase factor is `e (L v₀ w)`.
- `SchwartzMap.fourier_coe : 𝓕 f = 𝓕 (f : V → E)` (`SchwartzSpace/Fourier.lean:98`) —
  connects the Schwartz CLM `𝓕` to the raw `fourierIntegral`. **This is the bridge** that
  lets the raw modulation lemma be lifted to the Schwartz level.
- `Lp.compMeasurePreserving` + `measurePreserving_add_right` — already used for
  `translate_L2VF` (`RellichBall.lean:130`).
- `ContinuousLinearMap.compLpL`, `Lp.SecondCountableTopology`, `MemLp`, `integral_*`.
- Arzelà–Ascoli (abstract uniform form only): `ArzelaAscoli.isCompact_of_equicontinuous`,
  `...compactSpace_of_isClosedEmbedding` (`Topology/UniformSpace/Ascoli.lean:496,453`).
- `MeasureTheory.convolution_tendsto_right` (`Analysis/Convolution.lean:789`) — but
  **pointwise** only; `ContDiffBump.convolution_tendsto_right`.
- Young's inequality (scalar/nnreal/ennreal `young_inequality`) — `MeanInequalities.lean`.

**LACK (grep-confirmed absent — these are the frontier):**
- **No Lp-level modulation/translation lemma** for `Lp.fourierTransformₗᵢ`. Grep of
  `Analysis/Fourier/` for `fourier.*comp_add` returns only the *raw-integral* lemma. None
  on the a.e. Lp class.
- **No bounded L^∞-multiplier-on-Lp operator** (`phaseMul`/`smulLeftCLM` at Lp level):
  grep of `MeasureTheory/Function/LpSpace/` for `phaseMul|smulLeftCLM|boundedMul` →
  no files. Must be built.
- **No Fréchet–Kolmogorov / Riesz L²-precompactness criterion** anywhere (grep
  `FrechetKolmogorov|frechet_kolmogorov` → no files).
- **No Rellich–Kondrachov** (grep `RellichKondrachov|rellich` in mathlib → no files).
- **No L²-norm convolution approximate-identity** (`‖f∗ρ_ε − f‖₂ → 0`): grep
  `eLpNorm_convolution|MemLp.convolution|tendsto_convolution` → only the pointwise
  `convolution_tendsto_right`. No `MemLp`/`eLpNorm` convolution mapping lemma.
- **No Helmholtz/Leray decomposition, no curl operator, no transverse-spanning lemma**
  (already noted in `SchwartzDivFreeBasis.lean:42`).

---

## 1. New files (dependency order)

```
LerayHopf/R3/FourierL2.lean           [NEW — shared foundation; foundation FIRST]
   ├── (consumer 1)  LerayHopf/R3/RellichBall.lean       [EXISTING — close T0b only]
   └── (consumer 2)  LerayHopf/R3/SchwartzDivFreeBasis.lean [EXISTING — attack CurlSchwartzDense]
```

- `FourierL2.lean` imports `LerayHopf.R3.Regularity` (for `viscousFormSq_R3`,
  `L2VF_projComponentC_R3`, `L2C_R3`, `Domain3`) and `Mathlib.Analysis.Fourier.LpSpace`.
  It must NOT import `AxiomaticClosure` (keep the NS axioms out of its `#print axioms`).
- **Confirm: NO edits to `SolutionInterfaces.lean` (T³ or ℝ³), NO edits to the root
  `LerayHopf.lean` wiring.** Both consumers stay siblings; capstone wiring is deferred.
- FK (consumer 1b), if attempted, gets its **own** new file
  `LerayHopf/R3/FrechetKolmogorov.lean` (mollification-based, independent of FourierL2).
  See §4 — the recommendation is to **defer FK** this cycle.

---

## 2. SHARED FOUNDATION — `LerayHopf/R3/FourierL2.lean`

Goal: provide BOTH the Lp modulation identity (B/T0b needs) and the Schwartz↔Lp Fourier
bridge + Plancherel weight bookkeeping (D and B both need). Generalize
`galerkinSpan_fourier_ae`'s pattern out of `GalerkinODEExistence.lean` so it is reusable.

Declarations (coder = signatures/defs/structure/imports; prover = proof bodies):

| id | name (informal signature) | kind | owner |
|---|---|---|---|
| F1 | `phaseFun (h : Domain3) : Domain3 → ℂ := fun ξ => Complex.exp (2π i ⟪h,ξ⟫)` (the modulation phase; `‖phaseFun h ξ‖ = 1`) | **must-prove** (def + `norm_phaseFun_eq_one`) | coder def / prover lemma |
| F2 | `phaseMulCLM (h : Domain3) : L2C_R3 →L[ℂ] L2C_R3` — pointwise mult by `phaseFun h`, a bounded (operator-norm ≤ 1) multiplier on `L²(ℝ³;ℂ)`. Built via `MemLp`-preserving a.e. mult + `Lp` extensionality; NOT in mathlib so built here. | **must-prove** | coder def / prover |
| F3 | `coeFn_phaseMulCLM : (phaseMulCLM h g : Domain3 → ℂ) =ᵐ[volume] fun ξ => phaseFun h ξ * g ξ` (a.e. characterization) | **must-prove** | prover |
| F4 | `toLp_fourier_compMeasurePreserving_eq` — **Schwartz-level modulation**: for `ψ : 𝓢(Domain3,ℂ)`, `𝓕 ((τ_h ψ).toLp 2) = phaseMulCLM h (𝓕 (ψ.toLp 2))`, where `τ_h ψ` is the Schwartz precomposition with `(·+h)` (or the toLp of the translate). Proved by `fourier_coe` + `VectorFourier.fourierIntegral_comp_add_right` + `F3`. | **must-prove** | prover |
| F5 | `fourier_translate_eq` — **Lp-level modulation (THE missing piece)**: for `f : L2C_R3`, `𝓕 (Lp.compMeasurePreserving (·+h) (measurePreserving_add_right volume h) f) = phaseMulCLM h (𝓕 f)`. Proved by `DenseRange.induction_on` over `denseRange_toLpCLM`, base case = F4, closedness from continuity of both sides (`isClosed_eq`). **Template: `Lp.fourier_toTemperedDistribution_eq`.** | **must-prove** | prover |
| F6 | `fourierComponentC_ae_schwartz` — generalization of `galerkinSpan_fourier_ae`: for any `f` whose component has a Schwartz rep, the a.e. coercion of `𝓕` of the component is a.e. a genuine Schwartz `𝓕`. (Lift the existing private lemma to public, domain-general.) | **must-prove** | coder (move/generalize) / prover |
| F7 | `viscousFormSq_R3_eq_integral_normSq_fourier` — Plancherel weight bookkeeping: `viscousFormSq_R3 1 w = ∑ j ∫ (2π)²‖ξ‖² ‖(𝓕 cⱼ) ξ‖² dξ` (just `rfl`/`unfold` exposure as a named lemma so consumers cite a stable name) | **must-prove** | prover (likely `rfl`) |
| F8 | `normSq_sub_eq_integral_phase_sub` — Plancherel core helper: `‖𝓕(τ_h c) − 𝓕 c‖² = ∫ ‖phaseFun h ξ − 1‖² ‖(𝓕 c) ξ‖² dξ` for a component `c` (combines F5 + `Lp.norm_fourier_eq` + `phaseMulCLM` a.e.). | **must-prove** | prover |
| F9 | `normSq_phaseFun_sub_one_le` — pointwise `‖phaseFun h ξ − 1‖² ≤ (2π)²‖h‖²‖ξ‖²` (`|e^{iθ}−1| ≤ |θ|` via `Complex.norm_exp_ofReal_mul_I_sub_one_le`/`abs`, Cauchy–Schwarz `|⟪h,ξ⟫| ≤ ‖h‖‖ξ‖`). | **must-prove** | prover |

Notes for coder:
- F1–F2 are the genuinely new infrastructure. F2 needs a `MemLp`-preserving multiplication
  lemma: `phaseFun h` is bounded (norm 1), so `(phaseFun h · g) ∈ MemLp 2` whenever
  `g ∈ MemLp 2`; assemble the CLM with operator norm ≤ 1. There is no mathlib
  `boundedMulLp`, so build it directly (a.e.-mult + `Lp.mk`, bound via `eLpNorm` monotone
  under `‖phaseFun‖ ≤ 1`).
- Keep F1–F9 as **small** separate declarations (Small-PR rule). F2 may itself need 2–3
  private helpers (memLp of product, eLpNorm bound).

**Feasibility verdict (foundation):**
- F1, F3, F6, F7, F9 — **fully feasible** (standard, all API present).
- F4 — **feasible with moderate gaps**: needs careful matching of `fourier_coe`'s raw
  `fourierIntegral` form (with its `e (L v₀ w)` phase and the `(2π)` / `innerₗ` convention)
  to `phaseFun`. Convention bookkeeping (the `(2π)`, the sign, `innerₗ V` vs `⟪·,·⟫`) is
  the real work; mathematically routine.
- F2 — **feasible, the heaviest new build** (~80–150 lines): a bounded Lp multiplier is
  genuinely absent. Self-contained though (no Fourier needed for F2 itself).
- F5 — **feasible**: it is exactly `Lp.fourier_toTemperedDistribution_eq`'s density-induction
  pattern with F4 as the base case. This is the crux that retires the `RellichBall.lean`
  TODO's blocker.
- F8 — **feasible** given F5 + F3.

Overall foundation verdict: **fully feasible, no new axiom.** The one previously-claimed
"multi-hundred-line, possibly-impossible" blocker (the Lp modulation identity, per
`RellichBall.lean:181-193`) is real but reducible to F2+F4+F5 via the existing
`DenseRange.induction_on` template — **not impossible, ~250–400 lines total**.

---

## 3. CONSUMER 1 — Pillar B, T0b (`RellichBall.lean`)

Target: discharge the SOLE `sorry` —
`normSq_translate_sub_le_viscousFormSq (h) (w) (hw : memH1VF_R3 w) :
  ‖translate_L2VF h w − w‖² ≤ ‖h‖² · viscousFormSq_R3 1 w`
(`RellichBall.lean:173`). Statement **stays verbatim** (Hard rule 3).

The in-file TODO (`:195-204`) already gives the exact axiom-free decomposition (a)–(d).
The foundation supplies the missing (c). Declaration plan:

| id | name | kind | owner |
|---|---|---|---|
| B-T0b.1 | `translate_component_ae` — component proj commutes with `compMeasurePreserving` a.e.; `‖τ_h w − w‖² = ∑_j ‖τ_h^C cⱼ − cⱼ‖²` (TODO step (a); `RCLike.ofRealCLM` norm-preserving) | must-prove (local lemma) | coder sig / prover |
| B-T0b.2 | the closing proof of `normSq_translate_sub_le_viscousFormSq` itself: chain (a)=B-T0b.1, (b)=`Lp.norm_fourier_eq`, (c)=`FourierL2.normSq_sub_eq_integral_phase_sub` (F8), (d)=`FourierL2.normSq_phaseFun_sub_one_le` (F9) + `integral_mono` + pull out `‖h‖²` + recognize F7. | **must-prove** (replaces `sorry`) | prover |

Dependency edge: B-T0b.2 depends on F5, F7, F8, F9 (and B-T0b.1).

**Feasibility verdict (T0b): fully feasible once the foundation lands.** The peeling/sign
bookkeeping downstream (T0c, T1b, T2) is already proved axiom-free; closing T0b makes the
**entire deliverable `localRellichInput_of_frechetKolmogorov` sorry-free MODULO the
`FrechetKolmogorovInput` hypothesis** (which remains an explicit hypothesis, not an axiom).
DoD: `#print axioms normSq_translate_sub_le_viscousFormSq` contains no `sorryAx`.

---

## 4. CONSUMER 1b — Pillar B, Fréchet–Kolmogorov (`FrechetKolmogorovInput`)

Question posed: PROVE FK (removing the `FrechetKolmogorovInput` hypothesis) or KEEP it?

**Honest assessment — KEEP it as a hypothesis this cycle; do NOT attempt the full proof.**

Reasons, grep-backed:
- FK = (bounded + uniform L²-translation-modulus ⇒ precompact in L²(ball)). The standard
  proof is: mollify `f_ε = f ∗ ρ_ε`; (i) `‖f_ε − f‖₂ → 0` **uniformly over the family**
  (needs the L²-convolution approximate-identity — **absent**, only pointwise
  `convolution_tendsto_right` exists); (ii) `{f_ε}` is equibounded + equicontinuous on the
  ball (needs Young `L²∗L²→L^∞`-type bounds wiring into the **abstract** Ascoli, which has
  no `C(K)`-precompactness wrapper); (iii) total-boundedness transfer. Each of (i)–(iii) is
  a standalone multi-hundred-line development on top of missing infrastructure.
- This is a **substantial standalone theorem** (the project's `HANDOFF.md` P3 pillar). It
  is mathlib-library-grade, not a milestone-sized task. Proving it does not advance the B
  pillar's *architecture* (the conditional constructor T2 already cleanly consumes it).
- It is **independent of the Fourier foundation**, so it can be picked up later in its own
  file `LerayHopf/R3/FrechetKolmogorov.lean` without blocking anything.

If a *partial* FK foothold is desired later (separate milestone, not this contract): the
smallest honest first sub-deliverable is the **L²-convolution approximate identity**
`tendsto (fun ε => ‖f ∗ ρ_ε − f‖₂) (𝓝[>]0) (𝓝 0)` for `f ∈ L²`, as its own lemma — that
is the genuinely missing analytic core and is reusable. Recommend deferring even that.

**Verdict (FK): blocked-with-reason for a full proof this cycle; KEEP as hypothesis.**
No declarations scheduled. (Decision is explicit per the task's request to recommend honestly.)

---

## 5. CONSUMER 2 — Pillar D, `CurlSchwartzDense` (`SchwartzDivFreeBasis.lean`)

Target: the isolated frontier
`CurlSchwartzDense : L2Sigma_R3 ≤ (span ℝ (range curlSchwartzL2)).topologicalClosure`
(`SchwartzDivFreeBasis.lean:217`), currently exposed only via the `sorry` in C2
`nonempty_schwartzGalerkinBasis` (`:459`).

Fourier route (the task's sketch), pressure-tested:
1. `𝓕(curl ψ)(ξ) = 2πi ξ × ψ̂(ξ)` — at each ξ the curls' Fourier transforms fill the
   transverse plane `{v ⊥ ξ}` (the range of `v ↦ ξ × v` is exactly `ξ^⊥` for `ξ ≠ 0`).
2. `u ∈ L2Sigma_R3 ⟺ ξ·û(ξ) = 0` a.e. (weak-div-free ⟺ transverse in Fourier).
3. Density reduces to: (pointwise-in-ξ cross products span `ξ^⊥`) + (Schwartz density
   transfer into the constrained subspace).

**Feasibility verdict (CurlSchwartzDense): PARTIAL / mostly blocked this cycle. Recommend
isolating a strictly-smaller sub-hypothesis, do NOT claim a closed density.**

Why, grep-backed and structurally:
- Step (1) requires a **Fourier-of-curl identity at the Lp/Schwartz level**. The
  foundation gives `𝓕(∂_j ψ) = 2πi ξ_j ψ̂` only if we also build the **Fourier-derivative
  multiplier** identity at Lp level (mathlib has `Real.fourierIntegral_deriv`-type lemmas at
  the integral level and `fourierPowSMulRight` for Schwartz, but not packaged as the
  curl-cross-product). Reachable via the same `fourier_coe` + density route as F4/F5, but
  it is a **second** modulation-style development, comparable in size to F4–F5.
- Step (2): `L2Sigma_R3` is defined via `divTestFunctional` (weak), NOT spectrally. Proving
  `u ∈ L2Sigma_R3 ⟺ ξ·û = 0 a.e.` is a **Fourier characterization of the weak-div-free
  subspace** — itself a real theorem (Parseval pairing of the weak-div functional). Not in
  mathlib; medium-heavy.
- Step (3) the **transverse-spanning + density transfer** is the genuine slice of Helmholtz:
  even granting (1)+(2), turning "pointwise span ξ^⊥" into "L²-closure of curl-span ⊇
  L2Sigma_R3" needs a measurable-selection / fiberwise-density argument (a vector-bundle
  density) that mathlib has no tooling for.

Net: the Fourier route replaces one hard frontier (`CurlSchwartzDense`) with **three**
sub-frontiers (curl-Fourier identity, spectral characterization of `L2Sigma_R3`, fiberwise
density), only the first of which the foundation meaningfully shortens. This is **deeper
than T0b** and is honestly a multi-file research formalization.

Recommended deliverable for THIS cycle (small, honest, monotone refinement):

| id | name | kind | owner |
|---|---|---|---|
| D1 | `fourier_curlSchwartz_eq` — Lp-level `𝓕(curlSchwartzL2 ψ)` componentwise `= 2πi ξ ×-component of ψ̂` (uses foundation F4/F5 + a Fourier-derivative multiplier helper). **Statement only this cycle if the multiplier helper is not built; else must-prove.** | **scaffold/with-gaps** (statement-first; prove if cheap) | coder sig / prover |
| D2 | `MemL2Sigma_iff_fourier_transverse` — spectral characterization `u ∈ L2Sigma_R3 ⟺ ∀ᵐ ξ, ⟪ξ, û ξ⟫ = 0`. **Statement + isolate as a thin `Prop`-hypothesis `L2SigmaFourierCriterion` if not provable.** | **scaffold-only** (isolate) | coder |
| D3 | `curlSchwartzDense_of_fourierTransverseSpan` — the conditional: from D1 + D2 + a single isolated **fiberwise-density** hypothesis `Prop` (`FourierTransverseSpanDense`), conclude `CurlSchwartzDense`. | **must-prove** (the assembly), conditional on the isolated `Prop` | prover |
| D4 | keep C2 `nonempty_schwartzGalerkinBasis`'s marked `sorry` as-is OR feed it `schwartzGalerkinBasis_of_curlDense (curlSchwartzDense_of_… h₁ h₂ h₃)`; **no axiom added without orchestrator+Codex sign-off.** | scaffold-only | (orchestrator decision) |

So this cycle D **thins** the single `CurlSchwartzDense` frontier into a clearly-labelled
conditional `curlSchwartzDense_of_fourierTransverseSpan` whose only irreducible input is the
fiberwise-density `Prop` — strictly more honest and smaller than the current opaque
`CurlSchwartzDense`, but it does **not** close D. If D1's Fourier-curl multiplier proves
cheap on top of the foundation, promote D1 to must-prove; otherwise leave D as the thinned
conditional. **Do not overclaim D as solved.**

---

## 6. Sequencing

```
PHASE 0 (foundation, blocking):  FourierL2.lean  F1 → F2 → F3 → F4 → F5 ; F6,F7,F9 parallel ; F8 after F5
        └── Codex adversarial-review on ALL new statements (F1–F9) BEFORE proving (gate).
PHASE 1 (parallel after foundation green + Codex-approved):
   Pillar B:  RellichBall.lean   B-T0b.1 → B-T0b.2   [closes the sole sorry; high confidence]
   Pillar D:  SchwartzDivFreeBasis.lean  D1/D2 (statements) → D3 (conditional assembly)
              [thins the frontier; does NOT close it]
FK (consumer 1b):  DEFERRED — separate later milestone, own file.
```

B and D are independent once the foundation exists (different files, no shared decl beyond
the foundation). They may be handed to two prover passes in parallel.

---

## 7. Codex review points (orchestrator-run, BEFORE proofs)

Adversarial-review (`--effort xhigh`) the **statements** of:
- **F2 `phaseMulCLM`** — that it is genuinely the phase multiplier (norm-1, a.e. mult), not
  a vacuous/zero CLM; check `coeFn_phaseMulCLM` pins it.
- **F4/F5 modulation identities** — convention audit: the `(2π)`, the sign of the phase,
  `innerₗ V`/`⟪h,ξ⟫` vs the `e^{2πi⟪h,ξ⟫}` convention used by `viscousFormSq_R3`. This is the
  classic NL↔Lean trap (HANDOFF §8 item 3). **Highest-priority Codex point.**
- **F9** — direction of the inequality and the `(2π)²` factor matching F7.
- **D1 `fourier_curlSchwartz_eq`** — that the cross-product form is faithful (no smuggling a
  Leray projection; cf. existing no-smuggle note `SchwartzDivFreeBasis.lean:179`).
- **D2 `MemL2Sigma_iff_fourier_transverse` / `L2SigmaFourierCriterion`** — that the spectral
  criterion is equivalent to the *weak* `divTestFunctional` definition, not a redefinition.
- **D3 + the isolated `FourierTransverseSpanDense` Prop** — no-smuggle: confirm the isolated
  hypothesis is strictly the fiberwise-density fact and carries no Schwartz/div-free witness
  already proved elsewhere (it must be thinner than `CurlSchwartzDense`).

The B-T0b closing proof reuses already-audited statements, so it needs only the standard
post-proof `#print axioms` check, not a fresh statement review.

---

## 8. Definition of done (this cycle)

**Must be sorry-free (`#print axioms` shows no `sorryAx`, no new `axiom`):**
- All of `FourierL2.lean` F1–F9 (the foundation).
- `RellichBall.lean : normSq_translate_sub_le_viscousFormSq` (T0b) — and hence the whole
  `RellichBall.lean` file becomes `sorry`-free, with `FrechetKolmogorovInput` remaining an
  explicit *hypothesis* (not an axiom).

**Scaffold / thinned (honest partial, no overclaim):**
- `SchwartzDivFreeBasis.lean`: D3 `curlSchwartzDense_of_fourierTransverseSpan` sorry-free
  *conditional* on the isolated `FourierTransverseSpanDense` Prop (+ D2's criterion if kept
  as hypothesis). D1 promoted to must-prove only if cheap. C2's `sorry` (or an
  orchestrator-approved single marked axiom) remains — **D is NOT closed**.

**Explicitly NOT done (carried honestly):**
- Fréchet–Kolmogorov full proof (KEPT as hypothesis).
- `CurlSchwartzDense` as an unconditional theorem (thinned, not closed).
- Any `SolutionInterfaces.lean` / root `LerayHopf.lean` wiring (deferred capstone).

**Invariant checks (every handoff):** `bash scripts/agent-preflight.sh` green; no new
`axiom`/`opaque`/`unsafe` without `-- ALLOW_AXIOM:` + assumptions entry; no unmarked `sorry`;
no overclaim names; `SolutionInterfaces.lean` untouched (confirmed).

---

## 9. Overall verdict — how much of B and D closes this cycle

- **Pillar B: substantially closed.** The foundation retires the only real blocker (the Lp
  modulation identity that `RellichBall.lean` flagged as possibly-impossible). After this
  cycle, B's T0b is sorry-free and the LOCAL-Rellich conditional constructor is fully
  proved modulo the *one* honest, mathlib-absent `FrechetKolmogorovInput` hypothesis. FK
  itself is deferred (genuine library-grade theorem). **Net: B goes from "1 open sorry +
  1 hypothesis" to "0 sorry + 1 hypothesis".**
- **Pillar D: thinned, not closed.** The Fourier route is real but replaces one frontier
  with three sub-frontiers; only the curl-Fourier identity is shortened by the foundation.
  This cycle delivers a more honest *conditional* (`curlSchwartzDense_of_fourierTransverseSpan`)
  isolating a single fiberwise-density `Prop`, but `CurlSchwartzDense` remains open. **Net:
  D's frontier becomes smaller and better-labelled; D is not finished.**

**Recommendation:** ship the foundation + B this cycle as the high-confidence win; treat D
as a thinning/scoping pass and FK as a deferred separate milestone.

---

## 10. First task for `lean-coder`

Create `LerayHopf/R3/FourierL2.lean` with the imports
(`LerayHopf.R3.Regularity`, `Mathlib.Analysis.Fourier.LpSpace`) and the **signatures/defs
only** for F1–F9 (def bodies for F1, F2; `theorem … := by sorry -- ALLOW_SORRY: prover
target` for F3–F9), plus the module docstring listing declarations + the (empty) Assumptions
section. Do NOT touch `RellichBall.lean`, `SchwartzDivFreeBasis.lean`, `SolutionInterfaces.lean`,
or `GalerkinODEExistence.lean` in this first task. After it compiles, the orchestrator runs
the Codex statement review (§7) before any prover pass.
