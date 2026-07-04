> CAMPAIGN COMPLETE (2026-07-04). All 6 PRs merged (T-AL-1..6 = #78/#79/#80/#85/#88/#89); axiom aubin_lions DELETED; exists_lerayHopf_torus3_axiomatic UNCONDITIONAL (#print axioms kernel-only); issue #23 closed. The body below is the historical plan.

# Torus `aubin_lions` removal — the MODE-WISE SPECTRAL route (torus 1 → 0)

**Architect doc (fable, 2026-07-03). PLAN ONLY — no Lean edited by this doc.**
Campaign issue: #23 (under umbrella #26). Prize: `exists_lerayHopf_torus3_axiomatic`
becomes **unconditional** (`#print axioms` = `propext`, `Classical.choice`, `Quot.sound`
only) — ZERO project axioms on the torus capstone.

**Supersedes, on the torus only:** the PHASE-3/T-B section of
`docs/scratch/bochner-foundation-metaplan.md` ("port the R3 Steklov toolkit, build the
Bochner Aubin–Lions–Simon engine, months-class"). That plan remains the honest route for
**R3-B** (`galerkin_spacetime_precompact_R3`, lane #74 — NOT this lane). This doc replaces
it for **T-B** because the torus Fourier-spectral scheme makes the abstract Bochner
machinery **structurally unnecessary** — the same asymmetry that made #25 close in days
while its R3 twin walled (see `project_limit_passage_r3_removal_campaign` memory: the
spectral scheme's band-limited tests fire `u_ode` directly).

---

## 0. The target, verbatim (verified on main @ 148ee59)

`axiom aubin_lions` at `LerayHopf/AxiomaticClosure.lean:376–386`. Binders:
`(F : Torus3NSForms) (ν) (hν : 0 < ν) (T) (hT : 0 < T) (u₀ : L2Sigma)`
`(galSeq : ∀ n, GalerkinSolutionData F ν u₀ n)` `(spatial : …rellich-shaped…)`.
Conclusion: **`AubinLionsPackage F ν T u₀ galSeq`** — a `Type`-valued structure
(`AxiomaticClosure.lean:311–338`) with exactly **five** fields, each a separate
pressure-test obligation for the P0.7 dry run:

1. `φ : ℕ → ℕ`,
2. `φ_mono : StrictMono φ`,
3. `u : Time → L2Sigma`,
4. `strong_convergence : Tendsto (fun n => eLpNorm (fun t => ((galSeq (φ n)).u t : L2VF) - (u t : L2VF)) 2 (volume.restrict (Icc 0 T))) atTop (𝓝 0)`,
5. `u_aestronglyMeasurable : AEStronglyMeasurable (fun t => (u t : L2VF)) (volume.restrict (Icc 0 T))`.

Sole consumer: `build_galerkin_package_of_galSeq` (`TorusGalerkinODECapstone.lean:77–95`),
which passes `spatial := rellich_L2Sigma` (already proved). The replacement is a
`noncomputable def` (Type-valued, mirroring `aubinLionsPackage_R3_of_timeCompactness`,
`R3/AubinLionsLimitPassage.lean`), NOT a `theorem`.

**Note the `spatial` binder:** the replacing def must either keep it (byte-compatible
swap, then feed `rellich_L2Sigma` at the consumer as today) or drop it (it becomes unused
— the mode-wise proof does not route through Rellich). Decision at the statement gate:
**keep the binder byte-identical** to the axiom's for a no-drama consumer rewire; mark it
`_spatial` if unused. No-weakening is automatic (same hypotheses, same conclusion type).

### Available inputs per `GalerkinSolutionData F ν u₀ n` (`AxiomaticClosure.lean:237–284`)

- `u_ode` (line 264): ∀ `t ≥ 0`, ∀ `w : L2Sigma` with `velocityProjection_n n w = w`:
  `⟪deriv u_n t, w⟫ + ν·stokesTestPairing (u_n t) w + F.b (u_n t) (u_n t) w = 0`.
  **Fires on any div-free test band-limited at level n. Forward-only.**
- `u_hasDeriv` (254): `HasDerivAt` at every `t ≥ 0` (gives `HasDerivAt.inner` chain rule).
- `energy_bound` (270): `½‖u_n t‖² ≤ ½‖Pₙu₀‖² ≤ ½‖u₀‖²` for `t ≥ 0` (n-uniform sup bound).
- `reg_bound` (282): `∫₀ᵀ h1EnergySq (u_n t) ≤ T‖u₀‖² + ‖u₀‖²/(2ν)` (n-uniform H¹ budget).
- `u_inVn` (244): `u_n t` band-limited at level n for every t.

### Existing tools this plan consumes (all verified present)

- `Torus3NSForms.b_bound` (`AxiomaticClosure.lean:170`): `IsGalerkinTest w → ∃ C, ∀ u v, |b u v w| ≤ C‖u‖‖v‖`.
- `stokesTestPairing` def (`AxiomaticClosure.lean:104–108`): the explicit mode sum
  `∑_j ∑'_k (2π)²|k|² Re(û_j(k)·conj(ŵ_j(k)))` — for band-limited `w` the k-sum is a
  **finite** `fourierBox` sum, so `|stokesTestPairing u w| ≤ C(w)·‖u‖` is a finite
  Cauchy–Schwarz (NEW small lemma, S1 below; no analogue exists yet — grep-verified).
- `velocityProjection_n_eq_of_le` (`TorusConvectionExtension.lean:744`): projection nesting.
- `velocityProjection_n_tendsto` (`VelocityGalerkin.lean:349`): `Pₙv → v` for every `v`.
- Fourier tail machinery (`RellichEmbedding.lean`): `L2C_norm_sub_fourierProjection_sq`
  (‖v−P_N v‖² = out-of-box tail, per component), `H1_tail_bound` (tail ≤ M²/(1+N²)).
- `viscousEnn` quartet (PUBLIC, `TorusTraceEnergy.lean:981,988,1016,1062`): the honest
  ENNReal mode-sum + Fatou lsc pattern — the template for the limit-curve tail bound (S6).
- Riesz weak-representative assembly pattern: `TorusTraceEnergy.lean` (PR #72) already
  builds a curve from countable inner-product data + Riesz; S4 reuses the pattern.
- Leray projection `lerayProjection` (M3, proved) — upgrades weak-in-`L2Sigma`
  convergence to weak-in-`L2VF` convergence (test v ↦ test `Π_σ v`), needed for
  per-mode coefficient convergence in S6.
- Cantor diagonalization precedents: `diag_ae_subseq` (R3 #44), #47 chain.
- mathlib: `Mathlib/Topology/UniformSpace/Ascoli.lean` exists but is the abstract
  compactness form; the plan does NOT depend on it (S3 is elementary; see below).

---

## 1. The mathematical route (why no Bochner Aubin–Lions–Simon is needed)

Classical Aubin–Lions–Simon is an abstract-Banach detour that mathlib lacks (verified
repeatedly: `r3b-pr0-verdict.md`). On T³ with the **spectral** Galerkin scheme, the
compactness proof can be executed mode-by-mode with only scalar tools:

**Step A (equi-Lipschitz scalar curves).** Fix a band-limited div-free test `w` (level
`m`). For every `n ≥ m` (nesting ⇒ `w` is a level-`n` test), `u_ode` + `HasDerivAt.inner`
give, for `t ≥ 0`:
`d/dt ⟪u_n t, w⟫ = −ν·stokesTestPairing (u_n t) w − F.b (u_n t) (u_n t) w`,
so `|d/dt ⟪u_n t, w⟫| ≤ ν·C₁(w)·‖u₀‖ + C₂(w)·‖u₀‖²` — **uniform in n and t** (by
`energy_bound`; constants from S1 + `b_bound`). Also `|⟪u_n t, w⟫| ≤ ‖u₀‖·‖w‖`. So
`{t ↦ ⟪u_n t, w⟫}ₙ` is a uniformly bounded, uniformly Lipschitz family on `[0,T]`.

**Step B (scalar compactness + diagonal).** A uniformly bounded L-Lipschitz sequence
`[0,T] → ℝ` has a uniformly convergent subsequence (Bolzano–Weierstrass pointwise on
`ℚ ∩ [0,T]` + diagonal + Lipschitz ⇒ uniform Cauchy). Elementary, scalar, NO vector-valued
measure theory. Diagonalize over the countable test family (S2) to get ONE subsequence
`φ` with `⟪u_{φ(n)} t, w_m⟫ → g_m(t)` uniformly on `[0,T]`, for every `m`.

**Step C (limit curve by Riesz).** For each `t`, `w_m ↦ g_m(t)` extends to a bounded
linear functional on `L2Sigma` (density of the family's span + uniform bound `‖u₀‖`);
Riesz gives `u(t) ∈ L2Sigma` with `⟪u t, w_m⟫ = g_m t` and `‖u t‖ ≤ ‖u₀‖`, and
`u_{φ(n)}(t) ⇀ u(t)` (weakly) for EVERY `t ∈ [0,T]`. Each `t ↦ ⟪u t, w_m⟫` is a uniform
limit of continuous functions, hence continuous. Since the family contains an orthonormal
basis of each finite-dim `velocitySpan N` (S2 design), `t ↦ P_N (u t)` is continuous, and
`u t = lim_N P_N (u t)` pointwise (`velocityProjection_n_tendsto`) ⇒ `u` is a pointwise
limit of continuous curves ⇒ **strongly measurable**. Field 4 falls out for free.

**Step D (finite-dim part converges strongly).** Fix `N`. `P_N` is an orthogonal
projection with finite-dim range; weak convergence at each `t` ⇒ coordinates against the
`velocitySpan N` orthonormal basis converge ⇒ `‖P_N(u_{φ(n)} t − u t)‖ → 0` for every
`t`, dominated by `2‖u₀‖`; DCT in `t` ⇒ `∫₀ᵀ ‖P_N(u_{φ(n)} t − u t)‖² dt → 0`.

**Step E (uniform tail).** Pythagoras for the orthogonal projection + the componentwise
tail identity: `‖v − P_N v‖²` = out-of-box mode sum ≤ `h1-tail/(1+N²)`-shaped bound
(`H1_tail_bound`). Integrate in `t` with `reg_bound`:
`∫₀ᵀ ‖u_n t − P_N (u_n t)‖² dt ≤ (T‖u₀‖² + ‖u₀‖²/(2ν)) / (1+N²)` — **uniform in n**.
For the limit curve: per-mode coefficient convergence (weak conv upgraded through
`lerayProjection` to L2VF tests) + Fatou over the mode sum + Fatou in `t` (the
`viscousEnn_lsc` ENNReal pattern) gives the SAME bound for `u`.

**Step F (assemble).** `∫₀ᵀ‖u_{φ(n)} − u‖² = ∫₀ᵀ‖P_N(…)‖² + ∫₀ᵀ‖tail(…)‖²`
(Pythagoras, pointwise in t): first term → 0 (D), second ≤ 2·C/(1+N²) uniformly (E).
`limsup ≤ 2C/(1+N²)` for every `N` ⇒ limit 0. Convert `∫‖·‖² → 0` to the `eLpNorm` form
(measurable by C, bounded by `2‖u₀‖` ⇒ MemLp; `eLpNorm`² = lintegral identity — the #44
dominated-convergence assembly has the precedent). Pack the four fields. Done.

**Every ingredient is scalar analysis, finite-dim linear algebra, Fourier tail sums, and
lintegral Fatou — all mathlib-present or already built in-repo. No `W^{1,p}(0,T;X)`, no
Steklov, no Simon, no vector-valued FTC.**

### Why this cannot work for R3-B (honesty check)

The route is spectral-scheme-specific three times over: (i) fixed band-limited tests are
`u_ode`-admissible at all levels `n ≥ m` (R3's L²-projection scheme has no analogous
Sobolev-stable fixed-test family); (ii) the tail bound is a Fourier-mode sum with the
`|k|² ≥ N²+1` spectral gap (R3 has continuous spectrum — no gap); (iii) `velocitySpan N`
is finite-dim with an explicit orthonormal basis. R3-B stays on the
`bochner-foundation-metaplan` route (lane #74). **Do not advertise this plan as removing
the shared "B-pair" — it removes T-B only.**

---

## 2. Phase 0 — the SPIKE (mandatory gate; NO scaffold before GO)

**Lesson enforced (from the R3 #69 wall postmortem): pressure-test EVERY conclusion
field and EVERY step's interface premise, not just the ones that look hard.** The R3
conjunct-2 wall was missed because the spike checked conjuncts 1&3 only.

Deliverable: `LerayHopf/Scratch/TorusAubinLionsSpike.lean` (campaign spike, since deleted) (`-- SCRATCH` header, marked
`ALLOW_SORRY: scratch` on target lines), typechecking against the real interfaces, +
verdict appended to this doc. Owner: **lean-architect (fable)**. Builder: incremental
`flock /tmp/lean-build.lock lake build LerayHopf.Scratch.TorusAubinLionsSpike` only.

Checklist — each item is a STATEMENT that must typecheck (sorry-marked bodies), plus the
listed non-Lean verifications:

- [ ] **P0.1 (test family).** Define `testFamily : ℕ → L2Sigma` enumerating, for each
  `N`, an orthonormal basis of `velocitySpan N` (finite-dim — verify the
  `FiniteDimensional` instance is available from `TorusGalerkinScheme.lean`; the ODE
  solver of #24 needed it, so it should be). Verify: countability bookkeeping (`ℕ ≃ Σ`
  encode), `IsGalerkinTest (testFamily m)`, and density: `⋃ N velocitySpan N` dense in
  `L2Sigma` (from `velocityProjection_n_tendsto` + `velocityProjection_n_preserves_L2Sigma`).
  RISK to check: how `velocitySpan` is defined (image of `P_N` on `L2Sigma`, per #24 —
  `mem_velocitySpan_of_fixed` needs the `w ∈ L2Sigma` side condition; see memory
  `project_torus_velocity_span_is_image_not_range`).
- [ ] **P0.2 (S1 statement).** `stokesTestPairing_bound_of_galerkinTest : IsGalerkinTest w
  → ∃ C, ∀ u : L2VF, |stokesTestPairing u w| ≤ C * ‖u‖` — statement typechecks; sanity:
  the proof is a finite `fourierBox` Cauchy–Schwarz (each coefficient functional bounded:
  `|mFourierCoeff3 (proj_j u) k| ≤ ‖u‖`-shaped; verify which normalization lemma provides
  it — `mFourierBasis_repr` / Bessel).
- [ ] **P0.3 (equi-Lipschitz statement).** For `w` band-limited at level `m`, `n ≥ m`,
  `0 ≤ s ≤ t ≤ T`: `|⟪u_n t − u_n s, w⟫| ≤ L(w,u₀,ν) * (t − s)`. Verify the derivative
  transfer: `HasDerivAt (fun s => ⟪(u_n s : L2VF), w⟫) …` from `u_hasDeriv` +
  `HasDerivAt.inner`, and the mean-value/FTC step on `[s,t] ⊆ [0,T]` (mathlib:
  `norm_image_sub_le_of_norm_deriv_le_segment` or `Convex.inner_smul_le_norm_mul_norm`-free
  route; confirm the exact lemma name).
- [ ] **P0.4 (S3 engine statement).** `exists_uniform_subseq_of_lipschitz_family`:
  countable family of uniformly bounded, per-family-uniformly-Lipschitz real sequences on
  `[0,T]` ⇒ one strictly-mono `φ` with uniform convergence for every family member.
  Confirm the mathlib primitives: bounded-real B–W (`tendsto_subseq_of_bounded` /
  `Bornology.IsBounded.exists_seq …` — pin the exact name), `StrictMono.comp`, and decide
  Ascoli-vs-hand-rolled. The statement must be **domain-neutral scalar** (reusable).
- [ ] **P0.5 (Riesz/limit-curve statements).** The S4 statements: weak limit at every t,
  `‖u t‖ ≤ ‖u₀‖`, per-test continuity, `AEStronglyMeasurable` via pointwise limit of
  continuous `P_N ∘ u`. Verify `Continuous.aestronglyMeasurable` + pointwise-limit
  measurability lemma names (`aestronglyMeasurable_of_tendsto_ae` shape).
- [ ] **P0.6 (tail statements).** (a) the VECTOR tail identity `‖v − velocityProjection_n
  N v‖² = Σ_j out-of-box component tails` (assemble from `L2C_norm_sub_fourierProjection_sq`
  — check the L2VF↔component bridge lemmas in `VelocityGalerkin.lean`); (b) the h1
  domination `out-of-box tail ≤ h1EnergySq v/(1+N²)` (relate `h1EnergySq`'s exact
  definition to `H1_tail_bound`'s hypothesis shape — verify `h1EnergySq` def matches the
  `(1+Σkᵢ²)`-weighted sum, `SobolevTorus.lean`); (c) interval-integral monotonicity to
  consume `reg_bound`; (d) the limit-curve Fatou statement (ENNReal mode-sum, mirror
  `viscousEnn_lsc`'s structure).
- [ ] **P0.7 (conclusion-shape dry run).** State the final
  `torusAubinLionsPackage_of_galSeq` def with the axiom's EXACT binder list and
  `AubinLionsPackage` conclusion; typecheck with a sorry body. This is the "all-conjuncts"
  pressure test — the package has 4 fields and ALL of them must be visibly reachable from
  P0.1–P0.6 before GO.
- [ ] **P0.8 (eLpNorm conversion).** Statement converting `Tendsto (fun n => ∫₀ᵀ ‖…‖²) …
  (𝓝 0)` + AEStronglyMeasurable + a.e.-bound into the `eLpNorm`-form field 3. Verify the
  exact `eLpNorm`/`lintegral` bridge lemmas (`eLpNorm_eq_lintegral_rpow_enorm` etc. — the
  R3 #44/#47 assemblies contain working patterns to copy).

**GO criterion:** all statements typecheck AND no checklist item surfaces a
missing-interface fact that cannot be stated. **NO-GO handling:** the failing item comes
back to the architect (fable) for route revision — the orchestrator does NOT improvise an
alternative route (doctrine §D3, `docs/agent-roles.md`).

### ★ PHASE-0 VERDICT (architect/fable, 2026-07-03): **GO**

`LerayHopf/Scratch/TorusAubinLionsSpike.lean` — ALL 11 statements typecheck on the first
build (`flock … lake build LerayHopf.Scratch.TorusAubinLionsSpike`, EXIT=0, 2953 jobs,
only the expected marked-sorry warnings; module NOT in the default build target).
Covered: P0.2 (S1 stokes bound), P0.1 (test family — finite-SPANNING design adopted
instead of ONB: weak→strong in finite-dim and `t ↦ P_N(u t)` continuity need only a
finite spanning set of each `velocitySpan N`; `velocitySpan_finiteDimensional` verified
present), P0.3 (equi-Lipschitz, forward-only), P0.4 (S3 scalar engine, domain-neutral
statement), P0.5 (S4 Riesz limit curve: ∀t weak conv against `L2Sigma` tests + ball
bound + AEStronglyMeasurable — all three package-relevant conclusions stated), P0.6a/b/b′/c
(vector tail identity; H¹ domination gated on `memH1VF` so the `tsum` junk-0 trap is
closed; `h1EnergySq`-continuity for band-limited curves to consume `reg_bound` soundly;
ENNReal tail lsc under WEAK convergence for the limit curve), P0.8 (eLpNorm conversion),
P0.7 (conclusion dry run: `torusAubinLionsPackage_of_galSeq` with the axiom's binder
list byte-copied INCLUDING `spatial`, conclusion `AubinLionsPackage F ν T u₀ galSeq` —
all five fields reachable from the pieces above).

Residual proof-time (not statement-time) items, flagged for the owning PRs: pin the
exact mathlib names for bounded-real Bolzano–Weierstrass (T-AL-2), the MVT/FTC step for
P0.3 (T-AL-3), the coefficient-functional-as-inner-product Riesz upgrade for P0.6c
(T-AL-5), and the `eLpNorm`↔`lintegral` bridge (T-AL-6; copy the #44/#47 patterns).
None of these is a statement risk. Next action: T-AL-1 (coder transcribes S1 + the
test-family statements from the spike verbatim into `LerayHopf/TorusTestFamily.lean`).

STATEMENT-GATE AMENDMENT (codex P2, PR #77 round 1): P0.4's Lipschitz hypothesis is
**eventual** — `∀ m, ∃ n₀, ∀ n ≥ n₀, …` (per-family band-limit cutoff), because P0.3
supplies the estimate only for `n ≥ m`. Boundedness stays universal (`energy_bound`
holds for all n). Conclusion unchanged (tail property). The spike file carries the
corrected statement; T-AL-2 must implement THIS form.

---

## 3. PR sequence (after GO), owners, and gates

Small-PR rule applies; each PR lands only with local incremental build green +
grep-guardrails PASS + codex broker review. **Every NEW statement gets
`/codex:adversarial-review --effort xhigh` at the statement stage, before proof
dispatch.** Statement text is frozen by the architect; provers never edit statements.

| PR | Content | Lean file | Owner (proof) | Notes |
|----|---------|-----------|---------------|-------|
| T-AL-1 | S1 `stokesTestPairing_bound_of_galerkinTest` + S2 `testFamily` (def + `IsGalerkinTest` + density + per-N ONB property) | new `LerayHopf/TorusTestFamily.lean` | sonnet (S1), opus (S2 density/ONB) | coder scaffolds signatures from the spike verbatim |
| T-AL-2 | S3 scalar engine `exists_uniform_subseq_of_lipschitz_family` (+ its small B–W/diagonal helpers) | new `LerayHopf/Bochner/ScalarEquicontinuity.lean` (domain-neutral) | **opus**; escalate to fable if 2 sessions stall | the one genuinely new "engine"; scalar-elementary but decomposition-sensitive |
| T-AL-3 | Step A+B wiring: equi-Lipschitz lemma (P0.3) + apply S3 over `testFamily` → the extraction `φ` + uniform per-test limits | new `LerayHopf/TorusModeCompactness.lean` | opus | consumes T-AL-1/2 |
| T-AL-4 | Step C+D: Riesz limit curve, weak convergence ∀t, measurability, finite-dim strong part (DCT) | same file | **fable** (statement subtleties: ∀t vs a.e., forward-only domain) with sonnet chore split | the soundness-critical PR |
| T-AL-5 | Step E: uniform tail + limit-curve Fatou tail | same file or `TorusModeTail.lean` | opus (Fatou mirror of `viscousEnn_lsc`) | reuse quartet patterns |
| T-AL-6 | Step F assembly `torusAubinLionsPackage_of_galSeq` + **delete `axiom aubin_lions`** + rewire `build_galerkin_package_of_galSeq` + `check-axioms-live.sh` pin torus→0 + STATUS.md banner | `AxiomaticClosure.lean`, `TorusGalerkinODECapstone.lean`, scripts | lean-coder (sonnet) + pr-reviewer + modularity-reviewer fan-out | acyclicity note: the assembly file must sit downstream of `AxiomaticClosure` (mirror the #75 relocation pattern) |

Estimated scale: 5–6 merged PRs, days-to-2-weeks-class at the #25 cadence — NOT
months-class. The single riskiest node is T-AL-4's statement design (∀t-vs-a.e. and
forward-only-time traps — both bitten before; see memories
`project_torus_galerkin_solution_data_overstrength`, `project_r3_15_aubinlions_thinswap`).

### Kill criteria (honest walls, checked at spike + each PR)

- P0.1 fails structurally (no finite-dim instance / no ONB extraction for
  `velocitySpan N`) → fall back to explicit transverse trigonometric mode tests (heavier
  but constructible); if THAT fails, NO-GO and revert to the bochner-metaplan T-B port.
- S3 turns out to need uncountable-family or non-Lipschitz machinery → route error;
  architect revisits (should not happen: Lipschitz constants are per-test, countably many).
- The `eLpNorm` conversion (P0.8) hits a measurability gap for `fun t => u_{φ(n)} t − u t`
  → u_n is continuous on `[0,T]` (differentiable forward), u is measurable by C; the
  difference is fine — if a gap appears it is a statement bug, not a wall.

---

## 4. Out-of-scope / adjacent items (recorded so nobody improvises)

- **R3-B (#46):** lane #74 (fable, other host). HANDS OFF from this lane. No file overlap:
  this campaign touches only torus files + a new domain-neutral scalar file.
- **R3-C (#4 / PR #69):** PARKED at the verified conjunct-2 wall (codex P1 ×2 on PR #69,
  2026-07-01: `u_ode` fires only on Galerkin-range tests; bridging `P_N w → w` needs
  H²+W^{1,∞}-stability the L²-projection scheme lacks). Sound unlock = Sobolev-stable
  div-free basis witness swap (codex "Option A") — its own future architect spike, after
  torus-zero. **Cleanup task (small, separate PR):** the sorry comment at
  `LerayHopf/R3/AubinLionsLimitPassage.lean:2424` on main still claims
  "(c) DENSITY UNNECESSARY … (Earlier "interface wall" claim RETRACTED)" — this is the
  OPTIMISTIC PRE-WALL text, contradicted by the verified wall (opus prover + codex
  gpt-5.5 independent confirmation, 2026-07-01, memory
  `project_limit_passage_r3_removal_campaign`). Rewrite that comment to state the wall
  and point here. Comment-only edit; needs one incremental rebuild of the R3 chain, so
  batch it with the next R3-touching PR rather than shipping alone.
- **Issue #25:** work merged in PR #75; close with a pointer (bookkeeping).
- After torus-zero: do NOT rename `exists_lerayHopf_torus3_axiomatic` (no-rename rule);
  add a doc-comment + STATUS banner announcing unconditionality; a separate alias theorem
  can be proposed to the owner if they want a headline name.

## 5. Definition of done

- `axiom aubin_lions` deleted from `AxiomaticClosure.lean`; no new axiom/opaque anywhere.
- `#print axioms exists_lerayHopf_torus3_axiomatic` = kernel axioms only (torus **0**
  project axioms); `scripts/check-axioms-live.sh` pin updated and EXIT=0 **run locally**.
- `bash scripts/agent-preflight.sh` green (incremental); grep-guardrails PASS.
- Issues #23 closed, #26 updated (1 domain done); STATUS.md banner updated.
- All six PRs codex-reviewed via the broker (`$REVIEW_ACQUIRE_SCRIPT`, kind `codex`),
  every finding resolved or explicitly owner-waived.
