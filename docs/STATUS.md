# STATUS — autonomous run ledger

Running ledger for the autonomous build of Leray–Hopf weak existence on the real
3-torus. This file is the **integrity backstop and final report**: every `sorry` and
every `axiom` in the Lean sources is listed here with a reason, a reference, and a
plan to discharge it. Higher-level scope/posture: the approved plan and `docs/milestone.md`.

## Goal (authoritative)

Build the Leray–Hopf weak-existence formalization on the **real 3-torus**, bottom-up on
mathlib, as far as possible toward an **unconditional T³ existence theorem**
(`u₀ ∈ L²_σ(𝕋³) ⇒ ∃ Leray–Hopf weak solution`). Reduce anything not closable to a
**documented marked-`sorry` frontier** with exact statements. R³ is out of scope.

Roadmap: M1 spine ✅ → M2 real domain & function spaces → M3 Galerkin `Pₙ` + Leray `Π_div`
→ M4 finite-dim Galerkin ODE + energy identity → M5–7 compactness + Aubin–Lions on T³
(Fourier-tail Rellich, the crux) + limit passage ⇒ unconditional T³.

**Posture:** maximal depth, minimal axioms. Prove what mathlib supports; axiomatize only
the true frontier (each with `ALLOW_AXIOM` + reference + ledger entry); leave
provable-but-unfinished pieces as *marked* `sorry`, never as weakened/vacuous/renamed
statements.

**Method:** branch `autorun/leray-hopf-torus3`, 1 milestone = 1 commit gated by
`bash scripts/agent-preflight.sh` green. Strict role delegation to subagents
(planner/coder/reviewers = sonnet, prover = fable; read-only reviewers) under their
`.claude/agents/*.md` contracts; orchestrator owns Codex `--effort xhigh` calls and
maintains this ledger as the final report.

## Milestone status

| # | Milestone | State |
|---|---|---|
| M1 | Structural spine (Basic/Statement/GalerkinPackage/ExistenceFromPackage/EnergySkeleton) | in progress |
| Side A/B | Blow-up lower bound · nonuniqueness statement | done (pending commit) |
| M2 | Real domain & function spaces (Torus3, L²(T³), L²_σ, H¹, Bochner) | **done** (axiom-free) |
| M3 | Galerkin P_n + Leray Π_div (Fourier multipliers) | **done** (axiom-free) |
| M4 | Finite-dim Galerkin ODE + energy identity | **abstract done** (axiom-free); concrete = frontier |
| M5–7 | Compactness + Aubin–Lions on T³ + limit passage → unconditional T³ | **Rellich done** (axiom-free); time-compactness + limit passage = frontier |
| M6 | **Sound minimal-axiom closure of T³ existence** (`exists_lerayHopf_torus3`) | **DONE** — proved modulo exactly 4 Codex-approved axioms; abstract evolution framework for R³ reuse |
| R3 | **Whole-space ℝ³ Leray–Hopf existence** (`exists_lerayHopf_r3`) — the real target (Leray 1934) | **DONE** — proved modulo exactly 6 Codex-approved axioms; ℝ³ spatial+regularity layer built axiom-free; abstract layer reused unmodified |
| R3-d | **Concrete trilinear convection estimate** (`LerayHopf/R3/TrilinearEstimate.lean`) — upgrades the `r3_NSForms_exist` axiom's *justification prose* into 11 proved, axiom-free lemmas about `convIntegralSchwartz` | **DONE** (axiom-free) — multilinearity (6), integrability, direct H¹ bound, **IBP identity**, **antisymmetry under div-free**, and the genuine **`b_bound` shape** `\|b(u,v,w)\| ≤ C(w)·‖u‖₂·‖v‖₂`; each `#print axioms`-clean (only propext/Classical.choice/Quot.sound). Does NOT remove the axiom (defining `b` on all of L²_σ still needs the `(u·∇)v` operator), but substantiates its analytic content |
| P5 | **Galerkin scheme constructive content** (`LerayHopf/R3/GalerkinScheme.lean`) — substantiates the `r3GalerkinScheme_exists` axiom by *constructing* the scheme from a Schwartz div-free basis | **DONE** (axiom-free) — `nonempty_r3GalerkinScheme_of_basis (B : SchwartzGalerkinBasis) : Nonempty R3GalerkinScheme` builds all six structure fields from orthogonal projections (`Submodule.starProjection`) onto finite prefix-spans of `B`; the one classical input (density of smooth div-free fields in L²_σ, a Helmholtz/Weyl fact) is the bundled hypothesis `B.dense_span`, not an axiom. `#print axioms`-clean. **Soundness fix (Codex-confirmed):** `R3GalerkinScheme.tendsto_id` weakened from `∀ u : L2VF_R3` to the honest `∀ u ∈ L2Sigma_R3` (a div-free Galerkin scheme is total only in Σ; the unrestricted form was a latent over-strength never consumed by the closure). `exists_lerayHopf_r3` unaffected (still 6 project axioms, no sorryAx). Does NOT remove the axiom (unconditional `Nonempty SchwartzGalerkinBasis` still needs the density fact) |
| P3 | **LOCAL Rellich–Kondrachov on ℝ³** (`LerayHopf/R3/SpatialCompactness.lean`) — substantiates the `spatial_compactness_R3` axiom by proving the full reduction axiom-free from one isolated frontier hypothesis | **DONE** (axiom-free) — `localCompactness_R3_of_ballCompact (B : LocalRellichInput)` reproduces the **byte-identical** `spatial_compactness_R3` conclusion (per-ball L² subsequence convergence of any L²∩H¹-bounded div-free sequence, limit in `L2Sigma_R3`). The reduction is fully proved: per-ball extraction (`IsCompact.tendsto_subseq`), countable diagonal over expanding balls, global glue `g₀ x := g(⌈dist x 0⌉)x` with `MemLp` via ball-exhaustion, div-free closure via the **G5 ε/3 ball-truncation** (`divTestFunctional φ g = lim = 0`: ball part by local convergence + Cauchy–Schwarz tail uniform in `n` via `‖z n‖≤M` + Schwartz/L²-tail→0). The ONE classical input — local compact embedding `H¹(B_R)↪↪L²(B_R)` (mathlib lacks Rellich) — is the bundled hypothesis `LocalRellichInput.ballCompact` (Codex-confirmed non-smuggling), not an axiom. `#print axioms`-clean. `exists_lerayHopf_r3` unaffected. Does NOT remove the axiom (unconditional local compactness still needs the embedding) |

## M2 design decisions (orchestrator, adopted)

- **0-A velocity codomain:** `VelocityValue := EuclideanSpace ℝ (Fin 3)` (physically faithful
  ℝ³ energy inner product). Fourier work uses component-wise ℝ↪ℂ embedding, made explicit.
- **0-B measure normalization:** probability/Haar (total mass 1), consistent with `mFourierBasis`
  (`AddCircleMulti` uses `haarAddCircle`). The `volume` vs `haarAddCircle` definitional match at
  `T = 1` is a known M2 friction point (planner D-06); to be verified by lean-coder.

## Axiom ledger

**Posture shift (M6):** T³ is the warm-up scaffold, not the destination (R³ is). Per the
approved plan `ssot-reference-list-cuddly-meteor.md`, the remaining T³ analytic frontier is
decomposed into **four minimal, true, literature-referenced axioms** that close the T³
existence theorem, with the framework built abstractly for R³ reuse. The **spatial** Rellich
compactness is *not* axiomatized — it is the proved `rellich_seq_compact`/`rellich_L2Sigma`,
discharged into the Aubin–Lions axiom as an explicit hypothesis. Every axiom passed a Codex
`--effort xhigh` soundness audit (8 rounds; see the Codex log).

The four axioms (in `LerayHopf/AxiomaticClosure.lean`; `## Assumptions` section there):

| Axiom | Statement (informal) | Why TRUE / NON-VACUOUS | Reference |
|---|---|---|---|
| `torus3_NSForms_exist` | ∃ the 𝕋³ convection trilinear form `b` (antisymmetric, trilinear, with the true 3D smooth-test bound `|b(u,v,w)|≤C‖u‖_{L²}‖v‖_{L²}` for Galerkin `w`), pinned on Galerkin subspaces to the concrete `galerkinConvection` | the genuine `(u·∇)v` form witnesses it; `b=0` is excluded by the `galerkinConvection` pin (non-vacuous). Viscous form is **concrete** (`stokesTestPairing`/`viscousFormSq`), not axiomatized. | Temam II.§1; RRS §3.2 |
| `galerkin_ode_solution` | the `n`-th finite-dim projected NS ODE has a global solution `uₙ` with `uₙ(0)=Pₙu₀`, the projected ODE, H¹ regularity, and uniform (n-indep) energy + dissipation bounds | Picard–Lindelöf on finite-dim `Vₙ` + energy identity (`b(u,u,u)=0`) preventing blow-up | Temam III.3 |
| `aubin_lions` | from a Galerkin sequence + uniform bounds + an explicit **spatial-compactness hypothesis** (= `rellich_L2Sigma`, discharged), extract a subsequence converging strongly in `L²(0,T;L²_σ)` | classical Aubin–Lions; axiom adds ONLY the missing Bochner-time half (spatial half proved) | Temam III.2.1 |
| `galerkin_limit_passage` | from the structured sequence + the strong-L² limit, ∃ a **good representative** `u` (a.e.-equal to the limit) satisfying `WeakFormNS ∧ energy-ineq ∧ initial-trace ∧ energy-class (u∈L²(0,T;H¹_σ))` | strong-L² convergence kills the nonlinear error; lsc energy; existential good representative is null-set-invariant and tied a.e. to the Aubin–Lions limit | Temam III.3 |

`b(u,u,u)=0` is a **proved lemma** (`Torus3NSForms.b_self_zero`) from antisymmetry, NOT an axiom.
`#print axioms exists_lerayHopf_torus3` → exactly these 4 + `propext`/`Classical.choice`/`Quot.sound`
(no `sorryAx`).

### ℝ³ (whole-space) — the 6 axioms (`LerayHopf/R3/AxiomaticClosure.lean`)

The ℝ³ spatial+regularity layer is **built axiom-free** (`R3/Domain.lean`, `DivergenceFree.lean`,
`Regularity.lean`): `L2Sigma_R3 := ⨅ φ:𝓢, ker(divTestFunctional φ)` (weak divergence against Schwartz
tests; closed div-free subspace), `lerayProjection_R3`, `memH1VF_R3` (via `MemSobolev`),
`stokesTestPairing_R3`/`viscousFormSq_R3` (via the L² Fourier transform `Lp.fourierTransformₗᵢ`),
`convIntegralSchwartz` (the genuine convection integral on Schwartz fields). The abstract
`DissipativeEvolution`/`WeakFormNS`/`AbstractEnergyLaw` layer is **reused unmodified**.

| Axiom | Role | T³ analogue | Why ℝ³ needs it |
|---|---|---|---|
| `r3GalerkinScheme_exists` | Galerkin approximation-projection family (range Schwartz div-free) | T³ **PROVED** `velocityProjection_n` | ℝ³ frequency-truncation subspaces are infinite-dim; indicator Fourier multiplier not in mathlib (Paley–Wiener) |
| `r3_NSForms_exist` | ℝ³ convection form `b` (antisym, trilinear, smooth-test bound), **non-vacuity pinned** to the genuine `convIntegralSchwartz` | T³ A4 `torus3_NSForms_exist` | missing `(u·∇)v` operator on ℝ³ |
| `galerkin_ode_solution_R3` | approximate ODE + uniform energy/dissipation bounds + H¹ regularity | T³ A1 | Temam III.3 |
| `spatial_compactness_R3` | **LOCAL** Rellich `H¹(B_R)↪↪L²(B_R)` ⇒ L²_loc-convergent subsequence | T³ **PROVED** `rellich_L2Sigma` | **global Rellich FAILS on ℝ³** — the structurally-new axiom; local form is TRUE without tightness |
| `aubin_lions_R3` | Aubin–Lions; takes `spatial_compactness_R3` as hypothesis (not discharged) | T³ A2 | Temam III.2.1 |
| `galerkin_limit_passage_R3` | existential good representative (a.e.-linked), weak form + energy-ineq + trace + energy-class | T³ A3 | Temam III.3; local convergence + Schwartz-test decay |

The 2 extra axioms vs T³ (`r3GalerkinScheme_exists`, `spatial_compactness_R3`) are **exactly the two
pieces T³ PROVED** (`velocityProjection_n`, `rellich_L2Sigma`) but ℝ³ cannot — the honest cost of the
unbounded domain. `R3NSForms.b_self_zero` is a proved lemma. `#print axioms exists_lerayHopf_r3` →
exactly these 6 + `propext`/`Classical.choice`/`Quot.sound` (no `sorryAx`).

**Earlier (M2) axiom eliminated:** the M2 plan tentatively proposed `L2Sigma_eq_divFreeL2`
(closure-of-span ↔ Fourier-diagonal). **Eliminated**: `L²_σ` is defined *directly* as
`⨅ k, ker (divSymbol k)`, so membership coincides with `DivFreeL2` by construction (no axiom),
and `L²_σ` is a closed submodule giving its Hilbert structure + Leray projection for free.

## Sorry frontier

**In the Lean tree:** still ZERO frontier `sorry`. The only `sorry` is the deliberate target
statement `exists_lerayHopf_torus3_statement` (not frontier debt — see Notes). No axioms.
Every M1–M4(abstract) must-prove target is sorry-free and `#print axioms`-clean.

**The genuine analytic frontier (NOT coded — documented here, not faked as sorry/axiom).**
Reaching unconditional T³ existence requires the following, each blocked by *structural mathlib
absences* (not hard-but-routine proofs). They are demarcated as future work, with the abstract
interfaces (`AbstractEnergyLaw`, `GalerkinCompactnessPackage`) already in place to receive them:

| Frontier item | Precise content | Blocker |
|---|---|---|
| Concrete NS convection `b(u,v,w)` | `∫_{𝕋³} ((u·∇)v)·w` on `L²/H¹` torus fields | mathlib has no `(u·∇)v` for `Lp` a.e.-classes; needs torus weak-derivative/Fourier-convection API |
| Nonlinear cancellation `b(u,u,u)=0` | skew-symmetry for divergence-free `u` | needs torus integration-by-parts; mathlib's divergence theorem is for ℝⁿ boxes only |
| Galerkin ODE existence | `uₙ` solving the projected ODE via `PicardLindelof` | API exists but gated on the concrete RHS above |
| ~~Rellich on T³~~ **DONE** | `H¹(𝕋³)`-ball totally bounded in `L²(𝕋³)` (`H1_ball_totallyBounded`), via Fourier-tail decay | ✅ proved axiom-free (M5) — the Aubin–Lions *spatial* linchpin |
| Aubin–Lions (full, time) | time-equicontinuity + Rellich ⟹ strong `L²(0,T;L²)` compactness | needs Bochner time-derivative bounds + Arzelà–Ascoli plumbing (Rellich half done) |
| Limit passage | weak-* + strong-L² limits ⟹ weak solution | needs the above + Banach–Alaoglu plumbing |

The **abstract energy law ⟹ energy inequality ⟹ nonincreasing energy** chain is fully proved
(`AbstractEnergyLaw`); only the *concrete construction supplying* such a law is frontier.

## Known scaffold caveats (disclosed, not hidden)

These are deliberate properties of the M1 scaffold, recorded so they are never mistaken
for proved mathematics. Each is discharged by the monotone refinement of placeholders.

- **`ExistsLerayHopf` is vacuous at M1.** `LerayHopfSolution`'s analytical fields are free
  `Prop` placeholders, so `ExistsLerayHopf Ω u₀` is structurally inhabited and is *not*
  yet a meaningful existence claim. `exists_lerayHopf_from_galerkin_package` is therefore a
  real but currently low-content implication (package ⟹ solution). The target
  `exists_lerayHopf_torus3_statement` is kept as a marked `sorry` and must **not** be
  discharged via a junk package. _Discharge:_ M2+ refines the `Prop` fields into real
  predicates (`WeakEquation`, `EnergyClass`, …) tied to the candidate field, `u₀`, `Ω`,
  after which the implication carries genuine analytical content.
- **`Torus3` is a fresh placeholder with the zero measure**, not the real torus. The zero
  measure is intentionally wrong-but-honest (signals "unrealized"). _Discharge:_ M2 realizes
  `Torus3 := UnitAddTorus 3` with Haar/volume measure.

## Codex adversarial-review log

- **M1 spine** (`/codex:adversarial-review --effort xhigh`, working tree): verdict
  *needs-attention*, 3 findings.
  - [high] no-sorry guard could fail open → **fixed**: `scripts/check-no-sorry.sh` rewritten
    to fail closed (single non-suppressed `awk`; scanner error ⇒ nonzero exit; verified by test).
  - [medium] `Torus3 := ℝ` leaked real-line semantics → **fixed**: fresh `PUnit`-backed
    placeholder with zero measure.
  - [high] structural theorem vacuous / `ExistsLerayHopf` overclaim risk → **disclosed** (see
    "Known scaffold caveats"); structural redesign deferred to M2+ refinement per the
    plan-authoritative interface. Not closable at M1 without real function spaces.
- **Side A/B** (`--effort xhigh`, working tree): verdict *needs-attention*, 2 findings.
  - [high] Branch A `lower_bound_from_inverse_square_lifespan` proved the *opposite* direction
    (an upper bound on `N`), overclaiming its name. The MVP-plan code sketch was itself
    inconsistent with Branch A's stated lower-bound intent. → **fixed**: statement flipped to
    the genuine lower bound (`C/N² ≤ T−t ⇒ 1/N ≤ √((T−t)/C)`, i.e. `N ≥ √(C/(T−t))`),
    reproved sorry-free by lean-prover.
  - [medium] Branch B `LerayHopfNonunique` froze initial data at universe 0 (non-monotone vs
    the `Type*` interface) → **fixed**: explicit `universe u v`, `Ω : Type u`, `u₀ : Type v`.
- **M2-part1 function spaces** (`--effort xhigh`, `FunctionSpaces.lean`/`TorusDomain.lean`):
  verdict *needs-attention*, 2 findings, both fixed.
  - [high] two non-defeq torus measures (`L2VF` on `volume`, `L2C`/basis on `haarTorus3`)
    would force measure-transport at every M3 boundary → **fixed**: unified all torus L²
    spaces on the single canonical `haarTorus3`; added proven bridge
    `volume_torus3_eq_haarTorus3`.
  - [medium] `mFourierCoeff3` doc claimed a global-`volume` integral while `L2C` is Haar-based
    (Parseval-divergence risk) → **fixed**: redefined `mFourierCoeff3 := torus3_mFourierBasis.repr`.
  - `IsProbabilityMeasure (volume : Measure UnitAddCircle)` instance confirmed sound/non-conflicting.
- **M2 `DivFreeL2`** (`--effort xhigh`, `DivergenceFree.lean`): verdict *approve*. Confirmed the
  Fourier characterization `∑_j k_j û_j(k)=0 ∀k` faithfully encodes `div u = 0` (2π/i
  normalization cancels in the `=0` condition), `compLpL` a.e. semantics correct, non-vacuous.
- **M2 `L2Sigma`** (`--effort xhigh`, `Leray.lean`): verdict *approve*. `⨅ k, ker(divSymbol k)`
  is the genuine divergence-free subspace by construction; closedness sound (continuous kernels
  + arbitrary closed intersection); axiom-free (`#print axioms`: only propext/Choice/Quot).
- **M3-part1 projections** (`--effort xhigh`, `Leray.lean`/`GalerkinProjection.lean`): verdict
  *needs-attention*, 2 findings, both fixed.
  - [medium] `lerayProjection` docstring overclaimed a Helmholtz gradient-kernel theorem not
    formalized → **fixed**: docstring states only the proved orthogonal-projection facts
    (kernel = `L2Sigma`ᗮ); Helmholtz identification flagged as future work.
  - [medium] `Pₙ` not connected to Fourier truncation → **fixed**: proved
    `fourierProjection_n_mFourierCoeff` (`P̂ₙf(k) = if k ∈ box then f̂(k) else 0`), the genuine
    Fourier-multiplier formula, sorry-free/axiom-clean. Leray projection (idempotent, range,
    self-adjoint, contraction, fixes div-free) + `Pₙ` convergence `Pₙf→f` all sorry-free.
- **M3-part2 velocity Galerkin** (`--effort xhigh`, `VelocityGalerkin.lean`): verdict *approve*,
  no findings. `velocityProjection_n : L2VF →L[ℝ] L2VF` (componentwise truncation) with
  `velocityProjection_n_tendsto` (`Pₙu→u`) and `velocityProjection_n_preserves_L2Sigma`
  (truncation preserves div-free) proved sorry-free/axiom-clean. The real-valuedness of `Pₙ`
  on real inputs is proved (`conjL2C_fourierProjection`: conjugate-symmetric coefficients +
  symmetric box). Bonus: `mFourierCoeff3 f k = ∫ mFourier(-k)·f ∂haarTorus3` holds by
  `mFourierBasis_repr` with NO measure bridge — confirms the M2 measure unification is
  definitionally exact.
- **M4 abstract energy** (`--effort xhigh`, `EnergyEstimate.lean`): verdict *needs-attention*,
  2 findings, both fixed.
  - [medium] capstone didn't supply the nonneg-dissipation premise for `energy_nonincreasing`
    → **fixed**: added `accumulatedDissipation_nonneg` + `energy_nonincreasing` (proved),
    closing the bridge to `EnergySkeleton`.
  - [medium] `GalerkinApproximation` name overclaimed (it's an abstract scalar energy law, not
    a full Galerkin construction) → **fixed**: renamed `AbstractEnergyLaw` with a docstring
    stating the concrete Galerkin construction is frontier. Abstract energy identity/inequality
    proved sorry-free/axiom-clean.
- **M5 Rellich compact embedding** (`--effort xhigh`, `RellichEmbedding.lean`): verdict
  *approve*, no findings. Confirmed `H1_ball_totallyBounded` is the GENUINE non-vacuous Rellich
  (H¹-ball precompact in the ambient L² metric; set non-empty via `memH1Torus_zero`), Parseval
  (L1) correct, tail bound (L3) correct, `‖f−Pₙf‖²` = out-of-box tail (L2) correct. All 6 lemmas
  (L1–L4, the finite-rank compactness Bonus, L5) sorry-free and `#print axioms`-clean. The
  Aubin–Lions *spatial* linchpin on T³ — the user's key strategy — is cracked, axiom-free.

- **M6 axiomatic closure** (`/codex:adversarial-review --effort xhigh`, working tree,
  `AxiomaticClosure.lean` + `EvolutionTriple.lean`): **8 rounds** of adversarial axiom auditing,
  ending in **`approve`**. Codex caught and forced fixes to, in order:
  (v1) a hidden inconsistency — `stokes`/`b` under-specified off-diagonal, with the ∀-`F` ODE axiom
  demanding `stokes(u,0)=0` ⇒ added `b` trilinearity + `stokes` bilinearity;
  (v1) a FALSE 3D convection bound (`H¹×H¹→L²`) ⇒ replaced with the true smooth-test bound
  `|b(u,v,w)|≤C‖u‖_{L²}‖v‖_{L²}` for Galerkin `w` (via antisymmetry);
  (v1) `WeakFormNS` testing all of L² ⇒ restricted to `isTest` (Galerkin/smooth div-free) tests;
  (v2) the Aubin–Lions package's `galSeq` untied to the input ⇒ parameterized the package by `galSeq`;
  (v2) energy inequality stated for all `t≥0` ⇒ scoped to `[0,T]`;
  (v3) `stokes` pinned only on the diagonal (free skew term) ⇒ added symmetry (polarization pins it);
  (v4) a TOTAL real Stokes form with H¹ diagonal is impossible (∞ off H¹) ⇒ **de-axiomatized** the
  viscous form entirely (concrete `stokesTestPairing`/`viscousFormSq`); A4 is now convection-only;
  (v5) energy inequality didn't enforce the H¹ energy class (`tsum` collapse) ⇒ proof-carry
  a.e.-`memH1VF` + integrable dissipation (`u∈L²(0,T;H¹_σ)`);
  (v6) A3 asserted pointwise facts for an arbitrary null-set representative ⇒ made A3 **existential**
  (a good representative exists);
  (v7) the existential became untethered (≈ standalone existence) ⇒ added the a.e.-link
  `∀ᵐ t, u t = alPkg.u t` to the Aubin–Lions limit; (v8) **approve**.
  Final assembly proved sorry-free; `#print axioms exists_lerayHopf_torus3` = the 4 axioms +
  `propext`/`Classical.choice`/`Quot.sound`.
- **R3 ℝ³ axiomatic closure** (`/codex:adversarial-review --effort xhigh`, `R3/AxiomaticClosure.lean`):
  **2 rounds** → **`approve`** (the T³ audit lessons applied preemptively converged it fast). Codex
  caught and forced fixes to: (v1-crit) `R3GalerkinScheme` admitting the identity map (which collapsed
  `IsGalerkinTest_R3` to all of L² and falsified `b_bound`/`reg_mem`) ⇒ added `range_schwartz` forcing
  the projector range to be Schwartz div-free; (v1-high) `aubin_lions_R3` asserting **global** ℝ³
  compactness (false without tightness) ⇒ reformulated `spatial_compactness_R3`/`aubin_lions_R3` to
  **LOCAL** L²(B_R) convergence (true local Rellich, no tightness; Schwartz-test decay handles the
  tail); (v2) **approve**. Final assembly proved sorry-free; `#print axioms exists_lerayHopf_r3` = the
  6 ℝ³ axioms + `propext`/`Classical.choice`/`Quot.sound`. The ℝ³ spatial+regularity layer
  (`R3/Domain`, `DivergenceFree`, `Regularity`) is axiom-free.

## Notes

- `exists_lerayHopf_torus3_statement` (in `Statement.lean`) is intentionally a marked `sorry`
  (the original scaffold target). It is superseded by the genuinely proved
  `exists_lerayHopf_torus3` (in `AxiomaticClosure.lean`), which carries the proof-carrying
  `LerayHopfSolutionFull` (weak form, energy inequality, initial trace, energy class) modulo
  the 4 axioms. The scaffold `sorry` is kept (no-rename rule) and is not frontier debt.
- **Next:** pivot to R³ — instantiate the abstract `DissipativeEvolution`/`WeakFormNS` + the
  abstract A1–A3 pattern; R³ needs its OWN spatial-compactness axiom (Rellich FAILS on ℝ³ —
  no compact Sobolev embedding; needs tightness/concentration-compactness).
