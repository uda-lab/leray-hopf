# HANDOFF — Leray–Hopf weak existence (Lean 4 + mathlib)

Self-contained handoff for picking up this project (fresh session or new contributor).
Last updated: 2026-07-04. Default branch: `main`; work lands via per-issue lane branches + Codex-reviewed PRs.
Canonical current axiom frontier: `scripts/check-axioms-live.sh` (ℝ³ = **1** project axiom,
𝕋³ = **1** project axiom). Where any statement below conflicts with the live pin, the pin wins.

---

## 1. Status snapshot

Two headline theorems are **proved and verified** (each `#print axioms`-clean: only the listed
project axioms + `propext`/`Classical.choice`/`Quot.sound`, **no `sorryAx`**):

```lean
-- LerayHopf/TorusGalerkinODECapstone.lean  (T³, the 3-torus)
theorem exists_lerayHopf_torus3_axiomatic (u₀ : L2Sigma) (ν : ℝ) (hν : 0 < ν)
    (T : ℝ) (hT : 0 < T) :
    ∃ F : Torus3NSForms, Nonempty (LerayHopfSolutionFull F ν T u₀)
-- LerayHopf/R3/GalerkinODECapstone.lean    (ℝ³, whole space — the real target, Leray 1934)
theorem exists_lerayHopf_r3_axiomatic (u₀ : L2Sigma_R3) (ν : ℝ) (hν : 0 < ν)
    (T : ℝ) (hT : 0 < T) :
    ∃ (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊),
    Nonempty (LerayHopfSolutionFull_R3 𝔊 F ν T u₀)
```

`LerayHopfSolution(_R3)Full` is **proof-carrying**: its fields are actual proofs of the weak NS
equation (`WeakFormNS`, over canonical Schwartz/smooth div-free tests), the energy inequality on
`[0,T]`, the initial trace, and the energy class `u ∈ L²(0,T;H¹_σ)`.

- Current frontier (2026-07-04): ℝ³ closed modulo **1 axiom**
  (`galerkin_limit_passage_R3`); T³ closed modulo **1 axiom**
  (`aubin_lions`) — each + 3 kernel (`propext`/`Classical.choice`/`Quot.sound`).
- The entire **spatial+regularity layer** on both domains is built **axiom-free**.
- Each axiom set passed a **Codex `--effort xhigh` adversarial soundness audit** (T³: 8 rounds;
  ℝ³: 2 rounds + a final faithfulness fix) → **approve**.
- **Both convection gap axioms are gone — proved theorem content:**
  `r3ConvectionGapOp_exists` PROVED as `r3ConvectionGapOp_holds` (determined-form BLT
  construction, issue #56 / PR #60; built on the R3-d `TrilinearEstimate.lean` lemmas), and
  `torusConvectionGap_exists` PROVED as `torusConvectionGap_holds` (issue #53 / PR #62).
- **T³ `galerkin_limit_passage` REMOVED** (issue #25 / PR #75) — proved via
  `torus_galerkin_limit_passage_of_energyClass` + `torus_energyClass_of_aubinLions`.
  T³ is **not unconditional**: `aubin_lions` remains live.
- **ℝ³ `galerkin_spacetime_precompact_R3` DISCHARGED** (axiom → theorem, issue #46 PR-4,
  2026-07-04) — the LOCAL Aubin–Lions–Simon spacetime precompactness is now assembled
  sorry-free via File E `LerayHopf/R3/SpacetimePrecompact.lean`
  (`galerkin_spacetime_precompact_of_goodSampling`); ℝ³ frontier 2 → 1.

## 2. How to verify (commands)

```bash
export PATH="$HOME/.elan/bin:$PATH"     # lake is here, not on PATH
bash scripts/agent-preflight.sh          # lake build + 3 guardrail scripts (no-sorry / no-axiom / names)
# canonical axiom check (preferred):
bash scripts/check-axioms-live.sh
# or manually:
echo 'import LerayHopf.R3.GalerkinODECapstone
open LerayHopf
#print axioms exists_lerayHopf_r3_axiomatic' > /tmp/chk.lean && lake env lean /tmp/chk.lean
```
Toolchain: `leanprover/lean4:v4.31.0-rc2` (see `lean-toolchain`). The two capstones are
`sorryAx`-free (asserted by the live pin). Marked `ALLOW_SORRY` frontier/scaffold debt exists in
non-capstone files (e.g. `Statement.lean:exists_lerayHopf_torus3_statement`, the deliberate
scaffold target kept by the no-rename rule, and the `Bochner/`/campaign scaffolds); see
`docs/STATUS.md` for the ledger — none of it leaks into the capstones.

## 3. Repository map

| File | Purpose | Axioms |
|---|---|---|
| `LerayHopf/EvolutionTriple.lean` | **Abstract** `DissipativeEvolution`, `WeakFormNS`, `convForm_self_zero` | 0 |
| `LerayHopf/EnergyEstimate.lean` | **Abstract** `AbstractEnergyLaw` + energy identity/inequality/non-increasing | 0 |
| `LerayHopf/{TorusDomain,FunctionSpaces,SobolevTorus}.lean` | T³ L² spaces, Fourier basis, H¹ predicate | 0 |
| `LerayHopf/{DivergenceFree,Leray}.lean` | T³ `L2Sigma := ⨅ k, ker(divSymbol k)`, Leray projection | 0 |
| `LerayHopf/{GalerkinProjection,VelocityGalerkin}.lean` | Fourier truncation `Pₙ`, velocity Galerkin proj (+ real-valuedness) | 0 |
| `LerayHopf/RellichEmbedding.lean` | **Fourier-tail Rellich** `rellich_seq_compact` (the axiom-free crux) | 0 |
| `LerayHopf/H1Sigma.lean` | `h1EnergySq`, `viscousFormSq`, `rellich_L2Sigma` (componentwise+diagonal) | 0 |
| `LerayHopf/AxiomaticClosure.lean` | T³ axioms + `build_galerkin_package_of_galSeq`; capstone assembly in `TorusGalerkinODECapstone.lean` | — |
| `LerayHopf/R3/Domain.lean` | ℝ³ L² spaces, component projections | 0 |
| `LerayHopf/R3/DivergenceFree.lean` | ℝ³ `L2Sigma_R3 := ⨅ φ, ker(divTestFunctional φ)` (weak div × Schwartz), Leray proj | 0 |
| `LerayHopf/R3/Regularity.lean` | `memH1VF_R3` (MemSobolev), Fourier-integral viscous forms, Schwartz test class | 0 |
| `LerayHopf/R3/AxiomaticClosure.lean` | ℝ³ axioms + package builder; capstone assembly in `R3/GalerkinODECapstone.lean` (**1 live project axiom**) | 1 |
| `LerayHopf/TorusGalerkinODECapstone.lean` | T³ capstone `exists_lerayHopf_torus3_axiomatic` (**1 live project axiom**) | 1 |
| `LerayHopf/R3/GalerkinODECapstone.lean` | ℝ³ capstone `exists_lerayHopf_r3_axiomatic` (**1 live project axiom**) | 1 |
| `docs/STATUS.md` | axiom ledger + Codex audit log (per round) | — |
| `docs/REPORT.md` | narrative final report (T³ + ℝ³) | — |
| `docs/formalization-review-ja.md` | **Japanese** deep review: key lemmas w/ NL-proof translations, non-trivial tactics, NL↔Lean gaps | — |
| `docs/scratch/m6-*.md`, `r3c-*.md` | design contracts (orchestrator deltas, per Codex round) | — |

## 4. The axioms (what is admitted, and why)

All carry `-- ALLOW_AXIOM: <reason + Temam/Leray/Lemarié-Rieusset ref>` and a `## Assumptions` entry.
`b(u,u,u)=0` is a **proved lemma** (not an axiom); convection forms are **non-vacuity-pinned** to a
concrete convection integral so `b=0` (secretly-Stokes) is excluded.

| Role | T³ | ℝ³ | Underlying gap |
|---|---|---|---|
| Spacetime precompactness / Aubin–Lions (time half; spatial half **proved** on both) | `aubin_lions` | **DISCHARGED** (#46 PR-4, 2026-07-04 — theorem via File E `SpacetimePrecompact.lean`) | Bochner–Sobolev in time + Aubin–Lions lemma (T³ side only) |
| Limit passage (existential good representative, a.e.-linked) | **REMOVED** (#25 / PR #75 — proved) | `galerkin_limit_passage_R3` | nonlinear passage + weak-in-time continuity |
| Convection form `b` exists (pinned to concrete `∫(u·∇)v·w`) | **PROVED** `torusConvectionGap_holds` (#53 / PR #62) | **PROVED** `r3ConvectionGapOp_holds` (#56 / PR #60) | determined-form BLT constructions closed the gap |

Removed axioms (now proved theorem content — do NOT list as live):
`galerkin_ode_solution` / `galerkin_ode_solution_R3` (issues #24 / #10), `spatial_compactness_R3` (#2),
`r3GalerkinScheme_exists` (#21), `aubin_lions_R3` (#15/#44), `galerkin_weakLimit_R3` (#47),
`curlSchwartzDense_holds` (#3), `torus3_NSForms_exist` → swapped for `torusConvectionGap_exists` (#22),
`torusConvectionGap_exists` (#53 / PR #62), `r3ConvectionGapOp_exists` (#56 / PR #60),
T³ `galerkin_limit_passage` (#25 / PR #75), `galerkin_spacetime_precompact_R3`
(#46 PR-4, 2026-07-04).

## 5. De-axiomatizing: the cost, and why heavy

Each axiom is a thin interface over a **missing mathlib infrastructure pillar**:

- **P1** weak derivatives + `(u·∇)v` operator + IBP/divergence on `Lp` + 3D trilinear estimate —
  **DISCHARGED at the capstone level** (determined-form BLT constructions, #53/#56); no convection
  axiom is live.
- **P2** Bochner–Sobolev `W^{1,2}(0,T;X)` + weak time-derivative + **Aubin–Lions lemma** — the ℝ³
  half (`galerkin_spacetime_precompact_R3`) **DISCHARGED** (#46 PR-4, step-curve route, File E);
  remaining: the T³ `aubin_lions` content, attacked via the mode-wise spectral route (issue #23).
- **P3** **Rellich–Kondrachov** on bounded domains — **PROVED** (ℝ³ FK chain, issue #2; T³ Fourier tails).
- **P4** nonlinear limit passage (the actual Leray argument) — T³ **PROVED** (#25 / PR #75);
  ℝ³ (`galerkin_limit_passage_R3`) still live, gated on P2.
- **P5** ℝ³ Galerkin scheme (Hermite basis / freq projector) — **PROVED** (issue #21, curl-density route).

Full de-axiomatization ≈ **a multi-person-year mathlib sub-chapter**. This is *why* the project
axiomatizes the frontier cleanly (true, minimal, referenced building blocks) and captures the
**logical architecture** soundly instead of grinding it out.

## 6. Current work queues and strategic options

**Active next actions (2026-07-04):**

- **T³ (`aubin_lions`, issue #23):** continue the mode-wise spectral campaign after PR #80
  (T-AL-3 mode-wise Galerkin extraction). Landed, all sorry-free and axiom-neutral: PR #76
  (replan), #77 (Phase-0 statement gate), #78 (T-AL-1 torus test family + Stokes pairing
  bound), #79 (T-AL-2 scalar equicontinuity engine), #80. Target: the final rewiring PR that
  removes `aubin_lions` → unconditional T³. Not done yet.
- **ℝ³ (1 axiom):** the issue #46 `galerkin_spacetime_precompact_R3` campaign is
  **COMPLETE** (PR #74 step-curve Lp compactness + Galerkin curve library, PR #81 File C
  trilinear bound chain, PR #86 File D time-sampling modulus, PR-4 File E discharge on
  2026-07-04: axiom → theorem). Remaining: the #69 `galerkin_limit_passage_R3` work
  (open, pin-neutral) — the last ℝ³ axiom.

**Strategic options:**

- **Axiomatize-and-stop** (earlier posture): correct for *this* theorem's architecture. Cost-effective.
- **Grind the frontier** (current posture): the removals to date (ℝ³ 6 → 1, T³ 4 → 1) came from
  exactly this — pick one axiom, build its missing sub-library, rewire the capstone.
- **Build a reusable analysis library** (pays off at ≳3–5 downstream PDE/numerical results). Recommended
  **spine, in order**: (1) weak derivatives + `Wᵏ′ᵖ` + grad/div/trace; (2) Lax–Milgram + abstract
  Galerkin/Ritz (cheap, high-leverage, gives FEM scaffold); (3) Rellich–Kondrachov + Aubin–Lions;
  (4) Brouwer → Schauder. Defer degree theory / semigroups / unbounded spectral theory.
- **Highest-leverage single deliverable:** an **"abstract weak solutions of evolution equations"**
  library (Gelfand triple + Bochner–Sobolev-in-time + Aubin–Lions + abstract Galerkin). It would
  discharge the *abstract* A1/A2/A3 on **both** domains at once (the framework was built to receive it)
  and serve a large class of parabolic PDEs / Galerkin–FEM. Est. ~6–10 AI-amplified person-months.
  Use the **generate (Fable) + adversarially-verify (Codex `--effort xhigh`)** loop with the soundness
  gate as a hard blocker — that loop is what made this project sound (it caught 8 unsoundness classes).

## 7. Working conventions (read `AGENTS.md` / `CLAUDE.md` / `docs/agent-roles.md`)

- **Delegation is strict**: `lean-coder` (sonnet) writes defs/signatures/structures/imports/**axioms**;
  the prover (model chosen per dispatch — Fable when available, else Opus) writes proof bodies only;
  reviewers are read-only. The **orchestrator never edits `.lean` directly** — it sequences agents,
  runs Codex, and edits `docs/` only.
- **Codex is orchestrator-owned**: workers request a review in their report; the orchestrator acquires
  Codex review via the Hermes broker: `python3 "$REVIEW_ACQUIRE_SCRIPT" uda-lab/lean-pde <PR#> codex`
  (do NOT copy/override `REVIEW_ACQUIRE_SCRIPT`), and routes the verdict back. **The axiom audit
  is a BLOCKING gate** before any proving; iterate to *approve*.
- **Guardrails (CI)**: every `axiom` needs same-line `-- ALLOW_AXIOM:`; every `sorry` same-line
  `-- ALLOW_SORRY:`; declaration names must avoid the reserved overclaim terms. `scripts/agent-preflight.sh`
  before and after every Lean change; never report success on a red build.
- **1 logical unit = 1 commit**, gated by preflight green + Codex.

## 8. Key soundness lessons (the NL↔Lean gaps — see `docs/formalization-review-ja.md` §4)

These are the traps the Codex audit caught; apply them **preemptively** in any extension:
1. **`tsum` collapse**: `∑' = 0` (not `+∞`) off the summable set ⇒ energy inequalities can be vacuous;
   must proof-carry the **energy class** (a.e. `memH1` + integrable dissipation).
2. **Measure-zero representatives**: pointwise claims for an arbitrary strong-L² representative are false;
   make limit passage **existential** + a.e.-link to the limit (the "good representative").
3. **`(2π)²`** gradient normalization (`e^{2πi k·x}` convention).
4. **Stokes form is `+∞` off H¹** ⇒ cannot be a total real bilinear form; **de-axiomatize** it (concrete
   Fourier multiplier) + separate energy class.
5. **Global vs local compactness on ℝ³**: global Rellich fails; use **local-on-balls** (true, no tightness).
6. **Test class**: weak form must test against **canonical** smooth/Schwartz div-free fields, not a
   scheme-dependent Galerkin class (else overclaim).
7. **Non-vacuity**: abstract antisymmetric `b` is satisfiable by `0` (secretly Stokes) ⇒ **pin** to a
   concrete convection integral on a dense set.
8. **Multilinearity**: forms must be multilinear or a `∀F` ODE axiom becomes inconsistent at `w=0`.

## 9. Standing user constraints (project memory)

- Reply in **English** even when the user writes Japanese (documents may be requested in Japanese).
- The assistant **owns goal-setting** — don't ask who sets the goal.
- **Strict edit-ownership**: orchestrator never edits Lean directly (delegate to lean-coder/fable).
- Posture: **minimally axiomatize the analytic frontier** (true/minimal/referenced building blocks),
  build what mathlib supports; don't grind on missing tooling — capture the architecture soundly.
