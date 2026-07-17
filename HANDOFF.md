# HANDOFF — Leray–Hopf weak existence (Lean 4 + mathlib)

Self-contained handoff for picking up this project (fresh session or new contributor).
Last updated: 2026-07-09. Default branch: `main`; work lands via per-issue lane branches + Codex-reviewed PRs.
Canonical current axiom frontier: `scripts/check-axioms-live.sh` (ℝ³ = **0** project axioms,
𝕋³ = **0** project axioms). Where any statement below conflicts with the live pin, the pin wins.

---

## 1. Status snapshot

Two headline theorems are **proved and verified** (each `#print axioms`-clean: only `propext`/`Classical.choice`/`Quot.sound`, **no project axioms** and **no `sorryAx`**):

```lean
-- LerayHopf/Torus/GalerkinODECapstone.lean  (T³, the 3-torus)
theorem exists_lerayHopf_torus3 (u₀ : L2Sigma) (ν : ℝ) (hν : 0 < ν)
    (T : ℝ) (hT : 0 < T) :
    ∃ F : Torus3NSForms, Nonempty (LerayHopfSolutionFull F ν T u₀)
-- LerayHopf/R3/GalerkinODECapstone.lean    (ℝ³, whole space — the real target, Leray 1934)
theorem exists_lerayHopf_r3 (u₀ : L2Sigma_R3) (ν : ℝ) (hν : 0 < ν)
    (T : ℝ) (hT : 0 < T) :
    ∃ (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊),
    Nonempty (LerayHopfSolutionFull_R3 𝔊 F ν T u₀)
```

`LerayHopfSolution(_R3)Full` is **proof-carrying**: its fields are actual proofs of the weak NS
equation (`WeakFormNS`, over separated-variable tests `ψ(t)w(x)` with `w` canonical
Schwartz/smooth div-free), the energy inequality on `[0,T]`, the one-sided initial trace at
`t → 0⁺`, and the energy class — a.e.-in-time H¹ membership plus interval-integrable viscous
dissipation. See `README.md`'s claims table for the exact field-by-claim mapping; in
particular the energy class is **not** literal Bochner membership `u ∈ L²(0,T;H¹_σ)`, and
there is no `C_w([0,T];L²_σ)` weak-continuity field.

- Current frontier (2026-07-09): ℝ³ closed with **0** project axioms; T³ closed with **0** project axioms — each + 3 kernel (`propext`/`Classical.choice`/`Quot.sound`).
- The entire **spatial+regularity layer** on both domains is built **axiom-free**.
- Each axiom set passed a **Codex `--effort xhigh` adversarial soundness audit** (T³: 8 rounds;
  ℝ³: 2 rounds + a final faithfulness fix) → **approve**.
- **Both convection gap axioms are gone — proved theorem content:**
  `r3ConvectionGapOp_exists` PROVED as `r3ConvectionGapOp_holds` (determined-form BLT
  construction, issue #56 / PR #60; built on the R3-d `TrilinearEstimate.lean` lemmas), and
  `torusConvectionGap_exists` PROVED as `torusConvectionGap_holds` (issue #53 / PR #62).
- **T³ `galerkin_limit_passage` REMOVED** (issue #25 / PR #75) — proved via
  `torus_galerkin_limit_passage_of_energyClass` + `torus_energyClass_of_aubinLions`.
  T³ `aubin_lions` is also discharged (`torusAubinLionsPackage_of_galSeq`), so the torus capstone is unconditional and kernel-only.
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
#print axioms exists_lerayHopf_r3' > /tmp/chk.lean && lake env lean /tmp/chk.lean
```
Toolchain: `leanprover/lean4:v4.31.0-rc2` (see `lean-toolchain`). The two capstones are
`sorryAx`-free (asserted by the live pin). Marked `ALLOW_SORRY` frontier debt exists in
non-capstone `Bochner/` campaign files only; see `docs/STATUS.md` for the ledger — none of
it leaks into the capstones.

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
| `LerayHopf/Torus/SolutionInterfaces.lean` | T³ support layer + `build_galerkin_package_of_galSeq`; capstone assembly in `Torus/GalerkinODECapstone.lean` | 0 |
| `LerayHopf/R3/Domain.lean` | ℝ³ L² spaces, component projections | 0 |
| `LerayHopf/R3/DivergenceFree.lean` | ℝ³ `L2Sigma_R3 := ⨅ φ, ker(divTestFunctional φ)` (weak div × Schwartz), Leray proj | 0 |
| `LerayHopf/R3/Regularity.lean` | `memH1VF_R3` (MemSobolev), Fourier-integral viscous forms, Schwartz test class | 0 |
| `LerayHopf/R3/SolutionInterfaces.lean` | ℝ³ support layer + package builder; capstone assembly in `R3/GalerkinODECapstone.lean` | 0 |
| `LerayHopf/Torus/GalerkinODECapstone.lean` | T³ capstone `exists_lerayHopf_torus3` | 0 |
| `LerayHopf/R3/GalerkinODECapstone.lean` | ℝ³ capstone `exists_lerayHopf_r3` | 0 |
| `docs/STATUS.md` | axiom ledger + Codex audit log (per round) | — |
| `docs/archive/REPORT.md` | narrative final report (T³ + ℝ³), archived/historical | — |
| `docs/formalization-review-ja.md` | **Japanese** deep review: key lemmas w/ NL-proof translations, non-trivial tactics, NL↔Lean gaps | — |
| `docs/scratch/m6-*.md`, `r3c-*.md` | design contracts (orchestrator deltas, per Codex round) | — |

## 4. Former axioms — all removed (historical ledger)

Both capstones are kernel-only: no project axiom is currently admitted. Each row below was
once an `axiom` carrying `-- ALLOW_AXIOM: <reason + Temam/Leray/Lemarié-Rieusset ref>` and a
`## Assumptions` entry before being discharged as a theorem.
`b(u,u,u)=0` is a **proved lemma** (not an axiom); convection forms are **formula-pinned** to a
concrete convection integral.  Non-triviality (`b ≠ 0`, i.e. that the pin excludes the
secretly-Stokes `b=0` case) is *not* separately formalized: no concrete witness theorem is
proved in this repository — a statement about the scope of the formal guarantee, not about
mathematical soundness (issue #153).

| Role | T³ | ℝ³ | Underlying gap |
|---|---|---|---|
| Spacetime precompactness / Aubin–Lions (time half; spatial half **proved** on both) | **DISCHARGED** (`torusAubinLionsPackage_of_galSeq`) | **DISCHARGED** (#46 PR-4, 2026-07-04 — theorem via File E `SpacetimePrecompact.lean`) | Bochner–Sobolev in time + Aubin–Lions lemma |
| Limit passage (existential good representative, a.e.-linked) | **REMOVED** (#25 / PR #75 — proved) | **REMOVED** (#4 PR-6 — proved) | nonlinear passage + weak-in-time continuity |
| Convection form `b` exists (pinned to concrete `∫(u·∇)v·w`) | **PROVED** `torusConvectionGap_holds` (#53 / PR #62) | **PROVED** `r3ConvectionGapOp_holds` (#56 / PR #60) | determined-form BLT constructions closed the gap |

Removed axioms (now proved theorem content — do NOT list as live):
`galerkin_ode_solution` / `galerkin_ode_solution_R3` (issues #24 / #10), `spatial_compactness_R3` (#2),
`r3GalerkinScheme_exists` (#21), `aubin_lions_R3` (#15/#44), `galerkin_weakLimit_R3` (#47),
`curlSchwartzDense_holds` (#3), `torus3_NSForms_exist` → swapped for `torusConvectionGap_exists` (#22),
`torusConvectionGap_exists` (#53 / PR #62), `r3ConvectionGapOp_exists` (#56 / PR #60),
T³ `galerkin_limit_passage` (#25 / PR #75), `galerkin_spacetime_precompact_R3`
(#46 PR-4, 2026-07-04).

## 5. De-axiomatizing: what each former axiom cost (historical)

Each former axiom was a thin interface over a **missing mathlib infrastructure pillar**; all
five are now discharged and both capstones are kernel-only:

- **P1** weak derivatives + `(u·∇)v` operator + IBP/divergence on `Lp` + 3D trilinear estimate —
  **DISCHARGED at the capstone level** (determined-form BLT constructions, #53/#56).
- **P2** Bochner–Sobolev `W^{1,2}(0,T;X)` + weak time-derivative + **Aubin–Lions lemma** — the ℝ³
  half (`galerkin_spacetime_precompact_R3`) **DISCHARGED** (#46 PR-4, step-curve route, File E);
  the T³ half: discharged by the mode-wise spectral route (issue #23).
- **P3** **Rellich–Kondrachov** on bounded domains — **PROVED** (ℝ³ FK chain, issue #2; T³ Fourier tails).
- **P4** nonlinear limit passage (the actual Leray argument) — T³ **PROVED** (#25 / PR #75);
  ℝ³ **PROVED** (`galerkin_limit_passage_R3`, issue #4 PR-6).
- **P5** ℝ³ Galerkin scheme (Hermite basis / freq projector) — **PROVED** (issue #21, curl-density route).

Full de-axiomatization turned out to be **a multi-person-year mathlib sub-chapter**, done
incrementally rather than axiomatized-and-left: each frontier item above was closed with a
true, minimal, referenced building block, one at a time, rather than accepted as a permanent
axiom.

## 6. Strategic options for future work

Both capstones are already kernel-only (§4): the T³ Aubin–Lions axiom is DISCHARGED (the
mode-wise spectral route lands as `torusAubinLionsPackage_of_galSeq`, issue #23) and the ℝ³
`galerkin_limit_passage_R3` axiom is DISCHARGED (issue #4 PR-6) — new work should not
reintroduce a live project axiom on either domain. The options below are about *optional*
further work beyond the closed existence theorems.

**Strategic options:**

- **Axiomatize-and-stop** (earlier posture): correct for *this* theorem's architecture. Cost-effective.
- **Grind the frontier** (current posture): the removals to date (ℝ³ 6 → 0, T³ 4 → 0) came from
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
  Codex review via the Hermes broker: `python3 "$REVIEW_ACQUIRE_SCRIPT" uda-lab/leray-hopf <PR#> codex`
  (do NOT copy/override `REVIEW_ACQUIRE_SCRIPT`; if the broker's allowlist has not yet caught up
  with the `uda-lab/lean-pde` → `uda-lab/leray-hopf` rename, pass `uda-lab/lean-pde` instead —
  GitHub's rename redirect resolves both to the same repository), and routes the verdict back.
  **The axiom audit is a BLOCKING gate** before any proving; iterate to *approve*.
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
