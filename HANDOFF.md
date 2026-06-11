# HANDOFF — Leray–Hopf weak existence (Lean 4 + mathlib)

Self-contained handoff for picking up this project (fresh session or new contributor).
Last updated: 2026-06-11. Branch: `autorun/leray-hopf-torus3` (not pushed; no PR opened).

---

## 1. Status snapshot

Two headline theorems are **proved and verified** (each `#print axioms`-clean: only the listed
project axioms + `propext`/`Classical.choice`/`Quot.sound`, **no `sorryAx`**):

```lean
-- LerayHopf/AxiomaticClosure.lean         (T³, the 3-torus)
exists_lerayHopf_torus3 (u₀ : L2Sigma)    (ν>0) (T>0) : ∃ F,   Nonempty (LerayHopfSolutionFull    F ν T u₀)
-- LerayHopf/R3/AxiomaticClosure.lean       (ℝ³, whole space — the real target, Leray 1934)
exists_lerayHopf_r3     (u₀ : L2Sigma_R3) (ν>0) (T>0) : ∃ 𝔊 F, Nonempty (LerayHopfSolutionFull_R3 𝔊 F ν T u₀)
```

`LerayHopfSolution(_R3)Full` is **proof-carrying**: its fields are actual proofs of the weak NS
equation (`WeakFormNS`, over canonical Schwartz/smooth div-free tests), the energy inequality on
`[0,T]`, the initial trace, and the energy class `u ∈ L²(0,T;H¹_σ)`.

- T³ closed modulo **4 axioms**; ℝ³ modulo **6 axioms** (the +2 are exactly the two pieces T³ *proved*
  but ℝ³ cannot — the honest cost of the unbounded domain).
- The entire **spatial+regularity layer** on both domains is built **axiom-free**.
- Each axiom set passed a **Codex `--effort xhigh` adversarial soundness audit** (T³: 8 rounds;
  ℝ³: 2 rounds + a final faithfulness fix) → **approve**.

## 2. How to verify (commands)

```bash
export PATH="$HOME/.elan/bin:$PATH"     # lake is here, not on PATH
bash scripts/agent-preflight.sh          # lake build + 3 guardrail scripts (no-sorry / no-axiom / names)
# axiom check:
echo 'import LerayHopf.R3.AxiomaticClosure
open LerayHopf
#print axioms exists_lerayHopf_r3' > /tmp/chk.lean && lake env lean /tmp/chk.lean
```
Toolchain: `leanprover/lean4:v4.31.0-rc2` (see `lean-toolchain`). Only repo `sorry` is the deliberate
scaffold target `Statement.lean:exists_lerayHopf_torus3_statement` (kept by the no-rename rule;
superseded by the proved `exists_lerayHopf_torus3`).

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
| `LerayHopf/AxiomaticClosure.lean` | T³ **4 axioms** + assembly `exists_lerayHopf_torus3` | 4 |
| `LerayHopf/R3/Domain.lean` | ℝ³ L² spaces, component projections | 0 |
| `LerayHopf/R3/DivergenceFree.lean` | ℝ³ `L2Sigma_R3 := ⨅ φ, ker(divTestFunctional φ)` (weak div × Schwartz), Leray proj | 0 |
| `LerayHopf/R3/Regularity.lean` | `memH1VF_R3` (MemSobolev), Fourier-integral viscous forms, Schwartz test class | 0 |
| `LerayHopf/R3/AxiomaticClosure.lean` | ℝ³ **6 axioms** + assembly `exists_lerayHopf_r3` | 6 |
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
| Convection form `b` exists (pinned to concrete `∫(u·∇)v·w`) | `torus3_NSForms_exist` | `r3_NSForms_exist` | no `(u·∇)v` operator / IBP for `Lp` fields |
| Galerkin ODE + uniform estimates | `galerkin_ode_solution` | `galerkin_ode_solution_R3` | concrete RHS gated on convection |
| Aubin–Lions (time half; spatial half **discharged on T³**, hypothesis on ℝ³) | `aubin_lions` | `aubin_lions_R3` | Bochner–Sobolev in time + Aubin–Lions lemma |
| Limit passage (existential good representative, a.e.-linked) | `galerkin_limit_passage` | `galerkin_limit_passage_R3` | nonlinear passage + weak-in-time continuity |
| Galerkin projection family | *(PROVED `velocityProjection_n`)* | `r3GalerkinScheme_exists` | ℝ³ freq-truncation is ∞-dim / Lp indicator multiplier absent |
| Spatial compactness | *(PROVED `rellich_L2Sigma`)* | `spatial_compactness_R3` (LOCAL) | Rellich–Kondrachov on bounded domains absent |

## 5. De-axiomatizing: the cost, and why heavy

Each axiom is a thin interface over a **missing mathlib infrastructure pillar**:

- **P1** weak derivatives + `(u·∇)v` operator + IBP/divergence on `Lp` + 3D trilinear estimate — *very heavy* (the convection axioms; deepest "new calculus").
- **P2** Bochner–Sobolev `W^{1,2}(0,T;X)` + weak time-derivative + **Aubin–Lions lemma** — *heavy* (A2, A3's good representative).
- **P3** **Rellich–Kondrachov** on bounded domains — *heavy* (ℝ³ spatial compactness; T³ already done via Fourier tails).
- **P4** nonlinear limit passage (the actual Leray argument) — *heavy*, gated on P1+P2.
- **P5** ℝ³ Galerkin scheme (Hermite basis / freq projector) — *medium*, most self-contained.

Full de-axiomatization ≈ **a multi-person-year mathlib sub-chapter**. This is *why* the project
axiomatizes the frontier cleanly (true, minimal, referenced building blocks) and captures the
**logical architecture** soundly instead of grinding it out.

## 6. Strategic options for going further

- **Axiomatize-and-stop** (current state): correct for *this* theorem's architecture. Cost-effective.
- **Grind one axiom**: best first target is **P5** (ℝ³ Hermite Galerkin scheme — self-contained), or
  the concrete trilinear bound (we already have `convIntegralSchwartz`).
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
  `lean-prover` = **fable** writes proof bodies only; reviewers are read-only. The **orchestrator never
  edits `.lean` directly** — it sequences agents, runs Codex, and edits `docs/` only.
- **Codex is orchestrator-owned**: workers request a review in their report; the orchestrator runs
  `node "$CLAUDE_PLUGIN_ROOT/scripts/codex-companion.mjs" adversarial-review "--wait --scope working-tree --effort xhigh <focus>"`
  (`CLAUDE_PLUGIN_ROOT=~/.claude/plugins/marketplaces/openai-codex/plugins/codex`), reads the verdict from
  the task output (`sed -n '/# Codex Adversarial Review/,$p'`), and routes fixes back. **The axiom audit
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
