# Bochner-time foundation metaplan — driving the FINAL 4 project axioms to ZERO

**Planner doc. PLAN ONLY — no Lean edited.** Scope is fixed by `docs/milestone.md` +
`docs/leray_hopf_lean_mvp_plan.md`; this doc only sequences the removal of the last four
project axioms and decomposes the shared Bochner functional-analysis build they need.

**Predecessor spikes (read these first):** `docs/scratch/bc-feasibility.md` (4-axiom survey),
`docs/scratch/r3b-pr0-verdict.md` (R3-B one-PR NO-GO).

---

## The four target axioms (verified against current code)

| # | axiom | file:line | consumed by |
|---|-------|-----------|-------------|
| R3-B | `galerkin_spacetime_precompact_R3` | `LerayHopf/R3/ArzelaAscoliTime.lean:123` | `perBall_ae_subseq` → `diag_ae_subseq` → `u_lim_aestronglyMeasurable` → `aubinLionsPackage_R3_of_timeCompactness` (`R3/AubinLionsLimitPassage.lean`) → `build_galerkin_package_R3_of_galSeq` |
| T-B  | `aubin_lions` | `LerayHopf/AxiomaticClosure.lean:367` | `build_galerkin_package_of_galSeq` (`AxiomaticClosure.lean:533`, `spatial := rellich_L2Sigma`) → capstone |
| R3-C | `galerkin_limit_passage_R3` | `LerayHopf/R3/AxiomaticClosure.lean:558` | `AubinLionsAssembly.lean:84` (`build_galerkin_package_R3_of_galSeq`) → capstone |
| T-C  | `galerkin_limit_passage` | `LerayHopf/AxiomaticClosure.lean:421` | `build_galerkin_package_of_galSeq` (`AxiomaticClosure.lean:538`) → capstone |

R3 currently carries 3 project axioms (these two B/C + `r3_NSForms_exist`); torus carries 3
(these two B/C + `torusConvectionGap_exists`). The B/C pair is what this plan removes; the
NSForms/ConvectionGap residuals are out of scope (tracked separately, #56/#53).

---

## Ground truth on the existing shared layer (verified by reading the source)

### Sorry-free TODAY in `LerayHopf/Bochner/` (domain-neutral, 0 axioms)

`GelfandTriple.lean`:
- `GelfandTriple` (structure: V,H Hilbert + bundled CLM `ι` + injective + dense range),
- `GelfandTriple.IsOfDissipativeEvolution` (faithfulness `Prop`),
- `GelfandTriple.ofDissipativeEvolution` (**sorry-free**) — carves `(V,H,ι)` from a
  `DissipativeEvolution E` given an explicit Hilbert `V` + CLM `ι : V →L[ℝ] E.H` + density +
  `‖v‖² = E.reg (ι v)`; returns `Σ' GT, GT.IsOfDissipativeEvolution E (range ι)`.

`TimeSobolev.lean`:
- `IsWeakTimeDeriv` (def), `isWeakTimeDeriv_unique` (**sorry-free**, `[CompleteSpace X]`,
  du-Bois-Reymond), `hasDerivAt_isWeakTimeDeriv` (**sorry-free**, strong⇒weak via Bochner IBP),
- `GelfandTriple.{ιCLM,Vprime,hToVprime,hToVprimeCLM,hToVprimeCLM_apply}` (**sorry-free**; the
  embedding `H ↪ V'` as a genuine CLM),
- `W1pTime` (structure: `u' ∈ L^q(0,T;V')`, `mem_p`, `mem_q`, `weakDeriv`),
- `W1pTime.ofHValuedDeriv` (**sorry-free**, under `1 ≤ p`, `1 ≤ q`),
- `isWeakTimeDeriv_comp_clm` (**sorry-free**, transport a weak time-deriv through a CLM),
- `aeStronglyMeasurable_of_spaceTimeL2`, `kineticEnergy_lsc_transfer` (**both sorry-free**,
  after the `hg : AEStronglyMeasurable g μ` statement-gate fix — see
  [[project_d2_measurable_rep_false_as_stated]]).

### The single OPEN kernel in the shared layer

- `w1pTime_continuous_in_H` (`TimeSobolev.lean:470`, **open `sorry`**, line 480,
  `ALLOW_SORRY` tagged MONTHS-CLASS). Exact statement:

  > `(GT : GelfandTriple) {p q} {T} (hT : 0 < T) (hpq : 1 ≤ p ∧ 1 ≤ q) {uV : ℝ → GT.V}`
  > `(W : W1pTime GT p q T uV) : ∃ ũ : ℝ → GT.H, ContinuousOn ũ (Icc 0 T) ∧`
  > `ũ =ᵐ[volume.restrict (Icc 0 T)] (fun t => GT.ι (uV t))`

  This is Lions–Magenes `W^{1,p}(0,T;V) ∩ L^q(0,T;V') ↪ C([0,T];H)` (the good-representative
  embedding). **No current consumer.** It is built but not yet referenced by anything outside
  its own file.

### CRITICAL CORRECTION to the bc-feasibility framing

The bc-feasibility report says R3-C/T-C "literally defer to the same kernel
`w1pTime_continuous_in_H`." **This is NOT the current code state — it is the intended
architecture.** Verified facts:
- Neither `LerayHopf/R3/AxiomaticClosure.lean` nor `LerayHopf/AxiomaticClosure.lean` imports
  `LerayHopf.Bochner.*` or references `GelfandTriple` / `W1pTime` / `w1pTime_continuous_in_H`
  (grep: zero hits beyond doc-comments).
- The two C axioms are **free-standing axioms** asserting the full good-representative existence
  (a.e.-equality + `WeakFormNS` + energy ineq + initial trace + energy class) directly, with no
  routing through the Bochner layer.
- The Bochner layer is imported only at the top aggregator `LerayHopf.lean:86-87`.

**Consequence for planning:** the C-axiom removal is NOT "discharge one `sorry` and the axioms
fall." It is **build `w1pTime_continuous_in_H` AND build the wiring tower** that turns a
good-representative-in-`H` plus the strong-L² Aubin–Lions limit into the full five-conjunct
conclusion of each C axiom (nonlinear passage via `b_bound`, energy lsc, initial trace, energy
class). That wiring is itself substantial and currently absent. The "one proof harvested twice"
story holds for the *Lions–Magenes embedding kernel*; the per-domain *limit-passage assembly* on
top of it is new work per domain (though largely domain-generic — see §3).

---

## The from-scratch theorem inventory (what mathlib does NOT provide)

Verified absent (grep + bc-feasibility, re-confirmed): Bochner-valued Aubin–Lions /
Fréchet–Kolmogorov `L^p`-precompactness; equicontinuity-in-time → totally-bounded bridge in
`L²(0,T;X)`; Lions–Magenes `W^{1,p}(0,T;V,V') ↪ C([0,T];H)`; weak-time-derivative `W^{1,p}(0,T;X)`
space beyond what `TimeSobolev.lean` already builds; Eberlein–Šmulian / reflexive
weak-sequential-compactness; real-interpolation `[H,V']`. Present and reusable: `MeasureTheory.Lp`
completeness + `eLpNorm` API; `tendstoInMeasure_of_tendsto_eLpNorm` +
`TendstoInMeasure.exists_seq_tendsto_ae` (already the spine of `ArzelaAscoliTime.lean`); weak
topology + Riesz dual (already used for Mazur in `weakLimit_mem_L2Sigma_R3`); Bochner interval IBP
+ FTC + dominated convergence; abstract `Ascoli` (equicontinuous→compact, no L²-modulus feed).

The genuinely-new theorems, in rough increasing size:
1. **Strong-L² time modulus for Galerkin curves** (R3-B/T-B STEP 1). Was attempted as the
   UNSOUND `galerkin_equicontinuity_from_ODE` (deleted, `ArzelaAscoliTime.lean:13-18`); the honest
   route is the integrated `W^{1,p}(0,T;V')`-Bochner–Sobolev bound, which needs the foundation.
2. **Lions–Magenes good representative** `w1pTime_continuous_in_H` (R3-C/T-C). Biggest single
   from-scratch theorem; needs the `[H,V']` interpolation / Aubin–Lions–Simon-in-time backbone.
3. **Bochner Aubin–Lions–Simon compactness** (R3-B/T-B STEP 3): equicontinuity-in-time +
   spatial-precompactness ⟹ relatively-compact in `L²(0,T;X)`. The actual compactness engine.

Items 2 and 3 share a common substrate (vector-valued time-Sobolev + interpolation), which is why
the foundation is built once. The **biggest single from-scratch theorem is the Lions–Magenes
representative (item 2)**; the Bochner Aubin–Lions–Simon engine (item 3) is the second.

---

## DECOMPOSED MULTI-PR PLAN

Notation: **[F]** = foundation (domain-neutral, `LerayHopf/Bochner/`); **[R3]**/**[T]** =
domain-specific wiring. Every new *statement* gets a `/codex:adversarial-review --effort xhigh`
(orchestrator-run) BEFORE proof bodies — soundness traps in these statements have bitten the
project repeatedly (over-strength global-vs-local, all-t-vs-forward, false-without-`hg`). Each PR
is small per the Small-PR rule; "PR" below is a *milestone* that may itself split.

### PHASE 0 — De-risking spikes (scaffold-only scratch, not for merge)

Run these BEFORE committing to the foundation build. Each is a single make-or-break sub-lemma in
`LerayHopf/Scratch/`, `-- SCRATCH` top, one `ALLOW_SORRY: scratch` permitted on the target line.

- **SPIKE-1 (NEXT — the hardest kernel, de-risk first): Lions–Magenes interpolation core.**
  Validate the make-or-break sub-lemma of `w1pTime_continuous_in_H`: that for `u ∈ L²(0,T;V)`
  with `u' ∈ L²(0,T;V')`, the map `t ↦ ½‖ũ(t)‖²_H` is absolutely continuous with
  `d/dt ½‖ũ‖²_H = ⟨u'(t), u(t)⟩_{V',V}` (the Lions–Magenes energy identity) — this is the crux
  that yields the continuous-in-`H` representative. If the AC + duality-pairing identity closes
  from the existing `IsWeakTimeDeriv` API + mathlib FTC/IBP, the embedding is a real but bounded
  build; if it needs the full `[H,V']` real-interpolation theory from scratch, that is the wall to
  size before scaffolding. **This is the single recommended next spike.** (Rationale: it is the
  biggest from-scratch theorem and underpins BOTH C axioms and B's STEP-1 modulus; de-risk the
  costliest item first, exactly the r3b-verdict discipline.)
- **SPIKE-2: Bochner totally-bounded extraction.** Reprise the r3b STEP-3 `sorry`
  (`R3BSpike.lean` already exists): GIVEN a uniform strong-L² time modulus + local Rellich at a
  δ-mesh, is `n ↦ restrictToBall k ∘ (galSeq (ψ n)).u` totally bounded in `L²(0,T;L²(B_k))` via
  `Ascoli` + `Lp` completeness, OR does it need a direct Fréchet–Kolmogorov-in-time mollification
  proof? Sizes the Aubin–Lions–Simon engine (item 3).

### PHASE 1 — The shared time-Sobolev foundation (build ONCE) — removes the C linchpin

- **PR-F1 [F] — Bochner time-Sobolev energy identity / absolute continuity.** Prove the
  SPIKE-1 core as a real lemma in `LerayHopf/Bochner/TimeSobolev.lean` (or a new
  `Bochner/TimeSobolevAC.lean` to keep files small): `W1pTime` element ⟹ `t ↦ ‖·‖²_H` AC with the
  duality-pairing derivative. **must-prove.** Mathlib provides FTC/IBP/dominated-convergence;
  the `[H,V']` pairing structure is the from-scratch part.
- **PR-F2 [F] — `w1pTime_continuous_in_H` discharge.** Replace the months-class `sorry` at
  `TimeSobolev.lean:480` using PR-F1 (continuous representative from the AC energy identity +
  density of smooth curves). **must-prove. This is the linchpin** — it is the single proof
  harvested by both C axioms. Statement is ALREADY codex-reviewable as written (kept intact);
  re-review on any signature refinement.
- **PR-F3 [F] (only if PR-F1/F2 expose a gap) — interpolation `[H,V']` / `W^{1,p}(0,T;X)`
  helpers.** Any vector-valued time-Sobolev infrastructure PR-F2 needs that is not yet sorry-free
  (e.g. mollification-in-time of `V`-valued curves, density of `C¹` curves in `L^p(0,T;V)`).
  Split out as needed; keep each small. **must-prove.**

### PHASE 2 — Wire the C pair through the foundation — removes R3-C then T-C

The foundation gives a good representative continuous-in-`H` a.e.-equal to the curve. Each C axiom
additionally needs: nonlinear limit passage (`b_bound` on strong L² convergence), energy lsc,
initial trace, energy class. Most of that machinery already exists per domain
(`bForm_tendsto_of_strongL2`, `kineticEnergy_lsc_bound` (E1), `kineticEnergy_lsc_transfer`).

- **PR-R3C1 [R3] — Gelfand triple instance for `r3Evolution`.** Construct
  `GelfandTriple.ofDissipativeEvolution (r3Evolution 𝔊 F) …` by supplying `V := H¹_σ(ℝ³)` (or its
  `MemLp`-carved realization), the inclusion CLM, density, and `‖·‖² = reg`. **must-prove**
  (the `ofDissipativeEvolution` bridge is already sorry-free; this is its instantiation +
  discharging the four data hypotheses from existing R3 H¹/L² API).
- **PR-R3C2 [R3] — limit-passage assembly + axiom removal.** Build
  `galerkin_limit_passage_R3` as a THEOREM: feed the Aubin–Lions package into the PR-R3C1 triple,
  obtain the continuous-in-`H` representative from `w1pTime_continuous_in_H`, then discharge the
  five conjuncts via the existing strong-convergence/lsc/trace lemmas. Delete the axiom. Wire
  `AubinLionsAssembly.lean:84` to the theorem. **must-prove.** Likely splits into a representative
  PR + a conjuncts PR.
- **PR-TC1 [T] — Gelfand triple instance for `torus3Evolution`** (mirror PR-R3C1 with
  `V := H¹_σ(T³)`, `reg := h1EnergySq`). **must-prove.** Smaller (compact domain, `rellich_L2Sigma`
  already proved).
- **PR-TC2 [T] — torus limit-passage assembly + `galerkin_limit_passage` removal.** Mirror
  PR-R3C2. The assembly is domain-generic given the triple; the per-domain pieces are the
  `b_bound`/lsc/trace lemmas (torus side currently leans more on R3's built helpers — see the
  torus `strong_convergence` C2 `sorry` referenced at `AxiomaticClosure.lean:357-365`). **must-prove.**

### PHASE 3 — The B pair (Aubin–Lions–Simon compactness) — removes R3-B then T-B

B is gated on TWO walls (r3b-verdict): STEP-1 strong-L² modulus + STEP-3 Bochner compactness.
STEP-1's honest route reuses the PHASE-1 foundation, so B is sequenced AFTER the foundation lands.

- **PR-B1 [F/R3] — uniform strong-L² time modulus for Galerkin curves.** From the PHASE-1
  `W^{1,p}(0,T;V')` foundation + the energy identity (`reg_bound`), derive the uniform-in-`n`
  modulus `‖(galSeq n).u s − (galSeq n).u t‖_{L²} < ε for |s−t|<δ` that the Steklov toolkit and the
  deleted-as-unsound `galerkin_equicontinuity_from_ODE` both lacked. **must-prove.** This is the
  `TimeCompactnessInput.uniform_time_modulus` that is currently only consumed, never produced.
- **PR-B2 [F] — Bochner Aubin–Lions–Simon compactness engine.** The genuinely-new mathlib-grade
  theorem (SPIKE-2 target): equicontinuity-in-time (PR-B1) + spatial precompactness (local Rellich
  `spatial_compactness_R3`, already proved) ⟹ totally bounded ⟹ convergent subsequence in
  `L²(0,T;L²(B_k))`. **must-prove. Hardest single B piece.**
- **PR-R3B [R3] — `galerkin_spacetime_precompact_R3` removal.** Apply PR-B2 per `(k, ψ)`. The
  refine-capable Cantor-diagonal consumer tower (`perBall_ae_subseq` → `diag_ae_subseq` →
  `u_lim_aestronglyMeasurable`) ALREADY EXISTS, so this is the cheap wiring once PR-B2 lands.
  Delete the axiom. **must-prove (wiring).**
- **PR-TB [T] — `aubin_lions` removal.** Port the Steklov/modulus toolkit to T³ (the torus has NO
  Steklov scaffold today — this is the underestimated cost per bc-feasibility risk) and apply PR-B2
  GLOBALLY (compact domain, no ball exhaustion, spatial input = `rellich_L2Sigma`). Delete the
  axiom. **must-prove.**

---

## §3 Domain mirroring (generic vs domain-specific)

- **Domain-GENERIC (build once, `LerayHopf/Bochner/`):** the entire Gelfand/`W1pTime` layer,
  PR-F1/F2/F3 (Lions–Magenes), PR-B2 (Aubin–Lions–Simon engine). These speak only about an
  abstract `GelfandTriple` / `DissipativeEvolution`, so they serve T³ and ℝ³ without duplication
  (the layer already imports only `EvolutionTriple` + mathlib — no domain import, no cycle).
- **Domain-SPECIFIC wiring:** the `ofDissipativeEvolution` *instantiation* per evolution
  (PR-R3C1, PR-TC1 — supply `V`, `ι`, density, norm-identity from each domain's H¹/L² API); the
  limit-passage conjunct assembly (PR-R3C2, PR-TC2 — `b_bound`/lsc/trace are per-domain lemmas,
  though the assembly skeleton is shared); the B modulus + Steklov port (PR-B1, PR-R3B, PR-TB).
- **Sequencing:** R3 before torus in each pair (R3 is strictly more built — the Steklov toolkit,
  the diagonal consumer tower, the strong-convergence helpers all exist on the R3 side; torus
  reuses them). So: **R3-C before T-C; R3-B before T-B.**

---

## §4 ORDER, next spike, and realistic PR count

**Critical-path order:** SPIKE-1 → PHASE 1 (F1→F2[→F3]) → PHASE 2 (R3C1→R3C2 → TC1→TC2) ‖
SPIKE-2 → PHASE 3 (B1→B2 → R3B → TB). PHASE 2 and the B-track can overlap once the foundation
(PR-F2) lands, since both consume it. The foundation is the serial bottleneck; everything else
fans out from it.

**The single PR-0 spike to run NEXT: SPIKE-1 (the Lions–Magenes energy-identity / AC core).**
It de-risks the biggest from-scratch theorem, which is also the linchpin both C axioms and B's
modulus route through. Per the r3b-verdict discipline (validate the costliest kernel before
scaffolding), this is the make-or-break to settle first. SPIKE-2 (Bochner totally-bounded) is the
second spike, runnable in parallel since it is B-specific.

**Realistic PR count: 12–16 merged PRs** (eyes-open, months-class):
- Foundation: 2–4 (PR-F1, PR-F2, plus 0–2 interpolation/density helpers as PR-F3 splits).
- C pair: 4–6 (two triple-instance PRs + two limit-passage assemblies, each assembly likely
  splitting representative-vs-conjuncts).
- B pair: 4–6 (modulus, compactness engine — likely 2 PRs itself, R3 removal, torus port +
  removal).
- 2 spikes (scratch, not merged) up front.

This is a genuine multi-month Bochner functional-analysis build. The "months-class" label is an
honest scale estimate, NOT a reason to defer (per [[feedback_months_class_excuse_banned]]): the
plan above is the eyes-open multi-PR commitment, with the hardest kernel de-risked first.

---

## Codex review points (every NEW statement, before proofs)

`/codex:adversarial-review --effort xhigh` (orchestrator-run) on the *statement* of: PR-F1 AC
energy identity; PR-F2 `w1pTime_continuous_in_H` (on any signature change from the kept form);
each `GelfandTriple.ofDissipativeEvolution` instantiation's data hypotheses (PR-R3C1/PR-TC1 —
the `‖·‖²=reg`, density, CLM contracts are exactly where over-strength hides); each
de-axiomatized C/B THEOREM signature (must match the deleted axiom's type EXACTLY — no
weakening, the No-overclaim and statement-gate rules); PR-B1 modulus statement (the
deleted-unsound `galerkin_equicontinuity_from_ODE` is the cautionary precedent — confirm it is
the strong-L² integrated form, NOT a dual-norm ODE consequence); PR-B2 Aubin–Lions–Simon
statement (LOCAL vs global, refine-capability).

## Definition of done

ZERO project axioms on both Leray–Hopf B/C fronts:
- `galerkin_spacetime_precompact_R3`, `aubin_lions`, `galerkin_limit_passage_R3`,
  `galerkin_limit_passage` all converted axiom→sorry-free THEOREM (or deleted as dead, as
  `galerkin_weakLimit_R3` was) with their consumers rewired.
- `w1pTime_continuous_in_H` sorry-free (the foundation linchpin).
- `bash scripts/agent-preflight.sh` green; `check-no-axiom`/`check-no-sorry`/`check-theorem-names`
  pass; no new axiom introduced anywhere on the path.
- Out of scope (NOT part of DoD): `r3_NSForms_exist`, `torusConvectionGap_exists` (the NSForms /
  convection-gap residuals, tracked elsewhere).

## Recommended first task to hand to `lean-coder`

**SPIKE-1 scaffold:** create `LerayHopf/Scratch/LionsMagenesSpike.lean` (`-- SCRATCH` top,
one `ALLOW_SORRY: scratch` permitted) stating the Lions–Magenes energy-identity core lemma — for
a `W1pTime GT 2 2 T uV` element, `t ↦ ½‖ũ(t)‖²_H` is absolutely continuous on `[0,T]` with weak
derivative `t ↦ ⟪u'(t), uV(t)⟫_{V',V}` — wired against the existing `IsWeakTimeDeriv` /
`hToVprimeCLM` API, and attempt to close it from mathlib FTC/IBP. Report whether it closes from
existing pieces or hits the `[H,V']` interpolation wall. `lean-coder` writes the signature; the
verdict gates whether PHASE 1 scaffolds as planned or needs an interpolation sub-build first.
