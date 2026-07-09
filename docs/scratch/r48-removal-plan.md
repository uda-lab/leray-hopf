# Task Contract: Issue #48 — Remove the fat axiom `r3_NSForms_exist` (thin-swap, mirroring torus #22)

> **⚠️ SUPERSEDED BY IMPLEMENTATION (2026-06-26, PR #55).** The body below was the
> initial scoping. The actual landed design DIVERGED after codex review — do NOT follow
> the body verbatim. Authoritative final design:
> - The residual axiom is **`r3ConvectionGapOp_exists : ∀ 𝔊, Nonempty (ConvectionGapOp 𝔊)`**
>   (NOT `r3ConvectionGap_exists : Nonempty (ConvectionGap 𝔊)`). `ConvectionGapOp` is the
>   thinner structure carrying only the five operator fields; **`schwartz_dense` is deliberately
>   kept OUT of the axiom** and supplied in `r3_NSForms_exists` from the proved
>   `convectionGap_schwartz_dense curlSchwartzDense_holds` (codex P2: never re-assume the
>   proved density).
> - This is a **reorganization** of AX-4, **not** a strict thinning: `b_cont_fixedTest` is
>   analytically EQUIVALENT to `R3NSForms.b_bound`, so the bound remains assumed (codex P1).
>   What genuinely becomes theorem content is the multilinear algebra + the density. Net R3
>   project-axiom count stays **3**. Genuine full removal (3→2) is the months-class
>   `(u·∇)v` Sobolev-operator build (tracked as the #48-residual / torus #53 follow-up).

**Plan author:** lean-planner
**Date:** 2026-06-26
**Scope:** READ-ONLY planning (this file only). Produces the task contract for `lean-coder` / `lean-prover`.

**Source files read (verbatim):**
- `LerayHopf/R3/SolutionInterfaces.lean` (lines 200–330: `R3NSForms` structure, the `r3_NSForms_exist` axiom at :300, `r3Evolution`)
- `LerayHopf/R3/ConvectionForm.lean` (FULL: `ConvectionGap` structure :146, `R3NSForms_of_gap` :230 — **already sorry-free**, plus H1–H4/P1/P2 density chain :337–527 — **already sorry-free**)
- `LerayHopf/R3/ConvectionOperator.lean` (FULL: Tier-S `convFormSchwartz_*` — all 11 lemmas sorry-free)
- `LerayHopf/R3/TrilinearEstimate.lean` (FULL: the 12 R3-d `convIntegralSchwartz_*` lemmas — all sorry-free)
- `LerayHopf/TorusConvectionForm.lean` (lines 460–671: the accepted torus #22 precedent — `TorusConvectionGap` :523, `Torus3NSForms_of_gap` :583, `torusConvectionGap_exists` axiom :664, `torus3_NSForms_exists` theorem :669)
- `LerayHopf/R3/GalerkinODECapstone.lean` (lines 80–101: the capstone `exists_lerayHopf_r3`, which calls `r3_NSForms_exist` at :97)
- `LerayHopf/R3/CurlDensityCapstone.lean` (lines 5–82: `curlSchwartzDense_holds` is a **proved theorem**, sorry-free + axiom-free, NOT an axiom)
- `LerayHopf/R3Capstone.lean` (axiom inventory)
- `docs/scratch/r3-48-nsforms-plan.md` (the earlier #48 partial-discharge plan, now superseded — its density work P1/P2 is already merged into `ConvectionForm.lean`)

---

## 0. Headline correction to the prompt's framing

The prompt asked us to decide between (A) full removal via a total algebraic trilinear `b`, or (B) build a *new* R3 thin-gap analogue of the torus. **Neither is the work that remains.** The investigation shows:

1. **The R3 thin-gap analogue already exists and is already proved sorry-free.** `LerayHopf/R3/ConvectionForm.lean` contains `ConvectionGap 𝔊` (the thin structure, the exact R3 mirror of `TorusConvectionGap`) and `R3NSForms_of_gap : ConvectionGap 𝔊 → Nonempty (R3NSForms 𝔊)` (sorry-free). All the trilinear algebra (`b_add_*`/`b_smul_*` ← `b_multilinear`), `b_antisymm` ← `b_antisymm_gap`, the `b_bound` transfer (← `convFormSchwartz_bound` + `b_cont_fixedTest` + `schwartz_dense`), and the `b_galerkin` non-vacuity pin (← `b_extends` + `convFormSchwartz_eq_witness`) are **already theorem content**, exactly as the torus #22 outcome.

2. **The ONE genuinely-provable gap field is also already proved.** `convectionGap_schwartz_dense` (`ConvectionForm.lean:522`) derives `schwartz_dense` from `CurlSchwartzDense`, and `curlSchwartzDense_holds` is itself a **proved, axiom-free theorem** (`CurlDensityCapstone.lean:62`). So `schwartz_dense` is unconditionally available with no axiom cost.

3. **The only thing that was never done is the final rewire.** Unlike the torus — which has `torusConvectionGap_exists` (axiom) + `torus3_NSForms_exists` (theorem) + a rerouted capstone — the R3 side never introduced `r3ConvectionGap_exists` and never rerouted `exists_lerayHopf_r3`. The capstone still calls the **fat** axiom `r3_NSForms_exist` directly (`GalerkinODECapstone.lean:97`).

**Verdict: route (B) — the thin-swap — and it is a SMALL, bounded, immediately-landable PR**, because every supporting theorem already exists. The PR is purely the torus-#22-style rewire: introduce the thin axiom, prove `r3_NSForms_exists` from it through the existing `R3NSForms_of_gap`, and reroute the capstone to consume the proved theorem instead of the fat axiom. Net effect on the R3 capstone's axiom set: `r3_NSForms_exist` (fat) is **removed** and replaced by the strictly-thinner `r3ConvectionGap_exists`. Axiom *count* stays the same (a 1-for-1 swap), but the **fat structure-existence axiom is eliminated** and all of its trilinear/bound/pin content becomes theorem content. This is exactly the accepted torus #22 result and exactly what issue #48 asks for ("3 project axioms to 2 by removing this axiom — or the honest thinner-gap swap").

### On route (A) (full removal to a genuinely lower axiom count)

Full removal — discharging `ConvectionGap 𝔊` itself with no residual axiom — is **NOT reachable in bounded work**, for the reason the prompt itself names and the codebase documents in detail (`ConvectionForm.lean:42–70`, `ConvectionOperator.lean:18–27`):

- The five non-density `ConvectionGap` fields (`b`, `b_extends`, `b_multilinear`, `b_antisymm_gap`, `b_cont_fixedTest`) collectively encode a **total weak convection operator** `(u·∇)v` on `L²_σ(ℝ³)`. Mathlib has no such operator.
- The candidate algebraic-extension routes the prompt lists do **not** rescue full removal:
  - *Hamel/`LinearMap.extend`/`Basis.constr` extension of `b` from the Schwartz-representable subspace.* The algebra (`b_multilinear`) could in principle be obtained by choosing a Hamel basis and extending linearly — but this does **not** give `b_antisymm_gap` over arbitrary `L²_σ` (antisymmetry in slots 2,3 is the IBP/divergence content, not preserved by an arbitrary linear extension), and it does **not** give `b_cont_fixedTest` (a non-canonical Hamel extension is generically discontinuous even in slots 1,2 at fixed Schwartz `w`). An extension that is *simultaneously* trilinear, slot-2,3 antisymmetric on all triples, and slot-1,2 continuous at every fixed Schwartz test IS the bounded weak convection operator; there is no shortcut that yields all three from algebra alone. Mathlib has no `AlternatingMap`/exterior-algebra tool that produces a *bounded* (continuous-at-fixed-test) antisymmetric extension here.
  - *A direct total formula via the Leray projector or fixed mollification.* Any such formula must still satisfy `b_extends` (agree with `convFormSchwartz` on the dense Schwartz class) AND `b_antisymm_gap` AND `b_cont_fixedTest`; pinning to `convFormSchwartz` on a dense set plus continuity at fixed test forces the value, so a "total formula" that satisfies all fields IS (a construction of) the missing operator. This is months-class (a genuine P-γ analysis build: weak `(u·∇)v` on `Lp` + distributional IBP for `L²` vector fields).

So the honest, bounded, completing deliverable is the route-(B) thin-swap, and the residual `r3ConvectionGap_exists` is the precise, strictly-thinner frontier whose eventual removal is the months-class weak-operator build.

---

## 1. Verdict

| Question | Answer |
|---|---|
| Full removal (A) achievable in bounded work? | **No.** The five operator-extension fields of `ConvectionGap` are the genuine weak-`(u·∇)v` operator on `L²_σ(ℝ³)`, absent from Mathlib; months-class. |
| Thin-swap (B) achievable now? | **Yes — and it is a SMALL PR**, because `ConvectionGap` + `R3NSForms_of_gap` + the density chain are already built and proved sorry-free. The remaining work is only the torus-#22-style rewire. |
| Does the swap eliminate the fat axiom? | **Yes.** `r3_NSForms_exist` (fat structure-existence) is removed from the capstone's axiom set, replaced by the strictly-thinner `r3ConvectionGap_exists`. |
| Net axiom count change for the R3 capstone | **0** (1-for-1 swap). Fat → thin. All trilinear/bound/pin algebra becomes theorem content via the already-proved `R3NSForms_of_gap`. |
| Mirrors accepted torus #22? | **Exactly.** Same shape: thin `*ConvectionGap` structure + `*3NSForms_of_gap` derivation + `*ConvectionGap_exists` thin axiom + rerouted `*3_NSForms_exists` theorem + rerouted capstone. |

**Evidence that decided it:** `ConvectionForm.lean:230` (`R3NSForms_of_gap`, sorry-free) + `ConvectionForm.lean:522` (`convectionGap_schwartz_dense`, sorry-free) + `CurlDensityCapstone.lean:62` (`curlSchwartzDense_holds` proved, axiom-free) + `TorusConvectionForm.lean:664–671` (the torus precedent to copy) + `GalerkinODECapstone.lean:97` (the single fat-axiom call site to reroute).

---

## 2. File / declaration decomposition

Two files are touched. **No edit to `SolutionInterfaces.lean`** (the fat axiom there is left in place but becomes *unused by the capstone*; see §5 soundness flag 1 for the disposition options). The work mirrors `TorusConvectionForm.lean:655–671` and the torus capstone reroute (#24).

### File 1 — `LerayHopf/R3/ConvectionForm.lean` (append a new section at end, before `end LerayHopf`)

Owner split: the `axiom` line and the two theorem *signatures* are **lean-coder**; the proof body of the rerouted existence theorem is **lean-prover** (it is a one-liner; may be co-located).

| # | Name | Kind | Status | Owner | Signature (informal) | Consumes |
|---|---|---|---|---|---|---|
| R1 | `r3ConvectionGap_exists` | `axiom` | **scaffold / residual axiom** (ALLOW_AXIOM) | lean-coder | `∀ (𝔊 : R3GalerkinScheme), Nonempty (ConvectionGap 𝔊)` | — (the isolated weak-operator frontier) |
| R2 | `r3_NSForms_exists` | `theorem` | **must-prove** (sorry-free, one line) | lean-coder sig / lean-prover body | `∀ (𝔊 : R3GalerkinScheme), Nonempty (R3NSForms 𝔊)` | `r3ConvectionGap_exists` (R1) + `R3NSForms_of_gap` (existing :230) |

R1 signature (exact intended form, mirroring `TorusConvectionForm.lean:664`):
```lean
axiom r3ConvectionGap_exists (𝔊 : R3GalerkinScheme) : Nonempty (ConvectionGap 𝔊)
-- ALLOW_AXIOM: isolates the single ℝ³ weak-convection-operator frontier (total b on L²_σ
-- extending convFormSchwartz, its algebraic trilinear/antisymmetry structure over arbitrary
-- L²_σ, and slot-1,2 continuity at fixed Schwartz test — the weak (u·∇)v calculus / distributional
-- IBP that mathlib lacks). STRICTLY THINNER than r3_NSForms_exist: all trilinear b_add_*/b_smul_*
-- algebra, the unrestricted b_bound transfer, and the b_galerkin Schwartz pin are now THEOREM
-- content via R3NSForms_of_gap; the schwartz_dense field is itself provable (curlSchwartzDense_holds).
-- TRUE (genuine (u·∇)v form witnesses); NON-VACUOUS (b_extends + convFormSchwartz_eq_witness pin
-- excludes b=0). Temam II.§1; Lemarié-Rieusset §5.
```

R2 signature + body (exact intended form, mirroring `TorusConvectionForm.lean:669`):
```lean
theorem r3_NSForms_exists (𝔊 : R3GalerkinScheme) : Nonempty (R3NSForms 𝔊) :=
  (r3ConvectionGap_exists 𝔊).elim fun g => R3NSForms_of_gap 𝔊 g
```

### File 2 — `LerayHopf/R3/GalerkinODECapstone.lean` (one-line edit at :97)

Owner: this is a proof-body edit inside `exists_lerayHopf_r3` (a `:= by` block), so **lean-prover** owns it. It is a single-token reroute.

| # | Name | Kind | Status | Owner | Change |
|---|---|---|---|---|---|
| C1 | `exists_lerayHopf_r3` | existing `theorem` (reroute its body) | **must-prove** (stays sorry-free) | lean-prover | replace `r3_NSForms_exist (schemeOfBasis B)` with `r3_NSForms_exists (schemeOfBasis B)` at line 97 |

The surrounding line is `obtain ⟨F⟩ := r3_NSForms_exist (schemeOfBasis B)`; after the edit it reads `obtain ⟨F⟩ := r3_NSForms_exists (schemeOfBasis B)`. Everything downstream (`build_galerkin_package_R3_of_basis B F ν hν T hT u₀`, etc.) is unchanged — `F : R3NSForms (schemeOfBasis B)` has the same type.

Also update the `_axiomatic` doc-comment inventory in this file (the `FOUR remaining project axioms` list at :83–85 and :34) so it names `r3ConvectionGap_exists` instead of `r3_NSForms_exist`. **Doc-comment edits in `.lean` files are lean-coder's** (non-proof structure). Mirror the analogous torus comment update from #22/#24.

### Optional follow-up (NOT this PR) — dispose of the now-unused fat axiom

After C1, `r3_NSForms_exist` in `SolutionInterfaces.lean:300` is no longer referenced by the capstone (verify with `#print axioms exists_lerayHopf_r3`). Disposition options, to be decided by the orchestrator under soundness review (see §5 flag 1):
- **(a) Leave it.** Harmless dead axiom; CI axiom-leak gate keys on `#print axioms` of the capstone, which will no longer list it. Lowest-risk, matches "no edit to AxiomaticClosure" boundary.
- **(b) Demote it to a proved theorem** `r3_NSForms_exist := r3_NSForms_exists` (so any other consumer keeps compiling) — only if a grep shows other live consumers. Grep at plan time found the only non-doc consumer is the capstone at :97; `R3Capstone.lean` and doc strings reference it textually only.
- **(c) Delete it** if grep confirms the capstone is the sole consumer. Cleanest, but edits `SolutionInterfaces.lean` (outside this PR's minimal boundary). Recommend deferring (a)/(c) to a tiny follow-up after the swap PR is green.

**Recommendation: ship the swap with option (a) (leave the fat axiom dead), then a one-line follow-up PR for (c).** Keeps this PR minimal and the boundary clean.

---

## 3. Which existing decls each step consumes (verified names)

- **R2 (`r3_NSForms_exists`)** consumes `R3NSForms_of_gap` (`ConvectionForm.lean:230`, sorry-free) and the new `r3ConvectionGap_exists`. `R3NSForms_of_gap` in turn already consumes, as proved theorem content:
  - `convFormSchwartz_bound` (`ConvectionOperator.lean:360`) — the `b_bound` shape; itself a transport of R3-d `convIntegralSchwartz_bound_sup` (`TrilinearEstimate.lean:725`).
  - `convFormSchwartz_eq_witness` (`ConvectionOperator.lean:110`) — the `b_galerkin` non-vacuity pin to `convIntegralSchwartz`.
  - `convFormSchwartz_add_{1,2,3}` / `_smul_{1,2,3}` (`ConvectionOperator.lean:179–323`) — backing the algebra (consumed indirectly; the gap supplies `b_multilinear` as the tower).
  - `convFormSchwartz_antisymm` (`ConvectionOperator.lean:336`) — backing `b_antisymm_gap`.
  - These Tier-S lemmas consume the **12 TrilinearEstimate lemmas**: `convIntegralSchwartz_add_{1,2,3}` (A1–A3), `_smul_{1,2,3}` (A4–A6), `_integrand_integrable` (B1), `_bound_H1` (B2), `_ibp` (C1), `_antisymm_of_divFree` (C2), `_bound_sup` (C3) — all already proved (`TrilinearEstimate.lean`).
- **The density field** `schwartz_dense` of any `ConvectionGap` instance is dischargeable via `convectionGap_schwartz_dense` (`ConvectionForm.lean:522`) ← `schwartzDivFree_dense_of_curlDense` (`:481`) ← `curlSchwartzDense_holds` (proved theorem, `CurlDensityCapstone.lean:62`). Note: this PR does NOT construct a `ConvectionGap` instance (that is the months-class residual); the density lemma is already in the tree and is what makes the residual axiom *strictly* thinner (the density face is provably NOT part of the frontier).
- **C1 reroute** consumes `r3_NSForms_exists` (R2) in place of `r3_NSForms_exist`; type-compatible (`Nonempty (R3NSForms 𝔊)` for `𝔊 := schemeOfBasis B`).
- **Torus pattern consumed (as the template to copy, not a Lean dep):** `TorusConvectionForm.lean:664` (`torusConvectionGap_exists` axiom shape) and `:669` (`torus3_NSForms_exists` reroute shape).

**Mathlib decls:** none new. The whole PR is internal rewiring of already-proved project content.

---

## 4. Tractability + first PR

**Tractability: hours, not weeks.** Every supporting theorem is already proved sorry-free; the PR is a 2-file mechanical rewire that exactly copies the accepted torus #22 pattern. No new mathematics, no new Mathlib API, no proof search.

**The single first PR to land (and the whole of #48's reachable scope):**

> **PR "#48: thin-swap `r3_NSForms_exist` → `r3ConvectionGap_exists`"**
> 1. In `ConvectionForm.lean`, append `r3ConvectionGap_exists` (R1, ALLOW_AXIOM) and `r3_NSForms_exists` (R2, one-line proof via existing `R3NSForms_of_gap`).
> 2. In `GalerkinODECapstone.lean`, reroute the body of `exists_lerayHopf_r3` from `r3_NSForms_exist` to `r3_NSForms_exists` (C1), and update the `_axiomatic` doc-comment axiom inventory.
> 3. Leave the now-dead fat axiom in `SolutionInterfaces.lean` (option (a)); verify `#print axioms exists_lerayHopf_r3` no longer lists `r3_NSForms_exist` and now lists `r3ConvectionGap_exists`.

**Recommended FIRST task to hand to `lean-coder`:** Add the `r3ConvectionGap_exists` axiom (R1) and the `r3_NSForms_exists` theorem signature (R2) to `ConvectionForm.lean`. This is the smallest, self-contained, build-checkable unit; the file already imports everything needed (`ConvectionOperator`, `AxiomaticClosure`, `SchwartzDivFreeBasis`) and `R3NSForms_of_gap` is in-file, so R2's body compiles immediately. Then hand C1 (the capstone reroute) to `lean-prover`.

**Decl order:** R1 → R2 (same file, R2 depends on R1) → C1 (other file, depends on R2).

---

## 5. Soundness flags for orchestrator review

1. **Residual-axiom faithfulness (the central soundness check).** `r3ConvectionGap_exists : ∀ 𝔊, Nonempty (ConvectionGap 𝔊)` must be confirmed (a) TRUE — the genuine `(u·∇)v` form on `L²_σ` witnesses a `ConvectionGap` (its `b_extends`/`b_multilinear`/`b_antisymm_gap`/`b_cont_fixedTest`/`schwartz_dense` are all real properties of that form); and (b) STRICTLY THINNER than `r3_NSForms_exist` — i.e. `R3NSForms_of_gap` genuinely derives every `R3NSForms` field (it does, sorry-free), and `ConvectionGap` carries NO `R3NSForms`/`Nonempty (R3NSForms 𝔊)` field and does NOT pre-bake `b_bound`/`b_galerkin` (confirmed: `ConvectionForm.lean:136–145` no-smuggle audit). **This is the statement that should get `/codex:adversarial-review --effort xhigh` before merge** (see §6). The non-vacuity pin survives: `b_extends` + `convFormSchwartz_eq_witness` force `b = convIntegralSchwartz` on Schwartz triples, excluding `b = 0`/secretly-Stokes — exactly as the fat axiom required.

2. **No statement weakening.** `R3NSForms` is untouched; `r3_NSForms_exists` (R2) proves the *identical* conclusion `Nonempty (R3NSForms 𝔊)` the fat axiom asserted. No hypothesis dropped, no conclusion narrowed. The swap is conclusion-preserving.

3. **`ConvectionGap` honesty label is MIXED, not uniformly thinner — already documented and accepted.** `ConvectionForm.lean:51–70,123–134` is explicit that `b_multilinear` + `b_antisymm_gap` are *equi-level* (asserted residual of the missing operator), while `b_bound`/`b_galerkin`/extension are *thinner* (derived). This is the honest, reviewed state from the Tier-G round-3 correction (the false all-three-slot `b_cont` was already removed). The orchestrator should confirm the codex review of R1 re-affirms this MIXED label is acceptable as a 1-for-1 swap of the fat axiom (it is the same standard the torus #22 `torusConvectionGap_exists` was accepted under).

4. **Dead-axiom disposition.** If option (a) (leave the fat axiom) is taken, confirm the CI axiom-leak gate keys on `#print axioms` of the capstone (not on textual presence of `axiom` lines), so the dead `r3_NSForms_exist` does not re-trip a gate. Plan-time reading of the gate behavior (memory: `project_parallel_lane_ci_gate`, `feedback_run_grep_guardrails_locally_before_pr`) indicates the grep guard trips on line-initial `axiom` — so leaving the fat axiom keeps a marked `axiom` line in the tree; that is fine (it is still a legitimately-marked ALLOW_AXIOM), but if a tighter follow-up wants axiom-count to actually drop, take option (c) (delete) in the follow-up PR.

5. **No new analytical claim in any name.** `r3ConvectionGap_exists` names a structure-existence; `ConvectionGap` already encodes the (reviewed) frontier. No overclaim term enters a name. `r3_NSForms_exists` (note the trailing `s`) is the proved theorem; it is intentionally one character off from the axiom `r3_NSForms_exist` to mirror the torus pair `torus3_NSForms_exists`/`torus3_NSForms_exist` — flag for codex that this near-collision is the deliberate, torus-matching naming (so a reviewer does not flag it as an accidental typo).

---

## 6. Codex review points

- **R1 `r3ConvectionGap_exists` (the new axiom statement) — REQUIRED `/codex:adversarial-review --effort xhigh` before merge.** Verify: (a) it is genuinely thinner than `r3_NSForms_exist` (all `R3NSForms` algebra is theorem content via `R3NSForms_of_gap`); (b) it is TRUE and NON-VACUOUS (the `b_extends`/`convFormSchwartz_eq_witness` pin excludes `b=0`); (c) the MIXED honesty label (`b_multilinear`/`b_antisymm_gap` equi-level) is acceptable, matching the accepted torus `torusConvectionGap_exists`; (d) no over-strength (no false all-three-slot continuity — already removed). This is the soundness gate of the PR; the orchestrator owns the codex call (workers cannot run slash commands).
- **R2 `r3_NSForms_exists` reroute** — light review: confirm it proves the identical conclusion the fat axiom asserted (conclusion-preserving swap) and is sorry-free via the existing `R3NSForms_of_gap`.
- **C1 capstone reroute** — confirm `#print axioms exists_lerayHopf_r3` drops `r3_NSForms_exist` and now lists `r3ConvectionGap_exists` (and still the other R3 axioms), proving the swap actually took effect.

`R3NSForms_of_gap`, the Tier-S `convFormSchwartz_*`, the 12 TrilinearEstimate lemmas, and the density chain were already reviewed when merged; they do NOT need re-review for this PR.

---

## 7. Definition of done for #48

- `r3ConvectionGap_exists` added with `ALLOW_AXIOM` marker + an entry in the file's assumptions section.
- `r3_NSForms_exists` added, **sorry-free**, proved via the existing `R3NSForms_of_gap` (must-prove target).
- `exists_lerayHopf_r3` rerouted to consume `r3_NSForms_exists`; stays **sorry-free** (must-prove target).
- `#print axioms exists_lerayHopf_r3` no longer lists `LerayHopf.r3_NSForms_exist`; it now lists `LerayHopf.r3ConvectionGap_exists` (strictly thinner). The fat structure-existence axiom is eliminated from the capstone's axiom set.
- `lake build` green; `scripts/agent-preflight.sh` + the grep guardrails (`check-no-sorry`, `check-no-axiom` ALLOW-marker, `check-theorem-names`) pass.
- Codex `/codex:adversarial-review` on R1 returns no soundness blocker (orchestrator-run).

**Must-prove targets:** `r3_NSForms_exists` (R2), rerouted `exists_lerayHopf_r3` (C1).
**Scaffold / residual axiom:** `r3ConvectionGap_exists` (R1) — marked, reviewed, strictly thinner.

---

## 8. The precise remaining frontier (after this PR)

The single residual `r3ConvectionGap_exists` carries exactly the **weak convection operator** `(u·∇)v` on `L²_σ(ℝ³)`: a total trilinear `b` extending the proved Schwartz-class `convFormSchwartz`, antisymmetric in slots 2,3 over arbitrary `L²_σ` (distributional IBP for `L²` vector fields), and jointly L²-continuous in slots 1,2 at each fixed Schwartz test. Its eventual full removal (route A) requires building, in Lean/Mathlib:
- the weak `(u·∇)v` map as an `L²` (or `H⁻¹`) element for `L²_σ` inputs;
- distributional integration-by-parts / the divergence theorem for `L²` vector fields beyond Schwartz tests;
- the bounded-bilinear-at-fixed-test extension that ties them together.

That is a months-class P-γ analysis milestone, not bounded work, and is correctly deferred. After this PR the R3 capstone's axiom set is `{curlSchwartzDense_holds (PROVED — not an axiom), galerkin_limit_passage_R3, galerkin_spacetime_precompact_R3, r3ConvectionGap_exists}` in place of `{…, r3_NSForms_exist}` — fat convection-form existence eliminated, thin weak-operator frontier isolated.
