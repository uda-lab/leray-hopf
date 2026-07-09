# Task contract — torus #53: discharge `torusConvectionGap_exists` (3 → 2 axioms)

**Milestone / issue:** #53 — genuinely remove the torus project axiom
`torusConvectionGap_exists : Nonempty TorusConvectionGap`, reducing the 𝕋³ capstone
`exists_lerayHopf_torus3` from **3 → 2** project axioms
(`aubin_lions`, `galerkin_limit_passage` remain). *(NOTE 2026-07-04: both remaining axioms are now also REMOVED — `galerkin_limit_passage` by #25/PR #75 and `aubin_lions` by #23/PR #89; T³ is unconditional. This doc is historical.)*

**Template:** ℝ³ #56 (merged PR #60). Files studied on `main`:
`LerayHopf/R3/{SobolevEmbedding,EnergyClassConvection,TensorIntersection,ConvectionForm,ConvectionExtension}.lean`.

**Hard boundary (No-overclaim):** Hard Rule #2 — `torusConvectionGap_exists` is re-exported as a
**theorem** of the same name, never renamed; the proved operator core is a new name
(`torusConvectionGapOp_holds`). No analytical assumption may be encoded into any new name.

---

## Executive summary

Discharging the torus gap is **not** a verbatim copy of R3 — it is *easier on two axes and
harder on one*. **Easier:** density is already proved (`velocityProjection_n_tendsto`,
`VelocityGalerkin.lean`); `TensorIntersection` is domain-generic and **reused verbatim**; and the
finite box form `galerkinConvection` already has **sorry-free** trilinearity, `Vₙ`-antisymmetry,
an L²-bound, and level-stability in `TorusConvectionForm.lean`. **Harder:** unlike R3, the torus has
**no energy-class convection form at all** — `SobolevTorus.lean` is a scalar Fourier-weight
*predicate scaffold* (no H¹_σ space, no H¹↪L⁶, no IBP, no `convFormH1` analogue). The whole
`EnergyClassConvection.lean` analytic layer (B4–B7 + the from-scratch H¹·H¹ weak Leibniz
`h1Leibniz2` + IBP) has **no torus counterpart**.

**Biggest risk / decision point.** There are two viable routes for the torus energy-class form, and
the PR count hinges on which is taken (PR-1 below resolves this with a codex-gated assessment, not a
guess):

- **Route F (Fourier/Parseval — recommended).** Define the torus total convection form *directly*
  on the Fourier side as a Parseval bilinear in (∇v̂, û, ŵ), bypassing any spatial integral and the
  entire `convFormH1`/IBP/`h1Leibniz2` machinery. The torus `galerkinConvection` is *already* a
  finite Fourier sum, so its infinite-mode extension is the natural total form, and antisymmetry
  reduces to the same div-free identity `∑ₐ kₐ ûₐ(k)=0` already used in
  `galerkinConvection_antisymm` — **no Leibniz product rule, no integration by parts**. This is the
  payoff of the compact domain. The cost is a torus H¹_σ space + Parseval summability/bound
  (Bessel-type, much lighter than R3's GNS embedding).

- **Route S (spatial mirror).** Faithfully port `convFormH1` + IBP + `h1Leibniz2` to 𝕋³. This is
  the literal R3 mirror but re-derives the hardest analytic file from scratch and needs a real torus
  H¹↪L⁶; estimated ~2–3 extra PRs of pure analysis. Not recommended unless PR-1 finds a blocking
  obstruction to Route F.

**Reusable as-is:** `LerayHopf/R3/TensorIntersection.lean` (`[Field K] [AddCommGroup V] [Module K V]`
generic) — imported and instantiated at `K = ℝ`, `V = L2Sigma`; **no torus analogue**. The R3
`ConvectionExtension.lean` *gluing skeleton* (edge submodules, `LinearPMap.sup`, `gInv` left-inverse,
antisymmetrizer `(id − swap)/2`, `TensorProduct.lift` edges) is **structurally reusable** with the
edge class swapped `𝒮 → 𝒢 = span of Galerkin tests`; the *contents* of the edge bilinear (R3's
`convBLT_fixedTest` double-BLT) are replaced by the torus fixed-test BLT from PR-2.

**Realistic PR count:** **6 PRs** on Route F (7–8 on Route S). PR-0 is the assessment; PRs 1–4 build;
PR-5 assembles the gap-op core; PR-6 rewires + flips the axiom gate.

---

## What already exists (do NOT rebuild)

| Piece | Location | Status |
|---|---|---|
| `structure TorusConvectionGap` (7 fields) | `TorusConvectionForm.lean:523` | **given** — the construction target |
| axiom `torusConvectionGap_exists` | `TorusConvectionForm.lean:664` | to be removed in PR-6 |
| `Torus3NSForms_of_gap : TorusConvectionGap → Nonempty Torus3NSForms` | `TorusConvectionForm.lean:583` | **sorry-free** — do not touch |
| `theorem torus3_NSForms_exists` | `TorusConvectionForm.lean:669` | consumer of the axiom; stays, reroutes automatically |
| `galerkinConvection n` (finite Fourier box form) | `SolutionInterfaces.lean:89` | **given** |
| `galerkinConvection_{add,smul}_{1,2,3}`, `_bound`, `_antisymm` (over Vₙ), `_level_stable` | `TorusConvectionForm.lean` | **sorry-free** — reuse |
| `IsGalerkinTest w := ∃ n, velocityProjection_n n w = w` | `SolutionInterfaces.lean:123` | **given** |
| `velocityProjection_n_tendsto` (density of Pₙ → id) | `VelocityGalerkin.lean:349` | **sorry-free** — this IS `galerkinTest_dense` |
| `velocitySpan n`, `velocityP_fixes_span`, `mem_velocitySpan_of_fixed`, finite-dim | `TorusGalerkinScheme.lean` | **given** |
| `L2Sigma`, `L2VF`, `L2C`, `mFourierCoeff3`, `fourierBox`, `DivFreeL2`, `mem_L2Sigma_iff` | `Leray.lean`, `FunctionSpaces.lean` | **given** |
| `coeff_zero_outside_box`, `norm_mFourierCoeff3_le` | `TorusConvectionForm.lean` | **sorry-free** — reuse |
| `TensorIntersection.range_map_subtype_inf_range_map_subtype` | `R3/TensorIntersection.lean` | **generic — reuse verbatim** |

**Crucial gap vs R3:** `SobolevTorus.lean` is scaffold-only — it gives a *scalar* `memH1Torus`
Fourier-weight predicate on `L2C` and nothing else. There is **no** torus H¹_σ submodule, **no**
H¹↪L⁶, **no** spatial convection integral. This is the single largest build difference from R3.

---

## Files (dependency order, Route F)

1. `LerayHopf/SobolevTorus.lean` — **EXTEND** (currently scaffold): add a vector H¹_σ submodule of
   `L2Sigma` via the Fourier-weight predicate, plus the Parseval/Bessel summability facts. (coder)
2. `LerayHopf/TorusEnergyConvection.lean` — **NEW**: the torus total convection form `convFormFourier`
   on H¹_σ (Parseval bilinear), its trilinearity, antisymmetry (div-free identity, **no IBP**), the
   `galerkinConvection`-pin on Vₙ, and the fixed-Galerkin-test L² bound + BLT. (coder + prover)
3. `LerayHopf/TorusConvectionExtension.lean` — **NEW**: the determined-form construction —
   edge submodules over `𝒢 = galerkinSpan`, `LinearPMap.sup` glue (via the reused
   `TensorIntersection` overlap), `gInv`, antisymmetrizer, and the assembled five operator fields.
   Produces `torusConvectionGapOp_holds`. (coder + prover)
4. `LerayHopf/TorusConvectionForm.lean` — **EDIT (PR-6 only)**: delete the axiom; re-export
   `torusConvectionGap_exists` as a theorem assembling `torusConvectionGapOp_holds` + density.
5. `scripts/check-axioms-live.sh` — **EDIT (PR-6 only)**: drop `LerayHopf.torusConvectionGap_exists`
   from the `exists_lerayHopf_torus3` expected set (6 → 5 total; 3 → 2 project).

> All new modules sit **below** `SolutionInterfaces.lean`/`SobolevTorus.lean` and **above**
> `TorusConvectionForm.lean` in the DAG. `TorusConvectionForm.lean` is imported by
> `TorusGalerkinODECapstone.lean`, `TorusAxiomatic.lean`, and `LerayHopf.lean` — see "Acyclic rewire".

---

## Declarations, in dependency order

> Legend: **[MP]** must-prove (sorry-free target) · **[SO]** scaffold-only (placeholder/Prop field,
> may carry a marked `sorry`). Each new *statement* (def or theorem signature) gets a codex review
> point — see "Codex review points".

### PR-0 — Route assessment (planning artifact only; no Lean edit)
- Decide **Route F vs Route S** by checking whether a Parseval-side antisymmetry is expressible with
  the existing `mFourierCoeff3` API (it is — `galerkinConvection_antisymm` already does the finite
  case). Output: a short note appended here + go/no-go for Route F. **This is the de-risking step the
  R3 lane skipped and paid for in codex rounds.** Owner: lean-planner (this agent) on request, or a
  research subagent. No new declarations.

### PR-1 — Torus H¹_σ space + Parseval (file 1, `SobolevTorus.lean` EXTEND)
- `memH1VFTorus (u : L2VF) : Prop` **[MP]** — vector H¹: all three complex components satisfy
  `memH1Torus`. (mirror of `memH1VF_R3`; reuse the existing scalar `memH1Torus`.)
- `H1SigmaTorus : Submodule ℝ L2Sigma` **[MP]** — `{u | memH1VFTorus (u:L2VF)}` as a submodule
  (closed under +, • via additivity of `mFourierCoeff3` already proved in TorusConvectionForm).
- `mem_H1SigmaTorus_iff` **[MP]** — membership unfolding.
- `gradPairingSummable` **[MP]** — for `u ∈ H¹_σ`, `v ∈ H¹_σ`, `w ∈ L²_σ` the Parseval triple sum
  `∑_k û_a(k)·(2πi lₐ)·v̂_i(l)·ŵ_i(-(k+l))`-shape is summable (Bessel + Cauchy–Schwarz on the
  H¹ weight). **This is the torus analogue of R3 `convFormH1_integrable`** but is a *Fourier
  summability* lemma, not a spatial-integrability one — much lighter.
- `galerkinTestSpan_subset_H1Sigma` **[MP]** — every `IsGalerkinTest` field is in `H1SigmaTorus`
  (finite Fourier support ⟹ the weighted sum is finite).

### PR-2 — Torus energy-class convection form (file 2, `TorusEnergyConvection.lean` NEW)
- `convFormFourier (u v w : L2VF) : ℝ` **[MP]** — the **total** Parseval convection form
  `(∑_i ∑_a ∑'_k ∑'_l û_a(k)·(2πi lₐ)·v̂_i(l)·ŵ_i(-(k+l))).re` (the infinite-mode `tsum` extension
  of `galerkinConvection`). Sound for all `u,v,w : L2VF` by the mathlib `tsum`-off-summable
  convention; equals the genuine `∫(u·∇)v·w` on H¹_σ.
- `convFormFourier_galerkin_pin` **[MP]** — on `Vₙ` triples, `convFormFourier = galerkinConvection n`
  (the finite box exhausts the support; reuse `coeff_zero_outside_box`). **This is the non-vacuity
  pin and the `b_galerkin_pin` field.** *(Codex: vacuity — must exclude `b=0`.)*
- `convFormFourier_add_{1,2,3}`, `convFormFourier_smul_{1,2,3}` **[MP]** — trilinearity from `tsum`
  linearity (mirror the finite `galerkinConvection_{add,smul}_*` proofs, with `tsum_add`/`tsum_mul`).
- `convFormFourier_multilinear` **[MP]** — package the trilinear `B : L²_σ →ₗ →ₗ →ₗ ℝ` tower
  (the `b_multilinear` field).
- `convFormFourier_antisymm` **[MP]** — `convFormFourier u v w = - convFormFourier u w v` over
  **arbitrary** L²_σ. **THE soundness-critical lemma.** On the torus this is the div-free identity
  `∑ₐ kₐ ûₐ(k)=0` applied mode-by-mode (the involution `l ↦ -(k+l)` over the *full* lattice, which —
  unlike the box — IS invariant), **with no IBP and no `h1Leibniz2`**. *(Codex: this is where R3
  needed a from-scratch weak Leibniz; confirm the Fourier route is genuinely IBP-free and the tsum
  reindex is valid — needs `gradPairingSummable` for unconditional rearrangement.)*
- `convFormFourier_bound_test` **[MP]** — for a Galerkin test `w`, `|convFormFourier u v w| ≤ C(w)·‖u‖·‖v‖`
  with `C(w)` depending only on `w` (the `b_bound_test` field). The genuine `|b| ≤ ‖∇w‖_∞‖u‖‖v‖`;
  on Fourier side, `‖∇w‖_∞ < ∞` because `w` is a trig polynomial (finite support).
  **MUST be uniform in `(u,v)` and `n`-independent** — the level-dependent `galerkinConvection_bound`
  does NOT supply this. *(Codex: over-strength bound trap — the constant must NOT secretly depend on
  the L² level of u,v; and the varied slot is (u,v), the FIXED slot is the smooth w.)*
- `convFormFourier_cont_fixedTest` **[MP]** — joint L²-continuity of `(u,v) ↦ convFormFourier u v w`
  at fixed Galerkin test `w` (the `b_cont_fixedTest` field), via the BLT extension of the bounded
  bilinear from PR-1's H¹_σ density / the fixed-test bound. *(Codex: discontinuous-slot trap — the
  varied args (u,v) must be in the L²-continuous slots, w fixed smooth; this is exactly the field R3
  codex refuted on the raw-Hamel object.)*

> **Assess (PR-0 deliverable):** whether `convFormFourier_cont_fixedTest` needs the full
> R3 double-BLT `extendOfNorm`/`extend` tower, or whether — because `convFormFourier` is already
> *total and bounded at fixed test* — continuity follows directly from `isBoundedBilinearMap` on the
> fixed-test slice (skipping R3's `convBLT_fixedTest` infrastructure entirely). Recommended: try the
> direct `LinearMap.mkContinuousâ‚‚`/`isBoundedBilinearMap` route first; fall back to the determined-edge
> construction (PR-3) only if the bound-at-fixed-test does not directly give continuity for *all*
> `(u,v)` (R3 needed the determined edge precisely because its raw form was a Hamel object — the torus
> `convFormFourier` is NOT, so this may collapse PR-3).

### PR-3 — Determined-form gluing (file 3, `TorusConvectionExtension.lean` NEW) — *conditional*
> **Build PR-3 only if PR-2's direct route fails the `b_cont_fixedTest` field for arbitrary (u,v).**
> If `convFormFourier` is already total + jointly continuous at fixed test (likely, since it is not a
> Hamel object), **skip PR-3 entirely** and feed `convFormFourier` straight into the gap-op assembly.
> If needed, mirror the R3 skeleton with `𝒮 → 𝒢`:
- `galerkinSpan : Submodule ℝ L2Sigma` **[MP]** — `span ℝ {x | IsGalerkinTest x}` (mirror `schwartzSpan`).
- `edgeSlot2`, `edgeSlot3`, `detDomain` **[MP]** — `𝒢⊗L²`, `L²⊗𝒢`, their sup (mirror R3 verbatim,
  `S := galerkinSpan`).
- `edge_inf_eq_galerkin_tensor` **[MP]** — `edgeSlot2 ⊓ edgeSlot3 = 𝒢⊗𝒢`; **`:= TensorIntersection
  .range_map_subtype_inf_range_map_subtype galerkinSpan`** (the generic lemma, **reused verbatim**).
- `edge2Bil`, `edge3Bil`, `psiD` (glue via `LinearPMap.sup`), `gInv`, `antisymmetrizer`,
  `detExtend`, `convFormL2Torus_def` **[MP]** — mirror R3 `ConvectionExtension.lean` C4–C10, edge
  bilinears built from PR-2's torus fixed-test BLT instead of R3's `convBLTspan`.

### PR-4 — Operator-core sub-structure + assembly (file 2 or 3, whichever is the leaf)
- `structure TorusConvectionGapOp` **[MP]** — `TorusConvectionGap` minus `galerkinTest_dense`
  (mirror R3's `ConvectionGapOp` reorg): the six operator fields `b`, `b_galerkin_pin`,
  `b_multilinear`, `b_antisymm_gap`, `b_bound_test`, `b_cont_fixedTest`.
  *(Note: torus has `b_bound_test` AND `b_cont_fixedTest` as SEPARATE fields — R3 folded the bound
  into `b_cont_fixedTest`; both must be produced.)*
- `torusConvectionGapOp_holds : Nonempty TorusConvectionGapOp` **[MP]** — assemble the six fields from
  the PR-2 (and PR-3 if built) lemmas. **This is the sorry-free operator core** that replaces the
  axiom's hard content. *(Codex: full-structure review — vacuity via the pin, bound strength,
  continuity slot, antisymmetry over arbitrary L²_σ.)*

### PR-5 — *(merged into PR-4 if small)* — proved-density helper
- `torusGalerkinTest_dense` **[MP]** — the `galerkinTest_dense` field, **proved** from
  `velocityProjection_n_tendsto` (the sequence `Pₙ u` is `IsGalerkinTest` and tends to `u`).
  This is the one provable field that R3 carried as `convectionGap_schwartz_dense`. *(No new axiom.)*

### PR-6 — Rewire + axiom flip (files 4, 5 EDIT)
- In `TorusConvectionForm.lean`: **delete** `axiom torusConvectionGap_exists`; add
  `theorem torusConvectionGap_exists : Nonempty TorusConvectionGap` **[MP]** (same name, Hard Rule #2)
  assembling `torusConvectionGapOp_holds` + `torusGalerkinTest_dense` into a full `TorusConvectionGap`
  (mirror R3 `r3_NSForms_exists` body shape: `.elim fun g => ⟨{ … , galerkinTest_dense := … }⟩`).
  `torus3_NSForms_exists` (unchanged) consumes it; `Torus3NSForms_of_gap` (unchanged) does the rest.
- In `scripts/check-axioms-live.sh`: drop `LerayHopf.torusConvectionGap_exists` from the
  `exists_lerayHopf_torus3` assert set; update the header comment (3 → 2 project, 6 → 5 total).
- Run `bash scripts/agent-preflight.sh` + the three grep guardrails before the PR.

---

## Dependency edges (compile order)

```
SobolevTorus.lean (extended: H1SigmaTorus, Parseval)         [PR-1]
        │
        ▼
TorusEnergyConvection.lean (convFormFourier + 6 properties)  [PR-2]   ← uses galerkinConvection,
        │                                                              coeff_zero_outside_box,
        │  (only if direct cont. route fails)                          velocityProjection_n_tendsto
        ▼
TorusConvectionExtension.lean (determined edges, gInv, …)    [PR-3]   ← reuses R3/TensorIntersection
        │
        ▼
TorusConvectionGapOp + torusConvectionGapOp_holds            [PR-4]
        │
        ▼
TorusConvectionForm.lean  (axiom → theorem; PR-6)            [PR-6]   ← consumed by
        │                                                              TorusGalerkinODECapstone,
        ▼                                                              TorusAxiomatic, LerayHopf.lean
check-axioms-live.sh torus pin flip (3→2)                    [PR-6]
```

**Acyclic rewire.** The new modules import `SolutionInterfaces.lean` (for `galerkinConvection`,
`IsGalerkinTest`, `Torus3NSForms`), `SobolevTorus.lean`, `VelocityGalerkin.lean`,
`TorusGalerkinScheme.lean`, and `R3/TensorIntersection.lean` — all **upstream** of
`TorusConvectionForm.lean`. `TorusConvectionForm.lean` then imports the new
`TorusConvection{Energy,Extension}` modules and its existing `AxiomaticClosure`. Because
`TorusConvectionForm.lean` is the file that defines `TorusConvectionGap`/`Torus3NSForms_of_gap`
and is imported by the three downstream capstone files, the operator core MUST be defined
**upstream** of it (new files) and only the final theorem re-export lives **in** it — exactly the
R3 split where `r3ConvectionGapOp_holds` lives in `ConvectionExtension.lean` and
`r3ConvectionGapOp_exists`/`r3_NSForms_exists` re-export at the bottom. The consumer
(`torus3_NSForms_exists`) does NOT move; it already sits in `TorusConvectionForm.lean` and reroutes
automatically once the axiom becomes a theorem.

---

## Assumptions to package as marked `axiom`s

**None new.** This milestone *removes* an axiom; it must not introduce one. If PR-2's
`convFormFourier_antisymm` or `_bound_test` hits a genuine mathlib wall, the correct response per
AGENTS.md Rule #8 is to **leave the statement intact + `-- TODO:` the blocker and stop**, NOT to
re-axiomatize. The whole point of #53 is that the torus Fourier route makes these *provable*
(div-free identity for antisymmetry; finite support for the bound) — this is the de-risking content
of PR-0. The capstone's two then-surviving axioms (`aubin_lions`, `galerkin_limit_passage`) were
out of scope for #53 and untouched. (Both subsequently removed: `galerkin_limit_passage` by #25/PR #75, `aubin_lions` by #23/PR #89.)

---

## Codex review points (`/codex:adversarial-review --effort xhigh`, run by orchestrator)

Every new *statement* gets reviewed before proofs are attempted. Priority (soundness-sensitive —
these are the exact traps codex caught on R3 #56/#48 and torus #22):

1. **`convFormFourier_antisymm`** (PR-2) — antisymmetry over **arbitrary** L²_σ. *Trap:* is the
   torus Fourier route genuinely IBP-free, and is the `tsum` involution reindex `l ↦ -(k+l)` valid
   over the full lattice (needs unconditional summability from `gradPairingSummable`)? Confirm it is
   NOT the box-restricted `Vₙ` antisymmetry (which is the only thing `galerkinConvection_antisymm`
   gives). *(Same class as R3's `h1Leibniz2` / "antisymmetry is part of the missing operator".)*
2. **`convFormFourier_bound_test`** (PR-2) — *over-strength bound trap.* The constant must depend
   ONLY on `w`, be uniform in `(u,v)`, and be **`n`-independent** (NOT the level-dependent
   `galerkinConvection_bound` constant). The varied slot is `(u,v)`; the fixed smooth slot is `w`.
3. **`convFormFourier_cont_fixedTest`** (PR-2) — *discontinuous-slot trap.* Continuity must be in the
   two L² slots `(u,v)` at fixed Galerkin test `w`. This is the field R3 codex refuted on the raw
   Hamel object — verify the torus total form does not put a varied argument into a discontinuous
   index.
4. **`convFormFourier_galerkin_pin` / non-vacuity** (PR-2) — the pin must exclude `b = 0`
   (`galerkinConvection ≢ 0`); same vacuity audit codex applied to torus #22 / R3 #48's
   fat→thin swap. **Watch the #48 lesson:** do NOT let the thin gap secretly re-assume a
   proved-equivalent of the bound (`b_cont_fixedTest ≡ b_bound`); state honestly that the bound is
   *assumed in continuity form*, not re-proved, if the direct route does not actually discharge it.
5. **`TorusConvectionGapOp` + `torusConvectionGapOp_holds`** (PR-4) — full-structure review: no
   `TorusConvectionGap`/`Torus3NSForms` field smuggled in; six fields match the gap's first six;
   density genuinely separated out.
6. **PR-6 axiom flip** — confirm `#print axioms exists_lerayHopf_torus3` shows exactly
   `propext Classical.choice Quot.sound aubin_lions galerkin_limit_passage` (no
   `torusConvectionGap_exists`, no `sorryAx`) before merge. *(Historical: `aubin_lions` and `galerkin_limit_passage` were subsequently removed by #23/PR #89 and #25/PR #75 respectively.)*

---

## Definition of done

- `bash scripts/agent-preflight.sh` green (`lake build` passes) at PR-6.
- `convFormFourier` and its six properties (PR-2), `torusConvectionGapOp_holds` (PR-4),
  `torusGalerkinTest_dense` (PR-5/4), and the re-exported `theorem torusConvectionGap_exists` (PR-6)
  are **sorry-free** (must-prove targets).
- `axiom torusConvectionGap_exists` is **deleted**; the name survives as a theorem (Hard Rule #2).
- `scripts/check-axioms-live.sh` `exists_lerayHopf_torus3` pin reduced to **2 project +
  3 kernel = 5 total**; CI axiom-leak gate green.
- No new `axiom`/`opaque`/`constant`/`unsafe` anywhere in the new files.
- `Torus3NSForms_of_gap`, `torus3_NSForms_exists`, and the capstone are **untouched** in statement
  and reroute automatically.

**Scaffold-only vs must-prove summary:** *Everything load-bearing is must-prove.* The only
intentionally-`Prop`/placeholder items are the structure *field declarations* of
`TorusConvectionGapOp` (data + Prop, like the existing `TorusConvectionGap`) — but their **inhabitant**
`torusConvectionGapOp_holds` is must-prove and sorry-free, so no marked `sorry` should survive past
PR-4. If PR-2's analytic lemmas cannot be finished, they stay `-- TODO:`-blocked (Rule #8), and PR-6
does NOT land — the axiom is not removed until the core is genuinely proved.

---

## Recommended first task to hand to `lean-coder`

**PR-1 (`SobolevTorus.lean` EXTEND):** add `memH1VFTorus`, `H1SigmaTorus` (submodule),
`mem_H1SigmaTorus_iff`, and the signatures (statements only, bodies deferred to `lean-prover`) of
`gradPairingSummable` and `galerkinTestSpan_subset_H1Sigma`. This is the unblocking foundation —
mechanical, mirrors `memH1VF_R3`/`H1Sigma'`, and reuses the already-proved `mFourierCoeff3`
additivity/`coeff_zero_outside_box` lemmas. **Before PR-1, run PR-0** (Route F vs S go/no-go) so the
coder builds against the Fourier form, not the spatial one.
