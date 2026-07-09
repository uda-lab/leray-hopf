# Convection Frontier Gate Note — Issue #12

**Date:** 2026-06-20
**Branch:** `lane-c/convection-near`
**Files examined:**
- `LerayHopf/R3/ConvectionForm.lean` (lines 1–323)
- `LerayHopf/R3/ConvectionOperator.lean` (lines 1–421)
- `LerayHopf/R3/TrilinearEstimate.lean` (lines 1–799)
- `LerayHopf/R3/DivergenceFree.lean` (lines 1–145)
- `LerayHopf/R3/Regularity.lean` (lines 1–100)
- `LerayHopf/R3/SolutionInterfaces.lean` (lines 1–648)
- `docs/scratch/stream-c-convgap-topology.md`

---

## 1. Honest domain for `b(u,v,w)` in 3D

**Verdict: H¹×H¹×L² (Ladyzhenskaya) or two-L²-slots at fixed Schwartz w. Never L²×L²×L².**

Evidence (file:line):

- `ConvectionOperator.lean:19–26`: "The trilinear convection form `b(u,v,w) = ∫(u·∇)v·w` is **unbounded in pure L²×L²×L² norms** ... So `b` does **not** extend continuously from Schwartz triples to all of `L²_σ × L²_σ × L²_σ`."
- `TrilinearEstimate.lean:361–369` (B2): `|conv ψu ψv ψw| ≤ (∑_a ‖ψu_a‖_{L²}) · (∑_{a,i} ‖∂_a ψv_i‖_{L²}) · (∑_i ‖ψw_i‖_{L∞})`. Slot v = H¹ seminorm, slot w = L∞.
- `TrilinearEstimate.lean:725–739` (C3): Under div-free on slot u, `|conv| ≤ C(w) · ‖ψu_a‖_{L²} · ‖ψv_i‖_{L²}` where `C(w) = ∑_{i,a} ‖∂_a ψw_i‖_{L∞-seminorm}`. Two L² slots, but slot w must be Schwartz (C(w) finite only for Schwartz w).
- `stream-c-convgap-topology.md:114–116`: "In **every** proven bound, **exactly two** factors are L² and the **third** factor lives in L∞/H¹. There is **no** proven (nor true) bound with all three factors in L²."
- `SolutionInterfaces.lean:227–229` (`R3NSForms.b_bound`): "For a **canonical Schwartz divergence-free** test `w` (`IsSchwartzDivFree_R3 w`), `|b(u,v,w)| ≤ C(w)·‖u‖·‖v‖`." The test slot w is explicitly restricted to Schwartz; slots u, v range over all L²_σ.

**Conclusion:** The correct domain is:
- **In slots u, v:** all of L²_σ(ℝ³).
- **In slot w (test slot):** restricted to `IsSchwartzDivFree_R3 w` (Schwartz div-free class) for the `b_bound` control. The form can be *defined* on all of L²_σ (as a trilinear functional), but the L²-bilinear bound `|b u v w| ≤ C(w)‖u‖‖v‖` is only guaranteed when w is Schwartz.
- **NOT** L²×L²×L² with a joint-continuity bound in all three slots simultaneously: this is false and was the round-3 error (`b_cont`, `ConvectionForm.lean:44–47`).
- The downstream use (`galerkin_limit_passage_R3`, `r3Evolution`) puts w in the Schwartz class in every actual application (`SolutionInterfaces.lean:70–76`, `stream-c-convgap-topology.md:69–76`).

---

## 2. Which `R3NSForms` fields are genuinely needed downstream

Evidence from `SolutionInterfaces.lean`:

| Field | Used where | Evidence |
|---|---|---|
| `b : L2Sigma_R3^3 → ℝ` | `r3Evolution.convForm := F.b` | line 309 |
| `b_antisymm` | `R3NSForms.b_self_zero` → energy proof | lines 279–283 |
| `b_add_{1,2,3}`, `b_smul_{1,2,3}` | Galerkin ODE linearity in `u_ode` | line 347–350 |
| `b_bound` | `galerkin_limit_passage_R3` kills nonlinear error "via `b_bound`" | lines 496, comment at 491 |
| `b_galerkin` | Non-vacuity pin; ensures `b≠0` at construction | lines 242–253 |

Fields used at Galerkin test functions only (range of `𝔊.P n`, which by `range_schwartz` are Schwartz): **`b_bound`** and the ODE evaluation `F.b (u t) (u t) w` where `w = 𝔊.P n w` is Schwartz by `range_schwartz` (line 163–167).

Fields needed for arbitrary L²_σ arguments: `b_add_{1,2,3}`, `b_smul_{1,2,3}` (algebraic linearity in the ODE and limit passage), `b_antisymm` (self-zeroing).

**Summary:** the Galerkin ODE needs the algebraic trilinear structure for arbitrary L²_σ. The limit passage needs `b_bound` at Schwartz test w only. `b_galerkin` is non-vacuity.

---

## 3. Can `R3NSForms` be refactored to separate Galerkin from too-strong all-L²_σ assumptions?

**Already done in the current codebase.** The round-4 `ConvectionGap` structure (`ConvectionForm.lean:145–196`) implements exactly this separation:

- The **algebraic** structure (trilinearity, antisymmetry) is carried as gap fields `b_multilinear` and `b_antisymm_gap` — both explicitly labeled as "the honest residual of the missing weak operator" (`ConvectionForm.lean:159–176`).
- The **analytic** structure (bilinear bound at Schwartz w) is derived in `R3NSForms_of_gap` from `b_cont_fixedTest` + `schwartz_dense` + `convFormSchwartz_bound` — not assumed.
- The **false** global L²×L²×L² continuity is absent: `ConvectionForm.lean:141–143` explicitly states "There is **no** `Continuous (… L2Sigma_R3 × L2Sigma_R3 × L2Sigma_R3 …)` field — the round-3 `b_cont` (joint continuity on `L²×L²×L²`) was **false** for the real form."

The refactoring is structurally complete. What remains is discharging the two frontier fields (`schwartz_dense` and `b_cont_fixedTest`) and the algebraic fields (`b_multilinear`, `b_antisymm_gap`) — all four are currently *assumptions* in `ConvectionGap`, isolating the genuine Mathlib-absent pillars.

---

## 4. Does a narrower domain reduce `r3_NSForms_exist`, or force capstone-interface changes?

**The narrower domain does NOT change `R3NSForms` or force interface changes.** Evidence:

- `R3NSForms.b_bound` (`SolutionInterfaces.lean:227–229`) already has the Schwartz-test restriction (`IsSchwartzDivFree_R3 w`). The interface is already stated at the honest domain.
- `r3_NSForms_exist` (`SolutionInterfaces.lean:272`) is an axiom with an `ALLOW_AXIOM` marker; it asserts `Nonempty (R3NSForms 𝔊)` without change.
- `ConvectionForm.lean:229` proves `R3NSForms_of_gap` as `ConvectionGap 𝔊 → Nonempty (R3NSForms 𝔊)`, leaving `r3_NSForms_exist` in `SolutionInterfaces.lean` untouched. The assembly path is: discharge `ConvectionGap` → get `r3_NSForms_exist` via `R3NSForms_of_gap`.
- The Galerkin-ODE interface (`GalerkinSolutionData_R3`) and limit-passage axiom (`galerkin_limit_passage_R3`) use `b` only at Schwartz test fields, consistent with the narrower domain.

**No capstone-interface changes required.**

---

## 5. Subtargets: `b_cont_fixedTest` and `schwartz_dense`

### Location and current declaration status

Both are **structure fields** of `ConvectionGap`, not standalone lemmas. They appear at:
- `ConvectionForm.lean:187–188` (`b_cont_fixedTest` field declaration)
- `ConvectionForm.lean:194–196` (`schwartz_dense` field declaration)

They are **not** declared as standalone `theorem` or `lemma` targets elsewhere in the codebase. They exist only as assumed fields within `ConvectionGap`, which is the honesty isolation mechanism.

### `schwartz_dense` — assessment

**Statement** (`ConvectionForm.lean:194–196`):
```lean
schwartz_dense : ∀ (u : L2Sigma_R3),
  ∃ s : ℕ → L2Sigma_R3, (∀ n, IsSchwartzDivFree_R3 (s n)) ∧
    Filter.Tendsto s Filter.atTop (nhds u)
```

**Verdict: BLOCKED from current Mathlib.** This is the Weyl/Helmholtz density theorem:
the Schwartz divergence-free class is dense in L²_σ(ℝ³). The nearest Mathlib lemma is
`SchwartzMap.denseRange_toLpCLM` (dense Schwartz functions in L²), but that does not
account for the divergence-free constraint. The missing piece is:
"the intersection of the Schwartz class with the weakly-divergence-free subspace is dense
in `L²_σ`," which requires either the Leray projection (not in Mathlib) or the Helmholtz
decomposition. The sibling file `SchwartzDivFreeBasis.lean` exposes exactly this as
`CurlSchwartzDense` — a `Prop` frontier with a marked `sorry` (`SchwartzDivFreeBasis.lean:460`):
```
sorry -- ALLOW_SORRY: depends on CurlSchwartzDense (Helmholtz/Weyl density frontier,
-- not in mathlib; see helmholtz-density.md §4).  Orchestrator decides axiom-vs-sorry
```
`schwartz_dense` as a standalone statement is **equivalent** to `CurlSchwartzDense` plus
the curl-form construction in `SchwartzDivFreeBasis.lean`. It is **not provable now** from
existing Mathlib-level lemmas without that density frontier.

**Near-term provability:** Not reachable without either:
1. A Mathlib PR adding the Helmholtz decomposition for L²(ℝ³), or
2. Accepting `CurlSchwartzDense` as an axiom (the path `SchwartzDivFreeBasis.lean` sets up).

### `b_cont_fixedTest` — assessment

**Statement** (`ConvectionForm.lean:187–188`):
```lean
b_cont_fixedTest : ∀ (w : L2Sigma_R3), IsSchwartzDivFree_R3 w →
  Continuous (fun p : L2Sigma_R3 × L2Sigma_R3 => b p.1 p.2 w)
```

**Verdict: BLOCKED by the `b` reference.** This is a field of `ConvectionGap` asserting
continuity of the *particular* extension `b`. Stated as a standalone lemma, it would read:
"if `b` is the genuine convection form and w is Schwartz, then (u,v) ↦ b u v w is continuous
in the L²×L² topology." The underlying mathematical fact is TRUE:
- `convIntegralSchwartz_bound_sup` (`TrilinearEstimate.lean:725–739`) proves
  `|b u v w| ≤ C(w) · ‖ψu_a‖_{L²} · ‖ψv_i‖_{L²}` for Schwartz u, v, w,
  where `C(w) = ∑_{i,a} ‖∂_a ψw_i‖_{L∞-seminorm} < ∞` (finite for Schwartz w).
- A bounded bilinear form on Banach spaces is continuous (`ContinuousLinearMap` in Mathlib).

However, the statement as a field of `ConvectionGap` is about a *given* `b` (the candidate
total extension), not directly about `convFormSchwartz`. To prove this field for a *concrete*
`b`, one would need to:
1. Show `b` restricts to `convFormSchwartz` on the dense Schwartz class (via `b_extends`).
2. Show continuity of the bilinear map at Schwartz (u,v), fixed Schwartz w, from the bound.
3. Extend by density to all (u,v) in L²_σ — but this requires `schwartz_dense` (blocked above).

So `b_cont_fixedTest` for the candidate extension `b` is **also blocked** by the same density
frontier. The underlying bilinear bound is proved (in Tier S, `convFormSchwartz_bound`), but
the extension-by-density step to non-Schwartz (u,v) requires `schwartz_dense`.

**What IS currently provable at the Schwartz level:**
`convFormSchwartz_bound` (`ConvectionOperator.lean:360–419`) proves exactly the bound
`|convFormSchwartz u v w hu hv hw| ≤ C · ‖u‖ · ‖v‖` for Schwartz u, v (with fixed Schwartz w).
From this one can derive **Schwartz-restricted** bilinear continuity:
`Continuous (fun p : {u : L2Sigma_R3 // IsSchwartzDivFree_R3 u} ×
  {v : L2Sigma_R3 // IsSchwartzDivFree_R3 v} => convFormSchwartz p.1 p.2 w ...)`.
But that is not the same as continuity on all of L²_σ × L²_σ for the total extension `b`.

---

## 6. Gate verdict and frontier report

### Primary verdict

The statement-gate confirms:

1. **`R3NSForms` is already stated at the correct domain:** the two-L²-slots-at-fixed-Schwartz-w bound (not L²×L²×L²). No change needed.
2. **`ConvectionGap` (round 4) is the correct isolation:** it separates the genuine Mathlib-absent pillars from what is already proved. The algebraic fields (`b_multilinear`, `b_antisymm_gap`) are honest residuals; the analytic field (`b_cont_fixedTest`) and the density field (`schwartz_dense`) are the frontier.
3. **Do NOT assert a global L²_σ × L²_σ × L²_σ convection form** as a new target. The form is not L²-continuously extensible to all three slots simultaneously (false). The correct capstone is `R3NSForms_of_gap`: conditional on `ConvectionGap`, which contains the honest weaker data.
4. **`schwartz_dense` is BLOCKED** (Helmholtz/Weyl density, not in Mathlib). Its route to discharge is via `CurlSchwartzDense` in `SchwartzDivFreeBasis.lean`.
5. **`b_cont_fixedTest` (for the candidate extension b) is BLOCKED** by the same density frontier: one needs `schwartz_dense` to extend the Schwartz-level bilinear bound to non-Schwartz (u,v).
6. **What IS proved:** the bilinear bound at the Schwartz-class level (`convFormSchwartz_bound`, `ConvectionOperator.lean:360–419`), which is the correct analytic foundation. The sorry-free Tier-S (`ConvectionOperator.lean`) and R3-d (`TrilinearEstimate.lean`) layers are complete.

### The smallest-interface frontier

The two irreducible blockers, in dependency order:
1. **`CurlSchwartzDense` / `schwartz_dense`:** density of the Schwartz-div-free class in L²_σ(ℝ³). Mathlib gap: Helmholtz/Weyl decomposition. Path: `SchwartzDivFreeBasis.lean`, pending `curlSchwartzDense_holds`.
2. **`b_cont_fixedTest`** (and `b_multilinear`, `b_antisymm_gap`) for the candidate extension `b`: algebraic and analytic properties of the *total* operator, which requires the missing IBP/divergence-theorem calculus on general L²(ℝ³) functions (not just Schwartz). This is the original `r3_NSForms_exist` blocker.

### What is NOT a blocker

- The bilinear bound itself (`convFormSchwartz_bound`, proved sorry-free at `ConvectionOperator.lean:360–419`).
- The antisymmetry at the Schwartz level (`convFormSchwartz_antisymm`, proved at `ConvectionOperator.lean:336–348`).
- The trilinear estimates (`TrilinearEstimate.lean`, all sorry-free).
- The `R3NSForms_of_gap` derivation (correctly chains the gap fields to `R3NSForms`; proof body is the only outstanding obligation once `ConvectionGap` is discharged).

### Secondary deliverable assessment

The issue instructions authorize proving ONE of `schwartz_dense` or `b_cont_fixedTest`
**only if the gate confirms it is honest and reachable from existing lemmas.** The gate
confirms: **neither is reachable now** without the Helmholtz/Weyl density frontier. No
attempt at a sorry-free proof is made here, consistent with the instruction to leave a
frontier report instead.

The next step for this issue is:
1. Accept `CurlSchwartzDense` as a marked axiom (orchestrator decision per `SchwartzDivFreeBasis.lean:87–88`), which would discharge `schwartz_dense` conditionally.
2. With `schwartz_dense` in hand, `b_cont_fixedTest` becomes provable for the *Schwartz-level restriction* (the extension to L²×L² at fixed Schwartz w follows from the proved bound + density).
3. With both, `ConvectionGap` becomes dischargeable, and `R3NSForms_of_gap` wires everything to `r3_NSForms_exist`.
