# Task Contract: Issue #48 — Discharge `r3_NSForms_exist`

**Plan author:** lean-planner  
**Date:** 2026-06-23  
**Source files read:** `LerayHopf/R3/AxiomaticClosure.lean` (lines 231–301, the axiom and `R3NSForms` structure), `LerayHopf/R3/ConvectionForm.lean` (the already-built `ConvectionGap` + `R3NSForms_of_gap`), `LerayHopf/R3/ConvectionOperator.lean` (Tier-S `convFormSchwartz_*` lemmas, all discharged), `LerayHopf/R3/TrilinearEstimate.lean` (R3-d multilinearity + IBP + bound, all discharged), `LerayHopf/R3/DivergenceFree.lean` (`convIntegralSchwartz`, `L2Sigma_R3`), `LerayHopf/R3/SchwartzDivFreeBasis.lean` (`curlSchwartzDense_holds`).

---

## 1. Current state of the axiom

```
axiom r3_NSForms_exist (𝔊 : R3GalerkinScheme) : Nonempty (R3NSForms 𝔊)
-- ALLOW_AXIOM: ℝ³ NS convection form b exists ...
```

Located in `LerayHopf/R3/AxiomaticClosure.lean` at line 300. Its `ALLOW_AXIOM` justification already describes the correct witness and outlines why each `R3NSForms` field is true.

**The twist:** `ConvectionForm.lean` (file already committed to `main`) already contains:

1. `ConvectionGap 𝔊` — a structure isolating the genuine Mathlib-absent residual behind `r3_NSForms_exist`; specifically: a total `b`, `b_extends` (restricts to `convFormSchwartz`), `b_multilinear` (trilinear witness `B : L2Sigma_R3 →ₗ[ℝ] L2Sigma_R3 →ₗ[ℝ] L2Sigma_R3 →ₗ[ℝ] ℝ`), `b_antisymm_gap` (antisymmetry over all `L²_σ`), `b_cont_fixedTest` (joint slot-1,2 continuity at fixed Schwartz `w`), and `schwartz_dense` (density of `IsSchwartzDivFree_R3` in `L2Sigma_R3`).

2. `R3NSForms_of_gap (𝔊 : R3GalerkinScheme) (g : ConvectionGap 𝔊) : Nonempty (R3NSForms 𝔊)` — a sorry-free conditional proof that `ConvectionGap 𝔊 → Nonempty (R3NSForms 𝔊)`, discharging every `R3NSForms` field from the gap fields.

**Therefore:** The "discharge" question for issue #48 reduces entirely to: _can we construct a `ConvectionGap 𝔊` instance without any new axiom?_

---

## 2. What `ConvectionGap 𝔊` requires: field-by-field analysis

### Field 1: `b : L2Sigma_R3 → L2Sigma_R3 → L2Sigma_R3 → ℝ`

A total function definition. Must be given explicitly as a candidate form.

**Candidate:** Define `b u v w` via density approximation — take Schwartz approximating sequences `(su n)` and `(sv n)` and `(sw n)` (from `schwartz_dense`), and set `b u v w = lim_n convFormSchwartz (su n) (sv n) (sw n)`. However this requires:
- Showing the limit exists (i.e., the sequence is Cauchy/convergent in ℝ).
- Showing the limit is independent of the approximating sequences.

Both of these require `b_cont_fixedTest` (for well-definedness in slots 1,2) but the third-slot extension is harder: `convFormSchwartz` is not bounded in L² at all in slot 3 (no L²×L²×L² bound exists — this is the fundamental difficulty stated in `ConvectionForm.lean`).

**Conclusion:** We cannot define `b` by density extension to all three slots from `convFormSchwartz`. The third-slot extension is genuinely unavailable.

**Alternative:** Define `b` using the IBP-form `b u v w = -∫ (u·∇w)·v`. For Schwartz triples this equals `convFormSchwartz u v w` by the C2 antisymmetry. But extending this to arbitrary `L²_σ` requires `(u·∇)w` to be a well-defined `L²` element when `u ∈ L²_σ` and `w ∈ L²_σ` — this is the weak-`(u·∇)v` operator on `Lp` that `ConvectionForm.lean` explicitly identifies as the Mathlib-absent frontier.

**Verdict on `b`:** No way to define a total `b` on `L²_σ(ℝ³) × L²_σ(ℝ³) × L²_σ(ℝ³)` from currently available Mathlib primitives without asserting the existence of the weak convection operator.

### Field 2: `b_extends : b u v w = convFormSchwartz u v w` for `IsSchwartzDivFree_R3` triples

Depends on the definition of `b`. If `b` is defined by restriction from the weak operator, this is immediate. But we have no weak operator.

### Field 3: `b_multilinear` — trilinear witness `B : L2Sigma_R3 →ₗ[ℝ] L2Sigma_R3 →ₗ[ℝ] L2Sigma_R3 →ₗ[ℝ] ℝ`

A linear map tower. Requires a well-defined `b` with the algebraic structure. The trilinearity of `b` over arbitrary `L²_σ` — not just Schwartz fields — is exactly the algebraic content of the missing weak convection operator. `ConvectionForm.lean` explicitly labels this as the "explicitly asserted residual of the missing operator."

**Mathlib gap:** `Mathlib.MeasureTheory.Function.L2Space` and `Mathlib.Analysis.Distribution.SchwartzSpace` do not contain a construction of the weak convection operator `(u·∇)v` as an `L^p` element for general `L^p` inputs.

### Field 4: `b_antisymm_gap : ∀ u v w, b u v w = -b u w v` for all `L²_σ`

Antisymmetry over arbitrary `L²_σ` is a consequence of integration by parts + `div u = 0`. For Schwartz triples this is `convFormSchwartz_antisymm` (already proved). For general `L²_σ` triples, this requires the distributional IBP for the weak convection operator — again the missing Mathlib primitive.

### Field 5: `b_cont_fixedTest : Continuous ((u,v) ↦ b u v w)` for fixed Schwartz `w`

This is the TRUE continuity (distinct from the false all-three-slot claim). For fixed Schwartz `w` with `IsSchwartzDivFree_R3 w`, `b(u,v,w) = -∫(u·∇)w·v` (by antisymmetry), and since `∇w ∈ L∞`, the bound `|b u v w| ≤ ‖∇w‖_∞ · ‖u‖ · ‖v‖` shows bounded bilinearity in slots 1,2. This is the content of `convFormSchwartz_bound` (already proved for Schwartz `u,v`). The extension to all `L²_σ(u,v)` at fixed Schwartz `w` requires the total extension `b`.

**If `b` were defined:** `b_cont_fixedTest` would follow from `convFormSchwartz_bound` (Tier S, already proved) by a bounded-bilinear continuity argument using `schwartz_dense`. This is actually carried out in `R3NSForms_of_gap`'s `b_bound` case — which goes: use `convFormSchwartz_bound` + `b_cont_fixedTest` + `schwartz_dense` → `b_bound`. So `b_cont_fixedTest` and `b_bound` are logically equivalent in strength. If one is known, the other follows.

### Field 6: `schwartz_dense : ∀ u : L2Sigma_R3, ∃ s : ℕ → L2Sigma_R3, (∀ n, IsSchwartzDivFree_R3 (s n)) ∧ Filter.Tendsto s atTop (nhds u)`

This is the density of `IsSchwartzDivFree_R3` in `L2Sigma_R3`. It is NOT proved in the codebase. It is precisely what `CurlSchwartzDense` (in `SchwartzDivFreeBasis.lean`) would give, via the curl-dense route. The existing axiom `curlSchwartzDense_holds : CurlSchwartzDense` asserts that the Schwartz-curl fields are dense in `L2Sigma_R3`. The Schwartz-curl fields are a subset of `IsSchwartzDivFree_R3` fields (curl of a Schwartz potential has Schwartz components), so `curlSchwartzDense_holds` implies `schwartz_dense`.

**Mathlib path:** `curlSchwartzDense_holds` → each `u ∈ L2Sigma_R3` is an L²-limit of Schwartz-curl fields → those fields are `IsSchwartzDivFree_R3` → `schwartz_dense` holds.

**This field is the ONE field of `ConvectionGap` that can be discharged from existing axioms.**

---

## 3. Summary of gap analysis

| `ConvectionGap` field | Status | Blocker if not proved |
|---|---|---|
| `b` (total form definition) | **Genuine residual** | Mathlib lacks weak `(u·∇)v` on `L^p` |
| `b_extends` | **Genuine residual** (depends on `b`) | Same |
| `b_multilinear` | **Genuine residual** | Algebraic face of the missing weak operator |
| `b_antisymm_gap` | **Genuine residual** | IBP for weak convection operator over all `L²_σ` |
| `b_cont_fixedTest` | **Genuine residual** (depends on `b`) | Needs `b` total |
| `schwartz_dense` | **Provable from `curlSchwartzDense_holds`** | No blocker — MATHLIB-PROVABLE |

---

## 4. Verdict

**Full removal of `r3_NSForms_exist` in one PR: NOT REACHABLE.**

The five genuinely residual fields of `ConvectionGap` collectively encode the existence of a total weak convection operator `b : L2Sigma_R3 →ₗ[ℝ] L2Sigma_R3 →ₗ[ℝ] L2Sigma_R3 →ₗ[ℝ] ℝ` continuous in the first two slots at a fixed Schwartz test. Mathlib (as of `leanprover/mathlib4` current) does not contain:

- A weak `(u·∇)v` operator on `L^p(ℝ³;ℝ³)` for `p = 2`.
- Integration by parts for `L^2` vector fields in the distributional sense beyond Schwartz test functions.
- A bounded bilinear extension theorem that works in this topological setting.

The missing primitive is specifically the construction of a continuous bilinear form on `L²_σ × L²_σ` at fixed Schwartz test (i.e., the embedding `L²_σ × L²_σ ↪ ℝ` induced by each `w ∈ IsSchwartzDivFree_R3`). Without this, there is no `b`.

**`r3_NSForms_exist` is a genuine analytic residual.** The `ConvectionGap` structure in `ConvectionForm.lean` already represents the thinnest possible isolate: the proof `R3NSForms_of_gap` is sorry-free, meaning all algebraic content has been extracted into proved theorems; only the operator-extension content remains.

---

## 5. What #48 can achieve: a partial discharge of `schwartz_dense`

The one dischargeable field is `schwartz_dense`. This can be extracted into a standalone lemma:

### P1 (must-prove): `schwartzDivFree_dense_of_curlDense`

**File:** `LerayHopf/R3/ConvectionForm.lean` (add after `ConvectionGap` structure, before `R3NSForms_of_gap`)

**Signature:**
```lean
theorem schwartzDivFree_dense_of_curlDense
    (h : CurlSchwartzDense) (u : L2Sigma_R3) :
    ∃ s : ℕ → L2Sigma_R3, (∀ n, IsSchwartzDivFree_R3 (s n)) ∧
      Filter.Tendsto s Filter.atTop (nhds u)
```

**Proof path:** From `CurlSchwartzDense` (which equals `L2Sigma_R3 ≤ (Submodule.span ℝ (Set.range curlSchwartzL2)).topologicalClosure`), every `u ∈ L2Sigma_R3` is a limit of finite linear combinations of `curlSchwartzL2 ψ` elements. Each `curlSchwartzL2 ψ` has Schwartz components (its components are `lineDerivOpCLM` applied to Schwartz functions, which are Schwartz by `SchwartzMap.lineDerivOpCLM`). A finite linear combination of `IsSchwartzDivFree_R3` fields is again `IsSchwartzDivFree_R3` (Schwartz class is closed under addition and scalar multiplication). So the approximating sequence witnessing density is `IsSchwartzDivFree_R3`.

**Mathlib lemmas needed:**
- `Submodule.topologicalClosure_le_iff` or `mem_closure_iff_seq_limit` for `ℝ`-modules.
- `curlSchwartzL2_mem_sigma` (already proved in `SchwartzDivFreeBasis.lean`): `curlSchwartzL2 ψ ∈ L2Sigma_R3`.
- `curlSchwartzL2_projComponent` (from `SchwartzDivFreeBasis.lean`): the component structure.
- `SchwartzMap.lineDerivOpCLM` (already available via `Mathlib.Analysis.Distribution.SchwartzSpace.Deriv`): the partial derivative of a Schwartz function is Schwartz.
- `IsSchwartzDivFree_R3` is closed under finite linear combinations — this is a small lemma.

**Difficulty:** Medium. The density transfer from `CurlSchwartzDense` to `schwartz_dense`-for-L2Sigma involves unrolling the `Submodule.topologicalClosure` definition and constructing the approximating sequence explicitly, combined with showing the closure of `IsSchwartzDivFree_R3` under linear span. Requires care with `Subtype` vs `L2VF_R3` coercions. **This is the recommended first task for `lean-coder`.**

### P2 (scaffold-only): `convectionGap_schwartz_dense_field`

An intermediate packaging lemma extracting the proved `schwartz_dense` for eventual assembly into `ConvectionGap`:

```lean
-- scaffold-only: used once b, b_extends, b_multilinear, b_antisymm_gap, b_cont_fixedTest are available
lemma convectionGap_schwartz_dense (h : CurlSchwartzDense) :
    ∀ (u : L2Sigma_R3),
    ∃ s : ℕ → L2Sigma_R3, (∀ n, IsSchwartzDivFree_R3 (s n)) ∧
      Filter.Tendsto s Filter.atTop (nhds u) :=
  fun u => schwartzDivFree_dense_of_curlDense h u
```

This is definitionally equal to P1; useful as a named entry point for future `ConvectionGap` instance construction.

---

## 6. The thinnest possible residual as a clean general statement

The genuine irreducible content behind `r3_NSForms_exist` — after stripping everything that is already proved (trilinearity on Schwartz class, IBP, `b_bound` for Schwartz triples, antisymmetry for Schwartz triples, density) — is the following:

### Candidate thin axiom (for future use; do NOT add in #48)

```lean
-- CandidateThinAxiom (NOT to be added in this PR):
-- axiom r3_weakConvectionOperator_exists :
--   ∃ B : L2Sigma_R3 →ₗ[ℝ] L2Sigma_R3 →ₗ[ℝ] L2Sigma_R3 →ₗ[ℝ] ℝ,
--   (∀ u v w, IsSchwartzDivFree_R3 u → IsSchwartzDivFree_R3 v →
--     IsSchwartzDivFree_R3 w → B u v w = convFormSchwartz u v w hu hv hw) ∧
--   (∀ u v w, B u v w = - B u w v) ∧
--   (∀ w, IsSchwartzDivFree_R3 w →
--     ∃ C, ∀ u v, |B u v w| ≤ C * ‖(u : L2VF_R3)‖ * ‖(v : L2VF_R3)‖)
```

This is the mathematically precise statement of the missing bounded trilinear extension theorem for the ℝ³ convection form, with no over-strength. It combines the operator-extension content and the antisymmetry into one statement, avoiding the false all-three-slot continuity removed in Round 3.

**No-overclaim check:** This does not assert Leray–Hopf existence, a global solution, or any regularity beyond the bounded bilinear nature. It is mathematically TRUE (Temam II.§1, Lemarié-Rieusset §5) and blocked only by the missing weak-operator Mathlib API.

**However:** `ConvectionGap` already encodes exactly this content across its fields `b`, `b_multilinear`, `b_antisymm_gap`, and `b_cont_fixedTest`. Adding a new axiom in #48 would be redundant with the existing `ConvectionGap`-mediated route.

**Recommendation:** Do NOT add a new axiom for #48. The `ConvectionGap` structure is already the minimal interface. Issue #48 should be scoped as a partial discharge (proving `schwartz_dense` from `curlSchwartzDense_holds`) plus documentation of the remaining gap.

---

## 7. Ordered task list

### Files to touch

1. `LerayHopf/R3/ConvectionForm.lean` — add `schwartzDivFree_dense_of_curlDense` (P1, must-prove) and `convectionGap_schwartz_dense` (P2, scaffold). Imports: already imports `ConvectionOperator.lean` and `AxiomaticClosure.lean`; needs to also import `SchwartzDivFreeBasis.lean` for `CurlSchwartzDense` and `curlSchwartzDense_holds`.

   **Import DAG check:** `SchwartzDivFreeBasis.lean` imports `GalerkinScheme.lean` which imports `AxiomaticClosure.lean` which imports... check for cycles. `ConvectionForm.lean` currently imports `AxiomaticClosure.lean`. `SchwartzDivFreeBasis.lean` imports `GalerkinScheme.lean` which imports `AxiomaticClosure.lean`. So the chain is: `DivergenceFree.lean → AxiomaticClosure.lean → GalerkinScheme.lean → SchwartzDivFreeBasis.lean`. `ConvectionForm.lean` already imports `AxiomaticClosure.lean`. Adding `import LerayHopf.R3.SchwartzDivFreeBasis` to `ConvectionForm.lean` would create a potential cycle IF `SchwartzDivFreeBasis.lean` imports `ConvectionForm.lean` — it does not (it imports `GalerkinScheme.lean` only). So the import is safe.

2. **No other files require editing for #48's reachable scope.**

### Declarations

| # | Name | File | Type | Status |
|---|---|---|---|---|
| H1 | `isSchwartzDivFree_add` | `ConvectionForm.lean` | `theorem` (helper) | **must-prove** |
| H2 | `isSchwartzDivFree_smul` | `ConvectionForm.lean` | `theorem` (helper) | **must-prove** |
| H3 | `isSchwartzDivFree_linearCombination` | `ConvectionForm.lean` | `theorem` (helper) | **must-prove** |
| H4 | `curlSchwartzL2_isSchwartzDivFree_R3` | `ConvectionForm.lean` | `theorem` | **must-prove** |
| P1 | `schwartzDivFree_dense_of_curlDense` | `ConvectionForm.lean` | `theorem` | **must-prove** |
| P2 | `convectionGap_schwartz_dense` | `ConvectionForm.lean` | `lemma` | **scaffold-only** |

**Dependency order:** H1 → H3, H2 → H3, H4 → P1, H3 → P1, `curlSchwartzDense_holds` (existing axiom) → P1 (applied), P1 → P2.

### Signatures (informal)

```lean
-- H1
theorem isSchwartzDivFree_add (u v : L2Sigma_R3)
    (hu : IsSchwartzDivFree_R3 u) (hv : IsSchwartzDivFree_R3 v) :
    IsSchwartzDivFree_R3 (u + v)

-- H2
theorem isSchwartzDivFree_smul (c : ℝ) (u : L2Sigma_R3)
    (hu : IsSchwartzDivFree_R3 u) :
    IsSchwartzDivFree_R3 (c • u)

-- H3
theorem isSchwartzDivFree_linearCombination (s : Finset ι) (f : ι → ℝ) (v : ι → L2Sigma_R3)
    (hv : ∀ i ∈ s, IsSchwartzDivFree_R3 (v i)) :
    IsSchwartzDivFree_R3 (∑ i ∈ s, f i • v i)

-- H4 (may already follow from SchwartzDivFreeBasis; check before coding)
theorem curlSchwartzL2_isSchwartzDivFree_R3 (ψ : Fin 3 → SchwartzMap Domain3 ℝ) :
    IsSchwartzDivFree_R3 ⟨curlSchwartzL2 ψ, curlSchwartzL2_mem_sigma ψ⟩

-- P1 (the main deliverable)
theorem schwartzDivFree_dense_of_curlDense
    (h : CurlSchwartzDense) (u : L2Sigma_R3) :
    ∃ s : ℕ → L2Sigma_R3, (∀ n, IsSchwartzDivFree_R3 (s n)) ∧
      Filter.Tendsto s Filter.atTop (nhds u)

-- P2 (scaffold-only packaging for future ConvectionGap construction)
lemma convectionGap_schwartz_dense (h : CurlSchwartzDense) :
    ∀ (u : L2Sigma_R3),
    ∃ s : ℕ → L2Sigma_R3, (∀ n, IsSchwartzDivFree_R3 (s n)) ∧
      Filter.Tendsto s Filter.atTop (nhds u) :=
  fun u => schwartzDivFree_dense_of_curlDense h u
```

---

## 8. Dependency edges

```
LerayHopf/R3/DivergenceFree.lean
  → LerayHopf/R3/Regularity.lean         (IsSchwartzDivFree_R3)
  → LerayHopf/R3/AxiomaticClosure.lean   (R3NSForms, R3GalerkinScheme)
    → LerayHopf/R3/GalerkinScheme.lean   (SchwartzGalerkinBasis)
      → LerayHopf/R3/SchwartzDivFreeBasis.lean
          (CurlSchwartzDense, curlSchwartzL2, curlSchwartzL2_mem_sigma,
           curlSchwartzDense_holds)
  → LerayHopf/R3/ConvectionOperator.lean  (Tier S: convFormSchwartz_*)
    → LerayHopf/R3/ConvectionForm.lean    [EDIT TARGET]
        (ConvectionGap, R3NSForms_of_gap)
        + NEW: H1, H2, H3, H4, P1, P2
```

`ConvectionForm.lean` must add `import LerayHopf.R3.SchwartzDivFreeBasis`.

---

## 9. Assumptions to package

No new `axiom` is added in this PR. The one existing axiom used is `curlSchwartzDense_holds` (already in `SchwartzDivFreeBasis.lean`), applied to prove P1.

---

## 10. Codex review points

Before proofs are attempted:

1. **P1 statement** (`schwartzDivFree_dense_of_curlDense`): Request adversarial review to verify (a) the statement faithfully encodes "density of `IsSchwartzDivFree_R3` in `L2Sigma_R3`" — not a weaker claim; (b) that `CurlSchwartzDense` as defined in `SchwartzDivFreeBasis.lean` does imply this (i.e., Schwartz-curl fields are a subset of `IsSchwartzDivFree_R3` fields).

2. **H4 statement** (`curlSchwartzL2_isSchwartzDivFree_R3`): Verify the `L2Sigma_R3` subtype coercion is correct — that `⟨curlSchwartzL2 ψ, curlSchwartzL2_mem_sigma ψ⟩` compiles as an element of `L2Sigma_R3` and that `IsSchwartzDivFree_R3` is correctly stated about it.

3. **Import DAG**: Verify adding `import LerayHopf.R3.SchwartzDivFreeBasis` to `ConvectionForm.lean` does not create a cycle. (Spot-check: `SchwartzDivFreeBasis.lean` must not transitively import `ConvectionForm.lean`.)

---

## 11. Definition of done for #48

**Minimum (partial discharge):**
- `schwartzDivFree_dense_of_curlDense` is sorry-free.
- `isSchwartzDivFree_add`, `isSchwartzDivFree_smul`, `isSchwartzDivFree_linearCombination`, `curlSchwartzL2_isSchwartzDivFree_R3` are sorry-free.
- `lake build` passes.
- No new `axiom` added.
- `r3_NSForms_exist` stays (not removed); the PR reduces the _total_ content it must cover by formally proving the density subclaim.

**Full discharge:** NOT achievable in one PR without Mathlib's weak convection operator. The PR's honest scope is the density lemma.

**Axiom count:** Unchanged from 5 (ℝ³ layer): `curlSchwartzDense_holds`, `r3_NSForms_exist`, `galerkin_limit_passage_R3`, `galerkin_spacetime_precompact_R3`, `galerkin_weakLimit_R3`.

---

## 12. Hardest step

The hardest single step is **P1** (`schwartzDivFree_dense_of_curlDense`). The challenge is unwrapping `CurlSchwartzDense` (a `Submodule ≤ topologicalClosure` statement) into a sequential density argument, while managing the `L2Sigma_R3` subtype coercions and verifying that finite linear combinations of Schwartz-curl fields remain `IsSchwartzDivFree_R3`.

The required Mathlib API survey before coding P1:
- `Submodule.mem_topologicalClosure_iff` or `mem_closure_iff_seq_limit` for `ℝ`-modules.
- Whether `topologicalClosure` of a `Submodule` has a `mem_iff_seq_limit` characterization (it does via `TopologicalSpace.mem_closure_iff_seq_limit` in `Mathlib.Topology.Order.Basic` or `Mathlib.Topology.Bases`).
- `L2Sigma_R3.coe_add`, `L2Sigma_R3.coe_smul` (coercion behavior in the submodule).

---

## Report

**Contract file:** `/workspaces/lean-pde/docs/scratch/r3-48-nsforms-plan.md`

**Ordered declaration list** (dependency order):
1. `isSchwartzDivFree_add` (H1) — must-prove helper
2. `isSchwartzDivFree_smul` (H2) — must-prove helper
3. `isSchwartzDivFree_linearCombination` (H3) — must-prove helper (depends H1, H2)
4. `curlSchwartzL2_isSchwartzDivFree_R3` (H4) — must-prove
5. `schwartzDivFree_dense_of_curlDense` (P1) — must-prove (depends H3, H4, `curlSchwartzDense_holds`)
6. `convectionGap_schwartz_dense` (P2) — scaffold-only wrapper

**Must-prove:** H1, H2, H3, H4, P1.  
**Scaffold-only:** P2.

**Verdict:** Full removal of `r3_NSForms_exist` is NOT reachable in one PR. The five fields `b`, `b_extends`, `b_multilinear`, `b_antisymm_gap`, `b_cont_fixedTest` of `ConvectionGap` collectively constitute the weak convection operator extension, which Mathlib lacks. The one provable sub-claim is `schwartz_dense` (density of `IsSchwartzDivFree_R3` in `L2Sigma_R3`), derivable from the already-axiomatized `curlSchwartzDense_holds`. The `ConvectionGap` structure + `R3NSForms_of_gap` proof in `ConvectionForm.lean` already represent the thinnest possible isolate of the residual — no thinner new axiom can be proposed that is not already encoded there.

**Hardest step:** P1 (`schwartzDivFree_dense_of_curlDense`) — requires the right Mathlib `topologicalClosure`-mem-seq characterization plus `IsSchwartzDivFree_R3` closure under linear combinations. Needs a Mathlib API survey before coding.

**Recommended first task for `lean-coder`:** Add `import LerayHopf.R3.SchwartzDivFreeBasis` to `ConvectionForm.lean` and implement H1 (`isSchwartzDivFree_add`) with proof body. This is the smallest sorry-free leaf and tests that the import chain compiles cleanly before tackling the denser P1.
