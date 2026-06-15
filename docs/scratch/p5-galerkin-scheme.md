# P5 — Galerkin scheme: axiom-free constructive content (`r3GalerkinScheme_exists`)

**Milestone:** `p5-galerkin-scheme`
**Author:** lean-planner
**Status:** task contract (no Lean edited)

## Goal

Substantiate — **axiom-free and sorry-free** — the analytic content of the
`r3GalerkinScheme_exists` axiom (`LerayHopf/R3/AxiomaticClosure.lean:152-153`), by
*constructing* a `R3GalerkinScheme` from a single honest density hypothesis, in a
**new standalone file**.

This follows the **exact R3-d template**
(`LerayHopf/R3/TrilinearEstimate.lean`, commit `6e00fa1`):

- It does **NOT** remove the axiom and does **NOT** import `AxiomaticClosure.lean`.
- `AxiomaticClosure.lean` does **NOT** import the new file.
- The connection is **semantic**, not structural: the new file proves a theorem of the
  shape `(density hypothesis) → Nonempty R3GalerkinScheme`, demonstrating the axiom is
  true modulo one cleanly-isolated classical input.
- `#print axioms` on the deliverable must be clean (only `propext`,
  `Classical.choice`, `Quot.sound`).

## Feasibility verdict

**FEASIBLE-WITH-NOTED-GAPS.** Every field of `R3GalerkinScheme` is constructible from
mathlib's orthogonal-projection API applied to the finite-dimensional spans of a
countable Schwartz div-free family. The **one genuinely hard input** (density of the
span of smooth/Schwartz div-free fields in `L2Sigma_R3` — a Helmholtz/Weyl-lemma fact)
is **isolated as a single hypothesis, not proved and not axiomatized here**. The only
*noted gaps* are minor API-shape risks flagged inline (gating notes G1–G3); none is a
blocker. See "Risks / gating notes".

## Mathlib API verified (paths under `.lake/packages/mathlib/`)

All confirmed present:

- `Submodule.starProjection : (U : Submodule 𝕜 E) → [U.HasOrthogonalProjection] → E →L[𝕜] E`
  (`…/InnerProductSpace/Projection/Basic.lean:185`) — this is `U.subtypeL ∘L U.orthogonalProjectionOnto`,
  i.e. the **self-map** `E →L[ℝ] E`. This is the correct type for `P n : L2VF_R3 →L[ℝ] L2VF_R3`.
- `Submodule.norm_starProjection_apply_le : ‖U.starProjection v‖ ≤ ‖v‖`
  (`…/Projection/Basic.lean:399`) → **`norm_le`**.
- `Submodule.isIdempotentElem_starProjection : IsIdempotentElem U.starProjection`
  (`…/Projection/Basic.lean:287`) → **`idem`** (`P n (P n u) = P n u`; unfold `IsIdempotentElem`
  = `f ∘ f = f`, apply at `u`).
- `Submodule.starProjection_apply_mem : U.starProjection x ∈ U` (`…/Projection/Basic.lean:199`)
  and `Submodule.range_starProjection : U.starProjection.range = U`
  (`…/Projection/Basic.lean:291`) → range ⊆ `U`, used for **`preserves_sigma`** and **`range_schwartz`**.
- `Submodule.starProjection_tendsto_self`
  (`…/Projection/Submodule.lean:146-155`):
  `(U : ι → Submodule) [∀ t, (U t).HasOrthogonalProjection] (hU : Monotone U)
   (x) (hU' : ⊤ ≤ (⨆ t, U t).topologicalClosure) → Tendsto (fun t => (U t).starProjection x) atTop (𝓝 x)`
  → **`tendsto_id`**. This is the engine; it reduces `tendsto_id` to monotonicity + density.
- `Submodule.starProjection_eq_self_iff` (`…/Projection/Basic.lean:279`) — convenience.
- `FiniteDimensional.span_of_finite : Set.Finite A → FiniteDimensional K (Submodule.span K A)`
  (`…/LinearAlgebra/FiniteDimensional/Defs.lean:200`) and
  `FiniteDimensional.span_finset` (ibid:208). A finite span is finite-dimensional, hence
  `CompleteSpace`, hence `HasOrthogonalProjection` via
  `HasOrthogonalProjection.ofCompleteSpace` (`…/Projection/Basic.lean:53`).
- `Submodule.span_induction` (`…/LinearAlgebra/Span/Defs.lean:139`) — propagate the
  "has Schwartz components" predicate through `mem`, `0`, `+`, `•` → **`range_schwartz`**.
- `SchwartzMap.toLpCLM 𝕜 F p μ : 𝓢(E,F) →L[𝕜] Lp F p μ` (`…/SchwartzSpace/Basic.lean:1365`)
  with `toLpCLM_apply : toLpCLM 𝕜 F p μ f = f.toLp p μ` (ibid:1371). **ℝ-linear**, so
  `(c • ψ + ψ').toLp = c • ψ.toLp + ψ'.toLp` is `map_smul`/`map_add` on the CLM. This is
  what makes finite combinations of Schwartz-component data stay Schwartz at the `toLp` level.
- `L2VF_projComponent_R3 j : L2VF_R3 →L[ℝ] Lp ℝ 2 volume` (already in `Domain.lean:66`) — a
  CLM, so it commutes with the finite ℝ-combinations appearing in `range_schwartz`.
- `volume : Measure Domain3` is `HasTemperateGrowth` (noted in `DivergenceFree.lean:56-58`),
  required for `toLp`/`toLpCLM`. `Fact (1 ≤ 2)` is the global ENNReal instance.

**Naming note (deprecation):** `orthogonalProjection` is deprecated since 2026-05-05 in
favor of `orthogonalProjectionOnto`/`starProjection`. Use `starProjection` throughout
(it is the `→L[ℝ] E` self-map, which is the field type we need).

## New file

`LerayHopf/R3/GalerkinScheme.lean`

### Imports
```
import LerayHopf.R3.DivergenceFree   -- L2VF_R3, L2Sigma_R3, L2VF_projComponent_R3, Domain3
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
```
(Do NOT import `AxiomaticClosure.lean`. Justify any addition beyond these.)

### Namespace / opens
```
namespace LerayHopf
open MeasureTheory SchwartzMap
open scoped Topology
```

### DAG position
```
Domain.lean
  └── DivergenceFree.lean   (L2VF_R3, L2Sigma_R3, L2VF_projComponent_R3)
        └── GalerkinScheme.lean   [THIS FILE]
              (standalone; NOT imported by AxiomaticClosure.lean)
```

Note `AxiomaticClosure.lean` already imports `DivergenceFree` (transitively) and defines
`R3GalerkinScheme`. **This file must NOT import `AxiomaticClosure.lean`**, so it cannot
reference the `R3GalerkinScheme` structure by name. Therefore the deliverable is stated
*field-by-field* (D1–D6 below) as standalone lemmas about `starProjection`, plus a final
"assembly readiness" statement (D7) whose conclusion is the conjunction of the six field
properties. This keeps the file standalone exactly as R3-d keeps its lemmas independent
of `R3NSForms`. (If, during review, we decide the semantic link is clearer by *moving*
the structure to `DivergenceFree.lean` and importing it, that is a separate refactor PR —
do not do it here.)

## Hypothesis packaging (the one honest interface)

Mirroring how R3-d isolated its frontier via the bare `hdiv` hypothesis, the density
input is a **bundled `structure`** carrying the basis family together with the three
facts that make it usable. Bundling (vs. bare ∀/∃) is preferred because the basis,
its Schwartz-component witnesses, and the density fact travel together everywhere.

**scaffold-of-interface (a definition, not an assumption):**

```
/-- A countable Schwartz, divergence-free basis family for `L²_σ(ℝ³)` whose finite
spans exhaust `L²_σ(ℝ³)`.  This bundles the single classical input to the Galerkin
construction (existence + density of smooth div-free fields, a Helmholtz/Weyl fact)
WITHOUT proving it: it is a hypothesis, supplied by the caller. -/
structure SchwartzGalerkinBasis where
  /-- The basis vectors, as L² vector fields. -/
  e : ℕ → L2VF_R3
  /-- Each basis vector has Schwartz component representatives. -/
  e_schwartz : ∀ k : ℕ, ∃ ψ : Fin 3 → SchwartzMap Domain3 ℝ,
      ∀ j : Fin 3,
        L2VF_projComponent_R3 j (e k) = (ψ j).toLp 2 (volume : Measure Domain3)
  /-- Each basis vector is (weakly) divergence-free. -/
  e_mem_sigma : ∀ k : ℕ, e k ∈ L2Sigma_R3
  /-- The closure of the union of finite spans is all of `L²_σ(ℝ³)`:
      the basis is total in the divergence-free subspace.  This is the ONE classical
      input (density of smooth div-free fields in weakly-div-free L²_σ). -/
  dense_span :
      (L2Sigma_R3 : Submodule ℝ L2VF_R3) ≤
        (⨆ n : ℕ, Submodule.span ℝ (Set.range (fun k : Fin n => e (k : ℕ)))).topologicalClosure
```

Design notes for `dense_span`:
- The supremum is over **prefix spans** `span{e 0, …, e (n-1)}` so the family is
  automatically **monotone** in `n` (needed by `starProjection_tendsto_self`).
  `Set.range (fun k : Fin n => e k)` is the finite set `{e 0,…,e(n-1)}`; it is `Set.Finite`
  (range of a function from a `Fintype`).
- The honest content is `L2Sigma_R3 ≤ closure(⨆ …)`, i.e. **every div-free field is
  approximable by finite combinations of the basis**. We only need the `≤` direction
  for `tendsto_id` on `u ∈ L2Sigma_R3`. (Gating note G2 below explains the `x : L2VF_R3`
  vs `x ∈ L2Sigma_R3` mismatch and the chosen resolution.)
- This is the minimal honest interface: it asserts existence + totality of a smooth
  div-free basis and **nothing analytic is hidden in a name** (it is literally a density
  statement on a `Submodule`).

## Declarations in dependency order

Let `Vspan : SchwartzGalerkinBasis → ℕ → Submodule ℝ L2VF_R3` abbreviate the prefix
span `fun B n => Submodule.span ℝ (Set.range (fun k : Fin n => B.e k))`.

### S0 (scaffold helper, lean-coder) — `SchwartzGalerkinBasis` structure
As above. **Role:** lean-coder (signature/structure). Pure interface, no proof.

### S1 — `galerkinSpan` (def, lean-coder)
```
/-- Prefix span `span{e 0, …, e (n-1)}` of the basis. -/
noncomputable def galerkinSpan (B : SchwartzGalerkinBasis) (n : ℕ) :
    Submodule ℝ L2VF_R3 :=
  Submodule.span ℝ (Set.range (fun k : Fin n => B.e (k : ℕ)))
```
**Role:** lean-coder. **Deps:** S0.

### S2 — `galerkinSpan_finiteDimensional` (instance/lemma, lean-prover)
```
instance (B) (n) : FiniteDimensional ℝ (galerkinSpan B n)
-- via FiniteDimensional.span_of_finite (Set.finite_range _)
```
**Role:** lean-prover (proof body). **Deps:** S1.
**Mathlib:** `FiniteDimensional.span_of_finite`, `Set.finite_range`.
**Gating note G1:** confirm the instance resolves `HasOrthogonalProjection` downstream
automatically (`CompleteSpace` of finite-dim ⇒ `HasOrthogonalProjection.ofCompleteSpace`).
If instance synthesis does not fire, add an explicit
`instance : (galerkinSpan B n).HasOrthogonalProjection := inferInstance` helper.

### S3 — `galerkinSpan_mono` (lemma, lean-prover)
```
theorem galerkinSpan_mono (B) : Monotone (galerkinSpan B)
-- span is monotone in the generating set; Fin n ⊆ Fin m range for n ≤ m
```
**Role:** lean-prover. **Deps:** S1.
**Mathlib:** `Submodule.span_mono`, `Set.range_subset` between `Fin n`/`Fin m`.

### S4 — `galerkinP` (def, lean-coder) — the projector family
```
/-- The n-th Galerkin projector: orthogonal projection onto `galerkinSpan B n`. -/
noncomputable def galerkinP (B : SchwartzGalerkinBasis) (n : ℕ) :
    L2VF_R3 →L[ℝ] L2VF_R3 :=
  (galerkinSpan B n).starProjection
```
**Role:** lean-coder. **Deps:** S1, S2 (for the `HasOrthogonalProjection` instance).

### D1 — `galerkinP_norm_le` (must-prove, lean-prover) → field `norm_le`
```
theorem galerkinP_norm_le (B) (n) (u : L2VF_R3) : ‖galerkinP B n u‖ ≤ ‖u‖
-- exact: norm_starProjection_apply_le
```

### D2 — `galerkinP_idem` (must-prove, lean-prover) → field `idem`
```
theorem galerkinP_idem (B) (n) (u : L2VF_R3) : galerkinP B n (galerkinP B n u) = galerkinP B n u
-- from isIdempotentElem_starProjection (IsIdempotentElem = self-compose); apply at u
```

### D3 — `galerkinP_mem_span` (helper, lean-prover)
```
theorem galerkinP_mem_span (B) (n) (u) : galerkinP B n u ∈ galerkinSpan B n
-- starProjection_apply_mem
```
Supports D4 and D6.

### D4 — `galerkinP_preserves_sigma` (must-prove, lean-prover) → field `preserves_sigma`
```
theorem galerkinP_preserves_sigma (B) (n) (u) (hu : u ∈ L2Sigma_R3) :
    galerkinP B n u ∈ L2Sigma_R3
```
**Proof sketch:** `galerkinP B n u ∈ galerkinSpan B n` (D3); and
`galerkinSpan B n ≤ L2Sigma_R3` because all generators `B.e k ∈ L2Sigma_R3`
(`B.e_mem_sigma`) and `L2Sigma_R3` is a submodule, so `Submodule.span_le.mpr`. Note the
hypothesis `hu` is **not actually needed** (range is in the span ⊆ Σ regardless) — but
the `R3GalerkinScheme.preserves_sigma` field signature includes it, so keep it for the
assembly statement; discard it in the proof. **No-overclaim check:** keeping an unused
hypothesis is safe; do NOT drop it from the assembly conjunction (would change the
field's type).

### D5 — `galerkinP_tendsto_id` (must-prove, lean-prover) → field `tendsto_id`
```
theorem galerkinP_tendsto_id (B) (u : L2VF_R3) (hu : u ∈ L2Sigma_R3) :
    Filter.Tendsto (fun n => galerkinP B n u) Filter.atTop (𝓝 u)
```
**Proof sketch:** `starProjection_tendsto_self (galerkinSpan B) (galerkinSpan_mono B) u hU'`
where `hU' : ⊤ ≤ (⨆ n, galerkinSpan B n).topologicalClosure`.
**Gating note G2 (the one real subtlety):** `starProjection_tendsto_self` requires
`⊤ ≤ closure(⨆)` (density in the WHOLE space `L2VF_R3`), but `B.dense_span` only gives
density in `L2Sigma_R3` (the physically correct statement — the Galerkin space is NOT
dense in all of L², only in the div-free part). The `R3GalerkinScheme.tendsto_id` field
as currently written is `∀ u : L2VF_R3, …` (ALL u), which is **stronger than true** for
a div-free basis. Resolution options, in order of preference:
  - **(G2-a, recommended)** Prove the honest restricted statement D5 (`hu : u ∈ L2Sigma_R3`)
    here, and **flag for Codex/orchestrator** that the structure field `tendsto_id`'s
    `∀ u : L2VF_R3` quantifier is mathematically too strong for a div-free Galerkin scheme.
    The assembly statement D7 then provides `tendsto_id` only on `L2Sigma_R3`. This means
    D7 establishes the conjunction of the *honest* field properties; the gap between
    "honest tendsto on Σ" and "structure's tendsto on all L²" is a **statement-level
    overclaim in the existing axiom's structure**, which P5 surfaces but does not silently
    paper over (Hard rule 3/6). Record this precisely in the file's assumptions/notes
    section and in the report.
  - (G2-b) If the orchestrator decides the structure field is intended only for div-free
    inputs (the only place `𝔊.P` is applied in `AxiomaticClosure`/`Regularity` is to
    `w : L2Sigma_R3` via `IsGalerkinTest_R3`), then a **follow-up lean-coder PR** should
    weaken the structure field to `∀ u, u ∈ L2Sigma_R3 → Tendsto …`. That is a separate
    PR (touches `AxiomaticClosure.lean`); **out of scope for P5**, which stays standalone.
  - Do NOT prove a false `∀ u : L2VF_R3` statement. If forced, leave the unrestricted
    form as a `-- TODO:` with the precise blocker (basis not total in L²).
**Mathlib:** `starProjection_tendsto_self`; `iSup`/`topologicalClosure` from `B.dense_span`
(note: `dense_span` is `L2Sigma_R3 ≤ closure(⨆)`; combined with `u ∈ L2Sigma_R3` we get
`u ∈ closure(⨆)`, then `starProjection_tendsto_closure_iSup` + `u`'s membership give 𝓝 u).
**Refinement:** D5 may be cleaner via `starProjection_tendsto_closure_iSup` directly
(`…/Projection/Submodule.lean:118`) plus the fact `u ∈ closure(⨆) ⇒ closure-projection u = u`
(`starProjection_eq_self_iff` after `topologicalClosure` `HasOrthogonalProjection`).

### D6 — `galerkinP_range_schwartz` (must-prove, lean-prover) → field `range_schwartz`
```
theorem galerkinP_range_schwartz (B) (n) (u : L2VF_R3) :
    ∃ ψ : Fin 3 → SchwartzMap Domain3 ℝ,
      ∀ j : Fin 3,
        L2VF_projComponent_R3 j (galerkinP B n u) = (ψ j).toLp 2 (volume : Measure Domain3)
```
**Proof sketch (the technically richest, mirrors R3-d's tiered helpers):**
1. `galerkinP B n u ∈ galerkinSpan B n` (D3).
2. Define the predicate `HasSchwartzComponents (v : L2VF_R3) : Prop :=`
   `∃ ψ : Fin 3 → 𝓢, ∀ j, L2VF_projComponent_R3 j v = (ψ j).toLp 2 volume`.
3. Prove `HasSchwartzComponents` is preserved under `0`, `+`, `• (c : ℝ)`, and holds on
   generators `B.e k` (`B.e_schwartz`). Then `Submodule.span_induction` over membership
   in `galerkinSpan B n` gives `HasSchwartzComponents (galerkinP B n u)`.
   - **0:** components are `0 = (0 : 𝓢).toLp` (use `map_zero` of `L2VF_projComponent_R3`
     and `toLpCLM`).
   - **+:** components add; `(ψ j).toLp + (ψ' j).toLp = (ψ j + ψ' j).toLp` by
     `map_add (toLpCLM ℝ ℝ 2 volume)`; Schwartz closed under `+`.
   - **• c:** `c • (ψ j).toLp = (c • ψ j).toLp` by `map_smul (toLpCLM …)`; Schwartz module.
   - uses linearity of `L2VF_projComponent_R3 j` (`map_add`, `map_smul`, `map_zero` — it
     is a CLM) to push the projection through the combination.
**Private helpers (lean-coder may scaffold signatures; lean-prover fills):** one helper
per closure property (`hasSchwartzComponents_zero/add/smul/of_basis`), matching R3-d's
private-helper pattern. **No vector-valued Schwartz construction is needed** — the proof
stays entirely at the `L2VF_projComponent_R3 j (·) = (· ).toLp` level, exactly as
`IsSchwartzDivFree_R3` (`Regularity.lean:83`) is phrased.
**Gating note G3:** confirm `toLpCLM ℝ ℝ 2 (volume : Measure Domain3)` typechecks for the
**scalar** target `F = ℝ` (it should: `toLpCLM 𝕜 F p μ`). If `map_smul` over `ℝ` needs the
`𝕜 = ℝ` slot explicitly, supply it. Also confirm `Submodule.span_induction`'s motive
signature `(x) → x ∈ span → Prop` accepts the `HasSchwartzComponents` motive without the
membership argument (it is allowed to ignore it).

### D7 — `nonempty_r3GalerkinScheme_of_basis` (must-prove, lean-prover) — DELIVERABLE
**Because this file does not import `AxiomaticClosure`, it cannot mention
`R3GalerkinScheme` or `Nonempty R3GalerkinScheme` by name.** The deliverable is the
**conjunction of the six honest field properties**, stated standalone:

```
/-- **Deliverable (P5).** From a total Schwartz divergence-free basis, the orthogonal
projections onto its finite prefix spans form a Galerkin approximation scheme on
`L²_σ(ℝ³)`: they are non-expansive, idempotent, preserve the divergence-free subspace,
have component-wise Schwartz range, and converge strongly to the identity on
`L²_σ(ℝ³)`.  This is the axiom-free constructive content of `r3GalerkinScheme_exists`
(modulo the bundled density hypothesis `B.dense_span`). -/
theorem galerkinScheme_properties_of_basis (B : SchwartzGalerkinBasis) :
    (∀ n u, u ∈ L2Sigma_R3 → galerkinP B n u ∈ L2Sigma_R3)            -- preserves_sigma
  ∧ (∀ u, u ∈ L2Sigma_R3 →
        Filter.Tendsto (fun n => galerkinP B n u) Filter.atTop (𝓝 u)) -- tendsto_id (honest, on Σ)
  ∧ (∀ n u, ‖galerkinP B n u‖ ≤ ‖u‖)                                  -- norm_le
  ∧ (∀ n u, galerkinP B n (galerkinP B n u) = galerkinP B n u)        -- idem
  ∧ (∀ n u, ∃ ψ : Fin 3 → SchwartzMap Domain3 ℝ, ∀ j,
        L2VF_projComponent_R3 j (galerkinP B n u) = (ψ j).toLp 2 (volume : Measure Domain3))
  := ⟨D4, D5, D1, D2, D6⟩
```
**Role:** lean-prover (assembles D1–D6). **Deps:** D1–D6.
**Naming:** `galerkinScheme_properties_of_basis` — describes exactly what is proved
(no overclaim term; "scheme properties", not "scheme exists", since the unrestricted
`tendsto_id` field is intentionally NOT claimed; see G2).

**Optional D7' (only if orchestrator approves moving the structure):** If a *separate*
PR moves `R3GalerkinScheme` into `DivergenceFree.lean` (and weakens `tendsto_id` to Σ per
G2-b), then a `nonempty_r3GalerkinScheme_of_basis (B) : Nonempty R3GalerkinScheme` becomes
statable. **Out of scope for P5.** Do not attempt under the standalone constraint.

## lean-coder vs lean-prover split

- **lean-coder** (signatures, defs, structure, imports, helper *statements*):
  S0 (`SchwartzGalerkinBasis`), S1 (`galerkinSpan`), S4 (`galerkinP`), the `private`
  predicate `HasSchwartzComponents` and the four closure-helper *signatures* for D6, and
  all theorem *statements* D1–D7. lean-coder lands these compiling with `-- ALLOW_SORRY:`
  placeholders on each proof body.
- **lean-prover** (proof bodies only): S2, S3, D1–D7 and the four D6 helpers.

## Assumptions / axioms section

**NO new `axiom`, `opaque`, `constant`, or `unsafe`.** Zero.

The single classical input (density of smooth/Schwartz divergence-free fields in
weakly-divergence-free `L²_σ(ℝ³)` — a Helmholtz/Weyl-lemma fact) is carried as the
**hypothesis field `SchwartzGalerkinBasis.dense_span`**, supplied by the caller. It is a
`Submodule` inequality, not an assumption baked into the environment. This is the honest
analogue of R3-d's `hdiv` hypothesis.

**Statement-level note to record in the file header (per G2):** the existing
`R3GalerkinScheme.tendsto_id` field quantifies over *all* `u : L2VF_R3`; that is
mathematically too strong for a divergence-free Galerkin basis (which is total only in
`L2Sigma_R3`). P5 proves the honest `tendsto_id`-on-`L2Sigma_R3`. Surfacing this is
required by Hard rules 3 and 6; it must appear in the report to the orchestrator as a
recommended follow-up (G2-b) to weaken the structure field.

## Codex review points (`/codex:adversarial-review --effort xhigh`)

Review the **statements** before proofs are attempted:
1. `SchwartzGalerkinBasis` (S0) — especially `dense_span`: is `L2Sigma_R3 ≤ closure(⨆ prefix spans)`
   the correct, minimal, honest density interface? Is the prefix-span/`Fin n` monotonicity
   formulation right? Does it avoid hiding any analytic claim in a name?
2. `galerkinP` (S4) and the `tendsto_id` honest form (D5) — confirm the
   `∀ u : L2VF_R3` vs `u ∈ L2Sigma_R3` analysis (G2) is correct and that proving the
   restricted form is the honest, non-overclaiming choice; confirm we are NOT silently
   weakening a target we were asked to prove (we are surfacing a pre-existing
   structure-field overclaim, not introducing one).
3. `galerkinP_range_schwartz` (D6) — confirm the `span_induction` over `HasSchwartzComponents`
   is sound, that `toLpCLM` linearity correctly transfers Schwartz combinations, and that
   no vector-valued Schwartz construction is silently required.
4. `galerkinScheme_properties_of_basis` (D7) — confirm the six-way conjunction faithfully
   matches the six `R3GalerkinScheme` fields (`AxiomaticClosure.lean:126-150`) up to the
   documented `tendsto_id` restriction, so the semantic link to the axiom is genuine.

## Definition of done

- New file `LerayHopf/R3/GalerkinScheme.lean` compiles (`lake build` green).
- **Must-prove, sorry-free:** D1, D2, D3, D4, D5 (honest Σ form), D6 (+ its 4 helpers),
  D7, and lemmas S2, S3.
- **Interface defs (no proof obligation beyond typechecking):** S0, S1, S4.
- **Zero new axioms / opaque / sorry.** `grep` for `axiom|opaque|sorry|ALLOW_` returns
  nothing in the file.
- `#print axioms galerkinScheme_properties_of_basis` shows only
  `[propext, Classical.choice, Quot.sound]` (R3-d discipline; add the `#print axioms`
  line as a comment-checked sanity, not committed output).
- File does NOT import `AxiomaticClosure.lean`; `AxiomaticClosure.lean` does NOT import it.
- `bash scripts/agent-preflight.sh` green.
- Codex `/codex:adversarial-review --effort xhigh` → approve on statements (points 1–4),
  routed by orchestrator before proof work and again after.
- Report records the G2 `tendsto_id` overclaim finding as a recommended follow-up PR.

## Risks / gating notes (summary)

- **G1** (low): finite-dim ⇒ `HasOrthogonalProjection` instance synthesis for `galerkinP`.
  Mitigation: explicit `inferInstance` helper if needed.
- **G2** (medium, **the one real issue**): structure field `tendsto_id : ∀ u : L2VF_R3`
  is stronger than true for a div-free basis. Resolution: prove honest Σ-restricted D5;
  surface as follow-up; do not prove a false statement, do not silently weaken. Keeps P5
  honest and standalone.
- **G3** (low): `toLpCLM`/`span_induction` motive shapes for scalar `F = ℝ`. Mitigation:
  explicit `𝕜 = ℝ` slots; standard.

## First task to hand to lean-coder

Land `LerayHopf/R3/GalerkinScheme.lean` with: imports, `namespace LerayHopf`/opens, the
structure **S0 `SchwartzGalerkinBasis`**, defs **S1 `galerkinSpan`** and **S4 `galerkinP`**,
the `private` predicate `HasSchwartzComponents`, and the *statements* of S2, S3, D1–D7
(plus D6's four helper signatures), each proof body a marked
`sorry -- ALLOW_SORRY: P5 lean-prover target` so the file compiles. Then hand to Codex
(review points 1–4), then to lean-prover for proofs in order S2 → S3 → D1 → D2 → D3 →
D4 → D6 (+helpers) → D5 → D7.

---

## ADDENDUM — Resolution decision (orchestrator, post Codex gate-1)

**Codex gate-1 verdict: needs-attention.** G2 confirmed real (a div-free basis's
prefix-span projections land in the closed subspace `L2Sigma_R3`, so unrestricted
`tendsto_id` would force every `u` div-free — contradiction). **User decision: Option 1
— weaken the field, then witness.** This SUPERSEDES the standalone constraint and the
honest-partial D7 framing below where they conflict.

Verified before deciding: `R3GalerkinScheme.tendsto_id` is **never mechanically consumed**
in proof code (only the field decl at `AxiomaticClosure.lean:132` + prose at lines
118/162/459); every application of `𝔊.P` in the closure is on **divergence-free** data
(`IsGalerkinTest_R3`, `u_inVn`, initial trace at `u₀ ∈ L2Sigma_R3`). The unrestricted
quantifier is strictly stronger than the Leray–Hopf assembly needs.

Scope changes vs. the original plan:

1. **AxiomaticClosure.lean edit (lean-coder).** Weaken the field
   `tendsto_id : ∀ (u : L2VF_R3), Filter.Tendsto (fun n => P n u) atTop (nhds u)`
   →
   `tendsto_id : ∀ (u : L2VF_R3), u ∈ L2Sigma_R3 → Filter.Tendsto (fun n => P n u) atTop (nhds u)`.
   This is a SOUNDNESS FIX (removes a latent over-strength), not a weaken-to-pass.
   Update the field docstring (line ~118) and the axiom-justification prose to state the
   Σ-restriction and why (Codex-confirmed: a div-free Galerkin scheme is total only in Σ).
   Fix any construction/use site of this field in the closure (likely none — prose only).

2. **Re-verify the whole ℝ³ closure.** `exists_lerayHopf_r3` must still build and
   `#print axioms exists_lerayHopf_r3` must stay clean (the 6 project axioms +
   propext/Classical.choice/Quot.sound, no sorryAx). Preflight green.

3. **GalerkinScheme.lean now IMPORTS `AxiomaticClosure.lean`** (standalone constraint
   lifted — the deliverable now witnesses the structure). DAG: AxiomaticClosure →
   GalerkinScheme. Confirm NO cycle (AxiomaticClosure must not import GalerkinScheme).
   `SchwartzGalerkinBasis`, `galerkinSpan`, `galerkinP` stay in GalerkinScheme.lean.

4. **New headline deliverable D7' (replaces D7's role).**
   `theorem nonempty_r3GalerkinScheme_of_basis (B : SchwartzGalerkinBasis) :
      Nonempty R3GalerkinScheme`
   built as `⟨{ P := galerkinP B, preserves_sigma := D4, tendsto_id := D5 (Σ-restricted),
   norm_le := D1, idem := D2, range_schwartz := D6 }⟩`. Axiom-free; only input is `B`.
   Keep `galerkinScheme_properties_of_basis` (D7) as a supporting lemma if convenient.
   D5's signature already matches the weakened field exactly.

5. **(Capstone, decide after green + re-audit — do NOT auto-do.)** Optionally convert
   `axiom r3GalerkinScheme_exists : Nonempty R3GalerkinScheme` into a thin
   `axiom schwartzGalerkinBasis_exists : Nonempty SchwartzGalerkinBasis` + proved
   `theorem r3GalerkinScheme_exists : Nonempty R3GalerkinScheme` (via D7'). Converts a
   fat 6-field structure axiom into a thin density axiom + proved construction (same axiom
   count, much thinner frontier). Orchestrator decides after the witness is green.

**Updated definition of done:** closure builds + `#print axioms exists_lerayHopf_r3` clean;
GalerkinScheme.lean sorry-free + zero new axioms; `#print axioms
nonempty_r3GalerkinScheme_of_basis` clean; preflight green; Codex re-review → approve.
