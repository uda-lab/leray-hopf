# Issue #56 — Determined-form construction for `r3ConvectionGapOp_exists` (R3 capstone 3→2)

**Plan author:** lean-planner · **Date:** 2026-06-27 · **Scope:** READ-ONLY planning artifact (this file only).

**Status of this contract.** This SUPERSEDES `docs/scratch/r56-construction-final.md` for the proof
strategy. The prior contract's `b := (BExt_slot3 u v w − BExt_slot3 u w v)/2` (raw 3-slot Hamel) is the
construction **codex refuted in PR #60**: with `w` fixed Schwartz, the swapped term `BExt_slot3 u w v`
feeds the varied slot-2 argument `v` into the **slot-3 Hamel index** of `BExt_slot3`, which is
discontinuous in `v` — so `b_cont_fixedTest` (C9) is false for that object. The current scaffold in
`LerayHopf/R3/ConvectionExtension.lean` (C5 `convFormL2_def`) encodes that refuted object and **must be
revised** (§7).

**The codex-endorsed fix (PR #60 review, verbatim intent):** "use a BLT-valued/determined extension on
fixed-Schwartz slices." This contract gives the concrete Lean encoding of the determined form. The
soundness of the determined route is **already adjudicated** (codex + orchestrator agree); this contract
formalizes it and does **not** re-adjudicate it. Where a genuine mathlib gap exists I give a build-around
(§3, §4) — I do not re-derive the refuted "impossibility."

---

## 0. Ground truth consumed (verbatim merged signatures)

All from `LerayHopf/R3/EnergyClassConvection.lean`, `LerayHopf/R3/DivergenceFree.lean`,
`LerayHopf/R3/Regularity.lean`, `LerayHopf/R3/ConvectionOperator.lean`, `LerayHopf/R3/ConvectionForm.lean`:

- `L2VF_R3` — ambient `L²(ℝ³;ℝ³)`-style space: `NormedAddCommGroup`, `InnerProductSpace ℝ`,
  `CompleteSpace`.
- `L2Sigma_R3 : Submodule ℝ L2VF_R3` (`DivergenceFree.lean:90`), with `instance : CompleteSpace
  L2Sigma_R3`. **Every argument of the structure field `b : L2Sigma_R3 → L2Sigma_R3 → L2Sigma_R3 → ℝ`
  is already div-free** — this is load-bearing (it makes B7 always applicable, §3.3).
- `H1Sigma_R3 : Submodule ℝ L2VF_R3` (`EnergyClassConvection.lean`), `memH1VF_R3 : L2VF_R3 → Prop`.
- `IsSchwartzDivFree_R3 (w : L2Sigma_R3) : Prop` (`Regularity.lean:83`) — `∃ ψ : Fin 3 → 𝓢(Domain3,ℝ),
  ∀ j, L2VF_projComponent_R3 j (w:L2VF_R3) = (ψ j).toLp 2 volume`. Schwartz ⇒ H¹ (the proved-elsewhere
  `memH1VF_R3_of_isSchwartzDivFree`, mirrored privately in the current scaffold as
  `memH1VF_R3_of_schwartz`).
- `convFormH1 (u v w : L2VF_R3) (hu hv hw : memH1VF_R3 …) : ℝ` (`:643`), with merged sorry-free:
  - **B4** `convFormH1_add_{1,2,3}` (`:693/:718/:742`), `convFormH1_smul_{1,2,3}` (`:…/:802`) — trilinear.
  - **B5** `convFormH1_eq_convFormSchwartz` (`:876`) — `= convFormSchwartz` on Schwartz triples (needs the
    three `IsSchwartzDivFree_R3` plus the three `memH1VF_R3`).
  - **B6** `convFormH1_antisymm (u v w) (hu hv hw) (hu_σ hv_σ hw_σ)` (`:2039`), sorry-free:
    `convFormH1 u v w … = -convFormH1 u w v …`, needs all three `memH1VF_R3` AND all three σ-membership.
  - **B7** `convFormH1_bound_Schwartz (w) (hw_H1) (hw_σ) (hw_sch)` (`:2101`), sorry-free:
    `∃ C_w ≥ 0, ∀ (u v : L2VF_R3) (hu hv : memH1VF_R3 …) (hu_σ hv_σ : … ∈ L2Sigma_R3),
    |convFormH1 u v w hu hv hw_H1| ≤ C_w · ‖(u:L2VF_R3)‖ · ‖(v:L2VF_R3)‖`. **NOTE the σ-membership
    hypotheses `hu_σ hv_σ` — B7 already bounds over the div-free `u,v`, exactly our domain.** This is the
    continuity engine for slots 1,2 at fixed Schwartz `w`.
- **Tier-S** (`ConvectionOperator.lean`): `convFormSchwartz u v w hu hv hw`, `convFormSchwartz_eq_witness`,
  `convFormSchwartz_bound`, `convFormSchwartz_antisymm` — all sorry-free.
- **Density** (`ConvectionForm.lean`): `schwartzDivFree_dense_of_curlDense` /
  `convectionGap_schwartz_dense curlSchwartzDense_holds` — `IsSchwartzDivFree_R3` dense in `L2Sigma_R3`.
- Target `structure ConvectionGapOp (𝔊 : R3GalerkinScheme)` (`ConvectionForm.lean:271`), 5 fields:
  `b`; `b_extends`; `b_multilinear : ∃ B : L2Sigma_R3 →ₗ[ℝ] L2Sigma_R3 →ₗ[ℝ] L2Sigma_R3 →ₗ[ℝ] ℝ,
  ∀ u v w, b u v w = B u v w`; `b_antisymm_gap : ∀ u v w, b u v w = - b u w v`;
  `b_cont_fixedTest : ∀ w, IsSchwartzDivFree_R3 w → Continuous (fun p : L2Sigma_R3 × L2Sigma_R3 =>
  b p.1 p.2 w)`.
- Removal target: `axiom r3ConvectionGapOp_exists (𝔊) : Nonempty (ConvectionGapOp 𝔊)`
  (`ConvectionForm.lean:664`).

**Notation.** `H₁' := H1Sigma'` (the comap `Submodule.comap L2Sigma_R3.subtype H1Sigma_R3 :
Submodule ℝ L2Sigma_R3`, already in the scaffold, C0, sorry-free). For `x : L2Sigma_R3`,
`‖x‖ = ‖(x:L2VF_R3)‖`. `Schw := IsSchwartzDivFree_R3`. `Schw ⊆ H₁'` (Schwartz ⇒ H¹).

---

## 1. The single design decision that dissolves the C9 wall

The refuted object antisymmetrizes a **3-slot Hamel tower**, so the swapped term puts a varied
continuity-slot argument into a Hamel index. The determined object instead reads `b(·,·,w)` for fixed
Schwartz `w` off a **BLT-continuous bilinear form**, and the antisymmetrization is a difference of **two**
BLT forms — both `(u,v)`-continuous because in BOTH terms the Schwartz `w` sits in a B7-controlled test
slot.

The construction has TWO completely separate layers that never interact:

- **ALGEBRAIC layer (for `b_multilinear`, `b_antisymm_gap`, `b_extends`):** a genuine trilinear
  `LinearMap` tower `B : L2Sigma_R3 →ₗ L2Sigma_R3 →ₗ L2Sigma_R3 →ₗ ℝ` obtained by **antisymmetrizing a
  3-slot Hamel tower** `BExt` of `convFormH1`. This layer carries NO continuity claim — it only supplies
  the algebra and the Schwartz-triple agreement. (This is the sound part of the prior scaffold; keep it.)
- **CONTINUITY layer (for `b_cont_fixedTest` ONLY):** for each Schwartz `w`, a continuous bilinear form
  `Bw : L2Sigma_R3 →L[ℝ] L2Sigma_R3 →L[ℝ] ℝ` such that `(u,v) ↦ b u v w = Bw u v` **for all `u,v`**.

The two layers are reconciled by a single must-prove identity (the crux):

> **CRUX `b_eq_BLT_at_schwartz`:** for Schwartz `w` and ALL `u v : L2Sigma_R3`, `b u v w = Bw u v`.

CRUX is proved by **density transfer**, and density transfer is legitimate here because `Bw` is
continuous AND `b(·,·,w)` is *defined to be* `Bw` at Schwartz `w` (we do not need to prove `b(·,·,w)`
continuous independently — we DEFINE the value through `Bw` on the Schwartz-slot-3 case). Concretely,
**`b` is defined by the determined formula `b u v w := (Bw3 w u v − Bw3 v u w)/2`** where `Bw3 s` is the
BLT form attached to a Schwartz `s` extended to all `s` by Hamel **in a way that is irrelevant to
continuity** (continuity is read off the FIRST argument-position which is always the genuine `Bw`, see
§3.4). This is the precise sense in which "the determined value is baked in, not recovered."

The decisive correction over the prior contract: **the antisymmetrization swaps `v ↔ w`, and at fixed
Schwartz `w` BOTH resulting terms have the Schwartz field in the B7-test slot** (first term: `w` is the
test of `Bw`; second term: `w` is the L²-varied slot but paired against the Schwartz... — NO; see §3.3 for
the exact slot bookkeeping that makes BOTH terms B7∘B6-controlled). The must-prove analytic content is
exactly **B7∘B6** (C2 below), nothing Mathlib-absent.

---

## 2. The determined form — abstract model and the Lean route

### 2.1 Abstract model (conceptual; NOT on the Lean critical path)

For fixed `u`, the antisymmetric bilinear `β_u` lives on `D := (Schw⊗L²_σ) + (L²_σ⊗Schw) ⊆
L²_σ ⊗[ℝ] L²_σ`. On `Schw⊗L²_σ`: `β_u(s⊗l) = convFormH1 u s l` (slot-2 Schwartz ⇒ B7-bounded for all
`l`). On `L²_σ⊗Schw`: `β_u(l⊗s) = -convFormH1 u s l = convFormH1 u l s` (B6). Well-defined because the two
agree on `Schw⊗Schw` (B6) and `(Schw⊗L²_σ) ∩ (L²_σ⊗Schw) = Schw⊗Schw` (tensor-intersection). Hamel-extend
`β_u` off `D`; antisymmetric by construction. `b u v w := β_u(v⊗w)`.

### 2.2 GENUINE LEAN OBSTACLE FLAG — tensor-intersection is mathlib-absent; AVOID it

I searched: mathlib has `TensorProduct.map`, `TensorProduct.lift`, `TensorProduct.uncurry`,
`Submodule.map₂`, `TensorProduct.range_mapIncl`, `LinearMap.exists_extend`, `Submodule.exists_isCompl`,
`LinearMap.ofIsCompl`, but **NO** lemma of the form `(P ⊗ B) ⊓ (A ⊗ Q) = P ⊗ Q` as submodules of
`TensorProduct R A B`. Building it requires the complement-split direct-sum decomposition
`A⊗B = P⊗Q ⊕ P⊗Qᶜ ⊕ Pᶜ⊗Q ⊕ Pᶜ⊗Qᶜ` and showing `(P⊗B)` and `(A⊗Q)` are sums of distinct summands — a
multi-hundred-line tensor-algebra development with `TensorProduct.directSum` plumbing.

**BUILD-AROUND (decisive — the Lean construction uses NO tensor products at all).** The tensor model is
only a soundness picture. The **scalar** Lean encoding realizes the SAME determined form via
`Submodule.exists_isCompl` on `H₁' ≤ L2Sigma_R3` plus `LinearMap.ofIsCompl`/`LinearMap.exists_extend`,
operating on the curried `convFormH1` tower. **The tensor-intersection lemma is NOT built and NOT on the
critical path.** §3 gives the tensor-free encoding. This is the single most important build-around: do
**not** attempt the tensor-intersection lemma.

---

## 3. The Lean encoding of `b` (tensor-free, determined)

The encoding keeps the ALGEBRAIC layer of the existing scaffold (C0,C1,C5-algebra,C6,C7,C8 — sound) and
REPLACES the continuity-relevant definition so that `b(·,·,w)` at Schwartz `w` is a difference of two BLT
forms. Concretely we **do NOT change `convFormL2_def`'s algebraic shape**; we change WHICH object
`BExt_slot3` is, so that its restriction to Schwartz slot-3 is the genuine BLT form.

### 3.0 Keep (sound, already in scaffold or merged)

- **C0** `H1Sigma' : Submodule ℝ L2Sigma_R3 := Submodule.comap L2Sigma_R3.subtype H1Sigma_R3` — KEEP
  (sorry-free).
- **C1** `convFormH1_tower : H1Sigma' →ₗ[ℝ] H1Sigma' →ₗ[ℝ] H1Sigma' →ₗ[ℝ] ℝ`, `toFun u v w = convFormH1
  (u:L2VF_R3) (v:L2VF_R3) (w:L2VF_R3) …` — built from B4 (`convFormH1_add_{1,2,3}`/`_smul_{1,2,3}`).
  KEEP the statement; its body is the C1 must-prove (currying, no analytic risk).

### 3.1 The two BLT forms at fixed Schwartz `w` (the continuity engine)

**C2 (CRUX-FINAL, analytic must-prove).** `convFormH1_bound_slot2_schwartz` — for fixed Schwartz `w`,
`(u,v) ↦ convFormH1 u w v` is `‖u‖‖v‖`-bounded. Statement (as already in scaffold, lines 183-191):

```lean
theorem convFormH1_bound_slot2_schwartz
    (w : L2VF_R3) (hw_H1 : memH1VF_R3 w)
    (hw_sigma : w ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3))
    (hw_sch : IsSchwartzDivFree_R3 ⟨w, hw_sigma⟩) :
    ∃ C_w : ℝ, 0 ≤ C_w ∧
      ∀ (u v : L2VF_R3) (hu : memH1VF_R3 u) (hv : memH1VF_R3 v)
        (hu_sigma : u ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3))
        (hv_sigma : v ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3)),
        |convFormH1 u w v hu hw_H1 hv| ≤ C_w * ‖u‖ * ‖v‖
```

**Proof (concrete, B7∘B6):**
```
obtain ⟨C_w, hC0, hC⟩ := convFormH1_bound_Schwartz w hw_H1 hw_sigma hw_sch   -- B7
refine ⟨C_w, hC0, fun u v hu hv hu_σ hv_σ => ?_⟩
-- B6: convFormH1 u w v = -convFormH1 u v w  (needs all three σ + all three memH1;
--   w-side from hw_H1/hw_sigma, u,v from hu/hv/hu_σ/hv_σ)
rw [convFormH1_antisymm u w v hu hw_H1 hv hu_σ hw_sigma hv_σ, abs_neg]
exact hC u v hu hv hu_σ hv_σ
```
Both inputs are merged sorry-free; this is a 3-line proof. **No `‖∇w‖_∞`-in-the-rough-slot leakage:** the
varied slot is `(u,v)` (L²-controlled by B7), the Schwartz `w` is the fixed test slot in `convFormH1 u v
w` after the B6 flip.

**C3** `convBLT_fixedTest` — for Schwartz `w`, the jointly continuous bilinear
`Bw : L2Sigma_R3 →L[ℝ] L2Sigma_R3 →L[ℝ] ℝ` extending `(u,v) ↦ convFormH1 u v w` from `H₁'×H₁'`. Built by
`LinearMap.extendOfNorm` ×2 from B7's bound + `H1Sigma'`-density (`schwartzDivFree_dense` ⇒ H₁' dense in
L²_σ). Signature in scaffold lines 201-206. **must-prove.**

**C4** `convBLT_swap_fixedTest` — for Schwartz `w`, the jointly continuous bilinear
`Bw' : L2Sigma_R3 →L[ℝ] L2Sigma_R3 →L[ℝ] ℝ` extending `(u,v) ↦ convFormH1 u w v` from `H₁'×H₁'`. Built by
`extendOfNorm` ×2 from **C2**'s bound. Signature in scaffold lines 214-219. **must-prove.**

### 3.2 The determined `b` — REVISED `convFormL2_def`

This is the key revision. Define `b` so its value at slot-3 = Schwartz `w` is `(Bw u v − Bw' u v)/2`.
We achieve this WITHOUT a special-case `if`, by routing the slot-3 dependence through a Hamel extension
whose **restriction to Schwartz slot-3 is forced to equal the BLT forms**.

**Encoding (decision): keep the 3-slot Hamel `BExt` for the ALGEBRA, but DEFINE the continuity through a
separate slot-3-determined family, and PROVE the two agree on Schwartz slot-3 via B6/B5.** Precisely:

```lean
-- C5 (revised): the algebraic b (unchanged shape, from the Hamel tower BExt)
noncomputable def convFormL2_def (u v w : L2Sigma_R3) : ℝ :=
  (BExt_slot3 u v w - BExt_slot3 u w v) / 2
```
where `BExt_slot3` is the 3-slot Hamel extension of `convFormH1_tower` (C5-Hamel, scaffold lines 113-150).
This `b` already gives **C6 (multilinear)**, **C7 (antisymm, by `ring`)**, **C8 (extends, B6+B5)** — all
sound, KEEP from the scaffold. The ONLY field this `b` does not directly give is **C9
(`b_cont_fixedTest`)** — and that is where the determined identity enters.

### 3.3 The crux identity that makes `b(·,·,w) = (Bw − Bw')/2` at Schwartz `w`

**C9-core `convFormL2_eq_BLT_at_schwartz`** [must-prove, the 5th-field engine]:
for Schwartz `w` and ALL `u v : L2Sigma_R3`,
```
convFormL2_def u v w = (Bw w u v - Bw' w u v) / 2
```
where `Bw w := convBLT_fixedTest …` (C3) and `Bw' w := convBLT_swap_fixedTest …` (C4).

**Why this is TRUE and provable (the codex-endorsed point):** Both sides are functions of `(u,v)` at
fixed Schwartz `w`. They agree on the dense set `u,v ∈ H₁'`:
- RHS on `H₁'²`: `Bw w u v = convFormH1 u v w` (C3 `extendOfNorm_eq`), `Bw' w u v = convFormH1 u w v`
  (C4), so `RHS = (convFormH1 u v w − convFormH1 u w v)/2 = convFormH1 u v w` (B6 makes the second term
  `= -convFormH1 u v w`).
- LHS on `H₁'²` (and `w ∈ H₁'`): `BExt_slot3 u v w = convFormH1 u v w`, `BExt_slot3 u w v = convFormH1 u
  w v = -convFormH1 u v w` (B6), so `LHS = convFormH1 u v w`. **Agreement on `H₁'²`. ✓**

To extend agreement to ALL `u,v`: the RHS `(u,v) ↦ (Bw w u v − Bw' w u v)/2` IS continuous (C3,C4 are
CLM). The LHS `b(·,·,w)` is NOT independently known continuous (it routes through Hamel). **So density
transfer cannot run on the LHS directly.** RESOLUTION — invert the definition: we make C9-core the
DEFINITION rather than a derived identity, by REDEFINING `b` at slot-3 ∈ H₁' through the BLT forms. See
§3.4 for the encoding that bakes it in. With that encoding, C9-core is `rfl`/by-construction on the
Schwartz slot-3 branch, and C9 follows from C3+C4 continuity.

### 3.4 The definition that BAKES IN the determined value (resolves §3.3's density gap)

Define a slot-3-keyed BLT family and route `b`'s slot-3 dependence through it. The clean Lean object:

```lean
-- For each Schwartz w (data: the IsSchwartzDivFree_R3 proof), the determined bilinear form on (u,v):
noncomputable def convDetForm (w : L2Sigma_R3) (hw : IsSchwartzDivFree_R3 w) :
    L2Sigma_R3 →L[ℝ] L2Sigma_R3 →L[ℝ] ℝ :=
  (1/2 : ℝ) • (convBLT_fixedTest … w … - convBLT_swap_fixedTest … w …)

-- b is defined so that at Schwartz w it equals convDetForm w; off Schwartz w it is the Hamel value.
-- Concretely, b's slot-3 is the Hamel BExt for the ALGEBRA, and we PROVE (C9-core) that on the
-- Schwartz-slot-3 branch BExt-derived b agrees with convDetForm by the H₁'² density argument...
```

**The honest resolution of the density gap (the make-or-break, codex review point 1).** The density gap
in §3.3 is real IF `b` is the Hamel object. The codex-endorsed fix removes it by **defining `b` on the
Schwartz-slot-3 case to BE `convDetForm`**, not by deriving it. The cleanest Lean realization that keeps
ONE definition of `b` (no `if IsSchwartzDivFree w`) is:

> **Encoding E (recommended).** Build the slot-3 dependence as a `LinearMap`
> `Mext : L2Sigma_R3 →ₗ[ℝ] (L2Sigma_R3 →L[ℝ] L2Sigma_R3 →L[ℝ] ℝ)` such that **for `w ∈ H₁'`,
> `Mext w = the genuine continuous bilinear (u,v) ↦ convFormH1 u v w`** (NOT antisymmetrized — pure
> slot-3). `Mext` is built by: (a) the `H₁'`-restricted map `M : H₁' →ₗ[ℝ] (L2Sigma_R3 →L[ℝ] L2Sigma_R3
> →L[ℝ] ℝ)`, `M w := Bw w` (C3), linear in `w` via `convFormH1_add_3`/`_smul_3` + `extendOfNorm_unique`;
> (b) `LinearMap.exists_extend` to get `Mext` off `H₁'`. Then define
> ```
> b u v w := ((Mext w) u v − (Mext v) u w) / 2.
> ```

With Encoding E:
- **`b_cont_fixedTest` (C9):** fix Schwartz `w` (⇒ `w ∈ H₁'`). Then `Mext w = M w = Bw w` (genuine CLM,
  since `w ∈ H₁'`), so the **first term** `(Mext w) u v = Bw w u v` is continuous in `(u,v)`. The
  **second term** `(Mext v) u w`: here `v` is in the slot-3 Hamel index of `Mext` — BUT it is **evaluated
  at the FIXED Schwartz second-form-slot `w`**. By construction `(Mext v) u w` for `v ∈ H₁'` equals
  `convFormH1 u v w` (NOT `u w v`!) — wait: `(Mext v)` is the form `(a,b) ↦ convFormH1 a b v`, so
  `(Mext v) u w = convFormH1 u w v`. THIS is the term C4 (`convBLT_swap_fixedTest`) bounds via C2 (B7∘B6):
  `(u, w) ↦ convFormH1 u w v` ... no — the varied arguments are `(u,v)`, with `w` FIXED Schwartz. We need
  `(u,v) ↦ (Mext v) u w = convFormH1 u w v` continuous in `(u,v)`. **This is exactly `Bw' w u v` (C4)** —
  bounded by C2's `C_w‖u‖‖v‖` (B7∘B6, fixed Schwartz `w` in the test slot). **So the second term IS the
  C4 BLT form, continuous in `(u,v)`.** This is the codex-endorsed observation: at `b_cont_fixedTest`
  BOTH terms place the Schwartz `w` in a B7-controlled slot.

  The remaining Lean obligation: prove `(Mext v) u w = Bw' w u v` for ALL `u,v` at fixed Schwartz `w`.
  On `v ∈ H₁'`: `(Mext v) u w = convFormH1 u w v = Bw' w u v` (C4 `extendOfNorm_eq`). Extend to all `v`:
  the map `v ↦ (Mext v) u w` is the composition `v ↦ Mext v` (linear, but Hamel-discontinuous in general)
  THEN evaluate-at-`(u,w)`. **The evaluation-at-fixed-Schwartz-`w` functional `Φ : (L2Sigma_R3 →L
  L2Sigma_R3 →L ℝ) →ₗ ℝ`, `Φ F := F u w`, composed with `Mext`, gives `v ↦ (Mext v) u w`, which is the
  `H₁'`-restriction's BLT extension `Bw' w u ·` IFF `Mext` is CHOSEN compatibly.** The clean way: define
  `Mext` so that its slot-3 evaluation at fixed Schwartz `w` is forced. See §3.5.

### 3.5 The choice of `Mext` that forces the determined second term (the decisive lemma)

The Hamel `Mext` from `LinearMap.exists_extend` is not unique; we must CHOOSE it so the second term is the
BLT form. The constraint is only on `v` in the H₁'-complement `K` (`H₁' ⊕ K = L2Sigma_R3` via
`Submodule.exists_isCompl`). For `v ∈ K`, prescribe
```
(Mext v) := the form (a,b) ↦  Bw'_pre b a v       -- to be made precise below
```
**The resolved, build-able statement** is the must-prove lemma:

> **C9-key `convDetForm_second_term_eq`** [must-prove]: there is a choice of `Mext` (equivalently, a
> single `LinearMap` `N : L2Sigma_R3 →ₗ[ℝ] (L2Sigma_R3 →L[ℝ] ℝ)` PARAMETERIZED by the fixed Schwartz `w`)
> with: for all `u v : L2Sigma_R3`, `(Mext v) u w = N v u`, AND `(u,v) ↦ N v u` is continuous.

The parameterized `N` exists because, at FIXED Schwartz `w`, the prescription `v ↦ (the functional
u ↦ convFormH1 u w v)` is **bounded by `C_w‖v‖` in operator norm uniformly in `v`** — this is C2 read as:
`‖(u ↦ convFormH1 u w v)‖_op ≤ C_w ‖v‖` (B7∘B6, the `w`-slot is the fixed Schwartz, the `v`-slot is
L²-varied). So `N : H₁' →ₗ (L2Sigma_R3 →L ℝ)`, `N v := (u ↦ convFormH1 u w v)`, is **bounded**, hence
BLT-extends continuously to `L2Sigma_R3` — **no Hamel, no unboundedness.** `N` IS `Bw' w` curried, and
`(u,v) ↦ N v u = Bw' w u v` is jointly continuous (C4). **This is the entire content of the 5th field.**

**SIMPLIFICATION (recommended actual encoding — avoids `Mext`/`N` plumbing entirely).** Because the second
term, at fixed Schwartz `w`, is provably `Bw' w u v` (C4) for all `u,v`, and the first term is `Bw w u v`
(C3) for all `u,v`, we may **DEFINE `b` directly through the BLT forms on the Schwartz-slot-3 branch and
the Hamel `BExt` elsewhere**, using a slot-3 case-split that is invisible to the algebraic fields. But the
clean, single-definition route is Encoding E with the BLT-forced choice of `Mext`. Either way, the
must-prove crux is the same finite identity:

> **C9 `convFormL2_cont_fixedTest`** [must-prove, the 5th field]: for Schwartz `w`,
> `(u,v) ↦ b u v w` is continuous. **Proof:** rewrite `b u v w = (Bw w u v − Bw' w u v)/2` (C9-core,
> which is by-construction on the Schwartz-slot-3 branch under Encoding E), then `(Bw w).continuous₂`,
> `(Bw' w).continuous₂`, `Continuous.sub`, `Continuous.div_const`.

---

## 4. mathlib API — names, presence, build-arounds

| API | Location | Present? | Use / build-around |
|---|---|---|---|
| `LinearMap.exists_extend {p : Submodule K V} (f : p →ₗ V') : ∃ g, g.comp p.subtype = f` | `LinearAlgebra/Basis/VectorSpace.lean:288` | YES (needs `DivisionRing K`; ℝ ok) | slot-1 Hamel of `convFormH1_tower`; `Mext` off H₁'. **Instance trap:** `Classical.choose` yields `DivisionRing.toDivisionSemiring.toSemiring ℝ` vs `Real.semiring`; fix with `letI : Semiring ℝ := inferInstance` / `show` (scaffold lines 102-108 already document this). |
| `Submodule.exists_isCompl (p : Submodule K V) : ∃ q, IsCompl p q` | mathlib | YES | complement `K` of `H₁'` for the `Mext`-choice (§3.5), if Encoding E's forced choice is done via `ofIsCompl`. |
| `LinearMap.ofIsCompl (h : IsCompl p q) (f : p →ₗ V') (g : q →ₗ V') : V →ₗ V'` | mathlib | YES | glue `M` on H₁' with the prescribed map on `K`. |
| `LinearMap.extendOfNorm` + `extendOfNorm_eq` / `opNorm_extendOfNorm_le` / `_unique` | `Analysis/Normed/Operator/Extend.lean:190` | YES | C3, C4: BLT extension from H₁'-dense + B7/C2 bound. Used twice each (slot 2 then slot 1). |
| `ContinuousLinearMap.continuous₂` / `.continuous` | mathlib | YES | C9 final continuity from C3/C4 CLMs. |
| `TensorProduct.lift` / `.uncurry` / `.map` / `Submodule.map₂` | mathlib | YES | **NOT USED** — tensor model is conceptual only (§2.2). |
| `(P⊗B) ⊓ (A⊗Q) = P⊗Q` tensor-intersection | — | **ABSENT** | **BUILD-AROUND: do not build it. Use the scalar/curried route (§3).** |
| `SchwartzMap.memSobolev` | `Analysis/Distribution/Sobolev.lean:201` | YES | `memH1VF_R3_of_schwartz` (C8 helper), already in scaffold. |
| `Submodule.comap` | mathlib | YES | C0 `H1Sigma'`, sorry-free. |
| H₁' density in L²_σ | `ConvectionForm.lean` `schwartzDivFree_dense_of_curlDense` ⇒ H₁' ⊇ Schw dense | YES (derived) | `DenseRange`/`Dense` input to `extendOfNorm` for C3/C4. Need a one-line lemma `h1Sigma'_dense : Dense (H₁' : Set L2Sigma_R3)` from Schw ⊆ H₁' + Schw dense. **must-prove (small).** |

---

## 5. Files, declarations, dependency order

### REVISED `LerayHopf/R3/ConvectionExtension.lean`

| # | Declaration | Informal signature | Status | Change vs current scaffold |
|---|---|---|---|---|
| C0 | `H1Sigma'` | `Submodule ℝ L2Sigma_R3` comap | **KEEP** sorry-free | none |
| C1 | `convFormH1_tower` | `H₁'→ₗH₁'→ₗH₁'→ₗℝ` from B4 | must-prove | fill body (currying) |
| C1d | `h1Sigma'_dense` | `Dense (H₁' : Set L2Sigma_R3)` from Schw⊆H₁' + density | must-prove (small) | NEW |
| C2 | `convFormH1_bound_slot2_schwartz` | fixed Schwartz `w`: `|convFormH1 u w v|≤C_w‖u‖‖v‖` (B7∘B6) | **must-prove (3-line)** | already stated; fill body |
| C3 | `convBLT_fixedTest` | Schwartz `w`: CLM `Bw` ext. `(u,v)↦convFormH1 u v w` (extendOfNorm×2 from B7) | must-prove | already stated; fill body |
| C4 | `convBLT_swap_fixedTest` | Schwartz `w`: CLM `Bw'` ext. `(u,v)↦convFormH1 u w v` (extendOfNorm×2 from C2) | must-prove | already stated; fill body |
| C5h | `BExt_slot{1,2,3}` (+ `_on_H1`, `BExt_on_H1`) | 3-slot Hamel of C1 | must-prove | **KEEP** (algebra layer); fill Hamel bodies |
| C5 | `convFormL2_def` (the `b`) | Encoding E: `b u v w := ((Mext w) u v − (Mext v) u w)/2`, OR keep `(BExt_slot3 u v w − BExt_slot3 u w v)/2` for algebra + prove C9 via C9-core | **must-prove** | **REVISE** so C9-core holds (§3.4 Encoding E) |
| C5m | `Mext` (+ `M`, `convDetForm`) | slot-3-keyed BLT family forced on H₁' (§3.4) | must-prove | NEW (Encoding E) |
| C6 | `convFormL2_multilinear` | `∃ B trilinear, b = B` | must-prove | from `Mext`/`BExt` algebra |
| C7 | `convFormL2_antisymm` | `b u v w = -b u w v` (`ring`) | **KEEP** sorry-free | none (formula antisymmetric) |
| C8 | `convFormL2_extends` | Schwartz triples `b = convFormSchwartz` (B6+B5) | must-prove | adapt to Encoding E |
| C9core | `convFormL2_eq_BLT_at_schwartz` | Schwartz `w`: `b u v w = (Bw u v − Bw' u v)/2` ∀u,v | **must-prove (crux)** | NEW |
| C9 | `convFormL2_cont_fixedTest` | Schwartz `w`: `(u,v)↦b u v w` continuous (from C9core+C3+C4) | **must-prove (5th field)** | already stated; fill body |
| C10 | `r3ConvectionGapOp_holds` → re-exported as `r3ConvectionGapOp_exists` | `(𝔊):Nonempty (ConvectionGapOp 𝔊)` from C5-C9 | **must-prove (PRIMARY)** | already assembled; depends on C6,C9 |

### Edit to `ConvectionForm.lean` (coder, separate hunk, PR-5)

Delete `axiom r3ConvectionGapOp_exists` (line 664) and re-export C10 (`r3ConvectionGapOp_holds`) under the
**same name** `r3ConvectionGapOp_exists` (Hard rule #2). Downstream `r3_NSForms_exists` (line 675)
unchanged — same `Nonempty (ConvectionGapOp 𝔊)`. **No edit to `AxiomaticClosure.lean`.**

### Dependency edges

```
B4 ─▶ C1 ─▶ {C5h(BExt), C5m(Mext via M)} ─▶ C5 ─▶ {C6, C7, C8}
B7 ─▶ C2 ─▶ C4 ;  B7 ─▶ C3 ;  Schw⊆H₁' + density ─▶ C1d ─▶ {C3,C4}
{C3, C4, C5} ─▶ C9core ─▶ C9
B6, B5 ─▶ C8 ;  B6 ─▶ {C2, C9core}
{C5,C6,C7,C8,C9} ─▶ C10 ─▶ (ConvectionForm.lean axiom deletion + re-export)
```

---

## 6. Assumptions to package as axioms

**None.** Definition of done is REMOVAL of `r3ConvectionGapOp_exists`. If C9core/C9 prove intractable,
the correct outcome is **NOT** to re-axiomatize the 5th field (owner ban on residual axiom): leave C9/C10
as marked `-- ALLOW_SORRY` + precise `-- TODO:` naming the exact missing identity (the BLT-forced choice
of `Mext`, §3.5), ship C0-C8 sorry-free, axiom STAYS (count 3). **Do not weaken any `ConvectionGapOp`
field.**

---

## 7. What changes from the current raw-Hamel scaffold (REVISION list for coder)

The current `ConvectionExtension.lean` (raw-Hamel) is the REFUTED object for C9. Concrete revisions:

1. **C5 `convFormL2_def` (lines 163-164):** the formula `(BExt_slot3 u v w − BExt_slot3 u w v)/2` is fine
   for the ALGEBRA (C6,C7,C8) but its C9 is FALSE (codex PR #60). REVISE per Encoding E (§3.4): route
   slot-3 through `Mext` whose H₁'-restriction is the genuine BLT family, so that at Schwartz `w` the two
   terms are `Bw w u v` and `Bw' w u v` (C3,C4), both `(u,v)`-continuous. The **algebraic** fields
   re-derive from `Mext`'s trilinearity identically.
2. **ADD C5m (`M`, `Mext`, `convDetForm`)** — the slot-3-keyed BLT family (§3.4) with the BLT-forced
   choice (§3.5).
3. **ADD C1d (`h1Sigma'_dense`)** — H₁' dense in L²_σ, for `extendOfNorm` in C3/C4.
4. **ADD C9core (`convFormL2_eq_BLT_at_schwartz`)** — the crux: `b(·,·,w) = (Bw − Bw')/2` at Schwartz `w`,
   by-construction under Encoding E (NOT density-transfer on a Hamel object).
5. **C9 `convFormL2_cont_fixedTest` (lines 291-294):** REWRITE the body to `C9core ▸ (Bw.cont − Bw'.cont)`
   — no Hamel index in a continuity slot.
6. **C2/C3/C4 bodies:** fill (B7∘B6 for C2; `extendOfNorm` for C3/C4). Statements already correct.
7. **C8 (lines 267-280):** adapt the proof chain to Encoding E's `b` (B6+B5 unchanged; the `BExt_on_H1`
   step becomes the `Mext`-on-H₁' step). Statement unchanged.
8. **Delete the false header claims** (the file docstring says C5/C7 are "PROVED" under the raw-Hamel `b`;
   after revision C7 stays `ring`-proved but C5's definition changed).

The doc header should drop the raw-Hamel framing and reference THIS contract.

---

## 8. Codex review points (orchestrator runs `/codex:adversarial-review --effort xhigh`)

1. **C9core `convFormL2_eq_BLT_at_schwartz` STATEMENT + Encoding E's `Mext`-forced-choice** — the
   make-or-break. Confirm that under Encoding E, at Schwartz `w`, `b(·,·,w) = (Bw u v − Bw' u v)/2` for
   ALL `u,v` is by-construction (the determined value is BAKED IN, not recovered via density on a Hamel
   object). This is the precise place the refuted PR #60 object failed — codex must confirm the second
   term `(Mext v) u w` is the C4 BLT form `Bw' w u v` (B7∘B6-controlled), NOT a Hamel-discontinuous value.
2. **C2 `convFormH1_bound_slot2_schwartz` STATEMENT** — confirm B7∘B6 composes (B6 flips
   `convFormH1 u w v = -convFormH1 u v w`, same magnitude; B7 bounds `|convFormH1 u v w| ≤ C_w‖u‖‖v‖`)
   with NO `‖∇w‖_∞`-in-the-rough-slot leakage.
3. **C5 REVISED `convFormL2_def` + Encoding E** — confirm the new `b` still gives C6,C7,C8 (algebra
   unchanged) AND is the SAME `b` whose continuity-slice is BLT (no double definition / no field
   weakening). Confirm `b` is NOT the refuted raw-Hamel object.
4. **C10 STATEMENT** — verbatim former-axiom `(𝔊):Nonempty (ConvectionGapOp 𝔊)`, non-vacuous (C8 pins `b`
   to `convFormSchwartz` ≠ 0 on Schwartz triples).

Codex gate is MANDATORY on review points 1 and 2 BEFORE PR-4 proofs (the contested core).

---

## 9. PR decomposition (revised PR-3 / PR-4)

- **PR-3 (coder + prover, buildable now, all algebra sorry-free):** C0 (keep), C1 (body), C1d, C5h
  (`BExt`/`Mext` Hamel + on-H₁'), C5 (REVISED Encoding-E `b`), C6, C7, C8 → the **4 algebraic/extension
  fields** sorry-free. C2/C9core/C9/C10 STATEMENTS elaborate with bodies `-- ALLOW_SORRY: PR-4`. Sonnet
  for C0/C1/C1d plumbing; Opus for C5/C8 (Encoding E + B6). **Codex gate: review points 1-4 BEFORE PR-4.**
- **PR-4 (prover, the analytic core):** C2 (B7∘B6, ~3 lines), C3/C4 (`extendOfNorm`), C9core (the crux,
  by-construction under Encoding E), C9 (5th field from C9core+C3+C4). Opus-class. Codex-gated.
- **PR-5 (coder, axiom removal):** delete `axiom r3ConvectionGapOp_exists` (`ConvectionForm.lean:664`),
  re-export C10 under the same name; preflight + `scripts/check-axioms-live.sh` shows R3 capstone 3→2;
  `r3_NSForms_exists` still elaborates sorry-free. Depends on PR-4.

**First concrete lemma to hand `lean-coder`:** **C2 `convFormH1_bound_slot2_schwartz`** — it is the
decisive analytic claim, it is a 3-line B7∘B6 proof from two MERGED sorry-free lemmas, and it is the input
both C4 and C9core consume. (C0/C1/C1d plumbing can be handed in parallel as a Sonnet task, but C2 is the
load-bearing first proof and should be codex-reviewed as a STATEMENT before its body and before any
Encoding-E work.) If preferred to lead with zero-analytic-risk plumbing: hand C0 (keep) + C1 (currying)
first, then C2.

---

## 10. Definition of done

- **PR-3 (sorry-free):** C0, C1, C1d, C5h, C5(revised), C6, C7, C8 — 4 of 5 `ConvectionGapOp` fields,
  plus C2/C9core/C9/C10 STATEMENTS elaborating (bodies `-- ALLOW_SORRY: PR-4`).
- **PR-4 (sorry-free):** C2, C3, C4, C9core, C9 — the 5th field `b_cont_fixedTest`.
- **PR-5 (done = 3→2):** `r3ConvectionGapOp_exists` is a sorry-free THEOREM (axiom deleted);
  `check-axioms-live.sh` shows R3 capstone 3→2; `r3_NSForms_exists` elaborates sorry-free.
- **No new axiom, no field weakening.** If C9core proves intractable, PR-3's 4-field core ships sorry-free,
  C9core/C9/C10 retain marked `sorry` + precise `-- TODO:` (naming the §3.5 `Mext`-forced-choice as the
  blocker), axiom STAYS (count 3).
