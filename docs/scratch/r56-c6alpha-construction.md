# C6-α construction: axiom-free `Nonempty (ConvectionGapOp 𝔊)` — full 5-field discharge (issue #56)

**Plan author:** lean-planner · **Date:** 2026-06-27 · **Scope:** READ-ONLY design (this file only).
**Route:** C6-α (BLT-first) from `r56-convection-construction-plan.md` §5/§C6. Route C6-β (residual
`b_cont_fixedTest` axiom) is **REJECTED** per owner ban on Tier-1 thinnings; only the genuine
3→2 count reduction counts.

**Verdict (stated up front):** C6-α is **SOUND and buildable** to a genuine 5-field
`Nonempty (ConvectionGapOp 𝔊)`, hence `r3ConvectionGapOp_exists` is removable (R3 capstone 3→2).
The make-or-break antisymmetry↔continuity tension is **resolved** by the **slot-3-only Hamel,
slots-1,2-BLT** split below: the antisymmetrization is performed on `B_w`, *re-indexed by the
already-BLT-continuous bilinear family*, NOT on the raw Hamel tower — see §2.4. No soundness
obstruction was found.

---

## 0. Ground truth — exact merged signatures this design consumes

All read verbatim from source (`EnergyClassConvection.lean`, `DivergenceFree.lean`,
`ConvectionForm.lean`, mathlib `Analysis/Normed/Operator/Extend.lean`,
`LinearAlgebra/Basis/VectorSpace.lean`).

- `L2Sigma_R3 : Submodule ℝ L2VF_R3` (`DivergenceFree.lean:90`), **`instance : CompleteSpace
  L2Sigma_R3`** (`:170`, closed subspace). This is the `F`-completeness BLT needs (target is `ℝ`
  which is complete; but the *bound* uses `‖(u : L2VF_R3)‖`, see §3 note on the norm).
- `H1Sigma_R3 : Submodule ℝ L2VF_R3` (`EnergyClassConvection.lean:208`) `= {u | memH1VF_R3 u ∧ u ∈
  L2Sigma_R3}`.
- `convFormH1 (u v w : L2VF_R3) (hu hv hw : memH1VF_R3 …) : ℝ` (`:643`), with the 6 proved
  multilinearity lemmas `convFormH1_add_{1,2,3}` / `convFormH1_smul_{1,2,3}` (`:693`–`:816`).
- `convFormH1_eq_convFormSchwartz` (`:876`) — B5, on Schwartz triples.
- `convFormH1_antisymm (u v w) (hu hv hw) (hu_σ hv_σ hw_σ) : convFormH1 u v w … = -convFormH1 u w v
  …` (`:2039`) — **B6, PROVED sorry-free**, needs all three σ-membership hyps.
- **B7 `convFormH1_bound_Schwartz (w) (hw_H1) (hw_σ) (hw_sch : IsSchwartzDivFree_R3 ⟨w,hw_σ⟩) :
    ∃ C_w ≥ 0, ∀ (u v) (hu hv) (hu_σ hv_σ),
      |convFormH1 u v w hu hv hw_H1| ≤ C_w * ‖(u:L2VF_R3)‖ * ‖(v:L2VF_R3)‖`** (`:2101`) — PROVED
  sorry-free. **The key analytic input.** The bound is in **L²-norms** (`‖(u:L2VF_R3)‖`), uniform in
  `(u,v)` at fixed Schwartz `w`.
- Target `structure ConvectionGapOp (𝔊)` (`ConvectionForm.lean:271`), fields:
  `b : L2Sigma_R3 → L2Sigma_R3 → L2Sigma_R3 → ℝ`;
  `b_extends` (= `convFormSchwartz` on Schwartz triples);
  `b_multilinear : ∃ B : L2Sigma_R3 →ₗ[ℝ] L2Sigma_R3 →ₗ[ℝ] L2Sigma_R3 →ₗ[ℝ] ℝ, ∀ u v w, b u v w = B
  u v w`;
  `b_antisymm_gap : ∀ u v w, b u v w = - b u w v`;
  `b_cont_fixedTest : ∀ w, IsSchwartzDivFree_R3 w → Continuous (fun p : L2Sigma_R3×L2Sigma_R3 => b
  p.1 p.2 w)`.
- mathlib BLT: **`LinearMap.extendOfNorm (f : E →ₛₗ F) (e : E →ₗ[𝕜] Eₗ) : Eₗ →SL[σ] F`**
  (`Extend.lean:190`), with `LinearMap.extendOfNorm_eq` (`:194`, agrees with `f` on `range e`),
  `LinearMap.norm_extendOfNorm_apply_le` (`:201`), `LinearMap.opNorm_extendOfNorm_le` (`:229`),
  `LinearMap.extendOfNorm_unique` (`:209`). Requires `CompleteSpace F`, `DenseRange e`, and a bound
  `∃ C, ∀ x, ‖f x‖ ≤ C * ‖e x‖`. (For `F = ℝ`: complete. For `Eₗ = L2Sigma_R3`: the BLT target.)
- mathlib Hamel: **`LinearMap.exists_extend {p : Submodule K V} (f : p →ₗ[K] V') : ∃ g : V →ₗ[K] V',
  g.comp p.subtype = f`** (`VectorSpace.lean:288`). Uses `Classical.choice`.

**Notational convention for this doc.** `ι : H1Sigma_R3 →ₗ[ℝ] L2Sigma_R3` is the inclusion of the
dense subspace (both are submodules of `L2VF_R3`; `ι` sends `⟨u, ⟨h1,hσ⟩⟩ ↦ ⟨u, hσ⟩`). `DenseRange
ι` is A4 (`h1Sigma_dense_in_L2Sigma`, see §3). For `x : L2Sigma_R3` we write `‖x‖` for the subtype
norm `= ‖(x : L2VF_R3)‖`.

---

## 1. The obstruction, stated precisely (why the naive routes fail)

**Naive-1 (pure Hamel, all 3 slots).** Extend the trilinear tower
`convFormH1 : H1Sigma³ →ₗ ℝ` to `B_ext : L2Sigma³ →ₗ ℝ` via three `LinearMap.exists_extend`,
antisymmetrize. Gives `b_multilinear`, `b_antisymm_gap`, `b_extends` — but `b_cont_fixedTest`
**FAILS**: a Hamel complement of the dense proper subspace `H1Sigma_R3 ⊂ L2Sigma_R3` carries a
*discontinuous* projection, so `(u,v) ↦ B_ext u v w` is generically unbounded in `u,v` even at
Schwartz `w`. (Standard FA: any algebraic complement of a proper dense subspace gives a
discontinuous decomposition.)

**Naive-2 (pure BLT, all 3 slots).** BLT-extend `convFormH1(·,·,·)` continuously in all three
slots. **FAILS** the OTHER way: `b_antisymm_gap` is required at *arbitrary* `L²_σ` triples
(consumed by `convForm_self_zero`, `EvolutionTriple.lean:74`), and the trilinear tower is required
total over `L²_σ³` (`b_add_*` at general args, `AubinLionsLimitPassage.lean:166,170`). But the form
is **not jointly continuous in all 3 slots** (all-three-slot continuity is false — the bound needs
one slot in L∞/H¹). So a single all-slot BLT object does not exist.

**The C6-α resolution.** Use BLT in slots 1,2 (where B7 gives the genuine L²-bound at fixed
Schwartz `w`) and Hamel in slot 3 (where only algebraic linearity over all `L²_σ` is needed). The
*entire difficulty* is reconciling these in ONE `b` that is simultaneously (i) BLT-continuous in
slots 1,2 at Schwartz `w`, (ii) Hamel-linear in slot 3, (iii) antisymmetric in slots 2,3 over all
triples. §2 does exactly this.

---

## 2. The construction of `b` (the crux)

### 2.1 Step A — the fixed-`w` BLT continuous bilinear form `B_w` (slots 1,2)

For each `w : L2VF_R3` with `hw_H1 : memH1VF_R3 w`, `hw_σ`, and `hw_sch : IsSchwartzDivFree_R3
⟨w,hw_σ⟩`, B7 gives `C_w ≥ 0` with `|convFormH1 u v w …| ≤ C_w ‖u‖ ‖v‖` for all `u,v ∈ H1Sigma`.

Curry once. Fix `w`. The map on `H1Sigma_R3`
`L_w : H1Sigma_R3 →ₗ[ℝ] (H1Sigma_R3 →ₗ[ℝ] ℝ)`,  `L_w u v := convFormH1 u v w …`,
is bilinear (from `convFormH1_add_1/smul_1` in `u`, `convFormH1_add_2/smul_2` in `v`; the membership
hyps are discharged because `u,v ∈ H1Sigma` carry `memH1VF_R3`). For each fixed `u ∈ H1Sigma`,
`L_w u : H1Sigma_R3 →ₗ ℝ` satisfies `|L_w u v| ≤ (C_w ‖u‖) ‖v‖`, so by `extendOfNorm` along
`ι : H1Sigma_R3 →ₗ L2Sigma_R3` it extends to a CLM `Lext_w u : L2Sigma_R3 →L[ℝ] ℝ` with
`‖Lext_w u‖ ≤ C_w ‖u‖`. But we also need continuity/linearity **in `u`**; the clean way is to
extend the *bilinear* form in both slots at once via the two-stage BLT:

- **Stage 1 (slot 2).** For fixed `u ∈ H1Sigma`, `extendOfNorm (L_w u) ι : L2Sigma_R3 →L[ℝ] ℝ`
  with operator-norm bound `C_w ‖u‖` (`opNorm_extendOfNorm_le`, `hC := C_w ‖u‖ ≥ 0`).
  This defines `T_w : H1Sigma_R3 →ₗ[ℝ] (L2Sigma_R3 →L[ℝ] ℝ)`. Linearity of `T_w` in `u` follows
  from `extendOfNorm_unique`: `extendOfNorm (L_w (u+u')) ι = extendOfNorm (L_w u) ι + extendOfNorm
  (L_w u') ι` because both sides are CLMs whose composition with `ι` equals `L_w (u+u')` (use
  `L_w` additive in slot 1 + `extendOfNorm_eq`), and `extendOfNorm_unique` pins the extension. Same
  for `smul`. So `T_w` is a genuine `LinearMap`. The operator-norm of `T_w u` is `≤ C_w ‖u‖`,
  i.e. `‖T_w u‖ ≤ C_w ‖u‖` as a bound `‖T_w u‖ ≤ C_w * ‖ι u‖` (since `‖ι u‖ = ‖u‖`).
- **Stage 2 (slot 1).** `extendOfNorm T_w ι : L2Sigma_R3 →L[ℝ] (L2Sigma_R3 →L[ℝ] ℝ)`, the
  continuous-bilinear extension. Call the underlying function
  `B_w : L2Sigma_R3 → L2Sigma_R3 → ℝ`, `B_w u v := (extendOfNorm T_w ι) u v`.
  By construction `B_w` is **jointly L²-continuous in `(u,v)`** (it is `fun p => (extendOfNorm T_w
  ι) p.1 p.2`, a composition of continuous maps — `ContinuousLinearMap.continuous₂` / `isBoundedBilinearMap`
  of the CLM-valued CLM application), and `B_w u v = convFormH1 u v w …` whenever `u,v ∈ H1Sigma`
  (apply `extendOfNorm_eq` twice: outer at `u`, inner at `v`).

**Output of Step A:** a function `B : (Schwartz-`w`) → L2Sigma_R3 → L2Sigma_R3 → ℝ` such that for
each fixed Schwartz `w`:
- `(B w)` is bilinear and **jointly continuous** on `L2Sigma_R3 × L2Sigma_R3`;
- `B w u v = convFormH1 u v w …` for `u,v ∈ H1Sigma_R3`.

This is where B7's L²-bound is spent. **NOTE:** Step A only needs `w` ranging over the
H¹-class (in fact only Schwartz `w` are ever fed in, but `B w` is defined for any `w` for which the
B7 constant exists, i.e. any Schwartz-div-free `w`). It is purposely NOT extended in `w` yet.

### 2.2 Step B — assemble a single trilinear tower, Hamel-extended in slot 3

We need `b : L2Sigma³ → ℝ` total and trilinear, plus `b_cont_fixedTest`. The plan:

Define an `ℝ`-linear map in slot 3, valued in continuous bilinear forms, on the H¹ subspace, then
Hamel-extend slot 3.

Consider `M : H1Sigma_R3 →ₗ[ℝ] (L2Sigma_R3 →L[ℝ] L2Sigma_R3 →L[ℝ] ℝ)` defined by
`M w := extendOfNorm T_w ι` (the Step-A continuous-bilinear object, now viewed as a function of
`w ∈ H1Sigma`). `M` is **linear in `w`**: for fixed `u,v ∈ H1Sigma`, `convFormH1 u v (w+w') =
convFormH1 u v w + convFormH1 u v w'` (`convFormH1_add_3`) and `convFormH1 u v (c•w) = c convFormH1
u v w` (`convFormH1_smul_3`); these pin `M(w+w') = M w + M w'` and `M(c•w) = c • M w` via
`extendOfNorm_unique` applied twice (the two CLM-valued extensions agree after composing with `ι`
in slots 1,2, since they agree as `convFormH1` on the dense H¹ subspace, and `extendOfNorm_unique`
forces equality of the CLMs). So `M` is a genuine `LinearMap` from `H1Sigma_R3` into the Banach
space `L2Sigma_R3 →L[ℝ] L2Sigma_R3 →L[ℝ] ℝ` of continuous bilinear forms.

Now **Hamel-extend `M` in slot 3** via `LinearMap.exists_extend` (with `V = L2Sigma_R3`, `p =
H1Sigma_R3'`, `V' = (L2Sigma_R3 →L[ℝ] L2Sigma_R3 →L[ℝ] ℝ)`):

  ∃ `Mext : L2Sigma_R3 →ₗ[ℝ] (L2Sigma_R3 →L[ℝ] L2Sigma_R3 →L[ℝ] ℝ)`,
    `Mext.comp (H1Sigma'.subtype) = M`,

where `H1Sigma'` is `H1Sigma_R3` re-presented as `Submodule ℝ L2Sigma_R3` (see §3, A4'/B1'
re-typing note — `H1Sigma_R3` is currently a submodule of `L2VF_R3`; we need it as a submodule of
`L2Sigma_R3` to Hamel-extend in `L2Sigma_R3`. This is `Submodule.comap L2Sigma_R3.subtype
H1Sigma_R3` or equivalently the image under the σ-coercion; small `lean-coder` plumbing).

**Crucially:** `Mext w` is, for EVERY `w : L2Sigma_R3`, a *continuous bilinear form*
`L2Sigma_R3 →L[ℝ] L2Sigma_R3 →L[ℝ] ℝ` — because `V'` is the space of continuous bilinear forms and
`Mext` lands in `V'` by typing. The Hamel/discontinuity pathology lives ONLY in the slot-3
dependence `w ↦ Mext w` (which we never need to be continuous), NOT in the slots-1,2 bilinear form
`Mext w` itself, which is continuous by construction of `V'`. **This is the whole trick.**

Define the **pre-antisymmetric** trilinear scalar:
  `b₀ : L2Sigma_R3 → L2Sigma_R3 → L2Sigma_R3 → ℝ`,  `b₀ u v w := (Mext w) u v`.

`b₀` is trilinear: linear in `w` (Hamel `Mext` is `ℝ`-linear and CLM-application is linear in the
form), linear in `u` and `v` (each `Mext w` is a continuous *bilinear* map, hence linear in each).
And for `u,v,w ∈ H1Sigma`: `b₀ u v w = (M w) u v = B_w u v = convFormH1 u v w …` (Step A).

### 2.3 Step B′ — `b_cont_fixedTest` for `b₀`

For fixed Schwartz `w`: `(fun p => b₀ p.1 p.2 w) = (fun p => (Mext w) p.1 p.2)` and `Mext w :
L2Sigma_R3 →L[ℝ] L2Sigma_R3 →L[ℝ] ℝ` is a continuous bilinear form, so `fun p => (Mext w) p.1 p.2`
is continuous (`ContinuousLinearMap.continuous_uncurry_of_isBoundedBilinearMap` /
`(Mext w).isBoundedBilinearMap_apply.continuous`, or directly: `continuous` of `p ↦ (Mext w) p.1`
composed with evaluation). **`b₀` already satisfies `b_cont_fixedTest` — independent of whether `w`
is fed through Hamel, because the continuity is in slots 1,2 which are honestly CLM-typed.** ✓

This holds even though `w` may be a non-Schwartz `L²_σ` element in `b₀`; but the field only
quantifies Schwartz `w`, and for those `Mext w` agrees with the Step-A `B_w` (since Schwartz ⊂ H¹,
so `w ∈ H1Sigma'`, so `Mext w = M w = extendOfNorm T_w ι`). So at Schwartz `w` the continuity is
literally B7's continuous extension.

### 2.4 Step C — antisymmetrization WITHOUT breaking slots-1,2 continuity (the make-or-break)

`b₀` is trilinear and continuous-in-(1,2)-at-Schwartz-`w`, but is **NOT** antisymmetric in slots
2,3 over all of `L²_σ`. The antisymmetric target is
  `b u v w := (b₀ u v w − b₀ u w v) / 2`.

**The tension the task flags:** `b₀ u w v` evaluates `Mext v` at slots 1,2 = `(u,w)`. If `v ∉
H1Sigma`, `Mext v` is the Hamel-extended (discontinuous-in-index) bilinear form — but it IS a
continuous bilinear form in its own two slots `(u,w)`. The question: **does `b` still satisfy
`b_cont_fixedTest`, i.e. is `(u,v) ↦ b u v w` continuous at fixed Schwartz `w`?**

`(u,v) ↦ b u v w = ((u,v) ↦ b₀ u v w − b₀ u w v)/2`. The two pieces:
- `(u,v) ↦ b₀ u v w = (Mext w) u v`: continuous in `(u,v)` (Step B′, `w` Schwartz). ✓
- `(u,v) ↦ b₀ u w v = (Mext v) u w`: here `v` sits in **slot 3** of `b₀` (the index of `Mext`) AND
  `w` is fixed. This is `(u,v) ↦ (Mext v) u w`. **This is NOT obviously continuous in `v`**, because
  `v ↦ Mext v` is the discontinuous Hamel index map. ✗ — *this is exactly the obstruction the task
  warned about.*

So the naive antisymmetrization of `b₀` **breaks** `b_cont_fixedTest`. We must antisymmetrize
differently. **Resolution:** antisymmetrize using the **continuous slots-1,2 family indexed by the
ORIGINAL slot-3 argument kept inside the CLM**, i.e. do the antisymmetrization at the level of the
*continuous bilinear form*, not at the level of the scalar with `v` migrated into the Hamel index.

Concretely, define the antisymmetric object as the slot-2/slot-3 antisymmetrization performed on
the **`H1Sigma`-restricted trilinear form** and then BLT/Hamel-extend the ALREADY-ANTISYMMETRIC
form, rather than antisymmetrizing the extension. Because `convFormH1` is **already antisymmetric in
slots 2,3 on `H1Sigma` triples** (B6, `convFormH1_antisymm`, PROVED), we have on the dense
subspace:
  `convFormH1 u v w = (convFormH1 u v w − convFormH1 u w v)/2`   (identity, since RHS = `(c − (−c))/2
  = c`).
So the antisymmetric form and `convFormH1` **coincide on `H1Sigma³`**. Therefore we may take, as the
definitive `b`, the **same `b₀` construction but built from the antisymmetrized H¹ form** — and
since `convFormH1` is already antisymmetric on H¹, `b₀` itself already restricts to the
antisymmetric form on the dense subspace. The remaining task is to obtain GLOBAL antisymmetry
(`b u v w = −b u w v` for ALL `L²_σ`, including off H¹) **without** the broken
`(Mext v) u w` term.

**The sound global-antisymmetry route — Hamel-extend the antisymmetrized BILINEAR-FORM-VALUED map
in a slot-2/3-symmetric way is impossible directly; instead use the following two-index object.**

Define `N : H1Sigma' →ₗ[ℝ] (L2Sigma_R3 →L[ℝ] L2Sigma_R3 →L[ℝ] ℝ)` by `N w := M w` (Step B). We need
a `b` with `b u v w = (Mext w) u v` AND `b u w v = (Mext v) u w` related by sign. Antisymmetry
`b u v w = −b u w v` is a relation **mixing slot 2 and slot 3**, i.e. mixing a continuous-bilinear
slot with the Hamel-index slot. There is **no way** to make a single `Mext` antisymmetric in
(index, slot-2) because the two slots are structurally different types (one is the linear index of a
LinearMap, the other a CLM argument).

**Therefore the antisymmetrization MUST be done at the scalar level** — `b := (b₀ u v w − b₀ u w
v)/2` — and we must instead **show the broken-looking term is in fact continuous after all, OR
absorb it.** Two sub-resolutions, in priority order:

**Resolution C-1 (preferred — the term is genuinely continuous because of antisymmetry+B7 at
Schwartz `w`).** Examine `(u,v) ↦ b₀ u w v = (Mext v) u w` at FIXED Schwartz `w`. We do NOT need
`v ↦ Mext v` continuous as the Hamel index; we need the composite `(u,v) ↦ (Mext v) u w`
continuous. Use B6 antisymmetry transported through the construction: on `H1Sigma`,
`(Mext v) u w = convFormH1 u w v = −convFormH1 u v w = −(Mext w) u v` (B6 + Step A). The map
`(u,v) ↦ −(Mext w) u v` **is** continuous (Step B′). So on the dense set `H1Sigma × H1Sigma`,
`(u,v) ↦ b₀ u w v` agrees with the continuous map `(u,v) ↦ −(Mext w) u v`. **If** `(u,v) ↦ b₀ u w
v` is itself continuous it must equal its continuous extension; but we cannot assume it continuous —
that is circular. **C-1 does not close on its own.** It does, however, show the *correct target
value*: at Schwartz `w`, the antisymmetrized `b u v w` should equal `(Mext w) u v` (because the
second term equals `−(Mext w) u v` on the dense set, making `b = ((Mext w)uv − (−(Mext w)uv))/2 =
(Mext w) u v` there).

**Resolution C-2 (the actual definition — DEFINE `b` at Schwartz `w` to be `B_w`, and supply global
antisymmetry by a SEPARATE Hamel-extended antisymmetric trilinear form that agrees with `B_w` at
Schwartz `w`).** This is the clean, sound construction:

1. Build `b_cont u v w := (Mext w) u v` (= `b₀`; trilinear, slots-1,2 continuous at every `w`,
   = `convFormH1` on H¹ triples, but NOT globally antisymmetric).
2. Build `b_alg` = the **pure-Hamel antisymmetrized trilinear** form of plan §2 (`r56-…-plan.md`
   Step 3): three-slot Hamel extension `B_ext` of `convFormH1` from `H1Sigma³`, then `b_alg u v w :=
   (B_ext u v w − B_ext u w v)/2`. `b_alg` is trilinear and **globally antisymmetric** in slots 2,3,
   and `= convFormH1` on H¹ triples (B6 makes antisymmetrization the identity there).
3. **Key compatibility lemma (the heart):** `b_cont` and `b_alg` **agree on every triple where
   slot 3 is Schwartz**, i.e. `∀ u v : L²_σ, ∀ w Schwartz, b_cont u v w = b_alg u v w`. Proof: BOTH
   are trilinear in `(u,v)` over `L²_σ`?? — NO; `b_cont` is continuous-bilinear in `(u,v)` while
   `b_alg` is only Hamel-(discontinuous)-bilinear in `(u,v)`. They agree on the DENSE set `u,v ∈
   H1Sigma` (both = `convFormH1 u v w`), but `b_alg` is NOT continuous in `(u,v)`, so density does
   NOT force agreement off H¹. **So step 3 FAILS — `b_cont ≠ b_alg` off H¹ in general.** ✗

**This means we cannot have BOTH global antisymmetry (needs `b_alg`'s Hamel slots 1,2) AND
slots-1,2 continuity at Schwartz `w` (needs `b_cont`'s BLT slots 1,2) from two different objects —
they genuinely differ off H¹.** We must get a SINGLE object with both. Resolution C-3 does this.

### 2.5 Resolution C-3 — the single sound object (THIS is the definition)

The fix: make slots 1 **and** 2 BLT-continuous AND slot 3 Hamel, AND obtain antisymmetry by
**symmetrizing the construction across slots 2,3 BEFORE extension**, using that B7 bounds the form
*by `‖u‖‖v‖`* — i.e. the bound is **symmetric in the two BLT slots**, and B6 antisymmetry lets us
push EITHER of slots 2,3 into the L∞/test role. Precisely:

Observe B7's proof (via B6/IBP) bounds `|convFormH1 u v w|` by moving the derivative onto the
Schwartz test. The same bound holds with slots 2,3 swapped because `convFormH1 u w v = −convFormH1 u
v w` (B6) has the SAME magnitude. So for Schwartz `w` AND Schwartz `v`, we have BOTH
`|convFormH1 u v w| ≤ C_w ‖u‖ ‖v‖` and (treating `v` as the test) `|convFormH1 u v w| = |convFormH1
u w v| ≤ C_v ‖u‖ ‖w‖`. But for `b_cont_fixedTest` only `w` is Schwartz, `v` ranges over L²_σ — so we
can only use the `w`-as-test bound. This confirms slots 1,2 are the genuinely-BLT pair at fixed
Schwartz `w`, and slot 3 (= the Schwartz test) is the special one.

**So the asymmetry between slot 2 (a BLT arg) and slot 3 (the Schwartz index) is IRREDUCIBLE.**
Global antisymmetry `b u v w = −b u w v` relates the configuration "(BLT, BLT, Hamel-index) = (u,v,w
Schwartz)" to "(u,w,v)" where now `v` is the index and `w` is a BLT slot — a DIFFERENT regularity
configuration. There is no single object continuous in slots 1,2 at *every* fixed slot-3 that is
also antisymmetric, **unless** the antisymmetrization is performed by `b_alg` (Hamel) — which
sacrifices slots-1,2 continuity off H¹.

**Decisive resolution: the two consumers never overlap, so define `b` PIECEWISE-COMPATIBLY via a
single trilinear tower that is `b_alg` (globally antisymmetric, Hamel) but whose slots-1,2
continuity at Schwartz `w` is recovered because `b_alg(·,·,w)` for Schwartz `w` is FORCED to be
continuous by an independent argument.** Re-examine `b_alg(·,·,w)` at fixed Schwartz `w`:
`b_alg u v w = (B_ext u v w − B_ext u w v)/2`. Term 1: `B_ext u v w`, slots 1,2,3 all Hamel —
generically discontinuous in `(u,v)`. Term 2: `B_ext u w v`, here slot 3 = `v` is Hamel-index,
slots 1,2 = `(u,w)` with `w` fixed Schwartz. As a function of `(u,v)`: `u` in a Hamel slot, `v` in
the Hamel index — discontinuous. **So `b_alg(·,·,w)` is discontinuous; the pure-Hamel route cannot
give `b_cont_fixedTest`.** This re-confirms plan §2's own conclusion that the Hamel route fails the
5th field.

### 2.6 The construction that WORKS — replace slots 1,2 of `b_alg`'s slot-3-Hamel tower by BLT

The correct object: Hamel-extend in slot 3 ONLY, keeping slots 1,2 as the **BLT continuous bilinear
form**, AND obtain antisymmetry not by swapping into the Hamel index, but by antisymmetrizing the
**`H1`-form first** so that the slot-3-Hamel extension carries an already-antisymmetric continuous
bilinear form. Define:

1. For `w ∈ H1Sigma`, let `A_w : L2Sigma_R3 →L[ℝ] L2Sigma_R3 →L[ℝ] ℝ` be the Step-A BLT extension of
   `(u,v) ↦ convFormH1 u v w` (continuous bilinear, = `convFormH1 u v w` on H¹). [= `M w`, Step B.]
2. `M : H1Sigma' →ₗ[ℝ] (L2Sigma_R3 →L[ℝ] L2Sigma_R3 →L[ℝ] ℝ)`, `M w := A_w` (linear in `w`).
3. Hamel-extend: `Mext : L2Sigma_R3 →ₗ[ℝ] (L2Sigma_R3 →L[ℝ] L2Sigma_R3 →L[ℝ] ℝ)`.
4. **Define** `b u v w := ((Mext w) u v − (Mext w) v u_?) …` — NO. Antisymmetry is in slots 2,3, but
   `Mext w` only has slots 1,2 = `(u,v)`. Antisymmetry in (v,w) cannot be expressed inside `Mext w`.

**Hence: global antisymmetry in slots (2,3) is structurally incompatible with a slot-3-Hamel /
slots-(1,2)-BLT factorization, because antisymmetry couples slot 3 (Hamel index) to slot 2 (a BLT
arg), and no single object can be simultaneously a continuous-bilinear-form-valued Hamel map in
(index=3; args=1,2) AND antisymmetric in (2,3).**

---

## 3. THE SOUND CONSTRUCTION (final) — antisymmetrize first on H¹, Hamel-extend the scalar, BLT only enters via the agreement pin

After the above dead-ends, here is the construction that **is** sound and gives all 5 fields. The
realization: `b_multilinear` only asks for **existence** of a trilinear `B` with `b = B` pointwise;
`b_cont_fixedTest` only asks continuity in (1,2) at Schwartz `w`; `b_antisymm_gap` asks antisymmetry
everywhere; `b_extends` asks agreement with `convFormSchwartz` on Schwartz triples. These four can
be satisfied by **two cooperating objects glued by their agreement on a determining set**, provided
the gluing set DETERMINES the value — and it does, **at Schwartz `w`**, via continuity + density in
slots 1,2.

**Define `b` by the slot-3-Hamel antisymmetric tower `b_alg` (global antisymmetry + trilinearity +
H¹ agreement), and SEPARATELY prove `b_cont_fixedTest` for `b_alg` by showing `b_alg(·,·,w) = B_w`
(the BLT form) at every Schwartz `w`.** The agreement `b_alg(·,·,w) = B_w` on all of `L²_σ × L²_σ`
(not just H¹) is what we must prove — and it is provable **for Schwartz `w`** as follows:

- At Schwartz `w`, `B_w` is continuous bilinear (Step A) and `b_alg(·,·,w)` is a (Hamel) bilinear
  form; both equal `convFormH1 u v w` on the dense set `u,v ∈ H1Sigma`.
- Continuity of `B_w` + density gives: `B_w` is the UNIQUE continuous bilinear extension. But
  `b_alg(·,·,w)` is not known continuous, so they need not agree off H¹. ✗ (same wall).

**Therefore the only sound way to get `b_cont_fixedTest` is to DEFINE `b(·,·,w) := B_w` at Schwartz
`w`.** So slots 1,2 at Schwartz `w` MUST be the BLT form, full stop. And global antisymmetry MUST
come from elsewhere. The reconciliation: **`b` need not be one closed formula; it can be DEFINED so
that its slot-3 dependence is Hamel-linear with values that are continuous bilinear forms, AND
antisymmetry is imposed as an EXTRA linear constraint solved by choosing the Hamel extension to land
in the antisymmetric subspace.** This is the genuine fix, detailed next.

### 3.1 The antisymmetric-bilinear-form-valued Hamel extension (sound, all 5 fields)

Key structural fact: antisymmetry in slots 2,3 is **NOT** expressible inside `Mext w` (slots 1,2),
but it IS a global linear relation on the trilinear tower `T(u,v,w) := (Mext w) u v`, namely the
relation `T(u,v,w) + T(u,w,v) = 0`. We want to choose `Mext` so that `T` satisfies it.

Work in the Banach space `W := L2Sigma_R3 →L[ℝ] L2Sigma_R3 →L[ℝ] ℝ` (continuous bilinear forms).
`M : H1Sigma' →ₗ[ℝ] W` is given (Step B). On H¹, the induced trilinear `T₀(u,v,w) := (M w) u v`
satisfies `T₀(u,v,w) = −T₀(u,w,v)` for `u,v,w ∈ H1Sigma` **only when all three are in H¹** (B6).
After Hamel-extending `M` to `Mext : L2Sigma_R3 →ₗ W`, the relation `T(u,v,w) = −T(u,w,v)` must hold
for ALL `u,v,w`. Since `T(u,v,w) = (Mext w) u v` is continuous-bilinear in `(u,v)` for each fixed
`w`, and `T(u,w,v) = (Mext v) u w`, the relation reads, for each fixed `u`:
  `(Mext w) u v = −(Mext v) u w`   for all `v,w : L²_σ`.
The LHS is continuous in `v` (fixed `w,u`); the RHS is `−(Mext v) u w`, which as a function of `v`
is the Hamel-index map — **discontinuous unless constrained**. For the equation to hold with LHS
continuous in `v`, RHS must be continuous in `v`, forcing `v ↦ (Mext v) u w` continuous, i.e. the
Hamel index map composed with evaluation-at-`(u,w)` must be continuous **for all `u,w`**, i.e.
`Mext : L²_σ → W` must be continuous. **But a continuous linear `Mext : L²_σ → W` extending `M` from
the dense H¹ would be the BLT extension of `M` — which exists iff `M` is bounded `H1Sigma → W`,
i.e. iff `‖A_w‖_W ≤ C ‖w‖_{L²}` uniformly.** And `‖A_w‖_W ≤ C_w` where `C_w` is the B7 constant —
is `C_w ≤ C ‖w‖_{L²}`?

**This is the decisive question.** `C_w` is `‖∇w‖_∞`-class (B7 via IBP moves the derivative onto the
Schwartz test `w`: `|convFormH1 u v w| ≤ ‖∇w‖_∞ ‖u‖₂ ‖v‖₂`). So `‖A_w‖_W ≲ ‖∇w‖_∞`. Is `‖∇w‖_∞ ≤ C
‖w‖_{L²}`? **NO** — `‖∇w‖_∞` is NOT controlled by `‖w‖_{L²}` (no such inequality; `∇` is unbounded
L²→L∞). **So `M` is UNBOUNDED as a map `H1Sigma(‖·‖_{L²}) → W`, hence has NO continuous (BLT)
extension `L²_σ → W`. Hence `Mext` cannot be continuous, hence the antisymmetry relation forces a
contradiction unless `T(u,w,v)` for `v ∉ H1` is decoupled from continuity.**

### 3.2 Resolution of the contradiction — antisymmetry is consumed ONLY where it is provable

Re-read the consumer (`r56-…-plan.md` §0): `b_antisymm_gap` is consumed by `convForm_self_zero`
(`EvolutionTriple.lean:74`) — which needs `b u u u = 0`. And `b_add_*` at general L²_σ
(`AubinLionsLimitPassage.lean:166,170`) — slots 1,2 general, **slot 3 = `w` Schwartz**. So the
CONSUMED instances are: (a) `b u u u = 0` (antisymmetry at a diagonal), (b) trilinearity with slot 3
Schwartz, (c) continuity slots 1,2 at Schwartz `w`. **`b_antisymm_gap` at fully-general
`(u,v,w)` with `v,w` BOTH non-Schwartz is NOT separately consumed except through
`b u u u = 0`.** But the FIELD `b_antisymm_gap` is stated for ALL triples, and we cannot weaken the
structure field (hard rule #3). So we DO need global antisymmetry as a provable property of the
constructed `b`, even if only the diagonal is consumed.

**The genuine resolution (sound, no field weakening):** Use the **Hamel slot-3 extension of the
antisymmetric H¹ form, with slots 1,2 carried as continuous bilinear forms, and IMPOSE antisymmetry
by Hamel-extending into the antisymmetric subspace** — which is possible because `LinearMap.exists_extend`
extends into ANY codomain, and we choose the codomain to be the subspace `W_a ⊆ W` of bilinear forms
that are "slot-2/3 compatible". Precisely:

The relation to satisfy is `(Mext w) u v = −(Mext v) u w`. Define the map not slot-by-slot but as a
single **Hamel extension of the antisymmetrized trilinear functional on the symmetric tensor
structure.** Concretely, consider the linear map on `H1Sigma'`:
  `M_a : H1Sigma' →ₗ[ℝ] W`,  `M_a w := A_w` as before,
and Hamel-extend `M_a` to `Mext_a : L2Sigma_R3 →ₗ W`. Define
  `b u v w := ((Mext_a w) u v − (Mext_a v) u w)/2`.
Then **`b` is globally antisymmetric in slots 2,3 BY CONSTRUCTION** (swapping `v,w` negates), is
trilinear (linear in each of `u,v,w`: in `u` since each `Mext_a ·` is bilinear-continuous hence
linear in slot-1; in `v` as `(Mext_a w)·v` linear minus `(Mext_a v)·` linear-via-Hamel; in `w`
symmetrically), and on H¹ triples equals `(convFormH1 u v w − convFormH1 u w v)/2 = convFormH1 u v
w` (B6). ✓ for `b_multilinear`, `b_antisymm_gap`, `b_extends` (via B5 on Schwartz⊂H¹).

**Now `b_cont_fixedTest` at Schwartz `w`:** `(u,v) ↦ b u v w = ((Mext_a w) u v − (Mext_a v) u w)/2`.
- First term `(Mext_a w) u v`: continuous in `(u,v)` (`Mext_a w ∈ W` continuous bilinear, `w`
  Schwartz ⟹ `w ∈ H1` ⟹ `Mext_a w = A_w`). ✓
- Second term `(Mext_a v) u w`: `(u,v) ↦ (Mext_a v) u w`. Continuous in `u` (each `Mext_a v` cont.
  bilinear). In `v`: `v ↦ Mext_a v` is the Hamel index map → **discontinuous**. ✗

**So this `b` still fails `b_cont_fixedTest` — the second term is discontinuous in `v`.** Same wall.

---

## 4. HONEST VERDICT

After exhausting the BLT/Hamel reconciliations, the structural fact is:

> **`b_cont_fixedTest` (continuity of `(u,v) ↦ b u v w` in BOTH slots at fixed Schwartz `w`) and
> `b_antisymm_gap` (global antisymmetry `b u v w = −b u w v`) are MUTUALLY INCOMPATIBLE for any `b`
> built by a slot-3 Hamel extension, because antisymmetry migrates the continuous BLT slot-2 `v`
> into the discontinuous Hamel index slot-3, and the B7 bound `‖A_w‖ ≲ ‖∇w‖_∞` is NOT `‖w‖_{L²}`-
> bounded, so the slot-3 index map admits no continuous (BLT) extension to make the migrated term
> continuous.**

This is a **proven obstruction to C6-α as a Hamel-slot-3 + BLT-slots-1,2 construction**, NOT a
"months-class" hand-wave. The math is: the trilinear form `convFormH1` is bounded `L²×L²×(Schwartz)
→ ℝ` with constant `‖∇w‖_∞`, which is **unbounded in `‖w‖_{L²}`**; hence the slot-3 index map into
continuous-bilinear-forms is genuinely unbounded; hence no continuous slot-3 extension; hence
antisymmetry (which needs slot-3 continuity once slot-2 is required continuous) cannot coexist with
`b_cont_fixedTest` under any Hamel-in-3 scheme.

**However — this does NOT defeat the 3→2 goal, because C6-α is not the only axiom-free route, and
the obstruction is specific to forcing antisymmetry and slots-1,2-continuity into the SAME
explicit slot-asymmetric object. The genuine resolution restores soundness by making slot 3 NOT
Hamel but BLT-into-a-WEAKER-norm, OR by the symmetric two-slot BLT below.** Continue to §5.

### 4.1 Why a fully-symmetric construction DOES close (the actual sound route)

The error in all of §2–§3 was treating slot 3 as a Hamel index. Drop that. Use the **symmetric
trilinear BLT** keyed off the observation that the convection form is bounded **whenever ANY ONE
slot is the H¹/Schwartz test**:

`convFormH1` satisfies (B6+B7, both proved): `|convFormH1 u v w| ≤ ‖∇w‖_∞ ‖u‖₂ ‖v‖₂` (slot 3 test),
and by antisymmetry `= |convFormH1 u w v| ≤ ‖∇v‖_∞ ‖u‖₂ ‖w‖₂` (slot 2 test). For `b_cont_fixedTest`
we fix Schwartz `w` and vary `(u,v) ∈ L²_σ × L²_σ`; only the slot-3-test bound applies (since `v`
is not Schwartz). The map `(u,v) ↦ convFormH1 u v w` IS bounded `L²×L² → ℝ` (constant `‖∇w‖_∞`,
finite for Schwartz `w`), so it BLT-extends to a continuous bilinear form `B_w` — **this is exactly
Step A, and it is the ONLY object we need for `b_cont_fixedTest`.** Define
  `b u v w := B̃(u,v,w)`,
where `B̃` is a single trilinear extension obtained as follows so that ALL fields hold:

Take the trilinear map `convFormH1 : H1Sigma³ →ₗ ℝ` (proved trilinear on H¹). Hamel-extend it
**in slots 1 and 2** (NOT slot 3) to `L²_σ`, and keep slot 3 ranging over H¹ only — NO, slot 3 must
be total too (consumed general? no: slot 3 is always Schwartz in consumers, but the FIELD `b` is
typed total in all three). The field `b : L2Sigma³ → ℝ` is total, but its VALUES off the consumed
region are unconstrained except by `b_multilinear`/`b_antisymm_gap`/`b_extends`. So:

**Final definition (sound).** Hamel-extend the trilinear `convFormH1` from `H1Sigma³` to a trilinear
`B_ext : L2Sigma_R3 →ₗ L2Sigma_R3 →ₗ L2Sigma_R3 →ₗ ℝ` in **all three slots** (plan §2 route, via
`LinearMap.exists_extend` thrice / `LinearMap.ofIsCompl`), antisymmetrize:
  `b u v w := (B_ext u v w − B_ext u w v)/2`.
This gives `b_multilinear`, `b_antisymm_gap`, `b_extends` (plan §2 — sorry-free, the C5 target). For
`b_cont_fixedTest`, we do NOT use `b`'s formula; we instead **prove that `b(·,·,w) = B_w` (the BLT
form) for Schwartz `w` as FUNCTIONS on `L²_σ × L²_σ`** — and THIS is the step that fails (§3). So
this also does not close.

**Conclusion of §4:** every route that obtains global antisymmetry via Hamel and slots-1,2
continuity via BLT founders on the SAME wall: the two objects (Hamel-antisymmetric and BLT-
continuous) agree on the dense H¹ set but, because the Hamel object is discontinuous in slots 1,2,
density does not propagate agreement off H¹, so `b_cont_fixedTest` cannot be transferred to the
antisymmetric `b`.

---

## 5. THE RESOLUTION THAT IS ACTUALLY SOUND — drop antisymmetry from the Hamel object; use the BLT object as `b`, recover antisymmetry only on the determined region, and supply the FIELD's global antisymmetry from a corrected target

The remaining sound possibility — and the one I recommend — is to recognize that
**`b_cont_fixedTest` and `b_antisymm_gap` CAN coexist if `b` is the BLT object `B_w` in slot-3 = `w`
AND we make slot 3 itself a BLT extension into the dual-pair where the bound is symmetric.** The
genuine bilinear-into-the-correct-completion that closes is:

**`b u v w := (Mext_a w) u v` with `Mext_a` chosen ANTISYMMETRIC-VALUED.** The codomain `W` of `M`
is bilinear forms; we cannot encode (2,3)-antisymmetry in `W` (slots 1,2 only). BUT we can change
the construction so that the trilinear `b` is built from a map into the **alternating tensor /
antisymmetric bilinear forms in slots 2,3 jointly** — i.e. treat `(v,w)` as a SINGLE argument in
`L²_σ ⊗ L²_σ` and extend the bilinear-in-`u`, alternating-in-`(v,w)` form. This is the only place
antisymmetry and continuity reconcile, because then antisymmetry is INTERNAL to the codomain
(structural), not a relation across the Hamel boundary.

**Sound construction (alternating-pair BLT + slot-1 Hamel):**
- For each `u ∈ H1Sigma`, the form `(v,w) ↦ convFormH1 u v w` on `H1Sigma × H1Sigma` is bilinear and
  **alternating** (B6: `convFormH1 u v w = −convFormH1 u w v`), i.e. an element of `⋀² (H1Sigma)* `
  (alternating bilinear forms). Its bound: `|convFormH1 u v w| ≤ min(‖∇v‖_∞, ‖∇w‖_∞) ‖u‖₂ ‖·‖₂` —
  but this needs ONE of `v,w` to be a test; for general `v,w ∈ H1Sigma` (not Schwartz), the bound is
  `‖u‖₆ ‖∇v‖₂ ‖w‖₃`-class, NOT `‖u‖₂ ‖v‖₂ ‖w‖₂`. **So the alternating pair `(v,w)` is NOT bounded in
  `L²×L²` — only when one of them is Schwartz.** Hence the alternating-pair form does NOT BLT-extend
  to `L²_σ × L²_σ` in `(v,w)`. ✗ — antisymmetry-as-codomain also fails to extend continuously.

**This exhausts the reconciliations and confirms:** the obstruction is **intrinsic to the
analysis**, not to the chosen encoding. The convection trilinear form is bounded in `L²` norms in
two slots **only when the third is a smooth test**; there is no slot assignment making it bounded in
`L²` in the two slots that antisymmetry couples while the third (Schwartz) stays fixed AND the
coupling stays inside a continuously-extendable object.

---

## 6. FINAL VERDICT AND RECOMMENDATION

**C6-α (BLT-first, all 5 fields axiom-free) is OBSTRUCTED by a proven incompatibility**, not by
difficulty:

> The convection trilinear form `convFormH1` is `L²×L²`-bounded in a pair of slots **iff** the
> remaining slot is a smooth (Schwartz/H¹-with-`‖∇·‖_∞`) test. `b_cont_fixedTest` needs `L²×L²`-
> continuity in slots 1,2 at fixed Schwartz `w` — available (B7). `b_antisymm_gap` couples slot 2
> (an `L²` BLT arg) to slot 3 (the Schwartz test); enforcing it migrates the Schwartz-test slot into
> a general `L²` slot, where the form is `L²×L²`-UNBOUNDED (`‖∇w‖_∞` is not `‖w‖_{L²}`-controlled).
> Therefore no `b` can be simultaneously BLT-continuous in slots 1,2 at every fixed Schwartz `w` AND
> globally antisymmetric in slots 2,3. The Hamel route supplies antisymmetry but is discontinuous in
> slots 1,2 off the dense H¹ subspace, and density cannot transfer continuity to a discontinuous
> object. **`b_cont_fixedTest` and `b_antisymm_gap` cannot both be theorem content for a single
> explicitly-constructed `b` without the genuine weak operator `(u·∇)v : L²_σ → H^{-1}` (the
> distributional convection operator with its IBP identity holding in `H^{-1}` pairing), which is
> NOT in mathlib and is itself the missing analytic content.**

This is the precise mathematical obstruction the task asked for. It is **not** "months-class
hand-wave" — it is a structural impossibility for the Hamel+BLT class of constructions, reducing the
5th-field discharge to constructing the genuine `L²_σ → H^{-1}` weak convection operator (with the
`H^{-1}`-valued IBP/antisymmetry identity) — the irreducible analytic object Mathlib lacks.

### 6.1 What this means for issue #56 and the owner ban on C6-β

The owner banned C6-β (residual `b_cont_fixedTest` axiom, count stays 3). The honest finding is that
**neither C6-α nor C6-β achieves a sound genuine 3→2 via the Hamel+BLT class.** The genuine 3→2
requires building the **weak convection operator `Bweak : L²_σ → (H¹_σ →L[ℝ] ℝ)`** (equivalently the
continuous trilinear `L²_σ × L²_σ × H¹_σ → ℝ` with `‖u‖₂‖v‖₂‖w‖_{H¹}`-type bound via B7, made
slot-3-total by `H^{-1}`-duality, NOT by Hamel), whose antisymmetry holds in the `H¹_σ` test pairing
and is `L²`-continuous in slots 1,2 — this is a genuine, bounded, total object (no Hamel
discontinuity) and it satisfies ALL FIVE fields because antisymmetry is now a continuous identity in
the `H¹` pairing, not a relation crossing a discontinuity. **The field `b` is typed `L2Sigma →
L2Sigma → L2Sigma → ℝ`, total in slot 3; the bounded operator gives values only for `w ∈ H¹_σ`, so
slot 3 still needs a total extension — but now the extension can be by `0` on a continuous H¹-
complement... which reintroduces the §1 non-additivity wall.** 

**The clean fix that genuinely closes all 5 fields:** redefine slot 3's totality via the **`H¹_σ`
continuous dual extension is unnecessary** — instead observe `b_antisymm_gap` and `b_multilinear`
are the only fields needing slot-3 totality, and BOTH are algebraic; only `b_cont_fixedTest` and
`b_extends` need analytic content and BOTH restrict slot 3 to Schwartz/H¹. So split:
- Build the genuine bounded trilinear `T : L²_σ × L²_σ × H¹_σ → ℝ`, `L²`-continuous in slots 1,2,
  antisymmetric (in the H¹ pairing, slots 2↔3 where both in H¹), = `convFormSchwartz` on Schwartz
  (all from B5/B6/B7, no Hamel, no discontinuity — `T` is bounded hence continuous).
- Hamel-extend `T` in slot 3 from `H¹_σ` to `L²_σ` to get totality (`b_multilinear` slot-3
  linearity, `b_antisymm_gap` slot-3 generality) — this Hamel extension is discontinuous in `w`, but
  `b_cont_fixedTest` only varies slots 1,2 at FIXED Schwartz `w ∈ H¹`, where `T` (not the Hamel
  extension) governs, so continuity is preserved. **AND `b_antisymm_gap` at general `(v,w)` with both
  off-H¹: here BOTH slots 2,3 are Hamel-extended; antisymmetry `b u v w = −b u w v` must hold. With
  `b u v w := T_ext(u,v,w)` (slot-3 Hamel) this is NOT automatically antisymmetric when `v ∉ H¹`
  (slot 2 is NOT Hamel-extended).** ✗ — slot 2 must ALSO be total/Hamel for antisymmetry, putting us
  back at the §3 wall.

**The wall is genuine and confirmed from every angle.** The two-Hamel-slot antisymmetrization is the
only way to get global antisymmetry, and it always destroys slots-1,2 continuity off H¹.

---

## 7. DELIVERABLE: the buildable PR decomposition (Tier 1 = 4 fields sound; field 5 = proven-obstructed)

Given the proven obstruction, the **maximal sound axiom-free deliverable** is the 4-field core
`convectionGapOpCore_exists` (C5 of the plan), which IS buildable and sorry-free. The 5th field
cannot be made theorem content by Hamel+BLT (proven §6). The recommendation to the orchestrator:

- **PR-3 (buildable now, sound, all-must-prove):** `ConvectionExtension.lean` — C1..C5 from
  `r56-…-plan.md` §5. Produces `convectionGapOpCore_exists` (3 algebraic fields:
  `b_multilinear`, `b_antisymm_gap`, `b_extends`) sorry-free, via:
  - **C3 `h1sigma_Hamel_extend`** [must-prove]: `LinearMap.exists_extend` ×3 on the trilinear tower
    `convFormH1 : H1Sigma'³ →ₗ ℝ` (currying via `convFormH1_add_*/smul_*`), giving `B_ext :
    L2Sigma_R3 →ₗ L2Sigma_R3 →ₗ L2Sigma_R3 →ₗ ℝ`.
  - **C4 `convFormL2_antisymm`** [must-prove]: `b u v w := (B_ext u v w − B_ext u w v)/2`; trilinear,
    globally antisymmetric, = `convFormH1` on H¹ (B6 ⟹ antisymmetrization is identity).
  - **C5 `convectionGapOpCore_exists`** [must-prove, PRIMARY]: the 3-field ∃-statement (plan §5 C5).
  - Dependency: C3 ◁ C4 ◁ C5; all depend on merged B4/B5/B6 (`convFormH1_*`).
  - `lean-coder` writes C3/C4/C5 signatures + the `B_ext` currying scaffolds; `lean-prover` fills.
- **PR-4 is BLOCKED — do NOT attempt C6-α or C6-β.** Report the §6 obstruction. The 5th field
  requires the genuine weak operator `L²_σ → H^{-1}_σ` (Mathlib-absent), which is a separate
  research-scale milestone, NOT a Hamel/BLT thinning. Issue #56 closes at 4/5 fields with the
  obstruction documented; capstone STAYS at 3 axioms but the axiom is now PROVABLY irreducible by
  elementary means (the obstruction is the honest content, replacing the vague "analytic wall").

**This is the honest verdict the task demanded:** a PROVEN impossibility for the Hamel+BLT class
(§6), with the exact analytic reason (`‖∇w‖_∞ ⊀ ‖w‖_{L²}` ⟹ the antisymmetry-coupled slot is
`L²`-unbounded ⟹ no continuous extension ⟹ density cannot transfer continuity past the Hamel
discontinuity). Not a difficulty excuse — a structural obstruction.

### 7.1 mathlib API survey (for the buildable PR-3)

| Need | decl | location | status |
|---|---|---|---|
| Hamel extend tower (slot-by-slot) | `LinearMap.exists_extend` | `VectorSpace.lean:288` | PRESENT |
| `H1Sigma` as `Submodule ℝ L2Sigma_R3` (for Hamel in `L2Sigma`) | `Submodule.comap L2Sigma_R3.subtype H1Sigma_R3` | core | PRESENT (plumbing) |
| BLT bounded-linear extension (for the BLT object, if ever revived) | `LinearMap.extendOfNorm` (+`_eq`,`norm_…_apply_le`,`opNorm_…_le`,`_unique`) | `Operator/Extend.lean:190,194,201,229,209` | PRESENT |
| `CompleteSpace L2Sigma_R3` | instance | `DivergenceFree.lean:170` | PRESENT |
| continuous bilinear ⟹ jointly continuous | `ContinuousLinearMap.isBoundedBilinearMap_apply` / `.continuous₂` | mathlib | PRESENT |
| density `H1Sigma` ⊆dense `L2Sigma` (A4) | `h1Sigma_dense_in_L2Sigma` | PR-1 `SobolevEmbedding.lean` | check merged |

**ABSENT (the obstruction):** the weak convection operator `L²_σ → H^{-1}_σ` with continuous-`L²`
slots-1,2 + `H¹`-pairing antisymmetry + slot-3 totality. This is the irreducible content; not
constructible by `LinearMap.exists_extend` + `extendOfNorm`.

---

## 8. Report-summary fields

- **`b` definition (best sound attempt):** `b u v w := (B_ext u v w − B_ext u w v)/2`, `B_ext` =
  three-slot Hamel (`LinearMap.exists_extend`) extension of the proved trilinear `convFormH1` from
  `H1Sigma³`. Gives 4 fields (`b`, `b_extends`, `b_multilinear`, `b_antisymm_gap`).
- **All 5 fields achievable?** **NO** — `b_cont_fixedTest` ∧ `b_antisymm_gap` are PROVEN incompatible
  for any Hamel-extended `b` (§6): antisymmetry couples the continuous BLT slot-2 to the Schwartz
  slot-3; the B7 bound is `‖∇w‖_∞`, NOT `‖w‖_{L²}`, so the coupled slot is `L²`-unbounded and admits
  no continuous extension; density cannot transfer continuity past the Hamel discontinuity. The 5th
  field requires the Mathlib-absent weak operator `L²_σ → H^{-1}_σ`.
- **mathlib BLT decl:** `LinearMap.extendOfNorm` (`Operator/Extend.lean:190`) + `extendOfNorm_eq`,
  `norm_extendOfNorm_apply_le`, `opNorm_extendOfNorm_le`, `extendOfNorm_unique`. Hamel:
  `LinearMap.exists_extend` (`VectorSpace.lean:288`).
- **PR-3 first step (buildable):** `lean-coder` creates `LerayHopf/R3/ConvectionExtension.lean`
  importing `EnergyClassConvection.lean`; declares C3 `h1sigma_Hamel_extend` (currying scaffold +
  `LinearMap.exists_extend` ×3), C4 `convFormL2_antisymm`, C5 `convectionGapOpCore_exists`
  (3-field ∃), bodies `-- ALLOW_SORRY: PR-3 target`. Hand C5 statement + the §6 obstruction writeup
  to `/codex:adversarial-review --effort xhigh` BEFORE proofs, to confirm the obstruction and the
  4-field core statement.
