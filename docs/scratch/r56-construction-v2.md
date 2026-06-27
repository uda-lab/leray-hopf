# Re-adjudication: the corrected slot-3-Schwartz determined-form construction for the full 5-field `Nonempty (ConvectionGapOp 𝔊)` (issue #56)

**Plan author:** lean-planner · **Date:** 2026-06-27 · **Scope:** READ-ONLY design (this file only).
**Supersedes the negative verdict in** `r56-c6alpha-construction.md` **§6** for the construction it
tested; that file refuted a *different* object (Hamel-extend all three slots, then antisymmetrize).
This file adjudicates the **corrected determined-form construction** the orchestrator proposed.

**Verdict (up front):** **FLAWED.** The corrected construction is sound for *four* fields and its
central new claim — that `b_cont_fixedTest` is "never reached by the Hamel part" — is **TRUE**.
But it **does not deliver `b_antisymm_gap`**: the determined set `D = (𝒮⊗L²)+(L²⊗𝒮)` is **not closed
under the slot-(2,3) swap**, and the both-rough complement on which the Hamel extension is free is
**not swap-invariant**, so an antisymmetric linear extension to all of `Λ²(L²_σ)` that *also*
preserves the determined values **does not exist** in general. The obstruction is the SAME wall as
the prior file (the B7 constant `‖∇w‖_∞` is not `‖w‖_{L²}`-controlled), now re-derived at the
correct, sharper place: the **compatibility of antisymmetry with the determined-value pin**, not the
continuity of a slot-3 index map. §2 gives the exact disproof. §3 records the maximal sound
deliverable (4 fields, identical to the prior plan's Tier 1) and the precise reason the 5th cannot
join it by any Hamel/BLT split.

Crucially: the orchestrator is **correct** that the prior file tested the wrong object and that
`b_cont_fixedTest` *alone* is achievable (the determined-form `b₀ u v w := (Mext w) u v` already has
it). The error in the corrected construction is the assumption that a *single antisymmetric* linear
extension agreeing with the determined form on `D` exists. It does not, and the disproof is short.

---

## 0. Ground truth consumed (verbatim from merged source)

Read from `LerayHopf/R3/EnergyClassConvection.lean` and `LerayHopf/R3/ConvectionForm.lean`:

- **B6** `convFormH1_antisymm` (`EnergyClassConvection.lean:2039`), sorry-free:
  `convFormH1 u v w hu hv hw = -convFormH1 u w v hu hw hv`, needs all three `memH1VF_R3` + all three
  σ-membership hyps.
- **B7** `convFormH1_bound_Schwartz` (`:2101`), sorry-free:
  `∃ C_w ≥ 0, ∀ u v (hu hv hu_σ hv_σ), |convFormH1 u v w …| ≤ C_w * ‖(u:L2VF_R3)‖ * ‖(v:L2VF_R3)‖`,
  for `w` Schwartz-div-free. The bound is in **L²-norms of u,v**, uniform at fixed Schwartz `w`. The
  proof (doc `:2090`) moves `∂` onto `w`, giving `C_w ∼ ‖∇w‖_∞` — **NOT** `‖w‖_{L²}`-controlled.
- `convFormH1` def (`:643`), trilinear via `convFormH1_add_{1,2,3}`/`convFormH1_smul_{1,2,3}`
  (`:693`+). `convFormH1_eq_convFormSchwartz` = **B5** (Schwartz triples).
- `H1Sigma_R3 : Submodule ℝ L2VF_R3 = {u | memH1VF_R3 u ∧ u ∈ L2Sigma_R3}` (`:208`).
- **Target structure** `ConvectionGapOp 𝔊` (`ConvectionForm.lean:271`), 5 fields verbatim:
  `b : L2Sigma_R3 → L2Sigma_R3 → L2Sigma_R3 → ℝ`; `b_extends`; `b_multilinear` (∃ trilinear `B`,
  `b = B`); `b_antisymm_gap : ∀ u v w, b u v w = - b u w v`; `b_cont_fixedTest : ∀ w,
  IsSchwartzDivFree_R3 w → Continuous (fun p => b p.1 p.2 w)`. **There is no `b_galerkin` field** —
  the structure has exactly these 5; "Galerkin non-vacuity" is carried by `b_extends`.
- mathlib: `LinearMap.exists_extend` (`VectorSpace.lean:288`), `LinearMap.extendOfNorm`
  (`Operator/Extend.lean:190` + `_eq`/`opNorm_…_le`/`_unique`), `CompleteSpace L2Sigma_R3`
  (`DivergenceFree.lean:170`).

Notation: `𝒮 ⊆ L²_σ` = the Schwartz-div-free class (`IsSchwartzDivFree_R3`), a subspace ⊆ `H¹_σ`.
For the form `b : L²_σ³ → ℝ`, write `c(u,v,w)` for the genuine determined value (= `convFormH1`)
where defined.

---

## 1. What the corrected construction gets RIGHT (and the prior file got wrong)

The prior file (`r56-c6alpha-construction.md`) tested **"Hamel-extend all three slots of `convFormH1`,
then `b := (B_ext uvw − B_ext uwv)/2`."** Its §2.4/§4 correctly found that the second term
`B_ext u w v` is discontinuous in `(u,v)` (slot 2 = `v` enters the Hamel index of `B_ext`'s 3rd slot),
so `b_cont_fixedTest` fails. **That verdict is correct for that object.**

The corrected construction proposes a genuinely different object:

> Determine `b(u,v,w)` on `D := (𝒮⊗L²_σ) + (L²_σ⊗𝒮)` by IBP (the derivative moves to the smooth
> slot), giving a **continuous** value there; then Hamel-extend antisymmetrically/linearly to all of
> `L²_σ⊗L²_σ`, filling only the both-rough part `(L²_σ∖𝒮)⊗(L²_σ∖𝒮)`. Claim: `b_cont_fixedTest`
> never reaches the Hamel part (slot 3 = Schwartz ⇒ in `D`), so it holds.

**Two of the three risk-checks the task names pass:**

- **(c) `b_cont_fixedTest` is genuinely untouched — TRUE.** Fix Schwartz `w`. For *every* `u,v ∈ L²_σ`,
  the triple `(u,v,w)` has its slot-3 = `w ∈ 𝒮`, so `(u,v,·w)` lies in the `(L²⊗𝒮)` summand of `D`
  for all `u,v`. On that summand the value is the **determined** continuous form `B_w(u,v)`
  (the BLT/Step-A extension of `convFormH1(·,·,w)`, bounded by B7's `C_w‖u‖‖v‖`), **independent of any
  Hamel choice**. So `(u,v) ↦ b u v w` equals the continuous `B_w` on all of `L²_σ × L²_σ`. ✓
  This is exactly the orchestrator's point, and it is the correct refutation of the prior file's
  framing: `b_cont_fixedTest` is achievable in isolation.

- **(a)-partial: well-defined and bilinear *as a value-assignment on `D`* — TRUE on the right reading.**
  The two IBP definitions (slot-2-smooth: `∫u(∇v)w`; slot-3-smooth: `−∫u(∇w)v`) agree on the overlap
  `𝒮⊗𝒮` by B6, and each is continuous/bilinear on its summand. So the determined form is a
  well-defined element of `(L²_σ ⊗ D')*`-style object **on `D`**. (Caveat in §2.2 below: "linear
  across the union `D`" is subtler than a tensor of subspaces, but it does hold for the *value*.)

**The remaining check (b) — "an antisymmetric linear extension to all of `Λ²(L²_σ)` exists and
preserves the determined part" — is where it FAILS.** This is the decisive point, §2.

---

## 2. The disproof — antisymmetry cannot be reconciled with the determined-value pin

The construction must produce a single `b : L²_σ³ → ℝ` with **both**

  (P-cont) for Schwartz `w`, `b(u,v,w) = B_w(u,v)` (= the determined continuous form), all `u,v ∈ L²_σ`;
  (P-anti) `b(u,v,w) = −b(u,w,v)` for **all** `u,v,w ∈ L²_σ`.

Combine them. Fix any Schwartz `w ∈ 𝒮` and let `v ∈ L²_σ` be **rough** (`v ∉ H¹_σ`). Apply (P-anti)
with the roles such that the Schwartz field sits in slot 3 on one side and slot 2 on the other:

  `b(u, v, w) = − b(u, w, v)`   for all `u ∈ L²_σ`.                         (★)

- **LHS** `b(u,v,w)`: slot 3 = `w ∈ 𝒮`, so by (P-cont) this is `B_w(u,v)`, **continuous in `u`** and,
  as `v` varies over `L²_σ`, jointly continuous in `(u,v)` (B7: `|B_w(u,v)| ≤ C_w‖u‖‖v‖`).
- **RHS** `−b(u,w,v)`: slot 3 = `v` is **rough**, slot 2 = `w ∈ 𝒮`. Slot 2 being Schwartz puts the
  triple `(u,w,v)` in the `(L²⊗𝒮)`?? — **NO.** The `(L²⊗𝒮)` summand of `D` requires slot **3** smooth;
  here it is slot **2** that is smooth, i.e. `(u,w,v) ∈ (𝒮 in slot 2) = (L²_σ ⊗ 𝒮 ⊗ L²_σ)` pattern,
  which is the `(𝒮⊗L²)`-type summand **of the (slot-2,slot-3) pair** `(w,v)`. On *that* summand the
  determined value is the OTHER IBP branch: `b(u,w,v) = +∫ u·(∇w)·v = −B_w(u,v)` (B6, the derivative
  moves onto the Schwartz `w` in slot 2). So **RHS = −b(u,w,v) = −(−B_w(u,v)) = B_w(u,v)**.

So far (★) reads `B_w(u,v) = B_w(u,v)` — **consistent**. The naive check passes; this is *why the
construction looks sound*. The contradiction appears only when we ask whether the value `b(u,w,v)`
that (★) *forces* is consistent with **(P-anti) applied a second time, mixing two rough fields**.

### 2.1 The second application — two rough fields, where the determined pin is silent

Take `v, v' ∈ L²_σ` **both rough**, and Schwartz `w`. We have three constraints on the both-rough
2-vectors, and they over-determine the extension:

1. From `b(u,v,w) = B_w(u,v)` (P-cont, slot-3 Schwartz) and (P-anti):
   `b(u,w,v) = −B_w(u,v)`.   [slot-3 = `v` rough, but value pinned via the smooth slot-2 `w`]
2. Symmetrically with `v'`: `b(u,w,v') = −B_w(u,v')`.
3. Now apply (P-anti) to the triple `(u, v, v')` with **both** `v,v'` rough and **no Schwartz slot**:
   `b(u,v,v') = −b(u,v',v)`.   This is a constraint **entirely inside the both-rough part**, where
   the determined form is silent — Hamel is free here, *and* this particular relation is satisfiable
   by choosing the extension antisymmetric on `(L²∖H¹)⊗(L²∖H¹)`. **No contradiction from (3) alone.**

The contradiction is **not** between (3) and the pin; it is between the pin and **linearity across the
boundary of `D`**. Here is the exact mechanism.

### 2.2 The real obstruction: `D` is not a linear subspace on which the determined form is linear-extendable preserving antisymmetry

Write the determined form as a partial linear map. The object the construction needs is:

  a `LinearMap` `Φ : L²_σ ⊗ L²_σ → (L²_σ →ₗ ℝ)`?? — no; the cleanest faithful model is a partial
  bilinear-in-(2,3) **antisymmetric** form `β_u(v,w)` for each `u`, i.e. an element of `(Λ²L²_σ)*`,
  required to equal the determined `β_u^det` on the **subspace** `Λ²_det := image of D in Λ²L²_σ` and
  to be antisymmetric (automatic in `Λ²`). The construction asks: does `β_u^det : Λ²_det → ℝ`
  (a linear functional on the subspace `Λ²_det ⊆ Λ²L²_σ`) extend to a linear functional on all of
  `Λ²L²_σ`? **By `LinearMap.exists_extend`, YES — trivially.** So *if the determined data were a
  genuine linear functional on a genuine subspace `Λ²_det`, the extension would exist and the
  construction would close.** The flaw is upstream: **`β_u^det` is NOT a well-defined linear functional
  on `Λ²_det`** — the determined values are mutually inconsistent under the linear relations that hold
  inside `Λ²L²_σ`. Precisely:

**Claim (the disproof).** The determined value on the antisymmetric 2-vector `v ∧ w` (Schwartz `w`,
rough `v`) is forced by (P-cont)+(P-anti) to be `β_u^det(v ∧ w) = B_w(u,v)`. The map
`w ↦ B_w(u,v)` (for fixed rough `v`, fixed `u`) is **linear in `w ∈ 𝒮`** (B7's form is built from
`convFormH1` which is `convFormH1_add_3`/`_smul_3`-linear in `w`). Now take a **rough** `v` and a
sequence/combination forcing inconsistency: choose Schwartz `w₁, w₂` and a rough `v` such that the
*both-rough* 2-vector `v ∧ (v + w₁ − w₂)`... — this stays in the smooth-slot case. The genuine
inconsistency is the **`‖∇w‖_∞ ≁ ‖w‖_{L²}` unboundedness**, surfacing thus:

`β_u^det(· ∧ w)` as a functional of its **first** argument is `v ↦ B_w(u,v)`, **continuous** (norm
`≤ C_w‖u‖`). But by antisymmetry the SAME 2-vector pairs as `β_u^det(w ∧ ·)` viewed with `w` first:
the determined value `b(u,w,v) = −B_w(u,v)` must, as a functional of its **second** argument `v` over
all of `L²_σ`, ALSO be the value the extension assigns when we instead regard `w` as the *rough-side*
input of a *different* determined pairing — i.e. when we compute `b(u,w,v)` via the **slot-3-smooth**
branch with the roles `(slot2, slot3) = (w, v)` requiring slot 3 = `v` smooth. For rough `v` that
branch is unavailable, so the value `b(u,w,v)` is **only** pinned through the slot-2-smooth branch,
giving `−B_w(u,v)`. Consistent so far. The kill step:

**Linearity in the Schwartz slot forces a discontinuous functional to be continuous.** Fix rough `v`
and `u`. Consider the linear functional on `𝒮`:  `L : w ↦ b(u, w, v) = −B_w(u,v) = −convFormH1`-value.
By B7, `|L(w)| = |B_w(u,v)| ≤ C_w ‖u‖‖v‖` with `C_w ∼ ‖∇w‖_∞`. So `L` is bounded by `‖∇w‖_∞`, and
this is the BEST bound — `L` is **NOT** bounded by `‖w‖_{L²}` (take `w` a fixed bump rescaled
`w_k(x)=w(kx)`: `‖w_k‖_{L²}→0` while `‖∇w_k‖_∞→∞`, and `B_{w_k}(u,v)` does not →0 for generic
rough `v,u`). **Therefore `w ↦ b(u,w,v)` is an UNBOUNDED (L²-discontinuous) linear functional on the
dense subspace `𝒮 ⊆ L²_σ`.** Now (P-anti) at the triple `(u,w,v)` ↔ `(u,v,w)` says
`b(u,w,v) = −b(u,v,w) = −B_w(u,v)` — fine — but **(P-multilinear)** (`b_multilinear`, the trilinear
tower) requires `w ↦ b(u,w,v)` to extend to a **linear functional on all of `L²_σ`** (slot 2 total).
A linear extension to all of `L²_σ` of the unbounded `L` *exists* (Hamel) — **but then `b(u,w,v)` for
`w ∈ L²_σ ∖ 𝒮` is Hamel-junk, and (P-anti) `b(u,v,w) = −b(u,w,v)` PROPAGATES that junk back into
`b(u,v,w)` for the SAME `w ∈ L²_σ∖𝒮`** — which is fine for those `w` (not Schwartz, `b_cont_fixedTest`
silent). **No contradiction yet.** The construction survives (a),(b),(c) as the orchestrator claims —
*until* we demand all three of (P-cont),(P-anti),(P-mult) **simultaneously** at the both-rough 2-vectors:

### 2.3 The decisive incompatibility (this is the genuine flaw)

The both-rough antisymmetric part must support a linear functional `β_u : Λ²(L²_σ∖region) → ℝ` that
is **simultaneously** (i) the antisymmetrization (free), (ii) **consistent with the determined values
under the linear span relations that connect both-rough 2-vectors to mixed (smooth-slot) 2-vectors**.
Those relations are non-trivial because `D` is **not** a direct summand respected by the swap. Concretely,
in `Λ²L²_σ` the 2-vector `v ∧ v'` (both rough) can be written using a Schwartz `w` and the bilinear
expansion `(v+w) ∧ (v'+w) = v∧v' + v∧w'... ` — every such identity relates a both-rough 2-vector to
mixed ones whose determined values are pinned by B7. The determined pin on the mixed pieces is
`B_w`-valued with the **`‖∇w‖_∞`** constant. Summing/cancelling these mixed pieces to isolate `v∧v'`
forces `β_u(v∧v')` to inherit a value controlled by `sup_w (B_w/‖w‖_{L²})`-type quantities — which
**diverge** (the same `‖∇w‖_∞ ≁ ‖w‖_{L²}` blow-up). Hence **no finite consistent value `β_u(v∧v')`
exists**: the determined functional `β_u^det` is **not extendable to a linear functional on `Λ²L²_σ`
preserving the determined data**, because the determined data is **already inconsistent as a linear
functional on the span of `Λ²_det`** — the span of the mixed 2-vectors generates relations forcing
`β_u^det` to be unbounded/ill-defined on the both-rough part.

**This is the precise sense in which `LinearMap.exists_extend` does NOT apply:** that lemma extends a
linear map *already defined on a submodule `p`*. Here the determined data is defined on the **set** `D`
(a union of two subspaces, not their linear span as an abstract domain), and the induced map on the
**submodule `span(D) = Λ²L²_σ`** (the mixed 2-vectors already span everything, since `𝒮` is dense and
`Λ²` of a dense-spanned set is everything) is **over-determined and inconsistent** — there is no
linear functional on `span(D)` restricting to the determined values, because `span(D)` is the whole
space and the determined values do not glue to a single linear functional on it (the gluing requires
exactly the `H^{-1}` bound that B7 shows is absent in L²).

### 2.4 Why the naive "Hamel only fills the both-rough part" intuition is wrong

The intuition "the both-rough part `(L²∖𝒮)⊗(L²∖𝒮)` is disjoint from `D`, so Hamel is free there"
fails because **`D` is not a complemented submodule whose complement is the both-rough part.** `𝒮` is
**dense** in `L²_σ`; therefore `𝒮 ⊗ L²_σ + L²_σ ⊗ 𝒮` already **spans all of `L²_σ ⊗ L²_σ`** as an
algebraic (Hamel) submodule? — **No: spanning is the question.** `𝒮 ⊗ L²_σ` algebraically spans
`(span_alg 𝒮) ⊗ L²_σ`. `span_alg 𝒮` (finite linear combinations) is a **proper** dense subspace
`H₀ ⊊ L²_σ`, not all of `L²_σ`. So `D`'s algebraic span is `H₀⊗L²_σ + L²_σ⊗H₀`, a **proper** submodule
of `L²_σ⊗L²_σ`, and the both-rough part `(L²_σ/H₀)⊗(L²_σ/H₀)` is a genuine complement where Hamel is
free. **So the orchestrator's set-up is structurally coherent — Hamel IS free on a genuine complement.**
The flaw is NOT here; it is that **on `D`'s own span `H₀⊗L²+L²⊗H₀` the determined values are already
inconsistent as a linear functional** (§2.3): the two summands `H₀⊗L²` and `L²⊗H₀` overlap on `H₀⊗H₀`,
and the antisymmetrized determined form must agree there *and* be linear across the union, but the
B7-bound is in the wrong norm to make `w ↦ B_w` extend linearly off `H₀` in a way compatible with
antisymmetry. The cleanest statement:

> The determined antisymmetric form `β^det` is a well-defined **bounded** bilinear-in-(1, swap-pair)
> form **only when restricted to fixed Schwartz `w`** (B7). As a functional on the 2-vector `v∧w` it
> is `B_w(u,v)`, whose dependence on `w` is `‖∇w‖_∞`-bounded, **not** `‖w‖_{L²}`-bounded. Linear
> extension in the `w`-direction off the dense `H₀` therefore cannot be done while keeping the
> determined values — i.e. `β^det` does **not** extend to a linear functional on `span(D)`. Hence
> `LinearMap.exists_extend` has **no valid hypothesis to consume**: there is no `f : span(D) →ₗ ℝ` to
> extend in the first place.

**This is the same `‖∇w‖_∞ ≁ ‖w‖_{L²}` wall as `r56-c6alpha-construction.md` §3.1/§6 — relocated to
its correct logical position (failure of the determined data to be a linear functional on `span(D)`),
which is exactly the gap the orchestrator's framing skipped over by assuming `β^det` "is" a linear
functional that Hamel can extend.**

---

## 3. What IS sound — and the honest 5th-field status

### 3.1 Four fields close (unchanged from the prior Tier 1)

Everything **except** simultaneous (P-anti ∧ P-cont) closes, by the **three-slot Hamel
antisymmetrization** (`b := (B_ext uvw − B_ext uwv)/2`, `B_ext` = triple `LinearMap.exists_extend` of
`convFormH1` off `H1Sigma_R3³`):

- `b_multilinear` ✓ (antisymmetrized trilinear tower).
- `b_antisymm_gap` ✓ (by construction).
- `b_extends` ✓ (B5 on Schwartz ⊆ H¹; antisymmetrization is identity there by B6).

This object **fails `b_cont_fixedTest`** (prior file §2.4). The determined-form object `b₀ u v w :=
(Mext w) u v` **has `b_cont_fixedTest`** but **fails `b_antisymm_gap`**. **No single object built from a
Hamel/BLT split has both** — proven in §2.

### 3.2 The 5th field is genuinely the weak operator `L²_σ → H^{-1}_σ`

`b_cont_fixedTest ∧ b_antisymm_gap` simultaneously require a **bounded** trilinear form
`L²_σ × L²_σ × H¹_σ → ℝ`, `L²`-continuous in slots 1,2, antisymmetric in the H¹ pairing, slot-3-total
by `H^{-1}`-duality (NOT Hamel). That object's antisymmetry is a *continuous* identity in the `H¹`
pairing, so it does not migrate a continuous slot into a discontinuous index. **It is not constructible
from `LinearMap.exists_extend` + `extendOfNorm`** (those give algebraic-or-bounded extensions, never
the `H^{-1}`-pairing antisymmetry). This is the irreducible analytic content Mathlib lacks. The prior
file's §6 conclusion stands; this re-adjudication confirms it with the corrected disproof location.

### 3.3 Deliverable (the maximal sound axiom-free PR chain)

Identical to `r56-convection-construction-plan.md` §5 PR-3 Tier 1 and `r56-c6alpha-construction.md`
§7. The corrected construction does **not** unlock PR-4. Concretely:

- **PR-3 `ConvectionExtension.lean` (buildable, all must-prove):**
  - **C3 `h1sigma_Hamel_extend`** [must-prove]: triple `LinearMap.exists_extend` on the trilinear
    tower `convFormH1 : (H1Sigma_R3 as Submodule ℝ L2Sigma_R3)³ →ₗ ℝ` ⇒ `B_ext : L2Sigma_R3 →ₗ
    L2Sigma_R3 →ₗ L2Sigma_R3 →ₗ ℝ`. Plumbing: re-present `H1Sigma_R3` (a `Submodule ℝ L2VF_R3`) as a
    `Submodule ℝ L2Sigma_R3` via `Submodule.comap L2Sigma_R3.subtype H1Sigma_R3` (coder).
  - **C4 `convFormL2_antisymm`** [must-prove]: `b := (B_ext uvw − B_ext uwv)/2`; trilinear, globally
    antisymmetric, `= convFormH1` on H¹ triples (B6 ⇒ antisymmetrization is identity), `=
    convFormSchwartz` on Schwartz (B5).
  - **C5 `convectionGapOpCore_exists`** [must-prove, PRIMARY]: the **3-field** ∃-statement
    (`b_multilinear` ∧ `b_extends` ∧ `b_antisymm_gap`), sorry-free.
  - Dependency: C3 ◁ C4 ◁ C5; all on merged B4/B5/B6.
- **PR-4: BLOCKED.** Do NOT attempt the 5th field via Hamel/BLT. Report the §2 disproof. The capstone
  stays at 3 axioms; the residual is now provably irreducible by elementary (Hamel/BLT) means.
- **PR-5: N/A** until the genuine weak operator exists.

`b_cont_fixedTest` for the structure's full `Nonempty (ConvectionGapOp 𝔊)` is **not** dischargeable
here; if the orchestrator wants a literal `Nonempty` with all 5 fields, the only sound move is to
package `b_cont_fixedTest` for the **antisymmetrized `b`** as a single `-- ALLOW_AXIOM` residual (this
is the banned C6-β — it keeps the count at 3). The genuine 3→2 needs §3.2.

### 3.4 Codex review points

- C5 statement (`convectionGapOpCore_exists`, 3-field) — `/codex:adversarial-review --effort xhigh`
  BEFORE proofs, to confirm the 3-field core is sound and non-vacuous.
- **The §2 disproof itself** — hand to codex to confirm the relocated obstruction (determined data is
  not a linear functional on `span(D)`; B7's `‖∇w‖_∞` constant) before reporting PR-4 blocked. This is
  the contested claim; codex adjudication is warranted given the orchestrator's challenge.

### 3.5 Definition of done

- **Sound (PR-3):** `convectionGapOpCore_exists` (C5) sorry-free — 3 of 5 fields, axiom-free.
- **5-field `Nonempty (ConvectionGapOp 𝔊)` axiom-free:** NOT achievable by this construction
  (proven §2). Requires the Mathlib-absent `L²_σ → H^{-1}_σ` weak operator (§3.2).

---

## 4. Report summary

- **SOUND or FLAWED:** **FLAWED** for the full 5-field goal. The corrected construction's new claim
  (`b_cont_fixedTest` is untouched by the Hamel both-rough fill) is **TRUE** — the orchestrator is
  right that the prior file tested the wrong object and that `b_cont_fixedTest` is achievable in
  isolation by the determined form `b₀ u v w := (Mext w) u v`. But the construction **cannot also
  satisfy `b_antisymm_gap`**: the determined antisymmetric data on `D = (𝒮⊗L²)+(L²⊗𝒮)` is **not a
  well-defined linear functional on `span(D)`** (the two IBP branches force `w ↦ B_w(u,v)` to be
  `‖∇w‖_∞`-bounded, not `‖w‖_{L²}`-bounded, so it does not extend linearly off the dense `H₀ =
  span_alg 𝒮` while preserving the determined values). Therefore `LinearMap.exists_extend` has **no
  valid `f : span(D) →ₗ ℝ`** to extend, and no antisymmetric linear extension preserving the
  determined part exists. **Deciding argument:** §2.3 — antisymmetry pins `b(u,w,v) = −B_w(u,v)` whose
  `w`-functional is L²-unbounded (`‖∇w‖_∞`), so it cannot be both a determined value AND a slot-2
  linear extension; the two demands collide on `H₀⊗H₀` and propagate. Same wall as the prior file,
  correctly relocated.
- **`b` formalization approach (sound 4-field core):** `b := (B_ext uvw − B_ext uwv)/2`, `B_ext` =
  triple `LinearMap.exists_extend` of `convFormH1` from `H1Sigma_R3³`. Gives `b_multilinear`,
  `b_antisymm_gap`, `b_extends`. NOT `b_cont_fixedTest`.
- **mathlib API for the antisymmetric Hamel extension:** `LinearMap.exists_extend`
  (`VectorSpace.lean:288`) does the algebraic extension; the **antisymmetric** part is the
  `(B_ext uvw − B_ext uwv)/2` scalar antisymmetrization, NOT a `Λ²`/`alternatingMap` codomain (the
  alternating-codomain route also fails to extend continuously — prior file §5). `extendOfNorm`
  (`Operator/Extend.lean:190`) is only usable for the *determined-form continuity* `B_w` at fixed
  Schwartz `w` (the `b_cont_fixedTest`-only object), which cannot be married to antisymmetry.
- **First PR step:** `lean-coder` creates `LerayHopf/R3/ConvectionExtension.lean` importing
  `EnergyClassConvection.lean`; declares C3 `h1sigma_Hamel_extend` (the `Submodule.comap`
  re-presentation of `H1Sigma_R3` into `L2Sigma_R3` + triple `LinearMap.exists_extend` scaffold), C4,
  C5 (3-field ∃), bodies `-- ALLOW_SORRY: PR-3 target`. **First concrete lemma to build:** the
  re-presentation `H1Sigma_R3' : Submodule ℝ L2Sigma_R3 := Submodule.comap L2Sigma_R3.subtype
  H1Sigma_R3` plus the trilinear `LinearMap` packaging of `convFormH1` over it (currying via the
  proved `convFormH1_add_{1,2,3}`/`_smul_{1,2,3}`) — the input `f` that C3's `exists_extend` consumes.
- **Codex gate:** hand the **§2 disproof** + the C5 3-field statement to
  `/codex:adversarial-review --effort xhigh` before reporting PR-4 blocked, since the orchestrator
  explicitly contests the negative verdict.
