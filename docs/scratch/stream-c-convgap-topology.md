# Stream C — Corrected `ConvectionGap` topology contract

**Stream:** `stream-c-convection-operator` (Tier G repair, round 4)
**File to edit (lean-coder, signatures only):** `LerayHopf/R3/ConvectionForm.lean`
**Do NOT edit:** `SolutionInterfaces.lean`, `ConvectionOperator.lean`, `TrilinearEstimate.lean`, `Regularity.lean`.
**Status of this doc:** statement-level contract only. No Lean edited by the planner.

---

## 0. Why round 3 failed (the wall, restated precisely)

Round-3 `ConvectionGap.b_cont` asserted

```
b_cont : Continuous (fun p : L2Sigma_R3 × L2Sigma_R3 × L2Sigma_R3 => b p.1 p.2.1 p.2.2)
```

i.e. **joint continuity of `b` in the pure L²_σ × L²_σ × L²_σ product topology.**
Combined with `b_extends` (b = `convFormSchwartz` on the dense Schwartz-div-free class),
this asserts a continuous extension of the Schwartz convection form to all of
L²×L²×L² **in the L² topology**.

That extension **does not exist**. The sibling Tier-S file
(`ConvectionOperator.lean`, lines 19–26) states, and R3-d
(`convIntegralSchwartz_bound_sup`) proves, that `b(u,v,w) = ∫(u·∇)v·w` is
**unbounded in pure L² × L² × L² norms**: the genuine bound needs an L∞ (or H¹)
slot for the differentiated/undifferentiated factor. A function that is genuinely
unbounded on a dense subset in a given topology has **no** continuous extension in
that topology. So `b_cont` is **false for the real convection form** — discharging it
later is impossible, and the conditional `R3NSForms_of_gap` would be vacuously
"satisfiable" only by a fictitious `b`. This is an over-strength encoded into the gap.

The fix below replaces the false pure-L² joint continuity with the **genuinely available
analytic facts in the topology where they hold**, matched slot-by-slot to what
`R3NSForms` actually needs — no more, no less.

---

## 1. Exact `R3NSForms` findings (`SolutionInterfaces.lean` lines 203–253)

`R3NSForms (𝔊 : R3GalerkinScheme)` is a structure. The convection form and its
required properties:

- **`b : L2Sigma_R3 → L2Sigma_R3 → L2Sigma_R3 → ℝ`** — total, on **all** of `L²_σ(ℝ³)`,
  not just Schwartz fields. (line 205)
- **`b_antisymm`** : `∀ u v w : L2Sigma_R3, b u v w = - b u w v` — totally quantified. (207)
- **`b_add_{1,2,3}`** : additivity in each slot, totally quantified over `L2Sigma_R3`. (209–213)
- **`b_smul_{1,2,3}`** : ℝ-homogeneity in each slot, totally quantified. (215–219)
- **`b_bound`** (the load-bearing field — lines 227–229):
  ```
  ∀ (w : L2Sigma_R3), IsSchwartzDivFree_R3 w →
    ∃ C : ℝ, ∀ (u v : L2Sigma_R3),
      |b u v w| ≤ C * ‖(u : L2VF_R3)‖ * ‖(v : L2VF_R3)‖
  ```
  **CRITICAL READING.** The bound is **NOT** a joint L²-continuity claim, and **NOT**
  symmetric across slots:
  - the test slot `w` is restricted to **`IsSchwartzDivFree_R3 w`** (a Schwartz field),
    and the constant `C = C(w)` is allowed to depend on that fixed `w`
    (it is the sup-norm of `∇w`, finite only because `w` is Schwartz);
  - **only slots 1 and 2** (`u`, `v`) are controlled by the **L² norm**
    `‖·‖_{L2VF_R3}`, and they range over **all** of `L2Sigma_R3`.
  So `R3NSForms` itself **never** asserts an L²-bound in the third slot, and **never**
  asserts a bound for non-Schwartz `w`. The convection form's genuine third-slot
  unboundedness is *already respected* by `R3NSForms`: it asks for control only at fixed
  Schwartz `w`.
- **`b_galerkin`** (228–253): the non-vacuity pin — on fields with Schwartz component
  representatives (`toLp` of `ψu ψv ψw`), `b u v w = convIntegralSchwartz ψu ψv ψw`.

**Consumer check (where `b` is actually used):**
- `r3Evolution` (300–311) sets `convForm := F.b` and `isTest := IsSchwartzDivFree_R3`.
- `galerkin_limit_passage_R3` (496–515) kills the nonlinear error "via `b_bound`."
  The test functions are Schwartz (rapid decay); `b_bound` is the only analytic property
  of `b` consumed downstream, and it is consumed **only at Schwartz `w`** in slots 1,2.
- `GalerkinSolutionData_R3.u_ode` (347–350) uses `F.b (u t) (u t) w` with
  `(w : L2VF_R3) = 𝔊.P n w` — i.e. Galerkin test fields, which by
  `R3GalerkinScheme.range_schwartz` are component-wise Schwartz. So `w` is Schwartz there too.

**Net:** every downstream use of `b` puts the *test slot* `w` in the Schwartz class. The
total quantifier over arbitrary `w : L2Sigma_R3` appears only in the *algebraic* fields
(`b_antisymm`, `b_add_*`, `b_smul_*`), and `b_bound` is honestly Schwartz-`w`-only.

---

## 2. Exact Tier-S and R3-d bound norms

### Tier-S (`ConvectionOperator.lean`)

- `convFormSchwartz u v w hu hv hw : ℝ` — defined for `u v w : L2Sigma_R3` each carrying
  `IsSchwartzDivFree_R3`. It equals `convIntegralSchwartz` on the chosen Schwartz witnesses.
- `convFormSchwartz_bound` (lines 205–211) — the proven `b_bound` shape, **identical** to
  `R3NSForms.b_bound`:
  ```
  ∀ (w : L2Sigma_R3), IsSchwartzDivFree_R3 w →
    ∃ C, ∀ (u v) (hu hv), |convFormSchwartz u v w hu hv hw| ≤ C * ‖u‖ * ‖v‖
  ```
  Bounded slots = `u, v` in **L²**; constant carried by the fixed **Schwartz** `w`.
- `convFormSchwartz_antisymm`, `_add_{1,2,3}`, `_smul_{1,2,3}` — all quantified over the
  **Schwartz-div-free class only** (every argument carries an `IsSchwartzDivFree_R3` hyp).
- `convFormSchwartz_eq_witness` — the pin to `convIntegralSchwartz`.

### R3-d (`TrilinearEstimate.lean`) — the classically-available bounds

- `convIntegralSchwartz_bound_H1` (B2, lines 361–369):
  ```
  |conv ψu ψv ψw| ≤ (∑_a ‖ψu_a‖_{L²}) · (∑_{a,i} ‖∂_a ψv_i‖_{L²}) · (∑_i ‖ψw_i‖_{L∞})
  ```
  Norms: slot u = **L²**, slot v = **L² of the gradient (H¹ seminorm)**, slot w = **L∞**.
- `convIntegralSchwartz_bound_sup` (C3, lines 725–739), under div-free `hdiv`:
  ```
  |conv ψu ψv ψw| ≤ (∑_{i,a} ‖∂_a ψw_i‖_{∞-seminorm}) · (∑_a ‖ψu_a‖_{L²}) · (∑_i ‖ψv_i‖_{L²})
  ```
  Norms: slot u = **L²**, slot v = **L²**, slot w = **L∞ of the gradient**.

**Conclusion on norms.** In **every** proven bound, **exactly two** factors are L² and the
**third** factor lives in L∞/H¹ (an essentially-bounded-derivative slot). There is **no**
proven (nor true) bound with all three factors in L². The sup/H¹ slot is mandatory.
This is exactly why round-3 pure-L² joint continuity is false.

### Regularity.lean (the energy/H¹ topology available)

- `memH1VF_R3 (u : L2VF_R3) : Prop` — H¹ membership via `MemSobolev 1 2` per component.
- `viscousFormSq_R3 ν u = ν · ∑_j ∫ (2π)²‖ξ‖²‖𝓕 u_j ξ‖²` — the spectral `ν‖∇u‖²_{L²}`,
  i.e. the squared H¹-seminorm (× ν). This is the genuine "energy/H¹ norm" the project
  carries. There is **no** `H¹` *topology* instance on `L2Sigma_R3` (the carrier is the L²
  subspace `L2Sigma_R3` with its L² norm); `memH1VF_R3` / `viscousFormSq_R3` are
  *predicates/functionals*, not a topology. This matters for §3.

---

## 3. The reconciled correct topology / honesty verdict

Two facts pull in opposite directions:

1. The convection trilinear form is **genuinely bounded only when each slot is measured in
   the right norm** — two L² slots + one L∞/H¹ slot (R3-d). In particular it is
   **continuous on H¹ × H¹ × H¹** (Ladyzhenskaya), **not** on L² × L² × L².
2. But `R3NSForms.b` is **typed on L²_σ** with the **L² norm**, and `R3NSForms.b_bound`
   only ever needs the two-L²-slots-at-fixed-Schwartz-`w` form. There is **no H¹ topology
   on `L2Sigma_R3`** in the repo to state "continuity in the H¹ topology" against.

**Therefore the honest reconciliation is NOT "switch `b_cont` to an H¹-topology
continuity field"** (there is no such topology instance to be continuous *for*, and
`R3NSForms` is typed in L²). The honest reconciliation is:

> **Replace the single false joint-continuity field with two slot-asymmetric fields that
> mirror exactly the asymmetry already present in `R3NSForms`:**
>
> - **a continuity field restricted to the first two (L²) slots, at a fixed Schwartz
>   test `w`** — which IS true (the form is L²-bilinear-bounded in `(u,v)` for fixed
>   Schwartz `w`, by R3-d C3); this is what drives `b_bound`, `b_add_1/2`, `b_smul_1/2`,
>   `b_antisymm` and `b_add_3/b_smul_3` *at Schwartz `w`*;
>
> - **plus the third-slot algebra over arbitrary `w` handled NOT by continuity but by a
>   direct multilinear-extension field** (see §4): we cannot get third-slot control from
>   any genuine continuity, so we do not claim it; instead the gap supplies the third-slot
>   linear-extension data explicitly, as the honest residual of the missing operator.

This keeps the gap **satisfiable** (every field is true for the real convection form) and
**thinner-where-honest / explicitly-strengthened-where-not** (see §6 verdict).

---

## 4. Field-by-field spec for the corrected `ConvectionGap`

`structure ConvectionGap (𝔊 : R3GalerkinScheme)`. All fields are data/Prop, **no new
`axiom`**. Names are stable; only `b_cont` is removed and replaced.

### F1. `b` (unchanged)
```
b : L2Sigma_R3 → L2Sigma_R3 → L2Sigma_R3 → ℝ
```
The total candidate convection form on all of `L²_σ(ℝ³)`. **Scaffold data field.**

### F2. `b_extends` (unchanged) — the operator-extension frontier
```
b_extends : ∀ (u v w : L2Sigma_R3)
  (hu : IsSchwartzDivFree_R3 u) (hv : IsSchwartzDivFree_R3 v) (hw : IsSchwartzDivFree_R3 w),
  b u v w = convFormSchwartz u v w hu hv hw
```
On the Schwartz-div-free class, `b` restricts to the proven Tier-S functional. This is the
only link between `b` and the genuine `∫(u·∇)v·w`. **Scaffold Prop field.**

### F3 (REPLACES `b_cont`). `b_cont_fixedTest` — joint L²-continuity in slots 1,2 at fixed Schwartz `w`
```
b_cont_fixedTest : ∀ (w : L2Sigma_R3), IsSchwartzDivFree_R3 w →
  Continuous (fun p : L2Sigma_R3 × L2Sigma_R3 => b p.1 p.2 w)
```
**Intent / why TRUE:** for a fixed Schwartz `w`, R3-d C3
(`convIntegralSchwartz_bound_sup`) gives `|b u v w| ≤ C(w)·‖u‖·‖v‖` with `C(w) < ∞`; a
bounded bilinear map on a normed space is continuous, and it extends from the dense
Schwartz `(u,v)` to all `(u,v)` by uniform continuity **in the two L² slots** (the
bilinear form is uniformly continuous on L²×L² *for fixed Schwartz `w`*, unlike the full
trilinear form). This is the genuine, satisfiable continuity — it lives in the **L²
topology of the first two slots only**, exactly the topology `R3NSForms.b_bound` is
stated in.
**Codex note:** This is the corrected continuity. It is strictly weaker than round-3
`b_cont` (no third-slot / arbitrary-`w` continuity), and it is TRUE for the real form.

### F4 (NEW). `b_linExt_3` — third-slot affine/linear extension to arbitrary `w`
```
b_linExt_3 : ∀ (u v : L2Sigma_R3),
  ∃ (T : L2Sigma_R3 →ₗ[ℝ] ℝ),
    (∀ w : L2Sigma_R3, b u v w = T w) ∧
    (∀ w : L2Sigma_R3, IsSchwartzDivFree_R3 w →
      T w = convFormSchwartz u v w · · ·)   -- via b_extends; see derivation note
```
**Intent.** This is the **honest residual of the missing weak-`(u·∇)v` operator** in the
third slot: it states that for each `(u,v)`, the map `w ↦ b u v w` is an **ℝ-linear
functional on all of `L²_σ`** that agrees with the proven Schwartz form on the dense
Schwartz class. We **cannot** get third-slot additivity/homogeneity over arbitrary `w`
from any L² continuity (the form is unbounded there), so we supply third-slot linearity
**directly** as the gap datum. This is the genuine analytic frontier: the existence of the
convection functional as a (possibly unbounded) **linear** functional in the test slot.

> **Implementation note for lean-coder.** The second conjunct's RHS needs the
> `IsSchwartzDivFree_R3 u/v/w` hypotheses to mention `convFormSchwartz`. Since `u v` here
> are arbitrary (not necessarily Schwartz), state the agreement only as
> `b u v w = T w` (first conjunct, total) plus linearity of `T`. The Schwartz-agreement is
> then obtained downstream from `b_extends` (F2) at Schwartz `u v w`, so the second
> conjunct can be DROPPED — keep F4 minimal:
> ```
> b_linExt_3 : ∀ (u v : L2Sigma_R3),
>   ∃ T : L2Sigma_R3 →ₗ[ℝ] ℝ, ∀ w : L2Sigma_R3, b u v w = T w
> ```
> The linear-functional witness `T` carries `map_add`/`map_smul`, which is exactly
> third-slot additivity (`b_add_3`) and homogeneity (`b_smul_3`) for arbitrary `w`.

### F5 (NEW, companion). `b_linExt_12` — first/second-slot linearity to arbitrary `u`, `v`
```
b_linExt_1 : ∀ (v w : L2Sigma_R3), ∃ T : L2Sigma_R3 →ₗ[ℝ] ℝ, ∀ u, b u v w = T u
b_linExt_2 : ∀ (u w : L2Sigma_R3), ∃ T : L2Sigma_R3 →ₗ[ℝ] ℝ, ∀ v, b u v w = T v
```
**Intent.** Same honest device for slots 1 and 2: linearity over arbitrary arguments,
supplied as gap data because the full form is not L²-continuous jointly. Note: for slots
1,2 *at fixed Schwartz `w`* we ALSO have `b_cont_fixedTest` (F3), but `w` here is
arbitrary, so we still need the linear-functional datum to push `b_add_1/2`,`b_smul_1/2`
to arbitrary `w`. (Equivalently, one combined field
`b_trilinear : <multilinear-map data>` could replace F4+F5; see §4.1.)

### F6 (unchanged). `schwartz_dense`
```
schwartz_dense : ∀ (u : L2Sigma_R3),
  ∃ s : ℕ → L2Sigma_R3, (∀ n, IsSchwartzDivFree_R3 (s n)) ∧
    Filter.Tendsto s Filter.atTop (nhds u)
```
Density of the Schwartz-div-free class in `L²_σ`. Property of the space; carries no
convection content. **Scaffold Prop field.**

### 4.1 Recommended compaction (lean-coder's choice)

F4 + F5 are three existential-linear-functional fields. They can be packaged as a single
**multilinear** datum, which is cleaner and removes redundancy:
```
b_multilinear :
  ∃ B : L2Sigma_R3 →ₗ[ℝ] L2Sigma_R3 →ₗ[ℝ] L2Sigma_R3 →ₗ[ℝ] ℝ,
    ∀ u v w, b u v w = B u v w
```
A single trilinear-map witness `B` yields **all** of `b_add_{1,2,3}` and `b_smul_{1,2,3}`
over arbitrary `L2Sigma_R3` directly from `map_add`/`map_smul`, with no continuity needed.
**This is the preferred form** — it is the honest statement "the convection form is a
genuine algebraic trilinear functional on L²_σ" (true; the algebra is unconditional, only
the *bound* requires the L∞/H¹ slot). Then the gap has exactly four fields:
`b`, `b_extends`, `b_multilinear`, `b_cont_fixedTest`, `schwartz_dense`.

> **Pick one and commit:** ship **`b_multilinear`** (4.1) over F4/F5. Final field list:
> `b`, `b_extends`, `b_multilinear`, `b_cont_fixedTest`, `schwartz_dense`.

---

## 5. How each `R3NSForms` field derives from the corrected gap (`R3NSForms_of_gap`)

Let `g : ConvectionGap 𝔊`, with the §4.1 field set. Set `R3NSForms.b := g.b`.

- **`b_add_{1,2,3}`** : obtain `B` from `g.b_multilinear`; rewrite `g.b _ _ _ = B _ _ _`;
  close by `B`'s `map_add` in the respective slot. **No continuity, no density.** Works for
  **arbitrary** `u v w : L2Sigma_R3` — this is precisely what the false `b_cont` was
  (wrongly) needed for, and what `b_multilinear` supplies honestly.
- **`b_smul_{1,2,3}`** : same, via `B`'s `map_smul`.
- **`b_antisymm`** : `convFormSchwartz_antisymm` (Tier-S) gives it on the Schwartz class via
  `g.b_extends`. To reach arbitrary `u v w`: approximate `u v w` by Schwartz sequences
  (`g.schwartz_dense`), and pass to the limit. **Here is the subtle point** — antisymmetry
  over arbitrary `w` is an *algebraic* identity `b u v w = -b u w v`, which holds for ALL
  `w` because both sides are values of the trilinear functional `B`, and antisymmetry holds
  on the dense Schwartz class. Use: both `(u,v,w) ↦ B u v w` and `(u,v,w) ↦ -B u w v` are
  trilinear; they agree on the dense Schwartz-div-free set (`b_extends` +
  `convFormSchwartz_antisymm`); two trilinear functionals agreeing on a spanning/dense
  set... — **do NOT** route this through topological density (the functionals are not
  L²-continuous). Instead route it **algebraically via slot-wise linearity + density of
  the Schwartz class as a spanning argument**, OR more cheaply: fix `u v` Schwartz, get
  antisymmetry in `w` on Schwartz `w`; both `w ↦ B u v w` and `w ↦ -B u w v` are linear;
  if Schwartz-div-free fields **span** a dense subspace and the two linear maps agree there,
  they need NOT agree globally without continuity.
  **Resolution (this is a Codex review point — see §7):** antisymmetry over arbitrary `w`
  genuinely requires either (a) `b_cont_fixedTest`-style continuity in the slot being
  varied — but `w` is the unbounded slot — or (b) an explicit gap field. **Recommend
  adding** an antisymmetry gap field rather than over-deriving:
  ```
  b_antisymm_gap : ∀ u v w : L2Sigma_R3, b u v w = - b u w v
  ```
  Honesty: antisymmetry of the weak convection form over arbitrary L²_σ test fields is
  itself part of the missing weak operator (it is the IBP/divergence-theorem content);
  asserting it as a gap field is honest and is NOT derivable from continuity alone. With
  `b_antisymm_gap`, `R3NSForms.b_antisymm := g.b_antisymm_gap` directly.
  (Non-vacuity preserved: `b_extends` + `convFormSchwartz_eq_witness` still pin `b ≠ 0`.)
- **`b_bound`** : take `C` from `convFormSchwartz_bound w hw` (the given Schwartz `w`); on
  the Schwartz class `g.b_extends` turns `|g.b u v w|` into `|convFormSchwartz …| ≤ C‖u‖‖v‖`;
  extend to all `u v : L2Sigma_R3` using **`g.b_cont_fixedTest w hw`** (continuity of
  `(u,v) ↦ g.b u v w` in L²) + `g.schwartz_dense` + continuity of `‖·‖`. The fixed-`w`
  continuity is exactly the topology this inequality lives in. **This is the field that
  round-3's wrong `b_cont` was supposed to serve; `b_cont_fixedTest` serves it correctly
  and is TRUE.**
- **`b_galerkin`** : from the `toLp` hypotheses build `IsSchwartzDivFree_R3 u/v/w`, rewrite
  via `g.b_extends`, close with `convFormSchwartz_eq_witness`. **Unchanged from round 3.**

### Net field set after §5 (FINAL):
```
structure ConvectionGap (𝔊 : R3GalerkinScheme) where
  b               : L2Sigma_R3 → L2Sigma_R3 → L2Sigma_R3 → ℝ
  b_extends       : ... (F2, on Schwartz class → convFormSchwartz)
  b_multilinear   : ∃ B : (… →ₗ →ₗ →ₗ[ℝ] ℝ), ∀ u v w, b u v w = B u v w
  b_antisymm_gap  : ∀ u v w, b u v w = - b u w v
  b_cont_fixedTest: ∀ w, IsSchwartzDivFree_R3 w →
                      Continuous (fun p : L2Sigma_R3 × L2Sigma_R3 => b p.1 p.2 w)
  schwartz_dense  : ... (F6)
```

---

## 6. No-smuggle + satisfiability + honesty verdict

### Not a rename / not R3NSForms in disguise
- No `R3NSForms` field, no `Nonempty (R3NSForms 𝔊)` field.
- `b_bound` is **not** a field of `ConvectionGap` — it is **derived** in `R3NSForms_of_gap`
  from `convFormSchwartz_bound` + `b_extends` + `b_cont_fixedTest` + `schwartz_dense`.
- The Tier-S algebra/estimate lemmas remain the source of the *quantitative* content; the
  gap supplies only (i) the extension link, (ii) the algebraic trilinear structure on L²_σ,
  (iii) antisymmetry on L²_σ, (iv) fixed-Schwartz-`w` L² bilinear continuity, (v) density.

### Not the false L²³ extension
- There is **no** `Continuous (fun p : L²×L²×L² => b …)` field. The only continuity is
  `b_cont_fixedTest`: bilinear in `(u,v)` **at fixed Schwartz `w`** — which is TRUE
  (R3-d C3 gives the bounded bilinear form at fixed Schwartz `w`). The unbounded third
  slot is **never** claimed continuous.
- Satisfiability witness: the genuine convection form `b(u,v,w)=∫(u·∇)v·w` satisfies every
  field — `b_extends` by definition of `convFormSchwartz`; `b_multilinear` because the
  integral is genuinely trilinear; `b_antisymm_gap` by IBP+div-free; `b_cont_fixedTest`
  by C3's bilinear bound at fixed Schwartz `w`; `schwartz_dense` by
  `SchwartzMap.denseRange_toLpCLM` + the div-free projection. None of these is the
  nonexistent L² joint extension.

### Honesty verdict: MIXED — and that is the correct, honest outcome
- **Thinner-than-`R3NSForms`:** `b_extends`, `b_cont_fixedTest`, `schwartz_dense` are
  strictly lower-level analytic facts (the genuine Mathlib-absent pillars). The quantitative
  `b_bound` is **derived**, not assumed → thinner here.
- **Algebraic fields (`b_multilinear`, `b_antisymm_gap`) are at the SAME level as the
  corresponding `R3NSForms` fields** — they are *not* thinner; they essentially restate
  trilinearity/antisymmetry of `b` over all of L²_σ. This is **unavoidable and honest**:
  the third-slot algebra over arbitrary (non-Schwartz) `w` is genuinely part of the missing
  weak operator and **cannot** be derived from any true continuity/density (round 3's error
  was trying to derive it from a false continuity). We therefore carry it as an explicit gap
  field, **clearly labeled as the residual of the missing weak-`(u·∇)v` operator, NOT as a
  derived consequence.**

  > **Label to put in the docstring:** "`b_multilinear` and `b_antisymm_gap` are the
  > algebraic core of the missing weak convection operator on L²_σ; they are asserted, not
  > derived, and `ConvectionGap` is therefore NOT uniformly thinner than `R3NSForms` — it is
  > thinner in the *quantitative* (`b_bound`) and *extension* content, and equi-level in the
  > *algebraic* content. This is the honest minimal residual: the convection form's L²_σ
  > trilinearity/antisymmetry is exactly the IBP/divergence-theorem pillar Mathlib lacks."

This is preferable to round 3 (false `b_cont`) and to a vacuous repack: it is **satisfiable**
and it **names the genuine gap** without overclaiming derivability.

---

## 7. Codex adversarial-review points (statement-level, before any proof)

Run `/codex:adversarial-review --effort xhigh` on the new `ConvectionGap` statement and on
the `R3NSForms_of_gap` signature, checking specifically:

1. **`b_cont_fixedTest` truth.** Confirm `(u,v) ↦ b u v w` IS jointly L²-continuous for
   fixed Schwartz `w` (it is: bounded bilinear by R3-d C3). Confirm it does NOT secretly
   re-assert the false third-slot continuity.
2. **`b_antisymm_gap` honesty.** Confirm it is labeled as an asserted residual of the
   missing operator, not as "thinner than R3NSForms," and that the docstring does not claim
   it is derived from continuity.
3. **`b_multilinear` non-overclaim.** Confirm a trilinear *algebraic* functional on L²_σ
   is honestly available/asserted (it is the algebraic content; the bound is separate) and
   is not smuggling the bound.
4. **`b_bound` derivation soundness.** Confirm `b_bound` is genuinely *derived* in
   `R3NSForms_of_gap` from `convFormSchwartz_bound` + `b_cont_fixedTest` + `schwartz_dense`,
   with the constant `C(w)` taken at the fixed Schwartz `w` (slots 1,2 limit only).
5. **No vacuity.** Confirm the `b_extends` + `convFormSchwartz_eq_witness` pin still
   excludes `b = 0`.
6. **No pure-L²-joint-continuity anywhere.** Grep the final statement for any
   `Continuous (… L2Sigma_R3 × L2Sigma_R3 × L2Sigma_R3 …)` — must be ABSENT.

---

## 8. Definition of done (this PR = statement repair only)

- **Must-compile, scaffold-OK:** `ConvectionForm.lean` builds with the corrected
  `ConvectionGap` (final field set §5) and the `R3NSForms_of_gap` skeleton, each proof
  obligation carrying a single `-- ALLOW_SORRY: …` marker (this PR is a *statement* repair;
  proofs land in the Tier-G prover pass).
- **Must-pass statement gate (Codex):** all six §7 checks green; in particular round-3's
  pure-L² joint continuity is removed and replaced by `b_cont_fixedTest`.
- **No new `axiom`/`opaque`/`constant`.** `SolutionInterfaces.lean` untouched.
- **Later (Tier-G prover pass, separate PR):** `R3NSForms_of_gap` sorry-free.

### Targets
| Target | Status this PR |
|---|---|
| `ConvectionGap` (corrected statement) | **must-compile (statement is the deliverable)** |
| `R3NSForms_of_gap` body | scaffold-only (`ALLOW_SORRY`), must-prove in next pass |
| `R3NSForms_of_gap` signature `ConvectionGap 𝔊 → Nonempty (R3NSForms 𝔊)` | **must-compile, unchanged** |

---

## 9. Recommended first task for lean-coder

Edit `LerayHopf/R3/ConvectionForm.lean`:
1. Replace the `b_cont` field of `ConvectionGap` with the four corrected fields:
   `b_multilinear`, `b_antisymm_gap`, `b_cont_fixedTest` (keep `b`, `b_extends`,
   `schwartz_dense`). Use the §5 FINAL field set.
2. Update the structure docstring per the §6 honesty label.
3. Update `R3NSForms_of_gap`'s per-field `case` comments to the new derivation routes (§5):
   `b_add_*/b_smul_*` ← `b_multilinear`; `b_antisymm` ← `b_antisymm_gap`;
   `b_bound` ← `convFormSchwartz_bound` + `b_cont_fixedTest` + `schwartz_dense`;
   `b_galerkin` ← `b_extends` + `convFormSchwartz_eq_witness`. Keep each body as a single
   marked `sorry`.
Then `bash scripts/agent-preflight.sh`, and hand the statement to the orchestrator for the
§7 Codex gate.
