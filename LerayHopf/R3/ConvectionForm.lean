import LerayHopf.R3.ConvectionOperator
import LerayHopf.R3.AxiomaticClosure
import LerayHopf.R3.SchwartzDivFreeBasis
import LerayHopf.R3.CurlDensityCapstone  -- curlSchwartzDense_holds (proved theorem, issue #3/#21)

/-!
# Tier G — The isolated convection gap and the conditional concrete `R3NSForms` (ℝ³)

**Milestone / stream:** `stream-c-convection-operator` (Tier G).

This file isolates the genuine Mathlib-absent pillar behind the
`r3_NSForms_exist` assumption (declared in `LerayHopf/R3/AxiomaticClosure.lean`)
as a single named hypothesis `ConvectionGap`, and proves the conditional

  `ConvectionGap 𝔊 → Nonempty (R3NSForms 𝔊)`

so that discharging `ConvectionGap` once (when the missing weak-`(u·∇)v` calculus on
`Lp` lands) discharges `r3_NSForms_exist` everywhere, with no edit to `AxiomaticClosure`.

It imports `AxiomaticClosure.lean` (allowed) to reference `R3NSForms`, but does **not**
edit it.

## What the gap is — and is not

The sibling Tier-S file `LerayHopf/R3/ConvectionOperator.lean` already proves, *axiom-free*,
the genuine convection functional `convFormSchwartz` on the Schwartz-div-free class
(`IsSchwartzDivFree_R3`), **together with all of its real analytic properties**:
multilinearity (`convFormSchwartz_add_{1,2,3}`, `convFormSchwartz_smul_{1,2,3}`),
antisymmetry (`convFormSchwartz_antisymm`), the 3D trilinear bound
(`convFormSchwartz_bound`), and the `convIntegralSchwartz` pin
(`convFormSchwartz_eq_witness`).  Those are **not** what is missing.

What Mathlib cannot yet furnish — and what `ConvectionGap` therefore isolates — is the
**weak-convection-operator extension** of that partial form to *all* of `L²_σ(ℝ³)`:
a total `b` that (i) restricts to the proven `convFormSchwartz` on the Schwartz class
(`b_extends`), (ii) is an algebraic trilinear functional on `L²_σ` (`b_multilinear`),
(iii) is antisymmetric in the last two slots over arbitrary `L²_σ` (`b_antisymm_gap`),
(iv) is jointly L²-continuous in the first two slots **at a fixed Schwartz test** `w`
(`b_cont_fixedTest`), together with (v) the density of the Schwartz-div-free class in
`L²_σ(ℝ³)` (`schwartz_dense`).  See the corrected design contract in
`docs/scratch/stream-c-convgap-topology.md`.

**Round-3 correction.** The previous field `b_cont` asserted *joint L²-continuity in all
three slots* — i.e. a continuous extension of the convection form to `L²×L²×L²` in the
L² topology.  That extension does **not** exist: the genuine form `b(u,v,w)=∫(u·∇)v·w` is
**unbounded in pure L²×L²×L² norms** (R3-d `convIntegralSchwartz_bound_sup`/`_H1` always
keep one factor in L∞/H¹), so it has no continuous extension in that topology and `b_cont`
was **false** for the real form.  It is replaced by `b_cont_fixedTest` (genuine bilinear
continuity in slots 1,2 at fixed Schwartz `w`) plus the algebraic fields `b_multilinear`
and `b_antisymm_gap` carrying the third-slot structure that no true continuity can supply.

**Honesty label (MIXED — not uniformly thinner).** `ConvectionGap` does **not** contain an
`R3NSForms` field and does **not** restate `Nonempty (R3NSForms 𝔊)`, but it is **NOT**
uniformly thinner than `R3NSForms`.  The thin/equi split is:
- *Thinner* in the **quantitative** content (the trilinear `b_bound`) and the **extension**
  content: those are **derived** in `R3NSForms_of_gap`, not assumed.  `b_bound` follows from
  `convFormSchwartz_bound` + `b_cont_fixedTest` + `schwartz_dense`; the pin `b_galerkin`
  follows from `b_extends` + `convFormSchwartz_eq_witness`.  So a skeptical reader cannot read
  the quantitative `R3NSForms` content straight out of `ConvectionGap`.
- *Equi-level* in the **algebraic** content: `b_multilinear` and `b_antisymm_gap` carry
  trilinearity and last-two-slot antisymmetry of `b` over **all** of `L²_σ`.  These are the
  **explicitly ASSERTED residual** of the missing weak-`(u·∇)v` / IBP-divergence operator —
  the third-slot algebra over arbitrary (non-Schwartz) `w` is genuinely part of the operator
  Mathlib lacks and **cannot** be derived from any true continuity (round 3's error was to
  derive it from a *false* L²×L²×L² continuity).
The **only** continuity assumption is `b_cont_fixedTest`: joint L²-continuity of `(u,v) ↦
b u v w` at a **fixed Schwartz** test `w`, on slots 1,2 only.  There is **no** pure-L²³
joint-continuity field — the round-3 `b_cont` (joint continuity on `L²×L²×L²`) was **false**
for the real form (one factor must live in L∞/H¹) and has been **deleted**.
`ConvectionGap` is therefore **NOT a rename of `R3NSForms`** and **NOT the false L²³
extension**; it carries no `LerayHopfSolution` / `WeakFormNS` / energy-inequality content.

## Declarations

- `ConvectionGap`        : the isolated frontier — the weak-convection-operator extension
                           (`b` total + `b_extends` + `b_multilinear` + `b_antisymm_gap`
                           + `b_cont_fixedTest` + `schwartz_dense`).
- `ConvectionGapOp`      : the operator-core sub-structure (issue #48 reorganization) —
                           exactly `ConvectionGap` minus `schwartz_dense`; the five operator
                           fields including the fixed-test bound (as `b_cont_fixedTest`);
                           density is proved separately and assembled in `r3_NSForms_exists`.
- `R3NSForms_of_gap`     : the conditional `ConvectionGap 𝔊 → Nonempty (R3NSForms 𝔊)`,
                           a genuine derivation of every `R3NSForms` field from Tier-S.

## Scaffold status

All proof bodies of `R3NSForms_of_gap` are now discharged (Tier G).  The H1–H4 / P1 / P2
density chain is sorry-free.

**Issue #48 reorganization:** The named axiom `r3_NSForms_exist` is REPLACED by
`r3ConvectionGapOp_exists` (see `## Assumptions` below), mirroring the accepted torus #22
pattern (`torusConvectionGap_exists`).  `r3_NSForms_exists` is a proved theorem (sorry-free).
`AxiomaticClosure.lean` is NOT edited.

What becomes THEOREM content (no longer assumed):
- The multilinear ALGEBRA: `b_add_{1,2,3}` and `b_smul_{1,2,3}` are derived from `b_multilinear`.
- DENSITY: `schwartz_dense` is the proved lemma `convectionGap_schwartz_dense curlSchwartzDense_holds`,
  assembled in `r3_NSForms_exists` — not bundled in the axiom.

What REMAINS ASSUMED (the irreducible weak `(u·∇)v` operator core):
- The total form `b` and its existence, `b_multilinear`, `b_antisymm_gap`, the
  `convFormSchwartz` pin (`b_extends`), and the fixed-test bound — which is assumed in the
  equivalent continuity form `b_cont_fixedTest`.  Note: bounded bilinear ↔ continuous bilinear,
  so `b_cont_fixedTest` is analytically EQUIVALENT to `R3NSForms.b_bound`; the bound is
  assumed, not proved, just rephrased.

This is a reorganization of AX-4 into the operator-gap form, NOT a strict analytic thinning
of the bound content.

## Assumptions

One axiom is added in THIS file.

1. `r3ConvectionGapOp_exists` — ℝ³ weak `(u·∇)v` operator core (issue #48 reorganization).
   For any `R3GalerkinScheme 𝔊`, a `ConvectionGapOp 𝔊` exists.  `ConvectionGapOp` carries
   the five operator-core fields: `b`, `b_extends`, `b_multilinear`, `b_antisymm_gap`,
   `b_cont_fixedTest`.  These are the irreducible IBP/divergence-theorem content Mathlib lacks
   for the weak `(u·∇)v` operator on `L²_σ(ℝ³)`.
   DENSITY NOT BUNDLED: `schwartz_dense` is NOT a field of `ConvectionGapOp`; it is the
   proved lemma `convectionGap_schwartz_dense curlSchwartzDense_holds` (sorry-free).
   ANALYTIC STRENGTH: `b_cont_fixedTest` (joint L²-continuity of `(u,v)↦b u v w` at fixed
   Schwartz `w`) is EQUIVALENT to `R3NSForms.b_bound` by the bounded/continuous-bilinear
   equivalence.  The fixed-test bound is therefore still ASSUMED (in continuous form), not
   proved.  What genuinely becomes theorem content is (a) the multilinear algebra (`b_add`,
   `b_smul` from `b_multilinear`) and (b) density (`schwartz_dense`, proved separately).
   NON-VACUOUS: `b_extends` + `convFormSchwartz_eq_witness` pin `b` to `convIntegralSchwartz`
   on Schwartz triples, excluding `b = 0`.
   Temam II.§1; Lemarié-Rieusset §5; mirrors torus `torusConvectionGap_exists` (issue #22).
-/

namespace LerayHopf
open MeasureTheory LineDeriv SchwartzMap

/-! ### G1 — The isolated convection gap -/

/-- **G1. The isolated convection gap — the weak-convection-operator extension.**

`ConvectionGap 𝔊` isolates the *genuine* Mathlib-absent pillar behind `r3_NSForms_exist`.
The quantitative content (the trilinear bound, the `convIntegralSchwartz` pin) is **not**
carried as a field — it is *derived* in `R3NSForms_of_gap` from the Tier-S
`convFormSchwartz_*` lemmas in `LerayHopf/R3/ConvectionOperator.lean` via `b_extends`.

What is genuinely missing — and what this structure carries — is the **extension** of that
partial, proven Schwartz-class form to a *total* operator on `L²_σ(ℝ³)`:

- `b`             — a total candidate form on all of `L²_σ(ℝ³)`;
- `b_extends`     — `b` *restricts* to the proven `convFormSchwartz` on the Schwartz class
                    (the operator-extension content, the actual frontier);
- `b_multilinear` — `b` is an algebraic trilinear functional on `L²_σ` (a `→ₗ[ℝ]`-tower
                    witness `B` with `b u v w = B u v w`); this supplies `b_add_{1,2,3}`
                    and `b_smul_{1,2,3}` over arbitrary `L²_σ` directly from `map_add`/
                    `map_smul`, with **no continuity needed**;
- `b_antisymm_gap`— antisymmetry in the last two slots over **arbitrary** `L²_σ`
                    (`b u v w = - b u w v`), carried as an explicit gap field;
- `b_cont_fixedTest` — joint L²-continuity of `(u,v) ↦ b u v w` at a **fixed Schwartz**
                    test `w` (this is the genuine, TRUE continuity — bounded bilinear by
                    R3-d C3 — that drives the *derivation* of `b_bound`);
- `schwartz_dense` — density of the Schwartz-div-free class in `L²_σ(ℝ³)`.

**Round-3 correction.** The previous `b_cont` (joint L²-continuity in all three slots) was
**false**: it asserted a continuous extension of `b` to `L²×L²×L²` in the L² topology, but
the convection form is unbounded in pure L²×L²×L² norms (one factor must live in L∞/H¹), so
no such extension exists.  It is removed and replaced by `b_cont_fixedTest`.

This is a **hypothesis** (data + Prop fields), **not** an `axiom`, and it never enters a
theorem *name*; the resulting `R3NSForms_of_gap` is explicitly conditional.

**Honesty label (MIXED — the correct, honest outcome).**  `ConvectionGap` is **NOT**
uniformly thinner than `R3NSForms`.  It is *thinner* in the **quantitative** (`b_bound`)
and **extension** content — those are derived, not assumed (`b_extends`, `b_cont_fixedTest`,
`schwartz_dense` are strictly lower-level analytic pillars; the bound is a *consequence*).
It is *equi-level* in the **algebraic** content: `b_multilinear` and `b_antisymm_gap`
essentially restate trilinearity / antisymmetry of `b` over all of `L²_σ`.  This is
unavoidable and honest — the third-slot algebra over arbitrary (non-Schwartz) `w` is
genuinely part of the missing weak-`(u·∇)v` operator (the IBP / divergence-theorem pillar
Mathlib lacks) and **cannot** be derived from any true continuity (round 3's error was
deriving it from a *false* continuity).  These two fields are therefore the explicitly
*asserted* (not derived) residual of the missing weak operator — **NOT a rename of
`R3NSForms`, and NOT the false L²³ extension.**

**No-smuggle audit.**  `ConvectionGap`
- contains **no** `R3NSForms` field and **no** `Nonempty (R3NSForms 𝔊)` field;
- does **not** carry `b_bound` or `b_galerkin` — those are *derived* in `R3NSForms_of_gap`
  (`b_bound` ← `convFormSchwartz_bound` + `b_cont_fixedTest` + `schwartz_dense`;
  `b_galerkin` ← `b_extends` + `convFormSchwartz_eq_witness`), so a skeptical reader cannot
  read the quantitative `R3NSForms` content straight out of `ConvectionGap`;
- contains **no** `Continuous (… L2Sigma_R3 × L2Sigma_R3 × L2Sigma_R3 …)` field (the false
  pure-L² joint continuity is absent); the only continuity is the slot-1,2 / fixed-Schwartz
  bilinear `b_cont_fixedTest`, which is TRUE;
- carries no `WeakFormNS`, energy-inequality, or solution content. -/
structure ConvectionGap (𝔊 : R3GalerkinScheme) where
  /-- The **total** candidate convection form on all of `L²_σ(ℝ³)`. -/
  b : L2Sigma_R3 → L2Sigma_R3 → L2Sigma_R3 → ℝ
  /-- **Operator-extension property (the frontier).** On the Schwartz-div-free class, `b`
  restricts to the already-proven Tier-S functional `convFormSchwartz`.  This is the only
  link between `b` and the genuine `∫(u·∇)v·w`; the algebraic/analytic Schwartz-class
  properties of `b` are then *inherited* from the `convFormSchwartz_*` lemmas, not assumed
  here.  (Non-vacuity flows from this together with the Tier-S `convFormSchwartz_eq_witness`
  pin to `convIntegralSchwartz`, excluding `b = 0`.) -/
  b_extends : ∀ (u v w : L2Sigma_R3)
    (hu : IsSchwartzDivFree_R3 u) (hv : IsSchwartzDivFree_R3 v)
    (hw : IsSchwartzDivFree_R3 w),
    b u v w = convFormSchwartz u v w hu hv hw
  /-- **Algebraic trilinear structure of the extension over arbitrary `L²_σ`.**
  `b` is realised by a genuine `ℝ`-trilinear-map tower `B : L²_σ →ₗ[ℝ] L²_σ →ₗ[ℝ] L²_σ
  →ₗ[ℝ] ℝ` with `b u v w = B u v w` for all `u v w`.  This is the *algebraic core* of the
  missing weak convection operator: the convection integral is genuinely trilinear (the
  algebra is unconditional — only the *bound* requires the L∞/H¹ slot), so this is TRUE for
  the real form.  It yields `b_add_{1,2,3}` and `b_smul_{1,2,3}` over arbitrary `L²_σ`
  directly from `B`'s `map_add` / `map_smul`, with **no continuity and no density**.  It is
  *asserted*, not derived — the explicitly-labeled residual of the missing operator (it does
  **not** carry the bound, which is separate). -/
  b_multilinear :
    ∃ B : L2Sigma_R3 →ₗ[ℝ] L2Sigma_R3 →ₗ[ℝ] L2Sigma_R3 →ₗ[ℝ] ℝ,
      ∀ (u v w : L2Sigma_R3), b u v w = B u v w
  /-- **Antisymmetry in the last two slots over arbitrary `L²_σ`.**
  `b u v w = - b u w v` for **all** `u v w : L²_σ`.  Antisymmetry of the weak convection
  form over arbitrary L²_σ test fields is itself part of the missing weak operator (it is
  the IBP / divergence-theorem content); it is **NOT derivable from continuity alone** (the
  varied slot `w` is the unbounded one), so it is carried as an explicit gap field — the
  honest residual of the missing weak-`(u·∇)v` operator. -/
  b_antisymm_gap : ∀ (u v w : L2Sigma_R3), b u v w = - b u w v
  /-- **Joint L²-continuity of the extension in slots 1,2 at a fixed Schwartz test `w`.**
  For a fixed `IsSchwartzDivFree_R3 w`, the bilinear map `(u,v) ↦ b u v w` is jointly
  L²-continuous.  This is the **genuine, TRUE** continuity (round 3's all-three-slot
  `b_cont` was false): R3-d C3 (`convIntegralSchwartz_bound_sup`) gives
  `|b u v w| ≤ C(w)·‖u‖·‖v‖` with `C(w) < ∞` for Schwartz `w`, so the form is bounded
  bilinear in `(u,v)` and hence continuous, and extends from the dense Schwartz `(u,v)` by
  uniform continuity **in the two L² slots only**.  It lives in exactly the L² topology of
  the first two slots that `R3NSForms.b_bound` is stated in.  It does **not** assert any
  third-slot / arbitrary-`w` continuity — the unbounded slot is never claimed continuous.
  It drives the *derivation* of `b_bound`; it gives no algebra or bound on its own. -/
  b_cont_fixedTest : ∀ (w : L2Sigma_R3), IsSchwartzDivFree_R3 w →
    Continuous (fun p : L2Sigma_R3 × L2Sigma_R3 => b p.1 p.2 w)
  /-- **Density of the Schwartz-div-free class in `L²_σ(ℝ³)`.**  Every field of `L²_σ`
  is an L²-limit of `IsSchwartzDivFree_R3` fields.  This is the missing density pillar that,
  with `b_cont_fixedTest`, transports the proven Schwartz-class bound to all `u v : L²_σ`
  (at fixed Schwartz `w`).  It is a property of the *space*, not of `b`, so it carries no
  convection content of its own. -/
  schwartz_dense : ∀ (u : L2Sigma_R3),
    ∃ s : ℕ → L2Sigma_R3, (∀ n, IsSchwartzDivFree_R3 (s n)) ∧
      Filter.Tendsto s Filter.atTop (nhds u)

/-! ### G1b — `ConvectionGapOp`: operator-core sub-structure (no density field) -/

/-- **G1b. The weak `(u·∇)v` operator core — density is NOT bundled (issue #48 reorganization).**

`ConvectionGapOp 𝔊` is exactly `ConvectionGap 𝔊` minus the `schwartz_dense` field.
It carries the five Mathlib-absent operator-core fields for the weak convection operator on
`L²_σ(ℝ³)`: `b`, `b_extends`, `b_multilinear`, `b_antisymm_gap`, `b_cont_fixedTest`.

The `schwartz_dense` field is the PROVED lemma `convectionGap_schwartz_dense curlSchwartzDense_holds`
— density is a property of the function space (not of `b`) and is proved separately.

Analytic note: `b_cont_fixedTest` (joint L²-continuity of `(u,v)↦b u v w` at fixed Schwartz `w`)
is analytically EQUIVALENT to `R3NSForms.b_bound` by the bounded/continuous-bilinear equivalence.
The fixed-test bound is therefore still ASSUMED in this structure (in continuity form), not proved.
What genuinely becomes theorem content in `R3NSForms_of_gap` is: (a) the multilinear algebra
(`b_add_{1,2,3}`, `b_smul_{1,2,3}` from `b_multilinear`) and (b) density (from `schwartz_dense`
which is assembled from the proved `curlSchwartzDense_holds`).

This is used by the axiom `r3ConvectionGapOp_exists` (issue #48, mirrors torus #22).
To obtain a full `ConvectionGap 𝔊`, supply the proved density:
```
ConvectionGap.mk g.b g.b_extends g.b_multilinear g.b_antisymm_gap g.b_cont_fixedTest
  (convectionGap_schwartz_dense curlSchwartzDense_holds)
```

Fields are identical to the corresponding `ConvectionGap` fields (same signatures,
same doc-comments). -/
structure ConvectionGapOp (𝔊 : R3GalerkinScheme) where
  /-- The **total** candidate convection form on all of `L²_σ(ℝ³)`. -/
  b : L2Sigma_R3 → L2Sigma_R3 → L2Sigma_R3 → ℝ
  /-- **Operator-extension property (the frontier).** On the Schwartz-div-free class, `b`
  restricts to the already-proven Tier-S functional `convFormSchwartz`.  This is the only
  link between `b` and the genuine `∫(u·∇)v·w`; the algebraic/analytic Schwartz-class
  properties of `b` are then *inherited* from the `convFormSchwartz_*` lemmas, not assumed
  here.  (Non-vacuity flows from this together with the Tier-S `convFormSchwartz_eq_witness`
  pin to `convIntegralSchwartz`, excluding `b = 0`.) -/
  b_extends : ∀ (u v w : L2Sigma_R3)
    (hu : IsSchwartzDivFree_R3 u) (hv : IsSchwartzDivFree_R3 v)
    (hw : IsSchwartzDivFree_R3 w),
    b u v w = convFormSchwartz u v w hu hv hw
  /-- **Algebraic trilinear structure of the extension over arbitrary `L²_σ`.**
  `b` is realised by a genuine `ℝ`-trilinear-map tower `B : L²_σ →ₗ[ℝ] L²_σ →ₗ[ℝ] L²_σ
  →ₗ[ℝ] ℝ` with `b u v w = B u v w` for all `u v w`.  This is the *algebraic core* of the
  missing weak convection operator: the convection integral is genuinely trilinear (the
  algebra is unconditional — only the *bound* requires the L∞/H¹ slot), so this is TRUE for
  the real form.  It is *asserted*, not derived — the explicitly-labeled residual. -/
  b_multilinear :
    ∃ B : L2Sigma_R3 →ₗ[ℝ] L2Sigma_R3 →ₗ[ℝ] L2Sigma_R3 →ₗ[ℝ] ℝ,
      ∀ (u v w : L2Sigma_R3), b u v w = B u v w
  /-- **Antisymmetry in the last two slots over arbitrary `L²_σ`.**
  `b u v w = - b u w v` for **all** `u v w : L²_σ`.  Antisymmetry of the weak convection
  form over arbitrary L²_σ test fields is itself part of the missing weak operator (the
  IBP / divergence-theorem content); it is NOT derivable from continuity alone. -/
  b_antisymm_gap : ∀ (u v w : L2Sigma_R3), b u v w = - b u w v
  /-- **Joint L²-continuity of the extension in slots 1,2 at a fixed Schwartz test `w`.**
  For a fixed `IsSchwartzDivFree_R3 w`, the bilinear map `(u,v) ↦ b u v w` is jointly
  L²-continuous.  This is the **genuine, TRUE** continuity (all-three-slot continuity is
  false).  Note: this field is analytically EQUIVALENT to `R3NSForms.b_bound` via the
  bounded/continuous-bilinear equivalence; the bound is ASSUMED here (in continuity form),
  not derived. -/
  b_cont_fixedTest : ∀ (w : L2Sigma_R3), IsSchwartzDivFree_R3 w →
    Continuous (fun p : L2Sigma_R3 × L2Sigma_R3 => b p.1 p.2 w)

/-! ### G2 — The conditional concrete `R3NSForms` -/

/-- **G2. The conditional concrete `R3NSForms` — a genuine derivation.**

Given the isolated `ConvectionGap 𝔊` (a total `b`, its extension `b_extends`, the
algebraic trilinear witness `b_multilinear`, antisymmetry `b_antisymm_gap`, fixed-test
bilinear continuity `b_cont_fixedTest`, and density `schwartz_dense`), a genuine
`R3NSForms 𝔊` exists.  Each `R3NSForms` field is obtained as follows:

- `b_add_{1,2,3}` — from `g.b_multilinear`: obtain `B`, rewrite `g.b _ _ _ = B _ _ _`, close
                  by `B`'s `map_add` in the respective slot.  **No continuity, no density**;
                  works for *arbitrary* `u v w : L²_σ` — this is exactly what the false
                  `b_cont` was (wrongly) needed for, supplied honestly by `b_multilinear`;
- `b_smul_{1,2,3}` — same, via `B`'s `map_smul`;
- `b_antisymm`  — directly from `g.b_antisymm_gap` (asserted over arbitrary `L²_σ`); it is
                  the honest residual of the missing operator, **not** derived from
                  continuity;
- `b_bound`     — from `convFormSchwartz_bound` (Tier S): take the constant `C` at the
                  *given* Schwartz `w`; `g.b_extends` turns `|g.b u v w|` into
                  `|convFormSchwartz …| ≤ C‖u‖‖v‖` on the Schwartz class, then
                  `g.b_cont_fixedTest w hw` (slots 1,2 at fixed `w`) + `g.schwartz_dense`
                  + continuity of `‖·‖` extend it to all `u v : L²_σ`;
- `b_galerkin`  — from `convFormSchwartz_eq_witness` (Tier S) via `g.b_extends`.

So `ConvectionGap` does *not* hand over the *quantitative* `R3NSForms` content ready-made:
the bound and the pin are derived from the Tier-S lemmas through `b_extends` /
`b_cont_fixedTest`; only the algebraic trilinear/antisymmetry content (`b_multilinear`,
`b_antisymm_gap`) is asserted, as the honest residual of the missing weak operator.
Discharging `ConvectionGap` later (when the weak-`(u·∇)v` extension calculus lands)
discharges `r3_NSForms_exist` for free, with no edit to `AxiomaticClosure.lean`, and never
vacuously (the `convFormSchwartz_eq_witness` pin through `b_extends` excludes `b = 0`). -/
theorem R3NSForms_of_gap (𝔊 : R3GalerkinScheme) (g : ConvectionGap 𝔊) :
    Nonempty (R3NSForms 𝔊) := by
  obtain ⟨B, hB⟩ := g.b_multilinear
  refine ⟨{ b := g.b
          , b_antisymm := ?b_antisymm
          , b_add_1 := ?b_add_1
          , b_add_2 := ?b_add_2
          , b_add_3 := ?b_add_3
          , b_smul_1 := ?b_smul_1
          , b_smul_2 := ?b_smul_2
          , b_smul_3 := ?b_smul_3
          , b_bound := ?b_bound
          , b_galerkin := ?b_galerkin }⟩
  case b_antisymm =>
    -- Directly from g.b_antisymm_gap (asserted over arbitrary L²_σ)
    exact g.b_antisymm_gap
  case b_add_1 =>
    -- From g.b_multilinear: rewrite to B then close by map_add + LinearMap.add_apply
    intro u u' v w
    simp only [hB, map_add, LinearMap.add_apply]
  case b_add_2 =>
    -- From g.b_multilinear: close by map_add in slot 2
    intro u v v' w
    simp only [hB, map_add, LinearMap.add_apply]
  case b_add_3 =>
    -- From g.b_multilinear: close by map_add in slot 3 (purely algebraic)
    intro u v w w'
    simp only [hB, map_add]
  case b_smul_1 =>
    -- From g.b_multilinear: close by map_smul in slot 1
    intro c u v w
    simp only [hB, map_smul, LinearMap.smul_apply, smul_eq_mul]
  case b_smul_2 =>
    -- From g.b_multilinear: close by map_smul in slot 2
    intro c u v w
    simp only [hB, map_smul, LinearMap.smul_apply, smul_eq_mul]
  case b_smul_3 =>
    -- From g.b_multilinear: close by map_smul in slot 3 (purely algebraic)
    intro c u v w
    simp only [hB, map_smul, smul_eq_mul]
  case b_bound =>
    -- Derive b_bound from g.b_extends + convFormSchwartz_bound + g.b_cont_fixedTest + g.schwartz_dense
    intro w hw
    -- Get the constant C from the Tier-S Schwartz-class bound
    obtain ⟨C, hC⟩ := convFormSchwartz_bound w hw
    -- For u, v in the Schwartz class: |g.b u v w| = |convFormSchwartz u v w| ≤ C * ‖u‖ * ‖v‖
    -- For general u, v: use g.b_cont_fixedTest + g.schwartz_dense to extend by continuity
    refine ⟨C, fun u v => ?_⟩
    -- Approximate u, v by Schwartz sequences
    obtain ⟨su, hsu_sch, hsu_lim⟩ := g.schwartz_dense u
    obtain ⟨sv, hsv_sch, hsv_lim⟩ := g.schwartz_dense v
    -- The map (u', v') ↦ g.b u' v' w is continuous (b_cont_fixedTest)
    have hcont := g.b_cont_fixedTest w hw
    -- The bound holds on each diagonal term of the sequence
    have hbound_seq : ∀ n : ℕ,
        |g.b (su n) (sv n) w| ≤ C * ‖(su n : L2VF_R3)‖ * ‖(sv n : L2VF_R3)‖ := by
      intro n
      rw [g.b_extends (su n) (sv n) w (hsu_sch n) (hsv_sch n) hw]
      exact hC (su n) (sv n) (hsu_sch n) (hsv_sch n)
    -- Diagonal sequence (su n, sv n) → (u, v) in the product topology
    have hlim_pair : Filter.Tendsto (fun n => (su n, sv n)) Filter.atTop (nhds (u, v)) :=
      (Prod.tendsto_iff _ _).mpr ⟨hsu_lim, hsv_lim⟩
    -- b(su n, sv n, w) → b(u, v, w) by continuity of (u', v') ↦ b u' v' w
    have hlim_b : Filter.Tendsto (fun n => g.b (su n) (sv n) w)
        Filter.atTop (nhds (g.b u v w)) :=
      (hcont.tendsto (u, v)).comp hlim_pair
    -- The bound passes to the limit: since |b(su n, sv n, w)| ≤ C * ‖su n‖ * ‖sv n‖
    -- and b(su n, sv n, w) → b(u, v, w), ‖su n‖ → ‖u‖, ‖sv n‖ → ‖v‖
    -- we get |b(u, v, w)| ≤ C * ‖u‖ * ‖v‖
    have hlim_norm_u : Filter.Tendsto (fun n => ‖(su n : L2VF_R3)‖) Filter.atTop (nhds ‖(u : L2VF_R3)‖) :=
      (continuous_norm.tendsto _).comp
        ((continuous_subtype_val.tendsto _).comp hsu_lim)
    have hlim_norm_v : Filter.Tendsto (fun n => ‖(sv n : L2VF_R3)‖) Filter.atTop (nhds ‖(v : L2VF_R3)‖) :=
      (continuous_norm.tendsto _).comp
        ((continuous_subtype_val.tendsto _).comp hsv_lim)
    have hlim_rhs : Filter.Tendsto (fun n => C * ‖(su n : L2VF_R3)‖ * ‖(sv n : L2VF_R3)‖)
        Filter.atTop (nhds (C * ‖(u : L2VF_R3)‖ * ‖(v : L2VF_R3)‖)) :=
      ((tendsto_const_nhds.mul hlim_norm_u).mul hlim_norm_v)
    -- Apply le_of_tendsto_of_tendsto to pass the bound to the limit
    apply le_of_tendsto_of_tendsto
      ((continuous_abs.tendsto _).comp hlim_b)
      hlim_rhs
    exact Filter.Eventually.of_forall (fun n => hbound_seq n)
  case b_galerkin =>
    -- From convFormSchwartz_eq_witness via g.b_extends
    intro ψu ψv ψw u v w hpu hpv hpw
    -- Build IsSchwartzDivFree_R3 witnesses from the toLp hypotheses
    have hu : IsSchwartzDivFree_R3 u := ⟨ψu, hpu⟩
    have hv : IsSchwartzDivFree_R3 v := ⟨ψv, hpv⟩
    have hw : IsSchwartzDivFree_R3 w := ⟨ψw, hpw⟩
    -- Rewrite g.b to convFormSchwartz via b_extends, then use eq_witness
    rw [g.b_extends u v w hu hv hw,
        convFormSchwartz_eq_witness u v w hu hv hw ψu ψv ψw hpu hpv hpw]

/-! ### Issue #48 — Partial discharge of `schwartz_dense` in `ConvectionGap`

The five fields `b`, `b_extends`, `b_multilinear`, `b_antisymm_gap`, `b_cont_fixedTest`
of `ConvectionGap` are genuine Mathlib-absent residuals (the weak convection operator on
`L²_σ`).  The ONE provable sub-claim is `schwartz_dense`: density of `IsSchwartzDivFree_R3`
in `L2Sigma_R3`, derivable from the proved theorem `curlSchwartzDense_holds`.

The declarations H1–H4, P1, P2 formally prove that density.

**Axiom delta (issue #48 thin-swap, refined):** The fat axiom `r3_NSForms_exist` is DISCHARGED
and replaced by the OPERATOR-ONLY residual axiom `r3ConvectionGapOp_exists` (below), which
carries only the five operator-extension fields.  Density (`schwartz_dense`) is proved here (P2)
and assembled in `r3_NSForms_exists`.  All trilinear/bound/pin algebra that `r3_NSForms_exist`
formerly assumed is now THEOREM content via `R3NSForms_of_gap` (above).  The capstone
`exists_lerayHopf_r3_axiomatic` is rerouted from `r3_NSForms_exist` to the proved theorem
`r3_NSForms_exists` (below).
-/

/-! ### H1 — `IsSchwartzDivFree_R3` is closed under addition -/

/-- **H1.** The sum of two `IsSchwartzDivFree_R3` fields is again `IsSchwartzDivFree_R3`.

Proof: if `u` has Schwartz witnesses `ψu` and `v` has witnesses `ψv`, then
`u + v` has witnesses `(fun j => ψu j + ψv j)`, because `toLp` is additive a.e.
and `L2VF_projComponent_R3` is linear. -/
theorem isSchwartzDivFree_add (u v : L2Sigma_R3)
    (hu : IsSchwartzDivFree_R3 u) (hv : IsSchwartzDivFree_R3 v) :
    IsSchwartzDivFree_R3 (u + v) := by
  obtain ⟨ψu, hψu⟩ := hu
  obtain ⟨ψv, hψv⟩ := hv
  -- Witness: component-wise sum of Schwartz representatives
  refine ⟨fun j => ψu j + ψv j, fun j => ?_⟩
  -- L2VF_projComponent_R3 is a CLM, hence additive
  rw [Submodule.coe_add, map_add, hψu j, hψv j]
  -- (ψu j + ψv j).toLp = ψu j .toLp + ψv j .toLp via toLpCLM (a CLM)
  show (ψu j + ψv j).toLp 2 (volume : Measure Domain3) =
    (ψu j).toLp 2 (volume : Measure Domain3) + (ψv j).toLp 2 (volume : Measure Domain3)
  have := (SchwartzMap.toLpCLM ℝ ℝ 2 (volume : Measure Domain3)).map_add (ψu j) (ψv j)
  simp only [SchwartzMap.toLpCLM_apply] at this
  exact this

/-! ### H2 — `IsSchwartzDivFree_R3` is closed under scalar multiplication -/

/-- **H2.** A scalar multiple of an `IsSchwartzDivFree_R3` field is again `IsSchwartzDivFree_R3`.

Proof: if `u` has witnesses `ψu` then `c • u` has witnesses `(fun j => c • ψu j)`. -/
theorem isSchwartzDivFree_smul (c : ℝ) (u : L2Sigma_R3)
    (hu : IsSchwartzDivFree_R3 u) :
    IsSchwartzDivFree_R3 (c • u) := by
  obtain ⟨ψu, hψu⟩ := hu
  -- Witness: scalar multiple of Schwartz representatives
  refine ⟨fun j => c • ψu j, fun j => ?_⟩
  rw [Submodule.coe_smul, map_smul, hψu j]
  show (c • ψu j).toLp 2 (volume : Measure Domain3) =
    c • (ψu j).toLp 2 (volume : Measure Domain3)
  have := (SchwartzMap.toLpCLM ℝ ℝ 2 (volume : Measure Domain3)).map_smul c (ψu j)
  simp only [SchwartzMap.toLpCLM_apply] at this
  exact this

/-! ### H3 — `IsSchwartzDivFree_R3` is closed under finite linear combinations -/

/-- **H3.** A finite ℝ-linear combination of `IsSchwartzDivFree_R3` fields is
`IsSchwartzDivFree_R3`.

Follows by induction from H1 and H2 (scalar multiplication preserves the class, and the
class is closed under addition). -/
theorem isSchwartzDivFree_linearCombination {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (v : ι → L2Sigma_R3) (hv : ∀ i ∈ s, IsSchwartzDivFree_R3 (v i)) :
    IsSchwartzDivFree_R3 (∑ i ∈ s, f i • v i) := by
  induction s using Finset.cons_induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    -- zero element: empty Schwartz witness
    exact ⟨fun _ => 0, fun j => by
      simp only [Submodule.coe_zero, map_zero]
      exact (map_zero (SchwartzMap.toLpCLM ℝ ℝ 2 (volume : Measure Domain3))).symm⟩
  | cons a s' ha ih =>
    rw [Finset.sum_cons]
    apply isSchwartzDivFree_add
    · exact isSchwartzDivFree_smul _ _ (hv a (Finset.mem_cons_self a s'))
    · exact ih (fun i hi => hv i (Finset.mem_cons.mpr (Or.inr hi)))

/-! ### H4 — `curlSchwartzL2 ψ` packaged as `L2Sigma_R3` is `IsSchwartzDivFree_R3` -/

/-- **H4.** For any Schwartz potential `ψ : Fin 3 → 𝓢(Domain3, ℝ)`, the curl field
`⟨curlSchwartzL2 ψ, curlSchwartzL2_mem_sigma ψ⟩ : L2Sigma_R3` is `IsSchwartzDivFree_R3`.

Proof: `curlSchwartz_isSchwartz ψ` supplies Schwartz witnesses `curlSchwartz ψ j` for each
component, matching exactly the `L2VF_projComponent_R3` via `curlSchwartzL2_projComponent`. -/
theorem curlSchwartzL2_isSchwartzDivFree_R3 (ψ : Fin 3 → SchwartzMap Domain3 ℝ) :
    IsSchwartzDivFree_R3
      (⟨curlSchwartzL2 ψ, curlSchwartzL2_mem_sigma ψ⟩ : L2Sigma_R3) := by
  -- Witness: curlSchwartz ψ provides Schwartz components
  exact ⟨curlSchwartz ψ, fun j => curlSchwartzL2_projComponent ψ j⟩

/-! ### P1 — Main density theorem: `IsSchwartzDivFree_R3` is dense in `L2Sigma_R3` -/

/-- **P1 (main deliverable).** Given `CurlSchwartzDense`, every element of `L2Sigma_R3` is
an L²-limit of `IsSchwartzDivFree_R3` fields.

Proof route:
1. `CurlSchwartzDense` says `L2Sigma_R3 ≤ closure (span (range curlSchwartzL2))` (in `L2VF_R3`).
2. Any `u ∈ L2Sigma_R3` lies in the `topologicalClosure` of `span (range curlSchwartzL2)`.
3. By `mem_closure_iff_seq_limit`, there exist finite linear combinations of
   `curlSchwartzL2` fields converging to `u` in `L2VF_R3`.
4. Each such combination, lifted to `L2Sigma_R3` via the submodule's closedness, is
   `IsSchwartzDivFree_R3` by H3 + H4.
5. Convergence in `L2Sigma_R3` (subspace topology = subtype topology) follows from
   convergence in `L2VF_R3`. -/
-- Helper: the set-level Schwartz-components predicate, living on `L2VF_R3`.
-- `IsSchwartzComp x` iff `x` has Schwartz component witnesses (no div-free condition needed).
private def IsSchwartzComp (x : L2VF_R3) : Prop :=
  ∃ ψ : Fin 3 → SchwartzMap Domain3 ℝ,
    ∀ j : Fin 3, L2VF_projComponent_R3 j x = (ψ j).toLp 2 (volume : Measure Domain3)

private theorem isSchwartzComp_curlSchwartzL2 (ψ : Fin 3 → SchwartzMap Domain3 ℝ) :
    IsSchwartzComp (curlSchwartzL2 ψ) :=
  ⟨curlSchwartz ψ, fun j => curlSchwartzL2_projComponent ψ j⟩

private theorem isSchwartzComp_zero : IsSchwartzComp (0 : L2VF_R3) :=
  ⟨fun _ => 0, fun j => by
    simp only [map_zero]
    exact (map_zero (SchwartzMap.toLpCLM ℝ ℝ 2 (volume : Measure Domain3))).symm⟩

private theorem isSchwartzComp_add {x y : L2VF_R3}
    (hx : IsSchwartzComp x) (hy : IsSchwartzComp y) : IsSchwartzComp (x + y) :=
  let ⟨ψx, hψx⟩ := hx
  let ⟨ψy, hψy⟩ := hy
  ⟨fun j => ψx j + ψy j, fun j => by
    rw [map_add, hψx j, hψy j]
    have := (SchwartzMap.toLpCLM ℝ ℝ 2 (volume : Measure Domain3)).map_add (ψx j) (ψy j)
    simp only [SchwartzMap.toLpCLM_apply] at this
    exact this⟩

private theorem isSchwartzComp_smul (c : ℝ) {x : L2VF_R3} (hx : IsSchwartzComp x) :
    IsSchwartzComp (c • x) :=
  let ⟨ψx, hψx⟩ := hx
  ⟨fun j => c • ψx j, fun j => by
    rw [map_smul, hψx j]
    have := (SchwartzMap.toLpCLM ℝ ℝ 2 (volume : Measure Domain3)).map_smul c (ψx j)
    simp only [SchwartzMap.toLpCLM_apply] at this
    exact this⟩

-- Every element of `Submodule.span ℝ (Set.range curlSchwartzL2)` has Schwartz components.
private theorem isSchwartzComp_of_mem_span
    {x : L2VF_R3} (hx : x ∈ Submodule.span ℝ (Set.range curlSchwartzL2)) :
    IsSchwartzComp x := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨ψ, rfl⟩ := hx
    exact isSchwartzComp_curlSchwartzL2 ψ
  | zero => exact isSchwartzComp_zero
  | add x y _ _ hx hy => exact isSchwartzComp_add hx hy
  | smul c x _ hx => exact isSchwartzComp_smul c hx

-- The span of curl fields is contained in `L2Sigma_R3`
private theorem span_curlSchwartzL2_le_L2Sigma :
    Submodule.span ℝ (Set.range curlSchwartzL2) ≤ L2Sigma_R3 := by
  rw [Submodule.span_le]
  rintro x ⟨ψ, rfl⟩
  exact curlSchwartzL2_mem_sigma ψ

theorem schwartzDivFree_dense_of_curlDense
    (h : CurlSchwartzDense) (u : L2Sigma_R3) :
    ∃ s : ℕ → L2Sigma_R3, (∀ n, IsSchwartzDivFree_R3 (s n)) ∧
      Filter.Tendsto s Filter.atTop (nhds u) := by
  -- Step 1: u ∈ closure (Submodule.span ℝ (Set.range curlSchwartzL2)) in L2VF_R3
  have hu_in_closure : (u : L2VF_R3) ∈
      closure (↑(Submodule.span ℝ (Set.range curlSchwartzL2)) : Set L2VF_R3) := by
    rw [← Submodule.topologicalClosure_coe]
    exact h u.2
  -- Step 2: L2VF_R3 is a metric space, hence FrechetUrysohnSpace
  -- (NormedAddCommGroup → PseudoMetricSpace → FirstCountableTopology → FrechetUrysohnSpace)
  haveI : FrechetUrysohnSpace L2VF_R3 :=
    inferInstance  -- via NormedAddCommGroup → MetricSpace → FirstCountable → FrechetUrysohn
  -- Step 3: Get a sequence in the span converging to u in L2VF_R3
  rw [mem_closure_iff_seq_limit] at hu_in_closure
  obtain ⟨sn, hsn_mem, hsn_lim⟩ := hu_in_closure
  -- Step 4: Each sn n ∈ L2Sigma_R3 (since span ≤ L2Sigma_R3)
  have hsn_sigma : ∀ n, (sn n : L2VF_R3) ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3) :=
    fun n => span_curlSchwartzL2_le_L2Sigma (hsn_mem n)
  -- Step 5: Lift sn to L2Sigma_R3
  let s : ℕ → L2Sigma_R3 := fun n => ⟨sn n, hsn_sigma n⟩
  -- Step 6: Each s n is IsSchwartzDivFree_R3
  have hs_sch : ∀ n, IsSchwartzDivFree_R3 (s n) := by
    intro n
    exact isSchwartzComp_of_mem_span (hsn_mem n)
  -- Step 7: s n → u in L2Sigma_R3 (subtype topology)
  have hs_lim : Filter.Tendsto s Filter.atTop (nhds u) := by
    rw [tendsto_subtype_rng]
    exact hsn_lim
  exact ⟨s, hs_sch, hs_lim⟩

/-! ### Step 1 — fixed-Schwartz-`w` integral representation of `F.b` (conjunct-2 atom b)

For a fixed Schwartz divergence-free test `w` (witness `ψw`), `F.b (·) (·) w` is — on ALL of
`L²_σ × L²_σ`, not only on Schwartz pairs — the IBP'd antisymmetric integral with the derivative
on the test:
  `F.b f g w = -∑_{i,a} ∫ fₐ·gᵢ·(∂ₐ ψwᵢ)`.
Both sides are jointly `L²`-continuous in `(f, g)` (LHS by `b_bound`; RHS by Cauchy–Schwarz with
`∂ψw ∈ L^∞`), and they agree on the dense Schwartz×Schwartz set (`b_galerkin = convIntegralSchwartz`,
then `convIntegralSchwartz_divFree_eq`), so they agree everywhere.  This exposes the genuine `L¹`
Lebesgue integral that the limit-passage layer ball-splits (the nonlinear `b`-term passage). -/

/-- Multiplication of a real `L²` element by an essentially bounded real function, landing in
`L²` (local builder; only its `coeFn` and an `L²`-Lipschitz bound are needed). -/
private noncomputable def mulBddR (h : Domain3 → ℝ)
    (hh : MemLp h ⊤ (volume : Measure Domain3)) (a : Lp ℝ 2 (volume : Measure Domain3)) :
    Lp ℝ 2 (volume : Measure Domain3) :=
  (((Lp.memLp a).smul (p := ⊤) (q := 2) (r := 2) hh)).toLp

private theorem mulBddR_coeFn (h : Domain3 → ℝ)
    (hh : MemLp h ⊤ (volume : Measure Domain3)) (a : Lp ℝ 2 (volume : Measure Domain3)) :
    (mulBddR h hh a : Domain3 → ℝ) =ᵐ[volume] fun x => h x * a x := by
  filter_upwards [MemLp.coeFn_toLp (((Lp.memLp a).smul (p := ⊤) (q := 2) (r := 2) hh))]
    with x hx
  rw [mulBddR]; rw [hx]; rfl

private theorem norm_mulBddR_le (h : Domain3 → ℝ)
    (hh : MemLp h ⊤ (volume : Measure Domain3)) (a : Lp ℝ 2 (volume : Measure Domain3)) :
    ‖mulBddR h hh a‖ ≤ (eLpNorm h ⊤ (volume : Measure Domain3)).toReal * ‖a‖ := by
  have hnorm : ‖mulBddR h hh a‖
      = (eLpNorm (h • (a : Domain3 → ℝ)) 2 (volume : Measure Domain3)).toReal :=
    Lp.norm_toLp _ _
  have hcnorm : ‖a‖ = (eLpNorm a 2 (volume : Measure Domain3)).toReal := Lp.norm_def a
  rw [hnorm, hcnorm, ← ENNReal.toReal_mul]
  haveI hHT : ENNReal.HolderTriple ⊤ 2 2 := ⟨by simp⟩
  refine ENNReal.toReal_mono
    (ENNReal.mul_ne_top hh.eLpNorm_lt_top.ne (Lp.memLp a).eLpNorm_lt_top.ne) ?_
  exact eLpNorm_smul_le_mul_eLpNorm (Lp.aestronglyMeasurable _) hh.aestronglyMeasurable

private theorem mulBddR_sub (h : Domain3 → ℝ)
    (hh : MemLp h ⊤ (volume : Measure Domain3)) (a a' : Lp ℝ 2 (volume : Measure Domain3)) :
    mulBddR h hh a' - mulBddR h hh a = mulBddR h hh (a' - a) := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub (mulBddR h hh a') (mulBddR h hh a), mulBddR_coeFn h hh a',
    mulBddR_coeFn h hh a, mulBddR_coeFn h hh (a' - a), Lp.coeFn_sub a' a] with x h1 h2 h3 h4 h5
  rw [h1, Pi.sub_apply, h2, h3, h4, h5, Pi.sub_apply, mul_sub]

private theorem mulBddR_continuous (h : Domain3 → ℝ)
    (hh : MemLp h ⊤ (volume : Measure Domain3)) :
    Continuous (fun a : Lp ℝ 2 (volume : Measure Domain3) => mulBddR h hh a) := by
  -- `mulBddR` is `ℝ`-linear with operator bound `C := ‖h‖_∞`, hence `(C+1)`-Lipschitz.
  refine LipschitzWith.continuous (K := ((eLpNorm h ⊤ (volume : Measure Domain3)).toReal.toNNReal + 1))
    (LipschitzWith.of_dist_le_mul (fun a' a => ?_))
  rw [dist_eq_norm, dist_eq_norm, mulBddR_sub]
  calc ‖mulBddR h hh (a' - a)‖
      ≤ (eLpNorm h ⊤ (volume : Measure Domain3)).toReal * ‖a' - a‖ := norm_mulBddR_le h hh (a' - a)
    _ ≤ ((((eLpNorm h ⊤ (volume : Measure Domain3)).toReal.toNNReal : ℝ) + 1)) * ‖a' - a‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        rw [Real.coe_toNNReal _ ENNReal.toReal_nonneg]; linarith
    _ = (((eLpNorm h ⊤ (volume : Measure Domain3)).toReal.toNNReal + 1 : NNReal) : ℝ) * ‖a' - a‖ := by
        push_cast; ring

/-- The fixed-`w` antisymmetric integral form `Ψ_w(f,g) = -∑_{i,a} ∫ fₐ·gᵢ·(∂ₐψwᵢ)`, written via
`L²` inner products so its joint continuity in `(f,g)` is immediate. -/
@[irreducible] private noncomputable def antisymmIntegral (ψw : Fin 3 → SchwartzMap Domain3 ℝ)
    (hbdd : ∀ a i : Fin 3, MemLp
      (fun x => (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
        (EuclideanSpace.single a (1 : ℝ) : Domain3) (ψw i)) x) ⊤ (volume : Measure Domain3))
    (f g : L2VF_R3) : ℝ :=
  -(∑ i : Fin 3, ∑ a : Fin 3,
    (inner ℝ (L2VF_projComponent_R3 a f)
      (mulBddR (fun x => (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
          (EuclideanSpace.single a (1 : ℝ) : Domain3) (ψw i)) x) (hbdd a i)
        (L2VF_projComponent_R3 i g)) : ℝ))

/-- `antisymmIntegral` is jointly `L²`-continuous in `(f, g)`: a finite sum of inner products
`⟪comp_a f, mulBddR (∂ψw) (comp_i g)⟫`, each continuous (component CLMs ∘ `mulBddR` continuous ∘
`inner` continuous). -/
private theorem antisymmIntegral_continuous (ψw : Fin 3 → SchwartzMap Domain3 ℝ)
    (hbdd : ∀ a i : Fin 3, MemLp
      (fun x => (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
        (EuclideanSpace.single a (1 : ℝ) : Domain3) (ψw i)) x) ⊤ (volume : Measure Domain3)) :
    Continuous (fun p : L2VF_R3 × L2VF_R3 => antisymmIntegral ψw hbdd p.1 p.2) := by
  unfold antisymmIntegral
  refine continuous_neg.comp (continuous_finset_sum _ (fun i _ => continuous_finset_sum _
    (fun a _ => ?_)))
  -- `(f,g) ↦ ⟪comp_a f, mulBddR (∂ψw) (comp_i g)⟫` : inner of two continuous maps.
  refine continuous_inner.comp (Continuous.prodMk ?_ ?_)
  · exact (L2VF_projComponent_R3 a).continuous.comp continuous_fst
  · exact (mulBddR_continuous _ (hbdd a i)).comp
      ((L2VF_projComponent_R3 i).continuous.comp continuous_snd)

/-- A bounded multiplier `∂ₐψwᵢ` is `MemLp ⊤` (it is a Schwartz function, hence `L^∞`). -/
private theorem lineDerivOp_schwartz_memLp_top (ψ : SchwartzMap Domain3 ℝ) (a : Fin 3) :
    MemLp (fun x => (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
        (EuclideanSpace.single a (1 : ℝ) : Domain3) ψ) x) ⊤ (volume : Measure Domain3) := by
  have : (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
      (EuclideanSpace.single a (1 : ℝ) : Domain3) ψ).toLp 2 (volume : Measure Domain3)
      = (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
          (EuclideanSpace.single a (1 : ℝ) : Domain3) ψ).toLp 2 (volume : Measure Domain3) := rfl
  exact (SchwartzMap.memLp (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
    (EuclideanSpace.single a (1 : ℝ) : Domain3) ψ) ⊤ (volume : Measure Domain3))

/-! ### Step 1 lemmas: `F.b` continuity, Schwartz agreement, and the integral representation.
The main result `fb_eq_antisymmIntegral` says `F.b f g w = -∑_{i,a} ∫ (comp_a f)·(comp_i g)·(∂ₐψwᵢ)`
for ALL `f, g ∈ L²_σ` and Schwartz-div-free `w`; the RHS is a genuine `L¹` Lebesgue integral,
ball-splittable by the limit-passage layer.  Built by density extension of the Schwartz-pair
agreement using joint `L²`-continuity of both sides. -/

set_option maxHeartbeats 1000000 in
/-- `F.b (·) (·) w` is jointly `L²`-continuous at a fixed Schwartz `w` — from the bilinear bound
`b_bound` (`|F.b u v w| ≤ Cb·‖u‖·‖v‖`) together with bilinearity (`b_add`, `b_smul`).  Proved by
the standard bounded-bilinear ⇒ continuous estimate on the difference
`F.b u v w − F.b u₀ v₀ w = F.b (u−u₀) v w + F.b u₀ (v−v₀) w`. -/
theorem fb_continuous_fixedTest {𝔊 : R3GalerkinScheme} (F : R3NSForms 𝔊)
    (w : L2Sigma_R3) (hw : IsSchwartzDivFree_R3 w) :
    Continuous (fun p : L2Sigma_R3 × L2Sigma_R3 => F.b p.1 p.2 w) := by
  obtain ⟨Cb, hCb⟩ := F.b_bound w hw
  -- use `C := |Cb| + 1 > 0` so the bound `|F.b u v w| ≤ C ‖u‖ ‖v‖` holds with `0 < C`.
  set C : ℝ := |Cb| + 1 with hCdef
  have hCpos : 0 < C := by positivity
  have hCbound : ∀ u v : L2Sigma_R3, |F.b u v w| ≤ C * ‖(u : L2VF_R3)‖ * ‖(v : L2VF_R3)‖ := by
    intro u v
    refine (hCb u v).trans ?_
    have hle : Cb ≤ C := by rw [hCdef]; linarith [le_abs_self Cb]
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle (norm_nonneg _)) (norm_nonneg _)
  refine Metric.continuous_iff.2 (fun p ε hε => ?_)
  set M : ℝ := ‖(p.1 : L2VF_R3)‖ + ‖(p.2 : L2VF_R3)‖ + 1 with hM
  -- choose `δ = min 1 (ε / (2CM + 1))` so the small-difference bound also gives `‖q.2‖ ≤ M`.
  set δ : ℝ := min 1 (ε / (C * M + C * M + 1)) with hδ
  refine ⟨δ, lt_min one_pos (by positivity), fun q hq => ?_⟩
  rw [Prod.dist_eq, max_lt_iff, dist_eq_norm, dist_eq_norm] at hq
  obtain ⟨hq1, hq2⟩ := hq
  have hcoe1 : ‖q.1 - p.1‖ = ‖((q.1 : L2VF_R3) - (p.1 : L2VF_R3))‖ := by
    rw [← AddSubgroupClass.coe_sub]; rfl
  have hcoe2 : ‖q.2 - p.2‖ = ‖((q.2 : L2VF_R3) - (p.2 : L2VF_R3))‖ := by
    rw [← AddSubgroupClass.coe_sub]; rfl
  rw [hcoe1] at hq1; rw [hcoe2] at hq2
  -- the two small-norm facts and the `< δ ≤ ε/(2CM+1)` consequence.
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδ2 : δ ≤ ε / (C * M + C * M + 1) := min_le_right _ _
  have hq1' : ‖((q.1 : L2VF_R3) - (p.1 : L2VF_R3))‖ < ε / (C * M + C * M + 1) := lt_of_lt_of_le hq1 hδ2
  have hq2' : ‖((q.2 : L2VF_R3) - (p.2 : L2VF_R3))‖ < ε / (C * M + C * M + 1) := lt_of_lt_of_le hq2 hδ2
  have hdecomp : F.b q.1 q.2 w - F.b p.1 p.2 w
      = F.b (q.1 - p.1) q.2 w + F.b p.1 (q.2 - p.2) w := by
    have e1 : F.b q.1 q.2 w = F.b (q.1 - p.1) q.2 w + F.b p.1 q.2 w := by
      have := F.b_add_1 (q.1 - p.1) p.1 q.2 w; simpa [sub_add_cancel] using this
    have e2 : F.b p.1 q.2 w = F.b p.1 (q.2 - p.2) w + F.b p.1 p.2 w := by
      have := F.b_add_2 p.1 (q.2 - p.2) p.2 w; simpa [sub_add_cancel] using this
    rw [e1, e2]; ring
  rw [dist_eq_norm, Real.norm_eq_abs, hdecomp]
  have hb1 := hCbound (q.1 - p.1) q.2
  have hb2 := hCbound p.1 (q.2 - p.2)
  rw [AddSubgroupClass.coe_sub] at hb1 hb2
  -- `‖q.2‖ ≤ M`: `‖q.2‖ ≤ ‖p.2‖ + ‖q.2 - p.2‖ ≤ ‖p.2‖ + 1 ≤ M` (uses `δ ≤ 1`).
  have hq2n : ‖((q.2 : L2VF_R3))‖ ≤ M := by
    have htri : ‖(q.2 : L2VF_R3)‖
        ≤ ‖(p.2 : L2VF_R3)‖ + ‖((q.2 : L2VF_R3) - (p.2 : L2VF_R3))‖ := by
      have := norm_add_le (p.2 : L2VF_R3) ((q.2 : L2VF_R3) - (p.2 : L2VF_R3))
      simpa using this
    have hle1 : ‖((q.2 : L2VF_R3) - (p.2 : L2VF_R3))‖ ≤ 1 := le_trans hq2.le hδ1
    rw [hM]; linarith [htri, hle1, norm_nonneg (p.1 : L2VF_R3)]
  have hp1M : ‖((p.1 : L2VF_R3))‖ ≤ M := by rw [hM]; linarith [norm_nonneg (p.2 : L2VF_R3)]
  calc |F.b (q.1 - p.1) q.2 w + F.b p.1 (q.2 - p.2) w|
      ≤ |F.b (q.1 - p.1) q.2 w| + |F.b p.1 (q.2 - p.2) w| := abs_add_le _ _
    _ ≤ C * M * ‖((q.1 : L2VF_R3) - (p.1 : L2VF_R3))‖
          + C * M * ‖((q.2 : L2VF_R3) - (p.2 : L2VF_R3))‖ := by
        refine add_le_add ?_ ?_
        · calc |F.b (q.1 - p.1) q.2 w|
              ≤ C * ‖((q.1 : L2VF_R3) - (p.1 : L2VF_R3))‖ * ‖(q.2 : L2VF_R3)‖ := hb1
            _ = C * ‖(q.2 : L2VF_R3)‖ * ‖((q.1 : L2VF_R3) - (p.1 : L2VF_R3))‖ := by ring
            _ ≤ C * M * ‖((q.1 : L2VF_R3) - (p.1 : L2VF_R3))‖ := by
                refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
                exact mul_le_mul_of_nonneg_left hq2n hCpos.le
        · calc |F.b p.1 (q.2 - p.2) w|
              ≤ C * ‖(p.1 : L2VF_R3)‖ * ‖((q.2 : L2VF_R3) - (p.2 : L2VF_R3))‖ := hb2
            _ ≤ C * M * ‖((q.2 : L2VF_R3) - (p.2 : L2VF_R3))‖ := by
                refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
                exact mul_le_mul_of_nonneg_left hp1M hCpos.le
    _ < C * M * (ε / (C * M + C * M + 1)) + C * M * (ε / (C * M + C * M + 1)) := by
        have hM1 : (1:ℝ) ≤ M := by
          rw [hM]; linarith [norm_nonneg (p.1 : L2VF_R3), norm_nonneg (p.2 : L2VF_R3)]
        have hCM : 0 < C * M := mul_pos hCpos (by linarith)
        exact add_lt_add (mul_lt_mul_of_pos_left hq1' hCM) (mul_lt_mul_of_pos_left hq2' hCM)
    _ = ((C * M + C * M) / (C * M + C * M + 1)) * ε := by ring
    _ ≤ 1 * ε := by
        refine mul_le_mul_of_nonneg_right ?_ hε.le
        rw [div_le_one (by positivity)]; linarith
    _ = ε := one_mul ε

set_option maxHeartbeats 1600000 in
/-- The Schwartz-pair agreement: for Schwartz-div-free `f', g'`, `F.b f' g' w` equals the
antisymmetric integral.  `b_galerkin` rewrites `F.b` to `convIntegralSchwartz`, then
`convIntegralSchwartz_divFree_eq` gives the IBP'd integral, which matches `antisymmIntegral`'s
inner-product integrands a.e. -/
theorem fb_eq_antisymmIntegral_schwartz {𝔊 : R3GalerkinScheme} (F : R3NSForms 𝔊)
    (w : L2Sigma_R3) (ψw : Fin 3 → SchwartzMap Domain3 ℝ)
    (hψw : ∀ j : Fin 3,
      L2VF_projComponent_R3 j (w : L2VF_R3) = (ψw j).toLp 2 (volume : Measure Domain3))
    (f' g' : L2Sigma_R3) (hf' : IsSchwartzDivFree_R3 f') (hg' : IsSchwartzDivFree_R3 g') :
    F.b f' g' w
      = antisymmIntegral ψw
          (fun a i => lineDerivOp_schwartz_memLp_top (ψw i) a) (f' : L2VF_R3) (g' : L2VF_R3) := by
  classical
  obtain ⟨ψf, hψf⟩ := hf'
  obtain ⟨ψg, hψg⟩ := hg'
  rw [F.b_galerkin ψf ψg ψw f' g' w hψf hψg hψw,
    convIntegralSchwartz_divFree_eq ψf ψg ψw (schwartzDivFree_of_L2Sigma f' ψf hψf)]
  unfold antisymmIntegral
  congr 1
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun a _ => ?_))
  rw [MeasureTheory.L2.inner_def]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [show (L2VF_projComponent_R3 a (f' : L2VF_R3) : Domain3 → ℝ)
        =ᵐ[volume] fun x => (ψf a) x from by
      rw [hψf a]; exact (ψf a).coeFn_toLp 2 (volume : Measure Domain3),
    mulBddR_coeFn (fun x => (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
        (EuclideanSpace.single a (1 : ℝ) : Domain3) (ψw i)) x)
      (lineDerivOp_schwartz_memLp_top (ψw i) a)
      (L2VF_projComponent_R3 i (g' : L2VF_R3)),
    show (L2VF_projComponent_R3 i (g' : L2VF_R3) : Domain3 → ℝ)
        =ᵐ[volume] fun x => (ψg i) x from by
      rw [hψg i]; exact (ψg i).coeFn_toLp 2 (volume : Measure Domain3)]
    with x hfx hmulx hgx2
  rw [RCLike.inner_apply, conj_trivial, hfx, hmulx, hgx2]
  ring

set_option maxHeartbeats 800000 in
/-- **Step 1 (conjunct-2 atom b): the integral representation `F.b f g w = antisymmIntegral`.**
Density extension of `fb_eq_antisymmIntegral_schwartz` using joint `L²`-continuity of both sides
(`fb_continuous_fixedTest`; `antisymmIntegral_continuous`). -/
theorem fb_eq_antisymmIntegral {𝔊 : R3GalerkinScheme} (F : R3NSForms 𝔊)
    (w : L2Sigma_R3) (ψw : Fin 3 → SchwartzMap Domain3 ℝ)
    (hψw : ∀ j : Fin 3,
      L2VF_projComponent_R3 j (w : L2VF_R3) = (ψw j).toLp 2 (volume : Measure Domain3))
    (f g : L2Sigma_R3) :
    F.b f g w
      = antisymmIntegral ψw
          (fun a i => lineDerivOp_schwartz_memLp_top (ψw i) a) (f : L2VF_R3) (g : L2VF_R3) := by
  have hw_sch : IsSchwartzDivFree_R3 w := ⟨ψw, hψw⟩
  -- Both sides are continuous in `(f,g)` and agree on the dense Schwartz set.  Use the explicit
  -- `hbdd` term (not `set`) so all `antisymmIntegral` applications are syntactically identical.
  have hRHS_cont : Continuous
      (fun p : L2Sigma_R3 × L2Sigma_R3 =>
        antisymmIntegral ψw (fun a i => lineDerivOp_schwartz_memLp_top (ψw i) a)
          (p.1 : L2VF_R3) (p.2 : L2VF_R3)) :=
    (antisymmIntegral_continuous ψw (fun a i => lineDerivOp_schwartz_memLp_top (ψw i) a)).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))
  obtain ⟨sf, hsf_sch, hsf_lim⟩ := schwartzDivFree_dense_of_curlDense curlSchwartzDense_holds f
  obtain ⟨sg, hsg_sch, hsg_lim⟩ := schwartzDivFree_dense_of_curlDense curlSchwartzDense_holds g
  have hpair_lim : Filter.Tendsto (fun n => ((sf n, sg n) : L2Sigma_R3 × L2Sigma_R3))
      Filter.atTop (nhds (f, g)) := hsf_lim.prodMk_nhds hsg_lim
  have hLHS : Filter.Tendsto (fun n => F.b (sf n) (sg n) w) Filter.atTop (nhds (F.b f g w)) :=
    ((fb_continuous_fixedTest F w hw_sch).tendsto (f, g)).comp hpair_lim
  have hRHS := (hRHS_cont.tendsto (f, g)).comp hpair_lim
  refine tendsto_nhds_unique (hLHS.congr (fun n => ?_)) hRHS
  exact fb_eq_antisymmIntegral_schwartz F w ψw hψw (sf n) (sg n) (hsf_sch n) (hsg_sch n)

/-! ### Per-ball convergence of F.b (atom b — WeakFormNS limit passage) -/

/-- Schwartz tail decay: for any Schwartz map φ on Domain3 and ε > 0, there is R₀ > 0
with |φ(x)| < ε whenever ‖x‖ > R₀. Follows from `SchwartzMap.tendsto_cocompact`. -/
private theorem schwartz_ball_tail_decay (φ : SchwartzMap Domain3 ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ x : Domain3, R₀ < ‖x‖ → ‖φ x‖ < ε := by
  obtain ⟨K, hKcomp, hKsub⟩ :=
    Filter.mem_cocompact.mp (Metric.tendsto_nhds.mp φ.tendsto_cocompact ε hε)
  obtain ⟨R₀, hR₀pos, hKball⟩ := hKcomp.isBounded.subset_closedBall_lt 0 (0 : Domain3)
  refine ⟨R₀, hR₀pos, fun x hxR => ?_⟩
  have hxK : x ∉ K := fun hxK =>
    absurd (hKball hxK) (by rwa [Metric.mem_closedBall, dist_zero_right, not_le])
  simpa [dist_zero_right] using hKsub (Set.mem_compl hxK)

/-- Self-adjointness of real pointwise multiplication: `⟨f, h·g⟩ = ⟨h·f, g⟩`
in `Lp ℝ 2 volume`.

Both sides equal `∫ x, (↑f x) * h x * (↑g x) ∂μ` via `MeasureTheory.L2.inner_def`,
`mulBddR_coeFn`, and the identity `inner ℝ a b = a * b` for real scalars. -/
private theorem mulBddR_self_adjoint (h : Domain3 → ℝ) (hh : MemLp h ⊤ (volume : Measure Domain3))
    (f g : Lp ℝ 2 (volume : Measure Domain3)) :
    (inner ℝ f (mulBddR h hh g) : ℝ) = (inner ℝ (mulBddR h hh f) g : ℝ) := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [mulBddR_coeFn h hh f, mulBddR_coeFn h hh g] with x hxf hxg
  -- After RCLike.inner_apply (which gives ⟪a, b⟫_ℝ = conj a * b) and conj_trivial
  -- (conj is identity on ℝ), both sides reduce to a * h x * b expressions.
  simp only [RCLike.inner_apply, conj_trivial, hxf, hxg]
  ring

set_option maxHeartbeats 800000 in
/-- **Per-ball convergence of F.b (atom b of WeakFormNS passage).**

For a Schwartz-div-free test `w` with witnesses `ψw`, if `uₙ → u` in L²(B_R) for every
radius R (per-ball convergence) with uniform L² bound `‖uₙ‖ ≤ M`, then
`F.b(uₙ, uₙ, w) → F.b(u, u, w)`.

**Method.** After applying `fb_eq_antisymmIntegral` and unfolding `antisymmIntegral`, each
(i, a)-term is `inner (comp_a uₙ) (mulBddR φ_{a,i} (comp_i uₙ))`.  The bilinear difference
splits into:
- TERM A `= inner (comp_a (uₙ - u)) (mulBddR φ (comp_i uₙ))`: ε/3 split via
  `schwartz_ball_tail_decay` for the `‖x‖>R` tail and per-ball for the `‖x‖≤R` ball;
- TERM B `= inner (comp_a u) (mulBddR φ (comp_i (uₙ - u)))`: self-adjointness +
  scalar ball-tail ε/3 argument (tail of FIXED element → 0, ball uses per-ball). -/
theorem fb_tendsto_of_perball {𝔊 : R3GalerkinScheme} (F : R3NSForms 𝔊)
    (w : L2Sigma_R3) (hw : IsSchwartzDivFree_R3 w)
    (un : ℕ → L2Sigma_R3) (u : L2Sigma_R3)
    (M : ℝ) (hM0 : 0 ≤ M)
    (hbd : ∀ n, ‖(un n : L2VF_R3)‖ ≤ M)
    (hbu : ‖(u : L2VF_R3)‖ ≤ M)
    (hperball : ∀ k : ℕ, Filter.Tendsto
        (fun n => restrictToBall (k : ℝ) (un n : L2VF_R3))
        Filter.atTop (nhds (restrictToBall (k : ℝ) (u : L2VF_R3)))) :
    Filter.Tendsto (fun n => F.b (un n) (un n) w) Filter.atTop (nhds (F.b u u w)) := by
  obtain ⟨ψw, hψw⟩ := hw
  simp_rw [fb_eq_antisymmIntegral F w ψw hψw]
  -- Unfold the (private, @[irreducible]) def — allowed from within this file.
  unfold antisymmIntegral
  apply Filter.Tendsto.neg
  apply tendsto_finsetSum; intro i _
  apply tendsto_finsetSum; intro a _
  -- Abbreviated notation for this (i, a)-summand
  set φs : SchwartzMap Domain3 ℝ :=
    lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ) (EuclideanSpace.single a (1 : ℝ) : Domain3) (ψw i)
  set φ : Domain3 → ℝ := ⇑φs
  set hφ : MemLp φ ⊤ (volume : Measure Domain3) := lineDerivOp_schwartz_memLp_top (ψw i) a
  set cA := L2VF_projComponent_R3 a
  set cI := L2VF_projComponent_R3 i
  -- Reduce to showing the difference → 0
  suffices hd : Filter.Tendsto
      (fun n => (inner ℝ (cA (un n : L2VF_R3)) (mulBddR φ hφ (cI (un n : L2VF_R3))) : ℝ) -
               (inner ℝ (cA (u : L2VF_R3)) (mulBddR φ hφ (cI (u : L2VF_R3))) : ℝ))
      Filter.atTop (nhds 0) by
    have := hd.add (tendsto_const_nhds (x := (inner ℝ (cA (u : L2VF_R3)) (mulBddR φ hφ (cI (u : L2VF_R3))) : ℝ)))
    simp only [sub_add_cancel, zero_add] at this
    exact this
  -- Bilinear decomposition: diff = TERM_A + TERM_B
  have hdecomp : ∀ n,
      (inner ℝ (cA (un n : L2VF_R3)) (mulBddR φ hφ (cI (un n : L2VF_R3))) : ℝ) -
      (inner ℝ (cA (u : L2VF_R3)) (mulBddR φ hφ (cI (u : L2VF_R3))) : ℝ) =
      (inner ℝ (cA (un n : L2VF_R3) - cA (u : L2VF_R3))
          (mulBddR φ hφ (cI (un n : L2VF_R3))) : ℝ) +
      (inner ℝ (cA (u : L2VF_R3))
          (mulBddR φ hφ (cI (un n : L2VF_R3)) - mulBddR φ hφ (cI (u : L2VF_R3))) : ℝ) := by
    intro n
    linarith [inner_sub_left (𝕜 := ℝ) (cA (un n : L2VF_R3)) (cA (u : L2VF_R3))
                (mulBddR φ hφ (cI (un n : L2VF_R3))),
              inner_sub_right (𝕜 := ℝ) (cA (u : L2VF_R3)) (mulBddR φ hφ (cI (un n : L2VF_R3)))
                (mulBddR φ hφ (cI (u : L2VF_R3)))]
  simp_rw [hdecomp]
  -- TERM A → 0
  have htermA : Filter.Tendsto
      (fun n => (inner ℝ (cA (un n : L2VF_R3) - cA (u : L2VF_R3))
        (mulBddR φ hφ (cI (un n : L2VF_R3))) : ℝ)) Filter.atTop (nhds 0) := by
    sorry -- ALLOW_SORRY: TERM A ε/3 split (Schwartz decay on tail, per-ball on ball).
          -- |inner(cA(uₙ-u))(mulBddR φ (cI uₙ))| ≤ BALL + TAIL.
          -- BALL ≤ eLpNorm(φ,⊤) * ‖cA(uₙ-u)|_{B_R}‖ * M → 0 (‖cA(uₙ-u)|_{B_R}‖ ≤ ‖restrictToBall R(uₙ-u)‖ → 0 by hperball).
          -- TAIL ≤ sup_{‖x‖>R}|φ| * ‖cA(uₙ-u)‖ * M → 0 (schwartz_ball_tail_decay for φs + uniform bound 2M).
  -- TERM B → 0
  have htermB : Filter.Tendsto
      (fun n => (inner ℝ (cA (u : L2VF_R3))
        (mulBddR φ hφ (cI (un n : L2VF_R3)) - mulBddR φ hφ (cI (u : L2VF_R3))) : ℝ))
      Filter.atTop (nhds 0) := by
    -- self-adjointness: inner(cA u)(mulBddR φ (cI(uₙ-u))) = inner(mulBddR φ (cA u))(cI(uₙ-u))
    sorry -- ALLOW_SORRY: TERM B scalar ball-tail ε/3 argument.
          -- After mulBddR_self_adjoint + mulBddR_sub + map_sub:
          -- need inner(FIXED e_B)(cI(uₙ-u)) → 0 where e_B := mulBddR φ (cA u) ∈ Lp ℝ 2 vol.
          -- Tail of e_B → 0 (fixed-element tail vanishing by Vitali/dominated convergence).
          -- Ball: ‖e_B‖ * ‖cI(uₙ-u)|_{B_R}‖ → 0 (per-ball + comp_j ∘ restrictToBall = scalarBall ∘ comp_j).
  simpa only [add_zero] using htermA.add htermB

/-! ### P2 — Scaffold packaging for future `ConvectionGap` construction -/

/-- **P2 (scaffold-only).** Packaging of the density result as the `schwartz_dense`
field shape used by `ConvectionGap`.

This is a definitional wrapper around P1; useful as a named entry point for future
`ConvectionGap` instance construction once the five operator-extension fields are available.

Used as: `convectionGap_schwartz_dense curlSchwartzDense_holds` gives the density
needed for `ConvectionGap.schwartz_dense`. -/
lemma convectionGap_schwartz_dense (h : CurlSchwartzDense) :
    ∀ (u : L2Sigma_R3),
    ∃ s : ℕ → L2Sigma_R3, (∀ n, IsSchwartzDivFree_R3 (s n)) ∧
      Filter.Tendsto s Filter.atTop (nhds u) :=
  fun u => schwartzDivFree_dense_of_curlDense h u

/-! ### Issue #56 — `r3ConvectionGapOp_exists` REMOVED (proved as `r3ConvectionGapOp_holds`)

The former axiom `r3ConvectionGapOp_exists` (operator core, five `ConvectionGapOp` fields)
is NOW PROVED sorry-free as the theorem `r3ConvectionGapOp_holds` in
`LerayHopf/R3/ConvectionExtension.lean` (C11, determined-form construction).  It is NO
LONGER declared here as an axiom.

The theorem `r3_NSForms_exists` (same conclusion `Nonempty (R3NSForms 𝔊)`) is also now
located in `ConvectionExtension.lean`, where it is proved from `r3ConvectionGapOp_holds`
(NOT from an axiom) + proved density via `R3NSForms_of_gap`.  Net result: the operator core
is PROVED; no project axiom remains for the convection operator.  R3 capstone now rests on
TWO project axioms: `galerkin_limit_passage_R3` and `galerkin_spacetime_precompact_R3`. -/

end LerayHopf
