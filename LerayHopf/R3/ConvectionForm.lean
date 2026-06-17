import LerayHopf.R3.ConvectionOperator
import LerayHopf.R3.AxiomaticClosure

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
- `R3NSForms_of_gap`     : the conditional `ConvectionGap 𝔊 → Nonempty (R3NSForms 𝔊)`,
                           a genuine derivation of every `R3NSForms` field from Tier-S.

## Scaffold status

Proof body of `R3NSForms_of_gap` is placeholder this pass; it carries an `ALLOW_SORRY`
marker. **No new `axiom`/`opaque`/`constant`. `AxiomaticClosure.lean` is not edited.**
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
    -- DERIVED: directly from g.b_antisymm_gap (asserted over arbitrary L²_σ as the honest
    -- residual of the missing weak operator; NOT derived from continuity).
    sorry -- ALLOW_SORRY: scaffold (Tier G); derive R3NSForms.b_antisymm directly from g.b_antisymm_gap (∀ u v w, g.b u v w = - g.b u w v over arbitrary L2Sigma_R3); proved by lean-prover
  case b_add_1 =>
    -- DERIVED: from g.b_multilinear — obtain B, rewrite g.b _ _ _ = B _ _ _, close by B's
    -- map_add in slot 1. No continuity, no density; arbitrary u u' v w : L²_σ.
    sorry -- ALLOW_SORRY: scaffold (Tier G); derive R3NSForms.b_add_1 from g.b_multilinear — obtain B, rewrite g.b _ _ _ to B _ _ _, close by (B _ _).map_add / B.map_add in slot 1; works for arbitrary L2Sigma_R3 with no continuity/density; proved by lean-prover
  case b_add_2 =>
    sorry -- ALLOW_SORRY: scaffold (Tier G); derive R3NSForms.b_add_2 from g.b_multilinear — obtain B, rewrite to B, close by map_add in slot 2; proved by lean-prover
  case b_add_3 =>
    -- DERIVED: from g.b_multilinear via B's map_add in slot 3. The third-slot additivity over
    -- arbitrary w w' : L²_σ is purely algebraic (B is genuinely trilinear) — NO continuity.
    sorry -- ALLOW_SORRY: scaffold (Tier G); derive R3NSForms.b_add_3 from g.b_multilinear — obtain B, rewrite to B, close by map_add in the THIRD slot; this is the slot the false b_cont was wrongly invoked for, now supplied algebraically by the trilinear witness with no continuity; proved by lean-prover
  case b_smul_1 =>
    sorry -- ALLOW_SORRY: scaffold (Tier G); derive R3NSForms.b_smul_1 from g.b_multilinear — obtain B, rewrite to B, close by map_smul in slot 1; proved by lean-prover
  case b_smul_2 =>
    sorry -- ALLOW_SORRY: scaffold (Tier G); derive R3NSForms.b_smul_2 from g.b_multilinear — obtain B, rewrite to B, close by map_smul in slot 2; proved by lean-prover
  case b_smul_3 =>
    -- DERIVED: from g.b_multilinear via B's map_smul in slot 3 (purely algebraic, NO continuity).
    sorry -- ALLOW_SORRY: scaffold (Tier G); derive R3NSForms.b_smul_3 from g.b_multilinear — obtain B, rewrite to B, close by map_smul in the THIRD slot; algebraic, no continuity; proved by lean-prover
  case b_bound =>
    -- DERIVED: convFormSchwartz_bound (Tier S) gives the constant C at the GIVEN Schwartz w
    -- via g.b_extends; g.b_cont_fixedTest w hw (slots 1,2 at the fixed w) + g.schwartz_dense
    -- extend the inequality to all u v (the third slot w is fixed throughout).
    sorry -- ALLOW_SORRY: scaffold (Tier G); derive R3NSForms.b_bound — take the C from convFormSchwartz_bound w hw (w fixed, IsSchwartzDivFree_R3 w from the hypothesis); on the Schwartz class g.b_extends turns |g.b u v w| into |convFormSchwartz …| ≤ C‖u‖‖v‖; g.b_cont_fixedTest w hw (continuity of (u,v) ↦ g.b u v w at the fixed Schwartz w) + g.schwartz_dense extend the bound to all u v : L2Sigma_R3 with continuity of the norms; proved by lean-prover
  case b_galerkin =>
    -- DERIVED: convFormSchwartz_eq_witness (Tier S) + g.b_extends. The hypotheses give
    -- IsSchwartzDivFree_R3 u v w (the ψ's are the witnesses), so g.b_extends applies, then
    -- convFormSchwartz_eq_witness rewrites convFormSchwartz to convIntegralSchwartz ψu ψv ψw.
    sorry -- ALLOW_SORRY: scaffold (Tier G); derive R3NSForms.b_galerkin — from the toLp hypotheses build IsSchwartzDivFree_R3 u/v/w, rewrite g.b u v w to convFormSchwartz via g.b_extends, then close with convFormSchwartz_eq_witness u v w … ψu ψv ψw; proved by lean-prover

end LerayHopf
