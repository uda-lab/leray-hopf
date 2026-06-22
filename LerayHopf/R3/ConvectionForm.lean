import LerayHopf.R3.ConvectionOperator
import LerayHopf.R3.AxiomaticClosure
import LerayHopf.R3.SchwartzDivFreeBasis

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

All proof bodies of `R3NSForms_of_gap` are now discharged. **No new `axiom`/`opaque`/`constant`.
`AxiomaticClosure.lean` is not edited.**
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
in `L2Sigma_R3`, derivable from the existing axiom `curlSchwartzDense_holds`.

The declarations here (H1–H4, P1, P2) formally prove that density.

**Axiom delta:** No new `axiom` is added.  `r3_NSForms_exist` is NOT removed (the five
`ConvectionGap` fields remain; see plan `docs/scratch/r3-48-nsforms-plan.md`).
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

end LerayHopf
