# Task Contract — Stream C: The `(u·∇)v` convection operator/form on `L²_σ(ℝ³)`

**Milestone / stream:** `stream-c-convection-operator`
**Objective:** substantiate (toward eventually discharging) the `r3_NSForms_exist`
axiom in `LerayHopf/R3/SolutionInterfaces.lean` by constructing a *concrete*
`R3NSForms 𝔊` — i.e. a genuine trilinear convection form `b` defined on **all** of
`L2Sigma_R3`, not just on Schwartz-representable fields.
**New file deliverable:** `LerayHopf/R3/ConvectionOperator.lean` (sibling; substantiation only).
**Plan reference:** `HANDOFF.md` §5 P1 ("very heavy"); `LerayHopf/R3/SolutionInterfaces.lean`
lines 185–272 (`R3NSForms`, `r3_NSForms_exist`); `LerayHopf/R3/TrilinearEstimate.lean`
(R3-d proved Schwartz-level content); `LerayHopf/R3/DivergenceFree.lean`
(`convIntegralSchwartz`, `L2Sigma_R3`); `LerayHopf/R3/Regularity.lean`
(`memH1VF_R3`, `viscousFormSq_R3`, `IsSchwartzDivFree_R3`).

> Discipline note (`lean-formalization-discipline`): this contract was written
> Mathlib-boundary-first; it gives an honest gap-size, isolates the genuine gaps at
> the least-abstract level as clean `structure` fields / `∀∃` hypotheses (never new
> `axiom`s, never weakened statements), and uses standard Mathlib API where it exists
> (`SchwartzMap.denseRange_toLpCLM`, the GNS family in `SobolevInequality.lean`).

---

## 0. TL;DR verdict (read this first)

**A concrete `R3NSForms` on all of `L²_σ(ℝ³)` is NOT reachable axiom-free today, and
NOT reachable by a thin density lift of R3-d alone.** The blocker is genuine, not
cosmetic, and it is *months-class* if pursued to the bottom. Precisely:

- The trilinear convection form `b(u,v,w) = ∫(u·∇)v·w` is **unbounded in pure L² × L² ×
  L² norms**. R3-d's proved bound (`convIntegralSchwartz_bound_sup`) needs `‖∇w‖_∞ < ∞`
  (an L∞ slot). So `b` does **not** extend continuously from Schwartz triples to
  `L²_σ × L²_σ × L²_σ` by density. There is no continuous-extension shortcut.
- The honest functional-analytic home of `b` is `H¹ × H¹ × H¹` (or the
  Ladyzhenskaya/GN-interpolated `L⁴` class). The estimate
  `|b(u,v,w)| ≤ C‖u‖_{L²}^{1/4}‖u‖_{H¹}^{3/4} · ‖v‖_{H¹} · ‖w‖_{L²}^{1/4}‖w‖_{H¹}^{3/4}`
  (3D Ladyzhenskaya, via `L⁴(ℝ³) ↪ H^{3/4}`) is the genuine bound and is **not present
  in Mathlib** in usable form (see §4 Mathlib audit: only the `ContDiff`+`HasCompactSupport`
  GNS inequality `eLpNorm_le_eLpNorm_fderiv` exists, in `fderiv` form, no fractional/
  interpolation Sobolev norms, no `L⁴` product estimate).
- `R3NSForms.b` has type `L2Sigma_R3 → L2Sigma_R3 → L2Sigma_R3 → ℝ` (total on L²_σ).
  A genuine `(u·∇)v` for arbitrary L²_σ fields requires the missing P1 pillar (weak
  derivative + product + IBP/divergence theorem for `Lp` fields). **No honest total `b`
  is definable today** without smuggling.

**Therefore the deliverable shape is CONDITIONAL**, not `… → Nonempty (R3NSForms 𝔊)`
unconditionally. We deliver:

1. A genuine, axiom-free **partial** convection form on the Schwartz-div-free class,
   lifted from R3-d (this is real, provable, and useful — see §5 Tier S).
2. A precise, minimal **`structure ConvectionGap`** (clean `∀∃` Prop fields, no new
   `axiom`) capturing *exactly* the missing Mathlib pillars (weak `(u·∇)v` operator +
   3D trilinear/Ladyzhenskaya bound), at the least-abstract level.
3. A **`theorem`** (must-prove) of the form
   `ConvectionGap 𝔊 → Nonempty (R3NSForms 𝔊)`
   that assembles a concrete `R3NSForms` from the isolated gap hypotheses + R3-d lemmas.

This (a) makes the *axiom-free remainder* maximal, (b) names the genuine gap honestly
(no overclaim, no smuggle), and (c) leaves a single clean conditional whose hypothesis
is the literal P1 pillar — discharging `ConvectionGap` later (once Mathlib or a future
stream supplies the weak-derivative calculus) discharges `r3_NSForms_exist` for free.

`SolutionInterfaces.lean` is **NOT edited** (capstone wiring deferred; see §8).

---

## 1. Mathlib boundary audit (pressure-tested against `.lake/packages/mathlib/`)

| Ingredient needed | Mathlib status | Usable here? |
|---|---|---|
| Schwartz dense in `Lp` (`p ≠ ⊤`) | `SchwartzMap.denseRange_toLpCLM` (SchwartzSpace/Basic.lean:1379), `toLpCLM` (1365), `continuous_toLp` (1376) | **YES** — foundation for the partial form's density characterization and for the gap's well-definedness premise. |
| `MemSobolev s p` via Fourier, `MemSobolev.lineDerivOp`, `.add/.smul`, `SchwartzMap.memSobolev` | `Analysis/Distribution/Sobolev.lean:149,201,281,…` (already used by `memH1VF_R3`) | **PARTIAL** — gives H¹ membership of distributions and that `∂_a` lowers order by 1, but **no** `(u·∇)v` product, **no** pairing `⟨(u·∇)v, w⟩` as an L² integral, **no** IBP/divergence theorem on `Lp`. |
| Weak/distributional derivative of an `Lp` function as an `Lp`/distribution | `lineDerivOp` on `𝓢'` exists; `Lp → 𝓢'` coercion exists (`Lp.instCoeDep`). No "derivative of an `Lp` fn is again `Lp`" without the `MemSobolev` hypothesis. | **PARTIAL** — only along the `MemSobolev` route, complex-valued. |
| Divergence of `Lp` field / divergence theorem for `Lp` | **ABSENT.** Only `SchwartzMap.integral_mul_lineDerivOp_right_eq_neg_left` (Schwartz IBP, Deriv.lean:295) — already exhausted by R3-d. | **NO** — this is the core of the gap. |
| Pointwise product `(u·∇)v · w` integrable for L²/H¹ fields | **ABSENT** — needs L⁴×L⁴×L² Hölder + Sobolev embedding `H¹(ℝ³) ↪ L⁶` / `↪ L⁴`. | **NO**. |
| 3D Gagliardo–Nirenberg / Ladyzhenskaya `‖u‖_{L⁴} ≤ C‖u‖_{L²}^{1/4}‖∇u‖_{L²}^{3/4}` | **ABSENT in usable form.** `eLpNorm_le_eLpNorm_fderiv*` (SobolevInequality.lean:442–707) is `ContDiff ℝ 1` + `HasCompactSupport`, stated in `fderiv` and `eLpNorm`, **no** fractional/interpolation norms, **no** L²-L∇L² split, **no** Sobolev-embedding `H¹ ↪ L⁶`. | **NO** (would need a substantial build to specialize even on Schwartz fns). |
| Continuous bilinear/trilinear extension by density (BCLM) | `LinearMap.extend`/`DenseInducing.extend`, `ContinuousLinearMap` uniform-extension API exists | **YES but inapplicable** — `b` is NOT uniformly continuous in the L² topology (see §0), so the standard extension lemma's hypothesis fails. This is the precise reason the density lift does not close the gap. |

**Net Mathlib verdict:** the foundation (Schwartz density, `MemSobolev`, Schwartz IBP)
exists and is already used; the *operator* (`(u·∇)v` for `Lp` fields, IBP/divergence on
`Lp`, the 3D trilinear estimate) is genuinely absent. R3-d already extracted everything
the Schwartz layer can give. The remaining content is exactly the P1 "new calculus".

---

## 2. No-smuggle / no-overclaim audit

- **Cannot** define `b u v w := convIntegralSchwartz (rep u) (rep v) (rep w)` for chosen
  Schwartz representatives of general L²_σ fields: general L²_σ fields have **no** Schwartz
  representative, so `rep` does not exist; using `Classical.choice` on the (false) "every
  L² fn is Schwartz" would be smuggling a false premise. Forbidden.
- **Cannot** define `b := 0` off the Schwartz class: violates `b_galerkin`/non-vacuity and
  is the exact "secretly-Stokes" overclaim the project guards against.
- **Cannot** extend `b` by L²-density continuity: `b` is L²-discontinuous (unbounded in
  three L² slots). The continuous-extension lemma's uniform-continuity hypothesis is
  *false*; invoking it would weaken the statement to triviality. Forbidden.
- **Allowed and honest:** isolate the missing operator as a `structure ConvectionGap`
  whose fields are precise `∀∃`/Prop statements of the genuine missing facts (existence of
  a total trilinear `b` agreeing with `convIntegralSchwartz` on Schwartz triples + the 3D
  bound). This is a hypothesis, not an `axiom`; it does not enter any theorem *name*; the
  resulting theorem is conditional and labelled as such.

This keeps the no-overclaim rule: no theorem name asserts the convection form *exists*; the
existence is gated behind the explicit `ConvectionGap` hypothesis.

---

## 3. Deliverable shape (decision)

**Conditional**, in two honest pieces:

- **(S) Axiom-free partial form** — a genuine convection functional on the Schwartz
  div-free class, defined directly from `convIntegralSchwartz`, with all R3-d properties
  re-exported at the `L2Sigma_R3` level (via `IsSchwartzDivFree_R3` witnesses). Sorry-free.
- **(G) Conditional concrete `R3NSForms`** — `ConvectionGap 𝔊 → Nonempty (R3NSForms 𝔊)`,
  must-prove, assembling the structure from the gap hypotheses and R3-d lemmas.

We do **not** deliver `(u₀ …) → Nonempty (R3NSForms 𝔊)` unconditionally; that would
require discharging `ConvectionGap`, which is the months-class P1 pillar.

---

## 4. New file: `LerayHopf/R3/ConvectionOperator.lean`

### 4.1 Imports (coder owns)

```
import LerayHopf.R3.TrilinearEstimate   -- R3-d proved lemmas (pulls DivergenceFree, Domain)
import LerayHopf.R3.Regularity          -- IsSchwartzDivFree_R3, memH1VF_R3, L2VF norms
```

Do **not** import `SolutionInterfaces.lean` if it can be avoided; but `R3NSForms` is defined
there, so the conditional assembly theorem (G) **must** import it. Resolve by putting
Tier S (partial form, no `R3NSForms` mention) in this file and Tier G in a thin sibling
`LerayHopf/R3/ConvectionForm.lean` that imports both `ConvectionOperator` and
`AxiomaticClosure`. (Importing `AxiomaticClosure` is allowed; *editing* it is not.)

> Coder decides the 1-file vs 2-file split based on import hygiene; prefer 2 files
> (Small-PR rule), keeping the `R3NSForms`-dependent assembly isolated.

### 4.2 Namespace / opens

```
namespace LerayHopf
open MeasureTheory LineDeriv SchwartzMap
```

---

## 5. Declarations in dependency order

Legend: **[coder]** = signature/structure/def shell (no proof body beyond `rfl`-level);
**[prover]** = proof body. **MUST-PROVE** = sorry-free target. **SCAFFOLD** = placeholder/
Prop-field only.

### Tier S — Axiom-free Schwartz-div-free partial convection form (MUST-PROVE)

Re-package R3-d into `L2Sigma_R3`-level statements using `IsSchwartzDivFree_R3` witnesses.
No new analysis; pure transport of existing lemmas.

- **S1 `convFormSchwartzWitness`** [coder] — given `u v w : L2Sigma_R3` together with
  Schwartz-component witnesses `ψu ψv ψw` (from `IsSchwartzDivFree_R3`), the real value
  `convIntegralSchwartz ψu ψv ψw`. *(A `def`, plus a well-definedness `lemma` below.)*
  Dep: `convIntegralSchwartz`. MUST-PROVE (def).

- **S2 `convForm_witness_wd`** [prover] — **well-definedness**: if two Schwartz tuples
  represent the same L²_σ fields (equal `toLp` classes), the `convIntegralSchwartz` values
  agree. Needed because `IsSchwartzDivFree_R3` exposes *some* witness, not a canonical one.
  Proof: `convIntegralSchwartz` depends on the witnesses only through their `toLp 2`
  classes (each factor enters via an integral that is a.e.-class-determined), so equal
  `toLp` ⇒ equal value via `integral_congr_ae` + `coeFn_toLp`. Dep: S1. MUST-PROVE.
  Dep: `SchwartzMap.coeFn_toLp`, R3-d `integrand_integrable'`.
  **Honest gap-size: medium.** This is the one genuinely new (small) lemma; it is the
  a.e.-determinacy of the Schwartz integral. Provable with current Mathlib.

- **S3 `convFormSchwartz`** [coder] — the well-defined map
  `(u v w : L2Sigma_R3) → IsSchwartzDivFree_R3 u → IsSchwartzDivFree_R3 v →
   IsSchwartzDivFree_R3 w → ℝ`, via `Exists.choose` of the witnesses + S2 for
  independence. Dep: S1, S2. MUST-PROVE (def).

- **S4–S9 multilinearity & smul** [prover] — additivity and ℝ-homogeneity of
  `convFormSchwartz` in each slot, on the div-free class. Direct transport of R3-d
  `convIntegralSchwartz_add_{1,2,3}` / `convIntegralSchwartz_smul_{1,2,3}` through S2/S3.
  MUST-PROVE. **Gap-size: small** (transport).

- **S10 `convFormSchwartz_antisymm`** [prover] — `b u v w = - b u w v` for div-free
  `u,v,w`, from R3-d `convIntegralSchwartz_antisymm_of_divFree`. The R3-d lemma needs the
  Schwartz-level `hdiv`; supply it from `u ∈ L2Sigma_R3` unfolded against the chosen
  Schwartz witness (the `divTestFunctional φ u = 0` definition of `L2Sigma_R3`, specialized
  and IBP'd to the `hdiv` shape). MUST-PROVE. **Gap-size: medium** — bridging
  `L2Sigma_R3` membership to the Schwartz `hdiv` predicate is the substantive sub-step;
  it is provable (same content R3-d's `divFree_intLeft` already handles, now at the L² level).

- **S11 `convFormSchwartz_bound`** [prover] — the `b_bound` shape on the div-free class:
  `|b u v w| ≤ C(w) ‖u‖ ‖v‖` for `IsSchwartzDivFree_R3 w`, from R3-d
  `convIntegralSchwartz_bound_sup` + `SchwartzMap.norm_toLp'` to convert component
  `toLp` norms to `‖u‖_{L2VF_R3}` (or to a constant times it). MUST-PROVE.
  **Gap-size: medium** — the norm bookkeeping (component `toLp` sums vs the
  `EuclideanSpace`-valued L² norm) is the only real work; standard.

> Tier S is the maximal axiom-free deliverable. It is genuinely useful: it gives the
> project a *real* convection form on a dense class with proven properties, independent of
> the gap.

### Tier G — The isolated gap and the conditional concrete `R3NSForms`

- **G1 `ConvectionGap`** [coder] — **the minimal isolated hypothesis** (NOT an axiom; a
  `structure` of Prop fields). Captures *exactly* the two genuine Mathlib-absent pillars:

  ```
  structure ConvectionGap (𝔊 : R3GalerkinScheme) where
    -- (i) a total trilinear convection form on L²_σ
    b        : L2Sigma_R3 → L2Sigma_R3 → L2Sigma_R3 → ℝ
    b_antisymm : ∀ u v w, b u v w = - b u w v
    b_add_1 / b_add_2 / b_add_3 / b_smul_1 / b_smul_2 / b_smul_3 : (multilinearity)
    -- (ii) the genuine 3D trilinear bound on the canonical Schwartz test class
    b_bound  : ∀ w, IsSchwartzDivFree_R3 w →
                 ∃ C, ∀ u v, |b u v w| ≤ C * ‖(u:L2VF_R3)‖ * ‖(v:L2VF_R3)‖
    -- (iii) agreement with the genuine Schwartz convection integral (faithfulness pin)
    b_galerkin : (exact b_galerkin field shape from R3NSForms, lines 242–253)
  ```

  SCAFFOLD (Prop-carrying structure; no proof obligations here — it is the hypothesis).
  **This is, field-for-field, the content of `R3NSForms`** — deliberately so: the gap is
  *precisely* "a genuine `R3NSForms` exists", with the non-trivial fields being the ones
  Mathlib cannot yet furnish (`b` total + `b_bound`). Isolating it as a named structure
  documents the gap at the least-abstract level and makes the conditional theorem trivial.

  **No-smuggle check:** every field is a true property of the genuine `∫(u·∇)v·w`; none is
  vacuous (`b_galerkin` excludes `b=0`); the structure adds no false premise. It is exactly
  the missing pillar, not a convenience over-assumption.

- **G2 `R3NSForms_of_gap`** [prover] — **the conditional theorem (MUST-PROVE)**:

  ```
  theorem R3NSForms_of_gap (𝔊 : R3GalerkinScheme) (g : ConvectionGap 𝔊) :
      Nonempty (R3NSForms 𝔊)
  ```

  Proof: assemble the `R3NSForms` record field-by-field from `g`'s fields (they are aligned
  by construction). Trivial once `ConvectionGap` mirrors `R3NSForms`. Dep: G1, imports
  `AxiomaticClosure`. MUST-PROVE. **Gap-size: trivial** (structure repacking).

  *Rationale for splitting G1/G2 rather than just re-deriving:* it makes the *conditional*
  explicit and CI-checkable, and lets a future stream discharge `ConvectionGap` once
  (anywhere) to close `r3_NSForms_exist` everywhere, without touching the assembly.

- **G3 (optional, documentation)** `convForm_gap_partial_consistent` [prover] — a lemma
  that any `ConvectionGap.b` agrees with `convFormSchwartz` (Tier S) on the div-free class,
  via the shared `b_galerkin`/`b_galerkin`-pin. Ties Tier S to Tier G, demonstrating the
  partial form is the restriction of any gap-witness. MUST-PROVE. **Gap-size: small.**
  Mark optional; include only if cheap.

---

## 6. Dependency edges

```
DivergenceFree (convIntegralSchwartz)        Regularity (IsSchwartzDivFree_R3, norms)
        │                                              │
        └──────────────► TrilinearEstimate (R3-d) ◄────┘
                                  │
                                  ▼
        ConvectionOperator.lean:  S1 → S2 → S3 → {S4..S9, S10, S11}   [Tier S, axiom-free]
                                  │
                                  ▼
        ConvectionForm.lean (imports AxiomaticClosure):
                                  G1 (ConvectionGap)  →  G2 (R3NSForms_of_gap)
                                                       →  G3 (optional, also uses Tier S)
```

No edge points into `SolutionInterfaces.lean` (it is unedited; only imported by Tier G).

---

## 7. Assumptions to package

- **No new `axiom`.** The genuine gap is packaged as the `structure ConvectionGap`
  (Prop-field hypothesis), discharged by the caller, never asserted.
- Tier S is fully axiom-free and sorry-free.
- Tier G is axiom-free *conditional* on `ConvectionGap`; the conditional is the honest
  encoding of P1 (weak `(u·∇)v` + 3D trilinear bound + IBP/divergence on `Lp`).

---

## 8. Confirm: no `SolutionInterfaces.lean` edit

Confirmed. This stream **substantiates** `r3_NSForms_exist` in sibling files only:
- it proves the axiom-free Schwartz-level partial form (Tier S);
- it reduces the axiom to a single named, minimal hypothesis (`ConvectionGap`) via a
  must-prove conditional (Tier G).

The **capstone** — actually replacing `axiom r3_NSForms_exist` with `R3NSForms_of_gap`
applied to a discharged `ConvectionGap` — is **deferred** (it cannot happen until
`ConvectionGap` is dischargeable, i.e. until the P1 pillar lands). When that day comes, the
edit to `SolutionInterfaces.lean` is one line and is owned by a future coder task, not this one.

---

## 9. Codex adversarial-review points (orchestrator runs `/codex:adversarial-review --effort xhigh`)

Review **statements** before proofs:
1. **S2 `convForm_witness_wd`** — confirm well-definedness is genuinely a.e.-class
   determined and the formulation is not accidentally vacuous.
2. **S10 `convFormSchwartz_antisymm`** — confirm the `L2Sigma_R3 → hdiv` bridge is sound
   (that `divTestFunctional φ u = 0` IBP's to R3-d's `hdiv` shape) and not over/under-strong.
3. **G1 `ConvectionGap`** — **the critical review.** Confirm: (a) every field is a true
   property of `∫(u·∇)v·w` (no over-assumption beyond P1), (b) `b_bound` is the canonical
   `IsSchwartzDivFree_R3` class (not narrowed), (c) `b_galerkin` non-vacuity pin matches
   `R3NSForms` exactly, (d) the structure is genuinely the *minimal* gap, not a convenience
   bundle that smuggles trivial discharge.
4. **G2 `R3NSForms_of_gap`** — confirm it is a faithful conditional (no hidden weakening of
   `R3NSForms`), and that its existence does not let `r3_NSForms_exist` be discharged
   *vacuously* (it cannot: `ConvectionGap` is undischarged).

---

## 10. Definition of done

- **MUST-PROVE (sorry-free):** S1–S11 (Tier S partial form, axiom-free) and G1–G2 (the
  isolated gap structure + the conditional `R3NSForms_of_gap`). G3 optional.
- **`lake build` green**, preflight clean, no new `axiom`/`sorry`/`opaque`.
- `SolutionInterfaces.lean` unchanged.
- The contract's honest scope is met: maximal axiom-free remainder extracted; the
  irreducible P1 gap isolated as one minimal named hypothesis with a trivial conditional
  to `R3NSForms`.

---

## 11. Parallelism with Streams A / B / D

- **Independent of B (Aubin–Lions / Bochner time) and D** — no shared symbols beyond the
  already-merged R3-a/b/c/d layer; can run fully in parallel.
- **Shares a foundation with Stream A** if A is the weak-derivative / Fourier-Sobolev
  stream: both build on `Analysis/Distribution/Sobolev.lean` (`MemSobolev`, `lineDerivOp`)
  and `SchwartzSpace` (`denseRange_toLpCLM`, Schwartz IBP). **No file-level conflict** for
  *this* stream as scoped (Tier S + the `ConvectionGap`/conditional), because we do NOT
  attempt to discharge `ConvectionGap` here. If/when a later task tries to *discharge*
  `ConvectionGap` (build the genuine `(u·∇)v` operator + 3D Ladyzhenskaya bound), it must
  be **sequenced after Stream A** — that discharge is exactly the weak-derivative/3D-Sobolev
  calculus A would provide, and is the months-class core of P1.

**Candor:** the scoped deliverable here (Tier S + isolated gap + conditional) is a
**1–2 PR, days-class** task and is genuinely valuable (axiom-free partial form + honest gap
isolation). **Actually constructing a total concrete `R3NSForms`** — i.e. discharging
`ConvectionGap` — is **months-class**: it requires a weak `(u·∇)v` operator on `Lp`/H¹,
IBP/divergence theorem for `Lp` fields, and the 3D trilinear (Ladyzhenskaya/GN) estimate,
none of which Mathlib provides in usable form. This stream deliberately does **not** promise
that; it makes the remaining gap as small, explicit, and well-isolated as possible.
