# Phase plan — removing `torus3_NSForms_exist` (T³ 4 → 3 axioms)

**Author:** lean-planner
**Date:** 2026-06-21
**Goal as stated:** PROVE `Nonempty Torus3NSForms` (construct the witness), driving
`exists_lerayHopf_torus3` from 4 project axioms to 3 — the real goal, not
frontier-isolation.
**Scope rule:** planning document only. No Lean edits proposed inline; this produces a
contract for `lean-coder` / `lean-prover`.

---

## 0. Source-of-truth reconciliation (READ FIRST — affects everything)

The task prompt describes "current code on main = `5b3c561`" and asserts that PR #27 has
already landed the finite Galerkin lemmas
(`galerkinConvection_add_1/2/3`, `_smul_1/2/3`, `coeff_zero_outside_box`,
`galerkinConvection_bound`, `galerkinConvection_antisymm`).

**These lemmas do not exist in the actual working tree.** The repo HEAD is `3a66d66`
(`main`). I verified:

- `LerayHopf/Torus/SolutionInterfaces.lean` (read in full) contains `galerkinConvection`
  (def at :89), `IsGalerkinTest` (:123), `Torus3NSForms` (:151), the axiom
  `torus3_NSForms_exist` (:203), and the assembly. It contains **none** of the
  `galerkinConvection_add_*`, `_smul_*`, `_bound`, `_antisymm`, `coeff_zero_outside_box`
  lemmas.
- `Grep galerkinConvection_add_1|galerkinConvection_smul_1|galerkinConvection_antisymm`
  over the entire repo → **no files found**.

**Consequence for sequencing.** Every finite lemma the construction leans on must be
treated as *to-be-built-here* (PR-0 below), not as an existing dependency. If PR #27 lands
upstream first, PR-0 collapses to a no-op import. This does not change the verdict, only
the work breakdown. The verdict below is computed assuming those finite lemmas are
available (whether from #27 or PR-0), so it is the optimistic reading.

---

## 1. FEASIBILITY VERDICT — **RED** (genuine construction), with a GREEN fallback that does NOT remove the axiom

### 1.1 Verdict statement

The **stated goal** — constructing a closed-form witness of `Nonempty Torus3NSForms`
sorry-free and project-axiom-free (only `Classical.choice`) via a Hamel-basis linear
extension of the trig-polynomial convection form — is **RED**. It cannot be completed at
the floor (no new axiom, no sorry) without smuggling the missing analytic operator back in
under a different name. The obstruction is mathematical, not a mathlib-API gap, so no
amount of API survey rescues it.

The **floor-safe fallback** — the R3-mirror isolation `TorusConvectionGap` +
`Torus3NSForms_of_gap` — is **GREEN** (lands sorry-free, no new axiom), but it **does not
remove `torus3_NSForms_exist`**: it replaces the fat structure-existence axiom with a
thinner `Prop`/data hypothesis that is then either (a) carried as a new isolated axiom
[net 0 on count, thinner content] or (b) left as a conditional theorem with no axiom but
the capstone still wired through the original `torus3_NSForms_exist`. Neither path achieves
4 → 3 honestly. **If the requirement is strictly "drop to 3 project axioms," the honest
answer is: not reachable today.**

I will not return a wrong GREEN. The construction key proposed in the prompt is *almost*
right and fails on one specific, load-bearing field. The rest of this document proves
exactly where, surveys the APIs (so a future attempt is not starting cold), and specifies
the GREEN fallback in full.

### 1.2 The decisive obstruction — antisymmetry vs. the Galerkin pin over arbitrary L²

Write `P = ` the trig-polynomial subspace of `L2Sigma` (finite Fourier support; every
`IsGalerkinTest` element lives here, and every `Vₙ` triple). Write `Q` for an algebraic
complement, so `L2Sigma = P ⊕ Q` (Hamel, `Classical`-powered). The genuine finite
convection `β(u,v,w) = galerkinConvection N u v w` (for `N` large enough to contain the
supports) is defined and trilinear **on `P × P × P`** and is genuinely antisymmetric in
slots 2↔3 there (this is `galerkinConvection_antisymm`, but ONLY in its `Vₙ`-restricted
form — see §1.3). The construction wants to extend `β` to a total trilinear `b` on
`L2Sigma³` keeping:

- (G) `b = β` on `P³` (so `b_galerkin` holds, non-vacuously);
- (A) `b u v w = -b u w v` for **all** `u,v,w ∈ L2Sigma`;
- (B) `|b u v w| ≤ C(w)‖u‖‖v‖` for `w ∈ P`.

**Claim: (G) + (A) are jointly satisfiable, but only if `b` is forced to the genuine value
whenever EITHER of slots 2 or 3 lies in `P`, and (B) then forces a quantitative bound on a
form that is genuinely the analytic `−∫(u·∇)w·v` on `u ∈ Q`, `w ∈ P` — which is exactly
the operator Lean lacks.**

Concretely. Fix `w ∈ P` (a Galerkin test). (A) says `b(u,v,w) = -b(u,w,v)`. Now `b(u,w,v)`
has its slot-2 argument `w ∈ P`. By trilinearity + (G)-on-the-`P`-part, the value
`b(u,w,v)` is **not free**: decompose `u = u_P + u_Q`, `v = v_P + v_Q`. Trilinearity gives

```
b(u,w,v) = b(u_P,w,v_P) + b(u_P,w,v_Q) + b(u_Q,w,v_P) + b(u_Q,w,v_Q).
```

The first term is genuine (`β`). The terms `b(u_P,w,v_Q)`, `b(u_Q,w,v_P)`, `b(u_Q,w,v_Q)`
involve a `Q`-direction in slot 1 or slot 3 with `w ∈ P` fixed in slot 2. Antisymmetry (A)
applied again relates `b(u_Q,w,v_P)` to `-b(u_Q,v_P,w)` whose slot-3 is now `w ∈ P`. So the
"junk on Q" you wanted to assign freely is **chained by antisymmetry back onto
configurations with a `P`-element in the privileged slot**, where (B) demands a genuine
quantitative bound `|·| ≤ C(w)‖u_Q‖‖v_P‖`.

That bound `|b(u_Q, v_P, w)| ≤ C(w)‖u_Q‖‖v_P‖` for **arbitrary L² `u_Q`** (non-trig) and
`v_P, w ∈ P` is precisely the statement "the bilinear form `(u,v) ↦ −∫(u·∇)w·v` extends
boundedly from trig `u` to all of `L²`." That extension is TRUE mathematically (it is the
content of the smooth-test bound), but **proving it in Lean requires the weak `(u·∇)v`
operator / IBP-on-the-torus machinery that is the entire reason `torus3_NSForms_exist` is
an axiom.** A Hamel extension can *define* `b` to satisfy (A) and (G) (linear algebra is
unconditional), but it **cannot prove (B)** for the extended form, because (B) is an
analytic continuity statement about the genuine convection integral on non-trig inputs —
not a consequence of the finite `galerkinConvection_bound`, which only bounds the
`P × P`-diagonal.

**Why the finite bound does not transfer.** `galerkinConvection_bound` (the
Cauchy–Schwarz + Bessel `ℓ²∗ℓ²` convolution-diagonal estimate) bounds
`|galerkinConvection N u v w|` in terms of `‖u‖‖v‖` **with the constant depending on `N`
(the box size)**. For `w ∈ P` fixed at level `N_w`, but `u, v` arbitrary L², the relevant
`b(u,v,w)` after the antisymmetry chaining requires summing the convolution diagonal over
**all** Fourier modes of `u, v` (unbounded `N`), against the *fixed* finite support of
`∇w`. That is a genuinely different, `N`-uniform estimate
`|Σ_k Σ_l û(k)·(2πi l_a)·v̂(l)·ŵ(−(k+l))| ≤ ‖∇w‖_∞‖u‖_{L²}‖v‖_{L²}` where the `ŵ` factor's
finite support collapses the double sum to a single convolution against `u,v ∈ ℓ²`. This
IS provable in principle (it is Young/Cauchy–Schwarz with the fixed finite `∇w` kernel),
**but it is NOT `galerkinConvection_bound`** and **NOT a finite-`Vₙ` fact** — it is the
infinite-tsum smooth-test bound, which requires either (i) a convergent tsum definition of
`b` on all of `L²` (the rejected raw-`tsum` total form, which the prompt forbids because the
non-diagonal junk is non-summable), or (ii) the weak operator. So (B) is the wall.

### 1.3 Second, independent obstruction: `galerkinConvection_antisymm` is only Vₙ-restricted

Even setting (B) aside, the prompt's own constraint forbids using
`galerkinConvection_antisymm` outside its `Vₙ` hypotheses
(`velocityProjection_n n v = v`, `… w = w`). The genuine `β` on `P³` is antisymmetric only
*after* projecting both slots into a common `Vₙ`. For the Hamel extension to inherit (A) on
`P³`, you need antisymmetry of `β` on **all** trig triples, including mixed-level ones
(`u ∈ V₅`, `v ∈ V₃`, `w ∈ V₇`). This holds (take `N = max` of the levels; both project to
identity in `V_N`), but the *Lean proof* requires
`galerkinConvection N u v w = galerkinConvection M u v w` whenever the supports fit in both
boxes (a `coeff_zero_outside_box`-style stability lemma) **plus** the `Vₙ` antisymmetry at
the common level. That is buildable (it is finite combinatorics) and is **GREEN** on its
own — but it is real work and is a prerequisite the prompt assumes already done. It does
not rescue (B).

### 1.4 Net

- Linear-algebra fields (`b_add_*`, `b_smul_*`): **GREEN** via `Basis.constr` /
  `MultilinearMap` extension — unconditional.
- `b_antisymm` over arbitrary L²: **YELLOW→GREEN** *if* the extension is built as a single
  antisymmetrized trilinear map (see §2.4), provided the `P³` antisymmetry of `β` is
  proved first (§1.3). Achievable.
- `b_galerkin`: **GREEN** by construction (extension fixes `β` on `P³`).
- `b_bound` for the EXTENDED `b`: **RED**. Requires the infinite smooth-test estimate on
  non-trig inputs = the missing weak operator. The finite `galerkinConvection_bound` does
  **not** transfer. This single field is the wall.

One must-prove field is genuinely blocked by a mathlib-absent analytic input. Therefore:
**RED — the construction would force either a new axiom (the smooth-test bound as a
hypothesis) or a `sorry` on `b_bound`. That violates the absolute floor.**

---

## 2. What the construction WOULD be (documented for a future attempt)

Recorded so the next attempt does not re-derive scope. This is the design that gets you to
the `b_bound` wall and no further.

### 2.1 The space objects
- `P := ` the trig-polynomial divergence-free subspace of `L2Sigma`. Realisable as
  `⨆ n, (velocityProjection_n n).range ⊓ L2Sigma`, or as the span of the finite Fourier
  modes. `IsGalerkinTest w ↔ w ∈ P` (already true by the def at `SolutionInterfaces.lean:123`).
- A Hamel basis `𝓑` of `L2Sigma` containing a basis of `P` as a subset, via
  `Basis.extend` / `LinearIndependent.extend` on a basis of `P`. `Classical`-powered;
  allowed (kernel axiom).

### 2.2 `b` on `P³`
`b|_{P³} := fun u v w => galerkinConvection (commonLevel u v w) u v w`, where
`commonLevel` is the smallest `N` whose `fourierBox` contains all three supports. Needs a
**level-stability lemma** (PR-0): `galerkinConvection N u v w` is independent of `N` once
`N` bounds the supports (from `coeff_zero_outside_box`).

### 2.3 Trilinear extension
Use the iterated `Basis.constr` / `LinearMap` tower (or `Basis.constr` three times) to
extend the values on `𝓑 × 𝓑 × 𝓑` to a genuine `B : L2Sigma →ₗ[ℝ] L2Sigma →ₗ[ℝ] L2Sigma
→ₗ[ℝ] ℝ`, assigning the genuine `β` on basis triples inside `P` and `0` (or any controlled
value) when any basis vector is outside `P`. This is exactly the R3 `b_multilinear` witness
shape (`R3/ConvectionForm.lean:167`). `b u v w := B u v w`. Gives `b_add_*`, `b_smul_*` for
free (`map_add`/`map_smul`), like R3 cases `b_add_1..3`, `b_smul_1..3`.

### 2.4 `b_antisymm` over arbitrary L²
Build `B` as the antisymmetrization in slots 2,3 of a base trilinear map `B₀`:
`B u v w := (B₀ u v w - B₀ u w v)/2` (or define basis values antisymmetrically). Then
`b u v w = -b u w v` is algebraic and holds for ALL u,v,w. For this to also satisfy (G),
the basis values of `B₀` on `P³` must already be antisymmetric and equal to `β` — which
needs §1.3 (the all-trig-triple antisymmetry of `β`). Achievable but nontrivial.

### 2.5 `b_bound` — THE WALL
For `w ∈ P` fixed, `(u,v) ↦ b u v w` must satisfy `|b u v w| ≤ C(w)‖u‖‖v‖` for arbitrary
L² `u,v`. By §2.3 the value is genuine only when `u,v ∈ P`; off `P` it is whatever the
basis assignment dictates. There is **no choice of basis assignment** that is simultaneously
(i) antisymmetric, (ii) genuine on `P³`, and (iii) L²-bounded at fixed `w ∈ P` over
arbitrary `u,v`, **unless** the off-`P` values coincide with the genuine analytic
`−∫(u·∇)w·v` (forced by antisymmetry chaining, §1.2), which is unprovable without the weak
operator. **This field cannot be discharged.** Any Lean attempt terminates in a `sorry` or
a new `axiom` of exactly the smooth-test-bound shape. RED.

---

## 3. Mathlib API survey (with exact decl names + gaps)

| Need | Mathlib decl | Status |
|---|---|---|
| Hamel basis of a vector space | `Basis.ofVectorSpace ℝ L2Sigma` | PRESENT |
| Extend lin-indep set to basis | `LinearIndependent.extend`, `Basis.extend` | PRESENT |
| Linear extension from basis values | `Basis.constr : Basis ι R M → (ι → M') → (M →ₗ[R] M')` | PRESENT |
| Trilinear tower target type | `M →ₗ[ℝ] M →ₗ[ℝ] M →ₗ[ℝ] ℝ` (as in R3 `b_multilinear`) | PRESENT (pattern proven in `R3/ConvectionForm.lean`) |
| Multilinear map alternative | `MultilinearMap`, `MultilinearMap.mkPiAlgebra` | PRESENT but heavier; `LinearMap` tower preferred (matches R3) |
| `ℓ²` Cauchy–Schwarz / convolution-diagonal | used inside `galerkinConvection_bound` (finite); `inner_mul_le_norm_mul_norm`, `tsum_mul_le...` | PARTIAL — finite version is the planned PR-0 lemma; **the infinite smooth-test version is the GAP** |
| Trig-poly dense subspace as a Lean object | `velocityProjection_n_tendsto` (`VelocityGalerkin.lean`) gives density; `P` as `⨆ n range` | PRESENT (density), but a packaged `P`-subspace + Hamel-containment needs construction |
| Weak `(u·∇)v` operator / torus IBP | — | **ABSENT (the actual frontier)** |

The **only** genuinely-absent item is the weak convection operator / torus integration-by-
parts that makes `b_bound` provable for non-trig inputs. Everything else (Hamel, `constr`,
the trilinear tower, the finite `ℓ²` estimate) is present. The gap is not closeable by API.

---

## 4. The floor-safe fallback — GREEN, but does NOT achieve 4 → 3

Mirror the R3 `ConvectionGap` / `R3NSForms_of_gap` pattern (`R3/ConvectionForm.lean`).
This is the honest, mergeable, floor-respecting deliverable when the genuine construction
is RED. It **isolates** the frontier into a single named hypothesis but does **not** remove
the axiom unless you then re-axiomatize the (thinner) hypothesis.

### 4.1 New structure `TorusConvectionGap` (mirror of `ConvectionGap`)
Fields (named, mirroring `R3/ConvectionForm.lean:145`):
- `b : L2Sigma → L2Sigma → L2Sigma → ℝ` — total candidate form.
- `b_extends : ∀ u v w, IsGalerkinTest u → IsGalerkinTest v → IsGalerkinTest w → ` (or the
  common-`Vₙ` predicate) `→ b u v w = galerkinConvection (commonLevel …) u v w` — the
  operator-extension / pin to the genuine finite form (the frontier link; excludes `b=0`).
- `b_multilinear : ∃ B : L2Sigma →ₗ[ℝ] L2Sigma →ₗ[ℝ] L2Sigma →ₗ[ℝ] ℝ, ∀ u v w, b u v w = B u v w`
  — algebraic trilinear witness (gives `b_add_*`, `b_smul_*`).
- `b_antisymm_gap : ∀ u v w, b u v w = - b u w v` — the asserted residual (third-slot
  algebra over arbitrary L²; the IBP content Lean lacks).
- `b_cont_fixedTest : ∀ w, IsGalerkinTest w → Continuous (fun p : L2Sigma × L2Sigma => b p.1 p.2 w)`
  — the TRUE fixed-test bilinear continuity (drives `b_bound`).
- `galerkinTest_dense : ∀ u : L2Sigma, ∃ s : ℕ → L2Sigma, (∀ n, IsGalerkinTest (s n)) ∧ Tendsto s atTop (nhds u)`
  — density of trig polynomials (DISCHARGEABLE from `velocityProjection_n_tendsto`, so this
  field may be **proved away** rather than assumed; preferable, makes the gap thinner).

### 4.2 Conditional theorem `Torus3NSForms_of_gap` (mirror of `R3NSForms_of_gap`)
`theorem Torus3NSForms_of_gap (g : TorusConvectionGap) : Nonempty Torus3NSForms`.
Each `Torus3NSForms` field derived exactly as in `R3NSForms_of_gap`
(`R3/ConvectionForm.lean:229`):
- `b_add_*`, `b_smul_*` ← `b_multilinear` `map_add`/`map_smul`.
- `b_antisymm` ← `b_antisymm_gap`.
- `b_bound` ← finite `galerkinConvection_bound` (PR-0) + `b_extends` + `b_cont_fixedTest`
  + `galerkinTest_dense`, via the `le_of_tendsto_of_tendsto` limiting argument copied
  verbatim from `R3NSForms_of_gap` case `b_bound`.
- `b_galerkin` ← `b_extends` + the level-stability lemma.

This is GREEN (sorry-free, no new axiom) **as a conditional theorem**. But the capstone
still needs a `TorusConvectionGap` witness, and producing one runs straight back into the
§1.2 wall (you cannot prove `b_cont_fixedTest` + `b_extends` simultaneously for a concrete
`b` without the weak operator). So either:

- **(4a)** Add a new isolated axiom `torusConvectionGap_exists : Nonempty TorusConvectionGap`
  and re-route the capstone through `Torus3NSForms_of_gap`. Net axiom **count unchanged at
  4** (lose `torus3_NSForms_exist`, gain `torusConvectionGap_exists`), but the new axiom is
  **thinner** (isolates the single weak-operator frontier; the trilinear/bound/pin algebra
  is now THEOREM content). This is the R3 honesty posture. **Does NOT reach 3.**
- **(4b)** Keep `Torus3NSForms_of_gap` as a pure conditional theorem with **no** witness
  axiom; the capstone stays wired through `torus3_NSForms_exist`. Axiom count stays 4. The
  gap theorem is dead-code-useful documentation of the frontier. **Does NOT reach 3.**

**Neither fallback achieves the stated 4 → 3.** Reaching 3 requires *constructing* the
witness, which is RED.

---

## 5. Ordered task list

> Only execute PR-1+ if the owner accepts the GREEN-fallback (4a/4b) as the deliverable,
> having been told it does NOT reach 3 axioms. If the owner insists on 4 → 3, the honest
> response is: blocked on the missing torus weak-convection operator; no PR can deliver it
> at the floor.

### PR-0 (prerequisite, GREEN) — finite Galerkin lemmas + level stability
Owner: `lean-coder` (signatures) → `lean-prover` (bodies). File:
`LerayHopf/Torus/SolutionInterfaces.lean` (these are upstream finite facts) OR a new
`LerayHopf/GalerkinConvectionLemmas.lean` imported by it.
- `galerkinConvection_add_1/2/3`, `_smul_1/2/3` — multilinearity of the finite form.
- `coeff_zero_outside_box` — Fourier coeffs vanish outside `fourierBox n`.
- `galerkinConvection_level_stable` — `galerkinConvection N = galerkinConvection M` when
  both boxes bound the supports.
- `galerkinConvection_bound` — finite `ℓ²` Cauchy–Schwarz/Bessel bound.
- `galerkinConvection_antisymm` — Vₙ-restricted antisymmetry (keep its `Vₙ` hyps).
**If PR #27 lands upstream, PR-0 is a no-op.** All GREEN, all must-prove.

### PR-1 (GREEN fallback structure) — `TorusConvectionGap` + density discharge
New file `LerayHopf/TorusConvectionForm.lean`, importing `AxiomaticClosure` (downstream —
no cycle, mirrors how R3 `ConvectionForm.lean` imports `R3/AxiomaticClosure`).
- coder: `structure TorusConvectionGap` (fields per §4.1). **scaffold-only** (data + Prop
  fields, no proof obligation in the structure itself).
- prover: prove `galerkinTest_dense` as a standalone lemma from
  `velocityProjection_n_tendsto` (so it need not be a field). **must-prove.**

### PR-2 (GREEN fallback theorem) — `Torus3NSForms_of_gap`
Same file.
- coder: signature `theorem Torus3NSForms_of_gap (g : TorusConvectionGap) : Nonempty Torus3NSForms`.
- prover: bodies for all 10 fields, copying the `R3NSForms_of_gap` structure
  (`R3/ConvectionForm.lean:229`), substituting `galerkinConvection_bound` for
  `convFormSchwartz_bound`. **must-prove, sorry-free.**

### PR-3 (DECISION GATE — needs owner sign-off; does NOT reach 3)
Either:
- (4a) coder adds `axiom torusConvectionGap_exists : Nonempty TorusConvectionGap`
  (`-- ALLOW_AXIOM: isolates the single weak-convection-operator frontier; thinner than
  torus3_NSForms_exist; b algebra/bound/pin now theorem content via Torus3NSForms_of_gap`)
  in `TorusConvectionForm.lean`; re-route the capstone in a new `Torus3NSForms_provider`
  lemma so `torus3_NSForms_exist` is no longer referenced by
  `exists_lerayHopf_torus3`. Then UPDATE the pins:
  - `scripts/print_axioms.lean` comment block: replace `torus3_NSForms_exist` with
    `torusConvectionGap_exists` in the torus expected set.
  - `scripts/check-axioms-live.sh` lines 11–14 and 141–144: same substitution. **Count
    stays 7 total / 4 project.** (Per the "no new axiom during burn" floor, even this
    swap-for-thinner is axiom-neutral, not axiom-increasing — but it is NOT axiom-removing.
    Confirm with owner that a thinner-swap is in-scope; the burn floor forbids axiom
    *increase*, and this is net 0.)
- (4b) no axiom; capstone unchanged; pins unchanged.

**There is no PR that removes `torus3_NSForms_exist` and reaches 3 project axioms without a
`sorry` or a new axiom. State this plainly to the owner.**

---

## 6. Riskiest lemmas, ranked, with fallbacks

1. **`b_bound` for a CONCRETE total `b` (the witness) — RANK 1, RED.**
   Requires the infinite smooth-test estimate on non-trig inputs = the missing weak torus
   convection operator. **No fallback at the floor.** Forces axiom or sorry. This is the
   verdict-determining lemma.
2. **`b_cont_fixedTest` for a CONCRETE `b` — RANK 2, RED (same root).**
   The fixed-test bilinear continuity is provable for the *genuine* form but not for any
   Hamel-extension that also satisfies `b_extends`; it is the same wall as #1 in
   continuity clothing. Fallback: only as an assumed field of `TorusConvectionGap` (GREEN
   as a hypothesis, never as a constructed fact).
3. **`b_antisymm` over arbitrary L² jointly with `b_galerkin` — RANK 3, YELLOW.**
   Needs the all-trig-triple antisymmetry of `β` (§1.3) and the antisymmetrized-tower
   construction (§2.4). Buildable but fiddly. Fallback: assert as `b_antisymm_gap` field
   (GREEN as hypothesis), exactly as R3 does.

---

## 7. Definition of done

- **If RED is accepted (recommended):** no Lean change; this document is the deliverable.
  `exists_lerayHopf_torus3` stays at 4 project axioms. Report to owner that 4 → 3
  is blocked on the missing torus weak-convection operator (the same frontier R3 isolates
  but does not discharge).
- **If GREEN fallback (4a) is authorised:** PR-0, PR-1, PR-2 land sorry-free; PR-3 swaps to
  the thinner `torusConvectionGap_exists`; `check-axioms-live.sh` torus pin updated to the
  new name; total axiom count unchanged at 7 (4 project). `Torus3NSForms_of_gap` is
  must-prove sorry-free. **This does not satisfy the original 4 → 3 goal** and must be
  reported as such.

---

## 8. Constraints restated (compliance ledger)

- ABSOLUTE FLOOR honored: no path here adds a new axiom/sorry to reach the goal; the goal
  is declared unreachable at the floor rather than papered over. `Classical.choice` only.
- `Torus3NSForms` and `exists_lerayHopf_torus3` are NOT weakened anywhere.
- The rejected raw-`tsum` total form is NOT used (it is named in §1.2 as the non-summable
  trap that the smooth-test bound cannot rescue).
- `galerkinConvection_antisymm` is used ONLY with its `Vₙ` hypotheses (§1.3, §5 PR-0).
- Faithfulness preserved: in every GREEN artifact `b` is genuine on the Galerkin-test slot
  (`b_extends` + `b_galerkin`), where the weak form and the R3-mirror limit passage
  evaluate it; non-vacuity holds via the pin to `galerkinConvection`.
