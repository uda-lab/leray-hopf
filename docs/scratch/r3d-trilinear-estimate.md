# Task Contract — R3-d: Concrete Trilinear Convection Estimate (axiom-free)

**Milestone:** `r3d-trilinear-estimate`
**File deliverable:** `LerayHopf/R3/TrilinearEstimate.lean` (new)
**Branch:** `autorun/leray-hopf-torus3` (same working branch)
**Plan reference:** `HANDOFF.md` §5 P1; `LerayHopf/R3/AxiomaticClosure.lean` lines 167–281.

---

## 1. Goal

Prove, axiom-free and sorry-free, the genuine analytic properties of
`convIntegralSchwartz` that the `r3_NSForms_exist` axiom currently only *asserts*
in its justification prose.  This does **not** remove that axiom (defining `b` on
all of `L²_σ` requires a missing `(u·∇)v` operator), but it upgrades the axiom's
stated facts into proved lemmas about the concrete Schwartz integral.

The new file is **standalone**: it does NOT import `AxiomaticClosure.lean`, so
the axiom justification remains independent.  `AxiomaticClosure.lean` does not
need to import `TrilinearEstimate.lean` either; the connection is semantic, not
structural.

---

## 2. New file: `LerayHopf/R3/TrilinearEstimate.lean`

### 2.1 Imports

```
import LerayHopf.R3.DivergenceFree
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
```

`DivergenceFree` transitively pulls in `Domain`, `SchwartzSpace.Basic`, and
`MeasureTheory.Function.L2Space`.  The `Deriv` import brings in
`integral_mul_lineDerivOp_right_eq_neg_left` (the key IBP lemma) and
`SchwartzMap.integrable`.

### 2.2 Namespace / opens

```
namespace LerayHopf
open MeasureTheory LineDeriv SchwartzMap
open scoped LineDeriv
```

---

## 3. Declarations in dependency order

### Tier A — Multilinearity (6 lemmas)

These are cheap: the sum-of-integrals structure means each instance reduces to
`integral_add` / `integral_smul` plus `map_add` / `map_smul` of the CLMs
`lineDerivOpCLM` and `SchwartzMap.evalCLM`.

---

**A1. `convIntegralSchwartz_add_1`** — scaffold-only → must-prove

```lean
theorem convIntegralSchwartz_add_1
    (ψu ψu' ψv ψw : Fin 3 → SchwartzMap Domain3 ℝ) :
    convIntegralSchwartz (fun a => ψu a + ψu' a) ψv ψw =
      convIntegralSchwartz ψu ψv ψw + convIntegralSchwartz ψu' ψv ψw
```

**Role:** lean-prover (proof body only after lean-coder creates the file skeleton).
**Proof sketch:** Unfold `convIntegralSchwartz`; push `add` inside the sum via
`Finset.sum_add_distrib`; apply `integral_add` (both integrands are integrable by
`SchwartzMap.integrable` applied to the product, which is Schwartz); use pointwise
ring arithmetic `(ψu a x + ψu' a x) * _ * _ = ψu a x * _ * _ + ψu' a x * _ * _`.
**Dependencies:** `convIntegralSchwartz` definition; `MeasureTheory.integral_add`;
`SchwartzMap.integrable`.

---

**A2. `convIntegralSchwartz_add_2`** — must-prove

```lean
theorem convIntegralSchwartz_add_2
    (ψu ψv ψv' ψw : Fin 3 → SchwartzMap Domain3 ℝ) :
    convIntegralSchwartz ψu (fun i => ψv i + ψv' i) ψw =
      convIntegralSchwartz ψu ψv ψw + convIntegralSchwartz ψu ψv' ψw
```

**Proof sketch:** Same pattern; linearity of `lineDerivOpCLM` via `map_add` moves
the addition through the derivative, then `integral_add` and ring arithmetic split
the sum.
**Dependencies:** A1 (same pattern); `ContinuousLinearMap.map_add` for
`lineDerivOpCLM`.

---

**A3. `convIntegralSchwartz_add_3`** — must-prove

```lean
theorem convIntegralSchwartz_add_3
    (ψu ψv ψw ψw' : Fin 3 → SchwartzMap Domain3 ℝ) :
    convIntegralSchwartz ψu ψv (fun i => ψw i + ψw' i) =
      convIntegralSchwartz ψu ψv ψw + convIntegralSchwartz ψu ψv ψw'
```

**Proof sketch:** Same as A1 with the third slot.

---

**A4. `convIntegralSchwartz_smul_1`** — must-prove

```lean
theorem convIntegralSchwartz_smul_1
    (c : ℝ) (ψu ψv ψw : Fin 3 → SchwartzMap Domain3 ℝ) :
    convIntegralSchwartz (fun a => c • ψu a) ψv ψw =
      c * convIntegralSchwartz ψu ψv ψw
```

**Proof sketch:** Unfold; `(c • ψu a) x = c * ψu a x` (pointwise scalar action);
pull `c` out of the integral via `integral_mul_left`; pull out of the double sum via
`Finset.mul_sum`.
**Dependencies:** `MeasureTheory.integral_mul_left`.

---

**A5. `convIntegralSchwartz_smul_2`** — must-prove

```lean
theorem convIntegralSchwartz_smul_2
    (c : ℝ) (ψu ψv ψw : Fin 3 → SchwartzMap Domain3 ℝ) :
    convIntegralSchwartz ψu (fun i => c • ψv i) ψw =
      c * convIntegralSchwartz ψu ψv ψw
```

**Proof sketch:** `lineDerivOpCLM` is ℝ-linear so `map_smul` gives
`(∂_a (c • ψv i)) x = c * (∂_a ψv i) x`; then pull `c` out as in A4.
**Dependencies:** `ContinuousLinearMap.map_smul`.

---

**A6. `convIntegralSchwartz_smul_3`** — must-prove

```lean
theorem convIntegralSchwartz_smul_3
    (c : ℝ) (ψu ψv ψw : Fin 3 → SchwartzMap Domain3 ℝ) :
    convIntegralSchwartz ψu ψv (fun i => c • ψw i) ψw =
      c * convIntegralSchwartz ψu ψv ψw
```

**Proof sketch:** Same as A4 with the third slot.

*Note on A6 signature:* The last formal parameter `ψw` above is a naming conflict;
the correct signature is:
```lean
    (c : ℝ) (ψu ψv ψw : Fin 3 → SchwartzMap Domain3 ℝ) :
    convIntegralSchwartz ψu ψv (fun i => c • ψw i) =
      c * convIntegralSchwartz ψu ψv ψw
```

---

### Tier B — Integrability and direct Cauchy–Schwarz bound (2 declarations)

**B1. `convIntegralSchwartz_integrand_integrable`** — must-prove

```lean
theorem convIntegralSchwartz_integrand_integrable
    (ψu ψv ψw : Fin 3 → SchwartzMap Domain3 ℝ)
    (i a : Fin 3) :
    MeasureTheory.Integrable
      (fun x : Domain3 =>
        (ψu a x) *
        ((lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
            (EuclideanSpace.single a (1 : ℝ) : Domain3) (ψv i)) x) *
        (ψw i x))
      (volume : Measure Domain3)
```

**Proof sketch:** The integrand is a product of three pointwise values of Schwartz
functions. The function `x ↦ (ψu a x) * (∂_a ψv i)(x) * (ψw i x)` is the
pointwise product of `ψu a`, the Schwartz function `lineDerivOpCLM ... (ψv i)`, and
`ψw i`.  Products of Schwartz functions are Schwartz (closed under products), and
Schwartz functions are integrable (`SchwartzMap.integrable`).  In practice: form the
pointwise product `f := ψu a * lineDerivOpCLM ... (ψv i) * ψw i` as a Schwartz
function via `SchwartzMap.mul` (if available) or bound by the seminorm decay
`‖f x‖ ≤ C (1 + ‖x‖)^{-n}` to conclude integrability from
`SchwartzMap.integrable_pow_mul`.
**Dependencies:** `SchwartzMap.integrable`; `SchwartzMap.mul` or pointwise bound.

*Gating note:* If `SchwartzMap.mul` (the ring structure on Schwartz space) is not
present in the mathlib version in use, fall back to a direct seminorm bound argument
using `SchwartzMap.integrable_pow_mul` with `k = 0` after bounding
`‖(ψu a x) * (∂_a ψv i)(x) * (ψw i x)‖` by a Schwartz-class envelope.

---

**B2. `convIntegralSchwartz_bound_H1`** — must-prove

```lean
/-- Direct Cauchy–Schwarz bound on `convIntegralSchwartz` with an H¹-seminorm
    of ψv (derivative sits on ψv).

    `|convIntegralSchwartz ψu ψv ψw| ≤ 9 * ‖ψu‖_{L²}^{vec} * ‖∇ψv‖_{L²}^{vec} * ‖ψw‖_{L²}^{vec}`

    where the norms are `∑_{a} ‖(ψu a).toLp 2 volume‖` etc. (component-wise L² norms).
    The constant 9 = 3 × 3 comes from the double Fin 3 sum. -/
theorem convIntegralSchwartz_bound_H1
    (ψu ψv ψw : Fin 3 → SchwartzMap Domain3 ℝ) :
    |convIntegralSchwartz ψu ψv ψw| ≤
      9 * (∑ a : Fin 3, ‖(ψu a).toLp 2 (volume : Measure Domain3)‖) *
          (∑ a : Fin 3, ∑ i : Fin 3,
            ‖((lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
                (EuclideanSpace.single a (1 : ℝ) : Domain3) (ψv i)).toLp
              2 (volume : Measure Domain3))‖) *
          (∑ i : Fin 3, ‖(ψw i).toLp 2 (volume : Measure Domain3)‖)
```

**Proof sketch:** Use `abs_sum_le_sum_abs` + `Finset.sum_le_sum` to reduce to
component-level bounds.  For each `(i, a)` term, apply Cauchy–Schwarz
(`MeasureTheory.inner_le_nnorm_mul_nnorm` / `integral_mul_le_sqrt_mul_sqrt`) to
`∫ (ψu a x) * (∂_a ψv i)(x) * (ψw i x)` viewed as `⟪ψu a, (∂_a ψv i) * ψw i⟫_{L²}`
or as `∫ f * g` with `f = ψu a · ψw i ∈ L²` and `g = ∂_a ψv i ∈ L²`.  This
produces a bound in terms of L² norms of ψu a, ∂_a ψv i, and ψw i.  The derivative
norm `‖∂_a ψv i‖_{L²}` is the `(a,i)`-component of the H¹-seminorm of ψv.

**Codex review point:** The exact constant and the exact RHS shape (whether to use
`‖ψu a‖_{L²} * ‖∂_a ψv i‖_{L²} * ‖ψw i‖_{L∞}` or a pure L² triple) should be
reviewed before the proof is attempted.  The form stated here (L² for all three
factors after IBP is NOT applied — derivative stays on ψv) is correct as a direct
bound.
**Dependencies:** B1; `MeasureTheory.integral_mul_le_eLpNorm_mul_eLpNorm` or
Hölder's inequality for p=2.

---

### Tier C — Integration by parts identity and `b_bound`-shape estimate

**Availability check (CRITICAL before attempting):** Mathlib (as of the pinned
`lean4:v4.31.0-rc2` / mathlib master at lake-manifest.json revision) contains
`SchwartzMap.integral_mul_lineDerivOp_right_eq_neg_left` and
`SchwartzMap.integral_bilinear_lineDerivOp_right_eq_neg_left` in
`Mathlib.Analysis.Distribution.SchwartzSpace.Deriv` (confirmed present).  The
Tier C lemmas below are therefore NOT gated on an absent API — IBP for Schwartz
directional derivatives is available.  The remaining difficulty is algebraic
bookkeeping over the `Fin 3 × Fin 3` double sum and the weak-div-free hypothesis.

---

**C1. `convIntegralSchwartz_ibp`** — must-prove

```lean
/-- Integration by parts: moves the directional derivative ∂_a off ψv onto ψu,
    with a sign change.

    For each component (i, a), the IBP identity gives:
      ∫ (ψu a x) * (∂_a ψv i)(x) * (ψw i x) dx
      = -∫ (∂_a ψu a x) * (ψv i x) * (ψw i x) dx
        - ∫ (ψu a x) * (ψv i x) * (∂_a ψw i x) dx  -- only if ∂_a(ψw i) is involved

    In the simpler form used here: fix ψw, treat h(x) = ψw i x as a scalar factor,
    and apply IBP to move ∂_a off ψv onto ψu:
      ∫ (ψu a x) * (∂_a ψv i x) * (ψw i x)
      = -∫ (∂_a ψu a x) * ψv i x * ψw i x  -- Leibniz in the ψu-ψv pair
        (using ψw i as the "outer" factor).

    More precisely: `integral_mul_lineDerivOp_right_eq_neg_left` (in direction
    `EuclideanSpace.single a 1`) for scalar-valued Schwartz functions gives
      ∫ f * (∂_a g) = -∫ (∂_a f) * g
    with f = ψu a * ψw i ∈ 𝓢 and g = ψv i ∈ 𝓢.  Expanding f by Leibniz:
    ∂_a(ψu a * ψw i) = (∂_a ψu a) * ψw i + ψu a * (∂_a ψw i).
    This yields the full triple IBP. -/
theorem convIntegralSchwartz_ibp
    (ψu ψv ψw : Fin 3 → SchwartzMap Domain3 ℝ) :
    convIntegralSchwartz ψu ψv ψw =
      -(∑ i : Fin 3, ∑ a : Fin 3,
          ∫ x : Domain3,
            ((lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
                (EuclideanSpace.single a (1 : ℝ) : Domain3) (ψu a)) x) *
            (ψv i x) * (ψw i x) ∂(volume : Measure Domain3))
      - (∑ i : Fin 3, ∑ a : Fin 3,
          ∫ x : Domain3,
            (ψu a x) * (ψv i x) *
            ((lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
                (EuclideanSpace.single a (1 : ℝ) : Domain3) (ψw i)) x)
            ∂(volume : Measure Domain3))
```

**Role:** lean-prover (proof body).
**Proof sketch:**  For each `(i, a)` term in `convIntegralSchwartz`, apply
`SchwartzMap.integral_mul_lineDerivOp_right_eq_neg_left` with `f := ψu a * ψw i`
(pointwise product, which is Schwartz), `g := ψv i`, and direction
`EuclideanSpace.single a 1`.  Then expand `∂_a(ψu a * ψw i)` by the Leibniz rule
for `lineDerivOpCLM` (which is a derivation for Schwartz functions).  Collect terms.
**Dependencies:** B1 (integrability); `integral_mul_lineDerivOp_right_eq_neg_left`;
Leibniz rule for `lineDerivOpCLM` (should be `SchwartzMap.lineDerivOpCLM_mul` or
deduced from `fderivCLM_mul`).

*Gating note:* If `lineDerivOpCLM` on a product of Schwartz functions is not directly
available as a Schwartz-to-Schwartz map (i.e., the product `ψu a * ψw i` does not
canonically live in `SchwartzMap Domain3 ℝ`), the proof should instead apply IBP
directly to the two-factor form `∫ (ψu a) * ∂_a(ψv i) * (ψw i)` by treating
`ψu a * ψw i` as a pointwise product and checking it satisfies the integrability
hypotheses of `integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable`.
If that path also fails, mark C1 with `-- TODO: Leibniz rule for lineDerivOpCLM on
SchwartzMap product needed; check Mathlib.Analysis.Distribution.SchwartzSpace.Deriv`.

---

**C2. `convIntegralSchwartz_antisymm_of_divFree`** — must-prove
(Codex review point before proving)

```lean
/-- Antisymmetry of `convIntegralSchwartz` in the last two slots,
    under a divergence-free condition on ψu.

    If ψu represents a weakly divergence-free field in the sense that
      ∑ a : Fin 3, ∫ x, (∂_a ψu a x) * φ x = 0  for every φ ∈ 𝓢(Domain3, ℝ),
    i.e., ∑_a ∂_a ψu_a = 0 in the distributional sense (strong form: pointwise),
    then:
      convIntegralSchwartz ψu ψv ψw = -convIntegralSchwartz ψu ψw ψv. -/
theorem convIntegralSchwartz_antisymm_of_divFree
    (ψu ψv ψw : Fin 3 → SchwartzMap Domain3 ℝ)
    (hdiv : ∀ φ : SchwartzMap Domain3 ℝ,
      ∑ a : Fin 3,
        ∫ x : Domain3, (ψu a x) *
          ((lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
              (EuclideanSpace.single a (1 : ℝ) : Domain3) φ) x)
        ∂(volume : Measure Domain3) = 0) :
    convIntegralSchwartz ψu ψv ψw = -convIntegralSchwartz ψu ψw ψv
```

**Design note on `hdiv`:** The hypothesis `hdiv` is exactly the condition that ψu
represents a weakly divergence-free field at the Schwartz level (i.e., the weak
divergence against any Schwartz test is zero).  This is the Schwartz-level unfolding
of `u ∈ L2Sigma_R3` when u has a Schwartz representative ψu.  The exact form chosen
here avoids importing `L2Sigma_R3` into the proof and works purely with Schwartz
integrals.

**Proof sketch:** From `convIntegralSchwartz_ibp` (C1):
```
convIntegralSchwartz ψu ψv ψw
  = -(∑_i ∑_a ∫ (∂_a ψu a) * ψv i * ψw i)
    -(∑_i ∑_a ∫ ψu a * ψv i * (∂_a ψw i))
```
Similarly compute `convIntegralSchwartz ψu ψw ψv` by IBP:
```
convIntegralSchwartz ψu ψw ψv
  = -(∑_i ∑_a ∫ (∂_a ψu a) * ψw i * ψv i)
    -(∑_i ∑_a ∫ ψu a * ψw i * (∂_a ψv i))
```
The last term of the second expression equals `convIntegralSchwartz ψu ψv ψw` (by
reindexing i).  Adding `convIntegralSchwartz ψu ψv ψw + convIntegralSchwartz ψu ψw ψv`:
the `∂_a ψu a` terms vanish by `hdiv` (with φ = ψv i * ψw i, using the Leibniz
product structure — requires `ψv i * ψw i ∈ 𝓢`), giving
`2 * convIntegralSchwartz ψu ψv ψw = -2 * convIntegralSchwartz ψu ψw ψv` mod the
div-free cancellation.  Division by 2 concludes.
**Dependencies:** C1.

---

**C3. `convIntegralSchwartz_bound_sup`** — must-prove
(Codex review point before proving)

```lean
/-- Smooth-test L²-bound on `convIntegralSchwartz` with the sup-norm of ∇ψw.

    After integration by parts (moving ∂_a off ψv onto ψw via C1 and the IBP identity
    c = -∫ ψu a * ψv i * ∂_a ψw i  — the second summand in C1):

    |convIntegralSchwartz ψu ψv ψw|
      ≤ (∑_i ∑_a ‖∂_a ψw i‖_{L∞}) * ‖ψu‖_{L²,comp} * ‖ψv‖_{L²,comp}

    where ‖∂_a ψw i‖_{L∞} = SchwartzMap.seminorm ℝ 0 1 (∂_a ψw i) (finite for Schwartz w)
    and ‖ψu‖_{L²,comp} = ∑_a ‖(ψu a).toLp 2 volume‖.

    Precise statement:
-/
theorem convIntegralSchwartz_bound_sup
    (ψu ψv ψw : Fin 3 → SchwartzMap Domain3 ℝ) :
    |convIntegralSchwartz ψu ψv ψw| ≤
      (∑ i : Fin 3, ∑ a : Fin 3,
        SchwartzMap.seminorm ℝ 0 1
          (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
            (EuclideanSpace.single a (1 : ℝ) : Domain3) (ψw i))) *
      (∑ a : Fin 3, ‖(ψu a).toLp 2 (volume : Measure Domain3)‖) *
      (∑ i : Fin 3, ‖(ψv i).toLp 2 (volume : Measure Domain3)‖)
```

**Derivation of shape:** The antisymmetry identity C2 gives
`convIntegralSchwartz ψu ψv ψw = -convIntegralSchwartz ψu ψw ψv` (under div-free ψu,
but we state the bound without the div-free hypothesis by using C1 directly).
From the IBP decomposition (C1), the term involving `∂_a ψu a` vanishes when ψu is
div-free; the surviving term is `-(∑_i ∑_a ∫ ψu a * ψv i * (∂_a ψw i))`.  Bounding:
`|∫ ψu a * ψv i * ∂_a ψw i| ≤ ‖∂_a ψw i‖_{L∞} * ∫ |ψu a| * |ψv i|`
`≤ ‖∂_a ψw i‖_{L∞} * ‖ψu a‖_{L²} * ‖ψv i‖_{L²}` by Cauchy–Schwarz.
`‖∂_a ψw i‖_{L∞} ≤ SchwartzMap.seminorm ℝ 0 1 (∂_a ψw i)` (Schwartz seminorm at order
(0,1) bounds the sup-norm of the function itself).

**NOTE:** C3 is stated WITHOUT the div-free hypothesis on ψu (it is a direct estimate
from C1 regardless; the div-free term from `∂_a ψu a` is bounded similarly and can be
absorbed into a larger constant, or the bound can be split into two terms). If lean-coder
and lean-prover determine that the cleanest route requires the div-free hypothesis, the
signature should add `hdiv` from C2 and then the bound follows from the single remaining
term.  This decision is deferred to the Codex review gate.

**Dependencies:** C1; B1; `MeasureTheory.norm_integral_le_integral_norm`;
Cauchy–Schwarz for L² (`MeasureTheory.inner_le_nnorm_mul_nnorm`);
`SchwartzMap.seminorm` sup-norm bound.

---

## 4. Module DAG position

```
Domain.lean
    └── DivergenceFree.lean   (imports SchwartzSpace.Deriv)
            └── TrilinearEstimate.lean   [NEW — this PR]
                    (standalone; NOT imported by AxiomaticClosure.lean)
```

`AxiomaticClosure.lean` imports `DivergenceFree.lean` (transitively via `Regularity.lean`)
and will continue to do so unchanged.  `TrilinearEstimate.lean` is a sibling of
`AxiomaticClosure.lean` in the DAG, not a dependency of it.

The `LerayHopf` library target in `lakefile.toml` will pick up `TrilinearEstimate.lean`
automatically since it covers the whole `LerayHopf` namespace.

---

## 5. Assumptions to package as axioms

None.  This milestone is explicitly axiom-free.  If any lemma cannot be proved without
a mathlib gap, it must be left as a `-- TODO: <exact blocker>` with the theorem
statement intact (no sorry, no axiom, per the hard rules).

---

## 6. Codex review points

The following should receive `/codex:adversarial-review --effort xhigh` **before**
proof bodies are attempted:

1. **All new theorem statements** — run together as a block once `lean-coder` has
   written the full file skeleton (signatures, imports, namespace, no proof bodies).
   Focus: correctness of the multilinearity statement shapes; whether the `DFunLike`
   coercion `(ψu a) x` vs `(ψu a : Domain3 → ℝ) x` is explicit enough; whether
   `convIntegralSchwartz` definitional unfolding proceeds without `simp` explosions.

2. **C2 (`convIntegralSchwartz_antisymm_of_divFree`) statement** — specifically:
   - Is the `hdiv` hypothesis the right Schwartz-level formulation of weak div-free?
     (Does it unambiguously exclude div-free up to a set of measure zero?)
   - The proof sketch for C2 uses `ψv i * ψw i ∈ 𝓢`; confirm that Schwartz functions
     are closed under pointwise products in the mathlib version in use.

3. **C3 (`convIntegralSchwartz_bound_sup`) statement** — specifically:
   - Is the sup-norm bound via `SchwartzMap.seminorm ℝ 0 1` the right mathlib lemma,
     or is there a dedicated `SchwartzMap.norm_le_seminorm`?
   - Confirm the constant shape (no hidden factor from `volume.toReal` etc.).

---

## 7. Lean-coder vs lean-prover split

**lean-coder** (file skeleton, imports, signatures):
- Create `LerayHopf/R3/TrilinearEstimate.lean` with:
  - All import statements (section 2.1 above)
  - Namespace / opens
  - Module-level doc comment referencing `AxiomaticClosure.lean` lines 167–281
  - All 9 theorem signatures (A1–A6, B1, B2, C1, C2, C3) with `by sorry -- ALLOW_SORRY: scaffold pending lean-prover` as placeholders
  - Inline `-- Proof sketch:` comments for each declaration (lean-prover guidance)
  - No proof bodies

**lean-prover (fable)** (proof bodies, in dependency order):
1. B1 (`convIntegralSchwartz_integrand_integrable`) — no dep on other new lemmas; proves integrability first
2. A1–A6 (multilinearity) — parallel, no inter-dependency; tackle after B1
3. B2 (`convIntegralSchwartz_bound_H1`) — after A1–A6 and B1
4. C1 (`convIntegralSchwartz_ibp`) — after B1
5. C2 (`convIntegralSchwartz_antisymm_of_divFree`) — after C1
6. C3 (`convIntegralSchwartz_bound_sup`) — after C1, C2

---

## 8. Definition of done

The milestone is complete when all of the following hold:

- [ ] `LerayHopf/R3/TrilinearEstimate.lean` compiles without error.
- [ ] All 9 theorems (A1–A6, B1, B2, C1, C2, C3) are **sorry-free**.
- [ ] Zero new `axiom` declarations in the file.
- [ ] `bash scripts/agent-preflight.sh` returns green (full `lake build` + all 3 guardrail scripts).
- [ ] `#print axioms` on each theorem in the file shows only `propext`, `Classical.choice`, `Quot.sound` (the standard Lean kernel axioms) — no `sorryAx`, no project axioms.
- [ ] Codex adversarial review of the statement block (gate 1 in §6) returns **approve**.
- [ ] C2 and C3 Codex review gates (§6 items 2–3) return **approve**.

Partial done: if C1–C3 cannot be closed (e.g., `SchwartzMap.mul` / product-Schwartz
structure is absent), the milestone is declared partially done with:
- A1–A6 + B1 + B2 sorry-free (counts as Tier A/B closed)
- C1–C3 left with intact statements and precise `-- TODO:` blockers

---

## 9. Recommended first task for lean-coder

Create `LerayHopf/R3/TrilinearEstimate.lean` with the full file skeleton:
imports, namespace, module doc, and all 9 theorem signatures each carrying
`by sorry -- ALLOW_SORRY: scaffold pending lean-prover` and a one-line proof hint
comment.  Do not write any proof bodies.  Report the file path and all declaration
names so the orchestrator can run the Codex statement review (gate 1) before lean-prover
begins.
