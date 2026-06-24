# Issue #3 — `CurlSchwartzDense` discharge plan

**Planner:** lean-planner
**Issue:** #3 — remove `axiom curlSchwartzDense_holds`
**Source files read:** `LerayHopf/R3/SchwartzDivFreeBasis.lean` (axiom definition),
`LerayHopf/R3/CurlDensity.lean` (discharge route, current sorry map)
**Read-only output — no Lean files edited.**

---

## Executive summary

The target axiom is

```lean
axiom curlSchwartzDense_holds : CurlSchwartzDense
-- CurlSchwartzDense :=
--   (L2Sigma_R3 : Submodule ℝ L2VF_R3) ≤
--     (Submodule.span ℝ (Set.range curlSchwartzL2)).topologicalClosure
```

**Verdict: full axiom removal is NOT one-PR-reachable today.**
The file `LerayHopf/R3/CurlDensity.lean` already contains the discharge route with
almost all sub-steps proved. Two `sorry`s remain, both tracing to a single named gap:

> **(P2)** — Schwartz-space real-part extraction under Hermitian symmetry: the inverse
> Fourier transform of a Hermitian-symmetric complex Schwartz function is (a.e. equal to)
> the complexification of a real Schwartz function. Equivalently, the map
> `φ ↦ testSymbol φ` (where `testSymbol φ ξ = conj((2πi)·𝓕(schwartzC φ)(ξ))`) has
> range dense in the anti-Hermitian complex Schwartz functions.

(P2) is absent from Mathlib. It is constructible in weeks-class work from existing
Mathlib primitives (`SchwartzMap.postcompCLM`, `Complex.conjCLE`, `Complex.reCLM`,
`FourierTransform.fourierCLE`), but is a genuine new sub-development.

**Maximal one-PR progress:** prove the (P2) lemma to fill the remaining two sorrys,
completing `curlSchwartzDense_provedRoute : CurlSchwartzDense` in `CurlDensity.lean`.
This retires `curlSchwartzDense_holds`. This is the recommended scope.

---

## Current state of `CurlDensity.lean`

The file introduces **no axioms, no opaque, no unsafe**. It carries exactly **2 marked
sorrys**, both tracing to (P2):

| Line | Theorem | Blocker |
|------|---------|---------|
| 739 | `mem_sigma_iff_fourier_transverse` (forward dir) | (P2) surjectivity of `testSymbol` map |
| 829 | `l2sigma_le_closure_span_curl` | depends on line-739 forward direction |

`curlSchwartzDense_provedRoute` at line 849 is `l2sigma_le_closure_span_curl`, so it
carries the same sorry transitively.

### What is already proved (sorry-free, axiom-free) in `CurlDensity.lean`

All of these are complete:

- `crossWithIξ` — cross-product Fourier symbol of curl (definition)
- `potentialComponentC` — complex Lp embedding of real Schwartz potential
- `schwartzC` / `lineDerivOp_schwartzC` / `fourier_schwartzC_lineDeriv_apply` — Schwartz
  complexification and its derivative/Fourier behaviour
- `fourier_schwartzC_curl_apply` — Schwartz-level curl Fourier multiplier (pointwise)
- **`fourier_curlSchwartz_eq_cross`** (Step 1, proved) — L²-level a.e. identity
  `𝓕(curl ψ)_j =ᵐ crossWithIξ ξ (𝓕(ψ_k))_j`
- `fourier_schwartzC_hermitian` — `𝓕(schwartzC φ)(-ξ) = conj(𝓕(schwartzC φ)(ξ))`
- `IsTransverseAt` / `transverseDefect` / `testSymbol` — spectral bookkeeping defs
- `divTestFunctional_eq_fourier_integral` — weak-div functional = Fourier-side integral
- `mem_sigma_iff_fourier_integral_zero` — membership in L2Sigma ↔ test integrals vanish
- `testSymbol_antiHermitian` — anti-Hermitian symmetry of test symbols
- **(P1) `fourier_ofReal_reflect_eq_conj`** (proved, 600+ lines work) — Lp-level
  Hermitian reflection identity for Fourier of real functions; formerly a sorry
- `mem_sigma_of_transverse_ae` — REVERSE direction proved (a.e. transverse ⇒ in L2Sigma)
- `mem_sigma_iff_fourier_transverse` REVERSE direction — proved
- **`cross_iξ_spans_transverse`** (Step 3, proved) — fiberwise: every transverse `b` is a
  curl symbol at `ξ ≠ 0`

The reverse direction of `mem_sigma_iff_fourier_transverse` is fully proved; the forward
direction (L2Sigma membership ⇒ a.e. transverse) requires (P2).

---

## Irreducible core: gap (P2)

**(P2) statement** (informal): For every anti-Hermitian Schwartz symbol `h : 𝓢(ℝ³, ℂ)`
satisfying `h(-ξ) = -conj(h(ξ))`, there exists a real Schwartz function
`φ : 𝓢(ℝ³, ℝ)` such that `testSymbol φ = h` (or with range dense in such `h`).

Equivalently: the inverse Fourier transform `𝓕⁻` maps Hermitian Schwartz functions to
real-valued Schwartz functions (up to the `schwartzC` embedding).

**Why absent from Mathlib:** Mathlib's `SchwartzMap/Fourier.lean` has `fourierCLE`
(Fourier as CLEquiv on Schwartz), `postcompCLM`, and `FourierInvPair`. It does NOT have:
- a lemma that `𝓕(schwartzC φ)` is Hermitian for real `φ` (only the pointwise version
  is used; the converse, that Hermitian Schwartz preimages under `𝓕` are real, is absent)
- any lemma asserting that Hermitian Schwartz symbols are in the range of `φ ↦ testSymbol φ`

**Constructibility:** (P2) can be built from available Mathlib in three steps:

1. **Conjugation CLM on Schwartz:** `f.postcompCLM (Complex.conjCLE : ℂ →L[ℝ] ℂ)` gives
   the CLM `conj_schwartz : 𝓢(V, ℂ) →L[ℝ] 𝓢(V, ℂ)`, `f ↦ conj ∘ f`. Available now.

2. **Real-part extraction CLM:** `f.postcompCLM (RCLike.reCLM : ℂ →L[ℝ] ℝ)` gives
   `re_schwartz : 𝓢(V, ℂ) →L[ℝ] 𝓢(V, ℝ)`, `f ↦ Re ∘ f`. Available now.

3. **Hermitian preimage construction:** Given anti-Hermitian `h ∈ 𝓢(ℝ³, ℂ)`, define
   `g = (1/(2πi)) · h` (Hermitian). Then set `Ψ = Re(𝓕⁻ g)` as a real Schwartz
   function, and verify `testSymbol (schwartzC⁻¹ Ψ) = h` using:
   - `fourierCLE.symm.continuousLinearEquivOfLinear` to apply `𝓕⁻`
   - `postcompCLM reCLM` to extract the real part
   - The already-proved `fourier_schwartzC_hermitian` to check that `𝓕(schwartzC Ψ)`
     recovers `g`

The missing piece is assembling these steps and checking the algebraic identity. It
requires a real-valuedness argument: if `g` is Hermitian (i.e., `g(-ξ) = conj(g(ξ))`),
then `𝓕⁻ g` is real-valued, which follows from the Hermitian-reflecting property of `𝓕⁻`
together with the fact that real functions have Hermitian Fourier transforms.

**Effort:** weeks-class (2–4 weeks for a careful formalization, not months). The
algebraic structure is clear; the Lean work is threading CLMs and a.e. equalities through
the Schwartz/Lp bridge.

---

## Mathlib survey results

Real Mathlib decls confirmed present (grepped `.lake/packages/mathlib/`):

| Decl | File | Role |
|------|------|------|
| `SchwartzMap.postcompCLM` | `SchwartzSpace/Basic.lean:1040` | CLM on Schwartz from post-composition |
| `SchwartzMap.postcompCLM_apply` | `SchwartzSpace/Basic.lean:1060` | evaluation lemma |
| `FourierTransform.fourierCLE` | `SchwartzSpace/Fourier.lean:~100` | Fourier as CLEquiv on Schwartz |
| `FourierTransform.fourierCLE_symm_apply` | alias `fourierTransformCLE_symm_apply` | inverse Fourier on Schwartz |
| `FourierInvPair` instance | `SchwartzSpace/Fourier.lean:135` | `𝓕 ∘ 𝓕⁻ = id` and `𝓕⁻ ∘ 𝓕 = id` on Schwartz |
| `SchwartzMap.fourierInv_coe` | `SchwartzSpace/Fourier.lean:118` | coercion for inverse Fourier |
| `Complex.conjCLE` | Mathlib | conjugation as CLEquiv on ℂ |
| `RCLike.reCLM` | Mathlib | real-part CLM `ℂ →L[ℝ] ℝ` |
| `SchwartzMap.denseRange_toLpCLM` | `SchwartzSpace/Basic.lean:~1379` | Schwartz dense in Lp |
| `MeasureTheory.Lp.fourierTransformₗᵢ` | `Fourier/LpSpace.lean` | L² Fourier isometry |
| `Lp.inner_fourier_eq` | `Fourier/LpSpace.lean` | Parseval on L² |
| `Submodule.orthogonal_orthogonal_eq_closure` | Mathlib | orthogonal complement criterion |
| `ae_eq_zero_of_integral_contDiff_smul_eq_zero` | Mathlib | du-Bois-Reymond (used in step 4 route) |

Confirmed ABSENT from Mathlib:
- Any lemma asserting `𝓕⁻(Hermitian Schwartz) = complexification of real Schwartz`
- Any Helmholtz/Hodge decomposition
- Any `curl`/`div` operator at the L² level
- Any curl-density theorem (`closure(span curl) = L²_σ`)

---

## Reachable sub-lemma list (all in `CurlDensity.lean`)

All in dependency order. Items 1–10 are **already proved** in the current file.
Item 11 is the (P2) core that blocks the two remaining sorrys.
Items 12–13 follow immediately once 11 is in place.

| # | Name | Status | Notes |
|---|------|--------|-------|
| 1 | `crossWithIξ` | proved | def; cross-product Fourier symbol |
| 2 | `potentialComponentC` | proved | def; complex Lp component |
| 3 | `schwartzC`, `lineDerivOp_schwartzC` | proved | Schwartz complexification |
| 4 | `fourier_schwartzC_lineDeriv_apply` | proved | derivative → Fourier multiplier |
| 5 | `fourier_schwartzC_curl_apply` | proved | Schwartz-level curl Fourier identity |
| 6 | `fourier_curlSchwartz_eq_cross` | proved (Step 1) | L² a.e. curl multiplier |
| 7 | `fourier_schwartzC_hermitian` | proved | `𝓕(schwartzC φ)` is Hermitian |
| 8 | `divTestFunctional_eq_fourier_integral` | proved | div functional = Fourier integral |
| 9 | `fourier_ofReal_reflect_eq_conj` (P1) | proved | Lp-level Hermitian reflection |
| 10 | `cross_iξ_spans_transverse` | proved (Step 3) | fiberwise spanning |
| 11 | **`schwartz_hermitian_preimage_real`** (P2) | **must-prove** | `𝓕⁻(Hermitian Schwartz) = schwartzC(real Schwartz)` or equivalent surjectivity of `testSymbol` — the sole sorry blocker |
| 12 | `mem_sigma_iff_fourier_transverse` (forward) | **must-prove** | depends on (P2); forward direction of Step 2 |
| 13 | `l2sigma_le_closure_span_curl` (Step 4) | **must-prove** | density transfer; depends on Step 2 forward |
| 14 | `curlSchwartzDense_provedRoute` | **must-prove** | = `l2sigma_le_closure_span_curl`; the deliverable |

Items 12–14 will discharge trivially (short tactic blocks) once (P2) (item 11) is proved.

---

## The single hardest step

**(P2) `schwartz_hermitian_preimage_real`.**

Lean proof sketch:
```lean
-- Given h : 𝓢(ℝ³, ℂ), anti-Hermitian: h(-ξ) = -conj(h(ξ))
-- Let g = (2πi)⁻¹ • h  (Hermitian)
-- Let Ψ : 𝓢(ℝ³, ℝ) := (𝓕⁻ g).postcompCLM reCLM  (real part of inverse FT)
-- Claim: testSymbol (schwartzC⁻¹ Ψ) = h
-- Proof:
--   testSymbol φ ξ = conj((2πi) · 𝓕(schwartzC φ)(ξ))
--   = conj((2πi) · 𝓕(schwartzC (Re(𝓕⁻ g)))(ξ))
--   Reducing: need 𝓕(schwartzC (Re f)) = (f + conj ∘ f ∘ neg) / 2 for Schwartz f
--   Using FourierInvPair + fourier_schwartzC_hermitian for g Hermitian ⇒ 𝓕⁻ g real-valued
--   ⇒ schwartzC(Re(𝓕⁻ g)) = 𝓕⁻ g ⇒ 𝓕(schwartzC(Re(𝓕⁻ g))) = g ⇒ testSymbol = conj(2πi·g) = h
```

The algebraic chain is complete; Lean formalization requires:
- threading `postcompCLM reCLM` and `postcompCLM conjCLE` through Fourier inversion,
- establishing that `𝓕⁻ g` is real-valued when `g` is Hermitian (an a.e. argument via
  Lp-level Hermitian reflection, essentially the same machinery as the proved `(P1)`),
- assembling into a surjectivity statement usable by the du-Bois-Reymond argument.

No Mathlib PR is required — all primitives are present. A lean-prover session of O(days)
to O(2 weeks) is a realistic estimate.

---

## Recommended one-PR slice

**PR scope:** Add (P2) to `LerayHopf/R3/CurlDensity.lean` and use it to discharge the
two remaining sorrys (`mem_sigma_iff_fourier_transverse` forward direction,
`l2sigma_le_closure_span_curl`), then remove the `axiom curlSchwartzDense_holds` from
`SchwartzDivFreeBasis.lean` by routing through `curlSchwartzDense_provedRoute`.

**Files to touch:**
1. `LerayHopf/R3/CurlDensity.lean` — add (P2) lemma + discharge 2 sorrys (items 11–14)
2. `LerayHopf/R3/SchwartzDivFreeBasis.lean` — remove `axiom curlSchwartzDense_holds`;
   replace with `theorem curlSchwartzDense_holds := curlSchwartzDense_provedRoute`
   (or remove and re-route `nonempty_schwartzGalerkinBasis` through
   `curlSchwartzDense_provedRoute` directly)

**Definition of done:** `#print axioms nonempty_schwartzGalerkinBasis` does not contain
`curlSchwartzDense_holds`; `lake build` passes; no unmarked sorry; `check-no-axiom`
passes on both files.

---

## Over-strength check on any residual axiom

If (P2) cannot be completed in one PR, the thinnest possible residual replaces the
current axiom with a strictly weaker one. **Do not strengthen** the residual beyond:

```lean
axiom schwartz_hermitian_preimage_real :
    ∀ (h : SchwartzMap Domain3 ℂ),
      h.postcompCLM (Complex.conjCLE : ℂ →L[ℝ] ℂ) = h.postcompCLM ...(reflect)...
      → ∃ φ : SchwartzMap Domain3 ℝ, testSymbol φ = h
```

This is strictly weaker than `CurlSchwartzDense` (which is itself strictly weaker than
the original `r3GalerkinScheme_exists` 6-field structure). The no-overclaim rule applies:
name it `schwartzHermitianPreimageReal_holds` or similar.

---

## Dependency edges

```
CurlDensity.lean depends on: SchwartzDivFreeBasis.lean, FourierL2.lean
Items 1–10: already proved, no new dependencies
(P2) item 11: depends on SchwartzMap.postcompCLM, Complex.conjCLE, RCLike.reCLM,
              FourierTransform.fourierCLE (symm), FourierInvPair, fourier_schwartzC_hermitian (item 7)
Items 12–13: depend on item 11 + items 7–10 (all proved)
Item 14: = item 13
SchwartzDivFreeBasis.lean axiom removal: depends on item 14 in CurlDensity.lean
```

---

## Codex review points

Before proof attempt on (P2), request `/codex:adversarial-review` on:
1. The statement of `schwartz_hermitian_preimage_real` (P2) — check that the "real-part
   extraction" formulation is equivalent to the needed surjectivity, and that it is not
   stronger than what the du-Bois-Reymond step needs.
2. The intended rewiring in `SchwartzDivFreeBasis.lean` — check that removing the axiom
   and routing through `curlSchwartzDense_provedRoute` does not introduce a circularity
   (the axiom file imports `CurlDensity.lean` which imports `SchwartzDivFreeBasis.lean`).

**Circularity warning (critical):** `CurlDensity.lean` already imports
`SchwartzDivFreeBasis.lean`. If the discharge route is `SchwartzDivFreeBasis` ← proven
result in `CurlDensity`, this is acyclic (CurlDensity is downstream). The correct
rewiring is: `nonempty_schwartzGalerkinBasis` in `SchwartzDivFreeBasis.lean` is changed
from `schwartzGalerkinBasis_of_curlDense curlSchwartzDense_holds` to a `sorry` until a
THIRD file (or the same-file theorem body) routes through `CurlDensity`. Alternatively,
move the axiom `curlSchwartzDense_holds` body to reference `CurlDensity.curlSchwartzDense_provedRoute` in a new import position — but this would create a cycle. The clean route is:

- Keep `CurlDensity.lean` as a leaf (no downstream import).
- In `SchwartzDivFreeBasis.lean`, the axiom stays until a separate capstone file
  (`CurlDensityCapstone.lean` or similar) imports BOTH and re-exports the discharged
  `nonempty_schwartzGalerkinBasis`. Alternatively, move `nonempty_schwartzGalerkinBasis`
  and `r3GalerkinScheme_exists` to a downstream file that can import `CurlDensity`.

This import-DAG restructuring must be planned before Lean edits begin.

---

## Definition of done (must-prove targets)

| Target | File | Condition |
|--------|------|-----------|
| `schwartz_hermitian_preimage_real` (P2) | `CurlDensity.lean` | sorry-free |
| `mem_sigma_iff_fourier_transverse` (forward) | `CurlDensity.lean` | sorry-free (uses P2) |
| `l2sigma_le_closure_span_curl` | `CurlDensity.lean` | sorry-free |
| `curlSchwartzDense_provedRoute` | `CurlDensity.lean` | sorry-free |
| removal of `axiom curlSchwartzDense_holds` | `SchwartzDivFreeBasis.lean` | axiom gone; capstone still typechecks |

`lake build` must pass with `check-no-axiom` clean on `SchwartzDivFreeBasis.lean`.

---

## Recommended first task for `lean-coder`

**Hand to `lean-coder`:** Add a stub for (P2) in `CurlDensity.lean` with an
`-- ALLOW_SORRY` marker and the precise intended type signature, so `lean-prover` has a
clean target. The statement to stub is:

```lean
/-- (P2) Schwartz Hermitian preimage extraction.
    If `h : 𝓢(ℝ³, ℂ)` is anti-Hermitian (`h(-ξ) = -conj(h(ξ))`), there exists
    `φ : 𝓢(ℝ³, ℝ)` such that `testSymbol φ = h`.
    Constructible from `postcompCLM (Complex.conjCLE)` + `postcompCLM reCLM` + `fourierCLE.symm`. -/
private theorem schwartz_antiHermitian_has_testSymbol_preimage
    (h : SchwartzMap Domain3 ℂ)
    (hH : ∀ ξ : Domain3, h (-ξ) = -(starRingEnd ℂ) (h ξ)) :
    ∃ φ : SchwartzMap Domain3 ℝ, testSymbol φ = h :=
  sorry -- ALLOW_SORRY: (P2) Schwartz Hermitian real-extraction; not in mathlib;
        -- constructible from postcompCLM conjCLE + reCLM + fourierCLE.symm + FourierInvPair
```

Send this stub + the full `CurlDensity.lean` context to `lean-prover` with the proof
sketch from the "hardest step" section above.
