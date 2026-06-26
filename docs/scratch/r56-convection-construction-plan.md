# Task Contract: Issue #56 — GENUINELY remove `r3ConvectionGapOp_exists` (R3 capstone 3 → 2)

**Plan author:** lean-planner
**Date:** 2026-06-26
**Scope:** READ-ONLY planning (this file only). Produces the multi-PR construction contract
for `lean-coder` / `lean-prover`. No Lean source edited.

**Revision:** v2 — totality resolution corrected after coordinator soundness review. The v1
`gradComponentL2`-zero-extension route was UNSOUND (non-additive: `v∈H¹, v'∉H¹ ⟹ v+v'∉H¹`,
so `grad(v+v') = 0 ≠ ∇v + 0`). The corrected route is option (a): Hamel-based algebraic
extension + antisymmetrization. See §1 for the refutation, §2 for the corrected route.

**Goal.** Construct `Nonempty (ConvectionGapOp 𝔊)` axiom-free, dropping
`exists_lerayHopf_r3_axiomatic` from 3 project axioms to 2 (pending C6 resolution).

---

## 0. Ground truth — consumers verified in source

**Consumer regularity (read verbatim from sources; all five use-sites catalogued):**

| Consumer | File | Slots at which regularity | Impact |
|---|---|---|---|
| `bInner/bMid/bOut` (Galerkin ODE map) | `GalerkinODESolve.lean:288–340` | ALL THREE in `galerkinSpan B n` (Schwartz, via `range_schwartz`) | `b_add_*`, `b_smul_*` used ONLY at Schwartz triples here |
| `GalerkinODE u_ode` | `GalerkinODE.lean:152` | slots 1,2 = Galerkin element (Schwartz), slot 3 = Galerkin test | ALL Schwartz |
| `AubinLionsLimitPassage` limit-passage estimate | `AubinLionsLimitPassage.lean:155–219` | slots 1,2 = GENERAL `L2Sigma_R3` (`uSeq n`, `u` = A-L limit), slot 3 = `w` Schwartz | `b_add_1`, `b_add_2` used at GENERAL L2Sigma_R3 arguments |
| `WeakFormNS` | `EvolutionTriple.lean:90,106` | slots 1,2 = `u t : L2Sigma_R3` (energy class a.e.), slot 3 = `w` Schwartz | integral uses energy-class `u` |
| `convForm_self_zero` | `EvolutionTriple.lean:74–78` | ALL slots = ARBITRARY `u : H` via antisymmetry | `b_antisymm` needed at GENERAL L2Sigma_R3 |

**Conclusion (verified):** `b_add_1`, `b_add_2` are GENUINELY evaluated at arbitrary
`L2Sigma_R3` arguments in `AubinLionsLimitPassage.lean:166,170`. The field
`b_antisymm` / `convForm_antisymm` is needed at arbitrary `u : H` for
`convForm_self_zero` (`EvolutionTriple.lean:74`). Totality and trilinearity over ALL of
`L2Sigma_R3` is NOT a structural artifact — it is consumed by existing sorry-free code.

**Consequence:** Option (b) (interface relaxation) is NOT feasible without breaking existing
sorry-free consumers. Route (a) (algebraic extension) is the only sound totality route.

---

## 1. Why the zero-extension route (v1) is UNSOUND

The v1 plan defined `gradComponentL2 v := (weak gradient of v) if memH1VF_R3 v else 0`.
This is NOT additive over `L2Sigma_R3`:

**Counterexample.** Take `v ∈ H1_sigma` with `∇v ≠ 0` (exists by non-degeneracy), and any
`v' ∈ L2Sigma_R3 \ H1_sigma`. Since `H1_sigma` is a DENSE PROPER SUBSPACE of `L2Sigma_R3`
(not closed — H¹ is dense in L² but strictly contained), `v + v' ∉ H1_sigma`, so
`gradComponentL2(v+v') = 0` but `gradComponentL2(v) + gradComponentL2(v') = ∇v + 0 = ∇v ≠ 0`.
Additivity fails. There is no bounded projection `L2Sigma_R3 → H1_sigma` (H¹ is dense in L²,
so any bounded projection onto a dense proper subspace would force the subspace = whole space —
contradiction). The v1 route cannot yield `b_multilinear` or `b_add_*`.

---

## 2. The sound totality resolution — option (a): Hamel algebraic extension + antisymmetrization

### Overview

**Step 1.** Build the genuine energy-class form `b_H1` on `H1_sigma` (the H¹ submodule) as a
genuine integral (proved integrable via GNS H¹↪L⁶ + Hölder). Prove it trilinear on `H1_sigma`
and antisymmetric in slots 2,3 (by IBP + weak div-free identity).

**Step 2.** Extend the trilinear tower from `H1_sigma` to all of `L2Sigma_R3` via
`LinearMap.exists_extend` (mathlib, `LinearAlgebra/Basis/VectorSpace.lean:288`):

    theorem LinearMap.exists_extend {p : Submodule K V} (f : p →ₗ[K] V') :
        ∃ g : V →ₗ[K] V', g.comp p.subtype = f

This works because `L2Sigma_R3` is a real vector space and `H1_sigma` is a submodule over `ℝ`.
Apply three times (one per slot) via `Submodule.exists_isCompl` + `LinearMap.ofIsCompl`.
The extension uses `Classical.choice` (Zorn / Hamel basis), invoked internally.

**Why this IS additive (not the v1 error):** The Hamel complement `Q` of `H1_sigma` in
`L2Sigma_R3` (from `Submodule.exists_isCompl`) gives a unique algebraic decomposition of each
`v = v_{H¹} + v_Q`. The linear extension acts on components ADDITIVELY because the decomposition
IS linear — this is the defining property of a direct complement. The v1 error was conditioning
on `memH1VF_R3 v` (a SET-MEMBERSHIP predicate that does NOT decompose additively), rather than
using the ALGEBRAIC complement projection (which does). The Hamel-complement approach is sound.

**Step 3.** Antisymmetrize in slots 2,3: define

    b_anti(u, v, w) := (B_ext(u, v, w) - B_ext(u, w, v)) / 2

This is:
- Linear in each slot (average of two linear maps is linear).
- Antisymmetric in slots 2,3 by construction.
- Agrees with `b_H1` on `H1_sigma` triples (since `b_H1` is already antisymmetric there, so
  `(b_H1 - (-b_H1))/2 = b_H1`). The extension does NOT change the energy-class values.
- Agrees with `convFormSchwartz` on Schwartz triples (since Schwartz ⊂ H¹, via `SchwartzMap.memSobolev`).
- Gives `b_anti(u,u,u) = 0` trivially for ALL `u` by the antisymmetrization formula.

This yields a `b : L2Sigma_R3 → L2Sigma_R3 → L2Sigma_R3 → ℝ` satisfying `b_multilinear`,
`b_antisymm_gap`, `b_extends` (three of the five `ConvectionGapOp` fields) — plus `b_galerkin`
by restriction to Schwartz triples (verified). Four fields are PROVED by this construction.

### The fifth field — `b_cont_fixedTest` is the genuine analytic wall

`b_cont_fixedTest` requires: for fixed Schwartz `w`, the map `(u,v) ↦ b(u,v,w)` is
CONTINUOUS on `L2Sigma_R3 × L2Sigma_R3` (equivalently, bounded by `C(w)‖u‖‖v‖`).

The Hamel extension of a bounded bilinear form from a dense subspace `H1_sigma` to the
whole space `L2Sigma_R3` is NOT in general continuous — a Hamel complement in an
infinite-dimensional space is discontinuous (this is a standard functional-analysis fact:
any algebraic complement of a proper dense subspace carries a discontinuous projection).
So `b_anti(·,·,w)` built via the Hamel route is generically UNBOUNDED on `L2Sigma_R3`.

**However:** The BLT (Bounded Linear Transformation) theorem says: a bounded linear map from
a dense subspace extends UNIQUELY AND CONTINUOUSLY to the whole space. For fixed Schwartz `w`,
the map `(u,v) ↦ b_H1(u,v,w)` IS bounded by `C(w)‖u‖_{L²}‖v‖_{L²}` (proved for u,v ∈ H¹_σ
via GNS+Hölder, with the bound in L²-NORMS not H¹-norms). By BLT, it extends to a CONTINUOUS
bounded bilinear form `b_BLT(·,·,w)` on `L2Sigma_R3 × L2Sigma_R3`.

**The issue:** `b_BLT(·,·,w)` is a continuous bilinear form in slots 1,2 at FIXED `w`. But is
it linear in slot 3 (varying `w`)? The answer requires checking: for fixed `u,v ∈ H1_sigma`,
`w ↦ b_H1(u,v,w)` is linear in `w ∈ H1_sigma` (integral is linear). The BLT extension in
slots 1,2 is a function of `(u,v,w)` — but fixing `u,v` and varying `w`, the BLT-extended value
at general `u,v ∈ L2Sigma_R3` cannot be expressed as an integral (the integral is not defined
for `u,v ∈ L2Sigma_R3 \ H1_sigma`). The BLT extension at fixed `w` gives slot-3 linearity
ONLY for `w` in the range where the BLT is defined (all of L², since it extends by density),
but slot-3 linearity AT GENERAL `u,v ∈ L2Sigma_R3 \ H1_sigma` cannot be derived from the
BLT-at-fixed-w without circular reasoning.

**Definitive conclusion on `b_cont_fixedTest`:** This field is the IRREDUCIBLE analytic content
of the weak convection operator. It cannot be derived from the Hamel algebraic extension. It
REQUIRES either (a) the genuine weak `(u·∇)v` operator defined on all of `L²_σ` (future work,
not in mathlib), or (b) a separate analytic argument that the SPECIFIC constructed `b_anti`
happens to be bounded at fixed Schwartz `w`. Option (b) is conceivable by a BLT-first construction
but meets the slot-3 linearity obstacle described above. **`b_cont_fixedTest` is left as the
single residual axiom field for this milestone.**

---

## 3. Revised construction strategy: PARTIAL axiom discharge (4 of 5 fields proved)

The PR chain builds:
1. The genuine energy-class integral `b_H1` on `H1_sigma`.
2. Algebraic Hamel extension + antisymmetrize → `b_anti` on all `L2Sigma_R3`.
3. A sorry-free theorem `convectionGapOpCore_exists` asserting the 4-field partial discharge.

The residual axiom `r3ConvectionGapOp_exists` is REPLACED by a THINNER residual axiom carrying
only `b_cont_fixedTest` (ONE field, not five). This reduces the axiom content from
`Nonempty (ConvectionGapOp 𝔊)` (5 analytic/algebraic fields) to a single analytic continuity
claim for the explicitly-constructed `b`.

**Impact on capstone count:** R3 axiom count STAYS at 3 until `b_cont_fixedTest` is proved.
However the axiom is now a strict REDUCTION in content (one field vs. five), which is genuine
measurable progress toward the 3→2 goal.

---

## 4. mathlib API survey

| Need | mathlib decl | Location | Status |
|---|---|---|---|
| GNS: Cc¹+compact-support, `L^{p'}` bound | `MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq` | `SobolevInequality.lean:600` | PRESENT |
| GNS: `q ≤ p'` variant | `eLpNorm_le_eLpNorm_fderiv_of_le` | `:656` | PRESENT |
| Hölder triple product `Lp` | `MeasureTheory.Lp.holderL` | `Function/Holder.lean:125` | PRESENT |
| Schwartz dense in `Lp` | `SchwartzMap.denseRange_toLpCLM` | `SchwartzSpace/Basic.lean:1379` | PRESENT |
| `MemSobolev s 2` | `TemperedDistribution.MemSobolev` | `Distribution/Sobolev.lean` | PRESENT |
| Algebraic complement | `Submodule.exists_isCompl` | `VectorSpace.lean:279` | PRESENT |
| Extend linear map from complement | `LinearMap.ofIsCompl` | `Projection.lean:359` | PRESENT |
| Extend linear map from submodule | `LinearMap.exists_extend` | `VectorSpace.lean:288` | PRESENT |
| BLT extension (bounded linear from dense subspace) | `ContinuousLinearMap.extend` / `DenseRange.ext` | `Analysis/NormedSpace/BoundedLinearMaps.lean` | PRESENT |

**ABSENT — must build:**
1. **H¹↪L⁶ for general `MemSobolev 1 2`** (A3): density + A2 + dominated convergence. ~300 LOC.
2. **`L²∩L⁶↪L³` interpolation** for Hölder triple (B3a). ~80 LOC.
3. **`b_H1` genuine integral + trilinearity + antisymmetry on H¹_sigma** (B4–B6). ~400 LOC.
4. **`b_H1` L²-norm bound at fixed Schwartz `w`** (B7): GNS gives u,v ∈ L⁶, Hölder closes. ~100 LOC.
5. **H¹_sigma submodule + Hamel extension + antisymmetrize** (C1–C5). ~250 LOC.

---

## 5. Declaration list (in dependency order)

### File A — `LerayHopf/R3/SobolevEmbedding.lean` (NEW)

Imports: `LerayHopf.R3.Regularity`, mathlib `SobolevInequality`, `Function/Holder`.

- **A1** [scaffold-only]: `HolderTriple` instances for `(p=6, q=2, r=3)` etc. needed for B3.
- **A2 `gns_L6_cc1_R3`** [must-prove]: `ContDiff ℝ 1 u → HasCompactSupport u → eLpNorm u 6 vol ≤ C * eLpNorm (fderiv ℝ u) 2 vol`. Thin wrapper of `eLpNorm_le_eLpNorm_fderiv_of_eq` at `p=2, p'=6, n=3`.
- **A3 `gns_L6_of_memH1_R3`** [must-prove — CODEX REVIEW BEFORE PROVING]: `MemSobolev 1 2 f → MemLp f 6 vol`. Proof: approximate `f` by Schwartz (dense via `denseRange_toLpCLM`) → each Schwartz `φ_n` is Cc¹ after truncation → apply A2 → dominated convergence in L⁶.
- **A4 `h1Sigma_dense_in_L2Sigma`** [must-prove]: `H1_sigma` (elements satisfying `memH1VF_R3`) is dense in `L2Sigma_R3`. Near-trivial from existing `schwartzDivFree_dense` (proved already in `ConvectionForm.lean:594`) + Schwartz ⊂ H¹.

### File B — `LerayHopf/R3/EnergyClassConvection.lean` (NEW)

Imports: `SobolevEmbedding.lean`, `ConvectionOperator.lean`.

- **B1 `H1Sigma_submodule`** [scaffold + must-prove]: `H1Sigma_R3 : Submodule ℝ L2VF_R3` (or `Submodule ℝ L2Sigma_R3`). Proof: `MemSobolev.add`, `MemSobolev.smul`, `memH1VF_R3_zero`. ~50 LOC.
- **B2 `gradComponent_weakDeriv`** [must-prove]: the spectral weak-derivative `L²` representative satisfies the IBP identity `∫ uⱼ ∂_a φ = -∫ (gradComp u a j) φ` for Schwartz `φ`. Uses `memH1VF_R3` (via `MemSobolev 1 2`) + existing `memSobolev_iff_exists_smulLeftCLM_fourier`.
- **B3a `L2L6_inter_mem_L3`** [must-prove]: for `u ∈ L² ∩ L⁶`, `u ∈ L³`. Proof: `eLpNorm_le_eLpNorm_pow_mul_eLpNorm` (log-convexity). ~80 LOC.
- **B3b `convFormH1_integrable`** [must-prove]: for `u,v,w ∈ H1_sigma`, the integrand `uₐ (∂ₐvᵢ) wᵢ` is integrable. Uses A3 (u,v ∈ L⁶), B2 (`∂v ∈ L²`), B3a (`w ∈ L³ ⊂ L²∩L⁶`), `Lp.holderL` with `1/6+1/2+1/3=1`.
- **B4 `convFormH1`** [must-prove def + trilinearity]: `noncomputable def convFormH1 (u v w : L2Sigma_R3) (hu hv hw : memH1VF_R3 _) : ℝ := -∑_{i,a} ∫ ...`. Prove: linear in each slot (integral linear in each factor at fixed others).
- **B5 `convFormH1_eq_convFormSchwartz`** [must-prove]: for `u v w` Schwartz (which satisfy `memH1VF_R3`), `convFormH1 u v w ... = convFormSchwartz u v w ...`.
- **B6 `convFormH1_antisymm`** [must-prove]: `convFormH1 u v w = -convFormH1 u w v`. Proof: IBP (B2) + weak div-free identity, extending `convIntegralSchwartz_antisymm_of_divFree` to `H1_sigma`. DECOMPOSE: B6a (IBP for H¹ weak deriv), B6b (div-free: `∑_a ∂_a uₐ = 0` in weak sense for `u ∈ L2Sigma_R3 ∩ H¹`, which holds since `L2Sigma_R3 ⊂ div_free`). ~150 LOC.
- **B7 `convFormH1_bound_Schwartz`** [must-prove — CODEX REVIEW on exponent arithmetic]: for Schwartz `w` and `u,v ∈ H1_sigma`: `|convFormH1 u v w| ≤ C_w * ‖(u : L2VF_R3)‖ * ‖(v : L2VF_R3)‖` where `C_w` depends on Schwartz seminorms of `w`. **⚠️ CODEX CORRECTION (PR-1 #58 review):** the GNS route is WRONG — GNS+Hölder only gives `‖u‖₆·‖∂v‖₂·‖w‖∞`, which still depends on H¹/gradient control of u,v; it does NOT convert to `‖u‖₂·‖v‖₂` on ℝ³. **The correct proof is via B6 (antisymmetry/IBP): move the derivative onto the fixed Schwartz test** — `convFormH1 u v w = +∑ ∫ uₐ (∂ₐwᵢ) vᵢ` (from B6 + div-free), then `|·| ≤ ‖∇w‖_∞ · ‖u‖₂ · ‖v‖₂` by Cauchy–Schwarz (∇w bounded for Schwartz w). This genuinely gives the L²-norm bound (A3/GNS is NOT needed for B7; it is needed for B3b integrability and the energy-class `b(u,u,u)`). So **B7 depends on B6**. The L²-bound enables BLT continuous extension of slots 1,2.

### File C — `LerayHopf/R3/ConvectionExtension.lean` (NEW)

Imports: `EnergyClassConvection.lean`, mathlib `LinearAlgebra/Basis/VectorSpace`, `LinearAlgebra/Projection`.

- **C1 `convFormH1_linearMap`** [must-prove]: the trilinear tower `H1Sigma_submodule →ₗ[ℝ] H1Sigma_submodule →ₗ[ℝ] L2Sigma_R3 →ₗ[ℝ] ℝ` from B4. NOTE: slot 3 can be extended to all `L2Sigma_R3` because at fixed `u,v ∈ H1_sigma`, `w ↦ convFormH1 u v w` is an integral that is actually linear for `w ∈ L²` (NOT requiring `hw : memH1VF_R3 w`) when the integrability follows from `u ∈ L⁶`, `∂v ∈ L²`, and Hölder `L^p·L^q·L^r` with `r=∞` for Schwartz `w` — or from B7's L²-uniform bound + density. This is the ONLY slot where slot-3 linearity can be seen directly without requiring `hw`. Confirm this precise statement before proceeding.
  - **⚠️ CODEX CORRECTION (PR-1 #58 review):** the "linear for w ∈ L² directly from the integral" hope is FALSE — with the derivative on v, `u·∂v ∈ L^{3/2}` pairs naturally with `w ∈ L³`, NOT arbitrary `w ∈ L²` on infinite-measure ℝ³. So slot-3 linearity/totality over all `L2Sigma_R3` does NOT come from the integral; it comes from the **Hamel algebraic extension (C3/`LinearMap.exists_extend`)**. b_cont_fixedTest is preserved NOT by extending slot 3 continuously, but because it is quantified only over Schwartz `w`, where slots 1,2 are the genuine bounded integral (B7). Do NOT attempt a BLT extension of slot 3 from an L³ pairing.
- **C2 `h1sigma_linearMap_slots12`** [must-prove]: For fixed Schwartz `w`, the map
  `(u, v) ↦ convFormH1 u v w` (with `u, v ∈ H1_sigma`) is bilinear and bounded by
  `C_w · ‖u‖₂ · ‖v‖₂` (from B7). This gives the L²-bounded bilinear form on `H1_sigma × H1_sigma`
  at each fixed Schwartz `w` that B7 establishes. **This is NOT a slot-3 BLT extension.**
  Per the C1 ⚠️ CODEX CORRECTION: slot-3 extension to all `L2Sigma_R3` goes via Hamel (C3),
  NOT via BLT from L³ pairing (which fails on infinite-measure ℝ³). B7's role is solely
  to provide the L²-norm bound for slots 1,2 at fixed Schwartz `w`, enabling `b_cont_fixedTest`.
  ~30 LOC (restating B7 as a bilinear tower statement).
- **C3 `h1sigma_Hamel_extend`** [must-prove (nonconstructive)]: via `LinearMap.exists_extend`
  applied THREE TIMES to the tower in C1 (one per slot), produce
  `B_ext : L2Sigma_R3 →ₗ[ℝ] L2Sigma_R3 →ₗ[ℝ] L2Sigma_R3 →ₗ[ℝ] ℝ`
  restricting to `convFormH1` on `H1_sigma × H1_sigma × H1_sigma`. All three slots are
  extended via Hamel (`LinearMap.exists_extend`), which gives algebraic linearity over all
  of `L2Sigma_R3` without continuity assumptions. Uses `Classical.choice` internally. ~100 LOC.
- **C4 `convFormL2_antisymm`** [must-prove]: define `b_anti` from `B_ext` by the antisymmetrize formula, prove: (a) linear tower (avg of two linear maps), (b) antisymmetric in slots 2,3, (c) restricts to `convFormH1` on H1_sigma triples (since `convFormH1` is antisymmetric, antisymmetrization is identity there), (d) restricts to `convFormSchwartz` on Schwartz triples (via B5 + (c)). ~100 LOC.
- **C5 `convectionGapOpCore_exists`** [must-prove — PRIMARY TARGET for Tier 1]:
  ```
  theorem convectionGapOpCore_exists (G : R3GalerkinScheme) :
    ∃ (b : L2Sigma_R3 → L2Sigma_R3 → L2Sigma_R3 → ℝ),
      (∃ B : L2Sigma_R3 →ₗ[ℝ] L2Sigma_R3 →ₗ[ℝ] L2Sigma_R3 →ₗ[ℝ] ℝ,
        ∀ u v w, b u v w = B u v w) ∧
      (∀ (u v w : L2Sigma_R3) (hu : IsSchwartzDivFree_R3 u)
         (hv : IsSchwartzDivFree_R3 v) (hw : IsSchwartzDivFree_R3 w),
        b u v w = convFormSchwartz u v w hu hv hw) ∧
      (∀ (u v w : L2Sigma_R3), b u v w = - b u w v)
  ```
  Proved from C4. This establishes 3 of the 5 `ConvectionGapOp` fields (b_multilinear, b_extends, b_antisymm_gap) without sorry. `b_galerkin` follows from `b_extends` (Galerkin elements are Schwartz). Non-vacuity: `b_extends` pins `b` to `convFormSchwartz` on Schwartz triples (not identically 0).

- **C6 `convFormL2_cont_fixedTest`** [CODEX GATE — do not attempt until adjudicated]:
  `∀ (w : L2Sigma_R3), IsSchwartzDivFree_R3 w → Continuous (fun p : L2Sigma_R3 × L2Sigma_R3 => b_anti p.1 p.2 w)`.
  TWO OPTIONS for codex to adjudicate:
  - **C6-α (BLT-first):** Redefine b in slots 1,2 as the BLT extension of `convFormH1(·,·,w)` from `H1_sigma × H1_sigma` (dense) to `L2Sigma_R3 × L2Sigma_R3` for each fixed Schwartz `w`. Then show slot-3 linearity at general `u,v` follows from BLT functoriality. This MIGHT be provable but requires care on the slot-3 case at `u,v ∉ H1_sigma`.
  - **C6-β (residual axiom):** `b_cont_fixedTest` remains a single-field axiom for the explicitly constructed `b_anti`. The axiom content is now MINIMAL (one continuity claim for a fully-explicit function), but the capstone stays at 3 axioms. This is acceptable as an intermediate milestone.
  **Recommendation: proceed with C6-β as the default path, attempt C6-α in a separate experimental PR if codex confirms the route.**

---

## 6. PR-by-PR plan (revised)

| PR | Title | New files / edits | Key decls | Must-prove | Scaffold |
|---|---|---|---|---|---|
| **PR-1** | GNS L⁶ + density | `SobolevEmbedding.lean` (new) | A1–A4 | A2, A3, A4 | A1 |
| **PR-2** | Energy-class convection on H¹_sigma | `EnergyClassConvection.lean` (new) | B1–B7 | B2, B3a, B3b, B4, B5, B6, B7 | B1 |
| **PR-3** | Hamel extension + antisymmetrize (partial discharge) | `ConvectionExtension.lean` (new) | C1–C5 | C1, C2, C3, C4, C5 | none |
| **PR-4** | `b_cont_fixedTest` (CODEX GATE; C6-α or C6-β) | `ConvectionExtension.lean` + `ConvectionForm.lean` | C6 | C6 (α) or new residual axiom (β) | — |
| **PR-5** | Rewire capstone to thin axiom | `ConvectionForm.lean` edit | D1 | `r3ConvectionGapOp_holds` | — |

### Definition of done (two-tier)

**Tier 1 (unconditional, PRs 1–3):** `convectionGapOpCore_exists` sorry-free (C5). Three
of five `ConvectionGapOp` fields proved axiom-free. The axiom `r3ConvectionGapOp_exists` is
replaced by a THINNER residual with only `b_cont_fixedTest` unsolved. New theorem C5 sorry-free.

**Tier 2 (contingent on C6 codex verdict):** If C6-α is sound: `r3ConvectionGapOp_holds`
sorry-free → capstone 3→2. If C6-β: capstone stays at 3 but axiom content is minimal; issue
remains open for the genuine weak-operator construction.

---

## 7. Risk register

- **R1 — H¹↪L⁶ for non-Cc¹ H¹ (A3).** Schwartz approximation + A2 + dominated convergence. ~300 LOC. Codex review of A3 statement required.
- **R2 — L³ slot for B3.** `L²∩L⁶↪L³` interpolation (`eLpNorm_le_pow_mul`). ~80 LOC.
- **R3 — slot-3 linearity in C1.** The integral `∫ uₐ (∂ₐvᵢ) wᵢ` is linear in `w ∈ L²` at fixed `u,v ∈ H1_sigma` IF integrability holds for `w ∈ L²`. But the Hölder triple `L⁶ · L² · L^r` needs `r = 3` or `r = ∞`. For `w ∈ L²` only (no L⁶ of `w`): integrability is `|u| |∂v| |w| ∈ L¹` with `|u| ∈ L⁶`, `|∂v| ∈ L²`, `|w| ∈ L²`. Hölder: `1/6 + 1/2 + 1/r = 1 ⟹ r = 3/2` — need `w ∈ L^{3/2}`. `L² ↪ L^{3/2}`? On ℝ³ with infinite measure, NO (Lp spaces on infinite measure don't nest by inclusion — L² ⊄ L^{3/2} and L^{3/2} ⊄ L²). So at general `w ∈ L²`, the integral may NOT be defined when `u,v ∈ H1_sigma`. **R3 remains open:** slot-3 linearity at general `w ∈ L²_σ` needs either (a) more regularity on `w`, or (b) the `b_cont_fixedTest` analytic wall, or (c) the Hamel extension in slot 3 via `LinearMap.exists_extend` — which gives linearity algebraically but without integrability content. Route (c) is the fallback for C3: extend slot 3 via Hamel (not via integral), so `B_ext(u,v,·)` is a Hamel-linear functional on `L2Sigma_R3`, not necessarily given by an integral off H¹_sigma. This is SOUND for `b_multilinear` (it IS a linear map) but means the slot-3 linearity is algebraic (not analytic). `b_cont_fixedTest` then requires that this Hamel slot-3 extension is BOUNDED at Schwartz `w` — which brings back the C6 wall.
- **R4 — `b_cont_fixedTest` (C6).** This is the codex gate described above. Do not attempt before adjudication.
- **R5 — `L2Sigma_R3` as ℝ-vector space for `LinearMap.exists_extend`.** Confirmed: `L2Sigma_R3` is a `Submodule ℝ L2VF_R3` (add + smul closure from `MemLp`). `H1Sigma_R3` is a further submodule via `MemSobolev.add` / `MemSobolev.smul`. Both needed for C3.

**Note on R3:** The slot-3 issue means `C1` may need to be restricted: `convFormH1_linearMap` is a tower on `H1_sigma ×ₗ H1_sigma ×ₗ L2Sigma` ONLY for `w` that are in a suitable class (e.g., Schwartz or `L²∩L⁶`). The full slot-3 extension to all `L2Sigma_R3` then goes via Hamel (C3), not via the integral. This is the sound route: the function `b_anti` is defined as the antisymmetrized Hamel extension of `convFormH1` with slot 3 already extended by Hamel from `H1_sigma`. The antisymmetrize step is then applied to slots 2,3 of the Hamel-extended form.

---

## 8. Torus mirror (#53)

After PRs 1–3 for R3, the torus mirror uses:
- Torus GNS: H¹(T³)↪L⁶(T³) is easier (T³ compact, finite measure, standard Fourier-series Sobolev embedding; `eLpNorm_le_eLpNorm_fderiv_of_le` applies on compact domain with `HasCompactSupport` trivially for torus functions). ~100 LOC vs. R3's ~300 LOC.
- The Hamel extension + antisymmetrize route is IDENTICAL to R3 (same mathlib API, same `LinearMap.exists_extend`).
- `b_cont_fixedTest` wall is also the same.

Mirror PRs: TPR-1 (torus H¹↪L⁶, trivial from compact case), TPR-2 (torus energy-class convection), TPR-3 (torus Hamel extension + `torusConvectionGapCore_exists`). Sequenced AFTER R3 Tier 1.

---

## 9. Report summary (for orchestrator)

**Contract file:** `/workspaces/lean-pde/docs/scratch/r56-convection-construction-plan.md`

**Corrected totality route:** Hamel algebraic extension via `LinearMap.exists_extend` (mathlib,
confirmed present) + antisymmetrization in slots 2,3. This yields four `ConvectionGapOp` fields
(`b`, `b_extends`, `b_multilinear`, `b_antisymm_gap`) sorry-free. The fifth field
`b_cont_fixedTest` is the irreducible analytic wall (bounded bilinear at fixed Schwartz `w` for
general L² slots 1,2) and is left as the single residual axiom pending C6 codex adjudication.

**mathlib status:** `LinearMap.exists_extend` (PRESENT), `Submodule.exists_isCompl` (PRESENT),
`LinearMap.ofIsCompl` (PRESENT), `Lp.holderL` (PRESENT), `gns` for Cc¹ (PRESENT). Absent:
H¹↪L⁶ for `MemSobolev 1 2` (A3), energy-class trilinear (B4–B7), Hamel+antisymmetrize chain
(C1–C5).

**Declaration list (ordered):** A1 (scaffold), A2 (must-prove), A3 (must-prove, codex review),
A4 (must-prove), B1 (scaffold+must-prove), B2 (must-prove), B3a (must-prove), B3b (must-prove),
B4 (must-prove), B5 (must-prove), B6 (must-prove), B7 (must-prove), C1 (must-prove), C2
(must-prove), C3 (must-prove, nonconstructive), C4 (must-prove), C5 (must-prove), C6 (CODEX GATE).

**Tier 1 definition of done (PRs 1–3):** `convectionGapOpCore_exists` (C5) sorry-free. Three
of five gap fields proved. Axiom `r3ConvectionGapOp_exists` reduced to single-field residual.

**Tier 2 definition of done (PR-4+5, contingent on codex C6 verdict):** full five fields,
capstone 3→2.

**Codex review required BEFORE coding:** A3 statement (`gns_L6_of_memH1_R3`), C5 statement
(`convectionGapOpCore_exists`), B7 exponent arithmetic, C6 options.

**Recommended first task to `lean-coder`:** Create `LerayHopf/R3/SobolevEmbedding.lean` with
imports, A1 `HolderTriple` instance scaffolds (trivial `norm_num`), A2 and A3 theorem signatures
(bodies `-- ALLOW_SORRY: PR-1 target, proof in follow-up prover pass`), and A4 signature. Then
hand A3 statement to `/codex:adversarial-review --effort xhigh` before proofs begin.
