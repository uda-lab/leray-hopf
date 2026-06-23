# Task contract: issue #47 — discharge `galerkin_weakLimit_R3`

**File to touch:** `LerayHopf/R3/ArzelaAscoliTime.lean`
**Axiom to remove:** `galerkin_weakLimit_R3`

---

## 1. What the axiom says

Given:
- a diagonal subsequence `φ : ℕ → ℕ` (StrictMono),
- a Galerkin sequence `galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n`,
- for each integer ball radius `k : ℕ`, a measurable per-ball limit `g_k : ℝ → L2ballR3 k`
  such that for a.e. `t`, `restrictToBall k ((galSeq (φ n)).u t : L2VF_R3) → g_k t`,

conclude: there exists `u : Time → L2Sigma_R3` with
- `AEStronglyMeasurable (fun t => (u t : L2VF_R3)) (volume.restrict (Icc 0 T))`, and
- for every `R : ℝ`, for a.e. `t`, `restrictToBall R ((galSeq (φ n)).u t) → restrictToBall R (u t)`.

Two components are needed:
1. **Banach–Alaoglu (pointwise-in-time):** for a.e. `t`, the bounded sequence
   `(galSeq (φ n)).u t : L2VF_R3` has a weakly convergent subsequence in `L2VF_R3`.
2. **Weak-closedness of `L2Sigma_R3`:** the weak limit lies in `L2Sigma_R3`
   (it is the kernel of a family of continuous linear functionals, hence weakly closed).
3. **Measurability gluing:** the pointwise-a.e. weak limit `u t` is AEStronglyMeasurable
   as a curve `Time → L2VF_R3` (equivalently, as a curve into the separable Hilbert space).

---

## 2. Mathlib survey — honest assessment

### 2a. Banach–Alaoglu for the DUAL space: PRESENT

`WeakDual.isCompact_closedBall` (`Mathlib.Analysis.Normed.Module.WeakDual`, line ~268):
closed balls in `WeakDual 𝕜 E` are compact (weak-star topology), when `𝕜` is proper.

`WeakDual.isSeqCompact_closedBall` (same file, line ~368):
sequential version for **separable** `E`:
> "Closed balls of the dual of a separable normed space `V` are sequentially compact
> in the weak-star topology."

`WeakDual.isSeqCompact_of_isBounded_of_isClosed` (same file, line ~349):
bounded closed sets in `WeakDual 𝕜 E` are sequentially compact when `E` is separable.

### 2b. Banach–Alaoglu for the PRIMAL space (Hilbert / reflexive): NOT PRESENT as stated

What Mathlib has for the primal weak topology:
- `NormedSpace.isCompact_closure_of_isBounded` (`Mathlib.Analysis.Normed.Module.DoubleDual`):
  transfers compactness from weak-star bidual back to weak topology on `X`, but requires
  a hypothesis `closure (inclusionInDoubleDualWeak ... '' S) ⊆ range (inclusionInDoubleDualWeak ...)`.
  This is exactly reflexivity of `X`. Mathlib does NOT provide a reflexivity instance for
  `Lp E 2 μ` or for `L2VF_R3` concretely.
- `Convex.toWeakSpace_closure` (`Mathlib.Analysis.LocallyConvex.WeakSpace`):
  the strong closure and weak closure of a convex set coincide in a locally convex space.
  This is Mazur's lemma and IS in Mathlib. It implies: every strongly closed convex set
  is weakly closed (its weak closure equals its strong closure).

The SEQUENTIAL Banach–Alaoglu for a separable Hilbert space (the statement:
"every bounded sequence in a separable Hilbert space has a weakly convergent subsequence")
**is NOT a single named theorem in Mathlib**.

The route to get it from what exists:
- `L2VF_R3 = Lp (EuclideanSpace ℝ (Fin 3)) 2 volume` is a Hilbert space
  (instance `L2.innerProductSpace`, `Mathlib.MeasureTheory.Function.L2Space`).
- Via Fréchet–Riesz, `L2VF_R3` is isometrically isomorphic to its own dual
  (`InnerProductSpace.toDual 𝕜 E`, `Mathlib.Analysis.InnerProductSpace.Dual`).
- So the DUAL Banach–Alaoglu (`WeakDual.isSeqCompact_closedBall`) for the DUAL of
  `L2VF_R3` translates to a sequential result in `L2VF_R3` itself — but this
  translation requires:
  (a) that `L2VF_R3` is separable (it is: the underlying L² of a finite-dimensional
      separable target over a σ-finite measure space is separable — `MeasureTheory.Lp.instSeparableSpace`
      or similar; needs checking for the EuclideanSpace codomain),
  (b) that the isomorphism between `L2VF_R3` and `WeakDual ℝ L2VF_R3` (via toDual)
      intertwines the weak topology on `L2VF_R3` and the weak-star topology on `WeakDual`.

This intertwining IS essentially the content of `WeakSpace` vs `WeakDual` for a Hilbert space,
but it is NOT packaged as a single named lemma in Mathlib. Assembling it would require:
  - constructing the isometric conjugate-linear equivalence `L2VF_R3 ≃L⋆[ℝ] WeakDual ℝ L2VF_R3`
    (this is `InnerProductSpace.toDual ℝ L2VF_R3`),
  - verifying it is a homeomorphism between `WeakSpace ℝ L2VF_R3` and `WeakDual ℝ L2VF_R3`,
  - then pulling back `WeakDual.isSeqCompact_closedBall` through this homeomorphism.

The Mathlib TODO comment in `WeakDual.lean` explicitly notes:
> "Add the sequential Banach-Alaoglu theorem: the dual unit ball of a separable normed space E
>  is sequentially compact in the weak-star topology. This would follow from the metrizability above."

This is now present (`isSeqCompact_closedBall`) but only for the DUAL side.

**Conclusion for component 1:** NOT a one-liner. Requires ~5–8 non-trivial sub-lemmas to
bridge from `WeakDual.isSeqCompact_closedBall` to weak sequential compactness in `L2VF_R3`.

### 2c. Weak-closedness of `L2Sigma_R3`: ACCESSIBLE via Mazur

`L2Sigma_R3` is defined as `⨅ φ, (divTestFunctional φ).ker` — the intersection of kernels
of continuous linear functionals. Each kernel is strongly closed (CLM.isClosed_ker).
By `Convex.toWeakSpace_closure` (Mazur's lemma, present in Mathlib), every strongly
closed CONVEX set is also weakly closed. Each kernel is a closed SUBSPACE (hence convex),
so it is weakly closed. An arbitrary intersection of weakly closed sets is weakly closed.

Therefore: `isClosed_L2Sigma_R3` (already proved in `DivergenceFree.lean`) + Mazur's lemma
⟹ `L2Sigma_R3` is weakly closed.

However, the statement needed here is slightly different: the weak limit of a sequence in
`L2Sigma_R3` lies in `L2Sigma_R3`. This follows from weak-closedness if we can state
"the limit of a sequence in a weakly closed set is in that set". This is the definition
of sequential closedness in the weak topology, which follows from topological closedness.

The interface gap: "weakly closed" means `IsClosed` in the `WeakSpace` topology.
`Convex.toWeakSpace_closure` gives closure equality for the `WeakSpace` image.
To extract: "`L2Sigma_R3` is closed in `WeakSpace ℝ L2VF_R3`" requires pushing the
`WeakSpace` topology through the `toWeakSpace` equivalence. This is ~2–3 lemmas of glue.

**Conclusion for component 2:** PRESENT in principle via Mazur but requires ~3 glue lemmas
to put into the form needed (IsClosed of L2Sigma_R3 in WeakSpace topology).

### 2d. Measurability of the a.e. pointwise weak limit: ACCESSIBLE

`aestronglyMeasurable_of_tendsto_ae` (`Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable`):
> "An a.e. sequential limit of a.e. strongly measurable functions is a.e. strongly measurable."
Requires: `PseudoMetrizableSpace β`, countably generated filter, a.e. tendsto.

The issue: the weak topology on `L2VF_R3` is NOT metrizable on the whole space.
However, the weak topology IS metrizable on bounded sets of a separable space
(`WeakDual.metrizable_of_isCompact` is in Mathlib for the dual side).

The measurability argument needs to work as follows:
- The pointwise-a.e. weak limits `u t` come from the a.e.-t convergence in `L2ballR3 k`,
  which is STRONG convergence (in the norm of `L2ballR3 k`).
- We need `u` to be AEStronglyMeasurable as a curve `Time → L2VF_R3` (strong topology).
- The existing proof in `ArzelaAscoliTime.lean` (the `u_lim_aestronglyMeasurable` theorem)
  deduces this FROM axiom B. Axiom B directly asserts AESM of `u`.
  Inside a proof of axiom B, we would need to construct `u t` pointwise and then verify AESM.

The measurability argument inside axiom B would be:
- For a.e. `t`, apply weak compactness to `(galSeq (φ n)).u t` (bounded sequence in `L2VF_R3`)
  to get a weakly convergent subsequence with limit `u t ∈ L2Sigma_R3`.
- The mapping `t ↦ u t` would need to be shown AESM. This is the hardest part:
  the selection is non-constructive (Axiom of Choice used in compactness) and the
  measurable selection theorem for weakly metrizable (on bounded sets) Hilbert-valued
  maps would be needed.
- `aestronglyMeasurable_of_tendsto_ae` can be applied IF the sequence of functions
  converges a.e. in the STRONG topology of `L2VF_R3`. But per-ball convergence in `L2ballR3 k`
  is NOT strong convergence in `L2VF_R3`.
- Alternative: the weak topology on the bounded subset `closedBall 0 C ⊆ WeakSpace ℝ L2VF_R3`
  is metrizable (Mathlib: `WeakDual.metrizable_of_isCompact`, which via Riesz gives the primal
  side), so the limit `u t` can be defined as a genuine metric-space limit on this compact set,
  and then `aestronglyMeasurable_of_tendsto_ae` applies in the weak metric.
  BUT: the weak norm and strong norm are different topologies, and "a.e. strongly measurable
  in the weak topology" does not directly give AESM in the strong topology.

For `L2VF_R3` which is SEPARABLE (L² of a separable Hilbert space over a σ-finite measure),
weak AESM = strong AESM (both are characterized by measurability into the Borel σ-algebra,
which for a separable Hilbert space is the same for weak and strong topologies by a standard
result). This fact needs `instSeparableSpace` for `L2VF_R3`.

**Conclusion for component 3:** ACCESSIBLE if `L2VF_R3` is known to be separable
(which requires checking the instance chain for `Lp (EuclideanSpace ℝ (Fin 3)) 2 volume`
on `ℝ³` with Lebesgue measure — expected to be present via `MeasureTheory.Lp.instSeparableSpace`
or an analogue, but needs verification).

---

## 3. The weakest sound replacement

The thinnest general statement that captures only the non-Mathlib content:

```lean
-- PROPOSED RESIDUAL AXIOM (thinnest form):
axiom L2VF_R3_weakSeqCompact_closedBall (C : ℝ) (hC : 0 ≤ C)
    (f : ℕ → L2VF_R3) (hf : ∀ n, ‖f n‖ ≤ C) :
    ∃ (φ : ℕ → ℕ) (v : L2VF_R3),
      StrictMono φ ∧
      Filter.Tendsto (fun n => (toWeakSpace ℝ L2VF_R3) (f (φ n)))
        Filter.atTop (𝓝 ((toWeakSpace ℝ L2VF_R3) v))
```

This is: **sequential weak compactness of bounded sets in L2VF_R3**.
It is the SINGLE non-Mathlib primitive. Everything else (Mazur for L2Sigma_R3,
measurability of pointwise weak limit, reassembly) can be proved from Mathlib.

Over-strength check: this is NOT over-strong. It states exactly the standard theorem
(Eberlein–Šmulian for reflexive separable Hilbert spaces, which is the sequential form of
Banach–Alaoglu on the primal space). It does NOT claim anything about the limit being in
`L2Sigma_R3` — that is proved by Mazur. It does NOT claim measurability — that comes from
separability. The name `L2VF_R3_weakSeqCompact_closedBall` encodes exactly what is proved.

---

## 4. Sub-lemma task list

### MUST-PROVE (from Mathlib — all standard glue)

**WL-1** `L2VF_R3_separable : SeparableSpace L2VF_R3`
Proof route: `Lp.instSeparableSpace` or the chain
`EuclideanSpace ℝ (Fin 3)` is finite-dimensional ⟹ separable ⟹ `Lp E 2 μ` is separable
for σ-finite μ (Lebesgue on ℝ³ is σ-finite).
Expected Mathlib lemma: `MeasureTheory.Lp.instSeparableSpace` or similar.
Status: Likely PRESENT but needs exact name check.

**WL-2** `L2VF_R3_toDual_isometry : L2VF_R3 ≃ₗᵢ[ℝ] StrongDual ℝ L2VF_R3`
(Fréchet–Riesz for L2VF_R3)
Proof route: `InnerProductSpace.toDual ℝ L2VF_R3`
Status: PRESENT in Mathlib (`Mathlib.Analysis.InnerProductSpace.Dual`).

**WL-3** `weakSpace_toDual_homeomorph : WeakSpace ℝ L2VF_R3 ≃ₜ WeakDual ℝ L2VF_R3`
(the Fréchet–Riesz isometry intertwines weak topology and weak-star topology)
This is the conceptual gap: the homeomorphism between `WeakSpace ℝ L2VF_R3` and
`WeakDual ℝ (StrongDual ℝ L2VF_R3)` via the isometry.
Status: NOT a named theorem. Requires ~3 tactics using universal properties of weak topologies.
Assessment: Provable but requires care about conjugate-linear vs linear (ℝ vs ℂ case).
For ℝ, `toDual` is linear (not conjugate-linear), making this cleaner.

**WL-4** `L2Sigma_R3_weaklyClosed : IsClosed (L2Sigma_R3 : Set (WeakSpace ℝ L2VF_R3))`
Proof route: Each `(divTestFunctional φ).ker` is strongly closed (already proved in
`DivergenceFree.lean`), hence by Mazur (`Convex.toWeakSpace_closure`) also weakly closed;
intersection of weakly closed sets is weakly closed.
Status: ACHIEVABLE from Mathlib via Mazur.

**WL-5** `weakLimit_mem_L2Sigma_R3`: if `vₙ ∈ L2Sigma_R3` and `vₙ ⇀ v` weakly in `L2VF_R3`,
then `v ∈ L2Sigma_R3`.
Proof route: from **WL-4** (weak closedness of `L2Sigma_R3`) and sequential characterization.
Status: ACHIEVABLE (1–2 tactics after WL-4).

**WL-6** `weakLimit_aestronglyMeasurable`: if `fₙ : α → L2VF_R3` are AESM and
for a.e. `t`, `fₙ t ⇀ g t` weakly in `L2VF_R3`, then `g` is AESM.
Proof route: In a separable Hilbert space, the Borel σ-algebra for the weak topology
equals the Borel σ-algebra for the strong topology (classical). The weak limits, being
limits in the metrizable weak topology on bounded sets (WL-3 + WL-1 + metrizability
from `WeakDual.metrizable_of_isCompact`), are measurable. Alternatively: the map
`t ↦ ⟪g t, e_i⟫` is measurable for each basis element `e_i` (by taking limits of
measurable functions `t ↦ ⟪fₙ t, e_i⟫`), and a separable Hilbert space is characterized
by inner products against a countable dense set.
Status: ACHIEVABLE but not trivial; requires ~5 lemmas.

### RESIDUAL AXIOM (genuinely Mathlib-absent)

**WL-A** `L2VF_R3_weakSeqCompact_closedBall`:
Bounded sequences in `L2VF_R3` (viewed as `WeakSpace ℝ L2VF_R3`) have weakly convergent
subsequences.
Mathematical content: Banach–Alaoglu / Eberlein–Šmulian for separable reflexive Hilbert space.
Mathlib route (described above) requires WL-1 + WL-2 + WL-3 + `WeakDual.isSeqCompact_closedBall`.
The gap: WL-3 (weak/weak-star homeomorphism via Riesz isometry) is NOT in Mathlib.
This is the SINGLE remaining non-trivial piece.

---

## 5. Verdict: WALL or ASSEMBLY?

**WALL — not purely assembly.**

The key obstruction is **WL-3**: the homeomorphism between `WeakSpace ℝ L2VF_R3` and
`WeakDual ℝ L2VF_R3` via the Fréchet–Riesz isometry is NOT in Mathlib.
Without it, the sequential Banach–Alaoglu for the PRIMAL Hilbert space cannot be derived
from what is present.

Size of the wall: the gap is NOT months-class. It is a 1–2 PR gap of glue work.
The lemma WL-3 can be proved from first principles (~20 lines): the weak topology on
`WeakSpace ℝ E` is induced by `{x ↦ ⟪v, x⟫ | v : E}`, and the weak-star topology on
`WeakDual ℝ E` is induced by `{f ↦ f(x) | x : E}`. Via Fréchet–Riesz, these families
correspond: `x ↦ ⟪v, x⟫` is identified with evaluation at `toDualMap v`. Both induce
the same topology on the unit ball. The key lemma is that `toWeakSpace` composed with
`toDualMap` is a homeomorphism onto `WeakDual`.

**Comparison to issue #3:** Issue #3 (GalerkinScheme assembly) was mostly pre-built assembly.
Issue #47 sits BETWEEN: more work than pure assembly, but NOT a months-class research wall.
Estimate: 2–3 PRs by a skilled `lean-prover`. The most time-consuming step is WL-3 + WL-6.

**One-PR tractability: NO.** The minimal decomposition is:
- PR A: establish WL-A as a thin axiom (possibly proved or left as a thin residual),
  plus WL-1 through WL-5, then assemble the full proof of `galerkin_weakLimit_R3`.
- PR B (optional): discharge WL-A by proving WL-3.

If WL-A is kept as a thin axiom, the PR removes `galerkin_weakLimit_R3` (the current
5-parameter, assembly-heavy axiom) and replaces it with the thinner
`L2VF_R3_weakSeqCompact_closedBall` (pure abstract FA, no Galerkin parameters, reusable).

---

## 6. The single hardest step

**WL-3** (`weakSpace_toDual_homeomorph`): proving that the Fréchet–Riesz isometry
`toDual ℝ L2VF_R3 : L2VF_R3 →L⋆[ℝ] StrongDual ℝ L2VF_R3` induces a homeomorphism
between `WeakSpace ℝ L2VF_R3` and `WeakDual ℝ L2VF_R3`.

The difficulty is purely typological (topology of weak spaces): one must show the
induced topology from evaluations by the dual coincides under the Riesz identification.
In ℝ, conjugate-linear = linear, but Lean's `toDual` is conjugate-linear in general,
requiring care about `starRingEnd` instances. For ℝ this simplifies.

**WL-6** (measurability of pointwise weak limit) is the second hardest, since it requires
either a measurable selection theorem or the coincidence of weak/strong Borel σ-algebras
in a separable Hilbert space (the latter requires SeparableSpace and some measure theory).

---

## 7. Recommended sub-axiom if WL-A is kept

```lean
axiom L2VF_R3_weakSeqCompact_closedBall -- ALLOW_AXIOM: sequential weak compactness
    -- of bounded sets in the separable Hilbert space L2VF_R3 = L²(ℝ³;ℝ³);
    -- standard Eberlein–Šmulian / Banach–Alaoglu for reflexive separable Hilbert space;
    -- Mathlib has WeakDual.isSeqCompact_closedBall but lacks the primal-space version
    -- (requires the Riesz-isometry homeomorphism between WeakSpace and WeakDual, WL-3);
    -- scheme-independent; reusable for torus #23.
    (C : ℝ) (hC : 0 ≤ C) (f : ℕ → L2VF_R3) (hf : ∀ n, ‖f n‖ ≤ C) :
    ∃ (φ : ℕ → ℕ) (v : L2VF_R3), StrictMono φ ∧
      Filter.Tendsto (fun n => (toWeakSpace ℝ L2VF_R3) (f (φ n)))
        Filter.atTop (𝓝 ((toWeakSpace ℝ L2VF_R3) v))
```

---

## 8. Definition of done for issue #47

**Minimal (thin-axiom replacement route):**
- `galerkin_weakLimit_R3` is removed as an axiom.
- A new thin axiom `L2VF_R3_weakSeqCompact_closedBall` is introduced with `ALLOW_AXIOM`.
- Lemmas WL-1 through WL-6 are proved sorry-free.
- `galerkin_weakLimit_R3` is proved as a theorem using the thin axiom + WL-1..6.
- `lake build` green; axiom count does not increase (one-for-one swap or net decrease).

**Full discharge (no residual):**
- Additionally, WL-A is proved by establishing WL-3 (Riesz homeomorphism between WeakSpace
  and WeakDual) and pulling back `WeakDual.isSeqCompact_closedBall`.
- Then `L2VF_R3_weakSeqCompact_closedBall` is also removed.

---

## 9. Ordered declaration list

| # | Name | File | Status |
|---|------|------|--------|
| 1 | `L2VF_R3_separable` | `LerayHopf/R3/DivergenceFree.lean` or new helper | must-prove |
| 2 | `L2VF_R3_toDual` | (Mathlib's `InnerProductSpace.toDual`) | present |
| 3 | `weakSpace_toDual_homeomorph` | new file or `ArzelaAscoliTime.lean` | must-prove (wall piece) |
| 4 | `L2VF_R3_weakSeqCompact_closedBall` | `ArzelaAscoliTime.lean` | thin axiom OR must-prove via 3 |
| 5 | `L2Sigma_R3_weaklyClosed` | `LerayHopf/R3/DivergenceFree.lean` | must-prove (via Mazur) |
| 6 | `weakLimit_mem_L2Sigma_R3` | `ArzelaAscoliTime.lean` | must-prove (via 5) |
| 7 | `weakLimit_aestronglyMeasurable` | `ArzelaAscoliTime.lean` | must-prove (via 1, 4) |
| 8 | `galerkin_weakLimit_R3` | `ArzelaAscoliTime.lean` | must-prove (removes axiom) |

Dependency edges:
`1 → 4`, `2 → 3 → 4`, `5 → 6`, `1 + 4 → 7`, `4 + 6 + 7 → 8`.

---

## 10. Codex review points

Before any proof is attempted, request `/codex:adversarial-review` on:
- The proposed statement of `L2VF_R3_weakSeqCompact_closedBall` (is it genuinely weaker
  than the original axiom? Does it have no hidden over-strength?).
- The statement of `weakSpace_toDual_homeomorph` (does the topology claim hold
  for the conjugate-linear Riesz map over ℝ?).
- The statement of `weakLimit_aestronglyMeasurable` (is the hypothesis per-ball a.e.
  convergence strong enough to conclude AESM in the strong topology?).

---

## 11. Summary

**Verdict:** WALL (moderate scale), not months-class, approximately 2–3 PRs.

**Key Mathlib decls found:**
- PRESENT: `WeakDual.isSeqCompact_closedBall` (sequential Banach–Alaoglu for DUAL of separable space)
- PRESENT: `Convex.toWeakSpace_closure` (Mazur's lemma — strong-closed convex = weakly closed)
- PRESENT: `InnerProductSpace.toDual` (Fréchet–Riesz isometry)
- PRESENT: `aestronglyMeasurable_of_tendsto_ae` (measurability of a.e. limits in pseudometrizable spaces)
- ABSENT: sequential Banach–Alaoglu for the PRIMAL Hilbert space (needs WL-3 as the bridge)
- ABSENT: `WeakSpace`/`WeakDual` homeomorphism via Riesz isometry (WL-3)

**Hardest step:** WL-3 (Riesz homeomorphism between `WeakSpace ℝ L2VF_R3` and `WeakDual ℝ L2VF_R3`).

**Tractable in one PR: NO.** Recommend thin-axiom swap route: PR-A removes `galerkin_weakLimit_R3`
and replaces with thinner `L2VF_R3_weakSeqCompact_closedBall` (pure abstract FA, no PDE parameters),
then PR-B discharges `L2VF_R3_weakSeqCompact_closedBall` via WL-3.
