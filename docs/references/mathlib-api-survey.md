# Mathlib API Survey — Current Axiom Frontier

This document records the Mathlib declarations directly relevant to discharging (or
understanding the gap of) each current project axiom. Updated after PR #45 (merged).

---

## R³ capstone: current 5 project axioms

After PR #45 the `#print axioms exists_lerayHopf_r3_axiomatic` footprint is:

| # | Axiom name | File | Mathematical content |
|---|---|---|---|
| 1 | `curlSchwartzDense_holds` | `R3/SchwartzDivFreeBasis.lean` | Helmholtz/Weyl density: closure of curls of Schwartz potentials = L²_σ(ℝ³) |
| 2 | `r3_NSForms_exist` | `R3/AxiomaticClosure.lean` | ℝ³ convection form b exists (trilinear, antisymmetric, Schwartz-test-bounded) |
| 3 | `galerkin_spacetime_precompact_R3` | `R3/ArzelaAscoliTime.lean` | LOCAL Aubin–Lions–Simon L²(0,T;L²(B_k)) precompactness (refine-capable) |
| 4 | `galerkin_weakLimit_R3` | `R3/ArzelaAscoliTime.lean` | Banach–Alaoglu + weak-closedness of L2Sigma_R3: measurable weak limit |
| 5 | `galerkin_limit_passage_R3` | `R3/AxiomaticClosure.lean` | Limit passage: good representative, WeakFormNS, energy inequality, initial trace |

**Changes from pre-PR #45 (5-axiom footprint):**
- REMOVED: `aubin_lions_R3` (its spatial half proved; time half rerouted through two
  thinner axioms below).
- ADDED: `galerkin_spacetime_precompact_R3` (axiom 3 above).
- ADDED: `galerkin_weakLimit_R3` (axiom 4 above).
- Net count: unchanged at 5 (one removed, two added; this is the "thin swap" described
  in `AubinLionsAssembly.lean`).

## T³ capstone: current 3 project axioms

`#print axioms exists_lerayHopf_torus3_axiomatic` footprint:

| # | Axiom name | File | Mathematical content |
|---|---|---|---|
| 1 | `torusConvectionGap_exists` | `TorusConvectionForm.lean` | T³ convection operator gap (IBP/smooth-test bound on T³) |
| 2 | `aubin_lions` | `AxiomaticClosure.lean` | Aubin–Lions time compactness (spatial half = rellich_L2Sigma, proved) |
| 3 | `galerkin_limit_passage` | `AxiomaticClosure.lean` | T³ limit passage to weak NS solution |

---

## Mathlib API relevant to each axiom

### Axiom 3: `galerkin_spacetime_precompact_R3`

**What it asserts:** For any Galerkin sequence + subsequence ψ + ball radius k, there
exists a further ρ and measurable g_k such that the Bochner L²(0,T;L²(B_k)) norm of
`restrictToBall k ∘ (galSeq ∘ ψ ∘ ρ) - g_k` → 0.

**Mathlib extraction plumbing (available, used in proof of downstream lemmas):**

```
MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm
  (Mathlib.MeasureTheory.Function.ConvergenceInMeasure)
  If eLpNorm (f n - g) 2 μ → 0 (with f n, g ae strongly measurable) then
  TendstoInMeasure μ f atTop g.

MeasureTheory.TendstoInMeasure.exists_seq_tendsto_ae
  (Mathlib.MeasureTheory.Function.ConvergenceInMeasure)
  TendstoInMeasure μ f atTop g → ∃ (φ : ℕ → ℕ) (hφ : StrictMono φ),
    ∀ᵐ x ∂μ, Filter.Tendsto (fun n => f (φ n) x) atTop (nhds (g x))
```

**The gap:** Mathlib has no theorem asserting that a Galerkin sequence in L²(0,T;H¹_σ)
with uniform energy bounds is relatively compact in L²(0,T;L²(B_k)). The plumbing above
gives a.e. convergence FROM an existing norm-to-zero bound; the axiom asserts that such
a further subsequence with norm→0 exists (the compactness step).

**Literature:** Simon [L4], Aubin [L3], Temam [M1] §III.2.1.

---

### Axiom 4: `galerkin_weakLimit_R3`

**What it asserts:** From per-ball a.e.-t convergence (hypothesis `hball`), extract a
measurable u : Time → L2Sigma_R3 with AEStronglyMeasurable + per-ball a.e.-t convergence.

**Mathlib declarations relevant to discharging:**

```
WeakDual.isSeqCompact_closedBall
  (Mathlib.Analysis.Normed.Module.WeakDual)
  Closed balls of the dual of a SEPARABLE normed space V are sequentially compact
  in the weak-star topology.
  -- Gap: L2VF_R3 is reflexive; need to identify it with its own dual via Riesz,
  -- then apply this to get a weakly convergent subsequence for a.e. t.

Submodule.isClosed_iff_isComplete  (or similar)
  (Mathlib.Topology.Algebra.Module.*)
  A closed submodule of a complete space is complete; completeness ⟹ IsClosed.
  -- Needed for: L2Sigma_R3 (as ⨅ k ker divTestFunctional k) is norm-closed
  -- ⟹ weakly closed (by Mazur).
  -- Direct declaration for weak closedness not found; route is:
  --   IsClosed L2Sigma_R3 (known, R3/DivergenceFree.lean) + Hahn-Banach /
  --   Mazur ⟹ weakly closed.

aestronglyMeasurable_of_tendsto_ae   (line ~1009)
  (Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable)
  If f n are ae strongly measurable and f n →ᵐ g ae, then g is ae strongly measurable.
  -- Used to conclude AEStronglyMeasurable of the assembled limit curve.
```

**What is NOT in Mathlib:**
- No direct `WeakSeqCompact_of_bounded_reflexive` for L² spaces identified with their
  own dual (the reflexive Hilbert-space sequential compactness result, which follows from
  `WeakDual.isSeqCompact_closedBall` + Riesz identification but is not threaded through
  the project's type hierarchy).
- No `L2Sigma_R3.isWeaklyClosed` (would follow from `isClosed_L2Sigma_R3` +
  Mazur/Hahn-Banach, but is not formalized at this interface in Mathlib).

**Literature:** Alaoglu [L5] (Banach–Alaoglu), Mazur [L6] (closed convex = weakly closed).

---

### Axiom 1: `curlSchwartzDense_holds`

**What it asserts:** CurlSchwartzDense — the L²-closure of the span of curls of Schwartz
vector potentials equals L²_σ(ℝ³).

**Relevant Mathlib:**
```
Submodule.orthogonal_orthogonal_eq_closure
  (Mathlib.Topology.Algebra.Module.*)
  (orthogonal complement)^⊥ = closure of the original submodule.
  -- Used in the "orthogonal complement route" in CurlDensity.lean.

Lp.fourierTransformₗᵢ  (FourierL2)
  (Mathlib.Analysis.Fourier.*)
  The L² Fourier transform as a linear isometry equivalence.

Measure.measurePreserving_neg
  Used in the Hermitian reflection step (fourier_ofReal_reflect_eq_conj,
  proved in CurlDensity.lean).
```

**Remaining wall (P2 in Stream A):** Schwartz surjectivity of φ ↦ testSymbol φ onto
anti-Hermitian Schwartz symbols. Not in Mathlib; `SchwartzMap.postcompCLM Complex.conjCLE`
is the path but the real-valuedness step is missing.

---

### Axiom 2: `r3_NSForms_exist`

**What it asserts:** Existence of the R³ NS convection form b (antisymmetric, trilinear,
b_bound via Schwartz-test decay, b_galerkin = convIntegralSchwartz).

**Gap:** No (u·∇)v operator on L²(ℝ³) in Mathlib. The Schwartz-level trilinear estimates
are proved in `TrilinearEstimate.lean` (b_bound, IBP, antisymmetry) but these cover the
Schwartz-test class only; lifting to a genuine operator on L²_σ requires weak derivatives
+ IBP on ℝ³ at the Lp level, which Mathlib lacks.

**Literature:** Temam [M1] §II.1, Lemarié-Rieusset [M3] §5, Robinson–Rodrigo–Sadowski
[M4] §3.2.

---

### Axiom 5: `galerkin_limit_passage_R3`

**What it asserts:** Good representative u (a.e. equal to AL limit), WeakFormNS, energy
inequality, initial trace, energy class.

**Proved reductions available (not yet wired):**
- `bForm_tendsto_of_strongL2` (`AubinLionsLimitPassage.lean`): b-term passage under
  strong L² convergence. Sorry-free, #print axioms clean.
- `kineticEnergy_lsc_bound` (`AubinLionsLimitPassage.lean`): OPEN (sorry) — blocked
  by time-measurability of the limit.
- `w1pTime_continuous_in_H` (`Bochner/TimeSobolev.lean`): OPEN (sorry) — Lions–Magenes
  good-representative; months-class.

**Gap (same as T³ `galerkin_limit_passage`):** No W^{1,p}(0,T;X) Bochner–Sobolev theory
in Mathlib. The weak time derivative, initial trace recovery, energy-class lower-closure,
and WeakFormNS time-IBP step all require this missing pillar.

**Literature:** Temam [M1] §III.3, Lions [M2].

---

## T³ axiom API survey

### T³ axiom 2: `aubin_lions`

Same mathematical content as `galerkin_spacetime_precompact_R3` (time-compactness) but
for T³. The spatial half is discharged by `rellich_L2Sigma` (`H1Sigma.lean`, proved via
Fourier-tail decay). The time half is the same Aubin–Lions–Simon gap as the R³ version.

**Mathlib:** Same as axiom 3 above.

### T³ axiom 1: `torusConvectionGap_exists`

**What it asserts:** `Nonempty TorusConvectionGap` — existence of the T³ weak convection
operator gap (IBP identity and smooth-test bound for the torus trilinear form).

**Gap:** Torus integration by parts for the (u·∇)v form. Mathlib's divergence theorem
is for ℝⁿ boxes only; no torus IBP at the Lp level. All trilinear/bilinear algebra is
proved in `TorusConvectionForm.lean`; the single gap is the IBP identity on T³.

**Literature:** Temam [M1] §II.1, Robinson–Rodrigo–Sadowski [M4] §3.2.
