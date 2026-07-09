# Mathlib API Survey — Historical Axiom Frontier

> **Historical snapshot** (as of issue #53 / PR #62). Both capstones are now
> **KERNEL-ONLY (0 project axioms)** — see `HANDOFF.md` §4 and `docs/STATUS.md` for the
> current, canonical axiom ledger and `scripts/check-axioms-live.sh` for the live pin.
> The R³ "1 project axiom" below (`r3ConvectionGapOp_exists`) was subsequently PROVED as
> `r3ConvectionGapOp_holds` (issue #56 / PR #60); this document was not updated to track it.

This document records the Mathlib declarations directly relevant to discharging (or
understanding the gap of) each axiom that was live at the time of writing. Updated after
issue #53 / PR #62.

---

## R³ capstone: current 1 project axiom (at time of writing — see banner above)

The current `#print axioms exists_lerayHopf_r3` footprint is:

| # | Axiom name | File | Mathematical content |
|---|---|---|---|
| 1 | `galerkin_limit_passage_R3` | `R3/SolutionInterfaces.lean` | Limit passage: good representative, WeakFormNS, energy inequality, initial trace |

**Removed since the earlier 5-axiom survey:**
- `curlSchwartzDense_holds` / `r3GalerkinScheme_exists` — proved by the Fourier curl-density route.
- `r3_NSForms_exist` / `r3ConvectionGapOp_exists` — proved by the determined-form BLT construction.
- `galerkin_weakLimit_R3` — proved by the strong ball-exhaustion + Mazur route.
- REMOVED: `aubin_lions_R3` (its spatial half proved; time half rerouted through two
  thinner statements; only `galerkin_spacetime_precompact_R3` remains live).
- REMOVED: `galerkin_spacetime_precompact_R3` — proved via the step-curve route (#46/PR-4).

## T³ capstone: 0 project axioms (unconditional)

`#print axioms exists_lerayHopf_torus3` = kernel axioms only (`propext`,
`Classical.choice`, `Quot.sound`). **T³ is unconditional.**

**All T³ project axioms removed:**
- `aubin_lions` — **REMOVED (issue #23, PR #89, 2026-07-04)**: now the proved
  `noncomputable def torusAubinLionsPackage_of_galSeq`
  (`LerayHopf/TorusAubinLionsAssembly.lean`) via the mode-wise spectral route.
- `galerkin_limit_passage` — **REMOVED (#25/PR #75)**: proved via
  `torus_galerkin_limit_passage_of_energyClass` + `torus_energyClass_of_aubinLions`.
- `torusConvectionGap_exists` — **REMOVED (#53/PR #62)**: now the theorem
  `torusConvectionGap_holds`.

---

## Mathlib API relevant to each axiom

### R3 axiom 1: `galerkin_spacetime_precompact_R3`

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

### Removed former R3 axiom: `galerkin_weakLimit_R3`

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

### Removed former R3 axiom: `curlSchwartzDense_holds`

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

### Removed former R3 axiom: `r3_NSForms_exist`

**What it asserts:** Existence of the R³ NS convection form b (antisymmetric, trilinear,
b_bound via Schwartz-test decay, b_galerkin = convIntegralSchwartz).

**Gap:** No (u·∇)v operator on L²(ℝ³) in Mathlib. The Schwartz-level trilinear estimates
are proved in `TrilinearEstimate.lean` (b_bound, IBP, antisymmetry) but these cover the
Schwartz-test class only; lifting to a genuine operator on L²_σ requires weak derivatives
+ IBP on ℝ³ at the Lp level, which Mathlib lacks.

**Literature:** Temam [M1] §II.1, Lemarié-Rieusset [M3] §5, Robinson–Rodrigo–Sadowski
[M4] §3.2.

---

### R3 axiom 2: `galerkin_limit_passage_R3`

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

## T³ axiom API survey (historical — all T³ axioms now removed)

### Former T³ axiom 1: `aubin_lions` (REMOVED, issue #23 / PR #89)

This was the Aubin–Lions time compactness axiom for T³. The spatial half was discharged by
`rellich_L2Sigma` (`H1Sigma.lean`). The time half — rather than the abstract Bochner
Aubin–Lions–Simon route — was discharged by the mode-wise spectral route: equi-Lipschitz
scalar test-pairings + scalar Bolzano–Weierstrass diagonal + Riesz limit curve + H¹ Fourier
tail. No `W^{1,p}(0,T;X)` or Simon's lemma was needed. The result is the proved
`noncomputable def torusAubinLionsPackage_of_galSeq`
(`LerayHopf/TorusAubinLionsAssembly.lean`), with the same binder list and conclusion type
as the former axiom.

**Mathlib used:** scalar `BoundedContinuousFunction` / Bolzano–Weierstrass (bounded real
sequences), `Continuous.aestronglyMeasurable`, lintegral Fatou, existing `viscousEnn`
quartet patterns (`TorusTraceEnergy.lean`), Riesz representation on `L2Sigma`.

### Removed former T³ axiom: `torusConvectionGap_exists`

**What it asserts:** `Nonempty TorusConvectionGap` — existence of the T³ weak convection
operator gap (IBP identity and smooth-test bound for the torus trilinear form).

**Gap:** Torus integration by parts for the (u·∇)v form. Mathlib's divergence theorem
is for ℝⁿ boxes only; no torus IBP at the Lp level. All trilinear/bilinear algebra is
proved in `TorusConvectionForm.lean`; the single gap is the IBP identity on T³.

**Literature:** Temam [M1] §II.1, Robinson–Rodrigo–Sadowski [M4] §3.2.
