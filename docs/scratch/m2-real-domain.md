# M2 Task Contract: Real Domain & Function Spaces

**Milestone:** M2 — "Real domain & function spaces"  
**Scope:** `docs/milestone.md` Milestone 5 territory + refinement of M1 placeholders.  
**Planner:** lean-planner · 2026-06-10  
**Status of M1 spine:** in progress (Basic/Statement/GalerkinPackage/ExistenceFromPackage/EnergySkeleton)

---

## 0. Preamble and decision points for the orchestrator

The following questions must be resolved **before** coding begins. They have
mathematical consequences that propagate through every subsequent declaration.

### Decision 0-A — scalar field for velocity

A Navier–Stokes velocity field on T³ is ℝ³-valued (3 real components).
In Lean, the natural type is `Fin 3 → ℝ` (or `EuclideanSpace ℝ (Fin 3)`,
which is `PiLp 2 (fun _ : Fin 3 => ℝ)`, confirmed below).

The `mFourierBasis` and `mFourierCoeff` in mathlib take the coefficient space
`E` to be a `NormedSpace ℂ E` (complex scalars acting on `E`).
This means:

- `L²(T³; ℂ)` = `Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 3)))` —
  **directly supported** by `mFourierBasis`.
- `L²(T³; ℝ)` = `Lp ℝ 2 …` — basis convergence theorems are stated over ℂ;
  ℝ scalar fields need a complexification detour or real-to-ℂ embedding at
  the Fourier-series level.
- `L²(T³; EuclideanSpace ℝ (Fin 3))` — Bochner Lp with vector-valued codomain
  is supported (`Lp E p μ` for `E = EuclideanSpace ℝ (Fin 3)`, a
  `NormedAddCommGroup` with an `InnerProductSpace ℝ`), but `mFourierBasis`
  infrastructure (in `AddCircleMulti`) works for ℂ-module `E`; vector-valued
  Fourier modes would need component-wise projections.

**Recommended resolution:**

For M2 define `VelocityField` as a type alias for
`Lp (EuclideanSpace ℝ (Fin 3)) 2 (volume : Measure (UnitAddTorus (Fin 3)))`.
For Fourier series work in M3, use the component-wise decomposition: the
`j`-th component lies in `Lp ℝ 2 …`, which embeds into `Lp ℂ 2 …` via
`IsROrC.ofReal`, keeping `mFourierBasis` usable. This is the most honest choice;
embedding or complexification should be explicit, not hidden.

**Orchestrator must confirm one of:**
1. Use `EuclideanSpace ℝ (Fin 3)` as the velocity codomain (recommended).
2. Use `ℂ`-valued scalar fields for simplicity (less physically faithful
   for the energy inner product).
3. Something else (give explicit type).

### Decision 0-B — measure normalization on T³

Mathlib provides two measures for `UnitAddCircle`:

- `AddCircle.haarAddCircle` — Haar measure normalized to **total mass 1**
  (a probability measure). Used in `AddCircleMulti` for `mFourierBasis`.
- `AddCircle.measureSpace` (= `volume`) — Haar measure of **total mass T**
  for `AddCircle T`. For `T = 1` these agree up to a scalar.

The product `MeasureSpace (∀ i : Fin 3, UnitAddCircle)` (i.e.
`UnitAddTorus (Fin 3)`) is the Pi measure via
`MeasureTheory.MeasureSpace.pi` (`Mathlib/MeasureTheory/Constructions/Pi.lean:215`).
But `AddCircleMulti` uses a `local instance : MeasureSpace UnitAddCircle` that
sets `volume := haarAddCircle` (prob. measure), so `volume` on
`UnitAddTorus (Fin 3)` is the **probability** product measure.

**For M2 we adopt the probability/Haar normalization** (total mass 1). All
function-space norms inherit this choice; it is consistent with `mFourierBasis`.
The orchestrator should record this in `STATUS.md` once confirmed.

---

## 1. File layout

```text
LerayHopf/
  Basic.lean              ← EDIT: replace Torus3 placeholder
  TorusDomain.lean        ← NEW: UnitAddTorus instance + type aliases
  FunctionSpaces.lean     ← NEW: L2VF, L2Sigma, H1Sigma definitions
  TorusFourier.lean       ← NEW (partial): mFourierBasis wrapper + L2Sigma Fourier filter
```

These four files comprise M2. They must compile before M3 begins.

`Basic.lean` gets exactly one surgical edit: `Torus3` is promoted from
`PUnit`-backed placeholder to the real torus. All other `Basic.lean` content
is unchanged.

---

## 2. Declaration list, ordered by dependency

### File 1: `LearyHopf/Basic.lean` (edit only)

**D-01 · `Torus3`** — `must-prove` (the new definition must typecheck cleanly)

- Current: `def Torus3 : Type := PUnit` with zero measure.
- Replace with:
  ```lean
  /-- The spatial 3-torus 𝕋³.
  Realized as `UnitAddTorus (Fin 3)` — the product of three copies of
  `UnitAddCircle = AddCircle (1 : ℝ)`. -/
  abbrev Torus3 := UnitAddTorus (Fin 3)
  ```
  and **delete** the manual `MeasureSpace Torus3` instance; the Pi instance
  `MeasureTheory.MeasureSpace.pi` in `Mathlib/MeasureTheory/Constructions/Pi.lean`
  provides it automatically, given that `MeasureSpace UnitAddCircle` is inherited
  from `AddCircle.measureSpace` (`Mathlib/MeasureTheory/Integral/IntervalIntegral/Periodic.lean`).

  **Caveat:** `AddCircle.measureSpace` sets volume = T = 1 (total mass 1 for
  `AddCircle 1`), which coincides with `haarAddCircle`. The Pi measure on
  `Fin 3 → UnitAddCircle` is the product of three such, so total mass = 1.

- Required imports to add to `Basic.lean`:
  ```lean
  import Mathlib.Topology.Instances.AddCircle.Real       -- UnitAddCircle, UnitAddTorus
  import Mathlib.MeasureTheory.Constructions.Pi          -- MeasureSpace.pi
  import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic  -- measureSpace instance
  ```
  Remove: `import Mathlib.MeasureTheory.Measure.Lebesgue.Basic` (no longer needed for this file).

- **Monotone check:** PUnit placeholder → real torus. The zero measure is gone;
  the real Haar/volume measure is installed. This is a genuine strengthening, not a weakening.

- Dependency: none (base file).

---

### File 2: `LerayHopf/TorusDomain.lean` (new)

This file consolidates the domain type, its instances, and basic aliases.
It imports `Basic.lean`.

**D-02 · `LerayHopf.torus3_measureSpace`** — scaffold-only (instances come from mathlib)

The goal of this declaration is to document (not prove) the chain of instances
that gives `Torus3` its `MeasureSpace`:

```lean
-- Confirm instances compile:
example : MeasureSpace Torus3 := inferInstance
example : IsProbabilityMeasure (volume : Measure Torus3) := inferInstance
example : Measure.IsAddHaarMeasure (volume : Measure Torus3) := inferInstance
```

These `example` blocks are proof-of-instance checks, not named theorems. If
they fail, there is an import or instance-resolution gap that must be fixed
before proceeding. **They count as must-typecheck.**

- Mathlib source:  
  - `UnitAddTorus (Fin 3)` = `Fin 3 → UnitAddCircle`  
    (`Mathlib/Topology/Instances/AddCircle/Real.lean:52`)
  - `MeasureSpace (∀ i, α i)` from `MeasureTheory.MeasureSpace.pi`  
    (`Mathlib/MeasureTheory/Constructions/Pi.lean:215`)
  - `IsProbabilityMeasure` for the product via `pi.instIsProbabilityMeasure`  
    (`Mathlib/MeasureTheory/Constructions/Pi.lean:312`, applies when each factor is a probability measure)
  - `AddCircle.measureSpace` for `UnitAddCircle`  
    (`Mathlib/MeasureTheory/Integral/IntervalIntegral/Periodic.lean:67`)

**D-03 · `LerayHopf.VelocityValue`** — scaffold-only

```lean
/-- The fiber type of a velocity field: a 3-vector of real numbers. -/
abbrev VelocityValue := EuclideanSpace ℝ (Fin 3)
```

`EuclideanSpace ℝ (Fin 3)` = `PiLp 2 (fun _ : Fin 3 => ℝ)`  
(`Mathlib/Analysis/InnerProductSpace/PiL2.lean:111`)  
carries `NormedAddCommGroup`, `InnerProductSpace ℝ`, `CompleteSpace` all for free.

---

### File 3: `LerayHopf/FunctionSpaces.lean` (new)

Imports: `TorusDomain.lean`, plus:
```lean
import Mathlib.MeasureTheory.Function.LpSpace.Basic   -- Lp
import Mathlib.MeasureTheory.Function.L2Space          -- L2.innerProductSpace
import Mathlib.MeasureTheory.Function.LpSpace.Complete -- instCompleteSpace
import Mathlib.Analysis.Fourier.AddCircleMulti         -- mFourierBasis, mFourierCoeff
```

**D-04 · `LerayHopf.L2VF`** — scaffold-only

```lean
/-- L²(𝕋³; ℝ³) — the Bochner L² space of ℝ³-valued functions on the 3-torus.
Used as the ambient space for velocity fields. -/
abbrev L2VF := Lp VelocityValue 2 (volume : Measure Torus3)
```

- Mathlib source: `MeasureTheory.Lp` (`Mathlib/MeasureTheory/Function/LpSpace/Basic.lean:89`)
- `Lp E 2 μ` for `E : NormedAddCommGroup` with `CompleteSpace E` carries:
  - `NormedAddCommGroup` (instance, `instNormedAddCommGroup`, fact `1 ≤ 2`)
  - `CompleteSpace` (instance, `instCompleteSpace`, `Mathlib/MeasureTheory/Function/LpSpace/Complete.lean:378`)
  - `NormedSpace ℝ` (from `MemLp`-to-`Lp` apparatus; `E = VelocityValue` is an ℝ-module)
  - **No** `InnerProductSpace ℝ` directly, because `VelocityValue` is ℝ-valued
    not ℂ-valued. (The `L2.innerProductSpace` instance at
    `Mathlib/MeasureTheory/Function/L2Space.lean:192` is over `𝕜 : RCLike`
    and requires `E` to be an `InnerProductSpace 𝕜 E`; `VelocityValue` is an
    `InnerProductSpace ℝ VelocityValue` so `𝕜 = ℝ` and the instance fires.)

  Instance check (must-typecheck, not named):
  ```lean
  example : InnerProductSpace ℝ L2VF := inferInstance
  example : CompleteSpace L2VF := inferInstance
  ```

**D-05 · `LerayHopf.L2C`** — scaffold-only (helper for Fourier diagonal)

```lean
/-- L²(𝕋³; ℂ) — complex scalar L² space. Used as the ambient space for
scalar Fourier modes; velocity components embed here via ofReal. -/
abbrev L2C := Lp ℂ 2 (volume : Measure Torus3)
```

`mFourierBasis` in mathlib (`Mathlib/Analysis/Fourier/AddCircleMulti.lean:265`)
is a `HilbertBasis (d → ℤ) ℂ L²(UnitAddTorus d)` where `L²(α)` is notation for
`Lp ℂ 2 (volume : Measure α)`. Instantiating at `d = Fin 3` gives
`HilbertBasis (Fin 3 → ℤ) ℂ L2C` directly. **No new proof needed.**

**D-06 · `LerayHopf.torus3_mFourierBasis`** — must-prove (instantiation, no sorry)

```lean
/-- The ℤ³-indexed Fourier Hilbert basis for L²(𝕋³; ℂ). -/
noncomputable def torus3_mFourierBasis :
    HilbertBasis (Fin 3 → ℤ) ℂ L2C :=
  UnitAddTorus.mFourierBasis
```

This is a one-line unfolding of `UnitAddTorus.mFourierBasis` at `d = Fin 3`.
No proof. Requires that `UnitAddTorus (Fin 3)` definitionally equals `Torus3`
(it does by the `abbrev` in D-01) and that the `local instance : MeasureSpace
UnitAddCircle` in `AddCircleMulti` matches the `volume` on `Torus3` (it does
because both use `AddCircle.haarAddCircle`).

**Important gap:** `AddCircleMulti` sets `local instance : MeasureSpace
UnitAddCircle := ⟨AddCircle.haarAddCircle⟩` while `Periodic.lean` uses
`AddCircle.measureSpace` (which for `T = 1` equals `ENNReal.ofReal 1 • haarAddCircle`
= `haarAddCircle`). These coincide but are not definitionally equal without
a `simp` lemma (`AddCircle.volume_eq_smul_haarAddCircle` at T=1).
The `lean-coder` must check whether this causes an instance-mismatch error
and, if so, introduce:

```lean
-- TODO(lean-coder): verify or prove
example : (volume : Measure UnitAddCircle) = AddCircle.haarAddCircle := by
  simp [AddCircle.volume_eq_smul_haarAddCircle]
```

If it does cause a mismatch, one approach is to redefine `Torus3` using the
`haarAddCircle` measure explicitly (installing `MeasureSpace UnitAddCircle`
locally as in `AddCircleMulti`). This is a **lean-coder decision**, but the
planner flags it as the most likely friction point in M2.

**D-07 · `LerayHopf.mFourierCoeff3`** — scaffold-only (type alias, no proof)

```lean
/-- Fourier coefficient at wavenumber k ∈ ℤ³ for a ℂ-valued L² function on T³.
The n-th coefficient of f is mFourierCoeff f n = ∫ t, mFourier (-n) t • f t.  -/
noncomputable abbrev mFourierCoeff3 (f : L2C) (k : Fin 3 → ℤ) : ℂ :=
  UnitAddTorus.mFourierCoeff (f : Torus3 → ℂ) k
```

Note: `UnitAddTorus.mFourierCoeff` is defined for `f : UnitAddTorus d → E`
(`E` a `NormedSpace ℂ E`), not for `f : Lp ℂ 2 μ` directly. The coercion
`(f : Torus3 → ℂ)` goes through `Lp.coeFn`. Measurability is implicit.
This is a scaffold definition — the `lean-coder` may need to use `AEEqFun`
API to handle the a.e. equivalence class issue.

---

#### 3-A. L²_σ(T³): divergence-free subspace

This is the most substantial M2 build and the hardest gap. Mathlib does not
provide a `divergence` operator for torus functions or a divergence-free
subspace predicate. Everything below must be built.

**D-08 · `LerayHopf.isDivFree_mFourier`** — must-prove (small lemma)

Mathematical content: A Fourier mode `e_k(x) = exp(2πi k·x)` with amplitude
vector `v : ℂ³` (or `EuclideanSpace ℂ (Fin 3)`) is divergence-free iff `k · v = 0`
(inner product over ℤ/ℂ). In the Fourier domain, `div(v e_k) = i k · v` (where
`k·v` is the standard inner product).

On the torus, divergence of a smooth function can be defined via the Fourier
characterization: `div u = 0` iff `∑_k (k · û(k)) e_k = 0` iff `k · û(k) = 0`
for all k. A distribution-theoretic or weak formulation must be chosen.

**Plan:** Define divergence-free via the Fourier characterization (avoiding the
need for a full distributional divergence operator):

```lean
/-- Predicate: a function u in L²(T³; ℂ³) is divergence-free (in the L² sense)
if for every wavenumber k, the k-th Fourier coefficient of u satisfies k · û(k) = 0.
This is the Fourier characterization of div u = 0 for L² vector fields on T³. -/
def DivFreeL2 (u : Lp (EuclideanSpace ℂ (Fin 3)) 2 (volume : Measure Torus3)) : Prop :=
  ∀ k : Fin 3 → ℤ,
    ∑ i : Fin 3, (k i : ℂ) * mFourierCoeff3_component u i k = 0
```

where `mFourierCoeff3_component u i k` is the k-th Fourier coefficient of the
i-th component of u. The exact type requires the component-extraction morphism.

**Gap assessment for D-08:** `mathlib` has:
- `UnitAddTorus.mFourierCoeff` for ℂ-valued functions ✓
- `EuclideanSpace.proj : EuclideanSpace 𝕜 ι → 𝕜` ✓
- Standard inner product / `Finset.sum` on `Fin 3 → ℤ` ✓

What is missing:
- No `Lp (EuclideanSpace ℂ (Fin 3)) 2` component extraction with Fourier
  coefficient interaction. The lean-coder must show that the Fourier coefficients
  of the components of a vector-valued function are the components of the
  vector-valued Fourier coefficient. This is elementary but requires a short proof.

**Tag: must-prove. Small.** Codex review recommended on the statement.

**D-09 · `LerayHopf.L2Sigma`** — scaffold-only initially, promoted to must-prove by end of M2

```lean
/-- L²_σ(T³): the closed subspace of divergence-free vector fields in L²(T³; ℝ³).

Defined as the topological closure of the span of the divergence-free Fourier modes
{e_k ⊗ v : k ∈ ℤ³, v ∈ ℝ³, k · v = 0}. This is a closed subspace of L²VF,
hence itself a Hilbert space. -/
noncomputable def L2SigmaSubspace : Submodule ℝ L2VF :=
  (Submodule.span ℝ
    {f : L2VF | ∃ (k : Fin 3 → ℤ) (v : EuclideanSpace ℝ (Fin 3)),
       (∑ i, (k i : ℝ) * v i = 0) ∧ f = mFourierMode3_real k v}).topologicalClosure

abbrev L2Sigma := L2SigmaSubspace
```

Here `mFourierMode3_real k v` is the real vector field `x ↦ (Re e_k(x)) • v`
(the real part of a Fourier mode, treated as an L² function). Its definition
requires a subsidiary declaration (see D-10).

**Gap assessment:**
- `Submodule.topologicalClosure` exists: `Mathlib/Topology/Algebra/Module/Basic.lean:157` ✓
- `Submodule.isClosed_topologicalClosure`: `Mathlib/Topology/Algebra/Module/Basic.lean:174` ✓
- `IsClosed → CompleteSpace` for a submodule: `Mathlib/Topology/Algebra/Module/Basic.lean:214` ✓
- Orthogonal projection onto a closed subspace:
  `Submodule.orthogonalProjectionOnto : E →L[𝕜] K` given `K.HasOrthogonalProjection`
  (`Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean:143`)  
  and `HasOrthogonalProjection.ofCompleteSpace` fires when `CompleteSpace K`  
  (`Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean:53`) ✓

**What must be built:**
- The injection `mFourierMode3_real` (D-10).
- Proof that `L2SigmaSubspace` is non-trivially characterized (i.e. that the
  Fourier-diagonal criterion is equivalent to topological closure of span).
  This equivalence is a non-trivial Fourier-analytic fact.

**Decision for the orchestrator:** The Fourier-diagonal characterization requires
knowing that the mFourier modes are dense and that the span of divergence-free
modes is dense in L²_σ. This is true analytically but requires a proof that
`L2SigmaSubspace` coincides with the set `{u : ∀ k, k·û(k) = 0}`. This
equivalence is **not** in mathlib and is the main analytical content of M2.

**Recommendation:** For M2, define `L2Sigma` as the topological closure of the
span (D-09) and define `DivFreeL2` separately (D-08), and *axiomatize* the
equivalence:

```lean
axiom L2Sigma_eq_divFreeL2 :
    ∀ u : L2VF, u ∈ L2Sigma ↔ DivFreeL2 u
-- ALLOW_AXIOM: Fourier density + div-free span density on T³;
--   discharging in M3 requires mFourier density + divergence cancellation
```

This is honest: the closure-of-span definition is rigorous; the Fourier
characterization is the content that needs to be proved (or axiomatized).

**D-10 · `LerayHopf.mFourierMode3_real`** — must-prove (small)

```lean
/-- The real Fourier mode at wavenumber k with amplitude v.
The map k v ↦ (the real part of e_k) ⊗ v, as an element of L²(T³; ℝ³). -/
noncomputable def mFourierMode3_real
    (k : Fin 3 → ℤ) (v : EuclideanSpace ℝ (Fin 3)) : L2VF := by
  apply MeasureTheory.Lp.toLp (fun x => (mFourier k x).re • v)
  -- MemLp proof: continuous function on compact space is in Lp
  exact (ContinuousMap.continuous _).memLp_of_isCompact
```

The exact elaboration requires that `fun x => (mFourier k x).re • v` is
measurable and in L² (both follow from continuity + compactness of Torus3).
The `lean-coder` will need `MeasureTheory.Continuous.memLp` or similar.
This is a short proof.

---

#### 3-B. H¹(T³) and H¹_σ(T³)

**Summary of mathlib Sobolev API:**

The file `Mathlib/Analysis/Distribution/Sobolev.lean` defines Bessel potential
Sobolev spaces `MemSobolev s p f` for tempered distributions on a finite-
dimensional normed space `E` (variables: `[FiniteDimensional ℝ E]`). This is
the **whole-space ℝⁿ Sobolev theory** via the Fourier transform, **not** the
torus Sobolev theory.

For `T³`, mathlib does **not** have a named Sobolev space type. The correct
approach for the torus is the Fourier multiplier / weighted ℓ² approach:

H¹(T³) = {u ∈ L²(T³) : ∑_k (1 + |k|²) |û(k)|² < ∞}

with norm ‖u‖²_{H¹} = ∑_k (1 + |k|²) |û(k)|².

**D-11 · `LerayHopf.H1Torus`** — scaffold-only for M2

```lean
/-- H¹(T³; ℂ): the Sobolev space of order 1 on the 3-torus, defined as the
Fourier-weighted ℓ² subspace of L²(T³; ℂ).

H¹(T³) ≅ {f ∈ L²(T³;ℂ) | ∑_k (1 + ‖k‖²) |f̂(k)|² < ∞}

where ‖k‖² = ∑ᵢ kᵢ².  In this Lean formalization the space is realized as
a subtype of L2C, defined by the membership predicate below.  No mathlib
Sobolev-on-torus API exists; this must be built. -- TODO(M2): full definition.
-/
def memH1Torus (f : L2C) : Prop :=
  Summable (fun k : Fin 3 → ℤ =>
    (1 + ∑ i, (k i : ℝ) ^ 2) * ‖mFourierCoeff3 f k‖ ^ 2)

def H1Torus : Set L2C := {f | memH1Torus f}
```

The `Summable` predicate on `Fin 3 → ℤ` is available from
`Mathlib/Topology/Algebra/InfiniteSum/Basic`. The rest requires no new mathlib.

**Gap:**  No proof that `H1Torus` is a submodule, a Hilbert space under the
weighted norm, or that the inclusion `H1Torus ↪ L2C` is continuous/compact.
These are the core M3 tasks. For M2, the definition suffices as scaffold.

**D-12 · `LerayHopf.Torus.H1SigmaSubspace`** — scaffold-only for M2

```lean
/-- H¹_σ(T³): the divergence-free H¹ subspace (real vector fields). -/
def H1SigmaSubspace : Submodule ℝ L2VF :=
  L2SigmaSubspace ⊓ {f | f ∈ H1Torus}  -- informal; needs proper type alignment
  -- TODO(M2): proper definition after H1Torus and L2Sigma are unified
```

This is intentionally left as a TODO for M2/M3 boundary. The clean definition
requires establishing `H1Torus` as a submodule and intersecting with `L2Sigma`.

---

### File 4: `LerayHopf/TorusFourier.lean` (new, partial for M2)

This file wraps `mFourierBasis` and provides the API needed by M3's Galerkin
projections.

**D-13 · `LerayHopf.fourierProjection_n`** — scaffold-only

```lean
/-- The n-th Galerkin projection: project a function f in L²(T³;ℂ) onto the span
of Fourier modes {e_k : ‖k‖_∞ ≤ n}. Defined as the partial sum of the Hilbert
basis expansion.

P_n f = ∑_{|k|_∞ ≤ n} ⟪e_k, f⟫ e_k
-/
noncomputable def fourierProjection_n (n : ℕ) (f : L2C) : L2C :=
  ∑ k ∈ Finset.filter (fun k => k.sup' ‖·‖ ≤ n) Finset.univ,  -- informal indexing
    (mFourierBasis.repr f) k • (mFourierBasis k)
```

The precise Finset over `Fin 3 → ℤ` with `‖k‖_∞ ≤ n` requires care:
`(Fin 3 → ℤ)` is not a Fintype, so the sum must be over a finite subset.
The lean-coder should use `Finset.filter (fun k : Fin 3 → ℤ => ∀ i, |k i| ≤ n)
(Finset.pi (Finset.Icc (-n) n))` or similar.

This is scaffold-only for M2; the continuity and projection properties are M3.

**D-14 · `LerayHopf.fourierProjection_n_tendsto`** — must-prove (uses mathlib)

```lean
/-- The Galerkin projections P_n converge to the identity in L²(T³;ℂ). -/
theorem fourierProjection_n_tendsto (f : L2C) :
    Filter.Tendsto (fun n => fourierProjection_n n f) Filter.atTop (nhds f) := by
  -- follows from HilbertBasis.hasSum_repr and properties of
  -- sub-partial sums tending to the full sum
  sorry -- ALLOW_SORRY: depends on D-13 definition being finalized
```

The mathematical content follows from `mFourierBasis.hasSum_repr`
(`Mathlib/Analysis/InnerProductSpace/l2Space.lean:440`) which gives
`HasSum (fun i => mFourierBasis.repr f i • mFourierBasis i) f`. Converting
HasSum to Tendsto of partial sums over increasing Finsets requires
`HasSum.tendsto_sum_nat` or the filter-atTop apparatus. This is provable but
non-trivial; the prover will need to match the specific Finset shape.

**Tag: must-prove (with marked sorry until D-13 is finalized).**

---

## 3. Dependency edges (strict order)

```
D-01 (Torus3 edit in Basic.lean)
  └─ D-02 (instance checks, TorusDomain.lean)
       └─ D-03 (VelocityValue)
            ├─ D-04 (L2VF)
            │    ├─ D-10 (mFourierMode3_real)
            │    │    └─ D-09 (L2SigmaSubspace)
            │    │         └─ D-12 (H1SigmaSubspace)
            │    └─ D-08 (DivFreeL2)
            └─ D-05 (L2C)
                 ├─ D-06 (torus3_mFourierBasis)
                 │    └─ D-07 (mFourierCoeff3)
                 │         ├─ D-11 (H1Torus)
                 │         └─ D-13 (fourierProjection_n)
                 │              └─ D-14 (fourierProjection_n_tendsto)
                 └─ D-06 (feeds into D-13)
```

Fan-out after D-05 and D-04 can be done in parallel.

---

## 4. Mathlib building blocks (verified by grep)

| Component | Mathlib path | Status |
|---|---|---|
| `UnitAddTorus (d : Type*)` = `d → UnitAddCircle` | `Topology/Instances/AddCircle/Real.lean:52` | exists |
| `UnitAddCircle = AddCircle (1 : ℝ)` | `Topology/Instances/AddCircle/Real.lean:48` | exists |
| `AddCircle.measureSpace` (Haar, total mass T) | `MeasureTheory/Integral/IntervalIntegral/Periodic.lean:67` | exists |
| `MeasureTheory.MeasureSpace.pi` | `MeasureTheory/Constructions/Pi.lean:215` | exists |
| `IsProbabilityMeasure` for Pi of prob. measures | `MeasureTheory/Constructions/Pi.lean:312` | exists |
| `MeasureTheory.Lp E p μ` | `MeasureTheory/Function/LpSpace/Basic.lean:89` | exists |
| `Lp.instNormedAddCommGroup` | `MeasureTheory/Function/LpSpace/Basic.lean:384` | exists |
| `Lp.instCompleteSpace` | `MeasureTheory/Function/LpSpace/Complete.lean:378` | exists |
| `L2.innerProductSpace` (for `Lp E 2 μ`) | `MeasureTheory/Function/L2Space.lean:192` | exists |
| `EuclideanSpace ℝ (Fin 3)` = `PiLp 2 (fun _ : Fin 3 => ℝ)` | `Analysis/InnerProductSpace/PiL2.lean:111` | exists |
| `PiLp.innerProductSpace` | `Analysis/InnerProductSpace/PiL2.lean:82` | exists |
| `UnitAddTorus.mFourier : C(UnitAddTorus d, ℂ)` | `Analysis/Fourier/AddCircleMulti.lean:49` | exists |
| `UnitAddTorus.mFourierBasis : HilbertBasis (d→ℤ) ℂ L²(UnitAddTorus d)` | `Analysis/Fourier/AddCircleMulti.lean:265` | exists |
| `UnitAddTorus.mFourierCoeff f n` | `Analysis/Fourier/AddCircleMulti.lean:246` | exists |
| `UnitAddTorus.hasSum_mFourier_series_L2` | `Analysis/Fourier/AddCircleMulti.lean:285` | exists |
| `AddCircle.fourierCoeff f n` (1D case) | `Analysis/Fourier/AddCircle.lean:297` | exists |
| `HilbertBasis.hasSum_repr` | `Analysis/InnerProductSpace/l2Space.lean:440` | exists |
| `Submodule.topologicalClosure` | `Topology/Algebra/Module/Basic.lean:157` | exists |
| `Submodule.isClosed_topologicalClosure` | `Topology/Algebra/Module/Basic.lean:174` | exists |
| `IsClosed → CompleteSpace` for submodule | `Topology/Algebra/Module/Basic.lean:214` | exists |
| `Submodule.orthogonalProjectionOnto` | `Analysis/InnerProductSpace/Projection/Basic.lean:143` | exists |
| `HasOrthogonalProjection.ofCompleteSpace` | `Analysis/InnerProductSpace/Projection/Basic.lean:53` | exists |
| `lp.instInnerProductSpace` (ℓ² sequence space) | `Analysis/InnerProductSpace/l2Space.lean:110` | exists |
| `TemperedDistribution.memSobolev` (ℝⁿ Sobolev) | `Analysis/Distribution/Sobolev.lean:149` | exists (ℝⁿ ONLY) |

---

## 5. Gaps to build (not in mathlib)

| Gap | Severity | Plan |
|---|---|---|
| Divergence operator on T³ (even weak/distributional) | High | Define via Fourier character (D-08 predicate); avoid full distributional setup |
| `DivFreeL2` predicate (D-08) | Must build | 5–10 lines, uses mFourierCoeff |
| `mFourierMode3_real` (D-10) | Must build | ~10 lines, uses Lp.toLp + continuity |
| `L2SigmaSubspace` span + closure (D-09) | Must build | Submodule.span + topologicalClosure, ~ 20 lines |
| Equivalence: closure-of-span = Fourier-diagonal criterion | Research-level | Axiomatize for M2; discharge M3+ |
| `H1Torus` as Hilbert space with weighted norm | Must build | Define as set first (D-11); submodule/norm in M3 |
| Torus Sobolev embedding / Rellich compactness | Not in mathlib | Axiomatize in M6 (compactness axioms milestone) |
| `fourierProjection_n` onto finite-dim subspace (D-13) | Must build | ~15 lines once Finset shape is fixed |
| `fourierProjection_n_tendsto` (D-14) | Must prove | Uses HilbertBasis.hasSum_repr from mathlib |
| Component extraction for vector-valued Fourier coefficients | Must build | ~5 lines, uses `EuclideanSpace.proj` |
| Leray projection `Π_div` (onto L2Sigma) | Must build (M3) | Uses `orthogonalProjectionOnto` once L2Sigma is complete |

**The Sobolev spaces on T³ are entirely absent from mathlib.** `TemperedDistribution.memSobolev`
covers only ℝⁿ via the Schwartz space + Fourier transform. The torus Sobolev
theory must be developed from the Fourier characterization. This is genuine
mathematical infrastructure, not a gap that can be bridged by imports.

---

## 6. M1 placeholder update summary

| M1 item | Location | M2 change | Monotone? |
|---|---|---|---|
| `Torus3 := PUnit` + zero measure | `Basic.lean:30-35` | Replaced by `abbrev Torus3 := UnitAddTorus (Fin 3)` with Haar measure | YES — real torus replaces dummy |
| `SpatialField Ω` placeholder struct | `Basic.lean:38-41` | No change in M2; replaced in M3 when velocity fields are attached to solution fields | — |
| `LerayHopfSolution.u : Time → Type` | `Basic.lean:51` | No change in M2; refined in M3 to use L2VF | — |
| `LerayHopfSolution.energy_class : Prop` | `Basic.lean:57` | No change in M2; refined in M4 | — |

All M2 changes to `Basic.lean` are monotone: the placeholder is replaced by the
real object; no analytical content is weakened.

---

## 7. Axiom ledger for M2

```lean
-- In LerayHopf/FunctionSpaces.lean:
axiom L2Sigma_eq_divFreeL2 :
    ∀ u : L2VF, u ∈ L2Sigma ↔ DivFreeL2 u
-- ALLOW_AXIOM: density of divergence-free Fourier modes in L²_σ(T³);
--   requires: (a) mFourier modes are dense in L²(T³) [from mFourierBasis],
--             (b) divergence-free modes span a dense set in L²_σ [analytic content];
--   discharge milestone: M3 (Galerkin P_n + Leray projection).
--   Reference: Temam, "Navier–Stokes Equations", Proposition 1.1 and Corollary 1.1.
```

No other new axioms are needed for M2 if the remaining items are left as
scaffold-only or marked sorry.

---

## 8. Sorry frontier for M2

| ID | Location | Content | Blocker |
|---|---|---|---|
| S-M2-01 | `TorusFourier.lean`, D-14 | `fourierProjection_n_tendsto` | D-13 Finset definition |
| S-M2-02 | `FunctionSpaces.lean`, D-06 | measure mismatch check `haarAddCircle` vs `measureSpace` at T=1 | lean-coder verification |

Both must carry `-- ALLOW_SORRY: <blocker>` and be tracked in `STATUS.md`.

---

## 9. Codex review points

The following new statements should receive `/codex:adversarial-review --effort xhigh`
before proofs are attempted:

1. **D-08 (`DivFreeL2`)** — the Fourier characterization of divergence-free is
   the mathematical core of M2; the statement must be validated before building on it.
2. **D-09 (`L2SigmaSubspace`)** — the closure-of-span definition must be checked
   for correctness and coherence with the intended mathematics.
3. **D-06 (`torus3_mFourierBasis`)** — the measure normalization issue (D-06 caveat)
   should be adversarially checked.
4. **`L2Sigma_eq_divFreeL2` axiom** — validate that this axiom is (a) mathematically
   correct and (b) not secretly vacuous or trivial given the current definitions.

---

## 10. Definition of done for M2

M2 is done when:

1. `lake build` passes.
2. `Torus3` is realized as `UnitAddTorus (Fin 3)` with the product Haar measure.
3. The three `example` instance checks in D-02 typecheck without sorry.
4. `L2VF` and `L2C` elaborate with `InnerProductSpace` and `CompleteSpace` instances.
5. `torus3_mFourierBasis` compiles sorry-free.
6. `DivFreeL2` and `L2SigmaSubspace` are defined (scaffold bodies permitted).
7. `H1Torus` is defined (scaffold).
8. `L2Sigma_eq_divFreeL2` axiom is placed with proper `ALLOW_AXIOM` marker.
9. All sorry entries are marked and entered in `STATUS.md`.
10. `lean-planner` updates `STATUS.md` milestone row M2 to `in progress` → `done`.

---

## 11. Recommended first task for lean-coder

**Task 1 (lean-coder):** Edit `Basic.lean` to replace the `Torus3` placeholder
(D-01). This is a 5-line change. The change is:
1. Replace `def Torus3 : Type := PUnit` with `abbrev Torus3 := UnitAddTorus (Fin 3)`.
2. Remove the manual `MeasureSpace Torus3` instance.
3. Add the required imports.
4. Run `lake build`; the existing M1 files must still compile (they use `Torus3` as
   a type parameter only, with no dependence on the specific type).

If the build is green after this change, proceed to D-02 (instance checks) and
D-03–D-05 (type aliases). Flag the `haarAddCircle` vs `measureSpace` issue (D-06
caveat) immediately if the instance check fails.

**Task 2 (lean-coder, parallel):** Open `LerayHopf/FunctionSpaces.lean` and
write D-04 (`L2VF`) and D-05 (`L2C`) as `abbrev`s. Verify the `InnerProductSpace`
and `CompleteSpace` instance checks elaborate.

These two tasks together form the minimum M2 footprint that unblocks Codex review
of D-06 and D-08.
