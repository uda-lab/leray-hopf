# Lean formalization MVP plan for Leray--Hopf weak existence

## Aim

Formalize the first tractable part of the Leray--Hopf weak existence project:

\[
\text{Galerkin compactness package} \Longrightarrow
\exists u,\; u \text{ is a Leray--Hopf solution}.
\]

This MVP deliberately avoids proving the PDE estimates, compactness theorem, and Fourier--Galerkin construction.  The goal is to fix the Lean interface and prove the purely structural implication.

> **Authority.**  This file is the authoritative interface design for the MVP
> (`milestone.md` Milestones 1–4).  Where `milestone.md` sketches different field names or
> signatures (e.g. its `GalerkinCompactnessPackage` with an `approx` field instead of a
> `limit` field), this file wins; those sketches describe the post-MVP refinement direction.

## Scope

Target domain:

\[
\Omega = \mathbb T^3
\]

but the first files should be domain-parametric when possible.

Out of scope for the first MVP:

- full construction of Galerkin approximations,
- Aubin--Lions theorem,
- Bochner space development,
- pressure recovery,
- \(\mathbb R^3\) version,
- Hou--Wang--Yang nonuniqueness.

## File layout

```text
LerayHopf/
  Basic.lean
  Statement.lean
  GalerkinPackage.lean
  ExistenceFromPackage.lean
  EnergySkeleton.lean
```

### Scaffold designation

| File | Status |
|---|---|
| `Basic.lean`, `Statement.lean`, `GalerkinPackage.lean` | **scaffold-only** — placeholder types, `Prop` fields, and marked `sorry` are allowed. These are the `AGENTS.md` Rule 4 exception files. |
| `ExistenceFromPackage.lean`, `EnergySkeleton.lean` | **must-prove** — sorry-free required. |

`exists_lerayHopf_torus3_statement` must stay
`sorry -- ALLOW_SORRY: target statement; do NOT discharge while definitions are placeholders`
while the definitions are placeholders.  Giving it a proof while the underlying definitions
are still vacuous is treated as a **No-vacuous-proof** violation, not progress.

## Milestone A: Basic objects

File:

```text
LerayHopf/Basic.lean
```

Define abstract types first.

```lean
namespace LerayHopf

variable (Ω : Type*) [MeasureSpace Ω]

abbrev Time := ℝ

structure SpatialField (Ω : Type*) where
  carrier : Type*
  dummy : True := by trivial
```

In the first MVP, `SpatialField` can be a placeholder.  The point is not to encode \(L^2_\sigma\) yet.

For the MVP, `Torus3` is declared as a **placeholder type in `Basic.lean`** — e.g. an
abbreviation around a dummy type carrying a `MeasureSpace` instance, with
`-- TODO: realized in Milestone 5`.  Realizing it via mathlib's `AddCircle` is Milestone 5
work and must not be anticipated here.  `L2Sigma` does **not** appear in the MVP at all.

Define the solution concept.

```lean
structure LerayHopfSolution
  (Ω : Type*) [MeasureSpace Ω]
  (u₀ : Type*) where
  u : Time → Type*
  weak_eq : Prop
  divergence_free : Prop
  energy_class : Prop
  initial_trace : Prop
  energy_inequality : Prop
```

This is intentionally skeletal.  It gives us a target type for existence theorems.

Expected proof burden: none.

## Milestone B: Statement layer

File:

```text
LerayHopf/Statement.lean
```

Define the existence proposition.

```lean
def ExistsLerayHopf
  (Ω : Type*) [MeasureSpace Ω]
  (u₀ : Type*) : Prop :=
  Nonempty (LerayHopfSolution Ω u₀)
```

Then create named theorem statements.

```lean
theorem exists_lerayHopf_torus3_statement
  (u₀ : Type*) :
  ExistsLerayHopf Torus3 u₀ := by
  -- not proved in MVP
  sorry -- ALLOW_SORRY: target statement; do NOT discharge while definitions are placeholders
```

This file may contain `sorry`; it is only the target statement.

Expected proof burden: none, except checking that the statement elaborates.

## Milestone C: Galerkin package

File:

```text
LerayHopf/GalerkinPackage.lean
```

Define a package that already contains a candidate limit and all properties needed to declare it a Leray--Hopf solution.

```lean
structure GalerkinCompactnessPackage
  (Ω : Type*) [MeasureSpace Ω]
  (u₀ : Type*) where
  limit : Time → Type*
  weak_eq_limit : Prop
  divergence_free_limit : Prop
  energy_class_limit : Prop
  initial_trace_limit : Prop
  energy_inequality_limit : Prop
```

This is the key MVP trick: compactness and limit passage are not proved yet, but their conclusions are stored as fields.

Expected proof burden: none.

## Milestone D: Structural existence proof

File:

```text
LerayHopf/ExistenceFromPackage.lean
```

Prove:

```lean
theorem exists_lerayHopf_from_galerkin_package
  {Ω : Type*} [MeasureSpace Ω]
  {u₀ : Type*}
  (pkg : GalerkinCompactnessPackage Ω u₀) :
  ExistsLerayHopf Ω u₀ := by
  exact ⟨{
    u := pkg.limit
    weak_eq := pkg.weak_eq_limit
    divergence_free := pkg.divergence_free_limit
    energy_class := pkg.energy_class_limit
    initial_trace := pkg.initial_trace_limit
    energy_inequality := pkg.energy_inequality_limit
  }⟩
```

This should be sorry-free.

This is the first concrete proof.

## Milestone E: Nontrivial but still small proof: energy inequality wrapper

File:

```text
LerayHopf/EnergySkeleton.lean
```

Formalize a purely abstract energy inequality, without PDE.

Define:

```lean
structure EnergyData where
  E : ℝ → ℝ
  D : ℝ → ℝ
  ν : ℝ
```

Define:

```lean
def EnergyInequality (ed : EnergyData) : Prop :=
  ∀ s t : ℝ, 0 ≤ s → s ≤ t →
    ed.E t + ed.ν * ∫ τ in s..t, ed.D τ ≤ ed.E s
```

**Decision (not a choice left to implementation):** the MVP uses the abstract
accumulated-dissipation `A : ℝ → ℝ → ℝ` version below.  Replacing it with the
interval-integral version above is PR 2+ refinement, not first-pass work.

```lean
structure EnergyData where
  E : ℝ → ℝ
  A : ℝ → ℝ → ℝ
  ν : ℝ

def EnergyInequality (ed : EnergyData) : Prop :=
  ∀ s t : ℝ, 0 ≤ s → s ≤ t →
    ed.E t + ed.ν * ed.A s t ≤ ed.E s
```

Then prove simple consequences.

Example:

```lean
theorem energy_nonincreasing_from_nonnegative_dissipation
  (ed : EnergyData)
  (hE : EnergyInequality ed)
  (hν : 0 ≤ ed.ν)
  (hA : ∀ s t, 0 ≤ s → s ≤ t → 0 ≤ ed.A s t) :
  ∀ s t, 0 ≤ s → s ≤ t → ed.E t ≤ ed.E s := by
  intro s t hs hst
  have h := hE s t hs hst
  have hnonneg : 0 ≤ ed.ν * ed.A s t := mul_nonneg hν (hA s t hs hst)
  linarith
```

This is a good second proof target.  It checks that the formalization is not merely a collection of records.

## Milestone F: Blow-up lower bound as a separate small theorem

Optional but useful.

File:

```text
Leray/BlowupLowerBound.lean
```

Prove the abstract algebraic implication:

\[
T-t \le C N(t)^{-\alpha}
\quad\Rightarrow\quad
N(t)\ge c (T-t)^{-1/\alpha}.
\]

For the first pass, avoid real powers and use a simplified positive integer exponent version.

Example first theorem:

```lean
theorem lower_bound_from_inverse_square_lifespan
  (N : ℝ → ℝ)
  (T C : ℝ)
  (hC : 0 < C)
  (hNpos : ∀ t, t < T → 0 < N t)
  (h : ∀ t, t < T → T - t ≤ C / (N t)^2) :
  ∀ t, t < T → Real.sqrt ((T - t) / C) ≤ 1 / N t := by
  ...
```

This may need more real-analysis API.  It is optional for the first MVP.

## Recommended first PR

A minimal first PR should include only:

```text
LerayHopf/Basic.lean
LerayHopf/GalerkinPackage.lean
LerayHopf/ExistenceFromPackage.lean
LerayHopf/EnergySkeleton.lean
```

with the following sorry-free theorems:

1. `exists_lerayHopf_from_galerkin_package`
2. `energy_nonincreasing_from_nonnegative_dissipation`

This is small, but it fixes the architectural spine.

`Statement.lean` (with `exists_lerayHopf_torus3_statement` kept as the marked `sorry`
above) is part of the first MVP and lands in this PR or the immediately following one, so
that the Definition of done's "main future theorem statement exists" holds.  The four-file
list above is the strict subset that must be **sorry-free**; `Statement.lean` is not.

## Follow-up PRs

### PR 2: refine fields

Replace `Type*` placeholders with abstract normed spaces:

```lean
variable (H V : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
```

Interpret:

\[
H = L^2_\sigma,\qquad V = H^1_\sigma.
\]

Viscosity positivity decision: keep `0 < ν` (or `0 ≤ ν`) as a **hypothesis on the energy
lemmas**, as `EnergySkeleton` already does, rather than baking it into a structure field —
unless a later estimate genuinely needs it structurally.

### PR 3: finite-dimensional Galerkin ODE interface

Define a finite-dimensional approximation package:

```lean
structure GalerkinApproximation where
  Vn : Type*
  finite_dimensional : Prop
  uₙ : Time → Vn
  ode_holds : Prop
  energy_identity : Prop
```

### PR 4: actual energy cancellation statement

Add an abstract trilinear form \(b(u,v,w)\) and assume skew-symmetry:

\[
b(u,u,u)=0.
\]

Prove that this gives the Galerkin energy identity.

### PR 5: compactness axiom interface

Introduce:

```lean
structure NSCompactnessTheorem where
  compactness : Prop
  limit_passage : Prop
  lower_semicontinuity : Prop
```

Then connect it to `GalerkinCompactnessPackage`.

## Design rule

Do not encode false precision too early.

In particular, avoid pretending that we already have mature Lean definitions of:

- \(L^\infty_t L^2_x\),
- \(L^2_t H^1_x\),
- divergence-free Sobolev spaces on \(\mathbb T^3\),
- weak Navier--Stokes equation,
- pressure recovery.

Use placeholders first, but make the names mathematically correct and refine them monotonically.

## Definition of done for the first MVP

The first MVP is done when:

- the project compiles,
- `exists_lerayHopf_from_galerkin_package` is sorry-free,
- `energy_nonincreasing_from_nonnegative_dissipation` is sorry-free,
- the main future theorem statement exists,
- all remaining PDE-heavy assumptions are explicitly packaged rather than hidden.
