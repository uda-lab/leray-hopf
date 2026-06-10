# M1 task contract — structural spine

Executable contract for Milestone 1 (the MVP structural spine). Interface authority:
`docs/leray_hopf_lean_mvp_plan.md` (Milestones A–F). Roadmap: `docs/milestone.md` (M1–4).
Rules: `AGENTS.md`, `docs/guardrails.md`.

## Files, declarations, ownership (dependency order)

### `LerayHopf/Basic.lean` — **scaffold-only**
- `Time := ℝ` (abbrev).
- `Torus3` — **placeholder** type carrying a `MeasureSpace` instance.
  `-- TODO: realized via UnitAddTorus 3 in M2`. Do NOT use `AddCircle` here.
- `structure SpatialField (Ω : Type*)` — placeholder (`carrier : Type*`, `dummy : True`).
- `structure LerayHopfSolution (Ω) [MeasureSpace Ω] (u₀ : Type*)` with fields
  `u : Time → Type*`, and `weak_eq / divergence_free / energy_class / initial_trace /
  energy_inequality : Prop`. Skeletal; gives a target type.
- Proof burden: none.

### `LerayHopf/Statement.lean` — **scaffold-only** (carries the one target marked sorry)
- `def ExistsLerayHopf (Ω) [MeasureSpace Ω] (u₀ : Type*) : Prop := Nonempty (LerayHopfSolution Ω u₀)`.
- `theorem exists_lerayHopf_torus3_statement (u₀ : Type*) : ExistsLerayHopf Torus3 u₀`
  := `sorry -- ALLOW_SORRY: target statement; do NOT discharge while definitions are placeholders`.
- Depends on Basic.

### `LerayHopf/GalerkinPackage.lean` — **scaffold-only**
- `structure GalerkinCompactnessPackage (Ω) [MeasureSpace Ω] (u₀ : Type*)` with fields
  `limit : Time → Type*`, `weak_eq_limit / divergence_free_limit / energy_class_limit /
  initial_trace_limit / energy_inequality_limit : Prop`. (MVP plan field names — `limit`,
  not `approx`; the MVP plan wins over milestone.md's sketch.)
- Depends on Basic.

### `LerayHopf/ExistenceFromPackage.lean` — **must-prove, sorry-free**
- `theorem exists_lerayHopf_from_galerkin_package {Ω} [MeasureSpace Ω] {u₀}
  (pkg : GalerkinCompactnessPackage Ω u₀) : ExistsLerayHopf Ω u₀` — build the solution
  from the package fields (structural). **Sorry-free.** First concrete proof.
- Depends on Basic, Statement, GalerkinPackage.

### `LerayHopf/EnergySkeleton.lean` — **must-prove, sorry-free**
- `structure EnergyData` with `E : ℝ → ℝ`, `A : ℝ → ℝ → ℝ`, `ν : ℝ` (accumulated-dissipation
  version — the MVP plan Decision).
- `def EnergyInequality (ed : EnergyData) : Prop :=
  ∀ s t, 0 ≤ s → s ≤ t → ed.E t + ed.ν * ed.A s t ≤ ed.E s`.
- `theorem energy_nonincreasing_from_nonnegative_dissipation (ed) (hE : EnergyInequality ed)
  (hν : 0 ≤ ed.ν) (hA : ∀ s t, 0 ≤ s → s ≤ t → 0 ≤ ed.A s t) :
  ∀ s t, 0 ≤ s → s ≤ t → ed.E t ≤ ed.E s` — **sorry-free** (`mul_nonneg` + `linarith`).
- Independent of the package files (only needs `ℝ`).

### `LerayHopf/BlowupLowerBound.lean` — **must-prove, sorry-free** (Branch A, independent)
- `theorem lower_bound_from_inverse_square_lifespan (N : ℝ → ℝ) (T C : ℝ) (hC : 0 < C)
  (hNpos : ∀ t, t < T → 0 < N t) (h : ∀ t, t < T → T - t ≤ C / (N t)^2) :
  ∀ t, t < T → Real.sqrt ((T - t) / C) ≤ 1 / N t`. Real-analysis; sorry-free if it lands,
  else marked sorry with blocker. Optional for the spine PR.

### `LerayHopf/NonuniquenessStatement.lean` — **scaffold-only** (Branch B, statement only)
- `def LerayHopfNonunique (Ω) [MeasureSpace Ω] : Prop :=
  ∃ u₀ : Type*, ∃ u v : LerayHopfSolution Ω u₀, u ≠ v`. Statement only; no proof obligation.
  Uses placeholder domain (R3 placeholder or Ω-parametric). Depends on Basic.

### Root wiring
- `LerayHopf.lean` imports the submodules (keep the scaffold docstring).

## Codex adversarial-review points (statements are the contract)
- `LerayHopf/Basic.lean` — `LerayHopfSolution` shape.
- `LerayHopf/Statement.lean` — `ExistsLerayHopf` + target statement.
- `LerayHopf/GalerkinPackage.lean` — package fields.
- `LerayHopf/ExistenceFromPackage.lean` — the structural theorem statement.
- `LerayHopf/EnergySkeleton.lean` — energy inequality def + monotonicity statement.

## Definition of done (M1)
- Project compiles (`lake build` green).
- `exists_lerayHopf_from_galerkin_package` sorry-free.
- `energy_nonincreasing_from_nonnegative_dissipation` sorry-free.
- Target statement `exists_lerayHopf_torus3_statement` exists (marked sorry).
- All PDE-heavy content packaged (no hidden assumptions); only the one target sorry +
  scaffold placeholders. No unmarked sorry/axiom; guardrails green.

## First lean-coder task
Create `LerayHopf/Basic.lean` with the placeholder types and `LerayHopfSolution`, wire it
into the root, build green. Then Statement → GalerkinPackage → ExistenceFromPackage →
EnergySkeleton in dependency order.
