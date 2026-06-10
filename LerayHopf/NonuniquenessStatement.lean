import LerayHopf.Basic

open MeasureTheory

/-!
# Non-uniqueness statement (Branch B scaffold)

**Scaffold only — statement only.** States the non-uniqueness proposition for the
Leray–Hopf class: the existence of an initial datum `u₀` admitting two distinct
solutions. No proof obligation at this milestone.

The definition is universe-polymorphic: `Ω : Type u` is the spatial domain and the
initial-datum type `u₀ : Type v` ranges over an independent universe, keeping the API
monotone with `LerayHopfSolution (u₀ : Type*)`.

Interface authority: `docs/scratch/m1-structural-spine.md` (Branch B).
-/

universe u v

namespace LerayHopf

/-- (Branch B non-uniqueness statement, scaffold only)
Non-uniqueness in the Leray–Hopf class on `Ω`: there exists an initial datum type
`u₀` (in universe `v`) admitting two distinct solutions. -/
def LerayHopfNonunique (Ω : Type u) [MeasureSpace Ω] : Prop :=
  ∃ u₀ : Type v, ∃ p q : LerayHopfSolution Ω u₀, p ≠ q

end LerayHopf
