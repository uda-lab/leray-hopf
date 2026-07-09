import LerayHopf.Torus.Basic

open MeasureTheory

/-!
# The Leray–Hopf existence statement

**Scaffold only.** Defines the existence proposition `ExistsLerayHopf` and the named
target theorem on the (placeholder) torus. The target carries a *marked* `sorry`: it is
the goal of the whole project, and it must **not** be discharged while the underlying
definitions in `Basic.lean` are still placeholders (doing so would be a No-vacuous-proof
violation, not progress).

Interface authority: `docs/leray_hopf_lean_mvp_plan.md` (Milestone B).
-/

namespace LerayHopf

/-- Existence of a Leray–Hopf weak solution on the domain `Ω` for initial datum `u₀`.

**Scaffold caveat (No-overclaim).** At this milestone `LerayHopfSolution`'s analytical
fields are free `Prop` placeholders, so `ExistsLerayHopf` is *structurally* inhabited
(e.g. by a record whose `Prop` fields are all `True`). It is therefore **not yet a
meaningful existence assertion**. It becomes one only as the placeholder fields are
refined (M2+) into real predicates tied to the candidate field, `u₀`, and `Ω`. Do not
read a proof of `ExistsLerayHopf Ω u₀` as Leray–Hopf existence while the placeholders
stand; see `docs/STATUS.md` ("Known scaffold caveats"). -/
def ExistsLerayHopf (Ω : Type*) [MeasureSpace Ω] (u₀ : Type*) : Prop :=
  Nonempty (LerayHopfSolution Ω u₀)

/-- **Target statement.** Existence of a Leray–Hopf weak solution on `𝕋³`.

Intentionally left as a marked `sorry`: this is what the project aims to prove, and it
is dishonest to close it while `LerayHopfSolution`'s fields are placeholders. -/
theorem exists_lerayHopf_torus3_statement (u₀ : Type*) :
    ExistsLerayHopf Torus3 u₀ := by
  sorry -- ALLOW_SORRY: target statement; do NOT discharge while definitions are placeholders

end LerayHopf
