import LerayHopf.Statement
import LerayHopf.GalerkinPackage

open MeasureTheory

/-!
# Structural existence from a Galerkin compactness package

**Must-prove, sorry-free.** The first concrete theorem of the project: a
`GalerkinCompactnessPackage` yields a Leray–Hopf solution. This is the purely structural
implication

  Galerkin compactness package  ⟹  ∃ Leray–Hopf solution,

with no analysis — it just reassembles the packaged conclusions into the solution record.

Interface authority: `docs/leray_hopf_lean_mvp_plan.md` (Milestone D).
-/

namespace LerayHopf

/-- From a `GalerkinCompactnessPackage` for `u₀` on `Ω`, a Leray–Hopf solution exists.

Purely structural: the package's stored conclusions become the solution's fields. The
content is the *implication* (package ⟹ solution), which is honest and stable under
refinement. Its conclusion `ExistsLerayHopf` is only as strong as the package fields,
which are placeholders at this milestone (see `ExistsLerayHopf`'s scaffold caveat and
`docs/STATUS.md`); the implication is not an unconditional existence claim. -/
theorem exists_lerayHopf_from_galerkin_package
    {Ω : Type*} [MeasureSpace Ω] {u₀ : Type*}
    (pkg : GalerkinCompactnessPackage Ω u₀) :
    ExistsLerayHopf Ω u₀ :=
  ⟨{ u := pkg.limit
     weak_eq := pkg.weak_eq_limit
     divergence_free := pkg.divergence_free_limit
     energy_class := pkg.energy_class_limit
     initial_trace := pkg.initial_trace_limit
     energy_inequality := pkg.energy_inequality_limit }⟩

end LerayHopf
