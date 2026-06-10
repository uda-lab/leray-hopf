/-
# LerayHopf

Root module for the Leray–Hopf weak-existence formalization project.

This is **scaffold only**. The mathematical scope — solution concept, existence
statement, Galerkin compactness package, energy skeleton — is specified in:

* `docs/milestone.md`            (roadmap)
* `docs/leray_hopf_lean_mvp_plan.md` (MVP design and file layout)

Those plan files are the source of truth for mathematical content. No definitions
or theorems are declared yet; they are introduced in later, reviewed PRs under the
`LerayHopf/` namespace (e.g. `LerayHopf.Basic`, `LerayHopf.GalerkinPackage`).

No claim is made that existence, regularity, uniqueness, or nonuniqueness of the
Navier–Stokes equations has been formalized.
-/
