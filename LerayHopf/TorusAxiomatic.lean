import LerayHopf.AxiomaticClosure
import LerayHopf.TorusConvectionForm
import LerayHopf.TorusGalerkinODECapstone

/-!
# LerayHopf.TorusAxiomatic — axiomatic closure for 𝕋³

This module re-exports the full axiomatic closure of the Torus³ Leray–Hopf
existence argument.  The capstone declaration is:

    `LerayHopf.exists_lerayHopf_torus3_axiomatic`

(relocated to `LerayHopf/TorusGalerkinODECapstone.lean` in issue #24), which depends on **zero
project axioms** — KERNEL-ONLY.  All former project axioms removed:
- `galerkin_ode_solution` removed (issue #24)
- `torusConvectionGap_exists` removed (issue #53/PR #62)
- `galerkin_limit_passage` removed (issue #25/PR #75)
- `aubin_lions` removed (issue #23); proved as `torusAubinLionsPackage_of_galSeq`

The former `galerkin_ode_solution` axiom (Picard–Lindelöf on finite-dim Vₙ) has been **removed**
(issue #24): the finite-dim torus Galerkin ODE is now solved unconditionally by the proved
`galerkinSolutionData_torus` (`LerayHopf/TorusGalerkinODESolve.lean`), over the finite-dim
`velocitySpan n`, and the capstone is rerouted through it via `galSeq_of_torus`.

The former `torusConvectionGap_exists` axiom has also been **removed** (issue #53 / PR #62):
it is now the proved theorem `torusConvectionGap_exists`, re-exporting
`TorusConvectionExtension.torusConvectionGap_holds`.  The resulting convection form is a
proof-carrying total trilinear extension pinned to the finite Fourier/Galerkin test-class
form and continuous in the two solution slots at fixed Galerkin tests; it is not a claim of a
canonical continuous operator on all pure `L² × L² × L²` triples.

Import this module ONLY when you need the axiom-dependent results.
For axiom-free work, use `import LerayHopf.Core`.
-/
