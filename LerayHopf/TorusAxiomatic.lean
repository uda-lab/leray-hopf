import LerayHopf.AxiomaticClosure
import LerayHopf.TorusConvectionForm
import LerayHopf.TorusGalerkinODECapstone

/-!
# LerayHopf.TorusAxiomatic — axiomatic closure for 𝕋³

This module re-exports the full axiomatic closure of the Torus³ Leray–Hopf
existence argument.  The capstone declaration is:

    `LerayHopf.exists_lerayHopf_torus3_axiomatic`

(relocated to `LerayHopf/TorusGalerkinODECapstone.lean` in issue #24), which depends on three
project axioms:
- `torusConvectionGap_exists` (AX-1): the thin torus weak-convection-operator gap — replaces the
  removed fat `torus3_NSForms_exist` (issue #22); the trilinear algebra, the L²-bound transfer,
  and the Galerkin pin are now theorem content via `Torus3NSForms_of_gap`
- `aubin_lions` (AX-2): Aubin–Lions time compactness (spatial half proved)
- `galerkin_limit_passage` (AX-3): limit passage to weak NS solution

The former `galerkin_ode_solution` axiom (Picard–Lindelöf on finite-dim Vₙ) has been **removed**
(issue #24): the finite-dim torus Galerkin ODE is now solved unconditionally by the proved
`galerkinSolutionData_torus` (`LerayHopf/TorusGalerkinODESolve.lean`), over the finite-dim
`velocitySpan n`, and the capstone is rerouted through it via `galSeq_of_torus`.

Import this module ONLY when you need the axiom-dependent results.
For axiom-free work, use `import LerayHopf.Core`.
-/
