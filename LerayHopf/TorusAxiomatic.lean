import LerayHopf.AxiomaticClosure
import LerayHopf.TorusConvectionForm

/-!
# LerayHopf.TorusAxiomatic — axiomatic closure for 𝕋³

This module re-exports the full axiomatic closure of the Torus³ Leray–Hopf
existence argument.  The capstone declaration is:

    `LerayHopf.exists_lerayHopf_torus3_axiomatic`

(defined in `LerayHopf/TorusConvectionForm.lean` since issue #22), which depends on four project
axioms:
- `torusConvectionGap_exists` (AX-1): the thin torus weak-convection-operator gap — replaces the
  removed fat `torus3_NSForms_exist` (issue #22); the trilinear algebra, the L²-bound transfer,
  and the Galerkin pin are now theorem content via `Torus3NSForms_of_gap`
- `galerkin_ode_solution` (AX-2): Picard–Lindelöf on finite-dim Vₙ
- `aubin_lions` (AX-3): Aubin–Lions time compactness (spatial half proved)
- `galerkin_limit_passage` (AX-4): limit passage to weak NS solution

Import this module ONLY when you need the axiom-dependent results.
For axiom-free work, use `import LerayHopf.Core`.
-/
