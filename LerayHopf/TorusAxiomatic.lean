import LerayHopf.AxiomaticClosure

/-!
# LerayHopf.TorusAxiomatic — axiomatic closure for 𝕋³

This module re-exports the full axiomatic closure of the Torus³ Leray–Hopf
existence argument.  The capstone declaration is:

    `LerayHopf.exists_lerayHopf_torus3_axiomatic`

which depends on four project axioms:
- `torus3_NSForms_exist` (AX-1): T³ NS convection form exists
- `galerkin_ode_solution` (AX-2): Picard–Lindelöf on finite-dim Vₙ
- `aubin_lions` (AX-3): Aubin–Lions time compactness (spatial half proved)
- `galerkin_limit_passage` (AX-4): limit passage to weak NS solution

Import this module ONLY when you need the axiom-dependent results.
For axiom-free work, use `import LerayHopf.Core`.
-/
