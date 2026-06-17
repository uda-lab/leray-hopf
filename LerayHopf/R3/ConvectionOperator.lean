import LerayHopf.R3.TrilinearEstimate
import LerayHopf.R3.Regularity

/-!
# Tier S — Axiom-free partial convection form on the Schwartz-div-free class (ℝ³)

**Milestone / stream:** `stream-c-convection-operator` (Tier S).

This file lifts the R3-d Schwartz-level trilinear estimates
(`LerayHopf/R3/TrilinearEstimate.lean`) to the *operator level*: a genuine,
axiom-free convection functional defined on fields of `L2Sigma_R3` that carry a
component-wise Schwartz representative (the `IsSchwartzDivFree_R3` class).

It does **not** mention `R3NSForms` (that conditional assembly lives in the sibling
`LerayHopf/R3/ConvectionForm.lean`, which imports `AxiomaticClosure.lean`).

## Why a *partial* form, not a total one

The trilinear convection form `b(u,v,w) = ∫(u·∇)v·w` is **unbounded in pure
L²×L²×L² norms** (R3-d's bound `convIntegralSchwartz_bound_sup` needs an L∞ slot for
`∇w`). So `b` does **not** extend continuously from Schwartz triples to all of
`L²_σ × L²_σ × L²_σ` by density: there is no continuous-extension shortcut. The genuine
*total* operator requires the missing weak-`(u·∇)v` calculus on `Lp` (isolated as
`ConvectionGap` in `ConvectionForm.lean`). What is honestly available — and proved here
— is the convection functional on the Schwartz-representable class, transported from
R3-d through the `IsSchwartzDivFree_R3` witnesses.

## Declarations (dependency order)

- `convFormSchwartzWitness`     : the R3-d value on explicit Schwartz witnesses (a `def`).
- `convFormSchwartz_witness_wd` : well-definedness — equal `toLp` classes ⇒ equal value.
- `convFormSchwartz`            : the well-defined functional on the `IsSchwartzDivFree_R3`
                                   class (via `Exists.choose` + well-definedness).
- `convFormSchwartz_eq_witness` : `convFormSchwartz` agrees with any chosen witness.
- `convFormSchwartz_add_{1,2,3}`  : additivity in each slot (transport of R3-d A1–A3).
- `convFormSchwartz_smul_{1,2,3}` : ℝ-homogeneity in each slot (transport of R3-d A4–A6).
- `convFormSchwartz_antisymm`   : antisymmetry in the last two slots on the div-free class
                                   (transport of R3-d `convIntegralSchwartz_antisymm_of_divFree`).
- `convFormSchwartz_bound`      : the `b_bound` shape `|b u v w| ≤ C(w)·‖u‖·‖v‖`
                                   (transport of R3-d `convIntegralSchwartz_bound_sup`).

## Scaffold status

Proof bodies are placeholder this pass (Tier S is sorry-free in the final milestone);
every obligation carries an `ALLOW_SORRY` marker naming the precise blocker.
**No new `axiom`/`opaque`/`constant`.**
-/

namespace LerayHopf
open MeasureTheory LineDeriv SchwartzMap

/-! ### S1 — The R3-d value on explicit Schwartz witnesses -/

/-- **S1.** The convection value `∫(u·∇)v·w` on *explicit* Schwartz component witnesses.

Given `u v w : L2Sigma_R3` together with component-wise Schwartz representatives
`ψu ψv ψw` (the data exposed by `IsSchwartzDivFree_R3`), this is just the genuine
`convIntegralSchwartz` of those representatives.  It is a thin wrapper recording the
intended dependency on the *fields* `u v w` (through their witnesses); the genuine
field-level functional `convFormSchwartz` below quotients out the choice of witness via
well-definedness (S2). -/
noncomputable def convFormSchwartzWitness
    (ψu ψv ψw : Fin 3 → SchwartzMap Domain3 ℝ) : ℝ :=
  convIntegralSchwartz ψu ψv ψw

/-! ### S2 — Well-definedness: equal `toLp` classes give equal value -/

/-- **S2.** Well-definedness of the convection value in the Schwartz witnesses.

If two Schwartz tuples represent the same `L²` classes component-wise (equal `toLp 2`),
then `convIntegralSchwartz` returns the same value.  This is the a.e.-class determinacy
of the Schwartz integral: each factor enters `convIntegralSchwartz` only through an
integral that is determined by the a.e. class of the factor, so equal `toLp 2` ⇒ equal
integrand a.e. ⇒ equal integral.  Needed because `IsSchwartzDivFree_R3` exposes *some*
witness, not a canonical one. -/
theorem convFormSchwartz_witness_wd
    (ψu ψu' ψv ψv' ψw ψw' : Fin 3 → SchwartzMap Domain3 ℝ)
    (hu : ∀ j : Fin 3, (ψu j).toLp 2 (volume : Measure Domain3)
            = (ψu' j).toLp 2 (volume : Measure Domain3))
    (hv : ∀ j : Fin 3, (ψv j).toLp 2 (volume : Measure Domain3)
            = (ψv' j).toLp 2 (volume : Measure Domain3))
    (hw : ∀ j : Fin 3, (ψw j).toLp 2 (volume : Measure Domain3)
            = (ψw' j).toLp 2 (volume : Measure Domain3)) :
    convIntegralSchwartz ψu ψv ψw = convIntegralSchwartz ψu' ψv' ψw' := by
  sorry -- ALLOW_SORRY: scaffold (Tier S, stream-c-convection-operator); a.e.-class determinacy of convIntegralSchwartz — equal toLp 2 classes give a.e.-equal Schwartz factors (SchwartzMap.coeFn_toLp + toLp injectivity on classes), whence equal integrands a.e. and equal Bochner integrals via integral_congr_ae; one genuinely new (medium) lemma, proved by lean-prover

/-! ### S3 — The field-level functional on the Schwartz-div-free class -/

/-- **S3.** The well-defined convection functional on the `IsSchwartzDivFree_R3` class.

Given `u v w : L2Sigma_R3` each carrying a Schwartz component representative
(`IsSchwartzDivFree_R3`), the value is `convIntegralSchwartz` of the *chosen* witnesses.
Independence of the choice is `convFormSchwartz_witness_wd` (S2): different witnesses for
the same field have equal `toLp 2` classes, hence equal value.  This is the genuine
field-level convection functional on a dense class of `L²_σ(ℝ³)`. -/
noncomputable def convFormSchwartz
    (u v w : L2Sigma_R3)
    (hu : IsSchwartzDivFree_R3 u) (hv : IsSchwartzDivFree_R3 v)
    (hw : IsSchwartzDivFree_R3 w) : ℝ :=
  convIntegralSchwartz hu.choose hv.choose hw.choose

/-- **S3'.** `convFormSchwartz` agrees with the value on *any* Schwartz witness tuple
representing the same fields.  This is the user-facing computation rule: it lets one
replace the (opaque) chosen witnesses by any explicit Schwartz representatives. -/
theorem convFormSchwartz_eq_witness
    (u v w : L2Sigma_R3)
    (hu : IsSchwartzDivFree_R3 u) (hv : IsSchwartzDivFree_R3 v)
    (hw : IsSchwartzDivFree_R3 w)
    (ψu ψv ψw : Fin 3 → SchwartzMap Domain3 ℝ)
    (hψu : ∀ j : Fin 3, L2VF_projComponent_R3 j (u : L2VF_R3)
            = (ψu j).toLp 2 (volume : Measure Domain3))
    (hψv : ∀ j : Fin 3, L2VF_projComponent_R3 j (v : L2VF_R3)
            = (ψv j).toLp 2 (volume : Measure Domain3))
    (hψw : ∀ j : Fin 3, L2VF_projComponent_R3 j (w : L2VF_R3)
            = (ψw j).toLp 2 (volume : Measure Domain3)) :
    convFormSchwartz u v w hu hv hw = convIntegralSchwartz ψu ψv ψw := by
  sorry -- ALLOW_SORRY: scaffold (Tier S); apply convFormSchwartz_witness_wd (S2) to the chosen witnesses (hu.choose_spec etc.) vs ψu ψv ψw — both equal the same L2VF_projComponent_R3 j classes, so equal toLp 2; proved by lean-prover

/-! ### S4–S9 — Multilinearity (transport of R3-d A1–A6) -/

/-- **S4.** Additivity of `convFormSchwartz` in the first slot, on the div-free class. -/
theorem convFormSchwartz_add_1
    (u u' v w : L2Sigma_R3)
    (hu : IsSchwartzDivFree_R3 u) (hu' : IsSchwartzDivFree_R3 u')
    (huu' : IsSchwartzDivFree_R3 (u + u'))
    (hv : IsSchwartzDivFree_R3 v) (hw : IsSchwartzDivFree_R3 w) :
    convFormSchwartz (u + u') v w huu' hv hw
      = convFormSchwartz u v w hu hv hw + convFormSchwartz u' v w hu' hv hw := by
  sorry -- ALLOW_SORRY: scaffold (Tier S); transport R3-d convIntegralSchwartz_add_1 through convFormSchwartz_eq_witness (S3'); the component of (u+u') is the sum of components, so its Schwartz witness is the slot-wise sum; proved by lean-prover

/-- **S5.** Additivity of `convFormSchwartz` in the second slot, on the div-free class. -/
theorem convFormSchwartz_add_2
    (u v v' w : L2Sigma_R3)
    (hu : IsSchwartzDivFree_R3 u)
    (hv : IsSchwartzDivFree_R3 v) (hv' : IsSchwartzDivFree_R3 v')
    (hvv' : IsSchwartzDivFree_R3 (v + v'))
    (hw : IsSchwartzDivFree_R3 w) :
    convFormSchwartz u (v + v') w hu hvv' hw
      = convFormSchwartz u v w hu hv hw + convFormSchwartz u v' w hu hv' hw := by
  sorry -- ALLOW_SORRY: scaffold (Tier S); transport R3-d convIntegralSchwartz_add_2 through convFormSchwartz_eq_witness (S3'); proved by lean-prover

/-- **S6.** Additivity of `convFormSchwartz` in the third slot, on the div-free class. -/
theorem convFormSchwartz_add_3
    (u v w w' : L2Sigma_R3)
    (hu : IsSchwartzDivFree_R3 u) (hv : IsSchwartzDivFree_R3 v)
    (hw : IsSchwartzDivFree_R3 w) (hw' : IsSchwartzDivFree_R3 w')
    (hww' : IsSchwartzDivFree_R3 (w + w')) :
    convFormSchwartz u v (w + w') hu hv hww'
      = convFormSchwartz u v w hu hv hw + convFormSchwartz u v w' hu hv hw' := by
  sorry -- ALLOW_SORRY: scaffold (Tier S); transport R3-d convIntegralSchwartz_add_3 through convFormSchwartz_eq_witness (S3'); proved by lean-prover

/-- **S7.** ℝ-homogeneity of `convFormSchwartz` in the first slot, on the div-free class. -/
theorem convFormSchwartz_smul_1
    (c : ℝ) (u v w : L2Sigma_R3)
    (hu : IsSchwartzDivFree_R3 u) (hcu : IsSchwartzDivFree_R3 (c • u))
    (hv : IsSchwartzDivFree_R3 v) (hw : IsSchwartzDivFree_R3 w) :
    convFormSchwartz (c • u) v w hcu hv hw = c * convFormSchwartz u v w hu hv hw := by
  sorry -- ALLOW_SORRY: scaffold (Tier S); transport R3-d convIntegralSchwartz_smul_1 through convFormSchwartz_eq_witness (S3'); the component of c•u is c• the component; proved by lean-prover

/-- **S8.** ℝ-homogeneity of `convFormSchwartz` in the second slot, on the div-free class. -/
theorem convFormSchwartz_smul_2
    (c : ℝ) (u v w : L2Sigma_R3)
    (hu : IsSchwartzDivFree_R3 u)
    (hv : IsSchwartzDivFree_R3 v) (hcv : IsSchwartzDivFree_R3 (c • v))
    (hw : IsSchwartzDivFree_R3 w) :
    convFormSchwartz u (c • v) w hu hcv hw = c * convFormSchwartz u v w hu hv hw := by
  sorry -- ALLOW_SORRY: scaffold (Tier S); transport R3-d convIntegralSchwartz_smul_2 through convFormSchwartz_eq_witness (S3'); proved by lean-prover

/-- **S9.** ℝ-homogeneity of `convFormSchwartz` in the third slot, on the div-free class. -/
theorem convFormSchwartz_smul_3
    (c : ℝ) (u v w : L2Sigma_R3)
    (hu : IsSchwartzDivFree_R3 u) (hv : IsSchwartzDivFree_R3 v)
    (hw : IsSchwartzDivFree_R3 w) (hcw : IsSchwartzDivFree_R3 (c • w)) :
    convFormSchwartz u v (c • w) hu hv hcw = c * convFormSchwartz u v w hu hv hw := by
  sorry -- ALLOW_SORRY: scaffold (Tier S); transport R3-d convIntegralSchwartz_smul_3 through convFormSchwartz_eq_witness (S3'); proved by lean-prover

/-! ### S10 — Antisymmetry on the div-free class -/

/-- **S10.** Antisymmetry of `convFormSchwartz` in the last two slots, on the div-free class.

`convFormSchwartz u v w = - convFormSchwartz u w v` for `u v w` in the
`IsSchwartzDivFree_R3` class.  This transports R3-d
`convIntegralSchwartz_antisymm_of_divFree`, whose hypothesis is the Schwartz-level
weak-div-free predicate `hdiv`.  That predicate is supplied from `u ∈ L2Sigma_R3`:
membership means `divTestFunctional φ u = 0` for every Schwartz `φ`, which unfolds (via
the chosen witness `hu.choose`) to exactly the `∑_a ∫ ψu_a (∂_a φ) = 0` shape of `hdiv`
(this is the L²-level counterpart of R3-d's `divFree_intLeft`). -/
theorem convFormSchwartz_antisymm
    (u v w : L2Sigma_R3)
    (hu : IsSchwartzDivFree_R3 u) (hv : IsSchwartzDivFree_R3 v)
    (hw : IsSchwartzDivFree_R3 w) :
    convFormSchwartz u v w hu hv hw = - convFormSchwartz u w v hu hw hv := by
  sorry -- ALLOW_SORRY: scaffold (Tier S); transport R3-d convIntegralSchwartz_antisymm_of_divFree; the substantive sub-step is the L2Sigma_R3 → Schwartz `hdiv` bridge: u.2 (membership in ⨅ ker divTestFunctional) gives divTestFunctional φ u = 0 ∀φ, which via hu.choose_spec + Real.inner/L2.inner unfolding and IBP becomes ∑_a ∫ ψu_a (∂_a φ) = 0; proved by lean-prover

/-! ### S11 — The `b_bound` shape on the div-free class -/

/-- **S11.** Smooth-test L²-bound for `convFormSchwartz`, on the div-free class.

For `w` in the `IsSchwartzDivFree_R3` class there is a constant `C` (depending on `w`)
with `|convFormSchwartz u v w| ≤ C · ‖u‖ · ‖v‖` for all div-free `u v`.  This is the
operator-level `b_bound` shape, transported from R3-d `convIntegralSchwartz_bound_sup`
(the divergence-free sup-bound, with `C = ∑_{i,a} ‖∂_a ψw_i‖_∞`) via the norm bookkeeping
that relates the component `toLp 2` norms to the `EuclideanSpace`-valued L² norm
`‖(u : L2VF_R3)‖`. -/
theorem convFormSchwartz_bound
    (w : L2Sigma_R3) (hw : IsSchwartzDivFree_R3 w) :
    ∃ C : ℝ, ∀ (u v : L2Sigma_R3)
      (hu : IsSchwartzDivFree_R3 u) (hv : IsSchwartzDivFree_R3 v),
      |convFormSchwartz u v w hu hv hw|
        ≤ C * ‖(u : L2VF_R3)‖ * ‖(v : L2VF_R3)‖ := by
  sorry -- ALLOW_SORRY: scaffold (Tier S); take C = ∑_{i,a} SchwartzMap.seminorm ℝ 0 0 (∂_a (ψw_i)) from R3-d convIntegralSchwartz_bound_sup (needs the L2Sigma → hdiv bridge of S10), then convert ∑_a ‖(ψu a).toLp 2‖ ≤ C' ‖(u:L2VF_R3)‖ via component-wise L² norm bookkeeping (L2VF_projComponent_R3 + SchwartzMap.norm_toLp'); proved by lean-prover

end LerayHopf
