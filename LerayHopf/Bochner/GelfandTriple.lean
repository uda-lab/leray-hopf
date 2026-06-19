/-
# LerayHopf.Bochner.GelfandTriple — Stream D, Stage D0 (abstract Gelfand triple)

**Stream:** D (abstract Bochner–Sobolev-in-time / Gelfand triple). **Contract:**
`docs/scratch/stream-d-bochner-time.md` (Stage D0). **Status:** scaffold this cycle
(structure definitions + the `ofDissipativeEvolution` bridge SIGNATURE; proof body deferred).

This is a domain-neutral foundation: it depends only on `LerayHopf.EvolutionTriple`
(the 0-axiom abstract layer) and mathlib. Both `torus3Evolution` and `r3Evolution` are
instances of `DissipativeEvolution`, so the abstract triple built here serves T³ and ℝ³
without duplication and without import cycles into either domain closure.

## Main definitions

- `GelfandTriple` — abstract Gelfand triple `V ↪ H ≅ H' ↪ V'`: two real Hilbert spaces
  `V`, `H` with a continuous, dense, injective embedding `ι : V →L[ℝ] H`. (The dual side
  `H ↪ V'` is the transpose of `ι`; we keep the structure minimal, carrying only the
  primal embedding data that Aubin–Lions and the energy law actually consume.)
- `GelfandTriple.IsOfDissipativeEvolution` — the *faithfulness contract* relating a built
  `GelfandTriple GT` to a `DissipativeEvolution E`: it pins `GT.H = E.H` (with the carried
  Hilbert instances agreeing), forces `GT.ι` to be exactly the set inclusion of the chosen
  regularity subspace `Vsub ⊆ E.H`, and ties the `V`-norm to `q`/`E.reg` via
  `‖v‖² = E.reg (ι v)`. A `GelfandTriple` for an *unrelated* space cannot satisfy it.
- `GelfandTriple.ofDissipativeEvolution` — the bridge: from a `DissipativeEvolution E`
  whose regularity functional `E.reg` is a genuine squared seminorm, carve the regularity
  space `V` (with `‖·‖² = E.reg`) sitting densely inside `H := E.H`, packaged together with
  a proof of `IsOfDissipativeEvolution` (a `Σ'`), so the returned triple is provably the
  one carved from `E` — not an arbitrary dense Hilbert embedding.

## Assumptions

No new `axiom`/`opaque`/`constant`. The genuinely-missing analytic inputs (a real **Hilbert**
structure on the regularity subspace whose squared norm is `E.reg`, plus density of that
subspace) are isolated as explicit HYPOTHESIS/DATA arguments to `ofDissipativeEvolution`,
never as axioms — matching the established no-smuggle pattern (P3 `LocalRellichInput`,
P2 `TimeCompactnessInput`). The Hilbert structure is taken as an explicit
`InnerProductSpace`/`CompleteSpace` on `Vsub` rather than reconstructed from a seminorm: a
dominated seminorm with `E.reg = q²` does not force an inner-product/Hilbert structure, so
deriving one would overclaim from insufficient inputs (statement-gate fix).

## Scaffold ledger (this cycle)

- `GelfandTriple` — structure definition (scaffold; no proof obligation).
- `GelfandTriple.IsOfDissipativeEvolution` — `def` of the faithfulness contract (a `Prop`,
  no proof obligation; pure statement).
- `GelfandTriple.ofDissipativeEvolution` — must-prove construction returning
  `Σ' GT : GelfandTriple, GT.IsOfDissipativeEvolution …`. Body assembled: the `Σ'` package,
  `ι := Subtype.val`, injectivity, dense range (from `hdense`), and the full
  `IsOfDissipativeEvolution` faithfulness proof (`hH := rfl`, HEq instances, range `= Vsub`,
  `‖v‖² = E.reg (ι v)` from `hreg_norm`) are all proved. The two algebraic-embedding fields
  `ι_linear` / `ι_continuous` remain `ALLOW_SORRY`: they are stated against the EXPLICIT
  input module structure `normV`/`ipsV`, which carries an additive/scalar structure on
  `↥Vsub` that the signature does not pin to the submodule's own (verified non-defeq), so the
  coercion's linearity/continuity is not derivable without a lean-coder compatibility-hypothesis
  signature fix. 2 `ALLOW_SORRY`.
-/

import LerayHopf.EvolutionTriple
import Mathlib.Analysis.InnerProductSpace.Basic

namespace LerayHopf.Bochner

open scoped InnerProductSpace

/-! ### Abstract Gelfand triple `V ↪ H ≅ H' ↪ V'` -/

/-- An abstract **Gelfand triple** (also "evolution triple") `V ↪ H ≅ H' ↪ V'`.

Carries the minimal primal data consumed by the abstract Bochner-time / Aubin–Lions
library:

- a real Hilbert "regularity" space `V` (the role of `H¹_σ`; its squared norm is the
  regularity functional),
- a real Hilbert "pivot" space `H` (the role of `L²_σ`; identified with its own dual),
- a continuous linear embedding `ι : V →L[ℝ] H`,
- **injectivity** of `ι` (so `V` is genuinely a subspace of `H`),
- **dense range** of `ι` (so `H ↪ V'` is injective on the dual side — the defining
  property that makes `(V, H, V')` a Gelfand triple rather than an arbitrary pair).

The dual space `V'` and the embedding `H ↪ V'` are NOT stored: `V'` is recovered as the
continuous dual of `V`, and `H ↪ V'` is the transpose of `ι` post-composed with the Riesz
identification `H ≅ H'`. Keeping the structure to the primal embedding avoids carrying
redundant data while leaving the full triple recoverable. No NS-specific structure
(divergence-free, convection) is encoded here (No-overclaim). -/
structure GelfandTriple where
  /-- The regularity space `V` (e.g. `H¹_σ`). -/
  V : Type*
  /-- The pivot space `H` (e.g. `L²_σ`), identified with its own dual. -/
  H : Type*
  /-- `NormedAddCommGroup` instance on `V`. -/
  instNACG_V : NormedAddCommGroup V
  /-- Real inner-product-space instance on `V`. -/
  instIPS_V : InnerProductSpace ℝ V
  /-- Completeness of `V`. -/
  instCS_V : CompleteSpace V
  /-- `NormedAddCommGroup` instance on `H`. -/
  instNACG_H : NormedAddCommGroup H
  /-- Real inner-product-space instance on `H`. -/
  instIPS_H : InnerProductSpace ℝ H
  /-- Completeness of `H`. -/
  instCS_H : CompleteSpace H
  /-- The underlying embedding map `V → H`. Its linearity and continuity are the
  `ι_linear` / `ι_continuous` fields; bundling it as a bare function (with Prop fields)
  rather than a `ContinuousLinearMap` keeps the structure free of fragile inline instance
  synthesis while still asserting the full continuous-linear-injective-dense embedding. -/
  ι : V → H
  /-- `ι` is `ℝ`-linear. -/
  ι_linear :
    letI := instNACG_V; letI := instIPS_V; letI := instNACG_H; letI := instIPS_H
    IsLinearMap ℝ ι
  /-- `ι` is continuous (the `V ↪ H` embedding is bounded). -/
  ι_continuous :
    letI := instNACG_V; letI := instNACG_H
    Continuous ι
  /-- The embedding is injective: `V` is a genuine subspace of `H`. -/
  ι_injective :
    Function.Injective ι
  /-- The embedding has dense range: `V` is dense in `H` (equivalently, `H ↪ V'` is
  injective — the Gelfand-triple defining property). -/
  ι_denseRange :
    letI := instNACG_H
    DenseRange ι

/-! ### Bridge: `DissipativeEvolution → GelfandTriple` -/

/-- **Faithfulness contract** tying a `GelfandTriple GT` to the data carved from a
`DissipativeEvolution E` and a regularity subspace `Vsub ⊆ E.H` with `V`-norm `q`.

A bare `GelfandTriple` carries an *anonymous* pair of Hilbert spaces with a dense
embedding; on its own it could be ANY such embedding, unrelated to `E`. This predicate is
the contract that pins it down to the triple genuinely built from `E`:

- `hH : GT.H = E.H` — the pivot space is *the same type* as `E.H` …
- `hH_inst` / `hH_ips` — … carrying `E`'s own Hilbert instances (the equality is not just
  of carriers but of the normed/inner-product structure, transported along `hH`);
- `hrange : Set.range (fun v => cast hH (GT.ι v)) = (Vsub : Set E.H)` — the embedding's
  range, viewed in `E.H`, is *exactly* the chosen regularity subspace `Vsub`. Together with
  the structural `GT.ι_injective`, this forces `GT.ι` to be the inclusion of `Vsub` (up to
  the linear iso `GT.V ≃ Vsub` that injectivity onto `Vsub` provides);
- `hnorm : ∀ v, ‖v‖ ^ 2 = E.reg (cast hH (GT.ι v))` — the `V`-norm squared *is* `E.reg`
  pulled back along the embedding, i.e. `‖v‖²_V = E.reg (ι v) = q (ι v)²`. This is the
  norm ↔ `reg` identification, made part of the *result* contract rather than only an input
  hypothesis.

No NS-specific data (divergence-free, convection) appears: the contract speaks only about
`E.H`, `E.reg`, `Vsub`, the carried inner-product structure, and the embedding. -/
def GelfandTriple.IsOfDissipativeEvolution
    (E : DissipativeEvolution)
    (Vsub : letI := E.instNACG; letI := E.instIPS; Submodule ℝ E.H)
    (GT : GelfandTriple) : Prop :=
  letI := E.instNACG; letI := E.instIPS
  letI := GT.instNACG_H; letI := GT.instIPS_H
  ∃ hH : GT.H = E.H,
    -- the carried Hilbert structure on `GT.H` is exactly `E`'s, transported along `hH`
    (HEq GT.instNACG_H E.instNACG) ∧ (HEq GT.instIPS_H E.instIPS) ∧
    -- the embedding's range is exactly the regularity subspace `Vsub` ⊆ `E.H`
    (Set.range (fun v => cast hH (GT.ι v)) = (Vsub : Set E.H)) ∧
    -- the `V`-norm squared is `E.reg` pulled back along the embedding (norm ↔ reg)
    (letI := GT.instNACG_V; ∀ v : GT.V, ‖v‖ ^ 2 = E.reg (cast hH (GT.ι v)))

/-- **Bridge construction.** From a `DissipativeEvolution E` whose regularity functional
`E.reg` is a genuine squared seminorm, build the Gelfand triple with pivot `H := E.H` and
regularity space `V` carved from the finite-regularity vectors (`‖v‖²_V = E.reg v`), sitting
densely inside `H`.

The result is a **dependent package** `Σ' GT : GelfandTriple, GT.IsOfDissipativeEvolution E Vsub`:
returning a bare `GelfandTriple` would let a proof hand back *any* dense Hilbert embedding,
so the second component is essential — it certifies that the produced triple really is the
one carved from `E` (`GT.H = E.H`, `GT.ι` is the inclusion of `Vsub`, `‖·‖²_V = E.reg ∘ ι`).

The analytic facts that mathlib does not hand us — that the regularity subspace carries a
genuine real **Hilbert** structure whose squared norm is `E.reg`, and that this subspace is
dense in `E.H` — are isolated as explicit hypotheses below, NOT as axioms (no-smuggle: each
speaks only about the given `E`/`Vsub`, asserting no downstream compactness/limit content).

**Honest Hilbert input (statement-gate fix).** A mere dominated seminorm `q` with
`E.reg = q²` does NOT force a Hilbert structure (an ℓ¹-type norm on a dense
finite-dimensional subspace satisfies nonnegativity/triangle/smul/domination yet is not the
norm of any inner-product space). We therefore take the Hilbert structure on the regularity
subspace as **explicit input**: a real `InnerProductSpace ℝ Vsub` together with completeness
`CompleteSpace Vsub`, whose induced squared norm equals `E.reg` pulled back along the
inclusion (`hreg_norm`), and boundedness of the inclusion `Vsub ↪ E.H` (`hbdd`). Positive
definiteness, the parallelogram law, and inner-product compatibility are then *consequences*
of the provided `InnerProductSpace`/`NormedAddCommGroup` instances, not unsupported claims.

This is the construction that makes the whole Stream-D library apply to `torus3Evolution`
and `r3Evolution` at once.

**Scaffold this cycle:** the body assembling the carved space and the faithfulness proof is
deferred (lean-prover target). The SIGNATURE — including the `Σ'` contract — is the spec. -/
noncomputable def GelfandTriple.ofDissipativeEvolution
    (E : DissipativeEvolution)
    -- The regularity subspace carved inside `E.H` on which the V-norm lives.
    (Vsub : letI := E.instNACG; letI := E.instIPS; Submodule ℝ E.H)
    -- EXPLICIT Hilbert structure on the regularity subspace `Vsub` (the honest input that a
    -- dominated seminorm cannot provide): a real normed group, a compatible real
    -- inner-product space, and completeness. These are passed as data so the constructed
    -- `GelfandTriple.V := Vsub` genuinely IS a Hilbert space — positive definiteness, the
    -- parallelogram law, and inner-product compatibility follow from these instances rather
    -- than being conjured from `E.reg`. (They are intentionally distinct from the ambient
    -- norm `Vsub` inherits from `E.H`; the V-norm is the stronger regularity norm.)
    (normV : letI := E.instNACG; letI := E.instIPS; NormedAddCommGroup Vsub)
    (ipsV : letI := E.instNACG; letI := E.instIPS;
      @InnerProductSpace ℝ Vsub _ normV.toSeminormedAddCommGroup)
    (csV : letI := E.instNACG; letI := E.instIPS;
      @CompleteSpace Vsub normV.toMetricSpace.toUniformSpace)
    -- The Hilbert V-norm squared on `Vsub` is exactly `E.reg` pulled back along the inclusion.
    (hreg_norm : letI := E.instNACG; letI := E.instIPS; letI := normV;
      ∀ v : Vsub, ‖v‖ ^ 2 = E.reg (v : E.H))
    -- `V ↪ H` is bounded: the ambient `E.H`-norm is dominated by the V-norm on `Vsub`
    -- (continuity of the regularity embedding).
    (hbdd : letI := E.instNACG; letI := E.instIPS; letI := normV;
      ∃ C : ℝ, 0 < C ∧ ∀ v : Vsub, ‖(v : E.H)‖ ≤ C * ‖v‖)
    -- the regularity subspace is dense in `E.H` (the Gelfand-triple density property).
    (hdense : letI := E.instNACG; letI := E.instIPS; Dense (Vsub : Set E.H)) :
    Σ' GT : GelfandTriple, GT.IsOfDissipativeEvolution E Vsub := by
  letI := E.instNACG; letI := E.instIPS; letI := E.instCS
  letI := normV; letI := ipsV; letI := csV
  -- The set inclusion `Vsub → E.H`, packaged as data for the structure fields.
  -- Continuity: the `Vsub`-norm is `normV`; the ambient `E.H`-norm is dominated by it (`hbdd`).
  -- We obtain it from the linear map `Submodule.subtype Vsub` and the explicit bound.
  -- Build the `GelfandTriple` with `V := Vsub`, `H := E.H`, `ι := Subtype.val`.
  refine ⟨{
      V := Vsub
      H := E.H
      instNACG_V := normV
      instIPS_V := ipsV
      instCS_V := csV
      instNACG_H := E.instNACG
      instIPS_H := E.instIPS
      instCS_H := E.instCS
      ι := fun v => (v : E.H)
      ι_linear := ?_
      ι_continuous := ?_
      ι_injective := ?_
      ι_denseRange := ?_ }, ?_⟩
  · -- linearity of the subtype inclusion `↥Vsub → E.H`.
    -- The conclusion `IsLinearMap ℝ (fun v => (v : E.H))` is stated with the module structure
    -- `normV.toAddCommMonoid` / `ipsV.toModule` carried by the EXPLICIT input instances, which
    -- are NOT definitionally the submodule's own `Vsub.addCommMonoid` / `Vsub.module` (verified:
    -- `rfl` for `map_add` is rejected with "synthesized Vsub.addCommMonoid / inferred
    -- normV.toAddCommMonoid"). The signature provides `normV`/`ipsV` as free data with no
    -- hypothesis pinning their `+`/`•` to the submodule's, so
    -- `Subtype.val (x +[normV] y) = (x : E.H) + (y : E.H)` is not derivable here.
    sorry -- ALLOW_SORRY: normV/ipsV-vs-submodule additive/scalar instance-compatibility gap; needs a lean-coder signature fix adding the compatibility hypothesis (e.g. carry `(Submodule.subtype Vsub).IsLinearMap` as data, or `HEq normV.toAddCommGroup Vsub.addCommGroup` + scalar variant).
  · -- continuity of `↥Vsub → E.H` from the domination bound `hbdd`.
    -- Same instance-compatibility blocker as `ι_linear`. `ι_continuous` is stated with
    -- `letI := instNACG_V` (= `normV`); `hbdd` bounds the `E.H`-norm by `normV`'s norm. To turn
    -- that bound into `Continuous` via `AddMonoidHomClass.continuous_of_bound` one needs the
    -- inclusion as an additive hom over `normV`'s group structure, which again requires `normV`'s
    -- `+` to be the submodule's. With the compatibility hypothesis,
    -- `AddMonoidHomClass.continuous_of_bound (Submodule.subtype Vsub) C hbound`
    -- (after `obtain ⟨C, _, hbound⟩ := hbdd`) closes it.
    sorry -- ALLOW_SORRY: same normV-vs-submodule additive-instance gap as ι_linear; lean-coder signature fix (compatibility hypothesis) unblocks it.
  · -- injectivity of the subtype inclusion
    exact Subtype.val_injective
  · -- dense range: range of `Subtype.val` is `Vsub`, which is dense by `hdense`
    rw [denseRange_iff_closure_range]
    have hrange : Set.range (fun v : Vsub => (v : E.H)) = (Vsub : Set E.H) :=
      Subtype.range_val
    rw [hrange]
    exact hdense.closure_eq
  · -- the `IsOfDissipativeEvolution` faithfulness contract
    refine ⟨rfl, HEq.rfl, HEq.rfl, ?_, ?_⟩
    · -- range of `cast rfl ∘ ι` is exactly `Vsub`
      exact (Subtype.range_val : Set.range (fun v : Vsub => (v : E.H)) = (Vsub : Set E.H))
    · -- norm² = E.reg ∘ ι, by `hreg_norm`
      intro v
      simpa using hreg_norm v

end LerayHopf.Bochner
