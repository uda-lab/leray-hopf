import LerayHopf.EvolutionTriple
import LerayHopf.Galerkin.Domain          -- issue #112 PR-C: generic Galerkin.Domain
import LerayHopf.Galerkin.SolutionBundles -- issue #112 PR-C: generic solution bundles
import LerayHopf.Torus.H1Sigma
import LerayHopf.EnergyEstimate
import LerayHopf.Torus.GalerkinProjection
import LerayHopf.Torus.Leray  -- L2Sigma (issue #113 PR-1: explicit — was relying on transitivity)
import LerayHopf.Torus.VelocityGalerkin  -- velocityProjection_n(_preserves_L2Sigma) (issue #113
  -- PR-1: was reached transitively via H1Sigma → VelocityGalerkin, no longer since H1Sigma's
  -- import was narrowed to Leray)
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open MeasureTheory Filter Topology

/-!
# Solution interfaces of Leray–Hopf existence on 𝕋³

**M6 — assembly + the remaining axiom.**

This file closes the T³ Leray–Hopf existence proof by axiomatizing the analytic result that
remains out of reach in Lean (Aubin–Lions time compactness),
constructing the proof-carrying solution structures, and assembling the existence machinery.

**Issue #22 de-axiomatization:** The former fat axiom A4 `torus3_NSForms_exist` has been
**removed**.  `Nonempty Torus3NSForms` is now the theorem `torus3_NSForms_exists` in
`LerayHopf/Torus/ConvectionForm.lean`, derived sorry-free from the gap hypothesis via
`Torus3NSForms_of_gap`.  Issue #53 / PR #62 then proved `torusConvectionGap_exists` itself using
the determined-form construction in `TorusConvectionExtension.lean`.  The capstone
`exists_lerayHopf_torus3` is relocated downstream.

## Architecture

The two axioms remaining in this file are *true* and *minimal* (every field is used in the
assembly).  Non-vacuity of the convection form `b` is pinned (in the downstream theorem) via
`b_galerkin` to the finite Galerkin convection form `galerkinConvection`, which is generically
nonzero and explicitly excludes `b = 0`.  The spatial half of Aubin–Lions is *not* axiomatized:
it is supplied as an explicit hypothesis discharged by the proved `rellich_L2Sigma`.

**v4 de-axiomatization:** The viscous (Stokes) form is no longer a field of `Torus3NSForms`
(axiom A4).  It is the concrete `stokesTestPairing` definition (a Fourier tsum), which is
sound for all `u : L2VF`.  The energy-inequality fields use `viscousFormSq ν` directly.

## Main definitions and theorems

- `galerkinConvection`              : finite Galerkin convection form (Finset.sum, .re)
- `Torus3NSForms`                   : structure bundling the T³ NS forms with their properties
  (existence is now `torus3_NSForms_exists`, downstream in `TorusConvectionForm.lean`, issue #22)
- `Torus3NSForms.b_self_zero`       : proved lemma — `b u u u = 0` from antisymmetry
- `torus3Evolution`                 : `DissipativeEvolution` built from a `Torus3NSForms`
- `GalerkinSolutionData`            : structure for the `n`-th Galerkin ODE solution (issue #24:
  `u_hasDeriv`/`u_ode` forward-only `∀ t, 0 ≤ t →`, matching the merged ℝ³ sibling — the all-`t`
  form was an un-physical over-claim, see those fields' SOUNDNESS comments)
- `AubinLionsPackage`               : structure carrying the compactness subsequence (parameterized by the Galerkin sequence)
- (no project axioms remain in this file — `aubin_lions` REMOVED, issue #23 T-AL-6)
- `LerayHopfSolutionFull`           : proof-carrying Leray–Hopf solution structure
- `GalerkinCompactnessPackageFull`  : proof-carrying Galerkin compactness package
- `exists_lerayHopf_from_package_full` : copies proofs from package to solution
- `exists_lerayHopf_torus3` : main existence theorem — RELOCATED to
  `TorusGalerkinODECapstone.lean` (issue #24), rerouted through the proved `galSeq_of_torus`

## Assumptions

**No project axioms remain in this file** — every former project axiom has been removed.
The former `torusConvectionGap_exists` project axiom has been **removed** (issue #53 / PR #62): it is now
the theorem re-exported from `TorusConvectionExtension.lean`.  The former `galerkin_ode_solution`
has also been **removed** (issue #24): the finite-dim torus Galerkin ODE is solved
unconditionally by the proved `galerkinSolutionData_torus`.  The former `galerkin_limit_passage`
has been **removed**: it is replaced by the proved theorems
`torus_galerkin_limit_passage_of_energyClass` + `torus_energyClass_of_aubinLions`, assembled in
`TorusGalerkinODECapstone.lean` (the consumer had to move downstream to avoid an import cycle).
The former `aubin_lions` project axiom has been **removed** (issue #23, this change): it is now
the proved def `torusAubinLionsPackage_of_galSeq` in `TorusAubinLionsAssembly.lean`.
-/

namespace LerayHopf

/-! ### Finite Galerkin convection form (non-vacuity pin) -/

/-- The finite (box-`n`) Galerkin convection form.

For Fourier modes `e^{2πi k·x}`, the convection structure constant is:
  `b(u, v, w) = Σᵢ Σₐ Σ_{k,l ∈ fourierBox n} û_a(k) · (2πi lₐ) · v̂ᵢ(l) · ŵᵢ(-(k+l))`
where `û_a(k) = mFourierCoeff3 (L2VF_projComponentC a u) k`.

This is the correct finite-sum approximation of the convection trilinear form `(u·∇)v·w`
on `𝕋³`.  It is well-defined (finite sum), generically nonzero (so `b = 0` is excluded by
`b_galerkin`), and equals the genuine convection form on Galerkin subspaces `Vₙ`. -/
noncomputable def galerkinConvection (n : ℕ) (u v w : L2VF) : ℝ :=
  (∑ i : Fin 3, ∑ a : Fin 3, ∑ k ∈ fourierBox n, ∑ l ∈ fourierBox n,
    (mFourierCoeff3 (L2VF_projComponentC a u) k) *
    ((2 * (Real.pi : ℂ) * Complex.I * (l a : ℂ)) *
    ((mFourierCoeff3 (L2VF_projComponentC i v) l) *
    (mFourierCoeff3 (L2VF_projComponentC i w) (-(k + l)))))).re

/-! ### Concrete Stokes test-slot pairing -/

/-- The **concrete viscous (Stokes) test-slot pairing** defined via Fourier coefficients:

  `stokesTestPairing u w = ∑ j, ∑' k, (2π)² (∑ᵢ kᵢ²) · Re[ûⱼ(k) · conj(ŵⱼ(k))]`

This is the Fourier-series representation of `∫_{𝕋³} ∇u : ∇w` (using the `e^{2πi k·x}`
convention where `∂_xᵢ e^{2πi k·x}` contributes `(2π kᵢ)²`).  The diagonal recovers
`viscousFormSq 1 u` (since `Re[ûⱼ(k)·conj(ûⱼ(k))] = |ûⱼ(k)|²`).

This is a **concrete definition** — NOT axiomatized — so it is sound even for `u ∉ H¹`
(the tsum is simply 0 off the summable set, a mathlib convention). -/
noncomputable def stokesTestPairing (u w : L2VF) : ℝ :=
  ∑ j : Fin 3, ∑' k : Fin 3 → ℤ,
    ((2 * Real.pi) ^ 2 * (∑ i : Fin 3, (k i : ℝ) ^ 2) : ℝ) *
      (mFourierCoeff3 (L2VF_projComponentC j u) k *
        (starRingEnd ℂ (mFourierCoeff3 (L2VF_projComponentC j w) k))).re

/-! ### Galerkin test predicate -/

/-- A vector `w : L2Sigma` is a **Galerkin test function** if it lies in a finite Galerkin
subspace `Vₙ`, i.e., it has finite Fourier support:
  `IsGalerkinTest w ↔ ∃ n : ℕ, velocityProjection_n n (w : L2VF) = (w : L2VF)`.

Every trig polynomial in `L²_σ` satisfies this.  The class is dense in `L²_σ` and
every element is smooth (finite Fourier sum), so it is the standard Faedo–Galerkin
test class used in the weak NS formulation. -/
def IsGalerkinTest (w : L2Sigma) : Prop :=
  ∃ n : ℕ, velocityProjection_n n (w : L2VF) = (w : L2VF)

/-! ### T³ Navier–Stokes forms structure -/

/-- The bundle of T³ Navier–Stokes forms: only the trilinear convection form `b`
(the viscous form is the concrete `stokesTestPairing`, NOT axiomatized).

**Non-vacuity:** The field `b_galerkin` pins `b` to `galerkinConvection` on Galerkin
subspaces, which is generically nonzero.  This excludes the vacuous witness `b := 0`
and ensures the existence witness `torus3_NSForms_exists` (issue #22, in
`TorusConvectionForm.lean`) is genuinely about Navier–Stokes (not Stokes or heat).

**Antisymmetry convention:** `b u v w = -b u w v` (skew in the last two slots).
This is the correct form for the T³ convection form `b(u,v,w) = ∫ (u·∇v)·w`.

**Multilinearity:** `b` is trilinear (additive + ℝ-homogeneous in each argument).
Required to exclude pathological `F` where `b(u,u,0)≠0` (which would render
`galerkin_ode_solution` inconsistent when tested against `w=0`).

**Smooth-test convection bound (Fix 2):** For a Galerkin test `w`, the bound is
`|b(u,v,w)| ≤ C(w) · ‖u‖_{L²} · ‖v‖_{L²}`.  TRUE: `b(u,v,w) = -∫(u·∇)w·v`,
so `|b| ≤ ‖∇w‖_∞ ‖u‖_{L²} ‖v‖_{L²}` with `‖∇w‖_∞ < ∞` for trig polynomials.
This is the correct shape for the strong-L²(0,T) limit passage.

**Viscous form (v4 de-axiomatization):** The Stokes form is no longer a field of this
structure.  It is the concrete definition `stokesTestPairing`, which is sound for all
`u : L2VF` (tsum returns 0 off the summable set).  The diagonal recovers `viscousFormSq 1 u`. -/
structure Torus3NSForms where
  /-- The trilinear convection form `b : L²_σ × L²_σ × L²_σ → ℝ`. -/
  b : L2Sigma → L2Sigma → L2Sigma → ℝ
  /-- Antisymmetry in the last two slots: `b u v w = -b u w v`. -/
  b_antisymm : ∀ (u v w : L2Sigma), b u v w = - b u w v
  /-- Additivity in the first slot. -/
  b_add_1 : ∀ (u u' v w : L2Sigma), b (u + u') v w = b u v w + b u' v w
  /-- Additivity in the second slot. -/
  b_add_2 : ∀ (u v v' w : L2Sigma), b u (v + v') w = b u v w + b u v' w
  /-- Additivity in the third slot. -/
  b_add_3 : ∀ (u v w w' : L2Sigma), b u v (w + w') = b u v w + b u v w'
  /-- ℝ-homogeneity in the first slot. -/
  b_smul_1 : ∀ (c : ℝ) (u v w : L2Sigma), b (c • u) v w = c * b u v w
  /-- ℝ-homogeneity in the second slot. -/
  b_smul_2 : ∀ (c : ℝ) (u v w : L2Sigma), b u (c • v) w = c * b u v w
  /-- ℝ-homogeneity in the third slot. -/
  b_smul_3 : ∀ (c : ℝ) (u v w : L2Sigma), b u v (c • w) = c * b u v w
  /-- **Smooth-test convection bound (Fix 2):** For a Galerkin test function `w`, the
  convection form is L²-bounded in the first two slots:
  `|b(u,v,w)| ≤ C(w) · ‖u‖_{L²} · ‖v‖_{L²}`.
  TRUE: `b(u,v,w) = -∫(u·∇)w·v`, so `|b| ≤ ‖∇w‖_∞ ‖u‖_{L²} ‖v‖_{L²}`
  with `‖∇w‖_∞ < ∞` for trig polynomials.  This is the correct shape for strong-L²(0,T)
  convergence in the nonlinear limit passage. -/
  b_bound : ∀ (w : L2Sigma), IsGalerkinTest w →
    ∃ C : ℝ, ∀ (u v : L2Sigma), |b u v w| ≤ C * ‖(u : L2VF)‖ * ‖(v : L2VF)‖
  /-- Non-vacuity pin: `b` agrees with `galerkinConvection` on Galerkin subspaces `Vₙ`.
  This field genuinely excludes `b = 0` (which would fail here since `galerkinConvection ≢ 0`).
  **FLAG for Codex non-vacuity audit:** (i) `galerkinConvection` is the correct convection
  structure constant from `(u·∇)v` on `𝕋³`; (ii) this field excludes `b = 0`; (iii) the
  genuine convection form witnesses `torus3_NSForms_exists` (issue #22); (iv) `b_bound` is the
  smooth-test L² bound. -/
  b_galerkin : ∀ (n : ℕ) (u v w : L2Sigma),
    velocityProjection_n n (u : L2VF) = (u : L2VF) →
    velocityProjection_n n (v : L2VF) = (v : L2VF) →
    velocityProjection_n n (w : L2VF) = (w : L2VF) →
    b u v w = galerkinConvection n (u : L2VF) (v : L2VF) (w : L2VF)

/-! ### A4 (de-axiomatized, issues #22 and #53): T³ NS forms exist via the proved gap

The former fat axiom `torus3_NSForms_exist : Nonempty Torus3NSForms` has been **removed**.  Its
content is now the theorem `torus3_NSForms_exists`, derived from the proved determined-form
theorem `torusConvectionGap_exists` via `Torus3NSForms_of_gap`: all trilinear
`b_add_*`/`b_smul_*` algebra, the unrestricted L²-bound transfer, and the Galerkin pin are theorem
content.  The resulting total trilinear extension is pinned to the genuine Fourier/Galerkin test
form and continuous in the two solution slots at fixed Galerkin tests; it is not advertised as a
canonical continuous operator on all pure `L² × L² × L²` triples.  The capstone
`exists_lerayHopf_torus3` is relocated downstream and rerouted through
`torus3_NSForms_exists`.  Temam II.§1; RRS §3.2. -/

/-! ### Proved lemma: b u u u = 0 -/

/-- **b(u, u, u) = 0** follows purely from antisymmetry.

Proof: `b(u, u, u) = -b(u, u, u)` by `b_antisymm u u u`, so `b(u, u, u) = 0`. -/
theorem Torus3NSForms.b_self_zero (F : Torus3NSForms) (u : L2Sigma) :
    F.b u u u = 0 := by
  have h := F.b_antisymm u u u
  linarith

/-- The convection trilinear form vanishes when its last two arguments coincide —
the energy-estimate workhorse.

Proof: `b(u, v, v) = -b(u, v, v)` by `b_antisymm u v v`, so `b(u, v, v) = 0`. -/
theorem Torus3NSForms.b_self_zero_right (F : Torus3NSForms) (u v : L2Sigma) :
    F.b u v v = 0 := by
  have h := F.b_antisymm u v v
  linarith

/-! ### Generic Galerkin domain instance (issue #112 PR-C) -/

/-- The 𝕋³ Galerkin domain: ambient `L2VF`, divergence-free subspace `L2Sigma`, projector
family `velocityProjection_n`, and the concrete T³ domain functionals (`memH1VF`,
`stokesTestPairing`, `viscousFormSq`, `h1EnergySq`, `IsGalerkinTest`).  The reg-bound
integrand is the full `h1EnergySq` (ν-independent) with RHS `T‖u₀‖² + ‖u₀‖²/(2ν)`. -/
@[reducible] noncomputable def torusDomain : Galerkin.Domain where
  X := L2VF
  σ := L2Sigma
  σ_complete := inferInstance
  P := velocityProjection_n
  P_preserves_σ := velocityProjection_n_preserves_L2Sigma
  regMem := memH1VF
  stokes := stokesTestPairing
  dissip := viscousFormSq
  evoReg := h1EnergySq
  evoReg_nonneg := h1EnergySq_nonneg
  regIntegrand := fun _ => h1EnergySq
  regBoundRHS := fun ν T r => T * r ^ 2 + r ^ 2 / (2 * ν)
  isTest := IsGalerkinTest

/-- The domain-neutral convection core of a `Torus3NSForms` (the `b_galerkin` non-vacuity
pin stays on `Torus3NSForms`; this is a projection onto the `NSFormCore` fields). -/
def Torus3NSForms.core (F : Torus3NSForms) : Galerkin.NSFormCore torusDomain where
  b := F.b
  b_antisymm := F.b_antisymm
  b_add_1 := F.b_add_1
  b_add_2 := F.b_add_2
  b_add_3 := F.b_add_3
  b_smul_1 := F.b_smul_1
  b_smul_2 := F.b_smul_2
  b_smul_3 := F.b_smul_3
  b_bound := F.b_bound

/-! ### Domain-projection reduction lemmas (issue #112 PR-C, §6.2)

`rfl`-lemmas normalizing `torusDomain` / `Torus3NSForms.core` projections back to the
concrete T³ functionals.  After the abbrev rewiring, field accesses like `gs.u_ode`
present `torusDomain.stokes`/`F.core.b` rather than `stokesTestPairing`/`F.b`; these
lemmas let downstream `rw`/`linarith` sites that pattern-match the concrete forms normalize
via `simp only [...]`.  (Not `@[simp]`-tagged to avoid perturbing green proofs.) -/

theorem torusDomain_stokes (u w : L2VF) :
    torusDomain.stokes u w = stokesTestPairing u w := rfl

theorem torusDomain_dissip (μ : ℝ) (u : L2VF) :
    torusDomain.dissip μ u = viscousFormSq μ u := rfl

theorem torusDomain_regMem (u : L2VF) :
    torusDomain.regMem u = memH1VF u := rfl

theorem torusDomain_regIntegrand (μ : ℝ) (u : L2VF) :
    torusDomain.regIntegrand μ u = h1EnergySq u := rfl

theorem Torus3NSForms.core_b (F : Torus3NSForms) (u v w : L2Sigma) :
    (F.core).b u v w = F.b u v w := rfl

/-! ### Dissipative evolution from T³ NS forms (sorry-free) -/

/-- Build a `DissipativeEvolution` from a `Torus3NSForms`, as `torusDomain.evolution F.core`.

`H := L2Sigma`, with the `L2Sigma`-subspace instances.  The regularity functional is
`h1EnergySq ∘ (↑)`, viscous form is the concrete `stokesTestPairing`, convection form is `F.b`.

This construction is **sorry-free**.  The weak formulation tests against the Fourier/Galerkin
class `IsGalerkinTest`; density and fixed-test continuity support extension arguments, but the
current theorem statement itself is Galerkin-test based rather than quantified over all smooth
divergence-free tests. -/
noncomputable abbrev torus3Evolution (F : Torus3NSForms) : DissipativeEvolution :=
  torusDomain.evolution F.core

/-! ### Galerkin ODE solution data -/

/-- Data produced by the `n`-th Galerkin ODE on `Vₙ ⊆ L²_σ`.

Packages: the solution curve, initial condition, subspace-range property, differentiability,
the projected ODE, H¹ regularity, and uniform (n-independent) energy and regularity bounds.
Every field is used in the Aubin–Lions assembly (`torusAubinLionsPackage_of_galSeq`, proved;
formerly the `aubin_lions` axiom, removed issue #23) or the proved limit passage
(`torus_galerkin_limit_passage_of_energyClass`). -/
abbrev GalerkinSolutionData (F : Torus3NSForms) (ν : ℝ) (u₀ : L2Sigma) (n : ℕ) :=
  Galerkin.SolutionData torusDomain F.core ν u₀ n

/-! ### A1: Galerkin ODE existence — DISCHARGED (issue #24)

The former `axiom galerkin_ode_solution : GalerkinSolutionData F ν u₀ n` has been **removed**.
The `n`-th finite-dimensional torus Galerkin ODE is now solved **unconditionally** by the proved
`galerkinSolutionData_torus` (`LerayHopf/Torus/GalerkinODESolve.lean`), built over the finite-dim
real subspace `velocitySpan n` (`LerayHopf/Torus/GalerkinScheme.lean`) via Picard–Lindelöf +
forward-global continuation (`forwardGlobalSolution_exists`) and the proved energy/dissipation
bounds.  The capstone `exists_lerayHopf_torus3` is rerouted through it via
`galSeq_of_torus` (`LerayHopf/Torus/GalerkinODECapstone.lean`), dropping this axiom from its
`#print axioms`.  Mirrors the merged ℝ³ discharge of `galerkin_ode_solution_R3` (issue #10). -/

/-! ### Aubin–Lions compactness package -/

/-- Package produced by the Aubin–Lions theorem.

Carries: the extracted subsequence `φ`, its strict monotonicity, a limit curve
`u : Time → L2Sigma`, and **strong `L²(0,T; L²_σ)` convergence**: the time-integral of
the squared `L²_σ`-distance between the subsequence and the limit tends to `0`.

`galSeq` is a **structure parameter** (not a field), so the convergence statement is
type-enforced against the same sequence passed to `torusAubinLionsPackage_of_galSeq` (the
proved replacement for the former `aubin_lions` axiom) and the proved limit passage,
tying the A1 → A2 → A3 chain on one sequence.

The spatial compactness half is NOT in this package — it is supplied as an explicit
hypothesis to `torusAubinLionsPackage_of_galSeq` and discharged by `rellich_L2Sigma`. -/
structure AubinLionsPackage (F : Torus3NSForms) (ν T : ℝ) (u₀ : L2Sigma)
    (galSeq : ∀ n, GalerkinSolutionData F ν u₀ n) where
  /-- The strictly monotone extraction index. -/
  φ : ℕ → ℕ
  /-- Strict monotonicity of `φ`. -/
  φ_mono : StrictMono φ
  /-- The limit curve. -/
  u : Time → L2Sigma
  /-- **Strong `L²(0,T; L²_σ)` convergence** of the subsequence to the limit, in `eLpNorm`
  form.  MIRRORS the ℝ³ fix (`AubinLionsPackage_R3.strong_convergence`): the earlier Bochner
  `∫‖·‖²→0` form was "vacuous-shaped" (`integral_undef` collapses non-integrable integrands to
  `0`), so it could not certify genuine L²-in-time convergence / `MemLp` of the limit.  The
  `eLpNorm` form has no junk-`0` collapse and carries exactly the intended content; it
  strengthens the field's *statement* (the axiom's type) WITHOUT adding any axiom. -/
  strong_convergence :
    Filter.Tendsto
      (fun n => MeasureTheory.eLpNorm
        (fun t => ((galSeq (φ n)).u t : L2VF) - (u t : L2VF))
        2 (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)))
      Filter.atTop (nhds 0)
  /-- **AE strong measurability of the limit curve** `t ↦ (u t : L2VF)` on `[0,T]`.
  Matches the ℝ³ sibling `AubinLionsPackage_R3.u_aestronglyMeasurable`; it is a standard,
  true part of the Aubin–Lions conclusion (the limit of a bounded measurable sequence is
  measurable) and is needed by the density-free WeakFormNS limit passage
  (`TorusLimitPassage.lean`). -/
  u_aestronglyMeasurable :
    AEStronglyMeasurable (fun t => (u t : L2VF))
      (MeasureTheory.volume.restrict (Set.Icc 0 T))

-- NOTE: `aubin_lions` (former Axiom A2) was REMOVED in issue #23 (T-AL-6 Stage C).
-- Its content is now the proved def `torusAubinLionsPackage_of_galSeq` in
-- `LerayHopf/Torus/AubinLionsAssembly.lean`.  The `AubinLionsPackage` structure (above)
-- remains as the shared type; only the axiom that produced it is gone.

/-! ### Proof-carrying solution structures -/

/-- The **full Leray–Hopf solution** structure carrying genuine proof fields.

All fields are typed propositions (not `Prop` placeholders):
- `weak_eq`: the curve satisfies the weak NS identity against separated-variable tests
  `ψ(t)w(x)` with `w` ranging over `IsGalerkinTest` (the standard space-time test
  formulation is not derived from this; see `WeakFormNS`'s docstring),
- `energy_ineq`: the energy inequality holds for `t ∈ [0, T]`,
- `initial_trace`: the initial datum is attained in the strong L² sense as `t → 0⁺`
  (a one-sided trace at the initial time only; this is **not** a claim of weak
  continuity `u ∈ C_w([0,T]; L²_σ)` on the whole interval, which is not a field of
  this structure).

This structure carries actual proof obligations (not `Prop` placeholders) and is
produced by the assembly below.

**Energy class (v5 fix):** The `energy_class` field proof-carries that `u` lies in the
Leray–Hopf energy class: a.e. `memH1VF` on `[0, T]` and interval-integrable viscous
dissipation. This gives a.e.-in-time H¹ membership plus integrable dissipation — **not**
literal Bochner space membership `u ∈ L²(0,T;H¹_σ)`, since `u_aestronglyMeasurable` is
strong measurability into the ambient `L2VF`, not into `H¹` as a Banach space. Without
this field, `energy_ineq` could hold vacuously for `u ∉ H¹` because `viscousFormSq` is a
`tsum` that collapses off H¹. -/
abbrev LerayHopfSolutionFull (F : Torus3NSForms) (ν T : ℝ) (u₀ : L2Sigma) :=
  Galerkin.LerayHopfSolution torusDomain F.core ν T u₀

/-- The **full Galerkin compactness package** carrying genuine proof fields.

Produced by `build_galerkin_package_of_galSeq` (A2 with `rellich_L2Sigma` → proved limit
passage) from an explicit Galerkin sequence — for the capstone, the proved axiom-free
`galSeq_of_torus` (issue #24).

**Energy class (v5 fix):** The `energy_class_limit` field proof-carries that the limit
curve lies in the Leray–Hopf energy class: a.e. `memH1VF` on `[0, T]` and
interval-integrable viscous dissipation — a.e.-in-time H¹ membership plus integrable
dissipation, **not** literal Bochner membership `limit ∈ L²(0,T;H¹_σ)` (see the note on
`LerayHopfSolutionFull` above). Populated from the fifth conjunct of
`torus_galerkin_limit_passage_of_energyClass`. -/
abbrev GalerkinCompactnessPackageFull (F : Torus3NSForms) (ν T : ℝ) (u₀ : L2Sigma) :=
  Galerkin.CompactnessPackage torusDomain F.core ν T u₀

/-! ### Assembly theorems -/

/-! `build_galerkin_package_of_galSeq` (the core assembly, A2 → proved limit passage) has been
**relocated** to `LerayHopf/Torus/GalerkinODECapstone.lean` so that it can call the proved
theorems `torus_galerkin_limit_passage_of_energyClass` + `torus_energyClass_of_aubinLions`
(which are downstream of this file — keeping the def here would create an import cycle).
The former `build_galerkin_package` (A1 → A2 → A3, sourcing `galSeq` from the now-removed
`galerkin_ode_solution` axiom) has been **deleted** (issue #24).  The capstone
`exists_lerayHopf_torus3` routes through `build_galerkin_package_of_torus`
(`LerayHopf/Torus/GalerkinODECapstone.lean`), which feeds the axiom-free proved sequence
`galSeq_of_torus` into the relocated `build_galerkin_package_of_galSeq`. -/

/-- **Assembly:** A `GalerkinCompactnessPackageFull` yields `Nonempty (LerayHopfSolutionFull …)`. -/
theorem exists_lerayHopf_from_package_full (F : Torus3NSForms) (ν T : ℝ) (u₀ : L2Sigma)
    (pkg : GalerkinCompactnessPackageFull F ν T u₀) :
    Nonempty (LerayHopfSolutionFull F ν T u₀) :=
  Galerkin.exists_lerayHopf_from_package torusDomain F.core ν T u₀ pkg

/-! ### Main existence theorem (capstone) — relocated (issues #22, #24)

The capstone `exists_lerayHopf_torus3` now lives downstream in
`LerayHopf/Torus/GalerkinODECapstone.lean` (relocated again in issue #24).  It is rerouted through
the proved convection theorem `torusConvectionGap_exists` (via `torus3_NSForms_exists` /
`Torus3NSForms_of_gap`, issue #53) for the NS-forms witness, and through the proved axiom-free
`galSeq_of_torus` (issue #24) for the per-`n` Galerkin sequence — discharging the former
`galerkin_ode_solution` axiom.  The assembly machinery `exists_lerayHopf_from_package_full` stays here; `build_galerkin_package_of_galSeq`
was relocated to `LerayHopf/Torus/GalerkinODECapstone.lean` (to avoid an import cycle with the proved
limit-passage theorems).  Only the final capstone moved downstream in issue #24. -/

end LerayHopf
