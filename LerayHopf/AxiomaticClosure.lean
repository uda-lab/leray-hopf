import LerayHopf.EvolutionTriple
import LerayHopf.H1Sigma
import LerayHopf.EnergyEstimate
import LerayHopf.GalerkinProjection
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open MeasureTheory Filter Topology

/-!
# Axiomatic closure of Leray–Hopf existence on 𝕋³

**M6 — assembly + the remaining 2 axioms.**

This file closes the T³ Leray–Hopf existence proof by axiomatizing the analytic results that
remain out of reach in Lean (Aubin–Lions compactness and limit passage),
constructing the proof-carrying solution structures, and assembling the existence machinery.

**Issue #22 de-axiomatization:** The former fat axiom A4 `torus3_NSForms_exist` has been
**removed**.  `Nonempty Torus3NSForms` is now the theorem `torus3_NSForms_exists` in
`LerayHopf/TorusConvectionForm.lean`, derived sorry-free from the gap hypothesis via
`Torus3NSForms_of_gap`.  Issue #53 / PR #62 then proved `torusConvectionGap_exists` itself using
the determined-form construction in `TorusConvectionExtension.lean`.  The capstone
`exists_lerayHopf_torus3_axiomatic` is relocated downstream.

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
- `aubin_lions`                     : axiom — Aubin–Lions with spatial half discharged
- `galerkin_limit_passage`          : axiom — limit passage to weak NS solution (Temam III.3)
- `LerayHopfSolutionFull`           : proof-carrying Leray–Hopf solution structure
- `GalerkinCompactnessPackageFull`  : proof-carrying Galerkin compactness package
- `build_galerkin_package_of_galSeq` : assembly (axiom-free core) — chains A2 (with rellich_L2Sigma) → A3 from an explicit Galerkin sequence
- `exists_lerayHopf_from_package_full` : copies proofs from package to solution
- `exists_lerayHopf_torus3_axiomatic` : main existence theorem — RELOCATED to
  `TorusGalerkinODECapstone.lean` (issue #24), rerouted through the proved `galSeq_of_torus`

## Assumptions

Two axioms are added in this file (names below with one-line justifications).  The former
`torusConvectionGap_exists` project axiom has been **removed** (issue #53 / PR #62): it is now
the theorem re-exported from `TorusConvectionExtension.lean`, so the torus convection operator
contributes no project axioms to the capstone.  The former `galerkin_ode_solution` axiom has also
been **removed** (issue #24): the finite-dim torus Galerkin ODE is solved unconditionally by the
proved `galerkinSolutionData_torus` (`LerayHopf/TorusGalerkinODESolve.lean`), and the capstone is
rerouted through `galSeq_of_torus`.

1. `aubin_lions` — Aubin–Lions time compactness; the spatial half is an explicit hypothesis
   discharged by the proved `rellich_L2Sigma`, so this axiom covers ONLY the Bochner-time
   half.  TRUE: classical Aubin–Lions/Lions–Aubin.  Blocked by missing Bochner-Sobolev
   time-derivative bounds in Lean.  Temam III.2.1.

2. `galerkin_limit_passage` — passage from the strong-L²(0,T) subsequence to a weak NS
   solution satisfying the energy inequality and initial trace.  TRUE: strong L²(0,T)
   convergence kills the nonlinear error via Cauchy–Schwarz + the continuity bound; lsc
   energy; initial trace from energy + `velocityProjection_n_tendsto`.  Temam III.3.
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
`exists_lerayHopf_torus3_axiomatic` is relocated downstream and rerouted through
`torus3_NSForms_exists`.  Temam II.§1; RRS §3.2. -/

/-! ### Proved lemma: b u u u = 0 -/

/-- **b(u, u, u) = 0** follows purely from antisymmetry.

Proof: `b(u, u, u) = -b(u, u, u)` by `b_antisymm u u u`, so `b(u, u, u) = 0`. -/
theorem Torus3NSForms.b_self_zero (F : Torus3NSForms) (u : L2Sigma) :
    F.b u u u = 0 := by
  have h := F.b_antisymm u u u
  linarith

/-! ### Dissipative evolution from T³ NS forms (sorry-free) -/

/-- Build a `DissipativeEvolution` from a `Torus3NSForms`.

`H := L2Sigma`, with the `L2Sigma`-subspace instances.  The regularity functional is
`h1EnergySq ∘ (↑)`, viscous form is the concrete `stokesTestPairing`, convection form is `F.b`.

This construction is **sorry-free**.  The weak formulation tests against the Fourier/Galerkin
class `IsGalerkinTest`; density and fixed-test continuity support extension arguments, but the
current theorem statement itself is Galerkin-test based rather than quantified over all smooth
divergence-free tests. -/
noncomputable def torus3Evolution (F : Torus3NSForms) : DissipativeEvolution where
  H := L2Sigma
  instNACG := inferInstance
  instIPS := inferInstance
  instCS := inferInstance
  reg := fun u => h1EnergySq (u : L2VF)
  reg_nonneg := fun _ => h1EnergySq_nonneg _
  viscousForm := fun u w => stokesTestPairing (u : L2VF) (w : L2VF)
  convForm := F.b
  convForm_antisymm := F.b_antisymm
  isTest := fun w => IsGalerkinTest w

/-! ### Galerkin ODE solution data -/

/-- Data produced by the `n`-th Galerkin ODE on `Vₙ ⊆ L²_σ`.

Packages: the solution curve, initial condition, subspace-range property, differentiability,
the projected ODE, H¹ regularity, and uniform (n-independent) energy and regularity bounds.
Every field is used in the Aubin–Lions assembly (`aubin_lions`) or the limit passage
(`galerkin_limit_passage`). -/
structure GalerkinSolutionData (F : Torus3NSForms) (ν : ℝ) (u₀ : L2Sigma) (n : ℕ) where
  /-- The Galerkin solution curve. -/
  u : Time → L2Sigma
  /-- Initial condition: `u(0) = Pₙ u₀`. -/
  u_initial : u 0 = ⟨velocityProjection_n n (u₀ : L2VF),
    velocityProjection_n_preserves_L2Sigma n (u₀ : L2VF) u₀.2⟩
  /-- Range in `Vₙ`: the solution stays in the Galerkin subspace. -/
  u_inVn : ∀ t, (u t : L2VF) = velocityProjection_n n (u t : L2VF)
  /-- The curve `t ↦ (u t : L2VF)` is differentiable at every **forward** time `t ≥ 0`.

  SOUNDNESS (forward-only, issue #24): physical Galerkin solutions are confined by the forward
  energy bound `½‖u(t)‖² ≤ ½‖Pₙu₀‖²`, which controls the solution only for `t ≥ 0`.  This
  quadratic-in-`u` ODE field can blow up in finite *backward* time, so asserting the derivative
  for all `t : ℝ` was a latent over-strength claim (an un-physical guarantee that the global
  solver cannot honor — it would assert inhabitation of a generically-empty type).  Restricted to
  `0 ≤ t`, matching the merged ℝ³ sibling `GalerkinSolutionData_R3.u_hasDeriv`
  (`LerayHopf/R3/AxiomaticClosure.lean`). -/
  u_hasDeriv : ∀ t, 0 ≤ t → HasDerivAt (fun s => (u s : L2VF))
    (deriv (fun s => (u s : L2VF)) t) t
  /-- The projected Galerkin ODE at **forward** times `t ≥ 0`: for all `w ∈ Vₙ`,
  `⟪u'(t), w⟫ + ν · stokesTestPairing(u(t), w) + b(u(t), u(t), w) = 0`.

  SOUNDNESS (forward-only, issue #24): same rationale as `u_hasDeriv` — the ODE identity is only
  guaranteed on the forward time interval where the energy estimate confines the solution; the
  quadratic field blows up in finite backward time, so the all-`t` form was a latent over-strength
  claim.  Restricted to `0 ≤ t`, matching the merged ℝ³ sibling `GalerkinSolutionData_R3.u_ode`
  (`LerayHopf/R3/AxiomaticClosure.lean`). -/
  u_ode : ∀ t, 0 ≤ t → ∀ w : L2Sigma, (w : L2VF) = velocityProjection_n n (w : L2VF) →
    inner (𝕜 := ℝ) (deriv (fun s => (u s : L2VF)) t) (w : L2VF) +
    ν * stokesTestPairing (u t : L2VF) (w : L2VF) + F.b (u t) (u t) w = 0
  /-- H¹ regularity: the solution stays in H¹ (required for `rellich_L2Sigma` summability). -/
  reg_mem : ∀ t, memH1VF (u t : L2VF)
  /-- Uniform energy bound: `½‖u(t)‖² ≤ ½‖Pₙu₀‖²`. -/
  energy_bound : ∀ t, 0 ≤ t →
    (1 / 2 : ℝ) * ‖(u t : L2VF)‖ ^ 2 ≤
    (1 / 2 : ℝ) * ‖velocityProjection_n n (u₀ : L2VF)‖ ^ 2
  /-- Uniform (n-independent) regularity bound: `∫₀ᵀ h1EnergySq(u(t)) dt ≤ T‖u₀‖² + ‖u₀‖²/(2ν)`.
  The RHS is generous and n-independent; follows from integrating the energy identity.

  NOTE (scaling, unlike the ℝ³ `viscousFormSq_R3` field): here the integrand is the full
  `h1EnergySq u = ‖u‖²_{L²} + ∑ⱼ∑'ₖ(∑ᵢkᵢ²)‖ûⱼ(k)‖²`, which carries NO `ν` and NO `(2π)²`
  factor.  Decomposing, `∫₀ᵀ h1EnergySq(u t) = ∫₀ᵀ‖u t‖²_{L²} + (ν(2π)²)⁻¹ ∫₀ᵀ viscousFormSq ν (u t)`.
  By the energy identity `∫₀ᵀ‖u t‖²_{L²} ≤ T‖u₀‖²` and `∫₀ᵀ viscousFormSq ν (u t) ≤ ½‖u₀‖²`,
  the gradient part is `≤ ‖u₀‖²/(2ν(2π)²) ≤ ‖u₀‖²/(2ν)` (since `(2π)² ≥ 1`).  So this RHS is a
  TRUE upper bound (the `T‖u₀‖²` L²-part is needed; the `/(2ν)` gradient part is generous). -/
  reg_bound : ∀ T, 0 < T →
    ∫ t in (0 : ℝ)..T, h1EnergySq (u t : L2VF) ≤
    T * ‖(u₀ : L2VF)‖ ^ 2 + ‖(u₀ : L2VF)‖ ^ 2 / (2 * ν)

/-! ### A1: Galerkin ODE existence — DISCHARGED (issue #24)

The former `axiom galerkin_ode_solution : GalerkinSolutionData F ν u₀ n` has been **removed**.
The `n`-th finite-dimensional torus Galerkin ODE is now solved **unconditionally** by the proved
`galerkinSolutionData_torus` (`LerayHopf/TorusGalerkinODESolve.lean`), built over the finite-dim
real subspace `velocitySpan n` (`LerayHopf/TorusGalerkinScheme.lean`) via Picard–Lindelöf +
forward-global continuation (`forwardGlobalSolution_exists`) and the proved energy/dissipation
bounds.  The capstone `exists_lerayHopf_torus3_axiomatic` is rerouted through it via
`galSeq_of_torus` (`LerayHopf/TorusGalerkinODECapstone.lean`), dropping this axiom from its
`#print axioms`.  Mirrors the merged ℝ³ discharge of `galerkin_ode_solution_R3` (issue #10). -/

/-! ### Aubin–Lions compactness package -/

/-- Package produced by the Aubin–Lions theorem.

Carries: the extracted subsequence `φ`, its strict monotonicity, a limit curve
`u : Time → L2Sigma`, and **strong `L²(0,T; L²_σ)` convergence**: the time-integral of
the squared `L²_σ`-distance between the subsequence and the limit tends to `0`.

`galSeq` is a **structure parameter** (not a field), so the convergence statement is
type-enforced against the same sequence passed to `aubin_lions` and `galerkin_limit_passage`,
tying the A1 → A2 → A3 chain on one sequence.

The spatial compactness half is NOT in this package — it is supplied as an explicit
hypothesis to `aubin_lions` and discharged by `rellich_L2Sigma`. -/
structure AubinLionsPackage (F : Torus3NSForms) (ν T : ℝ) (u₀ : L2Sigma)
    (galSeq : ∀ n, GalerkinSolutionData F ν u₀ n) where
  /-- The strictly monotone extraction index. -/
  φ : ℕ → ℕ
  /-- Strict monotonicity of `φ`. -/
  φ_mono : StrictMono φ
  /-- The limit curve. -/
  u : Time → L2Sigma
  /-- **Strong `L²(0,T; L²_σ)` convergence** of the subsequence to the limit:
  `∫₀ᵀ ‖uₙ(t) - u(t)‖²_{L²_σ} dt → 0` along the subsequence `φ`. This is the genuine
  Aubin–Lions conclusion (NOT mere pointwise-in-time convergence) — it is exactly what
  the nonlinear limit passage in `galerkin_limit_passage` consumes.
  The convergence is stated against the PARAMETER `galSeq` (not an internal field),
  enforcing chain faithfulness. -/
  strong_convergence :
    Filter.Tendsto
      (fun n => ∫ t in (0 : ℝ)..T, ‖((galSeq (φ n)).u t : L2VF) - (u t : L2VF)‖ ^ 2)
      Filter.atTop (nhds 0)

/-! ### Axiom A2: Aubin–Lions (spatial half discharged by rellich_L2Sigma) -/

/-- **Axiom A2:** Aubin–Lions time compactness.

Takes the Galerkin sequence `galSeq`, its uniform bounds (from A1), and an explicit
spatial-compactness hypothesis `spatial` (whose type matches `rellich_L2Sigma`'s conclusion
exactly, so the assembly can pass `rellich_L2Sigma` directly).

This axiom covers ONLY the genuinely-missing Bochner-time compactness half.  The spatial
half is discharged by the proved `rellich_L2Sigma`, NOT axiomatized.

**The `spatial` hypothesis type is byte-identical to `rellich_L2Sigma`'s conclusion shape.**

**Precise remaining frontier (issue #23 audit, 2026-06-21).** The conclusion this axiom
must produce is the `AubinLionsPackage.strong_convergence` field, i.e. strong
`L²(0,T;L²_σ)` convergence of a subsequence:
`∫₀ᵀ ‖(galSeq (φ n)).u t − u t‖²_{L²_σ} dt → 0`.  This is the classical Lions–Aubin
time-compactness extraction and is NOT derivable from the currently-available lemmas:
* the proved `rellich_L2Sigma` gives the SPATIAL embedding only (compactness in space,
  pointwise in time);
* the Stream-D sublibrary (`aeStronglyMeasurable_of_spaceTimeL2`,
  `kineticEnergy_lsc_transfer`, `isWeakTimeDeriv_unique`, `W1pTime.ofHValuedDeriv`,
  `GelfandTriple.*`) supplies measurable-representative extraction and norm-lsc transfer
  *given* an already-`L²`-convergent sequence — it does NOT produce the relative
  compactness (the strongly-`L²(0,T;L²_σ)`-convergent subsequence) from the uniform
  `L²(0,T;H¹)` + time-derivative bounds.
The genuinely-missing pillar is the time-equicontinuity/Steklov interval-averaging
assembly: from the integrated `reg_bound` (NOT a pointwise H¹ bound), build the uniform
time modulus, Jensen-bound the Steklov averages' H¹ seminorm, feed `rellich_L2Sigma` at
the δ-mesh base-points, and diagonalize over δ→0 with a boundary-strip estimate.  The
strictly-more-built ℝ³ sibling `aubinLionsPackage_R3_of_timeCompactness`
(`R3/AubinLionsLimitPassage.lean`) — which is GIVEN a `TimeCompactnessInput` and has the
Steklov helpers proved axiom-free — STILL carries an open `sorry` for exactly this
`strong_convergence` centerpiece (its C2), so the torus side (which lacks even the
`TimeCompactnessInput` scaffolding) is not closer.  Axiom KEPT this cycle per the
no-fake-removal floor.  Temam III.2.1. -/
axiom aubin_lions -- ALLOW_AXIOM: Aubin–Lions time compactness; spatial half discharged by rellich_L2Sigma (proved); axiom adds only Bochner-time half; TRUE and MINIMAL; Temam III.2.1
    (F : Torus3NSForms) (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T)
    (u₀ : L2Sigma)
    (galSeq : ∀ n, GalerkinSolutionData F ν u₀ n)
    (spatial : ∀ (M : ℝ) (z : ℕ → L2VF),
      (∀ n, z n ∈ L2Sigma) →
      (∀ n, memH1VF (z n)) →
      (∀ n, h1EnergySq (z n) ≤ M ^ 2) →
      ∃ (ψ : ℕ → ℕ) (g : L2VF), StrictMono ψ ∧ g ∈ L2Sigma ∧
        Filter.Tendsto (fun n => z (ψ n)) Filter.atTop (nhds g)) :
    AubinLionsPackage F ν T u₀ galSeq

/-! ### Axiom A3: Galerkin limit passage -/

/-- **Axiom A3:** Galerkin limit passage (existential good representative).

Consumes the Galerkin sequence `galSeq` (the same sequence passed to `aubin_lions`) plus
the Aubin–Lions package `alPkg` (which is type-indexed by `galSeq`), and concludes that
a **good representative** `u` exists satisfying:
- a.e.-equality to the Aubin–Lions limit `alPkg.u`: `u t = alPkg.u t` for a.e. `t ∈ [0,T]`,
- `WeakFormNS`: `u` satisfies the weak NS equation,
- energy inequality: the Leray–Hopf energy inequality holds for `t ∈ [0, T]`,
- initial trace: `u(t) → u₀` in `L²_σ` as `t → 0⁺`,
- energy class: a.e. `memH1VF` on `[0, T]` and integrable viscous dissipation.

**Why existential?** The Aubin–Lions package `alPkg` pins `alPkg.u` only via
integral strong-convergence, which is blind to measure-zero modifications.  Pointwise
properties stated directly for `alPkg.u` would be false (a null-set spike can falsify
them).  Instead, A3 asserts the *existence* of a weakly-continuous (hence pointwise-good)
representative `u` that carries all five properties.  This is the standard construction:
select `u` as the weakly continuous representative of the strong-L² limit; it exists by
the Lebesgue–Besicovitch theorem and is unique in `L²(0,T;H¹_σ)`.

**A.e.-equality link (v7 fix):** The FIRST conjunct `∀ᵐ t …, u t = alPkg.u t` ties `u`
to the Aubin–Lions compactness limit `alPkg.u`, confirming that `u` is the good
representative OF that limit (not an unrelated standalone solution).  Both `u t` and
`alPkg.u t` are of type `L2Sigma`, so this is L2Sigma equality a.e. in time.
A3 upgrades `alPkg.u` (integral-level convergence, null-set blind) to a pointwise-good
representative; it does NOT assert a new, unrelated solution.

The explicit `galSeq` parameter (with `alPkg : AubinLionsPackage F ν T u₀ galSeq`)
type-enforces that A1 → A2 → A3 all operate on the **same** Galerkin sequence.

Strong L²(0,T) convergence from A2 kills the nonlinear error (Cauchy–Schwarz + `b_bound`);
the energy inequality passes by lower-semicontinuity of the L² norm on `[0,T]`; the initial
trace follows from the energy inequality and `velocityProjection_n_tendsto`.

**Energy class (proof-carry, v5 fix):** The fifth conjunct certifies that `u` lies in the
Leray–Hopf energy class: a.e. `memH1VF` on `[0, T]` (so `u ∈ L∞(0,T;L²_σ)
∩ L²(0,T;H¹_σ)`) and integrable viscous dissipation.  Both hold because the Galerkin
approximants satisfy `reg_mem` uniformly and the H¹ bounds pass to the limit.

Blocked in Lean by: nonlinear limit passage requires the `b_bound` estimate applied to
strong L² convergence (integration of product estimates).  Temam III.3. -/
axiom galerkin_limit_passage -- ALLOW_AXIOM: limit passage produces a GOOD REPRESENTATIVE of alPkg.u (a.e.-equal to the Aubin–Lions limit, NOT standalone existence); null-set-invariant; weakly-continuous representative exists in L²(0,T;H¹_σ); strong convergence kills nonlinear error; lsc energy; initial trace; energy class; Temam III.3
    (F : Torus3NSForms) (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T)
    (u₀ : L2Sigma)
    (galSeq : ∀ n, GalerkinSolutionData F ν u₀ n)
    (alPkg : AubinLionsPackage F ν T u₀ galSeq) :
    ∃ u : Time → L2Sigma,
    (∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc 0 T)), u t = alPkg.u t) ∧
    WeakFormNS ν T (torus3Evolution F) u ∧
    (∀ t, 0 ≤ t → t ≤ T →
      (1 / 2 : ℝ) * ‖(u t : L2VF)‖ ^ 2 +
      ∫ s in (0 : ℝ)..t, viscousFormSq ν (u s : L2VF) ≤
      (1 / 2 : ℝ) * ‖(u₀ : L2VF)‖ ^ 2) ∧
    Filter.Tendsto
      (fun t => (u t : L2VF))
      (nhdsWithin 0 (Set.Ici 0))
      (nhds (u₀ : L2VF)) ∧
    ((∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc 0 T)), memH1VF (u t : L2VF)) ∧
    IntervalIntegrable (fun s => viscousFormSq ν (u s : L2VF))
      MeasureTheory.volume 0 T)

/-! ### Proof-carrying solution structures -/

/-- The **full Leray–Hopf solution** structure carrying genuine proof fields.

All three fields are typed propositions (not `Prop` placeholders):
- `weak_eq`: the curve satisfies the weak NS identity for all test functions,
- `energy_ineq`: the energy inequality holds for all `t ≥ 0`,
- `initial_trace`: the initial datum is attained in the strong L² sense.

Compare with the scaffold `LerayHopfSolution` (in `Basic.lean`) which uses `Prop` fields;
this structure carries actual proof obligations and is produced by the assembly below.

**Energy class (v5 fix):** The `energy_class` field proof-carries that `u` lies in the
Leray–Hopf energy class: a.e. `memH1VF` on `[0, T]` (giving `u ∈ L²(0,T;H¹_σ)`) and
integrable viscous dissipation.  Without this field, `energy_ineq` could hold vacuously
for `u ∉ H¹` because `viscousFormSq` is a `tsum` that collapses off H¹. -/
structure LerayHopfSolutionFull (F : Torus3NSForms) (ν T : ℝ) (u₀ : L2Sigma) where
  /-- The solution curve. -/
  u : Time → L2Sigma
  /-- Weak NS equation (proof-carrying). -/
  weak_eq : WeakFormNS ν T (torus3Evolution F) u
  /-- Energy inequality (proof-carrying): holds for `t ∈ [0, T]`. -/
  energy_ineq : ∀ t, 0 ≤ t → t ≤ T →
    (1 / 2 : ℝ) * ‖(u t : L2VF)‖ ^ 2 +
    ∫ s in (0 : ℝ)..t, viscousFormSq ν (u s : L2VF) ≤
    (1 / 2 : ℝ) * ‖(u₀ : L2VF)‖ ^ 2
  /-- Initial trace: `u(t) → u₀` as `t → 0⁺` (proof-carrying). -/
  initial_trace : Filter.Tendsto
    (fun t => (u t : L2VF))
    (nhdsWithin 0 (Set.Ici 0))
    (nhds (u₀ : L2VF))
  /-- **Energy class (proof-carry, v5 fix):** `u` lies in the Leray–Hopf energy class:
  a.e. `memH1VF` on `[0, T]` (so `u ∈ L²(0,T;H¹_σ)`) and the viscous dissipation
  `∫₀ᵀ viscousFormSq ν (u s) ds` is integrable.  This prevents `viscousFormSq` from
  collapsing to zero off H¹ on a positive-measure set, making `energy_ineq` non-vacuous. -/
  energy_class : (∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc 0 T)), memH1VF (u t : L2VF)) ∧
    IntervalIntegrable (fun s => viscousFormSq ν (u s : L2VF)) MeasureTheory.volume 0 T

/-- The **full Galerkin compactness package** carrying genuine proof fields.

Produced by `build_galerkin_package_of_galSeq` (A2 with `rellich_L2Sigma` → A3) from an explicit
Galerkin sequence — for the capstone, the proved axiom-free `galSeq_of_torus` (issue #24).

**Energy class (v5 fix):** The `energy_class_limit` field proof-carries that the limit
curve lies in the Leray–Hopf energy class: a.e. `memH1VF` on `[0, T]` (giving
`limit ∈ L²(0,T;H¹_σ)`) and integrable viscous dissipation.  Populated directly from
the fourth conjunct of `galerkin_limit_passage`. -/
structure GalerkinCompactnessPackageFull (F : Torus3NSForms) (ν T : ℝ) (u₀ : L2Sigma) where
  /-- The limit curve. -/
  limit : Time → L2Sigma
  /-- Weak NS equation for the limit. -/
  weak_eq_limit : WeakFormNS ν T (torus3Evolution F) limit
  /-- Energy inequality for the limit: holds for `t ∈ [0, T]`. -/
  energy_ineq_limit : ∀ t, 0 ≤ t → t ≤ T →
    (1 / 2 : ℝ) * ‖(limit t : L2VF)‖ ^ 2 +
    ∫ s in (0 : ℝ)..t, viscousFormSq ν (limit s : L2VF) ≤
    (1 / 2 : ℝ) * ‖(u₀ : L2VF)‖ ^ 2
  /-- Initial trace for the limit. -/
  initial_trace_limit : Filter.Tendsto
    (fun t => (limit t : L2VF))
    (nhdsWithin 0 (Set.Ici 0))
    (nhds (u₀ : L2VF))
  /-- **Energy class (proof-carry, v5 fix):** the limit curve `limit` lies in the
  Leray–Hopf energy class: a.e. `memH1VF` on `[0, T]` (so `limit ∈ L²(0,T;H¹_σ)`)
  and the viscous dissipation is integrable.  Prevents `viscousFormSq` from collapsing
  off H¹, making `energy_ineq_limit` non-vacuous. -/
  energy_class_limit : (∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc 0 T)),
      memH1VF (limit t : L2VF)) ∧
    IntervalIntegrable (fun s => viscousFormSq ν (limit s : L2VF)) MeasureTheory.volume 0 T

/-! ### Assembly theorems -/

/-- **Assembly (axiom-free core).**  Build a `GalerkinCompactnessPackageFull` from an
EXPLICIT Galerkin sequence `galSeq`, chaining A2 (with `rellich_L2Sigma`) → A3.

This is the body of `build_galerkin_package` factored from Step 2 onward (issue #24): it takes
`galSeq` as a parameter instead of producing it via the `galerkin_ode_solution` axiom, so it
carries NO dependency on A1.  Every downstream consumer (`aubin_lions`,
`galerkin_limit_passage`, the whole packing) is unchanged; only the source of `galSeq` is lifted
out.  Routing the capstone through this builder with a concrete, axiom-free `galSeq` is what
discharges `galerkin_ode_solution`.

The steps are:
1. Apply `aubin_lions` (A2) with `spatial := rellich_L2Sigma` to get the Aubin–Lions package.
2. Apply `galerkin_limit_passage` (A3) to get the weak equation + energy inequality + initial trace.
3. Pack into `GalerkinCompactnessPackageFull`. -/
noncomputable def build_galerkin_package_of_galSeq (F : Torus3NSForms) (ν : ℝ) (hν : 0 < ν)
    (T : ℝ) (hT : 0 < T) (u₀ : L2Sigma)
    (galSeq : ∀ n, GalerkinSolutionData F ν u₀ n) :
    GalerkinCompactnessPackageFull F ν T u₀ := by
  -- Step 1 (A2): Aubin–Lions, with the spatial half discharged by `rellich_L2Sigma`.
  have alPkg : AubinLionsPackage F ν T u₀ galSeq :=
    aubin_lions F ν hν T hT u₀ galSeq rellich_L2Sigma
  -- Step 2 (A3): limit passage to the good representative.  The goal is a `Type`
  -- (a structure), so the existential is unpacked with `Exists.choose` rather than
  -- `obtain` (which only eliminates into `Prop`).  The a.e.-link conjunct
  -- (`hspec.1`) is intentionally discarded.
  have hex := galerkin_limit_passage F ν hν T hT u₀ galSeq alPkg
  have hspec := hex.choose_spec
  -- Step 3: pack into the proof-carrying structure.
  exact
    { limit := hex.choose
      weak_eq_limit := hspec.2.1
      energy_ineq_limit := hspec.2.2.1
      initial_trace_limit := hspec.2.2.2.1
      energy_class_limit := hspec.2.2.2.2 }

/-! The former `build_galerkin_package` (A1 → A2 → A3, sourcing `galSeq` from the now-removed
`galerkin_ode_solution` axiom) has been **deleted** (issue #24).  The capstone
`exists_lerayHopf_torus3_axiomatic` now routes through `build_galerkin_package_of_torus`
(`LerayHopf/TorusGalerkinODECapstone.lean`), which feeds the axiom-free proved sequence
`galSeq_of_torus` into `build_galerkin_package_of_galSeq` directly. -/

/-- **Assembly:** A `GalerkinCompactnessPackageFull` yields `Nonempty (LerayHopfSolutionFull …)`. -/
theorem exists_lerayHopf_from_package_full (F : Torus3NSForms) (ν T : ℝ) (u₀ : L2Sigma)
    (pkg : GalerkinCompactnessPackageFull F ν T u₀) :
    Nonempty (LerayHopfSolutionFull F ν T u₀) := by
  exact
    ⟨{ u := pkg.limit
       weak_eq := pkg.weak_eq_limit
       energy_ineq := pkg.energy_ineq_limit
       initial_trace := pkg.initial_trace_limit
       energy_class := pkg.energy_class_limit }⟩

/-! ### Main existence theorem (axiomatic) — relocated (issues #22, #24)

The capstone `exists_lerayHopf_torus3_axiomatic` now lives downstream in
`LerayHopf/TorusGalerkinODECapstone.lean` (relocated again in issue #24).  It is rerouted through
the proved convection theorem `torusConvectionGap_exists` (via `torus3_NSForms_exists` /
`Torus3NSForms_of_gap`, issue #53) for the NS-forms witness, and through the proved axiom-free
`galSeq_of_torus` (issue #24) for the per-`n` Galerkin sequence — discharging the former
`galerkin_ode_solution` axiom.  The assembly machinery it uses
(`build_galerkin_package_of_galSeq`, `exists_lerayHopf_from_package_full`) stays here; only the
final capstone moved, because both the convection construction and the proved solver are downstream
of this file. -/

end LerayHopf
