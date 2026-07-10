import LerayHopf.EvolutionTriple
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
Every field is used in the Aubin–Lions assembly (`torusAubinLionsPackage_of_galSeq`, proved;
formerly the `aubin_lions` axiom, removed issue #23) or the proved limit passage
(`torus_galerkin_limit_passage_of_energyClass`). -/
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
  (`LerayHopf/R3/SolutionInterfaces.lean`). -/
  u_hasDeriv : ∀ t, 0 ≤ t → HasDerivAt (fun s => (u s : L2VF))
    (deriv (fun s => (u s : L2VF)) t) t
  /-- The projected Galerkin ODE at **forward** times `t ≥ 0`: for all `w ∈ Vₙ`,
  `⟪u'(t), w⟫ + ν · stokesTestPairing(u(t), w) + b(u(t), u(t), w) = 0`.

  SOUNDNESS (forward-only, issue #24): same rationale as `u_hasDeriv` — the ODE identity is only
  guaranteed on the forward time interval where the energy estimate confines the solution; the
  quadratic field blows up in finite backward time, so the all-`t` form was a latent over-strength
  claim.  Restricted to `0 ≤ t`, matching the merged ℝ³ sibling `GalerkinSolutionData_R3.u_ode`
  (`LerayHopf/R3/SolutionInterfaces.lean`). -/
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
  /-- **Time-measurability (proof-carry):** the solution curve `t ↦ (u t : L2VF)` is
  `AEStronglyMeasurable` for the Lebesgue measure restricted to `[0, T]`.  This is the
  Bochner-measurability half of the textbook Leray–Hopf class `u ∈ L∞(0,T;H) ∩ L²(0,T;V)`;
  without it a non-measurable curve could satisfy `weak_eq` vacuously (the `WeakFormNS`
  interval integral collapses to junk-`0` off the measurable class).  It is inherited from
  the Aubin–Lions limit `AubinLionsPackage.u_aestronglyMeasurable` through the a.e.-link
  (`u t = alPkg.u t` a.e. on `[0, T]`) of the good representative. -/
  u_aestronglyMeasurable :
    AEStronglyMeasurable (fun t => (u t : L2VF))
      (MeasureTheory.volume.restrict (Set.Icc 0 T))

/-- The **full Galerkin compactness package** carrying genuine proof fields.

Produced by `build_galerkin_package_of_galSeq` (A2 with `rellich_L2Sigma` → proved limit
passage) from an explicit Galerkin sequence — for the capstone, the proved axiom-free
`galSeq_of_torus` (issue #24).

**Energy class (v5 fix):** The `energy_class_limit` field proof-carries that the limit
curve lies in the Leray–Hopf energy class: a.e. `memH1VF` on `[0, T]` (giving
`limit ∈ L²(0,T;H¹_σ)`) and integrable viscous dissipation.  Populated from the fifth
conjunct of `torus_galerkin_limit_passage_of_energyClass`. -/
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
  /-- **Time-measurability (proof-carry):** the limit curve `t ↦ (limit t : L2VF)` is
  `AEStronglyMeasurable` for the Lebesgue measure restricted to `[0, T]`, inherited from
  `AubinLionsPackage.u_aestronglyMeasurable` through the good-representative a.e.-link. -/
  u_aestronglyMeasurable_limit :
    AEStronglyMeasurable (fun t => (limit t : L2VF))
      (MeasureTheory.volume.restrict (Set.Icc 0 T))

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
    Nonempty (LerayHopfSolutionFull F ν T u₀) := by
  exact
    ⟨{ u := pkg.limit
       weak_eq := pkg.weak_eq_limit
       energy_ineq := pkg.energy_ineq_limit
       initial_trace := pkg.initial_trace_limit
       energy_class := pkg.energy_class_limit
       u_aestronglyMeasurable := pkg.u_aestronglyMeasurable_limit }⟩

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
