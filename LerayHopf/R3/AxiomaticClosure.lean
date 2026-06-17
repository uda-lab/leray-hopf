import LerayHopf.EvolutionTriple
import LerayHopf.R3.Regularity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open MeasureTheory Filter Topology LineDeriv

/-!
# Axiomatic closure of Leray–Hopf existence on ℝ³

**Milestone R3-c — ℝ³ axiomatic closure.**

Port of the Codex-approved T³ `LerayHopf/AxiomaticClosure.lean` to the whole-space
setting, reusing `DissipativeEvolution`, `WeakFormNS`, and `Time` verbatim.
The T³ 8-round audit lessons are baked in preemptively.

## Architecture

Six axioms are added in this file.  Two extra (vs. T³) are exactly the two pieces
T³ PROVED but ℝ³ cannot:

- **AX-G `r3GalerkinScheme_exists`** — the approximation-projection family
  (replaces T³'s proved `velocityProjection_n`).
- **AX-SC `spatial_compactness_R3`** — spatial compactness LOCAL form
  (local Rellich H¹(B_R)↪↪L²(B_R); replaces T³'s proved `rellich_L2Sigma`;
  Rellich FAILS globally on ℝ³ but LOCAL convergence on every ball is TRUE without
  tightness).

The remaining four axioms mirror the T³ ones:

- **AX-4 `r3_NSForms_exist`** — the ℝ³ convection form.
- **AX-1 `galerkin_ode_solution_R3`** — Galerkin ODE global solution.
- **AX-2 `aubin_lions_R3`** — Aubin–Lions time compactness.
- **AX-3 `galerkin_limit_passage_R3`** — limit passage to weak NS solution.

`𝔊 : R3GalerkinScheme` is threaded as a parameter throughout (cleaner than
`.some` noise).

**Non-vacuity:** `r3_NSForms_exist.b_galerkin` pins `b` to `convIntegralSchwartz`
(the genuine `∑_{i,a} ∫ u_a (∂_a v_i) w_i` Schwartz convection integral, sorry-free)
on fields that have component-wise Schwartz representatives.  This is a faithful pin:
`b = 0` fails since `convIntegralSchwartz` is the genuine convection form, not a
calibration constant, and does not vanish on all Schwartz triples.

**v4 de-axiomatization lesson applied:** The viscous (Stokes) form is the concrete
`stokesTestPairing_R3` — NOT axiomatized — for all `u : L2VF_R3`.

## Main definitions and theorems

- `R3GalerkinScheme`                 : structure bundling the approximation-projection family
- `r3GalerkinScheme_exists`          : axiom — existence of `R3GalerkinScheme`
- `IsGalerkinTest_R3`                : test-function predicate for ℝ³
- `convIntegralSchwartz`             : genuine `∑_{i,a} ∫ u_a (∂_a v_i) w_i` convection integral on Schwartz fields (defined in `DivergenceFree.lean`)
- `R3NSForms`                        : structure bundling the ℝ³ NS convection form
- `r3_NSForms_exist`                 : axiom — existence of `R3NSForms`
- `R3NSForms.b_self_zero`            : proved lemma — `b u u u = 0` from antisymmetry
- `r3Evolution`                      : `DissipativeEvolution` built from `R3GalerkinScheme` + `R3NSForms`
- `GalerkinSolutionData_R3`          : structure for the n-th Galerkin ODE solution on ℝ³
- `galerkin_ode_solution_R3`         : axiom — Picard–Lindelöf on finite-dim approximation space
- `spatial_compactness_R3`           : axiom — ℝ³ spatial compactness LOCAL (ball-restricted, no tightness)
- `AubinLionsPackage_R3`             : structure carrying the compactness subsequence
- `aubin_lions_R3`                   : axiom — Aubin–Lions with spatial half = `spatial_compactness_R3`
- `galerkin_limit_passage_R3`        : axiom — limit passage to weak NS solution
- `LerayHopfSolutionFull_R3`         : proof-carrying Leray–Hopf solution structure
- `GalerkinCompactnessPackageFull_R3`: proof-carrying Galerkin compactness package
- `build_galerkin_package_R3`        : assembly — chains A1 → A2 (spatial_compactness_R3) → A3
- `exists_lerayHopf_from_package_full_R3` : lifts a package to `Nonempty (LerayHopfSolutionFull_R3 …)`
- `exists_lerayHopf_r3`              : main existence theorem

## Assumptions

Six axioms are added in this file (names below with justifications):

1. `r3GalerkinScheme_exists` — existence of a Galerkin approximation-projection family
   on `L²_σ(ℝ³)` with smooth (Schwartz) range (e.g. frequency-ball truncation or smooth
   Hermite/mollification basis). The `range_schwartz` field excludes `P = id` (L² ⊄
   Schwartz), ensuring every Galerkin test field is Schwartz so `b_bound` and `reg_mem`
   are non-vacuous.  The `tendsto_id` field is RESTRICTED to `u ∈ L2Sigma_R3` (strong
   convergence on the divergence-free subspace only): a divergence-free Galerkin scheme is
   total only in `L²_σ(ℝ³)`, never in all of `L²(ℝ³; ℝ³)`, so an unrestricted
   `∀ u : L2VF_R3` form was a latent over-strength (Codex-confirmed) and has been removed;
   every consumer applies `P n` only to div-free data. TRUE classically (Paley–Wiener;
   smooth Galerkin bases exist); blocked in Lean by the missing indicator Fourier-multiplier
   on Lp. Lemarié-Rieusset §2.  See `LerayHopf/R3/GalerkinScheme.lean`
   (`nonempty_r3GalerkinScheme_of_basis`) for the axiom-free constructive witness of this
   structure from a single density hypothesis.

2. `r3_NSForms_exist` — existence of the ℝ³ NS convection form `b`. The genuine
   `∫(u·∇)v·w` form witnesses it; non-vacuity pinned via `b_galerkin` to
   `convIntegralSchwartz` (the genuine `∑_{i,a} ∫ u_a (∂_a v_i) w_i`, sorry-free).
   The `b_bound` field is over the **canonical `IsSchwartzDivFree_R3` test class**
   (‖∇w‖_∞ < ∞ for Schwartz w), matching the test predicate in `r3Evolution`.
   Blocked by missing `(u·∇)v` operator on L²(ℝ³) and integration by parts on ℝ³.
   Temam II.§1; Lemarié-Rieusset §5.

3. `galerkin_ode_solution_R3` — Picard–Lindelöf on the finite-dimensional approximation
   subspace + uniform energy and regularity bounds. TRUE; blocked by missing Galerkin
   ODE solver and missing concrete `(u·∇)v`. Temam III.3, Theorem 3.1.

4. `spatial_compactness_R3` — ℝ³ LOCAL spatial compactness = local Rellich
   H¹(B_R)↪↪L²(B_R). Concludes convergence on every ball B_R (NOT global strong L²(ℝ³));
   no tightness premise required. TRUE; blocked by local Rellich + ball-restricted
   integrals not in mathlib. Leray 1934; Lemarié-Rieusset §6.

5. `aubin_lions_R3` — Aubin–Lions time compactness; spatial half supplied as the
   LOCAL `spatial_compactness_R3` hypothesis (ball-restricted convergence, no tightness).
   Axiom covers only the Bochner-time half. TRUE; blocked by missing Bochner-Sobolev
   time-derivative bounds. Temam III.2.1.

6. `galerkin_limit_passage_R3` — limit passage from the strong-L²(0,T) subsequence to a
   weak NS solution with energy inequality, initial trace, and energy class. TRUE; blocked
   by the nonlinear limit passage via `b_bound`. Temam III.3.
-/

namespace LerayHopf

/-! ### AX-G: Galerkin approximation-projection scheme on L²_σ(ℝ³) -/

/-- The Galerkin approximation-projection family on `L²(ℝ³; ℝ³)`.

Bundles the `n`-indexed family of continuous projectors `P n : L2VF_R3 →L[ℝ] L2VF_R3`
with the five key properties needed for the Galerkin construction:

- `preserves_sigma`: each `P n` maps `L2Sigma_R3` into itself (the approximation respects
  the divergence-free constraint; follows for frequency-ball truncation or mollification);
- `tendsto_id`: `P n u → u` in `L²` as `n → ∞` **for every `u ∈ L2Sigma_R3`** (strong
  convergence of the approximation on the divergence-free subspace; Paley–Wiener
  approximation theory).  The convergence is RESTRICTED to `L2Sigma_R3`: a divergence-free
  Galerkin scheme is total only in `L²_σ(ℝ³)`, never in all of `L²(ℝ³; ℝ³)` (its prefix-span
  projections land in the closed div-free subspace, so an unrestricted `∀ u : L2VF_R3` form
  would force every `u` to be divergence-free — a latent over-strength, Codex-confirmed).
  Every consumer applies `P n` only to div-free data, so the Σ-restriction is exactly what
  the Leray–Hopf assembly needs;
- `norm_le`: `‖P n u‖ ≤ ‖u‖` (non-expansiveness; follows e.g. from the fact that `P n` is
  the L² projection onto a subspace);
- `idem`: `P n ∘ P n = P n` (idempotence; `P n` is a projection);
- `range_schwartz`: every element of the range of `P n` has Schwartz component
  representatives (excludes `P = id` since `L²(ℝ³) ⊄ Schwartz(ℝ³)`; ensures every
  `IsGalerkinTest_R3` field is Schwartz so `b_bound` and `reg_mem`/H¹ apply). -/
structure R3GalerkinScheme where
  /-- The n-th approximation projector. -/
  P : ℕ → (L2VF_R3 →L[ℝ] L2VF_R3)
  /-- P n preserves the divergence-free subspace. -/
  preserves_sigma : ∀ (n : ℕ) (u : L2VF_R3), u ∈ L2Sigma_R3 → P n u ∈ L2Sigma_R3
  /-- Strong convergence on the divergence-free subspace: `P n u → u` in `L²` for every
  `u ∈ L2Sigma_R3`.  The Σ-restriction is mathematically necessary — a div-free Galerkin
  scheme is total only in `L²_σ(ℝ³)`, not in all of `L²(ℝ³; ℝ³)` — and is exactly the
  range used by every consumer (`P n` is only ever applied to div-free data). -/
  tendsto_id : ∀ (u : L2VF_R3), u ∈ L2Sigma_R3 →
    Filter.Tendsto (fun n => P n u) Filter.atTop (nhds u)
  /-- Non-expansiveness: ‖P n u‖ ≤ ‖u‖. -/
  norm_le : ∀ (n : ℕ) (u : L2VF_R3), ‖P n u‖ ≤ ‖u‖
  /-- Idempotence: P n (P n u) = P n u. -/
  idem : ∀ (n : ℕ) (u : L2VF_R3), P n (P n u) = P n u
  /-- **Range regularity (Schwartz):** every element in the range of `P n` has component-wise
  Schwartz representatives.  Concretely: for every `n` and `u : L2VF_R3`, there exist
  Schwartz functions `ψ : Fin 3 → 𝓢(Domain3, ℝ)` such that the `j`-th component of
  `P n u` equals `(ψ j).toLp 2 volume`.

  This field excludes `P n = id` (since L²(ℝ³) ⊄ Schwartz(ℝ³)); as a consequence every
  `IsGalerkinTest_R3 𝔊 w` field is component-wise Schwartz, making `b_bound` (smooth-test
  bound) and `reg_mem` (H¹ regularity) non-vacuous.  Smooth/Hermite Galerkin bases
  satisfy this. -/
  range_schwartz : ∀ (n : ℕ) (u : L2VF_R3),
    ∃ (ψ : Fin 3 → SchwartzMap Domain3 ℝ),
    ∀ j : Fin 3,
      L2VF_projComponent_R3 j (P n u) =
        (ψ j).toLp 2 (volume : Measure Domain3)

/-- **Axiom AX-G:** A Galerkin approximation-projection family on `L²_σ(ℝ³)` exists. -/
axiom r3GalerkinScheme_exists : Nonempty R3GalerkinScheme -- ALLOW_AXIOM: existence of a Galerkin approximation-projection family on L²_σ(ℝ³) with SMOOTH (Schwartz) range (e.g. frequency-ball truncation / smooth Hermite basis); range_schwartz excludes P=id (L²⊄Schwartz) ensuring IsGalerkinTest fields are Schwartz, making b_bound and reg_mem non-vacuous; TRUE classically (Paley–Wiener; smooth Galerkin bases exist); blocked in Lean by the missing indicator Fourier-multiplier on Lp; Lemarié-Rieusset §2

/-! ### Galerkin test predicate for ℝ³ -/

/-- A vector `w ∈ L²_σ(ℝ³)` is a **Galerkin test function** (relative to scheme `𝔊`) if
it is a fixed point of some approximation projector:
  `IsGalerkinTest_R3 𝔊 w ↔ ∃ n, 𝔊.P n (w : L2VF_R3) = (w : L2VF_R3)`.

Mirrors `IsGalerkinTest` on T³.  Every element of the range of `𝔊.P n` satisfies this.
The class is dense in `L²_σ(ℝ³)` (by `𝔊.tendsto_id`, the Σ-restricted strong convergence)
and is the standard Faedo–Galerkin
test class used in the weak NS formulation. -/
def IsGalerkinTest_R3 (𝔊 : R3GalerkinScheme) (w : L2Sigma_R3) : Prop :=
  ∃ n : ℕ, 𝔊.P n (w : L2VF_R3) = (w : L2VF_R3)

/-! ### AX-4: ℝ³ Navier–Stokes forms structure -/

/-- The bundle of ℝ³ Navier–Stokes forms: only the trilinear convection form `b`
(the viscous form is the concrete `stokesTestPairing_R3`, NOT axiomatized).

Mirrors `Torus3NSForms` with `L2Sigma_R3` in place of `L2Sigma`.  The `𝔊 : R3GalerkinScheme`
parameter is threaded so that `b_galerkin` can pin `b` to `convIntegralSchwartz` via the
Galerkin range's Schwartz structure.

**Non-vacuity:** `b_galerkin` pins `b` to `convIntegralSchwartz` (the genuine
`∑_{i,a} ∫ u_a (∂_a v_i) w_i` convection integral) on Schwartz div-free fields.
This excludes `b := 0` since `convIntegralSchwartz ≢ 0` on a concrete Schwartz triple.

**Antisymmetry convention:** `b u v w = -b u w v` (skew in the last two slots).

**Smooth-test convection bound:** For a **canonical Schwartz divergence-free** test `w`
(`IsSchwartzDivFree_R3 w`), `|b(u,v,w)| ≤ C(w)·‖u‖·‖v‖`.  This uses the full
(scheme-independent) test class, matching the weak NS formulation in `r3Evolution`. -/
structure R3NSForms (𝔊 : R3GalerkinScheme) where
  /-- The trilinear convection form `b : L²_σ(ℝ³) × L²_σ(ℝ³) × L²_σ(ℝ³) → ℝ`. -/
  b : L2Sigma_R3 → L2Sigma_R3 → L2Sigma_R3 → ℝ
  /-- Antisymmetry in the last two slots: `b u v w = -b u w v`. -/
  b_antisymm : ∀ (u v w : L2Sigma_R3), b u v w = - b u w v
  /-- Additivity in the first slot. -/
  b_add_1 : ∀ (u u' v w : L2Sigma_R3), b (u + u') v w = b u v w + b u' v w
  /-- Additivity in the second slot. -/
  b_add_2 : ∀ (u v v' w : L2Sigma_R3), b u (v + v') w = b u v w + b u v' w
  /-- Additivity in the third slot. -/
  b_add_3 : ∀ (u v w w' : L2Sigma_R3), b u v (w + w') = b u v w + b u v w'
  /-- ℝ-homogeneity in the first slot. -/
  b_smul_1 : ∀ (c : ℝ) (u v w : L2Sigma_R3), b (c • u) v w = c * b u v w
  /-- ℝ-homogeneity in the second slot. -/
  b_smul_2 : ∀ (c : ℝ) (u v w : L2Sigma_R3), b u (c • v) w = c * b u v w
  /-- ℝ-homogeneity in the third slot. -/
  b_smul_3 : ∀ (c : ℝ) (u v w : L2Sigma_R3), b u v (c • w) = c * b u v w
  /-- **Smooth-test convection bound:** For a Schwartz divergence-free test `w`, the
  convection form is L²-bounded in the first two slots:
  `|b(u,v,w)| ≤ C(w) · ‖u‖_{L²} · ‖v‖_{L²}`.
  TRUE: `b(u,v,w) = -∫(u·∇)w·v`, so `|b| ≤ ‖∇w‖_∞ ‖u‖_{L²} ‖v‖_{L²}` with
  `‖∇w‖_∞ < ∞` for `IsSchwartzDivFree_R3 w` (Schwartz functions have all derivatives
  bounded).  Correct shape for strong-L²(0,T) convergence in the nonlinear limit passage.
  This covers the CANONICAL test class used in the weak NS formulation. -/
  b_bound : ∀ (w : L2Sigma_R3), IsSchwartzDivFree_R3 w →
    ∃ C : ℝ, ∀ (u v : L2Sigma_R3),
      |b u v w| ≤ C * ‖(u : L2VF_R3)‖ * ‖(v : L2VF_R3)‖
  /-- **Non-vacuity pin (genuine):** `b` agrees with `convIntegralSchwartz` on L²_σ fields
  that are component-wise represented by Schwartz witnesses (via `L2VF_projComponent_R3`).

  Concretely: given `ψu ψv ψw : Fin 3 → 𝓢(Domain3, ℝ)` such that each component projection
  `L2VF_projComponent_R3 j (u : L2VF_R3) = (ψu j).toLp 2 volume` (and similarly for `v`, `w`),
  we require `b u v w = convIntegralSchwartz ψu ψv ψw`.

  This is the **faithful** non-vacuity pin: `convIntegralSchwartz` is the genuine
  `∑_{i,a} ∫ u_a (∂_a v_i) w_i` convection integral (not a calibration constant), so
  `b = 0` is excluded (the genuine convection form does not vanish on all Schwartz triples).
  The Schwartz div-free set is dense in `L²_σ(ℝ³)`, so the pin constrains `b` on a dense
  subset — sufficient for faithfulness. -/
  b_galerkin : ∀ (ψu ψv ψw : Fin 3 → SchwartzMap Domain3 ℝ)
    (u v w : L2Sigma_R3),
    (∀ j : Fin 3,
      L2VF_projComponent_R3 j (u : L2VF_R3) =
        (ψu j).toLp 2 (volume : Measure Domain3)) →
    (∀ j : Fin 3,
      L2VF_projComponent_R3 j (v : L2VF_R3) =
        (ψv j).toLp 2 (volume : Measure Domain3)) →
    (∀ j : Fin 3,
      L2VF_projComponent_R3 j (w : L2VF_R3) =
        (ψw j).toLp 2 (volume : Measure Domain3)) →
    b u v w = convIntegralSchwartz ψu ψv ψw

/-! ### Axiom AX-4: ℝ³ NS forms exist -/

/-- **Axiom AX-4:** The ℝ³ Navier–Stokes convection form exists.

The genuine convection form `b(u,v,w) = ∫_{ℝ³} ((u·∇)v)·w` is a witness:
- Antisymmetry: integration by parts + `div u = 0` gives `b u v w = -b u w v`.
- Trilinearity: the genuine form is multilinear.
- Smooth-test bound: `b(u,v,w) = -∫(u·∇)w·v`, so `|b| ≤ ‖∇w‖_∞ ‖u‖_{L²} ‖v‖_{L²}`
  with `‖∇w‖_∞ < ∞` for any `IsSchwartzDivFree_R3 w` (Schwartz functions have bounded
  derivatives).
- Schwartz pin: `b` equals `convIntegralSchwartz ψu ψv ψw` on fields with Schwartz
  component representatives (the genuine `∑_{i,a} ∫ u_a (∂_a v_i) w_i` form).

NOTE: The viscous form is NOT axiomatized — it is the concrete `stokesTestPairing_R3`.

Blocked in Lean by: missing `(u·∇)v` operator on L²(ℝ³) + integration by parts on ℝ³.
Temam II.§1; Lemarié-Rieusset §5. -/
axiom r3_NSForms_exist (𝔊 : R3GalerkinScheme) : Nonempty (R3NSForms 𝔊) -- ALLOW_AXIOM: ℝ³ NS convection form b exists (b=convIntegralSchwartz on Schwartz-component fields, trilinear, b_bound over canonical IsSchwartzDivFree_R3 test class via b=-∫(u·∇)w·v, ‖∇w‖_∞<∞ for Schwartz w); viscous form is concrete stokesTestPairing_R3 (NOT axiomatized); TRUE (genuine (u·∇)v form witnesses); NON-VACUOUS (b=0 fails b_galerkin since convIntegralSchwartz is genuine convection ≢ 0); Temam II.§1; Lemarié-Rieusset §5

/-! ### Proved lemma: b u u u = 0 -/

/-- **b(u, u, u) = 0** follows purely from antisymmetry.

Proof: `b(u, u, u) = -b(u, u, u)` by `b_antisymm u u u`, so `b(u, u, u) = 0`. -/
theorem R3NSForms.b_self_zero {𝔊 : R3GalerkinScheme} (F : R3NSForms 𝔊) (u : L2Sigma_R3) :
    F.b u u u = 0 := by
  have h := F.b_antisymm u u u
  linarith

/-! ### Dissipative evolution from ℝ³ NS forms (sorry-free) -/

/-- Build a `DissipativeEvolution` from an `R3GalerkinScheme` and an `R3NSForms`.

`H := L2Sigma_R3`, with the `L2Sigma_R3`-subspace instances inherited from `L2VF_R3`.
The regularity functional is `viscousFormSq_R3 1 ∘ (↑)` (matching the design doc:
`reg := viscousFormSq_R3 1`), the viscous form is the concrete `stokesTestPairing_R3`,
the convection form is `F.b`, and the test predicate is the **canonical**
`IsSchwartzDivFree_R3` (Schwartz divergence-free test class — scheme-independent).

Using `IsSchwartzDivFree_R3` here (rather than `IsGalerkinTest_R3 𝔊`) ensures that
`WeakFormNS … (r3Evolution 𝔊 F) u` is tested against the full Schwartz div-free class,
which is the correct formulation for the whole-space Leray–Hopf weak equation.

This construction is **sorry-free**: `DissipativeEvolution` carries no Galerkin or
compactness fields. -/
@[reducible] noncomputable def r3Evolution (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊) :
    DissipativeEvolution where
  H := L2Sigma_R3
  instNACG := inferInstance
  instIPS := inferInstance
  instCS := inferInstance
  reg := fun u => viscousFormSq_R3 1 (u : L2VF_R3)
  reg_nonneg := fun u => viscousFormSq_R3_nonneg zero_le_one (u : L2VF_R3)
  viscousForm := fun u w => stokesTestPairing_R3 (u : L2VF_R3) (w : L2VF_R3)
  convForm := F.b
  convForm_antisymm := F.b_antisymm
  isTest := fun w => IsSchwartzDivFree_R3 w

/-! ### AX-1: Galerkin ODE solution data on ℝ³ -/

/-- Data produced by the `n`-th Galerkin ODE on the approximation subspace of `L²_σ(ℝ³)`.

Mirrors `GalerkinSolutionData` with `𝔊.P n` for `velocityProjection_n n`, and with
`stokesTestPairing_R3`, `viscousFormSq_R3 ν`, and `memH1VF_R3`.

The `u_initial` field uses the fact that `𝔊.preserves_sigma` ensures `𝔊.P n u₀ ∈ L2Sigma_R3`.

Every field is used in the Aubin–Lions assembly or the limit passage. -/
structure GalerkinSolutionData_R3 (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (u₀ : L2Sigma_R3) (n : ℕ) where
  /-- The Galerkin solution curve. -/
  u : Time → L2Sigma_R3
  /-- Initial condition: `u(0) = 𝔊.P n u₀` (coerced into `L2Sigma_R3` via `preserves_sigma`). -/
  u_initial : u 0 = ⟨𝔊.P n (u₀ : L2VF_R3), 𝔊.preserves_sigma n (u₀ : L2VF_R3) u₀.2⟩
  /-- Range in the n-th approximation subspace: `(u t : L2VF_R3) = 𝔊.P n (u t : L2VF_R3)`. -/
  u_inVn : ∀ t, (u t : L2VF_R3) = 𝔊.P n (u t : L2VF_R3)
  /-- The curve `t ↦ (u t : L2VF_R3)` is differentiable at every **forward** time `t ≥ 0`.

  SOUNDNESS (forward-only): physical Galerkin solutions are confined by the forward energy
  bound `½‖u(t)‖² ≤ ½‖𝔊.P n u₀‖²`, which controls the solution only for `t ≥ 0`.  This
  quadratic-in-`u` ODE field can blow up in finite *backward* time, so asserting the
  derivative for all `t : ℝ` was a latent over-strength claim (an un-physical guarantee that
  the global solver cannot honor).  Restricted to `0 ≤ t`. -/
  u_hasDeriv : ∀ t, 0 ≤ t → HasDerivAt (fun s => (u s : L2VF_R3))
    (deriv (fun s => (u s : L2VF_R3)) t) t
  /-- The projected Galerkin ODE at **forward** times: for `t ≥ 0` and all test vectors `w`
  with `𝔊.P n w = w`,
  `⟪u'(t), w⟫ + ν · stokesTestPairing_R3(u(t), w) + b(u(t), u(t), w) = 0`.

  SOUNDNESS (forward-only): same rationale as `u_hasDeriv` — the ODE identity is only
  guaranteed on the forward time interval where the energy estimate confines the solution;
  the all-`t` form was a latent over-strength claim.  Restricted to `0 ≤ t`. -/
  u_ode : ∀ t, 0 ≤ t → ∀ w : L2Sigma_R3,
    (w : L2VF_R3) = 𝔊.P n (w : L2VF_R3) →
    inner (𝕜 := ℝ) (deriv (fun s => (u s : L2VF_R3)) t) (w : L2VF_R3) +
    ν * stokesTestPairing_R3 (u t : L2VF_R3) (w : L2VF_R3) + F.b (u t) (u t) w = 0
  /-- H¹ regularity: the solution stays in H¹ (required for `spatial_compactness_R3`). -/
  reg_mem : ∀ t, memH1VF_R3 (u t : L2VF_R3)
  /-- Uniform energy bound: `½‖u(t)‖² ≤ ½‖𝔊.P n u₀‖²`. -/
  energy_bound : ∀ t, 0 ≤ t →
    (1 / 2 : ℝ) * ‖(u t : L2VF_R3)‖ ^ 2 ≤
    (1 / 2 : ℝ) * ‖𝔊.P n (u₀ : L2VF_R3)‖ ^ 2
  /-- Uniform (n-independent) regularity bound:
  `∫₀ᵀ viscousFormSq_R3 ν (u t) dt ≤ ½‖u₀‖²`.
  The RHS is n-independent and `T`-independent; it follows from integrating the energy
  identity `∫₀ᵀ viscousFormSq_R3 ν (u t) = ½‖u(0)‖² − ½‖u(T)‖² ≤ ½‖𝔊.P n u₀‖² ≤ ½‖u₀‖²`
  (using `‖u(0)‖ = ‖𝔊.P n u₀‖ ≤ ‖u₀‖` and `½‖u(T)‖² ≥ 0`).  Note: `viscousFormSq_R3`
  already carries the `ν` factor (`= ν · ‖∇u‖²`), so the bound is `ν`-independent. -/
  reg_bound : ∀ T, 0 < T →
    ∫ t in (0 : ℝ)..T, viscousFormSq_R3 ν (u t : L2VF_R3) ≤
    (1 / 2 : ℝ) * ‖(u₀ : L2VF_R3)‖ ^ 2

/-! ### Axiom AX-1: Galerkin ODE existence on ℝ³ -/

/-- **Axiom AX-1:** The `n`-th Galerkin ODE on ℝ³ has a global solution with uniform bounds.

Picard–Lindelöf applies on the finite-dimensional approximation subspace (the RHS is
polynomial hence locally Lipschitz); global existence follows from the energy estimate
`‖uₙ(t)‖ ≤ ‖𝔊.P n u₀‖ ≤ ‖u₀‖` (using `b_antisymm` → `b_self_zero`).

Blocked in Lean by: missing concrete `(u·∇)v` operator on ℝ³ and missing Picard–Lindelöf
for the ℝ³ Galerkin ODE in mathlib.  Temam III.3, Theorem 3.1. -/
axiom galerkin_ode_solution_R3 (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊) -- ALLOW_AXIOM: Picard–Lindelöf on finite-dim approximation subspace + energy identity → global bounds; TRUE and MINIMAL; blocked by missing (u·∇)v on ℝ³ and Galerkin ODE solver; Temam III.3
    (ν : ℝ) (hν : 0 < ν) (u₀ : L2Sigma_R3) (n : ℕ) :
    GalerkinSolutionData_R3 𝔊 F ν u₀ n

/-! ### Axiom AX-SC: Spatial compactness on ℝ³ (LOCAL — no tightness) -/

/-- **Axiom AX-SC:** LOCAL spatial compactness on ℝ³ — the ℝ³ replacement for `rellich_L2Sigma`.

Rellich's theorem FAILS globally on ℝ³, but the LOCAL version holds: given uniform L²
and H¹ bounds, there is a subsequence `z (ψ n)` and a limit `g ∈ L²_σ(ℝ³)` such that
`z (ψ n)` converges to `g` in L² on every ball `{x | ‖x‖ ≤ R}`.

No tightness hypothesis is needed: local Rellich `H¹(B_R) ↪↪ L²(B_R)` (compact embedding)
is unconditional; a diagonal argument over growing balls extracts the subsequence.
This is the genuine Leray 1934 construction. -/
axiom spatial_compactness_R3 : -- ALLOW_AXIOM: ℝ³ LOCAL spatial compactness = local Rellich H¹(B_R)↪↪L²(B_R); TRUE without tightness; replaces the proved T³ rellich_L2Sigma; Leray 1934; Lemarié-Rieusset §6
    ∀ (M : ℝ) (z : ℕ → L2VF_R3),
    (∀ n, z n ∈ L2Sigma_R3) →
    (∀ n, memH1VF_R3 (z n)) →
    (∀ n, ‖z n‖ ≤ M) →
    (∀ n, viscousFormSq_R3 1 (z n) ≤ M ^ 2) →
    ∃ (ψ : ℕ → ℕ) (g : L2VF_R3), StrictMono ψ ∧ g ∈ L2Sigma_R3 ∧
      ∀ R : ℝ, Filter.Tendsto
        (fun n => ∫ x in Metric.closedBall (0 : Domain3) R,
          ‖((z (ψ n)) x : EuclideanSpace ℝ (Fin 3)) - (g x : EuclideanSpace ℝ (Fin 3))‖ ^ 2
          ∂(volume : Measure Domain3))
        Filter.atTop (nhds 0)

/-! ### AX-2: Aubin–Lions compactness package on ℝ³ -/

/-- Package produced by the Aubin–Lions theorem on ℝ³.

Parameterized by `galSeq` (a Galerkin sequence from AX-1), enforcing chain faithfulness
(A1 → A2 → A3 all operate on the same sequence).  Carries: the extracted subsequence `φ`,
its strict monotonicity, a limit curve `u`, and LOCAL space-time convergence.

**LOCAL convergence:** `strong_convergence` asserts convergence in L²(0,T; L²(B_R)) for
every ball radius R — this is the form supported by the local `spatial_compactness_R3`
(no tightness needed).  The Schwartz test functions in `b_bound` have rapid decay, so
the tail outside B_R is controlled uniformly under the H¹ bound.

The spatial compactness half is NOT in this package — it is supplied as an explicit
hypothesis to `aubin_lions_R3` (the type matches `spatial_compactness_R3` exactly). -/
structure AubinLionsPackage_R3 (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν T : ℝ) (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n) where
  /-- The strictly monotone extraction index. -/
  φ : ℕ → ℕ
  /-- Strict monotonicity of `φ`. -/
  φ_mono : StrictMono φ
  /-- The limit curve. -/
  u : Time → L2Sigma_R3
  /-- **LOCAL space-time convergence** of the subsequence to the limit: for every ball
  radius `R`, `∫₀ᵀ ∫_{B_R} ‖uₙ(t,x) - u(t,x)‖² dx dt → 0` along the subsequence `φ`.

  This is the LOCAL form (ball-restricted), supported by the local `spatial_compactness_R3`
  (no tightness).  Sufficient for the nonlinear limit passage since `b_bound` test fields
  are Schwartz (rapid decay controls the tail). -/
  strong_convergence : ∀ R : ℝ,
    Filter.Tendsto
      (fun n => ∫ t in (0 : ℝ)..T,
        ∫ x in Metric.closedBall (0 : Domain3) R,
          ‖(((galSeq (φ n)).u t : L2VF_R3) x : EuclideanSpace ℝ (Fin 3)) -
           ((u t : L2VF_R3) x : EuclideanSpace ℝ (Fin 3))‖ ^ 2
          ∂(volume : Measure Domain3))
      Filter.atTop (nhds 0)

/-! ### Axiom AX-2: Aubin–Lions on ℝ³ -/

/-- **Axiom AX-2:** Aubin–Lions time compactness on ℝ³.

Takes the Galerkin sequence `galSeq` (from AX-1) and an explicit LOCAL spatial-compactness
hypothesis `spatial` whose type matches the new `spatial_compactness_R3` exactly
(LOCAL ball-restricted convergence, no tightness), so the assembly can pass
`spatial_compactness_R3` directly.

This axiom covers ONLY the genuinely-missing Bochner-time compactness half.  The spatial
half is supplied via the `spatial` hypothesis, which the assembly discharges using the
LOCAL `spatial_compactness_R3`.

Blocked in Lean by: missing Bochner-Sobolev time-derivative bounds.  Temam III.2.1. -/
axiom aubin_lions_R3 -- ALLOW_AXIOM: Aubin–Lions time compactness on ℝ³; spatial half supplied as explicit LOCAL hypothesis (discharged by spatial_compactness_R3, ball-restricted, no tightness); axiom adds only Bochner-time half; TRUE and MINIMAL; Temam III.2.1
    (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T)
    (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n)
    (spatial : ∀ (M : ℝ) (z : ℕ → L2VF_R3),
      (∀ n, z n ∈ L2Sigma_R3) →
      (∀ n, memH1VF_R3 (z n)) →
      (∀ n, ‖z n‖ ≤ M) →
      (∀ n, viscousFormSq_R3 1 (z n) ≤ M ^ 2) →
      ∃ (ψ : ℕ → ℕ) (g : L2VF_R3), StrictMono ψ ∧ g ∈ L2Sigma_R3 ∧
        ∀ R : ℝ, Filter.Tendsto
          (fun n => ∫ x in Metric.closedBall (0 : Domain3) R,
            ‖((z (ψ n)) x : EuclideanSpace ℝ (Fin 3)) - (g x : EuclideanSpace ℝ (Fin 3))‖ ^ 2
            ∂(volume : Measure Domain3))
          Filter.atTop (nhds 0)) :
    AubinLionsPackage_R3 𝔊 F ν T u₀ galSeq

/-! ### Axiom AX-3: Galerkin limit passage on ℝ³ -/

/-- **Axiom AX-3:** Galerkin limit passage on ℝ³ (existential good representative).

Consumes the Galerkin sequence `galSeq` and the Aubin–Lions package `alPkg`
(type-indexed by `galSeq`, enforcing chain faithfulness), and concludes that a
**good representative** `u` exists satisfying:
- a.e.-equality to the Aubin–Lions limit `alPkg.u`,
- `WeakFormNS`: the weak NS equation with evolution `r3Evolution 𝔊 F`,
- energy inequality on `[0, T]`,
- initial trace: `u(t) → u₀` as `t → 0⁺`,
- energy class: a.e. `memH1VF_R3` + integrable `viscousFormSq_R3 ν`.

The a.e.-equality link ties `u` to the Aubin–Lions limit (not a standalone solution).
Strong L²(0,T) convergence from AX-2 kills the nonlinear error via `b_bound`;
energy inequality by lsc; initial trace from `𝔊.tendsto_id` (applied at the div-free
initial datum `u₀ ∈ L2Sigma_R3`, within the Σ-restricted convergence).

Blocked in Lean by: nonlinear limit passage requires `b_bound` applied to strong
L² convergence.  Temam III.3. -/
axiom galerkin_limit_passage_R3 -- ALLOW_AXIOM: limit passage produces a GOOD REPRESENTATIVE of alPkg.u (a.e.-equal to Aubin–Lions limit); strong convergence kills nonlinear error via b_bound; lsc energy; initial trace; energy class; Temam III.3
    (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T)
    (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n)
    (alPkg : AubinLionsPackage_R3 𝔊 F ν T u₀ galSeq) :
    ∃ u : Time → L2Sigma_R3,
    (∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc 0 T)), u t = alPkg.u t) ∧
    WeakFormNS ν T (r3Evolution 𝔊 F) u ∧
    (∀ t, 0 ≤ t → t ≤ T →
      (1 / 2 : ℝ) * ‖(u t : L2VF_R3)‖ ^ 2 +
      ∫ s in (0 : ℝ)..t, viscousFormSq_R3 ν (u s : L2VF_R3) ≤
      (1 / 2 : ℝ) * ‖(u₀ : L2VF_R3)‖ ^ 2) ∧
    Filter.Tendsto
      (fun t => (u t : L2VF_R3))
      (nhdsWithin 0 (Set.Ici 0))
      (nhds (u₀ : L2VF_R3)) ∧
    ((∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc 0 T)), memH1VF_R3 (u t : L2VF_R3)) ∧
    IntervalIntegrable (fun s => viscousFormSq_R3 ν (u s : L2VF_R3))
      MeasureTheory.volume 0 T)

/-! ### Proof-carrying solution structures -/

/-- The **full Leray–Hopf solution** structure on ℝ³, carrying genuine proof fields.

All fields are typed propositions (not `Prop` placeholders):
- `weak_eq`: the curve satisfies the weak NS identity for all test functions,
- `energy_ineq`: the Leray–Hopf energy inequality on `[0, T]`,
- `initial_trace`: the initial datum is attained in the strong L² sense,
- `energy_class`: `u ∈ L²(0,T;H¹_σ(ℝ³))` + integrable viscous dissipation
  (prevents `viscousFormSq_R3 ν` collapsing off H¹, making `energy_ineq` non-vacuous). -/
structure LerayHopfSolutionFull_R3 (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν T : ℝ) (u₀ : L2Sigma_R3) where
  /-- The solution curve. -/
  u : Time → L2Sigma_R3
  /-- Weak NS equation (proof-carrying). -/
  weak_eq : WeakFormNS ν T (r3Evolution 𝔊 F) u
  /-- Energy inequality (proof-carrying): holds for `t ∈ [0, T]`. -/
  energy_ineq : ∀ t, 0 ≤ t → t ≤ T →
    (1 / 2 : ℝ) * ‖(u t : L2VF_R3)‖ ^ 2 +
    ∫ s in (0 : ℝ)..t, viscousFormSq_R3 ν (u s : L2VF_R3) ≤
    (1 / 2 : ℝ) * ‖(u₀ : L2VF_R3)‖ ^ 2
  /-- Initial trace: `u(t) → u₀` as `t → 0⁺` (proof-carrying). -/
  initial_trace : Filter.Tendsto
    (fun t => (u t : L2VF_R3))
    (nhdsWithin 0 (Set.Ici 0))
    (nhds (u₀ : L2VF_R3))
  /-- **Energy class (proof-carry):** `u` lies in the Leray–Hopf energy class: a.e.
  `memH1VF_R3` on `[0, T]` and integrable viscous dissipation.  This prevents
  `viscousFormSq_R3 ν` from collapsing to zero off H¹, making `energy_ineq` non-vacuous. -/
  energy_class :
    (∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc 0 T)), memH1VF_R3 (u t : L2VF_R3)) ∧
    IntervalIntegrable (fun s => viscousFormSq_R3 ν (u s : L2VF_R3))
      MeasureTheory.volume 0 T

/-- The **full Galerkin compactness package** on ℝ³, carrying genuine proof fields.

Produced by `build_galerkin_package_R3` (AX-1 → AX-2 with `spatial_compactness_R3` → AX-3).

`energy_class_limit` proof-carries that the limit curve lies in the Leray–Hopf energy
class: a.e. `memH1VF_R3` + integrable viscous dissipation (non-vacuity of the
energy inequality). -/
structure GalerkinCompactnessPackageFull_R3 (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν T : ℝ) (u₀ : L2Sigma_R3) where
  /-- The limit curve. -/
  limit : Time → L2Sigma_R3
  /-- Weak NS equation for the limit. -/
  weak_eq_limit : WeakFormNS ν T (r3Evolution 𝔊 F) limit
  /-- Energy inequality for the limit: holds for `t ∈ [0, T]`. -/
  energy_ineq_limit : ∀ t, 0 ≤ t → t ≤ T →
    (1 / 2 : ℝ) * ‖(limit t : L2VF_R3)‖ ^ 2 +
    ∫ s in (0 : ℝ)..t, viscousFormSq_R3 ν (limit s : L2VF_R3) ≤
    (1 / 2 : ℝ) * ‖(u₀ : L2VF_R3)‖ ^ 2
  /-- Initial trace for the limit. -/
  initial_trace_limit : Filter.Tendsto
    (fun t => (limit t : L2VF_R3))
    (nhdsWithin 0 (Set.Ici 0))
    (nhds (u₀ : L2VF_R3))
  /-- **Energy class (proof-carry):** the limit curve lies in the Leray–Hopf energy class:
  a.e. `memH1VF_R3` on `[0, T]` and integrable viscous dissipation. -/
  energy_class_limit :
    (∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc 0 T)), memH1VF_R3 (limit t : L2VF_R3)) ∧
    IntervalIntegrable (fun s => viscousFormSq_R3 ν (limit s : L2VF_R3))
      MeasureTheory.volume 0 T

/-! ### Assembly theorems -/

/-- **Assembly:** Build a `GalerkinCompactnessPackageFull_R3` by chaining
AX-1 → AX-2 (with LOCAL `spatial_compactness_R3`) → AX-3.

The prover fills the body; the key steps are:
1. Apply `galerkin_ode_solution_R3` (AX-1) for each `n`.
2. Apply `aubin_lions_R3` (AX-2) with `spatial := spatial_compactness_R3` (LOCAL form,
   no tightness).
3. Apply `galerkin_limit_passage_R3` (AX-3) to obtain the weak equation + energy + trace.
4. Pack into `GalerkinCompactnessPackageFull_R3`. -/
noncomputable def build_galerkin_package_R3 (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T) (u₀ : L2Sigma_R3) :
    GalerkinCompactnessPackageFull_R3 𝔊 F ν T u₀ := by
  -- Step 1 (AX-1): the Galerkin ODE solutions, one per `n`.
  have galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n :=
    fun n => galerkin_ode_solution_R3 𝔊 F ν hν u₀ n
  -- Step 2 (AX-2): Aubin–Lions, with the spatial half discharged by the LOCAL
  -- `spatial_compactness_R3` (whose type matches the `spatial` parameter exactly).
  have alPkg : AubinLionsPackage_R3 𝔊 F ν T u₀ galSeq :=
    aubin_lions_R3 𝔊 F ν hν T hT u₀ galSeq spatial_compactness_R3
  -- Step 3 (AX-3): limit passage to the good representative.  The goal is a `Type`
  -- (a structure), so the existential is unpacked with `Exists.choose` rather than
  -- `obtain` (which only eliminates into `Prop`).  The a.e.-link conjunct
  -- (`hspec.1`) is intentionally discarded.
  have hex := galerkin_limit_passage_R3 𝔊 F ν hν T hT u₀ galSeq alPkg
  have hspec := hex.choose_spec
  -- Step 4: pack into the proof-carrying structure.
  exact
    { limit := hex.choose
      weak_eq_limit := hspec.2.1
      energy_ineq_limit := hspec.2.2.1
      initial_trace_limit := hspec.2.2.2.1
      energy_class_limit := hspec.2.2.2.2 }

/-- **Assembly:** A `GalerkinCompactnessPackageFull_R3` yields
`Nonempty (LerayHopfSolutionFull_R3 …)`. -/
theorem exists_lerayHopf_from_package_full_R3 (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν T : ℝ) (u₀ : L2Sigma_R3)
    (pkg : GalerkinCompactnessPackageFull_R3 𝔊 F ν T u₀) :
    Nonempty (LerayHopfSolutionFull_R3 𝔊 F ν T u₀) := by
  exact
    ⟨{ u := pkg.limit
       weak_eq := pkg.weak_eq_limit
       energy_ineq := pkg.energy_ineq_limit
       initial_trace := pkg.initial_trace_limit
       energy_class := pkg.energy_class_limit }⟩

/-- **Main existence theorem on ℝ³:** For any `u₀ ∈ L²_σ(ℝ³)`, `ν > 0`, `T > 0`, there
exist a Galerkin scheme `𝔊`, an NS-forms bundle `F`, and a Leray–Hopf solution `u` on
`[0, T]`. -/
theorem exists_lerayHopf_r3 (u₀ : L2Sigma_R3) (ν : ℝ) (hν : 0 < ν)
    (T : ℝ) (hT : 0 < T) :
    ∃ (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊),
    Nonempty (LerayHopfSolutionFull_R3 𝔊 F ν T u₀) := by
  obtain ⟨𝔊⟩ := r3GalerkinScheme_exists
  obtain ⟨F⟩ := r3_NSForms_exist 𝔊
  exact ⟨𝔊, F, exists_lerayHopf_from_package_full_R3 𝔊 F ν T u₀
    (build_galerkin_package_R3 𝔊 F ν hν T hT u₀)⟩

end LerayHopf
