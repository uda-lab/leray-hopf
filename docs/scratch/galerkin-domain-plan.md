# Campaign plan — issue #112: generic Galerkin interface + finite-dim ODE layer (R3/Torus unification)

Architect: lean-architect (fable). Date: 2026-07-10. Status: **GO** (spike verified, see §9).

Executable by a sonnet/opus orchestrator without further route judgment. Any premise
failure (a listed anchor doesn't hold, a frozen statement doesn't elaborate, a fallback
trigger fires) returns to the architect — do not improvise (doctrine D1–D8,
`docs/agent-roles.md`).

---

## 1. Verified interface anchors (2026-07-10, main @ b896afb)

The four main files (3,192 lines total; the ≥800-LOC acceptance target is measured as
net reduction across these four):

| File | Lines | Content |
|---|---|---|
| `LerayHopf/R3/GalerkinODESolve.lean` | 825 | CLM tower, A1–A3, G1 tiling, `finDimGlobalODE_exists`, `galerkinSolutionData_unconditional` |
| `LerayHopf/Torus/GalerkinODESolve.lean` | 1165 | B.0 stokes-on-Vₙ, CLM tower, A1–A3, G1 tiling, reg-payoff tail, `galerkinSolutionData_torus` |
| `LerayHopf/R3/SolutionInterfaces.lean` | 725 | `R3GalerkinScheme`, `R3NSForms`, `r3Evolution`, `GalerkinSolutionData_R3`, `AubinLionsPackage_R3`, `LerayHopfSolutionFull_R3`, `GalerkinCompactnessPackageFull_R3`, `exists_lerayHopf_from_package_full_R3` |
| `LerayHopf/Torus/SolutionInterfaces.lean` | 479 | `Torus3NSForms`, `torus3Evolution`, `GalerkinSolutionData`, `AubinLionsPackage`, `LerayHopfSolutionFull`, `GalerkinCompactnessPackageFull`, `exists_lerayHopf_from_package_full` |

Load-bearing anchors (re-verified in source; line numbers at plan time):

- Capstones (statements FROZEN — must be byte-identical after every PR):
  `exists_lerayHopf_r3` — `LerayHopf/R3/GalerkinODECapstone.lean:109`
  (`∃ (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊), Nonempty (LerayHopfSolutionFull_R3 𝔊 F ν T u₀)`);
  `exists_lerayHopf_torus3` — `LerayHopf/Torus/GalerkinODECapstone.lean:133`
  (`∃ F : Torus3NSForms, Nonempty (LerayHopfSolutionFull F ν T u₀)`).
  Success gate at every PR: both re-derive, `#print axioms` = `[propext, Classical.choice, Quot.sound]`.
- Finite-dim spans: `velocitySpan : ℕ → Submodule ℝ L2VF`
  (`LerayHopf/Torus/GalerkinScheme.lean:158`, findim instance line 220);
  `galerkinSpan : SchwartzGalerkinBasis → ℕ → Submodule ℝ L2VF_R3`
  (`LerayHopf/R3/GalerkinScheme.lean:113`, findim instance line 121).
- Div-free subspaces are Submodules: `L2Sigma : Submodule ℝ L2VF`
  (`LerayHopf/Torus/Leray.lean:107`), `L2Sigma_R3 : Submodule ℝ L2VF_R3`.
- Projectors: `velocityProjection_n : ℕ → L2VF →L[ℝ] L2VF`
  (`LerayHopf/Torus/VelocityGalerkin.lean:71`); R3 projectors are the `P` field of
  `R3GalerkinScheme` (`R3/SolutionInterfaces.lean:186`).
- The 12 byte-parallel ODE declarations (both `GalerkinODESolve.lean`):
  `galerkinODE_bilinearPart`, `galerkinODE_linearPart`, `galerkinODE_vectorField_eq_parts`,
  `galerkinODE_vectorField_contDiff`, `galerkinField_inner_self_nonpos`,
  `energy_hasDerivAt_of_localSolution`, `norm_le_of_forwardSolution`,
  `galerkinField_uniform_local_time`, `galerkinField_solution_agree`,
  private `solve_hasDerivAt_ambient`/`solve_exists_on_step`, `forwardGlobalSolution_exists`.
  **Consumers of these names outside their own file: NONE** (verified by grep), except the
  lane deliverables `galerkinSolutionData_torus` / `finDimGlobalODE_exists` /
  `galerkinSolutionData_unconditional` consumed by the two `GalerkinODECapstone.lean`.
  The torus file additionally hosts PUBLIC Fourier lemmas consumed downstream
  (`velocityProjection_n_norm_le`, `L2VF_norm_sq_eq_sum_componentC`,
  `h1EnergySq_eq_L2_add_viscous`, `galerkinCurve_reg_mem`, the `stokesTestPairing_*`
  B.0 family) — these STAY in the torus file (do not move).
- R3's vector field is defined one file up: `galerkinODE_functional` /
  `galerkinODE_vectorField` / `galerkinODE_vectorField_spec` in
  `LerayHopf/R3/GalerkinODEExistence.lean` (~line 117 ff). Torus's are in
  `Torus/GalerkinODESolve.lean:177–223`.
- `WeakFormNS (ν T : ℝ) (E : DissipativeEvolution) (u : Time → E.H) : Prop` —
  `LerayHopf/EvolutionTriple.lean:117`; `DissipativeEvolution` — same file line 44;
  `Time := ℝ` — `LerayHopf/Torus/Basic.lean:22`.
- `viscous_curve_continuous` (the R3-only SolutionData field) has 9 consumer files
  (EnergyWeakLsc, GalerkinCurveBounds, WeightedFourierCommute, GalerkinODE,
  GalerkinODEExistence, AubinLionsLimitPassage, GalerkinTrilinearBound,
  GalerkinTimeModulus, SteklovAverages) — blast radius of any change to
  `GalerkinSolutionData_R3`'s shape.
- Real bundle-layer divergences (the issue's `b_bound_test` claim is stale; these are
  the actual ones):
  1. `GalerkinSolutionData_R3` extra field `viscous_curve_continuous`
     (`R3/SolutionInterfaces.lean:451`), and `reg_bound` differs:
     torus integrand `h1EnergySq`, RHS `T‖u₀‖² + ‖u₀‖²/(2ν)`
     (`Torus/SolutionInterfaces.lean:293`); R3 integrand `viscousFormSq_R3 ν`,
     RHS `½‖u₀‖²` (`R3/SolutionInterfaces.lean:463`).
  2. `AubinLionsPackage` (torus): global `eLpNorm` strong convergence;
     `AubinLionsPackage_R3`: per-ball `restrictToBall R` convergence (∀R) PLUS
     `strong_convergence_ae` (torus has no such field).
  3. `DissipativeEvolution.reg`: torus `h1EnergySq`, R3 `viscousFormSq_R3 1`.
  4. Test classes: torus `IsGalerkinTest`, R3 `IsSchwartzDivFree_R3`.
- Old scaffolds: `LerayHopf/GalerkinPackage.lean` (38 lines, `Prop`-placeholder fields,
  header "Scaffold only") and `LerayHopf/ExistenceFromPackage.lean` (40 lines).
  Content consumers: NONE (grep-verified; only import edges from root `LerayHopf.lean:71–72`
  and `LerayHopf/Core.lean:17`, plus a row in `docs/architecture.md`).

## 2. Feasibility spike — PASSED (structural gate)

`LerayHopf/Scratch/GalerkinDomainSpike.lean` — compiled 2026-07-10, exit 0
(warnings only), incremental `lake build LerayHopf.Scratch.GalerkinDomainSpike`, 26 s.

Proved ONCE over abstract `{V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
[FiniteDimensional ℝ V]` and a field `g : V → V`:

- `dissipative_norm_le` (A3 from `hdiss : ∀ v, ⟪v, g v⟫_ℝ ≤ 0` alone),
- `dissipative_uniform_local_time` (G1 uniform-δ from `hg : ContDiff ℝ 1 g`),
- `dissipative_solution_agree` (splice uniqueness),
- `dissipative_forwardGlobal` (the tiling/gluing core),
- generic ambient transport `coe_hasDerivAt` over any `Submodule ℝ H`.

Instantiated on BOTH lanes reproducing the EXACT conclusions (all conjuncts) of
`Torus.forwardGlobalSolution_exists` and R3 `forwardGlobalSolution_exists`, consuming
only the lane theorems `galerkinODE_vectorField_contDiff` and
`galerkinField_inner_self_nonpos` (+ `Submodule.coe_inner`). Key finding: the abstract
proofs are SIMPLER than the lane originals (no ambient coercions until the last step),
and the global-solver layer needs only the INEQUALITY `⟪v, g v⟫ ≤ 0`, decoupling it
cleanly from the lanes' exact dissipation identities.

## 3. Frozen interface statements

`lean-coder` transcribes these verbatim (module docstrings and doc-comments to be
written by the coder; statements below are frozen — provers do not edit them).
New directory: **`LerayHopf/Galerkin/`** — ruling (e): the layer is Galerkin-specific,
NOT `LerayHopf/Analysis/`; `DissipativeODE.lean` and `QuadraticField.lean` are
pdelib-grade (mathlib-only imports) and get flagged in `docs/pdelib-staging.md`.

### 3.1 `LerayHopf/Galerkin/DissipativeODE.lean` (imports: mathlib only)

Namespace `LerayHopf.Galerkin`. Promote the spike section verbatim with these names
(bodies = the spike proofs, which are ports of the existing lane proofs):

```lean
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

theorem energy_hasDerivAt_of_solution (g : V → V) (c : ℝ → V) (t : ℝ)
    (hc : HasDerivAt c (g (c t)) t) :
    HasDerivAt (fun s => (1 / 2 : ℝ) * ‖c s‖ ^ 2) (inner (𝕜 := ℝ) (c t) (g (c t))) t

theorem norm_le_of_forwardSolution_of_dissipative (g : V → V)
    (hdiss : ∀ v : V, inner (𝕜 := ℝ) v (g v) ≤ (0 : ℝ))
    (c : ℝ → V) {T : ℝ} (hT : 0 ≤ T)
    (hsol : ∀ t ∈ Set.Icc (0 : ℝ) T, HasDerivAt c (g (c t)) t) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ‖c t‖ ≤ ‖c 0‖

theorem uniform_local_time (g : V → V) (hg : ContDiff ℝ 1 g) (R : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x₀ ∈ Metric.closedBall (0 : V) R, ∀ t₀ : ℝ,
      ∃ α : ℝ → V, α t₀ = x₀ ∧
        ∀ t ∈ Set.Ioo (t₀ - δ) (t₀ + δ), HasDerivAt α (g (α t)) t

theorem solution_agree (g : V → V) (hg : ContDiff ℝ 1 g)
    (α β : ℝ → V) {a b t₀ : ℝ} (hab : a ≤ b) (ht₀ : t₀ ∈ Set.Icc a b)
    (hαβ : α t₀ = β t₀)
    (hα : ∀ t ∈ Set.Icc a b, HasDerivAt α (g (α t)) t)
    (hβ : ∀ t ∈ Set.Icc a b, HasDerivAt β (g (β t)) t) :
    ∀ t ∈ Set.Icc a b, α t = β t

theorem forwardGlobalSolution_exists (g : V → V) (hg : ContDiff ℝ 1 g)
    (hdiss : ∀ v : V, inner (𝕜 := ℝ) v (g v) ≤ (0 : ℝ)) (x₀ : V) :
    ∃ c : ℝ → V, c 0 = x₀ ∧ ∀ t, 0 ≤ t → HasDerivAt c (g (c t)) t

theorem coe_hasDerivAt {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (W : Submodule ℝ H) (c : ℝ → W) (v : W) (t : ℝ) (h : HasDerivAt c v t) :
    HasDerivAt (fun s => (c s : H)) (v : H) t
```

(private helper `solve_exists_on_step` as in the spike; keep the spike's
`set_option maxHeartbeats` bumps.)

### 3.2 `LerayHopf/Galerkin/QuadraticField.lean` (imports: mathlib only)

The forms-driven field construction (deduplicates both CLM towers). Namespace
`LerayHopf.Galerkin`.

```lean
/-- Raw trilinear + viscous form data restricted to a finite-dimensional real
inner-product space, sufficient to build the Galerkin vector field.  Linearity is stated
raw (no CLM data): on the finite-dimensional `V` continuity is automatic. -/
structure FieldForms (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] where
  bV : V → V → V → ℝ
  bV_add_1 : ∀ u u' v w, bV (u + u') v w = bV u v w + bV u' v w
  bV_add_2 : ∀ u v v' w, bV u (v + v') w = bV u v w + bV u v' w
  bV_add_3 : ∀ u v w w', bV u v (w + w') = bV u v w + bV u v w'
  bV_smul_1 : ∀ (a : ℝ) u v w, bV (a • u) v w = a * bV u v w
  bV_smul_2 : ∀ (a : ℝ) u v w, bV u (a • v) w = a * bV u v w
  bV_smul_3 : ∀ (a : ℝ) u v w, bV u v (a • w) = a * bV u v w
  bV_diag_zero : ∀ v, bV v v v = 0
  sV : V → V → ℝ
  sV_symm : ∀ u w, sV u w = sV w u
  sV_add_right : ∀ u w w', sV u (w + w') = sV u w + sV u w'
  sV_smul_right : ∀ (a : ℝ) u w, sV u (a • w) = a * sV u w
  sV_diag_nonneg : ∀ v, 0 ≤ sV v v

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

noncomputable def FieldForms.vectorField (D : FieldForms V) (ν : ℝ) : V → V
  -- Riesz representative of `w ↦ -ν * D.sV u w - D.bV u u w`
theorem FieldForms.vectorField_spec (D : FieldForms V) (ν : ℝ) (u w : V) :
    inner (𝕜 := ℝ) (D.vectorField ν u) w = -ν * D.sV u w - D.bV u u w
theorem FieldForms.vectorField_contDiff (D : FieldForms V) (ν : ℝ) :
    ContDiff ℝ 1 (D.vectorField ν)
theorem FieldForms.inner_self_vectorField (D : FieldForms V) (ν : ℝ) (v : V) :
    inner (𝕜 := ℝ) v (D.vectorField ν v) = -(ν * D.sV v v)
theorem FieldForms.inner_self_vectorField_nonpos (D : FieldForms V) {ν : ℝ}
    (hν : 0 < ν) (v : V) : inner (𝕜 := ℝ) v (D.vectorField ν v) ≤ 0
theorem FieldForms.energy_hasDerivAt (D : FieldForms V) (ν : ℝ) (c : ℝ → V) (t : ℝ)
    (hc : HasDerivAt c (D.vectorField ν (c t)) t) :
    HasDerivAt (fun s => (1 / 2 : ℝ) * ‖c s‖ ^ 2) (-(ν * D.sV (c t) (c t))) t
theorem FieldForms.forwardGlobalSolution_exists (D : FieldForms V) {ν : ℝ}
    (hν : 0 < ν) (x₀ : V) :
    ∃ c : ℝ → V, c 0 = x₀ ∧ ∀ t, 0 ≤ t → HasDerivAt c (D.vectorField ν (c t)) t
```

Proof route (all ports of existing code): `vectorField` via
`(InnerProductSpace.toDual ℝ V).symm` of the `LinearMap.toContinuousLinearMap`-packaged
functional (right-linearity = `sV_add_right`/`sV_smul_right`/`bV_add_3`/`bV_smul_3`);
`contDiff` via the bilinearPart/linearPart CLM tower exactly as in the two lane files
(left/second-slot linearity from the remaining fields; sV left-linearity from
`sV_symm` + right-linearity, as in R3's `stokesInner_add`/`stokesInner_smul`);
`forwardGlobalSolution_exists` = `DissipativeODE.forwardGlobalSolution_exists` applied
to `vectorField_contDiff` + `inner_self_vectorField_nonpos`.

### 3.3 Lane rewiring contract for the ODE layer (PR-B)

Per-lane `FieldForms` witnesses (new defs; obligations discharged by EXISTING lemmas):

```lean
-- Torus/GalerkinODESolve.lean (namespace LerayHopf.Torus)
noncomputable def torusFieldForms (F : Torus3NSForms) (n : ℕ) :
    Galerkin.FieldForms (velocitySpan n)
  -- bV u u' w := F.b (velocitySpanToSigma n u) (velocitySpanToSigma n u') (velocitySpanToSigma n w)
  -- sV u w    := stokesTestPairing (u : L2VF) (w : L2VF)
  -- obligations: F.b_add_*/b_smul_* ∘ velocitySpanToSigma_add/_smul; F.b_self_zero;
  --   stokesTestPairing_symm/_add_right/_smul_right (+ velocityP_fixes_coe);
  --   stokesTestPairing_diag + viscousFormSq_nonneg.

-- R3/GalerkinODEExistence.lean (namespace LerayHopf)
noncomputable def r3FieldForms (B : SchwartzGalerkinBasis) (F : R3NSForms (schemeOfBasis B))
    (n : ℕ) : Galerkin.FieldForms (galerkinSpan B n)
  -- bV via galerkinSpanToSigma; sV := stokesTestPairing_R3 on coercions;
  -- obligations from the existing Schwartz-Fourier right-linearity layer
  --   (stokesTestPairing_R3_add_right/_smul_right/_symm/_diag, viscousFormSq_R3_nonneg).
```

**Equality-bridge rule (ruling on defeq risk):** do NOT redefine the lane
`galerkinODE_vectorField`s. Prove instead, by `ext_inner_right` + both specs:

```lean
theorem galerkinODE_vectorField_eq_generic (…) :
    galerkinODE_vectorField … ν n = (…FieldForms …).vectorField ν
```

then derive every lane theorem below as a one-to-five-line corollary, keeping its
statement BYTE-IDENTICAL: `galerkinODE_vectorField_contDiff`,
`galerkinField_inner_self_nonpos`, `energy_hasDerivAt_of_localSolution`,
`norm_le_of_forwardSolution`, `galerkinField_uniform_local_time`,
`galerkinField_solution_agree`, `forwardGlobalSolution_exists` (both lanes; ambient
transport via `Galerkin.coe_hasDerivAt`). Delete the now-dead duplicated bodies:
both CLM towers (`rieszSymmCLM`/`bInner`/`bMid`/`bOut`/`stokesInner`/`stokesOut`/
`galerkinODE_bilinearPart`/`galerkinODE_linearPart`/`_eq_parts`), both
`solve_hasDerivAt_ambient`/`solve_exists_on_step`, and the G1 tiling bodies.
`galerkinODE_bilinearPart`/`galerkinODE_linearPart` are public names with no external
consumers (grep-verified §1) — deleting them is sanctioned by this plan; everything
else public keeps its statement. The torus reg-payoff tail (lines 761–1165) and both
lane deliverables (`galerkinSolutionData_torus`, `finDimGlobalODE_exists`,
`galerkinSolutionData_unconditional`) are UNCHANGED except that they now cite the
corollary forms.

### 3.4 `LerayHopf/Galerkin/Domain.lean` + `SolutionBundles.lean` (PR-C)

Imports: `LerayHopf.EvolutionTriple` (+ `Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic`)
and whatever hosts `Time` (`LerayHopf.Torus.Basic:22` — coder may hoist `Time` to a
neutral home ONLY if a cycle forces it; otherwise import as-is).

```lean
namespace LerayHopf.Galerkin

/-- A Galerkin approximation domain: ambient L² Hilbert space of vector fields, closed
divergence-free subspace, projector family, and the domain functionals that
parameterize the solution bundles.  Instances: 𝕋³ (`torusDomain`) and ℝ³ (`r3Domain 𝔊`). -/
structure Domain where
  X : Type
  [instNACG : NormedAddCommGroup X]
  [instIPS : InnerProductSpace ℝ X]
  [instCS : CompleteSpace X]
  σ : Submodule ℝ X
  P : ℕ → X →L[ℝ] X
  P_preserves_σ : ∀ (n : ℕ) (x : X), x ∈ σ → P n x ∈ σ
  regMem : X → Prop                     -- memH1VF / memH1VF_R3
  stokes : X → X → ℝ                    -- stokesTestPairing / stokesTestPairing_R3
  dissip : ℝ → X → ℝ                    -- viscousFormSq / viscousFormSq_R3 (ν-indexed)
  evoReg : X → ℝ                        -- DissipativeEvolution.reg: h1EnergySq / viscousFormSq_R3 1
  evoReg_nonneg : ∀ x, 0 ≤ evoReg x
  regIntegrand : ℝ → X → ℝ              -- reg_bound integrand: (fun _ => h1EnergySq) / viscousFormSq_R3
  regBoundRHS : ℝ → ℝ → ℝ → ℝ           -- ν T ‖u₀‖ ↦ RHS: (T·r² + r²/(2ν)) / (½·r²)
  isTest : ↥σ → Prop                    -- IsGalerkinTest / IsSchwartzDivFree_R3

attribute [instance] Domain.instNACG Domain.instIPS Domain.instCS

/-- The domain-neutral core of the NS convection form (the lane pins `b_galerkin`
stay in `Torus3NSForms`/`R3NSForms`; this is a PROJECTION, not a replacement). -/
structure NSFormCore (D : Domain) where
  b : ↥D.σ → ↥D.σ → ↥D.σ → ℝ
  b_antisymm : ∀ u v w, b u v w = - b u w v
  b_add_1 : ∀ u u' v w, b (u + u') v w = b u v w + b u' v w
  b_add_2 : ∀ u v v' w, b u (v + v') w = b u v w + b u v' w
  b_add_3 : ∀ u v w w', b u v (w + w') = b u v w + b u v w'
  b_smul_1 : ∀ (a : ℝ) u v w, b (a • u) v w = a * b u v w
  b_smul_2 : ∀ (a : ℝ) u v w, b u (a • v) w = a * b u v w
  b_smul_3 : ∀ (a : ℝ) u v w, b u v (a • w) = a * b u v w
  b_bound : ∀ w, D.isTest w → ∃ C, ∀ u v, |b u v w| ≤ C * ‖(u : D.X)‖ * ‖(v : D.X)‖

noncomputable def Domain.evolution (D : Domain) (C : NSFormCore D) : DissipativeEvolution where
  H := ↥D.σ
  instNACG := inferInstance
  instIPS := inferInstance
  instCS := inferInstance                -- torus has `instance : CompleteSpace L2Sigma`
                                         -- (Torus/Leray.lean:124); R3 analogue exists —
                                         -- coder verifies; if missing on ↥σ generally,
                                         -- add a `σ_complete : CompleteSpace ↥σ` field.
  reg := fun u => D.evoReg ↑u
  reg_nonneg := fun u => D.evoReg_nonneg ↑u
  viscousForm := fun u w => D.stokes ↑u ↑w
  convForm := C.b
  convForm_antisymm := C.b_antisymm
  isTest := D.isTest
```

`SolutionBundles.lean`:

```lean
structure SolutionData (D : Domain) (C : NSFormCore D) (ν : ℝ) (u₀ : ↥D.σ) (n : ℕ) where
  u : Time → ↥D.σ
  u_initial : u 0 = ⟨D.P n ↑u₀, D.P_preserves_σ n ↑u₀ u₀.2⟩
  u_inVn : ∀ t, (u t : D.X) = D.P n ↑(u t)
  u_hasDeriv : ∀ t, 0 ≤ t →
    HasDerivAt (fun s => (u s : D.X)) (deriv (fun s => (u s : D.X)) t) t
  u_ode : ∀ t, 0 ≤ t → ∀ w : ↥D.σ, (w : D.X) = D.P n ↑w →
    inner (𝕜 := ℝ) (deriv (fun s => (u s : D.X)) t) (w : D.X)
      + ν * D.stokes ↑(u t) ↑w + C.b (u t) (u t) w = 0
  reg_mem : ∀ t, D.regMem ↑(u t)
  energy_bound : ∀ t, 0 ≤ t →
    (1 / 2 : ℝ) * ‖(u t : D.X)‖ ^ 2 ≤ (1 / 2 : ℝ) * ‖D.P n ↑u₀‖ ^ 2
  reg_bound : ∀ T, 0 < T →
    ∫ t in (0 : ℝ)..T, D.regIntegrand ν ↑(u t) ≤ D.regBoundRHS ν T ‖(u₀ : D.X)‖

structure LerayHopfSolution (D : Domain) (C : NSFormCore D) (ν T : ℝ) (u₀ : ↥D.σ) where
  u : Time → ↥D.σ
  weak_eq : WeakFormNS ν T (D.evolution C) u
  energy_ineq : ∀ t, 0 ≤ t → t ≤ T →
    (1 / 2 : ℝ) * ‖(u t : D.X)‖ ^ 2 + ∫ s in (0 : ℝ)..t, D.dissip ν ↑(u s)
      ≤ (1 / 2 : ℝ) * ‖(u₀ : D.X)‖ ^ 2
  initial_trace : Filter.Tendsto (fun t => (u t : D.X))
    (nhdsWithin 0 (Set.Ici 0)) (nhds ↑u₀)
  energy_class :
    (∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc 0 T)), D.regMem ↑(u t)) ∧
    IntervalIntegrable (fun s => D.dissip ν ↑(u s)) MeasureTheory.volume 0 T
  u_aestronglyMeasurable :
    MeasureTheory.AEStronglyMeasurable (fun t => (u t : D.X))
      (MeasureTheory.volume.restrict (Set.Icc 0 T))

structure CompactnessPackage (D : Domain) (C : NSFormCore D) (ν T : ℝ) (u₀ : ↥D.σ) where
  limit : Time → ↥D.σ
  weak_eq_limit : WeakFormNS ν T (D.evolution C) limit
  energy_ineq_limit : …   -- mirror LerayHopfSolution with `limit`-named fields,
  initial_trace_limit : …  -- byte-identical shapes to the current per-lane
  energy_class_limit : …   -- GalerkinCompactnessPackageFull[_R3] fields
  u_aestronglyMeasurable_limit : …

theorem exists_lerayHopf_from_package (D : Domain) (C : NSFormCore D) (ν T : ℝ)
    (u₀ : ↥D.σ) (pkg : CompactnessPackage D C ν T u₀) :
    Nonempty (LerayHopfSolution D C ν T u₀)
```

Lane rewiring (PR-C):

```lean
-- Torus/SolutionInterfaces.lean
noncomputable def torusDomain : Galerkin.Domain := { … as §1/§3.4 table … }
def Torus3NSForms.core (F : Torus3NSForms) : Galerkin.NSFormCore torusDomain := { b := F.b, … }
noncomputable abbrev torus3Evolution (F : Torus3NSForms) : DissipativeEvolution :=
  torusDomain.evolution F.core
abbrev GalerkinSolutionData (F : Torus3NSForms) (ν : ℝ) (u₀ : L2Sigma) (n : ℕ) :=
  Galerkin.SolutionData torusDomain F.core ν u₀ n
abbrev LerayHopfSolutionFull (F : Torus3NSForms) (ν T : ℝ) (u₀ : L2Sigma) :=
  Galerkin.LerayHopfSolution torusDomain F.core ν T u₀
abbrev GalerkinCompactnessPackageFull (F : Torus3NSForms) (ν T : ℝ) (u₀ : L2Sigma) :=
  Galerkin.CompactnessPackage torusDomain F.core ν T u₀
theorem exists_lerayHopf_from_package_full …  -- byte-identical statement, proof :=
  Galerkin.exists_lerayHopf_from_package _ _ _ _ _

-- R3/SolutionInterfaces.lean
noncomputable def r3Domain (𝔊 : R3GalerkinScheme) : Galerkin.Domain := { … }
def R3NSForms.core {𝔊} (F : R3NSForms 𝔊) : Galerkin.NSFormCore (r3Domain 𝔊) := { … }
@[reducible] noncomputable abbrev r3Evolution (𝔊) (F : R3NSForms 𝔊) := (r3Domain 𝔊).evolution F.core
structure GalerkinSolutionData_R3 (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (u₀ : L2Sigma_R3) (n : ℕ)
    extends Galerkin.SolutionData (r3Domain 𝔊) F.core ν u₀ n where
  viscous_curve_continuous : ∀ j : Fin 3,
    ContinuousOn (fun s => weightedFourierComponent (u s : L2VF_R3) (reg_mem s) j) (Set.Ici 0)
abbrev LerayHopfSolutionFull_R3 (𝔊) (F) (ν T) (u₀) := Galerkin.LerayHopfSolution (r3Domain 𝔊) F.core ν T u₀
abbrev GalerkinCompactnessPackageFull_R3 (𝔊) (F) (ν T) (u₀) := Galerkin.CompactnessPackage (r3Domain 𝔊) F.core ν T u₀
theorem exists_lerayHopf_from_package_full_R3 …  -- byte-identical statement
```

Every field of every abbrev'd structure specializes DEFINITIONALLY to the current
per-lane field (all `Domain` projections reduce on the concrete `torusDomain`/`r3Domain`
literals; `F.core.b` reduces to `F.b`). Field NAMES are kept identical, so
`refine { u := …, u_initial := ?_, … }` constructor sites keep working.

## 4. Rulings (a)–(e)

- **(a) R3 `viscous_curve_continuous` + `reg_bound` divergence.**
  `viscous_curve_continuous`: per-lane `extends`-extension of the generic
  `SolutionData` (§3.4) — NOT a generic field (it is R3-specific finite-dim-derived
  enrichment; a torus counterpart would be a vacuous invention). `reg_bound` scaling:
  parametrized through the two domain fields `regIntegrand`/`regBoundRHS` — NOT a
  common weakening (both lanes keep their exact current bounds; the difference is real
  and stays visible in the instance).
- **(b) `AubinLionsPackage` global-vs-local divergence.** NOT unified. The divergence
  is mathematics, not duplication: 𝕋³ Rellich is global, ℝ³ is per-ball local, and R3
  additionally carries `strong_convergence_ae` which the torus builder does not produce
  for the same extraction `φ`. Forcing a common shape would either change the torus
  statement or demand a new torus proof. Both structures stay per-lane (~35 lines each).
- **(c) Old scaffolds `GalerkinPackage.lean` / `ExistenceFromPackage.lean`.** DELETE
  in PR-D (both files + the import lines `LerayHopf.lean:71–72` item
  `ExistenceFromPackage`, `Core.lean:17` `GalerkinPackage`, + the row in
  `docs/architecture.md` and the mention in `docs/pdelib-staging.md`). They are
  `Prop`-placeholder MVP relics with zero content consumers; keeping a fake "abstract
  package layer" next to the genuine `LerayHopf/Galerkin/` layer would be actively
  misleading. They are NOT absorbed (there is nothing to absorb). Note for the
  orchestrator: this deletes the public names `GalerkinCompactnessPackage` and
  `exists_lerayHopf_from_galerkin_package`; if the owner's post-release API-stability
  bar forbids deletions, the fallback is deprecation + removal from the root import —
  ask the owner ONLY if the deletion is contested in review.
- **(d) Lane-irreducible ~20% (the cut-line).** Stays per-lane as instance obligations:
  the Stokes right-linearity/diagonal layer on Vₙ (torus finite-box tsum algebra =
  `Torus/GalerkinODESolve.lean` B.0; R3 Schwartz-Fourier integrability route), the σ-map
  plumbing (`velocitySpanToSigma`/`galerkinSpanToSigma`), the torus reg-payoff tail
  (Pythagoras/H¹-split/nonexpansiveness/viscous bound), R3's `GalerkinODE.lean` +
  `GalerkinODEExistence.lean` weighted-Fourier continuity discharge, the NS-forms
  non-vacuity pins (`b_galerkin`), and both `AubinLionsPackage`s (ruling b).
- **(e) Module placement.** `LerayHopf/Galerkin/{DissipativeODE, QuadraticField,
  Domain, SolutionBundles}.lean`. First two are mathlib-only (pdelib-grade → note in
  `docs/pdelib-staging.md`); last two sit just above `EvolutionTriple` and BELOW both
  lanes' `SolutionInterfaces` in the DAG.

## 5. PR decomposition

Sequenced; one writer per file; every PR gate = incremental local build green
(`bash scripts/agent-preflight.sh`), grep guards, both capstones `#print axioms`
kernel-only, unchanged capstone statements.

| PR | Content | Files touched | Est. LOC | Tier |
|---|---|---|---|---|
| **A** | `Galerkin/DissipativeODE.lean` + `Galerkin/QuadraticField.lean`, no consumers. | 2 new | +≈650 | coder: sonnet (transcribe §3.1–3.2); prover: sonnet for DissipativeODE (spike proofs exist verbatim), opus for QuadraticField (CLM-tower port) |
| **B** | Lane `FieldForms` witnesses + equality bridges; delete duplicated CLM towers, A-chains, G1 bodies; lane theorems become corollaries (statements byte-identical). | `Torus/GalerkinODESolve.lean` (−≈500), `R3/GalerkinODESolve.lean` (−≈550), `R3/GalerkinODEExistence.lean` (small) | net −≈1,000 on lane files | coder: sonnet; prover: opus (bridges + corollary plumbing); escalate fable only if a bridge fails elaboration |
| **C** | `Galerkin/Domain.lean` + `SolutionBundles.lean`; both `SolutionInterfaces.lean` rewired to abbrevs/extends per §3.4; downstream fixups. | 2 new (+≈420), both SolutionInterfaces (−≈380 combined), fallout in bundle consumers | net ≈ −0…+50 repo-wide, −380 on main files | coder: opus (blast radius); prover: opus; fable on any premise failure |
| **D** | Delete scaffolds (ruling c) + `LerayHopf/Scratch/GalerkinDomainSpike.lean`; docs de-stale (`docs/architecture.md`, `docs/pdelib-staging.md`); file a follow-up issue for the stretch goal (§7). | root, Core, docs | −≈90 | sonnet |

Acceptance arithmetic: reduction across the four main files ≈ 500+550+380 ≈ **1,430
lines** (target ≥800 met with margin). Repo-wide net ≈ −350 after adding ~1,070 generic
lines — state BOTH numbers in the PR-D report; the issue's criterion is the four-file
figure.

Pre-flight for PR-B/PR-C (coder, before editing): grep for consumers that unfold or
positionally construct the touched declarations —
`grep -rn "unfold galerkinODE_vectorField\|galerkinODE_vectorField]" LerayHopf/`,
`grep -rn "GalerkinSolutionData_R3\b" LerayHopf/ | grep "⟨"` (positional constructors
break under `extends`; convert to named-field syntax where found).

## 6. Kill criteria / fallbacks (architect-approved; anything else → back to architect)

1. **PR-B bridge failure:** if `galerkinODE_vectorField_eq_generic` cannot be proved by
   `ext_inner_right` + the two specs (it must — both sides have the same defining inner
   products), STOP: that is a premise failure, return to architect.
2. **PR-C abbrev fallout:** if rewiring `GalerkinSolutionData` (torus) or the two Full
   bundles to abbrevs breaks >~10 downstream proof sites in ways not fixable by
   named-field constructor conversion or a `rfl`-simp lemma
   (`Domain.evolution_viscousForm : (D.evolution C).viscousForm u w = D.stokes ↑u ↑w := rfl`
   family), fall back per-structure: keep that ONE structure per-lane and genericize the
   rest; record which structure fell back in the PR body. The capstone statements must
   never change under either branch.
3. **`extends` failure for `GalerkinSolutionData_R3`** (constructor/field-access
   breakage in the 9 consumer files beyond mechanical fixes): fall back to keeping
   `GalerkinSolutionData_R3` standalone (only its 8 shared fields lose dedup, ~60
   lines); proceed with the rest of PR-C.
4. Banned moves at every step: weakening any bundle field, adding hypotheses to any
   public theorem, `Prop`-stubbing, moving the torus-hosted public Fourier lemmas out
   of `Torus/GalerkinODESolve.lean`.

## 7. Stretch goal ruling

Restating `R3/ArzelaAscoliTime.lean` / `R3/GoodRepresentative.lean` against the
interface: SPLIT to a follow-up issue (file it in PR-D). They consume
`GalerkinSolutionData_R3`-specific fields including `viscous_curve_continuous`, so a
clean restatement is only cheap AFTER PR-C's `extends` shape lands and stabilizes;
bundling it into this campaign couples the highest-blast-radius PR to a cosmetic goal.

## 8. Codex gate points (orchestrator runs `/codex:adversarial-review --effort xhigh`)

- **PR-B (mandatory):** audit that every lane theorem statement is byte-identical
  pre/post; audit the equality bridges for accidental statement drift; audit that no
  `∀t`-vs-forward-time change slipped in.
- **PR-C (mandatory):** the central soundness question — the abbrev'd bundles must be
  FIELD-FOR-FIELD propositionally identical to the old structures (same quantifiers,
  same coercions, same integrands, same RHS constants); check `regBoundRHS`/`regIntegrand`
  instances against §1's divergence table; check the capstones' pretty-printed
  statements and `#print axioms` diff.
- PR-A / PR-D: standard review effort.

## 9. Verdicts (append-only)

- **2026-07-10 GO (architect, fable).** Spike
  `LerayHopf/Scratch/GalerkinDomainSpike.lean` compiled (exit 0, incremental, 26 s):
  abstract dissipative-C¹ forward-global solver proved once, instantiated on both lanes
  with EXACT production conclusions, consuming only `galerkinODE_vectorField_contDiff`
  + `galerkinField_inner_self_nonpos` per lane. The costliest kernel (G1
  tiling/gluing genericization + ambient transport) is de-risked. Bundle-layer route
  (§3.4) is design-frozen with two recorded fallbacks (§6.2, §6.3) that degrade LOC
  savings but cannot touch statements. First dispatch: PR-A (§5) — fully specified by
  §3.1–3.2, no route judgment required.
