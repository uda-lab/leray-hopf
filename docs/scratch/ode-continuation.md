# Task Contract — Construct `GalerkinODEInput` axiom-free (Pillar E: ODE global existence + weak-form↔vector-field)

**Milestone:** `ode-continuation` (Pillar E)
**Author:** lean-planner
**Status:** task contract (no Lean edited)
**File deliverable:** `LerayHopf/R3/GalerkinODEExistence.lean` (NEW, standalone sibling)
**Runs in PARALLEL with:** Rellich-on-balls track, Helmholtz-density track. Stay in lane:
this file touches ONLY the Galerkin ODE existence (`GalerkinODEInput` construction). It does
NOT touch `SchwartzGalerkinBasis`/`dense_span` (Helmholtz track) nor any Rellich/compactness.
**Target:** `theorem galerkinODEInput_R3 … : GalerkinODEInput 𝔊 F ν u₀ n` — combined with the
already-proved `galerkinSolutionData_R3_of_input` (`GalerkinODE.lean:307`) this discharges the
analytic content of `galerkin_ode_solution_R3`.
**Models to mirror EXACTLY:** P5 (`GalerkinScheme.lean`) and `GalerkinODE.lean` — standalone
new file under `LerayHopf/R3/`, isolated-hypothesis discipline if a residual frontier remains,
`#print axioms`-clean deliverable, root-build inclusion in `LerayHopf.lean`, Codex statement +
final gates, **never edit `SolutionInterfaces.lean`** (axiom removal is a later sequential capstone).

---

## 0. Goal and scope

`GalerkinODE.lean` (already shipped, all proofs done) reduces `GalerkinSolutionData_R3` to a
single isolated hypothesis `GalerkinODEInput` carrying the two genuine gaps:

1. **R-global** — global-in-time existence of the finite-dim Galerkin ODE solution curve.
2. **R-repr** — weak-form (`u_ode`) ↔ concrete vector field (`u' = G_n(u)`) representation.

This milestone attempts to **construct** a `GalerkinODEInput` axiom-free, i.e. discharge those
two gaps. The deliverable is the term `galerkinODEInput_R3` producing the structure with its
five fields `u, u_initial, u_inVn, u_hasDeriv, u_ode`.

**The new file MAY import `SolutionInterfaces.lean` and `GalerkinODE.lean`** to reference the
structures/defs by name (`GalerkinODEInput`, `R3GalerkinScheme`, `R3NSForms`,
`stokesTestPairing_R3`, `galerkinSpan`, `galerkinP`, …) — these are defs/structures, not the
axiom. It does NOT edit `SolutionInterfaces.lean` and is NOT imported by it (one-directional DAG,
no cycle), exactly like `GalerkinScheme.lean`/`GalerkinODE.lean`.

> **DAG check (lean-coder):** `SolutionInterfaces.lean → GalerkinODE.lean → GalerkinODEExistence.lean`
> and `GalerkinScheme.lean → GalerkinODEExistence.lean` (for `galerkinP`/`galerkinSpan`/
> finite-dim instances). Confirm NO cycle. Note: `GalerkinODEInput`/`R3GalerkinScheme` are
> abstract — `𝔊.P n` is an opaque CLO with the field axioms (`norm_le`, `idem`, `range_schwartz`,
> `preserves_sigma`); it is NOT necessarily the concrete `galerkinP`. See §1.4 (the abstraction
> barrier) — this is decisive for feasibility.

---

## 1. FEASIBILITY VERDICT — **BLOCKED at full axiom-freeness; PARTIAL is reachable**

**Honest bottom line: a fully axiom-free `galerkinODEInput_R3` is NOT attainable now.** Both
R-global and R-repr are genuine mathlib gaps, *and* there is a third structural blocker (§1.4)
specific to this abstract setting that the parent contract under-weighted. The recommended
deliverable is therefore one of two honest shapes (§2): either (A) a thin reduction theorem
that isolates the SMALLEST residual frontier as a new bundled hypothesis, or (B) a precise
multi-`TODO` skeleton. **Do NOT over-promise an unconditional construction.** Detailed grep-
backed findings below.

### 1.1 R-global (global existence) — GENUINE GAP (re-verified against mathlib)

`.lake/packages/mathlib/Mathlib/Analysis/ODE/ExistUnique.lean`:

- Local only: `IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt` (`:57`) on a closed
  interval gated by the Picard-Lindelöf radius constraint; `ContDiffAt.…_Ioo_hasDerivAt₀`
  (`:157`) gives a solution only on a small open `Ioo`.
- Uniqueness only: `ODE_solution_unique` / `ODE_solution_unique_univ` (`:327`, `:341`) —
  `_univ` needs a GLOBAL `LipschitzOnWith`; our field `G_n` is quadratic ⇒ only locally
  Lipschitz, so `_univ` does not apply.
- No continuation / maximal-solution / global-existence-from-a-priori-bound theorem exists for
  vector spaces. `ODE/Gronwall.lean`, `ODE/Basic.lean`, `ODE/Transform.lean` contain no
  continuation lemma either (Grönwall gives uniqueness/stability bounds, not existence-extension).

The closest candidate, the manifold lemma `exists_isMIntegralCurve_of_isMIntegralCurveOn`
(`Geometry/Manifold/IntegralCurve/UniformTime.lean:15`), is now confirmed UNUSABLE here for a
SECOND reason beyond the parent contract's: its hypothesis is
`∀ a, ∃ γ, γ 0 = x ∧ IsMIntegralCurveOn γ v (Ioo (-a) a)` (see
`exists_isMIntegralCurve_iff_exists_isMIntegralCurveOn_Ioo:91`). That is **existence on every
finite interval** — i.e. it ALREADY assumes the continuation result; it converts "solution on
each `Ioo(-a,a)`" into "global solution" by uniqueness-gluing, but does NOT manufacture the
per-interval solutions for a field whose local existence time shrinks to 0 as `‖u‖→∞`. For our
quadratic field the per-interval existence is exactly what is missing. (It is also stated only
for `BoundarylessManifold I M` + `ContMDiff`, not `EuclideanSpace`-subspaces.)

**Hand-built route (the honest path to closing R-global):** global existence CAN in principle be
hand-built from (i) local Picard-Lindelöf, (ii) the a-priori energy bound `‖u(t)‖ ≤ ‖Pₙu₀‖`
(which is NOT yet available pre-construction — it is proved in `GalerkinODE.lean` only AFTER a
global curve exists; for the construction it must be re-derived along the local solution), and
(iii) a maximal-interval / blow-up-alternative argument (the maximal existence interval is open;
if finite-time-right-end `T*<∞`, then `‖u(t)‖→∞` as `t→T*`, contradicting the a-priori bound).
mathlib has NO blow-up-alternative lemma, so this argument must be built from scratch
(maximal solution as a `⨆` of local solutions, glued by `ODE_solution_unique`). **This is a
substantial, multi-lemma analytic development** — feasible in principle but NOT a small PR, and
its cost is dominated by the absence of any continuation scaffolding in mathlib. Recommend
isolating it (§2-A) rather than attempting it inside this milestone.

### 1.2 R-repr (weak-form ↔ vector field) — GENUINE GAP

To run Picard-Lindelöf one must rewrite `u_ode`
(`∀ w ∈ range(𝔊.P n), ⟨u',w⟩ + ν·stokes(u,w) + b(u,u,w) = 0`) as `u' = G_n(u)` on
`V_n := range(𝔊.P n)`, where `G_n(u) := Riesz-rep of (w ↦ −ν·stokes(u,w) − b(u,u,w))|_{V_n}`.

- **Riesz on `V_n`:** `V_n` is finite-dimensional (P5 `galerkinSpan_finiteDimensional`,
  `:120`), hence complete (`FiniteDimensional.complete`, `Normed/Module/FiniteDimension.lean:32`),
  so `InnerProductSpace.toDual` (`Analysis/InnerProductSpace/Dual.lean:135`, needs `CompleteSpace`)
  IS available on `V_n`. ✓ This step is feasible.
- **Continuity of the functional on `V_n`:** every linear map out of a finite-dim space is
  continuous (`LinearMap.continuous_of_finiteDimensional`,
  `Normed/Module/FiniteDimension.lean:51`). So once `w ↦ −ν·stokes(u,w) − b(u,u,w)` is shown
  LINEAR in `w` on `V_n` (it is: `stokes` is sesquilinear/linear in 2nd slot, `b` is additive
  +ℝ-homogeneous in 3rd slot via `b_add_3`/`b_smul_3`), it is automatically continuous, so
  `toDual.symm` applies WITHOUT needing the quantitative `b_bound`. ✓ The auto-continuity
  sidesteps the per-`w` constant issue the parent contract worried about — that worry is
  **partially defused** for getting `G_n` to *exist*.
- **Smoothness/local-Lipschitz of `u ↦ G_n(u)` (needed for Picard-Lindelöf):** `G_n` is
  quadratic in `u` (`b(u,u,w)` quadratic, `stokes(u,w)` linear). To feed Picard-Lindelöf one
  needs `G_n` `C¹` or locally Lipschitz in `u`. On a finite-dim space a quadratic map IS smooth,
  BUT proving it from the bare structure requires expressing `G_n` in a finite basis of `V_n`
  and showing each coordinate is polynomial in the coordinates of `u` — and the coefficients
  `b(e_i, e_j, e_k)` are well-defined finite reals, but assembling `G_n` as a `ContDiff`
  map needs the **finite basis of `V_n`**, which neither `R3GalerkinScheme` nor `R3NSForms`
  carries (see §1.4). **This is the residual hard core of R-repr.**
- **Transport curve `V_n → L2VF_R3`:** the subspace inclusion `V_n ↪ L2VF_R3` is a continuous
  linear embedding (finite-dim ⇒ continuous), so a `HasDerivAt` curve into `V_n` transports to
  `u_hasDeriv` into the ambient `L2VF_R3` (`ContinuousLinearMap.comp_hasDerivAt` style). Routine
  but must be done.

### 1.3 What is genuinely AXIOM-FREE deliverable content

- The **Riesz vector field `G_n` exists** and represents the functional on `V_n` (finite-dim
  Riesz + auto-continuity). This is a clean, small, axiom-free lemma worth landing regardless
  of whether the full construction closes (§3, `R1`/`R2`).
- The **subspace-curve ⇒ ambient `u_hasDeriv` / `u_inVn` transport** is axiom-free plumbing.
- The **a-priori bound re-derivation along a local solution** reuses `GalerkinODE.lean`'s energy
  algebra (it is stated for a `GalerkinODEInput`, but the core identity needs only the ODE on an
  interval — may need a local variant).

### 1.4 THE DECISIVE STRUCTURAL BLOCKER — abstraction barrier (new finding)

`galerkinODEInput_R3` is quantified over an ABSTRACT `𝔊 : R3GalerkinScheme` and abstract
`F : R3NSForms 𝔊`. From the abstract `R3GalerkinScheme` (`SolutionInterfaces.lean:139`) all we know
about `𝔊.P n` is: `norm_le`, `idem`, `preserves_sigma`, `range_schwartz`, `tendsto_id`. We do
**NOT** get a finite BASIS of `V_n = range(𝔊.P n)` — only that it has component-wise Schwartz
range and (via `idem`+`norm_le`) is an idempotent non-expansive operator. `FiniteDimensional V_n`
is NOT even derivable from the abstract fields (P5's `galerkinSpan_finiteDimensional` uses the
CONCRETE `galerkinSpan` = span of `Fin n` basis vectors; the abstract `range_schwartz` does NOT
bound the dimension). **Consequently, on an abstract `𝔊`, `V_n` need not be finite-dimensional,
Riesz/auto-continuity do not apply, and the whole R-repr/R-global program does not even start.**

This means `galerkinODEInput_R3 (𝔊 F ν hν u₀ n)` as a theorem over an ARBITRARY `R3GalerkinScheme`
is **false/unprovable** without additional structure on `𝔊`. Two honest fixes:

- **(barrier-fix-FD)** Add to `R3GalerkinScheme` a field `finrank_P : FiniteDimensional ℝ
  (LinearMap.range (P n))` (or expose the basis). This is a sanctioned `SolutionInterfaces.lean`
  soundness/strengthening edit — **OUT OF SCOPE here** (axiom-block edits are the later capstone).
  The Helmholtz/P5 track owns `R3GalerkinScheme` construction; coordinate via orchestrator.
- **(barrier-fix-CONCRETE)** Prove `galerkinODEInput_R3` only for the CONCRETE scheme produced by
  P5 (`𝔊 = ⟨galerkinP B, …⟩` from a `SchwartzGalerkinBasis B`), where `V_n = galerkinSpan B n` IS
  finite-dim with an explicit `Fin n` basis. This is the honest, in-lane route: the construction
  consumes the concrete Galerkin data, not an abstract `𝔊`. **RECOMMENDED.** It changes the
  deliverable signature (see §2).

---

## 2. Deliverable shape — choose at the Codex statement gate

Given §1.4, the headline signature in the task prompt
(`galerkinODEInput_R3 (𝔊 F ν hν u₀ n) : GalerkinODEInput 𝔊 F ν u₀ n` over abstract `𝔊`) is
**not provable**. Pick ONE honest shape; planner recommends **2-A (concrete + isolated residual)**.

### 2-A (RECOMMENDED) — concrete scheme + smallest isolated residual frontier

Work with the concrete P5 data. Build the Riesz vector field axiom-free, and isolate ONLY the
genuine residual (global existence of the finite-dim quadratic ODE) as a new minimal bundled
hypothesis `FinDimGlobalODE` (mirroring `LocalRellichInput`/`SchwartzGalerkinBasis`). Deliverable:

```
/-- From a Schwartz div-free basis `B` (concrete P5 scheme `𝔊 := schemeOfBasis B`) and the
    isolated finite-dim global-existence hypothesis, construct the Galerkin ODE input. -/
theorem galerkinODEInput_of_basis
    (B : SchwartzGalerkinBasis) (F : R3NSForms (schemeOfBasis B)) (ν : ℝ) (hν : 0 < ν)
    (u₀ : L2Sigma_R3) (n : ℕ) (G : FinDimGlobalODE B F ν u₀ n) :
    GalerkinODEInput (schemeOfBasis B) F ν u₀ n
```

where `FinDimGlobalODE` bundles ONLY: a global curve `c : Time → V_n` (`V_n := galerkinSpan B n`)
with `c 0 = projected u₀`, `∀ t, HasDerivAt c (c' t) t`, and the autonomous finite-dim ODE
`c' t = G_n (c t)` for the Riesz field `G_n` BUILT in this file (R1/R2). It does NOT bundle the
weak form, the energy bounds, regularity, or the ambient transport — all DERIVED here. This
isolates the irreducible "no continuation theorem in mathlib" gap into one honest field while
proving R-repr (the weak-form↔vector-field bridge) axiom-free.

> **No-smuggle gate:** `FinDimGlobalODE` must carry the curve as `Time → V_n` with the
> AUTONOMOUS field equation `c' = G_n(c)` — NOT the weak form `u_ode` (that is DERIVED from
> `c' = G_n(c)` via the Riesz characterization R2). If the hypothesis carried `u_ode` directly it
> would smuggle R-repr; Codex must confirm R-repr is genuinely proved, not assumed.

### 2-B (fallback) — multi-TODO skeleton

If even the concrete Riesz construction (R1/R2) proves too heavy this milestone, land R1/R2 as
the axiom-free payoff and leave `galerkinODEInput_of_basis` as a precise skeleton whose
`u_hasDeriv`/`u_ode` carry `-- TODO:` naming exactly the missing pieces (global continuation;
`G_n` `C¹`-ness for Picard-Lindelöf). Statements stay intact, no weakening (Hard rule 8).

### 2-C (NOT recommended) — abstract-`𝔊` with FD hypothesis

`galerkinODEInput_R3 (𝔊) (hFD : ∀ n, FiniteDimensional ℝ (LinearMap.range (𝔊.P n))) …`. This
keeps the abstract `𝔊` by bundling finite-dimensionality as a hypothesis, but then one still
lacks an explicit basis to prove `G_n` smooth, and the abstract `V_n` has no Schwartz-basis
handle for the eventual `b`-coefficient finiteness. Heavier than 2-A for no gain. Skip.

---

## 3. Declarations in dependency order (for shape 2-A)

New file `LerayHopf/R3/GalerkinODEExistence.lean`.

### Imports
```
import LerayHopf.R3.GalerkinODE       -- GalerkinODEInput, energy/regularity payoff lemmas
import LerayHopf.R3.GalerkinScheme    -- galerkinSpan, galerkinP, finiteDimensional instance, basis
import Mathlib.Analysis.InnerProductSpace.Dual          -- InnerProductSpace.toDual (Riesz)
import Mathlib.Analysis.Normed.Module.FiniteDimension   -- continuous_of_finiteDimensional, complete
import Mathlib.Analysis.ODE.PicardLindelof              -- ONLY if attempting local existence (2-A core)
import Mathlib.Analysis.ODE.Gronwall                    -- ONLY if hand-building continuation
```
Justify the ODE imports in-file. Do NOT add them in the 2-B skeleton path (no proof attempt).

### Namespace
```
namespace LerayHopf
open MeasureTheory
open scoped Topology InnerProductSpace
```

### C0 — `schemeOfBasis` (lean-coder, may already be derivable from P5's D7')
```
/-- The concrete Galerkin scheme attached to a basis (the witness inside P5's D7'). -/
noncomputable def schemeOfBasis (B : SchwartzGalerkinBasis) : R3GalerkinScheme
```
**Note:** P5's `nonempty_r3GalerkinScheme_of_basis` (`GalerkinScheme.lean:338`) builds this
record inside `Nonempty`; extract the underlying `def` (same fields) so its `P` is *definitionally*
`galerkinP B`, exposing `range (P n) = galerkinSpan B n`. **lean-coder.** If reusing P5's record
verbatim, ensure `(schemeOfBasis B).P n = galerkinP B n` holds by `rfl`.

### R1 — `galerkinODE_vectorField` (the Riesz field — must-prove, lean-prover)
```
/-- The finite-dim Galerkin vector field on `V_n := galerkinSpan B n`: the Riesz representative
    of `w ↦ −ν·stokesTestPairing_R3(u,w) − F.b u u w` restricted to `V_n`. -/
noncomputable def galerkinODE_vectorField
    (B : SchwartzGalerkinBasis) (F : R3NSForms (schemeOfBasis B)) (ν : ℝ) (n : ℕ)
    (u : galerkinSpan B n) : galerkinSpan B n
```
**Deps:** `galerkinSpan_finiteDimensional` (P5 `:120`), `InnerProductSpace.toDual` on the
finite-dim (hence complete) `V_n`, `LinearMap.continuous_of_finiteDimensional` for the functional.
**Gating note GR1:** the functional `w ↦ −ν·stokes(u,w) − b(u,u,w)` is over `w : L2Sigma_R3` with
`(w:L2VF_R3) ∈ V_n`; restricting to `V_n` and coercing `V_n → L2Sigma_R3` (each `V_n` elt is
div-free Schwartz via `range_schwartz`+`preserves_sigma`) needs a clean `V_n ↪ L2Sigma_R3`
embedding lemma. lean-coder supplies that embedding as a helper.

### R2 — `galerkinODE_vectorField_spec` (Riesz characterization — must-prove, lean-prover)
```
/-- Defining property of the Riesz field: testing against any `w ∈ V_n` recovers the functional. -/
theorem galerkinODE_vectorField_spec (B F ν n) (u w : galerkinSpan B n) :
    inner (𝕜 := ℝ) (galerkinODE_vectorField B F ν n u : L2VF_R3) (w : L2VF_R3)
      = - ν * stokesTestPairing_R3 (u : L2VF_R3) (w : L2VF_R3) - F.b ⟨u,…⟩ ⟨u,…⟩ ⟨w,…⟩
```
**Deps:** R1, `InnerProductSpace.toDual_symm_apply` (`Dual.lean:179`). This is the
weak-form↔vector-field bridge (R-repr) made precise; the whole point of the milestone's R-repr
content lives here.

### R3 — `galerkinODEInput_of_globalCurve` (assemble the input — must-prove, lean-prover)
```
/-- From a global curve `c : Time → V_n` solving the AUTONOMOUS field equation, assemble the
    full `GalerkinODEInput` (deriving u_inVn, u_hasDeriv-into-ambient, and the weak u_ode). -/
theorem galerkinODEInput_of_globalCurve
    (B F ν hν u₀ n) (G : FinDimGlobalODE B F ν u₀ n) :
    GalerkinODEInput (schemeOfBasis B) F ν u₀ n
```
**Builds the five fields:**
- `u` := `fun t => ⟨(G.c t : L2VF_R3), …⟩ : L2Sigma_R3` (V_n ⊂ Σ).
- `u_initial` := `G.c_initial` transported.
- `u_inVn` := membership of `G.c t` in `galerkinSpan B n` + `galerkinP` fixes the span
  (`galerkinP_mem_span`/`idem`).
- `u_hasDeriv` := transport `G.c'`-derivative through `V_n ↪ L2VF_R3` (continuous linear).
- `u_ode` := from `G.ode` (`c' = G_n(c)`) + R2 (Riesz spec) — test `w ∈ V_n`, rearrange the spec
  to `⟨c', w⟩ + ν·stokes + b = 0`. **This is where R-repr is discharged into the weak form.**
**Deps:** R1, R2, C0, the `S0` structure `FinDimGlobalODE`.

### S0 — `FinDimGlobalODE` (the residual isolated hypothesis — lean-coder)
```
/-- Residual isolated frontier: a GLOBAL solution of the finite-dim autonomous Galerkin ODE
    `c' = galerkinODE_vectorField` on `V_n`.  Bundles ONLY the mathlib continuation gap
    (no global-existence-from-a-priori-bound theorem); it does NOT supply the weak form,
    energy bounds, regularity, or transport — all derived. -/
structure FinDimGlobalODE (B : SchwartzGalerkinBasis) (F : R3NSForms (schemeOfBasis B))
    (ν : ℝ) (u₀ : L2Sigma_R3) (n : ℕ) where
  c        : Time → galerkinSpan B n
  c_initial : (c 0 : L2VF_R3) = galerkinP B n (u₀ : L2VF_R3)
  c_hasDeriv : ∀ t, HasDerivAt (fun s => (c s : L2VF_R3)) (deriv (fun s => (c s:L2VF_R3)) t) t
  ode      : ∀ t, deriv (fun s => (c s : L2VF_R3)) t
                = (galerkinODE_vectorField B F ν n (c t) : L2VF_R3)
```
**No-smuggle audit (Codex gate):** `ode` is the AUTONOMOUS field equation, NOT `u_ode`. The weak
form, `u_inVn`, energy/dissipation, and `reg_mem` are all ABSENT — they are derived (R3 + the
already-proved `GalerkinODE.lean` payoff). This bundle is strictly smaller than `GalerkinODEInput`
(it omits the weak-form representation, which R2/R3 PROVE). It is the honest analogue of P3/P5
isolated inputs, carrying exactly the one irreducible mathlib continuation gap.

### D — `galerkinODEInput_of_basis` (DELIVERABLE — must-prove, lean-prover)
```
theorem galerkinODEInput_of_basis (B F ν hν u₀ n) (G : FinDimGlobalODE B F ν u₀ n) :
    GalerkinODEInput (schemeOfBasis B) F ν u₀ n :=
  galerkinODEInput_of_globalCurve B F ν hν u₀ n G
```
Thin wrapper / alias for R3, named to match the milestone deliverable vocabulary. Optionally also
expose the full chain to `GalerkinSolutionData_R3` via `galerkinSolutionData_R3_of_input`
(`GalerkinODE.lean:307`):
```
noncomputable def galerkinSolutionData_of_basis (B F ν hν u₀ n) (G) :
    GalerkinSolutionData_R3 (schemeOfBasis B) F ν u₀ n :=
  galerkinSolutionData_R3_of_input (schemeOfBasis B) F ν hν u₀ n
    (galerkinODEInput_of_basis B F ν hν u₀ n G)
```

---

## 4. lean-coder vs lean-prover split

- **lean-coder** (signatures, structure, imports, statements; bodies = marked
  `sorry -- ALLOW_SORRY: ode-continuation lean-prover target`): C0 `schemeOfBasis`, the
  `V_n ↪ L2Sigma_R3` / `V_n ↪ L2VF_R3` embedding helpers, S0 `FinDimGlobalODE`, and the
  *statements* of R1, R2, R3, D (+ optional `galerkinSolutionData_of_basis`). Confirm imports
  + DAG (no cycle); add file to root `LerayHopf.lean` build after the existing
  `import LerayHopf.R3.GalerkinODE` line (`LerayHopf.lean:51`).
- **lean-prover** (proof bodies only), in order: R1 → R2 → R3 → D.

---

## 5. Assumptions / axioms

**NO new `axiom`, `opaque`, `constant`, or `unsafe`.** Zero.

The single residual frontier — global-in-time existence of the finite-dim quadratic Galerkin ODE
(no continuation-from-a-priori-bound theorem in mathlib) — is carried by the **hypothesis
structure `FinDimGlobalODE`**, supplied by the caller. It is a bundle of curve data, not an
environment axiom. This is the honest analogue of P3's `LocalRellichInput` and P5's
`SchwartzGalerkinBasis`, and is **strictly smaller** than the parent `GalerkinODEInput` because
R-repr (weak-form↔vector-field) is now PROVED (R1/R2/R3), not assumed.

**`SolutionInterfaces.lean` is NOT edited.** The abstraction-barrier finite-dimensionality fix
(§1.4 barrier-fix-FD) is explicitly DEFERRED to the later sequential capstone; this milestone
sidesteps it by working with the concrete `schemeOfBasis B` (barrier-fix-CONCRETE).

**If 2-B fallback:** R1/R2 land sorry-free; R3/D carry precise `-- TODO:` for the residual; no
weakening. Update DoD + STATUS accordingly.

---

## 6. Codex review points (`/codex:adversarial-review --effort xhigh`)

Review the **statements** before any proof is attempted:

1. **§1.4 abstraction barrier + deliverable shape (THE central gate).** Confirm that
   `galerkinODEInput_R3` over an ABSTRACT `R3GalerkinScheme` is NOT provable (no finite-dim/basis
   handle), and that the chosen shape (2-A concrete `schemeOfBasis B`) is the honest minimal route.
   Confirm `schemeOfBasis B`.P n = `galerkinP B n` definitionally so `V_n` has a finite basis.
2. **`FinDimGlobalODE` (S0) — no-smuggle.** Confirm it carries ONLY the autonomous field equation
   `c' = G_n(c)` + global curve, and does NOT smuggle (a) the weak form `u_ode` (must be derived
   by R2/R3), (b) energy/dissipation/regularity, (c) `u_inVn`/transport. Confirm it is strictly
   weaker than `GalerkinODEInput` (R-repr is proved, not assumed).
3. **`galerkinODE_vectorField` (R1) + `…_spec` (R2).** Confirm the Riesz construction is sound
   on the finite-dim `V_n` (completeness from `FiniteDimensional`, auto-continuity of the
   linear functional), the sign/`ν` conventions match `u_ode` (`SolutionInterfaces.lean:339`), and
   the `V_n ↔ L2Sigma_R3 ↔ L2VF_R3` coercions are faithful (div-free Schwartz membership real).
4. **`galerkinODEInput_of_globalCurve` (R3) + D.** Confirm the five assembled fields match
   `GalerkinODEInput` byte-for-byte (`GalerkinODE.lean:88-105`), that `u_ode` is genuinely DERIVED
   from `ode` + R2 (the R-repr discharge), and the transport of the derivative through
   `V_n ↪ L2VF_R3` is correct.
5. **Global-existence honesty.** Confirm the milestone does NOT claim global existence is proved —
   it is isolated in `FinDimGlobalODE.c`/`.ode`. Confirm the report/STATUS state this honestly
   (no overclaim; the R-global gap remains, R-repr is closed).

---

## 7. Definition of done (honest)

- New file `LerayHopf/R3/GalerkinODEExistence.lean` compiles (`lake build` green); added to root
  `LerayHopf.lean` build (after line 51).
- **Must-prove, sorry-free (shape 2-A):** C0 helpers, R1, R2, R3, D (+ optional
  `galerkinSolutionData_of_basis`). These discharge R-repr (weak-form↔vector-field) AND the
  ambient transport axiom-free.
- **Isolated hypothesis (NOT proved here, by design):** `FinDimGlobalODE` carries the residual
  R-global gap (finite-dim ODE global existence — no mathlib continuation theorem). This is the
  honest remaining frontier; the milestone does **NOT** make `galerkin_ode_solution_R3` axiom-free
  unconditionally, but it SHRINKS the frontier from "global existence + representation" to
  "global existence only".
- **`SolutionInterfaces.lean` NOT edited;** no import cycle; the §1.4 FD-field fix deferred.
- **Zero new axioms / opaque / unsafe.** Only transient `ALLOW_SORRY` during coder→prover handoff.
- `#print axioms galerkinODEInput_of_basis` → only `[propext, Classical.choice, Quot.sound]`.
- `#print axioms exists_lerayHopf_r3` unchanged (this file not imported by the closure path).
- `bash scripts/agent-preflight.sh` green.
- Codex `/codex:adversarial-review --effort xhigh` → approve on statements (points 1–5), routed by
  orchestrator before and after proof work.
- STATUS.md gets a new row: R-repr (weak-form↔vector-field via finite-dim Riesz) proved
  axiom-free; R-global (finite-dim ODE global existence) isolated in `FinDimGlobalODE`, not removed.
- **If 2-B fallback taken:** R1/R2 sorry-free; R3/D `-- TODO:`-annotated; DoD + STATUS say so
  explicitly (no optimistic "all proved").

---

## 8. Risks / gating notes (summary)

- **R-barrier (DECISIVE, §1.4):** abstract `R3GalerkinScheme` gives no finite-dim/basis handle ⇒
  the abstract-`𝔊` deliverable is unprovable. Resolved by working over concrete `schemeOfBasis B`
  (in lane; no axiom edit). Codex gate point 1.
- **R-global (HIGH, structural):** no continuation/global-existence-from-a-priori-bound theorem in
  mathlib (re-verified; the manifold lemma assumes per-interval existence). Isolated in
  `FinDimGlobalODE`. NOT a blocker for the milestone (it is the honestly-isolated residual), but
  it is why the axiom is NOT made unconditionally axiom-free.
- **R-repr (MEDIUM, now reachable):** finite-dim Riesz + auto-continuity make `G_n` and its spec
  provable (R1/R2) — the parent contract's per-`w`-constant worry is defused by auto-continuity
  of linear maps on finite-dim spaces. The residual smoothness-of-`G_n`-for-Picard-Lindelöf is
  pushed into `FinDimGlobalODE` (the caller supplies the solved curve), so R-repr's PROVABLE part
  (the representation identity R2) is delivered while the unprovable part stays isolated.
- **GR1 (MEDIUM):** the `V_n ↔ L2Sigma_R3 ↔ L2VF_R3` coercions / div-free-Schwartz embedding
  plumbing for the Riesz functional; routine but fiddly (lean-coder helper).
- **C0 (LOW):** extracting `schemeOfBasis` as a `def` with `P = galerkinP B` by `rfl`.

---

## 9. First task to hand to lean-coder

Land `LerayHopf/R3/GalerkinODEExistence.lean` with: imports (`GalerkinODE`, `GalerkinScheme`,
`InnerProductSpace.Dual`, `Normed.Module.FiniteDimension`; add ODE imports only if pursuing the
2-A proof core, not 2-B), `namespace LerayHopf` + opens, the **C0 `schemeOfBasis` def** (with
`P = galerkinP B` by `rfl`) and the `V_n ↪ L2Sigma_R3`/`L2VF_R3` embedding helpers, the **S0
`FinDimGlobalODE` structure**, and the *statements* of **R1, R2, R3, D** (+ optional
`galerkinSolutionData_of_basis`), each proof body a marked
`sorry -- ALLOW_SORRY: ode-continuation lean-prover target` so the file compiles. Confirm the
`GalerkinODE → GalerkinODEExistence` import direction has no cycle and add the file to the root
build (`LerayHopf.lean`, after line 51). Then hand to Codex (review points 1–5), then to
lean-prover for proofs in order R1 → R2 → R3 → D.
```
