# Task Contract — Galerkin ODE on ℝ³ (substantiate `galerkin_ode_solution_R3`)

**Milestone:** `ode-galerkin-r3`
**Author:** lean-planner
**Status:** task contract (no Lean edited)
**File deliverable:** `LerayHopf/R3/GalerkinODE.lean` (new, standalone)
**Branch (suggested):** `autorun/ode-galerkin-r3`
**Target axiom:** `galerkin_ode_solution_R3` (`LerayHopf/R3/AxiomaticClosure.lean:363-365`),
producing `GalerkinSolutionData_R3` (`…:323-351`).
**Models to mirror EXACTLY:** R3-d (`TrilinearEstimate.lean`), P5 (`GalerkinScheme.lean`),
P3 (`SpatialCompactness.lean`) — standalone new file under `LerayHopf/R3/`,
isolated-hypothesis discipline, `#print axioms`-clean deliverable, Codex statement+final
gates, root-build inclusion in `LerayHopf.lean`, **never edit `AxiomaticClosure.lean`**.

---

## 0. Goal and scope

Substantiate the analytic content of `galerkin_ode_solution_R3` axiom-free, by producing —
for each `n` — a `GalerkinSolutionData_R3 𝔊 F ν u₀ n` from a **minimal, honest, isolated
hypothesis** that captures the genuine mathlib gap, and from `F`'s algebraic properties
(`b_antisymm`/`b_self_zero`, multilinearity, `b_bound`).

This does **not** remove the axiom (the standalone discipline of R3-d/P5/P3). The new file
does **not** import nor is imported by `AxiomaticClosure.lean`'s axiom block; but — exactly
as P5's post-Codex addendum did — it **may** import `AxiomaticClosure.lean` to reference
`GalerkinSolutionData_R3`, `R3GalerkinScheme`, `R3NSForms`, `R3NSForms.b_self_zero` by name
(those are *definitions/structures/proved lemmas*, not the axiom). The connection is
semantic: we prove `(isolated hyp) → ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n`.

> **DAG check (lean-coder):** `AxiomaticClosure.lean → GalerkinODE.lean`. Confirm NO cycle
> (AxiomaticClosure must not import GalerkinODE). P5's `GalerkinScheme.lean` already imports
> `AxiomaticClosure.lean`, so this import direction is established and safe.

---

## 1. FEASIBILITY VERDICT

**FEASIBLE-WITH-ONE-ISOLATED-HYPOTHESIS** — but the honest hypothesis must carry the
*entire* "global-existence + weak-form-representation" frontier, because **both** of those
steps are genuine mathlib gaps. A fully axiom-free `GalerkinSolutionData_R3` is **NOT**
attainable; do not over-promise (this is the P2 lesson — pressure-test global existence and
weak-form representation, which is exactly what kills the naive plan).

The two pressure-tested steps:

### 1.1 Global existence — GENUINE GAP (verified against mathlib)

mathlib's ODE existence (`.lake/packages/mathlib/Mathlib/Analysis/ODE/`):

- **`IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt`** (`ExistUnique.lean:57`) —
  local existence on a *closed interval* `Icc tmin tmax`, gated by the constraint
  `L · max (tmax−t₀) (t₀−tmin) ≤ a − r` (`PicardLindelof.lean:88`). The interval shrinks
  with the vector-field bound `L` and Lipschitz radius `a`.
- **`ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀`**
  (`ExistUnique.lean:157`) — a `C¹` field gives a solution only on a *small open* `Ioo (t₀−ε) (t₀+ε)`.
- **`ODE_solution_unique_univ`** (`ExistUnique.lean:341`) — uniqueness, but requires a
  *global* `LipschitzOnWith` of the field. Our field is quadratic ⇒ only locally Lipschitz.
- **Manifold uniform-time global lemma** `exists_isMIntegralCurve_of_isMIntegralCurveOn`
  (`Geometry/Manifold/IntegralCurve/UniformTime.lean:162`): from a **UNIFORM** `ε>0` such
  that *every* point has a local curve on `Ioo(−ε) ε`, get a global integral curve. This is
  the closest thing to global existence — but its hypothesis (a uniform existence time over
  *all* initial points) is **false for a quadratic vector field** (existence time → 0 as
  ‖u‖ → ∞) and is itself the continuation/a-priori-bound argument. It is also stated for
  `BoundarylessManifold` + `CMDiff 1`, not directly for our `EuclideanSpace`-subspace setup.

**Conclusion:** mathlib has **NO** "global-existence-from-a-priori-bound" / maximal-solution
/ continuation theorem for vector spaces. The energy estimate
`½‖u(t)‖² ≤ ½‖𝔊.P n u₀‖²` does prevent blow-up *mathematically*, but converting "trajectory
stays bounded" into "solution extends to all `t : ℝ`" requires continuation machinery that
is absent. This is a structural gap, not a hard-but-routine proof. **Global existence is
therefore part of the isolated hypothesis** (or the deliverable is left a precise TODO).

### 1.2 Weak-form ⇄ vector-field representation — GENUINE GAP (the hard part, as flagged)

The structure's `u_ode` is the **weak/projected** ODE
`∀ w ∈ range(𝔊.P n), ⟨u'(t), w⟩ + ν·stokes(u,w) + b(u,u,w) = 0`.
To even *apply* Picard–Lindelöf one must rewrite this as a concrete vector field
`u'(t) = G_n(u(t))` on the finite-dim Hilbert subspace `V_n := range(𝔊.P n)`, where
`G_n : V_n → V_n` is the Riesz representative of the bounded linear functional
`w ↦ −ν·stokes(u,w) − b(u,u,w)`. Obstructions, each verified:

- **Riesz on the subspace:** `V_n` is finite-dimensional (P5: `galerkinSpan_finiteDimensional`)
  hence a complete inner-product space, so `InnerProductSpace.toDual`/`Riesz` *is* available.
  But it produces `G_n` only as an *abstract* element; one must then prove `G_n` is `C¹`
  (or locally Lipschitz) in `u` to feed Picard–Lindelöf.
- **Continuity/Lipschitz of `b(u,u,·)`:** `F.b` is supplied **only** with multilinearity
  + antisymmetry + the *test-side* bound `b_bound` (`|b(u,v,w)| ≤ C(w)·‖u‖·‖v‖`, and ONLY
  for `IsSchwartzDivFree_R3 w`). There is **no** hypothesis giving continuity of
  `u ↦ b(u,u,w)` jointly, nor a bound `|b(u,v,w)| ≤ C·‖u‖‖v‖‖w‖` uniform in `w` over the
  subspace. Even though `range(𝔊.P n)` is Schwartz (P5 `range_schwartz`), `b_bound` only
  bounds `b` for div-free Schwartz `w`, and the constant `C(w)` is per-`w`, not uniform —
  so deriving a single subspace operator norm requires a finite-basis argument over `V_n`
  (finite-dim ⇒ all norms equivalent ⇒ a uniform `C_n`), which is doable but nontrivial and
  needs the basis structure, which `R3NSForms` does NOT carry. This is the representation
  cost. **mathlib has no bridge from a bare abstract trilinear form to a `C¹` quadratic
  vector field.**
- **Identifying `deriv (fun s => (u s : L2VF_R3))` with `G_n`:** the structure's `u_ode`
  and `u_hasDeriv` speak of the derivative *of the curve into the ambient `L2VF_R3`*, while
  Picard–Lindelöf produces a curve into `V_n`. The bridge (subspace inclusion is a
  continuous linear embedding ⇒ derivatives transport) is routine but must be done.

**Conclusion:** the weak-form representation is the predicted hard part; it is partly doable
(Riesz on a finite-dim subspace) but blocked end-to-end by the absence of (a) joint
continuity/uniform bound of `F.b` on the subspace and (b) the global-continuation step.
Both belong in the isolated hypothesis.

### 1.3 What IS axiom-free deliverable content

The **energy identity / a-priori bound algebra** is fully provable from `F`'s properties
once a solution curve is *given*: with `b(u,u,u)=0` (`R3NSForms.b_self_zero`, already proved),
testing the ODE against `w = u(t)` yields
`⟨u',u⟩ + ν·stokes(u,u) + b(u,u,u) = 0`, i.e. `½ d/dt‖u‖² = −ν·viscousFormSq`, giving both
`energy_bound` and (by integration) `reg_bound`. **These two fields are genuinely derivable**
from the ODE + `b_self_zero` + the chain rule, modulo the integrability/FTC plumbing
(`stokesTestPairing_R3(u,u) = viscousFormSq_R3 1 u` on the diagonal — see N1 below). This is
the honest axiom-free payoff, mirroring how R3-d proved the `b_bound` *shape* axiom-free.

---

## 2. Design decision — the isolated frontier hypothesis

Mirroring P3's `LocalRellichInput` and P5's `SchwartzGalerkinBasis`: bundle the genuine gap
in **one structure** that supplies *only* what mathlib cannot, and **derive every
`GalerkinSolutionData_R3` field** from it axiom-free. The structure must NOT smuggle the
conclusion (P2 lesson): it provides the **bare curve + its two defining ODE facts**
(global differentiability and the weak ODE), but **not** the energy bounds, **not** the H¹
regularity, **not** `u_inVn`/`u_initial` as freebies beyond the minimal seed.

### 2.1 Chosen shape (preferred): `GalerkinODEInput`

```
/-- Isolated analytic frontier for the ℝ³ Galerkin ODE.

For each `n`, the finite-dim projected Navier–Stokes ODE on the subspace `range(𝔊.P n)`
admits a GLOBAL solution curve.  This bundles the two genuine mathlib gaps — (i) global
existence (no continuation-from-a-priori-bound theorem in mathlib) and (ii) the
weak-form ⇄ vector-field Riesz representation of the projected NS ODE for the abstract
trilinear form `F.b` — WITHOUT proving them; they are hypotheses supplied by the caller.

Honesty (no-smuggle): the input supplies ONLY the raw solution curve together with the two
facts that DEFINE it as a solution (its global differentiability and the weak Galerkin
ODE), plus the structural membership/initial-trace seeds.  It supplies NEITHER the energy
bound, NOR the dissipation bound, NOR H¹ regularity — all of those are DERIVED axiom-free
below from the ODE and `F`'s antisymmetry (`b_self_zero`).  This matches the genuine content
of Picard–Lindelöf+continuation (existence of the curve) and excludes exactly the analytic
payoff this milestone proves. -/
structure GalerkinODEInput (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (u₀ : L2Sigma_R3) (n : ℕ) where
  /-- The global Galerkin solution curve. -/
  u : Time → L2Sigma_R3
  /-- Initial condition seed. -/
  u_initial : u 0 = ⟨𝔊.P n (u₀ : L2VF_R3), 𝔊.preserves_sigma n (u₀ : L2VF_R3) u₀.2⟩
  /-- The curve stays in the n-th approximation subspace (so it is a genuine Galerkin curve). -/
  u_inVn : ∀ t, (u t : L2VF_R3) = 𝔊.P n (u t : L2VF_R3)
  /-- Global differentiability of the ambient curve. -/
  u_hasDeriv : ∀ t, HasDerivAt (fun s => (u s : L2VF_R3))
    (deriv (fun s => (u s : L2VF_R3)) t) t
  /-- The weak projected Galerkin ODE (the defining equation). -/
  u_ode : ∀ t, ∀ w : L2Sigma_R3,
    (w : L2VF_R3) = 𝔊.P n (w : L2VF_R3) →
    inner (𝕜 := ℝ) (deriv (fun s => (u s : L2VF_R3)) t) (w : L2VF_R3) +
    ν * stokesTestPairing_R3 (u t : L2VF_R3) (w : L2VF_R3) + F.b (u t) (u t) w = 0
```

**No-smuggle audit (the P2 gate):**
- Fields `u, u_initial, u_inVn, u_hasDeriv, u_ode` are *exactly* the first five
  `GalerkinSolutionData_R3` fields, verbatim (`u_hasDeriv` uses `HasDerivAt … t` for all `t`,
  identical to the structure). They are the *definition of "is a global solution"* — this is
  what an existence theorem hands you, so packaging them is honest (not the conclusion).
- Fields **deliberately ABSENT** from the input (= the genuine payoff DERIVED in §3):
  `reg_mem` (H¹ regularity), `energy_bound`, `reg_bound`. The input does NOT supply these.
- The input does NOT supply `b_self_zero` (already a proved lemma) nor any energy identity.

> **Codex must confirm** this boundary: that `reg_mem`/`energy_bound`/`reg_bound` are
> *genuinely derivable* from `u_ode + b_self_zero + chain rule + N1`, and are therefore NOT
> being smuggled by being placed in the input. If Codex finds `reg_mem` is **not** derivable
> from the ODE alone (it likely is **not** — H¹ regularity of the curve is an *extra*
> regularity fact, see Risk R-mem below), then `reg_mem` must be MOVED into the input as a
> sixth honest field, and the contract/DoD updated accordingly. **Do not leave `reg_mem` as
> a derived target if it cannot be derived** (no smuggling, no false claim).

### 2.2 Risk R-mem (decide at the Codex statement gate)

`reg_mem : ∀ t, memH1VF_R3 (u t)` asserts the curve is H¹ for all `t`. The Galerkin range is
Schwartz (P5 `range_schwartz`), and `u_inVn` says `u t ∈ range(𝔊.P n)`, so `u t` is
component-wise Schwartz ⇒ H¹. **This is plausibly derivable** from `u_inVn` +
`𝔊.range_schwartz` + "Schwartz ⊂ H¹" (`memH1VF_R3`). Verify whether `R3/Regularity` /
mathlib gives `Schwartz component ⇒ MemSobolev 1 2`. If yes → `reg_mem` is a **must-prove**
derived field (helper M0 below). If the Schwartz⇒H¹ Sobolev bridge is itself a mathlib gap,
then add `reg_mem` to `GalerkinODEInput` as an honest sixth field. **Planner's expectation:
likely derivable** (Schwartz functions are in every Sobolev space; check
`SchwartzMap`/`MemSobolev` API), so it is listed as must-prove M0 with a fallback note.

---

## 3. Declarations in dependency order

New file `LerayHopf/R3/GalerkinODE.lean`.

### Imports
```
import LerayHopf.R3.AxiomaticClosure   -- GalerkinSolutionData_R3, R3GalerkinScheme, R3NSForms,
                                       --   R3NSForms.b_self_zero, stokesTestPairing_R3, …
import LerayHopf.R3.GalerkinScheme     -- (optional) range_schwartz helpers if needed for M0
```
(Justify any heavier import. Do NOT add ODE/PicardLindelof imports unless an *attempted*
partial existence helper is built — see §4; the chosen design pushes existence into the input.)

### Namespace
```
namespace LerayHopf
open MeasureTheory
open scoped Topology
```

### S0 — `GalerkinODEInput` structure (lean-coder)
As in §2.1. Pure interface, no proof. **Role:** lean-coder.

### N1 — `stokesTestPairing_R3_diag` (must-prove, lean-prover)
```
/-- On the diagonal the viscous pairing is the dissipation: `stokesTestPairing_R3 u u = viscousFormSq_R3 1 u`. -/
theorem stokesTestPairing_R3_diag (u : L2VF_R3) :
    stokesTestPairing_R3 u u = viscousFormSq_R3 1 u
```
**Proof sketch:** both are `∑ⱼ ∫ (2π)²‖ξ‖²·(…)`; on the diagonal `Re[(𝓕uⱼ)·conj(𝓕uⱼ)] = ‖(𝓕uⱼ) ξ‖²`
(`Complex.mul_conj`/`normSq`), and `viscousFormSq_R3 1` has `ν = 1` so the leading `1*` drops.
**Deps:** the two defs in `R3/Regularity.lean` (already imported transitively).
**Mathlib:** `Complex.mul_conj`, `Complex.normSq_eq_abs`/`Complex.sq_abs`, `Finset.sum_congr`.
**Gating note Gn1:** confirm the `.re` of `z * conj z` simplifies to `‖z‖²` with the exact
`norm`/`normSq` lemma names; this is the one fiddly real-analysis step. Pure rewriting,
no frontier.

### M0 — `galerkinCurve_reg_mem` (must-prove if derivable; ELSE move to input)
```
/-- H¹ regularity of any curve staying in the Schwartz Galerkin subspace. -/
theorem galerkinCurve_reg_mem (𝔊 : R3GalerkinScheme) (n : ℕ) (v : L2VF_R3)
    (hv : v = 𝔊.P n v) : memH1VF_R3 v
```
**Proof sketch:** `𝔊.range_schwartz n v'` for the pre-image gives Schwartz components of
`𝔊.P n v'`; since `v = 𝔊.P n v`, `v`'s components are Schwartz; then Schwartz ⇒ `MemSobolev 1 2`.
**Deps:** `𝔊.range_schwartz`, `memH1VF_R3` def, a Schwartz⇒Sobolev bridge.
**Gating note Gm0 (decide at Codex gate):** if the Schwartz⇒`MemSobolev 1 2` bridge is NOT
available in `R3/Regularity`/mathlib, this is a **mathlib gap** → add `reg_mem` to
`GalerkinODEInput` (§2.2 fallback) and DELETE M0. Do not fake it.

### E1 — `galerkin_energy_identity` (must-prove, lean-prover) — the analytic core
```
/-- Energy identity: `½ d/dt ‖u(t)‖² = −ν · viscousFormSq_R3 1 (u t)` along the ODE.
Equivalently `HasDerivAt (fun s => ½‖u s‖²) (−ν·viscousFormSq_R3 1 (u t)) t`. -/
theorem galerkin_energy_identity (𝔊 F ν u₀ n) (I : GalerkinODEInput 𝔊 F ν u₀ n) (t : Time) :
    HasDerivAt (fun s => (1/2 : ℝ) * ‖(I.u s : L2VF_R3)‖ ^ 2)
      (- ν * viscousFormSq_R3 1 (I.u t : L2VF_R3)) t
```
**Proof sketch:**
1. `w := I.u t` is a legal test (`I.u_inVn t` ⇒ `(I.u t) = 𝔊.P n (I.u t)`).
2. `I.u_ode t (I.u t) (I.u_inVn t)` gives
   `⟨u', u⟩ + ν·stokes(u,u) + b(u,u,u) = 0`.
3. `R3NSForms.b_self_zero F (I.u t)` ⇒ `b(u,u,u) = 0`, so `⟨u', u⟩ = −ν·stokes(u,u)`.
4. `stokesTestPairing_R3_diag` (N1) ⇒ `stokes(u,u) = viscousFormSq_R3 1 u`.
5. Chain rule: `d/dt(½‖u‖²) = ⟨u', u⟩` from `I.u_hasDeriv t` via
   `HasDerivAt`-of-`‖·‖²` in an inner-product space.
**Mathlib:** `HasDerivAt.inner` / the derivative of `t ↦ ‖f t‖²` =
`2⟨f' , f⟩`; locate via `hasDerivAt_norm_sq`-style API (`inner_self_eq_norm_sq`,
`HasDerivAt.inner_self`, or compose `HasDerivAt.inner` with `I.u_hasDeriv` and itself).
**Gating note Ge1:** the cleanest route is `(I.u_hasDeriv t).inner (I.u_hasDeriv t)` giving
`HasDerivAt (fun s => ⟪u s, u s⟫) (⟪u',u⟫ + ⟪u,u'⟫) t = 2⟪u',u⟫`, then `‖u‖² = ⟪u,u⟫`
(`real_inner_self_eq_norm_sq`) and scale by ½. Confirm `inner` here is the **real** inner on
`L2VF_R3`; `u_ode` uses `inner (𝕜 := ℝ)`, consistent.
**Deps:** S0, N1, `R3NSForms.b_self_zero`.

### E2 — `galerkin_energy_bound` (must-prove, lean-prover) → field `energy_bound`
```
theorem galerkin_energy_bound (…) (I) (t) (ht : 0 ≤ t) :
    (1/2)*‖(I.u t)‖^2 ≤ (1/2)*‖𝔊.P n u₀‖^2
```
**Proof sketch:** the energy is nonincreasing: `E(t) := ½‖u t‖²` has
`E'(s) = −ν·viscousFormSq_R3 1 (u s) ≤ 0` (E1 + `viscousFormSq_R3_nonneg` + `hν`); so
`E(t) ≤ E(0)` for `t ≥ 0` by `antitone`/`HasDerivAt`-monotonicity
(`isAntitone_of_deriv_nonpos`-style or `Convex`/MVT). Then `E(0) = ½‖𝔊.P n u₀‖²` from
`I.u_initial`.
**Mathlib:** `StrictAntiOn`/`antitoneOn_of_hasDerivWithinAt_nonpos` /
`AntitoneOn` from nonpos derivative on `Ici 0`; or `inner_le_of_hasDerivAt`. Locate
`antitoneOn_of_deriv_nonpos` (`Mathlib/Analysis/Calculus/MeanValue.lean`).
**Deps:** E1, `viscousFormSq_R3_nonneg`, S0 (`u_initial`).
**Requires `hν : 0 < ν`** (thread from the deliverable signature; sign of derivative).

### E3 — `galerkin_reg_bound` (must-prove, lean-prover) → field `reg_bound`
```
theorem galerkin_reg_bound (…) (I) (T) (hT : 0 < T) :
    ∫ t in (0:ℝ)..T, viscousFormSq_R3 ν (I.u t) ≤ T*‖u₀‖^2 + ‖u₀‖^2/(2*ν)
```
**Proof sketch:** integrate the energy identity over `[0,T]`:
`∫₀ᵀ ν·viscousFormSq_R3 1 (u t) dt = E(0) − E(T) ≤ E(0) = ½‖𝔊.P n u₀‖² ≤ ½‖u₀‖²`
(FTC `integral_eq_sub_of_hasDerivAt` applied to `−E`). Then bound the RHS:
`½‖u₀‖²/ν ≤ T‖u₀‖² + ‖u₀‖²/(2ν)` — note the stated RHS is generous, so this is slack.
**Caveat (scaling):** `reg_bound` integrates `viscousFormSq_R3 ν` (factor `ν`), while the
identity uses `viscousFormSq_R3 1`; relate by `viscousFormSq_R3 ν u = ν · viscousFormSq_R3 1 u`
(immediate from the def's leading `ν *`). lean-coder may add a one-line helper
`viscousFormSq_R3_eq_smul`. Also `‖𝔊.P n u₀‖ ≤ ‖u₀‖` is `𝔊.norm_le`.
**Mathlib:** `intervalIntegral.integral_eq_sub_of_hasDerivAt`, `intervalIntegrable` of a
continuous integrand (the dissipation is continuous via E1's derivative existence), monotonic
RHS algebra.
**Gating note Ge3:** integrability of `t ↦ viscousFormSq_R3 1 (u t)` on `[0,T]`: it equals
`−E'(t)` which is continuous if `E` is `C¹`; `E1` only gives `HasDerivAt` pointwise. Confirm
continuity of the dissipation (or derive `IntervalIntegrable` from `E'` being a derivative via
`integral_eq_sub_of_hasDerivAt`'s integrability hypothesis). If the integrability is not
cleanly available, this becomes a precise `-- TODO:` naming the missing piece — but planner
expects it provable since `−E'` is the derivative of the `C¹` energy. **Honest fallback:** if
genuinely blocked, leave E3's statement intact with a `-- TODO:` (do not weaken).

### D — `galerkinSolutionData_R3_of_input` (must-prove, lean-prover) — DELIVERABLE
```
/-- **Deliverable.** From the isolated global-existence/representation input, assemble the
full `GalerkinSolutionData_R3`: the curve, its initial value, subspace confinement,
differentiability, the weak ODE, H¹ regularity, and the uniform energy + dissipation
bounds — the last three DERIVED axiom-free from the ODE via `b_self_zero`.  This is the
axiom-free analytic content of `galerkin_ode_solution_R3`, modulo the bundled input. -/
theorem galerkinSolutionData_R3_of_input
    (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊) (ν : ℝ) (hν : 0 < ν)
    (u₀ : L2Sigma_R3) (n : ℕ) (I : GalerkinODEInput 𝔊 F ν u₀ n) :
    GalerkinSolutionData_R3 𝔊 F ν u₀ n :=
  { u := I.u, u_initial := I.u_initial, u_inVn := I.u_inVn,
    u_hasDeriv := I.u_hasDeriv, u_ode := I.u_ode,
    reg_mem := …M0…, energy_bound := …E2…, reg_bound := …E3… }
```
**Role:** lean-prover (assembles). **Deps:** S0, M0 (or input field fallback), E2, E3.
**No-overclaim check:** the first five fields are passed straight from the input (they are
what existence supplies); the last three are the proved payoff. Field types must match
`GalerkinSolutionData_R3` byte-for-byte (do NOT alter the structure).

### D' (optional, only if orchestrator approves) — thin-axiom capstone
As in P5's optional step 5: a follow-up could replace `axiom galerkin_ode_solution_R3` by
`axiom galerkinODEInput_exists (𝔊 F ν hν u₀ n) : Nonempty (GalerkinODEInput 𝔊 F ν u₀ n)`
plus a proved `galerkin_ode_solution_R3` via `galerkinSolutionData_R3_of_input`. This trades
a fat 8-field-data axiom for a thinner 5-field-input axiom + proved energy/regularity payoff
(same axiom count, thinner frontier). **Out of scope here**; orchestrator decides after green
+ re-audit. **Touches `AxiomaticClosure.lean` — a sanctioned soundness/thinning edit only if
explicitly approved.**

---

## 4. Why not attempt partial Picard–Lindelöf existence?

One could attempt a *local* existence helper (build `IsPicardLindelof` for the subspace
vector field on a tiny `Icc`, via Riesz + `b_bound`-on-the-finite-basis). Planner's
recommendation: **do NOT** put this in the deliverable path, because (a) it does not reach
the GLOBAL `u_hasDeriv : ∀ t` / `Time → L2Sigma_R3` the structure demands, and (b) the
weak-form representation cost (§1.2) is heavy and still leaves the global gap. Bundling both
into `GalerkinODEInput` is the honest, minimal, R3-d/P5/P3-consistent choice. If a future
milestone wants to *shrink* the input, the right target is to prove the **local** existence
+ Riesz representation axiom-free and isolate ONLY the global-continuation step — a separate,
smaller milestone (`ode-galerkin-r3-local`).

---

## 5. lean-coder vs lean-prover split

- **lean-coder** (signatures, structure, imports, statements): S0 (`GalerkinODEInput`),
  the *statements* of N1, M0, E1, E2, E3, D (and the optional helper
  `viscousFormSq_R3_eq_smul` for E3), each proof body a marked
  `sorry -- ALLOW_SORRY: ode-galerkin-r3 lean-prover target` so the file compiles.
  Confirm imports + DAG (no cycle with `AxiomaticClosure`).
- **lean-prover** (proof bodies only): N1, M0, E1, E2, E3, D in order
  N1 → M0 → E1 → E2 → E3 → D.

---

## 6. Assumptions / axioms section

**NO new `axiom`, `opaque`, `constant`, or `unsafe`.** Zero.

The genuine frontier — (i) global existence (no continuation theorem in mathlib) and
(ii) the weak-form ⇄ `C¹`-vector-field Riesz representation of the abstract trilinear form —
is carried by the **hypothesis structure `GalerkinODEInput`**, supplied by the caller. It is
a bundle of curve data, not an environment axiom. This is the honest analogue of P3's
`LocalRellichInput` and P5's `SchwartzGalerkinBasis`.

**Possible second isolated field (decide at Codex gate, §2.2/M0):** `reg_mem` moves into
`GalerkinODEInput` *iff* the Schwartz⇒`MemSobolev 1 2` bridge is a mathlib gap. Record the
decision in the file header and the report.

`AxiomaticClosure.lean` is **NOT edited** (no sanctioned soundness fix is needed here, unlike
P5's `tendsto_id` weakening — `GalerkinSolutionData_R3` was already Codex-audited and is
consumed faithfully). Confirm no field of `GalerkinSolutionData_R3` is too strong/unused
during the build; if Codex flags one, escalate to orchestrator (do not silently edit).

---

## 7. Codex review points (`/codex:adversarial-review --effort xhigh`)

Review the **statements** before any proof is attempted:

1. **`GalerkinODEInput` (S0)** — the central gate. Confirm: (a) it does **NOT smuggle** the
   conclusion — the absent fields `reg_mem`/`energy_bound`/`reg_bound` are the genuine
   payoff and are derivable from `u_ode + b_self_zero` (or `reg_mem` must be added per §2.2);
   (b) the five present fields are exactly the *definition of a global solution* (what an
   existence theorem supplies), not the analytic content; (c) `u_inVn` + `u_hasDeriv (∀ t)` +
   `u_ode (∀ t, ∀ w)` faithfully encode the weak Galerkin ODE without hidden strengthening.
2. **`galerkin_energy_identity` (E1)** — confirm the chain-rule + `b_self_zero` + diagonal
   identity (N1) genuinely yields `½ d/dt‖u‖² = −ν·viscousFormSq`, and that the **real** inner
   product / derivative API is used correctly (no complex/real slip).
3. **`galerkin_energy_bound` (E2) / `galerkin_reg_bound` (E3)** — confirm the bounds match the
   `GalerkinSolutionData_R3` field types byte-for-byte, the `viscousFormSq_R3 1` ↔
   `viscousFormSq_R3 ν` scaling is correct, and the RHS slack in E3 is real (no false claim).
4. **`galerkinSolutionData_R3_of_input` (D)** — confirm the assembled record matches the
   `GalerkinSolutionData_R3` structure exactly (no field altered, no hypothesis dropped),
   and the semantic link to `galerkin_ode_solution_R3` is genuine (the deliverable IS the
   axiom's conclusion modulo `GalerkinODEInput`).
5. **`reg_mem` derivability (M0)** — the §2.2 decision: is Schwartz-component ⇒ `MemSobolev 1 2`
   available? Verdict routes M0 to must-prove or to a sixth input field.

---

## 8. Definition of done (honest; must stay consistent with shipped Lean state)

- New file `LerayHopf/R3/GalerkinODE.lean` compiles (`lake build` green); added to the root
  `LerayHopf.lean` build (lean-coder).
- **Must-prove, sorry-free:** N1, E1, E2, E3, D, and **M0 *iff* Codex/M0-check confirms
  Schwartz⇒Sobolev is available** (else M0 is dropped and `reg_mem` becomes an input field —
  update this DoD line and the STATUS row accordingly; **no optimistic "all proved"**).
- **Isolated hypothesis (NOT proved here, by design):** `GalerkinODEInput` carries global
  existence + weak-form representation (and possibly `reg_mem`). This is the honest frontier;
  the milestone does **NOT** make `galerkin_ode_solution_R3` axiom-free unconditionally.
- **Possible TODO (only if E3 integrability is genuinely blocked, §E3):** E3's statement
  stays intact with a precise `-- TODO:` naming the missing dissipation-integrability /
  FTC-integrability pillar; in that case E3 is *not* must-prove and the DoD + STATUS row must
  say so explicitly (no faking).
- **Zero new axioms / opaque / unsafe.** Only `ALLOW_SORRY` permitted, and only transiently
  during the coder→prover handoff (final state: sorry-free for the must-prove set).
- `#print axioms galerkinSolutionData_R3_of_input` → only
  `[propext, Classical.choice, Quot.sound]` (R3-d/P5/P3 discipline).
- File does **NOT** import the axiom block destructively; `AxiomaticClosure.lean` is
  **NOT edited**; no import cycle.
- `exists_lerayHopf_r3` unaffected: `#print axioms exists_lerayHopf_r3` stays = the 6 project
  axioms + propext/Classical.choice/Quot.sound, no `sorryAx` (this file is not imported by the
  closure).
- `bash scripts/agent-preflight.sh` green.
- Codex `/codex:adversarial-review --effort xhigh` → approve on statements (points 1–5),
  routed by orchestrator before proof work and again after.
- STATUS.md gets a new row (orchestrator/planner) describing the milestone honestly: the
  energy/dissipation/regularity payoff is proved axiom-free; the global-existence +
  weak-form-representation frontier is isolated in `GalerkinODEInput`, not removed.

---

## 9. Risks / gating notes (summary)

- **R-global (HIGH, structural):** no continuation/global-existence theorem in mathlib;
  global existence is part of the isolated input. Not a blocker for the milestone (it is the
  honestly-isolated frontier), but it is why the axiom is NOT made unconditionally axiom-free.
- **R-repr (HIGH, structural):** abstract trilinear `F.b` ⇒ `C¹` subspace vector field
  (Riesz + uniform subspace bound) has no mathlib bridge; bundled into the input. The Riesz
  step alone (finite-dim subspace) is feasible but insufficient; do not attempt in the
  deliverable path (§4).
- **R-mem (MEDIUM, decide at gate):** `reg_mem` derivable from `range_schwartz` + Schwartz⇒
  Sobolev — likely yes; fallback = sixth input field (§2.2/M0).
- **Ge3 (MEDIUM):** integrability of the dissipation on `[0,T]` for FTC in E3; expected
  provable from `E` being `C¹`; honest TODO fallback if blocked (§E3).
- **Gn1 / Ge1 (LOW):** `Re[z·conj z] = ‖z‖²` lemma names (N1) and the real-inner derivative
  API (E1) — pure rewriting, standard.

---

## 10. First task to hand to lean-coder

Land `LerayHopf/R3/GalerkinODE.lean` with: imports (`AxiomaticClosure`, optionally
`GalerkinScheme`), `namespace LerayHopf` + opens, the structure **S0 `GalerkinODEInput`**,
the optional helper `viscousFormSq_R3_eq_smul`, and the *statements* of **N1, M0, E1, E2, E3,
D**, each proof body a marked `sorry -- ALLOW_SORRY: ode-galerkin-r3 lean-prover target` so
the file compiles. Confirm the `AxiomaticClosure → GalerkinODE` import direction has no cycle
and add the file to the root build. Then hand to Codex (review points 1–5), then to
lean-prover for proofs in order N1 → M0 → E1 → E2 → E3 → D.
