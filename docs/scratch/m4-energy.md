# M4 Task Contract: Abstract Galerkin Energy Identity

**Milestone:** M4 — "Finite-dim Galerkin ODE + energy identity (skew-symmetry b(u,u,u)=0)"
**Planner:** lean-planner · 2026-06-10
**Prerequisite milestones:** M1 spine (in progress), M2 (done), M3 (done)
**Target file:** `LerayHopf/EnergyEstimate.lean`

---

## 0. What M3 already provides

| Item | Location | Type |
|---|---|---|
| `velocityProjection_n n` | `VelocityGalerkin.lean` | `L2VF →L[ℝ] L2VF` |
| `velocityProjection_n_preserves_L2Sigma` | `VelocityGalerkin.lean` | `u ∈ L2Sigma → velocityProjection_n n u ∈ L2Sigma` |
| `velocityProjection_n_tendsto` | `VelocityGalerkin.lean` | `Tendsto (velocityProjection_n · u) atTop (nhds u)` |
| `EnergyData`, `EnergyInequality` | `EnergySkeleton.lean` | abstract accumulated-dissipation form |
| `energy_nonincreasing_from_nonneg_dissipation` | `EnergySkeleton.lean` | sorry-free consequence |
| `L2Sigma` | `Leray.lean` | `Submodule ℝ L2VF` — the closed div-free subspace |

Mathlib inner-product calculus confirmed present (verified by grep):
- `HasDerivAt.inner`: `HasDerivAt f f' x → HasDerivAt g g' x → HasDerivAt (fun t => ⟪f t, g t⟫) (⟪f x, g'⟫ + ⟪f', g x⟫) x`
- `HasDerivAt.norm_sq`: `HasDerivAt f f' x → HasDerivAt (‖f ·‖²) (2 * ⟪f x, f'⟫) x`
- `intervalIntegral.integral_eq_sub_of_hasDerivAt`: FTC-2 for `ℝ → E`-valued functions
- `IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt₀`: Picard-Lindelöf existence

---

## 1. The central honest assessment

The MVP plan's PR4 frames M4 correctly: **the provable core is purely abstract**. The concrete NS trilinear form `b(u,v,w) = ∫_{𝕋³} ((u·∇)v)·w` is not in mathlib and requires infrastructure that does not exist. M4's genuine contribution to the project is the abstract energy framework that bridges the Galerkin ODE structure to `EnergySkeleton.EnergyInequality`. The concrete realization is Tier-2 frontier work.

---

## Tier 1 — PROVABLE NOW (abstract energy framework, must-prove, sorry-free target)

### 1.1 Abstract Galerkin energy structure

**File:** `LerayHopf/EnergyEstimate.lean`

The key abstraction: a time-dependent curve `u : ℝ → H` in a real inner product space `H`, a viscosity `ν ≥ 0`, a real-valued abstract "dissipation form" `D : H → ℝ` (representing `ν‖∇u‖²` in the abstract), and an abstract trilinear form `B : H → H → H → ℝ` with the single hypothesis `hB : ∀ w, B w w w = 0`.

**Required declarations (must-prove, sorry-free):**

```lean
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Abstract Galerkin energy data: a curve `u : ℝ → H` in a real inner product space, a
nonnegative viscosity `ν`, a dissipation form `D : H → ℝ`, and an abstract trilinear form
`B : H → H → H → ℝ`. -/
structure AbstractGalerkinData where
  H : Type*
  inst_nacg : NormedAddCommGroup H
  inst_ips  : InnerProductSpace ℝ H
  u   : ℝ → H          -- the Galerkin solution curve
  ν   : ℝ              -- viscosity
  D   : H → ℝ          -- pointwise dissipation: represents ν‖∇u(t)‖² at u(t)
  B   : H → H → H → ℝ  -- abstract trilinear form
```

```lean
/-- The abstract Galerkin energy law at time `t`: the ODE is
  `u'(t) + ν A u(t) + B(u(t), u(t), ·) = 0` (weak form projected to the finite-dim subspace),
which after taking `⟪·, u(t)⟫` gives:
  `⟪u'(t), u(t)⟫ + D(u(t)) + B(u(t), u(t), u(t)) = 0`.

We abstract this as a hypothesis on the curve. -/
def AbstractGalerkinODELaw (d : AbstractGalerkinData) : Prop :=
  ∀ t : ℝ,
    HasDerivAt d.u (deriv d.u t) t ∧
    ⟪deriv d.u t, d.u t⟫_ℝ + d.D (d.u t) + d.B (d.u t) (d.u t) (d.u t) = 0
```

Note: the `HasDerivAt` hypothesis is a differentiability requirement on `u`, which will be supplied by the ODE solver. In the abstract tier, we simply assume it.

**Core Tier-1 theorem (the key must-prove):**

```lean
/-- Abstract Galerkin energy identity: if `u : ℝ → H` satisfies the abstract Galerkin energy
law (inner-product form of the ODE) with trilinear skew-symmetry `B w w w = 0`, then
`d/dt (½ ‖u(t)‖²) = -D(u(t))`.

Proof: `d/dt ‖u‖² = 2 ⟪u', u⟫` by `HasDerivAt.norm_sq`, so
  `d/dt (½ ‖u‖²) = ⟪u', u⟫ = -D(u) - B(u,u,u) = -D(u)`
using the ODE law and `B w w w = 0`. -/
theorem abstract_galerkin_energy_identity
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (u   : ℝ → H)
    (ν   : ℝ)
    (D   : H → ℝ)
    (B   : H → H → H → ℝ)
    (hB  : ∀ w, B w w w = 0)
    (hD  : ∀ t, 0 ≤ D (u t))
    (hODE : ∀ t, HasDerivAt u (deriv u t) t ∧
                 ⟪deriv u t, u t⟫_ℝ + D (u t) + B (u t) (u t) (u t) = 0)
    (t   : ℝ) :
    HasDerivAt (fun s => (1/2 : ℝ) * ‖u s‖^2) (-D (u t)) t := by
  -- Step 1: d/dt ‖u t‖² = 2 * ⟪u t, u' t⟫  by HasDerivAt.norm_sq
  -- Step 2: ⟪u' t, u t⟫ = -D(u t) - B(u t)(u t)(u t) = -D(u t) by hB and hODE
  -- Step 3: conclude HasDerivAt (½ ‖u ·‖²) (-D(u t)) t
  sorry -- ALLOW_SORRY: proof body for lean-prover; statement is final
```

**Integrated energy inequality — the bridge to EnergySkeleton (must-prove):**

```lean
/-- Abstract Galerkin energy inequality: integrating the energy identity over `[s, t]` gives
`½ ‖u(t)‖² + ∫_s^t D(u(τ)) dτ ≤ ½ ‖u(s)‖²`.

This is `EnergyInequality` (from `EnergySkeleton`) for the explicit choice
  `E(t) = ½ ‖u(t)‖²`,  `A(s, t) = ∫_s^t D(u(τ)) dτ`,  `ν = 1`.

Proof: apply `intervalIntegral.integral_eq_sub_of_hasDerivAt` to
`abstract_galerkin_energy_identity` to get
  `∫_s^t (-D(u τ)) dτ = ½‖u t‖² - ½‖u s‖²`,
then rearrange.

Key hypotheses needed:
- `abstract_galerkin_energy_identity` (the pointwise `HasDerivAt` fact above)
- `IntervalIntegrable (fun τ => -D (u τ)) volume s t`
  (continuity of `D ∘ u` on `[s,t]`, from the ODE hypothesis)
- `hst : s ≤ t`, `hs : 0 ≤ s` -/
theorem abstract_galerkin_energy_inequality
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (u   : ℝ → H)
    (D   : H → ℝ)
    (B   : H → H → H → ℝ)
    (hB  : ∀ w, B w w w = 0)
    (hD  : ∀ t, 0 ≤ D (u t))
    (hODE : ∀ t, HasDerivAt u (deriv u t) t ∧
                 ⟪deriv u t, u t⟫_ℝ + D (u t) + B (u t) (u t) (u t) = 0)
    (hint : ∀ s t, s ≤ t → IntervalIntegrable (fun τ => D (u τ)) volume s t)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    (1/2 : ℝ) * ‖u t‖^2 + ∫ τ in s..t, D (u τ) ≤ (1/2 : ℝ) * ‖u s‖^2 := by
  sorry -- ALLOW_SORRY: proof body for lean-prover; statement is final
```

**Connection lemma to EnergySkeleton (must-prove, likely `linarith`/`exact`):**

```lean
/-- The abstract Galerkin energy inequality implies `EnergyInequality` for the
`EnergyData` with `E t = ½ ‖u t‖²`, `A s t = ∫_s^t D(u τ) dτ`, `ν = 1`. -/
theorem abstract_galerkin_satisfies_EnergyInequality
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (u : ℝ → H) (D : H → ℝ) (B : H → H → H → ℝ)
    (hB  : ∀ w, B w w w = 0)
    (hD  : ∀ t, 0 ≤ D (u t))
    (hODE : ∀ t, HasDerivAt u (deriv u t) t ∧
                 ⟪deriv u t, u t⟫_ℝ + D (u t) + B (u t) (u t) (u t) = 0)
    (hint : ∀ s t, s ≤ t → IntervalIntegrable (fun τ => D (u τ)) volume s t) :
    EnergyInequality {
      E := fun t => (1/2 : ℝ) * ‖u t‖^2
      A := fun s t => ∫ τ in s..t, D (u τ)
      ν := 1
    } := by
  intro s t hs hst
  exact abstract_galerkin_energy_inequality u D B hB hD hODE hint hs hst
```

### 1.2 Mathlib API map for the Tier-1 proofs

The `lean-prover` will need exactly these lemmas (all confirmed in mathlib by grep):

| Proof step | Mathlib lemma | Module |
|---|---|---|
| `d/dt ‖u t‖² = 2⟪u t, u' t⟫` | `HasDerivAt.norm_sq` | `Mathlib.Analysis.InnerProductSpace.Calculus` |
| `d/dt ⟪f t, g t⟫ = ⟪f t, g'⟫ + ⟪f', g t⟫` | `HasDerivAt.inner` | `Mathlib.Analysis.InnerProductSpace.Calculus` |
| FTC-2 | `intervalIntegral.integral_eq_sub_of_hasDerivAt` | `Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus` |
| nonincreasing from inequality | `energy_nonincreasing_from_nonneg_dissipation` | `LerayHopf.EnergySkeleton` (already proved) |
| scalar arithmetic | `linarith`, `ring` | built-in |

The key technical friction point is the `IntervalIntegrable` hypothesis on `D ∘ u`. In the abstract tier, this is simply assumed as a hypothesis (`hint`). In the concrete NS tier (Tier 2), it would require continuity of `‖∇ uₙ(t)‖²` in `t`, which is controlled by the ODE.

### 1.3 What the Tier-1 proofs do NOT require

- Any Fourier analysis on 𝕋³.
- Any concrete definition of the NS trilinear form.
- Any divergence-theorem/integration-by-parts argument.
- Any property of `velocityProjection_n` beyond what M3 provides.
- `FiniteDimensional` — the abstract framework is valid in any `InnerProductSpace ℝ H`.

This is the reason Tier 1 is genuinely provable: it is pure Hilbert-space calculus.

---

## Tier 2 — FRONTIER (concrete NS realization; do NOT claim provable)

### 2.1 The concrete NS trilinear form

**Intended Lean statement:**
```lean
noncomputable def nsBilinearForm (u v : L2VF) : L2VF :=
  -- the vector field x ↦ ((u(x) · ∇) v)(x)
  -- i.e., ∑_j u_j(x) * ∂v/∂xⱼ (x)
  sorry -- ALLOW_SORRY: NS convective term, no mathlib gradient-on-Lp API

noncomputable def nsTrilinearForm (u v w : L2VF) : ℝ :=
  ∫ x, ⟪nsBilinearForm u v x, w x⟫_ℝ ∂haarTorus3
```

**Classification: (ii) needs mathlib infrastructure that does not exist.**

Mathlib has (confirmed by grep):
- `gradient` for `f : F → ℝ` (scalar gradient, `Mathlib.Analysis.Calculus.Gradient.Basic`).
- `fderiv` for `f : E → F` (Fréchet derivative, general Banach spaces).
- Divergence theorem for rectangular boxes in `ℝⁿ` (`MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable`), but **only on boxes `[a,b]`, not on tori**.

What is missing:
- No `(u·∇)v` operator defined for `Lp`-valued torus fields.
- No `fderiv`/`gradient` for maps between Banach spaces at the `Lp`-level (only for maps between finite-dimensional spaces or abstract Banach spaces with a global differentiability assumption).
- In particular, `fderiv ℝ v` for `v : Torus3 → VelocityValue` is not directly available via `Lp` membership — the `Lp` definition is a.e.-equivalence class and does not carry pointwise differentiability.

The standard workaround in Fourier–Galerkin formalization would be to define `nsBilinearForm` via Fourier coefficients (convolution in frequency space), but this requires a separate development not present in mathlib.

**Recommended treatment:** abstract interface hypothesis in `GalerkinApproximation` structure (PR3 in MVP plan). Do not attempt a concrete definition in M4.

### 2.2 Concrete skew-symmetry `b(u,u,u) = 0` for divergence-free u

**Intended Lean statement:**
```lean
theorem nsTrilinearForm_skew (u : L2VF) (hu : u ∈ L2Sigma) :
    nsTrilinearForm u u u = 0 := by
  -- Proof: integrate by parts on 𝕋³.
  -- ∫ ((u·∇)u)·u = ∫ ∑_{i,j} uⱼ (∂uᵢ/∂xⱼ) uᵢ
  --              = (1/2) ∫ ∑_j uⱼ ∂(‖u‖²)/∂xⱼ
  --              = (1/2) ∫ (u·∇)(‖u‖²)
  --              = -(1/2) ∫ (div u) ‖u‖² = 0   (since div u = 0)
  sorry -- ALLOW_SORRY: needs integration by parts on 𝕋³
```

**Classification: (ii) needs mathlib infrastructure that does not exist.**

The integration by parts step requires:
1. A Stokes/divergence theorem on the torus `𝕋³`. Mathlib's divergence theorem (`integral_divergence_of_hasFDerivAt_off_countable`) is for **rectangular boxes** `[a,b] ⊂ ℝⁿ`, not for quotient spaces like `UnitAddTorus (Fin 3)`. Extending it to the torus requires a "periodization" argument that would itself be a substantial formalization task.
2. The identity `(u·∇)(‖u‖²) = 2((u·∇)u)·u` at the `Lp` level, requiring pointwise calculus on the equivalence-class elements.
3. The integration-by-parts formula for `Lp` functions at the level of weak derivatives.

None of these are in mathlib for the torus.

**Recommended treatment:** `hB : ∀ w, B w w w = 0` as an abstract hypothesis (exactly what Tier 1 does). For the `nsTrilinearForm_skew` statement, keep it as a marked-sorry frontier: it is mathematically standard (first-year PDE course), but its Lean formalization requires infrastructure that genuinely does not exist in mathlib today.

### 2.3 Finite-dimensional Galerkin ODE existence

**Intended Lean statement:**
```lean
theorem galerkin_ode_exists (n : ℕ) (u₀ : L2Sigma) :
    ∃ u : ℝ → (velocityProjection_n n).range,
      (u 0 : L2VF) = velocityProjection_n n u₀ ∧
      ∀ t, HasDerivAt (fun t => (u t : L2VF)) (galerkin_rhs n (u t)) t := by
  sorry -- ALLOW_SORRY: needs Picard-Lindelöf on the finite-dim subspace
```

**Classification: (i) provable with substantial effort.**

Mathlib has:
- `IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt₀` for a `C¹` autonomous RHS on a Banach space (confirmed by grep, `Mathlib.Analysis.ODE.ExistUnique`).
- `FiniteDimensional` instances propagate to submodule types in mathlib.

What is needed:
1. The Galerkin RHS `galerkin_rhs n : Vₙ → Vₙ` must be defined (requires the NS trilinear form restricted to the finite-dim subspace `(velocityProjection_n n).range` — same as 2.1 gap).
2. Even if `galerkin_rhs` is given abstractly, one must verify it is Lipschitz (or `C¹`) in the finite-dim space. On a finite-dim space every polynomial-type map is `C^∞`, so once the RHS is properly defined, the Picard-Lindelöf condition follows from `ContDiff.contDiffAt`.

**The gate is 2.1, not 2.3.** If `nsBilinearForm` were defined, 2.3 would be provable-hard but tractable using `ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀`. Without it, 2.3 stays behind the same frontier.

**Recommended treatment:** The `ode_holds : Prop` field of the `GalerkinApproximation` structure (MVP plan PR3) absorbs this gap cleanly. Mark the concrete ODE existence as `ALLOW_SORRY` with the blocker documented.

### 2.4 Uniform energy and dissipation bounds

**Intended Lean statement:**
```lean
theorem galerkin_uniform_energy_bound (n : ℕ) (u₀ : L2Sigma) :
    ∀ t, (1/2 : ℝ) * ‖(uₙ n t : L2VF)‖^2 ≤ (1/2 : ℝ) * ‖(u₀ : L2VF)‖^2 := ...

theorem galerkin_uniform_dissipation_bound (n : ℕ) (u₀ : L2Sigma) (T : ℝ) (hT : 0 < T) :
    ∫ t in (0 : ℝ)..T, ‖∇_hs (uₙ n t)‖^2 ≤ ‖(u₀ : L2VF)‖^2 / (2 * ν) := ...
```

**Classification: (i) provable once 2.1–2.3 are available, (iii) genuine research boundary otherwise.**

These bounds follow immediately from `abstract_galerkin_energy_inequality` (Tier 1) applied to the concrete solution `uₙ`. The chain is:
- ODE existence (2.3) → the solution satisfies the abstract law → energy inequality (Tier 1) → uniform bounds.

The first bound (energy) is exactly what `abstract_galerkin_satisfies_EnergyInequality` + `energy_nonincreasing_from_nonneg_dissipation` give, once the ODE existence is in hand.

**Recommended treatment:** Defer to M4 follow-up or M5. Once Tier 1 is done, the logical structure is ready; the concrete bounds require solving 2.1 first.

---

## 3. Recommended structure for `LerayHopf/EnergyEstimate.lean`

```
LerayHopf/EnergyEstimate.lean
  ├── Section 1: AbstractGalerkinData (structure)
  ├── Section 2: abstract_galerkin_energy_identity  [TIER 1, must-prove]
  ├── Section 3: abstract_galerkin_energy_inequality [TIER 1, must-prove]
  ├── Section 4: abstract_galerkin_satisfies_EnergyInequality [TIER 1, must-prove]
  ├── Section 5: GalerkinApproximation (structure, PR3 interface)
  │     -- absorbs ode_holds, energy_identity as Prop fields (scaffold-safe)
  ├── Section 6: nsTrilinearForm, nsBilinearForm  [TIER 2, ALLOW_SORRY]
  └── Section 7: nsTrilinearForm_skew             [TIER 2, ALLOW_SORRY]
```

Sections 1–4 are the M4 deliverable. Sections 5–7 are frontier scaffolds: the structure names are fixed, the proof bodies are `ALLOW_SORRY`.

---

## 4. First lean-coder task

**Deliver (lean-coder, sorry-free):**

1. `AbstractGalerkinData` — the structure definition (no proof needed).
2. `AbstractGalerkinODELaw` — the `Prop` definition (no proof needed).
3. The import block:
   ```lean
   import LerayHopf.EnergySkeleton
   import Mathlib.Analysis.InnerProductSpace.Calculus
   import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
   ```
4. Signatures for `abstract_galerkin_energy_identity`, `abstract_galerkin_energy_inequality`, `abstract_galerkin_satisfies_EnergyInequality` with `sorry -- ALLOW_SORRY: proof body for lean-prover`.
5. Signatures for `GalerkinApproximation`, `nsTrilinearForm`, `nsTrilinearForm_skew` as scaffolds.

**Then lean-prover discharges the three Tier-1 proof bodies** (sections 1–4 above).

The lean-coder task is bounded (signature work, no proof obligations) and unblocked. The lean-prover task is bounded (pure inner-product-space calculus + FTC, no PDE).

---

## 5. Candid assessment: how far can M4 go sorry-free?

**Tier 1 can be fully sorry-free.** The three key theorems (`abstract_galerkin_energy_identity`, `abstract_galerkin_energy_inequality`, `abstract_galerkin_satisfies_EnergyInequality`) require only:
- `HasDerivAt.norm_sq` (confirmed in mathlib)
- `HasDerivAt.inner` (confirmed in mathlib)
- `intervalIntegral.integral_eq_sub_of_hasDerivAt` (confirmed in mathlib)
- `linarith` for arithmetic steps

All three should be sorry-free after lean-prover work. This is genuine mathematical content: the abstract energy identity is the core computation of the Galerkin method.

**Tier 2 cannot be sorry-free in this autonomous run.** The blocking gap is the absence of:
1. A concrete `(u·∇)v` operator for `Lp`-valued torus fields (no mathlib API).
2. Integration by parts / divergence theorem on the torus (mathlib only has boxes).
3. The resulting ODE existence is then gated on (1).

These are not close calls. The mathlib divergence theorem does not apply to quotient spaces. Building a torus divergence theorem from scratch would be a multi-month formalization project independent of M4.

**Realistic M4 outcome in one autonomous run:**
- `LerayHopf/EnergyEstimate.lean` compiles.
- Three Tier-1 theorems sorry-free.
- `GalerkinApproximation` structure with `ode_holds : Prop`, `energy_identity : Prop` fields (scaffold).
- `nsTrilinearForm`, `nsTrilinearForm_skew`, concrete `galerkin_ode_exists` all carry `ALLOW_SORRY` with precise blockers documented.
- `lake build` green.
- Sorry count: 1 (the deliberate target) + 3 marked frontier scaffolds. Zero hidden sorry.

**The three Tier-1 theorems are the M4 deliverable.** They complete the abstract energy chain: the moment the concrete NS pieces (Tier 2) can be plugged in, the energy inequality follows from already-proved abstract machinery.

---

## 6. Connections to other milestones

- **M3 → M4:** `velocityProjection_n` is the concrete `Pₙ` that instantiates `AbstractGalerkinData.u` in the concrete setting. `velocityProjection_n_preserves_L2Sigma` is the reason `Pₙ u₀ ∈ L2Sigma` and hence the Galerkin solution stays div-free.
- **M4 → M5 (compactness):** The uniform energy bound and dissipation bound (Tier 2, item 2.4) are the inputs to Aubin–Lions. They cannot be proved until 2.1–2.3 are resolved, but their logical form is already clear from the abstract energy inequality.
- **M4 Tier 1 → GalerkinPackage:** `abstract_galerkin_satisfies_EnergyInequality` is exactly the `energy_inequality_limit` field of `GalerkinCompactnessPackage` in the concrete case; it closes the `EnergySkeleton` loop.
