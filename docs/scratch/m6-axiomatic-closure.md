# M6 — Sound minimal-axiom closure of T³ Leray–Hopf existence

Orchestrator design contract for the axiomatic closure. Builds on the Plan-agent
statement-level design; the **orchestrator deltas** below OVERRIDE it where they conflict.
Authority: the approved plan `ssot-reference-list-cuddly-meteor.md` + this file.

## Architecture (resolved)

We do NOT build the H¹_σ Hilbert space (user directive). Abstract over a real Hilbert
space `H` plus a **regularity functional** `reg : H → ℝ` (the "‖·‖²_V"), with spatial
compactness supplied as an explicit hypothesis (discharged on T³ by the proved
`rellich_seq_compact`; an axiom on R³). This is the sound core of Aubin–Lions and matches
`rellich_seq_compact` exactly.

## File / commit staging (de-risked)

- **Commit 1 (foundational, NO axioms):** `H1Sigma.lean` + `EvolutionTriple.lean`.
  All concrete/provable. Axiom-free, sorry-free after the prover pass.
- **Commit 2 (the 4 axioms + assembly), gated by the Codex axiom audit:**
  `AxiomaticClosure.lean` + spine wiring + `LerayHopf.lean`/`STATUS.md`.

## Commit 1 — `H1Sigma.lean`

`import LerayHopf.VelocityGalerkin / SobolevTorus / RellichEmbedding`. In `namespace LerayHopf`:

- `def h1EnergySq (u : L2VF) : ℝ := ∑ j, ∑' k, (1 + ∑ i, (k i:ℝ)^2) * ‖mFourierCoeff3 (L2VF_projComponentC j u) k‖^2`
- `theorem h1EnergySq_nonneg (u) : 0 ≤ h1EnergySq u`  (positivity)
- `def memH1VF (u : L2VF) : Prop := ∀ j, memH1Torus (L2VF_projComponentC j u)`
- `def memH1Sigma (u : L2VF) : Prop := u ∈ L2Sigma ∧ memH1VF u`
- `def viscousFormSq (ν : ℝ) (u : L2VF) : ℝ := ν * ∑ j, ∑' k, (2*Real.pi)^2 * (∑ i, (k i:ℝ)^2) * ‖mFourierCoeff3 (L2VF_projComponentC j u) k‖^2`
  — the **(2π)²** is load-bearing (defect 8); it is the true gradient energy of `e^{2πi k·x}`.
- `theorem viscousFormSq_nonneg {ν} (hν : 0 ≤ ν) (u) : 0 ≤ viscousFormSq ν u`
- `theorem rellich_L2Sigma (M : ℝ) (u : ℕ → L2VF) (hmem : ∀ n, u n ∈ L2Sigma) (hH1 : ∀ n, memH1VF (u n)) (hbound : ∀ n, h1EnergySq (u n) ≤ M^2) : ∃ (φ : ℕ → ℕ) (g : L2VF), StrictMono φ ∧ g ∈ L2Sigma ∧ Tendsto (fun n => u (φ n)) atTop (𝓝 g)`
  — **prover target** (componentwise `rellich_seq_compact` ×3 + diagonal extraction + pass
  `DivFreeL2` to the limit). Hardest proof in commit 1; it is *provable* (not a frontier
  sorry). NOTE the tsum convention: `hH1` (memH1VF, i.e. summability) is REQUIRED — a bare
  `h1EnergySq ≤ M²` does NOT give summability (tsum returns 0 off the summable set).

## Commit 1 — `EvolutionTriple.lean`  (lightened DissipativeEvolution)

`import LerayHopf.H1Sigma / EnergyEstimate` + interval-integral. The bundle carries ONLY
what `WeakFormNS` + the energy law need (the galerkin/compactness machinery stays in the
T³-concrete assembly, NOT in the bundle — this removes the Plan doc's 3 sorry fields):

```
structure DissipativeEvolution where
  H : Type*
  instNACG : NormedAddCommGroup H
  instIPS  : InnerProductSpace ℝ H
  instCS   : CompleteSpace H
  reg : H → ℝ
  reg_nonneg : ∀ u, 0 ≤ reg u
  viscousForm : H → H → ℝ
  convForm : H → H → H → ℝ
  convForm_antisymm : ∀ u v w, convForm u v w = - convForm u w v
```
- `theorem DissipativeEvolution.convForm_self_zero (E) (u : E.H) : E.convForm u u u = 0`
  (`have := E.convForm_antisymm u u u; linarith`) — `b u u u = 0` is a LEMMA, not an axiom.
- `def WeakFormNS (ν T : ℝ) (E : DissipativeEvolution) (u : Time → E.H) : Prop` — test
  functions `ψ : Time → ℝ`, `HasCompactSupport ψ`, `tsupport ψ ⊆ Set.Ioo 0 T` (compact
  support in the **OPEN** interval ⇒ endpoint terms vanish; defect 2), `ContDiff ℝ 1 ψ`,
  spatial `w : E.H`; identity `∫ t in 0..T, (-(⟪u t, w⟫_ℝ)*deriv ψ t + ψ t*(E.viscousForm (u t) w + E.convForm (u t) (u t) w)) = 0`.
  Use `letI := E.instNACG; letI := E.instIPS`. If abstract-instance resolution fights you,
  FALL BACK to stating `WeakFormNS` concretely over `L2Sigma`+forms and flag it — the math
  is identical; this is a Lean-ergonomics fallback, not a soundness change.

## Commit 2 — `AxiomaticClosure.lean` (the 4 axioms — Codex-audited BEFORE proving)

### A4 — convection + viscous forms. **NON-VACUITY IS THE CRUX.**
A bare abstract `b` with only antisymmetry + bound is satisfiable by `b := 0` ⇒ the theorem
would silently prove **Stokes/heat**, not Navier–Stokes (overclaim). A4 MUST pin `b` to the
genuine convection form. Target (in priority order):

1. **Preferred:** define a concrete `convectionFormFourier (u v w : L2VF) : ℝ` via the
   Fourier triple sum of `((u·∇)v)·w` (coefficients of `(u·∇)v` are the convolution
   `∑_{k+l=m} û_j(k)·(2πi l_j)·v̂_i(l)`; pair with `ŵ`). Then `b := convectionFormFourier`
   is a FIXED def (so `b=0` is excluded by construction), and A4 axiomatizes only its
   genuinely-missing analytic ESTIMATES: antisymmetry-on-div-free and the **true 3D**
   continuity bound `|b u v w| ≤ C·√(h1EnergySq u)·√(h1EnergySq v)·‖w‖` (defect 6; the false
   2D bound `≤C‖u‖‖v‖‖w‖` is NOT used). The Stokes form is likewise a Fourier multiplier —
   prefer `stokes` CONCRETE with `stokes u u = viscousFormSq 1 u`, so the (2π)² is load-bearing.
2. **Fallback if the triple-sum def is too heavy to typecheck cleanly:** keep a
   `Torus3NSForms` structure but ADD a pinning field calibrating `b` to the concrete
   convection value on the **finite-dimensional Galerkin subspaces** (finite sums, no
   convergence issue) — enough to exclude `b=0`. Add `stokes_eq : ∀ u, stokes u u = viscousFormSq 1 (u:L2VF)`.
   **FLAG this for the Codex non-vacuity audit explicitly.**

Either way `b u u u = 0` is the proved lemma; antisymmetry is `b u v w = -b u w v`.

### A1 `galerkin_ode_solution` (per-`n`) — returns `GalerkinSolutionData F ν u₀ n` with:
`u : Time → L2Sigma`; `u 0 = Pₙu₀`; range in `Vₙ` (`(u t:L2VF)=velocityProjection_n n (u t)`);
the **projected ODE** tested against `Vₙ` (inner-product form with `F.stokes`, `F.b`);
`HasDerivAt` for `(u ·:L2VF)`; **`reg_mem : ∀ t, memH1VF (u t)`** (REQUIRED for Rellich, tsum
convention); uniform `energy_bound : ½‖u t‖² ≤ ½‖Pₙu₀‖²`; uniform **n-independent**
`reg_bound : ∫₀ᵀ h1EnergySq(u t) ≤ Cbnd` with an honest n-independent RHS (e.g.
`T*‖u₀‖² + ‖u₀‖²/(2ν)` — true since `h1EnergySq ≤ ‖·‖²_{L²} + viscousFormSq 1`, energy
monotone, `‖Pₙu₀‖≤‖u₀‖`; a generous larger RHS is fine and SAFER). Temam III.3.

### A2 `aubin_lions` — Aubin–Lions, **spatial half discharged not axiomatized**.
Takes the Galerkin sequence + its uniform energy/reg bounds + an explicit **spatial-compactness
hypothesis whose statement is exactly `rellich_L2Sigma`'s** (the assembly passes
`rellich_L2Sigma`), and produces `∃ φ u, StrictMono φ ∧` strong `L²(0,T;H)` convergence,
stated as `Tendsto (fun n => ∫ t in 0..T, ‖galSeq (φ n) t - u t‖²) atTop (𝓝 0)`. So A2 adds
ONLY the genuinely-missing Bochner-time half (defect 3). Temam III.2.1.

### A3 `galerkin_limit_passage` — consumes the structured Galerkin sequence + A2's strong
limit, concludes `WeakFormNS ν T (torus3Evolution …) u ∧ energy-inequality(lsc) ∧ initial-trace`.
Temam III.3. (Initial trace: `Tendsto (fun t=>(u t:L2VF)) (𝓝[≥] 0) (𝓝 (u₀:L2VF))`.)

`torus3Evolution F : DissipativeEvolution` := `H:=L2Sigma, reg:=h1EnergySq∘coe, viscousForm:=F.stokes,
convForm:=F.b, convForm_antisymm:=F.b_antisymm` — **sorry-free** (no galerkin/compact fields now).

### Proof-carrying spine + assembly
`LerayHopfSolutionFull F ν T u₀` / `GalerkinCompactnessPackageFull …` with PROOF fields
(`weak_eq : WeakFormNS …`, `energy_ineq : ∀ t…`, `initial_trace : Tendsto…`) (defect 1).
`build_galerkin_package` (A1→A2 with `rellich_L2Sigma`→A3) → `exists_lerayHopf_from_package_full`
(copies proofs) → `exists_lerayHopf_torus3 (u₀:L2Sigma)(ν)(hν:0<ν)(T)(hT:0<T) : ∃ F, Nonempty (LerayHopfSolutionFull F ν T u₀)`.

### Spine wiring
Keep the OLD `LerayHopfSolution`/`GalerkinCompactnessPackage`/`exists_lerayHopf_from_galerkin_package`/
`exists_lerayHopf_torus3_statement` untouched (no renames; the `_statement` sorry stays as the
original scaffold target). The new proof-carrying `*Full` types + `exists_lerayHopf_torus3` are
the genuine results. Add the 3 new imports to `LerayHopf.lean`.

## Guardrails
Every `axiom` line: same-line `-- ALLOW_AXIOM: <reason + Temam/RRS ref>` + a `## Assumptions`
section + `docs/STATUS.md` ledger entry. Names avoid the reserved overclaim terms. Every `sorry`
gets `-- ALLOW_SORRY:`. `#print axioms exists_lerayHopf_torus3` must list EXACTLY the 4 axioms
(+ propext/Choice/Quot) — no `sorryAx`.

## Defect-fix checklist (all must hold)
(1) proof-carrying fields ✓ (2) WeakFormNS endpoints vanish via tsupport⊆Ioo 0 T ✓
(3) A2 spatial half discharged via rellich_L2Sigma, not axiomatized ✓ (4) **A4 pins b ≠ 0**
(non-vacuity — the crux above) ✓ (5) A1 has the actual ODE ✓ (6) true 3D bound ✓
(7) no false assembly sorries (bounds come from A1 fields) ✓ (8) (2π)² in viscousFormSq, made
load-bearing via stokes_eq ✓
