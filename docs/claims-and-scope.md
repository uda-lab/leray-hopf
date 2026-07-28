# Exact claims and scope

This document is the precise, field-by-field record of what the two capstone theorems
guarantee — and what they do not. It exists so that no natural-language summary (in the
README, in a talk, in a paper) can silently claim more than the Lean types actually
state. For a general-reader overview see [`README.md`](../README.md); for the module
layout see [`docs/architecture.md`](architecture.md); for the axiom/`sorry` ledger see
[`docs/STATUS.md`](STATUS.md).

## The capstones

Both are **kernel-only**: `#print axioms` returns only the standard kernel axioms
`propext` / `Classical.choice` / `Quot.sound`, with **zero project axioms** and
**no `sorryAx`**.

```lean
-- LerayHopf/Torus/GalerkinODECapstone.lean   (𝕋³)
theorem exists_lerayHopf_torus3 (u₀ : L2Sigma) (ν : ℝ) (hν : 0 < ν)
    (T : ℝ) (hT : 0 < T) :
    ∃ F : Torus3NSForms, Nonempty (LerayHopfSolutionFull F ν T u₀)

-- LerayHopf/R3/GalerkinODECapstone.lean      (ℝ³)
theorem exists_lerayHopf_r3 (u₀ : L2Sigma_R3) (ν : ℝ) (hν : 0 < ν)
    (T : ℝ) (hT : 0 < T) :
    ∃ (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊),
      Nonempty (LerayHopfSolutionFull_R3 𝔊 F ν T u₀)
```

```lean
-- LerayHopf/Torus/GlobalCapstone.lean   (𝕋³, global-in-time — issue #195)
theorem exists_global_lerayHopf_torus3 (u₀ : L2Sigma) (ν : ℝ) (hν : 0 < ν) :
    ∃ F : Torus3NSForms, ∃ u : Time → L2Sigma, ∀ T : ℝ, 0 < T →
      Galerkin.IsLerayHopfOn torusDomain F.core ν T u₀ u
```

Kernel-only (pinned by `check-axioms-live.sh`). The single curve `u` satisfies, at
every `T > 0`, exactly the five proof fields of `LerayHopfSolutionFull` (the
`IsLerayHopfOn` predicate is their field-for-field twin); coherence across horizons is
**pointwise** (`u t` is one curve), not an a.e. gluing.

Every component in the transitive dependency cones of the two capstones — the
functional-analytic backbone, the finite-dimensional ODE solver, spatial
Rellich–Kondrachov compactness, the Aubin–Lions-in-time diagonalization,
Helmholtz/curl density (Fourier route), the Mazur weak-limit closure, and the
determined-form convection extensions — is **proved sorry-free**, not assumed.
(The `LerayHopf.Experimental` opt-in, outside both cones, still carries residual
`sorry`s — see [`docs/STATUS.md`](STATUS.md).) The current project-axiom frontier
(𝕋³ = 0, ℝ³ = 0) is pinned by `scripts/check-axioms-live.sh`, a guard script run in
manually triggered GitHub Actions workflows; it runs `#print axioms` and fails on
any unexpected or missing axiom, or any `sorryAx`.

> **Honest scope.** The 𝕋³ and ℝ³ capstones are both **unconditional / kernel-only**.
> The limit-passage and compactness layers used by the capstones are proved theorems,
> not project axioms. The convection forms are proof-carrying total trilinear
> extensions pinned to the genuine Schwartz/Galerkin test-class forms, with
> fixed-test continuity; they are not claims of a canonical continuous convection
> operator on all pure `L² × L² × L²` triples. No smoothness or higher regularity
> beyond the stated energy-class properties (a.e.-in-time H¹ membership plus
> integrable viscous dissipation; see the claims table below) is claimed, and
> neither uniqueness nor non-uniqueness is claimed. Residual marked `sorry`
> declarations outside the two capstone cones are tracked in
> [`docs/STATUS.md`](STATUS.md).

Public summaries should cite the proof-carrying `LerayHopfSolutionFull` /
`LerayHopfSolutionFull_R3` structures and the capstones above — **not** a paraphrase
that claims more than the fields below.

## Modeling scope

- **No external force.** The weak identity carried by `weak_eq` has no forcing term;
  this is the homogeneous Navier–Stokes equation only.
- **Time horizon — 𝕋³ is now global-in-time; ℝ³ remains finite-horizon.** The
  finite-horizon capstones `exists_lerayHopf_torus3` / `exists_lerayHopf_r3` take
  `T : ℝ`, `hT : 0 < T` as input: for each such `T` there is a solution on `[0, T]`.
  **In addition**, the 𝕋³ global capstone `exists_global_lerayHopf_torus3` (issue #195)
  produces a **single** curve `u : Time → L²_σ` and one form bundle `F` such that the
  full finite-horizon Leray–Hopf contract holds at **every** `T > 0` simultaneously —
  global-in-time weak existence on `[0, ∞)` for 𝕋³, not a family of independently chosen
  finite-horizon witnesses. ℝ³ has no global capstone yet (P5 assessment gate). This is
  still weak (Leray–Hopf) existence only: **no** uniqueness, **no** non-uniqueness,
  **no** smoothness or higher regularity beyond the stated energy class, and the energy
  relation is the **inequality**, not equality.
- **𝕋³ is the unit torus.** `Torus3 = (AddCircle 1)³` — period **1** in each coordinate
  (not `2π`), with the Fourier basis convention `e^{2πi k·x}`; see
  `LerayHopf/Torus/Domain.lean`. ℝ³ is whole space with no periodicity.
- **Separated-variable weak formulation.** `WeakFormNS` tests against `ψ(t) · w(x)` (a
  scalar temporal factor times a fixed spatial test vector `w` from the domain's
  Galerkin/Schwartz div-free test class), not a general space-time test function
  `φ(t, x)`. The relation to the standard space-time test formulation is **out of
  scope** — this repository neither proves nor assumes it; see `WeakFormNS`'s
  docstring in `LerayHopf/EvolutionTriple.lean`.

## Claims table

Every mathematical claim below is matched to the exact field/theorem that carries it,
so that no natural-language paraphrase can silently claim more than the type. `D`
ranges over the generic `Galerkin.Domain` (`torusDomain` or `r3Domain 𝔊`);
`LerayHopfSolutionFull(_R3)` are abbreviations for `Galerkin.LerayHopfSolution`.

| Natural-language claim | Field / theorem | What is actually guaranteed |
|---|---|---|
| The solution curve stays divergence-free | `LerayHopfSolution.u : Time → ↥D.σ` | Type-level: `u t` is valued in the closed divergence-free subspace `σ` for every `t`, by construction. |
| `u` solves the weak Navier–Stokes equation | `weak_eq : WeakFormNS ν T (D.evolution C) u` | Holds against separated-variable tests `ψ(t)·w(x)` (see "Modeling scope" above); no forcing term. |
| Energy inequality | `energy_ineq` | `½‖u(t)‖² + ∫₀ᵗ dissip(ν, u(s)) ds ≤ ½‖u₀‖²` for `t ∈ [0, T]` (not for all `t ≥ 0`). |
| Initial condition is attained | `initial_trace` | `u(t) → u₀` in the ambient-L² norm as `t → 0⁺` — a **one-sided trace at `t = 0` only**. This is *not* a claim of weak continuity on all of `[0, T]`. |
| a.e.-in-time H¹ regularity | `energy_class.1` | `∀ᵐ t ∈ [0, T], regMem (u t)` (a.e. H¹ membership). |
| Viscous dissipation is integrable | `energy_class.2` | `IntervalIntegrable (fun s => dissip ν (u s)) volume 0 T`. |
| `u ∈ L²(0,T;H¹_σ)` (literal Bochner space membership) | — **not a field** | **Not claimed.** `energy_class` gives a.e. pointwise H¹ membership plus integrable dissipation — not Bochner `MemLp` valued in `H¹` as a Banach space. The measurability field below is into the *ambient* L² space, not into H¹, so it does not upgrade the a.e. statement to a literal Bochner-space membership. |
| `u` is measurable as a function of time | `u_aestronglyMeasurable` | `AEStronglyMeasurable (fun t => (u t : D.X)) …` on `[0, T]`, valued in the **ambient L² Hilbert space** `D.X` (not H¹). |
| `u ∈ C_w([0,T]; L²_σ)` (weak continuity in time) | — **not a field** | **Not claimed as a public guarantee.** Only the one-sided trace at `t = 0` (`initial_trace`) is exposed as a field; general-`t` weak continuity is a deliberate non-inclusion — a definitional choice of this repository's public structure, not a proof gap (see `docs/formalization-review-ja.md` §4.2 for the internal-construction note). |
| Existence on 𝕋³ | `exists_lerayHopf_torus3` | For every `u₀ ∈ L²_σ`, `ν > 0`, `T > 0`: `∃ F, Nonempty (LerayHopfSolutionFull F ν T u₀)`. |
| Existence on ℝ³ | `exists_lerayHopf_r3` | For every `u₀ ∈ L²_σ(ℝ³)`, `ν > 0`, `T > 0`: `∃ 𝔊 F, Nonempty (LerayHopfSolutionFull_R3 𝔊 F ν T u₀)`. |
| Global-in-time existence on 𝕋³ | `exists_global_lerayHopf_torus3` | For every `u₀, ν>0`: `∃ F, ∃ u, ∀ T>0, IsLerayHopfOn torusDomain F.core ν T u₀ u` — ONE curve valid on every `[0,T]`. Weak existence only; no uniqueness/smoothness. |
| Galerkin-level approximate solutions exist | `Galerkin.SolutionData` (per `n`) | An **intermediate** structure (per-`n` finite-dimensional Galerkin ODE data with uniform bounds) — not itself the final solution; consumed by `Galerkin.CompactnessPackage` / `exists_lerayHopf_from_package` on the way to `LerayHopfSolution`. |

Nothing above is a smoothness, uniqueness, or non-uniqueness claim.

## Import guide

`import LerayHopf` is the **complete release surface**: both capstones plus every
supporting layer, and it is **sorry-free and axiom-free, with no placeholder
namespaces** — statically enforced in CI by `scripts/check-release-cone.sh`, which
walks the transitive import closure of `LerayHopf.lean` and fails if any file it
reaches contains a `sorry` or an `axiom`/`constant`/`opaque`/`unsafe` (marked or
unmarked), or a `Scaffold`/`Placeholder`/`Stub`/`Draft` namespace. Narrower imports
are also available for consumers who only need one piece:

| Import | Brings in | Status |
|---|---|---|
| `import LerayHopf.Core` | Axiom-free, `sorryAx`-free spatial/regularity layer shared by both domains (L²_σ spaces, Leray/Galerkin projections, Fourier machinery). | Sorry-free, axiom-free. |
| `import LerayHopf.Torus.Capstone` | The full 𝕋³ capstone chain, `exists_lerayHopf_torus3`. | Kernel-only (no project axioms, no `sorryAx`). |
| `import LerayHopf.R3Capstone` | The full ℝ³ capstone chain, `exists_lerayHopf_r3`. | Kernel-only (no project axioms, no `sorryAx`). |
| `import LerayHopf` | Everything above, plus the remaining supporting files needed to assemble both capstones (Bochner Gelfand-triple time theory used by the R3 limit-passage chain, Galerkin ODE solvers, etc.). | **Sorry-free, axiom-free, no placeholder namespaces.** |
| `import LerayHopf.Experimental` | Explicit **opt-in** for incomplete Bochner time-layer work not needed by either capstone: `Bochner.TimeSobolevAC`, `Bochner.TimeMollification`, `Bochner.TimeMollifierInterval`, `Bochner.TimeSobolevExperimental`. | Contains all remaining `sorry`s; see that file's docstring for the per-module inventory and [`docs/STATUS.md`](STATUS.md) for the current count and locations. `TimeSobolevExperimental`'s `w1pTime_continuous_in_H` is restricted to `p = q = 2` — its prior generic-`p,q` statement was found FALSE (explicit `p = q = 1` counterexample; see `docs/postmortems/2026-07-w1ptime-false-statement.md`). |

Nothing reachable from `import LerayHopf` imports `LerayHopf.Experimental`, and
nothing in `LerayHopf.Experimental` is needed by either capstone — the split is
enforced, not just documented.
