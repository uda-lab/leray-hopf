# Phase R3 — removal path for `aubin_lions_R3` (4 → 3 project axioms)

Planning artifact (read-only). Target: take `exists_lerayHopf_r3_axiomatic` from 4 project
axioms to 3 by eliminating `aubin_lions_R3`. Live code read in worktree
`/workspaces/lean-pde-wt/lane-r3-15` (branch `lane-r3/aubinlions-15`, base `origin/main` 88813c8).

Source of truth: `docs/leray_hopf_lean_mvp_plan.md`, `docs/milestone.md`, `AGENTS.md`,
`docs/guardrails.md`. This document only sequences; it invents no statement.

---

## 1. FEASIBILITY VERDICT — **GREEN-THIN (4 → 4 swap), NOT GREEN-REMOVE**

The honest, count-aware verdict is **GREEN-THIN**: the centerpiece constructor
`aubinLionsPackage_R3_of_timeCompactness` can be wired into the assembly in place of
`aubin_lions_R3`, but it consumes a `TimeCompactnessInput` whose `uniform_time_modulus` field
**cannot be discharged from the available `GalerkinSolutionData_R3` data**. So removing
`aubin_lions_R3` only re-exposes the *same* Bochner-time-compactness content as a new marked
axiom `Nonempty (TimeCompactnessInput …)` (or a direct `timeCompactnessInput_R3` axiom). The
project-axiom **count does not drop**; it is a strictly *thinner* axiom (a uniform L² modulus of
continuity in time, no subsequence / no limit / no spatial content), mirroring the NS-form thin
swaps in PRs #22 / #24.

It is **NOT** GREEN-REMOVE, because GREEN-REMOVE additionally requires that
`TimeCompactnessInput` be dischargeable from `galSeq`. It is not — see §3. The lane's prize (4→3)
is **not reachable** on the current `GalerkinSolutionData_R3` interface.

It is **NOT** RED: nothing here is mathematically false, and the two open `sorry`s are not
fundamentally blocked (see §2 for the realistic assessment — but note the C2 body is a large
multi-step assembly, and the weighted Steklov–Jensen `sorry` is a genuine `convL2_coeFn_ae`-class
mathlib gap that is *hard*, see §2.2 / §5).

### Why not GREEN-REMOVE — the verdict-determining fact (one paragraph)

`TimeCompactnessInput.uniform_time_modulus` asserts an **n-uniform L² modulus of time
continuity** of the Galerkin curves: `∀ε>0 ∃δ>0 ∀n ∀s,t∈[0,T], |s−t|<δ ⇒ ‖uₙ(s)−uₙ(t)‖_{L²}<ε`.
The only fields of `GalerkinSolutionData_R3` (`AxiomaticClosure.lean:350–392`) that touch time
regularity are: `u_hasDeriv` (pointwise differentiability in `L2VF_R3` at forward times, with the
derivative being an **unquantified** `deriv (fun s => u s) t`), the **weak** ODE identity `u_ode`
(an inner-product identity tested only against `w ∈ Vₙ`), the n-uniform energy bound
`‖uₙ(t)‖ ≤ ‖u₀‖`, and the **time-integrated** n-uniform H¹ bound
`∫₀ᵀ viscousFormSq_R3 ν (uₙ t) ≤ ½‖u₀‖²` (`reg_bound`). The standard Bochner–Sobolev derivation of
this modulus controls `‖uₙ(s)−uₙ(t)‖_{L²}` via a **dual-norm (V′) bound on u′ₙ** —
`‖u′ₙ‖_{L^{4/3}(0,T;V′)} ≤ C` — coming from `u′ₙ = −νAuₙ − Pₙ B(uₙ,uₙ)` and the
`H^{-1}`/V′ estimate of the convection term. **None of those quantitative dual bounds is a field
of `GalerkinSolutionData_R3`.** `b_bound` (`AxiomaticClosure.lean:254`) is only `|b(u,v,w)| ≤
C(w)·‖u‖·‖v‖` against a **fixed Schwartz test `w`**, with `C` depending on `w` — it is *not* a
uniform V′ operator bound, and `Vₙ` is not a fixed Schwartz test. The file's own header
(`AubinLionsLimitPassage.lean:89–92`) states this exactly: the modulus is "derivable IN PRINCIPLE
from `u_hasDeriv` + the energy/regularity bounds, but whose vector-valued-Sobolev packaging
mathlib LACKS (no `W^{1,p}(0,T;X)`, no weak time derivative, no Aubin–Lions lemma)." So the modulus
is an honest *frontier hypothesis*, not a derivable lemma, on the current interface. Discharging it
would require either (a) mathlib's absent vector-valued Sobolev / Aubin–Lions theory, or (b)
**strengthening `GalerkinSolutionData_R3` with a new quantitative `u′ₙ` dual-norm bound field** —
which is itself a non-trivial analytic claim that would have to be substantiated upstream (in the
ODE-construction layer `GalerkinODESolve.lean`) and is out of scope for this lane.

**Decisive bottom line for the lane:** do **not** attempt 4→3. Pursue the GREEN-THIN swap if the
owner wants the axiom *shape* improved (thinner, more honest, mirrors #22/#24); otherwise the lane
yields no count reduction and should be reported as such. A "GREEN-REMOVE" claim here would be
wrong and would waste the lane.

---

## 2. Closure strategy for the two open `sorry`s

These are needed for the GREEN-THIN swap (the constructor must be `sorry`-free for the swap to be
honest), and they are the actual engineering payload of the lane regardless of the count outcome.

### 2.1 `aubinLionsPackage_R3_of_timeCompactness` (C2 body, `AubinLionsLimitPassage.lean:870–953`)

The single `sorry` at `:953` must produce **all four** fields of `AubinLionsPackage_R3`
(`AxiomaticClosure.lean:454–498`): `φ`, `φ_mono`, `u`, `u_aestronglyMeasurable`,
`strong_convergence`. What is unproved:

1. **Subsequence + limit extraction (`φ`, `φ_mono`, `u`).** Route (Steklov interval-averaging,
   already adjudicated viable in the in-body comment `:904`):
   - Build interval averages `steklovAvg gs δ t` (def `:635`, proved helpers
     `steklovAvg_norm_le_u0` `:643`, `steklovAvg_approx` `:680`).
   - Bound the averages' H¹ seminorm via `viscousFormSq_steklovAvg_le_average` (`:823`, the
     §2.2 `sorry`) combined with `reg_bound` ⇒ the averaged states carry an **n-uniform pointwise
     H¹ bound** (which the raw samples lacked).
   - Feed the averaged states (at the finitely-many per-δ-mesh base points) into P3
     `spatialInput_R3_of_localRellich B` (`:113`) to extract a common ball-restricted spatial
     limit and subsequence.
   - **Boundary strip `(T−δ,T]`** (`:911`, `:939`): the forward window `[t,t+δ]` leaves `[0,T]`,
     so `Htime.uniform_time_modulus` (both times in `[0,T]`) does not feed `steklovAvg_approx`.
     Fix: use **backward/clipped averages** over `[t−δ,t] ⊆ [0,T]` on that strip (define a
     `steklovAvgBack`, or reuse `steklovAvg` at base `t−δ`); the existing helpers transfer with the
     window reflected. This is a real sub-task, not free.
2. **`strong_convergence` (the `eLpNorm`-form `Tendsto`, `:493`).** δ-mesh ε/3 diagonalization:
   raw↔avg error → 0 (`steklovAvg_approx` + modulus), avg spatial convergence (P3), mesh refinement.
   Mathlib APIs: `MeasureTheory.eLpNorm_add_le` / `eLpNorm_sub` triangle, `Filter.Tendsto`
   ε/3 via `Metric.tendsto_atTop`, `tendsto_setIntegral_of_monotone` (already used `:424`),
   `eLpNorm_mono_measure`. Diagonal subsequence: `Filter.extraction`-style / explicit `Nat.rec`.
3. **`u_aestronglyMeasurable` (`:473`).** Discharge via the D2 primitive
   `aeStronglyMeasurable_of_spaceTimeL2` (`Bochner/TimeSobolev.lean`, referenced `:951`) applied
   to the assembled limit curve once (2) is built. Needs the local space-time L² convergence the
   constructor itself produces, so it is downstream of (2).

**Closable sorry-free given `TimeCompactnessInput`?** YES in principle (the route is sound and all
sub-pieces have mathlib analogues), but it is a **large multi-lemma assembly** (sub-lemmas:
`steklovAvgBack` + its `_approx`/`_norm` analogues; the per-δ finite spatial extraction; the ε/3
diagonalization; the measurability transport). Realistically 8–15 new private lemmas. It is the
heaviest engineering item in the lane and depends on §2.2 being closed first (step 1 needs the H¹
Jensen bound). Treat as **must-prove but multi-PR**.

### 2.2 `viscousFormSq_steklovAvg_le_average` (`:823`, ALLOW_SORRY `:850`)

After `rw [FourierL2.viscousFormSq_R3_eq_integral_normSq_fourier]` (`:832`) the goal is, per
component `j` and summed, a **weighted spectral Jensen bound**:

  `∑ⱼ ∫_ξ (2π)²‖ξ‖² ‖𝓕(projⱼ(steklovAvg)) ξ‖² dξ ≤ δ⁻¹ ∫_s ∑ⱼ ∫_ξ (2π)²‖ξ‖² ‖𝓕(projⱼ(uₛ)) ξ‖²`.

Proved sorry-free already and reusable: the L²-element commute
`fourier_proj_steklovAvg_eq` (`:757`) gives `𝓕(projⱼ(steklovAvg)) = δ⁻¹ • ∫_s 𝓕(projⱼ(uₛ))` as an
`L2C_R3` element; the scalar Jensen template `norm_integral_sq_le_length_mul_integral_normSq`
(`:551`); the L²-level instance `steklovAvg_normSq_le_average` (`:721`).

The genuine gap (the `sorry`): from the **L²-element** identity to a **pointwise-in-ξ** identity
`(δ⁻¹ • ∫_s 𝓕(projⱼ(uₛ))) ξ =ᵐ[ξ] δ⁻¹ • ∫_s (𝓕(projⱼ(uₛ))) ξ`, plus a **jointly
`(s,ξ)`-measurable representative**, so that the per-ξ scalar Jensen can be applied and the result
**Tonelli-swapped** against the **unbounded weight `(2π)²‖ξ‖²`**:
`∫_ξ w(ξ)·δ⁻¹∫_s ‖·‖²  =  δ⁻¹∫_s ∫_ξ w(ξ)‖·‖²`.

Intended closure strategy (the honest assessment is that this is HARD and may not close on mathlib
alone — see ranking §5):
- coeFn-of-Bochner-integral interchange: target `MeasureTheory.Lp.coeFn` + a coeFn-pushes-through-
  Bochner-integral lemma. The repo's `convL2_coeFn_ae` (`FrechetKolmogorov.lean`) is the *same
  obstruction class*; the comment `:846` says mathlib has no such lemma. Candidate mathlib hooks:
  `MeasureTheory.L2.integral_inner` style identities, `ContinuousLinearMap.integral_comp_comm`
  (already used for the *element* level), but **none** gives the pointwise-a.e. coeFn of an
  `Lp`-valued Bochner integral against an unbounded multiplier.
- per-ξ scalar Jensen: `norm_integral_sq_le_length_mul_integral_normSq` instantiated at each `ξ`
  (pointwise) — but this needs the pointwise integrand, i.e. requires the coeFn interchange first.
- weighted Tonelli: `MeasureTheory.lintegral_lintegral_swap` / `MeasureTheory.integral_integral_swap`
  for the `(s,ξ)` double integral, gated on a **jointly measurable** nonnegative integrand
  `(s,ξ) ↦ (2π)²‖ξ‖²‖(𝓕(projⱼ(uₛ)))ξ‖²` and on `σ`-finiteness (both `volume` on `[t,t+δ]` and on
  `ℝ³_ξ` are σ-finite — OK). The danger is precisely the **unbounded weight**: it blocks the
  L²-element / `Lp`-norm route (the weighted norm is not an `Lp`-norm), forcing the raw `(s,ξ)`
  double-integral route, which then *needs* the global jointly-measurable coeFn representative that
  mathlib does not hand you.

**Closable sorry-free?** UNCERTAIN — this is the riskiest item. Best realistic outcome: closable
with substantial bespoke measurability work IF a jointly-`(s,ξ)`-measurable representative of
`(s,ξ) ↦ (𝓕(projⱼ(uₛ)))ξ` can be constructed from the curve's continuity (the curve is continuous
in `s` into `L2C_R3`; pick a strongly-measurable representative via
`MeasureTheory.AEStronglyMeasurable` of the continuous-in-`s` `Lp`-valued map and
`MeasureTheory.Lp` joint-measurability lemmas). If that representative cannot be produced
sorry-free, this `sorry` is a genuine `convL2_coeFn_ae`-class mathlib-absence and the constructor
cannot be made fully sorry-free — in which case **even the GREEN-THIN swap regresses** (it would
trade one axiom for an axiom *plus* a retained `sorry`), and the lane should stop and report RED on
this sub-item. **This must be resolved/spiked FIRST** (see §5 ordering).

---

## 3. `TimeCompactnessInput` discharge analysis (field by field)

`structure TimeCompactnessInput` has **one** field (`AubinLionsLimitPassage.lean:98–105`):

- **`uniform_time_modulus`** — `∀ε>0 ∃δ>0 ∀n ∀s,t∈[0,T], |s−t|<δ ⇒ ‖uₙ(s)−uₙ(t)‖_{L²} < ε`.
  **NOT dischargeable** from `GalerkinSolutionData_R3`. Reasoning (the §1 paragraph, restated
  against each candidate source):
  - from `u_hasDeriv` (`:365`): gives differentiability but `deriv` is **unquantified**; no
    `‖u′ₙ(t)‖`-bound ⇒ no MVT/FTC modulus. Even with FTC
    (`‖uₙ(s)−uₙ(t)‖ ≤ ∫ₛᵗ ‖u′ₙ‖`), the integrand has no n-uniform bound.
  - from `u_ode` (`:374`): a **weak** identity tested against `w ∈ Vₙ`; recovering `‖u′ₙ‖_{L²}`
    or `‖u′ₙ‖_{V′}` from it requires a uniform inf-sup / dual bound on `νA + PₙB`, absent here.
    `b_bound` is per-fixed-Schwartz-`w` with `w`-dependent constant — **not** a uniform dual bound,
    and `Vₙ ≠` a fixed Schwartz test.
  - from `energy_bound` (`:381`) / `reg_bound` (`:390`): n-uniform but only give
    `‖uₙ(t)‖ ≤ ‖u₀‖` (pointwise) and the **time-integrated** H¹ bound — neither yields a
    *modulus of continuity* (the integrated bound controls `∫₀ᵀ‖∇uₙ‖²`, not short-time L² drift).

  **Conclusion:** `TimeCompactnessInput` IS the irreducible Bochner-time-compactness frontier on
  this interface. It is exactly the L²-modulus content of `‖uₙ‖_{W^{1,p}(0,T;X)} ≤ C`, which
  mathlib lacks. ⇒ GREEN-THIN, not GREEN-REMOVE.

**Contrast (the asymmetry that makes the spatial half removable but the time half not):** the
*spatial* `LocalRellichInput` argument of the constructor IS constructible axiom-free, because the
repo proved `frechetKolmogorov_holds : FrechetKolmogorovInput` sorry-free
(`FrechetKolmogorov.lean:1863`) and
`localRellichInput_of_frechetKolmogorov frechetKolmogorov_holds : LocalRellichInput`
(`RellichBall.lean:603`) — this is exactly how `spatial_compactness_R3` was discharged in issue #2
(`AxiomaticClosure.lean:436–437`). So the `(B : LocalRellichInput)` binder of
`aubinLionsPackage_R3_of_timeCompactness` is **NOT** a blocker. Only the time half is.

---

## 4. Wiring to perform the GREEN-THIN swap (drop the axiom, add the thin one)

### 4.1 New thin axiom (replaces `aubin_lions_R3`)

In `AxiomaticClosure.lean`, *after* `import LerayHopf.R3.AubinLionsLimitPassage` becomes available
(see acyclicity note 4.4), delete `axiom aubin_lions_R3` (`:514–530`) and add:

```
axiom timeCompactnessInput_R3 -- ALLOW_AXIOM: uniform L² time-modulus of the Galerkin curves
    (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊) (ν T : ℝ) (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n) :
    TimeCompactnessInput 𝔊 F ν T u₀ galSeq
```

This axiom is **strictly thinner** than `aubin_lions_R3`: it asserts only a uniform modulus of
continuity (a single field), supplying neither subsequence nor limit nor spatial compactness — all
of which `aubin_lions_R3` previously asserted and which are now *derived* by
`aubinLionsPackage_R3_of_timeCompactness`. State plainly in the marker and assumptions section:
**this does NOT reduce the axiom count (4→4), it thins one axiom**, mirroring #22/#24.

### 4.2 Rewire the assembly `build_galerkin_package_R3_of_galSeq` (`AxiomaticClosure.lean:656–676`)

Replace Step 1 (`:662–663`):

```
  have alPkg : AubinLionsPackage_R3 𝔊 F ν T u₀ galSeq :=
    aubin_lions_R3 𝔊 F ν hν T hT u₀ galSeq spatial_compactness_R3
```

with:

```
  have B : LocalRellichInput :=
    localRellichInput_of_frechetKolmogorov frechetKolmogorov_holds
  have alPkg : AubinLionsPackage_R3 𝔊 F ν T u₀ galSeq :=
    aubinLionsPackage_R3_of_timeCompactness 𝔊 F ν hν T hT u₀ galSeq B
      (timeCompactnessInput_R3 𝔊 F ν T u₀ galSeq)
```

Step 2 (`galerkin_limit_passage_R3`) and Step 3 (packing) are unchanged. `hν`, `hT` are already in
scope. `B` is axiom-free (kernel axioms only).

### 4.3 Pin updates

- `scripts/check-axioms-live.sh:169` — drop `LerayHopf.aubin_lions_R3`, add
  `LerayHopf.timeCompactnessInput_R3`. (Comment block `:24` likewise.)
- `scripts/print_axioms.lean:25` — same substitution in the expected-set comment.
- Net live R3 axiom set stays size 4: `{curlSchwartzDense_holds (or its current name),
  r3_NSForms_exist, galerkin_limit_passage_R3, timeCompactnessInput_R3}` — i.e. `aubin_lions_R3`
  out, `timeCompactnessInput_R3` in. **No size change** (this is the GREEN-THIN reality).
- Update `HANDOFF.md:80`, `docs/STATUS.md:110`, `docs/ROADMAP.md:28,81`, `docs/REPORT.md:135` to
  reflect the swap (planner/sot-researcher edits, not Lean).

### 4.4 Import / acyclicity

`AxiomaticClosure.lean` currently does **not** import `AubinLionsLimitPassage.lean`; the latter
imports the former (`AubinLionsLimitPassage.lean:70`). The swap needs
`aubinLionsPackage_R3_of_timeCompactness` and `TimeCompactnessInput` **at the assembly site**,
which is in `AxiomaticClosure.lean`. **This is a cycle** if done naively.

Resolution (REQUIRED — Hard rule 10): do **not** import `AubinLionsLimitPassage` into
`AxiomaticClosure`. Instead **relocate the assembly** `build_galerkin_package_R3_of_galSeq` (and
the thin `timeCompactnessInput_R3` axiom, and `B`-construction) **downstream**, into a new small
module `LerayHopf/R3/AubinLionsAssembly.lean` that imports both `AxiomaticClosure` and
`AubinLionsLimitPassage`. The capstone `GalerkinODECapstone.lean` (which calls
`build_galerkin_package_R3_of_basis` → `…_of_galSeq`) then imports the new assembly module instead
of getting the builder from `AxiomaticClosure`. Verify `GalerkinODECapstone` does not also feed
back into `AubinLionsLimitPassage` (it does not — `AubinLionsLimitPassage` is a leaf,
`AubinLionsLimitPassage.lean:68`). This keeps the DAG acyclic. **The `coder` must do this
relocation; it is the structurally load-bearing step.**

(Alternative considered and rejected: moving `aubinLionsPackage_R3_of_timeCompactness` *up* into
`AxiomaticClosure` — rejected because it drags P3/`SpatialCompactness`, `TrilinearEstimate`,
`FourierL2` imports up into the axiom-declaration module, violating Hard rule 10's
minimal-import intent and the file's standalone role.)

---

## 5. Ordered task list + risk ranking

### Ordered tasks

1. **[prover — SPIKE FIRST]** Attempt `viscousFormSq_steklovAvg_le_average` (§2.2). This is the
   gate: if the weighted coeFn-interchange + jointly-`(s,ξ)`-measurable representative cannot be
   built sorry-free, **STOP** and report RED on the constructor (the thin swap would regress to
   axiom+sorry). Time-box; do not let it sink the lane silently.
2. **[coder]** Add `steklovAvgBack` (backward/clipped Steklov average over `[t−δ,t]`) + signatures
   for its `_approx` / `_norm_le_u0` analogues (boundary-strip handling, §2.1 step 1).
3. **[prover]** Prove the `steklovAvgBack` analogues (reflect existing `:643`/`:680`/`:721` proofs).
4. **[coder]** Add private signatures for the per-δ-mesh finite spatial extraction wrapper and the
   ε/3 diagonalization scaffold inside `aubinLionsPackage_R3_of_timeCompactness`.
5. **[prover]** Discharge the C2 body (§2.1): subsequence/limit, `strong_convergence`,
   `u_aestronglyMeasurable` (via `aeStronglyMeasurable_of_spaceTimeL2`). Constructor sorry-free.
6. **[coder]** Create `LerayHopf/R3/AubinLionsAssembly.lean`; relocate
   `build_galerkin_package_R3_of_galSeq`; add `axiom timeCompactnessInput_R3`; rewire (§4.2);
   repoint `GalerkinODECapstone` import.
7. **[coder]** Delete `axiom aubin_lions_R3`; update its assumptions-section entry.
8. **[planner/sot]** Pin scripts (§4.3) + docs.
9. **[orchestrator]** `bash scripts/agent-preflight.sh`; `#print axioms exists_lerayHopf_r3_axiomatic`
   shows `timeCompactnessInput_R3` in place of `aubin_lions_R3`, count unchanged at 4.

### Codex `/codex:adversarial-review` points (statements before proofs)

- `axiom timeCompactnessInput_R3` — the new thin axiom statement (no-overclaim: must NOT name or
  encode the time-derivative bound it omits; it is a bare modulus).
- `steklovAvgBack` def + its lemma *statements*.
- Any new signature added to `AubinLionsLimitPassage.lean` for the C2 assembly.
- The relocation diff (acyclicity) in `AubinLionsAssembly.lean`.

### Riskiest 2–3 lemmas, ranked, with fallbacks

1. **`viscousFormSq_steklovAvg_le_average` (§2.2) — HIGHEST RISK.** The unbounded `(2π)²‖ξ‖²`
   weight blocks the `Lp`-norm/element route and forces a raw `(s,ξ)` double integral needing a
   global jointly-measurable coeFn representative — the `convL2_coeFn_ae` obstruction. **Fallback:**
   if not closable, keep it as the single retained `ALLOW_SORRY` and DO NOT claim the constructor
   sorry-free; then the swap is *not* honest and the lane should report RED (no axiom move). Do
   **not** convert this `sorry` into a new axiom (owner floor: removal/proof only on the relevant
   item; a thin *time* swap is permitted, but smuggling this spectral `sorry` into an axiom is a
   *different* axiom and not sanctioned).
2. **C2 `strong_convergence` δ-mesh diagonalization (§2.1 step 2) — HIGH.** Large multi-lemma
   ε/3 assembly with the boundary-strip wrinkle. **Fallback:** land the interior-window content
   first behind smaller lemmas; the boundary strip via backward averages is the most error-prone —
   if it resists, isolate it as a named private lemma with a precise TODO (Hard rule 8) rather than
   weakening `strong_convergence`.
3. **`u_aestronglyMeasurable` joint-measurability transport (§2.1 step 3) — MEDIUM.** Depends on
   `aeStronglyMeasurable_of_spaceTimeL2` applying cleanly to the Steklov-assembled limit.
   **Fallback:** if the D2 primitive's hypotheses don't match, derive measurability directly from
   the `eLpNorm`-limit (Lp-limit of measurable approximants is measurable:
   `aestronglyMeasurable` of an `eLpNorm`-`Tendsto` limit).

---

## Appendix — key live references

- Axiom to remove: `AxiomaticClosure.lean:514` (`aubin_lions_R3`), conclusion `AubinLionsPackage_R3`
  (`:454–498`); call site `build_galerkin_package_R3_of_galSeq` (`:656–676`, the `aubin_lions_R3`
  application at `:663`).
- Constructor to wire in: `aubinLionsPackage_R3_of_timeCompactness` (`AubinLionsLimitPassage.lean:870`).
- Frontier hypothesis: `TimeCompactnessInput` (`:98–105`), single field `uniform_time_modulus`.
- Open `sorry`s: C2 body `:953`; weighted Steklov–Jensen `:850`.
- Spatial half is axiom-free: `frechetKolmogorov_holds` (`FrechetKolmogorov.lean:1863`),
  `localRellichInput_of_frechetKolmogorov` (`RellichBall.lean:603`),
  `spatial_compactness_R3` discharge (`AxiomaticClosure.lean:436`).
- Pins: `scripts/check-axioms-live.sh:169`, `scripts/print_axioms.lean:25`.
