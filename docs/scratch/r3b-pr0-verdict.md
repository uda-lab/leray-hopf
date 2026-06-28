# PR-0 verdict — R3-B `galerkin_spacetime_precompact_R3` go/no-go

**Spike file:** `LerayHopf/Scratch/R3BSpike.lean` (scratch-only, `-- SCRATCH` top, not for merge).
**Build:** `flock /tmp/lean-build.lock lake build LerayHopf.Scratch.R3BSpike` → **green**
(`Build completed successfully (3096 jobs)`). One `sorry` (line 98), marked `ALLOW_SORRY: scratch`,
sitting exactly on the make-or-break bridge. STEP 2 typechecks sorry-free at the wiring level.

CI note: GitHub Actions is budget-blocked; this was verified LOCALLY only, as instructed.

## Verdict: **NO-GO for a one-PR removal.** The make-or-break bridge is a substantial unbuilt theorem.

The time-equicontinuity → totally-bounded-in-`L²(0,T;X)` bridge (STEP 3) is **NOT "wiring of
existing pieces."** It is a genuine from-scratch theorem with zero mathlib support, and it is gated
on a SECOND missing fact (the uniform strong-L² time modulus, STEP 1) that the `GalerkinSolutionData_R3`
interface provably does not supply. Removing the axiom is a real multi-PR Bochner-Aubin–Lions build,
not a thin swap. Scope below.

---

## What the spike established (per step)

### STEP 2 — spatial precompactness at a fixed time. **PROVED-available, axiom-free.**
`spatial_compactness_R3` is on the public surface and `sorry`-free (FK–Rellich chain, issue #2).
`step2_spatial` wires it for `n ↦ (galSeq n).u t₀` and typechecks sorry-free given the two uniform
bounds (`‖·‖ ≤ M` from `energy_bound`; `viscousFormSq ≤ M²` from `reg_bound`). The spatial half is
genuinely done. **This is the only one of the three steps that is "wiring."**

### STEP 1 — time-equicontinuity from a uniform L² time modulus. **WALL #1 (sound-derivation gap).**
The Steklov toolkit in `AubinLionsLimitPassage.lean` (`steklovAvg_approx`, `clampedAvg_approx`,
`eLpNorm_raw_sub_clampedAvg_le`) converts a uniform-in-`n` **strong-L²** time modulus
`‖(galSeq n).u s − (galSeq n).u t‖_{L²} < ε for |s−t|<δ` into the `eLpNorm` raw↔Steklov-average
estimate. **Every one of those lemmas takes that modulus as a HYPOTHESIS (`hmod`); none derives it.**

The modulus itself is isolated in-repo as `TimeCompactnessInput.uniform_time_modulus`
(`AubinLionsLimitPassage.lean:114`) and is **never discharged anywhere** (`grep` confirms: only ever
consumed, never produced). It cannot be obtained as a cheap consequence of the ODE: a prior agent's
`galerkin_equicontinuity_from_ODE` axiom was **DELETED as UNSOUND** (documented at
`ArzelaAscoliTime.lean:13-18`) because the Galerkin ODE controls `u'` only in the **dual/V\* norm**,
finite-dimensional norm-equivalence constants are **not uniform in `n`**, and the convection term is
not L²-dual-bounded from the H¹ energy alone. The honest strong-L² modulus is the integrated
`W^{1,p}(0,T;X)`-Bochner–Sobolev bound, whose vector-valued-Sobolev packaging mathlib lacks
(no `W^{1,p}(0,T;X)`, no weak time derivative). This is why the live axiom was made **unconditional**
— it *absorbs* the modulus precisely because the modulus is not provable from the interface.

### STEP 3 — the bridge: equicontinuity + spatial-net ⟹ totally bounded ⟹ convergent subseq. **WALL #2 (missing mathlib theorem).**
`step3_bridge` states the exact axiom conclusion for one `(k, ψ)`. Even GIVEN the STEP-1 modulus,
closing it requires the δ-time-mesh + spatial-net argument that upgrades pointwise-in-time local
spatial precompactness + time equicontinuity into **total boundedness in the Bochner space
`L²(0,T; L²(B_k))`**, followed by a convergent-subsequence extraction. **Mathlib has none of this:**
no Bochner-valued Aubin–Lions, no Fréchet–Kolmogorov-`Lp`-precompactness, no
equicontinuity→totally-bounded bridge in `L²(0,T;X)`. (`Topology/UniformSpace/Ascoli.lean` is the
abstract equicontinuous→compact form only, with no L²-in-time modulus machinery to feed it.) The
single `sorry` in the spike sits exactly here.

---

## Is the bridge "wiring" or "a substantial unbuilt theorem"?

**Substantial unbuilt theorem — and there are TWO walls, not one.** The roadmap's PR-0 framing
assumed the Steklov modulus toolkit already delivered STEP 1 ("the proved uniform Steklov
time-modulus"). The spike refutes that: the Steklov lemmas are **conditional on** the strong-L²
modulus `hmod`, which is itself unproved and provably not a dual-norm ODE consequence. So the work is:

1. **The strong-L² time modulus (STEP 1)** — a genuine Bochner–Sobolev `W^{1,p}(0,T;X)` interpolation
   bound. Requires either (a) a weak-time-derivative / vector-valued Sobolev embedding layer (overlaps
   the C-axiom Lions–Magenes kernel `w1pTime_continuous_in_H`, already declared MONTHS-CLASS), or (b) a
   bespoke L²-in-time modulus from the energy identity that does NOT route through the dual norm. Both
   are real builds; (a) shares the C wall.
2. **The Bochner Aubin–Lions / Fréchet–Kolmogorov-in-time compactness kernel (STEP 3)** — the
   equicontinuity-in-time + spatial-precompactness ⟹ relatively-compact-in-`L²(0,T;X)` theorem. This
   is the actual Aubin–Lions–Simon engine, absent from mathlib. From-scratch.

The legacy Steklov scaffold (`steklovAvg_spatial_extraction`, `clampedAvg`, the `eLpNorm` raw↔avg
bound) is **not even consumed** by the live assembly: `aubinLionsPackage_R3_of_timeCompactness`
(`AubinLionsLimitPassage.lean:1442`) bypasses it entirely, going straight through
`galerkinSpaceTimeExtraction_R3` → `u_lim_aestronglyMeasurable` → `diag_ae_subseq` →
`perBall_ae_subseq` → **the axiom**. The δ-mesh assembly that would chain Steklov into total
boundedness was abandoned (issue #15 collapse) in favor of isolating the whole thing as the axiom.
So there is no half-built bridge to finish — only a partially-built modulus toolkit that is itself
gated on an unproved hypothesis. The lemmas are `private` to that module, so even reusing them is a
refactor, not a one-import wiring.

## Scope if pursued (eyes-open, per the months-class-is-not-an-excuse directive)

This is a **multi-PR Bochner-Aubin–Lions build**, comparable in scope to the R3-C / T-C
`w1pTime_continuous_in_H` wall (the bc-feasibility scout itself ranks R3-B #1 only on
*built-infrastructure ratio*, with the time half flagged as the load-bearing risk — that risk is now
confirmed real). Honest decomposition:

- **PR-A (foundation):** a weak-time-derivative / `W^{1,p}(0,T;X)` layer sufficient for the strong-L²
  time modulus. This is shared infrastructure with the C pair (Gelfand-triple `TimeSobolev.lean`),
  so it should be planned jointly with R3-C, not duplicated. Weeks-to-months.
- **PR-B (modulus):** discharge `UniformL2TimeModulus` for the Galerkin curves from PR-A + the energy
  identity. Medium once PR-A lands.
- **PR-C (compactness kernel):** the Bochner Fréchet–Kolmogorov-in-time / Aubin–Lions–Simon theorem
  (equicontinuity + spatial net ⟹ totally bounded ⟹ convergent subseq in `L²(0,T; L²(B_k))`). This
  is the genuine new mathlib-grade theorem. The hardest single piece.
- **PR-D (discharge):** replace `galerkin_spacetime_precompact_R3` with PR-C applied per `(k, ψ)`;
  the Cantor-diagonal consumer tower (`perBall_ae_subseq` → `diag_ae_subseq`) already exists, so the
  refine-capable wiring is known and cheap.

## Recommended PR plan

**Do NOT scaffold a one-PR R3-B removal.** Recommend instead:

1. **Re-pair the attack order.** Because STEP 1 shares the `W^{1,p}(0,T;X)` / weak-time-derivative
   layer with the C-axiom kernel, the bc-feasibility "B-pair before C-pair" order is suboptimal for
   R3-B specifically: its time half *depends on* the same months-class layer C needs. Plan the
   weak-time-derivative foundation ONCE (PR-A above) and harvest it for both R3-B's modulus and
   R3-C's Lions–Magenes embedding.
2. **The one genuinely R3-B-specific new theorem is PR-C** (Bochner Aubin–Lions–Simon compactness).
   That is the make-or-break and should be its own metaplan'd build with its own PR-0 spike on the
   totally-bounded extraction (the abstract `Ascoli` + `Lp` completeness route vs a direct
   Fréchet–Kolmogorov-in-time mollification proof).
3. **T-B is strictly downstream** of R3-B's PR-C (it reuses the same kernel on compact T³, dropping
   ball exhaustion), so it stays sequenced after, as the scout said.

## Which steps compiled vs walled (spike)

| Step | Lean object | Status |
|---|---|---|
| STEP 2 spatial | `step2_spatial` | **typechecks sorry-free** (wiring of public `spatial_compactness_R3`); residue = two uniform bounds (mechanical) |
| STEP 1 modulus | `UniformL2TimeModulus`, `step1_modulus_is_assumed` | **WALL #1** — modulus is an unprovable-from-interface hypothesis (mirrors never-discharged `TimeCompactnessInput.uniform_time_modulus`; dual-norm ODE route was deleted as UNSOUND) |
| STEP 3 bridge | `step3_bridge` | **WALL #2** — single `sorry`; the equicontinuity→totally-bounded→convergent-subseq theorem in `L²(0,T;X)`, NO mathlib support, from-scratch |

**Bottom line:** the bridge is a substantial unbuilt theorem (two walls: the strong-L² time modulus
and the Bochner Aubin–Lions–Simon compactness kernel), not assembly of existing pieces. NO-GO for a
single PR; GO as a metaplan'd multi-PR build whose time-Sobolev foundation should be shared with the
R3-C / T-C kernel.
