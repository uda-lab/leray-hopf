# Cores B/C feasibility scout — the final 4 project axioms

READ-ONLY scout. Goal: drive R3 (now 2 axioms) and torus (now 3 axioms) to ZERO. After
core A (in-progress torus convection), the four remaining are the two **compactness** axioms
(B) and the two **limit-passage** axioms (C), one of each per domain.

## Exact statements + consumption

| # | axiom | file:line | consumed by |
|---|-------|-----------|-------------|
| R3-B | `galerkin_spacetime_precompact_R3` | `LerayHopf/R3/ArzelaAscoliTime.lean:123` | `perBall_ae_subseq` → `diag_ae_subseq` → `u_lim_aestronglyMeasurable` (T4 assembly) → feeds `AubinLionsPackage_R3` (`AubinLionsLimitPassage.lean`) |
| R3-C | `galerkin_limit_passage_R3` | `LerayHopf/R3/AxiomaticClosure.lean:558` | `AubinLionsAssembly.lean:84` (`build_galerkin_package_R3_of_galSeq`) → capstone |
| T-B | `aubin_lions` (torus) | `LerayHopf/AxiomaticClosure.lean:367` | `AxiomaticClosure.lean:533` (`build_galerkin_package_of_galSeq`, with `spatial := rellich_L2Sigma`) → capstone |
| T-C | `galerkin_limit_passage` (torus) | `LerayHopf/AxiomaticClosure.lean:421` | `AxiomaticClosure.lean:538` → capstone |

## Mathematical content (precise function-space setting)

- **R3-B** — REFINE-CAPABLE LOCAL Aubin–Lions–Simon. For every subsequence `ψ` and every ball
  radius `k`, the per-ball Galerkin curves `restrictToBall k (galSeq (ψ ·)).u` have a further
  subsequence converging to a limit `g_k` in the **Bochner norm `L²(0,T; L²(B_k))`** (`eLpNorm …
  2 (volume.restrict (Icc 0 T)) → 0`). The `ψ`-input (refine-capability) is what powers the
  Cantor-diagonal nesting over balls `k`, since `galSeq n` has level `n` in its dependent type
  and cannot be reindexed. Spatial half (local Rellich H¹(B_k)↪↪L²(B_k)) is **already PROVED**
  axiom-free via the Fréchet–Kolmogorov chain (`spatial_compactness_R3`, issue #2). The axiom
  adds ONLY the **Bochner-time** half (time-equicontinuity from the integrated reg-bound + Steklov
  modulus + δ→0 diagonalization).

- **T-B** — Aubin–Lions time compactness, spatial half presented as the hypothesis `spatial`
  (discharged at the call site by the proved compact-domain `rellich_L2Sigma`, `H1Sigma.lean:170`).
  The axiom body asserts: from the Galerkin sequence + spatial-compactness hypothesis, produce an
  `AubinLionsPackage` (a strongly-`L²(0,T;L²_σ)`-convergent subsequence). Same Bochner-time content
  as R3-B but on the **compact torus T³** — so it is GLOBAL (no ball exhaustion), and the spatial
  input is the simpler whole-domain Rellich, not the local one.

- **R3-C / T-C** — Lions–Magenes / Temam III.3 limit passage. Input: the Aubin–Lions package
  (strong-L² limit `alPkg.u`). Output: existence of a **good representative** `u` that is
  (1) a.e.-equal to `alPkg.u`, (2) satisfies `WeakFormNS` (nonlinear term passes via `b_bound` on
  strong convergence), (3) the energy inequality (lsc of the L² norm), (4) the initial trace
  `u(t)→u₀` as `t→0⁺`, (5) the energy class (a.e. `memH1VF` + integrable dissipation). The hard
  kernel is the **weakly-continuous representative in `L²(0,T;H¹_σ)`** — exactly the Lions–Magenes
  embedding `W¹ᵖ(0,T;Gelfand-triple) ↪ C([0,T];H)`.

## mathlib coverage (present vs ABSENT)

**ABSENT (the load-bearing gaps):**
- **No Bochner-valued Aubin–Lions / Fréchet–Kolmogorov compactness in `L²(0,T;X)`.** No
  `AubinLions`, no Fréchet–Kolmogorov `Lp`-precompactness, no time-equicontinuity → totally-bounded
  bridge. This is the entire content of B (both domains). Ascoli exists
  (`Topology/UniformSpace/Ascoli.lean`) but only the abstract equicontinuous→compact form, with no
  L²-in-time modulus machinery to feed it.
- **No Lions–Magenes embedding** `W¹ᵖ(0,T;V,V') ↪ C([0,T];H)` (no weak-time-derivative space, no
  Aubin–Lions–Simon, no continuous-representative theorem). This is the kernel of C.
- **No Eberlein–Šmulian / reflexive weak-sequential-compactness** (`grep` for `Eberlein`,
  `Smulian`, `weaklyCompact`, `IsReflexive` weak-seq: empty). Banach–Alaoglu exists only in the
  weak-* `WeakDual` form (`WeakDual.isCompact_closedBall`, `isCompact_polar`), NOT as
  "bounded sequence in a Hilbert space has a weakly-convergent subsequence."

**PRESENT (reusable building blocks):**
- `MeasureTheory.Lp` over `volume.restrict (Icc 0 T)` + completeness
  (`LpSpace/Complete.lean`); `eLpNorm` API.
- `tendstoInMeasure_of_tendsto_eLpNorm` + `TendstoInMeasure.exists_seq_tendsto_ae`
  (`ConvergenceInMeasure.lean`) — already used to turn B's L²-time convergence into an a.e.-t
  subsequence in `ArzelaAscoliTime.lean`.
- Weak topology (`Analysis/LocallyConvex/WeakSpace.lean`), Riesz dual
  (`InnerProductSpace.Dual`) — already used for the Mazur weak-closedness step
  (`weakLimit_mem_L2Sigma_R3`, WL-5).
- Bochner interval IBP (`IntervalIntegral/IntegrationByParts.lean`), FTC
  (`FundThmCalculus.lean`), dominated convergence — backbone for C's energy/trace conjuncts.
- **In-repo, axiom-free already:** R3 local Rellich (`spatial_compactness_R3`, FK chain),
  torus Rellich (`rellich_L2Sigma`), the whole Steklov toolkit (see Reuse).

## Existing partial proofs / scaffolds (DO NOT rebuild)

- **R3 is far more built than torus.** `R3/AubinLionsLimitPassage.lean` (~1430 lines) proves
  axiom-free: the Steklov interval-average toolkit (`steklovAvg` + `steklovAvg_norm_le_u0` uniform
  L² bound, `steklovAvg_inVn`, `steklovAvg_mem_sigma`, `steklovAvgBack`, `steklovAvg_approx`
  time-modulus estimate), `galerkin_norm_le_u0`, `galerkin_curve_continuous`,
  `kineticEnergy_lsc_bound` (E1), `bForm_tendsto_of_strongL2`, and the spatial half of the
  Aubin–Lions assembly via the `steklovAvg_spatial_extraction` chain over the FK-derived
  `LocalRellichInput`. The centerpiece `aubinLionsPackage_R3_of_timeCompactness` is sorry-free
  GIVEN the extraction; the single irreducible piece is the B axiom.
- **C is partially scaffolded domain-neutrally** in `Bochner/TimeSobolev.lean` +
  `Bochner/GelfandTriple.lean`: `GelfandTriple` + `ofDissipativeEvolution` (sorry-free),
  `IsWeakTimeDeriv`, `isWeakTimeDeriv_unique`, `hasDerivAt_isWeakTimeDeriv` (strong⇒weak),
  `W1pTime.ofHValuedDeriv` (all sorry-free). BUT the kernel
  `w1pTime_continuous_in_H` (D1, the Lions–Magenes good-representative embedding) is an **open
  `sorry` explicitly tagged MONTHS-CLASS** (`TimeSobolev.lean:480`). That is C's wall, already
  scouted and declared months-class in the body.
- **Torus B/C have NO dedicated scaffold** — no torus `AubinLionsLimitPassage`, no torus Steklov
  toolkit. Only the spatial Rellich (`rellich_L2Sigma`) and the abstract `GelfandTriple` layer
  (shared) exist.

## Tractability ranking (most → least removable)

1. **R3-B `galerkin_spacetime_precompact_R3`** — most tractable. Spatial half PROVED; the entire
   Steklov time-modulus toolkit is built and sorry-free; only the time-equicontinuity →
   per-ball-L²-precompact extraction remains. This is "assemble existing pieces + the δ→0
   diagonalization," not new theory from scratch. Highest built-infrastructure ratio.
2. **T-B `aubin_lions`** — second. SAME Bochner-time content as R3-B but GLOBAL on compact T³
   (no ball exhaustion → strictly simpler once R3-B's time half exists), and the spatial input is
   the simpler whole-domain `rellich_L2Sigma`. Blocked mainly by the MISSING torus Steklov
   scaffold, which R3-B would teach how to port.
3. **R3-C `galerkin_limit_passage_R3`** — third. Hard (Lions–Magenes embedding) but its kernel
   `w1pTime_continuous_in_H` is already scaffolded domain-neutrally with a precise statement; the
   energy/trace/weak-eq conjuncts have mathlib IBP/FTC backing. Declared MONTHS-CLASS.
4. **T-C `galerkin_limit_passage`** — least, but **near-free once R3-C lands**: the Gelfand-triple
   / `W1pTime` layer is domain-neutral, so the same `w1pTime_continuous_in_H` discharge serves both.
   Ranked last only because it strictly follows R3-C.

## Recommended ATTACK ORDER

**R3-B → T-B → R3-C → T-C** (compactness pair first, then limit-passage pair).
Rationale: B is the higher-built, lower-theory pair and clears the longest end-to-end path; the
C pair shares one domain-neutral kernel (`w1pTime_continuous_in_H`) so it is one months-class
proof spent once, harvested twice. Do B as a paired removal (R3 teaches torus), then C as a paired
removal (one Gelfand-triple kernel).

## PR-0 SPIKE target for the #1 pick (R3-B)

Mirror the torus Route-F discipline (validate `convFormFourier_antisymm` before committing the
build). The single make-or-break lemma to validate first:

> **Per-ball L²-in-time precompactness from the Steklov modulus + local Rellich.** For fixed `k`,
> prove that the sequence `n ↦ restrictToBall k ∘ (galSeq (ψ n)).u`, viewed in `L²(0,T; L²(B_k))`,
> is **totally bounded** — by combining (a) the proved uniform Steklov time-modulus
> (`steklovAvg_approx` + `steklovAvg_norm_le_u0`) for time-equicontinuity, with (b) the proved
> local Rellich `spatial_compactness_R3` at the δ-mesh base-points for spatial precompactness —
> then extract one convergent subsequence (mathlib `Lp` completeness + the existing
> `tendstoInMeasure → exists_seq_tendsto_ae` bridge).

Concretely: produce, for a SINGLE ball `k` and a SINGLE `ψ`, the conclusion of
`galerkin_spacetime_precompact_R3` (the `∃ ρ, g_k, … eLpNorm → 0`). If that one-ball case closes
sorry-free from existing toolkit, the refine-capable axiom is mechanical Cantor diagonalization
(the `diag_ae_subseq` tower already exists as a CONSUMER, so the wiring is known). If it does NOT
close, the wall is the time-modulus → totally-bounded bridge — stop and reassess before scaffolding.

## Reuse across domains (R3 ↔ torus)

- **B↔B: strong mirror, ASYMMETRIC build state.** Identical Bochner-time mathematical core; R3 is
  GLOBAL-via-ball-exhaustion while torus is directly GLOBAL on compact T³. R3-B is the harder of
  the two (the ball-exhaustion/diagonal layer is R3-specific overhead), so doing R3-B first yields
  a *superset* of the torus time-machinery; T-B then = "port the Steklov toolkit to the torus +
  drop the ball exhaustion." Pair them, R3 first. The axiom docstrings themselves flag
  "reusable for torus #23."
- **C↔C: strongest mirror — literally shared kernel.** The `Bochner/TimeSobolev.lean` +
  `GelfandTriple.lean` layer is domain-neutral by construction; `w1pTime_continuous_in_H` is the
  single Lions–Magenes embedding that BOTH `galerkin_limit_passage_R3` and `galerkin_limit_passage`
  defer to. Discharging it once + wiring each domain's `r3Evolution`/`torus3Evolution` through
  `ofDissipativeEvolution` removes both C axioms. Plan C as a single proof harvested twice.

## Biggest risk per core

- **R3-B:** the time-equicontinuity → totally-bounded-in-`L²(0,T;X)` bridge has NO mathlib support;
  the Steklov modulus gives equicontinuity but converting that to total boundedness of the
  time-integrated family is the unbuilt step. Risk: this bridge is itself substantial, not just
  "wiring." (Spike target above is designed to expose exactly this.)
- **T-B:** no torus Steklov scaffold exists — risk is underestimating the port cost (the R3 toolkit
  is ~1400 lines and FK-specific). Mitigated by sequencing after R3-B.
- **R3-C / T-C:** `w1pTime_continuous_in_H` is **declared MONTHS-CLASS in-repo** — the Lions–Magenes
  weakly-continuous-representative theorem with zero mathlib coverage (no weak-time-derivative
  space, no Eberlein–Šmulian). This is the single largest wall of the four; honest assessment is
  that C is genuinely months-class and should not be promised as a one-PR removal. Per the
  "months-class is a banned excuse" memory, it warrants a real multi-PR build plan, but the
  spike-first discipline must be applied to D1 before committing.
