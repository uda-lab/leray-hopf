# STATUS — autonomous run ledger

> **Current axiom frontier (2026-07-05):** R3 capstone = **0 project axioms — UNCONDITIONAL
> (kernel-only).** `galerkin_limit_passage_R3` PROVED as a theorem (issue #4, PR-6, 2026-07-05 —
> `LerayHopf/R3/LimitPassage.lean`; R3 frontier 1 → 0).
> `galerkin_spacetime_precompact_R3` DISCHARGED (issue #46 PR-4 — axiom → theorem, R3 frontier 2 → 1).
> `r3ConvectionGapOp_exists` PROVED as `r3ConvectionGapOp_holds` (issue #56, PR #60).
> `#print axioms exists_lerayHopf_r3` = `[propext, Classical.choice, Quot.sound]`.
> **T³ capstone = 0 project axioms — UNCONDITIONAL (kernel-only).**
> `aubin_lions` REMOVED (issue #23, T-AL-6 Stage C, 2026-07-04) via the mode-wise
> spectral route (`torusAubinLionsPackage_of_galSeq`, `TorusAubinLionsAssembly.lean`);
> `#print axioms exists_lerayHopf_torus3` = `[propext, Classical.choice, Quot.sound]`
> only — no project axioms, no `sorryAx`.  T³ frontier 1 → 0.
> Previous T³ removals: `galerkin_limit_passage` (issue #25 / PR #75),
> `torusConvectionGap_exists` (issue #53 / PR #62), `galerkin_ode_solution` (issue #24).
> Live pin: `bash scripts/check-axioms-live.sh`.
> Milestone-table and ledger rows below are historical (dated by their PR/issue refs);
> where a row's axiom count conflicts with this banner, the banner wins.

Running ledger for the autonomous build of Leray–Hopf weak existence on the real
3-torus. This file is the **integrity backstop and final report**: every `sorry` and
every `axiom` in the Lean sources is listed here with a reason, a reference, and a
plan to discharge it. Higher-level scope/posture: the original approved plan,
`docs/archive/milestone.md` (archived, historical — both capstones are long past it).

## Goal (authoritative)

Build the Leray–Hopf weak-existence formalization on the **real 3-torus and ℝ³**, bottom-up
on mathlib toward an **unconditional Leray–Hopf existence theorem**
(`u₀ ∈ L²_σ ⇒ ∃ Leray–Hopf weak solution`). **Both capstones are UNCONDITIONAL (kernel-only):**
`exists_lerayHopf_torus3` (T³) and `exists_lerayHopf_r3` (ℝ³) each have
`#print axioms` = `[propext, Classical.choice, Quot.sound]` — zero project axioms.
Residual marked `sorry` outside both capstone cones is documented below.

Roadmap: M1 spine ✅ → M2 real domain & function spaces → M3 Galerkin `Pₙ` + Leray `Π_div`
→ M4 finite-dim Galerkin ODE + energy identity → M5–7 compactness + Aubin–Lions on T³
(Fourier-tail Rellich, the crux) + limit passage ⇒ unconditional T³.

**Posture:** maximal depth, minimal axioms. Prove what mathlib supports; axiomatize only
the true frontier (each with `ALLOW_AXIOM` + reference + ledger entry); leave
provable-but-unfinished pieces as *marked* `sorry`, never as weakened/vacuous/renamed
statements.

**Method:** branch `autorun/leray-hopf-torus3`, 1 milestone = 1 commit gated by
`bash scripts/agent-preflight.sh` green. Strict role delegation to subagents
(planner/coder/reviewers = sonnet, prover = fable; read-only reviewers) under their
`.claude/agents/*.md` contracts; orchestrator owns Codex `--effort xhigh` calls and
maintains this ledger as the final report.

## Milestone status

| # | Milestone | State |
|---|---|---|
| M1 | Structural spine (Basic/Statement/GalerkinPackage/ExistenceFromPackage/EnergySkeleton) | **superseded** (2026-07-11, issue #112 PR-D): `LerayHopf/GalerkinPackage.lean` and `LerayHopf/ExistenceFromPackage.lean` — and their public names `GalerkinCompactnessPackage` / `exists_lerayHopf_from_galerkin_package` — were **deleted**. Both capstones are long past this M1 stage; the generic package/existence plumbing this row describes now lives in `LerayHopf/Galerkin/Domain.lean` + `LerayHopf/Galerkin/SolutionBundles.lean` as `Galerkin.CompactnessPackage` / `Galerkin.exists_lerayHopf_from_package`, consumed by the R3/Torus lanes via the `…Full` abbrevs (`GalerkinCompactnessPackageFull_R3`, `GalerkinCompactnessPackageFull`, etc.). See `docs/architecture.md` for the current module layout. **Also superseded (2026-07-17, issue #144):** `LerayHopf/Statement.lean` and the placeholder `LerayHopfSolution` in `Torus/Basic.lean` — the row's `Statement` component — were **deleted**, closing out the M1 vacuity caveat by removal rather than refinement (see "Known scaffold caveats" above). |
| Side A/B | Blow-up lower bound · nonuniqueness statement | Branch A (`BlowupLowerBound.lean`) done. Branch B (`NonuniquenessStatement.lean`, `LerayHopfNonunique`) **deleted (2026-07-17, issue #144)** — it was built on the same placeholder `LerayHopfSolution` deleted from `Torus/Basic.lean` and was not a genuine non-uniqueness claim. |
| M2 | Real domain & function spaces (Torus3, L²(T³), L²_σ, H¹, Bochner) | **done** (axiom-free) |
| M3 | Galerkin P_n + Leray Π_div (Fourier multipliers) | **done** (axiom-free) |
| M4 | Finite-dim Galerkin ODE + energy identity | **abstract done** (axiom-free); concrete = frontier |
| M5–7 | Compactness + Aubin–Lions on T³ + limit passage → unconditional T³ | **DONE** — Rellich axiom-free; limit passage PROVED (#25 / PR #75); `aubin_lions` REMOVED (issue #23 T-AL-6, mode-wise spectral route) → T³ existence is now **UNCONDITIONAL** (zero project axioms) |
| M6 | **Sound minimal-axiom closure of T³ existence** (`exists_lerayHopf_torus3`) | **DONE (UNCONDITIONAL)** — closed modulo 4 project axioms; all four burned to zero: `galerkin_ode_solution` proved (#24), `torusConvectionGap_exists` proved (#53 / PR #62), `galerkin_limit_passage` proved (#25 / PR #75), `aubin_lions` proved via mode-wise spectral route (#23, T-AL-6 Stage C, `torusAubinLionsPackage_of_galSeq`); `#print axioms` = kernel-only; abstract evolution framework reused by R³ |
| R3 | **Whole-space ℝ³ Leray–Hopf existence** (`exists_lerayHopf_r3`) — the real target (Leray 1934) | **DONE (UNCONDITIONAL)** — **0 project axioms, KERNEL-ONLY** (`galerkin_limit_passage_R3` PROVED as theorem, issue #4 PR-6, 2026-07-05, `LimitPassage.lean`; was 1 — `galerkin_spacetime_precompact_R3` DISCHARGED axiom → theorem, issue #46 PR-4; `r3ConvectionGapOp_exists` PROVED, issue #56, PR #60); ℝ³ spatial+regularity layer built axiom-free; `#print axioms` = kernel-only |
| Wave-0 | **Infra unblocker** — flock build-lock, Skill grant, `Core.lean` split, `_axiomatic` naming, CI axiom-leak gate | **DONE** — 5 items complete; GelfandTriple signature fix (item 1) deferred to Stream D (issue #4); tsum safe APIs (item 5) and componentwise extraction (item 6) deferred to hygiene pass |
| R3-d | **Concrete trilinear convection estimate** (`LerayHopf/R3/TrilinearEstimate.lean`) — upgrades the former `r3ConvectionGapOp_exists` axiom's *justification prose* into 11 proved, axiom-free lemmas about `convIntegralSchwartz` | **DONE** (axiom-free) — multilinearity (6), integrability, direct H¹ bound, **IBP identity**, **antisymmetry under div-free**, and the genuine **`b_bound` shape** `\|b(u,v,w)\| ≤ C(w)·‖u‖₂·‖v‖₂`; each `#print axioms`-clean (only propext/Classical.choice/Quot.sound). This did not by itself remove the axiom at that time; issue #56 later removed it via the determined-form construction. |
| P5 | **Galerkin scheme constructive content** (`LerayHopf/R3/GalerkinScheme.lean`) — substantiates the former `r3GalerkinScheme_exists` axiom by *constructing* the scheme from a Schwartz div-free basis | **DONE** (axiom-free) — `nonempty_r3GalerkinScheme_of_basis (B : SchwartzGalerkinBasis) : Nonempty R3GalerkinScheme` builds all six structure fields from orthogonal projections (`Submodule.starProjection`) onto finite prefix-spans of `B`; the one classical input (density of smooth div-free fields in L²_σ, a Helmholtz/Weyl fact) is the bundled hypothesis `B.dense_span`, not an axiom. `#print axioms`-clean. **Soundness fix (Codex-confirmed):** `R3GalerkinScheme.tendsto_id` weakened from `∀ u : L2VF_R3` to the honest `∀ u ∈ L2Sigma_R3` (a div-free Galerkin scheme is total only in Σ; the unrestricted form was a latent over-strength never consumed by the closure). This row predates the issue #21 curl-density discharge; current capstone status is the top banner above. |
| P3 | **LOCAL Rellich–Kondrachov on ℝ³** (`LerayHopf/R3/SpatialCompactness.lean`) — substantiates the `spatial_compactness_R3` axiom by proving the full reduction axiom-free from one isolated frontier hypothesis | **DONE** (axiom-free) — `localCompactness_R3_of_ballCompact (B : LocalRellichInput)` reproduces the **byte-identical** `spatial_compactness_R3` conclusion (per-ball L² subsequence convergence of any L²∩H¹-bounded div-free sequence, limit in `L2Sigma_R3`). The reduction is fully proved: per-ball extraction (`IsCompact.tendsto_subseq`), countable diagonal over expanding balls, global glue `g₀ x := g(⌈dist x 0⌉)x` with `MemLp` via ball-exhaustion, div-free closure via the **G5 ε/3 ball-truncation** (`divTestFunctional φ g = lim = 0`: ball part by local convergence + Cauchy–Schwarz tail uniform in `n` via `‖z n‖≤M` + Schwartz/L²-tail→0). The ONE classical input — local compact embedding `H¹(B_R)↪↪L²(B_R)` (mathlib lacks Rellich) — is the bundled hypothesis `LocalRellichInput.ballCompact` (Codex-confirmed non-smuggling), not an axiom. `#print axioms`-clean. `exists_lerayHopf_r3` unaffected. Does NOT remove the axiom (unconditional local compactness still needs the embedding) |
| P2 | **Aubin–Lions time-compactness + limit passage** (`LerayHopf/R3/AubinLionsLimitPassage.lean`) — substantiates the *reusable analytic core* of the `aubin_lions_R3` / `galerkin_limit_passage_R3` axioms | **PARTIAL** (honest) — **PROVED axiom-free** (`#print axioms`-clean, no sorryAx): `spatialInput_R3_of_localRellich` (the `aubin_lions_R3` spatial half, by reusing P3), `bForm_tendsto_of_strongL2` (nonlinear convection b-term passes to the limit under strong L², the R3-d `b_bound` payoff), and the Steklov interval-averaging building blocks (`steklovAvg`, its uniform L² bound, the time-modulus approximation). **OPEN** (`sorry` + truthful TODO, NOT smuggled, no new axioms): `kineticEnergy_lsc_bound` (E1) — statement CORRECTED at the Codex statement gate from the original `∀ t` pointwise form (smuggling — claimed pointwise-time representative control the package lacks) to the honest **a.e.-in-time** form, and still OPEN because `AubinLionsPackage_R3` carries no time-measurability for its limit; `aubinLionsPackage_R3_of_timeCompactness` (C2, the full Aubin–Lions assembly) — viable via the Steklov route (Codex-confirmed NOT unsound) but the δ-mesh diagonalization + H¹/Jensen-on-average + Bochner-average measurability + boundary-strip handling remain an open engineering target (mathlib lacks `W^{1,p}(0,T;X)` / Simon's lemma). Isolated time-frontier hypothesis: `TimeCompactnessInput`. Current capstone status is the 2-axiom banner above. |
| ODE | **Galerkin ODE energy/regularity algebra** (`LerayHopf/R3/GalerkinODE.lean`) — substantiates the energy-side content of the former `galerkin_ode_solution_R3` axiom + a **core soundness fix** | **DONE (axiom-free) + core fix.** `galerkinSolutionData_R3_of_input (I : GalerkinODEInput)` produces the full `GalerkinSolutionData_R3` from an isolated existence hypothesis: `GalerkinODEInput` carries the 5 solution-defining fields (`u, u_initial, u_inVn, u_hasDeriv, u_ode`); the 3 derived fields are **proved axiom-free** — `galerkin_energy_identity` (E1: `d/dt ½‖u‖² = −viscousFormSq_R3 ν` via `HasDerivAt.inner`, convection killed by `b_self_zero`), `galerkin_energy_bound` (E2: antitone energy), `galerkin_reg_bound` (E3: FTC ⇒ `∫₀ᵀ viscousFormSq_R3 ν ≤ ½‖u₀‖²`), `galerkinCurve_reg_mem` (M0: Schwartz-range ⇒ `MemSobolev 1 2`). Isolated frontier (mathlib gap): global ODE existence (only local Picard–Lindelöf) + weak-form↔vector-field representation. **SOUNDNESS FIX (Codex-gated):** `GalerkinSolutionData_R3.reg_bound` RHS corrected from the ν-mis-scaled `T‖u₀‖²+‖u₀‖²/(2ν)` (not energy-derivable, false for large ν/moderate T) to the energy-derivable `½‖u₀‖²`; the T³ analogue was verified CORRECT-as-is (different `h1EnergySq` integrand) and left intact. `#print axioms`-clean; current capstone status is the top banner above. |
| D | **Schwartz divergence-free basis** (`LerayHopf/R3/SchwartzDivFreeBasis.lean`) — thins P5's `SchwartzGalerkinBasis` frontier from the bundled `dense_span` to a single density Prop | **DONE (axiom-free)** — `schwartzGalerkinBasis_of_curlDense (h : CurlSchwartzDense) : Nonempty SchwartzGalerkinBasis`, `#print axioms`-clean. The hard content is PROVED: `curlSchwartz` (curl of Schwartz potentials, cyclic `lineDerivOpCLM`) is genuinely Schwartz (A3) and weakly divergence-free (A4, `div(curl)=0` via IBP + Clairaut mixed-partial symmetry), plus separability/countable-dense enumeration (B2). The residual frontier is the lone Prop `CurlSchwartzDense` (curls of Schwartz potentials are dense in `L²_σ`), exposed as the marked `sorry` in `nonempty_schwartzGalerkinBasis` (NOT an axiom; the Leray-projection route was rejected as smuggling non-Schwartz). `exists_lerayHopf_r3` unaffected |
| E | **Galerkin ODE existence (Riesz vector field)** (`LerayHopf/R3/GalerkinODEExistence.lean`) — thins the ODE frontier from "existence + representation" to "global existence only" | **DONE (axiom-free)** — `galerkinODEInput_of_basis (… G : FinDimGlobalODE …) : GalerkinODEInput (schemeOfBasis B) …`, `#print axioms`-clean. The weak-form↔vector-field **representation is PROVED**: the finite-dim Riesz vector field `galerkinODE_vectorField` (R1, via `InnerProductSpace.toDual`) + its spec (R2), resting on a genuinely-proved right-linearity/`‖ξ‖²`-weighted-integrability of `stokesTestPairing_R3` on Galerkin-span elements; `u_ode` is then DERIVED (R3). Worked over the CONCRETE `schemeOfBasis B` (abstract `R3GalerkinScheme` doesn't expose finite-dimensionality of `range(𝔊.P n)`). Residual frontier: `FinDimGlobalODE` = finite-dim global ODE existence (mathlib has only local Picard–Lindelöf), an isolated hypothesis (not a sorry/axiom). `exists_lerayHopf_r3` unaffected |
| FourierL2 | **Lp Fourier-modulation foundation** (`LerayHopf/R3/FourierL2.lean`) — shared L² Fourier toolkit | **DONE (axiom-free).** Fully proves F1–F9: the bounded unit phase-multiplier `phaseMulCLM` on L²C, the **Lp-level Fourier modulation identity** `𝓕(τ_{+h} f) = e^{2πi⟨h,·⟩}·𝓕 f` (`fourier_translate_eq`, F5 — via `VectorFourier.fourierIntegral_comp_add_right` lifted by density induction; this was the feared "deep wall"), Plancherel weight bookkeeping, and `‖phase−1‖² ≤ (2π)²‖h‖²‖ξ‖²` (F9). `#print axioms`-clean. Reusable by B's T0b (and a future D Fourier route) |
| B | **LOCAL Rellich via Fréchet–Kolmogorov** (`LerayHopf/R3/RellichBall.lean`) — thins P3's `LocalRellichInput` toward the standard FK criterion | **PARTIAL** (honest, improved) — `localRellichInput_of_frechetKolmogorov (FK : FrechetKolmogorovInput) : LocalRellichInput` fully assembled; T0a/T0c/T1b/T2 axiom-free; **T0b `normSq_translate_sub_le_viscousFormSq` now PROVED** via the FourierL2 foundation (the Lp-modulation wall is gone). **OPEN** (sole remaining `sorry`, strictly thinner): `integrable_viscous_integrand_of_memH1` — `memH1VF_R3 w ⇒` the `(2π)²‖ξ‖²‖𝓕w‖²` integrand is integrable; a distribution-theory faithfulness fact (mathlib's `smulLeftCLM` a.e.-characterization only covers bounded multipliers). Isolated hypothesis still: `FrechetKolmogorovInput`. `exists_lerayHopf_r3` unaffected |
| core-fwd | **Forward-time soundness fix** (`SolutionInterfaces.lean` + `GalerkinODE`/`GalerkinODEExistence`/`AubinLionsLimitPassage`) | **DONE (Codex-gated).** 3rd latent over-strength corrected: `GalerkinSolutionData_R3.u_hasDeriv`/`u_ode` (core axiom struct), `GalerkinODEInput`, and `FinDimGlobalODE` restricted from `∀ t : ℝ` to `∀ t, 0 ≤ t →` (physical Galerkin solutions are forward-only; the quadratic field can blow up in finite backward time, so all-`t` was stronger than constructible). Consumers fixed: E1 (added `0≤t`), E2 reproved `AntitoneOn (Ici 0)` (same conclusion), E3, R3, and `galerkin_curve_continuous` → `ContinuousOn (Ici 0)`. `exists_lerayHopf_r3` unchanged (6 project + 3 kernel, no sorryAx); T³ analogue verified not-affected and left intact |
| Track 3 | **Finite-dim Galerkin ODE global existence** (`LerayHopf/R3/GalerkinODESolve.lean`) — discharges the `FinDimGlobalODE` frontier (forward-time) | **DONE (axiom-free).** `finDimGlobalODE_exists … : Nonempty (FinDimGlobalODE B F ν u₀ n)` UNCONDITIONAL, `#print axioms`-clean. The `(u·∇)`-quadratic field `G_n` is `C¹` on the finite-dim `V_n` (Riesz-built bilinear+linear parts); A1 `⟪v,G_n v⟫≤0`; A2 energy identity; A3 forward a-priori `‖c t‖≤‖c 0‖`; **G1 forward-global by tiling** (uniform local-existence time on the a-priori ball via Picard–Lindelöf + Grönwall uniqueness, re-derived locally since `ODE.ExistUnique` sits above the import set). Wired into the default build. With a concrete scheme (Stream A capstone) + concrete `F` (Stream C) this feeds the removal of `galerkin_ode_solution_R3`. `exists_lerayHopf_r3` unchanged |
| 4-stream scaffold | **Statement layer for the four parallel pillars** (`CurlDensity`, `FrechetKolmogorov`, `ConvectionOperator`+`ConvectionForm`, `Bochner/{GelfandTriple,TimeSobolev}`) — sound, Codex-gate-APPROVED statements; proofs scaffolded | **STATEMENTS DONE (gate-approved), proofs OPEN (debt, NOT a removal yet).** Six new files, all in default build, `#print axioms exists_lerayHopf_r3` unchanged (6 project + 3 kernel, 0 sorryAx). Survived a 4-round adversarial statement gate that caught and fixed: A's circular curl-symbol; B's wrong-norm mollifier bounds (→ upstream-strengthened `FrechetKolmogorovInput` with an honest global-L²-bound field, satisfiable from the family's `‖w‖≤M`); C's `ConvectionGap` over-correction (round-3 `b_cont` on L²³ was FALSE since the form is unbounded there → corrected to mixed-honesty `b_multilinear`/`b_antisymm_gap` asserted residual + `b_cont_fixedTest`); D's bare/over-strong Gelfand bridge and H-valued (→ V′-valued) time derivative + non-Bochner `mem_p`. **Deliverables (each a real discharge target or honest isolation):** A `curlSchwartzDense_holds : CurlSchwartzDense` (discharge → removes `r3GalerkinScheme_exists`); B `frechetKolmogorov_holds : FrechetKolmogorovInput` + `memH1_weightedL2_integrable` (discharge → removes `spatial_compactness_R3`); C Tier-S `convFormSchwartz_*` (PROVED-shape) + `R3NSForms_of_gap` (conditional on `ConvectionGap`); D `aeStronglyMeasurable_of_spaceTimeL2` (feeds P2's E1) + Gelfand/time-Sobolev spine. **Proving outcome this session (partial):** B — `integrable_viscous_integrand_of_memH1` PROVED ⇒ **`RellichBall.lean` now sorry-free**, `localRellichInput_of_frechetKolmogorov` axiom-clean (no sorryAx); `memH1_weightedL2_integrable` PROVED. A — structural/linear-algebra core proved (`cross_iξ_spans_transverse` + `schwartzC`/`potentialComponentC`/Fourier-helper lemmas). **Precise remaining walls (named missing-mathlib sub-developments, NOT tactic fills):** B's `frechetKolmogorov_holds` needs the FK mollification chain = an L²-translation-continuity lemma (`‖τ_h η−η‖₂→0` via DCT), a convolution-difference Cauchy–Schwarz bridge, and a vector-valued Young sup-bound (none in pinned mathlib); A's `curlSchwartzDense_holds` needs `fourier_curlSchwartz_eq_cross` (curl Fourier multiplier), `mem_sigma_iff_fourier_transverse` (spectral div-free char), and `l2sigma_le_closure_span_curl` (the Helmholtz/Weyl density core). **No axiom removed this batch** — debt reduced (RellichBall discharged, ~7 sorries closed), the two removals remain gated on the named sub-libraries |
| FK-sublib + Fourier (goal a+b) | **Stream B FK mollification sub-library + Stream A Fourier lemmas** (`FrechetKolmogorov.lean`, `CurlDensity.lean`) — drive the two axiom-removal streams toward discharge | **MAJOR PROOF PROGRESS, axioms still gated on 2 genuine missing-mathlib walls.** (a) Stream B: **all 3 mollifier helpers PROVED** (`kernel_translate_L2_tendsto` via DCT, `mollifyRep_sup_le` + `mollifyRep_sub_le` via kernel-reach localization + L² Cauchy–Schwarz); `mollified_family_uniformly_bounded`/`_equicontinuous` PROVED (derive from helpers); **`mollified_family_totallyBounded_L2` PROVED** (direct Arzelà–Ascoli ε-net + sup→L²(B_R) transfer); `convolution_l2_tendsto_uniform` **restructured** to derive from a real `ContDiffBump.normed` kernel constructor (`exists_normalized_mollifierKernel`, no sorry) + `MollifierKernel` now carries `mass_one`/`nonneg`/`even` + two precisely-named analytic frontier lemmas. **Remaining FK frontier (genuine missing-mathlib, isolated):** `young_convolution_memLp_L2` (global Young `L¹×L²→L²`) and `convolution_sub_L2_le_translation_modulus` (Lp-valued Bochner Minkowski integral inequality — a 3.5h prover grind confirmed its depth), then `frechetKolmogorov_holds` assembly. (b) Stream A: **`fourier_curlSchwartz_eq_cross` PROVED** (curl Fourier multiplier); **`mem_sigma_iff_fourier_transverse` REVERSE PROVED** + `fourier_schwartzC_hermitian` (Fourier-of-real ⇒ conjugate-symmetric) + `testSymbol_antiHermitian` + `mem_sigma_of_transverse_ae` PROVED. **Remaining A frontier:** `mem_sigma` forward (needs Fourier surjectivity onto Hermitian Schwartz + even/odd density) and `l2sigma_le_closure_span_curl` (Helmholtz/Weyl density core). `exists_lerayHopf_r3` pin unchanged (6 project + 3 kernel, 0 sorryAx) throughout |
| Stream A (curl density, issue #3) | **(P1) Lp Hermitian-reflection PROVED + frontier collapse to a single named fact** (`LerayHopf/R3/CurlDensity.lean`) — drives Stream A's `mem_sigma_iff_fourier_transverse` forward toward discharge | **P1 DISCHARGED (axiom-free, no sorry) + frontier collapsed from 2 walls to 1.** Proved `fourier_ofReal_reflect_eq_conj` (+ base case `reflect_fourier_schwartzC_eq_conj`): the **Lp-level Hermitian reflection identity** `(𝓕(ofReal∘a))(-ξ) =ᵐ conj((𝓕(ofReal∘a))ξ)`, via `DenseRange.induction_on` over real Schwartz (mirroring `FourierL2.fourier_translate_eq`) with base case the proved `fourier_schwartzC_hermitian`; honest `Lp` operations `Lp.compMeasurePreserving Neg.neg` (reflection) + `Complex.conjCLE.compLpL` (conjugation). This was one of the two named blockers of the forward `mem_sigma_iff_fourier_transverse`. **Corrected a stale assessment:** pinned mathlib DOES have the L²-Fourier toolkit the earlier doc said it lacked — `Lp.fourierTransformₗᵢ` (LinearIsometryEquiv) + `Lp.inner_fourier_eq` (Parseval), `Submodule.orthogonal_orthogonal_eq_closure` (orthogonal-complement density), `ae_eq_zero_of_integral_contDiff_smul_eq_zero` (du-Bois-Reymond), `Measure.measurePreserving_neg`. So `l2sigma_le_closure_span_curl` is NOT independently months-class: it reduces (via the orthogonal-complement route) to the forward `mem_sigma_iff_fourier_transverse`, which now bottoms out on the **single** remaining frontier **(P2)**: Schwartz surjectivity of `φ ↦ testSymbol φ` onto anti-Hermitian symbols = `𝓕⁻` of a Hermitian Schwartz function is a *real* Schwartz complexification (Schwartz-space real-part extraction under Hermitian symmetry). NOT in mathlib; **weeks-class** constructible (`SchwartzMap.postcompCLM Complex.conjCLE` + real-valuedness + `Complex.reCLM`), not months. Net: the two CurlDensity `sorry`s now both name exactly (P2). No axiom removed (full `r3GalerkinScheme_exists` removal still gated on P2); no new axiom/opaque. `exists_lerayHopf_r3` pin unchanged (6 project + 3 kernel, 0 sorryAx) |
| Stream B / capstone C2 (`spatial_compactness_R3` removal, issue #2 / #9) | **AXIOM REMOVED — `spatial_compactness_R3` is now a proved theorem** (`LerayHopf/R3/SolutionInterfaces.lean` + the FK chain) | **DONE (PR #35) — FIRST capstone axiom removal, 6→5.** `spatial_compactness_R3` rewritten from `axiom` to `theorem`, defined as `localCompactness_R3_of_ballCompact (localRellichInput_of_frechetKolmogorov frechetKolmogorov_holds)` — the sorry-free Fréchet–Kolmogorov chain wired into the capstone. `#print axioms exists_lerayHopf_r3` = **5** project axioms (`aubin_lions_R3`, `galerkin_limit_passage_R3`, `galerkin_ode_solution_R3`, `r3GalerkinScheme_exists`, `r3_NSForms_exist`) + 3 kernel (`propext`, `Classical.choice`, `Quot.sound`); no `sorryAx`. Supporting: T0b `integrable_viscous_integrand_of_memH1` (`RellichBall.lean`) is now FULLY PROVED (was the sole marked `sorry`) ⇒ `RellichBall.lean` is sorry-free; the FK chain (`frechetKolmogorov_holds`, `localRellichInput_of_frechetKolmogorov`, `localCompactness_R3_of_ballCompact`) carries no `sorryAx` |
| Stream D follow-up (Bochner-time discharges, issue #13-B) | **`isWeakTimeDeriv_unique` + `W1pTime.ofHValuedDeriv` PROVED sorry-free** (`LerayHopf/Bochner/TimeSobolev.lean`) — supersedes the "Months-class residuals" note in the prior Stream D row | **DONE (axiom-free, this cycle).** `isWeakTimeDeriv_unique` (a.e. uniqueness of the weak time derivative, via du-Bois-Reymond for Bochner integrals) and `W1pTime.ofHValuedDeriv` (the H-valued weak-time-derivative specialization, under the `1 ≤ p` domain guards) are both now PROVED sorry-free; `#print axioms`-clean. The one remaining `TimeSobolev.lean` `sorry` is the SEPARATE D1 Lions–Magenes good-representative embedding `w1pTime_continuous_in_H` (declared months-class) — **relocated to `TimeSobolevExperimental.lean` by issue #147**; `TimeSobolev.lean` itself is now sorry-free (see the residual-sorry list below). `exists_lerayHopf_r3` pin unchanged |
| Stream D (Bochner-time, issue #4) | **GelfandTriple interface fix + Bochner-time D1/D2** (`LerayHopf/Bochner/{GelfandTriple,TimeSobolev}.lean`) — the prerequisite Wave-0 item 1 signature fix plus reachable D1/D2 lemmas; statement-gate fix of the D2 primitives | **PREREQUISITE DONE + 3 lemmas PROVED + statement-gate defect found and fixed.** (1) **GelfandTriple signature fix (Wave-0 item 1 / issue #1) DONE** — `ofDissipativeEvolution` rewritten to take an abstract Hilbert `V` with the embedding as a genuine `ι : V →L[ℝ] E.H` (CLM), so `ι_linear`/`ι_continuous` are the CLM's own `isLinear`/`continuous` and the regularity subspace `Vsub` is the *derived* `LinearMap.range ι`; **removes the 2 former `ALLOW_SORRY`** by fixing the interface, not proving around it (no caller existed — clean change). (2) **`hasDerivAt_isWeakTimeDeriv` PROVED sorry-free** — strong⇒weak time derivative via Bochner IBP (`integral_smul_deriv_eq_deriv_smul_of_hasDerivAt`, boundary terms killed by `tsupport ψ ⊆ Ioo 0 T`). (3) **STATEMENT-GATE DEFECT found AND fixed:** both D2 "KEY primitives" `aeStronglyMeasurable_of_spaceTimeL2` and `kineticEnergy_lsc_transfer` were **FALSE as originally stated** — missing a hypothesis pinning the limit `g` measurably (explicit Vitali-set counterexample: `eLpNorm g = 0` does NOT force `g =ᵐ 0` without measurability of `g`, and every `tendstoInMeasure_of_tendsto_eLpNorm*` mathlib lemma *requires* measurability of the limit as input — a `MemLp (f n)` fix does NOT suffice since `f n = 0` satisfies it). **Fix (orchestrator-authorized in-file signature change):** added the isolated no-smuggle hypothesis `hg : AEStronglyMeasurable g μ`, making both statements TRUE; **both then PROVED sorry-free** (`tendstoInMeasure_of_tendsto_eLpNorm` → `exists_seq_tendsto_ae` → `le_of_tendsto'`). Honest: this isolates, not removes, E1's genuine blocker — `g`'s time-measurability is now an explicit input E1 must still supply. **Months-class residuals unchanged** (honest sorry + TODO, no axiom): `w1pTime_continuous_in_H` (Lions–Magenes embedding), `isWeakTimeDeriv_unique`, `W1pTime.ofHValuedDeriv`, P2's E1/C2. No `aubin_lions_R3`/`galerkin_limit_passage_R3` removed; no new axiom/opaque. `exists_lerayHopf_r3` pin unchanged |

## M2 design decisions (orchestrator, adopted)

- **0-A velocity codomain:** `VelocityValue := EuclideanSpace ℝ (Fin 3)` (physically faithful
  ℝ³ energy inner product). Fourier work uses component-wise ℝ↪ℂ embedding, made explicit.
- **0-B measure normalization:** probability/Haar (total mass 1), consistent with `mFourierBasis`
  (`AddCircleMulti` uses `haarAddCircle`). The `volume` vs `haarAddCircle` definitional match at
  `T = 1` is a known M2 friction point (planner D-06); to be verified by lean-coder.

## Axiom ledger

**Posture shift (M6):** T³ is the warm-up scaffold, not the destination (R³ is). Per the
approved plan `ssot-reference-list-cuddly-meteor.md`, the remaining T³ analytic frontier is
decomposed into **four minimal, true, literature-referenced axioms** that close the T³
existence theorem, with the framework built abstractly for R³ reuse. The **spatial** Rellich
compactness is *not* axiomatized — it is the proved `rellich_seq_compact`/`rellich_L2Sigma`,
discharged into the Aubin–Lions axiom as an explicit hypothesis. Every axiom passed a Codex
`--effort xhigh` soundness audit (8 rounds; see the Codex log).

**No live T³ project axioms remain.**  All four former T³ axioms are now proved theorem content
(`galerkin_ode_solution` — issue #24; `torusConvectionGap_exists` — issue #53 / PR #62;
`galerkin_limit_passage` — issue #25 / PR #75; `aubin_lions` — issue #23, T-AL-6 Stage C).

| Axiom | Status |
|---|---|
| ~~`aubin_lions`~~ | **REMOVED (issue #23, T-AL-6 Stage C, 2026-07-04)** — proved as `torusAubinLionsPackage_of_galSeq` (`LerayHopf/TorusAubinLionsAssembly.lean`) via the mode-wise spectral route (equi-Lipschitz test pairings + scalar Bolzano–Weierstrass diagonal + Riesz + H¹ tail); spatial half discharged by `rellich_L2Sigma`; `#print axioms` clean. T³ frontier 1 → 0. |
| ~~`galerkin_limit_passage`~~ | **REMOVED (#25 / PR #75)** — proved via `torus_galerkin_limit_passage_of_energyClass` + `torus_energyClass_of_aubinLions`; T³ frontier 2 → 1. |
| ~~`torusConvectionGap_exists`~~ | **PROVED (#53 / PR #62)** as `torusConvectionGap_holds` (determined-form torus construction). |
| ~~`galerkin_ode_solution`~~ | **PROVED (#24)** via the axiom-free `galerkinSolutionData_torus`. |

`b(u,u,u)=0` is a **proved lemma** (`Torus3NSForms.b_self_zero`) from antisymmetry, NOT an axiom.
`#print axioms exists_lerayHopf_torus3` → `[propext, Classical.choice, Quot.sound]`
only — **zero project axioms, no `sorryAx`**.
Renamed from `exists_lerayHopf_torus3` in Wave-0 (Issue #1 item 3).

### ℝ³ (whole-space) — 0 project axioms — KERNEL-ONLY (`LerayHopf/R3/GalerkinODECapstone.lean`)

(Was 6; `spatial_compactness_R3` removed in PR #35 / issue #2 — now a proved theorem, see
the row marked **REMOVED** below.)

The ℝ³ spatial+regularity layer is **built axiom-free** (`R3/Domain.lean`, `DivergenceFree.lean`,
`Regularity.lean`): `L2Sigma_R3 := ⨅ φ:𝓢, ker(divTestFunctional φ)` (weak divergence against Schwartz
tests; closed div-free subspace), `memH1VF_R3` (via `MemSobolev`),
`stokesTestPairing_R3`/`viscousFormSq_R3` (via the L² Fourier transform `Lp.fourierTransformₗᵢ`),
`convIntegralSchwartz` (the genuine convection integral on Schwartz fields). The abstract
`DissipativeEvolution`/`WeakFormNS`/`AbstractEnergyLaw` layer is **reused unmodified**.

| Axiom | Role | T³ analogue | Why ℝ³ needs it |
|---|---|---|---|
| ~~`galerkin_limit_passage_R3`~~ | **PROVED (issue #4 PR-6, 2026-07-05)** in `LimitPassage.lean` — existential good representative + weak form + energy-ineq + trace + energy-class | T³ `galerkin_limit_passage` | Temam III.3; local convergence + Schwartz-test decay |

Removed from axiom set (now proved theorems):
- ~~`galerkin_spacetime_precompact_R3`~~ **REMOVED (#46 PR-4, 2026-07-04)** — axiom → theorem
  in `ArzelaAscoliTime.lean`, delegating to `galerkin_spacetime_precompact_of_goodSampling`
  (File E, `LerayHopf/R3/SpacetimePrecompact.lean`): the LOCAL Aubin–Lions–Simon spacetime
  precompactness assembled sorry-free from the step-curve total-boundedness engine
  (n-uniform integrated sampling modulus + Rellich ball-compactness); R3 frontier 2 → 1
- ~~`r3GalerkinScheme_exists`~~ **REMOVED (#21)** — curl-density + Schwartz Galerkin basis (CurlDensity.lean / issue #3)
- ~~`spatial_compactness_R3`~~ **REMOVED (#2/PR #35)** — Fréchet–Kolmogorov chain
- ~~`galerkin_ode_solution_R3`~~ **REMOVED (#10)** — finite-dim ODE solver
- ~~`aubin_lions_R3`~~ **REMOVED (#15)** → split → `galerkinSpaceTimeExtraction_R3` → **PROVED (#44)**
- ~~`galerkin_weakLimit_R3`~~ **REMOVED (#47)** — strong ball-exhaustion + Mazur weak-closedness
- ~~`r3ConvectionGapOp_exists`~~ **REMOVED (#56/PR #60)** — proved sorry-free as `r3ConvectionGapOp_holds` via determined-form BLT construction (`ConvectionExtension.lean`, C11)

`R3NSForms.b_self_zero` is a proved lemma. `#print axioms exists_lerayHopf_r3` →
**0 project axioms** + `propext`/`Classical.choice`/`Quot.sound` (no `sorryAx`) — **KERNEL-ONLY**.
(Was 6; successive removals: `spatial_compactness_R3` #2, `galerkin_ode_solution_R3` #10,
`r3GalerkinScheme_exists` #21, `aubin_lions_R3`→time-extraction proved #15/#44,
`galerkin_weakLimit_R3` #47, `r3ConvectionGapOp_exists` #56,
`galerkin_spacetime_precompact_R3` #46 PR-4, `galerkin_limit_passage_R3` #4 PR-6.)
Renamed from `exists_lerayHopf_r3` in Wave-0 (Issue #1 item 3).

**Earlier (M2) axiom eliminated:** the M2 plan tentatively proposed `L2Sigma_eq_divFreeL2`
(closure-of-span ↔ Fourier-diagonal). **Eliminated**: `L²_σ` is defined *directly* as
`⨅ k, ker (divSymbol k)`, so membership coincides with `DivFreeL2` by construction (no axiom),
and `L²_σ` is a closed submodule giving its Hilbert structure + Leray projection for free.

## Sorry frontier

**In the Lean tree:** the headline existence theorems (`exists_lerayHopf_torus3`,
`exists_lerayHopf_r3`) and the R3-d/P5/P3 deliverables are sorry-free and
`#print axioms`-clean.  (Renamed from bare `exists_lerayHopf_torus3`/`exists_lerayHopf_r3` in
Wave-0; Issue #1 item 3.)
**`kineticEnergy_lsc_bound` (E1) and `aubinLionsPackage_R3_of_timeCompactness` (C2) are PROVED
sorry-free** as of issue #31 and issue #15 respectively.  `AubinLionsLimitPassage.lean` carries
zero `sorry` lines.  Their former open status is historical.

**(issue #144, 2026-07-17):** the former scaffold target `Statement.lean:
exists_lerayHopf_torus3_statement` — together with the underlying placeholder
`LerayHopfSolution`/`ExistsLerayHopf` in `Torus/Basic.lean` — has been **deleted**; it was a
permanent `ALLOW_SORRY` on a structurally-vacuous `Prop`-field record that risked being
mistaken for the real capstones. `LerayHopf/NonuniquenessStatement.lean` (`LerayHopfNonunique`,
also built on the placeholder `LerayHopfSolution`) was deleted alongside it.

Actual residual marked `sorry` (6 total, all outside both capstone cones, all Lions–Magenes-class
Bochner-time walls):
- `LerayHopf/Bochner/TimeSobolevExperimental.lean:57` — D1 Lions–Magenes good-representative
  embedding (`w1pTime_continuous_in_H`); declared months-class residual. Extracted from
  `TimeSobolev.lean` by issue #147 (see below).
- `LerayHopf/Bochner/TimeSobolevAC.lean:322` — Bochner–Fubini distributional FTC for the
  interval primitive `w(t)=∫₀ᵗ v`; isolated single residual of R1.
- `LerayHopf/Bochner/TimeMollification.lean:196` — S1 time-mollification with linked
  L²(V)/L²(V') convergence; interval Steklov assembly wall.
- `LerayHopf/Bochner/TimeMollifierInterval.lean:297` — Fubini side-condition (compact-box L¹
  bound); not soundness-critical; the mathematical commutation identity is proved unconditionally.
- `LerayHopf/Bochner/TimeMollifierInterval.lean:466` — B1 even-reflection no-Dirac identity;
  blocked on Bochner 1D-Sobolev FTC/trace pillar.
- `LerayHopf/Bochner/TimeMollifierInterval.lean:601` — B assembly; transitively blocked on B1.

**Both capstones are unaffected by all residual sorries** — the kernel-only `#print axioms` pin
(`[propext, Classical.choice, Quot.sound]`, no `sorryAx`) is the authoritative justification,
not import-level reachability.

**(issue #147):** all 6 residuals above are now also outside the **release import cone**, not
just outside the capstone cones. `import LerayHopf` (root) transitively imports none of them;
they are reachable only via the explicit opt-in `import LerayHopf.Experimental`.
`w1pTime_continuous_in_H` was extracted out of `TimeSobolev.lean` into a new
`TimeSobolevExperimental.lean` (nothing else depends on it — `TraceEnergy.lean` already
documented it as quarantined — so `TimeSobolev.lean` itself is now sorry-free and stays in the
release cone, still imported directly by `R3/AubinLionsLimitPassage.lean` and
`R3/EnergyWeakLsc.lean` for the unrelated, sorry-free `kineticEnergy_lsc_transfer`).
`scripts/check-release-cone.sh` enforces this statically in CI: it fails if the transitive
import closure of `LerayHopf.lean` ever contains a `sorry`, marked or unmarked.

**Former analytic frontier (HISTORICAL — both capstones now UNCONDITIONAL, 2026-07-05).**
These were the items that required structural mathlib sub-libraries to close the existence
theorems; all are now resolved.  Retained as a record.

| Frontier item | Precise content | Resolution |
|---|---|---|
| ~~Concrete NS convection `b(u,v,w)`~~ | `∫_{𝕋³} ((u·∇)v)·w` on `L²/H¹` torus fields | **DONE** — `torusConvectionGap_holds` (issue #53/PR #62) |
| ~~Nonlinear cancellation `b(u,u,u)=0`~~ | skew-symmetry for divergence-free `u` | **DONE** — proved lemma `Torus3NSForms.b_self_zero` |
| ~~Galerkin ODE existence~~ | `uₙ` solving the projected ODE via `PicardLindelof` | **DONE** — `galerkinSolutionData_torus` (issue #24) + `finDimGlobalODE_exists` (track 3) |
| ~~Rellich on T³~~ | `H¹(𝕋³)`-ball totally bounded in `L²(𝕋³)` (`H1_ball_totallyBounded`) | **DONE** — proved axiom-free (M5) |
| ~~Aubin–Lions (full, time)~~ | time-equicontinuity + Rellich ⟹ strong `L²(0,T;L²)` | **DONE** — `torusAubinLionsPackage_of_galSeq` (issue #23, T-AL-6) |
| ~~Limit passage~~ | weak-* + strong-L² limits ⟹ weak solution | **DONE** — `galerkin_limit_passage_R3` proved (issue #4 PR-6); T³ `torus_galerkin_limit_passage_of_energyClass` (issue #25) |

The **abstract energy law ⟹ energy inequality ⟹ nonincreasing energy** chain is fully proved
(`AbstractEnergyLaw`); only the *concrete construction supplying* such a law is frontier.

## Known scaffold caveats (disclosed, not hidden)

These are deliberate properties of the M1 scaffold, recorded so they are never mistaken
for proved mathematics. Each is discharged by the monotone refinement of placeholders.

- ~~**`ExistsLerayHopf` is vacuous at M1.**~~ **RESOLVED by deletion (issue #144, 2026-07-17).**
  The M1-era placeholder `LerayHopfSolution` (free `Prop` fields, `Torus/Basic.lean`) and the
  vacuous `ExistsLerayHopf`/`Scaffold.exists_lerayHopf_torus3_statement` it fed (`Statement.lean`)
  were **deleted outright** rather than further refined, once the real capstones
  (`exists_lerayHopf_torus3`, `exists_lerayHopf_r3`, both proof-carrying and kernel-only) made
  the M1 scaffold's structural role obsolete and its name/namespace collision with the
  production `Galerkin.LerayHopfSolution` a release-blocking overclaim risk. This caveat no
  longer applies — there is no vacuous `ExistsLerayHopf` left in the public API to misread.
  (Partial history: `exists_lerayHopf_from_galerkin_package` and its host file
  `GalerkinPackage.lean` were already deleted in issue #112 PR-D, 2026-07-11; the generic
  package/existence layer lives on in `LerayHopf/Galerkin/Domain.lean` +
  `LerayHopf/Galerkin/SolutionBundles.lean` as `Galerkin.CompactnessPackage` /
  `Galerkin.exists_lerayHopf_from_package`, consumed by both capstones via the lanes'
  `…Full` abbrevs — unaffected by this deletion.)
- **`Torus3` is a fresh placeholder with the zero measure**, not the real torus. The zero
  measure is intentionally wrong-but-honest (signals "unrealized"). _Discharge:_ M2 realizes
  `Torus3 := UnitAddTorus 3` with Haar/volume measure.

## Codex adversarial-review log

- **M1 spine** (`/codex:adversarial-review --effort xhigh`, working tree): verdict
  *needs-attention*, 3 findings.
  - [high] no-sorry guard could fail open → **fixed**: `scripts/check-no-sorry.sh` rewritten
    to fail closed (single non-suppressed `awk`; scanner error ⇒ nonzero exit; verified by test).
  - [medium] `Torus3 := ℝ` leaked real-line semantics → **fixed**: fresh `PUnit`-backed
    placeholder with zero measure.
  - [high] structural theorem vacuous / `ExistsLerayHopf` overclaim risk → **disclosed** (see
    "Known scaffold caveats"); structural redesign deferred to M2+ refinement per the
    plan-authoritative interface. Not closable at M1 without real function spaces.
- **Side A/B** (`--effort xhigh`, working tree): verdict *needs-attention*, 2 findings.
  - [high] Branch A `lower_bound_from_inverse_square_lifespan` proved the *opposite* direction
    (an upper bound on `N`), overclaiming its name. The MVP-plan code sketch was itself
    inconsistent with Branch A's stated lower-bound intent. → **fixed**: statement flipped to
    the genuine lower bound (`C/N² ≤ T−t ⇒ 1/N ≤ √((T−t)/C)`, i.e. `N ≥ √(C/(T−t))`),
    reproved sorry-free by lean-prover.
  - [medium] Branch B `LerayHopfNonunique` froze initial data at universe 0 (non-monotone vs
    the `Type*` interface) → **fixed**: explicit `universe u v`, `Ω : Type u`, `u₀ : Type v`.
- **M2-part1 function spaces** (`--effort xhigh`, `FunctionSpaces.lean`/`TorusDomain.lean`):
  verdict *needs-attention*, 2 findings, both fixed.
  - [high] two non-defeq torus measures (`L2VF` on `volume`, `L2C`/basis on `haarTorus3`)
    would force measure-transport at every M3 boundary → **fixed**: unified all torus L²
    spaces on the single canonical `haarTorus3`; added proven bridge
    `volume_torus3_eq_haarTorus3`.
  - [medium] `mFourierCoeff3` doc claimed a global-`volume` integral while `L2C` is Haar-based
    (Parseval-divergence risk) → **fixed**: redefined `mFourierCoeff3 := torus3_mFourierBasis.repr`.
  - `IsProbabilityMeasure (volume : Measure UnitAddCircle)` instance confirmed sound/non-conflicting.
- **M2 `DivFreeL2`** (`--effort xhigh`, `DivergenceFree.lean`): verdict *approve*. Confirmed the
  Fourier characterization `∑_j k_j û_j(k)=0 ∀k` faithfully encodes `div u = 0` (2π/i
  normalization cancels in the `=0` condition), `compLpL` a.e. semantics correct, non-vacuous.
- **M2 `L2Sigma`** (`--effort xhigh`, `Leray.lean`): verdict *approve*. `⨅ k, ker(divSymbol k)`
  is the genuine divergence-free subspace by construction; closedness sound (continuous kernels
  + arbitrary closed intersection); axiom-free (`#print axioms`: only propext/Choice/Quot).
- **M3-part1 projections** (`--effort xhigh`, `Leray.lean`/`GalerkinProjection.lean`): verdict
  *needs-attention*, 2 findings, both fixed.
  - [medium] `lerayProjection` docstring overclaimed a Helmholtz gradient-kernel theorem not
    formalized → **fixed**: docstring states only the proved orthogonal-projection facts
    (kernel = `L2Sigma`ᗮ); Helmholtz identification flagged as future work.
  - [medium] `Pₙ` not connected to Fourier truncation → **fixed**: proved
    `fourierProjection_n_mFourierCoeff` (`P̂ₙf(k) = if k ∈ box then f̂(k) else 0`), the genuine
    Fourier-multiplier formula, sorry-free/axiom-clean. Leray projection (idempotent, range,
    self-adjoint, contraction, fixes div-free) + `Pₙ` convergence `Pₙf→f` all sorry-free.
- **M3-part2 velocity Galerkin** (`--effort xhigh`, `VelocityGalerkin.lean`): verdict *approve*,
  no findings. `velocityProjection_n : L2VF →L[ℝ] L2VF` (componentwise truncation) with
  `velocityProjection_n_tendsto` (`Pₙu→u`) and `velocityProjection_n_preserves_L2Sigma`
  (truncation preserves div-free) proved sorry-free/axiom-clean. The real-valuedness of `Pₙ`
  on real inputs is proved (`conjL2C_fourierProjection`: conjugate-symmetric coefficients +
  symmetric box). Bonus: `mFourierCoeff3 f k = ∫ mFourier(-k)·f ∂haarTorus3` holds by
  `mFourierBasis_repr` with NO measure bridge — confirms the M2 measure unification is
  definitionally exact.
- **M4 abstract energy** (`--effort xhigh`, `EnergyEstimate.lean`): verdict *needs-attention*,
  2 findings, both fixed.
  - [medium] capstone didn't supply the nonneg-dissipation premise for `energy_nonincreasing`
    → **fixed**: added `accumulatedDissipation_nonneg` + `energy_nonincreasing` (proved),
    closing the bridge to `EnergySkeleton`.
  - [medium] `GalerkinApproximation` name overclaimed (it's an abstract scalar energy law, not
    a full Galerkin construction) → **fixed**: renamed `AbstractEnergyLaw` with a docstring
    stating the concrete Galerkin construction is frontier. Abstract energy identity/inequality
    proved sorry-free/axiom-clean.
- **M5 Rellich compact embedding** (`--effort xhigh`, `RellichEmbedding.lean`): verdict
  *approve*, no findings. Confirmed `H1_ball_totallyBounded` is the GENUINE non-vacuous Rellich
  (H¹-ball precompact in the ambient L² metric; set non-empty via `memH1Torus_zero`), Parseval
  (L1) correct, tail bound (L3) correct, `‖f−Pₙf‖²` = out-of-box tail (L2) correct. All 6 lemmas
  (L1–L4, the finite-rank compactness Bonus, L5) sorry-free and `#print axioms`-clean. The
  Aubin–Lions *spatial* linchpin on T³ — the user's key strategy — is cracked, axiom-free.

- **M6 axiomatic closure** (`/codex:adversarial-review --effort xhigh`, working tree,
  `SolutionInterfaces.lean` + `EvolutionTriple.lean`): **8 rounds** of adversarial axiom auditing,
  ending in **`approve`**. Codex caught and forced fixes to, in order:
  (v1) a hidden inconsistency — `stokes`/`b` under-specified off-diagonal, with the ∀-`F` ODE axiom
  demanding `stokes(u,0)=0` ⇒ added `b` trilinearity + `stokes` bilinearity;
  (v1) a FALSE 3D convection bound (`H¹×H¹→L²`) ⇒ replaced with the true smooth-test bound
  `|b(u,v,w)|≤C‖u‖_{L²}‖v‖_{L²}` for Galerkin `w` (via antisymmetry);
  (v1) `WeakFormNS` testing all of L² ⇒ restricted to `isTest` (Galerkin/smooth div-free) tests;
  (v2) the Aubin–Lions package's `galSeq` untied to the input ⇒ parameterized the package by `galSeq`;
  (v2) energy inequality stated for all `t≥0` ⇒ scoped to `[0,T]`;
  (v3) `stokes` pinned only on the diagonal (free skew term) ⇒ added symmetry (polarization pins it);
  (v4) a TOTAL real Stokes form with H¹ diagonal is impossible (∞ off H¹) ⇒ **de-axiomatized** the
  viscous form entirely (concrete `stokesTestPairing`/`viscousFormSq`); A4 is now convection-only;
  (v5) energy inequality didn't enforce the H¹ energy class (`tsum` collapse) ⇒ proof-carry
  a.e.-`memH1VF` + integrable dissipation (a.e.-in-time H¹ membership; not literal Bochner
  membership `u∈L²(0,T;H¹_σ)`, see `README.md`'s claims table);
  (v6) A3 asserted pointwise facts for an arbitrary null-set representative ⇒ made A3 **existential**
  (a good representative exists);
  (v7) the existential became untethered (≈ standalone existence) ⇒ added the a.e.-link
  `∀ᵐ t, u t = alPkg.u t` to the Aubin–Lions limit; (v8) **approve**.
  Final assembly proved sorry-free; `#print axioms exists_lerayHopf_torus3` at time of
  M6 closure = 1 project axiom (`aubin_lions`) + `propext`/`Classical.choice`/`Quot.sound`
  (`galerkin_ode_solution` proved #24; `torusConvectionGap_exists` proved #53;
  `galerkin_limit_passage` removed #25 / PR #75). **`aubin_lions` subsequently REMOVED
  (issue #23 T-AL-6 Stage C)** — T³ is now kernel-only; see top banner.
- **R3 ℝ³ axiomatic closure** (`/codex:adversarial-review --effort xhigh`, `R3/SolutionInterfaces.lean`):
  **2 rounds** → **`approve`** (the T³ audit lessons applied preemptively converged it fast). Codex
  caught and forced fixes to: (v1-crit) `R3GalerkinScheme` admitting the identity map (which collapsed
  `IsGalerkinTest_R3` to all of L² and falsified `b_bound`/`reg_mem`) ⇒ added `range_schwartz` forcing
  the projector range to be Schwartz div-free; (v1-high) `aubin_lions_R3` asserting **global** ℝ³
  compactness (false without tightness) ⇒ reformulated `spatial_compactness_R3`/`aubin_lions_R3` to
  **LOCAL** L²(B_R) convergence (true local Rellich, no tightness; Schwartz-test decay handles the
  tail); (v2) **approve**. Final assembly proved sorry-free; current
  `#print axioms exists_lerayHopf_r3` = `[propext, Classical.choice, Quot.sound]` — **0
  project axioms, KERNEL-ONLY** (was 6 — removals #2/#10/#21/#15/#44/#47/#56/#46/#4-PR6).
  The ℝ³ spatial+regularity layer
  (`R3/Domain`, `DivergenceFree`, `Regularity`) is axiom-free.

## Notes

- The original scaffold target `exists_lerayHopf_torus3_statement` (formerly in
  `Statement.lean`, permanently marked `sorry`) has been **deleted (issue #144)**: the genuinely
  proved `exists_lerayHopf_torus3` (in `TorusGalerkinODECapstone.lean`) — which carries the
  proof-carrying `LerayHopfSolutionFull` (weak form, energy inequality, initial trace, energy
  class) **unconditionally**, all T³ project axioms removed (issue #23 T-AL-6 finish line;
  `#print axioms` = kernel-only) — made the scaffold target obsolete rather than merely
  superseded, so it was removed instead of kept as a permanent `ALLOW_SORRY`.
  (`exists_lerayHopf_torus3` was renamed from `exists_lerayHopf_torus3` in Wave-0.)
- **Next:** pivot to R³ — instantiate the abstract `DissipativeEvolution`/`WeakFormNS` + the
  abstract A1–A3 pattern; R³ needs its OWN spatial-compactness axiom (Rellich FAILS on ℝ³ —
  no compact Sobolev embedding; needs tightness/concentration-compactness).
