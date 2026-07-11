# Campaign plan — issue #4: discharge `galerkin_limit_passage_R3` (the LAST project axiom)

> **ARCHIVED — CAMPAIGN COMPLETE (2026-07-05).** Historical record only. Issue #4 is closed:
> `galerkin_limit_passage_R3` is PROVED (PR #94–#99; ℝ³ = 0 project axioms, kernel-only — see
> `docs/STATUS.md`). Do NOT execute any instruction below — in particular the §8
> "First dispatch-ready task" checkout recipe (`git checkout origin/lane-weakformns-p1 -- …`)
> targets the 2026-07-04 tree and would overwrite later refactors if run against today's main.

Architect: lean-architect (fable). Date: 2026-07-04. Base: main `c647b85` (preflight green,
live pin R3 = 1 project axiom, T³ = 0).

Spike: `LerayHopf/Scratch/Issue4LimitPassageSpike.lean` — BUILDS (exit 0; the only sorries are
the 4 intended statement probes S3–S6). Every conjunct of the target was elaborated against the
real interfaces (spike rule satisfied).

## 0. Target (verbatim anchor)

`axiom galerkin_limit_passage_R3` — `LerayHopf/R3/AxiomaticClosure.lean:574–593`.
Conclusion = `∃ u : Time → L2Sigma_R3` with FIVE conjuncts:

1. **a.e.-link**: `∀ᵐ t ∂(volume.restrict (Icc 0 T)), u t = alPkg.u t`
2. **weak equation**: `WeakFormNS ν T (r3Evolution 𝔊 F) u`
   (test class = `IsSchwartzDivFree_R3`, `EvolutionTriple.lean:106`, `AxiomaticClosure.lean:357`)
3. **energy inequality, ∀ t ∈ [0,T]** (NOT a.e.): `½‖u t‖² + ∫₀ᵗ visc_ν(u s) ≤ ½‖u₀‖²`
4. **initial trace**: `Tendsto (u ·) (nhdsWithin 0 (Ici 0)) (𝓝 u₀)` — NB this filter contains
   the point `0`, so it PINS `u 0 = u₀` exactly; the representative must be built accordingly.
5. **energy class**: a.e. `memH1VF_R3` + `IntervalIntegrable (visc_ν ∘ u) volume 0 T`

Sole code consumer: `build_galerkin_package_R3_of_galSeq`
(`LerayHopf/R3/AubinLionsAssembly.lean:72–93`), whose sole consumer is the capstone chain in
`GalerkinODECapstone.lean` (concrete scheme `schemeOfBasis B`, `B` from
`nonempty_schwartzGalerkinBasis`, line 106–108).

## 1. Feasibility verdict — GO, with TWO route corrections

### 1a. The Lions–Magenes "good representative" wall is BYPASSED (route decision R1)

Conjuncts 1/3/4 do NOT need `TimeSobolev`/Lions–Magenes `C([0,T];L²)` embedding. The torus
campaign already PROVED the identical 5-conjunct existential
(`torus_galerkin_limit_passage_of_energyClass`, `LerayHopf/TorusTraceEnergy.lean:1318`) via the
classical Temam-III.3 weakly-continuous-representative route:

- per-fixed-test scalar curves `t ↦ ⟪uₙ t, w⟫` are equi-Lipschitz (ODE + energy bound)
  — R3 analogue of the derivative step is ALREADY PROVED inside `galerkin_pairing_FTC`
  (`GalerkinTrilinearBound.lean:1001`, uses `mono_range`-free per-level test);
- they converge at a.e. t (dense in `[0,T]`), hence — equi-Lipschitz + uniform bound — at
  EVERY `t ∈ [0,T]` (`cauchySeq_of_equiLipschitz_of_dense`, `TorusTraceEnergy.lean:497`,
  generic in `f : ℕ → ℝ → ℝ`);
- Galerkin-test density (`𝔊.tendsto_id`) + uniform bound extends Cauchy-ness to all pairings
  (`cauchySeq_inner_extend`, `TorusTraceEnergy.lean:337`, generic Hilbert);
- Riesz representation inside the closed submodule gives the ∀t weak-limit representative
  (`exists_weak_limit_in_submodule`, `TorusTraceEnergy.lean:385`, generic
  `K : Submodule ℝ E` + `[K.HasOrthogonalProjection]`; `L2Sigma_R3` is a closed submodule,
  `DivergenceFree.lean:90/94`);
- ∀t energy by norm-lsc under ∀t weak convergence + per-n integrated energy identity — the R3
  identity `galerkinCurve_energy_identity` (B8) is ALREADY PROVED
  (`GalerkinCurveBounds.lean:364`); dissipation lsc via the ALREADY-PROVED
  `viscous_pointwise_lsc` / `viscous_lsc_under_strongL2`
  (`AubinLionsLimitPassage.lean:1240/1357`);
- strong trace at `0⁺` from `v 0 = u₀` + `‖v t‖ ≤ ‖u₀‖` ∀t + weak continuity
  (`strong_trace_of_props`, `TorusTraceEnergy.lean:935`).

R3 deltas vs torus: (i) a.e.-t STRONG global convergence is replaced by a.e.-t per-ball
convergence + tail (`alPkg.strong_convergence_ae` + `inner_tendsto_of_perball`,
`AubinLionsLimitPassage.lean:785` — proved); no further subsequence `ρ` is needed
(the package field already carries the a.e.-t form for the full subsequence `φ`).
(ii) test level-promotion uses `𝔊.mono_range` (AxiomaticClosure.lean:207, already a field);
(iii) the per-test stokes bound `|B(u,w)| ≤ C(w)‖u‖` comes from the negLap representation
`stokesTestPairing_R3_eq_sum_inner_negLap` (`CurlDensity.lean:1699`, proved) via
`range_schwartz` witnesses.

### 1b. NEW wall found (and resolved): conjunct 2 needs an H¹ test-approximation the current interfaces cannot supply (route decision R2)

The live sorry's plan (`AubinLionsLimitPassage.lean:2424`, atom "(c) DENSITY — UNNECESSARY")
is WRONG, and PR #69's step "(iii) N→∞ via `𝔊.tendsto_id`" is UNPROVABLE as written:

- `u_ode` (`AxiomaticClosure.lean:393`) fires ONLY on Galerkin-fixed tests
  (`𝔊.P n w = w`); the `WeakFormNS` test `w` is an arbitrary `IsSchwartzDivFree_R3` field, so
  a Galerkin→Schwartz test-extension step is unavoidable.
- In that extension, the viscous term `B(u t, ·)` and the convection term `b(u t, u t, ·)` are
  continuous in the test slot only in the H¹ graph seminorm
  (`stokesTestPairing_abs_le`, `GalerkinCurveBounds.lean:274`: `|B(u,z)| ≤ √V₁(u)·√V₁(z)`;
  `convIntegralSchwartz_bound_energy` C4, `GalerkinTrilinearBound.lean:706`: third slot enters
  as `√V₁(z)`). `𝔊.tendsto_id` is L²-only. L²-convergence of `P_N w → w` does NOT control
  `V₁(P_N w − w)`.
- The discharged curl-density proof (`CurlDensity.lean`, orthocomplement argument) is L²-only
  and gives no H¹-approximation; the abstract `R3GalerkinScheme` has no field from which the
  H¹ approximation follows. I judge the axiom UNPROVABLE VERBATIM for arbitrary abstract `𝔊`
  (an L²-dense but H¹-degenerate scheme has no reason to produce a limit satisfying the weak
  equation against all Schwartz tests).

**Resolution (R2):** thread ONE new hypothesis, not a structure field:

```
def R3TestApproxH1 (𝔊 : R3GalerkinScheme) : Prop :=
  ∀ w, IsSchwartzDivFree_R3 w → ∀ ε > 0,
    ∃ v, IsGalerkinTest_R3 𝔊 v ∧ IsSchwartzDivFree_R3 v ∧
      ‖(v:L2VF_R3) - w‖ < ε ∧ viscousFormSq_R3 1 ((v:L2VF_R3) - w) < ε
```

(elaborated in spike S2). The replacement theorem `galerkin_limit_passage_R3` gains exactly
this one binder (spike S3 elaborates the FULL statement); `build_galerkin_package_R3_of_galSeq`
and `build_galerkin_package_R3_of_basis` thread it; the capstone discharges it CONCRETELY.
Precedent for signature-evolving axiom removal: #15 (`aubin_lions_R3`), #48. The pinned
capstone statement `exists_lerayHopf_r3_axiomatic` is byte-unchanged.

**Concrete discharge of `R3TestApproxH1 (schemeOfBasis B')`** — the new analytic kernel:

- **H¹ curl approximation at Schwartz div-free targets** (spike S6): for
  `w` Schwartz-div-free and `ε > 0` there is a Schwartz potential `ψ` with
  `‖curlSchwartzL2 ψ − w‖ < ε` and `V₁(curlSchwartzL2 ψ − w) < ε`.
  Proof route (Fourier low-frequency cutoff — CONSTRUCTIVE, unlike the orthocomplement
  density): `ŵ` is transverse (`mem_sigma_iff_fourier_transverse`, `CurlDensity.lean:952`,
  proved; components continuous since Schwartz); set
  `ψ̂_δ(ξ) := χ_δ(ξ)·(ξ × ŵ(ξ))/(2πi‖ξ‖²)` with `χ_δ` smooth, radial, `0` near `0`, `1` on
  `‖ξ‖ ≥ δ`. Then `𝓕(curl ψ_δ) = χ_δ·ŵ` (BAC-CAB + transversality), so the L² and weighted-L²
  (H¹) errors are `∫_{‖ξ‖≤δ}(1+W)|ŵ|² → 0`. The symbol is Schwartz (smooth cutoff kills the
  singularity; temperate-growth multiplication), realized as a genuine `SchwartzMap` via
  `FourierTransform.fourierCLE` (live mathlib name — deprecation of
  `SchwartzMap.fourierTransformCLE` noted in spike S7) and the Hermitian-reality machinery
  already in `CurlDensity.lean` (`fourier_hermitian_real`, `FourierInvPair`) to get REAL
  potentials from the Hermitian symbol (`w` real ⇒ `ŵ` Hermitian ⇒ symbol Hermitian).
- **Countable H¹-dense curl family** for the strengthened basis: the graph space embeds in
  `L2VF_R3 × (Fin 3 → L2C)`; `SecondCountableTopology L2VF_R3` SYNTHESIZES from the pinned
  mathlib (`Lp.SecondCountableTopology`, `Mathlib/MeasureTheory/Measure/SeparableMeasure.lean:425`
  — spike S1 confirms; the ℂ-valued instance needs a one-line `haveI : Fact ((2:ENNReal) ≠ ⊤)`).
  A separable-metric-subspace argument yields a countable `𝒟 ⊆ range curlSchwartzL2` that is
  H¹-graph-dense in the curl class. A `SchwartzGalerkinBasis` enumerating `𝒟` keeps
  `dense_span` (H¹-dense ⇒ L²-dense in the curl class, whose span is L²-dense by
  `curlSchwartzDense_holds`) and its prefix spans H¹-capture every Schwartz div-free target
  (single curl fields suffice; a basis element is fixed by `schemeOfBasis` projectors —
  orthogonal projection onto `galerkinSpan B N`, `GalerkinScheme.lean:143–146`).

### 1c. Everything else is port/assembly on proved parts

Conjunct 5 is PROVED for `alPkg.u` (`viscous_lsc_under_strongL2`) and transfers a.e.
Conjunct 2 transfers from `alPkg.u` to the representative by
`intervalIntegral.integral_congr_ae` (torus assembly shows the exact pattern,
`TorusTraceEnergy.lean:1355–1364`).

## 2. Route decisions (binding — do not change without re-engaging the architect)

- **R1** Good representative via the torus-proven ∀t-weak-limit route
  (per-test equi-Lipschitz + dense-times Cauchy + Riesz-in-submodule). NO Lions–Magenes, NO
  `TimeSobolev` dependency, NO further subsequence beyond `alPkg.φ`.
- **R2** Conjunct 2 in two stages: W1 (n→∞ against FIXED Galerkin tests) + W2 (test extension
  under the new threaded hypothesis `R3TestApproxH1 𝔊`); `R3TestApproxH1` discharged only for
  the concrete strengthened basis (Fourier low-cut curl approximation + separability).
  `R3GalerkinScheme` is NOT enriched; `r3Evolution.isTest` is NOT weakened (guardrail).
- **R3** W2's nonlinear test-slot bound for the LIMIT curve uses the liminf dodge (transfer
  through the approximants with C5 `bForm_galerkin_abs_le` + Fatou), NOT an L⁶/GNS theory for
  general H¹ fields (which does not exist in the repo and is not needed).
- **R4** The axiom is DELETED and the byte-identical-conclusion theorem (with the one `htest`
  binder) lives DOWNSTREAM (new file), consumers rewired — the #15/#48 relocation pattern.
  Capstone statement unchanged; preflight pin flips R3 1 → 0 (KERNEL-ONLY).

## 3. Phases (PR-sized), exact targets, model tiers

Statement sources: spike file S2–S6 blocks are the AUTHORITATIVE Lean statements; lean-coder
transcribes them verbatim into scaffolds (Codex gate before proving, per doctrine).

### PR-1 — W1: weak identity against Galerkin tests (+ PR #69 adoption)
*Files: `LerayHopf/R3/ConvectionForm.lean` (adopt branch FILE STATE), `LerayHopf/R3/AubinLionsLimitPassage.lean` (or new `WeakFormLimit.lean`).*
1. Adopt the FULL FINAL `ConvectionForm.lean` FILE STATE from `origin/lane-weakformns-p1`
   tip `f8ae35d` (G1 Codex finding, route (a) — see §5 for ancestry):
   `git checkout origin/lane-weakformns-p1 -- LerayHopf/R3/ConvectionForm.lean` on the PR-1
   branch. SAFE: the main(`c647b85`)→branch-tip delta on this file is PURELY ADDITIVE
   (verified: 0 deleted lines), so branch file = main file + the +422 block
   (`schwartz_ball_tail_decay`, `mulBddR_projComp_norm_tendsto_CF`, `mulBddR_self_adjoint`,
   `fb_tendsto_of_perball`, incl. the cb693ed-era helpers `f8ae35d` builds on).
   Do NOT cherry-pick `f8ae35d` alone (its parent `cb693ed` is NOT in main; the patch is
   incremental on cb693ed helpers). Do NOT transplant ANY `AubinLionsLimitPassage.lean`
   delta from the branch (the cb693ed/f8ae35d +56 Temam-III.3 skeleton is superseded, §1b/§5).
   Expected sorry status of the transplanted file: 0 `sorry` tokens, 0 `ALLOW_SORRY`
   (verified on the branch tip; the 4 textual `sorry` grep hits are docstring "sorry-free"
   phrases). Gate: full `lake build` right after the checkout — the branch base is pre-#46
   main (`d2c8190`), so cross-file API drift is possible even though the file-level
   transplant is exact.
2. `weakFormNS_galerkinTest_limit` (spike S4 statement, VERBATIM): for a Galerkin test `w`
   and admissible `ψ`, the limit-curve integral identity `= 0`.
   Proof skeleton: per-n identity by time-IBP of `galerkin_pairing_FTC`'s derivative
   (`HasDerivAt ⟪uₙ·,w⟫` is literally proved inside `GalerkinTrilinearBound.lean:1014`;
   torus pattern `galerkin_weakFormNS_zero`, `TorusLimitPassage.lean:86`); n→∞ by time-DCT
   with constant dominators (`galerkin_norm_le_u0`; `b_bound` C(w)M²; negLap Cauchy–Schwarz),
   a.e.-t convergences: `inner_tendsto_of_perball` (linear),
   `stokesTestPairing_R3_eq_sum_inner_negLap` + weak (viscous), `fb_tendsto_of_perball`
   (nonlinear; `w` is Schwartz-div-free by `range_schwartz`). Level promotion `n ≥ m` via
   `𝔊.mono_range`.
3. De-privatize (lean-coder, no statement changes): `inner_tendsto_of_perball`,
   `weak_tendsto_of_inner_tendsto`, `norm_le_liminf_of_inner_tendsto`, `galerkin_norm_le_u0`,
   `galerkin_curve_continuous` in `AubinLionsLimitPassage.lean`.
4. Small lemma `galerkinCurve_energy_le` (from B8 + `u_initial` + `𝔊.norm_le`):
   `½‖uₙ t‖² + ∫₀ᵗ visc_ν(uₙ) ≤ ½‖u₀‖²` for `t ≥ 0`.
   Tier: scaffold sonnet / prove **opus**; step 2 is the hard part (escalate to fable-prover
   after 2 failed opus rounds).

### PR-2 — H¹ curl approximation (the new analytic kernel)
*New file `LerayHopf/R3/CurlDensityH1.lean`.*
- `curl_approx_H1` (spike S6 statement VERBATIM, name without `_spike`).
- Sub-lemmas (statement sketches, coder to refine with prover input): smooth radial low-cut
  `χ_δ` (mathlib bump/`Real.smoothTransition`); Schwartz symbol
  `ξ ↦ χ_δ(ξ)·(ξ × ŵ(ξ))·(2π‖ξ‖²)⁻¹`-componentwise (temperate-growth multiplication on
  `SchwartzMap`); inverse-Fourier realization (`FourierTransform.fourierCLE`); reality via the
  Hermitian machinery (`CurlDensity.lean` anchors: `fourier_hermitian_real`,
  `fourier_curlSchwartz_eq_cross:256`); BAC-CAB cancellation with transversality
  (`mem_sigma_iff_fourier_transverse:952`); weighted low-frequency error → 0 (DCT in `δ`).
  Tier: **fable-prover** (novel construction; all toolkit anchors verified in spike S7).
  Independent of PR-1; can run in parallel.

### PR-3 — strengthened basis + `R3TestApproxH1` discharge
*Files: new `LerayHopf/R3/GalerkinBasisH1.lean` (+ small additions where the coder judges).*
- `def R3TestApproxH1` (spike S2 VERBATIM; place upstream enough for PR-4/PR-6 — e.g. in
  `GalerkinScheme.lean` or the new file, coder's structural call).
- `nonempty_schwartzGalerkinBasis_H1 : Nonempty {B : SchwartzGalerkinBasis // R3TestApproxH1 (schemeOfBasis B)}`
  via: countable H¹-graph-dense `𝒟` in the curl class (separability, spike S1 instances; the
  ℂ-Lp instance needs the `Fact ((2:ENNReal) ≠ ⊤)` haveI), enumeration, `dense_span` from
  `curlSchwartzDense_holds` + H¹⇒L² density, prefix-span fixing
  (`galerkinSpan`/`starProjection` anchors `GalerkinScheme.lean:113–161`), and PR-2's
  `curl_approx_H1`. Also the small glue `IsSchwartzDivFree_R3` for basis elements
  (`curlSchwartz_isSchwartz`, `SchwartzDivFreeBasis.lean` A3/A4).
  Tier: **opus** (choice/plumbing-heavy, no new analysis). Depends on PR-2.

### PR-4 — W2: test extension ⇒ full `weakFormNS_limit_passage`
*File: `AubinLionsLimitPassage.lean` (or the PR-1 home of W1).*
- Restate `weakFormNS_limit_passage` with the added binder `(htest : R3TestApproxH1 𝔊)`
  (architect-approved signature change of a scaffold lemma; discharge its `ALLOW_SORRY`).
- Proof: fix `ψ, w`; take `v_k := htest`-approximants (`ε := 1/(k+1)`); W1 gives the identity
  at each `v_k`; the difference of integrands at test slot `z_k := v_k − w`:
  - inner term: `≤ ‖ψ'‖-weighted · M‖z_k‖` (a.e. bound `kineticEnergy_lsc_bound`);
  - viscous: `|B(u t, z_k)| ≤ √V₁(u t)·√V₁(z_k)` (`stokesTestPairing_abs_le`; `u t` a.e.-H¹
    and `∫V₁(u) < ∞` from `viscous_lsc_under_strongL2`; `z_k` H¹ via Schwartz reps —
    de-privatize `memH1VF_R3_of_isSchwartzDivFree`, `SobolevEmbedding.lean:1067`);
  - nonlinear (route R3): a.e.-t `b(u t,u t,z_k) = lim_n b(uₙ t,uₙ t,z_k)`
    (`fb_tendsto_of_perball`, `z_k` Schwartz-div-free) with
    `|b(uₙ,uₙ,z_k)| ≤ C_b‖u₀‖^{1/2}·V₁(uₙ t)^{3/4}·√V₁(z_k)` (C5
    `bForm_galerkin_abs_le:795`), then Fatou-in-t + Hölder `∫V₁^{3/4} ≤ (∫V₁)^{3/4}T^{1/4}`
    + `reg_bound`.
  All error terms `→ 0` with `√V₁(z_k) + ‖z_k‖ → 0`. Tier: **opus** (bookkeeping-heavy,
  fully specified). Depends on PR-1 + PR-3 (def only; can start once `R3TestApproxH1` def
  lands — proof needs nothing from PR-2/PR-3 beyond the def).

### PR-5 — good representative (torus port)
*New file `LerayHopf/R3/GoodRepresentative.lean` (+ hoisted generic toolkit).*
- Hoist/duplicate the GENERIC Hilbert/time toolkit from `TorusTraceEnergy.lean`
  (`normSq_le_liminf_of_inner_tendsto:274`, `cauchySeq_inner_extend:337`,
  `exists_weak_limit_in_submodule:385`, `exists_mem_of_ae_full:457`,
  `cauchySeq_of_equiLipschitz_of_dense:497`) into a shared generic file
  (coder decision: e.g. `LerayHopf/Bochner/WeakLimitToolkit.lean`), and REWIRE the torus file
  to consume it (no torus statement changes) — or duplicate if rewiring is riskier.
- `perTest_lipschitz_R3` (torus `:563` pattern; stokes bound via negLap + `range_schwartz`,
  b bound via `b_bound`, promotion via `mono_range`).
- `exists_weak_representative_R3` (spike S5 statement VERBATIM): conjuncts
  (a.e.-eq via weak-limit uniqueness against `inner_tendsto_of_perball`; `v 0 = u₀` via
  `u_initial` + `𝔊.tendsto_id` at `u₀`; ∀t bound; per-test Lipschitz limits).
- `weak_trace_inner_R3`, `strong_trace_of_props_R3` (torus `:824/:935` ports; density from
  `𝔊.tendsto_id`).
  Tier: **opus** (structured port). Independent of PR-1..4; may run parallel after PR-1's
  de-privatization lands (or include that de-privatization here if PR-1 lags).

### PR-6 — ∀t energy + assembly + AXIOM FLIP
*New file `LerayHopf/R3/LimitPassage.lean`; edits: `AxiomaticClosure.lean` (delete axiom),
`AubinLionsAssembly.lean`, `GalerkinODECapstone.lean`, `scripts/check-axioms-live.sh`, docs.*
- `viscous_lsc_partial`: ∀ `t ∈ [0,T]`,
  `ENNReal.ofReal (∫₀ᵗ V₁(alPkg.u)) ≤ liminf_n ofReal (∫₀ᵗ V₁(uₙ))`
  (Fatou-in-time against `viscous_pointwise_lsc`; the `[0,t]`-restriction inherits a.e. facts
  from `[0,T]` by measure monotonicity).
- `energy_ineq_of_representative_R3` (torus `:1109` port; kinetic part by
  `norm(Sq)_le_liminf_of_inner_tendsto` at `z := v t`, per-n bound by
  `galerkinCurve_energy_le`, liminf superadditivity).
- `galerkin_limit_passage_R3` as a THEOREM (spike S3 statement VERBATIM, incl. `htest`),
  assembled exactly like `torus_galerkin_limit_passage_of_energyClass:1318`
  (conjunct 2 via `intervalIntegral.integral_congr_ae` transfer; conjunct 5 via
  `viscous_lsc_under_strongL2` + a.e. transfer).
- Flip: delete the axiom; `build_galerkin_package_R3_of_galSeq` gains `htest`;
  `build_galerkin_package_R3_of_basis`/capstone obtains `B` from
  `nonempty_schwartzGalerkinBasis_H1` and supplies the witness; preflight pin R3 → 0
  (KERNEL-ONLY); doc de-staling (AxiomaticClosure header, STATUS/ROADMAP).
  Tier: energy/assembly **opus**; flip mechanics **sonnet**. Depends on PR-1..5.

Dependency order: PR-1 ∥ PR-2 → PR-3 → (PR-4) ; PR-5 ∥ (PR-2..4) ; PR-6 last.
Critical path: PR-2 → PR-3 → PR-6 and PR-1 → PR-4 → PR-6.

## 4. Reuse map

| Need | Existing artifact (verified anchor) |
|---|---|
| per-n energy identity/ineq | `galerkinCurve_energy_identity` B8, `GalerkinCurveBounds.lean:364` |
| per-test FTC/derivative | `galerkin_pairing_FTC` B9, `GalerkinTrilinearBound.lean:1001` |
| n-uniform trilinear energy bound | `bForm_galerkin_abs_le` C5 `:795`; C4 `:706` |
| a.e.-t weak convergence from per-ball | `inner_tendsto_of_perball` / `weak_tendsto_of_inner_tendsto`, `AubinLionsLimitPassage.lean:785/826` |
| kinetic a.e. bound | `kineticEnergy_lsc_bound:459` |
| viscous lsc + energy class | `viscous_pointwise_lsc:1240`, `viscous_lsc_under_strongL2:1357` |
| viscous weak-continuity in u | `stokesTestPairing_R3_eq_sum_inner_negLap`, `CurlDensity.lean:1699` |
| viscous H¹ Cauchy–Schwarz | `stokesTestPairing_abs_le`, `GalerkinCurveBounds.lean:274` |
| nonlinear a.e.-t passage | `fb_tendsto_of_perball` — PR #69 branch `f8ae35d` (sorry-free, to adopt) |
| b integral rep (fixed Schwartz test) | `fb_eq_antisymmIntegral`, `ConvectionForm.lean:855` (main) |
| ∀t-representative machinery | `TorusTraceEnergy.lean` `:274–:1376` (generic toolkit + port patterns) |
| WeakFormNS n→∞ + IBP pattern | `TorusLimitPassage.lean:86/:382` |
| Fourier/curl toolkit | `CurlDensity.lean` (`:256`, `:952`, Hermitian machinery), `FourierTransform.fourierCLE` |
| separability | `Lp.SecondCountableTopology`, mathlib `SeparableMeasure.lean:425` (spike S1) |

## 5. PR #69 verdict — ADOPT the final ConvectionForm FILE STATE, SUPERSEDE the rest

*(Revised after G1 Codex gate: the original claim "cb693ed already in main" was FALSE.)*

- **Verified ancestry** (2026-07-04): branch chain is
  `d2c8190 → a1778d6 (P0.5) → cb693ed (P1) → f8ae35d (F3)`.
  `git merge-base --is-ancestor a1778d6 c647b85` = 0 (P0.5 IS in main);
  `git merge-base --is-ancestor cb693ed c647b85` = 1 (P1 is NOT in main — main's
  `weakFormNS_limit_passage` skeleton at `AubinLionsLimitPassage.lean:2389` is a separate
  re-implementation, with the newer retracted-wall comment). `f8ae35d`'s parent is `cb693ed`,
  so its `ConvectionForm.lean` patch is INCREMENTAL on cb693ed-introduced helpers — a lone
  cherry-pick of `f8ae35d` is unsound.
- **Adoption path = route (a), FILE-STATE adoption**: take the whole
  `ConvectionForm.lean` as of the branch tip `f8ae35d`
  (`git checkout origin/lane-weakformns-p1 -- LerayHopf/R3/ConvectionForm.lean`).
  This is exact and lossless because the `c647b85 → f8ae35d` diff on this file is PURELY
  ADDITIVE (verified: 0 deleted lines), so no main-side content is dropped; it absorbs the
  cb693ed AND f8ae35d ConvectionForm contributions in one step, independent of ancestry.
- **Expected sorry status** of the transplanted file: 0 `sorry` tokens, 0 `ALLOW_SORRY`
  (verified at tip; the only textual `sorry` grep hits are 4 docstring "sorry-free" phrases).
  Residual risk is cross-file API drift (branch base is pre-#46 `d2c8190`) — caught by the
  mandatory full `lake build` immediately after the checkout.
- **Explicitly NOT transplanted**: the branch's `AubinLionsLimitPassage.lean` +56 delta
  (cb693ed skeleton + f8ae35d's structured Temam-III.3 sorry with steps i–iii). It is
  SUPERSEDED: its step (iii) (`N→∞` via L²-only `tendsto_id`) is unprovable for the viscous
  term (H¹-in-test continuity, §1b) — replaced by W1+W2 under `R3TestApproxH1`. The
  file-checkout above touches ONLY `ConvectionForm.lean`, so no skeleton lines can leak in.
- Close PR #69 after PR-1 lands, citing this plan.

## 6. Risk register

1. **PR-2 SchwartzMap symbol engineering** (top risk). Building
   `χ_δ·(ξ×ŵ)/‖ξ‖²` as a `SchwartzMap` and inverting 𝓕 with reality may fight mathlib's API
   (temperate-growth multiplication, vector cross bookkeeping). Mitigation: CurlDensity's
   existing Fourier-preimage/Hermitian machinery is the template; kill criterion: if after 2
   fable-prover rounds the SYMBOL-REALIZATION sub-lemma is still open, fall back to swapping
   the project axiom for the strictly-thinner `curl_approx_H1` statement (net axiom count
   unchanged 1→1, content strictly thinner than the full limit passage — still records the
   whole limit-passage superstructure as proved). This fallback keeps every other PR intact.
2. **W2 measurability/Fatou bookkeeping** (PR-4): integrand a.e.-measurability for the
   liminf-dominated nonlinear term. All patterns exist in `viscous_lsc_under_strongL2`;
   escalate to fable-prover on 2 failed opus rounds, do NOT weaken to an a.e.-t equation.
3. **Torus toolkit hoisting** (PR-5): de-privatizing/hoisting must not perturb the T³
   KERNEL-ONLY pin. Mitigation: hoist into a NEW file consumed by both, keep torus statements
   byte-identical, preflight after every step; duplication is the approved fallback.
4. **Statement traps audited**: conjunct 3 is ∀t (representative route, not a.e.-smuggle);
   conjunct 4's filter pins `u 0 = u₀` (construction sets `v 0 = u₀`; the Riesz limit at
   `t = 0` IS `u₀` since `uₙ 0 = 𝔊.P n u₀ → u₀`); `WeakFormNS` integrand integrability is
   established en route by DCT (no `integral_undef` reliance); no hypothesis equals the goal
   (`htest` is a test-approximation Prop, independent of the NS content).

## 7. Codex gate points (orchestrator runs; workers request)

- G1 (before any proving): this plan + the spike statements S2–S6, especially (a) the
  `htest`-binder signature evolution vs the "byte-identical" ideal, (b) the §1b unprovability
  judgment for the abstract scheme, (c) `R3TestApproxH1`'s non-vacuity/shape.
- G2 (after PR-1 scaffold): `weakFormNS_galerkinTest_limit` statement.
- G3 (after PR-3): `nonempty_schwartzGalerkinBasis_H1` statement (no density smuggling).
- G4 (before PR-6 merge): the flip diff (axiom deletion, pin update, capstone axiom print).

## 8. First dispatch-ready task

PR-1, step 1+3 (lean-coder), on a fresh branch off main:
1. `git fetch origin lane-weakformns-p1` and adopt the ConvectionForm FILE STATE:
   `git checkout origin/lane-weakformns-p1 -- LerayHopf/R3/ConvectionForm.lean`
   (route (a), §5 — NOT a cherry-pick of `f8ae35d`, whose parent `cb693ed` is absent from
   main). Touch ONLY this file from the branch; the branch's `AubinLionsLimitPassage.lean`
   skeleton delta must NOT be transplanted (superseded, §5). Expect the transplanted file to
   carry 0 `sorry` / 0 `ALLOW_SORRY`.
2. Full `lake build` immediately (cross-file drift gate; branch base is pre-#46).
3. De-privatize the five helpers listed in §3 PR-1.3; scaffold
   `weakFormNS_galerkinTest_limit` verbatim from spike S4 with `ALLOW_SORRY: scaffold`;
   preflight green; then Codex gate G2; then lean-prover (opus) on the W1 proof per §3 PR-1.2.

## Appendix — spike outcome (2026-07-04)

`LerayHopf/Scratch/Issue4LimitPassageSpike.lean` builds (exit 0). S1 instances synthesize
(ℂ-Lp needs `haveI : Fact ((2:ENNReal) ≠ ⊤)`); S2–S6 statements elaborate against real
interfaces; S7 anchors all resolve (`SchwartzMap.fourierTransformCLE` deprecated → use
`FourierTransform.fourierCLE`). GO.
