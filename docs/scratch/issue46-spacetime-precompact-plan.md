# Task Contract: Issue #46 — Discharge `galerkin_spacetime_precompact_R3` (Stream R3 / B-AL-precompact)

**Plan date:** 2026-07-02
**Author:** lean-planner
**Supersedes / updates:** `docs/scratch/r46-sound-plan.md` (2026-06-23).  That plan's verdict
("blocked by the trilinear Sobolev wall; no route without a new axiom") is now **obsolete**:
since then the repo has landed, sorry-free and axiom-free,

- `gns_L6_schwartz` — quantitative Gagliardo–Nirenberg–Sobolev `‖φ‖_{L⁶} ≤ C·‖∇φ‖_{L²}` for
  Schwartz maps (`LerayHopf/R3/SobolevEmbedding.lean:559`, public),
- `gns_L6_of_memH1_R3` — H¹ ↪ L⁶ for `MemSobolev 1 2` classes (same file, public),
- the `convIntegralSchwartz` algebra + IBP + integrability library
  (`LerayHopf/R3/TrilinearEstimate.lean`, public),
- L²∩L⁶ ↪ L³ interpolation machinery (`LerayHopf/R3/EnergyClassConvection.lean`,
  `L2L6_inter_mem_L3` public; quantitative form private — rebuild noted below),
- `totallyBounded_of_uniform_approx` (`LerayHopf/R3/FrechetKolmogorov.lean:1806`, **public**),
- `LocalRellichInput` discharged unconditionally
  (`localRellichInput_of_frechetKolmogorov frechetKolmogorov_holds`, visible from
  `R3/SolutionInterfaces.lean`).

With these, the trilinear Sobolev wall is **passable on Galerkin states** (which are
componentwise Schwartz by `R3GalerkinScheme.range_schwartz` + `u_inVn`), and the axiom can be
proved with **zero new axioms** (net project axiom count: −1).

---

## 0 Target

`LerayHopf/R3/ArzelaAscoliTime.lean:123`:

```
axiom galerkin_spacetime_precompact_R3
    (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T) (u₀ : L2Sigma_R3)
    (galSeq : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n)
    (ψ : ℕ → ℕ) (hψ : StrictMono ψ) (k : ℕ) :
    ∃ (ρ : ℕ → ℕ) (g_k : ℝ → L2ballR3 k), StrictMono ρ ∧
      AEStronglyMeasurable g_k (volume.restrict (Set.Icc (0:ℝ) T)) ∧
      Tendsto (fun n => eLpNorm
        (fun t => restrictToBall k ((galSeq (ψ (ρ n))).u t : L2VF_R3) - g_k t)
        2 (volume.restrict (Set.Icc (0:ℝ) T))) atTop (nhds 0)
```

**Conversion rule (hard constraint):** the statement stays **byte-identical** in
`ArzelaAscoliTime.lean` — same name, same binders, same conclusion; only `axiom … -- ALLOW_AXIOM…`
becomes `theorem … := fun … => galerkin_spacetime_precompact_of_goodSampling …` (docstring updated,
`ALLOW_AXIOM` marker and the file-header assumptions section updated, one `import` line added).
Downstream consumers (`perBall_ae_subseq`, `diag_ae_subseq`, `u_lim_aestronglyMeasurable`,
`galerkinSpaceTimeExtraction_R3`) are untouched.

**Files that must NOT be touched** (in-flight work / constraint 1):
`R3/AubinLionsLimitPassage.lean`, `R3/ConvectionForm.lean`, and all torus-#25 files
(`TorusTraceEnergy`, `TorusLimitPassage`, `AxiomaticClosure` (torus root), `TorusConvection*`).
The private Steklov chain in `AubinLionsLimitPassage.lean` (incl.
`steklovAvg_spatial_extraction`) may not be moved or edited; any similar machinery is **built
fresh** in the new upstream files below.  (It turns out we need much less of it than the Steklov
route: see §1.3.)

---

## 1 Mathematical route — "good-sampling" Simon compactness

We prove per-ball L²(0,T; L²(B_k)) total boundedness of the ball-restricted Galerkin curves by
the classical Simon (1987) / Temam III.2 argument, in the **piecewise-constant-sampling** form
(no Arzelà–Ascoli-in-C(K,X), no Steklov mollification, no pointwise time modulus):

For a mesh `δ = T/m` with cells `I_i = [iδ, (i+1)δ]`:

1. **(Good samples.)**  In each cell pick, per `n`, a sample time `τ_i^n ∈ I_i` with
   `viscousFormSq_R3 1 (u^n τ_i^n) ≤ δ⁻¹ · ∫_{I_i} viscousFormSq_R3 1 (u^n σ) dσ
    ≤ δ⁻¹ ν⁻¹ · ½‖u₀‖²`
   (mean-value on the continuous curve `σ ↦ V₁(u^n σ)`; the integrated bound is `reg_bound`,
   ν-rescaled).  Sample states are div-free (`u^n τ ∈ L2Sigma_R3`), H¹ (`reg_mem`), with
   `‖u^n τ‖ ≤ ‖u₀‖` (`energy_bound` + `𝔊.norm_le`) — all **n-uniform** for fixed δ.

2. **(Per-slice compactness.)**  By `LocalRellichInput.ballCompact` (unconditional, FK-derived)
   with `M_δ := max ‖u₀‖ √(δ⁻¹ν⁻¹·½‖u₀‖²)` and radius `k`, all ball-restricted samples
   `restrictToBall k (u^n τ_i^n)` lie in one fixed compact `K_{δ,k} ⊆ L2ballR3 k`.

3. **(Step curves.)**  `step^n(t) := restrictToBall k (u^n τ_{i(t)}^n)`, piecewise constant on
   the fixed mesh.  The set of ALL mesh-`m` step curves with values in `K_{δ,k}` is the
   continuous image of the compact `(K_{δ,k})^m`, hence **compact** in
   `Lp (L2ballR3 k) 2 (volume.restrict (Icc 0 T))`.

4. **(Uniform sampling error — the analytic core, dual-norm-only.)**  Cell-wise, split

   `‖u(t) − u(τ)‖² = (‖u t‖² − ‖u τ‖²) − 2⟪u t − u τ, u τ⟫`,

   and evaluate BOTH parts by scalar FTC along the curve using ONLY the Galerkin ODE tested
   against vectors of `V_n` (the pairing `⟪u'(σ), w⟫` for `w` with `𝔊.P n w = w` — never a
   pointwise norm of `u'`):
   * energy part: `‖u t‖² − ‖u τ‖² = −2∫_τ^t viscousFormSq_R3 ν (u σ) dσ`
     (ODE with `w := u σ`, `b(u,u,u) = 0` by `b_antisymm`), so `|·| ≤ 2∫_{I_i} V_ν`;
   * pairing part with FIXED test `w := u τ_i^n ∈ V_n`:
     `⟪u t − u τ, w⟫ = ∫_τ^t (−ν·stokesTestPairing_R3(u σ, w) − F.b (u σ) (u σ) w) dσ`, bounded by
     - `|stokesTestPairing_R3(v,w)| ≤ √V₁(v)·√V₁(w)` (weighted-Fourier Cauchy–Schwarz, new lemma), and
     - `|F.b(v,v,w)| ≤ C_b · ‖v‖^{1/2} · V₁(v)^{3/4} · √V₁(w)` on Galerkin states
       (Hölder 3–2–6 on `convIntegralSchwartz` via the `b_galerkin` pin + `gns_L6_schwartz`
       + L²∩L⁶↪L³ interpolation; `C_b` is an **absolute** constant — no n-dependence),
     with `√V₁(w) = √V₁(u τ_i^n) ≤ √(δ⁻¹ν⁻¹·½‖u₀‖²)` from the good sample.

   Integrating over `t ∈ I_i`, summing cells, and using `reg_bound` + Hölder in time
   (`∫√V₁ ≤ √T·√(∫V₁)`, `∫V₁^{3/4} ≤ T^{1/4}(∫V₁)^{3/4}`) gives the **n-uniform GLOBAL** bound

   `Σ_i ∫_{I_i} ‖u^n t − u^n τ_i^n‖²_{L²(ℝ³)} dt ≤ C_mod(‖u₀‖, ν, T) · √δ`.

   Ball restriction is 1-Lipschitz, so the same bound holds in `L²(B_k)`.

5. **(Assembly.)**  Steps 3+4 make the curve family uniformly approximable by a compact set for
   every ε (choose `m` with `C_mod·√(T/m) < ε²`), hence totally bounded in
   `Lp (L2ballR3 k) 2 μ_T` (transfer lemma).  `Lp` is complete, so the closure is compact;
   `IsCompact.tendsto_subseq` on the sequence `n ↦ toLp (t ↦ restrictToBall k (u^{ψ n} t))`
   yields `ρ` StrictMono and a limit `G : Lp (L2ballR3 k) 2 μ_T`; set `g_k := ⇑G`
   (`Lp.aestronglyMeasurable` ✓) and convert `‖·‖`-convergence to the axiom's `eLpNorm → 0`.

**Guardrail-4 compliance.**  No pointwise-in-time strong modulus is ever asserted; step 4 is the
*integrated* modulus, derived purely from ODE pairings against V_n vectors with constants built
from `energy_bound`/`reg_bound` and the absolute GNS constant.  No finite-dim norm-equivalence
constant appears anywhere.  Refine-capability is automatic: the extraction is performed on the
sequence indexed through the given `ψ` (all bounds are `∀ n`).

**`GalerkinSolutionData_R3` fields consumed** (and by which lemma):
`u_hasDeriv` (FTC identities, curve continuity), `u_ode` (energy identity + pairing FTC),
`u_inVn` (test admissibility of `u τ` and Schwartz representation), `reg_mem` (H¹ of samples,
weighted-Fourier CS), `viscous_curve_continuous` (continuity of `σ ↦ V₁(u σ)` and of the
stokes/b integrands; good-sample mean value), `energy_bound` (+ `𝔊.norm_le`: `‖u t‖ ≤ ‖u₀‖`),
`reg_bound` (all integrated V-bounds).  Scheme/forms fields: `𝔊.range_schwartz`,
`F.b_galerkin`, `F.b_antisymm`, `F.b_add_*`/`b_smul_*` (multilinearity for the continuity
lemma).  `F.b_bound` (Schwartz-test, n-dependent constant) is deliberately **not** used.

---

## 2 File layout (new files; dependency order; import-cycle safe)

All new files sit strictly upstream of `ArzelaAscoliTime.lean` (which imports
`R3/AxiomaticClosure`, `R3/SpatialCompactness`, `R3/DivergenceFree`; `AxiomaticClosure`
transitively provides `FrechetKolmogorov`/`RellichBall`, hence `frechetKolmogorov_holds` and
`localRellichInput_of_frechetKolmogorov`).  None of them imports `ArzelaAscoliTime`,
`AubinLionsLimitPassage`, `ConvectionForm`, or any torus file.

| # | Module | Imports | Content |
|---|--------|---------|---------|
| A | `LerayHopf/Bochner/StepFunctionCompactness.lean` | mathlib only | generic step-curve compactness in `Lp X 2 (volume.restrict (Icc 0 T))`, totally-bounded transfer, sequential eLpNorm extraction |
| B | `LerayHopf/R3/GalerkinCurveBounds.lean` | `R3.AxiomaticClosure`, `R3.FourierL2`, `R3.RellichBall` | curve continuity, `‖u t‖ ≤ ‖u₀‖`, wFC linearity + `V₁` along the curve, stokes Cauchy–Schwarz, energy identity, pairing FTC, Schwartz representation of states |
| C | `LerayHopf/R3/GalerkinTrilinearBound.lean` | B, `R3.TrilinearEstimate`, `R3.SobolevEmbedding` | quantitative ∇-Plancherel and L⁶/L³ bounds for Schwartz-represented fields; energy-norm trilinear bound; `F.b` pin bridge; continuity of the b-integrand along the curve |
| D | `LerayHopf/R3/GalerkinTimeModulus.lean` | B, C | good-sample existence; per-cell error estimate; master uniform sampling-error bound |
| E | `LerayHopf/R3/SpacetimePrecompact.lean` | A, D, `R3.SpatialCompactness`, `R3.FrechetKolmogorov` (via AxiomaticClosure) | `galerkin_spacetime_precompact_of_goodSampling` — identical statement to the axiom, fully proved |
| — | `LerayHopf/R3/ArzelaAscoliTime.lean` (edit) | + `R3.SpacetimePrecompact` | `axiom` → `theorem … := galerkin_spacetime_precompact_of_goodSampling …`; header assumptions section updated |

Fresh-build note (constraint 1): B intentionally re-derives, as **new public lemmas with new
names**, facts whose only existing versions are `private` in `AubinLionsLimitPassage.lean`
(`galerkin_curve_continuous`, `galerkin_norm_le_u0`, `viscousFormSq_curve_continuousOn`) or
`private` in `SobolevEmbedding.lean`/`EnergyClassConvection.lean` (derivative-Fourier Plancherel,
quantitative L³ interpolation).  No existing declaration is moved, renamed, or edited.

---

## 3 Ordered task list

Notation: `V₁ v := viscousFormSq_R3 1 v`, `V_ν v := viscousFormSq_R3 ν v`,
`μ_T := volume.restrict (Set.Icc (0:ℝ) T)`, `E₀ := (1/2)·‖(u₀ : L2VF_R3)‖^2`,
`gs := galSeq n`.  Roles: **coder** = lean-coder writes file + statements (marked
`-- ALLOW_SORRY: <task id>` bodies where indicated), **prover** = lean-prover fills bodies.
"must-prove" = sorry-free before its PR merges; nothing in this plan is scaffold-only at
merge time except transient intra-PR states.

### File A — `Bochner/StepFunctionCompactness.lean`  (generic over `X` a complete NormedAddCommGroup)

- **A1** `stepCurve` (def, coder):
  `def stepCurve (T : ℝ) (m : ℕ) (y : Fin m → X) : ℝ → X :=`
  piecewise constant: value `y ⟨min ⌊t·m/T⌋₊ (m−1), _⟩` on `[i·T/m, (i+1)·T/m)`
  (implementation freedom: any explicit formula measurably equal to it).
- **A2** `stepCurve_memLp` (must-prove, prover):
  `MemLp (stepCurve T m y) 2 μ_T` for `0 < T`, `0 < m` (finitely many values, finite measure).
- **A3** `stepCurve_sub_memLp` / plumbing: differences and `eLpNorm` of differences of a
  `MemLp` curve and a step curve (small, prover).
- **A4** `isCompact_stepCurve_toLp` (must-prove, prover):
  for `K : Set X` compact, `IsCompact ((fun y => (stepCurve_memLp …).toLp) '' {y | ∀ i, y i ∈ K})`
  in `Lp X 2 μ_T`.  Route: `y ↦ toLp (stepCurve T m y)` is Lipschitz from `(Fin m → X)`
  (sup metric) — `‖stepCurve y − stepCurve y'‖_{L²} ≤ √T · max_i ‖y i − y' i‖` — and
  `{y | ∀ i, y i ∈ K}` is compact (`isCompact_pi_infinite` / `IsCompact.pi`).
- **A5** `totallyBounded_of_uniform_approx'` (must-prove, prover; ~15-line fresh copy of the
  public FK lemma so File A stays mathlib-only — alternatively import
  `R3.FrechetKolmogorov` and reuse `totallyBounded_of_uniform_approx`; coder decides, note in
  PR which):
  a set uniformly ε-approximable by totally bounded sets is totally bounded.
- **A6** `exists_subseq_tendsto_eLpNorm_of_totallyBounded` (must-prove, prover):
  if `f : ℕ → ℝ → X` with `hf : ∀ n, MemLp (f n) 2 μ_T` and
  `TotallyBounded (Set.range (fun n => (hf n).toLp))`, then
  `∃ (ρ : ℕ → ℕ) (G : Lp X 2 μ_T), StrictMono ρ ∧
     Tendsto (fun j => eLpNorm (fun t => f (ρ j) t - G t) 2 μ_T) atTop (nhds 0)`.
  Route: closure compact (complete space + `TotallyBounded.closure`), `IsCompact.tendsto_subseq`,
  then `Lp.norm_def` + eLpNorm-congruence (`(hf n).coeFn_toLp`, `Lp.coeFn_sub`) + ENNReal↔ℝ
  conversion (`ENNReal.tendsto_toReal_iff`-style; all eLpNorms finite).

Dependency edges: A1→A2→A3,A4; A5,A6 independent of A1–A4.

### File B — `R3/GalerkinCurveBounds.lean`

- **B1** `galerkinCurve_continuousOn` (must-prove, prover):
  `ContinuousOn (fun t => (gs.u t : L2VF_R3)) (Set.Ici 0)` (from `u_hasDeriv`; fresh public
  mirror of the private downstream lemma).
- **B2** `galerkinCurve_norm_le_u0` (must-prove, prover):
  `∀ t, 0 ≤ t → ‖(gs.u t : L2VF_R3)‖ ≤ ‖(u₀ : L2VF_R3)‖` (energy_bound + `𝔊.norm_le`;
  the computation already appears inline in `ArzelaAscoliTime.lean` section (H) — re-derive).
- **B3** `weightedFourierComponent_sub` (must-prove, prover):
  linearity on differences: for `hu : memH1VF_R3 u`, `hv : memH1VF_R3 v`,
  `huv : memH1VF_R3 (u − v)` (memH1 is closed under sub via `memH1VF_R3_add/smul`,
  `EnergyClassConvection.lean` public),
  `weightedFourierComponent (u−v) huv j = weightedFourierComponent u hu j − weightedFourierComponent v hv j`
  (`Lp.ext` on the defining a.e. representative).
- **B4** `viscousFormSq_eq_sum_normSq_wFC` (must-prove, prover):
  `V₁ u = ∑ j, ‖weightedFourierComponent u hu j‖^2` for `hu : memH1VF_R3 u`
  (this is `norm_weightedFourierComponent_sq` summed; check whether it is already public in
  `WeightedFourierCommute`/`FourierL2` — if so, cite instead of proving).
- **B5** `galerkin_viscous_curve_continuousOn` (must-prove, prover):
  `ContinuousOn (fun s => V₁ (gs.u s : L2VF_R3)) (Set.Ici 0)` from `viscous_curve_continuous`
  + B4.
- **B6** `galerkin_curve_H1_continuousOn` (must-prove, prover):
  `ContinuousOn (fun s => weightedFourierComponent (gs.u s) (gs.reg_mem s) j) (Ici 0)` is the
  field itself; derive `s ↦ V₁ (gs.u s − gs.u s₀) → 0` as `s → s₀` (via B3, B4) — the
  H¹-continuity used by C6.
- **B7** `stokesTestPairing_abs_le` (must-prove, prover; **Codex review the statement**):
  `∀ u w, memH1VF_R3 u → memH1VF_R3 w → |stokesTestPairing_R3 u w| ≤ Real.sqrt (V₁ u) * Real.sqrt (V₁ w)`.
  Route: `stokesTestPairing_R3` is `∑_j ∫ (2π)²‖ξ‖² Re[𝓕u_j · conj (𝓕w_j)]`
  (`Regularity.lean:123`); componentwise Cauchy–Schwarz on the weighted L² integrands
  (integrability from `integrable_viscous_integrand_of_memH1`, `RellichBall`/`FrechetKolmogorov`
  public), then `Σ a_j b_j ≤ √(Σa_j²)·√(Σb_j²)`.
- **B8** `galerkin_energy_identity` (must-prove, prover):
  `∀ a b, 0 ≤ a → a ≤ b →
    (1/2)*‖(gs.u b : L2VF_R3)‖^2 − (1/2)*‖(gs.u a : L2VF_R3)‖^2
      = − ∫ σ in a..b, V_ν (gs.u σ : L2VF_R3)`.
  Route: `HasDerivAt (fun σ => (1/2)*‖u σ‖²) (⟪u' σ, u σ⟫) σ` (inner-product calculus on
  `u_hasDeriv`), ODE at `w := gs.u σ` (admissible by `u_inVn`), `F.b_self_zero`, then
  `intervalIntegral.integral_eq_sub_of_hasDerivAt` with the continuous derivative
  `σ ↦ −V_ν(u σ)` (B5).
- **B9** `galerkin_pairing_FTC` (must-prove, prover; **Codex review the statement**):
  for `w : L2Sigma_R3` with `(w : L2VF_R3) = 𝔊.P n (w : L2VF_R3)`, and `0 ≤ a ≤ b`:
  `⟪(gs.u b : L2VF_R3) − gs.u a, (w : L2VF_R3)⟫_ℝ
     = ∫ σ in a..b, (−ν * stokesTestPairing_R3 (gs.u σ : L2VF_R3) w − F.b (gs.u σ) (gs.u σ) w)`.
  Route: scalar FTC on `g σ := ⟪u σ, w⟫` with `g' σ` given by the ODE; interval-integrability
  of the RHS from continuity: stokes term continuous by `viscous_curve_continuous` + B7-style
  bilinear expansion (stokes = Σ⟪wFC u j, wFC w j⟫ up to the weight split — a small helper
  `stokesTestPairing_eq_sum_inner_wFC`), b term continuous by C6 (so B9's *proof* is finished
  in the File-C PR; coder may land B9 with `-- ALLOW_SORRY: needs C6` inside the File-B PR only
  if the PR ordering in §5 is changed — default: B9 lands in PR-2 with the b-continuity
  argument imported from C6, i.e. B9 moves to File C. Decision left to coder; keep the name).
- **B10** `galerkinState_schwartzRep` (must-prove, prover; plumbing):
  `∃ ψ : Fin 3 → SchwartzMap Domain3 ℝ, ∀ j, L2VF_projComponent_R3 j (gs.u t : L2VF_R3) = (ψ j).toLp 2 volume`
  (from `𝔊.range_schwartz` at `𝔊.P n (gs.u t)` + `u_inVn`).

Dependency edges: B3,B4→B5,B6; B5→B8; B6,B7,(C6)→B9; B1,B2 independent.

### File C — `R3/GalerkinTrilinearBound.lean`

- **C1** `sum_gradSq_eq_viscousFormSq_of_schwartzRep` (must-prove, prover; **mathlib-gap risk R1**):
  for `v : L2VF_R3` with Schwartz representatives `ψ` (as in B10),
  `∑ i, ∑ a, ‖(∂_{e_a} (ψ i)).toLp 2 volume‖^2 = V₁ v`
  (derivative-Fourier Plancherel `‖∂_a ψ‖² = ∫ (2π)² ξ_a² ‖𝓕ψ‖²` per component, summed over
  `a`; template: `normSq_lineDeriv_toLp`, private in `SobolevEmbedding.lean:243` — rebuild
  fresh).  An `≤` version suffices for everything downstream; state the `≤` form if the
  equality fights.
- **C2** `eLpNorm_six_le_of_schwartzRep` (must-prove, prover):
  `∃ C₆ ≥ 0` absolute:
  `eLpNorm ((ψ i) : Domain3 → ℝ) 6 volume ≤ ENNReal.ofReal (C₆ * Real.sqrt (V₁ v))` per
  component.  Route: `gns_L6_schwartz` (public; complex-valued — apply to `cxify (ψ i)` or the
  ℝ-valued variant, whichever typechecks; `gns_L6_cc1_R3` is the fallback) + bridging
  `eLpNorm (fderiv φ) 2` to `Σ_a ‖∂_a φ‖²` (template: `eLpNorm_fderiv_le_sum_lineDeriv`,
  private in `EnergyClassConvection.lean:1174` — rebuild fresh) + C1.
- **C3** `eLpNorm_three_le_interp_pub` (must-prove, prover):
  fresh public copy of the private `eLpNorm_three_le_interp`
  (`EnergyClassConvection.lean:510`): `eLpNorm f 3 ≤ (eLpNorm f 2)^{1/2} · (eLpNorm f 6)^{1/2}`.
- **C4** `convIntegralSchwartz_bound_energy` (must-prove, prover; **Codex review the statement**):
  `∃ C_b ≥ 0` absolute: for all Schwartz triples `ψu ψv ψw` representing
  `u v w : L2VF_R3` (componentwise `toLp` equalities),
  `|convIntegralSchwartz ψu ψv ψw|
     ≤ C_b * ‖u‖^(1/2:ℝ) * (V₁ u)^(1/4:ℝ) * Real.sqrt (V₁ v) * Real.sqrt (V₁ w)`.
  Route: per-(i,a) Hölder with exponents (3,2,6) on `∫ u_a (∂_a v_i) w_i`
  (`ENNReal.HolderTriple` iteration as in `EnergyClassConvection`), then
  `‖u_a‖₃ ≤ ‖u_a‖₂^{1/2}‖u_a‖₆^{1/2}` (C3), `‖u_a‖₆, ‖w_i‖₆ ≤ C₆√V₁` (C2),
  `‖∂_a v_i‖₂ ≤ √V₁ v` (C1), finite-sum aggregation (pattern of
  `convIntegralSchwartz_bound_H1`).
- **C5** `bForm_galerkin_abs_le` (must-prove, prover; **Codex review the statement** —
  n-uniformity of the constant is the load-bearing claim):
  `∃ C_b ≥ 0` absolute (same as C4): for Galerkin states `u v : L2Sigma_R3` of any level `n`
  (i.e. `(u:L2VF_R3) = 𝔊.P n u`, same for `v`, `w`),
  `|F.b u v w| ≤ C_b * ‖(u:L2VF_R3)‖^(1/2:ℝ) * (V₁ u)^(1/4:ℝ) * √(V₁ v) * √(V₁ w)`.
  Route: B10 representations + `F.b_galerkin` pin + C4.
- **C6** `galerkin_bForm_curve_continuousOn` (must-prove, prover):
  for fixed level-`n` test `w`, `ContinuousOn (fun σ => F.b (gs.u σ) (gs.u σ) w) (Set.Ici 0)`.
  Route: multilinearity (`b_add_*`) splits the difference into two terms controlled by C5
  applied with one slot `= gs.u σ − gs.u σ₀` (still level-`n`), then B6 (H¹-continuity of the
  curve) kills them.  (Only needed as *interval-integrability* input to B9; if C5's fractional
  powers make the ε-δ tedious, the weaker `IntervalIntegrable` statement on `[a,b] ⊆ Ici 0`
  is an acceptable substitute — keep the name honest, e.g.
  `galerkin_bForm_intervalIntegrable`.)

Dependency edges: C1→C2→C4; C3→C4→C5→C6; B10→C5; B6→C6.

### File D — `R3/GalerkinTimeModulus.lean`

- **D1** `exists_goodSample` (must-prove, prover; generic):
  `f` continuous nonneg on `[a,b]`, `a < b` ⇒ `∃ τ ∈ Icc a b, f τ ≤ (b−a)⁻¹ * ∫ σ in a..b, f σ`
  (min ≤ average on a compact interval).
- **D2** `galerkin_cell_error_bound` (must-prove, prover):
  for a cell `[a, a+δ] ⊆ [0,T]`, `0 < δ`, and `τ ∈ [a, a+δ]` with
  `V₁ (gs.u τ) ≤ δ⁻¹ ν⁻¹ E₀·2` (shape as delivered by D1 + reg_bound; exact constant free):
  `∫ t in a..(a+δ), ‖(gs.u t : L2VF_R3) − gs.u τ‖^2
     ≤ 2*δ*(∫ σ in a..(a+δ), V_ν (gs.u σ))
       + 2*δ*Real.sqrt (δ⁻¹*ν⁻¹*E₀) *
           ∫ σ in a..(a+δ), (ν * Real.sqrt (V₁ (gs.u σ))
                              + C_b * ‖(u₀:L2VF_R3)‖^(1/2:ℝ) * (V₁ (gs.u σ))^(3/4:ℝ))`
  (exact algebraic shape at coder's discretion; the *content* is: cell L²-error ≤
  energy part + pairing part, each expressed through cell integrals of `V` powers with the
  good-sample factor `√(δ⁻¹ν⁻¹E₀)` and n-free constants).  Consumes B2, B5, B7, B8, B9, C5.
- **D3** `galerkin_sampling_error_bound` (MASTER, must-prove, prover; **Codex review the
  statement first** — check: integrated not pointwise, constants n-free, mesh fixed):
  `∃ C_mod ≥ 0` (function of `‖u₀‖, ν, T, C_b` only): for all `n`, all `m : ℕ`, `0 < m`, with
  `δ := T/m`, **there exist** sample times `τ : Fin m → ℝ`, `τ i ∈ Icc (i*δ) ((i+1)*δ)`, with
  `V₁ (gs.u (τ i)) ≤ 2*δ⁻¹*ν⁻¹*E₀` for all `i`, and
  `∑ i, ∫ t in (i*δ)..((i+1)*δ), ‖(gs.u t : L2VF_R3) − gs.u (τ i)‖^2 ≤ C_mod * Real.sqrt δ`.
  Route: D1 per cell (choice per `(n,i)` is classical, no measurability needed), D2 per cell,
  sum with `intervalIntegral.sum_integral_adjacent_intervals`, time-Hölder
  `∫₀ᵀ √V₁ ≤ √T·√(∫V₁)` and `∫₀ᵀ V₁^{3/4} ≤ T^{1/4}·(∫V₁)^{3/4}` (from reg_bound, ν-scaled).

Dependency edges: D1→D3; B*, C5→D2→D3.

### File E — `R3/SpacetimePrecompact.lean` + the conversion

- **E1** `restrictToBall_comp_curve_memLp` (must-prove, prover):
  `MemLp (fun t => restrictToBall k ((gs.u t : L2VF_R3))) 2 μ_T`
  (continuous on `Icc 0 T` via B1 + 1-Lipschitz restriction — fresh copies of
  `norm_restrictToBall_sub_le`/`continuous_restrictToBall'` are NOT needed if the
  `ArzelaAscoliTime` privates are unavailable: re-derive the 1-Lipschitz bound locally,
  ~20 lines, or check for a public equivalent in `SpatialCompactness`/`FrechetKolmogorov`
  (`restrictToBall_dist_le` exists but is private downstream)).
- **E2** `galerkin_spacetime_precompact_of_goodSampling` (must-prove, prover;
  **Codex review before proof**): statement **identical, binder-for-binder, to the axiom**
  (only the name differs).  Proof assembly:
  1. Fix `ψ, k`.  Family `f n := fun t => restrictToBall k ((galSeq (ψ n)).u t)`, `MemLp` by E1.
  2. `TotallyBounded (Set.range (fun n => (E1 …).toLp))`: given `ε`, pick `m` with
     `C_mod·√(T/m) < (ε/2)²`-scaled appropriately; D3 gives samples; per-slice
     `restrictToBall k ((galSeq (ψ n)).u (τ i)) ∈ K` with
     `K := (localRellichInput_of_frechetKolmogorov frechetKolmogorov_holds).ballCompact M_δ k`
     (membership needs: `∈ L2Sigma_R3` ✓, `memH1VF_R3` ✓ `reg_mem`, `‖·‖ ≤ M_δ` ✓ B2,
     `V₁ ≤ M_δ²` ✓ D3's sample bound); step curve within `ε/2` of `f n` in `Lp` (D3 +
     1-Lipschitz restriction + A3); step-curve set compact (A4) hence totally bounded;
     transfer (A5).
  3. Extraction A6 → `ρ, G`; `g_k := ⇑G`; `Lp.aestronglyMeasurable G`; eLpNorm convergence
     as in A6's conclusion.  Done.
- **E3** conversion in `ArzelaAscoliTime.lean` (coder; **Codex review the diff**):
  `axiom galerkin_spacetime_precompact_R3 …` →
  `theorem galerkin_spacetime_precompact_R3 … := galerkin_spacetime_precompact_of_goodSampling …`
  with the statement byte-identical; add `import LerayHopf.R3.SpacetimePrecompact`; update the
  file-header "Assumptions" section (now: zero axioms introduced by this file) and the
  docstring (drop `ALLOW_AXIOM`, record the discharge).  Run the full preflight; verify
  downstream (`AubinLionsLimitPassage`, capstones) rebuild **without any edit**.

Dependency edges: A6,A4,A5 + D3 + E1 → E2 → E3.

---

## 4 Risk register

| # | Risk | Likelihood | Mitigation / fallback |
|---|------|-----------|----------------------|
| R1 | **C1 derivative-Fourier Plancherel** for Schwartz maps not directly public (`𝓕(∂_a φ) = 2πi ξ_a 𝓕φ` + Plancherel). | Medium | Templates exist twice in-repo (`normSq_lineDeriv_toLp` in SobolevEmbedding, the wFC machinery in WeightedFourierCommute/FourierL2 — both proved). Rebuild fresh (~60–100 lines). Fallback: state C1 as `≤` against `V₁` only, which is all C2/C4 need. |
| R2 | **C2 constant extraction from `gns_L6_schwartz`** (ENNReal constant `SNormLESNormFDerivOfEqConst`, ℝ↔ℝ≥0∞ juggling). | Medium | The constant is a fixed term; keep the bound in `ENNReal` as long as possible and `toReal` once. Fallback: `gns_L6_cc1_R3` + the cutoff machinery (all in SobolevEmbedding, cutoff lemmas private → rebuild) — strictly worse; prefer primary. |
| R3 | **C6 continuity of the b-integrand** (needed only for interval-integrability in B9): ε-δ with fractional powers is fiddly. | Medium | Weaken target to `IntervalIntegrable` (rename honestly). Second fallback: measurability of the scalar derivative via `Measurable.deriv`-style lemmas + domination by the continuous bound from C5 (`IntervalIntegrable.mono_fun`-pattern). |
| R4 | **Three-factor Hölder (3,2,6)** in C4: mathlib API is two-factor (`MemLp.mul` with `HolderTriple`). | Low | Iterate exactly as `EnergyClassConvection.lean:477` does (proved pattern in-repo: `6·2→3/2` etc.); the (3,2,6) split is `3·6→2`-then-`2·2→1`. |
| R5 | **A4 compactness of the step set**: product-compactness + continuity of assembly. | Low | Assembly map is Lipschitz linear from `Fin m → X`; `IsCompact.image` closes it. Fallback: skip compactness, prove `TotallyBounded` of the step set directly from a finite ε-net of `K` (finite mesh × finite net = finite family). |
| R6 | **ENNReal/rpow bookkeeping** in D2/D3 (√δ, δ^{1/4}, `Real.sqrt` vs `rpow`). | Medium (time sink, not blocker) | Keep everything in ℝ with `Real.sqrt`/`^(3/4:ℝ)`; convert to `eLpNorm` only in E2. State D3 in plain-integral form (as written) precisely to avoid ENNReal inside the analytic core. |
| R7 | **B9 FTC hypotheses** (`intervalIntegral.integral_eq_sub_of_hasDerivAt` wants HasDerivAt on `uIcc` + IntervalIntegrable of the derivative; endpoint `a = 0` uses the full two-sided `u_hasDeriv` at `0` — available, the field is stated as full `HasDerivAt` at every `t ≥ 0`). | Low | Field already two-sided; no `derivWithin` needed. |
| R8 | Hidden coupling: some lemma needed here exists only `private` downstream and a reviewer flags duplication. | Certain (by design) | Constraint 1 mandates fresh builds; every duplicate is a NEW name in a NEW upstream file, with a docstring pointing at the downstream private original. Record in each PR report. |

Overall size estimate: ~1,900–2,300 new lines across five files.  No new axiom, no statement
weakening, net project-axiom count −1.

---

## 5 Milestone slicing (each chunk: `lake build` green, axiom count non-increasing)

**PR-1 (Files A + B).**  Generic Bochner step-curve compactness + Galerkin curve/pairing
library.  Sorry-free at merge (B9 may move to PR-2 if the C6 dependency is kept — coder
decides and records; no `sorry` merges either way).  Axiom untouched.
*Codex gates:* B7, B9 statements.

**PR-2 (File C).**  Energy-norm trilinear bound chain (C1–C6) + B9 if deferred.
Sorry-free.  Axiom untouched.
*Codex gates:* C4, C5 statements (n-uniform constant is the critical claim).

**PR-3 (File D).**  Good sampling + master uniform sampling-error bound.  Sorry-free.
Axiom untouched.
*Codex gates:* D3 statement (integrated-only modulus; no pointwise claim; constants n-free).

**PR-4 (File E + conversion).**  Assembly theorem + `axiom` → `theorem` swap in
`ArzelaAscoliTime.lean`.  Axiom count −1.
*Codex gates:* E2 statement (verbatim-match check against the axiom), E3 diff (byte-identity
of the statement, no downstream edits).

Conflict safety: none of PR-1..4 touches `AubinLionsLimitPassage.lean`, `ConvectionForm.lean`,
or torus files; PR-4 touches only `ArzelaAscoliTime.lean` (a file no in-flight PR edits) plus
new files.  If PR #69 lands meanwhile, no rebase conflicts are expected beyond the lakefile /
root-import wiring (new files must be reachable from the root `LerayHopf.lean` per repo
convention — coder checks how existing `R3/*` files are wired and mirrors it).

---

## 6 Definition of done

- `LerayHopf/R3/ArzelaAscoliTime.lean` contains `theorem galerkin_spacetime_precompact_R3`
  with the byte-identical statement; the string `axiom galerkin_spacetime_precompact_R3` no
  longer occurs in the codebase.
- Zero new `axiom`/`opaque`/`constant`; zero unmarked `sorry`; all five new files sorry-free.
- All downstream consumers compile **unchanged** (`perBall_ae_subseq`, `diag_ae_subseq`,
  `u_lim_aestronglyMeasurable`, `galerkinSpaceTimeExtraction_R3`,
  `aubinLionsPackage_R3_of_timeCompactness`, capstones).
- `bash scripts/agent-preflight.sh` green; PR reports list files/decls/sorries/axioms per
  AGENTS.md.

## 7 Blocking questions for the owner (before coding starts)

1. **Duplication budget:** constraint 1 forces fresh upstream rebuilds of ~4 small lemma
   groups whose only current versions are `private` downstream (curve continuity, viscous
   curve continuity, 1-Lipschitz restriction, L³ interpolation, ∇-Plancherel).  Confirm this
   is acceptable vs. waiting for PR #69 to land and then de-privatizing (the plan assumes
   fresh rebuild NOW; a later dedup pass can consolidate).
2. **Constant policy:** C2/C4/C5/D3 are stated in `∃ C ≥ 0` form (constants not named
   globally).  Confirm, or request named `noncomputable def` constants.
3. **File-A genericity:** `Bochner/StepFunctionCompactness.lean` is stated over a generic
   complete `NormedAddCommGroup X` for torus-#23 reuse.  Confirm the `LerayHopf/Bochner/`
   placement (it imports mathlib only).
