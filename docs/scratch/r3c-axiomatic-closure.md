# R3-c — ℝ³ axiomatic closure (design contract)

Port of the **Codex-approved** T³ `LerayHopf/AxiomaticClosure.lean` to ℝ³ types, reusing the
abstract `DissipativeEvolution`/`WeakFormNS`/`AbstractEnergyLaw` verbatim. The T³ 8-round audit
lessons are baked in PREEMPTIVELY. New file `LerayHopf/R3/AxiomaticClosure.lean`.

## ℝ³ types already built (axiom-free, R3-a/R3-b)
`L2VF_R3`, `L2C_R3`, `L2VF_projComponent(C)_R3 j`, `L2Sigma_R3` (closed div-free subspace),
`lerayProjection_R3`, `memH1VF_R3` (via `MemSobolev`), `IsSchwartzDivFree_R3`,
`stokesTestPairing_R3` (= ∫∇u:∇w, Fourier integral), `viscousFormSq_R3 ν` (= ν‖∇u‖², Fourier
integral) + `viscousFormSq_R3_nonneg`.

## Axioms (6) — the 2 extra vs T³ are exactly the two pieces T³ PROVED but ℝ³ cannot

### AX-G `r3GalerkinScheme` — the approximation-projection family (replaces T³'s PROVED `velocityProjection_n`)
On ℝ³ there is no finite-dim Fourier truncation (frequency balls are infinite-dim; the indicator
multiplier is not in mathlib). Bundle the approximation projector + its properties into ONE axiom:
```
structure R3GalerkinScheme where
  P : ℕ → (L2VF_R3 →L[ℝ] L2VF_R3)
  preserves_sigma : ∀ n u, u ∈ L2Sigma_R3 → P n u ∈ L2Sigma_R3
  tendsto_id : ∀ u, Filter.Tendsto (fun n => P n u) atTop (nhds u)
  norm_le : ∀ n u, ‖P n u‖ ≤ ‖u‖
  idem : ∀ n u, P n (P n u) = P n u
axiom r3GalerkinScheme_exists : Nonempty R3GalerkinScheme
  -- ALLOW_AXIOM: existence of a Galerkin approximation-projection family on L²_σ(ℝ³)
  -- (e.g. frequency-ball truncation / mollification); TRUE classically (Paley–Wiener);
  -- blocked in Lean by the missing indicator Fourier-multiplier on Lp. Lemarié-Rieusset §2.
```
Fix one `𝔊 : R3GalerkinScheme` (from the axiom) and use `𝔊.P n` everywhere below.
`IsGalerkinTest_R3 (𝔊) (w : L2Sigma_R3) := ∃ n, 𝔊.P n (w:L2VF_R3) = (w:L2VF_R3)`.
(Or keep tests = `IsSchwartzDivFree_R3` and use `𝔊.P` only for the ODE/approximation. Coder picks
the choice that makes the assembly typecheck; FLAG it.)

### AX-4 `r3_NSForms_exist` — the ℝ³ convection form (port of T³ A4)
`structure R3NSForms` with `b : L2Sigma_R3→L2Sigma_R3→L2Sigma_R3→ℝ`, `b_antisymm`, trilinearity
(`b_add_1/2/3`, `b_smul_1/2/3`), smooth-test bound
`b_bound : ∀ w, IsGalerkinTest_R3 𝔊 w → ∃ C, ∀ u v, |b u v w| ≤ C*‖(u:L2VF_R3)‖*‖(v:L2VF_R3)‖`,
and the **non-vacuity pin** `b_galerkin` to a concrete `galerkinConvection_R3` on test fields.
`axiom r3_NSForms_exist : Nonempty R3NSForms` (ALLOW_AXIOM: genuine ∫(u·∇)v·w witnesses; b=0 excluded
by b_galerkin; Temam II.§1; Lemarié-Rieusset §5). `b_self_zero` proved from antisymmetry.

**`galerkinConvection_R3` (non-vacuity pin) — concrete; CODER attempts, fallback flagged.**
Target: the genuine convection integral on Schwartz fields, `∑_{i,a} ∫ u_a (∂_a v_i) w_i`, via the
`IsSchwartzDivFree_R3` witnesses + `lineDerivOpCLM` (∂_a) + pointwise product + integral; OR the
Fourier double-integral analogue of T³ `galerkinConvection`. If both are a quagmire, fall back to a
single explicit nonzero calibration (one Schwartz triple with a hand-checkable nonzero value) to
exclude b=0, and FLAG for the Codex non-vacuity audit. (Viscous form is CONCRETE `stokesTestPairing_R3`
— NOT axiomatized; lesson from T³ v4.)

### AX-1 `galerkin_ode_solution_R3` — port of T³ A1 (with `𝔊.P n` for `velocityProjection_n`)
`structure GalerkinSolutionData_R3 (𝔊)(F)(ν)(u₀)(n)`: `u : Time→L2Sigma_R3`; `u_initial`
(`u 0 = 𝔊.P n u₀`-corestricted, via `preserves_sigma`); `u_inVn` (`(u t)=𝔊.P n (u t)`);
`u_hasDeriv`; `u_ode` (tested against `w` with `𝔊.P n w = w`, using `stokesTestPairing_R3`+`F.b`);
`reg_mem : ∀ t, memH1VF_R3 (u t)`; uniform `energy_bound`; n-indep `reg_bound`
(`∫₀ᵀ viscousFormSq_R3 ν (u t) ≤ honest n-indep RHS`). `axiom galerkin_ode_solution_R3 … : GalerkinSolutionData_R3 …` (Temam III.3).

### AX-SC `spatial_compactness_R3` — THE structurally-new ℝ³ axiom (replaces PROVED `rellich_L2Sigma`)
Rellich FAILS on ℝ³ ⇒ this is a genuine axiom, and it MUST carry the L²+tightness hypothesis (the H¹
bound ALONE is insufficient — mass can escape to infinity). State as a hypothesis-shape that the
assembly can supply:
```
axiom spatial_compactness_R3 :
  ∀ (M : ℝ) (z : ℕ → L2VF_R3),
    (∀ n, z n ∈ L2Sigma_R3) → (∀ n, memH1VF_R3 (z n)) →
    (∀ n, ‖z n‖ ≤ M) →                                   -- uniform L² bound
    (∀ n, viscousFormSq_R3 1 (z n) ≤ M^2) →              -- uniform H¹ (gradient) bound
    (∀ ε > 0, ∃ R : ℝ, ∀ n, ∫ x in {x : Domain3 | R < ‖x‖}, ‖(z n) x‖^2 ∂volume ≤ ε) →  -- TIGHTNESS
    ∃ (ψ : ℕ → ℕ) (g : L2VF_R3), StrictMono ψ ∧ g ∈ L2Sigma_R3 ∧
      Filter.Tendsto (fun n => z (ψ n)) atTop (nhds g)
  -- ALLOW_AXIOM: ℝ³ spatial compactness = local Rellich (H¹_loc↪L²_loc compact) + tightness;
  -- Rellich FAILS globally on ℝ³, so the tightness hypothesis is REQUIRED (the H¹ bound alone is
  -- insufficient — this is the whole point). TRUE; blocked by local Rellich + real-space ball
  -- integrals not in mathlib. Leray 1934; Lemarié-Rieusset §6.3.
```

### AX-2 `aubin_lions_R3` — port of T³ A2, but spatial half is the AXIOM `spatial_compactness_R3` (NOT discharged)
`structure AubinLionsPackage_R3 (𝔊)(F)(ν T)(u₀)(galSeq)` (parameterized by galSeq, `strong_convergence`
= `∫₀ᵀ‖galSeq(φ n).u t - u t‖²→0`). `axiom aubin_lions_R3 … (galSeq) (spatial : <shape of spatial_compactness_R3, incl. tightness>) : AubinLionsPackage_R3 …`. The assembly passes `spatial_compactness_R3`
AND must supply the tightness premise (from `u₀∈L²` + energy bound — itself axiom or proved; for now
the tightness is part of the `spatial` hypothesis the assembly discharges via `spatial_compactness_R3`).

### AX-3 `galerkin_limit_passage_R3` — port of T³ A3 (existential good representative, a.e.-linked)
`axiom galerkin_limit_passage_R3 … (galSeq) (alPkg) : ∃ u : Time→L2Sigma_R3, (∀ᵐ t ∂vol.restrict(Icc 0 T), u t = alPkg.u t) ∧ WeakFormNS ν T (r3Evolution 𝔊 F) u ∧ (∀ t, 0≤t→t≤T→ ½‖u t‖²+∫₀ᵗ viscousFormSq_R3 ν (u s) ≤ ½‖u₀‖²) ∧ Tendsto (u·) (𝓝[≥]0) (𝓝 u₀) ∧ ((∀ᵐ t…, memH1VF_R3 (u t)) ∧ IntervalIntegrable (viscousFormSq_R3 ν ∘ u) vol 0 T)` (Temam III.3).

## `r3Evolution` + proof-carrying spine + assembly (port T³)
`r3Evolution (𝔊)(F) : DissipativeEvolution := { H := L2Sigma_R3, reg := viscousFormSq_R3 1 ∘ coe,
viscousForm := stokesTestPairing_R3∘coe, convForm := F.b, convForm_antisymm := F.b_antisymm,
isTest := IsGalerkinTest_R3 𝔊 }`. Proof-carrying `LerayHopfSolutionFull_R3`/`GalerkinCompactnessPackageFull_R3`
(weak_eq, energy_ineq[0,T], initial_trace, energy_class). Assembly: `build_galerkin_package_R3`
(A1→A2[spatial_compactness_R3]→A3 obtain existential) → `exists_lerayHopf_from_package_full_R3` →
`exists_lerayHopf_r3 (u₀:L2Sigma_R3)(ν)(hν)(T)(hT) : ∃ F, Nonempty (LerayHopfSolutionFull_R3 𝔊 F ν T u₀)`.
(`𝔊` from `r3GalerkinScheme_exists`.) Assembly proofs = lean-prover (sorry-stubs for coder pass).

## Preemptive T³-audit lessons (must all hold)
multilinear forms (no off-diagonal inconsistency); smooth-test convection bound (Schwartz w);
non-vacuity pin (exclude b=0); A3 existential + a.e.-link; energy-class proof-carried; viscous form
concrete (no collapse vacuity); WeakFormNS reused (isTest-restricted, ν-scaled, open support);
**spatial_compactness_R3 carries the tightness hypothesis** (the ℝ³-specific soundness point).

## Codex R3-c audit v1 (needs-attention) — REQUIRED FIXES

**Fix 1 (critical — identity scheme): `R3GalerkinScheme` must exclude the identity.**
The current fields (idempotent contraction → id, preserves σ) admit `P = id`, which makes
`IsGalerkinTest_R3` = all of L²_σ ⟹ `b_bound` (smooth-test) and `reg_mem` (H¹) become FALSE.
Add a **range-regularity** field forcing the projector's range to be Schwartz div-free:
```
range_schwartz : ∀ n (u : L2VF_R3), ∃ (ψ : Fin 3 → SchwartzMap Domain3 ℝ),
  ∀ j, L2VF_projComponent_R3 j (P n u) = (ψ j).toLp 2 (volume : Measure Domain3)
```
(excludes identity since L²⊄Schwartz; ⟹ every `IsGalerkinTest_R3` field is Schwartz, so `b_bound`
applies and `reg_mem`/H¹ holds. `r3GalerkinScheme_exists` stays TRUE — smooth/Hermite Galerkin
bases exist.)

**Fix 2 (high — global vs LOCAL compactness): reformulate to L²_loc (no tightness).**
Global strong `L²(ℝ³)` convergence is FALSE on ℝ³ without tightness; but the genuine Leray
construction uses **local** compactness (local Rellich on balls — TRUE, no tightness) + decaying
(Schwartz) test functions. Reformulate:
- `spatial_compactness_R3`: drop the tightness premise; conclude **local** convergence:
  `… → ∃ ψ g, StrictMono ψ ∧ g ∈ L2Sigma_R3 ∧ ∀ R : ℝ, Filter.Tendsto (fun n => ∫ x in {x : Domain3 | ‖x‖ ≤ R}, ‖(z (ψ n)) x - g x‖^2 ∂volume) atTop (𝓝 0)`
  (hypotheses: `∀n, z n ∈ L2Sigma_R3`, `memH1VF_R3 (z n)`, `‖z n‖ ≤ M`, `viscousFormSq_R3 1 (z n) ≤ M^2`).
  TRUE by local Rellich `H¹(B_R)↪↪L²(B_R)`; no tightness. [Leray 1934; Lemarié-Rieusset §6]
- `AubinLionsPackage_R3.strong_convergence`: space-time LOCAL form
  `∀ R : ℝ, Filter.Tendsto (fun n => ∫ t in (0:ℝ)..T, ∫ x in {x | ‖x‖ ≤ R}, ‖((galSeq (φ n)).u t) x - (u t) x‖^2 ∂volume) atTop (𝓝 0)`.
- `aubin_lions_R3`'s `spatial` hypothesis = the (local) `spatial_compactness_R3` shape; assembly passes it.
- `galerkin_limit_passage_R3` (A3) consumes the LOCAL convergence (its conclusion shape unchanged —
  weak form passes via local convergence + Schwartz-test decay controlling the tail uniformly under the
  uniform H¹ bound).
This removes the tightness obligation entirely (Codex finding 2) and asserts only the TRUE local
compactness. Axiom count stays 6.

## `## Assumptions` section listing all 6 axioms + Temam/Leray/Lemarié-Rieusset refs.
