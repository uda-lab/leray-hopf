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
  `SolutionInterfaces.lean` + spine wiring + `LerayHopf.lean`/`STATUS.md`.

## Commit 1 — `H1Sigma.lean`

`import LerayHopf.Torus.VelocityGalerkin / SobolevTorus / RellichEmbedding`. In `namespace LerayHopf`:

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

`import LerayHopf.Torus.H1Sigma / EnergyEstimate` + interval-integral. The bundle carries ONLY
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

## Commit 2 — `SolutionInterfaces.lean` (the 4 axioms — Codex-audited BEFORE proving)

### A4 — convection + viscous forms. **NON-VACUITY IS THE CRUX.**
A bare abstract `b` with only antisymmetry + bound is satisfiable by `b := 0` ⇒ the theorem
would silently prove **Stokes/heat**, not Navier–Stokes (overclaim). And a naive INFINITE
Fourier triple sum is NOT absolutely summable for general 3D H¹ fields (the borderline
Ladyzhenskaya case) ⇒ `tsum` returns 0 ⇒ re-vacuous. The sound, bounded resolution is to pin
`b` to the genuine convection form on the **finite** Galerkin subspaces (finite sums; no
convergence issue; excludes `b=0`; honest on a dense set).

**Concrete convection structure constant (finite).** For `mFourier_k(x)=e^{2πi k·x}`, write
`û_a(k) := mFourierCoeff3 (L2VF_projComponentC a u) k : ℂ`. From `(u·∇)v_i = Σ_a u_a ∂_a v_i`,
`∂_a v_i ↦ (2πi l_a) v̂_i(l)`, and `∫_{𝕋³} e^{2πi(k+l+m)·x}=δ_{k+l+m=0}`:
`b(u,v,w) = Σ_i Σ_a Σ_{k,l} û_a(k)·(2πi l_a)·v̂_i(l)·ŵ_i(-(k+l))`.
Define the FINITE (box-`n`) version as a `def` (a `Finset.sum` over `fourierBox n × fourierBox n`,
take `.re`):
```
def galerkinConvection (n : ℕ) (u v w : L2VF) : ℝ :=
  (∑ i : Fin 3, ∑ a : Fin 3, ∑ k ∈ fourierBox n, ∑ l ∈ fourierBox n,
     (mFourierCoeff3 (L2VF_projComponentC a u) k)
       * (2 * (Real.pi : ℂ) * Complex.I * (l a : ℂ))
       * (mFourierCoeff3 (L2VF_projComponentC i v) l)
       * (mFourierCoeff3 (L2VF_projComponentC i w) (-(k + l)))).re
```
This is well-defined (finite), generically nonzero ⇒ excludes `b=0`.

**A4 as a structure + pinned existence axiom:**
```
structure Torus3NSForms where
  b : L2Sigma → L2Sigma → L2Sigma → ℝ
  b_antisymm : ∀ u v w, b u v w = - b u w v
  C_b : ℝ ; C_b_pos : 0 < C_b
  b_bound : ∀ u v w, memH1Sigma (u:L2VF) → memH1Sigma (v:L2VF) →
    |b u v w| ≤ C_b * Real.sqrt (h1EnergySq (u:L2VF)) * Real.sqrt (h1EnergySq (v:L2VF)) * ‖(w:L2VF)‖
  b_galerkin : ∀ (n : ℕ) (u v w : L2Sigma),               -- the non-vacuity PIN (dense set)
    velocityProjection_n n (u:L2VF) = (u:L2VF) → velocityProjection_n n (v:L2VF) = (v:L2VF) →
    velocityProjection_n n (w:L2VF) = (w:L2VF) →
    b u v w = galerkinConvection n (u:L2VF) (v:L2VF) (w:L2VF)
  stokes : L2Sigma → L2Sigma → ℝ
  stokes_nonneg : ∀ u, 0 ≤ stokes u u
  stokes_eq : ∀ u, stokes u u = viscousFormSq 1 (u:L2VF)     -- makes (2π)² load-bearing
axiom torus3_NSForms_exist : Nonempty Torus3NSForms
  -- ALLOW_AXIOM: existence of the 𝕋³ NS convection form (= galerkinConvection on trig
  -- polynomials, extended by the 3D continuity bound) with div-free antisymmetry, and the
  -- Stokes form; TRUE (the genuine convection form is a witness), NON-VACUOUS (b=0 fails
  -- b_galerkin since galerkinConvection ≢ 0). Blocked in Lean by the missing torus (u·∇)v
  -- operator + integration-by-parts. Temam II.§1; RRS §3.2.
```
`b u u u = 0` is the proved lemma (`b_antisymm`); antisymmetry is `b u v w = -b u w v`.
**FLAG for the Codex non-vacuity/truth audit:** (i) `galerkinConvection` is the correct
convection structure constant; (ii) `b_galerkin` genuinely excludes `b=0`; (iii)
`torus3_NSForms_exist` is TRUE (real convection form witnesses it); (iv) the 3D `b_bound` is
the true Ladyzhenskaya form; (v) `stokes_eq`/(2π)² correct. If `galerkinConvection` proves too
heavy to typecheck, fall back to a single hand-computed nonzero calibration triple and flag.

### A1 `galerkin_ode_solution` (per-`n`) — returns `GalerkinSolutionData F ν u₀ n` with:
`u : Time → L2Sigma`; `u 0 = Pₙu₀`; range in `Vₙ` (`(u t:L2VF)=velocityProjection_n n (u t)`);
the **projected ODE** tested against `Vₙ` (inner-product form with `F.stokes`, `F.b`);
`HasDerivAt` for `(u ·:L2VF)`; **`reg_mem : ∀ t, memH1VF (u t)`** (REQUIRED for Rellich, tsum
convention); uniform `energy_bound : ½‖u t‖² ≤ ½‖Pₙu₀‖²`; uniform **n-independent**
`reg_bound : ∫₀ᵀ h1EnergySq(u t) ≤ Cbnd` with an honest n-independent RHS (e.g.
`T*‖u₀‖² + ‖u₀‖²/(2ν)` — true since `h1EnergySq ≤ ‖·‖²_{L²} + viscousFormSq 1`, energy
monotone, `‖Pₙu₀‖≤‖u₀‖`; a generous larger RHS is fine and SAFER). Temam III.3.

### A2 ~~`aubin_lions`~~ — **(REMOVED 2026-07-04, #23 / PR #89 — now the proved def `torusAubinLionsPackage_of_galSeq` via mode-wise spectral route; this row is historical)**
~~Aubin–Lions, **spatial half discharged not axiomatized**.
Takes the Galerkin sequence + its uniform energy/reg bounds + an explicit **spatial-compactness
hypothesis whose statement is exactly `rellich_L2Sigma`'s** (the assembly passes
`rellich_L2Sigma`), and produces `∃ φ u, StrictMono φ ∧` strong `L²(0,T;H)` convergence,
stated as `Tendsto (fun n => ∫ t in 0..T, ‖galSeq (φ n) t - u t‖²) atTop (𝓝 0)`. So A2 adds
ONLY the genuinely-missing Bochner-time half (defect 3). Temam III.2.1.~~

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

## Codex axiom audit v1 (verdict needs-attention) — REQUIRED FIXES

Three soundness defects found; all fixable without building the H¹ Hilbert space. These
OVERRIDE the earlier A4/WeakFormNS text above.

**Fix 1 (critical — hidden inconsistency): `b` trilinear + `stokes` bilinear.**
The diagonal-only constraints let a pathological `F` have `stokes(u,0)≠0` / `b(u,u,0)≠0`;
since `galerkin_ode_solution` is ∀-quantified over `F` and `u_ode` tests `w=0`, the ODE then
demands `ν·stokes(u,0)=0` — impossible ⇒ the axiom asserts a non-existent object ⇒ `False`.
Add multilinearity fields to `Torus3NSForms` (TRUE of the genuine forms, so existence axiom
stays true; pathological `F` excluded):
- `stokes_add_left/right`, `stokes_smul_left/right` (bilinear), giving `stokes u 0 = 0`.
- `b_add_i`, `b_smul_i` for i=1,2,3 (trilinear), giving `b u u 0 = 0`, `b 0 v w = 0`, etc.
  (A compact way: state `b` is additive+ℝ-homogeneous in each of its three arguments.)

**Fix 2 (critical — false/wrong-shape bound): smooth-test convection bound.**
Replace `b_bound` (the false `H¹×H¹→L²`) with the TRUE limit-passage-compatible estimate:
for a **smooth (Galerkin) test** `w`, the converging slots are in L²:
`b_bound : ∀ (w : L2Sigma), IsGalerkinTest w → ∃ C : ℝ, ∀ u v : L2Sigma, |b u v w| ≤ C * ‖(u:L2VF)‖ * ‖(v:L2VF)‖`.
TRUE: by antisymmetry `b(u,v,w) = -∫(u·∇)w·v`, so `|b(u,v,w)| ≤ ‖∇w‖_∞‖u‖_{L²}‖v‖_{L²}`
(`‖∇w‖_∞<∞` for trig polynomials). This is the shape strong-L²(0,T) convergence consumes
(controls `b(uₙ-u,uₙ,w)` via `‖uₙ-u‖_{L²}`). Drop `C_b`/`C_b_pos`/the old `b_bound`.

**Fix 3 (high — test space): restrict `WeakFormNS` to smooth/H¹ div-free tests.**
- `def IsGalerkinTest (w : L2Sigma) : Prop := ∃ n, velocityProjection_n n (w:L2VF) = (w:L2VF)`
  (finite Fourier support ⇒ smooth div-free — the standard Faedo–Galerkin test class).
- Add a field `isTest : H → Prop` to `DissipativeEvolution`; `WeakFormNS` quantifies
  `∀ w : E.H, E.isTest w → <identity>` (not all of `E.H`). `torus3Evolution` sets
  `isTest := fun w => IsGalerkinTest w`.

**Non-vacuity note (Codex follow-up):** `b_galerkin` (pin to `galerkinConvection`) stays — it is
what excludes `b=0`. A machine-checkable witness `∃ Galerkin u v w n, galerkinConvection n u v w ≠ 0`
is DEFERRED (documented in STATUS) unless Codex re-blocks on it; mathematically clear (the
convection structure constants do not all vanish).

After these fixes, re-run the Codex axiom audit (blocking) before the prover builds the assembly.

## Codex axiom audit v2 (needs-attention) — REQUIRED FIXES (the 3 v1 defects are confirmed fixed)

Two chain-faithfulness fixes (no inconsistency this round):

**Fix A (A2 sequence ownership): tie the Aubin–Lions package to the input sequence.**
Make `galSeq` a STRUCTURE PARAMETER of `AubinLionsPackage` and drop the internal `galSeq` field:
`structure AubinLionsPackage (F) (ν T) (u₀) (galSeq : ∀ n, GalerkinSolutionData F ν u₀ n) where φ; φ_mono; u; strong_convergence`
with `strong_convergence` stated against the PARAMETER `galSeq`
(`Tendsto (fun n => ∫ t in 0..T, ‖((galSeq (φ n)).u t : L2VF) - (u t : L2VF)‖^2) atTop (𝓝 0)`).
Then `aubin_lions … (galSeq) (spatial) : AubinLionsPackage F ν T u₀ galSeq` and
`galerkin_limit_passage … (galSeq) (alPkg : AubinLionsPackage F ν T u₀ galSeq) : …` — the A1→A2→A3
chain is now type-enforced on one sequence. `build_galerkin_package` passes the single A1 `galSeq`
through both A2 and A3.

**Fix B (interval scoping): the energy inequality holds only on `[0,T]`.**
In `galerkin_limit_passage`'s conclusion, in `GalerkinCompactnessPackageFull.energy_ineq_limit`, and
in `LerayHopfSolutionFull.energy_ineq`, change the hypothesis `0 ≤ t →` to `0 ≤ t → t ≤ T →`.

## Codex axiom audit v3 (needs-attention) — REQUIRED FIX (v2 fixes confirmed good)

One remaining `[high]`: `stokes` is pinned only on the diagonal, leaving a free skew bilinear
term `K` (with `K u u = 0`) that would appear in `WeakFormNS` as a non-NS viscosity term.
**Symmetry fully pins it** (a symmetric bilinear form is determined by its diagonal via
polarization). Add to `Torus3NSForms`:
- `stokes_symm : ∀ (u v : L2Sigma), stokes u v = stokes v u`
  (excludes the skew `K`; TRUE: `∫∇u:∇v` is symmetric.)
- `stokes_bound : ∀ (w : L2Sigma), IsGalerkinTest w → ∃ C : ℝ, ∀ u : L2Sigma, |stokes u w| ≤ C * Real.sqrt (h1EnergySq (u : L2VF))`
  (Galerkin-test continuity for faithful limit passage; TRUE: `|∫∇u:∇w| ≤ ‖∇u‖_{L²}‖∇w‖_{L²} ≤ C_w·√(h1EnergySq u)`,
  `‖∇w‖_{L²}<∞` for trig polynomials.)
Both hold for the genuine viscous form, so `torus3_NSForms_exist` stays true; together with
bilinearity + `stokes_eq` they pin `stokes` to exactly the NS viscous form.

## Codex axiom audit v4 (needs-attention) — REQUIRED FIX: de-axiomatize Stokes (make it concrete)

`[critical]`: a TOTAL real-valued bilinear `stokes` on `L2Sigma` with diagonal `= viscousFormSq 1`
cannot be witnessed by the genuine viscous form (`∫|∇u|² = +∞` off H¹, while the `tsum`
convention gives 0) ⇒ `torus3_NSForms_exist` over-pins an impossible object. The viscous form is
used two ways; split them, and make BOTH concrete (no Stokes axiom at all — strictly shrinks the
trusted base to just the convection form):

1. **Test-slot pairing → concrete `def`** (always finite: used only with a smooth/Galerkin `w`):
```
noncomputable def stokesTestPairing (u w : L2VF) : ℝ :=
  ∑ j : Fin 3, ∑' k : Fin 3 → ℤ,
    (2 * Real.pi) ^ 2 * (∑ i : Fin 3, (k i : ℝ) ^ 2) *
      (mFourierCoeff3 (L2VF_projComponentC j u) k *
        (starRingEnd ℂ) (mFourierCoeff3 (L2VF_projComponentC j w) k)).re
```
(= `⟨∇u, ∇w⟩`; for Galerkin `w` the `tsum` is a finite sum; diagonal `stokesTestPairing u u = viscousFormSq 1 u`.)

2. **Diagonal dissipation → use the existing concrete `viscousFormSq ν`** in the energy inequality.

**Edits (coder):**
- **DELETE from `Torus3NSForms` ALL Stokes fields** (`stokes`, `stokes_nonneg`, `stokes_eq`,
  `stokes_symm`, `stokes_bound`, `stokes_add_left/right`, `stokes_smul_left/right`). `Torus3NSForms`
  keeps only the convection form `b` + its properties (antisymm, trilinearity, smooth-test `b_bound`,
  `b_galerkin`). Update the structure docstring + `torus3_NSForms_exist` justification.
- Add the `stokesTestPairing` def (before `torus3Evolution`).
- `torus3Evolution.viscousForm := fun u w => stokesTestPairing (u : L2VF) (w : L2VF)`.
- `GalerkinSolutionData.u_ode`: replace `ν * F.stokes (u t) w` with `ν * stokesTestPairing (u t : L2VF) (w : L2VF)`.
- Energy-inequality fields (in `galerkin_limit_passage` conclusion, `GalerkinCompactnessPackageFull.energy_ineq_limit`,
  `LerayHopfSolutionFull.energy_ineq`): replace `ν * ∫ s in 0..t, F.stokes (u s) (u s)` with
  `∫ s in (0:ℝ)..t, viscousFormSq ν (u s : L2VF)`. (`viscousFormSq ν u = ν‖∇u‖²` — the genuine dissipation.)
- Remove `hν`/`F` args that become unused only if truly unused (keep `F` — still needed for `b`).

After this, A4 = convection form only; the viscous form is fully concrete. Re-audit.

## Codex axiom audit v5 (needs-attention) — REQUIRED FIX: proof-carry the energy class

`[high]`: the energy inequality `∫ viscousFormSq ν (u s)` is a `tsum` that collapses to a real
default off H¹, so it can hold WITHOUT `u ∈ L²(0,T;H¹_σ)` — the Leray–Hopf energy class isn't
enforced. Fix: A3 (and the two solution structures) must PROOF-CARRY the energy class. Add a field
`energy_class` to `galerkin_limit_passage`'s conclusion, `GalerkinCompactnessPackageFull`, and
`LerayHopfSolutionFull`:
```
energy_class :
  (∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc 0 T)), memH1VF (u t : L2VF)) ∧
  IntervalIntegrable (fun s => viscousFormSq ν (u s : L2VF)) MeasureTheory.volume 0 T
```
(a.e. — NOT ∀-everywhere, which would be false: L² solutions are H¹ only a.e.). TRUE: genuine
Leray–Hopf solutions satisfy `u ∈ L²(0,T;H¹_σ)` ⇒ a.e. `memH1VF` + integrable dissipation. This
makes the energy inequality meaningful (genuine finite dissipation a.e., not a `tsum`-collapse) and
the assembled solution faithful. `exists_lerayHopf_from_package_full` copies this field too.

## Codex axiom audit v6 (needs-attention) — REQUIRED FIX: A3 must produce a GOOD representative

`[critical]`: `galerkin_limit_passage` concludes POINTWISE properties (energy ineq at every `t`,
initial trace) for `alPkg.u`, but `alPkg.u` is pinned only via the integral strong-convergence
(blind to measure-zero changes). A null-set spike preserves the hypotheses but breaks the pointwise
conclusion ⇒ A3 is FALSE for such representatives. Fix: make A3 **existential** — it asserts a good
representative EXISTS (true), not properties of an arbitrary one.

**Edit (coder):** change `galerkin_limit_passage`'s conclusion from properties-of-`alPkg.u` to:
```
∃ u : Time → L2Sigma,
  WeakFormNS ν T (torus3Evolution F) u ∧
  (∀ t, 0 ≤ t → t ≤ T → (1/2)*‖(u t:L2VF)‖^2 + ∫ s in (0:ℝ)..t, viscousFormSq ν (u s:L2VF) ≤ (1/2)*‖(u₀:L2VF)‖^2) ∧
  Filter.Tendsto (fun t => (u t:L2VF)) (nhdsWithin 0 (Set.Ici 0)) (nhds (u₀:L2VF)) ∧
  ((∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc 0 T)), memH1VF (u t:L2VF)) ∧
   IntervalIntegrable (fun s => viscousFormSq ν (u s:L2VF)) MeasureTheory.volume 0 T)
```
A3 still takes `galSeq` + `alPkg` as hypotheses (they justify the existence). The `*Full` structures
are UNCHANGED (they carry a specific curve + proof fields); `build_galerkin_package` (sorry-stub)
will `obtain ⟨u, …⟩` the witness and pack it. Only A3's statement changes.

## Codex axiom audit v7 (needs-attention) — REQUIRED FIX: link the existential to the Aubin–Lions limit

`[high]`: the v6 existential `u` is now UNTETHERED from `alPkg.u`, so A3 reads as "∃ a standalone
Leray–Hopf solution for the data" — essentially the conclusion (not minimal / not-the-conclusion).
Fix: keep the existential good representative BUT add an a.e.-equality link to the Aubin–Lions limit,
so `u` is the good representative OF that limit (not an unrelated solution). Add ONE conjunct to
`galerkin_limit_passage`'s existential (as the FIRST conjunct):
```
(∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc 0 T)), u t = alPkg.u t) ∧
WeakFormNS … ∧ <energy ineq> ∧ <initial trace> ∧ <energy_class>
```
(a.e. equality preserves null-set invariance AND ties A3 to the compactness limit it upgrades.)
`u t = alPkg.u t` is equality in `L2Sigma`. This is the only change.

## Defect-fix checklist (all must hold)
(1) proof-carrying fields ✓ (2) WeakFormNS endpoints vanish via tsupport⊆Ioo 0 T ✓
(3) A2 spatial half discharged via rellich_L2Sigma, not axiomatized ✓ (4) **A4 pins b ≠ 0**
(non-vacuity — the crux above) ✓ (5) A1 has the actual ODE ✓ (6) true 3D bound ✓
(7) no false assembly sorries (bounds come from A1 fields) ✓ (8) (2π)² in viscousFormSq, made
load-bearing via stokes_eq ✓
