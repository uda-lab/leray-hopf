# Global-in-time Leray–Hopf via diagonal extraction — torus-lane campaign (issue #195)

**Author:** lean-architect (fable). **Status:** design + feasibility phase of issue #195.
**Verdict:** **CONDITIONAL-GO** (§9, §11, §12 — all spikes compile sorry-free and every
conjunct of the final target is traced to an existing interface plus a named, provable
transfer lemma; P1/P2 dispatch unconditional, P3/P4 conditioned on the typed
`P2ExitWitness` instantiation + committed scratch-pin checker, §5 P2 row).

Owner decision (recorded at dispatch): on GO the campaign continues through the **torus
global capstone**. ℝ³ implementation is out of scope (assessment only, §8).

---

## 1. Verified interface anchors (all re-read in source at commit `8ef1114`)

| Anchor | Location | Role |
|---|---|---|
| `Galerkin.SolutionData` | `LerayHopf/Galerkin/SolutionBundles.lean:42` | per-`n` Galerkin datum; **all fields horizon-free** (`energy_bound : ∀ t, 0 ≤ t → …`, `reg_bound : ∀ T, 0 < T → …`) — the forward-global premise of the whole campaign |
| `GalerkinSolutionData F ν u₀ n` | `LerayHopf/Torus/SolutionInterfaces.lean:313` | torus abbrev of the above |
| `galSeq_of_torus` | `LerayHopf/Torus/GalerkinODECapstone.lean:54` | the one axiom-free forward-global base family `∀ n, GalerkinSolutionData F ν u₀ n` |
| `AubinLionsPackage` | `LerayHopf/Torus/SolutionInterfaces.lean:342` | `galSeq` is a structure **parameter**; fields `φ, φ_mono, u, strong_convergence (eLpNorm), u_aestronglyMeasurable` |
| `exists_galerkin_modewise_extraction` | `LerayHopf/Torus/ModeCompactness.lean:147` | first extraction; consumes cutoff-quantified leaf `galerkin_test_pairing_lipschitz` (`ModeCompactness.lean:40`, `∀ n, m ≤ n → …`) + per-datum `galerkin_u_norm_le` |
| `exists_limit_curve_of_galSeq` | `LerayHopf/Torus/ModeCompactness.lean:513` | extraction `φ` + limit curve with **pointwise weak convergence at every `t ∈ Icc 0 T` against `z : L2Sigma`**, ball bound `‖u t‖ ≤ ‖u₀‖`, AESM, and level-`N` strong part |
| `torusAubinLionsPackage_of_galSeq` | `LerayHopf/Torus/AubinLionsAssembly.lean:349` | AL package assembly |
| `torus_energyClass_of_aubinLions` | `LerayHopf/Torus/ViscousLimit.lean:168` | energy-class conjunct for `alPkg.u` |
| `exists_weak_representative` (private) | `LerayHopf/Torus/TraceEnergy.lean:491` | the **coherence lever**: sub-extraction `ρ` + *everywhere* weak convergence `∀ t ∈ Icc 0 T, ∀ z : L2VF, ⟪u_{φ(ρ k)}(t), z⟫ → ⟪v t, z⟫` + `v 0 = u₀` + per-test Lipschitz |
| `torus_galerkin_limit_passage_of_energyClass` | `LerayHopf/Torus/TraceEnergy.lean:1150` | good-representative existential: a.e. link, `WeakFormNS`, ∀t energy inequality, strong initial trace, energy class. **Currently drops the `ρ`/weak-pin conjuncts** — P2 re-exports them (§5) |
| `torus_weakFormNS_of_strongConvergence` | `LerayHopf/Torus/LimitPassage.lean:386` | WeakFormNS for `alPkg.u`; the only structural index use is the eventual test-cutoff `n₀ ≤ φ N` |
| `Galerkin.LerayHopfSolution` | `LerayHopf/Galerkin/SolutionBundles.lean:68` | finite-horizon contract: fields `u` + 5 proof fields (`weak_eq`, `energy_ineq`, `initial_trace`, `energy_class`, `u_aestronglyMeasurable`) — all `Prop` |
| `WeakFormNS` | `LerayHopf/EvolutionTriple.lean:125` | separated-variable distributional identity, tests `tsupport ψ ⊆ Ioo 0 T` |
| `exists_lerayHopf_torus3` | `LerayHopf/Torus/GalerkinODECapstone.lean:133` | finite-horizon release capstone — **stays byte-identical** throughout this campaign |
| ℝ³ sibling pin | `LerayHopf/R3/GoodRepresentative.lean:198` | `exists_weak_representative_R3` carries the SAME everywhere-weak pin (against all `z : L2VF_R3`) — reuse basis for §8 |

Structural index-usage audit (grep + read of every consumer): `galSeq : ∀ n, GalerkinSolutionData …`
appears in **22 declarations** across 8 files (ModeCompactness 3, ModeTail 1, AubinLionsAssembly 2,
SolutionInterfaces 1 (the structure), LimitPassage 3, TraceEnergy 10, ViscousLimit 1,
GalerkinODECapstone 1). In every one of them the index enters ONLY as:
(a) per-datum lemma applications parameterized by the datum's own index
    (`galerkin_u_norm_le F ν u₀ (φ n) (galSeq (φ n))` — index-generic);
(b) growth facts `k ≤ φ (ρ k)` via `StrictMono.le_apply` (`TraceEnergy.lean` `hlevel`);
(c) eventual test-cutoff firing `n₀ ≤ φ N` (`LimitPassage.lean:386` body, `galerkin_weakFormNS_zero`);
(d) `u_initial` + `velocityProjection_n_tendsto` along a strictly monotone index sequence.
All four shapes survive replacing the effective mode `φ n` by `κ (φ n)` with `StrictMono κ`
(compose `hκ.comp hφ`; `n₀ ≤ n ≤ κ n` via `hκ.le_apply`). No declaration conflates the datum's
mode with its list position in any other way. This is the load-bearing feasibility fact, and
spike 2 (§7) verifies it end-to-end on the first real pipeline theorem.

---

## 2. Mathematical proof outline (torus lane)

Fix `F : Torus3NSForms`, `ν > 0`, `u₀ : L2Sigma`, and the base family
`galSeq := galSeq_of_torus F ν hν u₀`. Each datum is forward-global (anchor 1), so the SAME
family serves every horizon; `T`-dependence enters only at the compactness layer.

**Step 1 (stages — nested extraction).** By recursion on `m : ℕ` construct per-stage
extractions `e m : ℕ → ℕ` (strictly monotone) and stage limit curves `U m : Time → L2Sigma`:
stage `m` applies the κ-generalized `exists_limit_curve_of_galSeq` (P2) at horizon `T = m + 1`
to the composed family `κ := nestedComp e m = e 0 ∘ ⋯ ∘ e m`, yielding
`∀ t ∈ Icc 0 (m+1), ∀ z : L2Sigma, ⟪(galSeq (nestedComp e m j)).u t, z⟫ → ⟪U m t, z⟫` (in `j`).

**Step 2 (diagonal).** By the abstract diagonal lemma (spike 1, §7):
`δ k := nestedComp e k k` is strictly monotone and for every `m` there is a strictly monotone
`ψ` with `δ (m + j) = nestedComp e m (ψ j)`. By the limit-transfer corollary
(`tendsto_diag_of_tendsto_stage`), for every `m`, every `t ∈ Icc 0 (m+1)`, every `z : L2Sigma`:
`⟪(galSeq (δ k)).u t, z⟫ → ⟪U m t, z⟫` — the FULL diagonal sequence converges weakly at every
forward time (stage witnesses supply the limit). In particular the stage curves cohere:
for `m ≤ m'` and `t ∈ Icc 0 (m+1)`, `U m t = U m' t` (uniqueness of limits in ℝ per test +
subspace separation, Step 4). Define the global curve
`W : Time → L2Sigma, W t := U (Nat.floor (max t 0)) t` (junk below `t = 0` is harmless: every
contract field looks only at `t ≥ 0`; `t ≤ Nat.floor (max t 0) + 1` for `t ≥ 0`).

**Step 3 (per-horizon contracts along the diagonal).** For each `m : ℕ` run the
κ-generalized pipeline at horizon `Tₘ := (m + 1 : ℝ)` with `κ := δ`:
`torusAubinLionsPackage_of_galSeq` (κ-version) → `alPkgₘ`; `torus_energyClass_of_aubinLions`
(κ-version) → `h4ₘ`; `torus_galerkin_limit_passage_of_energyClass` (κ-version, conclusion
strengthened per §5/P2 to re-export what its proof already has) →
`vₘ : Time → L2Sigma` with:
 (0) `vₘ = alPkgₘ.u` a.e. on `[0, Tₘ]`,
 (pin) sub-extraction `ρₘ`, `StrictMono ρₘ`, and **everywhere** weak convergence
      `∀ t ∈ Icc 0 Tₘ, ∀ z : L2VF, ⟪(galSeq (δ (alPkgₘ.φ (ρₘ k)))).u t, z⟫ → ⟪vₘ t, z⟫`,
 (1) `WeakFormNS ν Tₘ (torus3Evolution F) vₘ`,
 (2) ∀t energy inequality on `[0, Tₘ]` with dissipation `viscousFormSq ν`,
 (3) strong initial trace `vₘ(t) → u₀` as `t → 0⁺`,
 (4) energy class (a.e. `memH1VF` + interval-integrable dissipation on `[0, Tₘ]`);
 AESM of `vₘ` on `[0, Tₘ]` is recovered from (0) + `alPkgₘ.u_aestronglyMeasurable` exactly as
 in `build_galerkin_package_of_galSeq` (`GalerkinODECapstone.lean:94–98`).

**Step 4 (overlap coherence — pointwise, not a.e.).** Fix `m` and `t ∈ Icc 0 Tₘ`. The pin
sequence is a sub-subsequence of the diagonal (positions `δ ∘ alPkgₘ.φ ∘ ρₘ`, strictly
monotone by composition). By Step 2 the full diagonal pairing converges to `⟪W t, z⟫` for
every `z : L2Sigma`, hence so does the sub-subsequence; the pin says it converges to
`⟪vₘ t, z⟫` (its `z` ranges over all of `L2VF ⊇ L2Sigma`). Uniqueness of limits in ℝ gives
`⟪vₘ t − W t, z⟫ = 0` for all `z : L2Sigma`; since `vₘ t − W t ∈ L2Sigma`, testing with
`z := vₘ t − W t` gives **`vₘ t = W t` for EVERY `t ∈ Icc 0 Tₘ`** (`Subtype.ext` +
`inner_self_eq_zero`). No a.e.-only identification anywhere in the globalization —
this discharges the issue's "coherent pointwise" requirement via the existing pointwise
weak-convergence information, exactly as requested.

**Step 5 (transfer to `W` and monotone restriction).** By the pointwise-congruence lemma
(`IsLerayHopfOn.congr_Icc`, §4 — every contract field evaluates the curve only inside
`Icc 0 T` / germs at `0⁺`), the horizon-`Tₘ` contract transfers from `vₘ` to `W`. For an
arbitrary `T > 0`, set `m := Nat.floor T` (so `T ≤ m + 1`), and restrict by
`IsLerayHopfOn.mono` (§4; the only non-trivial conjunct is `WeakFormNS`, handled by
`support_deriv_subset`/`tsupport_deriv_subset` + indicator truncation of the interval
integral — a horizon-`T'` test has `tsupport ψ ⊆ Ioo 0 T' ⊆ Ioo 0 T` and its integrand
vanishes identically on `(T', T]`, so `∫₀ᵀ = ∫₀ᵀ'` without any integrability hypothesis:
compare on `Ioc 0 T` via `setIntegral_congr_fun` + `integral_indicator`).

**Result:** `∃ u : Time → L2Sigma, ∀ T > 0, IsLerayHopfOn … T u₀ u` with `u := W` — one
curve, literal `∃u ∀T`. No uniqueness assumption, no gluing of independently chosen
finite-horizon witnesses: every horizon's witness is pinned to the same diagonal.

### 2.1 D2 conjunct table — every conjunct of the final target vs its source

Final target (torus): `exists_global_lerayHopf_torus3` (§4.4), whose per-`T` content is
`Galerkin.IsLerayHopfOn torusDomain F.core ν T u₀ u` = conjunction of exactly the 5 proof
fields of `Galerkin.LerayHopfSolution` (`SolutionBundles.lean:68–88`), specialized at the
torus by `torusDomain_dissip`/`torusDomain_regMem` (`SolutionInterfaces.lean:271–284`, `rfl`):

| # | Conjunct (at horizon `T`, curve `W`) | Source at horizon `Tₘ ≥ T` (curve `vₘ`) | Transfer |
|---|---|---|---|
| 1 | `WeakFormNS ν T (torusDomain.evolution F.core) W` | limit-passage conjunct (1) for `vₘ` | `congr_Icc` (integrand equality on `uIcc 0 Tₘ`) then `WeakFormNS.mono` (§4.2) |
| 2 | `∀ t ∈ [0,T]`, `½‖W t‖² + ∫₀ᵗ viscousFormSq ν (W s) ≤ ½‖u₀‖²` | conjunct (2) for `vₘ` | pointwise eq on `[0,Tₘ]` (norm + `intervalIntegral.integral_congr`); restriction trivial (`T ≤ Tₘ`) |
| 3 | `Tendsto (W ·) (𝓝[≥] 0) (𝓝 u₀)` (strong trace) | conjunct (3) for `vₘ` | germ transfer: `Icc 0 Tₘ ∈ 𝓝[≥] 0` since `Tₘ > 0`; `T`-free |
| 4a | `∀ᵐ t ∂(vol.restrict (Icc 0 T)), memH1VF (W t)` | conjunct (4a) for `vₘ` | pointwise eq + `ae_restrict_of_ae_restrict_of_subset` (`Icc 0 T ⊆ Icc 0 Tₘ`) |
| 4b | `IntervalIntegrable (viscousFormSq ν (W ·)) volume 0 T` | conjunct (4b) for `vₘ` | pointwise eq on `uIoc` + `IntervalIntegrable.mono_set` |
| 5 | `AEStronglyMeasurable (W ·) (vol.restrict (Icc 0 T))` | `alPkgₘ.u_aestronglyMeasurable` + a.e. link (0) + pointwise eq `W = vₘ` on `[0,Tₘ]` | `.congr` + `.mono_measure (restrict_mono …)` |

No conjunct is sourced from anything unproved except the P2/P3/P4 lemmas themselves, each of
which is named below with its exact statement and its kill criterion.

---

## 3. Index-dependence resolution (issue obstacle 1) — DECISION

**Decision: generalize over a strictly monotone mode map `κ`, in the "base + κ" form** —
every generalized declaration keeps the base sequence and adds the mode map:

```lean
(galSeq : ∀ n, GalerkinSolutionData F ν u₀ n) (κ : ℕ → ℕ) (hκ : StrictMono κ)
```

operating on the reindexed family `fun k => galSeq (κ k)`; a subsequent extraction `φ` is
consumed as the composition `κ ∘ φ` (`hκ.comp hφ`). The `AubinLionsPackage` structure gains
one parameter (`κ`, inserted before `galSeq`'s replacement role; `hκ` is NOT a structure
parameter — no field mentions it; only builders take it):

```lean
structure AubinLionsPackage (F : Torus3NSForms) (ν T : ℝ) (u₀ : L2Sigma)
    (galSeq : ∀ n, GalerkinSolutionData F ν u₀ n) (κ : ℕ → ℕ) where
  φ : ℕ → ℕ
  φ_mono : StrictMono φ
  u : Time → L2Sigma
  strong_convergence : Filter.Tendsto (fun n => MeasureTheory.eLpNorm
      (fun t => ((galSeq (κ (φ n))).u t : L2VF) - (u t : L2VF)) 2
      (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T))) Filter.atTop (nhds 0)
  u_aestronglyMeasurable : AEStronglyMeasurable (fun t => (u t : L2VF))
      (MeasureTheory.volume.restrict (Set.Icc 0 T))
```

(shape verified compiling in spike 2 as `AubinLionsPackageKappa`, with the `κ = id`
embedding `ofId` — definitional field transfer — and the package-level extraction closure
`extract`).

**Rejected alternative — index-independent family package** (a structure bundling
`modes : ℕ → ℕ`, `data : ∀ k, GalerkinSolutionData F ν u₀ (modes k)` with no base):
- the cutoff-quantified leaves (`galerkin_test_pairing_lipschitz`,
  `galerkin_weakFormNS_zero`, level-promotion lemmas) are stated over the base sequence with
  `∀ n, m ≤ n → …`; an abstract family would force re-proving them family-generically
  (including re-deriving the n-INDEPENDENT Lipschitz/bound constants, which the current
  statements hide behind an `∃ L` *after* the `galSeq` binder — verified: the constants
  depend only on `Cs, Cb', ν, ‖u₀‖`, but the statement does not say so);
- it breaks the type-enforced "one sequence through the whole A1→A2→A3 chain" design that
  `AubinLionsPackage`'s docstring calls out as intentional;
- the campaign only ever consumes subsequences of the single `galSeq_of_torus`, so "base + κ"
  loses no needed generality.

**Rejected workaround — interleave the extracted family back into a full sequence** (fill
missing modes with fresh `galerkinSolutionData_torus` data): typechecks, but the pipeline's
own extraction may then select interleaved indices carrying NO weak-convergence information,
destroying Step 4's coherence. This is why the API generalization is genuinely required
(confirms the issue's premise).

**Expected diff surface (P2):** the 22 declarations of §1's audit + the structure parameter;
inside proof bodies the only edits are `φ n` → `κ (φ n)` at datum-index positions (most are
`_`-inferred), `hφ.le_apply`-chains gaining one `hκ.le_apply` hop, and `StrictMono`
compositions. Existing fixed-horizon consumers instantiate `κ := id` (definitionally
transparent: `id n ≡ n`), `hκ := strictMono_id`; `build_galerkin_package_of_galSeq`,
`build_galerkin_package_of_torus`, and the release capstone `exists_lerayHopf_torus3`
keep their exact current signatures and statements.

---

## 4. Global contract design (issue obstacle 2) — exact target statements

All statements below are frozen by this document (D1); `lean-coder` transcribes verbatim.
New generic production file `LerayHopf/Galerkin/GlobalContract.lean` (imports
`LerayHopf.Galerkin.SolutionBundles`).

> **Machine-checked (codex-gate remediation, 2026-07-26):** every statement in §4.1–4.4
> now exists in checked Lean in `LerayHopf/Scratch/GlobalContract.lean` (namespace
> `LerayHopf.Scratch195`), and — beyond the gate's minimum of typechecking — the
> equivalences and BOTH transfer lemmas are **fully proved** there (no sorry):
> `nonempty_lerayHopfSolution_iff_exists_isOn`, `globalLerayHopfSolution_nonempty_iff`,
> `toSolution_u` (rfl), `weakFormNS_mono`, `weakFormNS_congr_Icc`, `IsLerayHopfOn.mono`,
> `IsLerayHopfOn.congr_Icc`, `globalTorusCapstone_implies_finite`. The only unproved
> object is `GlobalTorusCapstoneStatement`, deliberately a `def : Prop` (the P4 target
> itself). P1 becomes a namespace move + preflight coverage, not fresh proving. See §10.

### 4.1 The finite-horizon predicate (Prop-valued twin of `LerayHopfSolution`)

```lean
/-- The finite-horizon Leray–Hopf contract as a predicate on a FIXED curve: exactly the
five proof fields of `Galerkin.LerayHopfSolution`, with the curve supplied externally. -/
def Galerkin.IsLerayHopfOn (D : Galerkin.Domain) (C : Galerkin.NSFormCore D)
    (ν T : ℝ) (u₀ : ↥D.σ) (u : Time → ↥D.σ) : Prop :=
  WeakFormNS ν T (D.evolution C) u ∧
  (∀ t, 0 ≤ t → t ≤ T →
    (1 / 2 : ℝ) * ‖(u t : D.X)‖ ^ 2 + ∫ s in (0 : ℝ)..t, D.dissip ν ↑(u s)
      ≤ (1 / 2 : ℝ) * ‖(u₀ : D.X)‖ ^ 2) ∧
  Filter.Tendsto (fun t => (u t : D.X)) (nhdsWithin 0 (Set.Ici 0)) (nhds ↑u₀) ∧
  ((∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc 0 T)), D.regMem ↑(u t)) ∧
    IntervalIntegrable (fun s => D.dissip ν ↑(u s)) MeasureTheory.volume 0 T) ∧
  MeasureTheory.AEStronglyMeasurable (fun t => (u t : D.X))
    (MeasureTheory.volume.restrict (Set.Icc 0 T))
```

Equivalence with the existing contract (blocks any "weakened target" objection):

```lean
theorem Galerkin.LerayHopfSolution.isLerayHopfOn (s : LerayHopfSolution D C ν T u₀) :
    IsLerayHopfOn D C ν T u₀ s.u
def Galerkin.LerayHopfSolution.ofIsOn (h : IsLerayHopfOn D C ν T u₀ u) :
    LerayHopfSolution D C ν T u₀            -- with @[simp] lemma (ofIsOn h).u = u := rfl
theorem Galerkin.nonempty_lerayHopfSolution_iff :
    Nonempty (LerayHopfSolution D C ν T u₀) ↔ ∃ u, IsLerayHopfOn D C ν T u₀ u
```

### 4.2 Transfer lemmas (both provable against current mathlib; §2 Step 5 arguments)

```lean
/-- Contract fields only see the curve inside `Icc 0 T` (plus the germ at `0⁺`). -/
theorem Galerkin.IsLerayHopfOn.congr_Icc (hT : 0 < T)
    (heq : ∀ t ∈ Set.Icc (0 : ℝ) T, u t = v t)
    (h : IsLerayHopfOn D C ν T u₀ v) : IsLerayHopfOn D C ν T u₀ u

/-- Horizon restriction. The `WeakFormNS` part needs no integrability side condition:
a horizon-`T'` test's integrand vanishes identically on `(T', T]`
(`support_deriv_subset`), so the `0..T` and `0..T'` interval integrals agree by
indicator truncation on `Ioc`. -/
theorem WeakFormNS.mono {E : DissipativeEvolution} (h : WeakFormNS ν T E u)
    (hT' : 0 < T') (hle : T' ≤ T) : WeakFormNS ν T' E u
theorem Galerkin.IsLerayHopfOn.mono (h : IsLerayHopfOn D C ν T u₀ u)
    (hT' : 0 < T') (hle : T' ≤ T) : IsLerayHopfOn D C ν T' u₀ u
```

### 4.3 The global structure — literal `∃ u, ∀ T`, no curve duplication

```lean
/-- A single curve satisfying the finite-horizon Leray–Hopf contract at EVERY positive
horizon. The finite-horizon content is a `Prop`-valued predicate on the one field `u`,
so no witness curve is duplicated and coherence of restrictions is definitional
(`(toSolution · ·).u = u` by `rfl`). This is the literal `∃ u, ∀ T > 0, …` shape —
NOT a repackaging of `∀ T > 0, ∃ u_T, …`. -/
structure Galerkin.GlobalLerayHopfSolution (D : Galerkin.Domain)
    (C : Galerkin.NSFormCore D) (ν : ℝ) (u₀ : ↥D.σ) where
  u : Time → ↥D.σ
  isLerayHopfOn : ∀ T : ℝ, 0 < T → Galerkin.IsLerayHopfOn D C ν T u₀ u

def Galerkin.GlobalLerayHopfSolution.toSolution (g : GlobalLerayHopfSolution D C ν u₀)
    (T : ℝ) (hT : 0 < T) : LerayHopfSolution D C ν T u₀ :=
  LerayHopfSolution.ofIsOn (g.isLerayHopfOn T hT)
@[simp] theorem Galerkin.GlobalLerayHopfSolution.toSolution_u … :
    (g.toSolution T hT).u = g.u := rfl
```

Torus abbrev (in the torus assembly file, P4):
`abbrev GlobalLerayHopfSolutionFull (F : Torus3NSForms) (ν : ℝ) (u₀ : L2Sigma) :=
  Galerkin.GlobalLerayHopfSolution torusDomain F.core ν u₀`.

### 4.4 Torus global capstone (final target; P4)

```lean
theorem exists_global_lerayHopf_torus3 (u₀ : L2Sigma) (ν : ℝ) (hν : 0 < ν) :
    ∃ F : Torus3NSForms, ∃ u : Time → L2Sigma, ∀ T : ℝ, 0 < T →
      Galerkin.IsLerayHopfOn torusDomain F.core ν T u₀ u

theorem exists_globalLerayHopfSolutionFull_torus3 (u₀ : L2Sigma) (ν : ℝ) (hν : 0 < ν) :
    ∃ F : Torus3NSForms, Nonempty (GlobalLerayHopfSolutionFull F ν u₀)
```

Statement traps checked (role-contract checklist): forward-time only (all fields are
`0 ≤ t`-guarded or `Icc 0 T`-restricted; `W`'s values below `0` are never inspected);
∀t-vs-a.e. — energy inequality and trace are ∀t/limit statements exactly as in the
finite-horizon contract, coherence is pointwise (§2 Step 4), only `energy_class`/AESM are
intrinsically a.e. (as in the existing contract); no `integral_undef` vacuity introduced —
`WeakFormNS.mono`'s truncation argument is junk-value-proof (§2 Step 5) and `energy_class`
keeps the integrability conjunct; no hypothesis equivalent to the goal (inputs are the
already-proved finite-horizon machinery); quantifier order is literally `∃ F ∃ u ∀ T`
(`F` from `torus3_NSForms_exists` is `T`-independent already today).

---

## 5. Phase decomposition (PR-sized, with tier table and kill criteria)

Model pool on this deployment: **fable and opus ONLY**. "coder/prover" per
`docs/agent-roles.md` ownership; statements always transcribed verbatim from this doc (D1);
codex statement gate before each phase's proof dispatch (orchestrator-run).

Dependencies: P1 ∥ P2 (independent); P3 needs P2; P4 needs P1+P2+P3. One PR per phase.

| Phase | Sub-issue title (`Parent: #195`) | Content | Files | Coder | Prover | Kill criterion (→ back to architect) |
|---|---|---|---|---|---|---|
| **P1** | `[#195-A] Generic global contract layer: IsLerayHopfOn + GlobalLerayHopfSolution + horizon restriction` | §4.1–4.3 verbatim; `WeakFormNS.mono` + `congr_Icc` + `mono` proofs — **all already compiled sorry-free in `LerayHopf/Scratch/GlobalContract.lean` (§10); P1 = move out of `Scratch195` + review** (the generic/torus import-cone split is already proven compiled by the Scratch pair, §10.1 pass-2 note — the generic file moves as-is; the torus capstone `Prop` waits for P4's file). Also (finding 5 + pass-2 F-D): preflight/CI additions, lean-coder-owned — scratch (or successor) build-cone coverage AND automated `#print axioms` pin enforcement (fail on `sorryAx`/project axioms) | new `LerayHopf/Galerkin/GlobalContract.lean` | opus | opus | `WeakFormNS.mono` not closable via the indicator-truncation route after 2 attempts (do NOT add integrability hypotheses — that is a statement change ⇒ architect); risk retired by the compiled spike |
| **P2** | `[#195-B] κ-generalize the torus compactness chain (mode map through AubinLionsPackage → limit passage)` | thread `(κ, hκ)` per §3 through the 22 declarations; strengthen `torus_galerkin_limit_passage_of_energyClass` to re-export `(ρ, StrictMono ρ, everywhere weak-convergence pin)` (its proof already holds them — pass-through from `exists_weak_representative`); rewire fixed-horizon consumers with `κ := id`. **Exit gate (pass-2 F-A, hardened at pass-3 G-1 into a typed artifact):** P2 is complete — and P3/P4 may be dispatched — only when a production theorem is compiled instantiating the shape of `LerayHopf.Scratch195.P2ExitWitness` (`LerayHopf/Scratch/P2ExitContract.lean`): `∀ F ν hν T hT u₀ φ₁ (hφ₁ : StrictMono φ₁) galSeq₁, Nonempty (P2ExitWitness F ν T u₀ φ₁ galSeq₁)` — production names may differ, the FIELDS may not lose content. The `transport : ∀ k, base (φ₁ k) = galSeq₁ k` field is mandatory: a base family is admissible ONLY as bound by `transport` to the GIVEN dependent family, every stage (package, energy class, limit passage, pin) is a field over that same family, and the pin is phrased against `galSeq₁` itself — an end-to-end chain over an unlinked fresh/canonical family cannot instantiate the artifact. ADDITIONALLY (pass-3 G-2): the fail-closed scratch-pin checker (§10.5) must be committed (`scripts/`, lean-coder) and green before P3/P4 dispatch | `ModeCompactness, ModeTail, SolutionInterfaces, AubinLionsAssembly, ViscousLimit, TraceEnergy, LimitPassage, GalerkinODECapstone` | opus | opus (bodies are mechanical re-threading) | any statement fails to typecheck as designed, OR >2 proof bodies need non-mechanical re-proving, OR the release capstone's statement would change, OR the F-A exit gate cannot be reached without a statement change (e.g. limit passage demands index transport the design did not anticipate) |
| **P3** | `[#195-C] Diagonal machinery: abstract diagonal lemma + stage recursion + diagonal weak limit W` | promote spike 1 to production (new PDE-independent `LerayHopf/Bochner/DiagonalExtraction.lean`, names/statements as in §7 minus scratch prefix); stage recursion (indexed `StageData m` structure + structural recursion, §2 Step 1) and the packaged theorem `exists_diagonal_weakly_convergent_galSeq : ∃ δ, StrictMono δ ∧ ∃ W, ∀ m : ℕ, ∀ t ∈ Icc (0:ℝ) (m+1), ∀ z : L2Sigma, Tendsto (fun k => ⟪(galSeq (δ k)).u t, z⟫) atTop (𝓝 ⟪W t, z⟫)` | above + new `LerayHopf/Torus/DiagonalGalerkin.lean` | opus | **fable** (dependent recursion + coherence) | stage recursion not expressible as designed, or stage-limit coherence fails from `z : L2Sigma` tests alone |
| **P4** | `[#195-D] Torus global capstone: exists_global_lerayHopf_torus3` | per-horizon runs over `κ := δ`, Step-4 coherence lemma, `congr_Icc`/`mono` assembly, §4.4 capstones, docs (`claims-and-scope.md`, `architecture.md`) | new `LerayHopf/Torus/GlobalCapstone.lean` + docs | opus | **fable** | pin insufficient for some conjunct's transfer (must NOT be patched by weakening — architect) |
| **P5** | `[#195-E] ℝ³-lane reuse design addendum (assessment only)` | update §8 against post-P4 reality; open/scope R3 sub-issues | docs only | — (architect/planner) | — | n/a |

Escalation per D4: 2 failed attempts or ~1.5h thrash → next tier (opus → fable), with
evidence. `#print axioms` / `scripts/check-axioms-live.sh` evidence required for every
sorry-free claim (D7). Codex gate points: after P1 statements, after P2 signature diff,
after P3 statements, after P4 proofs (before PR).

---

## 6. What this campaign does NOT do (scope guards)

- Does not touch, rename, or weaken `exists_lerayHopf_torus3` (release capstone stays
  byte-identical; `v0.1.0-rc1` claims unchanged).
- No uniqueness of weak solutions assumed anywhere; no gluing of independently chosen
  witnesses (single diagonal family end-to-end).
- No new axioms; no re-proof of Aubin–Lions; no new NS estimates (all analytic content is
  already in the merged chain — the campaign is extraction/plumbing/logic).
- ℝ³ implementation deferred (P5 assessment gate).

---

## 7. Spike results (this phase's evidence)

### Spike 1 — `LerayHopf/Scratch/DiagonalExtraction.lean` (abstract diagonal, fully proved)

Mathlib was checked for a ready-made lemma: `Filter.extraction_forall_of_frequently` /
`extraction_forall_of_eventually` (`Mathlib/Order/Filter/AtTopBot/Basic.lean:114–139`)
diagonalize *predicates*, not nested subsequence towers; nothing matching the
stage-refinement conclusion exists, so it is proved from scratch (pure order theory,
~120 lines). Key declarations (exact statements in the file):

- `nestedComp e m` (= `e 0 ∘ ⋯ ∘ e m`), `nestedComp_strictMono`, `nestedComp_add`
  (`nestedComp e (m+j) = nestedComp e m ∘ tailComp e m j`);
- `diagExtraction e k := nestedComp e k k`, `diagExtraction_strictMono`;
- `exists_diagonal_extraction : (∀ m, StrictMono (e m)) → ∃ δ, StrictMono δ ∧ ∀ m, ∃ ψ,
  StrictMono ψ ∧ ∀ j, δ (m + j) = nestedComp e m (ψ j)`;
- `tendsto_diag_of_tendsto_stage` (arbitrary target filter — the Step-2 workhorse).

### Spike 2 — `LerayHopf/Scratch/KappaReindex.lean` (κ-interface against REAL interfaces)

- `exists_galerkin_modewise_extraction_kappa` — the κ-generalized twin of the production
  extraction entry point, proved by the production body with indices threaded through `κ`;
  demonstrates that per-datum leaves (`galerkin_u_norm_le`) and cutoff-quantified leaves
  (`galerkin_test_pairing_lipschitz`, via `m ≤ n ≤ κ n`) apply UNCHANGED.
- `reindexed_family_second_extraction` — second extraction over the base+map presentation
  (`galSeq` + `φ₁`), composing to `StrictMono (φ₁ ∘ φ₂)`. NOTE (codex finding 2): this
  consumes the base family plus a map, NOT the dependent family type; the literal shape
  is handled by the next item.
- `exists_galerkin_modewise_extraction_of_reindexed` (codex-gate remediation) — the
  issue's acceptance criterion in its LITERAL shape: the hypothesis is
  `galSeq₁ : ∀ k, GalerkinSolutionData F ν u₀ (φ₁ k)` itself (no base family), consumed
  via the `extendReindexedFamily` embedding (off-subsequence indices filled by the
  axiom-free `galSeq_of_torus`; restoration on the subsequence proved in
  `extendReindexedFamily_apply` from injectivity alone). See §10.2.
- `AubinLionsPackageKappa` + `ofId` (definitional `κ = id` embedding) + `extract`
  (package-level subsequence closure) — the P2 structure design typechecks against the real
  `AubinLionsPackage` fields. Effective-map lemmas (`effective_strictMono`,
  `effective_tendsto_atTop`, `extract_φ` (rfl), `extract_effective_strictMono`) thread
  strictness/cofinality through composition — §10.3.

### Spike 3 — `LerayHopf/Scratch/GlobalContract.lean` + `GlobalContractTorus.lean` (contract layer + truncation, fully proved)

Added at the codex gate (findings 1 and 4): the entire §4 contract layer machine-checked
with the transfer lemmas fully proved, plus the no-integrability truncation lemma with
concrete non-integrable witness and integrable-branch cross-check (a real
`setIntegral_union` additivity theorem + route-agreement corollary, pass-2 F-C).
Split at pass-2 F-B into the generic file (imports only
`LerayHopf.Galerkin.SolutionBundles` + mathlib) and the torus-side capstone file —
compiling the P1 import-cone design. Details in §10.1/§10.4.

All spike files compile sorry-free under the flock'd incremental build (see the task
report for the exit status; scratch modules are built explicitly — they are not imported
by the `LerayHopf` root; re-verification commands and axiom-pin expectations in §10.5).

---

## 8. ℝ³-lane reuse assessment (assessment only; implementation out of scope)

- **Reused as-is (no per-lane work):** the abstract diagonal machinery (P3's
  `DiagonalExtraction`, PDE-independent) and the entire generic contract layer (P1:
  `IsLerayHopfOn`, `WeakFormNS.mono`, `congr_Icc`, `mono`, `GlobalLerayHopfSolution`) — all
  stated over `Galerkin.Domain`/`DissipativeEvolution`, both lanes instantiate.
- **Same design, re-threaded per file (P2-analogue):** the R³ compactness chain has the same
  "base `galSeq` + per-datum/cutoff leaves" architecture; `GalerkinSolutionData_R3` is the
  same generic `Galerkin.SolutionData` (issue #112), and the crucial coherence lever exists
  verbatim: `exists_weak_representative_R3` (`R3/GoodRepresentative.lean:198`) already
  exports the everywhere weak-convergence pin against all `z : L2VF_R3` (even without a
  sub-extraction `ρ` — along `alPkg.φ` directly, slightly SIMPLER than the torus). The
  κ-threading pattern validated by spike 2 transfers mechanically; volume is comparable
  (R³ chain: `SpaceTimeCompactness`, `GoodRepresentative`, `TraceEnergy_R3`-equivalents).
- **Genuinely R³-specific residue:** the stage/extraction layer works against R³'s
  ball-restricted strong convergence (`strong_convergence_ae` per ball radius) instead of
  the torus mode-wise construction; the stage recursion (P3-analogue) must consume R³'s
  limit-curve theorem, whose weak-convergence conjunct should be checked for
  every-`t`-vs-a.e. before committing (kill-criterion analogue of P3).
- **Estimate:** P1+P3(abstract) amortize fully; the R³ campaign ≈ one P2-sized re-threading
  PR + one P3/P4-sized assembly PR. Open R3 sub-issues only after P4 lands (P5 gate).

---

## 9. GO/NO-GO verdict

**GO** — refined at the pass-2 codex gate to **CONDITIONAL-GO**: unconditional for
P1/P2 dispatch, with P3/P4 dispatch conditioned on P2's end-to-end κ-chain exit gate
(§5 P2 row; disposition in §11). Grounds:

1. **Both issue obstacles are discharged with compiled evidence**, not on paper: the
   abstract diagonal lemma is fully proved (spike 1), and the index-dependence obstacle is
   resolved by a design whose entry-point instance compiles against the real interfaces,
   including consumption of a previously extracted subsequence and composition of
   extractions (spike 2).
2. **The coherence risk — the one place this campaign could have died — is closed by an
   existing interface**: `exists_weak_representative` already proves the everywhere
   (∀ t ∈ Icc, ∀ z : L2VF) weak-convergence pin for the good representative; P2 only
   re-exports through one existential what the proof already holds. Given the pin,
   overlap coherence is pointwise equality by uniqueness of weak limits in the ambient
   Hilbert space plus subspace separation (§2 Step 4) — no a.e.-representative gluing.
3. **Every conjunct of the final target is traced** (§2.1) to a merged theorem plus a named
   transfer lemma each of which has a concrete mathlib-supported proof route
   (`support_deriv_subset` + indicator truncation for the only nontrivial one).
4. **The forward-global premise holds by construction**: `Galerkin.SolutionData`'s bounds
   are horizon-free and `galSeq_of_torus` rests on `forwardGlobalSolution_exists`, so no
   new analysis is needed anywhere — the campaign is extraction, reindexing, and logic.
5. Residual risks are localized and each phase has a kill criterion routing back here
   (D3): P2 volume risk (mechanical, bounded by the §1 audit), P3 recursion-engineering
   risk (fable-tier, pattern is standard), P4 assembly risk (pin-based, Step 4 argument
   is three named lemmas).

6. **Post-gate reaffirmation (2026-07-26):** the codex adversarial statement gate raised
   five findings; all five are remediated in §10 — four with newly compiled sorry-free
   evidence (`GlobalContract.lean` contract layer + no-integrability truncation with a
   concrete non-integrable witness; dependent-family extraction
   `exists_galerkin_modewise_extraction_of_reindexed`; effective-map
   strictness/cofinality lemmas), and one (the P2 κ-thread volume) by the explicit,
   argued narrowing in §10.2 with the P2 kill criterion as the standing safeguard. No
   finding falsified a premise; the P1 proof risk is now retired outright.

First dispatch-ready task: **P1** (independent of P2; statements in §4 are frozen and
complete). P2 may run in parallel on a separate branch/worktree per D6.

## 10. Codex statement-gate remediation (2026-07-26)

The B0 adversarial review (`--effort xhigh`, orchestrator-run) returned five findings.
Disposition, one by one:

### 10.1 Finding 1 (high) — contract existed only as markdown

**Resolved with compiled evidence, beyond the requested minimum.** All §4 statements
are now checked Lean in `LerayHopf/Scratch/GlobalContract.lean`, and the transfer
lemmas are fully proved, not deferred: `weakFormNS_mono`, `weakFormNS_congr_Icc`,
`IsLerayHopfOn.mono`, `IsLerayHopfOn.congr_Icc`, plus the round-trip equivalences
`nonempty_lerayHopfSolution_iff_exists_isOn` (the per-horizon conjunct is *exactly*
`Nonempty (Galerkin.LerayHopfSolution …)` — not weaker) and
`globalLerayHopfSolution_nonempty_iff` (the structure *is* the literal
`∃ u, ∀ T > 0, …`), and the no-duplication witness `toSolution_u : (g.toSolution T hT).u
= g.u := rfl`. `globalTorusCapstone_implies_finite` proves in Lean that the frozen P4
target implies the existing finite-horizon capstone shape at every horizon. The single
unproved object is `GlobalTorusCapstoneStatement`, a `def : Prop` — the campaign target
itself, which the gate asked to see stated, not proved. Verdict impact: finding 1's
CONDITIONAL-GO fallback is unnecessary; the finding-1 obligation is discharged
unconditioned (P1 is now a move + review; the campaign-level verdict is set in §11).

**Pass-2 F-B (import-cone separation), resolved by compilation:** the scratch contract
is now TWO files mirroring the frozen P1 design exactly —
`LerayHopf/Scratch/GlobalContract.lean` (everything generic: `IsLerayHopfOn`, the
equivalences, `GlobalLerayHopfSolution`, all transfer lemmas, the truncation toolkit)
imports ONLY `LerayHopf.Galerkin.SolutionBundles` + two mathlib modules — no
`LerayHopf.Torus.SolutionInterfaces`, no torus-lane instantiation; and
`LerayHopf/Scratch/GlobalContractTorus.lean` (the frozen P4 capstone `Prop` +
`globalTorusCapstone_implies_finite`) imports the generic file plus
`LerayHopf.Torus.SolutionInterfaces`. Both compile, so "a literal namespace move cannot
preserve both generic layering and the torus target" is answered: P1 moves the generic
file to `LerayHopf/Galerkin/GlobalContract.lean` with its import cone intact, and the
torus capstone statement rides with the torus lane (P4's file), exactly as §5 assigns.
(Note: the generic layer's `Time` abbrev itself lives in `LerayHopf/Torus/Basic.lean`
and reaches `SolutionBundles` through `EvolutionTriple` — a PRE-EXISTING production
layering fact, unchanged by this campaign; "generic" here means generic over
`Galerkin.Domain`, exactly as `Galerkin.LerayHopfSolution` already is.)

### 10.2 Finding 2 (high) — dependent family shape not consumed; audit prose-only

**First half resolved with compiled evidence.**
`exists_galerkin_modewise_extraction_of_reindexed` (KappaReindex.lean) now consumes the
LITERAL previously-extracted family type `galSeq₁ : ∀ k, GalerkinSolutionData F ν u₀
(φ₁ k)` — no base family among its hypotheses — via the embedding
`extendReindexedFamily` (+ `extendReindexedFamily_apply`, needing only injectivity),
which fills off-subsequence indices with the canonical axiom-free `galSeq_of_torus`
datum. This DERIVES the dependent shape from the base+κ entry point rather than
re-proving it, which is precisely the §3 design claim: base+κ loses no generality on
this lane, because the torus Galerkin ODE layer is total (`forwardGlobalSolution_exists`),
so every dependent family embeds. (Abstract caveat, stated honestly: on a lane without
a total ODE layer the embedding would need some filler family; that is a non-issue
here and for ℝ³, whose Galerkin layer is likewise total.)

**Second half — explicit, argued narrowing (the gate's stated alternative).** Compiling
the κ-thread through all 22 audited declarations IS phase P2; doing it in scratch would
duplicate a full production phase inside the design gate, without review or ownership
(the declarations are production files owned by lean-coder/lean-prover, which the
architect must not edit). What the design phase owes is: (a) the audit itself (§1, all
22 declarations re-read in source at `8ef1114`, each classified into the four index-usage
shapes), (b) compiled proof that the HARDEST consumer pattern — the extraction entry
point with its eventual-cutoff Lipschitz leaf, the only shape-(c) + shape-(b) mix —
survives κ-reindexing (`exists_galerkin_modewise_extraction_kappa`, and now the
dependent form), and (c) a kill criterion that routes any audit miss back to the
architect (P2 row, §5: "any statement fails to typecheck as designed, OR >2 proof
bodies need non-mechanical re-proving"). All three are in place; acceptance of #195's
criterion is via the compiled dependent-shape theorem, not via the base+κ surrogate.

**Pass-2 F-A (the residual, stated honestly and gated):** codex correctly observes
that the dependent-family spike proves scalar mode-pairing extraction only — it does
not compile a κ-version of the Aubin–Lions builder, the energy-class proof, the
weak-form limit passage, or the representative pin, and the `galSeq_of_torus` filler
lives downstream (GalerkinODECapstone) of the layers P2 reworks. That residual IS
phase P2, and the campaign adopts codex's own recommendation rather than pretending
the spike covers it: the campaign verdict is **CONDITIONAL-GO** with P2 carrying an
explicit exit gate — end-to-end κ chain compiled through package construction, energy
class, limit passage, and representative pin, consumed from the dependent/reindexed
family with transport equalities proved (or the base family as an explicit parameter)
— and P3/P4 are not dispatched until that gate is green (§5 P2 row; §11). The
filler-downstream observation also yields a concrete P2 design note: inside P2, the
embedding is available only ABOVE the ODE layer (which P2 does not modify), or the
base family is carried as a parameter. At pass-3 (G-1) this gate was hardened into the
TYPED artifact `P2ExitWitness` (`Scratch/P2ExitContract.lean`, §12): the base-family
vehicle survives only through the mandatory `transport` field binding it to the given
dependent family, so the "unlinked canonical family" implementation codex warned about
is unrepresentable, not merely discouraged.

### 10.3 Finding 3 (medium) — effective-map strictness/cofinality not carried

**Resolved with compiled evidence, via the composition-lemma option.** New lemmas
(KappaReindex.lean): `AubinLionsPackageKappa.effective_strictMono`,
`.effective_tendsto_atTop` (cofinality, the form the `n₀ ≤ κ (φ N)` cutoffs consume),
`.extract_φ` (`rfl`; extraction composes position maps on the nose), and
`.extract_effective_strictMono` (strictness survives package-level extraction).
Design decision defended: `hκ : StrictMono κ` stays a SIDE hypothesis rather than a
structure field, because (i) the `κ = id` instance must stay definitionally transparent
for the existing consumers P2 rewires (`ofId` is a field-copy), and (ii) the structure's
constructor arity stays byte-stable, which P2's mechanical rewiring assumes. Every
consumer needing strictness/cofinality gets it from these lemmas with `hκ` in scope —
which P2's signatures all have, since they take `(κ, hκ)` together (§3).

### 10.4 Finding 4 (medium) — junk-safety of the no-integrability truncation

**Resolved with compiled evidence, both branches.**
`setIntegral_Ioc_eq_of_tail_zero` (GlobalContract.lean) proves the truncation step with
NO integrability hypothesis and NO appeal to interval additivity: the two indicator
functions are pointwise equal, so the Bochner integrals coincide even when both are the
junk value (`integral_indicator` twice + `funext`). The feared `integral_undef` vacuity
cannot arise because no step ever cases on integrability. Branch evidence: the
NON-integrable branch is exercised concretely (`badTail := 1/t on (0,1], 0 after`;
`badTail_not_integrableOn` via `intervalIntegrable_inv_iff`; `badTail_truncation`
applies the lemma to it), and the integrable branch is cross-checked against the
classical additivity route — **as a theorem, not prose** (pass-2 F-C):
`truncation_agrees_with_additivity` proves `∫_{Ioc 0 c} = ∫_{Ioc 0 b} + ∫_{Ioc b c}` by
genuinely invoking `MeasureTheory.setIntegral_union` on the disjoint decomposition
`Ioc_union_Ioc_eq_Ioc` (both `0 ≤ b` and integrability are consumed), plus tail `= 0`;
`truncation_routes_agree` then derives from it exactly the equation the indicator route
emits, so conservativity-over-classical is itself machine-checked. `weakFormNS_mono`
then uses exactly this lemma; the integrand vanishes on `(T', T]` term-by-term via
`image_eq_zero_of_notMem_tsupport` + `deriv_of_notMem_tsupport` (every term carries a
`ψ t` or `deriv ψ t` factor). No integrability hypothesis was added to any statement.

### 10.5 Finding 5 (medium) — scratch evidence outside the default build cone

**Resolved within architect ownership; script change delegated to P1.** The spikes are
not imported by `LerayHopf.lean` (by design — scratch must stay out of the release
cone), so `agent-preflight.sh`'s default build does not rebuild them. Mitigations now
in place: (a) every spike file ends with `#print axioms` pins for its key theorems, so
any rebuild of the scratch targets re-verifies axiom hygiene in the log; (b) the
verbatim re-verification commands are recorded here and MUST be run (and their tail
quoted) by any phase that touches the spikes:

```sh
#!/usr/bin/env bash
# Fail-closed scratch evidence gate (pass-3 G-2): non-zero exit on build failure OR
# any axiom pin outside the kernel trio.  No pipe swallows the build status.
set -euo pipefail
export PATH="$HOME/.elan/bin:$PATH"
log="$(mktemp)"
flock /tmp/lean-build.lock lake build \
  LerayHopf.Scratch.DiagonalExtraction \
  LerayHopf.Scratch.KappaReindex \
  LerayHopf.Scratch.GlobalContract \
  LerayHopf.Scratch.GlobalContractTorus \
  LerayHopf.Scratch.P2ExitContract >"$log" 2>&1 \
  || { echo "BUILD FAILED"; tail -40 "$log"; exit 1; }
grep -q "Build completed successfully" "$log"
# Join wrapped info lines, keep only axiom-pin lines, then reject any axiom token
# other than the kernel trio (in particular sorryAx and any project axiom).
pins="$(tr '\n' '@' <"$log" | sed 's/@ / /g' | tr '@' '\n' | grep 'depends on axioms')"
[ -n "$pins" ]  # at least one pin line must exist (else the targets were not checked)
if printf '%s\n' "$pins" | sed -E 's/propext|Classical\.choice|Quot\.sound//g' \
    | grep -oE '\[[^]]*\]' | grep -qE '[A-Za-z_]'; then
  echo "PIN VIOLATION:"; printf '%s\n' "$pins"; exit 1
fi
echo "SCRATCH PIN CHECK OK ($(printf '%s\n' "$pins" | wc -l) pinned declarations)"
```

This gate is reproducible from repo state alone and FAIL-CLOSED (pass-2 F-D + pass-3
G-2): the pins are `#print axioms` lines INSIDE the committed spike files, the build
status is checked directly (no `| tail` pipe to swallow it), and the pin assertion
exits non-zero on `sorryAx` or any project axiom. Session logs quoted in reports are
convenience transcripts; the committed files and this script are the source of truth.
(c) Committing this checker as a repository script wired into preflight/CI is a
`scripts/` change owned by lean-coder (dispatched as a P1-precursor work item); per
pass-3, P3/P4 dispatch additionally requires that committed checker merged and green
(§5 P2 row, §12).

---

## 11. Codex pass-2 gate disposition (2026-07-28) — final verdict CONDITIONAL-GO

The re-gate (`--effort xhigh`) credited the contract layer, effective-map lemmas, and
core truncation identity, and raised four findings. Disposition:

- **F-A (high, spike ≠ full κ pipeline)** — accepted, not contested. Adopted codex's
  own recommendation as the campaign verdict: **CONDITIONAL-GO**, the condition being
  the P2 exit gate (§5 P2 row: end-to-end κ chain through Aubin–Lions package
  construction, energy class, limit passage, representative pin, from the
  dependent/reindexed family; P3/P4 dispatch blocked until green). Honest residual
  analysis + P2 design notes in §10.2 (pass-2 paragraph). Rationale for not spiking
  further now: the remaining risk is exactly P2's content; compiling it in scratch
  would duplicate a production phase inside the design gate at multi-day cost, against
  an explicitly gated dispatch that produces the same evidence under review and
  ownership.
- **F-B (medium, import-cone separability)** — resolved by compilation: the scratch
  contract split into `Scratch/GlobalContract.lean` (generic-only imports) +
  `Scratch/GlobalContractTorus.lean` (torus lane); both build green (§10.1 pass-2
  note). P1's move is now literally file-for-file.
- **F-C (medium, additivity cross-check was not an additivity proof)** — resolved by
  proving the real theorem: `truncation_agrees_with_additivity` now invokes
  `MeasureTheory.setIntegral_union` on `Ioc_union_Ioc_eq_Ioc` (integrability and
  `0 ≤ b` genuinely consumed), and `truncation_routes_agree` derives the indicator
  route's exact equation from it (§10.4).
- **F-D (medium, evidence pointed at a failed /tmp log)** — resolved: §10.5 now
  declares the committed `#print axioms` lines + the verbatim build command as the
  sole evidence contract (reproducible from repo state); session logs are demoted to
  convenience transcripts; automated pin enforcement folded into P1's lean-coder task.

**Verdict line: CONDITIONAL-GO.** P1 and P2 are dispatch-ready now (P1 independent;
P2 carries the F-A exit gate); P3/P4 wait on P2's gate; P5 unchanged.

---

## 12. Codex pass-3 gate disposition (2026-07-28) — gate hardened, verdict unchanged

Pass-3 ratified F-B and F-C as materially remediated and called P1/P2 dispatch
reasonable; both remaining findings harden the P2 exit gate. Disposition:

- **G-1 (high, gate permitted an unlinked base-family implementation)** — resolved by
  a TYPED acceptance artifact, compiled: `LerayHopf/Scratch/P2ExitContract.lean`
  defines `P2ExitWitness F ν T u₀ φ₁ galSeq₁` with the dependent family as a
  PARAMETER, a mandatory `transport : ∀ k, base (φ₁ k) = galSeq₁ k` field (the
  loophole is unrepresentable, not discouraged), all four chain stages as fields over
  the same `base`/`alPkg`/`v` (types transcribed verbatim from
  `torus_energyClass_of_aubinLions`, `torus_galerkin_limit_passage_of_energyClass`,
  `exists_weak_representative`), and the representative pin phrased against `galSeq₁`
  itself. Three fully-proved smoke lemmas show the artifact is usable and sufficient:
  `pin_base` (transport genuinely transports), `effective_strictMono` (finding-3
  lemmas apply), `v_aestronglyMeasurable` (the one implicit contract conjunct is
  derivable from the fields — no hidden extra input for P4). §5's P2 exit gate now
  names the artifact and DELETES the free-standing base-family alternative.
- **G-2 (medium, evidence command not fail-closed, pins not enforced)** — resolved in
  two parts. (a) §10.5's verbatim command is now a fail-closed script: `set -euo
  pipefail`, build status checked directly (no `| tail` pipe), wrapped-line-safe pin
  extraction, non-zero exit on `sorryAx`/any non-kernel axiom, and a positive
  assertion that pin lines exist. It was extracted from this doc VERBATIM and run
  green (all scratch targets, pins clean) before commit. (b) The committed repository
  checker (wired into preflight/CI) is `scripts/` territory = lean-coder, dispatched
  by the orchestrator as a P1-precursor item; per codex's bottom line, P3/P4 dispatch
  requires that checker merged and green — recorded in the §5 P2 exit gate.

**Verdict line: CONDITIONAL-GO (unchanged).** P1/P2 dispatch-ready; P3/P4 blocked
until (i) a production instantiation of the `P2ExitWitness` shape is compiled and
(ii) the committed scratch-pin checker is merged and green.
