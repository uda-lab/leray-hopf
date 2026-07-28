# Global-in-time Leray–Hopf on ℝ³ via diagonal extraction — ℝ³-lane campaign (issue #212)

**Author:** lean-architect (fable). **Status:** B0 design gate, 2026-07-28.
**Verdict (§9): CONDITIONAL-GO** — P1′/P2′ dispatch-ready; P3′/P4′ dispatch blocked on the
P2′ typed exit gate (§6, six clauses), mirroring the #195 torus-campaign discipline whose
condition was met on schedule. Codex adversarial statement gate (xhigh) pass-1 through
pass-7 findings dispositioned in §11.

This campaign document is NEW and separate from the frozen torus campaign doc
(`docs/scratch/global-diagonal-campaign.md`, #195 — COMPLETE, not edited by this lane).
It follows the same B0 standard: verified interface anchors, conjunct-by-conjunct trace of
the final target, typed exit gate, phase table with tier assignments and kill criteria,
compiled sorry-free spikes.

Integration policy (owner directive 2026-07-28, recorded in issue #212): this lane lands on
`dev/v0.2.0`; the owner merges dev→main only once BOTH lanes are complete.

---

## 1. Verified interface anchors (all re-read in source at commit `455ca3b`)

| Anchor | Location | Role |
|---|---|---|
| `Galerkin.SolutionData` | `LerayHopf/Galerkin/SolutionBundles.lean:42` | horizon-free per-`n` datum (`energy_bound : ∀ t, 0 ≤ t → …`) — the forward-global premise, shared with the torus lane |
| `GalerkinSolutionData_R3` | `LerayHopf/R3/SolutionInterfaces.lean:470` | `extends Galerkin.SolutionData (r3Domain 𝔊) F.core ν u₀ n` + weighted-Fourier enrichment; per-datum leaves apply index-generically |
| `galSeq_R3_of_basis` | `LerayHopf/R3/GalerkinODECapstone.lean:64` | the axiom-free forward-global base family over the CONCRETE scheme `schemeOfBasis B`; `T`-free |
| `exists_lerayHopf_r3` | `LerayHopf/R3/GalerkinODECapstone.lean:109` | finite-horizon release capstone — `∃ 𝔊 F, Nonempty (LerayHopfSolutionFull_R3 𝔊 F ν T u₀)`; **stays byte-identical**. Its witnesses `schemeOfBasis B` (from `nonempty_schwartzGalerkinBasis_H1`) and `F` (from `r3_NSForms_exists`) are `T`-independent — the global lane fixes them ONCE |
| `AubinLionsPackage_R3` | `LerayHopf/R3/SolutionInterfaces.lean:550` | fields `φ, φ_mono, u, u_aestronglyMeasurable, strong_convergence` (per-`R` `eLpNorm`), `strong_convergence_ae` (per-`R` a.e.-`t`); `galSeq` is a structure parameter — gains the `κ` parameter in P2′ (§4) |
| `galerkin_spacetime_precompact_of_goodSampling` / `galerkin_spacetime_precompact_R3` | `R3/SpacetimePrecompact.lean:445` / `R3/ArzelaAscoliTime.lean:135` | REFINE-CAPABLE root: takes arbitrary external `ψ : ℕ → ℕ` StrictMono + ball `k`, returns further `ρ`; soundness (subsequence stability of the Aubin–Lions–Simon hypotheses) proved + documented. **No change needed in P2′** |
| `perBall_ae_subseq` | `R3/ArzelaAscoliTime.lean:783` | refine-capable (external `ψ`); **no change needed** |
| `diag_ae_subseq` | `R3/ArzelaAscoliTime.lean:839` | per-ball Cantor tower, internally seeded `Φ 0 = id` — κ-threading layer 1 (§4); seed composed by pre-composition (spike (b), compiled) |
| `galerkin_weakLimit_R3` | `R3/ArzelaAscoliTime.lean:284` | THEOREM (not axiom); extraction-GENERIC (takes arbitrary `φ, hφ`) — **no change needed** (spike (b) layer 2 passes `κ ∘ φ`) |
| `u_lim_aestronglyMeasurable` | `R3/ArzelaAscoliTime.lean:937` | κ-threading layer 2 |
| `galerkinSpaceTimeExtraction_R3` | `R3/SteklovAverages.lean:941` | κ-threading layer 3 (pure delegation to layer 2) |
| `aubinLionsPackage_R3_of_timeCompactness` | `R3/AubinLionsLimitPassage.lean:1436` | κ-threading layer 4 (field assembly; consumes only per-datum leaves `galerkin_norm_le_u0`, curve continuity — index-generic) |
| `localRellichInput_of_frechetKolmogorov frechetKolmogorov_holds` | applied at `R3/AubinLionsAssembly.lean:79` | the concrete, unconditional, `T`-free spatial input; stages construct packages at every horizon with it |
| `exists_weak_representative_R3` | `R3/GoodRepresentative.lean:198` | **the coherence lever, verified in source**: conjunct 2 is `∀ t ∈ Icc 0 T, ∀ z : L2VF_R3, ⟪(galSeq (alPkg.φ n)).u t, z⟫ → ⟪v t, z⟫` — pointwise weak convergence at EVERY `t`, tests over the FULL ambient space, along `alPkg.φ` directly (no sub-extraction `ρ` — simpler than the torus). Plus: `v = alPkg.u` a.e. (the only a.e. link), ∀t norm bound `≤ ‖u₀‖`, `v 0 = u₀`, per-Galerkin-test equi-Lipschitz |
| `inner_tendsto_of_perball` | `R3/EnergyWeakLsc.lean:377` | the per-ball → full-space-weak upgrade (fixed-test ball/tail ε/3 split under the uniform `‖u₀‖` bound) — the reason the per-ball chain still yields full-space pins (§3) |
| `galerkin_norm_le_u0`, `galerkin_curve_continuous` | `R3/EnergyWeakLsc.lean:62/82` | `T`-independent per-datum leaves (valid on `Ici 0`) — exactly what growing-`T` stage recursion needs; **unchanged in P2′** |
| `galerkin_limit_passage_R3` | `R3/LimitPassage.lean:322` | 5-conjunct good-representative existential. Its proof HOLDS the ∀t weak pin (`hweak` from `exists_weak_representative_R3`, consumed at `LimitPassage.lean:344`) but **drops it from the conclusion** — P2′ re-exports it (exact torus-P2 situation) |
| `build_galerkin_package_R3_of_galSeq` | `R3/AubinLionsAssembly.lean:72` | rewired IN PLACE in P2′ (`κ := id`), signature kept — capstone untouched |
| `r3Domain` / `R3NSForms.core` / `r3Evolution` | `R3/SolutionInterfaces.lean:393/410/456` | `@[reducible]` `Galerkin.Domain` instance; `r3Evolution 𝔊 F` IS `(r3Domain 𝔊).evolution F.core` definitionally; `rfl`-lemmas `r3Domain_dissip`, `r3Domain_regMem` normalize the contract fields |
| `Galerkin.IsLerayHopfOn`, `.congr_Icc`, `.mono`, `WeakFormNS.mono/.congr_Icc`, `GlobalLerayHopfSolution` | `LerayHopf/Galerkin/GlobalContract.lean` | **verbatim reuse** (#195 P1). `congr_Icc` (`:289`) requires POINTWISE equality on `Icc 0 T` — exactly what §3 supplies |
| `nestedComp`, `diagExtraction`, `exists_diagonal_extraction`, `tendsto_diag_of_tendsto_stage` | `LerayHopf/Bochner/DiagonalExtraction.lean` | **verbatim reuse** (#195 P3): pure order theory, arbitrary target filter |
| `nested_extraction_factor` | `R3/SpatialCompactness.lean:162` | public; the tower-factorization workhorse reused by spike (b) |
| `R3TestApproxH1` / `nonempty_schwartzGalerkinBasis_H1` | `R3/SolutionInterfaces.lean:267` / `R3/GalerkinBasisH1.lean` | `htest`, needed ONLY by the `WeakFormNS` limit passage (per-horizon exit witness), not by the stage recursion; `T`-free, supplied with `B` |
| Torus templates: `P2ExitWitness`/`torus_kappaChain_exit`, `StageData`/`stageData`/`exists_diagonal_weakly_convergent_galSeq`, `exists_global_lerayHopf_torus3` | `Torus/KappaChainExit.lean:65/110`, `Torus/DiagonalGalerkin.lean`, `Torus/GlobalCapstone.lean:71` | **template-copied** (shape reused, bodies rewritten against ℝ³ interfaces) |

**κ-audit (this lane's analogue of the torus §1 22-declaration audit).** Declarations
whose signature mentions `AubinLionsPackage_R3` or sits in the sealed extraction chain,
re-read in source, each classified:

- **Gain `(κ, hκ)` — 20 declarations + 1 structure parameter:**
  chain wrappers (4): `diag_ae_subseq`, `u_lim_aestronglyMeasurable`,
  `galerkinSpaceTimeExtraction_R3`, `aubinLionsPackage_R3_of_timeCompactness`;
  `EnergyWeakLsc` (5): `kineticEnergy_lsc_bound`, `liminf_viscousFormSq_lt_top_ae`
  (private), `viscousFormSq_aestronglyMeasurable_of_memH1`, `viscous_pointwise_lsc`,
  `viscous_lsc_under_strongL2`;
  `AubinLionsLimitPassage` (7): `weakFormNS_galerkinTest_uniform_dominator` (private),
  `weakFormNS_galerkinTest_limit`, `bForm_galerkin_crude_dominator_bound` (private),
  `bForm_limit_convection_bound` (private), `weakFormNS_limit_G_integrable` (private),
  `weakFormNS_limit_diff_bound` (private), `weakFormNS_limit_passage`;
  `LimitPassage` (2): `energy_ineq_of_representative_R3` (private),
  `galerkin_limit_passage_R3` (also conclusion-strengthened, §5 P2′);
  `GoodRepresentative` (1): `exists_weak_representative_R3`;
  plus the structure parameter on `AubinLionsPackage_R3` (fields reindex
  `galSeq (φ n)` → `galSeq (κ (φ n))`).
- **Rewired in place, signature kept — 1:** `build_galerkin_package_R3_of_galSeq`
  (body instantiates `κ := id`, definitionally transparent; capstone unchanged).
- **Unchanged leaves:** `galerkin_norm_le_u0`, `galerkin_curve_continuous`,
  `perTest_lipschitz_R3`, `perTest_hasDerivAt_R3`, `inner_tendsto_of_perball`,
  `kineticEnergy_lsc_transfer` chain, `strong_trace_of_props_R3`,
  `galerkin_weakLimit_R3`, `perBall_ae_subseq`,
  `galerkin_spacetime_precompact_R3`/`_of_goodSampling`, the whole FK/Steklov spatial
  chain, `exists_lerayHopf_from_package_full_R3`, the capstone.

Index-usage shapes inside the bodies (same four shapes as the torus audit, verified on
the load-bearing consumers): (a) per-datum applications
`galerkin_norm_le_u0 … (alPkg.φ n) (galSeq (alPkg.φ n))` (index-generic → `κ (alPkg.φ n)`),
e.g. `GoodRepresentative.lean:219`, `LimitPassage.lean:81/97/110`,
`AubinLionsLimitPassage.lean:1503`; (b) growth `n ≤ alPkg.φ n` via `φ_mono.le_apply`
feeding eventual cutoffs (`hlevel`, `GoodRepresentative.lean:220`, consumed at `:258` as
`le_trans hn (hlevel n)`) — gains one `hκ.le_apply` hop; (c) `StrictMono` compositions
(`hκ.comp hφ`); (d) `u_initial`/trace uses along a strictly monotone index sequence.
All four shapes survive `φ n ↦ κ (φ n)`; spike (b) verifies this end-to-end on the two
deepest sealed layers, including the only structurally novel one (the Cantor tower).

---

## 2. Mathematical proof outline (ℝ³ lane) and final target

### 2.1 Frozen final target (D1; `lean-coder` transcribes verbatim)

**Quantifier-prefix decision: `∃ 𝔊, ∃ F, ∃ u, ∀ T`.** Stated honestly (codex gate
finding 4, §11): the finite-horizon capstone is `∀ T, ∃ 𝔊 F, Nonempty (…)` — scheme,
forms, and solution are chosen PER HORIZON. The global target is therefore **not a
quantifier-only rearrangement**: it carries two ADDITIONAL theorem obligations beyond
anything the finite theorem provides — (α) **uniform witness selection**: one `𝔊`/`F`
pair serving every horizon, discharged because the concrete construction is `T`-free
(`B, htest` from `nonempty_schwartzGalerkinBasis_H1`, `𝔊 := schemeOfBasis B`, `F` from
`r3_NSForms_exists (schemeOfBasis B)`, `galSeq := galSeq_R3_of_basis B F ν hν u₀` — no
per-`T` re-choice ever occurs, the dossier's "stages must fix `𝔊, F` once" requirement);
and (β) **one curve across all horizons**: a single `u` satisfying every horizon's
contract, discharged by the diagonal extraction + Step-4 representative coherence
(§2.2), which is the entire mathematical content of P3′/P4′. The consistency witness
`globalR3Capstone_implies_finite` proves ONLY the easy direction (global ⇒ finite,
via `ofIsOn`); nothing in this campaign treats it as evidence for the hard one.
Remaining grounds for the prefix itself: one curve `u` under a single contract family
forces one `𝔊` anyway (`IsLerayHopfOn (r3Domain 𝔊) …` mentions `𝔊`), and the `∃ 𝔊 F`
outer prefix is the weakest form making the statement well-formed while keeping the
finite-horizon release capstone byte-identical.

```lean
-- P1′, new file LerayHopf/R3/GlobalCapstone.lean
def GlobalR3CapstoneStatement : Prop := -- ALLOW_NAME: statement only (bare def : Prop, the frozen P4′ campaign target)
  ∀ (u₀ : L2Sigma_R3) (ν : ℝ), 0 < ν →
    ∃ (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊), ∃ u : Time → L2Sigma_R3,
      ∀ T : ℝ, 0 < T → Galerkin.IsLerayHopfOn (r3Domain 𝔊) F.core ν T u₀ u

abbrev GlobalLerayHopfSolutionFull_R3 (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (u₀ : L2Sigma_R3) :=
  Galerkin.GlobalLerayHopfSolution (r3Domain 𝔊) F.core ν u₀

theorem globalR3Capstone_implies_finite (hG : GlobalR3CapstoneStatement) : -- ALLOW_NAME: reserved term is the hypothesis Prop's name; the implication is fully proved
    ∀ (u₀ : L2Sigma_R3) (ν : ℝ), 0 < ν → ∀ T : ℝ, 0 < T →
      ∃ (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊),
        Nonempty (LerayHopfSolutionFull_R3 𝔊 F ν T u₀)
-- proof: Galerkin.LerayHopfSolution.ofIsOn, 3 lines (torus twin at Torus/GlobalCapstone.lean:46)

-- P4′, same file
theorem exists_global_lerayHopf_r3 (u₀ : L2Sigma_R3) (ν : ℝ) (hν : 0 < ν) :
    ∃ (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊), ∃ u : Time → L2Sigma_R3,
      ∀ T : ℝ, 0 < T → Galerkin.IsLerayHopfOn (r3Domain 𝔊) F.core ν T u₀ u

theorem exists_globalLerayHopfSolutionFull_r3 (u₀ : L2Sigma_R3) (ν : ℝ) (hν : 0 < ν) :
    ∃ (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊),
      Nonempty (GlobalLerayHopfSolutionFull_R3 𝔊 F ν u₀)

theorem globalR3Capstone : GlobalR3CapstoneStatement := -- ALLOW_NAME: reserved term is the frozen target Prop's name; this declaration is its full proof
  fun u₀ ν hν => exists_global_lerayHopf_r3 u₀ ν hν
```

Statement traps checked (role-contract checklist): forward-time only (all contract fields
`0 ≤ t`-guarded / `Icc`-restricted; the global curve's values below `0` never inspected);
∀t-vs-a.e. — energy inequality and trace are ∀t/limit statements as in the finite-horizon
contract, coherence is pointwise (§2.2 Step 4), only `energy_class`/AESM intrinsically
a.e. (as in the existing contract); no global-in-space compactness or tightness claim
appears anywhere in the target (the contract's five conjuncts are exactly the merged
finite-horizon ones); no `integral_undef` vacuity introduced (the transfer lemmas are the
#195 P1 ones, junk-value-proofed there); no hypothesis equivalent to the goal.

### 2.2 Proof outline (Steps 1–5, mirroring torus §2 with the ℝ³ substitutions)

Fix once: `⟨B, htest⟩` from `nonempty_schwartzGalerkinBasis_H1`, `𝔊 := schemeOfBasis B`,
`F` from `r3_NSForms_exists 𝔊`, `galSeq := galSeq_R3_of_basis B F ν hν u₀`,
`Rell := localRellichInput_of_frechetKolmogorov frechetKolmogorov_holds`. Each datum is
forward-global (`Galerkin.SolutionData` horizon-free bounds); `T` enters only at the
compactness layer.

**Step 1 (stages — nested extraction).** By recursion on `m` build `StageData_R3 m`:
per-stage fresh extraction `eStep m`, composed extraction `comp m = nestedComp e m`, stage
curve `U m`, invariant `∀ t ∈ Icc 0 (m+1), ∀ z : L2VF_R3, ⟪(galSeq (comp m j)).u t, z⟫ →
⟪U m t, z⟫`. The stage handle (P3′ deliverable, composed from P2′ outputs) is

```
exists_weakLimitCurve_R3_kappa :
  ∀ … (κ : ℕ → ℕ) (hκ : StrictMono κ), ∃ φ, StrictMono φ ∧ ∃ U : Time → L2Sigma_R3,
    ∀ t ∈ Icc 0 T, ∀ z : L2VF_R3, Tendsto (fun n => ⟪(galSeq (κ (φ n))).u t, z⟫) atTop (𝓝 ⟪U t, z⟫)
```

— body: κ-`aubinLionsPackage_R3_of_timeCompactness` (with `Rell`) then
κ-`exists_weak_representative_R3`; the returned `φ` is `alPkg.φ` (the pin runs along
`κ ∘ alPkg.φ` directly — no `ρ`). Stage `0`: `κ := id`, horizon `1`. Stage `m+1`:
`κ := comp m`, horizon `m+2`; `comp (m+1) := comp m ∘ eStep (m+1)`. Note the stage handle
needs `Rell` but NOT `htest` (no `WeakFormNS` at stage level). The invariant's test space
is the FULL `L2VF_R3` — stronger than the torus stage invariant (`L2Sigma` tests), because
`exists_weak_representative_R3`'s pin is already full-space.

**Step 2 (diagonal).** Verbatim `Bochner.DiagonalExtraction`: `δ k := diagExtraction e k`,
`tendsto_diag_of_tendsto_stage` transfers each stage invariant to the full diagonal.
Stage-curve coherence `U a t = U b t` on window overlaps by uniqueness of limits in ℝ per
test + subspace separation (`L2Sigma_R3_eq_of_forall_inner`, spike (a), compiled).
`W t := U (Nat.floor (max t 0)) t`.

**Step 3 (per-horizon contracts along the diagonal).** For each `m`, instantiate the P2′
typed exit witness (§6) at `T := (m:ℝ)+1`, `κ = φ₁ := δ`, family `fun k => galSeq (δ k)`,
filler `galSeq`, `htest`: obtain `w` with the five contract conjuncts for `w.v` and the pin
`∀ t ∈ Icc 0 Tₘ, ∀ z : L2VF_R3, ⟪(galSeq₁ (w.alPkg.φ n)).u t, z⟫ → ⟪w.v t, z⟫`, i.e. along
`δ ∘ w.alPkg.φ` — a sub-extraction of the diagonal. AESM of `w.v` recovered from
`w.alPkg.u_aestronglyMeasurable` + `w.v_ae` (torus P4 Node B pattern,
`Torus/GlobalCapstone.lean:88–92`).

**Step 4 (overlap coherence — pointwise, not a.e.).** Spike (a)'s compiled lemma
`r3_representative_diag_coherence`: the pin sequence is a sub-subsequence of the diagonal;
for each `z : L2Sigma_R3` the SAME real sequence `⟪(galSeq (δ (σ k))).u t, z⟫` converges to
both `⟪W t, z⟫` (Step 2 composed with `σ := w.alPkg.φ` monotone) and `⟪w.v t, z⟫` (pin,
whose `z` ranges over `L2VF_R3 ⊇ L2Sigma_R3`); `tendsto_nhds_unique` +
`L2Sigma_R3_eq_of_forall_inner` give **`w.v t = W t` for EVERY `t ∈ Icc 0 Tₘ`**. §3 states
why the per-ball structure does not obstruct this.

**Step 5 (transfer and monotone restriction).** `IsLerayHopfOn.congr_Icc` (pointwise
hypothesis — supplied by Step 4) moves the horizon-`Tₘ` contract from `w.v` to `W`;
for arbitrary `T > 0` take `m := ⌊T⌋₊` and restrict by `IsLerayHopfOn.mono`. Both lemmas
verbatim #195 P1 (`Galerkin/GlobalContract.lean:272/289`); `WeakFormNS`'s evolution
argument matches definitionally (`r3Evolution 𝔊 F ≡ (r3Domain 𝔊).evolution F.core`,
`@[reducible]`).

### 2.3 D2 conjunct table — every conjunct of the final target vs its ℝ³ source

Per-`T` content of the target: `Galerkin.IsLerayHopfOn (r3Domain 𝔊) F.core ν T u₀ W` =
the 5 proof fields of `Galerkin.LerayHopfSolution`, specialized by the `rfl`-lemmas
`r3Domain_dissip` / `r3Domain_regMem` (`R3/SolutionInterfaces.lean:433/437`):

| # | Conjunct (horizon `T`, curve `W`) | Source at horizon `Tₘ ≥ T` (witness `w`, curve `w.v`) | Transfer |
|---|---|---|---|
| 1 | `WeakFormNS ν T ((r3Domain 𝔊).evolution F.core) W` | `w.weak_eq : WeakFormNS ν Tₘ (r3Evolution 𝔊 F) w.v` (from `galerkin_limit_passage_R3` conjunct 2) — evolution defeq | `WeakFormNS.congr_Icc` (pointwise eq, Step 4) then `WeakFormNS.mono` |
| 2 | `∀ t ∈ [0,T]`, `½‖W t‖² + ∫₀ᵗ viscousFormSq_R3 ν (W s) ≤ ½‖u₀‖²` | `w.energy_ineq` (limit-passage conjunct 3, itself ∀t via `energy_ineq_of_representative_R3` — kinetic lsc + viscous Fatou, `LimitPassage.lean:51`) | pointwise eq on `[0,Tₘ]` (norm + `intervalIntegral.integral_congr`); restriction trivial (`T ≤ Tₘ`), via `congr_Icc`/`mono` |
| 3 | `Tendsto (W ·) (𝓝[≥] 0) (𝓝 u₀)` | `w.initial_trace` (limit-passage conjunct 4, `strong_trace_of_props_R3` from `v 0 = u₀` + ∀t bound + equi-Lipschitz) | germ transfer inside `congr_Icc` (`0 < Tₘ`); `T`-free |
| 4a | `∀ᵐ t ∂(vol.restrict (Icc 0 T)), memH1VF_R3 (W t)` | `w.energy_class_v.1` (limit-passage conjunct 5a) | pointwise eq + `ae_restrict_of_ae_restrict_of_subset` |
| 4b | `IntervalIntegrable (viscousFormSq_R3 ν (W ·)) volume 0 T` | `w.energy_class_v.2` (conjunct 5b) | pointwise eq on `uIoc` + `mono_set` |
| 5 | `AEStronglyMeasurable (W ·) (vol.restrict (Icc 0 T))` | `w.alPkg.u_aestronglyMeasurable` + a.e. link `w.v_ae` + pointwise eq `W = w.v` on `[0,Tₘ]` | `.congr` + `.mono_measure` (torus P4 Node B verbatim pattern) |

Every source is a MERGED ℝ³ theorem conjunct (re-verified in source at `455ca3b`) except
the P2′ pin re-export, whose proof already exists inside `galerkin_limit_passage_R3`
(it binds `hweak` at `LimitPassage.lean:344` and passes it to the energy step at `:394` —
P2′ only re-exports it through the existential, the exact torus-P2 move).

---

## 3. ℝ³ overlap coherence at the good-representative layer — why per-ball does not break it

The honest concern (issue #212 kill-criterion check + scout dossier §7): EVERYTHING in the
ℝ³ compactness tree is ball-restricted (`restrictToBall R`, Fréchet–Kolmogorov with no
tightness; full-space strong convergence is genuinely FALSE-in-general — mass can escape
to spatial infinity, `SteklovAverages.lean:902–909`). Does full-space ∀t weak-limit
uniqueness still hold for the coherence step?

**Yes, and no new lemma is needed.** Resolution, in three verified facts:

1. **The per-ball structure never reaches the coherence argument.** Coherence (Step 4)
   consumes only the pin exported by `exists_weak_representative_R3` — full-space weak
   pairings against fixed `z : L2VF_R3` at every `t` — not any per-ball datum. The
   per-ball → full-space-weak upgrade happens INSIDE `GoodRepresentative.lean` and is
   already merged: at a.e.-good times, `inner_tendsto_of_perball`
   (`EnergyWeakLsc.lean:377`) converts per-ball strong convergence + the uniform `‖u₀‖`
   bound into weak convergence against every fixed `z` (ball/tail ε/3 split — the TAIL OF
   THE FIXED TEST VECTOR decays, so escaping mass of `uₙ` is invisible to the pairing);
   the extension from the a.e.-good set to EVERY `t ∈ [0,T]` is the equi-Lipschitz
   Cauchy + density argument (`cauchySeq_of_equiLipschitz_of_dense`,
   `GoodRepresentative.lean:246–266`). Weak convergence against a fixed test is exactly
   the notion that survives lack of tightness; nothing stronger is ever claimed.
2. **Uniqueness needs only ℝ-limit uniqueness + subspace separation.** `w.v t = W t`
   follows from: the same real sequence cannot have two limits (`tendsto_nhds_unique`),
   plus `L2Sigma_R3` points are separated by `L2Sigma_R3` tests (test with the difference,
   `inner_self_eq_zero` — spike (a) `L2Sigma_R3_eq_of_forall_inner`). Neither ingredient
   mentions balls, norms of `uₙ`, or compactness.
3. **The pin's test space is the full ambient `L2VF_R3`** (verified at
   `GoodRepresentative.lean:206–208`) — strictly more than the `L2Sigma_R3` tests
   separation needs, and along `alPkg.φ` directly (no torus-style sub-extraction `ρ`).

Compiled evidence — and its honest scope (codex finding 2, §11): spike (a)
(`LerayHopf/Scratch/R3StageCoherence.lean`) proves the coherence STEP — the coherence
core and the two-representatives-on-nested-windows overlap form — against the real ℝ³
types, sorry-free, kernel-trio pins (§7), with no a.e.-in-time leak. That discharges the
step **conditionally**: its two hypotheses are exactly the hard outputs still to be
produced — `hW` (diagonal invariant) is P3′'s stage-handle obligation, and `hpin`
(everywhere-weak pin against the extracted family) is P2′'s re-export obligation; TODAY
`galerkin_limit_passage_R3` still drops the pin from its conclusion, and `R3KappaSeed`
supplies only per-ball a.e.-time convergence at the tower layer. The coherence risk is
therefore retired as mathematics but NOT yet as a compiled pipeline; §6 gates P3′/P4′
dispatch on compiled artifacts instantiating the EXACT `hW`/`hpin` types.

What WOULD have killed the lane (checked first, per the issue): an a.e.-in-`t`-only weak
conjunct in the limit-curve theorem. Verified NOT the case — conjunct 2 of
`exists_weak_representative_R3` is ∀t (the only a.e. statements are the `v = alPkg.u`
identification and the energy-class conjunct, mirroring the torus exactly; negative
control: `kineticEnergy_lsc_bound`'s docstring confirms the package-level bound is
a.e.-only and the ∀t upgrade lives in `GoodRepresentative`).

---

## 4. κ-threading design through the four sealed wrapper layers

The root primitive is already refine-capable; the chain seals it at `diag_ae_subseq`.
Design (validated by compiled spike (b) on the two deepest layers):

| Layer | Declaration | Change | Mechanism |
|---|---|---|---|
| 1 | `diag_ae_subseq` | `+ (κ, hκ)`; conclusion index `φ n` → `κ (φ n)` | **Pre-composition seeding**: every tower step feeds `κ ∘ Φ k` (StrictMono by `hκ.comp`) to `perBall_ae_subseq`; the tower maps `Φ`/`ρ` and their factorization (`nested_extraction_factor`) are untouched because `κ` stays OUTSIDE the tower, at datum-index positions only. The external seed and the per-ball Cantor tower compose exactly here: `Φ 0 = id` under the seed means level-`k` convergence holds along `κ ∘ Φ (k+1)`, and the diagonal factorization is applied inside `κ` by `congrArg`-rewriting (spike (b), verbatim-body port, compiled) |
| 2 | `u_lim_aestronglyMeasurable` | `+ (κ, hκ)`; conclusion `κ (φ n)` | passes `κ ∘ φ` (with `hκ.comp hφ`) to `galerkin_weakLimit_R3`, which is extraction-generic and needs **no change** (spike (b) layer 2, compiled) |
| 3 | `galerkinSpaceTimeExtraction_R3` | `+ (κ, hκ)`; conclusion `κ (φ n)` | pure delegation to layer 2 (byte-level wrapper) |
| 4 | `aubinLionsPackage_R3_of_timeCompactness` + `AubinLionsPackage_R3` | structure gains parameter `κ` (after `galSeq`); builder gains `(κ, hκ)`; fields reindex to `galSeq (κ (φ n))` | field assembly uses only index-generic per-datum leaves (`galerkin_norm_le_u0` at `κ (φ n)`, curve continuity per index, dominated convergence) — shape-(a) edits only |

Torus §3 design decisions adopted unchanged: **base + κ form** (base family stays a
parameter; reindexed family = `galSeq ∘ κ`; subsequent extraction consumed as `κ ∘ φ`);
`hκ` is a SIDE hypothesis, never a structure field (κ = id instance stays definitionally
transparent for the in-place rewiring of `build_galerkin_package_R3_of_galSeq` and the
byte-identical capstone); downstream `alPkg.φ`-consumers (the 15 audited declarations, §1)
gain `(κ, hκ)` with body edits of the four audited shapes only. Effective-map
strictness/cofinality via the torus finding-3 lemma pattern where needed
(`hκ.comp alPkg.φ_mono`, `le_apply` chains).

### 4.1 Semantic κ-protection (codex gate findings — pass-1 F1 and pass-2 1–2 dispositions)

Compilation alone does not prove every load-bearing limit uses the reindexed sequence:
with a TOTAL base family, a stale `galSeq (alPkg.φ n)` where `galSeq (κ (alPkg.φ n))`
is meant stays well-typed. **Correction of record (pass-2 finding 2, accepted):** the
pass-1 version of this section rejected "type-level protection" on the ground that it
would fork the datum type — that conflated changing the Galerkin DATUM type with
parameterizing the PACKAGE and using a dependent extracted FAMILY. The merged torus
production code achieves type-level κ-protection with the datum type UNCHANGED
(`Torus/SolutionInterfaces.lean:342`: `AubinLionsPackage F ν T u₀ galSeq κ` — `κ` a
structure parameter, convergence fields typed at `galSeq (κ (φ n))`; verified in
source), and §6 already mirrors that pattern. The design is therefore re-based on the
torus precedent:

- **PRIMARY protection — type-level, torus-style (ADOPTED).** Three type-guarded
  surfaces make stale indices unrepresentable wherever the sequence appears:
  1. `AubinLionsPackage_R3` gains the structure parameter `κ` (after `galSeq`, §4
     layer 4) and its convergence fields (`strong_convergence`,
     `strong_convergence_ae`) are TYPED at `galSeq (κ (φ n))` — a builder or consumer
     cannot state or use a package-level limit at a stale index; the field type
     rejects it. `AubinLionsPackage_R3.effective_strictMono :
     StrictMono (fun n => κ (φ n))` (torus scratch twin already pin-gated) is the
     composition lemma consumers go through.
  2. The four sealed-layer conclusions are typed at `κ (φ n)` (spike (b) compiled
     this for the two deepest layers, including the Cantor tower), and the
     strengthened `galerkin_limit_passage_R3` pin conjunct (below) is typed at
     `κ (alPkg.φ n)`. A stale variant of any of these statements is not merely
     against-convention — it is UNPROVABLE, because the only limit facts available to
     its proof are the seeded package fields (for `κ` a variable, convergence along
     an un-seeded subsequence is not derivable from them).
  3. The exit witness (§6) takes the DEPENDENT extracted family
     `galSeq₁ : ∀ k, GalerkinSolutionData_R3 𝔊 F ν u₀ (φ₁ k)` with the mandatory
     `transport` field, and its `pin` is stated against `galSeq₁` itself — the torus
     `P2ExitWitness` invariant verbatim.
- **Mechanical assertion of the primary invariant — the exact-shape gate (pass-3
  finding 1).** The invariant above is NOT left as prose: it has a committed,
  independently executable check. `LerayHopf/Scratch/KappaShapeGate.lean` (compiled
  and pin-gated AT B0, inside `check-scratch-pins.sh`) re-states each κ-critical
  declaration surface verbatim — with the mode map `κ` a FREE variable — and proves
  it by the bare field projection (no `by`, no rewriting). Elaboration succeeds only
  if the projected field's declared type literally carries `galSeq (κ (φ n))`: for
  free `κ`, a stale field `galSeq (p.φ n)` does not unify with the probe's
  `galSeq (κ (p.φ n))`, so a "dummy κ" package (parameter present but unapplied) or
  any bare-index convergence surface FAILS the probe at compile time. Two committed
  gate modules, both green at B0 inside `check-scratch-pins.sh`:
  `KappaShapeGate.lean` (mechanism demonstration against the compiled torus scratch
  model) and — the pass-4 upgrade, replacing the pass-3 "spec now, write in P2′"
  deferral — **`LerayHopf/Scratch/R3ShapeGate.lean`, the FULL ℝ³-surface twin,
  compiled at B0**: it declares the frozen design MIRROR of the two κ-critical P2′
  declarations (the κ-parameterized `AubinLionsPackage_R3` with BOTH ball-restricted
  convergence fields transcribed byte-faithfully from the merged production
  structure, and the §6 `R3KappaChainExitWitness`) under the production-intended
  unqualified names inside `Scratch212`, and probes: both convergence fields (a₁/a₂),
  limit-curve measurability (a₃), the effective `le_apply` bound (b, the
  category-(iii) coupling below), the frozen limit-passage pin-conjunct Prop
  `R3LimitPassagePinConjunct` with its defeq probe (c), witness `transport` (d₁),
  witness pin against the dependent family (d₂), and the alPkg linkage — the
  witness package's convergence field typed at `base (φ₁ (alPkg.φ n))` (d₃) — plus
  transport-usability linkage smokes (`pin_base`,
  `alPkg_convergence_dependent_family`). Because the mirror compiles against the
  REAL merged ℝ³ interfaces, the P2′ structure design is type-checked TODAY, and
  the P2′ re-point is mechanical (§6 clause 6): delete the mirror declarations, add
  the production import — zero changes to any probe statement; a probe failing
  after the swap is a kill-criterion event. Sealed-layer coverage map: layers 1–2
  κ-threaded conclusions are compiled and pinned in spike (b) itself
  (`R3KappaSeed`); layer 3's conclusion is the layer-2 shape (pure delegation);
  layer 4's output type IS the probed mirror package. The "not negotiable"
  requirement is thereby checker-enforced over the full κ-critical surface, not
  prose.
- **Production coupling (pass-5 findings 1–2 — the mirror is now TIED to the live
  production surface, not just compiled beside it).** The mirror discipline above
  freezes and type-checks the P2′ design, but by itself never APPLIES a production
  declaration — production could drift (or a future layer stay bare-indexed) while
  every mirror probe stayed green. The third committed gate module,
  **`LerayHopf/Scratch/R3ProductionCoupling.lean`** (checker-wired, kernel-trio
  pinned), closes this with probes that CONSUME the actual production declarations,
  compiled at B0 at the κ-less production surface:
  (a) bidirectional field-by-field bridges `AubinLionsPackage_R3.ofProduction` /
  `.toProduction` between the production package and the mirror at `κ := id` —
  together they assert field-set + field-type equality up to the single designed
  κ-insertion, so package drift in EITHER direction breaks the B0 build;
  (b) `r3LimitPassage_production_exact_shape` — a bare application of the actual
  `galerkin_limit_passage_R3` restating its current 5-conjunct conclusion verbatim;
  (c) `r3LimitPassagePin_production_source` — consumes the actual
  `exists_weak_representative_R3` (the declaration the limit passage draws its
  representative from) and lands its weak-convergence conjunct in the frozen
  `R3LimitPassagePinConjunct` at `κ := id` through the compiled bridge: the pin
  conjunct P2′ must append is production-DERIVABLE today, in frozen-Prop form;
  (d) bare applications of the actual sealed layer-1/2 declarations
  (`diag_ae_subseq`, `u_lim_aestronglyMeasurable`,
  `galerkinSpaceTimeExtraction_R3`), conclusions restated verbatim — production
  PROBING, counted separately from the standalone seeded feasibility proofs in
  `R3KappaSeed`; and (e) seed↔production id-coherence probes: the frozen κ-generic
  seeded statements instantiated at `κ := id` prove the production conclusions
  VERBATIM (definitional `id`-collapse only), so the P2′ κ-threading is exactly the
  frozen seed statement, not a redesign; and (f) **free-κ statement guards (pass-6
  finding 2):** the seeded κ-generic conclusions RESTATED VERBATIM with `κ` FREE
  (`diag_ae_subseq_seeded_free_kappa_exact_shape`,
  `spacetime_extraction_seeded_free_kappa_exact_shape`), proved by direct
  application of the seeded theorems at that free `κ`/`hκ`. The id-coherence probes
  in (e) would still elaborate if the seeded statements were weakened to ignore `κ`
  while keeping an `id`-specializable form; for FREE `κ`, a degenerated
  `galSeq (φ n)` does not unify with the frozen `galSeq (κ (φ n))`, so (f) fails to
  elaborate under any κ-dropping weakening — and (f)'s conclusion texts are the
  very texts the §6 clause 6 (γ) P2′ couplings carry, now compiled at B0 instead
  of frozen by reference only. The frozen FULL strengthened limit-passage
  conclusion (production 5 conjuncts + pin appended) is committed as
  `R3StrengthenedLimitPassageConclusion` in `R3ShapeGate.lean` with a compiled
  pin-projection probe; the P2′ bare-application coupling against it is frozen in
  §6 clause 6 (it can only compile once production's conclusion carries the pin —
  which is exactly what it will detect).
- **Coverage of sequence-free consumers (pass-2 finding 1, taxonomy CORRECTED at
  pass-3 finding 2).** `weak_eq`, `energy_ineq`, `initial_trace`, and the
  energy-class conjuncts mention only the limit curve, so their statements cannot
  carry the index — the question is whether a HELPER behind them can go stale. The
  pass-2 version claimed a two-category taxonomy was exhaustive; codex pass-3
  exhibited a third category it omitted. The corrected taxonomy of what any helper
  in the chain can consume:
  (i) **limit facts** — available exclusively as package fields / sealed-layer
  conclusions / the pin conjunct, all type-guarded at the effective index by the
  primary protection above (a stale limit fact is underivable, not just unproven);
  (ii) **per-datum facts** (`galerkin_norm_le_u0`, curve continuity, ODE identities)
  — index-GENERIC true statements about genuine Galerkin data: applying one at a
  stale index yields a true-but-useless premise, never a false one;
  (iii) **κ-sensitive index-selection facts** (pass-3 category, RE-SCOPED at pass-4
  finding 2 — the pass-3 version wrongly swept `transport` and measurability into
  this category and imposed one blanket derivation rule; corrected here): facts
  about the extraction MAP that SELECT the datum index a leaf fires at — the
  `hlevel`-style growth bound (`∀ n, n ≤ alPkg.φ n`, used by `GoodRepresentative`
  to select the per-test Lipschitz/cutoff leaf), strictness/cofinality of the
  effective sequence, eventual-cutoff bounds. These are neither limit facts nor
  single-datum truths: a stale pairing — a bound derived for the bare `φ` while
  the data the chain consumes runs at `κ ∘ φ` — stays WELL-TYPED and silently
  selects the wrong index, so the (i)+(ii) soundness argument does not cover it.
  **Coupling rule (mandatory, P2′, applies to THIS category only):** every
  category-(iii) fact is DERIVED from the package's effective-map surface —
  `AubinLionsPackage_R3.effective_strictMono`, its `tendsto_atTop`/`le_apply`
  corollaries at the COMPOSED map — never from the bare `φ_mono` field or a
  free-floating `hφ`; e.g. `GoodRepresentative`'s `hlevel` becomes
  `∀ n, n ≤ κ (alPkg.φ n)` (shape-gate probe compiled at B0, torus and ℝ³ both).
  Enforcement: the clause-5 audit patterns flag bare-`φ` category-(iii)
  consumption, and the clause-3 smoke/production test exercises a category-(iii)
  path at `κ := Nat.succ`, not only total-family applications at `alPkg.φ`;
  (iv) **family-linkage facts** (pass-4 finding 2: split OUT of (iii) — its
  derivation rule is DIFFERENT, and the pass-3 blanket rule contradicted the §6
  design itself): the `transport` equalities tying the dependent family to the
  base family (`∀ k, base (φ₁ k) = galSeq₁ k`). Their honest proof source is the
  embedding construction — `extendReindexedFamily_R3`'s `_apply` lemma applied
  with INJECTIVITY of the supplied extraction (`hφ₁.injective`), exactly as the
  compiled torus `extendReindexedFamily_apply` does — or direct consumption of the
  witness's `transport` FIELD; they are NOT derivable from, and must not be
  claimed to derive from, `effective_strictMono`. Enforcement is type-level and
  probed: `transport` is a mandatory witness field (an unlinked family is
  unrepresentable), the shape gate projects it (`r3WitnessShape_transport`), and
  the linkage smokes (`pin_base`, `alPkg_convergence_dependent_family`) certify it
  genuinely transports;
  (v) **index-free ambient inputs** (pass-4 finding 2, listed so the enumeration
  is honest): `htest : R3TestApproxH1 𝔊`, the `LocalRellichInput`/
  Fréchet–Kolmogorov chain inputs, positivity side conditions (`hν`, `hT`). These
  mention no Galerkin index and no extraction map; κ-threading cannot stale them,
  so they carry NO coupling obligation. (Package-limit measurability and
  continuity, which pass-3 misfiled under (iii), are category (i): they are
  package FIELDS, type-guarded and probed — `r3PackageShape_u_aestronglyMeasurable`.)
  Sequence-free conclusions proved from (i)+(ii)+coupled-(iii)+probed-(iv)+(v) are
  sound regardless of helper internals; the enforcement is in the TYPES of (i),
  the genericity of (ii), the checked derivation discipline of (iii), and the
  mandatory probed field of (iv).
- **Defense-in-depth (kept, demoted from primary to belt-and-suspenders):**
  1. **Smoke gate (§6 clause 3, WIDENED at pass-3 finding 2).** A production smoke
     theorem at a genuinely nontrivial seed (`κ := Nat.succ` — StrictMono, provably
     ≠ `id`) threads the FULL path package construction → every limit-passage
     consumer → pin re-export → `r3_kappaChain_exit`, then CONSUMES the witness via
     `transport` down to a pin on `galSeq (w.alPkg.φ k + 1)` — catching at P2′ any
     statement-level staleness that slipped past the types. Widening: the smoke
     file must ADDITIONALLY exercise a category-(iii) path at the nonidentity seed —
     apply the production selection helper (the `GoodRepresentative`-side consumer
     of `hlevel`) with the effective bound `∀ n, n ≤ w.alPkg.φ n + 1` derived from
     `effective_strictMono`, so the extraction-dependent pairing itself is exercised
     at `κ ≠ id`, not only total-family applications at `alPkg.φ`.
  2. **Automated stale-index audit (§6 clause 5, patterns EXTENDED at pass-3
     finding 2).** `scripts/check-kappa-effective-index.sh`, shipped IN THE P2′ PR:
     fails closed on (a) any application of a total family at a bare extraction
     index (`galSeq (alPkg.φ`, `base (alPkg.φ`, `fill (alPkg.φ` and spacing
     variants) in the κ-generic files, AND (b) bare-`φ` category-(iii) consumption
     sites in those files: `alPkg.φ_mono` used outside the effective-map composition
     lemmas, and `≤ alPkg.φ` / `.φ_mono.le_apply`-shaped bounds not phrased at the
     composed index. Legitimate fixed-horizon `κ := id` sites (and the composition
     lemmas' own defining uses of `φ_mono`) carry a same-line
     `-- KAPPA_ID_SITE: <reason>` allowlist marker, mirroring the ALLOW_NAME
     mechanism. It is specified now but written in P2′ because its file/pattern
     surface IS P2′'s diff — a deferral that is admissible ONLY because the
     exact-shape gate above exists and runs from B0 (pass-3 overall note); the
     audit is residual-hygiene on top of a mechanically asserted invariant, not
     the assertion itself.
- Why not full κ-compilation at B0 (unchanged): threading the 20-declaration audit
  surface IS phase P2′ (8 files); B0's spike (b) retires the structural risk, the
  type-level invariant + clauses above gate the semantic risk fail-closed before any
  P3′/P4′ dispatch.

**P2′ additionally strengthens `galerkin_limit_passage_R3`'s conclusion** with the pin
conjunct its proof already holds:

```
… ∧ (∀ t ∈ Set.Icc (0:ℝ) T, ∀ z : L2VF_R3,
      Tendsto (fun n => ⟪((galSeq (κ (alPkg.φ n))).u t : L2VF_R3), z⟫) atTop
        (𝓝 ⟪(u t : L2VF_R3), z⟫))
```

(along `alPkg.φ` directly — no `ρ` existential, simpler than torus P2's re-export).
Fixed-horizon consumers rewire with `κ := id`; `exists_lerayHopf_r3` and
`LerayHopfSolutionFull_R3` stay byte-identical.

---

## 5. Phase decomposition (PR-sized, tier table, kill criteria)

Model pool: **fable and opus only** (owner cost directive 2026-07-28: opus for
coder/prover wherever justifiable; fable reserved for genuinely-new-math nodes).
**Tier justification:** every genuinely-new-math node of this lane is retired at B0 with
compiled evidence — the coherence core (spike (a)) and the κ-seeding of the only
structurally novel wrapper, the Cantor tower (spike (b)); torus P3/P4, which were
fable-tier because the recursion/assembly pattern was then novel, are now MERGED templates
(`DiagonalGalerkin.lean`, `GlobalCapstone.lean`) this lane mirrors declaration-for-
declaration. Hence all coder/prover nodes are **opus**, with D4 escalation to fable
(2 failed attempts or ~1.5h thrash, evidence attached) explicitly available; the expected
escalation points are flagged per phase.

Dependencies: P1′ ∥ P2′ (independent); P3′ needs P2′ (exit gate green); P4′ needs
P1′+P2′+P3′. One PR per phase, target `dev/v0.2.0`, per-phase gates identical to #195
(codex adversarial `xhigh` statement gate before proof dispatch, pr-reviewer +
modularity-reviewer, broker codex PR review, §8 evidence; append-only live axiom pins).

| Phase | Sub-issue title (`Parent: #212`) | Content | Files | Coder | Prover | Kill criterion (→ back to architect) |
|---|---|---|---|---|---|---|
| **P1′** | `[#212-A] ℝ³ global contract instantiation: frozen capstone target + consistency witness` | §2.1 `GlobalR3CapstoneStatement` + `GlobalLerayHopfSolutionFull_R3` + `globalR3Capstone_implies_finite` (verbatim). (The `check-scratch-pins.sh` extension originally slated here was pulled forward into the B0 commit itself — codex finding 3, §11: 4 targets / 14 pins; extended at pass-3 with the exact-shape gate module, at pass-4 with the full ℝ³ mirror gate + source-manifest equality, and at pass-5 with the production-coupling module + source-discipline rejections, reaching 7 targets / 52 pins — checker green at B0) | new `LerayHopf/R3/GlobalCapstone.lean` (statement layer only) | opus | opus (one 3-line proof) | `implies_finite` not closable via `ofIsOn` (would mean the contract equivalence broke — architect) |
| **P2′** | `[#212-B] κ-generalize the ℝ³ compactness chain + pin re-export + typed exit witness` | §1 κ-audit surface: 20 declarations + `AubinLionsPackage_R3` parameter + `build_galerkin_package_R3_of_galSeq` rewired `κ := id`; strengthen `galerkin_limit_passage_R3` conclusion with the §4 pin conjunct; `AubinLionsPackage_R3.effective_strictMono` (§4.1 clause 1); NEW `extendReindexedFamily_R3` (takes an explicit filler family — ℝ³'s total ODE layer is scheme-specific, so the filler is a parameter, not hardwired; deviation from torus noted §6), `R3KappaChainExitWitness`, `r3_kappaChain_exit`, the §4.1 smoke theorem at `κ := Nat.succ` (widened: category-(iii) exercise included), the §4.1 stale-index audit script `check-kappa-effective-index.sh`, and the §6 clause-6 RE-POINT of the B0-committed shape-gate mirror `LerayHopf/Scratch/R3ShapeGate.lean` (delete the mirror declarations + add the production import; ZERO probe-statement changes — probe failure after re-point is a kill-criterion event). **Exit gate (§6, SIX clauses): typed artifact + live pin, exact-hpin coupling, widened smoke theorem, scratch-pin checker green, stale-index audit green, shape-gate re-point green.** P3′/P4′ dispatch blocked until all six green | `ArzelaAscoliTime, SteklovAverages, AubinLionsLimitPassage, SolutionInterfaces, EnergyWeakLsc, GoodRepresentative, LimitPassage, AubinLionsAssembly` + new `LerayHopf/R3/KappaChainExit.lean` | opus | opus (mechanical re-threading; spike (b) covers the only novel layer) | any statement fails to typecheck as designed; >2 proof bodies need non-mechanical re-proving; the release capstone's statement would change; the exit witness cannot be reached without a statement change |
| **P3′** | `[#212-C] ℝ³ stage recursion + diagonal weak limit W` | stage handle `exists_weakLimitCurve_R3_kappa` (§2.2 Step 1, composition of two P2′ outputs); `StageData_R3`, `stageData_R3`, `stageData_R3_comp_eq_nestedComp`, `stageData_R3_diag_tendsto`, `stageData_R3_U_coherent` (promotes spike (a)'s separation lemma to production), `diagWeakLimit_R3`, `exists_diagonal_weakly_convergent_galSeq_R3` (invariant over `z : L2VF_R3` tests, §2.2 Step 2). Reuses `Bochner.DiagonalExtraction` VERBATIM (zero new order theory) | new `LerayHopf/R3/DiagonalGalerkin.lean` | opus | opus — template mirror of merged `Torus/DiagonalGalerkin.lean`; **flagged D4 escalation point**: the `Nat.rec` stage carrier (torus needed fable when the pattern was novel) | stage recursion not expressible as designed; stage-limit coherence fails from `L2Sigma_R3` tests; the stage handle needs data P2′ does not export |
| **P4′** | `[#212-D] ℝ³ global capstone: exists_global_lerayHopf_r3` | per-horizon exit witnesses at `κ := δ` over `fun k => galSeq (δ k)` (filler `galSeq`, `htest` from `nonempty_schwartzGalerkinBasis_H1`); Step-4 coherence via the compiled spike-(a) lemma shape; `congr_Icc`/`mono` assembly; §2.1 capstones + fold `globalR3Capstone`; live pins (append-only); docs (`claims-and-scope.md`, `architecture.md`, `STATUS.md`) | `LerayHopf/R3/GlobalCapstone.lean` (fills the P1′ file) + docs | opus | opus — node-for-node mirror of merged `Torus/GlobalCapstone.lean` with spike (a) compiled; **flagged D4 escalation point**: Node C coherence assembly | the pin is insufficient for some conjunct's transfer (must NOT be patched by weakening — architect); defeq mismatch `r3Evolution` vs `(r3Domain 𝔊).evolution F.core` that `rfl`-lemmas cannot bridge |

Escalation per D4 with evidence attached; `#print axioms` / `scripts/check-axioms-live.sh`
evidence for every sorry-free claim (D7). Codex gate points: after P1′ statements, after
the P2′ signature diff, after P3′ statements, after P4′ proofs (before PR).

---

## 6. Typed exit gate (P2′) — ℝ³ analogue of `P2ExitWitness`

Frozen shape (production file `LerayHopf/R3/KappaChainExit.lean`; since the pass-4
remediation the design below is no longer doc-only — it is COMPILED at B0 as the
mirror declarations of `LerayHopf/Scratch/R3ShapeGate.lean` (clause 6), type-checked
against the real merged ℝ³ interfaces and probed; the production artifact still goes
straight to production under the P2′ PR, per the torus `KappaChainExit.lean`
precedent, and must match the mirror on re-point):

```lean
structure R3KappaChainExitWitness (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν T : ℝ) (u₀ : L2Sigma_R3) (φ₁ : ℕ → ℕ)
    (galSeq₁ : ∀ k, GalerkinSolutionData_R3 𝔊 F ν u₀ (φ₁ k)) where
  base : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n
  transport : ∀ k, base (φ₁ k) = galSeq₁ k          -- MANDATORY (unlinked family unrepresentable)
  alPkg : AubinLionsPackage_R3 𝔊 F ν T u₀ base φ₁   -- κ-parameterized structure (P2′)
  energy_class_pkg :
    (∀ᵐ t ∂(volume.restrict (Set.Icc (0:ℝ) T)), memH1VF_R3 (alPkg.u t : L2VF_R3)) ∧
      IntervalIntegrable (fun s => viscousFormSq_R3 ν (alPkg.u s : L2VF_R3)) volume 0 T
  v : Time → L2Sigma_R3
  v_ae : ∀ᵐ t ∂(volume.restrict (Set.Icc (0:ℝ) T)), v t = alPkg.u t
  weak_eq : WeakFormNS ν T (r3Evolution 𝔊 F) v
  energy_ineq : ∀ t, 0 ≤ t → t ≤ T →
    (1/2 : ℝ) * ‖(v t : L2VF_R3)‖ ^ 2 + ∫ s in (0:ℝ)..t, viscousFormSq_R3 ν (v s : L2VF_R3)
      ≤ (1/2 : ℝ) * ‖(u₀ : L2VF_R3)‖ ^ 2
  initial_trace : Filter.Tendsto (fun t => (v t : L2VF_R3))
    (nhdsWithin 0 (Set.Ici 0)) (nhds (u₀ : L2VF_R3))
  energy_class_v :
    (∀ᵐ t ∂(volume.restrict (Set.Icc (0:ℝ) T)), memH1VF_R3 (v t : L2VF_R3)) ∧
      IntervalIntegrable (fun s => viscousFormSq_R3 ν (v s : L2VF_R3)) volume 0 T
  /-- Everywhere-weak pin, phrased against `galSeq₁` ITSELF, along `alPkg.φ` directly
  (ℝ³ simplification: `exists_weak_representative_R3` pins along `alPkg.φ` with no
  sub-extraction `ρ` — the torus witness's `ρ`/`ρ_mono` fields are ABSENT by design). -/
  pin : ∀ t, t ∈ Set.Icc (0:ℝ) T → ∀ z : L2VF_R3,
    Filter.Tendsto (fun k => inner (𝕜 := ℝ) (((galSeq₁ (alPkg.φ k)).u t : L2VF_R3)) z)
      Filter.atTop (nhds (inner (𝕜 := ℝ) ((v t : L2VF_R3)) z))

theorem r3_kappaChain_exit (𝔊 : R3GalerkinScheme) (F : R3NSForms 𝔊)
    (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T) (u₀ : L2Sigma_R3)
    (fill : ∀ n, GalerkinSolutionData_R3 𝔊 F ν u₀ n)   -- filler family, see note
    (htest : R3TestApproxH1 𝔊)
    (φ₁ : ℕ → ℕ) (hφ₁ : StrictMono φ₁)
    (galSeq₁ : ∀ k, GalerkinSolutionData_R3 𝔊 F ν u₀ (φ₁ k)) :
    Nonempty (R3KappaChainExitWitness 𝔊 F ν T u₀ φ₁ galSeq₁)
```

Torus-deviation note (argued, not silent): `extendReindexedFamily`'s off-subsequence
filler is a PARAMETER (`fill`) rather than a hardwired canonical family, because ℝ³'s
total Galerkin ODE layer (`galerkinSolutionData_unconditional`) exists over
`schemeOfBasis B`, not over an abstract `𝔊`. P4′ instantiates `fill := galSeq` (the one
fixed family), so no generality is lost and the `transport` field still makes an unlinked
implementation unrepresentable. `hν` is consumed by the κ-chain builders; `hT` by the
package; `htest` only by the `WeakFormNS` stage.

**Exit-gate condition (P3′/P4′ dispatch blocker) — six clauses, all mandatory:**

1. a production `r3_kappaChain_exit` compiled sorry-free, guarded by a live pin in
   `scripts/check-axioms-live.sh` (append-only);
2. the witness `pin` field instantiates the EXACT `hpin` hypothesis type of spike (a)'s
   `r3_representative_diag_coherence` (finding 2, §11): same `∀ t ∈ Icc 0 T, ∀ z :
   L2VF_R3, Tendsto …` shape, against `galSeq₁` itself along `alPkg.φ` — checked by a
   compiled coupling lemma applying the spike-(a) statement (promoted in P3′) to the
   witness output, not by visual inspection;
3. the §4.1 smoke theorem at `κ := Nat.succ` compiled sorry-free: full-path threading
   plus witness consumption via `transport`, concluding the base-family pin at the
   composed effective index `w.alPkg.φ k + 1`, AND (pass-3 widening) the
   category-(iii) exercise — the production selection helper applied at the
   nonidentity seed with the effective bound derived from `effective_strictMono`;
4. `scripts/check-scratch-pins.sh` green at the B0-extended enumeration (pass-7
   state: 7 targets / 54 pinned surface declarations inside a TOTALLY PINNED
   187-constant manifest, evidenced by the **STATIC OLEAN READER**
   `scripts/scratch_reader.lean`). The evidence-channel lineage, each step closing
   the previous step's execution surface: text/regex manifest + build-log pin
   parsing (passes 4–5, RETIRED at pass-6 — text scanning cannot enumerate an
   elaborated environment, and the build-log channel was spoofable); the
   elaborated-environment manifest `scripts/scratch_manifest.lean` (pass-6,
   RETIRED at pass-7 — importing a target EXECUTES it: a target-registered
   command elaborator or `initialize` block runs inside the manifest process and
   could fake the evidence block, codex pass-7 finding 2). The pass-7 reader
   imports ONLY `Lean` and reads the target `.olean` files as DATA
   (`Lean.readModuleData`): zero elaboration of target code, zero initializer
   execution, zero imported syntax/command extensions — no target-authored code
   executes anywhere in the evidence path. Its evidence sources are all
   compiler-written olean data: `ModuleData.constNames`/`constants` (a
   declaration cannot exist without appearing there, whatever its spelling —
   Unicode names, anonymous instances, macro-generated forms included), the
   toolchain's own precomputed per-declaration axiom closures
   (`exportedAxiomsExt` entries, the exact data behind `#print axioms`; 1:1 with
   `constNames`, a missing entry is a violation), exact generated-name
   provenance (`projectionFnInfoExt`/`auxRecExt` entries), per-declaration
   STATEMENT type-hashes, and the free-κ guards' proof-term dependencies
   (DEPGUARD lines, clause 6 rule (δ)). The checker snapshots the reader, the
   fixture self-test, and the frozen manifest to a private temp dir BEFORE the
   untrusted `lake build` step (build-time elaboration can run arbitrary IO),
   then asserts fail-closed: fresh rebuild of every target; the
   collision-fixture self-test (`LerayHopf/Scratch/GateFixture.lean`: compiled
   hand-written declarations with generated-/internal-looking names —
   `P.ibelow`, `C.mk.noConfusionType`, `P.proof_1` — are enumerated by the
   static channel; the def-companion suffixes are reserved names and cannot be
   collision-declared at all, verified negatively); zero VIOLATION lines
   (`private`/`axiom`/`opaque`/unsafe/initializer declarations, non-trio axioms,
   missing axiom entries, broken depguards); exact sentinel/count grammar; the
   TOTAL manifest — every constant of every target: class, name, kind, type
   hash, axiom closure, plus both DEPGUARD lines — byte-identical to the frozen
   `scripts/scratch-manifest.expected` (pass-7 finding 1: classification labels
   are display-only; a smuggled declaration is a NEW line and fails the diff
   whatever label it gets, so lexical label collisions are moot); redundantly,
   surface-class = pinned 54 in both directions and the kernel-trio bound
   re-verified shell-side on every DECL line. Statement freezing is now
   mechanical (a type edit re-hashes and fails the byte-diff), not just
   probe-mediated. Residual trust boundary, documented in the reader header:
   build-time same-user filesystem malice from reviewed scratch sources
   (post-snapshot daemon races) is out of the gate's scope — every scratch
   source line is in the reviewed diff, and lakefile + pinned toolchain are
   repo-owned trusted inputs;
5. the §4.1 automated stale-index audit `scripts/check-kappa-effective-index.sh`
   committed in the P2′ PR and green: fails closed on total-family applications at
   bare extraction indices AND on bare-`φ` category-(iii) consumption sites
   (`alPkg.φ_mono`, `≤ alPkg.φ`-shaped bounds) in the κ-generic files,
   `-- KAPPA_ID_SITE:` same-line allowlist for legitimate fixed-horizon `κ := id`
   sites;
6. **the exact-shape gate re-point (pass-4 finding 1 — the gate artifact itself is
   ALREADY COMMITTED AND GREEN AT B0):** `LerayHopf/Scratch/R3ShapeGate.lean` is in
   the tree and in the checker NOW, containing (i) the frozen design MIRROR of the
   two κ-critical P2′ declarations — the κ-parameterized `AubinLionsPackage_R3`
   (BOTH ball-restricted convergence fields, byte-faithful to the merged production
   structure at `455ca3b` with the single change `galSeq (φ n)` ↦
   `galSeq (κ (φ n))`) and the `R3KappaChainExitWitness` above — declared inside
   `Scratch212` under the production-intended UNQUALIFIED names, (ii) the frozen
   limit-passage pin-conjunct Prop `R3LimitPassagePinConjunct` (the §4 strengthened
   conclusion shape) with its defeq probe, and (iii) the shape probes and linkage
   smokes (probes a₁/a₂/a₃/b/c/d₁/d₂/d₃ + smokes, see §4.1) — probe proofs are bare
   projections with `κ`/`φ₁` FREE, so a dummy-κ or bare-index declaration cannot
   elaborate. **The P2′ obligation under this clause is the RE-POINT:** delete the
   four mirror declarations (`AubinLionsPackage_R3`, its two `effective_*` lemmas,
   `R3KappaChainExitWitness`) from the scratch file and add
   `import LerayHopf.R3.KappaChainExit`; the probes' unqualified references then
   resolve to the production declarations (the production package lives in the
   already-imported `SolutionInterfaces`), with ZERO changes to any probe or smoke
   statement (checker pin list updated exact-set for the removed mirror names
   only). The strengthened `galerkin_limit_passage_R3` conclusion must state its
   pin conjunct as `R3LimitPassagePinConjunct` or definitionally equal to it
   (probe c is the defeq witness). A probe that fails to compile after the
   re-point means the production shape deviates from the frozen design: that is a
   kill-criterion event — back to the architect, never a probe edit.

   **Pass-5 extension (production coupling — findings 1–2): the re-point rules for
   `LerayHopf/Scratch/R3ProductionCoupling.lean`.** The B0 tree additionally
   contains the compiled production-coupling probes (§4.1) and, in
   `R3ShapeGate.lean`, the frozen FULL strengthened limit-passage conclusion
   `R3StrengthenedLimitPassageConclusion` (production 5 conjuncts, `alPkg` ↦ `p`,
   + `R3LimitPassagePinConjunct` appended as the sixth conjunct) with its compiled
   pin-projection probe `r3StrengthenedConclusion_projects_pin` (survives the
   re-point unchanged). At P2′, exactly three kinds of change are sanctioned in
   the coupling module — anything else is a kill-criterion event:
   (α) **DELETE with the mirror:** `AubinLionsPackage_R3.ofProduction`,
   `.toProduction`, and `r3LimitPassagePin_production_source` — the κ-less
   production package they bridge ceases to exist when P2′ rewires it;
   (β) **STATEMENTS FROZEN, proof term gains `id strictMono_id` only:** the three
   layer-1/2 bare-application probes (`r3Production_diag_ae_subseq_exact_shape`,
   `r3Production_u_lim_aestronglyMeasurable_exact_shape`,
   `r3Production_galerkinSpaceTimeExtraction_exact_shape`) and the two
   seed-coherence probes — their conclusions never change; only the application
   supplies the new κ arguments at `id`;
   (γ) **the ONE sanctioned statement replacement + two additions (texts frozen
   NOW, also in the module header):** `r3LimitPassage_production_exact_shape` is
   replaced by, and the P2′ PR must add, bare-application couplings
   `r3LimitPassage_strengthened_production_coupling : R3StrengthenedLimitPassageConclusion 𝔊 F ν T u₀ galSeq κ p := galerkin_limit_passage_R3 … κ hκ p htest`,
   `r3Production_diag_ae_subseq_kappa_coupling : «the exact diag_ae_subseq_seeded conclusion» := diag_ae_subseq … κ hκ`, and
   `r3Production_spacetime_extraction_kappa_coupling : «the exact spacetime_extraction_seeded conclusion» := galerkinSpaceTimeExtraction_R3 … κ hκ`
   — i.e. the κ-threaded production layers must prove, by BARE APPLICATION, the
   κ-generic statements frozen at B0 (`R3KappaSeed` seeds and the strengthened
   conclusion Prop); only the production argument-list spelling is a P2′ freedom.
   These couplings cannot compile today (production lacks κ and the pin
   conjunct); their failure to compile at P2′ is exactly the drift they exist to
   detect.
   (δ) **(pass-6 finding 2) the two free-κ statement guards are REPLACED by the
   (γ) κ-generic couplings:** `diag_ae_subseq_seeded_free_kappa_exact_shape` and
   `spacetime_extraction_seeded_free_kappa_exact_shape` compile the (γ) coupling
   conclusion texts TODAY with `κ` free (proof = the `R3KappaSeed` seeds applied
   at that `κ`); at P2′ the conclusion texts stay frozen VERBATIM and the only
   sanctioned change is the proof head swapping from the scratch seeds to the
   κ-threaded production declarations (plus the (γ) coupling names). Any other
   edit to those conclusion texts is a kill-criterion event. This closes the
   pass-6 gap that the id-coherence probes alone would tolerate a κ-dropping
   weakening of the seeds: at free `κ`, a seed conclusion degenerated to
   `galSeq (φ n)` cannot unify with the frozen `galSeq (κ (φ n))`.
   **Machine-enforced since pass-7 (finding 3):** the static reader's DEPGUARD
   check requires each guard's elaborated proof term to reference its seeded
   theorem directly (`scripts/scratch_reader.lean` `depGuards` pairs, asserted
   again by name in `check-scratch-pins.sh` and frozen in
   `scripts/scratch-manifest.expected`) — a guard re-proved from anything other
   than its seed fails the gate even with identical statement text. The P2′
   re-point therefore MUST update, in the SAME reviewed diff: the guards' proof
   heads, the reader's `depGuards` pairs (seed → κ-threaded production
   declaration), the checker's two DEPGUARD assertion lines, and the expected
   manifest. A re-point that forgets any of the four breaks the gate loudly —
   by design, not by accident.

Fields may not lose content relative to the shape above; names may differ. The
structural κ-invariant itself (κ-parameterized package with fields typed at
`galSeq (κ (φ n))`, dependent `galSeq₁` + `transport` in the witness) is §4.1's
PRIMARY protection and is not negotiable in P2′ — clause 6 is its MECHANICAL
assertion (checker-enforced, not prose), and clauses 3 and 5 are defense-in-depth
on top of it, not substitutes. P3′ carries
the twin obligation on the OTHER coherence input: the stage handle
`exists_weakLimitCurve_R3_kappa` must produce the EXACT `hW` hypothesis type of
spike (a) (diagonal invariant over `L2Sigma_R3`-tests at minimum; the design gives
`L2VF_R3`), verified the same way — a compiled application of the promoted coherence
lemma to stage outputs is a P3′ deliverable, not deferred to P4′.

---

## 7. Spike results (B0 evidence — all compiled sorry-free at `455ca3b` + spikes)

Build: `flock /tmp/lean-build.lock lake build LerayHopf.Scratch.R3StageCoherence
LerayHopf.Scratch.R3KappaSeed` → `Build completed successfully (3113 jobs)`, log
`/tmp/lh212-spike-build.log`. Re-verification from repo state alone:
`bash scripts/check-scratch-pins.sh` — the checker enumeration was extended IN THIS
B0 COMMIT (codex finding 3, §11) to 4 targets / 14 pins with forced-fresh rebuild and
exact-set fail-closed semantics, so the five new `#print axioms` lines inside the
committed spike files are CI-enforced from B0 onward, not deferred to P1′. At the
pass-3 remediation the enumeration was extended again (append-only) to 5 targets /
18 pins with the exact-shape gate module `LerayHopf/Scratch/KappaShapeGate.lean`
(§4.1): four probes — package convergence-field effective typing, effective
strictness, effective `le_apply` (category-(iii) coupling), witness pin against the
dependent family — each proved by the bare projection with `κ` free, all kernel-trio
(run green: log `/tmp/lh212-pins-check3.log`, `SCRATCH PIN CHECK OK (18/18)`). At
the pass-4 remediation the checker reached its current form: **6 targets / 41 pins
with source-manifest equality** — the full ℝ³ mirror shape gate
`LerayHopf/Scratch/R3ShapeGate.lean` added (16 declarations: mirror structures,
effective lemmas, pin-conjunct Prop, 8 probes, 3 linkage smokes — §4.1, §6
clause 6; its compilation ALSO type-checks the P2′ κ-package/witness design against
the real merged ℝ³ interfaces at B0), every top-level declaration of every target
now pinned (KappaReindex 12, P2ExitContract 4 — completing the previously unpinned
helper defs/structures), and the checker fails closed on any source declaration
missing from the pin set (pass-4 finding 3). Run green: log
`/tmp/lh212-pins-check4.log`, `SCRATCH PIN CHECK OK (41/41)`. At the pass-5
remediation the checker reached **7 targets / 52 pins**: the production-coupling
module `LerayHopf/Scratch/R3ProductionCoupling.lean` added (9 declarations — the
`ofProduction`/`toProduction` package bridges, the `galerkin_limit_passage_R3` and
layer-1/2 bare-application exact-shape probes, the `exists_weak_representative_R3`
pin-source coupling, and the two seed↔production id-coherence probes; §4.1, §6
clause 6 pass-5 extension), `R3StrengthenedLimitPassageConclusion` + its projection
probe added to `R3ShapeGate.lean` (16→18), and the source-discipline hard
rejections added to the checker (pass-5 finding 3). Run green: log
`/tmp/lh212-pins-check5.log`, `SCRATCH PIN CHECK OK (52/52)`. At the pass-6
remediation the evidence CHANNEL itself was rebuilt: **7 targets / 54 surface
declarations, environment manifest** — the text/regex manifest and build-log pin
parsing were retired in favor of `scripts/scratch_manifest.lean` (§6 clause 4:
elaborated-environment enumeration of every constant of every target — 187
constants total: 54 surface, plus compiler-generated companions, internal
auxiliaries, and codegen extras — each axiom-checked via `Lean.collectAxioms`,
emitted through the sentinel-delimited machine block that is now the checker's
only accepted evidence), and the two free-κ statement guards were added to
`R3ProductionCoupling.lean` (9→11; §4.1 item (f), §6 clause 6 (δ)). Run green:
log `/tmp/lh212-pins-check6.log`,
`SCRATCH PIN CHECK OK (54/54 surface declarations, env-manifest of 187 constants, kernel-trio only)`.
At the pass-7 remediation the evidence channel was rebuilt once more as the
**STATIC OLEAN READER** (§6 clause 4 pass-7 state): `scripts/scratch_reader.lean`
imports only `Lean`, reads the target oleans as data (`Lean.readModuleData` — no
target-authored code executes anywhere in the evidence path), takes axiom
closures from the toolchain's own precomputed `exportedAxiomsExt` entries,
freezes every statement by type-hash, and checks the free-κ guards' proof-term
dependencies (DEPGUARD). The TOTAL 187-constant manifest (+ 2 DEPGUARD lines) is
byte-pinned in `scripts/scratch-manifest.expected`; the collision fixture
`LerayHopf/Scratch/GateFixture.lean` + `scripts/scratch_fixture_selftest.lean`
demonstrate enumeration of hand-written generated-/internal-looking names; the
checker snapshots all gate inputs before the untrusted build.
`scripts/scratch_manifest.lean` is DELETED. Run green: log
`/tmp/lh212-pins-check7.log`,
`SCRATCH PIN CHECK OK (54/54 surface declarations; total static manifest of 187 constants byte-pinned, kernel-trio only; 2/2 free-kappa depguards; collision fixture enumerated)`.

### Spike (a) — `LerayHopf/Scratch/R3StageCoherence.lean` (every-t overlap coherence)

- `L2Sigma_R3_eq_of_forall_inner` — subspace separation on ℝ³ (mirror of the torus
  `L2Sigma_eq_of_forall_inner`).
- `r3_representative_diag_coherence` — the P4′ Step-4 core against real ℝ³ types: diagonal
  convergence (`L2Sigma_R3` tests) + everywhere-weak pin along a sub-extraction (`L2VF_R3`
  tests, the exact `exists_weak_representative_R3` conjunct-2 shape) ⇒ POINTWISE equality
  `v t = W t` on the whole window.
- `r3_representatives_agree_on_overlap` — the issue's requested form: two good
  representatives on nested windows `[0,T₁] ⊆ [0,T₂]` from nested extractions of the same
  diagonal agree pointwise on `[0,T₁]`.

Pins (from the build log, verbatim): all three
`depends on axioms: [propext, Classical.choice, Quot.sound]`.

### Spike (b) — `LerayHopf/Scratch/R3KappaSeed.lean` (κ-threading feasibility)

- `diag_ae_subseq_seeded` — the refine-capable primitive accepting a previously extracted
  subsequence: the production Cantor tower (`diag_ae_subseq`, the ONLY sealed layer with
  internal extraction structure) with an external seed `κ` composed in by pre-composition;
  conclusion along `κ (φ n)`. Verbatim-body port; the tower factorization
  (`nested_extraction_factor`) is consumed unchanged, confirming §4's "κ stays outside the
  tower" design.
- `spacetime_extraction_seeded` — the seed survives layer 2: `galerkin_weakLimit_R3`
  consumed UNCHANGED at extraction `κ ∘ φ`, output in the
  `galerkinSpaceTimeExtraction_R3` conclusion shape with effective index `κ (φ n)`.

Pins: both `depends on axioms: [propext, Classical.choice, Quot.sound]`.

Honest residual (stated, gated — the torus F-A discipline): the spikes do NOT compile
κ-versions of layers 3–4, the 15 downstream `alPkg` consumers, the limit-passage pin
re-export, or the exit witness; that residual IS phase P2′, and P3′/P4′ dispatch is
conditioned on its typed exit gate (§6), exactly as the torus campaign gated P3/P4 on
`P2ExitWitness` — a condition that was met there by the same mechanical pattern.

---

## 8. Reuse ledger (#195 artifacts)

**Consumed verbatim (zero re-proving):**
- `LerayHopf/Bochner/DiagonalExtraction.lean` — `nestedComp`, `diagExtraction`,
  `exists_diagonal_extraction`, `tendsto_diag_of_tendsto_stage` (arbitrary filter; the ℝ³
  stage invariant feeds through unchanged).
- `LerayHopf/Galerkin/GlobalContract.lean` — `IsLerayHopfOn`, round-trip equivalences,
  `GlobalLerayHopfSolution`, `WeakFormNS.mono/.congr_Icc`, `IsLerayHopfOn.mono/.congr_Icc`
  (instantiated at `r3Domain 𝔊`, already a `Galerkin.Domain`).
- `Galerkin/SolutionBundles.lean` contract + `r3Domain` instance + `rfl`-normalization
  lemmas (`r3Domain_dissip`, `r3Domain_regMem`).

**Template-copied (shape reused, body re-derived against ℝ³ interfaces):**
- `Torus/KappaChainExit.lean` → `R3/KappaChainExit.lean` (§6; ℝ³ drops the `ρ` fields,
  parameterizes the filler).
- `Torus/DiagonalGalerkin.lean` → `R3/DiagonalGalerkin.lean` (P3′; invariant upgraded to
  `L2VF_R3` tests).
- `Torus/GlobalCapstone.lean` → `R3/GlobalCapstone.lean` (P4′; quantifier prefix gains
  `∃ 𝔊`).
- Torus §3 base+κ design decisions (base+map form, `hκ` as side hypothesis, `κ := id`
  rewiring) — adopted as-is, revalidated by spike (b).

**Not transferable (re-derived nothing — different route):** torus mode-basis compactness
(`ModeCompactness`/`ModeTail`); ℝ³ uses its own merged ball-restricted FK chain, which this
campaign does not touch below `diag_ae_subseq`.

---

## 9. GO/NO-GO verdict

**CONDITIONAL-GO** — unconditional for P1′/P2′ dispatch; P3′/P4′ dispatch conditioned on
the P2′ typed exit gate (§6). Grounds:

1. **The issue's kill criterion is discharged with source-verified evidence**: the ℝ³
   limit-curve pin is ∀t (not a.e.), full-space tests, along `alPkg.φ` directly
   (`GoodRepresentative.lean:206–208`); the a.e. statements are confined to the same two
   places as the torus (representative identification, energy class).
2. **The one genuinely ℝ³-specific risk — per-ball structure vs full-space coherence —
   is CONDITIONALLY discharged** (downgraded per codex finding 2, §11): spike (a)
   compiles the coherence STEP against the real interfaces, sorry-free, and §3 explains
   why the per-ball data never reaches the argument; but its `hW`/`hpin` hypotheses are
   exactly the outputs P3′ and P2′ must still produce, and `galerkin_limit_passage_R3`
   today drops the pin. The mathematics of the step is retired; its applicability is
   gated fail-closed (§6 clauses 2–3 and the P3′ `hW`-coupling deliverable).
3. **The κ-threading risk is retired on the only STRUCTURALLY novel layer, and the
   residual semantic risk is gated**: spike (b) compiles the seeded Cantor tower
   verbatim-body and its composition into the measurable-limit layer, with
   `galerkin_weakLimit_R3` and the refine-capable root consumed UNCHANGED. Compilation
   alone cannot exclude stale-index uses in the 20-declaration thread (codex pass-1
   finding 1 / pass-2 findings 1–2); §4.1 records the design answer — PRIMARY
   protection is the torus-precedent type-level invariant (κ-parameterized package
   with convergence fields typed at `galSeq (κ (φ n))`, sealed-layer conclusions typed
   at the effective index, dependent `galSeq₁` + `transport` in the exit witness),
   with the sequence-free-consumer taxonomy closing the coverage question, and the
   nontrivial-κ smoke theorem + automated stale-index audit as §6 clauses 3/5
   defense-in-depth — so ship confidence for P3′/P4′ is claimed only AFTER the full
   κ-threaded exit path is compiled and gated, never from this B0 commit.
4. **Every conjunct of the final target is traced** (§2.3) to a merged ℝ³ theorem conjunct
   plus a #195-merged transfer lemma; the only new conjunct content (pin re-export) is
   already held inside the merged proof it is exported from.
5. **The forward-global premise holds by construction** (`Galerkin.SolutionData`
   horizon-free; `galSeq_R3_of_basis` axiom-free and `T`-free; the capstone's `𝔊`/`F`
   witnesses `T`-free), so the campaign is extraction, reindexing, and logic — no new
   analysis, no new axioms, and the release capstone stays byte-identical.

NO-GO triggers routed back here (D3): any P2′/P3′/P4′ kill criterion in §5.

## 10. Scope guards

- `exists_lerayHopf_r3` and `LerayHopfSolutionFull_R3` stay byte-identical; the finite-
  horizon ℝ³ claims of the release cone are unchanged.
- No global-in-space compactness, tightness, or full-space strong-convergence claim is
  introduced anywhere — every per-ball statement stays per-ball; the capstone asserts only
  the five merged contract conjuncts per horizon.
- No uniqueness of weak solutions assumed; no gluing of independently chosen witnesses
  (single diagonal family end-to-end, one `𝔊`/`F`/`galSeq` fixed once).
- No new `axiom`/`opaque`; kernel-trio pins throughout; append-only live pins.
- The torus lane and the frozen #195 campaign doc are untouched.
- All PRs target `dev/v0.2.0`; owner merges dev→main only with both lanes complete.

---

## 11. Codex adversarial statement gate — findings and dispositions (B0)

### 11.1 Pass 1 (at `43f0f9a`)

Gate run at the B0 commit (`43f0f9a`), effort xhigh, verdict **needs-attention**
(4 findings). Dispositions below; the amended sections are marked in place.

| # | Sev | Finding (condensed) | Disposition |
|---|---|---|---|
| 1 | high | κ-threading not semantically protected: total base family keeps stale `galSeq (alPkg.φ n)` well-typed; spike validates only tower + measurable-limit layers; package consumers, limit passage, pin re-export, exit witness uncompiled | **Design answer recorded, gate hardened** (new §4.1): reindexed-family-type route rejected with grounds (capstone byte-identity, partial protection); adopted effective-index statement discipline (`AubinLionsPackage_R3.effective_strictMono`, two statement sites written as literal `κ (alPkg.φ n)` compositions) + mandatory production smoke theorem at `κ := Nat.succ` consuming the exit witness through `transport` down to a base-family pin at the composed effective index — now §6 exit-gate clause 3. Full κ-compilation at B0 judged disproportionate (it IS P2′); justification in §4.1(3). P3′/P4′ remain dispatch-blocked until all four §6 clauses are green |
| 2 | high | Coherence only conditionally proved: spike (a)'s `hW`/`hpin` are exactly the still-unproduced P3′/P2′ outputs; `galerkin_limit_passage_R3` still drops the pin; §9 overclaimed "closed by compiled evidence" | **Accepted, claims downgraded**: §3 closing paragraph and §9 grounds 2–3 rewritten to "conditionally discharged — mathematics retired, pipeline gated"; §6 gains clause 2 (exit-witness pin must instantiate spike (a)'s EXACT `hpin` type via a compiled coupling lemma) and the twin P3′ `hW`-coupling deliverable. P3′/P4′ stay blocked until compiled stage handle + production exit witness instantiate the exact hypothesis types |
| 3 | medium | Spike evidence outside the enforced gate: `check-scratch-pins.sh` still enumerated only the 2 torus targets / 9 pins; deferring to P1′ left this commit's pins non-fail-closed | **Accepted, done at B0 (this commit)**: checker extended append-only to 4 targets / 14 pins (fully-qualified names — `Scratch195` + `Scratch212` namespaces), forced-fresh rebuild + exact-set semantics unchanged, run green locally (log `/tmp/lh212-pins-check.log`). §5 P1′ row and §7 updated accordingly. (Scripts are lean-coder territory in phase work; this edit was executed at B0 on explicit orchestrator instruction, recorded here) |
| 4 | medium | Quantifier rationale misstated the strengthening: finite theorem is `∀T ∃𝔊 ∃F Nonempty`; global target ALSO fixes scheme/forms and one curve across horizons — additional obligations, not a rearrangement; `implies_finite` is the easy direction only | **Accepted, reworded** (§2.1): the decision paragraph now states obligations (α) uniform witness selection (discharged by the `T`-free construction) and (β) one curve across all horizons (discharged by diagonal + coherence, the content of P3′/P4′) explicitly, and flags `globalR3Capstone_implies_finite` as the easy direction only |

### 11.2 Pass 2 (at `7d3b37c`)

Verdict **needs-attention**; findings 2–4 of pass 1 accepted as remediated; both
remaining findings target the pass-1 F1 disposition (κ semantic protection).

| # | Sev | Finding (condensed) | Disposition |
|---|---|---|---|
| 2.1 | high | The `Nat.succ` smoke gate covers only the pin projection: witness fields with SEQUENCE-FREE conclusions (`weak_eq`, `energy_ineq`, `initial_trace`, energy-class) can be proved via helpers using stale base indices and stay well-typed; the pass-1 statement-site rules were prose-only, not enforced | **Accepted — coverage argument made type-level, plus an automated audit** (§4.1 rewritten): (a) the exhaustive helper-input taxonomy — every LIMIT fact downstream of the package is a package field / sealed-layer conclusion / pin conjunct, all TYPED at the effective index, so a stale limit is underivable, not just unproven; per-datum facts are index-generic TRUE statements, so a stale application cannot inject a false premise — hence sequence-free conclusions are sound regardless of helper internals; (b) NEW §6 clause 5: `scripts/check-kappa-effective-index.sh` (shipped in the P2′ PR, fail-closed on total-family applications at bare extraction indices, `-- KAPPA_ID_SITE:` allowlist for `κ := id` sites) makes the residual statement-hygiene rule checker-enforced rather than prose. Smoke theorem retained as clause 3 |
| 2.2 | high | Pass-1 rejection of type-level protection conflated changing the Galerkin DATUM type with parameterizing the PACKAGE / using a dependent family; the merged torus P2 already achieves type-level κ-protection with the datum type unchanged (`AubinLionsPackage … galSeq κ`), which §6's own witness mirrors — the fallback to prose discipline was unjustified | **Accepted — record corrected, design re-based on the torus precedent** (§4.1 rewritten): the PRIMARY protection is now stated as the type-level invariant — `AubinLionsPackage_R3` gains the `κ` structure parameter with convergence fields typed at `galSeq (κ (φ n))` (verified against merged `Torus/SolutionInterfaces.lean:342`), sealed-layer conclusions typed at `κ (φ n)` (spike (b) compiled), dependent `galSeq₁` + mandatory `transport` in the exit witness. What remains rejected is only the narrower move of wrapping `galSeq ∘ κ` in a new datum-carrying type. Smoke theorem and audit script demoted to defense-in-depth (§6 clauses 3/5); §6 now states the structural invariant is non-negotiable in P2′, clauses 3/5 are not substitutes |

### 11.3 Pass 3 (at `6c3e19d`)

Verdict **needs-attention**; overall note: "the κ invariant is clearly specified but
not mechanically enforced, and §4.1's taxonomy omits extraction-dependent helper
facts. Deferring the checker is defensible only after an independent exact-shape
gate exists." Both findings refine the same κ-protection axis.

| # | Sev | Finding (condensed) | Disposition |
|---|---|---|---|
| 3.1 | high | None of the exit clauses mechanically asserts the package's effective-index typing: clauses 1–4 check compilation/pins/coupling/smoke, clause 5 is a future grep; "not negotiable" was prose. P2′ could carry a dummy `κ` (parameter unapplied, fields at `galSeq (φ n)`) or hide stale applications behind helpers while satisfying every listed clause | **Accepted — exact-shape gate COMMITTED AT B0, production twin made exit clause 6**: new `LerayHopf/Scratch/KappaShapeGate.lean` (this commit) re-states each κ-critical surface verbatim with `κ` FREE and proves it by bare projection — a dummy-κ/bare-index declaration cannot elaborate (no unifier for free `κ`). Wired into `check-scratch-pins.sh` (5 targets / 18 pins, forced-fresh, green: `/tmp/lh212-pins-check3.log`). §6 gains clause 6: `R3ShapeGate.lean` with the probe statements FROZEN VERBATIM in §6 (both convergence fields of `AubinLionsPackage_R3`, effective strictness, effective `le_apply`, witness pin), proofs required to stay bare projections; deviation = kill-criterion event, not a probe edit. Clause-5 deferral is now backed by the independent gate, per the pass-3 overall note |
| 3.2 | high | §4.1's "exhaustive" two-category helper taxonomy omits extraction/map-dependent facts: `GoodRepresentative`'s `hlevel : ∀ n, n ≤ alPkg.φ n` selects per-test Lipschitz bounds at the datum index and must be re-coupled to `κ (alPkg.φ n)`; package measurability/continuity feed the lsc path; a stale map/data pairing stays well-typed while `weak_eq`/energy are sequence-free | **Accepted — taxonomy corrected to three categories with a mandatory coupling rule** (§4.1): new category (iii) extraction/map-dependent facts (`hlevel`-style growth bounds, strictness/cofinality, `transport`, measurability/continuity inputs); every such fact must be DERIVED from the package's effective-map surface (`effective_strictMono` + corollaries at the composed map), never from bare `φ_mono`. Shape-gate probe (c) compiles the `hlevel` coupling (`∀ n, n ≤ κ (p.φ n)`) at B0. Enforcement widened: §6 clause 3 smoke must exercise a category-(iii) path at `κ := Nat.succ` (production selection helper with the effective bound); clause 5 audit patterns extended to bare-`φ` category-(iii) consumption (`alPkg.φ_mono`, `≤ alPkg.φ` shapes) outside `KAPPA_ID_SITE`. (Category membership re-scoped at pass-4 finding 2, §11.4) |

### 11.4 Pass 4 (at `2a3e72a`)

Verdict **needs-attention**; probe (a)'s free-κ unification mechanism confirmed
sound — all three findings are coverage/enforcement refinements.

| # | Sev | Finding (condensed) | Disposition |
|---|---|---|---|
| 4.1 | high | The committed shape gate covers only a synthetic torus one-field model; ℝ³'s `strong_convergence_ae`, sealed-layer outputs, the strengthened limit-passage pin, `transport`, and the witness's package linkage are unprobed; the promised `R3ShapeGate.lean` is absent from the commit and the checker | **Accepted — full ℝ³ mirror gate COMMITTED AND CHECKER-WIRED at B0** (this commit): `LerayHopf/Scratch/R3ShapeGate.lean` declares the frozen design mirror of the κ-parameterized `AubinLionsPackage_R3` (BOTH ball-restricted convergence fields, byte-faithful to the merged production structure) and the §6 `R3KappaChainExitWitness`, under production-intended unqualified names in `Scratch212` — so the mirror COMPILES TODAY against the real merged ℝ³ interfaces, type-checking the P2′ design itself. Probes (bare projections, `κ`/`φ₁` free): both convergence fields, limit-curve measurability, effective `le_apply`, the frozen `R3LimitPassagePinConjunct` Prop + defeq probe, witness `transport`, witness pin, alPkg-linkage convergence at `base (φ₁ (alPkg.φ n))`; plus transport-usability linkage smokes. Sealed layers 1–2 are already κ-probed by their own pinned spike statements (`R3KappaSeed`); layer 3 = layer-2 shape; layer 4's output type IS the probed package. §6 clause 6 is now a RE-POINT obligation (delete mirror decls + add production import, zero probe changes; deviation = kill criterion). Checker: 6 targets / 41 pins, green (`/tmp/lh212-pins-check4.log`) |
| 4.2 | medium | The three-category coupling rule misclassifies `transport` (its honest proof source is `extendReindexedFamily_apply` + injectivity of the SUPPLIED map, not `effective_strictMono`), and omits non-index inputs (`htest`, `LocalRellichInput`) — the blanket rule was internally inconsistent with the §6 witness design | **Accepted — taxonomy re-scoped to five categories** (§4.1): (iii) narrowed to κ-sensitive INDEX-SELECTION facts (the effective-map derivation rule applies to these only); NEW (iv) family-linkage facts — `transport` equalities, proof source honestly stated as the embedding construction (`extendReindexedFamily_R3` `_apply` + `hφ₁.injective`) or the witness field itself, enforced type-level (mandatory field) and probed (`r3WitnessShape_transport` + linkage smokes); NEW (v) index-free ambient inputs (`htest`, Rellich/FK chain inputs, positivity) — no κ-sensitivity, no coupling obligation; limit-curve measurability/continuity refiled under (i) as probed package fields |
| 4.3 | medium | The 18-pin checker is not fail-closed for UNPINNED declarations: only listed names + total count are verified; a new theorem added to a target without a pin passes unaudited | **Accepted — source-manifest equality added** (this commit): the checker derives the set of top-level declarations (`theorem`/`def`/`structure`/… keyword-led lines, namespace-qualified) from every target source and requires EXACT set equality with the pin enumeration before any axiom parsing — an unpinned declaration (or a pin for a nonexistent declaration) fails the gate. All previously unpinned helpers are now pinned (`KappaReindex` 6→12, `P2ExitContract` 3→4), total 41 pins; per-declaration parsing accepts the axiom-free `#print axioms` form (empty set ⊆ kernel trio) |

### 11.5 Pass 5 (at `ec0cbcb`)

Verdict **needs-attention**; positives: mirror transcription confirmed byte-faithful,
41/41 manifest count consistent. All three findings target the same axis: the mirror
compiles BESIDE production but nothing yet APPLIED production — coupling gaps.

| # | Sev | Finding (condensed) | Disposition |
|---|---|---|---|
| 5.1 | high | The limit-passage pin probe is not coupled to production: the scratch Prop and probe only unfold a locally declared hypothesis; they never apply `galerkin_limit_passage_R3` or extract its result — production could keep its current five-conjunct conclusion while the probe stays green | **Accepted — production coupling COMMITTED AND CHECKER-WIRED at B0** (this commit): new `LerayHopf/Scratch/R3ProductionCoupling.lean` (§4.1) applies the ACTUAL production declarations today, at the κ-less surface they have at `455ca3b`: `r3LimitPassage_production_exact_shape` (bare application of `galerkin_limit_passage_R3`, current 5-conjunct conclusion verbatim — drift detector until P2′) and `r3LimitPassagePin_production_source` (consumes the actual `exists_weak_representative_R3` — the declaration the limit passage draws its representative from — and PROJECTS its weak-convergence conjunct into the frozen `R3LimitPassagePinConjunct` at `κ := id` through the compiled `ofProduction` bridge; pure destructuring + definitional unfolding, no rewriting). The FULL strengthened conclusion is now frozen and compiled as `R3StrengthenedLimitPassageConclusion` (`R3ShapeGate.lean`: production 5 conjuncts + pin appended) with the compiled projection probe `r3StrengthenedConclusion_projects_pin`; §6 clause 6 (pass-5 extension) freezes the P2′ bare-application coupling `r3LimitPassage_strengthened_production_coupling := galerkin_limit_passage_R3 …` — compilable only once production's conclusion carries the pin, which is exactly the drift it detects. Bidirectional package bridges `ofProduction`/`toProduction` additionally assert mirror↔production field-set/type equality at B0 |
| 5.2 | high | Layer-1/2 coverage is standalone feasibility code: the seeded theorems are proved from lower-level primitives and never project or apply production `diag_ae_subseq` / `u_lim_aestronglyMeasurable` / `galerkinSpaceTimeExtraction_R3`; a future production layer could stay bare-indexed while pins pass | **Accepted — production-probing added as SEPARATE coverage** (this commit, same module; the stronger today-option since the κ-less production layers exist at `455ca3b`): bare-application exact-shape probes of all three ACTUAL production declarations (conclusions restated verbatim — consumption + drift detection), PLUS seed↔production id-coherence probes (`diag_ae_subseq_seeded_id_recovers_production`, `spacetime_extraction_seeded_id_recovers_production`: the frozen κ-generic seed statements at `κ := id` prove the production conclusions verbatim, definitional `id`-collapse only — the P2′ κ-threading is the frozen seed statement, not a redesign). §6 clause 6 (γ) freezes the P2′ κ-generic couplings (`… := diag_ae_subseq … κ hκ`, `… := galerkinSpaceTimeExtraction_R3 … κ hκ`) and (β) freezes the exact-shape probe statements with the only sanctioned proof change being the `id strictMono_id` arguments |
| 5.3 | medium | Manifest extraction misses modifier-prefixed and indented declarations (`private`/`protected`/`scoped`/`local`/`nonrec`/`partial`/`class`, mutual/nested-namespace blocks) — such declarations can evade the manifest | **Accepted — hard fail-closed rejection over regex sophistication** (this commit, per the round-5 recommendation's simple option): the checker now REJECTS outright, per target file, (1) modifier-prefixed and `mutual` declarations, (2) top-level `class`, (3) indented declaration keywords, (4) indented/dotted `namespace` lines, `namespace` after the first declaration, and namespace/`end` count imbalance. A false positive fails the gate loudly (reword the line); a false negative cannot occur for rejected forms because they never reach the manifest. Checker at 7 targets / 52 pins, manifest equality intact |

### 11.6 Pass 6 (at `5d30fce`)

Verdict **needs-attention**, 2 high. Finding 1 closed the checker arms race at its
root (orchestrator concurrence: each round found a new textual evasion because text
scanning cannot enumerate an elaborated environment; the terminal fix is the
repo's own `print_axioms.lean` pattern taken to its conclusion).

| # | Sev | Finding (condensed) | Disposition |
|---|---|---|---|
| 6.1 | high | Manifest gate still misses valid Lean declaration forms: indented declarations with Unicode names evade the `[A-Za-z_]` anchor, anonymous `instance : …` is ignored by the manifest regex, macro/elab-generated declarations are never inspected, and the axiom parser trusts arbitrary build-log text — tactic/command output could SPOOF pin lines | **Accepted — evidence channel REBUILT as an elaborated-environment manifest** (this commit, codex's own first recommendation): new `scripts/scratch_manifest.lean` imports the freshly built targets, enumerates EVERY environment constant of every target module (`EnvironmentHeader.moduleData` — Unicode names, anonymous instances, and macro-generated declarations are all just constants there), classifies each as pinned surface / compiler-generated child / internal auxiliary / codegen extra, computes every constant's axiom closure via `Lean.collectAxioms` (the `#print axioms` machinery — never a text log), and rejects `private`/`axiom`/`opaque`/non-`safe`/initializer declarations from the environment itself. Output is a sentinel-delimited machine block that `check-scratch-pins.sh` now accepts as its ONLY evidence: exactly-one-START/END grammar + self-reported count (a spoofed block injected by import-time IO duplicates sentinels because the genuine block still prints; initializer aux defs are additionally name-banned), surface = pinned 54 in both directions, kernel-trio bound re-verified shell-side on every DECL line. The pass-4/5 regex manifest, source-discipline greps, and build-log pin parsing are DELETED — total axiom coverage now includes internals and generated companions the per-pin scheme never touched. The `#print axioms` footers in scratch files remain as human-visible evidence but are parsed by nothing |
| 6.2 | high | Seed-to-production probes do not guard generic κ threading: the id-coherence probes would also pass if the seeded theorems were weakened to ignore κ while keeping the id specialization; the seeded declarations' κ-dependent types are never independently projected with κ FREE | **Accepted — free-κ statement guards added exactly as specified** (this commit): `diag_ae_subseq_seeded_free_kappa_exact_shape` and `spacetime_extraction_seeded_free_kappa_exact_shape` in `R3ProductionCoupling.lean` restate the seeded conclusions VERBATIM with `κ` free (independently frozen text) and prove them by direct application of `diag_ae_subseq_seeded` / `spacetime_extraction_seeded` at that free `κ`/`hκ`; a κ-dropping weakening of the seeds fails to elaborate here because `galSeq (φ n)` does not unify with the frozen `galSeq (κ (φ n))` at free `κ`. Checker-pinned alongside the id-coherence checks (surface 52→54); §4.1 item (f) records the mechanism, §6 clause 6 (δ) the P2′ re-point rule (conclusion texts frozen; only the proof head swaps to the κ-threaded production declarations — these guards become the (γ) couplings) |

### 11.7 Pass 7 (at `fdd435e`)

Verdict **needs-attention**, 2 high + 1 medium — all three on the gate
infrastructure, none on the mathematical design (no design finding since round 4;
rounds 5–7 are exclusively fail-closed hardening of the evidence channel, which
this campaign made a B0 deliverable in its own right). All three findings are
closed by ONE mechanism (orchestrator concurrence: the static reader is the
terminal move for this axis): the evidence process no longer executes any
target-authored code, pins the total manifest rather than a classified subset,
and reads proof-term dependencies directly.

| # | Sev | Finding (condensed) | Disposition |
|---|---|---|---|
| 7.1 | high | Hand-written declarations can escape surface pinning: `Name.isInternalDetail` is lexical and suffix classification relies only on parent kind — a user theorem named `Parent.eq_def` or `Ctor.inj` gets labeled internal/child and dodges the 54-name equality; recommendation: compiler provenance or exact generated-name metadata, default every unproven constant to surface, add collision fixtures | **Accepted — TOTAL manifest pinning makes labels display-only** (this commit): the gate no longer decides anything by classification. Every constant of every target — surface, child, internal, codegen alike — is one frozen line (class, name, kind, statement type-hash, axiom closure) in `scripts/scratch-manifest.expected`, byte-compared on every run; a collision-named declaration is a NEW constant, hence a new line, hence a diff failure WHATEVER label it gets ("default to surface" is subsumed: every class is pinned). Exact compiler provenance is now used where the olean provides it (`projectionFnInfoExt`, `auxRecExt` entries; kernel `ctorInfo`/`recInfo` kinds). Collision fixtures added as recommended: `LerayHopf/Scratch/GateFixture.lean` compiles hand-written `Probe.ibelow`, `Probe.mk.noConfusionType`, `Probe.proof_1` (the classes the retired classifier mislabeled) and `scripts/scratch_fixture_selftest.lean` asserts, per run, that the static channel enumerates them; the def-companion suffixes (`eq_def`/`eq_unfold`/`congr_simp`) were verified NON-declarable (reserved names — that collision class is closed by the elaborator itself, recorded as a negative fixture) |
| 7.2 | high | Imported extensions can prevent genuine manifest execution: `lake env lean` elaborates the manifest's `#eval` AFTER importing the targets — a target could register a command elaborator that fakes the block and returns success, or an initializer printing fake evidence and exiting 0 before the genuine command runs | **Accepted — trusted STATIC reader, exactly as recommended** (this commit): `scripts/scratch_reader.lean` imports only `Lean` and loads the target `.olean` files as data via `Lean.readModuleData` — pure deserialization; no initializer execution, no imported command/syntax extensions, no elaboration of target code anywhere in the evidence path. Axiom closures are not recomputed but read from the toolchain's own `exportedAxiomsExt` entries (the precomputed per-declaration data behind `#print axioms`, 1:1 with `constNames`; a missing entry fails closed). The build-then-read ordering is hardened too: the checker snapshots the reader, the fixture self-test, and the expected manifest to a private temp dir BEFORE `lake build` (build-time elaboration of scratch sources can run arbitrary IO and could otherwise rewrite the gate artifacts it is about to be judged by), and its bash body is a single `main` invoked with same-line `exit` so a mid-run rewrite of the script file cannot inject into the running shell. Residual boundary documented in the reader header (post-snapshot same-user filesystem races from reviewed sources: out of scope, covered by diff review; lakefile + pinned toolchain trusted). `scripts/scratch_manifest.lean` DELETED |
| 7.3 | medium | Free-κ proof heads not enforced by the machine gate: the manifest checks only axiom closures — nothing requires each guard's elaborated proof term to depend on `diag_ae_subseq_seeded` / `spacetime_extraction_seeded`; a guard re-proved from elsewhere would pass with identical statement text | **Accepted — DEPGUARD proof-term dependency check** (this commit): the reader hardcodes the two (guard, seed) pairs and requires the seed to occur in the guard's elaborated proof term (`ConstantInfo.value.getUsedConstants` — direct reference, stronger than closure membership), emitting `DEPGUARD\|guard\|seed\|direct` lines that are (a) grammar-checked and asserted by exact line in `check-scratch-pins.sh` and (b) frozen in the expected manifest. §6 clause 6 rule (δ) extended: the sanctioned P2′ re-point must update proof heads, reader `depGuards` pairs, checker assertion lines, and expected manifest in the SAME reviewed diff — forgetting any one breaks the gate loudly. As a free by-product of the same mechanism, every statement is now frozen mechanically by its type-hash in the expected manifest (an edit to ANY pinned statement re-hashes and fails the byte-diff, closing the gap that statement freezes were previously probe-mediated only) |
