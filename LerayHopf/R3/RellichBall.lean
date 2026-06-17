import LerayHopf.R3.SpatialCompactness          -- LocalRellichInput, L2ballR3, restrictToBall (P3 plumbing)
import Mathlib.Analysis.Fourier.LpSpace          -- Lp.fourierTransformₗᵢ, 𝓕 on L² (Plancherel)
import Mathlib.MeasureTheory.Measure.Haar.Unique -- volume add-invariance (translation measure-preserving)
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

namespace LerayHopf
open MeasureTheory Filter Topology Metric

/-!
# LOCAL Rellich–Kondrachov on a ball, reduced to Fréchet–Kolmogorov (Pillar B)

**Milestone:** `rellich-balls`

This file shrinks the analytic frontier carried by the `spatial_compactness_R3` axiom
(via `LocalRellichInput.ballCompact`, `SpatialCompactness.lean:94-99`) WITHOUT removing
the axiom.  It is an **HONEST PARTIAL milestone**: the full FK reduction and the
gradient ⇒ modulus bridge are assembled here, but the assembly is reduced down to a
*single* still-`sorry` Plancherel lemma (T0b), so the deliverable presently carries
`sorryAx` through that one lemma.  Concretely it does two things:

1. the Navier–Stokes-specific bridge "global spectral gradient bound ⇒ uniform
   L²-translation modulus" — its PEELING/ASSEMBLY (T0c) is axiom-free, but it consumes
   the Plancherel core T0b, which is still a marked `sorry` (see "Honest scope" below); and
2. the **reduction** of `LocalRellichInput` to the *standard, domain-agnostic*
   Fréchet–Kolmogorov (Riesz) L²-precompactness criterion `FrechetKolmogorovInput` —
   fully assembled (T1b + T2), axiom-free except for what it inherits from T0b via T0c.

`FrechetKolmogorovInput` is the **global-representative** precompactness criterion: each
family member `f : L2ballR3 R` carries a global representative `rep f : L2VF_R3` with
`restrictToBall R (rep f) = f`, and the uniform modulus is the GLOBAL L²-translation modulus
`‖translate_L2VF h (rep f) − rep f‖`.  This is a legitimate, sound, non-smuggling criterion
(it mentions no Sobolev/gradient/`L2Sigma`/velocity object); it is INTENTIONALLY phrased on
the global representative.  The Navier–Stokes bridge content lives entirely in T0b/T0c (the
Plancherel gradient ⇒ global-translation-modulus estimate), NOT in any bespoke ball-modulus
plus a separate ball/global bridge lemma.  The deliverable feeds T0c's global modulus directly
into the criterion (with `rep := the admissible global field` and `hrep` from `restrictToBall`).

## Honest scope (no overclaim) — PARTIAL milestone

This file does **NOT** prove Rellich–Kondrachov and does **NOT** remove any axiom.  It
substantiates the FK reduction and the gradient ⇒ modulus bridge DOWN TO a single
Plancherel-modulation lemma.  The status of each piece, with no rounding up:

**PROVED (axiom-free; no `sorryAx` on their own statements):**
- T0a `translate_L2VF` — L² translation `τ_h w (x) = w (x − h)` (pure Lp plumbing).
- T0c `norm_translate_sub_le_of_viscousBound` — the gradient ⇒ uniform-modulus PEELING
  step (square-root + sign bookkeeping).  Its *body* is axiom-free; it CONSUMES T0b's
  statement, so its `#print axioms` inherits T0b's `sorryAx` until T0b is closed.
- T1b `admissible_family_uniform_bound` — the restricted family is uniformly `‖·‖ ≤ M`.

**ASSEMBLED (deliverable, fully wired, axiom-free assembly):**
- T2 `localRellichInput_of_frechetKolmogorov` — the conditional constructor.  Its
  assembly logic (build `rep`/`S`, feed T0c's modulus + T1b's bound into the FK
  criterion) is complete and axiom-free; its ONLY gap is the T0b lemma it consumes
  transitively through T0c, so it currently carries `sorryAx` via T0b alone.

**OPEN frontier (marked `sorry`):**
- T0b `normSq_translate_sub_le_viscousFormSq` — the Plancherel translation-modulation
  estimate `‖τ_h w − w‖² ≤ ‖h‖²·viscousFormSq_R3 1 w`.  This is the SOLE `sorry` in the
  file.  It is blocked because mathlib lacks the Lp-level Fourier modulation identity
  `𝓕(τ_h f) = phase · 𝓕 f` (a bounded phase-multiplier on L²C + the Schwartz-level
  modulation identity + density extension — a multi-hundred-line development).  It is
  **NOT impossible, just unbuilt**; see the in-line `-- TODO:` at the `sorry` for the
  exact grep-confirmed blocker and the remaining axiom-free decomposition.

**Isolated hypothesis (mathlib-absent, a hypothesis is not an axiom):**
- `FrechetKolmogorovInput` — the standard Fréchet–Kolmogorov (Riesz) L²-precompactness
  criterion that mathlib still lacks, carried as an explicit hypothesis structure exactly
  as P3's `LocalRellichInput` and R3-d's `hdiv`.

Net: this file substantiates the FK reduction + the gradient ⇒ modulus bridge down to the
single Plancherel-modulation lemma T0b; everything else around T0b — translation plumbing,
the modulus peeling, the uniform bound, and the assembly into a `LocalRellichInput` — is
proved here.

The deliverable is the conditional constructor
`localRellichInput_of_frechetKolmogorov : FrechetKolmogorovInput → LocalRellichInput`,
whose conclusion reproduces `LocalRellichInput` verbatim.  Closing T0b (the unbuilt mathlib
Fourier-modulation development), discharging `FrechetKolmogorovInput` itself (a future
mathlib FK development), and rewriting `spatial_compactness_R3` from `axiom` to `theorem`
are separate later capstones; this file touches NEITHER `AxiomaticClosure.lean` NOR the root
`LerayHopf.lean` (deferred wiring).

## Architecture (standalone sibling)

This file imports `R3.SpatialCompactness` (reusing `LocalRellichInput`, `L2ballR3`,
`restrictToBall`), but NOT `R3.AxiomaticClosure`.  Its `#print axioms` for the deliverable
stays clean of the NS axioms; it does, however, currently report `sorryAx` (and only that)
because of the single open lemma T0b — it carries NO `axiom`/`opaque`/`constant`.

DAG position:
```
R3/Regularity.lean   (L2VF_R3, L2Sigma_R3, memH1VF_R3, viscousFormSq_R3, Domain3)
  └── R3/SpatialCompactness.lean   (L2ballR3, restrictToBall, LocalRellichInput) [P3]
        └── R3/RellichBall.lean    [THIS FILE; imports SpatialCompactness, NOT AxiomaticClosure]
```

## Declarations (dependency order)

- `translate_L2VF`                              : T0a — L² translation `τ_h w (x) = w (x − h)`
- `FrechetKolmogorovInput`                      : isolated frontier (abstract FK precompactness)
- `normSq_translate_sub_le_viscousFormSq`       : T0b — Plancherel translation-modulus core [OPEN: marked `sorry`, sole gap]
- `norm_translate_sub_le_of_viscousBound`       : T0c — uniform modulus from the gradient bound
- `admissible_family_uniform_bound`             : T1b — uniform L²-bound of the restricted family
- `localRellichInput_of_frechetKolmogorov`      : T2 — DELIVERABLE (conditional `LocalRellichInput`)

## Assumptions

Zero new `axiom`/`opaque`/`constant`.  Two distinct kinds of gap are carried, neither an
axiom:

1. **Hypothesis** `FrechetKolmogorovInput` — the mathlib-absent Fréchet–Kolmogorov
   precompactness criterion, carried as an explicit hypothesis structure exactly as
   P3's `LocalRellichInput` and R3-d's `hdiv`.  A hypothesis is not an axiom.
2. **Marked `sorry`** on T0b `normSq_translate_sub_le_viscousFormSq` — the Plancherel
   Fourier-modulation estimate, blocked by an unbuilt (but not impossible) mathlib
   development; see its in-line `-- TODO:`.  This is the SOLE `sorry` in the file and the
   ONLY source of `sorryAx` in the deliverable.
-/

/-! ### Tier 0 — translation plumbing -/

/-- **T0a.** L² translation `τ_h w (x) = w (x − h)` of an L²(ℝ³) velocity field, as an element
of `L2VF_R3`.

Translation `(· + h)` is measure-preserving for the Lebesgue `volume`, so — unlike
`restrictToBall` — this goes through `Lp.compMeasurePreserving` with the translation map and
its `MeasurePreserving` proof (`measurePreserving_add_right`).  This is pure Lp plumbing: it
mentions no Sobolev/gradient/divergence object. -/
noncomputable def translate_L2VF (h : Domain3) (w : L2VF_R3) : L2VF_R3 :=
  Lp.compMeasurePreserving (· + h)
    (measurePreserving_add_right (volume : Measure Domain3) h) w

/-- Isolated analytic frontier: the **Fréchet–Kolmogorov (Riesz) L²-precompactness criterion**
on a fixed ball.

A family of `L²(B_R)` elements that (i) is uniformly L²-bounded and (ii) has a uniform
L²-translation modulus vanishing as the shift `h → 0` is contained in a compact set of
`L²(B_R)`.  This is the ONE thing mathlib still lacks (no Fréchet–Kolmogorov / Riesz
criterion, no Rellich).

**No-smuggle (Codex Gate 1).**  This structure is a pure statement about abstract L²
families and translation.  It mentions NONE of: `memH1VF_R3`, `viscousFormSq_R3`,
`L2Sigma_R3`, gradients/`∇`, the word Sobolev, the velocity sequence, a subsequence, or a
limit.  The translation modulus is phrased via the global-field translation
`translate_L2VF` (pure Lp plumbing, NS-agnostic) of an explicitly supplied global
representative `rep f` of each family member: the family element `f : L2ballR3 R` is the
ball-restriction of `rep f : L2VF_R3` (hypothesis `hrep`), and the modulus is the GLOBAL
L²-norm `‖translate_L2VF h (rep f) − rep f‖` (NOT an in-ball translation, which would run
off the domain — see G-MOD).  This is strictly SMALLER than `LocalRellichInput.ballCompact`:
it is the abstract compactness *criterion*, not the H¹↪↪L² embedding.

The implication direction (modulus ⇒ precompact) is exactly the content mathlib lacks; the
modulus *hypothesis* itself is supplied downstream from the gradient bound (T0c) — whose
peeling is axiom-free but inherits T0b's open `sorry`. -/
structure FrechetKolmogorovInput where
  precompact_of_uniform_modulus :
    ∀ (R C : ℝ) (S : Set (L2ballR3 R))
      (rep : L2ballR3 R → L2VF_R3)
      (hrep : ∀ f ∈ S, restrictToBall R (rep f) = f),
    (∀ f ∈ S, ‖f‖ ≤ C) →
    (∀ ε > 0, ∃ δ > 0, ∀ f ∈ S, ∀ h : Domain3, ‖h‖ < δ →
        ‖translate_L2VF h (rep f) - rep f‖ < ε) →
    ∃ K : Set (L2ballR3 R), IsCompact K ∧ S ⊆ K

/-- **T0b.** L²-translation modulus controlled by the spectral gradient form (Plancherel):
`‖τ_h w − w‖²_{L²(ℝ³)} ≤ ‖h‖² · viscousFormSq_R3 1 w`.

This is the Navier–Stokes-specific core.  **OPEN:** it is the sole `sorry` in this file —
blocked by the unbuilt Lp-level Fourier modulation identity (see the in-line `-- TODO:` at
the proof). Everything downstream (T0c, T1b, T2/deliverable) is assembled axiom-free and
consumes ONLY this statement, so closing it discharges the whole pillar. -/
theorem normSq_translate_sub_le_viscousFormSq (h : Domain3) (w : L2VF_R3)
    (hw : memH1VF_R3 w) :
    ‖translate_L2VF h w - w‖ ^ 2 ≤ ‖h‖ ^ 2 * viscousFormSq_R3 1 w := by
  sorry -- ALLOW_SORRY: rellich-balls lean-prover target (T0b, G-PLANCHEREL) — STOP per
  -- AGENTS.md Hard rule 8 / task contract §7-§8. Statement intact; no axiom, no weakening.
  -- TODO (exact blocker): the L²-level Fourier-translation/modulation identity
  --   `𝓕 (Lp.compMeasurePreserving (· + h) (measurePreserving_add_right volume h) f)
  --      = phaseMul h (𝓕 f)`   for the L²-Fourier transform `Lp.fourierTransformₗᵢ`,
  -- where `phaseMul h g` is the Lp class of `ξ ↦ e^{2πi⟨h,ξ⟩} g(ξ)`, is ABSENT from mathlib at
  -- EVERY layer (grep-confirmed): `Lp.fourierTransformₗᵢ` occurs only in its defining file with
  -- NO translation/modulation lemma; `TemperedDistribution`/`FourierSchwartz` carry none either;
  -- and the only mathlib translation lemma `VectorFourier.fourierIntegral_comp_add_right` is at
  -- the raw-integral level (`fourierIntegral e μ L (f ∘ (· + v₀)) = fun w ↦ e (L v₀ w) • …`),
  -- not on the a.e. Lp class that `viscousFormSq_R3` is built on.
  -- Closing it requires building, from scratch: (1) the bounded phase-multiplier CLM
  -- `phaseMul h : L2C_R3 →L[ℂ] L2C_R3` (no bounded-`L∞`-multiplier-on-`Lp` operator exists in
  -- mathlib), (2) the Schwartz-level modulation identity bridging
  -- `fourierIntegral_comp_add_right` to `SchwartzMap.toLp_fourier_eq`, and (3) extension by
  -- continuity over the dense Schwartz range (`DenseRange.induction_on`) — a multi-hundred-line
  -- analytic development. Everything downstream (T0c, T1b, T2/deliverable) is proved axiom-free
  -- and consumes ONLY this statement, so completing it discharges the whole pillar.
  --
  -- Remaining axiom-free, structurally-complete decomposition once the bridge above lands:
  -- (a) `‖translate_L2VF h w − w‖² = ∑_j ‖τ_h^C cⱼ − cⱼ‖²`  (cⱼ := L2VF_projComponentC_R3 j w;
  --     component proj commutes with `compMeasurePreserving` a.e.; Euclidean-norm decomposition;
  --     `RCLike.ofRealCLM` is norm-preserving);
  -- (b) Plancherel `‖τ_h^C cⱼ − cⱼ‖ = ‖𝓕(τ_h^C cⱼ) − 𝓕 cⱼ‖`  (`Lp.norm_fourier_eq`);
  -- (c) modulation bridge (THE BLOCKER) ⇒ `‖𝓕(τ_h^C cⱼ) − 𝓕 cⱼ‖²
  --       = ∫ |e^{2πi⟨h,ξ⟩}−1|² ‖(𝓕 cⱼ) ξ‖² dξ`;
  -- (d) pointwise `|e^{2πi⟨h,ξ⟩}−1|² ≤ (2π)²‖h‖²‖ξ‖²` (`Complex.norm_exp_ofReal_mul_I_sub_one_le`
  --     / `|e^{iθ}−1| ≤ |θ|`, Cauchy–Schwarz `|⟨h,ξ⟩| ≤ ‖h‖‖ξ‖`); integrate and pull out `‖h‖²`
  --     to recognize `∑_j ∫ (2π)²‖ξ‖²‖(𝓕 cⱼ) ξ‖² = viscousFormSq_R3 1 w`.

/-- **T0c.** Uniform translation modulus for the admissible family: from `0 ≤ M` and
`viscousFormSq_R3 1 w ≤ M²`, `‖τ_h w − w‖ ≤ ‖h‖·M`.  Supplies the modulus hypothesis of
`FrechetKolmogorovInput`.

The sign hypothesis `hM : 0 ≤ M` is REQUIRED: the squared bound `viscousFormSq_R3 1 w ≤ M²`
alone does not control the sign of `M` (e.g. `M = -1`, `w = 0` would give the false
`0 ≤ -‖h‖`).  Taking square roots of the T0b estimate only yields `‖h‖·|M|`; the conclusion
`‖h‖·M` is correct precisely when `M ≥ 0`.  Downstream (`localRellichInput_of_frechetKolmogorov`)
`0 ≤ M` is discharged from `‖w‖ ≤ M` on any admissible witness. -/
theorem norm_translate_sub_le_of_viscousBound (M : ℝ) (h : Domain3) (w : L2VF_R3)
    (hw : memH1VF_R3 w) (hM : 0 ≤ M) (hvf : viscousFormSq_R3 1 w ≤ M ^ 2) :
    ‖translate_L2VF h w - w‖ ≤ ‖h‖ * M := by
  have hsq : ‖translate_L2VF h w - w‖ ^ 2 ≤ (‖h‖ * M) ^ 2 := by
    refine le_trans (normSq_translate_sub_le_viscousFormSq h w hw) ?_
    have : ‖h‖ ^ 2 * viscousFormSq_R3 1 w ≤ ‖h‖ ^ 2 * M ^ 2 :=
      mul_le_mul_of_nonneg_left hvf (by positivity)
    calc ‖h‖ ^ 2 * viscousFormSq_R3 1 w ≤ ‖h‖ ^ 2 * M ^ 2 := this
      _ = (‖h‖ * M) ^ 2 := by ring
  have hrhs : 0 ≤ ‖h‖ * M := mul_nonneg (norm_nonneg _) hM
  nlinarith [norm_nonneg (translate_L2VF h w - w), hsq, hrhs]

/-! ### Tier 1 — assemble the modulus into the FK-criterion input -/

/-- **T1b.** The restricted admissible family `S_{M,R} := {restrictToBall R w | w admissible}`
is uniformly `‖·‖ ≤ M`: each restriction does not increase the norm and `‖w‖ ≤ M`. -/
theorem admissible_family_uniform_bound (M R : ℝ) (w : L2VF_R3) (hbd : ‖w‖ ≤ M) :
    ‖restrictToBall R w‖ ≤ M := by
  refine le_trans ?_ hbd
  -- Local copy of `norm_restrictToBall_le` (it is `private` in SpatialCompactness).
  rw [Lp.norm_def, Lp.norm_def]
  have hle : volume.restrict (Metric.closedBall (0 : Domain3) R) ≤ (volume : Measure Domain3) :=
    Measure.restrict_le_self
  have hcong : ⇑(restrictToBall R w)
      =ᵐ[volume.restrict (Metric.closedBall (0 : Domain3) R)]
        (w : Domain3 → EuclideanSpace ℝ (Fin 3)) := MemLp.coeFn_toLp _
  rw [eLpNorm_congr_ae hcong]
  exact ENNReal.toReal_mono (Lp.memLp w).2.ne (eLpNorm_mono_measure _ hle)

/-! ### Tier 2 — DELIVERABLE -/

/-- **T2 (DELIVERABLE).  LOCAL Rellich input on ℝ³, from the abstract Fréchet–Kolmogorov
criterion.**

Constructs a `LocalRellichInput` (per-ball precompactness of the H¹-bounded div-free family)
from `FrechetKolmogorovInput`.  The Navier–Stokes-specific content (gradient bound ⇒ uniform
translation modulus, via Plancherel on `viscousFormSq_R3`) is ASSEMBLED axiom-free here, but
its Plancherel core T0b is still a marked `sorry`, so this deliverable currently carries
`sorryAx` through T0b alone; only the domain-agnostic FK precompactness criterion is assumed
as a hypothesis.  The conclusion reproduces `LocalRellichInput` verbatim (no weakening;
Hard rule 3). -/
theorem localRellichInput_of_frechetKolmogorov (FK : FrechetKolmogorovInput) :
    LocalRellichInput := by
  classical
  refine ⟨fun M R => ?_⟩
  -- Admissibility predicate for the global field.
  set adm : L2VF_R3 → Prop :=
    fun w => w ∈ L2Sigma_R3 ∧ memH1VF_R3 w ∧ ‖w‖ ≤ M ∧ viscousFormSq_R3 1 w ≤ M ^ 2 with hadm
  -- The restricted admissible family in `L2ballR3 R`.
  set S : Set (L2ballR3 R) :=
    {f | ∃ w : L2VF_R3, adm w ∧ restrictToBall R w = f} with hS
  -- Global representative: for `f ∈ S`, choose an admissible witness; otherwise arbitrary.
  have hex : ∀ f ∈ S, ∃ w : L2VF_R3, adm w ∧ restrictToBall R w = f := fun f hf => hf
  let rep : L2ballR3 R → L2VF_R3 := fun f =>
    if hf : f ∈ S then (hex f hf).choose else 0
  -- `rep f` is admissible and restricts back to `f`, for `f ∈ S`.
  have hrep_adm : ∀ f ∈ S, adm (rep f) := by
    intro f hf
    simp only [rep, dif_pos hf]
    exact (hex f hf).choose_spec.1
  have hrep : ∀ f ∈ S, restrictToBall R (rep f) = f := by
    intro f hf
    simp only [rep, dif_pos hf]
    exact (hex f hf).choose_spec.2
  -- Uniform L²-bound C := M on the family (T1b).
  have hbound : ∀ f ∈ S, ‖f‖ ≤ M := by
    intro f hf
    obtain ⟨w, hw, rfl⟩ := hf
    exact admissible_family_uniform_bound M R w hw.2.2.1
  -- Uniform global translation modulus (T0c), the slot FK consumes.
  have hmod : ∀ ε > 0, ∃ δ > 0, ∀ f ∈ S, ∀ h : Domain3, ‖h‖ < δ →
      ‖translate_L2VF h (rep f) - rep f‖ < ε := by
    intro ε hε
    -- Use `max M 0 + 1 > 0` as denominator so `δ > 0` holds unconditionally; on a nonempty
    -- family `M ≥ 0`, so `max M 0 = M`.
    have hden : (0 : ℝ) < max M 0 + 1 := by positivity
    refine ⟨ε / (max M 0 + 1), by positivity, ?_⟩
    intro f hf h hh
    -- `rep f` is admissible: gives `0 ≤ M`, `memH1VF_R3`, and the viscous bound.
    obtain ⟨hmemf, hH1f, hnormf, hvff⟩ := hrep_adm f hf
    have hMnn : 0 ≤ M := le_trans (norm_nonneg _) hnormf
    have hmaxM : max M 0 = M := max_eq_left hMnn
    -- T0c: `‖τ_h (rep f) − rep f‖ ≤ ‖h‖·M`.
    have hT0c : ‖translate_L2VF h (rep f) - rep f‖ ≤ ‖h‖ * M :=
      norm_translate_sub_le_of_viscousBound M h (rep f) hH1f hMnn hvff
    calc ‖translate_L2VF h (rep f) - rep f‖ ≤ ‖h‖ * M := hT0c
      _ ≤ ‖h‖ * (max M 0 + 1) := by
            apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
            rw [hmaxM]; linarith
      _ < (ε / (max M 0 + 1)) * (max M 0 + 1) := by
            apply mul_lt_mul_of_pos_right hh hden
      _ = ε := by field_simp
  obtain ⟨K, hK, hKS⟩ := FK.precompact_of_uniform_modulus R M S rep hrep hbound hmod
  refine ⟨K, hK, ?_⟩
  intro w hmem hH1 hnorm hvf
  apply hKS
  exact ⟨w, ⟨hmem, hH1, hnorm, hvf⟩, rfl⟩

end LerayHopf
