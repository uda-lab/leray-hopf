import LerayHopf.R3.SobolevEmbedding
import LerayHopf.Analysis.SpectralWeakGradient  -- gradComp_of_memH1 (for memLp_two_gradRe)

namespace LerayHopf

open MeasureTheory

/-!
# `L²∩L⁶ ↪ L³` Hölder interpolation on ℝ³

Generic `Lp` infrastructure extracted from `EnergyClassConvection.lean` (issue #113 PR-2):
the `L²∩L⁶ ↪ L³` interpolation inequality (pure Hölder/log-convexity, no convection content),
plus the four small `H¹_σ`-component `MemLp` facts built on top of it that feed
`convFormH1_integrable` (which stays in `EnergyClassConvection.lean`, since it is genuinely
convection-specific).

Depends on `SobolevEmbedding.lean`'s `gns_L6_of_memH1_R3`/`gns_L6_schwartz` (GNS H¹↪L⁶), which
is `ConvectionForm`-free since issue #113 PR-1 — this import is therefore R3-analysis-clean,
not a route back into the Galerkin/solution-package layer.

## Declarations

- `L2L6_inter_mem_L3` — **B3a**, the interpolation inequality itself (public on `main`; no
  external callers found by repo-wide grep, but the qualified name is preserved regardless)
- `memLp_six_componentRe`, `memLp_two_componentRe`, `memLp_three_componentRe`,
  `memLp_two_gradRe` — component-level `MemLp` facts for `H¹_σ` fields. Kept public (not
  `private` as on `main`): `EnergyClassConvection.lean`'s remaining B6 content (still there
  pending PR-2 commit "4"/WeakLeibniz.lean) references them by name.

## Assumptions

No `axiom`/`opaque`/`constant`/`unsafe` in this file.
-/

/-- **B3a `L2L6_inter_mem_L3` [must-prove].** If `f : Domain3 → F` satisfies
both `MemLp f 2 volume` and `MemLp f 6 volume`, then `MemLp f 3 volume`.

This is the Lp log-convexity / Hölder interpolation at exponent `3` between `2` and `6`:
`1/3 = θ/2 + (1-θ)/6` with `θ = 2/3`; equivalently, `‖f‖_{L³} ≤ ‖f‖_{L²}^{2/3} · ‖f‖_{L⁶}^{1/3}`.

**Proof route (for prover):** Apply `MeasureTheory.eLpNorm'_le_eLpNorm'_mul_eLpNorm'`
(mathlib `LpSeminorm/CompareExp.lean:206`) with `r = 3`, `p = 6`, `q = 2`:
  `‖f‖_{L³} = ‖f·f^0‖_{L³} ≤ ‖f‖_{L⁶} · ‖1‖_{L²}` — but this is not the right split.

Actually the correct interpolation is via Hölder with pointwise `|f|^(1/3)·|f|^(2/3)`:
split `f = f · 1` and use the `HolderTriple (6 : ENNReal) (2 : ENNReal) (3 : ENNReal)`
instance together with `eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm` from
`LpSeminorm/CompareExp.lean:229`. The instance `HolderTriple 6 2 3` follows from
`1/6 + 1/2 = 2/3` — wait, that's `HolderTriple 6 2 (3/2)` not `3`. Let me reconsider:

The interpolation `L²∩L⁶↪L³` holds by Hölder with:
`∫|f|³ = ∫|f|^(3/2) · |f|^(3/2) ≤ (∫|f|²)^(3/4) · (∫|f|⁶)^(1/4)` (Cauchy–Schwarz)
giving `‖f‖_{L³}³ ≤ ‖f‖_{L²}^(3/2) · ‖f‖_{L⁶}^(3/2)`, so `‖f‖_{L³} ≤ ‖f‖_{L²}^{1/2} · ‖f‖_{L⁶}^{1/2}`.
Or equivalently `eLpNorm f 3 ≤ (eLpNorm f 2)^(1/2) · (eLpNorm f 6)^(1/2)`.

⚠️ NOTE for prover: The plan cites `eLpNorm_le_eLpNorm_pow_mul_eLpNorm` which does NOT exist
in mathlib. Use `MeasureTheory.eLpNorm'_le_eLpNorm'_mul_eLpNorm'` (with the A1 instances)
or the Cauchy–Schwarz approach above via `MeasureTheory.inner_mul_le_norm_mul_norm`. -/
theorem L2L6_inter_mem_L3 {F : Type*} [NormedAddCommGroup F] (f : Domain3 → F)
    (h2 : MemLp f 2 (volume : Measure Domain3))
    (h6 : MemLp f 6 (volume : Measure Domain3)) :
    MemLp f 3 (volume : Measure Domain3) := by
  -- Work with the real-valued norm function `g x = ‖f x‖`.
  set g : Domain3 → ℝ := fun x => ‖f x‖ with hg
  have hg2 : MemLp g 2 (volume : Measure Domain3) := h2.norm
  have hg6 : MemLp g 6 (volume : Measure Domain3) := h6.norm
  -- `g * g ∈ L^{3/2}` by Hölder with `1/6 + 1/2 = 2/3 = 1/(3/2)`.
  haveI : ENNReal.HolderTriple 6 2 (3 / 2) := by
    have h : Real.HolderTriple (6 : ℝ) (2 : ℝ) (3 / 2 : ℝ) := by
      constructor <;> norm_num
    have h2 := h.ennrealOfReal
    have e32 : ENNReal.ofReal (3 / 2 : ℝ) = (3 / 2 : ENNReal) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp
    simp only [ENNReal.ofReal_ofNat, e32] at h2
    exact h2
  have hgg : MemLp (g * g) (3 / 2) (volume : Measure Domain3) := hg6.mul hg2
  -- Identify `g * g` with `fun x => ‖f x‖ ^ (2 : ℝ)` and use `eLpNorm_norm_rpow`.
  have hsm : AEStronglyMeasurable f (volume : Measure Domain3) := h2.aestronglyMeasurable
  refine ⟨hsm, ?_⟩
  -- `eLpNorm f 3 < ∞` from `(eLpNorm f 3) ^ 2 = eLpNorm (fun x => ‖f x‖ ^ 2) (3/2) < ∞`.
  have hpow : (fun x => ‖f x‖ ^ (2 : ℝ)) = (g * g) := by
    funext x; simp [hg, Pi.mul_apply, Real.rpow_natCast, sq]
  have hkey : eLpNorm (fun x => ‖f x‖ ^ (2 : ℝ)) (3 / 2) (volume : Measure Domain3)
      = eLpNorm f ((3 / 2) * ENNReal.ofReal 2) (volume : Measure Domain3) ^ (2 : ℝ) :=
    eLpNorm_norm_rpow f (by norm_num)
  have h32 : ((3 : ENNReal) / 2) * ENNReal.ofReal 2 = 3 := by
    rw [show ENNReal.ofReal 2 = (2 : ENNReal) by norm_num [ENNReal.ofReal]]
    rw [ENNReal.div_mul_cancel] <;> norm_num
  rw [hpow, h32] at hkey
  -- `eLpNorm (g*g) (3/2) < ∞`, so `(eLpNorm f 3)^2 < ∞`, hence `eLpNorm f 3 < ∞`.
  have hfin : eLpNorm f 3 (volume : Measure Domain3) ^ (2 : ℝ) < ⊤ := by
    rw [← hkey]; exact hgg.eLpNorm_lt_top
  by_contra hcon
  rw [not_lt, top_le_iff] at hcon
  rw [hcon] at hfin
  simp at hfin

/-- The real part of the j-th complex component of `u ∈ H¹_σ` lies in `L⁶` (via A3 / GNS). -/
theorem memLp_six_componentRe (u : L2VF_R3) (hu : memH1VF_R3 u) (j : Fin 3) :
    MemLp (fun x => (L2VF_projComponentC_R3 j u x).re) 6 (volume : Measure Domain3) :=
  (gns_L6_of_memH1_R3 _ (hu j)).re

/-- The real part of the j-th complex component of `u ∈ L²` lies in `L²`. -/
theorem memLp_two_componentRe (u : L2VF_R3) (j : Fin 3) :
    MemLp (fun x => (L2VF_projComponentC_R3 j u x).re) 2 (volume : Measure Domain3) :=
  (Lp.memLp (L2VF_projComponentC_R3 j u)).re

/-- The real part of the j-th complex component of `u ∈ H¹_σ` lies in `L³` (interpolation). -/
theorem memLp_three_componentRe (u : L2VF_R3) (hu : memH1VF_R3 u) (j : Fin 3) :
    MemLp (fun x => (L2VF_projComponentC_R3 j u x).re) 3 (volume : Measure Domain3) :=
  L2L6_inter_mem_L3 _ (memLp_two_componentRe u j) (memLp_six_componentRe u hu j)

/-- The real part of the weak gradient component `gradComp_of_memH1` lies in `L²`. -/
theorem memLp_two_gradRe (v : L2VF_R3) (hv : memH1VF_R3 v) (a i : Fin 3) :
    MemLp (fun x => (gradComp_of_memH1 v hv a i x).re) 2 (volume : Measure Domain3) :=
  (Lp.memLp (gradComp_of_memH1 v hv a i)).re

end LerayHopf
