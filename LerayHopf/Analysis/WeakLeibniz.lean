import LerayHopf.R3.SobolevEmbedding
import LerayHopf.Analysis.PlancherelKernels
import LerayHopf.Analysis.RealComplexLpBridge
import LerayHopf.Analysis.SpectralWeakGradient
import LerayHopf.Analysis.LpInterpolation
import Mathlib.Analysis.Distribution.Sobolev

namespace LerayHopf

open MeasureTheory TemperedDistribution SchwartzMap LineDeriv

/-!
# H¹·H¹ weak Leibniz product rule via Schwartz approximation

Generic infrastructure extracted from `EnergyClassConvection.lean` (issue #113 PR-2): the B6a
integration-by-parts identity needs the distributional Leibniz rule
`∂ₐ(f·g) = (∂ₐf)·g + f·(∂ₐg)` for two H¹ factors, tested against a Schwartz function. Mathlib
has no such two-H¹-factor product rule, so it is built here by smooth-approximation:
approximate both `f` and `g` (with their weak derivatives) by Schwartz sequences via
`schwartz_h1_gradConv`, apply the classical Schwartz IBP
`SchwartzMap.integral_bilinear_lineDerivOp_right_eq_neg_left`, and pass to the L²-limit
(`tendsto_integral_mul_mul`, `Analysis/RealComplexLpBridge.lean`). None of this is
convection-specific — it is pure H¹/Schwartz-approximation machinery.

## Declarations (all `private`, as on `main`, except where noted)

- `prodS`, `prodS_apply`, `lineDerivOp_prodS` — pointwise product of real Schwartz maps and
  its Leibniz rule
- `schwartzLeibniz2` — the Schwartz-level Leibniz IBP identity
- `reS`, `reS_apply`, `lineDerivOp_reS`, `reS_toLp_eq_reLp`, `reS_sub_apply` — real part of a
  complex Schwartz function
- `reSchwartz_L3_approx` — L³ approximation of the un-differentiated H¹ test factor
- `reSchwartz_approx` — per-component Schwartz approximation with real-part gradient
  convergence
- `Schwartz_mul_mul_integrable`, `reInt_integrable`, `integral_schwartz_eq_toLp` — integrability
  helpers
- `h1Leibniz2` — **the H¹·H¹ weak Leibniz identity** (Schwartz test factor)
- `tendsto_integral_pairing` — Hölder integral pairing limit lemma
- `h1Leibniz2_H1test` — the H¹-test extension of `h1Leibniz2`. Kept public (not `private`
  as on `main`): `EnergyClassConvection.lean`'s remaining B6 content references it by name.

Depends on `LpInterpolation.lean` (for `L2L6_inter_mem_L3`, used by `reSchwartz_L3_approx`) and
`SpectralWeakGradient.lean` (for `L2C_eq_of_toTempered_eq`), beyond the contract's originally
scoped `R3.Regularity` + `RealComplexLpBridge` — discovered via the build, not guessed; both are
themselves generic, non-convection modules, so this stays within the intended `Analysis/` layer.

## Assumptions

No `axiom`/`opaque`/`constant`/`unsafe` in this file.
-/

/-! ### B6 IBP infrastructure — H¹·H¹ weak Leibniz via Schwartz approximation

The B6a integration-by-parts identity needs the distributional Leibniz rule
`∂ₐ(f·g) = (∂ₐf)·g + f·(∂ₐg)` for two H¹ factors, tested against a Schwartz function.
Mathlib has no such two-H¹-factor product rule, so we build it here by
smooth-approximation: approximate both `f` and `g` (with their weak derivatives) by Schwartz
sequences via `schwartz_h1_gradConv`, apply the classical Schwartz IBP
`SchwartzMap.integral_bilinear_lineDerivOp_right_eq_neg_left`, and pass to the L²-limit.

The limit passage rests on a single clean fact: if `aₙ → a` and `bₙ → b` in `L²(ℝ³)` and
`h` is essentially bounded, then `∫ aₙ·bₙ·h → ∫ a·b·h`, proved by writing the integral as
the real `L²` inner product `⟪aₙ, (h·bₙ)⟫` and using joint continuity of `inner`. -/

/-! #### Schwartz-level Leibniz product rule -/

/-- The pointwise product of two real Schwartz functions, as a Schwartz function. -/
private noncomputable def prodS (f g : SchwartzMap Domain3 ℝ) : SchwartzMap Domain3 ℝ :=
  SchwartzMap.bilinLeftCLM (ContinuousLinearMap.mul ℝ ℝ) g.hasTemperateGrowth f

private theorem prodS_apply (f g : SchwartzMap Domain3 ℝ) (x : Domain3) :
    (prodS f g) x = f x * g x := by
  simp [prodS, SchwartzMap.bilinLeftCLM_apply]

/-- Classical Leibniz rule for the directional derivative of a Schwartz product. -/
private theorem lineDerivOp_prodS (f g : SchwartzMap Domain3 ℝ) (v x : Domain3) :
    (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ) v (prodS f g)) x
      = (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ) v f) x * g x
        + f x * (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ) v g) x := by
  simp only [LineDeriv.lineDerivOpCLM_apply]
  have hf : HasDerivAt (fun t : ℝ => f (x + t • v)) ((fderiv ℝ (⇑f) x) v) 0 :=
    (SchwartzMap.hasFDerivAt f x).hasLineDerivAt v
  have hg : HasDerivAt (fun t : ℝ => g (x + t • v)) ((fderiv ℝ (⇑g) x) v) 0 :=
    (SchwartzMap.hasFDerivAt g x).hasLineDerivAt v
  have hmul := hf.mul hg
  rw [zero_smul, add_zero] at hmul
  have hfun : ((fun t : ℝ => f (x + t • v)) * fun t : ℝ => g (x + t • v))
      = fun t : ℝ => (prodS f g) (x + t • v) := by funext t; rw [prodS_apply]; rfl
  rw [hfun] at hmul
  have hline : HasLineDerivAt ℝ (⇑(prodS f g))
      ((fderiv ℝ (⇑f) x) v * g x + f x * (fderiv ℝ (⇑g) x) v) x v := hmul
  rw [lineDerivOp_apply, hline.lineDeriv, lineDerivOp_apply, lineDerivOp_apply,
    (SchwartzMap.hasFDerivAt f x).hasLineDerivAt v |>.lineDeriv,
    (SchwartzMap.hasFDerivAt g x).hasLineDerivAt v |>.lineDeriv]

/-- **Schwartz-level Leibniz IBP.** For real Schwartz `f, g, φ` and direction `eₐ`:
`∫ f·g·(∂ₐφ) = -∫ (∂ₐf·g + f·∂ₐg)·φ`. -/
private theorem schwartzLeibniz2 (f g φ : SchwartzMap Domain3 ℝ) (a : Fin 3) :
    ∫ x : Domain3, (f x) * (g x)
        * (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ) (EuclideanSpace.single a (1 : ℝ)) φ) x
        ∂(volume : Measure Domain3)
      = -∫ x : Domain3,
          ((lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ) (EuclideanSpace.single a (1 : ℝ)) f) x * g x
            + f x * (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ) (EuclideanSpace.single a (1 : ℝ)) g) x)
          * (φ x) ∂(volume : Measure Domain3) := by
  set m : Domain3 := EuclideanSpace.single a (1 : ℝ) with hm
  -- Schwartz IBP for the product `prodS f g` against `φ`.
  have hibp := SchwartzMap.integral_bilinear_lineDerivOp_right_eq_neg_left
    (μ := (volume : Measure Domain3)) (prodS f g) φ (ContinuousLinearMap.mul ℝ ℝ) m
  simp only [ContinuousLinearMap.mul_apply',
    ← LineDeriv.lineDerivOpCLM_apply (R := ℝ) (E := SchwartzMap Domain3 ℝ)] at hibp
  -- `hibp : ∫ (prodS f g)·∂ₘφ = -∫ ∂ₘ(prodS f g)·φ`. Rewrite both integrands.
  rw [show (fun x => (prodS f g) x * (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ) m φ) x)
        = fun x => (f x) * (g x) * (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ) m φ) x by
        funext x; rw [prodS_apply],
      show (fun x => (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ) m (prodS f g)) x * (φ x))
        = fun x => ((lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ) m f) x * g x
            + f x * (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ) m g) x) * (φ x) by
        funext x; rw [lineDerivOp_prodS]] at hibp
  exact hibp

/-! #### Real-part of a complex Schwartz function, as a real Schwartz function -/

/-- The real part of a complex Schwartz function, as a real Schwartz function (post-composition
with `Complex.reCLM`). -/
private noncomputable def reS (φ : SchwartzMap Domain3 ℂ) : SchwartzMap Domain3 ℝ :=
  φ.postcompCLM Complex.reCLM

private theorem reS_apply (φ : SchwartzMap Domain3 ℂ) (x : Domain3) : (reS φ) x = (φ x).re := by
  rw [reS, SchwartzMap.postcompCLM_apply]; rfl

/-- The directional derivative of the real part is the real part of the directional derivative. -/
private theorem lineDerivOp_reS (φ : SchwartzMap Domain3 ℂ) (m x : Domain3) :
    (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ) m (reS φ)) x
      = ((lineDerivOpCLM ℝ (SchwartzMap Domain3 ℂ) m φ) x).re := by
  simp only [LineDeriv.lineDerivOpCLM_apply, lineDerivOp_apply]
  have hφ : HasDerivAt (fun t : ℝ => φ (x + t • m)) ((fderiv ℝ (⇑φ) x) m) 0 :=
    (SchwartzMap.hasFDerivAt φ x).hasLineDerivAt m
  have hcomp := Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 hφ
  simp only [Function.comp_def] at hcomp
  have hfun : (fun t : ℝ => Complex.reCLM (φ (x + t • m))) = fun t : ℝ => (reS φ) (x + t • m) := by
    funext t; rw [reS_apply]; rfl
  rw [hfun] at hcomp
  have hl : HasLineDerivAt ℝ (⇑(reS φ)) (Complex.reCLM ((fderiv ℝ (⇑φ) x) m)) x m := hcomp
  rw [hl.lineDeriv, (SchwartzMap.hasFDerivAt φ x).hasLineDerivAt m |>.lineDeriv]; rfl

/-- The real `L²` class of `reS φ` is the real part `reLp` of the complex `L²` class of `φ`. -/
private theorem reS_toLp_eq_reLp (φ : SchwartzMap Domain3 ℂ) :
    (reS φ).toLp 2 (volume : Measure Domain3)
      = reLp (φ.toLp 2 (volume : Measure Domain3)) := by
  apply Lp.ext
  filter_upwards [(reS φ).coeFn_toLp 2 (volume : Measure Domain3),
    reLp_coeFn (φ.toLp 2 (volume : Measure Domain3)),
    φ.coeFn_toLp 2 (volume : Measure Domain3)] with x h1 h2 h3
  rw [h1, h2, h3, reS_apply]

/-! #### L³-convergence of the multi-direction Schwartz approximants

For the H¹-test extension of the weak Leibniz rule we need the un-differentiated test factor's
Schwartz approximants to converge in `L³`, not just `L²`. This is obtained from a uniform `L⁶`
bound on the (multi-direction) Schwartz sequence — itself a consequence of GNS
(`gns_L6_schwartz`: `‖φ‖₆ ≤ C·‖∇φ‖₂`) plus an `L²∩L⁶ ↪ L³` interpolation. The `L⁶`-Cauchy
property follows because the full gradient of the difference sequence tends to `0` in `L²`. -/

/-- `reS (φ - ψ) x = (reS φ) x - (reS ψ) x` pointwise. -/
private theorem reS_sub_apply (φ ψ : SchwartzMap Domain3 ℂ) (x : Domain3) :
    (reS (φ - ψ)) x = (reS φ) x - (reS ψ) x := by
  rw [reS_apply, reS_apply, reS_apply, SchwartzMap.sub_apply, Complex.sub_re]

/-- **L³-convergence step.**  Given the value-L²-convergent real Schwartz sequence `ψₙ = reS φₙ`
(from the multi-direction Brick-1 sequence `φ`, whose full gradient family `hφgrad` supplies a
uniform `L⁶` bound via GNS), `ψₙ` also converges to `h.re` in `L³`, via the interpolation
`‖g‖₃ ≤ ‖g‖₂^{1/2}·‖g‖₆^{1/2}` applied to `ψₙ - h.re`. -/
private theorem reSchwartz_L3_conv_of_valueConv (h : L2C_R3)
    (hh : MemSobolev 1 2 (h : 𝓢'(Domain3, ℂ)))
    (φ : ℕ → SchwartzMap Domain3 ℂ)
    (hφgrad : ∀ m : Domain3, ∃ (g : L2C_R3)
        (_ : (∂_{m} (h : 𝓢'(Domain3, ℂ))) = (g : 𝓢'(Domain3, ℂ))),
      Filter.Tendsto
        (fun n => (∂_{m} (φ n)).toLp 2 (volume : Measure Domain3))
        Filter.atTop (nhds g))
    (ψ : ℕ → SchwartzMap Domain3 ℝ) (hψdef : ψ = fun n => reS (φ n))
    (hval2 : Filter.Tendsto (fun n => (ψ n).toLp 2 (volume : Measure Domain3))
      Filter.atTop (nhds (reLp h))) :
    ∃ Φ : Lp ℝ 3 (volume : Measure Domain3),
      (⇑Φ =ᵐ[volume] fun x => (h x).re) ∧
      Filter.Tendsto (fun n => (ψ n).toLp 3 (volume : Measure Domain3))
        Filter.atTop (nhds Φ) := by
  -- `h.re ∈ L⁶` (A3/GNS) and `h.re ∈ L²` (Lp membership).
  have hh6 : MemLp (fun x => (h x).re) 6 (volume : Measure Domain3) :=
    (gns_L6_of_memH1_R3 h hh).re
  have hh2 : MemLp (fun x => (h x).re) 2 (volume : Measure Domain3) := (Lp.memLp h).re
  -- `h.re ∈ L³` (interpolation).
  have hh3 : MemLp (fun x => (h x).re) 3 (volume : Measure Domain3) := L2L6_inter_mem_L3 _ hh2 hh6
  set Φ : Lp ℝ 3 (volume : Measure Domain3) := hh3.toLp with hΦdef
  have hΦae : (⇑Φ : Domain3 → ℝ) =ᵐ[volume] fun x => (h x).re := hh3.coeFn_toLp
  refine ⟨Φ, hΦae, ?_⟩
  -- Uniform `L⁶` bound on `ψₙ`: `eLpNorm ψₙ 6 ≤ C` for all `n`.
  -- Each gradient direction `i`: `eLpNorm (∂ᵢφₙ) 2 = ‖(∂ᵢφₙ).toLp 2‖ₑ` is bounded (convergent).
  obtain ⟨C6, hC6_ne_top, hC6⟩ : ∃ C6 : ENNReal, C6 ≠ ⊤ ∧
      ∀ n, eLpNorm ((ψ n) : Domain3 → ℝ) 6 (volume : Measure Domain3) ≤ C6 := by
    -- bound on `eLpNorm (φₙ) 6 ≤ Cgns · ∑ᵢ eLpNorm (∂ᵢφₙ) 2`.
    set Cgns : ENNReal := (SNormLESNormFDerivOfEqConst ℂ (volume : Measure Domain3) 2 : ENNReal)
      with hCgns
    -- each `eLpNorm (∂ᵢφₙ) 2` is bounded: the sequence `(∂ᵢφₙ).toLp 2` converges, hence is bounded.
    have hbdd_i : ∀ i : Fin 3, ∃ Bi : ENNReal, Bi ≠ ⊤ ∧ ∀ n,
        eLpNorm (fun x => (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℂ)
          (EuclideanSpace.single i (1 : ℝ)) (φ n)) x) 2 (volume : Measure Domain3) ≤ Bi := by
      intro i
      obtain ⟨gi, _, hφgi⟩ := hφgrad (EuclideanSpace.single i (1 : ℝ))
      -- the convergent sequence `(∂ᵢφₙ).toLp 2` is bounded in norm.
      obtain ⟨Ri, _, hRi⟩ := (Metric.isBounded_range_of_tendsto _ hφgi).subset_closedBall_lt 0 0
      refine ⟨ENNReal.ofReal Ri, ENNReal.ofReal_ne_top, fun n => ?_⟩
      have hnorm : eLpNorm (fun x => (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℂ)
          (EuclideanSpace.single i (1 : ℝ)) (φ n)) x) 2 (volume : Measure Domain3)
          = ‖(lineDerivOpCLM ℝ (SchwartzMap Domain3 ℂ)
            (EuclideanSpace.single i (1 : ℝ)) (φ n)).toLp 2 (volume : Measure Domain3)‖ₑ := by
        rw [Lp.enorm_def]
        exact (eLpNorm_congr_ae ((lineDerivOpCLM ℝ (SchwartzMap Domain3 ℂ)
          (EuclideanSpace.single i (1 : ℝ)) (φ n)).coeFn_toLp 2 (volume : Measure Domain3)).symm)
      rw [hnorm]
      have hmem : (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℂ)
          (EuclideanSpace.single i (1 : ℝ)) (φ n)).toLp 2 (volume : Measure Domain3)
          ∈ Metric.closedBall (0 : Lp ℂ 2 (volume : Measure Domain3)) Ri :=
        hRi (Set.mem_range_self n)
      rw [Metric.mem_closedBall, dist_zero_right] at hmem
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal hmem
    choose B hBfin hB using hbdd_i
    refine ⟨Cgns * ∑ i : Fin 3, B i, ?_, fun n => ?_⟩
    · refine ENNReal.mul_ne_top (by rw [hCgns]; exact ENNReal.coe_ne_top) ?_
      exact ENNReal.sum_ne_top.mpr (fun i _ => hBfin i)
    -- `eLpNorm (reS φₙ) 6 ≤ eLpNorm φₙ 6 ≤ Cgns · ∑ᵢ eLpNorm (∂ᵢφₙ) 2 ≤ Cgns · ∑ᵢ Bᵢ`.
    have hre6 : eLpNorm ((ψ n) : Domain3 → ℝ) 6 (volume : Measure Domain3)
        ≤ eLpNorm ((φ n) : Domain3 → ℂ) 6 (volume : Measure Domain3) := by
      refine eLpNorm_mono_ae (Filter.Eventually.of_forall fun x => ?_)
      have : ((ψ n) x : ℝ) = (φ n x).re := by rw [hψdef, reS_apply]
      rw [Real.norm_eq_abs, this]
      exact Complex.abs_re_le_norm _
    refine hre6.trans ((gns_L6_schwartz (φ n)).trans ?_)
    rw [← hCgns]
    refine mul_le_mul_right ?_ Cgns
    refine (PlancherelKernels.eLpNorm_fderiv_le_sum_lineDeriv (φ n)).trans ?_
    exact Finset.sum_le_sum (fun i _ => hB i n)
  -- C6 and ‖h.re‖₆ are finite, so the L⁶ bound `D6` is finite.
  have hh6_top : eLpNorm (fun x => (h x).re) 6 (volume : Measure Domain3) ≠ ⊤ :=
    hh6.eLpNorm_lt_top.ne
  -- L⁶-norm of `ψₙ - h.re` is bounded: `≤ C6 + ‖h.re‖₆ =: D6`.
  set D6 : ENNReal := C6 + eLpNorm (fun x => (h x).re) 6 (volume : Measure Domain3) with hD6
  have hD6_ne_top : D6 ≠ ⊤ := by rw [hD6]; exact ENNReal.add_ne_top.mpr ⟨hC6_ne_top, hh6_top⟩
  have hbnd6 : ∀ n, eLpNorm (fun x => (ψ n) x - (h x).re) 6 (volume : Measure Domain3) ≤ D6 := by
    intro n
    refine (eLpNorm_sub_le ((SchwartzMap.continuous _).aestronglyMeasurable)
      hh6.aestronglyMeasurable (by norm_num)).trans ?_
    rw [hD6]; exact add_le_add (hC6 n) (le_refl _)
  -- L²-norm of `ψₙ - h.re` → 0 (from value-L² convergence).
  have h2to0 : Filter.Tendsto
      (fun n => eLpNorm (fun x => (ψ n) x - (h x).re) 2 (volume : Measure Domain3))
      Filter.atTop (nhds 0) := by
    have heq : ∀ n, eLpNorm (fun x => (ψ n) x - (h x).re) 2 (volume : Measure Domain3)
        = ENNReal.ofReal ‖(ψ n).toLp 2 (volume : Measure Domain3) - reLp h‖ := by
      intro n
      rw [ofReal_norm, Lp.enorm_def]
      refine (eLpNorm_congr_ae ?_)
      filter_upwards [Lp.coeFn_sub ((ψ n).toLp 2 (volume : Measure Domain3)) (reLp h),
        (ψ n).coeFn_toLp 2 (volume : Measure Domain3), reLp_coeFn h] with x hx h1 h2
      simp only [hx, Pi.sub_apply, h1, h2]
    rw [show (fun n => eLpNorm (fun x => (ψ n) x - (h x).re) 2 (volume : Measure Domain3))
        = fun n => ENNReal.ofReal ‖(ψ n).toLp 2 (volume : Measure Domain3) - reLp h‖ from funext heq]
    have hd : Filter.Tendsto
        (fun n => ‖(ψ n).toLp 2 (volume : Measure Domain3) - reLp h‖) Filter.atTop (nhds 0) :=
      tendsto_iff_norm_sub_tendsto_zero.mp hval2
    have := ENNReal.tendsto_ofReal hd
    rwa [ENNReal.ofReal_zero] at this
  -- Interpolation bound: `eLpNorm (ψₙ - h.re) 3 ≤ (eLpNorm (ψₙ-h.re) 2)^{1/2}·D6^{1/2}`.
  have hinterp : ∀ n, eLpNorm (fun x => (ψ n) x - (h x).re) 3 (volume : Measure Domain3)
      ≤ (eLpNorm (fun x => (ψ n) x - (h x).re) 2 (volume : Measure Domain3)) ^ (1/2 : ℝ)
        * D6 ^ (1/2 : ℝ) := by
    intro n
    have hmem2 : MemLp (fun x => (ψ n) x - (h x).re) 2 (volume : Measure Domain3) :=
      ((ψ n).memLp 2 (volume : Measure Domain3)).sub hh2
    have hmem6 : MemLp (fun x => (ψ n) x - (h x).re) 6 (volume : Measure Domain3) :=
      ((ψ n).memLp 6 (volume : Measure Domain3)).sub hh6
    refine (PlancherelKernels.eLpNorm_three_le_interp _ hmem2 hmem6).trans ?_
    gcongr
    exact hbnd6 n
  -- Squeeze: RHS → 0^{1/2}·D6^{1/2} = 0.
  have h3to0 : Filter.Tendsto
      (fun n => eLpNorm (fun x => (ψ n) x - (h x).re) 3 (volume : Measure Domain3))
      Filter.atTop (nhds 0) := by
    have hrhs : Filter.Tendsto
        (fun n => (eLpNorm (fun x => (ψ n) x - (h x).re) 2 (volume : Measure Domain3)) ^ (1/2 : ℝ)
          * D6 ^ (1/2 : ℝ)) Filter.atTop (nhds 0) := by
      have h1 : Filter.Tendsto
          (fun n => (eLpNorm (fun x => (ψ n) x - (h x).re) 2 (volume : Measure Domain3)) ^ (1/2 : ℝ))
          Filter.atTop (nhds 0) := by
        have := h2to0.ennrpow_const (1/2 : ℝ)
        rwa [ENNReal.zero_rpow_of_pos (by norm_num)] at this
      have hD6_pow_top : D6 ^ (1/2 : ℝ) ≠ ⊤ :=
        ENNReal.rpow_ne_top_of_nonneg (by norm_num) hD6_ne_top
      have := ENNReal.Tendsto.mul_const h1 (Or.inr hD6_pow_top)
      rwa [zero_mul] at this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hrhs
      (fun n => bot_le) hinterp
  -- `eLpNorm (ψₙ - h.re) 3 → 0` ⇒ `(ψₙ).toLp 3 → Φ` in `Lp ℝ 3`.
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have heqnorm : ∀ n, ‖(ψ n).toLp 3 (volume : Measure Domain3) - Φ‖
      = (eLpNorm (fun x => (ψ n) x - (h x).re) 3 (volume : Measure Domain3)).toReal := by
    intro n
    rw [Lp.norm_def]
    congr 1
    refine eLpNorm_congr_ae ?_
    filter_upwards [Lp.coeFn_sub ((ψ n).toLp 3 (volume : Measure Domain3)) Φ,
      (ψ n).coeFn_toLp 3 (volume : Measure Domain3), hΦae] with x hx h1 h2
    simp only [hx, Pi.sub_apply, h1, h2]
  rw [show (fun n => ‖(ψ n).toLp 3 (volume : Measure Domain3) - Φ‖)
      = fun n => (eLpNorm (fun x => (ψ n) x - (h x).re) 3 (volume : Measure Domain3)).toReal
      from funext heqnorm]
  have := (ENNReal.tendsto_toReal (by simp : (0:ENNReal) ≠ ⊤)).comp h3to0
  rwa [ENNReal.toReal_zero] at this

/-- **L³ approximation of the un-differentiated `H¹` test factor.**
For `h : L2C_R3` in `H^{1,2}` and direction `eₐ` with weak `eₐ`-derivative `(hG : 𝓢')`, there is
a real Schwartz sequence `ψₙ` (the real parts of the multi-direction Brick-1 sequence) that
converges to `reLp h` in `L²`, whose `eₐ`-derivatives converge to `reLp hGval` in `L²`, **and**
which converges to `h.re` in `L³` (`reSchwartz_L3_conv_of_valueConv`). -/
private theorem reSchwartz_L3_approx (h hGval : L2C_R3) (a : Fin 3)
    (hh : MemSobolev 1 2 (h : 𝓢'(Domain3, ℂ)))
    (hG : (∂_{EuclideanSpace.single a (1 : ℝ)} (h : 𝓢'(Domain3, ℂ))) = (hGval : 𝓢'(Domain3, ℂ))) :
    ∃ ψ : ℕ → SchwartzMap Domain3 ℝ,
      Filter.Tendsto (fun n => (ψ n).toLp 2 (volume : Measure Domain3))
          Filter.atTop (nhds (reLp h)) ∧
      Filter.Tendsto (fun n =>
          (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ) (EuclideanSpace.single a (1 : ℝ)) (ψ n)).toLp 2
            (volume : Measure Domain3))
          Filter.atTop (nhds (reLp hGval)) ∧
      ∃ Φ : Lp ℝ 3 (volume : Measure Domain3),
        (⇑Φ =ᵐ[volume] fun x => (h x).re) ∧
        Filter.Tendsto (fun n => (ψ n).toLp 3 (volume : Measure Domain3))
          Filter.atTop (nhds Φ) := by
  classical
  -- Multi-direction Brick-1 sequence φₙ.
  obtain ⟨φ, hφval, hφgrad⟩ := schwartz_h1_gradConv_multi h hh
  -- Direction-a gradient limit gₐ with ∂ₐ(h:𝓢')=(gₐ:𝓢'); identify gₐ = hGval.
  obtain ⟨ga, hga_spec, hφga0⟩ := hφgrad (EuclideanSpace.single a (1 : ℝ))
  have hga_eq : ga = hGval := L2C_eq_of_toTempered_eq (by rw [← hga_spec, hG])
  have hφga : Filter.Tendsto
      (fun n => (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℂ)
        (EuclideanSpace.single a (1 : ℝ)) (φ n)).toLp 2 (volume : Measure Domain3))
      Filter.atTop (nhds hGval) := by rw [← hga_eq]; exact hφga0
  set ψ : ℕ → SchwartzMap Domain3 ℝ := fun n => reS (φ n) with hψdef
  -- (1) value L²: (ψₙ).toLp 2 = reLp (φₙ.toLp 2) → reLp h.
  have hval2 : Filter.Tendsto (fun n => (ψ n).toLp 2 (volume : Measure Domain3))
      Filter.atTop (nhds (reLp h)) := by
    have heq : (fun n => (ψ n).toLp 2 (volume : Measure Domain3))
        = fun n => reLp (φ n |>.toLp 2 (volume : Measure Domain3)) := by
      funext n; rw [hψdef]; exact reS_toLp_eq_reLp (φ n)
    rw [heq]; exact (reLp.continuous.tendsto h).comp hφval
  -- (2) gradient L² (direction a): (∂ₐψₙ).toLp 2 = reLp ((∂ₐφₙ).toLp 2) → reLp hGval.
  have hgrad2 : Filter.Tendsto (fun n =>
      (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ) (EuclideanSpace.single a (1 : ℝ)) (ψ n)).toLp 2
        (volume : Measure Domain3)) Filter.atTop (nhds (reLp hGval)) := by
    have heq : (fun n =>
        (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ) (EuclideanSpace.single a (1 : ℝ)) (ψ n)).toLp
          2 (volume : Measure Domain3))
        = fun n => reLp ((lineDerivOpCLM ℝ (SchwartzMap Domain3 ℂ)
            (EuclideanSpace.single a (1 : ℝ)) (φ n)).toLp 2 (volume : Measure Domain3)) := by
      funext n
      apply Lp.ext
      filter_upwards [(lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
          (EuclideanSpace.single a (1 : ℝ)) (ψ n)).coeFn_toLp 2 (volume : Measure Domain3),
        reLp_coeFn ((lineDerivOpCLM ℝ (SchwartzMap Domain3 ℂ)
          (EuclideanSpace.single a (1 : ℝ)) (φ n)).toLp 2 (volume : Measure Domain3)),
        (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℂ)
          (EuclideanSpace.single a (1 : ℝ)) (φ n)).coeFn_toLp 2 (volume : Measure Domain3)]
        with x h1 h2 h3
      rw [h1, h2, h3, hψdef, lineDerivOp_reS]
    rw [heq]; exact (reLp.continuous.tendsto hGval).comp hφga
  exact ⟨ψ, hval2, hgrad2, reSchwartz_L3_conv_of_valueConv h hh φ hφgrad ψ hψdef hval2⟩

/-- **Per-component Schwartz approximation with real-part gradient convergence.**
For `f : L2C_R3` in `H^{1,2}` and direction `eₐ` whose weak derivative distribution equals
`(g : 𝓢')`, there is a real Schwartz sequence `ψₙ` with `(ψₙ).toLp → reLp f` and
`(∂ₐψₙ).toLp → reLp g` in `Lp ℝ 2`. -/
private theorem reSchwartz_approx (f g : L2C_R3) (a : Fin 3)
    (hf : MemSobolev 1 2 (f : 𝓢'(Domain3, ℂ)))
    (hg : (∂_{EuclideanSpace.single a (1 : ℝ)} (f : 𝓢'(Domain3, ℂ))) = (g : 𝓢'(Domain3, ℂ))) :
    ∃ ψ : ℕ → SchwartzMap Domain3 ℝ,
      Filter.Tendsto (fun n => (ψ n).toLp 2 (volume : Measure Domain3))
          Filter.atTop (nhds (reLp f)) ∧
      Filter.Tendsto (fun n =>
          (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ) (EuclideanSpace.single a (1 : ℝ)) (ψ n)).toLp 2
            (volume : Measure Domain3))
          Filter.atTop (nhds (reLp g)) := by
  obtain ⟨g', hg', φ, hφf, hφg⟩ := schwartz_h1_gradConv f (EuclideanSpace.single a (1 : ℝ)) hf
  -- g' and g are both L² representatives of the same distribution `∂ₐ(f:𝓢')`, hence equal.
  have hgg' : g' = g := L2C_eq_of_toTempered_eq (by rw [← hg', hg])
  subst hgg'
  refine ⟨fun n => reS (φ n), ?_, ?_⟩
  · -- (reS φₙ).toLp = reLp (φₙ.toLp) → reLp f.
    have heq : (fun n => (reS (φ n)).toLp 2 (volume : Measure Domain3))
        = fun n => reLp (φ n |>.toLp 2 (volume : Measure Domain3)) := by
      funext n; exact reS_toLp_eq_reLp (φ n)
    rw [heq]; exact (reLp.continuous.tendsto f).comp hφf
  · -- (∂ₐ(reS φₙ)).toLp = reLp ((∂ₐφₙ).toLp) → reLp g'.
    have heq : (fun n =>
        (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ) (EuclideanSpace.single a (1 : ℝ)) (reS (φ n))).toLp
          2 (volume : Measure Domain3))
        = fun n => reLp ((lineDerivOpCLM ℝ (SchwartzMap Domain3 ℂ)
            (EuclideanSpace.single a (1 : ℝ)) (φ n)).toLp 2 (volume : Measure Domain3)) := by
      funext n
      apply Lp.ext
      filter_upwards [(lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ)
          (EuclideanSpace.single a (1 : ℝ)) (reS (φ n))).coeFn_toLp 2 (volume : Measure Domain3),
        reLp_coeFn ((lineDerivOpCLM ℝ (SchwartzMap Domain3 ℂ)
          (EuclideanSpace.single a (1 : ℝ)) (φ n)).toLp 2 (volume : Measure Domain3)),
        (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℂ)
          (EuclideanSpace.single a (1 : ℝ)) (φ n)).coeFn_toLp 2 (volume : Measure Domain3)]
        with x h1 h2 h3
      rw [h1, h2, h3, lineDerivOp_reS]
    rw [heq]
    -- ∂ₐ in ℂ corresponds via toLp to `∂_{eₐ}(φₙ)`; hφg : (∂ₐφₙ).toLp → g'.
    have hφg' : Filter.Tendsto (fun n =>
        (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℂ) (EuclideanSpace.single a (1 : ℝ)) (φ n)).toLp 2
          (volume : Measure Domain3)) Filter.atTop (nhds g') := hφg
    exact (reLp.continuous.tendsto g').comp hφg'

/-! #### H¹·H¹ weak Leibniz product rule (the analytic heart of B6a) -/

/-- Integrability of a triple product of real Schwartz functions. -/
private theorem Schwartz_mul_mul_integrable (ψ ψ' φ : SchwartzMap Domain3 ℝ) :
    MeasureTheory.Integrable (fun x => (ψ x) * (ψ' x) * (φ x)) (volume : Measure Domain3) := by
  have := (SchwartzMap.bilinLeftCLM (ContinuousLinearMap.mul ℝ ℝ) φ.hasTemperateGrowth
    (SchwartzMap.bilinLeftCLM (ContinuousLinearMap.mul ℝ ℝ) ψ'.hasTemperateGrowth ψ)).integrable
    (μ := (volume : Measure Domain3))
  refine this.congr ?_
  filter_upwards with x
  simp only [SchwartzMap.bilinLeftCLM_apply, ContinuousLinearMap.mul_apply']

/-- Integrability of `(f.re)·(g.re)·φ` for `f, g : L2C_R3` and a real Schwartz test `φ`
(Hölder `L²·L²·L^∞`). -/
private theorem reInt_integrable (f g : L2C_R3) (φ : SchwartzMap Domain3 ℝ) :
    MeasureTheory.Integrable (fun x => (f x).re * (g x).re * (φ x)) (volume : Measure Domain3) := by
  have hfre : MemLp (fun x => (f x).re) 2 (volume : Measure Domain3) := (Lp.memLp f).re
  have hgre : MemLp (fun x => (g x).re) 2 (volume : Measure Domain3) := (Lp.memLp g).re
  have hφ : MemLp (fun x => φ x) ⊤ (volume : Measure Domain3) := φ.memLp_top (volume : Measure Domain3)
  have hfg : MemLp (fun x => (f x).re * (g x).re) 1 (volume : Measure Domain3) :=
    hgre.mul (p := 2) (q := 2) (r := 1) hfre
  have hp := hfg.mul (p := ⊤) (q := 1) (r := 1) hφ
  rw [memLp_one_iff_integrable] at hp
  refine hp.congr ?_
  filter_upwards with x
  simp only [Pi.mul_apply]; ring

/-- For a real Schwartz `ψ` and an essentially bounded `h`, the integral of `ψ·ψ'·h` (Schwartz
values) equals the same integral with the `L²`-classes of `ψ, ψ'` (a.e. equal to `ψ, ψ'`). -/
private theorem integral_schwartz_eq_toLp (ψ ψ' : SchwartzMap Domain3 ℝ) (h : Domain3 → ℝ) :
    ∫ x : Domain3, (ψ x) * (ψ' x) * (h x) ∂(volume : Measure Domain3)
      = ∫ x : Domain3, ((ψ.toLp 2 (volume : Measure Domain3)) x)
          * ((ψ'.toLp 2 (volume : Measure Domain3)) x) * (h x) ∂(volume : Measure Domain3) := by
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [ψ.coeFn_toLp 2 (volume : Measure Domain3),
    ψ'.coeFn_toLp 2 (volume : Measure Domain3)] with x hx hx'
  rw [hx, hx']

/-- **H¹·H¹ weak Leibniz.** For `f, g : L2C_R3` in `H^{1,2}` with weak `eₐ`-derivatives
`fG, gG` (i.e. `∂ₐ(f:𝓢') = (fG:𝓢')`, `∂ₐ(g:𝓢') = (gG:𝓢')`), and any real Schwartz `φ`:

  `∫ (f.re)·(g.re)·(∂ₐφ) = -∫ ((fG.re)·(g.re) + (f.re)·(gG.re))·φ`.

Proved by approximating `f, g, fG, gG` by Schwartz sequences (`reSchwartz_approx`), applying
the classical Schwartz Leibniz IBP (`schwartzLeibniz2`), and passing to the `L²` limit
(`tendsto_integral_mul_mul`). -/
private theorem h1Leibniz2 (f g fG gG : L2C_R3) (a : Fin 3)
    (hf : MemSobolev 1 2 (f : 𝓢'(Domain3, ℂ)))
    (hg : MemSobolev 1 2 (g : 𝓢'(Domain3, ℂ)))
    (hfG : (∂_{EuclideanSpace.single a (1 : ℝ)} (f : 𝓢'(Domain3, ℂ))) = (fG : 𝓢'(Domain3, ℂ)))
    (hgG : (∂_{EuclideanSpace.single a (1 : ℝ)} (g : 𝓢'(Domain3, ℂ))) = (gG : 𝓢'(Domain3, ℂ)))
    (φ : SchwartzMap Domain3 ℝ) :
    ∫ x : Domain3, (f x).re * (g x).re
        * (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ) (EuclideanSpace.single a (1 : ℝ)) φ) x
        ∂(volume : Measure Domain3)
      = -∫ x : Domain3,
          ((fG x).re * (g x).re + (f x).re * (gG x).re) * (φ x)
          ∂(volume : Measure Domain3) := by
  classical
  set m : Domain3 := EuclideanSpace.single a (1 : ℝ) with hm
  -- Schwartz approximants for f and g.
  obtain ⟨ψf, hψf_val, hψf_grad⟩ := reSchwartz_approx f fG a hf hfG
  obtain ⟨ψg, hψg_val, hψg_grad⟩ := reSchwartz_approx g gG a hg hgG
  -- Essential boundedness of the test functions `∂ₐφ` and `φ`.
  have hdφ_bdd : MemLp (fun x => (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ) m φ) x) ⊤
      (volume : Measure Domain3) :=
    (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ) m φ).memLp_top (volume : Measure Domain3)
  have hφ_bdd : MemLp (fun x => φ x) ⊤ (volume : Measure Domain3) :=
    φ.memLp_top (volume : Measure Domain3)
  -- The three convergent integral sequences (LHS and the two RHS terms).
  set LHS : ℕ → ℝ := fun n => ∫ x : Domain3, ((ψf n).toLp 2 (volume : Measure Domain3) x)
      * ((ψg n).toLp 2 (volume : Measure Domain3) x)
      * (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ) m φ) x ∂(volume : Measure Domain3) with hLHSdef
  set R1 : ℕ → ℝ := fun n => ∫ x : Domain3,
      ((lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ) m (ψf n)).toLp 2 (volume : Measure Domain3) x)
        * ((ψg n).toLp 2 (volume : Measure Domain3) x) * (φ x) ∂(volume : Measure Domain3)
    with hR1def
  set R2 : ℕ → ℝ := fun n => ∫ x : Domain3, ((ψf n).toLp 2 (volume : Measure Domain3) x)
      * ((lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ) m (ψg n)).toLp 2 (volume : Measure Domain3) x)
        * (φ x) ∂(volume : Measure Domain3) with hR2def
  -- Per-n Schwartz Leibniz identity: `LHS n = -(R1 n + R2 n)`.
  have hper : ∀ n, LHS n = -(R1 n + R2 n) := by
    intro n
    have hL := schwartzLeibniz2 (ψf n) (ψg n) φ a
    rw [← hm] at hL
    rw [hLHSdef, hR1def, hR2def]
    simp only
    rw [← integral_schwartz_eq_toLp (ψf n) (ψg n),
      ← integral_schwartz_eq_toLp (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ) m (ψf n)) (ψg n) φ,
      ← integral_schwartz_eq_toLp (ψf n) (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ) m (ψg n)) φ]
    rw [hL]
    rw [← MeasureTheory.integral_add (Schwartz_mul_mul_integrable _ _ φ)
      (Schwartz_mul_mul_integrable _ _ φ)]
    refine congrArg Neg.neg (MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_))
    intro x; ring
  -- Limits of each sequence (rewriting the limit point via `reLp_coeFn`).
  have hLHS : Filter.Tendsto LHS Filter.atTop (nhds (∫ x : Domain3, (f x).re * (g x).re
      * (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ) m φ) x ∂(volume : Measure Domain3))) := by
    have h := tendsto_integral_mul_mul _ hdφ_bdd hψf_val hψg_val
    refine h.mono_right (le_of_eq (congrArg nhds (MeasureTheory.integral_congr_ae ?_)))
    filter_upwards [reLp_coeFn f, reLp_coeFn g] with x hxf hxg; rw [hxf, hxg]
  have hR1 : Filter.Tendsto R1 Filter.atTop (nhds (∫ x : Domain3, (fG x).re * (g x).re * (φ x)
      ∂(volume : Measure Domain3))) := by
    have h := tendsto_integral_mul_mul _ hφ_bdd hψf_grad hψg_val
    refine h.mono_right (le_of_eq (congrArg nhds (MeasureTheory.integral_congr_ae ?_)))
    filter_upwards [reLp_coeFn fG, reLp_coeFn g] with x hxf hxg; rw [hxf, hxg]
  have hR2 : Filter.Tendsto R2 Filter.atTop (nhds (∫ x : Domain3, (f x).re * (gG x).re * (φ x)
      ∂(volume : Measure Domain3))) := by
    have h := tendsto_integral_mul_mul _ hφ_bdd hψf_val hψg_grad
    refine h.mono_right (le_of_eq (congrArg nhds (MeasureTheory.integral_congr_ae ?_)))
    filter_upwards [reLp_coeFn f, reLp_coeFn gG] with x hxf hxg; rw [hxf, hxg]
  -- Uniqueness of the limit: LHS limit = -(R1 limit + R2 limit).
  have huniq := tendsto_nhds_unique hLHS ((hR1.add hR2).neg.congr (fun n => (hper n).symm))
  rw [huniq, ← MeasureTheory.integral_add (reInt_integrable fG g φ) (reInt_integrable f gG φ)]
  refine congrArg Neg.neg (MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_))
  intro x; ring

/-! #### Hölder integral pairing limit (for the H¹-test extension) -/

/-- The real `L^p × L^q → ℝ` pairing `(c, k) ↦ ∫ c·k` (for Hölder-conjugate `p q`) is continuous
in `k`; hence `kₙ → k₀` in `Lp q` gives `∫ c·kₙ → ∫ c·k₀`. -/
private theorem tendsto_integral_pairing {p q : ENNReal} [ENNReal.HolderConjugate p q]
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (c : Lp ℝ p (volume : Measure Domain3)) {k : ℕ → Lp ℝ q (volume : Measure Domain3)}
    {k₀ : Lp ℝ q (volume : Measure Domain3)}
    (hk : Filter.Tendsto k Filter.atTop (nhds k₀)) :
    Filter.Tendsto
      (fun n => ∫ x : Domain3, (c x) * (k n x) ∂(volume : Measure Domain3))
      Filter.atTop (nhds (∫ x : Domain3, (c x) * (k₀ x) ∂(volume : Measure Domain3))) := by
  set B : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.mul ℝ ℝ with hB
  have hpair : ∀ a : Lp ℝ q (volume : Measure Domain3),
      (B.lpPairing (volume : Measure Domain3) p q c a)
        = ∫ x : Domain3, (c x) * (a x) ∂(volume : Measure Domain3) := by
    intro a
    rw [ContinuousLinearMap.lpPairing_eq_integral]
    rfl
  have hcont : Filter.Tendsto (fun n => B.lpPairing (volume : Measure Domain3) p q c (k n))
      Filter.atTop (nhds (B.lpPairing (volume : Measure Domain3) p q c k₀)) :=
    ((B.lpPairing (volume : Measure Domain3) p q c).continuous.tendsto k₀).comp hk
  simpa only [hpair] using hcont

/-- **RHS pairing-limit step.**  The `L^{3/2}` coefficients `cR1 := fG.re·g.re`,
`cR2 := f.re·gG.re` (via `L²·L⁶` Hölder) pair against the L³-convergent Schwartz sequence `ψ`
to give the limit `∫ (fG.re·g.re + f.re·gG.re)·ψₙ → ∫ (fG.re·g.re + f.re·gG.re)·vt.re`. -/
private theorem h1Leibniz2_H1test_RHS_limit (f g fG gG vt : L2C_R3)
    (hvt : MemSobolev 1 2 (vt : 𝓢'(Domain3, ℂ)))
    (hf6 : MemLp (fun x => (f x).re) 6 (volume : Measure Domain3))
    (hg6 : MemLp (fun x => (g x).re) 6 (volume : Measure Domain3))
    (ψ : ℕ → SchwartzMap Domain3 ℝ)
    (Φ : Lp ℝ 3 (volume : Measure Domain3))
    (hΦae : (⇑Φ : Domain3 → ℝ) =ᵐ[volume] fun x => (vt x).re)
    (hψ3 : Filter.Tendsto (fun n => (ψ n).toLp 3 (volume : Measure Domain3))
      Filter.atTop (nhds Φ)) :
    Filter.Tendsto
      (fun n => ∫ x : Domain3, ((fG x).re * (g x).re + (f x).re * (gG x).re) * (ψ n) x
        ∂(volume : Measure Domain3))
      Filter.atTop (nhds (∫ x : Domain3,
        ((fG x).re * (g x).re + (f x).re * (gG x).re) * (vt x).re ∂(volume : Measure Domain3))) := by
  -- Membership facts for the coefficient functions.
  have hfGre2 : MemLp (fun x => (fG x).re) 2 (volume : Measure Domain3) := (Lp.memLp fG).re
  have hgGre2 : MemLp (fun x => (gG x).re) 2 (volume : Measure Domain3) := (Lp.memLp gG).re
  -- Coefficients `cR1 = fG.re·g.re`, `cR2 = f.re·gG.re ∈ L^{3/2}` (via L²·L⁶).
  haveI hHT263 : ENNReal.HolderTriple 6 2 (3/2) := by
    have h : Real.HolderTriple (6 : ℝ) (2 : ℝ) (3/2 : ℝ) := by constructor <;> norm_num
    have h2 := h.ennrealOfReal
    have e32 : ENNReal.ofReal (3 / 2 : ℝ) = (3 / 2 : ENNReal) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp
    simpa only [ENNReal.ofReal_ofNat, e32] using h2
  haveI hHT263' : ENNReal.HolderTriple 2 6 (3/2) := by
    have h : Real.HolderTriple (2 : ℝ) (6 : ℝ) (3/2 : ℝ) := by constructor <;> norm_num
    have h2 := h.ennrealOfReal
    have e32 : ENNReal.ofReal (3 / 2 : ℝ) = (3 / 2 : ENNReal) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp
    simpa only [ENNReal.ofReal_ofNat, e32] using h2
  have hcR1_mem : MemLp (fun x => (fG x).re * (g x).re) (3/2) (volume : Measure Domain3) :=
    MeasureTheory.MemLp.ae_eq (Filter.Eventually.of_forall fun x => by simp [Pi.mul_apply, mul_comm])
      (hfGre2.mul (p := 6) (q := 2) (r := 3/2) hg6)
  have hcR2_mem : MemLp (fun x => (f x).re * (gG x).re) (3/2) (volume : Measure Domain3) :=
    MeasureTheory.MemLp.ae_eq (Filter.Eventually.of_forall fun x => by simp [Pi.mul_apply, mul_comm])
      (hf6.mul (p := 2) (q := 6) (r := 3/2) hgGre2)
  set cR1 : Lp ℝ (3/2) (volume : Measure Domain3) := hcR1_mem.toLp with hcR1
  set cR2 : Lp ℝ (3/2) (volume : Measure Domain3) := hcR2_mem.toLp with hcR2
  haveI : Fact ((1 : ENNReal) ≤ 3/2) := ⟨by
    rw [ENNReal.le_div_iff_mul_le (by norm_num) (by norm_num)]; norm_num⟩
  haveI : Fact ((1 : ENNReal) ≤ 3) := ⟨by norm_num⟩
  haveI hHC23 : ENNReal.HolderConjugate (3/2 : ENNReal) 3 := by
    have h : Real.HolderTriple (3/2 : ℝ) (3 : ℝ) (1 : ℝ) := by constructor <;> norm_num
    have h2 := h.ennrealOfReal
    have e32 : ENNReal.ofReal (3 / 2 : ℝ) = (3 / 2 : ENNReal) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp
    simpa only [ENNReal.ofReal_ofNat, ENNReal.ofReal_one, e32] using h2
  have hp1 := tendsto_integral_pairing (p := 3/2) (q := 3) cR1 hψ3
  have hp2 := tendsto_integral_pairing (p := 3/2) (q := 3) cR2 hψ3
  -- Rewrite each pairing to the component integrals.
  have hr1n : ∀ n, ∫ x : Domain3, (cR1 x) * ((ψ n).toLp 3 (volume : Measure Domain3) x)
        ∂(volume : Measure Domain3)
      = ∫ x : Domain3, (fG x).re * (g x).re * (ψ n) x ∂(volume : Measure Domain3) := by
    intro n
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hcR1_mem.coeFn_toLp, (ψ n).coeFn_toLp 3 (volume : Measure Domain3)]
      with x hcx hkx
    rw [hcx, hkx]
  have hr2n : ∀ n, ∫ x : Domain3, (cR2 x) * ((ψ n).toLp 3 (volume : Measure Domain3) x)
        ∂(volume : Measure Domain3)
      = ∫ x : Domain3, (f x).re * (gG x).re * (ψ n) x ∂(volume : Measure Domain3) := by
    intro n
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hcR2_mem.coeFn_toLp, (ψ n).coeFn_toLp 3 (volume : Measure Domain3)]
      with x hcx hkx
    rw [hcx, hkx]
  have hr1lim : ∫ x : Domain3, (cR1 x) * (Φ x) ∂(volume : Measure Domain3)
      = ∫ x : Domain3, (fG x).re * (g x).re * (vt x).re ∂(volume : Measure Domain3) := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hcR1_mem.coeFn_toLp, hΦae] with x hcx hkx
    rw [hcx, hkx]
  have hr2lim : ∫ x : Domain3, (cR2 x) * (Φ x) ∂(volume : Measure Domain3)
      = ∫ x : Domain3, (f x).re * (gG x).re * (vt x).re ∂(volume : Measure Domain3) := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hcR2_mem.coeFn_toLp, hΦae] with x hcx hkx
    rw [hcx, hkx]
  -- Integrability for splitting the sum-integral.
  haveI hHT3321 : ENNReal.HolderTriple (3/2) 3 1 := by
    have h : Real.HolderTriple (3/2 : ℝ) (3 : ℝ) (1 : ℝ) := by constructor <;> norm_num
    have h2 := h.ennrealOfReal
    have e32 : ENNReal.ofReal (3 / 2 : ℝ) = (3 / 2 : ENNReal) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp
    simpa only [ENNReal.ofReal_ofNat, ENNReal.ofReal_one, e32] using h2
  have hint1 : ∀ n, MeasureTheory.Integrable
      (fun x => (fG x).re * (g x).re * (ψ n) x) (volume : Measure Domain3) := by
    intro n
    have := ((ψ n).memLp 3 (volume : Measure Domain3)).mul (p := 3/2) (q := 3) (r := 1) hcR1_mem
    rw [memLp_one_iff_integrable] at this
    refine this.congr ?_
    filter_upwards with x
    simp only [Pi.mul_apply]
  have hint2 : ∀ n, MeasureTheory.Integrable
      (fun x => (f x).re * (gG x).re * (ψ n) x) (volume : Measure Domain3) := by
    intro n
    have := ((ψ n).memLp 3 (volume : Measure Domain3)).mul (p := 3/2) (q := 3) (r := 1) hcR2_mem
    rw [memLp_one_iff_integrable] at this
    refine this.congr ?_
    filter_upwards with x
    simp only [Pi.mul_apply]
  -- Combine: the n-integral = R1ₙ + R2ₙ, with limit hr1lim + hr2lim.
  have hsplit : ∀ n, ∫ x : Domain3, ((fG x).re * (g x).re + (f x).re * (gG x).re) * (ψ n) x
      ∂(volume : Measure Domain3)
      = (∫ x : Domain3, (fG x).re * (g x).re * (ψ n) x ∂(volume : Measure Domain3))
        + ∫ x : Domain3, (f x).re * (gG x).re * (ψ n) x ∂(volume : Measure Domain3) := by
    intro n
    rw [← MeasureTheory.integral_add (hint1 n) (hint2 n)]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    ring
  -- integrability of the two limit coefficients against `vt.re`.
  have hvt_re3 : MemLp (fun x => (vt x).re) 3 (volume : Measure Domain3) :=
    L2L6_inter_mem_L3 _ (Lp.memLp vt).re ((gns_L6_of_memH1_R3 vt hvt).re)
  have hintlim1 : MeasureTheory.Integrable
      (fun x => (fG x).re * (g x).re * (vt x).re) (volume : Measure Domain3) := by
    have := ((hvt_re3).mul (p := 3/2) (q := 3) (r := 1) hcR1_mem)
    rw [memLp_one_iff_integrable] at this
    refine this.congr ?_; filter_upwards with x; simp only [Pi.mul_apply]
  have hintlim2 : MeasureTheory.Integrable
      (fun x => (f x).re * (gG x).re * (vt x).re) (volume : Measure Domain3) := by
    have := ((hvt_re3).mul (p := 3/2) (q := 3) (r := 1) hcR2_mem)
    rw [memLp_one_iff_integrable] at this
    refine this.congr ?_; filter_upwards with x; simp only [Pi.mul_apply]
  have hcomb := ((hp1.congr hr1n).add (hp2.congr hr2n))
  rw [hr1lim, hr2lim, ← MeasureTheory.integral_add hintlim1 hintlim2] at hcomb
  have hcomb2 : Filter.Tendsto
      (fun n => ∫ x : Domain3, ((fG x).re * (g x).re + (f x).re * (gG x).re) * (ψ n) x
        ∂(volume : Measure Domain3)) Filter.atTop
      (nhds (∫ x : Domain3, ((fG x).re * (g x).re * (vt x).re
        + (f x).re * (gG x).re * (vt x).re) ∂(volume : Measure Domain3))) :=
    hcomb.congr (fun n => (hsplit n).symm)
  refine hcomb2.mono_right (le_of_eq (congrArg nhds ?_))
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  ring

/-- **H¹-test weak Leibniz.** Same as `h1Leibniz2`, but the test factor is an `H¹` function `vt`
(with weak `eₐ`-derivative `vtG`) rather than a Schwartz function. The un-differentiated test is
paired in `L³` (its multi-direction Schwartz approximants converge in `L³` via
`reSchwartz_L3_approx`, and pair against the `L^{3/2}` coefficients via
`h1Leibniz2_H1test_RHS_limit`); the differentiated test in `L²`. -/
theorem h1Leibniz2_H1test (f g fG gG vt vtG : L2C_R3) (a : Fin 3)
    (hf : MemSobolev 1 2 (f : 𝓢'(Domain3, ℂ)))
    (hg : MemSobolev 1 2 (g : 𝓢'(Domain3, ℂ)))
    (hfG : (∂_{EuclideanSpace.single a (1 : ℝ)} (f : 𝓢'(Domain3, ℂ))) = (fG : 𝓢'(Domain3, ℂ)))
    (hgG : (∂_{EuclideanSpace.single a (1 : ℝ)} (g : 𝓢'(Domain3, ℂ))) = (gG : 𝓢'(Domain3, ℂ)))
    (hvt : MemSobolev 1 2 (vt : 𝓢'(Domain3, ℂ)))
    (hvtG : (∂_{EuclideanSpace.single a (1 : ℝ)} (vt : 𝓢'(Domain3, ℂ))) = (vtG : 𝓢'(Domain3, ℂ)))
    (hf6 : MemLp (fun x => (f x).re) 6 (volume : Measure Domain3))
    (hf3 : MemLp (fun x => (f x).re) 3 (volume : Measure Domain3))
    (hg6 : MemLp (fun x => (g x).re) 6 (volume : Measure Domain3)) :
    ∫ x : Domain3, (f x).re * (g x).re * (vtG x).re ∂(volume : Measure Domain3)
      = -∫ x : Domain3,
          ((fG x).re * (g x).re + (f x).re * (gG x).re) * (vt x).re
          ∂(volume : Measure Domain3) := by
  classical
  set m : Domain3 := EuclideanSpace.single a (1 : ℝ) with hm
  -- L³ approximation of the test factor `vt`.
  obtain ⟨ψ, hψ_val, hψ_grad, Φ, hΦae, hψ3⟩ := reSchwartz_L3_approx vt vtG a hvt hvtG
  -- Membership facts for the coefficient functions.
  have hfre2 : MemLp (fun x => (f x).re) 2 (volume : Measure Domain3) := (Lp.memLp f).re
  have hgre2 : MemLp (fun x => (g x).re) 2 (volume : Measure Domain3) := (Lp.memLp g).re
  -- Coefficient `cLHS = f.re·g.re ∈ L²` (via L³·L⁶).
  haveI hHT362 : ENNReal.HolderTriple 6 3 2 := instHolderTriple_6_3_2
  have hcLHS_mem : MemLp (fun x => (f x).re * (g x).re) 2 (volume : Measure Domain3) :=
    MeasureTheory.MemLp.ae_eq (Filter.Eventually.of_forall fun x => by simp [Pi.mul_apply, mul_comm])
      (hf3.mul (p := 6) (q := 3) (r := 2) hg6)
  set cLHS : Lp ℝ 2 (volume : Measure Domain3) := hcLHS_mem.toLp with hcLHS
  haveI : Fact ((1 : ENNReal) ≤ 2) := ⟨by norm_num⟩
  haveI hHC22 : ENNReal.HolderConjugate (2 : ENNReal) 2 := ⟨by
    rw [inv_one]; exact ENNReal.inv_two_add_inv_two⟩
  -- Per-n Schwartz Leibniz identity (Schwartz test `ψ n`).
  have hper : ∀ n,
      ∫ x : Domain3, (f x).re * (g x).re
        * (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ) m (ψ n)) x ∂(volume : Measure Domain3)
      = -∫ x : Domain3,
          ((fG x).re * (g x).re + (f x).re * (gG x).re) * (ψ n) x
          ∂(volume : Measure Domain3) :=
    fun n => h1Leibniz2 f g fG gG a hf hg hfG hgG (ψ n)
  -- LHS limit: `∫ (f.re·g.re)·(∂ₐψₙ) → ∫ (f.re·g.re)·(vtG.re)` (pairing 2,2).
  have hLHS : Filter.Tendsto
      (fun n => ∫ x : Domain3, (f x).re * (g x).re
        * (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ) m (ψ n)) x ∂(volume : Measure Domain3))
      Filter.atTop (nhds (∫ x : Domain3, (f x).re * (g x).re * (vtG x).re
        ∂(volume : Measure Domain3))) := by
    have hpair := tendsto_integral_pairing (p := 2) (q := 2) cLHS hψ_grad
    -- rewrite the pairing integrals to match.
    have hkn : ∀ n, ∫ x : Domain3, (cLHS x)
        * ((lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ) m (ψ n)).toLp 2 (volume : Measure Domain3)) x
          ∂(volume : Measure Domain3)
        = ∫ x : Domain3, (f x).re * (g x).re
          * (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ) m (ψ n)) x ∂(volume : Measure Domain3) := by
      intro n
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [hcLHS_mem.coeFn_toLp,
        (lineDerivOpCLM ℝ (SchwartzMap Domain3 ℝ) m (ψ n)).coeFn_toLp 2 (volume : Measure Domain3)]
        with x hcx hkx
      rw [hcx, hkx]
    have hk0 : ∫ x : Domain3, (cLHS x) * ((reLp vtG) x) ∂(volume : Measure Domain3)
        = ∫ x : Domain3, (f x).re * (g x).re * (vtG x).re ∂(volume : Measure Domain3) := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [hcLHS_mem.coeFn_toLp, reLp_coeFn vtG] with x hcx hkx
      rw [hcx, hkx]
    rw [← hk0]
    refine hpair.congr (fun n => hkn n)
  -- RHS limit: `∫ (fG.re·g.re + f.re·gG.re)·ψₙ → ∫(...)·vt.re` (pairing 3/2,3), via the
  -- extracted step.
  have hRHS := h1Leibniz2_H1test_RHS_limit f g fG gG vt hvt hf6 hg6 ψ Φ hΦae hψ3
  -- Equate the two limits.
  have hlim : (∫ x : Domain3, (f x).re * (g x).re * (vtG x).re ∂(volume : Measure Domain3))
      = -(∫ x : Domain3, ((fG x).re * (g x).re + (f x).re * (gG x).re) * (vt x).re
          ∂(volume : Measure Domain3)) := by
    refine tendsto_nhds_unique hLHS ?_
    exact (hRHS.neg).congr (fun n => (hper n).symm)
  exact hlim

end LerayHopf
