-- Narrowest import: provides `stokesTestPairing` + `IsGalerkinTest` (via SolutionInterfaces)
-- and `velocitySpan` (defined here). No heavier ODE-solver layer needed. (AGENTS.md rule 10)
import LerayHopf.Torus.GalerkinScheme

open MeasureTheory Filter Topology

/-!
# Torus test family for the T-AL-1 campaign (issue #23)

This file belongs to the `T-AL-1` node of the torus `aubin_lions` mode-wise
de-axiomatization campaign; see `docs/scratch/torus-aubinlions-modewise-plan.md`.

Two statements were transcribed VERBATIM from the Phase-0 campaign spike (now deleted;
see PR history); proof bodies were discharged by `lean-prover`.

* `stokesTestPairing_bound_of_galerkinTest` (plan §2 P0.2 / S1):
  the Stokes test pairing with a Galerkin test is bounded by `C(w)·‖u‖`.

* `exists_galerkin_test_family` (plan §2 P0.1 / S2):
  there exists a countable family of Galerkin tests that finitely spans each
  finite-dimensional `velocitySpan N`.
-/

namespace LerayHopf

/-! ## P0.2 (S1) — Stokes pairing bound for band-limited tests

`stokesTestPairing u w` is the mode sum `∑_j ∑'_k (2π)²|k|² Re(û_j(k)·conj(ŵ_j(k)))`;
for a Galerkin test `w` the `k`-sum is a finite `fourierBox` sum (`coeff_zero_outside_box`),
so finite Cauchy–Schwarz gives the `C(w)·‖u‖` bound. -/
theorem stokesTestPairing_bound_of_galerkinTest (w : L2Sigma) (hw : IsGalerkinTest w) :
    ∃ C : ℝ, ∀ u : L2VF, |stokesTestPairing u (w : L2VF)| ≤ C * ‖u‖ := by
  obtain ⟨n₀, hn₀⟩ := hw
  classical
  -- Witness: finite fourierBox n₀ sum of mode weights times ‖ŵⱼ(k)‖
  refine ⟨∑ j : Fin 3, ∑ k ∈ fourierBox n₀,
      |(2 * Real.pi) ^ 2 * ∑ i : Fin 3, (k i : ℝ) ^ 2| *
        (‖fourierCoeffCLM k‖ * ‖L2VF_projComponentC j‖) *
        ‖mFourierCoeff3 (L2VF_projComponentC j (w : L2VF)) k‖, fun u => ?_⟩
  -- Step 1: collapse the ∑' over k to a finite sum over fourierBox n₀,
  -- using that ŵⱼ(k) = 0 for k ∉ fourierBox n₀ (coeff_zero_outside_box).
  have hboxsum : stokesTestPairing u (w : L2VF) =
      ∑ j : Fin 3, ∑ k ∈ fourierBox n₀,
        ((2 * Real.pi) ^ 2 * ∑ i : Fin 3, (k i : ℝ) ^ 2) *
          (mFourierCoeff3 (L2VF_projComponentC j u) k *
            starRingEnd ℂ (mFourierCoeff3 (L2VF_projComponentC j (w : L2VF)) k)).re := by
    unfold stokesTestPairing; congr 1; ext j
    apply tsum_eq_sum; intro k hk
    simp [coeff_zero_outside_box n₀ (w : L2VF) hn₀ j k hk]
  rw [hboxsum]
  -- Step 2: triangle inequality for both finite sums
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ => ?_
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun k _ => ?_
  -- Step 3: per-mode bound via Cauchy–Schwarz on the Fourier coefficient
  set cjk : ℝ := (2 * Real.pi) ^ 2 * ∑ i : Fin 3, (k i : ℝ) ^ 2 with hcjk
  set cu : ℂ := mFourierCoeff3 (L2VF_projComponentC j u) k with hcu
  set cw_k : ℂ := mFourierCoeff3 (L2VF_projComponentC j (w : L2VF)) k with hcw
  rw [abs_mul]
  -- |Re(cu · conj(cw_k))| ≤ ‖cu‖ · ‖cw_k‖
  have hre : |(cu * starRingEnd ℂ cw_k).re| ≤ ‖cu‖ * ‖cw_k‖ :=
    calc |(cu * starRingEnd ℂ cw_k).re|
        ≤ ‖cu * starRingEnd ℂ cw_k‖ := Complex.abs_re_le_norm _
      _ = ‖cu‖ * ‖cw_k‖ := by rw [norm_mul, RCLike.norm_conj]
  -- ‖cu‖ = ‖fourierCoeffCLM k (L2VF_projComponentC j u)‖ ≤ ‖fourierCoeffCLM k‖ · ‖L2VF_projComponentC j‖ · ‖u‖
  have hcubd : ‖cu‖ ≤ ‖fourierCoeffCLM k‖ * ‖L2VF_projComponentC j‖ * ‖u‖ := by
    rw [hcu, ← fourierCoeffCLM_apply]
    calc ‖fourierCoeffCLM k (L2VF_projComponentC j u)‖
        ≤ ‖fourierCoeffCLM k‖ * ‖L2VF_projComponentC j u‖ := (fourierCoeffCLM k).le_opNorm _
      _ ≤ ‖fourierCoeffCLM k‖ * (‖L2VF_projComponentC j‖ * ‖u‖) := by
            gcongr; exact (L2VF_projComponentC j).le_opNorm _
      _ = ‖fourierCoeffCLM k‖ * ‖L2VF_projComponentC j‖ * ‖u‖ := by ring
  calc |cjk| * |(cu * starRingEnd ℂ cw_k).re|
      ≤ |cjk| * (‖cu‖ * ‖cw_k‖) := by gcongr
    _ ≤ |cjk| * ((‖fourierCoeffCLM k‖ * ‖L2VF_projComponentC j‖ * ‖u‖) * ‖cw_k‖) := by gcongr
    _ = |cjk| * (‖fourierCoeffCLM k‖ * ‖L2VF_projComponentC j‖) * ‖cw_k‖ * ‖u‖ := by ring

/-! ## P0.1 (S2) — the countable band-limited div-free test family

A countable family of Galerkin tests that finitely spans each finite-dimensional
`velocitySpan N`; density in `L2Sigma` follows from `velocityProjection_n_tendsto`. -/
theorem exists_galerkin_test_family :
    ∃ w : ℕ → L2Sigma,
      (∀ m, IsGalerkinTest (w m)) ∧
      ∀ N : ℕ, ∃ s : Finset ℕ,
        velocitySpan N ≤ Submodule.span ℝ ((fun m => ((w m : L2Sigma) : L2VF)) '' ↑s) := by
  classical
  -- Step 1: each finite-dimensional `velocitySpan N` is finitely generated, so pick a
  -- spanning finset `S N : Finset L2VF`.
  have hspan : ∀ N : ℕ, ∃ S : Finset L2VF,
      Submodule.span ℝ (↑S : Set L2VF) = velocitySpan N := fun N =>
    Module.Finite.iff_fg.mp inferInstance
  choose S hS using hspan
  -- Step 2: flatten `⋃ N S N` into a single ℕ-indexed family via `Nat.pair`.  The value at
  -- `m` is the `(m.unpair.2)`-th element of the list of `S (m.unpair.1)`, padded with `0`.
  let f : ℕ → L2VF := fun m => ((S m.unpair.1).toList[m.unpair.2]?).getD 0
  -- Every value of `f` lies in the corresponding `velocitySpan`, hence in `L2Sigma`.
  have hmemspan : ∀ m : ℕ, f m ∈ velocitySpan m.unpair.1 := by
    intro m
    show ((S m.unpair.1).toList[m.unpair.2]?).getD 0 ∈ velocitySpan m.unpair.1
    rcases h : (S m.unpair.1).toList[m.unpair.2]? with _ | x
    · simp only [Option.getD_none]; exact (velocitySpan m.unpair.1).zero_mem
    · rw [Option.getD_some]
      have hxmem : x ∈ (S m.unpair.1).toList := by
        rw [List.getElem?_eq_some_iff] at h
        obtain ⟨hlt, rfl⟩ := h
        exact List.getElem_mem hlt
      rw [Finset.mem_toList] at hxmem
      have := Submodule.subset_span (R := ℝ) (s := (↑(S m.unpair.1) : Set L2VF)) hxmem
      rwa [hS m.unpair.1] at this
  have hmemsigma : ∀ m : ℕ, f m ∈ L2Sigma := fun m =>
    velocitySpan_le_sigma m.unpair.1 (hmemspan m)
  -- Assemble the family in `L2Sigma`.
  refine ⟨fun m => ⟨f m, hmemsigma m⟩, ?_, ?_⟩
  · -- Every member is a Galerkin test: it is fixed by its own projector.
    intro m
    exact ⟨m.unpair.1, velocityP_fixes_span m.unpair.1 ⟨f m, hmemspan m⟩⟩
  · -- Each `velocitySpan N` is spanned by the images at indices `Nat.pair N i`.
    intro N
    refine ⟨(Finset.range (S N).toList.length).image (Nat.pair N), ?_⟩
    rw [← hS N]
    refine Submodule.span_mono ?_
    intro x hx
    rw [Finset.mem_coe, ← Finset.mem_toList, List.mem_iff_getElem] at hx
    obtain ⟨i, hilt, hget⟩ := hx
    refine ⟨Nat.pair N i, ?_, ?_⟩
    · rw [Finset.mem_coe, Finset.mem_image]
      exact ⟨i, Finset.mem_range.mpr hilt, rfl⟩
    · show f (Nat.pair N i) = x
      show ((S (Nat.pair N i).unpair.1).toList[(Nat.pair N i).unpair.2]?).getD 0 = x
      rw [Nat.unpair_pair, List.getElem?_eq_getElem hilt, Option.getD_some, hget]

end LerayHopf
