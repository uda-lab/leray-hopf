-- SCRATCH — issue #195 feasibility spike (lean-architect). NOT production code.
-- Codex-gate remediation (findings 1 and 4 of the B0 adversarial review):
--
-- Finding 1: the global contract of docs/scratch/global-diagonal-campaign.md §4 existed
-- only as markdown.  Here every §4 statement is MACHINE-CHECKED: `IsLerayHopfOn` (the
-- Prop-valued conjunction of the five proof fields of `Galerkin.LerayHopfSolution`),
-- the round-trip equivalence with `Nonempty (Galerkin.LerayHopfSolution …)`, the
-- single-curve `GlobalLerayHopfSolution` with its `toSolution`/`toSolution_u` (rfl)
-- no-duplication witnesses, the horizon-restriction lemma `IsLerayHopfOn.mono`, and the
-- curve-congruence lemma `IsLerayHopfOn.congr_Icc`.  (The frozen torus P4 target
-- `GlobalTorusCapstoneStatement` lives in Scratch/GlobalContractTorus.lean — see the
-- F-B note below.)
--
-- Finding 4: `WeakFormNS.mono`'s truncation step is compiled here WITHOUT any
-- integrability hypothesis (`setIntegral_Ioc_eq_of_tail_zero`: the integrands are
-- pointwise-equal indicator functions, so Bochner integrals agree even when both are
-- junk values), with the non-integrable branch witnessed CONCRETELY
-- (`badTail_not_integrableOn` + `badTail_truncation`) and the integrable branch
-- cross-checked against GENUINE union additivity (`truncation_agrees_with_additivity`
-- invokes `setIntegral_union`; `truncation_routes_agree` shows both routes emit the
-- same equation — codex pass-2 finding F-C).
--
-- Pass-2 finding F-B (import-cone separation): this file now imports ONLY the generic
-- solution-bundle layer, matching the frozen P1 design target
-- `LerayHopf/Galerkin/GlobalContract.lean`.  The torus capstone statement lives in
-- `LerayHopf/Scratch/GlobalContractTorus.lean`, which imports this file plus
-- `LerayHopf.Torus.SolutionInterfaces` — compiling both proves generic layering and
-- the torus target are separable exactly as P1 specifies.
--
-- All declarations below are fully proved (no sorry, no axioms).
import LerayHopf.Galerkin.SolutionBundles
import Mathlib.Analysis.SpecialFunctions.NonIntegrable
import Mathlib.Analysis.Calculus.Deriv.Support

open MeasureTheory Filter Topology Set

namespace LerayHopf
namespace Scratch195

/-! ### Finding 4 — truncation without integrability -/

/-- **Tail-truncation for set integrals, no integrability hypothesis.**  If `f` vanishes
on `(b, c]` then its Bochner integrals over `Ioc a c` and `Ioc a b` coincide: the two
indicator functions are *pointwise equal*, so the integrals agree even when `f` is not
integrable on either set (both sides are then the same junk value `0`).  This is the
exact step `WeakFormNS.mono` needs, and it never invokes interval additivity. -/
theorem setIntegral_Ioc_eq_of_tail_zero {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] {f : ℝ → X} {a b c : ℝ} (hbc : b ≤ c)
    (hf : ∀ t, b < t → t ≤ c → f t = 0) :
    ∫ t in Set.Ioc a c, f t = ∫ t in Set.Ioc a b, f t := by
  have hind : (Set.Ioc a c).indicator f = (Set.Ioc a b).indicator f := by
    funext x
    by_cases hxc : x ∈ Set.Ioc a c
    · by_cases hxb : x ∈ Set.Ioc a b
      · rw [Set.indicator_of_mem hxc, Set.indicator_of_mem hxb]
      · have hbx : b < x := by
          rcases hxc with ⟨hax, hxc'⟩
          by_contra hnb
          exact hxb ⟨hax, not_lt.mp hnb⟩
        rw [Set.indicator_of_mem hxc, Set.indicator_of_notMem hxb, hf x hbx hxc.2]
    · have hxb : x ∉ Set.Ioc a b := fun hx => hxc (Set.Ioc_subset_Ioc le_rfl hbc hx)
      rw [Set.indicator_of_notMem hxc, Set.indicator_of_notMem hxb]
  rw [← integral_indicator measurableSet_Ioc, ← integral_indicator measurableSet_Ioc,
    hind]

/-- Concrete NON-integrable branch witness: `1/t` up to time `1`, then `0`. -/
noncomputable def badTail : ℝ → ℝ := fun t => if t ≤ 1 then t⁻¹ else 0

theorem badTail_tail_zero : ∀ t : ℝ, 1 < t → t ≤ 2 → badTail t = 0 := by
  intro t ht _
  simp [badTail, not_le.mpr ht]

/-- `badTail` is genuinely non-integrable on `Ioc 0 2` (it dominates `1/t` near `0`),
so `badTail_truncation` below exercises the junk-value branch of
`setIntegral_Ioc_eq_of_tail_zero`, where interval additivity is NOT available. -/
theorem badTail_not_integrableOn :
    ¬ IntegrableOn badTail (Set.Ioc 0 2) volume := by
  intro hInt
  have h1 : IntegrableOn badTail (Set.Ioc 0 1) volume :=
    hInt.mono_set (Set.Ioc_subset_Ioc le_rfl one_le_two)
  have h2 : IntegrableOn (fun t : ℝ => t⁻¹) (Set.Ioc 0 1) volume :=
    h1.congr_fun (fun t ht => by simp [badTail, ht.2]) measurableSet_Ioc
  have h3 : IntervalIntegrable (fun t : ℝ => t⁻¹) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr h2
  rcases intervalIntegrable_inv_iff.mp h3 with h | h
  · exact one_ne_zero h.symm
  · exact h Set.left_mem_uIcc

/-- The truncation identity holds for the non-integrable `badTail` — compiled evidence
that the `WeakFormNS.mono` restriction step is sound with NO integrability side
condition (codex finding 4's "non-integrable prefix" scenario). -/
theorem badTail_truncation :
    ∫ t in Set.Ioc (0 : ℝ) 2, badTail t = ∫ t in Set.Ioc (0 : ℝ) 1, badTail t :=
  setIntegral_Ioc_eq_of_tail_zero one_le_two badTail_tail_zero

/-- Integrable-branch cross-check via the REAL classical route (codex pass-2 F-C):
under integrability, `Ioc 0 c = Ioc 0 b ∪ Ioc b c` and `setIntegral_union` give genuine
union additivity — the first conjunct is proved by ADDITIVITY, not by re-running the
indicator route — and the tail integral vanishes.  Both `0 ≤ b` (for the union
decomposition) and integrability (for `setIntegral_union`, restricted to each piece by
`mono_set`) are genuinely consumed. -/
theorem truncation_agrees_with_additivity {f : ℝ → ℝ} {b c : ℝ}
    (hb : 0 ≤ b) (hbc : b ≤ c)
    (hfint : IntegrableOn f (Set.Ioc 0 c) volume)
    (hf : ∀ t, b < t → t ≤ c → f t = 0) :
    (∫ t in Set.Ioc 0 c, f t) =
        (∫ t in Set.Ioc 0 b, f t) + (∫ t in Set.Ioc b c, f t) ∧
      (∫ t in Set.Ioc b c, f t) = 0 := by
  have hunion : Set.Ioc (0 : ℝ) b ∪ Set.Ioc b c = Set.Ioc 0 c :=
    Set.Ioc_union_Ioc_eq_Ioc hb hbc
  constructor
  · rw [← hunion]
    exact setIntegral_union (Set.Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
      (hfint.mono_set (Set.Ioc_subset_Ioc le_rfl hbc))
      (hfint.mono_set (Set.Ioc_subset_Ioc hb le_rfl))
  · have hzero : EqOn f (fun _ => (0 : ℝ)) (Set.Ioc b c) := fun t ht => hf t ht.1 ht.2
    calc ∫ t in Set.Ioc b c, f t = ∫ _t in Set.Ioc b c, (0 : ℝ) :=
          setIntegral_congr_fun measurableSet_Ioc hzero
      _ = 0 := integral_zero _ _

/-- **The two routes agree on the integrable branch**: classical additivity plus the
vanishing tail yields exactly the equation `setIntegral_Ioc_eq_of_tail_zero` produces
with no integrability at all — so the indicator route is conservative over the
standard argument, now as a THEOREM rather than a prose claim. -/
theorem truncation_routes_agree {f : ℝ → ℝ} {b c : ℝ}
    (hb : 0 ≤ b) (hbc : b ≤ c)
    (hfint : IntegrableOn f (Set.Ioc 0 c) volume)
    (hf : ∀ t, b < t → t ≤ c → f t = 0) :
    (∫ t in Set.Ioc 0 c, f t) = ∫ t in Set.Ioc 0 b, f t := by
  obtain ⟨hadd, hzero⟩ := truncation_agrees_with_additivity hb hbc hfint hf
  rw [hadd, hzero, add_zero]

/-! ### Finding 1 — the global contract, machine-checked

Statements below mirror docs/scratch/global-diagonal-campaign.md §4 verbatim, over the
REAL generic layer (`Galerkin.Domain`, `Galerkin.NSFormCore`,
`Galerkin.LerayHopfSolution` from `LerayHopf/Galerkin/SolutionBundles.lean`).  P1 will
move them (unchanged) out of the `Scratch195` namespace into production. -/

/-- **Prop-valued Leray–Hopf contract on `[0, T]`** — the conjunction of the five proof
fields of `Galerkin.LerayHopfSolution`, with the curve `u` exposed as an argument
instead of bundled as data.  Field-for-field mirror of
`LerayHopf/Galerkin/SolutionBundles.lean:68`. -/
def IsLerayHopfOn (D : Galerkin.Domain) (C : Galerkin.NSFormCore D) (ν T : ℝ)
    (u₀ : ↥D.σ) (u : Time → ↥D.σ) : Prop :=
  WeakFormNS ν T (D.evolution C) u ∧
  (∀ t, 0 ≤ t → t ≤ T →
    (1 / 2 : ℝ) * ‖(u t : D.X)‖ ^ 2 + ∫ s in (0 : ℝ)..t, D.dissip ν ↑(u s)
      ≤ (1 / 2 : ℝ) * ‖(u₀ : D.X)‖ ^ 2) ∧
  Filter.Tendsto (fun t => (u t : D.X)) (nhdsWithin 0 (Set.Ici 0)) (nhds ↑u₀) ∧
  ((∀ᵐ t ∂(volume.restrict (Set.Icc 0 T)), D.regMem ↑(u t)) ∧
    IntervalIntegrable (fun s => D.dissip ν ↑(u s)) volume 0 T) ∧
  AEStronglyMeasurable (fun t => (u t : D.X)) (volume.restrict (Set.Icc 0 T))

variable {D : Galerkin.Domain} {C : Galerkin.NSFormCore D} {ν T T' : ℝ} {u₀ : ↥D.σ}

/-- Projection: a proof-carrying solution satisfies the Prop-valued contract. -/
theorem LerayHopfSolution.isLerayHopfOn (s : Galerkin.LerayHopfSolution D C ν T u₀) :
    IsLerayHopfOn D C ν T u₀ s.u :=
  ⟨s.weak_eq, s.energy_ineq, s.initial_trace, s.energy_class,
    s.u_aestronglyMeasurable⟩

/-- Packing: the Prop-valued contract rebuilds the proof-carrying solution with the
SAME curve (no data change, no choice). -/
def LerayHopfSolution.ofIsOn {u : Time → ↥D.σ} (h : IsLerayHopfOn D C ν T u₀ u) :
    Galerkin.LerayHopfSolution D C ν T u₀ where
  u := u
  weak_eq := h.1
  energy_ineq := h.2.1
  initial_trace := h.2.2.1
  energy_class := h.2.2.2.1
  u_aestronglyMeasurable := h.2.2.2.2

/-- The packing preserves the curve on the nose. -/
theorem LerayHopfSolution.ofIsOn_u {u : Time → ↥D.σ} (h : IsLerayHopfOn D C ν T u₀ u) :
    (LerayHopfSolution.ofIsOn h).u = u := rfl

/-- **Round-trip equivalence:** the Prop-valued contract is *exactly* as strong as
`Nonempty (Galerkin.LerayHopfSolution …)` per horizon — the finite-horizon conjunct of
the global contract is not a weakening (codex focus question (i)). -/
theorem nonempty_lerayHopfSolution_iff_exists_isOn :
    Nonempty (Galerkin.LerayHopfSolution D C ν T u₀) ↔
      ∃ u : Time → ↥D.σ, IsLerayHopfOn D C ν T u₀ u := by
  constructor
  · rintro ⟨s⟩
    exact ⟨s.u, LerayHopfSolution.isLerayHopfOn s⟩
  · rintro ⟨u, h⟩
    exact ⟨LerayHopfSolution.ofIsOn h⟩

/-- **The global contract**: ONE curve field, and the finite-horizon contract for THAT
curve at EVERY positive horizon.  The logical content is literally
`∃ u, ∀ T > 0, IsLerayHopfOn … u` (see `globalLerayHopfSolution_nonempty_iff`) — not a
repackaged `∀ T, ∃ u_T`. -/
structure GlobalLerayHopfSolution (D : Galerkin.Domain) (C : Galerkin.NSFormCore D)
    (ν : ℝ) (u₀ : ↥D.σ) where
  /-- The single global solution curve. -/
  u : Time → ↥D.σ
  /-- The finite-horizon Leray–Hopf contract for `u`, at every positive horizon. -/
  isOn : ∀ T : ℝ, 0 < T → IsLerayHopfOn D C ν T u₀ u

/-- The global structure IS the literal `∃ u, ∀ T > 0, …` statement (curve duplication
or quantifier reordering would break this `rfl`-adjacent equivalence). -/
theorem globalLerayHopfSolution_nonempty_iff :
    Nonempty (GlobalLerayHopfSolution D C ν u₀) ↔
      ∃ u : Time → ↥D.σ, ∀ T : ℝ, 0 < T → IsLerayHopfOn D C ν T u₀ u := by
  constructor
  · rintro ⟨g⟩
    exact ⟨g.u, g.isOn⟩
  · rintro ⟨u, h⟩
    exact ⟨⟨u, h⟩⟩

/-- Horizon slice of a global solution — WITHOUT changing the curve. -/
def GlobalLerayHopfSolution.toSolution (g : GlobalLerayHopfSolution D C ν u₀)
    (T : ℝ) (hT : 0 < T) : Galerkin.LerayHopfSolution D C ν T u₀ :=
  LerayHopfSolution.ofIsOn (g.isOn T hT)

/-- **No-curve-duplication witness** (definitional): every horizon slice carries the
one global curve. -/
theorem GlobalLerayHopfSolution.toSolution_u (g : GlobalLerayHopfSolution D C ν u₀)
    (T : ℝ) (hT : 0 < T) : (g.toSolution T hT).u = g.u := rfl

/-- The global contract implies the existing per-horizon contract (with one uniform
curve) — the strengthening direction of the quantifier swap. -/
theorem GlobalLerayHopfSolution.nonempty_solution (g : GlobalLerayHopfSolution D C ν u₀)
    (T : ℝ) (hT : 0 < T) : Nonempty (Galerkin.LerayHopfSolution D C ν T u₀) :=
  ⟨g.toSolution T hT⟩

/-! ### Transfer lemmas: horizon restriction (`mono`) and curve congruence
(`congr_Icc`) -/

/-- **`WeakFormNS` restricts to smaller horizons** — with NO integrability hypothesis.
A `T'`-test is a `T`-test (`Ioo 0 T' ⊆ Ioo 0 T`), and the integrand carries a factor
`ψ t` or `deriv ψ t` in every term, so it vanishes identically on `(T', T]`;
`setIntegral_Ioc_eq_of_tail_zero` then transports the `T`-identity down to `T'`. -/
theorem weakFormNS_mono {E : DissipativeEvolution} {u : Time → E.H}
    (hT' : 0 < T') (hle : T' ≤ T) (h : WeakFormNS ν T E u) : WeakFormNS ν T' E u := by
  letI := E.instNACG
  letI := E.instIPS
  intro ψ hψc hψsupp hψC1 w hw
  have h0 := h ψ hψc (hψsupp.trans (Set.Ioo_subset_Ioo le_rfl hle)) hψC1 w hw
  have hzero : ∀ t : ℝ, T' < t → t ≤ T →
      (-(inner (𝕜 := ℝ) (u t) w) * deriv ψ t +
        ψ t * (ν * E.viscousForm (u t) w + E.convForm (u t) (u t) w)) = 0 := by
    intro t ht _
    have hnot : t ∉ tsupport ψ :=
      fun hmem => absurd (hψsupp hmem).2 (not_lt.mpr ht.le)
    rw [image_eq_zero_of_notMem_tsupport hnot, deriv_of_notMem_tsupport hnot]
    ring
  rw [intervalIntegral.integral_of_le hT'.le]
  rw [intervalIntegral.integral_of_le (hT'.le.trans hle)] at h0
  rw [← setIntegral_Ioc_eq_of_tail_zero hle hzero]
  exact h0

/-- **`WeakFormNS` depends on the curve only through `[0, T]` values**: the test
integrand is compared pointwise on `[[0, T]]` (`intervalIntegral.integral_congr`), so
curves agreeing on `Icc 0 T` satisfy the same weak identity. -/
theorem weakFormNS_congr_Icc {E : DissipativeEvolution} {u v : Time → E.H}
    (hT : 0 < T) (huv : ∀ t ∈ Set.Icc (0 : ℝ) T, u t = v t)
    (h : WeakFormNS ν T E u) : WeakFormNS ν T E v := by
  letI := E.instNACG
  letI := E.instIPS
  intro ψ hψc hψsupp hψC1 w hw
  have h0 := h ψ hψc hψsupp hψC1 w hw
  have hEq : Set.EqOn
      (fun t => (-(inner (𝕜 := ℝ) (v t) w) * deriv ψ t +
        ψ t * (ν * E.viscousForm (v t) w + E.convForm (v t) (v t) w)))
      (fun t => (-(inner (𝕜 := ℝ) (u t) w) * deriv ψ t +
        ψ t * (ν * E.viscousForm (u t) w + E.convForm (u t) (u t) w)))
      (Set.uIcc (0 : ℝ) T) := by
    intro t ht
    rw [Set.uIcc_of_le hT.le] at ht
    simp only [← huv t ht]
  rw [intervalIntegral.integral_congr hEq]
  exact h0

/-- **Horizon restriction for the full contract** (`IsLerayHopfOn.mono`): all five
conjuncts restrict from `[0, T]` to `[0, T'] ⊆ [0, T]`.  No integrability is ADDED
anywhere (codex focus question (iii)): the weak form restricts by
`weakFormNS_mono`, the dissipation integrability RESTRICTS (`mono_set`), it is never
assumed afresh. -/
theorem IsLerayHopfOn.mono {u : Time → ↥D.σ} (hT' : 0 < T') (hle : T' ≤ T)
    (h : IsLerayHopfOn D C ν T u₀ u) : IsLerayHopfOn D C ν T' u₀ u := by
  obtain ⟨hweak, henergy, htrace, ⟨hreg, hdiss⟩, haesm⟩ := h
  refine ⟨weakFormNS_mono hT' hle hweak,
    fun t ht0 htT' => henergy t ht0 (htT'.trans hle), htrace, ⟨?_, ?_⟩, ?_⟩
  · exact ae_restrict_of_ae_restrict_of_subset (Set.Icc_subset_Icc le_rfl hle) hreg
  · refine hdiss.mono_set (Set.uIcc_subset_uIcc Set.left_mem_uIcc ?_)
    rw [Set.uIcc_of_le (hT'.le.trans hle)]
    exact ⟨hT'.le, hle⟩
  · exact haesm.mono_measure
      (Measure.restrict_mono (Set.Icc_subset_Icc le_rfl hle) le_rfl)

/-- **Curve congruence on `[0, T]`** (`IsLerayHopfOn.congr_Icc`): the contract sees the
curve only through its values on `[0, T]` — POINTWISE equality there (which the
diagonal-coherence step provides; not merely a.e.) transfers all five conjuncts.
`hT : 0 < T` feeds the initial-trace transfer (equality on a right-neighborhood of
`0`). -/
theorem IsLerayHopfOn.congr_Icc {u v : Time → ↥D.σ} (hT : 0 < T)
    (huv : ∀ t ∈ Set.Icc (0 : ℝ) T, u t = v t)
    (h : IsLerayHopfOn D C ν T u₀ u) : IsLerayHopfOn D C ν T u₀ v := by
  obtain ⟨hweak, henergy, htrace, ⟨hreg, hdiss⟩, haesm⟩ := h
  -- a.e. version of the pointwise hypothesis, on the restricted measure
  have hae : ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)), u t = v t := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact huv t ht
  refine ⟨weakFormNS_congr_Icc hT huv hweak, ?_, ?_, ⟨?_, ?_⟩, ?_⟩
  · -- energy inequality: rewrite `v` back to `u` at `t` and under the integral
    intro t ht0 htT
    have hcurve : ((v t : D.X)) = ((u t : D.X)) :=
      congrArg Subtype.val (huv t ⟨ht0, htT⟩).symm
    have hint : ∫ s in (0 : ℝ)..t, D.dissip ν ↑(v s) = ∫ s in (0 : ℝ)..t, D.dissip ν ↑(u s) := by
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [Set.uIcc_of_le ht0] at hs
      exact congrArg (fun x : ↥D.σ => D.dissip ν ↑x)
        (huv s ⟨hs.1, hs.2.trans htT⟩).symm
    rw [hcurve, hint]
    exact henergy t ht0 htT
  · -- initial trace: `u` and `v` agree eventually in `𝓝[Ici 0] 0` (inside `[0, T)`)
    have hev : (fun t => (u t : D.X)) =ᶠ[nhdsWithin (0 : ℝ) (Set.Ici 0)]
        (fun t => (v t : D.X)) := by
      have h1 : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ici 0), t ∈ Set.Iio T :=
        (isOpen_Iio.eventually_mem hT).filter_mono nhdsWithin_le_nhds
      have h2 : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ici 0), t ∈ Set.Ici (0 : ℝ) :=
        self_mem_nhdsWithin
      filter_upwards [h1, h2] with t hlt hge
      exact congrArg Subtype.val (huv t ⟨hge, hlt.le⟩)
    exact htrace.congr' hev
  · -- a.e. regularity membership
    filter_upwards [hreg, hae] with t hregt heqt
    rw [show ((v t : D.X)) = ((u t : D.X)) from congrArg Subtype.val heqt.symm]
    exact hregt
  · -- dissipation integrability: transported by pointwise equality on `Ioc 0 T`
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le] at hdiss ⊢
    refine hdiss.congr_fun (fun s hs => ?_) measurableSet_Ioc
    exact congrArg (fun x : ↥D.σ => D.dissip ν ↑x) (huv s ⟨hs.1.le, hs.2⟩)
  · -- time-measurability
    refine haesm.congr ?_
    filter_upwards [hae] with t heqt
    exact congrArg Subtype.val heqt

end Scratch195
end LerayHopf

-- Axiom pins (recorded in docs/scratch/global-diagonal-campaign.md §10; expected:
-- [propext, Classical.choice, Quot.sound] — no sorryAx, no project axioms).
#print axioms LerayHopf.Scratch195.setIntegral_Ioc_eq_of_tail_zero
#print axioms LerayHopf.Scratch195.badTail_not_integrableOn
#print axioms LerayHopf.Scratch195.badTail_truncation
#print axioms LerayHopf.Scratch195.truncation_agrees_with_additivity
#print axioms LerayHopf.Scratch195.truncation_routes_agree
#print axioms LerayHopf.Scratch195.nonempty_lerayHopfSolution_iff_exists_isOn
#print axioms LerayHopf.Scratch195.globalLerayHopfSolution_nonempty_iff
#print axioms LerayHopf.Scratch195.GlobalLerayHopfSolution.toSolution_u
#print axioms LerayHopf.Scratch195.weakFormNS_mono
#print axioms LerayHopf.Scratch195.weakFormNS_congr_Icc
#print axioms LerayHopf.Scratch195.IsLerayHopfOn.mono
#print axioms LerayHopf.Scratch195.IsLerayHopfOn.congr_Icc
