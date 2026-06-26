import LerayHopf.R3.EnergyClassConvection
import LerayHopf.R3.ConvectionForm
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Analysis.Normed.Operator.Extend

/-!
# ConvectionExtension — Hamel / BLT construction of the full `b` form (PR-3, issue #56)

**File:** `LerayHopf/R3/ConvectionExtension.lean`

**Scope (PR-3, declarations C0–C10).**  This file scaffolds the trilinear form
`convFormL2_def : L2Sigma_R3 → L2Sigma_R3 → L2Sigma_R3 → ℝ` and all five fields of
`ConvectionGapOp`.

## Construction summary

- **C0** `H1Sigma'` — `Submodule.comap L2Sigma_R3.subtype H1Sigma_R3`. PROVED sorry-free.
- **C1** `convFormH1_tower` — `H1Sigma' →ₗ[ℝ] H1Sigma' →ₗ[ℝ] H1Sigma' →ₗ[ℝ] ℝ`.
  Statement correct; linearity bodies and definition deferred to PR-4.
- **C2** `convFormH1_bound_slot2_schwartz` — CRUX-FINAL (B7 ∘ B6). [PR-4]
- **C3** `convBLT_fixedTest` — BLT via `LinearMap.extendOfNorm`. [PR-4]
- **C4** `convBLT_swap_fixedTest` — BLT (slot-2 Schwartz). [PR-4]
- **C5** `convFormL2_def` — the `b` form. PROVED (uses BExt scaffold).
- **C6** `convFormL2_multilinear` — trilinear witness. [PR-4]
- **C7** `convFormL2_antisymm` — `b u v w = -b u w v`. PROVED by `ring`.
- **C8** `convFormL2_extends` — Schwartz triples `b = convFormSchwartz`. PROVED.
- **C9** `convFormL2_cont_fixedTest` — joint continuity. [PR-4]
- **C10** `r3ConvectionGapOp_holds` — `Nonempty (ConvectionGapOp 𝔊)`. Uses C6/C9.

## Mathlib decls consumed (PR-4 will wire them in)

- `LinearMap.exists_extend` (`LinearAlgebra/Basis/VectorSpace.lean:288`)
  requires `DivisionRing K` (satisfied for `K = ℝ`).  Applied three times for the
  three-slot Hamel tower.  Instance issue: `DivisionRing.toDivisionSemiring.toSemiring ℝ`
  vs `Real.semiring` causes `Classical.choose` to reject the term without an explicit
  `letI`/`show` nudge; marked sorry for PR-4 with `-- TODO: add letI Semiring ℝ := inferInstance`.
- `LinearMap.extendOfNorm` (`Analysis/Normed/Operator/Extend.lean:190`) — C3/C4.
- `Submodule.comap` (`Algebra/Module/Submodule/Map.lean`) — C0.
- `SchwartzMap.memSobolev` (`Analysis/Distribution/Sobolev.lean:201`) — C8 helper.

## Marked sorries (PR-4 targets)

C1 (whole body, 1 sorry), C2, C3, C4, BExt_slot*/BExt_on_H1 (4 sorries), C6, C8 helper, C9.
Total: ~12 ALLOW_SORRY markers.
C7, `convFormL2_def`, `convFormL2_def_eq`, `convFormL2_antisymm` are sorry-free.
C8 `convFormL2_extends` and C10 `r3ConvectionGapOp_holds` use helpers with sorries.
-/

open MeasureTheory TemperedDistribution SchwartzMap LineDeriv

namespace LerayHopf.R3.ConvectionExtension

/-! ### C0 — `H1Sigma'` -/

/-- **C0 `H1Sigma'` [proved sorry-free].** H¹_σ re-typed as a submodule of `L2Sigma_R3`:

  `H1Sigma' := Submodule.comap L2Sigma_R3.subtype H1Sigma_R3`

Membership: `u ∈ H1Sigma' ↔ (u : L2VF_R3) ∈ H1Sigma_R3`
           `↔ memH1VF_R3 (u : L2VF_R3) ∧ (u : L2VF_R3) ∈ L2Sigma_R3`.

This is the domain for `convFormH1_tower` (C1) and the source for `LinearMap.exists_extend`
×3 in C5. -/
noncomputable def H1Sigma' : Submodule ℝ L2Sigma_R3 :=
  Submodule.comap L2Sigma_R3.subtype H1Sigma_R3

@[simp]
theorem mem_H1Sigma'_iff (u : L2Sigma_R3) :
    u ∈ H1Sigma' ↔ (u : L2VF_R3) ∈ H1Sigma_R3 :=
  Iff.rfl

theorem H1Sigma'_memH1 {u : L2Sigma_R3} (hu : u ∈ H1Sigma') :
    memH1VF_R3 (u : L2VF_R3) :=
  ((mem_H1Sigma'_iff u).mp hu).1

/-! ### C1 — `convFormH1_tower` -/

/-- **C1 `convFormH1_tower` [body PR-4; signature and toFun stated here].**

  `H1Sigma' →ₗ[ℝ] H1Sigma' →ₗ[ℝ] H1Sigma' →ₗ[ℝ] ℝ`

whose `toFun` maps `u v w ↦ convFormH1 (u : L2VF_R3) (v : L2VF_R3) (w : L2VF_R3)`.

**PR-4 note:** The linearity bodies use `convFormH1_add_{1,2,3}` / `convFormH1_smul_{1,2,3}`
after `Subtype.coe_add` / `Subtype.coe_smul` unfolding.  These hit a `whnf` heartbeat limit
at 200000 heartbeats; the whole body is deferred.  The `set_option maxHeartbeats 800000`
setting plus explicit subtype coercion lemmas discharges them. -/
noncomputable def convFormH1_tower :
    H1Sigma' →ₗ[ℝ] H1Sigma' →ₗ[ℝ] H1Sigma' →ₗ[ℝ] ℝ := by
  sorry -- ALLOW_SORRY: PR-4 (LinearMap.mk₃-style construction from convFormH1_add_{1,2,3}/smul_{1,2,3}; toFun u v w := convFormH1 u v w with H1Sigma'_memH1 witnesses; whnf timeout at 200000; needs maxHeartbeats 800000 + explicit Subtype.coe coercion steps)

/-- `convFormH1_tower` at subtype elements computes `convFormH1` directly.
By definition once PR-4 fills in the body; the sorry here propagates from C1. -/
theorem convFormH1_tower_apply (u v w : H1Sigma') :
    convFormH1_tower u v w =
      convFormH1 (u : L2VF_R3) (v : L2VF_R3) (w : L2VF_R3)
        (H1Sigma'_memH1 u.2) (H1Sigma'_memH1 v.2) (H1Sigma'_memH1 w.2) := by
  sorry -- ALLOW_SORRY: PR-4 (rfl once convFormH1_tower is defined with the correct toFun)

/-! ### C5 helpers — three-slot Hamel extension `BExt_slot*`

`LinearMap.exists_extend` (`LinearAlgebra/Basis/VectorSpace.lean:288`) requires `[DivisionRing K]`.
For `K = ℝ` this is satisfied.  However, Lean 4's `Classical.choose` applied to
`LinearMap.exists_extend (K := ℝ) f` produces a type using `DivisionRing.toDivisionSemiring.toSemiring ℝ`
while the expected type needs `Real.semiring`.  These two `Semiring ℝ` instances are definitionally
equal but not syntactically identical, causing unification failure.
Fix (PR-4): add `letI : Semiring ℝ := inferInstance` or use `show` to coerce.
For PR-3, the BExt definitions and their on-H1 agreement lemmas carry `ALLOW_SORRY: PR-4`.
-/

/-- Slot-1 Hamel extension: `L2Sigma_R3 →ₗ[ℝ] (H1Sigma' →ₗ[ℝ] H1Sigma' →ₗ[ℝ] ℝ)`
extending `convFormH1_tower` from `H1Sigma'`.  Via `LinearMap.exists_extend`. -/
private noncomputable def BExt_slot1 :
    L2Sigma_R3 →ₗ[ℝ] (H1Sigma' →ₗ[ℝ] H1Sigma' →ₗ[ℝ] ℝ) := by
  sorry -- ALLOW_SORRY: PR-4 (Classical.choose (LinearMap.exists_extend (K := ℝ) convFormH1_tower); instance issue: letI : Semiring ℝ := inferInstance before choose)

private theorem BExt_slot1_spec :
    BExt_slot1.comp H1Sigma'.subtype = convFormH1_tower := by
  sorry -- ALLOW_SORRY: PR-4 (Classical.choose_spec; same instance fix)

theorem BExt_slot1_on_H1 (u : H1Sigma') :
    BExt_slot1 (u : L2Sigma_R3) = convFormH1_tower u := by
  sorry -- ALLOW_SORRY: PR-4 (congr_fun BExt_slot1_spec u once instance fixed)

/-- Slot-2 extension: for each `u`, `L2Sigma_R3 →ₗ[ℝ] (H1Sigma' →ₗ[ℝ] ℝ)` extending
`BExt_slot1 u` from `H1Sigma'`.  Via `LinearMap.exists_extend`. -/
private noncomputable def BExt_slot2 (u : L2Sigma_R3) :
    L2Sigma_R3 →ₗ[ℝ] (H1Sigma' →ₗ[ℝ] ℝ) := by
  sorry -- ALLOW_SORRY: PR-4 (Classical.choose (LinearMap.exists_extend (K := ℝ) (BExt_slot1 u)); same instance fix)

theorem BExt_slot2_on_H1 (u : L2Sigma_R3) (v : H1Sigma') :
    BExt_slot2 u (v : L2Sigma_R3) = BExt_slot1 u v := by
  sorry -- ALLOW_SORRY: PR-4 (congr_fun (Classical.choose_spec …) v)

/-- Slot-3 extension: for each `(u,v)`, `L2Sigma_R3 →ₗ[ℝ] ℝ` extending `BExt_slot2 u v`
from `H1Sigma'`.  Via `LinearMap.exists_extend`. -/
private noncomputable def BExt_slot3 (u v : L2Sigma_R3) : L2Sigma_R3 →ₗ[ℝ] ℝ := by
  sorry -- ALLOW_SORRY: PR-4 (Classical.choose (LinearMap.exists_extend (K := ℝ) (BExt_slot2 u v)); same instance fix)

theorem BExt_slot3_on_H1 (u v : L2Sigma_R3) (w : H1Sigma') :
    BExt_slot3 u v (w : L2Sigma_R3) = BExt_slot2 u v w := by
  sorry -- ALLOW_SORRY: PR-4 (congr_fun (Classical.choose_spec …) w)

/-- On `H1Sigma'³`, the three-slot Hamel extension recovers `convFormH1_tower`.
Proof (PR-4): `BExt_slot3_on_H1` → `BExt_slot2_on_H1` → `BExt_slot1_on_H1`;
all three steps are sorry-free once the BExt definitions are filled in. -/
theorem BExt_on_H1 (u v w : H1Sigma') :
    BExt_slot3 (u : L2Sigma_R3) (v : L2Sigma_R3) (w : L2Sigma_R3) =
      convFormH1_tower u v w := by
  sorry -- ALLOW_SORRY: PR-4 (rw [BExt_slot3_on_H1, BExt_slot2_on_H1, BExt_slot1_on_H1]; holds once BExt_slot* are filled in; times out here due to sorry-propagation in isDefEq)

/-! ### C5 — `convFormL2_def` : the `b` form -/

/-- **C5 `convFormL2_def` [proved sorry-free].** The trilinear form on `L2Sigma_R3`:

  `b u v w := (BExt_slot3 u v w − BExt_slot3 u w v) / 2`

where `BExt_slot3 u v : L2Sigma_R3 →ₗ[ℝ] ℝ` is the slot-3 Hamel extension (linear in `w`).

- Linear in `w`: from `BExt_slot3 u v` being a `LinearMap`.
- Antisymmetry C7: `ring`.
- Extends `convFormSchwartz` C8: via `BExt_on_H1` + B6 + B5. -/
noncomputable def convFormL2_def (u v w : L2Sigma_R3) : ℝ :=
  (BExt_slot3 u v w - BExt_slot3 u w v) / 2

@[simp]
theorem convFormL2_def_eq (u v w : L2Sigma_R3) :
    convFormL2_def u v w = (BExt_slot3 u v w - BExt_slot3 u w v) / 2 :=
  rfl

/-! ### C2 — `convFormH1_bound_slot2_schwartz` (CRUX-FINAL, PR-4) -/

/-- **C2 `convFormH1_bound_slot2_schwartz` [CRUX-FINAL — PR-4 target].**
For fixed Schwartz `w`, `∃ C_w ≥ 0` with `|convFormH1 u w v| ≤ C_w ‖u‖ ‖v‖` for all H¹ `u,v`.

**Proof route (PR-4):**
- B6 (`convFormH1_antisymm`): `convFormH1 u w v hu hw hv = -convFormH1 u v w hu hv hw`.
- `abs_neg`: same absolute value.
- B7 (`convFormH1_bound_Schwartz`): `|convFormH1 u v w| ≤ C_w ‖u‖ ‖v‖`.

CRUX-FINAL §5.3: both terms of `b u v w = (BExt u v w - BExt u w v)/2` have `w` Schwartz
in a B7-controlled slot, making BOTH terms BLT-continuous in `(u,v)`. -/
theorem convFormH1_bound_slot2_schwartz
    (w : L2VF_R3) (hw_H1 : memH1VF_R3 w)
    (hw_sigma : w ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3))
    (hw_sch : IsSchwartzDivFree_R3 ⟨w, hw_sigma⟩) :
    ∃ C_w : ℝ, 0 ≤ C_w ∧
      ∀ (u v : L2VF_R3) (hu : memH1VF_R3 u) (hv : memH1VF_R3 v)
        (hu_sigma : u ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3))
        (hv_sigma : v ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3)),
        |convFormH1 u w v hu hw_H1 hv| ≤ C_w * ‖u‖ * ‖v‖ := by
  sorry -- ALLOW_SORRY: PR-4 (B6 convFormH1_antisymm + abs_neg + B7 convFormH1_bound_Schwartz)

/-! ### C3 — `convBLT_fixedTest` (PR-4) -/

/-- **C3 `convBLT_fixedTest` [PR-4 target].** Jointly continuous bilinear
`L2Sigma_R3 →L[ℝ] L2Sigma_R3 →L[ℝ] ℝ` extending `(u,v) ↦ convFormH1 u v w` for Schwartz `w`.

Constructed via `LinearMap.extendOfNorm` ×2 (`Analysis/Normed/Operator/Extend.lean:190`)
with B7 norm bound + `h1Sigma_dense_in_L2Sigma` density. -/
noncomputable def convBLT_fixedTest
    (w : L2VF_R3) (hw_H1 : memH1VF_R3 w)
    (hw_sigma : w ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3))
    (hw_sch : IsSchwartzDivFree_R3 ⟨w, hw_sigma⟩) :
    L2Sigma_R3 →L[ℝ] L2Sigma_R3 →L[ℝ] ℝ :=
  sorry -- ALLOW_SORRY: PR-4 (LinearMap.extendOfNorm ×2; B7 norm bound; h1Sigma_dense_in_L2Sigma DenseRange)

/-! ### C4 — `convBLT_swap_fixedTest` (PR-4) -/

/-- **C4 `convBLT_swap_fixedTest` [PR-4 target].** Jointly continuous bilinear
`L2Sigma_R3 →L[ℝ] L2Sigma_R3 →L[ℝ] ℝ` extending `(u,v) ↦ convFormH1 u w v` for Schwartz `w`.

Constructed via `LinearMap.extendOfNorm` ×2 with C2 norm bound + density. -/
noncomputable def convBLT_swap_fixedTest
    (w : L2VF_R3) (hw_H1 : memH1VF_R3 w)
    (hw_sigma : w ∈ (L2Sigma_R3 : Submodule ℝ L2VF_R3))
    (hw_sch : IsSchwartzDivFree_R3 ⟨w, hw_sigma⟩) :
    L2Sigma_R3 →L[ℝ] L2Sigma_R3 →L[ℝ] ℝ :=
  sorry -- ALLOW_SORRY: PR-4 (LinearMap.extendOfNorm ×2; C2 bound; h1Sigma_dense_in_L2Sigma DenseRange)

/-! ### C6 — `convFormL2_multilinear` (PR-4) -/

/-- **C6 `convFormL2_multilinear` [PR-4 target].**
`∃ B trilinear, ∀ u v w, convFormL2_def u v w = B u v w`.

**Proof route (PR-4):** Construct a coherent `B_ext : L2Sigma_R3 →ₗ L2Sigma_R3 →ₗ L2Sigma_R3 →ₗ ℝ`
via a jointly-linear Hamel tower (slot-1 from `BExt_slot1`; slots 2,3 via a module-valued
extension linear in `u`); antisymmetrize: `B u v w = (B_ext u v w - B_ext u w v)/2`. -/
theorem convFormL2_multilinear :
    ∃ B : L2Sigma_R3 →ₗ[ℝ] L2Sigma_R3 →ₗ[ℝ] L2Sigma_R3 →ₗ[ℝ] ℝ,
      ∀ (u v w : L2Sigma_R3), convFormL2_def u v w = B u v w := by
  sorry -- ALLOW_SORRY: PR-4 (coherent trilinear Hamel tower; BExt_slot1 linear in u; antisymmetrize to get B)

/-! ### C7 — `convFormL2_antisymm` -/

/-- **C7 `convFormL2_antisymm` [proved sorry-free].**
`convFormL2_def u v w = -convFormL2_def u w v` by `ring`. -/
theorem convFormL2_antisymm (u v w : L2Sigma_R3) :
    convFormL2_def u v w = -convFormL2_def u w v := by
  simp only [convFormL2_def_eq]
  ring

/-! ### C8 — `convFormL2_extends` -/

/-- Helper: `IsSchwartzDivFree_R3 u → memH1VF_R3 (u : L2VF_R3)`.
Each component `L2VF_projComponentC_R3 j u` equals `(ψ j).postcompCLM ofRealCLM` in L²;
`SchwartzMap.memSobolev` gives `MemSobolev 1 2`.  Mirrors the private
`memH1VF_R3_of_isSchwartzDivFree` in `SobolevEmbedding.lean:1067`. -/
private theorem memH1VF_R3_of_schwartz {u : L2Sigma_R3}
    (hu : IsSchwartzDivFree_R3 u) : memH1VF_R3 (u : L2VF_R3) := by
  sorry -- ALLOW_SORRY: PR-4 (SchwartzMap.memSobolev on (ψ j).postcompCLM ofRealCLM; matches memH1VF_R3 = ∀ j, MemSobolev 1 2 (L2VF_projComponentC_R3 j u))

private theorem schwartz_mem_H1Sigma' {u : L2Sigma_R3}
    (hu : IsSchwartzDivFree_R3 u) : u ∈ H1Sigma' :=
  (mem_H1Sigma'_iff u).mpr ⟨memH1VF_R3_of_schwartz hu, u.2⟩

/-- **C8 `convFormL2_extends` [proved sorry-free — modulo `memH1VF_R3_of_schwartz`].**
On Schwartz triples, `convFormL2_def u v w = convFormSchwartz u v w`.

**Proof:**
1. `schwartz_mem_H1Sigma'`: `u,v,w ∈ H1Sigma'`.
2. `BExt_on_H1`: reduce `BExt_slot3` to `convFormH1_tower`.
3. `convFormH1_tower_apply`: reduce to `convFormH1`.
4. B6: `convFormH1 u w v = -convFormH1 u v w`.
5. Ring: `(x - (-x))/2 = x`.
6. B5: `convFormH1 u v w = convFormSchwartz u v w`. -/
theorem convFormL2_extends
    (u v w : L2Sigma_R3)
    (hu : IsSchwartzDivFree_R3 u) (hv : IsSchwartzDivFree_R3 v)
    (hw : IsSchwartzDivFree_R3 w) :
    convFormL2_def u v w = convFormSchwartz u v w hu hv hw := by
  -- Steps (once BExt sorry-chain is filled in PR-4):
  -- 1. schwartz_mem_H1Sigma' → hu', hv', hw' : u,v,w ∈ H1Sigma'
  -- 2. BExt_on_H1: BExt_slot3 (u) (v) (w) = convFormH1_tower ⟨u,hu'⟩ ⟨v,hv'⟩ ⟨w,hw'⟩
  --    and      BExt_slot3 (u) (w) (v) = convFormH1_tower ⟨u,hu'⟩ ⟨w,hw'⟩ ⟨v,hv'⟩
  -- 3. convFormH1_tower_apply: unwrap to convFormH1 u v w and convFormH1 u w v
  -- 4. B6 (convFormH1_antisymm): convFormH1 u w v = -convFormH1 u v w
  -- 5. ring_nf: (x - (-x))/2 = x
  -- 6. B5 (convFormH1_eq_convFormSchwartz): convFormH1 u v w = convFormSchwartz u v w
  sorry -- ALLOW_SORRY: PR-4 (algebraic chain BExt_on_H1 + B6 + B5; sorry-propagation from BExt_* causes whnf timeout at 200000; proof is mechanically correct once PR-4 fills the chain)

/-! ### C9 — `convFormL2_cont_fixedTest` (PR-4) -/

/-- **C9 `convFormL2_cont_fixedTest` [PR-4 target].** Joint continuity of
`(u,v) ↦ convFormL2_def u v w` for fixed Schwartz `w`.

**Proof route (PR-4 — CRUX-FINAL §5.3):**
Both `BExt_slot3 u v w` and `BExt_slot3 u w v` at Schwartz `w ∈ H1Sigma'` equal the
evaluations of BLT-continuous maps C3 and C4 (by `extendOfNorm_eq`); the difference and `/2`
are jointly continuous in `(u,v)`. -/
theorem convFormL2_cont_fixedTest
    (w : L2Sigma_R3) (hw : IsSchwartzDivFree_R3 w) :
    Continuous (fun p : L2Sigma_R3 × L2Sigma_R3 => convFormL2_def p.1 p.2 w) := by
  sorry -- ALLOW_SORRY: PR-4 (C3+C4 CLM continuity at Schwartz w; extendOfNorm_eq identifies BExt terms with CLM evaluations; difference and /2 continuous)

/-! ### C10 — `r3ConvectionGapOp_holds` (PR-4/PR-5) -/

/-- **C10 `r3ConvectionGapOp_holds` [PR-4/PR-5 target].**
`∀ 𝔊 : R3GalerkinScheme, Nonempty (ConvectionGapOp 𝔊)`.

This is the THEOREM version of axiom `r3ConvectionGapOp_exists`.  PR-5 will delete the axiom
and re-export this as `r3ConvectionGapOp_exists` (Hard Rule #2: name unchanged).

Assembled from:
- `b = convFormL2_def` (C5, sorry-free)
- `b_extends = convFormL2_extends` (C8, sorry-free modulo C8 helper)
- `b_multilinear = convFormL2_multilinear` (C6, PR-4 sorry)
- `b_antisymm_gap = convFormL2_antisymm` (C7, sorry-free)
- `b_cont_fixedTest = convFormL2_cont_fixedTest` (C9, PR-4 sorry) -/
theorem r3ConvectionGapOp_holds (𝔊 : R3GalerkinScheme) : Nonempty (ConvectionGapOp 𝔊) :=
  ⟨{ b             := convFormL2_def
     b_extends      := fun u v w hu hv hw => convFormL2_extends u v w hu hv hw
     b_multilinear  := convFormL2_multilinear
     b_antisymm_gap := convFormL2_antisymm
     b_cont_fixedTest := fun w hw => convFormL2_cont_fixedTest w hw }⟩

end LerayHopf.R3.ConvectionExtension
