# PR-0 verdict — torus #53 Route F go/no-go

**Spike file:** `LerayHopf/Scratch/TorusRouteFSpike.lean` (scaffold-only, not for merge).
**Build:** `flock /tmp/lean-build.lock lake build LerayHopf.Scratch.TorusRouteFSpike` → **green**
(`Build completed successfully (2919 jobs)`), 3 marked `sorry` on the analytic substeps of the
three claims; everything else sorry-free.

## Verdict: **GO** (Route F is sound), with two design refinements that MUST be carried into PR-2.

Route F is mathematically sound and the build infrastructure is in place (the torus H¹ predicates
`memH1VF` / `memH1Sigma` / `h1EnergySq` already exist in `LerayHopf/H1Sigma.lean` — the plan's
"no torus H¹_σ at all" is partly outdated; only the *submodule packaging* is missing, which is light).
But the spike surfaced two structural facts the plan stated too loosely. Neither is a blocker; both
change HOW PR-2 must be written, and both are exactly the kind of thing codex will flag if PR-2
ignores them.

---

## Claim 1 — summability / well-definedness locus

**Finding: the form is summable iff the GRADIENT (middle / `v`) slot is H¹ — NOT for three L² args.**

The summand is `û_a(k)·(2πi lₐ)·v̂_i(l)·ŵ_i(-(k+l))`. The `lₐ` weight on the `v`-coefficient is the
`∂_a v` Fourier multiplier. Writing `α(k)=|û_a(k)|`, `β(l)=‖l‖|v̂_i(l)|`, `γ(m)=|ŵ_i(m)|`, the double
sum is the convolution-diagonal `∑_m γ(m)·(α ∗ β̃)(m)`. Cauchy–Schwarz over `m` bounds it by
`‖γ‖₂·‖α∗β̃‖₂`, and Young needs `‖α∗β̃‖₂ ≤ ‖α‖₁‖β‖₂` (or `‖α‖₂‖β‖₁`) — i.e. ONE of `α,β` in **ℓ¹**.
For three arbitrary L² arguments all of `α,β,γ` are only **ℓ²**, so there is **no hypothesis-free
summability**: the `tsum` is generically divergent and the form is the mathlib `tsum`-junk value `0`
off the summable locus.

**Exact well-definedness hypotheses (the summable locus):**
- `b` is TOTAL on `L2VF³` by the `tsum`-off-summable convention (value `0` where not summable) — sound.
- `b` AGREES with the genuine convection value exactly on the **H¹-gradient locus**: `v ∈ H¹`
  (so `β = ‖l‖|v̂(l)| ∈ ℓ²`) together with either `w` a Galerkin test (finite support ⟹ `γ` finitely
  supported ⟹ `γ ∈ ℓ¹`, the anti-diagonal collapse) or `u ∈ H¹`. The spike states this as
  `convSummand_summable_of_h1_test` (hyps `memH1VF v`, `IsGalerkinTestVF w`) — typechecks; assembly
  `sorry`-ed (anti-diagonal collapse + per-diagonal ℓ²·ℓ² Cauchy–Schwarz, mechanical).

**Refinement for PR-2:** `gradPairingSummable` in the plan (PR-1) must be stated with `v ∈ H¹`, not
"`u,v ∈ H¹, w ∈ L²`" symmetrically — the derivative is on the MIDDLE slot, so it is the **middle**
argument that must be H¹ for the raw form. (After antisymmetry the roles swap; see Claim 3.)

---

## Claim 2 — antisymmetry over arbitrary L²_σ

**Finding: genuinely IBP-free AND the reindex is a valid full-lattice bijection — but it is NOT a
single unconditional `tsum` reindex; it needs a case split.**

- *Reindex validity (the lynchpin) — CONFIRMED sorry-free.* The involution `σ_k : l ↦ -(k+l)` is a
  genuine `Equiv (Fin 3 → ℤ) (Fin 3 → ℤ)` of the **full** lattice (`latticeInvol`,
  `latticeInvol_involutive` — both compiled with no `sorry`). Unlike `fourierBox`, the full lattice
  IS invariant, so `Equiv.tsum_eq (latticeInvol k)` applies. No double-counting. This is the payoff
  of the compact domain: antisymmetry reduces to relabelling the lattice + the divergence-free
  identity `∑_a kₐ ûₐ(k)=0` (already used in `galerkinConvection_antisymm`). **No Leibniz, no IBP,
  no `h1Leibniz2`.** This is the genuine Route-F advantage over R3's from-scratch weak Leibniz.

- *BLOCKER STRUCTURE (must be handled, not a failure).* `Equiv.tsum_eq` rewrites a `tsum` regardless
  of summability, BUT to combine the two reindexed sums into one and apply the div-free cancellation
  you need them summable (otherwise you are manipulating `tsum`-junk and the cancellation step
  `A + A' = 0` is not valid termwise). Per Claim 1, summability fails for arbitrary L² `v`. So
  `convFormFourier_antisymm` over **arbitrary** `L²_σ` (the `b_antisymm_gap` field has NO H¹
  hypothesis) must be proved by a **case split**:
  - **H¹ locus** (`v,w ∈ H¹`): summable ⟹ reindex + div-free identity close it (the real content).
  - **off-locus:** both `b u v w` and `b u w v` are the `tsum`-junk `0` ⟹ `0 = -0`.

  This is SOUND but the off-locus branch is real proof obligation, because `b_antisymm_gap` quantifies
  over ALL `u v w : L2Sigma`. The spike states `convFormFourier_antisymm (u : L2Sigma) (v w : L2VF)`
  and `sorry`s the case split. **Codex watch-point:** do not claim antisymmetry "is just a tsum
  reindex" — it is reindex-on-the-locus + both-zero-off-it.

---

## Claim 3 — `b_bound_test` and the quantifier order `∃ C, ∀ u v`

**Finding: the `∃C, ∀u,v` order IS achievable — but ONLY through antisymmetry, which moves the
derivative onto the FIXED test `w`.** This is the single most important design fact and mirrors the
R3 lane's hard-won correction (R3 `ConvectionGap` round-3: the form is unbounded in pure L²×L²×L²;
the derivative must sit on the smooth fixed slot).

- The raw middle-slot form has its `(2πi lₐ)` weight on `v`. A bound in that shape would carry
  `‖∇v‖`, which is **unbounded** over Galerkin-test `v` as the support level grows — so `∃C(w),∀v`
  is **impossible** for the raw form (the over-strength trap codex caught on R3).
- Antisymmetry (`b u v w = - b u w v`, Claim 2) puts the weight onto `w`'s coefficients. Since the
  fixed test `w` is a trig polynomial, `‖l‖·|ŵ_i(l)|` is supported on a finite box and uniformly
  bounded by `2πN·(‖proj‖·‖w‖)`-type data depending ONLY on `w`. Then `|b u v w| ≤ C(w)·‖u‖·‖v‖`
  with `C(w)` n-independent and uniform in `(u,v)` — for **arbitrary** `u,v : L2VF` (the spike states
  exactly this stronger form, `convFormFourier_bound_test`, ∀ u v with no test hypothesis; typechecks).

- **Consequence for `b_cont_fixedTest`.** Because Claim 3 gives the bound for ARBITRARY `(u,v)` (not
  only Galerkin tests), `(u,v) ↦ b u v w` is a bounded — hence continuous — bilinear form at fixed
  Galerkin test `w`. So `b_cont_fixedTest` follows DIRECTLY from the (antisymmetry-derived) fixed-test
  bound via `LinearMap.mkContinuous₂` / `isBoundedBilinearMap`, **without** the R3 determined-edge /
  double-BLT tower. ⇒ **PR-3 (determined-form gluing) is very likely UNNECESSARY** — the torus form
  is total + bounded at fixed test, not a Hamel object. This collapses the build toward ~5 PRs.

- The real structure's `b_bound_test` (TorusConvectionForm.lean:549) is even weaker than Claim 3 (it
  restricts `u,v` to Galerkin tests), so it is trivially satisfied by the arbitrary-`(u,v)` bound.

---

## Net design deltas to carry into the build (vs the plan)

1. **Derivative placement.** State the H¹ requirement on the **middle** slot for the raw form; the
   fixed-test bound and `b_cont_fixedTest` come from antisymmetry moving the weight onto `w`. PR-2
   MUST prove antisymmetry BEFORE the bound (the bound depends on it). Reorder the PR-2 lemmas:
   `convFormFourier_antisymm` is a prerequisite of `convFormFourier_bound_test`, not independent.

2. **Antisymmetry is a case split, not a bare reindex.** `b_antisymm_gap` over arbitrary `L²_σ` =
   (H¹-locus reindex + div-free identity) ∪ (off-locus both-zero). Budget for the off-locus branch.

3. **PR-3 likely droppable.** With the arbitrary-`(u,v)` fixed-test bound, continuity is direct;
   skip the determined-edge construction unless the bound proof unexpectedly needs only Galerkin-test
   `(u,v)` (it should not — the ℓ²·ℓ² Cauchy–Schwarz in `(u,v)` is hypothesis-free once the weight is
   on `w`).

4. **H¹ infra is lighter than the plan thought.** `memH1VF`/`memH1Sigma`/`h1EnergySq` already exist
   in `H1Sigma.lean`. PR-1 only needs the submodule packaging + the `gradPairingSummable` (Claim 1a)
   and `galerkinTestSpan ⊆ H¹` facts.

## Which claims compiled vs hit a wall

| Claim | Lean object | Status |
|---|---|---|
| Reindex validity (Claim 2 core) | `latticeInvol`, `latticeInvol_involutive` | **compiled sorry-free** — full-lattice `Equiv` confirmed |
| Total form well-defined | `convFormFourier`, `convSummand` | **compiled sorry-free** (defs typecheck) |
| Claim 1a summable locus | `convSummand_summable_of_h1_test` | signature typechecks; `sorry` on anti-diagonal + Cauchy–Schwarz (mechanical) |
| Claim 2b antisymmetry | `convFormFourier_antisymm` | signature typechecks; `sorry` on case split (validated design) |
| Claim 3 fixed-test bound | `convFormFourier_bound_test` | signature typechecks (∀ u v form); `sorry` on antisymmetry-then-CS (validated design) |

No genuine wall. The three `sorry`s are mechanical/assembly, not missing mathlib. The soundness-
critical *structural* facts (full-lattice reindex bijection; the H¹-on-middle-slot summability locus;
the antisymmetry-moves-derivative-to-`w` bound order) are all confirmed.
