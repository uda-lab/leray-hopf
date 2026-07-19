# Statement card — `LerayHopf.Bochner.w1pTime_continuous_in_H`

See `docs/statement-gates.md` for the field template and process this card implements.

- **Location:** `LerayHopf/Bochner/TimeSobolevExperimental.lean:71` (namespace `LerayHopf.Bochner`).
- **Status:** `sorry`, `ALLOW_SORRY` — declared MONTHS-CLASS residual. Outside both capstone
  cones and outside the release import cone (`LerayHopf.Experimental` opt-in only).
- **History:** introduced (as a generic-exponent form) in scaffold commit `95571d3`; extracted
  from `TimeSobolev.lean` into this file by issue #147; signature corrected to `p = q = 2` by
  issue #158 after a false-statement postmortem — see
  `docs/postmortems/2026-07-w1ptime-false-statement.md`.

## Exact type

```
theorem w1pTime_continuous_in_H (GT : GelfandTriple) {T : ℝ} (hT : 0 < T)
    {uV : ℝ → GT.V} (W : W1pTime GT 2 2 T uV) :
    ∃ ũ : ℝ → GT.H, ContinuousOn ũ (Set.Icc 0 T) ∧
      ũ =ᵐ[volume.restrict (Set.Icc 0 T)] (fun t => GT.ι (uV t))
```

(`letI` instance lines eliding the `V`/`H` norm/inner-product structure omitted above; see the
source for the exact elaborated form.)

## Literature reference

Lions–Magenes good-representative embedding, `{u ∈ L²(0,T;V) : u' ∈ L²(0,T;V')} ↪ C([0,T];H)`, for a
Gelfand (evolution) triple `V ↪ H ↪ V'`. Standard reference: J.-L. Lions & E. Magenes,
*Non-Homogeneous Boundary Value Problems and Applications, Vol. I* (Springer, 1972), and
R. Temam, *On the Theory and Numerical Analysis of the Navier–Stokes Equations*, Université
Paris XI, No. 64, 1973, Chapter III, Lemma 1.2, p. 205.

Lemma III.1.2's conclusion is **strictly stronger** than this declaration: it gives both the
continuous `H`-valued representative and the distributional energy identity (1.68) for that
representative. `w1pTime_continuous_in_H` must not be identified with Lemma III.1.2 — the Lean
declaration claims only the continuous-representative part; the energy identity (1.68) is not
formalized here, and no explicit initial-value estimate appears in the lemma's displayed claim.

**No exact literature pin had been recorded for the former generic `p, q` form** — this is
exactly the gap issue #158 identifies as antipattern #1 (named-theorem anchoring): the repo had
cited "Lions–Magenes" by name without checking the source against the exact exponent hypotheses
the cited theorem needs. The corrected `p = q = 2` case is pinned here to Temam's
Chapter III, Lemma 1.2, p. 205 (1973). A generic-`p,q` reintroduction MUST NOT ship without first
pinning an exact edition/theorem-number citation for that generality (see "Required before
widening" below).

## Hypothesis mapping

| Lean hypothesis | Role |
|---|---|
| `GT : GelfandTriple` | supplies `V`, `H`, `V'`, the embedding `ι : V →L[ℝ] H`, and the induced `hToVprime : H →L[ℝ] V'` making `V ↪ H ↪ V'` a genuine evolution triple. |
| `hT : 0 < T` | not needed for `Set.Icc 0 T` nonemptiness (that holds for any `T ≥ 0`); it gives the open interval `Set.Ioo 0 T` positive length, which the weak-time-derivative apparatus (test functions with `tsupport ψ ⊆ Set.Ioo 0 T`, du Bois-Reymond bump construction) requires. |
| `uV : ℝ → GT.V` | the `V`-valued curve whose `H`-representative is sought. |
| `W : W1pTime GT 2 2 T uV` | packages `uV ∈ L²(0,T;V)` **and** its weak time derivative `u' ∈ L²(0,T;V')`, at the fixed exponent pair `2, 2`. |

The `2, 2` exponent pin is load-bearing: it is what makes the dual-pairing integrand
`t ↦ ⟨u'(t), u(t)⟩_{V',V}` integrable via Cauchy–Schwarz on `L²(V') × L²(V)`, which the proof
route needs. **No other exponent pair is asserted by this declaration.**

## Consumer / special case

**No live consumer.** Nothing in the codebase calls this declaration (confirmed at issue #147's
extraction: `LerayHopf/Torus/TraceEnergy.lean` documents it as quarantined; the two root-closure
importers of `TimeSobolev.lean` use only the unrelated `kineticEnergy_lsc_transfer`). The only
analysis ever done of a proof route (issue #4's Lions–Magenes spike,
`docs/scratch/spike1-lions-magenes-verdict.md`) is for exactly `p = q = 2`, which is why this is
the stated case — special-case-proof ⇒ special-case-API (issue #158 process rule).

## Boundary-case checklist (issue #158 process requirement)

- **Weighted `ℓ²` / spike counterexample:** REVIEWED. This is the exact counterexample that
  falsified the prior generic-`p,q` form — see the postmortem doc, "Explicit counterexample at
  `p = q = 1`" (weighted Hilbert triple on `ℓ²`, triangle spikes on disjoint shrinking
  intervals). At `p = q = 2` the same construction's `L²`-norms diverge
  (`∑ 2^{2n}·4^{-n} = ∑ 1 = ∞`), so it is not a counterexample at this exponent.
- **`p = 1, q = ∞` (mixed endpoint):** NOT covered by this declaration — out of scope, no proof
  plan exists.
- **Noncomplete `V`:** N/A — `GelfandTriple` requires `V` complete (Hilbert) by construction; not
  an independent axis for this declaration.
- **Nonmeasurable perturbation:** N/A — `uV` is universally quantified over an arbitrary function
  of the stated type; `W1pTime` membership already forces the required measurability/integrability
  via `MemLp`.

## Gate separation

- **Elaboration gate:** the declaration type-checks (`sorry`-free otherwise); confirmed by
  `lake build` in the release-candidate attestation and by local incremental builds.
- **Axiom gate:** `sorry`/`sorryAx` only, via the same-line `ALLOW_SORRY` marker; no `axiom` /
  `opaque` introduced. `scripts/check-no-axiom.sh` and `scripts/check-axioms-live.sh` cover this.
- **Semantic (statement-truth) gate:** this card. The `p = q = 2` restriction is the semantic
  fix; `scripts/check-statement-cards.sh` guards against silent regeneralization.

## Required before widening

A generic-`p, q` (or any `p, q ≠ 2, 2`) version of this declaration MUST NOT be reintroduced
without, together in the same PR:

1. an exact literature citation (edition, theorem number, page) for that exact exponent pair;
2. an explicit exponent-compatibility hypothesis on the dual pairing, stated in the Lean type
   (not left implicit in prose);
3. a proof, or an explicit experimental/scaffold status with the boundary-case checklist above
   re-run at the new generality (in particular, re-checking whether the weighted-`ℓ²` spike
   counterexample still applies);
4. an update to this card and to `scripts/check-statement-cards.sh`'s guard (a).
