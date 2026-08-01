-- SCRATCH — issue #212 B0 exact-shape gate (codex statement-gate pass-3 finding 1;
-- docs/scratch/r3-global-diagonal-campaign.md §4.1/§6 clause 6, §11.3). NOT production.
--
-- MECHANISM.  Each probe below RE-STATES a κ-critical declaration surface of the
-- compiled κ-package model verbatim — with the index map `κ` a FREE VARIABLE — and
-- proves it by the raw field projection / lemma application (a bare term: no `by`,
-- no rewriting).  Elaboration therefore succeeds ONLY if the declared type of the
-- projected field literally carries the effective index `galSeq (κ (φ n))`: `κ` is
-- universally bound in the probe, so a stale/bare-index field `galSeq (p.φ n)` (as
-- in a "dummy κ" package that takes the parameter but never applies it) does NOT
-- unify with the probe's `galSeq (κ (p.φ n))`, and the probe FAILS TO COMPILE.
-- This makes the primary type-level κ-invariant of campaign-doc §4.1 a mechanical,
-- independently executable assertion — prose-free: `bash scripts/check-scratch-pins.sh`
-- rebuilds this module from deleted artifacts and pins every probe to the kernel trio.
--
-- The P2′ production twin (`LerayHopf/Scratch/R3ShapeGate.lean`, statements frozen
-- verbatim in campaign-doc §6 clause 6) applies the same probes to
-- `AubinLionsPackage_R3` and `R3KappaChainExitWitness`; it is an exit-gate clause,
-- required green before any P3′/P4′ dispatch.
import LerayHopf.Scratch.P2ExitContract

open MeasureTheory Filter Topology Set

namespace LerayHopf
namespace Scratch212

open Scratch195

/-- Probe (a) — the κ-package's convergence field is TYPED at the effective index
`galSeq (κ (φ n))`.  Proof is the bare projection: if the field were declared at the
stale index `galSeq (φ n)` (κ present but unapplied), this statement — in which `κ`
is free — would not elaborate. -/
theorem packageShape_strong_convergence_effective
    (F : Torus3NSForms) (ν T : ℝ) (u₀ : L2Sigma)
    (galSeq : ∀ n, GalerkinSolutionData F ν u₀ n) (κ : ℕ → ℕ)
    (p : AubinLionsPackageKappa F ν T u₀ galSeq κ) :
    Filter.Tendsto
      (fun n => MeasureTheory.eLpNorm
        (fun t => ((galSeq (κ (p.φ n))).u t : L2VF) - (p.u t : L2VF))
        2 (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)))
      Filter.atTop (nhds 0) :=
  p.strong_convergence

/-- Probe (b) — the effective-map strictness surface has the composed shape
`StrictMono (fun n => κ (φ n))`, obtained from the package's composition lemma (not
from bare `φ_mono`). -/
theorem packageShape_effective_strictMono
    (F : Torus3NSForms) (ν T : ℝ) (u₀ : L2Sigma)
    (galSeq : ∀ n, GalerkinSolutionData F ν u₀ n) (κ : ℕ → ℕ) (hκ : StrictMono κ)
    (p : AubinLionsPackageKappa F ν T u₀ galSeq κ) :
    StrictMono (fun n => κ (p.φ n)) :=
  p.effective_strictMono hκ

/-- Probe (c) — extraction-dependent cofinality at the EFFECTIVE index (codex pass-3
finding 2, category (iii) of campaign-doc §4.1): the `hlevel`-style bound that the
good-representative layer uses to fire per-test Lipschitz/cutoff leaves is derivable
at `κ (φ n)` FROM the package's effective map alone.  Under κ-threading this bound —
not the bare `n ≤ φ n` — is the one that pairs with the data the chain actually
consumes; the probe shows the required effective-map coupling compiles. -/
theorem packageShape_effective_le_apply
    (F : Torus3NSForms) (ν T : ℝ) (u₀ : L2Sigma)
    (galSeq : ∀ n, GalerkinSolutionData F ν u₀ n) (κ : ℕ → ℕ) (hκ : StrictMono κ)
    (p : AubinLionsPackageKappa F ν T u₀ galSeq κ) :
    ∀ n, n ≤ κ (p.φ n) :=
  fun _ => (p.effective_strictMono hκ).le_apply

/-- Probe (d) — the exit witness's pin surface is phrased against the DEPENDENT
family `galSeq₁` itself at the package extraction (the §6 invariant).  Bare
projection: a witness whose pin were phrased against a base family, or at a bare
index, would not elaborate against this statement. -/
theorem witnessShape_pin_dependent_family
    (F : Torus3NSForms) (ν T : ℝ) (u₀ : L2Sigma) (φ₁ : ℕ → ℕ)
    (galSeq₁ : ∀ k, GalerkinSolutionData F ν u₀ (φ₁ k))
    (w : P2ExitWitness F ν T u₀ φ₁ galSeq₁) :
    ∀ t, t ∈ Set.Icc (0 : ℝ) T → ∀ z : L2VF,
      Filter.Tendsto
        (fun k => inner (𝕜 := ℝ) (((galSeq₁ (w.alPkg.φ (w.ρ k))).u t : L2VF)) z)
        Filter.atTop (nhds (inner (𝕜 := ℝ) ((w.v t : L2VF)) z)) :=
  w.pin

end Scratch212
end LerayHopf

-- Axiom pins (campaign doc §6 clause 4 / §7; enforced by scripts/check-scratch-pins.sh;
-- expected: at most [propext, Classical.choice, Quot.sound] — no sorryAx, no project axioms).
#print axioms LerayHopf.Scratch212.packageShape_strong_convergence_effective
#print axioms LerayHopf.Scratch212.packageShape_effective_strictMono
#print axioms LerayHopf.Scratch212.packageShape_effective_le_apply
#print axioms LerayHopf.Scratch212.witnessShape_pin_dependent_family
