-- Scratch ENVIRONMENT manifest (issue #212 B0 codex-gate pass-6 finding 1;
-- docs/scratch/r3-global-diagonal-campaign.md §6 clause 4, §11.6).
--
-- Run via:
--   lake env lean scripts/scratch_manifest.lean
-- (after `lake build` of the scratch targets; consumed EXCLUSIVELY by
-- scripts/check-scratch-pins.sh).
--
-- WHY THIS EXISTS.  Passes 4–6 of the #212 B0 statement gate demonstrated that a
-- TEXT-scanning manifest (regex over the scratch sources + `#print axioms` lines
-- parsed out of the lake build log) cannot be made fail-closed: each round found a
-- new evasion (modifier-prefixed declarations, indented/Unicode declaration names,
-- anonymous instances, macro-generated declarations, and — worst — the pin parser
-- trusted arbitrary build-log text, so command output could SPOOF pin lines).  This
-- script ends that class: it enumerates the scratch targets' declarations from the
-- ELABORATED ENVIRONMENT (the same environment the kernel checked), so every
-- constant — however it was spelled or generated — is just an environment entry
-- here, and computes each constant's axiom closure with `Lean.collectAxioms` (the
-- machinery behind `#print axioms`), so the axiom evidence never passes through a
-- spoofable text channel.
--
-- OUTPUT GRAMMAR (the ONLY text check-scratch-pins.sh accepts as evidence):
--   SCRATCH-MANIFEST-START
--   DECL|<class>|<name>|<kind>|<axioms>          (one line per environment constant
--                                                 of a target module; <axioms> is a
--                                                 comma-joined list or `-` if empty)
--   VIOLATION|<rule>|<detail...>                 (zero lines when clean)
--   SCRATCH-MANIFEST-END|<decl-count>|<OK|FAIL>
-- <class> is `surface` (must equal the checker's pinned enumeration exactly),
-- `child` (compiler-generated companion of a surface inductive/ctor/def: projections,
-- ctors, recursors, casesOn/noConfusion/injEq/eq_def families), `internal`
-- (`Name.isInternalDetail`/`isInternal`: proof_/match_/eq_N/macro-scoped auxiliaries),
-- or `codegen` (ModuleData.extraConstNames entries with no ConstantInfo).  EVERY
-- class gets the kernel-trio axiom check — internals and children included, which is
-- strictly stronger than the retired per-pin text scheme.
--
-- SPOOF RESISTANCE.  The only import-time execution channel a scratch module has is
-- an `initialize` block, and (a) initializers fire while the environment is set up,
-- BEFORE this script's commands elaborate — any output they inject lands before the
-- real SCRATCH-MANIFEST-START, and a fully faked block trips the consumer's
-- exactly-one-START/exactly-one-END rule because the real block still follows;
-- (b) initializer aux definitions are environment constants of the scratch module,
-- rejected below by name (`initFn`).  Declaring `axiom`/`opaque`/`unsafe`/`private`
-- in a scratch target is likewise rejected from the environment itself, where no
-- surface spelling can hide it.
import Lean
import LerayHopf.Scratch.KappaReindex
import LerayHopf.Scratch.P2ExitContract
import LerayHopf.Scratch.KappaShapeGate
import LerayHopf.Scratch.R3ShapeGate
import LerayHopf.Scratch.R3StageCoherence
import LerayHopf.Scratch.R3KappaSeed
import LerayHopf.Scratch.R3ProductionCoupling

open Lean

/-- The scratch gate targets (keep in sync with `targets=(…)` in
`scripts/check-scratch-pins.sh`; a missing module is a VIOLATION, not a skip). -/
def scratchTargets : Array Name := #[
  `LerayHopf.Scratch.KappaReindex,
  `LerayHopf.Scratch.P2ExitContract,
  `LerayHopf.Scratch.KappaShapeGate,
  `LerayHopf.Scratch.R3ShapeGate,
  `LerayHopf.Scratch.R3StageCoherence,
  `LerayHopf.Scratch.R3KappaSeed,
  `LerayHopf.Scratch.R3ProductionCoupling]

/-- The kernel trio — the ONLY axioms any scratch constant may depend on. -/
def kernelTrio : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Companion definitions Lean generates next to an inductive/structure `P`
(`P.recOn`, `P.casesOn`, `P.ctorIdx`, …).  `P.rec` and constructors are recognized
by `ConstantInfo` kind instead, projections via `getProjectionFnInfo?`. -/
def indGenSuffixes : List String :=
  ["recOn", "casesOn", "brecOn", "binductionOn", "below", "ibelow",
   "noConfusion", "noConfusionType", "ndrec", "ndrecOn", "ctorIdx"]

/-- Companion theorems Lean generates next to a constructor `P.mk`. -/
def ctorGenSuffixes : List String :=
  ["injEq", "sizeOf_spec", "inj", "noConfusion", "noConfusionType"]

/-- Equational/congruence companions Lean generates next to a `def`/`theorem`
(numbered equation lemmas `eq_N` are already `Name.isInternalDetail`; `congr_simp`
auxiliaries can be realized in a USING module for an imported parent, so the parent
may live outside the scratch targets). -/
def defGenSuffixes : List String := ["eq_def", "eq_unfold", "congr_simp"]

/-- `initialize`/`builtin_initialize` aux definitions carry an `initFn` name
component; they are the one import-time IO channel and are banned outright. -/
def hasInitFnComponent : Name → Bool
  | .str p s => s.startsWith "initFn" || hasInitFnComponent p
  | .num p _ => hasInitFnComponent p
  | .anonymous => false

def kindStr : ConstantInfo → String
  | .axiomInfo _  => "axiom"
  | .defnInfo _   => "def"
  | .thmInfo _    => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _   => "quot"
  | .inductInfo _ => "inductive"
  | .ctorInfo _   => "ctor"
  | .recInfo _    => "recursor"

/-- Surface/child/internal classification, computed from the environment only.
A suffix-recognized companion is `child` only when its parent EXISTS as a constant
of the matching kind (hand-writing e.g. `theorem Foo.casesOn2` stays `surface`).
Fail-closed direction: anything unrecognized is `surface` and must therefore appear
in the checker's pinned enumeration — an unexpected constant FAILS the gate loudly
rather than slipping past it. -/
def classify (env : Environment) (n : Name) : String :=
  if n.isInternalDetail || n.isInternal then "internal"
  else if (env.getProjectionFnInfo? n).isSome then "child"
  else match env.find? n with
  | some (.ctorInfo _) => "child"
  | some (.recInfo _)  => "child"
  | _ =>
    match n with
    | .str p s =>
      match env.find? p with
      | some (.inductInfo _) =>
        if indGenSuffixes.contains s then "child" else "surface"
      | some (.ctorInfo _) =>
        if ctorGenSuffixes.contains s then "child" else "surface"
      | some (.defnInfo _) | some (.thmInfo _) =>
        if defGenSuffixes.contains s then "child" else "surface"
      | _ => "surface"
    | _ => "surface"

open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut targetIdxs : Array Nat := #[]
  let mut missing : Array Name := #[]
  for tmod in scratchTargets do
    match env.getModuleIdx? tmod with
    | some i => targetIdxs := targetIdxs.push i.toNat
    | none   => missing := missing.push tmod
  IO.println "SCRATCH-MANIFEST-START"
  let mut nDecl := 0
  let mut nViol := 0
  for tmod in missing do
    IO.println s!"VIOLATION|module-missing|{tmod}"
    nViol := nViol + 1
  for i in targetIdxs do
    if h : i < env.header.moduleData.size then
      let md := env.header.moduleData[i]
      for n in md.constNames ++ md.extraConstNames do
        if isPrivateName n then
          IO.println s!"VIOLATION|private-decl|{n}"
          nViol := nViol + 1
        if hasInitFnComponent n then
          IO.println s!"VIOLATION|initializer|{n}"
          nViol := nViol + 1
        let ci? := env.find? n
        match ci? with
        | some (.axiomInfo _) =>
          IO.println s!"VIOLATION|axiom-decl|{n}"
          nViol := nViol + 1
        | some (.opaqueInfo _) =>
          IO.println s!"VIOLATION|opaque-decl|{n}"
          nViol := nViol + 1
        | some (.defnInfo v) =>
          if v.safety != .safe then
            IO.println s!"VIOLATION|non-safe-def|{n}"
            nViol := nViol + 1
        | _ => pure ()
        let axs ← collectAxioms n
        for ax in axs do
          if !kernelTrio.contains ax then
            IO.println s!"VIOLATION|axioms|{n}|{ax}"
            nViol := nViol + 1
        let axStr := if axs.isEmpty then "-"
          else String.intercalate "," (axs.toList.map toString)
        let kind := match ci? with
          | some ci => kindStr ci
          | none    => "codegen"
        IO.println s!"DECL|{classify env n}|{n}|{kind}|{axStr}"
        nDecl := nDecl + 1
    else
      IO.println s!"VIOLATION|no-module-data|{i}"
      nViol := nViol + 1
  IO.println s!"SCRATCH-MANIFEST-END|{nDecl}|{if nViol == 0 then "OK" else "FAIL"}"
  if nViol != 0 then
    throwError "scratch environment manifest: {nViol} violation(s) — see VIOLATION lines"
