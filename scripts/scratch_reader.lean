-- Scratch STATIC OLEAN READER (issue #212 B0 codex-gate pass-7 findings 1–3;
-- docs/scratch/r3-global-diagonal-campaign.md §6 clause 4, §11.7).
--
-- Run via:
--   lake env lean scripts/scratch_reader.lean
-- (after `lake build` of the scratch targets; consumed EXCLUSIVELY by
-- scripts/check-scratch-pins.sh, which snapshots this script AND the frozen
-- manifest scripts/scratch-manifest.expected to a private temp dir BEFORE the
-- untrusted `lake build` step, then diffs this script's output block against the
-- snapshot byte-for-byte).
--
-- TRUST MODEL (pass-7 finding 2 — the terminal fix for the whole evasion axis).
-- The pass-6 manifest imported the scratch targets and enumerated the elaborated
-- environment; codex round 7 observed that importing a target EXECUTES it: an
-- `initialize` block or a registered command elaborator from a target module runs
-- inside the manifest process and could fake the evidence block wholesale.  This
-- reader closes that channel structurally: it imports ONLY `Lean` (pinned
-- toolchain code) and reads the target .olean files as DATA via
-- `Lean.readModuleData` — pure deserialization of the compacted region.  Zero
-- elaboration of target code, zero initializer execution, zero imported syntax or
-- command extensions.  No target-authored code runs in this process, so no
-- target-authored code can influence what is printed.
--
-- EVIDENCE SOURCES (all statically read, all produced by the pinned toolchain at
-- olean export time, i.e. by the compiler — not recomputed here and not
-- influenceable by target-module run-time behavior):
--   * `ModuleData.constNames`/`constants` — the complete kernel-checked constant
--     list of each target module.  A declaration cannot exist without appearing
--     here, whatever its surface spelling (pass-7 finding 1: nothing lexical can
--     hide a constant from this enumeration).
--   * `ModuleData.extraConstNames` — codegen-only auxiliary names.
--   * The `exportedAxiomsExt` persistent-extension entries — the toolchain's OWN
--     per-declaration axiom closures, precomputed by `beforeExportFn` when the
--     olean is serialized (this is the exact data `#print axioms` /
--     `Lean.collectAxioms` consult for imported declarations).  Coverage is 1:1
--     with `constNames`; a constant with no entry is a VIOLATION, fail-closed.
--   * `Lean.projectionFnInfoExt` / `Lean.auxRecExt` entries — exact compiler
--     provenance for projection functions and auxiliary recursors (casesOn/recOn),
--     used for classification labels.
--   * `ConstantInfo.type.hash` — a structural hash of each declaration's
--     elaborated statement, deterministic for a pinned toolchain and identical
--     sources.  Freezing it in scratch-manifest.expected freezes every STATEMENT,
--     not just every name: editing any type re-hashes and fails the byte-diff.
--   * `ConstantInfo.value` of the free-κ guards (pass-7 finding 3): each guard's
--     proof term must reference its seeded theorem directly (DEPGUARD lines).
--     At P2′ the sanctioned (δ) re-point (campaign doc §6 clause 6) swaps the
--     guards' proof heads to the κ-threaded production declarations; that same
--     reviewed diff MUST update the DEPGUARD pairs below and the expected
--     manifest together — the gate is deliberately broken by a re-point that
--     forgets either.
--
-- CLASSIFICATION IS DISPLAY-ONLY (pass-7 finding 1).  Passes 4–6 tried to make
-- the surface/child/internal partition load-bearing and codex kept finding
-- lexical collisions (a hand-written `theorem P.ibelow` or `C.mk.noConfusionType`
-- matches a generated-name pattern; `Name.isInternalDetail` is lexical, so a
-- hand-written `P.proof_1` looks internal).  The pass-7 gate therefore pins the
-- TOTAL manifest: every constant of every target — surface, child, internal,
-- codegen alike — is one frozen DECL line (class, name, kind, type hash, axiom
-- closure) byte-compared against scratch-manifest.expected.  A collision-named
-- declaration is still a NEW constant: it adds a DECL line that is not in the
-- frozen manifest and the gate fails, whatever label it gets.  The 54-name
-- surface equality is retained as a redundant human-level check, no longer
-- load-bearing alone.  (`LerayHopf/Scratch/GateFixture.lean` +
-- scripts/scratch_fixture_selftest.lean keep a compiled collision fixture proving
-- the enumeration sees such declarations.)
--
-- RESIDUAL TRUST BOUNDARY (documented, not hidden): `lake build` of the targets
-- elaborates scratch source, and elaboration can run arbitrary same-user IO
-- (`#eval`, macros).  The checker therefore snapshots this script and the
-- expected manifest BEFORE building; the oleans this reader consumes are kernel-
-- checked artifacts of the reviewed sources.  What remains (a build-time-forked
-- daemon racing the checker's temp files) is same-user filesystem malice, out of
-- scope for the B0 gate and covered by the fact that every scratch source line is
-- in the reviewed diff.  Lakefile and toolchain are trusted (repo-owned, not
-- scratch-editable).
--
-- OUTPUT GRAMMAR (the ONLY text check-scratch-pins.sh accepts as evidence):
--   SCRATCH-MANIFEST-START
--   DECL|<class>|<name>|<kind>|<type-hash>|<axioms>   (one line per constant of a
--                                                      target module; <axioms> is a
--                                                      comma-joined sorted list or
--                                                      `-` if empty)
--   DEPGUARD|<guard>|<seed>|direct                    (one line per free-κ guard)
--   VIOLATION|<rule>|<detail...>                      (zero lines when clean)
--   SCRATCH-MANIFEST-END|<decl-count>|<depguard-count>|<OK|FAIL>
import Lean

open Lean

/-- The scratch gate targets (keep in sync with `targets=(…)` in
`scripts/check-scratch-pins.sh` and with scratch-manifest.expected; a missing
olean is a hard error, not a skip). -/
def scratchTargets : Array Name := #[
  `LerayHopf.Scratch.KappaReindex,
  `LerayHopf.Scratch.P2ExitContract,
  `LerayHopf.Scratch.KappaShapeGate,
  `LerayHopf.Scratch.R3ShapeGate,
  `LerayHopf.Scratch.R3StageCoherence,
  `LerayHopf.Scratch.R3KappaSeed,
  `LerayHopf.Scratch.R3ProductionCoupling]

/-- The free-κ statement guards (round-6 finding 2) and the seeded theorems their
proof terms MUST reference directly (round-7 finding 3).  See the (δ) lifecycle
rule in the campaign doc §6 clause 6 for the sanctioned P2′ re-point. -/
def depGuards : List (Name × Name) := [
  (`LerayHopf.Scratch212.diag_ae_subseq_seeded_free_kappa_exact_shape,
   `LerayHopf.Scratch212.diag_ae_subseq_seeded),
  (`LerayHopf.Scratch212.spacetime_extraction_seeded_free_kappa_exact_shape,
   `LerayHopf.Scratch212.spacetime_extraction_seeded)]

/-- The kernel trio — the ONLY axioms any scratch constant may depend on. -/
def kernelTrio : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- On-disk name of the toolchain's precomputed-axioms extension
(`private builtin_initialize exportedAxiomsExt` in Lean/Util/CollectAxioms.lean;
the private prefix is part of the serialized name). -/
def axExtName : Name :=
  ((`_private.Lean.Util.CollectAxioms).num 0).str "Lean" |>.str "exportedAxiomsExt"

-- Persistent-extension entries are serialized as opaque `EnvExtensionEntry`
-- values; decoding them back to the extension's entry type is the same
-- `unsafeCast` the import machinery itself performs (types fixed by the pinned
-- toolchain: exportedAxiomsExt entries are `Name × Array Name`, tag extensions
-- store `Name`, map extensions store `Name × α`).
unsafe def decodeAxEntryImpl (e : EnvExtensionEntry) : Name × Array Name := unsafeCast e
@[implemented_by decodeAxEntryImpl]
opaque decodeAxEntry (e : EnvExtensionEntry) : Name × Array Name

unsafe def decodeTagEntryImpl (e : EnvExtensionEntry) : Name := unsafeCast e
@[implemented_by decodeTagEntryImpl]
opaque decodeTagEntry (e : EnvExtensionEntry) : Name

unsafe def decodeProjEntryImpl (e : EnvExtensionEntry) : Name × ProjectionFunctionInfo := unsafeCast e
@[implemented_by decodeProjEntryImpl]
opaque decodeProjEntry (e : EnvExtensionEntry) : Name × ProjectionFunctionInfo

/-- Companion definitions Lean generates next to an inductive/structure `P`. -/
def indGenSuffixes : List String :=
  ["recOn", "casesOn", "brecOn", "binductionOn", "below", "ibelow",
   "noConfusion", "noConfusionType", "ndrec", "ndrecOn", "ctorIdx"]

/-- Companion theorems Lean generates next to a constructor `P.mk`. -/
def ctorGenSuffixes : List String :=
  ["injEq", "sizeOf_spec", "inj", "noConfusion", "noConfusionType"]

/-- Equational/congruence companions Lean generates next to a `def`/`theorem`
(`congr_simp` auxiliaries can be realized in a USING module for an imported
parent, so the parent may live outside the scratch targets — LerayHopf production
modules are loaded for the parent-kind lookup; a parent outside that closure
defaults to `surface`, fail-closed). -/
def defGenSuffixes : List String := ["eq_def", "eq_unfold", "congr_simp"]

/-- `initialize`/`builtin_initialize` aux definitions carry an `initFn` name
component.  They no longer execute anywhere in the gate (nothing imports the
targets), but an `initialize` block has no business in a scratch module and is
banned outright. -/
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

/-- Everything the reader accumulates from statically loaded oleans. -/
structure Loaded where
  /-- Module name → data, for the targets and their LerayHopf.* import closure. -/
  mods     : Array (Name × ModuleData) := #[]
  /-- Compacted regions, kept alive for the process lifetime (never freed). -/
  regions  : Array CompactedRegion := #[]
  visited  : NameSet := {}
  /-- name → ConstantInfo across all loaded modules (parent-kind lookups, guards). -/
  consts   : NameMap ConstantInfo := {}
  /-- Toolchain-precomputed axiom closures of TARGET-module constants. -/
  axioms   : NameMap (Array Name) := {}
  /-- Exact compiler provenance (target modules): projections, aux recursors. -/
  projTags : NameSet := {}
  auxRecs  : NameSet := {}

/-- Read the targets plus their transitive `LerayHopf.*` imports (mathlib/core
imports are never read: axiom evidence for anything imported is already folded
into the targets' own exported entries by the toolchain). -/
partial def load (work : List Name) (acc : Loaded) : IO Loaded := do
  match work with
  | [] => return acc
  | m :: rest =>
    if acc.visited.contains m then load rest acc else
    let path ← findOLean m
    let (md, region) ← readModuleData path
    let isTarget := scratchTargets.contains m
    let mut acc := { acc with
      visited := acc.visited.insert m
      mods    := acc.mods.push (m, md)
      regions := acc.regions.push region }
    for (n, ci) in md.constNames.zip md.constants do
      acc := { acc with consts := acc.consts.insert n ci }
    if isTarget then
      for (extName, es) in md.entries do
        if extName == axExtName then
          for e in es do
            let (n, axs) := decodeAxEntry e
            acc := { acc with axioms := acc.axioms.insert n axs }
        else if extName == `Lean.projectionFnInfoExt then
          for e in es do
            acc := { acc with projTags := acc.projTags.insert (decodeProjEntry e).1 }
        else if extName == `Lean.auxRecExt then
          for e in es do
            acc := { acc with auxRecs := acc.auxRecs.insert (decodeTagEntry e) }
    let deps := md.imports.toList.map (·.module) |>.filter (·.getRoot == `LerayHopf)
    load (deps ++ rest) acc

/-- Surface/child/internal classification — DISPLAY-ONLY since pass-7 (see
header): the gate pins every constant totally, so a mislabel cannot hide a
declaration; labels only keep the manifest and the 54-pin cross-check readable.
Rule order matches the pass-6 classifier for label stability, with exact
compiler provenance (projection/auxRec tags) consulted before suffix patterns. -/
def classify (acc : Loaded) (n : Name) : String :=
  if n.isInternalDetail || n.isInternal then "internal"
  else if acc.projTags.contains n then "child"
  else if acc.auxRecs.contains n then "child"
  else match acc.consts.find? n with
  | some (.ctorInfo _) => "child"
  | some (.recInfo _)  => "child"
  | _ =>
    match n with
    | .str p s =>
      match acc.consts.find? p with
      | some (.inductInfo _) =>
        if indGenSuffixes.contains s then "child" else "surface"
      | some (.ctorInfo _) =>
        if ctorGenSuffixes.contains s then "child" else "surface"
      | some (.defnInfo _) | some (.thmInfo _) =>
        if defGenSuffixes.contains s then "child" else "surface"
      | _ => "surface"
    | _ => "surface"

def main' : IO Unit := do
  let acc ← load scratchTargets.toList {}
  IO.println "SCRATCH-MANIFEST-START"
  let mut nDecl := 0
  let mut nViol := 0
  let mut nDep  := 0
  for tmod in scratchTargets do
    let some (_, md) := acc.mods.find? (·.1 == tmod)
      | throw <| IO.userError s!"scratch reader: module data missing for {tmod}"
    let names := md.constNames.qsort (fun a b => a.toString < b.toString)
    let extras := md.extraConstNames.qsort (fun a b => a.toString < b.toString)
    for n in names ++ extras do
      if isPrivateName n then
        IO.println s!"VIOLATION|private-decl|{n}"
        nViol := nViol + 1
      if hasInitFnComponent n then
        IO.println s!"VIOLATION|initializer|{n}"
        nViol := nViol + 1
      let ci? := acc.consts.find? n
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
      | some (.inductInfo v) =>
        if v.isUnsafe then
          IO.println s!"VIOLATION|unsafe-inductive|{n}"
          nViol := nViol + 1
      | _ => pure ()
      -- Axiom evidence: the toolchain's own exported closure.  Constants without
      -- an entry are codegen extras (no ConstantInfo); a REAL constant with no
      -- entry is fail-closed a violation.
      let axStr ← match acc.axioms.find? n with
        | some axs =>
          for ax in axs do
            if !kernelTrio.contains ax then
              IO.println s!"VIOLATION|axioms|{n}|{ax}"
              nViol := nViol + 1
          pure <| if axs.isEmpty then "-"
            else String.intercalate "," (axs.toList.map toString)
        | none =>
          if ci?.isSome then
            IO.println s!"VIOLATION|missing-axiom-entry|{n}"
            nViol := nViol + 1
          pure "-"
      let kind := match ci? with
        | some ci => kindStr ci
        | none    => "codegen"
      let hash := match ci? with
        | some ci => toString ci.type.hash
        | none    => "-"
      IO.println s!"DECL|{classify acc n}|{n}|{kind}|{hash}|{axStr}"
      nDecl := nDecl + 1
  for (guard, seed) in depGuards do
    match acc.consts.find? guard with
    | some (.thmInfo v) =>
      if v.value.getUsedConstants.contains seed then
        IO.println s!"DEPGUARD|{guard}|{seed}|direct"
        nDep := nDep + 1
      else
        IO.println s!"VIOLATION|depguard-missing-seed|{guard}|{seed}"
        nViol := nViol + 1
    | _ =>
      IO.println s!"VIOLATION|depguard-not-a-theorem|{guard}"
      nViol := nViol + 1
  IO.println s!"SCRATCH-MANIFEST-END|{nDecl}|{nDep}|{if nViol == 0 then "OK" else "FAIL"}"
  if nViol != 0 then
    throw <| IO.userError s!"scratch static reader: {nViol} violation(s) — see VIOLATION lines"

#eval main'
