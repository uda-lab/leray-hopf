-- Scratch STATIC OLEAN READER (issue #212 B0 codex-gate pass-7 findings 1–3,
-- REVISED at pass-8 findings 1–3;
-- docs/scratch/r3-global-diagonal-campaign.md §6 clause 4, §11.7, §11.8).
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
-- ASSUMPTIONS (hard-rule-5 register; the marked declarations below are the ONLY
-- trust-extending declarations in the gate, and each cites this section):
--   A1 (layout pin): under the repo-pinned toolchain (`lean-toolchain`,
--      leanprover/lean4:v4.31.0-rc2 — repo-owned, not scratch-editable), the
--      persistent-extension entries recorded under `exportedAxiomsExt` in an
--      .olean have payload type `Name × Array Name`: that is the entry type
--      `exportEntriesFnEx` constructs in Lean/Util/CollectAxioms.lean, and the
--      `unsafeCast` in `decodeAxEntryImpl` is the SAME cast the toolchain's own
--      import machinery performs when it consumes these entries (extension
--      payloads are serialized as opaque `EnvExtensionEntry` values by design;
--      the toolchain provides no typed public decoder at ModuleData level).
--   A2 (fail-loud): the decoded data cannot drift silently.  It is cross-checked
--      by (i) 1:1 coverage against `constNames` (a real constant without an
--      entry is a VIOLATION), (ii) the kernel-trio whitelist on every decoded
--      axiom name, and (iii) the total byte-diff against the frozen manifest.
--      A layout change under a future toolchain bump yields garbage `Name`s and
--      trips (i)–(iii); it cannot decode to plausible-but-wrong closures.
--   A3 (why not recompute): computing axiom closures by walking
--      `ConstantInfo.value` proof terms would need name→ConstantInfo for the
--      full transitive import graph (mathlib-scale: thousands of modules,
--      millions of constants) loaded in this container's 3.4 GiB cgroup —
--      an OOM-prohibitive reimplementation of exactly the computation whose
--      toolchain-exported result we read (`exportedAxiomsExt` is the data
--      `#print axioms` / `Lean.collectAxioms` consult for imported constants).
--      Pass-8 removed every OTHER unsafe/opaque declaration this file had
--      (projection/auxRec extension decoders): projections are now derived from
--      constructor binder telescopes — pure `ModuleData`, no casts.
--   A4 (digest tool): statement digests are SHA-256, computed by piping the
--      canonical serialization through `sha256sum` (GNU coreutils, container-
--      provided) — the same trust class as the grep/awk/diff the bash checker
--      itself is built from.
--
-- EVIDENCE SOURCES (all statically read, all produced by the pinned toolchain at
-- olean export time, i.e. by the compiler — not influenceable by target-module
-- run-time behavior):
--   * `ModuleData.constNames`/`constants` — the complete kernel-checked constant
--     list of each target module.  A declaration cannot exist without appearing
--     here, whatever its surface spelling (pass-7 finding 1: nothing lexical can
--     hide a constant from this enumeration).
--   * `ModuleData.extraConstNames` — codegen-only auxiliary names.
--   * The `exportedAxiomsExt` persistent-extension entries — the toolchain's OWN
--     per-declaration axiom closures, precomputed when the olean is serialized.
--     Coverage is 1:1 with `constNames`; a constant with no entry is a
--     VIOLATION, fail-closed.  (Decoded under ASSUMPTIONS A1–A2.)
--   * A SHA-256 STATEMENT DIGEST per constant (pass-8 finding 2 replaced the
--     32-bit-truncating `Expr.hash`, which was neither injective nor
--     levelParams-aware): the digest is taken over a CANONICAL HASH-CONSED
--     SERIALIZATION of `levelParams` plus the full elaborated type — every
--     unique subterm is emitted exactly once as an indexed node (constants with
--     universe levels, sorts, binder names + binder info, literals,
--     projections, let/lambda/forall structure), children referenced by index
--     in deterministic first-visit order.  The stream determines the term, so
--     equal digests mean equal serializations, i.e. equal types (two caveats,
--     both fail-closed or inert: binder NAMES are included, so an
--     alpha-renaming changes the digest and surfaces in review as a manifest
--     edit; `mdata` PAYLOADS are elided — node presence is kept — matching the
--     kernel's treatment of mdata as inert annotation).  Collision resistance
--     is SHA-256's.  Freezing these digests in scratch-manifest.expected
--     freezes every STATEMENT, not just every name: editing any type re-digests
--     and fails the byte-diff.  (Sharing note: the serialization is emitted per
--     constant with a fresh index table; hash-consing keeps it proportional to
--     unique subterms — the expanded trees of these statements measure in the
--     gigabytes and are never materialized.)
--   * `ConstantInfo.value` of the free-κ guards (pass-7 finding 3, STRENGTHENED
--     at pass-8 finding 3): a guard's proof term, after stripping its leading
--     lambda binders (the guard's own hypotheses) and inert mdata, must have the
--     seeded theorem as its APPLICATION HEAD — `DEPGUARD|…|head` lines.  Mere
--     occurrence of the seed anywhere in the term (an unused `let`, a dead
--     branch) no longer passes: the seed application must be the term that
--     PROVES the guard.  At P2′ the sanctioned (δ) re-point (campaign doc §6
--     clause 6) swaps the guards' proof heads to the κ-threaded production
--     declarations; that same reviewed diff MUST update the DEPGUARD pairs
--     below, the checker's DEPGUARD lines, and the expected manifest together —
--     the gate is deliberately broken by a re-point that forgets any of them.
--
-- CLASSIFICATION IS DISPLAY-ONLY (pass-7 finding 1).  Passes 4–6 tried to make
-- the surface/child/internal partition load-bearing and codex kept finding
-- lexical collisions (a hand-written `theorem P.ibelow` or `C.mk.noConfusionType`
-- matches a generated-name pattern; `Name.isInternalDetail` is lexical, so a
-- hand-written `P.proof_1` looks internal).  The pass-7 gate therefore pins the
-- TOTAL manifest: every constant of every target — surface, child, internal,
-- codegen alike — is one frozen DECL line (class, name, kind, statement digest,
-- axiom closure) byte-compared against scratch-manifest.expected.  A
-- collision-named declaration is still a NEW constant: it adds a DECL line that
-- is not in the frozen manifest and the gate fails, whatever label it gets.  The
-- 54-name surface equality is retained as a redundant human-level check, no
-- longer load-bearing alone.  (`LerayHopf/Scratch/GateFixture.lean` +
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
--   DECL|<class>|<name>|<kind>|<sha256|- >|<axioms>   (one line per constant of a
--                                                      target module; digest `-`
--                                                      only for codegen extras;
--                                                      <axioms> is a comma-joined
--                                                      list or `-` if empty)
--   DEPGUARD|<guard>|<seed>|head                      (one line per free-κ guard)
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

/-- The free-κ statement guards (round-6 finding 2) and the seeded theorems that
must be each guard's proof-term APPLICATION HEAD (round-7 finding 3, head-check
per round-8 finding 3).  See the (δ) lifecycle rule in the campaign doc §6
clause 6 for the sanctioned P2′ re-point. -/
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
-- values; this pair is the gate's ONLY trust-extending surface (pass-8
-- finding 1: marked, registered, and minimized — the two display-only decoders
-- pass-7 also had were removed in favor of cast-free derivations).
unsafe def decodeAxEntryImpl (e : EnvExtensionEntry) : Name × Array Name := unsafeCast e -- ALLOW_AXIOM: decode of the toolchain's own exportedAxiomsExt olean entries; layout pinned by the repo toolchain and fail-loud cross-checked — see ASSUMPTIONS A1–A3 in the header
@[implemented_by decodeAxEntryImpl]
opaque decodeAxEntry (e : EnvExtensionEntry) : Name × Array Name -- ALLOW_AXIOM: safe-code interface to decodeAxEntryImpl (implemented_by); same single-cast surface — see ASSUMPTIONS A1–A3 in the header

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

-- ── Canonical statement serialization (pass-8 finding 2) ────────────────────
-- Injective, deterministic, hash-consed: every unique subterm becomes one
-- `#<idx>=<node>` line (children referenced by index, assigned in first-visit
-- order), so the stream size is proportional to the SHARED term graph, never
-- the expanded tree.  Name/level/string payloads are length-prefixed or
-- bracketed unambiguously.  See the header bullet for the two documented
-- identifications (binder names included; mdata payload elided).

partial def serName : Name → String
  | .anonymous => "A"
  | .str p s => s!"S({serName p},{s.length}:{s})"
  | .num p k => s!"N({serName p},{k})"

partial def serLevel : Level → String
  | .zero => "0"
  | .succ l => s!"s({serLevel l})"
  | .max a b => s!"m({serLevel a},{serLevel b})"
  | .imax a b => s!"i({serLevel a},{serLevel b})"
  | .param n => s!"p({serName n})"
  | .mvar _ => "MVAR"

def biChar : BinderInfo → String
  | .default => "d"
  | .implicit => "i"
  | .strictImplicit => "s"
  | .instImplicit => "c"

structure SerSt where
  idx  : Std.HashMap Expr Nat := {}
  out  : String := ""
  next : Nat := 0

/-- Serialize `e` into the state's node stream, returning its node index.
Applications are emitted n-ary (`getAppFn` + argument list) so recursion depth
follows term NESTING, not application-spine length. -/
partial def serE (e : Expr) : StateM SerSt Nat := do
  if let some i := (← get).idx[e]? then
    return i
  let line : String ← do
    match e with
    | .app .. => do
      let fi ← serE e.getAppFn
      let mut l := s!"a({fi}"
      for a in e.getAppArgs do
        let ai ← serE a
        l := l ++ s!",{ai}"
      pure (l ++ ")")
    | .bvar i => pure s!"B{i}"
    | .fvar _ => pure "FVAR"
    | .mvar _ => pure "MVAR"
    | .sort u => pure s!"U({serLevel u})"
    | .const n ls => pure s!"C({serName n},[{String.intercalate "," (ls.map serLevel)}])"
    | .lam bn bt b bi => do
      let ti ← serE bt
      let bo ← serE b
      pure s!"l({serName bn},{biChar bi},{ti},{bo})"
    | .forallE bn bt b bi => do
      let ti ← serE bt
      let bo ← serE b
      pure s!"f({serName bn},{biChar bi},{ti},{bo})"
    | .letE bn bt bv b nd => do
      let ti ← serE bt
      let vi ← serE bv
      let bo ← serE b
      pure s!"L({serName bn},{nd},{ti},{vi},{bo})"
    | .lit (.natVal k) => pure s!"n({k})"
    | .lit (.strVal s) => pure s!"t({s.length}:{s})"
    | .mdata _ b => do
      let bo ← serE b
      pure s!"d({bo})"
    | .proj tn i b => do
      let bo ← serE b
      pure s!"P({serName tn},{i},{bo})"
  let st ← get
  let i := st.next
  set { st with idx := st.idx.insert e i, next := i + 1,
                out := st.out ++ s!"#{i}={line}\n" }
  return i

/-- The canonical text a constant's digest is taken over: universe-parameter
list plus the hash-consed node stream of its (fully elaborated) type. -/
def canonicalOf (ci : ConstantInfo) : String :=
  let (ri, st) := (serE ci.type).run {}
  s!"LP[{String.intercalate "," (ci.levelParams.map serName)}]\n{st.out}ROOT={ri}\n"

/-- SHA-256 of `s` via coreutils `sha256sum` (ASSUMPTIONS A4). -/
def sha256 (s : String) : IO String := do
  let child ← IO.Process.spawn
    { cmd := "sha256sum", stdin := .piped, stdout := .piped, stderr := .null }
  let (h, child) ← child.takeStdin
  h.putStr s
  h.flush
  let out ← child.stdout.readToEnd
  let rc ← child.wait
  if rc != 0 then throw <| IO.userError s!"sha256sum exited with {rc}"
  let digest := (out.splitOn " ").headD ""
  unless digest.length == 64 && digest.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')) do
    throw <| IO.userError s!"sha256sum produced a malformed digest: {out}"
  return digest

/-- Strip a proof term's leading lambda binders and inert mdata — nothing else —
exposing the term that actually proves the (universally quantified) statement. -/
partial def stripLamsMData : Expr → Expr
  | .lam _ _ b _ => stripLamsMData b
  | .mdata _ b   => stripLamsMData b
  | e => e

/-- Field names of a structure, read off the constructor's binder telescope
(pure `ModuleData` — this is what replaced the pass-7 projectionFnInfoExt
decode).  `none` if the telescope is shorter than the constructor's declared
`numParams + numFields` (cannot happen for a kernel-accepted constructor;
treated as a violation by the caller, fail-closed). -/
def fieldNames (cv : ConstructorVal) : Option (List Name) :=
  go cv.type cv.numParams cv.numFields
where
  go : Expr → Nat → Nat → Option (List Name)
    | _, 0, 0 => some []
    | .forallE bn _ body _, 0, k+1 => (go body 0 k).map (bn :: ·)
    | .forallE _ _ body _, s+1, k => go body s k
    | _, _, _ => none

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
  /-- Projection names of target-module structures, derived from constructor
  binder telescopes (display-only classification input). -/
  projNames : NameSet := {}
  /-- Single-ctor inductives whose field derivation failed (violation). -/
  fieldFailures : Array Name := #[]

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
      -- Structure projections, cast-free (pass-8 finding 1): a single-ctor
      -- inductive's projections are `S.<field>` for the constructor's field
      -- binders (the constructor lives in the same module, already inserted).
      for (n, ci) in md.constNames.zip md.constants do
        if let .inductInfo iv := ci then
          if let [c] := iv.ctors then
            if let some (.ctorInfo cv) := acc.consts.find? c then
              match fieldNames cv with
              | some fs =>
                for f in fs do
                  acc := { acc with projNames := acc.projNames.insert (n.str f.toString) }
              | none =>
                acc := { acc with fieldFailures := acc.fieldFailures.push n }
    let deps := md.imports.toList.map (·.module) |>.filter (·.getRoot == `LerayHopf)
    load (deps ++ rest) acc

/-- Surface/child/internal classification — DISPLAY-ONLY since pass-7 (see
header): the gate pins every constant totally, so a mislabel cannot hide a
declaration; labels only keep the manifest and the 54-pin cross-check readable.
Rule order matches the pass-6/7 classifiers for label stability; projection
labels come from the cast-free constructor-telescope derivation, auxiliary
recursors (`casesOn`/`recOn`/…) from the generated-suffix lists below. -/
def classify (acc : Loaded) (n : Name) : String :=
  if n.isInternalDetail || n.isInternal then "internal"
  else if acc.projNames.contains n then "child"
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
  for f in acc.fieldFailures do
    IO.println s!"VIOLATION|field-derivation|{f}"
    nViol := nViol + 1
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
      -- Statement digest (pass-8 finding 2): SHA-256 over the canonical
      -- hash-consed serialization of levelParams + elaborated type.  A kernel
      -- type never contains free/meta variables; seeing one means the olean is
      -- not what a kernel accepted — fail closed.
      let digest ← match ci? with
        | some ci =>
          if ci.type.hasFVar || ci.type.hasMVar then
            IO.println s!"VIOLATION|open-statement|{n}"
            nViol := nViol + 1
          sha256 (canonicalOf ci)
        | none    => pure "-"
      IO.println s!"DECL|{classify acc n}|{n}|{kind}|{digest}|{axStr}"
      nDecl := nDecl + 1
  for (guard, seed) in depGuards do
    match acc.consts.find? guard with
    | some (.thmInfo v) =>
      -- Pass-8 finding 3: the seed must be the proof term's APPLICATION HEAD
      -- once the guard's own hypothesis binders (and inert mdata) are stripped —
      -- an unused `let` or a dead branch mentioning the seed does not pass.
      if (stripLamsMData v.value).getAppFn.constName? == some seed then
        IO.println s!"DEPGUARD|{guard}|{seed}|head"
        nDep := nDep + 1
      else
        IO.println s!"VIOLATION|depguard-head-not-seed|{guard}|{seed}"
        nViol := nViol + 1
    | _ =>
      IO.println s!"VIOLATION|depguard-not-a-theorem|{guard}"
      nViol := nViol + 1
  IO.println s!"SCRATCH-MANIFEST-END|{nDecl}|{nDep}|{if nViol == 0 then "OK" else "FAIL"}"
  if nViol != 0 then
    throw <| IO.userError s!"scratch static reader: {nViol} violation(s) — see VIOLATION lines"

#eval main'
