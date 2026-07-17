/-
# ExtractNotes

Zero-dependency metadata extractor for the LerayHopf library.

This executable imports the *already-built* `LerayHopf` and `LerayHopf.Experimental` oleans
(it deliberately does NOT `import` either at the top of this file, so the exe compiles
against Lean core only and never drags the library/mathlib into its own build), reflects
over the resulting `Environment`, and emits one JSON record per LerayHopf declaration.
Both the release surface and the `Experimental` opt-in (the incomplete Bochner time-layer
modules split out by issue #147) are covered, so the annotated corpus does not silently
lose those declarations on a repin (issue #166).

Run it under the project's Lean search path so the LerayHopf/mathlib oleans are found.
The JSON array goes to stdout by default, or to `--out <path>`; the human-readable
report (kind summary + dependency/identity audit) always goes to stderr, so stdout
stays pipe-clean:

    lake exe extract_notes                      -- JSON to stdout
    lake exe extract_notes -- --out notes.json  -- JSON to notes.json

## Record schema

Each record has: `id`, `name`, `private`, `kind`, `signature`, `doc`, `file`,
`startLine`, `endLine`, `deps`.

* `id` is the *real internal name* string — unique by construction, and the key the
  `deps` edges point at. For a public declaration `id == name`.
* `name` is the *display user-name*. It can collide across modules for `private`
  helpers (Lean strips the module-specific part of a private name), so `name` is NOT a
  key; use `id` (plus `file`) to disambiguate.
* `deps` are project-internal edges (constants referenced in the declaration's type and
  value), each normalized to an emitted record `id`: a field projection or constructor
  of a kept structure is remapped to that structure's `id`; auxiliaries and range-less
  synthetics are dropped and tallied in the stderr audit. Every emitted `deps` entry
  resolves to exactly one record `id` (asserted before write). The run exits nonzero if
  a dep is unresolved for an unknown reason, an `id` is duplicated, or a dep dangles.

Design constraints (spike S0, tracking uda-lab/lean-pde-notes#2):
* `import Lean` ONLY.
* `loadExts := true` on import — required so declaration ranges, docstrings, instance,
  reducibility and structure env-extensions carry their imported state (see the note on
  `importModules` in `Lean/Environment.lean`). This in turn needs
  `enableInitializersExecution`, hence `unsafe def main`.

## Assumptions (this file only)

* `main` is `unsafe`. `Lean.enableInitializersExecution` — a prerequisite of
  `importModules (loadExts := true)`, enforced at runtime — is itself `unsafe`, so the
  executable entry point must be `unsafe`. This is confined to the standalone extractor:
  `ExtractNotes` is not imported by any `LerayHopf` module, so it appears in no theorem's
  `#print axioms` profile and does not widen the project's kernel trust base. The library
  and both `exists_lerayHopf_*` capstones remain kernel-only. (The `-- ALLOW_AXIOM:`
  marker on the `unsafe def main` line satisfies the No-silent-axiom grep guard.)
-/
import Lean

open Lean Meta

namespace ExtractNotes

/-- Leftmost (root) string component of a `Name`, e.g. `LerayHopf.Core.Foo` ↦ "LerayHopf". -/
partial def rootString : Name → String
  | .str .anonymous s => s
  | .str p _          => rootString p
  | .num p _          => rootString p
  | .anonymous        => ""

/-- Is this *module* name part of the LerayHopf library? -/
def isLerayHopfModule (m : Name) : Bool := rootString m == "LerayHopf"

/-- Module name ↦ source path, e.g. `LerayHopf.Core` ↦ "LerayHopf/Core.lean". -/
def moduleToFile (m : Name) : String :=
  "/".intercalate (m.components.map (·.toString)) ++ ".lean"

/-- Defining module of `declName`, if it is an imported constant. -/
def moduleOf? (env : Environment) (declName : Name) : Option Name :=
  match env.getModuleIdxFor? declName with
  | some idx => env.header.moduleNames[idx.toNat]?
  | none     => none

/-- Last string component of a `Name`. -/
def lastComp : Name → String
  | .str _ s => s
  | _        => ""

/-- Suffixes of auto-generated structural lemmas that are not part of the human API
    (`Foo.mk.injEq`, `Foo.sizeOf_spec`, `Foo.noConfusionType`, …) and are not caught by
    `isAuxRecursor`/`isNoConfusion`/`isInternalDetail`. A suffix match alone never drops a
    declaration — see `suffixCorroboratedNoise`. -/
def autoLemmaSuffixes : List String :=
  ["injEq", "inj", "sizeOf_spec", "sizeOf_eq", "eq_def", "eq_unfold", "toCtorIdx", "ofNat",
   "noConfusion", "noConfusionType"]

/-- Does some strict prefix of `name` name an inductive/structure? Used to corroborate
    that a suffix-matching declaration is a generated structural companion rather than a
    hand-written declaration that happens to share a suffix. -/
partial def parentIsInductive (env : Environment) : Name → Bool
  | .str p _ =>
      (match env.find? p with | some (.inductInfo _) => true | _ => false)
        || parentIsInductive env p
  | .num p _ => parentIsInductive env p
  | .anonymous => false

/-- Metadata-confirmed generated / internal noise, independent of source range: a noisy
    `ConstantInfo` kind, an internal display name, a field projection, or an auxiliary
    recursor / `noConfusion`. These are never human API, range or no range. -/
def isHardNoise (env : Environment) (name : Name) (userName : Name) (ci : ConstantInfo) : Bool :=
  let kindNoise :=
    match ci with
    | .ctorInfo _ | .recInfo _ | .quotInfo _ => true
    | _ => false
  kindNoise
    || userName.isInternalDetail
    || env.isProjectionFn name
    || isAuxRecursor env name         -- .casesOn/.recOn/.brecOn/.below/.binductionOn/…
    || isNoConfusion env name         -- .noConfusion (ext-marked)

/-- A generated structural lemma recognized by an `autoLemmaSuffixes` suffix, corroborated
    by Lean metadata that it is generated (a strict prefix names an inductive/structure).
    The corroboration is required so a range-bearing hand-written declaration is NEVER
    dropped by suffix match alone (Codex round-2 medium). -/
def suffixCorroboratedNoise (env : Environment) (name : Name) : Bool :=
  autoLemmaSuffixes.contains (lastComp name) && parentIsInductive env name

/-- Should this constant be dropped as auto-generated / internal noise? -/
def isNoise (env : Environment) (name : Name) (userName : Name) (ci : ConstantInfo) : Bool :=
  isHardNoise env name userName ci || suffixCorroboratedNoise env name

/-- Coarse declaration kind used by the notes UI. Instance takes priority over the
    `ConstantInfo` shape because a `Prop`-valued instance is stored as a `thmInfo`. -/
def classifyKind (env : Environment) (name : Name) (ci : ConstantInfo) : MetaM String := do
  if isStructure env name then return "structure"
  if (← Meta.isInstance name) then return "instance"
  match ci with
  | .thmInfo _    => return "theorem"
  | .inductInfo _ => return "inductive"
  | .axiomInfo _  => return "axiom"
  | .opaqueInfo _ => return "def"
  | .defnInfo _   => return (if (← isReducible name) then "abbrev" else "def")
  | _             => return "other"

/-- Structural parent (owning inductive/structure) of an auto-generated companion `d`
    that is itself dropped from the record set: a field projection's or constructor's
    inductive. Returns `none` for companions we do not remap (recursors, noConfusion,
    equation lemmas, …); those are dropped from `deps` with an audited reason. -/
def structuralParent? (env : Environment) (d : Name) : Option Name :=
  let ctorInduct (cn : Name) : Option Name :=
    match env.find? cn with
    | some (.ctorInfo cval) => some cval.induct
    | _                     => none
  if env.isProjectionFn d then
    (env.getProjectionFnInfo? d).bind (fun info => ctorInduct info.ctorName)
  else
    ctorInduct d

/-- IDs (real internal-name strings) of the declarations actually emitted as records. -/
abbrev KeptIds := Std.HashSet String

/-- Why a dependency edge did not resolve to an emitted record. Explicitly typed so the
    run's failure discipline is not stringly: only `syntheticConfirmed` and `rangeLess`
    are nonfatal (audited, exit 0); every other category — a projection/constructor whose
    parent structure was not emitted, or an unclassifiable constant — is fatal (exit ≠ 0),
    because it signals a hole in the record set rather than an expected drop. -/
inductive DepDrop where
  | syntheticConfirmed   -- metadata-confirmed generated companion (isNoise)
  | rangeLess            -- a real declaration that carries no source range
  | missingParent        -- projection/constructor whose parent structure is not emitted
  | unknown              -- a normal declaration absent from `keptIds` (emission bug)

def DepDrop.reason : DepDrop → String
  | .syntheticConfirmed => "synthetic-confirmed"
  | .rangeLess          => "range-less"
  | .missingParent      => "projection-remap-missing-parent"
  | .unknown            => "unknown"

/-- Only confirmed-synthetic and range-less drops are tolerated; all others fail the run. -/
def DepDrop.fatal : DepDrop → Bool
  | .syntheticConfirmed | .rangeLess => false
  | .missingParent | .unknown        => true

/-- Resolve one project-internal dependency `d` (a real constant name) to an emitted
    record id, or to a typed drop. A projection/constructor of a kept structure is
    remapped to that structure's id (the field lives inside the structure node); a dep
    that is itself a kept record is kept; everything else is dropped with a typed reason. -/
def resolveDep (env : Environment) (keptIds : KeptIds) (d : Name) :
    MetaM (Except DepDrop String) := do
  let did := d.toString
  if keptIds.contains did then
    return .ok did
  match structuralParent? env d with
  | some p =>
      let pid := p.toString
      if keptIds.contains pid then return .ok pid
      else return .error .missingParent
  | none =>
      let du := (privateToUserName? d).getD d
      match env.find? d with
      | some ci =>
          if isNoise env d du ci then return .error .syntheticConfirmed
          else if (← findDeclarationRanges? d).isNone then return .error .rangeLess
          else return .error .unknown
      | none => return .error .unknown

/-- Normalized project-internal dependency ids of `ci` (referenced in type and value):
    resolved against `keptIds`, self excluded, deduplicated, sorted. Also returns the
    typed drops for edges that did not resolve to a record. -/
def depsOf (env : Environment) (name : Name) (ci : ConstantInfo) (keptIds : KeptIds) :
    MetaM (Array String × Array DepDrop) := do
  let used := ci.type.getUsedConstants ++ (ci.value?.map Expr.getUsedConstants).getD #[]
  let self := name.toString
  let mut ids : Std.HashSet String := {}
  let mut drops : Array DepDrop := #[]
  for d in used do
    match moduleOf? env d with
    | some m =>
        -- Filter on the *display* name's internal-detail status: this keeps genuine
        -- declarations — public and `private` (whose real names are `isInternalDetail`
        -- but whose display names are not) — while dropping every auxiliary of either
        -- (`_proof_`, `.eq_*`, `match_*`, private equation lemmas, …) before the audit.
        let du := (privateToUserName? d).getD d
        if isLerayHopfModule m && !du.isInternalDetail then
          match ← resolveDep env keptIds d with
          | .ok id    => if id != self then ids := ids.insert id
          | .error dr => drops := drops.push dr
    | none => pure ()
  return (ids.toArray.qsort (· < ·), drops)

/-- Build one JSON record for a single (kept) declaration. Returns its kind, the JSON,
    its resolved dep ids, and the audit reasons for dropped edges.
    `id` is the real internal name (unique by construction); `name` is the display
    user-name (may collide across modules for private helpers — see the validation in
    `extractAll`). Deps reference `id`s. `ranges` is the source range located upstream. -/
def recordOf (name : Name) (ci : ConstantInfo) (ranges : DeclarationRanges)
    (keptIds : KeptIds) : MetaM (String × Json × Array String × Array DepDrop) := do
  let env ← getEnv
  let userName := (privateToUserName? name).getD name
  let isPriv := (privateToUserName? name).isSome
  let kind ← classifyKind env name ci
  let sig ←
    try
      let fmt ← Meta.ppExpr ci.type
      pure (toString fmt)
    catch _ => pure "<pp-error>"
  let doc ← findDocString? env name
  let fileStr := (moduleOf? env name).map moduleToFile |>.getD ""
  let (deps, drops) ← depsOf env name ci keptIds
  let json := Json.mkObj [
    ("id",        Json.str name.toString),
    ("name",      Json.str userName.toString),
    ("private",   Json.bool isPriv),
    ("kind",      Json.str kind),
    ("signature", Json.str sig),
    ("doc",       match doc with | some d => Json.str d | none => Json.null),
    ("file",      Json.str fileStr),
    ("startLine", toJson ranges.range.pos.line),
    ("endLine",   toJson ranges.range.endPos.line),
    ("deps",      Json.arr (deps.map Json.str))
  ]
  return (kind, json, deps, drops)

/-- Format a `reason → count` audit map as `total (r1: n1; r2: n2)`. -/
def fmtAudit (m : Std.HashMap String Nat) : String :=
  let total := m.fold (fun acc _ n => acc + n) 0
  let parts := (m.toList.toArray.qsort (fun a b => a.1 < b.1)).map (fun (r, n) => s!"{r}: {n}")
  s!"{total} (" ++ "; ".intercalate parts.toList ++ ")"

/-- Walk the environment, keep LerayHopf declarations, emit records + a stderr report.
    Two passes: first fix the set of emitted record ids, then build records whose `deps`
    are normalized against that set. Returns `(json, report, ok)`; `ok = false` (nonzero
    exit) iff any dep drop is fatal (`missingParent`/`unknown`), a record id is duplicated,
    or an emitted dep does not point at a record. -/
def extractAll : MetaM (Json × String × Bool) := do
  let env ← getEnv
  -- Pure pass: gather (name, ConstantInfo) for constants defined in LerayHopf modules.
  let targets : Array (Name × ConstantInfo) :=
    env.constants.fold (init := #[]) fun acc name ci =>
      match moduleOf? env name with
      | some m => if isLerayHopfModule m then acc.push (name, ci) else acc
      | none   => acc
  let targets := targets.qsort (fun a b => a.1.toString < b.1.toString)
  -- Pass 1: fix the emitted-record id set (real names, unique by construction).
  let mut kept : Array (Name × ConstantInfo × DeclarationRanges) := #[]
  let mut keptIds : KeptIds := {}
  for (name, ci) in targets do
    let userName := (privateToUserName? name).getD name
    if isNoise env name userName ci then continue
    -- Drop synthetic decls with no source range (`.ctorIdx`, `.congr_simp`, …):
    -- the notes UI needs a `file:line` to link to.
    let some ranges ← findDeclarationRanges? name | continue
    kept := kept.push (name, ci, ranges)
    keptIds := keptIds.insert name.toString
  -- Pass 2: build records with normalized deps + collect audits.
  let mut records : Array Json := #[]
  let mut counts : Std.HashMap String Nat := {}
  let mut unresolved : Std.HashMap String Nat := {}
  let mut nameCounts : Std.HashMap String Nat := {}
  let mut idCounts : Std.HashMap String Nat := {}
  let mut dangling := 0
  let mut fatalDrops := 0
  for (name, ci, ranges) in kept do
    let (k, json, deps, drops) ← recordOf name ci ranges keptIds
    records := records.push json
    counts := counts.insert k (counts.getD k 0 + 1)
    for dr in drops do
      unresolved := unresolved.insert dr.reason (unresolved.getD dr.reason 0 + 1)
      if dr.fatal then fatalDrops := fatalDrops + 1
    for id in deps do if !keptIds.contains id then dangling := dangling + 1
    let disp := ((privateToUserName? name).getD name).toString
    nameCounts := nameCounts.insert disp (nameCounts.getD disp 0 + 1)
    idCounts := idCounts.insert name.toString (idCounts.getD name.toString 0 + 1)
  -- Audits. Nonfatal drops (synthetic-confirmed, range-less) are tolerated; every fatal
  -- drop (missing parent, unknown), a duplicate id, or a dangling dep fails the run.
  let dupIds := idCounts.toList.filter (fun (_, n) => n > 1)
  let dupNameGroups := nameCounts.toList.filter (fun (_, n) => n > 1)
  let dupNameDecls := dupNameGroups.foldl (fun acc (_, n) => acc + n) 0
  let ok := fatalDrops == 0 && dupIds.isEmpty && dangling == 0
  let kindLines := (counts.toList.toArray.qsort (fun a b => a.1 < b.1)).map
    (fun (k, n) => s!"  {k}: {n}")
  let mut report := s!"kept {records.size} declarations\n" ++ "\n".intercalate kindLines.toList
  report := report ++ s!"\nunresolved_deps: {fmtAudit unresolved}"
  report := report ++ s!"\nfatal_dep_drops: {fatalDrops}"
  report := report ++
    s!"\nduplicate_display_names: {dupNameGroups.length} groups ({dupNameDecls} decls)"
  report := report ++ s!"\nduplicate_ids: {dupIds.length}"
  report := report ++ s!"\ndangling_deps: {dangling}"
  unless ok do
    report := report ++ s!"\nFAIL: fatal_dep_drops={fatalDrops} duplicate_ids={dupIds.length} \
      dangling_deps={dangling}"
  return (Json.arr records, report, ok)

/-- `none` = write to stdout; `some p` = write to file `p`. -/
def parseArgs : List String → Except String (Option String)
  | []           => .ok none
  | ["--out", p] => .ok (some p)
  | [s]          =>
      if s.startsWith "--out=" then .ok (some (s.drop 6).toString)  -- 6 = "--out=".length
      else .error s!"unknown argument: {s}"
  | args         => .error s!"unexpected arguments: {" ".intercalate args}"

def usage : String :=
  "usage: extract_notes [--out <path>]\n\n" ++
  "Emits one JSON record per public LerayHopf declaration.\n" ++
  "  --out <path>   write the JSON array to <path> (default: stdout)\n" ++
  "The kind summary is always written to stderr.\n" ++
  "Run under the library search path, e.g. `lake exe extract_notes -- --out notes.json`."

end ExtractNotes

open ExtractNotes in
unsafe def main (rawArgs : List String) : IO UInt32 := do  -- ALLOW_AXIOM: exe-only `unsafe`; `enableInitializersExecution` (required by `importModules (loadExts := true)`) is unsafe. Not imported by any LerayHopf theorem — kernel trust base unchanged; see Assumptions above.
  -- `lake exe extract_notes -- --out p` forwards the bare `--` separator through to
  -- the program on this toolchain; drop it so the documented invocation parses.
  let args := rawArgs.filter (· != "--")
  if args.contains "--help" || args.contains "-h" then
    IO.println usage
    return 0
  let out? ←
    match parseArgs args with
    | .ok v    => pure v
    | .error e =>
        IO.eprintln s!"extract_notes: {e}\n{usage}"
        return 1
  Lean.enableInitializersExecution
  Lean.initSearchPath (← Lean.findSysroot)
  -- Import both the release surface and the Experimental opt-in (issue #147 split) so the
  -- Bochner time-layer modules gathered behind `LerayHopf.Experimental` are not silently
  -- dropped from the extracted corpus (issue #166).
  let env ← Lean.importModules #[{ module := `LerayHopf }, { module := `LerayHopf.Experimental }]
    {} (trustLevel := 1024) (loadExts := true)
  let coreCtx : Core.Context := {
    fileName := "<extract_notes>"
    fileMap := FileMap.ofString ""
    maxHeartbeats := 0
  }
  let coreState : Core.State := { env := env }
  let ((jsonArr, report, ok), _) ← (extractAll.run').toIO coreCtx coreState
  -- Gate all artifact output on validation: on failure emit only the report and exit 1,
  -- never a partial/invalid artifact. On success write atomically (temp + rename) so a
  -- reader never observes a half-written `--out` file.
  if ok then
    match out? with
    | some path =>
        let tmp := path ++ ".tmp"
        IO.FS.writeFile tmp jsonArr.pretty
        IO.FS.rename tmp path
        IO.eprintln report
        IO.eprintln s!"wrote {path}"
    | none =>
        IO.println jsonArr.pretty
        IO.eprintln report
    return 0
  else
    IO.eprintln report
    return 1
