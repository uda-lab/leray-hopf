/-
# ExtractNotes

Zero-dependency metadata extractor for the LerayHopf library.

This executable imports the *already-built* `LerayHopf` oleans (it deliberately does
NOT `import LerayHopf`, so the exe compiles against Lean core only and never drags the
library/mathlib into its own build), reflects over the resulting `Environment`, and
emits one JSON record per public LerayHopf declaration.

Run it under the project's Lean search path so the LerayHopf/mathlib oleans are found.
The JSON array goes to stdout by default, or to `--out <path>`; the human-readable
kind summary always goes to stderr, so stdout stays pipe-clean:

    lake exe extract_notes                      -- JSON to stdout
    lake exe extract_notes -- --out notes.json  -- JSON to notes.json

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
    (`Foo.mk.injEq`, `Foo.sizeOf_spec`, `Foo.eq_def`, …) and are not caught by
    `isAuxRecursor`/`isNoConfusion`/`isInternalDetail`. -/
def autoLemmaSuffixes : List String :=
  ["injEq", "inj", "sizeOf_spec", "sizeOf_eq", "eq_def", "eq_unfold", "toCtorIdx", "ofNat",
   "noConfusion", "noConfusionType"]

/-- Should this constant be dropped as auto-generated / internal noise? -/
def isNoise (env : Environment) (name : Name) (userName : Name) (ci : ConstantInfo) : Bool :=
  let kindNoise :=
    match ci with
    | .ctorInfo _ | .recInfo _ | .quotInfo _ => true
    | _ => false
  kindNoise
    || userName.isInternalDetail
    || env.isProjectionFn name
    || isAuxRecursor env name         -- .casesOn/.recOn/.brecOn/.below/.binductionOn/…
    || isNoConfusion env name         -- .noConfusion/.noConfusionType
    || autoLemmaSuffixes.contains (lastComp name)

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

/-- Project-internal constants referenced in `ci`'s type and value, mapped to user
    names, deduplicated, self excluded, sorted. -/
def depsOf (env : Environment) (userName : Name) (ci : ConstantInfo) : Array String := Id.run do
  let used := ci.type.getUsedConstants ++ (ci.value?.map Expr.getUsedConstants).getD #[]
  let mut seen : Std.HashSet String := {}
  for d in used do
    match moduleOf? env d with
    | some m =>
        if isLerayHopfModule m && !d.isInternalDetail then
          let du := (privateToUserName? d).getD d
          if du != userName then seen := seen.insert du.toString
    | none => pure ()
  seen.toArray.qsort (· < ·)

/-- Build one JSON record for a single (kept) declaration, paired with its kind.
    `ranges` is the source range located by the caller; range-less synthetic decls
    (`.ctorIdx`, `.congr_simp`, …) are dropped upstream, so every record carries a
    real `file:line` the notes UI can link to. -/
def recordOf (name : Name) (ci : ConstantInfo) (ranges : DeclarationRanges) :
    MetaM (String × Json) := do
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
  return (kind, Json.mkObj [
    ("name",      Json.str userName.toString),
    ("private",   Json.bool isPriv),
    ("kind",      Json.str kind),
    ("signature", Json.str sig),
    ("doc",       match doc with | some d => Json.str d | none => Json.null),
    ("file",      Json.str fileStr),
    ("startLine", toJson ranges.range.pos.line),
    ("endLine",   toJson ranges.range.endPos.line),
    ("deps",      Json.arr ((depsOf env userName ci).map Json.str))
  ])

/-- Walk the environment, keep LerayHopf declarations, emit records + a kind summary. -/
def extractAll : MetaM (Json × String) := do
  let env ← getEnv
  -- Pure pass: gather (name, ConstantInfo) for constants defined in LerayHopf modules.
  let targets : Array (Name × ConstantInfo) :=
    env.constants.fold (init := #[]) fun acc name ci =>
      match moduleOf? env name with
      | some m => if isLerayHopfModule m then acc.push (name, ci) else acc
      | none   => acc
  let targets := targets.qsort (fun a b => a.1.toString < b.1.toString)
  let mut records : Array Json := #[]
  let mut counts : Std.HashMap String Nat := {}
  for (name, ci) in targets do
    let userName := (privateToUserName? name).getD name
    if isNoise env name userName ci then continue
    -- Drop synthetic decls with no source range (`.ctorIdx`, `.congr_simp`, …):
    -- the notes UI needs a `file:line` to link to.
    let some ranges ← findDeclarationRanges? name | continue
    let (k, rec_) ← recordOf name ci ranges
    records := records.push rec_
    counts := counts.insert k (counts.getD k 0 + 1)
  let summaryLines := counts.toList.toArray.qsort (fun a b => a.1 < b.1)
    |>.map (fun (k, n) => s!"  {k}: {n}")
  let summary := s!"kept {records.size} declarations\n" ++ "\n".intercalate summaryLines.toList
  return (Json.arr records, summary)

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
  let env ← Lean.importModules #[{ module := `LerayHopf }] {} (trustLevel := 1024)
    (loadExts := true)
  let coreCtx : Core.Context := {
    fileName := "<extract_notes>"
    fileMap := FileMap.ofString ""
    maxHeartbeats := 0
  }
  let coreState : Core.State := { env := env }
  let ((jsonArr, summary), _) ← (extractAll.run').toIO coreCtx coreState
  match out? with
  | some path =>
      IO.FS.writeFile path jsonArr.pretty
      IO.eprintln summary
      IO.eprintln s!"wrote {path}"
  | none =>
      IO.println jsonArr.pretty
      IO.eprintln summary
  return 0
