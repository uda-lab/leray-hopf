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
--      by (i) an EXACT PER-MODULE BIJECTION against `constNames`, enforced in
--      `load` before any manifest line is emitted (pass-9 finding 3): duplicate
--      entry names, entry names that are not constants of the module, constants
--      without an entry, and cardinality mismatches are each their own
--      VIOLATION — a duplicate cannot silently overwrite a closure and an extra
--      entry cannot be silently ignored; (ii) the kernel-trio whitelist on
--      every decoded axiom name; and (iii) the total byte-diff against the
--      frozen manifest.  A layout change under a future toolchain bump yields
--      garbage `Name`s and trips (i)–(iii); it cannot decode to
--      plausible-but-wrong closures.
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
--     in deterministic first-visit order.  "Unique" means EXACT STRUCTURAL
--     equality: the memoization is keyed on `ExprStructEq` (`Expr.equal`), not
--     on `BEq Expr` = `Expr.eqv` alpha-equivalence (pass-9 finding 1 — under
--     eqv keys a repeated alpha-equivalent subterm reused its first
--     occurrence's index, so a binder rename/annotation change in the later
--     occurrence never reached the stream; the GateFixture alpha/binderInfo
--     pairs assert the discrimination per run, see FIXTURE-DIGEST below).  The
--     stream determines the term, so equal digests mean equal serializations,
--     i.e. equal types (two caveats, both fail-closed or inert: binder NAMES
--     are included, so an alpha-renaming changes the digest and surfaces in
--     review as a manifest edit; `mdata` PAYLOADS are elided — node presence is
--     kept — matching the kernel's treatment of mdata as inert annotation).
--     Collision resistance is SHA-256's.  Freezing these digests in
--     scratch-manifest.expected freezes every STATEMENT, not just every name:
--     editing any type re-digests and fails the byte-diff.  (Sharing note: the
--     serialization is emitted per constant with a fresh index table;
--     hash-consing keeps it proportional to unique subterms — the expanded
--     trees of these statements measure in the gigabytes and are never
--     materialized.)
--   * `ConstantInfo.value` of EVERY production-coupling probe (pass-7
--     finding 3; head semantics per pass-8 finding 3; extended from the two
--     free-κ guards to the full 11-pin table per pass-9 finding 2): each pin
--     names the constant that must be the probe's proof-term APPLICATION HEAD
--     after stripping its own binders and inert mdata — the actual production
--     declarations for the exact-shape probes, the SEEDS for the id-coherence
--     and free-κ probes (the production/seed distinction is part of the pin:
--     a probe re-proved from the wrong side fails even with identical
--     statement digest and axiom closure), the `mk` constructors for the
--     field-by-field bridges — plus one structural `exists-destruct` pin for
--     the destructuring probe: its proof term must BE an `Exists.casesOn`
--     application whose SCRUTINEE is headed by the pinned production
--     existential, so a dead mention cannot satisfy the pin (see
--     `depGuards`).  At P2′ the sanctioned (δ)
--     re-point (campaign doc §6 clause 6) rewrites the pin table in the SAME
--     reviewed diff as the probe changes, together with the checker's DEPGUARD
--     lines and the expected manifest — the gate is deliberately broken by a
--     re-point that forgets any of them.
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
--   FIXTURE-DIGEST|<label>|eqv-equal-canonical-distinct   (before START; one per
--                                                      serializer-discrimination
--                                                      fixture pair)
--   SCRATCH-MANIFEST-START
--   DECL|<class>|<name>|<kind>|<sha256|- >|<axioms>   (one line per constant of a
--                                                      target module; digest `-`
--                                                      only for codegen extras;
--                                                      <axioms> is a comma-joined
--                                                      list or `-` if empty)
--   DEPGUARD|<decl>|<required>|<head|exists-destruct> (one line per proof-value
--                                                      pin, 8-entry table after
--                                                      the P2′ (δ) re-point)
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

/-- PROOF-VALUE PINS (round-7 finding 3, head-check per round-8 finding 3,
extended to EVERY production-coupling probe per round-9 finding 2): each entry
is `(declaration, required constant, mode)`.

Mode `"head"`: the declaration's proof/definition term — its own hypothesis
binders and inert mdata stripped — must have the required constant as its
APPLICATION HEAD.  This encodes the module doctrine literally: the exact-shape
probes are BARE APPLICATIONS of the named production declarations, the
id-coherence and free-κ probes are bare applications of the SEEDS (which is
their point — the distinction production-head vs seed-head is part of the pin,
so a probe silently re-proved from the wrong side fails even with an identical
statement digest and axiom closure), and the two bridges are field-by-field
`mk` constructions.

Mode `"exists-destruct"` (round-10 finding; replaces the pass-9 `uses` mode,
whose bare `getUsedConstants` reference would also have accepted a DEAD
mention — an unused `let` or dead branch — while the result was derived from
some other proof): the stripped proof term must BE an `Exists.casesOn`
application whose SCRUTINEE (the major premise) is itself headed by the
required constant, so the pinned existential is the value the proof actually
destructures; the direct-reference check is retained as a secondary guard.
The mode machinery is retained but currently has ZERO uses: it was sanctioned
for exactly one pin, `r3LimitPassagePin_production_source` (it destructured the
production existential via `obtain`/`exact`, so its stripped head was
`Exists.casesOn`, not the production source), and that pin was DELETED at the
P2′ re-point (§6 clause 6 (α)) along with the κ-less production package it
bridged.  The present table is all-`head` (see `depGuards` below).  Any new
`exists-destruct` pin needs a documented reason like that one did.

At P2′ the sanctioned (δ) re-point (campaign doc §6 clause 6) rewrites this
table in the SAME reviewed diff as the probe changes: the three probes deleted
with the mirror lose their pins, the free-κ guards' heads swap to the
κ-threaded production declarations, and the exact-shape probes keep their
production heads (their proofs gain `id strictMono_id` arguments only). -/
def depGuards : List (Name × Name × String) := [
  (`LerayHopf.Scratch212.r3LimitPassage_strengthened_production_coupling,
   `LerayHopf.galerkin_limit_passage_R3, "head"),
  (`LerayHopf.Scratch212.r3Production_diag_ae_subseq_exact_shape,
   `LerayHopf.diag_ae_subseq, "head"),
  (`LerayHopf.Scratch212.r3Production_u_lim_aestronglyMeasurable_exact_shape,
   `LerayHopf.u_lim_aestronglyMeasurable, "head"),
  (`LerayHopf.Scratch212.r3Production_galerkinSpaceTimeExtraction_exact_shape,
   `LerayHopf.galerkinSpaceTimeExtraction_R3, "head"),
  (`LerayHopf.Scratch212.diag_ae_subseq_seeded_id_recovers_production,
   `LerayHopf.Scratch212.diag_ae_subseq_seeded, "head"),
  (`LerayHopf.Scratch212.spacetime_extraction_seeded_id_recovers_production,
   `LerayHopf.Scratch212.spacetime_extraction_seeded, "head"),
  (`LerayHopf.Scratch212.r3Production_diag_ae_subseq_kappa_coupling,
   `LerayHopf.diag_ae_subseq, "head"),
  (`LerayHopf.Scratch212.r3Production_spacetime_extraction_kappa_coupling,
   `LerayHopf.galerkinSpaceTimeExtraction_R3, "head")]

/-- The collision-fixture module (NOT a gate target): loaded so the serializer
discrimination fixtures (pass-9 finding 1) can be digest-checked per run. -/
def fixtureModule : Name := `LerayHopf.Scratch.GateFixture

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
  /-- Memoization keyed on EXACT STRUCTURAL equality (`ExprStructEq` wraps
  `Expr.equal`), NOT on `BEq Expr` (= `Expr.eqv`, alpha-equivalence): pass-9
  finding 1 — under eqv keys a repeated alpha-equivalent subterm reused the
  index of its first occurrence, so a binder rename/annotation change in the
  later occurrence never reached the stream, and two distinct types could share
  a digest.  With structural keys, only byte-identical subterms share a node
  (the `GateFixture` alpha/binderInfo pairs assert this discrimination per run). -/
  idx  : Std.HashMap ExprStructEq Nat := {}
  out  : String := ""
  next : Nat := 0

/-- Serialize `e` into the state's node stream, returning its node index.
Applications are emitted n-ary (`getAppFn` + argument list) so recursion depth
follows term NESTING, not application-spine length. -/
partial def serE (e : Expr) : StateM SerSt Nat := do
  if let some i := (← get).idx[ExprStructEq.mk e]? then
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
  set { st with idx := st.idx.insert (ExprStructEq.mk e) i, next := i + 1,
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

/-- Strip ONLY inert mdata (no binders).  Used on the scrutinee of an
`exists-destruct` pin: a proof of an `Exists` proposition is never a lambda,
so stripping binders there would be wrong — only kernel-inert metadata may
stand between the argument position and the application head. -/
partial def stripMData : Expr → Expr
  | .mdata _ b => stripMData b
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
  /-- Per-module axiom-entry bijection failures (violation; pass-9 finding 3):
  formatted `rule|module|detail` for duplicate/unknown/missing/count defects. -/
  axEntryFailures : Array String := #[]

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
      -- Axiom entries with EXACT PER-MODULE BIJECTION enforcement (pass-9
      -- finding 3 — A2's fail-loud promise, now actually checked before any
      -- manifest line is emitted): entry names must be pairwise distinct,
      -- every entry name must be a constant of THIS module, every constant of
      -- this module must have an entry from this module, and the cardinalities
      -- must match.  A duplicate can no longer silently overwrite a closure;
      -- an unknown or cross-module entry can no longer be silently ignored.
      let mut eset : NameSet := {}
      let mut nEntries : Nat := 0
      for (extName, es) in md.entries do
        if extName == axExtName then
          for e in es do
            let (n, axs) := decodeAxEntry e
            nEntries := nEntries + 1
            if eset.contains n then
              acc := { acc with axEntryFailures :=
                acc.axEntryFailures.push s!"axentry-duplicate|{m}|{n}" }
            eset := eset.insert n
            acc := { acc with axioms := acc.axioms.insert n axs }
      let cset : NameSet := md.constNames.foldl (·.insert ·) {}
      for n in eset.toList do
        if !cset.contains n then
          acc := { acc with axEntryFailures :=
            acc.axEntryFailures.push s!"axentry-unknown|{m}|{n}" }
      for n in md.constNames do
        if !eset.contains n then
          acc := { acc with axEntryFailures :=
            acc.axEntryFailures.push s!"axentry-missing|{m}|{n}" }
      if nEntries != md.constNames.size then
        acc := { acc with axEntryFailures :=
          acc.axEntryFailures.push s!"axentry-count|{m}|{nEntries}≠{md.constNames.size}" }
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
  let acc ← load (scratchTargets.toList ++ [fixtureModule]) {}
  let mut nDecl := 0
  let mut nViol := 0
  let mut nDep  := 0
  -- SERIALIZER DISCRIMINATION FIXTURES (pass-9 finding 1), asserted BEFORE the
  -- manifest block: each GateFixture pair is alpha-equivalent (`Expr.eqv` true —
  -- the retired eqv-keyed memoization would have collapsed them to one stream)
  -- but must produce DISTINCT canonical digests under structural keying.
  for (label, na, nb) in [
      ("alpha-binder-name", `LerayHopf.ScratchFixture.alphaSame,
       `LerayHopf.ScratchFixture.alphaRenamed),
      ("binder-info", `LerayHopf.ScratchFixture.binfoBase,
       `LerayHopf.ScratchFixture.binfoVariant)] do
    match acc.consts.find? na, acc.consts.find? nb with
    | some ca, some cb =>
      if !(Expr.eqv ca.type cb.type) then
        IO.println s!"VIOLATION|fixture-not-alpha-equivalent|{label}"
        nViol := nViol + 1
      else if canonicalOf ca == canonicalOf cb then
        IO.println s!"VIOLATION|fixture-digest-collision|{label}"
        nViol := nViol + 1
      else
        IO.println s!"FIXTURE-DIGEST|{label}|eqv-equal-canonical-distinct"
    | _, _ =>
      IO.println s!"VIOLATION|fixture-missing|{label}"
      nViol := nViol + 1
  IO.println "SCRATCH-MANIFEST-START"
  for f in acc.fieldFailures do
    IO.println s!"VIOLATION|field-derivation|{f}"
    nViol := nViol + 1
  for f in acc.axEntryFailures do
    IO.println s!"VIOLATION|{f}"
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
  for (guard, required, mode) in depGuards do
    -- Pass-8 finding 3 (head mode): the required constant must be the proof
    -- term's APPLICATION HEAD once the declaration's own binders (and inert
    -- mdata) are stripped — an unused `let` or dead branch does not pass.
    -- Pass-9 finding 2: the pin table covers EVERY production-coupling probe,
    -- each naming the production/seed/constructor head its doctrine prescribes.
    -- Pass-10 finding: the documented destructuring probe is pinned
    -- structurally (`exists-destruct`), not by mere direct reference.
    let value? := match acc.consts.find? guard with
      | some (.thmInfo v)  => some v.value
      | some (.defnInfo v) => some v.value
      | _ => none
    match value? with
    | some v =>
      let ok := match mode with
        | "head" => (stripLamsMData v).getAppFn.constName? == some required
        | "exists-destruct" =>
          -- The stripped proof term must BE an `Exists.casesOn` application
          -- whose SCRUTINEE is headed by the required constant.  The scrutinee
          -- is argument index 3: `Exists.casesOn` takes the two implicit
          -- parameters and the motive before the major premise — a position
          -- fixed by the toolchain, legitimate to hard-code because the head
          -- is simultaneously pinned to exactly this constant.  The
          -- direct-reference check stays as a secondary guard.
          let s := stripLamsMData v
          let args := s.getAppArgs
          s.getAppFn.constName? == some ``Exists.casesOn
            && args.size ≥ 4
            && (stripMData args[3]!).getAppFn.constName? == some required
            && v.getUsedConstants.contains required
        | _      => false
      if ok then
        IO.println s!"DEPGUARD|{guard}|{required}|{mode}"
        nDep := nDep + 1
      else
        IO.println s!"VIOLATION|depguard-{mode}-failed|{guard}|{required}"
        nViol := nViol + 1
    | none =>
      IO.println s!"VIOLATION|depguard-no-value|{guard}"
      nViol := nViol + 1
  IO.println s!"SCRATCH-MANIFEST-END|{nDecl}|{nDep}|{if nViol == 0 then "OK" else "FAIL"}"
  if nViol != 0 then
    throw <| IO.userError s!"scratch static reader: {nViol} violation(s) — see VIOLATION lines"

#eval main'
