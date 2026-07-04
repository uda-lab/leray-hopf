# Issue #1 Finding 2 — Import Hygiene: Axiomatic Closures via Root Module

**Planner:** lean-planner  
**Source commit:** 93f74f4 / main  
**Scope:** READ-ONLY assessment; no Lean source edits in this document.

---

## 1. What finding 2 says

Issue #1 finding 2 names three files:

- `LerayHopf.lean` (the root re-export module)
- `LerayHopf/AxiomaticClosure.lean` (T³ axiomatic closure — formerly carried `axiom aubin_lions` and `axiom galerkin_limit_passage`; both REMOVED as of 2026-07-04: `aubin_lions` by #23/PR #89, `galerkin_limit_passage` by #25/PR #75; T³ now unconditional)
- `LerayHopf/R3/AxiomaticClosure.lean` (ℝ³ axiomatic closure — carries `axiom r3_NSForms_exist` and `axiom galerkin_limit_passage_R3`)

The concern: any file that writes `import LerayHopf` transitively inherits every project axiom, even if it only needs axiom-free pieces like `LerayHopf.Core`.

---

## 2. Current state (as of 93f74f4)

### 2a. The split already exists and is documented

The Wave-0 refactor introduced a three-layer import surface, documented in both `LerayHopf.lean` (lines 22–31) and `LerayHopf/Core.lean` (lines 33–67):

| Import | Content | Axioms |
|---|---|---|
| `import LerayHopf.Core` | axiom-free, sorryAx-free | 0 project axioms |
| `import LerayHopf.TorusAxiomatic` | T³ capstone chain | 0 project axioms (all three former axioms now proved: `torusConvectionGap_exists` → #53/PR#62, `galerkin_limit_passage` → #25/PR#75, `aubin_lions` → #23/PR#89) |
| `import LerayHopf.R3Axiomatic` | ℝ³ capstone chain | 1 (`galerkin_limit_passage_R3`; former axioms `r3_NSForms_exist`, `curlSchwartzDense_holds`, `galerkinSpaceTimeExtraction_R3`, `galerkin_weakLimit_R3`, `galerkin_spacetime_precompact_R3` all proved) |
| `import LerayHopf` | all three | 1 project axiom total (`galerkin_limit_passage_R3`; T³ unconditional) |

The root `LerayHopf.lean` is an intentional full-surface re-export. Its docstring says so explicitly. `LerayHopf.Core` exists precisely for consumers who want the axiom-free layer.

### 2b. Who actually uses `import LerayHopf` (the root)?

Grep result: **zero Lean source files** write `import LerayHopf` (the bare root). The pattern matches only:
- Comments inside `LerayHopf.lean` itself (the doc lines 25–28)
- Planning documents in `docs/scratch/`
- `LerayHopf/Core.lean` comments

The root module is consumed by `lake build` via `lakefile.toml`'s `[[lean_lib]] name = "LerayHopf"` — this compiles the whole library as one target, not because any file imports the root. No source file in the repo does `import LerayHopf`.

### 2c. What `scripts/print_axioms.lean` imports

```
import LerayHopf.TorusAxiomatic
import LerayHopf.R3Axiomatic
import LerayHopf.Core
```

It does NOT import the root `LerayHopf`. It imports the three sub-aggregators directly. The axiom live-pin is therefore already correctly scoped and would be unaffected by any change to the root module.

### 2d. The redundant imports in `LerayHopf.lean`

The root currently lists 22 imports. Eight of them are already transitively covered by `LerayHopf.TorusAxiomatic` or `LerayHopf.R3Axiomatic`:

- `LerayHopf.TorusAxiomatic` imports:
  - `LerayHopf.AxiomaticClosure` (which imports `LerayHopf.EvolutionTriple`, `LerayHopf.H1Sigma`, `LerayHopf.EnergyEstimate`, `LerayHopf.GalerkinProjection`)
  - `LerayHopf.TorusConvectionForm`
  - `LerayHopf.TorusGalerkinODECapstone` (which imports `LerayHopf.TorusConvectionForm` and `LerayHopf.TorusGalerkinODESolve`)
  - Transitively also: `LerayHopf.TorusGalerkinScheme`, `LerayHopf.RellichEmbedding`, `LerayHopf.SobolevTorus`, `LerayHopf.Statement`, `LerayHopf.ExistenceFromPackage`

- `LerayHopf.R3Axiomatic` imports `LerayHopf.R3.GalerkinODECapstone`, which transitively pulls in the entire R3 chain.

So the explicit lines in `LerayHopf.lean` for:

```
import LerayHopf.RellichEmbedding
import LerayHopf.H1Sigma
import LerayHopf.EvolutionTriple
import LerayHopf.Statement
import LerayHopf.ExistenceFromPackage
import LerayHopf.EnergyEstimate
import LerayHopf.TorusConvectionForm
import LerayHopf.TorusGalerkinScheme
import LerayHopf.TorusGalerkinODESolve
import LerayHopf.TorusGalerkinODECapstone
import LerayHopf.R3.GalerkinScheme
import LerayHopf.R3.SchwartzDivFreeBasis
import LerayHopf.R3.GalerkinODE
import LerayHopf.R3.GalerkinODEExistence
import LerayHopf.R3.GalerkinODESolve
import LerayHopf.R3.GalerkinODECapstone
import LerayHopf.R3.ArzelaAscoliTime
import LerayHopf.R3.AubinLionsLimitPassage
import LerayHopf.R3.CurlDensity
import LerayHopf.R3.FrechetKolmogorov
import LerayHopf.R3.ConvectionOperator
import LerayHopf.R3.ConvectionForm
import LerayHopf.Bochner.GelfandTriple
import LerayHopf.Bochner.TimeSobolev
```

...are redundant (already transitively covered) once `LerayHopf.TorusAxiomatic` and `LerayHopf.R3Axiomatic` are imported. The root could, in principle, be reduced to:

```
import LerayHopf.Core
import LerayHopf.TorusAxiomatic
import LerayHopf.R3Axiomatic
import LerayHopf.Bochner.GelfandTriple
import LerayHopf.Bochner.TimeSobolev
```

(The Bochner files are not transitively covered by any of the three aggregators and must be listed explicitly if the root is to remain a complete re-export.)

---

## 3. Ripple assessment

### Who would be affected by changing the root module?

- **Zero source files** import the root, so zero source files would break.
- The lakefile target `name = "LerayHopf"` compiles whatever is in `LerayHopf.lean`; a shorter import list in the root does not remove any module from the build (each module builds if imported from anywhere in the DAG).
- `scripts/print_axioms.lean` imports the three sub-aggregators directly — not the root — so it is unaffected.

Ripple count: **0 Lean source files touched, 1 file changed (LerayHopf.lean itself).**

### Is the concern real?

The concern (consumers inheriting axioms by importing the root) is technically valid but practically moot: no source file in the repo currently does `import LerayHopf`. All internal cross-imports use the specific sub-module paths. The only scenario where the finding applies is to a hypothetical future consumer or a downstream project that does `import LerayHopf` to get everything; such a consumer is documented to receive axioms via the root by design.

---

## 4. Chosen bounded change

**The change is safe, minimal, and bounded to a single file.** Prune the redundant explicit imports from `LerayHopf.lean`, reducing it to:

```lean
-- Axiom-free core layer
import LerayHopf.Core

-- Full axiomatic closures (transitive covers of all torus/R3 chain files)
import LerayHopf.TorusAxiomatic
import LerayHopf.R3Axiomatic

-- Bochner layer (not covered by either aggregator above)
import LerayHopf.Bochner.GelfandTriple
import LerayHopf.Bochner.TimeSobolev
```

Update the module docstring to reflect the pruned list and add an explicit note that `Bochner.*` are not yet aggregated under any sub-aggregator.

### What this does NOT do

- Does not move any theorem or axiom.
- Does not change any statement.
- Does not change the build target (lake still sees all files via transitivity).
- Does not break `print_axioms.lean` (it already imports sub-aggregators, not root).
- Does not change the axiom count or the live-pin.

---

## 5. Files to touch

| File | Change type | Classification |
|---|---|---|
| `LerayHopf.lean` | Remove redundant explicit imports; update docstring | scaffold-only (module structure) |

No other files touched.

---

## 6. Declarations

No declarations added, removed, or renamed. This is a pure module-structure edit.

---

## 7. Dependency edges affected

None — the DAG is unchanged. Lean only elaborates what is reachable; removing a redundant explicit import line from the root does not remove any transitive dependency.

---

## 8. Axiom packaging

None. This PR does not introduce or remove any `axiom`, `opaque`, `constant`, or `unsafe`.

---

## 9. Codex review points

Because this is a pure import-list prune with zero statement changes, the only review
gate is mechanical:

- Confirm that every module previously listed explicitly in `LerayHopf.lean` is still
  transitively reachable from the new five-line import list.  The verification is a DAG
  walk, not a proof obligation.  The mapping is:
  - `LerayHopf.Core` — unchanged; already covers all the Core-layer files.
  - `LerayHopf.TorusAxiomatic` → `LerayHopf.AxiomaticClosure` → `LerayHopf.EvolutionTriple`, `LerayHopf.H1Sigma`, `LerayHopf.EnergyEstimate`, `LerayHopf.GalerkinProjection`; and `LerayHopf.TorusConvectionForm`, `LerayHopf.TorusGalerkinODECapstone` → `LerayHopf.TorusGalerkinODESolve` → `LerayHopf.TorusGalerkinScheme`.  Also `LerayHopf.RellichEmbedding`, `LerayHopf.Statement`, `LerayHopf.ExistenceFromPackage` via `AxiomaticClosure`'s chain through `H1Sigma`.
  - `LerayHopf.R3Axiomatic` → `LerayHopf.R3.GalerkinODECapstone` → entire R3 chain including `GalerkinScheme`, `SchwartzDivFreeBasis`, `GalerkinODE`, `GalerkinODEExistence`, `GalerkinODESolve`, `AubinLionsAssembly`, `AubinLionsLimitPassage`, `ArzelaAscoliTime`, `CurlDensity`, `FrechetKolmogorov`, `ConvectionOperator`, `ConvectionForm`.
  - `LerayHopf.Bochner.GelfandTriple` and `LerayHopf.Bochner.TimeSobolev` — listed explicitly as before; not covered by any aggregator.

No adversarial-review slash command is needed for this PR (no new statement, no new proof, no axiom).

---

## 10. Axiom live-pin safety

`scripts/print_axioms.lean` imports:
```
import LerayHopf.TorusAxiomatic
import LerayHopf.R3Axiomatic
import LerayHopf.Core
```

It does not import the root. This PR does not touch any of those three files.
Pin-safe: confirmed.

---

## 11. Assessment: is finding 2 one-PR-bounded?

**Yes, trivially.**  The finding is already substantially resolved by Wave-0 (`LerayHopf.Core` exists and is documented). The only remaining mechanical improvement is pruning the explicit redundant imports from the root file, which is a one-file, zero-ripple, no-statement-change edit.

The residual gap (Bochner files not aggregated under any named sub-aggregator) is a cosmetic issue, not a soundness concern. A follow-up could create `LerayHopf.BochnerAxiomatic` or similar, but that is out of scope for this PR.

---

## 12. Definition of done

The PR is done when:

1. `lake build` passes (CI green).
2. `LerayHopf.lean` contains exactly the five import lines listed in §4 (or a superset that is justified in a code comment).
3. The module docstring accurately describes the new import surface.
4. `scripts/check-no-axiom.sh` passes (no new unmarked axiom — import changes cannot introduce axioms, but CI should confirm).
5. `scripts/print_axioms.lean` still compiles and the pinned axiom sets are unchanged.
6. `sorry` count is unchanged (this PR cannot affect it).

---

## 13. What remains for issue #1

This PR addresses only the import-hygiene finding. The other open finding from issue #1 (instance-fields bundled in `DissipativeEvolution`/`GelfandTriple` vs typeclass params — or the `GelfandTriple.ι` CLM refactor) is a separate PR, scoped in `docs/scratch/r1-arch-plan.md`.
