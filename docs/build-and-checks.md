# Build and checks

How to build the project and run the discipline checks. No mathematical content here.

## Prerequisites

The Lean toolchain is managed by [elan](https://github.com/leanprover/elan). If `lake`
is not on your `PATH`:

```bash
curl -fsSL https://elan.lean-lang.org/elan-init.sh | sh -s -- -y
export PATH="$HOME/.elan/bin:$PATH"
```

elan reads `lean-toolchain` and installs the pinned Lean version automatically on first use.

### Why `lean-toolchain` pins an RC, not a stable release

`lean-toolchain` currently pins `leanprover/lean4:v4.31.0-rc2`. This is deliberate
mathlib-alignment, not a stale pin left over from bootstrap: `[[require]] mathlib` in
`lakefile.toml` tracks `rev = "master"` (a floating target, made reproducible by the explicit
commit pin in `lake-manifest.json`), and the mathlib commit currently pinned there itself
depends on `leanprover/lean4-cli` at `inputRev = "v4.31.0-rc2"`. That match is evidence — not
a formal proof — that mathlib master, as resolved, targets this same Lean release; it is the
closest signal available without querying the Lean/mathlib release calendar directly. Treat
this pin as tied to mathlib's own toolchain, not to a preference for release-candidates: moving
to a later stable release ahead of mathlib's own pin risks desyncing the build. Re-evaluate
this pin whenever `lake update` re-resolves mathlib (an explicit `lean-coder` task; see below).

## Build

```bash
lake exe cache get   # download prebuilt mathlib oleans (first time / after mathlib bump)
lake build
```

> `lake update` (bumping the mathlib revision) is an **explicit `lean-coder` task only**. The
> pinned commit in `lake-manifest.json` is the reproducibility source of truth — do not run
> `lake update` as a side effect of other work.

## Discipline checks

```bash
bash scripts/check-no-sorry.sh          # unmarked `sorry`
bash scripts/check-no-axiom.sh          # unmarked axiom/constant/opaque/unsafe
bash scripts/check-theorem-names.sh     # overclaiming declaration names
bash scripts/check-axioms.sh            # axiom-leak static pre-filter
bash scripts/check-release-cone.sh      # release cone (import LerayHopf) is sorry-free
bash scripts/check-statement-cards.sh   # every ALLOW_SORRY decl has a statement card (issue #158)
```

`check-statement-cards.sh` also pins `w1pTime_continuous_in_H` at `p = q = 2` — see
`docs/statement-gates.md` for the statement-card process this enforces and
`docs/postmortems/2026-07-w1ptime-false-statement.md` for why.

## Preflight (run before and after editing)

Builds, then runs all the discipline checks above (plus the live axiom pin) in order:

```bash
bash scripts/agent-preflight.sh
```

For agent runs, do not stream full Lean build or preflight output into the chat/context.
Capture the log, inspect the exit status, and read only the relevant success tail or
error slice:

```bash
bash scripts/agent-preflight.sh >/tmp/lean-pde-preflight.log 2>&1
echo $?
tail -n 80 /tmp/lean-pde-preflight.log
```

On failure, narrow the log with `rg`, `sed`, or `tail` before quoting output.

## Markers

The checks honor same-line justification markers:

| Marker | Permits |
|---|---|
| `-- ALLOW_SORRY: <reason>` | a `sorry` on that line |
| `-- ALLOW_AXIOM: <reason>` | an `axiom`/`constant`/`opaque`/`unsafe` on that line |
| `-- ALLOW_NAME: <reason>` | a reserved term in a declaration name on that line |

Markers are per-line by design, so every exception is justified where it occurs.

## CI

Auto full builds are **abolished** (GitHub Actions cost).

- **PRs** run the `guards` job: the six static/textual guards above
  (`check-no-sorry.sh`, `check-no-axiom.sh`, `check-theorem-names.sh`, `check-axioms.sh`,
  `check-release-cone.sh`, `check-statement-cards.sh`). No Lean build on CI for PRs.
- **Full build + live axiom pin** (`check-axioms-live.sh`, which additionally prints the
  `LerayHopf.Experimental` axiom profile for visibility — see
  `docs/statement-gates.md`) runs **manually** via the `lean` workflow's
  `workflow_dispatch` trigger on GitHub, together with all six guards above.
- **Release-candidate build attestation** — a separate, persisted evidence record
  for one exact SHA — runs manually via the `release-attestation` workflow (see
  below).
- **Mandatory build gate** is the **local incremental build**, enforced by the
  `scripts/hooks/pre-push` git hook.

### Activating the pre-push hook (once per clone)

```bash
git config core.hooksPath scripts/hooks
```

After activation, every `git push` runs the grep guards and, when `.lean` /
`lakefile` / `lean-toolchain` files changed, a flock-serialized `lake build`.
A failing build or failing guard blocks the push.

Verify activation:

```bash
git config --get core.hooksPath   # should print: scripts/hooks
```

## Release-candidate build attestation (issue #150)

The README badge links to the `release-attestation` workflow, a `workflow_dispatch`-only
job that certifies one exact commit SHA has a full `lake build` pass plus all discipline
guards, including the capstone live axiom pin (`check-axioms-live.sh`). It never runs on
push, pull request, or a schedule, and it is separate from the `lean` workflow's routine
`full-build` dispatch job (see above) — it takes an explicit SHA input and produces a
persisted attestation record, rather than only a job log.

### Producing a new attestation

```bash
gh workflow run release-attestation.yml --repo uda-lab/lean-pde -f ref=<candidate-sha-or-tag>
```

The run resolves `<candidate-sha-or-tag>` and checks it out, records the resulting commit
SHA, the `lean-toolchain` content, and the sha256 of `lake-manifest.json`, runs the full
build and every guard script, and writes the results as:

- the workflow run's **job summary** (a Markdown table: SHA, toolchain, manifest hash,
  per-step pass/fail, guard log checksums), and
- an **artifact** named `release-attestation-<sha>` (the same Markdown file plus the raw
  guard logs), retained for 90 days (the GitHub maximum for public repositories).

### Finding the SHA of the latest attestation

Open the workflow's [runs page](https://github.com/uda-lab/lean-pde/actions/workflows/release-attestation.yml)
(same link as the README badge) and open the most recent run — the job summary states the
attested SHA at the top. **A green badge or a green run does not mean the current branch
HEAD is attested** — it means exactly the SHA recorded in that run's summary is attested.
If commits have landed since that SHA, treat the code between the attested SHA and HEAD as
unattested (though still covered by the local pre-push build gate and, on PRs, the fast
`guards` job) until a new attestation is run against the new candidate SHA.

### Durability caveat

The job summary and artifact are bounded by GitHub's run/artifact retention window, not
stored forever. For a commit that is being cut as an actual public release, additionally
attach the attestation Markdown file as an asset on the corresponding GitHub Release —
Release assets do not expire.
