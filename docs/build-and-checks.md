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
bash scripts/check-no-sorry.sh        # unmarked `sorry`
bash scripts/check-no-axiom.sh        # unmarked axiom/constant/opaque/unsafe
bash scripts/check-theorem-names.sh   # overclaiming declaration names
```

## Preflight (run before and after editing)

Builds, then runs all three checks in order:

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

- **PRs** run the `guards` job: grep guards only (`check-no-sorry.sh`,
  `check-no-axiom.sh`, `check-theorem-names.sh`). No Lean build on CI for PRs.
- **Full build + axiom pins** (`check-axioms.sh`, `check-axioms-live.sh`) run
  **manually** via the `lean` workflow's `workflow_dispatch` trigger on GitHub.
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
