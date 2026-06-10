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

## Markers

The checks honor same-line justification markers:

| Marker | Permits |
|---|---|
| `-- ALLOW_SORRY: <reason>` | a `sorry` on that line |
| `-- ALLOW_AXIOM: <reason>` | an `axiom`/`constant`/`opaque`/`unsafe` on that line |
| `-- ALLOW_NAME: <reason>` | a reserved term in a declaration name on that line |

Markers are per-line by design, so every exception is justified where it occurs.

## CI

`.github/workflows/lean.yml` runs the same build and checks on push, pull request, and
manual dispatch. Local preflight and CI run the identical scripts.
