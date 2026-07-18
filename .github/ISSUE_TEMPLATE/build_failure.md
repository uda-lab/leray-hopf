---
name: Build failure
about: "`lake build` or a discipline check script fails"
title: "[build] "
labels: bug
---

## Command that failed

<!-- e.g. `lake build`, `bash scripts/agent-preflight.sh`, a specific check-*.sh -->

## Error output

<!-- Paste the relevant tail of the error. Do not paste a full multi-thousand-line
     log — narrow it first (see docs/build-and-checks.md's "Preflight" section for
     how). -->

## Environment

- Commit SHA:
- `lean-toolchain` content:
- Did `lake exe cache get` succeed first?:
- OS / arch:

## Checked already

- [ ] `lean-toolchain` matches what is committed (no local override)
- [ ] `lake-manifest.json` is unmodified / matches HEAD
- [ ] This is not the known macOS `flock` pre-push-hook issue (#118)
