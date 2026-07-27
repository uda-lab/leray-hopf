#!/usr/bin/env bash
# Combined preflight: agents MUST run this before and after editing Lean sources.
# Order matters — build first (Build-first rule), then the discipline checks.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

# Make an elan-installed toolchain visible to non-login shells (e.g. subagents, CI).
export PATH="$HOME/.elan/bin:$PATH"

if ! command -v lake >/dev/null 2>&1; then
  echo "ERROR: 'lake' not found." >&2
  echo "Install the Lean toolchain manager first:" >&2
  echo "  curl -fsSL https://elan.lean-lang.org/elan-init.sh | sh -s -- -y" >&2
  echo "Then re-run: bash scripts/agent-preflight.sh" >&2
  exit 1
fi

echo "==> lake build"
# Serialize concurrent builds to avoid OOM in the 3.42 GiB cgroup (swap disabled).
# Full build peaks ~3.40 GiB; a second parallel build is fatal.
# flock is present on this container (util-linux); if absent (non-Linux dev machine)
# we fall back to running without a lock rather than failing the preflight entirely.
if command -v flock >/dev/null 2>&1; then
  flock /tmp/lean-build.lock lake build
else
  echo "WARNING: flock not found; running lake build without serialization lock." >&2
  lake build
fi

echo "==> scripts/check-no-sorry.sh"
bash scripts/check-no-sorry.sh

echo "==> scripts/check-no-axiom.sh"
bash scripts/check-no-axiom.sh

echo "==> scripts/check-theorem-names.sh"
bash scripts/check-theorem-names.sh

echo "==> scripts/check-axioms.sh"
bash scripts/check-axioms.sh

echo "==> scripts/check-release-cone.sh"
bash scripts/check-release-cone.sh

echo "==> scripts/test-check-release-cone.sh"
bash scripts/test-check-release-cone.sh

echo "==> scripts/check-statement-cards.sh"
bash scripts/check-statement-cards.sh

echo "==> scripts/check-axioms-live.sh"
bash scripts/check-axioms-live.sh

# Invoked UNWRAPPED: check-scratch-pins.sh self-locks on /tmp/lean-build.lock (held
# through its own build); an outer flock on the same lock would self-deadlock.
echo "==> scripts/check-scratch-pins.sh"
bash scripts/check-scratch-pins.sh

echo "PREFLIGHT OK"
