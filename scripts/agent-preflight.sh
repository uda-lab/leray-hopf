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
lake build

echo "==> scripts/check-no-sorry.sh"
bash scripts/check-no-sorry.sh

echo "==> scripts/check-no-axiom.sh"
bash scripts/check-no-axiom.sh

echo "==> scripts/check-theorem-names.sh"
bash scripts/check-theorem-names.sh

echo "PREFLIGHT OK"
