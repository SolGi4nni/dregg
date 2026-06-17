#!/usr/bin/env bash
# emit-descriptors.sh — THE one command that regenerates every circuit descriptor
# artifact from the verified Lean emission (the SOURCE OF TRUTH) and re-pins the
# sha256 fingerprints in the Rust registry.
#
# Lean is authoritative. The `circuit/descriptors/*.json` files and the `*_FP`
# constants in `circuit/src/*.rs` are machine-generated projections of the Lean
# `EffectVmDescriptor` objects. Running this on a clean tree is a NO-OP (idempotent):
# it leaves the tree byte-identical. After moving any Lean emit, run this and commit.
#
# Usage:  scripts/emit-descriptors.sh
# Exit:   0 = regenerated (or no-op); nonzero = an emitter failed or a routing gap.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"

if ! command -v lake >/dev/null 2>&1; then
  echo "emit-descriptors: ERROR — 'lake' not on PATH (Lean toolchain required)." >&2
  exit 1
fi

exec python3 "$ROOT/scripts/emit_descriptors.py"
