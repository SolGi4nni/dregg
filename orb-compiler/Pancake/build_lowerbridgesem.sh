#!/usr/bin/env bash
# Build Pancake/LowerBridgeSem.lean (the SEMANTIC half of the PStmt⟷PancakeProg
# bridge — the byte-store landing lemma) against the prebuilt olean set. Imports
# Pancake.LowerBridge (transitively Sem/ServeEmit/Lower). Same per-file pattern as
# build_lowerbridge.sh. Run under swarm-build on hbox (box-safety).
set -euo pipefail
cd "$(dirname "$0")/.."
LEAN="${LEAN:-$HOME/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lean}"
O="${OLEANS:-/tmp/lb_oleans}"
mkdir -p "$O/Pancake"
echo "building Pancake/LowerBridgeSem ..."
LEAN_PATH="$O" nice -n 15 "$LEAN" --root=. -o "$O/Pancake/LowerBridgeSem.olean" Pancake/LowerBridgeSem.lean
echo "OK — LowerBridgeSem green"
