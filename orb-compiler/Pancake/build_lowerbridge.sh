#!/usr/bin/env bash
# Build Pancake/LowerBridge.lean against the prebuilt olean set (ServeEmit is not
# a lakefile root, so this file — which imports it — has its own build, the same
# pattern the other serve lanes use). Per-file, SYNC, nice'd (swarm-build wraps
# the cgroup memory cap around the whole invocation).
set -euo pipefail
cd "$(dirname "$0")/.."
LEAN="${LEAN:-$HOME/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lean}"
O="${OLEANS:-/tmp/lb_oleans}"
mkdir -p "$O/Pancake"
echo "building Pancake/LowerBridge ..."
LEAN_PATH="$O" nice -n 15 "$LEAN" --root=. -o "$O/Pancake/LowerBridge.olean" Pancake/LowerBridge.lean
echo "OK — LowerBridge green"
