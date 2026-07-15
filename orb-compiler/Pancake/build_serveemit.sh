#!/usr/bin/env bash
# Build Pancake/ServeEmit.lean (and its ServeSlice dependency chain) and write
# Pancake/serve_slice_export.pnk. Per-file, SYNC, nice'd.
set -euo pipefail
cd "$(dirname "$0")/.."
LEAN="${LEAN:-$HOME/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lean}"
O="${OLEANS:-$(mktemp -d)/oleans}"
mkdir -p "$O/Dsl" "$O/Pancake"
for f in Dsl/EmitPancake Pancake/Sem Pancake/Lower Pancake/EmitCorrectRegion \
         Pancake/EmitCorrectCompose Pancake/EmitCorrectLoop Pancake/EmitCorrectClock \
         Pancake/ProofProducing Pancake/ServeFragment Pancake/SerializeCompile \
         Pancake/ServeSlice Pancake/ServeEmit; do
  echo "building $f ..."
  LEAN_PATH="$O" taskset -c 0-15 nice -n 15 "$LEAN" --root=. -o "$O/$f.olean" "$f.lean"
done
echo "OK — all green"
echo "OLEANS=$O"
