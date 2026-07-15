#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
LEAN="${LEAN:-$HOME/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lean}"
O="${OLEANS:-$(mktemp -d)/oleans}"
mkdir -p "$O/Dsl" "$O/Pancake"
for f in Dsl/EmitPancake Pancake/Sem Pancake/Lower Pancake/EmitCorrectRegion \
         Pancake/EmitCorrectCompose Pancake/EmitCorrectLoop Pancake/EmitCorrectClock \
         Pancake/SerializeCompile; do
  echo "building $f ..."
  LEAN_PATH="$O" "$LEAN" --root=. -o "$O/$f.olean" "$f.lean"
done
echo "OK — all green"
echo "OLEANS=$O"
