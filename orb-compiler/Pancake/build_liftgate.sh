#!/usr/bin/env bash
# Build the chain prefix + Pancake/StageLiftGate.lean (the gate lift) and print its
# axiom footprint. Own file; touches no other lane's build script or the lakefile.
set -euo pipefail
cd "$(dirname "$0")/.."
LEAN="${LEAN:-$HOME/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lean}"
O="${LIFTGATE_OLEANS:-$HOME/.cache/liftgate-oleans}"
mkdir -p "$O/Dsl" "$O/Pancake"
CHAIN="Dsl/EmitPancake Pancake/Sem Pancake/Lower Pancake/EmitCorrectRegion \
       Pancake/EmitCorrectCompose Pancake/EmitCorrectLoop Pancake/EmitCorrectClock \
       Pancake/BytesModel Pancake/StructModel \
       Pancake/SerializeCompile Pancake/NatToDecCompile Pancake/StageProg Pancake/StageCompile \
       Pancake/StageLiftGate"
for f in ${*:-$CHAIN}; do
  echo "building $f ..."
  LEAN_PATH="$O" "$LEAN" --root=. -o "$O/$f.olean" "$f.lean"
done
echo "OK — green"
