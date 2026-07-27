#!/usr/bin/env bash
# Build the chain prefix + Pancake/StageProg2.lean (the two-phase onion DSL) and
# print its axiom footprint. Own file; touches no other lane's build script.
# Run under swarm-build on hbox: SWARM_MEM_MAX=24G swarm-build bash Pancake/build_stageprog2.sh
set -euo pipefail
cd "$(dirname "$0")/.."
LEAN="${LEAN:-$HOME/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lean}"
O="${STAGEPROG2_OLEANS:-$HOME/.cache/stageprog2-oleans}"
mkdir -p "$O/Dsl" "$O/Pancake"
CHAIN="Dsl/EmitPancake Pancake/Sem Pancake/Lower Pancake/EmitCorrectRegion \
       Pancake/EmitCorrectCompose Pancake/EmitCorrectLoop Pancake/EmitCorrectClock \
       Pancake/BytesModel Pancake/StructModel \
       Pancake/SerializeCompile Pancake/NatToDecCompile Pancake/StageProg Pancake/StageCompile \
       Pancake/StageProg2"
for f in ${*:-$CHAIN}; do
  echo "building $f ..."
  LEAN_PATH="$O" "$LEAN" --root=. -o "$O/$f.olean" "$f.lean"
done
echo "OK — green"
