#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
LEAN="${LEAN:-$HOME/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lean}"
O="${STAGEPROG2_OLEANS:-$HOME/.cache/stageprog2-oleans}"
mkdir -p "$O/Dsl" "$O/Pancake"
CHAIN="Dsl/EmitPancake Pancake/Sem Pancake/Lower Pancake/EmitCorrectRegion \
       Pancake/EmitCorrectCompose Pancake/EmitCorrectLoop Pancake/EmitCorrectClock \
       Pancake/BytesModel Pancake/StructModel \
       Pancake/SerializeCompile Pancake/NatToDecCompile Pancake/StageProg Pancake/StageCompile \
       Pancake/StageProg2 Pancake/StageLift2 Pancake/StageLift2Inst"
for f in ${*:-$CHAIN}; do
  echo "building $f ..."
  LEAN_PATH="$O" "$LEAN" --root=. -o "$O/$f.olean" "$f.lean"
done
echo "OK — green"
