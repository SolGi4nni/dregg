#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
LEAN="${LEAN:-$HOME/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lean}"
O="${OLEANS:-$(mktemp -d)/oleans}"
mkdir -p "$O/Dsl" "$O/Pancake"
for f in Dsl/EmitPancake Pancake/Sem Pancake/Lower Pancake/EmitCorrectRegion \
         Pancake/EmitCorrectCompose Pancake/EmitCorrectLoop Pancake/EmitCorrectClock \
         Pancake/SerializeCompile Pancake/StructModel Pancake/SerializeFull; do
  echo "building $f ..."
  LEAN_PATH="$O" "$LEAN" --root=. -o "$O/$f.olean" "$f.lean"
done
echo "OK — all green"
cat > "$O/AxSF.lean" <<AXEOF
import Pancake.SerializeFull
open Pancake.SerializeFull
#print axioms copy_stepF
#print axioms copy_loop
#print axioms writeSeg_correct
#print axioms writeSegs_correct
#print axioms serialize_structured_correct
AXEOF
LEAN_PATH="$O" "$LEAN" --root=. "$O/AxSF.lean"
echo "OLEANS=$O"
