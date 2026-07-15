#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
LEAN="${LEAN:-$HOME/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lean}"
O="$(mktemp -d)/oleans"
mkdir -p "$O/Dsl" "$O/Pancake"
for f in Dsl/EmitPancake Pancake/Sem Pancake/Lower Pancake/EmitCorrectRegion \
         Pancake/EmitCorrectCompose Pancake/EmitCorrectLoop Pancake/EmitCorrectClock \
         Pancake/StructModel; do
  echo "building $f ..."
  LEAN_PATH="$O" "$LEAN" --root=. -o "$O/$f.olean" "$f.lean"
done
echo "OK — all green"
cat > "$O/AxSM.lean" <<AXEOF
import Pancake.StructModel
open Pancake.StructModel
#print axioms eval_loadWord_of_wordAt
#print axioms resp_load_status
#print axioms resp_load_bodyLen
#print axioms resp_load_bodyByte
#print axioms list_load_count
#print axioms list_load_keyLen
#print axioms sum_step
#print axioms sumLen_loop
#print axioms refinesClk_sumLoop
#print axioms resp_layout_witness
#print axioms list_iter_witness
AXEOF
LEAN_PATH="$O" "$LEAN" --root=. "$O/AxSM.lean"
