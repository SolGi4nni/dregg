#!/usr/bin/env bash
# Build the grown serve end-to-end certificate (Pancake/ServeFull.lean) and print
# the axiom footprint. Additive over build_serveslice.sh + build_serializefull.sh
# (imports ServeSlice + SerializeFull unchanged).
#
#   LEAN=~/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lean bash Pancake/build_servefull.sh
set -euo pipefail
cd "$(dirname "$0")/.."
LEAN="${LEAN:-$HOME/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lean}"
O="${OLEANS:-$(mktemp -d)/oleans}"
mkdir -p "$O/Dsl" "$O/Pancake"
for f in Dsl/EmitPancake Pancake/Sem Pancake/Lower Pancake/EmitCorrectRegion \
         Pancake/EmitCorrectCompose Pancake/EmitCorrectLoop Pancake/EmitCorrectClock \
         Pancake/ProofProducing Pancake/ServeFragment Pancake/SerializeCompile \
         Pancake/StructModel Pancake/SerializeFull Pancake/ServeSlice Pancake/ServeFull; do
  echo "building $f ..."
  LEAN_PATH="$O" "$LEAN" --root=. -o "$O/$f.olean" "$f.lean"
done
echo "OK — all green"
cat > "$O/AxServeFull.lean" <<AXEOF
import Pancake.ServeFull
open Pancake.ServeFull
#print axioms serveFull_correct
#print axioms decisionPrefix_cert
#print axioms prefix_frame
#print axioms SourcesOK_congr
AXEOF
LEAN_PATH="$O" "$LEAN" --root=. "$O/AxServeFull.lean"
echo "OLEANS=$O"
