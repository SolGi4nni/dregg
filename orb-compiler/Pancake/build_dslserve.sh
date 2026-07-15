#!/usr/bin/env bash
# Build the stage-algebra serve payoff (Pancake/DslServe.lean) and print the axiom
# footprint. Additive over build_serveslice.sh — imports Pancake.ServeSlice
# unchanged and adds the shared StageProg algebra, its denote/compile
# interpretations, the keystone compiler-correctness theorem, and the composed
# serveProg verified byte-identical to the leanc reference serve on a request corpus.
#
#   LEAN=~/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lean bash Pancake/build_dslserve.sh
set -euo pipefail
cd "$(dirname "$0")/.."
LEAN="${LEAN:-$HOME/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lean}"
O="${OLEANS:-$(mktemp -d)/oleans}"
mkdir -p "$O/Dsl" "$O/Pancake"
for f in Dsl/EmitPancake Pancake/Sem Pancake/Lower Pancake/EmitCorrectRegion \
         Pancake/EmitCorrectCompose Pancake/EmitCorrectLoop Pancake/EmitCorrectClock \
         Pancake/ProofProducing Pancake/ServeFragment Pancake/SerializeCompile \
         Pancake/ServeSlice Pancake/DslServe; do
  echo "building $f ..."
  LEAN_PATH="$O" "$LEAN" --root=. -o "$O/$f.olean" "$f.lean"
done
echo "OK — all green"
cat > "$O/AxDsl.lean" <<AXEOF
import Pancake.DslServe
open Pancake.DslServe
#print axioms stageprog_compile_correct
#print axioms compileStep_dToC
#print axioms serveProg_get_eq_machine
#print axioms serveProg_refuse_eq_machine
#print axioms serveProg_eq_serveSlice_postcondition
AXEOF
LEAN_PATH="$O" "$LEAN" --root=. "$O/AxDsl.lean"
echo "OLEANS=$O"
