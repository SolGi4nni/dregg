#!/usr/bin/env bash
# Build the Pancake-in-Lean chain + the CLOCK-ACCOUNTING extension
# (Pancake/EmitCorrectClock.lean) and print the axiom footprint of the new
# theorems. Additive over Pancake/build_loop.sh.
set -euo pipefail
cd "$(dirname "$0")/.."
LEAN="${LEAN:-$HOME/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lean}"
O="$(mktemp -d)/oleans"
mkdir -p "$O/Dsl" "$O/Pancake"
for f in Dsl/EmitPancake Pancake/Sem Pancake/Lower Pancake/EmitCorrectRegion \
         Pancake/EmitCorrectCompose Pancake/EmitCorrectLoop Pancake/EmitCorrectClock; do
  echo "building $f ..."
  LEAN_PATH="$O" "$LEAN" --root=. -o "$O/$f.olean" "$f.lean"
done
echo "OK — all green"
cat > "$O/AxK.lean" <<'EOF'
import Pancake.EmitCorrectClock
open Pancake.EmitCorrectClock
#print axioms RefinesClk
#print axioms refinesClk_of_refines
#print axioms refinesClk_assign
#print axioms refinesClk_seq
#print axioms refinesClk_dec
#print axioms refinesClk_conseq
#print axioms while_inv_cond_clk
#print axioms refinesClk_scanWhile
#print axioms refinesClk_scan_publish
#print axioms region_via_clock
EOF
LEAN_PATH="$O" "$LEAN" --root=. "$O/AxK.lean"
