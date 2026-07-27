#!/usr/bin/env bash
# Build the Pancake-in-Lean chain + the REAL-STAGE byte-effect witness
# (Pancake/RealStageDemo.lean) and print the axiom footprint of the new theorems.
# Additive over Pancake/build_clock.sh (does not touch any earlier file).
#
# TOOLCHAIN: authored for Lean 4.30/4.31. On hbox the default `lean` is 4.17, so
# point LEAN at the 4.30 elan toolchain:
#   LEAN=~/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lean bash Pancake/build_realstage.sh
set -euo pipefail
cd "$(dirname "$0")/.."
LEAN="${LEAN:-$HOME/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lean}"
O="$(mktemp -d)/oleans"
mkdir -p "$O/Dsl" "$O/Pancake"
for f in Dsl/EmitPancake Pancake/Sem Pancake/Lower Pancake/EmitCorrectRegion \
         Pancake/EmitCorrectCompose Pancake/EmitCorrectLoop Pancake/EmitCorrectClock \
         Pancake/RealStageDemo; do
  echo "building $f ..."
  LEAN_PATH="$O" taskset -c 0-15 nice -n 15 "$LEAN" --root=. -o "$O/$f.olean" "$f.lean"
done
echo "OK — all green"
# axiom footprint (must be ⊆ {propext, Quot.sound, Classical.choice}; NO native_decide/ofReduceBool):
cat > "$O/AxR.lean" <<'EOF'
import Pancake.RealStageDemo
open Pancake.RealStageDemo
#print axioms hdrStore_byte_effect   -- straight-line header-append: byte-view = getByte-decomp of stored word
#print axioms hdrStore_ascii         -- concrete "X: 1" CRLF -> exact ASCII output bytes [88,58,32,49,13,10]
#print axioms fill_step              -- one write-loop iteration advances the fill invariant
#print axioms fill_loop_slots        -- the write-While: every slot < n holds the header word
#print axioms fill_byte_effect       -- write-loop byte-view over the whole 8*n-byte region = getByte-decomp
#print axioms fillDemo_ascii         -- concrete 3-slot fill -> ASCII bytes decided in-kernel
#print axioms emit_fillBody          -- the certified loop body IS what the translator emits
EOF
LEAN_PATH="$O" taskset -c 0-15 nice -n 15 "$LEAN" --root=. "$O/AxR.lean"
