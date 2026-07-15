#!/usr/bin/env bash
# Build the Pancake-in-Lean pilot + the compositional emit-correctness extension
# + the LOOP-BEARING extension (Pancake/EmitCorrectLoop.lean), and print the axiom
# footprint of the new loop theorems. Additive over Pancake/build_compose.sh
# (does not touch any earlier file; just adds the loop file after Compose).
#
# TOOLCHAIN: the proofs are authored for Lean 4.30/4.31. On hbox the default
# `lean` is 4.17 (the `Nat.and_two_pow_sub_one_eq_mod` mask lemma was renamed
# there), so point LEAN at the 4.30 elan toolchain:
#     LEAN=~/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lean bash Pancake/build_loop.sh   # hbox
#     bash Pancake/build_loop.sh                                                                # local (4.31)
set -euo pipefail
cd "$(dirname "$0")/.."
LEAN="${LEAN:-lean}"
O="$(mktemp -d)/oleans"
mkdir -p "$O/Dsl" "$O/Pancake"
for f in Dsl/EmitPancake Pancake/Sem Pancake/Lower Pancake/EmitCorrectRegion \
         Pancake/EmitCorrectCompose Pancake/EmitCorrectLoop; do
  echo "building $f ..."
  LEAN_PATH="$O" "$LEAN" --root=. -o "$O/$f.olean" "$f.lean"
done
echo "OK — all green"
# axiom footprint (must be ⊆ {propext, Quot.sound, Classical.choice}):
cat > "$O/AxL.lean" <<'EOF'
import Pancake.EmitCorrectLoop
open Pancake.EmitCorrect Pancake.EmitCorrectLoop
#print axioms while_inv_cond        -- reusable CONDITIONAL bounded-While rule
#print axioms scan_step             -- one scan iteration advances the invariant
#print axioms scan_loop_via_rule    -- the scan While via the reusable rule
#print axioms scanWhile_via_rule    -- scan-While emit-correctness (digest published)
#print axioms emit_scanLoop         -- ties the certified loop to the `emit` translator
EOF
LEAN_PATH="$O" "$LEAN" --root=. "$O/AxL.lean"
