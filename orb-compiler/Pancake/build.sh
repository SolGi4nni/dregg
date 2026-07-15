#!/usr/bin/env bash
# Build the Pancake-in-Lean pilot (Pancake/Sem.lean, Lower.lean,
# EmitCorrectRegion.lean) + its Dsl/EmitPancake.lean dependency.
#
# DreggNet has no lakefile; the Dsl/*.lean files build standalone with plain
# `lean`, and these Pancake files add cross-file imports, so we compile to
# oleans in dependency order and point LEAN_PATH at them. Run from the repo root:
#     bash Pancake/build.sh
set -euo pipefail
cd "$(dirname "$0")/.."
O="$(mktemp -d)/oleans"
mkdir -p "$O/Dsl" "$O/Pancake"
for f in Dsl/EmitPancake Pancake/Sem Pancake/Lower Pancake/EmitCorrectRegion; do
  echo "building $f ..."
  LEAN_PATH="$O" lean --root=. -o "$O/$f.olean" "$f.lean"
done
echo "OK — all green"
# axiom footprint of the emit-correctness theorems:
cat > "$O/Ax.lean" <<'EOF'
import Pancake.EmitCorrectRegion
open Pancake.EmitCorrect
#print axioms evaluate_boundsChk   -- bounds-If (the C1 cross-check anchor)
#print axioms scan_loop            -- scan-While fuel induction
#print axioms region_scan_correct  -- the composed digest branch
EOF
LEAN_PATH="$O" lean --root=. "$O/Ax.lean"
