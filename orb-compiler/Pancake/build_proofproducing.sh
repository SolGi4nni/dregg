#!/usr/bin/env bash
# Build the proof-producing-translation extension (Pancake/ProofProducing.lean)
# and print the axiom footprint of every new theorem. Additive over
# Pancake/build_compose.sh (imports EmitCorrectCompose unchanged).
#
# TOOLCHAIN: authored for Lean 4.30/4.31. On hbox the default `lean` is 4.17 and
# CANNOT build it; point LEAN at the 4.30 elan toolchain:
#   LEAN=~/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lean bash Pancake/build_proofproducing.sh   # hbox
#   bash Pancake/build_proofproducing.sh                                                                # local (4.31)
set -euo pipefail
cd "$(dirname "$0")/.."
LEAN="${LEAN:-lean}"
O="$(mktemp -d)/oleans"
mkdir -p "$O/Dsl" "$O/Pancake"
for f in Dsl/EmitPancake Pancake/Sem Pancake/Lower Pancake/EmitCorrectRegion Pancake/EmitCorrectCompose Pancake/ProofProducing; do
  echo "building $f ..."
  LEAN_PATH="$O" "$LEAN" --root=. -o "$O/$f.olean" "$f.lean"
done
echo "OK — all green"
# axiom footprint (must be ⊆ {propext, Quot.sound, Classical.choice}):
cat > "$O/AxPP.lean" <<'EOF'
import Pancake.ProofProducing
open Pancake.ProofProducing
#print axioms wf_skip
#print axioms wf_assign
#print axioms wf_store
#print axioms closedDemo_wf              -- WF closed by wf_auto, ZERO hyps
#print axioms closedDemo_cert            -- certificate auto-produced (closed stage)
#print axioms redirectStatusStage_wf     -- REAL stage WF, wf_auto + input contract
#print axioms redirectStatusStage_cert   -- REAL stage certificate, auto-produced
#print axioms emitServe_correct          -- translator correctness
EOF
LEAN_PATH="$O" "$LEAN" --root=. "$O/AxPP.lean"
