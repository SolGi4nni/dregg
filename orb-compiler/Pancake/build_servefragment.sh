#!/usr/bin/env bash
# Build the serve-fragment scaling extension (Pancake/ServeFragment.lean) and print
# the axiom footprint of every new certificate. Additive over
# Pancake/build_proofproducing.sh (imports ProofProducing + EmitCorrectCompose
# unchanged).
#
# TOOLCHAIN: authored for Lean 4.30/4.31. On hbox point LEAN at the 4.30 toolchain:
#   LEAN=~/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lean bash Pancake/build_servefragment.sh   # hbox
#   bash Pancake/build_servefragment.sh                                                                # local
set -euo pipefail
cd "$(dirname "$0")/.."
LEAN="${LEAN:-lean}"
O="$(mktemp -d)/oleans"
mkdir -p "$O/Dsl" "$O/Pancake"
for f in Dsl/EmitPancake Pancake/Sem Pancake/Lower Pancake/EmitCorrectRegion \
         Pancake/EmitCorrectCompose Pancake/ProofProducing Pancake/ServeFragment; do
  echo "building $f ..."
  LEAN_PATH="$O" "$LEAN" --root=. -o "$O/$f.olean" "$f.lean"
done
echo "OK — all green"
# axiom footprint (must be ⊆ {propext, Quot.sound, Classical.choice}):
cat > "$O/AxSF.lean" <<'EOF'
import Pancake.ServeFragment
open Pancake.ServeFragment
-- WF discharged by wf_auto (each is a `by wf_auto` one-liner):
#print axioms Pancake.ServeFragment.connLimitDecision_wf
#print axioms Pancake.ServeFragment.bodyLimitDecision_wf
#print axioms Pancake.ServeFragment.ipfilterDecision_wf
#print axioms Pancake.ServeFragment.methodFilterDecision_wf
#print axioms Pancake.ServeFragment.securityHeadersDecision_wf
-- certificates auto-produced (emit refines denote, WF from wf_auto):
#print axioms Pancake.ServeFragment.connLimitDecision_cert
#print axioms Pancake.ServeFragment.bodyLimitDecision_cert
#print axioms Pancake.ServeFragment.ipfilterDecision_cert
#print axioms Pancake.ServeFragment.methodFilterDecision_cert
#print axioms Pancake.ServeFragment.securityHeadersDecision_cert
EOF
LEAN_PATH="$O" "$LEAN" --root=. "$O/AxSF.lean"
