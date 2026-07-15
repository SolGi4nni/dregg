#!/usr/bin/env bash
# Build the Pancake-in-Lean pilot + the compositional emit-correctness extension
# (Pancake/EmitCorrectCompose.lean) and print the axiom footprint of every new
# emit_correct theorem. Additive over Pancake/build.sh (does not touch the region
# proof; just adds the compose file after it).
#
# TOOLCHAIN: the proofs are authored for Lean 4.30/4.31. On hbox the default
# `lean` is 4.17 (lacks e.g. `Nat.and_two_pow_sub_one_eq_mod`), so point LEAN at
# the 4.30 elan toolchain there. Locally (ember's box, 4.31) plain `lean` works.
#     LEAN=~/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lean bash Pancake/build_compose.sh   # hbox
#     bash Pancake/build_compose.sh                                                                # local (4.31)
set -euo pipefail
cd "$(dirname "$0")/.."
LEAN="${LEAN:-lean}"
O="$(mktemp -d)/oleans"
mkdir -p "$O/Dsl" "$O/Pancake"
for f in Dsl/EmitPancake Pancake/Sem Pancake/Lower Pancake/EmitCorrectRegion Pancake/EmitCorrectCompose; do
  echo "building $f ..."
  LEAN_PATH="$O" "$LEAN" --root=. -o "$O/$f.olean" "$f.lean"
done
echo "OK — all green"
# axiom footprint of the new emit-correctness theorems (must be ⊆ {propext, Quot.sound, Classical.choice}):
cat > "$O/AxC.lean" <<'EOF'
import Pancake.EmitCorrectCompose
open Pancake.EmitCorrectCompose
#print axioms refines_skip            -- SKIP  stage-kind
#print axioms refines_assign          -- ASSIGN (transform/set) stage-kind
#print axioms refines_store           -- STORE (memory-write) stage-kind
#print axioms refines_seq             -- SEQ (sequential composition) — the key lemma
#print axioms refines_cond            -- COND (branch) stage-kind
#print axioms refines_dec             -- DEC (lexical scope) wrapper
#print axioms emit_correct_generic    -- GENERIC emit over {prim, seq, cond}
#print axioms demoServe_emit_correct  -- a concrete 2-stage serve, compiled generically
#print axioms while_inv               -- reusable bounded-While rule (generalises scan_loop)
EOF
LEAN_PATH="$O" "$LEAN" --root=. "$O/AxC.lean"
