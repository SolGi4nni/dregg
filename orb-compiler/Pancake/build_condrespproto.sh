#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
LEAN="${LEAN:-$HOME/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lean}"
O="${STAGEPROG2_OLEANS:-$HOME/.cache/stageprog2-oleans}"
mkdir -p "$O/Pancake"
rm -f "$O/Pancake/CondRespProto.olean"
echo "building Pancake/CondRespProto ..."
LEAN_PATH="$O" "$LEAN" --root=. -o "$O/Pancake/CondRespProto.olean" Pancake/CondRespProto.lean
echo "OK -- green"
