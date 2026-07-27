#!/usr/bin/env bash
# Build the shared serve-spec library to an olean and print its axiom footprint.
# Raw-lean build (no lake, no external package) — same mechanism the translator
# tree uses. Run under swarm-build on the box:
#   SWARM_MEM_MAX=24G swarm-build bash -c "cd /home/hbox/dev/dregg-serve-spec && bash build_servespec.sh"
set -euo pipefail
cd "$(dirname "$0")"
LEAN="${LEAN:-$HOME/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lean}"
O="${SERVESPEC_OLEANS:-$HOME/.cache/servespec-oleans}"
mkdir -p "$O"
echo "building ServeSpec ..."
rm -f "$O/ServeSpec.olean"
LEAN_PATH="$O" "$LEAN" --root=. -o "$O/ServeSpec.olean" "ServeSpec.lean"
echo "OK — ServeSpec green, olean at $O/ServeSpec.olean"
