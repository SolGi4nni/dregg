#!/usr/bin/env bash
# Launcher for the dregg-mcp server (drives the starbridge-v2 live verified
# image). Built with native-full so its world matches the rendered cockpit
# (the lean embedded-executor build seeds a degenerate 4-cell world — see
# HORIZONLOG cell-census finding). Screenshots use the same binary's sibling
# starbridge-v2 headless-render bake.
set -euo pipefail
DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
BIN="$DIR/target/release/dregg-mcp"
if [ ! -x "$BIN" ]; then
  echo "dregg-mcp: building (first run)…" >&2
  ( cd "$DIR" && cargo build --release --features native-full --bin dregg-mcp ) >&2
fi
exec "$BIN" "$@"
