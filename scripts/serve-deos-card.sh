#!/usr/bin/env bash
# Serve the LIVE browser-native deos: a deos-js card rendered via the gpui-free web
# renderer (deos-view/src/web.rs), firing REAL cap-gated verified turns over an in-tab
# wasm executor (wasm/src/bindings_card.rs's CardWorld — the wasm analog of the native
# Applet). A `+1` click commits a SetField + IncrementNonce turn and the bound count
# re-paints from the committed ledger, with a live receipt count.
#
# Builds the wasm bundle, bakes the live page, assembles a self-contained dist/, and
# serves it (the page is a module-import + a .wasm fetch — file:// is CORS-blocked, so it
# MUST be served over HTTP).
#
#   scripts/serve-deos-card.sh           # build + bake + serve on :8000
#   scripts/serve-deos-card.sh --no-serve  # build + bake only (print the dist path)
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PORT="${PORT:-8000}"
DIST="$ROOT/deos-view/target/web-out/dist"

echo "=== 1/3 Building the playground wasm bundle (wasm-pack, --target web) ==="
wasm-pack build "$ROOT/wasm" --target web --out-dir pkg --release

echo "=== 2/3 Baking the live card page (gpui-free web renderer) ==="
( cd "$ROOT/deos-view" && cargo run --no-default-features --features web --example web_render_card )

echo "=== 3/3 Assembling the self-contained dist ==="
rm -rf "$DIST/pkg"
cp -R "$ROOT/wasm/pkg" "$DIST/pkg"
echo "dist ready: $DIST"
ls -la "$DIST"

if [[ "${1:-}" == "--no-serve" ]]; then
  echo "Skipping serve. Open it with:  (cd '$DIST' && python3 -m http.server $PORT)"
  exit 0
fi

echo
echo "=== Serving the LIVE deos card at http://localhost:$PORT ==="
echo "Open http://localhost:$PORT and click +1 — each click is a real cap-gated verified turn."
echo "(Ctrl-C to stop.)"
cd "$DIST"
exec python3 -m http.server "$PORT"
