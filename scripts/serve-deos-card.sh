#!/usr/bin/env bash
# Serve the LIVE browser-native deos: deos-js cards rendered via the gpui-free web renderer
# (deos-view/src/web.rs), firing REAL cap-gated verified turns over in-tab wasm executors
# (wasm/src/bindings_card.rs — the wasm analogs of the native Applet / inspector). Two pages
# are baked + served:
#
#   /                — the GALLERY / card-picker (plain HTML, no wasm): clickable tiles, one
#                      per live card — the discoverable front door that opens each card page.
#   /counter.html    — the COUNTER card (CardWorld): a `+1` click commits a SetField +
#                      IncrementNonce turn; the bound count re-paints from the committed ledger.
#   /inspector.html  — the REFLECTIVE-INSPECTOR card (InspectorWorld): a cockpit surface, in a
#                      TAB. The inspector card's view-tree (generated from a focused cell's REAL
#                      moldable faces — RawFields + Affordances, via deos-reflect) renders to
#                      HTML: a "Cell State" section (several live Bind rows + structural rows)
#                      and an "Affordances" section. Clicking an affordance (tick/add/score)
#                      fires a real cap-gated verified turn and the bound field re-paints, with
#                      a live balance/nonce/receipt readout.
#   /tally.html      — the TALLY-BOARD card (TallyWorld): the FULL ViewNode layout vocabulary
#                      (Row + Table + a multi-affordance row). A table of named tallies, each a
#                      row with a live count and +1/−1 buttons; every click fires a real
#                      cap-gated verified turn moving that one tally, and the row re-paints.
#
# Builds the wasm bundle, bakes the live pages, assembles a self-contained dist/, and serves it
# (each page is a module-import + a .wasm fetch — file:// is CORS-blocked, so it MUST be served
# over HTTP).
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
echo "=== Serving the LIVE deos cards at http://localhost:$PORT ==="
echo "  GALLERY   : http://localhost:$PORT/            — the card-picker (open a card below)"
echo "  COUNTER   : http://localhost:$PORT/counter.html   — click +1 (a real cap-gated verified turn)"
echo "  INSPECTOR : http://localhost:$PORT/inspector.html — a reflective cockpit surface; click an"
echo "              affordance (tick/add/score) → a real verified turn → the bound field re-paints."
echo "  TALLY     : http://localhost:$PORT/tally.html     — a table of named tallies (Row + Table);"
echo "              click +1/−1 on any row → a real verified turn moves that one tally."
echo "(Ctrl-C to stop.)"
cd "$DIST"
exec python3 -m http.server "$PORT"
