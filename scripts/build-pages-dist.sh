#!/usr/bin/env bash
# Assemble the GitHub Pages dist that LAUNCHES YOU INTO IN-BROWSER deos, node-less.
#
# The site is no longer an Eleventy content site — it is a thin static launcher that
# drops a visitor straight into the live, in-browser, node-LESS deos. Every surface
# here runs CLIENT-SIDE in WebAssembly: the verified executor runs in the visitor's
# own tab, firing real cap-gated verified turns, leaving real receipts. No backend.
#
# Layout of the produced dist/:
#   /                  — the deos cockpit (the WebImage launcher): cells · inspector ·
#                        affordances · ocap web. You land IN deos; clicking an
#                        authorized affordance fires a REAL verified turn in-tab.
#                        wasm: starbridge-v2/web (the gpui-FREE model skin).
#   /cockpit-gpui/     — the FULL gpui renderer (the same one the native desktop draws
#                        with) on a WebGPU canvas, driving the SAME in-tab executor +
#                        the firmament editor + chat panes. Heavier; needs WebGPU.
#                        wasm: starbridge-v2/web --features gpui-web.
#   /cards/            — the deos-js card gallery: a counter, a reflective inspector, and a
#                        tally board (Row + Table + multi-affordance), each a real verified
#                        turn in-tab (the deos-view web renderer).
#                        wasm: wasm/ (the card/runtime bindings).
#   /atlas/            — the interactive atlas (the whole protocol + UI surfaces).
#
# Usage:
#   scripts/build-pages-dist.sh           # full build (all wasm + bake + assemble)
#   GPUI=0 scripts/build-pages-dist.sh    # skip the heavy gpui-web cockpit build
#   ATLAS=0 scripts/build-pages-dist.sh   # skip the atlas copy
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
DIST="$ROOT/site/dist"
GPUI="${GPUI:-1}"
ATLAS="${ATLAS:-1}"

echo "=== clean dist ==="
rm -rf "$DIST"
mkdir -p "$DIST"

# ── 1. THE ROOT: the WebImage cockpit (gpui-free model skin), node-less ──────────
echo "=== 1/5 build the WebImage cockpit wasm (starbridge-v2/web, default) ==="
wasm-pack build "$ROOT/starbridge-v2/web" --target web --out-dir pkg --release
cp "$ROOT/site/root/index.html" "$DIST/index.html"
cp -R "$ROOT/starbridge-v2/web/pkg" "$DIST/pkg"
test -s "$DIST/pkg/starbridge_web_bg.wasm"

# ── 2. THE FULL gpui-web COCKPIT (WebGPU canvas), node-less ──────────────────────
# The gpui-web build pulls deos-matrix (the chat pane) AND zed's sqlez — the one
# `links="sqlite3"` pair the workspace cannot link together (a documented, narrow
# resolution wall, starbridge-v2/Cargo.toml "BLOCKER 1"). When it resolves it is the
# real full renderer; when the pair collides we still ship the rest of in-browser deos
# (the root WebImage cockpit IS node-less deos) rather than failing the whole deploy.
# Set GPUI=1 to REQUIRE it (fail-hard); default attempts it soft.
if [ "$GPUI" = "0" ]; then
  echo "=== 2/5 SKIPPED the gpui-web cockpit (GPUI=0) ==="
elif wasm-pack build "$ROOT/starbridge-v2/web" --target web --out-dir pkg-gpui --release -- --features gpui-web; then
  echo "=== 2/5 gpui-web cockpit built ==="
  mkdir -p "$DIST/cockpit-gpui"
  cp "$ROOT/starbridge-v2/web/cockpit_gpui.html" "$DIST/cockpit-gpui/index.html"
  cp -R "$ROOT/starbridge-v2/web/pkg-gpui" "$DIST/cockpit-gpui/pkg-gpui"
  test -s "$DIST/cockpit-gpui/pkg-gpui/starbridge_web_bg.wasm"
elif [ "${GPUI}" = "1" ]; then
  echo "=== 2/5 gpui-web cockpit FAILED and GPUI=1 (required) — failing ===" >&2
  exit 1
else
  echo "=== 2/5 gpui-web cockpit did not resolve (the matrix+zed sqlite pair) — shipping without it ===" >&2
fi

# ── 3. THE CARD GALLERY: the deos-js cards (wasm/ runtime bindings), node-less ────
echo "=== 3/5 build the card-world wasm (wasm/) + bake the gallery ==="
wasm-pack build "$ROOT/wasm" --target web --out-dir pkg --release
( cd "$ROOT/deos-view" && cargo run -q --no-default-features --features web --example web_render_card )
mkdir -p "$DIST/cards"
cp "$ROOT/deos-view/target/web-out/dist/index.html" "$DIST/cards/index.html"
cp "$ROOT/deos-view/target/web-out/dist/counter.html" "$DIST/cards/counter.html"
cp "$ROOT/deos-view/target/web-out/dist/inspector.html" "$DIST/cards/inspector.html"
cp "$ROOT/deos-view/target/web-out/dist/tally.html" "$DIST/cards/tally.html"
cp -R "$ROOT/wasm/pkg" "$DIST/cards/pkg"
test -s "$DIST/cards/pkg/dregg_wasm_bg.wasm"

# ── 4. THE ATLAS (relative paths, works at any subpath) ──────────────────────────
if [ "$ATLAS" = "1" ] && [ -d "$ROOT/dregg-atlas/site" ]; then
  echo "=== 4/5 bundle the atlas ==="
  mkdir -p "$DIST/atlas"
  cp -a "$ROOT/dregg-atlas/site/." "$DIST/atlas/"
  test -f "$DIST/atlas/index.html"
else
  echo "=== 4/5 SKIPPED the atlas ==="
fi

# ── 5. .nojekyll so /pkg/ + dotfiles ship verbatim ───────────────────────────────
echo "=== 5/5 finalize ==="
touch "$DIST/.nojekyll"

echo
echo "dist ready: $DIST"
echo "  /              -> $(du -sh "$DIST/index.html" 2>/dev/null | cut -f1) launcher + $(du -sh "$DIST/pkg" | cut -f1) wasm (the WebImage cockpit)"
[ -d "$DIST/cockpit-gpui" ] && echo "  /cockpit-gpui/ -> $(du -sh "$DIST/cockpit-gpui" | cut -f1) (the full gpui-web cockpit)"
echo "  /cards/        -> $(du -sh "$DIST/cards" | cut -f1) (the deos-js card gallery)"
[ -d "$DIST/atlas" ] && echo "  /atlas/        -> $(du -sh "$DIST/atlas" | cut -f1) (the atlas)"
