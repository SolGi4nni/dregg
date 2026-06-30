#!/usr/bin/env bash
# Assemble the GitHub Pages dist: a LAYERED site — a sober landing that opens into
# the live, in-browser, node-LESS deos.
#
# The landing (/) is plain static HTML on a shared green stylesheet (site/assets/).
# It explains what dregg/deos IS and links into the wonder layer. Every demo surface
# below runs CLIENT-SIDE in WebAssembly: the verified executor runs in the visitor's
# own tab, firing real cap-gated verified turns, leaving real receipts. No backend.
#
# Layout of the produced dist/:
#   /                  — the sober landing (what-is / play / quickstart / does / enables).
#                        Static HTML + site/assets/style.css (the salvaged green look).
#   /deos/             — the deos cockpit (the WebImage launcher): cells · inspector ·
#                        affordances · ocap web. Click an authorized affordance → a REAL
#                        verified turn in-tab. wasm: starbridge-v2/web (gpui-FREE skin).
#   /cockpit-gpui/     — the FULL gpui renderer on a WebGPU canvas (same in-tab executor).
#                        Heavier; needs WebGPU. wasm: starbridge-v2/web --features gpui-web.
#   /cards/            — the deos-js card gallery: counter · reflective inspector · tally
#                        board · kv-store · doc-collab. Each a real verified turn in-tab.
#                        wasm: wasm/ (the card/runtime bindings). Re-themed green.
#   /explorer/         — caps-as-rows: your capabilities expressed as the rows you may read
#                        (the browser twin of the pg-dregg cap-gated RLS cookbook).
#   /light-client/     — verify a whole finalized history in ONE recursive proof, in-tab,
#                        re-witnessing nothing. wasm: reuses /cards/pkg/dregg_wasm.js.
#   /atlas/            — the interactive atlas (the whole protocol + UI surfaces).
#
# Usage:
#   scripts/build-pages-dist.sh           # full build (all wasm + bake + assemble)
#   GPUI=0 scripts/build-pages-dist.sh    # skip the heavy gpui-web cockpit build
#   ATLAS=0 scripts/build-pages-dist.sh   # skip the atlas copy
#   REUSE_WASM=1 scripts/build-pages-dist.sh  # reuse already-built wasm pkgs + baked
#                                             # cards (fast local assembly/verify; no
#                                             # recompile). CI uses the full build.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
DIST="$ROOT/site/dist"
GPUI="${GPUI:-1}"
ATLAS="${ATLAS:-1}"
REUSE_WASM="${REUSE_WASM:-0}"

# Re-theme a baked deos-view card page from its fixed blue palette to the site's
# salvaged green palette (the cards are baked by a Rust example with an inline
# palette; we swap the tokens at assemble time so the gallery is of-a-piece).
greenify() {
  local f="$1"
  sed -i.bak \
    -e 's/#121317/#0a0f0d/g' \
    -e 's/#e6e7eb/#e4ddd0/g' \
    -e 's/#9aa0aa/#7a7265/g' \
    -e 's/#5b8cff/#5b8a5a/g' \
    -e 's/#2a2c33/#1a2d25/g' \
    -e 's/#181a20/#121b16/g' \
    "$f"
  rm -f "$f.bak"
}

echo "=== clean dist ==="
rm -rf "$DIST"
mkdir -p "$DIST"

# ── 0. THE LANDING (sober, static, green) ────────────────────────────────────────
echo "=== 0/6 the sober landing + shared green assets ==="
cp "$ROOT/site/root/index.html" "$DIST/index.html"
cp -R "$ROOT/site/assets" "$DIST/assets"
cp -R "$ROOT/site/explorer" "$DIST/explorer"
cp -R "$ROOT/site/light-client" "$DIST/light-client"
# dregg.works — the trustless-host front door + the injectable verify badge. Shipped
# under /dregg-works/ on the main site; the same dir is what deploys to the dregg.works
# apex (where verify-badge.js sits at the root as /verify-badge.js).
cp -R "$ROOT/site/dregg-works" "$DIST/dregg-works"
test -f "$DIST/explorer/index.html"
test -f "$DIST/light-client/index.html"
test -f "$DIST/dregg-works/index.html"
test -f "$DIST/dregg-works/verify-badge.js"

# ── 1. THE deos COCKPIT: the WebImage launcher (gpui-free skin), node-less ───────
echo "=== 1/6 build the WebImage cockpit wasm (starbridge-v2/web, default) ==="
if [ "$REUSE_WASM" = "0" ]; then
  wasm-pack build "$ROOT/starbridge-v2/web" --target web --out-dir pkg --release
fi
mkdir -p "$DIST/deos"
cp "$ROOT/site/deos/index.html" "$DIST/deos/index.html"
cp -R "$ROOT/starbridge-v2/web/pkg" "$DIST/deos/pkg"
test -s "$DIST/deos/pkg/starbridge_web_bg.wasm"

# ── 2. THE FULL gpui-web COCKPIT (WebGPU canvas), node-less ──────────────────────
# The gpui-web build pulls deos-matrix AND zed's sqlez — the one `links="sqlite3"`
# pair the workspace cannot link together (a documented narrow resolution wall,
# starbridge-v2/Cargo.toml "BLOCKER 1"). When it resolves it is the real full
# renderer; when the pair collides we still ship the rest of in-browser deos rather
# than failing the whole deploy. GPUI=1 REQUIRES it (fail-hard); default soft.
if [ "$GPUI" = "0" ]; then
  echo "=== 2/6 SKIPPED the gpui-web cockpit (GPUI=0) ==="
elif [ "$REUSE_WASM" = "1" ] && [ -d "$ROOT/starbridge-v2/web/pkg-gpui" ]; then
  echo "=== 2/6 reuse the prebuilt gpui-web cockpit ==="
  mkdir -p "$DIST/cockpit-gpui"
  cp "$ROOT/starbridge-v2/web/cockpit_gpui.html" "$DIST/cockpit-gpui/index.html"
  cp -R "$ROOT/starbridge-v2/web/pkg-gpui" "$DIST/cockpit-gpui/pkg-gpui"
elif [ "$REUSE_WASM" = "1" ]; then
  echo "=== 2/6 SKIPPED the gpui-web cockpit (REUSE_WASM, no prebuilt pkg-gpui) ==="
elif wasm-pack build "$ROOT/starbridge-v2/web" --target web --out-dir pkg-gpui --release -- --features gpui-web; then
  echo "=== 2/6 gpui-web cockpit built ==="
  mkdir -p "$DIST/cockpit-gpui"
  cp "$ROOT/starbridge-v2/web/cockpit_gpui.html" "$DIST/cockpit-gpui/index.html"
  cp -R "$ROOT/starbridge-v2/web/pkg-gpui" "$DIST/cockpit-gpui/pkg-gpui"
  test -s "$DIST/cockpit-gpui/pkg-gpui/starbridge_web_bg.wasm"
elif [ "${GPUI}" = "1" ]; then
  echo "=== 2/6 gpui-web cockpit FAILED and GPUI=1 (required) — failing ===" >&2
  exit 1
else
  echo "=== 2/6 gpui-web cockpit did not resolve (the matrix+zed sqlite pair) — shipping without it ===" >&2
fi

# ── 3. THE CARD GALLERY: the deos-js cards (wasm/ runtime bindings), node-less ────
echo "=== 3/6 build the card-world wasm (wasm/) + bake the gallery ==="
if [ "$REUSE_WASM" = "0" ]; then
  # A larger wasm stack gives the in-tab recursion verify (the light client's
  # verify-a-whole-history path) headroom — scoped to this build, not the native bake.
  RUSTFLAGS="-C link-arg=-zstack-size=33554432" wasm-pack build "$ROOT/wasm" --target web --out-dir pkg --release
  ( cd "$ROOT/deos-view" && cargo run -q --no-default-features --features web --example web_render_card )
fi
# The light-client page verifies a REAL pre-folded whole-history aggregate in-tab. The
# aggregate (site/light-client/history.json) is produced ONCE, off the verifier, by the
# heavy native prover and committed as a data artifact (CI does NOT re-fold it):
#   cargo run --release -p dregg-lightclient --bin produce_history_envelope --features prover -- 3 7 \
#     > site/light-client/history.json
# Regenerate it only if the WholeChainProofBytes wire format version bumps.
test -s "$ROOT/site/light-client/history.json"
mkdir -p "$DIST/cards"
for card in index counter inspector tally kvstore doccollab; do
  cp "$ROOT/deos-view/target/web-out/dist/$card.html" "$DIST/cards/$card.html"
  greenify "$DIST/cards/$card.html"
done
cp -R "$ROOT/wasm/pkg" "$DIST/cards/pkg"
test -s "$DIST/cards/pkg/dregg_wasm_bg.wasm"

# ── 4. THE ATLAS (relative paths, works at any subpath) ──────────────────────────
if [ "$ATLAS" = "1" ] && [ -d "$ROOT/dregg-atlas/site" ]; then
  echo "=== 4/6 bundle the atlas ==="
  mkdir -p "$DIST/atlas"
  cp -a "$ROOT/dregg-atlas/site/." "$DIST/atlas/"
  test -f "$DIST/atlas/index.html"
else
  echo "=== 4/6 SKIPPED the atlas ==="
fi

# ── 5. .nojekyll so /pkg/ + dotfiles ship verbatim ───────────────────────────────
echo "=== 5/6 finalize ==="
touch "$DIST/.nojekyll"

echo
echo "dist ready: $DIST"
echo "  /              -> the sober landing ($(du -sh "$DIST/index.html" | cut -f1))"
echo "  /deos/         -> $(du -sh "$DIST/deos" | cut -f1) (the WebImage cockpit)"
[ -d "$DIST/cockpit-gpui" ] && echo "  /cockpit-gpui/ -> $(du -sh "$DIST/cockpit-gpui" | cut -f1) (the full gpui-web cockpit)"
echo "  /cards/        -> $(du -sh "$DIST/cards" | cut -f1) (the deos-js card gallery)"
echo "  /explorer/     -> $(du -sh "$DIST/explorer" | cut -f1) (caps as rows)"
echo "  /light-client/ -> $(du -sh "$DIST/light-client" | cut -f1) (verify a whole history)"
[ -d "$DIST/atlas" ] && echo "  /atlas/        -> $(du -sh "$DIST/atlas" | cut -f1) (the atlas)"
echo "  total: $(find "$DIST" -type f | wc -l | tr -d ' ') files"
