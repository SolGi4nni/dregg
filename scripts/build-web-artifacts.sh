#!/usr/bin/env bash
# Build browser-facing artifacts in dependency order:
#   1. wasm/pkg for the site runtime
#   2. extension/dist packages and extension WASM
#   3. site/dist, including fresh wasm/pkg and extension downloads
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
MANIFEST="$ROOT/site/dist/artifacts-manifest.json"

sha256_file() {
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum "$1" | awk '{print $1}'
  else
    shasum -a 256 "$1" | awk '{print $1}'
  fi
}

echo "=== Building wasm/pkg ==="
wasm-pack build "$ROOT/wasm" --target web --out-dir pkg --release

# ── STRIP THE WASM NAME SECTION ───────────────────────────────────────────────
# `wasm-pack --release` does NOT post-process the bundle here: the committed artifact's `producers`
# section reads `rustc / walrus / wasm-bindgen` and nothing else, so no wasm-opt has ever run on it.
# What that leaves in the file the browser downloads (measured 2026-07-25 on the 61,108,004-byte
# bundle) is 9,866,160 bytes — 16.1% — of `custom:name`, i.e. debug symbol NAMES, shipped to every
# visitor of the hero CTA.
#
# `--strip-debug` removes exactly that section: 61,108,004 -> 51,246,200 on disk, and 3,738,736 ->
# 3,426,418 over the wire once the server's `br` layer has it.
#
# DELIBERATELY NOT `-Oz` / `-O2` / `opt-level = "z"`. That is the obvious next knob and it is the
# WRONG one here — measured on this same bundle, `-Oz` beats `--strip-debug` on disk (49,060,811 vs
# 51,246,200) and LOSES on the wire (br 3,867,836 vs 3,426,418, ~13% worse), because its size
# rewrites destroy more compressibility than they remove bytes. The wire number is the one a visitor
# pays. Re-measure before adding an optimisation pass here; do not assume smaller-on-disk is cheaper.
#
# No silent fallback: a missing binaryen FAILS the build rather than quietly shipping the 9.9 MiB of
# symbol names. Set DREGG_WASM_KEEP_NAMES=1 to deliberately keep them (a debuggable build with
# readable browser stack traces).
if [ "${DREGG_WASM_KEEP_NAMES:-0}" = "1" ]; then
  echo "=== Skipping wasm strip (DREGG_WASM_KEEP_NAMES=1; names kept for debuggable traces) ==="
else
  if ! command -v wasm-opt >/dev/null 2>&1; then
    echo "ERROR: wasm-opt (binaryen) not found, so the wasm name section cannot be stripped." >&2
    echo "       Install it (brew install binaryen) or set DREGG_WASM_KEEP_NAMES=1 to ship names." >&2
    exit 1
  fi
  echo "=== Stripping wasm debug names ==="
  WASM="$ROOT/wasm/pkg/dregg_wasm_bg.wasm"
  before=$(wc -c <"$WASM" | tr -d ' ')
  wasm-opt --strip-debug --strip-producers -o "$WASM.stripped" "$WASM"
  mv "$WASM.stripped" "$WASM"
  after=$(wc -c <"$WASM" | tr -d ' ')
  echo "    dregg_wasm_bg.wasm: $before -> $after bytes"
fi

echo "=== Refreshing site/pkg from wasm/pkg ==="
rm -rf "$ROOT/site/pkg/dregg_wasm"* "$ROOT/site/pkg/package.json" "$ROOT/site/pkg/.gitignore"
cp -R "$ROOT/wasm/pkg/." "$ROOT/site/pkg/"

echo "=== Building extension scripts and packages ==="
(cd "$ROOT/extension" && npm run build && ./build.sh package)

echo "=== Publishing extension downloads into site/extension ==="
cp "$ROOT/extension/dist/dregg-cipherclerk-chrome.zip" "$ROOT/site/extension/dregg-cipherclerk.zip"
cp "$ROOT/extension/dist/dregg-cipherclerk-chrome.zip" "$ROOT/site/extension/dregg-wallet.zip"
cp "$ROOT/extension/dist/dregg-cipherclerk-firefox.xpi" "$ROOT/site/extension/dregg-cipherclerk-firefox.xpi"

echo "=== Building site/dist ==="
(cd "$ROOT/site" && npm run build)

echo "=== Writing artifact manifest ==="
cat >"$MANIFEST" <<JSON
{
  "schema": "dregg-web-artifacts-v1",
  "built_at": "$(date -u +%Y-%m-%dT%H:%M:%SZ)",
  "artifacts": {
    "pkg/dregg_wasm.js": {
      "bytes": $(wc -c <"$ROOT/site/dist/pkg/dregg_wasm.js" | tr -d ' '),
      "sha256": "$(sha256_file "$ROOT/site/dist/pkg/dregg_wasm.js")"
    },
    "pkg/dregg_wasm_bg.wasm": {
      "bytes": $(wc -c <"$ROOT/site/dist/pkg/dregg_wasm_bg.wasm" | tr -d ' '),
      "sha256": "$(sha256_file "$ROOT/site/dist/pkg/dregg_wasm_bg.wasm")"
    },
    "extension/dregg-cipherclerk.zip": {
      "bytes": $(wc -c <"$ROOT/site/dist/extension/dregg-cipherclerk.zip" | tr -d ' '),
      "sha256": "$(sha256_file "$ROOT/site/dist/extension/dregg-cipherclerk.zip")"
    },
    "extension/dregg-cipherclerk-firefox.xpi": {
      "bytes": $(wc -c <"$ROOT/site/dist/extension/dregg-cipherclerk-firefox.xpi" | tr -d ' '),
      "sha256": "$(sha256_file "$ROOT/site/dist/extension/dregg-cipherclerk-firefox.xpi")"
    }
  }
}
JSON

echo "=== Web artifacts ready ==="
echo "Site:      $ROOT/site/dist"
echo "WASM:      $ROOT/site/dist/pkg/dregg_wasm.js"
echo "Extension: $ROOT/site/dist/extension/dregg-cipherclerk.zip"
echo "Manifest:  $MANIFEST"
