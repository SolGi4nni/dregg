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

# ── STEP 1: THE BROWSER BUNDLE ────────────────────────────────────────────────
# Delegated, deliberately. This step used to be an inline `wasm-pack` invocation here AND
# a differently-flagged one in `deploy/games/deploy-hbox.sh` AND a third in the workflows,
# and the flag pair they disagreed about (`getrandom_backend` vs the stack size — env
# RUSTFLAGS overrides `.cargo/config.toml` OUTRIGHT rather than merging) is exactly the
# kind of divergence you cannot see by looking at a bundle. `scripts/build-descent-wasm.sh`
# is now the ONE build: the flags, the conditional name-section strip, the provenance
# stamp, and the freshness gate that proves the result before anything ships it.
bash "$ROOT/scripts/build-descent-wasm.sh"

echo "=== Refreshing site/pkg from wasm/pkg ==="
# `mkdir -p` first: `site/pkg` is gitignored, so on a fresh checkout it does not exist
# and `cp -R src/. dest/` fails outright rather than creating it.
mkdir -p "$ROOT/site/pkg"
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
