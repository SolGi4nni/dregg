#!/usr/bin/env bash
# Build the FULL gpui cockpit (the real gpui element-tree renderer on the
# `gpui_web` backend, wasm32 + WebGPU) into `pkg-gpui/`, exporting the
# `boot_cockpit` wasm entrypoint that `cockpit_gpui.html` imports.
#
# This is the bundle the doc's "the full gpui cockpit in a browser tab" claim
# stands on. The default `pkg/` and `pkg-release/` bundles export only the
# gpui-free `webimage_*` JSON skin; this one exports `boot_cockpit`.
#
#   ./build-gpui.sh            # release (default; far smaller wasm)
#   PROFILE=dev ./build-gpui.sh   # debug (huge wasm, faster compile)
#
# Output: starbridge-v2/web/pkg-gpui/{starbridge_web.js,starbridge_web_bg.wasm,...}
set -euo pipefail
cd "$(dirname "$0")"

PROFILE="${PROFILE:-release}"
OUT_DIR="pkg-gpui"
CRATE="starbridge_web"

if [[ "$PROFILE" == "release" ]]; then
  CARGO_PROFILE_FLAG="--release"
  TARGET_SUBDIR="release"
else
  CARGO_PROFILE_FLAG=""
  TARGET_SUBDIR="debug"
fi

echo "[1/3] cargo build ($PROFILE) → wasm32, features=gpui-web"
cargo build $CARGO_PROFILE_FLAG \
  --target wasm32-unknown-unknown \
  -p starbridge-web \
  --features gpui-web

# Cargo puts the wasm under starbridge-v2/target (the `starbridge-v2` member's
# own target dir), not the web crate's dir. Probe the known locations.
WASM_IN=""
for cand in \
  "../target/wasm32-unknown-unknown/${TARGET_SUBDIR}/${CRATE}.wasm" \
  "../../target/wasm32-unknown-unknown/${TARGET_SUBDIR}/${CRATE}.wasm" \
  "target/wasm32-unknown-unknown/${TARGET_SUBDIR}/${CRATE}.wasm" ; do
  if [[ -f "$cand" ]]; then WASM_IN="$cand"; break; fi
done
if [[ -z "$WASM_IN" ]]; then
  echo "ERROR: built ${CRATE}.wasm not found under ../target, ../../target, or ./target" >&2
  exit 1
fi
echo "      input: $WASM_IN ($(du -h "$WASM_IN" | cut -f1))"

echo "[2/3] wasm-bindgen --target web → $OUT_DIR (exports boot_cockpit)"
# NOTE: the wasm-bindgen CLI version MUST match the resolved `wasm-bindgen` crate
# (see starbridge-v2/Cargo.lock). A mismatch fails with a "schema version" error;
# fix with: cargo install -f wasm-bindgen-cli --version <locked-version>.
rm -rf "$OUT_DIR"
wasm-bindgen --target web --out-dir "$OUT_DIR" "$WASM_IN"

echo "[3/3] wasm-opt -Oz (if available)"
if command -v wasm-opt >/dev/null 2>&1; then
  WASM_BG="$OUT_DIR/${CRATE}_bg.wasm"
  before=$(du -h "$WASM_BG" | cut -f1)
  wasm-opt -Oz "$WASM_BG" -o "$WASM_BG.opt" && mv "$WASM_BG.opt" "$WASM_BG"
  echo "      wasm-opt: $before → $(du -h "$WASM_BG" | cut -f1)"
else
  echo "      wasm-opt not installed — skipping (bundle still loads, just larger)"
fi

echo
echo "DONE. $OUT_DIR/ produced. Verify it exports boot_cockpit:"
grep -o 'export function boot_cockpit' "$OUT_DIR/${CRATE}.js" || \
  echo "  WARNING: boot_cockpit export not found in $OUT_DIR/${CRATE}.js"
echo "Serve & open: python3 -m http.server 8099  →  http://localhost:8099/cockpit_gpui.html"
