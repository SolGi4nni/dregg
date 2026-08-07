#!/usr/bin/env bash
# Build, validate, and package the Dragon's Egg Cipherclerk extension.
#
# Usage:
#   ./build.sh          — Build WASM + validate + package
#   ./build.sh wasm     — Only build WASM
#   ./build.sh package  — Only validate + package (skip WASM build)
#   ./build.sh lint     — Run web-ext lint (requires: npm i -g web-ext)
#
# Requirements:
#   - cargo, wasm-bindgen-cli (cargo install wasm-bindgen-cli)
#   - zip (for .zip/.xpi packaging)
#   - web-ext (optional, for Mozilla extension linting)
#
# ⚑ THIS BUILDS THE SECOND OF THIS REPO'S TWO BROWSER BUNDLES — AND IT IS NOT A COPY
# ----------------------------------------------------------------------------------
# `wasm/pkg/dregg_wasm.js` (built by `scripts/build-descent-wasm.sh`, `wasm-pack --target
# web`) is an ES MODULE: it opens `import * as import1 from "./snippets/…"`. The bundle
# HERE is `wasm-bindgen --target no-modules`: an IIFE that defines a global
# `wasm_bindgen`, because `background.ts` loads it with `importScripts` inside an MV3
# service worker, where an ES module and a `require()` both fail outright. So the two
# glues are DIFFERENT ARTIFACTS from the same crate, and copying one over the other
# breaks at load rather than at build. Nothing may "sync" them.
#
# What they must NOT differ in is the `RUSTFLAGS` pair. This script used to run a bare
# `cargo build` with none, so the shipped blob got `getrandom_backend` from
# `.cargo/config.toml` (and only while the CWD sat inside the repo) and NEVER the 32 MiB
# stack. Both now come from `scripts/wasm-build-flags.sh`, the one definition — which also
# means this build and the `wasm-pack` one share compiled artifacts in `wasm/target`
# instead of each forcing a full recompile of the other's.
#
# ⚑ AND THE ARTIFACT IS GATED NOW. Until 2026-08-07 nothing refreshed this bundle in the
# pipeline and nothing checked it: `scripts/build-web-artifacts.sh` ran `./build.sh
# package` only, so it packaged whatever glue happened to be committed, and
# `check-wasm-freshness.sh` was pointed at `wasm/pkg` — one artifact away. The extension
# shipped a glue with ZERO `build_poa_signal_claim_turn` while `wasm/src/lib.rs` exported
# one, and `background.ts` refused every judged PoA Signal claim on live beta.
#
# `build_wasm` now stamps `dregg-wasm-provenance.json`, the packages CARRY it, and
# `package` REFUSES to leave a package the gate calls stale.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
WASM_CRATE="$PROJECT_ROOT/wasm"
# The wasm/ crate is a STANDALONE cargo workspace (its Cargo.toml declares an
# empty `[workspace]`), so cargo builds it into `wasm/target/`, NOT the repo-root
# `target/`. Read the artifact from the wasm crate's own target dir.
TARGET_DIR="$WASM_CRATE/target"
WASM_OUT="$TARGET_DIR/wasm32-unknown-unknown/release/dregg_wasm.wasm"
DIST_DIR="$SCRIPT_DIR/dist"

COMMAND="${1:-all}"
CHROME_PACKAGE_NAME="dregg-cipherclerk-chrome.zip"
FIREFOX_PACKAGE_NAME="dregg-cipherclerk-firefox.xpi"

# ---------------------------------------------------------------------------
# Step 1: Build WASM
# ---------------------------------------------------------------------------

build_wasm() {
  # THE FLAG PAIR, from the one definition. `.cargo/config.toml` supplies only the
  # getrandom backend, and only when cargo's CWD walk happens to reach the repo root;
  # exporting RUSTFLAGS here makes both flags unconditional AND makes this build's cargo
  # fingerprint match `scripts/build-descent-wasm.sh`'s, so the two bundles share one
  # compile instead of invalidating each other.
  # shellcheck source=../scripts/wasm-build-flags.sh
  . "$PROJECT_ROOT/scripts/wasm-build-flags.sh"

  echo "[1/4] Building dregg-wasm (release, wasm32-unknown-unknown)..."
  echo "      RUSTFLAGS: $DREGG_WASM_RUSTFLAGS"
  RUSTFLAGS="$DREGG_WASM_RUSTFLAGS" cargo build \
    --manifest-path "$WASM_CRATE/Cargo.toml" \
    -p dregg-wasm \
    --target wasm32-unknown-unknown \
    --release

  if [ ! -f "$WASM_OUT" ]; then
    echo "ERROR: Expected output not found at $WASM_OUT"
    exit 1
  fi

  echo "[2/4] Running wasm-bindgen (--target no-modules for Firefox compat)..."
  wasm-bindgen "$WASM_OUT" \
    --out-dir "$SCRIPT_DIR" \
    --target no-modules \
    --no-typescript \
    --omit-default-module-path

  # ----- Inline JS snippets into the no-modules glue --------------------------
  # When a wasm dependency carries an `#[wasm_bindgen(inline_js = ...)]` shim
  # (e.g. biscuit-auth's `performance_now`), wasm-bindgen's `no-modules` target
  # emits a `require("./snippets/.../inline0.js")` call. `require` does not exist
  # in a browser extension service worker / classic worker, so the glue would
  # throw at load. We rewrite each such `require(...)` to inline the snippet's
  # exported functions directly, then delete the now-unreferenced snippets dir.
  # This keeps the extension a flat, self-contained bundle (glue + .wasm only).
  if [ -d "$SCRIPT_DIR/snippets" ]; then
    echo "  Inlining wasm-bindgen JS snippets (no-modules service-worker compat)..."
    node "$SCRIPT_DIR/inline-snippets.mjs" "$SCRIPT_DIR/dregg_wasm.js" "$SCRIPT_DIR/snippets"
    rm -rf "$SCRIPT_DIR/snippets"
  fi

  # ----- Optimize the wasm blob ----------------------------------------------
  optimize_wasm

  if [ -f "$SCRIPT_DIR/dregg_wasm_bg.wasm" ] && [ -f "$SCRIPT_DIR/dregg_wasm.js" ]; then
    WASM_SIZE=$(wc -c < "$SCRIPT_DIR/dregg_wasm_bg.wasm" | tr -d ' ')
    echo "  WASM output:"
    echo "    $SCRIPT_DIR/dregg_wasm.js"
    echo "    $SCRIPT_DIR/dregg_wasm_bg.wasm ($WASM_SIZE bytes)"
  else
    echo "ERROR: wasm-bindgen did not produce expected outputs."
    ls -la "$SCRIPT_DIR"/dregg_wasm* 2>/dev/null || true
    exit 1
  fi

  # ── STAMP WHAT THIS BUNDLE WAS BUILT FROM ───────────────────────────────────
  # AFTER the last pass that rewrites bytes (wasm-opt above), or the record describes a
  # file that no longer exists. Without this the bundle is UNGRADEABLE, which is what it
  # was for as long as it has existed.
  echo "  Recording bundle provenance..."
  bash "$PROJECT_ROOT/scripts/wasm-bundle-provenance.sh" "$SCRIPT_DIR" no-modules

  # And PROVE it here, in the build that made it — a gate that only runs somewhere else is
  # a gate the build can walk past.
  bash "$PROJECT_ROOT/scripts/check-wasm-freshness.sh" "$SCRIPT_DIR" --kind no-modules
}

# ---------------------------------------------------------------------------
# Shrink the wasm blob with wasm-opt -Oz (MED-2).
#
# `no-modules` does not run wasm-opt the way `wasm-pack` does, leaving a large
# unoptimized blob. `-Oz` optimizes aggressively for size — important for an
# MV3 extension whose service worker is killed/woken frequently (every wake
# re-instantiates the wasm) and for store size limits. Installs binaryen via
# brew if it is missing and brew is available.
#
# ⚑ CALLED FROM `build_wasm` ONLY, AND THAT IS LOAD-BEARING. `package_extension` used to
# call it too, "idempotent if already -Oz'd" — and it is not idempotent in the way that
# mattered: it `mv`s a fresh file over `dregg_wasm_bg.wasm` on every run, so the blob's
# MTIME ADVANCED on every packaging while its CONTENT stayed as old as the last real wasm
# build. That is how `extension/dregg_wasm_bg.wasm` read "modified today" on 2026-08-07
# while carrying an Aug-1 engine, and it is why the freshness gate hashes instead of
# stat()ing. Re-running it after the provenance stamp would also invalidate the record it
# just wrote.
# ---------------------------------------------------------------------------

optimize_wasm() {
  local wasm="$SCRIPT_DIR/dregg_wasm_bg.wasm"
  [ -f "$wasm" ] || return 0

  if ! command -v wasm-opt >/dev/null 2>&1; then
    if command -v brew >/dev/null 2>&1; then
      echo "  wasm-opt not found — installing binaryen via brew..."
      brew install binaryen >/dev/null 2>&1 || true
    fi
  fi

  if command -v wasm-opt >/dev/null 2>&1; then
    local before after
    before=$(wc -c < "$wasm" | tr -d ' ')
    echo "  Optimizing dregg_wasm_bg.wasm with wasm-opt -Oz (was $before bytes)..."
    if wasm-opt -Oz "$wasm" -o "$wasm.opt" 2>/dev/null; then
      mv "$wasm.opt" "$wasm"
      after=$(wc -c < "$wasm" | tr -d ' ')
      echo "  wasm-opt -Oz done: $before -> $after bytes."
    else
      rm -f "$wasm.opt"
      echo "  WARNING: wasm-opt failed; shipping the current blob."
    fi
  else
    echo "  WARNING: wasm-opt unavailable (install binaryen) — shipping unoptimized blob."
  fi
}

# ---------------------------------------------------------------------------
# Step 2: Validate manifest
# ---------------------------------------------------------------------------

validate_one_manifest() {
  local manifest_path="$1"
  local manifest_name="$2"

  if [ ! -f "$manifest_path" ]; then
    echo "ERROR: $manifest_name not found"
    exit 1
  fi

  # Check JSON is well-formed.
  if ! python3 -c "import json; json.load(open('$manifest_path'))" 2>/dev/null; then
    if ! node -e "JSON.parse(require('fs').readFileSync('$manifest_path','utf8'))" 2>/dev/null; then
      echo "ERROR: $manifest_name is not valid JSON"
      exit 1
    fi
  fi

  # Check required fields.
  local manifest_version
  manifest_version=$(python3 -c "import json; print(json.load(open('$manifest_path')).get('manifest_version',''))" 2>/dev/null || echo "")
  if [ "$manifest_version" != "3" ]; then
    echo "WARNING: $manifest_name manifest_version is not 3 (got: $manifest_version)"
  fi

  # Check no "type": "module" in background (Firefox compat).
  if grep -q '"type".*:.*"module"' "$manifest_path"; then
    echo "ERROR: $manifest_name contains \"type\": \"module\" in background — Firefox incompatible"
    exit 1
  fi
}

validate_manifest() {
  echo "[3/4] Validating manifests..."

  validate_one_manifest "$SCRIPT_DIR/manifest.json" "manifest.json (Chrome)"
  validate_one_manifest "$SCRIPT_DIR/manifest-firefox.json" "manifest-firefox.json (Firefox)"

  # Check all referenced files exist.
  local missing=0
  for file in dist/background.js dist/content.js dist/page.js popup.html dist/popup-script.js settings.html settings-script.js; do
    if [ ! -f "$SCRIPT_DIR/$file" ]; then
      echo "  WARNING: Referenced file missing: $file"
      missing=$((missing + 1))
    fi
  done

  if [ "$missing" -eq 0 ]; then
    echo "  Both manifests valid. All referenced files present."
  else
    echo "  Manifests valid but $missing referenced file(s) missing."
  fi
}

# ---------------------------------------------------------------------------
# Step 3: Package extension
# ---------------------------------------------------------------------------

package_extension() {
  echo "[4/4] Packaging extension..."

  # Rebuild the TS bundle so a stale dist/ can never be shipped (LOW finding).
  if [ -f "$SCRIPT_DIR/package.json" ]; then
    echo "  Rebuilding TS bundle (npm run build)..."
    (cd "$SCRIPT_DIR" && npm run build)
  fi

  # NOTHING HERE REWRITES THE BUNDLE. `optimize_wasm` used to run at this point and its
  # only observable effect on an already-optimized blob was to refresh the mtime — see its
  # header. Packaging reads the artifact; it does not produce it.

  mkdir -p "$DIST_DIR"

  # Base files to include in every package.
  # P2-1: ship only the TS-compiled dist/ scripts for background/content/page/popup.
  # Static popup HTML + their dedicated JS still ship from the root (they're not
  # TS-built today).
  local BASE_FILES=(
    dist/background.js
    dist/content.js
    dist/page.js
    popup.html
    dist/popup-script.js
    settings.html
    settings-script.js
    provision.html
    provision.js
    recovery.html
    recovery.js
    confirm-intent.html
    confirm-intent-script.js
    disclosure-picker.html
    disclosure-picker.js
    origin-permission.html
    origin-permission-script.js
    share-capability.html
    share-capability.js
    bip39_english.txt
    icons/icon-16.png
    icons/icon-32.png
    icons/icon-48.png
    icons/icon-128.png
  )

  # THE WASM BUNDLE — glue, blob, AND the record that describes them.
  #
  # The provenance file ships INSIDE the package on purpose: the artifact a store receives
  # and a user installs is the .zip, not this directory, and an artifact that cannot
  # describe itself cannot be graded after it leaves. `scripts/check-wasm-freshness.sh`
  # takes the .zip/.xpi directly and reads these three members out of it.
  #
  # NOT CONDITIONAL ANY MORE. The two `if [ -f ]` guards that stood here meant a package
  # built with no engine at all was a SUCCESSFUL build producing a silently crippled
  # extension. A missing bundle is a build failure.
  for f in dregg_wasm.js dregg_wasm_bg.wasm dregg-wasm-provenance.json; do
    if [ ! -f "$SCRIPT_DIR/$f" ]; then
      echo "ERROR: $f is missing — this package would ship without a working crypto core."
      echo "       Build it first:  ./build.sh wasm"
      exit 1
    fi
    BASE_FILES+=("$f")
  done

  # Build the file list (only include files that actually exist).
  local EXISTING_FILES=()
  for f in "${BASE_FILES[@]}"; do
    if [ -f "$SCRIPT_DIR/$f" ]; then
      EXISTING_FILES+=("$f")
    fi
  done

  # Remove any prior packages so the zip is rebuilt cleanly (no stale members).
  rm -f "$DIST_DIR/$CHROME_PACKAGE_NAME" "$DIST_DIR/$FIREFOX_PACKAGE_NAME"

  # --- Chrome package (.zip) ---
  local ZIP_NAME="$CHROME_PACKAGE_NAME"
  local CHROME_FILES=("${EXISTING_FILES[@]}")
  CHROME_FILES+=(manifest.json)
  (cd "$SCRIPT_DIR" && zip -q -r "$DIST_DIR/$ZIP_NAME" "${CHROME_FILES[@]}")
  local ZIP_SIZE
  ZIP_SIZE=$(wc -c < "$DIST_DIR/$ZIP_NAME" | tr -d ' ')
  echo "  Chrome package: $DIST_DIR/$ZIP_NAME ($ZIP_SIZE bytes)"

  # --- Firefox package (.xpi) ---
  # Use manifest-firefox.json renamed to manifest.json inside the package.
  local XPI_NAME="$FIREFOX_PACKAGE_NAME"
  local XPI_DIR="$DIST_DIR/firefox-tmp-$$"
  mkdir -p "$XPI_DIR"
  for f in "${EXISTING_FILES[@]}"; do
    if [ -f "$SCRIPT_DIR/$f" ]; then
      # Preserve subdirectory structure (e.g. dist/)
      local dir
      dir=$(dirname "$f")
      mkdir -p "$XPI_DIR/$dir"
      cp "$SCRIPT_DIR/$f" "$XPI_DIR/$f"
    fi
  done
  cp "$SCRIPT_DIR/manifest-firefox.json" "$XPI_DIR/manifest.json"
  (cd "$XPI_DIR" && zip -q -r "$DIST_DIR/$XPI_NAME" .)
  rm -rf "$XPI_DIR"
  local XPI_SIZE
  XPI_SIZE=$(wc -c < "$DIST_DIR/$XPI_NAME" | tr -d ' ')
  echo "  Firefox package: $DIST_DIR/$XPI_NAME ($XPI_SIZE bytes)"

  # ── GRADE THE THING THAT ACTUALLY SHIPS ─────────────────────────────────────
  # Not the source, not this directory: the archive. On 2026-08-07 this directory and the
  # archive were both a week stale and every instrument in the repo was pointed at
  # `wasm/pkg`, so nothing said a word while beta refused every judged claim.
  #
  # `DREGG_WASM_SKIP_VERIFY=1` skips it, the same named escape `build-descent-wasm.sh`
  # offers, and it says so out loud. CI and `scripts/local-gates.sh` never set it.
  if [ "${DREGG_WASM_SKIP_VERIFY:-0}" = "1" ]; then
    echo ""
    echo "  !! Skipping the package freshness gate (DREGG_WASM_SKIP_VERIFY=1)."
    echo "  !! These packages are UNVERIFIED: nothing has checked that their engine matches"
    echo "  !! this tree. Do not ship them."
  else
    echo ""
    echo "[5/5] Grading the packaged bundle..."
    bash "$PROJECT_ROOT/scripts/check-wasm-freshness.sh" \
      "$DIST_DIR/$CHROME_PACKAGE_NAME" --kind no-modules
    bash "$PROJECT_ROOT/scripts/check-wasm-freshness.sh" \
      "$DIST_DIR/$FIREFOX_PACKAGE_NAME" --kind no-modules
  fi

  echo ""
  echo "Done. Packages in: $DIST_DIR/"
}

# ---------------------------------------------------------------------------
# Step 4 (optional): Lint with web-ext
# ---------------------------------------------------------------------------

lint_extension() {
  if ! command -v web-ext &>/dev/null; then
    echo "web-ext not found. Install with: npm install -g web-ext"
    echo "Skipping lint."
    return 0
  fi

  echo "Running web-ext lint..."
  web-ext lint --source-dir "$SCRIPT_DIR" --self-hosted || true
}

# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

case "$COMMAND" in
  wasm)
    build_wasm
    ;;
  package)
    validate_manifest
    package_extension
    ;;
  lint)
    lint_extension
    ;;
  all)
    build_wasm
    validate_manifest
    package_extension
    echo ""
    echo "Extension built and packaged successfully."
    echo "Load in Chrome: chrome://extensions > Load unpacked > $SCRIPT_DIR"
    echo "Load in Firefox: about:debugging > This Firefox > Load Temporary Add-on > $DIST_DIR/$FIREFOX_PACKAGE_NAME"
    ;;
  *)
    echo "Usage: $0 [wasm|package|lint|all]"
    exit 1
    ;;
esac
