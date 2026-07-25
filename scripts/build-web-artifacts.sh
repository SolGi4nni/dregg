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

# ── THE FLAGS, IN FULL, IN ONE PLACE ──────────────────────────────────────────
# `-C link-arg=-zstack-size=33554432`: 32 MiB of linear-memory stack. The recursion
# verifier the light-client-in-the-tab runs overflows wasm's 1 MiB default. Every OTHER
# path that builds this bundle already sets it (`deploy/games/deploy-hbox.sh`,
# `scripts/build-pages-dist.sh`, `.github/workflows/{pages,ci,publish-sdk-ts}.yml`) —
# this script, the one actually named "build web artifacts", did not, so it produced an
# artifact that DIFFERED from every deployed one in a way nothing would notice until a
# tab blew its stack.
#
# `--cfg getrandom_backend="wasm_js"`: repeated here, and this is the subtle half.
# `.cargo/config.toml` sets it under `[target.wasm32-unknown-unknown] rustflags`, and
# cargo does NOT merge that with the `RUSTFLAGS` environment variable — env WINS
# OUTRIGHT and the config flags are dropped entirely. So the moment any build path
# exports `RUSTFLAGS` for the stack size, it silently deletes the getrandom backend
# selection, and getrandom 0.3/0.4 refuse to compile for wasm32 without it. Both flags
# must travel together or neither works. (The sibling paths listed above set only the
# stack size; they carry this hazard — flagged, not fixed here, they are not this
# lane's files.)
WASM_RUSTFLAGS='--cfg getrandom_backend="wasm_js" -C link-arg=-zstack-size=33554432'

echo "=== Building wasm/pkg ==="
RUSTFLAGS="$WASM_RUSTFLAGS" wasm-pack build "$ROOT/wasm" --target web --out-dir pkg --release

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
  WASM="$ROOT/wasm/pkg/dregg_wasm_bg.wasm"
  # ONLY strip if there is something to strip. RE-MEASURED 2026-07-25 after the zstd
  # repair, on the first bundle this tree has been able to produce since 07-20: with
  # binaryen on PATH, **`wasm-pack --release` runs `wasm-opt` itself** and the name
  # section is ALREADY GONE by the time this step sees the file. The premise above
  # ("no wasm-opt has ever run on it") was true of the 07-20 artifact — built on a box
  # where wasm-pack could not find binaryen — and is not true here.
  #
  # Running the pass anyway is not free and not neutral: measured on the 56,227,678-byte
  # rebuild it made the file 12,721 bytes BIGGER (56,240,399), because there was no name
  # section to remove and wasm-opt's re-encode is marginally less compact than the input.
  # So the strip is now conditional on the section actually being present. That keeps the
  # protection for a box without binaryen-in-wasm-pack, and stops paying minutes of
  # re-encode for a negative return on a box with it.
  name_bytes="$(python3 - "$WASM" <<'PYEOF'
import sys
b = open(sys.argv[1], "rb").read()
def leb(i):
    r = s = 0
    while True:
        x = b[i]; i += 1
        r |= (x & 0x7f) << s
        if not x & 0x80: return r, i
        s += 7
i, total = 8, 0
while i < len(b):
    sid = b[i]; i += 1
    size, i = leb(i)
    if sid == 0:
        n, j = leb(i)
        if b[j:j+n] == b"name":
            total += size
    i += size
print(total)
PYEOF
)"
  if [ "${name_bytes:-0}" = "0" ]; then
    echo "=== Skipping wasm strip (no name section — wasm-pack's own wasm-opt already removed it) ==="
  else
    echo "=== Stripping wasm debug names ==="
    before=$(wc -c <"$WASM" | tr -d ' ')
    wasm-opt --strip-debug --strip-producers -o "$WASM.stripped" "$WASM"
    mv "$WASM.stripped" "$WASM"
    after=$(wc -c <"$WASM" | tr -d ' ')
    echo "    dregg_wasm_bg.wasm: $before -> $after bytes"
  fi
fi

# ── RECORD WHAT THIS BUNDLE WAS BUILT FROM ────────────────────────────────────
# The staleness half of `descent_play.rs`'s "Missing/STALE wasm fails closed with a
# visible notice" did not exist: on 2026-07-25 the hero CTA was serving a bundle from
# 2026-07-20 21:46, five days and a v1->v3 portable-record wire bump behind the server
# it posts settled runs to, and nothing anywhere could tell. Missing was detected (an
# honest 503, with a test). Stale was not — no mtime, no hash, no manifest.
#
# This writes the record the check needs. `scripts/check-wasm-freshness.sh` recomputes
# the same fingerprint and goes RED on a mismatch; run it in CI and in the deploy.
# It is deliberately written BEFORE the copy into `site/pkg` so both copies carry it.
echo "=== Recording wasm provenance ==="
# ONE invocation (`--verbose` prints "files: N" then the digest); calling it twice would
# re-run `cargo metadata` and re-hash 1,500+ files for a number we already have.
PROV_OUT="$("$ROOT/scripts/wasm-source-fingerprint.sh" --verbose)"
PROV_COUNT="$(printf '%s\n' "$PROV_OUT" | head -1 | awk '{print $2}')"
PROV_SRC="$(printf '%s\n' "$PROV_OUT" | tail -1)"
cat >"$ROOT/wasm/pkg/dregg-wasm-provenance.json" <<PROVJSON
{
  "schema": "dregg-wasm-provenance-v1",
  "built_at": "$(date -u +%Y-%m-%dT%H:%M:%SZ)",
  "git_head": "$(git -C "$ROOT" rev-parse HEAD 2>/dev/null || echo unknown)",
  "git_dirty": $(if [ -n "$(git -C "$ROOT" status --porcelain 2>/dev/null)" ]; then echo true; else echo false; fi),
  "source_sha256": "$PROV_SRC",
  "source_file_count": ${PROV_COUNT:-0},
  "wasm_bytes": $(wc -c <"$ROOT/wasm/pkg/dregg_wasm_bg.wasm" | tr -d ' '),
  "wasm_sha256": "$(sha256_file "$ROOT/wasm/pkg/dregg_wasm_bg.wasm")",
  "glue_sha256": "$(sha256_file "$ROOT/wasm/pkg/dregg_wasm.js")"
}
PROVJSON
echo "    source fingerprint: $PROV_SRC (${PROV_COUNT:-?} files)"

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
