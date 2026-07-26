#!/usr/bin/env bash
# BUILD THE BROWSER BUNDLE — `wasm/pkg`, the artifact `/descent/play` serves when a player
# opts into running the game in their own tab.
#
# THE ONE PLACE THE BUNDLE IS BUILT
# ---------------------------------
# There were three, and they disagreed. `scripts/build-web-artifacts.sh` built it with the
# correct flag pair; `deploy/games/deploy-hbox.sh` built it with only the stack-size flag;
# `.github/workflows/*` did their own third thing. That divergence is not cosmetic — see
# THE FLAG PAIR below — and a bundle is not a thing you can eyeball for correctness, so
# every path now calls THIS script and there is nothing left to drift.
#
# THE ARTIFACT IS NOT IN THE REPOSITORY. `wasm/pkg/.gitignore` is a single `*`; a fresh
# clone has no bundle at all, and that is deliberate (it is ~54 MB). So the bundle is a
# BUILD OUTPUT of the deploy, never a committed blob, and a deployment that skips this
# step serves a `/descent/play` whose browser engine is simply absent — which the page now
# says out loud instead of throwing (`dreggnet-web/src/descent_play.rs`).
#
# THE FLAG PAIR — both, or neither works
# --------------------------------------
#   -C link-arg=-zstack-size=33554432   32 MiB of linear-memory stack. The recursion
#                                       verifier the light-client-in-the-tab runs overflows
#                                       wasm's 1 MiB default.
#   --cfg getrandom_backend="wasm_js"   getrandom 0.3/0.4 refuse to compile for wasm32
#                                       without a backend selection.
#
# `.cargo/config.toml` sets the second under `[target.wasm32-unknown-unknown] rustflags`,
# and cargo does NOT merge that with the `RUSTFLAGS` environment variable — env WINS
# OUTRIGHT and the config flags are dropped entirely. So the moment a build path exports
# `RUSTFLAGS` for the stack size alone it has silently deleted the getrandom selection.
# They travel together here so no caller can separate them again.
#
# USAGE
#   bash scripts/build-descent-wasm.sh            # build ./wasm/pkg, stamp, verify
#   DREGG_WASM_KEEP_NAMES=1 …                     # keep the debug name section (readable
#                                                 # browser stack traces, ~10 MiB bigger)
#   DREGG_WASM_SKIP_VERIFY=1 …                    # skip the closing freshness gate
#
# Exit 0 = `wasm/pkg` holds a bundle that matches this tree and carries its provenance.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PKG="$ROOT/wasm/pkg"

# BOTH FLAGS, ALWAYS. See the header — separating them is the documented landmine.
WASM_RUSTFLAGS='--cfg getrandom_backend="wasm_js" -C link-arg=-zstack-size=33554432'

sha256_file() {
  if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | awk '{print $1}'
  else shasum -a 256 "$1" | awk '{print $1}'; fi
}

die() { echo "build-descent-wasm: $*" >&2; exit 1; }

command -v wasm-pack >/dev/null 2>&1 \
  || die "wasm-pack is not on PATH. Install it (cargo install wasm-pack) — /descent/play's
  browser engine is a build output, and there is no committed blob to fall back on."

echo "=== Building wasm/pkg (wasm-pack --target web --release) ==="
RUSTFLAGS="$WASM_RUSTFLAGS" wasm-pack build "$ROOT/wasm" --target web --out-dir pkg --release

WASM="$PKG/dregg_wasm_bg.wasm"
[ -f "$WASM" ] || die "wasm-pack reported success but $WASM does not exist"

# ── STRIP THE WASM NAME SECTION, IF THERE IS ONE ──────────────────────────────
# `wasm-pack --release` runs `wasm-opt` ITSELF when binaryen is on PATH, in which case the
# name section is already gone and running the pass again costs minutes and ADDS bytes
# (measured 2026-07-25: +12,721 on a 56 MB bundle, because the re-encode is marginally less
# compact than the input). So the strip is conditional on the section actually being there.
#
# DELIBERATELY NOT `-Oz`. Measured on this bundle it wins on disk (49.0 MB vs 51.2 MB) and
# LOSES over the wire once brotli has it (3.87 MB vs 3.43 MB, ~13% worse) — its size
# rewrites destroy more compressibility than they remove bytes, and the wire number is the
# one a visitor pays. Re-measure before adding an optimisation pass.
if [ "${DREGG_WASM_KEEP_NAMES:-0}" = "1" ]; then
  echo "=== Skipping wasm strip (DREGG_WASM_KEEP_NAMES=1) ==="
else
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
    echo "=== Skipping wasm strip (no name section — wasm-pack's own wasm-opt removed it) ==="
  elif ! command -v wasm-opt >/dev/null 2>&1; then
    # NO SILENT FALLBACK: shipping ~10 MiB of debug symbol names to every visitor is a
    # decision, so it has to be made by name.
    die "the bundle carries a ${name_bytes}-byte debug name section and wasm-opt (binaryen)
  is not on PATH to strip it. Install it (brew install binaryen), or set
  DREGG_WASM_KEEP_NAMES=1 to ship the names deliberately."
  else
    echo "=== Stripping wasm debug names ($name_bytes bytes) ==="
    before=$(wc -c <"$WASM" | tr -d ' ')
    wasm-opt --strip-debug --strip-producers -o "$WASM.stripped" "$WASM"
    mv "$WASM.stripped" "$WASM"
    echo "    dregg_wasm_bg.wasm: $before -> $(wc -c <"$WASM" | tr -d ' ') bytes"
  fi
fi

# ── RECORD WHAT THIS BUNDLE WAS BUILT FROM ────────────────────────────────────
# Without this record there is NO WAY to tell a current bundle from a five-day-old one, and
# that is not hypothetical: `/descent/play` served a v1 portable-record wire against a v3
# server for five days in July 2026, answering 200 the whole time, and every settled run it
# exported was silently refused. `scripts/check-wasm-freshness.sh` reads this file and goes
# RED on a mismatch; a bundle without it is REFUSED rather than assumed fresh.
echo "=== Recording wasm provenance ==="
PROV_OUT="$("$ROOT/scripts/wasm-source-fingerprint.sh" --verbose)"
PROV_COUNT="$(printf '%s\n' "$PROV_OUT" | head -1 | awk '{print $2}')"
PROV_SRC="$(printf '%s\n' "$PROV_OUT" | tail -1)"
cat >"$PKG/dregg-wasm-provenance.json" <<PROVJSON
{
  "schema": "dregg-wasm-provenance-v1",
  "built_at": "$(date -u +%Y-%m-%dT%H:%M:%SZ)",
  "git_head": "$(git -C "$ROOT" rev-parse HEAD 2>/dev/null || echo unknown)",
  "git_dirty": $(if [ -n "$(git -C "$ROOT" status --porcelain 2>/dev/null)" ]; then echo true; else echo false; fi),
  "source_sha256": "$PROV_SRC",
  "source_file_count": ${PROV_COUNT:-0},
  "wasm_bytes": $(wc -c <"$WASM" | tr -d ' '),
  "wasm_sha256": "$(sha256_file "$WASM")",
  "glue_sha256": "$(sha256_file "$PKG/dregg_wasm.js")"
}
PROVJSON
echo "    source fingerprint: $PROV_SRC (${PROV_COUNT:-?} files)"

# ── AND PROVE IT, HERE, BEFORE ANYONE DEPLOYS IT ──────────────────────────────
# A gate that only runs somewhere else is a gate the build can walk past.
if [ "${DREGG_WASM_SKIP_VERIFY:-0}" = "1" ]; then
  echo "=== Skipping the freshness gate (DREGG_WASM_SKIP_VERIFY=1) ==="
else
  bash "$ROOT/scripts/check-wasm-freshness.sh" "$PKG"
fi

echo
echo "=== The Descent browser bundle is ready ==="
echo "glue     : $PKG/dregg_wasm.js"
echo "blob     : $WASM ($(wc -c <"$WASM" | tr -d ' ') bytes)"
echo "serve it : point DESCENT_PLAY_ASSET_DIR at $PKG (or copy the directory and point at"
echo "           the copy — the server reads dregg_wasm.js, dregg_wasm_bg.wasm and"
echo "           snippets/** out of it, and nothing else)."
