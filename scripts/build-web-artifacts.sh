#!/usr/bin/env bash
# Build EVERY browser-facing artifact this repo ships, in dependency order:
#   1. wasm/pkg                        — the site runtime (`wasm-pack --target web`)
#   2. site/pkg                        — the served copy of (1)
#   3. extension/dregg_wasm{.js,_bg.wasm} — the MV3 service worker's engine
#                                        (`wasm-bindgen --target no-modules`)
#   4. extension/dist/*.zip|.xpi       — the store packages, carrying (3)
#   5. site/extension/*                — the download copies of (4)
#
# ⚑ (3) WAS NOT IN THIS LIST UNTIL 2026-08-07, AND THAT WAS THE WHOLE DEFECT
# --------------------------------------------------------------------------
# This script ran `extension/build.sh package` and never `extension/build.sh wasm`. So it
# built the site bundle from source and then packaged the extension around whatever glue
# happened to be sitting in the tree. The two artifacts drifted independently for weeks —
# `wasm/pkg` at 2026-07-28, `extension/` at 2026-08-01, 312 KB of glue against 278 KB —
# and the consequence was live: `wasm/src/lib.rs` exported `build_poa_signal_claim_turn`,
# the extension's glue had ZERO occurrences of it, and `background.ts` refused EVERY
# judged PoA Signal claim on beta.pathofangels.network.
#
# `scripts/check-wasm-freshness.sh` existed for exactly this class and was aimed at
# `wasm/pkg`. The extension loaded a different file the gate never looked at.
#
# THE TWO BUNDLES ARE NOT COPIES OF EACH OTHER. `wasm/pkg`'s glue is an ES module;
# the extension's is an IIFE defining a global `wasm_bindgen`, because an MV3 service
# worker loads it with `importScripts`. Never `cp` one onto the other. What they share is
# the `RUSTFLAGS` pair, and that now has ONE definition (`scripts/wasm-build-flags.sh`),
# which also lets them share compiled artifacts in `wasm/target`.
#
# WHAT THIS SCRIPT NO LONGER DOES (2026-08-07)
#   * `(cd site && npm run build)` — `site/` has no `package.json`; that line belonged to
#     the pre-rewrite site (now `site-old-scavenge/`) and could not have run for months.
#   * write `site/dist/artifacts-manifest.json` over `site/dist/pkg/*` — `site/dist` is
#     assembled by `scripts/build-pages-dist.sh`, not by this script, and every path the
#     manifest measured was one this script does not create. The manifest now describes
#     the artifacts this script actually produces and lives beside them, at
#     `site/artifacts-manifest.json`.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
MANIFEST="$ROOT/site/artifacts-manifest.json"

sha256_file() {
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum "$1" | awk '{print $1}'
  else
    shasum -a 256 "$1" | awk '{print $1}'
  fi
}

die() { echo; echo "build-web-artifacts: $*" >&2; exit 1; }

# ── STEP 0: PREFLIGHT ─────────────────────────────────────────────────────────────────
# EVERY prerequisite of EVERY later step, checked before the first cargo invocation. This
# script spends ~20 minutes on two wasm builds, and it used to die AFTER all of it on
# `cp … site/extension/dregg-cipherclerk.zip: No such file or directory` — a missing
# output directory, discovered last. A missing tool or a missing directory is knowable in
# a second; find out then.
echo "=== Preflight ==="
missing=""
for tool in cargo wasm-pack wasm-bindgen node npm zip python3; do
  command -v "$tool" >/dev/null 2>&1 || missing="$missing
  $tool"
done
[ -z "$missing" ] || die "these tools are not on PATH, and every one of them is needed:$missing"

for f in \
  "$ROOT/scripts/build-descent-wasm.sh" \
  "$ROOT/scripts/wasm-build-flags.sh" \
  "$ROOT/scripts/wasm-bundle-provenance.sh" \
  "$ROOT/scripts/check-wasm-freshness.sh" \
  "$ROOT/extension/build.sh" \
  "$ROOT/extension/package.json"
do
  [ -f "$f" ] || die "required script is missing: $f"
done

# The output directories this script writes into. `site/pkg` and `site/extension` are
# gitignored publish targets, so on a fresh checkout neither exists — CREATE them here,
# where it costs nothing, rather than discovering it after the builds.
mkdir -p "$ROOT/site/pkg" "$ROOT/site/extension"
for d in "$ROOT/site/pkg" "$ROOT/site/extension"; do
  [ -w "$d" ] || die "output directory is not writable: $d"
done
echo "  tools present; site/pkg and site/extension ready"

# ── STEP 1: THE SITE BUNDLE ───────────────────────────────────────────────────────────
# Delegated, deliberately. This step used to be an inline `wasm-pack` invocation here AND
# a differently-flagged one in `deploy/games/deploy-hbox.sh` AND a third in the workflows,
# and the flag pair they disagreed about (`getrandom_backend` vs the stack size — env
# RUSTFLAGS overrides `.cargo/config.toml` OUTRIGHT rather than merging) is exactly the
# kind of divergence you cannot see by looking at a bundle. `scripts/build-descent-wasm.sh`
# is the ONE `wasm/pkg` build: the flags, the conditional name-section strip, the
# provenance stamp, and the freshness gate that proves the result before anything ships it.
bash "$ROOT/scripts/build-descent-wasm.sh"

echo "=== Refreshing site/pkg from wasm/pkg ==="
rm -rf "$ROOT/site/pkg/dregg_wasm"* "$ROOT/site/pkg/package.json" "$ROOT/site/pkg/.gitignore"
rm -f "$ROOT/site/pkg/dregg-wasm-provenance.json"
cp -R "$ROOT/wasm/pkg/." "$ROOT/site/pkg/"
# The served copy carries the record, so the gate can grade THE COPY and not merely the
# directory it was made from.
bash "$ROOT/scripts/check-wasm-freshness.sh" "$ROOT/site/pkg" --kind web

# ── STEP 2: THE EXTENSION BUNDLE, THEN THE PACKAGES ───────────────────────────────────
# `./build.sh wasm` is THE line whose absence was the defect. It compiles the same crate
# for the same target with the same flags as step 1 (so cargo reuses that work), runs
# wasm-bindgen with `--target no-modules`, inlines the JS snippets a service worker cannot
# `require`, optimizes, stamps provenance, and gates itself. `./build.sh package` then
# refuses to leave a package the gate calls stale.
echo "=== Building the extension bundle and packages ==="
(cd "$ROOT/extension" && npm run build && ./build.sh wasm && ./build.sh package)

echo "=== Publishing extension downloads into site/extension ==="
cp "$ROOT/extension/dist/dregg-cipherclerk-chrome.zip" "$ROOT/site/extension/dregg-cipherclerk.zip"
cp "$ROOT/extension/dist/dregg-cipherclerk-chrome.zip" "$ROOT/site/extension/dregg-wallet.zip"
cp "$ROOT/extension/dist/dregg-cipherclerk-firefox.xpi" "$ROOT/site/extension/dregg-cipherclerk-firefox.xpi"
# GRADE THE PUBLISHED COPIES, not just the originals. A copy is where a half-finished
# `cp` and a stale leftover both live, and these three are what a visitor downloads.
for p in dregg-cipherclerk.zip dregg-wallet.zip dregg-cipherclerk-firefox.xpi; do
  bash "$ROOT/scripts/check-wasm-freshness.sh" "$ROOT/site/extension/$p" --kind no-modules
done

# ── STEP 3: SAY WHAT WAS PRODUCED ─────────────────────────────────────────────────────
echo "=== Writing artifact manifest ==="
cat >"$MANIFEST" <<JSON
{
  "schema": "dregg-web-artifacts-v2",
  "built_at": "$(date -u +%Y-%m-%dT%H:%M:%SZ)",
  "git_head": "$(git -C "$ROOT" rev-parse HEAD 2>/dev/null || echo unknown)",
  "artifacts": {
    "site/pkg/dregg_wasm.js": {
      "bytes": $(wc -c <"$ROOT/site/pkg/dregg_wasm.js" | tr -d ' '),
      "sha256": "$(sha256_file "$ROOT/site/pkg/dregg_wasm.js")"
    },
    "site/pkg/dregg_wasm_bg.wasm": {
      "bytes": $(wc -c <"$ROOT/site/pkg/dregg_wasm_bg.wasm" | tr -d ' '),
      "sha256": "$(sha256_file "$ROOT/site/pkg/dregg_wasm_bg.wasm")"
    },
    "extension/dregg_wasm.js": {
      "bytes": $(wc -c <"$ROOT/extension/dregg_wasm.js" | tr -d ' '),
      "sha256": "$(sha256_file "$ROOT/extension/dregg_wasm.js")"
    },
    "extension/dregg_wasm_bg.wasm": {
      "bytes": $(wc -c <"$ROOT/extension/dregg_wasm_bg.wasm" | tr -d ' '),
      "sha256": "$(sha256_file "$ROOT/extension/dregg_wasm_bg.wasm")"
    },
    "site/extension/dregg-cipherclerk.zip": {
      "bytes": $(wc -c <"$ROOT/site/extension/dregg-cipherclerk.zip" | tr -d ' '),
      "sha256": "$(sha256_file "$ROOT/site/extension/dregg-cipherclerk.zip")"
    },
    "site/extension/dregg-cipherclerk-firefox.xpi": {
      "bytes": $(wc -c <"$ROOT/site/extension/dregg-cipherclerk-firefox.xpi" | tr -d ' '),
      "sha256": "$(sha256_file "$ROOT/site/extension/dregg-cipherclerk-firefox.xpi")"
    }
  }
}
JSON

echo "=== Web artifacts ready ==="
echo "Site wasm:  $ROOT/site/pkg/dregg_wasm.js"
echo "Ext  wasm:  $ROOT/extension/dregg_wasm.js"
echo "Extension:  $ROOT/site/extension/dregg-cipherclerk.zip"
echo "Manifest:   $MANIFEST"
echo
echo "site/dist is assembled separately, by scripts/build-pages-dist.sh."
