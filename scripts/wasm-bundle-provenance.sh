#!/usr/bin/env bash
# WRITE THE PROVENANCE RECORD for a wasm-bindgen bundle directory — the record
# `scripts/check-wasm-freshness.sh` reads and refuses on.
#
# WHY THIS IS A SCRIPT AND NOT A HEREDOC IN ONE BUILD
# ---------------------------------------------------
# It was a heredoc in `scripts/build-descent-wasm.sh`, and so only ONE of the two bundles
# this repo ships had a record at all. `wasm/pkg` (the site) had one and was gated;
# `extension/dregg_wasm.js` + `dregg_wasm_bg.wasm` (the MV3 service worker's engine) had
# none, was gated by nothing, and rotted for a week against a live beta — the extension
# refused every judged PoA Signal claim because its glue had no
# `build_poa_signal_claim_turn` while `wasm/src/lib.rs` had exported one.
#
# A bundle without a record is REFUSED by the gate rather than assumed fresh, so making the
# writer callable is what lets a second bundle be gated at all.
#
# USAGE
#   scripts/wasm-bundle-provenance.sh <bundle-dir> <bundle-kind>
#
#   <bundle-dir>   holds dregg_wasm.js + dregg_wasm_bg.wasm. The record is written to
#                  <bundle-dir>/dregg-wasm-provenance.json.
#   <bundle-kind>  the wasm-bindgen target the glue was emitted for: `web` or `no-modules`.
#                  RECORDED AND CHECKED, because the two glues are not interchangeable —
#                  `web` is an ES module with `import` statements, `no-modules` is an IIFE
#                  that defines a global `wasm_bindgen`, and dropping the wrong one into
#                  the other's slot fails at load, not at build.
#
# WHAT GOES IN, AND WHY EACH FIELD IS THERE
#   source_sha256   scripts/wasm-source-fingerprint.sh over the wasm32 local-crate graph.
#                   THE staleness check: the bundle is stale exactly when this moves.
#   wasm_sha256     the blob as it sits after every post-processing pass. Catches a
#                   hand-patched or half-copied directory.
#   glue_sha256     the JS glue. It was already being RECORDED by the old writer and
#                   COMPARED AGAINST NOTHING — and the glue is precisely where an absent
#                   export shows up, since `typeof w.build_poa_signal_claim_turn` reads the
#                   glue's exports, not the blob's. The gate checks it now.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

die() { echo "wasm-bundle-provenance: $*" >&2; exit 1; }

DIR="${1:-}"
KIND="${2:-}"
[ -n "$DIR" ]  || die "usage: $0 <bundle-dir> <web|no-modules>"
[ -d "$DIR" ]  || die "no such bundle directory: $DIR"
case "$KIND" in
  web|no-modules) ;;
  *) die "bundle kind must be 'web' or 'no-modules' (got: '${KIND:-<empty>}')" ;;
esac

WASM="$DIR/dregg_wasm_bg.wasm"
GLUE="$DIR/dregg_wasm.js"
[ -f "$WASM" ] || die "no $WASM — nothing to describe"
[ -f "$GLUE" ] || die "no $GLUE — nothing to describe"

sha256_file() {
  if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | awk '{print $1}'
  else shasum -a 256 "$1" | awk '{print $1}'; fi
}

# THE GLUE MUST BE THE KIND IT CLAIMS. A record is only worth what its writer checked, and
# this one is cheap and catches the whole misdelivery class (a `web` bundle copied over the
# extension's slot loads as a syntax error inside a service worker, days later, on a user's
# machine).
case "$KIND" in
  no-modules)
    grep -q 'let wasm_bindgen' "$GLUE" \
      || die "$GLUE does not define the \`wasm_bindgen\` global — that is not a
  \`--target no-modules\` glue, and the MV3 service worker loads it with importScripts."
    ;;
  web)
    grep -qE '^(import|export) ' "$GLUE" \
      || die "$GLUE has no top-level import/export — that is not a \`--target web\` glue."
    ;;
esac

PROV_OUT="$("$ROOT/scripts/wasm-source-fingerprint.sh" --verbose)"
PROV_COUNT="$(printf '%s\n' "$PROV_OUT" | head -1 | awk '{print $2}')"
PROV_SRC="$(printf '%s\n' "$PROV_OUT" | tail -1)"
[ -n "$PROV_SRC" ] || die "the source fingerprint came back empty"

cat >"$DIR/dregg-wasm-provenance.json" <<PROVJSON
{
  "schema": "dregg-wasm-provenance-v2",
  "bundle_kind": "$KIND",
  "built_at": "$(date -u +%Y-%m-%dT%H:%M:%SZ)",
  "git_head": "$(git -C "$ROOT" rev-parse HEAD 2>/dev/null || echo unknown)",
  "git_dirty": $(if [ -n "$(git -C "$ROOT" status --porcelain 2>/dev/null)" ]; then echo true; else echo false; fi),
  "source_sha256": "$PROV_SRC",
  "source_file_count": ${PROV_COUNT:-0},
  "wasm_bytes": $(wc -c <"$WASM" | tr -d ' '),
  "wasm_sha256": "$(sha256_file "$WASM")",
  "glue_bytes": $(wc -c <"$GLUE" | tr -d ' '),
  "glue_sha256": "$(sha256_file "$GLUE")"
}
PROVJSON

echo "    provenance: $DIR/dregg-wasm-provenance.json"
echo "    kind: $KIND · source fingerprint: $PROV_SRC (${PROV_COUNT:-?} files)"
