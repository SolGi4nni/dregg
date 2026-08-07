#!/usr/bin/env bash
# GATE: refuse a browser wasm bundle that does not match the source it is supposed to
# have been built from.
#
# THE WOUND THIS CLOSES
# ---------------------
# 2026-07-25: `/descent/play` — the flagship "Play" CTA — was serving a bundle built
# 2026-07-20 21:46. In between, ten commits touched `wasm/src`, four of them
# `bindings_native_descent.rs`, and the descent portable-record WIRE went v1 -> v3
# (`daySeedHex` in v2, `completion.bankedNotes` in v3). The served bundle exported v1
# envelopes; `/descent/native/submit` refuses anything that is not
# `native_descent_wire::PORTABLE_VERSION`. So every settled run from the hero CTA was
# rejected, silently, for five days.
#
# `descent_play.rs`'s module doc said "Missing/STALE wasm fails closed with a visible
# notice." Missing did (an honest 503, and it has a test). STALE did not exist at all —
# no mtime, no hash, no manifest, no comparison, anywhere in the tree. A documented
# wound is not a detected one, and a gate that cannot go red is not a gate.
#
# ⚑ AND THEN THE INSTRUMENT WAS AIMED ONE ARTIFACT AWAY (2026-08-07)
# ------------------------------------------------------------------
# This script closed the wound for `wasm/pkg`. This repo ships TWO browser bundles, and
# the other one — `extension/dregg_wasm.js` + `dregg_wasm_bg.wasm`, the engine the MV3
# service worker loads with `importScripts` — was checked by nothing. No build step
# refreshed it, no gate looked at it, and it rotted for a week: `wasm/src/lib.rs` exported
# `build_poa_signal_claim_turn`, the extension's glue had ZERO occurrences of it, and
# `background.ts` therefore refused EVERY judged PoA Signal claim, on live beta.
#
# Worse, the artifact LOOKED fresh. `extension/build.sh package` re-ran `wasm-opt -Oz`
# over the blob and `mv`'d the result into place on every packaging run, so
# `dregg_wasm_bg.wasm`'s mtime advanced while its CONTENT stayed a week old. An mtime is
# not evidence; that is why this gate hashes.
#
# So the gate now grades EITHER bundle, and grades the SHIPPED PACKAGE too: hand it a
# directory, or hand it the `.zip`/`.xpi` a store would receive.
#
# WHAT IT CHECKS
#   1. the provenance record exists at all (a bundle built by any path that does not
#      record provenance is REFUSED — there is no "assume fresh" fallback);
#   2. the record is the CURRENT schema (an older one refuses to load rather than being
#      reinterpreted — v1 recorded a glue hash that nothing ever compared, so a v1 record
#      cannot be read as evidence about the glue);
#   3. `dregg_wasm_bg.wasm` on disk still hashes to what the build recorded;
#   4. `dregg_wasm.js` on disk still hashes to what the build recorded — v1 wrote this
#      field and compared it against NOTHING, and the glue is where a missing export
#      actually shows up, because the JS caller reads the glue's exports;
#   5. the glue is the KIND the record claims (`web` is an ES module, `no-modules` is an
#      IIFE defining a global `wasm_bindgen`; they are not interchangeable and swapping
#      them fails at load, on a user's machine, not at build);
#   6. the wasm32 source closure hashes to what the build recorded (the actual staleness
#      check — see `scripts/wasm-source-fingerprint.sh` for exactly what is in that
#      closure and why it errs toward false-STALE).
#
# USAGE
#   scripts/check-wasm-freshness.sh                      # check ./wasm/pkg
#   scripts/check-wasm-freshness.sh <asset-dir>          # a vendored/deployed dir
#                                                        # (e.g. $DESCENT_PLAY_ASSET_DIR)
#   scripts/check-wasm-freshness.sh <pkg.zip|pkg.xpi>    # THE SHIPPED PACKAGE
#   scripts/check-wasm-freshness.sh <t> --kind no-modules # also assert the bundle kind
#   scripts/check-wasm-freshness.sh --self-test          # prove this gate can go red
#
# Exit 0 = current. Exit 1 = STALE / unverifiable. Run it in CI and in the deploy, and
# let it fail the deploy — that is the whole point.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SCHEMA_CURRENT="dregg-wasm-provenance-v2"

sha256_file() {
  if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | awk '{print $1}'
  else shasum -a 256 "$1" | awk '{print $1}'; fi
}

jget() { python3 -c 'import json,sys;print(json.load(open(sys.argv[1])).get(sys.argv[2],""))' "$1" "$2"; }

fail() { echo; echo "WASM FRESHNESS: RED — $*" >&2; exit 1; }

# The kind a glue file ACTUALLY is, read out of the file rather than believed from the
# record — so a swapped glue is caught even when the record was honest about the one it
# described.
glue_kind() {
  if grep -q 'let wasm_bindgen' "$1"; then echo "no-modules"
  elif grep -qE '^(import|export) ' "$1"; then echo "web"
  else echo "unrecognized"; fi
}

# ── ARGUMENTS ────────────────────────────────────────────────────────────────────────
TARGET=""
WANT_KIND=""
SELF_TEST=0
while [ $# -gt 0 ]; do
  case "$1" in
    --self-test) SELF_TEST=1; shift ;;
    --kind) WANT_KIND="${2:-}"; shift 2 ;;
    --kind=*) WANT_KIND="${1#--kind=}"; shift ;;
    -*) echo "check-wasm-freshness: unknown option $1" >&2; exit 2 ;;
    *) TARGET="$1"; shift ;;
  esac
done

if [ "$SELF_TEST" = "1" ]; then
  exec bash "$ROOT/scripts/check-wasm-freshness-selftest.sh"
fi

TARGET="${TARGET:-$ROOT/wasm/pkg}"

# ── SCOPE ─ this printf is the ONLY copy; it prints on every run, pass or fail. ───────
printf 'ANSWERS:         %s\nDOES NOT ANSWER: %s\n' \
  'does the artifact (a bundle directory, or the .zip/.xpi a store would receive) carry a current-schema dregg-wasm-provenance.json; do dregg_wasm_bg.wasm AND dregg_wasm.js still hash to the wasm_sha256/glue_sha256 that record names; is the glue the bundle_kind the record claims; and does a fresh run of scripts/wasm-source-fingerprint.sh over the wasm32 local-crate graph equal the source_sha256 that record names?' \
  'whether the bundle is correct, or whether it is the bundle anybody is serving. It compares hashes against a record the BUILD wrote about itself, so it grades THIS artifact only — a deployed copy elsewhere is out of scope unless you pass its path — and it never runs the wasm, never checks a wire version, never checks that any particular export is present, and never verifies that the recorded fingerprint was honest when written. The source closure is a deliberate superset (cfg(test) code and descriptor data in, tests/benches/examples pruned), so a red can mean a rebuild is due rather than that behaviour changed.'

echo "=== wasm freshness gate ==="

# ── RESOLVE THE TARGET ───────────────────────────────────────────────────────────────
# An archive is graded by unpacking the three bundle members into a scratch dir and then
# running the SAME checks — one gate, two input shapes, no second implementation to drift.
UNPACKED=""
cleanup() { [ -n "$UNPACKED" ] && rm -rf "$UNPACKED"; return 0; }
trap cleanup EXIT

case "$TARGET" in
  *.zip|*.xpi)
    [ -f "$TARGET" ] || fail "no such archive: $TARGET"
    command -v unzip >/dev/null 2>&1 || fail "unzip is not on PATH; cannot grade an archive"
    echo "archive:      $TARGET"
    UNPACKED="$(mktemp -d)"
    # `-o` overwrite, `-j` junk paths: the bundle members sit at the archive root in both
    # the Chrome .zip and the Firefox .xpi.
    unzip -qo -j "$TARGET" \
      dregg_wasm.js dregg_wasm_bg.wasm dregg-wasm-provenance.json -d "$UNPACKED" 2>/dev/null || true
    for m in dregg_wasm.js dregg_wasm_bg.wasm dregg-wasm-provenance.json; do
      [ -f "$UNPACKED/$m" ] || fail "$(printf 'the package does not contain %s.\n\nA package that does not carry its own provenance record cannot be graded at all — which\nis the state extension/dist/dregg-cipherclerk-chrome.zip was in while it shipped a\nweek-old engine to live beta.\n\nRebuild it:  cd extension && ./build.sh wasm && ./build.sh package' "$m")"
    done
    DIR="$UNPACKED"
    ;;
  *)
    DIR="$TARGET"
    echo "artifact dir: $DIR"
    [ -d "$DIR" ] || fail "no such directory: $DIR"
    ;;
esac

PROV="$DIR/dregg-wasm-provenance.json"

if [ ! -f "$PROV" ]; then
  cat >&2 <<EOF

WASM FRESHNESS: RED — no provenance record at
  $PROV

This bundle was NOT produced by a build that records provenance, so there is nothing
to compare it against and NO WAY to tell whether it is current. That is exactly the
state \`/descent/play\` was in on 2026-07-25 while serving a five-day-old wire, and the
state \`extension/\` was in on 2026-08-07 while refusing every judged claim on beta.

Rebuild it:  bash scripts/build-web-artifacts.sh          # both bundles
             cd extension && ./build.sh wasm              # the extension's alone
EOF
  exit 1
fi

# ── (1) THE RECORD IS THE CURRENT SHAPE ──────────────────────────────────────────────
# An old record is REFUSED, not reinterpreted. v1 carried a `glue_sha256` that nothing
# compared, so reading a v1 record as evidence about the glue would be a lie about what
# was checked.
schema="$(jget "$PROV" schema)"
if [ "$schema" != "$SCHEMA_CURRENT" ]; then
  fail "$(printf 'the provenance record is schema %s; this gate reads %s.\n\nThe old record cannot be reinterpreted: v1 wrote a glue_sha256 that NOTHING ever compared,\nso it is not evidence about the glue, and it names no bundle_kind at all.\n\nRebuild the bundle to re-stamp it.' "${schema:-<none>}" "$SCHEMA_CURRENT")"
fi

recorded_src="$(jget "$PROV" source_sha256)"
recorded_wasm="$(jget "$PROV" wasm_sha256)"
recorded_glue="$(jget "$PROV" glue_sha256)"
recorded_kind="$(jget "$PROV" bundle_kind)"
built_at="$(jget "$PROV" built_at)"
git_head="$(jget "$PROV" git_head)"
[ -n "$recorded_src" ]  || fail "provenance record has no source_sha256 (corrupt)"
[ -n "$recorded_wasm" ] || fail "provenance record has no wasm_sha256 (corrupt)"
[ -n "$recorded_glue" ] || fail "provenance record has no glue_sha256 (corrupt)"
[ -n "$recorded_kind" ] || fail "provenance record has no bundle_kind (corrupt)"

echo "built at:     ${built_at:-<unrecorded>}  (git ${git_head:-<unrecorded>}, kind $recorded_kind)"

# ── (2) THE BLOB STILL IS WHAT WAS BUILT ─────────────────────────────────────────────
blob="$DIR/dregg_wasm_bg.wasm"
[ -f "$blob" ] || fail "provenance exists but $blob does not — a half-copied artifact dir"
actual_wasm="$(sha256_file "$blob")"
if [ "$actual_wasm" != "$recorded_wasm" ]; then
  fail "$(printf 'dregg_wasm_bg.wasm does not match its own build record.\n  recorded %s\n  on disk  %s\nThe artifact was replaced or edited after the build that described it.' "$recorded_wasm" "$actual_wasm")"
fi

# ── (3) AND SO DOES THE GLUE ─────────────────────────────────────────────────────────
# This leg did not exist before 2026-08-07. The field was written and compared against
# nothing, and the glue is where a missing export is VISIBLE: `background.ts` tests
# `typeof w.build_poa_signal_claim_turn === "function"`, which reads the glue's export
# table, not the blob's.
glue="$DIR/dregg_wasm.js"
[ -f "$glue" ] || fail "provenance exists but $glue does not — a half-copied artifact dir"
actual_glue="$(sha256_file "$glue")"
if [ "$actual_glue" != "$recorded_glue" ]; then
  fail "$(printf 'dregg_wasm.js does not match its own build record.\n  recorded %s\n  on disk  %s\nThe glue was replaced or edited after the build that described it. A glue that is older\nthan its blob is how an export goes missing while everything still loads.' "$recorded_glue" "$actual_glue")"
fi

# ── (4) THE GLUE IS THE KIND IT CLAIMS ───────────────────────────────────────────────
actual_kind="$(glue_kind "$glue")"
if [ "$actual_kind" != "$recorded_kind" ]; then
  fail "$(printf 'dregg_wasm.js is a %s glue but the record calls it %s.\n\n`web` is an ES module; `no-modules` is an IIFE that defines a global `wasm_bindgen` and is\nthe only shape an MV3 service worker can importScripts. Dropping either one into the\nslot the other belongs in fails at LOAD, on a user machine, not at build.' "$actual_kind" "$recorded_kind")"
fi
if [ -n "$WANT_KIND" ] && [ "$recorded_kind" != "$WANT_KIND" ]; then
  fail "caller asked for a '$WANT_KIND' bundle; this artifact is '$recorded_kind'"
fi

# ── (5) THE SOURCE CLOSURE STILL IS WHAT IT WAS BUILT FROM ───────────────────────────
echo "recomputing the wasm32 source fingerprint..."
actual_src="$("$ROOT/scripts/wasm-source-fingerprint.sh")"

if [ "$actual_src" != "$recorded_src" ]; then
  cat >&2 <<EOF

WASM FRESHNESS: RED — the bundle is STALE.

  built from source  $recorded_src
  tree is now        $actual_src

The wasm32 source closure has changed since this bundle was built, so what this artifact
carries is NOT what this tree says the code is. This is the failure that shipped a v1
portable-record wire against a v3 server for five days: the bundle answered 200, the
browser played, and every settled run it exported was refused. It is also the failure
that shipped an extension with no \`build_poa_signal_claim_turn\` against a beta that
judges claims: the service worker loaded, and refused every one.

Rebuild it:  bash scripts/build-web-artifacts.sh          # both bundles
             cd extension && ./build.sh wasm              # the extension's alone
EOF
  exit 1
fi

echo
echo "WASM FRESHNESS: GREEN — $recorded_kind bundle matches the wasm32 source closure."
