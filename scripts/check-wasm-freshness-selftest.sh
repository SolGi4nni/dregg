#!/usr/bin/env bash
# PROVE `scripts/check-wasm-freshness.sh` CAN GO RED — constructively, on a bundle this
# script builds, in a scratch directory, touching nothing in the shared tree.
#
# WHY A NEGATIVE ASSERTION NEEDS ITS OWN RUN
# ------------------------------------------
# The freshness gate's headline is a REFUSAL, and a refusal passes just as happily when
# the refuser is broken. This repo has already paid for that twice:
#
#   * the wound the gate exists for — `descent_play.rs` DOCUMENTED "STALE wasm fails
#     closed" and the stale half did not exist at all;
#   * a falsifier that stopped falsifying — a mutation test whose mutation had silently
#     become a no-op (`replacen` of a string that had left the fixture), so the adversary
#     was dead while the gate stayed green.
#
# So every plant here is built CONSTRUCTIVELY and ASSERTED TO HAVE LANDED before the
# verdict is read. A plant that did not change the artifact is a FAILURE of this script,
# not a pass.
#
# AND THE CONTROL MATTERS AS MUCH AS THE PLANTS: leg 0 asserts the unmutated bundle is
# GREEN. Without it, "seven reds" is consistent with a gate that refuses everything.
#
# Exit 0 = the gate is alive: green on a clean bundle, red on each of seven defects.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
GATE="$ROOT/scripts/check-wasm-freshness.sh"
STAMP="$ROOT/scripts/wasm-bundle-provenance.sh"

WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT

PRISTINE="$WORK/pristine"
SUBJECT="$WORK/subject"

pass=0
fail=0

sha256_file() {
  if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | awk '{print $1}'
  else shasum -a 256 "$1" | awk '{print $1}'; fi
}

jget() { python3 -c 'import json,sys;print(json.load(open(sys.argv[1])).get(sys.argv[2],""))' "$1" "$2"; }
jset() { python3 -c '
import json,sys
p,k,v=sys.argv[1],sys.argv[2],sys.argv[3]
d=json.load(open(p)); d[k]=v
json.dump(d,open(p,"w"),indent=2)
' "$1" "$2" "$3"; }

die() { echo "SELF-TEST BROKEN: $*" >&2; exit 2; }

# ── A synthetic bundle, shaped like the real no-modules one ──────────────────────────
# The gate hashes these files and reads the glue's SHAPE; it never runs them. So a few
# bytes with the right silhouette exercise every leg, and the whole run is seconds.
make_pristine() {
  rm -rf "$PRISTINE"; mkdir -p "$PRISTINE"
  cat >"$PRISTINE/dregg_wasm.js" <<'GLUE'
let wasm_bindgen = (function(exports) {
    // synthetic no-modules glue for scripts/check-wasm-freshness-selftest.sh
    exports.build_poa_signal_claim_turn = function () {};
    return exports;
})({});
GLUE
  printf '\0asm\1\0\0\0synthetic-blob-for-the-freshness-selftest' >"$PRISTINE/dregg_wasm_bg.wasm"
}

# Stamp, then immediately grade. In a live multi-lane tree the wasm32 source fingerprint
# genuinely moves every few minutes, so a stamp can be overtaken between writing and
# checking. That is the gate WORKING; retry the control a bounded number of times and, if
# the tree outran all of them, say so and fail rather than pretend.
establish_green_control() {
  local attempt
  for attempt in 1 2 3; do
    make_pristine
    bash "$STAMP" "$PRISTINE" no-modules >/dev/null || die "the provenance writer refused a well-formed synthetic bundle"
    if bash "$GATE" "$PRISTINE" --kind no-modules >/dev/null 2>&1; then
      echo "  leg 0 CONTROL   green on a clean bundle (attempt $attempt)"
      pass=$((pass + 1))
      return 0
    fi
  done
  echo "  leg 0 CONTROL   COULD NOT BE ESTABLISHED — the wasm32 source closure changed" >&2
  echo "                  under three consecutive stamp+check attempts. That is a busy tree," >&2
  echo "                  not a broken gate, but no red below would prove anything." >&2
  exit 2
}

reset_subject() { rm -rf "$SUBJECT"; cp -R "$PRISTINE" "$SUBJECT"; }

# expect_red <label> <plant-fn>
# The plant function must (a) mutate $SUBJECT and (b) `die` if its mutation did not land.
expect_red() {
  local label="$1" plant="$2"
  reset_subject
  "$plant"
  if bash "$GATE" "$SUBJECT" --kind no-modules >/dev/null 2>&1; then
    echo "  $label  ✗ GATE STAYED GREEN — it does not detect this" >&2
    fail=$((fail + 1))
  else
    echo "  $label  red, as it must be"
    pass=$((pass + 1))
  fi
}

# ── THE PLANTS ───────────────────────────────────────────────────────────────────────

plant_no_record() {
  rm -f "$SUBJECT/dregg-wasm-provenance.json"
  [ -f "$SUBJECT/dregg-wasm-provenance.json" ] && die "plant_no_record did not remove the record"
  return 0
}

plant_old_schema() {
  local p="$SUBJECT/dregg-wasm-provenance.json"
  jset "$p" schema "dregg-wasm-provenance-v1"
  [ "$(jget "$p" schema)" = "dregg-wasm-provenance-v1" ] || die "plant_old_schema did not change the schema field"
}

plant_mutated_blob() {
  local b="$SUBJECT/dregg_wasm_bg.wasm" before after
  before="$(sha256_file "$b")"
  printf 'X' >>"$b"
  after="$(sha256_file "$b")"
  [ "$before" != "$after" ] || die "plant_mutated_blob left the blob byte-identical"
}

plant_mutated_glue() {
  local g="$SUBJECT/dregg_wasm.js" before after
  before="$(sha256_file "$g")"
  printf '\n// an edit the build never made\n' >>"$g"
  after="$(sha256_file "$g")"
  [ "$before" != "$after" ] || die "plant_mutated_glue left the glue byte-identical"
}

# THE ROT ITSELF, in miniature: a blob and a record that agree, and a glue that is a week
# behind them and no longer carries the export the caller looks for. Before 2026-08-07
# this plant was INVISIBLE — `glue_sha256` was recorded and compared against nothing.
plant_stale_glue_missing_export() {
  local g="$SUBJECT/dregg_wasm.js" before after
  before="$(sha256_file "$g")"
  # NOTE the older glue must not so much as MENTION the export — the assertion below is a
  # `grep`, and a comment naming the missing symbol would satisfy it. (It did, first try.)
  cat >"$g" <<'OLDGLUE'
let wasm_bindgen = (function(exports) {
    // an OLDER glue: the PoA Signal carrier had not landed yet
    return exports;
})({});
OLDGLUE
  after="$(sha256_file "$g")"
  [ "$before" != "$after" ] || die "plant_stale_glue_missing_export did not change the glue"
  grep -q build_poa_signal_claim_turn "$g" && die "plant_stale_glue_missing_export left the export in place"
  return 0
}

plant_wrong_source_fingerprint() {
  local p="$SUBJECT/dregg-wasm-provenance.json" before
  before="$(jget "$p" source_sha256)"
  jset "$p" source_sha256 "0000000000000000000000000000000000000000000000000000000000000000"
  [ "$(jget "$p" source_sha256)" != "$before" ] || die "plant_wrong_source_fingerprint did not change the field"
}

plant_wrong_kind() {
  local p="$SUBJECT/dregg-wasm-provenance.json"
  jset "$p" bundle_kind "web"
  [ "$(jget "$p" bundle_kind)" = "web" ] || die "plant_wrong_kind did not change the field"
}

# ── THE ARCHIVE FORM ─────────────────────────────────────────────────────────────────
# The shipped artifact is a .zip, not a directory. Grading it is a NEW input shape, so it
# gets its own control and its own plant.
archive_legs() {
  command -v zip >/dev/null 2>&1 || { echo "  (zip not on PATH — archive legs skipped)"; return 0; }

  local good="$WORK/good.zip" bad="$WORK/no-record.zip"
  ( cd "$PRISTINE" && zip -q "$good" dregg_wasm.js dregg_wasm_bg.wasm dregg-wasm-provenance.json )
  unzip -l "$good" | grep -q dregg-wasm-provenance.json || die "the good archive did not get the record"

  if bash "$GATE" "$good" --kind no-modules >/dev/null 2>&1; then
    echo "  leg 8 CONTROL   green on a well-formed package"
    pass=$((pass + 1))
  else
    echo "  leg 8 CONTROL   ✗ RED on a well-formed package — the archive path is broken" >&2
    fail=$((fail + 1))
  fi

  ( cd "$PRISTINE" && zip -q "$bad" dregg_wasm.js dregg_wasm_bg.wasm )
  unzip -l "$bad" | grep -q dregg-wasm-provenance.json \
    && die "the record-less archive still contains the record — the plant did not land"
  if bash "$GATE" "$bad" --kind no-modules >/dev/null 2>&1; then
    echo "  leg 9 package with NO provenance record  ✗ GATE STAYED GREEN" >&2
    fail=$((fail + 1))
  else
    echo "  leg 9 package with NO provenance record  red, as it must be"
    pass=$((pass + 1))
  fi
}

echo "=== check-wasm-freshness self-test (can it go red?) ==="
establish_green_control

expect_red "leg 1 no provenance record             " plant_no_record
expect_red "leg 2 superseded schema (v1)           " plant_old_schema
expect_red "leg 3 blob edited after the build      " plant_mutated_blob
expect_red "leg 4 glue edited after the build      " plant_mutated_glue
expect_red "leg 5 glue a week behind, export GONE  " plant_stale_glue_missing_export
expect_red "leg 6 source fingerprint moved         " plant_wrong_source_fingerprint
expect_red "leg 7 glue is not the kind claimed     " plant_wrong_kind
archive_legs

echo
if [ "$fail" -ne 0 ]; then
  echo "SELF-TEST: RED — $fail leg(s) the gate does not detect ($pass ok)." >&2
  exit 1
fi
echo "SELF-TEST: GREEN — $pass legs; the gate is green on a clean bundle and red on every planted defect."
