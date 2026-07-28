#!/usr/bin/env bash
# check-mina-attestation.sh — RUN the Mina<->dregg Poseidon attestation zkApp.
#
# `bridge/mina-zkapp/` was a complete orphan: measured 2026-07-27,
# `grep -rn 'mina-zkapp|attestation-poc|poseidon-kat' .github/ scripts/` returned
# ZERO hits across all 26 workflows and `scripts/local-gates.sh`
# (docs/AUDIT-IMPORTER-AND-DOCS.md §3.6, F-B10). Worse, what was committed did not
# run: `tsc` failed on `src/DreggPoseidonAttestation.ts`, and the PoC that was
# reported working had run in a SCRATCH DIRECTORY at a different o1js than the one
# the tree pinned. The good cryptographic result could not go red because nothing
# ever asked it to. This row is the thing that asks.
#
# What it runs (`bridge/mina-zkapp/scripts/attestation-gate.ts`, compiled from the
# committed TypeScript by `tsc` and executed from `dist/`):
#   [0] the toolchain pin is the one the tree declares (o1js 2.15.0, node >= 20)
#   [1] o1js `Poseidon.hash` reproduces every Mina-Poseidon vector the Rust probe
#       `circuit-prove/sketches/mina-pasta-hash-probe` asserts — 9 digests, the
#       depth-2 Merkle root, and the field modulus — bit-for-bit
#   [2] a `ZkProgram` verifies a Poseidon-Merkle path IN-CIRCUIT whose public
#       input is that Rust-emitted root
#   [3] a real Pickles compile + prove + verify, with the opened leaf carried out
#   [4] a tampered sibling and a tampered public root each FAIL to prove
#   [5] the `DreggAttestedGate` zkApp deploys on a local chain, CONSUMES the
#       attestation proof recursively, and REFUSES one bound to another root
#
# Second leg (`bridge/mina-zkapp/scripts/poseidon2-babybear-rows.ts`): the
# Poseidon2-w16-BabyBear permutation as an o1js circuit, checked against the
# Lean-pinned KAT of the DEPLOYED hash, compiled and PROVED, and its rows/perm
# figure RATCHETED against the number docs/MINA-VERIFIES-DREGG-FRI-SIZE.md quotes.
#
# ⚑ NO SKIPS. A missing `node`, a missing `npm`, an absent or unpinned o1js, a
# type error, or a diverging vector are all FAILURES — the same discipline as
# `embedded-js` and `opentheory-importer`. ~60s including `npm ci` when cold,
# ~45s warm. No cargo, no Lean.
#
#   bash scripts/check-mina-attestation.sh
#   bash scripts/check-mina-attestation.sh --self-test    # prove it can go red
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
APP="$ROOT/bridge/mina-zkapp"
PINNED_O1JS="2.15.0"

die() { echo "FAIL: $*" >&2; exit 1; }

require_toolchain() {
  command -v node >/dev/null 2>&1 || die "node is not on PATH (this gate does not skip)"
  command -v npm  >/dev/null 2>&1 || die "npm is not on PATH (this gate does not skip)"
  local major
  major="$(node -p 'process.versions.node.split(".")[0]')"
  [ "$major" -ge 20 ] || die "node v$major is below the supported floor v20"
}

# Ensure the pinned o1js is installed in $1 (a mina-zkapp dir). Installs if not.
ensure_o1js() {
  local dir="$1" have=""
  if [ -f "$dir/node_modules/o1js/package.json" ]; then
    have="$(node -p "require('$dir/node_modules/o1js/package.json').version" 2>/dev/null)"
  fi
  if [ "$have" != "$PINNED_O1JS" ]; then
    echo "installing o1js@$PINNED_O1JS in $dir (found: ${have:-none})"
    ( cd "$dir" && npm install --no-audit --no-fund --silent ) \
      || die "npm install failed in $dir"
    have="$(node -p "require('$dir/node_modules/o1js/package.json').version" 2>/dev/null)"
    [ "$have" = "$PINNED_O1JS" ] || die "o1js resolved to '${have:-none}', not the pin $PINNED_O1JS"
  fi
}

run_gate() { # run_gate <dir> -> exit status of the gate
  ( cd "$1" && npm run --silent gate )
}
run_rows() { # run_rows <dir> -> exit status of the Poseidon2 row measurement
  ( cd "$1" && npm run --silent poseidon2-rows )
}

# ── the headline run ──────────────────────────────────────────────────────────
if [ "${1:-}" != "--self-test" ]; then
  [ -d "$APP" ] || die "$APP does not exist"
  require_toolchain
  ensure_o1js "$APP"
  out="$(run_gate "$APP" 2>&1)"; rc=$?
  printf '%s\n' "$out"
  [ "$rc" -eq 0 ] || die "the attestation gate exited $rc"
  # Floors: a gate that ran but demonstrated nothing must not read as clean.
  n_ok="$(printf '%s' "$out" | grep -c '✓')"
  [ "$n_ok" -ge 18 ] || die "only $n_ok checks passed; expected >= 18 (a narrowed run is not a pass)"
  grep -q 'the zkApp CONSUMED the attestation proof' <<<"$out" \
    || die "the zkApp composition did not run"
  grep -q '=== PASS ===' <<<"$out" || die "the gate did not print its PASS line"

  # Leg 2: the Poseidon2-w16-BabyBear row measurement that
  # docs/MINA-VERIFIES-DREGG-FRI-SIZE.md quotes. It checks the circuit against
  # the Lean-pinned KAT of the DEPLOYED permutation, compiles and PROVES one
  # permutation, and RATCHETS the rows/perm figure: if o1js's gadget costs move
  # or the circuit changes, the document's headline is stale and this says so.
  # A cited measurement nobody re-runs is a number, not a measurement.
  rows_out="$(run_rows "$APP" 2>&1)"; rc=$?
  printf '%s\n' "$rows_out"
  [ "$rc" -eq 0 ] || die "the Poseidon2 row measurement exited $rc"
  grep -q 'the PROVEN public output == the deployed permutation' <<<"$rows_out" \
    || die "the Poseidon2 permutation was never actually proved"
  grep -q 'ratchet: ' <<<"$rows_out" || die "the rows/perm ratchet did not run"

  echo "mina-attestation: $n_ok checks green (compile+prove+verify, tamper rejected, zkApp consumed)"
  exit 0
fi

# ── --self-test: prove each leg can go red ────────────────────────────────────
# Faults are injected into a SCRATCH COPY, never the shared tree: a swarm runs in
# this working directory and a disarmed guard left behind is worse than no guard.
require_toolchain
WORK="$(mktemp -d "${TMPDIR:-/tmp}/mina-attest-selftest.XXXXXX")"
trap 'rm -rf "$WORK"' EXIT
COPY="$WORK/mina-zkapp"
mkdir -p "$COPY"
# Copy sources; symlink node_modules so we do not re-download o1js per fault.
( cd "$APP" && tar -cf - --exclude node_modules --exclude dist . ) | ( cd "$COPY" && tar -xf - )
ensure_o1js "$APP"
ln -s "$APP/node_modules" "$COPY/node_modules"

red=0; green=0
expect_red() { # expect_red <leg: gate|rows> <label> <sed-program> <file>
  local leg="$1" label="$2" prog="$3" file="$4"
  cp "$COPY/$file" "$WORK/.orig"
  perl -0pi -e "$prog" "$COPY/$file"
  if cmp -s "$WORK/.orig" "$COPY/$file"; then
    echo "  ✗ $label: the fault injection MATCHED NOTHING in $file"
    cp "$WORK/.orig" "$COPY/$file"; red=$((red+1)); return
  fi
  rm -rf "$COPY/dist"
  if "run_$leg" "$COPY" >"$WORK/.out" 2>&1; then
    echo "  ✗ $label: the gate stayed GREEN with the fault injected"
    red=$((red+1))
  else
    echo "  ✓ $label: gate went red — $(tail -3 "$WORK/.out" | grep -m1 . | cut -c1-72)"
    green=$((green+1))
  fi
  cp "$WORK/.orig" "$COPY/$file"
}

echo "self-test: injecting faults into $COPY"
expect_red gate "corrupted gold digest" \
  "s/0x10b41a5d3139ef0802e5faf6a7776aab079e44e99ec5b306ddddd88e15fe9e6d/0x10b41a5d3139ef0802e5faf6a7776aab079e44e99ec5b306ddddd88e15fe9e6e/" \
  src/rust-gold-vectors.ts
expect_red gate "corrupted Rust Merkle root" \
  "s/0x0f82b06f11a6dea422082c77668f6ac9fd97a5f21b81525cb61a46c335bbb777n/0x0f82b06f11a6dea422082c77668f6ac9fd97a5f21b81525cb61a46c335bbb778n/" \
  src/rust-gold-vectors.ts
expect_red gate "broken in-circuit Merkle fold" \
  "s/current = Poseidon\.hash\(\[left, right\]\)/current = Poseidon.hash([right, left])/" \
  src/DreggPoseidonAttestation.ts
expect_red gate "unpinned o1js" \
  "s/const PINNED_O1JS = '2\.15\.0'/const PINNED_O1JS = '9.9.9'/" \
  scripts/attestation-gate.ts
expect_red gate "type error in the committed source" \
  "s/export const ATTEST_DEPTH = 32;/export const ATTEST_DEPTH: string = 32;/" \
  src/DreggPoseidonAttestation.ts
# Leg 2: the row measurement must refuse to report a number for the wrong object,
# and must notice when the document's figure stops matching the circuit.
expect_red rows "Poseidon2 circuit diverges from the deployed KAT" \
  "s/const x6 = mul\(x4, x2\);/const x6 = mul(x4, x4);/" \
  src/Poseidon2BabyBearW16.ts
expect_red rows "rows/perm drifts from the figure the doc quotes" \
  "s/const RECORDED_ROWS_PER_PERM = 2600\.5;/const RECORDED_ROWS_PER_PERM = 2000;/" \
  scripts/poseidon2-babybear-rows.ts
# A lane bound of 2^32 instead of 2^31 puts x^7 past the Pasta modulus, i.e. the
# circuit stops being sound. `assertSafe` must refuse to emit a number for it.
expect_red rows "unsound lane bound (x^7 would wrap mod Pasta)" \
  "s/qp\.add\(r\)\.assertEquals\(v\.v\);\n  return \{ v: r, max: \(1n << 31n\) - 1n \};/qp.add(r).assertEquals(v.v);\n  return { v: r, max: (1n << 32n) - 1n };/" \
  src/Poseidon2BabyBearW16.ts

echo
if [ "$red" -gt 0 ]; then
  echo "self-test FAILED: $red of $((red+green)) fault(s) did not turn the gate red"
  exit 1
fi
echo "self-test PASS: all $green injected faults turned the gate red"
