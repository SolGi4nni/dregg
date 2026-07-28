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
#   [6] the root anchor is RELAY-AUTHORIZED: a non-relay signer, an empty
#       signature and a signature for another transition are each refused.
#       (`setDreggRoot` used to take no authorization at all while its comment
#       said "relay-authorized"; these are the checks that make the comment
#       true, and the first two would have passed against the old contract.)
#   [7] a WELL-FORMED proof of a statement its prover had no witness for is
#       refused by VERIFICATION, not by the parser — at the ZkProgram level and
#       again by moving a proof between two signed account updates, with the
#       identical bytes accepted on their own update as the control. A damaged
#       encoding is refused at DECODE, separately, so the two cannot be
#       mistaken for each other (the devnet run made exactly that mistake).
#
# Second leg (`bridge/mina-zkapp/scripts/poseidon2-babybear-rows.ts`): the
# Poseidon2-w16-BabyBear permutation as an o1js circuit, checked against the
# Lean-pinned KAT of the DEPLOYED hash, compiled and PROVED, and its rows/perm
# figure RATCHETED against the number docs/MINA-VERIFIES-DREGG-FRI-SIZE.md quotes.
#
# THIRD leg (`bridge/mina-zkapp/scripts/probe-gate.ts`) — the DREGG SIDE, in
# Rust. This gate was written Node-only and said so; the unstated consequence is
# that the half of the bridge that PRODUCES the attested root ran in no gate at
# all. `circuit-prove/sketches/mina-pasta-hash-probe`'s five tests were reachable
# only by hand, and the `merkle` subcommand that emits the deployed root ran only
# inside `npm run devnet:emit-root`, which needs devnet keys and is deliberately
# ungated. So this leg runs `cargo test --locked` in the probe crate, then the
# `merkle` subcommand end to end on leaves that cannot have been precomputed
# (domain tag + git HEAD + timestamp + 128-bit nonce), requires o1js to reproduce
# the root and all 32 siblings elementwise, and then bends the emission three
# ways to show the comparison can say no.
#
# ⚑ NO SKIPS. A missing `node`, a missing `npm`, a missing `cargo`, an absent or
# unpinned o1js, a type error, or a diverging vector are all FAILURES — the same
# discipline as `embedded-js` and `opentheory-importer`. ~75s including `npm ci`
# when cold, ~60s warm. Needs cargo for the third leg; no Lean.
#
#   bash scripts/check-mina-attestation.sh
#   bash scripts/check-mina-attestation.sh --self-test    # prove it can go red
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
APP="$ROOT/bridge/mina-zkapp"
PROBE="$ROOT/circuit-prove/sketches/mina-pasta-hash-probe"
PINNED_O1JS="2.15.0"

die() { echo "FAIL: $*" >&2; exit 1; }

require_toolchain() {
  command -v node  >/dev/null 2>&1 || die "node is not on PATH (this gate does not skip)"
  command -v npm   >/dev/null 2>&1 || die "npm is not on PATH (this gate does not skip)"
  # The Rust leg is not optional and does not degrade to "JS only": the emitting
  # side of the bridge going unwatched is the exact defect this leg closes.
  command -v cargo >/dev/null 2>&1 || die "cargo is not on PATH (the dregg-side probe leg does not skip)"
  command -v git   >/dev/null 2>&1 || die "git is not on PATH (the emitted leaf names a commit)"
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
# The dregg-side leg. `DREGG_PROBE_DIR` selects which copy of the Rust crate is
# under test (the self-test points it at a scratch copy so faults never touch
# the shared tree); `DREGG_ATTEST_GIT_DIR` keeps the emitted leaf naming THIS
# tree's HEAD even when the crate under test is a copy outside the repository.
run_probe() { # run_probe <dir> -> exit status of the dregg-side emitting leg
  ( cd "$1" && DREGG_PROBE_DIR="${PROBE_DIR:-$PROBE}" DREGG_ATTEST_GIT_DIR="$ROOT" \
      npm run --silent probe )
}

# ── the headline run ──────────────────────────────────────────────────────────
if [ "${1:-}" != "--self-test" ]; then
  [ -d "$APP" ] || die "$APP does not exist"
  [ -f "$PROBE/Cargo.toml" ] || die "$PROBE does not exist (the dregg-side emitter)"
  require_toolchain
  ensure_o1js "$APP"
  out="$(run_gate "$APP" 2>&1)"; rc=$?
  printf '%s\n' "$out"
  [ "$rc" -eq 0 ] || die "the attestation gate exited $rc"
  # Floors: a gate that ran but demonstrated nothing must not read as clean.
  n_ok="$(printf '%s' "$out" | grep -c '✓')"
  [ "$n_ok" -ge 28 ] || die "only $n_ok checks passed; expected >= 28 (a narrowed run is not a pass)"
  grep -q 'the zkApp CONSUMED the attestation proof' <<<"$out" \
    || die "the zkApp composition did not run"
  grep -q 'refused as an invalid PROOF' <<<"$out" \
    || die "the well-formed-proof-of-another-statement leg did not run"
  grep -q 'the identical proof bytes are ACCEPTED' <<<"$out" \
    || die "the spliced-proof CONTROL did not run (the refusal above is then unattributable)"
  grep -q 'an anchor signed by a NON-relay key' <<<"$out" \
    || die "the setDreggRoot authorization leg did not run"
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

  # Leg 3: the DREGG SIDE. `cargo test` in the probe crate, then the `merkle`
  # subcommand that emits the deployed root, cross-checked elementwise against
  # o1js on leaves that cannot have been precomputed. This is the half of the
  # bridge that had no gate at all.
  probe_out="$(run_probe "$APP" 2>&1)"; rc=$?
  printf '%s\n' "$probe_out"
  [ "$rc" -eq 0 ] || die "the dregg-side probe leg exited $rc"
  n_probe="$(printf '%s' "$probe_out" | grep -c '✓')"
  [ "$n_probe" -ge 10 ] || die "only $n_probe probe checks passed; expected >= 10"
  grep -q 'cargo test: ' <<<"$probe_out" || die "the probe crate's own tests did not run"
  grep -q 'all 32 siblings' <<<"$probe_out" \
    || die "the elementwise Rust<->o1js cross-check did not run"
  grep -q 'a doctored SIBLING' <<<"$probe_out" \
    || die "the cross-check's discriminating polarity did not run"
  grep -q '=== PROBE PASS ===' <<<"$probe_out" || die "the probe leg did not print its PASS line"

  echo "mina-attestation: $n_ok + $n_probe checks green (compile+prove+verify, tamper rejected," \
       "zkApp consumed, anchor authorized, spliced proof refused, Rust emitter cross-checked)"
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

# The Rust crate gets the same treatment — faults go into a COPY, never into the
# shared tree. `target/` is symlinked so each fault rebuilds only the probe
# crate rather than mina-poseidon and arkworks from scratch.
PCOPY="$WORK/mina-pasta-hash-probe"
mkdir -p "$PCOPY"
( cd "$PROBE" && tar -cf - --exclude target . ) | ( cd "$PCOPY" && tar -xf - )
mkdir -p "$PROBE/target"
ln -s "$PROBE/target" "$PCOPY/target"
PROBE_DIR="$PCOPY"

red=0; green=0
expect_red() { # expect_red <leg: gate|rows|probe> <label> <perl-program> <file> [base-dir]
  local leg="$1" label="$2" prog="$3" file="$4" base="${5:-$COPY}"
  cp "$base/$file" "$WORK/.orig"
  perl -0pi -e "$prog" "$base/$file"
  if cmp -s "$WORK/.orig" "$base/$file"; then
    echo "  ✗ $label: the fault injection MATCHED NOTHING in $file"
    cp "$WORK/.orig" "$base/$file"; red=$((red+1)); return
  fi
  rm -rf "$COPY/dist"
  if "run_$leg" "$COPY" >"$WORK/.out" 2>&1; then
    echo "  ✗ $label: the gate stayed GREEN with the fault injected"
    red=$((red+1))
  else
    echo "  ✓ $label: gate went red — $(tail -3 "$WORK/.out" | grep -m1 . | cut -c1-72)"
    green=$((green+1))
  fi
  cp "$WORK/.orig" "$base/$file"
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
# The authorization on `setDreggRoot`, disarmed the way it was originally absent:
# a check that is always true. Leg [6] must notice, because "any caller can
# re-anchor" is precisely what a passing gate used to be compatible with.
expect_red gate "setDreggRoot authorization made vacuous" \
  "s/\.assertTrue\('setDreggRoot: not signed by the anchored relay key'\)/.or(Bool(true)).assertTrue('setDreggRoot: not signed by the anchored relay key')/" \
  src/DreggPoseidonAttestation.ts
# Leg [7] is a controlled experiment: the spliced proof must carry a DIFFERENT
# statement, or its rejection means nothing. Make the "spliced" statement equal
# to the honest one and the leg must refuse to report a result.
expect_red gate "spliced-proof experiment stops varying the statement" \
  "s/const splicedJson = \{ \.\.\.honestJson, publicInput: \[foreignRoot\.toString\(\)\] \};/const splicedJson = { ...honestJson };/" \
  scripts/attestation-gate.ts
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

# ── Leg 3: the DREGG SIDE. Faults go into $PCOPY, a scratch copy of the Rust
# crate. Three of them, chosen to separate what each instrument sees:
#   - a transposed `compress` breaks BOTH the crate's KATs and the cross-check;
#   - flipping an assertion inside `sparse_path_folds_through_the_gold_depth2_root`
#     shows THAT test — the one the deployment record named as running in no
#     gate — actually executes here;
#   - bending the `merkle` subcommand's printed root breaks the emitted object
#     while every unit test still passes. Nothing in the crate covers the emit
#     path, so this fault is invisible to `cargo test` and visible only to the
#     elementwise cross-check. That gap is the reason this leg exists.
expect_red probe "transposed Rust compress(l, r)" \
  "s/mina_poseidon_hash\(&\[left, right\]\)/mina_poseidon_hash(&[right, left])/" \
  src/main.rs "$PCOPY"
expect_red probe "the depth-32 sparse-path test's own assertion" \
  "s/assert!\(!is_right\[0\]\);/assert!(is_right[0]);/" \
  src/main.rs "$PCOPY"
expect_red probe "the emitted root is off by one level (cargo test cannot see this)" \
  "s/fp_hex\(nodes\[depth - 1\]\)/fp_hex(nodes[depth - 2])/" \
  src/main.rs "$PCOPY"

echo
if [ "$red" -gt 0 ]; then
  echo "self-test FAILED: $red of $((red+green)) fault(s) did not turn the gate red"
  exit 1
fi
echo "self-test PASS: all $green injected faults turned the gate red"
