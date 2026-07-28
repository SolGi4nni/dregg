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
#   [6] the root anchor. TWO conditions of different kinds, and the gate keeps
#       them apart because conflating them is how a trusted key came to be
#       recorded as a fix:
#         - a PROOF OBLIGATION (`DreggAnchorStatement`): the anchored root is
#           the proof's public input, and the statement pins slot 0 of the
#           anchored tree to `Poseidon(R_bb)` for a BabyBear-Poseidon2 MMCS root
#           with a known opening. The gate checks the obligation REFUSES a root
#           with no vouch in it — an obligation that always holds is not one.
#         - a PLACEHOLDER SIGNATURE, tested as a placeholder and never called
#           authorization: a non-placeholder signer, an empty signature, a
#           signature for another transition, and a signature over a root the
#           PROOF does not claim are each refused.
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
# FOURTH leg (`poseidon2-merkle-rows.ts`) — RUNG 1, the Merkle OPENING. A FRI
# verifier never buys one permutation, it buys openings, and an opening is not
# `depth x rows-per-perm`: it also pays 8 witnessed-lane range checks and 8 lane
# reductions per node, neither of which a single permutation pays, and WITHOUT
# the range checks the bound tracking the whole 2,600.5 rests on is a claim
# about unconstrained witnesses. KAT'd elementwise against the DEPLOYED Rust
# MMCS (`p2merkle`: p3 `default_babybear_poseidon2_16` +
# `TruncatedPermutation<.,2,8,16>` + `PaddingFreeSponge<.,16,8,8>`) on rows
# carrying a git HEAD, a timestamp and a 128-bit nonce. Ratchets three figures.
#
# FIFTH leg (`fri-query-rows.ts`) — RUNG 2, ONE FRI QUERY at the deployed root's
# geometry (|D^0| = 2^22, 16 arity-2 commit layers, cap_height 0). The fold
# arithmetic is KAT'd against p3's own `BinomialExtensionField<BabyBear,4>` via
# the probe's `p2fold`, one commit-phase round COMPILES and PROVES, and the
# whole query's `getRows()` is ratcheted. ⚑ Needs a 16 GB node heap (the npm
# script passes `--max-old-space-size`); o1js OOMs at the 4 GB default.
#
# SIXTH leg (`fri-challenger-rows.ts`) — RUNG 3, THE CHALLENGER, and the one
# that changes what the others mean. Rungs 1/2 walk a query at a WITNESSED index
# under WITNESSED betas: that statement says "there EXIST 19 indices at which
# this proof is consistent", and a cheating prover supplies the 19 it can
# answer. This leg builds the Fiat-Shamir function itself —
# `DuplexChallenger<BabyBear, Poseidon2BabyBear<16>, 16, 8>`, KAT'd against the
# DEPLOYED one (`p2chal`, `p2fritranscript`) on the exact schedule
# `p3_fri::verifier::verify_fri` runs — so alpha, all 16 betas, the 16-bit query
# PoW and all 19 query indices are DERIVED. Four state-machine edges each get a
# discriminating polarity, the one constraint a witness can lie about (the
# bit-split's high part) gets a lying witness and must refuse, and a 4-layer
# instance of the same schedule COMPILES and PROVES.
#
# SEVENTH leg (`fri-chain-rows.ts`) — RUNG 4, the COMMIT PHASE as ONE object:
# all 16 fold layers chained, KAT'd against p3's OWN 16-round chain (`p2chain`)
# rather than 16 calls to a one-round emitter. ⚑ That distinction is not
# academic: this leg immediately found the coset descent taking `indexBits[r]`
# where `verify_query` takes `indexBits[r+1]` — right whenever two consecutive
# index bits agree, hence right on ~half of every chain and on ALL of the
# all-zero index `getRows()` supplies. The single-round descent check, made
# deterministic and both-polarity the day before, stayed green through it,
# because one round never consumes two bits. Also carries [4b], THE SEAM: one
# program that DERIVES the index from the transcript and then walks the chain at
# it, proved on an honest witness found by fixed-point search.
#
# ⚑ NO SKIPS. A missing `node`, a missing `npm`, a missing `cargo`, an absent or
# unpinned o1js, a type error, or a diverging vector are all FAILURES — the same
# discipline as `embedded-js` and `opentheory-importer`. ~11 min warm (the
# Rung-2/3/4 legs are ~8 of them: 684,726 rows is slow to BUILD, never mind
# prove, and three ZkProgram compiles run). Needs cargo for legs 3-7; no Lean.
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
# Rung 1: the Merkle opening, KAT'd against the DEPLOYED BabyBear MMCS.
run_merkle() { # run_merkle <dir>
  ( cd "$1" && DREGG_PROBE_DIR="${PROBE_DIR:-$PROBE}" DREGG_ATTEST_GIT_DIR="$ROOT" \
      npm run --silent poseidon2-merkle )
}
# Rung 2: one FRI query at the deployed geometry.
run_fri() { # run_fri <dir>
  ( cd "$1" && DREGG_PROBE_DIR="${PROBE_DIR:-$PROBE}" DREGG_ATTEST_GIT_DIR="$ROOT" \
      npm run --silent fri-query )
}
# Rung 3: the Fiat-Shamir challenger — the rung that makes the walk the PROVER'S.
run_chal() { # run_chal <dir>
  ( cd "$1" && DREGG_PROBE_DIR="${PROBE_DIR:-$PROBE}" DREGG_ATTEST_GIT_DIR="$ROOT" \
      npm run --silent fri-challenger )
}
# Rung 4: the 16-layer commit phase as one chain, plus the seam.
run_chain() { # run_chain <dir>
  ( cd "$1" && DREGG_PROBE_DIR="${PROBE_DIR:-$PROBE}" DREGG_ATTEST_GIT_DIR="$ROOT" \
      npm run --silent fri-chain )
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
  [ "$n_ok" -ge 35 ] || die "only $n_ok checks passed; expected >= 35 (a narrowed run is not a pass)"
  grep -q 'the zkApp CONSUMED the attestation proof' <<<"$out" \
    || die "the zkApp composition did not run"
  grep -q 'refused as an invalid PROOF' <<<"$out" \
    || die "the well-formed-proof-of-another-statement leg did not run"
  grep -q 'the identical proof bytes are ACCEPTED' <<<"$out" \
    || die "the spliced-proof CONTROL did not run (the refusal above is then unattributable)"
  grep -q 'an anchor signed by a NON-placeholder key' <<<"$out" \
    || die "the setDreggRoot placeholder-key leg did not run"
  grep -q 'the OBLIGATION refuses a root whose slot 0 is not a BabyBear vouch' <<<"$out" \
    || die "the anchor PROOF OBLIGATION leg did not run (the anchor would be key-only again)"
  grep -q 'a signature over a root the anchor PROOF does not claim' <<<"$out" \
    || die "the proof/signature agreement leg did not run"
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

  # Leg 4: RUNG 1 — the Merkle OPENING, elementwise against the DEPLOYED p3 MMCS.
  merkle_out="$(run_merkle "$APP" 2>&1)"; rc=$?
  printf '%s\n' "$merkle_out"
  [ "$rc" -eq 0 ] || die "the Poseidon2 Merkle-opening leg exited $rc"
  n_merkle="$(printf '%s' "$merkle_out" | grep -c '✓')"
  [ "$n_merkle" -ge 12 ] || die "only $n_merkle Merkle checks passed; expected >= 12"
  grep -q 'siblings, all 22 isRight bits, all 22 nodes and the root agree' <<<"$merkle_out" \
    || die "the elementwise Rust<->o1js MMCS cross-check did not run"
  grep -q 'the circuit REFUSES an out-of-range sibling lane' <<<"$merkle_out" \
    || die "the bound-tracking enforcement check did not run (the row count would be for an UNSOUND circuit)"
  grep -q 'the PROVEN public output == the leaf digest the DEPLOYED p3 MMCS emitted' <<<"$merkle_out" \
    || die "the Merkle opening was never actually proved"
  grep -q 'ratchet: ' <<<"$merkle_out" || die "the Merkle rows ratchet did not run"
  grep -q '=== MERKLE PASS ===' <<<"$merkle_out" || die "the Merkle leg did not print its PASS line"

  # Leg 5: RUNG 2 — one FRI query at the deployed geometry.
  fri_out="$(run_fri "$APP" 2>&1)"; rc=$?
  printf '%s\n' "$fri_out"
  [ "$rc" -eq 0 ] || die "the FRI query leg exited $rc"
  n_fri="$(printf '%s' "$fri_out" | grep -c '✓')"
  [ "$n_fri" -ge 10 ] || die "only $n_fri FRI checks passed; expected >= 10"
  grep -q 'fold_row (arity 2, two-point Lagrange) agrees with p3' <<<"$fri_out" \
    || die "the fold_row cross-check against p3 did not run"
  grep -q 'BOTH polarities' <<<"$fri_out" \
    || die "the coset-descent sign check did not run (it is wrong on half of all indices)"
  grep -q 'a commit-phase round PROVES and VERIFIES' <<<"$fri_out" \
    || die "no FRI commit-phase round was actually proved"
  grep -q 'ratchet: ' <<<"$fri_out" || die "the FRI query rows ratchet did not run"
  grep -q '=== FRI QUERY PASS ===' <<<"$fri_out" || die "the FRI leg did not print its PASS line"

  # Leg 6: RUNG 3 — the CHALLENGER. Without this the query walk proves nothing,
  # because a prover picks its own indices.
  chal_out="$(run_chal "$APP" 2>&1)"; rc=$?
  printf '%s\n' "$chal_out"
  [ "$rc" -eq 0 ] || die "the FRI challenger leg exited $rc"
  n_chal="$(printf '%s' "$chal_out" | grep -c '✓')"
  [ "$n_chal" -ge 25 ] || die "only $n_chal challenger checks passed; expected >= 25"
  grep -q 'all 19 query indices agree — DERIVED, not witnessed' <<<"$chal_out" \
    || die "the query-index derivation did not run (the FRI walk is over CHOSEN indices)"
  grep -q 'check_witness(0' <<<"$chal_out" \
    || die "the 0-bit check_witness edge did not run (all 16 betas would be wrong)"
  grep -q 'is CHOOSEABLE\|cannot be split to claim index' <<<"$chal_out" \
    || die "the bit-split soundness check did not run (the index would be witness-chosen)"
  grep -q 'a transcript PROVES and VERIFIES' <<<"$chal_out" \
    || die "no transcript was actually proved"
  grep -q 'NO proof exists for a query PoW witness' <<<"$chal_out" \
    || die "the query-PoW refusal did not run"
  grep -q 'ratchet: ' <<<"$chal_out" || die "the transcript rows ratchet did not run"
  grep -q '=== FRI CHALLENGER PASS ===' <<<"$chal_out" || die "the challenger leg did not print its PASS line"

  # Leg 7: RUNG 4 — the 16-layer chain, and the seam that joins it to leg 6.
  chain_out="$(run_chain "$APP" 2>&1)"; rc=$?
  printf '%s\n' "$chain_out"
  [ "$rc" -eq 0 ] || die "the FRI chain leg exited $rc"
  n_chain="$(printf '%s' "$chain_out" | grep -c '✓')"
  [ "$n_chain" -ge 18 ] || die "only $n_chain chain checks passed; expected >= 18"
  grep -q 'alternating bits (they differ at EVERY round)' <<<"$chain_out" \
    || die "the bit-alternating index did not run (the descent bug is invisible without it)"
  grep -q 'the check discriminates' <<<"$chain_out" \
    || die "the wrong-bit twin did not run (the chain KAT would be unattributable)"
  grep -q 'PROVES and VERIFIES' <<<"$chain_out" \
    || die "the 16-layer chain was never actually proved"
  grep -q 'NO proof exists at a different query index' <<<"$chain_out" \
    || die "the one-index-threads-all-layers check did not run"
  grep -q 'is DERIVED from the transcript, not witnessed' <<<"$chain_out" \
    || die "THE SEAM did not run — the transcript and the walk are still two unjoined objects"
  grep -q 'ratchet: ' <<<"$chain_out" || die "the chain rows ratchet did not run"
  grep -q '=== FRI CHAIN PASS ===' <<<"$chain_out" || die "the chain leg did not print its PASS line"

  echo "mina-attestation: $n_ok + $n_probe + $n_merkle + $n_fri + $n_chal + $n_chain checks green" \
       "(compile+prove+verify, tamper rejected, zkApp consumed, anchor PROOF-OBLIGATED +" \
       "placeholder-keyed, spliced proof refused, Rust emitter cross-checked; Merkle opening," \
       "FRI query, Fiat-Shamir transcript and the 16-layer fold chain all measured against p3," \
       "with the query index DERIVED rather than witnessed)"
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
# `useDefineForClassFields: false` is why the zkApp runs at all: at ES2022
# TypeScript's class-field emit runs `Object.defineProperty` BEFORE o1js's
# `@state` decorator has bound the field to its contract, and `State.set` then
# throws. It is a one-word setting in a config file that nothing else guards, so
# a well-meaning tsconfig cleanup could delete the reason this directory works.
expect_red gate "useDefineForClassFields flipped (o1js's @state decorator loses to TS class fields)" \
  "s/\"useDefineForClassFields\": false/\"useDefineForClassFields\": true/" \
  tsconfig.json
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

# The anchor's PROOF OBLIGATION, disarmed the way an obligation usually is: made
# true for free. `setDreggRoot`'s whole claim to be more than a signature check
# is that this fold has to REACH the anchored root, so leg [6] must notice.
expect_red gate "the anchor obligation made vacuous (the fold no longer has to reach the root)" \
  "s/cur\.assertEquals\(anchored\);/cur.assertEquals(cur);/" \
  src/DreggPoseidonAttestation.ts
# And the vouch must actually be a function of the BabyBear side: hashing a
# constant instead of the folded root would leave every check above green while
# the obligation stopped saying anything about an MMCS root at all.
expect_red gate "the vouch stops depending on the BabyBear root" \
  "s/const vouch = Poseidon\.hash\(bbRoot\.limbs\);/const vouch = Poseidon.hash([Field(7)]);/" \
  src/DreggPoseidonAttestation.ts

# ── Leg 4: RUNG 1, the Merkle opening. Three faults, chosen so each is visible
# to a DIFFERENT instrument: the twin-vs-p3 comparison, the circuit-vs-twin
# comparison, and the soundness check that nothing else can see.
expect_red merkle "the o1js compression twin transposed (twin vs p3)" \
  "s/return permBigInt\(\[\.\.\.l, \.\.\.r\]\)\.slice\(0, DIGEST_ELEMS\);/return permBigInt([...r, ...l]).slice(0, DIGEST_ELEMS);/" \
  src/Poseidon2Merkle.ts
expect_red merkle "the in-CIRCUIT compression transposed (circuit vs twin)" \
  "s/provablePermBounded\(\[\.\.\.l\.limbs, \.\.\.r\.limbs\], \(1n << 31n\) - 1n\)/provablePermBounded([...r.limbs, ...l.limbs], (1n << 31n) - 1n)/" \
  src/Poseidon2Merkle.ts
# ⚑ THE ONE NOTHING ELSE SEES. Drop the witnessed-lane range checks and every
# KAT still passes, every row count still prints — and the bound tracking the
# whole 2,600.5 rests on becomes a claim about unconstrained witnesses. This is
# the fault that makes the measurement one of an UNSOUND circuit.
expect_red merkle "witnessed-lane range checks removed (rows measured for an UNSOUND circuit)" \
  "s/  for \(const l of d\.limbs\) assertLaneLt2p31\(l\);/  \/* fault *\//" \
  src/Poseidon2Merkle.ts
expect_red merkle "rows/level drifts from the figure the doc quotes" \
  "s/const RECORDED_ROWS_PER_LEVEL = 2677;/const RECORDED_ROWS_PER_LEVEL = 2400;/" \
  scripts/poseidon2-merkle-rows.ts

# ── Leg 5: RUNG 2, the FRI query. The coset-descent sign is the interesting one:
# it is wrong on exactly half of all query indices, so a test that happened to
# pick an even index would never see it.
expect_red fri "the coset descent drops its sign (wrong on half of all indices)" \
  "s/return Provable\.if\(bit, neg, sq\);/return sq;/" \
  src/FriQueryStep.ts
expect_red fri "the extension modulus X^4 - W is wrong" \
  "s/export const EXT_W = 11n;/export const EXT_W = 12n;/" \
  src/FriQueryStep.ts
expect_red fri "rows/query drifts from the figure the doc quotes" \
  "s/const RECORDED_QUERY_ROWS = 684_726;/const RECORDED_QUERY_ROWS = 600_000;/" \
  scripts/fri-query-rows.ts

# ── Leg 6: RUNG 3, the CHALLENGER. One fault per state-machine edge that a
# transcription gets wrong while every hash still matches, plus the one
# constraint a witness can lie about, plus the ratchets.
expect_red chal "the output buffer is popped from the FRONT (samples in the wrong order)" \
  "s/    return this\.outputBuffer\.pop\(\)!;/    return this.outputBuffer.shift()!;/" \
  src/FriChallenger.ts
expect_red chal "observe stops discarding unread squeezes" \
  "s/  observe\(v: bigint\) \{\n    this\.outputBuffer = \[\];/  observe(v: bigint) {\n    \/* fault *\//" \
  src/FriChallenger.ts
expect_red chal "a 0-bit check_witness OBSERVES the witness (all 16 betas move)" \
  "s/    if \(bits === 0\) return true;/    if (bits === -1) return true;/" \
  src/FriChallenger.ts
# The unabsorbed rate lanes are OVERWRITTEN, not zero-filled. A challenger that
# zero-filled them agrees on every full-rate absorb and diverges the moment a
# PARTIAL buffer is duplexed — which the deployed schedule does at alpha.
expect_red chal "a partial absorb zero-fills the unabsorbed rate" \
  "s/    for \(let i = 0; i < this\.inputBuffer\.length; i\+\+\) this\.state\[i\] = this\.inputBuffer\[i\];/    for (let i = 0; i < RATE; i++) this.state[i] = this.inputBuffer[i] ?? 0n;/" \
  src/FriChallenger.ts
# ⚑ THE ONE NOTHING ELSE SEES. Every KAT in the leg compares against p3 on an
# HONEST witness, and an honest witness produces the right bit decomposition
# whether or not anything forces it to. Drop the bound on the high part and
# `c = hi*2^k + sum b_i 2^i` is satisfiable over Pasta for EVERY bit pattern —
# the prover chooses its own query indices out of a perfectly correct sponge,
# and every other check in this leg stays green.
expect_red chal "the bit-split's high-part bound removed (the query index becomes witness-CHOSEN)" \
  "s/  assertLtPow2\(hi, 31 - k\);/  \/* fault *\//" \
  src/FriChallenger.ts
expect_red chal "assertLtPow2 made a no-op" \
  "s/  if \(n <= 0\) \{/  if (n >= 0) return;\n  if (n <= 0) {/" \
  src/FriChallenger.ts
expect_red chal "rows/transcript drifts from the figure the doc quotes" \
  "s/const RECORDED_TRANSCRIPT_ROWS = 62_637;/const RECORDED_TRANSCRIPT_ROWS = 50_000;/" \
  scripts/fri-challenger-rows.ts
expect_red chal "the transcript's permutation count drifts" \
  "s/const RECORDED_TRANSCRIPT_PERMS = 23;/const RECORDED_TRANSCRIPT_PERMS = 22;/" \
  scripts/fri-challenger-rows.ts

# ── Leg 7: RUNG 4, the 16-layer chain. The first two faults are THE DEFECT THIS
# RUNG FOUND, put back: the coset descent driven by the slot bit instead of the
# next index bit. It is right whenever two consecutive index bits agree — so on
# the all-zero index every row measurement uses, and on about half of any
# chain's rounds — and no single-round check can see it, because one round never
# consumes two bits.
expect_red chain "the TWIN's coset descent driven by the SLOT bit (the defect this rung found)" \
  "s/    x = r \+ 1 < logD0 && w\.indexBits\[r \+ 1\] \? md\(P - sq\) : sq;/    x = w.indexBits[r] ? md(P - sq) : sq;/" \
  src/FriQueryStep.ts
expect_red chain "the CIRCUIT's coset descent driven by the SLOT bit" \
  "s/      r \+ 1 < logD0 \? w\.indexBits\[r \+ 1\] : Bool\(false\),/      w.indexBits[r],/" \
  src/FriQueryStep.ts
expect_red chain "the roll-in drops its beta^arity factor" \
  "s/      folded = extAdd\(folded, extMul\(extPowPow2\(w\.rounds\[r\]\.beta, 1\), ri\.value\)\);/      folded = extAdd(folded, ri.value);/" \
  src/FriQueryStep.ts
# A chain that does not have to LAND anywhere is not a FRI check: the final-poly
# comparison is the only thing that makes the fold sequence closed.
expect_red chain "the final-polynomial comparison made vacuous" \
  "s/        canonicalLane\(want\.limbs\[j\], LANE_MAX\),/        canonicalLane(folded.limbs[j], LANE_MAX),/" \
  src/FriQueryStep.ts
# THE SEAM. The index the chain walks must be the DERIVED one and the beta each
# round folds at must be the DERIVED one. Either substitution leaves a program
# that measures the same and verifies something strictly weaker.
expect_red chain "the seam walks a witnessed index instead of the derived one" \
  "s/          const bits = chal\.queryIndexBits\[0\];/          const bits = Provable.witness(Provable.Array(Bool, indexBits), () =>\n            Array.from({ length: indexBits }, () => Bool(false)),\n          );/" \
  src/FriChallenger.ts
expect_red chain "the seam folds at the wrong round's derived beta" \
  "s/              beta: chal\.betas\[r\],/              beta: chal.betas[(r + 1) % layers],/" \
  src/FriChallenger.ts
expect_red chain "rows/chain drifts from the figure the doc quotes" \
  "s/const RECORDED_DEPLOYED_ROWS = 623_310;/const RECORDED_DEPLOYED_ROWS = 600_000;/" \
  scripts/fri-chain-rows.ts

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
