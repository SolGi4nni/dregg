#!/usr/bin/env bash
# MINA PROOF MARSHAL GATE — a kimchi proof WE PRODUCED, turned into a wire object, read by Mina.
#
# The proof-side twin of `mina-vk-derivation-gate.sh`. That one asks whether Mina's reader accepts a
# VERIFICATION KEY derived from a Lean-assembled circuit; this one asks the same of a PROOF OBJECT
# marshalled out of a kimchi `ProverProof` the prover in this tree produced.
#
# WHAT IT MEASURES, in order, all green-or-bust, each judged on its tool's OWN sentinel and never on
# an exit code or on log motion:
#
#   1. `pickles_proof_wire`      → PROOF_WIRE_RESULT=GREEN
#      Seven real block proofs decode and re-encode BYTE-IDENTICALLY through our binprot encoder,
#      and an object we built round-trips. This is the encoder's verdict on real data.
#
#   2. `pickles_kimchi_marshal`  → PROOF_MARSHAL_RESULT=GREEN
#      A Pallas wrap proof over the Lean-authored `wrap_main` sub-circuit padded to the 2^15 Tock
#      domain, plus a Vesta step proof for `prev_evals`, both accepted by `kimchi::verifier::
#      batch_verify`, marshalled to `PicklesProofProofsVerified2ReprStableV2`; then FOUR
#      perturbations that must each move EXACTLY ONE NAMED WIRE FIELD, and FIVE input shapes that
#      must each be REFUSED. Its own red path is inside the binary: an accepted refusal or a
#      perturbation that moves the wrong field turns the sentinel RED.
#
#   3. `mina-proof-parse-gate.mjs` → PROOF_PARSE_GATE=GREEN
#      Both directories handed to `Pickles.proofOfBase64` — Mina's own OCaml reader, compiled into
#      o1js — and re-printed with `proofToBase64` and compared. Parse says well-formed; the
#      byte-identical re-print says our printer IS Mina's printer.
#
#   4. `--self-test` — THE RED PATH. The marshalled proof with one record field renamed must make
#      step 3 print PROOF_PARSE_GATE=RED. A gate that cannot go red is not a gate.
#
# ⚑ WHAT A GREEN HERE DOES NOT MEAN. `proofOfBase64` PARSES. It has been MEASURED to accept a field
# element set to the Pallas modulus, a curve point with `y` zeroed off the curve, and an IPA with
# fourteen of fifteen rounds. **The reader checks shape, not membership and not arity.** Parsing is
# a necessary and very weak condition. Nothing here verifies a proof and nothing is submitted.
#
# ⚠ Needs the openmina checkout at `../mina-rust` (read-only; the crate links it by path) and
# `bridge/mina-zkapp/node_modules/o1js`. Both ABSENT is RED, never skipped.
#
# USAGE
#   scripts/mina-proof-marshal-gate.sh              # the gate
#   scripts/mina-proof-marshal-gate.sh --self-test  # + PROVE it can go red
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
CRATE="$ROOT/metatheory/fixtures/pickles-extractors"
ZK="$ROOT/bridge/mina-zkapp"
GATE="$ZK/scripts/mina-proof-parse-gate.mjs"
WIRE_OUT="${TMPDIR:-/tmp}/pickles-proof-wire"
MARSHAL_OUT="${TMPDIR:-/tmp}/pickles-kimchi-marshal"

SELFTEST=0
for a in "$@"; do
  case "$a" in
    --self-test) SELFTEST=1 ;;
    -h|--help)   sed -n '2,40p' "$0"; exit 0 ;;
    *) echo "unknown argument $a" >&2; exit 2 ;;
  esac
done

fails=0
step() { echo; echo "── $* ──────────────────────────────────────────"; }
note() { echo "   $*"; }
red()  { echo "   RED:   $*"; fails=$((fails+1)); }

# Run a command, tee its output, and judge it ONLY by its own success sentinel.
run_sentinel() { # sentinel, log, cmd...
  local sentinel="$1"; shift
  local log="$1"; shift
  "$@" >"$log" 2>&1
  if grep -qF "$sentinel" "$log"; then
    note "$sentinel"
    grep -E '^\[(wrap|step|marshal|readback|perturb|refuse|parse|synthetic)\]' "$log" | sed 's/^/   /'
    return 0
  fi
  red "$sentinel not printed by: $*"
  tail -n 25 "$log" | sed 's/^/   | /'
  return 1
}

[ -d "$ROOT/../mina-rust" ] || red "openmina checkout missing at $ROOT/../mina-rust — the marshaller links it by path"
[ -d "$ZK/node_modules/o1js" ] || red "o1js missing at $ZK/node_modules/o1js (run 'cd bridge/mina-zkapp && npm ci')"
[ "$fails" -eq 0 ] || { echo; echo "== $fails PRECONDITION(S) RED =="; exit 1; }

step "build (release; a debug prove of a 2^15 circuit is minutes)"
if ! cargo build --release --manifest-path "$CRATE/Cargo.toml" \
      --bin pickles_proof_wire --bin pickles_kimchi_marshal >"${TMPDIR:-/tmp}/marshal-gate-build.log" 2>&1; then
  red "cargo build failed"
  tail -n 25 "${TMPDIR:-/tmp}/marshal-gate-build.log" | sed 's/^/   | /'
  echo; echo "== $fails STEP(S) RED =="; exit 1
fi
note "pickles_proof_wire, pickles_kimchi_marshal built"

step "1. the encoder on seven real block proofs (byte identity)"
( cd "$CRATE" && run_sentinel "PROOF_WIRE_RESULT=GREEN" "${TMPDIR:-/tmp}/marshal-gate-wire.log" \
    "$CRATE/target/release/pickles_proof_wire" "$WIRE_OUT" ) || fails=$((fails+1))

step "2. the marshaller: our own kimchi proofs -> the wire record"
( cd "$CRATE" && run_sentinel "PROOF_MARSHAL_RESULT=GREEN" "${TMPDIR:-/tmp}/marshal-gate-marshal.log" \
    "$CRATE/target/release/pickles_kimchi_marshal" "$MARSHAL_OUT" ) || fails=$((fails+1))

step "3. Mina's own reader on both (parse + byte-identical re-print)"
( cd "$ZK" && run_sentinel "PROOF_PARSE_GATE=GREEN" "${TMPDIR:-/tmp}/marshal-gate-parse-wire.log" \
    node "$GATE" --dir "$WIRE_OUT" ) || fails=$((fails+1))
( cd "$ZK" && run_sentinel "PROOF_PARSE_GATE=GREEN" "${TMPDIR:-/tmp}/marshal-gate-parse-marshal.log" \
    node "$GATE" --dir "$MARSHAL_OUT" ) || fails=$((fails+1))

if [ "$SELFTEST" = 1 ]; then
  step "4. RED PATH — the marshalled proof with one field renamed must be REFUSED"
  BENT="${TMPDIR:-/tmp}/marshal-gate-bent.json"
  node -e '
    const fs = require("node:fs");
    const j = JSON.parse(fs.readFileSync(process.argv[1], "utf8"));
    const raw = Buffer.from(j.proof, "base64").toString("binary");
    if (!raw.includes("(ft_eval1 ")) { console.error("the marshalled sexp has no ft_eval1 to bend"); process.exit(2); }
    j.proof = Buffer.from(raw.replace("(ft_eval1 ", "(ft_evalX "), "binary").toString("base64");
    fs.writeFileSync(process.argv[2], JSON.stringify(j));
  ' "$MARSHAL_OUT/marshalled.o1js-proof.json" "$BENT" || red "could not build the bent proof"
  ( cd "$ZK" && node "$GATE" --proof "$BENT" ) >"${TMPDIR:-/tmp}/marshal-gate-red.log" 2>&1
  if grep -qF "PROOF_PARSE_GATE=RED" "${TMPDIR:-/tmp}/marshal-gate-red.log"; then
    note "PROOF_PARSE_GATE=RED on the bent proof — the gate can go red"
    grep -E '^\[parse\]' "${TMPDIR:-/tmp}/marshal-gate-red.log" | sed 's/^/   /'
  else
    red "the bent proof did NOT turn the parse gate red — this gate cannot go red"
    tail -n 12 "${TMPDIR:-/tmp}/marshal-gate-red.log" | sed 's/^/   | /'
  fi
fi

echo
if [ "$fails" -eq 0 ]; then
  echo "== ALL GREEN — a proof we produced is a wire object Mina's own reader parses and re-prints byte-identically =="
  echo "   (parsing is shape, not membership: p-valued fields, off-curve points and a 14-round IPA all parse.)"
  exit 0
else
  echo "== $fails STEP(S) RED =="
  exit 1
fi
