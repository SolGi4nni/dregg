#!/usr/bin/env bash
#
# demo.sh — the "trustless web fact you can reuse" story, end to end.
#
#   1. PROVE   a real Coinbase BTC spot quote into a portable proof file.
#   2. SEND    the file to a "friend" (here: just a copy — a proof is only a file).
#   3. VERIFY  the friend re-checks it, trusting no one, offline from the API.
#   4. TAMPER  any single-byte change makes verification refuse (fail-closed).
#
# Runs against the default (self-hosted, in-process notary) build — no network,
# no third party. Pass --live to route the same machinery through the real
# internet-host MPC-TLS path (heavier build; see README "honest boundary").

set -euo pipefail
cd "$(dirname "$0")"

ASSET="${1:-BTC-USD}"
PROOF="proof.json"
FRIEND_COPY="proof.received.json"
TAMPERED="proof.tampered.json"

# Build once, then invoke quietly. No feature flags: the live MPC-TLS path is unconditional.
ORACLE=(cargo run --release --quiet --)

line() { printf '\n\033[1m── %s\033[0m\n' "$1"; }

line "1. PROVE — capture a real $ASSET spot quote as a portable proof"
"${ORACLE[@]}" prove price --asset "$ASSET" --out "$PROOF"
echo "wrote $PROOF ($(wc -c < "$PROOF" | tr -d ' ') bytes) — this is the whole proof."
echo
echo "the portable proof (self-contained; no key, no live connection inside it):"
# Pretty-print if jq is around; otherwise show it raw (head-limited for STARK-carrying proofs).
if command -v jq >/dev/null 2>&1; then
    jq '{ server: .presentation.server_name?, keys: (keys) }' "$PROOF" 2>/dev/null || head -c 800 "$PROOF"
else
    head -c 800 "$PROOF"; echo " …"
fi

line "2. SEND — a proof is just a file. Hand it to anyone; nothing secret travels."
cp "$PROOF" "$FRIEND_COPY"
echo "delivered $PROOF -> $FRIEND_COPY (imagine email / paste / git commit)."

line "3. VERIFY — the friend re-checks it locally, trusting no one"
if "${ORACLE[@]}" verify "$FRIEND_COPY"; then
    echo "=> PASS: the friend confirmed the fact without trusting the prover or the API."
else
    echo "=> unexpected FAIL on the genuine proof" >&2
    exit 1
fi

line "4. TAMPER — flip one byte and watch it refuse (fail-closed)"
cp "$PROOF" "$TAMPERED"
python3 - "$TAMPERED" <<'PY'
import sys
p = sys.argv[1]
b = bytearray(open(p, "rb").read())
i = len(b) // 2                 # flip a byte in the middle of the proof
b[i] ^= 0xFF
open(p, "wb").write(b)
print(f"flipped byte {i} of {len(b)}")
PY
if "${ORACLE[@]}" verify "$TAMPERED"; then
    echo "=> ERROR: a tampered proof verified — that must never happen" >&2
    exit 1
else
    echo "=> FAIL as expected: any change to the proof breaks verification."
fi

line "done"
echo "proof.json is portable and independently verifiable. that is the whole point."
