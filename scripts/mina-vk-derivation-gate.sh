#!/usr/bin/env bash
# MINA VK DERIVATION GATE — a verification key DERIVED from a Lean-assembled circuit, and Mina's own
# reader accepting it.
#
# WHAT IT MEASURES, in order, all green-or-bust:
#   1. `pickles-vk-derive` unit gates (11):
#        t1  three keys o1js ITSELF emitted decode + re-encode BYTE-IDENTICALLY
#        t2  our Poseidon reproduces o1js's `vk.hash` on all three (mina-rust has no such pin)
#        t3  a key DERIVED from Lean-emitted `KimchiWrapMain` gates is well-formed on the wire
#        t4  one coefficient of one Lean gate, +1 -> exactly `coeff[0]` moves and 27 hold
#        t5  two different Lean circuits -> two different keys
#        t6  the strict reader refuses off-curve / truncated / bad-nil / non-canonical / bad-tag
#        t7  determinism   t8  the o1js prefix constant   t9  no undeclarable wrap domain is emitted
#        t10 one WIRE re-pointed -> sigma[col] moves and no selector does
#        t11 one gate RETYPED    -> the selector moves and no sigma does
#   2. the derivation itself: `KimchiWrapMain` w3_branch + w4_bind + a one-coefficient perturbation,
#      each padded to Mina's 2^14 wrap domain and written as base64 binprot.
#   3. THE GATE — o1js's OCaml binprot reader (`Pickles.sideLoaded.vkToCircuit`) parsing each derived
#      key, `VerificationKey.checkValidity` returning true, the three hashes DISTINCT, and four
#      mutations REFUSED (anchored on the unmutated key parsing, so no refusal is vacuous).
#
# ⚠ SCOPE. This is about the KEY. It is not a proof, it does not verify a proof, and it does not
# claim the Lean wrap assembly is complete — `KimchiWrapMain` §13 names by sub-circuit what is not
# yet emitted. Nothing here deploys, registers or submits anything.
#
# USAGE
#   scripts/mina-vk-derivation-gate.sh              # the gate
#   scripts/mina-vk-derivation-gate.sh --self-test  # + PROVE the gate can go red
#   scripts/mina-vk-derivation-gate.sh --no-unit    # skip step 1 (it is also in the harness ratchet)
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
CRATE="$ROOT/metatheory/fixtures/pickles-vk-derive"
ZK="$ROOT/bridge/mina-zkapp"
GATE="$ZK/scripts/mina-vk-parse-gate.mjs"

SELFTEST=0; RUN_UNIT=1
for a in "$@"; do
  case "$a" in
    --self-test) SELFTEST=1 ;;
    --no-unit)   RUN_UNIT=0 ;;
    -h|--help)   sed -n '2,28p' "$0"; exit 0 ;;
    *) echo "unknown argument $a" >&2; exit 2 ;;
  esac
done

fails=0
step() { echo; echo "── $* ──────────────────────────────────────────"; }
note() { echo "   $*"; }
red()  { echo "   RED:   $*"; fails=$((fails+1)); }

# ⚠ NO FALLBACK. A missing tool is RED, never a skip: a gate that quietly stops running is the exact
# shape this tree keeps getting bitten by.
command -v cargo >/dev/null || { red "cargo not found"; echo "== VK DERIVATION GATE RED =="; exit 1; }
command -v node  >/dev/null || { red "node not found";  echo "== VK DERIVATION GATE RED =="; exit 1; }
[ -f "$GATE" ] || { red "$GATE missing"; echo "== VK DERIVATION GATE RED =="; exit 1; }
[ -d "$ZK/node_modules/o1js" ] || { red "o1js not installed (cd bridge/mina-zkapp && npm ci)"; echo "== VK DERIVATION GATE RED =="; exit 1; }

OUT="$(mktemp -d "${TMPDIR:-/tmp}/mina-vk-derive.XXXXXX")"
trap 'rm -rf "$OUT"' EXIT

if [ "$RUN_UNIT" = 1 ]; then
  step "1. pickles-vk-derive unit gates (encoding round-trip, hash cross-pin, movement)"
  if cargo test --release --manifest-path "$CRATE/Cargo.toml" 2>&1 | tee "$OUT/unit.log" | tail -14; then
    # A `cargo test` that ran ZERO tests exits 0. Demand the count.
    n=$(grep -oE 'test result: ok\. [0-9]+ passed' "$OUT/unit.log" | grep -oE '[0-9]+' | head -1)
    if [ "${n:-0}" -lt 11 ]; then
      red "only ${n:-0} unit tests ran; the crate declares 11"
    else
      note "GREEN: $n unit gates"
    fi
  else
    red "pickles-vk-derive unit gates"
  fi
fi

step "2. derive — Lean-emitted KimchiWrapMain gates -> Mina Side_loaded_verification_key"
if cargo run --release --quiet --manifest-path "$CRATE/Cargo.toml" -- "$OUT" --log2-domain 14 2>&1 | tee "$OUT/derive.log" | grep -E 'Lean rows|hash |MOVED|held'; then
  note "GREEN: derivation ran"
else
  red "derivation"
fi
VKS=()
for f in "$OUT"/vk-wrapmain-*.json; do [ -f "$f" ] && VKS+=(--vk "$f"); done
if [ "${#VKS[@]}" -lt 6 ]; then   # 3 keys x 2 argv tokens
  red "expected 3 derived keys, found $(( ${#VKS[@]} / 2 ))"
fi

step "3. THE GATE — o1js's own reader must PARSE the derived keys"
if node --max-old-space-size=8192 "$GATE" "${VKS[@]}" --self-test; then
  note "GREEN: o1js parsed every derived key and refused every mutation"
else
  red "o1js parse gate"
fi

if [ "$SELFTEST" = 1 ]; then
  step "4. --self-test — PROVE the gate can go RED"
  # (a) a key with one byte of one commitment bent must be REFUSED by the parse gate.
  python3 - "$OUT" <<'PY'
import base64, json, sys, pathlib
d = pathlib.Path(sys.argv[1])
src = json.loads((d / 'vk-wrapmain-w4_bind.json').read_text())
raw = bytearray(base64.b64decode(src['data']))
raw[2] = (raw[2] + 1) & 0xFF          # sigma_comm[0].x + 1 -> off Pallas
src['data'] = base64.b64encode(bytes(raw)).decode()
(d / 'bent.json').write_text(json.dumps(src))
PY
  if node --max-old-space-size=8192 "$GATE" --vk "$OUT/bent.json" >"$OUT/bent.log" 2>&1; then
    red "self-test: a BENT key was ACCEPTED — the gate cannot go red and proves nothing"
    tail -5 "$OUT/bent.log"
  else
    note "GREEN: a bent key is REFUSED — $(grep -m1 'FAIL' "$OUT/bent.log" | cut -c1-140)"
  fi
  # (b) the unit gates must go red when an o1js reference key is corrupted. The corruption goes to a
  # COPY in $OUT and is pointed at by PICKLES_VK_REF_FIXTURE — the tracked fixture is never touched,
  # because this working tree is shared with other lanes.
  cp "$CRATE/fixtures/o1js-reference-vks.json" "$OUT/refs-bent.json"
  python3 - "$OUT/refs-bent.json" <<'PY'
import json, sys, base64
p = sys.argv[1]
j = json.load(open(p))
raw = bytearray(base64.b64decode(j['refA']['data']))
raw[100] ^= 0x01
j['refA']['data'] = base64.b64encode(bytes(raw)).decode()
json.dump(j, open(p, 'w'), indent=2)
PY
  if PICKLES_VK_REF_FIXTURE="$OUT/refs-bent.json" \
     cargo test --release --quiet --manifest-path "$CRATE/Cargo.toml" >"$OUT/unit-red.log" 2>&1; then
    red "self-test: the unit gates stayed GREEN with a corrupted o1js reference key"
  else
    note "GREEN: corrupting an o1js reference key turns the unit gates RED"
  fi
fi

echo
if [ "$fails" -eq 0 ]; then
  echo "== VK DERIVATION GATE GREEN — a VK derived from Lean-emitted gates, PARSED by o1js =="
  exit 0
else
  echo "== VK DERIVATION GATE RED: $fails step(s) =="
  exit 1
fi
