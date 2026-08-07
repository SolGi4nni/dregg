#!/usr/bin/env bash
# FOREIGN-VK REGISTRATION GATE — a verification key we DERIVED OURSELVES, placed on a Mina account
# by Mina's own transaction logic.
#
# WHAT IT MEASURES, in order, all green-or-bust:
#   1. DERIVE — `pickles-vk-derive` takes the Lean-emitted `KimchiWrapMain` gate list to three
#      `Side_loaded_verification_key`s. (Same step as `scripts/mina-vk-derivation-gate.sh`, which is
#      about whether Mina can READ them. This gate is about whether Mina will STORE one.)
#   2. THE GATE — `bridge/mina-zkapp/scripts/foreign-vk-register-gate.ts`:
#        A  the mechanism at source, with the two runtime-checkable claims actually checked
#           (verificationKey.data contributes 0 fields; the default permission is Signature)
#        B  PROVENANCE INDIFFERENCE — derived keys and o1js `.compile()` keys through one builder
#        C  the transaction constructed, serialised, and round-tripped through o1js's own codec
#        D  applied on LocalBlockchain — MINA'S OWN OCaml, js_of_ocaml-compiled — and the key read
#           back OFF THE ACCOUNT byte-for-byte
#        E  RED: one bent byte refused at five layers, each anchored on the key that was accepted
#        E' WHICH layer refuses — Mina alone accepts a parseable key with a LYING hash; the only
#           acceptor that catches that is o1js's LOCAL-ONLY one. This is why the builder checks.
#        F  the devnet submit command PRINTED, NOT RUN
#
# ⚠ NOTHING HERE DEPLOYS, REGISTERS OR SUBMITS. The only chain touched is an in-process
# LocalBlockchain. Step F prints a command and stops.
#
# USAGE
#   scripts/foreign-vk-registration-gate.sh              # the gate
#   scripts/foreign-vk-registration-gate.sh --self-test  # + PROVE the gate can go red
#   scripts/foreign-vk-registration-gate.sh --compile    # + a LIVE o1js .compile() for the
#                                                        #   .compile()-provenance leg (~30s)
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
CRATE="$ROOT/metatheory/fixtures/pickles-vk-derive"
ZK="$ROOT/bridge/mina-zkapp"
GATE="$ZK/scripts/foreign-vk-register-gate.ts"

SELFTEST=0; COMPILE=()
for a in "$@"; do
  case "$a" in
    --self-test) SELFTEST=1 ;;
    --compile)   COMPILE=(--compile) ;;
    -h|--help)   sed -n '2,27p' "$0"; exit 0 ;;
    *) echo "unknown argument $a" >&2; exit 2 ;;
  esac
done

fails=0
step() { echo; echo "── $* ──────────────────────────────────────────"; }
note() { echo "   $*"; }
red()  { echo "   RED:   $*"; fails=$((fails+1)); }

# ⚠ NO FALLBACK. A missing tool is RED, never a skip: a gate that quietly stops running is exactly
# the shape this tree keeps getting bitten by.
command -v cargo >/dev/null || { red "cargo not found";  echo "== FOREIGN-VK REGISTRATION GATE RED =="; exit 1; }
command -v node  >/dev/null || { red "node not found";   echo "== FOREIGN-VK REGISTRATION GATE RED =="; exit 1; }
command -v python3 >/dev/null || { red "python3 not found (needed by --self-test)"; echo "== FOREIGN-VK REGISTRATION GATE RED =="; exit 1; }
[ -f "$GATE" ] || { red "$GATE missing"; echo "== FOREIGN-VK REGISTRATION GATE RED =="; exit 1; }
[ -d "$ZK/node_modules/o1js" ] || { red "o1js not installed (cd bridge/mina-zkapp && npm ci)"; echo "== FOREIGN-VK REGISTRATION GATE RED =="; exit 1; }
[ -f "$CRATE/fixtures/o1js-reference-vks.json" ] || { red "$CRATE/fixtures/o1js-reference-vks.json missing — the .compile()-provenance leg cannot run"; echo "== FOREIGN-VK REGISTRATION GATE RED =="; exit 1; }

OUT="$(mktemp -d "${TMPDIR:-/tmp}/foreign-vk-register.XXXXXX")"
trap 'rm -rf "$OUT"' EXIT

# ⚠ `ts-node --transpile-only`, NOT `tsc`. `bridge/mina-zkapp` has two PRE-EXISTING type errors in
# files this gate does not own (scripts/pickles-step-statement-oracle.ts,
# scripts/shrink-claim-in-openings-probe.ts), so `npm run build` cannot complete and every
# `build && node dist/...` script in that package is already blocked by them. Running the source
# directly means this gate's red/green reports on THIS gate. The gate's own sources DO typecheck
# clean — step 3 pins that, so "transpile-only" never becomes a place to hide a type error.
TSNODE=(node --max-old-space-size=16384 --loader ts-node/esm --no-warnings)

step "1. DERIVE — Lean-emitted KimchiWrapMain gates -> Mina Side_loaded_verification_key"
if cargo run --release --quiet --manifest-path "$CRATE/Cargo.toml" -- "$OUT" --log2-domain 14 2>&1 | tee "$OUT/derive.log" | grep -E 'Lean rows|hash '; then
  note "GREEN: derivation ran"
else
  red "derivation"
fi
n=$(ls "$OUT"/vk-wrapmain-*.json 2>/dev/null | wc -l | tr -d ' ')
if [ "$n" -lt 3 ]; then red "expected 3 derived keys, found $n"; fi

step "2. THE GATE — build the account update, and make Mina's own logic accept it"
if (cd "$ZK" && DREGG_VK_DIR="$OUT" "${TSNODE[@]}" "$GATE" "${COMPILE[@]+"${COMPILE[@]}"}") 2>&1 | tee "$OUT/gate.log"; then
  note "GREEN: a DERIVED key was registered on an account by Mina's own transaction logic"
else
  red "foreign-vk register gate"
fi

step "3. TYPES — the gate's own sources typecheck clean"
# `--transpile-only` above skips type checking, so pin it here instead of losing it. The package has
# exactly two pre-existing errors in files this lane does not own; anything else is ours and is RED.
tsc_out="$OUT/tsc.log"
(cd "$ZK" && npx tsc --noEmit) >"$tsc_out" 2>&1
if grep -qE 'ForeignVerificationKey\.ts|foreign-vk-register-gate\.ts' "$tsc_out"; then
  red "type errors in this gate's own sources:"
  grep -E 'ForeignVerificationKey\.ts|foreign-vk-register-gate\.ts' "$tsc_out" | sed 's/^/          /'
else
  note "GREEN: no type errors in src/ForeignVerificationKey.ts or scripts/foreign-vk-register-gate.ts"
  note "       (package-wide count: $(grep -c 'error TS' "$tsc_out") — pre-existing, in files this gate does not own)"
fi

if [ "$SELFTEST" = 1 ]; then
  step "4. --self-test — PROVE the gate can go RED"
  # A gate fed ONLY a bent key must fail. If it still reports green, every green above is worthless.
  mkdir -p "$OUT/bent"
  python3 - "$OUT" <<'PY'
import base64, json, sys, pathlib
d = pathlib.Path(sys.argv[1])
src = json.loads((d / 'vk-wrapmain-w4_bind.json').read_text())
raw = bytearray(base64.b64decode(src['data']))
raw[2] = (raw[2] + 1) & 0xFF          # sigma_comm[0].x + 1 -> off Pallas
src['data'] = base64.b64encode(bytes(raw)).decode()
(d / 'bent' / 'vk-wrapmain-w4_bind.json').write_text(json.dumps(src))
PY
  if (cd "$ZK" && DREGG_VK_DIR="$OUT/bent" "${TSNODE[@]}" "$GATE") >"$OUT/selftest.log" 2>&1; then
    red "self-test: a gate given ONLY a BENT key reported GREEN — it cannot go red and proves nothing"
    tail -8 "$OUT/selftest.log"
  else
    note "GREEN: a bent key drives the gate RED — $(grep -m1 -E 'RED:|Refusal' "$OUT/selftest.log" | cut -c1-150)"
  fi
  # And a gate with NO input must refuse rather than silently pass.
  if (cd "$ZK" && DREGG_VK_DIR="$OUT/definitely-not-here" "${TSNODE[@]}" "$GATE") >"$OUT/noinput.log" 2>&1; then
    red "self-test: the gate reported GREEN with NO verification keys — a missing input is being skipped"
  else
    note "GREEN: no input is RED, not a skip"
  fi
fi

echo
if [ "$fails" = 0 ]; then
  echo "== FOREIGN-VK REGISTRATION GATE GREEN =="
  echo "   A verification key derived from Lean-assembled wrap gates was placed on a Mina account"
  echo "   by Mina's own OCaml transaction logic, and read back byte-for-byte. No compiled o1js"
  echo "   contract anywhere in the path. Nothing was submitted to any network."
else
  echo "== FOREIGN-VK REGISTRATION GATE RED ($fails) =="
fi
exit $((fails > 0))
