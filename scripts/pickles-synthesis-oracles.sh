#!/usr/bin/env bash
# pickles-synthesis-oracles.sh — run the Pickles-in-Lean SYNTHESIS byte-diff oracles as ONE command,
# green-or-bust. Each oracle is the o1js / real-chain SIDE of a `metatheory/Dregg2/{Circuit/Emit,
# Bridge}/*.lean` EMIT module (rooted in the `PicklesSynthesis` lean_lib target). The Lean side runs
# in `lake build PicklesSynthesis`; THIS script runs the differential half — the byte-exactness of the
# emitted gates/placement/statement-packing against o1js 2.15.0 and a live kimchi-verified devnet block
# — so the diffs are re-checkable on demand, not one-shot elaboration-time `#guard`s.
#
# ⚑ OWNERSHIP. The oracle scripts live under `bridge/mina-zkapp/scripts/` (a sibling's partition) and
# are READ-ONLY here — this wrapper only INVOKES them; it does not edit them or the bridge package.json.
# Wiring them into the bridge's own npm gate tier (and out of `npm-scripts-allow.tsv`) is that partition's
# call; this script gives them a CI-runnable home without touching it.
#
# EXIT: 0 iff every green-or-bust oracle exits 0; non-zero (and the first RED named) otherwise.
# Each oracle `process.exit(1)`s on any byte divergence, so a bent gate coeff / mis-placed wire /
# permuted statement field turns this command RED.
#
# USAGE:  scripts/pickles-synthesis-oracles.sh            # run all
#         scripts/pickles-synthesis-oracles.sh --no-ts    # skip the .ts oracles (no tsc build)
set -uo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
ZK="$ROOT/bridge/mina-zkapp"
cd "$ZK" || { echo "pickles-oracles: cannot cd $ZK"; exit 2; }

RUN_TS=1
[ "${1:-}" = "--no-ts" ] && RUN_TS=0

# The green-or-bust diffs. `custom-gate-oracle.mjs` is a DUMP (always exit 0), not a gate — omitted.
MJS_ORACLES=(
  "custom-gate-diff.mjs"          # R2: emitted custom-gate typ+coeffs (poseidon 165 coeffs) vs o1js
  "pickles-placement-oracle.mjs"  # R1: {row,col} copy-permutation wires vs live o1js
)
TS_ORACLES=(
  "pickles-r3-branchdata-oracle.ts"    # R3: branch_data prefix-mask pack vs devnet block 539508
  "pickles-statement-oracle.ts"        # R3: WHOLE Wrap statement packing vs the same block
  "pickles-step-statement-oracle.ts"   # R3: Step per-proof layout + fq=Type2/Fq field-key
)

fails=0
run_one() { # name, cmd...
  local name="$1"; shift
  echo "── $name ─────────────────────────────────────────────"
  if "$@"; then
    echo "   GREEN: $name"
  else
    echo "   RED:   $name (exit $?)"
    fails=$((fails + 1))
  fi
  echo
}

echo "== Pickles-synthesis byte-diff oracles (green-or-bust) =="
echo

for o in "${MJS_ORACLES[@]}"; do
  run_one "$o" node "scripts/$o"
done

# The .ts oracles are TRANSPILE-ONLY scripts (their headers say `Run: npx tsx <file>`): they carry
# intentional literal-vs-literal falsification controls (e.g. `67 === 66`, the branch_data naive-tag
# mistake) that full `tsc` rejects as TS2367 but that are exactly the RED path at runtime. So they run
# under `ts-node --transpile-only --esm` (no type-check), NOT `npm run build`.
TSNODE="$ZK/node_modules/.bin/ts-node"
if [ "$RUN_TS" = 1 ]; then
  if [ ! -x "$TSNODE" ]; then
    echo "   RED: ts-node not found at $TSNODE (run 'cd bridge/mina-zkapp && npm ci'); .ts oracles skipped."
    fails=$((fails + 1))
  else
    for o in "${TS_ORACLES[@]}"; do
      run_one "$o" "$TSNODE" --transpile-only --esm "scripts/$o"
    done
  fi
else
  echo "(--no-ts: skipping pickles-r3-branchdata / -statement / -step-statement oracles)"
  echo
fi

if [ "$fails" -eq 0 ]; then
  echo "== ALL GREEN — every Pickles-synthesis byte-diff oracle byte-exact =="
  exit 0
else
  echo "== $fails ORACLE(S) RED =="
  exit 1
fi
