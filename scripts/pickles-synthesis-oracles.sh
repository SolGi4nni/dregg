#!/usr/bin/env bash
# pickles-synthesis-oracles.sh — run the Pickles-in-Lean SYNTHESIS byte-diff oracles as ONE command,
# green-or-bust. Each oracle is the o1js / real-chain SIDE of a `metatheory/Dregg2/{Circuit/Emit,
# Bridge}/*.lean` EMIT module (rooted in the `PicklesSynthesis` lean_lib target). The Lean side runs
# in `lake build PicklesSynthesis`; THIS script runs the differential half — the byte-exactness of the
# emitted gates/placement/statement-packing against o1js 2.15.0 and a live kimchi-verified devnet block
# — so the diffs are re-checkable on demand, not one-shot elaboration-time `#guard`s.
#
# ⚑ SHARED HARNESS. Three of the diffs now route their byte-walk through `bridge/mina-zkapp/scripts/
# diff-oracle.mjs` — the one differential-oracle harness (a REFERENCE producer + a CANDIDATE producer +
# an ordered {name,value} vector diff + exit-red-on-divergence + a RED-PATH self-test). Step 0 runs the
# harness engine's standalone `--self-test` (proves the diff reports RED on corruption for all three
# shapes), and the MIGRATED oracles are invoked with `--self-test` so each one MEASURES its own red path
# (green diff + corruption-bites) in this same run. A diff that cannot go red is documented-not-detected.
#
# EXIT: 0 iff every green-or-bust step exits 0; non-zero (and the first RED named) otherwise.
# Each oracle `process.exit(1)`s on any byte divergence, so a bent gate coeff / mis-placed wire /
# permuted statement field turns this command RED.
#
# ⚑ AND ONE THAT IS NOT A BYTE-DIFF AGAINST A BLOCK. Every oracle above compares a Lean emission to
# ONE reference value — one o1js render, one devnet block. `pickles-crossimpl-differential.sh` is the
# CROSS-IMPLEMENTATION half: it drives dregg's Lean value layer AND o1-labs' `proof-systems` 0.3.0
# over a deterministic sweep of 2576 inputs across 15 function pairs and requires the two vectors to
# be byte-identical. That is evidence about THE FUNCTION rather than about a value at one input, and
# it carries its own three-polarity red-path self-test.
#
# USAGE:  scripts/pickles-synthesis-oracles.sh            # run all (harness self-test + every oracle)
#         scripts/pickles-synthesis-oracles.sh --no-ts    # skip the .ts oracles (no ts-node)
#         scripts/pickles-synthesis-oracles.sh --no-xi    # skip the cross-implementation differential
#
# ⚠ The cross-impl differential runs the Lean emitter under the interpreter (minutes) and, unless
# `PICKLES_XI_RUST_VECTORS` points at a vector file produced elsewhere, a cold kimchi+arkworks cargo
# build. On a build box that is the right thing; `--no-xi` exists for the fast pass.
set -uo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
ZK="$ROOT/bridge/mina-zkapp"
cd "$ZK" || { echo "pickles-oracles: cannot cd $ZK"; exit 2; }

RUN_TS=1
RUN_XI=1
for a in "$@"; do
  case "$a" in
    --no-ts) RUN_TS=0 ;;
    --no-xi) RUN_XI=0 ;;
  esac
done

# The green-or-bust diffs. `custom-gate-oracle.mjs` is a DUMP (always exit 0), not a gate — omitted.
MJS_ORACLES=(
  "custom-gate-diff.mjs"               # R2: emitted custom-gate typ+coeffs (poseidon 165 coeffs) vs o1js
  "pickles-placement-oracle.mjs"       # R1: {row,col} copy-permutation wires vs live o1js
  "mina-canonical-circuit-oracle.mjs"  # R4: MINA'S OWN wrap+step gate lists as the byte TARGET
  "stepmain-region-conformance.mjs"    # R5: our `verify_one` vs Mina's step circuit GATE BY GATE
)
TS_ORACLES=(
  "pickles-r3-branchdata-oracle.ts"    # R3: branch_data prefix-mask pack vs devnet block 539508
  "pickles-statement-oracle.ts"        # R3: WHOLE Wrap statement packing vs the same block
  "pickles-step-statement-oracle.ts"   # R3: Step per-proof layout + fq=Type2/Fq field-key
)

# Oracles migrated to the shared diff-oracle.mjs harness — invoked with `--self-test` so each MEASURES
# its own red path (corrupted candidate → exit 1) alongside the live green diff.
MIGRATED="custom-gate-diff.mjs pickles-placement-oracle.mjs mina-canonical-circuit-oracle.mjs stepmain-region-conformance.mjs pickles-r3-branchdata-oracle.ts"

# `stepmain-region-conformance.mjs` additionally carries SIX falsifiers of its own (`--falsify`, passed
# in the loop below): five bend the Lean gate list by the smallest possible amount — one Poseidon round
# constant, one wire inside a Poseidon body, one retyped VarBaseMul, one Generic selector coefficient,
# one wire inside an EndoMul-32 body — and DEMAND the conformance vector move; the sixth drops the
# σ-probe rows so the ledger's OTHER leg bites too (a divergence that stops being observed is a stale
# allowance and must be red). A gate-by-gate diff a bent coefficient does not move would be decoration.
is_migrated() { case " $MIGRATED " in *" $1 "*) return 0;; *) return 1;; esac; }

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

# Step 0: the shared harness engine's OWN red-path proof — corruption must make the diff report RED for
# every shape (gates|statement|field). If this is GREEN the migrated oracles' `--self-test`s are trustworthy.
run_one "diff-oracle.mjs --self-test (harness engine red-path)" node "scripts/diff-oracle.mjs" --self-test

for o in "${MJS_ORACLES[@]}"; do
  extra=""
  [ "$o" = "stepmain-region-conformance.mjs" ] && extra="--falsify"
  if is_migrated "$o"; then
    run_one "$o" node "scripts/$o" --self-test ${extra:+$extra}
  else
    run_one "$o" node "scripts/$o"
  fi
done

# The .ts oracles are TRANSPILE-ONLY scripts: the non-migrated ones still carry intentional literal-vs-
# literal falsification controls (e.g. `t2q === LEAN_T2Q_SAMPLE`) that full `tsc` rejects as TS2367 but
# that are exactly the RED path at runtime, so they run under `ts-node --transpile-only --esm` (no type-
# check), NOT `npm run build`. The MIGRATED .ts oracle (branchdata) no longer needs the literal control —
# its red path is the harness `--self-test` — but it still runs under ts-node (it imports the .mjs harness).
TSNODE="$ZK/node_modules/.bin/ts-node"
if [ "$RUN_TS" = 1 ]; then
  if [ ! -x "$TSNODE" ]; then
    echo "   RED: ts-node not found at $TSNODE (run 'cd bridge/mina-zkapp && npm ci'); .ts oracles skipped."
    fails=$((fails + 1))
  else
    for o in "${TS_ORACLES[@]}"; do
      if is_migrated "$o"; then
        run_one "$o" "$TSNODE" --transpile-only --esm "scripts/$o" --self-test
      else
        run_one "$o" "$TSNODE" --transpile-only --esm "scripts/$o"
      fi
    done
  fi
else
  echo "(--no-ts: skipping pickles-r3-branchdata / -statement / -step-statement oracles)"
  echo
fi

# The CROSS-IMPLEMENTATION differential — the only step here that is not a diff against a single
# reference value. Green or bust, with its own red path.
if [ "$RUN_XI" = 1 ]; then
  run_one "pickles-crossimpl-differential.sh --self-test (Lean ↔ proof-systems 0.3.0, 15 pairs)" \
    bash "$ROOT/scripts/pickles-crossimpl-differential.sh" --self-test
else
  echo "(--no-xi: skipping the cross-implementation differential)"
  echo
fi

if [ "$fails" -eq 0 ]; then
  echo "== ALL GREEN — every Pickles-synthesis byte-diff oracle byte-exact, and the Lean↔Rust cross-implementation differential agrees =="
  exit 0
else
  echo "== $fails ORACLE(S) RED =="
  exit 1
fi
