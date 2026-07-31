#!/usr/bin/env bash
# fri-mutation-gate.sh — THE PERMANENT MUTATION-DIFFERENTIAL CONTROL.
#
# A proof-systems review ranked in-circuit verifier fidelity the #1 live risk: no systematic
# differential that the o1js FRI verifier accepts iff dregg's native verifier accepts. This gate
# IS that differential, run as a seeded, reproducible control:
#
#   the Rust oracle (`circuit-prove/src/bin/root_fri_mutation`) mutates dregg's REAL committed root
#   proof one field element at a time, runs the DEPLOYED FRI/PCS verifier (`TwoAdicFriPcs::verify`,
#   the object `RootFriWalk.ts` mirrors), and streams a faithful structural decode per trial;
#   the twin (`dist/scripts/fri-mutation-differential.js`) walks each with the SAME
#   `segmentWalk`/`walkTwin` the armed slice circuit (`runSegments`) executes, and asserts verdict
#   agreement — three-valued, per structural region.
#
# GOES RED on: a forgery-shaped disagreement (twin accepts what native rejects), agreement below
# the floor, or a free lane (both-accept) in a region not known to be unconstrained.
#
# ⚑ RECORDED CONSTANTS — reproducible. Changing these is a deliberate act, not a drift:
#     SEED=20260731  TRIALS=3000  FLOOR=1.0  EXPECTED_FREE=commit_pow_witness
#   Observed 2026-07-31 (seed 20260731, 3000 trials): agreement 100.000%, 0 forgeries,
#   0 completeness gaps; free lanes ONLY in commit_pow_witness (commitPowBits=0 ⇒ the 16 commit-PoW
#   witnesses are unabsorbed by `check_witness` and therefore unconstrained — both verifiers accept).
#
# USAGE:
#   FRIMUT_BIN=/abs/path/root_fri_mutation scripts/fri-mutation-gate.sh          # use a prebuilt bin
#   scripts/fri-mutation-gate.sh                                                  # build from repo root
#   FRIMUT_TRIALS=500 scripts/fri-mutation-gate.sh                                # quicker smoke
set -uo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
MZ="$(cd "$HERE/.." && pwd)"                      # bridge/mina-zkapp
REPO="$(cd "$MZ/../.." && pwd)"                   # repo root

SEED="${FRIMUT_SEED:-20260731}"
TRIALS="${FRIMUT_TRIALS:-3000}"
FLOOR="${FRIMUT_FLOOR:-1.0}"
export FRIMUT_EXPECTED_FREE="${FRIMUT_EXPECTED_FREE:-commit_pow_witness}"

# --- resolve the Rust oracle binary ----------------------------------------
BIN="${FRIMUT_BIN:-}"
if [[ -z "$BIN" ]]; then
  echo "building the Rust oracle (root_fri_mutation) from $REPO ..." >&2
  ( cd "$REPO" && cargo build -p dregg-circuit-prove --release --bin root_fri_mutation ) || {
    echo "✗ could not build root_fri_mutation (is the workspace green?). Set FRIMUT_BIN to a prebuilt binary." >&2
    exit 5
  }
  BIN="$REPO/target/release/root_fri_mutation"
fi
[[ -x "$BIN" ]] || { echo "✗ oracle binary not found/executable: $BIN" >&2; exit 5; }

# --- build the twin side ----------------------------------------------------
( cd "$MZ" && npm run build >/dev/null 2>&1 ) || { echo "✗ tsc build failed" >&2; exit 5; }

echo "=== FRI mutation differential — seed $SEED, $TRIALS trials, floor $FLOOR ===" >&2
cd "$MZ"
"$BIN" "$SEED" "$TRIALS" | node --max-old-space-size=16384 dist/scripts/fri-mutation-differential.js "$FLOOR"
rc=$?
exit $rc
