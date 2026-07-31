#!/usr/bin/env bash
# mina-verifies-dregg.sh — ONE COMMAND: Mina verifies dregg.
#
#   bridge/demo/mina-verifies-dregg.sh              # rehearse; touches no chain
#   bridge/demo/mina-verifies-dregg.sh --broadcast  # + deploy and advance on Mina devnet
#
# The direction: a Mina zkApp holds a head for dregg's state and moves it
# BECAUSE A PROOF VERIFIED — `DreggHeadGate.advanceHead` consumes the terminal
# proof of dregg's root-proof verification chain, pins the key it was made under,
# and requires the chain's closing seal to be exhibited at the pinned length.
#
# ── THE REGISTER THIS SCRIPT PRINTS IN ─────────────────────────────────────
# Every step ends in one of FOUR words, and the fourth is the honest one:
#
#   PASS             it ran and the thing it checks held.
#   FAIL             it ran and did not hold. The run stops.
#   BLOCKED          an INPUT is absent. The path is intact; something upstream
#                    has not produced its artifact yet. Named, never defaulted.
#   NOT ATTRIBUTABLE it ran, it was green, and the green does not mean what the
#                    step's name says. This exists because a green over a false
#                    premise is worse than a red.
#
# ── WHAT --broadcast DOES ──────────────────────────────────────────────────
# Deploys a zkApp and submits a transaction to Mina devnet. Outward-facing and
# irreversible, therefore never the default, and the two scripts it calls refuse
# again on their own account. Throwaway devnet keys, no real value.
#
# ⚑ IT DOES NOT MINT KEYS. If the proof-gated gate has no address the run stops
# and prints the one command that creates one. Key material is the operator's.

set -euo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
ZK="$ROOT/bridge/mina-zkapp"

BROADCAST=0
SKIP_CIRCUIT=0
for a in "$@"; do
  case "$a" in
    --broadcast) BROADCAST=1 ;;
    --no-circuit) SKIP_CIRCUIT=1 ;;
    -h|--help)
      sed -n '2,32p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'
      exit 0
      ;;
    *) echo "unknown flag: $a (see --help)" >&2; exit 2 ;;
  esac
done

LOGDIR="${DEMO_LOGDIR:-$(mktemp -d "${TMPDIR:-/tmp}/mina-verifies-dregg.XXXXXX")}"
mkdir -p "$LOGDIR"

STEPS=()
say()  { printf '\n\033[1m── %s\033[0m\n' "$*"; }
pass() { STEPS+=("PASS|$1"); printf '   \033[32mPASS\033[0m  %s\n' "$1"; }
fail() { STEPS+=("FAIL|$1"); printf '   \033[31mFAIL\033[0m  %s\n' "$1"; }
blok() { STEPS+=("BLOCKED|$1"); printf '   \033[33mBLOCKED\033[0m  %s\n' "$1"; }
nattr(){ STEPS+=("NOT ATTRIBUTABLE|$1"); printf '   \033[35mNOT ATTRIBUTABLE\033[0m  %s\n' "$1"; }
die()  { fail "$1"; summary; exit 1; }

summary() {
  printf '\n\033[1m════ MINA VERIFIES DREGG — SUMMARY ════\033[0m\n'
  for s in "${STEPS[@]}"; do printf '  %-18s %s\n' "${s%%|*}" "${s#*|}"; done
  printf '\n  transcripts: %s\n\n' "$LOGDIR"
}

# ===========================================================================
say "0 · PREFLIGHT"

command -v node >/dev/null || die "node is not on PATH"
NODE_MAJOR="$(node -p 'process.versions.node.split(".")[0]')"
[ "$NODE_MAJOR" -ge 20 ] || die "node $(node --version) is below the required 20"
pass "node $(node --version)  $(node -p 'process.platform+"-"+process.arch')"

if [ ! -d "$ZK/node_modules" ]; then
  echo "   node_modules absent — running npm ci (this is the fresh-clone path)"
  (cd "$ZK" && npm ci --no-audit --no-fund) > "$LOGDIR/npm-ci.log" 2>&1 \
    || die "npm ci failed — see $LOGDIR/npm-ci.log"
fi

# The native backend is a per-MACHINE fact (npm installs one platform binary),
# so it is asked rather than assumed. Absence is not a failure — it is slower.
NATIVE_PKG="$ZK/node_modules/@o1js/native-$(node -p 'process.platform+"-"+process.arch')"
if [ -d "$NATIVE_PKG" ]; then
  export O1JS_BACKEND="${O1JS_BACKEND:-native}"
  pass "o1js native backend available; O1JS_BACKEND=$O1JS_BACKEND  (measured on hbox: compile 4.1x, prove 1.9x, VK bit-identical)"
else
  pass "o1js native backend NOT installed for this platform — using the default (slower, same VK)"
fi

MINA_ENDPOINT="${MINA_ENDPOINT:-https://api.minascan.io/node/devnet/v1/graphql}"
case "$MINA_ENDPOINT" in
  *devnet*) : ;;
  *) die "MINA_ENDPOINT '$MINA_ENDPOINT' is not a devnet endpoint; these scripts are devnet-only" ;;
esac
DSTAT="$(curl -sS --max-time 30 -X POST "$MINA_ENDPOINT" \
  -H 'Content-Type: application/json' \
  -d '{"query":"{ daemonStatus { syncStatus blockchainLength } }"}' 2>/dev/null || true)"
if printf '%s' "$DSTAT" | grep -q '"syncStatus":"SYNCED"'; then
  HEIGHT="$(printf '%s' "$DSTAT" | sed -n 's/.*"blockchainLength":\([0-9]*\).*/\1/p')"
  pass "Mina devnet SYNCED at height $HEIGHT  ($MINA_ENDPOINT)"
else
  blok "Mina devnet did not answer SYNCED — the on-chain steps cannot run. Raw: ${DSTAT:0:200}"
fi

# ===========================================================================
say "1 · THE GATE'S DECISION, OUT OF CIRCUIT  (MINA_TIER=0, seconds)"
# The head decision, the seal, the bootstrap and the pin refusals as ARITHMETIC.
# On this directory's own record the cheap exhaustive differential is the better
# instrument — it is what found every defect the affordable proof runs missed.
if (cd "$ZK" && MINA_TIER=0 npm run head-anchor) > "$LOGDIR/tier0.log" 2>&1; then
  N="$(grep -c '✓' "$LOGDIR/tier0.log" || true)"
  pass "head-anchor tier-0: $N out-of-circuit checks (the decision table, the seal, the bootstrap)"
else
  fail "head-anchor tier-0 — see $LOGDIR/tier0.log"
  tail -20 "$LOGDIR/tier0.log"
  summary; exit 1
fi

# ===========================================================================
say "2 · THE DEPLOY PATH, AGAINST A REAL prove()  (LocalBlockchain, minutes)"
# Deploy the gate at a weak-subjectivity anchor, ACCEPT a correctly-shaped
# terminal proof, and refuse four things that are not one. Nothing here depends
# on dregg's rotating verification keys — the producer is a named stand-in.
if [ "$SKIP_CIRCUIT" = 1 ]; then
  blok "skipped by --no-circuit (this is the step that compiles Pickles circuits)"
elif (cd "$ZK" && npm run head-gate-rehearsal) > "$LOGDIR/rehearsal.log" 2>&1; then
  REF="$(grep -c 'REFUSED' "$LOGDIR/rehearsal.log" || true)"
  pass "deployed, ACCEPTED an honest advance (head moved to H), and REFUSED $REF things that are not one"
  grep -E '^\s+(✓|REFUSED)' "$LOGDIR/rehearsal.log" | sed 's/^/     /'
else
  fail "head-gate-rehearsal — see $LOGDIR/rehearsal.log"
  tail -30 "$LOGDIR/rehearsal.log"
  summary; exit 1
fi

# ===========================================================================
say "3 · THE PINS — is there a dregg chain to point at?"
PINS="$ZK/dregg-chain-pins.json"
if [ -f "$PINS" ]; then
  pass "dregg-chain-pins.json present: $(node -p "JSON.parse(require('fs').readFileSync('$PINS','utf8')).label" 2>/dev/null || echo '(unreadable)')"
  HAVE_PINS=1
else
  blok "dregg-chain-pins.json absent — the 131-program compile has not run, so there is no key list to pin and no terminal proof to consume. Emit with: (cd bridge/mina-zkapp && npm run head-anchor-pins -- --emit)"
  HAVE_PINS=0
fi

# ===========================================================================
say "4 · ON CHAIN — deploy the proof-gated anchor and advance its head"
if [ "$BROADCAST" = 0 ]; then
  blok "--broadcast not given. Deploying is outward-facing and irreversible, so it is never the default."
  echo "     when the chain is ready:  bridge/demo/mina-verifies-dregg.sh --broadcast"
elif [ "$HAVE_PINS" = 0 ]; then
  blok "refusing to broadcast without pins — a gate built on a placeholder accepts a proof of nothing"
else
  set +e
  (cd "$ZK" && npm run devnet:head-deploy -- --broadcast) 2>&1 | tee "$LOGDIR/head-deploy.log"
  DEP=${PIPESTATUS[0]}
  set -e
  case "$DEP" in
    0) pass "DreggHeadGate deployed — $(grep -o 'https://minascan.io/devnet/tx/[A-Za-z0-9]*' "$LOGDIR/head-deploy.log" | head -1)" ;;
    3) blok "head-deploy reported its blockers (exit 3) — the path is intact, an input is absent"; summary; exit 0 ;;
    *) die "head-deploy failed (exit $DEP) — see $LOGDIR/head-deploy.log" ;;
  esac

  set +e
  (cd "$ZK" && npm run devnet:head-advance -- --broadcast) 2>&1 | tee "$LOGDIR/head-advance.log"
  ADV=${PIPESTATUS[0]}
  set -e
  case "$ADV" in
    0) pass "advanceHead INCLUDED — the head moved because a proof verified. This is PLACEHOLDER_CUTOVER's P4 trigger." ;;
    3) blok "head-advance reported its blockers (exit 3) — the terminal proof / seal preimage is not in hand" ;;
    *) die "head-advance failed (exit $ADV) — see $LOGDIR/head-advance.log" ;;
  esac
fi

# ===========================================================================
summary
cat <<'EOF'
  ⚑ WHAT AN ACCEPTED ADVANCE ESTABLISHES, in one sentence:
      dregg's state went from G to H in N turns with ordered-history commitment
      D, G was the head this client already held, and a batch-STARK over the
      root's seven AIRs verified for exactly that claim under the key list this
      gate's verification key names.

  ⚑ AND WHAT IT DOES NOT:
      * not that the committed function is low degree — the FRI/STARK soundness
        floor is undischarged here as everywhere in this tree;
      * not that H is the head dregg FINALIZED — a segment proof establishes
        that N turns are EXECUTABLE from G to H; which executable future is
        canonical is dregg's consensus's answer, and no committee signature or
        blocklace certificate rides in this proof. `reportFork` exists because
        of exactly this.
EOF
