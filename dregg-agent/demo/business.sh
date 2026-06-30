#!/usr/bin/env bash
# ─────────────────────────────────────────────────────────────────────────────
# Acme Test-as-a-Service, run by an agent — the one-command hackathon demo.
#
#   bash demo/business.sh
#
# Runs the five beats (EARN · FUND · OPERATE · SPEND · SCALE), emits a run.json
# P&L, then PROVES it: re-witnesses the whole run offline (host untrusted), and
# shows a tampered line caught. Deterministic + offline by default (recorded
# brain + recorded signed webhook) so it ALWAYS films cleanly — no key, no
# network needed.
#
#   --live   drive OPERATE/SPEND with a real Nemotron/Hermes model if a key is
#            present (NVIDIA_API_KEY or NOUS_PORTAL_KEY); falls back to offline.
# ─────────────────────────────────────────────────────────────────────────────
set -euo pipefail

# Resolve repo root from this script's location (demo/ lives under dregg-agent/).
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$HERE/../.." && pwd)"
RUN_JSON="${RUN_JSON:-$HERE/run.json}"

LIVE_FLAG=""
FEATURES=""
if [[ "${1:-}" == "--live" ]]; then
  LIVE_FLAG="--live"
  FEATURES="--features live-brain"
fi

banner() {
  echo
  echo "════════════════════════════════════════════════════════════════════"
  echo "  $1"
  echo "════════════════════════════════════════════════════════════════════"
}

# Pre-build so the filmed run shows only the demo output, not cargo noise.
banner "BUILDING (one-time; the filmed run is instant)"
cargo build -q -p dregg-agent --bin dregg-agent-business $FEATURES --manifest-path "$REPO_ROOT/Cargo.toml"
BIN="$REPO_ROOT/target/debug/dregg-agent-business"

# Beats 1–5 + write run.json.
"$BIN" run --out "$RUN_JSON" $LIVE_FLAG

# Beat 6 (PROVE): re-witness the whole P&L offline, trusting no host.
"$BIN" verify "$RUN_JSON"

# Beat 7 (THE TEETH): flip one line → the proof rejects it. The binary prints
# its own "7 · THE TEETH" header so the verify beat and the tamper beat read as
# two distinct beats on camera.
"$BIN" verify --tamper "$RUN_JSON"

echo
echo "Done. The P&L receipt is at: $RUN_JSON"
echo "Anyone can re-verify it offline:  $BIN verify $RUN_JSON"
