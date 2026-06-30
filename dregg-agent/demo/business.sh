#!/usr/bin/env bash
# ─────────────────────────────────────────────────────────────────────────────
# dregg-agent — a REAL, flexible, live operator agent you can audit.
#
#   bash demo/business.sh "<natural-language goal>" [--budget N] [--caps a,b,…] [...]
#   bash demo/business.sh                      # uses a real default goal
#
# Hands a LIVE model (NVIDIA Nemotron) an arbitrary goal + a budget + a cap
# bundle, then runs a REAL reason→act→observe loop: the model decides the next
# tool call, every call is cap-gated + metered + receipted and runs FOR REAL (a
# real shell / fs / http / git, or a budget-gated spend). Then it PROVES the run:
# re-witnesses run.json offline (host untrusted) and shows a tampered line caught.
#
# This is NOT a script. Hand it a different goal and the agent genuinely adapts —
# that is the proof. Needs a model key in ~/.nvidiakey (or $NVIDIA_API_KEY).
#
# Flags after the goal pass straight through, e.g.:
#   bash demo/business.sh "clone https://github.com/octocat/Hello-World and \
#       run any tests, then report" --caps shell,fs,git:github.com --budget 800
#   bash demo/business.sh --replay demo/resp.json     # replay a captured run
# ─────────────────────────────────────────────────────────────────────────────
set -euo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$HERE/../.." && pwd)"
RUN_JSON="${RUN_JSON:-$HERE/run.json}"

# A leading non-flag argument is the goal; the rest pass through.
RUN_ARGS=()
if [[ $# -gt 0 && "${1:0:2}" != "--" ]]; then
  RUN_ARGS+=(--goal "$1"); shift
fi
RUN_ARGS+=("$@")

banner() { echo; echo "════════════════════════════════════════════════════════════════════"; echo "  $1"; echo "════════════════════════════════════════════════════════════════════"; }

# Build once (the live path needs the `live-brain` feature for the model + http).
banner "BUILDING dregg-agent (one-time)"
cargo build -q -p dregg-agent --bin dregg-agent --features live-brain --manifest-path "$REPO_ROOT/Cargo.toml"
BIN="$REPO_ROOT/target/debug/dregg-agent"

# Run the LIVE agent on the goal (default goal if none given): real tools,
# cap-gated + metered + receipted, narrated as it happens; writes run.json.
"$BIN" run --out "$RUN_JSON" "${RUN_ARGS[@]}"

# PROVE: re-witness the whole run offline, trusting no host.
"$BIN" verify "$RUN_JSON"

# THE TEETH: flip one receipted line → the proof rejects it (BadSignature).
"$BIN" verify --tamper "$RUN_JSON"

echo
echo "Done. The receipt is at: $RUN_JSON"
echo "Re-verify it yourself, offline:  $BIN verify $RUN_JSON"
echo "Hand the agent a DIFFERENT goal to see it adapt:"
echo "  bash demo/business.sh \"list the 3 newest files in your workdir and summarize them\""
