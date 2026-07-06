#!/usr/bin/env bash
# ─────────────────────────────────────────────────────────────────────────────
# grain-local.sh — drive a LOCALLY-HOSTED agent grain end-to-end, no host trust.
#
#   bash dregg-agent/demo/grain-local.sh
#
# This is NOT a scripted movie. It runs the REAL operations `docs/WALKTHROUGH.md`
# documents against a genuinely-usable local instance:
#
#   1. RENT + DRIVE a confined agent grain on the built-in local node, minting
#      every admitted action as a genuine committed kernel turn (R2), landed on
#      the node's finalized, light-client-verifiable receipt log.
#   2. VERIFY it yourself — R0 (tamper-evidence) + R2 (receipts are views over
#      committed turns) + LANDED (turns on a real node's chain) — trusting no host.
#   3. EARN via the audited DECO/zkTLS money-in: mint conserved USD-credit against
#      a Stripe-payment attestation, and re-verify the commitment by hand.
#
# Everything runs on localhost from a clean checkout. Recorded brain is the honest
# default (a live NVIDIA Nemotron drives the grain over HTTP with a key + the
# `live-brain` feature — see WALKTHROUGH.md §Live). The DECO leg is a test-mode
# fixture attestation (compiler-enforced honest label — see WALKTHROUGH.md §Earn).
# ─────────────────────────────────────────────────────────────────────────────
set -euo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$HERE/../.." && pwd)"
cd "$REPO_ROOT"

banner() { echo; echo "════════════════════════════════════════════════════════════════════"; echo "  $1"; echo "════════════════════════════════════════════════════════════════════"; }

banner "STEP 1+2 — rent, drive, and self-verify a local-hosted grain"
echo "  node → rent → drive (recorded brain) → R2 turns land → verify (no host trust)"
echo
# DREGG_NODE_URL, if set, names an external federation node (the deploy step); the
# in-process node still mints + verifies here.
cargo run -q -p agent-platform --example grain_local_e2e

banner "STEP 3 — EARN via the audited DECO/zkTLS money-in (fixture)"
echo "  verify a Stripe-payment attestation → conserved mint → re-verify by hand"
echo "  (test-mode fixture: --features test-utils is compiler-enforced honesty)"
echo
cargo run -q -p dregg-bridge --example deco_money_in --features test-utils

banner "DONE"
cat <<EOF
  What you just ran, all real, all local:
    • a confined agent grain drove 3 kernel turns onto a real local node ledger
    • those turns are on the node's finalized, light-client-verifiable receipt log
    • you re-verified R0 + R2 + landed trusting no host
    • you minted conserved USD-credit from a DECO attestation and recomputed its
      commitment by hand; a forged-facts attestation was refused

  Next (docs/WALKTHROUGH.md):
    • the REAL node daemon + faucet + CLI:   scripts/run-node-10min.sh
    • drive the grain with a LIVE model over HTTP:   §Live (needs a key)
    • the physically-jailed brain (macOS):   cargo test -p deos-hermes --test dregg_hosts_the_agent
    • point at a homelab federation node:   DREGG_NODE_URL=http://<homelab>:8421 (deploy step)
EOF
