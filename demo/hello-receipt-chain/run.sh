#!/usr/bin/env bash
# hello-receipt-chain — one agent, one turn, one receipt chain.
# Builds dregg-node if needed, runs against a fresh data-dir.
set -euo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$HERE/../.." && pwd)"
NODE_BIN="$REPO_ROOT/target/debug/dregg-node"
STATE_DIR="$HERE/state"

if [[ ! -x "$NODE_BIN" ]]; then
    echo "[hello] building dregg-node…"
    ( cd "$REPO_ROOT" && cargo build -p dregg-node )
fi

# Fresh data-dir each run so the node auto-generates its cipherclerk identity.
rm -rf "$STATE_DIR"
mkdir -p "$STATE_DIR"

python3 "$HERE/hello.py" --node-bin "$NODE_BIN" --data-dir "$STATE_DIR"
