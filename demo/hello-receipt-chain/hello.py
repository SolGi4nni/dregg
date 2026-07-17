#!/usr/bin/env python3
"""hello-receipt-chain — the smallest single-agent dregg demo.

One agent, one turn, one receipt chain. It drives the SAME MCP surface a real
AI process would (`dregg-node mcp` over newline-delimited JSON-RPC on stdio):

  1. dregg_create_agent      → register this node's cell (content-addressed id)
  2. dregg_submit_turn       → submit ONE turn (a set_field effect on our cell)
  3. dregg_get_receipt_chain → read back the auditable receipt chain

The last thing printed on stdout is the receipt chain as JSON — the smallest
agent-to-agent receipt shape dregg emits (receipt_hash, turn_hash, pre/post
state hashes, computrons_used, action_count).

Run it with ./run.sh, or directly:
    python3 hello.py --node-bin ../../target/debug/dregg-node --data-dir ./state
"""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
from pathlib import Path


class McpClient:
    """A persistent `dregg-node mcp` subprocess we talk JSON-RPC to.

    Trimmed sibling of demo/two-ai-handoff/mcp_stdio.py — just enough to call
    three tools. One JSON object per line, in and out.
    """

    def __init__(self, node_bin: str, data_dir: str):
        env = os.environ.copy()
        env.setdefault("RUST_LOG", "warn")
        self.proc = subprocess.Popen(
            [node_bin, "mcp", "--data-dir", data_dir],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=sys.stderr,
            env=env,
            bufsize=0,
        )
        self._next_id = 1
        # MCP handshake.
        self._call("initialize", {
            "protocolVersion": "2024-11-05",
            "capabilities": {},
            "clientInfo": {"name": "hello-receipt-chain", "version": "0.1"},
        })
        self._send({"jsonrpc": "2.0", "method": "notifications/initialized"})

    def _send(self, obj: dict) -> None:
        assert self.proc.stdin is not None
        self.proc.stdin.write((json.dumps(obj) + "\n").encode())
        self.proc.stdin.flush()

    def _call(self, method: str, params: dict) -> dict:
        rid = self._next_id
        self._next_id += 1
        self._send({"jsonrpc": "2.0", "id": rid, "method": method, "params": params})
        assert self.proc.stdout is not None
        line = self.proc.stdout.readline()
        if not line:
            raise RuntimeError("node closed stdout before responding")
        resp = json.loads(line.decode())
        if resp.get("error"):
            raise RuntimeError(f"RPC error: {resp['error']}")
        return resp.get("result", {})

    def tool(self, name: str, args: dict) -> dict:
        """Invoke an MCP tool; return its text-content payload parsed as JSON."""
        result = self._call("tools/call", {"name": name, "arguments": args})
        contents = result.get("content", [])
        if result.get("isError"):
            raise RuntimeError(f"tool {name} error: "
                               + " | ".join(c.get("text", "") for c in contents))
        text = contents[0].get("text", "") if contents else "{}"
        try:
            return json.loads(text)
        except json.JSONDecodeError:
            return {"text": text}

    def close(self) -> None:
        try:
            assert self.proc.stdin is not None
            self.proc.stdin.close()
            self.proc.wait(timeout=5)
        except Exception:
            self.proc.kill()


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--node-bin", required=True, help="path to dregg-node")
    parser.add_argument("--data-dir", required=True, help="fresh node data-dir")
    args = parser.parse_args()

    cli = McpClient(args.node_bin, args.data_dir)
    try:
        # ── 1. Become a cell ─────────────────────────────────────────────
        agent = cli.tool("dregg_create_agent",
                         {"name": "hello", "initial_balance": 1_000_000})
        cell = agent["cell_id"]
        print(f"[hello] agent cell = {cell[:16]}…  balance={agent['balance']}",
              file=sys.stderr)

        # ── 2. Submit ONE turn targeting our own cell ────────────────────
        # A single set_field effect (write value 42 to slot 0), per the
        # documented dregg_submit_turn schema. The receipt chains onto the
        # agent's prior state regardless of the effect's ledger write.
        # `fee` funds the turn's computron budget (a bare action costs ~100).
        turn = cli.tool("dregg_submit_turn", {
            "target_cell": cell,
            "method": "set_field",
            "fee": 1000,
            "effects": [{"type": "set_field", "cell": cell, "index": 0, "value": 42}],
            "memo": "hello, receipt chain",
        })
        print(f"[hello] turn accepted={turn.get('accepted')} "
              f"turn_hash={turn.get('turn_hash', '')[:16]}…", file=sys.stderr)

        # ── 3. Read the auditable receipt chain ──────────────────────────
        chain = cli.tool("dregg_get_receipt_chain", {"limit": 10})
        print(f"[hello] chain_length={chain['chain_length']}", file=sys.stderr)

        # The receipt chain — the smallest agent-to-agent receipt shape — on stdout.
        print(json.dumps(chain, indent=2))
        return 0
    finally:
        cli.close()


if __name__ == "__main__":
    sys.exit(main())
