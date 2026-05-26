"""Tiny MCP-over-stdio JSON-RPC client.

The dregg node exposes its MCP server as `dregg-node mcp`, reading JSON-RPC
requests from stdin and writing responses to stdout (one JSON object per line).
We don't need a real MCP SDK for that — just newline-delimited JSON.
"""

from __future__ import annotations

import json
import os
import subprocess
import threading
from pathlib import Path


class McpClient:
    """A persistent `dregg-node mcp` subprocess we talk JSON-RPC to."""

    def __init__(self, node_bin: str, data_dir: str, label: str, log_dir: Path):
        self.label = label
        self.log_dir = log_dir
        log_dir.mkdir(parents=True, exist_ok=True)
        self.stderr_log = open(log_dir / f"{label}.node.stderr.log", "wb")

        env = os.environ.copy()
        env.setdefault("RUST_LOG", "dregg_node=info,warn")

        self.proc = subprocess.Popen(
            [node_bin, "mcp", "--data-dir", data_dir],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=self.stderr_log,
            env=env,
            bufsize=0,
        )

        self._next_id = 1
        self._lock = threading.Lock()

        # MCP handshake.
        self._initialize()

    def _initialize(self) -> None:
        self.call(
            "initialize",
            {
                "protocolVersion": "2024-11-05",
                "capabilities": {},
                "clientInfo": {"name": f"two-ai-handoff/{self.label}", "version": "0.1"},
            },
        )
        # `notifications/initialized` is a notification (no id, no response).
        self._send({"jsonrpc": "2.0", "method": "notifications/initialized"})

    def _send(self, obj: dict) -> None:
        line = (json.dumps(obj) + "\n").encode()
        assert self.proc.stdin is not None
        self.proc.stdin.write(line)
        self.proc.stdin.flush()

    def _read(self) -> dict:
        assert self.proc.stdout is not None
        line = self.proc.stdout.readline()
        if not line:
            raise RuntimeError(
                f"[{self.label}] node closed stdout; see {self.log_dir}/{self.label}.node.stderr.log"
            )
        return json.loads(line.decode())

    def call(self, method: str, params: dict | None = None) -> dict:
        """Send a JSON-RPC request and return the response object."""
        with self._lock:
            rid = self._next_id
            self._next_id += 1
            self._send(
                {
                    "jsonrpc": "2.0",
                    "id": rid,
                    "method": method,
                    "params": params or {},
                }
            )
            resp = self._read()
            if resp.get("id") != rid:
                raise RuntimeError(
                    f"[{self.label}] id mismatch: sent {rid}, got {resp.get('id')}"
                )
            if "error" in resp and resp["error"] is not None:
                raise RuntimeError(f"[{self.label}] RPC error: {resp['error']}")
            return resp.get("result", {})

    def tool(self, name: str, args: dict | None = None) -> dict:
        """Invoke an MCP tool. Returns the parsed text-content payload as JSON
        if it looks like JSON; otherwise returns it as {'text': ...}."""
        result = self.call("tools/call", {"name": name, "arguments": args or {}})
        contents = result.get("content", [])
        if result.get("isError"):
            raise RuntimeError(
                f"[{self.label}] tool {name} returned isError: "
                + " | ".join(c.get("text", "") for c in contents)
            )
        if not contents:
            return {}
        text = contents[0].get("text", "")
        try:
            return json.loads(text)
        except json.JSONDecodeError:
            return {"text": text}

    def close(self) -> None:
        try:
            assert self.proc.stdin is not None
            self.proc.stdin.close()
        except Exception:
            pass
        try:
            self.proc.wait(timeout=5)
        except subprocess.TimeoutExpired:
            self.proc.kill()
        finally:
            try:
                self.stderr_log.close()
            except Exception:
                pass

    def __enter__(self) -> "McpClient":
        return self

    def __exit__(self, *exc) -> None:
        self.close()
