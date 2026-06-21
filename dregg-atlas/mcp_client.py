"""A tiny JSON-RPC stdio client for the dregg-mcp server (the dregg-image MCP).

Spawns `starbridge-v2/target/release/dregg-mcp` and drives it over stdin/stdout
line-delimited JSON-RPC 2.0. Every tool call returns the parsed JSON the tool
emitted (the server wraps it in an MCP text content block; we unwrap it).

This is the substrate the atlas crawler stands on — it speaks to the SAME
verified embedded executor the cockpit renders.
"""
import json
import os
import subprocess
import sys

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
MCP_BIN = os.path.join(REPO, "starbridge-v2", "target", "release", "dregg-mcp")


class Mcp:
    def __init__(self, bin_path=MCP_BIN):
        if not os.path.exists(bin_path):
            raise FileNotFoundError(
                f"{bin_path} not found — build it: "
                f"cd starbridge-v2 && cargo build --release --features native-full --bin dregg-mcp"
            )
        self.p = subprocess.Popen(
            [bin_path],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.DEVNULL,
            text=True,
            bufsize=1,
            env={**os.environ, "ZED_OFFSCREEN_PREFER_CPU": "1"},
        )
        self._id = 0
        self._rpc("initialize", {})

    def _rpc(self, method, params):
        self._id += 1
        req = {"jsonrpc": "2.0", "id": self._id, "method": method, "params": params}
        self.p.stdin.write(json.dumps(req) + "\n")
        self.p.stdin.flush()
        line = self.p.stdout.readline()
        if not line:
            raise RuntimeError(f"dregg-mcp closed the pipe (method={method})")
        resp = json.loads(line)
        if "error" in resp:
            raise RuntimeError(f"rpc error {method}: {resp['error']}")
        return resp["result"]

    def call(self, tool, **args):
        """Call an MCP tool; return the parsed JSON the tool produced."""
        result = self._rpc("tools/call", {"name": tool, "arguments": args})
        content = result.get("content", [{}])
        text = content[0].get("text", "{}")
        if result.get("isError"):
            raise RuntimeError(f"tool {tool} error: {text}")
        try:
            return json.loads(text)
        except json.JSONDecodeError:
            return {"_raw": text}

    def tools(self):
        return [t["name"] for t in self._rpc("tools/list", {})["tools"]]

    def close(self):
        try:
            self.p.stdin.close()
            self.p.wait(timeout=5)
        except Exception:
            self.p.kill()


if __name__ == "__main__":
    m = Mcp()
    print("tools:", m.tools(), file=sys.stderr)
    print(json.dumps(m.call("survey"), indent=2))
    m.close()
