"""THE DREGG ATLAS crawler — walk the reachable state-space of the live verified
image and dump it as data the site-builder renders.

Produces (under dregg-atlas/data/):
  protocol.json   — the AuthRequired lattice, effects, refusal taxonomy
  cells.json      — every cell at genesis, with its 7 faces + affordances + halo
  gametree.json   — the reachable state-space: nodes = world-states (keyed by
                    post-state digest), edges = turns (committed vs refused, with
                    reasons). The game tree.

State identity = the post-state hash a committed turn returns (the Merkle root of
the ledger after the turn). The empty path is "genesis". Because the per-cell
nonce ratchets monotonically (touch = IncrementNonce), the state-space is
infinite; we bound by depth + node/edge caps and LOG every bound so a truncation
is never mistaken for completeness.
"""
import json
import os
import sys

from mcp_client import Mcp

DATA = os.path.join(os.path.dirname(os.path.abspath(__file__)), "data")
os.makedirs(DATA, exist_ok=True)

MAX_DEPTH = int(os.environ.get("ATLAS_DEPTH", "4"))
MAX_NODES = int(os.environ.get("ATLAS_NODES", "600"))
MAX_EDGES = int(os.environ.get("ATLAS_EDGES", "4000"))


def survey_snapshot(m):
    s = m.call("survey")
    return {
        "cell_count": s["cell_count"],
        "cells": [
            {"short": c["short"], "kind": c["kind"], "balance": c.get("balance"),
             "cap_edges": c["cap_edges"], "title": c["title"]}
            for c in s["cells"]
        ],
    }


def all_moves(m):
    """Every affordance on every cell, as candidate moves (authorized or not)."""
    moves = []
    for c in m.call("survey")["cells"]:
        aff = m.call("affordances", cell=c["id"])
        for msg in aff["messages"]:
            moves.append({
                "cell_id": c["id"], "cell": c["short"],
                "message": msg["name"], "effect": msg["effect"],
                "required": msg["required"], "authorized": msg["authorized"],
            })
    return moves


def reconstruct(m, path):
    """Set the world to the state after `path` (a list of (cell_id, message))."""
    m.call("rewind", to=0)
    digest = "genesis"
    for (cell_id, msg) in path:
        res = m.call("act", cell=cell_id, message=msg)
        if res["outcome"] == "committed":
            digest = res["receipt"]["post_state"]
    return digest


def crawl_gametree(m):
    """DFS over the reachable state-space using cheap snapshot/restore for
    backtracking (instant, vs the 3s reboot a rewind costs). State identity is
    the post-state Merkle root a committed turn returns."""
    nodes = {}   # digest -> {depth, snapshot}
    edges = []   # {from, to, cell, message, effect, required, authorized, outcome, ...}
    seen = set()
    bounds = {"depth_capped": 0, "node_cap_hit": False, "edge_cap_hit": False}

    def dfs(depth, parent_dig):
        if bounds["edge_cap_hit"] or bounds["node_cap_hit"]:
            return
        snap = m.call("snapshot")["id"]
        try:
            moves = all_moves(m)
            for mv in moves:
                if len(edges) >= MAX_EDGES:
                    bounds["edge_cap_hit"] = True
                    break
                m.call("restore", id=snap)  # back to this node's state (instant)
                res = m.call("act", cell=mv["cell_id"], message=mv["message"])
                edge = {
                    "from": parent_dig, "cell": mv["cell"], "message": mv["message"],
                    "effect": mv["effect"], "required": mv["required"],
                    "authorized": mv["authorized"], "outcome": res["outcome"],
                }
                if res["outcome"] == "committed":
                    child = res["receipt"]["post_state"]
                    edge["to"] = child
                    edge["computrons"] = res["receipt"]["computrons"]
                    if child not in seen:
                        seen.add(child)
                        if len(nodes) >= MAX_NODES:
                            bounds["node_cap_hit"] = True
                        else:
                            nodes[child] = {"depth": depth + 1, "snapshot": survey_snapshot(m), "digest": child}
                            edges.append(edge)
                            if depth + 1 < MAX_DEPTH:
                                dfs(depth + 1, child)  # we are AT `child` now
                            else:
                                bounds["depth_capped"] += 1
                            continue
                    else:
                        edge["to_existing"] = True
                else:
                    edge["to"] = parent_dig  # refused → self-loop with a reason
                    edge["by_executor"] = res.get("by_executor")
                    edge["reason"] = res.get("reason", "")
                edges.append(edge)
        finally:
            m.call("forget", id=snap)

    m.call("rewind", to=0)  # clean genesis
    gdig = "genesis"
    nodes[gdig] = {"depth": 0, "snapshot": survey_snapshot(m), "digest": gdig}
    seen.add(gdig)
    dfs(0, gdig)

    return {
        "meta": {
            "max_depth": MAX_DEPTH, "max_nodes": MAX_NODES, "max_edges": MAX_EDGES,
            "node_count": len(nodes), "edge_count": len(edges),
            "committed_edges": sum(1 for e in edges if e["outcome"] == "committed"),
            "refused_edges": sum(1 for e in edges if e["outcome"] == "refused"),
            "bounds_hit": bounds,
            "note": "state digest = post-state Merkle root; refused edges are self-loops with a reason",
        },
        "nodes": list(nodes.values()),
        "edges": edges,
    }


def crawl_cells(m):
    m.call("rewind", to=0)
    exp = m.call("export", out=os.path.join(DATA, "_export_raw.json"))
    # the export tool wrote the full dump; re-read it for the cell faces
    with open(os.path.join(DATA, "_export_raw.json")) as f:
        return json.load(f)


def main():
    m = Mcp()
    try:
        print("crawling protocol…", file=sys.stderr)
        proto = m.call("protocol")
        json.dump(proto, open(os.path.join(DATA, "protocol.json"), "w"), indent=2)

        print("crawling cells (faces/affordances/halo via export)…", file=sys.stderr)
        cells = crawl_cells(m)
        json.dump(cells, open(os.path.join(DATA, "cells.json"), "w"), indent=2)

        print(f"crawling game tree (depth={MAX_DEPTH})…", file=sys.stderr)
        gt = crawl_gametree(m)
        json.dump(gt, open(os.path.join(DATA, "gametree.json"), "w"), indent=2)
        print(f"  game tree: {gt['meta']['node_count']} states, {gt['meta']['edge_count']} transitions "
              f"({gt['meta']['committed_edges']} committed, {gt['meta']['refused_edges']} refused)", file=sys.stderr)
        print(f"  bounds hit: {gt['meta']['bounds_hit']}", file=sys.stderr)
    finally:
        m.close()


if __name__ == "__main__":
    main()
