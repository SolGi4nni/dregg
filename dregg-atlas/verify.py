"""THE DREGG ATLAS oracle — turn the game-tree crawl into a standing property
checker. The crawl already visits the reachable state-space; this asserts
protocol invariants hold across ALL of it, and exits non-zero on any violation
(CI-friendly, green-or-bust).

The headline property: CONSERVATION across the whole reachable space. The crawl's
move set moves value (transfers) but never mints or burns, so the sum of cell
balances must be INVARIANT — equal in every reachable state to the genesis sum.
A single state that disagreed would be a conservation hole. Proving it holds over
hundreds of states is a real standing assurance, not a one-shot test.

Run after crawl.py:  python3 verify.py   (reads data/gametree.json)
"""
import json
import os
import sys

DATA = os.path.join(os.path.dirname(os.path.abspath(__file__)), "data")


def cell_sum(snapshot):
    return sum((c.get("balance") or 0) for c in snapshot.get("cells", []))


def main():
    gt = json.load(open(os.path.join(DATA, "gametree.json")))
    nodes = gt["nodes"]
    edges = gt["edges"]
    by_digest = {n["digest"]: n for n in nodes}
    failures = []

    # --- invariant 1: CONSERVATION across the whole reachable space ----------
    genesis = next((n for n in nodes if n["digest"] == "genesis"), nodes[0])
    base_sum = cell_sum(genesis["snapshot"])
    bad_sum = [n for n in nodes if cell_sum(n["snapshot"]) != base_sum]
    if bad_sum:
        for n in bad_sum[:5]:
            failures.append(
                f"CONSERVATION VIOLATED at state {n['digest']} (depth {n['depth']}): "
                f"Σ balances = {cell_sum(n['snapshot'])} ≠ genesis {base_sum}"
            )
    else:
        print(f"✓ conservation: Σ balances = {base_sum} in ALL {len(nodes)} reachable states")

    # --- invariant 2: the issuer well stays the sole negative balance --------
    # (an issuer well carries −supply; no other cell should ever go negative —
    #  that would be an unbacked overspend the executor must refuse.)
    neg_violations = []
    for n in nodes:
        negs = [c for c in n["snapshot"]["cells"] if (c.get("balance") or 0) < 0]
        if len(negs) > 1:
            neg_violations.append((n["digest"], [c["short"] for c in negs]))
    if neg_violations:
        for dig, cells in neg_violations[:5]:
            failures.append(f"MULTIPLE NEGATIVE BALANCES at {dig}: {cells} (unbacked overspend?)")
    else:
        print(f"✓ no unbacked overspend: ≤1 negative-balance cell (the issuer well) in every state")

    # --- invariant 3: edge well-formedness (committed vs refused) ------------
    # A committed edge to an unknown digest is a FRONTIER edge to a state the
    # bounded crawl did not expand (node/edge-capped) — honest truncation, not a
    # violation. We count those separately and only flag them if the crawl was
    # NOT capped (a genuine dangling edge).
    capped = bool(gt["meta"].get("bounds_hit", {}).get("node_cap_hit") or
                  gt["meta"].get("bounds_hit", {}).get("edge_cap_hit"))
    edge_bad = 0
    frontier = 0
    for e in edges:
        if e["outcome"] == "committed":
            if "to" not in e:
                edge_bad += 1
                if edge_bad <= 5:
                    failures.append(f"committed edge {e['cell']}·{e['message']} has no target state")
            elif e["to"] not in by_digest and e["to"] != e["from"]:
                frontier += 1
                if not capped:  # only a real fault if the crawl wasn't truncated
                    edge_bad += 1
                    if edge_bad <= 5:
                        failures.append(f"committed edge {e['cell']}·{e['message']} → dangling state {e['to']} (crawl not capped)")
        elif e["outcome"] == "refused":
            # a refusal must be classified (cap-gate vs executor) and carry a reason
            if e.get("by_executor") is None or not e.get("reason"):
                edge_bad += 1
                if edge_bad <= 5:
                    failures.append(f"refused edge {e['cell']}·{e['message']} missing classification/reason")
            # a refusal changes nothing — it is a self-loop
            elif e.get("to") not in (e["from"], None):
                edge_bad += 1
                if edge_bad <= 5:
                    failures.append(f"refused edge {e['cell']}·{e['message']} changed state ({e['from']}→{e.get('to')})")
    if edge_bad == 0:
        committed = sum(1 for e in edges if e["outcome"] == "committed")
        refused = sum(1 for e in edges if e["outcome"] == "refused")
        note = f" ({frontier} frontier edges to cap-truncated states)" if frontier else ""
        print(f"✓ {len(edges)} edges well-formed ({committed} committed · {refused} refused, classified self-loops){note}")

    # --- verdict -------------------------------------------------------------
    if failures:
        print(f"\n✗ ORACLE FAILED — {len(failures)} violation(s):", file=sys.stderr)
        for f in failures:
            print("  " + f, file=sys.stderr)
        sys.exit(1)
    print(f"\n✓ ORACLE GREEN — {len(nodes)} states, {len(edges)} transitions, all invariants hold")


if __name__ == "__main__":
    main()
