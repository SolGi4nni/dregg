#!/usr/bin/env python3
"""Extractor for the Samasika sliding-density-window differential.

Pulls REAL Mina devnet blocks and keeps, verbatim, the two consensus-state
fields the window mechanism produces:

    consensus_state.min_window_density        (a Length)
    consensus_state.sub_window_densities      (a Length list, sub_windows_per_window long)
    consensus_state.curr_global_slot_since_hard_fork.slot_number

Sources, both read-only and unauthenticated:

  * https://api.minascan.io/node/devnet/v1/graphql  -- `bestChain` gives the
    canonical parent/child order and the state hashes.  NOTE: the daemon
    GraphQL `ConsensusState` type does NOT expose `subWindowDensities`
    (introspected 2026-07-29; the 16 fields are blockchainLength, blockHeight,
    epochCount, minWindowDensity, lastVrfOutput, totalCurrency,
    stakingEpochData, nextEpochData, hasAncestorInSameCheckpointWindow, slot,
    slotSinceGenesis, epoch, superchargedCoinbase, blockStakeWinner,
    blockCreator, coinbaseReceiever), so GraphQL alone cannot seed a replay.
  * https://storage.googleapis.com/mina_network_block_data/devnet-<height>-<statehash>.json
    -- Mina's public precomputed-block archive, which carries the full
    protocol state including `sub_window_densities`.

`--heights` mode resolves a state hash straight from the GCS bucket listing,
so historical (sparse, outage-era) ranges can be pulled without a node.

Output is the pinned JSON consumed by
metatheory/Dregg2/Bridge/MinaSlidingWindow.lean.
"""
import argparse, json, sys, urllib.parse, urllib.request
from concurrent.futures import ThreadPoolExecutor

GQL = "https://api.minascan.io/node/devnet/v1/graphql"
BUCKET = "mina_network_block_data"
BLOB = "https://storage.googleapis.com/" + BUCKET + "/{net}-{h}-{sh}.json"
LIST = ("https://storage.googleapis.com/storage/v1/b/" + BUCKET +
        "/o?prefix={prefix}&fields=items(name)&maxResults=8")


UA = {"User-Agent": "dregg-samasika-density-extractor/1 (read-only)"}


def _get(url, timeout=120):
    with urllib.request.urlopen(urllib.request.Request(url, headers=UA), timeout=timeout) as r:
        raw = r.read()
    # A few archived blocks carry non-UTF8 bytes inside unrelated string fields
    # (memos / proof blobs).  latin-1 is byte-preserving and always succeeds; every
    # field this extractor reads is ASCII digits, so it is unaffected.
    try:
        return json.loads(raw.decode("utf-8"), strict=False)
    except UnicodeDecodeError:
        return json.loads(raw.decode("latin-1"), strict=False)


def graphql(query, timeout=900):
    req = urllib.request.Request(
        GQL, data=json.dumps({"query": query}).encode(),
        headers={"Content-Type": "application/json", **UA})
    with urllib.request.urlopen(req, timeout=timeout) as r:
        return json.load(r)


def best_chain(n):
    q = ("{ bestChain(maxLength:%d) { stateHash protocolState { previousStateHash "
         "consensusState { blockHeight slot epoch slotSinceGenesis minWindowDensity } } } }" % n)
    d = graphql(q)
    if d.get("errors"):
        raise SystemExit("graphql errors: %r" % d["errors"])
    return d["data"]["bestChain"]


def resolve_hash(net, height):
    """Find a height's state hash from the GCS bucket listing."""
    pfx = urllib.parse.quote("%s-%d-" % (net, height), safe="")
    items = _get(LIST.format(prefix=pfx)).get("items", [])
    if not items:
        return None
    # name is "<net>-<height>-<statehash>.json"
    return items[0]["name"].rsplit("-", 1)[1][: -len(".json")]


def precomputed(net, height, state_hash):
    d = _get(BLOB.format(net=net, h=height, sh=state_hash))
    cs = d["data"]["protocol_state"]["body"]["consensus_state"]
    if "curr_global_slot_since_hard_fork" not in cs:
        raise ValueError("pre-hard-fork block format at height %d" % height)
    return {
        "height": int(cs["blockchain_length"]),
        "state_hash": state_hash,
        "slot_number": int(cs["curr_global_slot_since_hard_fork"]["slot_number"]),
        "slots_per_epoch": int(cs["curr_global_slot_since_hard_fork"]["slots_per_epoch"]),
        "global_slot_since_genesis": int(cs["global_slot_since_genesis"]),
        "epoch_count": int(cs["epoch_count"]),
        "min_window_density": int(cs["min_window_density"]),
        "sub_window_densities": [int(x) for x in cs["sub_window_densities"]],
        "total_currency": int(cs["total_currency"]),
        "previous_state_hash": d["data"]["protocol_state"]["previous_state_hash"],
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--net", default="devnet")
    ap.add_argument("--tip", type=int, default=0,
                    help="pull N tip blocks via bestChain")
    ap.add_argument("--heights", default="",
                    help="explicit inclusive range LO-HI, resolved via the GCS listing")
    ap.add_argument("--walk-back", default="",
                    help="TOPHEIGHT:N -- start at TOPHEIGHT and follow previous_state_hash back "
                         "N blocks.  The GCS bucket holds ORPHANS too and a bare height listing "
                         "will happily hand you one, so this is the only way to pull a CANONICAL "
                         "historical run.")
    ap.add_argument("--jobs", type=int, default=8)
    ap.add_argument("-o", "--out", required=True)
    a = ap.parse_args()

    if a.tip:
        chain = best_chain(a.tip)
        want = [(int(b["protocolState"]["consensusState"]["blockHeight"]), b["stateHash"])
                for b in chain]
    elif a.walk_back:
        top, n = (int(x) for x in a.walk_back.split(":"))
        sh = resolve_hash(a.net, top)
        if not sh:
            raise SystemExit("no object at height %d" % top)
        rows, h = [], top
        while len(rows) < n and sh:
            r = precomputed(a.net, h, sh)
            rows.append(r)
            h, sh = h - 1, r["previous_state_hash"]
        rows.sort(key=lambda r: r["height"])
        want = None
    elif a.heights:
        lo, hi = (int(x) for x in a.heights.split("-"))
        with ThreadPoolExecutor(a.jobs) as ex:
            hs = list(ex.map(lambda h: (h, resolve_hash(a.net, h)), range(lo, hi + 1)))
        want = [(h, sh) for h, sh in hs if sh]
    else:
        raise SystemExit("need --tip or --heights")

    if want is not None:
        want.sort()
        with ThreadPoolExecutor(a.jobs) as ex:
            rows = list(ex.map(lambda t: precomputed(a.net, t[0], t[1]), want))
        rows.sort(key=lambda r: r["height"])

    # keep only the maximal parent-linked run, so a replay is over a real chain
    run = [rows[0]]
    for r in rows[1:]:
        if r["previous_state_hash"] == run[-1]["state_hash"]:
            run.append(r)
        else:
            run = [r]

    out = {
        "_source": ("Mina %s. Canonical order + state hashes from %s (bestChain); "
                    "consensus states verbatim from the public precomputed-block "
                    "archive gs://%s. Read-only, unauthenticated, no keys."
                    % (a.net, GQL, BUCKET)),
        "_extractor": "metatheory/fixtures/samasika-density/fetch_devnet_window.py",
        "net": a.net,
        "n": len(run),
        "height_lo": run[0]["height"],
        "height_hi": run[-1]["height"],
        "blocks": run,
    }
    with open(a.out, "w") as f:
        json.dump(out, f, indent=1)
    print("wrote %s: %d parent-linked blocks, heights %d..%d, slots %d..%d"
          % (a.out, len(run), run[0]["height"], run[-1]["height"],
             run[0]["slot_number"], run[-1]["slot_number"]), file=sys.stderr)


if __name__ == "__main__":
    main()
