#!/usr/bin/env python3
"""mina-block-fetch — write a Mina block fixture in the shape the Pickles extractors read.

⚑ WHY THIS EXISTS. Every real-data conformance claim in this tree used to be pinned to ONE
devnet block (539508), fetched by hand on 2026-07-28 and pasted into
`metatheory/fixtures/pickles-extractors/mina_devnet_block.json`. A constant accidentally fitted
to that block's particulars could never show. This script is the reproducible half of the fix:
it writes fixtures with the SAME schema, so `pickles-reality-gate-export <mode> <path>` runs the
identical code over any of them.

    bridge/tools/mina-block-fetch.py --network devnet --best 8 --out metatheory/fixtures/mina-blocks
    bridge/tools/mina-block-fetch.py --network devnet --genesis --out …
    bridge/tools/mina-block-fetch.py --network mainnet --best 2 --out …

⚠ AVAILABILITY, not authority. This reads a public GraphQL node with no key and no transaction.
The node is trusted for BYTES ONLY: a hostile node's block fails openmina's own
`kimchi::verifier::verify` in `pickles-reality-gate-export devnet`, which is the ground truth.

⚠ A public node serves only its TRANSITION FRONTIER (~290 blocks). Historical heights are NOT
retrievable — `block(height: N)` answers "Could not find block in transition frontier". That is
why the fixtures in this tree are the heights they are, and why re-fetching an old one is
impossible rather than merely inconvenient.
"""
import argparse
import json
import os
import sys
import urllib.request

ENDPOINT = "https://api.minascan.io/node/{network}/v1/graphql"

# The chain-id / genesis pair each network's fixtures must carry, so a fixture cannot silently
# be from the wrong chain. `pickles-reality-gate-export devnet` re-asserts the devnet pair.
NETWORKS = {
    "devnet": "29936104443aaf264a7f0192ac64b1c7173198c1ed404c1bcff5e562e05eb7f6",
    "mainnet": "5f704cc0c82e0ed70e873f0893d7e06f148524e3f0bdae2afb02e7819a0c24d1",
}

BLOCK_FIELDS = """
  stateHash
  protocolState {
    previousStateHash
    blockchainState { snarkedLedgerHash }
    consensusState { blockHeight epoch slotSinceGenesis }
  }
  protocolStateProof { base64 }
  transactions { userCommands { hash } zkappCommands { hash } feeTransfer { fee } coinbase }
  snarkJobs { workIds }
"""


def gql(network, query, timeout):
    req = urllib.request.Request(
        ENDPOINT.format(network=network),
        data=json.dumps({"query": query}).encode(),
        # ⚑ The endpoint 403s a bare urllib request; it wants a User-Agent. Named here rather
        # than left as a mystery failure for the next person.
        headers={"Content-Type": "application/json", "User-Agent": "dregg-mina-block-fetch/1"},
    )
    with urllib.request.urlopen(req, timeout=timeout) as r:
        d = json.loads(r.read())
    if "errors" in d and d["errors"]:
        raise SystemExit(f"mina-block-fetch: GraphQL error: {json.dumps(d['errors'])[:400]}")
    return d["data"]


def fixture_of(network, genesis_hash, b, source):
    cs = b["protocolState"]["consensusState"]
    tx = b.get("transactions") or {}
    return {
        "_source": f"{ENDPOINT.format(network=network)} (Mina {network.upper()} public node), GraphQL {source}",
        "_fetched_by": "bridge/tools/mina-block-fetch.py",
        "chain_id": NETWORKS[network],
        "genesis_state_hash": genesis_hash,
        "state_hash": b["stateHash"],
        "previous_state_hash": b["protocolState"]["previousStateHash"],
        "blockchain_length": cs["blockHeight"],
        "epoch": int(cs["epoch"]),
        "slot_since_genesis": int(cs["slotSinceGenesis"]),
        "snarked_ledger_hash": b["protocolState"]["blockchainState"]["snarkedLedgerHash"],
        # ⚑ The CONTENT axes. Devnet blockchain-SNARK proofs are all the same SHAPE
        # (proofs_verified = N2, domain_log2 = 16, 15 IPA rounds), so these are what actually
        # distinguishes one fixture from another: how much the wrapped Step proof had to do.
        "n_user_commands": len(tx.get("userCommands") or []),
        "n_zkapp_commands": len(tx.get("zkappCommands") or []),
        "n_fee_transfers": len(tx.get("feeTransfer") or []),
        "n_snark_jobs": len(b.get("snarkJobs") or []),
        "protocol_state_proof_base64_urlsafe": b["protocolStateProof"]["base64"],
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--network", choices=sorted(NETWORKS), default="devnet")
    ap.add_argument("--best", type=int, default=0, help="fetch the N most recent canonical blocks")
    ap.add_argument("--genesis", action="store_true", help="fetch the (hardfork) genesis block")
    ap.add_argument("--out", required=True, help="directory to write <network>-<height>.json into")
    ap.add_argument("--timeout", type=int, default=240)
    args = ap.parse_args()

    gen = gql(args.network, "{ genesisBlock { stateHash } }", args.timeout)
    genesis_hash = gen["genesisBlock"]["stateHash"]
    os.makedirs(args.out, exist_ok=True)
    written = []

    if args.genesis:
        d = gql(args.network, "{ genesisBlock {" + BLOCK_FIELDS + "} }", args.timeout)
        written.append(fixture_of(args.network, genesis_hash, d["genesisBlock"], "genesisBlock"))
    if args.best:
        d = gql(
            args.network,
            "{ bestChain(maxLength: %d) {" % args.best + BLOCK_FIELDS + "} }",
            args.timeout,
        )
        for b in d["bestChain"]:
            written.append(
                fixture_of(args.network, genesis_hash, b, f"bestChain(maxLength:{args.best})")
            )

    for fx in written:
        p = os.path.join(args.out, f"{args.network}-{fx['blockchain_length']}.json")
        with open(p, "w") as f:
            json.dump(fx, f, indent=1)
            f.write("\n")
        print(
            f"{p}  height={fx['blockchain_length']} proof_b64={len(fx['protocol_state_proof_base64_urlsafe'])} "
            f"ucmd={fx['n_user_commands']} zk={fx['n_zkapp_commands']} snark={fx['n_snark_jobs']}"
        )
    if not written:
        print("mina-block-fetch: nothing requested (--best N and/or --genesis)", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
