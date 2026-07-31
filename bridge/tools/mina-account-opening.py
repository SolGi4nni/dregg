#!/usr/bin/env python3
"""
`mina-account-opening` — fetch a REAL Mina devnet account together with its
ledger Merkle opening, and the ledger hash that opening must reach.

This is the byte source behind `Dregg2.Bridge.MinaAccountOpening` and the
`dregg_mina_account_state_ok` FFI gate. It is an I/O CLIENT and it decides
NOTHING: it does not hash an account, it does not fold a path, and it cannot
make the gate accept. Every field it emits goes into the Lean decision, and the
worst a hostile endpoint achieves is to be REFUSED.

⚑ WHY THE SERVER'S `leafHash` IS FETCHED AND NEVER USED AS AN INPUT

The daemon will happily tell you the leaf hash of an account. Believing it is
precisely the thing that makes a bridge non-semantic: you would then know "some
leaf is in the ledger" and not "this account has this balance". So `leafHash` is
recorded in the fixture as a CROSS-CHECK ONLY — the Lean gate recomputes the
leaf from `(balance, nonce, delegate, ...)` and a mismatch is a red gate, not a
fallback.

⚑ THE RACE, AND WHY IT IS SELF-DETECTING

`merklePath` is served from the daemon's best-tip ledger; `stagedLedgerHash` is
read off the best-tip block. Between the two resolvers a block can land. That is
not a soundness problem here because the fixture is only ACCEPTED when the
recomputed root equals the ledger hash — a 255-bit equation. A race shows up as
a refusal, and `--retries` re-fetches. There is no branch in which a stale path
is admitted.

Usage:
    mina-account-opening.py --public-key B62q... -o fixture.json
    mina-account-opening.py --from-tip-creator -o fixture.json

Devnet only. No keys, no state, nothing persisted beyond the fixture.
"""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
import time
import urllib.request

DEFAULT_ENDPOINT = "https://api.minascan.io/node/devnet/v1/graphql"

B58 = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"


def b58_decode(s: str) -> bytes:
    n = 0
    for c in s:
        n = n * 58 + B58.index(c)
    body = n.to_bytes((n.bit_length() + 7) // 8, "big")
    pad = len(s) - len(s.lstrip("1"))
    return b"\x00" * pad + body


def mina_hash_to_field(s: str) -> int:
    """Mina base58check for a `Data_hash` (ledger hash, receipt chain hash,
    state hash): `version_byte || 0x01 || 32 bytes LITTLE-endian || 4 checksum`.

    The 32 bytes are the field element little-endian — the same convention
    `Dregg2.Bridge.MinaBinprot.fpLE` reads off the binprot wire, which is why a
    value decoded here and a value decoded there are directly comparable."""
    raw = b58_decode(s)
    body = raw[:-4]
    if len(body) == 34:
        # `Data_hash`: outer version byte, then a `Stable.V1` version byte.
        if body[1] != 1:
            raise ValueError(f"unexpected inner version {body[1]} for {s!r}")
        payload = body[2:34]
    elif len(body) == 33:
        # `Token_id`: outer version byte only (`Mina_base.Token_id` serialises
        # its field directly, no per-value version).
        payload = body[1:33]
    else:
        raise ValueError(f"unexpected base58check body length {len(body)} for {s!r}")
    return int.from_bytes(payload, "little")


def b58_public_key_to_xy(s: str) -> tuple[int, bool]:
    """`Public_key.Compressed` base58check.

    ⚑ TWO version bytes, not one: `0xcb || 0x01 || 0x01 || 32 bytes LE x ||
    is_odd || checksum`. `Public_key.Compressed.Stable.V1` wraps
    `Non_zero_curve_point.Compressed.Poly.Stable.V1`, and binprot writes a
    version byte for EACH. Reading the field at offset 2 (one version byte, as
    for a `Data_hash`) parses without error and yields a different point — it
    was caught here by cross-reading o1js's `PublicKey.fromBase58`, which is why
    this decode has a second source at all."""
    raw = b58_decode(s)
    if len(raw) != 40:
        raise ValueError(f"unexpected pk length {len(raw)} for {s!r}")
    body = raw[:-4]
    if body[1] != 1 or body[2] != 1:
        raise ValueError(f"unexpected pk version bytes {body[1]},{body[2]} for {s!r}")
    x = int.from_bytes(body[3:35], "little")
    is_odd = body[35] != 0
    return x, is_odd


def gql(endpoint: str, query: str) -> dict:
    req = urllib.request.Request(
        endpoint,
        data=json.dumps({"query": query}).encode(),
        # ⚑ The UA is not cosmetic: minascan's edge 403s the bare urllib default.
        headers={
            "Content-Type": "application/json",
            "User-Agent": "curl/8.7.1",
            "Accept": "application/json",
        },
    )
    with urllib.request.urlopen(req, timeout=90) as r:
        out = json.loads(r.read())
    if "errors" in out:
        raise RuntimeError(json.dumps(out["errors"]))
    return out["data"]


ACCOUNT_QUERY = """query {
  bestChain(maxLength: 1) {
    stateHash
    protocolState {
      previousStateHash
      blockchainState { stagedLedgerHash snarkedLedgerHash }
      consensusState { blockHeight }
    }
  }
  account(publicKey: "%s") {
    publicKey tokenId balance { total } nonce receiptChainHash delegate
    votingFor tokenSymbol index leafHash zkappState provedState
    permissions {
      editState access send receive setDelegate setPermissions
      setVerificationKey { auth txnVersion }
      setZkappUri editActionState setTokenSymbol incrementNonce setVotingFor setTiming
    }
    timing { initialMinimumBalance cliffTime cliffAmount vestingPeriod vestingIncrement }
    merklePath { left right }
  }
}"""


def fetch(endpoint: str, pk: str) -> dict:
    d = gql(endpoint, ACCOUNT_QUERY % pk)
    tip = d["bestChain"][0]
    a = d["account"]
    if a is None:
        raise RuntimeError(f"no such account on this endpoint: {pk}")

    # The opening, flattened. Mina's `Merkle_path.t` is `Left h | Right h` and
    # the GraphQL element carries exactly one of the two. Which side the SIBLING
    # sits on is the direction bit; the value is the sibling hash.
    siblings: list[str] = []
    node_is_left: list[bool] = []
    for e in a["merklePath"]:
        if (e["left"] is None) == (e["right"] is None):
            raise RuntimeError(f"merkle path element is not a disjunction: {e}")
        # ⚑ `Merkle_path.t = Left of hash | Right of hash`, and the tag names
        # which side the CURRENT NODE is on, not the sibling's:
        # `implied_root` folds `Left h -> hash acc h` (acc left, sibling right).
        # Read the other way round the fold is transposed at every level and the
        # root is wrong — the fixture's own index bits are the cross-check
        # (`nodeIsLeft[i] == (index >> i) & 1 == 0`).
        if e["left"] is not None:
            siblings.append(e["left"])
            node_is_left.append(True)
        else:
            siblings.append(e["right"])
            node_is_left.append(False)

    for i, nl in enumerate(node_is_left):
        if nl != (((a["index"] >> i) & 1) == 0):
            raise RuntimeError(
                f"merkle path direction at level {i} contradicts the account index "
                f"{a['index']}: the server's own two answers disagree"
            )

    pk_x, pk_odd = b58_public_key_to_xy(a["publicKey"])
    dg_x, dg_odd = b58_public_key_to_xy(a["delegate"]) if a["delegate"] else (pk_x, pk_odd)

    t = a["timing"] or {}
    timed = t.get("cliffTime") is not None

    return {
        "kind": "mina-account-opening/v1",
        "endpoint": endpoint,
        "fetchedAtUnix": int(time.time()),
        "tip": {
            "stateHash": tip["stateHash"],
            "previousStateHashB58": tip["protocolState"]["previousStateHash"],
            "previousStateHash": str(
                mina_hash_to_field(tip["protocolState"]["previousStateHash"])
            ),
            "blockHeight": int(tip["protocolState"]["consensusState"]["blockHeight"]),
            "stagedLedgerHashB58": tip["protocolState"]["blockchainState"]["stagedLedgerHash"],
            "stagedLedgerHash": str(
                mina_hash_to_field(tip["protocolState"]["blockchainState"]["stagedLedgerHash"])
            ),
        },
        "account": {
            "publicKeyB58": a["publicKey"],
            "publicKeyX": str(pk_x),
            "publicKeyIsOdd": pk_odd,
            "tokenIdB58": a["tokenId"],
            "tokenId": str(mina_hash_to_field(a["tokenId"])),
            "tokenSymbol": a["tokenSymbol"] or "",
            "balance": a["balance"]["total"],
            "nonce": a["nonce"],
            "receiptChainHashB58": a["receiptChainHash"],
            "receiptChainHash": str(mina_hash_to_field(a["receiptChainHash"])),
            "delegateB58": a["delegate"],
            "delegateX": str(dg_x),
            "delegateIsOdd": dg_odd,
            "votingForB58": a["votingFor"],
            "votingFor": str(mina_hash_to_field(a["votingFor"])),
            "isTimed": timed,
            "timing": {
                "initialMinimumBalance": t.get("initialMinimumBalance") or "0",
                "cliffTime": t.get("cliffTime") or "0",
                "cliffAmount": t.get("cliffAmount") or "0",
                "vestingPeriod": t.get("vestingPeriod") or ("0" if not timed else "1"),
                "vestingIncrement": t.get("vestingIncrement") or "0",
            },
            "permissions": a["permissions"],
            "zkappState": a["zkappState"],
            "provedState": a["provedState"],
            "index": a["index"],
            # ⚑ CROSS-CHECK ONLY. The gate recomputes this from the fields above.
            "serverLeafHash": a["leafHash"],
        },
        "opening": {
            "depth": len(siblings),
            "siblings": siblings,
            "nodeIsLeft": node_is_left,
        },
    }


BESTTIP = os.path.join(os.path.dirname(os.path.abspath(__file__)), "mina-besttip.py")


def attach_block(fx: dict, prefix_bytes: int) -> dict:
    """Fetch the SAME tip's binprot `Protocol_state.Value.Stable.V2` over Mina's own
    p2p wire and attach its hex prefix.

    ⚑ THE TIP-IDENTITY CHECK IS A BYTE COMPARISON, NOT A HASH. The first 32 bytes of
    a `Protocol_state.Value` are `previous_state_hash`, little-endian. The GraphQL tip
    reports its own `previousStateHash`. If the two agree, the block these bytes are is
    the block the account opening came from — established without computing anything,
    which is exactly what a fixture builder should be able to do. A mismatch means a
    block landed between the two fetches; it RAISES, it does not paper over."""
    out = subprocess.run(
        [sys.executable, BESTTIP, "--emit-protocol-state"],
        capture_output=True, timeout=180,
    )
    if out.returncode != 0:
        raise RuntimeError(f"mina-besttip failed: {out.stderr.decode()[-400:]}")
    raw = out.stdout
    prev = int.from_bytes(raw[:32], "little")
    if str(prev) != fx["tip"]["previousStateHash"]:
        raise RuntimeError(
            "p2p tip and GraphQL tip are different blocks "
            f"(p2p previous_state_hash {prev} != GraphQL {fx['tip']['previousStateHash']})"
        )
    fx["block"] = {
        "source": "coda/rpcs/0.0.1 get_best_tip via bridge/tools/mina-besttip.py",
        "prefixBytes": prefix_bytes,
        "totalBytesServed": len(raw),
        "hex": raw[:prefix_bytes].hex(),
    }
    return fx


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--endpoint", default=DEFAULT_ENDPOINT)
    ap.add_argument("--public-key")
    ap.add_argument("--from-tip-creator", action="store_true")
    ap.add_argument("-o", "--out", default="-")
    ap.add_argument("--retries", type=int, default=3)
    ap.add_argument(
        "--with-block", action="store_true",
        help="also fetch the tip's binprot protocol state over p2p and attach its hex prefix",
    )
    ap.add_argument("--prefix-bytes", type=int, default=2048)
    args = ap.parse_args()

    pk = args.public_key
    if args.from_tip_creator or not pk:
        pk = gql(args.endpoint, "query { bestChain(maxLength: 1) { creator } }")["bestChain"][0][
            "creator"
        ]

    last: Exception | None = None
    for _ in range(max(1, args.retries)):
        try:
            fx = fetch(args.endpoint, pk)
            if args.with_block:
                fx = attach_block(fx, args.prefix_bytes)
            break
        except Exception as e:  # noqa: BLE001 — a network client, retry and report
            last = e
            time.sleep(2)
    else:
        print(f"fetch failed: {last}", file=sys.stderr)
        return 1

    text = json.dumps(fx, indent=1) + "\n"
    if args.out == "-":
        sys.stdout.write(text)
    else:
        with open(args.out, "w") as f:
            f.write(text)
        print(
            f"wrote {args.out}: account {fx['account']['publicKeyB58']} "
            f"index {fx['account']['index']} depth {fx['opening']['depth']} "
            f"@ height {fx['tip']['blockHeight']}",
            file=sys.stderr,
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
