# deos dev environment: a live local node + the cockpit attached to it

This is the working environment for developing on dregg: a real `dregg-node`
running locally with the verified **lean** state producer, and the deos cockpit
(`starbridge-v2`) attached to it so its receipt feed and federation/cell views
reflect that live node alongside the embedded image.

Nothing here is a demo or a mock. The node commits real verified turns; the
cockpit reads the node's real `/status`, `/api/cells`, `/api/receipts`, and the
SSE `/api/events/stream` receipt push.

## 1. Build

```sh
cargo build -p dregg-node
```

The node links the verified Lean kernel (`libdregg_lean.a`). If the metatheory
working tree has an in-progress proof regression (a module that fails its
`#assert_axioms` hygiene gate, so `lake build Dregg2.Exec.FFI` exits non-zero),
the FFI build script (`dregg-lean-ffi/build.rs`) now detects the failed Lean
build, restores the git-tracked consistent seed archive, and links that — instead
of splicing a torn partial set whose cross-module specializations don't resolve.
So the node builds and runs even while a proof lane is mid-flight. To pick up
fresh Lean changes in the kernel, make `lake build Dregg2.Exec.FFI` green in
`metatheory/` first, then rebuild.

## 2. Stand up the node

```sh
# fresh data dir (idempotent: init skips if the dir already exists)
./target/debug/dregg-node init --data-dir /tmp/deos-node

# run with the devnet faucet on port 8771
./target/debug/dregg-node run --data-dir /tmp/deos-node --enable-faucet --port 8771
```

The first `run` against a fresh data dir does a one-time devnet backfill
(materializes the `alice` agent key + a few starbridge factory cells), then binds
the HTTP API. Wait for:

```
INFO dregg_node: HTTP API listening addr=127.0.0.1:8771
```

(~15–20s on a fresh dir; near-instant afterward.) Until that line, `/status`
will refuse the connection — the node is still seeding.

### Confirm the lean producer is live

```sh
curl -s http://127.0.0.1:8771/status | python3 -m json.tool
```

```json
{
    "healthy": false,
    "peer_count": 0,
    "latest_height": 0,
    "consensus_live": true,
    "federation_mode": "solo",
    "state_producer": "lean",
    "lean_producer": true,
    "full_turn_proving": false,
    "producer_covered_effects": 21
}
```

`state_producer: "lean"` + `lean_producer: true` is the verified producer.
`healthy: false` is just `peer_count == 0` (n=1 solo devnet) — expected. Add
`--prove-turns` (or `DREGG_PROVE_TURNS=1`) to flip `full_turn_proving` on (every
committed turn carries a full-turn STARK; off by default since it is on the hot
path).

### Faucet a cell and read it back

The faucet recipient is `CellId::derive_raw(public_key, blake3("default"))`. With
`public_key` set, the node materializes a real hosted cell (not a stub):

```sh
curl -s -X POST http://127.0.0.1:8771/api/faucet \
  -H 'Content-Type: application/json' \
  -d '{"recipient":"<derived-cell-id-hex>","amount":5000,"public_key":"<pubkey-hex>"}'
# -> {"success":true,"turn_hash":"9696a1ad…","amount":5000,…}

curl -s http://127.0.0.1:8771/api/cell/<derived-cell-id-hex> | python3 -m json.tool
# -> {"found":true,"balance":5000,"public_key":"…","state_commitment":"…",…}
```

The faucet commits a real verified turn; its receipt appears in the feed
(`pre_state → post_state`, `has_proof:true`, `executor_signed:true`,
`has_witness:true`):

```sh
curl -s "http://127.0.0.1:8771/api/receipts?limit=5" | python3 -m json.tool
```

The same receipt is pushed over the SSE stream (replay from the start with
`Last-Event-ID: 0`):

```sh
curl -sN -H 'Last-Event-ID: 0' http://127.0.0.1:8771/api/events/stream
# event: receipt
# id: 1
# data: {"chain_index":1,"turn_hash":"…","has_proof":true,…}
```

A fresh SSE connection without `Last-Event-ID` tails from the current head — it
only emits receipts committed *after* you connect, so trigger a turn to see it
push. This is exactly what the cockpit's live pump consumes.

## 3. Boot deos against the node

```sh
cd starbridge-v2
cargo run --features native-full --bin starbridge-v2 -- --node http://localhost:8771
```

(`--node=http://localhost:8771` also works.) deos boots into the login ceremony;
pick an identity and the cockpit comes up over the embedded verified image AND
attached to the live node. The attach (`starbridge-v2/src/main.rs` →
`login::LoginSurface::boot` → `Cockpit::with_node`) does, on connect:

* `LiveNode::sync()` — one blocking snapshot of `/status` + `/api/cells` +
  `/api/receipts`, projected into the cockpit's live reflections (the live-node
  panel / federation view).
* `LiveNode::connect_stream()` — opens the SSE `/api/events/stream`; a background
  reader feeds the pure parser and the cockpit's `pump_live` drains it each frame,
  so the receipt feed advances LIVE on every turn the node commits.

An unreachable node is non-fatal: the embedded image stays fully usable, the live
panels just show no node state.

## One-liner to bring it all up

```sh
cargo build -p dregg-node && \
./target/debug/dregg-node init --data-dir /tmp/deos-node ; \
./target/debug/dregg-node run --data-dir /tmp/deos-node --enable-faucet --port 8771 &
# wait for "HTTP API listening", then:
( cd starbridge-v2 && cargo run --features native-full --bin starbridge-v2 -- --node http://localhost:8771 )
```

## THE ONE UNIFIED BOOT — node + editor + terminal + live-node pane, one frame

The cockpit struct already carries all the pieces at once (the live-node attach +
the FirmamentFs editor + the live PTY terminal); they are normally on separate
tabs. `--render-unified-boot` bakes a SINGLE headless frame that mounts THREE
panes side by side over a real running node, drives a real editor save, and
settles the editor-save write-back question EMPIRICALLY by re-reading the node's
receipt count. (`starbridge-v2/src/unified_boot.rs` + the `--render-unified-boot`
bake in `main.rs`.)

```sh
# 1. Stand up a node with the faucet (a known port + data dir).
NODE=./target/debug/dregg-node
$NODE init --data-dir /tmp/deos-unified-node
$NODE run --data-dir /tmp/deos-unified-node --enable-faucet --port 8775 --gossip-port 9775 &
# wait for "HTTP API listening"

# 2. Faucet a real cell so the node ledger has a real verified receipt. The
#    recipient cell is derive_raw(node_pubkey, H("default")) — read it off the node:
ID=$(curl -s http://127.0.0.1:8775/api/node/identity)
PK=$(echo "$ID" | python3 -c 'import sys,json;print(json.load(sys.stdin)["public_key"])')
CID=$(echo "$ID" | python3 -c 'import sys,json;print(json.load(sys.stdin)["agent_cell"])')
curl -s -X POST http://127.0.0.1:8775/api/faucet -H 'Content-Type: application/json' \
  -d "{\"recipient\":\"$CID\",\"amount\":5000,\"public_key\":\"$PK\"}"
# -> {"success":true,...}; /api/receipts now has one has_proof:true receipt.

# 3. Bake the unified frame attached to that node.
( cd starbridge-v2 && cargo build --features native-full --bin starbridge-v2 )
./starbridge-v2/target/debug/starbridge-v2 \
  --render-unified-boot /tmp/deos-unified-boot \
  --node http://127.0.0.1:8775 --render-size 1900x1000
```

The bake prints (and writes `/tmp/deos-unified-boot.png`, 3800x2000):

* **PANE (live node)** — attached to the node; lean producer LIVE; its cells +
  the latest verified receipt, pulled over `/api/cells` + `/api/receipts`. This is
  what proves the attach is LIVE, not embedded.
* **PANE (editor)** — a real save fired: the local on-ledger receipt count grew (a
  cap-gated `SetField` turn).
* **PANE (terminal)** — a live alacritty PTY ran `cargo --version` INSIDE deos.
* **WRITE-BACK PROBE** — the node's receipt count is re-read over the wire BEFORE
  and AFTER the editor save.

### The honest write-back seam (what the probe measures)

The editor save does **NOT** reach the node ledger today — it is LOCAL-ONLY.
`EditorPane::firmament_over` commits the `SetField` turn to the cockpit's OWN
`World` (a `WorldSpine` over `World::commit_turn`); the `--node` attach is
READ-ONLY-SYNCED (`LiveNode::sync` for the snapshot + the SSE pump for the live
receipt feed). So the unified boot is real (one window, node-attached-live +
editor + terminal), but the editor and the node are two ledgers: the node's
receipt count is unchanged by an editor save.

To make a save a self-hosting write-back to the NODE, the FirmamentFs save path
would route the turn through `NodeClient::submit_turn` (the designed-pending write
surface on `LiveNode`) instead of (or in addition to) the local `WorldSpine` —
which also needs local key custody to sign the turn (or routing it through the
node operator's cipherclerk). That is the named integration seam.

## A REAL two-node federation (n=2, proven by running)

This stands up two `dregg-node` processes that form ONE federation (committee of
two, threshold 2) over the live QUIC gossip + blocklace consensus, and shows a
turn submitted on node A finalizing on node B. This is not a mock: both nodes run
the verified Lean producer, exchange real Ed25519-signed blocks, and converge to a
byte-identical DAG.

The committee is established by a SHARED `genesis.json` carrying BOTH validators'
public keys. The `genesis` subcommand mints that file plus the two node keys:

```sh
NODE=./target/debug/dregg-node
cargo build -p dregg-node

# 1. Mint a 2-validator genesis (shared genesis.json + node-0.key/node-1.key +
#    the well/agent keys). Threshold is floor(2*2/3)+1 = 2.
$NODE genesis --validators 2 --output /tmp/deos-fed/stage

# 2. Build two data dirs sharing the SAME genesis + well/agent keys; give each
#    its own identity key (node-0 -> A, node-1 -> B). The shared genesis.json is
#    what makes both nodes the SAME federation (same committee -> same
#    federation_id -> participants == {A, B}).
for D in /tmp/deos-fed/nodeA /tmp/deos-fed/nodeB; do
  mkdir -p "$D"
  cp /tmp/deos-fed/stage/genesis.json /tmp/deos-fed/stage/.devnet "$D"/
  cp /tmp/deos-fed/stage/{agent-alice,agent-bob,agent-carol,faucet,fee-well,issuer-well}.key "$D"/
done
cp /tmp/deos-fed/stage/node-0.key /tmp/deos-fed/nodeA/node.key
cp /tmp/deos-fed/stage/node-1.key /tmp/deos-fed/nodeB/node.key
chmod 600 /tmp/deos-fed/node{A,B}/node.key

# 3. Run both, --federation-mode full, gossip ports cross-pointing.
RUST_LOG=info $NODE run --data-dir /tmp/deos-fed/nodeA --enable-faucet \
  --port 8801 --gossip-port 9801 --federation-peers 127.0.0.1:9802 \
  --federation-mode full --consensus blocklace &
RUST_LOG=info $NODE run --data-dir /tmp/deos-fed/nodeB --enable-faucet \
  --port 8802 --gossip-port 9802 --federation-peers 127.0.0.1:9801 \
  --federation-mode full --consensus blocklace &
```

Wait for both `HTTP API listening` lines. In each node's log you should see
`initializing blocklace consensus participants=2 quorum_threshold=2 solo=false`
and `consensus mesh ready ... connected=1 want=1` — the live QUIC link is up.
`/status` on each reports `federation_mode:"full"` and `peer_count:1`.

Submit a faucet turn on A (the recipient is
`CellId::derive_raw(agent_pubkey, blake3("default"))`); it will gossip to B and
both finalize it cross-node:

```sh
# (derive ALICE_PK / ALICE_CID from agent-alice.key as in §2 of the main runbook)
curl -s -X POST http://127.0.0.1:8801/api/faucet -H 'Content-Type: application/json' \
  -d "{\"recipient\":\"$ALICE_CID\",\"amount\":5000,\"public_key\":\"$ALICE_PK\"}"

# Within ~5s both DAGs converge identically and the turn finalizes on BOTH:
curl -s http://127.0.0.1:8801/status   # dag_height>0, latest_height=1
curl -s http://127.0.0.1:8802/status   # SAME
curl -s http://127.0.0.1:8801/api/cell/$ALICE_CID   # balance 5000
curl -s http://127.0.0.1:8802/api/cell/$ALICE_CID   # balance 5000 (finalized cross-node)
```

Observed: both `/api/blocklace/blocks` return the IDENTICAL 6-block DAG (same
block hashes; a round-2 `turn` block surrounded by round 1/2/3 attestation acks),
`latest_height=1` on both (the turn-bearing block super-ratified cross-node), and
alice's cell balance = 5000 on BOTH nodes — the faucet turn's effect applied
deterministically through consensus finalization, not locally.

## Robust federation: LATE JOIN / reconnect (a peer down at boot still converges)

The n=2 run above assumes both nodes are up when they dial. Federation is also
robust when a peer is DOWN at boot (or drops and returns): each node runs a
**peer reconnect prober** (`blocklace_sync::spawn_peer_prober`) that re-dials any
known-but-unconnected federation peer on a `RequestBackoff` schedule
(`net/src/peer_score.rs`), so the mesh forms — and the DAG converges — without an
operator restart. Two supporting pieces make this work:

* `GossipNetwork::{unconnected_topic_peers, reconnect_peer}` (`net/src/gossip.rs`):
  the prober asks which topic peers have no live link (graylisted peers excluded)
  and re-dials them; a recovered link is registered and the eager/lazy split
  recomputed, restoring a spanning tree.
* A **bounded initial dial** (`DIAL_TIMEOUT = 3s`): `join_topic`'s startup dial no
  longer blocks on the ~30s QUIC idle timeout when a peer is down — a peer
  unreachable at boot no longer stalls node startup; the prober picks it up.

### Demonstrate a late join (proven by running)

Stage a 2-validator genesis as above (into `/tmp/deos-fed/stage`), build the two
data dirs, then start **A first while B is still down**:

```sh
NODE=./target/debug/dregg-node
# A boots pointing at B (9802) — B is NOT up yet, so A's initial dial fails.
RUST_LOG=info,dregg_net=info $NODE run --data-dir /tmp/deos-fed/nodeA --enable-faucet \
  --port 8801 --gossip-port 9801 --federation-peers 127.0.0.1:9802 \
  --federation-mode full --consensus blocklace &
# Wait for A's "HTTP API listening" (it comes up promptly — the bounded dial does
# NOT hang on the down peer). A logs "peer reconnect prober active interval_ms=8000".

# Now B comes up (the peer returns):
RUST_LOG=info,dregg_net=info $NODE run --data-dir /tmp/deos-fed/nodeB --enable-faucet \
  --port 8802 --gossip-port 9802 --federation-peers 127.0.0.1:9801 \
  --federation-mode full --consensus blocklace &
```

Within the retry window the link forms (whichever node dials first; if A's initial
dial failed, A's prober re-dials B once it is up — or B's join dials A). A turn
submitted on EITHER node then converges cross-node to consensus-attested finality:

```sh
# (derive ALICE_PK / ALICE_CID as in §2)
curl -s -X POST http://127.0.0.1:8801/api/faucet -H 'Content-Type: application/json' \
  -d "{\"recipient\":\"$ALICE_CID\",\"amount\":5000,\"public_key\":\"$ALICE_PK\"}"
sleep 15
curl -s http://127.0.0.1:8801/status   # dag_height>0, latest_height=1
curl -s http://127.0.0.1:8802/status   # SAME
curl -s http://127.0.0.1:8801/api/cell/$ALICE_CID   # balance 5000
curl -s http://127.0.0.1:8802/api/cell/$ALICE_CID   # balance 5000 (finalized cross-node)
```

Observed (a real two-process run): A came up with B down (bounded dial, no stall)
and logged `peer reconnect prober active`; once B joined, both DAGs converged to
the IDENTICAL height (`dag_height 3`, `latest_height 1`), the turn-bearing block
reached `CONSENSUS-WIDE Attested finality … votes=2` on BOTH nodes, and alice's
cell = 5000 on both — the late-joined federation finalized a turn cross-node.

### The faithful in-process reconnect test

The prober/backoff reconnect path is pinned by a real two-node QUIC test,
`net/src/gossip.rs::late_join_prober_reconnects_after_initial_dial_failure`:
node A joins a topic pointing at B's address while B is DOWN (initial dial fails,
`connected_peer_count == 0`, B is an `unconnected_topic_peers` candidate); B then
comes up; A's prober loop (`unconnected_topic_peers` → `RequestBackoff::should_request`
→ `reconnect_peer`) reconnects within the retry window, and a `publish_eager` from
EACH node is delivered to the OTHER — the recovered link carries gossip in both
directions (`cd net && cargo test late_join_prober`).

## Federation DISCOVERY: gossip-of-peers (learn the mesh from one seed)

A node no longer has to list EVERY peer on its CLI. Configure one node (the
**seed**) with the full peer set and each other node with just the seed; the
nodes learn the rest of the mesh transitively over authenticated gossip-of-peers.

### How it works (authenticated; the committee key set is the trust anchor)

* The gossip layer records a **cryptographically-verified** `peer-identity →
  dialable listen address` binding for every link it dials over which an
  Ed25519-signed envelope verifies (`GossipNetwork::verified_peer_bindings`,
  `net/src/gossip.rs`). The identity is `blake3(committee_public_key)` — proven by
  the signature, not claimed.
* Each prober tick (and on every `PeerJoined`) a node SHARES those verified
  bindings as a `BlocklaceGossipMessage::PeerAddrs(Vec<(committee_pubkey, addr)>)`
  (`BlocklaceHandle::share_peer_addrs`, `node/src/blocklace_sync.rs`). The carrying
  envelope is itself signed by the sender's federation key.
* The receiver (`handle_peer_addrs`) accepts an address **only** when its
  `committee_pubkey` is one of its OWN `known_federation_keys` — a genesis-trusted
  member — and never for itself or an un-dialable (`0.0.0.0`/port-0) socket. A
  claimed address for a NON-committee key (a stranger an introducer tries to
  smuggle in) is REJECTED. Accepted addresses are fed to `GossipNetwork::learn_peer`
  (no synchronous dial); the existing reconnect prober dials them on its backoff
  schedule. So the trust anchor is the COMMITTEE, never the wire sender: discovery
  learns ADDRESSES for already-trusted identities, it never admits new identities.

### Demonstrate transitive discovery from partial config (3 nodes, one seed)

The committee (the trusted key set, `known_federation_keys`) is shared by all
three nodes via an identical `genesis.json` (its `validators[].public_key` list =
pkA, pkB, pkC) in each `--data-dir`. ONLY the `--federation-peers` address list
differs per node — that is the partial config discovery fills in.

```
# A is the SEED — its peer list names B and C.
dregg-node run --data-dir /tmp/dregg-A --auto-approve-joins \
  --port 8801 --gossip-port 9801 --federation-peers 127.0.0.1:9802,127.0.0.1:9803

# B's peer list names ONLY A (it does NOT list C).
dregg-node run --data-dir /tmp/dregg-B --auto-approve-joins \
  --port 8802 --gossip-port 9802 --federation-peers 127.0.0.1:9801

# C's peer list names ONLY A (it does NOT list B).
dregg-node run --data-dir /tmp/dregg-C --auto-approve-joins \
  --port 8803 --gossip-port 9803 --federation-peers 127.0.0.1:9801
```

B connects to its seed A, receives A's verified `PeerAddrs` (which includes C's
authenticated address, because C is a committee member A has dialed), learns it,
and B's prober dials C — symmetrically for C learning B. A full 3-node mesh forms
from partial CLI config; the DAG converges on all three. Watch for
`gossip-of-peers: learned committee peer address` then `peer reconnect prober:
(re)established link` on B and C.

### The faithful in-process discovery tests

* `net/src/gossip.rs::gossip_of_peers_transitive_discovery_from_single_seed` —
  three REAL gossip networks over loopback QUIC. Seed A knows B+C; B knows only A.
  After signed gossip crosses, A holds a verified binding for C that is C's real
  LISTEN address (asserted dialable). Driving the exact discovery write-path
  (`verified_peer_bindings` → `learn_peer` → prober `reconnect_peer`), B connects
  to the DISCOVERED peer C and B↔C gossip converges over the new link — the mesh
  formed from B's single seed (`cd net && cargo test gossip_of_peers_transitive`).
* `node/src/blocklace_sync.rs::gossip_of_peers_accepts_committee_rejects_forged` —
  the trust gate: a `PeerAddrs` carrying a valid committee binding (C), a FORGED
  binding for a non-committee Sybil key (X), and a self-binding is fed through the
  real `handle_peer_addrs`; ONLY C's address is learned into the gossip topic peer
  set. X is rejected (a stranger is not admitted), self is ignored, and re-announcing
  a known address is idempotent (`cd node && cargo test --bin dregg-node
  gossip_of_peers_accepts_committee_rejects_forged`).
