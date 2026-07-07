# STAGE 5 — the n=4 discriminating experiment: plateau → streaming, CONFIRMED

**Status:** empirical result (2026-07-06). Ran the single-variable experiment the diagnosis
(`docs/STAGE5-DIAGNOSIS.md`, design D1) predicted, on ember's re-runnable dev federation over the real
LAN (`192.168.50.0/24`). **The diagnosis is confirmed:** at n=3 `latest_height` plateaus at 1; the
*only* change to n=4 — a deploy-config change, no consensus code touched — converts the plateau into
**streaming cross-node finality**.

This is a **deployment** result, not a code change. No consensus/kernel/Lean/gentian/assurance code was
modified. The lever is exactly the one the diagnosis reserves for the operator: the committee size N,
which sets the super-ratification threshold `supermajority_threshold(N) = ⌊2N/3⌋ + 1`
(`blocklace/src/ordering.rs`).

---

## The single variable

| | n=3 (before) | n=4 (after) |
|---|---|---|
| `supermajority_threshold(N)` | **3** (unanimity) | **3** (3-of-4) |
| tolerated laggards / round (N − q) | **0** | **1** |
| observed `latest_height` | **plateaus at 1** | **streams: 0 → 22 → … climbing** |

Everything else held fixed: same binary, same `--idle-heartbeat-ms 2000 --block-cadence-ms 1000`, same
`--federation-mode full --consensus blocklace`, same real QUIC over the LAN, same marshal executor
(`DREGG_ALLOW_UNVERIFIED_CONSENSUS=1`, `state_producer=rust`).

## Setup

- **Genesis:** `dregg-node genesis --validators 4` → federation `8811baf9…`, threshold 3, 4 distinct
  validator keys sharing one `genesis.json`. Ephemeral/re-runnable.
- **Topology:** 4 marshal nodes across 2 boxes, 2 processes per box.
  - hbox `192.168.50.39`: node0 (http 8420 / gossip 9420), node1 (8421 / 9421) — binary
    `~/dev/breadstuffs-n3fed/target/debug/dregg-node`.
  - nextop `192.168.50.130`: node2 (8420 / 9420), node3 (8421 / 9421) — binary
    `~/dev/breadstuffs/target/debug/dregg-node`.
  - Each `--bind` its LAN IP; `--federation-peers` = the other three `IP:GOSSIPPORT` literals.
  - Launch scripts live on the boxes: `~/n4fed/launch-hbox.sh`, `~/n4fed/launch-nextop.sh`.
- **Mesh confirmed:** all 4 report `peer_count=3`, `consensus_live=true`, and a byte-identical DAG at
  every sample.
- **Turn stream:** `POST /api/faucet` (faucet cell → a fresh random recipient each call, amount 1) — a
  genuine state-mutating turn — submitted every ~4s, rotating across all 4 nodes.

## Measurement — `latest_height` across all 4 nodes over ~3 min of streaming

Each row is `latest_height` read from node0 / node1 / node2 / node3 independently. They agree at every
sample — the same height finalized on all four, receipts replicating.

```
 t     n0 n1 n2 n3
  4s    2  2  2  2
 12s    3  3  3  3
 21s    4  4  4  4
 30s    5  5  5  5
 42s    6  6  6  6
 51s    7  7  7  7
 60s    8  8  8  8
 69s    9  9  9  9
 78s   10 10 10 10
 87s   11 11 11 11
 …      (continuous)
 89s   21 21 21 21
 final 22 22 22 22   (dag_height=100, block_count=400, all peer_count=3, consensus_live=true)
```

- **Monotone, cross-node, no plateau.** Height climbed 0 → 22 and kept going, identical on all four
  nodes at every checkpoint. This is streaming finality — a living federation, not a single-turn
  liveness witness.
- **Steady rate, no observed slowdown.** ~1 height per ~8s held flat across the whole ~3-minute window
  (one height per ~2 submitted turns; a wave folds several turns). The O(history) amplifier (diagnosis
  cause 2 / D2 / D3) did **not** visibly degrade the rate over this window and this run length — it
  streamed steadily, it did not stream-then-slow. (D2/D3 remain the right levers for a much longer-lived
  node where the tau walk over an unbounded lace would eventually dominate; they were not needed to lift
  the plateau.)
- **Receipts replicate cross-node** (`/api/receipts`: 31/31/32/31 mid-stream, the ±1 a one-turn
  submission skew that converges).

## Verdict

The dominant root cause named in the diagnosis is confirmed: **n=3 is a zero-slack, unanimity-every-
round configuration** that cannot absorb a single asymmetrically-delivered block across a multi-round
wave, so waves after the first fail to close and `latest_height` sticks at 1. Moving to **n=4** gives
each wave-closing round one node of slack (3-of-4), and finality streams. Safety is unchanged — quorum
intersection still holds (`2·3 − 4 = 2 > f`).

**D1 is the fix, and it is a deploy dial, not a code change.** Run streaming federations at N ≥ 4.

## Reproduce

```
# stop any prior run, then on each box:
ssh hbox 'bash ~/n4fed/launch-hbox.sh'      # node0, node1
bash ~/n4fed/launch-nextop.sh               # node2, node3  (run on nextop)
# confirm mesh: each /status shows peer_count=3, consensus_live=true
# stream turns + watch height climb identically on all 4:
curl -s -X POST http://<node>/api/faucet -H 'content-type: application/json' \
  -d '{"recipient":"<random-32-byte-hex>","amount":1}'
curl -s http://<node>/status   # latest_height advances 1 → 2 → 3 → … cross-node
```

## Follow-up (stretch, not done here)

The turns finalized above are real state-mutating turns finalizing cross-node on the living n=4 mesh.
The depth-crowning payoff — pointing a flagship / full-turn-proving attested turn at the mesh
(`--features http` fleet, `DREGG_NODE_URL` at a node) and watching it finalize cross-node — remains as a
follow-up on this same living federation; it is orthogonal to the plateau→streaming result, which stands
on its own.
