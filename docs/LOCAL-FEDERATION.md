# The local multi-node federation — decentralized, not one node

`scripts/federation-local.sh` stands up a **private, localhost-bound, N-node
dregg federation** on a single box and drives a real **cross-node finality**
check: a turn submitted to one node finalizes across the whole committee.

This is the "it is actually decentralized" step past the solo private node. The
solo node processes turns alone (a `NullifierLog`, `Tentative` receipts, no
quorum). A federation is **N distinct validators** — distinct keys, distinct
ports — running **blocklace BFT consensus** (Cordial Miners DAG + the `tau`
total-ordering function, `blocklace/` + `node/src/blocklace_sync.rs`). A turn is
finalized only when a **supermajority of the committee** super-ratifies it; the
same attested-root height then climbs identically on every node.

## What runs

- **N validator processes** (default N=4), each `--bind 127.0.0.1` on its own
  HTTP + gossip port pair (`8420/9420`, `8421/9421`, …). Localhost only.
- **One committee genesis** (`dregg-node genesis --validators N`): N distinct
  Ed25519+ML-DSA validator keys sharing one `genesis.json`, federation_id
  = `derive_federation_id_hybrid_with_epoch(committee)`, BFT threshold
  `quorum_threshold(N)` (`node/src/genesis.rs`). A node identifies itself by
  matching its `node.key` against the committee in `genesis.json` — there is no
  index coupling (`node_index` is unused in `dregg_node::run`).
- **Peered mesh:** each node's `--federation-peers` lists the other N−1
  `127.0.0.1:<gossip_port>`. They blocklace-sync over QUIC; every node ends up
  with a byte-identical DAG.
- **Full mode + blocklace:** `--federation-mode full --consensus blocklace`.
  Finality is gated on quorum, not the local node.

## Quick start

```
scripts/federation-local.sh genesis     # roll a fresh 4-validator committee + data dirs
scripts/federation-local.sh up          # launch the 4 node processes
scripts/federation-local.sh status      # /status on every node (peer_count, latest_height, dag_height...)
scripts/federation-local.sh finality    # submit a turn to node0, watch it finalize on all 4
scripts/federation-local.sh heights 90  # sample latest_height across all 4 for 90s (watch them climb in lockstep)
scripts/federation-local.sh down        # stop the federation
scripts/federation-local.sh clean       # down + delete the run root
```

Config via env: `FED_N` (committee size), `FED_ROOT` (run root, default
`~/dregg-fed-local`), `FED_BIN` (binary path), `FED_HTTP_BASE`/`FED_GOSSIP_BASE`
(base ports), `FED_BIND` (default `127.0.0.1`).

## How to read the result

- **Federation formed:** each node's `/status` reports `peer_count = N−1`,
  `consensus_live = true`, `federation_mode = full`, and the DAG advances
  (`dag_height`, `block_count` climbing) identically across nodes.
- **Cross-node finality:** submit a faucet turn to node0. Its `turn_hash`
  receipt then appears in **`GET /api/receipts` on all N nodes**, and
  `latest_height` (the attested-root / committed-turn height,
  `node/src/api.rs` `get_status`; `+1` per finalized turn,
  `node/src/blocklace_sync.rs`) advances **identically on every node**. The
  turn was executed on node0, super-ratified by the committee over the
  blocklace, and its attested root replicated — that is BFT finality across the
  federation, not one node's say-so.

## Private-access model

- ⚠ **The HTTP API is localhost-only. The GOSSIP PORT IS NOT.** `--bind` (and so
  `FED_BIND`) governs only the axum HTTP listener. The QUIC gossip endpoint is
  bound at `node/src/blocklace_sync.rs:3556` as a hardcoded
  `format!("0.0.0.0:{gossip_port}")` — `--bind` is never consulted for it. So
  every node in this federation listens on `0.0.0.0:<gossip_port>` on every
  interface, whatever `FED_BIND` says. Measured 2026-08-08 on a 4-node run
  (`ss -ulpn` showed `0.0.0.0:19420..19423`; the node's own boot line reads
  `PeerNode started: … @ 0.0.0.0:19424` under `--bind 127.0.0.1`). **There IS a
  firewall exception to make**, or the box must not be network-reachable.
  Still leave `FED_BIND=127.0.0.1`: it keeps the *API* off the network, which is
  the part it can actually close.
  What limits the exposure is authentication, not the bind: `dregg_net::gossip`
  drops every envelope whose sender is not in the committee `peer_keys` registry
  ("unknown sender"). That is a real gate, but it is paid per envelope and it
  logs — one non-member peer produced 9,588 rejections (and ~7,300 WARN lines
  per node) in minutes, so an unauthenticated reachable gossip port is a log /
  CPU amplification surface even though it cannot inject.
- **Ephemeral committee.** `genesis` rolls fresh keys into `FED_ROOT` each run;
  the keys are devnet-grade (`.devnet` marker), never production.
- **Separate from any solo node.** This federation uses its own ports and its
  own `FED_ROOT` data dirs. It does not touch a solo private node on the box —
  run it on distinct ports (the defaults `8420+`/`9420+` are the federation's;
  point a solo node elsewhere).

## Honest scope

**What is real:** a genuine multi-node BFT federation. N distinct validators,
one committee, blocklace consensus over QUIC, quorum-gated finality. A turn
submitted to one node is finalized across the committee and its receipt +
attested-root height replicate cross-node. This is decentralized finalization,
not a single node.

**The caveats, named:**

1. **Marshal (un-verified) state producer.** The default binary is not
   Lean-linked, so it runs the un-verified Rust reference executor
   (`DREGG_ALLOW_UNVERIFIED_CONSENSUS=1`, `state_producer=rust`). Consensus and
   finality are real (blocklace BFT, quorum intersection, the tau ordering —
   `metatheory/Dregg2/Distributed/`) — but read caveat 3 before repeating
   "**proven**" about the tau ordering *on this harness*: the verified rule is
   the decider only on polls that meet a 2500 ms budget, and the same escape
   hatch named on this line is what lets a missed budget substitute the
   un-verified Rust twin; the **state transition
   function** committing each turn is the un-verified reference, not the
   Lean-shadowed verified kernel. For a verified-producer federation, build the
   Lean-linked node (`scripts/bootstrap.sh`, `docs/BUILD-LEAN-LINKED-NODE.md`)
   and drop the escape hatch. This is the standard devnet configuration, and it
   matches the prior LAN `n=4` run (`docs/STAGE5-N4-RESULT.md`).

2. **Run N ≥ 4, not N = 3.** At **N=3** the supermajority threshold is 3
   (unanimity) with **zero laggard slack**, so a single asymmetrically-delivered
   block stalls waves after the first and `latest_height` plateaus at 1
   (`docs/STAGE5-N4-RESULT.md`, `docs/STAGE5-DIAGNOSIS.md`). **N=4** gives each
   wave-closing round one node of slack (3-of-4, tolerates f=1) and finality
   streams. Safety holds at both (quorum intersection `2·3 − 4 = 2 > f`); the
   difference is **liveness**, and it is a deploy dial, not a code change.

3. **Finality-gate perf is O(history) under churn — and past a budget it stops
   being only a perf story.** The verified tau-order finality poll recomputes
   over the lace each poll; a cross-poll cache misses under continuous catch-up
   churn, so committed-turn throughput can fall below block production and
   `latest_height` *crawls* (`docs/CROSS-MACHINE-FINALITY-FINDING.md`,
   `docs/VERIFIED-GATE-PERF.md`).

   ⚑ **CORRECTED 2026-08-08. This used to end "a performance ceiling …, not a
   safety defect."** That is not true of *this script's* configuration. The
   verified FFI is bounded by a per-poll wall-clock budget
   (`DREGG_FINALITY_ORDER_TIMEOUT_MS`, default **2500 ms**), and because
   `federation-local.sh:86` sets `DREGG_ALLOW_UNVERIFIED_CONSENSUS=1`
   unconditionally, a poll that misses the budget **hands the finalized order to
   the un-verified Rust `ordering::tau` twin.** Over-budget warnings were
   observed on an *idle* 4-node committee at `lace_size` 773–981 — i.e. within
   an hour or so of ordinary running, not at some exotic scale. Past that point
   the ordering on this harness is un-verified more often than not, so the
   claim in caveat 1 stops applying and the degrade is a *correctness-surface*
   change, not a throughput one.

   Check which order actually decided, rather than assuming: `/status` reports
   `consensus_order`, `consensus_order_budget_ms`, and
   `consensus_order_{verified,unverified,failed_closed,over_budget}_polls`. A
   non-zero `consensus_order_unverified_polls` means this run did not finalize
   over the verified ordering throughout.

   (A Lean-linked node *without* the escape — the deployed PoA posture — fails
   CLOSED instead: the poll finalizes nothing. Same trigger, opposite failure.)

**Closed (formerly caveat 4): full-mode restart recovery.** A full-mode node
persists a genuine committee quorum with each finalized root: `FinalizationVote`
v2 binds the finalized `merkle_root` into the vote, the `VoteCollector` retains
the signature bytes, and the ≥threshold quorum is persisted into the root's
`finalization_quorum` (back-filled a gossip round or two after the synchronous
commit when peer votes trail — a deliberate liveness cost, never a block on
gossip). On restart the recovery anchor accepts
`verify_signatures || verify_finalization_quorum`
(`node/src/blocklace_sync.rs`; pinned by
`dregg_persist::tests::full_mode_single_sig_root_is_refused_genuine_quorum_accepted`
and `committee_node_restarts_cleanly_with_finalization_quorum`; design record:
`docs/HANDOFF-committee-restart-fix.md`, Fix B).

**Bottom line:** N=4 private federation with real cross-node BFT finality
(marshal producer), streaming steadily on a fresh box — a genuine
decentralization step past the solo node, with the verified-producer upgrade and
the perf items named and tracked.
