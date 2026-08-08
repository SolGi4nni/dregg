# INCIDENT-RESPONSE — first-responder diagnostic trees

The page fired (or something looks wrong) and you are the first responder.
Symptom → exact commands → likely cause → fix → when to escalate. Grounded on
the real edge ([`deploy/aws/README.md`](../../deploy/aws/README.md)): one node,
the docker container `dreggnet-dregg-node-1` (image `dregg-node:n5`), binding
`0.0.0.0:8420` (HTTP) and `9420/udp` (QUIC gossip). No Caddy fronts it, and
there are no `dregg-gateway`/`dregg-node@N` systemd units — autostart is the
docker `restart:` policy. The multi-member trees below apply to any n-member
federation the software runs; the deployed edge is a single node. Signal
meanings: [MONITORING.md](MONITORING.md).

## The 30-second orient

```sh
# the node's own view (from the box):
curl -s http://127.0.0.1:8420/status | jq
#   → { healthy, peer_count, dag_height, latest_height, block_count,
#       consensus_live, federation_mode, ... }        (node/src/api.rs)
# on a multi-member federation, read EVERY member's /status the same way.

cd /opt/dreggnet && docker compose ps
docker logs --tail 50 dreggnet-dregg-node-1
```

The four fields that resolve most incidents: **`peer_count`** (did the mesh
form?), **`federation_mode`** (`full` vs `solo`), **`dag_height`** on each node
(do they agree?), **`consensus_live`** (is quorum finalizing?).

> `/status` deliberately withholds private-activity counters (the F-8
> hardening, `node/src/api.rs`); volume questions are answered by `/metrics`,
> not `/status`.

## 1. "The network won't finalize new turns" (NodeNotFinalizing)

**Symptom.** Turns submit but never finalize; `dag_height` flat;
`dregg_mempool_pending > 0` with flat `dregg_consensus_attested_total`.

Diagnose, in order:

- **(a) Is quorum possible?** Read every member's `/status`. The threshold is
  the strict supermajority `⌊2n/3⌋+1` (`federation/src/lib.rs`): **n=3 needs
  all 3** (f=0). One member down ⇒ the survivors *correctly refuse* to
  finalize — that is BFT safety, not a bug. Fix: bring the member's container
  back (`docker compose up -d --no-deps <member-service>` on its box; if its
  store is wedged → [DISASTER-RECOVERY](DISASTER-RECOVERY.md) §B).
- **(b) All up but `peer_count: 0`** — the mesh didn't form. Tell: each
  node's `dag_height` advances *independently* instead of converging. Check
  the gossip ports (`0.0.0.0:942x`, hard-fenced by the security group), each
  member's configured peer list, and
  `dregg_gossip_stream_rejected_total{reason}` for `unknown_sender` /
  `bad_signature` (a genesis/committee mismatch looks like this).
- **(c) `federation_mode: "solo"` unexpectedly** — the node started without
  its committee descriptor. Verify `genesis.json` is present in the data dir
  and identical (`sha256sum`) across members.
- **(d) A member is up, meshed, but silent** (`ValidatorSilent` fired) — read
  its logs: `docker logs --tail 100 <member-container>`. A crash-looping
  container shows in `docker compose ps` (restart count); a live-but-mute one
  is usually a key/committee mismatch (its votes are rejected — look for
  `bad_signature` rejects on the *other* members).

**Escalate** when all members are up, meshed, agreed on genesis, and
attestations are still flat — that is a consensus bug; snapshot every
member's logs before restarting anything.

## 2. "A node is down" (NodeDown)

```sh
cd /opt/dreggnet && docker compose ps          # restart count = crash loop
docker logs --tail 200 dreggnet-dregg-node-1
df -h /   # full disk is the classic silent killer
```

- **Crash loop with `STORE INTEGRITY EVENT`** → fail-closed store divergence,
  go to [DISASTER-RECOVERY](DISASTER-RECOVERY.md) §B. Do NOT delete anything
  before the backup step there.
- **Failed after a deploy** → roll back to the previous image tag: point the
  compose file back at it and `docker compose up -d --no-deps dregg-node`. The
  old tags on the box ARE the rollback path — never prune them (the deployed
  images are not currently reproducible from this repo; `deploy/README.md`
  TODO-7). Update discipline:
  [`deploy/aws/README.md`](../../deploy/aws/README.md).
- **OOM-killed** (`journalctl -k | grep -i oom`) → check `dregg_mempool_pending`
  growth and host memory; a container restart is safe (state is durable in the
  node's mounted data dir).

## 3. Gossip storm (GossipStreamRejectionRate / GossipStreamStorm)

The operated layer once lost its edge to a gossip storm with zero dashboard
visibility; the reject counter was added at every inbound stream-reject site.

```sh
curl -s http://127.0.0.1:8420/metrics | grep dregg_gossip_stream_rejected_total
```

- Identify the offender: the `{peer, reason}` labels (Security dashboard has
  by-peer and by-reason panels).
- `conn_limit` / `read_timeout` floods from one peer → fence that peer's IP at
  the security group (the native peer set is IP:PORT literals — the SG is the
  admission control), then investigate whether it is misconfigured or hostile.
- `unknown_sender` / `bad_signature` from a *committee* peer → genesis or key
  mismatch on their side; see tree 1(b).

## 4. Disk / host pressure (HostDisk*, HostMemoryPressure, HostOOMKill)

The usual space consumers on the box: journald, docker images, container logs.
(There is no build tree — nothing compiles on the edge.) In order:

```sh
sudo journalctl --vacuum-size=500M
docker image prune -f            # dangling layers only — see the warning below
```

⚠ Never `docker system prune -af` or delete `dregg-node:*` /
`dregg-discord-bot:*` tags: old tags are the only rollback path and the
deployed images are not currently rebuildable from this repo
(`deploy/README.md` TODO-7). Observability images (grafana/prometheus/…) are
re-pulled on `up` and are safe to prune. Never free space by touching the
node's data dir — that is chain state.

## 5. ConsensusDivergence fired (rust↔lean disagreement)

This is the one alert that means *implementation bug*, not operations. The
counter (`dregg_consensus_differential_divergence_total`) advances when the
Rust finality decision disagrees with the Lean model
(`node/src/finality_gate.rs`).

1. Snapshot everything now: `docker logs dreggnet-dregg-node-1 >
   /tmp/divergence-$(date +%s).log 2>&1` (every member's container on a
   multi-node federation), plus each `/status`.
2. Do not restart-to-green; the evidence is the point.
3. Escalate to a developer with the snapshot. The node's fail-closed behavior
   (which side won) is in the node's logs around the counter increment.

## 6. Turn-reject / auth-failure / cap-refusal spikes

`dregg_turns_rejected_total` counts every `TurnResult::Rejected`; the metrics
layer classifies auth vs capability (`node/src/metrics.rs`,
`RefusalClass`). A burst is either a probe (interesting, not urgent — the
gates held) or a broken client (find it before its operator finds you).
Correlate the spike window with the node's own logs — the node binds the
public port directly; there is no proxy layer with separate request logs.

Since 2026-08-08 it ALSO counts the other refusal population: turns that
consensus finalized and the application predicate then deterministically
refused before any mutation (`blocklace_sync::persist_finalized_payload_rejection`).
Those never touched a `TurnError`, so until then they moved no counter at all —
a turn could be unanimously discarded by a whole federation with
`dregg_turns_rejected_total` reading 0 on every member. The per-cause breakdown
is `dregg_finalized_turns_rejected_total{reason="…"}`; `receipt-chain-mismatch`
is the common one and means two turns raced for the same agent's receipt head
(the loser is refused; nothing is lost but that turn).

A client holding a `turn_hash` gets the verdict from
`GET /api/turn/{hash}/verdict`: `accepted` / `rejected` (with the reason and the
finalized block id) / `pending` / `unknown`. Reach for it before reading logs —
it is the same durable row the counter came from.
