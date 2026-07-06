# INCIDENT-RESPONSE — first-responder diagnostic trees

The page fired (or something looks wrong) and you are the first responder.
Symptom → exact commands → likely cause → fix → when to escalate. Ported from
the operated layer's triage trees and re-grounded on the native `deploy/aws`
topology (gateway `:8420` + optional members `:8421/:8422`, all loopback-bound
behind Caddy; QUIC gossip on `:942x`). Signal meanings: [MONITORING.md](MONITORING.md).

## The 30-second orient

```sh
# each node's own view (loopback on the box):
curl -s http://127.0.0.1:8420/status | jq   # gateway
curl -s http://127.0.0.1:8421/status | jq   # node-2 (if enabled)
curl -s http://127.0.0.1:8422/status | jq   # node-3 (if enabled)
#   → { healthy, peer_count, dag_height, latest_height, block_count,
#       consensus_live, federation_mode, ... }        (node/src/api.rs)

sudo systemctl status dregg-gateway dregg-node@2 dregg-node@3 --no-pager | grep -E "●|Active"
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
  finalize — that is BFT safety, not a bug. Fix: bring the member back
  (`sudo systemctl restart dregg-node@N`; if its store is wedged →
  [DISASTER-RECOVERY](DISASTER-RECOVERY.md) §B).
- **(b) All up but `peer_count: 0`** — the mesh didn't form. Tell: each
  node's `dag_height` advances *independently* instead of converging. Check
  the gossip ports (`0.0.0.0:942x`, hard-fenced by the security group), each
  member's peer list in `/etc/dregg/node-N.env`, and
  `dregg_gossip_stream_rejected_total{reason}` for `unknown_sender` /
  `bad_signature` (a genesis/committee mismatch looks like this).
- **(c) `federation_mode: "solo"` unexpectedly** — the node started without
  its committee descriptor. Verify `genesis.json` is present in the data dir
  and identical (`sha256sum`) across members.
- **(d) A member is up, meshed, but silent** (`ValidatorSilent` fired) — read
  its journal: `sudo journalctl -u dregg-node@N -n 100`. A crash-looping unit
  shows in `systemctl status`; a live-but-mute one is usually a key/committee
  mismatch (its votes are rejected — look for `bad_signature` rejects on the
  *other* members).

**Escalate** when all members are up, meshed, agreed on genesis, and
attestations are still flat — that is a consensus bug; snapshot journals
before restarting anything.

## 2. "A node is down" (NodeDown)

```sh
sudo systemctl status dregg-gateway --no-pager -l | head -30
sudo journalctl -u dregg-gateway -n 200 --no-pager
df -h /   # full disk is the classic silent killer
```

- **Crash loop with `STORE INTEGRITY EVENT`** → fail-closed store divergence,
  go to [DISASTER-RECOVERY](DISASTER-RECOVERY.md) §B. Do NOT delete anything
  before the backup step there.
- **Failed after a deploy** → `deploy/aws/update-gated.sh rollback` (restores
  the previous release's binaries and restarts; [UPGRADE.md](UPGRADE.md)).
- **OOM-killed** (`journalctl -k | grep -i oom`) → check `dregg_mempool_pending`
  growth and host memory; restart is safe (state is durable in
  `/opt/dregg-data*`).

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

The usual space consumers on the box: the build tree (`/opt/dregg/target`),
journald, docker images. In order:

```sh
sudo journalctl --vacuum-size=500M
docker system prune -af          # observability images are re-pulled on up
# the nuclear-but-safe one (next deploy rebuilds, slowly):
cargo clean --manifest-path /opt/dregg/Cargo.toml
```

Never free space by touching `/opt/dregg-data*` — that is chain state.

## 5. ConsensusDivergence fired (rust↔lean disagreement)

This is the one alert that means *implementation bug*, not operations. The
counter (`dregg_consensus_differential_divergence_total`) advances when the
Rust finality decision disagrees with the Lean model
(`node/src/finality_gate.rs`).

1. Snapshot everything now: `sudo journalctl -u dregg-gateway -u dregg-node@2
   -u dregg-node@3 > /tmp/divergence-$(date +%s).log`, plus each `/status`.
2. Do not restart-to-green; the evidence is the point.
3. Escalate to a developer with the snapshot. The node's fail-closed behavior
   (which side won) is in the journal around the counter increment.

## 6. Turn-reject / auth-failure / cap-refusal spikes

`dregg_turns_rejected_total` counts every `TurnResult::Rejected`; the metrics
layer classifies auth vs capability (`node/src/metrics.rs`,
`RefusalClass`). A burst is either a probe (interesting, not urgent — the
gates held) or a broken client (find it before its operator finds you).
Correlate the spike window with the gateway's request logs behind Caddy.
