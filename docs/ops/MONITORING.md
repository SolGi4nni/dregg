# MONITORING — the signals, what each alert means, and the stack

The node self-exposes Prometheus metrics at `GET /metrics`
(`node/src/api.rs:1803` → `node/src/metrics.rs`); `deploy/observability/`
scrapes, alerts, and renders them. This doc is the *meanings*; the triage
commands live in [INCIDENT-RESPONSE.md](INCIDENT-RESPONSE.md).

## Run the stack

```sh
# on the box (nodes bind loopback, so the stack runs host-network):
rsync -a deploy/observability/ box:/opt/dregg-observability/
ssh box 'cd /opt/dregg-observability && GRAFANA_ADMIN_PASSWORD=<strong> \
  docker compose -f docker-compose.observability.yml up -d'
# view (everything binds 127.0.0.1 — tunnel in):
ssh -L 3000:127.0.0.1:3000 box     # Grafana → http://localhost:3000
```

Dashboards provisioned: **dregg · Consensus**, **dregg · Protocol**,
**dregg · Security**, **dregg · Host Overview**.

## The signal families (all from `node/src/metrics.rs`)

- **Liveness / consensus**: `dregg_block_height`, `dregg_mempool_pending`,
  `dregg_consensus_attested_total`, `dregg_consensus_finality_latency_seconds`,
  `dregg_federation_peers_connected`, `dregg_blocklace_{depth,frontier}`,
  `dregg_validator_votes_total{voter}`,
  `dregg_validator_last_seen_timestamp_seconds{voter}`.
- **Correctness tripwires**: `dregg_consensus_differential_divergence_total`
  (rust↔lean disagreement — MUST stay 0), `dregg_tau_prefix_shifts_total`
  (reorg/prefix churn).
- **Throughput**: `dregg_turns_{submitted,executed{status},rejected}_total`,
  `dregg_turn_execution_duration_seconds`,
  `dregg_proofs_verified_total{result=valid|invalid|error}`,
  `dregg_async_proofs_total{result=completed|failed|dropped}`.
- **Security counters** (flat is good):
  `dregg_auth_failures_total`, `dregg_cap_refusals_total`,
  `dregg_sandbox_denials_total`, `dregg_revocations_total`,
  `dregg_gossip_stream_rejected_total{peer,reason}`.
- **Host**: node_exporter (CPU/mem/disk/OOM).

## The alerts (`deploy/observability/prometheus/rules/dregg.rules.yml`)

**page** = wake someone; **warn** = look soon. Routing + the 10-minute page
re-fire live in `deploy/observability/alertmanager/alertmanager.yml`; by
default every alert also lands in the local `alert-sink` log container.

| Alert | Sev | Fires when | First move |
|---|---|---|---|
| ConsensusDivergence | page | rust↔lean divergence counter > 0 | INCIDENT-RESPONSE §5 — treat as a consensus bug, snapshot logs now |
| NodeDown | page | a node's /metrics unscrapeable 2m | `systemctl status dregg-gateway` / `dregg-node@N` |
| NodeNotFinalizing | page | mempool has turns, attestations flat 10m | quorum check — every member's `/status` (INCIDENT-RESPONSE §1) |
| ValidatorSilent | warn | no vote from a member >10m | that member's box/gossip; at n=3, one silent member halts finality |
| HeightNotAdvancing | warn | submissions but flat height 30m | finality stall triage |
| GossipStreamRejectionRate / Storm | warn / page | inbound stream rejects >0.5/s / >5/s | identify peer via `{peer,reason}`; INCIDENT-RESPONSE §3 |
| TauPrefixShifts | warn | prefix churn observed | watch; correlate with membership/epoch events |
| TurnRejectSpike / AuthFailureSpike / CapRefusalSpike | warn | >20 refusals in 10m | Security dashboard — probe vs broken client |
| SandboxDenials | warn | confined code hit its cage | inspect the workload |
| AsyncProofFailures / InvalidProofSubmissions | warn | proving pool failures / invalid proofs submitted | prove-pool logs; a submitter probing verification |
| HostExporterDown / HostDiskAlmostFull / HostDiskCritical / HostMemoryPressure / HostOOMKill | warn/page | host health | free disk (old logs, `cargo clean` in /opt/dregg), grow the volume |

## Known gaps (named, with the closure shape)

- **No bridge-conservation page.** The operated layer's single most important
  page (`BridgeConservationBreach`) read an ops-aggregator field that does not
  exist natively. Closure: emit a `dregg_bridge_conservation_ok` gauge from the
  bridge crate onto `/metrics`, then resurrect the rule (one alert block).
- **Single-box scrape config.** Other operators' nodes/hosts join by adding
  targets to `deploy/observability/prometheus/prometheus.yml`.
