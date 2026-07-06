# deploy/observability — Prometheus + Alertmanager + Grafana for dregg nodes

The monitoring/alerting stack for the `deploy/aws` topology, **ported from the
operated layer** (the prior operated layer) and **re-grounded on what
the native node actually emits** (`node/src/metrics.rs` → `GET /metrics`,
`node/src/api.rs:1803`). Nothing here references the dead operated fabric —
every PromQL expression names a real native series; every dropped piece is
listed below with its reason.

## Contents

```
docker-compose.observability.yml   # prometheus + alertmanager + grafana +
                                   # node-exporter + alert-sink, ALL host-network,
                                   # ALL loopback-bound (SSH-tunnel to view)
prometheus/prometheus.yml          # scrapes 127.0.0.1:8420/8421/8422 + node-exporter
prometheus/rules/dregg.rules.yml   # 20 alerts (promtool-validated)
alertmanager/alertmanager.yml      # page/warn routing + NodeDown inhibit +
                                   # local alert-sink record (amtool-validated)
grafana/provisioning/              # datasource + dashboard provider
grafana/dashboards/                # dregg-{consensus,protocol,security,hosts}.json
```

Bring-up and alert meanings: **`docs/ops/MONITORING.md`**. Triage:
**`docs/ops/INCIDENT-RESPONSE.md`**.

## Design notes

- **Host networking, loopback everywhere.** The nodes bind `127.0.0.1`
  (`deploy/aws/dregg-node@.service`), so the scrapers live on the box's own
  network namespace, and every UI/API here also binds loopback. Nothing is
  exposed; `ssh -L 3000:127.0.0.1:3000` is the front door.
- **`GRAFANA_ADMIN_PASSWORD` is required** (`:?` in the compose) — the
  operated layer once leaked a baked-in Grafana credential into git history;
  this stack cannot repeat that.
- **Alerts always leave a local record.** The `alert-sink` echo container logs
  every webhook delivery (`docker logs dregg-obs-alert-sink-1`) even after a
  real paging sink is added to `alertmanager.yml`.

## Ported vs dropped (vs the operated layer's stack)

| Old piece | Here | Why |
|---|---|---|
| dregg_* node rules (divergence, gossip storm, tau shifts, reject spikes, host rules) | **ported** | the old stack already scraped THIS node's metrics; re-pointed + thresholds kept |
| NodeDown via blackbox probe | **ported as `up{job="dregg-node"}`** | no blackbox-exporter needed for loopback targets |
| NodeNotFinalizing / HeightNotAdvancing via ops-aggregator fields | **re-derived natively** (mempool-pending × flat attestations / submissions × flat height) | the `the operated layer's ops` json-exporter feed does not exist here |
| ValidatorSilent, AsyncProofFailures, InvalidProofSubmissions | **new** | native series the old rules never used |
| BackendDown, GatewayDown, PostgresConnectionPressure | dropped | operated-fabric services (persvati agent, machines gateway, pg outbox) — dead-by-design |
| BridgeConservationBreach | **dropped, owed** | its source was an ops-aggregator gauge; closure = emit `dregg_bridge_conservation_ok` from `bridge/` onto `/metrics`, then restore the rule (see `docs/ops/MONITORING.md` §gaps) |
| json-exporter, blackbox-exporter, thermal-exporter | dropped | their targets (ops `/api/health`, gateway `/status` JSON, persvati thermals) don't exist natively |
| 10 dashboards (incl. Cloud/Economy/Compute/Federation) | **4 rebuilt** (Consensus absorbs Federation's committee panels; Cloud/Economy/Compute had no native series) | dashboards must render real series or they are set dressing |
