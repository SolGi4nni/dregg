# docs/ops — operator runbooks for the native deploy

The first-responder + lifecycle runbooks for operating dregg's boxes. The ground
truth on **what actually runs where** is [`deploy/README.md`](../../deploy/README.md)
(the three boxes: the AWS edge — a docker compose stack, the tailnet's public
exit; hbox — build/prove + systemd user units; persvati — build/test) and
[`deploy/PRACTICES.md`](../../deploy/PRACTICES.md). Every command here is the
native one; nothing references the dead operated fabric.

> ⚠ A prior version of this set was grounded on a `deploy/aws` topology (an
> always-on gateway node behind Caddy, in-box federation members `dregg-node@N`,
> systemd units built on the box). **That topology never ran** — it is
> quarantined in [`deploy/aws/SUPERSEDED/`](../../deploy/aws/SUPERSEDED/), and
> `deploy/aws/README.md` describes the box as it is. Where a runbook below still
> reaches for a `deploy/aws/*.sh` script, the script lives only under
> `SUPERSEDED/` and the live procedure is `deploy/aws/README.md`'s
> build-elsewhere-ship-the-image flow.

## The set

| Runbook | Covers |
|---|---|
| [MONITORING.md](MONITORING.md) | what each signal/alert means + running the `deploy/observability/` stack |
| [INCIDENT-RESPONSE.md](INCIDENT-RESPONSE.md) | symptom → diagnostic commands → cause → fix (the triage trees) |
| [DISASTER-RECOVERY.md](DISASTER-RECOVERY.md) | lost keys, store corruption, lost box, re-sync |
| [KEY-MANAGEMENT.md](KEY-MANAGEMENT.md) | credential lifecycles + what each rotation costs |
| [PAYMENTS-GO-LIVE.md](PAYMENTS-GO-LIVE.md) | the native `$DREGG`/USDC payment rail — devnet→mainnet go-live, custody contract, treasury refuel, the deferred signer-gated edges |
| [DISCORD-BOT.md](DISCORD-BOT.md) | running the bot frontend (env, hbox deploy, the paid-run flow, monitor, keys) |
| [PRIVATE-NODE.md](PRIVATE-NODE.md) | the private-deployment foundation — a single verified `dregg-node` on hbox, bound localhost/LAN (never public), executing real turns; `scripts/private-node.sh` start/stop/check |
| [OPS-RUNBOOK.md](OPS-RUNBOOK.md) | hosting the DrEX/launchpad testnet demos (groundwork; go-live ember-gated) |
| [DEPLOY-SOLANA-COSMOS-TESTNET.md](DEPLOY-SOLANA-COSMOS-TESTNET.md) | one-broadcast deploy of the Groth16 settlement verifier to Solana devnet + a CosmWasm testnet |
| [regenerating-verifiers.md](regenerating-verifiers.md) | regenerating the three cross-chain verifier constants (EVM/Solana/Cosmos) from the one canonical spec |

**Upgrades:** the former UPGRADE.md is superseded — it drove
`deploy/aws/SUPERSEDED/update-gated.sh`, a script for the never-ran topology.
The live update path is
`deploy/aws/README.md` § "Updating: build elsewhere, ship the image" (build on
persvati/hbox, `docker save | docker load`, recreate one service) plus
`deploy/PRACTICES.md`. The old doc is retained at
[`docs/SUPERSEDED/UPGRADE.md`](../SUPERSEDED/UPGRADE.md).

Companions elsewhere in the tree:

- `deploy/README.md` + `deploy/PRACTICES.md` — the verified what-runs-where map
  and the box-handling rules. Read these first.
- `docs/OPERATOR-ONBOARDING.md` — fold a new node/validator into a federation
  (the `gen-validator-key` / `join` / `add-validator` dance) — this IS the
  committee-change runbook's core.
- `deploy/observability/README.md` — the Prometheus/Grafana/Alertmanager stack.
- `deploy/aws/SUPERSEDED/N3-RUNBOOK.md` — the 3-member-devnet bring-up for the
  never-ran topology; quarantined, kept for the reasoning inside, not
  instructions.

## What was deliberately NOT ported (dead-by-design)

The operated layer's runbooks for its own fabric have no native referent and
were dropped, not lost: `MESH.md` + headscale/WireGuard overlay operations
(native peers over public QUIC + security groups; overlay joins are a
per-federation deployment concern — `docs/OPERATOR-ONBOARDING.md`),
`HARDWARE-PERSVATI.md` + thermal tuning (no operated compute box),
`STRIPE-SETUP/OPS.md` (superseded — the native rail is the `$DREGG`/USDC
`dregg-pay` rail; see PAYMENTS-GO-LIVE.md, not Stripe), `OPS-DASHBOARD.md` (the
operated layer's ops aggregator; the native pane is Grafana — MONITORING.md),
and `SECRETS.md`'s edge-box `.env` conventions (native secrets live in
`/etc/dregg/*.env` + the `secrets/` crate's local store; see KEY-MANAGEMENT).
The originals remain readable in the private operated-layer tree (reference
only).
