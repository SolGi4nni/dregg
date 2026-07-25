# Migrating the edge off AWS — the runbook

Written 2026-07-25, against `deploy/README.md`'s observed state. Every step that
exists because of a past incident says which one.

**The rule that governs the whole migration:** DNS moves **last**. Bring the new
boxes all the way up, verify them, and only then point a name at them. A name
pointed at a half-built box is an outage you announced.

---

## 0. Before you start

You need:

- a **Hetzner Cloud** project + API token (Security → API tokens, read/write)
- a **reusable, non-ephemeral tailscale auth key** for tailnet A (the
  `100.64.0.x` one the edge is the exit for) — <https://login.tailscale.com/admin/settings/keys>
- your SSH public key
- the current AWS box still **running** — we do not touch it until step 6

Put the secrets in `deploy/edge/tofu/terraform.tfvars` (gitignored) or export
them as `TF_VAR_hcloud_token` / `TF_VAR_tailscale_authkey`.

---

## 1. Provision

```bash
cd deploy/edge/tofu
tofu init
tofu plan          # read it. two servers, one network, one firewall, one floating IP.
tofu apply
tofu output dns_records   # keep this — step 5 needs it
```

Two boxes come up: **workhorse** (services, disposable) and **anchor** (the exit
node + the DNS target, deliberately boring). The floating IP attaches to the
anchor and is what DNS will eventually point at — so rebuilding the anchor later
never moves a name.

## 2. Approve the exit node

`--advertise-exit-node` proposes; a human approves. In the tailscale admin
console, approve `dregg-anchor` as an exit node, then:

```bash
ssh root@$(tofu output -raw anchor_ip) 'tailscale status'
```

> **Why this is its own step:** on the old edge the exit node and the services
> were one box, and `deploy/aws/README.md` carries a shouting warning that
> stopping it "cuts the exit for every peer." Here the exit lives alone. Confirm
> it works *before* anything depends on it.

## 3. Recover the truth of what runs

`deploy/edge/compose/docker-compose.yml` in this repo was written from
`deploy/README.md`'s **observed** table (node + discord-bot + observability),
not from the ancestor compose — which is a superset defining
postgres/gateway/caddy/headscale that were never actually up.

Before trusting it, diff against the live box:

```bash
# on the AWS box (EC2 Instance Connect recipe in deploy/aws/README.md)
cat /opt/dreggnet/docker-compose.yml
docker ps --format '{{.Names}}\t{{.Image}}\t{{.Ports}}'
```

Reconcile any difference **into the repo file**, not into a copy on a box. That
reconciliation *is* TODO-4 being closed. If something is running that this file
does not describe, the file is wrong — fix it here.

## 4. Ship images and bring services up

**Never build on these boxes.** persvati (CPU) and hbox (GPU) build; images ship.

```bash
ssh persvati 'cd ~/dregg-build/<lane> && cargo build --release -p dregg-node'
# ...docker build there, then:
docker save dregg-node:next | gzip | ssh root@$WORKHORSE 'gunzip | docker load'

scp -r deploy/edge/compose/* root@$WORKHORSE:/opt/dregg-edge/
ssh root@$WORKHORSE 'cd /opt/dregg-edge && docker compose up -d'
ssh root@$WORKHORSE 'cd /opt/dregg-edge && docker compose ps'
```

Note the **bot is profile-gated** (`--profile bot`) and stays down for now —
see step 6.

## 5. Point DNS

Only now. Use `tofu output dns_records`; TTL 300 while wiring.

```
dregg.gg.   300  IN  A    <floating ip>
```

Verify TLS issues (Caddy does ACME on first request):

```bash
curl -I https://dregg.gg/
```

## 6. Move the bot — carefully

> ⚠ **ONE TOKEN, ONE BOT.** Two running bots means every command fires twice.
> This is TODO-2 and the failure mode is loud and embarrassing.

```bash
# 1. STOP the old one first, and confirm it is stopped.
ssh <aws> 'docker stop dreggnet-dreggnet-discord-bot-1 && docker ps | grep -c discord'
# 2. Only then:
ssh root@$WORKHORSE 'cd /opt/dregg-edge && docker compose --profile bot up -d'
```

## 7. Cut over, then wait

- Confirm the node is reachable: `curl -fsS http://<floating ip>:8420/health`
- Confirm peering works over UDP 9420 (a TCP-only check will lie to you).
- Leave the AWS instance **stopped, not terminated, for one week.** The EIP is
  elastic and survives a stop, so rollback is a start-and-repoint.
- After a clean week: terminate, release the EIP, and delete this paragraph.

---

## What this migration deliberately fixes

| was | now |
|---|---|
| **TODO-4** — the compose stack existed only on the box, "one `rm` from gone" | declared in `deploy/edge/compose/`, diffable, in git |
| **TODO-2** — the Discord bot ran on the box whose job is being a network exit | its own service on the workhorse, profile-gated so it cannot double-start |
| exit node and services shared one box; stopping it cut the tailnet for everyone | split: rebuilding the workhorse never touches the exit |
| a node `--data-dir` on `mktemp`, ledger permanently lost | `/var/lib/dregg/node`, declared in cloud-init and in the compose |
| no TLS terminator despite the ancestor compose defining one | Caddy, with automatic ACME and the CAA record to authorize it |

## What it does NOT fix

- **TODO-3** — hbox is still both the GPU prove box and the live games host. The
  workhorse has the headroom to take the games funnel, but moving it is its own
  change with its own verification, and doing it inside a host migration would
  make two failures indistinguishable. Do it next, separately.
- The **two-tailnet** split is unchanged: edge-side (`100.64.0.x`) and
  hbox-side (`skunk-emperor.ts.net`) still cannot reach each other, and persvati
  is still the only box on both. Any plan that assumes otherwise is false at the
  network layer.
