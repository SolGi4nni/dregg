# DISASTER-RECOVERY — lost keys, corruption, restore, re-sync

The worst-case runbook: a validator key is gone, a node's store is corrupt, a
box is lost, or a node's ledger diverged from the committee. For each: what is
recoverable, what is not, and the procedure — ported from the operated layer's
recovery runbook (which ran these procedures live) and re-grounded on the
native layout (`/opt/dregg-data*`, systemd units, `dregg-node` subcommands).

The load-bearing fact that makes recovery sound: the blocklace is a CRDT — a
node rejoins by **pulling the finalized DAG from the quorum and unioning it**
(`node/src/blocklace_sync.rs`, `node/src/catchup.rs`), re-deriving the exact
finalized state. As long as **quorum is live**, a single node's local store is
disposable: wipe it, restart, re-sync.

> **Golden rule: BACK UP before you destroy.** `cp -a` the data dir before any
> `rm`. Recovery is a re-derivation; a backup is your only undo if the
> re-derivation surprises you.

The three artifacts in a data dir, and their disposability:

| artifact | what | disposable? |
|---|---|---|
| `node.key` | the validator's Ed25519 identity | **NO** — losing it costs a committee change |
| `genesis.json` | the committee descriptor | re-obtainable from any member |
| the store (redb) | the local ledger/DAG | YES while quorum is live (re-sync) |

## A. Lost / compromised validator key (`node.key`)

The **public** half sits in `genesis.json` and defines the validator's
committee slot (and contributes to `federation_id`) — so key loss is never a
local-only fix.

**LOST (no backup):**
1. That validator identity is unrecoverable; the committee still expects its
   signatures.
2. Generate a fresh identity on the box:
   `dregg-node gen-validator-key --data-dir /opt/dregg-data` (idempotent;
   prints the public key — `node/src/main.rs`, `GenValidatorKey`).
3. Replace the old member with the new key — two native paths
   (`docs/OPERATOR-ONBOARDING.md`):
   - **live epoch path** (preferred, no downtime):
     `dregg-node propose-epoch-transition --rotate <old-pub> <new-pub>` — the
     quorum-gated on-chain membership change (`MembershipSafety.lean` gates
     it; no genesis re-roll).
   - **offline re-roll**: regenerate `genesis.json` with the new committee
     (`add-validator`), distribute to every member, coordinated restart. New
     `federation_id`.
4. While keyless, the box can still run as a **follower** (it pulls + unions
   the finalized DAG); it just cannot vote.

**COMPROMISED (leaked / touched a shared surface):** treat as burned —
scrubbing is not enough. Same procedure as LOST, but the rotation is *urgent*:
until the old key is evicted, its holder can equivocate as that validator (the
equivocation court will catch double-votes, but eviction is the fix).

**Backed up?** A non-event: restore `node.key` into the data dir, restart.
This is why [KEY-MANAGEMENT.md](KEY-MANAGEMENT.md) §backup exists.

## B. Store corruption / STORE INTEGRITY EVENT

**Symptom.** On restart the node fail-closes (a reconstructed root does not
match the durably recorded finalized root) and crash-loops under
`Restart=always`. This is **fail-closed by design** — the node refuses to
serve a divergent ledger.

**Procedure — wipe the ledger, keep identity + committee, re-sync:**

```sh
sudo systemctl stop dregg-node@N          # or dregg-gateway
sudo cp -a /opt/dregg-data-N /opt/dregg-data-N.bak.$(date +%s)   # BACK UP FIRST
# keep node.key + genesis.json; remove ONLY the store files:
sudo find /opt/dregg-data-N -maxdepth 1 -type f ! -name node.key ! -name genesis.json -delete
sudo systemctl start dregg-node@N
# watch it re-sync from quorum:
watch -n2 'curl -s http://127.0.0.1:842N/status | jq "{dag_height, peer_count, consensus_live}"'
```

`dag_height` climbs as the DAG unions in; the node resumes voting when caught
up. If the *quorum itself* is not live, stop — you are in scenario D.

## C. Lost box

With backups of `node.key` + `genesis.json` (KEY-MANAGEMENT §backup):
provision a new box (`deploy/aws/setup.sh`), restore the two files into the
data dir, start the unit, let it re-sync (procedure B's watch loop). Without
a key backup: scenario A (LOST).

## D. Quorum itself lost (≥ n−⌊2n/3⌋ members' stores gone)

The un-fun one. The finalized DAG survives on ANY member or follower —
`cp -a` the healthiest surviving store, bring members up one at a time from
it, and verify they agree (`dag_height`, `federation_id`, and each
`/api/federations`) BEFORE re-opening the gateway to traffic. If literally no
store survives anywhere, the chain restarts from genesis: that is a product
decision, not an ops procedure — escalate to the humans who own the
federation.

## E. Bad deploy (not corruption)

A deploy that fails its health gate is [UPGRADE.md](UPGRADE.md)'s territory:
`deploy/aws/update-gated.sh rollback` restores the previous release's
binaries. Note the one thing binary rollback cannot undo: a
protocol-semantics bump that already rewrote durable state — that is why
UPGRADE.md stages such bumps on one member first.
