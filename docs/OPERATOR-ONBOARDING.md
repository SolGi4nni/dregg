# Operator onboarding — add a node + validator to a federation

This is the **dance**: the small, repeatable set of commands an operator (or a
homelab) walks to fold a new `dregg-node` into a federation and — when the
federation operator admits it — turn it into a voting validator. It is the same
path pug's homelab nodes use, so it is built to be clean and reusable.

The overlay/WireGuard join, the container images, and the live topology live in
your federation's deployment runbook. **This** file is the dregg-side command
surface those runbooks call.

## The model (what a federation actually is)

A federation is a fixed **committee** of validator Ed25519 public keys.

- The `federation_id` is a *commitment to that committee*:
  `derive_federation_id_with_epoch(sorted_committee_pubkeys, committee_epoch)`
  (`federation/src/identity.rs`). Every node derives the same id from the same
  committee. **Adding, removing, or rekeying a member changes the
  `federation_id`** — so growing the committee is a *coordinated re-roll*, not a
  unilateral act.
- The committee lives in each node's `genesis.json` (`validators[].public_key` +
  the derived `federation_id` + `threshold`). A node cannot verify a
  federation's blocks — cannot even follow it — without that committee
  descriptor.
- A turn is **final** only once a BFT supermajority of the committee has signed a
  finalization vote. The threshold is the strict blocklace supermajority
  `quorum_threshold(n) = ⌊2n/3⌋ + 1` (`federation/src/lib.rs`):

  | n (committee) | threshold (votes to finalize) | f (faulty tolerated) |
  |---|---|---|
  | 1 | 1 | 0 — solo, no consensus |
  | 2 | 2 | 0 — both must be online + honest |
  | **3** | **3** | **0** |
  | 4 | 3 | 1 — survives one down/Byzantine |
  | 5 | 4 | 1 |

  Note n=3 is threshold **3** (f=0), not "2-of-3". Byzantine fault tolerance
  (`f≥1`) begins at n=4; resisting an *attacker* begins where independent
  operators hold enough of the committee that no single party controls `n − f`
  keys. That is why the target is 5 independent operators.

## The three verbs

All three are `dregg-node` subcommands (they operate on a node's data dir, keys,
and committee descriptor).

### 1. `gen-validator-key` — make (or read) this box's identity

```sh
dregg-node gen-validator-key --data-dir ~/.dregg
```

Generates `node.key` (a raw 32-byte Ed25519 seed, `0600`) if absent and prints
the **public** key. Idempotent: re-running on a box that already has a key just
re-prints its pubkey. Hand the printed PUBLIC key to the federation operator.

### 2. `add-validator` — the authority op (run by the federation operator)

```sh
# On a committee node's data dir (the operator's box), fold in one or more keys:
dregg-node add-validator --data-dir ~/.dregg \
  --pubkey <node-b-public-key-hex> \
  --pubkey <node-c-public-key-hex>
```

Reads `genesis.json`, folds the pubkey(s) into the committee, **recomputes the
`federation_id` + `threshold`** (the exact derivation the node uses), and writes
the new descriptor back to `genesis.json` plus a content-named sibling
`genesis-<id8>.json` to distribute. Malformed keys, non-Ed25519 keys, and
"nothing to add" (all keys already present) are clear refusals.

> **Authority.** Filesystem access to a committee node's data dir *is* the
> authority — there is deliberately **no remote self-admit** (that would defeat
> BFT: a node could vote itself in). The operator who controls the existing
> federation runs this.

The re-roll changes `federation_id`, so it is a coordinated act: distribute the
new `genesis.json` to **every** committee node (each keeps its own `node.key`)
and restart them.

### 3. `join` — peer, sync, follow / vote

```sh
dregg-node join --bootstrap <bootstrap-overlay-ip>:9420 \
  --data-dir ~/.dregg --bind <this-node-overlay-ip>
```

Pre-flights the data dir (auto-generates `node.key` if absent, printing the
pubkey), **requires a committee `genesis.json`** to be present (it refuses, with
the exact next steps, rather than start a node that trusts nobody), then starts
the daemon in full (BFT-quorum) mode peered to the bootstrap. The blocklace
catches up the DAG from the bootstrap; if this node's key is **in** the committee
it casts finalization votes, otherwise it syncs as a **follower** and
auto-proposes membership (`propose_join_if_needed`) until an operator admits it.

- `--bind` should be the box's **overlay IP** (your private overlay address) so authorized
  peers can sync. **Not** `127.0.0.1` (loopback-only — peers can't reach it) and
  **not** `0.0.0.0` (exposes every interface — red-team MESH-2). `join` warns if
  you pass `0.0.0.0`.
- One live bootstrap peer is enough; gossip-of-peers fills in the rest of the
  mesh.

## The full dance — growing a 1-node committee to 3

Three independent boxes on the overlay (node-A the existing committee/bootstrap,
node-B and node-C joining):

1. **Keys.** On node-B and node-C: `dregg-node gen-validator-key`. Each sends
   its PUBLIC key to the operator.
2. **Admit (operator, on a committee node).** `dregg-node add-validator --pubkey
   <node-b> --pubkey <node-c>` → a 3-member committee, **threshold 3** (f=0), a
   new `federation_id`. This emits the descriptor `genesis-<id8>.json`.
3. **Distribute.** Copy the new `genesis.json` to node-B's and node-C's data
   dirs (each keeps its own `node.key`). For a box that can't reach a committee
   node's read API (loopback-only), hand it the descriptor out of band.
4. **Join + restart.** On node-B and node-C:
   `dregg-node join --bootstrap <bootstrap-overlay-ip>:9420 --bind <overlay-ip>`.
   Restart node-A into full mode with the new genesis and its own `--bind`.
5. **Verify.** Each `/status` shows `federation_mode: full`, the new
   `federation_id`, `peer_count` rising to 2 (each sees the other two), and they
   converge to the same `dag_height`. A faucet/transfer turn submitted on one
   node finalizes and becomes visible (same `state_commitment`) on the others —
   cross-node deterministic finality.

## Honest live state + the operator gate

- The **CLI dance** (`gen-validator-key`, `add-validator`, `join`) is built,
  tested (`node/src/operator_join.rs`), and reusable for the homelab.
- Binding the read API to the overlay is a run flag (`--bind <overlay-ip>`), not
  a code change — overlay-only, never `0.0.0.0`.
- **Validator-adds are gated on the federation operator.** Admitting a new box
  means running `add-validator` on a committee node (which requires operator
  access to that box) and a coordinated restart. Until then, a joining box syncs
  as a follower and auto-proposes membership; it anchors no finality. This gate
  is by design — BFT membership is not self-grantable.

## Reboot / recovery

`restart: unless-stopped` (docker) or a systemd unit brings the daemon back on
boot. A committee node rejoins by **catch-up**: clear its `dregg.redb` (keep
`genesis.json` + `node.key`) and restart; it re-seeds genesis, re-peers, and
replays the finalized DAG from the quorum, re-deriving the exact finalized state.
See your federation deployment runbook for the durable-state caveat below the
first ledger checkpoint (the recovery-order fix landed in `node/src/main.rs`).
