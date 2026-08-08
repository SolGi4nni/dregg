# Joining a federation — live, no genesis re-roll

> ⚠ **THE FLOW ON THIS PAGE DOES NOT REACH THE COMMITTEE TODAY (measured 2026-08-08, 4-node run).**
> A candidate's Join proposal is authored and gossiped, and every committee member **drops it at the
> transport** before any membership code sees it: `dregg_net::gossip` resolves a signed envelope's
> `sender` in the `peer_keys` registry and refuses anything it cannot find ("unknown sender"). That
> registry is seeded from the genesis committee (`node/src/blocklace_sync.rs:3598`) and extended in
> exactly one place — `apply_committee_change` step 3, *after* the committee already advanced
> (`node/src/blocklace_sync.rs:2536`). **A non-member's key enters the mesh only once it is a member,
> and it can only become a member via a block the mesh refuses.**
>
> What that looks like in practice: `join` logs `proposed join to federation (awaiting threshold
> approvals)`, and `GET /api/membership` then reports `participants=4, proposals=0` on **every** node
> **including the joiner itself**, indefinitely. The joiner establishes QUIC links to all peers,
> receives their frontiers, and stays at `dag_height=1, latest_height=0` — while `GET /status` on it
> reports **`"healthy": true`**. The only committee-side signal is a `WARN` flood
> (~7,300 lines/node in 3 minutes) and `dregg_gossip_stream_rejected_total{reason="unknown_sender"}`.
> `--auto-approve-joins` cannot help: no Join block ever arrives to approve.
>
> Until the joiner's key can be admitted to the gossip mesh *before* it is a committee member, the
> working path to add a validator is the genesis re-roll (`add-validator`, bottom of this page) with
> a coordinated restart. Everything below describes the intended design, not current behaviour.

A dregg federation admits a new validator as an **on-chain operation**: the
candidate proposes, the current committee's quorum approves, and the running
committee advances at the next wave boundary. The chain keeps advancing
throughout; the `federation_id` does not change, so bots, bridges, and light
clients never re-point; nobody restarts anything. This page is the complete
walk for both sides of that handshake.

The machinery underneath: `MembershipAction` blocks in the blocklace →
quorum-gated constitution amendment (`ConstitutionManager`, proven by
`metatheory/Dregg2/Distributed/MembershipSafety.lean`) → the live committee
advance (`blocklace_sync::apply_committee_change`). Amendments are derived
from the chain again on every boot (`node/src/committee_replay.rs`), so an
admitted validator survives every restart of every node.

## What a joiner does

1. **Make a validator key** (idempotent; prints your public key):

   ```sh
   dregg-node gen-validator-key --data-dir ~/.dregg
   ```

2. **Get two things from any current operator** (chat, email — this data is
   public; the authority is in the committee's votes, not in the transport):
   - the federation's `genesis.json` — the ORIGINAL committee descriptor;
     it stays valid forever because the `federation_id` is stable across
     membership changes. Put it in your data dir.
   - a live bootstrap peer address, `host:9420`.

3. **Join:**

   ```sh
   dregg-node join --bootstrap <host>:9420 --data-dir ~/.dregg
   ```

   The node syncs the blocklace from the bootstrap and, seeing that its key is
   not in the committee, **auto-proposes its own membership** on-chain
   (`propose_join_if_needed`). It then follows the chain as a verifying
   non-voting node until admitted.

4. **Watch your proposal:**

   ```sh
   curl -s localhost:8420/api/membership
   ```

   Your proposal appears under `proposals[]` with its tally
   (`approvals`/`required`). When it reaches the current committee's quorum,
   `participants` grows by your key, `constitution_version` bumps — and your
   node's finalization votes start counting from the next wave. Nothing to
   restart.

## What each committee operator does

1. **See what is pending** (on your own node):

   ```sh
   curl -s localhost:8420/api/membership
   ```

   Each entry carries the `proposal_block` id, the candidate key, and the live
   tally. Verify out-of-band that the key belongs to the person you think it
   does — your approval IS the authority.

2. **Approve:**

   ```sh
   dregg-node approve-membership --proposal <proposal_block-hex>
   ```

   (Or `curl -X POST localhost:8420/membership/approve -d
   '{"proposal_block":"<hex>"}' -H 'content-type: application/json'`, with
   `-H 'authorization: Bearer <token>'` if the node has a passphrase.)

   This casts YOUR node's vote as an on-chain block. When a quorum of the
   CURRENT committee (`⌊2n/3⌋+1`: n=3→3, n=4→3, n=5→4, n=6→5, n=7→5) has
   approved, every node applies the amendment and advances its live committee.

An operator can also open the proposal on a candidate's behalf (the candidate
still runs `join` afterward):

```sh
dregg-node propose-epoch-transition --add <candidate-pubkey>
```

The same verbs do removal and rotation: `--remove <pubkey>`,
`--rotate <old> <new>` — each is a proposal the committee's quorum must pass.

## Semantics worth knowing

- **`federation_id` is stable.** It commits to the GENESIS committee + epoch
  and is deliberately left unchanged by live amendments — it is the chain
  root that bots, bridges, and light clients pin. The current committee is a
  DERIVED quantity: genesis + every finalized amendment.
- **Restarts are safe.** On boot a node re-derives the committee (and any
  in-flight proposal tallies) from its persisted chain and anchors recovery
  against the committee that actually signed each attested root — an admitted
  validator never reverts to "unknown" because someone rebooted.
- **Proposing is not authority.** Anyone can put a Join proposal on-chain;
  only CURRENT participants' approval votes count, and the quorum rule is the
  same supermajority that finalizes blocks.
- **Devnet shortcut.** `--auto-approve-joins` (or a `.devnet` marker) makes a
  node approve every Join automatically. Never in production — any peer could
  then grow the committee.
- **Partition freeze.** If most of the committee times out at once, membership
  changes freeze until activity resumes (`membership_frozen` in
  `GET /api/membership`) — a partition cannot vote itself a new committee.

## The old way: `add-validator` (genesis re-roll)

`dregg-node add-validator` rewrites `genesis.json` with a new committee,
which CHANGES the `federation_id` and requires distributing the new descriptor
to every node and restarting all of them into a fresh chain identity. It
remains the right tool for exactly two situations: **bootstrapping** a brand
new federation's first committee, and **disaster recovery** when the chain
itself is lost. For everything else, use the live path above.

## Troubleshooting

- `POST /membership/approve` → 409 "not a current committee participant":
  your node's key is not in the committee — only members admit members.
- 409 "unknown membership proposal": the proposal block has not finalized on
  your node yet (sync lag). Check `GET /api/membership`; it appears once your
  node's finality catches up.
- 409 "already applied": the quorum was reached before your vote; the
  committee already advanced. Nothing to do.
- 401/403 on the POST: the node has a passphrase — pass
  `--token <bearer>` / the `authorization: Bearer` header.
- The joiner's proposal never appears: confirm the joiner's node is actually
  syncing (`curl -s localhost:8420/status` on the joiner — `dag_height` must
  climb) and that its `genesis.json` matches the federation
  (`federation_id` in `GET /api/membership` on both sides must agree).
