# Joining a federation — live, no genesis re-roll

> ✅ **THIS FLOW WORKS (measured 2026-08-08, 4 committee processes + 2 joiners, real QUIC).** A
> candidate reached a live committee, was ratified, and `GET /api/membership` went
> `participants=4 → 5` on every node in 168 s, with the candidate then syncing the real chain
> (`dag_height` 57 → parity, `self.participant: true` on its own view). A second joiner asking to
> join a **different** federation was refused by name on every retry and never entered the mesh.
>
> **What it used to do, and what changed** — worth reading, because the shape of the bug is the
> shape of the fix. Until 2026-08-08 a candidate AUTHORED ITS OWN Join BLOCK and gossiped it, and
> that could not work by three independent mechanisms:
>
> 1. **The mesh.** `dregg_net::gossip` resolves an envelope's `sender` in the `peer_keys` registry
>    and refuses what it cannot find ("unknown sender"). That registry is seeded from the genesis
>    committee and extended in exactly one place — `apply_committee_change` step 3, *after* the
>    committee already advanced. A non-member's key entered the mesh only once it was a member.
> 2. **The roster.** Even admitted, the block would have been refused by
>    `Blocklace::receive_block_pinned` as an `UnenrolledCreator`: a creator's ML-DSA key is enrolled
>    only at boot (genesis committee) and in `apply_committee_change`. The same cycle, one layer down.
> 3. **The order.** Even ratified, it would have **halted finality on every node**. A member's
>    ML-DSA half came only from the genesis roster, `MembershipAction::Join` carried just an ed25519
>    key, and `project_committed_participants` drops an admitted member with no committed ML-DSA
>    key — at which point `poll_finalized_blocks` fails closed and finalizes nothing, forever.
>
> The fix does not open the mesh. A non-member may now send exactly **one** envelope kind — a
> self-certifying, size-capped, rate-limited **join request** that is not a block, never enters the
> lace, and registers nothing. A committee **member** validates it (both key halves proven) and
> authors the Join proposal **under its own key**, so no unenrolled creator is ever involved. And
> `MembershipAction::Join` now carries the candidate's ML-DSA-65 public key, which is committed on
> ratification — closing (3).
>
> **This was a flag day.** `Payload::MembershipVote { Join }` changed shape, so block ids over Join
> payloads changed: **re-genesis any devnet carrying membership history.** An old-shape Join block
> no longer decodes. `dregg-node propose-epoch-transition --add <pk>` now **refuses** unless the
> candidate's ML-DSA key is known (from its own join request, or from committed state) — because
> authoring a Join without it would author the finality halt in (3). (⚠ The refusal is real in the
> authoring decision but does not currently reach the CLI's exit status or message — see the Known
> defect box in the operator walk below.)

A dregg federation admits a new validator as an **on-chain operation**: the
candidate announces itself over the self-certifying join-request channel, a
current committee member authors the Join proposal under its own key, the
committee's quorum approves, and the running committee advances at the next
wave boundary. The chain keeps advancing
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

   Seeing that its key is not in the committee, the node sends a signed **join
   request** over the narrow join channel and re-sends it every 15 s until it is
   admitted (`run_join_requests_until_member`). The request carries BOTH halves
   of its identity — the ed25519 strand key (proven by the envelope signature)
   and the ML-DSA-65 key (proven by a proof of possession) — because a member
   admitted without its post-quantum half cannot be projected into the tau
   participant set, and ratifying such a member would halt finality everywhere.

   It does **not** author a Join block: a non-member's block is refused twice
   over (unknown sender at the transport, unenrolled creator at ingest). The
   proposal is authored by a committee **member** that sponsors your request.

4. **Watch your request, then your proposal:**

   ```sh
   curl -s localhost:8420/metrics | grep dregg_join     # your side
   curl -s localhost:8420/api/membership                # the committee's answer
   ```

   `dregg_join_requests_sent_total` climbs and `dregg_join_waiting_seconds` is
   how long you have been asking — **if that number keeps climbing, nobody is
   sponsoring you**, and the node log says so every 15 s (`no proposal for our
   key is open yet`). Once a member sponsors, your proposal appears under
   `proposals[]` with its tally (`approvals`/`required`). At quorum,
   `participants` grows by your key, `constitution_version` bumps, and your
   node's finalization votes count from the next wave. Nothing restarts.

   Measured shape of a healthy join on a 4-node devnet committee with
   `--auto-approve-joins`: request accepted at ~2 s, proposal open at ~144 s,
   `participants=5` at ~168 s, then the new member syncs the chain to parity.

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

An operator can also open the proposal on a candidate's behalf — this is the
production path, where `--auto-approve-joins` is off and sponsorship is a human
decision:

```sh
dregg-node propose-epoch-transition --add <candidate-pubkey>
```

⚑ **The candidate must be running `join` FIRST, and this refuses if it is not.**
An add needs the candidate's ML-DSA-65 key, and nothing can derive it —
`ML-DSA.KeyGen` needs the seed. It arrives exactly one way: in the candidate's
own join request, whose proof of possession this node checked. With no such
request (and no committed key, i.e. the re-add-a-former-member case) the node
refuses to author the Join, rather than authoring one whose ratification would
halt finality on every node in the federation.

> ⚠ **Known defect — the refusal does not reach your terminal.** The refusal is
> real in the authoring decision (`blocklace_sync.rs::propose_membership` returns
> `None` and logs the reason at `error!` level on the NODE), but the HTTP handler
> (`node/src/api.rs:10122`–`10151`) collapses it into `success: true` with the
> string `"error: durable persist failed; proposal not created"` in the proposal
> column, and the CLI prints a success line and exits 0. Until that is fixed, a
> "successful" `--add` whose proposal column reads `error: durable p…` means the
> ML-DSA key was missing — check `/api/membership` for the proposal, and the
> node's log for the true reason. The misattributed diagnosis is the bug, not
> the refusal.

The same verbs do removal and rotation: `--remove <pubkey>`,
`--rotate <old> <new>` — each is a proposal the committee's quorum must pass.
`--remove` needs no key material.

## Semantics worth knowing

- **`federation_id` is stable.** It commits to the GENESIS committee + epoch
  and is deliberately left unchanged by live amendments — it is the chain
  root that bots, bridges, and light clients pin. The current committee is a
  DERIVED quantity: genesis + every finalized amendment.
- **Restarts are safe.** On boot a node re-derives the committee (and any
  in-flight proposal tallies) from its persisted chain and anchors recovery
  against the committee that actually signed each attested root — an admitted
  validator never reverts to "unknown" because someone rebooted.
- **Proposing is not authority.** Only a CURRENT committee member can author a
  Join proposal (an unenrolled key's blocks are dropped at the transport and
  refused at ingest — the candidate's only voice is the join-request channel),
  and only CURRENT participants' approval votes count; the quorum rule is the
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
