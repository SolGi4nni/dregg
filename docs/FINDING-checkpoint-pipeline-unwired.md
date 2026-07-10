# FINDING: the federation-checkpoint pipeline is unwired dead code

Established 2026-07-10 (swarm lane, independently code-verified). This corrects an
overclaim: the anchored trusted root is NOT merely "unexercised because the devnet
is quiet" — the qc-bearing `Checkpoint` object it depends on is never produced.

## The chain of dead ends

- `dregg_federation::Checkpoint` (the qc-bearing object `/checkpoint/latest` serves
  via `store.latest_checkpoint()`) carries `ledger_state_root`, `note_tree_root`,
  `nullifier_set_root`, `revocation_tree_root`, `epoch`, `qc` — and **no
  receipt-index MMR root** (`federation/src/checkpoint.rs:27`).
- `PersistentStore::store_checkpoint` (`persist/src/checkpoint.rs:31`) has **zero
  callers** repo-wide (`grep -rn 'store_checkpoint(' | grep -v 'fn ' | grep -v
  restore_` is empty).
- Nothing constructs a `Payload::Checkpoint {..}` block to propose — only `match`
  arms exist.
- `finalize_checkpoint` / `is_checkpoint_height` (`federation/src/checkpoint.rs`)
  are reached only from tests.
- The node's `FinalizedBlock::Checkpoint` arm (`node/src/blocklace_sync.rs:4086`)
  was a NO-OP that logged `"finalized checkpoint block (stored)"` while storing
  nothing (`let _ = (root, height); // handled elsewhere` — elsewhere does not
  exist). Log message corrected to say it is unwired.
- `checkpoint_interval` (`state.rs:280`, from genesis) drives a **different**
  structure: `maybe_produce_checkpoint` (`blocklace_sync.rs:7432`) writes a
  qc-less blocklace fast-sync DAG+ledger snapshot under `blocklace_checkpoint_*`,
  served at `/api/blocklace/checkpoint`. That is not what `/checkpoint/latest`
  reads and carries no quorum certificate.

Live confirmation: `curl -s -o /dev/null -w '%{http_code}' :7811/checkpoint/latest`
→ **404**, and stays 404 at any `checkpoint_interval`.

## Consequence for the DreggNet anchor (the honest verdict)

`DreggNet control/src/node_api.rs::verify_anchor` checks `cp.qc_votes >=
min_qc_votes` and `cp.height >= anchor.height`, then returns `anchor.mmr_root`
**verbatim from operator config** — a value never cross-checked against the
checkpoint. So even if the pipeline were wired, the anchor would prove two
*disjoint* things: (a) the node self-reports being at/above a finalized ledger
height, and (b) the receipt MMR root equals an operator-pinned constant
(config-time TOFU). The finality gate and the receipt MMR live on two disjoint
Merkle structures with **no cryptographic link** — the `Checkpoint` has no
receipt-index root field to bind to.

**Therefore, today:**
- `/checkpoint/latest` 404s, so exporting `DREGGNET_TRUSTED_ROOT` routes
  `verify_anchor` into a 404 error → `read_verified_leases` errors → `poll()`
  returns empty. **It DISABLES the lease read rather than hardening it.** Leave it
  unset (`TrustedRoot::NodeServed`) until the pipeline lands.
- The anchor, as designed, is theatre with respect to the receipt log even once
  wired: it does not bind the receipt-index MMR root to consensus finality.

## DON'T wire this pipeline — a live quorum already exists elsewhere (scholar study, 2026-07-10)

A follow-up scholar study found that resurrecting the qc-bearing `Checkpoint`
pipeline is the WRONG investment for a federation-wide read. **A live BFT quorum
already exists and is wired** — not on `Checkpoint`, but on
`StoredAttestedRoot.finalization_quorum` (`persist/src/federation.rs:130`), which
accumulates ≥threshold committee finalization-vote signatures over
`canonical_ledger_root(&s.ledger)` (bound into the vote at
`blocklace_sync.rs:4131`), populated live by `backfill_finalization_quorums`
(`:4241`) and verifiable by `verify_finalization_quorum` (`federation.rs:213`).

So the thing a federation-wide read fundamentally needs — a quorum-certified
`ledger_state_root` — is already produced. The dead `Checkpoint` would, if wired,
carry the *same* `ledger_state_root`. Therefore:

- The **receipt-anchor** path (add `receipt_index_root` to `Checkpoint`, wire
  production, have verify_anchor read it) is NOT federation-wide even done right —
  the receipt index is a per-node side log (the live 4/1/1 length divergence), so
  it only qc-anchors *one node's own* chain. Skip it.
- The **ledger-state inclusion** path (`~/dev/DreggNet/docs/FEDERATION-WIDE-READ.md`
  Option B) is federation-wide and rides the ALREADY-LIVE attested-root quorum. It
  needs a `GET /api/cell/{id}/proof` endpoint (B-flat: full leaf set + recompute the
  flat `canonical_ledger_root` — note it is FLAT, not a Merkle tree, so no O(log n)
  opening today) and a consumer that checks `finalization_quorum ≥ threshold` (or
  cross-checks f+1 nodes) + no-rollback. ~2-3 days, and **it does NOT depend on
  wiring this Checkpoint pipeline.**

Wire the qc-bearing `Checkpoint` pipeline only if pruning / fast-bootstrap
independently needs it — not for the lease read. The log-honesty fix above stands
regardless (the arm must not claim it stored something).
