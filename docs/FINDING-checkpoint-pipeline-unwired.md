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

## What "make it real" requires (not a targeted diff)

1. Add `receipt_index_root: [u8; 32]` to `dregg_federation::Checkpoint` and include
   it in `content_hash` / the checkpoint vote message so the qc actually attests it.
2. Populate it from `s.receipt_index.root()` at checkpoint-build time.
3. Wire the production path: propose `Payload::Checkpoint` at interval boundaries;
   call `finalize_checkpoint` + `store.store_checkpoint` in the
   `FinalizedBlock::Checkpoint` arm (currently the no-op).
4. Surface the field on `/checkpoint/latest` (`api.rs` `checkpoint_to_response`)
   and change `verify_anchor` to compare `cp.receipt_index_root` to
   `anchor.mmr_root` instead of returning the config constant.

Only after (1)+(4) does the anchor bind the receipt log to finality — and note it
would still bind *each node's own* receipt root (per-node chains legitimately
differ), so it hardens `CheckpointBound` for one node's chain but does not make the
receipt read federation-wide. A genuinely federation-wide lease read is the
separate ledger-state-inclusion-proof design (see
`~/dev/DreggNet/docs/FEDERATION-WIDE-READ.md`).
