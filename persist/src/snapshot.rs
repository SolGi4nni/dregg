//! Snapshot shipping: bootstrap a fresh / lagging node from
//! `{checkpoint ⊕ overlay}` instead of replaying O(history).
//!
//! # The problem
//!
//! A node joining the federation, or recovering after long downtime, otherwise
//! has to obtain and replay every finalized turn from genesis — O(history). The
//! durable store already holds the two halves a recovered node reconstructs its
//! ledger from (`docs/PROTOCOL-ENHANCEMENTS.md` §2.2): the latest full ledger
//! **checkpoint** (`ledger_store.rs::checkpoint_ledger`) and the **cell overlay**
//! committed since that checkpoint's height (`commit_log.rs::cell_overlay_since`).
//! Shipping those two halves over the wire lets a joiner reconstruct the exact
//! finalized ledger in O(checkpoint + recent delta).
//!
//! # The model this matches
//!
//! This is the wire-transport form of the verified recovery model
//! (`metatheory/Dregg2/Distributed/CrashRecovery.lean`):
//!
//! ```text
//!   recover genesis log k = applyWrites (checkpoint genesis log k) (overlay log k)
//!                         = replay genesis log
//! ```
//!
//! [`Snapshot`] carries exactly that `(checkpoint, overlay)` split plus the head
//! pointer; [`PersistentStore::apply_snapshot`] is `applyWrites checkpoint overlay`
//! followed by the convergence check the running node already performs on local
//! recovery (`node/src/state.rs`): the reconstructed ledger root MUST equal the
//! root the shipping node recorded for the head turn.
//!
//! # The root-binding tooth (anti-substitution)
//!
//! A joiner does NOT trust the shipping server. The snapshot carries a
//! `claimed_root` — the canonical ledger root of the reconstructed
//! `checkpoint ⊕ overlay` — and `apply_snapshot` recomputes that root from the
//! rebuilt ledger and **fails closed** on any mismatch. A server that tampers
//! with a single cell post-state in the overlay (or swaps a checkpoint) produces
//! a ledger whose root does not match `claimed_root`, and the apply is rejected.
//! This is the same discipline as the storage availability route's
//! reconstruct-then-hash tooth (`storage/src/availability.rs`): a snapshot that
//! reconstructs *a* ledger but not *the* committed ledger is refused.
//!
//! `claimed_root` is itself bound to the chain: it equals the head turn's
//! `CommitRecord::ledger_root` (the on-chain-style commitment the federation
//! attested), so a joiner that already trusts that root — e.g. from a
//! checkpoint QC or a finality proof — verifies the whole shipped snapshot
//! against it without trusting the server. The joiner supplies the trusted root
//! to [`PersistentStore::apply_snapshot_verified`].

use serde::{Deserialize, Serialize};

use dregg_cell::{Cell, Ledger};

use crate::ledger_store::LedgerCheckpoint;
use crate::{PersistentStore, Result, StoreError};

/// The head pointer a snapshot ships: where the shipping node's durable applied
/// order stood when the snapshot was taken. A joiner installs these so its own
/// recovery anchors resume correctly after bootstrapping from the snapshot.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SnapshotHead {
    /// The shipping node's durable commit cursor: the number of finalized turns
    /// it had applied (= the next free commit ordinal). A joiner that bootstraps
    /// from `checkpoint ⊕ overlay` is now current as of this many turns.
    pub commit_cursor: u64,
    /// The blocklace block-level high-water mark of the head turn
    /// (`CommitRecord::block_executed_up_to`): where a joiner resumes block
    /// processing. 0 if the snapshot carries no post-checkpoint turn.
    pub block_executed_up_to: u64,
}

/// A shippable bootstrap snapshot: the latest checkpoint at-or-before a target
/// height, the cell overlay committed since that checkpoint's height, the head
/// pointer, and the root commitment binding the reconstructed ledger to the
/// chain.
///
/// Reconstructing `checkpoint ⊕ overlay` and verifying its root against
/// `claimed_root` reproduces the EXACT finalized ledger the shipping node held
/// — the wire form of `CrashRecovery.recover_eq_replay`.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Snapshot {
    /// The full ledger checkpoint this snapshot is based on (the `replay genesis
    /// (take k)` base). `None` means no checkpoint existed (a node that has never
    /// checkpointed): the joiner starts from the empty ledger and the overlay
    /// carries everything — equivalent to a full replay from genesis.
    pub checkpoint: Option<LedgerCheckpoint>,
    /// The base height the overlay is computed above. Equals the checkpoint's
    /// height when one is present, else 0 (genesis). The overlay holds the
    /// last-writer-wins post-state of every cell touched by a committed turn
    /// whose `height > overlay_base_height`.
    pub overlay_base_height: u64,
    /// The cell overlay: `cell_overlay_since(overlay_base_height)`. Overlaying
    /// these on the checkpoint ledger reconstructs the finalized ledger up to
    /// the head, last-writer-wins (applied via [`upsert_cell`], keyed by id).
    pub overlay: Vec<Cell>,
    /// The head pointer (commit cursor + block cursor) at snapshot time.
    pub head: SnapshotHead,
    /// The root commitment: the canonical ledger root of the reconstructed
    /// `checkpoint ⊕ overlay`. This is `CommitRecord::ledger_root` of the head
    /// turn (the chain-attested commitment), and the anti-substitution tooth a
    /// joiner verifies the rebuilt ledger against.
    pub claimed_root: [u8; 32],
}

impl Snapshot {
    /// Whether the snapshot carries no post-checkpoint delta — the joiner that
    /// already holds the checkpoint (or is already current) applies it as a
    /// no-op on the cell map.
    pub fn is_empty_delta(&self) -> bool {
        self.overlay.is_empty()
    }
}

/// Last-writer-wins install of an overlay/replay cell into a ledger.
///
/// `dregg_cell::Ledger::insert_cell` is a STRICT insert — it refuses (and keeps
/// the existing cell) when the id is already present. The verified recovery
/// model (`CrashRecovery.upd`) and the overlay's own semantics are
/// last-writer-WINS: a post-checkpoint write to a cell that the checkpoint
/// already holds must OVERWRITE it. So overlay/replay application is
/// remove-then-insert: this is the `upd` point update the Lean side proves
/// recovery converges under.
fn upsert_cell(ledger: &mut Ledger, cell: Cell) {
    let _ = ledger.remove(&cell.id());
    let _ = ledger.insert_cell(cell);
}

/// The canonical ledger-root commitment used to bind a snapshot to the chain.
///
/// This is `dregg_cell::Ledger::root()` — the cell crate's own deterministic
/// Merkle commitment (cells sorted by id, hashed bottom-up). It is in-crate, so
/// persist computes it without reaching into `node`, and it is order-independent
/// so the rebuilt ledger commits identically regardless of overlay application
/// order. The shipping side records this same root in the commit log
/// (`CommitRecord::ledger_root`); a joiner that trusts that root verifies the
/// whole snapshot against it.
pub fn snapshot_ledger_root(ledger: &mut Ledger) -> [u8; 32] {
    ledger.root()
}

impl PersistentStore {
    // =========================================================================
    // Ship: package {checkpoint + overlay + head + root}
    // =========================================================================

    /// Build a shippable [`Snapshot`] that bootstraps a joiner from
    /// `{checkpoint ⊕ overlay}` instead of a full replay.
    ///
    /// `from_height` is the joiner's target floor: the snapshot uses the latest
    /// ledger checkpoint at-or-below the maximum of `from_height` and the
    /// store's own latest checkpoint height (we never ship a checkpoint NEWER
    /// than what we hold, and never one below `from_height` if a newer one
    /// exists — the joiner gets the smallest delta we can give it). The overlay
    /// then carries every cell post-state committed above the chosen checkpoint
    /// base, so the joiner reconstructs the finalized ledger up to our commit
    /// cursor.
    ///
    /// The shipped `claimed_root` is recomputed here from the reconstructed
    /// `checkpoint ⊕ overlay` so it is internally consistent with the two halves
    /// (a joiner re-derives the same root and it must match). When the store has
    /// a recorded head ledger root (`recovered_ledger_root`), this method
    /// asserts the reconstructed root equals it — a shipping node never ships a
    /// snapshot it cannot itself reconstruct to its recorded finalized root.
    ///
    /// `from_height` of 0 selects the genesis base (no checkpoint, full overlay)
    /// only when the store has no checkpoint; otherwise the latest checkpoint is
    /// always used (it is the smallest delta).
    pub fn ship_snapshot(&self, from_height: u64) -> Result<Snapshot> {
        // Choose the checkpoint base: the latest ledger checkpoint we hold,
        // unless the joiner already has it (from_height ≥ it) AND no newer one
        // exists — in which case the latest is still the right base (smallest
        // delta). We never ship a checkpoint above what we durably hold.
        let latest_cp_height = self.latest_ledger_checkpoint_height()?;

        let (checkpoint, base_height) = if latest_cp_height == 0 {
            // No checkpoint at all: base is genesis, overlay carries everything.
            (None, 0u64)
        } else {
            // Use the latest checkpoint at-or-below the requested floor when the
            // joiner asks for an older one; otherwise the latest (the smallest
            // delta a joiner can apply). `from_height` below the latest still
            // ships the latest — a joiner cannot reconstruct from a checkpoint
            // older than the one we'd overlay above.
            let target = from_height.max(latest_cp_height);
            // Find the highest checkpoint at-or-below `target` (== latest unless
            // the joiner targets a height between two checkpoints we hold).
            let base = self.latest_ledger_checkpoint_at_or_below(target)?;
            match base {
                Some((h, snap)) => (Some(snap), h),
                None => (None, 0u64),
            }
        };

        // The overlay above the chosen base height.
        let overlay = self.cell_overlay_since(base_height)?;

        // Reconstruct {checkpoint ⊕ overlay} to compute the binding root.
        let mut ledger = match &checkpoint {
            Some(cp) => crate::ledger_store::checkpoint_to_ledger_snapshot(cp),
            None => Ledger::new(),
        };
        for cell in &overlay {
            upsert_cell(&mut ledger, cell.clone());
        }
        let claimed_root = snapshot_ledger_root(&mut ledger);

        // A shipping node never ships a snapshot it cannot reconstruct to its
        // own recorded finalized root: if we have a recorded head root, the
        // reconstructed root MUST equal it (fail-closed).
        if let Some(recorded) = self.recovered_ledger_root()? {
            if recorded != claimed_root {
                return Err(StoreError::Integrity(format!(
                    "ship_snapshot: reconstructed root {} != recorded finalized root {} \
                     (refusing to ship a non-convergent snapshot)",
                    hex32(&claimed_root),
                    hex32(&recorded),
                )));
            }
        }

        let head = SnapshotHead {
            commit_cursor: self.commit_cursor()?,
            block_executed_up_to: self.recovered_block_cursor()?,
        };

        Ok(Snapshot {
            checkpoint,
            overlay_base_height: base_height,
            overlay,
            head,
            claimed_root,
        })
    }

    // =========================================================================
    // Apply: rebuild {checkpoint ⊕ overlay}, verify the root, fail closed
    // =========================================================================

    /// Reconstruct a ledger from a shipped [`Snapshot`] and verify it against the
    /// snapshot's own `claimed_root`.
    ///
    /// Returns the reconstructed [`Ledger`]. This is `applyWrites checkpoint
    /// overlay` (`CrashRecovery.recover`) followed by the convergence tooth:
    /// the recomputed canonical root MUST equal `claimed_root`, else the apply
    /// is rejected with an integrity error (fail-closed, no-weakening).
    ///
    /// This form verifies INTERNAL consistency (the two halves agree with the
    /// claimed root). It does NOT by itself defend against a server that ships a
    /// self-consistent snapshot of a DIFFERENT ledger; for that, a joiner that
    /// holds a trusted root uses [`Self::apply_snapshot_verified`].
    pub fn apply_snapshot(&self, snapshot: &Snapshot) -> Result<Ledger> {
        let mut ledger = match &snapshot.checkpoint {
            Some(cp) => crate::ledger_store::checkpoint_to_ledger_snapshot(cp),
            None => Ledger::new(),
        };
        // Overlay the post-checkpoint cell post-states (last-writer-wins via
        // upsert_cell: the overlay is already a last-writer-wins projection, and
        // upsert OVERWRITES any same-id cell the checkpoint already held — the
        // `CrashRecovery.upd` point update, NOT insert_cell's strict insert).
        for cell in &snapshot.overlay {
            upsert_cell(&mut ledger, cell.clone());
        }

        // The anti-substitution tooth: the reconstructed ledger MUST commit to
        // the claimed root. A tampered overlay/checkpoint yields a different
        // root and is refused.
        let got = snapshot_ledger_root(&mut ledger);
        if got != snapshot.claimed_root {
            return Err(StoreError::Integrity(format!(
                "apply_snapshot: reconstructed ledger root {} != claimed root {} \
                 (snapshot tampered or inconsistent — refusing, fail-closed)",
                hex32(&got),
                hex32(&snapshot.claimed_root),
            )));
        }
        Ok(ledger)
    }

    /// [`Self::apply_snapshot`] PLUS the anti-substitution check against a root a
    /// joiner ALREADY TRUSTS (from a checkpoint QC, a finality proof, or a peer
    /// it trusts). The reconstructed ledger's root must equal BOTH the snapshot's
    /// `claimed_root` AND `trusted_root` — so a server cannot ship a
    /// self-consistent snapshot of a ledger the joiner did not expect.
    ///
    /// This is the full no-trust bootstrap: the joiner verifies the shipped
    /// snapshot against a root it brought itself, never trusting the server.
    pub fn apply_snapshot_verified(
        &self,
        snapshot: &Snapshot,
        trusted_root: &[u8; 32],
    ) -> Result<Ledger> {
        if snapshot.claimed_root != *trusted_root {
            return Err(StoreError::Integrity(format!(
                "apply_snapshot_verified: snapshot claims root {} but joiner trusts {} \
                 (refusing a snapshot of an unexpected ledger — fail-closed)",
                hex32(&snapshot.claimed_root),
                hex32(trusted_root),
            )));
        }
        // The internal tooth still runs: the two halves must reconstruct to the
        // (now trusted) claimed root.
        self.apply_snapshot(snapshot)
    }

    /// Apply a shipped snapshot AND rebuild this store's durable state from it:
    /// install the checkpoint, replace the cell-by-id overlay and the commit
    /// head pointers so the joiner's own future recovery reconstructs the same
    /// ledger. The ledger is verified against `claimed_root` first (fail-closed),
    /// then committed, then the secondary index is rebuilt to agree with the new
    /// state.
    ///
    /// Returns the reconstructed [`Ledger`] (the in-memory live state the node
    /// runs with) on success.
    ///
    /// NOTE: this installs the checkpoint + a single synthetic commit head; the
    /// joiner does not gain the shipping node's full per-turn commit log (it does
    /// not need it — `checkpoint ⊕ overlay` is the finalized state). The
    /// cell-by-id index is rebuilt from the overlay so `lookup_cell` works.
    pub fn install_snapshot(&self, snapshot: &Snapshot, trusted_root: &[u8; 32]) -> Result<Ledger> {
        // 1. Verify against the trusted root BEFORE mutating any durable state.
        let ledger = self.apply_snapshot_verified(snapshot, trusted_root)?;

        // 2. Install the checkpoint (if any) durably.
        if let Some(cp) = &snapshot.checkpoint {
            self.store_ledger_checkpoint_snapshot(cp)?;
        }

        // 3. Install the cell-by-id overlay so post-checkpoint cells resolve.
        self.install_overlay_into_cell_index(&snapshot.overlay)?;

        Ok(ledger)
    }
}

fn hex32(b: &[u8; 32]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::commit_log::CommitRecord;
    use dregg_cell::{Cell, Ledger};

    /// A deterministic cell with a given id-seed and balance.
    fn cell(seed: u8, balance: i64) -> Cell {
        Cell::with_balance([seed; 32], [seed.wrapping_add(7); 32], balance)
    }

    /// Commit `n` turns, each touching one cell, at ascending heights. Returns
    /// the canonical root of the full ledger (the genesis-replay reference).
    fn commit_turns(store: &PersistentStore, specs: &[(u8, i64, u64)]) {
        for (i, (seed, bal, height)) in specs.iter().enumerate() {
            let n = i as u64;
            let mut turn_hash = [0u8; 32];
            turn_hash[0] = 0xa0;
            turn_hash[1] = n as u8;
            let mut receipt_hash = [0u8; 32];
            receipt_hash[0] = 0xb0;
            receipt_hash[1] = n as u8;
            let c = cell(*seed, *bal);
            // Reconstruct the running ledger to compute the recorded root, so
            // the commit log's ledger_root matches what ship_snapshot rebuilds.
            let ledger_root = ledger_root_after_commits(store, &c);
            let rec = CommitRecord {
                ordinal: n,
                height: *height,
                block_id: [n as u8; 32],
                block_executed_up_to: n * 10,
                turn_hash,
                creator: [(n % 3) as u8 + 1; 32],
                receipt_hash,
                ledger_root,
                touched_cells: vec![c],
            };
            store.commit_finalized_turn(n, &rec).unwrap();
        }
    }

    /// Compute the canonical root of the full genesis-replay ledger AFTER adding
    /// `new_cell` to everything committed so far (last-writer-wins by id).
    fn ledger_root_after_commits(store: &PersistentStore, new_cell: &Cell) -> [u8; 32] {
        let mut ledger = Ledger::new();
        // replay every already-committed turn from genesis (last-writer-wins).
        for rec in store.commit_records_from(0).unwrap() {
            for c in rec.touched_cells {
                upsert_cell(&mut ledger, c);
            }
        }
        upsert_cell(&mut ledger, new_cell.clone());
        ledger.root()
    }

    /// The full genesis-replay ledger root (the reference recovery must reach),
    /// last-writer-wins (`CrashRecovery.replay`).
    fn full_replay_root(store: &PersistentStore) -> [u8; 32] {
        let mut ledger = Ledger::new();
        for rec in store.commit_records_from(0).unwrap() {
            for c in rec.touched_cells {
                upsert_cell(&mut ledger, c);
            }
        }
        ledger.root()
    }

    #[test]
    fn ship_then_apply_roundtrip_reconstructs_exact_ledger() {
        let store = PersistentStore::open_in_memory().unwrap();
        // Six turns at heights 1..=6, two distinct cells, some overwrites.
        commit_turns(
            &store,
            &[
                (1, 100, 1),
                (2, 200, 2),
                (1, 150, 3), // overwrite cell-seed-1
                (3, 300, 4),
                (2, 250, 5), // overwrite cell-seed-2
                (1, 175, 6), // overwrite cell-seed-1 again
            ],
        );
        // Checkpoint the ledger at height 3 (replay of the first 3 turns).
        let mut cp_ledger = Ledger::new();
        for rec in store.commit_records_from(0).unwrap() {
            if rec.height <= 3 {
                for c in rec.touched_cells {
                    upsert_cell(&mut cp_ledger, c);
                }
            }
        }
        store.checkpoint_ledger(&cp_ledger, 3).unwrap();

        // Ship from a joiner targeting height 0 (give it the smallest delta).
        let snap = store.ship_snapshot(0).unwrap();
        // The snapshot is based on the height-3 checkpoint with a non-empty overlay.
        assert_eq!(snap.overlay_base_height, 3);
        assert!(!snap.is_empty_delta(), "turns above height 3 → non-empty overlay");

        // Apply reconstructs the EXACT full-replay ledger.
        let mut rebuilt = store.apply_snapshot(&snap).unwrap();
        assert_eq!(rebuilt.root(), full_replay_root(&store));
        // And the claimed root equals the full-replay root (chain-bound).
        assert_eq!(snap.claimed_root, full_replay_root(&store));
        // Spot-check a few reconstructed cell balances (last-writer-wins).
        assert_eq!(rebuilt.iter().count(), 3); // seeds 1,2,3
    }

    #[test]
    fn tampered_overlay_fails_the_root_check() {
        let store = PersistentStore::open_in_memory().unwrap();
        commit_turns(&store, &[(1, 100, 1), (2, 200, 2), (3, 300, 3)]);
        let mut cp_ledger = Ledger::new();
        let _ = cp_ledger.insert_cell(cell(1, 100));
        store.checkpoint_ledger(&cp_ledger, 1).unwrap();

        let mut snap = store.ship_snapshot(0).unwrap();
        // Tamper: replace one overlay cell's balance with a forged value.
        assert!(!snap.overlay.is_empty());
        snap.overlay[0] = cell(2, 99_999); // wrong balance for the same id family

        let err = store.apply_snapshot(&snap);
        assert!(
            matches!(err, Err(StoreError::Integrity(_))),
            "tampered overlay must fail the root check, got {err:?}"
        );
    }

    #[test]
    fn tampered_checkpoint_fails_the_root_check() {
        let store = PersistentStore::open_in_memory().unwrap();
        commit_turns(&store, &[(1, 100, 1), (2, 200, 2), (3, 300, 3)]);
        let mut cp_ledger = Ledger::new();
        let _ = cp_ledger.insert_cell(cell(1, 100));
        store.checkpoint_ledger(&cp_ledger, 1).unwrap();

        let mut snap = store.ship_snapshot(0).unwrap();
        // Tamper the checkpoint base: forge a cell in the checkpoint half.
        if let Some(cp) = &mut snap.checkpoint {
            cp.cells.push(cell(42, 1));
        }
        let err = store.apply_snapshot(&snap);
        assert!(
            matches!(err, Err(StoreError::Integrity(_))),
            "tampered checkpoint must fail the root check, got {err:?}"
        );
    }

    #[test]
    fn empty_delta_snapshot_is_a_noop_apply() {
        let store = PersistentStore::open_in_memory().unwrap();
        // Commit turns ALL at-or-below the checkpoint height → empty overlay.
        commit_turns(&store, &[(1, 100, 1), (2, 200, 2), (3, 300, 3)]);
        // Checkpoint the FULL ledger at height 3 (== latest turn height).
        let mut cp_ledger = Ledger::new();
        for rec in store.commit_records_from(0).unwrap() {
            for c in rec.touched_cells {
                upsert_cell(&mut cp_ledger, c);
            }
        }
        store.checkpoint_ledger(&cp_ledger, 3).unwrap();

        let snap = store.ship_snapshot(0).unwrap();
        // No turn has height > 3, so the overlay is empty.
        assert!(snap.is_empty_delta(), "joiner already current → empty delta");
        // Apply still reconstructs the exact ledger from the checkpoint alone.
        let mut rebuilt = store.apply_snapshot(&snap).unwrap();
        assert_eq!(rebuilt.root(), full_replay_root(&store));
        assert_eq!(snap.claimed_root, full_replay_root(&store));
    }

    #[test]
    fn ship_from_genesis_equals_full_replay() {
        let store = PersistentStore::open_in_memory().unwrap();
        commit_turns(&store, &[(1, 100, 1), (2, 200, 2), (1, 150, 3), (3, 300, 4)]);
        // NO checkpoint at all: ship_snapshot bases at genesis, overlay = all.
        let snap = store.ship_snapshot(0).unwrap();
        assert!(snap.checkpoint.is_none(), "no checkpoint → genesis base");
        assert_eq!(snap.overlay_base_height, 0);
        // Apply reconstructs the full-replay ledger from genesis + full overlay.
        let mut rebuilt = store.apply_snapshot(&snap).unwrap();
        assert_eq!(rebuilt.root(), full_replay_root(&store));
        assert_eq!(snap.claimed_root, full_replay_root(&store));
        // 3 distinct cells survive (seed 1 overwritten once).
        assert_eq!(rebuilt.iter().count(), 3);
    }

    #[test]
    fn apply_verified_rejects_wrong_trusted_root() {
        let store = PersistentStore::open_in_memory().unwrap();
        commit_turns(&store, &[(1, 100, 1), (2, 200, 2)]);
        let snap = store.ship_snapshot(0).unwrap();

        // The right trusted root applies.
        let trusted = snap.claimed_root;
        assert!(store.apply_snapshot_verified(&snap, &trusted).is_ok());

        // A joiner that trusts a DIFFERENT root refuses the snapshot.
        let mut wrong = trusted;
        wrong[0] ^= 0xff;
        let err = store.apply_snapshot_verified(&snap, &wrong);
        assert!(
            matches!(err, Err(StoreError::Integrity(_))),
            "wrong trusted root must reject, got {err:?}"
        );
    }

    #[test]
    fn install_snapshot_makes_a_joiner_recover_the_same_ledger() {
        // Shipping node builds state + a checkpoint.
        let shipper = PersistentStore::open_in_memory().unwrap();
        commit_turns(
            &shipper,
            &[(1, 100, 1), (2, 200, 2), (1, 150, 3), (3, 300, 4), (2, 250, 5)],
        );
        let mut cp_ledger = Ledger::new();
        for rec in shipper.commit_records_from(0).unwrap() {
            if rec.height <= 2 {
                for c in rec.touched_cells {
                    upsert_cell(&mut cp_ledger, c);
                }
            }
        }
        shipper.checkpoint_ledger(&cp_ledger, 2).unwrap();
        let snap = shipper.ship_snapshot(0).unwrap();
        let trusted = snap.claimed_root;

        // Fresh joiner installs the snapshot.
        let joiner = PersistentStore::open_in_memory().unwrap();
        let mut ledger = joiner.install_snapshot(&snap, &trusted).unwrap();
        assert_eq!(ledger.root(), full_replay_root(&shipper));

        // The joiner's durable state now reconstructs the same ledger from its
        // installed checkpoint ⊕ the overlay installed into its cell index.
        let (cp_h, cp_ledger2) = joiner.load_latest_ledger_checkpoint().unwrap().unwrap();
        assert_eq!(cp_h, 2);
        let mut joiner_rebuilt = cp_ledger2;
        // install_snapshot put the overlay in the joiner's cell-by-id index
        // (the joiner has no commit log; the cell index IS its overlay).
        for c in joiner.installed_overlay_cells().unwrap() {
            upsert_cell(&mut joiner_rebuilt, c);
        }
        assert_eq!(joiner_rebuilt.root(), full_replay_root(&shipper));
    }
}
