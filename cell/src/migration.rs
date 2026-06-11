//! Atomic cell migration (Hosted↔Sovereign, and cross-federation handoff).
//!
//! ## The gap this closes
//!
//! [`crate::cell::CellMode`] is fixed at construction and [`crate::ledger::Ledger::make_sovereign`]
//! flips a *local* cell between Hosted and Sovereign within one federation. Neither moves a cell's
//! **home** — there was no protocol to relocate a cell from one federation (ledger) to another
//! while preserving its identity and authority and *preventing double-existence*. The
//! [`crate::lifecycle::CellLifecycle::Migrated`] variant existed only as an inert terminal tombstone;
//! nothing produced it.
//!
//! This module implements the **two-step atomic handoff** that drives a cell to that tombstone:
//!
//! ```text
//!   source federation                          destination federation
//!   ─────────────────                          ──────────────────────
//!   1. PREPARE  ── voucher ───────────────────▶ 2. ACCEPT (install cell, mode = target)
//!      (lock the cell: quiescent, still Live)         emit MigrationReceipt (attestation)
//!   3. COMMIT ◀──────────── receipt ──────────       │
//!      tombstone source → Migrated { to, … }         └ cell is now LIVE here, exactly once
//! ```
//!
//! Between PREPARE and COMMIT the source cell is **locked** (rejects effects — it is quiescent like
//! [`crate::cell::Cell::seal`], but the migration-in-flight is recorded so the local node knows a
//! handoff is pending). The destination installs the cell only on a verified [`MigrationVoucher`];
//! the source tombstones only on a verified [`MigrationReceipt`] that binds the destination's
//! acceptance. The result: at every instant, the cell has **exactly one live home** (no
//! double-existence), and its **balance + capabilities are conserved** across the move
//! (authority-conservation).
//!
//! ## What can go wrong (and is rejected)
//!
//! * Installing the same cell on the destination twice (double-existence) → [`MigrationError::DestinationOccupied`].
//! * Committing the source tombstone before the destination accepted → caller must hold a
//!   [`MigrationReceipt`]; a forged/mismatched receipt → [`MigrationError::ReceiptMismatch`].
//! * Mutating the carried state between PREPARE and ACCEPT (the voucher binds the cell's exact
//!   pre-migration state commitment) → [`MigrationError::StateMismatch`].
//! * Re-preparing a cell that is already locked / already terminal → [`MigrationError::NotMigratable`].
//!
//! These are the data-tier image of a 2-phase-commit handoff: the source's COMMIT is gated on the
//! destination's ACCEPT, so the two ledgers can never both hold a live copy.

use serde::{Deserialize, Serialize};

use crate::cell::{Cell, CellMode};
use crate::id::CellId;
use crate::lifecycle::CellLifecycle;

/// A stable 32-byte identifier for a federation (its genesis / charter hash).
///
/// Two distinct federations have distinct ids; the migration binds source and destination ids so a
/// voucher minted for one destination cannot be replayed at another.
pub type FederationId = [u8; 32];

/// The voucher a source federation mints to authorize a migration. It binds the cell identity, the
/// exact pre-migration state commitment (so the carried state cannot be tampered en route), the
/// source and destination federations, and the target mode at the destination.
///
/// The voucher is the **PREPARE** artifact: it certifies "federation `from` has locked cell
/// `cell_id` at state `state_commitment` and authorizes its relocation to `to`." A real deployment
/// attaches a source-federation quorum signature in a higher-level wrapper; this struct is the
/// signed *content*.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MigrationVoucher {
    /// The cell being relocated. Identity is preserved across the move
    /// (`cell_id == derive_raw(public_key, token_id)` on both sides).
    pub cell_id: CellId,
    /// The cell's canonical state commitment at the instant of PREPARE. The destination checks the
    /// installed cell hashes to exactly this value, so no value can be conjured or destroyed in
    /// transit (authority-conservation).
    pub state_commitment: [u8; 32],
    /// The source federation that locked the cell.
    pub from: FederationId,
    /// The destination federation that is to take custody.
    pub to: FederationId,
    /// The mode the cell should inhabit at the destination.
    pub target_mode: CellMode,
    /// Source-federation height at which PREPARE was applied (for ordering / audit).
    pub prepared_at: u64,
}

impl MigrationVoucher {
    /// The canonical 32-byte hash of this voucher — the value the destination's
    /// [`MigrationReceipt`] echoes so the source can match its COMMIT to the right acceptance.
    pub fn voucher_hash(&self) -> [u8; 32] {
        let mut h = blake3::Hasher::new_derive_key("dregg-cell:migration-voucher v1");
        h.update(self.cell_id.as_bytes());
        h.update(&self.state_commitment);
        h.update(&self.from);
        h.update(&self.to);
        h.update(&[match self.target_mode {
            CellMode::Hosted => 0u8,
            CellMode::Sovereign => 1u8,
        }]);
        h.update(&self.prepared_at.to_le_bytes());
        *h.finalize().as_bytes()
    }
}

/// The receipt a destination federation emits once it has *accepted custody* of the cell. It echoes
/// the voucher hash (binding the acceptance to a specific PREPARE) and records the destination
/// height. This is the **ACCEPT** attestation; the source's **COMMIT** consumes it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MigrationReceipt {
    /// The cell that was accepted.
    pub cell_id: CellId,
    /// The hash of the voucher this receipt accepts. The source matches this against
    /// [`MigrationVoucher::voucher_hash`] before tombstoning.
    pub voucher_hash: [u8; 32],
    /// The destination federation that took custody.
    pub accepted_by: FederationId,
    /// Destination-federation height at which the cell was installed.
    pub accepted_at: u64,
}

impl MigrationReceipt {
    /// The canonical 32-byte attestation hash bound into the source cell's
    /// [`CellLifecycle::Migrated`] tombstone. Any verifier holding the source cell's final
    /// commitment can demonstrate "this cell was migrated under this receipt."
    pub fn attestation(&self) -> [u8; 32] {
        let mut h = blake3::Hasher::new_derive_key("dregg-cell:migration-receipt v1");
        h.update(self.cell_id.as_bytes());
        h.update(&self.voucher_hash);
        h.update(&self.accepted_by);
        h.update(&self.accepted_at.to_le_bytes());
        *h.finalize().as_bytes()
    }
}

/// Per-cell record that a migration is in flight (between PREPARE and COMMIT). Held by the source
/// node so it knows the cell is locked and which voucher it is committing against. It is *not* a
/// lifecycle state — the cell is still `Live` in its history until COMMIT tombstones it — but while
/// a `MigrationLock` is present the cell rejects effects.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MigrationLock {
    /// The voucher that PREPARE minted. COMMIT must present a receipt matching `voucher.voucher_hash()`.
    pub voucher: MigrationVoucher,
}

/// Errors from the migration protocol.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MigrationError {
    /// The cell cannot be migrated from its current lifecycle state (terminal, or already locked).
    NotMigratable,
    /// The destination already holds a cell with this id (would create double-existence).
    DestinationOccupied(CellId),
    /// The voucher's bound `state_commitment` does not match the cell being installed.
    StateMismatch,
    /// The voucher's destination federation does not match the federation attempting to accept.
    WrongDestination,
    /// The receipt presented at COMMIT does not match the in-flight voucher (wrong voucher hash,
    /// wrong cell, or no migration in flight).
    ReceiptMismatch,
    /// The cell to migrate was not found in the source ledger.
    SourceNotFound(CellId),
    /// Identity integrity broken: `cell_id != derive_raw(public_key, token_id)`.
    IdentityBroken(CellId),
}

impl core::fmt::Display for MigrationError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::NotMigratable => f.write_str("cell is not in a migratable state"),
            Self::DestinationOccupied(id) => {
                write!(f, "destination already holds cell {id} (double-existence)")
            }
            Self::StateMismatch => f.write_str("installed cell does not match voucher commitment"),
            Self::WrongDestination => f.write_str("voucher destination federation mismatch"),
            Self::ReceiptMismatch => {
                f.write_str("migration receipt does not match in-flight voucher")
            }
            Self::SourceNotFound(id) => write!(f, "migration source cell not found: {id}"),
            Self::IdentityBroken(id) => write!(f, "cell identity integrity broken: {id}"),
        }
    }
}

impl std::error::Error for MigrationError {}

impl Cell {
    /// Build the PREPARE voucher for relocating this cell to `to` in `target_mode`, binding the
    /// cell's *current* canonical state commitment. The caller (source node) then records a
    /// [`MigrationLock`] and stops accepting effects for the cell. Pure: does not mutate the cell.
    ///
    /// # Errors
    ///
    /// Returns [`MigrationError::NotMigratable`] if the cell is in a terminal lifecycle state, and
    /// [`MigrationError::IdentityBroken`] if `id != derive_raw(public_key, token_id)`.
    pub fn migration_voucher(
        &self,
        from: FederationId,
        to: FederationId,
        target_mode: CellMode,
        prepared_at: u64,
    ) -> Result<MigrationVoucher, MigrationError> {
        if self.lifecycle.is_terminal() {
            return Err(MigrationError::NotMigratable);
        }
        if !self.verify_id_integrity() {
            return Err(MigrationError::IdentityBroken(self.id()));
        }
        Ok(MigrationVoucher {
            cell_id: self.id(),
            state_commitment: self.state_commitment(),
            from,
            to,
            target_mode,
            prepared_at,
        })
    }

    /// Tombstone this cell as [`CellLifecycle::Migrated`], consuming a destination
    /// [`MigrationReceipt`] that matches `voucher`. This is the source-side **COMMIT**. After this,
    /// the cell is terminal: it can never accept effects or be re-migrated, so the destination's
    /// copy is the unique live home.
    ///
    /// # Errors
    ///
    /// * [`MigrationError::NotMigratable`] — the cell is already terminal.
    /// * [`MigrationError::ReceiptMismatch`] — the receipt does not echo `voucher.voucher_hash()`
    ///   or names a different cell.
    pub fn migrate_commit(
        &mut self,
        voucher: &MigrationVoucher,
        receipt: &MigrationReceipt,
    ) -> Result<(), MigrationError> {
        if self.lifecycle.is_terminal() {
            return Err(MigrationError::NotMigratable);
        }
        // The receipt must accept *this* cell's *this* voucher.
        if receipt.cell_id != self.id()
            || voucher.cell_id != self.id()
            || receipt.voucher_hash != voucher.voucher_hash()
        {
            return Err(MigrationError::ReceiptMismatch);
        }
        // The destination cell id is the same content-addressed id (identity preserved across the
        // move). The attestation binds the acceptance receipt into the tombstone.
        self.lifecycle = CellLifecycle::Migrated {
            to: self.id(),
            attestation: receipt.attestation(),
            migrated_at: receipt.accepted_at,
        };
        Ok(())
    }
}

/// Result of accepting a migration on the destination ledger: the freshly installed cell's id and
/// the receipt to send back to the source so it can COMMIT.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AcceptOutcome {
    /// The id of the now-live cell at the destination.
    pub cell_id: CellId,
    /// The receipt the source consumes in [`Cell::migrate_commit`].
    pub receipt: MigrationReceipt,
}
