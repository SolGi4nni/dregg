//! GENESIS-FROM-SNAPSHOT — carry a cell-set across an EPOCH bump.
//!
//! ## The gap this closes
//!
//! A devnet re-genesis today is a **WIPE**: `node/src/genesis.rs` mints fresh
//! committee keys → a fresh `federation_id` → a brand-new chain, and
//! `deploy/genesis/generate.sh --force` deletes the old `genesis.json` and keys.
//! Every character, leaderboard, and universe minted on the old chain is gone.
//!
//! The vat-migration design (`plans/vat-migration-design.md`) already specifies a
//! `CellExportBundle` — a cell carried FROM one federation TO another with an IVC
//! proof of its history-from-genesis and a state-commitment binding, so the target
//! can install it without trusting the source. That primitive is **cross-federation**.
//! This crate **generalizes it to cross-EPOCH**: the "source federation" is the OLD
//! chain (committee epoch N), the "destination federation" is the FRESH GENESIS
//! (epoch N+1). A re-genesis can then SEED the new chain with a frozen EXPORT of the
//! old cell-set instead of wiping it.
//!
//! ```text
//!   OLD chain (epoch N)                         FRESH genesis (epoch N+1)
//!   ───────────────────                         ─────────────────────────
//!   mint new committee keys ── new fed id ─────▶ (destination federation id)
//!   FREEZE + EXPORT cell-set:                    IMPORT / SEED:
//!     per cell:                                    per entry, REFUSE unless
//!       · full Cell                                  · id re-addresses identically
//!       · content-address (CellId)                     (verify_id_integrity)
//!       · cross-epoch MigrationVoucher              · voucher binds this exact state
//!         (from = old fed, to = new fed)               (from/to + state_commitment)
//!       · IVC proof of history-from-old-genesis    · IVC history verifies AND its
//!                                                      final root binds THIS cell
//!                                                 ⇒ carried-forward cells re-address
//!                                                    IDENTICALLY, history validated.
//! ```
//!
//! ## Why the imported cell re-addresses identically
//!
//! A cell's identity is `CellId = derive_raw(public_key, token_id)` — a pure
//! content-address, independent of which federation or epoch hosts it. So an
//! honestly-carried cell, dropped into the fresh genesis, recomputes to the SAME
//! `CellId`. [`seed_genesis`] re-checks this ([`SnapshotEntry`] integrity) and
//! refuses any entry whose declared address does not match its recomputed one.
//!
//! ## What is refused on import (non-vacuous tamper rejection)
//!
//! * A **forged cell** (e.g. a balance bumped after freeze) changes the cell's
//!   `state_commitment`, which breaks BOTH the migration voucher binding
//!   ([`EntryReject::VoucherMismatch`]) and the IVC history's final-root binding
//!   ([`EntryReject::HistoryStateMismatch`]).
//! * A **broken history proof** (a flipped accumulated hash / trace commitment)
//!   fails [`dregg_circuit::ivc::verify_ivc`] → [`EntryReject::HistoryInvalid`].
//! * A cell whose **content-address does not recompute** → [`EntryReject::AddressMismatch`]
//!   / [`EntryReject::IdentityBroken`].
//! * A snapshot minted for a **different destination epoch** → [`ImportError::WrongDestination`].
//!
//! The honest cell in every one of these pairs imports cleanly, so the rejection
//! is non-vacuous.
//!
//! ## HONEST SCOPE
//!
//! * **Real**: the export/import carry-forward, the content-address re-addressing
//!   stability, and the layered history/state-commitment validation on import.
//! * **NAMED CAVEAT — the unsound fold.** The IVC history leg is a real
//!   [`dregg_circuit::ivc::IvcProof`] built with the real prover/verifier over a
//!   real fold chain — BUT the vat-migration story it generalizes leans on a
//!   **bridge fold that the project flags UNSOUND** (see memory
//!   `project-carrier-deployment-architecture` / `project-universal-fold-buff-lightclient`).
//!   The history proof here models the cell's turn history as a chain of fold
//!   deltas (a modeled stand-in for the real per-turn state-transition witnesses);
//!   the *chain structure* (linkage, ordering, endpoint binding) is sound, but the
//!   soundness of the history leg as a whole inherits that flagged fold. The
//!   state-commitment voucher binding is an independent, unconditional second check.
//! * **Deploy wiring** (NOT built here): threading [`GenesisSnapshot::export`] into a
//!   node's freeze path and [`seed_genesis`] into `node/src/genesis.rs` /
//!   `deploy/genesis/generate.sh` so a live re-genesis reads a snapshot file. This
//!   crate is the additive primitive; the operator wiring is a separate deploy step.

use dregg_cell::migration::{FederationId, MigrationError as CellMigrationError, MigrationVoucher};
use dregg_cell::{Cell, CellId};
use dregg_circuit::field::{BABYBEAR_P, BabyBear};
use dregg_circuit::fold_air::create_test_fold;
use dregg_circuit::ivc::{
    FoldDelta, IvcProof, IvcVerification, MAX_FOLD_DEPTH, prove_ivc, verify_ivc,
};
use serde::{Deserialize, Serialize};

/// Domain tag for deriving the old chain's IVC genesis root from its federation id.
const OLD_GENESIS_DOMAIN: &str = "dregg-genesis-snapshot:old-genesis-root v1";
/// Domain tag for deriving a cell's state-history felt from its state commitment.
const CELL_STATE_DOMAIN: &str = "dregg-genesis-snapshot:cell-state-root v1";

/// Map a 32-byte commitment to a single BabyBear felt (domain-separated BLAKE3 → mod p).
///
/// This is the modeled projection of a 32-byte commitment into the field the IVC
/// hash chain operates over. It is deterministic, so the exporter's and importer's
/// derivations agree.
fn felt_from_bytes(domain: &str, bytes: &[u8; 32]) -> BabyBear {
    let d = blake3::derive_key(domain, bytes);
    let v = u32::from_le_bytes([d[0], d[1], d[2], d[3]]);
    BabyBear::new(v % BABYBEAR_P)
}

/// The OLD chain's IVC genesis root — the `initial_root` every carried cell's
/// history proof starts from. Derived from the source federation id so a proof
/// minted against a different old chain will not verify here.
fn old_genesis_root(source_federation_id: &FederationId) -> BabyBear {
    felt_from_bytes(OLD_GENESIS_DOMAIN, source_federation_id)
}

/// The IVC final root that binds a cell's CURRENT state — the last root in its
/// history chain. A forged cell (mutated state) yields a different felt, so a
/// history proof minted for the honest cell will not bind the forged one.
fn cell_state_root(cell: &Cell) -> BabyBear {
    felt_from_bytes(CELL_STATE_DOMAIN, &cell.state_commitment())
}

/// Build the IVC proof of a cell's history from the OLD chain's genesis to its
/// current state.
///
/// `prior_state_commitments` is the (modeled) sequence of the cell's state
/// commitments at each historical turn, oldest first, EXCLUDING the current
/// state. The chain walks: `old_genesis_root → felt(prior_0) → … → felt(prior_k)
/// → cell_state_root(current)`, so the proof's `final_root` binds the cell's
/// present state and its `initial_root` binds the old genesis.
///
/// Each step is a real [`FoldDelta`] (a no-removal fold from
/// [`create_test_fold`], whose roots we set to walk the history), and the whole
/// chain is proven by the real [`prove_ivc`].
fn build_history_proof(
    source_federation_id: &FederationId,
    cell: &Cell,
    prior_state_commitments: &[[u8; 32]],
) -> Result<IvcProof, SnapshotError> {
    let genesis = old_genesis_root(source_federation_id);

    // History roots: each prior state's felt, then the CURRENT state felt.
    let mut roots: Vec<BabyBear> = prior_state_commitments
        .iter()
        .map(|s| felt_from_bytes(CELL_STATE_DOMAIN, s))
        .collect();
    roots.push(cell_state_root(cell));

    if roots.len() as u32 > MAX_FOLD_DEPTH {
        return Err(SnapshotError::HistoryTooLong {
            steps: roots.len(),
            max: MAX_FOLD_DEPTH as usize,
        });
    }

    // Chain the roots into fold deltas: delta[i].old_root == delta[i-1].new_root.
    let mut deltas = Vec::with_capacity(roots.len());
    let mut prev = genesis;
    for r in roots {
        // A valid single fold (0 removals, 1 check) whose roots we overwrite to
        // walk this cell's history. The fold's checks-commitment / trace stay
        // internally consistent because the AIR recomputes them from the roots.
        let mut w = create_test_fold(0, 1);
        w.old_root = prev;
        w.new_root = r;
        deltas.push(FoldDelta::new(w));
        prev = r;
    }

    prove_ivc(genesis, deltas).ok_or(SnapshotError::ProofGeneration)
}

/// One carried cell in a [`GenesisSnapshot`]: the full cell, its content-address,
/// a cross-epoch migration voucher, and an IVC proof of its history-from-old-genesis.
///
/// (No `PartialEq`/`Eq`: [`IvcProof`] does not implement them.)
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct SnapshotEntry {
    /// The full cell state carried forward.
    pub cell: Cell,
    /// The content-addressed id declared for this cell. Import recomputes
    /// `cell.id()` and refuses on mismatch, so the address is stable and honest.
    pub content_address: CellId,
    /// The cross-epoch migration voucher — the vat-migration primitive
    /// ([`Cell::migration_voucher`](dregg_cell::Cell::migration_voucher)) reused
    /// with `from = old federation id`, `to = new (fresh-genesis) federation id`.
    /// It binds the exact pre-freeze `state_commitment`, so a state forged after
    /// freeze is caught independently of the IVC leg.
    pub voucher: MigrationVoucher,
    /// IVC proof that this cell's state followed a valid history from the OLD
    /// chain's genesis to its present state.
    pub history: IvcProof,
}

/// A frozen EXPORT of an old chain's cell-set, minted to seed a fresh genesis.
///
/// (No `PartialEq`/`Eq`: its entries carry an [`IvcProof`], which has neither.)
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct GenesisSnapshot {
    /// The OLD chain's federation id (committee epoch N).
    pub source_federation_id: FederationId,
    /// The fresh genesis's federation id (committee epoch N+1). Bound into every
    /// voucher; import refuses a snapshot whose target is not the seeding chain.
    pub target_federation_id: FederationId,
    /// The old-chain height at which the cell-set was frozen and exported.
    pub frozen_at_height: u64,
    /// The carried cells.
    pub entries: Vec<SnapshotEntry>,
}

impl GenesisSnapshot {
    /// FREEZE + EXPORT: build a snapshot of `cells` (each paired with its prior
    /// state-commitment history) targeting the fresh-genesis `target_federation_id`.
    ///
    /// This models the operator flow of a carry-forward re-genesis: mint the new
    /// committee keys first (→ `target_federation_id`), then freeze the old
    /// cell-set and export it toward that new chain.
    pub fn export(
        source_federation_id: FederationId,
        target_federation_id: FederationId,
        frozen_at_height: u64,
        cells: &[(Cell, Vec<[u8; 32]>)],
    ) -> Result<Self, SnapshotError> {
        let mut entries = Vec::with_capacity(cells.len());
        for (cell, prior) in cells {
            // The vat-migration voucher, generalized cross-epoch: from = old fed,
            // to = fresh-genesis fed, mode preserved, height = freeze height.
            let voucher = cell
                .migration_voucher(
                    source_federation_id,
                    target_federation_id,
                    cell.mode.clone(),
                    frozen_at_height,
                )
                .map_err(SnapshotError::Voucher)?;
            let history = build_history_proof(&source_federation_id, cell, prior)?;
            entries.push(SnapshotEntry {
                content_address: cell.id(),
                voucher,
                history,
                cell: cell.clone(),
            });
        }
        Ok(Self {
            source_federation_id,
            target_federation_id,
            frozen_at_height,
            entries,
        })
    }
}

/// The result of seeding a fresh genesis from a snapshot: the new federation id
/// plus the carried-forward cells (each having re-addressed identically and had
/// its history validated). An empty snapshot yields an empty cell-set — the
/// baseline WIPE behaviour when there is nothing to carry.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SeededGenesis {
    /// The fresh chain's federation id.
    pub new_federation_id: FederationId,
    /// The carried-forward, validated cells — ready to be materialized as the
    /// fresh genesis's initial cell-set.
    pub cells: Vec<Cell>,
}

/// IMPORT / SEED: validate every entry of `snapshot` and produce the fresh
/// genesis's carried-forward cell-set.
///
/// Refuses (returns `Err`) if the snapshot targets a different destination epoch,
/// or if ANY entry fails validation (forged cell / broken history / non-stable
/// address). The honest snapshot seeds cleanly.
pub fn seed_genesis(
    snapshot: &GenesisSnapshot,
    new_federation_id: FederationId,
) -> Result<SeededGenesis, ImportError> {
    // Cross-epoch destination binding: the snapshot must have been minted FOR
    // this fresh chain (the vouchers' `to` == this federation id).
    if snapshot.target_federation_id != new_federation_id {
        return Err(ImportError::WrongDestination);
    }

    let mut cells = Vec::with_capacity(snapshot.entries.len());
    for (index, entry) in snapshot.entries.iter().enumerate() {
        validate_entry(snapshot, entry).map_err(|kind| ImportError::Entry { index, kind })?;
        cells.push(entry.cell.clone());
    }

    Ok(SeededGenesis {
        new_federation_id,
        cells,
    })
}

/// Validate a single carried cell. Layered so that a forged cell trips at least
/// one independent check.
fn validate_entry(snapshot: &GenesisSnapshot, entry: &SnapshotEntry) -> Result<(), EntryReject> {
    // 1. Content-address stability: the imported cell must re-address identically.
    //    `verify_id_integrity` recomputes `derive_raw(public_key, token_id)` and
    //    compares to the carried id (federation/epoch-independent), and the
    //    declared `content_address` must match it too.
    if !entry.cell.verify_id_integrity() {
        return Err(EntryReject::IdentityBroken);
    }
    if entry.content_address != entry.cell.id() {
        return Err(EntryReject::AddressMismatch);
    }

    // 2. Cross-epoch migration voucher binding (the vat-migration primitive):
    //    the voucher must bind THIS cell's id + exact state commitment, and the
    //    old→new federation pair. A state forged after freeze changes
    //    `state_commitment` and is caught here, independent of the IVC leg.
    let state_commitment = entry.cell.state_commitment();
    if entry.voucher.cell_id != entry.cell.id()
        || entry.voucher.state_commitment != state_commitment
        || entry.voucher.from != snapshot.source_federation_id
        || entry.voucher.to != snapshot.target_federation_id
    {
        return Err(EntryReject::VoucherMismatch);
    }

    // 3. IVC history-from-old-genesis: verify the proof against the old chain's
    //    genesis root, AND check its final root binds THIS cell's present state.
    let genesis = old_genesis_root(&snapshot.source_federation_id);
    match verify_ivc(&entry.history, Some(genesis)) {
        IvcVerification::Valid => {}
        other => return Err(EntryReject::HistoryInvalid(other)),
    }
    if entry.history.final_root != cell_state_root(&entry.cell) {
        return Err(EntryReject::HistoryStateMismatch);
    }

    Ok(())
}

/// Errors from building a snapshot (EXPORT side).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SnapshotError {
    /// The underlying vat-migration voucher could not be minted (terminal / broken cell).
    Voucher(CellMigrationError),
    /// The modeled history exceeds the IVC fold-depth bound.
    HistoryTooLong { steps: usize, max: usize },
    /// The IVC prover rejected the history chain (should not happen for a well-formed chain).
    ProofGeneration,
}

impl core::fmt::Display for SnapshotError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Voucher(e) => write!(f, "migration voucher mint failed: {e}"),
            Self::HistoryTooLong { steps, max } => {
                write!(
                    f,
                    "history too long: {steps} steps exceeds fold-depth bound {max}"
                )
            }
            Self::ProofGeneration => f.write_str("IVC history proof generation failed"),
        }
    }
}

impl std::error::Error for SnapshotError {}

/// Errors from seeding a genesis (IMPORT side).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ImportError {
    /// The snapshot was minted for a different destination federation (epoch).
    WrongDestination,
    /// A specific entry was refused.
    Entry {
        /// Index of the offending entry in `snapshot.entries`.
        index: usize,
        /// Why it was refused.
        kind: EntryReject,
    },
}

impl core::fmt::Display for ImportError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::WrongDestination => {
                f.write_str("snapshot target federation does not match the seeding chain")
            }
            Self::Entry { index, kind } => write!(f, "snapshot entry {index} refused: {kind}"),
        }
    }
}

impl std::error::Error for ImportError {}

/// The specific reason a carried cell was refused on import.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EntryReject {
    /// `id != derive_raw(public_key, token_id)` — the cell does not re-address to its own id.
    IdentityBroken,
    /// The declared `content_address` does not match the recomputed `cell.id()`.
    AddressMismatch,
    /// The migration voucher does not bind this cell's id/state or the old→new federations.
    VoucherMismatch,
    /// The IVC history proof did not verify against the old chain's genesis.
    HistoryInvalid(IvcVerification),
    /// The IVC history's final root does not bind this cell's present state (forged state).
    HistoryStateMismatch,
}

impl core::fmt::Display for EntryReject {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::IdentityBroken => f.write_str("cell does not re-address to its own id"),
            Self::AddressMismatch => f.write_str("declared content-address does not recompute"),
            Self::VoucherMismatch => f.write_str("cross-epoch migration voucher binding broken"),
            Self::HistoryInvalid(v) => write!(f, "IVC history proof invalid: {v:?}"),
            Self::HistoryStateMismatch => {
                f.write_str("IVC history final root does not bind this cell's state (forged)")
            }
        }
    }
}

/// Recompute the content-address a cell would take in ANY chain/epoch. Exposed so
/// callers (and the demo) can demonstrate re-address stability directly.
pub fn recompute_content_address(cell: &Cell) -> CellId {
    CellId::derive_raw(cell.public_key(), cell.token_id())
}

#[cfg(test)]
mod tests;
