use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::sync::mpsc;

use serde::{Deserialize, Serialize};

use crate::capability::CapabilityRef;
use crate::cell::Cell;
use crate::id::CellId;
use crate::permissions::Permissions;
use crate::state::{FieldElement, STATE_SLOTS};

// =============================================================================
// Witness Freshness Types
// =============================================================================

/// A diff representing changes to a cell's Merkle path between two roots.
///
/// Used for witness freshness subscriptions: when the ledger root changes,
/// subscribers receive a diff that lets them update their local witness
/// (Merkle proof) without re-downloading the entire state.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct WitnessDiff {
    /// The cell whose witness path changed.
    pub cell_id: CellId,
    /// The old Merkle path (sibling hashes from leaf to root).
    pub old_path: Vec<[u8; 32]>,
    /// The new Merkle path (sibling hashes from leaf to root).
    pub new_path: Vec<[u8; 32]>,
    /// The new Merkle root after the change.
    pub new_root: [u8; 32],
}

/// A delta to apply to a single cell's state.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CellStateDelta {
    /// Field updates: (slot_index, new_value).
    pub field_updates: Vec<(usize, FieldElement)>,
    /// Whether to increment the nonce.
    pub nonce_increment: bool,
    /// Balance change (can be negative).
    pub balance_change: i64,
    /// Optional complete permission replacement.
    pub permission_changes: Option<Permissions>,
    /// Capabilities to grant.
    pub capability_grants: Vec<CapabilityRef>,
    /// Capability slots to revoke.
    pub capability_revocations: Vec<u32>,
}

impl CellStateDelta {
    /// Create an empty delta (no changes).
    pub fn empty() -> Self {
        CellStateDelta {
            field_updates: Vec::new(),
            nonce_increment: false,
            balance_change: 0,
            permission_changes: None,
            capability_grants: Vec::new(),
            capability_revocations: Vec::new(),
        }
    }
}

/// A set of changes to apply atomically to the ledger.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LedgerDelta {
    /// Cells to create.
    pub created: Vec<Cell>,
    /// Cells to update: (cell_id, delta).
    pub updated: Vec<(CellId, CellStateDelta)>,
    /// Computron transfers: (from, to, amount).
    pub computron_transfers: Vec<(CellId, CellId, u64)>,
}

impl LedgerDelta {
    /// Create an empty delta.
    pub fn new() -> Self {
        LedgerDelta {
            created: Vec::new(),
            updated: Vec::new(),
            computron_transfers: Vec::new(),
        }
    }
}

impl Default for LedgerDelta {
    fn default() -> Self {
        Self::new()
    }
}

/// A Merkle membership proof for a cell in the ledger.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MembershipProof {
    /// The cell ID this proof is for.
    pub cell_id: CellId,
    /// Hash of the cell's state (leaf hash).
    pub leaf_hash: [u8; 32],
    /// Sibling hashes along the path to the root (from leaf to root).
    pub path: Vec<([u8; 32], Side)>,
    /// The Merkle root this proof validates against.
    pub root: [u8; 32],
}

/// Which side a sibling is on in a Merkle proof path.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Side {
    Left,
    Right,
}

impl MembershipProof {
    /// Verify this membership proof.
    pub fn verify(&self) -> bool {
        let mut current = self.leaf_hash;
        for (sibling, side) in &self.path {
            let mut hasher = blake3::Hasher::new();
            match side {
                Side::Left => {
                    hasher.update(sibling);
                    hasher.update(&current);
                }
                Side::Right => {
                    hasher.update(&current);
                    hasher.update(sibling);
                }
            }
            current = *hasher.finalize().as_bytes();
        }
        current == self.root
    }
}

/// Errors that can occur when applying a ledger delta.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LedgerError {
    /// Attempted to create a cell that already exists.
    CellAlreadyExists(CellId),
    /// Attempted to update a cell that doesn't exist.
    CellNotFound(CellId),
    /// Invalid field index in a state update.
    InvalidFieldIndex { cell_id: CellId, index: usize },
    /// Insufficient balance for a transfer or deduction. `available` is
    /// SIGNED (THE EPOCH §5): an issuer well legitimately reads negative,
    /// and ordinary verbs refuse to take any cell below zero.
    InsufficientBalance {
        cell_id: CellId,
        available: i64,
        required: u64,
    },
    /// Balance overflow.
    BalanceOverflow { cell_id: CellId },
    /// Transfer source cell not found.
    TransferSourceNotFound(CellId),
    /// Transfer destination cell not found.
    TransferDestNotFound(CellId),
    /// Attempted to operate on a sovereign cell without providing a witness.
    SovereignWitnessRequired(CellId),
    /// The provided sovereign witness commitment does not match the stored commitment.
    SovereignCommitmentMismatch {
        cell_id: CellId,
        expected: [u8; 32],
        got: [u8; 32],
    },
    /// Attempted to register a sovereign cell that already exists (hosted or sovereign).
    SovereignAlreadyExists(CellId),
    /// The cell is not sovereign.
    NotSovereign(CellId),
    /// A ledger delta could not be applied (e.g. nonce overflow).
    InvalidDelta(String),
}

impl core::fmt::Display for LedgerError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            LedgerError::CellAlreadyExists(id) => write!(f, "cell already exists: {id}"),
            LedgerError::CellNotFound(id) => write!(f, "cell not found: {id}"),
            LedgerError::InvalidFieldIndex { cell_id, index } => {
                write!(f, "invalid field index {index} for cell {cell_id}")
            }
            LedgerError::InsufficientBalance {
                cell_id,
                available,
                required,
            } => {
                write!(
                    f,
                    "insufficient balance for cell {cell_id}: have {available}, need {required}"
                )
            }
            LedgerError::BalanceOverflow { cell_id } => {
                write!(f, "balance overflow for cell {cell_id}")
            }
            LedgerError::TransferSourceNotFound(id) => {
                write!(f, "transfer source not found: {id}")
            }
            LedgerError::TransferDestNotFound(id) => {
                write!(f, "transfer destination not found: {id}")
            }
            LedgerError::SovereignWitnessRequired(id) => {
                write!(f, "sovereign cell requires witness: {id}")
            }
            LedgerError::SovereignCommitmentMismatch {
                cell_id,
                expected,
                got,
            } => {
                write!(
                    f,
                    "sovereign commitment mismatch for cell {cell_id}: expected {:02x}{:02x}..., got {:02x}{:02x}...",
                    expected[0], expected[1], got[0], got[1]
                )
            }
            LedgerError::SovereignAlreadyExists(id) => {
                write!(f, "sovereign cell already exists: {id}")
            }
            LedgerError::NotSovereign(id) => {
                write!(f, "cell is not sovereign: {id}")
            }
            LedgerError::InvalidDelta(msg) => write!(f, "invalid delta: {msg}"),
        }
    }
}

impl std::error::Error for LedgerError {}

/// Metadata for a sovereign cell's ephemeral federation registration.
///
/// Sovereign cells exist locally on the agent and register with the federation
/// only when they need federation services (ordering, nullifier check, proving
/// to strangers). They can deregister at will or be automatically expired after
/// `ttl_blocks` of inactivity.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SovereignRegistration {
    /// Current state commitment (32-byte hash of the cell's local state).
    pub commitment: [u8; 32],
    /// Block height at which this cell was registered.
    pub registered_at: u64,
    /// Time-to-live in blocks. After `last_activity + ttl_blocks` the registration
    /// is eligible for automatic expiry.
    pub ttl_blocks: u64,
    /// Block height of the most recent activity (registration, commitment update,
    /// or any federation interaction that resets the timer).
    pub last_activity: u64,
    /// Optional verification key hash binding this cell to a deployed program.
    /// When set, proof-carrying turns for this cell are verified against the
    /// program in the ProgramRegistry identified by this VK hash.
    #[serde(default)]
    pub verification_key_hash: Option<[u8; 32]>,
    /// Stage 1 (`DESIGN-max-custom-effects.md`): per-cell maximum number of
    /// `Effect::Custom` slots allowed in a single turn. The verifier enforces
    /// `PI[CUSTOM_EFFECT_COUNT] <= max_custom_effects`; the AIR's Stage 1
    /// sum-check (Group 7) makes `PI[CUSTOM_EFFECT_COUNT]` algebraically
    /// binding to the trace.
    ///
    /// Default (when `None`):
    /// [`dregg_circuit::effect_vm::pi::MAX_CUSTOM_EFFECTS_DEFAULT`] (=4).
    /// Hard cap: [`dregg_circuit::effect_vm::pi::MAX_CUSTOM_EFFECTS_HARD_CAP`]
    /// (=64).
    #[serde(default)]
    pub max_custom_effects: Option<u8>,
    /// Sovereign-witness AIR teeth (SOVEREIGN-WITNESS-AIR-DESIGN.md §3.2):
    /// the Ed25519 public key that signs sovereign witnesses for this cell.
    /// The federation stores this at registration time so the verifier can
    /// recompute `PI[SOVEREIGN_WITNESS_KEY_COMMIT_BASE..+4]` independent of
    /// the cipherclerk's claim. `None` represents pre-AIR-teeth registrations;
    /// those proofs verify with zero-sentinel PI, which the AIR boundary
    /// accepts (sentinel agreement). Phase 1.5: existing call sites
    /// populate this field; the option type goes away in Stage 10.
    #[serde(default)]
    pub owner_public_key: Option<[u8; 32]>,
}

/// Default TTL for sovereign cell registrations (in blocks).
pub const DEFAULT_SOVEREIGN_TTL: u64 = 1000;

/// The accumulated, NOT-YET-MATERIALIZED Merkle work. A mutation records into
/// this and returns immediately — no hashing. The tree materializes lazily on the
/// first `root()`/`membership_proof()` after the mutation batch.
#[derive(Clone, Debug, PartialEq, Eq)]
enum Pending {
    /// The cached tree + root are current; `root()` is a free read.
    Clean,
    /// Only cell *values* changed (state mutations); the leaf *set* (positions)
    /// is unchanged. Materialize with one O(log N) `update_leaf` per id — a batch
    /// of O(k · log N), far cheaper than the O(N) full rebuild.
    Values(BTreeSet<CellId>),
    /// The leaf *set* changed (insert/remove → positions shift). Materialize with
    /// a single full O(N) rebuild (the per-id batch can't fix shifted positions).
    Structural,
}

impl Pending {
    /// Record a VALUE mutation of `id` (state changed, position unchanged).
    /// A pending structural rebuild already subsumes it.
    fn touch_value(&mut self, id: CellId) {
        match self {
            Pending::Clean => {
                let mut s = BTreeSet::new();
                s.insert(id);
                *self = Pending::Values(s);
            }
            Pending::Values(s) => {
                s.insert(id);
            }
            Pending::Structural => {}
        }
    }

    /// Record a STRUCTURAL mutation (insert/remove → a full rebuild is owed). It
    /// subsumes any pending value updates.
    fn touch_structural(&mut self) {
        *self = Pending::Structural;
    }
}

/// The world state: a collection of cells with a Merkle commitment.
///
/// The Merkle tree is **truly lazy and batched**: a mutation does NO tree work —
/// it only records what changed (a [`Pending`]). The tree (and root) materializes
/// only when `root()`/`membership_proof()` is called (the network/publish
/// boundary), and then with the MINIMAL recompute — a batch of O(log N) leaf
/// updates when only values changed, a single O(N) rebuild when the leaf set
/// changed. An internal/UI turn that never asks for a root pays ZERO hashing.
#[derive(Clone, Debug)]
pub struct Ledger {
    cells: HashMap<CellId, Cell>,
    /// Sovereign cells: federation stores only a 32-byte state commitment.
    /// The agent must provide the full cell state in each turn as a witness.
    sovereign_commitments: HashMap<CellId, [u8; 32]>,
    /// Ephemeral sovereign registrations with TTL metadata.
    /// Supersedes bare `sovereign_commitments` for cells that register via the
    /// on-demand federation registration API.
    sovereign_registrations: HashMap<CellId, SovereignRegistration>,
    /// Sorted leaf positions: CellId -> index in the leaf layer.
    leaf_positions: BTreeMap<[u8; 32], usize>,
    /// The Merkle tree nodes, indexed by level then position.
    /// Level 0 = leaves (padded to next power of two with zero hashes).
    /// Level N = root (single element).
    tree_levels: Vec<Vec<[u8; 32]>>,
    root: [u8; 32],
    /// THE TRULY-LAZY MERKLE STATE. Mutations do NO tree work — they only record
    /// WHAT changed here. The tree (and hence the root) materializes ONLY when
    /// someone actually asks for it (`root()` / `membership_proof()` — the network
    /// boundary), and even then with the MINIMAL recompute: a batch of O(log N)
    /// leaf updates when only cell *values* changed, a single full rebuild when
    /// the leaf *set* changed (insert/remove shift positions). An internal/UI turn
    /// that never publishes a root therefore pays ZERO hashing.
    pending: Pending,
    /// Witness freshness subscribers: cell_id -> senders.
    /// When the Merkle root changes, subscribers receive `WitnessDiff` updates
    /// containing the new path for their subscribed cell.
    witness_subscribers: HashMap<CellId, Vec<mpsc::Sender<WitnessDiff>>>,
    /// Monotonic per-cell sovereign-witness sequence.
    ///
    /// Each accepted `SovereignCellWitness` for a cell must carry
    /// `sequence == last_accepted_sequence + 1`. After execution, this map
    /// is bumped so a replay of the same witness is rejected even if the
    /// underlying state_commitment happens to round-trip back to its
    /// previous value (paranoia against any future commitment-collision
    /// path). Persisted alongside the sovereign commitment for the cell.
    sovereign_witness_sequence: HashMap<CellId, u64>,
    /// In-flight migration locks: a cell PREPAREd for relocation but not yet COMMITted. While a
    /// lock is present the cell is quiescent (rejects effects) and the local node retains the
    /// voucher it will COMMIT against. See [`crate::migration`].
    migration_locks: HashMap<CellId, crate::migration::MigrationLock>,
}

impl Ledger {
    /// Create an empty ledger.
    pub fn new() -> Self {
        Ledger {
            cells: HashMap::new(),
            sovereign_commitments: HashMap::new(),
            sovereign_registrations: HashMap::new(),
            leaf_positions: BTreeMap::new(),
            tree_levels: Vec::new(),
            root: Self::compute_empty_root(),
            pending: Pending::Clean,
            witness_subscribers: HashMap::new(),
            sovereign_witness_sequence: HashMap::new(),
            migration_locks: HashMap::new(),
        }
    }

    /// Get an immutable reference to a cell.
    pub fn get(&self, id: &CellId) -> Option<&Cell> {
        self.cells.get(id)
    }

    /// Get a mutable reference to a cell.
    ///
    /// Marks the tree as dirty since the cell's state may change. The Merkle
    /// tree will be lazily rebuilt on the next call to `root()`.
    ///
    /// Audit P1-6: prefer [`Ledger::update_with`] — `get_mut` hands out a raw
    /// `&mut Cell` and the caller can forget to maintain invariants (e.g. set
    /// dirty before returning, re-derive `id` if pubkey changed). The closure
    /// form scopes the mutation and runs an integrity check on exit.
    pub fn get_mut(&mut self, id: &CellId) -> Option<&mut Cell> {
        let result = self.cells.get_mut(id);
        if let Some(cell) = &result {
            // VALUE mutation: the leaf set is unchanged, so a batched O(log N)
            // leaf update suffices when the root is next asked for.
            // INVALIDATE the cell's leaf-digest cache BEFORE handing out the
            // `&mut` — the caller may write any (even `pub`) field, so the
            // cached leaf is conservatively dirty (the cell-leaf cache's
            // `&mut`-boundary completeness rule).
            cell.invalidate_leaf_cache();
            self.pending.touch_value(*id);
        }
        result
    }

    /// Apply a closure to a cell with automatic dirty-marking and identity-
    /// integrity checking.
    ///
    /// This is the preferred mutation API over `get_mut` (audit P1-6). After
    /// the closure runs, `verify_id_integrity` (P2-3) is asserted: if the
    /// closure changed `public_key` or `token_id` without updating `id`, the
    /// mutation is rejected and the cell is restored from a pre-mutation
    /// snapshot. Returns `Ok(R)` with the closure's return value, or
    /// `Err(LedgerError::InvalidDelta)` if integrity was broken.
    ///
    /// The cell is also restored on closure panic — callers that need to
    /// mutate must not panic for control flow.
    pub fn update_with<F, R>(&mut self, id: &CellId, f: F) -> Result<R, LedgerError>
    where
        F: FnOnce(&mut Cell) -> R,
    {
        // Snapshot for integrity rollback.
        let snapshot = match self.cells.get(id) {
            Some(c) => c.clone(),
            None => return Err(LedgerError::CellNotFound(*id)),
        };
        let cell = self.cells.get_mut(id).expect("cell present");
        // INVALIDATE the leaf-digest cache before the closure can mutate any
        // (even `pub`) field — the cell-leaf cache's `&mut`-boundary rule.
        cell.invalidate_leaf_cache();
        let result = f(cell);
        if !cell.verify_id_integrity() {
            // Restore and reject.
            *cell = snapshot;
            return Err(LedgerError::InvalidDelta(format!(
                "cell id integrity broken for {:?}: id must match derive_raw(public_key, token_id)",
                id
            )));
        }
        // VALUE mutation (the id is asserted unchanged by the integrity check
        // above, so the leaf position is stable): a batched leaf update suffices.
        self.pending.touch_value(*id);
        Ok(result)
    }

    /// Number of cells in the ledger.
    pub fn len(&self) -> usize {
        self.cells.len()
    }

    /// Whether the ledger is empty.
    pub fn is_empty(&self) -> bool {
        self.cells.is_empty()
    }

    /// Create a new hosted cell and insert it. Returns the CellId.
    ///
    /// The cell is created in Hosted mode since the ledger stores its full state.
    /// The Merkle tree rebuild is deferred until `root()` is called, making
    /// sequential inserts O(N) total instead of O(N^2).
    pub fn create_cell(&mut self, public_key: [u8; 32], token_id: [u8; 32]) -> CellId {
        let cell = Cell::new_hosted(public_key, token_id);
        let id = cell.id;
        self.cells.insert(id, cell);
        self.pending.touch_structural(); // a new leaf shifts positions
        id
    }

    /// Insert a pre-built cell. Returns Err if a cell with the same ID already exists.
    ///
    /// The Merkle tree rebuild is deferred until `root()` is called, making
    /// sequential inserts O(N) total instead of O(N^2).
    pub fn insert_cell(&mut self, cell: Cell) -> Result<CellId, LedgerError> {
        let id = cell.id;
        if self.cells.contains_key(&id) {
            return Err(LedgerError::CellAlreadyExists(id));
        }
        // INVALIDATE: an externally-built cell may carry a clone's leaf cache
        // that is stale if the caller mutated a `pub` field after the clone.
        // Cheap insurance; a fresh dirty cache only costs ONE BLAKE3 on first
        // `hash_cell`.
        cell.invalidate_leaf_cache();
        self.cells.insert(id, cell);
        self.pending.touch_structural(); // a new leaf shifts positions
        Ok(id)
    }

    /// Apply a delta to the ledger atomically.
    /// If any operation fails, the ledger is left unchanged.
    pub fn apply_delta(&mut self, delta: &LedgerDelta) -> Result<(), LedgerError> {
        // Validate with cumulative balance tracking.
        self.validate_delta(delta)?;

        // Clone the cells map — all mutations go to the clone.
        let mut new_cells = self.cells.clone();

        // Apply creations.
        for cell in &delta.created {
            new_cells.insert(cell.id, cell.clone());
        }

        // Apply updates.
        for (cell_id, state_delta) in &delta.updated {
            let cell = new_cells
                .get_mut(cell_id)
                .ok_or(LedgerError::CellNotFound(*cell_id))?;
            Self::apply_cell_delta(cell, state_delta, cell_id)?;
        }

        // Apply transfers (on the already-modified clone). Transfers are
        // ORDINARY moves: the source may not go below zero (signed-well
        // discipline lives on the issuer-move verbs, not here).
        for &(from_id, to_id, amount) in &delta.computron_transfers {
            let amt = i64::try_from(amount)
                .map_err(|_| LedgerError::BalanceOverflow { cell_id: from_id })?;
            let from_balance = {
                let from_cell = new_cells
                    .get(&from_id)
                    .ok_or(LedgerError::TransferSourceNotFound(from_id))?;
                if from_cell.state.balance < amt {
                    return Err(LedgerError::InsufficientBalance {
                        cell_id: from_id,
                        available: from_cell.state.balance,
                        required: amount,
                    });
                }
                from_cell.state.balance - amt
            };
            {
                let from_cell = new_cells.get_mut(&from_id).unwrap();
                // INVALIDATE: this writes `state.balance` directly (pub field).
                from_cell.invalidate_leaf_cache();
                from_cell.state.balance = from_balance;
            }

            let to_cell = new_cells
                .get_mut(&to_id)
                .ok_or(LedgerError::TransferDestNotFound(to_id))?;
            // INVALIDATE: this writes `state.balance` directly (pub field).
            to_cell.invalidate_leaf_cache();
            to_cell.state.balance = to_cell
                .state
                .balance
                .checked_add(amt)
                .ok_or(LedgerError::BalanceOverflow { cell_id: to_id })?;
        }

        // All succeeded — swap in the new state atomically.
        self.cells = new_cells;

        // TRULY LAZY: do NO tree work here — just record what changed. The tree
        // materializes (minimally) on the next `root()`/`membership_proof()`.
        // Creations shift leaf positions ⇒ a full rebuild is owed (structural);
        // pure updates/transfers only change values ⇒ a batched leaf update.
        if !delta.created.is_empty() {
            self.pending.touch_structural();
        } else {
            for (id, _) in &delta.updated {
                self.pending.touch_value(*id);
            }
            for &(from_id, to_id, _) in &delta.computron_transfers {
                self.pending.touch_value(from_id);
                self.pending.touch_value(to_id);
            }
        }
        Ok(())
    }

    /// Validate that a delta can be applied without errors.
    /// Tracks cumulative balance effects across all operations so that a cell
    /// appearing in both `updated` and `computron_transfers` is checked correctly.
    fn validate_delta(&self, delta: &LedgerDelta) -> Result<(), LedgerError> {
        // Build a set of cells being created in this delta for reference.
        let mut created_cells: HashMap<CellId, &Cell> = HashMap::new();
        for cell in &delta.created {
            if self.cells.contains_key(&cell.id) {
                return Err(LedgerError::CellAlreadyExists(cell.id));
            }
            created_cells.insert(cell.id, cell);
        }

        // Helper: look up a cell in either the existing ledger or the delta's created set.
        let lookup = |id: &CellId| -> Option<&Cell> {
            self.cells
                .get(id)
                .or_else(|| created_cells.get(id).copied())
        };

        // Track running balances per cell (cumulative across all operations).
        // Initialized lazily from the cell's current balance on first access.
        // SIGNED: a well cell may start negative; ordinary verbs still refuse
        // to push any balance below zero.
        let mut running_balances: HashMap<CellId, i64> = HashMap::new();

        let get_running_balance =
            |balances: &mut HashMap<CellId, i64>, id: &CellId| -> Option<i64> {
                if let Some(&b) = balances.get(id) {
                    Some(b)
                } else {
                    // Initialize from current state.
                    let cell = lookup(id)?;
                    balances.insert(*id, cell.state.balance);
                    Some(cell.state.balance)
                }
            };

        // Check updates reference existing cells and validate cumulative balance.
        for (cell_id, state_delta) in &delta.updated {
            let cell = lookup(cell_id).ok_or(LedgerError::CellNotFound(*cell_id))?;

            // Validate field indices.
            for &(index, _) in &state_delta.field_updates {
                if index >= STATE_SLOTS {
                    return Err(LedgerError::InvalidFieldIndex {
                        cell_id: *cell_id,
                        index,
                    });
                }
            }

            // Get or initialize running balance for this cell.
            let balance =
                get_running_balance(&mut running_balances, cell_id).unwrap_or(cell.state.balance);

            // Validate and apply balance change cumulatively (ORDINARY
            // discipline: a debit may not land below zero; mirrors
            // `CellState::apply_balance_change`).
            let new_balance = balance
                .checked_add(state_delta.balance_change)
                .ok_or(LedgerError::BalanceOverflow { cell_id: *cell_id })?;
            if state_delta.balance_change < 0 && new_balance < 0 {
                return Err(LedgerError::InsufficientBalance {
                    cell_id: *cell_id,
                    available: balance,
                    required: state_delta.balance_change.unsigned_abs(),
                });
            }
            running_balances.insert(*cell_id, new_balance);
        }

        // Check transfers using cumulative running balances (ordinary moves;
        // source may not go below zero).
        for &(from_id, to_id, amount) in &delta.computron_transfers {
            let amt = i64::try_from(amount)
                .map_err(|_| LedgerError::BalanceOverflow { cell_id: from_id })?;
            let from_balance = get_running_balance(&mut running_balances, &from_id)
                .ok_or(LedgerError::TransferSourceNotFound(from_id))?;
            if from_balance < amt {
                return Err(LedgerError::InsufficientBalance {
                    cell_id: from_id,
                    available: from_balance,
                    required: amount,
                });
            }
            running_balances.insert(from_id, from_balance - amt);

            let to_balance = get_running_balance(&mut running_balances, &to_id)
                .ok_or(LedgerError::TransferDestNotFound(to_id))?;
            let new_to = to_balance
                .checked_add(amt)
                .ok_or(LedgerError::BalanceOverflow { cell_id: to_id })?;
            running_balances.insert(to_id, new_to);
        }

        Ok(())
    }

    /// Apply a CellStateDelta to a cell (assumes validation passed).
    fn apply_cell_delta(
        cell: &mut Cell,
        delta: &CellStateDelta,
        cell_id: &CellId,
    ) -> Result<(), LedgerError> {
        // INVALIDATE the leaf-digest cache: this mutates the cell's state /
        // permissions / capabilities directly through `pub` fields. The cell
        // was `clone`d into `new_cells` carrying a (valid-for-old-bytes) cache;
        // clear it so the next `hash_cell` re-absorbs the new bytes.
        cell.invalidate_leaf_cache();
        // Field updates.
        for &(index, ref value) in &delta.field_updates {
            if index >= STATE_SLOTS {
                return Err(LedgerError::InvalidFieldIndex {
                    cell_id: *cell_id,
                    index,
                });
            }
            cell.state.fields[index] = *value;
        }

        // Nonce.
        if delta.nonce_increment {
            // Audit P2-2: checked_add returns false on overflow. Refuse to
            // apply the delta rather than silently wrapping.
            if !cell.state.increment_nonce() {
                return Err(LedgerError::InvalidDelta(format!(
                    "nonce overflow for cell {:?}",
                    cell_id
                )));
            }
        }

        // Balance.
        if !cell.state.apply_balance_change(delta.balance_change) {
            if delta.balance_change < 0 {
                return Err(LedgerError::InsufficientBalance {
                    cell_id: *cell_id,
                    available: cell.state.balance,
                    required: delta.balance_change.unsigned_abs(),
                });
            } else {
                return Err(LedgerError::BalanceOverflow { cell_id: *cell_id });
            }
        }

        // Permissions.
        if let Some(ref new_perms) = delta.permission_changes {
            cell.permissions = new_perms.clone();
        }

        // Capability grants (preserving all fields including expires_at).
        for cap_ref in &delta.capability_grants {
            cell.capabilities.grant_full(
                cap_ref.target,
                cap_ref.permissions.clone(),
                cap_ref.breadstuff,
                cap_ref.expires_at,
            );
        }

        // Capability revocations.
        for &slot in &delta.capability_revocations {
            cell.capabilities.revoke(slot);
        }

        Ok(())
    }

    /// Force the lazy Merkle state to materialize: collapse the accumulated
    /// [`Pending`] into the cached tree + root with the MINIMAL recompute.
    ///   * `Clean` → nothing.
    ///   * `Values(set)` → a batch of O(log N) `update_leaf` (positions unchanged),
    ///     unless the tree was never built (then a full rebuild).
    ///   * `Structural` → a single O(N) full rebuild (positions shifted).
    ///
    /// Idempotent; leaves `pending == Clean`.
    fn materialize(&mut self) {
        match std::mem::replace(&mut self.pending, Pending::Clean) {
            Pending::Clean => {}
            Pending::Structural => self.rebuild_tree(),
            Pending::Values(ids) => {
                if self.tree_levels.is_empty() {
                    // No materialized tree to patch — full build (rare; e.g. a
                    // value touch recorded before the first root()).
                    self.rebuild_tree();
                } else {
                    for id in &ids {
                        self.update_leaf(id);
                    }
                }
            }
        }
    }

    /// Get the current Merkle root.
    ///
    /// MATERIALIZES the lazy Merkle state (the only place, besides
    /// `membership_proof`, that touches the tree). This is the network/publish
    /// boundary: an internal turn that never calls `root()` paid no hashing.
    pub fn root(&mut self) -> [u8; 32] {
        self.materialize();
        self.root
    }

    /// Get the current Merkle root without triggering a rebuild.
    ///
    /// WARNING: This may return a stale root if mutations have occurred since
    /// the last rebuild. Use only when you know the tree is up-to-date (e.g.,
    /// immediately after construction or after calling `root()`).
    pub fn root_cached(&self) -> [u8; 32] {
        self.root
    }

    /// Whether the cached tree + root are current (no pending Merkle work). When
    /// true, `root_cached()` / the stored paths are valid without materializing.
    fn is_clean(&self) -> bool {
        self.pending == Pending::Clean
    }

    /// Generate a membership proof for a cell using the stored tree.
    ///
    /// Triggers a tree rebuild if the ledger is dirty.
    pub fn membership_proof(&mut self, id: &CellId) -> Option<MembershipProof> {
        if !self.cells.contains_key(id) {
            return None;
        }

        self.materialize();

        let cell = self.cells.get(id).unwrap();
        // Cached: runs after `materialize()`; the proof leaf must equal the
        // tree's stored leaf (both via the same cell's cache).
        let leaf_hash = Self::hash_cell_cached(cell);

        // Look up position from stored leaf_positions.
        let pos = *self.leaf_positions.get(&id.0)?;

        // If tree is trivial (single leaf), no path needed.
        if self.tree_levels.len() <= 1 {
            return Some(MembershipProof {
                cell_id: *id,
                leaf_hash,
                path: Vec::new(),
                root: self.root,
            });
        }

        // Extract the authentication path from the stored tree levels.
        let mut path = Vec::new();
        let mut idx = pos;
        for level in 0..self.tree_levels.len() - 1 {
            let sibling_idx = if idx % 2 == 0 { idx + 1 } else { idx - 1 };
            let sibling_hash = self.tree_levels[level]
                .get(sibling_idx)
                .copied()
                .unwrap_or([0u8; 32]);
            let side = if idx % 2 == 0 {
                Side::Right
            } else {
                Side::Left
            };
            path.push((sibling_hash, side));
            idx /= 2;
        }

        Some(MembershipProof {
            cell_id: *id,
            leaf_hash,
            path,
            root: self.root,
        })
    }

    /// Incrementally update a single leaf and propagate changes to the root.
    /// O(log N) operation.
    fn update_leaf(&mut self, cell_id: &CellId) {
        let pos = match self.leaf_positions.get(&cell_id.0) {
            Some(&p) => p,
            None => return, // cell not in tree (shouldn't happen on hot path)
        };

        let cell = match self.cells.get(cell_id) {
            Some(c) => c,
            None => return,
        };

        // Cached: `update_leaf` is the hot per-touched-cell path; the cell's
        // leaf cache was invalidated at the ledger `&mut`-handoff seam.
        let leaf_hash = Self::hash_cell_cached(cell);
        self.tree_levels[0][pos] = leaf_hash;

        // Walk up the tree recomputing only affected parent nodes.
        let mut current_pos = pos;
        for level in 0..self.tree_levels.len() - 1 {
            let parent_pos = current_pos / 2;
            let left_child = current_pos & !1; // round down to even
            let right_child = left_child + 1;

            let left_hash = self.tree_levels[level][left_child];
            let right_hash = self.tree_levels[level]
                .get(right_child)
                .copied()
                .unwrap_or([0u8; 32]);

            let mut hasher = blake3::Hasher::new();
            hasher.update(&left_hash);
            hasher.update(&right_hash);
            self.tree_levels[level + 1][parent_pos] = *hasher.finalize().as_bytes();

            current_pos = parent_pos;
        }

        // Update cached root.
        self.root = *self.tree_levels.last().unwrap().first().unwrap();
    }

    /// Full rebuild of the Merkle tree from scratch.
    /// Called on structural changes (insert/remove) that alter leaf positions.
    /// Also clears the pending state (the tree is now current).
    fn rebuild_tree(&mut self) {
        self.pending = Pending::Clean;

        if self.cells.is_empty() {
            self.leaf_positions.clear();
            self.tree_levels.clear();
            self.root = Self::compute_empty_root();
            return;
        }

        // Collect and sort all cells by CellId bytes for deterministic ordering.
        let mut sorted_cells: Vec<(&CellId, &Cell)> = self.cells.iter().collect();
        sorted_cells.sort_by_key(|a| a.0.0);

        // Build leaf_positions map and leaf hashes.
        self.leaf_positions.clear();
        let mut leaves: Vec<[u8; 32]> = Vec::with_capacity(sorted_cells.len());
        for (i, (cid, cell)) in sorted_cells.iter().enumerate() {
            self.leaf_positions.insert(cid.0, i);
            // Cached: a structural rebuild re-hashes ALL cells, but an UNTOUCHED
            // cell's leaf cache is still valid (it was never invalidated), so
            // only the genuinely-mutated cells pay the BLAKE3 absorb.
            leaves.push(Self::hash_cell_cached(cell));
        }

        let n_leaves = leaves.len();
        if n_leaves == 1 {
            // Single leaf IS the root.
            self.tree_levels = vec![leaves.clone()];
            self.root = leaves[0];
            return;
        }

        // Pad to next power of two with zero hashes.
        let next_pow2 = n_leaves.next_power_of_two();
        leaves.resize(next_pow2, [0u8; 32]);

        // Build levels bottom-up.
        let mut levels: Vec<Vec<[u8; 32]>> = Vec::new();
        levels.push(leaves);

        loop {
            let current = levels.last().unwrap();
            if current.len() == 1 {
                break;
            }
            let mut next_level = Vec::with_capacity(current.len() / 2);
            for chunk in current.chunks(2) {
                let mut hasher = blake3::Hasher::new();
                hasher.update(&chunk[0]);
                hasher.update(&chunk[1]);
                next_level.push(*hasher.finalize().as_bytes());
            }
            levels.push(next_level);
        }

        self.root = levels.last().unwrap()[0];
        self.tree_levels = levels;
    }

    /// Full recompute of the Merkle root (validation/fallback).
    /// Equivalent to rebuild_tree but only returns the root without storing levels.
    #[cfg(test)]
    pub(crate) fn recompute_root_standalone(&self) -> [u8; 32] {
        if self.cells.is_empty() {
            return Self::compute_empty_root();
        }

        let mut all_hashes: Vec<(CellId, [u8; 32])> = self
            .cells
            .iter()
            .map(|(cid, c)| (*cid, Self::hash_cell(c)))
            .collect();
        all_hashes.sort_by_key(|a| a.0.0);

        let leaves: Vec<[u8; 32]> = all_hashes.iter().map(|(_, h)| *h).collect();
        Self::merkle_root(&leaves)
    }

    /// Compute Merkle root from a list of leaf hashes (used by standalone recompute).
    #[cfg(test)]
    fn merkle_root(leaves: &[[u8; 32]]) -> [u8; 32] {
        if leaves.is_empty() {
            return Self::compute_empty_root();
        }
        if leaves.len() == 1 {
            return leaves[0];
        }

        // Pad to power of two.
        let mut padded = leaves.to_vec();
        let next_pow2 = padded.len().next_power_of_two();
        padded.resize(next_pow2, [0u8; 32]);

        let mut current_level = padded;
        while current_level.len() > 1 {
            let mut next_level = Vec::new();
            for chunk in current_level.chunks(2) {
                let mut hasher = blake3::Hasher::new();
                hasher.update(&chunk[0]);
                hasher.update(&chunk[1]);
                next_level.push(*hasher.finalize().as_bytes());
            }
            current_level = next_level;
        }
        current_level[0]
    }

    /// Hash a cell for Merkle tree inclusion.
    ///
    /// Routes through `crate::commitment::compute_canonical_state_commitment`
    /// — the single source of truth for "what bytes commit to this cell." This
    /// closes audit P0-2 (three disjoint commitment schemes) and P2-4 (lossy
    /// delegation snapshot hashing): the canonical function hashes ALL
    /// security-relevant fields including full per-capability data inside
    /// `delegation.snapshot`.
    fn hash_cell(cell: &Cell) -> [u8; 32] {
        // ALWAYS FRESH. This is the cache-UNSAFE entry: it can be called on a
        // cell that was mutated outside the ledger's invalidation discipline
        // (the public `hash_cell_canonical` wrapper, the `recompute_root_standalone`
        // independent re-check). It never consults `leaf_cache`, so it can
        // never serve a stale leaf. The CACHED path is `hash_cell_cached`,
        // called ONLY from `update_leaf`/`rebuild_tree`, which run after the
        // ledger's `&mut`-handoff invalidation seams.
        crate::commitment::compute_canonical_state_commitment(cell)
    }

    /// The CACHED Merkle-leaf hash (`docs/INCREMENTAL-COMMITMENT.md` step 3).
    /// Called ONLY by `update_leaf`/`rebuild_tree` — the materialize path that
    /// runs strictly AFTER the ledger's `&mut`-handoff invalidation seams
    /// (`get_mut`/`update_with`/`apply_delta`/transfers/migrate-commit), so a
    /// hit is byte-identical to a fresh `compute_canonical_state_commitment`
    /// (pinned by the `leaf_digest_cache_matches_fresh` differential). A turn
    /// that touched a cell once re-absorbs nothing on later `root()` calls
    /// until the cell is next mutated.
    fn hash_cell_cached(cell: &Cell) -> [u8; 32] {
        cell.cached_leaf_digest()
    }

    /// Public wrapper for `hash_cell` used by tests that need to verify the
    /// canonical commitment is identical between `Cell::state_commitment` and
    /// `Ledger::hash_cell`. See `cell/src/commitment.rs::tests`.
    #[doc(hidden)]
    pub fn hash_cell_canonical(cell: &Cell) -> [u8; 32] {
        Self::hash_cell(cell)
    }

    /// Hash a single state constraint into the hasher for deterministic program hashing.
    ///
    /// Uses postcard canonical serialization rather than hand-rolled tag-and-fields
    /// matching, so the function is exhaustive-by-construction over the (now 21+
    /// variant) `StateConstraint` surface and doesn't need to be touched whenever
    /// new variants land.
    #[allow(dead_code)]
    fn hash_constraint(hasher: &mut blake3::Hasher, constraint: &crate::program::StateConstraint) {
        let encoded = postcard::to_allocvec(constraint).unwrap_or_default();
        hasher.update(&(encoded.len() as u64).to_le_bytes());
        hasher.update(&encoded);
    }

    /// The root of an empty tree.
    fn compute_empty_root() -> [u8; 32] {
        *blake3::hash(b"dregg-cell:empty-ledger").as_bytes()
    }

    /// Iterate over all cells.
    pub fn iter(&self) -> impl Iterator<Item = (&CellId, &Cell)> {
        self.cells.iter()
    }

    /// Check if a cell exists.
    pub fn contains(&self, id: &CellId) -> bool {
        self.cells.contains_key(id)
    }

    /// Remove a cell from the ledger. Returns the removed cell if it existed.
    ///
    /// The Merkle tree rebuild is deferred until `root()` is called.
    pub fn remove(&mut self, id: &CellId) -> Option<Cell> {
        let cell = self.cells.remove(id);
        if cell.is_some() {
            self.pending.touch_structural(); // a removed leaf shifts positions
        }
        cell
    }

    // =========================================================================
    // Sovereign cell support (Phase 1a)
    // =========================================================================

    /// Register a cell as sovereign, storing only its initial state commitment.
    ///
    /// The cell must not already exist in either the hosted cells or the sovereign
    /// commitments map.
    pub fn register_sovereign_cell(
        &mut self,
        id: CellId,
        initial_commitment: [u8; 32],
    ) -> Result<(), LedgerError> {
        if self.cells.contains_key(&id) || self.sovereign_commitments.contains_key(&id) {
            return Err(LedgerError::SovereignAlreadyExists(id));
        }
        self.sovereign_commitments.insert(id, initial_commitment);
        Ok(())
    }

    /// Get the stored commitment for a sovereign cell.
    pub fn get_sovereign_commitment(&self, id: &CellId) -> Option<&[u8; 32]> {
        self.sovereign_commitments.get(id)
    }

    /// Update the stored commitment for a sovereign cell after a verified transition.
    pub fn update_sovereign_commitment(
        &mut self,
        id: &CellId,
        new_commitment: [u8; 32],
    ) -> Result<(), LedgerError> {
        if !self.sovereign_commitments.contains_key(id) {
            return Err(LedgerError::NotSovereign(*id));
        }
        self.sovereign_commitments.insert(*id, new_commitment);
        Ok(())
    }

    /// Check whether a cell ID refers to a sovereign cell.
    pub fn is_sovereign(&self, id: &CellId) -> bool {
        self.sovereign_commitments.contains_key(id)
    }

    /// Last accepted sovereign-witness sequence for a cell.
    ///
    /// Returns 0 when no witness has ever been accepted for this cell. The
    /// next valid witness sequence is `last_accepted + 1`.
    pub fn last_sovereign_witness_sequence(&self, id: &CellId) -> u64 {
        self.sovereign_witness_sequence
            .get(id)
            .copied()
            .unwrap_or(0)
    }

    /// Record that a witness with `sequence` was accepted for `id`. Callers
    /// must validate monotonicity (`sequence == last + 1`) before calling.
    pub fn bump_sovereign_witness_sequence(&mut self, id: &CellId, sequence: u64) {
        self.sovereign_witness_sequence.insert(*id, sequence);
    }

    /// Move a hosted cell to sovereign mode. Stores only the state commitment
    /// and removes the full cell state from the hosted store.
    ///
    /// Returns the removed cell on success.
    pub fn make_sovereign(&mut self, id: &CellId) -> Result<Cell, LedgerError> {
        let cell = self
            .cells
            .remove(id)
            .ok_or(LedgerError::CellNotFound(*id))?;
        let commitment = cell.state_commitment();
        self.sovereign_commitments.insert(*id, commitment);
        self.pending.touch_structural(); // the cell left the hosted leaf set
        Ok(cell)
    }

    // =========================================================================
    // Ephemeral Sovereign Registration (on-demand federation registration)
    // =========================================================================

    /// Register a sovereign cell ephemerally with TTL metadata.
    ///
    /// The cell must not already exist as a hosted cell or have an existing
    /// sovereign registration. Returns an error if a conflict exists.
    pub fn register_sovereign_cell_ephemeral(
        &mut self,
        id: CellId,
        commitment: [u8; 32],
        current_height: u64,
        ttl_blocks: u64,
    ) -> Result<(), LedgerError> {
        self.register_sovereign_cell_with_vk(id, commitment, current_height, ttl_blocks, None)
    }

    /// Register a sovereign cell with an optional verification key hash binding
    /// it to a deployed program in the ProgramRegistry.
    pub fn register_sovereign_cell_with_vk(
        &mut self,
        id: CellId,
        commitment: [u8; 32],
        current_height: u64,
        ttl_blocks: u64,
        verification_key_hash: Option<[u8; 32]>,
    ) -> Result<(), LedgerError> {
        if self.cells.contains_key(&id)
            || self.sovereign_commitments.contains_key(&id)
            || self.sovereign_registrations.contains_key(&id)
        {
            return Err(LedgerError::SovereignAlreadyExists(id));
        }
        self.sovereign_registrations.insert(
            id,
            SovereignRegistration {
                commitment,
                registered_at: current_height,
                ttl_blocks,
                last_activity: current_height,
                verification_key_hash,
                max_custom_effects: None,
                owner_public_key: None,
            },
        );
        Ok(())
    }

    /// Deregister a sovereign cell (voluntary removal).
    ///
    /// Removes the cell from `sovereign_registrations`. Returns an error if
    /// the cell is not registered as a sovereign cell.
    pub fn deregister_sovereign_cell(&mut self, id: &CellId) -> Result<(), LedgerError> {
        if self.sovereign_registrations.remove(id).is_some() {
            Ok(())
        } else if self.sovereign_commitments.remove(id).is_some() {
            // Also allow deregistering from the legacy bare-commitment map.
            Ok(())
        } else {
            Err(LedgerError::NotSovereign(*id))
        }
    }

    /// Update the commitment for an ephemerally registered sovereign cell.
    ///
    /// Verifies that `old_commitment` matches the stored value, then updates
    /// to `new_commitment` and resets the TTL activity counter.
    pub fn update_sovereign_registration_commitment(
        &mut self,
        id: &CellId,
        old_commitment: [u8; 32],
        new_commitment: [u8; 32],
        current_height: u64,
    ) -> Result<(), LedgerError> {
        if let Some(reg) = self.sovereign_registrations.get_mut(id) {
            if reg.commitment != old_commitment {
                return Err(LedgerError::SovereignCommitmentMismatch {
                    cell_id: *id,
                    expected: reg.commitment,
                    got: old_commitment,
                });
            }
            reg.commitment = new_commitment;
            reg.last_activity = current_height;
            Ok(())
        } else {
            Err(LedgerError::NotSovereign(*id))
        }
    }

    /// Get the sovereign registration metadata for a cell.
    pub fn get_sovereign_registration(&self, id: &CellId) -> Option<&SovereignRegistration> {
        self.sovereign_registrations.get(id)
    }

    /// Expire sovereign registrations that have exceeded their TTL.
    ///
    /// Removes all registrations where `current_height - last_activity > ttl_blocks`.
    /// Returns the number of expired registrations removed.
    pub fn expire_sovereign_registrations(&mut self, current_height: u64) -> usize {
        let before = self.sovereign_registrations.len();
        self.sovereign_registrations
            .retain(|_, reg| current_height.saturating_sub(reg.last_activity) <= reg.ttl_blocks);
        before - self.sovereign_registrations.len()
    }

    /// Check whether a cell has an active ephemeral sovereign registration.
    pub fn is_sovereign_registered(&self, id: &CellId) -> bool {
        self.sovereign_registrations.contains_key(id)
    }

    // =========================================================================
    // Atomic cross-federation cell migration (two-step handoff). See
    // `crate::migration` for the protocol description and the no-double-existence
    // / authority-conservation guarantees.
    // =========================================================================

    /// Whether a cell is currently locked for an in-flight migration (PREPAREd, not yet COMMITted).
    /// A locked cell is quiescent: the executor must reject effects targeting it.
    pub fn is_migration_locked(&self, id: &CellId) -> bool {
        self.migration_locks.contains_key(id)
    }

    /// The voucher of an in-flight migration for `id`, if any.
    pub fn migration_voucher_for(
        &self,
        id: &CellId,
    ) -> Option<&crate::migration::MigrationVoucher> {
        self.migration_locks.get(id).map(|l| &l.voucher)
    }

    /// **PREPARE** (source side). Lock a hosted cell for relocation to federation `to` in
    /// `target_mode`, minting the [`crate::migration::MigrationVoucher`] the destination will accept.
    /// The cell remains in the ledger (still `Live` in history) but becomes quiescent — a lock is
    /// recorded so the executor rejects further effects until COMMIT.
    ///
    /// Re-preparing a cell that is already locked, terminal, or not present is rejected — so a cell
    /// can be in flight to at most one destination at a time (a precondition of no-double-existence).
    pub fn migrate_prepare(
        &mut self,
        id: &CellId,
        from: crate::migration::FederationId,
        to: crate::migration::FederationId,
        target_mode: crate::cell::CellMode,
        prepared_at: u64,
    ) -> Result<crate::migration::MigrationVoucher, crate::migration::MigrationError> {
        if self.migration_locks.contains_key(id) {
            return Err(crate::migration::MigrationError::NotMigratable);
        }
        let cell = self
            .cells
            .get(id)
            .ok_or(crate::migration::MigrationError::SourceNotFound(*id))?;
        let voucher = cell.migration_voucher(from, to, target_mode, prepared_at)?;
        self.migration_locks.insert(
            *id,
            crate::migration::MigrationLock {
                voucher: voucher.clone(),
            },
        );
        Ok(voucher)
    }

    /// **ACCEPT** (destination side). Install a migrating cell into *this* ledger under the
    /// authority of `voucher`, taking custody. Returns the receipt the source consumes at COMMIT.
    ///
    /// Rejects:
    /// * a destination that already holds the cell ([`crate::migration::MigrationError::DestinationOccupied`])
    ///   — the core no-double-existence gate;
    /// * a voucher addressed to a different federation than `this_federation`
    ///   ([`crate::migration::MigrationError::WrongDestination`]);
    /// * a `cell` whose canonical commitment differs from the voucher's bound `state_commitment`
    ///   ([`crate::migration::MigrationError::StateMismatch`]) — authority cannot be inflated en
    ///   route;
    /// * a `cell` whose id does not match the voucher or whose identity integrity is broken.
    ///
    /// On success the cell is installed `Live` with `mode = voucher.target_mode`. (For a Sovereign
    /// target only the commitment is registered; the full state is not retained.)
    pub fn migrate_accept(
        &mut self,
        voucher: &crate::migration::MigrationVoucher,
        cell: Cell,
        this_federation: crate::migration::FederationId,
        accepted_at: u64,
    ) -> Result<crate::migration::MigrationReceipt, crate::migration::MigrationError> {
        use crate::cell::CellMode;
        use crate::migration::{MigrationError, MigrationReceipt};

        if voucher.to != this_federation {
            return Err(MigrationError::WrongDestination);
        }
        if cell.id() != voucher.cell_id {
            return Err(MigrationError::StateMismatch);
        }
        if !cell.verify_id_integrity() {
            return Err(MigrationError::IdentityBroken(cell.id()));
        }
        if cell.state_commitment() != voucher.state_commitment {
            return Err(MigrationError::StateMismatch);
        }
        // No-double-existence: refuse if the destination already holds this cell in ANY custody
        // table (hosted, sovereign-commitment, or sovereign-registration).
        let id = cell.id();
        if self.cells.contains_key(&id)
            || self.sovereign_commitments.contains_key(&id)
            || self.sovereign_registrations.contains_key(&id)
        {
            return Err(MigrationError::DestinationOccupied(id));
        }

        // Install the cell at the destination in the requested mode.
        match voucher.target_mode {
            CellMode::Hosted => {
                let mut installed = cell;
                // INVALIDATE: mode/lifecycle are overwritten below (pub fields)
                // and the incoming cell may carry a clone's stale cache.
                installed.invalidate_leaf_cache();
                installed.mode = CellMode::Hosted;
                installed.lifecycle = crate::lifecycle::CellLifecycle::Live;
                self.cells.insert(id, installed);
                self.pending.touch_structural(); // a new leaf shifts positions
            }
            CellMode::Sovereign => {
                // Sovereign target: register only the commitment.
                self.sovereign_commitments
                    .insert(id, voucher.state_commitment);
            }
        }

        Ok(MigrationReceipt {
            cell_id: id,
            voucher_hash: voucher.voucher_hash(),
            accepted_by: this_federation,
            accepted_at,
        })
    }

    /// **COMMIT** (source side). Consume a destination [`crate::migration::MigrationReceipt`] and
    /// finalize the relocation: the source cell is tombstoned to
    /// [`crate::lifecycle::CellLifecycle::Migrated`] (terminal — it can never accept effects again
    /// or be re-migrated) and the in-flight lock is cleared. After COMMIT the destination's copy is
    /// the unique live home.
    ///
    /// Rejects a receipt that does not match the in-flight voucher
    /// ([`crate::migration::MigrationError::ReceiptMismatch`]) and a cell with no migration in
    /// flight.
    pub fn migrate_commit(
        &mut self,
        id: &CellId,
        receipt: &crate::migration::MigrationReceipt,
    ) -> Result<(), crate::migration::MigrationError> {
        use crate::migration::MigrationError;
        let lock = self
            .migration_locks
            .get(id)
            .ok_or(MigrationError::ReceiptMismatch)?;
        let voucher = lock.voucher.clone();
        let cell = self
            .cells
            .get_mut(id)
            .ok_or(MigrationError::SourceNotFound(*id))?;
        // INVALIDATE the leaf cache: migrate_commit tombstones the lifecycle.
        cell.invalidate_leaf_cache();
        cell.migrate_commit(&voucher, receipt)?;
        self.migration_locks.remove(id);
        // VALUE mutation (the cell stays at its leaf position; only its state /
        // lifecycle changed): a batched leaf update suffices.
        self.pending.touch_value(*id);
        Ok(())
    }

    // =========================================================================
    // Witness Freshness (Phase 5 prerequisite)
    // =========================================================================

    /// Compute the witness diff between two roots for a specific cell.
    ///
    /// Returns the old and new Merkle paths along with the new root.
    /// The caller can use this to update a previously-cached Merkle proof
    /// without re-downloading the entire tree.
    ///
    /// NOTE: This triggers a tree rebuild if the ledger is dirty (to compute
    /// the current path). The `old_path` is computed from the provided
    /// `old_root` if it matches the prior state; otherwise this returns None.
    pub fn compute_witness_diff(
        &mut self,
        cell_id: &CellId,
        old_root: [u8; 32],
    ) -> Option<WitnessDiff> {
        if !self.cells.contains_key(cell_id) {
            return None;
        }

        // The old root should match the cached root before we rebuild.
        // If it doesn't, the caller's state is too stale for incremental update.
        let cached_root = self.root_cached();
        if cached_root != old_root && self.is_clean() {
            // Root mismatch and tree is current — caller's root is stale.
            return None;
        }

        // Get old path before any materialize (if tree is current, this is valid).
        let old_path = if self.is_clean() {
            self.extract_path(cell_id)
        } else {
            // Pending mutations — the old root predates them and we can't
            // reconstruct the old path from the pre-materialized tree.
            // Return empty old_path indicating the subscriber should do a full refresh.
            Vec::new()
        };

        // Ensure tree is up to date (minimal recompute).
        self.materialize();

        let new_path = self.extract_path(cell_id);
        let new_root = self.root;

        Some(WitnessDiff {
            cell_id: *cell_id,
            old_path,
            new_path,
            new_root,
        })
    }

    /// Subscribe to witness updates for a specific cell.
    ///
    /// Returns a `mpsc::Receiver<WitnessDiff>` that will receive diffs
    /// whenever the cell's Merkle path changes due to ledger mutations.
    ///
    /// The sender is stored internally; when the ledger root changes,
    /// all subscribers for affected cells are notified.
    pub fn subscribe_witness_updates(&mut self, cell_id: CellId) -> mpsc::Receiver<WitnessDiff> {
        let (tx, rx) = mpsc::channel();
        self.witness_subscribers
            .entry(cell_id)
            .or_insert_with(Vec::new)
            .push(tx);
        rx
    }

    /// Notify witness subscribers after a ledger mutation.
    ///
    /// Call this after `apply_delta()` or any mutation that changes the Merkle root.
    /// It computes diffs for all subscribed cells and sends them via channels.
    pub fn notify_witness_subscribers(&mut self) {
        if self.witness_subscribers.is_empty() {
            return;
        }

        // Ensure tree is materialized so we have valid paths.
        self.materialize();

        let new_root = self.root;

        // Collect cell IDs with subscribers (to avoid borrowing issues).
        let subscribed_ids: Vec<CellId> = self.witness_subscribers.keys().cloned().collect();

        for cell_id in subscribed_ids {
            if !self.cells.contains_key(&cell_id) {
                // Cell was removed — drop subscribers.
                self.witness_subscribers.remove(&cell_id);
                continue;
            }

            let new_path = self.extract_path(&cell_id);
            let diff = WitnessDiff {
                cell_id,
                old_path: Vec::new(), // Subscribers track their own old state.
                new_path,
                new_root,
            };

            // Send to all subscribers, removing any whose receiver has been dropped.
            if let Some(senders) = self.witness_subscribers.get_mut(&cell_id) {
                senders.retain(|tx| tx.send(diff.clone()).is_ok());
                if senders.is_empty() {
                    self.witness_subscribers.remove(&cell_id);
                }
            }
        }
    }

    /// Extract the Merkle path (sibling hashes) for a cell from the stored tree.
    fn extract_path(&self, cell_id: &CellId) -> Vec<[u8; 32]> {
        let pos = match self.leaf_positions.get(&cell_id.0) {
            Some(&p) => p,
            None => return Vec::new(),
        };

        if self.tree_levels.len() <= 1 {
            return Vec::new();
        }

        let mut path = Vec::new();
        let mut idx = pos;
        for level in 0..self.tree_levels.len() - 1 {
            let sibling_idx = if idx % 2 == 0 { idx + 1 } else { idx - 1 };
            let sibling_hash = self.tree_levels[level]
                .get(sibling_idx)
                .copied()
                .unwrap_or([0u8; 32]);
            path.push(sibling_hash);
            idx /= 2;
        }
        path
    }

    // =========================================================================
    // Snapshot Accessors (for checkpoint persistence)
    // =========================================================================

    /// Iterate over all sovereign commitments (bare, legacy style).
    ///
    /// Used by the persistence layer to serialize sovereign cell state into
    /// ledger checkpoints.
    pub fn iter_sovereign_commitments(&self) -> impl Iterator<Item = (&CellId, &[u8; 32])> {
        self.sovereign_commitments.iter()
    }

    /// Iterate over all ephemeral sovereign registrations.
    ///
    /// Used by the persistence layer to serialize sovereign registration state
    /// into ledger checkpoints.
    pub fn iter_sovereign_registrations(
        &self,
    ) -> impl Iterator<Item = (&CellId, &SovereignRegistration)> {
        self.sovereign_registrations.iter()
    }
}

impl Default for Ledger {
    fn default() -> Self {
        Self::new()
    }
}

// =============================================================================
// Sovereign History (IVC-compressed cell history)
// =============================================================================

/// Compressed history of a sovereign cell from genesis to current state.
///
/// A sovereign cell can produce a SINGLE proof covering its entire history.
/// A stranger who has never followed this cell's chain can verify one IVC proof
/// instead of replaying N individual state transitions.
///
/// The accumulated hash commits to the full sequence:
///   `accumulated_hash = Poseidon2(previous_hash || effects_hash || step_count)`
/// at each step, forming an irrevocable hash chain from genesis.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SovereignHistory {
    /// The state commitment at genesis (first registered commitment).
    pub genesis_commitment: [u8; 32],
    /// The current (most recent) state commitment.
    pub current_commitment: [u8; 32],
    /// Number of valid transitions applied since genesis.
    pub step_count: u64,
    /// Running Poseidon2 hash accumulating the full transition history.
    /// Each step: `new_hash = Poseidon2(old_hash || effects_hash_field || step_count)`.
    pub accumulated_hash: [u8; 32],
    /// Optional serialized IVC proof compressing all N transitions into one.
    /// When present, a verifier checks this single proof rather than replaying history.
    /// When absent, the cell has not yet compressed its history (lazy compression).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub ivc_proof: Option<Vec<u8>>,
}

impl SovereignHistory {
    /// Create a new history starting at genesis.
    pub fn new(genesis_commitment: [u8; 32]) -> Self {
        // Initial accumulated hash: H(genesis_commitment).
        let accumulated_hash = *blake3::hash(&genesis_commitment).as_bytes();
        SovereignHistory {
            genesis_commitment,
            current_commitment: genesis_commitment,
            step_count: 0,
            accumulated_hash,
            ivc_proof: None,
        }
    }

    /// Record a new transition step. This extends the hash chain but does NOT
    /// regenerate the IVC proof (that is an expensive operation done on demand).
    pub fn record_step(&mut self, new_commitment: [u8; 32], effects_hash: [u8; 32]) {
        self.step_count += 1;
        self.current_commitment = new_commitment;

        // Extend accumulated hash: H(old_hash || effects_hash || step_count_le_bytes)
        let mut hasher = blake3::Hasher::new();
        hasher.update(&self.accumulated_hash);
        hasher.update(&effects_hash);
        hasher.update(&self.step_count.to_le_bytes());
        self.accumulated_hash = *hasher.finalize().as_bytes();

        // Invalidate the IVC proof (stale after a new step).
        self.ivc_proof = None;
    }

    /// Attach a compressed IVC proof covering the full history.
    /// This is produced offline by the sovereign cell's owner.
    pub fn attach_ivc_proof(&mut self, proof: Vec<u8>) {
        self.ivc_proof = Some(proof);
    }

    /// Returns true if this history has a compressed IVC proof attached.
    pub fn has_ivc_proof(&self) -> bool {
        self.ivc_proof.is_some()
    }
}
