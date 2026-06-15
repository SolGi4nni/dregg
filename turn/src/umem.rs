//! umem: THE EXECUTOR-STATE BRIDGE — the live executor's state as a view of the ONE
//! universal map, and the live executor's turn as a Blum memory-op trace.
//!
//! The universal-map rotation's long pole (`docs/UNIVERSAL-MAP-ROTATION.md` §2.3/§3:
//! "the 3-verb executor-state bridge: RecordKernelState → the ONE map"). This module is
//! the Rust half of the bridge whose Lean keystone is
//! `metatheory/Dregg2/Exec/UniversalBridge.lean` (`uproj` + the three
//! `*_is_memory_program` agreement theorems):
//!
//!  1. **THE PROJECTION** ([`project_executor_state`] / [`project_ledger`]): every cell
//!     field and executor side-table entry lands at a `(domain, collection, key) ↦ value`
//!     cell of the unified address space — the same five domains as
//!     `Dregg2/Crypto/UniversalMemory.lean`'s `Domain` enum (registers · heap · caps ·
//!     nullifiers · index), with the same wire codes as `DescriptorIR2.domainCode`.
//!
//!  2. **THE TRACE EMITTER** ([`emit_trace`]): for a turn executed by the live executor,
//!     the journal (the undo log that already records every forest mutation with its
//!     prior value, in execution order) is re-read as the turn's Blum WRITE trace —
//!     per-op `(kind, addr, val, prev_val, prev_serial)` rows under the memcheck
//!     discipline (`Dregg2/Crypto/MemoryChecking.lean`). The fold of the emitted trace
//!     over the pre-state projection MUST equal the post-state projection
//!     ([`fold`] — checked eagerly; the executable shadow of the Lean agreement
//!     theorems), and every journal-recorded prior value is cross-checked against the
//!     running fold (drift between the journal and the projection refuses loudly).
//!
//! Wiring: recursion-gated, exactly like the umem circuit leg — the witness is produced
//! only when `TurnExecutor::umem_witness_enabled` is set; the live proving path is
//! untouched (v1 stays the only prover on the wire).
//!
//! ## The projection table (Rust side)
//!
//! | executor state                          | `UKey` collection        | domain     |
//! |-----------------------------------------|--------------------------|------------|
//! | cell existence (ledger membership)      | `Exist`                  | heap       |
//! | `CellState.fields[0..16]`               | `Field` (slot < 16)      | heap       |
//! | `CellState.fields_map` (keys ≥ 16)      | `Field` (slot ≥ 16)      | heap       |
//! | `CellState.balance`                     | `Balance`                | heap       |
//! | `CellState.nonce`                       | `Nonce`                  | heap       |
//! | `CellState.proved_state`                | `ProvedState`            | heap       |
//! | `Cell.lifecycle` (incl. death cert)     | `Lifecycle`              | heap       |
//! | `Cell.mode`                             | `Mode`                   | heap       |
//! | `Cell.{public_key, token_id}`           | `Identity`               | heap       |
//! | `CellState.field_visibility[slot]`      | `FieldVisibility`        | heap       |
//! | `CellState.commitments[slot]`           | `FieldCommitment`        | heap       |
//! | `CellState.swiss_table_root`            | `SwissTableRoot`         | heap       |
//! | `CellState.refcount_table_root`         | `RefcountTableRoot`      | heap       |
//! | `CellState.system_roots[i]`             | `SystemRoot`             | heap       |
//! | `CellState.heap_root`                   | `HeapRoot`               | heap       |
//! | sovereign commitments                   | `SovereignCommitment`    | heap       |
//! | `Cell.capabilities` (c-list slots)      | `CapSlot`                | caps       |
//! | `Cell.delegate`                         | `Delegate`               | caps       |
//! | `Cell.delegation` (snapshot)            | `DelegationSnapshot`     | caps       |
//! | `CellState.delegation_epoch`            | `DelegationEpoch`        | caps       |
//! | `Cell.permissions`                      | `Permissions`            | caps       |
//! | `Cell.verification_key`                 | `VerificationKey`        | caps       |
//! | `Cell.program` (slot-caveat registry)   | `Program`                | caps       |
//! | `factory_registry.descriptors`          | `Factory`                | caps       |
//! | `note_nullifiers`                       | `NoteNullifier`          | nullifiers |
//! | `bridged_nullifiers`                    | `BridgedNullifier`       | nullifiers |
//! | receipt log position (caller-supplied)  | `Receipt`                | index      |
//!
//! **Named exceptions** (documented non-cells, mirroring the Lean module's `registers`
//! exception):
//!  * `registers` domain — EMPTY: per-proof VM transients, never persistent state.
//!  * `CellState.fields_root` — NOT projected: it is the DERIVED commitment of
//!    `fields_map` (a boundary view in the universal-memory design, recomputed on every
//!    map write without its own journal entry; projecting it would double-count the
//!    `Field` plane).
//!  * the ledger Merkle tree / root — NOT projected: derived commitment over the cells.
//!  * rate-limit counters / budget gate — NOT projected: per-window executor metering,
//!    not consensus state (they never enter the state commitment).
//!  * the receipt log — owned by the node's MMR lane, not the executor; [`receipt_op`]
//!    lets the caller append the index-domain write when composing a whole-turn witness
//!    (the Lean side carries it as `RecChainedState.log`; adapter (b)
//!    `index_boundary_mroot_derived` covers its boundary commitment).

use std::collections::BTreeMap;

use dregg_cell::{
    Cell, CellId, FactoryRegistry, Ledger, lifecycle::CellLifecycle,
    note_bridge::BridgedNullifierSet, nullifier_set::NullifierSet, state::STATE_SLOTS,
};

use crate::journal::JournalEntry;

/// The five state domains — wire codes IDENTICAL to the Lean
/// `DescriptorIR2.domainCode` (registers 0 · heap 1 · caps 2 · nullifiers 3 · index 4).
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub enum UDomain {
    /// Per-proof VM register file — EMPTY in the persistent projection by design.
    Registers = 0,
    /// Per-cell record state (existence, fields, balances, lifecycle, roots).
    Heap = 1,
    /// Authority state (c-lists, delegation, permissions, programs, factories).
    Caps = 2,
    /// Insert-only sets (note nullifiers, bridged nullifiers).
    Nullifiers = 3,
    /// The append-only receipt index (the MMR-committed log).
    Index = 4,
}

impl UDomain {
    /// The wire code (the circuit's domain column value).
    pub fn code(self) -> u32 {
        self as u32
    }
}

/// The structured in-domain key — one constructor per state plane (the Rust twin of the
/// Lean `UniversalBridge.UKey`). The deployed realization is
/// `addr = hash[domain_tag, collection_id, key]`; the constructor IS that triple's
/// abstract content.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum UKey {
    // -- heap domain --------------------------------------------------------
    /// Cell existence (ledger membership bit).
    Exist(CellId),
    /// A cell record field: slots `< 16` are `fields[]`, slots `≥ 16` are `fields_map`.
    Field { cell: CellId, slot: u64 },
    /// The cell's signed balance.
    Balance(CellId),
    /// The cell's action nonce.
    Nonce(CellId),
    /// The proved-state flag.
    ProvedState(CellId),
    /// The whole lifecycle object (Live/Sealed/Destroyed…, death certificate included —
    /// the Lean table splits `lifecycle`/`deathCert`; the Rust collection carries the
    /// one canonical object, split at rotation lockstep).
    Lifecycle(CellId),
    /// Hosted/Sovereign mode.
    Mode(CellId),
    /// The cell's immutable identity pair `(public_key, token_id)`.
    Identity(CellId),
    /// Per-slot field visibility.
    FieldVisibility { cell: CellId, slot: u64 },
    /// Per-slot field commitment (for non-public fields).
    FieldCommitment { cell: CellId, slot: u64 },
    /// The CapTP swiss-table root carried in cell state.
    SwissTableRoot(CellId),
    /// The CapTP refcount-table root carried in cell state.
    RefcountTableRoot(CellId),
    /// One `system_roots` sub-block cell.
    SystemRoot { cell: CellId, index: u64 },
    /// The committed openable sorted-Poseidon2 heap root carried in cell state.
    HeapRoot(CellId),
    /// A sovereign cell's 32-byte state commitment.
    SovereignCommitment(CellId),
    // -- caps domain --------------------------------------------------------
    /// One c-list slot of a cell (the capability table).
    CapSlot { cell: CellId, slot: u32 },
    /// The delegation parent pointer.
    Delegate(CellId),
    /// The delegation snapshot (`DelegatedRef`).
    DelegationSnapshot(CellId),
    /// The parent-side delegation epoch counter.
    DelegationEpoch(CellId),
    /// The block height at which the cell's state was last committed.
    CommittedHeight(CellId),
    /// The cell's permissions object.
    Permissions(CellId),
    /// The cell's verification key.
    VerificationKey(CellId),
    /// The cell's program (the slot-caveat registry a factory installs).
    Program(CellId),
    /// A published factory descriptor, keyed by factory VK hash.
    Factory([u8; 32]),
    // -- nullifiers domain (insert-only sets) -------------------------------
    /// A local note-spend nullifier.
    NoteNullifier([u8; 32]),
    /// An inbound cross-federation bridged nullifier.
    BridgedNullifier([u8; 32]),
    // -- index domain --------------------------------------------------------
    /// The receipt log at a chronological position (caller-supplied; see module docs).
    Receipt(u64),
}

impl UKey {
    /// The domain this key lives in (the projection table's right column).
    pub fn domain(&self) -> UDomain {
        match self {
            UKey::Exist(_)
            | UKey::Field { .. }
            | UKey::Balance(_)
            | UKey::Nonce(_)
            | UKey::ProvedState(_)
            | UKey::Lifecycle(_)
            | UKey::Mode(_)
            | UKey::Identity(_)
            | UKey::FieldVisibility { .. }
            | UKey::FieldCommitment { .. }
            | UKey::SwissTableRoot(_)
            | UKey::RefcountTableRoot(_)
            | UKey::SystemRoot { .. }
            | UKey::HeapRoot(_)
            | UKey::SovereignCommitment(_)
            | UKey::CommittedHeight(_) => UDomain::Heap,
            UKey::CapSlot { .. }
            | UKey::Delegate(_)
            | UKey::DelegationSnapshot(_)
            | UKey::DelegationEpoch(_)
            | UKey::Permissions(_)
            | UKey::VerificationKey(_)
            | UKey::Program(_)
            | UKey::Factory(_) => UDomain::Caps,
            UKey::NoteNullifier(_) | UKey::BridgedNullifier(_) => UDomain::Nullifiers,
            UKey::Receipt(_) => UDomain::Index,
        }
    }

    /// The cell a heap/caps-plane key belongs to (`None` for non-cell planes). Used to
    /// expand a `CreateCell` journal entry into the born cell's full bundle.
    pub fn cell(&self) -> Option<CellId> {
        match self {
            UKey::Exist(c)
            | UKey::Balance(c)
            | UKey::Nonce(c)
            | UKey::ProvedState(c)
            | UKey::Lifecycle(c)
            | UKey::Mode(c)
            | UKey::Identity(c)
            | UKey::SwissTableRoot(c)
            | UKey::RefcountTableRoot(c)
            | UKey::HeapRoot(c)
            | UKey::SovereignCommitment(c)
            | UKey::Delegate(c)
            | UKey::DelegationSnapshot(c)
            | UKey::DelegationEpoch(c)
            | UKey::CommittedHeight(c)
            | UKey::Permissions(c)
            | UKey::VerificationKey(c)
            | UKey::Program(c) => Some(*c),
            UKey::Field { cell, .. }
            | UKey::FieldVisibility { cell, .. }
            | UKey::FieldCommitment { cell, .. }
            | UKey::SystemRoot { cell, .. }
            | UKey::CapSlot { cell, .. } => Some(*cell),
            UKey::Factory(_)
            | UKey::NoteNullifier(_)
            | UKey::BridgedNullifier(_)
            | UKey::Receipt(_) => None,
        }
    }
}

/// A universal-memory cell VALUE. Plane-typed for debuggability; structured objects
/// (permissions, capability refs, lifecycle, programs…) carry their canonical JSON bytes
/// (deterministic: serde emits struct fields in declaration order).
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum UVal {
    /// Set-membership planes (existence, nullifiers): present.
    Present,
    /// Signed scalar (balance).
    Int(i64),
    /// Unsigned scalar (nonce, epochs, positions).
    U64(u64),
    /// Boolean flags (proved_state).
    Bool(bool),
    /// 32-byte values (field elements, roots, commitments).
    Bytes32([u8; 32]),
    /// Canonical JSON of a structured value.
    Blob(Vec<u8>),
}

fn json<T: serde::Serialize>(t: &T) -> UVal {
    UVal::Blob(serde_json::to_vec(t).expect("umem: canonical JSON encoding"))
}

/// The projection image: present cells only (`absent = not in the map`, exactly the
/// Lean `Option`-cell encoding with `none` dropped).
pub type UProjection = BTreeMap<UKey, UVal>;

/// Project one cell's planes into the universal address space.
pub fn project_cell(cell: &Cell, out: &mut UProjection) {
    let id = cell.id();
    out.insert(UKey::Exist(id), UVal::Present);
    for slot in 0..STATE_SLOTS {
        out.insert(
            UKey::Field {
                cell: id,
                slot: slot as u64,
            },
            UVal::Bytes32(cell.state.fields[slot]),
        );
        out.insert(
            UKey::FieldVisibility {
                cell: id,
                slot: slot as u64,
            },
            json(&cell.state.field_visibility[slot]),
        );
        if let Some(c) = cell.state.commitments[slot] {
            out.insert(
                UKey::FieldCommitment {
                    cell: id,
                    slot: slot as u64,
                },
                UVal::Bytes32(c),
            );
        }
    }
    for (k, v) in cell.state.fields_map.iter() {
        out.insert(UKey::Field { cell: id, slot: *k }, UVal::Bytes32(*v));
    }
    out.insert(UKey::Balance(id), UVal::Int(cell.state.balance()));
    out.insert(UKey::Nonce(id), UVal::U64(cell.state.nonce()));
    out.insert(UKey::ProvedState(id), UVal::Bool(cell.state.proved_state()));
    out.insert(UKey::Lifecycle(id), json(&cell.lifecycle));
    out.insert(UKey::Mode(id), json(&cell.mode));
    out.insert(UKey::Identity(id), {
        let mut bytes = Vec::with_capacity(64);
        bytes.extend_from_slice(cell.public_key());
        bytes.extend_from_slice(cell.token_id());
        UVal::Blob(bytes)
    });
    out.insert(
        UKey::SwissTableRoot(id),
        UVal::Bytes32(cell.state.swiss_table_root),
    );
    out.insert(
        UKey::RefcountTableRoot(id),
        UVal::Bytes32(cell.state.refcount_table_root),
    );
    for (i, root) in cell.state.system_roots.iter().enumerate() {
        out.insert(
            UKey::SystemRoot {
                cell: id,
                index: i as u64,
            },
            UVal::Bytes32(*root),
        );
    }
    out.insert(UKey::HeapRoot(id), UVal::Bytes32(cell.state.heap_root));
    out.insert(
        UKey::CommittedHeight(id),
        UVal::U64(cell.state.committed_height()),
    );
    // -- caps domain planes --
    for cap in cell.capabilities.iter() {
        out.insert(
            UKey::CapSlot {
                cell: id,
                slot: cap.slot,
            },
            json(cap),
        );
    }
    if let Some(parent) = cell.delegate {
        out.insert(UKey::Delegate(id), UVal::Bytes32(parent.0));
    }
    if let Some(delegation) = &cell.delegation {
        out.insert(UKey::DelegationSnapshot(id), json(delegation));
    }
    out.insert(
        UKey::DelegationEpoch(id),
        UVal::U64(cell.state.delegation_epoch()),
    );
    out.insert(UKey::Permissions(id), json(&cell.permissions));
    if let Some(vk) = &cell.verification_key {
        out.insert(UKey::VerificationKey(id), json(vk));
    }
    out.insert(UKey::Program(id), json(&cell.program));
}

/// Project the whole ledger (hosted cells + sovereign commitments).
pub fn project_ledger(ledger: &Ledger) -> UProjection {
    let mut out = UProjection::new();
    for (_, cell) in ledger.iter() {
        project_cell(cell, &mut out);
    }
    for (id, commitment) in ledger.iter_sovereign_commitments() {
        out.insert(UKey::SovereignCommitment(*id), UVal::Bytes32(*commitment));
    }
    out
}

/// Project the FULL executor state: the ledger + the executor-owned side tables
/// (note nullifiers, bridged nullifiers, the factory registry).
pub fn project_executor_state(
    ledger: &Ledger,
    note_nullifiers: &NullifierSet,
    bridged_nullifiers: &BridgedNullifierSet,
    factories: &FactoryRegistry,
) -> UProjection {
    let mut out = project_ledger(ledger);
    for n in note_nullifiers.iter() {
        out.insert(UKey::NoteNullifier(n.0), UVal::Present);
    }
    for n in bridged_nullifiers.iter() {
        out.insert(UKey::BridgedNullifier(*n), UVal::Present);
    }
    for (vk, desc) in factories.descriptors.iter() {
        out.insert(UKey::Factory(*vk), json(desc));
    }
    out
}

/// Memory-op kind (the memcheck `Kind`).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum UmemKind {
    /// A read (returns and re-claims the current cell).
    Read,
    /// A write (installs `val` over the claimed `prev_val`).
    Write,
}

/// One Blum trace op against the unified address space. `val`/`prev_val` are
/// `Option`-cells (`None` = absent), exactly the Lean `Op (UAddr UKey) (Option ℤ)` /
/// the circuit's `(present, value)` encoding. The op at trace position `i` carries
/// serial `i + 1` (positional, as the circuit assembly computes it); `prev_serial` is
/// the serial of the previous touch of the same address (`0` = the init boundary).
#[derive(Clone, PartialEq, Debug)]
pub struct UmemOp {
    /// Read or write.
    pub kind: UmemKind,
    /// The structured address (domain = `key.domain()`).
    pub key: UKey,
    /// The cell value after the op (for a read: the value returned).
    pub val: Option<UVal>,
    /// The claimed previous cell value.
    pub prev_val: Option<UVal>,
    /// The claimed previous serial (`0` = init boundary).
    pub prev_serial: u64,
}

/// The per-turn universal-memory witness the executor can now produce: the pre/post
/// projections plus the Blum op trace whose fold connects them (the executable shadow
/// of the Lean `*_is_memory_program` agreement theorems).
#[derive(Clone, Debug)]
pub struct UmemTurnWitness {
    /// The projection of the executor state at the journal window's start (post
    /// fee/nonce phase — the forest execution's pre-state).
    pub pre: UProjection,
    /// The Blum write trace of the forest execution, in journal (= execution) order.
    pub ops: Vec<UmemOp>,
    /// The projection at the journal window's end (before fee distribution).
    pub post: UProjection,
    /// How many ops were synthesized from the pre/post diff because no journal entry
    /// named their address (state surfaces whose effects don't journal per-address
    /// yet). `0` for the transfer / set-field / capability lanes.
    pub synthesized: usize,
}

/// The REAL memory semantics, independently implemented (the `MemoryChecking.step`
/// fold): a write installs its value (absent = remove), a read changes nothing.
pub fn fold(pre: &UProjection, ops: &[UmemOp]) -> UProjection {
    let mut m = pre.clone();
    for op in ops {
        if let UmemKind::Write = op.kind {
            match &op.val {
                Some(v) => {
                    m.insert(op.key.clone(), v.clone());
                }
                None => {
                    m.remove(&op.key);
                }
            }
        }
    }
    m
}

/// The per-op memcheck discipline: `prev_serial` strictly below the op's own positional
/// serial, and a read returns exactly its claimed previous value.
pub fn disciplined(ops: &[UmemOp]) -> bool {
    ops.iter().enumerate().all(|(i, op)| {
        op.prev_serial < (i as u64) + 1 && (op.kind != UmemKind::Read || op.val == op.prev_val)
    })
}

/// The index-domain write for the turn's receipt at log position `position` (the caller
/// owns the log — see module docs). `prev_val = None`: the position is fresh
/// (append-only log).
pub fn receipt_op(position: u64, receipt_hash: [u8; 32]) -> UmemOp {
    UmemOp {
        kind: UmemKind::Write,
        key: UKey::Receipt(position),
        val: Some(UVal::Bytes32(receipt_hash)),
        prev_val: None,
        prev_serial: 0,
    }
}

/// A journal entry's address touches: `(key, recorded_prev)` where
/// `recorded_prev = Some(cell)` when the journal recorded the prior value
/// (`Some(None)` = recorded-absent, e.g. a fresh capability slot) and `None` when the
/// entry doesn't carry it (the emitter falls back to the running fold value, which the
/// memory semantics guarantees is the truth whenever the trace is genuine).
enum Touch {
    At(UKey, Option<Option<UVal>>),
    /// A `CreateCell` bundle birth: expanded against the post-state into every plane of
    /// the born cell (all with recorded-absent prevs — the freshness gate).
    CreateCell(CellId),
}

fn touches_of_entry(e: &JournalEntry) -> Vec<Touch> {
    match e {
        JournalEntry::SetField {
            cell,
            index,
            old_value,
        } => vec![Touch::At(
            UKey::Field {
                cell: *cell,
                slot: *index as u64,
            },
            Some(old_value.map(|v| UVal::Bytes32(v))),
        )],
        JournalEntry::SetBalance { cell, old_balance } => vec![Touch::At(
            UKey::Balance(*cell),
            Some(Some(UVal::Int(*old_balance))),
        )],
        JournalEntry::SetNonce { cell, old_nonce } => vec![Touch::At(
            UKey::Nonce(*cell),
            Some(Some(UVal::U64(*old_nonce))),
        )],
        JournalEntry::GrantCapability { cell, slot } => vec![Touch::At(
            UKey::CapSlot {
                cell: *cell,
                slot: *slot,
            },
            Some(None), // a grant claims a FRESH slot
        )],
        JournalEntry::RevokeCapability { cell, old_cap } => vec![Touch::At(
            UKey::CapSlot {
                cell: *cell,
                slot: old_cap.slot,
            },
            Some(Some(json(old_cap))),
        )],
        JournalEntry::CreateCell { cell } => vec![Touch::CreateCell(*cell)],
        JournalEntry::SetProvedState { cell, old_value } => vec![Touch::At(
            UKey::ProvedState(*cell),
            Some(Some(UVal::Bool(*old_value))),
        )],
        JournalEntry::SetPermissions {
            cell,
            old_permissions,
        } => vec![Touch::At(
            UKey::Permissions(*cell),
            Some(Some(json(old_permissions))),
        )],
        JournalEntry::SetVerificationKey { cell, old_vk } => vec![Touch::At(
            UKey::VerificationKey(*cell),
            Some(old_vk.as_ref().map(json)),
        )],
        JournalEntry::SetDelegation {
            cell,
            old_delegation,
        } => vec![Touch::At(
            UKey::DelegationSnapshot(*cell),
            Some(old_delegation.as_ref().map(json)),
        )],
        JournalEntry::SetDelegationEpoch { cell, old_epoch } => vec![Touch::At(
            UKey::DelegationEpoch(*cell),
            Some(Some(UVal::U64(*old_epoch))),
        )],
        JournalEntry::SetCommittedHeight { cell, old_height } => vec![Touch::At(
            UKey::CommittedHeight(*cell),
            Some(Some(UVal::U64(*old_height))),
        )],
        JournalEntry::SetLifecycle {
            cell,
            old_lifecycle,
        } => {
            // a lifecycle transition can also be a destroy — same plane (the lifecycle
            // object carries the death certificate; see the projection table).
            let _: &CellLifecycle = old_lifecycle;
            vec![Touch::At(
                UKey::Lifecycle(*cell),
                Some(Some(json(old_lifecycle))),
            )]
        }
        JournalEntry::AttenuateCapability { cell, slot, .. } => vec![Touch::At(
            UKey::CapSlot {
                cell: *cell,
                slot: *slot,
            },
            None, // partial old fields recorded; prev = the running fold value
        )],
        JournalEntry::NoteNullifierInserted { nullifier } => vec![Touch::At(
            UKey::NoteNullifier(nullifier.0),
            Some(None), // freshness IS the double-spend gate
        )],
        JournalEntry::BridgedNullifierInserted { nullifier } => {
            vec![Touch::At(UKey::BridgedNullifier(*nullifier), Some(None))]
        }
        // Markers / receipt-surface entries: no state cell.
        JournalEntry::NoteSpend | JournalEntry::NoteCreate => vec![],
        JournalEntry::EventEmitted { .. } => vec![],
    }
}

/// **THE TRACE EMITTER** — re-read the executed turn's journal as its Blum write trace.
///
/// Guarantees on success:
///  * `fold(pre, ops) == post` (the agreement square, checked here — the executable
///    shadow of the Lean `*_is_memory_program` keystones);
///  * `disciplined(&ops)` (the per-op memcheck discipline);
///  * every journal-recorded prior value MATCHED the running fold (journal ⟷ projection
///    drift refuses loudly with a named address);
///  * `synthesized` counts diff-covered addresses no journal entry named (state
///    surfaces that mutate without per-address journaling — `0` on the
///    transfer/set-field/capability lanes).
pub(crate) fn emit_trace(
    pre: &UProjection,
    post: &UProjection,
    entries: &[JournalEntry],
) -> Result<UmemTurnWitness, String> {
    // 1. Expand journal entries into ordered address touches.
    let mut touches: Vec<(UKey, Option<Option<UVal>>)> = Vec::new();
    for e in entries {
        for t in touches_of_entry(e) {
            match t {
                Touch::At(k, p) => touches.push((k, p)),
                Touch::CreateCell(cell) => {
                    // the bundle birth: every post-state plane of the born cell, each
                    // with a recorded-absent prev (the freshness gate; Lean
                    // `createTrace` claims `prevVal = none` for the same reason).
                    for (k, _) in post.iter() {
                        if k.cell() == Some(cell) {
                            touches.push((k.clone(), Some(None)));
                        }
                    }
                }
            }
        }
    }

    // 2. Per-address touch positions, in order.
    let mut positions: BTreeMap<UKey, Vec<usize>> = BTreeMap::new();
    for (i, (k, _)) in touches.iter().enumerate() {
        positions.entry(k.clone()).or_default().push(i);
    }

    // 3. Emit ops: prev = recorded prior (cross-checked) or the running fold value;
    //    val = the NEXT touch's recorded prior, or the post-state cell for the last
    //    touch of each address.
    let mut current: BTreeMap<UKey, Option<UVal>> = BTreeMap::new();
    let mut last_serial: BTreeMap<UKey, u64> = BTreeMap::new();
    let mut ops: Vec<UmemOp> = Vec::new();
    for (i, (k, recorded_prev)) in touches.iter().enumerate() {
        let fold_prev: Option<UVal> = match current.get(k) {
            Some(v) => v.clone(),
            None => pre.get(k).cloned(),
        };
        let prev_val = match recorded_prev {
            Some(recorded) => {
                if *recorded != fold_prev {
                    return Err(format!(
                        "umem trace drift at {k:?}: journal recorded prior {recorded:?} \
                         but the projection fold carries {fold_prev:?}"
                    ));
                }
                recorded.clone()
            }
            None => fold_prev,
        };
        let my_positions = &positions[k];
        let my_idx = my_positions
            .iter()
            .position(|p| *p == i)
            .expect("position index");
        let val: Option<UVal> = if my_idx + 1 < my_positions.len() {
            // the next touch's recorded prior is this op's installed value when known;
            // otherwise install the post value (a sound coarsening: the fold agrees).
            match &touches[my_positions[my_idx + 1]].1 {
                Some(recorded_next) => recorded_next.clone(),
                None => post.get(k).cloned(),
            }
        } else {
            post.get(k).cloned()
        };
        let prev_serial = last_serial.get(k).copied().unwrap_or(0);
        last_serial.insert(k.clone(), (i as u64) + 1);
        current.insert(k.clone(), val.clone());
        ops.push(UmemOp {
            kind: UmemKind::Write,
            key: k.clone(),
            val,
            prev_val,
            prev_serial,
        });
    }

    // 4. Coverage: any pre/post difference not named by the journal becomes a
    //    synthesized trailing write (totality), counted honestly.
    let mut synthesized = 0usize;
    let mut diff_keys: Vec<UKey> = Vec::new();
    for (k, v) in post.iter() {
        if pre.get(k) != Some(v) && !positions.contains_key(k) {
            diff_keys.push(k.clone());
        }
    }
    for (k, _) in pre.iter() {
        if !post.contains_key(k) && !positions.contains_key(k) {
            diff_keys.push(k.clone());
        }
    }
    diff_keys.sort();
    diff_keys.dedup();
    for k in diff_keys {
        let serial_base = ops.len() as u64;
        let _ = serial_base;
        ops.push(UmemOp {
            kind: UmemKind::Write,
            key: k.clone(),
            val: post.get(&k).cloned(),
            prev_val: pre.get(&k).cloned(),
            prev_serial: last_serial.get(&k).copied().unwrap_or(0),
        });
        synthesized += 1;
    }

    // 5. THE AGREEMENT CHECK: fold(pre, ops) == post — refuse on any mismatch.
    let folded = fold(pre, &ops);
    if &folded != post {
        let mut mismatches = Vec::new();
        for (k, v) in post.iter() {
            if folded.get(k) != Some(v) {
                mismatches.push(format!("{k:?}: post {v:?} vs fold {:?}", folded.get(k)));
            }
        }
        for (k, v) in folded.iter() {
            if !post.contains_key(k) {
                mismatches.push(format!("{k:?}: fold {v:?} vs post absent"));
            }
        }
        return Err(format!(
            "umem fold/post disagreement ({} addresses): {}",
            mismatches.len(),
            mismatches.join("; ")
        ));
    }
    debug_assert!(disciplined(&ops));

    Ok(UmemTurnWitness {
        pre: pre.clone(),
        ops,
        post: post.clone(),
        synthesized,
    })
}
