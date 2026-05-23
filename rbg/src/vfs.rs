//! Userspace VFS/storage layer built from pyana primitives.
//!
//! # Design Heritage
//!
//! This maps Robigalia's VFS design into pyana's distributed runtime:
//!
//! | Robigalia | Pyana Equivalent | This Module |
//! |-----------|-----------------|-------------|
//! | Volume | Computron budget / staked note value | [`Volume`] |
//! | Blob | Cell state / content-addressed note | [`Blob`] |
//! | Directory | C-list + factory provenance | [`Directory`] |
//! | splice() | Effect VM atomic turn | [`Blob::splice`] |
//! | swap() | SetField + nonce check | [`Directory::swap`] |
//!
//! # Nameless Writes (Zhang et al.)
//!
//! The key insight from the nameless writes paper: clients write data, the storage
//! device picks the location, and returns the address. In pyana, notes ARE nameless
//! writes: you commit a value and get back the commitment hash as its address. This
//! eliminates the indirection overhead of traditional file systems (inode -> block
//! mapping) because the address IS the content.
//!
//! # Proving Strategy
//!
//! Every VFS operation maps to Effect VM effects. A turn that performs VFS operations
//! generates a trace where:
//! - `CreateBlob` = `NoteCreate` (content-addressed, returns commitment)
//! - `ReadBlob` = merkle membership proof (no state change, verified externally)
//! - `Splice` = `NoteSpend` (old blob) + `NoteCreate` (new blob) in one turn
//! - `Swap` = `SetField` with nonce precondition on the directory cell
//! - Volume accounting = balance checks (already enforced by Effect VM)
//!
//! The AIR constraints for VFS operations are a SUBSET of the existing Effect VM
//! constraints. No new AIR is needed -- VFS is a user-space library on top of the
//! existing proving system.

use std::collections::HashMap;
use std::fmt;

// =============================================================================
// Pyana primitive stubs (mirrors real types from pyana-types / pyana-cell)
// =============================================================================

/// Cell identity: BLAKE3(public_key || token_id). 32 bytes.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct CellId(pub [u8; 32]);

impl fmt::Debug for CellId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Cell({})",
            self.0[..4].iter().map(|b| format!("{b:02x}")).collect::<String>()
        )
    }
}

/// Monotonically increasing version counter on a cell.
pub type Nonce = u64;

/// A note commitment (content address). BLAKE3 hash of the note contents.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct NoteCommitment(pub [u8; 32]);

impl fmt::Debug for NoteCommitment {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Note({})",
            self.0[..4].iter().map(|b| format!("{b:02x}")).collect::<String>()
        )
    }
}

/// A nullifier: proof that a note has been spent. Published to prevent double-use.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Nullifier(pub [u8; 32]);

/// Capability reference -- an unforgeable token granting access to a resource.
/// In the real system this is a c-list index + swiss number. Here we model it
/// as a typed wrapper carrying the target cell and permitted operations.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CapRef {
    /// The cell this capability targets.
    pub target: CellId,
    /// Bitmask of permitted operations.
    pub permissions: Permissions,
}

/// Permission bitmask for capability attenuation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Permissions(pub u32);

impl Permissions {
    pub const READ: Self = Self(0b0001);
    pub const WRITE: Self = Self(0b0010);
    pub const SPLICE: Self = Self(0b0100);
    pub const DELETE: Self = Self(0b1000);
    pub const ALL: Self = Self(0b1111);

    pub fn contains(self, other: Self) -> bool {
        (self.0 & other.0) == other.0
    }

    pub fn attenuate(self, mask: Self) -> Self {
        Self(self.0 & mask.0)
    }
}

// =============================================================================
// Effect types (mirrors Effect VM, subset needed for VFS)
// =============================================================================

/// Effects that VFS operations decompose into for proving.
/// Each variant maps to an existing Effect VM row type.
#[derive(Clone, Debug)]
pub enum VfsEffect {
    /// Create a blob: produces a NoteCreate in the trace.
    CreateBlob {
        commitment: NoteCommitment,
        size: u64,
    },
    /// Spend (consume) a blob: produces a NoteSpend in the trace.
    SpendBlob {
        nullifier: Nullifier,
        commitment: NoteCommitment,
    },
    /// Update a directory entry: produces a SetField in the trace.
    SetEntry {
        dir_cell: CellId,
        field_idx: u32,
        /// New value (hash of the entry metadata).
        value: [u8; 32],
    },
    /// Debit from a volume's balance (resource accounting).
    VolumeDebit { amount: u64 },
    /// Credit to a volume's balance (on blob deletion / reclamation).
    VolumeCredit { amount: u64 },
}

/// A completed turn's effect trace, ready for proving.
#[derive(Clone, Debug, Default)]
pub struct EffectTrace {
    pub effects: Vec<VfsEffect>,
}

impl EffectTrace {
    pub fn push(&mut self, effect: VfsEffect) {
        self.effects.push(effect);
    }

    /// Total computational cost of this trace (for volume accounting).
    pub fn total_cost(&self) -> u64 {
        self.effects.iter().map(|e| match e {
            VfsEffect::CreateBlob { size, .. } => 100 + size, // base + per-byte
            VfsEffect::SpendBlob { .. } => 50,
            VfsEffect::SetEntry { .. } => 30,
            VfsEffect::VolumeDebit { .. } | VfsEffect::VolumeCredit { .. } => 10,
        }).sum()
    }
}

// =============================================================================
// Volume: Resource quota / allocation pool
// =============================================================================

/// A Volume is a resource container that tracks allocation budget.
///
/// In Robigalia, volumes are the unit of resource accounting. In pyana, this maps
/// to a cell's balance (computrons) which bounds how much storage/computation it
/// can allocate.
///
/// Volume cells are proven to never go negative via the Effect VM's balance
/// continuity constraint: `balance_after = balance_before - debit + credit` with
/// overflow check.
#[derive(Clone, Debug)]
pub struct Volume {
    /// The cell backing this volume.
    pub cell_id: CellId,
    /// Available allocation budget (in abstract storage units).
    pub capacity: u64,
    /// Currently allocated.
    pub used: u64,
    /// Monotonic version (cell nonce).
    pub nonce: Nonce,
}

/// Errors from volume operations.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VolumeError {
    /// Allocation would exceed volume capacity.
    InsufficientCapacity { requested: u64, available: u64 },
    /// Tried to free more than is allocated.
    Underflow { freed: u64, used: u64 },
    /// Stale nonce (concurrent modification detected).
    StaleNonce { expected: Nonce, actual: Nonce },
}

impl Volume {
    /// Create a new volume with the given capacity.
    pub fn new(cell_id: CellId, capacity: u64) -> Self {
        Self {
            cell_id,
            capacity,
            used: 0,
            nonce: 0,
        }
    }

    pub fn available(&self) -> u64 {
        self.capacity - self.used
    }

    /// Attempt to allocate `size` units. Returns the debit effect on success.
    pub fn allocate(&mut self, size: u64, trace: &mut EffectTrace) -> Result<(), VolumeError> {
        if size > self.available() {
            return Err(VolumeError::InsufficientCapacity {
                requested: size,
                available: self.available(),
            });
        }
        self.used += size;
        self.nonce += 1;
        trace.push(VfsEffect::VolumeDebit { amount: size });
        Ok(())
    }

    /// Free `size` units back to the volume.
    pub fn free(&mut self, size: u64, trace: &mut EffectTrace) -> Result<(), VolumeError> {
        if size > self.used {
            return Err(VolumeError::Underflow {
                freed: size,
                used: self.used,
            });
        }
        self.used -= size;
        self.nonce += 1;
        trace.push(VfsEffect::VolumeCredit { amount: size });
        Ok(())
    }
}

// =============================================================================
// Blob: Content-addressed storage (nameless writes)
// =============================================================================

/// A Blob is a content-addressed data object.
///
/// This IS a nameless write: you supply content, the system computes
/// the address (commitment hash). No indirection table, no inode-to-block map.
/// The commitment IS the address.
///
/// In pyana terms, each Blob is a note:
/// - Creating a blob = creating a note commitment (NoteCreate effect)
/// - Reading a blob = proving membership in the note tree (Merkle proof)
/// - Deleting a blob = spending the note (reveal nullifier, NoteSpend effect)
/// - Splicing a blob = spend old + create new in one atomic turn
///
/// The `splice()` operation provides Robigalia-style atomic partial update:
/// you can replace a range within the blob, producing a new blob with a new
/// commitment. The old blob is consumed (nullified) atomically.
#[derive(Clone, Debug)]
pub struct Blob {
    /// The content-address (note commitment). This IS the blob's identity.
    pub commitment: NoteCommitment,
    /// The raw data. In production this would be off-chain (only commitment on-chain).
    pub data: Vec<u8>,
    /// Which volume this blob is charged against.
    pub volume: CellId,
    /// Whether this blob has been spent (consumed/deleted).
    pub spent: bool,
}

/// Result of creating a blob -- the system picks the address (nameless write pattern).
#[derive(Clone, Debug)]
pub struct BlobReceipt {
    /// The content-address assigned by the system.
    pub commitment: NoteCommitment,
    /// Size in bytes (for volume accounting).
    pub size: u64,
}

impl Blob {
    /// Compute the commitment for arbitrary data.
    /// This is the "nameless write" -- the address is derived from content.
    fn compute_commitment(data: &[u8], volume: &CellId) -> NoteCommitment {
        let mut hasher = blake3::Hasher::new_derive_key("pyana-vfs blob commitment v1");
        hasher.update(data);
        hasher.update(&volume.0);
        NoteCommitment(*hasher.finalize().as_bytes())
    }

    /// Compute the nullifier for this blob.
    /// Only the volume owner can produce this (requires spending key).
    fn compute_nullifier(commitment: &NoteCommitment, spending_key: &[u8; 32]) -> Nullifier {
        let mut hasher = blake3::Hasher::new_derive_key("pyana-vfs blob nullifier v1");
        hasher.update(&commitment.0);
        hasher.update(spending_key);
        Nullifier(*hasher.finalize().as_bytes())
    }

    /// Create a new blob (nameless write).
    ///
    /// The caller provides data; the system returns the content-address.
    /// This parallels the nameless writes paper: client writes data, device picks
    /// location (= commitment), returns the address.
    pub fn create(
        data: Vec<u8>,
        volume: &mut Volume,
        spending_key: &[u8; 32],
        trace: &mut EffectTrace,
    ) -> Result<Self, VolumeError> {
        let size = data.len() as u64;
        volume.allocate(size, trace)?;

        let commitment = Self::compute_commitment(&data, &volume.cell_id);
        trace.push(VfsEffect::CreateBlob { commitment, size });

        Ok(Self {
            commitment,
            data,
            volume: volume.cell_id,
            spent: false,
        })
    }

    /// Splice: atomically replace a byte range within this blob.
    ///
    /// This consumes the old blob (spend) and creates a new one (create) in a
    /// single turn. The atomicity comes from the Effect VM: both effects are in
    /// the same trace, proven together.
    ///
    /// Returns the new blob. The old blob is marked spent.
    pub fn splice(
        &mut self,
        offset: usize,
        delete_count: usize,
        insert: &[u8],
        volume: &mut Volume,
        spending_key: &[u8; 32],
        trace: &mut EffectTrace,
    ) -> Result<Self, SpliceError> {
        if self.spent {
            return Err(SpliceError::AlreadySpent);
        }
        if offset > self.data.len() {
            return Err(SpliceError::OffsetOutOfBounds {
                offset,
                len: self.data.len(),
            });
        }
        let end = offset.saturating_add(delete_count).min(self.data.len());

        // Compute size delta for volume accounting.
        let old_size = self.data.len() as u64;
        let new_size = (self.data.len() - (end - offset) + insert.len()) as u64;

        // If new blob is larger, allocate the difference.
        if new_size > old_size {
            volume.allocate(new_size - old_size, trace)?;
        } else if new_size < old_size {
            volume.free(old_size - new_size, trace).map_err(|_| SpliceError::VolumeUnderflow)?;
        }

        // Spend the old blob.
        let nullifier = Self::compute_nullifier(&self.commitment, spending_key);
        trace.push(VfsEffect::SpendBlob {
            nullifier,
            commitment: self.commitment,
        });
        self.spent = true;

        // Build new data.
        let mut new_data = Vec::with_capacity(new_size as usize);
        new_data.extend_from_slice(&self.data[..offset]);
        new_data.extend_from_slice(insert);
        new_data.extend_from_slice(&self.data[end..]);

        // Create new blob (nameless write -- system picks address).
        let new_commitment = Self::compute_commitment(&new_data, &volume.cell_id);
        trace.push(VfsEffect::CreateBlob {
            commitment: new_commitment,
            size: new_size,
        });

        Ok(Self {
            commitment: new_commitment,
            data: new_data,
            volume: volume.cell_id,
            spent: false,
        })
    }

    /// Delete this blob, freeing its volume allocation.
    pub fn delete(
        &mut self,
        volume: &mut Volume,
        spending_key: &[u8; 32],
        trace: &mut EffectTrace,
    ) -> Result<Nullifier, SpliceError> {
        if self.spent {
            return Err(SpliceError::AlreadySpent);
        }
        let size = self.data.len() as u64;
        volume.free(size, trace).map_err(|_| SpliceError::VolumeUnderflow)?;

        let nullifier = Self::compute_nullifier(&self.commitment, spending_key);
        trace.push(VfsEffect::SpendBlob {
            nullifier,
            commitment: self.commitment,
        });
        self.spent = true;
        Ok(nullifier)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SpliceError {
    AlreadySpent,
    OffsetOutOfBounds { offset: usize, len: usize },
    VolumeExhausted(VolumeError),
    VolumeUnderflow,
}

impl From<VolumeError> for SpliceError {
    fn from(e: VolumeError) -> Self {
        SpliceError::VolumeExhausted(e)
    }
}

// =============================================================================
// Directory: Versioned naming with atomic swap
// =============================================================================

/// A directory entry. Names are arbitrary byte arrays (no path separator convention).
/// Each entry is versioned independently, enabling fine-grained conflict detection.
///
/// In pyana terms, each entry is stored in a cell's fields (or as a Merkle tree
/// of entries for large directories). The version maps to the directory cell's nonce
/// at the time of last modification.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DirEntry {
    /// The name (arbitrary bytes, no separator, no null termination required).
    pub name: Vec<u8>,
    /// What this entry points to -- either a blob or a subdirectory.
    pub target: EntryTarget,
    /// Version at which this entry was last modified (maps to cell nonce).
    pub version: Nonce,
}

/// What a directory entry points to.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EntryTarget {
    /// A content-addressed blob.
    Blob(NoteCommitment),
    /// A subdirectory (another directory cell).
    SubDir(CellId),
    /// A capability reference to an external resource (cross-federation).
    CapRef(CellId),
}

/// A Directory is a naming container backed by a cell.
///
/// Properties (inherited from Robigalia):
/// - Names are byte arrays (no path separator -- the VFS composes directories)
/// - Every mutation is versioned (atomic, detectable conflicts)
/// - `swap()` is the fundamental mutation primitive (compare-and-swap)
/// - Stateless interaction: no cursors, no implicit seek position
///
/// Properties (from pyana):
/// - Directory cell has a c-list: entries ARE capabilities
/// - Factory provenance: who created this directory is tracked
/// - Distributed GC: when all references to a blob are removed from all
///   directories, the blob becomes eligible for collection (via CapTP GC)
#[derive(Clone, Debug)]
pub struct Directory {
    /// The cell backing this directory.
    pub cell_id: CellId,
    /// Current entries (in production: Merkle tree; here: HashMap for clarity).
    pub entries: HashMap<Vec<u8>, DirEntry>,
    /// Cell nonce (incremented on every mutation).
    pub nonce: Nonce,
    /// The capability required to mutate this directory.
    pub write_cap: CapRef,
}

/// Errors from directory operations.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DirError {
    /// The entry does not exist.
    NotFound(Vec<u8>),
    /// The entry already exists (and create was not a swap).
    AlreadyExists(Vec<u8>),
    /// Version mismatch: someone else mutated between our read and our write.
    VersionMismatch {
        name: Vec<u8>,
        expected: Nonce,
        actual: Nonce,
    },
    /// Caller does not hold the required capability.
    PermissionDenied,
}

impl Directory {
    /// Create a new empty directory backed by the given cell.
    pub fn new(cell_id: CellId, _owner: CellId) -> Self {
        Self {
            cell_id,
            entries: HashMap::new(),
            nonce: 0,
            write_cap: CapRef {
                target: cell_id,
                permissions: Permissions::ALL,
            },
        }
    }

    /// Look up an entry by name. Stateless -- no cursor, no side effects.
    pub fn lookup(&self, name: &[u8]) -> Option<&DirEntry> {
        self.entries.get(name)
    }

    /// List all entries. Returns a snapshot (stateless -- no iterator invalidation).
    pub fn list(&self) -> Vec<&DirEntry> {
        self.entries.values().collect()
    }

    /// Insert a new entry. Fails if the name already exists.
    pub fn insert(
        &mut self,
        name: Vec<u8>,
        target: EntryTarget,
        caller_cap: &CapRef,
        trace: &mut EffectTrace,
    ) -> Result<Nonce, DirError> {
        self.check_write_permission(caller_cap)?;
        if self.entries.contains_key(&name) {
            return Err(DirError::AlreadyExists(name));
        }
        self.nonce += 1;
        let entry = DirEntry {
            name: name.clone(),
            target,
            version: self.nonce,
        };
        self.emit_set_entry(&name, &entry, trace);
        self.entries.insert(name, entry);
        Ok(self.nonce)
    }

    /// Atomic swap: replace an entry only if its version matches `expected_version`.
    ///
    /// This is the fundamental mutation primitive from the Robigalia VFS design.
    /// It composes with the Effect VM because:
    /// 1. The version check maps to a nonce precondition on the cell
    /// 2. The update maps to a SetField effect
    /// 3. Both are in the same trace row, proven atomically
    ///
    /// If the version does not match, the operation fails without mutation --
    /// the caller must re-read and retry (optimistic concurrency).
    pub fn swap(
        &mut self,
        name: &[u8],
        expected_version: Nonce,
        new_target: EntryTarget,
        caller_cap: &CapRef,
        trace: &mut EffectTrace,
    ) -> Result<Nonce, DirError> {
        self.check_write_permission(caller_cap)?;
        let entry = self
            .entries
            .get(name)
            .ok_or_else(|| DirError::NotFound(name.to_vec()))?;
        if entry.version != expected_version {
            return Err(DirError::VersionMismatch {
                name: name.to_vec(),
                expected: expected_version,
                actual: entry.version,
            });
        }
        self.nonce += 1;
        let new_entry = DirEntry {
            name: name.to_vec(),
            target: new_target,
            version: self.nonce,
        };
        self.emit_set_entry(name, &new_entry, trace);
        self.entries.insert(name.to_vec(), new_entry);
        Ok(self.nonce)
    }

    /// Remove an entry. Fails if it does not exist.
    pub fn remove(
        &mut self,
        name: &[u8],
        caller_cap: &CapRef,
        trace: &mut EffectTrace,
    ) -> Result<DirEntry, DirError> {
        self.check_write_permission(caller_cap)?;
        let entry = self
            .entries
            .remove(name)
            .ok_or_else(|| DirError::NotFound(name.to_vec()))?;
        self.nonce += 1;
        // Emit a "clear" effect (set to zeroes).
        trace.push(VfsEffect::SetEntry {
            dir_cell: self.cell_id,
            field_idx: self.field_index_for(name),
            value: [0u8; 32],
        });
        Ok(entry)
    }

    /// Rename: atomic remove + insert as a single turn.
    /// Both effects appear in the same trace, so the rename is atomic.
    pub fn rename(
        &mut self,
        old_name: &[u8],
        new_name: Vec<u8>,
        caller_cap: &CapRef,
        trace: &mut EffectTrace,
    ) -> Result<Nonce, DirError> {
        self.check_write_permission(caller_cap)?;
        let entry = self
            .entries
            .remove(old_name)
            .ok_or_else(|| DirError::NotFound(old_name.to_vec()))?;
        if self.entries.contains_key(&new_name) {
            // Put it back -- we failed.
            self.entries.insert(old_name.to_vec(), entry);
            return Err(DirError::AlreadyExists(new_name));
        }
        self.nonce += 1;
        // Clear old entry.
        trace.push(VfsEffect::SetEntry {
            dir_cell: self.cell_id,
            field_idx: self.field_index_for(old_name),
            value: [0u8; 32],
        });
        // Set new entry.
        let new_entry = DirEntry {
            name: new_name.clone(),
            target: entry.target,
            version: self.nonce,
        };
        self.emit_set_entry(&new_name, &new_entry, trace);
        self.entries.insert(new_name, new_entry);
        Ok(self.nonce)
    }

    // --- internals ---

    fn check_write_permission(&self, caller_cap: &CapRef) -> Result<(), DirError> {
        if caller_cap.target != self.cell_id || !caller_cap.permissions.contains(Permissions::WRITE)
        {
            return Err(DirError::PermissionDenied);
        }
        Ok(())
    }

    fn emit_set_entry(&self, name: &[u8], entry: &DirEntry, trace: &mut EffectTrace) {
        let value = self.entry_hash(entry);
        trace.push(VfsEffect::SetEntry {
            dir_cell: self.cell_id,
            field_idx: self.field_index_for(name),
            value,
        });
    }

    /// Hash an entry for storage in the cell's field array.
    /// In production this would be a Poseidon2 hash over BabyBear; here BLAKE3.
    fn entry_hash(&self, entry: &DirEntry) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new_derive_key("pyana-vfs dir entry v1");
        hasher.update(&entry.name);
        match &entry.target {
            EntryTarget::Blob(c) => {
                hasher.update(&[0x01]);
                hasher.update(&c.0);
            }
            EntryTarget::SubDir(id) => {
                hasher.update(&[0x02]);
                hasher.update(&id.0);
            }
            EntryTarget::CapRef(id) => {
                hasher.update(&[0x03]);
                hasher.update(&id.0);
            }
        }
        hasher.update(&entry.version.to_le_bytes());
        *hasher.finalize().as_bytes()
    }

    /// Map a name to a field index. In production this would be a Merkle tree;
    /// here we use a simple hash-to-index for illustration.
    fn field_index_for(&self, name: &[u8]) -> u32 {
        let hash = blake3::hash(name);
        let bytes = hash.as_bytes();
        u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]])
    }
}

// =============================================================================
// Distributed GC integration
// =============================================================================

/// Tracks which blobs are referenced by which directories.
/// When a blob's reference count hits zero across all directories (local and remote),
/// it becomes eligible for garbage collection.
///
/// This composes with captp/gc.rs: the ExportGcManager tracks cross-federation
/// references, while this tracks local directory references. A blob is collectible
/// only when BOTH counts are zero.
#[derive(Clone, Debug, Default)]
pub struct BlobRefTracker {
    /// blob commitment -> set of directories referencing it.
    refs: HashMap<NoteCommitment, Vec<CellId>>,
}

impl BlobRefTracker {
    pub fn new() -> Self {
        Self::default()
    }

    /// Record that a directory references a blob.
    pub fn add_ref(&mut self, blob: NoteCommitment, dir: CellId) {
        self.refs.entry(blob).or_default().push(dir);
    }

    /// Remove a reference from a directory to a blob.
    /// Returns true if the blob is now unreferenced (eligible for GC).
    pub fn drop_ref(&mut self, blob: &NoteCommitment, dir: &CellId) -> bool {
        if let Some(dirs) = self.refs.get_mut(blob) {
            dirs.retain(|d| d != dir);
            if dirs.is_empty() {
                self.refs.remove(blob);
                return true;
            }
        }
        false
    }

    /// Check if a blob is referenced by any directory.
    pub fn is_referenced(&self, blob: &NoteCommitment) -> bool {
        self.refs
            .get(blob)
            .map(|dirs| !dirs.is_empty())
            .unwrap_or(false)
    }

    /// Return the set of directories referencing a given blob.
    pub fn holders(&self, blob: &NoteCommitment) -> &[CellId] {
        self.refs.get(blob).map(|v| v.as_slice()).unwrap_or(&[])
    }
}

// =============================================================================
// VFS: Composition layer
// =============================================================================

/// The VFS composes Volumes, Blobs, and Directories into a coherent storage system.
///
/// It enforces:
/// - All blob creation/deletion goes through a volume (resource accounting)
/// - All naming goes through directories (capability-secured)
/// - All mutations produce an effect trace (provable)
///
/// The VFS itself is stateless in the Robigalia sense: each operation takes
/// explicit parameters (no hidden cursors). The returned effect trace is what
/// gets proven by the Effect VM.
pub struct Vfs {
    /// Volume registry (volume cell ID -> volume state).
    pub volumes: HashMap<CellId, Volume>,
    /// Directory registry.
    pub directories: HashMap<CellId, Directory>,
    /// Blob reference tracking for GC.
    pub blob_refs: BlobRefTracker,
}

impl Vfs {
    pub fn new() -> Self {
        Self {
            volumes: HashMap::new(),
            directories: HashMap::new(),
            blob_refs: BlobRefTracker::new(),
        }
    }

    /// Register a new volume with the given capacity.
    pub fn create_volume(&mut self, cell_id: CellId, capacity: u64) -> &Volume {
        self.volumes
            .entry(cell_id)
            .or_insert_with(|| Volume::new(cell_id, capacity))
    }

    /// Register a new directory.
    pub fn create_directory(&mut self, cell_id: CellId, owner: CellId) -> &Directory {
        self.directories
            .entry(cell_id)
            .or_insert_with(|| Directory::new(cell_id, owner))
    }

    /// Write a blob and name it in a directory, atomically.
    ///
    /// This is the common "create file" operation. It:
    /// 1. Allocates from the volume (VolumeDebit)
    /// 2. Creates the blob (NoteCreate -- nameless write)
    /// 3. Inserts the entry in the directory (SetField)
    ///
    /// All three effects are in the same trace: proven in one turn.
    pub fn write_file(
        &mut self,
        dir_id: &CellId,
        name: Vec<u8>,
        data: Vec<u8>,
        volume_id: &CellId,
        spending_key: &[u8; 32],
        caller_cap: &CapRef,
    ) -> Result<(BlobReceipt, EffectTrace), VfsError> {
        let mut trace = EffectTrace::default();

        let volume = self
            .volumes
            .get_mut(volume_id)
            .ok_or(VfsError::VolumeNotFound(*volume_id))?;

        let blob = Blob::create(data, volume, spending_key, &mut trace)
            .map_err(VfsError::Volume)?;

        let receipt = BlobReceipt {
            commitment: blob.commitment,
            size: blob.data.len() as u64,
        };

        let dir = self
            .directories
            .get_mut(dir_id)
            .ok_or(VfsError::DirectoryNotFound(*dir_id))?;

        dir.insert(
            name,
            EntryTarget::Blob(blob.commitment),
            caller_cap,
            &mut trace,
        )
        .map_err(VfsError::Dir)?;

        // Track the reference for GC.
        self.blob_refs.add_ref(blob.commitment, *dir_id);

        Ok((receipt, trace))
    }

    /// Atomic rename across directories (if same volume).
    /// Both the remove-from-source and insert-to-dest are in one trace.
    pub fn move_file(
        &mut self,
        src_dir_id: &CellId,
        src_name: &[u8],
        dst_dir_id: &CellId,
        dst_name: Vec<u8>,
        caller_cap: &CapRef,
    ) -> Result<EffectTrace, VfsError> {
        let mut trace = EffectTrace::default();

        // Remove from source.
        let src_dir = self
            .directories
            .get_mut(src_dir_id)
            .ok_or(VfsError::DirectoryNotFound(*src_dir_id))?;
        let entry = src_dir
            .remove(src_name, caller_cap, &mut trace)
            .map_err(VfsError::Dir)?;

        // Insert into dest.
        let dst_cap = CapRef {
            target: *dst_dir_id,
            permissions: caller_cap.permissions,
        };
        let dst_dir = self
            .directories
            .get_mut(dst_dir_id)
            .ok_or(VfsError::DirectoryNotFound(*dst_dir_id))?;
        dst_dir
            .insert(dst_name, entry.target.clone(), &dst_cap, &mut trace)
            .map_err(VfsError::Dir)?;

        // Update GC tracking.
        if let EntryTarget::Blob(commitment) = &entry.target {
            self.blob_refs.drop_ref(commitment, src_dir_id);
            self.blob_refs.add_ref(*commitment, *dst_dir_id);
        }

        Ok(trace)
    }
}

#[derive(Clone, Debug)]
pub enum VfsError {
    Volume(VolumeError),
    Dir(DirError),
    VolumeNotFound(CellId),
    DirectoryNotFound(CellId),
    BlobNotFound(NoteCommitment),
}

// =============================================================================
// AIR constraint sketch (documentation of what the prover enforces)
// =============================================================================

/// Documents the AIR constraints that validate VFS operations.
///
/// These are NOT new constraints -- they map onto existing Effect VM rows.
/// This trait exists to make the mapping explicit and testable.
pub trait VfsAirConstraints {
    /// Volume balance continuity:
    /// `balance_after = balance_before + credit - debit`
    /// Already enforced by Effect VM row for NoteSpend/NoteCreate.
    const BALANCE_CONTINUITY: &'static str =
        "row.balance_after == row.balance_before + row.credit - row.debit";

    /// Blob commitment well-formedness:
    /// `commitment == H(data || volume_id)`
    /// Enforced by NoteCreate constraint (commitment = H(fields || randomness)).
    const BLOB_COMMITMENT: &'static str =
        "row.commitment == poseidon2(row.data_fields || row.volume_cell)";

    /// Directory swap atomicity:
    /// `entry.version_before == expected_version AND nonce_after == nonce_before + 1`
    /// Enforced by SetField constraint with nonce precondition.
    const SWAP_ATOMICITY: &'static str =
        "row.nonce_before == row.expected_nonce AND row.nonce_after == row.nonce_before + 1";

    /// Nullifier uniqueness:
    /// Published nullifier must not already appear in the nullifier set.
    /// Enforced by NoteSpend constraint (Merkle non-membership proof).
    const NULLIFIER_UNIQUENESS: &'static str =
        "nullifier_set.contains(row.nullifier) == false";

    /// Splice atomicity:
    /// Old blob spent AND new blob created in the same trace (consecutive rows).
    /// Enforced by the turn boundary: all effects in one trace are atomic.
    const SPLICE_ATOMICITY: &'static str =
        "trace contains NoteSpend(old) AND NoteCreate(new) with matching volume";
}

/// Marker struct implementing the constraint documentation.
pub struct VfsConstraints;
impl VfsAirConstraints for VfsConstraints {}

// =============================================================================
// Migration callbacks (from nameless writes paper)
// =============================================================================

/// When the underlying storage moves a blob (e.g., during compaction or
/// replication), it notifies the VFS of the new address. In pyana terms,
/// this is a "migration turn": spend the old note, create a new note with
/// the same content but different tree position.
///
/// The migration is proven like any other turn -- the Effect VM ensures
/// the old commitment is consumed and a new one is created with the same
/// content hash (custom constraint: `H(old_data) == H(new_data)`).
#[derive(Clone, Debug)]
pub struct MigrationCallback {
    /// Old commitment being retired.
    pub old_commitment: NoteCommitment,
    /// New commitment (same content, new tree position).
    pub new_commitment: NoteCommitment,
    /// Directories that need entry updates.
    pub affected_dirs: Vec<CellId>,
}

impl MigrationCallback {
    /// Apply this migration: update all affected directory entries to point
    /// to the new commitment. Each update is a swap with version check.
    pub fn apply(
        &self,
        vfs: &mut Vfs,
        caller_cap: &CapRef,
    ) -> Result<EffectTrace, VfsError> {
        let mut trace = EffectTrace::default();

        for dir_id in &self.affected_dirs {
            let dir = vfs
                .directories
                .get_mut(dir_id)
                .ok_or(VfsError::DirectoryNotFound(*dir_id))?;

            // Find the entry pointing to old_commitment.
            let entry_name = dir
                .entries
                .iter()
                .find(|(_, e)| e.target == EntryTarget::Blob(self.old_commitment))
                .map(|(name, _)| name.clone());

            if let Some(name) = entry_name {
                let version = dir.entries[&name].version;
                let cap = CapRef {
                    target: *dir_id,
                    permissions: caller_cap.permissions,
                };
                dir.swap(
                    &name,
                    version,
                    EntryTarget::Blob(self.new_commitment),
                    &cap,
                    &mut trace,
                )
                .map_err(VfsError::Dir)?;

                // Update GC tracking.
                vfs.blob_refs.drop_ref(&self.old_commitment, dir_id);
                vfs.blob_refs.add_ref(self.new_commitment, *dir_id);
            }
        }

        Ok(trace)
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn test_cell_id(seed: u8) -> CellId {
        CellId([seed; 32])
    }

    fn test_spending_key() -> [u8; 32] {
        [0xAA; 32]
    }

    fn make_cap(target: CellId, perms: Permissions) -> CapRef {
        CapRef {
            target,
            permissions: perms,
        }
    }

    // --- Volume tests ---

    #[test]
    fn volume_allocate_and_free() {
        let mut vol = Volume::new(test_cell_id(1), 1000);
        let mut trace = EffectTrace::default();

        vol.allocate(400, &mut trace).unwrap();
        assert_eq!(vol.used, 400);
        assert_eq!(vol.available(), 600);
        assert_eq!(vol.nonce, 1);

        vol.allocate(600, &mut trace).unwrap();
        assert_eq!(vol.used, 1000);
        assert_eq!(vol.available(), 0);

        // Over-allocate fails.
        let err = vol.allocate(1, &mut trace).unwrap_err();
        assert_eq!(
            err,
            VolumeError::InsufficientCapacity {
                requested: 1,
                available: 0,
            }
        );

        // Free some.
        vol.free(500, &mut trace).unwrap();
        assert_eq!(vol.available(), 500);

        // Over-free fails.
        let err = vol.free(501, &mut trace).unwrap_err();
        assert_eq!(
            err,
            VolumeError::Underflow {
                freed: 501,
                used: 500,
            }
        );
    }

    #[test]
    fn volume_tracks_effects() {
        let mut vol = Volume::new(test_cell_id(1), 1000);
        let mut trace = EffectTrace::default();

        vol.allocate(100, &mut trace).unwrap();
        vol.allocate(200, &mut trace).unwrap();
        vol.free(50, &mut trace).unwrap();

        assert_eq!(trace.effects.len(), 3);
        assert!(matches!(trace.effects[0], VfsEffect::VolumeDebit { amount: 100 }));
        assert!(matches!(trace.effects[1], VfsEffect::VolumeDebit { amount: 200 }));
        assert!(matches!(trace.effects[2], VfsEffect::VolumeCredit { amount: 50 }));
    }

    // --- Blob tests ---

    #[test]
    fn blob_create_is_nameless_write() {
        let mut vol = Volume::new(test_cell_id(1), 10000);
        let mut trace = EffectTrace::default();
        let key = test_spending_key();

        let blob = Blob::create(b"hello world".to_vec(), &mut vol, &key, &mut trace).unwrap();

        // The commitment is deterministic (content-addressed).
        let expected = Blob::compute_commitment(b"hello world", &vol.cell_id);
        assert_eq!(blob.commitment, expected);

        // Volume was charged.
        assert_eq!(vol.used, 11);

        // Creating the same content again yields the same commitment (content-addressed!).
        let blob2 = Blob::create(b"hello world".to_vec(), &mut vol, &key, &mut trace).unwrap();
        assert_eq!(blob.commitment, blob2.commitment);
    }

    #[test]
    fn blob_splice_atomic() {
        let mut vol = Volume::new(test_cell_id(1), 10000);
        let mut trace = EffectTrace::default();
        let key = test_spending_key();

        let mut blob = Blob::create(b"hello world".to_vec(), &mut vol, &key, &mut trace).unwrap();
        let old_commitment = blob.commitment;

        // Splice: replace "world" with "pyana"
        let new_blob =
            blob.splice(6, 5, b"pyana", &mut vol, &key, &mut trace).unwrap();

        // Old blob is spent.
        assert!(blob.spent);
        // New blob has updated content.
        assert_eq!(new_blob.data, b"hello pyana");
        // New commitment differs from old.
        assert_ne!(new_blob.commitment, old_commitment);
        // New blob is not spent.
        assert!(!new_blob.spent);

        // Trace contains spend + create for the splice.
        let create_count = trace
            .effects
            .iter()
            .filter(|e| matches!(e, VfsEffect::CreateBlob { .. }))
            .count();
        let spend_count = trace
            .effects
            .iter()
            .filter(|e| matches!(e, VfsEffect::SpendBlob { .. }))
            .count();
        assert_eq!(create_count, 2); // original + spliced
        assert_eq!(spend_count, 1); // original consumed
    }

    #[test]
    fn blob_splice_size_change() {
        let mut vol = Volume::new(test_cell_id(1), 10000);
        let mut trace = EffectTrace::default();
        let key = test_spending_key();

        let mut blob = Blob::create(b"abc".to_vec(), &mut vol, &key, &mut trace).unwrap();
        assert_eq!(vol.used, 3);

        // Grow: replace "b" with "xyz" (3 -> 5)
        let new_blob = blob.splice(1, 1, b"xyz", &mut vol, &key, &mut trace).unwrap();
        assert_eq!(new_blob.data, b"axyzc");
        assert_eq!(vol.used, 5); // grew by 2
    }

    #[test]
    fn blob_delete_frees_volume() {
        let mut vol = Volume::new(test_cell_id(1), 10000);
        let mut trace = EffectTrace::default();
        let key = test_spending_key();

        let mut blob = Blob::create(b"data".to_vec(), &mut vol, &key, &mut trace).unwrap();
        assert_eq!(vol.used, 4);

        blob.delete(&mut vol, &key, &mut trace).unwrap();
        assert_eq!(vol.used, 0);
        assert!(blob.spent);
    }

    #[test]
    fn blob_double_spend_rejected() {
        let mut vol = Volume::new(test_cell_id(1), 10000);
        let mut trace = EffectTrace::default();
        let key = test_spending_key();

        let mut blob = Blob::create(b"data".to_vec(), &mut vol, &key, &mut trace).unwrap();
        blob.delete(&mut vol, &key, &mut trace).unwrap();

        // Cannot delete again.
        let err = blob.delete(&mut vol, &key, &mut trace).unwrap_err();
        assert_eq!(err, SpliceError::AlreadySpent);

        // Cannot splice either.
        let err = blob.splice(0, 1, b"x", &mut vol, &key, &mut trace).unwrap_err();
        assert_eq!(err, SpliceError::AlreadySpent);
    }

    // --- Directory tests ---

    #[test]
    fn directory_insert_and_lookup() {
        let dir_cell = test_cell_id(2);
        let owner = test_cell_id(1);
        let mut dir = Directory::new(dir_cell, owner);
        let mut trace = EffectTrace::default();
        let cap = make_cap(dir_cell, Permissions::ALL);

        let blob_commitment = NoteCommitment([0x42; 32]);
        dir.insert(
            b"readme.txt".to_vec(),
            EntryTarget::Blob(blob_commitment),
            &cap,
            &mut trace,
        )
        .unwrap();

        let entry = dir.lookup(b"readme.txt").unwrap();
        assert_eq!(entry.target, EntryTarget::Blob(blob_commitment));
        assert_eq!(entry.version, 1);
    }

    #[test]
    fn directory_swap_version_check() {
        let dir_cell = test_cell_id(2);
        let owner = test_cell_id(1);
        let mut dir = Directory::new(dir_cell, owner);
        let mut trace = EffectTrace::default();
        let cap = make_cap(dir_cell, Permissions::ALL);

        let blob_v1 = NoteCommitment([0x01; 32]);
        let blob_v2 = NoteCommitment([0x02; 32]);

        dir.insert(b"file".to_vec(), EntryTarget::Blob(blob_v1), &cap, &mut trace)
            .unwrap();

        // Swap with correct version succeeds.
        let new_ver = dir
            .swap(b"file", 1, EntryTarget::Blob(blob_v2), &cap, &mut trace)
            .unwrap();
        assert_eq!(new_ver, 2);
        assert_eq!(
            dir.lookup(b"file").unwrap().target,
            EntryTarget::Blob(blob_v2)
        );

        // Swap with stale version fails.
        let blob_v3 = NoteCommitment([0x03; 32]);
        let err = dir
            .swap(b"file", 1, EntryTarget::Blob(blob_v3), &cap, &mut trace)
            .unwrap_err();
        assert_eq!(
            err,
            DirError::VersionMismatch {
                name: b"file".to_vec(),
                expected: 1,
                actual: 2,
            }
        );
    }

    #[test]
    fn directory_capability_enforcement() {
        let dir_cell = test_cell_id(2);
        let owner = test_cell_id(1);
        let mut dir = Directory::new(dir_cell, owner);
        let mut trace = EffectTrace::default();

        // Read-only cap cannot insert.
        let read_cap = make_cap(dir_cell, Permissions::READ);
        let err = dir
            .insert(
                b"evil".to_vec(),
                EntryTarget::Blob(NoteCommitment([0; 32])),
                &read_cap,
                &mut trace,
            )
            .unwrap_err();
        assert_eq!(err, DirError::PermissionDenied);

        // Wrong target cap cannot insert.
        let wrong_cap = make_cap(test_cell_id(99), Permissions::ALL);
        let err = dir
            .insert(
                b"evil".to_vec(),
                EntryTarget::Blob(NoteCommitment([0; 32])),
                &wrong_cap,
                &mut trace,
            )
            .unwrap_err();
        assert_eq!(err, DirError::PermissionDenied);
    }

    #[test]
    fn directory_rename_atomic() {
        let dir_cell = test_cell_id(2);
        let owner = test_cell_id(1);
        let mut dir = Directory::new(dir_cell, owner);
        let mut trace = EffectTrace::default();
        let cap = make_cap(dir_cell, Permissions::ALL);

        let blob = NoteCommitment([0x42; 32]);
        dir.insert(b"old_name".to_vec(), EntryTarget::Blob(blob), &cap, &mut trace)
            .unwrap();

        dir.rename(b"old_name", b"new_name".to_vec(), &cap, &mut trace)
            .unwrap();

        assert!(dir.lookup(b"old_name").is_none());
        assert_eq!(
            dir.lookup(b"new_name").unwrap().target,
            EntryTarget::Blob(blob)
        );

        // Trace has both clear and set effects for rename.
        let set_count = trace
            .effects
            .iter()
            .filter(|e| matches!(e, VfsEffect::SetEntry { .. }))
            .count();
        assert_eq!(set_count, 3); // insert + clear(old) + set(new)
    }

    // --- GC tests ---

    #[test]
    fn gc_tracks_references() {
        let mut tracker = BlobRefTracker::new();
        let blob = NoteCommitment([0x42; 32]);
        let dir1 = test_cell_id(1);
        let dir2 = test_cell_id(2);

        tracker.add_ref(blob, dir1);
        tracker.add_ref(blob, dir2);
        assert!(tracker.is_referenced(&blob));

        // Drop one ref -- still referenced.
        let gc_ready = tracker.drop_ref(&blob, &dir1);
        assert!(!gc_ready);
        assert!(tracker.is_referenced(&blob));

        // Drop last ref -- eligible for GC.
        let gc_ready = tracker.drop_ref(&blob, &dir2);
        assert!(gc_ready);
        assert!(!tracker.is_referenced(&blob));
    }

    // --- Integration: VFS write_file ---

    #[test]
    fn vfs_write_file_end_to_end() {
        let mut vfs = Vfs::new();
        let vol_id = test_cell_id(1);
        let dir_id = test_cell_id(2);
        let owner = test_cell_id(3);

        vfs.create_volume(vol_id, 10000);
        vfs.create_directory(dir_id, owner);

        let cap = make_cap(dir_id, Permissions::ALL);
        let key = test_spending_key();

        let (receipt, trace) = vfs
            .write_file(&dir_id, b"hello.txt".to_vec(), b"file content".to_vec(), &vol_id, &key, &cap)
            .unwrap();

        // Receipt has a valid commitment.
        assert_ne!(receipt.commitment.0, [0u8; 32]);
        assert_eq!(receipt.size, 12); // "file content".len()

        // Volume was charged.
        assert_eq!(vfs.volumes[&vol_id].used, 12);

        // Directory has the entry.
        let dir = &vfs.directories[&dir_id];
        let entry = dir.lookup(b"hello.txt").unwrap();
        assert_eq!(entry.target, EntryTarget::Blob(receipt.commitment));

        // GC tracker knows about the reference.
        assert!(vfs.blob_refs.is_referenced(&receipt.commitment));

        // Trace has volume debit + blob create + dir set = 3 effects.
        assert_eq!(trace.effects.len(), 3);
    }

    #[test]
    fn vfs_move_file_updates_gc() {
        let mut vfs = Vfs::new();
        let vol_id = test_cell_id(1);
        let src_dir = test_cell_id(2);
        let dst_dir = test_cell_id(3);
        let owner = test_cell_id(4);

        vfs.create_volume(vol_id, 10000);
        vfs.create_directory(src_dir, owner);
        vfs.create_directory(dst_dir, owner);

        let src_cap = make_cap(src_dir, Permissions::ALL);
        let key = test_spending_key();

        let (receipt, _) = vfs
            .write_file(&src_dir, b"doc.pdf".to_vec(), b"PDF data".to_vec(), &vol_id, &key, &src_cap)
            .unwrap();

        // Move from src to dst.
        let trace = vfs
            .move_file(&src_dir, b"doc.pdf", &dst_dir, b"moved.pdf".to_vec(), &src_cap)
            .unwrap();

        // Source no longer has it.
        assert!(vfs.directories[&src_dir].lookup(b"doc.pdf").is_none());
        // Dest has it.
        assert_eq!(
            vfs.directories[&dst_dir].lookup(b"moved.pdf").unwrap().target,
            EntryTarget::Blob(receipt.commitment)
        );

        // GC: blob is still referenced (by dst_dir now).
        assert!(vfs.blob_refs.is_referenced(&receipt.commitment));

        // Trace has clear(src) + set(dst) = 2 set_entry effects.
        let set_count = trace
            .effects
            .iter()
            .filter(|e| matches!(e, VfsEffect::SetEntry { .. }))
            .count();
        assert_eq!(set_count, 2);
    }

    // --- Migration callback test ---

    #[test]
    fn migration_updates_directory_entries() {
        let mut vfs = Vfs::new();
        let vol_id = test_cell_id(1);
        let dir_id = test_cell_id(2);
        let owner = test_cell_id(3);

        vfs.create_volume(vol_id, 10000);
        vfs.create_directory(dir_id, owner);

        let cap = make_cap(dir_id, Permissions::ALL);
        let key = test_spending_key();

        let (receipt, _) = vfs
            .write_file(&dir_id, b"data.bin".to_vec(), b"original".to_vec(), &vol_id, &key, &cap)
            .unwrap();

        // Simulate migration: storage moved the blob.
        let new_commitment = NoteCommitment([0xFF; 32]);
        let migration = MigrationCallback {
            old_commitment: receipt.commitment,
            new_commitment,
            affected_dirs: vec![dir_id],
        };

        let trace = migration.apply(&mut vfs, &cap).unwrap();

        // Directory entry now points to new commitment.
        let entry = vfs.directories[&dir_id].lookup(b"data.bin").unwrap();
        assert_eq!(entry.target, EntryTarget::Blob(new_commitment));

        // GC tracking updated.
        assert!(!vfs.blob_refs.is_referenced(&receipt.commitment));
        assert!(vfs.blob_refs.is_referenced(&new_commitment));

        // Trace contains the swap effect.
        assert!(!trace.effects.is_empty());
    }

    // --- Effect trace cost accounting ---

    #[test]
    fn effect_trace_cost_accounting() {
        let mut trace = EffectTrace::default();
        trace.push(VfsEffect::CreateBlob {
            commitment: NoteCommitment([0; 32]),
            size: 1000,
        });
        trace.push(VfsEffect::SpendBlob {
            nullifier: Nullifier([0; 32]),
            commitment: NoteCommitment([0; 32]),
        });
        trace.push(VfsEffect::SetEntry {
            dir_cell: CellId([0; 32]),
            field_idx: 0,
            value: [0; 32],
        });

        // Cost: (100 + 1000) + 50 + 30 = 1180
        assert_eq!(trace.total_cost(), 1180);
    }

    // --- Permission attenuation ---

    #[test]
    fn permissions_attenuate_correctly() {
        let all = Permissions::ALL;
        let read_write = all.attenuate(Permissions(0b0011));

        assert!(read_write.contains(Permissions::READ));
        assert!(read_write.contains(Permissions::WRITE));
        assert!(!read_write.contains(Permissions::SPLICE));
        assert!(!read_write.contains(Permissions::DELETE));

        // Attenuating again can only remove, never add.
        let read_only = read_write.attenuate(Permissions::READ);
        assert!(read_only.contains(Permissions::READ));
        assert!(!read_only.contains(Permissions::WRITE));
    }
}
