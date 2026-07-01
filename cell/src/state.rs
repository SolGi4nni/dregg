use dregg_circuit::cap_root::fold_bytes32;
use dregg_circuit::field::BabyBear;
use dregg_circuit::heap_root::{
    HeapLeaf, compute_canonical_heap_root_8 as compute_canonical_heap_root_8_circuit,
    compute_heap_root as compute_heap_root_felt, empty_heap_root as empty_heap_root_felt,
    heap_addr,
};
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;

/// A generic 32-byte field element.
/// Could represent a BabyBear element, a BLAKE3 hash, a scalar, etc.
pub type FieldElement = [u8; 32];

/// The zero field element.
pub const FIELD_ZERO: FieldElement = [0u8; 32];

/// Number of user-defined state slots per cell.
pub const STATE_SLOTS: usize = 16;

/// **Protocol-reserved ext-field key for the refusal audit record** (`>= STATE_SLOTS`, so it
/// lands in the committed [`CellState::fields_map`] / [`fields_root`], NOT a user-addressable
/// `fields[0..15]` indexed slot). The deployed `apply_refusal` writes the
/// `(offered_action_commitment, reason)` audit commitment here so it is FOLDED by
/// `compute_authority_digest_felt` (via `fields_root`) into the rotated AFTER block's
/// `record_digest` limb — matching the Lean SPEC `TurnExecutorFull.refusalField` (the named
/// `"refusal"` record slot lands in `fields_root`), which makes the rotated `refusalV3`
/// record-pin a genuine forcing gate. Keyed high to avoid clashing with app ext-field usage.
pub const REFUSAL_AUDIT_EXT_KEY: u64 = 0x0000_0001_0000_0000; // 2^32, far above app ext keys

/// Number of kernel-owned side-table roots in the dedicated `system_roots`
/// sub-block (`_RECORD-LAYER-UPGRADE.md` §C, Option C1; record-layer STAGE 3).
/// One root per side-table; parallel to (and disjoint from) the 16 user
/// `fields[0..15]` and the `fields_root` map.
pub const N_SYSTEM_ROOTS: usize = 8;

/// Kernel-owned indices into [`CellState::system_roots`] — the dedicated home
/// for each side-table's committed root (`_RECORD-LAYER-UPGRADE.md` §C). The
/// IR-extension originally STOLE the user `fields[1..7]` cells for these roots
/// (`_IR-EXTENSION-DESIGN.md:138-143`), colliding with app data; STAGE 0–2 freed
/// the user namespace onto `fields_root`, and STAGE 3 gives the side-table roots
/// their OWN namespace so they never collide with user fields again. Apps never
/// address these (no `set_field*` reaches them); only the kernel's escrow/queue/
/// nullifier/… transitions mutate them.
///
/// Mirrors the Lean `Dregg2.Exec.SystemRoots.systemRoot::*` constants.
pub mod system_root {
    /// `escrows` list digest (createEscrow / refund / release / bridge-park).
    pub const ESCROW: usize = 0;
    /// `queues` table digest (allocate / enqueue / dequeue / resize / pipeline;
    /// FIFO order intrinsic to the digest).
    pub const QUEUE: usize = 1;
    /// refcount table digest (dropRef GC); was the running prover's `fields[3]`.
    pub const REFCOUNT: usize = 2;
    /// `swiss` sturdyref table digest (export / enliven / handoff / drop); was
    /// `fields[4]`.
    pub const STURDYREF: usize = 3;
    /// `delegations` keyed-map digest (refresh / revoke delegation epoch).
    pub const DELEG: usize = 4;
    /// `nullifiers` accumulator digest (noteSpend append; non-membership via the
    /// spend-proof PI cross-binding).
    pub const NULLIFIER: usize = 5;
    /// `commitments` accumulator digest (noteCreate append).
    pub const COMMIT: usize = 6;
    /// `sealedBoxes` store digest (seal / unseal / createSealPair); its OWN home
    /// now, no longer folded into `cap_root`.
    pub const SEALED_BOXES: usize = 7;
}

/// Visibility level for a cell state field.
///
/// Controls progressive disclosure: fields can be fully public, committed (hidden
/// behind a hash), or selectively disclosable (committed but provable via ZK).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum FieldVisibility {
    /// Value stored in plaintext — anyone can read it.
    Public,
    /// Only a hash commitment is stored publicly. The actual value is private.
    Committed,
    /// Committed, but the holder can produce membership/predicate proofs
    /// over the value without revealing it.
    SelectivelyDisclosable,
}

impl Default for FieldVisibility {
    fn default() -> Self {
        FieldVisibility::Public
    }
}

/// The mutable state of an agent cell.
///
/// Audit P0-1 sealing: `nonce`, `balance`, `proved_state`, and
/// `delegation_epoch` are `pub(crate)` — external code reads them via
/// accessors ([`CellState::nonce`], [`CellState::balance`],
/// [`CellState::proved_state`], [`CellState::delegation_epoch`]) and mutates
/// them only through `apply_balance_change`, `increment_nonce`,
/// `bump_delegation_epoch`, and `set_proved_state`. `fields[]`,
/// `field_visibility[]`, and `commitments[]` remain public arrays because the
/// executor mutates them by index in tight loops.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CellState {
    /// 16 user-defined state fields (like Mina's app_state).
    pub fields: [FieldElement; STATE_SLOTS],
    /// Visibility level for each field slot.
    pub field_visibility: [FieldVisibility; STATE_SLOTS],
    /// Hash commitments for non-public fields (BLAKE3 hash of value || nonce).
    /// `None` for Public fields, `Some(hash)` for Committed/SelectivelyDisclosable.
    pub commitments: [Option<[u8; 32]>; STATE_SLOTS],
    /// Monotonically increasing action counter. Sealed (P0-1); mutate via
    /// `increment_nonce`, read via `nonce()`.
    pub(crate) nonce: u64,
    /// SIGNED value balance (THE EPOCH, `docs/EPOCH-DESIGN.md` §5 "signed
    /// wells"). The Lean kernel's ledger is `bal : cell → asset → ℤ` and
    /// `reachable_total_zero` holds because issuer WELLS carry −supply; the
    /// Rust value model now matches: `i64`, encoded at every commitment/wire
    /// boundary via the order-preserving biased two-limb encoding
    /// ([`encode_balance_le`] / [`balance_limbs`] — the range-table limb
    /// discipline).
    ///
    /// Sign discipline is enforced BY VERB, mirroring the Lean dispatch:
    /// ordinary moves go through [`CellState::debit_balance`] /
    /// [`CellState::apply_balance_change`] (refuse to go below zero);
    /// issuer-well moves (mint / genesis issuer-moves) go through
    /// [`CellState::well_debit_balance`] /
    /// [`CellState::apply_balance_change_well`] (may go negative — the well
    /// carries −supply). Sealed (P0-1); read via `balance()`.
    pub(crate) balance: i64,
    /// Whether all 16 state fields were last set by a verified proof.
    /// Becomes `true` only when ALL 16 fields are set by a single proof-authorized action.
    /// Becomes `false` if any field is modified by a non-proof authorization.
    /// Sealed (P0-1); mutate via `set_proved_state`, read via `proved_state()`.
    pub(crate) proved_state: bool,
    /// Delegation epoch counter. Parent cells bump this to signal their children
    /// should refresh their capability snapshots. Children whose snapshot epoch is
    /// behind the parent's current epoch are considered stale.
    /// Sealed (P0-1); mutate via `bump_delegation_epoch`, read via
    /// `delegation_epoch()`.
    #[serde(default)]
    pub(crate) delegation_epoch: u64,
    /// `docs/UNIVERSAL-MAP-ROTATION.md` §2.6 (PI v3): the block height at which
    /// this cell's state was last committed. Folded into the canonical state
    /// commitment as the `committedHeight` limb so the commitment (and its PI
    /// face) is bound to a specific chain height — closing the temporal gate's
    /// prover-chosen-height note. A legacy (never-committed) cell carries 0;
    /// the absorption is a uniform no-op for legacy cells.
    #[serde(default)]
    pub(crate) committed_height: u64,
    /// Stage 1 / `DESIGN-captp-integration.md` §4.1: per-cell CapTP swiss
    /// table Merkle root. Initialised to the empty-tree sentinel; populated
    /// by `Effect::ExportSturdyRef` and `Effect::EnlivenRef` in Stage 7.
    ///
    /// Included in `compute_canonical_state_commitment` so the cell's
    /// state commitment binds its CapTP exports.
    #[serde(default)]
    pub swiss_table_root: [u8; 32],
    /// Stage 1 / `DESIGN-captp-integration.md` §4.3: per-cell CapTP refcount
    /// table Merkle root (cross-federation reference counts). Initialised
    /// to the empty-tree sentinel; populated by `Effect::ExportSturdyRef`
    /// and `Effect::DropRef` in Stage 7.
    #[serde(default)]
    pub refcount_table_root: [u8; 32],
    /// `_RECORD-LAYER-UPGRADE.md` §B (Stage 0): the committed root of the
    /// **user-field MAP** — an unbounded `key → FieldElement` accumulator over
    /// keys `>= STATE_SLOTS` (16). The hybrid unsqueeze of the 16-fixed-slot
    /// cell: keys `0..15` stay in `fields[]` (existing access byte-identical);
    /// keys `>= 16` live in [`fields_map`] and are committed here.
    ///
    /// `fields_root` is the **committed** root (the on-cell/in-circuit
    /// witness); [`fields_map`] is the prover-side store whose digest this is.
    /// Initialised to [`empty_fields_root`] — the digest of the empty map — so
    /// a legacy cell (no map entries) carries the FIXED empty-map constant and
    /// its canonical commitment is unchanged when this is later folded in
    /// (Stage 1). `#[serde(default)]` keeps every existing serialized cell
    /// deserializing (the additive pattern already used for
    /// `swiss_table_root`/`refcount_table_root`).
    ///
    /// Stage 0 is strictly additive: this is NOT yet absorbed into
    /// `compute_canonical_state_commitment` (that is Stage 1, with a `v2->v3`
    /// bump). It is present, load-bearing for the map read/write path, and
    /// recomputed on every map write.
    #[serde(default = "empty_fields_root")]
    pub fields_root: [u8; 32],
    /// `_RECORD-LAYER-UPGRADE.md` §B.3: the **prover-side witness** store for
    /// the user-field map — the actual `key (>= 16) -> value` entries whose
    /// digest is [`fields_root`]. Not itself committed (its digest is).
    /// `BTreeMap` for a canonical (sorted-key) iteration order so the digest is
    /// deterministic. `#[serde(default)]` ⇒ old cells deserialize with an empty
    /// map.
    #[serde(default)]
    pub fields_map: BTreeMap<u64, FieldElement>,
    /// `_RECORD-LAYER-UPGRADE.md` §C (record-layer STAGE 3): the dedicated
    /// `system_roots` sub-block — each kernel-owned side-table's committed root
    /// at its OWN fixed index ([`system_root`]). Parallel to (and disjoint from)
    /// the user `fields[]` and the `fields_root` map: a `set_field*` can NEVER
    /// reach these, and the kernel's escrow/queue/nullifier/… transitions can
    /// only touch these (never user fields) — strictly stronger namespace
    /// separation than today (where the circuit aliased swiss/refcount into
    /// user-addressable `fields[3]/fields[4]`).
    ///
    /// Their committed digest [`compute_system_roots_digest`] is folded into the
    /// canonical commitment (with a `v3->v4` bump) so a verifier binds the WHOLE
    /// side-table state. A legacy cell carries the all-zero default — whose
    /// digest is the cell-INDEPENDENT [`empty_system_roots_digest`] constant — so
    /// the absorption is a uniform no-op for legacy cells (the STAGE 3
    /// backward-compat keystone, mirrored in Lean by
    /// `SystemRoots.legacy_commitS_absorbs_empty_roots`). `#[serde(default)]`
    /// keeps every existing serialized cell deserializing.
    #[serde(default = "default_system_roots")]
    pub system_roots: [FieldElement; N_SYSTEM_ROOTS],
    /// `docs/UNIVERSAL-MAP-ROTATION.md` §2.4: the committed openable sorted-
    /// Poseidon2 root of the cell's **heap** — a `(collection_id, key) →
    /// FieldElement` map. Included in `compute_canonical_state_commitment` so
    /// the cell's state commitment binds heap state. A legacy (no-heap-activity)
    /// cell carries the FIXED [`empty_heap_root`] constant so the absorption is
    /// a uniform no-op across legacy cells.
    #[serde(default = "empty_heap_root")]
    pub heap_root: [u8; 32],
    /// `docs/UNIVERSAL-MAP-ROTATION.md` §2.4: the **prover-side witness** store
    /// for the heap — the actual `(collection, key) → value` entries whose
    /// digest is [`heap_root`]. Not itself committed (its digest is).
    /// `BTreeMap` for deterministic iteration order so the root is canonical.
    /// `#[serde(default)]` keeps every existing serialized cell deserializing.
    #[serde(default)]
    pub heap_map: BTreeMap<(u32, u32), FieldElement>,
}

/// The all-empty-tree-sentinel `system_roots` sub-block a LEGACY cell carries:
/// every side-table empty. Cell-independent, so its digest folds into the
/// canonical commitment as a uniform no-op.
pub fn default_system_roots() -> [FieldElement; N_SYSTEM_ROOTS] {
    [FIELD_ZERO; N_SYSTEM_ROOTS]
}

/// Domain-separation context for the `system_roots` sub-block digest
/// ([`compute_system_roots_digest`]). Distinct from the canonical-state-commitment
/// and `fields_root` contexts so a side-table digest can never be confused with a
/// full-cell commitment or a user-field-map root.
pub const SYSTEM_ROOTS_CONTEXT: &str = "dregg-cell:system-roots v1";

/// Compute the committed digest over the dedicated `system_roots` sub-block.
///
/// The Rust shadow of the Lean `SystemRoots.systemRootsDigest`
/// (`ListCommit.listDigest` over the ordered side-table roots): a length-seeded
/// BLAKE3 sponge over the 8 fixed-order root cells. Order is kernel-fixed (the
/// [`system_root`] index assignment), so the digest is order-canonical and
/// injective enough that two distinct sub-blocks cannot share a digest (the
/// anti-ghost guarantee — a `:= 0` stub is forbidden). The all-zero sub-block
/// yields the fixed [`empty_system_roots_digest`].
/// A `new_derive_key(SYSTEM_ROOTS_CONTEXT)` hasher cached at its keyed initial
/// state. `Hasher::clone` copies that keyed state, so cloning + absorbing is
/// BYTE-IDENTICAL to a fresh `new_derive_key` + absorbing, while skipping the
/// key-derivation compression on each call. This digest is recomputed inside
/// every `compute_canonical_state_commitment` (the per-touched-cell Merkle leaf),
/// so the saved compression is on the hot post-state-root path.
fn system_roots_base() -> blake3::Hasher {
    static BASE: std::sync::OnceLock<blake3::Hasher> = std::sync::OnceLock::new();
    BASE.get_or_init(|| blake3::Hasher::new_derive_key(SYSTEM_ROOTS_CONTEXT))
        .clone()
}

pub fn compute_system_roots_digest(roots: &[FieldElement; N_SYSTEM_ROOTS]) -> [u8; 32] {
    // Fast path: a legacy (no-side-table-activity) cell carries the all-zero
    // sub-block, whose digest is the cell-independent `empty_system_roots_digest()`
    // constant. Return it WITHOUT re-running the sponge — a 256-byte equality check
    // is ~30x cheaper than the BLAKE3 fold, and the returned bytes are IDENTICAL to
    // the full computation (the constant IS this function over the zero block). This
    // is the common case on the hot per-cell-commitment path (ordinary balance/nonce
    // cells never touch the kernel side-table roots).
    if roots == &default_system_roots() {
        return empty_system_roots_digest();
    }
    let mut hasher = system_roots_base();
    // Length prefix (seed): pins the root count (always N_SYSTEM_ROOTS, but the
    // seed keeps the sponge shape identical to the fields-root accumulator).
    hasher.update(&(N_SYSTEM_ROOTS as u64).to_le_bytes());
    for root in roots.iter() {
        hasher.update(root);
    }
    *hasher.finalize().as_bytes()
}

/// The digest of the all-empty `system_roots` sub-block — the FIXED constant a
/// legacy (no-side-table-activity) cell contributes. Cell-independent: folding it
/// into the canonical commitment is a no-op across legacy cells (the STAGE 3
/// backward-compat keystone, mirrored in Lean by
/// `SystemRoots.emptySystemRootsDigest`).
pub fn empty_system_roots_digest() -> [u8; 32] {
    // Cached process constant. Computes the sponge DIRECTLY (not via
    // `compute_system_roots_digest`, which fast-paths to THIS function — calling
    // back would recurse). The result is byte-identical to the full fold over the
    // all-zero sub-block.
    static EMPTY: std::sync::OnceLock<[u8; 32]> = std::sync::OnceLock::new();
    *EMPTY.get_or_init(|| {
        let roots = default_system_roots();
        let mut hasher = system_roots_base();
        hasher.update(&(N_SYSTEM_ROOTS as u64).to_le_bytes());
        for root in roots.iter() {
            hasher.update(root);
        }
        *hasher.finalize().as_bytes()
    })
}

/// Domain-separation context for the user-field-map keyed digest
/// ([`CellState::fields_root`]). Distinct from the canonical-state-commitment
/// context so a map root can never be confused with a full-cell commitment.
pub const FIELDS_ROOT_CONTEXT: &str = "dregg-cell:fields-root v1";

/// The sorted-tree leaf set committing a user-field map, in the OPENABLE
/// scheme. Each overflow entry `(key, value)` becomes a [`HeapLeaf`] keyed by
/// the domain-tagged sort-key felt [`field_key_hash`] and valued by the folded
/// 32-byte field value. The cell that can refuse carries the
/// [`REFUSAL_AUDIT_EXT_KEY`] slot RESERVED (a position-stable value-ZERO leaf)
/// so the in-circuit refusal map-op is a value WRITE at a present key (the
/// noteSpend `.write` discipline) rather than a re-indexing insert.
///
/// This is the SINGLE leaf set both the cell-side root and the in-circuit
/// map-op (`prove_vm_descriptor2`'s `map_heaps`) build their
/// [`dregg_circuit::heap_root::CanonicalHeapTree`] over — so the committed
/// `fields_root` limb is the OPENABLE Poseidon2 root the refusal map-op WRITE
/// gate constrains in-circuit (`EffectVmEmitRotationV3.refusalFieldsWriteV3`),
/// NOT an opaque `poseidon2(blake3(map))` no gate could bind.
pub fn fields_root_leaves(map: &BTreeMap<u64, FieldElement>) -> Vec<HeapLeaf> {
    let mut leaves: Vec<HeapLeaf> = map
        .iter()
        .map(|(key, value)| HeapLeaf {
            addr: field_key_hash(*key),
            value: fold_bytes32(value),
        })
        .collect();
    // RESERVE the protocol-reserved refusal-audit slot (position-stable, value
    // ZERO) when the map does not already carry it — so a refusal WRITE opens
    // the slot's existing path rather than re-indexing the sorted tree.
    let audit_addr = field_key_hash(REFUSAL_AUDIT_EXT_KEY);
    if !leaves.iter().any(|l| l.addr == audit_addr) {
        leaves.push(HeapLeaf {
            addr: audit_addr,
            value: BabyBear::ZERO,
        });
    }
    leaves
}

/// The canonical sort-key felt for an overflow user-field key. A
/// domain-tagged Poseidon2 image of the unbounded `u64` key (both 32-bit limbs
/// fold, so [`REFUSAL_AUDIT_EXT_KEY`] = `2^32` binds its high limb). Mirrors
/// `dregg_circuit::openable_fields_root::field_key_hash` — pinned equal by the
/// differential — so the cell-side root and the in-circuit map-op address the
/// same sorted positions.
pub fn field_key_hash(key: u64) -> BabyBear {
    dregg_circuit::openable_fields_root::field_key_hash(key)
}

/// The OPENABLE root of the **empty** user-field map — the fixed `fields_root`
/// constant a legacy (no-overflow) cell carries: the sorted-tree root over the
/// sentinels PLUS the reserved (value-ZERO) refusal-audit slot. Cell-independent
/// (the Stage 0 backward-compat keystone, mirrored in Lean by
/// `FieldsMap.fieldsRoot_empty_legacy` — every legacy cell shares ONE constant,
/// so absorbing it into the canonical commitment is a uniform no-op across
/// legacy cells).
pub fn empty_fields_root() -> [u8; 32] {
    compute_fields_root(&BTreeMap::new())
}

/// Compute the OPENABLE root committing a user-field map.
///
/// The Rust realization of the Lean `FieldsMap.fieldsRoot` openable digest: the
/// sorted Poseidon2 binary Merkle root (the SAME `dregg_circuit::heap_root`
/// scheme the nullifier / accounts / heap roots use) over the
/// [`fields_root_leaves`]. Sorted by sort-key (`field_key_hash`), sentinel-
/// bracketed, so the root is order-canonical and injective (two distinct maps
/// cannot share a root — the anti-vacuity guarantee, a `:= 0` stub is
/// forbidden). An empty map yields the fixed [`empty_fields_root`].
///
/// Because the root is an OPENABLE sorted-Poseidon2 tree (not a BLAKE3 sponge),
/// the deployed committed `fields_root` limb (36) is the root a ledgerless
/// light client can constrain via the refusal map-op WRITE gate: a forged
/// post-`fields_root` is UNSAT vs the genuine `insert(pre_root, AUDIT_KEY,
/// audit_felt)` (`circuit/tests/vk_epoch_refusal_lifecycle_light_client_binding.rs`).
pub fn compute_fields_root(map: &BTreeMap<u64, FieldElement>) -> [u8; 32] {
    let root = compute_heap_root_felt(fields_root_leaves(map));
    babybear_to_bytes32(root)
}

/// The canonical 32-byte encoding of a BabyBear felt: the felt's 4
/// little-endian bytes in the low 4 positions, the rest zero. Deterministic
/// and injective on canonical BabyBear values (< p), so distinct roots encode
/// to distinct byte strings.
fn babybear_to_bytes32(felt: BabyBear) -> [u8; 32] {
    let mut out = [0u8; 32];
    out[0..4].copy_from_slice(&felt.as_u32().to_le_bytes());
    out
}

/// The digest of the **empty** heap — the fixed `heap_root` constant a legacy
/// (no-heap-activity) cell carries. Cell-independent: folding it into the
/// canonical commitment is a no-op for legacy cells (`UNIVERSAL-MAP-ROTATION.md`
/// §2.4).
pub fn empty_heap_root() -> [u8; 32] {
    babybear_to_bytes32(empty_heap_root_felt())
}

/// Compute the canonical heap root over a `(collection_id, key) → value` map.
///
/// The Rust shadow of the Lean `Substrate.Heap.root`: a sorted Poseidon2 binary
/// Merkle tree over `hash[hash[coll, key], value]` leaves. Values are folded
/// from 32-byte `FieldElement`s to a single BabyBear felt so the leaf shape
/// matches `circuit::heap_root::HeapLeaf`.
pub fn compute_heap_root(map: &BTreeMap<(u32, u32), FieldElement>) -> [u8; 32] {
    let leaves: Vec<HeapLeaf> = map
        .iter()
        .map(|((coll, key), value)| HeapLeaf {
            addr: heap_addr(BabyBear::new(*coll), BabyBear::new(*key)),
            value: fold_bytes32(value),
        })
        .collect();
    babybear_to_bytes32(compute_heap_root_felt(leaves))
}

/// Compute the FAITHFUL 8-felt canonical heap root over a `(collection_id, key) → value` map:
/// the FULL native-`heap_node8` (arity-16) sorted-Poseidon2 Merkle root the EffectVM circuit's
/// 8-felt `heap_root` column GROUP carries (lane 0 ‖ lanes 1..7). Lane 0 is byte-identical to the
/// lane-0 projection of [`compute_heap_root`] as a felt (the historical scalar root); lanes 1..7 are
/// the ~124-bit completion the faithful weld commits at the rotated-block extras 58..64
/// (`compute_rotated_pre_limbs`). The 8-felt twin of
/// [`crate::commitment::compute_canonical_capability_root_8`]. Cell and circuit fold through the SAME
/// implementation, so they agree lane-for-lane (the GENTIAN differential guards it).
pub fn compute_canonical_heap_root_8(map: &BTreeMap<(u32, u32), FieldElement>) -> [BabyBear; 8] {
    let leaves: Vec<HeapLeaf> = map
        .iter()
        .map(|((coll, key), value)| HeapLeaf {
            addr: heap_addr(BabyBear::new(*coll), BabyBear::new(*key)),
            value: fold_bytes32(value),
        })
        .collect();
    compute_canonical_heap_root_8_circuit(leaves)
}

/// The public view of a field — either the actual value (if public) or its commitment hash.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PublicFieldView {
    /// The field value is revealed (public).
    Revealed(FieldElement),
    /// The field value is hidden; only the commitment hash is visible.
    Committed([u8; 32]),
}

impl CellState {
    /// Read accessor for `nonce`. Sealed for P0-1.
    ///
    /// External code cannot mutate this field directly:
    /// ```compile_fail
    /// # use dregg_cell::CellState;
    /// let mut s = CellState::new(0);
    /// s.nonce = 42;
    /// ```
    #[inline]
    pub fn nonce(&self) -> u64 {
        self.nonce
    }

    /// Read accessor for `balance`. Sealed for P0-1. SIGNED (THE EPOCH):
    /// ordinary cells are kept ≥ 0 by the verb discipline; issuer wells may
    /// legitimately read negative (−supply).
    ///
    /// External code cannot mutate this field directly:
    /// ```compile_fail
    /// # use dregg_cell::CellState;
    /// let mut s = CellState::new(0);
    /// s.balance = i64::MAX;
    /// ```
    #[inline]
    pub fn balance(&self) -> i64 {
        self.balance
    }

    /// Read accessor for `proved_state`. Sealed for P0-1.
    ///
    /// External code cannot mutate this field directly:
    /// ```compile_fail
    /// # use dregg_cell::CellState;
    /// let mut s = CellState::new(0);
    /// s.proved_state = true;
    /// ```
    #[inline]
    pub fn proved_state(&self) -> bool {
        self.proved_state
    }

    /// Read accessor for `delegation_epoch`. Sealed for P0-1.
    ///
    /// External code cannot mutate this field directly:
    /// ```compile_fail
    /// # use dregg_cell::CellState;
    /// let mut s = CellState::new(0);
    /// s.delegation_epoch = 7;
    /// ```
    #[inline]
    pub fn delegation_epoch(&self) -> u64 {
        self.delegation_epoch
    }

    /// Read the `committed_height` field. Sealed-read accessor (P0-1).
    ///
    /// The block height at which this cell's state was last committed.
    #[inline]
    pub fn committed_height(&self) -> u64 {
        self.committed_height
    }

    /// Set the `proved_state` flag. Sealed-write accessor (P0-1).
    ///
    /// The executor calls this after applying a proof-authorized action: it
    /// passes `true` only when all 16 fields were set by a single proof, and
    /// `false` when any non-proof authorization touched the cell.
    #[inline]
    pub fn set_proved_state(&mut self, value: bool) {
        self.proved_state = value;
    }

    /// Raw write of `balance`. Sealed-write accessor (P0-1).
    ///
    /// **Low-level**: callers are expected to be the executor's effect-apply
    /// pipeline or the journal-rollback path. Application code should never
    /// touch this — go through `Effect::Transfer`/`NoteSpend`/`NoteCreate` via
    /// the executor so authorization and conservation are enforced. Provided
    /// because journal restoration needs to put balance back to an exact prior
    /// value on rollback.
    #[inline]
    pub fn set_balance(&mut self, value: i64) {
        self.balance = value;
    }

    /// Raw write of `nonce`. Sealed-write accessor (P0-1).
    ///
    /// **Low-level**: same caveats as `set_balance`. Use `increment_nonce()`
    /// for the common +1 path; this exists for journal-rollback restoration
    /// to an exact prior value.
    #[inline]
    pub fn set_nonce(&mut self, value: u64) {
        self.nonce = value;
    }

    /// Raw write of `delegation_epoch`. Sealed-write accessor (P0-1).
    ///
    /// **Low-level**: same caveats as `set_balance`. Use
    /// `bump_delegation_epoch()` for the common +1 path; this exists for
    /// journal-rollback restoration.
    #[inline]
    pub fn set_delegation_epoch(&mut self, value: u64) {
        self.delegation_epoch = value;
    }

    /// Raw write of `committed_height`. Sealed-write accessor (P0-1).
    ///
    /// **Low-level**: same caveats as `set_balance`. Exists for journal-
    /// rollback restoration to an exact prior height.
    #[inline]
    pub fn set_committed_height(&mut self, value: u64) {
        self.committed_height = value;
    }

    /// Credit balance by `amount`. Returns `false` on `i64` overflow (caller
    /// must check). Sealed-write semantic accessor. Valid on ANY cell —
    /// crediting a (negative) issuer well moves it toward zero, which is how
    /// `burn` returns supply to the well.
    #[inline]
    #[must_use = "balance credit may overflow; the caller must handle the false return"]
    pub fn credit_balance(&mut self, amount: u64) -> bool {
        let Ok(amt) = i64::try_from(amount) else {
            return false;
        };
        match self.balance.checked_add(amt) {
            Some(new) => {
                self.balance = new;
                true
            }
            None => false,
        }
    }

    /// ORDINARY-CELL debit by `amount`: refuses to take the balance below
    /// ZERO. Returns `false` on underflow (caller must check). This is the
    /// verb every ordinary move (transfer source, fee payer, burn target)
    /// uses — only issuer-well verbs may go negative, via
    /// [`well_debit_balance`](Self::well_debit_balance).
    #[inline]
    #[must_use = "balance debit may underflow; the caller must handle the false return"]
    pub fn debit_balance(&mut self, amount: u64) -> bool {
        let Ok(amt) = i64::try_from(amount) else {
            return false;
        };
        if self.balance >= amt {
            self.balance -= amt;
            true
        } else {
            false
        }
    }

    /// ISSUER-WELL debit by `amount`: the balance MAY go negative (the well
    /// carries −supply — `reachable_total_zero`'s issuer rows). Fails only on
    /// `i64` overflow. The EXECUTOR gates who may use this verb (production
    /// authority = control of the issuer cell, never of the recipient); this
    /// accessor is the mechanism, not the policy.
    #[inline]
    #[must_use = "well debit may overflow; the caller must handle the false return"]
    pub fn well_debit_balance(&mut self, amount: u64) -> bool {
        let Ok(amt) = i64::try_from(amount) else {
            return false;
        };
        match self.balance.checked_sub(amt) {
            Some(new) => {
                self.balance = new;
                true
            }
            None => false,
        }
    }

    /// Create a fresh cell state with zero fields and the given balance.
    pub fn new(balance: i64) -> Self {
        CellState {
            fields: [FIELD_ZERO; STATE_SLOTS],
            field_visibility: [FieldVisibility::Public; STATE_SLOTS],
            commitments: [None; STATE_SLOTS],
            nonce: 0,
            balance,
            proved_state: false,
            delegation_epoch: 0,
            committed_height: 0,
            // Stage 1 CapTP-prep: empty-tree sentinels.
            swiss_table_root: [0u8; 32],
            refcount_table_root: [0u8; 32],
            // Record-layer Stage 0: empty user-field map.
            fields_root: empty_fields_root(),
            fields_map: BTreeMap::new(),
            // Record-layer Stage 3: empty (all-sentinel) side-table sub-block.
            system_roots: default_system_roots(),
            // Universal-map rotation §2.4: empty heap.
            heap_root: empty_heap_root(),
            heap_map: BTreeMap::new(),
        }
    }

    // ───────────────────────────────────────────────────────────────────────
    // `_RECORD-LAYER-UPGRADE.md` §C — the dedicated `system_roots` sub-block
    // (record-layer STAGE 3). Kernel-only accessors: a `set_field*` path NEVER
    // reaches these, only the escrow/queue/nullifier/… kernel transitions do.
    // ───────────────────────────────────────────────────────────────────────

    /// Read a kernel-owned side-table root by its [`system_root`] index.
    /// Returns `None` for an out-of-range index.
    pub fn system_root(&self, index: usize) -> Option<&FieldElement> {
        self.system_roots.get(index)
    }

    /// Write a kernel-owned side-table root by its [`system_root`] index.
    /// Returns `true` on success, `false` for an out-of-range index. This is the
    /// ONLY mutator for the sub-block — there is deliberately no `set_field`-style
    /// path that can reach it, so user fields and system roots are disjoint
    /// namespaces with disjoint mutators.
    pub fn set_system_root(&mut self, index: usize, value: FieldElement) -> bool {
        if index < N_SYSTEM_ROOTS {
            self.system_roots[index] = value;
            true
        } else {
            false
        }
    }

    /// The committed digest over the current `system_roots` sub-block — the
    /// single carrier the circuit absorbs into `state_commit`. Recomputed on
    /// demand (the sub-block is tiny and kernel-mutated rarely).
    pub fn system_roots_digest(&self) -> [u8; 32] {
        compute_system_roots_digest(&self.system_roots)
    }

    /// Set a field's visibility level. If transitioning to Committed or
    /// SelectivelyDisclosable, computes and stores the commitment hash.
    /// The `commitment_nonce` is mixed into the hash to prevent rainbow attacks.
    pub fn set_field_visibility(
        &mut self,
        index: usize,
        visibility: FieldVisibility,
        commitment_nonce: u64,
    ) -> bool {
        if index >= STATE_SLOTS {
            return false;
        }
        self.field_visibility[index] = visibility;
        match visibility {
            FieldVisibility::Public => {
                self.commitments[index] = None;
            }
            FieldVisibility::Committed | FieldVisibility::SelectivelyDisclosable => {
                self.commitments[index] = Some(Self::compute_commitment(
                    &self.fields[index],
                    commitment_nonce,
                ));
            }
        }
        true
    }

    /// Public re-export of the cell's field-commitment function — `BLAKE3(value
    /// || nonce)`, byte-identical to what [`set_field_visibility`](Self::set_field_visibility)
    /// stores in [`commitments`](Self::commitments). Exposed (additively) so the
    /// read-cap layer ([`crate::read_cap`]) can compute the SAME commitment for an
    /// encrypted slot — the binding the circuit sees is unchanged; only the
    /// ciphertext is new. Does NOT alter the commitment shape.
    #[inline]
    pub fn compute_commitment_pub(value: &FieldElement, nonce: u64) -> [u8; 32] {
        Self::compute_commitment(value, nonce)
    }

    /// Compute a BLAKE3 commitment: H(value || nonce_bytes).
    fn compute_commitment(value: &FieldElement, nonce: u64) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new();
        hasher.update(value);
        hasher.update(&nonce.to_le_bytes());
        *hasher.finalize().as_bytes()
    }

    /// Get the public view of a field: returns the value if Public, or the
    /// commitment hash if Committed/SelectivelyDisclosable.
    ///
    /// Audit P1-2: previously, if the visibility was `Committed` or
    /// `SelectivelyDisclosable` but the stored `commitments[index]` was `None`
    /// (because `set_field` invalidated the stale hash), this function fell
    /// through to `PublicFieldView::Revealed(self.fields[index])` and silently
    /// leaked the supposedly-private value. We now return a sentinel
    /// `PublicFieldView::Committed([0u8; 32])` instead — callers MUST treat
    /// the zero-hash as "commitment is stale; ask the holder to re-commit
    /// with `set_field_visibility`," not as a free plaintext disclosure.
    pub fn get_field_public(&self, index: usize) -> Option<PublicFieldView> {
        if index >= STATE_SLOTS {
            return None;
        }
        match self.field_visibility[index] {
            FieldVisibility::Public => Some(PublicFieldView::Revealed(self.fields[index])),
            FieldVisibility::Committed | FieldVisibility::SelectivelyDisclosable => {
                match self.commitments[index] {
                    Some(hash) => Some(PublicFieldView::Committed(hash)),
                    // Stale commitment after `set_field`: refuse to reveal the
                    // plaintext. Return the all-zero sentinel so the public
                    // view is non-informative until the holder re-commits.
                    None => Some(PublicFieldView::Committed([0u8; 32])),
                }
            }
        }
    }

    /// Get a state field by index.
    pub fn get_field(&self, index: usize) -> Option<&FieldElement> {
        self.fields.get(index)
    }

    /// Set a state field by index.
    ///
    /// Invalidates any stale commitment for this field. Callers that need the
    /// commitment to remain valid must call `set_field_visibility` with a fresh
    /// nonce after updating the value.
    pub fn set_field(&mut self, index: usize, value: FieldElement) -> bool {
        if index < STATE_SLOTS {
            self.fields[index] = value;
            // Invalidate stale commitment — old hash no longer matches new value.
            if self.commitments[index].is_some() {
                self.commitments[index] = None;
            }
            true
        } else {
            false
        }
    }

    // ───────────────────────────────────────────────────────────────────────
    // `_RECORD-LAYER-UPGRADE.md` §B.3 — the committed user-field MAP (Stage 0).
    //
    // The hybrid read/write: keys `< STATE_SLOTS` (16) hit the existing fixed
    // `fields[]` array (byte-identical to before); keys `>= STATE_SLOTS` hit the
    // committed map. These are NEW methods — every existing `get_field`/
    // `set_field` call (which takes a `usize` slot index) is untouched.
    // ───────────────────────────────────────────────────────────────────────

    /// Read a field by its **unbounded key**. Keys `< STATE_SLOTS` read the
    /// fixed cell `fields[key]`; keys `>= STATE_SLOTS` read the committed map
    /// (returning `None` if the key is absent — the negative membership case).
    ///
    /// The Rust shadow of the Lean `FieldsMap.tailLookup` / `Value.scalar`
    /// uniform name-keyed read.
    pub fn get_field_ext(&self, key: u64) -> Option<FieldElement> {
        if (key as usize) < STATE_SLOTS {
            Some(self.fields[key as usize])
        } else {
            self.fields_map.get(&key).copied()
        }
    }

    /// Write a field by its **unbounded key**. Keys `< STATE_SLOTS` write the
    /// fixed cell (delegating to [`set_field`](Self::set_field), so stale-
    /// commitment invalidation is preserved); keys `>= STATE_SLOTS` insert into
    /// the committed map and recompute [`fields_root`](Self::fields_root).
    /// Returns `true` on success.
    pub fn set_field_ext(&mut self, key: u64, value: FieldElement) -> bool {
        if (key as usize) < STATE_SLOTS {
            self.set_field(key as usize, value)
        } else {
            self.fields_map.insert(key, value);
            self.fields_root = compute_fields_root(&self.fields_map);
            true
        }
    }

    /// Recompute and store `fields_root` from the current `fields_map`. Idempotent;
    /// callers that mutate `fields_map` out-of-band must call this to re-seal the
    /// root (the normal [`set_field_ext`](Self::set_field_ext) path does it
    /// automatically).
    pub fn reseal_fields_root(&mut self) {
        self.fields_root = compute_fields_root(&self.fields_map);
    }

    /// **Membership witness** for a committed user-map key: returns the value
    /// `Some(v)` iff `key` is present in the map AND the recomputed root over
    /// the current map equals the stored `fields_root` (i.e. the value `v` is
    /// genuinely committed by `fields_root`). This is the end-to-end read-back
    /// the subscription app uses: a read proves the value is committed.
    ///
    /// The Rust shadow of the Lean `FieldsMap.fieldsRoot_membership` read law.
    pub fn fields_root_membership(&self, key: u64) -> Option<FieldElement> {
        let v = self.fields_map.get(&key).copied()?;
        if compute_fields_root(&self.fields_map) == self.fields_root {
            Some(v)
        } else {
            None
        }
    }

    // ───────────────────────────────────────────────────────────────────────
    // `docs/UNIVERSAL-MAP-ROTATION.md` §2.4 — the committed HEAP (sorted-
    // Poseidon2 `(collection, key) → value` map). The heap root is a canonical
    // commitment limb; `heap_map` is the prover-side witness store.
    // ───────────────────────────────────────────────────────────────────────

    /// Read a heap entry by its `(collection_id, key)`.
    pub fn get_heap(&self, coll: u32, key: u32) -> Option<FieldElement> {
        self.heap_map.get(&(coll, key)).copied()
    }

    /// Write a heap entry by its `(collection_id, key)` and recompute
    /// [`heap_root`](Self::heap_root).
    pub fn set_heap(&mut self, coll: u32, key: u32, value: FieldElement) -> bool {
        self.heap_map.insert((coll, key), value);
        self.heap_root = compute_heap_root(&self.heap_map);
        true
    }

    /// Remove a heap entry by its `(collection_id, key)` and recompute
    /// [`heap_root`](Self::heap_root). Returns `true` if the key was present.
    pub fn remove_heap(&mut self, coll: u32, key: u32) -> bool {
        let removed = self.heap_map.remove(&(coll, key)).is_some();
        if removed {
            self.heap_root = compute_heap_root(&self.heap_map);
        }
        removed
    }

    /// Recompute and store `heap_root` from the current `heap_map`. Idempotent;
    /// callers that mutate `heap_map` out-of-band must call this to re-seal the
    /// root.
    pub fn reseal_heap_root(&mut self) {
        self.heap_root = compute_heap_root(&self.heap_map);
    }

    /// **Membership witness** for a committed heap key: returns the value
    /// `Some(v)` iff `(coll, key)` is present AND the recomputed root over the
    /// current map equals the stored `heap_root`.
    pub fn heap_root_membership(&self, coll: u32, key: u32) -> Option<FieldElement> {
        let v = self.heap_map.get(&(coll, key)).copied()?;
        if compute_heap_root(&self.heap_map) == self.heap_root {
            Some(v)
        } else {
            None
        }
    }

    /// Increment the nonce by 1, returning `true` on success and `false` on
    /// overflow.
    ///
    /// Audit P2-2: previously used `wrapping_add`, which would silently wrap
    /// after 2^64 increments and re-enable replay of historical actions.
    /// Callers must check the return value and refuse to proceed on `false`.
    #[must_use = "nonce overflow must be handled; ignoring the return value re-introduces P2-2"]
    pub fn increment_nonce(&mut self) -> bool {
        match self.nonce.checked_add(1) {
            Some(n) => {
                self.nonce = n;
                true
            }
            None => false,
        }
    }

    /// Apply an ORDINARY balance change (positive or negative). Refuses to
    /// take the balance below ZERO (ordinary-cell sign discipline) and
    /// returns `false` on underflow/overflow. Issuer-well moves use
    /// [`apply_balance_change_well`](Self::apply_balance_change_well).
    pub fn apply_balance_change(&mut self, delta: i64) -> bool {
        match self.balance.checked_add(delta) {
            // A credit (delta ≥ 0) may land anywhere (a negative well
            // credited toward zero stays valid); an ordinary debit must not
            // land below zero.
            Some(new_bal) if delta >= 0 || new_bal >= 0 => {
                self.balance = new_bal;
                true
            }
            _ => false,
        }
    }

    /// Apply an ISSUER-WELL balance change (positive or negative). The well
    /// may go negative (−supply); only `i64` overflow fails. The executor
    /// gates who may invoke well verbs.
    pub fn apply_balance_change_well(&mut self, delta: i64) -> bool {
        match self.balance.checked_add(delta) {
            Some(new_bal) => {
                self.balance = new_bal;
                true
            }
            None => false,
        }
    }

    /// Bump the delegation epoch (signals children to refresh).
    ///
    /// Audit P2-2: previously used `wrapping_add`. Returns `false` on overflow;
    /// in practice 2^64 epoch bumps is unreachable but a wrap would let stale
    /// delegations regain freshness.
    #[must_use = "delegation epoch overflow must be handled"]
    pub fn bump_delegation_epoch(&mut self) -> bool {
        match self.delegation_epoch.checked_add(1) {
            Some(e) => {
                self.delegation_epoch = e;
                true
            }
            None => false,
        }
    }
}

impl Default for CellState {
    fn default() -> Self {
        Self::new(0)
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// THE EPOCH signed-balance boundary encoding (`docs/EPOCH-DESIGN.md` §5 +
// the range-table limb discipline).
//
// A signed balance crosses a proof/commitment boundary as the ORDER-PRESERVING
// biased u64: `biased = (balance as u64) ⊕ 2^63` (two's complement with the
// sign bit flipped), so `a < b  ⇔  biased(a) < biased(b)` as unsigned — the
// comparison the range table wants. The biased value decomposes into TWO
// 32-bit limbs `(lo, hi)`; in-circuit each limb is further range-checked by
// lookup (BabyBear holds < 2^31, so the circuit lane splits limbs again as it
// pleases — these two limbs are the canonical WIRE shape it must reproduce).
// ─────────────────────────────────────────────────────────────────────────────

/// The order-preserving biased encoding of a signed balance:
/// `i64::MIN → 0`, `0 → 2^63`, `i64::MAX → 2^64−1`.
#[inline]
pub fn balance_biased(balance: i64) -> u64 {
    (balance as u64) ^ (1u64 << 63)
}

/// Invert [`balance_biased`].
#[inline]
pub fn balance_from_biased(biased: u64) -> i64 {
    (biased ^ (1u64 << 63)) as i64
}

/// The canonical two-limb decomposition `(lo, hi)` of the biased balance —
/// the range-table shape (each limb < 2^32).
#[inline]
pub fn balance_limbs(balance: i64) -> (u32, u32) {
    let b = balance_biased(balance);
    ((b & 0xFFFF_FFFF) as u32, (b >> 32) as u32)
}

/// Encode a signed balance for a commitment/wire boundary: the biased u64,
/// little-endian (= limbs `lo‖hi`, each LE). THE canonical byte shape every
/// commitment site uses (`compute_canonical_state_commitment` v6).
#[inline]
pub fn encode_balance_le(balance: i64) -> [u8; 8] {
    balance_biased(balance).to_le_bytes()
}

/// Invert [`encode_balance_le`].
#[inline]
pub fn decode_balance_le(bytes: [u8; 8]) -> i64 {
    balance_from_biased(u64::from_le_bytes(bytes))
}

#[cfg(test)]
mod signed_balance_tests {
    //! THE EPOCH §5: the signed value model + the biased two-limb boundary
    //! encoding. Positive AND negative witnesses for every discipline.

    use super::*;

    /// The biased encoding is order-preserving and round-trips.
    #[test]
    fn biased_encoding_order_preserving_roundtrip() {
        let samples = [i64::MIN, -1_085_000, -1, 0, 1, 50_000, i64::MAX];
        for w in samples.windows(2) {
            assert!(
                balance_biased(w[0]) < balance_biased(w[1]),
                "bias must preserve order: {} vs {}",
                w[0],
                w[1]
            );
        }
        for &s in &samples {
            assert_eq!(decode_balance_le(encode_balance_le(s)), s);
            assert_eq!(balance_from_biased(balance_biased(s)), s);
            let (lo, hi) = balance_limbs(s);
            assert_eq!(((hi as u64) << 32) | lo as u64, balance_biased(s));
        }
        // The fixed pins the circuit lane reproduces:
        assert_eq!(balance_biased(0), 1u64 << 63);
        assert_eq!(balance_biased(i64::MIN), 0);
        assert_eq!(balance_biased(i64::MAX), u64::MAX);
    }

    /// Ordinary discipline: debit refuses to cross zero; well debit goes
    /// negative (−supply).
    #[test]
    fn sign_discipline_by_verb() {
        let mut ordinary = CellState::new(10);
        assert!(ordinary.debit_balance(10), "exact spend-to-zero is fine");
        assert!(
            !ordinary.debit_balance(1),
            "ordinary cells may not go negative"
        );
        assert_eq!(ordinary.balance(), 0);

        let mut well = CellState::new(0);
        assert!(
            well.well_debit_balance(1_085_000),
            "the well carries −supply"
        );
        assert_eq!(well.balance(), -1_085_000);
        // burn returns supply: an ordinary CREDIT moves the well toward zero.
        assert!(well.credit_balance(85_000));
        assert_eq!(well.balance(), -1_000_000);
    }

    /// `apply_balance_change` keeps the ordinary floor; the well variant
    /// doesn't.
    #[test]
    fn apply_change_disciplines() {
        let mut s = CellState::new(5);
        assert!(!s.apply_balance_change(-6), "ordinary refuses below zero");
        assert!(s.apply_balance_change(-5));
        assert_eq!(s.balance(), 0);
        assert!(
            s.apply_balance_change_well(-7),
            "well variant may go negative"
        );
        assert_eq!(s.balance(), -7);
        // credit on a negative balance is an ORDINARY change (delta ≥ 0).
        assert!(s.apply_balance_change(3));
        assert_eq!(s.balance(), -4);
    }

    /// Overflow teeth: amounts beyond i64 refuse on every verb.
    #[test]
    fn overflow_refusals() {
        let mut s = CellState::new(0);
        assert!(!s.credit_balance(u64::MAX));
        assert!(!s.debit_balance(u64::MAX));
        assert!(!s.well_debit_balance(u64::MAX));
        s.set_balance(i64::MAX);
        assert!(!s.credit_balance(1));
        s.set_balance(i64::MIN);
        assert!(!s.well_debit_balance(1));
    }
}

#[cfg(test)]
mod fields_map_tests {
    //! `_RECORD-LAYER-UPGRADE.md` Stage 0: the committed user-field MAP. The
    //! Rust shadow of `Dregg2/Exec/FieldsMap.lean`'s pos/neg vacuity guard.

    use super::*;

    fn fe(byte: u8) -> FieldElement {
        let mut f = [0u8; 32];
        f[31] = byte;
        f
    }

    /// A fresh cell has the FIXED empty-map root (legacy backward-compat
    /// constant) and an empty map.
    #[test]
    fn fresh_cell_has_empty_fields_root() {
        let s = CellState::new(0);
        assert!(s.fields_map.is_empty());
        assert_eq!(
            s.fields_root,
            empty_fields_root(),
            "a no-overflow cell carries the fixed empty-map constant"
        );
    }

    /// POSITIVE membership: a written key `>= STATE_SLOTS` reads back exactly its value,
    /// and the membership witness confirms it is committed by `fields_root`.
    #[test]
    fn map_field_write_then_membership_readback() {
        let mut s = CellState::new(0);
        assert!(s.set_field_ext(16, fe(42)));
        assert!(s.set_field_ext(17, fe(7)));
        assert_eq!(s.get_field_ext(16), Some(fe(42)));
        assert_eq!(s.get_field_ext(17), Some(fe(7)));
        // The committed read-back: value is genuinely committed by fields_root.
        assert_eq!(s.fields_root_membership(16), Some(fe(42)));
        assert_eq!(s.fields_root_membership(17), Some(fe(7)));
    }

    /// NEGATIVE membership: an absent key reads `None` (the tail does not commit
    /// it) — the anti-vacuity negative witness.
    #[test]
    fn absent_map_field_reads_none() {
        let mut s = CellState::new(0);
        s.set_field_ext(16, fe(42));
        assert_eq!(s.get_field_ext(18), None);
        assert_eq!(s.fields_root_membership(18), None);
    }

    /// Keys `< STATE_SLOTS` fall through to the fixed array (existing access unchanged):
    /// `set_field_ext`/`get_field_ext` on a low key mirror `set_field`/`get_field`.
    #[test]
    fn low_keys_hit_the_fixed_array() {
        let mut s = CellState::new(0);
        assert!(s.set_field_ext(3, fe(99)));
        assert_eq!(s.fields[3], fe(99));
        assert_eq!(s.get_field_ext(3), Some(fe(99)));
        // The map and its root are untouched by a low-key write.
        assert!(s.fields_map.is_empty());
        assert_eq!(s.fields_root, empty_fields_root());
    }

    /// ANTI-VACUITY: a map with data has a root DIFFERENT from the empty
    /// constant, and a tampered value FLIPS the root (the digest genuinely
    /// commits the map — a `:= 0` stub is forbidden).
    #[test]
    fn fields_root_is_not_vacuous() {
        let mut s = CellState::new(0);
        s.set_field_ext(16, fe(42));
        assert_ne!(
            s.fields_root,
            empty_fields_root(),
            "a populated map must not collapse to the empty constant"
        );
        let root_before = s.fields_root;
        // Tamper the value at the same key.
        s.set_field_ext(16, fe(43));
        assert_ne!(
            root_before, s.fields_root,
            "tampering a value must flip the root"
        );
        // Distinct maps cannot share a root: a drop also flips it.
        s.set_field_ext(17, fe(1));
        let two_entries = s.fields_root;
        s.fields_map.remove(&17);
        s.reseal_fields_root();
        assert_ne!(
            two_entries, s.fields_root,
            "dropping an entry must flip the root"
        );
    }

    /// `fields_root` is deterministic and order-canonical (BTreeMap key order):
    /// inserting the same entries in a different order yields the same root.
    #[test]
    fn fields_root_is_order_canonical() {
        let mut a = CellState::new(0);
        a.set_field_ext(16, fe(1));
        a.set_field_ext(17, fe(2));
        let mut b = CellState::new(0);
        b.set_field_ext(17, fe(2));
        b.set_field_ext(16, fe(1));
        assert_eq!(a.fields_root, b.fields_root);
    }

    /// An existing serialized cell (no `fields_root`/`fields_map`) deserializes
    /// unchanged: the `#[serde(default)]` fields populate to the empty map.
    #[test]
    fn legacy_serialized_cell_deserializes() {
        // A JSON blob with the pre-Stage-0 field set only (no fields_root /
        // fields_map). Deserialization must succeed and default the new fields.
        // Built by serializing a fresh cell, then stripping the new keys — so
        // the blob is exactly a pre-upgrade serialized cell.
        let fresh = CellState::new(100);
        let mut blob = serde_json::to_value(&fresh).expect("serialize");
        let obj = blob.as_object_mut().unwrap();
        obj.remove("fields_root");
        obj.remove("fields_map");
        obj.insert("nonce".into(), serde_json::json!(5));
        let s: CellState = serde_json::from_value(blob).expect("legacy cell deserializes");
        assert_eq!(s.nonce(), 5);
        assert_eq!(s.balance(), 100);
        assert!(s.fields_map.is_empty());
        assert_eq!(s.fields_root, empty_fields_root());
    }
}

#[cfg(test)]
mod heap_root_tests {
    //! `docs/UNIVERSAL-MAP-ROTATION.md` §2.4: the committed `heap_root` register.

    use super::*;

    fn fe(byte: u8) -> FieldElement {
        let mut f = [0u8; 32];
        f[31] = byte;
        f
    }

    /// A fresh cell has the FIXED empty-heap root (legacy backward-compat
    /// constant) and an empty heap map.
    #[test]
    fn fresh_cell_has_empty_heap_root() {
        let s = CellState::new(0);
        assert!(s.heap_map.is_empty());
        assert_eq!(
            s.heap_root,
            empty_heap_root(),
            "a no-heap-activity cell carries the fixed empty-heap constant"
        );
    }

    /// POSITIVE membership: a written `(coll, key)` reads back exactly its value,
    /// and the membership witness confirms it is committed by `heap_root`.
    #[test]
    fn heap_write_then_membership_readback() {
        let mut s = CellState::new(0);
        assert!(s.set_heap(1, 2, fe(42)));
        assert!(s.set_heap(1, 3, fe(7)));
        assert_eq!(s.get_heap(1, 2), Some(fe(42)));
        assert_eq!(s.get_heap(1, 3), Some(fe(7)));
        assert_eq!(s.heap_root_membership(1, 2), Some(fe(42)));
        assert_eq!(s.heap_root_membership(1, 3), Some(fe(7)));
    }

    /// NEGATIVE membership: an absent key reads `None`.
    #[test]
    fn absent_heap_entry_reads_none() {
        let mut s = CellState::new(0);
        s.set_heap(1, 2, fe(42));
        assert_eq!(s.get_heap(1, 10), None);
        assert_eq!(s.heap_root_membership(1, 10), None);
    }

    /// ANTI-VACUITY: a heap with data has a root DIFFERENT from the empty
    /// constant, and a tampered value FLIPS the root.
    #[test]
    fn heap_root_is_not_vacuous() {
        let mut s = CellState::new(0);
        s.set_heap(1, 2, fe(42));
        assert_ne!(
            s.heap_root,
            empty_heap_root(),
            "a populated heap must not collapse to the empty constant"
        );
        let root_before = s.heap_root;
        s.set_heap(1, 2, fe(43));
        assert_ne!(
            root_before, s.heap_root,
            "tampering a heap value must flip the root"
        );
        let two_entries = s.heap_root;
        s.remove_heap(1, 2);
        assert_ne!(
            two_entries, s.heap_root,
            "dropping an entry must flip the root"
        );
        assert_eq!(s.heap_root, empty_heap_root());
    }

    /// The root is deterministic and order-canonical (`BTreeMap` order): the
    /// same entries in any insertion order yield the same root.
    #[test]
    fn heap_root_is_order_canonical() {
        let mut a = CellState::new(0);
        a.set_heap(1, 2, fe(1));
        a.set_heap(1, 3, fe(2));
        let mut b = CellState::new(0);
        b.set_heap(1, 3, fe(2));
        b.set_heap(1, 2, fe(1));
        assert_eq!(a.heap_root, b.heap_root);
    }

    /// Collection ids bind the root: the same value at the same key under
    /// different collections yields different roots.
    #[test]
    fn collection_id_binds_heap_root() {
        let mut a = CellState::new(0);
        a.set_heap(1, 2, fe(1));
        let mut b = CellState::new(0);
        b.set_heap(2, 2, fe(1));
        assert_ne!(a.heap_root, b.heap_root);
    }

    /// A legacy serialized cell (no `heap_root`/`heap_map`) deserializes with
    /// the empty-heap defaults.
    #[test]
    fn legacy_serialized_cell_deserializes_heap_defaults() {
        let fresh = CellState::new(100);
        let mut blob = serde_json::to_value(&fresh).expect("serialize");
        let obj = blob.as_object_mut().unwrap();
        obj.remove("heap_root");
        obj.remove("heap_map");
        let s: CellState = serde_json::from_value(blob).expect("legacy cell deserializes");
        assert!(s.heap_map.is_empty());
        assert_eq!(s.heap_root, empty_heap_root());
    }
}
