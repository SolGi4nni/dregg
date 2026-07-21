use serde::{Deserialize, Serialize};

use crate::capability::CapabilitySet;
use crate::delegation::DelegatedRef;
use crate::id::CellId;
use crate::lifecycle::{CellLifecycle, LifecycleTransitionError};
use crate::permissions::Permissions;
use crate::program::CellProgram;
use crate::state::CellState;

/// Whether a cell's full state is stored by the federation or only a commitment.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum CellMode {
    /// Federation stores full cell state (current behavior).
    Hosted,
    /// Federation stores only a 32-byte state commitment.
    /// The agent must provide cell state in each turn.
    Sovereign,
}

impl Default for CellMode {
    fn default() -> Self {
        CellMode::Sovereign
    }
}

/// A verification key associated with a cell's proof circuit.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct VerificationKey {
    /// Hash of the verification key for cheap comparison.
    pub hash: [u8; 32],
    /// Serialized verification key data (opaque blob).
    pub data: Vec<u8>,
}

impl VerificationKey {
    /// Create a new verification key from raw data, computing its BLAKE3 hash.
    ///
    /// **Deprecated.** This constructor uses a plain `blake3(data)` hash, which
    /// is *not* a `canonical_vk_v2` hash (domain key `"dregg-vk-v2"`). Any VK
    /// built here is internally consistent but not interoperable with a validator
    /// that re-derives the expected VK hash via `canonical_vk_v2` from the four
    /// canonical components. Use [`VerificationKey::from_components`] for all
    /// production VK construction where the circuit/AIR/verifier/proving-system
    /// identity components are available. Opaque-fixture uses (tests, demos) may
    /// continue to call `new` — the deprecation warning is expected and acceptable
    /// for those sites. Do **not** suppress the warning with `#[allow(deprecated)]`
    /// unless the call site is genuinely opaque-fixture only.
    ///
    /// See `docs-old/VK-NEW-CALLER-AUDIT.md` §2 Option A for the full rationale.
    #[deprecated(note = "use from_components for canonical vk_v2 hashing; see VK-NEW-CALLER-AUDIT")]
    pub fn new(data: Vec<u8>) -> Self {
        let hash = *blake3::hash(&data).as_bytes();
        VerificationKey { hash, data }
    }

    /// Create a verification key from the four canonical VK v2 components,
    /// computing the hash via [`crate::vk_v2::canonical_vk_v2`].
    ///
    /// This is the correct constructor for any production code path that has the
    /// cell-program / AIR / verifier / proving-system identity components in hand:
    ///
    /// - `components.program_bytes` — canonical postcard(CellProgram), DSL AST,
    ///   or opaque app-provided bytes encoding the executable spec.
    /// - `components.air_fingerprint` — 32-byte hash of the AIR descriptor.
    /// - `components.verifier_fingerprint` — which verifier implementation runs
    ///   the circuit (source-hash / wasm-hash / compiled-VK-hash variant).
    /// - `components.proving_system_id` — Plonky3BabyBearFri, KimchiPasta,
    ///   Sp1V6, or Custom.
    ///
    /// The resulting `hash` field is a `blake3_keyed("dregg-vk-v2", …)` digest —
    /// the same value that a validator re-derives independently. The `data` field
    /// stores `program_bytes` so the program spec is recoverable for
    /// cross-checking (AIR/verifier/proving-system identity is conveyed
    /// out-of-band via `VkComponents`; see `vk_v2.rs` for the full boundary
    /// contract).
    ///
    /// # Example
    ///
    /// ```
    /// use dregg_cell::VerificationKey;
    /// use dregg_cell::vk_v2::{VkComponents, VerifierFingerprint, ProvingSystemId};
    ///
    /// let program_bytes = b"my-cell-program-postcard-bytes";
    /// let vk = VerificationKey::from_components(&VkComponents {
    ///     program_bytes,
    ///     air_fingerprint: [0x11; 32],
    ///     verifier_fingerprint: VerifierFingerprint::SourceHash([0x22; 32]),
    ///     proving_system_id: ProvingSystemId::Plonky3BabyBearFri {
    ///         p3_rev: "82cfad73",
    ///     },
    /// });
    /// // vk.hash is canonical_vk_v2(components), not blake3(program_bytes).
    /// ```
    pub fn from_components(components: &crate::vk_v2::VkComponents<'_>) -> Self {
        let hash = crate::vk_v2::canonical_vk_v2(components);
        // Store the program bytes so the executable spec is recoverable for
        // cross-checking. The AIR/verifier/proving-system fields are conveyed
        // out-of-band via VkComponents and are NOT embedded in `data`.
        let data = components.program_bytes.to_vec();
        VerificationKey { hash, data }
    }

    /// Create a verification key with a pre-computed hash (e.g., from
    /// deserialization).
    ///
    /// **Audit P0 #69:** this constructor does *not* validate the
    /// `hash == blake3(data)` invariant. It exists for the
    /// deserialization fast-path where the producer has already paid
    /// the hash and we want to avoid recomputing it. Untrusted-input
    /// call sites (the `SetVerificationKey` apply, wire decoders,
    /// federation gossip ingest) MUST use [`Self::from_parts_checked`]
    /// instead — otherwise an attacker can pin an arbitrary `hash` and
    /// defeat the layered-VK design (the cell commitment binds the
    /// `hash`, but downstream verifiers expect that `hash` to be the
    /// commitment of `data`).
    pub fn from_parts(hash: [u8; 32], data: Vec<u8>) -> Self {
        VerificationKey { hash, data }
    }

    /// Create a verification key with a pre-computed hash, validating
    /// the integrity invariant `hash == blake3(data)`.
    ///
    /// Returns `Err(VerificationKeyIntegrityError)` if the supplied hash
    /// does not match the BLAKE3 commitment of the supplied data. This
    /// is the correct constructor for any code path that consumes a
    /// `VerificationKey` from outside trust boundaries (a turn body, a
    /// federation broadcast, a deserialized snapshot) — see audit P0 #69.
    pub fn from_parts_checked(
        hash: [u8; 32],
        data: Vec<u8>,
    ) -> Result<Self, VerificationKeyIntegrityError> {
        let expected = *blake3::hash(&data).as_bytes();
        if expected != hash {
            return Err(VerificationKeyIntegrityError {
                expected,
                got: hash,
            });
        }
        Ok(VerificationKey { hash, data })
    }
}

/// Returned when a [`VerificationKey`]'s declared `hash` does not match
/// `blake3(data)`. See [`VerificationKey::from_parts_checked`] and audit
/// P0 #69.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerificationKeyIntegrityError {
    /// Hash the validator computed from the supplied `data`.
    pub expected: [u8; 32],
    /// Hash the caller declared.
    pub got: [u8; 32],
}

impl std::fmt::Display for VerificationKeyIntegrityError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "VerificationKey hash mismatch: declared {:02x}{:02x}{:02x}{:02x}.. \
             but blake3(data) is {:02x}{:02x}{:02x}{:02x}..",
            self.got[0],
            self.got[1],
            self.got[2],
            self.got[3],
            self.expected[0],
            self.expected[1],
            self.expected[2],
            self.expected[3],
        )
    }
}

impl std::error::Error for VerificationKeyIntegrityError {}

/// The cached canonical Merkle-leaf digest of a `Cell`
/// (`.docs-history-noclaude/INCREMENTAL-COMMITMENT.md` step 3 — the cell-leaf cache).
///
/// ## Why this exists
///
/// The federation Merkle leaf for a cell is
/// [`crate::commitment::compute_canonical_state_commitment`] — a BLAKE3
/// absorption of the cell's FULL canonical byte serialization (identity +
/// balance + perms + cap-root + program + lifecycle + fields/heap/side-table
/// roots). With the sub-roots already cached (cap-root `e0c6bd6f9`,
/// fields/heap/system roots resealed on write), the residual cost is the
/// ~1.5µs BLAKE3 absorb itself, paid on EVERY touched cell at `Ledger::root()`
/// time. This cache stores the finished 32-byte leaf so a turn that touched a
/// cell once (e.g. one nonce/balance write) re-absorbs nothing on the SECOND
/// and later `root()` calls until the cell is next mutated.
///
/// ## The byte-identity contract (why this is safe)
///
/// The cache is read ONLY by `Ledger::hash_cell` (the Merkle-leaf path).
/// `Cell::state_commitment()` — used off the ledger by sovereign-witness and
/// migration paths — ALWAYS recomputes fresh and never consults the cache, so a
/// standalone mutated-via-`pub`-field cell can never serve a stale digest.
/// Inside the ledger, EVERY path that hands out a `&mut Cell` (or mutates a
/// cell's fields directly) invalidates this cache via
/// [`Cell::invalidate_leaf_cache`] BEFORE the mutation is observable — exactly
/// the conservative `&mut`-boundary discipline the cap-root cache uses for
/// `iter_mut`. A cache hit is therefore byte-identical to a fresh
/// `compute_canonical_state_commitment` (pinned by the differential
/// `leaf_digest_cache_matches_fresh`).
///
/// Interior mutability (`Mutex`) gives `Sync` so the lazy fill can run behind
/// the shared `&Cell` the commitment path holds and a `Cell` stays `Send +
/// Sync`. NOT serialized (`#[serde(skip)]` ⇒ reconstructs dirty on decode),
/// NOT part of `PartialEq`/`Eq` (two equal cells with different cache states are
/// equal), and a `Clone` copies the current cached digest (the cell bytes are
/// identical, so the leaf is valid for the clone too).
#[derive(Debug, Default)]
pub struct LeafDigestCache(std::sync::Mutex<Option<[u8; 32]>>);

impl LeafDigestCache {
    #[inline]
    fn load(&self) -> Option<[u8; 32]> {
        *self.0.lock().expect("leaf-digest cache mutex poisoned")
    }

    #[inline]
    fn store(&self, digest: Option<[u8; 32]>) {
        *self.0.lock().expect("leaf-digest cache mutex poisoned") = digest;
    }
}

impl Clone for LeafDigestCache {
    fn clone(&self) -> Self {
        LeafDigestCache(std::sync::Mutex::new(self.load()))
    }
}

impl PartialEq for LeafDigestCache {
    fn eq(&self, _other: &Self) -> bool {
        // The cache is a derived value, not part of the cell's identity.
        true
    }
}
impl Eq for LeafDigestCache {}

/// Exact serialized public-key length for ML-DSA-65 (FIPS 204).
///
/// The cell crate deliberately stores only a commitment to this public key;
/// signed turns carry the 1,952 public bytes needed for verification.  Keeping
/// the fixed length here lets the committed identity object reject a malformed
/// key before it can become authority without pulling a signing implementation
/// into the state-model crate.
pub const ML_DSA_65_PUBLIC_KEY_LEN: usize = 1_952;

/// The post-quantum authorization anchor committed by a cell.
///
/// The raw ML-DSA key stays on the signed wire.  A validator hashes those bytes
/// with [`ml_dsa_public_key_commitment`] and compares the result with this
/// independently persisted value before verifying the signature.  `key_epoch`
/// is a dedicated identity counter; it is intentionally distinct from
/// `CellState::delegation_epoch`, which revokes capability snapshots.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CellPqIdentity {
    pub key_epoch: u64,
    pub ml_dsa_key_commitment: [u8; 32],
}

/// Failure to install or rotate a cell's committed PQ identity.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CellPqIdentityError {
    InvalidPublicKeyLength { got: usize },
    AlreadyInstalled,
    NotInstalled,
    EpochMismatch { expected: u64, actual: u64 },
    EpochOverflow,
    UnchangedKey,
}

impl core::fmt::Display for CellPqIdentityError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::InvalidPublicKeyLength { got } => write!(
                f,
                "ML-DSA-65 public key must be {ML_DSA_65_PUBLIC_KEY_LEN} bytes, got {got}"
            ),
            Self::AlreadyInstalled => f.write_str("cell PQ identity is already installed"),
            Self::NotInstalled => f.write_str("cell PQ identity is not installed"),
            Self::EpochMismatch { expected, actual } => write!(
                f,
                "cell PQ identity epoch mismatch: expected {expected}, live {actual}"
            ),
            Self::EpochOverflow => f.write_str("cell PQ identity epoch overflow"),
            Self::UnchangedKey => f.write_str("cell PQ identity rotation must install a new key"),
        }
    }
}

impl std::error::Error for CellPqIdentityError {}

/// Domain-separated commitment to one exact-length ML-DSA-65 public key.
pub fn ml_dsa_public_key_commitment(public_key: &[u8]) -> Result<[u8; 32], CellPqIdentityError> {
    if public_key.len() != ML_DSA_65_PUBLIC_KEY_LEN {
        return Err(CellPqIdentityError::InvalidPublicKeyLength {
            got: public_key.len(),
        });
    }
    let mut hasher = blake3::Hasher::new_derive_key("dregg-cell-ml-dsa-key-v1");
    hasher.update(&(public_key.len() as u32).to_le_bytes());
    hasher.update(public_key);
    Ok(*hasher.finalize().as_bytes())
}

/// A Cell is an isolated agent execution context.
/// This is the agent-model analog of a Mina zkApp account.
///
/// Audit P0-1 sealing: the identity-bearing fields `id`, `public_key`, and
/// `token_id` are `pub(crate)` rather than `pub` — external code must use the
/// accessors [`Cell::id`], [`Cell::public_key`], [`Cell::token_id`] for reads
/// and go through `Ledger::update_with` for mutations. This preserves the
/// content-address invariant `id == derive_raw(public_key, token_id)` (P2-3).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Cell {
    /// Content-addressed identity: BLAKE3(public_key || token_id).
    ///
    /// `pub(crate)`: external code must read via `Cell::id()` and cannot mutate
    /// without going through `Ledger::update_with` (which re-checks integrity).
    pub(crate) id: CellId,
    /// The cell's public key (Ed25519). See `id` for sealing rationale.
    pub(crate) public_key: [u8; 32],
    /// Mutable state: 16 fields + nonce + balance.
    pub state: CellState,
    /// Authorization requirements for each action type.
    pub permissions: Permissions,
    /// Optional verification key for ZK proof validation.
    pub verification_key: Option<VerificationKey>,
    /// Optional parent/supervisor cell. Planned for delegation chain walking
    /// (child inherits parent's capabilities). Not yet enforced by the executor.
    pub delegate: Option<CellId>,
    /// Rich delegation snapshot: point-in-time copy of the parent's c-list.
    /// Used for snapshot+refresh E-style delegation. The child acts using this
    /// snapshot; acceptors check freshness via `max_staleness`.
    pub delegation: Option<DelegatedRef>,
    /// Which token domain this cell belongs to. See `id` for sealing rationale.
    pub(crate) token_id: [u8; 32],
    /// The c-list: what other cells this cell can reference.
    pub capabilities: CapabilitySet,
    /// The cell's program: defines valid state transitions.
    /// If `CellProgram::None`, any authorized state change is valid (backward compat).
    pub program: CellProgram,
    /// Whether this cell is hosted (federation stores full state) or sovereign
    /// (federation stores only a 32-byte commitment). Defaults to Hosted for
    /// backward compatibility with existing serialized cells.
    #[serde(default)]
    pub mode: CellMode,
    /// Canonical lifecycle state of the cell. Per
    /// `PROTOCOL-CATEGORICAL-ANALYSIS.md §1`, this enumerates the
    /// structural states a cell can inhabit (Live, Sealed, Migrated,
    /// Destroyed, Archived). Defaults to [`CellLifecycle::Live`].
    ///
    /// `#[serde(default)]`: existing serialized cells deserialize to
    /// `Live`, preserving backward compatibility while making the
    /// lifecycle explicit going forward.
    #[serde(default)]
    pub lifecycle: CellLifecycle,
    /// Canonical post-quantum authorization anchor. Native required-PQ
    /// authorization refuses a cell with no anchor; `None` remains useful only
    /// for deliberately unaudited low-level fixtures and non-signing stubs.
    ///
    /// This is the final serialized field, keeping the v10 schema extension
    /// localized at the wire tail. Postcard is positional and does not accept a
    /// missing trailing struct field, so pre-v10 durable snapshots require the
    /// store-level schema migration rather than silently decoding as unbound.
    #[serde(default)]
    pub(crate) pq_identity: Option<CellPqIdentity>,
    /// Cached canonical Merkle-leaf digest (`.docs-history-noclaude/INCREMENTAL-COMMITMENT.md`
    /// step 3). Read ONLY by `Ledger::hash_cell`; invalidated at every ledger
    /// `&mut`-handoff seam. `#[serde(skip)]` ⇒ reconstructs dirty on decode;
    /// excluded from `PartialEq`/`Eq`/`Clone`-identity via the
    /// [`LeafDigestCache`] impls. See that type's docs for the byte-identity
    /// contract.
    #[serde(skip)]
    pub(crate) leaf_cache: LeafDigestCache,
}

/// Configuration for creating a new cell.
///
/// Allows choosing mode, initial balance, permissions, and program at creation time.
#[derive(Clone, Debug)]
pub struct CellConfig {
    /// Whether the cell is hosted or sovereign.
    pub mode: CellMode,
    /// Initial balance (SIGNED — THE EPOCH §5; negative only for issuer
    /// wells seeded by genesis issuer-moves).
    pub balance: i64,
    /// Permissions (defaults to Permissions::default() if None).
    pub permissions: Option<Permissions>,
    /// Cell program (defaults to CellProgram::None if None).
    pub program: Option<CellProgram>,
    /// Verification key (optional).
    pub verification_key: Option<VerificationKey>,
}

impl Default for CellConfig {
    fn default() -> Self {
        CellConfig {
            mode: CellMode::Sovereign,
            balance: 0,
            permissions: None,
            program: None,
            verification_key: None,
        }
    }
}

impl CellConfig {
    /// Create a config for a hosted cell.
    pub fn hosted() -> Self {
        CellConfig {
            mode: CellMode::Hosted,
            ..Default::default()
        }
    }

    /// Create a config for a sovereign cell.
    pub fn sovereign() -> Self {
        CellConfig {
            mode: CellMode::Sovereign,
            ..Default::default()
        }
    }

    /// Set the initial balance.
    pub fn with_balance(mut self, balance: i64) -> Self {
        self.balance = balance;
        self
    }

    /// Set the permissions.
    pub fn with_permissions(mut self, permissions: Permissions) -> Self {
        self.permissions = Some(permissions);
        self
    }

    /// Set the cell program.
    pub fn with_program(mut self, program: CellProgram) -> Self {
        self.program = Some(program);
        self
    }

    /// Set the verification key.
    pub fn with_verification_key(mut self, vk: VerificationKey) -> Self {
        self.verification_key = Some(vk);
        self
    }
}

impl Cell {
    /// Create a new cell with default permissions and the given public key and token domain.
    ///
    /// Defaults to `CellMode::Sovereign` (Phase 4). Use `Cell::new_hosted()` for
    /// explicit hosted creation.
    pub fn new(public_key: [u8; 32], token_id: [u8; 32]) -> Self {
        let id = CellId::derive_raw(&public_key, &token_id);
        Cell {
            id,
            public_key,
            pq_identity: None,
            state: CellState::default(),
            permissions: Permissions::default(),
            verification_key: None,
            delegate: None,
            delegation: None,
            token_id,
            capabilities: CapabilitySet::new(),
            program: CellProgram::None,
            mode: CellMode::Sovereign,
            lifecycle: CellLifecycle::Live,
            leaf_cache: LeafDigestCache::default(),
        }
    }

    /// Create a new hosted cell explicitly.
    ///
    /// This is the pre-Phase-4 behavior where the federation stores full cell state.
    pub fn new_hosted(public_key: [u8; 32], token_id: [u8; 32]) -> Self {
        let id = CellId::derive_raw(&public_key, &token_id);
        Cell {
            id,
            public_key,
            pq_identity: None,
            state: CellState::default(),
            permissions: Permissions::default(),
            verification_key: None,
            delegate: None,
            delegation: None,
            token_id,
            capabilities: CapabilitySet::new(),
            program: CellProgram::None,
            mode: CellMode::Hosted,
            lifecycle: CellLifecycle::Live,
            leaf_cache: LeafDigestCache::default(),
        }
    }

    /// Create a new cell with a specific initial balance.
    ///
    /// Remains hosted for backward compatibility with existing tests.
    pub fn with_balance(public_key: [u8; 32], token_id: [u8; 32], balance: i64) -> Self {
        let id = CellId::derive_raw(&public_key, &token_id);
        Cell {
            id,
            public_key,
            pq_identity: None,
            state: CellState::new(balance),
            permissions: Permissions::default(),
            verification_key: None,
            delegate: None,
            delegation: None,
            token_id,
            capabilities: CapabilitySet::new(),
            program: CellProgram::None,
            mode: CellMode::Hosted,
            lifecycle: CellLifecycle::Live,
            leaf_cache: LeafDigestCache::default(),
        }
    }

    /// Create a placeholder cell for a remote peer using their pre-derived
    /// cell id directly, without re-deriving from a (pk, token_id) pair.
    ///
    /// # When to use
    ///
    /// Inter-node operations (cross-federation grants, peer introductions,
    /// gossip of a remote cell's c-list entry) sometimes need a landing site
    /// for a remote cell whose canonical state lives on another node. The
    /// remote node has the real `(pk, token_id)`; the local node only sees
    /// the resulting content-addressed `CellId`. Calling `with_balance` would
    /// re-derive from a placeholder pk and produce a *different* id; calling
    /// this constructor preserves the id chosen by the remote node.
    ///
    /// # Soundness
    ///
    /// The returned cell breaks the invariant `id == derive_raw(public_key,
    /// token_id)` (the stub's public_key is zeros). This is acceptable because:
    ///
    /// 1. The stub cannot sign — its pk is zero — so no local authorization
    ///    path will accept a Signature(r, s) against it.
    /// 2. The stub's id is consistent with what the remote node would emit,
    ///    so cross-node gossip remains coherent.
    /// 3. The integrity invariant `verify_id_integrity()` will fail on this
    ///    stub, which is intentional: callers that need a canonical cell
    ///    must use `Ledger::update_with` and verify integrity there.
    ///
    /// In short: this is the escape hatch for "we know the id but not the
    /// pre-image." Use sparingly.
    pub fn remote_stub_with_id(id: CellId) -> Self {
        Self::remote_stub_with_id_and_balance(id, 0)
    }

    /// Like [`Cell::remote_stub_with_id`] but with an initial balance set on
    /// the placeholder. Use this when the local node knows the remote cell
    /// should have at least a certain balance for a turn to commit (for
    /// example, when a bearer-cap holder needs to issue a Transfer from a
    /// remote cell whose canonical balance lives on another node — without
    /// the local balance, the Transfer would hit InsufficientBalance even
    /// though it would succeed on the canonical node).
    pub fn remote_stub_with_id_and_balance(id: CellId, balance: i64) -> Self {
        Self::remote_stub_with_id_pk_balance(id, [0u8; 32], balance)
    }

    /// Like [`Cell::remote_stub_with_id_and_balance`] but also lets the
    /// caller specify the remote cell's public key. Required when the
    /// executor walks the local ledger to find the *delegator* of a bearer
    /// cap by pk: a zero-pk stub wouldn't match, so the bearer-cap proof
    /// would be rejected as if the delegator weren't present.
    pub fn remote_stub_with_id_pk_balance(id: CellId, public_key: [u8; 32], balance: i64) -> Self {
        Cell {
            id,
            public_key,
            pq_identity: None,
            state: CellState::new(balance),
            permissions: Permissions::default(),
            verification_key: None,
            delegate: None,
            delegation: None,
            token_id: [0u8; 32],
            capabilities: CapabilitySet::new(),
            program: CellProgram::None,
            mode: CellMode::Hosted,
            lifecycle: CellLifecycle::Live,
            leaf_cache: LeafDigestCache::default(),
        }
    }

    /// Create a new cell from a configuration.
    pub fn from_config(public_key: [u8; 32], token_id: [u8; 32], config: CellConfig) -> Self {
        let id = CellId::derive_raw(&public_key, &token_id);
        Cell {
            id,
            public_key,
            pq_identity: None,
            state: CellState::new(config.balance),
            permissions: config.permissions.unwrap_or_default(),
            verification_key: config.verification_key,
            delegate: None,
            delegation: None,
            token_id,
            capabilities: CapabilitySet::new(),
            program: config.program.unwrap_or(CellProgram::None),
            mode: config.mode,
            lifecycle: CellLifecycle::Live,
            leaf_cache: LeafDigestCache::default(),
        }
    }

    /// Read accessor for the content-addressed cell ID. Sealed for P0-1.
    ///
    /// External code cannot mutate this field directly — the following must
    /// not compile:
    /// ```compile_fail
    /// # use dregg_cell::Cell;
    /// let mut cell = Cell::new([0u8; 32], [0u8; 32]);
    /// cell.id = dregg_cell::CellId::derive_raw(&[1u8; 32], &[2u8; 32]);
    /// ```
    #[inline]
    pub fn id(&self) -> CellId {
        self.id
    }

    /// Read accessor for the cell's Ed25519 public key. Sealed for P0-1.
    ///
    /// External code cannot mutate this field directly:
    /// ```compile_fail
    /// # use dregg_cell::Cell;
    /// let mut cell = Cell::new([0u8; 32], [0u8; 32]);
    /// cell.public_key = [1u8; 32];
    /// ```
    #[inline]
    pub fn public_key(&self) -> &[u8; 32] {
        &self.public_key
    }

    /// Construct a hosted cell whose ML-DSA identity is committed at birth.
    pub fn with_hybrid_balance(
        public_key: [u8; 32],
        ml_dsa_public_key: &[u8],
        token_id: [u8; 32],
        balance: i64,
    ) -> Result<Self, CellPqIdentityError> {
        let mut cell = Self::with_balance(public_key, token_id, balance);
        cell.install_pq_identity(ml_dsa_public_key)?;
        Ok(cell)
    }

    /// Read the canonical PQ authorization anchor committed by this cell.
    #[inline]
    pub fn pq_identity(&self) -> Option<&CellPqIdentity> {
        self.pq_identity.as_ref()
    }

    /// Install the epoch-zero PQ identity on a newly-created cell.
    pub fn install_pq_identity(
        &mut self,
        ml_dsa_public_key: &[u8],
    ) -> Result<(), CellPqIdentityError> {
        if self.pq_identity.is_some() {
            return Err(CellPqIdentityError::AlreadyInstalled);
        }
        self.pq_identity = Some(CellPqIdentity {
            key_epoch: 0,
            ml_dsa_key_commitment: ml_dsa_public_key_commitment(ml_dsa_public_key)?,
        });
        self.invalidate_leaf_cache();
        Ok(())
    }

    /// Rotate to a new committed ML-DSA key and advance exactly one epoch.
    /// Authorization and new-key possession are checked by the turn executor
    /// before it calls this state transition.
    pub fn rotate_pq_identity(
        &mut self,
        expected_epoch: u64,
        new_ml_dsa_public_key: &[u8],
    ) -> Result<(), CellPqIdentityError> {
        let new_commitment = ml_dsa_public_key_commitment(new_ml_dsa_public_key)?;
        let current = self
            .pq_identity
            .as_ref()
            .ok_or(CellPqIdentityError::NotInstalled)?;
        if current.key_epoch != expected_epoch {
            return Err(CellPqIdentityError::EpochMismatch {
                expected: expected_epoch,
                actual: current.key_epoch,
            });
        }
        if current.ml_dsa_key_commitment == new_commitment {
            return Err(CellPqIdentityError::UnchangedKey);
        }
        let next_epoch = current
            .key_epoch
            .checked_add(1)
            .ok_or(CellPqIdentityError::EpochOverflow)?;
        self.pq_identity = Some(CellPqIdentity {
            key_epoch: next_epoch,
            ml_dsa_key_commitment: new_commitment,
        });
        self.invalidate_leaf_cache();
        Ok(())
    }

    /// Restore a previously journaled identity image during atomic rollback.
    #[doc(hidden)]
    pub fn restore_pq_identity(&mut self, old: Option<CellPqIdentity>) {
        self.pq_identity = old;
        self.invalidate_leaf_cache();
    }

    /// Read accessor for the cell's token-domain ID. Sealed for P0-1.
    ///
    /// External code cannot mutate this field directly:
    /// ```compile_fail
    /// # use dregg_cell::Cell;
    /// let mut cell = Cell::new([0u8; 32], [0u8; 32]);
    /// cell.token_id = [1u8; 32];
    /// ```
    #[inline]
    pub fn token_id(&self) -> &[u8; 32] {
        &self.token_id
    }

    /// Compute the canonical commitment to this cell's current state.
    ///
    /// This is a thin wrapper around
    /// [`crate::commitment::compute_canonical_state_commitment`], the single
    /// source of truth for "what bytes commit to this cell." `Ledger::hash_cell`
    /// is also routed through the same function so the sovereign-witness check
    /// (which uses `state_commitment`) and the federation Merkle leaf (which
    /// uses `hash_cell`) agree byte-for-byte. See `cell/src/commitment.rs` for
    /// the full hash shape and the audit context (P0-2).
    pub fn state_commitment(&self) -> [u8; 32] {
        // ALWAYS fresh: this is the off-ledger reader (sovereign-witness,
        // migration). It never consults `leaf_cache`, so a standalone cell
        // mutated through its `pub` fields can never serve a stale digest. The
        // cache is read only by `Ledger::hash_cell`, gated behind the ledger's
        // `&mut`-handoff invalidation. See [`LeafDigestCache`].
        crate::commitment::compute_canonical_state_commitment(self)
    }

    /// Mark the cached Merkle-leaf digest dirty
    /// (`.docs-history-noclaude/INCREMENTAL-COMMITMENT.md` step 3). Called by EVERY ledger path
    /// that hands out a `&mut Cell` or mutates a cell's fields directly, BEFORE
    /// the mutation is observable — the completeness guarantee. Cheap (a single
    /// `Mutex` store), so calling it unconditionally (even when a mutation turns
    /// out to be a no-op) is harmless: a dirty cache costs ONE extra BLAKE3 on
    /// the next `Ledger::hash_cell`, never a wrong leaf.
    #[inline]
    pub(crate) fn invalidate_leaf_cache(&self) {
        self.leaf_cache.store(None);
    }

    /// The canonical Merkle-leaf digest, consulting + filling the per-cell
    /// cache. ONLY `Ledger::hash_cell` calls this. On a hit the finished
    /// 32-byte leaf is returned with no BLAKE3 absorb; on a miss the full
    /// [`crate::commitment::compute_canonical_state_commitment`] runs and its
    /// result is stored back. Byte-identical to `state_commitment()` because
    /// the ledger invalidates the cache at every `&mut`-handoff seam.
    #[inline]
    pub(crate) fn cached_leaf_digest(&self) -> [u8; 32] {
        if let Some(d) = self.leaf_cache.load() {
            return d;
        }
        let d = crate::commitment::compute_canonical_state_commitment(self);
        self.leaf_cache.store(Some(d));
        d
    }

    /// Verify that `self.id` matches `derive_raw(public_key, token_id)`.
    ///
    /// Audit P2-3: the `id` field is content-addressed at construction but
    /// nothing in the type system maintains the invariant after construction.
    /// Authoritative call sites (sovereign-witness ingest, peer-exchange ingest,
    /// post-deserialization) should call this and reject cells that fail.
    pub fn verify_id_integrity(&self) -> bool {
        self.id == CellId::derive_raw(&self.public_key, &self.token_id)
    }

    /// Seal this cell: transition `lifecycle` to [`CellLifecycle::Sealed`].
    ///
    /// Per `PROTOCOL-CATEGORICAL-ANALYSIS.md §1.4`. Sealing is *reversible*
    /// quiescence — the cell rejects new effects but state and history
    /// are preserved. Use [`Cell::unseal`] to return to
    /// [`CellLifecycle::Live`]. Sealing is the prelude to destruction;
    /// it clarifies what destruction is not.
    ///
    /// # Errors
    ///
    /// Returns `Err(LifecycleTransitionError::Terminal)` if the cell is
    /// already in a terminal state (Destroyed or Migrated). Returns
    /// `Err(LifecycleTransitionError::AlreadySealed)` if the cell is
    /// already sealed (sealing is idempotent in effect but explicit so
    /// callers don't silently overwrite the original `reason_hash` /
    /// `sealed_at`).
    pub fn seal(
        &mut self,
        reason_hash: [u8; 32],
        sealed_at: u64,
    ) -> Result<(), LifecycleTransitionError> {
        match &self.lifecycle {
            CellLifecycle::Live | CellLifecycle::Archived { .. } => {
                self.lifecycle = CellLifecycle::Sealed {
                    reason_hash,
                    sealed_at,
                };
                Ok(())
            }
            CellLifecycle::Sealed { .. } => Err(LifecycleTransitionError::AlreadySealed),
            CellLifecycle::Destroyed { .. } | CellLifecycle::Migrated { .. } => {
                Err(LifecycleTransitionError::Terminal)
            }
        }
    }

    /// Reverse a seal: transition `lifecycle` from [`CellLifecycle::Sealed`]
    /// back to [`CellLifecycle::Live`].
    ///
    /// Per `PROTOCOL-CATEGORICAL-ANALYSIS.md §1.4`. The reversibility of
    /// seal/unseal is precisely what distinguishes sealing from
    /// destruction.
    ///
    /// # Errors
    ///
    /// Returns `Err(LifecycleTransitionError::NotSealed)` if the cell is
    /// not currently in [`CellLifecycle::Sealed`].
    pub fn unseal(&mut self) -> Result<(), LifecycleTransitionError> {
        if matches!(self.lifecycle, CellLifecycle::Sealed { .. }) {
            self.lifecycle = CellLifecycle::Live;
            Ok(())
        } else {
            Err(LifecycleTransitionError::NotSealed)
        }
    }

    /// Permanently retire this cell: transition `lifecycle` to
    /// [`CellLifecycle::Destroyed`] and bind a [`DeathCertificate`] hash
    /// into the final state.
    ///
    /// Per `PROTOCOL-CATEGORICAL-ANALYSIS.md §1.4`. Destruction is
    /// *permanent* — once a cell is Destroyed it cannot transition to
    /// any other lifecycle state. Descendants / observers can present
    /// the cell's final state-commitment alongside the
    /// `DeathCertificate` to prove "this cell is permanently retired"
    /// rather than inferring from absence.
    ///
    /// # Errors
    ///
    /// Returns `Err(LifecycleTransitionError::Terminal)` if the cell is
    /// already in a terminal state.
    pub fn destroy(
        &mut self,
        certificate: &crate::lifecycle::DeathCertificate,
    ) -> Result<(), LifecycleTransitionError> {
        if self.lifecycle.is_terminal() {
            return Err(LifecycleTransitionError::Terminal);
        }
        if certificate.cell_id != self.id {
            return Err(LifecycleTransitionError::CertificateMismatch);
        }
        self.lifecycle = CellLifecycle::Destroyed {
            death_certificate_hash: certificate.certificate_hash(),
            destroyed_at: certificate.destroyed_at_height,
        };
        Ok(())
    }

    /// Mark this cell's receipt-chain prefix as archived. Lifecycle
    /// transitions to [`CellLifecycle::Archived`] (or stays Archived
    /// with the newer checkpoint).
    ///
    /// Per `PROTOCOL-CATEGORICAL-ANALYSIS.md §4.2`. Archival does NOT
    /// disable the cell — `lifecycle.accepts_effects()` remains true.
    /// What changes: verifiers reconstructing the chain prior to
    /// `archived_through` consult the off-chain blob referenced by
    /// `checkpoint_hash`; chain links above the cutover walk the live
    /// tail.
    ///
    /// # Errors
    ///
    /// Returns `Err(LifecycleTransitionError::Terminal)` if the cell is
    /// in a terminal state, `Err(LifecycleTransitionError::SealedCannotArchive)`
    /// if it is sealed (unseal first if you really mean to archive a
    /// sealed cell's history), and
    /// `Err(LifecycleTransitionError::CertificateMismatch)` if the
    /// attestation does not bind to this cell.
    pub fn archive(
        &mut self,
        attestation: &crate::lifecycle::ArchivalAttestation,
    ) -> Result<(), LifecycleTransitionError> {
        if self.lifecycle.is_terminal() {
            return Err(LifecycleTransitionError::Terminal);
        }
        if self.lifecycle.is_sealed() {
            return Err(LifecycleTransitionError::SealedCannotArchive);
        }
        if attestation.cell_id != self.id {
            return Err(LifecycleTransitionError::CertificateMismatch);
        }
        attestation
            .validate()
            .map_err(LifecycleTransitionError::InvalidAttestation)?;
        // Monotonicity: an earlier archival cutover cannot replace a
        // later one (archived_through is monotone).
        if let CellLifecycle::Archived {
            archived_through, ..
        } = &self.lifecycle
            && attestation.archive_end_height <= *archived_through
        {
            return Err(LifecycleTransitionError::ArchiveNotMonotone);
        }
        self.lifecycle = CellLifecycle::Archived {
            checkpoint_hash: attestation.checkpoint_hash(),
            archived_through: attestation.archive_end_height,
        };
        Ok(())
    }

    /// Whether this cell currently accepts new effects.
    ///
    /// Shortcut for `self.lifecycle.accepts_effects()`. The executor
    /// consults this before applying any state-mutating effect; effects
    /// targeting a non-accepting cell are rejected with a structural
    /// "cell is sealed / destroyed / migrated" error.
    pub fn accepts_effects(&self) -> bool {
        self.lifecycle.accepts_effects()
    }

    /// Shortcut for `self.lifecycle.is_live()` — the verified-kernel Live-ONLY
    /// predicate (lifecycle discriminant `0`), matching Lean's `cellLive` /
    /// `cellLifecycleLive` / `acceptsEffects`. Unlike [`Self::accepts_effects`]
    /// this REJECTS `Archived`; cross-cell state-mutating effects gate on this.
    pub fn is_live(&self) -> bool {
        self.lifecycle.is_live()
    }

    /// Create a child cell delegated to this cell.
    pub fn spawn_child(&self, child_public_key: [u8; 32], child_token_id: [u8; 32]) -> Cell {
        let id = CellId::derive_raw(&child_public_key, &child_token_id);
        Cell {
            id,
            public_key: child_public_key,
            pq_identity: None,
            state: CellState::default(),
            permissions: Permissions::default(),
            verification_key: None,
            delegate: Some(self.id),
            delegation: None,
            token_id: child_token_id,
            capabilities: CapabilitySet::new(),
            program: CellProgram::None,
            mode: CellMode::Hosted,
            lifecycle: CellLifecycle::Live,
            leaf_cache: LeafDigestCache::default(),
        }
    }

    /// Create a child cell with snapshot+refresh delegation from this cell.
    ///
    /// The child inherits a point-in-time snapshot of the parent's c-list.
    /// The snapshot epoch and refresh timestamp are set by the caller.
    ///
    /// Audit P1-5: This constructor produces a `DelegatedRef` with a
    /// placeholder all-zero signature, which `verify_parent_signature` will
    /// reject. To prevent external code from minting forged delegations by
    /// calling this and then skipping verification, the function is now
    /// `pub(crate)` — only the cell crate (and downstream callers that
    /// re-export it deliberately) can invoke it. External orchestration
    /// should go through a signature-required constructor or
    /// `DelegatedRef::new` with a real signature.
    #[cfg(test)]
    pub(crate) fn spawn_child_with_delegation(
        &self,
        child_public_key: [u8; 32],
        child_token_id: [u8; 32],
        delegation_epoch: u64,
        refreshed_at: u64,
        max_staleness: u64,
    ) -> Cell {
        let id = CellId::derive_raw(&child_public_key, &child_token_id);
        let snapshot: Vec<crate::capability::CapabilityRef> =
            self.capabilities.iter().cloned().collect();
        Cell {
            id,
            public_key: child_public_key,
            pq_identity: None,
            state: CellState::default(),
            permissions: Permissions::default(),
            verification_key: None,
            delegate: Some(self.id),
            delegation: Some({
                let clist_bytes = postcard::to_allocvec(&snapshot).unwrap_or_default();
                let clist_commitment = DelegatedRef::compute_clist_commitment(&clist_bytes);
                DelegatedRef::new(
                    self.id,
                    id,
                    snapshot,
                    delegation_epoch,
                    refreshed_at,
                    max_staleness,
                    clist_commitment,
                    [0u8; 64], // Placeholder signature — spawn_child is a privileged internal op.
                )
            }),
            token_id: child_token_id,
            capabilities: CapabilitySet::new(),
            program: CellProgram::None,
            mode: CellMode::Hosted,
            lifecycle: CellLifecycle::Live,
            leaf_cache: LeafDigestCache::default(),
        }
    }
}

#[cfg(test)]
mod pq_identity_tests {
    use super::*;

    fn key(byte: u8) -> Vec<u8> {
        vec![byte; ML_DSA_65_PUBLIC_KEY_LEN]
    }

    #[test]
    fn identity_rotation_is_exactly_monotone_and_rejects_rollback() {
        let mut cell = Cell::new([1u8; 32], [2u8; 32]);
        cell.install_pq_identity(&key(3))
            .expect("epoch-zero install");
        let epoch0 = cell.pq_identity().cloned().expect("installed identity");
        assert_eq!(epoch0.key_epoch, 0);

        assert!(matches!(
            cell.rotate_pq_identity(1, &key(4)),
            Err(CellPqIdentityError::EpochMismatch {
                expected: 1,
                actual: 0
            })
        ));
        assert_eq!(cell.pq_identity(), Some(&epoch0));

        cell.rotate_pq_identity(0, &key(4))
            .expect("one-step rotation");
        let epoch1 = cell.pq_identity().expect("rotated identity");
        assert_eq!(epoch1.key_epoch, 1);
        assert_eq!(
            epoch1.ml_dsa_key_commitment,
            ml_dsa_public_key_commitment(&key(4)).unwrap()
        );
        assert!(matches!(
            cell.rotate_pq_identity(0, &key(5)),
            Err(CellPqIdentityError::EpochMismatch {
                expected: 0,
                actual: 1
            })
        ));
        assert!(matches!(
            cell.rotate_pq_identity(1, &key(4)),
            Err(CellPqIdentityError::UnchangedKey)
        ));
    }

    #[test]
    fn identity_is_durable_across_canonical_wire_roundtrip() {
        let bound =
            Cell::with_hybrid_balance([7u8; 32], &key(8), [9u8; 32], 42).expect("bound cell");
        let encoded = postcard::to_stdvec(&bound).expect("encode current cell");
        let decoded: Cell = postcard::from_bytes(&encoded).expect("decode current cell");
        assert_eq!(decoded.pq_identity(), bound.pq_identity());
        assert_eq!(decoded.state_commitment(), bound.state_commitment());
    }
}

#[cfg(test)]
mod lifecycle_transition_tests {
    //! Adversarial tests for the Cell lifecycle transition primitives.
    //!
    //! Per PROTOCOL-CATEGORICAL-ANALYSIS.md §1.4: seal/unseal must be
    //! exactly inverse; destroy is terminal; the certificate must bind
    //! to the cell being retired; archive must be monotone.
    use super::*;
    use crate::lifecycle::{ArchivalAttestation, DeathCertificate, DeathReason};

    fn fresh(b: u8) -> Cell {
        let mut k = [0u8; 32];
        k[0] = b;
        Cell::new(k, [0u8; 32])
    }

    #[test]
    fn seal_then_unseal_round_trips() {
        let mut c = fresh(1);
        assert!(c.accepts_effects());
        c.seal([9u8; 32], 100).unwrap();
        assert!(!c.accepts_effects());
        assert!(c.lifecycle.is_sealed());
        c.unseal().unwrap();
        assert!(c.accepts_effects());
        assert!(matches!(c.lifecycle, CellLifecycle::Live));
    }

    #[test]
    fn second_seal_rejected() {
        let mut c = fresh(1);
        c.seal([9u8; 32], 100).unwrap();
        let err = c.seal([7u8; 32], 200).unwrap_err();
        assert_eq!(err, LifecycleTransitionError::AlreadySealed);
        // Original seal data must be preserved.
        if let CellLifecycle::Sealed {
            reason_hash,
            sealed_at,
        } = c.lifecycle
        {
            assert_eq!(reason_hash, [9u8; 32]);
            assert_eq!(sealed_at, 100);
        } else {
            panic!("expected Sealed");
        }
    }

    #[test]
    fn unseal_on_live_cell_rejected() {
        let mut c = fresh(1);
        let err = c.unseal().unwrap_err();
        assert_eq!(err, LifecycleTransitionError::NotSealed);
    }

    #[test]
    fn destroy_is_terminal() {
        let mut c = fresh(1);
        let dc = DeathCertificate {
            cell_id: c.id(),
            last_receipt_hash: [1u8; 32],
            final_state_commitment: c.state_commitment(),
            destroyed_at_height: 42,
            reason: DeathReason::Voluntary,
        };
        c.destroy(&dc).unwrap();
        assert!(c.lifecycle.is_destroyed());
        assert!(c.lifecycle.is_terminal());
        assert!(!c.accepts_effects());

        // No further transition is allowed.
        assert_eq!(
            c.seal([0u8; 32], 1).unwrap_err(),
            LifecycleTransitionError::Terminal
        );
        assert_eq!(c.unseal().unwrap_err(), LifecycleTransitionError::NotSealed);
        assert_eq!(
            c.destroy(&dc).unwrap_err(),
            LifecycleTransitionError::Terminal
        );
    }

    #[test]
    fn destroy_rejects_certificate_for_other_cell() {
        let mut c = fresh(1);
        let other = fresh(2);
        let dc = DeathCertificate {
            cell_id: other.id(),
            last_receipt_hash: [1u8; 32],
            final_state_commitment: other.state_commitment(),
            destroyed_at_height: 42,
            reason: DeathReason::Voluntary,
        };
        let err = c.destroy(&dc).unwrap_err();
        assert_eq!(err, LifecycleTransitionError::CertificateMismatch);
        assert!(matches!(c.lifecycle, CellLifecycle::Live));
    }

    #[test]
    fn destroy_from_sealed_is_allowed() {
        // Sealing-as-prelude-to-destruction is the documented usage.
        let mut c = fresh(1);
        c.seal([9u8; 32], 100).unwrap();
        let dc = DeathCertificate {
            cell_id: c.id(),
            last_receipt_hash: [1u8; 32],
            final_state_commitment: c.state_commitment(),
            destroyed_at_height: 200,
            reason: DeathReason::Forced,
        };
        c.destroy(&dc).unwrap();
        assert!(c.lifecycle.is_destroyed());
    }

    #[test]
    fn archive_succeeds_and_cell_still_accepts() {
        let mut c = fresh(1);
        let a = ArchivalAttestation {
            cell_id: c.id(),
            archive_start_height: 0,
            archive_end_height: 100,
            archive_blob_hash: [1u8; 32],
            archive_terminal_commitment: [2u8; 32],
            archive_terminal_receipt_hash: [3u8; 32],
        };
        c.archive(&a).unwrap();
        assert!(c.accepts_effects(), "archived cells still accept effects");
        if let CellLifecycle::Archived {
            archived_through, ..
        } = c.lifecycle
        {
            assert_eq!(archived_through, 100);
        } else {
            panic!("expected Archived");
        }
    }

    #[test]
    fn archive_must_be_monotone() {
        let mut c = fresh(1);
        let a1 = ArchivalAttestation {
            cell_id: c.id(),
            archive_start_height: 0,
            archive_end_height: 100,
            archive_blob_hash: [1u8; 32],
            archive_terminal_commitment: [2u8; 32],
            archive_terminal_receipt_hash: [3u8; 32],
        };
        let a2_older = ArchivalAttestation {
            cell_id: c.id(),
            archive_start_height: 0,
            archive_end_height: 50, // older
            archive_blob_hash: [4u8; 32],
            archive_terminal_commitment: [5u8; 32],
            archive_terminal_receipt_hash: [6u8; 32],
        };
        let a3_newer = ArchivalAttestation {
            cell_id: c.id(),
            archive_start_height: 101,
            archive_end_height: 200,
            archive_blob_hash: [7u8; 32],
            archive_terminal_commitment: [8u8; 32],
            archive_terminal_receipt_hash: [9u8; 32],
        };

        c.archive(&a1).unwrap();
        assert_eq!(
            c.archive(&a2_older).unwrap_err(),
            LifecycleTransitionError::ArchiveNotMonotone
        );
        c.archive(&a3_newer).unwrap(); // monotone advance OK
        if let CellLifecycle::Archived {
            archived_through, ..
        } = c.lifecycle
        {
            assert_eq!(archived_through, 200);
        }
    }

    #[test]
    fn archive_rejects_other_cell_attestation() {
        let mut c = fresh(1);
        let other = fresh(2);
        let a = ArchivalAttestation {
            cell_id: other.id(),
            archive_start_height: 0,
            archive_end_height: 100,
            archive_blob_hash: [1u8; 32],
            archive_terminal_commitment: [2u8; 32],
            archive_terminal_receipt_hash: [3u8; 32],
        };
        assert_eq!(
            c.archive(&a).unwrap_err(),
            LifecycleTransitionError::CertificateMismatch
        );
    }

    #[test]
    fn sealed_cells_cannot_be_archived() {
        let mut c = fresh(1);
        c.seal([1u8; 32], 50).unwrap();
        let a = ArchivalAttestation {
            cell_id: c.id(),
            archive_start_height: 0,
            archive_end_height: 100,
            archive_blob_hash: [1u8; 32],
            archive_terminal_commitment: [2u8; 32],
            archive_terminal_receipt_hash: [3u8; 32],
        };
        assert_eq!(
            c.archive(&a).unwrap_err(),
            LifecycleTransitionError::SealedCannotArchive
        );
    }

    #[test]
    fn terminal_cells_reject_archive() {
        let mut c = fresh(1);
        let dc = DeathCertificate {
            cell_id: c.id(),
            last_receipt_hash: [1u8; 32],
            final_state_commitment: c.state_commitment(),
            destroyed_at_height: 42,
            reason: DeathReason::Voluntary,
        };
        c.destroy(&dc).unwrap();
        let a = ArchivalAttestation {
            cell_id: c.id(),
            archive_start_height: 0,
            archive_end_height: 100,
            archive_blob_hash: [1u8; 32],
            archive_terminal_commitment: [2u8; 32],
            archive_terminal_receipt_hash: [3u8; 32],
        };
        assert_eq!(
            c.archive(&a).unwrap_err(),
            LifecycleTransitionError::Terminal
        );
    }

    /// State-commitment difference: sealing produces a *different*
    /// commitment than the original Live cell. This is what binds the
    /// lifecycle transition into the chain.
    #[test]
    fn lifecycle_transition_changes_state_commitment() {
        let mut c = fresh(1);
        let live_commit = c.state_commitment();
        c.seal([5u8; 32], 100).unwrap();
        let sealed_commit = c.state_commitment();
        assert_ne!(live_commit, sealed_commit);
        c.unseal().unwrap();
        let unsealed_commit = c.state_commitment();
        // Round-trip: unsealed cell agrees with original Live commit.
        assert_eq!(live_commit, unsealed_commit);
    }
}
