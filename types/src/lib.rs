//! Canonical shared types for the dregg federation protocol.
//!
//! This crate defines the ONE TRUE version of cryptographic primitives and
//! consensus types used across `dregg-wire`, `dregg-persist`, `dregg-federation`,
//! and other crates.
//!
//! # Key invariants
//!
//! - [`Signature`] is ALWAYS 64 bytes (Ed25519).
//! - [`PublicKey`] is ALWAYS 32 bytes (Ed25519).
//! - [`AttestedRoot`] carries `Vec<(PublicKey, Signature)>` with correct sizes.
//!
//! # Serde
//!
//! All types derive `Serialize`/`Deserialize` and are compatible with both
//! postcard (compact binary) and JSON serialization.

pub mod causal;

use std::collections::HashSet;
use std::fmt;

use serde::{Deserialize, Serialize};
use zeroize::Zeroize;

pub use causal::{CausalDag, CausalError};

// =============================================================================
// Cryptographic Primitives
// =============================================================================

/// Ed25519 public key (32 bytes).
///
/// # Serialization
///
/// Uses `serde_32` which serializes as a length-prefixed byte sequence (Vec<u8>)
/// for format compatibility. Note that this differs from `dregg_cell::NoteCommitment`
/// which derives Serialize/Deserialize directly on its `[u8; 32]` (raw fixed array,
/// no length prefix in postcard). Both are correct for their respective wire formats:
/// `PublicKey` appears in variable-length structures (AttestedRoot signatures) while
/// NoteCommitment appears in fixed-layout note trees.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct PublicKey(#[serde(with = "serde_32")] pub [u8; 32]);

impl PublicKey {
    /// Short hex representation for display (first 4 bytes).
    pub fn short_hex(&self) -> String {
        self.0[..4].iter().map(|b| format!("{b:02x}")).collect()
    }

    /// Full hex representation.
    pub fn hex(&self) -> String {
        self.0.iter().map(|b| format!("{b:02x}")).collect()
    }

    /// Return the underlying bytes.
    pub fn as_bytes(&self) -> &[u8; 32] {
        &self.0
    }

    /// Convert to the underlying ed25519_dalek verifying key.
    fn to_verifying_key(&self) -> Option<ed25519_dalek::VerifyingKey> {
        ed25519_dalek::VerifyingKey::from_bytes(&self.0).ok()
    }

    /// Verify that a signature over `message` was produced by this key.
    ///
    /// Uses `verify_strict` to reject non-canonical S values, preventing
    /// signature malleability (transaction malleability attacks).
    pub fn verify(&self, message: &[u8], signature: &Signature) -> bool {
        match self.to_verifying_key() {
            Some(vk) => {
                let sig = ed25519_dalek::Signature::from_bytes(&signature.0);
                vk.verify_strict(message, &sig).is_ok()
            }
            None => false,
        }
    }
}

impl fmt::Debug for PublicKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "PubKey({})", self.short_hex())
    }
}

impl fmt::Display for PublicKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.short_hex())
    }
}

/// Ed25519 signature (64 bytes).
///
/// This is the CORRECT size for Ed25519 signatures. Previous versions of
/// `dregg-wire` and `dregg-persist` incorrectly used 32-byte arrays, which
/// truncated signatures and made verification impossible.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Signature(#[serde(with = "serde_64")] pub [u8; 64]);

impl fmt::Debug for Signature {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Sig({})",
            self.0[..4]
                .iter()
                .map(|b| format!("{b:02x}"))
                .collect::<String>()
        )
    }
}

/// An Ed25519 signing key (private key).
///
/// NOTE: Clone is intentionally retained for key derivation workflows, but each
/// clone is an untracked copy of the secret material. Prefer passing references
/// where possible.
#[derive(Clone)]
pub struct SigningKey(ed25519_dalek::SigningKey);

impl SigningKey {
    /// Create a signing key from raw 32-byte secret key material.
    ///
    /// # Security
    ///
    /// The caller is responsible for ensuring the key material is from a
    /// trusted source and is properly zeroized after use.
    pub fn from_bytes(bytes: &[u8; 32]) -> Self {
        Self(ed25519_dalek::SigningKey::from_bytes(bytes))
    }

    /// Derive the corresponding public key from this signing key.
    pub fn public_key(&self) -> PublicKey {
        PublicKey(self.0.verifying_key().to_bytes())
    }

    /// Return the raw 32-byte secret key material.
    ///
    /// # Security
    ///
    /// The returned bytes are sensitive. The caller must ensure they are not
    /// leaked or persisted without appropriate protections.
    pub fn to_bytes(&self) -> [u8; 32] {
        self.0.to_bytes()
    }
}

// Safety: ed25519_dalek::SigningKey (with the "zeroize" feature enabled in Cargo.toml)
// implements ZeroizeOnDrop. When this wrapper is dropped, the inner SigningKey's
// Drop impl scrubs the secret_key bytes from memory. No additional Drop impl is
// needed on the wrapper itself -- the inner type handles key hygiene.

impl fmt::Debug for SigningKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "SigningKey(<redacted>)")
    }
}

/// Generate an Ed25519 keypair.
pub fn generate_keypair() -> (SigningKey, PublicKey) {
    let mut key_bytes = [0u8; 32];
    getrandom::fill(&mut key_bytes).expect("getrandom failed");
    let sk = ed25519_dalek::SigningKey::from_bytes(&key_bytes);
    key_bytes.zeroize();
    let vk = sk.verifying_key();
    (SigningKey(sk), PublicKey(vk.to_bytes()))
}

/// Sign a message with a signing key (Ed25519).
pub fn sign(key: &SigningKey, message: &[u8]) -> Signature {
    use ed25519_dalek::Signer;
    let sig = key.0.sign(message);
    Signature(sig.to_bytes())
}

/// Verify a signature against a public key (Ed25519).
pub fn verify(public_key: &PublicKey, message: &[u8], signature: &Signature) -> bool {
    public_key.verify(message, signature)
}

/// Hex-encode a byte slice.
pub fn hex_encode(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

/// **Char-safe** decode of exactly 64 ASCII hex characters into 32 bytes — the
/// canonical inverse of [`hex_encode`] for a 32-byte id. Returns `None` on any
/// non-hex byte or a length other than 64 bytes.
///
/// This is the ONE codec the deos JS / view surfaces route their `parse_cell_id`
/// / `hex_decode_*` helpers through. It NEVER slices a `&str` by byte offset, so
/// a 64-BYTE guest/author string containing a multibyte char returns `None` (its
/// first non-ASCII byte fails the hex-digit check) instead of PANICKING on a
/// mid-codepoint slice. That panic matters: inside a JS engine's `extern "C"`
/// callback it unwinds across the FFI boundary to an abort. `str::len` counts
/// BYTES, so the old guards that checked `len() == 64` and then indexed
/// `&s[i*2..i*2+2]` mixed a byte-length check with a char-boundary slice.
pub fn parse_hex32(s: &str) -> Option<[u8; 32]> {
    let bytes = s.as_bytes();
    if bytes.len() != 64 {
        return None;
    }
    let mut out = [0u8; 32];
    for (i, o) in out.iter_mut().enumerate() {
        let hi = hex_nibble(bytes[2 * i])?;
        let lo = hex_nibble(bytes[2 * i + 1])?;
        *o = (hi << 4) | lo;
    }
    Some(out)
}

/// The `0..=15` value of one ASCII hex-digit byte, or `None` if it is not a hex
/// digit. Byte-wise (never `&str`-indexed), so it is immune to codepoint
/// boundaries — see [`parse_hex32`].
fn hex_nibble(b: u8) -> Option<u8> {
    match b {
        b'0'..=b'9' => Some(b - b'0'),
        b'a'..=b'f' => Some(b - b'a' + 10),
        b'A'..=b'F' => Some(b - b'A' + 10),
        _ => None,
    }
}

/// BLS threshold quorum certificate (opaque bytes, constant size regardless of committee).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ThresholdQC(pub Vec<u8>);

// =============================================================================
// FederationId
// =============================================================================

/// Identifies a federation in the unified model.
///
/// **Canonical home.** Previously, two disjoint definitions lived in
/// `dregg-captp` and `dregg-blocklace`; both now re-export this single type
/// (see `FEDERATION-UNIFICATION-DESIGN.md` step 2). The id is a commitment to
/// the federation's committee — `H(sorted(members) || epoch)` — derived via
/// `dregg_federation::derive_federation_id_with_epoch`.
///
/// In the unified lace model, a `FederationId` is semantically equivalent to a
/// `GroupId` (the content-hash of a reference group's strands). Routing layers
/// treat them interchangeably.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize, Default)]
pub struct FederationId(pub [u8; 32]);

impl FederationId {
    /// All-zeros placeholder. Used during boot before the local federation's
    /// members are known. Real federations always have a non-zero id (the
    /// hash of a non-empty committee).
    pub const PLACEHOLDER: FederationId = FederationId([0u8; 32]);

    /// Construct from raw bytes.
    pub const fn from_bytes(bytes: [u8; 32]) -> Self {
        FederationId(bytes)
    }

    /// Borrow the underlying bytes.
    pub fn as_bytes(&self) -> &[u8; 32] {
        &self.0
    }

    /// Short hex representation for logging (first 4 bytes).
    pub fn short_hex(&self) -> String {
        self.0[..4].iter().map(|b| format!("{b:02x}")).collect()
    }

    /// Full hex representation.
    pub fn hex(&self) -> String {
        self.0.iter().map(|b| format!("{b:02x}")).collect()
    }

    /// Derive a HYBRID single-member `FederationId` that commits to BOTH a
    /// member's ed25519 public key AND its ML-DSA public key
    /// ([`hybrid_id_commitment`]).
    ///
    /// This binds one participant's hybrid keypair — the shape the CapTP
    /// handoff / peer-authentication surfaces need, where a `FederationId`
    /// stands for a single peer identity rather than a whole committee. The
    /// committee-commitment form (`H(sorted(members) ‖ epoch)`,
    /// `dregg_federation::derive_federation_id_with_epoch`) is unchanged; at
    /// genesis each committee MEMBER's per-member id becomes this hybrid id so
    /// the enrolled ML-DSA roster is derivable from the member ids.
    pub fn derive_hybrid(ed25519_pk: &[u8; 32], ml_dsa_pk: &[u8]) -> Self {
        FederationId(hybrid_id_commitment(ed25519_pk, ml_dsa_pk))
    }

    /// The cryptographic enroll+pin check for a hybrid member id: does this id
    /// commit to `ed25519_pk` AND `ml_dsa_pk`? See [`verify_committed_ml_dsa`].
    pub fn verify_committed_ml_dsa(&self, ed25519_pk: &[u8; 32], ml_dsa_pk: &[u8]) -> bool {
        verify_committed_ml_dsa(&self.0, ed25519_pk, ml_dsa_pk)
    }
}

impl fmt::Debug for FederationId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "FedId({})", self.short_hex())
    }
}

impl fmt::Display for FederationId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            self.0[..8]
                .iter()
                .map(|b| format!("{b:02x}"))
                .collect::<String>()
        )
    }
}

impl From<[u8; 32]> for FederationId {
    fn from(bytes: [u8; 32]) -> Self {
        FederationId(bytes)
    }
}

impl From<FederationId> for [u8; 32] {
    fn from(id: FederationId) -> Self {
        id.0
    }
}

// =============================================================================
// Consensus / Federation Types
// =============================================================================

/// Attested revocation root with quorum signatures.
///
/// This is the canonical definition. It carries FULL 64-byte signatures.
///
/// Closes finding F3 in `AUDIT-federation.md` / gap D in
/// `AUDIT-blocklace-consensus.md`: an attested root now binds to a specific
/// blocklace block id and finality round. Two attested roots at the same
/// `height` from different blocklace forks are distinguishable because their
/// `blocklace_block_id` differs.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AttestedRoot {
    /// The Merkle root of the revocation tree (cell state).
    pub merkle_root: [u8; 32],
    /// The note commitment tree root (append-only Merkle tree of note commitments).
    /// `None` if the federation has not yet integrated note tree attestation.
    pub note_tree_root: Option<[u8; 32]>,
    /// The nullifier set root (commitment to all spent nullifiers).
    /// `None` if the federation has not yet integrated nullifier attestation.
    pub nullifier_set_root: Option<[u8; 32]>,
    /// The block height at which this root was finalized.
    pub height: u64,
    /// Unix timestamp (seconds) when finalized.
    pub timestamp: i64,
    /// The blocklace block id (32-byte BLAKE3) this attestation is anchored
    /// to. `None` for legacy roots produced before F3 was wired; production
    /// roots from the live consensus path always carry it.
    #[serde(default)]
    pub blocklace_block_id: Option<[u8; 32]>,
    /// The Cordial Miners "round" (DAG depth, monotone per-participant) at
    /// the anchoring block. `None` for legacy roots.
    #[serde(default)]
    pub finality_round: Option<u64>,
    /// Quorum signatures: (public_key, signature) pairs with FULL 64-byte sigs.
    pub quorum_signatures: Vec<(PublicKey, Signature)>,
    /// Optional threshold aggregate QC (constant-size BLS, preferred over individual sigs).
    pub threshold_qc: Option<ThresholdQC>,
    /// The number of signatures required for validity.
    pub threshold: usize,
    /// The federation id this attestation is produced by. Bound into the
    /// signing message preimage so that a verifier who reconstructs the
    /// message can detect cross-federation attestation swaps without
    /// consulting any out-of-band state. `FederationId::PLACEHOLDER`
    /// (all-zero) for legacy roots produced before v3 was wired.
    #[serde(default)]
    pub federation_id: FederationId,
    /// **v4 (issue #80):** Merkle root over the canonical
    /// [`TurnReceipt::receipt_hash`] of every receipt the federation
    /// committed in this attestation period.
    ///
    /// Today `AttestedRoot` commits to ledger state (`merkle_root`,
    /// `note_tree_root`, `nullifier_set_root`) but not to the receipt
    /// stream: two federations with the same `merkle_root` could process
    /// disjoint receipt streams and look indistinguishable. Binding the
    /// receipt stream into the signed preimage makes "the WitnessedReceipt
    /// chain IS the persistence layer" enforceable — a verifier that holds
    /// the claimed receipt set can recompute this root via
    /// [`merkle_root_of_receipt_hashes`] and reject any divergence.
    ///
    /// `None` for legacy v3 roots that predate this field; production
    /// v4 attestations always carry it. Receipts that hash into this root
    /// are those whose `receipt_hash()` corresponds to the turns commiteed
    /// in this attestation's block / period / epoch.
    #[serde(default)]
    pub receipt_stream_root: Option<[u8; 32]>,
    /// **HYBRID quorum (post-quantum closure of the cross-federation finality
    /// wire).** Per-signer [`HybridQuorumSig`] over the SAME canonical bytes as
    /// `quorum_signatures` sign ([`signing_message`](Self::signing_message)):
    /// each entry carries the voter's ed25519 signature AND its ML-DSA-65
    /// (FIPS 204) signature plus the SELF-CONTAINED ML-DSA public key. A
    /// verifier counts a signer only when BOTH halves verify (classical ∧ pq),
    /// so an adversary who breaks ed25519 alone cannot forge the quorum.
    ///
    /// This is the wire twin of the persist layer's
    /// `StoredAttestedRoot::finalization_quorum` and the light-client
    /// `SignedVote` hybrid record. The ML-DSA verification itself lives in
    /// `dregg_federation` (which owns the FIPS 204 primitive); this crate is
    /// the leaf and carries only the wire DATA. The cross-fed verifier
    /// (`dregg_verifier::cross_fed`) requires this quorum: a classical-only
    /// root (empty `hybrid_quorum`) fails closed.
    ///
    /// **Wire note (postcard flag-day).** Adding this field changes the
    /// non-self-describing postcard bytes of an `AttestedRoot`. A hybrid
    /// deployment is a big-bang flag day (state wipe) — accepted, exactly as
    /// the `StoredAttestedRoot`/`Checkpoint`/`ReceiptQc::HybridVotes` hybrid
    /// widenings were. Empty for legacy roots and classical-only builders.
    #[serde(default)]
    pub hybrid_quorum: Vec<HybridQuorumSig>,
}

/// Compute the canonical Merkle root over a slice of 32-byte receipt
/// hashes (the `receipt_hash()` of each receipt).
///
/// **Empty input → all-zero root.** This is the canonical "no receipts in
/// this block" commitment and matches the `receipt_stream_root: None`
/// path's sentinel for v3-style empty attestations promoted to v4 form.
///
/// The tree is a balanced BLAKE3 Merkle tree with explicit leaf/inner
/// domain separation (`b"\x00"` prefix for leaves, `b"\x01"` for internal
/// nodes) so leaf-vs-inner collisions are not possible. Odd levels duplicate
/// the last node (the standard Bitcoin/Ethereum pad) — note that this means
/// a one-element tree's root differs from the lone leaf's domain-tagged
/// hash, which is desirable: we want the root to commit to "this set has
/// one element" rather than be indistinguishable from the leaf hash.
///
/// **Determinism:** the function is order-sensitive; callers MUST pass
/// receipt hashes in the canonical order the federation committed them.
/// For per-block attestations that is the block's turn-commit order; the
/// production attestation site in `node/src/blocklace_sync.rs` uses the
/// finalized-turn order so all honest verifiers reconstruct the same root.
pub fn merkle_root_of_receipt_hashes(receipts: &[[u8; 32]]) -> [u8; 32] {
    if receipts.is_empty() {
        return [0u8; 32];
    }
    // Domain-tag leaves so an internal node can never collide with one.
    let mut layer: Vec<[u8; 32]> = receipts
        .iter()
        .map(|h| {
            let mut hasher = blake3::Hasher::new();
            hasher.update(b"\x00dregg-receipt-leaf-v1");
            hasher.update(h);
            *hasher.finalize().as_bytes()
        })
        .collect();
    while layer.len() > 1 {
        if layer.len() % 2 == 1 {
            let last = *layer.last().unwrap();
            layer.push(last);
        }
        let mut next: Vec<[u8; 32]> = Vec::with_capacity(layer.len() / 2);
        for pair in layer.chunks_exact(2) {
            let mut hasher = blake3::Hasher::new();
            hasher.update(b"\x01dregg-receipt-inner-v1");
            hasher.update(&pair[0]);
            hasher.update(&pair[1]);
            next.push(*hasher.finalize().as_bytes());
        }
        layer = next;
    }
    layer[0]
}

/// The domain-separation tag for a committee member's finalization vote over a
/// finalized `(block_id, merkle_root)`. Bumped v1 -> v2 with the N3
/// committee-restart fix, when the vote gained its `merkle_root` binding: a v2
/// vote signs the finalized state root it attests, so a quorum of these votes
/// IS the restart anchor's quorum. The bump fences the format against a v1 vote
/// (which signed `block_id || level` only) being replayed as a v2 root vote.
///
/// **v2 -> v3 (state anchor).** `merkle_root` here is
/// `dregg_persist::canonical_ledger_root` — a BLAKE3 whole-image digest — and it
/// DELIBERATELY stays that. It is the **restart anchor**: a node re-reads its
/// store, reconstructs the ledger, and checks the reconstruction against this
/// quorum-signed value. No per-cell algebraic commitment fills that role, and
/// the whole-ledger 8-felt that would (`cells_root` Phase-E) is deferred. What
/// DID change is everything downstream: the receipts this vote's block carries
/// now anchor on the AIR-bound chip 8-felt commitment
/// (`dregg_turn::state_commit`) rather than a trusted-Rust `Ledger::root()`, and
/// the `AttestedRoot` this quorum re-anchors binds those receipts through
/// `receipt_stream_root`. The bump fences a v2 signature — made when the receipt
/// stream meant a BLAKE3 ledger root — from counting toward a v3 quorum.
pub const FINALIZATION_VOTE_DOMAIN_V3: &[u8] = b"dregg-finalization-vote-v3";

/// The canonical bytes a committee member signs when it votes that it has
/// finalized `block_id` over committed state root `merkle_root`.
///
/// This is the SINGLE source of truth for the finalization-vote preimage,
/// shared by the node's `FinalizationVote` (which produces the signatures) and
/// the persistence layer's `StoredAttestedRoot::verify_finalization_quorum`
/// (which re-verifies the persisted quorum on restart). Keeping it here — the
/// crate both depend on — makes the two byte-identical by construction, so a
/// gossiped finalization vote's signature verifies as a persisted quorum
/// signature with no format drift.
///
/// It binds ONLY the two provably-deterministic quantities that identify the
/// finalized state — the blocklace `block_id` and the canonical `merkle_root` —
/// so every honest committee member computes the identical preimage regardless
/// of local wall clock or per-node DAG bookkeeping.
pub fn finalization_vote_signing_message(block_id: &[u8; 32], merkle_root: &[u8; 32]) -> Vec<u8> {
    let mut buf = Vec::with_capacity(FINALIZATION_VOTE_DOMAIN_V3.len() + 32 + 32);
    buf.extend_from_slice(FINALIZATION_VOTE_DOMAIN_V3);
    buf.extend_from_slice(block_id);
    buf.extend_from_slice(merkle_root);
    buf
}

/// One committee member's HYBRID quorum signature over a canonical message:
/// the classical ed25519 half AND the FIPS 204 ML-DSA-65 half, with a REDUNDANT
/// copy of the signer's ML-DSA-65 public key carried ALONGSIDE the signature.
/// Mirrors `dregg_persist::QuorumSignature` (the finalization-quorum hybrid
/// record): a verifier counts a signer only when BOTH halves verify — and the
/// carried `ml_dsa_pubkey` is PINNED equal to the signer's genesis-ENROLLED
/// ML-DSA key (which the verifier threads in as an `ml_dsa_committee` roster
/// aligned with the ed25519 committee), NEVER trusted on its own. That pin is
/// what makes "an adversary who breaks ed25519 alone still cannot forge the
/// quorum" TRUE: the PQ half must verify under the enrolled key it does not hold.
///
/// This is the widened Votes-QC wire record for the checkpoint QC
/// ([`dregg_federation::checkpoint`]), the receipt QC's hybrid Votes flavor
/// ([`dregg_federation::receipt::ReceiptQc::HybridVotes`]), and the cross-fed
/// attested-root quorum. This crate is the leaf, so it carries only the wire
/// DATA — the ML-DSA verification (and the enrolled-key pin) lives in
/// `dregg_federation` (which owns the FIPS 204 primitive; see
/// `dregg_federation::receipt::verify_hybrid_quorum_sigs`).
///
/// **Wire note (postcard flag-day).** Carrying this record — a new receipt-QC
/// enum variant or a new checkpoint field — changes the non-self-describing
/// postcard bytes of those structures. A hybrid deployment is a big-bang flag
/// day (state wipe), accepted: there is no back-compatible in-place widening of
/// a per-signer classical tuple to a hybrid record.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct HybridQuorumSig {
    /// The voter's federation Ed25519 public key (the committee identity).
    pub pubkey: PublicKey,
    /// The ed25519 (CLASSICAL) signature over the canonical message.
    pub signature: Signature,
    /// A REDUNDANT copy of the voter's ML-DSA-65 (FIPS 204) public key, as its
    /// 1952 serialized bytes (`Vec<u8>` because the 1952-byte array is beyond
    /// serde's array-derive ceiling). At verify time it is PINNED equal to the
    /// voter's enrolled roster key — never trusted on its own — and fail-closed
    /// on a mismatch or an undecodable key.
    pub ml_dsa_pubkey: Vec<u8>,
    /// The ML-DSA-65 (POST-QUANTUM) signature over the SAME canonical message as
    /// `signature`, verified under the voter's ENROLLED key. The quorum counts a
    /// signer only when BOTH halves verify (and the enrolled-key pin holds), so
    /// an adversary who breaks ed25519 alone still cannot forge the quorum.
    pub pq_signature: Vec<u8>,
}

impl AttestedRoot {
    /// Convenience constructor for the common "no blocklace binding yet" case
    /// (tests, legacy fixtures). Production code in `node/` always sets
    /// `blocklace_block_id` and `finality_round` directly.
    pub fn new_legacy(
        merkle_root: [u8; 32],
        height: u64,
        timestamp: i64,
        quorum_signatures: Vec<(PublicKey, Signature)>,
        threshold_qc: Option<ThresholdQC>,
        threshold: usize,
    ) -> Self {
        Self {
            merkle_root,
            note_tree_root: None,
            nullifier_set_root: None,
            height,
            timestamp,
            blocklace_block_id: None,
            finality_round: None,
            quorum_signatures,
            threshold_qc,
            threshold,
            federation_id: FederationId::PLACEHOLDER,
            // Legacy roots predate the v4 receipt-stream binding (#80).
            receipt_stream_root: None,
            // Legacy/classical-only roots carry no post-quantum quorum; the
            // cross-fed verifier fails such a root closed.
            hybrid_quorum: Vec::new(),
        }
    }

    /// Is this attested root v4-complete (carries `receipt_stream_root`)?
    ///
    /// v3 roots that predate issue #80 return `false`: they attest only to
    /// ledger state, not to the receipt stream that produced it. Callers
    /// that require Silver-complete attestation (e.g. cross-federation
    /// verifiers that intend to enforce "the WitnessedReceipt chain IS
    /// the persistence layer") MUST reject `false` here.
    pub fn is_v4_receipt_complete(&self) -> bool {
        self.receipt_stream_root.is_some()
    }

    /// Verify that the claimed receipt set hashes to this root's
    /// `receipt_stream_root` (v4, issue #80).
    ///
    /// Returns `false` if:
    /// - the root is v3-legacy (no `receipt_stream_root`), OR
    /// - the recomputed Merkle root over the provided receipt hashes
    ///   does not match the bound value.
    ///
    /// Returns `true` only when the root carries a binding AND the
    /// reconstruction matches. Callers that wish to *accept* a v3
    /// root's bare ledger attestation MUST gate on
    /// [`is_v4_receipt_complete`](Self::is_v4_receipt_complete) before
    /// calling this method.
    ///
    /// `receipt_hashes` must be in the same canonical order the
    /// federation used to compute the bound root (see
    /// [`merkle_root_of_receipt_hashes`] doc).
    pub fn verify_receipt_stream(&self, receipt_hashes: &[[u8; 32]]) -> bool {
        let Some(bound) = self.receipt_stream_root else {
            return false;
        };
        let recomputed = merkle_root_of_receipt_hashes(receipt_hashes);
        bound == recomputed
    }

    /// Check if this root has sufficient signatures (count-only check, no crypto).
    ///
    /// **STRUCTURAL VALIDATION ONLY.** This performs no cryptographic verification.
    /// For Ed25519 signatures it checks count >= threshold. For a ThresholdQC it
    /// checks minimum byte length (>= 48 bytes for BLS12-381 G1 compressed point).
    /// Full cryptographic BLS verification of ThresholdQC requires the `hints`
    /// crate and is performed at a higher layer.
    ///
    /// Use `is_valid()` for Ed25519 cryptographic verification against known keys.
    pub fn has_quorum(&self) -> bool {
        if let Some(ref qc) = self.threshold_qc {
            // A ThresholdQC must be non-empty and meet minimum BLS12-381 G1 size.
            return qc.0.len() >= 48;
        }
        self.quorum_signatures.len() >= self.threshold
    }

    /// Alias for [`has_quorum`](Self::has_quorum) that makes the non-cryptographic
    /// nature of the check explicit in calling code.
    ///
    /// **STRUCTURAL VALIDATION ONLY.** This checks signature count and QC byte
    /// length but does NOT perform any cryptographic verification. Full BLS
    /// verification of ThresholdQC requires the `hints` crate and is done at a
    /// higher layer.
    pub fn is_structurally_valid(&self) -> bool {
        self.has_quorum()
    }

    /// Verify that this attested root has sufficient valid signatures.
    ///
    /// Performs **cryptographic verification** of the Ed25519 signatures against
    /// the provided set of known federation public keys. Each signer must be in
    /// `known_keys` and each signature must be cryptographically valid over the
    /// canonical signing message.
    ///
    /// Duplicate signers are rejected: if the same public key appears more than
    /// once in `quorum_signatures`, only the first occurrence counts toward the
    /// threshold. This prevents replay of a single valid (key, signature) pair
    /// to satisfy quorum.
    ///
    /// **NOTE on ThresholdQC:** If a threshold QC is present, this method performs
    /// STRUCTURAL validation only (>= 48 bytes for BLS12-381 G1 compressed). Full
    /// cryptographic BLS verification of the aggregate signature requires the
    /// `hints` crate and is done at a higher layer.
    pub fn is_valid(&self, known_keys: &[PublicKey]) -> bool {
        if let Some(ref qc) = self.threshold_qc {
            // ThresholdQC must be non-empty and at least BLS12-381 G1 size.
            // Full BLS verification is done at a higher layer; reject obviously
            // invalid (empty/truncated) QCs here.
            return qc.0.len() >= 48;
        }
        // A trust anchor requiring ZERO signatures is not a trust anchor: with
        // `threshold == 0`, `quorum_signatures.len() < 0` is never true and the final
        // `valid_count >= 0` is always true, so an EMPTY quorum over a prover-CHOSEN
        // `merkle_root` would "verify" — bypassing the committee entirely (a revocation /
        // admission / attested-root forgery). No legitimate attested root sets a zero
        // threshold (the committee-signed path always requires >= 1 signer; the
        // threshold_qc path is handled above + verified by the higher BLS/FROST layer).
        if self.threshold == 0 {
            return false;
        }
        if self.quorum_signatures.len() < self.threshold {
            return false;
        }
        let message = self.signing_message();
        let mut seen_signers: HashSet<[u8; 32]> = HashSet::new();
        let mut valid_count = 0usize;
        for (pubkey, sig) in &self.quorum_signatures {
            if !known_keys.contains(pubkey) {
                return false;
            }
            if !pubkey.verify(&message, sig) {
                return false;
            }
            // Only count unique signers toward the threshold.
            if seen_signers.insert(pubkey.0) {
                valid_count += 1;
            }
        }
        // Require that the number of UNIQUE valid signers meets the threshold.
        valid_count >= self.threshold
    }

    /// Alias for [`is_valid`](Self::is_valid) for API compatibility with the
    /// federation crate's previous local definition.
    pub fn is_valid_with_keys(&self, known_keys: &[PublicKey]) -> bool {
        self.is_valid(known_keys)
    }

    /// Compute the canonical message that quorum members sign.
    ///
    /// Each optional field is encoded with a tag byte prefix:
    /// - `0x00` for `None`
    /// - `0x01` followed by the 32-byte value for `Some`
    ///
    /// This ensures unambiguous encoding: `note_tree_root = Some(X), nullifier_set_root = None`
    /// produces a different message than `note_tree_root = None, nullifier_set_root = Some(X)`.
    pub fn signing_message(&self) -> Vec<u8> {
        let mut msg = Vec::new();
        // v6 (state anchor): `merkle_root` REMAINS `canonical_ledger_root` (a
        // BLAKE3 whole-image digest) because it is the RESTART ANCHOR — a node
        // reconstructs its ledger from the store and checks it against this
        // quorum-signed value, a role no per-cell algebraic commitment fills
        // (the whole-ledger 8-felt is the deferred `cells_root` Phase-E). What
        // moved is what `receipt_stream_root` now covers: the receipts it roots
        // carry the AIR-bound chip 8-felt state commitment
        // (`dregg_turn::state_commit`), not a trusted-Rust `Ledger::root()`. So
        // this quorum signature DOES certify the AIR-bound anchor — transitively,
        // through the receipt stream. The domain bump fences a v5 signature from
        // being read as a v6 claim.
        // v4 (issue #80) binds the receipt_stream_root so two federations
        // with identical ledger state but different receipt streams produce
        // different attestations.
        // v3 binds the federation_id into the preimage so a verifier
        // reconstructing the message can detect cross-federation attestation
        // swaps without consulting any out-of-band state (audit F2 applied to
        // attested roots).
        // v2 binds the blocklace block_id + finality_round so that two
        // attested roots at the same `height` from different blocklace forks
        // are distinguishable (closes audit F3).
        // v5 (N3 committee-restart fix): the wall-clock `timestamp` is DROPPED
        // from the signed preimage. Binding a per-node wall clock made the
        // preimage non-deterministic across the committee, so peers could never
        // produce matching signatures over the same finalized root (the blocker
        // that forced the committee-restart hole). The `timestamp` field is
        // retained on the struct for display/freshness heuristics but is no
        // longer consensus-bound. The domain bump v4->v5 fences the format: a v4
        // verifier reconstructing a v5 preimage fails the signature check, so all
        // committee members must upgrade together (a genesis/epoch boundary).
        msg.extend_from_slice(b"dregg-attested-root-v6");
        msg.extend_from_slice(&self.federation_id.0);
        msg.extend_from_slice(&self.merkle_root);
        match self.note_tree_root {
            Some(ref note_root) => {
                msg.push(0x01);
                msg.extend_from_slice(note_root);
            }
            None => {
                msg.push(0x00);
            }
        }
        match self.nullifier_set_root {
            Some(ref nullifier_root) => {
                msg.push(0x01);
                msg.extend_from_slice(nullifier_root);
            }
            None => {
                msg.push(0x00);
            }
        }
        msg.extend_from_slice(&self.height.to_le_bytes());
        // NOTE (v5): `timestamp` is intentionally NOT mixed in — see the domain
        // comment above. It stays a struct field but out of the signed preimage.
        match self.blocklace_block_id {
            Some(ref id) => {
                msg.push(0x01);
                msg.extend_from_slice(id);
            }
            None => {
                msg.push(0x00);
            }
        }
        match self.finality_round {
            Some(round) => {
                msg.push(0x01);
                msg.extend_from_slice(&round.to_le_bytes());
            }
            None => {
                msg.push(0x00);
            }
        }
        // v4 (#80): receipt_stream_root with 0x00 / 0x01||32-byte framing.
        // Legacy v3 roots carry None here and produce a `0x00` tag — the
        // verifier still sees a distinct v3-vs-v4 preimage because the
        // domain tag changed from v3 to v4. (A v3 verifier reconstructing
        // a v4 root's preimage with v3 tag fails signature check; that
        // is intentional: legacy verifiers MUST be upgraded to read v4.)
        match self.receipt_stream_root {
            Some(ref r) => {
                msg.push(0x01);
                msg.extend_from_slice(r);
            }
            None => {
                msg.push(0x00);
            }
        }
        msg
    }

    /// Verify that this attested root is valid AND recent enough.
    ///
    /// Combines cryptographic verification with a freshness check:
    /// - Negative timestamps are rejected (invalid state)
    /// - Signatures must be valid against `known_keys`
    /// - The root must not be older than `max_age_secs`
    /// - The root's timestamp must not be more than 60s in the future (clock skew tolerance)
    pub fn is_valid_at(&self, known_keys: &[PublicKey], now: u64, max_age_secs: u64) -> bool {
        // Reject negative timestamps: they are invalid and would wrap to huge
        // u64 values when cast, bypassing the staleness check.
        if self.timestamp < 0 {
            return false;
        }
        if !self.is_valid(known_keys) {
            return false;
        }
        let ts = self.timestamp as u64;
        if now > ts + max_age_secs {
            return false; // too old
        }
        if ts > now + 60 {
            return false; // clock skew tolerance
        }
        true
    }

    /// Short hex of the Merkle root for display.
    pub fn root_hex(&self) -> String {
        self.merkle_root[..4]
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect()
    }
}

impl fmt::Display for AttestedRoot {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.threshold_qc.is_some() {
            write!(
                f,
                "AttestedRoot(root={}, height={}, threshold_qc=yes, threshold={})",
                self.root_hex(),
                self.height,
                self.threshold
            )
        } else {
            write!(
                f,
                "AttestedRoot(root={}, height={}, sigs={}/{})",
                self.root_hex(),
                self.height,
                self.quorum_signatures.len(),
                self.threshold
            )
        }
    }
}

/// A revocation event submitted to consensus.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct RevocationEvent {
    /// The token ID being revoked.
    pub token_id: String,
    /// The revoking authority's public key.
    pub authority: PublicKey,
    /// Signature over the token_id by the revoking authority (64 bytes).
    pub signature: Signature,
}

/// Cell identity (32 bytes, derived from public key + domain).
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct CellId(pub [u8; 32]);

impl CellId {
    /// Derive a HYBRID CellId that cryptographically commits to BOTH the
    /// holder's ed25519 public key AND its ML-DSA public key
    /// ([`hybrid_id_commitment`]). This is the post-quantum identity: the
    /// enrolled ML-DSA key is a derivable function of the id, not an
    /// out-of-band roster entry.
    ///
    /// `ml_dsa_pk` is the serialized ML-DSA public-key bytes
    /// (`dregg_pq::MlDsaPublicKey.0`).
    pub fn derive_hybrid(ed25519_pk: &PublicKey, ml_dsa_pk: &[u8]) -> Self {
        CellId(hybrid_id_commitment(&ed25519_pk.0, ml_dsa_pk))
    }

    /// Raw-bytes variant of [`CellId::derive_hybrid`]: bind both keys given the
    /// ed25519 public key as a raw `[u8; 32]` (the shape the cell/agent model
    /// uses, cf. [`CellId::derive_raw`]).
    pub fn derive_hybrid_raw(ed25519_pk: &[u8; 32], ml_dsa_pk: &[u8]) -> Self {
        CellId(hybrid_id_commitment(ed25519_pk, ml_dsa_pk))
    }

    /// The cryptographic enroll+pin check for a hybrid CellId: is this id the
    /// commitment to `ed25519_pk` AND `ml_dsa_pk`? Rejects a self-supplied
    /// ML-DSA key that does not hash into the id. See [`verify_committed_ml_dsa`].
    pub fn verify_committed_ml_dsa(&self, ed25519_pk: &[u8; 32], ml_dsa_pk: &[u8]) -> bool {
        verify_committed_ml_dsa(&self.0, ed25519_pk, ml_dsa_pk)
    }

    /// Derive a CellId by hashing a public key and domain string.
    ///
    /// LEGACY (ed25519-only): this id does NOT commit to a post-quantum key.
    /// New identities on PQ-relevant surfaces should use
    /// [`CellId::derive_hybrid`] and be checked with
    /// [`CellId::verify_committed_ml_dsa`]. Retained so the tree compiles
    /// during the staged flag-day cutover.
    pub fn derive(pubkey: &PublicKey, domain: &str) -> Self {
        let hash = blake3::derive_key("dregg-cell-id-v1", &{
            let mut buf = Vec::with_capacity(32 + domain.len());
            buf.extend_from_slice(&pubkey.0);
            buf.extend_from_slice(domain.as_bytes());
            buf
        });
        CellId(hash)
    }

    /// Derive a CellId from raw byte arrays (public key + token domain bytes).
    ///
    /// Uses domain-separated BLAKE3. This is the derivation method used by the
    /// cell/agent model where both inputs are 32-byte arrays.
    ///
    /// LEGACY (ed25519-only): does not commit to a post-quantum key; prefer
    /// [`CellId::derive_hybrid_raw`] for PQ-relevant identities (staged cutover).
    pub fn derive_raw(public_key: &[u8; 32], token_id: &[u8; 32]) -> Self {
        let hash = blake3::derive_key("dregg-cell-id-v1", &{
            let mut buf = Vec::with_capacity(64);
            buf.extend_from_slice(public_key);
            buf.extend_from_slice(token_id);
            buf
        });
        CellId(hash)
    }

    /// Create from raw bytes.
    pub fn from_bytes(bytes: [u8; 32]) -> Self {
        CellId(bytes)
    }

    /// Get the underlying bytes.
    pub fn as_bytes(&self) -> &[u8; 32] {
        &self.0
    }

    /// The zero/null cell ID.
    pub const ZERO: CellId = CellId([0u8; 32]);
}

impl Default for CellId {
    fn default() -> Self {
        CellId::ZERO
    }
}

impl fmt::Debug for CellId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "CellId({})",
            self.0[..4]
                .iter()
                .map(|b| format!("{b:02x}"))
                .collect::<String>()
        )
    }
}

impl fmt::Display for CellId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            self.0[..8]
                .iter()
                .map(|b| format!("{b:02x}"))
                .collect::<String>()
        )
    }
}

// =============================================================================
// Hybrid post-quantum identity commitment
// =============================================================================
//
// The pre-quantum audit (2026-07-09) closed every load-bearing SIGNATURE surface
// to a hybrid `ed25519 ∧ ML-DSA-65`, but the identities those surfaces speak for
// (`CellId`, `FederationId`, the wire participant node-id) were ed25519-ONLY:
// they did not cryptographically commit to the ML-DSA key, so the PQ key had to
// be ENROLLED OUT-OF-BAND (a separate roster table, pinned by the caller). That
// left a gap — nothing in the identity itself forced a presented ML-DSA key to
// be the RIGHT one.
//
// The fix below makes the identity BE the enrollment: a hybrid id is the
// domain-separated BLAKE3 hash of BOTH public keys, so the ML-DSA key is a
// derivable function of the id, not a side table. A verifier recomputes the
// commitment from the two presented keys and REJECTS any ML-DSA key that does
// not hash into the claimed id (`verify_committed_ml_dsa`). This is the
// cryptographic enroll+pin.
//
// `dregg-types` deliberately takes NO post-quantum crypto dependency (no
// `fips204` / `dregg-pq`) — it hashes the ML-DSA public-key BYTES only. The
// ML-DSA key handling itself lives in `dregg-pq`; callers pass the serialized
// public key (`MlDsaPublicKey.0`, 1952 bytes for ML-DSA-65) as `ml_dsa_pk`.

/// Domain-separation context for the canonical hybrid identity commitment.
const HYBRID_ID_CONTEXT: &str = "dregg-hybrid-id-v1";

/// Compute the canonical hybrid-identity commitment binding an ed25519 public
/// key AND an ML-DSA public key into a single 32-byte identity.
///
/// `commit = BLAKE3_derive_key("dregg-hybrid-id-v1", ed25519_pk (32)
///           ‖ (ml_dsa_pk.len() as u32 LE) ‖ ml_dsa_pk)`.
///
/// The ed25519 key is fixed-width (32 bytes) and hashed first, and the ML-DSA
/// key is length-prefixed, so the encoding is injective in both keys: no pair
/// `(ed, ml)` collides with a different pair, and no hybrid id can collide with
/// the legacy ed25519-only [`CellId::derive`] / [`CellId::derive_raw`] domain
/// (a different context string).
///
/// `ml_dsa_pk` is the serialized ML-DSA public key bytes (from
/// `dregg_pq::MlDsaPublicKey`); `dregg-types` treats them as opaque bytes and
/// takes no PQ crypto dependency.
pub fn hybrid_id_commitment(ed25519_pk: &[u8; 32], ml_dsa_pk: &[u8]) -> [u8; 32] {
    let mut buf = Vec::with_capacity(32 + 4 + ml_dsa_pk.len());
    buf.extend_from_slice(ed25519_pk);
    buf.extend_from_slice(&(ml_dsa_pk.len() as u32).to_le_bytes());
    buf.extend_from_slice(ml_dsa_pk);
    blake3::derive_key(HYBRID_ID_CONTEXT, &buf)
}

/// The cryptographic enroll+pin check: does `id` commit to BOTH `ed25519_pk`
/// and `ml_dsa_pk`?
///
/// Recomputes [`hybrid_id_commitment`] from the two presented keys and returns
/// `true` iff it equals `id`. An attacker who presents the honest ed25519 key
/// but their OWN ML-DSA key gets a commitment that does not equal `id`, so this
/// returns `false` — the self-supplied PQ key is REJECTED. This is what lets a
/// surface replace out-of-band roster enrollment: the id IS the enrollment.
///
/// The comparison is over 32 hashed bytes (public commitments, not secrets);
/// a plain equality is appropriate.
pub fn verify_committed_ml_dsa(id: &[u8; 32], ed25519_pk: &[u8; 32], ml_dsa_pk: &[u8]) -> bool {
    hybrid_id_commitment(ed25519_pk, ml_dsa_pk) == *id
}

// =============================================================================
// Serde helpers for fixed-size byte arrays
// =============================================================================

mod serde_32 {
    use serde::{Deserialize, Deserializer, Serialize, Serializer};

    pub fn serialize<S: Serializer>(bytes: &[u8; 32], serializer: S) -> Result<S::Ok, S::Error> {
        bytes.as_ref().serialize(serializer)
    }

    pub fn deserialize<'de, D: Deserializer<'de>>(deserializer: D) -> Result<[u8; 32], D::Error> {
        let v: Vec<u8> = Deserialize::deserialize(deserializer)?;
        v.try_into()
            .map_err(|_| serde::de::Error::custom("expected 32 bytes"))
    }
}

mod serde_64 {
    use serde::{Deserialize, Deserializer, Serialize, Serializer};

    pub fn serialize<S: Serializer>(bytes: &[u8; 64], serializer: S) -> Result<S::Ok, S::Error> {
        bytes.as_ref().serialize(serializer)
    }

    pub fn deserialize<'de, D: Deserializer<'de>>(deserializer: D) -> Result<[u8; 64], D::Error> {
        let v: Vec<u8> = Deserialize::deserialize(deserializer)?;
        v.try_into()
            .map_err(|_| serde::de::Error::custom("expected 64 bytes"))
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pubkey_size() {
        assert_eq!(std::mem::size_of::<PublicKey>(), 32);
    }

    #[test]
    fn parse_hex32_round_trips_and_is_case_insensitive() {
        let bytes: [u8; 32] = core::array::from_fn(|i| i as u8);
        let hex = hex_encode(&bytes);
        assert_eq!(hex.len(), 64);
        assert_eq!(parse_hex32(&hex), Some(bytes));
        assert_eq!(parse_hex32(&hex.to_uppercase()), Some(bytes));
    }

    #[test]
    fn parse_hex32_rejects_bad_length_and_non_hex() {
        assert_eq!(parse_hex32(""), None);
        assert_eq!(parse_hex32(&"a".repeat(63)), None);
        assert_eq!(parse_hex32(&"a".repeat(65)), None);
        // 64 chars but a 'g' is not hex.
        assert_eq!(parse_hex32(&format!("g{}", "a".repeat(63))), None);
    }

    #[test]
    fn parse_hex32_multibyte_64_byte_id_returns_none_not_panic() {
        // 61 ASCII + one 2-byte char + 1 ASCII = 64 BYTES; the multibyte char
        // straddles the `i*2` grid so the OLD `&s[i*2..i*2+2]` would panic on a
        // mid-codepoint slice. The char-safe codec returns None instead.
        let id = format!("{}\u{00e9}b", "a".repeat(61));
        assert_eq!(id.len(), 64, "the adversarial id is 64 BYTES");
        assert!(id.chars().count() < 64, "…but fewer than 64 CHARS");
        assert_eq!(parse_hex32(&id), None);
    }

    #[test]
    fn signature_size() {
        assert_eq!(std::mem::size_of::<Signature>(), 64);
    }

    #[test]
    fn attested_root_has_quorum() {
        let root = AttestedRoot {
            merkle_root: [0xAB; 32],
            note_tree_root: None,
            nullifier_set_root: None,
            height: 42,
            timestamp: 1700000000,
            blocklace_block_id: None,
            finality_round: None,
            quorum_signatures: vec![
                (PublicKey([0x11; 32]), Signature([0x22; 64])),
                (PublicKey([0x33; 32]), Signature([0x44; 64])),
                (PublicKey([0x55; 32]), Signature([0x66; 64])),
            ],
            threshold_qc: None,
            threshold: 2,
            federation_id: FederationId::PLACEHOLDER,
            receipt_stream_root: None,
            hybrid_quorum: Vec::new(),
        };
        assert!(root.has_quorum()); // 3 sigs >= threshold 2

        let invalid = AttestedRoot {
            threshold: 5,
            ..root.clone()
        };
        assert!(!invalid.has_quorum()); // 3 sigs < threshold 5

        let with_qc = AttestedRoot {
            threshold_qc: Some(ThresholdQC(vec![0xFF; 48])),
            quorum_signatures: vec![],
            threshold: 100,
            ..root.clone()
        };
        assert!(with_qc.has_quorum()); // Valid QC (48 bytes = BLS12-381 G1 minimum)

        // Empty ThresholdQC must NOT bypass verification.
        let empty_qc = AttestedRoot {
            threshold_qc: Some(ThresholdQC(vec![])),
            quorum_signatures: vec![],
            threshold: 100,
            ..root.clone()
        };
        assert!(!empty_qc.has_quorum()); // Empty QC is rejected

        // Truncated ThresholdQC (< 48 bytes) must also fail.
        let truncated_qc = AttestedRoot {
            threshold_qc: Some(ThresholdQC(vec![0xFF; 10])),
            quorum_signatures: vec![],
            threshold: 100,
            ..root
        };
        assert!(!truncated_qc.has_quorum()); // Truncated QC is rejected
    }

    #[test]
    fn zero_threshold_empty_quorum_attested_root_is_refused() {
        // CLASS-1 sibling (the committee-gate residual): a forger sets threshold:0 +
        // an EMPTY quorum + a CHOSEN merkle_root + no threshold_qc. Before the guard,
        // is_valid returned true (zero sigs vacuously "meet" a zero threshold), so the
        // committee was never consulted — a revocation/admission/attested-root forgery.
        // It must be REFUSED against ANY committee. (A genuine 2-of-3 root still verifies
        // per attested_root_is_valid_verifies_signatures.)
        let (_sk1, pk1) = generate_keypair();
        let forged = AttestedRoot {
            merkle_root: [0x77; 32], // attacker-chosen (e.g. an empty revocation tree)
            note_tree_root: None,
            nullifier_set_root: None,
            height: 1,
            timestamp: 1700000000,
            blocklace_block_id: None,
            finality_round: None,
            quorum_signatures: vec![], // NO signatures
            threshold_qc: None,
            threshold: 0, // requires ZERO signers
            federation_id: FederationId::PLACEHOLDER,
            receipt_stream_root: None,
            hybrid_quorum: Vec::new(),
        };
        assert!(
            !forged.is_valid(&[pk1]),
            "zero-threshold root must be refused"
        );
        assert!(
            !forged.is_valid(&[]),
            "zero-threshold root must be refused (empty committee)"
        );
    }

    #[test]
    fn attested_root_is_valid_verifies_signatures() {
        // Generate real keypairs.
        let (sk1, pk1) = generate_keypair();
        let (sk2, pk2) = generate_keypair();
        let (_sk3, pk3) = generate_keypair();

        let mut root = AttestedRoot {
            merkle_root: [0xAB; 32],
            note_tree_root: None,
            nullifier_set_root: None,
            height: 42,
            timestamp: 1700000000,
            blocklace_block_id: None,
            finality_round: None,
            quorum_signatures: vec![],
            threshold_qc: None,
            threshold: 2,
            federation_id: FederationId::PLACEHOLDER,
            receipt_stream_root: None,
            hybrid_quorum: Vec::new(),
        };

        // Sign with real keys.
        let message = root.signing_message();
        let sig1 = sign(&sk1, &message);
        let sig2 = sign(&sk2, &message);
        root.quorum_signatures = vec![(pk1, sig1), (pk2, sig2)];

        // Valid: both signers are in known_keys and signatures are correct.
        let known_keys = vec![
            root.quorum_signatures[0].0,
            root.quorum_signatures[1].0,
            pk3,
        ];
        assert!(root.is_valid(&known_keys));

        // Invalid: signer not in known_keys.
        let partial_keys = vec![root.quorum_signatures[0].0];
        assert!(!root.is_valid(&partial_keys));

        // Invalid: tampered signature.
        let mut tampered = root.clone();
        tampered.quorum_signatures[0].1 = Signature([0xFF; 64]);
        assert!(!tampered.is_valid(&known_keys));
    }

    #[test]
    fn postcard_roundtrip_attested_root() {
        let root = AttestedRoot {
            merkle_root: [0x01; 32],
            note_tree_root: Some([0x02; 32]),
            nullifier_set_root: Some([0x03; 32]),
            height: 99,
            timestamp: 1700000000,
            blocklace_block_id: Some([0x04; 32]),
            finality_round: Some(7),
            quorum_signatures: vec![(PublicKey([0xAA; 32]), Signature([0xBB; 64]))],
            threshold_qc: None,
            threshold: 1,
            federation_id: FederationId::PLACEHOLDER,
            receipt_stream_root: Some([0x05; 32]),
            hybrid_quorum: Vec::new(),
        };
        let bytes = postcard::to_stdvec(&root).unwrap();
        let decoded: AttestedRoot = postcard::from_bytes(&bytes).unwrap();
        assert_eq!(root, decoded);
    }

    // -------------------------------------------------------------------
    // Issue #80 adversarial tests: receipt_stream_root
    // -------------------------------------------------------------------

    /// Constructor for tests: builds a v4 root with the given receipt
    /// stream root pre-computed.
    fn root_with_receipts(merkle: [u8; 32], receipts: &[[u8; 32]]) -> AttestedRoot {
        AttestedRoot {
            merkle_root: merkle,
            note_tree_root: None,
            nullifier_set_root: None,
            height: 1,
            timestamp: 1_700_000_000,
            blocklace_block_id: Some([0xAA; 32]),
            finality_round: Some(1),
            quorum_signatures: vec![],
            threshold_qc: None,
            threshold: 1,
            federation_id: FederationId::PLACEHOLDER,
            receipt_stream_root: Some(merkle_root_of_receipt_hashes(receipts)),
            hybrid_quorum: Vec::new(),
        }
    }

    #[test]
    fn receipt_stream_root_empty_is_zero() {
        // Empty input → all-zero canonical sentinel.
        assert_eq!(merkle_root_of_receipt_hashes(&[]), [0u8; 32]);
    }

    #[test]
    fn receipt_stream_root_single_leaf_distinct_from_hash() {
        // One-element tree's root must NOT equal the bare leaf — the
        // domain tag commits to "set with one element" vs the lone hash.
        let h = [0x11u8; 32];
        let root = merkle_root_of_receipt_hashes(&[h]);
        assert_ne!(root, h);
        assert_ne!(root, [0u8; 32]);
    }

    #[test]
    fn receipt_stream_root_order_sensitive() {
        // Reordering receipts MUST change the root.
        let a = [0x11u8; 32];
        let b = [0x22u8; 32];
        let r1 = merkle_root_of_receipt_hashes(&[a, b]);
        let r2 = merkle_root_of_receipt_hashes(&[b, a]);
        assert_ne!(r1, r2);
    }

    #[test]
    fn receipt_stream_root_disjoint_streams_diverge() {
        // **The core #80 adversarial test.** Two AttestedRoots with the
        // SAME ledger merkle_root but DIFFERENT receipt streams MUST
        // produce different `receipt_stream_root` values.
        let same_ledger = [0xDE; 32];

        let stream_a = vec![[0x01u8; 32], [0x02u8; 32], [0x03u8; 32]];
        let stream_b = vec![[0xF1u8; 32], [0xF2u8; 32], [0xF3u8; 32]];

        let root_a = root_with_receipts(same_ledger, &stream_a);
        let root_b = root_with_receipts(same_ledger, &stream_b);

        // Same ledger commitment...
        assert_eq!(root_a.merkle_root, root_b.merkle_root);
        // ...but DIFFERENT receipt stream commitment.
        assert_ne!(root_a.receipt_stream_root, root_b.receipt_stream_root);
        assert!(root_a.is_v4_receipt_complete());
        assert!(root_b.is_v4_receipt_complete());

        // The signing-message preimage MUST also diverge: a verifier
        // reconstructing the v4 message would catch the swap even if
        // the ledger root looked identical.
        assert_ne!(root_a.signing_message(), root_b.signing_message());
    }

    #[test]
    fn receipt_stream_root_disjoint_streams_subset_diverge() {
        // Subset attack: federation A claims [r1, r2, r3], B claims [r1, r2].
        // Same ledger merkle_root; receipt stream MUST diverge.
        let same_ledger = [0xCA; 32];
        let stream_full = vec![[0x11u8; 32], [0x22u8; 32], [0x33u8; 32]];
        let stream_subset = vec![[0x11u8; 32], [0x22u8; 32]];

        let root_full = root_with_receipts(same_ledger, &stream_full);
        let root_subset = root_with_receipts(same_ledger, &stream_subset);

        assert_eq!(root_full.merkle_root, root_subset.merkle_root);
        assert_ne!(
            root_full.receipt_stream_root,
            root_subset.receipt_stream_root
        );
    }

    #[test]
    fn verify_receipt_stream_round_trip() {
        let stream = vec![[0x01u8; 32], [0x02u8; 32], [0x03u8; 32]];
        let root = root_with_receipts([0xDE; 32], &stream);
        assert!(root.verify_receipt_stream(&stream));
        // Tampering with one receipt hash must be rejected.
        let mut tampered = stream.clone();
        tampered[1][0] ^= 0xFF;
        assert!(!root.verify_receipt_stream(&tampered));
        // Reordering must be rejected.
        let mut reordered = stream.clone();
        reordered.swap(0, 2);
        assert!(!root.verify_receipt_stream(&reordered));
        // Truncation must be rejected.
        assert!(!root.verify_receipt_stream(&stream[..2]));
    }

    #[test]
    fn verify_receipt_stream_rejects_legacy_root() {
        // A v3-legacy root (receipt_stream_root: None) must NOT verify
        // any claimed receipt set — even the empty one. Callers that
        // wish to accept legacy roots' bare ledger attestation must
        // gate on `is_v4_receipt_complete` themselves.
        let legacy = AttestedRoot::new_legacy([0xAB; 32], 1, 0, vec![], None, 1);
        assert!(!legacy.is_v4_receipt_complete());
        assert!(!legacy.verify_receipt_stream(&[]));
        assert!(!legacy.verify_receipt_stream(&[[0u8; 32]]));
    }

    #[test]
    fn v5_signing_message_distinct_from_legacy_preimage() {
        // Bumping the domain tag to v5 means a v5 root's signing message starts
        // with "dregg-attested-root-v6" — a v5 verifier reconstructing the
        // preimage with the v4 tag (and mixing the now-dropped timestamp) would
        // fail the signature check, so legacy verifiers MUST be upgraded.
        let v5_root = root_with_receipts([0xCC; 32], &[[0x99; 32]]);
        let msg = v5_root.signing_message();
        assert!(msg.starts_with(b"dregg-attested-root-v6"));
        // The receipt_stream_root tag (0x01) precedes the 32-byte hash
        // at the end of the preimage.
        assert_eq!(msg[msg.len() - 33], 0x01u8);
    }

    #[test]
    fn v5_preimage_is_timestamp_independent() {
        // The N3 determinism prerequisite: two attested roots that agree on
        // everything EXCEPT the wall-clock timestamp produce the IDENTICAL
        // signed preimage, so committee members with skewed clocks sign matching
        // bytes over the same finalized state.
        let a = root_with_receipts([0x42; 32], &[[0x01; 32]]);
        let mut b = a.clone();
        b.timestamp = a.timestamp + 9_999;
        assert_eq!(
            a.signing_message(),
            b.signing_message(),
            "timestamp must not affect the v5 signed preimage"
        );
    }

    #[test]
    fn finalization_vote_message_binds_block_and_root() {
        // The shared finalization-vote preimage binds both the block id and the
        // finalized merkle_root: flipping either yields a different message.
        let base = finalization_vote_signing_message(&[0x11; 32], &[0x22; 32]);
        assert!(base.starts_with(FINALIZATION_VOTE_DOMAIN_V3));
        assert_ne!(
            base,
            finalization_vote_signing_message(&[0x11; 32], &[0x23; 32]),
            "a different merkle_root must change the vote preimage"
        );
        assert_ne!(
            base,
            finalization_vote_signing_message(&[0x10; 32], &[0x22; 32]),
            "a different block_id must change the vote preimage"
        );
    }

    #[test]
    fn adversarial_same_ledger_different_receipts_signed_swap_detected() {
        // Full Ed25519-signed scenario for #80:
        //   1. Federation produces v4 root over (ledger=L, receipts=[a,b]).
        //   2. Adversary swaps the receipt stream to [a,b'] but keeps the
        //      old signature.
        //   3. Verifier reconstructs the v4 signing message; signature
        //      check fails because `receipt_stream_root` changed.
        let (sk, pk) = generate_keypair();

        let ledger = [0xAB; 32];
        let receipts_honest = vec![[0x01u8; 32], [0x02u8; 32]];
        let mut root = root_with_receipts(ledger, &receipts_honest);
        root.threshold = 1;
        let msg = root.signing_message();
        let sig = sign(&sk, &msg);
        root.quorum_signatures = vec![(pk, sig)];
        assert!(root.is_valid(&[pk]));

        // Adversary: tamper the receipt_stream_root field but keep the
        // old signature.
        let mut tampered = root.clone();
        let receipts_evil = vec![[0x01u8; 32], [0xEEu8; 32]];
        tampered.receipt_stream_root = Some(merkle_root_of_receipt_hashes(&receipts_evil));
        // Signature check MUST reject — the signed v4 preimage no longer
        // matches the reconstructed one.
        assert!(!tampered.is_valid(&[pk]));
    }

    #[test]
    fn postcard_roundtrip_revocation_event() {
        let event = RevocationEvent {
            token_id: "tok-abc".to_string(),
            authority: PublicKey([0x42; 32]),
            signature: Signature([0x77; 64]),
        };
        let bytes = postcard::to_stdvec(&event).unwrap();
        let decoded: RevocationEvent = postcard::from_bytes(&bytes).unwrap();
        assert_eq!(event, decoded);
    }

    #[test]
    fn cell_id_derive_deterministic() {
        let pk = PublicKey([0x42; 32]);
        let id1 = CellId::derive(&pk, "example.com");
        let id2 = CellId::derive(&pk, "example.com");
        assert_eq!(id1, id2);

        let id3 = CellId::derive(&pk, "other.com");
        assert_ne!(id1, id3);
    }

    #[test]
    fn cell_id_derive_raw_deterministic() {
        let pk = [0x42u8; 32];
        let token = [0x99u8; 32];
        let id1 = CellId::derive_raw(&pk, &token);
        let id2 = CellId::derive_raw(&pk, &token);
        assert_eq!(id1, id2);

        let other_token = [0xAA; 32];
        let id3 = CellId::derive_raw(&pk, &other_token);
        assert_ne!(id1, id3);
    }

    #[test]
    fn sign_and_verify() {
        let (sk, pk) = generate_keypair();
        let message = b"hello world";
        let sig = sign(&sk, message);
        assert!(pk.verify(message, &sig));
        assert!(!pk.verify(b"wrong message", &sig));
    }

    // ── Hybrid identity commitment ──────────────────────────────────────────

    #[test]
    fn hybrid_id_commitment_deterministic_and_binds_both_keys() {
        let ed = [0x11u8; 32];
        // ML-DSA-65 public keys are 1952 bytes; the length is irrelevant to the
        // commitment (it hashes the bytes) but use a realistic width.
        let ml = vec![0x22u8; 1952];

        // Deterministic in both keys.
        assert_eq!(
            hybrid_id_commitment(&ed, &ml),
            hybrid_id_commitment(&ed, &ml)
        );

        // Changing EITHER key changes the id.
        let ed2 = [0x33u8; 32];
        assert_ne!(
            hybrid_id_commitment(&ed, &ml),
            hybrid_id_commitment(&ed2, &ml)
        );
        let mut ml2 = ml.clone();
        ml2[0] ^= 0xFF;
        assert_ne!(
            hybrid_id_commitment(&ed, &ml),
            hybrid_id_commitment(&ed, &ml2)
        );

        // A hybrid id never collides with the legacy ed25519-only derivations
        // (distinct domain-separation contexts).
        let legacy_raw = CellId::derive_raw(&ed, &[0u8; 32]);
        assert_ne!(legacy_raw.0, hybrid_id_commitment(&ed, &[0u8; 32]));
    }

    #[test]
    fn adversarial_committed_ml_dsa_rejects_attacker_key() {
        // Honest holder: hybrid id H(P_ed ‖ P_ml).
        let p_ed = [0x42u8; 32];
        let p_ml = vec![0xA5u8; 1952];
        let id = CellId::derive_hybrid_raw(&p_ed, &p_ml);

        // The honest (P_ed, P_ml) passes the enroll+pin check.
        assert!(id.verify_committed_ml_dsa(&p_ed, &p_ml));
        assert!(verify_committed_ml_dsa(id.as_bytes(), &p_ed, &p_ml));

        // ATTACKER presents the honest ed25519 key but their OWN ML-DSA key
        // (a valid ML-DSA keypair they control). It does NOT hash into the id,
        // so the commitment check REJECTS it — the self-carried PQ key cannot
        // impersonate the enrolled one.
        let mut attacker_ml = p_ml.clone();
        attacker_ml[0] ^= 0xFF; // a different (attacker-owned) ML-DSA public key
        assert!(!id.verify_committed_ml_dsa(&p_ed, &attacker_ml));
        assert!(!verify_committed_ml_dsa(id.as_bytes(), &p_ed, &attacker_ml));

        // An attacker who also swaps the ed25519 key is likewise rejected.
        let attacker_ed = [0x99u8; 32];
        assert!(!id.verify_committed_ml_dsa(&attacker_ed, &p_ml));

        // FederationId shares the same primitive: same adversarial guarantee.
        let fed = FederationId::derive_hybrid(&p_ed, &p_ml);
        assert!(fed.verify_committed_ml_dsa(&p_ed, &p_ml));
        assert!(!fed.verify_committed_ml_dsa(&p_ed, &attacker_ml));
    }

    #[test]
    fn legacy_ed25519_only_id_is_not_a_hybrid_commitment() {
        // The staged flag-day path: a legacy ed25519-only id must NOT pass the
        // hybrid enroll+pin check for any presented ML-DSA key — it never
        // committed to one. Surfaces distinguish legacy from hybrid ids by
        // whether `verify_committed_ml_dsa` holds.
        let pk = PublicKey([0x42; 32]);
        let legacy = CellId::derive(&pk, "example.com");
        let some_ml = vec![0x01u8; 1952];
        assert!(!legacy.verify_committed_ml_dsa(&pk.0, &some_ml));
    }
}
