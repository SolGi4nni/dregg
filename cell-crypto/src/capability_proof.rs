//! Proof-carrying capability exercise for sovereign cells.
//!
//! This module enables peer-to-peer capability exercise without federation mediation.
//! Alice holds a capability to Bob's cell; she proves she holds it and sends the proof
//! along with the requested effect directly to Bob. Bob verifies locally and executes.
//!
//! Protocol:
//! 1. Alice proves: "my state contains a capability with these permissions for Bob's cell"
//! 2. Alice sends Bob: (her proof, the requested effect)
//! 3. Bob verifies: proof shows Alice holds a valid cap, effect is within permissions
//! 4. Bob executes the effect on his own cell
//!
//! The `SignedAttestation` variant is the initial implementation (both parties
//! online). A future ZK variant (where the holder doesn't reveal the slot) is
//! tracked in the slot-caveats design; it is intentionally **not** carried as
//! a typed placeholder here, because the prior `StarkMembership` variant had
//! no real verification path — `verify(...)` accepted it on signature alone,
//! which is an authority-amplification hazard. The variant has been removed.
//! When the swiss-table membership gadget lands, reintroduce the variant
//! alongside a working verification path in the same patch.

use serde::{Deserialize, Serialize};

use dregg_cell::id::CellId;
use dregg_cell::permissions::AuthRequired;
use dregg_cell::state::FieldElement;

/// Serde helper for `[u8; 64]` (Ed25519 signatures).
mod sig_serde {
    use serde::{Deserialize, Deserializer, Serialize, Serializer};

    pub fn serialize<S: Serializer>(bytes: &[u8; 64], ser: S) -> Result<S::Ok, S::Error> {
        bytes.as_slice().serialize(ser)
    }

    pub fn deserialize<'de, D: Deserializer<'de>>(de: D) -> Result<[u8; 64], D::Error> {
        let v: Vec<u8> = Vec::deserialize(de)?;
        v.try_into()
            .map_err(|_| serde::de::Error::custom("expected 64 bytes for signature"))
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Core types
// ─────────────────────────────────────────────────────────────────────────────

/// A proof that an agent holds a specific capability (for peer-to-peer exercise).
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CapabilityProof {
    /// The holder's cell ID.
    pub holder_cell: CellId,
    /// The holder's current state commitment.
    pub holder_commitment: [u8; 32],
    /// The target cell this capability is for.
    pub target_cell: CellId,
    /// The permissions level of the capability.
    pub permissions: AuthRequired,
    /// Proof that this capability exists in the holder's state.
    /// (For now: signed attestation. Future: STARK Merkle membership proof)
    pub proof_data: CapabilityProofData,
    /// Timestamp (freshness, unix seconds).
    pub timestamp: i64,
    /// Classical signature from the holder over the whole thing (Ed25519, 64 bytes).
    #[serde(with = "sig_serde")]
    pub signature: [u8; 64],
    /// POST-QUANTUM half of the HYBRID authenticator: an ML-DSA-65 (FIPS 204)
    /// signature over the SAME canonical [`Self::signing_message`] the ed25519
    /// half covers. The holder derives the ML-DSA key DETERMINISTICALLY from the
    /// same ed25519 seed ([`MlDsaCapKey::from_ed25519_seed`]), so a forger must
    /// break ed25519 discrete-log AND module-lattice SIS/LWE simultaneously.
    ///
    /// `None` is treated as a missing half and fails CLOSED at [`Self::verify`].
    #[serde(default)]
    pub pq_signature: Option<Vec<u8>>,
    /// The holder's serialized ML-DSA-65 public key, self-carried in the proof.
    ///
    /// This is SAFE to self-carry because the verifier does NOT trust it on its
    /// own: [`Self::verify`] first checks that the holder's IDENTITY commits to
    /// it — [`CellId::verify_committed_ml_dsa`] recomputes `H("dregg-hybrid-id-v1",
    /// P_ed ‖ P_ml)` and equality-checks [`Self::holder_cell`]. A key that does
    /// not hash into the holder's CellId is REJECTED, so the CellId itself is the
    /// enrollment (replacing the out-of-band roster). An attacker who forges the
    /// ed25519 half and presents their OWN ML-DSA key is rejected because that
    /// key is not committed by the holder's identity.
    ///
    /// `None` is a missing half and fails CLOSED at [`Self::verify`].
    #[serde(default)]
    pub holder_ml_dsa_pubkey: Option<Vec<u8>>,
}

/// How the holder proves capability membership.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum CapabilityProofData {
    /// Signed attestation (simple, no ZK -- holder signs "I have cap X").
    /// Sufficient for peer-to-peer where both parties are online.
    SignedAttestation {
        /// Which slot in the holder's c-list contains the capability.
        capability_slot: u32,
        /// Optional expiry height of the capability itself.
        expires_at: Option<u64>,
    },
    // Note: a `StarkMembership` variant previously existed here as a typed
    // placeholder, but `verify(...)` had no path to actually check it,
    // which meant any caller using `StarkMembership` was admitted on
    // signature alone — an authority-amplification hazard. Removed
    // pending a real swiss-table-membership gadget; see module doc.
}

// ─────────────────────────────────────────────────────────────────────────────
// Peer effects (subset of Effect exercisable via capability)
// ─────────────────────────────────────────────────────────────────────────────

/// An effect that can be requested via peer-to-peer capability exercise.
///
/// This is a restricted subset of the full `Effect` enum (which lives in `dregg-turn`).
/// Only effects that make sense for a remote capability holder to request on a target
/// cell are included here.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum PeerEffect {
    /// Set a state field on the target cell.
    SetField { index: u64, value: FieldElement },
    /// Transfer computrons from the target cell to the holder.
    Transfer { amount: u64 },
    /// Increment the target cell's nonce.
    IncrementNonce,
    /// Emit an event from the target cell.
    EmitEvent {
        topic: FieldElement,
        data: Vec<FieldElement>,
    },
}

impl PeerEffect {
    /// What action type does this effect require on the target cell?
    pub fn required_action(&self) -> dregg_cell::permissions::Action {
        match self {
            PeerEffect::SetField { .. } => dregg_cell::permissions::Action::SetState,
            PeerEffect::Transfer { .. } => dregg_cell::permissions::Action::Send,
            PeerEffect::IncrementNonce => dregg_cell::permissions::Action::IncrementNonce,
            PeerEffect::EmitEvent { .. } => dregg_cell::permissions::Action::Access,
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Request / Response
// ─────────────────────────────────────────────────────────────────────────────

/// Request to exercise a capability (sent from holder to target).
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CapabilityExerciseRequest {
    /// The proof that the holder possesses this capability.
    pub capability_proof: CapabilityProof,
    /// The effects the holder wants to perform on the target cell.
    pub requested_effects: Vec<PeerEffect>,
}

/// Response from the target after processing an exercise request.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CapabilityExerciseResponse {
    /// Whether the exercise was accepted.
    pub accepted: bool,
    /// The target's new state commitment (if accepted).
    pub new_target_commitment: Option<[u8; 32]>,
    /// Error description (if rejected).
    pub error: Option<String>,
}

// ─────────────────────────────────────────────────────────────────────────────
// Errors
// ─────────────────────────────────────────────────────────────────────────────

/// Errors that can occur during capability proof verification.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CapabilityProofError {
    /// The classical (Ed25519) signature over the proof is invalid.
    InvalidSignature,
    /// The post-quantum (ML-DSA-65) half is absent — a HYBRID proof MUST carry
    /// both halves, so a missing PQ half fails CLOSED.
    MissingPqSignature,
    /// The proof does not carry the holder's ML-DSA-65 public key — the hybrid
    /// PQ half is incomplete, so it fails CLOSED.
    MissingPqPublicKey,
    /// The holder's CellId does not COMMIT to the presented ML-DSA-65 public key
    /// (`H("dregg-hybrid-id-v1", P_ed ‖ P_ml) != holder_cell`). The key was not
    /// enrolled by the holder's identity — e.g. an attacker who forged the
    /// ed25519 half and self-supplied their own ML-DSA key, or a legacy
    /// ed25519-only CellId that commits to no ML-DSA key at all.
    IdentityCommitmentMismatch,
    /// The post-quantum (ML-DSA-65) half does not verify against the holder's
    /// id-committed ML-DSA key (e.g. it was signed under an attacker's key).
    InvalidPqSignature,
    /// The holder_commitment doesn't match our last-known view of the holder's state.
    CommitmentMismatch { expected: [u8; 32], got: [u8; 32] },
    /// The capability's permissions are insufficient for the requested effects.
    InsufficientPermissions {
        held: AuthRequired,
        required: AuthRequired,
    },
    /// The proof timestamp is too old (exceeds freshness window).
    StaleTimestamp {
        proof_timestamp: i64,
        current_timestamp: i64,
        max_age_seconds: i64,
    },
    /// The capability has expired (past its expiry height).
    CapabilityExpired {
        expires_at: u64,
        current_height: u64,
    },
    /// The target_cell in the proof doesn't match our cell ID.
    WrongTarget { expected: CellId, got: CellId },
}

impl std::fmt::Display for CapabilityProofError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidSignature => write!(f, "invalid ed25519 signature on capability proof"),
            Self::MissingPqSignature => {
                write!(
                    f,
                    "capability proof is missing its ML-DSA-65 (post-quantum) signature half"
                )
            }
            Self::MissingPqPublicKey => {
                write!(
                    f,
                    "capability proof is missing the holder's ML-DSA-65 public key"
                )
            }
            Self::IdentityCommitmentMismatch => write!(
                f,
                "holder CellId does not commit to the presented ML-DSA-65 public key \
                 (the key was not enrolled by the holder's identity)"
            ),
            Self::InvalidPqSignature => write!(
                f,
                "ML-DSA-65 half does not verify against the holder's id-committed post-quantum key"
            ),
            Self::CommitmentMismatch { .. } => {
                write!(f, "holder commitment does not match expected state")
            }
            Self::InsufficientPermissions { held, required } => {
                write!(
                    f,
                    "capability permissions {:?} insufficient for required {:?}",
                    held, required
                )
            }
            Self::StaleTimestamp {
                proof_timestamp,
                current_timestamp,
                max_age_seconds,
            } => write!(
                f,
                "proof timestamp {} is stale (current: {}, max age: {}s)",
                proof_timestamp, current_timestamp, max_age_seconds
            ),
            Self::CapabilityExpired {
                expires_at,
                current_height,
            } => write!(
                f,
                "capability expired at height {} (current: {})",
                expires_at, current_height
            ),
            Self::WrongTarget { expected, got } => {
                write!(f, "proof targets {:?} but we are {:?}", got, expected)
            }
        }
    }
}

impl std::error::Error for CapabilityProofError {}

// ─────────────────────────────────────────────────────────────────────────────
// Verification context (Bob's side)
// ─────────────────────────────────────────────────────────────────────────────

/// Parameters for verifying a capability proof (Bob's view).
pub struct VerificationContext {
    /// Our own cell ID (the target).
    pub our_cell_id: CellId,
    /// Our current view of the holder's state commitment (from PeerCellView or last sync).
    pub expected_holder_commitment: [u8; 32],
    /// Current unix timestamp (for freshness check).
    pub current_timestamp: i64,
    /// Maximum age of a proof in seconds before it's considered stale.
    pub max_proof_age_seconds: i64,
    /// Current block height (for capability expiry check).
    pub current_height: u64,
}

// ─────────────────────────────────────────────────────────────────────────────
// Implementation
// ─────────────────────────────────────────────────────────────────────────────

impl CapabilityProof {
    /// Compute the signing message for this proof (everything except the signature itself).
    pub fn signing_message(&self) -> Vec<u8> {
        let mut msg = Vec::with_capacity(256);
        msg.extend_from_slice(b"dregg-cap-proof-v1:");
        msg.extend_from_slice(self.holder_cell.as_bytes());
        msg.extend_from_slice(&self.holder_commitment);
        msg.extend_from_slice(self.target_cell.as_bytes());
        // Encode permissions as discriminant byte (plus vk_hash when Custom).
        // The signing message must distinguish `Custom { vk_hash: A }` from
        // `Custom { vk_hash: B }` so that two proofs over different
        // app-defined auth modes never collide.
        msg.push(auth_required_discriminant(&self.permissions));
        if let AuthRequired::Custom { vk_hash } = &self.permissions {
            msg.extend_from_slice(vk_hash);
        }
        // Encode proof_data. (StarkMembership variant was removed per
        // module-doc note above; SignedAttestation is currently the only
        // shape.)
        let CapabilityProofData::SignedAttestation {
            capability_slot,
            expires_at,
        } = &self.proof_data;
        msg.push(0u8); // variant discriminant
        msg.extend_from_slice(&capability_slot.to_le_bytes());
        match expires_at {
            Some(exp) => {
                msg.push(1u8);
                msg.extend_from_slice(&exp.to_le_bytes());
            }
            None => msg.push(0u8),
        }
        // Timestamp.
        msg.extend_from_slice(&self.timestamp.to_le_bytes());
        msg
    }

    /// Verify this capability proof from the target's perspective.
    ///
    /// Checks:
    /// 1. Target cell matches us
    /// 2. Holder commitment matches our last-known view
    /// 3. Timestamp freshness
    /// 4. Capability expiry (if applicable)
    /// 5. HYBRID authenticator: the classical Ed25519 half AND the post-quantum
    ///    ML-DSA-65 half both verify over the same canonical message
    ///    (`ed25519 ∧ ML-DSA`). The PQ half is checked against the ML-DSA key
    ///    the holder self-carries in the proof — but ONLY after the holder's
    ///    IDENTITY is shown to commit to it: `holder_cell.verify_committed_ml_dsa
    ///    (holder_pubkey, presented_ml)` recomputes `H("dregg-hybrid-id-v1",
    ///    P_ed ‖ P_ml)` and equality-checks the CellId. The CellId is thus the
    ///    enrollment (replacing the out-of-band roster): a self-supplied key not
    ///    committed by the identity is rejected.
    ///
    /// `holder_pubkey` is the holder's ed25519 public key (the caller-pinned
    /// classical identity anchor; it is also bound into the id-commitment). A
    /// missing PQ half, a key not committed by the CellId, or an attacker-signed
    /// PQ half all fail CLOSED.
    pub fn verify(
        &self,
        holder_pubkey: &[u8; 32],
        ctx: &VerificationContext,
    ) -> Result<(), CapabilityProofError> {
        // 1. Verify the target is us.
        if self.target_cell != ctx.our_cell_id {
            return Err(CapabilityProofError::WrongTarget {
                expected: ctx.our_cell_id,
                got: self.target_cell,
            });
        }

        // 2. Check holder_commitment matches expected (our last-known view).
        if self.holder_commitment != ctx.expected_holder_commitment {
            return Err(CapabilityProofError::CommitmentMismatch {
                expected: ctx.expected_holder_commitment,
                got: self.holder_commitment,
            });
        }

        // 3. Check timestamp freshness.
        let age = ctx.current_timestamp - self.timestamp;
        if age > ctx.max_proof_age_seconds || age < -ctx.max_proof_age_seconds {
            return Err(CapabilityProofError::StaleTimestamp {
                proof_timestamp: self.timestamp,
                current_timestamp: ctx.current_timestamp,
                max_age_seconds: ctx.max_proof_age_seconds,
            });
        }

        // 4. Check capability expiry.
        let CapabilityProofData::SignedAttestation { expires_at, .. } = &self.proof_data;
        if let Some(exp) = expires_at
            && ctx.current_height > *exp
        {
            return Err(CapabilityProofError::CapabilityExpired {
                expires_at: *exp,
                current_height: ctx.current_height,
            });
        }

        // 5. Verify the HYBRID authenticator over the canonical message. BOTH
        //    halves must check (`ed25519 ∧ ML-DSA`).
        let msg = self.signing_message();

        // 5a. Classical Ed25519 half.
        if !verify_ed25519(holder_pubkey, &msg, &self.signature) {
            return Err(CapabilityProofError::InvalidSignature);
        }

        // 5b. Post-quantum ML-DSA-65 half. The holder self-carries their ML-DSA
        //     public key, but we do NOT trust it on its own: first require the
        //     holder's IDENTITY to commit to it. `holder_cell.verify_committed_
        //     ml_dsa` recomputes `H("dregg-hybrid-id-v1", P_ed ‖ P_ml)` and
        //     equality-checks the CellId, so the CellId is the enrollment
        //     (replacing the out-of-band roster). An attacker who forges the
        //     ed25519 half and self-supplies their OWN ML-DSA key is rejected
        //     here because that key does not hash into the holder's CellId; a
        //     legacy ed25519-only CellId (which commits to no ML-DSA key) also
        //     fails CLOSED.
        let Some(presented_ml_dsa_pk) = &self.holder_ml_dsa_pubkey else {
            return Err(CapabilityProofError::MissingPqPublicKey);
        };
        if !self
            .holder_cell
            .verify_committed_ml_dsa(holder_pubkey, presented_ml_dsa_pk)
        {
            return Err(CapabilityProofError::IdentityCommitmentMismatch);
        }
        // Only now that the identity commits to it do we trust the presented key
        // to check the PQ signature. Fail CLOSED on a missing or invalid half.
        let Some(pq_sig) = &self.pq_signature else {
            return Err(CapabilityProofError::MissingPqSignature);
        };
        if !ml_dsa_cap_verify(presented_ml_dsa_pk, &msg, pq_sig) {
            return Err(CapabilityProofError::InvalidPqSignature);
        }

        Ok(())
    }

    /// Check whether this proof's permissions are sufficient for the given effects.
    ///
    /// The capability's `permissions` level must satisfy the target cell's requirement
    /// for each effect type. For peer-to-peer exercise, we check that the cap's auth
    /// level is at least as permissive as what the target requires for each action.
    pub fn check_permissions_for_effects(
        &self,
        effects: &[PeerEffect],
        target_permissions: &dregg_cell::permissions::Permissions,
    ) -> Result<(), CapabilityProofError> {
        for effect in effects {
            let action = effect.required_action();
            let required = target_permissions.for_action(action);
            // The capability's permissions must be able to satisfy what the target requires.
            // A cap with AuthRequired::None can satisfy anything (it's the most permissive).
            // A cap with AuthRequired::Signature can only satisfy Signature or None requirements.
            if !can_satisfy(&self.permissions, required) {
                return Err(CapabilityProofError::InsufficientPermissions {
                    held: self.permissions.clone(),
                    required: required.clone(),
                });
            }
        }
        Ok(())
    }
}

/// Check if a capability's permission level can satisfy a target's requirement.
///
/// The cap's permission level represents what auth the holder provided to GET the cap.
/// When exercising, we check: does the cap's auth level meet or exceed what the target
/// requires for this action?
///
/// Ordering (most permissive to least):
/// - None: can satisfy any requirement (the cap was freely granted)
/// - Either: can satisfy Signature, Proof, Either, or None requirements
/// - Signature: can satisfy Signature or None requirements
/// - Proof: can satisfy Proof or None requirements
/// - Impossible: cannot satisfy anything
fn can_satisfy(cap_permissions: &AuthRequired, target_requires: &AuthRequired) -> bool {
    match target_requires {
        // Target requires nothing -- any cap suffices.
        AuthRequired::None => true,
        // Target requires impossible -- nothing can satisfy.
        AuthRequired::Impossible => false,
        // Target requires a specific auth kind.
        AuthRequired::Signature => matches!(
            cap_permissions,
            AuthRequired::None | AuthRequired::Signature | AuthRequired::Either
        ),
        AuthRequired::Proof => matches!(
            cap_permissions,
            AuthRequired::None | AuthRequired::Proof | AuthRequired::Either
        ),
        AuthRequired::Either => matches!(
            cap_permissions,
            AuthRequired::None
                | AuthRequired::Signature
                | AuthRequired::Proof
                | AuthRequired::Either
        ),
        // Custom requires the cap to carry an identical Custom requirement;
        // the executor's per-variant check enforces the vk_hash match.
        AuthRequired::Custom { vk_hash } => matches!(
            cap_permissions,
            AuthRequired::Custom { vk_hash: cap_vk } if cap_vk == vk_hash
        ),
    }
}

/// Map AuthRequired to a single discriminant byte for signing messages.
fn auth_required_discriminant(auth: &AuthRequired) -> u8 {
    match auth {
        AuthRequired::None => 0,
        AuthRequired::Signature => 1,
        AuthRequired::Proof => 2,
        AuthRequired::Either => 3,
        AuthRequired::Impossible => 4,
        // Custom authorizers: encode as 5 (same tier byte as in canonical
        // commitment; the full vk_hash is committed separately).
        AuthRequired::Custom { .. } => 5,
    }
}

/// Ed25519 signature verification (using ed25519-dalek).
fn verify_ed25519(pubkey_bytes: &[u8; 32], message: &[u8], signature: &[u8; 64]) -> bool {
    use ed25519_dalek::{Signature, VerifyingKey};
    let Ok(vk) = VerifyingKey::from_bytes(pubkey_bytes) else {
        return false;
    };
    let sig = Signature::from_bytes(signature);
    vk.verify_strict(message, &sig).is_ok()
}

// ─────────────────────────────────────────────────────────────────────────────
// Post-quantum (ML-DSA-65, FIPS 204) half of the HYBRID capability authenticator
// ─────────────────────────────────────────────────────────────────────────────

/// Domain-separation context for the ML-DSA half of a HYBRID capability proof
/// (FIPS 204 `ctx`, bound into every signature). Distinct from the turn-path
/// (`dregg-hybrid-turn-v1`) and consensus (`dregg-hybrid-qc-v1`) contexts so a
/// capability-proof PQ signature can never be replayed onto another surface.
pub const CAP_PROOF_PQ_CTX: &[u8] = b"dregg-cap-proof-pq-v1";

/// Serialized length of an ML-DSA-65 public key (FIPS 204 = 1952 bytes).
pub const ML_DSA_CAP_PK_LEN: usize = dregg_pq::ML_DSA_PK_LEN;

/// The post-quantum half of a hybrid capability identity: an ML-DSA-65 signing
/// key plus its serialized public key, derived from the SAME 32-byte ed25519
/// seed the classical identity uses.
///
/// A thin newtype over the shared [`dregg_pq::MlDsaKey`] primitive that pins the
/// capability-proof domain-separation context ([`CAP_PROOF_PQ_CTX`]).
#[derive(Clone, Debug)]
pub struct MlDsaCapKey(dregg_pq::MlDsaKey);

impl MlDsaCapKey {
    /// Derive the ML-DSA-65 keypair DETERMINISTICALLY from a 32-byte ed25519
    /// seed (`ML-DSA.KeyGen` from `ξ = seed`). Same seed → same PQ key, so the
    /// holder's PQ public key can be re-derived at enrollment with no separate
    /// ceremony.
    pub fn from_ed25519_seed(seed: &[u8; 32]) -> Self {
        Self(dregg_pq::MlDsaKey::from_ed25519_seed(seed))
    }

    /// The serialized ML-DSA-65 public key — the value a verifier ENROLLS and
    /// PINS to this holder's identity.
    pub fn public_bytes(&self) -> Vec<u8> {
        self.0.public_bytes()
    }

    /// Sign `message` under [`CAP_PROOF_PQ_CTX`]. `None` only on the vanishingly
    /// rare internal RNG failure (which then fails CLOSED at verification).
    pub fn sign(&self, message: &[u8]) -> Option<Vec<u8>> {
        self.0.try_sign(CAP_PROOF_PQ_CTX, message)
    }
}

/// The ML-DSA-65 public key a verifier must ENROLL for a holder whose classical
/// identity uses `ed25519_seed`. Convenience over
/// [`MlDsaCapKey::from_ed25519_seed`] for enrollment flows.
pub fn enrolled_ml_dsa_pubkey(ed25519_seed: &[u8; 32]) -> Vec<u8> {
    dregg_pq::ml_dsa_public_from_seed(ed25519_seed)
}

/// Verify an ML-DSA-65 signature over `message` under [`CAP_PROOF_PQ_CTX`].
///
/// Returns `false` — never a panic — on a wrong-length public key, a
/// wrong-length signature, an undecodable key, or a failed cryptographic check.
/// This is the fail-CLOSED primitive for the PQ half of the hybrid proof.
pub fn ml_dsa_cap_verify(public_bytes: &[u8], message: &[u8], sig_bytes: &[u8]) -> bool {
    dregg_pq::ml_dsa_verify(public_bytes, CAP_PROOF_PQ_CTX, message, sig_bytes)
}

// ─────────────────────────────────────────────────────────────────────────────
// Signing helper (for the holder/Alice side)
// ─────────────────────────────────────────────────────────────────────────────

/// Sign a capability proof with the holder's signing key, producing BOTH halves
/// of the hybrid authenticator.
///
/// Constructs the canonical signing message from the proof fields, then signs it
/// with the classical Ed25519 key AND with the ML-DSA-65 key derived
/// DETERMINISTICALLY from the same ed25519 seed ([`MlDsaCapKey::from_ed25519_seed`]).
/// Both halves cover the identical message, so the pair is bound together.
///
/// A ONE-SHOT: it builds a [`CapabilityProofSigner`], uses it once and drops it, so it pays a full
/// ML-DSA keygen (174–227 ms on the deployed build) per call. Correct for a single proof and WRONG
/// in a loop — a holder that signs more than one capability proof should hold a
/// [`CapabilityProofSigner`] instead. The bytes are identical either way.
pub fn sign_capability_proof(proof: &mut CapabilityProof, signing_key: &ed25519_dalek::SigningKey) {
    CapabilityProofSigner::new(signing_key.clone()).sign(proof);
}

/// A holder's HYBRID capability-signing identity: the ed25519 key and the ML-DSA-65 key its seed
/// derives, held TOGETHER and derived ONCE.
///
/// This type exists because the derivation is expensive and the signing site was not.
/// `MlDsaCapKey::from_ed25519_seed` is deterministic FIPS 204 `ML-DSA.KeyGen(ξ)` and, on the
/// deployed build, runs the Lean-verified keygen core across the FFI boundary at **174–227 ms of
/// CPU**. [`sign_capability_proof`] takes a BARE `SigningKey`, so there was nothing for a derived
/// key to belong to and every capability proof a holder signed paid a fresh keygen for one
/// unchanging key. A holder that signs more than one proof should hold one of these.
///
/// **The key lives INSIDE the identity, not in a lookup table.** A process-global map keyed by seed
/// would pool every holder's ML-DSA secret in one process-lifetime structure outliving the holders
/// that own them, and make "who may read this entry" a property of a lookup key rather than of
/// ownership. Here the derived key is a private field of the object that owns the ed25519 key, so
/// two holders are two objects and cross-identity sharing has no path to express itself.
///
/// Both fields are private, set together at construction, with no mutator — so an identity cannot be
/// re-keyed in place and its two halves cannot drift apart.
pub struct CapabilityProofSigner {
    classical: ed25519_dalek::SigningKey,
    /// Behind an `Arc` so the in-module tests can prove by OBJECT IDENTITY, rather than by a
    /// stopwatch, that signing reads this key instead of deriving another.
    pq: std::sync::Arc<MlDsaCapKey>,
}

impl std::fmt::Debug for CapabilityProofSigner {
    /// Never renders key material.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("CapabilityProofSigner(..)")
    }
}

impl CapabilityProofSigner {
    /// Take ownership of a holder's ed25519 identity and derive its ML-DSA half. This is where the
    /// keygen is paid — once.
    pub fn new(classical: ed25519_dalek::SigningKey) -> Self {
        let pq = std::sync::Arc::new(MlDsaCapKey::from_ed25519_seed(&classical.to_bytes()));
        Self { classical, pq }
    }

    /// The ML-DSA-65 public key a verifier ENROLLS (or matches against the holder's committed
    /// `CellId`) for this identity — exactly the key [`Self::sign`] signs under.
    pub fn ml_dsa_public_bytes(&self) -> Vec<u8> {
        self.pq.public_bytes()
    }

    /// The holder's ed25519 public key.
    pub fn ed25519_public_bytes(&self) -> [u8; 32] {
        self.classical.verifying_key().to_bytes()
    }

    /// Sign a capability proof with BOTH halves of this identity — the same bytes
    /// [`sign_capability_proof`] produces, with no key derivation however many proofs are signed.
    ///
    /// Constructs the canonical signing message from the proof fields, then signs it with the
    /// classical Ed25519 key AND with the ML-DSA-65 key derived from the same seed. Both halves
    /// cover the identical message, so the pair is bound together. `None` from the PQ half (RNG
    /// failure) leaves it absent, which fails CLOSED at verification. The public key is self-carried
    /// in the proof; it is safe to carry because the verifier only trusts it after the holder's
    /// `CellId` is shown to commit to it (`verify_committed_ml_dsa`).
    pub fn sign(&self, proof: &mut CapabilityProof) {
        use ed25519_dalek::Signer;
        let msg = proof.signing_message();
        proof.signature = self.classical.sign(&msg).to_bytes();
        proof.holder_ml_dsa_pubkey = Some(self.pq.public_bytes());
        proof.pq_signature = self.pq.sign(&msg);
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Tests
// ─────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    use ed25519_dalek::SigningKey;

    /// Helper: create a deterministic CellId from a byte.
    fn test_cell_id(seed: u8) -> CellId {
        let pk = [seed; 32];
        let token = [0u8; 32];
        CellId::derive_raw(&pk, &token)
    }

    /// Helper: create a signed proof for testing.
    fn make_signed_proof(
        holder_key: &SigningKey,
        holder_cell: CellId,
        target_cell: CellId,
        holder_commitment: [u8; 32],
        permissions: AuthRequired,
        capability_slot: u32,
        expires_at: Option<u64>,
        timestamp: i64,
    ) -> CapabilityProof {
        let mut proof = CapabilityProof {
            holder_cell,
            holder_commitment,
            target_cell,
            permissions,
            proof_data: CapabilityProofData::SignedAttestation {
                capability_slot,
                expires_at,
            },
            timestamp,
            signature: [0u8; 64],
            pq_signature: None,
            holder_ml_dsa_pubkey: None,
        };
        sign_capability_proof(&mut proof, holder_key);
        proof
    }

    /// The HYBRID CellId for a holder whose classical identity is `holder_key`:
    /// `H("dregg-hybrid-id-v1", P_ed ‖ P_ml)`, committing to BOTH the ed25519
    /// public key AND the ML-DSA-65 key derived from the SAME 32-byte seed. This
    /// is the identity that ENROLLS the holder's PQ key — the honest holder's
    /// self-carried ML-DSA key hashes into it, so `verify` accepts.
    fn hybrid_cell_for(holder_key: &SigningKey) -> CellId {
        let ed = holder_key.verifying_key().to_bytes();
        let ml = enrolled_ml_dsa_pubkey(&holder_key.to_bytes());
        CellId::derive_hybrid_raw(&ed, &ml)
    }

    /// Helper: standard verification context.
    fn make_context(
        our_cell_id: CellId,
        expected_commitment: [u8; 32],
        current_timestamp: i64,
        current_height: u64,
    ) -> VerificationContext {
        VerificationContext {
            our_cell_id,
            expected_holder_commitment: expected_commitment,
            current_timestamp,
            max_proof_age_seconds: 300, // 5 minutes
            current_height,
        }
    }

    #[test]
    fn test_valid_exercise_accepted() {
        let holder_key = SigningKey::from_bytes(&[1u8; 32]);
        let holder_pubkey = holder_key.verifying_key().to_bytes();
        let holder_cell = hybrid_cell_for(&holder_key);
        let target_cell = test_cell_id(2);
        let commitment = [42u8; 32];

        let proof = make_signed_proof(
            &holder_key,
            holder_cell,
            target_cell,
            commitment,
            AuthRequired::Signature,
            0,
            None,
            1000,
        );

        let ctx = make_context(target_cell, commitment, 1001, 100);
        assert!(proof.verify(&holder_pubkey, &ctx).is_ok());

        // Also check permissions for a SetField effect.
        let effects = vec![PeerEffect::SetField {
            index: 0,
            value: [0u8; 32],
        }];
        let target_perms = dregg_cell::permissions::Permissions::default_user();
        assert!(
            proof
                .check_permissions_for_effects(&effects, &target_perms)
                .is_ok()
        );
    }

    /// ADVERSARIAL (GAP #4, id-commitment closure): a proof with a VALID ed25519
    /// half for holder H, whose CellId = `H("dregg-hybrid-id-v1", P_ed ‖ P_ml)`,
    /// but whose self-carried ML-DSA key is an ATTACKER's OWN fresh key (≠ the
    /// key committed by H's CellId), must REJECT — by the id-commitment, NOT a
    /// roster mismatch. The honest holder passes; missing halves fail CLOSED.
    ///
    /// This is the crux the just-committed hybrid-id foundation buys: the holder
    /// self-carries the ML-DSA key (previously an unsafe GAP #0 pattern), but the
    /// verifier trusts it ONLY because the holder's IDENTITY commits to it. A
    /// quantum attacker who forges the ed25519 half and presents their own
    /// ML-DSA key cannot make that key hash into H's CellId.
    #[test]
    fn test_pq_half_attacker_key_rejected_by_id_commitment() {
        let holder_key = SigningKey::from_bytes(&[20u8; 32]);
        let holder_pubkey = holder_key.verifying_key().to_bytes();
        // The holder's IDENTITY commits to BOTH keys: CellId = H(P_ed ‖ P_ml).
        let holder_cell = hybrid_cell_for(&holder_key);
        let target_cell = test_cell_id(21);
        let commitment = [50u8; 32];

        let proof = make_signed_proof(
            &holder_key,
            holder_cell,
            target_cell,
            commitment,
            AuthRequired::Signature,
            0,
            None,
            1000,
        );
        let ctx = make_context(target_cell, commitment, 1001, 100);

        // Honest holder: the self-carried ML-DSA key is committed by the CellId
        // → passes. Sanity-check the enrollment is exactly the committed key.
        assert_eq!(
            proof.holder_ml_dsa_pubkey.as_deref(),
            Some(enrolled_ml_dsa_pubkey(&holder_key.to_bytes()).as_slice())
        );
        assert!(proof.verify(&holder_pubkey, &ctx).is_ok());

        // The ATTACKER (a quantum ed25519-forger) presents their OWN fresh
        // ML-DSA key AND a valid ML-DSA signature under it, keeping H's ed25519
        // half. Because that key does NOT hash into H's CellId, the id-commitment
        // gate rejects it BEFORE the signature is ever trusted.
        let attacker = MlDsaCapKey::from_ed25519_seed(&[99u8; 32]);
        let mut forged = proof.clone();
        forged.holder_ml_dsa_pubkey = Some(attacker.public_bytes());
        forged.pq_signature = attacker.sign(&forged.signing_message());
        assert!(matches!(
            forged.verify(&holder_pubkey, &ctx),
            Err(CapabilityProofError::IdentityCommitmentMismatch)
        ));
        // The forged PQ half IS itself a valid ML-DSA signature under the
        // attacker's key — so had the verifier trusted a self-carried key on its
        // own (the old GAP #0 hazard), this forgery would PASS. It is rejected
        // ONLY because the holder's CellId does not commit to that key.
        assert!(ml_dsa_cap_verify(
            &attacker.public_bytes(),
            &forged.signing_message(),
            forged.pq_signature.as_ref().unwrap()
        ));

        // Missing PQ public key → fail CLOSED (not admitted on ed25519 alone).
        let mut no_pk = proof.clone();
        no_pk.holder_ml_dsa_pubkey = None;
        assert!(matches!(
            no_pk.verify(&holder_pubkey, &ctx),
            Err(CapabilityProofError::MissingPqPublicKey)
        ));

        // Missing PQ signature → fail CLOSED.
        let mut no_sig = proof.clone();
        no_sig.pq_signature = None;
        assert!(matches!(
            no_sig.verify(&holder_pubkey, &ctx),
            Err(CapabilityProofError::MissingPqSignature)
        ));
    }

    /// STAGED FLAG-DAY: a holder whose CellId is a LEGACY ed25519-only identity
    /// (`derive_raw`, distinct domain) commits to NO ML-DSA key, so the hybrid
    /// cap-proof id-commitment gate fails CLOSED. Exercising a hybrid capability
    /// proof requires a hybrid CellId — a legacy id can never satisfy the PQ
    /// enrollment, and is rejected rather than silently admitted.
    #[test]
    fn test_legacy_ed25519_only_cellid_rejected() {
        let holder_key = SigningKey::from_bytes(&[30u8; 32]);
        let holder_pubkey = holder_key.verifying_key().to_bytes();
        // Legacy identity: no ML-DSA key is committed by this CellId.
        let legacy_cell = CellId::derive_raw(&holder_pubkey, &[0u8; 32]);
        let target_cell = test_cell_id(31);
        let commitment = [60u8; 32];

        let proof = make_signed_proof(
            &holder_key,
            legacy_cell,
            target_cell,
            commitment,
            AuthRequired::Signature,
            0,
            None,
            1000,
        );
        let ctx = make_context(target_cell, commitment, 1001, 100);

        // Even though the self-carried key + signature are internally consistent,
        // the legacy CellId does not commit to any ML-DSA key → REJECTED.
        assert!(matches!(
            proof.verify(&holder_pubkey, &ctx),
            Err(CapabilityProofError::IdentityCommitmentMismatch)
        ));
    }

    #[test]
    fn test_wrong_permissions_rejected() {
        let holder_key = SigningKey::from_bytes(&[2u8; 32]);
        let holder_pubkey = holder_key.verifying_key().to_bytes();
        let holder_cell = hybrid_cell_for(&holder_key);
        let target_cell = test_cell_id(4);
        let commitment = [43u8; 32];

        // Cap has Impossible permissions -- can't satisfy anything.
        let proof = make_signed_proof(
            &holder_key,
            holder_cell,
            target_cell,
            commitment,
            AuthRequired::Impossible,
            0,
            None,
            1000,
        );

        let ctx = make_context(target_cell, commitment, 1001, 100);
        // Proof itself verifies (both hybrid halves + id-commitment are fine).
        assert!(proof.verify(&holder_pubkey, &ctx).is_ok());

        // But permissions check fails for SetField (requires Signature on default perms).
        let effects = vec![PeerEffect::SetField {
            index: 0,
            value: [0u8; 32],
        }];
        let target_perms = dregg_cell::permissions::Permissions::default_user();
        let result = proof.check_permissions_for_effects(&effects, &target_perms);
        assert!(matches!(
            result,
            Err(CapabilityProofError::InsufficientPermissions { .. })
        ));
    }

    #[test]
    fn test_expired_cap_rejected() {
        let holder_key = SigningKey::from_bytes(&[3u8; 32]);
        let holder_pubkey = holder_key.verifying_key().to_bytes();
        let holder_cell = test_cell_id(5);
        let target_cell = test_cell_id(6);
        let commitment = [44u8; 32];

        // Cap expires at height 50, but current height is 100.
        let proof = make_signed_proof(
            &holder_key,
            holder_cell,
            target_cell,
            commitment,
            AuthRequired::Signature,
            0,
            Some(50), // expires at height 50
            1000,
        );

        let ctx = make_context(target_cell, commitment, 1001, 100); // current height 100
        let result = proof.verify(&holder_pubkey, &ctx);
        assert!(matches!(
            result,
            Err(CapabilityProofError::CapabilityExpired {
                expires_at: 50,
                current_height: 100
            })
        ));
    }

    #[test]
    fn test_commitment_mismatch_rejected() {
        let holder_key = SigningKey::from_bytes(&[4u8; 32]);
        let holder_pubkey = holder_key.verifying_key().to_bytes();
        let holder_cell = test_cell_id(7);
        let target_cell = test_cell_id(8);

        let proof_commitment = [45u8; 32];
        let expected_commitment = [99u8; 32]; // Different!

        let proof = make_signed_proof(
            &holder_key,
            holder_cell,
            target_cell,
            proof_commitment,
            AuthRequired::Signature,
            0,
            None,
            1000,
        );

        let ctx = make_context(target_cell, expected_commitment, 1001, 100);
        let result = proof.verify(&holder_pubkey, &ctx);
        assert!(matches!(
            result,
            Err(CapabilityProofError::CommitmentMismatch { .. })
        ));
    }

    #[test]
    fn test_stale_timestamp_rejected() {
        let holder_key = SigningKey::from_bytes(&[5u8; 32]);
        let holder_pubkey = holder_key.verifying_key().to_bytes();
        let holder_cell = test_cell_id(9);
        let target_cell = test_cell_id(10);
        let commitment = [46u8; 32];

        let proof = make_signed_proof(
            &holder_key,
            holder_cell,
            target_cell,
            commitment,
            AuthRequired::Signature,
            0,
            None,
            1000, // timestamp from the past
        );

        // Current time is 2000, max age is 300s, so 1000 is 1000s old -> stale.
        let ctx = make_context(target_cell, commitment, 2000, 100);
        let result = proof.verify(&holder_pubkey, &ctx);
        assert!(matches!(
            result,
            Err(CapabilityProofError::StaleTimestamp { .. })
        ));
    }

    #[test]
    fn test_invalid_signature_rejected() {
        let holder_key = SigningKey::from_bytes(&[6u8; 32]);
        let holder_cell = test_cell_id(11);
        let target_cell = test_cell_id(12);
        let commitment = [47u8; 32];

        let mut proof = make_signed_proof(
            &holder_key,
            holder_cell,
            target_cell,
            commitment,
            AuthRequired::Signature,
            0,
            None,
            1000,
        );

        // Corrupt the signature.
        proof.signature[0] ^= 0xff;

        let holder_pubkey = holder_key.verifying_key().to_bytes();
        let ctx = make_context(target_cell, commitment, 1001, 100);
        let result = proof.verify(&holder_pubkey, &ctx);
        assert!(matches!(
            result,
            Err(CapabilityProofError::InvalidSignature)
        ));
    }

    #[test]
    fn test_wrong_target_rejected() {
        let holder_key = SigningKey::from_bytes(&[7u8; 32]);
        let holder_pubkey = holder_key.verifying_key().to_bytes();
        let holder_cell = test_cell_id(13);
        let target_cell = test_cell_id(14);
        let wrong_target = test_cell_id(15); // Not us!
        let commitment = [48u8; 32];

        let proof = make_signed_proof(
            &holder_key,
            holder_cell,
            target_cell,
            commitment,
            AuthRequired::Signature,
            0,
            None,
            1000,
        );

        // Verification context says we are wrong_target, but proof says target_cell.
        let ctx = make_context(wrong_target, commitment, 1001, 100);
        let result = proof.verify(&holder_pubkey, &ctx);
        assert!(matches!(
            result,
            Err(CapabilityProofError::WrongTarget { .. })
        ));
    }

    #[test]
    fn test_proof_permissions_satisfy_transfer() {
        let holder_key = SigningKey::from_bytes(&[8u8; 32]);
        let holder_cell = test_cell_id(16);
        let target_cell = test_cell_id(17);
        let commitment = [49u8; 32];

        // Cap with Signature permissions can satisfy Send (which requires Signature).
        let proof = make_signed_proof(
            &holder_key,
            holder_cell,
            target_cell,
            commitment,
            AuthRequired::Signature,
            0,
            None,
            1000,
        );

        let effects = vec![PeerEffect::Transfer { amount: 100 }];
        let target_perms = dregg_cell::permissions::Permissions::default_user();
        assert!(
            proof
                .check_permissions_for_effects(&effects, &target_perms)
                .is_ok()
        );

        // Cap with Proof permissions cannot satisfy Send (which requires Signature).
        let proof_only = make_signed_proof(
            &holder_key,
            holder_cell,
            target_cell,
            commitment,
            AuthRequired::Proof,
            1,
            None,
            1000,
        );
        let result = proof_only.check_permissions_for_effects(&effects, &target_perms);
        assert!(matches!(
            result,
            Err(CapabilityProofError::InsufficientPermissions { .. })
        ));
    }

    #[test]
    fn test_can_satisfy_logic() {
        // None cap can satisfy anything except Impossible.
        assert!(can_satisfy(&AuthRequired::None, &AuthRequired::None));
        assert!(can_satisfy(&AuthRequired::None, &AuthRequired::Signature));
        assert!(can_satisfy(&AuthRequired::None, &AuthRequired::Proof));
        assert!(can_satisfy(&AuthRequired::None, &AuthRequired::Either));
        assert!(!can_satisfy(&AuthRequired::None, &AuthRequired::Impossible));

        // Signature cap can satisfy Signature, Either, None.
        assert!(can_satisfy(&AuthRequired::Signature, &AuthRequired::None));
        assert!(can_satisfy(
            &AuthRequired::Signature,
            &AuthRequired::Signature
        ));
        assert!(!can_satisfy(&AuthRequired::Signature, &AuthRequired::Proof));
        assert!(can_satisfy(&AuthRequired::Signature, &AuthRequired::Either));

        // Impossible can satisfy nothing except None.
        assert!(can_satisfy(&AuthRequired::Impossible, &AuthRequired::None));
        assert!(!can_satisfy(
            &AuthRequired::Impossible,
            &AuthRequired::Signature
        ));
        assert!(!can_satisfy(
            &AuthRequired::Impossible,
            &AuthRequired::Proof
        ));
        assert!(!can_satisfy(
            &AuthRequired::Impossible,
            &AuthRequired::Either
        ));
        assert!(!can_satisfy(
            &AuthRequired::Impossible,
            &AuthRequired::Impossible
        ));
    }

    // ─────────────────────────────────────────────────────────────────────────
    // The HELD ML-DSA key: `CapabilityProofSigner`
    // ─────────────────────────────────────────────────────────────────────────

    fn unsigned_proof(holder: &SigningKey, target: CellId, slot: u32) -> CapabilityProof {
        CapabilityProof {
            holder_cell: hybrid_cell_for(holder),
            holder_commitment: [42u8; 32],
            target_cell: target,
            permissions: AuthRequired::Signature,
            proof_data: CapabilityProofData::SignedAttestation {
                capability_slot: slot,
                expires_at: None,
            },
            timestamp: 1000,
            signature: [0u8; 64],
            pq_signature: None,
            holder_ml_dsa_pubkey: None,
        }
    }

    /// THE MANDATORY ONE. Four holders, signing INTERLEAVED: no holder may ever present, or sign
    /// under, another holder's derived ML-DSA key.
    ///
    /// A held signer is a memo, and a memo that ever served one identity's key to another would be
    /// a FORGERY ENGINE rather than a slow path. The falsifier is on the wire: every proof's PQ
    /// half must verify under its own carried key and under NO other holder's.
    #[test]
    fn two_identities_never_share_a_derived_pq_key() {
        let seeds: [[u8; 32]; 4] = [[0x11; 32], [0x22; 32], [0x33; 32], [0xf0; 32]];
        let signers: Vec<CapabilityProofSigner> = seeds
            .iter()
            .map(|s| CapabilityProofSigner::new(SigningKey::from_bytes(s)))
            .collect();

        // The truth each holder must keep telling, computed independently of the signer.
        let expected: Vec<Vec<u8>> = seeds.iter().map(enrolled_ml_dsa_pubkey).collect();
        for (i, a) in expected.iter().enumerate() {
            for (j, b) in expected.iter().enumerate() {
                if i != j {
                    assert_ne!(
                        a, b,
                        "distinct seeds must derive distinct keys ({i} vs {j})"
                    );
                }
            }
        }

        // INTERLEAVED across rounds, so a single-slot or last-writer cache mis-serves somebody.
        let target = test_cell_id(9);
        let mut signed: Vec<Vec<CapabilityProof>> =
            (0..signers.len()).map(|_| Vec::new()).collect();
        for round in 0..3u32 {
            for (i, signer) in signers.iter().enumerate() {
                let holder = SigningKey::from_bytes(&seeds[i]);
                let mut proof = unsigned_proof(&holder, target, round * 16 + i as u32);
                signer.sign(&mut proof);
                assert_eq!(
                    proof.holder_ml_dsa_pubkey.as_deref(),
                    Some(expected[i].as_slice()),
                    "holder {i} presented a PQ key that is not the one its own seed derives \
                     (round {round})"
                );
                assert_eq!(signer.ml_dsa_public_bytes(), expected[i]);
                signed[i].push(proof);
            }
        }

        // THE FALSIFIER, on the wire: every holder's PQ half verifies under its OWN carried key and
        // under no other holder's.
        for (i, per_holder) in signed.iter().enumerate() {
            for proof in per_holder {
                let msg = proof.signing_message();
                let sig = proof
                    .pq_signature
                    .as_deref()
                    .expect("a PQ half was produced");
                assert!(
                    ml_dsa_cap_verify(&expected[i], &msg, sig),
                    "holder {i}'s own PQ half must verify under its own key"
                );
                for (j, other) in expected.iter().enumerate() {
                    if i != j {
                        assert!(
                            !ml_dsa_cap_verify(other, &msg, sig),
                            "holder {i}'s PQ signature verified under holder {j}'s key — two \
                             identities are sharing a derived key"
                        );
                    }
                }
            }
        }
    }

    /// The signer derives its ML-DSA key ONCE, proven by OBJECT IDENTITY rather than by a
    /// stopwatch: a timing assertion flakes on a loaded box and says nothing about which key was
    /// served. Signing many proofs must read the same `Arc`, never mint a second key.
    #[test]
    fn a_signer_derives_its_pq_key_once_however_many_proofs_it_signs() {
        let holder = SigningKey::from_bytes(&[0x7a; 32]);
        let signer = CapabilityProofSigner::new(holder.clone());
        let held = std::sync::Arc::clone(&signer.pq);
        for slot in 0..4u32 {
            let mut proof = unsigned_proof(&holder, test_cell_id(3), slot);
            signer.sign(&mut proof);
            assert!(
                std::sync::Arc::ptr_eq(&held, &signer.pq),
                "signing replaced the holder's derived key — the identity must hold ONE key"
            );
            assert_eq!(
                proof.holder_ml_dsa_pubkey.as_deref(),
                Some(signer.ml_dsa_public_bytes().as_slice())
            );
        }
    }

    /// The one-shot `sign_capability_proof` must remain byte-identical to the held-signer path:
    /// this refactor changed WHEN the key is derived, never WHAT is signed or by which key.
    ///
    /// The ML-DSA half is HEDGED (randomized), so the signature bytes differ between any two calls
    /// by construction; what must match is the public key presented, the classical half, and that
    /// both PQ halves verify under that one key.
    #[test]
    fn the_one_shot_and_the_held_signer_agree_on_the_key() {
        let holder = SigningKey::from_bytes(&[0x7b; 32]);
        let target = test_cell_id(4);

        let mut one_shot = unsigned_proof(&holder, target, 1);
        sign_capability_proof(&mut one_shot, &holder);
        let mut held = unsigned_proof(&holder, target, 1);
        CapabilityProofSigner::new(holder.clone()).sign(&mut held);

        assert_eq!(one_shot.holder_ml_dsa_pubkey, held.holder_ml_dsa_pubkey);
        assert_eq!(one_shot.signature, held.signature);
        let key = one_shot
            .holder_ml_dsa_pubkey
            .as_deref()
            .expect("a PQ key was presented");
        let msg = one_shot.signing_message();
        assert_eq!(msg, held.signing_message());
        assert!(ml_dsa_cap_verify(
            key,
            &msg,
            one_shot.pq_signature.as_deref().expect("PQ half")
        ));
        assert!(ml_dsa_cap_verify(
            key,
            &msg,
            held.pq_signature.as_deref().expect("PQ half")
        ));
    }
}
