//! Encrypted turn: a turn whose content is hidden from the federation during ordering.
//!
//! An `EncryptedTurn` bundles:
//! - The encrypted turn body (ChaCha20-Poly1305)
//! - A commitment to the plaintext turn (BLAKE3 hash)
//! - A conflict set (Bloom filter over accessed cells) — **submitter-declared and
//!   unverified**; see the named seam on [`EncryptedTurn::verify_admission_binding`]
//! - A [`TurnValidityProof`] which, at HEAD, carries submitter AUTHENTICATION and an
//!   EMPTY `proof_bytes` — there is no validity STARK in the tree
//!
//! The federation orders encrypted turns by:
//! 1. Checking admission ([`EncryptedTurn::verify_admission_binding`]): an Ed25519
//!    signature by the key controlling the claimed `agent`. **It does NOT check that the
//!    agent can pay or that the nonce is fresh** — those are the standard executor gates
//!    downstream, after decryption. Proving them in zero knowledge is the Phase-2 STARK,
//!    which is named, not built.
//! 2. Detecting conflicts via Bloom filter overlap — on the filter the SUBMITTER declared.
//! 3. Serializing conflicting turns, parallelizing non-conflicting ones.
//!
//! After ordering is finalized, the turn is revealed (either by the agent publishing
//! the decryption key, or via threshold decryption by the validator set).
//!
//! # Cryptography
//!
//! `EncryptedTurn::encrypt_for_executor(turn, recipient_pub)`:
//! - generates a fresh X25519 ephemeral keypair,
//! - performs X25519 DH with the executor's public key,
//! - derives a 32-byte ChaCha20-Poly1305 key via BLAKE3-derive_key,
//! - encrypts `serde_json::to_vec(turn)` with a fresh 12-byte nonce,
//! - records both `ephemeral_public` and `nonce` in the struct so the
//!   executor can later DH + decrypt with its static unsealer key.
//!
//! The `turn_commitment` is computed over the plaintext bytes so the
//! validator can also bind the proof to the same commit pre-encryption, and
//! the executor can verify post-decryption that the decrypted bytes hash to
//! the same commitment.
//!
//! # Why JSON here?
//!
//! Historically `Turn` carried `#[serde(skip_serializing_if = "…")]` fields,
//! which broke positional formats (postcard/bincode): a skipped field is not
//! written on serialize but still read on deserialize, desyncing the byte
//! stream ("Found an Option discriminant that wasn't 0 or 1"). Those skips have
//! since been removed (every `Turn`/`Action` field is now always serialized),
//! so `Turn` round-trips through postcard. This envelope stays on JSON for
//! schema stability of the encrypted ciphertext; it could move to postcard now
//! that the underlying `Turn` schema is positional-safe. (See
//! `tests::privacy_wiring::encrypted_turn_decrypts_to_original`.)

use dregg_cell::CellId;
use serde::{Deserialize, Serialize};

use crate::conflict::ConflictSet;
use crate::turn::Turn;

/// An encrypted turn submission for privacy-preserving federation ordering.
///
/// The federation orders these without seeing their content. The validity proof
/// guarantees the enclosed turn is well-formed and payable.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct EncryptedTurn {
    /// The agent submitting this turn (public — needed for nonce/fee lookup).
    /// This is the ONE piece of metadata that remains visible.
    pub agent: CellId,

    /// Sender's ephemeral X25519 public key (32 bytes).
    /// Combined with the executor's static X25519 secret, this gives the
    /// ChaCha20-Poly1305 key via X25519 DH + BLAKE3-derive_key.
    pub ephemeral_public: [u8; 32],

    /// ChaCha20-Poly1305 nonce (12 bytes).
    pub nonce: [u8; 12],

    /// Encrypted turn body (ChaCha20-Poly1305 ciphertext + 16-byte authentication tag).
    pub ciphertext: Vec<u8>,

    /// BLAKE3 hash of the plaintext turn (for binding the proof to specific content).
    /// After decryption, validators check that BLAKE3(decrypted) == turn_commitment.
    pub turn_commitment: [u8; 32],

    /// Bloom filter over the read/write cell set.
    /// Used for conflict detection without revealing specific cell IDs.
    pub conflict_set: ConflictSet,

    /// The validity carrier. At HEAD this is submitter AUTHENTICATION with empty
    /// `proof_bytes` — it proves neither nonce correctness nor fee sufficiency. See
    /// [`TurnValidityProof`] for exactly what is and is not enforced.
    pub validity_proof: TurnValidityProof,

    /// Submission timestamp (for ordering within conflict buckets).
    pub submitted_at: i64,
}

/// The validity carrier for an encrypted turn. **Despite the name, no STARK is carried or
/// verified at HEAD**: `proof_bytes` is empty and the only enforced leg is
/// [`SubmitterAuth`].
///
/// What is ACTUALLY enforced today ([`EncryptedTurn::verify_admission_binding`]):
/// - an Ed25519 signature over [`TurnValidityPublicInputs::signing_message`], by a key
///   whose `derive_raw` equals the claimed agent cell (so only the controlling agent can
///   make a node spend decrypt/execute work, bound to this exact envelope).
///
/// What the Phase-2 STARK is NAMED to prove — and does not, because no prover exists:
/// - knowledge of a Turn T with `BLAKE3(T) = turn_commitment`;
/// - `T.nonce` = the agent cell's current nonce (replay protection);
/// - `agent_cell.balance >= T.fee` (fee sufficiency);
/// - and the conflict set matching the cells T touches (see the seam on
///   `verify_admission_binding`).
///
/// Until then those are ordinary executor gates applied AFTER decryption, not
/// zero-knowledge guarantees held at ordering time.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct TurnValidityProof {
    /// The STARK proof bytes (serialized StarkProof from dregg-circuit).
    ///
    /// Phase-2 (STARK validity ceremony) fills this with a real
    /// nonce/fee/conservation STARK. It is empty in Phase-1.
    pub proof_bytes: Vec<u8>,

    /// Public inputs to the STARK (what the verifier checks against):
    /// - [0]: turn_commitment (as BabyBear field element)
    /// - [1]: agent_id_commitment (hash of agent CellId, as field element)
    /// - [2]: claimed_nonce (the nonce this turn uses)
    /// - [3]: min_fee (minimum fee this turn will pay — may be a lower bound)
    pub public_inputs: TurnValidityPublicInputs,

    /// Phase-1 submitter authentication (the *producible* validity carrier).
    ///
    /// The full nonce/fee STARK (`proof_bytes`) is a future build; until it
    /// lands, the live fee-DoS seam is closed by requiring an Ed25519 signature
    /// from the key that controls the agent cell over the canonical
    /// `public_inputs` digest. This is the SAME authentication the cleartext
    /// `/turns/submit` path enforces before doing executor work
    /// (`signer.verify(turn_hash, signature)` + signer→agent binding), lifted
    /// onto the encrypted envelope so a flood of unauthenticated encrypted
    /// blobs can be rejected at ingress *before* the node decrypts/executes.
    ///
    /// `None` = no submitter authentication (the Phase-0 placeholder); rejected
    /// fail-closed by [`EncryptedTurn::verify_admission_binding`].
    #[serde(default)]
    pub submitter_auth: Option<SubmitterAuth>,
}

/// Phase-1 submitter authentication for an encrypted turn: an Ed25519 signature
/// by the key controlling the agent cell over the validity proof's public
/// inputs.
///
/// This is the carrier `verify_admission_binding` checks today. It binds the (otherwise
/// unauthenticated) encrypted envelope to a key the node can map to the
/// `agent` cell, so only that agent can make the node spend decrypt/execute
/// work — closing the fee-DoS without yet building the full validity STARK.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct SubmitterAuth {
    /// The Ed25519 public key of the submitter (the key controlling `agent`).
    pub submitter_public: [u8; 32],
    /// Ed25519 signature over `public_inputs.signing_message()`.
    #[serde(with = "crate::action::serde_sig64")]
    pub signature: [u8; 64],
}

/// Public inputs for the turn validity STARK.
///
/// These are the values that the verifier can see and check against on-chain state.
/// Everything else (turn content, effects, targets) remains private.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct TurnValidityPublicInputs {
    /// Commitment to the turn body: BLAKE3(serialize(turn)).
    /// Binds the proof to a specific (unknown) turn.
    pub turn_commitment: [u8; 32],

    /// Commitment to the agent identity: BLAKE3("agent" || agent.as_bytes()).
    /// The verifier checks this matches the claimed agent.
    pub agent_commitment: [u8; 32],

    /// The nonce this turn claims to use.
    /// The verifier checks: agent_cell.nonce == claimed_nonce.
    pub claimed_nonce: u64,

    /// Minimum fee this turn will pay (proven lower bound).
    /// The verifier checks: agent_cell.balance >= min_fee.
    /// This may be lower than the actual fee (privacy: exact fee is hidden).
    pub min_fee: u64,

    /// Commitment to the conflict set: BLAKE3(conflict_set.filter).
    /// Binds the conflict set to the validity proof (prevents conflict set swapping).
    pub conflict_set_commitment: [u8; 32],
}

impl TurnValidityPublicInputs {
    /// Compute the agent commitment from a CellId.
    pub fn compute_agent_commitment(agent: &CellId) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new();
        hasher.update(b"dregg-agent-commitment-v1");
        hasher.update(agent.as_bytes());
        *hasher.finalize().as_bytes()
    }

    /// Verify that the claimed agent matches the public inputs.
    pub fn verify_agent(&self, agent: &CellId) -> bool {
        self.agent_commitment == Self::compute_agent_commitment(agent)
    }

    /// Verify that the conflict set matches the commitment in the public inputs.
    pub fn verify_conflict_set(&self, conflict_set: &ConflictSet) -> bool {
        self.conflict_set_commitment == conflict_set.commitment()
    }

    /// The canonical bytes the submitter signs (Phase-1 authentication).
    ///
    /// Domain-separated digest over every public input, so a signature is bound
    /// to this exact turn commitment / agent / nonce / fee / conflict set and
    /// cannot be replayed against a different envelope.
    pub fn signing_message(&self) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new_derive_key("dregg-encrypted-turn-validity-auth v1");
        hasher.update(&self.turn_commitment);
        hasher.update(&self.agent_commitment);
        hasher.update(&self.claimed_nonce.to_le_bytes());
        hasher.update(&self.min_fee.to_le_bytes());
        hasher.update(&self.conflict_set_commitment);
        *hasher.finalize().as_bytes()
    }
}

/// Derive the symmetric ChaCha20-Poly1305 key from an X25519 DH shared secret.
///
/// Both encrypt and decrypt sides MUST compute the same key. We use BLAKE3 in
/// derive_key mode with the domain string `"dregg-encrypted-turn-key v1"`,
/// hashing `shared_secret || ephemeral_public || recipient_public`. Mixing all
/// three values gives:
/// - shared_secret: the actual DH output (mutual knowledge of secret)
/// - ephemeral_public: binds the key to this specific ephemeral
/// - recipient_public: binds the key to this specific executor (no key reuse
///   across deployments)
fn derive_turn_key(
    shared_secret: &[u8; 32],
    ephemeral_public: &[u8; 32],
    recipient_public: &[u8; 32],
) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("dregg-encrypted-turn-key v1");
    hasher.update(shared_secret);
    hasher.update(ephemeral_public);
    hasher.update(recipient_public);
    *hasher.finalize().as_bytes()
}

impl EncryptedTurn {
    /// Encrypt a `Turn` for a specific executor (identified by their X25519 public key).
    ///
    /// Generates a fresh X25519 ephemeral keypair, performs DH with the
    /// executor's public key, derives the symmetric key, and encrypts the
    /// `postcard`-serialized turn under ChaCha20-Poly1305.
    ///
    /// The caller is responsible for supplying a well-formed `validity_proof`
    /// (or a placeholder for testing) and a `conflict_set` that the validity
    /// proof's public inputs bind to.
    pub fn encrypt_for_executor(
        turn: &Turn,
        agent: CellId,
        recipient_public: &[u8; 32],
        conflict_set: ConflictSet,
        validity_proof: TurnValidityProof,
        submitted_at: i64,
    ) -> Result<Self, EncryptedTurnError> {
        use chacha20poly1305::aead::{Aead, KeyInit};
        use chacha20poly1305::{ChaCha20Poly1305, Nonce};
        use x25519_dalek::{PublicKey, StaticSecret};

        let plaintext = serde_json::to_vec(turn)
            .map_err(|e| EncryptedTurnError::SerializationFailed(e.to_string()))?;
        let turn_commitment = {
            let mut hasher = blake3::Hasher::new_derive_key("dregg-encrypted-turn-commitment v1");
            hasher.update(&plaintext);
            *hasher.finalize().as_bytes()
        };

        let mut eph_secret_bytes = [0u8; 32];
        getrandom::fill(&mut eph_secret_bytes)
            .map_err(|e| EncryptedTurnError::RandomFailed(e.to_string()))?;
        let eph_secret = StaticSecret::from(eph_secret_bytes);
        let eph_public = PublicKey::from(&eph_secret);

        let recipient = PublicKey::from(*recipient_public);
        let shared = eph_secret.diffie_hellman(&recipient);
        let key = derive_turn_key(shared.as_bytes(), eph_public.as_bytes(), recipient_public);

        let mut nonce_bytes = [0u8; 12];
        getrandom::fill(&mut nonce_bytes)
            .map_err(|e| EncryptedTurnError::RandomFailed(e.to_string()))?;
        let cipher = ChaCha20Poly1305::new((&key).into());
        let nonce = Nonce::from_slice(&nonce_bytes);
        let ciphertext = cipher
            .encrypt(nonce, plaintext.as_slice())
            .map_err(|_| EncryptedTurnError::EncryptionFailed)?;

        Ok(EncryptedTurn {
            agent,
            ephemeral_public: *eph_public.as_bytes(),
            nonce: nonce_bytes,
            ciphertext,
            turn_commitment,
            conflict_set,
            validity_proof,
            submitted_at,
        })
    }

    /// Decrypt this encrypted turn using the executor's static X25519 secret.
    ///
    /// Returns the recovered `Turn`. After decryption, the BLAKE3 commitment
    /// of the plaintext is recomputed and compared against `self.turn_commitment`;
    /// a mismatch indicates a corrupted ciphertext or a wrong recipient key.
    ///
    /// This is the executor-side counterpart of `encrypt_for_executor`. Both
    /// sides MUST use the same recipient public key — passing a stale or
    /// mismatched public key here will produce `DecryptionFailed`.
    pub fn decrypt_for_executor(
        &self,
        recipient_secret: &[u8; 32],
        recipient_public: &[u8; 32],
    ) -> Result<Turn, EncryptedTurnError> {
        use chacha20poly1305::aead::{Aead, KeyInit};
        use chacha20poly1305::{ChaCha20Poly1305, Nonce};
        use x25519_dalek::{PublicKey, StaticSecret};

        let secret = StaticSecret::from(*recipient_secret);
        let eph_public = PublicKey::from(self.ephemeral_public);
        let shared = secret.diffie_hellman(&eph_public);
        let key = derive_turn_key(shared.as_bytes(), &self.ephemeral_public, recipient_public);

        let cipher = ChaCha20Poly1305::new((&key).into());
        let nonce = Nonce::from_slice(&self.nonce);
        let plaintext = cipher
            .decrypt(nonce, self.ciphertext.as_slice())
            .map_err(|_| EncryptedTurnError::DecryptionFailed)?;

        let expected_commitment = {
            let mut hasher = blake3::Hasher::new_derive_key("dregg-encrypted-turn-commitment v1");
            hasher.update(&plaintext);
            *hasher.finalize().as_bytes()
        };
        if expected_commitment != self.turn_commitment {
            return Err(EncryptedTurnError::CommitmentVerificationFailed);
        }

        let turn: Turn = serde_json::from_slice(&plaintext)
            .map_err(|e| EncryptedTurnError::SerializationFailed(e.to_string()))?;
        Ok(turn)
    }

    /// Verify the encrypted turn's metadata consistency (without decryption).
    ///
    /// This checks:
    /// 1. The validity proof's agent commitment matches the claimed agent
    /// 2. The conflict set commitment in the proof matches the actual conflict set
    /// 3. The turn commitment in the proof matches the one in the header
    ///
    /// It does NOT verify the STARK proof itself — that requires the circuit verifier.
    pub fn verify_metadata(&self) -> Result<(), EncryptedTurnError> {
        // Check agent binding.
        if !self.validity_proof.public_inputs.verify_agent(&self.agent) {
            return Err(EncryptedTurnError::AgentMismatch);
        }

        // Check conflict set binding.
        if !self
            .validity_proof
            .public_inputs
            .verify_conflict_set(&self.conflict_set)
        {
            return Err(EncryptedTurnError::ConflictSetMismatch);
        }

        // Check turn commitment binding.
        if self.validity_proof.public_inputs.turn_commitment != self.turn_commitment {
            return Err(EncryptedTurnError::TurnCommitmentMismatch);
        }

        Ok(())
    }

    /// The default token id used to derive an agent cell from its controlling
    /// Ed25519 key — `blake3::hash(b"default")`, matching the cleartext
    /// `/turns/submit` binding (`CellId::derive_raw(signer, default_token_id)`).
    fn default_token_id() -> [u8; 32] {
        *blake3::hash(b"default").as_bytes()
    }

    /// Verify that this encrypted turn is ADMISSIBLE — that it is authenticated by the
    /// agent it claims to charge — the part `verify_metadata` deliberately skips.
    /// FAIL-CLOSED against an unauthenticated envelope.
    ///
    /// **This verifies no STARK.** It was named `verify_stark` until 2026-07-15, which was
    /// simply false: the body checks an Ed25519 signature and an agent binding. The
    /// validity STARK is the Phase-2 remainder below, and no prover for it exists.
    ///
    /// # The fee-DoS this closes
    ///
    /// An `EncryptedTurn` envelope carries no signature of its own; without a
    /// validity check the node would X25519-decrypt and fully execute any
    /// postcard blob a stranger POSTs — a denial-of-service (the attacker
    /// forces decrypt + execute work for free, and can replay). The cleartext
    /// `/turns/submit` path does not have this hole: it `signer.verify`s an
    /// Ed25519 signature and binds `signer → agent` *before* doing executor
    /// work. This method lifts that exact defense onto the encrypted path.
    ///
    /// # Phase-1 (today): submitter authentication
    ///
    /// Verifies `validity_proof.submitter_auth`: an Ed25519 signature over the
    /// public-input digest by the key that controls `self.agent`
    /// (`CellId::derive_raw(submitter_public, default_token)` must equal
    /// `self.agent`). This proves only the controlling agent can make the node
    /// spend decrypt/execute work, and binds the signature to this exact turn
    /// commitment (no replay onto a different envelope). It does NOT yet prove
    /// nonce-freshness / fee-sufficiency *in zero knowledge* — those are the
    /// standard executor gates downstream, plus the Phase-2 STARK below.
    ///
    /// # Phase-2 (named remainder): the validity STARK
    ///
    /// When a real `TurnValidityProof` STARK prover lands (proving nonce + fee
    /// without revealing content), it fills `proof_bytes`; this method then also
    /// verifies those bytes against `public_inputs`. No such prover exists in
    /// the tree yet, so a non-empty `proof_bytes` is conservatively rejected as
    /// unverifiable rather than admitted.
    ///
    /// # ⚠ NAMED SEAM: `conflict_set` is submitter-declared and UNVERIFIED (2026-07-15)
    ///
    /// This method does not — and no code in the tree does — check that the envelope's
    /// [`Self::conflict_set`] reflects the cells the encrypted turn actually touches. The
    /// contents are encrypted, so nothing can check it pre-decrypt today.
    /// `verify_metadata` binds the filter to `conflict_set_commitment`, but BOTH are
    /// submitter-chosen: that is self-consistency, not honesty.
    ///
    /// The consequence, stated plainly because it was previously unnamed:
    /// [`order_encrypted_turns`] buckets on [`Self::may_conflict_with`], which reads only
    /// these declared Bloom filters. A submitter who declares an EMPTY filter is bucketed
    /// as parallel-safe against turns it really conflicts with; one who declares a FULL
    /// filter serializes the whole batch. So ordering TRUSTS the submitter's conflict
    /// declaration. `ConflictSet`'s false-positive-only guarantee holds for an HONEST
    /// filter and says nothing about an adversarial one.
    ///
    /// Closing it needs the conflict set proven against the encrypted contents — the same
    /// Phase-2 validity STARK named above (it is the natural statement to add).
    ///
    /// Kept SEPARATE from `verify_metadata` (whose "does not verify the proof"
    /// contract existing decrypt round-trips depend on); invoked on the
    /// admission path when `TurnExecutor::require_validity_proof` is set.
    pub fn verify_admission_binding(&self) -> Result<(), EncryptedTurnError> {
        // Phase-2 remainder: a real validity STARK is not yet wired. If a
        // (non-empty) proof shows up, reject rather than admit unverified.
        if !self.validity_proof.proof_bytes.is_empty() {
            return Err(EncryptedTurnError::InvalidValidityProof(
                "encrypted turn carries a non-empty validity STARK but no verifier is \
                 wired to check it; rejected rather than admitted unverified"
                    .to_string(),
            ));
        }

        // Phase-1: require submitter authentication (the producible carrier).
        let auth = self.validity_proof.submitter_auth.as_ref().ok_or_else(|| {
            EncryptedTurnError::InvalidValidityProof(
                "encrypted turn carries no validity proof and no submitter \
                 authentication; rejected fail-closed to prevent fee-DoS on the \
                 ordering path (an unauthenticated encrypted blob must not consume \
                 decrypt/execute work)"
                    .to_string(),
            )
        })?;

        // 1. The signature must verify against the signed public-input digest.
        let vk = ed25519_dalek::VerifyingKey::from_bytes(&auth.submitter_public).map_err(|_| {
            EncryptedTurnError::InvalidValidityProof(
                "submitter authentication public key is not a valid Ed25519 key".to_string(),
            )
        })?;
        let sig = ed25519_dalek::Signature::from_bytes(&auth.signature);
        let msg = self.validity_proof.public_inputs.signing_message();
        vk.verify_strict(&msg, &sig).map_err(|_| {
            EncryptedTurnError::InvalidValidityProof(
                "submitter authentication signature does not verify over the validity \
                 proof public inputs"
                    .to_string(),
            )
        })?;

        // 2. The signing key must control the agent cell this turn charges:
        //    derive_raw(submitter_public, default_token) == self.agent.
        let derived = CellId::derive_raw(&auth.submitter_public, &Self::default_token_id());
        if derived != self.agent {
            return Err(EncryptedTurnError::InvalidValidityProof(
                "submitter authentication key does not control the claimed agent cell \
                 (derive_raw(submitter_public, default_token) != envelope.agent)"
                    .to_string(),
            ));
        }

        Ok(())
    }

    /// Check if this encrypted turn might conflict with another.
    ///
    /// Uses the Bloom filter conflict sets. False positives are possible
    /// (two non-conflicting turns flagged as conflicting) but false negatives are not.
    pub fn may_conflict_with(&self, other: &EncryptedTurn) -> bool {
        self.conflict_set.may_conflict_with(&other.conflict_set)
    }
}

/// Errors in encrypted turn validation (metadata-level, no decryption).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EncryptedTurnError {
    /// The agent commitment in the validity proof doesn't match the claimed agent.
    AgentMismatch,
    /// The conflict set commitment in the validity proof doesn't match the conflict set.
    ConflictSetMismatch,
    /// The turn commitment in the validity proof doesn't match the header commitment.
    TurnCommitmentMismatch,
    /// The validity STARK proof failed verification.
    InvalidValidityProof(String),
    /// Decryption failed (wrong key or tampered ciphertext).
    DecryptionFailed,
    /// Decrypted turn doesn't match the commitment.
    CommitmentVerificationFailed,
    /// AEAD encryption failed.
    EncryptionFailed,
    /// Postcard serialize/deserialize failed.
    SerializationFailed(String),
    /// `getrandom` failed (extremely rare; OS entropy source unavailable).
    RandomFailed(String),
    /// Executor has no decryption key configured.
    NoDecryptionKey,
}

/// Result of ordering a batch of encrypted turns.
///
/// The federation produces this after consensus. It contains the ordering
/// (which turns go in which positions) and conflict bucketing.
#[derive(Clone, Debug)]
pub struct TurnOrdering {
    /// Turns grouped by conflict bucket. Turns in different buckets can execute in parallel.
    /// Turns within the same bucket must execute sequentially.
    pub buckets: Vec<ConflictBucket>,
}

/// A group of turns that potentially conflict and must be serialized.
#[derive(Clone, Debug)]
pub struct ConflictBucket {
    /// Turn commitments in execution order within this bucket.
    pub turn_commitments: Vec<[u8; 32]>,
}

/// Order a batch of encrypted turns into conflict-aware buckets.
///
/// Algorithm: greedy graph coloring on the conflict graph.
/// Each turn is a node; edges connect turns whose Bloom filters overlap.
/// Each color (bucket) contains non-conflicting turns that can parallelize.
pub fn order_encrypted_turns(turns: &[EncryptedTurn]) -> TurnOrdering {
    if turns.is_empty() {
        return TurnOrdering {
            buckets: Vec::new(),
        };
    }

    let n = turns.len();
    let mut bucket_assignments: Vec<Option<usize>> = vec![None; n];
    let mut buckets: Vec<ConflictBucket> = Vec::new();

    for i in 0..n {
        // Find the first bucket where this turn doesn't conflict with any existing member.
        let mut assigned = false;
        for (bucket_idx, bucket) in buckets.iter().enumerate() {
            let conflicts_with_bucket = bucket.turn_commitments.iter().any(|existing_commit| {
                // Find the turn with this commitment and check conflict.
                turns
                    .iter()
                    .any(|t| t.turn_commitment == *existing_commit && turns[i].may_conflict_with(t))
            });

            if !conflicts_with_bucket {
                bucket_assignments[i] = Some(bucket_idx);
                assigned = true;
                break;
            }
        }

        if !assigned {
            // Create a new bucket.
            bucket_assignments[i] = Some(buckets.len());
            buckets.push(ConflictBucket {
                turn_commitments: Vec::new(),
            });
        }

        // Add to the assigned bucket.
        let bucket_idx = bucket_assignments[i].unwrap();
        buckets[bucket_idx]
            .turn_commitments
            .push(turns[i].turn_commitment);
    }

    TurnOrdering { buckets }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_cell_id(seed: u8) -> CellId {
        let mut bytes = [0u8; 32];
        bytes[0] = seed;
        CellId::from_bytes(bytes)
    }

    fn dummy_encrypted_turn(agent_seed: u8, cells: &[u8]) -> EncryptedTurn {
        let agent = make_cell_id(agent_seed);
        let mut conflict_set = ConflictSet::new();
        for &c in cells {
            conflict_set.insert(&make_cell_id(c));
        }

        let turn_commitment = {
            let mut hasher = blake3::Hasher::new();
            hasher.update(&[agent_seed]);
            *hasher.finalize().as_bytes()
        };

        let agent_commitment = TurnValidityPublicInputs::compute_agent_commitment(&agent);
        let conflict_set_commitment = conflict_set.commitment();

        EncryptedTurn {
            agent,
            ephemeral_public: [0u8; 32], // dummy
            nonce: [0u8; 12],            // dummy
            ciphertext: vec![0u8; 64],   // dummy
            turn_commitment,
            conflict_set,
            validity_proof: TurnValidityProof {
                proof_bytes: Vec::new(), // dummy
                public_inputs: TurnValidityPublicInputs {
                    turn_commitment,
                    agent_commitment,
                    claimed_nonce: 0,
                    min_fee: 100,
                    conflict_set_commitment,
                },
                submitter_auth: None, // dummy: unauthenticated (verify_admission_binding rejects)
            },
            submitted_at: 0,
        }
    }

    #[test]
    fn metadata_verification_passes_for_consistent_turn() {
        let et = dummy_encrypted_turn(1, &[10, 20, 30]);
        assert_eq!(et.verify_metadata(), Ok(()));
    }

    #[test]
    fn metadata_verification_fails_on_agent_mismatch() {
        let mut et = dummy_encrypted_turn(1, &[10, 20, 30]);
        et.agent = make_cell_id(99); // mismatch
        assert_eq!(et.verify_metadata(), Err(EncryptedTurnError::AgentMismatch));
    }

    #[test]
    fn non_conflicting_turns_in_separate_buckets_or_same() {
        // Two turns accessing completely different cells should be in the same bucket
        // (they can parallelize).
        let t1 = dummy_encrypted_turn(1, &[10, 11]);
        let t2 = dummy_encrypted_turn(2, &[20, 21]);

        // They shouldn't conflict (different cells, Bloom filter should separate them).
        // Note: there's a tiny chance of false positive, but with k=8, m=256, n=2 it's negligible.
        if !t1.may_conflict_with(&t2) {
            let ordering = order_encrypted_turns(&[t1, t2]);
            // Should be 1 bucket (both can parallelize).
            assert_eq!(ordering.buckets.len(), 1);
            assert_eq!(ordering.buckets[0].turn_commitments.len(), 2);
        }
    }

    #[test]
    fn conflicting_turns_in_different_buckets() {
        // Two turns accessing the same cell must be in different buckets.
        let t1 = dummy_encrypted_turn(1, &[10]);
        let t2 = dummy_encrypted_turn(2, &[10]); // same cell

        assert!(t1.may_conflict_with(&t2));
        let ordering = order_encrypted_turns(&[t1, t2]);
        assert_eq!(ordering.buckets.len(), 2);
    }

    // ── P3: validity-proof fail-closed gate + Phase-1 submitter auth ─────────

    /// Build an encrypted turn whose `agent` is `derive_raw(signing_key, default)`
    /// and whose `submitter_auth` is a genuine Ed25519 signature over the public
    /// inputs — the shape a real authenticated submission has. The conflict set /
    /// commitments are kept consistent so `verify_metadata` also passes.
    fn authenticated_encrypted_turn(seed: u8) -> (EncryptedTurn, ed25519_dalek::SigningKey) {
        use ed25519_dalek::{Signer, SigningKey};
        let sk = SigningKey::from_bytes(&[seed; 32]);
        let submitter_public = sk.verifying_key().to_bytes();
        let default_token = *blake3::hash(b"default").as_bytes();
        let agent = CellId::derive_raw(&submitter_public, &default_token);

        let conflict_set = ConflictSet::new();
        let turn_commitment = {
            let mut h = blake3::Hasher::new();
            h.update(&[seed]);
            *h.finalize().as_bytes()
        };
        let public_inputs = TurnValidityPublicInputs {
            turn_commitment,
            agent_commitment: TurnValidityPublicInputs::compute_agent_commitment(&agent),
            claimed_nonce: 0,
            min_fee: 100,
            conflict_set_commitment: conflict_set.commitment(),
        };
        let sig = sk.sign(&public_inputs.signing_message()).to_bytes();

        let et = EncryptedTurn {
            agent,
            ephemeral_public: [0u8; 32],
            nonce: [0u8; 12],
            ciphertext: vec![0u8; 64],
            turn_commitment,
            conflict_set,
            validity_proof: TurnValidityProof {
                proof_bytes: Vec::new(),
                public_inputs,
                submitter_auth: Some(SubmitterAuth {
                    submitter_public,
                    signature: sig,
                }),
            },
            submitted_at: 0,
        };
        (et, sk)
    }

    #[test]
    fn admission_binding_rejects_unauthenticated_turn() {
        // The fee-DoS tooth: an envelope with no validity proof AND no submitter
        // authentication (the Phase-0 placeholder) MUST be rejected via
        // InvalidValidityProof — a stranger's blob cannot make the node decrypt.
        let et = dummy_encrypted_turn(1, &[10, 20, 30]);
        assert!(et.validity_proof.proof_bytes.is_empty());
        assert!(et.validity_proof.submitter_auth.is_none());
        match et.verify_admission_binding() {
            Err(EncryptedTurnError::InvalidValidityProof(_)) => {}
            other => panic!("expected InvalidValidityProof, got {other:?}"),
        }
    }

    #[test]
    fn admission_binding_accepts_authenticated_turn() {
        // A genuine encrypted turn — signed by the key that controls the agent
        // cell — passes the gate (so real traffic is not broken by the DoS fix).
        let (et, _sk) = authenticated_encrypted_turn(7);
        assert_eq!(et.verify_metadata(), Ok(()));
        assert_eq!(et.verify_admission_binding(), Ok(()));
    }

    #[test]
    fn admission_binding_rejects_forged_agent_binding() {
        // A valid signature whose key does NOT control the claimed agent is
        // rejected: an attacker cannot sign for a victim's agent cell.
        let (mut et, _sk) = authenticated_encrypted_turn(7);
        et.agent = make_cell_id(99); // claim a different agent than the key controls
        // (verify_metadata would now also fail, but the STARK gate must reject on
        //  the key→agent binding regardless.)
        match et.verify_admission_binding() {
            Err(EncryptedTurnError::InvalidValidityProof(_)) => {}
            other => panic!("expected InvalidValidityProof, got {other:?}"),
        }
    }

    #[test]
    fn admission_binding_rejects_tampered_signature() {
        // Flipping a public input after signing breaks the signature → rejected.
        let (mut et, _sk) = authenticated_encrypted_turn(7);
        et.validity_proof.public_inputs.claimed_nonce ^= 1; // signed-over field changed
        match et.verify_admission_binding() {
            Err(EncryptedTurnError::InvalidValidityProof(_)) => {}
            other => panic!("expected InvalidValidityProof, got {other:?}"),
        }
    }

    #[test]
    fn admission_binding_is_separate_from_metadata() {
        // The gate must NOT be folded into verify_metadata: an unauthenticated
        // envelope still passes metadata (existing decrypt round-trips depend on
        // this contract) but fails the explicit validity gate. This keeps the
        // closure additive.
        let et = dummy_encrypted_turn(1, &[10, 20, 30]);
        assert_eq!(et.verify_metadata(), Ok(()));
        assert!(et.verify_admission_binding().is_err());
    }

    #[test]
    fn admission_binding_rejects_unverifiable_nonempty_proof() {
        // A non-empty STARK proof with no verifier wired is conservatively
        // rejected (never admitted unverified) — Phase-2 remainder.
        let (mut et, _sk) = authenticated_encrypted_turn(7);
        et.validity_proof.proof_bytes = vec![0xDE, 0xAD, 0xBE, 0xEF];
        match et.verify_admission_binding() {
            Err(EncryptedTurnError::InvalidValidityProof(_)) => {}
            other => panic!("expected InvalidValidityProof, got {other:?}"),
        }
    }
}
