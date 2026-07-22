//! Restart-safe authority for the exact FNSP-v3 receipt epoch and frame head.
//!
//! The exact accumulator head alone is not a receipt-chain authority.  This module stores the
//! persist-once epoch activation, every exact frame, and the current frame head beside the exact
//! accumulator.  Loads validate the complete frame suffix and require it to end at the exact state
//! head.  Fresh writes and idempotent replay are driven from the finalized-turn writer, so no
//! caller-authored value is ever returned as a committed head.
//!
//! The current devnet authorization policy is one node executor Ed25519 signature.  Both the
//! activation and every frame pin that executor key; recovery re-verifies every signature.  This
//! is deliberately named as a devnet policy rather than a quorum-finality claim.

use std::fmt;

use dregg_circuit::exact_nullifier_aafi::{Digest8, exact_state_commit};
use dregg_circuit::field::{BABYBEAR_P, BabyBear};
use dregg_turn::{Finality, TurnReceipt, verify_receipt_signature_with_keys};
use dregg_types::{PublicKey, Signature, verify};
use redb::{
    ReadTransaction, ReadableTable, ReadableTableMetadata, TableDefinition, WriteTransaction,
};

use crate::exact_fnsp_v3_state::{
    ExactFnspV3StateCasV1, ExactFnspV3StateHeadV1, compare_and_commit_exact_fnsp_v3_append_in,
    exact_fnsp_v3_state_head_in,
};
use crate::{PersistentStore, Result as StoreResult, StoreError};

const ACTIVATION_MAGIC: [u8; 4] = *b"F3EA";
const FRAME_MAGIC: [u8; 4] = *b"F3FR";
const WIRE_VERSION: u8 = 1;
const HEADER_LEN: usize = 8;
const SINGLETON_KEY: u8 = 0;

const ACTIVATION_HASH_DOMAIN: &str = "dregg-exact-fnsp-v3-receipt-epoch-activation-v1";
const ACTIVATION_SIGNATURE_DOMAIN: &[u8] = b"executor-exact-fnsp-v3-receipt-epoch-activation-v1:";
const FRAME_SIGNATURE_DOMAIN: &[u8] = b"executor-exact-fnsp-v3-receipt-frame-v1:";
const FRAME_HASH_DOMAIN: &str = "dregg-exact-fnsp-v3-receipt-state-frame-v1";
const ACTIVATION_SEAL_DOMAIN: &str = "dregg-exact-fnsp-v3-durable-activation-v1";
const FRAME_SEAL_DOMAIN: &str = "dregg-exact-fnsp-v3-durable-frame-v1";

const A_EPOCH: usize = HEADER_LEN;
const A_INITIAL_GENERATION: usize = A_EPOCH + 8;
const A_INITIAL_COUNT: usize = A_INITIAL_GENERATION + 8;
const A_INITIAL_ROOT: usize = A_INITIAL_COUNT + 8;
const A_INITIAL_FNS3: usize = A_INITIAL_ROOT + 32;
const A_FEDERATION: usize = A_INITIAL_FNS3 + 32;
const A_AGENT: usize = A_FEDERATION + 32;
const A_LEGACY_RECEIPT: usize = A_AGENT + 32;
const A_LEGACY_OUTER: usize = A_LEGACY_RECEIPT + 32;
const A_HASH: usize = A_LEGACY_OUTER + 32;
const A_EXECUTOR_KEY: usize = A_HASH + 32;
const A_SIGNATURE: usize = A_EXECUTOR_KEY + 32;
const A_SEAL: usize = A_SIGNATURE + 64;
pub const EXACT_FNSP_V3_ACTIVATION_V1_WIRE_LEN: usize = A_SEAL + 32;

const F_SEQUENCE: usize = HEADER_LEN;
const F_EPOCH: usize = F_SEQUENCE + 8;
const F_PREDECESSOR_TAG: usize = F_EPOCH + 8;
const F_ACTIVATION_HASH: usize = F_PREDECESSOR_TAG + 8;
const F_PREDECESSOR_HASH: usize = F_ACTIVATION_HASH + 32;
const F_FRAME_HASH: usize = F_PREDECESSOR_HASH + 32;
const F_PREVIOUS_RECEIPT: usize = F_FRAME_HASH + 32;
const F_RECEIPT_HASH: usize = F_PREVIOUS_RECEIPT + 32;
const F_FULL_PRE: usize = F_RECEIPT_HASH + 32;
const F_FULL_POST: usize = F_FULL_PRE + 32;
const F_BEFORE_COUNT: usize = F_FULL_POST + 32;
const F_BEFORE_ROOT: usize = F_BEFORE_COUNT + 8;
const F_BEFORE_FNS3: usize = F_BEFORE_ROOT + 32;
const F_AFTER_COUNT: usize = F_BEFORE_FNS3 + 32;
const F_AFTER_ROOT: usize = F_AFTER_COUNT + 8;
const F_AFTER_FNS3: usize = F_AFTER_ROOT + 32;
const F_PROOF_OUTER_BEFORE: usize = F_AFTER_FNS3 + 32;
const F_PROOF_OUTER_AFTER: usize = F_PROOF_OUTER_BEFORE + 32;
const F_ACCEPTED_STATEMENT: usize = F_PROOF_OUTER_AFTER + 32;
const F_SIGNED_SPENDING_PROOF: usize = F_ACCEPTED_STATEMENT + 32;
const F_FEDERATION: usize = F_SIGNED_SPENDING_PROOF + 32;
const F_AGENT: usize = F_FEDERATION + 32;
const F_EXECUTOR_KEY: usize = F_AGENT + 32;
const F_SIGNATURE: usize = F_EXECUTOR_KEY + 32;
const F_SEAL: usize = F_SIGNATURE + 64;
pub const EXACT_FNSP_V3_FRAME_V1_WIRE_LEN: usize = F_SEAL + 32;

pub(crate) const EXACT_FNSP_V3_ACTIVATION: TableDefinition<u8, &[u8]> =
    TableDefinition::new("exact_fnsp_v3_activation_v1");
pub(crate) const EXACT_FNSP_V3_FRAME_HEAD: TableDefinition<u8, &[u8]> =
    TableDefinition::new("exact_fnsp_v3_frame_head_v1");
pub(crate) const EXACT_FNSP_V3_FRAME_RECORDS: TableDefinition<u64, &[u8]> =
    TableDefinition::new("exact_fnsp_v3_frame_records_v1");

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ExactFnspV3DurableReceiptLinkV1 {
    EpochActivation([u8; 32]),
    ExactFrame([u8; 32]),
}

impl ExactFnspV3DurableReceiptLinkV1 {
    const fn tag(self) -> u8 {
        match self {
            Self::EpochActivation(_) => 1,
            Self::ExactFrame(_) => 2,
        }
    }

    pub const fn hash(self) -> [u8; 32] {
        match self {
            Self::EpochActivation(hash) | Self::ExactFrame(hash) => hash,
        }
    }
}

/// Structurally valid, executor-signed activation proposed to the store.
///
/// This remains untrusted until [`PersistentStore::install_exact_fnsp_v3_activation`] checks the
/// exact prefix and writes it once.  The resulting committed activation has no public constructor.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct UntrustedExactFnspV3ActivationV1 {
    epoch: u64,
    exact_initial: ExactFnspV3StateHeadV1,
    federation_id: [u8; 32],
    agent: [u8; 32],
    legacy_tip_receipt_hash: [u8; 32],
    legacy_tip_outer_commit: [u8; 32],
    activation_hash: [u8; 32],
    executor_public_key: [u8; 32],
    executor_signature: Signature,
}

impl UntrustedExactFnspV3ActivationV1 {
    #[allow(clippy::too_many_arguments)]
    pub fn authenticate_devnet_executor(
        epoch: u64,
        exact_initial: ExactFnspV3StateHeadV1,
        federation_id: [u8; 32],
        agent: [u8; 32],
        legacy_tip_receipt_hash: [u8; 32],
        legacy_tip_outer_commit: [u8; 32],
        activation_hash: [u8; 32],
        executor_public_key: [u8; 32],
        executor_signature: Signature,
    ) -> StoreResult<Self> {
        let value = Self {
            epoch,
            exact_initial,
            federation_id,
            agent,
            legacy_tip_receipt_hash,
            legacy_tip_outer_commit,
            activation_hash,
            executor_public_key,
            executor_signature,
        };
        value.validate().map_err(integrity)?;
        Ok(value)
    }

    pub const fn epoch(&self) -> u64 {
        self.epoch
    }
    pub const fn exact_initial(&self) -> ExactFnspV3StateHeadV1 {
        self.exact_initial
    }
    pub const fn federation_id(&self) -> [u8; 32] {
        self.federation_id
    }
    pub const fn agent(&self) -> [u8; 32] {
        self.agent
    }
    pub const fn legacy_tip_receipt_hash(&self) -> [u8; 32] {
        self.legacy_tip_receipt_hash
    }
    pub const fn legacy_tip_outer_commit(&self) -> [u8; 32] {
        self.legacy_tip_outer_commit
    }
    pub const fn activation_hash(&self) -> [u8; 32] {
        self.activation_hash
    }
    pub const fn executor_public_key(&self) -> [u8; 32] {
        self.executor_public_key
    }

    pub fn signature_message(activation_hash: [u8; 32]) -> Vec<u8> {
        let mut message = Vec::with_capacity(ACTIVATION_SIGNATURE_DOMAIN.len() + 32);
        message.extend_from_slice(ACTIVATION_SIGNATURE_DOMAIN);
        message.extend_from_slice(&activation_hash);
        message
    }

    fn validate(&self) -> Result<(), ExactFnspV3FrameStoreError> {
        if self.epoch == 0 {
            return Err(ExactFnspV3FrameStoreError::LegacyEpoch);
        }
        validate_digest_bytes("legacy outer commitment", self.legacy_tip_outer_commit)?;
        let computed = activation_hash(
            self.epoch,
            self.federation_id,
            self.agent,
            self.legacy_tip_receipt_hash,
            self.legacy_tip_outer_commit,
            self.exact_initial,
        );
        if computed != self.activation_hash {
            return Err(ExactFnspV3FrameStoreError::ActivationHashMismatch);
        }
        if !verify(
            &PublicKey(self.executor_public_key),
            &Self::signature_message(self.activation_hash),
            &self.executor_signature,
        ) {
            return Err(ExactFnspV3FrameStoreError::ActivationSignatureInvalid);
        }
        Ok(())
    }

    fn encode(&self) -> [u8; EXACT_FNSP_V3_ACTIVATION_V1_WIRE_LEN] {
        let mut out = [0u8; EXACT_FNSP_V3_ACTIVATION_V1_WIRE_LEN];
        out[..4].copy_from_slice(&ACTIVATION_MAGIC);
        out[4] = WIRE_VERSION;
        put_u64(&mut out, A_EPOCH, self.epoch);
        put_u64(
            &mut out,
            A_INITIAL_GENERATION,
            self.exact_initial.generation(),
        );
        put_u64(&mut out, A_INITIAL_COUNT, self.exact_initial.count());
        put_digest(&mut out, A_INITIAL_ROOT, self.exact_initial.root());
        put_digest(&mut out, A_INITIAL_FNS3, self.exact_initial.fns3());
        out[A_FEDERATION..A_AGENT].copy_from_slice(&self.federation_id);
        out[A_AGENT..A_LEGACY_RECEIPT].copy_from_slice(&self.agent);
        out[A_LEGACY_RECEIPT..A_LEGACY_OUTER].copy_from_slice(&self.legacy_tip_receipt_hash);
        out[A_LEGACY_OUTER..A_HASH].copy_from_slice(&self.legacy_tip_outer_commit);
        out[A_HASH..A_EXECUTOR_KEY].copy_from_slice(&self.activation_hash);
        out[A_EXECUTOR_KEY..A_SIGNATURE].copy_from_slice(&self.executor_public_key);
        out[A_SIGNATURE..A_SEAL].copy_from_slice(&self.executor_signature.0);
        let seal = seal(ACTIVATION_SEAL_DOMAIN, &out[..A_SEAL]);
        out[A_SEAL..].copy_from_slice(&seal);
        out
    }

    fn decode(bytes: &[u8]) -> StoreResult<Self> {
        check_wire(
            "activation",
            bytes,
            EXACT_FNSP_V3_ACTIVATION_V1_WIRE_LEN,
            ACTIVATION_MAGIC,
            A_SEAL,
            ACTIVATION_SEAL_DOMAIN,
        )?;
        let initial = decode_head(
            get_u64(bytes, A_INITIAL_GENERATION),
            get_digest(bytes, A_INITIAL_ROOT)?,
            get_u64(bytes, A_INITIAL_COUNT),
            get_digest(bytes, A_INITIAL_FNS3)?,
        )?;
        let value = Self {
            epoch: get_u64(bytes, A_EPOCH),
            exact_initial: initial,
            federation_id: take32(bytes, A_FEDERATION),
            agent: take32(bytes, A_AGENT),
            legacy_tip_receipt_hash: take32(bytes, A_LEGACY_RECEIPT),
            legacy_tip_outer_commit: take32(bytes, A_LEGACY_OUTER),
            activation_hash: take32(bytes, A_HASH),
            executor_public_key: take32(bytes, A_EXECUTOR_KEY),
            executor_signature: Signature(take64(bytes, A_SIGNATURE)),
        };
        value.validate().map_err(integrity)?;
        Ok(value)
    }
}

/// Opaque activation authority loaded from the sole validated durable row.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StoreAuthenticatedExactFnspV3ActivationV1(UntrustedExactFnspV3ActivationV1);

impl StoreAuthenticatedExactFnspV3ActivationV1 {
    pub const fn epoch(&self) -> u64 {
        self.0.epoch
    }
    pub const fn exact_initial(&self) -> ExactFnspV3StateHeadV1 {
        self.0.exact_initial
    }
    pub const fn federation_id(&self) -> [u8; 32] {
        self.0.federation_id
    }
    pub const fn agent(&self) -> [u8; 32] {
        self.0.agent
    }
    pub const fn legacy_tip_receipt_hash(&self) -> [u8; 32] {
        self.0.legacy_tip_receipt_hash
    }
    pub const fn legacy_tip_outer_commit(&self) -> [u8; 32] {
        self.0.legacy_tip_outer_commit
    }
    pub const fn activation_hash(&self) -> [u8; 32] {
        self.0.activation_hash
    }
    pub const fn executor_public_key(&self) -> [u8; 32] {
        self.0.executor_public_key
    }
}

/// Structural frame candidate.  Signature and wire shape are checked at construction and again
/// under the store writer; committed authority is returned only after atomic success.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct UntrustedExactFnspV3FrameV1 {
    sequence: u64,
    epoch: u64,
    predecessor: ExactFnspV3DurableReceiptLinkV1,
    activation_hash: [u8; 32],
    frame_hash: [u8; 32],
    predecessor_receipt_hash: [u8; 32],
    full_receipt_hash: [u8; 32],
    full_pre_state_hash: [u8; 32],
    full_post_state_hash: [u8; 32],
    exact_before: ExactFnspV3StateHeadV1,
    exact_after: ExactFnspV3StateHeadV1,
    proof_outer_before: [u8; 32],
    proof_outer_after: [u8; 32],
    accepted_statement_digest: [u8; 32],
    signed_spending_proof_digest: [u8; 32],
    federation_id: [u8; 32],
    agent: [u8; 32],
    executor_public_key: [u8; 32],
    executor_signature: Signature,
}

impl UntrustedExactFnspV3FrameV1 {
    #[allow(clippy::too_many_arguments)]
    pub fn authenticate_devnet_executor(
        epoch: u64,
        predecessor: ExactFnspV3DurableReceiptLinkV1,
        activation_hash: [u8; 32],
        frame_hash: [u8; 32],
        predecessor_receipt_hash: [u8; 32],
        full_receipt_hash: [u8; 32],
        full_pre_state_hash: [u8; 32],
        full_post_state_hash: [u8; 32],
        exact_before: ExactFnspV3StateHeadV1,
        exact_after: ExactFnspV3StateHeadV1,
        proof_outer_before: [u8; 32],
        proof_outer_after: [u8; 32],
        accepted_statement_digest: [u8; 32],
        signed_spending_proof_digest: [u8; 32],
        federation_id: [u8; 32],
        agent: [u8; 32],
        executor_public_key: [u8; 32],
        executor_signature: Signature,
    ) -> StoreResult<Self> {
        let value = Self {
            sequence: exact_before.generation(),
            epoch,
            predecessor,
            activation_hash,
            frame_hash,
            predecessor_receipt_hash,
            full_receipt_hash,
            full_pre_state_hash,
            full_post_state_hash,
            exact_before,
            exact_after,
            proof_outer_before,
            proof_outer_after,
            accepted_statement_digest,
            signed_spending_proof_digest,
            federation_id,
            agent,
            executor_public_key,
            executor_signature,
        };
        value.validate().map_err(integrity)?;
        Ok(value)
    }

    pub const fn sequence(&self) -> u64 {
        self.sequence
    }
    pub const fn epoch(&self) -> u64 {
        self.epoch
    }
    pub const fn predecessor(&self) -> ExactFnspV3DurableReceiptLinkV1 {
        self.predecessor
    }
    pub const fn activation_hash(&self) -> [u8; 32] {
        self.activation_hash
    }
    pub const fn frame_hash(&self) -> [u8; 32] {
        self.frame_hash
    }
    pub const fn predecessor_receipt_hash(&self) -> [u8; 32] {
        self.predecessor_receipt_hash
    }
    pub const fn full_receipt_hash(&self) -> [u8; 32] {
        self.full_receipt_hash
    }
    pub const fn full_pre_state_hash(&self) -> [u8; 32] {
        self.full_pre_state_hash
    }
    pub const fn full_post_state_hash(&self) -> [u8; 32] {
        self.full_post_state_hash
    }
    pub const fn exact_before(&self) -> ExactFnspV3StateHeadV1 {
        self.exact_before
    }
    pub const fn exact_after(&self) -> ExactFnspV3StateHeadV1 {
        self.exact_after
    }
    pub const fn proof_outer_before(&self) -> [u8; 32] {
        self.proof_outer_before
    }
    pub const fn proof_outer_after(&self) -> [u8; 32] {
        self.proof_outer_after
    }
    pub const fn accepted_statement_digest(&self) -> [u8; 32] {
        self.accepted_statement_digest
    }
    pub const fn signed_spending_proof_digest(&self) -> [u8; 32] {
        self.signed_spending_proof_digest
    }
    pub const fn federation_id(&self) -> [u8; 32] {
        self.federation_id
    }
    pub const fn agent(&self) -> [u8; 32] {
        self.agent
    }

    fn validate(&self) -> Result<(), ExactFnspV3FrameStoreError> {
        if self.epoch == 0 {
            return Err(ExactFnspV3FrameStoreError::LegacyEpoch);
        }
        if self.sequence != self.exact_before.generation()
            || self.exact_after.generation() != self.sequence.checked_add(1).unwrap_or(u64::MAX)
        {
            return Err(ExactFnspV3FrameStoreError::ExactStepMismatch);
        }
        if self.frame_hash == [0; 32] || self.full_receipt_hash == [0; 32] {
            return Err(ExactFnspV3FrameStoreError::ZeroHash);
        }
        validate_digest_bytes("proof outer before", self.proof_outer_before)?;
        validate_digest_bytes("proof outer after", self.proof_outer_after)?;
        if self.compute_frame_hash() != self.frame_hash {
            return Err(ExactFnspV3FrameStoreError::FrameHashMismatch);
        }
        let mut message = Vec::with_capacity(FRAME_SIGNATURE_DOMAIN.len() + 32);
        message.extend_from_slice(FRAME_SIGNATURE_DOMAIN);
        message.extend_from_slice(&self.frame_hash);
        if !verify(
            &PublicKey(self.executor_public_key),
            &message,
            &self.executor_signature,
        ) {
            return Err(ExactFnspV3FrameStoreError::FrameSignatureInvalid);
        }
        Ok(())
    }

    fn encode(&self) -> [u8; EXACT_FNSP_V3_FRAME_V1_WIRE_LEN] {
        let mut out = [0u8; EXACT_FNSP_V3_FRAME_V1_WIRE_LEN];
        out[..4].copy_from_slice(&FRAME_MAGIC);
        out[4] = WIRE_VERSION;
        put_u64(&mut out, F_SEQUENCE, self.sequence);
        put_u64(&mut out, F_EPOCH, self.epoch);
        out[F_PREDECESSOR_TAG] = self.predecessor.tag();
        out[F_ACTIVATION_HASH..F_PREDECESSOR_HASH].copy_from_slice(&self.activation_hash);
        out[F_PREDECESSOR_HASH..F_FRAME_HASH].copy_from_slice(&self.predecessor.hash());
        out[F_FRAME_HASH..F_PREVIOUS_RECEIPT].copy_from_slice(&self.frame_hash);
        out[F_PREVIOUS_RECEIPT..F_RECEIPT_HASH].copy_from_slice(&self.predecessor_receipt_hash);
        out[F_RECEIPT_HASH..F_FULL_PRE].copy_from_slice(&self.full_receipt_hash);
        out[F_FULL_PRE..F_FULL_POST].copy_from_slice(&self.full_pre_state_hash);
        out[F_FULL_POST..F_BEFORE_COUNT].copy_from_slice(&self.full_post_state_hash);
        put_u64(&mut out, F_BEFORE_COUNT, self.exact_before.count());
        put_digest(&mut out, F_BEFORE_ROOT, self.exact_before.root());
        put_digest(&mut out, F_BEFORE_FNS3, self.exact_before.fns3());
        put_u64(&mut out, F_AFTER_COUNT, self.exact_after.count());
        put_digest(&mut out, F_AFTER_ROOT, self.exact_after.root());
        put_digest(&mut out, F_AFTER_FNS3, self.exact_after.fns3());
        out[F_PROOF_OUTER_BEFORE..F_PROOF_OUTER_AFTER].copy_from_slice(&self.proof_outer_before);
        out[F_PROOF_OUTER_AFTER..F_ACCEPTED_STATEMENT].copy_from_slice(&self.proof_outer_after);
        out[F_ACCEPTED_STATEMENT..F_SIGNED_SPENDING_PROOF]
            .copy_from_slice(&self.accepted_statement_digest);
        out[F_SIGNED_SPENDING_PROOF..F_FEDERATION]
            .copy_from_slice(&self.signed_spending_proof_digest);
        out[F_FEDERATION..F_AGENT].copy_from_slice(&self.federation_id);
        out[F_AGENT..F_EXECUTOR_KEY].copy_from_slice(&self.agent);
        out[F_EXECUTOR_KEY..F_SIGNATURE].copy_from_slice(&self.executor_public_key);
        out[F_SIGNATURE..F_SEAL].copy_from_slice(&self.executor_signature.0);
        let seal = seal(FRAME_SEAL_DOMAIN, &out[..F_SEAL]);
        out[F_SEAL..].copy_from_slice(&seal);
        out
    }

    fn decode(bytes: &[u8]) -> StoreResult<Self> {
        check_wire(
            "frame",
            bytes,
            EXACT_FNSP_V3_FRAME_V1_WIRE_LEN,
            FRAME_MAGIC,
            F_SEAL,
            FRAME_SEAL_DOMAIN,
        )?;
        if bytes[F_PREDECESSOR_TAG + 1..F_ACTIVATION_HASH] != [0; 7] {
            return Err(integrity(ExactFnspV3FrameStoreError::NonZeroReserved(
                "frame predecessor",
            )));
        }
        let predecessor_hash = take32(bytes, F_PREDECESSOR_HASH);
        let predecessor = match bytes[F_PREDECESSOR_TAG] {
            1 => ExactFnspV3DurableReceiptLinkV1::EpochActivation(predecessor_hash),
            2 => ExactFnspV3DurableReceiptLinkV1::ExactFrame(predecessor_hash),
            _ => return Err(integrity(ExactFnspV3FrameStoreError::BadPredecessorTag)),
        };
        let sequence = get_u64(bytes, F_SEQUENCE);
        let value = Self {
            sequence,
            epoch: get_u64(bytes, F_EPOCH),
            predecessor,
            activation_hash: take32(bytes, F_ACTIVATION_HASH),
            frame_hash: take32(bytes, F_FRAME_HASH),
            predecessor_receipt_hash: take32(bytes, F_PREVIOUS_RECEIPT),
            full_receipt_hash: take32(bytes, F_RECEIPT_HASH),
            full_pre_state_hash: take32(bytes, F_FULL_PRE),
            full_post_state_hash: take32(bytes, F_FULL_POST),
            exact_before: decode_head(
                sequence,
                get_digest(bytes, F_BEFORE_ROOT)?,
                get_u64(bytes, F_BEFORE_COUNT),
                get_digest(bytes, F_BEFORE_FNS3)?,
            )?,
            exact_after: decode_head(
                sequence
                    .checked_add(1)
                    .ok_or_else(|| integrity(ExactFnspV3FrameStoreError::ExactStepMismatch))?,
                get_digest(bytes, F_AFTER_ROOT)?,
                get_u64(bytes, F_AFTER_COUNT),
                get_digest(bytes, F_AFTER_FNS3)?,
            )?,
            proof_outer_before: take32(bytes, F_PROOF_OUTER_BEFORE),
            proof_outer_after: take32(bytes, F_PROOF_OUTER_AFTER),
            accepted_statement_digest: take32(bytes, F_ACCEPTED_STATEMENT),
            signed_spending_proof_digest: take32(bytes, F_SIGNED_SPENDING_PROOF),
            federation_id: take32(bytes, F_FEDERATION),
            agent: take32(bytes, F_AGENT),
            executor_public_key: take32(bytes, F_EXECUTOR_KEY),
            executor_signature: Signature(take64(bytes, F_SIGNATURE)),
        };
        value.validate().map_err(integrity)?;
        Ok(value)
    }

    fn compute_frame_hash(&self) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new_derive_key(FRAME_HASH_DOMAIN);
        hasher.update(&self.epoch.to_le_bytes());
        hasher.update(&self.activation_hash);
        hasher.update(&[self.predecessor.tag()]);
        hasher.update(&self.predecessor.hash());
        hasher.update(&self.full_receipt_hash);
        hash_exact_state_point(&mut hasher, self.exact_before);
        hash_exact_state_point(&mut hasher, self.exact_after);
        hasher.update(&self.proof_outer_before);
        hasher.update(&self.proof_outer_after);
        hasher.update(&self.accepted_statement_digest);
        hasher.update(&self.signed_spending_proof_digest);
        *hasher.finalize().as_bytes()
    }
}

/// Opaque durable predecessor for the next exact frame.  There is deliberately no public
/// constructor; store commit/recovery are the only minting paths.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CommittedExactFnspV3FrameHeadV1(UntrustedExactFnspV3FrameV1);

impl CommittedExactFnspV3FrameHeadV1 {
    pub const fn epoch(&self) -> u64 {
        self.0.epoch
    }
    pub const fn activation_hash(&self) -> [u8; 32] {
        self.0.activation_hash
    }
    pub const fn frame_hash(&self) -> [u8; 32] {
        self.0.frame_hash
    }
    pub const fn full_receipt_hash(&self) -> [u8; 32] {
        self.0.full_receipt_hash
    }
    pub const fn full_post_state_hash(&self) -> [u8; 32] {
        self.0.full_post_state_hash
    }
    pub const fn exact_after(&self) -> ExactFnspV3StateHeadV1 {
        self.0.exact_after
    }
    pub const fn federation_id(&self) -> [u8; 32] {
        self.0.federation_id
    }
    pub const fn agent(&self) -> [u8; 32] {
        self.0.agent
    }

    pub(crate) fn from_verified_durable(frame: UntrustedExactFnspV3FrameV1) -> Self {
        Self(frame)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExactFnspV3FrameStoreError {
    WireLength {
        wire: &'static str,
        expected: usize,
        actual: usize,
    },
    WrongMagic(&'static str),
    UnsupportedVersion {
        wire: &'static str,
        version: u8,
    },
    NonZeroReserved(&'static str),
    SealMismatch(&'static str),
    LegacyEpoch,
    ZeroHash,
    NonCanonicalLane {
        component: &'static str,
        lane: usize,
        value: u32,
    },
    ActivationHashMismatch,
    ActivationSignatureInvalid,
    FrameHashMismatch,
    FrameSignatureInvalid,
    FrameReceiptMismatch,
    BadPredecessorTag,
    ExactStepMismatch,
    ActivationAlreadyInstalled,
    ActivationMissing,
    ActivationReplacement,
    FrameRowsWithoutActivation,
    FrameHeadWithoutRows,
    FrameRowsWithoutHead,
    FrameRecordGap {
        expected: u64,
        found: u64,
    },
    FrameCountMismatch,
    FrameHeadMismatch,
    FrameChainBreak(&'static str),
    ExactHeadMismatch,
    FrameReplayMismatch,
}

impl fmt::Display for ExactFnspV3FrameStoreError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::WireLength {
                wire,
                expected,
                actual,
            } => {
                write!(
                    f,
                    "exact FNSP-v3 {wire} wire length {actual}, expected {expected}"
                )
            }
            Self::WrongMagic(wire) => write!(f, "exact FNSP-v3 {wire} wire has wrong magic"),
            Self::UnsupportedVersion { wire, version } => {
                write!(f, "unsupported exact FNSP-v3 {wire} version {version}")
            }
            Self::NonZeroReserved(wire) => write!(f, "exact FNSP-v3 {wire} reserved bytes nonzero"),
            Self::SealMismatch(wire) => write!(f, "exact FNSP-v3 {wire} seal mismatch"),
            Self::LegacyEpoch => f.write_str("exact FNSP-v3 activation epoch must be nonzero"),
            Self::ZeroHash => f.write_str("exact FNSP-v3 frame contains a zero identity hash"),
            Self::NonCanonicalLane {
                component,
                lane,
                value,
            } => write!(
                f,
                "exact FNSP-v3 {component} lane {lane} is non-canonical: {value}"
            ),
            Self::ActivationHashMismatch => f.write_str("exact FNSP-v3 activation hash mismatch"),
            Self::ActivationSignatureInvalid => {
                f.write_str("exact FNSP-v3 devnet activation signature invalid")
            }
            Self::FrameHashMismatch => {
                f.write_str("exact FNSP-v3 durable frame hash/preimage mismatch")
            }
            Self::FrameSignatureInvalid => {
                f.write_str("exact FNSP-v3 durable frame signature invalid")
            }
            Self::FrameReceiptMismatch => {
                f.write_str("exact FNSP-v3 durable frame disagrees with byte-exact receipt")
            }
            Self::BadPredecessorTag => f.write_str("exact FNSP-v3 frame predecessor tag invalid"),
            Self::ExactStepMismatch => f.write_str("exact FNSP-v3 frame exact step mismatch"),
            Self::ActivationAlreadyInstalled => {
                f.write_str("exact FNSP-v3 activation is already installed")
            }
            Self::ActivationMissing => f.write_str("exact FNSP-v3 activation is missing"),
            Self::ActivationReplacement => {
                f.write_str("exact FNSP-v3 activation replacement refused")
            }
            Self::FrameRowsWithoutActivation => {
                f.write_str("exact FNSP-v3 frame rows exist without activation")
            }
            Self::FrameHeadWithoutRows => {
                f.write_str("exact FNSP-v3 frame head exists without rows")
            }
            Self::FrameRowsWithoutHead => {
                f.write_str("exact FNSP-v3 frame rows exist without head")
            }
            Self::FrameRecordGap { expected, found } => {
                write!(
                    f,
                    "exact FNSP-v3 frame gap: expected {expected}, found {found}"
                )
            }
            Self::FrameCountMismatch => {
                f.write_str("exact FNSP-v3 frame count/exact head mismatch")
            }
            Self::FrameHeadMismatch => {
                f.write_str("exact FNSP-v3 frame head disagrees with frame rows")
            }
            Self::FrameChainBreak(what) => {
                write!(f, "exact FNSP-v3 durable frame chain break at {what}")
            }
            Self::ExactHeadMismatch => {
                f.write_str("exact FNSP-v3 durable frame/exact head mismatch")
            }
            Self::FrameReplayMismatch => f.write_str("exact FNSP-v3 durable frame replay mismatch"),
        }
    }
}

impl std::error::Error for ExactFnspV3FrameStoreError {}

struct ValidatedFrameSnapshot {
    activation: Option<UntrustedExactFnspV3ActivationV1>,
    frames: Vec<UntrustedExactFnspV3FrameV1>,
}

impl PersistentStore {
    /// Boot gate: a partial exact state/activation/frame image is an integrity failure, never an
    /// implicit rollback to legacy mode.
    pub(crate) fn validate_exact_fnsp_v3_receipt_authority_on_open(&self) -> StoreResult<()> {
        let read = self.db.begin_read()?;
        match crate::exact_fnsp_v3_state::load_state_head_from_read(&read)? {
            Some(exact_head) => {
                load_snapshot_from_read(&read, exact_head)?;
            }
            None => ensure_frame_authority_absent(&read)?,
        }
        Ok(())
    }

    /// Persist the devnet-authorized flag day once, welded to the exact prefix reconstructed by
    /// the store.  Replacement and activation after any frame row fail closed.
    pub fn install_exact_fnsp_v3_activation(
        &self,
        activation: UntrustedExactFnspV3ActivationV1,
    ) -> StoreResult<StoreAuthenticatedExactFnspV3ActivationV1> {
        activation.validate().map_err(integrity)?;
        let write = self.db.begin_write()?;
        crate::commit_log::validate_exact_fnsp_v3_faithful_prefix_in(&write)?;
        let exact_head = exact_fnsp_v3_state_head_in(&write)?;
        let snapshot = load_snapshot_from_write(&write, exact_head)?;
        if snapshot.activation.is_some() {
            return Err(integrity(
                ExactFnspV3FrameStoreError::ActivationAlreadyInstalled,
            ));
        }
        if !snapshot.frames.is_empty() {
            return Err(integrity(
                ExactFnspV3FrameStoreError::FrameRowsWithoutActivation,
            ));
        }
        if activation.exact_initial != exact_head {
            return Err(integrity(ExactFnspV3FrameStoreError::ExactHeadMismatch));
        }
        {
            let mut table = write.open_table(EXACT_FNSP_V3_ACTIVATION)?;
            let encoded = activation.encode();
            table.insert(SINGLETON_KEY, encoded.as_slice())?;
        }
        write.commit()?;
        Ok(StoreAuthenticatedExactFnspV3ActivationV1(activation))
    }

    pub fn exact_fnsp_v3_activation(
        &self,
    ) -> StoreResult<Option<StoreAuthenticatedExactFnspV3ActivationV1>> {
        let read = self.db.begin_read()?;
        let exact_head = match crate::exact_fnsp_v3_state::load_state_head_from_read(&read)? {
            Some(head) => head,
            None => {
                ensure_frame_authority_absent(&read)?;
                return Ok(None);
            }
        };
        Ok(load_snapshot_from_read(&read, exact_head)?
            .activation
            .map(StoreAuthenticatedExactFnspV3ActivationV1))
    }

    pub fn exact_fnsp_v3_committed_frame_head(
        &self,
    ) -> StoreResult<Option<CommittedExactFnspV3FrameHeadV1>> {
        let read = self.db.begin_read()?;
        let exact_head = match crate::exact_fnsp_v3_state::load_state_head_from_read(&read)? {
            Some(head) => head,
            None => {
                ensure_frame_authority_absent(&read)?;
                return Ok(None);
            }
        };
        let snapshot = load_snapshot_from_read(&read, exact_head)?;
        Ok(snapshot
            .frames
            .last()
            .cloned()
            .map(CommittedExactFnspV3FrameHeadV1))
    }
}

fn ensure_frame_authority_absent(read: &ReadTransaction) -> StoreResult<()> {
    let activation = read.open_table(EXACT_FNSP_V3_ACTIVATION)?;
    let head = read.open_table(EXACT_FNSP_V3_FRAME_HEAD)?;
    let records = read.open_table(EXACT_FNSP_V3_FRAME_RECORDS)?;
    if activation.len()? != 0 || head.len()? != 0 || records.len()? != 0 {
        return Err(integrity(
            ExactFnspV3FrameStoreError::FrameRowsWithoutActivation,
        ));
    }
    Ok(())
}

/// Refuse exact-state bootstrap over a partial/corrupt receipt authority.
pub(crate) fn ensure_frame_authority_absent_in_write(write: &WriteTransaction) -> StoreResult<()> {
    let activation = write.open_table(EXACT_FNSP_V3_ACTIVATION)?;
    let head = write.open_table(EXACT_FNSP_V3_FRAME_HEAD)?;
    let records = write.open_table(EXACT_FNSP_V3_FRAME_RECORDS)?;
    if activation.len()? != 0 || head.len()? != 0 || records.len()? != 0 {
        return Err(integrity(
            ExactFnspV3FrameStoreError::FrameRowsWithoutActivation,
        ));
    }
    Ok(())
}

pub(crate) fn stage_exact_fnsp_v3_frame_in(
    write: WriteTransaction,
    exact: ExactFnspV3StateCasV1,
    frame: UntrustedExactFnspV3FrameV1,
) -> StoreResult<(WriteTransaction, UntrustedExactFnspV3FrameV1)> {
    frame.validate().map_err(integrity)?;
    let exact_head = exact_fnsp_v3_state_head_in(&write)?;
    let snapshot = load_snapshot_from_write(&write, exact_head)?;
    let activation = snapshot
        .activation
        .ok_or_else(|| integrity(ExactFnspV3FrameStoreError::ActivationMissing))?;
    validate_frame_against_snapshot(&frame, &activation, &snapshot.frames, exact, false)?;
    let receipts = collect_receipts(&write.open_table(crate::tables::RECEIPT_CHAIN)?)?;
    validate_frame_receipt(&frame, &receipts)?;
    let (write, successor) = compare_and_commit_exact_fnsp_v3_append_in(write, exact)?;
    if successor != frame.exact_after {
        return Err(integrity(ExactFnspV3FrameStoreError::ExactHeadMismatch));
    }
    {
        let mut records = write.open_table(EXACT_FNSP_V3_FRAME_RECORDS)?;
        let mut head = write.open_table(EXACT_FNSP_V3_FRAME_HEAD)?;
        if records.get(frame.sequence)?.is_some() {
            return Err(integrity(ExactFnspV3FrameStoreError::FrameReplayMismatch));
        }
        let encoded = frame.encode();
        records.insert(frame.sequence, encoded.as_slice())?;
        head.insert(SINGLETON_KEY, encoded.as_slice())?;
    }
    Ok((write, frame))
}

pub(crate) fn verify_replayed_exact_fnsp_v3_frame_in(
    write: &WriteTransaction,
    exact: ExactFnspV3StateCasV1,
    frame: &UntrustedExactFnspV3FrameV1,
) -> StoreResult<()> {
    frame.validate().map_err(integrity)?;
    let exact_head = exact_fnsp_v3_state_head_in(write)?;
    let snapshot = load_snapshot_from_write(write, exact_head)?;
    let activation = snapshot
        .activation
        .ok_or_else(|| integrity(ExactFnspV3FrameStoreError::ActivationMissing))?;
    validate_frame_against_snapshot(frame, &activation, &snapshot.frames, exact, true)
}

fn validate_frame_against_snapshot(
    frame: &UntrustedExactFnspV3FrameV1,
    activation: &UntrustedExactFnspV3ActivationV1,
    frames: &[UntrustedExactFnspV3FrameV1],
    exact: ExactFnspV3StateCasV1,
    replay: bool,
) -> StoreResult<()> {
    if frame.exact_before != exact.expected() || frame.exact_after != exact.successor() {
        return Err(integrity(ExactFnspV3FrameStoreError::ExactHeadMismatch));
    }
    if frame.epoch != activation.epoch
        || frame.activation_hash != activation.activation_hash
        || frame.federation_id != activation.federation_id
        || frame.agent != activation.agent
        || frame.executor_public_key != activation.executor_public_key
    {
        return Err(integrity(ExactFnspV3FrameStoreError::ActivationReplacement));
    }
    if replay {
        let offset = frame
            .sequence
            .checked_sub(activation.exact_initial.generation())
            .and_then(|value| usize::try_from(value).ok())
            .ok_or_else(|| integrity(ExactFnspV3FrameStoreError::FrameReplayMismatch))?;
        if frames.get(offset) != Some(frame) {
            return Err(integrity(ExactFnspV3FrameStoreError::FrameReplayMismatch));
        }
        return Ok(());
    }
    let (expected_link, expected_receipt, expected_pre, expected_exact) = match frames.last() {
        Some(previous) => (
            ExactFnspV3DurableReceiptLinkV1::ExactFrame(previous.frame_hash),
            previous.full_receipt_hash,
            previous.full_post_state_hash,
            previous.exact_after,
        ),
        None => (
            ExactFnspV3DurableReceiptLinkV1::EpochActivation(activation.activation_hash),
            activation.legacy_tip_receipt_hash,
            activation.legacy_tip_outer_commit,
            activation.exact_initial,
        ),
    };
    if frame.predecessor != expected_link {
        return Err(integrity(ExactFnspV3FrameStoreError::FrameChainBreak(
            "frame predecessor",
        )));
    }
    if frame.predecessor_receipt_hash != expected_receipt {
        return Err(integrity(ExactFnspV3FrameStoreError::FrameChainBreak(
            "full receipt predecessor",
        )));
    }
    if frame.full_pre_state_hash != expected_pre {
        return Err(integrity(ExactFnspV3FrameStoreError::FrameChainBreak(
            "full state predecessor",
        )));
    }
    if frame.exact_before != expected_exact {
        return Err(integrity(ExactFnspV3FrameStoreError::FrameChainBreak(
            "exact state predecessor",
        )));
    }
    Ok(())
}

fn load_snapshot_from_read(
    read: &ReadTransaction,
    exact_head: ExactFnspV3StateHeadV1,
) -> StoreResult<ValidatedFrameSnapshot> {
    let activation = collect_singleton(&read.open_table(EXACT_FNSP_V3_ACTIVATION)?)?;
    let head = collect_singleton(&read.open_table(EXACT_FNSP_V3_FRAME_HEAD)?)?;
    let records = collect_records(&read.open_table(EXACT_FNSP_V3_FRAME_RECORDS)?)?;
    let receipts = collect_receipts(&read.open_table(crate::tables::RECEIPT_CHAIN)?)?;
    validate_snapshot(activation, head, records, receipts, exact_head)
}

fn load_snapshot_from_write(
    write: &WriteTransaction,
    exact_head: ExactFnspV3StateHeadV1,
) -> StoreResult<ValidatedFrameSnapshot> {
    let activation = collect_singleton(&write.open_table(EXACT_FNSP_V3_ACTIVATION)?)?;
    let head = collect_singleton(&write.open_table(EXACT_FNSP_V3_FRAME_HEAD)?)?;
    let records = collect_records(&write.open_table(EXACT_FNSP_V3_FRAME_RECORDS)?)?;
    let receipts = collect_receipts(&write.open_table(crate::tables::RECEIPT_CHAIN)?)?;
    validate_snapshot(activation, head, records, receipts, exact_head)
}

fn collect_singleton(
    table: &impl ReadableTable<u8, &'static [u8]>,
) -> StoreResult<Option<Vec<u8>>> {
    let mut rows = table.iter()?;
    let Some(first) = rows.next() else {
        return Ok(None);
    };
    let (key, value) = first?;
    if key.value() != SINGLETON_KEY || rows.next().is_some() {
        return Err(integrity(ExactFnspV3FrameStoreError::FrameHeadMismatch));
    }
    Ok(Some(value.value().to_vec()))
}

fn collect_records(
    table: &impl ReadableTable<u64, &'static [u8]>,
) -> StoreResult<Vec<(u64, Vec<u8>)>> {
    table
        .iter()?
        .map(|entry| {
            let (key, value) = entry?;
            Ok((key.value(), value.value().to_vec()))
        })
        .collect()
}

fn collect_receipts(table: &impl ReadableTable<u64, &'static [u8]>) -> StoreResult<Vec<Vec<u8>>> {
    let mut expected = 0u64;
    let mut receipts = Vec::new();
    for entry in table.iter()? {
        let (key, value) = entry?;
        if key.value() != expected {
            return Err(integrity(ExactFnspV3FrameStoreError::FrameReceiptMismatch));
        }
        receipts.push(value.value().to_vec());
        expected = expected
            .checked_add(1)
            .ok_or_else(|| integrity(ExactFnspV3FrameStoreError::FrameReceiptMismatch))?;
    }
    Ok(receipts)
}

fn validate_frame_receipt(
    frame: &UntrustedExactFnspV3FrameV1,
    receipt_rows: &[Vec<u8>],
) -> StoreResult<()> {
    let mut matching = None;
    for encoded in receipt_rows {
        let receipt: TurnReceipt = postcard::from_bytes(encoded)
            .map_err(|_| integrity(ExactFnspV3FrameStoreError::FrameReceiptMismatch))?;
        if receipt.receipt_hash() == frame.full_receipt_hash {
            if matching.replace(receipt).is_some() {
                return Err(integrity(ExactFnspV3FrameStoreError::FrameReceiptMismatch));
            }
        }
    }
    let receipt =
        matching.ok_or_else(|| integrity(ExactFnspV3FrameStoreError::FrameReceiptMismatch))?;
    if receipt.finality != Finality::Final
        || receipt.previous_receipt_hash != Some(frame.predecessor_receipt_hash)
        || receipt.pre_state_hash != frame.full_pre_state_hash
        || receipt.post_state_hash != frame.full_post_state_hash
        || receipt.federation_id != frame.federation_id
        || receipt.agent.0 != frame.agent
        || verify_receipt_signature_with_keys(&receipt, &[frame.executor_public_key]).is_err()
    {
        return Err(integrity(ExactFnspV3FrameStoreError::FrameReceiptMismatch));
    }
    Ok(())
}

fn validate_snapshot(
    activation_bytes: Option<Vec<u8>>,
    head_bytes: Option<Vec<u8>>,
    record_rows: Vec<(u64, Vec<u8>)>,
    receipt_rows: Vec<Vec<u8>>,
    exact_head: ExactFnspV3StateHeadV1,
) -> StoreResult<ValidatedFrameSnapshot> {
    let Some(activation_bytes) = activation_bytes else {
        if head_bytes.is_some() || !record_rows.is_empty() {
            return Err(integrity(
                ExactFnspV3FrameStoreError::FrameRowsWithoutActivation,
            ));
        }
        return Ok(ValidatedFrameSnapshot {
            activation: None,
            frames: Vec::new(),
        });
    };
    let activation = UntrustedExactFnspV3ActivationV1::decode(&activation_bytes)?;
    let expected_count = exact_head
        .generation()
        .checked_sub(activation.exact_initial.generation())
        .ok_or_else(|| integrity(ExactFnspV3FrameStoreError::FrameCountMismatch))?;
    if usize::try_from(expected_count).ok() != Some(record_rows.len()) {
        return Err(integrity(ExactFnspV3FrameStoreError::FrameCountMismatch));
    }
    if record_rows.is_empty() {
        if head_bytes.is_some() {
            return Err(integrity(ExactFnspV3FrameStoreError::FrameHeadWithoutRows));
        }
        if exact_head != activation.exact_initial {
            return Err(integrity(ExactFnspV3FrameStoreError::ExactHeadMismatch));
        }
        return Ok(ValidatedFrameSnapshot {
            activation: Some(activation),
            frames: Vec::new(),
        });
    }
    let Some(head_bytes) = head_bytes else {
        return Err(integrity(ExactFnspV3FrameStoreError::FrameRowsWithoutHead));
    };
    let mut frames: Vec<UntrustedExactFnspV3FrameV1> = Vec::with_capacity(record_rows.len());
    for (offset, (key, bytes)) in record_rows.into_iter().enumerate() {
        let expected = activation
            .exact_initial
            .generation()
            .checked_add(
                u64::try_from(offset)
                    .map_err(|_| integrity(ExactFnspV3FrameStoreError::FrameCountMismatch))?,
            )
            .ok_or_else(|| integrity(ExactFnspV3FrameStoreError::FrameCountMismatch))?;
        if key != expected {
            return Err(integrity(ExactFnspV3FrameStoreError::FrameRecordGap {
                expected,
                found: key,
            }));
        }
        let frame = UntrustedExactFnspV3FrameV1::decode(&bytes)?;
        if frame.sequence != key {
            return Err(integrity(ExactFnspV3FrameStoreError::FrameRecordGap {
                expected: key,
                found: frame.sequence,
            }));
        }
        let (link, receipt, pre, exact) = match frames.last() {
            Some(previous) => (
                ExactFnspV3DurableReceiptLinkV1::ExactFrame(previous.frame_hash),
                previous.full_receipt_hash,
                previous.full_post_state_hash,
                previous.exact_after,
            ),
            None => (
                ExactFnspV3DurableReceiptLinkV1::EpochActivation(activation.activation_hash),
                activation.legacy_tip_receipt_hash,
                activation.legacy_tip_outer_commit,
                activation.exact_initial,
            ),
        };
        if frame.epoch != activation.epoch
            || frame.activation_hash != activation.activation_hash
            || frame.federation_id != activation.federation_id
            || frame.agent != activation.agent
            || frame.executor_public_key != activation.executor_public_key
            || frame.predecessor != link
            || frame.predecessor_receipt_hash != receipt
            || frame.full_pre_state_hash != pre
            || frame.exact_before != exact
        {
            return Err(integrity(ExactFnspV3FrameStoreError::FrameChainBreak(
                "recovery",
            )));
        }
        validate_frame_receipt(&frame, &receipt_rows)?;
        frames.push(frame);
    }
    let last = frames.last().expect("nonempty frame rows");
    if last.encode().as_slice() != head_bytes.as_slice() {
        return Err(integrity(ExactFnspV3FrameStoreError::FrameHeadMismatch));
    }
    if last.exact_after != exact_head {
        return Err(integrity(ExactFnspV3FrameStoreError::ExactHeadMismatch));
    }
    Ok(ValidatedFrameSnapshot {
        activation: Some(activation),
        frames,
    })
}

fn activation_hash(
    epoch: u64,
    federation_id: [u8; 32],
    agent: [u8; 32],
    legacy_tip_receipt_hash: [u8; 32],
    legacy_tip_outer_commit: [u8; 32],
    exact_initial: ExactFnspV3StateHeadV1,
) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key(ACTIVATION_HASH_DOMAIN);
    hasher.update(&epoch.to_le_bytes());
    hasher.update(&federation_id);
    hasher.update(&agent);
    hasher.update(&legacy_tip_receipt_hash);
    hasher.update(&legacy_tip_outer_commit);
    hasher.update(&digest_bytes(exact_initial.root()));
    hasher.update(&exact_initial.count().to_le_bytes());
    hasher.update(&digest_bytes(exact_initial.fns3()));
    *hasher.finalize().as_bytes()
}

fn decode_head(
    generation: u64,
    root: Digest8,
    count: u64,
    fns3: Digest8,
) -> StoreResult<ExactFnspV3StateHeadV1> {
    let head = ExactFnspV3StateHeadV1::try_from_runtime(generation, root, count, fns3)
        .map_err(|error| StoreError::Integrity(error.to_string()))?;
    if exact_state_commit(head.root(), head.count()) != head.fns3() {
        return Err(integrity(ExactFnspV3FrameStoreError::ExactHeadMismatch));
    }
    Ok(head)
}

fn check_wire(
    wire: &'static str,
    bytes: &[u8],
    expected: usize,
    magic: [u8; 4],
    seal_offset: usize,
    seal_domain: &'static str,
) -> StoreResult<()> {
    if bytes.len() != expected {
        return Err(integrity(ExactFnspV3FrameStoreError::WireLength {
            wire,
            expected,
            actual: bytes.len(),
        }));
    }
    if bytes[..4] != magic {
        return Err(integrity(ExactFnspV3FrameStoreError::WrongMagic(wire)));
    }
    if bytes[4] != WIRE_VERSION {
        return Err(integrity(ExactFnspV3FrameStoreError::UnsupportedVersion {
            wire,
            version: bytes[4],
        }));
    }
    if bytes[5..HEADER_LEN] != [0; 3] {
        return Err(integrity(ExactFnspV3FrameStoreError::NonZeroReserved(wire)));
    }
    if bytes[seal_offset..] != seal(seal_domain, &bytes[..seal_offset]) {
        return Err(integrity(ExactFnspV3FrameStoreError::SealMismatch(wire)));
    }
    Ok(())
}

fn seal(domain: &'static str, bytes: &[u8]) -> [u8; 32] {
    *blake3::Hasher::new_derive_key(domain)
        .update(bytes)
        .finalize()
        .as_bytes()
}

fn validate_digest_bytes(
    component: &'static str,
    bytes: [u8; 32],
) -> Result<(), ExactFnspV3FrameStoreError> {
    for (lane, chunk) in bytes.chunks_exact(4).enumerate() {
        let value = u32::from_le_bytes(chunk.try_into().expect("four bytes"));
        if value >= BABYBEAR_P {
            return Err(ExactFnspV3FrameStoreError::NonCanonicalLane {
                component,
                lane,
                value,
            });
        }
    }
    Ok(())
}

fn put_u64(out: &mut [u8], offset: usize, value: u64) {
    out[offset..offset + 8].copy_from_slice(&value.to_le_bytes());
}

fn get_u64(bytes: &[u8], offset: usize) -> u64 {
    u64::from_le_bytes(bytes[offset..offset + 8].try_into().expect("eight bytes"))
}

fn put_digest(out: &mut [u8], offset: usize, digest: Digest8) {
    out[offset..offset + 32].copy_from_slice(&digest_bytes(digest));
}

fn get_digest(bytes: &[u8], offset: usize) -> StoreResult<Digest8> {
    let bytes = take32(bytes, offset);
    validate_digest_bytes("state digest", bytes).map_err(integrity)?;
    Ok(std::array::from_fn(|lane| {
        let start = lane * 4;
        BabyBear::from_canonical(u32::from_le_bytes(
            bytes[start..start + 4].try_into().expect("four bytes"),
        ))
    }))
}

fn digest_bytes(digest: Digest8) -> [u8; 32] {
    let mut out = [0u8; 32];
    for (chunk, lane) in out.chunks_exact_mut(4).zip(digest) {
        chunk.copy_from_slice(&lane.as_u32().to_le_bytes());
    }
    out
}

fn hash_exact_state_point(hasher: &mut blake3::Hasher, point: ExactFnspV3StateHeadV1) {
    hasher.update(&digest_bytes(point.root()));
    hasher.update(&point.count().to_le_bytes());
    hasher.update(&digest_bytes(point.fns3()));
}

fn take32(bytes: &[u8], offset: usize) -> [u8; 32] {
    bytes[offset..offset + 32].try_into().expect("32 bytes")
}

fn take64(bytes: &[u8], offset: usize) -> [u8; 64] {
    bytes[offset..offset + 64].try_into().expect("64 bytes")
}

fn integrity(error: ExactFnspV3FrameStoreError) -> StoreError {
    StoreError::Integrity(error.to_string())
}

#[cfg(test)]
mod tests {
    use super::*;

    use dregg_types::{SigningKey, generate_keypair, sign};

    fn setup_store() -> (PersistentStore, ExactFnspV3StateHeadV1) {
        let store = PersistentStore::open_in_memory().expect("store");
        let head = store
            .initialize_exact_fnsp_v3_state(std::iter::empty())
            .expect("exact genesis");
        (store, head)
    }

    fn activation_candidate(
        initial: ExactFnspV3StateHeadV1,
        key: &SigningKey,
        public: PublicKey,
    ) -> UntrustedExactFnspV3ActivationV1 {
        let epoch = 7;
        let federation = [0x21; 32];
        let agent = [0x22; 32];
        let legacy_receipt = [0x23; 32];
        let legacy_outer = [0; 32];
        let hash = activation_hash(
            epoch,
            federation,
            agent,
            legacy_receipt,
            legacy_outer,
            initial,
        );
        let signature = sign(
            key,
            &UntrustedExactFnspV3ActivationV1::signature_message(hash),
        );
        UntrustedExactFnspV3ActivationV1::authenticate_devnet_executor(
            epoch,
            initial,
            federation,
            agent,
            legacy_receipt,
            legacy_outer,
            hash,
            public.0,
            signature,
        )
        .expect("signed activation")
    }

    fn frame_candidate(
        store: &PersistentStore,
        activation: &UntrustedExactFnspV3ActivationV1,
        exact: ExactFnspV3StateCasV1,
        key: &SigningKey,
        tag: u8,
    ) -> UntrustedExactFnspV3FrameV1 {
        let post_state_hash = [tag.wrapping_add(2); 32];
        let mut receipt = TurnReceipt {
            turn_hash: [tag; 32],
            forest_hash: [tag.wrapping_add(1); 32],
            pre_state_hash: activation.legacy_tip_outer_commit,
            post_state_hash,
            agent: dregg_cell::CellId(activation.agent),
            federation_id: activation.federation_id,
            previous_receipt_hash: Some(activation.legacy_tip_receipt_hash),
            finality: Finality::Final,
            ..TurnReceipt::default()
        };
        receipt.executor_signature = Some(
            sign(key, &receipt.canonical_executor_signed_message())
                .0
                .to_vec(),
        );
        let proof_outer_before = [0; 32];
        let proof_outer_after = [0; 32];
        let accepted_statement_digest = [tag.wrapping_add(3); 32];
        let signed_spending_proof_digest = [tag.wrapping_add(4); 32];
        let mut unsigned = UntrustedExactFnspV3FrameV1 {
            sequence: exact.expected().generation(),
            epoch: activation.epoch,
            predecessor: ExactFnspV3DurableReceiptLinkV1::EpochActivation(
                activation.activation_hash,
            ),
            activation_hash: activation.activation_hash,
            frame_hash: [0; 32],
            predecessor_receipt_hash: activation.legacy_tip_receipt_hash,
            full_receipt_hash: receipt.receipt_hash(),
            full_pre_state_hash: activation.legacy_tip_outer_commit,
            full_post_state_hash: post_state_hash,
            exact_before: exact.expected(),
            exact_after: exact.successor(),
            proof_outer_before,
            proof_outer_after,
            accepted_statement_digest,
            signed_spending_proof_digest,
            federation_id: activation.federation_id,
            agent: activation.agent,
            executor_public_key: activation.executor_public_key,
            executor_signature: Signature([0; 64]),
        };
        let frame_hash = unsigned.compute_frame_hash();
        let mut message = Vec::from(FRAME_SIGNATURE_DOMAIN);
        message.extend_from_slice(&frame_hash);
        let signature = sign(key, &message);
        unsigned.frame_hash = frame_hash;
        unsigned.executor_signature = signature;
        store
            .append_receipt_chain_entry(
                store.receipt_chain_len().expect("receipt len"),
                &postcard::to_stdvec(&receipt).expect("encode receipt"),
            )
            .expect("append receipt");
        UntrustedExactFnspV3FrameV1::authenticate_devnet_executor(
            activation.epoch,
            ExactFnspV3DurableReceiptLinkV1::EpochActivation(activation.activation_hash),
            activation.activation_hash,
            frame_hash,
            activation.legacy_tip_receipt_hash,
            receipt.receipt_hash(),
            activation.legacy_tip_outer_commit,
            post_state_hash,
            exact.expected(),
            exact.successor(),
            proof_outer_before,
            proof_outer_after,
            accepted_statement_digest,
            signed_spending_proof_digest,
            activation.federation_id,
            activation.agent,
            activation.executor_public_key,
            signature,
        )
        .expect("signed frame")
    }

    #[test]
    fn activation_frame_and_head_restart_as_one_validated_chain() {
        let directory = tempfile::tempdir().expect("tempdir");
        let path = directory.path().join("exact-frame.redb");
        let expected_hash;
        {
            let store = PersistentStore::open(&path).expect("store");
            let initial = store
                .initialize_exact_fnsp_v3_state(std::iter::empty())
                .expect("genesis");
            let (key, public) = generate_keypair();
            let activation = activation_candidate(initial, &key, public);
            store
                .install_exact_fnsp_v3_activation(activation.clone())
                .expect("persist activation");
            let exact = store
                .prepare_exact_fnsp_v3_append([0x31; 32], 31)
                .expect("prepare");
            let frame = frame_candidate(&store, &activation, exact, &key, 0x41);
            expected_hash = frame.frame_hash();
            let write = store.db.begin_write().expect("writer");
            let (write, staged) =
                stage_exact_fnsp_v3_frame_in(write, exact, frame).expect("stage exact and frame");
            assert_eq!(staged.frame_hash(), expected_hash);
            write.commit().expect("atomic commit");
        }

        let reopened = PersistentStore::open(&path).expect("reopen");
        let activation = reopened
            .exact_fnsp_v3_activation()
            .expect("activation load")
            .expect("activated");
        let head = reopened
            .exact_fnsp_v3_committed_frame_head()
            .expect("frame load")
            .expect("committed frame");
        assert_eq!(activation.epoch(), 7);
        assert_eq!(head.frame_hash(), expected_hash);
        assert_eq!(
            head.exact_after(),
            reopened
                .exact_fnsp_v3_state_head()
                .expect("exact load")
                .expect("exact head")
        );
    }

    #[test]
    fn competing_frame_writer_and_mixed_epoch_fail_without_mutation() {
        let (store, initial) = setup_store();
        let (key, public) = generate_keypair();
        let activation = activation_candidate(initial, &key, public);
        store
            .install_exact_fnsp_v3_activation(activation.clone())
            .expect("activation");
        let exact = store
            .prepare_exact_fnsp_v3_append([0x51; 32], 51)
            .expect("prepare");
        let winner = frame_candidate(&store, &activation, exact, &key, 0x52);
        let stale = frame_candidate(&store, &activation, exact, &key, 0x53);
        let write = store.db.begin_write().expect("writer");
        let (write, winner) = stage_exact_fnsp_v3_frame_in(write, exact, winner).expect("winner");
        write.commit().expect("commit winner");

        let write = store.db.begin_write().expect("stale writer");
        assert!(stage_exact_fnsp_v3_frame_in(write, exact, stale).is_err());
        assert_eq!(
            store
                .exact_fnsp_v3_committed_frame_head()
                .expect("head")
                .expect("winner")
                .frame_hash(),
            winner.frame_hash()
        );

        let next = store
            .prepare_exact_fnsp_v3_append([0x54; 32], 54)
            .expect("next");
        let mut mixed = frame_candidate(&store, &activation, next, &key, 0x55);
        mixed.epoch += 1;
        let write = store.db.begin_write().expect("mixed writer");
        assert!(stage_exact_fnsp_v3_frame_in(write, next, mixed).is_err());
    }

    #[test]
    fn missing_activation_or_head_refuses_recovery() {
        let (store, initial) = setup_store();
        let (key, public) = generate_keypair();
        let activation = activation_candidate(initial, &key, public);
        store
            .install_exact_fnsp_v3_activation(activation.clone())
            .expect("activation");
        let exact = store
            .prepare_exact_fnsp_v3_append([0x61; 32], 61)
            .expect("prepare");
        let frame = frame_candidate(&store, &activation, exact, &key, 0x62);
        let write = store.db.begin_write().expect("writer");
        let (write, _) = stage_exact_fnsp_v3_frame_in(write, exact, frame).expect("frame");
        write.commit().expect("commit");

        let write = store.db.begin_write().expect("corrupt writer");
        write
            .open_table(EXACT_FNSP_V3_FRAME_HEAD)
            .expect("head table")
            .remove(SINGLETON_KEY)
            .expect("remove head");
        write.commit().expect("commit corruption");
        assert!(store.exact_fnsp_v3_committed_frame_head().is_err());

        // Restore the byte-identical head, then remove only the activation.  Recovery must not
        // reinterpret the remaining signed frame chain as a self-authorizing epoch.
        let write = store.db.begin_write().expect("second corrupt writer");
        let encoded = {
            let records = write
                .open_table(EXACT_FNSP_V3_FRAME_RECORDS)
                .expect("records");
            records
                .get(exact.expected().generation())
                .expect("read row")
                .expect("frame row")
                .value()
                .to_vec()
        };
        write
            .open_table(EXACT_FNSP_V3_FRAME_HEAD)
            .expect("head table")
            .insert(SINGLETON_KEY, encoded.as_slice())
            .expect("restore head");
        write
            .open_table(EXACT_FNSP_V3_ACTIVATION)
            .expect("activation table")
            .remove(SINGLETON_KEY)
            .expect("remove activation");
        write.commit().expect("commit missing activation");
        assert!(store.exact_fnsp_v3_activation().is_err());
    }

    #[test]
    fn missing_frame_head_refuses_store_reopen() {
        let directory = tempfile::tempdir().expect("tempdir");
        let path = directory.path().join("missing-frame-head.redb");
        {
            let store = PersistentStore::open(&path).expect("store");
            let initial = store
                .initialize_exact_fnsp_v3_state(std::iter::empty())
                .expect("genesis");
            let (key, public) = generate_keypair();
            let activation = activation_candidate(initial, &key, public);
            store
                .install_exact_fnsp_v3_activation(activation.clone())
                .expect("activation");
            let exact = store
                .prepare_exact_fnsp_v3_append([0x71; 32], 71)
                .expect("prepare");
            let frame = frame_candidate(&store, &activation, exact, &key, 0x72);
            let write = store.db.begin_write().expect("writer");
            let (write, _) = stage_exact_fnsp_v3_frame_in(write, exact, frame).expect("frame");
            write.commit().expect("commit");
            let write = store.db.begin_write().expect("corrupt writer");
            write
                .open_table(EXACT_FNSP_V3_FRAME_HEAD)
                .expect("heads")
                .remove(SINGLETON_KEY)
                .expect("remove head");
            write.commit().expect("commit corruption");
        }
        assert!(
            PersistentStore::open(&path).is_err(),
            "boot must fail closed on a partial exact frame image"
        );
    }

    #[test]
    fn coordinate_tamper_with_recomputed_unkeyed_seal_cannot_reuse_frame_signature() {
        let (store, initial) = setup_store();
        let (key, public) = generate_keypair();
        let activation = activation_candidate(initial, &key, public);
        store
            .install_exact_fnsp_v3_activation(activation.clone())
            .expect("activation");
        let exact = store
            .prepare_exact_fnsp_v3_append([0x81; 32], 81)
            .expect("prepare");
        let frame = frame_candidate(&store, &activation, exact, &key, 0x82);
        let write = store.db.begin_write().expect("writer");
        let (write, _) = stage_exact_fnsp_v3_frame_in(write, exact, frame).expect("frame");
        write.commit().expect("commit");

        // Model an offline store attacker: alter a signed frame-hash preimage coordinate, then
        // recompute the public/unkeyed corruption seal while preserving the executor signature.
        let write = store.db.begin_write().expect("tamper writer");
        let mut encoded = {
            let records = write
                .open_table(EXACT_FNSP_V3_FRAME_RECORDS)
                .expect("records");
            records
                .get(exact.expected().generation())
                .expect("read")
                .expect("row")
                .value()
                .to_vec()
        };
        encoded[F_PROOF_OUTER_BEFORE..F_PROOF_OUTER_BEFORE + 4]
            .copy_from_slice(&1u32.to_le_bytes());
        let resealed = seal(FRAME_SEAL_DOMAIN, &encoded[..F_SEAL]);
        encoded[F_SEAL..].copy_from_slice(&resealed);
        write
            .open_table(EXACT_FNSP_V3_FRAME_RECORDS)
            .expect("records")
            .insert(exact.expected().generation(), encoded.as_slice())
            .expect("tamper row");
        write
            .open_table(EXACT_FNSP_V3_FRAME_HEAD)
            .expect("head")
            .insert(SINGLETON_KEY, encoded.as_slice())
            .expect("tamper head");
        write.commit().expect("commit tamper");

        assert!(
            store.exact_fnsp_v3_committed_frame_head().is_err(),
            "the executor signature authenticates the recomputed frame preimage, not the seal"
        );
    }
}
