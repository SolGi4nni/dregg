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

use std::collections::{HashMap, HashSet};
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
const A_CUTOVER_NEXT_INDEX: usize = A_EPOCH + 8;
const A_CUTOVER_TAIL_TAG: usize = A_CUTOVER_NEXT_INDEX + 8;
const A_CUTOVER_TAIL_HASH: usize = A_CUTOVER_TAIL_TAG + 8;
const A_INITIAL_GENERATION: usize = A_CUTOVER_TAIL_HASH + 32;
const A_INITIAL_COUNT: usize = A_INITIAL_GENERATION + 8;
const A_INITIAL_ROOT: usize = A_INITIAL_COUNT + 8;
const A_INITIAL_FNS3: usize = A_INITIAL_ROOT + 32;
const A_FEDERATION: usize = A_INITIAL_FNS3 + 32;
const A_HASH: usize = A_FEDERATION + 32;
const A_EXECUTOR_KEY: usize = A_HASH + 32;
const A_SIGNATURE: usize = A_EXECUTOR_KEY + 32;
const A_SEAL: usize = A_SIGNATURE + 64;
pub const EXACT_FNSP_V3_ACTIVATION_V1_WIRE_LEN: usize = A_SEAL + 32;

const F_SEQUENCE: usize = HEADER_LEN;
const F_EPOCH: usize = F_SEQUENCE + 8;
const F_RECEIPT_LOG_INDEX: usize = F_EPOCH + 8;
const F_PREDECESSOR_TAG: usize = F_RECEIPT_LOG_INDEX + 8;
const F_ACTIVATION_HASH: usize = F_PREDECESSOR_TAG + 8;
const F_PREDECESSOR_HASH: usize = F_ACTIVATION_HASH + 32;
const F_FRAME_HASH: usize = F_PREDECESSOR_HASH + 32;
const F_PLAYER_PREDECESSOR_TAG: usize = F_FRAME_HASH + 32;
const F_PLAYER_PREDECESSOR_INDEX: usize = F_PLAYER_PREDECESSOR_TAG + 8;
const F_PLAYER_PREDECESSOR_HASH: usize = F_PLAYER_PREDECESSOR_INDEX + 8;
const F_AGENT: usize = F_PLAYER_PREDECESSOR_HASH + 32;
const F_FEDERATION: usize = F_AGENT + 32;
const F_TURN_HASH: usize = F_FEDERATION + 32;
const F_FOREST_HASH: usize = F_TURN_HASH + 32;
const F_RECEIPT_HASH: usize = F_FOREST_HASH + 32;
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
const F_EXECUTOR_KEY: usize = F_SIGNED_SPENDING_PROOF + 32;
const F_SIGNATURE: usize = F_EXECUTOR_KEY + 32;
const F_SEAL: usize = F_SIGNATURE + 64;
pub const EXACT_FNSP_V3_FRAME_V1_WIRE_LEN: usize = F_SEAL + 32;

pub(crate) const EXACT_FNSP_V3_ACTIVATION: TableDefinition<u8, &[u8]> =
    TableDefinition::new("exact_fnsp_v3_activation_v1");
pub(crate) const EXACT_FNSP_V3_FRAME_HEAD: TableDefinition<u8, &[u8]> =
    TableDefinition::new("exact_fnsp_v3_frame_head_v1");
pub(crate) const EXACT_FNSP_V3_FRAME_RECORDS: TableDefinition<u64, &[u8]> =
    TableDefinition::new("exact_fnsp_v3_frame_records_v1");
/// Derived per-agent receipt head for the active exact epoch.
///
/// This is an online-validation index, not an independent authority: store open rebuilds it from
/// the complete canonical receipt replay before any writer can use it.  Every post-activation
/// receipt append advances the corresponding row in the same redb transaction.
pub(crate) const EXACT_FNSP_V3_RECEIPT_HEADS: TableDefinition<&[u8; 32], &[u8]> =
    TableDefinition::new("exact_fnsp_v3_receipt_heads_v1");

const RECEIPT_HEAD_WIRE_LEN: usize = 8 + 32;

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
/// This remains untrusted until the finalized first-frame writer checks the exact prefix and
/// installs it in the same transaction as the first exact append, receipt, and signed frame.  The
/// resulting committed activation has no public constructor.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct UntrustedExactFnspV3ActivationV1 {
    epoch: u64,
    exact_initial: ExactFnspV3StateHeadV1,
    federation_id: [u8; 32],
    receipt_cutover_next_index: u64,
    receipt_cutover_tail_hash: Option<[u8; 32]>,
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
        receipt_cutover_next_index: u64,
        receipt_cutover_tail_hash: Option<[u8; 32]>,
        activation_hash: [u8; 32],
        executor_public_key: [u8; 32],
        executor_signature: Signature,
    ) -> StoreResult<Self> {
        let value = Self {
            epoch,
            exact_initial,
            federation_id,
            receipt_cutover_next_index,
            receipt_cutover_tail_hash,
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
    pub const fn receipt_cutover_next_index(&self) -> u64 {
        self.receipt_cutover_next_index
    }
    pub const fn receipt_cutover_tail_hash(&self) -> Option<[u8; 32]> {
        self.receipt_cutover_tail_hash
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
        if (self.receipt_cutover_next_index == 0) != self.receipt_cutover_tail_hash.is_none() {
            return Err(ExactFnspV3FrameStoreError::ActivationCutoverMismatch);
        }
        let computed = activation_hash(
            self.epoch,
            self.federation_id,
            self.executor_public_key,
            self.receipt_cutover_next_index,
            self.receipt_cutover_tail_hash,
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
            A_CUTOVER_NEXT_INDEX,
            self.receipt_cutover_next_index,
        );
        if let Some(hash) = self.receipt_cutover_tail_hash {
            out[A_CUTOVER_TAIL_TAG] = 1;
            out[A_CUTOVER_TAIL_HASH..A_INITIAL_GENERATION].copy_from_slice(&hash);
        }
        put_u64(
            &mut out,
            A_INITIAL_GENERATION,
            self.exact_initial.generation(),
        );
        put_u64(&mut out, A_INITIAL_COUNT, self.exact_initial.count());
        put_digest(&mut out, A_INITIAL_ROOT, self.exact_initial.root());
        put_digest(&mut out, A_INITIAL_FNS3, self.exact_initial.fns3());
        out[A_FEDERATION..A_HASH].copy_from_slice(&self.federation_id);
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
        if bytes[A_CUTOVER_TAIL_TAG + 1..A_CUTOVER_TAIL_HASH] != [0; 7] {
            return Err(integrity(ExactFnspV3FrameStoreError::NonZeroReserved(
                "activation cutover tail",
            )));
        }
        let receipt_cutover_tail_hash = match bytes[A_CUTOVER_TAIL_TAG] {
            0 if take32(bytes, A_CUTOVER_TAIL_HASH) == [0; 32] => None,
            1 => Some(take32(bytes, A_CUTOVER_TAIL_HASH)),
            _ => {
                return Err(integrity(
                    ExactFnspV3FrameStoreError::ActivationCutoverMismatch,
                ));
            }
        };
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
            receipt_cutover_next_index: get_u64(bytes, A_CUTOVER_NEXT_INDEX),
            receipt_cutover_tail_hash,
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
    pub const fn receipt_cutover_next_index(&self) -> u64 {
        self.0.receipt_cutover_next_index
    }
    pub const fn receipt_cutover_tail_hash(&self) -> Option<[u8; 32]> {
        self.0.receipt_cutover_tail_hash
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
    receipt_log_index: u64,
    predecessor: ExactFnspV3DurableReceiptLinkV1,
    activation_hash: [u8; 32],
    frame_hash: [u8; 32],
    predecessor_receipt_index: Option<u64>,
    predecessor_receipt_hash: Option<[u8; 32]>,
    agent: [u8; 32],
    federation_id: [u8; 32],
    turn_hash: [u8; 32],
    forest_hash: [u8; 32],
    full_receipt_hash: [u8; 32],
    full_pre_state_hash: [u8; 32],
    full_post_state_hash: [u8; 32],
    exact_before: ExactFnspV3StateHeadV1,
    exact_after: ExactFnspV3StateHeadV1,
    proof_outer_before: [u8; 32],
    proof_outer_after: [u8; 32],
    accepted_statement_digest: [u8; 32],
    signed_spending_proof_digest: [u8; 32],
    executor_public_key: [u8; 32],
    executor_signature: Signature,
}

impl UntrustedExactFnspV3FrameV1 {
    #[allow(clippy::too_many_arguments)]
    pub fn authenticate_devnet_executor(
        epoch: u64,
        receipt_log_index: u64,
        predecessor: ExactFnspV3DurableReceiptLinkV1,
        activation_hash: [u8; 32],
        frame_hash: [u8; 32],
        predecessor_receipt_index: Option<u64>,
        predecessor_receipt_hash: Option<[u8; 32]>,
        agent: [u8; 32],
        federation_id: [u8; 32],
        turn_hash: [u8; 32],
        forest_hash: [u8; 32],
        full_receipt_hash: [u8; 32],
        full_pre_state_hash: [u8; 32],
        full_post_state_hash: [u8; 32],
        exact_before: ExactFnspV3StateHeadV1,
        exact_after: ExactFnspV3StateHeadV1,
        proof_outer_before: [u8; 32],
        proof_outer_after: [u8; 32],
        accepted_statement_digest: [u8; 32],
        signed_spending_proof_digest: [u8; 32],
        executor_public_key: [u8; 32],
        executor_signature: Signature,
    ) -> StoreResult<Self> {
        let value = Self {
            sequence: exact_before.generation(),
            epoch,
            receipt_log_index,
            predecessor,
            activation_hash,
            frame_hash,
            predecessor_receipt_index,
            predecessor_receipt_hash,
            agent,
            federation_id,
            turn_hash,
            forest_hash,
            full_receipt_hash,
            full_pre_state_hash,
            full_post_state_hash,
            exact_before,
            exact_after,
            proof_outer_before,
            proof_outer_after,
            accepted_statement_digest,
            signed_spending_proof_digest,
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
    pub const fn receipt_log_index(&self) -> u64 {
        self.receipt_log_index
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
    pub const fn predecessor_receipt_index(&self) -> Option<u64> {
        self.predecessor_receipt_index
    }
    pub const fn predecessor_receipt_hash(&self) -> Option<[u8; 32]> {
        self.predecessor_receipt_hash
    }
    pub const fn turn_hash(&self) -> [u8; 32] {
        self.turn_hash
    }
    pub const fn forest_hash(&self) -> [u8; 32] {
        self.forest_hash
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
        let successor_sequence = self
            .sequence
            .checked_add(1)
            .ok_or(ExactFnspV3FrameStoreError::ExactStepMismatch)?;
        if self.sequence != self.exact_before.generation()
            || self.exact_after.generation() != successor_sequence
        {
            return Err(ExactFnspV3FrameStoreError::ExactStepMismatch);
        }
        if self.frame_hash == [0; 32] || self.full_receipt_hash == [0; 32] {
            return Err(ExactFnspV3FrameStoreError::ZeroHash);
        }
        if self.predecessor_receipt_index.is_some() != self.predecessor_receipt_hash.is_some()
            || self
                .predecessor_receipt_index
                .is_some_and(|index| index >= self.receipt_log_index)
        {
            return Err(ExactFnspV3FrameStoreError::FrameReceiptMismatch);
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
        put_u64(&mut out, F_RECEIPT_LOG_INDEX, self.receipt_log_index);
        out[F_PREDECESSOR_TAG] = self.predecessor.tag();
        out[F_ACTIVATION_HASH..F_PREDECESSOR_HASH].copy_from_slice(&self.activation_hash);
        out[F_PREDECESSOR_HASH..F_FRAME_HASH].copy_from_slice(&self.predecessor.hash());
        out[F_FRAME_HASH..F_PLAYER_PREDECESSOR_TAG].copy_from_slice(&self.frame_hash);
        if let (Some(index), Some(hash)) = (
            self.predecessor_receipt_index,
            self.predecessor_receipt_hash,
        ) {
            out[F_PLAYER_PREDECESSOR_TAG] = 1;
            put_u64(&mut out, F_PLAYER_PREDECESSOR_INDEX, index);
            out[F_PLAYER_PREDECESSOR_HASH..F_AGENT].copy_from_slice(&hash);
        }
        out[F_AGENT..F_FEDERATION].copy_from_slice(&self.agent);
        out[F_FEDERATION..F_TURN_HASH].copy_from_slice(&self.federation_id);
        out[F_TURN_HASH..F_FOREST_HASH].copy_from_slice(&self.turn_hash);
        out[F_FOREST_HASH..F_RECEIPT_HASH].copy_from_slice(&self.forest_hash);
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
        out[F_SIGNED_SPENDING_PROOF..F_EXECUTOR_KEY]
            .copy_from_slice(&self.signed_spending_proof_digest);
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
        if bytes[F_PLAYER_PREDECESSOR_TAG + 1..F_PLAYER_PREDECESSOR_INDEX] != [0; 7] {
            return Err(integrity(ExactFnspV3FrameStoreError::NonZeroReserved(
                "player receipt predecessor",
            )));
        }
        let predecessor_receipt_hash_bytes = take32(bytes, F_PLAYER_PREDECESSOR_HASH);
        let predecessor_receipt_index_raw = get_u64(bytes, F_PLAYER_PREDECESSOR_INDEX);
        let (predecessor_receipt_index, predecessor_receipt_hash) =
            match bytes[F_PLAYER_PREDECESSOR_TAG] {
                0 if predecessor_receipt_index_raw == 0
                    && predecessor_receipt_hash_bytes == [0; 32] =>
                {
                    (None, None)
                }
                1 => (
                    Some(predecessor_receipt_index_raw),
                    Some(predecessor_receipt_hash_bytes),
                ),
                _ => {
                    return Err(integrity(ExactFnspV3FrameStoreError::FrameReceiptMismatch));
                }
            };
        let sequence = get_u64(bytes, F_SEQUENCE);
        let value = Self {
            sequence,
            epoch: get_u64(bytes, F_EPOCH),
            receipt_log_index: get_u64(bytes, F_RECEIPT_LOG_INDEX),
            predecessor,
            activation_hash: take32(bytes, F_ACTIVATION_HASH),
            frame_hash: take32(bytes, F_FRAME_HASH),
            predecessor_receipt_index,
            predecessor_receipt_hash,
            agent: take32(bytes, F_AGENT),
            federation_id: take32(bytes, F_FEDERATION),
            turn_hash: take32(bytes, F_TURN_HASH),
            forest_hash: take32(bytes, F_FOREST_HASH),
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
        hasher.update(&self.receipt_log_index.to_le_bytes());
        match self.predecessor_receipt_index {
            None => hasher.update(&[0]),
            Some(index) => {
                hasher.update(&[1]);
                hasher.update(&index.to_le_bytes())
            }
        };
        hasher.update(&self.agent);
        hasher.update(&self.federation_id);
        hasher.update(&self.turn_hash);
        hasher.update(&self.forest_hash);
        match self.predecessor_receipt_hash {
            None => hasher.update(&[0]),
            Some(hash) => {
                hasher.update(&[1]);
                hasher.update(&hash)
            }
        };
        hasher.update(&self.full_pre_state_hash);
        hasher.update(&self.full_post_state_hash);
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
    pub const fn receipt_log_index(&self) -> u64 {
        self.0.receipt_log_index
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
    ActivationCutoverMismatch,
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
            Self::ActivationCutoverMismatch => {
                f.write_str("exact FNSP-v3 activation receipt cutover coordinates mismatch")
            }
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

/// The boundary rows needed by an online exact writer.
///
/// Opening the store has already replayed every receipt and exact frame.  A live writer therefore
/// revalidates the signed singleton activation, the signed current frame (and its immediate exact
/// predecessor), plus dense-table arithmetic.  It never turns this boundary cache into a recovery
/// authority: [`load_snapshot_from_read`] remains the full O(receipts + frames) boot/audit path.
struct ValidatedLiveFrameAuthority {
    activation: Option<UntrustedExactFnspV3ActivationV1>,
    head: Option<UntrustedExactFnspV3FrameV1>,
}

impl PersistentStore {
    /// Return the dense receipt-log cursor and optional terminal row from one read snapshot.
    ///
    /// Callers that need a staleness coordinate must not separately read the length and tail:
    /// another writer could advance the log between those reads.  The exact pre-execution actor
    /// authority uses this O(1) snapshot instead of loading the complete receipt history.
    pub fn receipt_chain_head(&self) -> StoreResult<(u64, Option<Vec<u8>>)> {
        let read = self.db.begin_read()?;
        let table = read.open_table(crate::tables::RECEIPT_CHAIN)?;
        let count = table.len()?;
        match (count, table.last()?) {
            (0, None) => Ok((0, None)),
            (0, Some((key, _))) => Err(StoreError::Integrity(format!(
                "receipt log has key {} but reports zero entries",
                key.value()
            ))),
            (count, Some((key, value))) if key.value() == count - 1 => {
                Ok((count, Some(value.value().to_vec())))
            }
            (count, Some((key, _))) => Err(StoreError::Integrity(format!(
                "receipt log is not dense: {count} entries but highest index is {}",
                key.value()
            ))),
            (count, None) => Err(StoreError::Integrity(format!(
                "receipt log reports {count} entries but has no last key"
            ))),
        }
    }

    /// Boot gate: a partial exact state/activation/frame image is an integrity failure, never an
    /// implicit rollback to legacy mode.
    pub(crate) fn validate_exact_fnsp_v3_receipt_authority_on_open(&self) -> StoreResult<()> {
        // The full canonical replay is the authority.  The per-agent head table is a derived
        // online index and is rebuilt only after this audit succeeds, so an interrupted/malformed
        // cache can never bless receipt history.
        let receipt_heads = {
            let read = self.db.begin_read()?;
            match crate::exact_fnsp_v3_state::load_state_head_from_read(&read)? {
                Some(exact_head) => {
                    let snapshot = load_snapshot_from_read(&read, exact_head)?;
                    if snapshot.activation.is_some() {
                        Some(
                            collect_receipts(&read.open_table(crate::tables::RECEIPT_CHAIN)?)?
                                .latest_heads(),
                        )
                    } else {
                        None
                    }
                }
                None => {
                    ensure_frame_authority_absent(&read)?;
                    None
                }
            }
        };
        let write = self.db.begin_write()?;
        replace_receipt_head_index_in(&write, receipt_heads.as_ref())?;
        write.commit()?;
        Ok(())
    }

    /// Test-only legacy activation installer.
    ///
    /// Production activation is deliberately impossible through a standalone write: the optional
    /// candidate is consumed only by the first finalized exact-frame transaction.  Tests which
    /// exercise continuation/recovery in isolation retain this helper as explicit scaffolding.
    #[cfg(test)]
    pub(crate) fn install_exact_fnsp_v3_activation(
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
        let receipts = collect_receipts(&write.open_table(crate::tables::RECEIPT_CHAIN)?)?;
        if usize::try_from(activation.receipt_cutover_next_index).ok() != Some(receipts.len()) {
            return Err(integrity(
                ExactFnspV3FrameStoreError::ActivationCutoverMismatch,
            ));
        }
        validate_activation_cutover(&activation, &receipts)?;
        replace_receipt_head_index_in(&write, Some(&receipts.latest_heads()))?;
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

    /// Return the currently signed exact-epoch boundary without replaying historical tables.
    ///
    /// This is intended for online node admission/finalization after `PersistentStore::open` has
    /// completed the full canonical audit.  It checks singleton cardinality, signatures/seals,
    /// dense frame-key arithmetic, the immediate exact predecessor, and the durable exact head in
    /// O(log N).  Recovery and offline audits must use the ordinary getters above.
    pub fn exact_fnsp_v3_live_authority(
        &self,
    ) -> StoreResult<
        Option<(
            StoreAuthenticatedExactFnspV3ActivationV1,
            Option<CommittedExactFnspV3FrameHeadV1>,
        )>,
    > {
        let read = self.db.begin_read()?;
        let exact_head = match crate::exact_fnsp_v3_state::load_live_state_head_from_read(&read)? {
            Some(head) => head,
            None => {
                ensure_frame_authority_absent(&read)?;
                return Ok(None);
            }
        };
        let live = load_live_authority_from_read(&read, exact_head)?;
        Ok(live.activation.map(|activation| {
            (
                StoreAuthenticatedExactFnspV3ActivationV1(activation),
                live.head.map(CommittedExactFnspV3FrameHeadV1),
            )
        }))
    }
}

fn ensure_frame_authority_absent(read: &ReadTransaction) -> StoreResult<()> {
    let activation = read.open_table(EXACT_FNSP_V3_ACTIVATION)?;
    let head = read.open_table(EXACT_FNSP_V3_FRAME_HEAD)?;
    let records = read.open_table(EXACT_FNSP_V3_FRAME_RECORDS)?;
    let receipt_heads = read.open_table(EXACT_FNSP_V3_RECEIPT_HEADS)?;
    if activation.len()? != 0
        || head.len()? != 0
        || records.len()? != 0
        || receipt_heads.len()? != 0
    {
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
    let receipt_heads = write.open_table(EXACT_FNSP_V3_RECEIPT_HEADS)?;
    if activation.len()? != 0
        || head.len()? != 0
        || records.len()? != 0
        || receipt_heads.len()? != 0
    {
        return Err(integrity(
            ExactFnspV3FrameStoreError::FrameRowsWithoutActivation,
        ));
    }
    Ok(())
}

/// Advance the derived per-agent receipt head after a fresh dense receipt append.
///
/// `PersistentStore::write_receipt_chain_entry_in` calls this after inserting the canonical row,
/// in the same write transaction.  Before activation the index is intentionally empty.  After
/// activation every appended receipt must extend exactly the indexed head for its own agent; this
/// is the O(log N) witness that no same-agent receipt sits between the predecessor named by an
/// exact frame and its current receipt.
pub(crate) fn stage_receipt_head_on_append_in(
    write: &WriteTransaction,
    index: u64,
    encoded: &[u8],
) -> StoreResult<()> {
    let activation = collect_singleton(&write.open_table(EXACT_FNSP_V3_ACTIVATION)?)?;
    let Some(activation) = activation else {
        if write.open_table(EXACT_FNSP_V3_RECEIPT_HEADS)?.len()? != 0 {
            return Err(integrity(
                ExactFnspV3FrameStoreError::FrameRowsWithoutActivation,
            ));
        }
        return Ok(());
    };
    let activation = UntrustedExactFnspV3ActivationV1::decode(&activation)?;
    if index < activation.receipt_cutover_next_index {
        return Err(integrity(
            ExactFnspV3FrameStoreError::ActivationCutoverMismatch,
        ));
    }
    let receipt = decode_canonical_receipt(encoded)?;
    if receipt.finality != Finality::Final
        || receipt.federation_id != activation.federation_id
        || verify_receipt_signature_with_keys(&receipt, &[activation.executor_public_key]).is_err()
    {
        return Err(integrity(ExactFnspV3FrameStoreError::FrameReceiptMismatch));
    }
    let hash = receipt.receipt_hash();
    let mut heads = write.open_table(EXACT_FNSP_V3_RECEIPT_HEADS)?;
    let previous = heads
        .get(&receipt.agent.0)?
        .map(|value| decode_receipt_head(value.value()))
        .transpose()?;
    if receipt.previous_receipt_hash != previous.map(|(_, hash)| hash)
        || previous.is_some_and(|(previous_index, _)| previous_index >= index)
    {
        return Err(integrity(ExactFnspV3FrameStoreError::FrameReceiptMismatch));
    }
    let head = encode_receipt_head(index, hash);
    heads.insert(&receipt.agent.0, head.as_slice())?;
    Ok(())
}

pub(crate) fn stage_exact_fnsp_v3_frame_with_activation_in(
    write: WriteTransaction,
    exact: ExactFnspV3StateCasV1,
    candidate_activation: Option<UntrustedExactFnspV3ActivationV1>,
    frame: UntrustedExactFnspV3FrameV1,
) -> StoreResult<(WriteTransaction, UntrustedExactFnspV3FrameV1)> {
    frame.validate().map_err(integrity)?;
    if let Some(candidate) = candidate_activation.as_ref() {
        candidate.validate().map_err(integrity)?;
    }
    let exact_head = exact_fnsp_v3_state_head_in(&write)?;
    let live = load_live_authority_from_write(&write, exact_head)?;
    let activation = match (live.activation, candidate_activation) {
        (Some(activation), None) => activation,
        (Some(_), Some(_)) => {
            return Err(integrity(
                ExactFnspV3FrameStoreError::ActivationAlreadyInstalled,
            ));
        }
        (None, None) => {
            return Err(integrity(ExactFnspV3FrameStoreError::ActivationMissing));
        }
        (None, Some(candidate)) => {
            stage_first_frame_activation_in(&write, exact_head, &frame, &candidate)?;
            candidate
        }
    };
    validate_fresh_frame_against_live(&frame, &activation, live.head.as_ref(), exact)?;
    validate_frame_receipt_online(&write, &frame, true, true)?;
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

/// Compatibility seam for already-installed epochs. Production finalized-turn callers should use
/// [`stage_exact_fnsp_v3_frame_with_activation_in`] and pass their optional first-frame candidate.
pub(crate) fn stage_exact_fnsp_v3_frame_in(
    write: WriteTransaction,
    exact: ExactFnspV3StateCasV1,
    frame: UntrustedExactFnspV3FrameV1,
) -> StoreResult<(WriteTransaction, UntrustedExactFnspV3FrameV1)> {
    stage_exact_fnsp_v3_frame_with_activation_in(write, exact, None, frame)
}

pub(crate) fn verify_replayed_exact_fnsp_v3_frame_with_activation_in(
    write: &WriteTransaction,
    exact: ExactFnspV3StateCasV1,
    candidate_activation: Option<&UntrustedExactFnspV3ActivationV1>,
    frame: &UntrustedExactFnspV3FrameV1,
) -> StoreResult<()> {
    frame.validate().map_err(integrity)?;
    let exact_head = exact_fnsp_v3_state_head_in(write)?;
    let live = load_live_authority_from_write(write, exact_head)?;
    let activation = live
        .activation
        .ok_or_else(|| integrity(ExactFnspV3FrameStoreError::ActivationMissing))?;
    if candidate_activation.is_some_and(|candidate| candidate.encode() != activation.encode()) {
        return Err(integrity(ExactFnspV3FrameStoreError::ActivationReplacement));
    }
    validate_replayed_frame_against_live(write, frame, &activation, exact)?;
    validate_frame_receipt_online(write, frame, false, false)
}

/// Compatibility seam for replay under an already-installed activation.
pub(crate) fn verify_replayed_exact_fnsp_v3_frame_in(
    write: &WriteTransaction,
    exact: ExactFnspV3StateCasV1,
    frame: &UntrustedExactFnspV3FrameV1,
) -> StoreResult<()> {
    verify_replayed_exact_fnsp_v3_frame_with_activation_in(write, exact, None, frame)
}

/// Whether the persist-once exact epoch is already live in this writer snapshot.
///
/// The commit log uses this only after resolving idempotent replay, to refuse a fresh faithful
/// nullifier mutation which omits the exact frame/CAS weld after the flag day.
pub(crate) fn exact_fnsp_v3_activation_installed_in(write: &WriteTransaction) -> StoreResult<bool> {
    Ok(write.open_table(EXACT_FNSP_V3_ACTIVATION)?.len()? != 0)
}

/// Validate and stage the persist-once activation carried by the first accepted exact frame.
///
/// The receipt append occurs earlier in the same caller-owned writer transaction. Therefore the
/// only admissible image is the historical cutover prefix plus exactly the first exact receipt at
/// `cutover`. Rebuilding the derived per-agent heads here includes that staged row; any subsequent
/// frame/CAS failure drops the sole writer and exposes neither activation nor cache rows.
fn stage_first_frame_activation_in(
    write: &WriteTransaction,
    exact_head: ExactFnspV3StateHeadV1,
    frame: &UntrustedExactFnspV3FrameV1,
    activation: &UntrustedExactFnspV3ActivationV1,
) -> StoreResult<()> {
    // A flag day may shadow a nonempty faithful/exact prefix. Frame numbering continues at that
    // prefix generation; zero is correct only for a genesis activation.
    if frame.sequence != activation.exact_initial.generation()
        || frame.receipt_log_index != activation.receipt_cutover_next_index
        || activation.exact_initial != exact_head
    {
        return Err(integrity(
            ExactFnspV3FrameStoreError::ActivationCutoverMismatch,
        ));
    }
    let receipts = collect_receipts(&write.open_table(crate::tables::RECEIPT_CHAIN)?)?;
    let expected_len = activation
        .receipt_cutover_next_index
        .checked_add(1)
        .ok_or_else(|| integrity(ExactFnspV3FrameStoreError::ActivationCutoverMismatch))?;
    if u64::try_from(receipts.len()).ok() != Some(expected_len) {
        return Err(integrity(
            ExactFnspV3FrameStoreError::ActivationCutoverMismatch,
        ));
    }
    validate_activation_cutover(activation, &receipts)?;
    validate_active_epoch_receipts(activation, &receipts)?;
    replace_receipt_head_index_in(write, Some(&receipts.latest_heads()))?;
    let mut table = write.open_table(EXACT_FNSP_V3_ACTIVATION)?;
    if table.len()? != 0 {
        return Err(integrity(
            ExactFnspV3FrameStoreError::ActivationAlreadyInstalled,
        ));
    }
    let encoded = activation.encode();
    table.insert(SINGLETON_KEY, encoded.as_slice())?;
    Ok(())
}

fn validate_fresh_frame_against_live(
    frame: &UntrustedExactFnspV3FrameV1,
    activation: &UntrustedExactFnspV3ActivationV1,
    head: Option<&UntrustedExactFnspV3FrameV1>,
    exact: ExactFnspV3StateCasV1,
) -> StoreResult<()> {
    if frame.exact_before != exact.expected() || frame.exact_after != exact.successor() {
        return Err(integrity(ExactFnspV3FrameStoreError::ExactHeadMismatch));
    }
    if frame.epoch != activation.epoch
        || frame.activation_hash != activation.activation_hash
        || frame.federation_id != activation.federation_id
        || frame.executor_public_key != activation.executor_public_key
    {
        return Err(integrity(ExactFnspV3FrameStoreError::ActivationReplacement));
    }
    let (expected_link, prior_receipt_log_index, expected_exact) = match head {
        Some(previous) => (
            ExactFnspV3DurableReceiptLinkV1::ExactFrame(previous.frame_hash),
            Some(previous.receipt_log_index),
            previous.exact_after,
        ),
        None => (
            ExactFnspV3DurableReceiptLinkV1::EpochActivation(activation.activation_hash),
            None,
            activation.exact_initial,
        ),
    };
    if frame.predecessor != expected_link {
        return Err(integrity(ExactFnspV3FrameStoreError::FrameChainBreak(
            "frame predecessor",
        )));
    }
    if frame.receipt_log_index < activation.receipt_cutover_next_index
        || prior_receipt_log_index.is_some_and(|index| frame.receipt_log_index <= index)
    {
        return Err(integrity(ExactFnspV3FrameStoreError::FrameChainBreak(
            "global receipt order",
        )));
    }
    if frame.exact_before != expected_exact {
        return Err(integrity(ExactFnspV3FrameStoreError::FrameChainBreak(
            "exact state predecessor",
        )));
    }
    Ok(())
}

fn validate_replayed_frame_against_live(
    write: &WriteTransaction,
    frame: &UntrustedExactFnspV3FrameV1,
    activation: &UntrustedExactFnspV3ActivationV1,
    exact: ExactFnspV3StateCasV1,
) -> StoreResult<()> {
    if frame.exact_before != exact.expected() || frame.exact_after != exact.successor() {
        return Err(integrity(ExactFnspV3FrameStoreError::ExactHeadMismatch));
    }
    if frame.epoch != activation.epoch
        || frame.activation_hash != activation.activation_hash
        || frame.federation_id != activation.federation_id
        || frame.executor_public_key != activation.executor_public_key
    {
        return Err(integrity(ExactFnspV3FrameStoreError::ActivationReplacement));
    }
    let records = write.open_table(EXACT_FNSP_V3_FRAME_RECORDS)?;
    let durable = records
        .get(frame.sequence)?
        .ok_or_else(|| integrity(ExactFnspV3FrameStoreError::FrameReplayMismatch))?;
    if durable.value() != frame.encode().as_slice() {
        return Err(integrity(ExactFnspV3FrameStoreError::FrameReplayMismatch));
    }
    Ok(())
}

fn load_live_authority_from_read(
    read: &ReadTransaction,
    exact_head: ExactFnspV3StateHeadV1,
) -> StoreResult<ValidatedLiveFrameAuthority> {
    let activation = collect_singleton(&read.open_table(EXACT_FNSP_V3_ACTIVATION)?)?;
    let head = collect_singleton(&read.open_table(EXACT_FNSP_V3_FRAME_HEAD)?)?;
    let records = read.open_table(EXACT_FNSP_V3_FRAME_RECORDS)?;
    validate_live_authority(activation, head, &records, exact_head)
}

fn load_live_authority_from_write(
    write: &WriteTransaction,
    exact_head: ExactFnspV3StateHeadV1,
) -> StoreResult<ValidatedLiveFrameAuthority> {
    let activation = collect_singleton(&write.open_table(EXACT_FNSP_V3_ACTIVATION)?)?;
    let head = collect_singleton(&write.open_table(EXACT_FNSP_V3_FRAME_HEAD)?)?;
    let records = write.open_table(EXACT_FNSP_V3_FRAME_RECORDS)?;
    validate_live_authority(activation, head, &records, exact_head)
}

/// Validate only the append boundary.  The `(len, first, last)` arithmetic proves the u64 frame
/// keys are the complete dense interval: there are exactly `len` distinct integer keys and only
/// `len` positions between the asserted endpoints.  The last two signed rows then re-establish the
/// exact/frame/receipt ordering edge that the next append will extend.
fn validate_live_authority(
    activation_bytes: Option<Vec<u8>>,
    head_bytes: Option<Vec<u8>>,
    records: &impl ReadableTable<u64, &'static [u8]>,
    exact_head: ExactFnspV3StateHeadV1,
) -> StoreResult<ValidatedLiveFrameAuthority> {
    let Some(activation_bytes) = activation_bytes else {
        if head_bytes.is_some() || records.len()? != 0 {
            return Err(integrity(
                ExactFnspV3FrameStoreError::FrameRowsWithoutActivation,
            ));
        }
        return Ok(ValidatedLiveFrameAuthority {
            activation: None,
            head: None,
        });
    };
    let activation = UntrustedExactFnspV3ActivationV1::decode(&activation_bytes)?;
    let expected_count = exact_head
        .generation()
        .checked_sub(activation.exact_initial.generation())
        .ok_or_else(|| integrity(ExactFnspV3FrameStoreError::FrameCountMismatch))?;
    if records.len()? != expected_count {
        return Err(integrity(ExactFnspV3FrameStoreError::FrameCountMismatch));
    }
    if expected_count == 0 {
        if head_bytes.is_some() {
            return Err(integrity(ExactFnspV3FrameStoreError::FrameHeadWithoutRows));
        }
        if exact_head != activation.exact_initial {
            return Err(integrity(ExactFnspV3FrameStoreError::ExactHeadMismatch));
        }
        return Ok(ValidatedLiveFrameAuthority {
            activation: Some(activation),
            head: None,
        });
    }

    let head_bytes =
        head_bytes.ok_or_else(|| integrity(ExactFnspV3FrameStoreError::FrameRowsWithoutHead))?;
    let expected_first = activation.exact_initial.generation();
    let expected_last = exact_head
        .generation()
        .checked_sub(1)
        .ok_or_else(|| integrity(ExactFnspV3FrameStoreError::FrameCountMismatch))?;
    let (first_key, _) = records
        .first()?
        .ok_or_else(|| integrity(ExactFnspV3FrameStoreError::FrameCountMismatch))?;
    let (last_key, last_bytes) = records
        .last()?
        .ok_or_else(|| integrity(ExactFnspV3FrameStoreError::FrameCountMismatch))?;
    if first_key.value() != expected_first {
        return Err(integrity(ExactFnspV3FrameStoreError::FrameRecordGap {
            expected: expected_first,
            found: first_key.value(),
        }));
    }
    if last_key.value() != expected_last {
        return Err(integrity(ExactFnspV3FrameStoreError::FrameRecordGap {
            expected: expected_last,
            found: last_key.value(),
        }));
    }
    if last_bytes.value() != head_bytes.as_slice() {
        return Err(integrity(ExactFnspV3FrameStoreError::FrameHeadMismatch));
    }
    let head = UntrustedExactFnspV3FrameV1::decode(&head_bytes)?;
    if head.sequence != expected_last
        || head.epoch != activation.epoch
        || head.activation_hash != activation.activation_hash
        || head.federation_id != activation.federation_id
        || head.executor_public_key != activation.executor_public_key
        || head.receipt_log_index < activation.receipt_cutover_next_index
        || head.exact_after != exact_head
    {
        return Err(integrity(ExactFnspV3FrameStoreError::FrameChainBreak(
            "live head",
        )));
    }
    if expected_count == 1 {
        if head.predecessor
            != ExactFnspV3DurableReceiptLinkV1::EpochActivation(activation.activation_hash)
            || head.exact_before != activation.exact_initial
        {
            return Err(integrity(ExactFnspV3FrameStoreError::FrameChainBreak(
                "live first frame",
            )));
        }
    } else {
        let previous_key = expected_last
            .checked_sub(1)
            .ok_or_else(|| integrity(ExactFnspV3FrameStoreError::FrameCountMismatch))?;
        let previous_bytes = records.get(previous_key)?.ok_or_else(|| {
            integrity(ExactFnspV3FrameStoreError::FrameRecordGap {
                expected: previous_key,
                found: expected_last,
            })
        })?;
        let previous = UntrustedExactFnspV3FrameV1::decode(previous_bytes.value())?;
        if previous.sequence != previous_key
            || previous.epoch != activation.epoch
            || previous.activation_hash != activation.activation_hash
            || previous.federation_id != activation.federation_id
            || previous.executor_public_key != activation.executor_public_key
            || head.predecessor != ExactFnspV3DurableReceiptLinkV1::ExactFrame(previous.frame_hash)
            || head.receipt_log_index <= previous.receipt_log_index
            || head.exact_before != previous.exact_after
        {
            return Err(integrity(ExactFnspV3FrameStoreError::FrameChainBreak(
                "live predecessor",
            )));
        }
    }
    Ok(ValidatedLiveFrameAuthority {
        activation: Some(activation),
        head: Some(head),
    })
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

struct ValidatedReceiptRow {
    receipt: TurnReceipt,
    hash: [u8; 32],
    player_predecessor: Option<(u64, [u8; 32])>,
}

struct ValidatedReceiptLog {
    rows: Vec<ValidatedReceiptRow>,
}

impl ValidatedReceiptLog {
    fn len(&self) -> usize {
        self.rows.len()
    }

    fn get(&self, index: usize) -> Option<&ValidatedReceiptRow> {
        self.rows.get(index)
    }

    fn latest_heads(&self) -> HashMap<[u8; 32], (u64, [u8; 32])> {
        let mut heads = HashMap::new();
        for (index, row) in self.rows.iter().enumerate() {
            heads.insert(
                row.receipt.agent.0,
                (
                    u64::try_from(index).expect("receipt index was originally a u64 table key"),
                    row.hash,
                ),
            );
        }
        heads
    }
}

fn decode_canonical_receipt(encoded: &[u8]) -> StoreResult<TurnReceipt> {
    let receipt: TurnReceipt = postcard::from_bytes(encoded)
        .map_err(|_| integrity(ExactFnspV3FrameStoreError::FrameReceiptMismatch))?;
    let canonical = postcard::to_stdvec(&receipt)
        .map_err(|_| integrity(ExactFnspV3FrameStoreError::FrameReceiptMismatch))?;
    if canonical.as_slice() != encoded {
        return Err(integrity(ExactFnspV3FrameStoreError::FrameReceiptMismatch));
    }
    Ok(receipt)
}

fn encode_receipt_head(index: u64, hash: [u8; 32]) -> [u8; RECEIPT_HEAD_WIRE_LEN] {
    let mut encoded = [0u8; RECEIPT_HEAD_WIRE_LEN];
    encoded[..8].copy_from_slice(&index.to_le_bytes());
    encoded[8..].copy_from_slice(&hash);
    encoded
}

fn decode_receipt_head(encoded: &[u8]) -> StoreResult<(u64, [u8; 32])> {
    if encoded.len() != RECEIPT_HEAD_WIRE_LEN {
        return Err(integrity(ExactFnspV3FrameStoreError::FrameReceiptMismatch));
    }
    Ok((
        u64::from_le_bytes(encoded[..8].try_into().expect("eight bytes")),
        encoded[8..].try_into().expect("32 bytes"),
    ))
}

fn replace_receipt_head_index_in(
    write: &WriteTransaction,
    expected: Option<&HashMap<[u8; 32], (u64, [u8; 32])>>,
) -> StoreResult<()> {
    let mut table = write.open_table(EXACT_FNSP_V3_RECEIPT_HEADS)?;
    let keys: Vec<[u8; 32]> = table
        .iter()?
        .map(|entry| entry.map(|(key, _)| *key.value()))
        .collect::<std::result::Result<_, redb::StorageError>>()?;
    for key in keys {
        table.remove(&key)?;
    }
    if let Some(expected) = expected {
        for (agent, (index, hash)) in expected {
            let encoded = encode_receipt_head(*index, *hash);
            table.insert(agent, encoded.as_slice())?;
        }
    }
    Ok(())
}

/// Decode the dense receipt log exactly once and derive each actor's causal predecessor at that
/// row.  Snapshot recovery can then validate every sparse exact frame in O(receipts + frames),
/// rather than rescanning the receipt prefix and full hash set for each exact frame.
fn collect_receipts(
    table: &impl ReadableTable<u64, &'static [u8]>,
) -> StoreResult<ValidatedReceiptLog> {
    let mut expected = 0u64;
    let mut rows = Vec::new();
    let mut latest_by_agent: HashMap<[u8; 32], (u64, [u8; 32])> = HashMap::new();
    let mut seen_hashes = HashSet::new();
    for entry in table.iter()? {
        let (key, value) = entry?;
        if key.value() != expected {
            return Err(integrity(ExactFnspV3FrameStoreError::FrameReceiptMismatch));
        }
        let encoded = value.value();
        let receipt = decode_canonical_receipt(encoded)?;
        let hash = receipt.receipt_hash();
        if !seen_hashes.insert(hash) {
            return Err(integrity(ExactFnspV3FrameStoreError::FrameReceiptMismatch));
        }
        let player_predecessor = latest_by_agent.get(&receipt.agent.0).copied();
        if receipt.previous_receipt_hash != player_predecessor.map(|(_, hash)| hash) {
            return Err(integrity(ExactFnspV3FrameStoreError::FrameReceiptMismatch));
        }
        rows.push(ValidatedReceiptRow {
            receipt,
            hash,
            player_predecessor,
        });
        latest_by_agent.insert(
            rows.last().expect("just pushed receipt").receipt.agent.0,
            (expected, hash),
        );
        expected = expected
            .checked_add(1)
            .ok_or_else(|| integrity(ExactFnspV3FrameStoreError::FrameReceiptMismatch))?;
    }
    Ok(ValidatedReceiptLog { rows })
}

fn validate_frame_receipt(
    frame: &UntrustedExactFnspV3FrameV1,
    receipt_rows: &ValidatedReceiptLog,
    require_current_tail: bool,
) -> StoreResult<()> {
    let index = usize::try_from(frame.receipt_log_index)
        .map_err(|_| integrity(ExactFnspV3FrameStoreError::FrameReceiptMismatch))?;
    if require_current_tail && index.checked_add(1) != Some(receipt_rows.len()) {
        return Err(integrity(ExactFnspV3FrameStoreError::FrameReceiptMismatch));
    }
    let row = receipt_rows
        .get(index)
        .ok_or_else(|| integrity(ExactFnspV3FrameStoreError::FrameReceiptMismatch))?;
    let receipt = &row.receipt;
    if receipt.finality != Finality::Final
        || row.hash != frame.full_receipt_hash
        || receipt.previous_receipt_hash != frame.predecessor_receipt_hash
        || row.player_predecessor
            != frame
                .predecessor_receipt_index
                .zip(frame.predecessor_receipt_hash)
        || receipt.turn_hash != frame.turn_hash
        || receipt.forest_hash != frame.forest_hash
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

/// Validate one exact receipt by direct table lookup.
///
/// Fresh writes additionally require the derived per-agent index to name this exact current row.
/// That index was advanced by the receipt append only after checking the prior per-agent head, so
/// the check preserves the "latest same-agent predecessor" law without a global receipt scan.
/// Historical replay compares the explicitly named predecessor row instead; full boot replay has
/// already established that it was the latest row at that historical point.
fn validate_frame_receipt_online(
    write: &WriteTransaction,
    frame: &UntrustedExactFnspV3FrameV1,
    require_current_tail: bool,
    require_indexed_agent_head: bool,
) -> StoreResult<()> {
    let receipts = write.open_table(crate::tables::RECEIPT_CHAIN)?;
    let count = receipts.len()?;
    let last = receipts.last()?;
    match (count, last.as_ref()) {
        (0, None) => {
            return Err(integrity(ExactFnspV3FrameStoreError::FrameReceiptMismatch));
        }
        (0, Some(_)) | (_, None) => {
            return Err(integrity(ExactFnspV3FrameStoreError::FrameReceiptMismatch));
        }
        (count, Some((key, _))) if key.value() == count - 1 => {}
        _ => return Err(integrity(ExactFnspV3FrameStoreError::FrameReceiptMismatch)),
    }
    if frame.receipt_log_index >= count
        || (require_current_tail && frame.receipt_log_index.checked_add(1) != Some(count))
    {
        return Err(integrity(ExactFnspV3FrameStoreError::FrameReceiptMismatch));
    }
    let current_bytes = receipts
        .get(frame.receipt_log_index)?
        .ok_or_else(|| integrity(ExactFnspV3FrameStoreError::FrameReceiptMismatch))?;
    let receipt = decode_canonical_receipt(current_bytes.value())?;
    let current_hash = receipt.receipt_hash();
    if receipt.finality != Finality::Final
        || current_hash != frame.full_receipt_hash
        || receipt.previous_receipt_hash != frame.predecessor_receipt_hash
        || receipt.turn_hash != frame.turn_hash
        || receipt.forest_hash != frame.forest_hash
        || receipt.pre_state_hash != frame.full_pre_state_hash
        || receipt.post_state_hash != frame.full_post_state_hash
        || receipt.federation_id != frame.federation_id
        || receipt.agent.0 != frame.agent
        || verify_receipt_signature_with_keys(&receipt, &[frame.executor_public_key]).is_err()
    {
        return Err(integrity(ExactFnspV3FrameStoreError::FrameReceiptMismatch));
    }

    match (
        frame.predecessor_receipt_index,
        frame.predecessor_receipt_hash,
    ) {
        (None, None) => {}
        (Some(index), Some(expected_hash)) => {
            let predecessor_bytes = receipts
                .get(index)?
                .ok_or_else(|| integrity(ExactFnspV3FrameStoreError::FrameReceiptMismatch))?;
            let predecessor = decode_canonical_receipt(predecessor_bytes.value())?;
            if predecessor.receipt_hash() != expected_hash || predecessor.agent.0 != frame.agent {
                return Err(integrity(ExactFnspV3FrameStoreError::FrameReceiptMismatch));
            }
        }
        _ => return Err(integrity(ExactFnspV3FrameStoreError::FrameReceiptMismatch)),
    }

    if require_indexed_agent_head {
        let heads = write.open_table(EXACT_FNSP_V3_RECEIPT_HEADS)?;
        let indexed = heads
            .get(&frame.agent)?
            .map(|value| decode_receipt_head(value.value()))
            .transpose()?;
        if indexed != Some((frame.receipt_log_index, frame.full_receipt_hash)) {
            return Err(integrity(ExactFnspV3FrameStoreError::FrameReceiptMismatch));
        }
    }
    Ok(())
}

fn validate_activation_cutover(
    activation: &UntrustedExactFnspV3ActivationV1,
    receipt_rows: &ValidatedReceiptLog,
) -> StoreResult<()> {
    let cutover = usize::try_from(activation.receipt_cutover_next_index)
        .map_err(|_| integrity(ExactFnspV3FrameStoreError::ActivationCutoverMismatch))?;
    if cutover > receipt_rows.len() {
        return Err(integrity(
            ExactFnspV3FrameStoreError::ActivationCutoverMismatch,
        ));
    }
    match (cutover, activation.receipt_cutover_tail_hash) {
        (0, None) => Ok(()),
        (0, Some(_)) | (_, None) => Err(integrity(
            ExactFnspV3FrameStoreError::ActivationCutoverMismatch,
        )),
        (cutover, Some(expected_hash)) => {
            let row = receipt_rows
                .get(cutover - 1)
                .ok_or_else(|| integrity(ExactFnspV3FrameStoreError::ActivationCutoverMismatch))?;
            if row.hash != expected_hash
                || row.receipt.finality != Finality::Final
                || row.receipt.federation_id != activation.federation_id
                || verify_receipt_signature_with_keys(
                    &row.receipt,
                    &[activation.executor_public_key],
                )
                .is_err()
            {
                return Err(integrity(
                    ExactFnspV3FrameStoreError::ActivationCutoverMismatch,
                ));
            }
            Ok(())
        }
    }
}

fn validate_active_epoch_receipts(
    activation: &UntrustedExactFnspV3ActivationV1,
    receipt_rows: &ValidatedReceiptLog,
) -> StoreResult<()> {
    let cutover = usize::try_from(activation.receipt_cutover_next_index)
        .map_err(|_| integrity(ExactFnspV3FrameStoreError::ActivationCutoverMismatch))?;
    for row in receipt_rows
        .rows
        .get(cutover..)
        .ok_or_else(|| integrity(ExactFnspV3FrameStoreError::ActivationCutoverMismatch))?
    {
        if row.receipt.finality != Finality::Final
            || row.receipt.federation_id != activation.federation_id
            || verify_receipt_signature_with_keys(&row.receipt, &[activation.executor_public_key])
                .is_err()
        {
            return Err(integrity(ExactFnspV3FrameStoreError::FrameReceiptMismatch));
        }
    }
    Ok(())
}

fn validate_snapshot(
    activation_bytes: Option<Vec<u8>>,
    head_bytes: Option<Vec<u8>>,
    record_rows: Vec<(u64, Vec<u8>)>,
    receipt_rows: ValidatedReceiptLog,
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
    validate_activation_cutover(&activation, &receipt_rows)?;
    validate_active_epoch_receipts(&activation, &receipt_rows)?;
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
        let (link, prior_receipt_log_index, exact) = match frames.last() {
            Some(previous) => (
                ExactFnspV3DurableReceiptLinkV1::ExactFrame(previous.frame_hash),
                Some(previous.receipt_log_index),
                previous.exact_after,
            ),
            None => (
                ExactFnspV3DurableReceiptLinkV1::EpochActivation(activation.activation_hash),
                None,
                activation.exact_initial,
            ),
        };
        if frame.epoch != activation.epoch
            || frame.activation_hash != activation.activation_hash
            || frame.federation_id != activation.federation_id
            || frame.executor_public_key != activation.executor_public_key
            || frame.predecessor != link
            || frame.receipt_log_index < activation.receipt_cutover_next_index
            || prior_receipt_log_index.is_some_and(|index| frame.receipt_log_index <= index)
            || frame.exact_before != exact
        {
            return Err(integrity(ExactFnspV3FrameStoreError::FrameChainBreak(
                "recovery",
            )));
        }
        validate_frame_receipt(&frame, &receipt_rows, false)?;
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
    executor_public_key: [u8; 32],
    receipt_cutover_next_index: u64,
    receipt_cutover_tail_hash: Option<[u8; 32]>,
    exact_initial: ExactFnspV3StateHeadV1,
) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key(ACTIVATION_HASH_DOMAIN);
    hasher.update(&epoch.to_le_bytes());
    hasher.update(&federation_id);
    hasher.update(&executor_public_key);
    hasher.update(&receipt_cutover_next_index.to_le_bytes());
    match receipt_cutover_tail_hash {
        None => hasher.update(&[0]),
        Some(hash) => {
            hasher.update(&[1]);
            hasher.update(&hash)
        }
    };
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

/// Build a canonical empty-cutover first-frame bundle for atomic commit-log tests.
///
/// This lives beside the private wire/hash implementation so higher-level tests do not duplicate
/// consensus encoding merely to exercise the full writer transaction.
#[cfg(test)]
pub(crate) fn exact_fnsp_v3_test_first_frame_bundle(
    store: &PersistentStore,
    exact: ExactFnspV3StateCasV1,
    key: &dregg_types::SigningKey,
    mut receipt: TurnReceipt,
) -> (
    UntrustedExactFnspV3ActivationV1,
    UntrustedExactFnspV3FrameV1,
    Vec<u8>,
) {
    assert_eq!(store.receipt_chain_len().expect("receipt len"), 0);
    assert!(receipt.previous_receipt_hash.is_none());
    let public = key.public_key();
    let epoch = 7;
    let federation = receipt.federation_id;
    let hash = activation_hash(epoch, federation, public.0, 0, None, exact.expected());
    let activation_signature = dregg_types::sign(
        key,
        &UntrustedExactFnspV3ActivationV1::signature_message(hash),
    );
    let activation = UntrustedExactFnspV3ActivationV1::authenticate_devnet_executor(
        epoch,
        exact.expected(),
        federation,
        0,
        None,
        hash,
        public.0,
        activation_signature,
    )
    .expect("test activation");

    receipt.executor_signature = Some(
        dregg_types::sign(key, &receipt.canonical_executor_signed_message())
            .0
            .to_vec(),
    );
    let encoded_receipt = postcard::to_stdvec(&receipt).expect("test receipt encoding");
    let predecessor = ExactFnspV3DurableReceiptLinkV1::EpochActivation(hash);
    let unsigned = UntrustedExactFnspV3FrameV1 {
        sequence: exact.expected().generation(),
        epoch,
        receipt_log_index: 0,
        predecessor,
        activation_hash: hash,
        frame_hash: [0; 32],
        predecessor_receipt_index: None,
        predecessor_receipt_hash: None,
        agent: receipt.agent.0,
        federation_id: federation,
        turn_hash: receipt.turn_hash,
        forest_hash: receipt.forest_hash,
        full_receipt_hash: receipt.receipt_hash(),
        full_pre_state_hash: receipt.pre_state_hash,
        full_post_state_hash: receipt.post_state_hash,
        exact_before: exact.expected(),
        exact_after: exact.successor(),
        proof_outer_before: [0; 32],
        proof_outer_after: [0; 32],
        accepted_statement_digest: [0xa3; 32],
        signed_spending_proof_digest: [0xa4; 32],
        executor_public_key: public.0,
        executor_signature: Signature([0; 64]),
    };
    let frame_hash = unsigned.compute_frame_hash();
    let mut message = Vec::from(FRAME_SIGNATURE_DOMAIN);
    message.extend_from_slice(&frame_hash);
    let frame = UntrustedExactFnspV3FrameV1::authenticate_devnet_executor(
        epoch,
        0,
        predecessor,
        hash,
        frame_hash,
        None,
        None,
        receipt.agent.0,
        federation,
        receipt.turn_hash,
        receipt.forest_hash,
        receipt.receipt_hash(),
        receipt.pre_state_hash,
        receipt.post_state_hash,
        exact.expected(),
        exact.successor(),
        [0; 32],
        [0; 32],
        [0xa3; 32],
        [0xa4; 32],
        public.0,
        dregg_types::sign(key, &message),
    )
    .expect("test frame");
    (activation, frame, encoded_receipt)
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
        let hash = activation_hash(epoch, federation, public.0, 0, None, initial);
        let signature = sign(
            key,
            &UntrustedExactFnspV3ActivationV1::signature_message(hash),
        );
        UntrustedExactFnspV3ActivationV1::authenticate_devnet_executor(
            epoch, initial, federation, 0, None, hash, public.0, signature,
        )
        .expect("signed activation")
    }

    fn frame_candidate(
        store: &PersistentStore,
        activation: &UntrustedExactFnspV3ActivationV1,
        exact: ExactFnspV3StateCasV1,
        key: &SigningKey,
        agent: [u8; 32],
        player_predecessor: Option<(u64, [u8; 32])>,
        exact_predecessor: Option<&UntrustedExactFnspV3FrameV1>,
        tag: u8,
    ) -> UntrustedExactFnspV3FrameV1 {
        let receipt_log_index = store.receipt_chain_len().expect("receipt len");
        let pre_state_hash = [tag.wrapping_add(5); 32];
        let post_state_hash = [tag.wrapping_add(2); 32];
        let mut receipt = TurnReceipt {
            turn_hash: [tag; 32],
            forest_hash: [tag.wrapping_add(1); 32],
            pre_state_hash,
            post_state_hash,
            agent: dregg_cell::CellId(agent),
            federation_id: activation.federation_id,
            previous_receipt_hash: player_predecessor.map(|(_, hash)| hash),
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
        let predecessor = exact_predecessor.map_or(
            ExactFnspV3DurableReceiptLinkV1::EpochActivation(activation.activation_hash),
            |previous| ExactFnspV3DurableReceiptLinkV1::ExactFrame(previous.frame_hash),
        );
        let unsigned = UntrustedExactFnspV3FrameV1 {
            sequence: exact.expected().generation(),
            epoch: activation.epoch,
            receipt_log_index,
            predecessor,
            activation_hash: activation.activation_hash,
            frame_hash: [0; 32],
            predecessor_receipt_index: player_predecessor.map(|(index, _)| index),
            predecessor_receipt_hash: player_predecessor.map(|(_, hash)| hash),
            agent,
            federation_id: activation.federation_id,
            turn_hash: receipt.turn_hash,
            forest_hash: receipt.forest_hash,
            full_receipt_hash: receipt.receipt_hash(),
            full_pre_state_hash: pre_state_hash,
            full_post_state_hash: post_state_hash,
            exact_before: exact.expected(),
            exact_after: exact.successor(),
            proof_outer_before,
            proof_outer_after,
            accepted_statement_digest,
            signed_spending_proof_digest,
            executor_public_key: activation.executor_public_key,
            executor_signature: Signature([0; 64]),
        };
        let frame_hash = unsigned.compute_frame_hash();
        let mut message = Vec::from(FRAME_SIGNATURE_DOMAIN);
        message.extend_from_slice(&frame_hash);
        let signature = sign(key, &message);
        store
            .append_receipt_chain_entry(
                store.receipt_chain_len().expect("receipt len"),
                &postcard::to_stdvec(&receipt).expect("encode receipt"),
            )
            .expect("append receipt");
        UntrustedExactFnspV3FrameV1::authenticate_devnet_executor(
            activation.epoch,
            receipt_log_index,
            predecessor,
            activation.activation_hash,
            frame_hash,
            player_predecessor.map(|(index, _)| index),
            player_predecessor.map(|(_, hash)| hash),
            agent,
            activation.federation_id,
            receipt.turn_hash,
            receipt.forest_hash,
            receipt.receipt_hash(),
            pre_state_hash,
            post_state_hash,
            exact.expected(),
            exact.successor(),
            proof_outer_before,
            proof_outer_after,
            accepted_statement_digest,
            signed_spending_proof_digest,
            activation.executor_public_key,
            signature,
        )
        .expect("signed frame")
    }

    fn append_ordinary_receipt(
        store: &PersistentStore,
        activation: &UntrustedExactFnspV3ActivationV1,
        key: &SigningKey,
        agent: [u8; 32],
        predecessor_hash: Option<[u8; 32]>,
        tag: u8,
    ) -> (u64, [u8; 32]) {
        let index = store.receipt_chain_len().expect("receipt len");
        let mut receipt = TurnReceipt {
            turn_hash: [tag; 32],
            forest_hash: [tag.wrapping_add(1); 32],
            pre_state_hash: [tag.wrapping_add(2); 32],
            post_state_hash: [tag.wrapping_add(3); 32],
            agent: dregg_cell::CellId(agent),
            federation_id: activation.federation_id,
            previous_receipt_hash: predecessor_hash,
            finality: Finality::Final,
            ..TurnReceipt::default()
        };
        receipt.executor_signature = Some(
            sign(key, &receipt.canonical_executor_signed_message())
                .0
                .to_vec(),
        );
        let hash = receipt.receipt_hash();
        store
            .append_receipt_chain_entry(
                index,
                &postcard::to_stdvec(&receipt).expect("encode ordinary receipt"),
            )
            .expect("append ordinary receipt");
        (index, hash)
    }

    #[test]
    fn first_frame_activation_continues_nonempty_exact_prefix_atomically() {
        let store = PersistentStore::open_in_memory().expect("store");
        let initial = store
            .initialize_exact_fnsp_v3_state([
                dregg_circuit::exact_nullifier_aafi::ExactAppendRecord {
                    seq: 0,
                    raw: [0x11; 32],
                    value: 11,
                },
                dregg_circuit::exact_nullifier_aafi::ExactAppendRecord {
                    seq: 1,
                    raw: [0x22; 32],
                    value: 22,
                },
            ])
            .expect("nonempty exact prefix");
        assert_eq!(initial.generation(), 2);
        let (key, public) = generate_keypair();
        let activation = activation_candidate(initial, &key, public);
        let exact = store
            .prepare_exact_fnsp_v3_append([0x33; 32], 33)
            .expect("next exact append");
        let frame = frame_candidate(
            &store,
            &activation,
            exact,
            &key,
            [0xA1; 32],
            None,
            None,
            0x33,
        );
        assert_eq!(frame.sequence(), initial.generation());

        // A correctly signed frame which rewinds sequence to zero is still inadmissible. Dropping
        // the consumed writer leaves activation and exact authority unchanged.
        let mut rewind = frame.clone();
        rewind.sequence = 0;
        rewind.frame_hash = rewind.compute_frame_hash();
        let mut message = Vec::from(FRAME_SIGNATURE_DOMAIN);
        message.extend_from_slice(&rewind.frame_hash);
        rewind.executor_signature = sign(&key, &message);
        let before = store.exact_fnsp_v3_state_head().expect("head before");
        let write = store.db.begin_write().expect("rewind writer");
        assert!(
            stage_exact_fnsp_v3_frame_with_activation_in(
                write,
                exact,
                Some(activation.clone()),
                rewind,
            )
            .is_err()
        );
        assert!(
            store
                .exact_fnsp_v3_activation()
                .expect("activation read")
                .is_none()
        );
        assert_eq!(
            store
                .exact_fnsp_v3_state_head()
                .expect("head after refusal"),
            before
        );

        let write = store.db.begin_write().expect("first-frame writer");
        let (write, staged) = stage_exact_fnsp_v3_frame_with_activation_in(
            write,
            exact,
            Some(activation.clone()),
            frame,
        )
        .expect("atomic activation and first frame");
        write.commit().expect("commit first frame");
        assert_eq!(staged.sequence(), initial.generation());
        assert_eq!(
            store
                .exact_fnsp_v3_activation()
                .expect("activation audit")
                .expect("installed activation")
                .activation_hash(),
            activation.activation_hash()
        );
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
            let frame = frame_candidate(
                &store,
                &activation,
                exact,
                &key,
                [0xA1; 32],
                None,
                None,
                0x41,
            );
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
        let winner = frame_candidate(
            &store,
            &activation,
            exact,
            &key,
            [0xA2; 32],
            None,
            None,
            0x52,
        );
        let write = store.db.begin_write().expect("writer");
        let (write, winner) = stage_exact_fnsp_v3_frame_in(write, exact, winner).expect("winner");
        write.commit().expect("commit winner");

        let stale = frame_candidate(
            &store,
            &activation,
            exact,
            &key,
            [0xA3; 32],
            None,
            Some(&winner),
            0x53,
        );
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
        let mut mixed = frame_candidate(
            &store,
            &activation,
            next,
            &key,
            [0xA4; 32],
            None,
            Some(&winner),
            0x55,
        );
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
        let frame = frame_candidate(
            &store,
            &activation,
            exact,
            &key,
            [0xA5; 32],
            None,
            None,
            0x62,
        );
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
            let frame = frame_candidate(
                &store,
                &activation,
                exact,
                &key,
                [0xA6; 32],
                None,
                None,
                0x72,
            );
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
        let frame = frame_candidate(
            &store,
            &activation,
            exact,
            &key,
            [0xA7; 32],
            None,
            None,
            0x82,
        );
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

    #[test]
    fn global_exact_chain_accepts_different_players_and_new_player_has_no_predecessor() {
        let (store, initial) = setup_store();
        let (key, public) = generate_keypair();
        let activation = activation_candidate(initial, &key, public);
        store
            .install_exact_fnsp_v3_activation(activation.clone())
            .expect("activation");

        let alice_exact = store
            .prepare_exact_fnsp_v3_append([0x91; 32], 91)
            .expect("alice exact");
        let alice = frame_candidate(
            &store,
            &activation,
            alice_exact,
            &key,
            [0xA1; 32],
            None,
            None,
            0x91,
        );
        let write = store.db.begin_write().expect("alice writer");
        let (write, alice) =
            stage_exact_fnsp_v3_frame_in(write, alice_exact, alice).expect("alice frame");
        write.commit().expect("commit alice");

        let bob_exact = store
            .prepare_exact_fnsp_v3_append([0x92; 32], 92)
            .expect("bob exact");
        let bob = frame_candidate(
            &store,
            &activation,
            bob_exact,
            &key,
            [0xB2; 32],
            None,
            Some(&alice),
            0x92,
        );
        let bob_receipt_hash = bob.full_receipt_hash();
        let write = store.db.begin_write().expect("bob writer");
        let (write, bob) = stage_exact_fnsp_v3_frame_in(write, bob_exact, bob).expect("bob frame");
        write.commit().expect("commit bob");

        assert_eq!(bob.predecessor_receipt_index(), None);
        assert_eq!(bob.predecessor_receipt_hash(), None);
        assert_eq!(bob.agent(), [0xB2; 32]);
        assert_eq!(
            store
                .exact_fnsp_v3_committed_frame_head()
                .expect("head")
                .expect("frame")
                .full_receipt_hash(),
            bob_receipt_hash
        );
    }

    #[test]
    fn recovery_accepts_ordinary_and_cross_player_receipt_interleaving() {
        let directory = tempfile::tempdir().expect("tempdir");
        let path = directory.path().join("exact-interleaving.redb");
        let expected_head;
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

            let exact1 = store
                .prepare_exact_fnsp_v3_append([0xA8; 32], 108)
                .expect("exact one");
            let frame1 = frame_candidate(
                &store,
                &activation,
                exact1,
                &key,
                [0xA1; 32],
                None,
                None,
                0xA8,
            );
            let alice_exact_receipt = frame1.full_receipt_hash();
            let write = store.db.begin_write().expect("first writer");
            let (write, frame1) =
                stage_exact_fnsp_v3_frame_in(write, exact1, frame1).expect("first frame");
            write.commit().expect("commit first");

            let (alice_ordinary_index, alice_ordinary_hash) = append_ordinary_receipt(
                &store,
                &activation,
                &key,
                [0xA1; 32],
                Some(alice_exact_receipt),
                0xA9,
            );
            append_ordinary_receipt(&store, &activation, &key, [0xB2; 32], None, 0xAA);

            let exact2 = store
                .prepare_exact_fnsp_v3_append([0xAB; 32], 109)
                .expect("exact two");
            let frame2 = frame_candidate(
                &store,
                &activation,
                exact2,
                &key,
                [0xA1; 32],
                Some((alice_ordinary_index, alice_ordinary_hash)),
                Some(&frame1),
                0xAB,
            );
            assert_eq!(frame2.receipt_log_index(), 3);
            expected_head = frame2.frame_hash();
            let write = store.db.begin_write().expect("second writer");
            let (write, _) =
                stage_exact_fnsp_v3_frame_in(write, exact2, frame2).expect("second frame");
            write.commit().expect("commit second");
        }

        let reopened = PersistentStore::open(&path).expect("interleaved recovery");
        assert_eq!(reopened.receipt_chain_len().expect("receipt len"), 4);
        assert_eq!(
            reopened
                .exact_fnsp_v3_committed_frame_head()
                .expect("head")
                .expect("frame")
                .frame_hash(),
            expected_head
        );
    }

    #[test]
    fn stale_same_player_receipt_predecessor_is_rejected_without_exact_mutation() {
        let (store, initial) = setup_store();
        let (key, public) = generate_keypair();
        let activation = activation_candidate(initial, &key, public);
        store
            .install_exact_fnsp_v3_activation(activation.clone())
            .expect("activation");
        let exact1 = store
            .prepare_exact_fnsp_v3_append([0xB1; 32], 111)
            .expect("first exact");
        let frame1 = frame_candidate(
            &store,
            &activation,
            exact1,
            &key,
            [0xA1; 32],
            None,
            None,
            0xB1,
        );
        let first_receipt_hash = frame1.full_receipt_hash();
        let write = store.db.begin_write().expect("first writer");
        let (write, _frame1) =
            stage_exact_fnsp_v3_frame_in(write, exact1, frame1).expect("first frame");
        write.commit().expect("commit first");

        let (ordinary_index, ordinary_hash) = append_ordinary_receipt(
            &store,
            &activation,
            &key,
            [0xA1; 32],
            Some(first_receipt_hash),
            0xB2,
        );
        let head_before = store.exact_fnsp_v3_state_head().expect("head before");
        let receipt_len_before = store.receipt_chain_len().expect("receipt len");
        let mut stale = TurnReceipt {
            turn_hash: [0xB3; 32],
            forest_hash: [0xB4; 32],
            pre_state_hash: [0xB5; 32],
            post_state_hash: [0xB6; 32],
            agent: dregg_cell::CellId([0xA1; 32]),
            federation_id: activation.federation_id,
            previous_receipt_hash: Some(first_receipt_hash),
            finality: Finality::Final,
            ..TurnReceipt::default()
        };
        stale.executor_signature = Some(
            sign(&key, &stale.canonical_executor_signed_message())
                .0
                .to_vec(),
        );
        assert!(
            store
                .append_receipt_chain_entry(
                    receipt_len_before,
                    &postcard::to_stdvec(&stale).expect("encode stale receipt"),
                )
                .is_err(),
            "the derived head must reject a signed stale predecessor at receipt append"
        );
        assert_eq!(
            store.receipt_chain_len().expect("receipt len after"),
            receipt_len_before
        );
        assert_eq!(
            store.exact_fnsp_v3_state_head().expect("head after"),
            head_before
        );
        let read = store.db.begin_read().expect("read head index");
        let heads = read
            .open_table(EXACT_FNSP_V3_RECEIPT_HEADS)
            .expect("receipt heads");
        assert_eq!(
            decode_receipt_head(
                heads
                    .get(&[0xA1; 32])
                    .expect("read indexed head")
                    .expect("indexed head")
                    .value(),
            )
            .expect("decode indexed head"),
            (ordinary_index, ordinary_hash),
            "failed append must not advance the online head"
        );
    }

    #[test]
    fn online_boundary_matches_full_audit_after_large_interleaved_receipt_table() {
        let directory = tempfile::tempdir().expect("tempdir");
        let path = directory.path().join("exact-online-boundary.redb");
        let exact_agent = [3u8; 32];
        let exact_receipt_hash;
        let (key, public) = generate_keypair();
        {
            let store = PersistentStore::open(&path).expect("store");
            let initial = store
                .initialize_exact_fnsp_v3_state(std::iter::empty())
                .expect("exact genesis");
            let activation = activation_candidate(initial, &key, public);
            store
                .install_exact_fnsp_v3_activation(activation.clone())
                .expect("activation");

            let mut player_heads = HashMap::new();
            for tag in 1u8..=128 {
                let agent = [tag % 8; 32];
                let previous = player_heads.get(&agent).map(|(_, hash)| *hash);
                let head = append_ordinary_receipt(&store, &activation, &key, agent, previous, tag);
                player_heads.insert(agent, head);
            }
            let exact = store
                .prepare_exact_fnsp_v3_append([0xD1; 32], 209)
                .expect("exact append");
            let frame = frame_candidate(
                &store,
                &activation,
                exact,
                &key,
                exact_agent,
                player_heads.get(&exact_agent).copied(),
                None,
                0xD1,
            );
            exact_receipt_hash = frame.full_receipt_hash();
            let expected_frame_hash = frame.frame_hash();
            let write = store.db.begin_write().expect("writer");
            let (write, _) = stage_exact_fnsp_v3_frame_in(write, exact, frame)
                .expect("online writer over large receipt table");
            write.commit().expect("commit exact frame");

            let (live_activation, live_head) = store
                .exact_fnsp_v3_live_authority()
                .expect("live authority")
                .expect("activated live authority");
            let full_activation = store
                .exact_fnsp_v3_activation()
                .expect("full activation audit")
                .expect("full activation");
            let full_head = store
                .exact_fnsp_v3_committed_frame_head()
                .expect("full frame audit")
                .expect("full frame");
            assert_eq!(
                live_activation.activation_hash(),
                full_activation.activation_hash()
            );
            assert_eq!(
                live_head.expect("live frame").frame_hash(),
                full_head.frame_hash()
            );
            assert_eq!(full_head.frame_hash(), expected_frame_hash);
        }

        // Reopen performs the full O(receipts + frames) replay and rebuilds the online index.
        // A subsequent same-agent append proves that rebuilt index retained the exact receipt.
        let reopened = PersistentStore::open(&path).expect("full replay + index rebuild");
        let activation = reopened
            .exact_fnsp_v3_activation()
            .expect("activation audit")
            .expect("activation");
        let result = append_ordinary_receipt(
            &reopened,
            &activation.0,
            &key,
            exact_agent,
            Some(exact_receipt_hash),
            0xD2,
        );
        assert_eq!(result.0, 129);
    }

    #[test]
    fn online_writer_rejects_missing_derived_agent_head_before_exact_cas() {
        let (store, initial) = setup_store();
        let (key, public) = generate_keypair();
        let activation = activation_candidate(initial, &key, public);
        store
            .install_exact_fnsp_v3_activation(activation.clone())
            .expect("activation");
        let exact = store
            .prepare_exact_fnsp_v3_append([0xE1; 32], 225)
            .expect("exact append");
        let frame = frame_candidate(
            &store,
            &activation,
            exact,
            &key,
            [0xE2; 32],
            None,
            None,
            0xE1,
        );
        let exact_before = store.exact_fnsp_v3_state_head().expect("exact before");
        let write = store.db.begin_write().expect("tamper derived index");
        write
            .open_table(EXACT_FNSP_V3_RECEIPT_HEADS)
            .expect("receipt heads")
            .remove(&[0xE2; 32])
            .expect("remove derived head");
        write.commit().expect("commit derived-index fault");

        let write = store.db.begin_write().expect("exact writer");
        assert!(stage_exact_fnsp_v3_frame_in(write, exact, frame).is_err());
        assert_eq!(
            store.exact_fnsp_v3_state_head().expect("exact after"),
            exact_before,
            "online-index failure must occur before exact CAS mutation"
        );
    }
}
