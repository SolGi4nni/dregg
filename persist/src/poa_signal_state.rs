//! Durable authority for finalized Path of Angels Signal transitions.
//!
//! Game semantics remain Lean-owned.  This module stores the adapter's exact
//! canonical judge input/output and advances one authenticated Canon head in
//! the same redb transaction as the carrying finalized turn.  Rust validates
//! only storage structure: exact predecessor CAS, dense transition sequence,
//! immutable deployment/config bytes, commit-coordinate binding, and exact
//! replay presence/bytes.

use redb::{ReadableTable, ReadableTableMetadata, WriteTransaction};
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};

use crate::{CommitRecord, PersistentStore, Result, StoreError, tables};

const HEAD_MAGIC: [u8; 4] = *b"PSHD";
const TRANSITION_MAGIC: [u8; 4] = *b"PSTR";
const WIRE_VERSION: u8 = 1;
const HEADER_LEN: usize = 8;
const HEAD_FIXED_LEN: usize = HEADER_LEN + 32 + 32 + 8 + 8 + 8 + 32 + 4 + 4;
const TRANSITION_FIXED_LEN: usize =
    HEADER_LEN + 32 + 8 + 8 + 32 + 32 + 32 + 32 + 32 + 32 + 32 + 4 + 4 + 4 + 4;
const SEAL_LEN: usize = 32;

/// Maximum bytes in one canonical config+Canon image or one exact judge wire.
///
/// This mirrors the current PoA outer-wire cap.  A transition temporarily
/// contains two heads and two judge wires, but no individual authority-bearing
/// image may exceed this bound.
pub const MAX_POA_SIGNAL_WIRE_BYTES_V1: usize = 16 * 1024 * 1024;

/// Result of the operator-only, globally singular PoA Signal genesis ceremony.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PoaSignalGenesisInitOutcome {
    /// The exact genesis head was inserted and committed by this call.
    Installed,
    /// The store already held the one exact encoded head and was not mutated.
    AlreadyIdentical,
}

/// Current durable head for one independently named PoA Signal authority.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PoaSignalHeadV1 {
    authority_id: [u8; 32],
    deployment_digest: [u8; 32],
    transition_count: u64,
    world_sequence: u64,
    canon_revision: u64,
    last_transition_digest: [u8; 32],
    config: Vec<u8>,
    canon: Vec<u8>,
}

impl PoaSignalHeadV1 {
    /// Construct the immutable zero-transition head installed by the deployment
    /// activation ceremony.  The bytes are opaque here and must already have
    /// been authenticated and canonically emitted by the higher layer.
    pub fn genesis(
        authority_id: [u8; 32],
        deployment_digest: [u8; 32],
        world_sequence: u64,
        canon_revision: u64,
        config: Vec<u8>,
        canon: Vec<u8>,
    ) -> Result<Self> {
        let head = Self {
            authority_id,
            deployment_digest,
            transition_count: 0,
            world_sequence,
            canon_revision,
            last_transition_digest: [0; 32],
            config,
            canon,
        };
        head.validate()?;
        Ok(head)
    }

    /// Stable authority/deployment-session identifier used as the table key.
    pub const fn authority_id(&self) -> [u8; 32] {
        self.authority_id
    }

    /// Digest of the authenticated deployment activation.
    pub const fn deployment_digest(&self) -> [u8; 32] {
        self.deployment_digest
    }

    /// Number of finalized Signal transitions following genesis.
    pub const fn transition_count(&self) -> u64 {
        self.transition_count
    }

    /// World sequence projected from the exact canonical Canon bytes.
    pub const fn world_sequence(&self) -> u64 {
        self.world_sequence
    }

    /// Canon revision projected from the exact canonical Canon bytes.
    pub const fn canon_revision(&self) -> u64 {
        self.canon_revision
    }

    /// Digest of the transition that produced this head, or zero at genesis.
    pub const fn last_transition_digest(&self) -> [u8; 32] {
        self.last_transition_digest
    }

    /// Exact authenticated Signal configuration bytes.
    pub fn config(&self) -> &[u8] {
        &self.config
    }

    /// Exact canonical Canon bytes.
    pub fn canon(&self) -> &[u8] {
        &self.canon
    }

    /// Domain-separated digest of the complete strict head wire.
    pub fn digest(&self) -> [u8; 32] {
        head_seal(
            &self
                .encode_without_seal()
                .expect("validated PoA Signal head"),
        )
    }

    fn validate(&self) -> Result<()> {
        if self.config.is_empty() || self.canon.is_empty() {
            return Err(integrity(
                "PoA Signal head config and Canon must both be non-empty",
            ));
        }
        checked_combined_len(&self.config, &self.canon, "PoA Signal head")?;
        if self.transition_count == 0 && self.last_transition_digest != [0; 32] {
            return Err(integrity(
                "PoA Signal genesis head has a nonzero last-transition digest",
            ));
        }
        if self.transition_count != 0 && self.last_transition_digest == [0; 32] {
            return Err(integrity(
                "PoA Signal non-genesis head has a zero last-transition digest",
            ));
        }
        Ok(())
    }

    fn encode_without_seal(&self) -> Result<Vec<u8>> {
        self.validate()?;
        let config_len = encoded_len(self.config.len(), "PoA Signal config")?;
        let canon_len = encoded_len(self.canon.len(), "PoA Signal Canon")?;
        let capacity = HEAD_FIXED_LEN
            .checked_add(self.config.len())
            .and_then(|n| n.checked_add(self.canon.len()))
            .ok_or_else(|| integrity("PoA Signal head length overflow"))?;
        let mut out = Vec::with_capacity(capacity);
        out.extend_from_slice(&HEAD_MAGIC);
        out.push(WIRE_VERSION);
        out.extend_from_slice(&[0; 3]);
        out.extend_from_slice(&self.authority_id);
        out.extend_from_slice(&self.deployment_digest);
        out.extend_from_slice(&self.transition_count.to_le_bytes());
        out.extend_from_slice(&self.world_sequence.to_le_bytes());
        out.extend_from_slice(&self.canon_revision.to_le_bytes());
        out.extend_from_slice(&self.last_transition_digest);
        out.extend_from_slice(&config_len.to_le_bytes());
        out.extend_from_slice(&canon_len.to_le_bytes());
        out.extend_from_slice(&self.config);
        out.extend_from_slice(&self.canon);
        Ok(out)
    }

    fn encode(&self) -> Result<Vec<u8>> {
        let mut out = self.encode_without_seal()?;
        out.extend_from_slice(&head_seal(&out));
        Ok(out)
    }

    fn decode(bytes: &[u8]) -> Result<Self> {
        if bytes.len() < HEAD_FIXED_LEN + SEAL_LEN {
            return Err(integrity("PoA Signal head wire is truncated"));
        }
        if bytes[..4] != HEAD_MAGIC {
            return Err(integrity("PoA Signal head wire has wrong magic"));
        }
        if bytes[4] != WIRE_VERSION || bytes[5..8] != [0; 3] {
            return Err(integrity(
                "PoA Signal head wire has unsupported version or reserved bytes",
            ));
        }
        let payload_end = bytes.len() - SEAL_LEN;
        if head_seal(&bytes[..payload_end]) != bytes[payload_end..] {
            return Err(integrity("PoA Signal head seal mismatch"));
        }
        let authority_id = array_at::<32>(bytes, 8)?;
        let deployment_digest = array_at::<32>(bytes, 40)?;
        let transition_count = u64_at(bytes, 72)?;
        let world_sequence = u64_at(bytes, 80)?;
        let canon_revision = u64_at(bytes, 88)?;
        let last_transition_digest = array_at::<32>(bytes, 96)?;
        let config_len = u32_at(bytes, 128)? as usize;
        let canon_len = u32_at(bytes, 132)? as usize;
        let expected = HEAD_FIXED_LEN
            .checked_add(config_len)
            .and_then(|n| n.checked_add(canon_len))
            .and_then(|n| n.checked_add(SEAL_LEN))
            .ok_or_else(|| integrity("PoA Signal head length overflow"))?;
        if expected != bytes.len() {
            return Err(integrity("PoA Signal head has trailing or missing bytes"));
        }
        let config_end = HEAD_FIXED_LEN + config_len;
        let head = Self {
            authority_id,
            deployment_digest,
            transition_count,
            world_sequence,
            canon_revision,
            last_transition_digest,
            config: bytes[HEAD_FIXED_LEN..config_end].to_vec(),
            canon: bytes[config_end..payload_end].to_vec(),
        };
        head.validate()?;
        Ok(head)
    }
}

/// Adapter-prepared successor material consumed by the atomic finalized-turn
/// weld. Authority fields and raw construction are private; external callers
/// can obtain one only from an opaque native-Lean acceptance carrier. Finality
/// is established separately by the receipt/executor commit apex.
///
/// ```compile_fail
/// let _raw_constructor = dregg_persist::PreparedPoaSignalTransitionV1::new;
/// ```
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PreparedPoaSignalTransitionV1 {
    authority_id: [u8; 32],
    expected_predecessor_head_digest: [u8; 32],
    successor_world_sequence: u64,
    successor_canon_revision: u64,
    successor_canon: Vec<u8>,
    judge_input: Vec<u8>,
    judge_output: Vec<u8>,
}

impl PreparedPoaSignalTransitionV1 {
    /// Construct a structurally bounded storage candidate.
    ///
    /// This checks byte bounds only. The caller must derive the authority and
    /// predecessor from finalized state and validate the exact Lean verdict.
    pub(crate) fn new(
        authority_id: [u8; 32],
        expected_predecessor_head_digest: [u8; 32],
        successor_world_sequence: u64,
        successor_canon_revision: u64,
        successor_canon: Vec<u8>,
        judge_input: Vec<u8>,
        judge_output: Vec<u8>,
    ) -> Result<Self> {
        for (what, bytes) in [
            ("successor Canon", successor_canon.as_slice()),
            ("judge input", judge_input.as_slice()),
            ("judge output", judge_output.as_slice()),
        ] {
            if bytes.is_empty() {
                return Err(integrity(format!("PoA Signal {what} is empty")));
            }
            if bytes.len() > MAX_POA_SIGNAL_WIRE_BYTES_V1 {
                return Err(integrity(format!(
                    "PoA Signal {what} exceeds {MAX_POA_SIGNAL_WIRE_BYTES_V1} bytes"
                )));
            }
        }
        Ok(Self {
            authority_id,
            expected_predecessor_head_digest,
            successor_world_sequence,
            successor_canon_revision,
            successor_canon,
            judge_input,
            judge_output,
        })
    }

    /// Prepare a transition from an opaque native-Lean acceptance carrier.
    ///
    /// The carrier binds the output to the exact `judge_input`; its private
    /// fields make caller-authored output bytes unrepresentable here.  This
    /// boundary also checks that the persistence projection is exactly the
    /// successor projection present in those Lean-authored bytes.  Finality is
    /// still established only by the receipt/executor commit apex.
    #[allow(clippy::too_many_arguments)]
    pub fn from_lean_accepted(
        authority_id: [u8; 32],
        expected_predecessor_head_digest: [u8; 32],
        successor_world_sequence: u64,
        successor_canon_revision: u64,
        successor_canon: Vec<u8>,
        judge_input: Vec<u8>,
        accepted: dregg_lean_ffi::poa_ffi::AcceptedPoaSignalOutput,
    ) -> Result<Self> {
        if !accepted.was_judged_for(&judge_input) {
            return Err(integrity(
                "PoA Signal Lean acceptance does not belong to the supplied judge input",
            ));
        }
        validate_accepted_projection(
            authority_id,
            successor_world_sequence,
            successor_canon_revision,
            &successor_canon,
            &judge_input,
            accepted.as_str().as_bytes(),
        )?;
        Self::new(
            authority_id,
            expected_predecessor_head_digest,
            successor_world_sequence,
            successor_canon_revision,
            successor_canon,
            judge_input,
            accepted.into_string().into_bytes(),
        )
    }

    /// Raw construction for cross-crate corruption/atomicity fixtures only.
    #[cfg(feature = "test-support")]
    #[doc(hidden)]
    #[allow(clippy::too_many_arguments)]
    pub fn new_for_test(
        authority_id: [u8; 32],
        expected_predecessor_head_digest: [u8; 32],
        successor_world_sequence: u64,
        successor_canon_revision: u64,
        successor_canon: Vec<u8>,
        judge_input: Vec<u8>,
        judge_output: Vec<u8>,
    ) -> Result<Self> {
        Self::new(
            authority_id,
            expected_predecessor_head_digest,
            successor_world_sequence,
            successor_canon_revision,
            successor_canon,
            judge_input,
            judge_output,
        )
    }

    /// Authority this candidate advances.
    pub const fn authority_id(&self) -> [u8; 32] {
        self.authority_id
    }

    /// CAS token captured with the persisted predecessor.
    pub const fn expected_predecessor_head_digest(&self) -> [u8; 32] {
        self.expected_predecessor_head_digest
    }

    /// SHA-256 of the exact canonical Lean judge input.
    pub fn judge_input_digest(&self) -> [u8; 32] {
        sha256(&self.judge_input)
    }

    /// SHA-256 of the exact canonical Lean judge output.
    pub fn judge_output_digest(&self) -> [u8; 32] {
        sha256(&self.judge_output)
    }

    /// Exact canonical Lean input retained by the finalized-transition weld.
    pub fn judge_input(&self) -> &[u8] {
        &self.judge_input
    }

    /// Exact canonical Lean output retained by the finalized-transition weld.
    pub fn judge_output(&self) -> &[u8] {
        &self.judge_output
    }
}

fn validate_accepted_projection(
    authority_id: [u8; 32],
    successor_world_sequence: u64,
    successor_canon_revision: u64,
    successor_canon: &[u8],
    judge_input: &[u8],
    judge_output: &[u8],
) -> Result<()> {
    let input: serde_json::Value = serde_json::from_slice(judge_input)
        .map_err(|error| integrity(format!("PoA Signal judge input is not JSON: {error}")))?;
    for path in [
        "/canon/federation_id",
        "/carrier/federation_id",
        "/request/federation_id",
    ] {
        let encoded = input
            .pointer(path)
            .and_then(serde_json::Value::as_str)
            .ok_or_else(|| integrity(format!("PoA Signal judge input lacks {path}")))?;
        let decoded = dregg_types::parse_hex32(encoded)
            .ok_or_else(|| integrity(format!("PoA Signal {path} is not a digest")))?;
        if decoded != authority_id {
            return Err(integrity(format!(
                "PoA Signal judge input {path} does not name the prepared authority"
            )));
        }
    }

    let output: serde_json::Value = serde_json::from_slice(judge_output)
        .map_err(|error| integrity(format!("PoA Signal Lean output is not JSON: {error}")))?;
    let output_sequence = output
        .pointer("/successor_world/sequence")
        .and_then(serde_json::Value::as_u64)
        .ok_or_else(|| integrity("PoA Signal Lean output lacks successor world sequence"))?;
    let output_revision = output
        .pointer("/successor_canon/revision")
        .and_then(serde_json::Value::as_u64)
        .ok_or_else(|| integrity("PoA Signal Lean output lacks successor Canon revision"))?;
    if output_sequence != successor_world_sequence || output_revision != successor_canon_revision {
        return Err(integrity(
            "PoA Signal persistence coordinates differ from the native Lean successor",
        ));
    }
    let projected: serde_json::Value = serde_json::from_slice(successor_canon)
        .map_err(|error| integrity(format!("PoA Signal successor Canon is not JSON: {error}")))?;
    if output.pointer("/successor_canon") != Some(&projected) {
        return Err(integrity(
            "PoA Signal persisted Canon differs from the native Lean successor",
        ));
    }
    Ok(())
}

/// Immutable typed record for one finalized Signal transition.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PoaSignalTransitionV1 {
    authority_id: [u8; 32],
    sequence: u64,
    commit_ordinal: u64,
    turn_hash: [u8; 32],
    receipt_hash: [u8; 32],
    predecessor_head_digest: [u8; 32],
    successor_head_digest: [u8; 32],
    transition_digest: [u8; 32],
    judge_input_digest: [u8; 32],
    judge_output_digest: [u8; 32],
    predecessor_head: Vec<u8>,
    successor_head: Vec<u8>,
    judge_input: Vec<u8>,
    judge_output: Vec<u8>,
}

impl PoaSignalTransitionV1 {
    /// Authority advanced by this transition.
    pub const fn authority_id(&self) -> [u8; 32] {
        self.authority_id
    }

    /// Dense one-based game transition sequence.
    pub const fn sequence(&self) -> u64 {
        self.sequence
    }

    /// Generic finalized commit ordinal carrying the transition.
    pub const fn commit_ordinal(&self) -> u64 {
        self.commit_ordinal
    }

    /// Carrying finalized turn hash.
    pub const fn turn_hash(&self) -> [u8; 32] {
        self.turn_hash
    }

    /// Carrying finalized receipt hash.
    pub const fn receipt_hash(&self) -> [u8; 32] {
        self.receipt_hash
    }

    /// Exact predecessor head digest used as the durable CAS token.
    pub const fn predecessor_head_digest(&self) -> [u8; 32] {
        self.predecessor_head_digest
    }

    /// Exact successor head digest.
    pub const fn successor_head_digest(&self) -> [u8; 32] {
        self.successor_head_digest
    }

    /// Domain-separated transition-chain digest.
    pub const fn transition_digest(&self) -> [u8; 32] {
        self.transition_digest
    }

    /// SHA-256 of the exact canonical Lean input bytes.
    pub const fn judge_input_digest(&self) -> [u8; 32] {
        self.judge_input_digest
    }

    /// SHA-256 of the exact canonical Lean output bytes.
    pub const fn judge_output_digest(&self) -> [u8; 32] {
        self.judge_output_digest
    }

    /// Exact canonical Lean input bytes.
    pub fn judge_input(&self) -> &[u8] {
        &self.judge_input
    }

    /// Exact canonical Lean output bytes.
    pub fn judge_output(&self) -> &[u8] {
        &self.judge_output
    }

    /// Decode the exact predecessor image carried by this immutable row.
    pub fn predecessor_head(&self) -> Result<PoaSignalHeadV1> {
        PoaSignalHeadV1::decode(&self.predecessor_head)
    }

    /// Decode the exact successor image carried by this immutable row.
    pub fn successor_head(&self) -> Result<PoaSignalHeadV1> {
        PoaSignalHeadV1::decode(&self.successor_head)
    }

    /// Deterministically reconstruct the complete storage row from a predecessor,
    /// generic finalized commit, and already-judged semantic candidate.
    ///
    /// This is an audit primitive, not a semantic judge: callers must obtain the
    /// candidate by invoking the authoritative evaluator. In particular it does
    /// not read or trust this row's stored successor. Comparing its result with a
    /// stored row proves that every storage field, including the successor head
    /// and transition-chain digest, was derived from those inputs.
    pub fn reconstruct_for_audit(
        predecessor: &PoaSignalHeadV1,
        commit: &CommitRecord,
        candidate: &PreparedPoaSignalTransitionV1,
    ) -> Result<Self> {
        plan_transition(
            predecessor.encode()?,
            predecessor.clone(),
            commit.ordinal,
            commit,
            candidate,
        )
    }

    fn key(&self) -> [u8; 40] {
        transition_key(self.authority_id, self.sequence)
    }

    fn encode_without_seal(&self) -> Result<Vec<u8>> {
        let predecessor_len = encoded_len(self.predecessor_head.len(), "predecessor head")?;
        let successor_len = encoded_len(self.successor_head.len(), "successor head")?;
        let input_len = encoded_len(self.judge_input.len(), "judge input")?;
        let output_len = encoded_len(self.judge_output.len(), "judge output")?;
        let capacity = [
            self.predecessor_head.len(),
            self.successor_head.len(),
            self.judge_input.len(),
            self.judge_output.len(),
        ]
        .into_iter()
        .try_fold(TRANSITION_FIXED_LEN, |acc, n| acc.checked_add(n))
        .ok_or_else(|| integrity("PoA Signal transition length overflow"))?;
        let mut out = Vec::with_capacity(capacity);
        out.extend_from_slice(&TRANSITION_MAGIC);
        out.push(WIRE_VERSION);
        out.extend_from_slice(&[0; 3]);
        out.extend_from_slice(&self.authority_id);
        out.extend_from_slice(&self.sequence.to_le_bytes());
        out.extend_from_slice(&self.commit_ordinal.to_le_bytes());
        out.extend_from_slice(&self.turn_hash);
        out.extend_from_slice(&self.receipt_hash);
        out.extend_from_slice(&self.predecessor_head_digest);
        out.extend_from_slice(&self.successor_head_digest);
        out.extend_from_slice(&self.transition_digest);
        out.extend_from_slice(&self.judge_input_digest);
        out.extend_from_slice(&self.judge_output_digest);
        out.extend_from_slice(&predecessor_len.to_le_bytes());
        out.extend_from_slice(&successor_len.to_le_bytes());
        out.extend_from_slice(&input_len.to_le_bytes());
        out.extend_from_slice(&output_len.to_le_bytes());
        out.extend_from_slice(&self.predecessor_head);
        out.extend_from_slice(&self.successor_head);
        out.extend_from_slice(&self.judge_input);
        out.extend_from_slice(&self.judge_output);
        Ok(out)
    }

    fn encode(&self) -> Result<Vec<u8>> {
        self.validate()?;
        let mut out = self.encode_without_seal()?;
        out.extend_from_slice(&transition_seal(&out));
        Ok(out)
    }

    fn decode(bytes: &[u8]) -> Result<Self> {
        if bytes.len() < TRANSITION_FIXED_LEN + SEAL_LEN {
            return Err(integrity("PoA Signal transition wire is truncated"));
        }
        if bytes[..4] != TRANSITION_MAGIC {
            return Err(integrity("PoA Signal transition wire has wrong magic"));
        }
        if bytes[4] != WIRE_VERSION || bytes[5..8] != [0; 3] {
            return Err(integrity(
                "PoA Signal transition wire has unsupported version or reserved bytes",
            ));
        }
        let payload_end = bytes.len() - SEAL_LEN;
        if transition_seal(&bytes[..payload_end]) != bytes[payload_end..] {
            return Err(integrity("PoA Signal transition seal mismatch"));
        }
        let predecessor_len = u32_at(bytes, 280)? as usize;
        let successor_len = u32_at(bytes, 284)? as usize;
        let input_len = u32_at(bytes, 288)? as usize;
        let output_len = u32_at(bytes, 292)? as usize;
        let expected = [predecessor_len, successor_len, input_len, output_len]
            .into_iter()
            .try_fold(TRANSITION_FIXED_LEN, |acc, n| acc.checked_add(n))
            .and_then(|n| n.checked_add(SEAL_LEN))
            .ok_or_else(|| integrity("PoA Signal transition length overflow"))?;
        if expected != bytes.len() {
            return Err(integrity(
                "PoA Signal transition has trailing or missing bytes",
            ));
        }
        let mut cursor = TRANSITION_FIXED_LEN;
        let predecessor_head = take_vec(bytes, &mut cursor, predecessor_len)?;
        let successor_head = take_vec(bytes, &mut cursor, successor_len)?;
        let judge_input = take_vec(bytes, &mut cursor, input_len)?;
        let judge_output = take_vec(bytes, &mut cursor, output_len)?;
        if cursor != payload_end {
            return Err(integrity("PoA Signal transition payload length mismatch"));
        }
        let transition = Self {
            authority_id: array_at::<32>(bytes, 8)?,
            sequence: u64_at(bytes, 40)?,
            commit_ordinal: u64_at(bytes, 48)?,
            turn_hash: array_at::<32>(bytes, 56)?,
            receipt_hash: array_at::<32>(bytes, 88)?,
            predecessor_head_digest: array_at::<32>(bytes, 120)?,
            successor_head_digest: array_at::<32>(bytes, 152)?,
            transition_digest: array_at::<32>(bytes, 184)?,
            judge_input_digest: array_at::<32>(bytes, 216)?,
            judge_output_digest: array_at::<32>(bytes, 248)?,
            predecessor_head,
            successor_head,
            judge_input,
            judge_output,
        };
        transition.validate()?;
        Ok(transition)
    }

    fn validate(&self) -> Result<()> {
        for (what, bytes) in [
            ("judge input", self.judge_input.as_slice()),
            ("judge output", self.judge_output.as_slice()),
        ] {
            if bytes.is_empty() || bytes.len() > MAX_POA_SIGNAL_WIRE_BYTES_V1 {
                return Err(integrity(format!(
                    "PoA Signal {what} is empty or exceeds the wire cap"
                )));
            }
        }
        if self.sequence == 0 {
            return Err(integrity("PoA Signal transition sequence is zero"));
        }
        let predecessor = PoaSignalHeadV1::decode(&self.predecessor_head)?;
        let successor = PoaSignalHeadV1::decode(&self.successor_head)?;
        if predecessor.authority_id != self.authority_id
            || successor.authority_id != self.authority_id
            || predecessor.deployment_digest != successor.deployment_digest
            || predecessor.config != successor.config
            || predecessor.digest() != self.predecessor_head_digest
            || successor.digest() != self.successor_head_digest
        {
            return Err(integrity(
                "PoA Signal transition head identity/digest/config mismatch",
            ));
        }
        if predecessor.transition_count.checked_add(1) != Some(self.sequence)
            || successor.transition_count != self.sequence
            || predecessor.world_sequence.checked_add(1) != Some(successor.world_sequence)
            || predecessor.canon_revision.checked_add(1) != Some(successor.canon_revision)
        {
            return Err(integrity(
                "PoA Signal transition does not advance sequence/revision exactly once",
            ));
        }
        if sha256(&self.judge_input) != self.judge_input_digest
            || sha256(&self.judge_output) != self.judge_output_digest
        {
            return Err(integrity("PoA Signal judge byte digest mismatch"));
        }
        let expected_transition_digest = transition_core_digest(
            self.authority_id,
            self.sequence,
            self.commit_ordinal,
            self.turn_hash,
            self.receipt_hash,
            self.predecessor_head_digest,
            &successor,
            self.judge_input_digest,
            self.judge_output_digest,
        );
        if expected_transition_digest != self.transition_digest
            || successor.last_transition_digest != self.transition_digest
        {
            return Err(integrity("PoA Signal transition-chain digest mismatch"));
        }
        Ok(())
    }
}

/// One structurally audited, immutable authority history captured from a
/// single redb read transaction. Semantic replay starts at [`Self::genesis`]
/// and must derive [`Self::current`] rather than trusting intermediate heads.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PoaSignalHistoryV1 {
    genesis: PoaSignalHeadV1,
    current: PoaSignalHeadV1,
    transitions: Vec<PoaSignalTransitionV1>,
}

impl PoaSignalHistoryV1 {
    /// Exact zero-transition image at the start of the retained journal.
    pub const fn genesis(&self) -> &PoaSignalHeadV1 {
        &self.genesis
    }

    /// Exact currently published head.
    pub const fn current(&self) -> &PoaSignalHeadV1 {
        &self.current
    }

    /// Dense, sequence-ordered immutable transition rows.
    pub fn transitions(&self) -> &[PoaSignalTransitionV1] {
        &self.transitions
    }
}

impl PersistentStore {
    /// Atomically install the one PoA deployment head, or accept an exact retry.
    ///
    /// Unlike [`Self::initialize_poa_signal_head`], this operator ceremony is
    /// globally singular: the first install requires no generic commits and no
    /// prior PoA head or transition under *any* authority. A retry succeeds only
    /// when the table contains exactly the same encoded zero-transition head.
    /// That no-op remains safe after ordinary commits have begun because it does
    /// not reinterpret or mutate them. Any different head, additional authority,
    /// or transition history refuses inside the same redb transaction.
    pub fn initialize_poa_signal_head_if_empty_or_identical(
        &self,
        head: &PoaSignalHeadV1,
    ) -> Result<PoaSignalGenesisInitOutcome> {
        if head.transition_count != 0 {
            return Err(integrity(
                "PoA Signal initialization requires a genesis head",
            ));
        }
        let encoded = head.encode()?;
        let write = self.db.begin_write()?;
        let cursor = {
            let metadata = write.open_table(tables::METADATA)?;
            metadata
                .get(tables::META_COMMIT_CURSOR)?
                .map(|value| value.value())
                .unwrap_or(0)
        };
        {
            let heads = write.open_table(tables::POA_SIGNAL_HEADS_V1)?;
            let transitions = write.open_table(tables::POA_SIGNAL_TRANSITIONS_V1)?;
            let by_ordinal = write.open_table(tables::POA_SIGNAL_BY_COMMIT_ORDINAL_V1)?;
            validate_tables(&heads, &transitions, &by_ordinal)?;

            if heads.len()? != 0 {
                let exact = heads.len()? == 1
                    && transitions.len()? == 0
                    && by_ordinal.len()? == 0
                    && heads
                        .get(&head.authority_id)?
                        .is_some_and(|stored| stored.value() == encoded.as_slice());
                return if exact {
                    Ok(PoaSignalGenesisInitOutcome::AlreadyIdentical)
                } else {
                    Err(integrity(
                        "PoA Signal store already has a different authority head or history",
                    ))
                };
            }
        }
        if cursor != 0 {
            return Err(integrity(
                "PoA Signal authority may only initialize before the first finalized commit",
            ));
        }
        {
            let mut heads = write.open_table(tables::POA_SIGNAL_HEADS_V1)?;
            heads.insert(&head.authority_id, encoded.as_slice())?;
        }
        write.commit()?;
        Ok(PoaSignalGenesisInitOutcome::Installed)
    }

    /// Install one authenticated zero-transition authority head.  Installation
    /// is absence-only and is refused once any finalized commit exists, avoiding
    /// retrospective reinterpretation of old ordinary event turns.
    pub fn initialize_poa_signal_head(&self, head: &PoaSignalHeadV1) -> Result<()> {
        if head.transition_count != 0 {
            return Err(integrity(
                "PoA Signal initialization requires a genesis head",
            ));
        }
        let encoded = head.encode()?;
        let write = self.db.begin_write()?;
        {
            let metadata = write.open_table(tables::METADATA)?;
            let cursor = metadata
                .get(tables::META_COMMIT_CURSOR)?
                .map(|value| value.value())
                .unwrap_or(0);
            if cursor != 0 {
                return Err(integrity(
                    "PoA Signal authority may only initialize before the first finalized commit",
                ));
            }
        }
        {
            let heads = write.open_table(tables::POA_SIGNAL_HEADS_V1)?;
            let transitions = write.open_table(tables::POA_SIGNAL_TRANSITIONS_V1)?;
            let by_ordinal = write.open_table(tables::POA_SIGNAL_BY_COMMIT_ORDINAL_V1)?;
            validate_tables(&heads, &transitions, &by_ordinal)?;
        }
        {
            let mut heads = write.open_table(tables::POA_SIGNAL_HEADS_V1)?;
            if heads.get(&head.authority_id)?.is_some() {
                return Err(integrity("PoA Signal authority is already initialized"));
            }
            heads.insert(&head.authority_id, encoded.as_slice())?;
        }
        write.commit()?;
        Ok(())
    }

    /// Load and validate the current head for one authority.
    pub fn load_poa_signal_head(&self, authority_id: [u8; 32]) -> Result<Option<PoaSignalHeadV1>> {
        let read = self.db.begin_read()?;
        let heads = read.open_table(tables::POA_SIGNAL_HEADS_V1)?;
        let Some(bytes) = heads.get(&authority_id)? else {
            return Ok(None);
        };
        let head = PoaSignalHeadV1::decode(bytes.value())?;
        if head.authority_id != authority_id {
            return Err(integrity("PoA Signal head key/authority mismatch"));
        }
        Ok(Some(head))
    }

    /// Load the globally singular PoA authority, regardless of the currently
    /// configured runtime federation. Boot uses this to ensure an authority
    /// cannot become invisible merely because genesis now derives another id.
    pub fn load_singular_poa_signal_head(&self) -> Result<Option<PoaSignalHeadV1>> {
        self.audit_poa_signal_state()?;
        let read = self.db.begin_read()?;
        let heads = read.open_table(tables::POA_SIGNAL_HEADS_V1)?;
        if heads.len()? > 1 {
            return Err(integrity("PoA Signal store has multiple authority heads"));
        }
        let Some(entry) = heads.iter()?.next() else {
            return Ok(None);
        };
        let (key, value) = entry?;
        let head = PoaSignalHeadV1::decode(value.value())?;
        if head.authority_id != *key.value() {
            return Err(integrity("PoA Signal head key/authority mismatch"));
        }
        Ok(Some(head))
    }

    /// Load one immutable transition by authority and one-based sequence.
    pub fn load_poa_signal_transition(
        &self,
        authority_id: [u8; 32],
        sequence: u64,
    ) -> Result<Option<PoaSignalTransitionV1>> {
        let key = transition_key(authority_id, sequence);
        let read = self.db.begin_read()?;
        let transitions = read.open_table(tables::POA_SIGNAL_TRANSITIONS_V1)?;
        let Some(bytes) = transitions.get(&key)? else {
            return Ok(None);
        };
        let transition = PoaSignalTransitionV1::decode(bytes.value())?;
        if transition.key() != key {
            return Err(integrity("PoA Signal transition key/wire mismatch"));
        }
        Ok(Some(transition))
    }

    /// Full structural audit of all PoA Signal heads, transition chains, and
    /// commit-ordinal reverse-index rows, including the exact generic commit
    /// carrier named by every transition.
    pub fn audit_poa_signal_state(&self) -> Result<()> {
        let read = self.db.begin_read()?;
        let heads = read.open_table(tables::POA_SIGNAL_HEADS_V1)?;
        let transitions = read.open_table(tables::POA_SIGNAL_TRANSITIONS_V1)?;
        let by_ordinal = read.open_table(tables::POA_SIGNAL_BY_COMMIT_ORDINAL_V1)?;
        validate_tables(&heads, &transitions, &by_ordinal)?;
        let commits = read.open_table(tables::COMMIT_LOG)?;
        validate_generic_commit_carriers(&transitions, &commits)
    }

    /// Capture one complete, structurally audited Signal history under one read
    /// transaction. This deliberately performs no game evaluation; the node's
    /// native-Lean semantic audit consumes the returned immutable snapshot.
    pub fn load_poa_signal_history(
        &self,
        authority_id: [u8; 32],
    ) -> Result<Option<PoaSignalHistoryV1>> {
        let read = self.db.begin_read()?;
        let heads = read.open_table(tables::POA_SIGNAL_HEADS_V1)?;
        let transitions = read.open_table(tables::POA_SIGNAL_TRANSITIONS_V1)?;
        let by_ordinal = read.open_table(tables::POA_SIGNAL_BY_COMMIT_ORDINAL_V1)?;
        validate_tables(&heads, &transitions, &by_ordinal)?;
        let commits = read.open_table(tables::COMMIT_LOG)?;
        validate_generic_commit_carriers(&transitions, &commits)?;

        let Some(current_bytes) = heads.get(&authority_id)? else {
            return Ok(None);
        };
        let current = PoaSignalHeadV1::decode(current_bytes.value())?;
        if current.authority_id != authority_id {
            return Err(integrity("PoA Signal history head key/authority mismatch"));
        }

        let capacity = usize::try_from(current.transition_count)
            .map_err(|_| integrity("PoA Signal history length exceeds usize"))?;
        let mut ordered = Vec::with_capacity(capacity);
        for sequence in 1..=current.transition_count {
            let key = transition_key(authority_id, sequence);
            let bytes = transitions
                .get(&key)?
                .ok_or_else(|| integrity("PoA Signal history has a sequence gap"))?;
            let transition = PoaSignalTransitionV1::decode(bytes.value())?;
            if transition.key() != key {
                return Err(integrity("PoA Signal history key/wire mismatch"));
            }
            ordered.push(transition);
        }
        let genesis = match ordered.first() {
            Some(first) => first.predecessor_head()?,
            None => current.clone(),
        };
        if genesis.transition_count != 0 {
            return Err(integrity(
                "PoA Signal semantic history does not start at genesis",
            ));
        }
        Ok(Some(PoaSignalHistoryV1 {
            genesis,
            current,
            transitions: ordered,
        }))
    }
}

pub(crate) fn stage_fresh_poa_signal_transition_in(
    write: &WriteTransaction,
    commit_ordinal: u64,
    record: &CommitRecord,
    candidate: &PreparedPoaSignalTransitionV1,
) -> Result<()> {
    if record.ordinal != commit_ordinal {
        return Err(integrity("PoA Signal carrying commit ordinal mismatch"));
    }
    {
        let by_ordinal = write.open_table(tables::POA_SIGNAL_BY_COMMIT_ORDINAL_V1)?;
        if by_ordinal.get(commit_ordinal)?.is_some() {
            return Err(integrity(
                "fresh PoA Signal commit ordinal already has a transition",
            ));
        }
    }
    let predecessor_bytes = {
        let heads = write.open_table(tables::POA_SIGNAL_HEADS_V1)?;
        heads
            .get(&candidate.authority_id)?
            .ok_or_else(|| integrity("PoA Signal authority is not initialized"))?
            .value()
            .to_vec()
    };
    let predecessor = PoaSignalHeadV1::decode(&predecessor_bytes)?;
    if predecessor.digest() != candidate.expected_predecessor_head_digest {
        return Err(integrity("PoA Signal predecessor CAS mismatch"));
    }
    let transition = plan_transition(
        predecessor_bytes,
        predecessor,
        commit_ordinal,
        record,
        candidate,
    )?;
    let key = transition.key();
    let transition_bytes = transition.encode()?;
    {
        let transitions = write.open_table(tables::POA_SIGNAL_TRANSITIONS_V1)?;
        if transitions.get(&key)?.is_some() {
            return Err(integrity("PoA Signal transition sequence already exists"));
        }
    }
    {
        let mut transitions = write.open_table(tables::POA_SIGNAL_TRANSITIONS_V1)?;
        transitions.insert(&key, transition_bytes.as_slice())?;
        let mut by_ordinal = write.open_table(tables::POA_SIGNAL_BY_COMMIT_ORDINAL_V1)?;
        by_ordinal.insert(commit_ordinal, &key)?;
        let mut heads = write.open_table(tables::POA_SIGNAL_HEADS_V1)?;
        heads.insert(
            &candidate.authority_id,
            transition.successor_head.as_slice(),
        )?;
    }
    Ok(())
}

pub(crate) fn verify_replayed_poa_signal_transition_in(
    write: &WriteTransaction,
    commit_ordinal: u64,
    record: &CommitRecord,
    candidate: Option<&PreparedPoaSignalTransitionV1>,
) -> Result<()> {
    let indexed = {
        let by_ordinal = write.open_table(tables::POA_SIGNAL_BY_COMMIT_ORDINAL_V1)?;
        by_ordinal.get(commit_ordinal)?.map(|value| *value.value())
    };
    let (Some(candidate), Some(key)) = (candidate, indexed) else {
        return match (candidate.is_some(), indexed.is_some()) {
            (false, false) => Ok(()),
            _ => Err(integrity(
                "replayed finalized turn omitted or invented its PoA Signal weld",
            )),
        };
    };
    let stored_bytes = {
        let transitions = write.open_table(tables::POA_SIGNAL_TRANSITIONS_V1)?;
        transitions
            .get(&key)?
            .ok_or_else(|| integrity("PoA Signal ordinal index points to no transition"))?
            .value()
            .to_vec()
    };
    let stored = PoaSignalTransitionV1::decode(&stored_bytes)?;
    if stored.key() != key
        || stored.commit_ordinal != commit_ordinal
        || stored.turn_hash != record.turn_hash
        || stored.receipt_hash != record.receipt_hash
        || stored.authority_id != candidate.authority_id
    {
        return Err(integrity(
            "replayed PoA Signal transition disagrees with carrying commit coordinates",
        ));
    }
    let predecessor = PoaSignalHeadV1::decode(&stored.predecessor_head)?;
    let expected = plan_transition(
        stored.predecessor_head.clone(),
        predecessor,
        commit_ordinal,
        record,
        candidate,
    )?;
    if expected.encode()? != stored_bytes {
        return Err(integrity(
            "replayed PoA Signal transition is not byte-identical",
        ));
    }
    Ok(())
}

/// Rewind PoA Signal authority to the same last-good generic commit cursor.
/// Called inside the generic tail-recovery writer before the lower cursor is
/// published.
pub(crate) fn truncate_poa_signal_state_in(
    write: &WriteTransaction,
    new_cursor: u64,
) -> Result<u64> {
    {
        let heads = write.open_table(tables::POA_SIGNAL_HEADS_V1)?;
        let transitions = write.open_table(tables::POA_SIGNAL_TRANSITIONS_V1)?;
        let by_ordinal = write.open_table(tables::POA_SIGNAL_BY_COMMIT_ORDINAL_V1)?;
        validate_tables(&heads, &transitions, &by_ordinal)?;
    }
    let doomed: Vec<(u64, [u8; 40], PoaSignalTransitionV1)> = {
        let by_ordinal = write.open_table(tables::POA_SIGNAL_BY_COMMIT_ORDINAL_V1)?;
        let transitions = write.open_table(tables::POA_SIGNAL_TRANSITIONS_V1)?;
        let mut rows = Vec::new();
        for entry in by_ordinal.range(new_cursor..)? {
            let (ordinal, key) = entry?;
            let ordinal = ordinal.value();
            let key = *key.value();
            let bytes = transitions
                .get(&key)?
                .ok_or_else(|| integrity("PoA Signal rewind found an orphan ordinal index"))?;
            let transition = PoaSignalTransitionV1::decode(bytes.value())?;
            rows.push((ordinal, key, transition));
        }
        rows
    };
    if doomed.is_empty() {
        return Ok(0);
    }
    let mut rewind_heads: BTreeMap<[u8; 32], (u64, Vec<u8>)> = BTreeMap::new();
    for (_, _, transition) in &doomed {
        rewind_heads
            .entry(transition.authority_id)
            .and_modify(|(sequence, bytes)| {
                if transition.sequence < *sequence {
                    *sequence = transition.sequence;
                    *bytes = transition.predecessor_head.clone();
                }
            })
            .or_insert_with(|| (transition.sequence, transition.predecessor_head.clone()));
    }
    {
        let mut transitions = write.open_table(tables::POA_SIGNAL_TRANSITIONS_V1)?;
        let mut by_ordinal = write.open_table(tables::POA_SIGNAL_BY_COMMIT_ORDINAL_V1)?;
        for (ordinal, key, _) in &doomed {
            transitions.remove(key)?;
            by_ordinal.remove(*ordinal)?;
        }
        let mut heads = write.open_table(tables::POA_SIGNAL_HEADS_V1)?;
        for (authority, (_, head_bytes)) in &rewind_heads {
            heads.insert(authority, head_bytes.as_slice())?;
        }
    }
    {
        let heads = write.open_table(tables::POA_SIGNAL_HEADS_V1)?;
        let transitions = write.open_table(tables::POA_SIGNAL_TRANSITIONS_V1)?;
        let by_ordinal = write.open_table(tables::POA_SIGNAL_BY_COMMIT_ORDINAL_V1)?;
        validate_tables(&heads, &transitions, &by_ordinal)?;
    }
    Ok(doomed.len() as u64)
}

fn plan_transition(
    predecessor_head: Vec<u8>,
    predecessor: PoaSignalHeadV1,
    commit_ordinal: u64,
    record: &CommitRecord,
    candidate: &PreparedPoaSignalTransitionV1,
) -> Result<PoaSignalTransitionV1> {
    if predecessor.authority_id != candidate.authority_id
        || predecessor.digest() != candidate.expected_predecessor_head_digest
    {
        return Err(integrity("PoA Signal predecessor CAS mismatch"));
    }
    let sequence = predecessor
        .transition_count
        .checked_add(1)
        .ok_or_else(|| integrity("PoA Signal transition sequence overflow"))?;
    if predecessor.world_sequence.checked_add(1) != Some(candidate.successor_world_sequence)
        || predecessor.canon_revision.checked_add(1) != Some(candidate.successor_canon_revision)
    {
        return Err(integrity(
            "PoA Signal candidate does not advance world/revision exactly once",
        ));
    }
    let judge_input_digest = sha256(&candidate.judge_input);
    let judge_output_digest = sha256(&candidate.judge_output);
    let mut successor = PoaSignalHeadV1 {
        authority_id: predecessor.authority_id,
        deployment_digest: predecessor.deployment_digest,
        transition_count: sequence,
        world_sequence: candidate.successor_world_sequence,
        canon_revision: candidate.successor_canon_revision,
        last_transition_digest: [0; 32],
        config: predecessor.config.clone(),
        canon: candidate.successor_canon.clone(),
    };
    let transition_digest = transition_core_digest(
        candidate.authority_id,
        sequence,
        commit_ordinal,
        record.turn_hash,
        record.receipt_hash,
        predecessor.digest(),
        &successor,
        judge_input_digest,
        judge_output_digest,
    );
    successor.last_transition_digest = transition_digest;
    successor.validate()?;
    let successor_head = successor.encode()?;
    let transition = PoaSignalTransitionV1 {
        authority_id: candidate.authority_id,
        sequence,
        commit_ordinal,
        turn_hash: record.turn_hash,
        receipt_hash: record.receipt_hash,
        predecessor_head_digest: predecessor.digest(),
        successor_head_digest: successor.digest(),
        transition_digest,
        judge_input_digest,
        judge_output_digest,
        predecessor_head,
        successor_head,
        judge_input: candidate.judge_input.clone(),
        judge_output: candidate.judge_output.clone(),
    };
    transition.validate()?;
    Ok(transition)
}

fn validate_tables(
    heads: &impl ReadableTable<&'static [u8; 32], &'static [u8]>,
    transitions: &impl ReadableTable<&'static [u8; 40], &'static [u8]>,
    by_ordinal: &impl ReadableTable<u64, &'static [u8; 40]>,
) -> Result<()> {
    let mut decoded_heads = BTreeMap::<[u8; 32], (PoaSignalHeadV1, Vec<u8>)>::new();
    for entry in heads.iter()? {
        let (key, value) = entry?;
        let key = *key.value();
        let bytes = value.value().to_vec();
        let head = PoaSignalHeadV1::decode(&bytes)?;
        if head.authority_id != key {
            return Err(integrity("PoA Signal head table key mismatch"));
        }
        decoded_heads.insert(key, (head, bytes));
    }

    if transitions.len()? != by_ordinal.len()? {
        return Err(integrity(
            "PoA Signal transition/commit-index cardinality mismatch",
        ));
    }
    let mut chains = BTreeMap::<[u8; 32], Vec<PoaSignalTransitionV1>>::new();
    let mut seen_ordinals = BTreeSet::new();
    for entry in transitions.iter()? {
        let (key, value) = entry?;
        let key = *key.value();
        let transition = PoaSignalTransitionV1::decode(value.value())?;
        if transition.key() != key {
            return Err(integrity("PoA Signal transition table key mismatch"));
        }
        if !seen_ordinals.insert(transition.commit_ordinal) {
            return Err(integrity(
                "multiple PoA Signal transitions share one generic commit ordinal",
            ));
        }
        if by_ordinal
            .get(transition.commit_ordinal)?
            .map(|stored| *stored.value())
            != Some(key)
        {
            return Err(integrity(
                "PoA Signal transition is absent or wrong in the commit index",
            ));
        }
        chains
            .entry(transition.authority_id)
            .or_default()
            .push(transition);
    }
    for entry in by_ordinal.iter()? {
        let (ordinal, key) = entry?;
        let key = *key.value();
        let Some(value) = transitions.get(&key)? else {
            return Err(integrity("PoA Signal commit index is orphaned"));
        };
        let transition = PoaSignalTransitionV1::decode(value.value())?;
        if transition.commit_ordinal != ordinal.value() {
            return Err(integrity("PoA Signal commit-index ordinal mismatch"));
        }
    }

    for (authority, chain) in &chains {
        let Some((current, current_bytes)) = decoded_heads.get(authority) else {
            return Err(integrity("PoA Signal transitions exist without a head"));
        };
        let mut expected_sequence = 1u64;
        let mut previous_successor: Option<&[u8]> = None;
        for transition in chain {
            if transition.sequence != expected_sequence {
                return Err(integrity("PoA Signal transition sequence has a gap"));
            }
            if let Some(previous) = previous_successor {
                if transition.predecessor_head.as_slice() != previous {
                    return Err(integrity("PoA Signal transition chain is disconnected"));
                }
            } else {
                let genesis = PoaSignalHeadV1::decode(&transition.predecessor_head)?;
                if genesis.transition_count != 0 {
                    return Err(integrity(
                        "PoA Signal transition chain does not begin at genesis",
                    ));
                }
            }
            previous_successor = Some(&transition.successor_head);
            expected_sequence = expected_sequence
                .checked_add(1)
                .ok_or_else(|| integrity("PoA Signal audit sequence overflow"))?;
        }
        if previous_successor != Some(current_bytes.as_slice())
            || current.transition_count != chain.len() as u64
        {
            return Err(integrity(
                "PoA Signal current head disagrees with transition-chain tail",
            ));
        }
    }
    for (authority, (head, _)) in &decoded_heads {
        if !chains.contains_key(authority) && head.transition_count != 0 {
            return Err(integrity(
                "PoA Signal non-genesis head has no transition history",
            ));
        }
    }
    Ok(())
}

fn validate_generic_commit_carriers(
    transitions: &impl ReadableTable<&'static [u8; 40], &'static [u8]>,
    commits: &impl ReadableTable<u64, &'static [u8]>,
) -> Result<()> {
    for entry in transitions.iter()? {
        let (_, value) = entry?;
        let transition = PoaSignalTransitionV1::decode(value.value())?;
        let commit_bytes = commits
            .get(transition.commit_ordinal)?
            .ok_or_else(|| integrity("PoA Signal transition has no generic commit carrier"))?;
        let commit = crate::commit_log::decode_commit_record(commit_bytes.value())?;
        if commit.ordinal != transition.commit_ordinal
            || commit.turn_hash != transition.turn_hash
            || commit.receipt_hash != transition.receipt_hash
        {
            return Err(integrity(
                "PoA Signal transition disagrees with its generic commit carrier",
            ));
        }
    }
    Ok(())
}

fn transition_core_digest(
    authority_id: [u8; 32],
    sequence: u64,
    commit_ordinal: u64,
    turn_hash: [u8; 32],
    receipt_hash: [u8; 32],
    predecessor_head_digest: [u8; 32],
    successor: &PoaSignalHeadV1,
    judge_input_digest: [u8; 32],
    judge_output_digest: [u8; 32],
) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("dregg-poa-signal-transition-core-v1");
    hasher.update(&authority_id);
    hasher.update(&sequence.to_le_bytes());
    hasher.update(&commit_ordinal.to_le_bytes());
    hasher.update(&turn_hash);
    hasher.update(&receipt_hash);
    hasher.update(&predecessor_head_digest);
    hasher.update(&successor.world_sequence.to_le_bytes());
    hasher.update(&successor.canon_revision.to_le_bytes());
    hasher.update(&sha256(&successor.config));
    hasher.update(&sha256(&successor.canon));
    hasher.update(&judge_input_digest);
    hasher.update(&judge_output_digest);
    *hasher.finalize().as_bytes()
}

fn transition_key(authority_id: [u8; 32], sequence: u64) -> [u8; 40] {
    let mut key = [0u8; 40];
    key[..32].copy_from_slice(&authority_id);
    key[32..].copy_from_slice(&sequence.to_be_bytes());
    key
}

fn head_seal(bytes: &[u8]) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("dregg-poa-signal-head-wire-v1");
    hasher.update(bytes);
    *hasher.finalize().as_bytes()
}

fn transition_seal(bytes: &[u8]) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("dregg-poa-signal-transition-wire-v1");
    hasher.update(bytes);
    *hasher.finalize().as_bytes()
}

fn sha256(bytes: &[u8]) -> [u8; 32] {
    Sha256::digest(bytes).into()
}

fn checked_combined_len(left: &[u8], right: &[u8], what: &str) -> Result<()> {
    let len = left
        .len()
        .checked_add(right.len())
        .ok_or_else(|| integrity(format!("{what} length overflow")))?;
    if len > MAX_POA_SIGNAL_WIRE_BYTES_V1 {
        return Err(integrity(format!(
            "{what} exceeds {MAX_POA_SIGNAL_WIRE_BYTES_V1} bytes"
        )));
    }
    Ok(())
}

fn encoded_len(len: usize, what: &str) -> Result<u32> {
    u32::try_from(len).map_err(|_| integrity(format!("{what} length exceeds u32")))
}

fn array_at<const N: usize>(bytes: &[u8], offset: usize) -> Result<[u8; N]> {
    bytes
        .get(offset..offset + N)
        .ok_or_else(|| integrity("PoA Signal wire field is truncated"))?
        .try_into()
        .map_err(|_| integrity("PoA Signal wire field has wrong length"))
}

fn u64_at(bytes: &[u8], offset: usize) -> Result<u64> {
    Ok(u64::from_le_bytes(array_at::<8>(bytes, offset)?))
}

fn u32_at(bytes: &[u8], offset: usize) -> Result<u32> {
    Ok(u32::from_le_bytes(array_at::<4>(bytes, offset)?))
}

fn take_vec(bytes: &[u8], cursor: &mut usize, len: usize) -> Result<Vec<u8>> {
    let end = cursor
        .checked_add(len)
        .ok_or_else(|| integrity("PoA Signal payload length overflow"))?;
    let out = bytes
        .get(*cursor..end)
        .ok_or_else(|| integrity("PoA Signal payload is truncated"))?
        .to_vec();
    *cursor = end;
    Ok(out)
}

fn integrity(message: impl Into<String>) -> StoreError {
    StoreError::Integrity(message.into())
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_cell::Ledger;

    const AUTHORITY: [u8; 32] = [0x41; 32];

    fn genesis() -> PoaSignalHeadV1 {
        PoaSignalHeadV1::genesis(
            AUTHORITY,
            [0xd1; 32],
            7,
            11,
            br#"{"config":"lean-emitted"}"#.to_vec(),
            br#"{"canon":"genesis"}"#.to_vec(),
        )
        .unwrap()
    }

    fn record(ordinal: u64, ledger_root: [u8; 32]) -> CommitRecord {
        let tag = u8::try_from(ordinal + 1).unwrap();
        CommitRecord {
            ordinal,
            height: ordinal + 1,
            block_id: [tag; 32],
            block_executed_up_to: ordinal + 1,
            turn_hash: [tag.wrapping_add(0x20); 32],
            creator: [tag.wrapping_add(0x40); 32],
            receipt_hash: [tag.wrapping_add(0x60); 32],
            ledger_root,
            touched_cells: Vec::new(),
            removed: Vec::new(),
        }
    }

    fn candidate(store: &PersistentStore, tag: u8) -> PreparedPoaSignalTransitionV1 {
        let head = store.load_poa_signal_head(AUTHORITY).unwrap().unwrap();
        PreparedPoaSignalTransitionV1::new(
            AUTHORITY,
            head.digest(),
            head.world_sequence() + 1,
            head.canon_revision() + 1,
            format!(r#"{{"canon":"successor-{tag}"}}"#).into_bytes(),
            format!(r#"{{"judgeInput":{tag}}}"#).into_bytes(),
            format!(r#"{{"judgeOutput":{tag}}}"#).into_bytes(),
        )
        .unwrap()
    }

    fn initialized_store() -> PersistentStore {
        let store = PersistentStore::open_in_memory().unwrap();
        store.initialize_poa_signal_head(&genesis()).unwrap();
        store
    }

    #[test]
    fn lean_accepted_projection_must_match_authority_coordinates_and_canon() {
        let input = include_bytes!("../../dregg-lean-ffi/tests/fixtures/poa-signal-input-v1.json");
        let output =
            include_bytes!("../../dregg-lean-ffi/tests/fixtures/poa-signal-output-v1.json");
        let input_json: serde_json::Value = serde_json::from_slice(input).unwrap();
        let output_json: serde_json::Value = serde_json::from_slice(output).unwrap();
        let authority =
            dregg_types::parse_hex32(input_json["carrier"]["federation_id"].as_str().unwrap())
                .unwrap();
        let sequence = output_json["successor_world"]["sequence"].as_u64().unwrap();
        let revision = output_json["successor_canon"]["revision"].as_u64().unwrap();
        let canon = serde_json::to_vec(&output_json["successor_canon"]).unwrap();

        validate_accepted_projection(authority, sequence, revision, &canon, input, output).unwrap();
        assert!(
            validate_accepted_projection([0xff; 32], sequence, revision, &canon, input, output,)
                .is_err()
        );
        assert!(
            validate_accepted_projection(authority, sequence + 1, revision, &canon, input, output,)
                .is_err()
        );
        let mut wrong_canon: serde_json::Value = serde_json::from_slice(&canon).unwrap();
        wrong_canon["curator_counter"] = serde_json::json!(revision + 10);
        assert!(
            validate_accepted_projection(
                authority,
                sequence,
                revision,
                &serde_json::to_vec(&wrong_canon).unwrap(),
                input,
                output,
            )
            .is_err()
        );
    }

    #[test]
    fn poa_signal_operator_genesis_is_globally_empty_or_exactly_idempotent() {
        let store = PersistentStore::open_in_memory().unwrap();
        let head = genesis();
        assert_eq!(
            store
                .initialize_poa_signal_head_if_empty_or_identical(&head)
                .unwrap(),
            PoaSignalGenesisInitOutcome::Installed
        );
        assert_eq!(
            store
                .initialize_poa_signal_head_if_empty_or_identical(&head)
                .unwrap(),
            PoaSignalGenesisInitOutcome::AlreadyIdentical
        );

        // An exact retry is still a no-op after generic history begins.
        store
            .commit_finalized_turn(0, &record(0, [0x81; 32]))
            .unwrap();
        assert_eq!(
            store
                .initialize_poa_signal_head_if_empty_or_identical(&head)
                .unwrap(),
            PoaSignalGenesisInitOutcome::AlreadyIdentical
        );

        let disagreement = PoaSignalHeadV1::genesis(
            AUTHORITY,
            [0xe2; 32],
            head.world_sequence(),
            head.canon_revision(),
            head.config().to_vec(),
            head.canon().to_vec(),
        )
        .unwrap();
        assert!(
            store
                .initialize_poa_signal_head_if_empty_or_identical(&disagreement)
                .is_err()
        );
        assert_eq!(store.load_poa_signal_head(AUTHORITY).unwrap(), Some(head));
    }

    #[test]
    fn poa_signal_operator_genesis_refuses_a_nonempty_generic_store() {
        let store = PersistentStore::open_in_memory().unwrap();
        store
            .commit_finalized_turn(0, &record(0, [0x82; 32]))
            .unwrap();
        assert!(
            store
                .initialize_poa_signal_head_if_empty_or_identical(&genesis())
                .is_err()
        );
        assert_eq!(store.load_poa_signal_head(AUTHORITY).unwrap(), None);
    }

    #[test]
    fn poa_signal_operator_genesis_refuses_a_second_authority() {
        let store = PersistentStore::open_in_memory().unwrap();
        store.initialize_poa_signal_head(&genesis()).unwrap();
        let other = PoaSignalHeadV1::genesis(
            [0x42; 32],
            [0xd2; 32],
            0,
            0,
            br#"{"config":"other"}"#.to_vec(),
            br#"{"canon":"other"}"#.to_vec(),
        )
        .unwrap();
        assert!(
            store
                .initialize_poa_signal_head_if_empty_or_identical(&other)
                .is_err()
        );
        assert_eq!(store.load_poa_signal_head([0x42; 32]).unwrap(), None);
    }

    #[test]
    fn poa_signal_fresh_weld_advances_head_and_commit_atomically() {
        let store = initialized_store();
        let before = store.load_poa_signal_head(AUTHORITY).unwrap().unwrap();
        let candidate = candidate(&store, 1);
        let record = record(0, [0x91; 32]);

        let outcome = store
            .commit_finalized_turn_with_poa_signal(0, &record, &candidate)
            .unwrap();
        assert!(outcome.freshly_committed);
        assert_eq!(outcome.ordinal, 0);
        assert_eq!(store.commit_cursor().unwrap(), 1);
        assert_eq!(
            store.commit_record_at(0).unwrap().unwrap().turn_hash,
            record.turn_hash
        );

        let after = store.load_poa_signal_head(AUTHORITY).unwrap().unwrap();
        assert_eq!(after.transition_count(), 1);
        assert_eq!(after.world_sequence(), before.world_sequence() + 1);
        assert_eq!(after.canon_revision(), before.canon_revision() + 1);
        let transition = store
            .load_poa_signal_transition(AUTHORITY, 1)
            .unwrap()
            .unwrap();
        assert_eq!(transition.commit_ordinal(), 0);
        assert_eq!(transition.turn_hash(), record.turn_hash);
        assert_eq!(transition.receipt_hash(), record.receipt_hash);
        assert_eq!(transition.predecessor_head_digest(), before.digest());
        assert_eq!(transition.successor_head_digest(), after.digest());
        assert_eq!(
            transition.judge_input_digest(),
            candidate.judge_input_digest()
        );
        assert_eq!(
            transition.judge_output_digest(),
            candidate.judge_output_digest()
        );
        store.audit_poa_signal_state().unwrap();
    }

    #[test]
    fn poa_signal_restart_audit_requires_exact_generic_commit_carrier() {
        let missing = initialized_store();
        let missing_candidate = candidate(&missing, 1);
        missing
            .commit_finalized_turn_with_poa_signal(0, &record(0, [0xa1; 32]), &missing_candidate)
            .unwrap();
        let write = missing.db.begin_write().unwrap();
        {
            let mut commits = write.open_table(tables::COMMIT_LOG).unwrap();
            commits.remove(0).unwrap();
        }
        write.commit().unwrap();
        let error = missing.audit_poa_signal_state().unwrap_err().to_string();
        assert!(error.contains("no generic commit carrier"), "{error}");

        let different = initialized_store();
        let different_candidate = candidate(&different, 2);
        let original = record(0, [0xa2; 32]);
        different
            .commit_finalized_turn_with_poa_signal(0, &original, &different_candidate)
            .unwrap();
        let mut substituted = original;
        substituted.turn_hash = [0xfe; 32];
        substituted.receipt_hash = [0xfd; 32];
        let encoded = postcard::to_stdvec(&substituted).unwrap();
        let write = different.db.begin_write().unwrap();
        {
            let mut commits = write.open_table(tables::COMMIT_LOG).unwrap();
            commits.insert(0, encoded.as_slice()).unwrap();
        }
        write.commit().unwrap();
        let error = different.audit_poa_signal_state().unwrap_err().to_string();
        assert!(
            error.contains("disagrees with its generic commit carrier"),
            "{error}"
        );
    }

    #[test]
    fn poa_signal_exact_replay_is_noop_and_conflict_refuses() {
        let store = initialized_store();
        let candidate = candidate(&store, 1);
        let record = record(0, [0x92; 32]);
        store
            .commit_finalized_turn_with_poa_signal(0, &record, &candidate)
            .unwrap();
        let head = store.load_poa_signal_head(AUTHORITY).unwrap().unwrap();

        let replay = store
            .commit_finalized_turn_with_poa_signal(0, &record, &candidate)
            .unwrap();
        assert!(!replay.freshly_committed);
        assert_eq!(
            store.load_poa_signal_head(AUTHORITY).unwrap().unwrap(),
            head
        );

        let conflicting = PreparedPoaSignalTransitionV1::new(
            AUTHORITY,
            candidate.expected_predecessor_head_digest(),
            8,
            12,
            br#"{"canon":"different"}"#.to_vec(),
            br#"{"judgeInput":1}"#.to_vec(),
            br#"{"judgeOutput":999}"#.to_vec(),
        )
        .unwrap();
        assert!(
            store
                .commit_finalized_turn_with_poa_signal(0, &record, &conflicting)
                .is_err()
        );
        assert_eq!(
            store.load_poa_signal_head(AUTHORITY).unwrap().unwrap(),
            head
        );
    }

    #[test]
    fn poa_signal_omitted_or_invented_replay_refuses() {
        let with_signal = initialized_store();
        let signal = candidate(&with_signal, 1);
        let signal_record = record(0, [0x93; 32]);
        with_signal
            .commit_finalized_turn_with_poa_signal(0, &signal_record, &signal)
            .unwrap();
        assert!(
            with_signal
                .commit_finalized_turn(0, &signal_record)
                .is_err()
        );

        let without_signal = initialized_store();
        let plain_record = record(0, [0x94; 32]);
        without_signal
            .commit_finalized_turn(0, &plain_record)
            .unwrap();
        let invented = candidate(&without_signal, 2);
        assert!(
            without_signal
                .commit_finalized_turn_with_poa_signal(0, &plain_record, &invented)
                .is_err()
        );
        assert_eq!(
            without_signal
                .load_poa_signal_head(AUTHORITY)
                .unwrap()
                .unwrap()
                .transition_count(),
            0
        );
    }

    #[test]
    fn poa_signal_wrong_predecessor_refuses_without_mutation() {
        let store = initialized_store();
        let before = store.load_poa_signal_head(AUTHORITY).unwrap().unwrap();
        let bad = PreparedPoaSignalTransitionV1::new(
            AUTHORITY,
            [0xee; 32],
            before.world_sequence() + 1,
            before.canon_revision() + 1,
            br#"{"canon":"bad-cas"}"#.to_vec(),
            br#"{"judgeInput":1}"#.to_vec(),
            br#"{"judgeOutput":1}"#.to_vec(),
        )
        .unwrap();
        assert!(
            store
                .commit_finalized_turn_with_poa_signal(0, &record(0, [0x95; 32]), &bad)
                .is_err()
        );
        assert_eq!(store.commit_cursor().unwrap(), 0);
        assert!(store.commit_record_at(0).unwrap().is_none());
        assert!(
            store
                .load_poa_signal_transition(AUTHORITY, 1)
                .unwrap()
                .is_none()
        );
        assert_eq!(
            store.load_poa_signal_head(AUTHORITY).unwrap().unwrap(),
            before
        );
    }

    #[test]
    fn poa_signal_tail_truncation_rewinds_head_to_last_survivor() {
        let store = initialized_store();
        let empty_root = crate::canonical_ledger_root(&Ledger::new());
        let first = candidate(&store, 1);
        store
            .commit_finalized_turn_with_poa_signal(0, &record(0, empty_root), &first)
            .unwrap();
        let surviving_head = store.load_poa_signal_head(AUTHORITY).unwrap().unwrap();

        let second = candidate(&store, 2);
        store
            .commit_finalized_turn_with_poa_signal(1, &record(1, [0xff; 32]), &second)
            .unwrap();
        assert_eq!(store.commit_cursor().unwrap(), 2);

        assert_eq!(store.recover_to_last_consistent().unwrap(), 1);
        assert_eq!(store.commit_cursor().unwrap(), 1);
        assert_eq!(
            store.load_poa_signal_head(AUTHORITY).unwrap().unwrap(),
            surviving_head
        );
        assert!(
            store
                .load_poa_signal_transition(AUTHORITY, 2)
                .unwrap()
                .is_none()
        );
        assert!(store.commit_record_at(1).unwrap().is_none());
        store.audit_poa_signal_state().unwrap();
    }

    #[test]
    fn poa_signal_gap_reorder_extra_and_orphan_audit_refuses() {
        let gap_store = initialized_store();
        let first = candidate(&gap_store, 1);
        gap_store
            .commit_finalized_turn_with_poa_signal(0, &record(0, [1; 32]), &first)
            .unwrap();
        let second = candidate(&gap_store, 2);
        gap_store
            .commit_finalized_turn_with_poa_signal(1, &record(1, [2; 32]), &second)
            .unwrap();
        let write = gap_store.db.begin_write().unwrap();
        {
            let mut transitions = write.open_table(tables::POA_SIGNAL_TRANSITIONS_V1).unwrap();
            transitions.remove(&transition_key(AUTHORITY, 1)).unwrap();
            let mut by_ordinal = write
                .open_table(tables::POA_SIGNAL_BY_COMMIT_ORDINAL_V1)
                .unwrap();
            by_ordinal.remove(0).unwrap();
        }
        write.commit().unwrap();
        assert!(gap_store.audit_poa_signal_state().is_err());
        assert!(gap_store.load_poa_signal_history(AUTHORITY).is_err());

        let reordered_store = initialized_store();
        let first = candidate(&reordered_store, 3);
        reordered_store
            .commit_finalized_turn_with_poa_signal(0, &record(0, [4; 32]), &first)
            .unwrap();
        let second = candidate(&reordered_store, 4);
        reordered_store
            .commit_finalized_turn_with_poa_signal(1, &record(1, [5; 32]), &second)
            .unwrap();
        let write = reordered_store.db.begin_write().unwrap();
        {
            let mut transitions = write.open_table(tables::POA_SIGNAL_TRANSITIONS_V1).unwrap();
            let first_key = transition_key(AUTHORITY, 1);
            let second_key = transition_key(AUTHORITY, 2);
            let first_bytes = transitions
                .get(&first_key)
                .unwrap()
                .unwrap()
                .value()
                .to_vec();
            let second_bytes = transitions
                .get(&second_key)
                .unwrap()
                .unwrap()
                .value()
                .to_vec();
            transitions
                .insert(&first_key, second_bytes.as_slice())
                .unwrap();
            transitions
                .insert(&second_key, first_bytes.as_slice())
                .unwrap();
        }
        write.commit().unwrap();
        assert!(reordered_store.audit_poa_signal_state().is_err());
        assert!(reordered_store.load_poa_signal_history(AUTHORITY).is_err());

        let extra_store = initialized_store();
        let first = candidate(&extra_store, 5);
        extra_store
            .commit_finalized_turn_with_poa_signal(0, &record(0, [6; 32]), &first)
            .unwrap();
        let published_first = extra_store
            .load_poa_signal_head(AUTHORITY)
            .unwrap()
            .unwrap();
        let second = candidate(&extra_store, 6);
        extra_store
            .commit_finalized_turn_with_poa_signal(1, &record(1, [7; 32]), &second)
            .unwrap();
        let published_first_bytes = published_first.encode().unwrap();
        let write = extra_store.db.begin_write().unwrap();
        {
            let mut heads = write.open_table(tables::POA_SIGNAL_HEADS_V1).unwrap();
            heads
                .insert(&AUTHORITY, published_first_bytes.as_slice())
                .unwrap();
        }
        write.commit().unwrap();
        assert!(extra_store.audit_poa_signal_state().is_err());
        assert!(extra_store.load_poa_signal_history(AUTHORITY).is_err());

        let orphan_store = initialized_store();
        let transition = candidate(&orphan_store, 1);
        orphan_store
            .commit_finalized_turn_with_poa_signal(0, &record(0, [3; 32]), &transition)
            .unwrap();
        let write = orphan_store.db.begin_write().unwrap();
        {
            let mut by_ordinal = write
                .open_table(tables::POA_SIGNAL_BY_COMMIT_ORDINAL_V1)
                .unwrap();
            by_ordinal.remove(0).unwrap();
        }
        write.commit().unwrap();
        assert!(orphan_store.audit_poa_signal_state().is_err());
        assert!(orphan_store.load_poa_signal_history(AUTHORITY).is_err());
    }
}
