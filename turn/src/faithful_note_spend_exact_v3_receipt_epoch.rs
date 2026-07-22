//! Explicit, additive receipt-chain epoch for the exact FNSP-v3 accumulator.
//!
//! The deployed [`TurnReceipt`] v4 state commitment contains the legacy
//! sorted-dense `FNL8/FNN8` nullifier root.  Exact FNSP-v3 instead commits the
//! linked append-order accumulator as `FNS3(root8, count)`.  Those are different
//! state machines even when reconstructed from the same durable append records.
//! This module therefore never places either root in an `Option`, never compares
//! them for equality, and never reinterprets one as the other.
//!
//! The migration is an explicit three-link chain:
//!
//! ```text
//! legacy TurnReceipt hash
//!          |
//!          v
//! ExactFnspV3ReceiptEpochV1 activation hash
//!          |
//!          v
//! first exact frame hash -> later exact frame hash -> ...
//! ```
//!
//! An activation binds both sides of the flag day: the terminal legacy receipt
//! and legacy full-turn outer commitment, plus the independently reconstructed
//! exact accumulator state.  The values are deliberately adjacent but are never
//! asserted equal.
//!
//! Each exact frame then binds two distinct receipts:
//!
//! * the ordinary inner [`TurnReceipt`] continues to carry the complete real
//!   actor transition (nonce, fees, all effects) and keeps its existing raw
//!   receipt-hash/state-continuity chain; and
//! * the exact subreceipt carries proof-local outer BEFORE/AFTER anchors plus
//!   FNS3 before/after.  Those proof-local outer anchors preserve the descriptor's
//!   stable frame and therefore are **not** equal to the real full-turn receipt's
//!   post-state when execution also changes nonce/fees.
//!
//! The outer versioned frame has its own activation/frame-hash chain.  A future
//! executor/quorum signature over the frame-domain message cryptographically
//! joins the exact subreceipt to the real receipt without conflating their state
//! commitments.
//!
//! Frame construction additionally requires an opaque, already-accepted exact
//! FNSP-v3 proof token.  It rechecks the proof-bound roots, counts, FNS3 commits,
//! and outer commitments before minting a non-`Clone` frame.  This is still
//! **non-live substrate**: no executor signs the frame-domain message, no node
//! registers it, and no persistence table treats its hash as final authority.

use core::fmt;
use std::error::Error;

use dregg_circuit::exact_nullifier_aafi::{Digest8, TREE_CAPACITY, exact_state_commit};
use dregg_circuit::field::{BABYBEAR_P, BabyBear};

use crate::{AcceptedFaithfulNoteSpendExactV3, Finality, TurnReceipt};

const ACTIVATION_HASH_DOMAIN: &str = "dregg-exact-fnsp-v3-receipt-epoch-activation-v1";
const FRAME_HASH_DOMAIN: &str = "dregg-exact-fnsp-v3-receipt-state-frame-v1";
const ACCEPTED_STATEMENT_HASH_DOMAIN: &str = "dregg-exact-fnsp-v3-receipt-accepted-statement-v1";
const FRAME_SIGNATURE_DOMAIN: &[u8] = b"executor-exact-fnsp-v3-receipt-frame-v1:";

/// Explicit, nonzero exact-receipt epoch number.
///
/// Epoch zero is reserved for the deployed legacy receipt interpretation.  A
/// caller cannot smuggle legacy mode through an absent/zero optional field.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ExactFnspV3ReceiptEpoch(u64);

impl ExactFnspV3ReceiptEpoch {
    pub fn new(epoch: u64) -> Result<Self, ExactFnspV3ReceiptEpochError> {
        if epoch == 0 {
            return Err(ExactFnspV3ReceiptEpochError::LegacyEpochNumber);
        }
        Ok(Self(epoch))
    }

    pub const fn get(self) -> u64 {
        self.0
    }
}

/// Canonical exact accumulator point.  FNS3 is derived, never caller-supplied.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ExactFnspV3StatePoint {
    root: Digest8,
    count: u64,
    fns3: Digest8,
}

impl ExactFnspV3StatePoint {
    /// Construct from the exact AAFI root and physical leaf count.
    ///
    /// The logical-empty accumulator has the permanent BOT leaf at count one;
    /// count zero is therefore not an exact state.  `TREE_CAPACITY` is the
    /// terminal full-tree count and is representable by the 33-bit circuit
    /// counter, but has no successor append.
    pub fn new(root: Digest8, count: u64) -> Result<Self, ExactFnspV3ReceiptEpochError> {
        if count == 0 || count > TREE_CAPACITY {
            return Err(ExactFnspV3ReceiptEpochError::ExactCountOutOfRange {
                count,
                maximum: TREE_CAPACITY,
            });
        }
        let fns3 = exact_state_commit(root, count);
        Ok(Self { root, count, fns3 })
    }

    fn from_u32(
        root: [u32; 8],
        count: u64,
        claimed_fns3: [u32; 8],
    ) -> Result<Self, ExactFnspV3ReceiptEpochError> {
        let root = canonical_digest("exact root", root)?;
        let point = Self::new(root, count)?;
        let claimed_fns3 = canonical_digest("FNS3", claimed_fns3)?;
        if point.fns3 != claimed_fns3 {
            return Err(ExactFnspV3ReceiptEpochError::Fns3Mismatch);
        }
        Ok(point)
    }

    pub const fn root(self) -> Digest8 {
        self.root
    }

    pub const fn count(self) -> u64 {
        self.count
    }

    pub const fn fns3(self) -> Digest8 {
        self.fns3
    }
}

/// Canonical eight-lane outer rotated-state commitment.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ExactFnspV3OuterCommit(Digest8);

impl ExactFnspV3OuterCommit {
    pub const fn new(lanes: Digest8) -> Self {
        Self(lanes)
    }

    fn from_u32(name: &'static str, lanes: [u32; 8]) -> Result<Self, ExactFnspV3ReceiptEpochError> {
        Ok(Self(canonical_digest(name, lanes)?))
    }

    fn from_bytes(
        name: &'static str,
        bytes: [u8; 32],
    ) -> Result<Self, ExactFnspV3ReceiptEpochError> {
        let mut lanes = [0u32; 8];
        for (index, chunk) in bytes.chunks_exact(4).enumerate() {
            lanes[index] = u32::from_le_bytes(chunk.try_into().expect("four-byte lane"));
        }
        Self::from_u32(name, lanes)
    }

    pub const fn lanes(self) -> Digest8 {
        self.0
    }

    pub fn to_bytes(self) -> [u8; 32] {
        digest_bytes(self.0)
    }
}

/// Explicit flag-day record between the terminal legacy receipt and exact v3.
///
/// Construction is structural, not authority: the caller must separately
/// authenticate/finalize `legacy_tip` and reconstruct `exact_initial` from the
/// complete durable append prefix.  The hash commits both facts so neither can
/// be replaced after the epoch is authorized.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExactFnspV3ReceiptEpochV1 {
    epoch: ExactFnspV3ReceiptEpoch,
    federation_id: [u8; 32],
    agent: dregg_cell::CellId,
    legacy_tip_receipt_hash: [u8; 32],
    legacy_tip_outer_commit: ExactFnspV3OuterCommit,
    exact_initial: ExactFnspV3StatePoint,
    activation_hash: [u8; 32],
}

impl ExactFnspV3ReceiptEpochV1 {
    /// Prepare an explicit legacy-to-exact flag day.
    ///
    /// A tentative legacy receipt cannot become an epoch boundary.  Signature,
    /// quorum, store-prefix equality, and finality-proof verification remain
    /// caller obligations; this module deliberately does not accept raw keys or
    /// claim to perform them.
    pub fn prepare(
        epoch: ExactFnspV3ReceiptEpoch,
        legacy_tip: &TurnReceipt,
        exact_initial: ExactFnspV3StatePoint,
    ) -> Result<Self, ExactFnspV3ReceiptEpochError> {
        if legacy_tip.finality != Finality::Final {
            return Err(ExactFnspV3ReceiptEpochError::LegacyTipNotFinal);
        }
        let legacy_tip_outer_commit = ExactFnspV3OuterCommit::from_bytes(
            "legacy tip outer commitment",
            legacy_tip.post_state_hash,
        )?;
        let mut prepared = Self {
            epoch,
            federation_id: legacy_tip.federation_id,
            agent: legacy_tip.agent,
            legacy_tip_receipt_hash: legacy_tip.receipt_hash(),
            legacy_tip_outer_commit,
            exact_initial,
            activation_hash: [0; 32],
        };
        prepared.activation_hash = prepared.compute_hash();
        Ok(prepared)
    }

    pub const fn epoch(&self) -> ExactFnspV3ReceiptEpoch {
        self.epoch
    }

    pub const fn federation_id(&self) -> [u8; 32] {
        self.federation_id
    }

    pub const fn agent(&self) -> dregg_cell::CellId {
        self.agent
    }

    pub const fn legacy_tip_receipt_hash(&self) -> [u8; 32] {
        self.legacy_tip_receipt_hash
    }

    pub const fn legacy_tip_outer_commit(&self) -> ExactFnspV3OuterCommit {
        self.legacy_tip_outer_commit
    }

    pub const fn exact_initial(&self) -> ExactFnspV3StatePoint {
        self.exact_initial
    }

    pub const fn activation_hash(&self) -> [u8; 32] {
        self.activation_hash
    }

    fn compute_hash(&self) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new_derive_key(ACTIVATION_HASH_DOMAIN);
        hasher.update(&self.epoch.get().to_le_bytes());
        hasher.update(&self.federation_id);
        hasher.update(self.agent.as_bytes());
        hasher.update(&self.legacy_tip_receipt_hash);
        hasher.update(&self.legacy_tip_outer_commit.to_bytes());
        hash_state_point(&mut hasher, self.exact_initial);
        *hasher.finalize().as_bytes()
    }
}

/// Typed predecessor of an exact receipt frame.  There is no absent link.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ExactFnspV3ReceiptLinkV1 {
    EpochActivation([u8; 32]),
    ExactFrame([u8; 32]),
}

impl ExactFnspV3ReceiptLinkV1 {
    pub const fn hash(self) -> [u8; 32] {
        match self {
            Self::EpochActivation(hash) | Self::ExactFrame(hash) => hash,
        }
    }

    const fn tag(self) -> u8 {
        match self {
            Self::EpochActivation(_) => 1,
            Self::ExactFrame(_) => 2,
        }
    }
}

/// Non-`Clone`, proof-bound exact receipt-state frame.
///
/// This token proves only that its coordinates were joined to an opaque exact
/// proof-acceptance token.  It does not prove the receipt was produced from a
/// durable executor snapshot; the future executor-result token must add that
/// fact before node finalization can become live.
#[derive(Debug)]
pub struct PreparedExactFnspV3ReceiptFrameV1 {
    epoch: ExactFnspV3ReceiptEpoch,
    activation_hash: [u8; 32],
    predecessor: ExactFnspV3ReceiptLinkV1,
    receipt: TurnReceipt,
    before: ExactFnspV3StatePoint,
    after: ExactFnspV3StatePoint,
    proof_outer_before: ExactFnspV3OuterCommit,
    proof_outer_after: ExactFnspV3OuterCommit,
    accepted_statement_digest: [u8; 32],
    signed_spending_proof_digest: [u8; 32],
    frame_hash: [u8; 32],
}

impl PreparedExactFnspV3ReceiptFrameV1 {
    /// Prepare the first frame after a cutover activation.
    pub fn begin(
        activation: &ExactFnspV3ReceiptEpochV1,
        receipt: TurnReceipt,
        accepted: &AcceptedFaithfulNoteSpendExactV3,
    ) -> Result<Self, ExactFnspV3ReceiptEpochError> {
        let binding = ExactFrameBinding::from_accepted(accepted)?;
        Self::begin_with_binding(activation, receipt, binding)
    }

    /// Prepare a continuation frame in the same exact epoch.
    pub fn extend(
        previous: &Self,
        receipt: TurnReceipt,
        accepted: &AcceptedFaithfulNoteSpendExactV3,
    ) -> Result<Self, ExactFnspV3ReceiptEpochError> {
        let binding = ExactFrameBinding::from_accepted(accepted)?;
        Self::extend_with_binding(previous, receipt, binding)
    }

    fn begin_with_binding(
        activation: &ExactFnspV3ReceiptEpochV1,
        receipt: TurnReceipt,
        binding: ExactFrameBinding,
    ) -> Result<Self, ExactFnspV3ReceiptEpochError> {
        validate_receipt_scope(
            &receipt,
            activation.federation_id,
            activation.agent,
            activation.legacy_tip_receipt_hash,
        )?;
        if binding.before != activation.exact_initial {
            return Err(ExactFnspV3ReceiptEpochError::CutoverExactStateMismatch);
        }
        Self::finish(
            activation.epoch,
            activation.activation_hash,
            ExactFnspV3ReceiptLinkV1::EpochActivation(activation.activation_hash),
            receipt,
            binding,
        )
    }

    fn extend_with_binding(
        previous: &Self,
        receipt: TurnReceipt,
        binding: ExactFrameBinding,
    ) -> Result<Self, ExactFnspV3ReceiptEpochError> {
        validate_receipt_scope(
            &receipt,
            previous.receipt.federation_id,
            previous.receipt.agent,
            previous.receipt.receipt_hash(),
        )?;
        if binding.before != previous.after {
            return Err(ExactFnspV3ReceiptEpochError::ExactStateChainBreak);
        }
        if receipt.pre_state_hash != previous.receipt.post_state_hash {
            return Err(ExactFnspV3ReceiptEpochError::FullTurnStateChainBreak);
        }
        Self::finish(
            previous.epoch,
            previous.activation_hash,
            ExactFnspV3ReceiptLinkV1::ExactFrame(previous.frame_hash),
            receipt,
            binding,
        )
    }

    fn finish(
        epoch: ExactFnspV3ReceiptEpoch,
        activation_hash: [u8; 32],
        predecessor: ExactFnspV3ReceiptLinkV1,
        receipt: TurnReceipt,
        binding: ExactFrameBinding,
    ) -> Result<Self, ExactFnspV3ReceiptEpochError> {
        if binding.after.count
            != binding
                .before
                .count
                .checked_add(1)
                .ok_or(ExactFnspV3ReceiptEpochError::ExactCountOverflow)?
        {
            return Err(ExactFnspV3ReceiptEpochError::ExactCountStepMismatch {
                before: binding.before.count,
                after: binding.after.count,
            });
        }
        let mut frame = Self {
            epoch,
            activation_hash,
            predecessor,
            receipt,
            before: binding.before,
            after: binding.after,
            proof_outer_before: binding.outer_before,
            proof_outer_after: binding.outer_after,
            accepted_statement_digest: binding.accepted_statement_digest,
            signed_spending_proof_digest: binding.signed_spending_proof_digest,
            frame_hash: [0; 32],
        };
        frame.frame_hash = frame.compute_hash();
        Ok(frame)
    }

    pub const fn epoch(&self) -> ExactFnspV3ReceiptEpoch {
        self.epoch
    }

    pub const fn activation_hash(&self) -> [u8; 32] {
        self.activation_hash
    }

    pub const fn predecessor(&self) -> ExactFnspV3ReceiptLinkV1 {
        self.predecessor
    }

    pub const fn receipt(&self) -> &TurnReceipt {
        &self.receipt
    }

    pub const fn before(&self) -> ExactFnspV3StatePoint {
        self.before
    }

    pub const fn after(&self) -> ExactFnspV3StatePoint {
        self.after
    }

    /// Proof-local rotated BEFORE commitment.  This is not the real receipt's
    /// full actor pre-state commitment and callers must not compare them.
    pub const fn proof_outer_before(&self) -> ExactFnspV3OuterCommit {
        self.proof_outer_before
    }

    /// Proof-local rotated AFTER commitment.  The exact descriptor changes only
    /// FNS3, while real execution may also change nonce/fees/other effects.
    pub const fn proof_outer_after(&self) -> ExactFnspV3OuterCommit {
        self.proof_outer_after
    }

    pub const fn accepted_statement_digest(&self) -> [u8; 32] {
        self.accepted_statement_digest
    }

    pub const fn signed_spending_proof_digest(&self) -> [u8; 32] {
        self.signed_spending_proof_digest
    }

    pub const fn frame_hash(&self) -> [u8; 32] {
        self.frame_hash
    }

    /// Future executor-signature message for this exact versioned frame.
    ///
    /// Today's `TurnReceipt::canonical_executor_signed_message` does not cover
    /// FNS3 or the epoch activation.  A live cut must sign this message (or an
    /// equivalent quorum-certified superset), not merely retain the v4 inner
    /// receipt signature.
    pub fn canonical_executor_signed_message(&self) -> [u8; FRAME_SIGNATURE_DOMAIN.len() + 32] {
        let mut message = [0u8; FRAME_SIGNATURE_DOMAIN.len() + 32];
        message[..FRAME_SIGNATURE_DOMAIN.len()].copy_from_slice(FRAME_SIGNATURE_DOMAIN);
        message[FRAME_SIGNATURE_DOMAIN.len()..].copy_from_slice(&self.frame_hash);
        message
    }

    fn compute_hash(&self) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new_derive_key(FRAME_HASH_DOMAIN);
        hasher.update(&self.epoch.get().to_le_bytes());
        hasher.update(&self.activation_hash);
        hasher.update(&[self.predecessor.tag()]);
        hasher.update(&self.predecessor.hash());
        hasher.update(&self.receipt.receipt_hash());
        hash_state_point(&mut hasher, self.before);
        hash_state_point(&mut hasher, self.after);
        hasher.update(&self.proof_outer_before.to_bytes());
        hasher.update(&self.proof_outer_after.to_bytes());
        hasher.update(&self.accepted_statement_digest);
        hasher.update(&self.signed_spending_proof_digest);
        *hasher.finalize().as_bytes()
    }
}

#[derive(Clone, Copy)]
struct ExactFrameBinding {
    before: ExactFnspV3StatePoint,
    after: ExactFnspV3StatePoint,
    outer_before: ExactFnspV3OuterCommit,
    outer_after: ExactFnspV3OuterCommit,
    accepted_statement_digest: [u8; 32],
    signed_spending_proof_digest: [u8; 32],
}

impl ExactFrameBinding {
    fn from_accepted(
        accepted: &AcceptedFaithfulNoteSpendExactV3,
    ) -> Result<Self, ExactFnspV3ReceiptEpochError> {
        let binding = accepted.binding();
        let mut statement_hasher = blake3::Hasher::new_derive_key(ACCEPTED_STATEMENT_HASH_DOMAIN);
        for lane in accepted.public_input_lanes() {
            statement_hasher.update(&lane.to_le_bytes());
        }
        let signed_spending_proof_digest = accepted.signed_spending_proof_digest();
        statement_hasher.update(&signed_spending_proof_digest);
        Ok(Self {
            before: ExactFnspV3StatePoint::from_u32(
                binding.prior_root(),
                binding.prior_count(),
                binding.prior_fns3(),
            )?,
            after: ExactFnspV3StatePoint::from_u32(
                binding.successor_root(),
                binding.successor_count(),
                binding.successor_fns3(),
            )?,
            outer_before: ExactFnspV3OuterCommit::from_u32(
                "exact outer BEFORE commitment",
                binding.before_outer_commit(),
            )?,
            outer_after: ExactFnspV3OuterCommit::from_u32(
                "exact outer AFTER commitment",
                binding.after_outer_commit(),
            )?,
            accepted_statement_digest: *statement_hasher.finalize().as_bytes(),
            signed_spending_proof_digest,
        })
    }
}

fn validate_receipt_scope(
    receipt: &TurnReceipt,
    federation_id: [u8; 32],
    agent: dregg_cell::CellId,
    inner_predecessor: [u8; 32],
) -> Result<(), ExactFnspV3ReceiptEpochError> {
    if receipt.finality != Finality::Final {
        return Err(ExactFnspV3ReceiptEpochError::ExactReceiptNotFinal);
    }
    if receipt.federation_id != federation_id {
        return Err(ExactFnspV3ReceiptEpochError::FederationMismatch);
    }
    if receipt.agent != agent {
        return Err(ExactFnspV3ReceiptEpochError::AgentMismatch);
    }
    if receipt.previous_receipt_hash != Some(inner_predecessor) {
        return Err(ExactFnspV3ReceiptEpochError::FullTurnPredecessorMismatch);
    }
    Ok(())
}

fn canonical_digest(
    name: &'static str,
    lanes: [u32; 8],
) -> Result<Digest8, ExactFnspV3ReceiptEpochError> {
    let mut digest = [BabyBear::ZERO; 8];
    for (index, value) in lanes.into_iter().enumerate() {
        if value >= BABYBEAR_P {
            return Err(ExactFnspV3ReceiptEpochError::NonCanonicalLane {
                name,
                lane: index,
                value,
            });
        }
        digest[index] = BabyBear::new_canonical(value);
    }
    Ok(digest)
}

fn digest_bytes(digest: Digest8) -> [u8; 32] {
    let mut bytes = [0u8; 32];
    for (index, lane) in digest.into_iter().enumerate() {
        bytes[index * 4..index * 4 + 4].copy_from_slice(&lane.as_u32().to_le_bytes());
    }
    bytes
}

fn hash_state_point(hasher: &mut blake3::Hasher, point: ExactFnspV3StatePoint) {
    hasher.update(&digest_bytes(point.root));
    hasher.update(&point.count.to_le_bytes());
    hasher.update(&digest_bytes(point.fns3));
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExactFnspV3ReceiptEpochError {
    LegacyEpochNumber,
    LegacyTipNotFinal,
    ExactReceiptNotFinal,
    ExactCountOutOfRange {
        count: u64,
        maximum: u64,
    },
    ExactCountOverflow,
    ExactCountStepMismatch {
        before: u64,
        after: u64,
    },
    NonCanonicalLane {
        name: &'static str,
        lane: usize,
        value: u32,
    },
    Fns3Mismatch,
    FederationMismatch,
    AgentMismatch,
    FullTurnPredecessorMismatch,
    CutoverExactStateMismatch,
    ExactStateChainBreak,
    FullTurnStateChainBreak,
}

impl fmt::Display for ExactFnspV3ReceiptEpochError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::LegacyEpochNumber => {
                f.write_str("exact receipt epoch zero is reserved for legacy")
            }
            Self::LegacyTipNotFinal => {
                f.write_str("exact epoch cutover requires a final legacy receipt")
            }
            Self::ExactReceiptNotFinal => f.write_str("exact receipt frame requires finality"),
            Self::ExactCountOutOfRange { count, maximum } => {
                write!(f, "exact FNSP-v3 count {count} is outside 1..={maximum}",)
            }
            Self::ExactCountOverflow => f.write_str("exact FNSP-v3 count overflow"),
            Self::ExactCountStepMismatch { before, after } => write!(
                f,
                "exact receipt frame count must advance by one ({before} -> {after})",
            ),
            Self::NonCanonicalLane { name, lane, value } => write!(
                f,
                "{name} lane {lane} is non-canonical BabyBear value {value}",
            ),
            Self::Fns3Mismatch => f.write_str("FNS3 does not bind the exact root/count pair"),
            Self::FederationMismatch => f.write_str("exact receipt frame federation changed"),
            Self::AgentMismatch => f.write_str("exact receipt frame agent changed"),
            Self::FullTurnPredecessorMismatch => f.write_str(
                "inner full-turn receipt does not extend the prior full-turn receipt hash",
            ),
            Self::CutoverExactStateMismatch => {
                f.write_str("first exact receipt does not begin at the activated exact state")
            }
            Self::ExactStateChainBreak => {
                f.write_str("exact FNSP-v3 root/count/FNS3 chain is discontinuous")
            }
            Self::FullTurnStateChainBreak => {
                f.write_str("inner full-turn receipt state chain is discontinuous")
            }
        }
    }
}

impl Error for ExactFnspV3ReceiptEpochError {}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_cell::Cell;
    use dregg_circuit::exact_nullifier_aafi::ExactNullifierAafi;

    fn state() -> ExactFnspV3StatePoint {
        let aafi = ExactNullifierAafi::new();
        ExactFnspV3StatePoint::new(aafi.root(), aafi.count()).expect("canonical exact state")
    }

    fn outer(tag: u32) -> ExactFnspV3OuterCommit {
        ExactFnspV3OuterCommit::new([BabyBear::new_canonical(tag); 8])
    }

    fn receipt(
        agent: dregg_cell::CellId,
        federation: [u8; 32],
        previous: [u8; 32],
        before: ExactFnspV3OuterCommit,
        after: ExactFnspV3OuterCommit,
    ) -> TurnReceipt {
        TurnReceipt {
            agent,
            federation_id: federation,
            previous_receipt_hash: Some(previous),
            pre_state_hash: before.to_bytes(),
            post_state_hash: after.to_bytes(),
            finality: Finality::Final,
            ..TurnReceipt::default()
        }
    }

    fn legacy_tip(agent: dregg_cell::CellId, federation: [u8; 32]) -> TurnReceipt {
        TurnReceipt {
            agent,
            federation_id: federation,
            post_state_hash: outer(3).to_bytes(),
            finality: Finality::Final,
            ..TurnReceipt::default()
        }
    }

    fn successor(before: ExactFnspV3StatePoint, tag: u32) -> ExactFnspV3StatePoint {
        ExactFnspV3StatePoint::new([BabyBear::new_canonical(tag); 8], before.count() + 1)
            .expect("successor")
    }

    fn binding(
        before: ExactFnspV3StatePoint,
        after: ExactFnspV3StatePoint,
        outer_before: ExactFnspV3OuterCommit,
        outer_after: ExactFnspV3OuterCommit,
    ) -> ExactFrameBinding {
        ExactFrameBinding {
            before,
            after,
            outer_before,
            outer_after,
            accepted_statement_digest: [21; 32],
            signed_spending_proof_digest: [22; 32],
        }
    }

    #[test]
    fn epoch_zero_and_tentative_cutover_refuse() {
        assert_eq!(
            ExactFnspV3ReceiptEpoch::new(0),
            Err(ExactFnspV3ReceiptEpochError::LegacyEpochNumber)
        );
        let agent = Cell::new([1; 32], [2; 32]).id();
        let mut tip = legacy_tip(agent, [4; 32]);
        tip.finality = Finality::Tentative;
        assert_eq!(
            ExactFnspV3ReceiptEpochV1::prepare(
                ExactFnspV3ReceiptEpoch::new(1).unwrap(),
                &tip,
                state(),
            ),
            Err(ExactFnspV3ReceiptEpochError::LegacyTipNotFinal)
        );
    }

    #[test]
    fn activation_hash_cannot_be_reinterpreted_as_the_full_turn_receipt_link() {
        let agent = Cell::new([1; 32], [2; 32]).id();
        let federation = [4; 32];
        let exact = state();
        let tip = legacy_tip(agent, federation);
        let activation = ExactFnspV3ReceiptEpochV1::prepare(
            ExactFnspV3ReceiptEpoch::new(7).unwrap(),
            &tip,
            exact,
        )
        .unwrap();
        let next = successor(exact, 11);

        // The full-turn chain must still name the terminal real receipt.  The
        // activation hash belongs only to the outer versioned frame chain.
        let conflated = receipt(
            agent,
            federation,
            activation.activation_hash(),
            outer(3),
            outer(100),
        );
        assert_eq!(
            PreparedExactFnspV3ReceiptFrameV1::begin_with_binding(
                &activation,
                conflated,
                binding(exact, next, outer(5), outer(6)),
            )
            .unwrap_err(),
            ExactFnspV3ReceiptEpochError::FullTurnPredecessorMismatch
        );
        assert_ne!(tip.receipt_hash(), activation.activation_hash());
    }

    #[test]
    fn exact_frame_chain_rejects_cross_version_and_mixed_state_roots() {
        let agent = Cell::new([1; 32], [2; 32]).id();
        let federation = [4; 32];
        let exact0 = state();
        let exact1 = successor(exact0, 11);
        let exact2 = successor(exact1, 12);
        let tip = legacy_tip(agent, federation);
        let activation = ExactFnspV3ReceiptEpochV1::prepare(
            ExactFnspV3ReceiptEpoch::new(7).unwrap(),
            &tip,
            exact0,
        )
        .unwrap();
        let first_receipt = receipt(agent, federation, tip.receipt_hash(), outer(3), outer(100));
        let first = PreparedExactFnspV3ReceiptFrameV1::begin_with_binding(
            &activation,
            first_receipt,
            binding(exact0, exact1, outer(5), outer(6)),
        )
        .expect("first exact frame");

        assert_ne!(first.receipt().pre_state_hash, outer(5).to_bytes());
        assert_ne!(first.receipt().post_state_hash, outer(6).to_bytes());
        assert_eq!(first.proof_outer_before(), outer(5));
        assert_eq!(first.proof_outer_after(), outer(6));

        // The outer exact frame hash cannot replace the ordinary receipt hash
        // in the inner full-state chain.
        let conflated_link = receipt(
            agent,
            federation,
            first.frame_hash(),
            outer(100),
            outer(101),
        );
        assert_eq!(
            PreparedExactFnspV3ReceiptFrameV1::extend_with_binding(
                &first,
                conflated_link,
                binding(exact1, exact2, outer(6), outer(7)),
            )
            .unwrap_err(),
            ExactFnspV3ReceiptEpochError::FullTurnPredecessorMismatch
        );

        // Correct full-turn link, but a different prior exact root/FNS3 pair is
        // not rescued by matching real receipt state hashes.
        let correct_link = receipt(
            agent,
            federation,
            first.receipt().receipt_hash(),
            outer(100),
            outer(101),
        );
        let mixed_prior =
            ExactFnspV3StatePoint::new([BabyBear::new_canonical(99); 8], exact1.count()).unwrap();
        assert_eq!(
            PreparedExactFnspV3ReceiptFrameV1::extend_with_binding(
                &first,
                correct_link,
                binding(mixed_prior, exact2, outer(6), outer(7)),
            )
            .unwrap_err(),
            ExactFnspV3ReceiptEpochError::ExactStateChainBreak
        );
    }

    #[test]
    fn frame_hash_and_signature_message_bind_epoch_and_both_exact_states() {
        let agent = Cell::new([1; 32], [2; 32]).id();
        let federation = [4; 32];
        let exact0 = state();
        let exact1 = successor(exact0, 11);
        let tip = legacy_tip(agent, federation);
        let activation = ExactFnspV3ReceiptEpochV1::prepare(
            ExactFnspV3ReceiptEpoch::new(7).unwrap(),
            &tip,
            exact0,
        )
        .unwrap();
        let first = PreparedExactFnspV3ReceiptFrameV1::begin_with_binding(
            &activation,
            receipt(agent, federation, tip.receipt_hash(), outer(3), outer(100)),
            binding(exact0, exact1, outer(5), outer(6)),
        )
        .unwrap();
        let message = first.canonical_executor_signed_message();
        assert_eq!(
            &message[..FRAME_SIGNATURE_DOMAIN.len()],
            FRAME_SIGNATURE_DOMAIN
        );
        assert_eq!(&message[FRAME_SIGNATURE_DOMAIN.len()..], first.frame_hash());

        let other_tip = legacy_tip(agent, federation);
        let other_epoch = ExactFnspV3ReceiptEpochV1::prepare(
            ExactFnspV3ReceiptEpoch::new(8).unwrap(),
            &other_tip,
            exact0,
        )
        .unwrap();
        let other = PreparedExactFnspV3ReceiptFrameV1::begin_with_binding(
            &other_epoch,
            receipt(
                agent,
                federation,
                other_tip.receipt_hash(),
                outer(3),
                outer(100),
            ),
            binding(exact0, exact1, outer(5), outer(6)),
        )
        .unwrap();
        assert_ne!(first.frame_hash(), other.frame_hash());
    }

    #[test]
    fn exact_state_constructor_derives_fns3_and_rejects_bad_claim() {
        let exact = state();
        assert_eq!(
            exact.fns3(),
            exact_state_commit(exact.root(), exact.count())
        );
        let mut bad = exact.fns3().map(|lane| lane.as_u32());
        bad[0] = (bad[0] + 1) % BABYBEAR_P;
        assert_eq!(
            ExactFnspV3StatePoint::from_u32(
                exact.root().map(|lane| lane.as_u32()),
                exact.count(),
                bad,
            ),
            Err(ExactFnspV3ReceiptEpochError::Fns3Mismatch)
        );
    }
}
