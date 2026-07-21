//! Ordered-batch optimizer certificate over settled private Dark Bazaar results.
//!
//! Each input is an authoritatively settled [`DarkBazaarSession`] paired with the
//! [`PrivateClearingReceipt`] produced by its HidingFRI-gated settlement. The
//! certificate re-corroborates every public join, commits the exact ordered
//! `(session, rule, root8, price, volume, winner, settlement-turn)` source image,
//! and deterministically selects exactly `capacity` highest-price results (lower
//! source index wins ties). The objective is the exact checked sum of selected
//! clearing prices.
//!
//! This is a batch allocator over already-proved results, not a second clearing
//! engine. It never receives or stores bid openings, private quantities, seals,
//! blinds, or proof witnesses. The public roots and outputs were already exposed
//! by each private statement; winners and settlement turns were already exposed
//! by the real market settlement.
//!
//! [`PrivateBatchConsequenceGate`] consumes a valid certificate once through one
//! caller-supplied real target-engine turn. The resulting receipt binds the exact
//! optimizer certificate, allocations, target/tag, every source settlement turn,
//! and the target engine's committed turn. As with the single-clearing consequence
//! gate, this is a process-local consumer: source receipts must remain beside their
//! authoritative settled sessions. It does not turn them into transferable proof
//! objects or close the named ciphertext-to-private-root same-opening boundary.

use std::collections::BTreeMap;

use dregg_app_framework::{CellId, TurnReceipt};
use dregg_circuit_prove::dark_bazaar_private::{self, PublicStatement};
use dreggnet_offerings::DreggIdentity;

use super::PrivateClearingReceipt;
use crate::DarkBazaarSession;

const MAX_BATCH_SOURCES: usize = 64;
const SOURCE_IDENTITY_DOMAIN: &str = "dreggnet-market/private-batch-source-identity/v1";
const SOURCE_ROOT_DOMAIN: &str = "dreggnet-market/private-batch-sources/v1";
const CERTIFICATE_DOMAIN: &str = "dreggnet-market/private-batch-optimizer-certificate/v1";
const CONSEQUENCE_TAG_DOMAIN: &str = "dreggnet-market/private-batch-consequence-tag/v1";
const CONSEQUENCE_DOMAIN: &str = "dreggnet-market/private-batch-consequence/v1";

/// One authoritative private-clearing source in the caller-selected batch order.
#[derive(Clone, Copy)]
pub struct PrivateBatchSource<'a> {
    pub session: &'a DarkBazaarSession,
    pub receipt: &'a PrivateClearingReceipt,
}

impl<'a> PrivateBatchSource<'a> {
    pub const fn new(session: &'a DarkBazaarSession, receipt: &'a PrivateClearingReceipt) -> Self {
        Self { session, receipt }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct SourceImage {
    statement: PublicStatement,
    winner: DreggIdentity,
    settlement_turn_hash: [u8; 32],
}

impl SourceImage {
    fn price(&self) -> u32 {
        self.statement.p_star
    }
}

/// One selected public market result. No private order information is present.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PrivateBatchAllocation {
    pub source_index: u32,
    pub private_session: u32,
    pub private_root: [u32; dark_bazaar_private::DIGEST_WIDTH],
    pub winner: DreggIdentity,
    pub price: u32,
    pub settlement_turn_hash: [u8; 32],
}

/// Canonical deterministic optimizer certificate over one exact ordered source batch.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PrivateBatchOptimizerCertificate {
    source_root: [u8; 32],
    source_count: u32,
    capacity: u32,
    selected_indices: Vec<u32>,
    objective: u64,
    commitment: [u8; 32],
}

impl PrivateBatchOptimizerCertificate {
    /// Recheck all authoritative sources and mint their deterministic top-price
    /// allocation certificate. Construction is the only authority constructor.
    pub fn issue(
        sources: &[PrivateBatchSource<'_>],
        capacity: usize,
    ) -> Result<Self, PrivateBatchOptimizerError> {
        let images = validate_sources(sources)?;
        if capacity == 0 || capacity > images.len() {
            return Err(PrivateBatchOptimizerError::InvalidCapacity {
                capacity,
                sources: images.len(),
            });
        }
        let source_root = source_root(&images);
        let mut order = (0..images.len()).collect::<Vec<_>>();
        order.sort_by(|left, right| {
            images[*right]
                .price()
                .cmp(&images[*left].price())
                .then_with(|| left.cmp(right))
        });
        let selected_indices = order
            .into_iter()
            .take(capacity)
            .map(|index| u32::try_from(index).expect("MAX_BATCH_SOURCES is representable as u32"))
            .collect::<Vec<_>>();
        let objective = selected_indices.iter().try_fold(0u64, |total, index| {
            total.checked_add(u64::from(images[*index as usize].price()))
        });
        let objective = objective.ok_or(PrivateBatchOptimizerError::ArithmeticOverflow)?;
        let source_count =
            u32::try_from(images.len()).expect("MAX_BATCH_SOURCES is representable as u32");
        let capacity = u32::try_from(capacity).expect("capacity is bounded by source count");
        let commitment = certificate_commitment(
            source_root,
            source_count,
            capacity,
            &selected_indices,
            objective,
        );
        Ok(Self {
            source_root,
            source_count,
            capacity,
            selected_indices,
            objective,
            commitment,
        })
    }

    pub const fn source_root(&self) -> [u8; 32] {
        self.source_root
    }

    pub const fn source_count(&self) -> u32 {
        self.source_count
    }

    pub const fn capacity(&self) -> u32 {
        self.capacity
    }

    pub fn selected_indices(&self) -> &[u32] {
        &self.selected_indices
    }

    pub const fn objective(&self) -> u64 {
        self.objective
    }

    pub const fn commitment(&self) -> [u8; 32] {
        self.commitment
    }

    /// Verify against the exact live source order and an independently selected
    /// capacity. A valid certificate for another batch or capacity cannot cross.
    pub fn verify(
        &self,
        sources: &[PrivateBatchSource<'_>],
        expected_capacity: usize,
    ) -> Result<(), PrivateBatchOptimizerError> {
        let reproduced = Self::issue(sources, expected_capacity)?;
        if &reproduced != self {
            return Err(PrivateBatchOptimizerError::CertificateMismatch);
        }
        Ok(())
    }

    /// Verify, then map selected indices to their real public winners and turns.
    pub fn allocations(
        &self,
        sources: &[PrivateBatchSource<'_>],
        expected_capacity: usize,
    ) -> Result<Vec<PrivateBatchAllocation>, PrivateBatchOptimizerError> {
        self.verify(sources, expected_capacity)?;
        Ok(self
            .selected_indices
            .iter()
            .map(|index| {
                let receipt = sources[*index as usize].receipt;
                PrivateBatchAllocation {
                    source_index: *index,
                    private_session: receipt.statement.session,
                    private_root: receipt.statement.order_root,
                    winner: receipt.winner.clone(),
                    price: receipt.statement.p_star,
                    settlement_turn_hash: receipt.settlement_turn.turn_hash,
                }
            })
            .collect())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PrivateBatchOptimizerError {
    EmptyBatch,
    TooManySources { actual: usize, maximum: usize },
    InvalidCapacity { capacity: usize, sources: usize },
    SourceMismatch { index: usize, reason: &'static str },
    DuplicateSource { first: usize, second: usize },
    ArithmeticOverflow,
    CertificateMismatch,
    TargetMismatch,
    AlreadyConsumed,
    GameRefused(String),
    InvalidGameTurn(&'static str),
}

impl std::fmt::Display for PrivateBatchOptimizerError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}

impl std::error::Error for PrivateBatchOptimizerError {}

/// Product-owned namespace for one consequence of the private batch optimizer.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PrivateBatchConsequenceTag(pub [u8; 32]);

impl PrivateBatchConsequenceTag {
    pub fn from_label(label: &str) -> Self {
        Self(
            *blake3::Hasher::new_derive_key(CONSEQUENCE_TAG_DOMAIN)
                .update(&(label.len() as u64).to_be_bytes())
                .update(label.as_bytes())
                .finalize()
                .as_bytes(),
        )
    }
}

/// Receipt for one real target-engine turn authorized by the exact batch plan.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PrivateBatchConsequenceReceipt {
    pub consequence_id: [u8; 32],
    pub certificate_commitment: [u8; 32],
    pub source_root: [u8; 32],
    pub objective: u64,
    pub allocations: Vec<PrivateBatchAllocation>,
    pub target_cell: CellId,
    pub consequence_tag: PrivateBatchConsequenceTag,
    pub game_turn_hash: [u8; 32],
}

/// One-shot target-engine consumer pinned to one optimizer certificate.
pub struct PrivateBatchConsequenceGate {
    target_cell: CellId,
    consequence_tag: PrivateBatchConsequenceTag,
    certificate: PrivateBatchOptimizerCertificate,
    consumed: bool,
}

impl PrivateBatchConsequenceGate {
    pub fn new(
        target_cell: CellId,
        consequence_tag: PrivateBatchConsequenceTag,
        certificate: PrivateBatchOptimizerCertificate,
    ) -> Self {
        Self {
            target_cell,
            consequence_tag,
            certificate,
            consumed: false,
        }
    }

    pub const fn target_cell(&self) -> CellId {
        self.target_cell
    }

    pub const fn consequence_tag(&self) -> PrivateBatchConsequenceTag {
        self.consequence_tag
    }

    pub fn certificate(&self) -> &PrivateBatchOptimizerCertificate {
        &self.certificate
    }

    pub const fn consumed(&self) -> bool {
        self.consumed
    }

    /// Restore the durable one-shot bit before accepting work after restart.
    pub fn restore_consumed(&mut self, consumed: bool) {
        self.consumed = consumed;
    }

    /// Reverify the complete source batch, derive the selected public allocations,
    /// then dispatch exactly one real target-engine turn. Refusal consumes nothing.
    pub fn apply_game_turn<F>(
        &mut self,
        sources: &[PrivateBatchSource<'_>],
        target_cell: CellId,
        game_turn: F,
    ) -> Result<PrivateBatchConsequenceReceipt, PrivateBatchOptimizerError>
    where
        F: FnOnce(&[PrivateBatchAllocation]) -> Result<TurnReceipt, String>,
    {
        if target_cell != self.target_cell {
            return Err(PrivateBatchOptimizerError::TargetMismatch);
        }
        let allocations = self
            .certificate
            .allocations(sources, self.certificate.capacity as usize)?;
        if self.consumed {
            return Err(PrivateBatchOptimizerError::AlreadyConsumed);
        }
        let game_receipt =
            game_turn(&allocations).map_err(PrivateBatchOptimizerError::GameRefused)?;
        validate_game_receipt(&game_receipt)?;
        let consequence_id = consequence_id(
            self.target_cell,
            self.consequence_tag,
            self.certificate.commitment,
        );
        self.consumed = true;
        Ok(PrivateBatchConsequenceReceipt {
            consequence_id,
            certificate_commitment: self.certificate.commitment,
            source_root: self.certificate.source_root,
            objective: self.certificate.objective,
            allocations,
            target_cell,
            consequence_tag: self.consequence_tag,
            game_turn_hash: game_receipt.turn_hash,
        })
    }
}

fn validate_sources(
    sources: &[PrivateBatchSource<'_>],
) -> Result<Vec<SourceImage>, PrivateBatchOptimizerError> {
    if sources.is_empty() {
        return Err(PrivateBatchOptimizerError::EmptyBatch);
    }
    if sources.len() > MAX_BATCH_SOURCES {
        return Err(PrivateBatchOptimizerError::TooManySources {
            actual: sources.len(),
            maximum: MAX_BATCH_SOURCES,
        });
    }
    let mut images = Vec::with_capacity(sources.len());
    let mut seen = BTreeMap::new();
    for (index, source) in sources.iter().enumerate() {
        let session = source.session;
        let receipt = source.receipt;
        let fail = |reason| PrivateBatchOptimizerError::SourceMismatch { index, reason };
        if !session.is_settled() {
            return Err(fail("market is not settled"));
        }
        if receipt.statement.rule != dark_bazaar_private::RULE_ID {
            return Err(fail("private rule differs"));
        }
        if receipt.statement.session != session.private_proof_session() {
            return Err(fail("private session differs"));
        }
        if receipt.statement.v_star != 1 {
            return Err(fail("clearing volume is not the live one-unit mechanic"));
        }
        let live_price = session
            .clearing()
            .and_then(|clearing| u32::try_from(clearing.price()).ok());
        if live_price != Some(receipt.statement.p_star) {
            return Err(fail("clearing price differs from live settlement"));
        }
        if session.winning_actor() != Some(&receipt.winner) {
            return Err(fail("winner differs from live settlement"));
        }
        if receipt.settlement_turn.turn_hash == [0; 32] {
            return Err(fail("settlement turn hash is zero"));
        }
        let image = SourceImage {
            statement: receipt.statement,
            winner: receipt.winner.clone(),
            settlement_turn_hash: receipt.settlement_turn.turn_hash,
        };
        let market_digest = source_market_digest(&image);
        if let Some(first) = seen.insert(market_digest, index) {
            return Err(PrivateBatchOptimizerError::DuplicateSource {
                first,
                second: index,
            });
        }
        images.push(image);
    }
    Ok(images)
}

fn source_market_digest(image: &SourceImage) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key(SOURCE_IDENTITY_DOMAIN);
    hasher.update(&image.statement.session.to_be_bytes());
    hasher.update(&image.statement.rule.to_be_bytes());
    for lane in image.statement.order_root {
        hasher.update(&lane.to_be_bytes());
    }
    *hasher.finalize().as_bytes()
}

fn source_binding_digest(image: &SourceImage) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key(SOURCE_ROOT_DOMAIN);
    hasher.update(&source_market_digest(image));
    hasher.update(&image.statement.p_star.to_be_bytes());
    hasher.update(&image.statement.v_star.to_be_bytes());
    hasher.update(&(image.winner.0.len() as u64).to_be_bytes());
    hasher.update(image.winner.0.as_bytes());
    hasher.update(&image.settlement_turn_hash);
    *hasher.finalize().as_bytes()
}

fn source_image_digest(index: usize, image: &SourceImage) -> [u8; 32] {
    *blake3::Hasher::new_derive_key(SOURCE_ROOT_DOMAIN)
        .update(&(index as u64).to_be_bytes())
        .update(&source_binding_digest(image))
        .finalize()
        .as_bytes()
}

fn source_root(images: &[SourceImage]) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key(SOURCE_ROOT_DOMAIN);
    hasher.update(&(images.len() as u64).to_be_bytes());
    for (index, image) in images.iter().enumerate() {
        hasher.update(&source_image_digest(index, image));
    }
    *hasher.finalize().as_bytes()
}

fn certificate_commitment(
    source_root: [u8; 32],
    source_count: u32,
    capacity: u32,
    selected_indices: &[u32],
    objective: u64,
) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key(CERTIFICATE_DOMAIN);
    hasher.update(&source_root);
    hasher.update(&source_count.to_be_bytes());
    hasher.update(&capacity.to_be_bytes());
    hasher.update(&(selected_indices.len() as u32).to_be_bytes());
    for index in selected_indices {
        hasher.update(&index.to_be_bytes());
    }
    hasher.update(&objective.to_be_bytes());
    *hasher.finalize().as_bytes()
}

fn consequence_id(
    target_cell: CellId,
    consequence_tag: PrivateBatchConsequenceTag,
    certificate_commitment: [u8; 32],
) -> [u8; 32] {
    *blake3::Hasher::new_derive_key(CONSEQUENCE_DOMAIN)
        .update(&target_cell.0)
        .update(&consequence_tag.0)
        .update(&certificate_commitment)
        .finalize()
        .as_bytes()
}

fn validate_game_receipt(receipt: &TurnReceipt) -> Result<(), PrivateBatchOptimizerError> {
    if receipt.turn_hash == [0; 32] {
        return Err(PrivateBatchOptimizerError::InvalidGameTurn(
            "zero turn hash",
        ));
    }
    if receipt.action_count == 0 {
        return Err(PrivateBatchOptimizerError::InvalidGameTurn(
            "empty action set",
        ));
    }
    if receipt.pre_state_hash == receipt.post_state_hash {
        return Err(PrivateBatchOptimizerError::InvalidGameTurn(
            "state did not change",
        ));
    }
    Ok(())
}
