//! Authenticated Path of Angels expedition receipts into bounded salvage.
//!
//! This is deliberately a narrow ingress adapter, not a second game engine.
//! A deployment pins the PoA federation, content/session epoch, and issuer key.
//! A receipt must be both authenticated and judged by the actual Lean-owned
//! transition verifier before it can mint an ordinary provenance-carrying
//! salvage note through [`dungeon_on_dregg::loot::LootVault`]. That runtime
//! verifier is not wired yet, so this module currently refuses every otherwise
//! valid mint with [`PoaExpeditionError::MissingTransitionVerifier`].
//!
//! The issuer signature authenticates the expedition result; it does not prove
//! the game transition.  The intended stronger producer is the PoA Lean program
//! and its emitted receipt artifact.  Keeping that distinction explicit avoids
//! turning this transport/domain adapter into a Rust-authored game semantics.

use std::fmt;

use dungeon_on_dregg::loot::LootVault;
use ed25519_dalek::{Signature, SigningKey, VerifyingKey};

const RECEIPT_VERSION: u16 = 2;
const RECEIPT_DOMAIN: &[u8] = b"pathofangels.network/expedition-judgement-receipt/v2";
const JUDGE_INPUT_DIGEST_DOMAIN: &[u8] = b"pathofangels.network/lean-judge-input-digest/v2";
const JUDGE_OUTPUT_DIGEST_DOMAIN: &[u8] = b"pathofangels.network/lean-judge-output-digest/v2";
const DIGEST_DOMAIN: &str = "dreggnet-market/poa-expedition-digest/v2";
const MAX_PLAYER_BYTES: usize = 128;

/// The ship has roughly one thousand decks.  `0..=999` is the v2 receipt
/// envelope; future content epochs can select another signed format/version.
pub const POA_DECK_COUNT: u16 = 1_000;

/// At most 32 independently addressable salvage discoveries may be claimed
/// from one expedition receipt namespace.  Each receipt names exactly one.
pub const POA_SALVAGE_SLOTS: u8 = 32;

/// Wire-admission limits only.  These prevent an authenticated receipt from
/// becoming an allocation/overflow carrier; they are not PoA game balance.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PoaContributionBounds {
    pub intel: u32,
    pub supplies: u32,
    pub cohesion: u32,
    pub influence: u32,
    pub score: u32,
}

impl PoaContributionBounds {
    pub fn contains(self, contribution: &PoaContributionClaim) -> bool {
        contribution.intel <= self.intel
            && contribution.supplies <= self.supplies
            && contribution.cohesion <= self.cohesion
            && contribution.influence <= self.influence
            && contribution.score <= self.score
            && contribution.relics.len() <= 64
            && {
                let mut relics = contribution.relics.clone();
                relics.sort_unstable();
                relics.dedup();
                relics.len() == contribution.relics.len()
            }
    }
}

/// Public contribution projection carried by the signed receipt.  The future
/// Lean-emitted wire adapter must populate this from
/// `Dregg2.Games.PathOfAngels.Contribution`; this Rust type does not claim type
/// identity with that proof-carrying Lean value.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PoaContributionClaim {
    pub intel: u32,
    pub supplies: u32,
    pub cohesion: u32,
    pub influence: u32,
    pub score: u32,
    pub relics: Vec<u32>,
}

/// The public statement signed by the PoA expedition receipt issuer.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PoaExpeditionClaim {
    pub version: u16,
    pub federation: [u8; 32],
    pub session: [u8; 32],
    pub mission: [u8; 32],
    /// Digest of the exact Lean-emitted program/schema bundle relied on by the
    /// receipt producer.  This adapter pins bytes; it does not reinterpret it.
    pub artifact_digest: [u8; 32],
    /// Exact 32-byte digest named by the pinned artifact for the bytes supplied
    /// to the Lean judge. The v2 signature labels and binds this value without
    /// rehashing, folding, decoding, or treating it as verification.
    pub judge_input_digest: [u8; 32],
    /// Exact 32-byte digest named by the pinned artifact for the bytes emitted
    /// by the Lean judge. It occupies a separately labelled v2 signature slot,
    /// so an input digest and output digest cannot be exchanged or cross-paired
    /// under a valid envelope signature.
    pub judge_output_digest: [u8; 32],
    pub pre_state: [u8; 32],
    pub post_state: [u8; 32],
    pub player: String,
    pub player_key: [u8; 32],
    /// Per-player/session receipt counter; zero is never a live receipt.
    pub counter: u64,
    pub deck: u16,
    pub salvage_slot: u8,
    pub contribution: PoaContributionClaim,
    /// Committed run seed used by the existing verified procgen/loot path.
    pub run_seed: [u8; 32],
}

impl PoaExpeditionClaim {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        federation: [u8; 32],
        session: [u8; 32],
        mission: [u8; 32],
        artifact_digest: [u8; 32],
        judge_input_digest: [u8; 32],
        judge_output_digest: [u8; 32],
        pre_state: [u8; 32],
        post_state: [u8; 32],
        player: impl Into<String>,
        player_key: [u8; 32],
        counter: u64,
        deck: u16,
        salvage_slot: u8,
        contribution: PoaContributionClaim,
        run_seed: [u8; 32],
    ) -> Self {
        Self {
            version: RECEIPT_VERSION,
            federation,
            session,
            mission,
            artifact_digest,
            judge_input_digest,
            judge_output_digest,
            pre_state,
            post_state,
            player: player.into(),
            player_key,
            counter,
            deck,
            salvage_slot,
            contribution,
            run_seed,
        }
    }

    /// Canonical v2 fields, excluding the receipt domain and signature.
    ///
    /// The judge digests are copied byte-for-byte after distinct, fixed labels.
    /// The pinned artifact owns their hashing/schema. A future transition
    /// verifier must recompute both from the exact input/output artifacts and
    /// establish that the judged input commits every transition-relevant claim
    /// field; this transport adapter deliberately does neither.
    pub fn canonical_fields(&self) -> Vec<u8> {
        let mut bytes = Vec::with_capacity(
            2 + 32 * 10
                + JUDGE_INPUT_DIGEST_DOMAIN.len()
                + JUDGE_OUTPUT_DIGEST_DOMAIN.len()
                + 49
                + self.player.len()
                + 4 * self.contribution.relics.len(),
        );
        bytes.extend_from_slice(&self.version.to_be_bytes());
        bytes.extend_from_slice(&self.federation);
        bytes.extend_from_slice(&self.session);
        bytes.extend_from_slice(&self.mission);
        bytes.extend_from_slice(&self.artifact_digest);
        bytes.extend_from_slice(JUDGE_INPUT_DIGEST_DOMAIN);
        bytes.push(0);
        bytes.extend_from_slice(&self.judge_input_digest);
        bytes.extend_from_slice(JUDGE_OUTPUT_DIGEST_DOMAIN);
        bytes.push(0);
        bytes.extend_from_slice(&self.judge_output_digest);
        bytes.extend_from_slice(&self.pre_state);
        bytes.extend_from_slice(&self.post_state);
        bytes.extend_from_slice(&(self.player.len() as u64).to_be_bytes());
        bytes.extend_from_slice(self.player.as_bytes());
        bytes.extend_from_slice(&self.player_key);
        bytes.extend_from_slice(&self.counter.to_be_bytes());
        bytes.extend_from_slice(&self.deck.to_be_bytes());
        bytes.push(self.salvage_slot);
        bytes.extend_from_slice(&self.contribution.intel.to_be_bytes());
        bytes.extend_from_slice(&self.contribution.supplies.to_be_bytes());
        bytes.extend_from_slice(&self.contribution.cohesion.to_be_bytes());
        bytes.extend_from_slice(&self.contribution.influence.to_be_bytes());
        bytes.extend_from_slice(&self.contribution.score.to_be_bytes());
        bytes.extend_from_slice(&(self.contribution.relics.len() as u64).to_be_bytes());
        for relic in &self.contribution.relics {
            bytes.extend_from_slice(&relic.to_be_bytes());
        }
        bytes.extend_from_slice(&self.run_seed);
        bytes
    }
}

/// A canonical claim plus the selected PoA expedition issuer's signature.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PoaExpeditionReceipt {
    pub claim: PoaExpeditionClaim,
    pub signature: [u8; 64],
}

impl PoaExpeditionReceipt {
    pub fn issue(claim: PoaExpeditionClaim, issuer: &SigningKey) -> Self {
        use ed25519_dalek::Signer as _;

        let message = signing_message(&claim);
        let signature = issuer.sign(&message).to_bytes();
        Self { claim, signature }
    }

    /// Digest of the exact signed claim.  A future judged-mint adapter can use
    /// this as its replay/provenance join, but this fail-closed adapter does not
    /// yet claim or persist it.
    pub fn digest(&self) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new_derive_key(DIGEST_DOMAIN);
        hasher.update(&signing_message(&self.claim));
        hasher.update(&self.signature);
        *hasher.finalize().as_bytes()
    }
}

fn signing_message(claim: &PoaExpeditionClaim) -> Vec<u8> {
    let claim_bytes = claim.canonical_fields();
    let mut message = Vec::with_capacity(RECEIPT_DOMAIN.len() + 1 + claim_bytes.len());
    message.extend_from_slice(RECEIPT_DOMAIN);
    message.push(0);
    message.extend_from_slice(&claim_bytes);
    message
}

/// Deployment-owned authority for one PoA federation and content/session epoch.
#[derive(Clone, Debug)]
pub struct PoaExpeditionPolicy {
    federation: [u8; 32],
    session: [u8; 32],
    mission: [u8; 32],
    artifact_digest: [u8; 32],
    contribution_bounds: PoaContributionBounds,
    issuer: VerifyingKey,
}

impl PoaExpeditionPolicy {
    pub fn new(
        federation: [u8; 32],
        session: [u8; 32],
        mission: [u8; 32],
        artifact_digest: [u8; 32],
        contribution_bounds: PoaContributionBounds,
        issuer: VerifyingKey,
    ) -> Self {
        Self {
            federation,
            session,
            mission,
            artifact_digest,
            contribution_bounds,
            issuer,
        }
    }

    pub const fn federation(&self) -> [u8; 32] {
        self.federation
    }

    pub const fn session(&self) -> [u8; 32] {
        self.session
    }

    pub fn issuer(&self) -> &VerifyingKey {
        &self.issuer
    }

    pub fn verify(&self, receipt: &PoaExpeditionReceipt) -> Result<(), PoaExpeditionError> {
        let claim = &receipt.claim;
        if claim.version != RECEIPT_VERSION {
            return Err(PoaExpeditionError::WrongVersion);
        }
        if claim.federation != self.federation {
            return Err(PoaExpeditionError::WrongFederation);
        }
        if claim.session != self.session {
            return Err(PoaExpeditionError::WrongSession);
        }
        if claim.mission != self.mission {
            return Err(PoaExpeditionError::WrongMission);
        }
        if claim.artifact_digest != self.artifact_digest {
            return Err(PoaExpeditionError::WrongArtifact);
        }
        if claim.judge_input_digest == [0; 32] {
            return Err(PoaExpeditionError::MissingJudgeInputDigest);
        }
        if claim.judge_output_digest == [0; 32] {
            return Err(PoaExpeditionError::MissingJudgeOutputDigest);
        }
        if claim.judge_input_digest == claim.judge_output_digest {
            return Err(PoaExpeditionError::InvalidJudgeDigestPair);
        }
        if claim.pre_state == [0; 32]
            || claim.post_state == [0; 32]
            || claim.pre_state == claim.post_state
        {
            return Err(PoaExpeditionError::InvalidStateTransition);
        }
        if claim.player.is_empty() || claim.player.len() > MAX_PLAYER_BYTES {
            return Err(PoaExpeditionError::InvalidPlayer);
        }
        if claim.player_key == [0; 32] || claim.counter == 0 {
            return Err(PoaExpeditionError::InvalidPlayer);
        }
        if claim.deck >= POA_DECK_COUNT {
            return Err(PoaExpeditionError::DeckOutOfBounds);
        }
        if claim.salvage_slot >= POA_SALVAGE_SLOTS {
            return Err(PoaExpeditionError::SalvageSlotOutOfBounds);
        }
        if !self.contribution_bounds.contains(&claim.contribution) {
            return Err(PoaExpeditionError::ContributionOutOfBounds);
        }
        let signature = Signature::from_bytes(&receipt.signature);
        self.issuer
            .verify_strict(&signing_message(claim), &signature)
            .map_err(|_| PoaExpeditionError::InvalidSignature)
    }
}

/// A versioned Lean judge protocol label.  The label is intentionally distinct
/// from the artifact digest: the former selects the public wire contract while
/// the latter pins the exact deployed Lean program/schema bundle.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PoaJudgeProgram {
    /// `POA-DARK-BAZAAR-IN-1` -> `POA-DARK-BAZAAR-OUT-1`, the bounded four-order
    /// private settlement judge.
    DarkBazaarV1,
}

/// A labelled observation of exact bytes entering and leaving a PoA Lean
/// judge.  Constructing this value does not assert that the judge accepted the
/// input; it only preserves the identities needed to join a runtime verdict to
/// a separately authenticated expedition receipt.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PoaLabelledJudgeObservation {
    pub program: PoaJudgeProgram,
    pub artifact_digest: [u8; 32],
    pub judge_input_digest: [u8; 32],
    pub judge_output_digest: [u8; 32],
}

impl PoaLabelledJudgeObservation {
    pub const fn dark_bazaar_v1(
        artifact_digest: [u8; 32],
        judge_input_digest: [u8; 32],
        judge_output_digest: [u8; 32],
    ) -> Self {
        Self {
            program: PoaJudgeProgram::DarkBazaarV1,
            artifact_digest,
            judge_input_digest,
            judge_output_digest,
        }
    }
}

/// Authenticated correlation evidence waiting for an actual Lean/runtime
/// transition verdict.  This type deliberately carries neither a minting
/// capability nor a claim that the observed output was accepted.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PoaPendingJudgeObservation {
    pub program: PoaJudgeProgram,
    pub receipt_digest: [u8; 32],
    pub artifact_digest: [u8; 32],
    pub judge_input_digest: [u8; 32],
    pub judge_output_digest: [u8; 32],
}

/// Deployment-selected receipt consumer. It deliberately has no issuer-only
/// mint path: the real Lean/runtime transition verifier must be wired first.
#[derive(Clone, Debug)]
pub struct PoaSalvageMinter {
    policy: PoaExpeditionPolicy,
}

impl PoaSalvageMinter {
    pub fn new(policy: PoaExpeditionPolicy) -> Self {
        Self { policy }
    }

    pub fn policy(&self) -> &PoaExpeditionPolicy {
        &self.policy
    }

    /// Authenticate an expedition envelope and correlate it with one labelled
    /// judge observation.  This is an observation-only stage: it accepts no
    /// [`LootVault`] and therefore cannot mint before a runtime has actually
    /// invoked the pinned Lean judge and validated its canonical output.
    pub fn observe_pending(
        &self,
        receipt: &PoaExpeditionReceipt,
        observation: PoaLabelledJudgeObservation,
    ) -> Result<PoaPendingJudgeObservation, PoaExpeditionError> {
        self.policy.verify(receipt)?;
        let claim = &receipt.claim;
        if observation.artifact_digest != claim.artifact_digest
            || observation.judge_input_digest != claim.judge_input_digest
            || observation.judge_output_digest != claim.judge_output_digest
        {
            return Err(PoaExpeditionError::JudgeObservationMismatch);
        }
        Ok(PoaPendingJudgeObservation {
            program: observation.program,
            receipt_digest: receipt.digest(),
            artifact_digest: observation.artifact_digest,
            judge_input_digest: observation.judge_input_digest,
            judge_output_digest: observation.judge_output_digest,
        })
    }

    /// Authenticate the outer envelope, then fail closed until the actual
    /// Lean-owned transition verifier can judge the bound mission/artifact,
    /// pre/post state, contribution, counter, and run seed.
    pub fn mint(
        &mut self,
        _vault: &mut LootVault,
        receipt: &PoaExpeditionReceipt,
    ) -> Result<(), PoaExpeditionError> {
        self.policy.verify(receipt)?;
        Err(PoaExpeditionError::MissingTransitionVerifier)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PoaExpeditionError {
    WrongVersion,
    WrongFederation,
    WrongSession,
    WrongMission,
    WrongArtifact,
    MissingJudgeInputDigest,
    MissingJudgeOutputDigest,
    InvalidJudgeDigestPair,
    InvalidStateTransition,
    InvalidPlayer,
    DeckOutOfBounds,
    SalvageSlotOutOfBounds,
    ContributionOutOfBounds,
    InvalidSignature,
    JudgeObservationMismatch,
    MissingTransitionVerifier,
}

impl fmt::Display for PoaExpeditionError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::WrongVersion => write!(f, "unsupported PoA expedition receipt version"),
            Self::WrongFederation => write!(f, "receipt belongs to another federation"),
            Self::WrongSession => write!(f, "receipt belongs to another PoA content session"),
            Self::WrongMission => write!(f, "receipt names an unknown PoA mission"),
            Self::WrongArtifact => write!(f, "receipt names another PoA program artifact"),
            Self::MissingJudgeInputDigest => write!(f, "receipt has no Lean judge input digest"),
            Self::MissingJudgeOutputDigest => write!(f, "receipt has no Lean judge output digest"),
            Self::InvalidJudgeDigestPair => {
                write!(
                    f,
                    "receipt reuses one digest for Lean judge input and output"
                )
            }
            Self::InvalidStateTransition => {
                write!(f, "receipt does not bind distinct nonzero pre/post states")
            }
            Self::InvalidPlayer => write!(
                f,
                "receipt player identity/key/counter is empty, zero, or oversized"
            ),
            Self::DeckOutOfBounds => write!(f, "receipt deck is outside the PoA ship envelope"),
            Self::SalvageSlotOutOfBounds => {
                write!(
                    f,
                    "receipt salvage slot is outside the bounded claim envelope"
                )
            }
            Self::ContributionOutOfBounds => {
                write!(
                    f,
                    "receipt contribution exceeds the deployment admission budget"
                )
            }
            Self::InvalidSignature => write!(f, "receipt issuer signature is invalid"),
            Self::JudgeObservationMismatch => write!(
                f,
                "labelled judge observation does not match the authenticated receipt"
            ),
            Self::MissingTransitionVerifier => write!(
                f,
                "PoA transition verifier is not wired; issuer authentication alone cannot mint"
            ),
        }
    }
}

impl std::error::Error for PoaExpeditionError {}
