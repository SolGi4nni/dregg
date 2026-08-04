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

const RECEIPT_VERSION: u16 = 1;
const RECEIPT_DOMAIN: &[u8] = b"pathofangels.network/run-receipt/v1";
const DIGEST_DOMAIN: &str = "dreggnet-market/poa-expedition-digest/v1";
const MAX_PLAYER_BYTES: usize = 128;

/// The ship has roughly one thousand decks.  `0..=999` is the v1 receipt
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
    /// Digest the issuer authenticates as the executor/proof receipt. This
    /// field is not accepted as a judgement until the Lean verifier consumes it.
    pub run_receipt: [u8; 32],
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
        run_receipt: [u8; 32],
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
            run_receipt,
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

    /// Canonical v1 fields, excluding the domain separator and signature.
    pub fn canonical_fields(&self) -> Vec<u8> {
        let mut bytes = Vec::with_capacity(2 + 32 * 8 + 40 + self.player.len());
        bytes.extend_from_slice(&self.version.to_be_bytes());
        bytes.extend_from_slice(&self.federation);
        bytes.extend_from_slice(&self.session);
        bytes.extend_from_slice(&self.mission);
        bytes.extend_from_slice(&self.artifact_digest);
        bytes.extend_from_slice(&self.run_receipt);
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
        if claim.run_receipt == [0; 32] {
            return Err(PoaExpeditionError::MissingRunReceipt);
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
    MissingRunReceipt,
    InvalidStateTransition,
    InvalidPlayer,
    DeckOutOfBounds,
    SalvageSlotOutOfBounds,
    ContributionOutOfBounds,
    InvalidSignature,
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
            Self::MissingRunReceipt => {
                write!(f, "receipt does not name an asserted executor receipt")
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
            Self::MissingTransitionVerifier => write!(
                f,
                "PoA transition verifier is not wired; issuer authentication alone cannot mint"
            ),
        }
    }
}

impl std::error::Error for PoaExpeditionError {}
