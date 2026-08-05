//! Path of Angels server admission for Solana `$DREGG` holders.
//!
//! This crate is an adapter, not a second Solana verifier. Wallet control uses
//! an exact PoA challenge transcript and the governance [`OwnerBinding`] wire
//! solely as a fixed-size `(player, signature)` carrier; it does not reuse a
//! broader governance signature. Raw RPC decoding uses `dregg-bridge`; the
//! live account shape is `dregg-pay`'s watcher seam. Consensus upgrade uses
//! `solana_feed` unchanged.
//!
//! A [`TrustTier::BetaRpcAttested`] capability is intentionally weaker than a
//! consensus holding and has no conversion into governance weight. Existing
//! governance code rejects `StructureOnly` before rendering any weight verdict.

use std::collections::{HashMap, HashSet};

use dregg_bridge::solana_feed::{HoldingFeedSource, prove_feed_holding_with_policy};
use dregg_bridge::solana_holdings::{
    HoldingAssetPolicy, HoldingProofError, ProvenHolding, decode_token_account,
};
use dregg_bridge::solana_provenance::WeakSubjectivityAnchor;
use dregg_governance::holding_weight::OwnerBinding;
use dregg_pay::watcher::FetchedAccount;
use ed25519_dalek::VerifyingKey;
use serde::{Deserialize, Serialize};
use sha2::{Digest as _, Sha256};

pub const DREGG_MINT_BASE58: &str = "XkeTXo1125vz5H9svJpGiw4JvLbN8VmMu9cmMvspump";
/// The `$DREGG` mint account is owned by Token-2022 (confirmed from finalized
/// mainnet `getAccountInfo`), not the legacy SPL Token program.
pub const DREGG_TOKEN_PROGRAM_BASE58: &str = "TokenzQdBNbLqP5VEhdkAS6EPFLC1PHnBqCXEpPxuEb";
pub const MAINNET_GENESIS_BASE58: &str = "5eykt4UsFv8P8NJdTREpY1vzqKqZKvdpKuc147dw2N9d";
const CHALLENGE_DOMAIN: &[u8] = b"path-of-angels/dregg-holding/challenge/v2";
const WALLET_CONSENT_DOMAIN: &[u8] = b"path-of-angels/dregg-holding/wallet-consent/v2";
const RECEIPT_DOMAIN: &[u8] = b"path-of-angels/dregg-holding/receipt/v2";
const CONSENSUS_RESERVATION_DOMAIN: &[u8] =
    b"path-of-angels/dregg-holding/consensus-reservation/v1";
const CONSENSUS_PRIVILEGE_NULLIFIER_DOMAIN: &[u8] =
    b"path-of-angels/dregg-holding/privilege-nullifier/v1";
const CONSENSUS_EVIDENCE_DOMAIN: &[u8] = b"path-of-angels/dregg-holding/consensus-evidence/v1";
const CONSENSUS_CAPABILITY_DOMAIN: &[u8] = b"path-of-angels/dregg-holding/consensus-capability/v1";
const EXTERNAL_CHECKPOINT_DOMAIN: &[u8] = b"path-of-angels/dregg-holding/external-checkpoint/v1";

pub type Bytes32 = [u8; 32];
/// Reservation window for the independently anchored proof/finality path. The
/// eventual capability remains shorter-lived; this merely prevents wallet
/// consent from expiring while the server assembles consensus evidence.
pub const CONSENSUS_RESERVATION_TTL_SECS: u64 = 15 * 60;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GateConfig {
    pub federation_id: Bytes32,
    pub origin: String,
    pub domain: String,
    pub cluster: String,
    pub genesis_hash: Bytes32,
    pub rpc_endpoint_id: Bytes32,
    pub mint: Bytes32,
    pub token_program: Bytes32,
    pub minimum_raw_balance: u64,
    pub challenge_ttl_secs: u64,
    pub capability_ttl_secs: u64,
}

impl GateConfig {
    pub fn path_of_angels_mainnet(federation_id: Bytes32, rpc_endpoint_id: Bytes32) -> Self {
        let dregg = HoldingAssetPolicy::dregg_mainnet();
        Self {
            federation_id,
            origin: "https://beta.pathofangels.network".into(),
            domain: "pathofangels.network".into(),
            cluster: "solana:mainnet-beta".into(),
            genesis_hash: decode_pubkey(MAINNET_GENESIS_BASE58).expect("mainnet genesis constant"),
            rpc_endpoint_id,
            mint: *dregg.mint(),
            token_program: dregg.program_id(),
            minimum_raw_balance: 1,
            challenge_ttl_secs: 300,
            capability_ttl_secs: 120,
        }
    }

    pub fn validate(&self) -> Result<(), GateError> {
        let dregg = HoldingAssetPolicy::dregg_mainnet();
        if self.origin != "https://beta.pathofangels.network"
            || self.domain != "pathofangels.network"
            || self.cluster != "solana:mainnet-beta"
            || self.genesis_hash != decode_pubkey(MAINNET_GENESIS_BASE58)?
            || self.mint != *dregg.mint()
            || self.token_program != dregg.program_id()
            || self.minimum_raw_balance == 0
            || self.challenge_ttl_secs == 0
            || self.capability_ttl_secs == 0
        {
            return Err(GateError::InvalidConfiguration);
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Challenge {
    id: Bytes32,
    player: Bytes32,
    player_cell: Bytes32,
    wallet: Bytes32,
    nonce: Bytes32,
    federation_id: Bytes32,
    origin: String,
    domain: String,
    cluster: String,
    genesis_hash: Bytes32,
    rpc_endpoint_id: Bytes32,
    mint: Bytes32,
    token_program: Bytes32,
    minimum_raw_balance: u64,
    min_context_slot: u64,
    issued_at: u64,
    expires_at: u64,
    capability_ttl_secs: u64,
}

impl Challenge {
    pub fn id(&self) -> Bytes32 {
        self.id
    }
    /// Exact Dregg signing public key this wallet chose to sponsor.
    pub fn player(&self) -> Bytes32 {
        self.player
    }
    /// Canonical one-player cell derived from [`Self::player`].
    pub fn player_cell(&self) -> Bytes32 {
        self.player_cell
    }
    pub fn wallet(&self) -> Bytes32 {
        self.wallet
    }
    pub fn nonce(&self) -> Bytes32 {
        self.nonce
    }
    pub fn issued_at(&self) -> u64 {
        self.issued_at
    }
    pub fn expires_at(&self) -> u64 {
        self.expires_at
    }
    pub fn min_context_slot(&self) -> u64 {
        self.min_context_slot
    }
    /// Exact wallet `signMessage` bytes. Unlike the reusable governance owner
    /// binding, this PoA-specific consent commits the complete issued challenge
    /// (deployment, federation, player, mint, slot floor, nonce, and expiry).
    pub fn signing_message(&self) -> Vec<u8> {
        challenge_signing_message(self)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Commitment {
    Finalized,
    Confirmed,
    Processed,
}

#[derive(Clone, Debug)]
pub struct RpcTokenAccount {
    pub address: Bytes32,
    pub account: FetchedAccount,
}

#[derive(Clone, Debug)]
pub struct RpcAccountSet {
    pub endpoint_id: Bytes32,
    pub genesis_hash: Bytes32,
    pub commitment: Commitment,
    pub requested_min_context_slot: u64,
    pub context_slot: u64,
    pub accounts: Vec<RpcTokenAccount>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RpcHoldingQuery {
    pub owner: Bytes32,
    pub mint: Bytes32,
    pub token_program: Bytes32,
    pub commitment: Commitment,
    pub min_context_slot: u64,
    pub expected_genesis_hash: Bytes32,
}

/// Live-source seam. Only the PoA server implements this over HTTPS JSON-RPC;
/// no client request is ever deserialized as an `RpcAccountSet`.
pub trait RpcHoldingSource {
    type Error: std::fmt::Display;
    fn fetch_token_accounts(&self, query: &RpcHoldingQuery) -> Result<RpcAccountSet, Self::Error>;
}

pub fn observe_with_rpc_source<S: RpcHoldingSource>(
    source: &S,
    config: &GateConfig,
    challenge: &Challenge,
) -> Result<RpcBetaObservation, GateError> {
    let query = RpcHoldingQuery {
        owner: challenge.wallet,
        mint: challenge.mint,
        token_program: challenge.token_program,
        commitment: Commitment::Finalized,
        min_context_slot: challenge.min_context_slot,
        expected_genesis_hash: challenge.genesis_hash,
    };
    let snapshot = source
        .fetch_token_accounts(&query)
        .map_err(|e| GateError::RpcSource(e.to_string()))?;
    validate_rpc_snapshot(config, challenge, &snapshot)
}

/// The only beta evidence constructor. Every account is decoded by the existing
/// bridge primitive; no client balance field exists in this API.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RpcBetaObservation {
    endpoint_id: Bytes32,
    wallet: Bytes32,
    mint: Bytes32,
    token_accounts: Vec<Bytes32>,
    amount: u64,
    slot: u64,
}

pub fn validate_rpc_snapshot(
    config: &GateConfig,
    challenge: &Challenge,
    snapshot: &RpcAccountSet,
) -> Result<RpcBetaObservation, GateError> {
    config.validate()?;
    let policy = HoldingAssetPolicy::dregg_mainnet();
    if snapshot.endpoint_id != config.rpc_endpoint_id
        || snapshot.endpoint_id != challenge.rpc_endpoint_id
    {
        return Err(GateError::WrongRpcEndpoint);
    }
    if snapshot.genesis_hash != config.genesis_hash
        || snapshot.genesis_hash != challenge.genesis_hash
    {
        return Err(GateError::WrongCluster);
    }
    if snapshot.commitment != Commitment::Finalized {
        return Err(GateError::NotFinalized);
    }
    if snapshot.requested_min_context_slot != challenge.min_context_slot
        || snapshot.context_slot < challenge.min_context_slot
    {
        return Err(GateError::StaleSlot);
    }

    let mut amount = 0u64;
    let mut token_accounts = Vec::with_capacity(snapshot.accounts.len());
    let mut seen = HashSet::new();
    for item in &snapshot.accounts {
        if item.account.slot != snapshot.context_slot {
            return Err(GateError::MixedSlots);
        }
        if item.account.owner_program != policy.program_id() {
            return Err(GateError::WrongTokenProgram);
        }
        if !seen.insert(item.address) {
            return Err(GateError::DuplicateTokenAccount);
        }
        let decoded = decode_token_account(&item.account.data, policy.token_program())
            .map_err(|_| GateError::MalformedTokenAccount)?;
        let (mint, owner, balance) = (decoded.mint, decoded.owner, decoded.amount);
        if mint != config.mint || mint != challenge.mint {
            return Err(GateError::WrongMint);
        }
        if owner != challenge.wallet {
            return Err(GateError::WrongOwner);
        }
        amount = amount
            .checked_add(balance)
            .ok_or(GateError::BalanceOverflow)?;
        token_accounts.push(item.address);
    }
    if amount < challenge.minimum_raw_balance {
        return Err(GateError::InsufficientBalance);
    }
    Ok(RpcBetaObservation {
        endpoint_id: snapshot.endpoint_id,
        wallet: challenge.wallet,
        mint: challenge.mint,
        token_accounts,
        amount,
        slot: snapshot.context_slot,
    })
}

/// Upgrade path through the existing anchored Solana feed. This is the only
/// function here that can return a `ConsensusVerified` holding.
pub fn verify_consensus_source<S: HoldingFeedSource>(
    source: &S,
    token_account: &Bytes32,
    config: &GateConfig,
    pinned_anchor: &WeakSubjectivityAnchor,
    require_poh: bool,
) -> Result<VerifiedConsensusHolding, ConsensusSourceError> {
    config
        .validate()
        .map_err(ConsensusSourceError::Configuration)?;
    let feed = source
        .ingest_holding(token_account)
        .map_err(|e| ConsensusSourceError::Feed(e.to_string()))?;
    let policy = HoldingAssetPolicy::dregg_mainnet();
    let holding = prove_feed_holding_with_policy(&feed, &policy, pinned_anchor, require_poh)
        .map_err(ConsensusSourceError::Proof)?;
    if !holding.is_consensus_proven() {
        return Err(ConsensusSourceError::NotConsensusProven);
    }
    if holding.token_account != *token_account
        || holding.mint != config.mint
        || holding.amount < config.minimum_raw_balance
    {
        return Err(ConsensusSourceError::HoldingPolicyMismatch);
    }
    let evidence_digest = consensus_evidence_digest(&holding, config, pinned_anchor, require_poh);
    Ok(VerifiedConsensusHolding {
        holding,
        token_program: config.token_program,
        cluster: config.cluster.clone(),
        genesis_hash: config.genesis_hash,
        ingest_source_id: config.rpc_endpoint_id,
        anchor_epoch: pinned_anchor.epoch,
        anchor_stake_table_root: pinned_anchor.stake_table_root,
        require_poh,
        evidence_digest,
    })
}

/// A consensus holding after the existing anchored Solana verifier has accepted
/// it.  The constructor is private: callers cannot relabel a beta RPC read by
/// constructing this adapter around a public `ProvenHolding` value.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerifiedConsensusHolding {
    holding: ProvenHolding,
    token_program: Bytes32,
    cluster: String,
    genesis_hash: Bytes32,
    ingest_source_id: Bytes32,
    anchor_epoch: u64,
    anchor_stake_table_root: Bytes32,
    require_poh: bool,
    evidence_digest: Bytes32,
}

impl VerifiedConsensusHolding {
    pub fn token_account(&self) -> Bytes32 {
        self.holding.token_account
    }
    pub fn owner(&self) -> Bytes32 {
        self.holding.owner
    }
    pub fn mint(&self) -> Bytes32 {
        self.holding.mint
    }
    pub fn amount(&self) -> u64 {
        self.holding.amount
    }
    pub fn slot(&self) -> u64 {
        self.holding.slot
    }
    pub fn token_program(&self) -> Bytes32 {
        self.token_program
    }
    pub fn cluster(&self) -> &str {
        &self.cluster
    }
    pub fn genesis_hash(&self) -> Bytes32 {
        self.genesis_hash
    }
    /// Identifier of the configured ingestion source. This is provenance, not
    /// the authority grade: authority comes from the independently pinned anchor.
    pub fn ingest_source_id(&self) -> Bytes32 {
        self.ingest_source_id
    }
    pub fn anchor_epoch(&self) -> u64 {
        self.anchor_epoch
    }
    pub fn anchor_stake_table_root(&self) -> Bytes32 {
        self.anchor_stake_table_root
    }
    pub fn require_poh(&self) -> bool {
        self.require_poh
    }
    pub fn evidence_digest(&self) -> Bytes32 {
        self.evidence_digest
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ConsensusEvidenceGrade {
    /// Finalized account inclusion and stake provenance verified against an
    /// independently supplied weak-subjectivity checkpoint.
    IndependentlyAnchoredFinalizedAccount,
}

/// Exact game-local intent reserved before expensive holding/finality work.
/// These are coordinates, not Rust-owned game semantics: Lean remains the
/// privilege decider.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ConsensusPrivilegeIntent {
    deployment_id: Bytes32,
    event_id: Bytes32,
    privilege_id: Bytes32,
    action_token: Bytes32,
    beneficiary: Bytes32,
    event_sequence: u64,
    expires_after_sequence: u64,
}

impl ConsensusPrivilegeIntent {
    pub fn new(
        deployment_id: Bytes32,
        event_id: Bytes32,
        privilege_id: Bytes32,
        action_token: Bytes32,
        beneficiary: Bytes32,
        event_sequence: u64,
        expires_after_sequence: u64,
    ) -> Result<Self, GateError> {
        if deployment_id == [0; 32]
            || event_id == [0; 32]
            || privilege_id == [0; 32]
            || action_token == [0; 32]
            || event_sequence == 0
            || expires_after_sequence < event_sequence
        {
            return Err(GateError::InvalidPrivilegeIntent);
        }
        Ok(Self {
            deployment_id,
            event_id,
            privilege_id,
            action_token,
            beneficiary,
            event_sequence,
            expires_after_sequence,
        })
    }
    pub fn deployment_id(&self) -> Bytes32 {
        self.deployment_id
    }
    pub fn event_id(&self) -> Bytes32 {
        self.event_id
    }
    pub fn privilege_id(&self) -> Bytes32 {
        self.privilege_id
    }
    pub fn action_token(&self) -> Bytes32 {
        self.action_token
    }
    pub fn beneficiary(&self) -> Bytes32 {
        self.beneficiary
    }
    pub fn event_sequence(&self) -> u64 {
        self.event_sequence
    }
    pub fn expires_after_sequence(&self) -> u64 {
        self.expires_after_sequence
    }
}

/// Reservation body persisted before the long consensus/finality path begins.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ConsensusPrivilegeReservation {
    reservation_id: Bytes32,
    challenge_id: Bytes32,
    wallet: Bytes32,
    player: Bytes32,
    player_cell: Bytes32,
    federation_id: Bytes32,
    intent: ConsensusPrivilegeIntent,
    privilege_nullifier: Bytes32,
    issued_at: u64,
    expires_at: u64,
}

impl ConsensusPrivilegeReservation {
    pub fn reservation_id(&self) -> Bytes32 {
        self.reservation_id
    }
    pub fn challenge_id(&self) -> Bytes32 {
        self.challenge_id
    }
    pub fn wallet(&self) -> Bytes32 {
        self.wallet
    }
    pub fn player(&self) -> Bytes32 {
        self.player
    }
    pub fn player_cell(&self) -> Bytes32 {
        self.player_cell
    }
    pub fn federation_id(&self) -> Bytes32 {
        self.federation_id
    }
    pub fn intent(&self) -> &ConsensusPrivilegeIntent {
        &self.intent
    }
    pub fn privilege_nullifier(&self) -> Bytes32 {
        self.privilege_nullifier
    }
    pub fn issued_at(&self) -> u64 {
        self.issued_at
    }
    pub fn expires_at(&self) -> u64 {
        self.expires_at
    }
}

/// Exact append-only checkpoint produced by the admission store after a
/// reservation. It is only a local report until an external verifier seals it.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ConsensusAdmissionCheckpoint {
    pub journal_len: u64,
    pub journal_head: Bytes32,
    pub observed_time_floor: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ConsensusReservationReceipt {
    reservation: ConsensusPrivilegeReservation,
    checkpoint: ConsensusAdmissionCheckpoint,
}

impl ConsensusReservationReceipt {
    /// Rebuild the exact receipt an [`AdmissionStore`] already recorded, from the
    /// durable reservation and the checkpoint that record produced.
    ///
    /// This is store-side reconstruction, not a second issuance path. It mints no
    /// authority the durable lineage does not already carry, and it cannot be used
    /// to widen one: [`Gate::admit_consensus`] reloads the store's own receipt,
    /// requires it to equal the receipt the caller presented, and requires the
    /// accompanying [`ExternallyAnchoredCheckpoint`] to carry a valid external seal
    /// over exactly this checkpoint. A fabricated pair therefore fails at the
    /// comparison, not at the constructor.
    pub fn from_durable_record(
        reservation: ConsensusPrivilegeReservation,
        checkpoint: ConsensusAdmissionCheckpoint,
    ) -> Self {
        Self {
            reservation,
            checkpoint,
        }
    }
    pub fn reservation(&self) -> &ConsensusPrivilegeReservation {
        &self.reservation
    }
    pub fn checkpoint(&self) -> ConsensusAdmissionCheckpoint {
        self.checkpoint
    }
}

/// Node-selected verifier for a checkpoint published outside the local redb
/// blob. There is intentionally no built-in "trust local anchor" implementation.
pub trait ExternalCheckpointVerifier {
    type Proof;
    type Error: std::fmt::Display;
    fn verify_checkpoint(
        &self,
        checkpoint: &ConsensusAdmissionCheckpoint,
        proof: &Self::Proof,
    ) -> Result<Bytes32, Self::Error>;
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExternallyAnchoredCheckpoint {
    checkpoint: ConsensusAdmissionCheckpoint,
    verifier_id: Bytes32,
    external_receipt: Bytes32,
    seal: Bytes32,
}

impl ExternallyAnchoredCheckpoint {
    pub fn checkpoint(&self) -> ConsensusAdmissionCheckpoint {
        self.checkpoint
    }
    pub fn verifier_id(&self) -> Bytes32 {
        self.verifier_id
    }
    pub fn external_receipt(&self) -> Bytes32 {
        self.external_receipt
    }
}

pub fn verify_external_checkpoint<V: ExternalCheckpointVerifier>(
    verifier: &V,
    verifier_id: Bytes32,
    checkpoint: ConsensusAdmissionCheckpoint,
    proof: &V::Proof,
) -> Result<ExternallyAnchoredCheckpoint, GateError> {
    if verifier_id == [0; 32] || checkpoint.journal_len == 0 || checkpoint.journal_head == [0; 32] {
        return Err(GateError::InvalidExternalCheckpoint);
    }
    let external_receipt = verifier
        .verify_checkpoint(&checkpoint, proof)
        .map_err(|error| GateError::ExternalCheckpoint(error.to_string()))?;
    if external_receipt == [0; 32] {
        return Err(GateError::InvalidExternalCheckpoint);
    }
    let mut hash = Sha256::new();
    hash.update(EXTERNAL_CHECKPOINT_DOMAIN);
    hash.update(checkpoint.journal_len.to_be_bytes());
    hash.update(checkpoint.journal_head);
    hash.update(checkpoint.observed_time_floor.to_be_bytes());
    hash.update(verifier_id);
    hash.update(external_receipt);
    let seal = hash.finalize().into();
    Ok(ExternallyAnchoredCheckpoint {
        checkpoint,
        verifier_id,
        external_receipt,
        seal,
    })
}

/// Sealed consensus authority. It binds verified account evidence and an
/// externally anchored reservation to one bounded game-local intent. It never
/// carries governance weight or a Rust-authored score/loot decision.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ConsensusHoldingCapability {
    capability: HoldingCapability,
    reservation: ConsensusPrivilegeReservation,
    evidence_grade: ConsensusEvidenceGrade,
    token_account: Bytes32,
    token_program: Bytes32,
    evidence_digest: Bytes32,
    anchor_epoch: u64,
    anchor_stake_table_root: Bytes32,
    require_poh: bool,
    external_checkpoint: ExternallyAnchoredCheckpoint,
}

impl ConsensusHoldingCapability {
    pub fn receipt_id(&self) -> Bytes32 {
        self.capability.receipt_id()
    }
    pub fn challenge_id(&self) -> Bytes32 {
        self.capability.challenge_id()
    }
    pub fn trust(&self) -> TrustTier {
        self.capability.trust()
    }
    pub fn wallet(&self) -> Bytes32 {
        self.capability.wallet()
    }
    pub fn player(&self) -> Bytes32 {
        self.capability.player()
    }
    pub fn player_cell(&self) -> Bytes32 {
        self.capability.player_cell()
    }
    pub fn federation_id(&self) -> Bytes32 {
        self.capability.federation_id()
    }
    pub fn origin(&self) -> &str {
        self.capability.origin()
    }
    pub fn domain(&self) -> &str {
        self.capability.domain()
    }
    pub fn cluster(&self) -> &str {
        self.capability.cluster()
    }
    pub fn mint(&self) -> Bytes32 {
        self.capability.mint()
    }
    pub fn snapshot_slot(&self) -> u64 {
        self.capability.snapshot_slot()
    }
    pub fn issued_at(&self) -> u64 {
        self.capability.issued_at()
    }
    pub fn expires_at(&self) -> u64 {
        self.capability.expires_at()
    }
    pub fn reservation(&self) -> &ConsensusPrivilegeReservation {
        &self.reservation
    }
    pub fn evidence_grade(&self) -> ConsensusEvidenceGrade {
        self.evidence_grade
    }
    pub fn token_account(&self) -> Bytes32 {
        self.token_account
    }
    pub fn token_program(&self) -> Bytes32 {
        self.token_program
    }
    pub fn evidence_digest(&self) -> Bytes32 {
        self.evidence_digest
    }
    pub fn anchor_epoch(&self) -> u64 {
        self.anchor_epoch
    }
    pub fn anchor_stake_table_root(&self) -> Bytes32 {
        self.anchor_stake_table_root
    }
    pub fn require_poh(&self) -> bool {
        self.require_poh
    }
    pub fn external_checkpoint(&self) -> &ExternallyAnchoredCheckpoint {
        &self.external_checkpoint
    }
    pub fn is_governance_weight_bearing(&self) -> bool {
        false
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum TrustTier {
    BetaRpcAttested,
    ConsensusVerified,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct HoldingCapability {
    receipt_id: Bytes32,
    challenge_id: Bytes32,
    trust: TrustTier,
    wallet: Bytes32,
    player: Bytes32,
    player_cell: Bytes32,
    federation_id: Bytes32,
    origin: String,
    domain: String,
    cluster: String,
    mint: Bytes32,
    snapshot_slot: u64,
    issued_at: u64,
    expires_at: u64,
}

impl HoldingCapability {
    pub fn receipt_id(&self) -> Bytes32 {
        self.receipt_id
    }
    pub fn challenge_id(&self) -> Bytes32 {
        self.challenge_id
    }
    pub fn trust(&self) -> TrustTier {
        self.trust
    }
    pub fn wallet(&self) -> Bytes32 {
        self.wallet
    }
    /// Exact Dregg signing public key bound by the Solana wallet signature.
    pub fn player(&self) -> Bytes32 {
        self.player
    }
    /// Canonical Dregg player cell for [`Self::player`].
    pub fn player_cell(&self) -> Bytes32 {
        self.player_cell
    }
    pub fn federation_id(&self) -> Bytes32 {
        self.federation_id
    }
    pub fn origin(&self) -> &str {
        &self.origin
    }
    pub fn domain(&self) -> &str {
        &self.domain
    }
    pub fn cluster(&self) -> &str {
        &self.cluster
    }
    pub fn mint(&self) -> Bytes32 {
        self.mint
    }
    pub fn snapshot_slot(&self) -> u64 {
        self.snapshot_slot
    }
    pub fn issued_at(&self) -> u64 {
        self.issued_at
    }
    pub fn expires_at(&self) -> u64 {
        self.expires_at
    }
    pub fn is_governance_weight_bearing(&self) -> bool {
        false
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CapabilityUse {
    Consumed,
    Unknown,
    Replay,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ChallengeIssue {
    Issued,
    Replay,
    CapacityExceeded,
}

/// Result of the single durable transition that spends a challenge and records
/// the capability it authorizes. Keeping this one store operation prevents a
/// crash from burning a valid challenge between two otherwise-atomic writes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CapabilityIssue {
    Issued,
    UnknownChallenge,
    ChallengeReplay,
    ChallengeMismatch,
    CapabilityCollision,
    CapacityExceeded,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ConsensusReservationIssue {
    Issued(ConsensusReservationReceipt),
    ExistingExact(ConsensusReservationReceipt),
    UnknownChallenge,
    ChallengeUnavailable,
    Conflict,
    NullifierConflict,
    CapacityExceeded,
    ClockRollback,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ConsensusCapabilityIssue {
    Issued(ConsensusHoldingCapability),
    ExistingExact(ConsensusHoldingCapability),
    UnknownReservation,
    ReservationMismatch,
    Conflict,
    CapacityExceeded,
    ClockRollback,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CapabilityStatus {
    Unknown,
    Active(HoldingCapability),
    Expired(HoldingCapability),
    Consumed(HoldingCapability),
}

/// Durable replay boundary. Production implementations must make each `*_once`
/// operation atomic and survive process restart; otherwise nonce replay reopens
/// after every deploy. In particular, [`Self::issue_capability_once`] is the
/// indivisible challenge-spend + capability-insert transition.
pub trait AdmissionStore {
    type Error: std::fmt::Display;
    fn insert_challenge_once(
        &mut self,
        nonce: Bytes32,
        challenge: Challenge,
    ) -> Result<ChallengeIssue, Self::Error>;
    fn challenge(&self, id: &Bytes32) -> Result<Option<Challenge>, Self::Error>;
    fn challenge_consumed(&self, id: &Bytes32) -> Result<bool, Self::Error>;
    fn issue_capability_once(
        &mut self,
        challenge_id: Bytes32,
        capability: HoldingCapability,
    ) -> Result<CapabilityIssue, Self::Error>;
    fn capability(&self, id: &Bytes32) -> Result<Option<HoldingCapability>, Self::Error>;
    fn capability_consumed(&self, id: &Bytes32) -> Result<bool, Self::Error>;
    fn consume_capability_once(&mut self, id: Bytes32) -> Result<CapabilityUse, Self::Error>;
    fn consensus_reservation(
        &self,
        id: &Bytes32,
    ) -> Result<Option<ConsensusReservationReceipt>, Self::Error>;
    fn reserve_consensus_intent_once(
        &mut self,
        challenge_id: Bytes32,
        reservation: ConsensusPrivilegeReservation,
        observed_now: u64,
    ) -> Result<ConsensusReservationIssue, Self::Error>;
    fn consensus_capability(
        &self,
        id: &Bytes32,
    ) -> Result<Option<ConsensusHoldingCapability>, Self::Error>;
    fn issue_consensus_capability_once(
        &mut self,
        reservation_id: Bytes32,
        capability: ConsensusHoldingCapability,
        observed_now: u64,
    ) -> Result<ConsensusCapabilityIssue, Self::Error>;
    fn consensus_observed_time_floor(&self) -> Result<u64, Self::Error>;
}

#[derive(Default)]
pub struct InMemoryAdmissionStore {
    issued: HashMap<Bytes32, Challenge>,
    used_nonces: HashSet<Bytes32>,
    spent_challenges: HashSet<Bytes32>,
    issued_capabilities: HashMap<Bytes32, HoldingCapability>,
    spent_capabilities: HashSet<Bytes32>,
    consensus_reservations: HashMap<Bytes32, ConsensusReservationReceipt>,
    consensus_reservation_by_challenge: HashMap<Bytes32, Bytes32>,
    consensus_reservation_by_nullifier: HashMap<Bytes32, Bytes32>,
    consensus_capabilities: HashMap<Bytes32, ConsensusHoldingCapability>,
    consensus_capability_by_reservation: HashMap<Bytes32, Bytes32>,
    consensus_journal_len: u64,
    consensus_journal_head: Bytes32,
    consensus_time_floor: u64,
}

impl AdmissionStore for InMemoryAdmissionStore {
    type Error = std::convert::Infallible;
    fn insert_challenge_once(
        &mut self,
        nonce: Bytes32,
        challenge: Challenge,
    ) -> Result<ChallengeIssue, Self::Error> {
        if self.used_nonces.contains(&nonce) || self.issued.contains_key(&challenge.id) {
            return Ok(ChallengeIssue::Replay);
        }
        self.used_nonces.insert(nonce);
        self.issued.insert(challenge.id, challenge);
        Ok(ChallengeIssue::Issued)
    }
    fn challenge(&self, id: &Bytes32) -> Result<Option<Challenge>, Self::Error> {
        Ok(self.issued.get(id).cloned())
    }
    fn challenge_consumed(&self, id: &Bytes32) -> Result<bool, Self::Error> {
        Ok(self.spent_challenges.contains(id))
    }
    fn issue_capability_once(
        &mut self,
        challenge_id: Bytes32,
        capability: HoldingCapability,
    ) -> Result<CapabilityIssue, Self::Error> {
        if !self.issued.contains_key(&challenge_id) {
            return Ok(CapabilityIssue::UnknownChallenge);
        }
        if self.spent_challenges.contains(&challenge_id)
            || self
                .consensus_reservation_by_challenge
                .contains_key(&challenge_id)
        {
            return Ok(CapabilityIssue::ChallengeReplay);
        }
        if capability.challenge_id != challenge_id {
            return Ok(CapabilityIssue::ChallengeMismatch);
        }
        let id = capability.receipt_id;
        if self.issued_capabilities.contains_key(&id) {
            return Ok(CapabilityIssue::CapabilityCollision);
        }
        self.spent_challenges.insert(challenge_id);
        self.issued_capabilities.insert(id, capability);
        Ok(CapabilityIssue::Issued)
    }
    fn capability(&self, id: &Bytes32) -> Result<Option<HoldingCapability>, Self::Error> {
        Ok(self.issued_capabilities.get(id).cloned())
    }
    fn capability_consumed(&self, id: &Bytes32) -> Result<bool, Self::Error> {
        Ok(self.spent_capabilities.contains(id))
    }
    fn consume_capability_once(&mut self, id: Bytes32) -> Result<CapabilityUse, Self::Error> {
        if self.spent_capabilities.contains(&id) {
            return Ok(CapabilityUse::Replay);
        }
        if !self.issued_capabilities.contains_key(&id) {
            return Ok(CapabilityUse::Unknown);
        }
        self.spent_capabilities.insert(id);
        Ok(CapabilityUse::Consumed)
    }

    fn consensus_reservation(
        &self,
        id: &Bytes32,
    ) -> Result<Option<ConsensusReservationReceipt>, Self::Error> {
        Ok(self.consensus_reservations.get(id).cloned())
    }

    fn reserve_consensus_intent_once(
        &mut self,
        challenge_id: Bytes32,
        reservation: ConsensusPrivilegeReservation,
        observed_now: u64,
    ) -> Result<ConsensusReservationIssue, Self::Error> {
        if observed_now < self.consensus_time_floor {
            return Ok(ConsensusReservationIssue::ClockRollback);
        }
        self.consensus_time_floor = observed_now;
        if let Some(existing) = self.consensus_reservations.get(&reservation.reservation_id) {
            return Ok(
                if consensus_reservation_static_eq(&existing.reservation, &reservation) {
                    ConsensusReservationIssue::ExistingExact(existing.clone())
                } else {
                    ConsensusReservationIssue::Conflict
                },
            );
        }
        if !self.issued.contains_key(&challenge_id) {
            return Ok(ConsensusReservationIssue::UnknownChallenge);
        }
        if self.spent_challenges.contains(&challenge_id)
            || self
                .consensus_reservation_by_challenge
                .contains_key(&challenge_id)
        {
            return Ok(ConsensusReservationIssue::ChallengeUnavailable);
        }
        if self
            .consensus_reservation_by_nullifier
            .contains_key(&reservation.privilege_nullifier)
        {
            return Ok(ConsensusReservationIssue::NullifierConflict);
        }
        let event_digest = consensus_reservation_record_digest(
            self.consensus_journal_len,
            self.consensus_journal_head,
            &reservation,
        );
        self.consensus_journal_len += 1;
        self.consensus_journal_head = event_digest;
        self.consensus_time_floor = self.consensus_time_floor.max(observed_now);
        let receipt = ConsensusReservationReceipt {
            reservation: reservation.clone(),
            checkpoint: ConsensusAdmissionCheckpoint {
                journal_len: self.consensus_journal_len,
                journal_head: self.consensus_journal_head,
                observed_time_floor: self.consensus_time_floor,
            },
        };
        self.consensus_reservation_by_challenge
            .insert(challenge_id, reservation.reservation_id);
        self.consensus_reservation_by_nullifier
            .insert(reservation.privilege_nullifier, reservation.reservation_id);
        self.consensus_reservations
            .insert(reservation.reservation_id, receipt.clone());
        Ok(ConsensusReservationIssue::Issued(receipt))
    }

    fn consensus_capability(
        &self,
        id: &Bytes32,
    ) -> Result<Option<ConsensusHoldingCapability>, Self::Error> {
        Ok(self.consensus_capabilities.get(id).cloned())
    }

    fn issue_consensus_capability_once(
        &mut self,
        reservation_id: Bytes32,
        capability: ConsensusHoldingCapability,
        observed_now: u64,
    ) -> Result<ConsensusCapabilityIssue, Self::Error> {
        if observed_now < self.consensus_time_floor {
            return Ok(ConsensusCapabilityIssue::ClockRollback);
        }
        self.consensus_time_floor = observed_now;
        let Some(reservation) = self.consensus_reservations.get(&reservation_id) else {
            return Ok(ConsensusCapabilityIssue::UnknownReservation);
        };
        if capability.reservation != reservation.reservation {
            return Ok(ConsensusCapabilityIssue::ReservationMismatch);
        }
        if let Some(existing_id) = self
            .consensus_capability_by_reservation
            .get(&reservation_id)
        {
            let existing = self
                .consensus_capabilities
                .get(existing_id)
                .expect("indexed capability");
            return Ok(if consensus_capability_static_eq(existing, &capability) {
                ConsensusCapabilityIssue::ExistingExact(existing.clone())
            } else {
                ConsensusCapabilityIssue::Conflict
            });
        }
        self.consensus_capability_by_reservation
            .insert(reservation_id, capability.receipt_id());
        self.consensus_capabilities
            .insert(capability.receipt_id(), capability.clone());
        Ok(ConsensusCapabilityIssue::Issued(capability))
    }

    fn consensus_observed_time_floor(&self) -> Result<u64, Self::Error> {
        Ok(self.consensus_time_floor)
    }
}

pub struct Gate<S: AdmissionStore = InMemoryAdmissionStore> {
    store: S,
}

impl Gate<InMemoryAdmissionStore> {
    /// Test/dev store. A production server must use [`Gate::with_store`] with a
    /// durable atomic implementation.
    pub fn new() -> Self {
        Self {
            store: InMemoryAdmissionStore::default(),
        }
    }
}

impl Default for Gate<InMemoryAdmissionStore> {
    fn default() -> Self {
        Self::new()
    }
}

impl<S: AdmissionStore> Gate<S> {
    pub fn with_store(store: S) -> Self {
        Self { store }
    }

    /// Reload the server-issued canonical challenge. HTTP adapters should accept
    /// only an id from the client and use this value, never deserialize a
    /// client-supplied challenge transcript.
    pub fn issued_challenge(&self, id: &Bytes32) -> Result<Option<Challenge>, GateError> {
        self.store
            .challenge(id)
            .map_err(|e| GateError::Store(e.to_string()))
    }

    pub fn capability_status(&self, id: &Bytes32, now: u64) -> Result<CapabilityStatus, GateError> {
        let Some(capability) = self
            .store
            .capability(id)
            .map_err(|e| GateError::Store(e.to_string()))?
        else {
            return Ok(CapabilityStatus::Unknown);
        };
        if self
            .store
            .capability_consumed(id)
            .map_err(|e| GateError::Store(e.to_string()))?
        {
            return Ok(CapabilityStatus::Consumed(capability));
        }
        if now < capability.issued_at || now > capability.expires_at {
            return Ok(CapabilityStatus::Expired(capability));
        }
        Ok(CapabilityStatus::Active(capability))
    }

    /// Cheap canonical checks that must pass before an HTTP adapter performs a
    /// live holding lookup. [`Self::admit_beta`] repeats this preflight before
    /// its atomic state transition, so callers cannot turn preflight into an
    /// authorization bypass or a time-of-check/time-of-use assumption.
    pub fn preflight_beta(
        &self,
        config: &GateConfig,
        presented: &Challenge,
        binding: &OwnerBinding,
        now: u64,
    ) -> Result<(), GateError> {
        let issued = self
            .store
            .challenge(&presented.id)
            .map_err(|e| GateError::Store(e.to_string()))?
            .ok_or(GateError::UnknownChallenge)?;
        if &issued != presented {
            return Err(GateError::ChallengeMutation);
        }
        config.validate()?;
        if presented.federation_id != config.federation_id
            || presented.origin != config.origin
            || presented.domain != config.domain
            || presented.cluster != config.cluster
            || presented.genesis_hash != config.genesis_hash
            || presented.rpc_endpoint_id != config.rpc_endpoint_id
            || presented.mint != config.mint
            || presented.token_program != config.token_program
            || presented.minimum_raw_balance != config.minimum_raw_balance
            || presented.capability_ttl_secs != config.capability_ttl_secs
        {
            return Err(GateError::ChallengeMutation);
        }
        if self
            .store
            .challenge_consumed(&presented.id)
            .map_err(|e| GateError::Store(e.to_string()))?
        {
            return Err(GateError::ChallengeReplay);
        }
        if now < presented.issued_at || now > presented.expires_at {
            return Err(GateError::ChallengeExpired);
        }
        let wallet_key = VerifyingKey::from_bytes(&presented.wallet)
            .map_err(|_| GateError::BadWalletSignature)?;
        let wallet_signature = ed25519_dalek::Signature::from_bytes(&binding.sig);
        if presented.player_cell != canonical_player_cell(&presented.player)
            || binding.voter != presented.player
            || wallet_key
                .verify_strict(&presented.signing_message(), &wallet_signature)
                .is_err()
        {
            return Err(GateError::BadWalletSignature);
        }
        Ok(())
    }

    pub fn issue(
        &mut self,
        config: &GateConfig,
        wallet: Bytes32,
        player: Bytes32,
        nonce: Bytes32,
        min_context_slot: u64,
        now: u64,
    ) -> Result<Challenge, GateError> {
        config.validate()?;
        if nonce == [0; 32] {
            return Err(GateError::WeakNonce);
        }
        let expires_at = now
            .checked_add(config.challenge_ttl_secs)
            .ok_or(GateError::TimeOverflow)?;
        if player == [0; 32] || VerifyingKey::from_bytes(&player).is_err() {
            return Err(GateError::InvalidPlayer);
        }
        let player_cell = canonical_player_cell(&player);
        let transcript = challenge_transcript(
            config,
            &wallet,
            &player,
            &player_cell,
            &nonce,
            min_context_slot,
            now,
            expires_at,
        );
        let mut id_hasher = Sha256::new();
        id_hasher.update(CHALLENGE_DOMAIN);
        id_hasher.update(&transcript);
        let id: Bytes32 = id_hasher.finalize().into();
        let challenge = Challenge {
            id,
            player,
            player_cell,
            wallet,
            nonce,
            federation_id: config.federation_id,
            origin: config.origin.clone(),
            domain: config.domain.clone(),
            cluster: config.cluster.clone(),
            genesis_hash: config.genesis_hash,
            rpc_endpoint_id: config.rpc_endpoint_id,
            mint: config.mint,
            token_program: config.token_program,
            minimum_raw_balance: config.minimum_raw_balance,
            min_context_slot,
            issued_at: now,
            expires_at,
            capability_ttl_secs: config.capability_ttl_secs,
        };
        match self
            .store
            .insert_challenge_once(nonce, challenge.clone())
            .map_err(|e| GateError::Store(e.to_string()))?
        {
            ChallengeIssue::Issued => {}
            ChallengeIssue::Replay => return Err(GateError::NonceAlreadyIssued),
            ChallengeIssue::CapacityExceeded => return Err(GateError::AdmissionCapacity),
        }
        Ok(challenge)
    }

    pub fn admit_beta(
        &mut self,
        config: &GateConfig,
        presented: &Challenge,
        binding: &OwnerBinding,
        observation: RpcBetaObservation,
        now: u64,
    ) -> Result<HoldingCapability, GateError> {
        self.preflight_beta(config, presented, binding, now)?;
        if observation.endpoint_id != config.rpc_endpoint_id
            || observation.wallet != presented.wallet
            || observation.mint != config.mint
            || observation.amount < config.minimum_raw_balance
            || observation.slot < presented.min_context_slot
        {
            return Err(GateError::ObservationMismatch);
        }
        let expires_at = now
            .checked_add(presented.capability_ttl_secs)
            .ok_or(GateError::TimeOverflow)?;
        let receipt_id = receipt_id(presented, &observation, now, expires_at);
        let capability = HoldingCapability {
            receipt_id,
            challenge_id: presented.id,
            trust: TrustTier::BetaRpcAttested,
            wallet: presented.wallet,
            player: presented.player,
            player_cell: presented.player_cell,
            federation_id: presented.federation_id,
            origin: presented.origin.clone(),
            domain: presented.domain.clone(),
            cluster: presented.cluster.clone(),
            mint: presented.mint,
            snapshot_slot: observation.slot,
            issued_at: now,
            expires_at,
        };
        match self
            .store
            .issue_capability_once(presented.id, capability.clone())
            .map_err(|e| GateError::Store(e.to_string()))?
        {
            CapabilityIssue::Issued => {}
            CapabilityIssue::UnknownChallenge => return Err(GateError::UnknownChallenge),
            CapabilityIssue::ChallengeReplay => return Err(GateError::ChallengeReplay),
            CapabilityIssue::ChallengeMismatch => return Err(GateError::ChallengeMutation),
            CapabilityIssue::CapabilityCollision => {
                return Err(GateError::CapabilityIdCollision);
            }
            CapabilityIssue::CapacityExceeded => return Err(GateError::AdmissionCapacity),
        }
        Ok(capability)
    }

    /// Reserve one exact bounded intent before the expensive consensus path.
    /// An exact retry returns the original receipt; a different player,
    /// beneficiary, or action for the same wallet/event/privilege nullifier is
    /// refused by the store.
    pub fn reserve_consensus_intent(
        &mut self,
        config: &GateConfig,
        presented: &Challenge,
        binding: &OwnerBinding,
        intent: ConsensusPrivilegeIntent,
        now: u64,
    ) -> Result<ConsensusReservationReceipt, GateError> {
        self.preflight_beta(config, presented, binding, now)?;
        let reservation_id = consensus_reservation_id(presented, &intent);
        let privilege_nullifier = consensus_privilege_nullifier(
            presented.wallet,
            presented.federation_id,
            intent.deployment_id,
            intent.event_id,
            intent.privilege_id,
        );
        let expires_at = now
            .checked_add(CONSENSUS_RESERVATION_TTL_SECS)
            .ok_or(GateError::TimeOverflow)?;
        let reservation = ConsensusPrivilegeReservation {
            reservation_id,
            challenge_id: presented.id,
            wallet: presented.wallet,
            player: presented.player,
            player_cell: presented.player_cell,
            federation_id: presented.federation_id,
            intent,
            privilege_nullifier,
            issued_at: now,
            expires_at,
        };
        match self
            .store
            .reserve_consensus_intent_once(presented.id, reservation, now)
            .map_err(|error| GateError::Store(error.to_string()))?
        {
            ConsensusReservationIssue::Issued(receipt)
            | ConsensusReservationIssue::ExistingExact(receipt) => {
                if now < receipt.reservation.issued_at || now > receipt.reservation.expires_at {
                    return Err(GateError::ConsensusReservationExpired);
                }
                Ok(receipt)
            }
            ConsensusReservationIssue::UnknownChallenge => Err(GateError::UnknownChallenge),
            ConsensusReservationIssue::ChallengeUnavailable => Err(GateError::ChallengeReplay),
            ConsensusReservationIssue::Conflict => Err(GateError::ConsensusReservationConflict),
            ConsensusReservationIssue::NullifierConflict => {
                Err(GateError::PrivilegeNullifierConflict)
            }
            ConsensusReservationIssue::CapacityExceeded => Err(GateError::AdmissionCapacity),
            ConsensusReservationIssue::ClockRollback => Err(GateError::ClockRollback),
        }
    }

    /// Finish a reserved intent with independently anchored Solana evidence.
    /// Neither a beta observation nor a caller-constructed `ProvenHolding` can
    /// enter this method: only `verify_consensus_source` constructs its evidence.
    pub fn admit_consensus(
        &mut self,
        config: &GateConfig,
        reservation_receipt: &ConsensusReservationReceipt,
        evidence: VerifiedConsensusHolding,
        external_checkpoint: ExternallyAnchoredCheckpoint,
        now: u64,
    ) -> Result<ConsensusHoldingCapability, GateError> {
        config.validate()?;
        let stored = self
            .store
            .consensus_reservation(&reservation_receipt.reservation.reservation_id)
            .map_err(|error| GateError::Store(error.to_string()))?
            .ok_or(GateError::UnknownConsensusReservation)?;
        if &stored != reservation_receipt {
            return Err(GateError::ConsensusReservationConflict);
        }
        let reservation = &stored.reservation;
        if now < reservation.issued_at || now > reservation.expires_at {
            return Err(GateError::ConsensusReservationExpired);
        }
        if external_checkpoint.checkpoint != stored.checkpoint
            || !external_checkpoint_seal_valid(&external_checkpoint)
        {
            return Err(GateError::InvalidExternalCheckpoint);
        }
        if reservation.federation_id != config.federation_id
            || reservation.wallet != evidence.owner()
            || evidence.mint() != config.mint
            || evidence.token_program() != config.token_program
            || evidence.cluster() != config.cluster
            || evidence.genesis_hash() != config.genesis_hash
            || evidence.ingest_source_id() != config.rpc_endpoint_id
            || evidence.amount() < config.minimum_raw_balance
            || evidence.slot()
                < self
                    .store
                    .challenge(&reservation.challenge_id)
                    .map_err(|error| GateError::Store(error.to_string()))?
                    .ok_or(GateError::UnknownChallenge)?
                    .min_context_slot
        {
            return Err(GateError::ConsensusEvidenceMismatch);
        }
        let expires_at = now
            .checked_add(config.capability_ttl_secs)
            .ok_or(GateError::TimeOverflow)?
            .min(reservation.expires_at);
        if expires_at < now {
            return Err(GateError::ConsensusReservationExpired);
        }
        let receipt_id = consensus_capability_id(reservation, &evidence, &external_checkpoint);
        let capability = ConsensusHoldingCapability {
            capability: HoldingCapability {
                receipt_id,
                challenge_id: reservation.challenge_id,
                trust: TrustTier::ConsensusVerified,
                wallet: reservation.wallet,
                player: reservation.player,
                player_cell: reservation.player_cell,
                federation_id: reservation.federation_id,
                origin: config.origin.clone(),
                domain: config.domain.clone(),
                cluster: config.cluster.clone(),
                mint: config.mint,
                snapshot_slot: evidence.slot(),
                issued_at: now,
                expires_at,
            },
            reservation: reservation.clone(),
            evidence_grade: ConsensusEvidenceGrade::IndependentlyAnchoredFinalizedAccount,
            token_account: evidence.token_account(),
            token_program: evidence.token_program(),
            evidence_digest: evidence.evidence_digest(),
            anchor_epoch: evidence.anchor_epoch(),
            anchor_stake_table_root: evidence.anchor_stake_table_root(),
            require_poh: evidence.require_poh(),
            external_checkpoint,
        };
        match self
            .store
            .issue_consensus_capability_once(reservation.reservation_id, capability, now)
            .map_err(|error| GateError::Store(error.to_string()))?
        {
            ConsensusCapabilityIssue::Issued(capability)
            | ConsensusCapabilityIssue::ExistingExact(capability) => {
                if now < capability.issued_at() || now > capability.expires_at() {
                    return Err(GateError::CapabilityExpired);
                }
                Ok(capability)
            }
            ConsensusCapabilityIssue::UnknownReservation => {
                Err(GateError::UnknownConsensusReservation)
            }
            ConsensusCapabilityIssue::ReservationMismatch | ConsensusCapabilityIssue::Conflict => {
                Err(GateError::ConsensusCapabilityConflict)
            }
            ConsensusCapabilityIssue::CapacityExceeded => Err(GateError::AdmissionCapacity),
            ConsensusCapabilityIssue::ClockRollback => Err(GateError::ClockRollback),
        }
    }

    pub fn consensus_capability(
        &self,
        id: &Bytes32,
    ) -> Result<Option<ConsensusHoldingCapability>, GateError> {
        self.store
            .consensus_capability(id)
            .map_err(|error| GateError::Store(error.to_string()))
    }

    pub fn consensus_observed_time_floor(&self) -> Result<u64, GateError> {
        self.store
            .consensus_observed_time_floor()
            .map_err(|error| GateError::Store(error.to_string()))
    }

    pub fn consume(&mut self, capability: &HoldingCapability, now: u64) -> Result<(), GateError> {
        let issued = self
            .store
            .capability(&capability.receipt_id)
            .map_err(|e| GateError::Store(e.to_string()))?
            .ok_or(GateError::ForgedCapability)?;
        if &issued != capability {
            return Err(GateError::ForgedCapability);
        }
        if now < capability.issued_at || now > capability.expires_at {
            return Err(GateError::CapabilityExpired);
        }
        if !self
            .store
            .challenge_consumed(&capability.challenge_id)
            .map_err(|e| GateError::Store(e.to_string()))?
        {
            return Err(GateError::ForgedCapability);
        }
        match self
            .store
            .consume_capability_once(capability.receipt_id)
            .map_err(|e| GateError::Store(e.to_string()))?
        {
            CapabilityUse::Consumed => Ok(()),
            CapabilityUse::Unknown => Err(GateError::ForgedCapability),
            CapabilityUse::Replay => Err(GateError::CapabilityReplay),
        }
    }
}

fn challenge_transcript(
    c: &GateConfig,
    wallet: &Bytes32,
    player: &Bytes32,
    player_cell: &Bytes32,
    nonce: &Bytes32,
    min_slot: u64,
    issued: u64,
    expires: u64,
) -> Vec<u8> {
    let mut out = Vec::new();
    put(&mut out, CHALLENGE_DOMAIN);
    put(&mut out, &c.federation_id);
    put(&mut out, c.origin.as_bytes());
    put(&mut out, c.domain.as_bytes());
    put(&mut out, c.cluster.as_bytes());
    put(&mut out, &c.genesis_hash);
    put(&mut out, &c.rpc_endpoint_id);
    put(&mut out, &c.mint);
    put(&mut out, &c.token_program);
    put(&mut out, wallet);
    put(&mut out, player);
    put(&mut out, player_cell);
    put(&mut out, nonce);
    put(&mut out, &c.minimum_raw_balance.to_be_bytes());
    put(&mut out, &min_slot.to_be_bytes());
    put(&mut out, &c.challenge_ttl_secs.to_be_bytes());
    put(&mut out, &c.capability_ttl_secs.to_be_bytes());
    put(&mut out, &issued.to_be_bytes());
    put(&mut out, &expires.to_be_bytes());
    out
}

fn challenge_signing_message(challenge: &Challenge) -> Vec<u8> {
    let mut out = Vec::new();
    put(&mut out, WALLET_CONSENT_DOMAIN);
    put(&mut out, &challenge.id);
    put(&mut out, &challenge.federation_id);
    put(&mut out, challenge.origin.as_bytes());
    put(&mut out, challenge.domain.as_bytes());
    put(&mut out, challenge.cluster.as_bytes());
    put(&mut out, &challenge.genesis_hash);
    put(&mut out, &challenge.rpc_endpoint_id);
    put(&mut out, &challenge.mint);
    put(&mut out, &challenge.token_program);
    put(&mut out, &challenge.wallet);
    put(&mut out, &challenge.player);
    put(&mut out, &challenge.player_cell);
    put(&mut out, &challenge.nonce);
    put(&mut out, &challenge.minimum_raw_balance.to_be_bytes());
    put(&mut out, &challenge.min_context_slot.to_be_bytes());
    put(&mut out, &challenge.issued_at.to_be_bytes());
    put(&mut out, &challenge.expires_at.to_be_bytes());
    put(&mut out, &challenge.capability_ttl_secs.to_be_bytes());
    out
}

fn receipt_id(c: &Challenge, o: &RpcBetaObservation, issued: u64, expires: u64) -> Bytes32 {
    let mut h = Sha256::new();
    h.update(RECEIPT_DOMAIN);
    h.update(c.id);
    h.update(o.endpoint_id);
    h.update(o.wallet);
    h.update(c.player);
    h.update(c.player_cell);
    h.update(o.mint);
    h.update(o.amount.to_be_bytes());
    h.update(o.slot.to_be_bytes());
    for a in &o.token_accounts {
        h.update(a);
    }
    h.update(issued.to_be_bytes());
    h.update(expires.to_be_bytes());
    h.finalize().into()
}

fn consensus_evidence_digest(
    holding: &ProvenHolding,
    config: &GateConfig,
    anchor: &WeakSubjectivityAnchor,
    require_poh: bool,
) -> Bytes32 {
    let mut hash = Sha256::new();
    hash.update(CONSENSUS_EVIDENCE_DOMAIN);
    hash.update(holding.token_account);
    hash.update(holding.owner);
    hash.update(holding.mint);
    hash.update(holding.amount.to_be_bytes());
    hash.update(holding.slot.to_be_bytes());
    hash.update(config.token_program);
    hash.update(config.genesis_hash);
    hash.update(config.rpc_endpoint_id);
    hash.update(anchor.epoch.to_be_bytes());
    hash.update(anchor.stake_table_root);
    hash.update([u8::from(require_poh)]);
    hash.finalize().into()
}

fn consensus_reservation_id(challenge: &Challenge, intent: &ConsensusPrivilegeIntent) -> Bytes32 {
    let mut hash = Sha256::new();
    hash.update(CONSENSUS_RESERVATION_DOMAIN);
    hash.update(challenge.id);
    hash.update(challenge.wallet);
    hash.update(challenge.player);
    hash.update(challenge.player_cell);
    hash.update(challenge.federation_id);
    hash.update(intent.deployment_id);
    hash.update(intent.event_id);
    hash.update(intent.privilege_id);
    hash.update(intent.action_token);
    hash.update(intent.beneficiary);
    hash.update(intent.event_sequence.to_be_bytes());
    hash.update(intent.expires_after_sequence.to_be_bytes());
    hash.finalize().into()
}

fn consensus_privilege_nullifier(
    wallet: Bytes32,
    federation_id: Bytes32,
    deployment_id: Bytes32,
    event_id: Bytes32,
    privilege_id: Bytes32,
) -> Bytes32 {
    let mut hash = Sha256::new();
    hash.update(CONSENSUS_PRIVILEGE_NULLIFIER_DOMAIN);
    hash.update(wallet);
    hash.update(federation_id);
    hash.update(deployment_id);
    hash.update(event_id);
    hash.update(privilege_id);
    hash.finalize().into()
}

fn consensus_reservation_record_digest(
    ordinal: u64,
    previous: Bytes32,
    reservation: &ConsensusPrivilegeReservation,
) -> Bytes32 {
    let bytes = postcard::to_stdvec(reservation)
        .expect("consensus reservation is a bounded canonical structure");
    let mut hash = Sha256::new();
    hash.update(CONSENSUS_RESERVATION_DOMAIN);
    hash.update(ordinal.to_be_bytes());
    hash.update(previous);
    hash.update((bytes.len() as u64).to_be_bytes());
    hash.update(bytes);
    hash.finalize().into()
}

fn consensus_capability_id(
    reservation: &ConsensusPrivilegeReservation,
    evidence: &VerifiedConsensusHolding,
    external: &ExternallyAnchoredCheckpoint,
) -> Bytes32 {
    let mut hash = Sha256::new();
    hash.update(CONSENSUS_CAPABILITY_DOMAIN);
    hash.update(reservation.reservation_id);
    hash.update(reservation.privilege_nullifier);
    hash.update(evidence.evidence_digest);
    hash.update(external.seal);
    hash.finalize().into()
}

fn external_checkpoint_seal_valid(external: &ExternallyAnchoredCheckpoint) -> bool {
    let mut hash = Sha256::new();
    hash.update(EXTERNAL_CHECKPOINT_DOMAIN);
    hash.update(external.checkpoint.journal_len.to_be_bytes());
    hash.update(external.checkpoint.journal_head);
    hash.update(external.checkpoint.observed_time_floor.to_be_bytes());
    hash.update(external.verifier_id);
    hash.update(external.external_receipt);
    Bytes32::from(hash.finalize()) == external.seal
}

fn consensus_reservation_static_eq(
    left: &ConsensusPrivilegeReservation,
    right: &ConsensusPrivilegeReservation,
) -> bool {
    left.reservation_id == right.reservation_id
        && left.challenge_id == right.challenge_id
        && left.wallet == right.wallet
        && left.player == right.player
        && left.player_cell == right.player_cell
        && left.federation_id == right.federation_id
        && left.intent == right.intent
        && left.privilege_nullifier == right.privilege_nullifier
}

fn consensus_capability_static_eq(
    left: &ConsensusHoldingCapability,
    right: &ConsensusHoldingCapability,
) -> bool {
    left.receipt_id() == right.receipt_id()
        && consensus_reservation_static_eq(&left.reservation, &right.reservation)
        && left.evidence_grade == right.evidence_grade
        && left.token_account == right.token_account
        && left.token_program == right.token_program
        && left.evidence_digest == right.evidence_digest
        && left.anchor_epoch == right.anchor_epoch
        && left.anchor_stake_table_root == right.anchor_stake_table_root
        && left.require_poh == right.require_poh
        && left.external_checkpoint == right.external_checkpoint
}

/// Exact player-cell derivation shared with the SDK's Galley carrier.
///
/// Keeping this in the gate makes a persisted capability self-authenticating:
/// a caller cannot ask a wallet to bind one Dregg signer while later naming a
/// different player cell.
pub fn canonical_player_cell(player: &Bytes32) -> Bytes32 {
    dregg_types::CellId::derive_raw(player, blake3::hash(b"default").as_bytes()).0
}

fn put(out: &mut Vec<u8>, bytes: &[u8]) {
    out.extend_from_slice(&(bytes.len() as u32).to_be_bytes());
    out.extend_from_slice(bytes);
}

pub fn decode_pubkey(text: &str) -> Result<Bytes32, GateError> {
    let bytes = bs58::decode(text)
        .into_vec()
        .map_err(|_| GateError::BadBase58)?;
    bytes.try_into().map_err(|_| GateError::BadPubkeyLength)
}

pub fn encode_pubkey(key: &Bytes32) -> String {
    bs58::encode(key).into_string()
}

#[derive(Debug, thiserror::Error, PartialEq, Eq)]
pub enum GateError {
    #[error("invalid gate configuration")]
    InvalidConfiguration,
    #[error("bad base58")]
    BadBase58,
    #[error("pubkey is not 32 bytes")]
    BadPubkeyLength,
    #[error("nonce must be a nonzero server CSPRNG value")]
    WeakNonce,
    #[error("Dregg player public key must be nonzero")]
    InvalidPlayer,
    #[error("nonce was already issued")]
    NonceAlreadyIssued,
    #[error("time arithmetic overflow")]
    TimeOverflow,
    #[error("unknown challenge")]
    UnknownChallenge,
    #[error("challenge was mutated")]
    ChallengeMutation,
    #[error("challenge already consumed")]
    ChallengeReplay,
    #[error("challenge expired or not yet valid")]
    ChallengeExpired,
    #[error("wallet signature is invalid")]
    BadWalletSignature,
    #[error("wrong RPC endpoint")]
    WrongRpcEndpoint,
    #[error("wrong Solana cluster/genesis")]
    WrongCluster,
    #[error("RPC read is not finalized")]
    NotFinalized,
    #[error("RPC context slot is stale")]
    StaleSlot,
    #[error("RPC account set mixes slots")]
    MixedSlots,
    #[error("account is not owned by configured SPL Token program")]
    WrongTokenProgram,
    #[error("duplicate token account")]
    DuplicateTokenAccount,
    #[error("malformed SPL token account")]
    MalformedTokenAccount,
    #[error("wrong mint")]
    WrongMint,
    #[error("wrong token owner")]
    WrongOwner,
    #[error("balance sum overflow")]
    BalanceOverflow,
    #[error("insufficient DREGG balance")]
    InsufficientBalance,
    #[error("holding observation does not match challenge/config")]
    ObservationMismatch,
    #[error("server RPC source failed: {0}")]
    RpcSource(String),
    #[error("durable admission store failed: {0}")]
    Store(String),
    #[error("capability expired")]
    CapabilityExpired,
    #[error("capability receipt id collided with an issued receipt")]
    CapabilityIdCollision,
    #[error("holding admission capacity is temporarily exhausted")]
    AdmissionCapacity,
    #[error("holder privilege intent is malformed or unbounded")]
    InvalidPrivilegeIntent,
    #[error("consensus reservation is unknown")]
    UnknownConsensusReservation,
    #[error("consensus reservation conflicts with durable authority")]
    ConsensusReservationConflict,
    #[error("wallet already reserved this event privilege under another player or beneficiary")]
    PrivilegeNullifierConflict,
    #[error("consensus reservation expired")]
    ConsensusReservationExpired,
    #[error("consensus holding evidence does not match its reservation/configuration")]
    ConsensusEvidenceMismatch,
    #[error("external admission checkpoint is malformed or does not cover the reservation")]
    InvalidExternalCheckpoint,
    #[error("external admission checkpoint verification failed: {0}")]
    ExternalCheckpoint(String),
    #[error("consensus capability conflicts with durable authority")]
    ConsensusCapabilityConflict,
    #[error("authority clock moved behind its durable observed-time floor")]
    ClockRollback,
    #[error("capability already consumed")]
    CapabilityReplay,
    #[error("capability is not backed by a consumed challenge")]
    ForgedCapability,
}

#[derive(Debug, thiserror::Error)]
pub enum ConsensusSourceError {
    #[error("holding gate configuration failed: {0}")]
    Configuration(GateError),
    #[error("holding feed failed: {0}")]
    Feed(String),
    #[error("holding proof failed: {0}")]
    Proof(HoldingProofError),
    #[error("feed did not produce consensus-verified evidence")]
    NotConsensusProven,
    #[error("verified holding does not match the exact DREGG account policy")]
    HoldingPolicyMismatch,
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_bridge::solana_trustless::LockProofTrust;
    use dregg_governance::holding_weight::{GrantError, binding_message, grant_weight};
    use ed25519_dalek::{Signer as _, SigningKey};
    use std::cell::RefCell;

    struct RecordingSource {
        response: RpcAccountSet,
        seen: RefCell<Vec<RpcHoldingQuery>>,
    }

    impl RpcHoldingSource for RecordingSource {
        type Error = std::convert::Infallible;

        fn fetch_token_accounts(
            &self,
            query: &RpcHoldingQuery,
        ) -> Result<RpcAccountSet, Self::Error> {
            self.seen.borrow_mut().push(query.clone());
            Ok(self.response.clone())
        }
    }

    fn config() -> GateConfig {
        GateConfig::path_of_angels_mainnet([7; 32], [8; 32])
    }
    fn account(config: &GateConfig, wallet: Bytes32, amount: u64, slot: u64) -> RpcTokenAccount {
        let mut data = vec![0u8; 165];
        data[..32].copy_from_slice(&config.mint);
        data[32..64].copy_from_slice(&wallet);
        data[64..72].copy_from_slice(&amount.to_le_bytes());
        data[108] = 1;
        RpcTokenAccount {
            address: [44; 32],
            account: FetchedAccount {
                data,
                owner_program: config.token_program,
                slot,
            },
        }
    }
    fn snapshot(
        config: &GateConfig,
        challenge: &Challenge,
        wallet: Bytes32,
        amount: u64,
    ) -> RpcAccountSet {
        RpcAccountSet {
            endpoint_id: config.rpc_endpoint_id,
            genesis_hash: config.genesis_hash,
            commitment: Commitment::Finalized,
            requested_min_context_slot: challenge.min_context_slot,
            context_slot: challenge.min_context_slot + 10,
            accounts: vec![account(
                config,
                wallet,
                amount,
                challenge.min_context_slot + 10,
            )],
        }
    }
    fn binding(key: &SigningKey, challenge: &Challenge) -> OwnerBinding {
        OwnerBinding {
            voter: challenge.player(),
            sig: key.sign(&challenge.signing_message()).to_bytes(),
        }
    }

    fn player() -> Bytes32 {
        SigningKey::from_bytes(&[0x51; 32])
            .verifying_key()
            .to_bytes()
    }

    #[test]
    fn poa_config_is_the_exact_closed_mainnet_dregg_policy() {
        let c = config();
        let dregg = HoldingAssetPolicy::dregg_mainnet();
        assert_eq!(c.mint, *dregg.mint());
        assert_eq!(c.token_program, dregg.program_id());
        assert_eq!(c.mint, decode_pubkey(DREGG_MINT_BASE58).unwrap());
        assert_eq!(
            c.token_program,
            decode_pubkey(DREGG_TOKEN_PROGRAM_BASE58).unwrap()
        );
    }

    #[test]
    fn exact_wallet_rpc_snapshot_mints_one_short_lived_beta_capability() {
        let c = config();
        let key = SigningKey::from_bytes(&[3; 32]);
        let wallet = key.verifying_key().to_bytes();
        let mut gate = Gate::new();
        let challenge = gate.issue(&c, wallet, player(), [9; 32], 1000, 50).unwrap();
        let observed =
            validate_rpc_snapshot(&c, &challenge, &snapshot(&c, &challenge, wallet, 17)).unwrap();
        let cap = gate
            .admit_beta(&c, &challenge, &binding(&key, &challenge), observed, 51)
            .unwrap();
        assert_eq!(cap.trust(), TrustTier::BetaRpcAttested);
        assert_eq!(cap.player(), player());
        assert_eq!(cap.player_cell(), canonical_player_cell(&player()));
        assert!(!cap.is_governance_weight_bearing());
        let mut forged = cap.clone();
        forged.snapshot_slot += 1;
        assert_eq!(gate.consume(&forged, 52), Err(GateError::ForgedCapability));
        assert_eq!(gate.consume(&cap, 52), Ok(()));
        assert_eq!(gate.consume(&cap, 53), Err(GateError::CapabilityReplay));
    }

    #[test]
    fn wallet_binding_commits_the_exact_dregg_player_and_canonical_cell() {
        let c = config();
        let wallet_key = SigningKey::from_bytes(&[3; 32]);
        let wallet = wallet_key.verifying_key().to_bytes();
        let intended_player = player();
        let attacker_player = SigningKey::from_bytes(&[0xA7; 32])
            .verifying_key()
            .to_bytes();
        let mut gate = Gate::new();
        let challenge = gate
            .issue(&c, wallet, intended_player, [9; 32], 1000, 50)
            .unwrap();

        assert_eq!(challenge.player(), intended_player);
        assert_eq!(
            challenge.player_cell(),
            canonical_player_cell(&intended_player)
        );
        let observation =
            validate_rpc_snapshot(&c, &challenge, &snapshot(&c, &challenge, wallet, 1)).unwrap();
        let wrong_player_binding = OwnerBinding {
            voter: attacker_player,
            sig: wallet_key.sign(&challenge.signing_message()).to_bytes(),
        };
        assert_eq!(
            gate.admit_beta(&c, &challenge, &wrong_player_binding, observation, 51,),
            Err(GateError::BadWalletSignature)
        );
    }

    #[test]
    fn wallet_consent_signature_cannot_cross_challenge_nonce_or_expiry() {
        let c = config();
        let wallet_key = SigningKey::from_bytes(&[3; 32]);
        let wallet = wallet_key.verifying_key().to_bytes();
        let mut gate = Gate::new();
        let first = gate.issue(&c, wallet, player(), [9; 32], 1000, 50).unwrap();
        let stale_signature = wallet_key.sign(&first.signing_message()).to_bytes();
        let second = gate
            .issue(&c, wallet, player(), [10; 32], 1000, 51)
            .unwrap();
        let observation =
            validate_rpc_snapshot(&c, &second, &snapshot(&c, &second, wallet, 1)).unwrap();
        assert_eq!(
            gate.admit_beta(
                &c,
                &second,
                &OwnerBinding {
                    voter: player(),
                    sig: stale_signature,
                },
                observation,
                52,
            ),
            Err(GateError::BadWalletSignature)
        );
    }

    #[test]
    fn nonce_challenge_signature_and_expiry_replays_are_refused() {
        let c = config();
        let key = SigningKey::from_bytes(&[3; 32]);
        let wallet = key.verifying_key().to_bytes();
        let mut gate = Gate::new();
        let challenge = gate.issue(&c, wallet, player(), [9; 32], 1000, 50).unwrap();
        assert_eq!(
            gate.issue(&c, wallet, player(), [9; 32], 1000, 50),
            Err(GateError::NonceAlreadyIssued)
        );
        let observed =
            validate_rpc_snapshot(&c, &challenge, &snapshot(&c, &challenge, wallet, 1)).unwrap();
        let attacker = SigningKey::from_bytes(&[4; 32]);
        assert_eq!(
            gate.admit_beta(
                &c,
                &challenge,
                &binding(&attacker, &challenge),
                observed.clone(),
                51
            ),
            Err(GateError::BadWalletSignature)
        );
        assert_eq!(
            gate.admit_beta(
                &c,
                &challenge,
                &binding(&key, &challenge),
                observed.clone(),
                351
            ),
            Err(GateError::ChallengeExpired)
        );
        gate.admit_beta(
            &c,
            &challenge,
            &binding(&key, &challenge),
            observed.clone(),
            51,
        )
        .unwrap();
        assert_eq!(
            gate.admit_beta(&c, &challenge, &binding(&key, &challenge), observed, 52),
            Err(GateError::ChallengeReplay)
        );
    }

    #[test]
    fn rpc_must_bind_endpoint_cluster_finality_slot_program_mint_and_owner() {
        let c = config();
        let key = SigningKey::from_bytes(&[3; 32]);
        let wallet = key.verifying_key().to_bytes();
        let mut gate = Gate::new();
        let challenge = gate.issue(&c, wallet, player(), [9; 32], 1000, 50).unwrap();
        let mut s = snapshot(&c, &challenge, wallet, u64::MAX);
        s.endpoint_id = [99; 32];
        assert_eq!(
            validate_rpc_snapshot(&c, &challenge, &s),
            Err(GateError::WrongRpcEndpoint)
        );
        let mut s = snapshot(&c, &challenge, wallet, 1);
        s.genesis_hash = [99; 32];
        assert_eq!(
            validate_rpc_snapshot(&c, &challenge, &s),
            Err(GateError::WrongCluster)
        );
        let mut s = snapshot(&c, &challenge, wallet, 1);
        s.commitment = Commitment::Confirmed;
        assert_eq!(
            validate_rpc_snapshot(&c, &challenge, &s),
            Err(GateError::NotFinalized)
        );
        let mut s = snapshot(&c, &challenge, wallet, 1);
        s.accounts[0].account.owner_program = [99; 32];
        assert_eq!(
            validate_rpc_snapshot(&c, &challenge, &s),
            Err(GateError::WrongTokenProgram)
        );
        let mut s = snapshot(&c, &challenge, wallet, 1);
        s.accounts[0].account.data[..32].copy_from_slice(&[99; 32]);
        assert_eq!(
            validate_rpc_snapshot(&c, &challenge, &s),
            Err(GateError::WrongMint)
        );
        let mut s = snapshot(&c, &challenge, wallet, 1);
        s.accounts[0].account.data[32..64].copy_from_slice(&[99; 32]);
        assert_eq!(
            validate_rpc_snapshot(&c, &challenge, &s),
            Err(GateError::WrongOwner)
        );
    }

    #[test]
    fn structure_only_beta_fact_still_grants_zero_governance_weight() {
        let key = SigningKey::from_bytes(&[3; 32]);
        let owner = key.verifying_key().to_bytes();
        let holding = ProvenHolding {
            token_account: [1; 32],
            owner,
            mint: config().mint,
            amount: u64::MAX,
            slot: 1,
            trust: LockProofTrust::StructureOnly,
        };
        let voter = [2; 32];
        let b = OwnerBinding {
            voter,
            sig: key.sign(&binding_message(&owner, &voter)).to_bytes(),
        };
        assert_eq!(
            grant_weight(&holding, &b),
            Err(GrantError::NotConsensusProven)
        );
    }

    #[test]
    fn no_client_asserted_balance_exists_and_empty_rpc_set_is_insufficient() {
        let c = config();
        let key = SigningKey::from_bytes(&[3; 32]);
        let wallet = key.verifying_key().to_bytes();
        let mut gate = Gate::new();
        let challenge = gate.issue(&c, wallet, player(), [9; 32], 1000, 50).unwrap();
        let mut s = snapshot(&c, &challenge, wallet, 1);
        s.accounts.clear();
        assert_eq!(
            validate_rpc_snapshot(&c, &challenge, &s),
            Err(GateError::InsufficientBalance)
        );
    }

    #[test]
    fn live_source_receives_the_exact_pinned_finalized_query() {
        let c = config();
        let key = SigningKey::from_bytes(&[3; 32]);
        let wallet = key.verifying_key().to_bytes();
        let mut gate = Gate::new();
        let challenge = gate
            .issue(&c, wallet, player(), [9; 32], 12_345, 50)
            .unwrap();
        let source = RecordingSource {
            response: snapshot(&c, &challenge, wallet, 7),
            seen: RefCell::new(Vec::new()),
        };

        let observed = observe_with_rpc_source(&source, &c, &challenge).unwrap();
        assert_eq!(observed.amount, 7);
        assert_eq!(
            source.seen.into_inner(),
            vec![RpcHoldingQuery {
                owner: wallet,
                mint: c.mint,
                token_program: c.token_program,
                commitment: Commitment::Finalized,
                min_context_slot: 12_345,
                expected_genesis_hash: c.genesis_hash,
            }]
        );
    }

    #[test]
    fn stale_mixed_duplicate_and_overflowing_account_sets_are_refused() {
        let c = config();
        let key = SigningKey::from_bytes(&[3; 32]);
        let wallet = key.verifying_key().to_bytes();
        let mut gate = Gate::new();
        let challenge = gate.issue(&c, wallet, player(), [9; 32], 1000, 50).unwrap();

        let mut s = snapshot(&c, &challenge, wallet, 1);
        s.requested_min_context_slot -= 1;
        assert_eq!(
            validate_rpc_snapshot(&c, &challenge, &s),
            Err(GateError::StaleSlot)
        );

        let mut s = snapshot(&c, &challenge, wallet, 1);
        s.context_slot = challenge.min_context_slot - 1;
        s.accounts[0].account.slot = s.context_slot;
        assert_eq!(
            validate_rpc_snapshot(&c, &challenge, &s),
            Err(GateError::StaleSlot)
        );

        let mut s = snapshot(&c, &challenge, wallet, 1);
        s.accounts[0].account.slot += 1;
        assert_eq!(
            validate_rpc_snapshot(&c, &challenge, &s),
            Err(GateError::MixedSlots)
        );

        let mut s = snapshot(&c, &challenge, wallet, 1);
        s.accounts.push(s.accounts[0].clone());
        assert_eq!(
            validate_rpc_snapshot(&c, &challenge, &s),
            Err(GateError::DuplicateTokenAccount)
        );

        let mut s = snapshot(&c, &challenge, wallet, u64::MAX);
        let mut second = account(&c, wallet, 1, s.context_slot);
        second.address = [45; 32];
        s.accounts.push(second);
        assert_eq!(
            validate_rpc_snapshot(&c, &challenge, &s),
            Err(GateError::BalanceOverflow)
        );
    }

    #[test]
    fn challenge_observation_and_capability_cannot_cross_their_boundaries() {
        let c = config();
        let key = SigningKey::from_bytes(&[3; 32]);
        let wallet = key.verifying_key().to_bytes();
        let mut gate = Gate::new();
        let first = gate.issue(&c, wallet, player(), [9; 32], 1000, 50).unwrap();
        let observed = validate_rpc_snapshot(&c, &first, &snapshot(&c, &first, wallet, 1)).unwrap();

        let mut mutated = first.clone();
        mutated.origin = "https://attacker.invalid".into();
        assert_eq!(
            gate.admit_beta(&c, &mutated, &binding(&key, &mutated), observed.clone(), 51),
            Err(GateError::ChallengeMutation)
        );

        let second = gate
            .issue(&c, wallet, player(), [10; 32], 2000, 51)
            .unwrap();
        assert_eq!(
            gate.admit_beta(&c, &second, &binding(&key, &second), observed, 52),
            Err(GateError::ObservationMismatch)
        );

        let observed = validate_rpc_snapshot(&c, &first, &snapshot(&c, &first, wallet, 1)).unwrap();
        let cap = gate
            .admit_beta(&c, &first, &binding(&key, &first), observed, 52)
            .unwrap();
        let mut forged = cap.clone();
        forged.receipt_id = [99; 32];
        assert_eq!(gate.consume(&forged, 53), Err(GateError::ForgedCapability));
        assert_eq!(gate.consume(&cap, 51), Err(GateError::CapabilityExpired));
        assert_eq!(
            gate.consume(&cap, cap.expires_at() + 1),
            Err(GateError::CapabilityExpired)
        );
    }
}
