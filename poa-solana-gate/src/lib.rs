//! Path of Angels server admission for Solana `$DREGG` holders.
//!
//! This crate is an adapter, not a second Solana verifier. Wallet control uses
//! Dregg governance's existing [`binding_message`] / [`OwnerBinding`] scheme.
//! Raw RPC account decoding uses `dregg-bridge`; the live account shape is
//! `dregg-pay`'s watcher seam. Consensus upgrade uses `solana_feed` unchanged.
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
use dregg_governance::holding_weight::{OwnerBinding, binding_message, verify_binding};
use dregg_pay::watcher::FetchedAccount;
use sha2::{Digest as _, Sha256};

pub const DREGG_MINT_BASE58: &str = "XkeTXo1125vz5H9svJpGiw4JvLbN8VmMu9cmMvspump";
/// The `$DREGG` mint account is owned by Token-2022 (confirmed from finalized
/// mainnet `getAccountInfo`), not the legacy SPL Token program.
pub const DREGG_TOKEN_PROGRAM_BASE58: &str = "TokenzQdBNbLqP5VEhdkAS6EPFLC1PHnBqCXEpPxuEb";
pub const MAINNET_GENESIS_BASE58: &str = "5eykt4UsFv8P8NJdTREpY1vzqKqZKvdpKuc147dw2N9d";
const CHALLENGE_DOMAIN: &[u8] = b"path-of-angels/dregg-holding/challenge/v1";
const RECEIPT_DOMAIN: &[u8] = b"path-of-angels/dregg-holding/receipt/v1";

pub type Bytes32 = [u8; 32];

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

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Challenge {
    id: Bytes32,
    voter: Bytes32,
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
    pub fn voter(&self) -> Bytes32 {
        self.voter
    }
    pub fn wallet(&self) -> Bytes32 {
        self.wallet
    }
    pub fn expires_at(&self) -> u64 {
        self.expires_at
    }
    /// Exact wallet `signMessage` bytes, reusing Dregg's owner→voter binding.
    pub fn signing_message(&self) -> Vec<u8> {
        binding_message(&self.wallet, &self.voter)
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
) -> Result<ProvenHolding, ConsensusSourceError> {
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
    Ok(holding)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TrustTier {
    BetaRpcAttested,
    ConsensusVerified,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HoldingCapability {
    receipt_id: Bytes32,
    challenge_id: Bytes32,
    trust: TrustTier,
    wallet: Bytes32,
    federation_id: Bytes32,
    origin: String,
    domain: String,
    cluster: String,
    mint: Bytes32,
    raw_balance: u64,
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
    pub fn raw_balance(&self) -> u64 {
        self.raw_balance
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

/// Durable replay boundary. Production implementations must make each `*_once`
/// operation atomic and survive process restart; otherwise nonce replay reopens
/// after every deploy.
pub trait AdmissionStore {
    type Error: std::fmt::Display;
    fn insert_challenge_once(
        &mut self,
        nonce: Bytes32,
        challenge: Challenge,
    ) -> Result<bool, Self::Error>;
    fn challenge(&self, id: &Bytes32) -> Result<Option<Challenge>, Self::Error>;
    fn consume_challenge_once(&mut self, id: Bytes32) -> Result<bool, Self::Error>;
    fn challenge_consumed(&self, id: &Bytes32) -> Result<bool, Self::Error>;
    fn insert_capability_once(&mut self, id: Bytes32) -> Result<bool, Self::Error>;
    fn consume_capability_once(&mut self, id: Bytes32) -> Result<CapabilityUse, Self::Error>;
}

#[derive(Default)]
pub struct InMemoryAdmissionStore {
    issued: HashMap<Bytes32, Challenge>,
    used_nonces: HashSet<Bytes32>,
    spent_challenges: HashSet<Bytes32>,
    issued_capabilities: HashSet<Bytes32>,
    spent_capabilities: HashSet<Bytes32>,
}

impl AdmissionStore for InMemoryAdmissionStore {
    type Error = std::convert::Infallible;
    fn insert_challenge_once(
        &mut self,
        nonce: Bytes32,
        challenge: Challenge,
    ) -> Result<bool, Self::Error> {
        if !self.used_nonces.insert(nonce) {
            return Ok(false);
        }
        self.issued.insert(challenge.id, challenge);
        Ok(true)
    }
    fn challenge(&self, id: &Bytes32) -> Result<Option<Challenge>, Self::Error> {
        Ok(self.issued.get(id).cloned())
    }
    fn consume_challenge_once(&mut self, id: Bytes32) -> Result<bool, Self::Error> {
        Ok(self.spent_challenges.insert(id))
    }
    fn challenge_consumed(&self, id: &Bytes32) -> Result<bool, Self::Error> {
        Ok(self.spent_challenges.contains(id))
    }
    fn insert_capability_once(&mut self, id: Bytes32) -> Result<bool, Self::Error> {
        Ok(self.issued_capabilities.insert(id))
    }
    fn consume_capability_once(&mut self, id: Bytes32) -> Result<CapabilityUse, Self::Error> {
        if self.spent_capabilities.contains(&id) {
            return Ok(CapabilityUse::Replay);
        }
        if !self.issued_capabilities.remove(&id) {
            return Ok(CapabilityUse::Unknown);
        }
        self.spent_capabilities.insert(id);
        Ok(CapabilityUse::Consumed)
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

    pub fn issue(
        &mut self,
        config: &GateConfig,
        wallet: Bytes32,
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
        let transcript =
            challenge_transcript(config, &wallet, &nonce, min_context_slot, now, expires_at);
        let voter: Bytes32 = Sha256::digest(&transcript).into();
        let mut id_hasher = Sha256::new();
        id_hasher.update(CHALLENGE_DOMAIN);
        id_hasher.update(&transcript);
        let id: Bytes32 = id_hasher.finalize().into();
        let challenge = Challenge {
            id,
            voter,
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
        if !self
            .store
            .insert_challenge_once(nonce, challenge.clone())
            .map_err(|e| GateError::Store(e.to_string()))?
        {
            return Err(GateError::NonceAlreadyIssued);
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
        if binding.voter != presented.voter || !verify_binding(&presented.wallet, binding) {
            return Err(GateError::BadWalletSignature);
        }
        if observation.endpoint_id != config.rpc_endpoint_id
            || observation.wallet != presented.wallet
            || observation.mint != config.mint
            || observation.amount < config.minimum_raw_balance
            || observation.slot < presented.min_context_slot
        {
            return Err(GateError::ObservationMismatch);
        }
        if !self
            .store
            .consume_challenge_once(presented.id)
            .map_err(|e| GateError::Store(e.to_string()))?
        {
            return Err(GateError::ChallengeReplay);
        }
        let expires_at = now
            .checked_add(presented.capability_ttl_secs)
            .ok_or(GateError::TimeOverflow)?;
        let receipt_id = receipt_id(presented, &observation, now, expires_at);
        if !self
            .store
            .insert_capability_once(receipt_id)
            .map_err(|e| GateError::Store(e.to_string()))?
        {
            return Err(GateError::CapabilityIdCollision);
        }
        Ok(HoldingCapability {
            receipt_id,
            challenge_id: presented.id,
            trust: TrustTier::BetaRpcAttested,
            wallet: presented.wallet,
            federation_id: presented.federation_id,
            origin: presented.origin.clone(),
            domain: presented.domain.clone(),
            cluster: presented.cluster.clone(),
            mint: presented.mint,
            raw_balance: observation.amount,
            snapshot_slot: observation.slot,
            issued_at: now,
            expires_at,
        })
    }

    pub fn consume(&mut self, capability: &HoldingCapability, now: u64) -> Result<(), GateError> {
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
    put(&mut out, nonce);
    put(&mut out, &c.minimum_raw_balance.to_be_bytes());
    put(&mut out, &min_slot.to_be_bytes());
    put(&mut out, &c.challenge_ttl_secs.to_be_bytes());
    put(&mut out, &c.capability_ttl_secs.to_be_bytes());
    put(&mut out, &issued.to_be_bytes());
    put(&mut out, &expires.to_be_bytes());
    out
}

fn receipt_id(c: &Challenge, o: &RpcBetaObservation, issued: u64, expires: u64) -> Bytes32 {
    let mut h = Sha256::new();
    h.update(RECEIPT_DOMAIN);
    h.update(c.id);
    h.update(o.endpoint_id);
    h.update(o.wallet);
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
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_bridge::solana_trustless::LockProofTrust;
    use dregg_governance::holding_weight::{GrantError, grant_weight};
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
            voter: challenge.voter(),
            sig: key.sign(&challenge.signing_message()).to_bytes(),
        }
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
        let challenge = gate.issue(&c, wallet, [9; 32], 1000, 50).unwrap();
        let observed =
            validate_rpc_snapshot(&c, &challenge, &snapshot(&c, &challenge, wallet, 17)).unwrap();
        let cap = gate
            .admit_beta(&c, &challenge, &binding(&key, &challenge), observed, 51)
            .unwrap();
        assert_eq!(cap.trust(), TrustTier::BetaRpcAttested);
        assert_eq!(cap.raw_balance(), 17);
        assert!(!cap.is_governance_weight_bearing());
        assert_eq!(gate.consume(&cap, 52), Ok(()));
        assert_eq!(gate.consume(&cap, 53), Err(GateError::CapabilityReplay));
    }

    #[test]
    fn nonce_challenge_signature_and_expiry_replays_are_refused() {
        let c = config();
        let key = SigningKey::from_bytes(&[3; 32]);
        let wallet = key.verifying_key().to_bytes();
        let mut gate = Gate::new();
        let challenge = gate.issue(&c, wallet, [9; 32], 1000, 50).unwrap();
        assert_eq!(
            gate.issue(&c, wallet, [9; 32], 1000, 50),
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
        let challenge = gate.issue(&c, wallet, [9; 32], 1000, 50).unwrap();
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
        let challenge = gate.issue(&c, wallet, [9; 32], 1000, 50).unwrap();
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
        let challenge = gate.issue(&c, wallet, [9; 32], 12_345, 50).unwrap();
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
        let challenge = gate.issue(&c, wallet, [9; 32], 1000, 50).unwrap();

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
        let first = gate.issue(&c, wallet, [9; 32], 1000, 50).unwrap();
        let observed = validate_rpc_snapshot(&c, &first, &snapshot(&c, &first, wallet, 1)).unwrap();

        let mut mutated = first.clone();
        mutated.origin = "https://attacker.invalid".into();
        assert_eq!(
            gate.admit_beta(&c, &mutated, &binding(&key, &mutated), observed.clone(), 51),
            Err(GateError::ChallengeMutation)
        );

        let second = gate.issue(&c, wallet, [10; 32], 2000, 51).unwrap();
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
