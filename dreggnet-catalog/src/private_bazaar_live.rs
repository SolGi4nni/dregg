//! Explicit deployment seam for the private/proven Dark Bazaar raid.
//!
//! The ordinary catalog deliberately does not fabricate a roster, reward,
//! executor key, reserve, or durability directory.  A deployment first loads
//! and validates a [`PrivateBazaarRaidPolicy`], then constructs this object.
//! The same object owns:
//!
//! * the immutable configured offering registered into `OfferingHost`;
//! * the live-session registry used by the private settlement worker; and
//! * the durable global exactly-once authority store.
//!
//! Keeping those three handles together prevents the common half-mount where a
//! UI can open a pretty card but no worker can reach the exact hosted market or
//! its prepare-before-dispatch journal.

use std::fs;
use std::path::{Path, PathBuf};

use dregg_types::CellId;
use dreggnet_market::private_bazaar_game_adapter::{
    PrivateBazaarGameAdapterError, PrivateBazaarXpAdapter,
};
use dreggnet_market::private_bazaar_journey::{
    PrivateBazaarDeploymentPin, PrivateBazaarPublicReceipt, PrivateBazaarRaidPolicy,
};
use dreggnet_market::private_bazaar_live_host::{
    PrivateBazaarLiveHostError, PrivateBazaarLiveRegistry, PrivateBazaarRaidOffering,
};
use dreggnet_market::private_clearing::{
    PrivateClearingCommitmentStore, PrivateClearingError, PrivateClearingReceipt,
    PrivateSealedIngressBook,
};
use dreggnet_market::private_clearing_guild_allocation::{GuildMember, GuildReward, GuildRoster};
use dreggnet_market::{DarkBazaarOffering, TURN_BID};
use dreggnet_offerings::{Action, DreggIdentity, Offering, OfferingHost, Outcome};
use dungeon_on_dregg::progression::DungeonWorldCell;

use crate::private_bazaar_ingress::PrivateBazaarSealedIngressQueue;
use crate::private_bazaar_service::{
    PRIVATE_BAZAAR_WORKER_INITIAL_BACKOFF_MS_ENV, PRIVATE_BAZAAR_WORKER_MAX_BACKOFF_MS_ENV,
    PRIVATE_BAZAAR_WORKER_POLL_MS_ENV, PrivateBazaarAuthenticatedReceiptSource,
    PrivateBazaarLiveRuntime, PrivateBazaarWorkerServiceConfig, PrivateBazaarWorkerServiceError,
    PrivateBazaarWorkerSupervisor,
};
use crate::private_bazaar_targets::PrivateBazaarDurableTargetRegistry;
use crate::private_bazaar_worker::{
    PrivateBazaarFileWorker, PrivateBazaarReceiptSpool, PrivateBazaarSpoolScope,
    PrivateBazaarWorkerError, PrivateBazaarWorkerListener, PrivateBazaarWorkerTargets,
};
use crate::{CatalogConfig, build_full_catalog};

pub const PRIVATE_BAZAAR_RAID_TITLE: &str =
    "The Dark Bazaar raid — a viewer-blind private allocation with one exact receipted game effect";

pub const PRIVATE_BAZAAR_DEPLOYMENT_ID_ENV: &str = "DREGG_PRIVATE_BAZAAR_DEPLOYMENT_ID";
pub const PRIVATE_BAZAAR_ROSTER_ENV: &str = "DREGG_PRIVATE_BAZAAR_ROSTER";
pub const PRIVATE_BAZAAR_ROSTER_COMMITMENT_ENV: &str = "DREGG_PRIVATE_BAZAAR_ROSTER_COMMITMENT";
pub const PRIVATE_BAZAAR_REWARD_KIND_ENV: &str = "DREGG_PRIVATE_BAZAAR_REWARD_KIND";
pub const PRIVATE_BAZAAR_REWARD_AMOUNT_ENV: &str = "DREGG_PRIVATE_BAZAAR_REWARD_AMOUNT";
pub const PRIVATE_BAZAAR_REWARD_COMMITMENT_ENV: &str = "DREGG_PRIVATE_BAZAAR_REWARD_COMMITMENT";
pub const PRIVATE_BAZAAR_REWARD_METHOD_ENV: &str = "DREGG_PRIVATE_BAZAAR_REWARD_METHOD";
pub const PRIVATE_BAZAAR_REWARD_EVENT_TOPIC_ENV: &str = "DREGG_PRIVATE_BAZAAR_REWARD_EVENT_TOPIC";
pub const PRIVATE_BAZAAR_EXECUTOR_PUBKEY_ENV: &str = "DREGG_PRIVATE_BAZAAR_EXECUTOR_PUBKEY";
pub const PRIVATE_BAZAAR_EXECUTOR_FEDERATION_ENV: &str = "DREGG_PRIVATE_BAZAAR_EXECUTOR_FEDERATION";
pub const PRIVATE_BAZAAR_EXECUTOR_SIGNING_SEED_FILE_ENV: &str =
    "DREGG_PRIVATE_BAZAAR_EXECUTOR_SIGNING_SEED_FILE";
pub const PRIVATE_BAZAAR_RESERVE_ENV: &str = "DREGG_PRIVATE_BAZAAR_RESERVE";
pub const PRIVATE_BAZAAR_AUTHORITY_DIR_ENV: &str = "DREGG_PRIVATE_BAZAAR_AUTHORITY_DIR";

#[derive(Debug)]
pub enum PrivateBazaarLiveDeploymentError {
    Host(PrivateBazaarLiveHostError),
    GameAdapter(PrivateBazaarGameAdapterError),
    PrivateClearing(PrivateClearingError),
    Config(String),
}

impl std::fmt::Display for PrivateBazaarLiveDeploymentError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "private Bazaar deployment refused: {self:?}")
    }
}

impl std::error::Error for PrivateBazaarLiveDeploymentError {}

impl From<PrivateBazaarLiveHostError> for PrivateBazaarLiveDeploymentError {
    fn from(error: PrivateBazaarLiveHostError) -> Self {
        Self::Host(error)
    }
}

impl From<PrivateBazaarGameAdapterError> for PrivateBazaarLiveDeploymentError {
    fn from(error: PrivateBazaarGameAdapterError) -> Self {
        Self::GameAdapter(error)
    }
}

impl From<PrivateClearingError> for PrivateBazaarLiveDeploymentError {
    fn from(error: PrivateClearingError) -> Self {
        Self::PrivateClearing(error)
    }
}

/// Host-retained, worker-reachable configuration for one deployment.
///
/// Clones share both the live-session registry and the same durable store root;
/// they do not clone or weaken policy.  The public constructors accept an
/// already validated policy rather than an untrusted runtime roster.
#[derive(Clone)]
pub struct PrivateBazaarLiveDeployment {
    offering: PrivateBazaarRaidOffering,
    policy: PrivateBazaarRaidPolicy,
    registry: PrivateBazaarLiveRegistry,
    xp_adapter: PrivateBazaarXpAdapter,
    commitment_store: PrivateClearingCommitmentStore,
    authority_dir: PathBuf,
}

impl PrivateBazaarLiveDeployment {
    pub fn open(
        policy: PrivateBazaarRaidPolicy,
        reserve: u64,
        authority_dir: impl AsRef<Path>,
    ) -> Result<Self, PrivateBazaarLiveDeploymentError> {
        let authority_dir = pin_private_authority_directory(authority_dir.as_ref())?;
        let registry = PrivateBazaarLiveRegistry::new();
        let offering = PrivateBazaarRaidOffering::new(policy.clone(), reserve, registry.clone())?;
        let xp_adapter = PrivateBazaarXpAdapter::open(&authority_dir)?;
        let commitment_store =
            PrivateClearingCommitmentStore::open(authority_dir.join("private-commitments"))?;
        Ok(Self {
            offering,
            policy,
            registry,
            xp_adapter,
            commitment_store,
            authority_dir,
        })
    }

    /// Register the exact configured offering into a host.  Re-registering the
    /// key intentionally replaces any unconfigured lookalike.
    pub fn register(&self, host: &mut OfferingHost) {
        host.register(
            PrivateBazaarRaidOffering::KEY,
            PRIVATE_BAZAAR_RAID_TITLE,
            self.offering.clone(),
        );
    }

    /// A frontend-specific typed adapter may clone this offering into its own
    /// confined store; it still shares this deployment's registry and policy.
    pub fn offering(&self) -> PrivateBazaarRaidOffering {
        self.offering.clone()
    }

    /// Worker-side reachability into the exact sessions opened by the mounted
    /// offering.  No frontend action carries this handle.
    pub fn registry(&self) -> PrivateBazaarLiveRegistry {
        self.registry.clone()
    }

    /// The concrete durable Dungeon-XP adapter. It derives the pre-value from
    /// the target world and owns the nested generic authority journal; a
    /// frontend never supplies either value.
    pub fn xp_adapter(&self) -> PrivateBazaarXpAdapter {
        self.xp_adapter.clone()
    }

    /// Worker-private commitment registry. Its opaque bindings never expose
    /// either the persisted blind or the exact private-input digest.
    pub fn commitment_store(&self) -> PrivateClearingCommitmentStore {
        self.commitment_store.clone()
    }

    /// Construct the single-owner out-of-band production listener over this
    /// exact deployment. All private cursor/claim state is rooted under the
    /// deployment authority directory; frontend hosts receive only the shared
    /// viewer-blind journey projection.
    pub fn private_worker(
        &self,
        targets: PrivateBazaarWorkerTargets,
    ) -> Result<PrivateBazaarWorkerListener, PrivateBazaarWorkerError> {
        PrivateBazaarWorkerListener::open(self.clone(), targets, self.private_worker_root())
    }

    /// Open the deployment-custodied append-only finalized-receipt producer.
    /// Its fixed-schema file is colocated with the listener cursor/claims but
    /// remains wholly outside every frontend host and status projection.
    pub fn private_receipt_spool(
        &self,
    ) -> Result<PrivateBazaarReceiptSpool, PrivateBazaarWorkerError> {
        PrivateBazaarReceiptSpool::open(self.clone(), self.private_worker_root())
    }

    /// Open the concrete authenticated source used by the production
    /// supervisor. It discovers only receipts retained by proof-verified live
    /// markets; callers cannot submit a lookalike through this handle.
    pub fn private_authenticated_receipt_source(
        &self,
    ) -> Result<PrivateBazaarAuthenticatedReceiptSource, PrivateBazaarWorkerError> {
        PrivateBazaarAuthenticatedReceiptSource::open(self.clone())
    }

    /// Start the bounded restartable production loop using deployment-pinned
    /// source configuration and strict environment timing knobs.
    pub fn start_private_worker_service(
        &self,
        targets: PrivateBazaarWorkerTargets,
    ) -> Result<PrivateBazaarWorkerSupervisor, PrivateBazaarWorkerServiceError> {
        let config = PrivateBazaarWorkerServiceConfig::from_env(self)?;
        PrivateBazaarWorkerSupervisor::start(self.clone(), targets, config)
    }

    /// Start the production-owned runtime over an already populated durable
    /// target registry. Unlike the lower-level supervisor seam, this refuses an
    /// empty registry and retains deployment, targets, and clean shutdown as
    /// one owned value suitable for a catalog process.
    pub fn start_private_runtime(
        &self,
        targets: PrivateBazaarDurableTargetRegistry,
    ) -> Result<PrivateBazaarLiveRuntime, PrivateBazaarWorkerServiceError> {
        PrivateBazaarLiveRuntime::start(self.clone(), targets)
    }

    /// Open the deployment-custodied sealed-ingress queue: the out-of-band
    /// SUBMISSION half of the private clearing.
    ///
    /// This is what a production bid collector holds. It is deliberately not
    /// reachable from any frontend action: `OfferingHost` routes carry Enter and
    /// nothing else, and a book submitted here never crosses a browser or chat
    /// boundary. The supervisor drains this queue and runs the real relation on
    /// what it finds; an out-of-family book is refused here, by name, before a
    /// single BID turn touches the executor board.
    pub fn private_sealed_ingress(
        &self,
    ) -> Result<PrivateBazaarSealedIngressQueue, PrivateBazaarWorkerError> {
        PrivateBazaarSealedIngressQueue::open(self)
    }

    pub(crate) fn private_worker_root(&self) -> PathBuf {
        self.authority_dir.join("private-worker")
    }

    pub(crate) fn private_ingress_root(&self) -> PathBuf {
        self.authority_dir.join("private-ingress")
    }

    /// Has this deterministic hosted seed already produced a proof-verified
    /// private clearing? Used to close the crash window between a landed
    /// settlement and its durable ingress acknowledgement: without it a restart
    /// would replay a submission whose market is already terminal, be refused
    /// `AlreadySettled`, and wedge the queue on work that in fact succeeded.
    pub(crate) fn private_clearing_is_finalized(
        &self,
        seed: u64,
    ) -> Result<bool, PrivateBazaarWorkerError> {
        self.registry
            .with_entered_typed(seed, |market, _| {
                Ok::<_, ()>(market.verified_private_clearing().is_some())
            })
            .map_err(PrivateBazaarWorkerError::from)?
            .map_err(|()| PrivateBazaarWorkerError::StaleLiveMarket)
    }

    pub(crate) fn private_target_root(&self) -> PathBuf {
        self.authority_dir.join("private-targets")
    }

    pub(crate) fn private_target_checkpoint_root(&self) -> PathBuf {
        self.authority_dir.join("private-target-checkpoints")
    }

    pub(crate) fn private_target_cells(&self) -> Vec<CellId> {
        self.policy
            .roster()
            .ordered_members()
            .iter()
            .map(|member| member.character_cell)
            .collect()
    }

    pub(crate) fn private_target_members(&self) -> Vec<(DreggIdentity, CellId)> {
        self.policy
            .roster()
            .ordered_members()
            .iter()
            .map(|member| (member.actor.clone(), member.character_cell))
            .collect()
    }

    pub(crate) fn private_executor_pubkey(&self) -> [u8; 32] {
        self.policy.pin().executor_pubkey()
    }

    pub(crate) fn private_executor_federation(&self) -> [u8; 32] {
        self.policy.pin().executor_federation()
    }

    pub(crate) fn private_policy_id(&self) -> [u8; 32] {
        self.policy.policy_id()
    }

    pub(crate) fn private_spool_scope(&self) -> PrivateBazaarSpoolScope {
        PrivateBazaarSpoolScope::new(
            self.policy.pin().deployment_id(),
            self.policy.pin().executor_federation(),
            self.policy.policy_id(),
        )
    }

    pub(crate) fn finalized_private_receipts(
        &self,
        after_seed: Option<u64>,
        limit: usize,
    ) -> Result<(Vec<(u64, PrivateClearingReceipt)>, Option<u64>, bool), PrivateBazaarWorkerError>
    {
        self.registry
            .finalized_private_receipts_for_worker(after_seed, limit)
            .map_err(PrivateBazaarWorkerError::from)
    }

    /// Bind a producer receipt to the exact live proof-verified market before
    /// any semantic core is allowed into the durable spool.
    pub(crate) fn validate_private_spool_receipt(
        &self,
        seed: u64,
        receipt: &PrivateClearingReceipt,
    ) -> Result<[u8; 32], PrivateBazaarWorkerError> {
        self.registry
            .with_entered_typed(seed, |market, journey| {
                if journey.policy().policy_id() != self.policy.policy_id()
                    || journey.policy().pin().deployment_id() != self.policy.pin().deployment_id()
                    || journey.policy().pin().executor_federation()
                        != self.policy.pin().executor_federation()
                {
                    return Err(PrivateBazaarWorkerError::StaleLiveMarket);
                }
                receipt
                    .validate_worker_spool_live_settlement(market)
                    .map_err(|_| PrivateBazaarWorkerError::StaleLiveMarket)?;
                Ok(journey.market_identity().digest())
            })
            .map_err(|_| PrivateBazaarWorkerError::StaleLiveMarket)?
    }

    /// Revalidate a persisted envelope against the currently hosted issuance.
    /// This is run at poll time so a stale pre-restart envelope cannot reach the
    /// consequence authority after the live market has been replayed.
    pub(crate) fn revalidate_private_spool_receipt(
        &self,
        seed: u64,
        expected_market_instance_id: [u8; 32],
        receipt: &PrivateClearingReceipt,
    ) -> Result<(), PrivateBazaarWorkerError> {
        let found = self.validate_private_spool_receipt(seed, receipt)?;
        if found != expected_market_instance_id {
            return Err(PrivateBazaarWorkerError::StaleLiveMarket);
        }
        Ok(())
    }

    /// Open the production file transport and listener as one bounded runner.
    /// Process/thread spawning remains an embedding concern; callers invoke
    /// `tick` or `run_until_idle` from their supervised worker context.
    pub fn private_file_worker(
        &self,
        targets: PrivateBazaarWorkerTargets,
    ) -> Result<PrivateBazaarFileWorker, PrivateBazaarWorkerError> {
        let listener = self.private_worker(targets)?;
        let source = self.private_receipt_spool()?;
        Ok(PrivateBazaarFileWorker::new(listener, source))
    }

    /// PRODUCTION producer of a proof-verified private clearing.
    ///
    /// Every other private-Bazaar production surface in this crate — the
    /// authenticated receipt source, the durable spool, the worker listener, the
    /// supervisor — CONSUMES a `PrivateClearingReceipt`. Until this method
    /// existed, nothing outside test code produced one, so the whole live path
    /// idled on a producer that was only ever exercised by tests. This is that
    /// producer, and it runs the real relation: the Lean-emitted `N=4,K=4`
    /// descriptor's Plonky3 `HidingFriPcs` proof is minted over the worker's own
    /// sealed book and must VERIFY before the executor-backed SETTLE is
    /// submitted. No operator assertion can stand in for it.
    ///
    /// Order of operations is load-bearing:
    ///
    /// 1. a durable binding that contradicts this book is refused while the
    ///    board is still untouched;
    /// 2. the sealed bids become real executor BID turns — private ingress, out
    ///    of band; no browser or chat action can carry a bid, a limit, a blind,
    ///    a witness, or a proof;
    /// 3. the worker-private commitment blind is bound or reloaded, and pinned
    ///    to this exact ingress book;
    /// 4. the expected root/price/volume are derived from this worker's own book
    ///    and blind — never copied out of the proof about to be checked;
    /// 5. the hiding proof is minted and `settle_private_verified` refuses
    ///    unless it verifies against those independently pinned public values.
    ///
    /// SCALE: `book` is already gated to the proved family by
    /// [`PrivateSealedIngressBook::new`] (at most
    /// `PROVEN_MAX_SEALED_BIDS` = 3 sealed bids, limits inside the four-bucket
    /// price family, quantities fixed at one). There is no path from here that
    /// runs the relation on a book the descriptor does not cover, and there is
    /// no "clear it anyway, unproved" branch.
    pub fn settle_private_clearing_verified(
        &self,
        seed: u64,
        book: &PrivateSealedIngressBook,
        new_commitment_blinding: Option<[u32; 8]>,
    ) -> Result<PrivateClearingReceipt, PrivateBazaarLiveDeploymentError> {
        let commitment_store = self.commitment_store.clone();
        self.registry
            .with_entered_typed(seed, |market, journey| {
                let market_instance_id = journey.market_identity().digest();
                commitment_store.precheck_untouched_ingress(market_instance_id, book)?;

                let offering = DarkBazaarOffering::new();
                for (actor, limit) in book.sealed_bids() {
                    let outcome = offering.advance(
                        market,
                        Action::new("private ingress sealed bid", TURN_BID, *limit, true),
                        actor.clone(),
                    );
                    if !matches!(outcome, Outcome::Landed { .. }) {
                        return Err(PrivateClearingError::SettlementRefused(format!(
                            "private ingress sealed bid refused: {outcome:?}"
                        )));
                    }
                }

                let binding = commitment_store.bind_or_load(
                    market,
                    market_instance_id,
                    new_commitment_blinding,
                )?;
                if !binding.matches_ingress_book(book) {
                    return Err(PrivateClearingError::CommitmentBindingMismatch);
                }
                let expected = market
                    .private_clearing_expectation_with_binding(market_instance_id, &binding)?;
                let authorization = market
                    .prepare_private_clearing_zk_with_binding(market_instance_id, &binding)?;
                offering.settle_private_verified(market, authorization, expected)
            })?
            .map_err(PrivateBazaarLiveDeploymentError::PrivateClearing)
    }

    /// Consume one verified private clearing already installed in the exact
    /// live market and apply its pinned Dungeon consequence.
    ///
    /// This is the deployment-owned private-worker boundary. The public host
    /// supplies only the deterministic session seed; no browser/chat action can
    /// carry a clearing receipt, winner, witness, target, reward, or expected XP
    /// value. The adapter derives those values from the live settled market,
    /// immutable policy, receipt, and authoritative hero immediately before it
    /// durably prepares and dispatches the exact effect.
    pub fn apply_private_settlement(
        &self,
        seed: u64,
        private_receipt: &PrivateClearingReceipt,
        hero: &DungeonWorldCell,
    ) -> Result<PrivateBazaarPublicReceipt, PrivateBazaarLiveDeploymentError> {
        let adapter = self.xp_adapter.clone();
        self.registry
            .with_entered_typed(seed, |market, journey| {
                let operation = adapter.prepare(journey, market, private_receipt, hero)?;
                adapter
                    .dispatch_and_install(operation, journey, market, private_receipt, hero)
                    .cloned()
            })?
            .map_err(PrivateBazaarLiveDeploymentError::GameAdapter)
    }

    /// Rejoin a durably prepared/dispatched/applied/committed exact effect to a
    /// freshly replayed hosted journey after process restart. Recovery never
    /// dispatches a merely `Prepared` operation and never applies XP twice; it
    /// authenticates an already landed executor receipt before publishing the
    /// same viewer-blind terminal receipt.
    pub fn recover_private_settlement(
        &self,
        seed: u64,
        private_receipt: &PrivateClearingReceipt,
        hero: &DungeonWorldCell,
    ) -> Result<PrivateBazaarPublicReceipt, PrivateBazaarLiveDeploymentError> {
        let adapter = self.xp_adapter.clone();
        self.registry
            .with_entered_typed(seed, |market, journey| {
                adapter
                    .recover_and_install(journey, market, private_receipt, hero)
                    .cloned()
            })?
            .map_err(PrivateBazaarLiveDeploymentError::GameAdapter)
    }

    /// Resolve the opt-in production deployment. No sentinel means disabled;
    /// a partial or malformed configuration is a boot error, never a silent
    /// featureless downgrade.
    pub fn from_env() -> Result<Option<Self>, PrivateBazaarLiveDeploymentError> {
        Self::from_config_source(|name| std::env::var(name).ok())
    }

    /// Injectable configuration resolver used by production and hostile tests.
    pub fn from_config_source(
        get: impl Fn(&str) -> Option<String>,
    ) -> Result<Option<Self>, PrivateBazaarLiveDeploymentError> {
        let all = [
            PRIVATE_BAZAAR_DEPLOYMENT_ID_ENV,
            PRIVATE_BAZAAR_ROSTER_ENV,
            PRIVATE_BAZAAR_ROSTER_COMMITMENT_ENV,
            PRIVATE_BAZAAR_REWARD_KIND_ENV,
            PRIVATE_BAZAAR_REWARD_AMOUNT_ENV,
            PRIVATE_BAZAAR_REWARD_COMMITMENT_ENV,
            PRIVATE_BAZAAR_REWARD_METHOD_ENV,
            PRIVATE_BAZAAR_REWARD_EVENT_TOPIC_ENV,
            PRIVATE_BAZAAR_EXECUTOR_PUBKEY_ENV,
            PRIVATE_BAZAAR_EXECUTOR_FEDERATION_ENV,
            PRIVATE_BAZAAR_EXECUTOR_SIGNING_SEED_FILE_ENV,
            PRIVATE_BAZAAR_RESERVE_ENV,
            PRIVATE_BAZAAR_AUTHORITY_DIR_ENV,
            PRIVATE_BAZAAR_WORKER_POLL_MS_ENV,
            PRIVATE_BAZAAR_WORKER_INITIAL_BACKOFF_MS_ENV,
            PRIVATE_BAZAAR_WORKER_MAX_BACKOFF_MS_ENV,
        ];
        let Some(deployment_text) = get(PRIVATE_BAZAAR_DEPLOYMENT_ID_ENV) else {
            if let Some(stray) = all.into_iter().skip(1).find(|name| get(name).is_some()) {
                return Err(PrivateBazaarLiveDeploymentError::Config(format!(
                    "{stray} is set without {PRIVATE_BAZAAR_DEPLOYMENT_ID_ENV}"
                )));
            }
            return Ok(None);
        };
        let required = |name: &'static str| {
            get(name)
                .filter(|value| !value.trim().is_empty())
                .ok_or_else(|| {
                    PrivateBazaarLiveDeploymentError::Config(format!(
                        "{name} is required when {PRIVATE_BAZAAR_DEPLOYMENT_ID_ENV} is set"
                    ))
                })
        };
        let deployment_id = parse_hex32(PRIVATE_BAZAAR_DEPLOYMENT_ID_ENV, &deployment_text)?;
        let roster_text = required(PRIVATE_BAZAAR_ROSTER_ENV)?;
        let members = roster_text
            .split(';')
            .enumerate()
            .map(|(index, entry)| {
                let (actor, cell) = entry.split_once('=').ok_or_else(|| {
                    PrivateBazaarLiveDeploymentError::Config(format!(
                        "{PRIVATE_BAZAAR_ROSTER_ENV} entry {index} must be actor=64hex-cell"
                    ))
                })?;
                if actor.trim().is_empty() {
                    return Err(PrivateBazaarLiveDeploymentError::Config(format!(
                        "{PRIVATE_BAZAAR_ROSTER_ENV} entry {index} has an empty actor"
                    )));
                }
                Ok(GuildMember::new(
                    DreggIdentity(actor.trim().to_owned()),
                    CellId(parse_hex32(PRIVATE_BAZAAR_ROSTER_ENV, cell.trim())?),
                ))
            })
            .collect::<Result<Vec<_>, _>>()?;
        let roster = GuildRoster::new(members)
            .map_err(|error| PrivateBazaarLiveDeploymentError::Config(error.to_string()))?;
        let reward_amount = parse_u64(
            PRIVATE_BAZAAR_REWARD_AMOUNT_ENV,
            &required(PRIVATE_BAZAAR_REWARD_AMOUNT_ENV)?,
        )?;
        let reward = GuildReward::new(required(PRIVATE_BAZAAR_REWARD_KIND_ENV)?, reward_amount)
            .map_err(|error| PrivateBazaarLiveDeploymentError::Config(error.to_string()))?;
        let pin = PrivateBazaarDeploymentPin::new(
            deployment_id,
            parse_hex32(
                PRIVATE_BAZAAR_ROSTER_COMMITMENT_ENV,
                &required(PRIVATE_BAZAAR_ROSTER_COMMITMENT_ENV)?,
            )?,
            parse_hex32(
                PRIVATE_BAZAAR_REWARD_COMMITMENT_ENV,
                &required(PRIVATE_BAZAAR_REWARD_COMMITMENT_ENV)?,
            )?,
            required(PRIVATE_BAZAAR_REWARD_METHOD_ENV)?,
            parse_hex32(
                PRIVATE_BAZAAR_REWARD_EVENT_TOPIC_ENV,
                &required(PRIVATE_BAZAAR_REWARD_EVENT_TOPIC_ENV)?,
            )?,
            parse_hex32(
                PRIVATE_BAZAAR_EXECUTOR_PUBKEY_ENV,
                &required(PRIVATE_BAZAAR_EXECUTOR_PUBKEY_ENV)?,
            )?,
            parse_hex32(
                PRIVATE_BAZAAR_EXECUTOR_FEDERATION_ENV,
                &required(PRIVATE_BAZAAR_EXECUTOR_FEDERATION_ENV)?,
            )?,
        )
        .map_err(|error| PrivateBazaarLiveDeploymentError::Config(error.to_string()))?;
        let policy = PrivateBazaarRaidPolicy::load(pin, roster, reward)
            .map_err(|error| PrivateBazaarLiveDeploymentError::Config(error.to_string()))?;
        let reserve = parse_u64(
            PRIVATE_BAZAAR_RESERVE_ENV,
            &required(PRIVATE_BAZAAR_RESERVE_ENV)?,
        )?;
        let authority_dir = required(PRIVATE_BAZAAR_AUTHORITY_DIR_ENV)?;
        // The production loader validates contents, permissions, and the
        // derived public key. Requiring the handle here prevents a complete
        // market policy from presenting as enabled without its target custody.
        let _ = required(PRIVATE_BAZAAR_EXECUTOR_SIGNING_SEED_FILE_ENV)?;
        Ok(Some(Self::open(policy, reserve, authority_dir)?))
    }
}

fn pin_private_authority_directory(
    path: &Path,
) -> Result<PathBuf, PrivateBazaarLiveDeploymentError> {
    fs::create_dir_all(path).map_err(|error| {
        PrivateBazaarLiveDeploymentError::Config(format!(
            "private Bazaar authority directory could not be created: {error}"
        ))
    })?;
    let metadata = fs::symlink_metadata(path).map_err(|error| {
        PrivateBazaarLiveDeploymentError::Config(format!(
            "private Bazaar authority directory could not be inspected: {error}"
        ))
    })?;
    if metadata.file_type().is_symlink() || !metadata.is_dir() {
        return Err(PrivateBazaarLiveDeploymentError::Config(
            "private Bazaar authority path is not a regular directory".to_owned(),
        ));
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        fs::set_permissions(path, fs::Permissions::from_mode(0o700)).map_err(|error| {
            PrivateBazaarLiveDeploymentError::Config(format!(
                "private Bazaar authority permissions could not be restricted: {error}"
            ))
        })?;
    }
    fs::canonicalize(path).map_err(|error| {
        PrivateBazaarLiveDeploymentError::Config(format!(
            "private Bazaar authority directory could not be pinned: {error}"
        ))
    })
}

fn parse_hex32(
    name: &'static str,
    value: &str,
) -> Result<[u8; 32], PrivateBazaarLiveDeploymentError> {
    if value.len() != 64 {
        return Err(PrivateBazaarLiveDeploymentError::Config(format!(
            "{name} must be exactly 64 lowercase or uppercase hex characters"
        )));
    }
    let mut out = [0u8; 32];
    fn nibble(byte: u8) -> Option<u8> {
        match byte {
            b'0'..=b'9' => Some(byte - b'0'),
            b'a'..=b'f' => Some(byte - b'a' + 10),
            b'A'..=b'F' => Some(byte - b'A' + 10),
            _ => None,
        }
    }
    for (index, pair) in value.as_bytes().chunks_exact(2).enumerate() {
        let high = nibble(pair[0]).ok_or_else(|| {
            PrivateBazaarLiveDeploymentError::Config(format!("{name} contains non-hex bytes"))
        })?;
        let low = nibble(pair[1]).ok_or_else(|| {
            PrivateBazaarLiveDeploymentError::Config(format!("{name} contains non-hex bytes"))
        })?;
        out[index] = (high << 4) | low;
    }
    Ok(out)
}

fn parse_u64(name: &'static str, value: &str) -> Result<u64, PrivateBazaarLiveDeploymentError> {
    value.parse::<u64>().map_err(|_| {
        PrivateBazaarLiveDeploymentError::Config(format!("{name} must be a decimal u64"))
    })
}

pub fn build_full_catalog_with_private_bazaar(
    host: &mut OfferingHost,
    cfg: &CatalogConfig,
    deployment: &PrivateBazaarLiveDeployment,
) {
    build_full_catalog(host, cfg);
    deployment.register(host);
}

pub fn full_catalog_host_with_private_bazaar(
    cfg: &CatalogConfig,
    deployment: &PrivateBazaarLiveDeployment,
) -> OfferingHost {
    let mut host = OfferingHost::new();
    build_full_catalog_with_private_bazaar(&mut host, cfg, deployment);
    host
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_app_framework::{
        CellId, MlDsaKeygenCoreRealInstall, MlDsaSignCoreRealInstall, MlDsaVerifyCoreInstall,
        install_verified_mldsa_keygen_core_real, install_verified_mldsa_sign_core_real,
        install_verified_mldsa_verify_core, symbol,
    };
    use dregg_turn::{Finality, TurnReceipt};
    use dreggnet_market::private_bazaar_journey::{
        PrivateBazaarDeploymentPin, PrivateBazaarRaidPolicy,
    };
    use dreggnet_market::private_bazaar_live_host::PRIVATE_BAZAAR_RAID_KEY;
    use dreggnet_market::private_clearing::{PrivateClearingExpectation, PrivateClearingReceipt};
    use dreggnet_market::private_clearing_guild_allocation::{
        GuildMember, GuildReward, GuildRoster,
    };
    use dreggnet_market::{DarkBazaarOffering, TURN_BID};
    use dreggnet_offerings::{
        Action, DreggIdentity, FileResumeStore, Offering, Outcome, SessionConfig, SessionId,
    };
    use dungeon_on_dregg::progression::{
        DungeonWorldCell, PRIVATE_BAZAAR_XP_EVENT, PRIVATE_BAZAAR_XP_METHOD, deploy_hero,
    };
    use std::collections::BTreeMap;
    use std::fs::OpenOptions;
    use std::io::Write;
    use std::sync::Arc;
    use std::thread;
    use std::time::{Duration, Instant};

    use crate::private_bazaar_service::{
        PrivateBazaarWorkerServiceConfig, PrivateBazaarWorkerServiceError,
        PrivateBazaarWorkerServicePhase, PrivateBazaarWorkerSupervisor,
    };
    use crate::private_bazaar_worker::{
        FinalizedPrivateBazaarReceiptSource, PrivateBazaarWorkerError, PrivateBazaarWorkerTargets,
    };

    fn deployment(root: &Path) -> PrivateBazaarLiveDeployment {
        let roster = GuildRoster::new(vec![GuildMember::new(
            DreggIdentity("catalog-private-raider".to_owned()),
            CellId([0x41; 32]),
        )])
        .unwrap();
        let reward = GuildReward::new("raid-xp/catalog/v1", 144).unwrap();
        let pin = PrivateBazaarDeploymentPin::new(
            [0x11; 32],
            roster.digest(),
            PrivateBazaarRaidPolicy::reward_commitment_for_configuration(&reward),
            PRIVATE_BAZAAR_XP_METHOD,
            symbol(PRIVATE_BAZAAR_XP_EVENT),
            [0x22; 32],
            [0x33; 32],
        )
        .unwrap();
        PrivateBazaarLiveDeployment::open(
            PrivateBazaarRaidPolicy::load(pin, roster, reward).unwrap(),
            1,
            root,
        )
        .unwrap()
    }

    fn install_verified_test_pq_runtime() {
        assert!(std::env::var_os("DREGG_ALLOW_UNAUDITED_PQ").is_none());
        assert!(matches!(
            install_verified_mldsa_keygen_core_real(),
            MlDsaKeygenCoreRealInstall::Installed | MlDsaKeygenCoreRealInstall::AlreadyInstalled
        ));
        assert!(matches!(
            install_verified_mldsa_sign_core_real(),
            MlDsaSignCoreRealInstall::Installed | MlDsaSignCoreRealInstall::AlreadyInstalled
        ));
        assert!(matches!(
            install_verified_mldsa_verify_core(),
            MlDsaVerifyCoreInstall::Installed | MlDsaVerifyCoreInstall::AlreadyInstalled
        ));
    }

    fn playable_policy(hero: &DungeonWorldCell) -> PrivateBazaarRaidPolicy {
        let roster = GuildRoster::new(vec![
            GuildMember::new(
                DreggIdentity("catalog-private-seller".to_owned()),
                deploy_hero(0x91).cell_id(),
            ),
            GuildMember::new(
                DreggIdentity("catalog-private-low-bidder".to_owned()),
                deploy_hero(0x92).cell_id(),
            ),
            GuildMember::new(
                DreggIdentity("catalog-private-winner".to_owned()),
                hero.cell_id(),
            ),
        ])
        .unwrap();
        let reward = GuildReward::new("raid-xp/catalog-live/v1", 144).unwrap();
        let pin = PrivateBazaarDeploymentPin::new(
            [0x51; 32],
            roster.digest(),
            PrivateBazaarRaidPolicy::reward_commitment_for_configuration(&reward),
            PRIVATE_BAZAAR_XP_METHOD,
            symbol(PRIVATE_BAZAAR_XP_EVENT),
            hero.executor_pubkey().unwrap(),
            hero.federation_id(),
        )
        .unwrap();
        PrivateBazaarRaidPolicy::load(pin, roster, reward).unwrap()
    }

    fn enter_hosted_raid(host: &mut OfferingHost, id: &SessionId, seed: u64) {
        host.open_session(
            PRIVATE_BAZAAR_RAID_KEY,
            id.clone(),
            SessionConfig::with_seed(seed),
        )
        .unwrap();
        let enter = host.actions(PRIVATE_BAZAAR_RAID_KEY, id).unwrap()[0].clone();
        let outcome = host
            .advance(
                PRIVATE_BAZAAR_RAID_KEY,
                id,
                enter,
                DreggIdentity("catalog-private-seller".to_owned()),
            )
            .unwrap();
        assert!(matches!(outcome, Outcome::Landed { .. }), "{outcome:?}");
    }

    fn synthetic_final_receipt() -> PrivateClearingReceipt {
        PrivateClearingReceipt::from_worker_spool_v1_parts(
            17,
            1_430_520_836,
            [19; 8],
            3,
            1,
            DreggIdentity("synthetic-private-winner".to_owned()),
            TurnReceipt {
                turn_hash: [0x71; 32],
                finality: Finality::Final,
                ..TurnReceipt::default()
            },
        )
        .unwrap()
    }

    /// Worker-only test helper: replay the durable private inputs into the
    /// deployment registry, produce the real hiding proof, and install the
    /// verified settlement in the exact market owned by the public host. None
    /// of these values cross the public Offering action boundary.
    fn settle_worker_market(
        deployment: &PrivateBazaarLiveDeployment,
        seed: u64,
        new_commitment_blinding: Option<[u32; 8]>,
    ) -> PrivateClearingReceipt {
        deployment
            .registry()
            .with_entered_typed(seed, |market, journey| {
                let offering = DarkBazaarOffering::new();
                for (actor, value) in [
                    ("catalog-private-low-bidder", 2),
                    ("catalog-private-winner", 3),
                ] {
                    let outcome = offering.advance(
                        market,
                        Action::new("private worker bid", TURN_BID, value, true),
                        DreggIdentity(actor.to_owned()),
                    );
                    if !matches!(outcome, Outcome::Landed { .. }) {
                        return Err(format!("private worker bid refused: {outcome:?}"));
                    }
                }
                let market_instance_id = journey.market_identity().digest();
                let binding = deployment
                    .commitment_store()
                    .bind_or_load(market, market_instance_id, new_commitment_blinding)
                    .map_err(|error| error.to_string())?;
                let authorization = market
                    .prepare_private_clearing_zk_with_binding(market_instance_id, &binding)
                    .map_err(|error| error.to_string())?;
                let statement = authorization.statement();
                offering
                    .settle_private_verified(
                        market,
                        authorization,
                        PrivateClearingExpectation::from_statement(statement),
                    )
                    .map_err(|error| error.to_string())
            })
            .unwrap()
            .unwrap()
    }

    #[test]
    fn opt_in_catalog_mount_owns_registry_and_real_enter_lifecycle() {
        let temp = tempfile::tempdir().unwrap();
        let deployment = deployment(temp.path());
        let mut host =
            full_catalog_host_with_private_bazaar(&CatalogConfig::default(), &deployment);
        assert!(host.has(PRIVATE_BAZAAR_RAID_KEY));
        assert_eq!(
            host.title(PRIVATE_BAZAAR_RAID_KEY),
            Some(PRIVATE_BAZAAR_RAID_TITLE)
        );

        let id = SessionId::new("catalog-private-bazaar");
        let seed = 0xB4A2;
        host.open_session(
            PRIVATE_BAZAAR_RAID_KEY,
            id.clone(),
            SessionConfig::with_seed(seed),
        )
        .unwrap();
        let actions = host
            .actions(PRIVATE_BAZAAR_RAID_KEY, &id)
            .expect("mounted action set");
        assert_eq!(actions.len(), 1);
        let outcome = host
            .advance(
                PRIVATE_BAZAAR_RAID_KEY,
                &id,
                actions[0].clone(),
                DreggIdentity("catalog-private-raider".to_owned()),
            )
            .expect("mounted route");
        assert!(matches!(outcome, Outcome::Landed { .. }), "{outcome:?}");
        assert!(deployment.registry().contains(seed));
        assert!(
            format!(
                "{:?}",
                host.render(PRIVATE_BAZAAR_RAID_KEY, &id).unwrap().view()
            )
            .contains("pending")
        );
    }

    #[test]
    fn production_spool_refuses_a_missing_live_market() {
        let temp = tempfile::tempdir().unwrap();
        let deployment = deployment(temp.path());
        let seed = 0x51_A1_E;

        let mut spool = deployment.private_receipt_spool().unwrap();
        assert!(matches!(
            spool.append(1, seed, synthetic_final_receipt()),
            Err(PrivateBazaarWorkerError::StaleLiveMarket)
        ));
    }

    #[test]
    fn production_supervisor_faults_once_on_spool_corruption() {
        let temp = tempfile::tempdir().unwrap();
        let deployment = deployment(temp.path());
        let config = PrivateBazaarWorkerServiceConfig::for_deployment_with_timing(
            &deployment,
            Duration::from_millis(5),
            Duration::from_millis(5),
            Duration::from_millis(20),
        )
        .unwrap();
        let supervisor = PrivateBazaarWorkerSupervisor::start(
            deployment,
            PrivateBazaarWorkerTargets::default(),
            config,
        )
        .unwrap();
        let healthy_deadline = Instant::now() + Duration::from_secs(2);
        loop {
            let health = supervisor.health();
            if health.phase == PrivateBazaarWorkerServicePhase::Healthy {
                break;
            }
            assert!(
                Instant::now() < healthy_deadline,
                "worker health: {health:?}"
            );
            thread::sleep(Duration::from_millis(5));
        }

        let spool_path = temp
            .path()
            .join("private-worker")
            .join("finalized-private-bazaar-v2.spool");
        let mut spool = OpenOptions::new().append(true).open(spool_path).unwrap();
        spool.write_all(&[0xFF]).unwrap();
        spool.sync_all().unwrap();
        drop(spool);

        let fault_deadline = Instant::now() + Duration::from_secs(2);
        let faulted = loop {
            let health = supervisor.health();
            if health.phase == PrivateBazaarWorkerServicePhase::Faulted {
                break health;
            }
            assert!(Instant::now() < fault_deadline, "worker health: {health:?}");
            thread::sleep(Duration::from_millis(5));
        };
        assert_eq!(
            faulted.last_failure,
            Some(crate::private_bazaar_service::PrivateBazaarWorkerFaultClass::Integrity)
        );
        thread::sleep(Duration::from_millis(30));
        assert_eq!(supervisor.health().ticks, faulted.ticks);
        assert_eq!(
            supervisor.shutdown().unwrap().phase,
            PrivateBazaarWorkerServicePhase::Faulted
        );
    }

    #[test]
    fn hosted_private_worker_settles_viewer_blind_and_xp_is_exactly_once_across_restart() {
        install_verified_test_pq_runtime();
        let temp = tempfile::tempdir().unwrap();
        let authority_dir = temp.path().join("authority");
        let sessions_dir = temp.path().join("sessions");
        let hero = deploy_hero(0x93);
        hero.set_executor_signing_key([0xA7; 32]);
        let policy = playable_policy(&hero);
        let id = SessionId::new("catalog-private-bazaar-settlement");
        let seed = 0xB4_2A_A3;
        // Worker-private durable input: reusing this only for replay of this
        // exact book keeps the semantic order_root stable while proof/receipt
        // randomness remains fresh.
        let commitment_blinding = [0x00C0_FFEE; 8];

        let (first_private_receipt, first_source_use, first_operation) = {
            let deployment =
                PrivateBazaarLiveDeployment::open(policy.clone(), 1, &authority_dir).unwrap();
            let store = FileResumeStore::open(&sessions_dir).unwrap();
            let mut host =
                full_catalog_host_with_private_bazaar(&CatalogConfig::default(), &deployment)
                    .with_resume_store(Box::new(store));
            enter_hosted_raid(&mut host, &id, seed);
            assert!(
                format!(
                    "{:?}",
                    host.render(PRIVATE_BAZAAR_RAID_KEY, &id).unwrap().view()
                )
                .contains("pending")
            );

            let private_receipt =
                settle_worker_market(&deployment, seed, Some(commitment_blinding));
            let public = deployment
                .apply_private_settlement(seed, &private_receipt, &hero)
                .unwrap();
            assert_eq!(hero.read_var("xp"), 144);
            assert_eq!(public.phase().as_str(), "settled");
            let rendered = format!(
                "{:?}",
                host.render(PRIVATE_BAZAAR_RAID_KEY, &id).unwrap().view()
            );
            assert!(rendered.contains("Settled"), "{rendered}");
            assert!(!rendered.contains("catalog-private-winner"), "{rendered}");

            let replay = deployment.apply_private_settlement(seed, &private_receipt, &hero);
            assert!(matches!(
                replay,
                Err(PrivateBazaarLiveDeploymentError::GameAdapter(_))
            ));
            assert_eq!(hero.read_var("xp"), 144);
            (
                private_receipt,
                public.source_use_id().unwrap(),
                public.operation_id().unwrap(),
            )
        };

        // New host, registry, adapter, and resume-store handles. The public log
        // replays only Enter/LIST. The private worker independently replays its
        // durable private inputs to reconstruct the same settled market, then
        // recovery rejoins the already committed exact effect without another
        // executor turn.
        let restarted = PrivateBazaarLiveDeployment::open(policy, 1, &authority_dir).unwrap();
        let store = FileResumeStore::open(&sessions_dir).unwrap();
        let mut host = full_catalog_host_with_private_bazaar(&CatalogConfig::default(), &restarted)
            .with_resume_store(Box::new(store));
        let results = host.resume_all();
        assert_eq!(results.len(), 1, "{results:?}");
        assert!(results[0].1.is_ok(), "{results:?}");
        assert!(restarted.registry().contains(seed));

        let replayed_private_receipt = settle_worker_market(&restarted, seed, None);
        assert_ne!(
            replayed_private_receipt.settlement_turn.turn_hash,
            first_private_receipt.settlement_turn.turn_hash,
            "the replay test must exercise a genuinely reissued executor turn"
        );
        assert_ne!(
            replayed_private_receipt.settlement_turn.receipt_hash(),
            first_private_receipt.settlement_turn.receipt_hash(),
            "the replay test must exercise a genuinely reissued receipt envelope"
        );
        assert_eq!(
            replayed_private_receipt.statement, first_private_receipt.statement,
            "reissued evidence must carry the identical semantic private claim"
        );
        assert_eq!(
            replayed_private_receipt.winner, first_private_receipt.winner,
            "reissued evidence must select the identical semantic winner"
        );
        let recovered = restarted
            .recover_private_settlement(seed, &replayed_private_receipt, &hero)
            .unwrap();
        assert_eq!(hero.read_var("xp"), 144);
        assert_eq!(recovered.phase().as_str(), "settled");
        assert_eq!(recovered.source_use_id(), Some(first_source_use));
        assert_eq!(recovered.operation_id(), Some(first_operation));
        assert!(
            restarted
                .recover_private_settlement(seed, &replayed_private_receipt, &hero)
                .is_err()
        );
        assert_eq!(hero.read_var("xp"), 144);
        let rendered = format!(
            "{:?}",
            host.render(PRIVATE_BAZAAR_RAID_KEY, &id).unwrap().view()
        );
        assert!(rendered.contains("Settled"), "{rendered}");
        assert!(!rendered.contains("catalog-private-winner"), "{rendered}");
    }

    #[test]
    fn production_source_supervisor_reissues_and_recovers_after_full_restart() {
        install_verified_test_pq_runtime();
        let temp = tempfile::tempdir().unwrap();
        let authority_dir = temp.path().join("authority");
        let sessions_dir = temp.path().join("sessions");
        let hero = Arc::new(deploy_hero(0x94));
        hero.set_executor_signing_key([0xA8; 32]);
        let policy = playable_policy(&hero);
        let id = SessionId::new("catalog-private-bazaar-listener");
        let seed = 0xB4_2A_B4;
        let commitment_blinding = [0x0011_57E9; 8];
        let targets = PrivateBazaarWorkerTargets::from_worlds([Arc::clone(&hero)]).unwrap();

        let first_receipt = {
            let deployment =
                PrivateBazaarLiveDeployment::open(policy.clone(), 1, &authority_dir).unwrap();
            let store = FileResumeStore::open(&sessions_dir).unwrap();
            let mut host =
                full_catalog_host_with_private_bazaar(&CatalogConfig::default(), &deployment)
                    .with_resume_store(Box::new(store));
            enter_hosted_raid(&mut host, &id, seed);
            let private_receipt =
                settle_worker_market(&deployment, seed, Some(commitment_blinding));
            let mut authenticated_source =
                deployment.private_authenticated_receipt_source().unwrap();
            let capture = authenticated_source.capture_once().unwrap();
            assert_eq!(capture.observed, 1);
            assert_eq!(capture.appended, 1);
            drop(authenticated_source);
            let worker = deployment.private_worker(targets.clone()).unwrap();
            let mut source = deployment.private_receipt_spool().unwrap();

            let injected = worker.poll_once_with_after_dispatch_crash(&mut source);
            assert!(matches!(
                injected,
                Err(PrivateBazaarWorkerError::InjectedAfterTargetDispatch)
            ));
            assert_eq!(hero.read_var("xp"), 144);
            let pending = format!(
                "{:?}",
                host.render(PRIVATE_BAZAAR_RAID_KEY, &id).unwrap().view()
            );
            assert!(pending.contains("pending"), "{pending}");
            assert!(!pending.contains("catalog-private-winner"), "{pending}");
            private_receipt
        };
        let target_receipts_after_uncertain_dispatch = hero.receipt_chain_snapshot().len();

        // A new host/deployment replays public Enter/LIST and independently
        // reissues proof/settlement evidence. The producer appends that fresh
        // local envelope as a revision of the identical semantic cursor. The
        // worker polls only the current live-bound envelope, then sees the
        // persisted exact claim in Dispatching and never redispatches.
        let restarted = PrivateBazaarLiveDeployment::open(policy, 1, &authority_dir).unwrap();
        let store = FileResumeStore::open(&sessions_dir).unwrap();
        let mut host = full_catalog_host_with_private_bazaar(&CatalogConfig::default(), &restarted)
            .with_resume_store(Box::new(store));
        let resumed = host.resume_all();
        assert_eq!(resumed.len(), 1, "{resumed:?}");
        assert!(resumed[0].1.is_ok(), "{resumed:?}");
        let reissued = settle_worker_market(&restarted, seed, None);
        assert_eq!(reissued.statement, first_receipt.statement);
        assert_ne!(
            reissued.settlement_turn.receipt_hash(),
            first_receipt.settlement_turn.receipt_hash()
        );
        assert_eq!(reissued.winner, first_receipt.winner);

        let mut stale_source = restarted.private_receipt_spool().unwrap();
        let stale = stale_source
            .poll_finalized_after(0, 1)
            .expect_err("the pre-restart envelope must not poll against the replayed market");
        assert!(matches!(stale, PrivateBazaarWorkerError::StaleLiveMarket));
        drop(stale_source);

        let config = PrivateBazaarWorkerServiceConfig::for_deployment_with_timing(
            &restarted,
            Duration::from_millis(5),
            Duration::from_millis(5),
            Duration::from_millis(20),
        )
        .unwrap();
        let supervisor = PrivateBazaarWorkerSupervisor::start(
            restarted.clone(),
            targets.clone(),
            config.clone(),
        )
        .unwrap();
        assert!(matches!(
            PrivateBazaarWorkerSupervisor::start(restarted.clone(), targets, config),
            Err(PrivateBazaarWorkerServiceError::Worker(
                PrivateBazaarWorkerError::SupervisorAlreadyRunning
            ))
        ));
        let deadline = Instant::now() + Duration::from_secs(5);
        let health = loop {
            let health = supervisor.health();
            if health.cursor == 1 && health.processed == 1 {
                break health;
            }
            assert!(Instant::now() < deadline, "worker health: {health:?}");
            thread::sleep(Duration::from_millis(5));
        };
        assert_eq!(health.phase, PrivateBazaarWorkerServicePhase::Healthy);
        assert_eq!(
            health.source_appends, 1,
            "the reissued envelope is appended once"
        );
        let operational = format!("{health:?}");
        assert!(!operational.contains("winner"), "{operational}");
        assert!(!operational.contains("order_root"), "{operational}");
        let stopped = supervisor.shutdown().unwrap();
        assert_eq!(stopped.phase, PrivateBazaarWorkerServicePhase::Stopped);
        assert_eq!(hero.read_var("xp"), 144);
        assert_eq!(
            hero.receipt_chain_snapshot().len(),
            target_receipts_after_uncertain_dispatch,
            "Dispatching recovery must not call the target executor again"
        );
        let rendered = format!(
            "{:?}",
            host.render(PRIVATE_BAZAAR_RAID_KEY, &id).unwrap().view()
        );
        assert!(rendered.contains("Settled"), "{rendered}");
        assert!(!rendered.contains("catalog-private-winner"), "{rendered}");
        assert!(!rendered.contains("order_root"), "{rendered}");
    }

    #[test]
    fn deployment_file_spool_replays_unacked_dispatch_and_runs_until_idle() {
        install_verified_test_pq_runtime();
        let temp = tempfile::tempdir().unwrap();
        let authority_dir = temp.path().join("authority");
        let hero = Arc::new(deploy_hero(0x95));
        hero.set_executor_signing_key([0xA9; 32]);
        let deployment =
            PrivateBazaarLiveDeployment::open(playable_policy(&hero), 1, &authority_dir).unwrap();
        let targets = PrivateBazaarWorkerTargets::from_worlds([Arc::clone(&hero)]).unwrap();
        let mut host =
            full_catalog_host_with_private_bazaar(&CatalogConfig::default(), &deployment);
        let id = SessionId::new("catalog-private-bazaar-file-worker");
        let seed = 0xB5_2A_B5;
        enter_hosted_raid(&mut host, &id, seed);
        let receipt = settle_worker_market(&deployment, seed, Some([0x0011_57EA; 8]));

        let mut producer = deployment.private_receipt_spool().unwrap();
        producer.append(1, seed, receipt).unwrap();
        let worker = deployment.private_worker(targets.clone()).unwrap();
        let mut source = deployment.private_receipt_spool().unwrap();
        assert!(matches!(
            worker.poll_once_with_after_dispatch_crash(&mut source),
            Err(PrivateBazaarWorkerError::InjectedAfterTargetDispatch)
        ));
        assert_eq!(hero.read_var("xp"), 144);
        let target_receipts_after_uncertain_dispatch = hero.receipt_chain_snapshot().len();

        // Reopening both halves models worker-process loss before cursor ack:
        // cursor 1 is replayed from the fsynced spool, while the dispatching
        // authority recovers the already-landed target receipt exactly once.
        let mut restarted_worker = deployment.private_file_worker(targets).unwrap();
        assert!(matches!(
            restarted_worker.run_until_idle(0),
            Err(PrivateBazaarWorkerError::InvalidRunBound { .. })
        ));
        let run = restarted_worker.run_until_idle(2).unwrap();
        assert_eq!(run.cursor, 1);
        assert_eq!(run.processed, 1);
        assert_eq!(run.ticks, 2);
        assert!(run.idle);
        assert_eq!(hero.read_var("xp"), 144);
        assert_eq!(
            hero.receipt_chain_snapshot().len(),
            target_receipts_after_uncertain_dispatch,
            "spool replay must recover, never redispatch"
        );
        let operational = format!("{run:?}");
        assert!(!operational.contains("winner"), "{operational}");
        assert!(!operational.contains("order_root"), "{operational}");
        let rendered = format!(
            "{:?}",
            host.render(PRIVATE_BAZAAR_RAID_KEY, &id).unwrap().view()
        );
        assert!(rendered.contains("Settled"), "{rendered}");
        assert!(!rendered.contains("catalog-private-winner"), "{rendered}");
        assert!(!rendered.contains("order_root"), "{rendered}");
    }

    #[test]
    fn production_config_is_absent_or_complete_never_partial() {
        assert!(
            PrivateBazaarLiveDeployment::from_config_source(|_| None)
                .unwrap()
                .is_none()
        );
        let partial = PrivateBazaarLiveDeployment::from_config_source(|name| {
            (name == PRIVATE_BAZAAR_RESERVE_ENV).then(|| "1".to_owned())
        });
        assert!(matches!(
            partial,
            Err(PrivateBazaarLiveDeploymentError::Config(_))
        ));
        let stray_worker = PrivateBazaarLiveDeployment::from_config_source(|name| {
            (name == PRIVATE_BAZAAR_WORKER_POLL_MS_ENV).then(|| "10".to_owned())
        });
        assert!(matches!(
            stray_worker,
            Err(PrivateBazaarLiveDeploymentError::Config(_))
        ));
        let stray_signer = PrivateBazaarLiveDeployment::from_config_source(|name| {
            (name == PRIVATE_BAZAAR_EXECUTOR_SIGNING_SEED_FILE_ENV)
                .then(|| "/not/opened/by-config-parser".to_owned())
        });
        assert!(matches!(
            stray_signer,
            Err(PrivateBazaarLiveDeploymentError::Config(_))
        ));

        let temp = tempfile::tempdir().unwrap();
        let deployment = deployment(temp.path());
        assert!(matches!(
            PrivateBazaarWorkerServiceConfig::from_config_source(&deployment, |name| {
                (name == PRIVATE_BAZAAR_WORKER_POLL_MS_ENV).then(|| "0".to_owned())
            }),
            Err(PrivateBazaarWorkerServiceError::InvalidMillis(
                PRIVATE_BAZAAR_WORKER_POLL_MS_ENV
            ))
        ));
        let config =
            PrivateBazaarWorkerServiceConfig::from_config_source(&deployment, |_| None).unwrap();
        let rendered = format!("{config:?}");
        assert!(
            !rendered.contains(temp.path().to_str().unwrap()),
            "{rendered}"
        );
        assert!(!rendered.contains("winner"), "{rendered}");
    }

    #[test]
    fn production_config_rechecks_independent_roster_and_reward_pins() {
        let temp = tempfile::tempdir().unwrap();
        let roster = GuildRoster::new(vec![GuildMember::new(
            DreggIdentity("configured-raider".to_owned()),
            CellId([0x81; 32]),
        )])
        .unwrap();
        let reward = GuildReward::new("raid-xp/configured/v1", 144).unwrap();
        let mut config = BTreeMap::from([
            (PRIVATE_BAZAAR_DEPLOYMENT_ID_ENV, hex(&[0x82; 32])),
            (
                PRIVATE_BAZAAR_ROSTER_ENV,
                format!("configured-raider={}", hex(&[0x81; 32])),
            ),
            (PRIVATE_BAZAAR_ROSTER_COMMITMENT_ENV, hex(&roster.digest())),
            (PRIVATE_BAZAAR_REWARD_KIND_ENV, reward.kind.clone()),
            (PRIVATE_BAZAAR_REWARD_AMOUNT_ENV, reward.amount.to_string()),
            (
                PRIVATE_BAZAAR_REWARD_COMMITMENT_ENV,
                hex(&PrivateBazaarRaidPolicy::reward_commitment_for_configuration(&reward)),
            ),
            (
                PRIVATE_BAZAAR_REWARD_METHOD_ENV,
                PRIVATE_BAZAAR_XP_METHOD.to_owned(),
            ),
            (
                PRIVATE_BAZAAR_REWARD_EVENT_TOPIC_ENV,
                hex(&symbol(PRIVATE_BAZAAR_XP_EVENT)),
            ),
            (PRIVATE_BAZAAR_EXECUTOR_PUBKEY_ENV, hex(&[0x83; 32])),
            (PRIVATE_BAZAAR_EXECUTOR_FEDERATION_ENV, hex(&[0x84; 32])),
            (PRIVATE_BAZAAR_RESERVE_ENV, "1".to_owned()),
            (
                PRIVATE_BAZAAR_AUTHORITY_DIR_ENV,
                temp.path().display().to_string(),
            ),
            (
                PRIVATE_BAZAAR_EXECUTOR_SIGNING_SEED_FILE_ENV,
                "/not-opened-by-config-parser".to_owned(),
            ),
        ]);
        assert!(
            PrivateBazaarLiveDeployment::from_config_source(|name| config.get(name).cloned())
                .unwrap()
                .is_some()
        );

        config.insert(PRIVATE_BAZAAR_ROSTER_COMMITMENT_ENV, hex(&[0xFF; 32]));
        assert!(matches!(
            PrivateBazaarLiveDeployment::from_config_source(|name| config.get(name).cloned()),
            Err(PrivateBazaarLiveDeploymentError::Config(_))
        ));
    }

    fn hex(bytes: &[u8; 32]) -> String {
        bytes.iter().map(|byte| format!("{byte:02x}")).collect()
    }

    const INGRESS_LOW_BIDDER: &str = "catalog-private-low-bidder";
    const INGRESS_WINNER: &str = "catalog-private-winner";

    fn ingress_bids() -> Vec<(DreggIdentity, i64)> {
        vec![
            (DreggIdentity(INGRESS_LOW_BIDDER.to_owned()), 2),
            (DreggIdentity(INGRESS_WINNER.to_owned()), 3),
        ]
    }

    /// THE DEPLOYED LOOP RUNS THE PROVEN RELATION, END TO END.
    ///
    /// Before this wiring the supervisor could only ever OBSERVE receipts, and
    /// the only thing in the tree that produced one was a test — so a shipped
    /// deployment polled a source no production caller could fill. Here a book
    /// is submitted out of band, the production supervisor thread picks it up,
    /// mints and verifies the real `HidingFriPcs` proof of the Lean-emitted
    /// `N=4,K=4` descriptor, lands the executor SETTLE, carries the receipt
    /// through the durable v3 spool, and dispatches the exact pinned Dungeon
    /// consequence. Nothing in this path is a stub and no step is simulated.
    ///
    /// SUBSTRATE, out loud: the constraints are Lean-authored
    /// (`metatheory/Market/DarkBazaarPrivateDescriptor.lean` → the emitted
    /// `dark-bazaar-private-n4k4.json` descriptor). Rust only calls the emitted
    /// artifact; nothing here hand-writes an AIR.
    #[test]
    fn the_deployed_supervisor_clears_a_submitted_sealed_book_end_to_end() {
        install_verified_test_pq_runtime();
        let temp = tempfile::tempdir().unwrap();
        let authority_dir = temp.path().join("authority");
        let hero = Arc::new(deploy_hero(0x9C));
        hero.set_executor_signing_key([0xB4; 32]);
        let deployment =
            PrivateBazaarLiveDeployment::open(playable_policy(&hero), 1, &authority_dir).unwrap();
        let mut host =
            full_catalog_host_with_private_bazaar(&CatalogConfig::default(), &deployment);
        let id = SessionId::new("catalog-private-bazaar-ingress");
        let seed = 0xB4_2A_C1;
        enter_hosted_raid(&mut host, &id, seed);
        let xp_before = hero.read_var("xp");

        // OUT OF BAND. This is the one production ingress, and no frontend
        // action can reach it: the mounted offering's only route is Enter.
        let mut ingress = deployment.private_sealed_ingress().unwrap();
        let accepted = ingress
            .submit(seed, ingress_bids(), Some([0x0011_57F1; 8]))
            .unwrap();
        assert_eq!(accepted.sequence, 1);
        assert_eq!(ingress.pending().unwrap(), 1);

        // A queued submission is NOT a settlement. Nothing has cleared, and the
        // executor board is untouched by the mere act of accepting a book.
        assert!(
            deployment
                .finalized_private_receipts(None, 8)
                .unwrap()
                .0
                .is_empty()
        );
        assert_eq!(hero.read_var("xp"), xp_before);

        let targets = PrivateBazaarWorkerTargets::from_worlds([Arc::clone(&hero)]).unwrap();
        let config = PrivateBazaarWorkerServiceConfig::for_deployment_with_timing(
            &deployment,
            Duration::from_millis(5),
            Duration::from_millis(5),
            Duration::from_millis(20),
        )
        .unwrap();
        let supervisor =
            PrivateBazaarWorkerSupervisor::start(deployment.clone(), targets, config).unwrap();

        let deadline = Instant::now() + Duration::from_secs(180);
        loop {
            let health = supervisor.health();
            assert_ne!(
                health.phase,
                PrivateBazaarWorkerServicePhase::Faulted,
                "the production loop faulted instead of clearing the submission: {health:?}"
            );
            if health.ingress_settled >= 1 && health.processed >= 1 {
                break;
            }
            assert!(
                Instant::now() < deadline,
                "the production loop never cleared the queued book: {health:?}"
            );
            thread::sleep(Duration::from_millis(25));
        }
        let health = supervisor.shutdown().unwrap();
        assert_eq!(health.ingress_settled, 1);
        assert_eq!(health.ingress_already_terminal, 0);
        assert_eq!(health.ingress_pending, 0);
        assert!(
            health.source_appends >= 1,
            "the REAL settlement receipt must reach the durable spool: {health:?}"
        );
        assert!(health.processed >= 1, "{health:?}");

        // The receipt is real, on the live path, at the real first price.
        let (finalized, _, _) = deployment.finalized_private_receipts(None, 8).unwrap();
        assert_eq!(finalized.len(), 1);
        assert_eq!(finalized[0].0, seed);
        assert_eq!((finalized[0].1.price(), finalized[0].1.volume()), (3, 1));
        assert_eq!(
            finalized[0].1.winner,
            DreggIdentity(INGRESS_WINNER.to_owned())
        );
        assert_ne!(finalized[0].1.settlement_turn.turn_hash, [0; 32]);
        assert!(
            !finalized[0].1.settlement_turn.emitted_events.is_empty(),
            "a real SETTLE emits events — that is exactly what the v2 spool could not carry"
        );

        // And the exact pinned game consequence landed, exactly once.
        assert_eq!(hero.read_var("xp"), xp_before + 144);

        // The queue is drained and stays drained across a reopen.
        assert_eq!(
            deployment
                .private_sealed_ingress()
                .unwrap()
                .pending()
                .unwrap(),
            0
        );
    }

    /// AN OUT-OF-FAMILY BOOK IS REFUSED AT INGRESS, BY NAME, AND NEVER QUEUED.
    ///
    /// The refusal happens at the API boundary, before anything durable exists
    /// and long before a BID turn could touch the executor board. Nothing is
    /// truncated to three bids and nothing is clamped into the price family.
    #[test]
    fn sealed_ingress_refuses_an_out_of_family_book_and_names_the_limit() {
        install_verified_test_pq_runtime();
        let temp = tempfile::tempdir().unwrap();
        let hero = Arc::new(deploy_hero(0x9D));
        hero.set_executor_signing_key([0xB5; 32]);
        let deployment =
            PrivateBazaarLiveDeployment::open(playable_policy(&hero), 1, temp.path()).unwrap();
        let mut ingress = deployment.private_sealed_ingress().unwrap();
        let seed = 0xB4_2A_C2;

        let too_many = ingress.submit(
            seed,
            vec![
                (DreggIdentity(INGRESS_LOW_BIDDER.to_owned()), 0),
                (DreggIdentity(INGRESS_WINNER.to_owned()), 1),
                (DreggIdentity("catalog-private-seller".to_owned()), 2),
                (DreggIdentity(INGRESS_WINNER.to_owned()), 3),
            ],
            None,
        );
        let named = too_many.as_ref().unwrap_err().to_string();
        assert!(
            named.contains("4 sealed bids exceeds PROVEN_MAX_SEALED_BIDS = 3"),
            "the refusal must name the limit that was exceeded: {named}"
        );

        let too_wide = ingress.submit(
            seed,
            vec![(DreggIdentity(INGRESS_WINNER.to_owned()), 4)],
            None,
        );
        let named = too_wide.as_ref().unwrap_err().to_string();
        assert!(
            named.contains("bid limit 4 is outside the proved price family 0..4"),
            "{named}"
        );

        let negative = ingress.submit(
            seed,
            vec![(DreggIdentity(INGRESS_WINNER.to_owned()), -1)],
            None,
        );
        assert!(
            negative
                .as_ref()
                .unwrap_err()
                .to_string()
                .contains("bid limit -1 is outside the proved price family"),
            "{negative:?}"
        );

        let empty = ingress.submit(seed, Vec::new(), None);
        assert!(matches!(
            empty,
            Err(crate::private_bazaar_ingress::PrivateBazaarIngressError::OutsideProvenFamily(_))
        ));

        // A bidder the deployment's immutable policy roster does not name is
        // refused too: the winner drives a pinned Dungeon consequence, so an
        // unknown winner has no target and must never reach the relation.
        let stranger = ingress.submit(
            seed,
            vec![(DreggIdentity("not-on-the-roster".to_owned()), 3)],
            None,
        );
        assert!(
            stranger
                .as_ref()
                .unwrap_err()
                .to_string()
                .contains("outside the deployment's immutable policy roster"),
            "{stranger:?}"
        );

        // Not one of those five attempts left a durable trace.
        assert_eq!(ingress.pending().unwrap(), 0);

        // And the type gate is the same one, so an in-family book still passes.
        assert_eq!(
            ingress.submit(seed, ingress_bids(), None).unwrap().sequence,
            1
        );
        assert_eq!(ingress.pending().unwrap(), 1);
    }

    /// THE RESTART PATH KNOWS WHO BID — BECAUSE THE COMMITMENT BINDING DOES NOT.
    ///
    /// The durable worker-private commitment binding pins the canonical ORDER
    /// records, `(side, qty, limit)`, because that is all the circuit commits
    /// to; a bidder identity is not in the relation at all. So the binding
    /// CANNOT distinguish `{low:2, winner:3}` from `{stranger:2, other:3}` —
    /// asserted below, so the hole is demonstrated rather than asserted about —
    /// while the WINNER, and therefore the pinned XP target, differs. The
    /// durable ingress record is what closes it: it carries the identities, and
    /// a restarted drain replays the exact submitted book.
    #[test]
    fn the_restart_path_replays_the_exact_bidders_the_binding_cannot_see() {
        install_verified_test_pq_runtime();
        let temp = tempfile::tempdir().unwrap();
        let authority_dir = temp.path().join("authority");
        let hero = Arc::new(deploy_hero(0x9E));
        hero.set_executor_signing_key([0xB6; 32]);
        let policy = playable_policy(&hero);
        let seed = 0xB4_2A_C3;

        // The hole, demonstrated: same limits, different bidders, IDENTICAL
        // canonical orders — which is exactly what the binding digests.
        let submitted = PrivateSealedIngressBook::new(ingress_bids()).unwrap();
        let substituted = PrivateSealedIngressBook::new(vec![
            (DreggIdentity("catalog-private-seller".to_owned()), 2),
            (DreggIdentity(INGRESS_LOW_BIDDER.to_owned()), 3),
        ])
        .unwrap();
        assert_eq!(
            submitted.canonical_orders(),
            substituted.canonical_orders(),
            "the commitment binding is blind to WHO bid; that is why the ingress \
             record must carry identities"
        );

        {
            let deployment =
                PrivateBazaarLiveDeployment::open(policy.clone(), 1, &authority_dir).unwrap();
            deployment
                .private_sealed_ingress()
                .unwrap()
                .submit(seed, ingress_bids(), Some([0x0011_57F2; 8]))
                .unwrap();
        }

        // Full restart: a fresh deployment over the same authority directory.
        let restarted = PrivateBazaarLiveDeployment::open(policy, 1, &authority_dir).unwrap();
        let ingress = restarted.private_sealed_ingress().unwrap();
        assert_eq!(ingress.pending().unwrap(), 1);
        let pending = ingress.next_pending().unwrap().expect("the queued book");
        assert_eq!(pending.sequence, 1);
        assert_eq!(pending.session_seed, seed);
        assert_eq!(pending.blinding, Some([0x0011_57F2; 8]));
        assert_eq!(
            pending.book.sealed_bids().to_vec(),
            ingress_bids(),
            "the restarted drain must replay the EXACT bidders, not merely a book \
             with the same multiset of limits"
        );
    }
}
