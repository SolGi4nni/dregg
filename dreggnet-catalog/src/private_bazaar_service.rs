//! Deployment-owned production supervision for the private Bazaar worker.
//!
//! The source is not a public submission socket. It snapshots only receipts
//! retained by live hosted markets after `settle_private_verified`, then writes
//! them through the deployment-bound v2 spool, whose append path revalidates
//! the exact live market and policy. The supervisor performs one bounded source
//! capture and one bounded worker poll per iteration, backs off on refusal, and
//! publishes operational counters only.

use std::fs::{self, File};
use std::path::PathBuf;
use std::sync::{Arc, Condvar, Mutex};
use std::thread::{self, JoinHandle};
use std::time::Duration;

use dreggnet_market::private_clearing::PrivateSealedIngressBook;

use crate::private_bazaar_live::PrivateBazaarLiveDeployment;
use crate::private_bazaar_targets::PrivateBazaarDurableTargetRegistry;
use crate::private_bazaar_worker::{
    PrivateBazaarFileWorker, PrivateBazaarReceiptSpool, PrivateBazaarSpoolAppend,
    PrivateBazaarSpoolScope, PrivateBazaarWorkerError, PrivateBazaarWorkerTargets,
    acquire_private_worker_lease,
};

pub const PRIVATE_BAZAAR_WORKER_POLL_MS_ENV: &str = "DREGG_PRIVATE_BAZAAR_WORKER_POLL_MS";
pub const PRIVATE_BAZAAR_WORKER_INITIAL_BACKOFF_MS_ENV: &str =
    "DREGG_PRIVATE_BAZAAR_WORKER_INITIAL_BACKOFF_MS";
pub const PRIVATE_BAZAAR_WORKER_MAX_BACKOFF_MS_ENV: &str =
    "DREGG_PRIVATE_BAZAAR_WORKER_MAX_BACKOFF_MS";

const DEFAULT_POLL_MS: u64 = 250;
const DEFAULT_INITIAL_BACKOFF_MS: u64 = 250;
const DEFAULT_MAX_BACKOFF_MS: u64 = 30_000;
const MAX_POLL_MS: u64 = 60_000;
const MAX_BACKOFF_MS: u64 = 300_000;
const MAX_LIVE_SCAN_BATCH: usize = 32;

/// Private, authenticated source capture result. Counts are operational only;
/// no seed, receipt, winner, root, price, or target identity is exposed.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct PrivateBazaarSourceCapture {
    pub observed: usize,
    pub appended: usize,
}

/// Concrete production source. It can capture only proof-verified receipts
/// retained in this deployment's live registry, and its spool is fixed by the
/// deployment authority directory and scope.
pub struct PrivateBazaarAuthenticatedReceiptSource {
    deployment: PrivateBazaarLiveDeployment,
    spool: PrivateBazaarReceiptSpool,
    scan_after_seed: Option<u64>,
}

impl std::fmt::Debug for PrivateBazaarAuthenticatedReceiptSource {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("PrivateBazaarAuthenticatedReceiptSource")
            .field("deployment", &"<pinned>")
            .field("spool", &"<private-v2>")
            .finish()
    }
}

impl PrivateBazaarAuthenticatedReceiptSource {
    pub(crate) fn open(
        deployment: PrivateBazaarLiveDeployment,
    ) -> Result<Self, PrivateBazaarWorkerError> {
        let spool = deployment.private_receipt_spool()?;
        Ok(Self {
            deployment,
            spool,
            scan_after_seed: None,
        })
    }

    /// Capture one bounded-by-live-registry snapshot. Each deterministic hosted
    /// seed owns one logical cursor. An unchanged issuance is idempotent; a
    /// restart issuance of the identical semantic core appends one fresh v2
    /// envelope revision at that same cursor.
    pub fn capture_once(&mut self) -> Result<PrivateBazaarSourceCapture, PrivateBazaarWorkerError> {
        let (receipts, last_scanned_seed, exhausted) = self
            .deployment
            .finalized_private_receipts(self.scan_after_seed, MAX_LIVE_SCAN_BATCH)?;
        self.scan_after_seed = if exhausted { None } else { last_scanned_seed };
        let observed = receipts.len();
        let mut appended = 0usize;
        for (seed, receipt) in receipts {
            if self.spool.append_discovered_live(seed, receipt)?
                == PrivateBazaarSpoolAppend::Appended
            {
                appended = appended
                    .checked_add(1)
                    .ok_or(PrivateBazaarWorkerError::ProcessedCountOverflow)?;
            }
        }
        Ok(PrivateBazaarSourceCapture { observed, appended })
    }

    /// PRODUCTION: mint the real private-book proof for one live hosted market,
    /// then capture the receipt it authorized into this worker's durable spool.
    ///
    /// This is the one in-tree path from private ingress to the spool that ends
    /// in real cryptography. `capture_once` alone can only ever observe what
    /// something else already produced; before this method the producer existed
    /// only in test code, so the deployed worker polled a source no production
    /// caller could fill. The clearing is authorized by a verified Plonky3
    /// `HidingFriPcs` proof of the Lean-emitted `N=4,K=4` descriptor, over a
    /// book already gated to that proved shape — a refusal anywhere in the
    /// relation, the binding, or the public joins leaves the spool untouched.
    pub fn settle_and_capture(
        &mut self,
        seed: u64,
        book: &PrivateSealedIngressBook,
        new_commitment_blinding: Option<[u32; 8]>,
    ) -> Result<PrivateBazaarSourceCapture, PrivateBazaarWorkerError> {
        self.deployment
            .settle_private_clearing_verified(seed, book, new_commitment_blinding)
            .map_err(|error| PrivateBazaarWorkerError::PrivateClearingRefused(error.to_string()))?;
        self.capture_once()
    }
}

/// Immutable production loop configuration. The spool root and semantic scope
/// are derived from the deployment and have no public setters, so timing knobs
/// cannot redirect a worker to another deployment's source.
#[derive(Clone)]
pub struct PrivateBazaarWorkerServiceConfig {
    worker_root: PathBuf,
    scope: PrivateBazaarSpoolScope,
    poll_interval: Duration,
    initial_backoff: Duration,
    max_backoff: Duration,
}

impl std::fmt::Debug for PrivateBazaarWorkerServiceConfig {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("PrivateBazaarWorkerServiceConfig")
            .field("worker_root", &"<deployment-pinned>")
            .field("scope", &"<deployment-pinned>")
            .field("poll_interval", &self.poll_interval)
            .field("initial_backoff", &self.initial_backoff)
            .field("max_backoff", &self.max_backoff)
            .finish()
    }
}

impl PrivateBazaarWorkerServiceConfig {
    pub fn from_env(
        deployment: &PrivateBazaarLiveDeployment,
    ) -> Result<Self, PrivateBazaarWorkerServiceError> {
        Self::from_config_source(deployment, |name| std::env::var(name).ok())
    }

    pub fn from_config_source(
        deployment: &PrivateBazaarLiveDeployment,
        get: impl Fn(&str) -> Option<String>,
    ) -> Result<Self, PrivateBazaarWorkerServiceError> {
        let poll_ms = parse_millis(
            PRIVATE_BAZAAR_WORKER_POLL_MS_ENV,
            get(PRIVATE_BAZAAR_WORKER_POLL_MS_ENV),
            DEFAULT_POLL_MS,
            MAX_POLL_MS,
        )?;
        let initial_backoff_ms = parse_millis(
            PRIVATE_BAZAAR_WORKER_INITIAL_BACKOFF_MS_ENV,
            get(PRIVATE_BAZAAR_WORKER_INITIAL_BACKOFF_MS_ENV),
            DEFAULT_INITIAL_BACKOFF_MS,
            MAX_BACKOFF_MS,
        )?;
        let max_backoff_ms = parse_millis(
            PRIVATE_BAZAAR_WORKER_MAX_BACKOFF_MS_ENV,
            get(PRIVATE_BAZAAR_WORKER_MAX_BACKOFF_MS_ENV),
            DEFAULT_MAX_BACKOFF_MS,
            MAX_BACKOFF_MS,
        )?;
        Self::for_deployment_with_timing(
            deployment,
            Duration::from_millis(poll_ms),
            Duration::from_millis(initial_backoff_ms),
            Duration::from_millis(max_backoff_ms),
        )
    }

    /// Explicit timing constructor for embeddings and deterministic tests. The
    /// source root and scope remain deployment-derived and immutable.
    pub fn for_deployment_with_timing(
        deployment: &PrivateBazaarLiveDeployment,
        poll_interval: Duration,
        initial_backoff: Duration,
        max_backoff: Duration,
    ) -> Result<Self, PrivateBazaarWorkerServiceError> {
        validate_duration("worker poll interval", poll_interval, MAX_POLL_MS)?;
        validate_duration("worker initial backoff", initial_backoff, MAX_BACKOFF_MS)?;
        validate_duration("worker maximum backoff", max_backoff, MAX_BACKOFF_MS)?;
        if initial_backoff > max_backoff {
            return Err(PrivateBazaarWorkerServiceError::Config(
                "worker initial backoff exceeds maximum backoff",
            ));
        }
        Ok(Self {
            worker_root: deployment.private_worker_root(),
            scope: deployment.private_spool_scope(),
            poll_interval,
            initial_backoff,
            max_backoff,
        })
    }

    fn validate_for(
        &self,
        deployment: &PrivateBazaarLiveDeployment,
    ) -> Result<(), PrivateBazaarWorkerServiceError> {
        if self.scope != deployment.private_spool_scope()
            || self.worker_root != deployment.private_worker_root()
        {
            return Err(PrivateBazaarWorkerServiceError::Config(
                "worker config belongs to another deployment",
            ));
        }
        match fs::symlink_metadata(&self.worker_root) {
            Ok(metadata) if metadata.file_type().is_symlink() => {
                return Err(PrivateBazaarWorkerServiceError::Config(
                    "deployment worker root is a symlink",
                ));
            }
            Ok(metadata) if !metadata.is_dir() => {
                return Err(PrivateBazaarWorkerServiceError::Config(
                    "deployment worker root is not a directory",
                ));
            }
            Ok(_) => {}
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
            Err(_) => {
                return Err(PrivateBazaarWorkerServiceError::Config(
                    "deployment worker root cannot be inspected",
                ));
            }
        }
        Ok(())
    }
}

fn parse_millis(
    name: &'static str,
    value: Option<String>,
    default: u64,
    maximum: u64,
) -> Result<u64, PrivateBazaarWorkerServiceError> {
    let Some(value) = value else {
        return Ok(default);
    };
    let parsed = value
        .parse::<u64>()
        .map_err(|_| PrivateBazaarWorkerServiceError::InvalidMillis(name))?;
    if parsed == 0 || parsed > maximum {
        return Err(PrivateBazaarWorkerServiceError::InvalidMillis(name));
    }
    Ok(parsed)
}

fn validate_duration(
    label: &'static str,
    duration: Duration,
    maximum_ms: u64,
) -> Result<(), PrivateBazaarWorkerServiceError> {
    if duration.is_zero() || duration.as_millis() > u128::from(maximum_ms) {
        return Err(PrivateBazaarWorkerServiceError::Config(label));
    }
    Ok(())
}

/// Sanitized service state. It contains progress and failure classes only;
/// private source records and worker error strings are never retained here.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PrivateBazaarWorkerServicePhase {
    Starting,
    Healthy,
    BackingOff,
    Faulted,
    Stopped,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PrivateBazaarWorkerFaultClass {
    LiveMarketUnavailable,
    TargetUnavailable,
    SourceContract,
    Integrity,
    Consequence,
    Storage,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PrivateBazaarWorkerHealth {
    pub phase: PrivateBazaarWorkerServicePhase,
    pub cursor: u64,
    pub processed: u64,
    pub ticks: u64,
    pub source_appends: u64,
    pub consecutive_failures: u32,
    pub last_failure: Option<PrivateBazaarWorkerFaultClass>,
}

impl Default for PrivateBazaarWorkerHealth {
    fn default() -> Self {
        Self {
            phase: PrivateBazaarWorkerServicePhase::Starting,
            cursor: 0,
            processed: 0,
            ticks: 0,
            source_appends: 0,
            consecutive_failures: 0,
            last_failure: None,
        }
    }
}

struct PrivateBazaarWorkerShared {
    stop: Mutex<bool>,
    wake: Condvar,
    health: Mutex<PrivateBazaarWorkerHealth>,
}

/// Owned worker-thread supervisor. Dropping it requests shutdown and joins the
/// thread, while [`shutdown`](Self::shutdown) returns the final sanitized state.
pub struct PrivateBazaarWorkerSupervisor {
    shared: Arc<PrivateBazaarWorkerShared>,
    thread: Option<JoinHandle<()>>,
}

/// Fail-closed production owner for one live deployment and its worker.
///
/// Construction requires a caller-populated target registry. This crate has no
/// authority to synthesize or recover a deployment's durable Dungeon cells;
/// the embedding that owns those authenticated cells must install them before
/// starting this runtime. Keeping the supervisor here gives the deployment a
/// concrete owned shutdown path instead of leaving an uncalled library loop.
pub struct PrivateBazaarLiveRuntime {
    deployment: PrivateBazaarLiveDeployment,
    targets: PrivateBazaarWorkerTargets,
    supervisor: Option<PrivateBazaarWorkerSupervisor>,
}

impl std::fmt::Debug for PrivateBazaarLiveRuntime {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("PrivateBazaarLiveRuntime")
            .field("deployment", &"<pinned>")
            .field("targets", &"<authenticated-registry>")
            .field("health", &self.health())
            .finish()
    }
}

impl PrivateBazaarLiveRuntime {
    pub fn start(
        deployment: PrivateBazaarLiveDeployment,
        targets: PrivateBazaarDurableTargetRegistry,
    ) -> Result<Self, PrivateBazaarWorkerServiceError> {
        let targets = targets
            .into_worker_targets_for(&deployment)
            .map_err(|_| PrivateBazaarWorkerServiceError::TargetRegistry)?;
        if targets.is_empty()? {
            return Err(PrivateBazaarWorkerServiceError::NoTargets);
        }
        let config = PrivateBazaarWorkerServiceConfig::from_env(&deployment)?;
        let supervisor =
            PrivateBazaarWorkerSupervisor::start(deployment.clone(), targets.clone(), config)?;
        Ok(Self {
            deployment,
            targets,
            supervisor: Some(supervisor),
        })
    }

    pub fn deployment(&self) -> &PrivateBazaarLiveDeployment {
        &self.deployment
    }

    /// Public-safe immutable target coverage retained by this runtime.
    pub fn target_count(&self) -> usize {
        self.targets.len()
    }

    pub fn health(&self) -> PrivateBazaarWorkerHealth {
        self.supervisor
            .as_ref()
            .map(PrivateBazaarWorkerSupervisor::health)
            .unwrap_or(PrivateBazaarWorkerHealth {
                phase: PrivateBazaarWorkerServicePhase::Stopped,
                ..PrivateBazaarWorkerHealth::default()
            })
    }

    pub fn shutdown(
        mut self,
    ) -> Result<PrivateBazaarWorkerHealth, PrivateBazaarWorkerServiceError> {
        self.supervisor
            .take()
            .expect("private Bazaar live runtime owns its supervisor")
            .shutdown()
    }
}

impl std::fmt::Debug for PrivateBazaarWorkerSupervisor {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("PrivateBazaarWorkerSupervisor")
            .field("health", &self.health())
            .finish_non_exhaustive()
    }
}

impl PrivateBazaarWorkerSupervisor {
    pub fn start(
        deployment: PrivateBazaarLiveDeployment,
        targets: PrivateBazaarWorkerTargets,
        config: PrivateBazaarWorkerServiceConfig,
    ) -> Result<Self, PrivateBazaarWorkerServiceError> {
        config.validate_for(&deployment)?;
        let source = PrivateBazaarAuthenticatedReceiptSource::open(deployment.clone())?;
        let pinned_root = fs::canonicalize(&config.worker_root).map_err(|_| {
            PrivateBazaarWorkerServiceError::Config(
                "deployment worker root could not be pinned after source open",
            )
        })?;
        if pinned_root != config.worker_root {
            return Err(PrivateBazaarWorkerServiceError::Config(
                "deployment worker root changed identity",
            ));
        }
        let lease = acquire_private_worker_lease(&pinned_root)?;
        let worker = deployment.private_file_worker(targets)?;
        let shared = Arc::new(PrivateBazaarWorkerShared {
            stop: Mutex::new(false),
            wake: Condvar::new(),
            health: Mutex::new(PrivateBazaarWorkerHealth::default()),
        });
        let thread_shared = Arc::clone(&shared);
        let thread = thread::Builder::new()
            .name("private-bazaar-worker".to_owned())
            .spawn(move || run_service(source, worker, config, thread_shared, lease))
            .map_err(|_| PrivateBazaarWorkerServiceError::ThreadSpawn)?;
        Ok(Self {
            shared,
            thread: Some(thread),
        })
    }

    pub fn health(&self) -> PrivateBazaarWorkerHealth {
        *self
            .shared
            .health
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
    }

    pub fn request_shutdown(&self) {
        let mut stop = self
            .shared
            .stop
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        *stop = true;
        self.shared.wake.notify_all();
    }

    pub fn shutdown(
        mut self,
    ) -> Result<PrivateBazaarWorkerHealth, PrivateBazaarWorkerServiceError> {
        self.request_shutdown();
        self.join_thread()?;
        Ok(self.health())
    }

    fn join_thread(&mut self) -> Result<(), PrivateBazaarWorkerServiceError> {
        if let Some(thread) = self.thread.take() {
            thread
                .join()
                .map_err(|_| PrivateBazaarWorkerServiceError::ThreadPanicked)?;
        }
        Ok(())
    }
}

impl Drop for PrivateBazaarWorkerSupervisor {
    fn drop(&mut self) {
        self.request_shutdown();
        let _ = self.join_thread();
    }
}

fn run_service(
    mut source: PrivateBazaarAuthenticatedReceiptSource,
    mut worker: PrivateBazaarFileWorker,
    config: PrivateBazaarWorkerServiceConfig,
    shared: Arc<PrivateBazaarWorkerShared>,
    _lease: File,
) {
    let mut backoff = config.initial_backoff;
    loop {
        if stop_requested(&shared) {
            break;
        }

        let result = match source.capture_once() {
            Ok(capture) => {
                let mut health = lock_health(&shared);
                health.source_appends = health
                    .source_appends
                    .saturating_add(capture.appended as u64);
                drop(health);
                worker.tick()
            }
            Err(error) => Err(error),
        };

        let delay = match result {
            Ok(poll) => {
                let mut health = lock_health(&shared);
                health.phase = PrivateBazaarWorkerServicePhase::Healthy;
                health.cursor = poll.cursor;
                health.processed = health.processed.saturating_add(poll.processed as u64);
                health.ticks = health.ticks.saturating_add(1);
                health.consecutive_failures = 0;
                health.last_failure = None;
                backoff = config.initial_backoff;
                config.poll_interval
            }
            Err(error) => {
                let fault = classify_worker_error(&error);
                let mut health = lock_health(&shared);
                health.ticks = health.ticks.saturating_add(1);
                health.consecutive_failures = health.consecutive_failures.saturating_add(1);
                health.last_failure = Some(fault);
                if !retryable_fault(fault) {
                    health.phase = PrivateBazaarWorkerServicePhase::Faulted;
                    break;
                }
                health.phase = PrivateBazaarWorkerServicePhase::BackingOff;
                let delay = backoff;
                backoff = backoff
                    .checked_mul(2)
                    .unwrap_or(config.max_backoff)
                    .min(config.max_backoff);
                delay
            }
        };

        if wait_or_stopped(&shared, delay) {
            break;
        }
    }
    let mut health = lock_health(&shared);
    if health.phase != PrivateBazaarWorkerServicePhase::Faulted {
        health.phase = PrivateBazaarWorkerServicePhase::Stopped;
    }
}

fn lock_health(
    shared: &PrivateBazaarWorkerShared,
) -> std::sync::MutexGuard<'_, PrivateBazaarWorkerHealth> {
    shared
        .health
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner())
}

fn stop_requested(shared: &PrivateBazaarWorkerShared) -> bool {
    *shared
        .stop
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner())
}

fn wait_or_stopped(shared: &PrivateBazaarWorkerShared, delay: Duration) -> bool {
    let stop = shared
        .stop
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    if *stop {
        return true;
    }
    match shared.wake.wait_timeout(stop, delay) {
        Ok((stop, _)) => *stop,
        Err(poisoned) => *poisoned.into_inner().0,
    }
}

fn classify_worker_error(error: &PrivateBazaarWorkerError) -> PrivateBazaarWorkerFaultClass {
    match error {
        PrivateBazaarWorkerError::StaleLiveMarket | PrivateBazaarWorkerError::Host(_) => {
            PrivateBazaarWorkerFaultClass::LiveMarketUnavailable
        }
        PrivateBazaarWorkerError::TargetNotInstalled(_) => {
            PrivateBazaarWorkerFaultClass::TargetUnavailable
        }
        PrivateBazaarWorkerError::SourceExceededBound { .. }
        | PrivateBazaarWorkerError::InvalidPollLimit { .. }
        | PrivateBazaarWorkerError::InvalidRunBound { .. }
        | PrivateBazaarWorkerError::NonContiguousCursor { .. }
        | PrivateBazaarWorkerError::SpoolGap { .. }
        | PrivateBazaarWorkerError::SpoolCursorAhead { .. } => {
            PrivateBazaarWorkerFaultClass::SourceContract
        }
        PrivateBazaarWorkerError::GameAdapter(_) | PrivateBazaarWorkerError::Journey(_) => {
            PrivateBazaarWorkerFaultClass::Consequence
        }
        PrivateBazaarWorkerError::Io { .. } => PrivateBazaarWorkerFaultClass::Storage,
        PrivateBazaarWorkerError::SpoolFork { .. }
        | PrivateBazaarWorkerError::SpoolTrailingBytes { .. }
        | PrivateBazaarWorkerError::SpoolFileReplaced
        | PrivateBazaarWorkerError::LegacySpoolRequiresMigration
        | PrivateBazaarWorkerError::SpoolScopeMismatch
        | PrivateBazaarWorkerError::CursorOverflow
        | PrivateBazaarWorkerError::ProcessedCountOverflow
        | PrivateBazaarWorkerError::UnfinalizedEvidence
        | PrivateBazaarWorkerError::UnsupportedReceiptField(_)
        | PrivateBazaarWorkerError::ReceiptCodec(_)
        | PrivateBazaarWorkerError::DuplicateTarget
        | PrivateBazaarWorkerError::ClaimMismatch
        | PrivateBazaarWorkerError::PublishedClaimMismatch
        | PrivateBazaarWorkerError::ClaimMissingAfterApply
        | PrivateBazaarWorkerError::Corrupt(_)
        | PrivateBazaarWorkerError::InjectedAfterTargetDispatch
        // A refused private-book relation, commitment binding, or public
        // settlement join is Integrity, therefore NOT retryable: a worker that
        // backed off and retried a tampered witness would be grinding toward
        // acceptance. It stays refused until an operator looks at it.
        | PrivateBazaarWorkerError::PrivateClearingRefused(_)
        | PrivateBazaarWorkerError::SupervisorAlreadyRunning => {
            PrivateBazaarWorkerFaultClass::Integrity
        }
    }
}

fn retryable_fault(fault: PrivateBazaarWorkerFaultClass) -> bool {
    matches!(
        fault,
        PrivateBazaarWorkerFaultClass::LiveMarketUnavailable
            | PrivateBazaarWorkerFaultClass::TargetUnavailable
            | PrivateBazaarWorkerFaultClass::Storage
    )
}

#[derive(Debug)]
pub enum PrivateBazaarWorkerServiceError {
    Config(&'static str),
    InvalidMillis(&'static str),
    NoTargets,
    TargetRegistry,
    Worker(PrivateBazaarWorkerError),
    ThreadSpawn,
    ThreadPanicked,
}

impl From<PrivateBazaarWorkerError> for PrivateBazaarWorkerServiceError {
    fn from(error: PrivateBazaarWorkerError) -> Self {
        Self::Worker(error)
    }
}

impl std::fmt::Display for PrivateBazaarWorkerServiceError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "private Bazaar worker service refused: {self:?}")
    }
}

impl std::error::Error for PrivateBazaarWorkerServiceError {}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_types::CellId;

    #[test]
    fn availability_backs_off_but_contract_and_integrity_fault() {
        for error in [
            PrivateBazaarWorkerError::StaleLiveMarket,
            PrivateBazaarWorkerError::TargetNotInstalled(CellId([0x11; 32])),
            PrivateBazaarWorkerError::Io {
                operation: "test availability",
                detail: "unavailable".to_owned(),
            },
        ] {
            assert!(retryable_fault(classify_worker_error(&error)));
        }
        for error in [
            PrivateBazaarWorkerError::SpoolFork {
                expected: 2,
                found: 1,
            },
            PrivateBazaarWorkerError::ClaimMismatch,
            PrivateBazaarWorkerError::SourceExceededBound {
                found: 33,
                limit: 32,
            },
        ] {
            assert!(!retryable_fault(classify_worker_error(&error)));
        }
    }
}
