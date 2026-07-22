//! Durable, globally one-shot authority for a private Bazaar game consequence.
//!
//! The private clearing receipt and the target game are different authority
//! domains.  This module joins them without treating a public receipt, a JSON
//! carrier, or a caller-provided callback result as authority:
//!
//! * [`PrivateBazaarExecutorAuthority`] is minted only after rejoining a private
//!   clearing receipt to the exact live settled market receipt and rebuilding
//!   the exact guild allocation.
//! * `source_use_id` contains no target or reward.  A durable reservation of it
//!   therefore burns one private clearing globally; choosing another game,
//!   target, method, or reward cannot manufacture a fresh replay key.
//! * `operation_id` additionally binds the allocation, exact target cell,
//!   method, event topic, reward opening, expected pre-value, federation, and
//!   executor verification key.
//! * [`PrivateBazaarAuthorityStore`] moves a fixed-schema file record through
//!   `Prepared -> Dispatching -> Applied -> Committed`.  `Dispatching` is
//!   replay-blocking: after a crash the host must look up the exact operation in
//!   the target engine and call `recover_applied`; it must never redispatch.
//! * an `Applied` record is accepted only from a final, correctly signed
//!   executor receipt containing exactly one event for the configured topic,
//!   target, operation id, pre-value, reward amount, and post-value.
//!
//! The files authenticate fixed semantic records, not incidental Rust/Lean
//! transport bytes.  They are an operator-custodied durability boundary, not a
//! portable proof against a host that can rewrite its whole data directory.

use std::fs::{self, File, OpenOptions};
use std::io::{self, Read, Write};
use std::path::{Path, PathBuf};

use dregg_app_framework::{CellId, TurnReceipt, field_from_u64};
use dregg_turn::{Finality, verify_receipt_signature_with_keys};

use crate::DarkBazaarSession;
use crate::private_bazaar_journey::{PrivateBazaarMarketIdentity, PrivateBazaarRaidPolicy};
use crate::private_clearing::PrivateClearingReceipt;
use crate::private_clearing_consequence::PrivateClearingConsequenceSource;
use crate::private_clearing_guild_allocation::{
    PrivateClearingGuildAllocation, PrivateClearingGuildAllocationError,
};

const SOURCE_USE_DOMAIN: &str = "dregg.private-bazaar-global-source-use.v1";
const OPERATION_DOMAIN: &str = "dregg.private-bazaar-exact-operation.v1";
const AUTHORITY_DOMAIN: &str = "dregg.private-bazaar-executor-authority.v1";
const EFFECT_DOMAIN: &str = "dregg.private-bazaar-exact-effect.v1";

const SOURCE_MAGIC: &[u8; 8] = b"DBSRC001";
const RECORD_MAGIC: &[u8; 8] = b"DBOP0001";
const SOURCE_RECORD_LEN: usize = 8 + 32 + 32 + 32;
const OPERATION_RECORD_LEN: usize = 8 + 1 + (8 * 32);
const MAX_METHOD_BYTES: usize = 256;
const MAX_REWARD_KIND_BYTES: usize = 256;

/// Exact engine effect assembled by the trusted game adapter before dispatch.
///
/// Target, method, topic, reward kind, and amount are rechecked against the
/// independently loaded deployment policy when authority is minted.
/// `expected_before` is necessarily dynamic: the concrete adapter must derive
/// it from the target engine's durable state, never from a public request. A
/// stale value makes the executor refuse and leaves the already sealed outbox
/// `Dispatching` (fail-closed); it is not a retry knob.
///
/// `event_topic` is the executor event emitted in the same turn as the state
/// mutation.  Its exact data schema is eight 32-bit lanes of `operation_id`,
/// followed by `expected_before`, `reward_amount`, and `expected_after`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PrivateBazaarExactEffect {
    target_cell: CellId,
    method: String,
    event_topic: [u8; 32],
    reward_kind: String,
    reward_amount: u64,
    expected_before: u64,
}

impl PrivateBazaarExactEffect {
    pub fn new(
        target_cell: CellId,
        method: impl Into<String>,
        event_topic: [u8; 32],
        reward_kind: impl Into<String>,
        reward_amount: u64,
        expected_before: u64,
    ) -> Result<Self, PrivateBazaarAuthorityError> {
        let method = method.into();
        let reward_kind = reward_kind.into();
        if target_cell.0 == [0; 32] {
            return Err(PrivateBazaarAuthorityError::InvalidPolicy(
                "target cell is zero",
            ));
        }
        validate_text("method", &method, MAX_METHOD_BYTES)?;
        validate_text("reward kind", &reward_kind, MAX_REWARD_KIND_BYTES)?;
        if event_topic == [0; 32] {
            return Err(PrivateBazaarAuthorityError::InvalidPolicy(
                "event topic is zero",
            ));
        }
        if reward_amount == 0 {
            return Err(PrivateBazaarAuthorityError::InvalidPolicy(
                "reward amount is zero",
            ));
        }
        expected_before.checked_add(reward_amount).ok_or(
            PrivateBazaarAuthorityError::InvalidPolicy("reward overflows target value"),
        )?;
        Ok(Self {
            target_cell,
            method,
            event_topic,
            reward_kind,
            reward_amount,
            expected_before,
        })
    }

    pub const fn target_cell(&self) -> CellId {
        self.target_cell
    }

    pub fn method(&self) -> &str {
        &self.method
    }

    pub const fn event_topic(&self) -> [u8; 32] {
        self.event_topic
    }

    pub fn reward_kind(&self) -> &str {
        &self.reward_kind
    }

    pub const fn reward_amount(&self) -> u64 {
        self.reward_amount
    }

    pub const fn expected_before(&self) -> u64 {
        self.expected_before
    }

    pub fn expected_after(&self) -> u64 {
        self.expected_before
            .checked_add(self.reward_amount)
            .expect("validated at construction")
    }

    fn digest(&self) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new_derive_key(EFFECT_DOMAIN);
        hash_field(&mut hasher, &self.target_cell.0);
        hash_field(&mut hasher, self.method.as_bytes());
        hash_field(&mut hasher, &self.event_topic);
        hash_field(&mut hasher, self.reward_kind.as_bytes());
        hash_field(&mut hasher, &self.reward_amount.to_be_bytes());
        hash_field(&mut hasher, &self.expected_before.to_be_bytes());
        *hasher.finalize().as_bytes()
    }
}

/// Deployment-owned executor identity. Uploaded proof or action bytes never
/// select these values.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PrivateBazaarExecutorPolicy {
    executor_pubkey: [u8; 32],
    federation_id: [u8; 32],
}

impl PrivateBazaarExecutorPolicy {
    pub fn new(
        executor_pubkey: [u8; 32],
        federation_id: [u8; 32],
    ) -> Result<Self, PrivateBazaarAuthorityError> {
        if executor_pubkey == [0; 32] {
            return Err(PrivateBazaarAuthorityError::InvalidPolicy(
                "executor public key is zero",
            ));
        }
        if federation_id == [0; 32] {
            return Err(PrivateBazaarAuthorityError::InvalidPolicy(
                "executor federation is zero",
            ));
        }
        Ok(Self {
            executor_pubkey,
            federation_id,
        })
    }

    pub const fn executor_pubkey(&self) -> [u8; 32] {
        self.executor_pubkey
    }

    pub const fn federation_id(&self) -> [u8; 32] {
        self.federation_id
    }
}

/// Opaque authority joining one live verified clearing to one exact effect.
/// Fields are private and the type has no deserializer.
#[derive(Clone, Debug)]
pub struct PrivateBazaarExecutorAuthority {
    source_use_id: [u8; 32],
    operation_id: [u8; 32],
    authority_digest: [u8; 32],
    market_instance_id: [u8; 32],
    policy_id: [u8; 32],
    allocation_digest: [u8; 32],
    settlement_receipt_hash: [u8; 32],
    effect: PrivateBazaarExactEffect,
    policy: PrivateBazaarExecutorPolicy,
}

impl PrivateBazaarExecutorAuthority {
    /// Rejoin the claimed receipt to the exact receipt at the head of the live
    /// settled market, then rebuild the allocation from its verified source.
    /// Merely constructing a `PrivateClearingReceipt` lookalike is insufficient.
    pub fn from_verified_allocation(
        session: &DarkBazaarSession,
        receipt: &PrivateClearingReceipt,
        market: PrivateBazaarMarketIdentity,
        raid_policy: &PrivateBazaarRaidPolicy,
        effect: PrivateBazaarExactEffect,
    ) -> Result<Self, PrivateBazaarAuthorityError> {
        if !session.is_settled() {
            return Err(PrivateBazaarAuthorityError::MarketNotSettled);
        }
        if receipt.statement.session != session.private_proof_session()
            || market.proof_session() != session.private_proof_session()
            || market.digest() != market_instance_id(session, raid_policy.pin().deployment_id())?
            || receipt.statement.v_star != 1
            || session.winning_actor() != Some(&receipt.winner)
            || session
                .clearing()
                .and_then(|clearing| u32::try_from(clearing.price()).ok())
                != Some(receipt.statement.p_star)
            || !session
                .clearing()
                .is_some_and(|clearing| clearing.conserved())
        {
            return Err(PrivateBazaarAuthorityError::ReceiptDoesNotMatchMarket);
        }

        let live_receipt = session
            .market
            .receipts
            .last()
            .ok_or(PrivateBazaarAuthorityError::MissingSettlementReceipt)?;
        let settlement_receipt_hash = receipt.settlement_turn.receipt_hash();
        if live_receipt.receipt_hash() != settlement_receipt_hash
            || live_receipt.turn_hash != receipt.settlement_turn.turn_hash
            || receipt.settlement_turn.turn_hash == [0; 32]
        {
            return Err(PrivateBazaarAuthorityError::ReceiptDoesNotMatchMarket);
        }

        let source = PrivateClearingConsequenceSource::from_verified_receipt(receipt)
            .map_err(|error| PrivateBazaarAuthorityError::Source(error.to_string()))?;
        let rebuilt = PrivateClearingGuildAllocation::new(
            source,
            raid_policy.roster().clone(),
            raid_policy.pin().expected_roster_commitment(),
            raid_policy.reward().clone(),
        )?;
        if effect.target_cell != rebuilt.selected_member().character_cell
            || effect.reward_kind != rebuilt.reward().kind
            || effect.reward_amount != rebuilt.reward().amount
            || effect.method != raid_policy.pin().reward_method()
            || effect.event_topic != raid_policy.pin().reward_event_topic()
        {
            return Err(PrivateBazaarAuthorityError::EffectMismatch);
        }

        let policy = PrivateBazaarExecutorPolicy::new(
            raid_policy.pin().executor_pubkey(),
            raid_policy.pin().executor_federation(),
        )?;
        let market_instance_id = market.digest();
        let policy_id = raid_policy.policy_id();
        let source_use_id = source_use_id(receipt, settlement_receipt_hash, market_instance_id);
        let allocation_digest = rebuilt.allocation_digest();
        let operation_id = operation_id(
            source_use_id,
            market_instance_id,
            policy_id,
            allocation_digest,
            &effect,
            policy,
        );
        let authority_digest = authority_digest(
            source_use_id,
            operation_id,
            market_instance_id,
            policy_id,
            allocation_digest,
            settlement_receipt_hash,
            &effect,
            policy,
        );
        Ok(Self {
            source_use_id,
            operation_id,
            authority_digest,
            market_instance_id,
            policy_id,
            allocation_digest,
            settlement_receipt_hash,
            effect,
            policy,
        })
    }

    /// Global one-shot key for the verified source. It deliberately excludes
    /// target, policy, method, and reward.
    pub const fn source_use_id(&self) -> [u8; 32] {
        self.source_use_id
    }

    /// Exact operation key including the full effect and executor policy.
    pub const fn operation_id(&self) -> [u8; 32] {
        self.operation_id
    }

    pub const fn authority_digest(&self) -> [u8; 32] {
        self.authority_digest
    }

    pub const fn market_instance_id(&self) -> [u8; 32] {
        self.market_instance_id
    }

    pub const fn policy_id(&self) -> [u8; 32] {
        self.policy_id
    }

    pub const fn allocation_digest(&self) -> [u8; 32] {
        self.allocation_digest
    }

    pub const fn settlement_receipt_hash(&self) -> [u8; 32] {
        self.settlement_receipt_hash
    }

    pub fn effect(&self) -> &PrivateBazaarExactEffect {
        &self.effect
    }

    pub const fn policy(&self) -> PrivateBazaarExecutorPolicy {
        self.policy
    }

    /// Rejoin this opaque value to the still-live market and independently
    /// loaded deployment policy. This is the check a journey performs before
    /// accepting a committed effect into its public projection.
    pub fn matches_source(
        &self,
        session: &DarkBazaarSession,
        receipt: &PrivateClearingReceipt,
        market: PrivateBazaarMarketIdentity,
        raid_policy: &PrivateBazaarRaidPolicy,
    ) -> bool {
        Self::from_verified_allocation(session, receipt, market, raid_policy, self.effect.clone())
            .is_ok_and(|rebuilt| {
                rebuilt.source_use_id == self.source_use_id
                    && rebuilt.operation_id == self.operation_id
                    && rebuilt.authority_digest == self.authority_digest
            })
    }

    fn matches_record(&self, record: &OperationRecord) -> bool {
        record.source_use_id == self.source_use_id
            && record.operation_id == self.operation_id
            && record.authority_digest == self.authority_digest
            && record.settlement_receipt_hash == self.settlement_receipt_hash
            && record.effect_digest == self.effect.digest()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum PrivateBazaarAuthorityPhase {
    Prepared = 1,
    Dispatching = 2,
    Applied = 3,
    Committed = 4,
}

impl TryFrom<u8> for PrivateBazaarAuthorityPhase {
    type Error = PrivateBazaarAuthorityError;

    fn try_from(value: u8) -> Result<Self, Self::Error> {
        match value {
            1 => Ok(Self::Prepared),
            2 => Ok(Self::Dispatching),
            3 => Ok(Self::Applied),
            4 => Ok(Self::Committed),
            _ => Err(PrivateBazaarAuthorityError::Corrupt(
                "invalid operation phase".to_owned(),
            )),
        }
    }
}

/// Opaque token issued only by the durable `Prepared -> Dispatching` CAS.
/// Possessing an authority without this token is insufficient to dispatch.
#[derive(Debug)]
pub struct PrivateBazaarDispatchToken {
    authority: PrivateBazaarExecutorAuthority,
}

impl PrivateBazaarDispatchToken {
    pub const fn operation_id(&self) -> [u8; 32] {
        self.authority.operation_id
    }

    pub fn effect(&self) -> &PrivateBazaarExactEffect {
        &self.authority.effect
    }
}

/// Opaque, reloadable authority that an exact signed effect was durably
/// observed and the global source reservation was committed.
#[derive(Clone, Debug)]
pub struct CommittedPrivateBazaarEffect {
    authority: PrivateBazaarExecutorAuthority,
    game_receipt_hash: [u8; 32],
    game_turn_hash: [u8; 32],
    game_post_state: [u8; 32],
}

impl CommittedPrivateBazaarEffect {
    pub const fn operation_id(&self) -> [u8; 32] {
        self.authority.operation_id
    }

    pub const fn source_use_id(&self) -> [u8; 32] {
        self.authority.source_use_id
    }

    pub fn effect(&self) -> &PrivateBazaarExactEffect {
        &self.authority.effect
    }

    pub const fn game_receipt_hash(&self) -> [u8; 32] {
        self.game_receipt_hash
    }

    pub const fn game_turn_hash(&self) -> [u8; 32] {
        self.game_turn_hash
    }

    pub const fn game_post_state(&self) -> [u8; 32] {
        self.game_post_state
    }

    pub fn matches_authority(&self, authority: &PrivateBazaarExecutorAuthority) -> bool {
        self.authority.source_use_id == authority.source_use_id
            && self.authority.operation_id == authority.operation_id
            && self.authority.authority_digest == authority.authority_digest
            && self.authority.settlement_receipt_hash == authority.settlement_receipt_hash
            && self.authority.effect == authority.effect
            && self.authority.policy == authority.policy
    }
}

/// Cloneable handle to one host-owned fixed-schema authority journal.
#[derive(Clone, Debug)]
pub struct PrivateBazaarAuthorityStore {
    root: PathBuf,
}

impl PrivateBazaarAuthorityStore {
    pub fn open(root: impl AsRef<Path>) -> Result<Self, PrivateBazaarAuthorityError> {
        let root = root.as_ref().to_path_buf();
        fs::create_dir_all(root.join("sources"))
            .map_err(|error| PrivateBazaarAuthorityError::io("create source directory", error))?;
        fs::create_dir_all(root.join("operations")).map_err(|error| {
            PrivateBazaarAuthorityError::io("create operation directory", error)
        })?;
        sync_directory(&root)?;
        Ok(Self { root })
    }

    /// Atomically reserve the source globally, then write the exact prepared
    /// operation. Repeating the identical prepare is idempotent; a different
    /// operation for the same source is refused even after restart.
    pub fn prepare(
        &self,
        authority: &PrivateBazaarExecutorAuthority,
    ) -> Result<PrivateBazaarAuthorityPhase, PrivateBazaarAuthorityError> {
        let source = SourceRecord::from_authority(authority);
        write_new_or_verify(&self.source_path(authority.source_use_id), &source.encode())?;

        let operation = OperationRecord::prepared(authority);
        let path = self.operation_path(authority.operation_id);
        match OpenOptions::new().write(true).create_new(true).open(&path) {
            Ok(mut file) => {
                file.write_all(&operation.encode()).map_err(|error| {
                    PrivateBazaarAuthorityError::io("write prepared operation", error)
                })?;
                file.sync_all().map_err(|error| {
                    PrivateBazaarAuthorityError::io("sync prepared operation", error)
                })?;
                sync_parent(&path)?;
            }
            Err(error) if error.kind() == io::ErrorKind::AlreadyExists => {
                // Any phase of this exact operation is an idempotent prepare;
                // it is never rewritten back to Prepared.
                self.load_exact(authority)?;
            }
            Err(error) => {
                return Err(PrivateBazaarAuthorityError::io(
                    "create prepared operation",
                    error,
                ));
            }
        }
        Ok(self.load_exact(authority)?.phase)
    }

    /// Seal the exact operation before calling the game engine. Any later
    /// retry observes `Dispatching` and must use recovery rather than dispatch.
    pub fn begin_dispatch(
        &self,
        authority: &PrivateBazaarExecutorAuthority,
    ) -> Result<PrivateBazaarDispatchToken, PrivateBazaarAuthorityError> {
        self.cas_phase(
            authority,
            PrivateBazaarAuthorityPhase::Prepared,
            PrivateBazaarAuthorityPhase::Dispatching,
            None,
        )?;
        Ok(PrivateBazaarDispatchToken {
            authority: authority.clone(),
        })
    }

    /// Observe the receipt returned by the just-dispatched engine call.
    /// `verify_engine_state` is the concrete engine's postcondition check (for
    /// example the hero engine also checks its current XP equals the committed
    /// `expected_after`). It runs only after generic finality/signature/event
    /// verification and before the durable `Applied` CAS.
    pub fn record_applied<F>(
        &self,
        dispatch: PrivateBazaarDispatchToken,
        receipt: &TurnReceipt,
        verify_engine_state: F,
    ) -> Result<(), PrivateBazaarAuthorityError>
    where
        F: FnOnce(&TurnReceipt) -> bool,
    {
        self.verify_applied_receipt(&dispatch.authority, receipt, verify_engine_state)?;
        self.cas_phase(
            &dispatch.authority,
            PrivateBazaarAuthorityPhase::Dispatching,
            PrivateBazaarAuthorityPhase::Applied,
            Some(AppliedReceipt::from(receipt)),
        )?;
        Ok(())
    }

    /// Crash recovery for an already sealed `Dispatching` operation. The host
    /// must retrieve the receipt by the exact operation id from the target
    /// engine; this method never invokes the engine or redispatches.
    pub fn recover_applied<F>(
        &self,
        authority: &PrivateBazaarExecutorAuthority,
        receipt: &TurnReceipt,
        verify_engine_state: F,
    ) -> Result<(), PrivateBazaarAuthorityError>
    where
        F: FnOnce(&TurnReceipt) -> bool,
    {
        self.verify_applied_receipt(authority, receipt, verify_engine_state)?;
        self.cas_phase(
            authority,
            PrivateBazaarAuthorityPhase::Dispatching,
            PrivateBazaarAuthorityPhase::Applied,
            Some(AppliedReceipt::from(receipt)),
        )?;
        Ok(())
    }

    /// Promote the exact applied record to its terminal durable state. The
    /// repeated exact promotion is idempotent.
    pub fn commit(
        &self,
        authority: &PrivateBazaarExecutorAuthority,
    ) -> Result<CommittedPrivateBazaarEffect, PrivateBazaarAuthorityError> {
        let current = self.load_exact(authority)?;
        if current.phase != PrivateBazaarAuthorityPhase::Committed {
            self.cas_phase(
                authority,
                PrivateBazaarAuthorityPhase::Applied,
                PrivateBazaarAuthorityPhase::Committed,
                None,
            )?;
        }
        self.load_committed(authority)
    }

    pub fn load_committed(
        &self,
        authority: &PrivateBazaarExecutorAuthority,
    ) -> Result<CommittedPrivateBazaarEffect, PrivateBazaarAuthorityError> {
        let record = self.load_exact(authority)?;
        if record.phase != PrivateBazaarAuthorityPhase::Committed {
            return Err(PrivateBazaarAuthorityError::WrongPhase {
                expected: PrivateBazaarAuthorityPhase::Committed,
                found: record.phase,
            });
        }
        if record.game_receipt_hash == [0; 32]
            || record.game_turn_hash == [0; 32]
            || record.game_post_state == [0; 32]
        {
            return Err(PrivateBazaarAuthorityError::Corrupt(
                "committed operation has empty executor receipt fields".to_owned(),
            ));
        }
        Ok(CommittedPrivateBazaarEffect {
            authority: authority.clone(),
            game_receipt_hash: record.game_receipt_hash,
            game_turn_hash: record.game_turn_hash,
            game_post_state: record.game_post_state,
        })
    }

    pub fn phase(
        &self,
        authority: &PrivateBazaarExecutorAuthority,
    ) -> Result<PrivateBazaarAuthorityPhase, PrivateBazaarAuthorityError> {
        Ok(self.load_exact(authority)?.phase)
    }

    fn verify_applied_receipt<F>(
        &self,
        authority: &PrivateBazaarExecutorAuthority,
        receipt: &TurnReceipt,
        verify_engine_state: F,
    ) -> Result<(), PrivateBazaarAuthorityError>
    where
        F: FnOnce(&TurnReceipt) -> bool,
    {
        let effect = &authority.effect;
        let policy = authority.policy;
        let expected_data = effect_event_data(authority.operation_id, effect);
        let matching_topic: Vec<_> = receipt
            .emitted_events
            .iter()
            .filter(|event| event.topic == effect.event_topic)
            .collect();
        if receipt.finality != Finality::Final
            || receipt.federation_id != policy.federation_id
            || receipt.action_count != 1
            || receipt.turn_hash == [0; 32]
            || receipt.effects_hash == [0; 32]
            || receipt.pre_state_hash == receipt.post_state_hash
            || matching_topic.len() != 1
            || matching_topic[0].cell != effect.target_cell
            || matching_topic[0].data != expected_data
        {
            return Err(PrivateBazaarAuthorityError::InvalidExecutorReceipt(
                "finality, route, shape, or exact effect event mismatch",
            ));
        }
        verify_receipt_signature_with_keys(receipt, &[policy.executor_pubkey]).map_err(|_| {
            PrivateBazaarAuthorityError::InvalidExecutorReceipt(
                "receipt is not signed by the deployment executor",
            )
        })?;
        if !verify_engine_state(receipt) {
            return Err(PrivateBazaarAuthorityError::InvalidExecutorReceipt(
                "target engine postcondition did not verify",
            ));
        }
        Ok(())
    }

    fn cas_phase(
        &self,
        authority: &PrivateBazaarExecutorAuthority,
        expected: PrivateBazaarAuthorityPhase,
        next: PrivateBazaarAuthorityPhase,
        applied: Option<AppliedReceipt>,
    ) -> Result<(), PrivateBazaarAuthorityError> {
        let path = self.operation_path(authority.operation_id);
        let lock_path = path.with_extension("cas");
        let lock = OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&lock_path)
            .map_err(|error| {
                if error.kind() == io::ErrorKind::AlreadyExists {
                    PrivateBazaarAuthorityError::CasBusyOrCrashed
                } else {
                    PrivateBazaarAuthorityError::io("create operation CAS lock", error)
                }
            })?;
        lock.sync_all()
            .map_err(|error| PrivateBazaarAuthorityError::io("sync operation CAS lock", error))?;

        let result = (|| {
            let mut record = read_operation(&path)?;
            if !authority.matches_record(&record) {
                return Err(PrivateBazaarAuthorityError::AuthorityMismatch);
            }
            if record.phase != expected {
                return Err(PrivateBazaarAuthorityError::WrongPhase {
                    expected,
                    found: record.phase,
                });
            }
            record.phase = next;
            if let Some(applied) = applied {
                record.game_receipt_hash = applied.receipt_hash;
                record.game_turn_hash = applied.turn_hash;
                record.game_post_state = applied.post_state;
            }
            atomic_replace(&path, &record.encode())
        })();

        // An ordinary refusal did not crash and may release the lock. If the
        // process dies before here, the surviving lock wedges the operation
        // fail-closed for operator reconciliation rather than reopening it.
        let unlock = fs::remove_file(&lock_path)
            .map_err(|error| PrivateBazaarAuthorityError::io("remove operation CAS lock", error));
        result.and(unlock)
    }

    fn load_exact(
        &self,
        authority: &PrivateBazaarExecutorAuthority,
    ) -> Result<OperationRecord, PrivateBazaarAuthorityError> {
        let source = read_source(&self.source_path(authority.source_use_id))?;
        if source != SourceRecord::from_authority(authority) {
            return Err(PrivateBazaarAuthorityError::SourceAlreadyReserved);
        }
        let record = read_operation(&self.operation_path(authority.operation_id))?;
        if !authority.matches_record(&record) {
            return Err(PrivateBazaarAuthorityError::AuthorityMismatch);
        }
        Ok(record)
    }

    fn source_path(&self, source_use_id: [u8; 32]) -> PathBuf {
        self.root
            .join("sources")
            .join(format!("{}.source", hex32(source_use_id)))
    }

    fn operation_path(&self, operation_id: [u8; 32]) -> PathBuf {
        self.root
            .join("operations")
            .join(format!("{}.operation", hex32(operation_id)))
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct SourceRecord {
    source_use_id: [u8; 32],
    operation_id: [u8; 32],
    authority_digest: [u8; 32],
}

impl SourceRecord {
    fn from_authority(authority: &PrivateBazaarExecutorAuthority) -> Self {
        Self {
            source_use_id: authority.source_use_id,
            operation_id: authority.operation_id,
            authority_digest: authority.authority_digest,
        }
    }

    fn encode(self) -> Vec<u8> {
        let mut out = Vec::with_capacity(SOURCE_RECORD_LEN);
        out.extend_from_slice(SOURCE_MAGIC);
        out.extend_from_slice(&self.source_use_id);
        out.extend_from_slice(&self.operation_id);
        out.extend_from_slice(&self.authority_digest);
        out
    }

    fn decode(bytes: &[u8]) -> Result<Self, PrivateBazaarAuthorityError> {
        if bytes.len() != SOURCE_RECORD_LEN || &bytes[..8] != SOURCE_MAGIC {
            return Err(PrivateBazaarAuthorityError::Corrupt(
                "source reservation schema/version mismatch".to_owned(),
            ));
        }
        Ok(Self {
            source_use_id: array_at(bytes, 8),
            operation_id: array_at(bytes, 40),
            authority_digest: array_at(bytes, 72),
        })
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct OperationRecord {
    phase: PrivateBazaarAuthorityPhase,
    source_use_id: [u8; 32],
    operation_id: [u8; 32],
    authority_digest: [u8; 32],
    settlement_receipt_hash: [u8; 32],
    effect_digest: [u8; 32],
    game_receipt_hash: [u8; 32],
    game_turn_hash: [u8; 32],
    game_post_state: [u8; 32],
}

impl OperationRecord {
    fn prepared(authority: &PrivateBazaarExecutorAuthority) -> Self {
        Self {
            phase: PrivateBazaarAuthorityPhase::Prepared,
            source_use_id: authority.source_use_id,
            operation_id: authority.operation_id,
            authority_digest: authority.authority_digest,
            settlement_receipt_hash: authority.settlement_receipt_hash,
            effect_digest: authority.effect.digest(),
            game_receipt_hash: [0; 32],
            game_turn_hash: [0; 32],
            game_post_state: [0; 32],
        }
    }

    fn encode(self) -> Vec<u8> {
        let mut out = Vec::with_capacity(OPERATION_RECORD_LEN);
        out.extend_from_slice(RECORD_MAGIC);
        out.push(self.phase as u8);
        for field in [
            self.source_use_id,
            self.operation_id,
            self.authority_digest,
            self.settlement_receipt_hash,
            self.effect_digest,
            self.game_receipt_hash,
            self.game_turn_hash,
            self.game_post_state,
        ] {
            out.extend_from_slice(&field);
        }
        out
    }

    fn decode(bytes: &[u8]) -> Result<Self, PrivateBazaarAuthorityError> {
        if bytes.len() != OPERATION_RECORD_LEN || &bytes[..8] != RECORD_MAGIC {
            return Err(PrivateBazaarAuthorityError::Corrupt(
                "operation record schema/version mismatch".to_owned(),
            ));
        }
        let record = Self {
            phase: bytes[8].try_into()?,
            source_use_id: array_at(bytes, 9),
            operation_id: array_at(bytes, 41),
            authority_digest: array_at(bytes, 73),
            settlement_receipt_hash: array_at(bytes, 105),
            effect_digest: array_at(bytes, 137),
            game_receipt_hash: array_at(bytes, 169),
            game_turn_hash: array_at(bytes, 201),
            game_post_state: array_at(bytes, 233),
        };
        let game_fields = [
            record.game_receipt_hash,
            record.game_turn_hash,
            record.game_post_state,
        ];
        let canonical = match record.phase {
            PrivateBazaarAuthorityPhase::Prepared | PrivateBazaarAuthorityPhase::Dispatching => {
                game_fields.iter().all(|field| *field == [0; 32])
            }
            PrivateBazaarAuthorityPhase::Applied | PrivateBazaarAuthorityPhase::Committed => {
                game_fields.iter().all(|field| *field != [0; 32])
            }
        };
        if !canonical {
            return Err(PrivateBazaarAuthorityError::Corrupt(
                "operation phase and executor receipt fields are noncanonical".to_owned(),
            ));
        }
        Ok(record)
    }
}

#[derive(Clone, Copy)]
struct AppliedReceipt {
    receipt_hash: [u8; 32],
    turn_hash: [u8; 32],
    post_state: [u8; 32],
}

impl From<&TurnReceipt> for AppliedReceipt {
    fn from(receipt: &TurnReceipt) -> Self {
        Self {
            receipt_hash: receipt.receipt_hash(),
            turn_hash: receipt.turn_hash,
            post_state: receipt.post_state_hash,
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum PrivateBazaarAuthorityError {
    InvalidPolicy(&'static str),
    MarketNotSettled,
    MissingSettlementReceipt,
    ReceiptDoesNotMatchMarket,
    AllocationMismatch,
    EffectMismatch,
    Source(String),
    Allocation(String),
    SourceAlreadyReserved,
    AuthorityMismatch,
    InvalidExecutorReceipt(&'static str),
    WrongPhase {
        expected: PrivateBazaarAuthorityPhase,
        found: PrivateBazaarAuthorityPhase,
    },
    CasBusyOrCrashed,
    Corrupt(String),
    Io {
        operation: &'static str,
        detail: String,
    },
}

impl PrivateBazaarAuthorityError {
    fn io(operation: &'static str, error: io::Error) -> Self {
        Self::Io {
            operation,
            detail: error.to_string(),
        }
    }
}

impl From<PrivateClearingGuildAllocationError> for PrivateBazaarAuthorityError {
    fn from(error: PrivateClearingGuildAllocationError) -> Self {
        Self::Allocation(error.to_string())
    }
}

impl std::fmt::Display for PrivateBazaarAuthorityError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "private Bazaar authority refused: {self:?}")
    }
}

impl std::error::Error for PrivateBazaarAuthorityError {}

fn source_use_id(
    receipt: &PrivateClearingReceipt,
    receipt_hash: [u8; 32],
    market_instance_id: [u8; 32],
) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key(SOURCE_USE_DOMAIN);
    hash_field(&mut hasher, &market_instance_id);
    hash_field(&mut hasher, &receipt.statement.session.to_be_bytes());
    hash_field(&mut hasher, &receipt.statement.rule.to_be_bytes());
    for lane in receipt.statement.order_root {
        hash_field(&mut hasher, &lane.to_be_bytes());
    }
    hash_field(&mut hasher, &receipt.statement.p_star.to_be_bytes());
    hash_field(&mut hasher, &receipt.statement.v_star.to_be_bytes());
    hash_field(&mut hasher, receipt.winner.0.as_bytes());
    hash_field(&mut hasher, &receipt.settlement_turn.turn_hash);
    hash_field(&mut hasher, &receipt_hash);
    *hasher.finalize().as_bytes()
}

fn operation_id(
    source_use_id: [u8; 32],
    market_instance_id: [u8; 32],
    policy_id: [u8; 32],
    allocation_digest: [u8; 32],
    effect: &PrivateBazaarExactEffect,
    policy: PrivateBazaarExecutorPolicy,
) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key(OPERATION_DOMAIN);
    for field in [
        source_use_id,
        market_instance_id,
        policy_id,
        allocation_digest,
        effect.digest(),
        policy.executor_pubkey,
        policy.federation_id,
    ] {
        hash_field(&mut hasher, &field);
    }
    *hasher.finalize().as_bytes()
}

fn authority_digest(
    source_use_id: [u8; 32],
    operation_id: [u8; 32],
    market_instance_id: [u8; 32],
    policy_id: [u8; 32],
    allocation_digest: [u8; 32],
    settlement_receipt_hash: [u8; 32],
    effect: &PrivateBazaarExactEffect,
    policy: PrivateBazaarExecutorPolicy,
) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key(AUTHORITY_DOMAIN);
    for field in [
        source_use_id,
        operation_id,
        market_instance_id,
        policy_id,
        allocation_digest,
        settlement_receipt_hash,
        effect.digest(),
        policy.executor_pubkey,
        policy.federation_id,
    ] {
        hash_field(&mut hasher, &field);
    }
    *hasher.finalize().as_bytes()
}

fn effect_event_data(
    operation_id: [u8; 32],
    effect: &PrivateBazaarExactEffect,
) -> Vec<dregg_app_framework::FieldElement> {
    let mut data = Vec::with_capacity(11);
    for chunk in operation_id.chunks_exact(4) {
        data.push(field_from_u64(u32::from_be_bytes(
            chunk.try_into().expect("four-byte operation lane"),
        ) as u64));
    }
    data.push(field_from_u64(effect.expected_before));
    data.push(field_from_u64(effect.reward_amount));
    data.push(field_from_u64(effect.expected_after()));
    data
}

fn hash_field(hasher: &mut blake3::Hasher, field: &[u8]) {
    hasher.update(&(field.len() as u64).to_be_bytes());
    hasher.update(field);
}

fn validate_text(
    name: &'static str,
    value: &str,
    max: usize,
) -> Result<(), PrivateBazaarAuthorityError> {
    if value.is_empty() {
        return Err(PrivateBazaarAuthorityError::InvalidPolicy(match name {
            "method" => "method is empty",
            _ => "reward kind is empty",
        }));
    }
    if value.len() > max {
        return Err(PrivateBazaarAuthorityError::InvalidPolicy(match name {
            "method" => "method is too long",
            _ => "reward kind is too long",
        }));
    }
    Ok(())
}

fn market_instance_id(
    session: &DarkBazaarSession,
    deployment_id: [u8; 32],
) -> Result<[u8; 32], PrivateBazaarAuthorityError> {
    let auction_cell = session
        .market
        .auction_cell
        .ok_or(PrivateBazaarAuthorityError::ReceiptDoesNotMatchMarket)?;
    let seller = session
        .market
        .seller
        .as_ref()
        .ok_or(PrivateBazaarAuthorityError::ReceiptDoesNotMatchMarket)?;
    let mut hasher =
        blake3::Hasher::new_derive_key("dreggnet-market/private-bazaar-market-instance/v2");
    hasher.update(&deployment_id);
    hasher.update(auction_cell.as_bytes());
    hasher.update(&session.market.seed.to_be_bytes());
    hasher.update(&session.market.reserve.to_be_bytes());
    hasher.update(&(seller.0.len() as u64).to_be_bytes());
    hasher.update(seller.0.as_bytes());
    Ok(*hasher.finalize().as_bytes())
}

fn write_new_or_verify(path: &Path, expected: &[u8]) -> Result<(), PrivateBazaarAuthorityError> {
    match OpenOptions::new().write(true).create_new(true).open(path) {
        Ok(mut file) => {
            file.write_all(expected)
                .map_err(|error| PrivateBazaarAuthorityError::io("write new record", error))?;
            file.sync_all()
                .map_err(|error| PrivateBazaarAuthorityError::io("sync new record", error))?;
            sync_parent(path)
        }
        Err(error) if error.kind() == io::ErrorKind::AlreadyExists => {
            let mut found = Vec::new();
            File::open(path)
                .and_then(|mut file| file.read_to_end(&mut found))
                .map_err(|error| PrivateBazaarAuthorityError::io("read existing record", error))?;
            if found == expected {
                Ok(())
            } else {
                Err(PrivateBazaarAuthorityError::SourceAlreadyReserved)
            }
        }
        Err(error) => Err(PrivateBazaarAuthorityError::io("create new record", error)),
    }
}

fn read_source(path: &Path) -> Result<SourceRecord, PrivateBazaarAuthorityError> {
    let bytes = fs::read(path)
        .map_err(|error| PrivateBazaarAuthorityError::io("read source reservation", error))?;
    SourceRecord::decode(&bytes)
}

fn read_operation(path: &Path) -> Result<OperationRecord, PrivateBazaarAuthorityError> {
    let bytes = fs::read(path)
        .map_err(|error| PrivateBazaarAuthorityError::io("read operation record", error))?;
    OperationRecord::decode(&bytes)
}

fn atomic_replace(path: &Path, bytes: &[u8]) -> Result<(), PrivateBazaarAuthorityError> {
    let temp = path.with_extension("next");
    let mut file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&temp)
        .map_err(|error| PrivateBazaarAuthorityError::io("create replacement record", error))?;
    file.write_all(bytes)
        .map_err(|error| PrivateBazaarAuthorityError::io("write replacement record", error))?;
    file.sync_all()
        .map_err(|error| PrivateBazaarAuthorityError::io("sync replacement record", error))?;
    fs::rename(&temp, path)
        .map_err(|error| PrivateBazaarAuthorityError::io("replace operation record", error))?;
    sync_parent(path)
}

fn sync_parent(path: &Path) -> Result<(), PrivateBazaarAuthorityError> {
    let parent = path.parent().ok_or_else(|| {
        PrivateBazaarAuthorityError::Corrupt("record path has no parent".to_owned())
    })?;
    sync_directory(parent)
}

fn sync_directory(path: &Path) -> Result<(), PrivateBazaarAuthorityError> {
    File::open(path)
        .and_then(|directory| directory.sync_all())
        .map_err(|error| PrivateBazaarAuthorityError::io("sync record directory", error))
}

fn array_at(bytes: &[u8], offset: usize) -> [u8; 32] {
    bytes[offset..offset + 32]
        .try_into()
        .expect("length checked before fixed record decode")
}

fn hex32(bytes: [u8; 32]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut out = String::with_capacity(64);
    for byte in bytes {
        out.push(HEX[(byte >> 4) as usize] as char);
        out.push(HEX[(byte & 0x0f) as usize] as char);
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fake_authority(source: u8, operation: u8) -> PrivateBazaarExecutorAuthority {
        let effect = PrivateBazaarExactEffect::new(
            CellId([9; 32]),
            "hero/gain_xp/private-bazaar/v1",
            [8; 32],
            "raid-xp/ashen-vault/v1",
            144,
            100,
        )
        .unwrap();
        PrivateBazaarExecutorAuthority {
            source_use_id: [source; 32],
            operation_id: [operation; 32],
            authority_digest: [operation.wrapping_add(1); 32],
            market_instance_id: [15; 32],
            policy_id: [16; 32],
            allocation_digest: [6; 32],
            settlement_receipt_hash: [7; 32],
            effect,
            policy: PrivateBazaarExecutorPolicy::new([4; 32], [5; 32]).unwrap(),
        }
    }

    #[test]
    fn global_source_reservation_refuses_target_or_reward_rebinding() {
        let directory = tempfile::tempdir().unwrap();
        let store = PrivateBazaarAuthorityStore::open(directory.path()).unwrap();
        let first = fake_authority(1, 2);
        let rebound = fake_authority(1, 3);

        assert_eq!(
            store.prepare(&first).unwrap(),
            PrivateBazaarAuthorityPhase::Prepared
        );
        assert_eq!(
            store.prepare(&first).unwrap(),
            PrivateBazaarAuthorityPhase::Prepared
        );
        assert_eq!(
            store.prepare(&rebound).unwrap_err(),
            PrivateBazaarAuthorityError::SourceAlreadyReserved
        );
    }

    #[test]
    fn dispatching_is_durable_and_never_reopened_after_restart() {
        let directory = tempfile::tempdir().unwrap();
        let authority = fake_authority(11, 12);
        let store = PrivateBazaarAuthorityStore::open(directory.path()).unwrap();
        store.prepare(&authority).unwrap();
        let token = store.begin_dispatch(&authority).unwrap();
        assert_eq!(token.operation_id(), authority.operation_id());
        drop(store);

        let restarted = PrivateBazaarAuthorityStore::open(directory.path()).unwrap();
        assert_eq!(
            restarted.phase(&authority).unwrap(),
            PrivateBazaarAuthorityPhase::Dispatching
        );
        assert_eq!(
            restarted.begin_dispatch(&authority).unwrap_err(),
            PrivateBazaarAuthorityError::WrongPhase {
                expected: PrivateBazaarAuthorityPhase::Prepared,
                found: PrivateBazaarAuthorityPhase::Dispatching,
            }
        );
    }

    #[test]
    fn malformed_fixed_records_fail_closed() {
        let directory = tempfile::tempdir().unwrap();
        let authority = fake_authority(21, 22);
        let store = PrivateBazaarAuthorityStore::open(directory.path()).unwrap();
        store.prepare(&authority).unwrap();
        fs::write(store.operation_path(authority.operation_id()), b"truncated").unwrap();

        assert!(matches!(
            store.phase(&authority),
            Err(PrivateBazaarAuthorityError::Corrupt(_))
        ));
    }
}
