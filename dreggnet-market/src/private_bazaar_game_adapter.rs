//! Concrete private-Bazaar consequence adapter for Dungeon hero XP.
//!
//! This is the only layer that turns the generic exact-effect authority into a
//! real game mutation.  The controller supplies no target value or reward
//! opening: the deployment policy supplies target routing/method/topic/reward,
//! and the adapter reads `xp` from the authoritative [`DungeonWorldCell`]
//! immediately before preparing the durable operation.
//!
//! Dispatch ordering is deliberately one-way:
//! `Prepared -> Dispatching` is durably CASed before the executor is called;
//! the signed/final exact-event receipt is then verified and recorded
//! `Applied -> Committed`; only the opaque committed authority can settle the
//! viewer-blind journey. A process that sees `Dispatching` after restart scans
//! the target world's immutable receipt chain for the exact operation and never
//! calls the executor again.

use std::fs::{self, File, OpenOptions};
use std::io::{self, Read, Write};
use std::path::{Path, PathBuf};

use dregg_app_framework::symbol;
use dungeon_on_dregg::progression::{
    DungeonWorldCell, PRIVATE_BAZAAR_XP_EVENT, PRIVATE_BAZAAR_XP_METHOD, gain_private_bazaar_xp,
    verify_private_bazaar_xp_receipt, verify_private_bazaar_xp_receipt_evidence,
};

use crate::DarkBazaarSession;
use crate::private_bazaar_authority::{
    PrivateBazaarAuthorityError, PrivateBazaarAuthorityPhase, PrivateBazaarAuthorityStore,
    PrivateBazaarExactEffect, PrivateBazaarExecutorAuthority, private_bazaar_source_use_id,
};
use crate::private_bazaar_journey::{
    PrivateBazaarJourneyError, PrivateBazaarPublicReceipt, PrivateBazaarRaidJourney,
};
use crate::private_clearing::PrivateClearingReceipt;

const LOOKUP_DOMAIN: &str = "dregg.private-bazaar-xp-adapter-lookup.v2";
const RECORD_DOMAIN: &str = "dregg.private-bazaar-xp-adapter-record.v2";
// v1 keyed recovery by timestamped receipt hash. Refuse it rather than
// silently aliasing it with the stable semantic-claim identity in v2.
const RECORD_MAGIC: &[u8; 8] = b"DBXP0002";
const RECORD_LEN: usize = 8 + (7 * 32) + 8 + 32;

/// Cloneable deployment-owned adapter. Both its semantic recovery record and
/// the generic authority journal are rooted beneath `root`.
#[derive(Clone, Debug)]
pub struct PrivateBazaarXpAdapter {
    root: PathBuf,
    authority_store: PrivateBazaarAuthorityStore,
}

impl PrivateBazaarXpAdapter {
    pub fn open(root: impl AsRef<Path>) -> Result<Self, PrivateBazaarGameAdapterError> {
        let root = root.as_ref().to_path_buf();
        fs::create_dir_all(root.join("xp-operations"))
            .map_err(|error| PrivateBazaarGameAdapterError::io("create XP journal", error))?;
        let authority_store = PrivateBazaarAuthorityStore::open(root.join("authority"))?;
        sync_directory(&root)?;
        Ok(Self {
            root,
            authority_store,
        })
    }

    /// Read the target's durable XP state and prepare exactly that absolute
    /// transition. `expected_before` is intentionally absent from this API.
    pub fn prepare(
        &self,
        journey: &PrivateBazaarRaidJourney,
        session: &DarkBazaarSession,
        private_receipt: &PrivateClearingReceipt,
        hero: &DungeonWorldCell,
    ) -> Result<PreparedPrivateBazaarXp, PrivateBazaarGameAdapterError> {
        journey.require_pending(session)?;
        validate_engine_policy(journey, hero)?;

        // The load-bearing target snapshot. No frontend/controller value enters
        // this lane; the same absolute value is persisted before source prepare.
        let expected_before = hero.read_var("xp");
        let authority = build_authority(journey, session, private_receipt, hero, expected_before)?;
        let record = XpOperationRecord::new(journey, &authority, hero, expected_before);
        write_new_or_verify(&self.record_path(record.lookup_id), &record.encode())?;

        let phase = self.authority_store.prepare(&authority)?;
        if phase != PrivateBazaarAuthorityPhase::Prepared {
            return Err(PrivateBazaarGameAdapterError::NeedsRecovery(phase));
        }
        Ok(PreparedPrivateBazaarXp {
            lookup_id: record.lookup_id,
            authority,
        })
    }

    /// Reconstruct the exact opaque authority after restart. The original
    /// target snapshot comes only from the adapter's checksummed fixed record;
    /// current XP is never substituted into the already reserved operation.
    pub fn resume(
        &self,
        journey: &PrivateBazaarRaidJourney,
        session: &DarkBazaarSession,
        private_receipt: &PrivateClearingReceipt,
        hero: &DungeonWorldCell,
    ) -> Result<ResumedPrivateBazaarXp, PrivateBazaarGameAdapterError> {
        journey.require_pending(session)?;
        validate_engine_policy(journey, hero)?;
        let lookup_id = lookup_id(journey, private_receipt);
        let record = read_record(&self.record_path(lookup_id))?;
        if record.lookup_id != lookup_id
            || record.market_instance_id != journey.market_identity().digest()
            || record.policy_id != journey.policy().policy_id()
            || record.target_cell != hero.cell_id().0
        {
            return Err(PrivateBazaarGameAdapterError::RecoveryRecordMismatch);
        }
        let authority = build_authority(
            journey,
            session,
            private_receipt,
            hero,
            record.expected_before,
        )?;
        if record.source_use_id != authority.source_use_id()
            || record.operation_id != authority.operation_id()
            || record.authority_digest != authority.authority_digest()
        {
            return Err(PrivateBazaarGameAdapterError::RecoveryRecordMismatch);
        }
        let phase = self.authority_store.phase(&authority)?;
        Ok(ResumedPrivateBazaarXp {
            operation: PreparedPrivateBazaarXp {
                lookup_id,
                authority,
            },
            phase,
        })
    }

    /// Seal before dispatch, apply the exact XP method, verify the signed/final
    /// event and target postcondition, commit the durable authority, then
    /// install the journey's viewer-blind terminal receipt.
    pub fn dispatch_and_install<'a>(
        &self,
        operation: PreparedPrivateBazaarXp,
        journey: &'a mut PrivateBazaarRaidJourney,
        session: &DarkBazaarSession,
        private_receipt: &PrivateClearingReceipt,
        hero: &DungeonWorldCell,
    ) -> Result<&'a PrivateBazaarPublicReceipt, PrivateBazaarGameAdapterError> {
        journey.require_pending(session)?;
        validate_operation_target(
            &operation.authority,
            journey,
            session,
            private_receipt,
            hero,
        )?;
        let effect = operation.authority.effect();
        if hero.read_var("xp") != effect.expected_before() {
            return Err(PrivateBazaarGameAdapterError::TargetChangedBeforeDispatch);
        }

        let dispatch = self.authority_store.begin_dispatch(&operation.authority)?;
        let receipt = gain_private_bazaar_xp(
            hero,
            operation.authority.operation_id(),
            effect.expected_before(),
            effect.reward_amount(),
        )
        .map_err(|error| PrivateBazaarGameAdapterError::DispatchUncertain(error.to_string()))?;
        let policy = operation.authority.policy();
        self.authority_store
            .record_applied(dispatch, &receipt, |candidate| {
                verify_private_bazaar_xp_receipt(
                    hero,
                    candidate,
                    policy.executor_pubkey(),
                    policy.federation_id(),
                    operation.authority.operation_id(),
                    effect.expected_before(),
                    effect.reward_amount(),
                )
            })?;
        let committed = self.authority_store.commit(&operation.authority)?;
        Ok(
            journey.install_committed(
                session,
                private_receipt,
                &operation.authority,
                &committed,
            )?,
        )
    }

    /// Recover a sealed operation exclusively from the target executor's
    /// immutable receipt index. `Prepared` is never dispatched here.
    pub fn recover_and_install<'a>(
        &self,
        journey: &'a mut PrivateBazaarRaidJourney,
        session: &DarkBazaarSession,
        private_receipt: &PrivateClearingReceipt,
        hero: &DungeonWorldCell,
    ) -> Result<&'a PrivateBazaarPublicReceipt, PrivateBazaarGameAdapterError> {
        let resumed = self.resume(journey, session, private_receipt, hero)?;
        let authority = resumed.operation.authority;
        validate_operation_target(&authority, journey, session, private_receipt, hero)?;

        match resumed.phase {
            PrivateBazaarAuthorityPhase::Prepared => {
                return Err(PrivateBazaarGameAdapterError::NotDispatched);
            }
            PrivateBazaarAuthorityPhase::Dispatching => {
                let receipt = authoritative_receipt_lookup(hero, &authority)?;
                let effect = authority.effect();
                let policy = authority.policy();
                self.authority_store
                    .recover_applied(&authority, &receipt, |candidate| {
                        verify_private_bazaar_xp_receipt_evidence(
                            hero,
                            candidate,
                            policy.executor_pubkey(),
                            policy.federation_id(),
                            authority.operation_id(),
                            effect.expected_before(),
                            effect.reward_amount(),
                        )
                    })?;
            }
            PrivateBazaarAuthorityPhase::Applied | PrivateBazaarAuthorityPhase::Committed => {}
        }

        let committed = self.authority_store.commit(&authority)?;
        Ok(journey.install_committed(session, private_receipt, &authority, &committed)?)
    }

    pub fn phase(
        &self,
        operation: &PreparedPrivateBazaarXp,
    ) -> Result<PrivateBazaarAuthorityPhase, PrivateBazaarGameAdapterError> {
        Ok(self.authority_store.phase(&operation.authority)?)
    }

    fn record_path(&self, lookup_id: [u8; 32]) -> PathBuf {
        self.root
            .join("xp-operations")
            .join(format!("{}.xp-operation", hex32(lookup_id)))
    }
}

/// Opaque in-memory handle to the exact already-durable Prepared operation.
/// It is intentionally not `Clone` and carries no controller-settable fields.
#[derive(Debug)]
pub struct PreparedPrivateBazaarXp {
    lookup_id: [u8; 32],
    authority: PrivateBazaarExecutorAuthority,
}

impl PreparedPrivateBazaarXp {
    pub const fn operation_id(&self) -> [u8; 32] {
        self.authority.operation_id()
    }

    pub const fn source_use_id(&self) -> [u8; 32] {
        self.authority.source_use_id()
    }

    pub const fn lookup_id(&self) -> [u8; 32] {
        self.lookup_id
    }
}

#[derive(Debug)]
pub struct ResumedPrivateBazaarXp {
    operation: PreparedPrivateBazaarXp,
    phase: PrivateBazaarAuthorityPhase,
}

impl ResumedPrivateBazaarXp {
    pub const fn phase(&self) -> PrivateBazaarAuthorityPhase {
        self.phase
    }

    pub fn operation(&self) -> &PreparedPrivateBazaarXp {
        &self.operation
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum PrivateBazaarGameAdapterError {
    UnsupportedGamePolicy,
    ExecutorPolicyMismatch,
    TargetChangedBeforeDispatch,
    NeedsRecovery(PrivateBazaarAuthorityPhase),
    NotDispatched,
    RecoveryReceiptNotFound,
    AmbiguousRecoveryReceipts,
    RecoveryRecordMismatch,
    RecoveryRecordAlreadyExists,
    DispatchUncertain(String),
    Authority(String),
    Journey(String),
    Corrupt(String),
    Io {
        operation: &'static str,
        detail: String,
    },
}

impl PrivateBazaarGameAdapterError {
    fn io(operation: &'static str, error: io::Error) -> Self {
        Self::Io {
            operation,
            detail: error.to_string(),
        }
    }
}

impl From<PrivateBazaarAuthorityError> for PrivateBazaarGameAdapterError {
    fn from(error: PrivateBazaarAuthorityError) -> Self {
        Self::Authority(error.to_string())
    }
}

impl From<PrivateBazaarJourneyError> for PrivateBazaarGameAdapterError {
    fn from(error: PrivateBazaarJourneyError) -> Self {
        Self::Journey(error.to_string())
    }
}

impl std::fmt::Display for PrivateBazaarGameAdapterError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "private Bazaar game adapter refused: {self:?}")
    }
}

impl std::error::Error for PrivateBazaarGameAdapterError {}

fn validate_engine_policy(
    journey: &PrivateBazaarRaidJourney,
    hero: &DungeonWorldCell,
) -> Result<(), PrivateBazaarGameAdapterError> {
    let pin = journey.policy().pin();
    if pin.reward_method() != PRIVATE_BAZAAR_XP_METHOD
        || pin.reward_event_topic() != symbol(PRIVATE_BAZAAR_XP_EVENT)
    {
        return Err(PrivateBazaarGameAdapterError::UnsupportedGamePolicy);
    }
    if hero.executor_pubkey() != Some(pin.executor_pubkey())
        || hero.federation_id() != pin.executor_federation()
    {
        return Err(PrivateBazaarGameAdapterError::ExecutorPolicyMismatch);
    }
    Ok(())
}

fn build_authority(
    journey: &PrivateBazaarRaidJourney,
    session: &DarkBazaarSession,
    private_receipt: &PrivateClearingReceipt,
    hero: &DungeonWorldCell,
    expected_before: u64,
) -> Result<PrivateBazaarExecutorAuthority, PrivateBazaarGameAdapterError> {
    let pin = journey.policy().pin();
    let reward = journey.policy().reward();
    let effect = PrivateBazaarExactEffect::new(
        hero.cell_id(),
        pin.reward_method(),
        pin.reward_event_topic(),
        reward.kind.clone(),
        reward.amount,
        expected_before,
    )?;
    Ok(PrivateBazaarExecutorAuthority::from_verified_allocation(
        session,
        private_receipt,
        journey.market_identity(),
        journey.policy(),
        effect,
    )?)
}

fn validate_operation_target(
    authority: &PrivateBazaarExecutorAuthority,
    journey: &PrivateBazaarRaidJourney,
    session: &DarkBazaarSession,
    private_receipt: &PrivateClearingReceipt,
    hero: &DungeonWorldCell,
) -> Result<(), PrivateBazaarGameAdapterError> {
    validate_engine_policy(journey, hero)?;
    let effect = authority.effect();
    if effect.target_cell() != hero.cell_id()
        || effect.method() != PRIVATE_BAZAAR_XP_METHOD
        || effect.event_topic() != symbol(PRIVATE_BAZAAR_XP_EVENT)
        || effect.reward_kind() != journey.policy().reward().kind
        || effect.reward_amount() != journey.policy().reward().amount
        || authority.market_instance_id() != journey.market_identity().digest()
        || authority.policy_id() != journey.policy().policy_id()
        || !authority.matches_source(
            session,
            private_receipt,
            journey.market_identity(),
            journey.policy(),
        )
    {
        return Err(PrivateBazaarGameAdapterError::RecoveryRecordMismatch);
    }
    Ok(())
}

fn authoritative_receipt_lookup(
    hero: &DungeonWorldCell,
    authority: &PrivateBazaarExecutorAuthority,
) -> Result<dregg_app_framework::TurnReceipt, PrivateBazaarGameAdapterError> {
    let effect = authority.effect();
    let policy = authority.policy();
    let mut matching = hero.receipt_chain_snapshot().into_iter().filter(|receipt| {
        verify_private_bazaar_xp_receipt_evidence(
            hero,
            receipt,
            policy.executor_pubkey(),
            policy.federation_id(),
            authority.operation_id(),
            effect.expected_before(),
            effect.reward_amount(),
        )
    });
    let receipt = matching
        .next()
        .ok_or(PrivateBazaarGameAdapterError::RecoveryReceiptNotFound)?;
    if matching.next().is_some() {
        return Err(PrivateBazaarGameAdapterError::AmbiguousRecoveryReceipts);
    }
    Ok(receipt)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct XpOperationRecord {
    lookup_id: [u8; 32],
    source_use_id: [u8; 32],
    operation_id: [u8; 32],
    authority_digest: [u8; 32],
    market_instance_id: [u8; 32],
    policy_id: [u8; 32],
    target_cell: [u8; 32],
    expected_before: u64,
}

impl XpOperationRecord {
    fn new(
        journey: &PrivateBazaarRaidJourney,
        authority: &PrivateBazaarExecutorAuthority,
        hero: &DungeonWorldCell,
        expected_before: u64,
    ) -> Self {
        Self {
            lookup_id: lookup_id_from_parts(
                journey.policy().policy_id(),
                authority.source_use_id(),
            ),
            source_use_id: authority.source_use_id(),
            operation_id: authority.operation_id(),
            authority_digest: authority.authority_digest(),
            market_instance_id: journey.market_identity().digest(),
            policy_id: journey.policy().policy_id(),
            target_cell: hero.cell_id().0,
            expected_before,
        }
    }

    fn encode(self) -> Vec<u8> {
        let mut out = Vec::with_capacity(RECORD_LEN);
        out.extend_from_slice(RECORD_MAGIC);
        for field in [
            self.lookup_id,
            self.source_use_id,
            self.operation_id,
            self.authority_digest,
            self.market_instance_id,
            self.policy_id,
            self.target_cell,
        ] {
            out.extend_from_slice(&field);
        }
        out.extend_from_slice(&self.expected_before.to_be_bytes());
        let checksum = record_checksum(&out);
        out.extend_from_slice(&checksum);
        out
    }

    fn decode(bytes: &[u8]) -> Result<Self, PrivateBazaarGameAdapterError> {
        if bytes.len() != RECORD_LEN || &bytes[..8] != RECORD_MAGIC {
            return Err(PrivateBazaarGameAdapterError::Corrupt(
                "XP operation schema/version mismatch".to_owned(),
            ));
        }
        if record_checksum(&bytes[..RECORD_LEN - 32]) != array_at(bytes, RECORD_LEN - 32) {
            return Err(PrivateBazaarGameAdapterError::Corrupt(
                "XP operation checksum mismatch".to_owned(),
            ));
        }
        let record = Self {
            lookup_id: array_at(bytes, 8),
            source_use_id: array_at(bytes, 40),
            operation_id: array_at(bytes, 72),
            authority_digest: array_at(bytes, 104),
            market_instance_id: array_at(bytes, 136),
            policy_id: array_at(bytes, 168),
            target_cell: array_at(bytes, 200),
            expected_before: u64::from_be_bytes(
                bytes[232..240]
                    .try_into()
                    .expect("fixed record length checked"),
            ),
        };
        if [
            record.lookup_id,
            record.source_use_id,
            record.operation_id,
            record.authority_digest,
            record.market_instance_id,
            record.policy_id,
            record.target_cell,
        ]
        .iter()
        .any(|field| *field == [0; 32])
        {
            return Err(PrivateBazaarGameAdapterError::Corrupt(
                "XP operation contains a zero authority field".to_owned(),
            ));
        }
        Ok(record)
    }
}

fn lookup_id(
    journey: &PrivateBazaarRaidJourney,
    private_receipt: &PrivateClearingReceipt,
) -> [u8; 32] {
    let source_use_id =
        private_bazaar_source_use_id(journey.market_identity().digest(), private_receipt);
    lookup_id_from_parts(journey.policy().policy_id(), source_use_id)
}

fn lookup_id_from_parts(policy_id: [u8; 32], source_use_id: [u8; 32]) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key(LOOKUP_DOMAIN);
    hasher.update(&policy_id);
    hasher.update(&source_use_id);
    *hasher.finalize().as_bytes()
}

fn record_checksum(bytes: &[u8]) -> [u8; 32] {
    *blake3::Hasher::new_derive_key(RECORD_DOMAIN)
        .update(bytes)
        .finalize()
        .as_bytes()
}

fn write_new_or_verify(path: &Path, expected: &[u8]) -> Result<(), PrivateBazaarGameAdapterError> {
    match OpenOptions::new().write(true).create_new(true).open(path) {
        Ok(mut file) => {
            file.write_all(expected)
                .map_err(|error| PrivateBazaarGameAdapterError::io("write XP operation", error))?;
            file.sync_all()
                .map_err(|error| PrivateBazaarGameAdapterError::io("sync XP operation", error))?;
            sync_parent(path)
        }
        Err(error) if error.kind() == io::ErrorKind::AlreadyExists => {
            let mut found = Vec::new();
            File::open(path)
                .and_then(|mut file| file.read_to_end(&mut found))
                .map_err(|error| {
                    PrivateBazaarGameAdapterError::io("read existing XP operation", error)
                })?;
            if found == expected {
                Ok(())
            } else {
                Err(PrivateBazaarGameAdapterError::RecoveryRecordAlreadyExists)
            }
        }
        Err(error) => Err(PrivateBazaarGameAdapterError::io(
            "create XP operation",
            error,
        )),
    }
}

fn read_record(path: &Path) -> Result<XpOperationRecord, PrivateBazaarGameAdapterError> {
    let bytes = fs::read(path)
        .map_err(|error| PrivateBazaarGameAdapterError::io("read XP operation", error))?;
    XpOperationRecord::decode(&bytes)
}

fn sync_parent(path: &Path) -> Result<(), PrivateBazaarGameAdapterError> {
    let parent = path.parent().ok_or_else(|| {
        PrivateBazaarGameAdapterError::Corrupt("XP operation path has no parent".to_owned())
    })?;
    sync_directory(parent)
}

fn sync_directory(path: &Path) -> Result<(), PrivateBazaarGameAdapterError> {
    File::open(path)
        .and_then(|directory| directory.sync_all())
        .map_err(|error| PrivateBazaarGameAdapterError::io("sync XP journal directory", error))
}

fn array_at(bytes: &[u8], offset: usize) -> [u8; 32] {
    bytes[offset..offset + 32]
        .try_into()
        .expect("fixed XP operation length checked")
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
    use crate::private_bazaar_journey::{
        PrivateBazaarDeploymentPin, PrivateBazaarPublicAction, PrivateBazaarPublicPhase,
        PrivateBazaarRaidPolicy,
    };
    use crate::private_clearing::PrivateClearingExpectation;
    use crate::private_clearing_guild_allocation::{GuildMember, GuildReward, GuildRoster};
    use crate::{DarkBazaarOffering, TURN_BID, TURN_LIST};
    use dreggnet_offerings::{Action, DreggIdentity, Offering, Outcome, SessionConfig};
    use dungeon_on_dregg::progression::{deploy_hero, gain_xp};

    const SELLER: &str = "adapter:guild-alice";
    const LOW_BIDDER: &str = "adapter:guild-bob";
    const WINNER: &str = "adapter:guild-carol";
    const RAID_XP: u64 = 144;

    fn actor(name: &str) -> DreggIdentity {
        DreggIdentity(name.to_owned())
    }

    fn land(
        offering: &DarkBazaarOffering,
        session: &mut DarkBazaarSession,
        turn: &str,
        value: i64,
        who: &str,
    ) {
        let outcome = offering.advance(session, Action::new(turn, turn, value, true), actor(who));
        assert!(matches!(outcome, Outcome::Landed { .. }), "{outcome:?}");
    }

    #[test]
    fn sealed_dispatch_recovers_by_authoritative_receipt_without_second_xp_turn() {
        let alice = deploy_hero(0x91);
        let bob = deploy_hero(0x92);
        let carol = deploy_hero(0x93);
        carol.set_executor_signing_key([0xA7; 32]);
        let roster = GuildRoster::new(vec![
            GuildMember::new(actor(SELLER), alice.cell_id()),
            GuildMember::new(actor(LOW_BIDDER), bob.cell_id()),
            GuildMember::new(actor(WINNER), carol.cell_id()),
        ])
        .unwrap();
        let reward = GuildReward::new("raid-xp/ashen-vault/v1", RAID_XP).unwrap();
        let pin = PrivateBazaarDeploymentPin::new(
            [0x31; 32],
            roster.digest(),
            PrivateBazaarRaidPolicy::reward_commitment_for_configuration(&reward),
            PRIVATE_BAZAAR_XP_METHOD,
            symbol(PRIVATE_BAZAAR_XP_EVENT),
            carol.executor_pubkey().unwrap(),
            carol.federation_id(),
        )
        .unwrap();
        let policy = PrivateBazaarRaidPolicy::load(pin, roster, reward).unwrap();

        let offering = DarkBazaarOffering::new();
        let mut market = offering.open(SessionConfig::with_seed(0xB4_2A_A3)).unwrap();
        land(&offering, &mut market, TURN_LIST, 1, SELLER);
        land(&offering, &mut market, TURN_BID, 2, LOW_BIDDER);
        land(&offering, &mut market, TURN_BID, 3, WINNER);
        let mut journey = PrivateBazaarRaidJourney::new(&market, policy).unwrap();
        journey
            .advance_public(&PrivateBazaarPublicAction::Enter.offering_action())
            .unwrap();

        let authorization = market.prepare_private_clearing_zk().unwrap();
        let statement = authorization.statement();
        let private_receipt = offering
            .settle_private_verified(
                &mut market,
                authorization,
                PrivateClearingExpectation::from_statement(statement),
            )
            .unwrap();

        let directory = tempfile::tempdir().unwrap();
        let adapter = PrivateBazaarXpAdapter::open(directory.path()).unwrap();
        let prepared = adapter
            .prepare(&journey, &market, &private_receipt, &carol)
            .unwrap();
        assert_eq!(carol.read_var("xp"), 0);

        // Fault-inject the exact process-death window: Dispatching is durable,
        // the executor lands, but Applied/Committed and journey publication do
        // not. The dispatch handle is lost rather than reused.
        let dispatch = adapter
            .authority_store
            .begin_dispatch(&prepared.authority)
            .unwrap();
        let receipt = gain_private_bazaar_xp(
            &carol,
            prepared.operation_id(),
            prepared.authority.effect().expected_before(),
            prepared.authority.effect().reward_amount(),
        )
        .unwrap();
        drop(dispatch);
        assert_eq!(carol.read_var("xp"), RAID_XP);
        assert!(carol.receipt_by_hash(receipt.receipt_hash()).is_some());
        assert_eq!(
            adapter.phase(&prepared).unwrap(),
            PrivateBazaarAuthorityPhase::Dispatching
        );
        // Historical recovery authenticates the exact receipt itself, not a
        // brittle requirement that it is still the hero's current head.
        gain_xp(&carol, 7).unwrap();
        assert_eq!(carol.read_var("xp"), RAID_XP + 7);
        drop(adapter);

        let restarted = PrivateBazaarXpAdapter::open(directory.path()).unwrap();
        let resumed = restarted
            .resume(&journey, &market, &private_receipt, &carol)
            .unwrap();
        assert_eq!(resumed.phase(), PrivateBazaarAuthorityPhase::Dispatching);
        let public = restarted
            .recover_and_install(&mut journey, &market, &private_receipt, &carol)
            .unwrap();
        assert_eq!(public.phase(), PrivateBazaarPublicPhase::Settled);
        assert_eq!(carol.read_var("xp"), RAID_XP + 7);

        // Recovery/refresh cannot become a second additive reward.
        let replay = gain_private_bazaar_xp(&carol, resumed.operation().operation_id(), 0, RAID_XP);
        assert!(replay.is_err());
        assert_eq!(carol.read_var("xp"), RAID_XP + 7);
    }
}
