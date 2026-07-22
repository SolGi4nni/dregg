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

use std::path::Path;

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
use dreggnet_market::private_clearing::PrivateClearingReceipt;
use dreggnet_market::private_clearing_guild_allocation::{GuildMember, GuildReward, GuildRoster};
use dreggnet_offerings::{DreggIdentity, OfferingHost};
use dungeon_on_dregg::progression::DungeonWorldCell;

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
pub const PRIVATE_BAZAAR_RESERVE_ENV: &str = "DREGG_PRIVATE_BAZAAR_RESERVE";
pub const PRIVATE_BAZAAR_AUTHORITY_DIR_ENV: &str = "DREGG_PRIVATE_BAZAAR_AUTHORITY_DIR";

#[derive(Debug)]
pub enum PrivateBazaarLiveDeploymentError {
    Host(PrivateBazaarLiveHostError),
    GameAdapter(PrivateBazaarGameAdapterError),
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

/// Host-retained, worker-reachable configuration for one deployment.
///
/// Clones share both the live-session registry and the same durable store root;
/// they do not clone or weaken policy.  The public constructors accept an
/// already validated policy rather than an untrusted runtime roster.
#[derive(Clone)]
pub struct PrivateBazaarLiveDeployment {
    offering: PrivateBazaarRaidOffering,
    registry: PrivateBazaarLiveRegistry,
    xp_adapter: PrivateBazaarXpAdapter,
}

impl PrivateBazaarLiveDeployment {
    pub fn open(
        policy: PrivateBazaarRaidPolicy,
        reserve: u64,
        authority_dir: impl AsRef<Path>,
    ) -> Result<Self, PrivateBazaarLiveDeploymentError> {
        let registry = PrivateBazaarLiveRegistry::new();
        let offering = PrivateBazaarRaidOffering::new(policy, reserve, registry.clone())?;
        let xp_adapter = PrivateBazaarXpAdapter::open(authority_dir)?;
        Ok(Self {
            offering,
            registry,
            xp_adapter,
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
            PRIVATE_BAZAAR_RESERVE_ENV,
            PRIVATE_BAZAAR_AUTHORITY_DIR_ENV,
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
        Ok(Some(Self::open(policy, reserve, authority_dir)?))
    }
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
    use dregg_app_framework::{CellId, symbol};
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

    /// Worker-only test helper: replay the durable private inputs into the
    /// deployment registry, produce the real hiding proof, and install the
    /// verified settlement in the exact market owned by the public host. None
    /// of these values cross the public Offering action boundary.
    fn settle_worker_market(
        deployment: &PrivateBazaarLiveDeployment,
        seed: u64,
    ) -> PrivateClearingReceipt {
        deployment
            .registry()
            .with_entered_typed(seed, |market, _journey| {
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
                let authorization = market
                    .prepare_private_clearing_zk()
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
    fn hosted_private_worker_settles_viewer_blind_and_xp_is_exactly_once_across_restart() {
        let temp = tempfile::tempdir().unwrap();
        let authority_dir = temp.path().join("authority");
        let sessions_dir = temp.path().join("sessions");
        let hero = deploy_hero(0x93);
        hero.set_executor_signing_key([0xA7; 32]);
        let policy = playable_policy(&hero);
        let id = SessionId::new("catalog-private-bazaar-settlement");
        let seed = 0xB4_2A_A3;

        let first_private_receipt = {
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

            let private_receipt = settle_worker_market(&deployment, seed);
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
            private_receipt
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

        let replayed_private_receipt = settle_worker_market(&restarted, seed);
        assert_eq!(
            replayed_private_receipt.settlement_turn.receipt_hash(),
            first_private_receipt.settlement_turn.receipt_hash(),
            "deterministic worker replay must reconstruct the exact source receipt"
        );
        let recovered = restarted
            .recover_private_settlement(seed, &replayed_private_receipt, &hero)
            .unwrap();
        assert_eq!(hero.read_var("xp"), 144);
        assert_eq!(recovered.phase().as_str(), "settled");
        let rendered = format!(
            "{:?}",
            host.render(PRIVATE_BAZAAR_RAID_KEY, &id).unwrap().view()
        );
        assert!(rendered.contains("Settled"), "{rendered}");
        assert!(!rendered.contains("catalog-private-winner"), "{rendered}");
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
}
