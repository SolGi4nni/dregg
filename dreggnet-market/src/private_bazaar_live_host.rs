//! Real [`OfferingHost`](dreggnet_offerings::OfferingHost) lifecycle for the
//! playable private Bazaar raid.
//!
//! `Enter` is not a presentation-only state flip: it drives the underlying
//! [`DarkBazaarOffering`] LIST action and returns that executor-produced
//! receipt.  The resulting listed market and its viewer-blind journey live in a
//! deployment-owned registry so the private proof/settlement worker can reach
//! the same object without transporting bids or witnesses through public
//! actions.  Once entered, the hosted action set is empty; refresh is a read and
//! must use `render`, never a fake journaled move.

use std::collections::{BTreeMap, Bound};
use std::sync::{Arc, Mutex, Weak};

use deos_view::ViewNode;
use dreggnet_offerings::{
    Action, DreggIdentity, Offering, OfferingError, Outcome, RunCost, SessionConfig, Surface,
    VerifyReport,
};

use crate::private_bazaar_journey::{
    PrivateBazaarPublicAction, PrivateBazaarRaidJourney, PrivateBazaarRaidPolicy,
};
use crate::private_clearing::PrivateClearingReceipt;
use crate::{DarkBazaarOffering, DarkBazaarSession, TURN_LIST};

pub const PRIVATE_BAZAAR_RAID_KEY: &str = "private-bazaar-raid";

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PrivateBazaarLiveHostError {
    MissingDeterministicSeed,
    DuplicateLiveSeed(u64),
    UnknownSeed(u64),
    NotEntered(u64),
    Poisoned,
    Backend(String),
}

impl std::fmt::Display for PrivateBazaarLiveHostError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "private Bazaar live host refused: {self:?}")
    }
}

impl std::error::Error for PrivateBazaarLiveHostError {}

struct PrivateBazaarLiveBackend {
    market: DarkBazaarSession,
    journey: Option<PrivateBazaarRaidJourney>,
    terminal_fault: Option<String>,
}

/// Cloneable deployment-side lookup for the same live state held by hosted
/// frontend sessions.  The key is the deterministic session seed supplied at
/// open; adapters keep their ordinary `SessionId`, while the private worker is
/// configured with this backend key out of band.
#[derive(Clone, Default)]
pub struct PrivateBazaarLiveRegistry {
    sessions: Arc<Mutex<BTreeMap<u64, Weak<Mutex<PrivateBazaarLiveBackend>>>>>,
}

impl PrivateBazaarLiveRegistry {
    pub fn new() -> Self {
        Self::default()
    }

    fn insert(
        &self,
        seed: u64,
        backend: &Arc<Mutex<PrivateBazaarLiveBackend>>,
    ) -> Result<(), PrivateBazaarLiveHostError> {
        let mut sessions = self
            .sessions
            .lock()
            .map_err(|_| PrivateBazaarLiveHostError::Poisoned)?;
        sessions.retain(|_, session| session.strong_count() != 0);
        if sessions.get(&seed).and_then(Weak::upgrade).is_some() {
            return Err(PrivateBazaarLiveHostError::DuplicateLiveSeed(seed));
        }
        sessions.insert(seed, Arc::downgrade(backend));
        Ok(())
    }

    /// Run one deployment-owned backend operation against the exact market and
    /// journey mounted in the public host, preserving the operation's own error
    /// type separately from registry/host failures. Frontend adapters never
    /// receive this handle; their only mutation is the payload-free Enter
    /// action.
    pub fn with_entered_typed<R, E>(
        &self,
        seed: u64,
        operation: impl FnOnce(&mut DarkBazaarSession, &mut PrivateBazaarRaidJourney) -> Result<R, E>,
    ) -> Result<Result<R, E>, PrivateBazaarLiveHostError> {
        let backend = {
            let sessions = self
                .sessions
                .lock()
                .map_err(|_| PrivateBazaarLiveHostError::Poisoned)?;
            sessions
                .get(&seed)
                .and_then(Weak::upgrade)
                .ok_or(PrivateBazaarLiveHostError::UnknownSeed(seed))?
        };
        let mut backend = backend
            .lock()
            .map_err(|_| PrivateBazaarLiveHostError::Poisoned)?;
        if let Some(reason) = &backend.terminal_fault {
            return Err(PrivateBazaarLiveHostError::Backend(reason.clone()));
        }
        let PrivateBazaarLiveBackend {
            market, journey, ..
        } = &mut *backend;
        let journey = journey
            .as_mut()
            .ok_or(PrivateBazaarLiveHostError::NotEntered(seed))?;
        Ok(operation(market, journey))
    }

    pub fn contains(&self, seed: u64) -> bool {
        self.sessions
            .lock()
            .ok()
            .and_then(|sessions| sessions.get(&seed).and_then(Weak::upgrade))
            .is_some()
    }

    /// Snapshot every proof-verified terminal receipt currently retained by a
    /// live hosted market. This is the authenticated production source for the
    /// private worker: entries can appear only after
    /// `settle_private_verified` has verified the hiding proof and landed the
    /// real executor settlement. The BTreeMap order makes first-time cursor
    /// assignment deterministic without exposing this method to a frontend
    /// rendering path.
    #[doc(hidden)]
    pub fn finalized_private_receipts_for_worker(
        &self,
        after_seed: Option<u64>,
        limit: usize,
    ) -> Result<(Vec<(u64, PrivateClearingReceipt)>, Option<u64>, bool), PrivateBazaarLiveHostError>
    {
        let sessions = {
            let mut registry = self
                .sessions
                .lock()
                .map_err(|_| PrivateBazaarLiveHostError::Poisoned)?;
            registry.retain(|_, session| session.strong_count() != 0);
            let lower = after_seed.map_or(Bound::Unbounded, Bound::Excluded);
            registry
                .range((lower, Bound::Unbounded))
                .filter_map(|(seed, session)| session.upgrade().map(|session| (*seed, session)))
                .take(limit)
                .collect::<Vec<_>>()
        };

        let last_scanned_seed = sessions.last().map(|(seed, _)| *seed);
        let exhausted = sessions.len() < limit;
        let mut finalized = Vec::new();
        for (seed, backend) in sessions {
            let backend = backend
                .lock()
                .map_err(|_| PrivateBazaarLiveHostError::Poisoned)?;
            if backend.terminal_fault.is_some() || backend.journey.is_none() {
                continue;
            }
            if let Some(receipt) = &backend.market.verified_private_clearing_receipt {
                finalized.push((seed, receipt.clone()));
            }
        }
        Ok((finalized, last_scanned_seed, exhausted))
    }
}

/// Offering mounted once into web/chat hosts.  Policy and reserve are immutable
/// deployment configuration, not action/request fields.
#[derive(Clone)]
pub struct PrivateBazaarRaidOffering {
    policy: PrivateBazaarRaidPolicy,
    reserve: i64,
    registry: PrivateBazaarLiveRegistry,
}

impl PrivateBazaarRaidOffering {
    pub const KEY: &'static str = PRIVATE_BAZAAR_RAID_KEY;

    pub fn new(
        policy: PrivateBazaarRaidPolicy,
        reserve: u64,
        registry: PrivateBazaarLiveRegistry,
    ) -> Result<Self, PrivateBazaarLiveHostError> {
        let reserve = i64::try_from(reserve).map_err(|_| {
            PrivateBazaarLiveHostError::Backend("market reserve exceeds i64".to_owned())
        })?;
        Ok(Self {
            policy,
            reserve,
            registry,
        })
    }

    pub fn registry(&self) -> PrivateBazaarLiveRegistry {
        self.registry.clone()
    }
}

pub struct PrivateBazaarHostedSession {
    seed: u64,
    backend: Arc<Mutex<PrivateBazaarLiveBackend>>,
}

impl Offering for PrivateBazaarRaidOffering {
    type Session = PrivateBazaarHostedSession;

    fn open(&self, cfg: SessionConfig) -> Result<Self::Session, OfferingError> {
        let seed = cfg.seed.ok_or_else(|| {
            OfferingError::Deploy(PrivateBazaarLiveHostError::MissingDeterministicSeed.to_string())
        })?;
        let market = DarkBazaarOffering::new().open(SessionConfig::with_seed(seed))?;
        let backend = Arc::new(Mutex::new(PrivateBazaarLiveBackend {
            market,
            journey: None,
            terminal_fault: None,
        }));
        self.registry
            .insert(seed, &backend)
            .map_err(|error| OfferingError::Deploy(error.to_string()))?;
        Ok(PrivateBazaarHostedSession { seed, backend })
    }

    fn actions(&self, session: &Self::Session) -> Vec<Action> {
        let Ok(backend) = session.backend.lock() else {
            return Vec::new();
        };
        if backend.terminal_fault.is_none() && backend.journey.is_none() {
            vec![PrivateBazaarPublicAction::Enter.offering_action()]
        } else {
            Vec::new()
        }
    }

    fn advance(&self, session: &mut Self::Session, input: Action, actor: DreggIdentity) -> Outcome {
        let Ok(semantic) = PrivateBazaarPublicAction::from_offering_action(&input) else {
            return Outcome::Refused(
                "the private Bazaar host accepts only its canonical payload-free action".to_owned(),
            );
        };
        if semantic != PrivateBazaarPublicAction::Enter {
            return Outcome::Refused(
                "refresh is a read; render the existing hosted session instead".to_owned(),
            );
        }
        let Ok(mut backend) = session.backend.lock() else {
            return Outcome::Refused("private Bazaar host state is unavailable".to_owned());
        };
        if let Some(reason) = &backend.terminal_fault {
            return Outcome::Refused(reason.clone());
        }
        if backend.journey.is_some() {
            return Outcome::Refused("the private Bazaar raid was already entered".to_owned());
        }

        // Public Enter becomes the real LIST turn. Reserve is deployment policy;
        // the public action's numeric lane remains fixed at zero.
        let list = Action::new("list private raid market", TURN_LIST, self.reserve, true);
        let outcome = DarkBazaarOffering::new().advance(&mut backend.market, list, actor);
        if matches!(outcome, Outcome::Landed { .. }) {
            match PrivateBazaarRaidJourney::new(&backend.market, self.policy.clone()).and_then(
                |mut journey| {
                    journey.advance_public(&input)?;
                    Ok(journey)
                },
            ) {
                Ok(journey) => backend.journey = Some(journey),
                Err(error) => {
                    // The LIST already committed. Quarantine the session and
                    // return its genuine receipt; never misreport a committed
                    // turn as a refusal that a client might retry.
                    backend.terminal_fault = Some(format!(
                        "listed market could not install its pinned journey: {error}"
                    ));
                }
            }
        }
        outcome
    }

    fn verify(&self, session: &Self::Session) -> VerifyReport {
        let Ok(backend) = session.backend.lock() else {
            return VerifyReport::broken(0, "private Bazaar host lock is poisoned");
        };
        if let Some(reason) = &backend.terminal_fault {
            return VerifyReport::broken(backend.market.market().receipts_len(), reason.clone());
        }
        DarkBazaarOffering::new().verify(&backend.market)
    }

    fn render(&self, session: &Self::Session) -> Surface {
        let Ok(backend) = session.backend.lock() else {
            return failure_surface("private Bazaar host state is unavailable");
        };
        if let Some(reason) = &backend.terminal_fault {
            return failure_surface(reason);
        }
        match backend
            .journey
            .as_ref()
            .and_then(PrivateBazaarRaidJourney::receipt)
        {
            Some(receipt) => receipt.surface(),
            None => Surface(ViewNode::Section {
                title: "Dark Bazaar raid · ready".to_owned(),
                tag: "accent".to_owned(),
                children: vec![ViewNode::Text(
                    "Enter to open the executor-backed sealed market. Bids and proof material never travel through this public action."
                        .to_owned(),
                )],
            }),
        }
    }

    fn price(&self, _input: &Action) -> RunCost {
        RunCost::free()
    }
}

fn failure_surface(reason: &str) -> Surface {
    Surface(ViewNode::Section {
        title: "Dark Bazaar raid · unavailable".to_owned(),
        tag: "bad".to_owned(),
        children: vec![ViewNode::Text(reason.to_owned())],
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::private_bazaar_journey::{PrivateBazaarDeploymentPin, PrivateBazaarRaidPolicy};
    use crate::private_clearing_guild_allocation::{GuildMember, GuildReward, GuildRoster};
    use dregg_app_framework::{CellId, symbol};
    use dreggnet_offerings::{OfferingHost, SessionId};
    use dungeon_on_dregg::progression::{PRIVATE_BAZAAR_XP_EVENT, PRIVATE_BAZAAR_XP_METHOD};

    fn fixture_policy() -> PrivateBazaarRaidPolicy {
        let roster = GuildRoster::new(vec![GuildMember::new(
            DreggIdentity("raid-member".to_owned()),
            CellId([0x41; 32]),
        )])
        .unwrap();
        let reward = GuildReward::new("raid-xp/hosted/v1", 144).unwrap();
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
        PrivateBazaarRaidPolicy::load(pin, roster, reward).unwrap()
    }

    #[test]
    fn offering_host_enter_is_a_real_list_turn_and_refresh_is_read_only() {
        let registry = PrivateBazaarLiveRegistry::new();
        let offering =
            PrivateBazaarRaidOffering::new(fixture_policy(), 1, registry.clone()).unwrap();
        let mut host = OfferingHost::new();
        host.register(
            PrivateBazaarRaidOffering::KEY,
            "The Dark Bazaar — private raid",
            offering,
        );
        let id = SessionId::new("private-bazaar-hosted");
        host.open_session(
            PrivateBazaarRaidOffering::KEY,
            id.clone(),
            SessionConfig::with_seed(0xB4A2),
        )
        .unwrap();

        let actions = host
            .actions(PrivateBazaarRaidOffering::KEY, &id)
            .expect("hosted actions");
        assert_eq!(actions.len(), 1);
        assert_eq!(
            PrivateBazaarPublicAction::from_offering_action(&actions[0]),
            Ok(PrivateBazaarPublicAction::Enter)
        );
        let outcome = host
            .advance(
                PrivateBazaarRaidOffering::KEY,
                &id,
                actions[0].clone(),
                DreggIdentity("raid-member".to_owned()),
            )
            .expect("host route exists");
        let receipt = match outcome {
            Outcome::Landed { receipt, .. } => receipt,
            other => panic!("entry must land the real LIST turn, got {other:?}"),
        };
        assert_ne!(receipt.turn_hash, [0; 32]);
        assert!(registry.contains(0xB4A2));
        assert!(
            host.actions(PrivateBazaarRaidOffering::KEY, &id)
                .expect("hosted actions after entry")
                .is_empty()
        );
        assert!(
            format!(
                "{:?}",
                host.render(PrivateBazaarRaidOffering::KEY, &id)
                    .expect("hosted render")
                    .view()
            )
            .contains("pending")
        );
        assert_eq!(
            host.move_log(PrivateBazaarRaidOffering::KEY, &id)
                .expect("real hosted move log")
                .moves
                .len(),
            1
        );

        let refresh = host
            .advance(
                PrivateBazaarRaidOffering::KEY,
                &id,
                PrivateBazaarPublicAction::Refresh.offering_action(),
                DreggIdentity("raid-member".to_owned()),
            )
            .expect("host route exists");
        assert!(matches!(refresh, Outcome::Refused(_)));
        assert_eq!(
            host.move_log(PrivateBazaarRaidOffering::KEY, &id)
                .expect("read refusal creates no ghost move")
                .moves
                .len(),
            1
        );
    }
}
