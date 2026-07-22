//! Live, public-only orchestration for a shielded Bazaar crown claim.
//!
//! A player chooses Red or Blue and submits one ordinary signed Dungeon
//! action. The server derives the exact current affordance from the bound game
//! session, verifies the signature before doing private-proof work, constructs
//! [`PrivateFheggGameConsequenceGate`] from the two verifier-minted authorities,
//! and durably seals its authorization id before dispatch.
//!
//! The authorization journal deliberately has no automatic rollback. A
//! `Reserved` record after a crash or post-reservation refusal is ambiguous:
//! the game turn may have landed while the final journal promotion did not.
//! Replaying a private witness in that state would be unsound, so both
//! `Reserved` and `Consumed` refuse reuse and the deployment must reconcile the
//! game receipt/state explicitly.

use dregg_persist::FinalizedFaithfulSpend;
use dreggnet_market::private_bfv_live_apex::PrivateBfvLiveApexReceipt;
use dreggnet_offerings::{
    Action, OfferingHost, SessionId, SignedAction, SignedError, verify_signed,
};

use crate::{
    GameAffordance, GameAudience, GameAuthorizationPhase, GameEpochError, GameEpochLedger,
    GameSpineError, PrivateFheggGameConsequenceError, PrivateFheggGameConsequenceGate,
    PrivateFheggGameConsequenceReceipt, PrivateFheggWinnerRoute, inspect_bound_game_session,
};

const DUNGEON_KEY: &str = "dungeon";

/// Which executor-enforced `WriteOnce` crown the shielded winner requests.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ShieldedCrownHand {
    Red,
    Blue,
}

impl ShieldedCrownHand {
    const fn choice_index(self) -> i64 {
        match self {
            Self::Red => dungeon_on_dregg::KP_CLAIM_RED as i64,
            Self::Blue => dungeon_on_dregg::KP_CLAIM_BLUE as i64,
        }
    }
}

/// Deployment policy joining the private market, faithful tender, and game
/// signer namespaces. None of these values is accepted from a player request.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShieldedCrownPolicy {
    required_market_asset_id: [u8; 32],
    required_tender_asset_type: u64,
    expected_spend_federation_id: [u8; 32],
    expected_spend_agent: [u8; 32],
    winner_route: PrivateFheggWinnerRoute,
}

impl ShieldedCrownPolicy {
    pub fn new(
        required_market_asset_id: [u8; 32],
        required_tender_asset_type: u64,
        expected_spend_federation_id: [u8; 32],
        expected_spend_agent: [u8; 32],
        winner_route: PrivateFheggWinnerRoute,
    ) -> Result<Self, ShieldedCrownOrchestrationError> {
        if required_market_asset_id == [0; 32] {
            return Err(ShieldedCrownOrchestrationError::InvalidPolicy(
                "market asset id is the all-zero sentinel",
            ));
        }
        if expected_spend_federation_id == [0; 32] {
            return Err(ShieldedCrownOrchestrationError::InvalidPolicy(
                "spend federation id is the all-zero sentinel",
            ));
        }
        if expected_spend_agent == [0; 32] {
            return Err(ShieldedCrownOrchestrationError::InvalidPolicy(
                "spend agent is the all-zero sentinel",
            ));
        }
        Ok(Self {
            required_market_asset_id,
            required_tender_asset_type,
            expected_spend_federation_id,
            expected_spend_agent,
            winner_route,
        })
    }

    pub fn winner_route(&self) -> &PrivateFheggWinnerRoute {
        &self.winner_route
    }
}

/// The whole player input. Proof bytes, openings, roots, prices, winner
/// identities, and game references are intentionally absent.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShieldedCrownAction {
    pub session: SessionId,
    pub hand: ShieldedCrownHand,
    pub signed_action: SignedAction,
}

#[derive(Clone, PartialEq, Eq)]
pub enum ShieldedCrownOrchestrationError {
    InvalidPolicy(&'static str),
    Epoch(GameEpochError),
    Spine(GameSpineError),
    CrownAffordanceUnavailable(ShieldedCrownHand),
    SignedActionMismatch,
    WrongGameSigner,
    SignerCounterExhausted,
    Signature(SignedError),
    Consequence(PrivateFheggGameConsequenceError),
    AuthorizationAlreadyRecorded {
        authorization_id: [u8; 32],
        source_use_id: [u8; 32],
        phase: GameAuthorizationPhase,
    },
    /// The durable reservation remains replay-blocking after this refusal.
    ExecutionSealed {
        authorization_id: [u8; 32],
        cause: PrivateFheggGameConsequenceError,
    },
    /// The game receipt landed, while the final `Consumed` promotion failed.
    /// The preceding `Reserved` record remains the fail-closed source of truth.
    LandedAwaitingDurability {
        receipt: PrivateFheggGameConsequenceReceipt,
        cause: GameEpochError,
    },
}

impl std::fmt::Debug for ShieldedCrownOrchestrationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidPolicy(reason) => f.debug_tuple("InvalidPolicy").field(reason).finish(),
            Self::Epoch(error) => f.debug_tuple("Epoch").field(error).finish(),
            Self::Spine(error) => f.debug_tuple("Spine").field(error).finish(),
            Self::CrownAffordanceUnavailable(hand) => f
                .debug_tuple("CrownAffordanceUnavailable")
                .field(hand)
                .finish(),
            Self::SignedActionMismatch => f.write_str("SignedActionMismatch"),
            Self::WrongGameSigner => f.write_str("WrongGameSigner"),
            Self::SignerCounterExhausted => f.write_str("SignerCounterExhausted"),
            Self::Signature(error) => f.debug_tuple("Signature").field(error).finish(),
            Self::Consequence(error) => f.debug_tuple("Consequence").field(error).finish(),
            Self::AuthorizationAlreadyRecorded {
                authorization_id,
                source_use_id,
                phase,
            } => f
                .debug_struct("AuthorizationAlreadyRecorded")
                .field("authorization_id", authorization_id)
                .field("source_use_id", source_use_id)
                .field("phase", phase)
                .finish(),
            Self::ExecutionSealed {
                authorization_id,
                cause,
            } => f
                .debug_struct("ExecutionSealed")
                .field("authorization_id", authorization_id)
                .field("cause", cause)
                .finish(),
            Self::LandedAwaitingDurability { receipt, cause } => f
                .debug_struct("LandedAwaitingDurability")
                .field("authorization_id", &receipt.authorization_id)
                .field("cause", cause)
                .finish_non_exhaustive(),
        }
    }
}

impl std::fmt::Display for ShieldedCrownOrchestrationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidPolicy(reason) => write!(f, "invalid shielded crown policy: {reason}"),
            Self::Epoch(error) => write!(f, "shielded crown epoch custody failed: {error}"),
            Self::Spine(error) => write!(f, "shielded crown game routing failed: {error}"),
            Self::CrownAffordanceUnavailable(hand) => {
                write!(f, "the {hand:?} crown is not currently available")
            }
            Self::SignedActionMismatch => {
                write!(f, "signed action does not match the live crown affordance")
            }
            Self::WrongGameSigner => write!(f, "signed action is not from the mapped winner"),
            Self::SignerCounterExhausted => write!(f, "winner replay counter is exhausted"),
            Self::Signature(error) => write!(f, "winner signature refused: {error}"),
            Self::Consequence(error) => write!(f, "private consequence refused: {error}"),
            Self::AuthorizationAlreadyRecorded { phase, .. } => {
                write!(f, "private source use is already {phase:?}")
            }
            Self::ExecutionSealed { cause, .. } => {
                write!(f, "sealed private source use could not execute: {cause}")
            }
            Self::LandedAwaitingDurability { cause, .. } => write!(
                f,
                "crown action landed but its consumed marker was not durably synced: {cause}"
            ),
        }
    }
}

impl std::error::Error for ShieldedCrownOrchestrationError {}

impl From<GameEpochError> for ShieldedCrownOrchestrationError {
    fn from(error: GameEpochError) -> Self {
        Self::Epoch(error)
    }
}

impl From<GameSpineError> for ShieldedCrownOrchestrationError {
    fn from(error: GameSpineError) -> Self {
        Self::Spine(error)
    }
}

impl From<SignedError> for ShieldedCrownOrchestrationError {
    fn from(error: SignedError) -> Self {
        Self::Signature(error)
    }
}

impl From<PrivateFheggGameConsequenceError> for ShieldedCrownOrchestrationError {
    fn from(error: PrivateFheggGameConsequenceError) -> Self {
        Self::Consequence(error)
    }
}

/// Execute a live shielded Bazaar result as one exact signed Dungeon crown
/// action. This is the production call site for
/// [`PrivateFheggGameConsequenceGate::new_shielded_crown`].
pub fn execute_shielded_crown_action(
    host: &mut OfferingHost,
    epoch_ledger: &GameEpochLedger,
    policy: &ShieldedCrownPolicy,
    apex: &PrivateBfvLiveApexReceipt,
    finalized_spend: &FinalizedFaithfulSpend,
    request: ShieldedCrownAction,
) -> Result<PrivateFheggGameConsequenceReceipt, ShieldedCrownOrchestrationError> {
    execute_shielded_crown_with_factory(
        host,
        epoch_ledger,
        &policy.winner_route,
        request,
        |target_reference, target_action| {
            PrivateFheggGameConsequenceGate::new_shielded_crown(
                apex,
                policy.required_market_asset_id,
                policy.required_tender_asset_type,
                policy.expected_spend_federation_id,
                policy.expected_spend_agent,
                finalized_spend,
                policy.winner_route.clone(),
                epoch_ledger,
                target_reference,
                target_action,
            )
        },
    )
}

fn execute_shielded_crown_with_factory<F>(
    host: &mut OfferingHost,
    epoch_ledger: &GameEpochLedger,
    winner_route: &PrivateFheggWinnerRoute,
    request: ShieldedCrownAction,
    make_gate: F,
) -> Result<PrivateFheggGameConsequenceReceipt, ShieldedCrownOrchestrationError>
where
    F: FnOnce(
        crate::GameActionRef,
        Action,
    ) -> Result<PrivateFheggGameConsequenceGate, PrivateFheggGameConsequenceError>,
{
    let bound_session = epoch_ledger.bound_session(DUNGEON_KEY, &request.session)?;
    let generation = epoch_ledger.current_generation(DUNGEON_KEY, &request.session)?;
    let view = inspect_bound_game_session(
        host,
        epoch_ledger.host_incarnation(),
        generation,
        bound_session,
        &GameAudience::Shared,
    )?;
    let desired_arg = request.hand.choice_index();
    let (target_reference, target_action) = view
        .affordances
        .iter()
        .find_map(|affordance| match affordance {
            GameAffordance::Turn {
                reference, action, ..
            } if action.turn == dreggnet_offerings::dungeon::TURN_CHOOSE
                && action.arg == desired_arg
                && action.text.is_none() =>
            {
                Some((reference.clone(), action.clone()))
            }
            _ => None,
        })
        .ok_or(ShieldedCrownOrchestrationError::CrownAffordanceUnavailable(
            request.hand,
        ))?;

    if !same_executor_action(&request.signed_action.action, &target_action) {
        return Err(ShieldedCrownOrchestrationError::SignedActionMismatch);
    }
    if request.signed_action.actor_pubkey_hex.to_ascii_lowercase()
        != winner_route.game_signer_pubkey_hex()
    {
        return Err(ShieldedCrownOrchestrationError::WrongGameSigner);
    }
    let expected_counter = match host.signed_counter(
        DUNGEON_KEY,
        &request.session,
        winner_route.game_signer_pubkey_hex(),
    ) {
        None => 0,
        Some(last) => last
            .checked_add(1)
            .ok_or(ShieldedCrownOrchestrationError::SignerCounterExhausted)?,
    };
    verify_signed(
        DUNGEON_KEY,
        &request.session,
        expected_counter,
        &request.signed_action,
    )?;

    let mut gate = make_gate(target_reference, target_action)?;
    let authorization_id = gate.authorization_id();
    let source_use_ids = gate.source_use_ids();
    for source_use_id in &source_use_ids {
        if let Some(phase) = epoch_ledger.authorization_phase(*source_use_id)? {
            gate.restore_consumed(authorization_id)?;
            return Err(
                ShieldedCrownOrchestrationError::AuthorizationAlreadyRecorded {
                    authorization_id,
                    source_use_id: *source_use_id,
                    phase,
                },
            );
        }
    }
    if !epoch_ledger.reserve_authorizations(&source_use_ids)? {
        let mut recorded = None;
        for source_use_id in &source_use_ids {
            if let Some(phase) = epoch_ledger.authorization_phase(*source_use_id)? {
                recorded = Some((*source_use_id, phase));
                break;
            }
        }
        let (source_use_id, phase) = recorded.ok_or_else(|| {
            GameEpochError::Corrupt(
                "atomic source-use reservation refused without a recorded key".to_string(),
            )
        })?;
        gate.restore_consumed(authorization_id)?;
        return Err(
            ShieldedCrownOrchestrationError::AuthorizationAlreadyRecorded {
                authorization_id,
                source_use_id,
                phase,
            },
        );
    }

    let receipt = gate
        .execute_signed(host, request.signed_action)
        .map_err(|cause| ShieldedCrownOrchestrationError::ExecutionSealed {
            authorization_id,
            cause,
        })?;
    if let Err(cause) = epoch_ledger.consume_authorizations(&source_use_ids) {
        return Err(ShieldedCrownOrchestrationError::LandedAwaitingDurability { receipt, cause });
    }
    Ok(receipt)
}

fn same_executor_action(left: &Action, right: &Action) -> bool {
    left.turn == right.turn && left.arg == right.arg && left.text == right.text
}

#[cfg(test)]
mod tests {
    use deos_view::ViewNode;
    use dreggnet_offerings::{
        DreggIdentity, Offering, OfferingError, Outcome, RunCost, SessionConfig, Surface,
        TurnSigner, VerifyReport,
    };
    use dungeon_on_dregg::KP_PRESS_ON;

    use crate::{
        GameCommand, GameHostIncarnation, GameResult, execute_bound_asserted_game_command,
    };

    use super::*;

    #[derive(Clone, Debug, Default)]
    struct CrownState {
        in_hall: bool,
        crown: Option<ShieldedCrownHand>,
        landed: usize,
    }

    /// Lightweight orchestration fixture. The already-banked consequence test
    /// drives the real Lean-authored Keep and its WriteOnce constraint; this
    /// fixture keeps restart-journal tests independent of rebuilding the whole
    /// linked Lean/PQ runtime while preserving the same action/refusal shape.
    struct CrownOffering;

    impl Offering for CrownOffering {
        type Session = CrownState;

        fn open(&self, _cfg: SessionConfig) -> Result<Self::Session, OfferingError> {
            Ok(CrownState::default())
        }

        fn actions(&self, session: &Self::Session) -> Vec<Action> {
            if !session.in_hall {
                return vec![Action::new(
                    "press on",
                    dreggnet_offerings::dungeon::TURN_CHOOSE,
                    KP_PRESS_ON as i64,
                    true,
                )];
            }
            vec![
                Action::new(
                    "claim red",
                    dreggnet_offerings::dungeon::TURN_CHOOSE,
                    dungeon_on_dregg::KP_CLAIM_RED as i64,
                    true,
                ),
                Action::new(
                    "claim blue",
                    dreggnet_offerings::dungeon::TURN_CHOOSE,
                    dungeon_on_dregg::KP_CLAIM_BLUE as i64,
                    true,
                ),
            ]
        }

        fn advance(
            &self,
            session: &mut Self::Session,
            input: Action,
            _actor: DreggIdentity,
        ) -> Outcome {
            if input.turn != dreggnet_offerings::dungeon::TURN_CHOOSE || input.text.is_some() {
                return Outcome::Refused("not an exact crown-fixture choice".to_string());
            }
            if !session.in_hall && input.arg == KP_PRESS_ON as i64 {
                session.in_hall = true;
                session.landed += 1;
                return Outcome::Landed {
                    receipt: Default::default(),
                    ended: false,
                };
            }
            let hand = match input.arg {
                arg if arg == dungeon_on_dregg::KP_CLAIM_RED as i64 => ShieldedCrownHand::Red,
                arg if arg == dungeon_on_dregg::KP_CLAIM_BLUE as i64 => ShieldedCrownHand::Blue,
                _ => return Outcome::Refused("unknown crown choice".to_string()),
            };
            if !session.in_hall {
                return Outcome::Refused("the crown is not reachable yet".to_string());
            }
            if session.crown.is_some() {
                return Outcome::Refused("the crown owner slot is WriteOnce".to_string());
            }
            session.crown = Some(hand);
            session.landed += 1;
            Outcome::Landed {
                receipt: Default::default(),
                ended: false,
            }
        }

        fn verify(&self, session: &Self::Session) -> VerifyReport {
            VerifyReport::ok(session.landed)
        }

        fn render(&self, session: &Self::Session) -> Surface {
            Surface(ViewNode::Text(format!(
                "hall={} crown={:?}",
                session.in_hall, session.crown
            )))
        }

        fn price(&self, _input: &Action) -> RunCost {
            RunCost::free()
        }
    }

    fn dungeon_host(session: &SessionId) -> OfferingHost {
        let mut host = OfferingHost::new();
        host.register("dungeon", "shielded crown fixture", CrownOffering);
        host.open_session("dungeon", session.clone(), SessionConfig::with_seed(31_337))
            .expect("dungeon opens");
        host
    }

    fn advance_to_hall(host: &mut OfferingHost, ledger: &GameEpochLedger, session: &SessionId) {
        let bound = ledger.bound_session("dungeon", session).unwrap();
        let view = inspect_bound_game_session(
            host,
            ledger.host_incarnation(),
            ledger.current_generation("dungeon", session).unwrap(),
            bound.clone(),
            &GameAudience::Shared,
        )
        .unwrap();
        let (reference, action) = view
            .affordances
            .iter()
            .find_map(|affordance| match affordance {
                GameAffordance::Turn {
                    reference, action, ..
                } if action.arg == KP_PRESS_ON as i64 => Some((reference.clone(), action.clone())),
                _ => None,
            })
            .expect("gatehall offers press-on");
        let result = execute_bound_asserted_game_command(
            host,
            ledger.host_incarnation(),
            ledger.current_generation("dungeon", session).unwrap(),
            &bound,
            GameCommand::Turn { reference, action },
            DreggIdentity("pathfinder".to_string()),
        )
        .unwrap();
        assert!(matches!(result, GameResult::Landed(_)));
    }

    fn fixture_policy(signer: &TurnSigner) -> ShieldedCrownPolicy {
        ShieldedCrownPolicy::new(
            [0x18; 32],
            9,
            [0x71; 32],
            [0x79; 32],
            PrivateFheggWinnerRoute::new(
                DreggIdentity("bazaar:winner".to_string()),
                signer.pubkey_hex(),
            )
            .unwrap(),
        )
        .unwrap()
    }

    fn attempt_fixture_source_reuse(
        host: &mut OfferingHost,
        ledger: &GameEpochLedger,
        policy: &ShieldedCrownPolicy,
        signer: &TurnSigner,
        session_name: &str,
        hand: ShieldedCrownHand,
        apex_variant: u8,
        spend_variant: u8,
    ) -> ShieldedCrownOrchestrationError {
        let session = SessionId::new(session_name);
        host.open_session(
            "dungeon",
            session.clone(),
            SessionConfig::with_seed(8 + u64::from(apex_variant) + u64::from(spend_variant)),
        )
        .unwrap();
        ledger.bind_after_ensure("dungeon", &session, true).unwrap();
        advance_to_hall(host, ledger, &session);
        let action = host
            .actions("dungeon", &session)
            .unwrap()
            .into_iter()
            .find(|action| action.arg == hand.choice_index())
            .unwrap();
        execute_shielded_crown_with_factory(
            host,
            ledger,
            policy.winner_route(),
            ShieldedCrownAction {
                session: session.clone(),
                hand,
                signed_action: signer.sign("dungeon", &session, 0, action),
            },
            |reference, action| {
                PrivateFheggGameConsequenceGate::fixture_shielded_crown_sources(
                    policy.winner_route.clone(),
                    ledger,
                    reference,
                    action,
                    apex_variant,
                    spend_variant,
                )
            },
        )
        .expect_err("a previously consumed source credential must block recombination")
    }

    #[test]
    fn shielded_crown_lands_and_authorization_replay_is_refused_after_restart() {
        let directory = tempfile::tempdir().unwrap();
        let session = SessionId::new("shielded-crown:restart");
        let ledger = GameEpochLedger::open(directory.path()).unwrap();
        let mut host = dungeon_host(&session);
        assert_eq!(
            ledger.bind_after_ensure("dungeon", &session, true).unwrap(),
            1
        );
        advance_to_hall(&mut host, &ledger, &session);

        let signer = TurnSigner::from_seed([0x51; 32]);
        let policy = fixture_policy(&signer);
        let crown_action = inspect_bound_game_session(
            &host,
            ledger.host_incarnation(),
            1,
            ledger.bound_session("dungeon", &session).unwrap(),
            &GameAudience::Shared,
        )
        .unwrap()
        .affordances
        .into_iter()
        .find_map(|affordance| match affordance {
            GameAffordance::Turn { action, .. }
                if action.arg == dungeon_on_dregg::KP_CLAIM_RED as i64 =>
            {
                Some(action)
            }
            _ => None,
        })
        .unwrap();
        let request = ShieldedCrownAction {
            session: session.clone(),
            hand: ShieldedCrownHand::Red,
            signed_action: signer.sign("dungeon", &session, 0, crown_action),
        };
        let receipt = execute_shielded_crown_with_factory(
            &mut host,
            &ledger,
            policy.winner_route(),
            request.clone(),
            |reference, action| {
                PrivateFheggGameConsequenceGate::fixture_shielded_crown(
                    policy.winner_route.clone(),
                    &ledger,
                    reference,
                    action,
                )
            },
        )
        .expect("the private winner lands the exact crown turn");
        assert!(receipt.binding_verifies());
        let redacted_debug = format!(
            "{:?}",
            ShieldedCrownOrchestrationError::LandedAwaitingDurability {
                receipt: receipt.clone(),
                cause: GameEpochError::MissingAuthorization([0xEE; 32]),
            }
        );
        assert!(!redacted_debug.contains("bazaar:winner"));
        assert!(!redacted_debug.contains(&session.0));
        assert_eq!(
            ledger
                .authorization_phase(receipt.authorization_id)
                .unwrap(),
            Some(GameAuthorizationPhase::Consumed)
        );
        assert_eq!(host.verify("dungeon", &session).unwrap().turns, 2);

        // The journal key is the private source use, not the selected action.
        // Rebinding the same apex/tender fixture to Blue in another session
        // must therefore find the exact same consumed id.
        let cross_target = attempt_fixture_source_reuse(
            &mut host,
            &ledger,
            &policy,
            &signer,
            "shielded-crown:cross-target",
            ShieldedCrownHand::Blue,
            0,
            0,
        );
        assert!(matches!(
            cross_target,
            ShieldedCrownOrchestrationError::AuthorizationAlreadyRecorded {
                authorization_id,
                phase: GameAuthorizationPhase::Consumed,
                ..
            } if authorization_id == receipt.authorization_id
        ));

        let changed_spend = attempt_fixture_source_reuse(
            &mut host,
            &ledger,
            &policy,
            &signer,
            "shielded-crown:same-apex-new-spend",
            ShieldedCrownHand::Red,
            0,
            1,
        );
        assert!(matches!(
            changed_spend,
            ShieldedCrownOrchestrationError::AuthorizationAlreadyRecorded {
                authorization_id,
                source_use_id,
                phase: GameAuthorizationPhase::Consumed,
            } if authorization_id != receipt.authorization_id
                && source_use_id != receipt.authorization_id
        ));

        let changed_apex = attempt_fixture_source_reuse(
            &mut host,
            &ledger,
            &policy,
            &signer,
            "shielded-crown:new-apex-same-spend",
            ShieldedCrownHand::Blue,
            1,
            0,
        );
        assert!(matches!(
            changed_apex,
            ShieldedCrownOrchestrationError::AuthorizationAlreadyRecorded {
                authorization_id,
                source_use_id,
                phase: GameAuthorizationPhase::Consumed,
            } if authorization_id != receipt.authorization_id
                && source_use_id != receipt.authorization_id
        ));

        let incarnation = ledger.host_incarnation();
        drop(ledger);
        let restarted = GameEpochLedger::open(directory.path()).unwrap();
        assert_eq!(restarted.host_incarnation(), incarnation);

        // Model a correctly restored pre-crown game snapshot. Its signer
        // counter has no memory of the first process, so only the durable
        // private-authorization journal can refuse this exact replay.
        let mut restored_host = dungeon_host(&session);
        assert_eq!(
            restarted
                .bind_after_ensure("dungeon", &session, false)
                .unwrap(),
            1
        );
        advance_to_hall(&mut restored_host, &restarted, &session);
        let replay = execute_shielded_crown_with_factory(
            &mut restored_host,
            &restarted,
            policy.winner_route(),
            request,
            |reference, action| {
                PrivateFheggGameConsequenceGate::fixture_shielded_crown(
                    policy.winner_route.clone(),
                    &restarted,
                    reference,
                    action,
                )
            },
        )
        .expect_err("restart must not reopen a private authorization");
        assert!(matches!(
            replay,
            ShieldedCrownOrchestrationError::AuthorizationAlreadyRecorded {
                authorization_id,
                phase: GameAuthorizationPhase::Consumed,
                ..
            } if authorization_id == receipt.authorization_id
        ));
        assert_eq!(restored_host.verify("dungeon", &session).unwrap().turns, 1);
    }

    #[test]
    fn wrong_signer_is_refused_before_private_authority_construction_or_reservation() {
        let incarnation = GameHostIncarnation::new([0x91; 32]).unwrap();
        let ledger = GameEpochLedger::in_memory(incarnation);
        let session = SessionId::new("shielded-crown:wrong-signer");
        let mut host = dungeon_host(&session);
        ledger.bind_after_ensure("dungeon", &session, true).unwrap();
        advance_to_hall(&mut host, &ledger, &session);
        let winner = TurnSigner::from_seed([0x51; 32]);
        let thief = TurnSigner::from_seed([0x52; 32]);
        let policy = fixture_policy(&winner);
        let action = host
            .actions("dungeon", &session)
            .unwrap()
            .into_iter()
            .find(|action| action.arg == dungeon_on_dregg::KP_CLAIM_BLUE as i64)
            .unwrap();
        let request = ShieldedCrownAction {
            session: session.clone(),
            hand: ShieldedCrownHand::Blue,
            signed_action: thief.sign("dungeon", &session, 0, action),
        };
        let error = execute_shielded_crown_with_factory(
            &mut host,
            &ledger,
            policy.winner_route(),
            request,
            |_reference, _action| panic!("wrong signer must be rejected before private work"),
        )
        .unwrap_err();
        assert_eq!(error, ShieldedCrownOrchestrationError::WrongGameSigner);
        assert_eq!(host.verify("dungeon", &session).unwrap().turns, 1);

        let action = host
            .actions("dungeon", &session)
            .unwrap()
            .into_iter()
            .find(|action| action.arg == dungeon_on_dregg::KP_CLAIM_BLUE as i64)
            .unwrap();
        let mut forged = winner.sign("dungeon", &session, 0, action);
        forged.signature[0] ^= 1;
        let error = execute_shielded_crown_with_factory(
            &mut host,
            &ledger,
            policy.winner_route(),
            ShieldedCrownAction {
                session: session.clone(),
                hand: ShieldedCrownHand::Blue,
                signed_action: forged,
            },
            |_reference, _action| {
                panic!("bad winner signature must be rejected before private work")
            },
        )
        .unwrap_err();
        assert_eq!(
            error,
            ShieldedCrownOrchestrationError::Signature(SignedError::BadSignature)
        );
    }

    #[test]
    fn post_reservation_failure_leaves_a_replay_blocking_reserved_record() {
        let incarnation = GameHostIncarnation::new([0x92; 32]).unwrap();
        let ledger = GameEpochLedger::in_memory(incarnation);
        let session = SessionId::new("shielded-crown:sealed-refusal");
        let mut host = dungeon_host(&session);
        ledger.bind_after_ensure("dungeon", &session, true).unwrap();
        advance_to_hall(&mut host, &ledger, &session);
        let signer = TurnSigner::from_seed([0x53; 32]);
        let policy = fixture_policy(&signer);
        let action = host
            .actions("dungeon", &session)
            .unwrap()
            .into_iter()
            .find(|action| action.arg == dungeon_on_dregg::KP_CLAIM_RED as i64)
            .unwrap();
        let request = ShieldedCrownAction {
            session: session.clone(),
            hand: ShieldedCrownHand::Red,
            signed_action: signer.sign("dungeon", &session, 0, action),
        };
        let error = execute_shielded_crown_with_factory(
            &mut host,
            &ledger,
            policy.winner_route(),
            request,
            |reference, action| {
                let gate = PrivateFheggGameConsequenceGate::fixture_shielded_crown(
                    policy.winner_route.clone(),
                    &ledger,
                    reference,
                    action,
                )?;
                assert!(ledger.mark_closed("dungeon", &session).unwrap());
                Ok(gate)
            },
        )
        .expect_err("epoch loss after construction must fail closed");
        let authorization_id = match error {
            ShieldedCrownOrchestrationError::ExecutionSealed {
                authorization_id, ..
            } => authorization_id,
            other => panic!("expected a sealed execution failure, got {other:?}"),
        };
        assert_eq!(
            ledger.authorization_phase(authorization_id).unwrap(),
            Some(GameAuthorizationPhase::Reserved)
        );
        assert_eq!(host.verify("dungeon", &session).unwrap().turns, 1);
    }
}
