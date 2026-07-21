use deos_view::ViewNode;
use dreggnet_catalog::{
    CatalogConfig, GameActionRef, GameAffordance, GameAudience, GameCommand, GameHostIncarnation,
    GameKind, GameOperationRef, GameReceipt, GameResult, GameSessionRef, GameSpineError,
    execute_asserted_game_command, execute_bound_asserted_game_command, execute_signed_game_turn,
    full_catalog_host, inspect_bound_game_session, inspect_game_session,
};
use dreggnet_offerings::{
    Action, Attribution, BinaryOperationDescriptor, BinaryOperationError, BinaryOperationReceipt,
    BinaryOperationReplayMaterial, DreggIdentity, InMemoryResumeStore, Offering, OfferingError,
    OfferingHost, Outcome, RunCost, SessionConfig, SessionId, Surface, TurnSigner, VerifyReport,
};

fn primary_turn(view: &dreggnet_catalog::GameSessionView) -> (GameActionRef, Action) {
    view.affordances
        .iter()
        .find_map(|affordance| match affordance {
            GameAffordance::Turn {
                reference, action, ..
            } if action.enabled => Some((reference.clone(), action.clone())),
            _ => None,
        })
        .expect("game exposes an enabled initial turn")
}

fn primary_operation(view: &dreggnet_catalog::GameSessionView) -> GameOperationRef {
    view.affordances
        .iter()
        .find_map(|affordance| match affordance {
            GameAffordance::Operation { reference, .. } => Some(reference.clone()),
            _ => None,
        })
        .expect("game exposes an operation")
}

#[test]
fn descent_dungeon_and_bazaar_share_one_address_affordance_receipt_and_resume_spine() {
    let cfg = CatalogConfig::default();
    let store = InMemoryResumeStore::new();
    let shared_surface_token = SessionId::new("player-session-73");
    let actor = DreggIdentity("player:coherent-spine".to_string());
    let games = [
        ("descent", GameKind::Descent, 73),
        ("dungeon", GameKind::Dungeon, 74),
        ("bazaar", GameKind::DarkBazaarCrawl, 75),
    ];

    let (before_restart, receipt_ids) = {
        let mut host = full_catalog_host(&cfg).with_resume_store(Box::new(store.clone()));
        let mut commitments = Vec::new();
        let mut receipt_ids = Vec::new();

        for (key, kind, seed) in games {
            host.open_session(
                key,
                shared_surface_token.clone(),
                SessionConfig::with_seed(seed),
            )
            .expect("catalog game opens at the explicit stable address");
            let session = GameSessionRef::new(key, shared_surface_token.clone()).unwrap();
            assert_eq!(session.kind(), kind);

            let view = inspect_game_session(
                &host,
                session.clone(),
                &GameAudience::AssertedPrivate(actor.clone()),
            )
            .expect("one common session view");
            assert_eq!(view.session, session);
            assert_eq!(view.kind, kind);
            assert!(view.replay_journal_present);
            assert_eq!(
                view.viewer_attribution,
                Some(Attribution::Asserted {
                    label: actor.0.clone()
                })
            );
            assert_eq!(view.landed_steps, 0);
            assert!(!view.affordances.is_empty());

            let (reference, action) = primary_turn(&view);
            let result = execute_asserted_game_command(
                &mut host,
                &session,
                GameCommand::Turn { reference, action },
                actor.clone(),
            )
            .expect("the common command route reaches the concrete game");
            let receipt = result.receipt().expect("the initial legal turn lands");
            assert_eq!(receipt.session(), &session);
            assert_eq!(receipt.attribution(), &Attribution::from(actor.clone()));
            assert_ne!(receipt.receipt_id(), [0; 32]);
            receipt_ids.push(receipt.receipt_id());

            let after = inspect_game_session(
                &host,
                session,
                &GameAudience::AssertedPrivate(actor.clone()),
            )
            .expect("advanced common session view");
            assert!(after.verification.verified, "{}", after.verification.detail);
            assert_eq!(after.landed_steps, 1);
            commitments.push(after.surface_commitment);
        }
        (commitments, receipt_ids)
    };

    assert_eq!(
        receipt_ids
            .iter()
            .collect::<std::collections::BTreeSet<_>>()
            .len(),
        3,
        "three rule engines return the same receipt vocabulary without aliasing receipts"
    );

    let mut restarted = full_catalog_host(&cfg).with_resume_store(Box::new(store.clone()));
    let resumed = restarted.resume_all();
    assert_eq!(resumed.len(), 3);
    assert!(
        resumed.iter().all(|(_, result)| result.is_ok()),
        "{resumed:?}"
    );

    for ((key, kind, _), expected_commitment) in games.into_iter().zip(before_restart) {
        let session = GameSessionRef::new(key, shared_surface_token.clone()).unwrap();
        let view = inspect_game_session(&restarted, session, &GameAudience::Shared)
            .expect("same structured address resumes on a different surface");
        assert_eq!(view.kind, kind);
        assert_eq!(view.surface_commitment, expected_commitment);
        assert_eq!(view.landed_steps, 1);
        assert!(view.verification.verified, "{}", view.verification.detail);
    }
}

#[test]
fn a_command_cannot_be_spliced_between_game_sessions_or_detached_from_its_action_ref() {
    let cfg = CatalogConfig::default();
    let mut host = full_catalog_host(&cfg);
    let token = SessionId::new("same-token-different-games");
    for key in ["descent", "dungeon"] {
        host.open_session(key, token.clone(), SessionConfig::with_seed(91))
            .unwrap();
    }
    let actor = DreggIdentity("player:route-falsifier".to_string());
    let descent = GameSessionRef::new("descent", token.clone()).unwrap();
    let dungeon = GameSessionRef::new("dungeon", token).unwrap();
    assert_ne!(descent, dungeon, "offering key is part of session identity");
    let dark_pool = GameSessionRef::new("dark-pool", SessionId::new("same-token-different-games"))
        .expect("the opt-in encrypted apex is admitted by the common spine");
    let bazaar_crawl =
        GameSessionRef::new("bazaar", SessionId::new("same-token-different-games")).unwrap();
    assert_eq!(dark_pool.kind(), GameKind::DarkPool);
    assert_eq!(bazaar_crawl.kind(), GameKind::DarkBazaarCrawl);
    assert_ne!(
        dark_pool, bazaar_crawl,
        "the public crawl and encrypted apex never alias at the same surface token"
    );

    let dungeon_view = inspect_game_session(
        &host,
        dungeon.clone(),
        &GameAudience::AssertedPrivate(actor.clone()),
    )
    .unwrap();
    let (reference, action) = primary_turn(&dungeon_view);
    let descent_before = host
        .commitment(descent.offering(), descent.session_id())
        .unwrap();
    let dungeon_before = host
        .commitment(dungeon.offering(), dungeon.session_id())
        .unwrap();

    let cross = execute_asserted_game_command(
        &mut host,
        &descent,
        GameCommand::Turn {
            reference: reference.clone(),
            action: action.clone(),
        },
        actor.clone(),
    );
    assert!(matches!(cross, Err(GameSpineError::AddressMismatch { .. })));

    let mut detached = action;
    detached.turn = "forged-turn".to_string();
    let detached = execute_asserted_game_command(
        &mut host,
        &dungeon,
        GameCommand::Turn {
            reference,
            action: detached,
        },
        actor.clone(),
    );
    assert!(matches!(detached, Err(GameSpineError::InvalidReference(_))));

    // A self-consistent but game-illegal route still reaches the real Dungeon
    // interpreter and returns its refusal with no receipt.  The spine is a
    // router, not a second admission implementation.
    let forged = Action::new("forged", "not-a-dungeon-move", 404, true);
    let forged_ref = GameActionRef::new(dungeon.clone(), &forged, dungeon_before.clone());
    let refused = execute_asserted_game_command(
        &mut host,
        &dungeon,
        GameCommand::Turn {
            reference: forged_ref,
            action: forged,
        },
        actor,
    )
    .unwrap();
    assert!(matches!(refused, GameResult::Refused { .. }));
    assert!(refused.receipt().is_none());

    assert_eq!(
        host.commitment(descent.offering(), descent.session_id()),
        Some(descent_before)
    );
    assert_eq!(
        host.commitment(dungeon.offering(), dungeon.session_id()),
        Some(dungeon_before)
    );
    assert_eq!(
        host.move_log("descent", descent.session_id())
            .unwrap()
            .len(),
        0
    );
    assert_eq!(
        host.move_log("dungeon", dungeon.session_id())
            .unwrap()
            .len(),
        0
    );
}

struct AmbiguousDungeon;

impl Offering for AmbiguousDungeon {
    type Session = ();

    fn open(&self, _cfg: SessionConfig) -> Result<Self::Session, OfferingError> {
        Ok(())
    }

    fn actions(&self, _session: &Self::Session) -> Vec<Action> {
        vec![
            Action::new("left label", "choose", 0, true),
            Action::new("right label", "choose", 0, true),
        ]
    }

    fn advance(
        &self,
        _session: &mut Self::Session,
        _input: Action,
        _actor: DreggIdentity,
    ) -> Outcome {
        panic!("ambiguous routes must fail discovery before execution")
    }

    fn verify(&self, _session: &Self::Session) -> VerifyReport {
        VerifyReport::ok(0)
    }

    fn render(&self, _session: &Self::Session) -> Surface {
        Surface(ViewNode::Text("ambiguous".to_string()))
    }

    fn price(&self, _input: &Action) -> RunCost {
        RunCost::free()
    }
}

#[test]
fn ambiguous_surface_routes_fail_closed_instead_of_becoming_frontend_dependent() {
    let mut host = OfferingHost::new();
    host.register("dungeon", "hostile duplicate", AmbiguousDungeon);
    let id = SessionId::new("duplicate-route");
    host.open_session("dungeon", id.clone(), SessionConfig::default())
        .unwrap();
    let reference = GameSessionRef::new("dungeon", id).unwrap();
    let error = inspect_game_session(&host, reference, &GameAudience::Shared).unwrap_err();
    assert!(matches!(error, GameSpineError::AmbiguousAffordance(_)));
}

#[derive(Clone, Debug)]
struct ChoiceState {
    seed: u64,
    landed: u64,
}

struct ChoiceDungeon;

impl Offering for ChoiceDungeon {
    type Session = ChoiceState;

    fn open(&self, cfg: SessionConfig) -> Result<Self::Session, OfferingError> {
        Ok(ChoiceState {
            seed: cfg.seed.unwrap_or(0),
            landed: 0,
        })
    }

    fn actions(&self, _session: &Self::Session) -> Vec<Action> {
        vec![
            Action::new("left", "choose", 0, true).with_text("left-text"),
            Action::new("right", "choose", 1, true).with_text("right-text"),
            Action::new("other prose", "choose", 0, true).with_text("other-text"),
        ]
    }

    fn advance(
        &self,
        session: &mut Self::Session,
        input: Action,
        _actor: DreggIdentity,
    ) -> Outcome {
        if input.turn != "choose" {
            return Outcome::Refused("not a choice".to_string());
        }
        session.landed += 1;
        Outcome::Landed {
            receipt: Default::default(),
            ended: false,
        }
    }

    fn verify(&self, session: &Self::Session) -> VerifyReport {
        VerifyReport::ok(session.landed as usize)
    }

    fn render(&self, session: &Self::Session) -> Surface {
        Surface(ViewNode::Text(format!(
            "seed={} landed={}",
            session.seed, session.landed
        )))
    }

    fn render_for(&self, session: &Self::Session, viewer: &DreggIdentity) -> Surface {
        Surface(ViewNode::Text(format!(
            "seed={} landed={} private-for={}",
            session.seed, session.landed, viewer.0
        )))
    }

    fn hidden_information(&self) -> bool {
        true
    }

    fn price(&self, _input: &Action) -> RunCost {
        RunCost::free()
    }
}

#[test]
fn full_action_identity_and_observed_head_reject_choice_text_and_reopen_splices() {
    let mut host = OfferingHost::new();
    host.register("dungeon", "choice identity fixture", ChoiceDungeon);
    let id = SessionId::new("choice-session");
    host.open_session("dungeon", id.clone(), SessionConfig::with_seed(11))
        .unwrap();
    let session = GameSessionRef::new("dungeon", id.clone()).unwrap();
    let victim = DreggIdentity("victim-without-a-signature".to_string());
    let view = inspect_game_session(
        &host,
        session.clone(),
        &GameAudience::AssertedPrivate(victim.clone()),
    )
    .unwrap();
    assert!(view.projection.private);
    assert_eq!(
        view.viewer_attribution,
        Some(Attribution::Asserted {
            label: victim.0.clone()
        }),
        "a caller-selected private viewer remains visibly asserted, never authenticated"
    );
    assert!(!view.viewer_attribution.as_ref().unwrap().is_signed());

    let turns: Vec<_> = view
        .affordances
        .iter()
        .filter_map(|affordance| match affordance {
            GameAffordance::Turn {
                reference, action, ..
            } => Some((reference.clone(), action.clone())),
            _ => None,
        })
        .collect();
    assert_eq!(turns.len(), 3);
    let distinct_refs: std::collections::BTreeSet<_> = turns
        .iter()
        .map(|(reference, _)| {
            (
                reference.turn.clone(),
                reference.arg,
                reference.text.clone(),
            )
        })
        .collect();
    assert_eq!(distinct_refs.len(), 3);

    let left = turns
        .iter()
        .find(|(_, action)| action.arg == 0 && action.text.as_deref() == Some("left-text"))
        .unwrap();
    let right = turns.iter().find(|(_, action)| action.arg == 1).unwrap();
    let other_text = turns
        .iter()
        .find(|(_, action)| action.text.as_deref() == Some("other-text"))
        .unwrap();
    for substituted in [&right.1, &other_text.1] {
        let error = execute_asserted_game_command(
            &mut host,
            &session,
            GameCommand::Turn {
                reference: left.0.clone(),
                action: substituted.clone(),
            },
            victim.clone(),
        )
        .unwrap_err();
        assert!(matches!(error, GameSpineError::InvalidReference(_)));
    }
    assert_eq!(host.verify("dungeon", &id).unwrap().turns, 0);

    let captured_reference = left.0.clone();
    let captured_action = left.1.clone();
    assert!(host.close("dungeon", &id));
    host.open_session("dungeon", id, SessionConfig::with_seed(12))
        .unwrap();
    let stale = execute_asserted_game_command(
        &mut host,
        &session,
        GameCommand::Turn {
            reference: captured_reference,
            action: captured_action,
        },
        victim,
    )
    .unwrap_err();
    assert!(matches!(stale, GameSpineError::StaleCommand { .. }));
}

#[test]
fn signed_turn_path_preserves_verified_attribution_instead_of_upgrading_a_label() {
    let mut host = OfferingHost::new();
    host.register("dungeon", "signed choice fixture", ChoiceDungeon);
    let id = SessionId::new("signed-choice");
    host.open_session("dungeon", id.clone(), SessionConfig::with_seed(13))
        .unwrap();
    let session = GameSessionRef::new("dungeon", id.clone()).unwrap();
    let view = inspect_game_session(&host, session.clone(), &GameAudience::Shared).unwrap();
    let (reference, action) = primary_turn(&view);
    let signer = TurnSigner::from_seed([31; 32]);
    let signed = signer.sign("dungeon", &id, 0, action);
    let result = execute_signed_game_turn(&mut host, &session, reference, signed).unwrap();
    assert_eq!(
        result.receipt().unwrap().attribution(),
        &Attribution::Signed {
            pubkey_hex: signer.pubkey_hex().to_string()
        }
    );
    let log = host.move_log("dungeon", &id).unwrap();
    assert_eq!(
        log.moves[0].attribution,
        Attribution::Signed {
            pubkey_hex: signer.pubkey_hex().to_string()
        }
    );
}

#[derive(Clone, Debug)]
struct BoundOperationState {
    seed: u64,
    value: u64,
}

struct BoundOperationDungeon {
    replayable: bool,
}

impl Offering for BoundOperationDungeon {
    type Session = BoundOperationState;

    fn open(&self, cfg: SessionConfig) -> Result<Self::Session, OfferingError> {
        Ok(BoundOperationState {
            seed: cfg.seed.unwrap_or(0),
            value: 0,
        })
    }

    fn actions(&self, _session: &Self::Session) -> Vec<Action> {
        Vec::new()
    }

    fn advance(
        &self,
        _session: &mut Self::Session,
        _input: Action,
        _actor: DreggIdentity,
    ) -> Outcome {
        Outcome::Refused("binary-only fixture".to_string())
    }

    fn verify(&self, session: &Self::Session) -> VerifyReport {
        VerifyReport::ok(session.value as usize)
    }

    fn render(&self, session: &Self::Session) -> Surface {
        Surface(ViewNode::Text(format!(
            "seed={} value={}",
            session.seed, session.value
        )))
    }

    fn binary_operations(&self, _session: &Self::Session) -> Vec<BinaryOperationDescriptor> {
        vec![BinaryOperationDescriptor {
            name: "resolve.v1".to_string(),
            title: "Resolve".to_string(),
            input_media_type: "application/x-one-byte".to_string(),
            max_input_bytes: 1,
            disclosure: "one public test byte".to_string(),
        }]
    }

    fn binary_operation_replay_material(
        &self,
        _session: &Self::Session,
        name: &str,
        payload: &[u8],
    ) -> Result<Option<BinaryOperationReplayMaterial>, BinaryOperationError> {
        if name != "resolve.v1" {
            return Err(BinaryOperationError::UnknownOperation(name.to_string()));
        }
        if payload.len() != 1 {
            return Err(BinaryOperationError::Malformed(
                "expected one byte".to_string(),
            ));
        }
        Ok(self
            .replayable
            .then(|| BinaryOperationReplayMaterial::new(payload.to_vec(), "one public test byte")))
    }

    fn invoke_binary_operation(
        &self,
        session: &mut Self::Session,
        name: &str,
        payload: &[u8],
        _actor: DreggIdentity,
    ) -> Result<BinaryOperationReceipt, BinaryOperationError> {
        if name != "resolve.v1" {
            return Err(BinaryOperationError::UnknownOperation(name.to_string()));
        }
        let [amount] = payload else {
            return Err(BinaryOperationError::Malformed(
                "expected one byte".to_string(),
            ));
        };
        session.value += u64::from(*amount);
        Ok(BinaryOperationReceipt {
            operation: name.to_string(),
            // Deliberately aliases across sessions and actors. The outer game
            // routing receipt is required to keep those host events distinct.
            receipt_id: *blake3::hash(b"deliberately constant inner receipt").as_bytes(),
            public_fields: vec![("value".to_string(), session.value.to_string())],
        })
    }

    fn price(&self, _input: &Action) -> RunCost {
        RunCost::free()
    }
}

fn bound_operation_host() -> OfferingHost {
    let mut host = OfferingHost::new();
    host.register(
        "dungeon",
        "host-address binding fixture",
        BoundOperationDungeon { replayable: true },
    );
    host
}

fn run_bound_operation(
    host: &mut OfferingHost,
    session: &GameSessionRef,
    actor: DreggIdentity,
) -> GameReceipt {
    let view = inspect_game_session(host, session.clone(), &GameAudience::Shared).unwrap();
    let reference = primary_operation(&view);
    let result = execute_asserted_game_command(
        host,
        session,
        GameCommand::Operation {
            reference,
            payload: vec![7],
        },
        actor,
    )
    .unwrap();
    result.receipt().unwrap().clone()
}

#[test]
fn operation_receipts_bind_host_session_and_asserted_actor_around_aliasing_inner_receipts() {
    let mut host = bound_operation_host();
    let first_id = SessionId::new("same-seed-a");
    let second_id = SessionId::new("same-seed-b");
    for id in [&first_id, &second_id] {
        host.open_session("dungeon", id.clone(), SessionConfig::with_seed(44))
            .unwrap();
    }
    let actor = DreggIdentity("asserted:alice".to_string());
    let first = run_bound_operation(
        &mut host,
        &GameSessionRef::new("dungeon", first_id).unwrap(),
        actor.clone(),
    );
    let second = run_bound_operation(
        &mut host,
        &GameSessionRef::new("dungeon", second_id).unwrap(),
        actor.clone(),
    );
    assert_eq!(first.inner_receipt_id(), second.inner_receipt_id());
    assert!(first.operation_routing_binding_valid());
    assert!(second.operation_routing_binding_valid());
    assert_ne!(
        first.receipt_id(),
        second.receipt_id(),
        "same-seed state and aliased inner receipts remain distinct at different host addresses"
    );

    let id = SessionId::new("same-address-fresh-host");
    let mut alice_host = bound_operation_host();
    let mut bob_host = bound_operation_host();
    for candidate in [&mut alice_host, &mut bob_host] {
        candidate
            .open_session("dungeon", id.clone(), SessionConfig::with_seed(55))
            .unwrap();
    }
    let address = GameSessionRef::new("dungeon", id).unwrap();
    let alice = run_bound_operation(
        &mut alice_host,
        &address,
        DreggIdentity("asserted:alice".to_string()),
    );
    let bob = run_bound_operation(
        &mut bob_host,
        &address,
        DreggIdentity("asserted:bob".to_string()),
    );
    assert_eq!(alice.inner_receipt_id(), bob.inner_receipt_id());
    assert_ne!(alice.receipt_id(), bob.receipt_id());
    assert!(matches!(alice.attribution(), Attribution::Asserted { .. }));
    assert!(matches!(bob.attribution(), Attribution::Asserted { .. }));
    let mut substituted_actor = alice.clone();
    if let GameReceipt::Operation { attribution, .. } = &mut substituted_actor {
        *attribution = Attribution::Asserted {
            label: "asserted:bob".to_string(),
        };
    }
    assert!(
        !substituted_actor.operation_routing_binding_valid(),
        "actor substitution breaks the exact bound envelope"
    );
}

#[test]
fn operation_execution_rechecks_live_byte_cap_before_any_mutation() {
    let mut host = bound_operation_host();
    let id = SessionId::new("oversized-operation");
    host.open_session("dungeon", id.clone(), SessionConfig::with_seed(66))
        .unwrap();
    let session = GameSessionRef::new("dungeon", id).unwrap();
    let view = inspect_game_session(&host, session.clone(), &GameAudience::Shared).unwrap();
    let reference = primary_operation(&view);
    let before = host
        .commitment(session.offering(), session.session_id())
        .unwrap();
    let error = execute_asserted_game_command(
        &mut host,
        &session,
        GameCommand::Operation {
            reference,
            payload: vec![1, 2],
        },
        DreggIdentity("asserted:oversize".to_string()),
    )
    .unwrap_err();
    assert!(matches!(error, GameSpineError::PayloadTooLarge { .. }));
    assert_eq!(
        host.commitment(session.offering(), session.session_id()),
        Some(before)
    );
    assert!(
        host.move_log(session.offering(), session.session_id())
            .unwrap()
            .operations
            .is_empty()
    );
}

#[test]
fn spine_refuses_an_unjournalable_operation_before_it_can_mutate() {
    let mut host = OfferingHost::new();
    host.register(
        "dungeon",
        "ephemeral operation fixture",
        BoundOperationDungeon { replayable: false },
    );
    let id = SessionId::new("ephemeral-operation");
    host.open_session("dungeon", id.clone(), SessionConfig::with_seed(77))
        .unwrap();
    let session = GameSessionRef::new("dungeon", id).unwrap();
    let view = inspect_game_session(&host, session.clone(), &GameAudience::Shared).unwrap();
    let reference = primary_operation(&view);
    let before = host
        .commitment(session.offering(), session.session_id())
        .unwrap();
    let error = execute_asserted_game_command(
        &mut host,
        &session,
        GameCommand::Operation {
            reference,
            payload: vec![9],
        },
        DreggIdentity("asserted:ephemeral".to_string()),
    )
    .unwrap_err();
    assert!(matches!(
        error,
        GameSpineError::UnreplayableOperation(ref name) if name == "resolve.v1"
    ));
    assert_eq!(
        host.commitment(session.offering(), session.session_id()),
        Some(before)
    );
    assert!(
        host.move_log(session.offering(), session.session_id())
            .unwrap()
            .operations
            .is_empty()
    );
}

#[test]
fn bound_session_rejects_cross_incarnation_and_generation_rollback_before_mutation() {
    let incarnation_a = GameHostIncarnation::new([0xA1; 32]).unwrap();
    let incarnation_b = GameHostIncarnation::new([0xB2; 32]).unwrap();
    let id = SessionId::new("same-human-name-and-state");
    let mut host = OfferingHost::new();
    host.register("dungeon", "authority epoch fixture", ChoiceDungeon);
    host.open_session("dungeon", id.clone(), SessionConfig::with_seed(91))
        .unwrap();

    let generation_seven = GameSessionRef::bound("dungeon", id.clone(), incarnation_a, 7).unwrap();
    let view = inspect_bound_game_session(
        &host,
        incarnation_a,
        7,
        generation_seven.clone(),
        &GameAudience::Shared,
    )
    .unwrap();
    let (captured_reference, captured_action) = primary_turn(&view);
    let captured_head = view.surface_commitment.clone();

    let cross_host = execute_bound_asserted_game_command(
        &mut host,
        incarnation_b,
        7,
        &generation_seven,
        GameCommand::Turn {
            reference: captured_reference.clone(),
            action: captured_action.clone(),
        },
        DreggIdentity("asserted:cross-host".to_string()),
    )
    .unwrap_err();
    assert!(matches!(
        cross_host,
        GameSpineError::AuthorityEpochMismatch { .. }
    ));
    assert_eq!(host.verify("dungeon", &id).unwrap().turns, 0);

    assert!(host.close("dungeon", &id));
    host.open_session("dungeon", id.clone(), SessionConfig::with_seed(91))
        .unwrap();
    assert_eq!(
        host.commitment("dungeon", &id).unwrap(),
        captured_head,
        "the hostile reopen deliberately recreates the same presentation head"
    );
    let rollback = execute_bound_asserted_game_command(
        &mut host,
        incarnation_a,
        8,
        &generation_seven,
        GameCommand::Turn {
            reference: captured_reference,
            action: captured_action,
        },
        DreggIdentity("asserted:generation-rollback".to_string()),
    )
    .unwrap_err();
    assert!(matches!(
        rollback,
        GameSpineError::AuthorityEpochMismatch { .. }
    ));
    assert_eq!(host.verify("dungeon", &id).unwrap().turns, 0);

    let generation_eight = GameSessionRef::bound("dungeon", id, incarnation_a, 8).unwrap();
    let current = inspect_bound_game_session(
        &host,
        incarnation_a,
        8,
        generation_eight,
        &GameAudience::Shared,
    )
    .unwrap();
    assert_ne!(
        primary_turn(&view).0.routing_preimage_id(),
        primary_turn(&current).0.routing_preimage_id(),
        "generation is part of the exact action router preimage even when state is identical"
    );
}

#[test]
fn same_incarnation_and_generation_resume_exactly_across_host_restart() {
    let incarnation = GameHostIncarnation::new([0xC3; 32]).unwrap();
    let store = InMemoryResumeStore::new();
    let id = SessionId::new("durable-bound-restart");
    let session = GameSessionRef::bound("dungeon", id.clone(), incarnation, 19).unwrap();

    let expected_after = {
        let mut host = OfferingHost::new().with_resume_store(Box::new(store.clone()));
        host.register("dungeon", "authority restart fixture", ChoiceDungeon);
        host.open_session("dungeon", id.clone(), SessionConfig::with_seed(123))
            .unwrap();
        let view = inspect_bound_game_session(
            &host,
            incarnation,
            19,
            session.clone(),
            &GameAudience::Shared,
        )
        .unwrap();
        let (reference, action) = primary_turn(&view);
        let landed = execute_bound_asserted_game_command(
            &mut host,
            incarnation,
            19,
            &session,
            GameCommand::Turn { reference, action },
            DreggIdentity("asserted:durable-player".to_string()),
        )
        .unwrap();
        let receipt = landed.receipt().unwrap();
        assert!(receipt.routing_binding_valid());
        inspect_bound_game_session(
            &host,
            incarnation,
            19,
            session.clone(),
            &GameAudience::Shared,
        )
        .unwrap()
        .surface_commitment
    };

    let mut restarted = OfferingHost::new().with_resume_store(Box::new(store));
    restarted.register("dungeon", "authority restart fixture", ChoiceDungeon);
    assert_eq!(restarted.resume_all().len(), 1);
    let resumed =
        inspect_bound_game_session(&restarted, incarnation, 19, session, &GameAudience::Shared)
            .unwrap();
    assert_eq!(resumed.surface_commitment, expected_after);
    assert_eq!(resumed.landed_steps, 1);
}

#[test]
fn receipt_binding_rejects_session_projection_substitution() {
    let incarnation = GameHostIncarnation::new([0xD4; 32]).unwrap();
    let other_incarnation = GameHostIncarnation::new([0xE5; 32]).unwrap();
    let id = SessionId::new("receipt-projection-binding");
    let session = GameSessionRef::bound("dungeon", id.clone(), incarnation, 3).unwrap();
    let mut host = OfferingHost::new();
    host.register("dungeon", "receipt projection fixture", ChoiceDungeon);
    host.open_session("dungeon", id.clone(), SessionConfig::with_seed(7))
        .unwrap();
    let view = inspect_bound_game_session(
        &host,
        incarnation,
        3,
        session.clone(),
        &GameAudience::Shared,
    )
    .unwrap();
    let (reference, action) = primary_turn(&view);
    let landed = execute_bound_asserted_game_command(
        &mut host,
        incarnation,
        3,
        &session,
        GameCommand::Turn { reference, action },
        DreggIdentity("asserted:projection-player".to_string()),
    )
    .unwrap();
    let receipt = landed.receipt().unwrap();
    assert_eq!(receipt.session(), &view.session);
    assert!(receipt.routing_binding_valid());

    let mut substituted = receipt.clone();
    let GameReceipt::Turn {
        action: projected_action,
        ..
    } = &mut substituted
    else {
        panic!("choice fixture returns a turn receipt")
    };
    projected_action.session = GameSessionRef::bound("dungeon", id, other_incarnation, 3).unwrap();
    assert!(
        !substituted.routing_binding_valid(),
        "moving an otherwise intact receipt beneath another projected session breaks its envelope"
    );

    assert!(matches!(
        inspect_game_session(&host, view.session, &GameAudience::Shared),
        Err(GameSpineError::BindingContextRequired(_))
    ));
}

#[test]
fn identical_opaque_operation_on_replacement_host_has_a_distinct_bound_receipt() {
    let incarnation_a = GameHostIncarnation::new([0x16; 32]).unwrap();
    let incarnation_b = GameHostIncarnation::new([0x27; 32]).unwrap();
    let id = SessionId::new("same-operation-replacement-host");
    let actor = DreggIdentity("asserted:same-actor".to_string());
    let session_a = GameSessionRef::bound("dungeon", id.clone(), incarnation_a, 5).unwrap();
    let session_b = GameSessionRef::bound("dungeon", id.clone(), incarnation_b, 5).unwrap();
    let mut host_a = bound_operation_host();
    let mut host_b = bound_operation_host();
    for host in [&mut host_a, &mut host_b] {
        host.open_session("dungeon", id.clone(), SessionConfig::with_seed(44))
            .unwrap();
    }

    let view_a = inspect_bound_game_session(
        &host_a,
        incarnation_a,
        5,
        session_a.clone(),
        &GameAudience::Shared,
    )
    .unwrap();
    let reference_a = primary_operation(&view_a);
    let captured = execute_bound_asserted_game_command(
        &mut host_b,
        incarnation_b,
        5,
        &session_a,
        GameCommand::Operation {
            reference: reference_a.clone(),
            payload: vec![7],
        },
        actor.clone(),
    )
    .unwrap_err();
    assert!(matches!(
        captured,
        GameSpineError::AuthorityEpochMismatch { .. }
    ));
    assert_eq!(host_b.verify("dungeon", &id).unwrap().turns, 0);

    let receipt_a = execute_bound_asserted_game_command(
        &mut host_a,
        incarnation_a,
        5,
        &session_a,
        GameCommand::Operation {
            reference: reference_a,
            payload: vec![7],
        },
        actor.clone(),
    )
    .unwrap()
    .receipt()
    .unwrap()
    .clone();
    let view_b = inspect_bound_game_session(
        &host_b,
        incarnation_b,
        5,
        session_b.clone(),
        &GameAudience::Shared,
    )
    .unwrap();
    let receipt_b = execute_bound_asserted_game_command(
        &mut host_b,
        incarnation_b,
        5,
        &session_b,
        GameCommand::Operation {
            reference: primary_operation(&view_b),
            payload: vec![7],
        },
        actor,
    )
    .unwrap()
    .receipt()
    .unwrap()
    .clone();
    assert_eq!(receipt_a.inner_receipt_id(), receipt_b.inner_receipt_id());
    assert_ne!(receipt_a.receipt_id(), receipt_b.receipt_id());
    assert!(receipt_a.routing_binding_valid());
    assert!(receipt_b.routing_binding_valid());

    let mut substituted = receipt_a;
    let GameReceipt::Operation { operation, .. } = &mut substituted else {
        panic!("binary fixture returns an operation receipt")
    };
    operation.session = session_b;
    assert!(!substituted.routing_binding_valid());
}
