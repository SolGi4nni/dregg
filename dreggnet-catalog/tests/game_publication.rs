use deos_view::ViewNode;
use dreggnet_catalog::{
    GameAffordance, GameAudience, GameCommand, GameHostIncarnation, GamePublicationError,
    GameReceipt, GameSessionRef, MAX_PUBLIC_GAME_FIELD_VALUE_BYTES, MAX_PUBLIC_GAME_FIELDS,
    PublicGameAttribution, PublicGameField, PublicGameReceiptResult,
    execute_bound_asserted_game_command, inspect_bound_game_session, project_public_game_receipt,
};
use dreggnet_offerings::{
    Action, Attribution, BinaryOperationDescriptor, BinaryOperationError, BinaryOperationReceipt,
    BinaryOperationReplayMaterial, DreggIdentity, Offering, OfferingError, OfferingHost, Outcome,
    RunCost, SessionConfig, SessionId, Surface, VerifyReport,
};

fn host_incarnation() -> GameHostIncarnation {
    GameHostIncarnation::new([0x73; 32]).unwrap()
}

fn enabled_turn(
    view: &dreggnet_catalog::GameSessionView,
) -> (dreggnet_catalog::GameActionRef, Action) {
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

struct OneMoveGame;

impl Offering for OneMoveGame {
    type Session = u64;

    fn open(&self, _cfg: SessionConfig) -> Result<Self::Session, OfferingError> {
        Ok(0)
    }

    fn actions(&self, _session: &Self::Session) -> Vec<Action> {
        vec![Action::new("enter", "enter", 0, true)]
    }

    fn advance(
        &self,
        session: &mut Self::Session,
        input: Action,
        _actor: DreggIdentity,
    ) -> Outcome {
        if input.turn != "enter" || input.arg != 0 || input.text.is_some() {
            return Outcome::Refused("not the exact fixture entrance".to_string());
        }
        *session += 1;
        Outcome::Landed {
            receipt: Default::default(),
            ended: false,
        }
    }

    fn verify(&self, session: &Self::Session) -> VerifyReport {
        VerifyReport::ok(*session as usize)
    }

    fn render(&self, session: &Self::Session) -> Surface {
        Surface(ViewNode::Text(format!("landed={session}")))
    }

    fn price(&self, _input: &Action) -> RunCost {
        RunCost::free()
    }
}

#[test]
fn descent_dungeon_and_bazaar_publish_one_opaque_grammar_without_losing_family() {
    let incarnation = host_incarnation();
    let generation = 9;
    let token = SessionId::new("private-player-route-must-not-appear");
    let actor = DreggIdentity("secret-actor-label-must-not-appear".to_string());
    // The owning game interpreters are covered by `game_spine` and the
    // offerings' real coherent-journey gate. Keep this publication-only test on
    // a tiny executor so it remains in the fast default profile even under
    // concurrent swarm load; the exact catalog route keys still exercise three
    // distinct GameKind/session-route domains.
    let mut host = OfferingHost::new();
    for offering in ["descent", "dungeon", "bazaar"] {
        host.register(offering, "one common-spine fixture", OneMoveGame);
    }
    let mut publications = Vec::new();

    for (offering, seed) in [("descent", 801), ("dungeon", 802), ("bazaar", 803)] {
        host.open_session(offering, token.clone(), SessionConfig::with_seed(seed))
            .unwrap();
        let session =
            GameSessionRef::bound(offering, token.clone(), incarnation, generation).unwrap();
        let view = inspect_bound_game_session(
            &host,
            incarnation,
            generation,
            session.clone(),
            &GameAudience::AssertedPrivate(actor.clone()),
        )
        .unwrap();
        let (reference, action) = enabled_turn(&view);
        let receipt = execute_bound_asserted_game_command(
            &mut host,
            incarnation,
            generation,
            &session,
            GameCommand::Turn { reference, action },
            actor.clone(),
        )
        .unwrap()
        .receipt()
        .unwrap()
        .clone();
        let public = project_public_game_receipt(&receipt).unwrap();
        assert_eq!(public.kind, session.kind());
        assert_eq!(public.receipt_id, receipt.receipt_id());
        assert_eq!(public.attribution, PublicGameAttribution::Asserted);
        assert!(matches!(
            public.result,
            PublicGameReceiptResult::Turn { .. }
        ));
        let debug = format!("{public:?}");
        assert!(
            !debug.contains(&token.0),
            "raw session route leaked: {debug}"
        );
        assert!(!debug.contains(&actor.0), "raw actor label leaked: {debug}");
        publications.push(public);
    }

    assert_eq!(
        publications
            .iter()
            .map(|receipt| receipt.kind)
            .collect::<std::collections::HashSet<_>>()
            .len(),
        3,
        "the common grammar retains three distinct rule families"
    );
    assert_eq!(
        publications
            .iter()
            .map(|receipt| receipt.session_route_id)
            .collect::<std::collections::BTreeSet<_>>()
            .len(),
        3,
        "the offering key prevents equal human session tokens from aliasing"
    );
}

#[derive(Clone)]
struct PublicOperationDungeon;

impl Offering for PublicOperationDungeon {
    type Session = u64;

    fn open(&self, _cfg: SessionConfig) -> Result<Self::Session, OfferingError> {
        Ok(0)
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
        VerifyReport::ok(*session as usize)
    }

    fn render(&self, session: &Self::Session) -> Surface {
        Surface(ViewNode::Text(format!("public root revision {session}")))
    }

    fn binary_operations(&self, _session: &Self::Session) -> Vec<BinaryOperationDescriptor> {
        vec![BinaryOperationDescriptor {
            name: "dungeon.chutes-narrated-turn.v1".to_string(),
            title: "private descriptor title".to_string(),
            input_media_type: "application/x-private-witness".to_string(),
            max_input_bytes: 1,
            disclosure: "fixture".to_string(),
        }]
    }

    fn binary_operation_replay_material(
        &self,
        _session: &Self::Session,
        name: &str,
        payload: &[u8],
    ) -> Result<Option<BinaryOperationReplayMaterial>, BinaryOperationError> {
        if name != "dungeon.chutes-narrated-turn.v1" || payload.len() != 1 {
            return Err(BinaryOperationError::Malformed(
                "wrong fixture input".to_string(),
            ));
        }
        Ok(Some(BinaryOperationReplayMaterial::new(
            payload.to_vec(),
            "fixture byte",
        )))
    }

    fn invoke_binary_operation(
        &self,
        session: &mut Self::Session,
        name: &str,
        payload: &[u8],
        actor: DreggIdentity,
    ) -> Result<BinaryOperationReceipt, BinaryOperationError> {
        *session += 1;
        Ok(BinaryOperationReceipt {
            operation: name.to_string(),
            receipt_id: *blake3::hash(b"public-operation-fixture").as_bytes(),
            public_fields: vec![
                ("narrationCommit".to_string(), "ab".repeat(32)),
                ("ended".to_string(), "false".to_string()),
                ("newRoot".to_string(), "root-1".to_string()),
                ("winner".to_string(), "north".to_string()),
                ("participant".to_string(), "alice".to_string()),
                ("candidateNonce".to_string(), "private-nonce".to_string()),
                ("privateWitness".to_string(), "witness-secret".to_string()),
                ("actor".to_string(), actor.0),
                ("payloadEcho".to_string(), hex(payload)),
            ],
        })
    }

    fn price(&self, _input: &Action) -> RunCost {
        RunCost::free()
    }
}

fn operation_receipt(bound: bool) -> GameReceipt {
    let incarnation = host_incarnation();
    let generation = 14;
    let mut host = OfferingHost::new();
    host.register("dungeon", "publication fixture", PublicOperationDungeon);
    let token = SessionId::new("raw-operation-session-secret");
    host.open_session("dungeon", token.clone(), SessionConfig::with_seed(17))
        .unwrap();
    let session = if bound {
        GameSessionRef::bound("dungeon", token, incarnation, generation).unwrap()
    } else {
        GameSessionRef::new("dungeon", token).unwrap()
    };
    let view = if bound {
        inspect_bound_game_session(
            &host,
            incarnation,
            generation,
            session.clone(),
            &GameAudience::Shared,
        )
        .unwrap()
    } else {
        dreggnet_catalog::inspect_game_session(&host, session.clone(), &GameAudience::Shared)
            .unwrap()
    };
    let reference = view
        .affordances
        .into_iter()
        .find_map(|affordance| match affordance {
            GameAffordance::Operation { reference, .. } => Some(reference),
            _ => None,
        })
        .unwrap();
    let command = GameCommand::Operation {
        reference,
        payload: vec![0xde],
    };
    let result = if bound {
        execute_bound_asserted_game_command(
            &mut host,
            incarnation,
            generation,
            &session,
            command,
            DreggIdentity("private-operation-actor".to_string()),
        )
    } else {
        dreggnet_catalog::execute_asserted_game_command(
            &mut host,
            &session,
            command,
            DreggIdentity("private-operation-actor".to_string()),
        )
    };
    result.unwrap().receipt().unwrap().clone()
}

#[test]
fn operation_publication_is_typed_deduplicated_and_viewer_blind() {
    let receipt = operation_receipt(true);
    let public = project_public_game_receipt(&receipt).unwrap();
    let PublicGameReceiptResult::Operation { fields } = &public.result else {
        panic!("expected operation publication")
    };
    assert_eq!(
        fields,
        &[
            dreggnet_catalog::PublicGameFieldValue {
                field: PublicGameField::Ended,
                value: "false".to_string(),
            },
            dreggnet_catalog::PublicGameFieldValue {
                field: PublicGameField::NarrationCommit,
                value: "ab".repeat(32),
            },
        ],
        "the exact Chutes policy omits allowlist-looking private outcome carriers"
    );
    assert!(public.binding_verifies());
    assert_eq!(public.validate(), Ok(()));
    let debug = format!("{public:?}");
    for secret in [
        "dungeon.chutes-narrated-turn.v1",
        "private-operation-actor",
        "raw-operation-session-secret",
        "witness-secret",
        "north",
        "alice",
        "private-nonce",
        "root-1",
    ] {
        assert!(!debug.contains(secret), "{secret:?} leaked in {debug}");
    }

    let mut disguised = receipt;
    if let GameReceipt::Operation { public_fields, .. } = &mut disguised {
        *public_fields = vec![(
            "narrationCommit".to_string(),
            "winner-is-alice-not-a-digest".to_string(),
        )];
    }
    let disguised = project_public_game_receipt(&disguised).unwrap();
    assert_eq!(
        disguised.result,
        PublicGameReceiptResult::Operation { fields: Vec::new() },
        "an allowed field name with a noncanonical value cannot smuggle private text"
    );
}

#[test]
fn publication_refuses_legacy_routes_forged_bindings_and_unbounded_fields() {
    assert_eq!(
        project_public_game_receipt(&operation_receipt(false)),
        Err(GamePublicationError::UnboundSession)
    );

    let receipt = operation_receipt(true);
    let mut forged_actor = receipt.clone();
    if let GameReceipt::Operation { attribution, .. } = &mut forged_actor {
        *attribution = Attribution::Asserted {
            label: "substituted-actor".to_string(),
        };
    }
    assert_eq!(
        project_public_game_receipt(&forged_actor),
        Err(GamePublicationError::InvalidRoutingBinding)
    );

    let mut too_many = receipt.clone();
    if let GameReceipt::Operation { public_fields, .. } = &mut too_many {
        *public_fields = (0..=MAX_PUBLIC_GAME_FIELDS)
            .map(|index| (format!("unknown-{index}"), "x".to_string()))
            .collect();
    }
    assert!(matches!(
        project_public_game_receipt(&too_many),
        Err(GamePublicationError::TooManyFields { .. })
    ));

    let mut oversized = receipt;
    if let GameReceipt::Operation { public_fields, .. } = &mut oversized {
        *public_fields = vec![(
            "narrationCommit".to_string(),
            "x".repeat(MAX_PUBLIC_GAME_FIELD_VALUE_BYTES + 1),
        )];
    }
    assert!(matches!(
        project_public_game_receipt(&oversized),
        Err(GamePublicationError::FieldValueTooLarge {
            field: PublicGameField::NarrationCommit,
            ..
        })
    ));
}

#[test]
fn publication_binding_detects_transport_substitution_and_noncanonical_fields() {
    let receipt = operation_receipt(true);
    let public = project_public_game_receipt(&receipt).unwrap();
    assert!(public.binding_verifies());
    assert_eq!(public.validate(), Ok(()));

    let mut changed = public.clone();
    let PublicGameReceiptResult::Operation { fields } = &mut changed.result else {
        panic!("expected operation publication")
    };
    fields[0].value = "true".to_string();
    assert!(!changed.binding_verifies());
    assert_eq!(
        changed.validate(),
        Err(GamePublicationError::InvalidPublicationBinding)
    );

    let mut duplicated = public;
    let PublicGameReceiptResult::Operation { fields } = &mut duplicated.result else {
        panic!("expected operation publication")
    };
    fields.push(fields[0].clone());
    assert!(!duplicated.binding_verifies());
    assert_eq!(
        duplicated.validate(),
        Err(GamePublicationError::InvalidPublicationBinding)
    );
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}
