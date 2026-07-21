//! Proof assignment → exact party capabilities → real tactical Arena, including durable replay.

use std::sync::OnceLock;

use deos_view::{AffordanceTransport, affordance_id_with_text, parse_affordance_id_with_text};
use dreggnet_offerings::resume::InMemoryResumeStore;
use dreggnet_offerings::{
    Action, Audience, BinaryOperationError, DreggIdentity, Offering, OfferingHost, SessionConfig,
    SessionId, project_for_audience,
};
use dreggnet_party::Role;
use dreggnet_surfaces::party::{
    TURN_ACT, TURN_CLAIM, TURN_FORK, TURN_LAUNCH, TURN_MISPLAY, TURN_READY, TURN_RESOLVE_FORK,
};
use dreggnet_surfaces::private_raid::{
    ASSIGN_OPERATION, HostedProofAssignedRaidOffering, KEY, MAX_STREAM_CHUNK_BYTES,
    MAX_STREAM_CHUNKS, ProofAssignedRaidOffering, TURN_ACCEPT_FHIR_ALLOCATION,
    TURN_FINALIZE_ASSIGNMENT, TURN_JOIN_RAID, TURN_PRIME_TACTIC, TURN_STREAM_ASSIGNMENT,
    proof_session_for_seed,
};
use dungeon_on_dregg::combat::{Arena, WARDEN, is_hero};
use dungeon_on_dregg::private_raid::{
    RaidAssignmentWireReceipt, RaidRole, prove_private_assignment,
};
use fhir::ast::{MatrixData, Product, ProductBody};
use fhir::{Compiled, ConvexProgram, build_exact_qp_certificate_bundle, compile};

fn roster() -> [String; 4] {
    ["player:alice", "player:bob", "player:cara", "player:devi"].map(str::to_string)
}

fn actor(name: &str) -> DreggIdentity {
    DreggIdentity(format!("player:{name}"))
}

fn action(turn: &str, arg: i64) -> Action {
    Action::new(turn, turn, arg, true)
}

fn hero_first_seed() -> u64 {
    static SEED: OnceLock<u64> = OnceLock::new();
    *SEED.get_or_init(|| {
        (0..=u8::MAX)
            .find(|candidate| is_hero(Arena::deploy(*candidate).active()))
            .expect("some deterministic Arena seed starts with a hero") as u64
    })
}

fn scores() -> [[u8; 4]; 4] {
    [[3, 2, 0, 0], [3, 0, 1, 0], [0, 0, 3, 1], [0, 1, 0, 3]]
}

fn proof_bytes() -> &'static [u8] {
    static PROOF: OnceLock<Vec<u8>> = OnceLock::new();
    PROOF.get_or_init(|| {
        prove_private_assignment(
            proof_session_for_seed(hero_first_seed()),
            scores(),
            [
                [false, true, true, true],
                [true, true, true, true],
                [true, true, true, true],
                [true, true, true, true],
            ],
        )
        .expect("the existing HidingFri assignment proves")
        .to_postcard()
        .expect("the verified assignment has a canonical wire image")
    })
}

fn lower_hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn round_trip_action_on_every_transport(template: &Action, text: Option<&str>) -> Action {
    let mut decoded = None;
    let transports: &[AffordanceTransport] = if text.is_some() {
        // The chat frontends collect text in a Discord modal / armed Telegram
        // reply. Web uses the owning binary-operation form for proof bytes.
        &[AffordanceTransport::Discord, AffordanceTransport::Telegram]
    } else {
        &[
            AffordanceTransport::Web,
            AffordanceTransport::Discord,
            AffordanceTransport::Telegram,
        ]
    };
    for transport in transports.iter().copied() {
        let wire = affordance_id_with_text(&template.turn, template.arg, text, transport);
        let next = parse_affordance_id_with_text(&wire, transport)
            .expect("every frontend decodes the same typed affordance");
        assert_eq!(next.0, template.turn);
        assert_eq!(next.1, template.arg);
        assert_eq!(next.2.as_deref(), text);
        if let Some(previous) = &decoded {
            assert_eq!(previous, &next, "transport changed the player input");
        }
        decoded = Some(next);
    }
    let (turn, arg, text) = decoded.expect("at least two transports were checked");
    let mut action = Action::new(template.label.clone(), turn, arg, template.enabled);
    if let Some(text) = text {
        action = action.with_text(text);
    }
    action
}

fn offered_action(
    offering: &HostedProofAssignedRaidOffering,
    session: &dreggnet_surfaces::private_raid::HostedProofAssignedRaidSession,
    viewer: &DreggIdentity,
    turn: &str,
) -> Action {
    let projection = project_for_audience(offering, session, &Audience::private(viewer.clone()));
    projection
        .actions
        .into_iter()
        .find(|action| action.turn == turn)
        .unwrap_or_else(|| panic!("{turn} must be exposed to {}", viewer.as_str()))
}

fn drive_offered(
    offering: &HostedProofAssignedRaidOffering,
    session: &mut dreggnet_surfaces::private_raid::HostedProofAssignedRaidSession,
    name: &str,
    turn: &str,
) {
    let viewer = actor(name);
    let template = offered_action(offering, session, &viewer, turn);
    let input = round_trip_action_on_every_transport(&template, None);
    assert!(
        offering.advance(session, input, viewer).landed(),
        "{name} must land offered {turn}"
    );
}

fn stream_assignment(
    offering: &HostedProofAssignedRaidOffering,
    session: &mut dreggnet_surfaces::private_raid::HostedProofAssignedRaidSession,
) {
    for chunk in proof_bytes().chunks(MAX_STREAM_CHUNK_BYTES) {
        let template = offered_action(offering, session, &actor("alice"), TURN_STREAM_ASSIGNMENT);
        let input = round_trip_action_on_every_transport(&template, Some(&lower_hex(chunk)));
        let outcome = offering.advance(session, input, actor("alice"));
        assert!(
            outcome.landed(),
            "one chat-native proof chunk lands as a replayed executor turn (proof bytes {}, outcome {outcome:?})",
            proof_bytes().len(),
        );
    }
    assert_eq!(session.streamed_assignment_bytes(), proof_bytes().len());
    let template = offered_action(offering, session, &actor("alice"), TURN_FINALIZE_ASSIGNMENT);
    let wrong_actor = round_trip_action_on_every_transport(&template, None);
    assert!(
        !offering
            .advance(session, wrong_actor, actor("bob"))
            .landed(),
        "only public seat zero may seal a streamed proof"
    );
    assert!(session.assignment().is_none());
    let input = round_trip_action_on_every_transport(&template, None);
    assert!(
        offering.advance(session, input, actor("alice")).landed(),
        "the assembled receipt reaches the same HidingFri verifier"
    );
}

fn muster(
    offering: &HostedProofAssignedRaidOffering,
) -> dreggnet_surfaces::private_raid::HostedProofAssignedRaidSession {
    let mut session = offering
        .open(SessionConfig::with_seed(hero_first_seed()))
        .expect("hosted raid opens");
    for name in ["alice", "bob", "cara", "devi"] {
        drive_offered(offering, &mut session, name, TURN_JOIN_RAID);
    }
    session
}

fn play_assigned_raid(
    offering: &HostedProofAssignedRaidOffering,
    session: &mut dreggnet_surfaces::private_raid::HostedProofAssignedRaidSession,
) {
    for (name, role) in [
        ("alice", Role::Mage),
        ("bob", Role::Tank),
        ("cara", Role::Healer),
        ("devi", Role::Scout),
    ] {
        let template = offered_action(offering, session, &actor(name), TURN_CLAIM);
        assert_eq!(template.arg, role.index() as i64);
        let input = round_trip_action_on_every_transport(&template, None);
        assert!(offering.advance(session, input, actor(name)).landed());
    }
    for name in ["alice", "bob", "cara", "devi"] {
        drive_offered(offering, session, name, TURN_READY);
    }
    drive_offered(offering, session, "alice", TURN_LAUNCH);
    for name in ["alice", "bob", "cara"] {
        drive_offered(offering, session, name, TURN_FORK);
    }
    drive_offered(offering, session, "alice", TURN_RESOLVE_FORK);
    assert_eq!(session.target(), Some(WARDEN));

    let before_prime = offered_action(offering, session, &actor("alice"), TURN_PRIME_TACTIC);
    assert_eq!(before_prime.arg, Role::Mage.index() as i64);
    let shared = offering.actions(session);
    assert!(
        shared.iter().any(|action| action.turn == TURN_PRIME_TACTIC),
        "a Telegram group/shared projection exposes the executor-gated burn"
    );
    assert!(shared.iter().all(|action| action.turn != TURN_ACT));
    assert!(
        project_for_audience(offering, session, &Audience::private(actor("alice")),)
            .actions
            .iter()
            .all(|action| action.turn != TURN_ACT),
        "unprimed act must not be exposed"
    );
    drive_offered(offering, session, "alice", TURN_PRIME_TACTIC);
    assert!(session.tactic_primed_for(actor("alice").as_str()));
    drive_offered(offering, session, "alice", TURN_ACT);
}

fn offering() -> ProofAssignedRaidOffering {
    ProofAssignedRaidOffering::new(roster()).expect("four distinct public raid seats")
}

fn fhir_allocation_artifact(rewarded_seat: usize, reward: f64) -> (Compiled, Vec<u8>) {
    let mut readiness = vec![0.0; 4];
    readiness[rewarded_seat] = reward;
    let compiled = compile(&Product::infer(
        format!("ash-gate-allocation-seat-{rewarded_seat}-reward-{reward}"),
        ProductBody::Portfolio {
            cov: MatrixData::public(
                4,
                4,
                vec![
                    1.0, 0.0, 0.0, 0.0, 0.0, 1.0, 0.0, 0.0, 0.0, 0.0, 1.0, 0.0, 0.0, 0.0, 0.0, 1.0,
                ],
            ),
            mu: readiness,
            lambda: 1.0,
            w_max: 1.0,
        },
    ))
    .expect("the public four-seat allocation is fhIR-admissible");
    let ConvexProgram::Qp(problem) = &compiled.program else {
        panic!("raid allocation policy must compile to QP")
    };
    let mut x = vec![0.0; problem.n];
    x[rewarded_seat] = 1.0;
    let mut y = vec![0.0; problem.mc];
    y[1 + rewarded_seat] = reward - 1.0;
    let wire = build_exact_qp_certificate_bundle(&compiled, x, y)
        .expect("known one-hot optimum has literal exact-zero KKT")
        .to_wire_bytes()
        .expect("exact raid allocation has canonical FHQPB001 wire");
    (compiled, wire)
}

fn fhir_offering(rewarded_seat: usize, reward: f64) -> ProofAssignedRaidOffering {
    let (compiled, wire) = fhir_allocation_artifact(rewarded_seat, reward);
    ProofAssignedRaidOffering::with_fhir_allocation(roster(), compiled, wire)
        .expect("exact optimizer claim binds the authenticated raid roster")
}

#[test]
fn fhir_optimum_selects_a_real_party_member_and_role_with_executor_and_replay_teeth() {
    let offering = fhir_offering(1, 2.0);
    let commitment = offering
        .fhir_allocation_commitment()
        .expect("deployment publishes its full optimizer claim");
    let mut session = offering
        .open(SessionConfig::with_seed(hero_first_seed()))
        .expect("fhIR-allocated raid opens");
    offering
        .invoke_binary_operation(
            &mut session,
            ASSIGN_OPERATION,
            proof_bytes(),
            actor("alice"),
        )
        .expect("private role proof lands");
    assert_eq!(session.fhir_selected_actor(), Some("player:bob"));
    assert_eq!(session.fhir_selected_role(), Some(Role::Tank));
    assert!(!session.fhir_allocation_landed());

    for (name, role) in [
        ("alice", Role::Mage),
        ("bob", Role::Tank),
        ("cara", Role::Healer),
        ("devi", Role::Scout),
    ] {
        assert!(
            offering
                .advance(
                    &mut session,
                    action(TURN_CLAIM, role.index() as i64),
                    actor(name),
                )
                .landed()
        );
    }
    let before = session.turns();

    // Alice is a real Mage party member, but the fhIR winner is Bob. The action
    // reaches Alice's allocation agent; its missing Tank-cell cap makes the
    // executor refuse without changing the acceptance journal.
    let wrong_actor = offering.advance(
        &mut session,
        action(TURN_ACCEPT_FHIR_ALLOCATION, Role::Tank.index() as i64),
        actor("alice"),
    );
    assert!(!wrong_actor.landed());
    assert_eq!(session.turns(), before);
    assert!(!session.fhir_allocation_landed());

    // Bob is the selected actor but asks for Alice's Mage role cell. His agent
    // holds only the Tank allocation cap derived from the private role proof.
    let wrong_role = offering.advance(
        &mut session,
        action(TURN_ACCEPT_FHIR_ALLOCATION, Role::Mage.index() as i64),
        actor("bob"),
    );
    assert!(!wrong_role.landed());
    assert_eq!(session.turns(), before);

    assert!(
        offering
            .advance(
                &mut session,
                action(TURN_ACCEPT_FHIR_ALLOCATION, Role::Tank.index() as i64),
                actor("bob"),
            )
            .landed(),
        "the exact QP winner lands as Bob's real Tank role"
    );
    assert!(session.fhir_allocation_landed());
    let after = session.turns();
    let duplicate = offering.advance(
        &mut session,
        action(TURN_ACCEPT_FHIR_ALLOCATION, Role::Tank.index() as i64),
        actor("bob"),
    );
    assert!(!duplicate.landed(), "the allocation cell is WriteOnce");
    assert_eq!(session.turns(), after);
    let report = offering.verify(&session);
    assert!(
        report.verified,
        "fhIR + role + executor replay: {}",
        report.detail
    );

    // Same winner, different exact objective: both optimizer artifacts are
    // independently valid, but the alternate deployment cannot replay/verify
    // the live session's roster/objective-bound claim.
    let alternate_objective = fhir_offering(1, 3.0);
    assert_ne!(
        alternate_objective.fhir_allocation_commitment(),
        Some(commitment)
    );
    let objective_replay = alternate_objective.verify(&session);
    assert!(!objective_replay.verified);
    assert!(objective_replay.detail.contains("allocation differs"));
    let (alternate_compiled, alternate_wire) = fhir_allocation_artifact(1, 3.0);
    assert!(matches!(
        ProofAssignedRaidOffering::with_precommitted_fhir_allocation(
            roster(),
            alternate_compiled,
            alternate_wire,
            commitment,
        ),
        Err(reason) if reason.contains("roster/objective claim")
    ));

    // A deployment precommitment made for this roster is not reusable after an
    // ordered actor substitution, even though the QP and one-hot coordinate are
    // unchanged.
    let mut reordered = roster();
    reordered.swap(1, 2);
    let (compiled, wire) = fhir_allocation_artifact(1, 2.0);
    let roster_refusal = ProofAssignedRaidOffering::with_precommitted_fhir_allocation(
        reordered, compiled, wire, commitment,
    );
    assert!(matches!(
        roster_refusal,
        Err(reason) if reason.contains("roster/objective claim")
    ));

    let rendered = format!("{:?}", offering.render(&session).view());
    assert!(rendered.contains("FHQPB001 EXACT OPTIMUM VERIFIED"));
    assert!(rendered.contains("executor allocation landed"));
}

#[test]
fn fhir_member_role_allocation_survives_host_operation_and_move_replay() {
    let store = InMemoryResumeStore::new();
    let id = SessionId::new("fhir-private-raid-restart");
    let offering = fhir_offering(1, 2.0);
    {
        let mut live = OfferingHost::new().with_resume_store(Box::new(store.clone()));
        live.register(KEY, "fhIR allocated Ash Gate", offering.clone());
        live.open_session(KEY, id.clone(), SessionConfig::with_seed(hero_first_seed()))
            .unwrap();
        live.invoke_binary_operation(KEY, &id, ASSIGN_OPERATION, proof_bytes(), actor("alice"))
            .expect("private role proof is retained for replay");
        for (name, role) in [("alice", Role::Mage), ("bob", Role::Tank)] {
            assert!(
                live.advance(
                    KEY,
                    &id,
                    action(TURN_CLAIM, role.index() as i64),
                    actor(name),
                )
                .unwrap()
                .landed()
            );
        }
        assert!(
            live.advance(
                KEY,
                &id,
                action(TURN_ACCEPT_FHIR_ALLOCATION, Role::Tank.index() as i64),
                actor("bob"),
            )
            .unwrap()
            .landed()
        );
        assert!(live.verify(KEY, &id).unwrap().verified);
    }

    let mut rebooted = OfferingHost::new().with_resume_store(Box::new(store));
    rebooted.register(KEY, "fhIR allocated Ash Gate", offering);
    let resumed = rebooted.resume_all();
    assert_eq!(resumed.len(), 1);
    assert!(
        resumed[0].1.is_ok(),
        "QP verification, private role proof, claims, and executor allocation replay: {resumed:?}"
    );
    let report = rebooted.verify(KEY, &id).unwrap();
    assert!(report.verified, "{}", report.detail);
}

#[test]
fn hiding_assignment_authorizes_exact_capability_claims_and_a_real_arena_turn() {
    let offering = offering();
    let mut session = offering
        .open(SessionConfig::with_seed(hero_first_seed()))
        .expect("raid opens");
    assert_eq!(
        offering.actions_for(&session, &actor("alice"))[0].turn,
        TURN_STREAM_ASSIGNMENT
    );
    assert!(offering.actions_for(&session, &actor("bob")).is_empty());
    assert!(offering.verify(&session).verified);

    // No ordinary lobby progress exists before the proof operation.
    let before_proof = offering.advance(
        &mut session,
        action(TURN_CLAIM, Role::Mage.index() as i64),
        actor("alice"),
    );
    assert!(!before_proof.landed());
    assert_eq!(session.turns(), 0);

    // The exact public roster is actor-bound at the operation boundary.
    let wrong_submitter = offering.invoke_binary_operation(
        &mut session,
        ASSIGN_OPERATION,
        proof_bytes(),
        actor("bob"),
    );
    assert!(matches!(
        wrong_submitter,
        Err(BinaryOperationError::Refused(_))
    ));
    assert!(session.assignment().is_none());

    // A canonical receipt with a substituted public session is refused before proof/state use.
    let mut wrong_wire = RaidAssignmentWireReceipt::from_postcard(proof_bytes()).unwrap();
    let expected = proof_session_for_seed(hero_first_seed());
    wrong_wire.public_inputs[0] = if expected == 2_013_265_920 {
        1
    } else {
        expected + 1
    };
    let wrong_session = wrong_wire.to_postcard().unwrap();
    assert!(matches!(
        offering.invoke_binary_operation(
            &mut session,
            ASSIGN_OPERATION,
            &wrong_session,
            actor("alice"),
        ),
        Err(BinaryOperationError::Refused(reason)) if reason.contains("session mismatch")
    ));
    assert!(session.assignment().is_none());

    // HOSTILE: keep the real proof bytes and session/root but substitute two published role
    // assignments. The HidingFri verifier refuses; no party claim or assignment slot appears.
    let mut substituted_wire = RaidAssignmentWireReceipt::from_postcard(proof_bytes()).unwrap();
    substituted_wire.public_inputs.swap(10, 11);
    let substituted_assignment = substituted_wire.to_postcard().unwrap();
    assert!(matches!(
        offering.invoke_binary_operation(
            &mut session,
            ASSIGN_OPERATION,
            &substituted_assignment,
            actor("alice"),
        ),
        Err(BinaryOperationError::Refused(_))
    ));
    assert!(session.assignment().is_none());
    assert_eq!(session.turns(), 0);

    let operation = offering
        .invoke_binary_operation(
            &mut session,
            ASSIGN_OPERATION,
            proof_bytes(),
            actor("alice"),
        )
        .expect("seat zero binds the verified assignment to the raid");
    assert_ne!(operation.receipt_id, [0u8; 32]);
    assert_eq!(
        session.assignment().unwrap().roles(),
        [
            RaidRole::Striker,
            RaidRole::Bulwark,
            RaidRole::Mender,
            RaidRole::Pathfinder,
        ]
    );
    let replayed_operation = offering.invoke_binary_operation(
        &mut session,
        ASSIGN_OPERATION,
        proof_bytes(),
        actor("alice"),
    );
    assert!(matches!(
        replayed_operation,
        Err(BinaryOperationError::Refused(reason)) if reason.contains("already filled")
    ));
    assert_eq!(session.turns(), 0);

    // HOSTILE: Alice's public seat was assigned Striker→Mage. Claiming Tank or claiming
    // before the designated leader is an assignment substitution, refused before lobby progress.
    let substituted = offering.advance(
        &mut session,
        action(TURN_CLAIM, Role::Tank.index() as i64),
        actor("alice"),
    );
    assert!(!substituted.landed());
    assert_eq!(session.turns(), 0);
    let premature = offering.advance(
        &mut session,
        action(TURN_CLAIM, Role::Tank.index() as i64),
        actor("bob"),
    );
    assert!(!premature.landed());
    assert_eq!(session.turns(), 0);

    for (name, role) in [
        ("alice", Role::Mage),
        ("bob", Role::Tank),
        ("cara", Role::Healer),
        ("devi", Role::Scout),
    ] {
        assert!(
            offering
                .advance(
                    &mut session,
                    action(TURN_CLAIM, role.index() as i64),
                    actor(name),
                )
                .landed(),
            "{name} claims only the capability assigned to its proof seat"
        );
        assert_eq!(session.role_of(&format!("player:{name}")), Some(role));
    }
    for name in ["alice", "bob", "cara", "devi"] {
        assert!(
            offering
                .advance(&mut session, action(TURN_READY, 0), actor(name))
                .landed()
        );
    }
    assert!(
        offering
            .advance(&mut session, action(TURN_LAUNCH, 0), actor("alice"))
            .landed()
    );
    assert!(session.launched());

    for name in ["alice", "bob", "cara"] {
        assert!(
            offering
                .advance(&mut session, action(TURN_FORK, 0), actor(name))
                .landed()
        );
    }
    assert!(
        offering
            .advance(&mut session, action(TURN_RESOLVE_FORK, 0), actor("alice"),)
            .landed()
    );
    assert_eq!(session.target(), Some(WARDEN));

    // HOSTILE: after launch, this is deliberately sent through the real party executor.
    // Alice holds Mage, while TURN_MISPLAY asks for Tank; missing capability refuses before Arena.
    let before_misplay = session.turns();
    let misplay = offering.advance(&mut session, action(TURN_MISPLAY, 0), actor("alice"));
    assert!(!misplay.landed());
    assert_eq!(session.turns(), before_misplay);

    // The role assignment is now a spendable mechanic, not only a receipt panel.
    // Until Alice burns the proof-minted Mage sigil, even her otherwise-valid role
    // contribution is refused before either party or Arena advances.
    let unprimed = offering.advance(&mut session, action(TURN_ACT, 0), actor("alice"));
    assert!(!unprimed.landed());
    assert_eq!(session.turns(), before_misplay);

    // Bob is seated and legitimately holds Tank, but asks the sigil world for Alice's
    // Mage target. There is deliberately no host equality check: Bob's proof-derived
    // agent lacks that capability, so the real executor refuses and no sigil is spent.
    let wrong_sigil = offering.advance(
        &mut session,
        action(TURN_PRIME_TACTIC, Role::Mage.index() as i64),
        actor("bob"),
    );
    assert!(!wrong_sigil.landed());
    assert!(!session.tactic_primed_for("player:bob"));
    assert!(!session.tactic_primed_for("player:alice"));
    assert_eq!(session.turns(), before_misplay);

    assert!(
        offering
            .advance(
                &mut session,
                action(TURN_PRIME_TACTIC, Role::Mage.index() as i64),
                actor("alice"),
            )
            .landed(),
        "Alice burns the exact sigil her proof seat owns"
    );
    assert!(session.tactic_primed_for("player:alice"));
    let after_prime = session.turns();
    assert_eq!(after_prime, before_misplay + 1);

    // A repeated burn reaches the sigil's FieldDelta(+1)/WriteOnce program.
    let double_burn = offering.advance(
        &mut session,
        action(TURN_PRIME_TACTIC, Role::Mage.index() as i64),
        actor("alice"),
    );
    assert!(!double_burn.landed());
    assert_eq!(session.turns(), after_prime);

    assert!(
        offering
            .advance(&mut session, action(TURN_ACT, 0), actor("alice"))
            .landed(),
        "the proof-assigned Mage capability authorizes a real tactical heavy turn"
    );
    let report = offering.verify(&session);
    assert!(
        report.verified,
        "proof + party + Arena replay: {}",
        report.detail
    );
    let rendered = format!(
        "{:?}",
        offering.render_for(&session, &actor("alice")).view()
    );
    assert!(rendered.contains("HIDING PROOF VERIFIED"));
    assert!(rendered.contains("Tactical Arena"));
    assert!(rendered.contains("not an ObservedFieldEquals"));
}

fn host(store: &InMemoryResumeStore, roster: [String; 4]) -> OfferingHost {
    let mut host = OfferingHost::new().with_resume_store(Box::new(store.clone()));
    host.register(
        KEY,
        "The Ash Gate Raid — shielded assignment + capability tactics",
        ProofAssignedRaidOffering::new(roster).unwrap(),
    );
    host
}

#[test]
fn operation_and_moves_restart_exactly_while_roster_order_substitution_fails_closed() {
    let store = InMemoryResumeStore::new();
    let id = SessionId::new("proof-assigned-raid-restart");
    {
        let mut live = host(&store, roster());
        live.open_session(KEY, id.clone(), SessionConfig::with_seed(hero_first_seed()))
            .unwrap();
        live.invoke_binary_operation(KEY, &id, ASSIGN_OPERATION, proof_bytes(), actor("alice"))
            .expect("durable proof operation lands");
        for (name, role) in [("alice", Role::Mage), ("bob", Role::Tank)] {
            let outcome = live
                .advance(
                    KEY,
                    &id,
                    action(TURN_CLAIM, role.index() as i64),
                    actor(name),
                )
                .unwrap();
            assert!(outcome.landed());
        }
        assert!(
            live.advance(
                KEY,
                &id,
                action(TURN_PRIME_TACTIC, Role::Mage.index() as i64),
                actor("alice"),
            )
            .unwrap()
            .landed()
        );
        assert!(live.verify(KEY, &id).unwrap().verified);
        let log = live.move_log(KEY, &id).unwrap();
        assert_eq!(log.operations.len(), 1);
        assert_eq!(log.moves.len(), 3);
    }

    let mut rebooted = host(&store, roster());
    let resumed = rebooted.resume_all();
    assert_eq!(resumed.len(), 1);
    assert!(
        resumed[0].1.is_ok(),
        "honest operation/action replay: {resumed:?}"
    );
    assert!(rebooted.verify(KEY, &id).unwrap().verified);

    // Same proof bytes plus a reordered identity interpretation is not interchangeable.
    // The journaled operation actor is no longer public seat zero, so restoration refuses
    // before any claim is replayed and no forged live session remains.
    let mut substituted = roster();
    substituted.swap(0, 1);
    let mut wrong_host = host(&store, substituted);
    let wrong = wrong_host.resume_all();
    assert_eq!(wrong.len(), 1);
    assert!(matches!(
        &wrong[0].1,
        Err(dreggnet_offerings::ResumeError::OperationRefused { reason, .. })
            if reason.contains("only public seat 0")
    ));
    assert!(!wrong_host.is_open(KEY, &id));
}

fn hosted_raid(store: &InMemoryResumeStore) -> OfferingHost {
    let mut host = OfferingHost::new().with_resume_store(Box::new(store.clone()));
    host.register(
        KEY,
        "The Ash Gate Raid — public muster + shielded assignment + capability tactics",
        HostedProofAssignedRaidOffering::new(),
    );
    host
}

#[test]
fn catalog_lobby_forms_the_exact_roster_then_restarts_through_proof_and_capability_claim() {
    let offering = HostedProofAssignedRaidOffering::new();
    let mut session = offering
        .open(SessionConfig::with_seed(hero_first_seed()))
        .expect("hosted raid opens without a pre-known roster");
    assert!(
        offering.verify(&session).verified,
        "empty audit cell is canonical"
    );

    for (seat, name) in ["alice", "bob", "cara", "devi"].into_iter().enumerate() {
        assert_eq!(
            offering.actions_for(&session, &actor(name))[0].turn,
            TURN_JOIN_RAID
        );
        assert!(
            offering
                .advance(&mut session, action(TURN_JOIN_RAID, 0), actor(name))
                .landed()
        );
        assert_eq!(session.roster().len(), seat + 1);
        let duplicate = offering.advance(&mut session, action(TURN_JOIN_RAID, 0), actor(name));
        assert!(!duplicate.landed(), "one identity cannot occupy two seats");
        assert!(
            offering.actions_for(&session, &actor(name)).is_empty(),
            "an occupied identity is not offered a second public seat"
        );
        assert!(offering.verify(&session).verified);
    }
    assert_eq!(session.roster(), roster());
    assert_eq!(offering.binary_operations(&session).len(), 1);
    assert!(matches!(
        offering.invoke_binary_operation(
            &mut session,
            ASSIGN_OPERATION,
            proof_bytes(),
            actor("bob")
        ),
        Err(BinaryOperationError::Refused(_))
    ));
    offering
        .invoke_binary_operation(
            &mut session,
            ASSIGN_OPERATION,
            proof_bytes(),
            actor("alice"),
        )
        .expect("public seat zero binds the shielded optimizer receipt");
    assert_eq!(
        session.assignment().unwrap().roles(),
        [
            RaidRole::Striker,
            RaidRole::Bulwark,
            RaidRole::Mender,
            RaidRole::Pathfinder,
        ]
    );
    assert!(
        offering
            .advance(
                &mut session,
                action(TURN_CLAIM, Role::Mage.index() as i64),
                actor("alice")
            )
            .landed()
    );
    assert_eq!(session.role_of(actor("alice").as_str()), Some(Role::Mage));
    assert!(
        offering
            .advance(
                &mut session,
                action(TURN_PRIME_TACTIC, Role::Mage.index() as i64),
                actor("alice")
            )
            .landed()
    );
    assert!(session.tactic_primed_for(actor("alice").as_str()));
    let report = offering.verify(&session);
    assert!(report.verified, "{}", report.detail);
    assert_eq!(
        report.turns, 6,
        "four roster joins plus one party claim and one sigil burn"
    );

    let store = InMemoryResumeStore::new();
    let id = SessionId::new("catalog-private-raid-restart");
    let before = {
        let mut host = hosted_raid(&store);
        host.open_session(KEY, id.clone(), SessionConfig::with_seed(hero_first_seed()))
            .unwrap();
        for name in ["alice", "bob", "cara", "devi"] {
            assert!(
                host.advance(KEY, &id, action(TURN_JOIN_RAID, 0), actor(name))
                    .unwrap()
                    .landed()
            );
        }
        host.invoke_binary_operation(KEY, &id, ASSIGN_OPERATION, proof_bytes(), actor("alice"))
            .expect("proof operation is journaled after the fourth roster move");
        assert!(
            host.advance(
                KEY,
                &id,
                action(TURN_CLAIM, Role::Mage.index() as i64),
                actor("alice"),
            )
            .unwrap()
            .landed()
        );
        assert!(
            host.advance(
                KEY,
                &id,
                action(TURN_PRIME_TACTIC, Role::Mage.index() as i64),
                actor("alice"),
            )
            .unwrap()
            .landed()
        );
        assert!(host.verify(KEY, &id).unwrap().verified);
        host.commitment(KEY, &id).expect("hosted raid commitment")
    };

    let mut rebooted = hosted_raid(&store);
    let resumed = rebooted.resume_all();
    assert_eq!(resumed.len(), 1);
    assert!(
        resumed[0].1.is_ok(),
        "lobby + operation + action replay: {resumed:?}"
    );
    assert_eq!(rebooted.commitment(KEY, &id), Some(before));
    assert!(rebooted.verify(KEY, &id).unwrap().verified);
}

#[test]
fn web_binary_and_chat_streaming_reach_one_join_proof_claim_burn_act_game() {
    let offering = HostedProofAssignedRaidOffering::new();

    let mut chat = muster(&offering);
    let template = offered_action(&offering, &chat, &actor("alice"), TURN_STREAM_ASSIGNMENT);
    let stale = Action::new(
        template.label.clone(),
        template.turn.clone(),
        template.arg + 1,
        true,
    )
    .with_text("00");
    assert!(!offering.advance(&mut chat, stale, actor("alice")).landed());
    let uppercase = template.with_text("AA");
    assert!(
        !offering
            .advance(&mut chat, uppercase, actor("alice"))
            .landed()
    );
    assert_eq!(chat.streamed_assignment_bytes(), 0);
    stream_assignment(&offering, &mut chat);
    assert!(chat.assignment().is_some());

    let mut web = muster(&offering);
    let descriptor = offering.binary_operations(&web);
    assert_eq!(descriptor.len(), 1);
    assert_eq!(descriptor[0].name, ASSIGN_OPERATION);
    offering
        .invoke_binary_operation(&mut web, ASSIGN_OPERATION, proof_bytes(), actor("alice"))
        .expect("web's owning-file upload reaches the verifier");
    assert_eq!(chat.assignment(), web.assignment());

    play_assigned_raid(&offering, &mut chat);
    play_assigned_raid(&offering, &mut web);
    assert!(chat.launched() && web.launched());
    assert_eq!(chat.target(), web.target());
    assert_eq!(
        chat.role_of(actor("alice").as_str()),
        web.role_of(actor("alice").as_str())
    );
    let chat_report = offering.verify(&chat);
    assert!(
        chat_report.verified,
        "chat-native raid replay failed: {}",
        chat_report.detail
    );
    let web_report = offering.verify(&web);
    assert!(
        web_report.verified,
        "owning-file raid replay failed: {}",
        web_report.detail
    );
}

#[test]
fn chat_proof_stream_refuses_oversize_chunks_and_has_a_finite_turn_budget() {
    let offering = offering();
    let mut session = offering
        .open(SessionConfig::with_seed(hero_first_seed()))
        .expect("fixed raid opens");

    let oversized = Action::new("oversized proof chunk", TURN_STREAM_ASSIGNMENT, 0, true)
        .with_text(lower_hex(&vec![0u8; MAX_STREAM_CHUNK_BYTES + 1]));
    assert!(
        !offering
            .advance(&mut session, oversized, actor("alice"))
            .landed()
    );
    assert_eq!(session.streamed_assignment_bytes(), 0);
    assert_eq!(session.streamed_assignment_chunks(), 0);

    for index in 0..MAX_STREAM_CHUNKS {
        let chunk = Action::new(
            "bounded proof chunk",
            TURN_STREAM_ASSIGNMENT,
            index as i64,
            true,
        )
        .with_text("00");
        assert!(
            offering
                .advance(&mut session, chunk, actor("alice"))
                .landed()
        );
    }
    assert_eq!(session.streamed_assignment_chunks(), MAX_STREAM_CHUNKS);
    assert!(
        offering
            .actions_for(&session, &actor("alice"))
            .iter()
            .all(|action| action.turn != TURN_STREAM_ASSIGNMENT),
        "the UI must stop soliciting chunks at the bounded turn ceiling"
    );
    let beyond_budget = Action::new(
        "one chunk too many",
        TURN_STREAM_ASSIGNMENT,
        MAX_STREAM_CHUNKS as i64,
        true,
    )
    .with_text("00");
    assert!(
        !offering
            .advance(&mut session, beyond_budget, actor("alice"))
            .landed()
    );
    assert_eq!(session.streamed_assignment_chunks(), MAX_STREAM_CHUNKS);
}

#[test]
fn live_adapter_sources_keep_the_text_and_binary_routes_the_flow_requires() {
    let discord = include_str!("../../discord-bot/src/commands/offering.rs");
    let telegram = include_str!("../../dreggnet-telegram/src/host.rs");
    let web = include_str!("../../dreggnet-web/src/lib.rs");
    let web_operation = include_str!("../../dreggnet-web/src/fhegg_operation.rs");

    assert!(discord.contains("dreggnet_surfaces::HostedProofAssignedRaidOffering"));
    assert!(discord.contains("Action::new(turn.clone(), turn, arg, true).with_text(text)"));
    assert!(telegram.contains(".find(|a| a.turn == turn && a.arg == arg && a.wants_text"));
    assert!(telegram.contains("let action = pending.with_text(text.to_string())"));
    assert!(web.contains("h.binary_operations(&k, &id)"));
    assert!(web.contains("render_operation_uploaders(&operations"));
    assert!(web_operation.contains("host.invoke_binary_operation("));
}
