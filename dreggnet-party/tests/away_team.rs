//! THE AWAY MISSION, driven end to end.
//!
//! A crew forms in a real lobby; four hidden preference rows are committed; the real
//! Lean-emitted HidingFri relation assigns the roles nobody revealed; the verified
//! assignment is bound to THIS crew inside the proof's own public statement; the crew
//! departs into the real cap-seated party world; an out-of-role move is refused BY NAME by
//! the executor; a sub-quorum steer moves nothing; a quorum steer lands exactly ONE real
//! turn; and the loot splits on the ledger, per member.
//!
//! Two hiding proofs are produced by this whole file — every other refusal here is checked
//! before any proof work — so the suite stays affordable.
#![cfg(feature = "private-role-assignment")]

use dreggnet_party::crew::{
    CREW_SEATS, CrewActError, CrewCharter, CrewError, CrewRoll, HiddenPreference, SteerError,
};
use dreggnet_party::lobby::PartyLobby;
use dreggnet_party::{GATE_SLOT, PartyMove, ROLE_SLOT, Role};

/// The crew, in the order players walked into the lobby (NOT charter seat order).
const ADA: &str = "player:ada";
const BO: &str = "player:bo";
const CYD: &str = "player:cyd";
const DREE: &str = "player:dree";

/// Every member's PRIVATE row, in charter seat order (identities sort ascending:
/// ada, bo, cyd, dree). Scores/willingness are indexed by [`Role::ALL`] —
/// `[Tank, Scout, Mage, Healer]`.
///
/// The rows are chosen so the globally-optimal admissible assignment is the exact
/// OPPOSITE of what each player claimed in the lobby: nobody gets the seat they clicked,
/// everybody gets the seat their hidden suitability earned. `cyd` additionally refuses to
/// tank at all, so admissibility is doing real work.
fn hidden_rows() -> [HiddenPreference; CREW_SEATS] {
    [
        // ada — a caster who cannot hold a line.
        HiddenPreference::new([0, 1, 3, 2], [true, true, true, true], [0x11; 32]).unwrap(),
        // bo — a wall.
        HiddenPreference::new([3, 0, 1, 0], [true, true, true, true], [0x22; 32]).unwrap(),
        // cyd — a mender who WILL NOT tank.
        HiddenPreference::new([0, 0, 0, 3], [false, true, true, true], [0x33; 32]).unwrap(),
        // dree — a pathfinder.
        HiddenPreference::new([1, 3, 0, 0], [true, true, true, true], [0x44; 32]).unwrap(),
    ]
}

/// The crew forms in a real lobby, claiming roles that will turn out to be wrong.
fn formed_lobby() -> PartyLobby {
    let mut lobby = PartyLobby::new("away-mission:the-drowned-marches", ADA).expect("a lobby");
    // Deliberately the WRONG seats — the lobby claim is only a seating protocol.
    lobby.claim(ADA, Role::Healer).expect("ada sits");
    lobby.claim(BO, Role::Mage).expect("bo sits");
    lobby.claim(CYD, Role::Scout).expect("cyd sits");
    lobby.claim(DREE, Role::Tank).expect("dree sits");
    lobby
}

/// **THE AWAY MISSION.** One walk from "who is here" to "what everyone got paid", with the
/// real executor and the real quorum engine refereeing every step.
#[test]
fn a_crew_forms_takes_proof_assigned_roles_steers_by_quorum_and_splits_the_loot() {
    // ── 1. A CREW FORMS. Four authenticated identities, one canonical seat order.
    let lobby = formed_lobby();
    let charter = CrewCharter::from_lobby(&lobby).expect("a full lobby forms a crew");
    assert_eq!(
        charter.members(),
        &[
            ADA.to_string(),
            BO.to_string(),
            CYD.to_string(),
            DREE.to_string()
        ],
        "the charter is canonical, not click-ordered"
    );

    // ── 2. ROLES ASSIGN FROM HIDDEN PREFERENCES. Each member publishes only a commitment.
    let rows = hidden_rows();
    let roll = CrewRoll::from_preferences(charter.clone(), &rows);
    let expected_session = roll.proof_session();
    let assignment = roll
        .assign_roles(&rows)
        .expect("the hidden preferences admit an optimal assignment");

    // The result is the globally suitability-maximal admissible permutation — and it is
    // the exact opposite of what everyone claimed in the lobby.
    assert_eq!(
        assignment.roles(),
        [Role::Mage, Role::Tank, Role::Healer, Role::Scout],
        "the proof, not the click, decided the roles"
    );
    for (identity, claimed) in [
        (ADA, Role::Healer),
        (BO, Role::Mage),
        (CYD, Role::Scout),
        (DREE, Role::Tank),
    ] {
        assert_ne!(
            assignment.role_of(identity),
            Some(claimed),
            "{identity} did not simply receive the seat they clicked"
        );
    }
    // It is a permutation: every role is held by exactly one member.
    let mut held: Vec<Role> = Role::ALL.to_vec();
    held.sort();
    let mut got: Vec<Role> = assignment.roles().to_vec();
    got.sort();
    assert_eq!(got, held, "a permutation of the four roles");

    // ── 3. THE BINDING. The proof's own public statement carries this crew's session.
    assert_eq!(
        assignment.session(),
        expected_session,
        "the verified statement is bound to THIS crew's charter + commitments"
    );

    // ── 4. THE CREW DEPARTS into the real cap-seated party world.
    let mut team = assignment.depart().expect("the crew is seated");
    let layout = team.party().layout();
    for identity in charter.members() {
        assert!(
            team.party().seat_index_for(identity).is_some(),
            "{identity} holds a real player-cell"
        );
        assert_eq!(
            team.role_of(identity),
            assignment.role_of(identity),
            "the seated role is the proof-assigned role"
        );
    }

    // ── 5. YOUR JOB IS YOURS. ada drew MAGE; firing bo's TANK move reaches the executor
    //      and is refused for want of the capability — named, not host-guessed.
    let refusal = team
        .act(ADA, PartyMove::GuardFront)
        .expect_err("ada cannot play bo's seat");
    let CrewActError::OutOfRole(out) = refusal else {
        panic!("an out-of-role move must be an OutOfRole refusal, got {refusal:?}");
    };
    assert_eq!(out.identity, ADA);
    assert_eq!(out.assigned, Role::Mage);
    assert_eq!(out.attempted, PartyMove::GuardFront);
    assert_eq!(out.sanctioned, Role::Tank);
    assert_eq!(out.sanctioned_holder, BO, "the job belonged to bo");
    assert!(
        out.executor_reason.to_lowercase().contains("cap"),
        "the refusal is the executor's own capability refusal, got: {}",
        out.executor_reason
    );
    let rendered = out.to_string();
    for fragment in [ADA, BO, "Mage", "Tank"] {
        assert!(
            rendered.contains(fragment),
            "the refusal names {fragment}: {rendered}"
        );
    }
    assert_eq!(
        team.party().read_field(layout.front, ROLE_SLOT),
        0,
        "anti-ghost: the forged move touched the front rank not at all"
    );

    // Non-vacuous: the SAME move by the member the PROOF gave that job commits.
    let receipt = team
        .act(BO, PartyMove::GuardFront)
        .expect("bo's own proof-assigned move commits");
    assert_ne!(receipt, [0u8; 32], "a genuine receipted turn");
    assert_ne!(team.party().read_field(layout.front, ROLE_SLOT), 0);

    // An outsider is not on the crew at all.
    assert!(matches!(
        team.act("player:mallory", PartyMove::Rally),
        Err(CrewActError::NotOnTheCrew(_))
    ));

    // ── 6. A SUB-QUORUM STEER MOVES NOTHING.
    team.open_steer(
        "The marches fork — where does the away team go?",
        vec![
            ("Down the sunken stair".into(), 1),
            ("Along the weir".into(), 2),
        ],
    )
    .expect("the steer opens");
    team.steer_vote(ADA, 0).expect("ada votes");
    team.steer_vote(BO, 0).expect("bo votes");
    let receipts_before = team.party().world().receipts().len();
    let root_before = team.party().world().state_root();
    assert!(
        matches!(team.steer(), Err(SteerError::BelowQuorum)),
        "two of four is below the quorum of three"
    );
    assert_eq!(
        team.party().read_field(layout.gate, GATE_SLOT),
        0,
        "anti-ghost: the gate did not move below quorum"
    );
    assert_eq!(team.party().world().state_root(), root_before);
    assert_eq!(
        team.party().world().receipts().len(),
        receipts_before,
        "a sub-quorum steer appends no committed receipt"
    );

    // A member cannot vote twice, and an outsider holds no ballot.
    assert!(team.steer_vote(ADA, 1).is_err(), "one member, one ballot");
    assert!(team.steer_vote("player:mallory", 0).is_err());

    // ── 7. A QUORUM STEER LANDS EXACTLY ONE REAL TURN.
    team.steer_vote(CYD, 0).expect("cyd votes");
    let resolution = team.steer().expect("the quorum-certified steer fires");
    assert_eq!(resolution.winner, 0);
    assert_eq!(resolution.path, 1);
    assert_eq!(resolution.winner_tally, 3);
    assert_ne!(resolution.receipt, [0u8; 32]);
    assert_eq!(
        team.party().read_field(layout.gate, GATE_SLOT),
        1,
        "the shared world reflects the quorum-certified path"
    );
    assert_eq!(
        team.party().world().receipts().len(),
        receipts_before + 1,
        "the certified steer committed exactly ONE turn"
    );

    // ── 8. THE LOOT SPLITS ON THE LEDGER, per MEMBER (charter order), not per role.
    let shares = [40u64, 30, 20, 10];
    assert!(
        team.split_loot(shares).committed(),
        "the away team's split commits"
    );
    for (seat, identity) in charter.members().iter().enumerate() {
        assert_eq!(
            team.loot_share(identity),
            Some(shares[seat]),
            "{identity}'s share is a committed ledger fact"
        );
    }
    assert!(
        team.split_loot([10, 10, 10, 10]).refused(),
        "a re-split of the frozen loot is refused (WriteOnce)"
    );
    assert_eq!(team.loot_share(ADA), Some(40), "the original split stands");

    // ── 9. THE NEXT MISSION. The braid is reachable from live play, and a fresh mission
    //      needs a fresh assignment: the same crew under a new charter derives a new
    //      session, so this receipt cannot be replayed into the next descent.
    let deeper =
        CrewCharter::from_party("away-mission:deeper", team.party()).expect("a fresh charter");
    assert_eq!(deeper.members(), charter.members());
    assert_ne!(
        CrewRoll::from_preferences(deeper, &rows).proof_session(),
        assignment.session(),
        "a new mission needs a new assignment, not a replayed one"
    );
}

/// **THE SEAM THAT WAS MISSING.** A private-raid statement names seats `0..3` and no
/// identities. Reusing this crew's receipt against ANOTHER crew is refused by the session
/// the statement itself carries — no host bookkeeping in the loop.
#[test]
fn a_role_assignment_minted_for_one_crew_is_refused_by_another_crew() {
    let charter = CrewCharter::from_lobby(&formed_lobby()).expect("a crew");
    let rows = hidden_rows();
    let roll = CrewRoll::from_preferences(charter.clone(), &rows);
    let receipt = roll.prove_roles(&rows).expect("a real hiding receipt");

    // Its own crew lands it.
    let landed = roll.accept(&receipt).expect("the crew it was minted for");
    assert_eq!(landed.session(), roll.proof_session());

    // Another crew — same commitments, one member swapped for an impostor — refuses it.
    let impostor_crew = CrewCharter::form(
        charter.mission(),
        [
            ADA.to_string(),
            BO.to_string(),
            CYD.to_string(),
            "player:mallory".to_string(),
        ],
    )
    .expect("a well-formed but different crew");
    let impostor_roll = CrewRoll::new(impostor_crew, *roll.commitments());
    match impostor_roll.accept(&receipt) {
        Err(CrewError::SessionNotThisCrew { expected, claimed }) => {
            assert_eq!(expected, impostor_roll.proof_session());
            assert_eq!(claimed, roll.proof_session());
            assert_ne!(expected, claimed);
        }
        other => panic!("another crew must not be able to land this receipt, got {other:?}"),
    }

    // The same crew on a DIFFERENT mission is also a different session.
    let other_mission =
        CrewCharter::form("away-mission:the-weir", charter.members().clone()).expect("a charter");
    assert!(matches!(
        CrewRoll::new(other_mission, *roll.commitments()).accept(&receipt),
        Err(CrewError::SessionNotThisCrew { .. })
    ));

    // And a crew that re-blinds one member's row derives a different session too.
    let mut rerolled = hidden_rows();
    rerolled[2] = HiddenPreference::new([0, 0, 0, 3], [false, true, true, true], [0x99; 32])
        .expect("a valid row");
    assert!(matches!(
        CrewRoll::from_preferences(charter, &rerolled).accept(&receipt),
        Err(CrewError::SessionNotThisCrew { .. })
    ));
}

/// A producer cannot quietly substitute a member's row: the roll's published commitment
/// binds it, and the swap is refused before any proof work.
#[test]
fn a_substituted_preference_row_is_refused_against_the_published_commitment() {
    let charter = CrewCharter::from_lobby(&formed_lobby()).expect("a crew");
    let rows = hidden_rows();
    let roll = CrewRoll::from_preferences(charter, &rows);

    let mut tampered = hidden_rows();
    // Rewrite cyd's row so the producer's preferred assignment wins instead.
    tampered[2] = HiddenPreference::new([3, 0, 0, 0], [true; 4], [0x33; 32]).expect("a valid row");
    match roll.prove_roles(&tampered) {
        Err(CrewError::PreferenceNotCommitted { seat, identity }) => {
            assert_eq!(seat, 2);
            assert_eq!(identity, CYD);
        }
        other => panic!("a substituted row must be refused, got {other:?}"),
    }
}

/// Admissibility is real: a crew where nobody will mend has no assignment, and says so
/// before any proof work.
#[test]
fn a_crew_with_no_admissible_assignment_is_refused_by_name() {
    let charter = CrewCharter::from_lobby(&formed_lobby()).expect("a crew");
    let rows: [HiddenPreference; CREW_SEATS] = std::array::from_fn(|seat| {
        HiddenPreference::new(
            [3, 2, 1, 0],
            [true, true, true, false],
            [seat as u8 + 1; 32],
        )
        .expect("a valid row")
    });
    let roll = CrewRoll::from_preferences(charter, &rows);
    assert!(matches!(
        roll.prove_roles(&rows),
        Err(CrewError::NoAdmissibleAssignment(_))
    ));
}
