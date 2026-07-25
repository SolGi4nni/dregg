//! The away mission, DRIVEN. Not "a crew could" — a crew of four forms, takes its jobs,
//! goes down the real Lean-refereed dungeon, argues about how deep to push, gets told no by
//! the capacity law it voted past, climbs out, and divides the haul by arithmetic.

use super::*;
use dungeon_on_dregg::collective::Custodian;

/// The four crew members. `CrewCharter` canonicalizes into ascending byte order, so these
/// ARE charter seats 0..3.
const BEARER: &str = "player:bramwen"; // charter seat 0 — Tank / Bulwark
const PATHFINDER: &str = "player:corvin"; // charter seat 1 — Scout / Pathfinder
const STRIKER: &str = "player:della"; // charter seat 2 — Mage / Striker
const MENDER: &str = "player:ferro"; // charter seat 3 — Healer / Mender

const DAY_SEED: [u8; 32] = [0x5E; 32];

fn charter() -> CrewCharter {
    CrewCharter::form(
        "descent:the-drowned-marches",
        [
            BEARER.to_string(),
            PATHFINDER.to_string(),
            STRIKER.to_string(),
            MENDER.to_string(),
        ],
    )
    .expect("a valid charter")
}

/// The seating this suite drives: seat 0 bears the pack, seat 1 finds the path, seat 2
/// strikes, seat 3 mends. DECLARED, not proven — the proof path is exercised under
/// `--features private-role-assignment` (see `a_proof_assigned_crew_descends`), and the
/// provenance says so in the type either way.
fn seating() -> CrewSeating {
    CrewSeating::declared(
        charter(),
        [Role::Tank, Role::Scout, Role::Mage, Role::Healer],
    )
    .expect("a permutation of the four jobs")
}

/// ⚑ CARRY OUT A CERTIFIED `ClimbOut` TO ITS END. `flee` demands the surface, so the
/// Mender's writ is spent over `depth + 1` moves — one `ascend` per floor, then the
/// `flee` that banks. The writ stays LIVE across the climb, which is what this exercises.
fn bring_home(mission: &mut CrewDescent) -> crate::crew_descent::MissionStep {
    let mut last = None;
    for floor in 0..=dungeon_on_dregg::descent::FLOORS {
        assert!(
            mission.writ().is_some(),
            "the climb writ is still live at floor {floor}"
        );
        last = Some(mission.carry_out(MENDER).expect("the Mender climbs"));
        if mission.is_home() {
            break;
        }
    }
    assert!(mission.is_home(), "the crew reached the mouth and banked");
    assert!(
        mission.writ().is_none(),
        "and the writ is spent by the flee that ended the run"
    );
    last.expect("the climb landed at least one move")
}

fn depart(seed: u8) -> CrewDescent {
    seating()
        .depart_on_map(seed, DAY_SEED, 0)
        .expect("the crew departs on the shipped map")
}

/// Reach quorum (3 of 4) for `option` and settle.
fn decide(mission: &mut CrewDescent, option: usize, voters: [&str; 3]) -> Writ {
    for voter in voters {
        mission
            .vote(voter, option)
            .unwrap_or_else(|error| panic!("{voter} votes: {error}"));
    }
    mission.settle().expect("quorum reached")
}

/// The crew votes to push and the Pathfinder takes the step.
fn push(mission: &mut CrewDescent) {
    mission
        .call_council(PATHFINDER, Question::Push)
        .expect("the council opens");
    decide(mission, 0, [BEARER, PATHFINDER, STRIKER]);
    mission
        .carry_out(PATHFINDER)
        .expect("the Pathfinder takes the certified step");
}

// ─────────────────────────────────────────────────────────────────────────────────
// THE DRIVING TEST — the whole mission, end to end, with the argument in the middle.
// ─────────────────────────────────────────────────────────────────────────────────

/// **A CREW RUNS THE DESCENT.** Four identities form a crew, take their jobs, and go down.
/// Each seat spends the crew's common 26-breath clock on its OWN job; the two irreversible
/// verbs — one more floor, and climbing out — go to a real quorum vote; and the Bearer's
/// greed on floor one is priced by the dungeon on floor three, when the certified push comes
/// back as a REAL refusal from the Lean-authored capacity law. Then they climb out and the
/// haul divides by a vote, onto the ledger, permanently.
///
/// Every "yes" here is a real committed turn; every "no" is the real executor, the real vote
/// engine, or a real signature check.
#[test]
fn a_crew_descends_argues_and_divides_the_haul() {
    let mut mission = depart(11);
    assert_eq!(mission.depth(), 0);
    assert_eq!(mission.breath_left(), 30, "the light is full");
    assert_eq!(
        mission.seating().provenance(),
        RoleProvenance::Declared,
        "this seating does not claim to be proof-assigned"
    );

    // ── Floor 0: nobody may go deeper on their own say-so. ───────────────────────
    // There is no `SeatMove::Delve` to call — descending is structurally the crew's — and
    // reaching for a decision the crew never made is refused.
    assert!(
        matches!(mission.carry_out(PATHFINDER), Err(CrewDescentError::NoWrit)),
        "one more floor is not a seat's call"
    );

    // The crew councils. Note the question carries the numbers worth arguing about.
    mission
        .call_council(BEARER, Question::Push)
        .expect("any crew member may call the crew together");
    assert!(
        mission.council_poll().is_some(),
        "a real quorum round is sitting"
    );

    // Two votes is not a decision: the AffineLe quorum gate refuses the decision-turn and
    // NOTHING moves.
    mission.vote(BEARER, 0).expect("the Bearer votes to push");
    mission.vote(PATHFINDER, 0).expect("the Pathfinder agrees");
    assert!(
        matches!(mission.settle(), Err(CrewDescentError::BelowQuorum)),
        "two of four certifies nothing"
    );
    assert_eq!(mission.depth(), 0, "anti-ghost: the crew did not move");
    assert_eq!(mission.breath_left(), 30, "and spent no light");
    assert!(
        mission.council_poll().is_some(),
        "the council stays open for the third ballot"
    );

    // The third ballot reaches quorum.
    mission.vote(STRIKER, 0).expect("the Striker agrees");
    let writ = mission.settle().expect("three of four certifies");
    assert_eq!(writ.mandate, Mandate::Descend);
    assert_eq!((writ.winner_tally, writ.total, writ.quorum), (3, 3, 3));

    // A certified decision still needs the hand whose job it is.
    match mission.carry_out(STRIKER) {
        Err(CrewDescentError::WrongHand {
            required, holder, ..
        }) => {
            assert_eq!(required, Role::Scout);
            assert_eq!(holder, PATHFINDER);
        }
        other => panic!("the Striker does not lead the way down, got {other:?}"),
    }
    assert_eq!(mission.depth(), 0, "the mis-aimed hand moved nothing");

    let step = mission
        .carry_out(PATHFINDER)
        .expect("the Pathfinder takes the step");
    assert_eq!(mission.depth(), 1, "floor one");
    assert!(
        mission.verify_step(&step),
        "the descent turn carries the council's warrant on the real receipt chain"
    );
    assert!(
        matches!(mission.carry_out(PATHFINDER), Err(CrewDescentError::NoWrit)),
        "a writ is single-use — one certified push is one floor"
    );

    // ── Floor 1: each seat does its own job, on the crew's common clock. ─────────
    // The guardian stands; only the Striker may strike, at two breath a blow.
    match mission.act(BEARER, SeatMove::Strike) {
        Err(CrewDescentError::OutOfRole(out)) => {
            assert_eq!(out.owner, Role::Mage);
            assert_eq!(out.owner_holder, STRIKER);
            assert!(out.to_string().contains("job"));
        }
        other => panic!("the Bearer does not strike, got {other:?}"),
    }
    mission
        .act(STRIKER, SeatMove::Strike)
        .expect("the Striker fells floor one's guardian");
    assert_eq!(mission.breath_left(), 30 - 1 - 2, "a blow costs two");

    // THE GREED. The Bearer takes way two's key — and two treasures nobody voted for.
    // `pack + depth <= CAP` is the whole game, and the Bearer alone spends it.
    mission
        .act(BEARER, SeatMove::Take { relic: 1 })
        .expect("the key to way two");
    assert_eq!(mission.carry_room(), 8 - 1 - 1);
    mission
        .act(BEARER, SeatMove::Take { relic: 4 })
        .expect("a treasure");
    mission
        .act(BEARER, SeatMove::Take { relic: 5 })
        .expect("another treasure");
    assert_eq!(mission.pack(), 3, "three in the pack on floor one");

    // Only the Pathfinder may exercise a carried key.
    assert!(
        matches!(
            mission.act(MENDER, SeatMove::OpenWay { way: 2 }),
            Err(CrewDescentError::OutOfRole(_))
        ),
        "the Mender does not open ways"
    );
    mission
        .act(PATHFINDER, SeatMove::OpenWay { way: 2 })
        .expect("way two opens");

    // ── Floors 2 and 3: the same shape, and the pack keeps growing. ──────────────
    push(&mut mission);
    assert_eq!(mission.depth(), 2);
    mission
        .act(STRIKER, SeatMove::Strike)
        .expect("the guardian");
    mission
        .act(BEARER, SeatMove::Take { relic: 2 })
        .expect("the key to way three");
    mission
        .act(PATHFINDER, SeatMove::OpenWay { way: 3 })
        .expect("way three opens");

    push(&mut mission);
    assert_eq!(mission.depth(), 3);
    mission.act(STRIKER, SeatMove::Strike).expect("first blow");
    mission.act(STRIKER, SeatMove::Strike).expect("second blow");
    mission
        .act(BEARER, SeatMove::Take { relic: 3 })
        .expect("the key to way four");
    mission
        .act(PATHFINDER, SeatMove::OpenWay { way: 4 })
        .expect("way four opens");

    // ── THE BILL. Five in the pack on floor three: the crew is too laden to go on. ──
    assert_eq!(mission.pack(), 5);
    assert!(
        !mission.can_still_descend(),
        "pack 5 + depth 3 + 1 exceeds the carry ceiling of 8"
    );
    mission
        .call_council(MENDER, Question::Push)
        .expect("the council opens anyway");
    let writ = decide(&mut mission, 0, [BEARER, PATHFINDER, STRIKER]);
    assert_eq!(
        writ.mandate,
        Mandate::Descend,
        "the crew certified the push"
    );
    match mission.carry_out(PATHFINDER) {
        Err(CrewDescentError::World(reason)) => assert!(
            reason.contains("laden"),
            "the DUNGEON refuses it, and says why: {reason}"
        ),
        other => panic!("a crew cannot vote past the capacity law, got {other:?}"),
    }
    assert_eq!(mission.depth(), 3, "anti-ghost: the prize stays unreached");
    assert!(
        mission.writ().is_some(),
        "a refused move burns no writ — drop weight and try again"
    );

    // ── Climbing out is the crew's call too, and the Mender's hand. ──────────────
    mission
        .call_council(MENDER, Question::ClimbOut)
        .expect("the council opens");
    let writ = decide(&mut mission, 0, [BEARER, STRIKER, MENDER]);
    assert_eq!(
        writ.mandate,
        Mandate::ClimbOut,
        "the stale push was replaced"
    );
    assert!(
        matches!(
            mission.carry_out(BEARER),
            Err(CrewDescentError::WrongHand { .. })
        ),
        "the Mender takes the crew home"
    );
    let home = bring_home(&mut mission);
    assert!(
        mission.is_home(),
        "the run is banked and the tomb is frozen"
    );
    assert!(mission.verify_step(&home));
    assert_eq!(mission.haul(), 5, "five relics came home");
    assert!(
        !mission.crowned(),
        "and the prize was NOT among them — the greed cost the crown"
    );

    // ── The split: settled by arithmetic, then frozen onto the ledger. ───────────
    // A division that does not add up never reaches a ballot.
    match mission.call_council(
        BEARER,
        Question::Split {
            candidates: vec![
                ("Even shares".to_string(), even_split(5)),
                ("A phantom share".to_string(), [2, 2, 1, 1]),
            ],
        },
    ) {
        Err(CrewDescentError::SplitDoesNotMatchHaul { proposed, haul, .. }) => {
            assert_eq!((proposed, haul), (6, 5));
        }
        other => panic!("a division must add up to the haul, got {other:?}"),
    }

    mission
        .call_council(
            MENDER,
            Question::Split {
                candidates: vec![
                    ("Even shares".to_string(), even_split(5)),
                    ("The Mender's cut".to_string(), weighted_split(5, 3)),
                ],
            },
        )
        .expect("the split council opens");
    let writ = decide(&mut mission, 1, [BEARER, PATHFINDER, MENDER]);
    assert_eq!(writ.mandate, Mandate::Split([1, 1, 1, 2]));
    mission
        .carry_out(STRIKER)
        .expect("any hand may pay out what the crew certified");

    // A LEDGER FACT, per member — not per job, and not a leader's promise.
    assert_eq!(mission.share_of(MENDER), Some(2), "the Mender's extra cut");
    for member in [BEARER, PATHFINDER, STRIKER] {
        assert_eq!(mission.share_of(member), Some(1));
    }

    // And it is frozen: a second certified division cannot overwrite it.
    mission
        .call_council(
            BEARER,
            Question::Split {
                candidates: vec![
                    ("The Bearer's cut".to_string(), weighted_split(5, 0)),
                    ("Even shares".to_string(), even_split(5)),
                ],
            },
        )
        .expect("the crew may argue again");
    decide(&mut mission, 0, [BEARER, PATHFINDER, STRIKER]);
    match mission.carry_out(BEARER) {
        Err(CrewDescentError::World(reason)) => assert!(
            reason.to_ascii_lowercase().contains("write-once"),
            "the split is WriteOnce-frozen on the ledger: {reason}"
        ),
        other => panic!("a committed split must not be rewritable, got {other:?}"),
    }
    assert_eq!(mission.share_of(MENDER), Some(2), "the split still stands");

    // The whole mission is a chain of real receipts, each naming its warrant — the descent
    // verbs on the descent's ledger, the certified split on the party's.
    assert!(mission.journal().len() >= 15);
    assert!(
        mission.journal().iter().any(|record| matches!(
            record.authority,
            Authority::Council {
                mandate: Mandate::Split(_),
                ..
            }
        )),
        "the split is journalled too, and is checked by the same loop"
    );
    for record in mission.journal() {
        assert_ne!(record.receipt, [0u8; 32]);
        assert!(
            mission.verify_step(record),
            "every descent turn carries the warrant the mission recorded: {record:?}"
        );
        // NON-VACUOUS: the check is a real comparison against the committed receipt, not a
        // structural `true`. A warrant nobody issued does not verify against that turn.
        let mut tampered = record.clone();
        tampered.warrant[0] ^= 0xFF;
        assert!(
            !mission.verify_step(&tampered),
            "a warrant the turn does not carry must NOT verify: {record:?}"
        );
    }

    // THE REPLAY TOOTH: no move on this run is unaccounted for. Every committed descent
    // turn after the deploy-time mint carries a warrant the journal records. (What makes
    // this discriminate is that a move driven around the crew layer carries NO warrant —
    // `authorized_descent::tests::a_move_driven_around_the_wrapper_carries_no_warrant`.)
    let chain = mission.run().descent().world().receipt_chain_snapshot();
    assert!(
        chain.len() >= 15,
        "the tooth walked a real chain of {} turns",
        chain.len()
    );
    assert_eq!(
        mission.unwarranted_turns(),
        Vec::<[u8; 32]>::new(),
        "no move happened on this run that the crew did not authorize"
    );

    // And the mover's story is the LEDGER's story: these registers were re-checked against
    // the Lean-loaded teeth on every one of those turns.
    let descent = mission.run().descent();
    assert_eq!(descent.read_reg("depth"), 3, "the committed depth");
    assert_eq!(descent.read_reg("fate"), 1, "the committed run is banked");
    assert_eq!(descent.read_reg("bank"), 5, "the committed haul");
    assert_eq!(descent.read_reg("pack"), 0, "nothing left in hand");
}

// ─────────────────────────────────────────────────────────────────────────────────
// The teeth, one at a time.
// ─────────────────────────────────────────────────────────────────────────────────

/// **A disciplined crew banks THE PRIZE.** The same four jobs, the same councils — but the
/// Bearer takes only the keys and the crown, so the carry ceiling never closes. This is the
/// non-vacuity partner to the greed run: the split above is not a limitation of the layer.
#[test]
fn a_disciplined_crew_banks_the_prize() {
    let mut mission = depart(12);

    // Floor 1: fell the guardian, take way two's key ONLY.
    push(&mut mission);
    mission.act(STRIKER, SeatMove::Strike).unwrap();
    mission.act(BEARER, SeatMove::Take { relic: 1 }).unwrap();
    mission
        .act(PATHFINDER, SeatMove::OpenWay { way: 2 })
        .unwrap();

    // Floor 2.
    push(&mut mission);
    mission.act(STRIKER, SeatMove::Strike).unwrap();
    mission.act(BEARER, SeatMove::Take { relic: 2 }).unwrap();
    mission
        .act(PATHFINDER, SeatMove::OpenWay { way: 3 })
        .unwrap();

    // Floor 3 — a two-vitality guardian.
    push(&mut mission);
    mission.act(STRIKER, SeatMove::Strike).unwrap();
    mission.act(STRIKER, SeatMove::Strike).unwrap();
    mission.act(BEARER, SeatMove::Take { relic: 3 }).unwrap();
    mission
        .act(PATHFINDER, SeatMove::OpenWay { way: 4 })
        .unwrap();

    // Floor 4 — the bottom, with exactly the room the crown needs.
    assert!(
        mission.can_still_descend(),
        "three keys leave room for one more floor"
    );
    push(&mut mission);
    assert_eq!(mission.depth(), 4);
    mission.act(STRIKER, SeatMove::Strike).unwrap();
    mission.act(STRIKER, SeatMove::Strike).unwrap();
    assert_eq!(
        mission.carry_room(),
        1,
        "room for the prize and nothing else"
    );
    mission
        .act(BEARER, SeatMove::Take { relic: 0 })
        .expect("THE PRIZE");

    mission.call_council(MENDER, Question::ClimbOut).unwrap();
    decide(&mut mission, 0, [BEARER, STRIKER, MENDER]);
    bring_home(&mut mission);

    assert!(mission.crowned(), "the crew banked the prize");
    assert_eq!(mission.haul(), 4, "the crown and three keys");
    assert!(mission.breath_left() > 0, "and got out inside the light");
}

/// **The crew may vote to hold.** A council is not a rubber stamp: the certified answer can
/// be "no", and then there is nothing to carry out and nothing moved.
#[test]
fn a_certified_hold_moves_nothing() {
    let mut mission = depart(13);
    mission.call_council(MENDER, Question::Push).unwrap();
    let writ = decide(&mut mission, 1, [BEARER, STRIKER, MENDER]);
    assert_eq!(writ.mandate, Mandate::Hold);
    assert!(
        matches!(mission.carry_out(PATHFINDER), Err(CrewDescentError::NoWrit)),
        "a hold mints no writ"
    );
    assert_eq!(mission.depth(), 0);
    assert_eq!(mission.breath_left(), 30);
}

/// **Nobody makes your move.** A move signature is verified before any turn is built: a
/// re-pointed one (signed for a strike, submitted as a take) fails, an outsider's genuine
/// signature holds no seat, and one member cannot sign in another's name.
#[test]
fn a_forged_or_repointed_move_signature_is_refused() {
    let mut mission = depart(14);
    push(&mut mission);

    // Re-pointing a signature at a different move: the verb is bound into the message.
    let mut repointed = mission
        .sign_seat_move(STRIKER, SeatMove::Strike)
        .expect("the Striker signs");
    repointed.mv = SeatMove::Take { relic: 1 };
    assert!(
        matches!(
            mission.submit(&repointed),
            Err(CrewDescentError::BadSignature)
        ),
        "a signature cannot be re-pointed at another move"
    );

    // A garbage signature over a real seat's key.
    let mut forged = mission
        .sign_seat_move(STRIKER, SeatMove::Strike)
        .expect("sign");
    forged.signature = dregg_types::Signature([0x7u8; 64]);
    assert!(matches!(
        mission.submit(&forged),
        Err(CrewDescentError::BadSignature)
    ));

    // Mallory's signature is genuine over HER key — and her key holds no crew seat.
    let mallory = Custodian::generate("player:mallory");
    let step = mission.run().step();
    let message =
        mission.seat_move_message_for(&mallory.public_key(), step, SeatMove::Strike.verb());
    let outsider = SignedSeatMove {
        mover_pk: mallory.public_key(),
        mv: SeatMove::Strike,
        step,
        signature: mallory.sign_raw(&message),
    };
    assert!(
        matches!(
            mission.submit(&outsider),
            Err(CrewDescentError::NotOnTheCrew(_))
        ),
        "a valid signature is not a seat"
    );

    // Anti-ghost: none of that moved the world, and the honest move still lands.
    assert_eq!(mission.run().sim().wounds, 0, "no blow was struck");
    mission
        .act(STRIKER, SeatMove::Strike)
        .expect("the honest move commits — the refusals were not vacuous");
    assert_eq!(mission.run().sim().wounds, 1);
}

/// **A move signature is single-use.** It binds the move ordinal, so a signature minted
/// before the mission moved on cannot be replayed after it.
#[test]
fn a_stale_move_signature_is_refused() {
    let mut mission = depart(15);
    push(&mut mission);
    let early = mission
        .sign_seat_move(STRIKER, SeatMove::Strike)
        .expect("signed at this ordinal");
    mission
        .act(STRIKER, SeatMove::Strike)
        .expect("the mission moves on");
    match mission.submit(&early) {
        Err(CrewDescentError::StaleWarrant {
            signed_for,
            current,
        }) => assert!(signed_for < current),
        other => panic!("a signature is spendable once, got {other:?}"),
    }
}

/// **Nobody forges your vote.** A non-crew key holds no ballot (`Ineligible`) and a forged
/// signature is refused before the board moves (`BadSignature`) — the real
/// `collective_choice` engine, not a host `if`.
#[test]
fn a_non_crew_ballot_and_a_forged_ballot_are_both_refused() {
    let mut mission = depart(16);
    let poll = mission
        .call_council(BEARER, Question::Push)
        .expect("the council opens");

    let mallory = Custodian::generate("player:mallory");
    match mission.cast(&mallory.sign_ballot(poll, 0)) {
        Err(CrewDescentError::Vote(reason)) => assert!(
            reason.contains("not in the electorate"),
            "an outsider holds no ballot: {reason}"
        ),
        other => panic!("expected an ineligible refusal, got {other:?}"),
    }

    let seat_pk = mission.party().seat(0).custody().public_key();
    let forged = SignedBallot {
        voter_pk: seat_pk,
        option: 0,
        signature: dregg_types::Signature([0x7u8; 64]),
    };
    match mission.cast(&forged) {
        Err(CrewDescentError::Vote(reason)) => assert!(
            reason.to_ascii_lowercase().contains("signature"),
            "a forged ballot is refused: {reason}"
        ),
        other => panic!("expected a signature refusal, got {other:?}"),
    }
    assert_eq!(
        mission.council_tally().expect("tally").total,
        0,
        "anti-ghost: the board did not move"
    );

    // And an outsider cannot even call the crew together.
    assert!(matches!(
        mission.call_council("player:mallory", Question::ClimbOut),
        Err(CrewDescentError::NotOnTheCrew(_))
    ));
}

/// **One question at a time**, and a split is not askable from inside the dungeon.
#[test]
fn a_split_is_decided_only_once_the_crew_is_home() {
    let mut mission = depart(17);
    assert!(matches!(
        mission.call_council(
            BEARER,
            Question::Split {
                candidates: vec![
                    ("Even".to_string(), even_split(0)),
                    ("Also even".to_string(), even_split(0)),
                ],
            },
        ),
        Err(CrewDescentError::NotHomeYet)
    ));

    mission.call_council(BEARER, Question::Push).unwrap();
    assert!(matches!(
        mission.call_council(MENDER, Question::ClimbOut),
        Err(CrewDescentError::CouncilAlreadySitting)
    ));
}

/// A seating is a PERMUTATION of the four jobs — a crew with two Strikers and no Mender is
/// refused before it can depart.
#[test]
fn a_seating_refuses_a_doubled_job() {
    assert!(
        CrewSeating::declared(
            charter(),
            [Role::Tank, Role::Mage, Role::Mage, Role::Healer]
        )
        .is_err(),
        "two Strikers is not a crew"
    );
    let seating = seating();
    assert_eq!(seating.identity_in(Role::Tank), BEARER);
    assert_eq!(seating.role_of(MENDER), Some(Role::Healer));
    assert_eq!(seating.role_of("player:mallory"), None);
}

/// Every move belongs to exactly one job, and the jobs partition the seat-owned verbs — so
/// naming an out-of-role refusal can never name the wrong seat, and no verb is ownerless.
#[test]
fn the_seat_owned_moves_partition_the_four_jobs() {
    let owners = [
        SeatMove::OpenWay { way: 2 }.owner(),
        SeatMove::Strike.owner(),
        SeatMove::Take { relic: 0 }.owner(),
    ];
    assert_eq!(owners, [Role::Scout, Role::Mage, Role::Tank]);
    // The two collective verbs take the remaining hands: the path role leads the step down,
    // the mender brings everyone home. All four jobs hold something.
    assert_eq!(Mandate::Descend.hand(), Some(Role::Scout));
    assert_eq!(Mandate::ClimbOut.hand(), Some(Role::Healer));
    assert_eq!(Mandate::Hold.hand(), None);
    assert_eq!(Mandate::Split([0; 4]).hand(), None);
}

/// The customary divisions always hand out exactly the haul — the arithmetic a split council
/// is bounded by.
#[test]
fn every_customary_division_adds_up() {
    for haul in 0..=16u64 {
        assert_eq!(even_split(haul).iter().sum::<u64>(), haul);
        for seat in 0..CREW_SEATS {
            assert_eq!(weighted_split(haul, seat).iter().sum::<u64>(), haul);
        }
        if haul > 0 {
            let weighted = weighted_split(haul, 3);
            assert!(
                weighted[3] >= even_split(haul)[3],
                "a cut is a cut off the top"
            );
        }
    }
}

/// **A warrant is bound to ITS run.** The same crew on a second descent derives different
/// warrants, so a signature or certificate from one mission never authorizes a move in
/// another.
#[test]
fn a_warrant_does_not_travel_between_missions() {
    let mut first = depart(18);
    let mut second = depart(19);
    push(&mut first);
    let signed = first
        .sign_seat_move(STRIKER, SeatMove::Strike)
        .expect("sign");
    assert_ne!(
        first.seat_warrant(&signed),
        second.seat_warrant(&signed),
        "the descent cell is bound into the warrant"
    );
    assert!(
        matches!(
            second.submit(&signed),
            Err(CrewDescentError::BadSignature) | Err(CrewDescentError::StaleWarrant { .. })
        ),
        "and the signature does not verify against the other run"
    );
}

/// **The proof path, end to end** — roles assigned by the real crew-bound hiding proof over
/// preferences nobody reveals, and THAT seating goes down the dungeon. Heavy (it links the
/// prover), so it rides the same feature the assignment itself does.
#[cfg(feature = "private-role-assignment")]
#[test]
fn a_proof_assigned_crew_descends() {
    use crate::crew::{CrewRoll, HiddenPreference};

    // Each member's private row, indexed by Role::ALL (Tank, Scout, Mage, Healer). Nobody
    // publishes these; only their commitments go on the roll.
    let preferences: [HiddenPreference; CREW_SEATS] = [
        HiddenPreference::new([3, 0, 0, 0], [true; 4], [1u8; 32]).unwrap(),
        HiddenPreference::new([0, 3, 0, 0], [true; 4], [2u8; 32]).unwrap(),
        HiddenPreference::new([0, 0, 3, 0], [true; 4], [3u8; 32]).unwrap(),
        HiddenPreference::new([0, 0, 0, 3], [true; 4], [4u8; 32]).unwrap(),
    ];
    let roll = CrewRoll::from_preferences(charter(), &preferences);
    let assignment = roll
        .assign_roles(&preferences)
        .expect("the crew-bound hiding proof verifies");

    let seating = CrewSeating::proven(&assignment);
    assert!(
        seating.provenance().is_proven(),
        "the seating records that a proof produced it"
    );
    assert_eq!(
        seating.roles(),
        [Role::Tank, Role::Scout, Role::Mage, Role::Healer]
    );

    let mut mission = seating
        .depart_on_map(20, DAY_SEED, 0)
        .expect("the proof-assigned crew departs");
    push(&mut mission);
    assert_eq!(mission.depth(), 1);
    mission
        .act(STRIKER, SeatMove::Strike)
        .expect("the job the proof gave them");
    assert!(matches!(
        mission.act(BEARER, SeatMove::Strike),
        Err(CrewDescentError::OutOfRole(_))
    ));
}
