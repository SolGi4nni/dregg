//! THE ORACLE PIT, DRIVEN: a confidential prediction market opened on one real Descent run.
//!
//! Two players take opposite PRIVATE positions, the line moves, the board freezes, the run's
//! record is re-executed, the market settles on what the re-execution found, the winner is paid,
//! and every way of faking a settlement is refused.
//!
//! The oracle half of this file (`read_verified_run`) needs no FHE at all — it is a pure function
//! of a subject and a run record — so the falsifiers there are cheap and exact. The market half
//! pays for a real n-of-n BFV keygen (and, at settlement, the multiparty relinearization ceremony
//! for the quadratic pool), so it is kept to as few sessions as the drive allows.

use dregg_sdk::{
    MlDsaKeygenCoreRealInstall, MlDsaSignCoreRealInstall, MlDsaVerifyCoreInstall,
    install_verified_mldsa_keygen_core_real, install_verified_mldsa_sign_core_real,
    install_verified_mldsa_verify_core,
};
use dreggnet_market::oracle_pit::{
    DescentQuestion, MAX_POSITION_STAKE, OraclePitOffering, OraclePitSession, PitCostMatrix,
    PitRefusal, PitRunTerminal, PitSide, PitSubject, TURN_BACK_NO, TURN_BACK_YES, TURN_CLAIM,
    pit_verdict, position_commitment, read_verified_run,
};
use dreggnet_offerings::audience::{Audience, project};
use dreggnet_offerings::native_descent::{
    CommittedSeed, NativeDescentOffering, NativeDescentRecord, native_descent_run_day_seed,
};
use dreggnet_offerings::{Action, DreggIdentity, Offering, Outcome, SessionConfig};

/// `NativeDescentOffering::open` normalizes its config seed to `((seed % 251) + 1) as u8`, so this
/// is the config seed that deploys the run on world seed 7.
const CONFIG_SEED: u64 = 6;
/// The deploy seed the config seed above normalizes to. The pit's subject names it.
const RUN_SEED: u8 = 7;

/// Install the real ML-DSA cores before any identity is derived. Both the Descent's world cell and
/// the pit's cipherclerk derive a PQ identity, and `dregg-pq` ABORTS the process rather than
/// silently answer with the unaudited `fips204` crate. The escape hatch is deliberately not used:
/// a prediction market whose settlement is the point does not get to sign its turns with crypto
/// outside the audited TCB.
fn install_verified_turn_pq_runtime() {
    assert!(
        std::env::var_os("DREGG_ALLOW_UNAUDITED_PQ").is_none(),
        "the Oracle Pit gate must run with the unaudited-PQ escape hatch unset"
    );
    assert!(
        matches!(
            install_verified_mldsa_keygen_core_real(),
            MlDsaKeygenCoreRealInstall::Installed | MlDsaKeygenCoreRealInstall::AlreadyInstalled
        ),
        "archive lacks dregg_mldsa_keygen_real; bootstrap/fetch a current verified-runtime seed"
    );
    assert!(
        matches!(
            install_verified_mldsa_sign_core_real(),
            MlDsaSignCoreRealInstall::Installed | MlDsaSignCoreRealInstall::AlreadyInstalled
        ),
        "archive lacks dregg_fips204_sign_real; bootstrap/fetch a current verified-runtime seed"
    );
    assert!(
        matches!(
            install_verified_mldsa_verify_core(),
            MlDsaVerifyCoreInstall::Installed | MlDsaVerifyCoreInstall::AlreadyInstalled
        ),
        "archive lacks dregg_fips204_verify_real; bootstrap/fetch a current verified-runtime seed"
    );
}

fn descender() -> DreggIdentity {
    DreggIdentity("descender:one".to_string())
}

fn day(byte: u8) -> CommittedSeed {
    CommittedSeed::from_bytes([byte; 32])
}

/// The perfect crowned run: descend, slay, take each way's key, exercise it, and bank the Crown of
/// the Deep out of floor four. 18 moves, 24 of the light's 26 breaths.
const CROWNED_RUN: &[(&str, i64)] = &[
    ("delve", 0),
    ("smite", 0),
    ("loot", 1),
    ("unlock", 2),
    ("delve", 0),
    ("smite", 0),
    ("loot", 2),
    ("unlock", 3),
    ("delve", 0),
    ("smite", 0),
    ("smite", 0),
    ("loot", 3),
    ("unlock", 4),
    ("delve", 0),
    ("smite", 0),
    ("smite", 0),
    ("loot", 0),
    ("flee", 0),
];

/// A timid run: one floor, one relic, bank and go home. No crown.
const TIMID_RUN: &[(&str, i64)] = &[("delve", 0), ("smite", 0), ("loot", 1), ("flee", 0)];

/// A run that is still going: a genuine record, but of an unfinished descent.
const UNFINISHED_RUN: &[(&str, i64)] = &[("delve", 0), ("smite", 0)];

/// Play `moves` on a real Descent bound to `beacon_day` and export its portable record.
fn play(beacon_day: CommittedSeed, moves: &[(&str, i64)]) -> NativeDescentRecord {
    install_verified_turn_pq_runtime();
    let offering = NativeDescentOffering::on_day(beacon_day);
    let mut session = offering
        .open(SessionConfig::with_seed(CONFIG_SEED))
        .expect("the Descent deploys");
    for (index, (turn, arg)) in moves.iter().enumerate() {
        let outcome = offering.advance(
            &mut session,
            Action::new(format!("{turn} {arg}"), *turn, *arg, true),
            descender(),
        );
        match outcome {
            Outcome::Landed { .. } => {}
            Outcome::Refused(why) => {
                panic!("move {index} ({turn} {arg}) was refused by the real executor: {why}")
            }
        }
    }
    session.export_record()
}

/// The pit subject for the run this file plays on `beacon_day`.
fn subject_on(beacon_day: CommittedSeed, question: DescentQuestion) -> PitSubject {
    PitSubject::new(
        RUN_SEED,
        native_descent_run_day_seed(&beacon_day, RUN_SEED),
        question,
    )
}

/// The canonical subject: the run played on day `0xd1`.
fn crowned_subject(question: DescentQuestion) -> PitSubject {
    subject_on(day(0xd1), question)
}

// =============================================================================
// THE ORACLE — pure, FHE-free, and the part a third party re-runs to audit us.
// =============================================================================

/// The settlement source reads a run's terminal state off an EXACT re-execution, and the reading
/// matches what the run actually did. This is the whole basis on which the market pays out.
#[test]
fn the_oracle_reads_a_run_by_re_executing_it() {
    let crowned = play(day(0xd1), CROWNED_RUN);
    let reading = read_verified_run(&crowned_subject(DescentQuestion::Crowned), &crowned)
        .expect("a genuine crowned record re-executes");
    assert_eq!(reading.terminal, PitRunTerminal::Banked);
    assert!(reading.banked, "the run reached a terminal bank");
    assert!(reading.crowned, "the Crown of the Deep banked");
    assert_eq!(reading.banked_relics, 4, "crown + three way keys banked");
    assert_eq!(reading.depth, 4, "the run reached the bottom");
    assert_eq!(reading.moves, CROWNED_RUN.len());
    assert!(reading.settlement_receipt_hash.is_some());
    assert_eq!(
        reading.run_root, crowned.root,
        "the reading's journal root is the replayed root"
    );

    let timid = play(day(0xd1), TIMID_RUN);
    let timid_reading = read_verified_run(&crowned_subject(DescentQuestion::Crowned), &timid)
        .expect("a genuine timid record re-executes");
    assert!(timid_reading.banked);
    assert!(!timid_reading.crowned, "no crown on a one-floor run");
    assert_eq!(timid_reading.banked_relics, 1);
    assert_eq!(timid_reading.depth, 1);

    // The questions resolve off the reading, not off anything the submitter said.
    assert!(DescentQuestion::Crowned.resolve(&reading));
    assert!(!DescentQuestion::Crowned.resolve(&timid_reading));
    assert!(DescentQuestion::Banked.resolve(&timid_reading));
    assert!(DescentQuestion::DepthAtLeast(4).resolve(&reading));
    assert!(!DescentQuestion::DepthAtLeast(4).resolve(&timid_reading));
    assert!(DescentQuestion::RelicsBankedAtLeast(4).resolve(&reading));
    assert!(!DescentQuestion::RelicsBankedAtLeast(4).resolve(&timid_reading));
}

/// EVERY way of faking a settlement, refused. This is the falsifier battery for the claim "the
/// settlement source is checkable, not asserted".
#[test]
fn the_oracle_refuses_every_faked_settlement() {
    let subject = crowned_subject(DescentQuestion::Crowned);
    let timid = play(day(0xd1), TIMID_RUN);
    let crowned = play(day(0xd1), CROWNED_RUN);

    // 1. THE MONEY FORGERY: a bettor holding a losing record hand-edits its completion to claim
    //    the crown. Re-execution recomputes the completion from the committed custody and the
    //    stated one no longer matches.
    let mut forged_crown = timid.clone();
    forged_crown
        .completion
        .as_mut()
        .expect("the timid run completed")
        .crowned = true;
    assert!(
        matches!(
            read_verified_run(&subject, &forged_crown),
            Err(PitRefusal::ReplayFailed(_))
        ),
        "a hand-edited completion settled the market"
    );

    // 2. A FORGED BANKED-RELIC LIST — the same class, on the payout-bearing field.
    let mut forged_relics = timid.clone();
    forged_relics
        .completion
        .as_mut()
        .expect("the timid run completed")
        .banked_relics = vec![0, 1, 2, 3];
    assert!(matches!(
        read_verified_run(&subject, &forged_relics),
        Err(PitRefusal::ReplayFailed(_))
    ));

    // 3. A SPLICED RECORD — drop the terminal bank and keep the summary that claims it.
    let mut spliced = crowned.clone();
    spliced.events.pop();
    assert!(
        matches!(
            read_verified_run(&subject, &spliced),
            Err(PitRefusal::ReplayFailed(_))
        ),
        "a spliced journal settled the market"
    );

    // 4. A GENUINE RUN FROM THE WRONG DAY. It re-executes perfectly — replay redeploys on the
    //    record's OWN day-seed — so only the subject binding catches it. This is why the pit
    //    checks `day_seed` before it replays anything.
    let other_day = play(day(0xd2), CROWNED_RUN);
    assert!(
        read_verified_run(&subject_on(day(0xd2), DescentQuestion::Crowned), &other_day).is_ok(),
        "the other day's record is itself genuine — the refusal below must be the BINDING, not a \
         broken record"
    );
    assert_eq!(
        read_verified_run(&subject, &other_day),
        Err(PitRefusal::WrongDay),
        "another day's genuine crowned run settled this pit"
    );

    // 5. A GENUINE RUN FROM THE WRONG WORLD SEED.
    let wrong_seed = PitSubject::new(
        RUN_SEED + 1,
        native_descent_run_day_seed(&day(0xd1), RUN_SEED),
        DescentQuestion::Crowned,
    );
    assert_eq!(
        read_verified_run(&wrong_seed, &crowned),
        Err(PitRefusal::WrongRun {
            want: RUN_SEED + 1,
            got: RUN_SEED
        })
    );

    // 6. A PREFIX OF A LIVE RUN. Perfectly genuine, re-executes cleanly, and still cannot settle:
    //    you do not get to close the market on the part of the run you like.
    let unfinished = play(day(0xd1), UNFINISHED_RUN);
    assert_eq!(
        read_verified_run(&subject, &unfinished),
        Err(PitRefusal::RunNotTerminal),
        "a live run's prefix settled the market"
    );

    // The genuine record still settles — the battery above is not just refusing everything.
    assert!(read_verified_run(&subject, &crowned).is_ok());
}

/// THE NAMED LIMITATION, DRIVEN HONESTLY. `(seed, day_seed)` fixes the day's WORLD, not a run of
/// it: a crowned run and a timid one on the same day are BOTH genuine and both re-execute, so an
/// unpinned pit settles on whichever arrives first. Pinning a player closes the cross-player half.
/// This test exists so the gap is a measured fact in the record, not a caveat in a doc comment.
#[test]
fn an_unpinned_subject_accepts_any_genuine_run_of_that_days_world() {
    let unpinned = crowned_subject(DescentQuestion::Crowned);
    let crowned = play(day(0xd1), CROWNED_RUN);
    let timid = play(day(0xd1), TIMID_RUN);

    // BOTH are genuine, and they disagree about the very question the market prices.
    let crowned_reading = read_verified_run(&unpinned, &crowned).expect("crowned re-executes");
    let timid_reading = read_verified_run(&unpinned, &timid).expect("timid re-executes");
    assert!(DescentQuestion::Crowned.resolve(&crowned_reading));
    assert!(!DescentQuestion::Crowned.resolve(&timid_reading));
    assert_ne!(
        crowned_reading.run_root, timid_reading.run_root,
        "two distinct runs of one day's world"
    );

    // Pinning the player who actually played still admits that player's run...
    let pinned = crowned_subject(DescentQuestion::Crowned).on_player(&descender());
    assert!(read_verified_run(&pinned, &crowned).is_ok());
    // ...and a pit pinned to somebody else refuses it, on the REPLAY-bound actor.
    let other = crowned_subject(DescentQuestion::Crowned)
        .on_player(&DreggIdentity("someone:else".to_string()));
    assert_eq!(
        read_verified_run(&other, &crowned),
        Err(PitRefusal::WrongPlayer)
    );
    // The pin is part of the pit's identity, so a pinned pit is a different on-ledger object.
    assert_ne!(pinned.digest(), unpinned.digest());
    assert_ne!(pinned.digest(), other.digest());
}

/// The verdict a settled pit freezes on-ledger is a function of the whole re-execution, so an
/// auditor recomputes it from the run record alone.
#[test]
fn the_verdict_recomputes_from_the_run_record_alone() {
    let subject = crowned_subject(DescentQuestion::Crowned);
    let crowned = play(day(0xd1), CROWNED_RUN);
    let reading = read_verified_run(&subject, &crowned).expect("re-execution");
    let outcome = subject.question.resolve(&reading);
    let verdict = pit_verdict(&subject, &reading, outcome);

    // Independently, from nothing but the record: same reading, same verdict.
    let again = read_verified_run(&subject, &crowned).expect("re-execution is deterministic");
    assert_eq!(again, reading);
    assert_eq!(pit_verdict(&subject, &again, outcome), verdict);

    // The losing run's verdict for the SAME question is a different 32 bytes.
    let timid = play(day(0xd1), TIMID_RUN);
    let timid_reading = read_verified_run(&subject, &timid).expect("re-execution");
    let timid_outcome = subject.question.resolve(&timid_reading);
    assert!(!timid_outcome);
    assert_ne!(
        pit_verdict(&subject, &timid_reading, timid_outcome),
        verdict
    );
}

// =============================================================================
// THE MARKET — real threshold BFV in the pricing and settlement path.
// =============================================================================

fn open_pit(question: DescentQuestion, parties: usize) -> (OraclePitOffering, OraclePitSession) {
    install_verified_turn_pq_runtime();
    let offering =
        OraclePitOffering::new(crowned_subject(question), PitCostMatrix::unit(), parties)
            .expect("the unit cost matrix fits under the plaintext modulus");
    let session = offering
        .open(SessionConfig::with_seed(0x0AC1E))
        .expect("the pit cell is born and the committee ceremony runs");
    (offering, session)
}

/// THE DRIVE. A market opens on today's run, two players take opposite private positions, the
/// published line moves, the board freezes, the verified run settles it, and the payouts are right.
#[test]
fn a_market_opens_on_a_run_takes_private_positions_moves_the_line_and_pays_the_winner() {
    let (offering, mut session) = open_pit(DescentQuestion::Crowned, 3);
    let alice = DreggIdentity("alice".to_string());
    let bob = DreggIdentity("bob".to_string());

    // ── PRIVATE POSITIONS ────────────────────────────────────────────────────
    // Each lands a real executor turn freezing a hiding commitment onto the pit cell's
    // WriteOnce board. The pit learns a 32-byte digest and two ciphertexts; nothing else.
    let alice_receipt = match offering.advance(
        &mut session,
        Action::new("back yes", TURN_BACK_YES, 3, true),
        alice.clone(),
    ) {
        Outcome::Landed { receipt, .. } => receipt,
        Outcome::Refused(why) => panic!("alice's position was refused: {why}"),
    };
    assert_ne!(alice_receipt.turn_hash, [0; 32]);
    let quote_after_alice = session.book.quote().expect("the committee opens the line");
    assert_eq!(quote_after_alice.price_yes, 6, "2A·q_yes + B·q_no at (3,0)");
    assert_eq!(quote_after_alice.price_no, 3, "B·q_yes + 2C·q_no at (3,0)");
    assert_eq!(quote_after_alice.implied_yes_bps, 6_666);

    match offering.advance(
        &mut session,
        Action::new("back no", TURN_BACK_NO, 5, true),
        bob.clone(),
    ) {
        Outcome::Landed { .. } => {}
        Outcome::Refused(why) => panic!("bob's position was refused: {why}"),
    }
    let quote_after_bob = session.book.quote().expect("the committee opens the line");
    assert_eq!(quote_after_bob.price_yes, 11, "2A·q_yes + B·q_no at (3,5)");
    assert_eq!(quote_after_bob.price_no, 13, "B·q_yes + 2C·q_no at (3,5)");
    assert_eq!(quote_after_bob.implied_yes_bps, 4_583);
    assert!(
        quote_after_bob.implied_yes_bps < quote_after_alice.implied_yes_bps,
        "the line did not move when the opposite side was backed"
    );
    assert_eq!(session.book.positions(), 2);

    // ── FREEZE, THEN CONSULT THE ORACLE ──────────────────────────────────────
    session.book.freeze().expect("the board freezes");
    assert!(!session.book.is_open());
    assert!(
        matches!(
            offering.advance(
                &mut session,
                Action::new("back yes", TURN_BACK_YES, 1, true),
                alice.clone(),
            ),
            Outcome::Refused(_)
        ),
        "a position landed after the board froze"
    );
    assert_eq!(session.book.positions(), 2, "a refusal minted no position");

    let record = play(day(0xd1), CROWNED_RUN);
    let settlement = session
        .book
        .settle_on_verified_run(&record)
        .expect("the verified crowned run settles the pit");

    assert!(settlement.outcome, "the run was crowned, so YES");
    assert!(settlement.reading.crowned);
    assert_eq!(settlement.reading.depth, 4);
    // The pool IS the quadratic cost function, opened out of a real ct×ct multiply under the
    // collective relinearization key by the full quorum.
    assert_eq!(
        settlement.pool as u128,
        PitCostMatrix::unit().cost(3, 5),
        "the dark pool did not open to the plaintext quadratic"
    );
    assert_eq!(settlement.pool, 49);
    assert_eq!(settlement.winning_shares, 3);
    assert_eq!(settlement.losing_shares, 5);
    assert_eq!(settlement.payout_per_share, 16, "49 / 3, floored");
    assert_eq!(
        settlement.verdict,
        pit_verdict(offering.subject(), &settlement.reading, true),
        "the frozen verdict is not the one an auditor recomputes"
    );

    // ── PAYOUTS ──────────────────────────────────────────────────────────────
    let alice_opening = session.wallets.openings(&alice)[0];
    let bob_opening = session.wallets.openings(&bob)[0];
    assert_eq!(alice_opening.side, PitSide::Yes);
    assert_eq!(bob_opening.side, PitSide::No);

    let (alice_payout, claim_receipt) = session
        .book
        .claim(
            alice_opening.side,
            alice_opening.stake,
            alice_opening.nonce,
            &alice,
        )
        .expect("alice's frozen position claims");
    assert_ne!(claim_receipt.turn_hash, [0; 32]);
    assert_eq!(alice_payout.amount, 48, "3 shares at 16 per share");

    let (bob_payout, _) = session
        .book
        .claim(bob_opening.side, bob_opening.stake, bob_opening.nonce, &bob)
        .expect("bob may open his losing position");
    assert_eq!(bob_payout.amount, 0, "the losing side is paid nothing");

    assert!(
        alice_payout.amount + bob_payout.amount <= settlement.pool,
        "the pit paid out more than the pool held"
    );

    // A second claim on the same frozen position is refused.
    assert!(
        session
            .book
            .claim(
                alice_opening.side,
                alice_opening.stake,
                alice_opening.nonce,
                &alice
            )
            .is_err(),
        "a position was claimed twice"
    );

    // ── A POSITION THAT WAS NEVER TAKEN CANNOT CLAIM ─────────────────────────
    let mallory = DreggIdentity("mallory".to_string());
    assert!(
        session.book.claim(PitSide::Yes, 3, 1, &mallory).is_err(),
        "an untaken position claimed the pool"
    );
    // Even alice's EXACT opening, presented by someone else, recomputes to a different commitment
    // and matches no frozen slot.
    assert!(
        session
            .book
            .claim(
                alice_opening.side,
                alice_opening.stake,
                alice_opening.nonce,
                &mallory
            )
            .is_err(),
        "a stolen opening claimed another holder's position"
    );
    assert_ne!(
        position_commitment(
            offering.subject(),
            alice_opening.side,
            alice_opening.stake,
            alice_opening.nonce,
            &mallory
        ),
        alice_opening.commitment
    );

    // ── THE PIT RE-VERIFIES AGAINST THE LEDGER ───────────────────────────────
    let report = offering.verify(&session);
    assert!(
        report.verified,
        "the settled pit failed re-verification: {}",
        report.detail
    );

    // ── AND CANNOT BE RE-SETTLED ─────────────────────────────────────────────
    let timid = play(day(0xd1), TIMID_RUN);
    assert_eq!(
        session.book.settle_on_verified_run(&timid),
        Err(PitRefusal::AlreadySettled),
        "the pit re-settled on a second run record"
    );
}

/// The board is FROZEN by the executor, not by our bookkeeping: an already-committed position
/// cannot be rewritten once the run starts to look bad, and the pit refuses to settle before the
/// board is closed.
#[test]
fn a_committed_position_cannot_be_rewritten_and_an_open_board_cannot_settle() {
    let (offering, mut session) = open_pit(DescentQuestion::Banked, 2);
    let alice = DreggIdentity("alice".to_string());
    let (opening, _) = session
        .back(PitSide::Yes, 4, &alice)
        .expect("alice takes a position");

    // THE WriteOnce TOOTH, DRIVEN: rewriting the frozen commitment is a real executor refusal.
    let attempt = session.book.attempt_overwrite(opening.slot, [0xff; 32]);
    assert!(
        attempt.is_err(),
        "the executor let a committed position be rewritten: {attempt:?}"
    );

    // Settling an open board is refused before the oracle is even consulted.
    let record = play(day(0xd1), CROWNED_RUN);
    assert_eq!(
        session.book.settle_on_verified_run(&record),
        Err(PitRefusal::StillOpen),
        "a live board settled"
    );

    // Bounds are real: a stake over the ceiling and a zero stake are both refused.
    assert!(
        session
            .back(PitSide::Yes, MAX_POSITION_STAKE + 1, &alice)
            .is_err()
    );
    assert!(matches!(
        offering.advance(
            &mut session,
            Action::new("back yes", TURN_BACK_YES, 0, true),
            alice.clone()
        ),
        Outcome::Refused(_)
    ));
    assert_eq!(session.book.positions(), 1, "no refusal minted a position");

    // TWO GENUINELY DISTINCT POSITIONS THAT COMMIT TO THE SAME DIGEST. A caller that reuses a
    // nonce for the same (side, stake, holder) produces identical commitments, but both stakes are
    // folded into the aggregate and both occupy their own frozen board slot — so both must be
    // claimable exactly once. Matching a claim on commitment alone would strand the second.
    let (twin_a, _) = session
        .book
        .take_position(PitSide::Yes, 2, 777, &alice)
        .expect("first twin position");
    let (twin_b, _) = session
        .book
        .take_position(PitSide::Yes, 2, 777, &alice)
        .expect("second twin position");
    assert_eq!(
        twin_a.commitment, twin_b.commitment,
        "a reused nonce is exactly the colliding-commitment case under test"
    );
    assert_ne!(twin_a.slot, twin_b.slot, "each position froze its own slot");
    assert_eq!(session.book.positions(), 3);

    let report = offering.verify(&session);
    assert!(
        report.verified,
        "an open pit failed re-verification: {}",
        report.detail
    );

    // Settle so the twins can be claimed. The subject asks whether the run BANKED; the crowned
    // record banked, so YES wins and every position here is on the winning side.
    session.book.freeze().expect("the board freezes");
    let settlement = session
        .book
        .settle_on_verified_run(&record)
        .expect("the verified run settles the pit");
    assert!(settlement.outcome, "the crowned run banked");
    assert_eq!(settlement.winning_shares, 8, "4 + 2 + 2 shares on YES");
    assert_eq!(settlement.losing_shares, 0);
    assert_eq!(settlement.pool, 64, "A·q_yes² at q_yes = 8, q_no = 0");
    assert_eq!(settlement.payout_per_share, 8);

    // BOTH twins claim, each exactly once — the fix this case exists for.
    let (first, _) = session
        .book
        .claim(PitSide::Yes, 2, 777, &alice)
        .expect("the first twin claims");
    assert_eq!(first.amount, 16);
    let (second, _) = session
        .book
        .claim(PitSide::Yes, 2, 777, &alice)
        .expect("the second twin must not be stranded by its twin's claim");
    assert_eq!(second.amount, 16);
    assert_ne!(first.slot, second.slot, "each claim consumed its own slot");
    assert!(
        session.book.claim(PitSide::Yes, 2, 777, &alice).is_err(),
        "a third claim found a position that was never taken"
    );

    // Conservation still holds across every claim on the pit.
    let (alice_main, _) = session
        .book
        .claim(opening.side, opening.stake, opening.nonce, &alice)
        .expect("alice's original position claims");
    assert_eq!(alice_main.amount, 32, "4 shares at 8 per share");
    assert!(
        first.amount + second.amount + alice_main.amount <= settlement.pool,
        "the pit paid out more than the pool held"
    );

    let report = offering.verify(&session);
    assert!(
        report.verified,
        "the settled pit failed re-verification: {}",
        report.detail
    );
}

/// The audience boundary. `hidden_information()` is `true`, the SHARED projection carries the line
/// and nothing else, and only the private projection names a holder's own side and stake.
#[test]
fn the_shared_surface_carries_the_line_but_never_a_position() {
    let (offering, mut session) = open_pit(DescentQuestion::Crowned, 2);
    assert!(
        offering.hidden_information(),
        "an offering whose render_for names a position must declare it"
    );

    let alice = DreggIdentity("alice".to_string());
    let bob = DreggIdentity("bob".to_string());
    session.back(PitSide::Yes, 7, &alice).expect("alice backs");
    session.back(PitSide::No, 2, &bob).expect("bob backs");
    let quote = session.book.quote().expect("the line opens");
    assert_eq!(quote.price_yes, 16, "2·7 + 2");
    assert_eq!(quote.price_no, 11, "7 + 2·2");

    let shared = project(&offering, &session, &Audience::Shared);
    let shared_text = format!("{:?} {:?}", shared.surface.view(), shared.actions);
    assert!(shared.hidden_information);
    assert!(!shared.private);
    assert!(
        shared_text.contains("THE LINE"),
        "the shared surface must still publish the odds"
    );
    assert!(
        !shared_text.contains("YOUR POSITION"),
        "the shared surface painted a private position"
    );
    for needle in ["alice", "bob"] {
        assert!(
            !shared_text.contains(needle),
            "the shared surface named a holder ({needle})"
        );
    }
    // The openings themselves must not be reachable from the shared projection.
    let alice_opening = session.wallets.openings(&alice)[0];
    assert!(
        !shared_text.contains(&alice_opening.encode()),
        "the shared surface leaked a position opening"
    );

    let private = project(&offering, &session, &Audience::private(alice.clone()));
    let private_text = format!("{:?} {:?}", private.surface.view(), private.actions);
    assert!(private.private);
    assert!(private_text.contains("THE LINE"), "the line is public too");
    assert!(
        private_text.contains("YOUR POSITION") && private_text.contains("YES"),
        "the private projection must show the viewer their own position"
    );
    assert!(private_text.contains(&alice_opening.encode()));

    // Bob's private projection shows BOB's position and not alice's.
    let bob_opening = session.wallets.openings(&bob)[0];
    assert_ne!(bob_opening.encode(), alice_opening.encode());
    let bobs = project(&offering, &session, &Audience::private(bob.clone()));
    let bobs_text = format!("{:?} {:?}", bobs.surface.view(), bobs.actions);
    assert!(bobs_text.contains(&bob_opening.encode()));
    assert!(
        !bobs_text.contains(&alice_opening.encode()),
        "one player's private projection leaked another's opening"
    );

    // A stranger sees only the public line — no position at all.
    let stranger = DreggIdentity("stranger".to_string());
    let strangers = project(&offering, &session, &Audience::private(stranger.clone()));
    let strangers_text = format!("{:?} {:?}", strangers.surface.view(), strangers.actions);
    assert!(strangers_text.contains("you hold no position"));
    assert!(!strangers_text.contains("YOUR POSITION"));

    // The claim affordance is a per-viewer capability: it never lights for a non-holder, and it
    // does not light for a holder before settlement either.
    let claim_enabled = |viewer: &DreggIdentity| {
        offering
            .actions_for(&session, viewer)
            .into_iter()
            .find(|action| action.turn == TURN_CLAIM)
            .map(|action| action.enabled)
            .expect("the claim affordance is always rendered")
    };
    assert!(!claim_enabled(&alice));
    assert!(!claim_enabled(&stranger));
}
