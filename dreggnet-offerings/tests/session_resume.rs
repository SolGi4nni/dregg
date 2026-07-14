//! **The session-resume seam, DRIVEN over the real dungeon substrate** — the last durable-store
//! closure: an [`OfferingHost`] session survives a restart by REPLAYING its move-log to the
//! identical committed state, never by trusting a serialized blob.
//!
//! - a live session records its **reproducible public input** (the seed + the ordered landed
//!   advances) as a [`SessionMoveLog`], written through to an attached [`SessionResumeStore`];
//! - across a simulated RESTART (drop the host, boot a fresh one over the same store) the session
//!   REOPENS by re-driving its log — to the byte-identical committed-state commitment (non-vacuous:
//!   a session at genesis, or driven differently, commits differently);
//! - a TAMPERED log (a forged / ineligible advance spliced in) is REFUSED by the executor on
//!   re-drive — the resume fails, no forged session is left live (fail-closed);
//! - the in-memory store round-trips (record open + landed, load, enumerate).

use dreggnet_offerings::dungeon::{DungeonOffering, TURN_CHOOSE};
use dreggnet_offerings::resume::{InMemoryResumeStore, LoggedMove, SessionMoveLog};
use dreggnet_offerings::{
    Action, DreggIdentity, OfferingHost, ResumeError, SessionConfig, SessionId, SessionResumeStore,
};
use dungeon_on_dregg::{KP_CLAIM_RED, KP_DESCEND, KP_PRESS_ON, KP_SEIZE};

/// The two-move mid-run line every resume test drives (press on into the hall, claim the crown for
/// the Red Hand) — each a real landed turn, and NOT ending the session (a returning player resumes
/// mid-run).
fn drive_midrun(host: &mut OfferingHost, id: &SessionId, actor: &DreggIdentity) {
    for arg in [KP_PRESS_ON, KP_CLAIM_RED] {
        let out = host
            .advance(
                "dungeon",
                id,
                Action::new("move", TURN_CHOOSE, arg as i64, true),
                actor.clone(),
            )
            .expect("the session is live");
        assert!(out.landed(), "move {arg} landed a real receipt");
    }
}

fn dungeon_host_with_store(store: &InMemoryResumeStore) -> OfferingHost {
    let mut host = OfferingHost::new().with_resume_store(Box::new(store.clone()));
    host.register("dungeon", "The Warden's Keep", DungeonOffering::new());
    host
}

/// **THE SEAM.** A live session's move-log is recorded (seed + the landed advances) into a durable
/// store; across a simulated RESTART the session reopens by REPLAYING that log — to the IDENTICAL
/// committed-state commitment (non-vacuous: a genesis session commits differently). The state was
/// never serialized; it was re-derived from the inputs through the real executor.
#[test]
fn a_session_survives_restart_by_replaying_its_move_log() {
    let store = InMemoryResumeStore::new();
    let actor = DreggIdentity("web:alice".to_string());

    // ── boot #1: open + play a mid-run line; the move-log is recorded through to the store ──
    let (original_commit, id) = {
        let mut host = dungeon_host_with_store(&store);
        let id = host.open("dungeon").expect("opens");
        drive_midrun(&mut host, &id, &actor);

        // The move-log holds exactly the two landed advances (genesis is implicit in the seed).
        let log = host
            .move_log("dungeon", &id)
            .expect("a live session has a log");
        assert_eq!(log.moves.len(), 2, "two landed advances recorded");
        assert_eq!(log.moves[0].action.arg, KP_PRESS_ON as i64);
        assert_eq!(log.moves[1].action.arg, KP_CLAIM_RED as i64);

        let commit = host
            .commitment("dungeon", &id)
            .expect("a live session commits");
        (commit, id)
        // host #1 is DROPPED here — its in-memory sessions (the `!Send` cell state) are gone.
    };

    // The store outlived the host: it holds the one session's reproducible public input.
    assert_eq!(store.len(), 1, "the store persisted the session's move-log");

    // A genesis session's commitment (on a throwaway host, so its minted id does not collide with
    // the resumed one), to prove the resumed match is NON-VACUOUS: different states commit
    // differently, so the equality below is not trivially always true.
    {
        let mut throwaway = OfferingHost::new();
        throwaway.register("dungeon", "The Warden's Keep", DungeonOffering::new());
        let g = throwaway.open("dungeon").expect("opens");
        assert_ne!(
            throwaway.commitment("dungeon", &g).unwrap(),
            original_commit,
            "a genesis session does NOT match the mid-run commitment (the commitment discriminates state)"
        );
    }

    // ── boot #2 (the RESTART): a fresh host over the SAME store reopens every session by replay ──
    let mut host2 = dungeon_host_with_store(&store);
    let results = host2.resume_all();
    assert_eq!(
        results.len(),
        1,
        "exactly the one persisted session is resumed"
    );
    let (log, outcome) = &results[0];
    let resumed_id = outcome.as_ref().expect("the honest log reopens");
    assert_eq!(resumed_id, &id, "reopened under its recorded id");
    assert_eq!(log.moves.len(), 2);

    // THE ASSERTION: the resumed session is in the IDENTICAL committed state — re-derived from the
    // move-log through the real executor, not restored from a trusted blob.
    assert_eq!(
        host2
            .commitment("dungeon", &id)
            .expect("resumed session is live"),
        original_commit,
        "the session reopened to its byte-identical committed state by replaying its move-log"
    );
    assert!(
        host2.verify("dungeon", &id).unwrap().verified,
        "the resumed session's committed chain re-verifies by replay"
    );

    // The resumed session keeps playing: a further landed advance appends to its adopted log.
    let out = host2
        .advance(
            "dungeon",
            &id,
            Action::new("descend", TURN_CHOOSE, KP_DESCEND as i64, true),
            actor.clone(),
        )
        .expect("the resumed session is live");
    assert!(
        out.landed(),
        "the returning player plays on from the resumed state"
    );
    assert_eq!(
        host2.move_log("dungeon", &id).unwrap().moves.len(),
        3,
        "the resumed log grew by the new landed advance",
    );
}

/// The move-log is a **transmissible** record too: export it from one host and resume it on a
/// brand-new, store-less host (the frontend-held-record path). Reopens to the identical state.
#[test]
fn an_exported_move_log_resumes_on_a_fresh_store_less_host() {
    let actor = DreggIdentity("party".to_string());

    let mut host = OfferingHost::new();
    host.register("dungeon", "The Warden's Keep", DungeonOffering::new());
    let id = host.open("dungeon").expect("opens");
    drive_midrun(&mut host, &id, &actor);
    let original_commit = host.commitment("dungeon", &id).unwrap();
    let log = host.move_log("dungeon", &id).expect("exportable log");

    // A different process entirely — no shared store, just the transmitted log.
    let mut fresh = OfferingHost::new();
    fresh.register("dungeon", "The Warden's Keep", DungeonOffering::new());
    let resumed = fresh.resume(&log).expect("the exported log reopens");
    assert_eq!(resumed, id);
    assert_eq!(
        fresh.commitment("dungeon", &id).unwrap(),
        original_commit,
        "the transmitted move-log reopens to the identical committed state",
    );
}

/// **The tamper tooth.** A move-log with a forged / ineligible advance spliced in is REFUSED by the
/// executor on re-drive — the resume FAILS, and no forged session is left live. A tampered log
/// cannot reopen to a forged state; it fails to reopen at all (fail-closed, the same anti-ghost gate
/// a live illegal move hits).
#[test]
fn a_tampered_move_log_is_refused_on_resume() {
    let actor = DreggIdentity("party".to_string());

    let mut host = OfferingHost::new();
    host.register("dungeon", "The Warden's Keep", DungeonOffering::new());
    let id = host.open("dungeon").expect("opens");
    drive_midrun(&mut host, &id, &actor);
    let honest = host.move_log("dungeon", &id).expect("log");

    // Forge the log: splice an INELIGIBLE advance (an arg that is not a choice on the current
    // ballot) between the two honest moves — a move that never legally landed.
    let mut forged = honest.clone();
    forged.moves.insert(
        1,
        LoggedMove::new(Action::new("forged", TURN_CHOOSE, 99, true), actor.clone()),
    );

    let mut fresh = OfferingHost::new();
    fresh.register("dungeon", "The Warden's Keep", DungeonOffering::new());
    let err = fresh
        .resume(&forged)
        .expect_err("a tampered log must NOT reopen");
    match err {
        ResumeError::Refused { index, .. } => {
            assert_eq!(index, 1, "the executor refused the spliced forged move");
        }
        other => panic!("expected a Refused resume, got {other:?}"),
    }
    // Fail-closed: no session was left live under the forged id.
    assert!(
        !fresh.is_open("dungeon", &id),
        "the partially-resumed session was rolled back — nothing forged is left live",
    );
    assert!(
        fresh.commitment("dungeon", &id).is_none(),
        "no committed state exists for a refused resume",
    );
}

/// A full WINNING line survives restart too (the end-to-end run, not just a mid-run prefix): the
/// four-move clear reopens to the identical won, re-verifiable state.
#[test]
fn a_full_winning_line_survives_restart() {
    let store = InMemoryResumeStore::new();
    let actor = DreggIdentity("party".to_string());

    let (won_commit, id) = {
        let mut host = dungeon_host_with_store(&store);
        let id = host.open("dungeon").expect("opens");
        for arg in [KP_PRESS_ON, KP_CLAIM_RED, KP_DESCEND, KP_SEIZE] {
            assert!(
                host.advance(
                    "dungeon",
                    &id,
                    Action::new("move", TURN_CHOOSE, arg as i64, true),
                    actor.clone(),
                )
                .expect("live")
                .landed()
            );
        }
        let report = host.verify("dungeon", &id).unwrap();
        assert!(
            report.verified && report.turns == 5,
            "the winning line clears + verifies"
        );
        (host.commitment("dungeon", &id).unwrap(), id)
    };

    let mut host2 = dungeon_host_with_store(&store);
    let results = host2.resume_all();
    assert_eq!(results.len(), 1);
    results[0].1.as_ref().expect("the won run reopens");
    assert_eq!(
        host2.commitment("dungeon", &id).unwrap(),
        won_commit,
        "the cleared run reopened to its identical won state",
    );
    assert_eq!(host2.verify("dungeon", &id).unwrap().turns, 5);
}

/// The in-memory store round-trips its records: an open establishes a (seeded) log; landed advances
/// append; `load` and `all` read them back; `forget` drops one.
#[test]
fn the_in_memory_store_round_trips() {
    let store = InMemoryResumeStore::new();
    let key = "dungeon";
    let id = SessionId::new("s1");
    let actor = DreggIdentity("a".to_string());

    assert!(store.is_empty());
    store.record_open(key, &id, &SessionConfig::with_seed(42));
    store.record_landed(key, &id, &Action::new("m", TURN_CHOOSE, 1, true), &actor);
    store.record_landed(key, &id, &Action::new("m", TURN_CHOOSE, 0, true), &actor);

    let loaded = store.load(key, &id).expect("recorded log");
    assert_eq!(loaded.cfg.seed, Some(42), "the seed round-trips");
    assert_eq!(loaded.moves.len(), 2, "both landed advances round-trip");
    assert_eq!(loaded.moves[0].action.arg, 1);
    assert_eq!(store.all().len(), 1);

    store.forget(key, &id);
    assert!(
        store.load(key, &id).is_none() && store.is_empty(),
        "forget drops the log"
    );

    // A move-log is a plain reproducible value (seed + ordered moves) — constructible/inspectable.
    let mut hand = SessionMoveLog::new(key, id, SessionConfig::with_seed(7));
    assert!(hand.is_empty());
    hand.record(Action::new("m", TURN_CHOOSE, 3, true), actor);
    assert_eq!(hand.len(), 1);
}
