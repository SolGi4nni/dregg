//! The no-cheat leaderboard, DRIVEN end-to-end (not named):
//!
//! * a universe is published and a REAL winning playthrough is accepted + ranked;
//! * a FORGED completion (edited moves that no longer reach the win) is REJECTED on
//!   replay — non-vacuous (the exact rejection is asserted);
//! * an INCOMPLETE completion (never reaches the win) is REJECTED;
//! * a TAMPERED RESULT (a lied turn count on an otherwise-honest win) is REJECTED;
//! * two real completions rank by turns;
//! * an accepted entry re-verifies INDEPENDENTLY (from a freshly reconstructed
//!   universe + the entry's own recorded playthrough);
//! * a procgen (daily) universe is winnable + content-addressed by its committed seed.

use dungeon_on_dregg::{
    CH_CLAIM, CH_DESCEND, CH_LEAVE_LANTERN, CH_RETREAT, CH_TAKE_LANTERN, DUNGEON,
};
use ugc_dregg::{
    Completion, Provenance, Registry, RejectReason, Universe, WinCondition, record_playthrough,
    verify_completion,
};

/// The built-in salt-shore dungeon as a published universe. Win = the hoard seized
/// (`gold == 500`) and the scene ENDED. Minimal winning path is 3 moves.
fn salt_shore() -> Universe {
    Universe::authored(
        "The Salt Shore Descent",
        "attested-dm-salvage",
        DUNGEON,
        WinCondition::ended_with(&[("gold", 500)]),
    )
    .expect("the salt-shore dungeon is a valid, deployable universe")
}

/// The minimal winning move sequence: take the lantern, descend the gate, claim.
const WIN_MOVES: [usize; 3] = [CH_TAKE_LANTERN, CH_DESCEND, CH_CLAIM];

#[test]
fn publish_is_content_addressed_and_idempotent() {
    let mut reg = Registry::new();
    let u1 = salt_shore();
    let u2 = salt_shore();
    // Same content ⇒ same id.
    assert_eq!(u1.id(), u2.id(), "the same universe has the same id");

    let id = reg.publish(u1);
    let id2 = reg.publish(u2); // idempotent re-publish
    assert_eq!(id, id2);
    assert_eq!(reg.universes().count(), 1, "re-publish did not duplicate");
    assert_eq!(reg.universe(id).unwrap().name(), "The Salt Shore Descent");
}

#[test]
fn a_real_winning_playthrough_is_accepted_and_ranked() {
    let mut reg = Registry::new();
    let u = salt_shore();
    let id = reg.publish(u.clone());

    let play = record_playthrough(&u, &WIN_MOVES).expect("the honest win drives cleanly");
    let accepted = reg
        .submit(Completion {
            universe: id,
            player: "ada".into(),
            play,
            claimed_turns: 3,
        })
        .expect("a real, complete win is accepted");
    assert_eq!(accepted.turns, 3);
    assert_eq!(accepted.rank, 1);

    let board = reg.leaderboard(id);
    assert_eq!(board.len(), 1);
    assert_eq!(board[0].player, "ada");
    assert_eq!(board[0].turns, 3);

    // The accepted entry re-verifies independently.
    reg.reverify_entry(id, &accepted.completion_id)
        .expect("the accepted entry re-verifies independently");
}

#[test]
fn a_forged_completion_is_rejected_on_replay() {
    let mut reg = Registry::new();
    let u = salt_shore();
    let id = reg.publish(u.clone());

    // An HONEST win, then FORGE it: retcon the first move to "leave the lantern".
    // On replay the gated descent (step 1) is refused by the real executor, or the
    // reproduced state diverges — either way the forged record fails.
    let mut forged = record_playthrough(&u, &WIN_MOVES).expect("record the honest win");
    forged.steps[0].choice_index = CH_LEAVE_LANTERN;

    let out = reg.submit(Completion {
        universe: id,
        player: "mallory".into(),
        play: forged,
        claimed_turns: 3,
    });
    assert!(
        matches!(out, Err(RejectReason::FailedVerification(_))),
        "a forged (edited-moves) completion must be REJECTED on replay, got {out:?}"
    );
    // Non-vacuous: nothing was added to the board.
    assert!(reg.leaderboard(id).is_empty(), "no cheat entry landed");
}

#[test]
fn an_incomplete_completion_is_rejected() {
    let mut reg = Registry::new();
    let u = salt_shore();
    let id = reg.publish(u.clone());

    // A REAL but INCOMPLETE playthrough: take the lantern and stop — never claims the
    // hoard, so the scene never ends. It replays fine but does NOT reach the win.
    let partial = record_playthrough(&u, &[CH_TAKE_LANTERN]).expect("a partial real play");
    let out = reg.submit(Completion {
        universe: id,
        player: "quinn".into(),
        play: partial,
        claimed_turns: 1,
    });
    assert!(
        matches!(out, Err(RejectReason::DidNotWin)),
        "an incomplete playthrough must be REJECTED (did not win), got {out:?}"
    );
    assert!(reg.leaderboard(id).is_empty());
}

#[test]
fn a_tampered_result_is_rejected() {
    let mut reg = Registry::new();
    let u = salt_shore();
    let id = reg.publish(u.clone());

    // An HONEST 3-move win, but the submitter LIES that it took 1 turn.
    let play = record_playthrough(&u, &WIN_MOVES).expect("honest win");
    let out = reg.submit(Completion {
        universe: id,
        player: "liar".into(),
        play,
        claimed_turns: 1, // the real count is 3
    });
    assert!(
        matches!(
            out,
            Err(RejectReason::ResultMismatch {
                claimed: 1,
                actual: 3
            })
        ),
        "a tampered turn count must be REJECTED, got {out:?}"
    );
    assert!(reg.leaderboard(id).is_empty());
}

#[test]
fn two_real_completions_rank_by_turns() {
    let mut reg = Registry::new();
    let u = salt_shore();
    let id = reg.publish(u.clone());

    // ada: the minimal 3-move win.
    let ada = record_playthrough(&u, &WIN_MOVES).expect("ada's fast win");
    // bran: a real win with a detour (take, retreat to shore, take again, descend, claim) = 5 moves.
    let bran_moves = [
        CH_TAKE_LANTERN,
        CH_RETREAT,
        CH_TAKE_LANTERN,
        CH_DESCEND,
        CH_CLAIM,
    ];
    let bran = record_playthrough(&u, &bran_moves).expect("bran's slower but real win");

    let a = reg
        .submit(Completion {
            universe: id,
            player: "ada".into(),
            play: ada,
            claimed_turns: 3,
        })
        .expect("ada accepted");
    let b = reg
        .submit(Completion {
            universe: id,
            player: "bran".into(),
            play: bran,
            claimed_turns: 5,
        })
        .expect("bran accepted");

    assert_eq!(a.turns, 3);
    assert_eq!(b.turns, 5);

    let board = reg.leaderboard(id);
    assert_eq!(board.len(), 2);
    assert_eq!(board[0].player, "ada", "fewer turns ranks first");
    assert_eq!(board[0].turns, 3);
    assert_eq!(board[1].player, "bran");
    assert_eq!(board[1].turns, 5);

    // Both entries re-verify independently.
    for e in &board {
        reg.reverify_entry(id, &e.completion_id)
            .expect("every ranked entry re-verifies independently");
    }
}

#[test]
fn an_entry_reverifies_against_a_freshly_reconstructed_universe() {
    // The stranger's re-verification: reconstruct the universe from its PUBLIC
    // definition (name + author + source) — a fresh `Universe` value, no shared state
    // with the registry — and re-verify the entry's recorded playthrough against it.
    let mut reg = Registry::new();
    let u = salt_shore();
    let id = reg.publish(u.clone());
    let play = record_playthrough(&u, &WIN_MOVES).expect("honest win");
    let accepted = reg
        .submit(Completion {
            universe: id,
            player: "ada".into(),
            play,
            claimed_turns: 3,
        })
        .expect("accepted");

    let entry = reg
        .leaderboard(id)
        .into_iter()
        .find(|e| e.completion_id == accepted.completion_id)
        .expect("entry present");

    // A completely independent universe object (a stranger rebuilding it from source).
    let independent = salt_shore();
    assert_eq!(
        independent.id(),
        id,
        "the stranger derives the same universe id"
    );
    let independent_completion = Completion {
        universe: id,
        player: entry.player.clone(),
        play: entry.playthrough().clone(),
        claimed_turns: entry.turns,
    };
    let turns = verify_completion(&independent, &independent_completion)
        .expect("anyone can independently re-verify a leaderboard entry");
    assert_eq!(turns, 3);
}

#[test]
fn a_procgen_universe_is_winnable_and_seed_addressed() {
    // A committed epoch value → a fair daily universe everyone re-derives identically.
    let epoch = [0x5eu8; 32];
    let u = Universe::daily("procgen-daily", &epoch).expect("the daily universe publishes");
    assert!(matches!(u.provenance(), Provenance::Procgen { .. }));
    // Content-addressed by the committed seed: it regenerates byte-for-byte.
    assert!(
        u.regenerates_from_seed(),
        "the world regenerates from its committed seed"
    );

    // The same epoch derives the same universe id (content address is stable).
    let u2 = Universe::daily("procgen-daily", &epoch).expect("re-derive");
    assert_eq!(u.id(), u2.id());

    // It is genuinely winnable: walk the generated linear dungeon to the hoard. The
    // gate is a real executor tooth — the winning path must hold the key. We discover
    // the move sequence by taking the key at room0, pressing onward through the chain,
    // descending the gate, and seizing the hoard.
    let moves = winning_moves_for(&u);
    let mut reg = Registry::new();
    let id = reg.publish(u.clone());
    let play = record_playthrough(&u, &moves).expect("the generated dungeon is winnable");
    let accepted = reg
        .submit(Completion {
            universe: id,
            player: "explorer".into(),
            play,
            claimed_turns: moves.len(),
        })
        .expect("a real win of the daily universe is accepted");
    assert_eq!(accepted.rank, 1);
    reg.reverify_entry(id, &accepted.completion_id)
        .expect("the daily-universe entry re-verifies independently");

    // And a cheat on the daily universe is refused too: skip taking the key (choice 1
    // at room0), then try the gated descent — refused on replay.
    let mut cheat_moves = moves.clone();
    cheat_moves[0] = 1; // "press on empty-handed" instead of taking the key
    let cheat = record_playthrough(&u, &cheat_moves);
    // The forged play either fails to record (executor refuses the gated descent while
    // driving) or is rejected on submit. Both are a real no-cheat refusal.
    match cheat {
        Err(_) => { /* the executor refused the keyless descent while recording */ }
        Ok(play) => {
            let out = reg.submit(Completion {
                universe: id,
                player: "cheater".into(),
                play,
                claimed_turns: cheat_moves.len(),
            });
            assert!(
                matches!(
                    out,
                    Err(RejectReason::FailedVerification(_)) | Err(RejectReason::DidNotWin)
                ),
                "a keyless run of the daily universe must be rejected, got {out:?}"
            );
        }
    }
}

/// Derive the winning move sequence for a generated linear dungeon: at room0 take the
/// key (choice 0), then "press onward" (choice 0) through the middle rooms, descend
/// the gate (choice 0), and seize the hoard (choice 0). Every choice on the winning
/// path is index 0, so the sequence is `[0; room_count]` — one move per room.
fn winning_moves_for(u: &Universe) -> Vec<usize> {
    // The generated dungeon has one winning move per room (room0 take-key, each middle
    // room press-onward, the gate descend, the last room seize). Count the rooms from
    // the source's `=== roomN` markers.
    let rooms = u.source().matches("=== room").count();
    vec![0usize; rooms]
}
