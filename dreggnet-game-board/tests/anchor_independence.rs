//! **The crown board's trust anchor is board CONFIG, pinned ONCE — never minted from a
//! submitted proof.**
//!
//! ## The bug this file exists for
//! The crown wiring opened a game's board per submission with `open(game, match_anchor(&proof))`,
//! deriving the trust anchor (VK + genesis + WIN roots) from the SUBMITTED proof. That made
//! `verify_proof_completion`'s genesis / win checks self-comparisons (a first fold is tautological
//! — it defines the very roots it is then checked against), and because the content [`UniverseId`]
//! is a per-game constant published `or_insert`, the FIRST fold's anchor was frozen forever: every
//! later distinct winner hit `GenesisMismatch` / `WinNotProven` and was refused. A first (even
//! malicious) submitter captured the board.
//!
//! ## The fix these tests lock in
//! The anchor is pinned ONCE per game from a submission-independent source and is IMMUTABLE
//! ([`GameBoard::ensure_open`]). A later caller — a submission's `match_anchor(&proof)`, an
//! attacker's chosen roots — can neither define nor replace it, and multiple honest winners of the
//! SAME anchored challenge all rank (the board does not cap at one match).
//!
//! No proving happens here (the fold is minutes-to-hours). The proof driven is a REAL folded
//! artifact — see `support::real_proof`.

mod support;

use dregg_circuit::field::BabyBear;
use dregg_lightclient::verify_history_bytes;
use dreggnet_game_board::{Game, GameBoard, MatchProof, ProofAnchor, match_anchor};

use support::real_proof;

/// The shippable `MatchProof` a player's prover would produce for `game`, from a real folded
/// artifact (the fold itself is the slow lane's job).
fn shipped(game: Game) -> MatchProof {
    let p = real_proof(game);
    let attested = verify_history_bytes(&p.bytes, &p.vk)
        .expect("the fixture must be a REAL proof the light client accepts");
    MatchProof {
        game,
        proof_bytes: p.bytes,
        attested,
        vk: p.vk,
    }
}

fn bump(mut a: [BabyBear; 8]) -> [BabyBear; 8] {
    a[0] = a[0] + BabyBear::ONE;
    a
}

/// **THE ANTI-CAPTURE TEST.** The board's anchor is pinned ONCE (from a submission-independent
/// canonical reference) and is immutable: an attempt to re-anchor it — exactly what the buggy
/// per-submission `open(game, match_anchor(&proof))` did on every fold — leaves the pinned genesis
/// / WIN roots untouched. So the anchor is genesis-derived, NOT proof-derived.
#[test]
fn the_board_anchor_is_pinned_once_and_a_submission_cannot_recapture_it() {
    let game = Game::MultiwayTug;
    let proof = shipped(game);

    // The OPERATOR's committed canonical anchor for the game's seeded challenge (VK + genesis +
    // WIN roots). In this fixture the canonical reference IS this honest winning fold; in a
    // deployment it is a baked reference the board holds as config, never a player's submission.
    let canonical = match_anchor(&proof);

    let mut board = GameBoard::new();
    let u1 = board.ensure_open(game, canonical.clone());
    assert!(
        board.is_open(game),
        "the board is open once the anchor is pinned"
    );

    // A submitter (the OLD crown code did this per fold) tries to make the board adopt an anchor
    // derived from THEIR proof — here a bumped genesis + win. `ensure_open` REFUSES to re-anchor.
    let attacker = ProofAnchor::new(
        proof.vk,
        bump(proof.attested.genesis_root),
        bump(proof.attested.final_root),
    );
    let u2 = board.ensure_open(game, attacker.clone());

    assert_eq!(
        u1, u2,
        "the board universe is stable across a re-open attempt"
    );
    let pinned = board.anchor(game).expect("the pinned anchor is readable");
    assert_eq!(
        pinned.genesis_root, canonical.genesis_root,
        "the GENESIS anchor is IMMUTABLE — a later submission cannot recapture it"
    );
    assert_eq!(
        pinned.win_root, canonical.win_root,
        "the WIN anchor is IMMUTABLE — a later submission cannot redefine the win"
    );
    assert_ne!(
        pinned.genesis_root, attacker.genesis_root,
        "the attacker's proof-derived genesis was NOT adopted"
    );

    // The honest winner is ACCEPTED under the canonical anchor…
    let w1 = board
        .submit(game, "ada", &proof)
        .expect("the honest canonical winner is accepted under the pinned anchor");
    assert_eq!(w1.rank, 1, "the first winner ranks first");

    // …and a SECOND winner of the SAME anchored challenge is ALSO accepted — the board does not
    // cap at one match, and later winners are not refused as they were once the first submission
    // captured the anchor. Both rank under ONE anchored universe.
    let w2 = board
        .submit(game, "bruno", &proof)
        .expect("a second winner under the SAME pinned anchor is ACCEPTED, not refused");
    assert_eq!(
        w2.rank, 2,
        "the second winner ranks behind the first (equal turns, stable order)"
    );
    assert_eq!(
        board.leaderboard(game).len(),
        2,
        "both winners rank under one anchored universe"
    );

    // Both entries independently re-verify against the pinned anchor (O(1), never a replay).
    for id in [w1.completion_id, w2.completion_id] {
        assert_eq!(
            board
                .reverify(game, &id)
                .expect("a ranked entry re-verifies via the O(1) light client"),
            proof.turns()
        );
    }
}

/// The anchor binding stays NON-VACUOUS under the pin-once path: a proof that does not attest the
/// pinned genesis is refused. (The bug made this check a self-comparison; here the pinned anchor is
/// independent of the submission, so the genesis binding genuinely bites.)
#[test]
fn a_proof_that_misses_the_pinned_genesis_is_refused() {
    let game = Game::MultiwayTug;
    let proof = shipped(game);

    // Pin an anchor whose genesis is NOT the proof's (an independent, committed reference).
    let independent = ProofAnchor::new(
        proof.vk,
        bump(proof.attested.genesis_root),
        proof.attested.final_root,
    );
    let mut board = GameBoard::new();
    board.ensure_open(game, independent);

    // The honest proof does not start at the pinned genesis → refused (not silently self-accepted).
    let verdict = board.submit(game, "ada", &proof);
    assert!(
        verdict.is_err(),
        "a proof that does not attest the pinned genesis must be REFUSED; got {verdict:?}"
    );
    assert!(
        board.leaderboard(game).is_empty(),
        "nothing ranked against the independent anchor"
    );
}
