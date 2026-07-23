//! SLOW (`--ignored`) — **THE HARD GATE, DRIVEN END-TO-END**: a real PLAYED match of each
//! portfolio game
//!
//!   PLAYS (fast) → FOLDS (the deployed recursive fold, minutes-to-hours, on a BACKGROUND
//!   worker) → SUBMITS the proof → the proof-carrying board VERIFIES it in O(1) and RANKS it,
//!   **storing no moves**.
//!
//! The multiway-tug match ranks with the HAND NEVER REVEALED (each play is a Poseidon2
//! membership leaf; the card ids are not in the proof). The automatafl match ranks with the
//! MOVES NEVER POSTED (each turn is the committed D1 board-transition leaf).
//!
//! Run:
//!   cargo test -p dreggnet-game-board --test end_to_end -- --ignored --nocapture
//!
//! Each lane BAKES its folded artifact to `tests/fixtures/<game>_match_proof.bin` (+ the anchor
//! hex), so the fast board lane then runs against the game's OWN match proof.

mod support;

use dregg_automatafl::reference::{ATT, AUTO, Board, VAC};
use dregg_circuit_prove::ivc_turn_chain::WholeChainProofBytes;
use dregg_lightclient::verify_history_bytes;
use dreggnet_game_board::{
    AutomataflMatch, Game, GameBoard, MatchProof, ProvingService, RejectReason, SubmitError,
    TugMatch, TugWin, match_anchor, stark_prover,
};

use support::{fixture_paths, hex32};

/// Bake the folded artifact so the fast board lane can drive the GAME's own proof.
fn bake(proof: &MatchProof) {
    let (bin, hex) = fixture_paths(proof.game);
    std::fs::create_dir_all(bin.parent().expect("fixtures dir")).expect("mkdir fixtures");
    std::fs::write(&bin, &proof.proof_bytes).expect("write the proof envelope");
    std::fs::write(&hex, hex32(&proof.vk.0)).expect("write the anchor");
    eprintln!(
        "BAKED {} ({} bytes) + anchor {}",
        bin.display(),
        proof.proof_bytes.len(),
        hex32(&proof.vk.0)
    );
}

/// Drive the whole async pipeline for a played match: enqueue the leaves on the REAL prover
/// (the background fold), submit the finished proof to the game's board, assert the O(1) accept
/// + rank + NO MOVES, then show the forgery bite on THIS match's own artifact.
fn play_prove_submit(game: Game, leaves: Vec<dreggnet_game_board::LeafBundle>) -> MatchProof {
    let n_leaves = leaves.len();

    // ── PROVE (slow, background). The play is already over. ──
    let service = ProvingService::spawn(stark_prover());
    let job = service.enqueue(game, leaves);
    eprintln!("{game}: enqueued a {n_leaves}-turn match; folding in the background…");
    let proof = service
        .wait(job)
        .unwrap_or_else(|e| panic!("{game}: the honest match must fold to ONE proof: {e}"));
    assert_eq!(
        proof.turns(),
        n_leaves,
        "the attested history covers every played turn"
    );
    bake(&proof);

    // ── The board OPENS against the game's anchor (vk + genesis + the WIN root). ──
    let mut board = GameBoard::new();
    board.open(game, match_anchor(&proof));

    // ── SUBMIT (the proof; never the moves) → the board verifies in O(1) and RANKS. ──
    let accepted = board
        .submit(game, "ada", &proof)
        .unwrap_or_else(|e| panic!("{game}: the board must accept the honest fold: {e}"));
    assert_eq!(accepted.rank, 1);
    assert_eq!(accepted.turns, proof.turns());

    let lb = board.leaderboard(game);
    assert_eq!(lb.len(), 1);
    assert!(lb[0].is_proof_backed());
    assert!(
        !lb[0].has_moves() && lb[0].playthrough().is_none(),
        "THE PRIVATE-STRATEGY PROPERTY: the ranked entry stores NO moves"
    );
    assert!(board.stores_no_moves(game));
    assert_eq!(
        board
            .reverify(game, &accepted.completion_id)
            .expect("the entry re-verifies via the O(1) light client"),
        proof.turns()
    );

    // ── NON-VACUOUS: a relabeled final root on THIS match's own proof is REJECTED. ──
    let mut env = WholeChainProofBytes::from_postcard(&proof.proof_bytes).expect("envelope");
    env.final_root[0] = env.final_root[0].wrapping_add(1);
    let v = board.submit_bytes(game, "mallory", env.to_postcard(), proof.turns());
    assert!(
        matches!(v, Err(SubmitError::Refused(RejectReason::ProofRejected(_)))),
        "{game}: a forged final root must be REJECTED; got {v:?}"
    );
    assert_eq!(
        board.leaderboard(game).len(),
        1,
        "the forgery added nothing"
    );

    // The shipped envelope is exactly what the board verified — no side channel.
    verify_history_bytes(&proof.proof_bytes, &proof.vk).expect("the shipped envelope verifies");

    eprintln!(
        "{game} END-TO-END: PLAY → FOLD({n_leaves} turns) → SUBMIT → O(1) ACCEPT, RANK #{}, \
         0 moves stored; a forged root REJECTED.",
        accepted.rank
    );
    proof
}

/// THE HARD GATE (multiway-tug): a real PRIVATE match — two membership-proven plays (each under
/// its own committed hand root) + the terminal win turn — folds to ONE proof and RANKS on the
/// proof-carrying board with **the hand never revealed**.
#[test]
#[ignore = "SLOW: the real deployed recursion fold over a played match (minutes-to-hours); run with --ignored"]
fn multiway_tug_match_plays_folds_submits_and_ranks() {
    let m = TugMatch {
        hand: vec![
            (0, 1001),
            (1, 1002),
            (3, 1003),
            (7, 1004),
            (12, 1005),
            (18, 1006),
        ],
        plays: vec![0, 1],
        win: Some(TugWin {
            charm: 13,
            winner: 1,
        }),
    };
    let leaves = m.leaves().expect("the played match lowers to leaves");
    assert_eq!(leaves.len(), 3, "2 plays + the win turn");
    // The hand is not in what leaves the player: only blinded leaves + roots (+ the win output).
    for l in leaves.iter().take(2) {
        for &card in &m.plays {
            assert!(
                !l.public_inputs
                    .contains(&dregg_circuit::field::BabyBear::from_u64(card)),
                "no card id is in the public inputs"
            );
        }
    }
    let proof = play_prove_submit(Game::MultiwayTug, leaves);
    eprintln!(
        "MULTIWAY-TUG: ranked on the proof-carrying board from a {}-turn fold — the hand \
         (6 cards, their nonces, the unplayed 4) was NEVER revealed.",
        proof.turns()
    );
}

/// THE HARD GATE (automatafl): a real played match — the D1-shaped chain of automaton-step board
/// transitions — folds to ONE proof and RANKS on the proof-carrying board with **the moves never
/// posted**. (Named residual: the full match beyond D1's shape — the D2/D3 player-move + conflict
/// stages exist in `dregg-automatafl` and lower the same way.)
#[test]
#[ignore = "SLOW: the real deployed recursion fold over the D1 board-transition chain; run with --ignored"]
fn automatafl_match_plays_folds_submits_and_ranks() {
    let n = 5usize;
    let mut cells = vec![VAC; n * n];
    cells[4 * n + 2] = ATT;
    cells[2 * n + 2] = AUTO;
    let start = Board {
        n,
        cells,
        auto: (2, 2),
        col_rule: true,
    };
    let m = AutomataflMatch::automaton_only(start, 2);
    let leaves = m.leaves().expect("the played match lowers to D1 leaves");
    assert_eq!(leaves.len(), 2);
    let proof = play_prove_submit(Game::Automatafl, leaves);
    eprintln!(
        "AUTOMATAFL: ranked on the proof-carrying board from a {}-turn fold — the boards/moves \
         were NEVER posted.",
        proof.turns()
    );
}

/// The two games rank on ONE proof-carrying registry, each against its own anchor — and neither
/// board accepts the other's proof. (Runs both folds; the slowest gate.)
#[test]
#[ignore = "SLOW: folds BOTH games' matches; run with --ignored"]
fn both_games_rank_on_the_same_proof_carrying_registry() {
    let tug = TugMatch {
        hand: vec![(0, 1001), (1, 1002), (3, 1003), (7, 1004)],
        plays: vec![0, 1],
        win: None,
    }
    .leaves()
    .expect("tug lowers");
    let n = 5usize;
    let mut cells = vec![VAC; n * n];
    cells[4 * n + 2] = ATT;
    cells[2 * n + 2] = AUTO;
    let afl = AutomataflMatch::automaton_only(
        Board {
            n,
            cells,
            auto: (2, 2),
            col_rule: true,
        },
        2,
    )
    .leaves()
    .expect("automatafl lowers");

    let service = ProvingService::spawn(stark_prover());
    let j1 = service.enqueue(Game::MultiwayTug, tug);
    let j2 = service.enqueue(Game::Automatafl, afl);
    let p1 = service.wait(j1).expect("the tug match folds");
    let p2 = service.wait(j2).expect("the automatafl match folds");

    let mut board = GameBoard::new();
    board.open(Game::MultiwayTug, match_anchor(&p1));
    board.open(Game::Automatafl, match_anchor(&p2));

    assert_eq!(
        board
            .submit(Game::MultiwayTug, "ada", &p1)
            .expect("tug ranks")
            .rank,
        1
    );
    assert_eq!(
        board
            .submit(Game::Automatafl, "bob", &p2)
            .expect("automatafl ranks")
            .rank,
        1
    );
    assert!(board.stores_no_moves(Game::MultiwayTug));
    assert!(board.stores_no_moves(Game::Automatafl));

    // Cross-game: each board refuses the other's (perfectly valid) proof — the anchor binds.
    assert!(matches!(
        board.submit(Game::Automatafl, "mallory", &p1),
        Err(SubmitError::Refused(
            RejectReason::GenesisMismatch | RejectReason::WinNotProven
        ))
    ));
    assert!(matches!(
        board.submit(Game::MultiwayTug, "mallory", &p2),
        Err(SubmitError::Refused(
            RejectReason::GenesisMismatch | RejectReason::WinNotProven
        ))
    ));
    eprintln!("BOTH GAMES ranked on one proof-carrying registry; cross-game proofs REFUSED.");
}
