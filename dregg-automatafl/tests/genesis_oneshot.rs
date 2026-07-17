//! THE GENESIS ONE-SHOT — the automatafl write-hatch closed at the root, DRIVEN.
//!
//! The permissive `genesis` case (it must seed the opening board from a blank baseline)
//! carried EMPTY teeth, and `WorldCell::apply_raw` re-dispatches ANY method with no
//! one-shot guard — so a POST-DEPLOY `apply_raw(GENESIS, [SetField(slot, V)])` re-hit the
//! permissive case and committed an arbitrary write to ANY slot, routing around every play
//! tooth. That is the stapleable-slot hole class: a genesis staple on an UNGUARDED slot is
//! a universal write-hatch.
//!
//! The fix makes genesis a `0 → 1` transition on `GENESIS_DONE_EXT_KEY`
//! (`Equals{1} ∧ DeltaEquals{1}`): admissible exactly once (at the opening seed, sentinel
//! still field-zero), jointly UNSATISFIABLE for every later genesis turn regardless of
//! which slot a stapled `SetField` targets — no per-slot dependence. Each play case freezes
//! the sentinel so no move can reset it.
//!
//! DRIVEN here: the legit one-time seed still lands; a normal play turn is unaffected; a
//! post-deploy genesis staple on an unguarded slot is REFUSED; and the CANARY — the same
//! staple against a build with the guard REMOVED COMMITS (the hole reopens), against the
//! real build is REFUSED (the guard restored) — proving the one-shot guard is load-bearing
//! and is what bites, with no per-slot dependence.

use dregg_automatafl::game::{
    AutomataflGame, GENESIS, MatchState, SELECT, index_of, opening_board,
};

/// The opening match state (the `old` value every relational tooth reads) — the same
/// seed `AutomataflOffering::open` commits under genesis.
fn opening_state() -> MatchState {
    let board = opening_board();
    MatchState {
        turn_no: 0,
        phase: 0,
        winner: 0,
        commits: 0,
        reveals: 0,
        commit: [0, 0],
        sel: [0, 0],
        frm: [0, 0],
        to: [0, 0],
        auto: board.auto,
        cells: board.cells.clone(),
    }
}

/// The legit one-time deploy + seed lands (the genesis guard admits the `0 → 1`
/// transition exactly once), and a normal play turn is unaffected by the sentinel freeze.
#[test]
fn legit_seed_lands_and_normal_play_is_unaffected() {
    let game = AutomataflGame::deploy(7).expect("deploy");

    // The opening seed is the one admissible genesis turn.
    game.seed(&opening_state())
        .expect("the opening seed lands under genesis");
    assert_eq!(
        game.read_state(),
        opening_state(),
        "the cell holds the seeded opening"
    );

    // A normal `select` turn (board + turn immutable, sentinel frozen-and-untouched) still
    // lands — the freeze does not block legit play.
    let mut sel = opening_state();
    sel.sel[0] = index_of((1, 1)).unwrap() as u64 + 1;
    game.commit_state(SELECT, &sel)
        .expect("a legal select still lands after the fix");
    assert_eq!(game.read_reg("a_sel"), sel.sel[0], "the select committed");
}

/// The post-deploy genesis staple on an UNGUARDED slot is REFUSED — the one-shot guard,
/// not a per-slot tooth. Two different unguarded targets (a board cell conjuring an illegal
/// particle, a register) are both refused, and nothing commits.
#[test]
fn post_deploy_genesis_staple_is_refused() {
    let game = AutomataflGame::deploy(11).expect("deploy");
    game.seed(&opening_state()).expect("seed");

    // Staple an arbitrary write on a board cell: conjure particle code 7 (illegal under
    // `resolve`'s MemberOf, but genesis carries no per-slot tooth — only the one-shot
    // sentinel can stop it).
    let cell0_before = game.read_cell(0);
    let staple_cell = vec![game.cell_effect(0, 7)];
    assert!(
        game.commit_raw(GENESIS, staple_cell).is_err(),
        "a post-deploy genesis staple on a board cell is REFUSED (the one-shot guard bites)"
    );
    assert_eq!(
        game.read_cell(0),
        cell0_before,
        "the refused staple committed nothing"
    );

    // A different unguarded target — the `winner` register — is refused by the SAME guard.
    let winner_before = game.read_reg("winner");
    let staple_reg = vec![game.reg_effect("winner", 2)];
    assert!(
        game.commit_raw(GENESIS, staple_reg).is_err(),
        "a post-deploy genesis staple on a register is REFUSED — no per-slot dependence"
    );
    assert_eq!(
        game.read_reg("winner"),
        winner_before,
        "the refused staple committed nothing"
    );
}

/// THE CANARY. The SAME post-deploy genesis staple, run against a build with the guard
/// REMOVED, COMMITS (the historical write-hatch reopens) — and against the real build is
/// REFUSED. The only difference is the genesis guard, so the guard is load-bearing and is
/// exactly what bites.
#[test]
fn canary_removing_the_guard_reopens_the_hatch() {
    // Guard REMOVED (`deploy_hatch_reopened`): the permissive genesis re-dispatches and the
    // staple COMMITS an arbitrary write to an unguarded slot.
    let reopened = AutomataflGame::deploy_hatch_reopened(23).expect("deploy (hatch reopened)");
    reopened.seed(&opening_state()).expect("seed");
    reopened
        .commit_raw(GENESIS, vec![reopened.cell_effect(0, 7)])
        .expect("with the guard removed, the post-deploy genesis staple COMMITS (hole reopened)");
    assert_eq!(
        reopened.read_cell(0),
        7,
        "the reopened hatch wrote a conjured particle"
    );

    // Guard RESTORED (`deploy`, the real build): the identical staple is REFUSED.
    let guarded = AutomataflGame::deploy(23).expect("deploy");
    guarded.seed(&opening_state()).expect("seed");
    assert!(
        guarded
            .commit_raw(GENESIS, vec![guarded.cell_effect(0, 7)])
            .is_err(),
        "with the guard restored, the identical staple is REFUSED — the guard is load-bearing"
    );
    assert_eq!(
        guarded.read_cell(0),
        opening_state().cells[0],
        "nothing committed under the guard"
    );
}
