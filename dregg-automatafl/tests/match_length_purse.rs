//! **How many turns can a deployed match ever take?** — the world agent's purse against what the
//! world is charged per turn. The falsifier for the two walls that made `/play offering:automatafl`
//! unplayable, and it fails if either comes back.
//!
//! `turn.fee` is two things at once in `dregg-turn`'s executor: the turn's computron LIMIT, and an
//! amount DEBITED IN FULL from the submitting agent at Phase 1 (`executor/execute.rs`, "commit fee
//! + nonce (NEVER rolled back)"), with no refund of the computrons the turn did not use. The
//! embedded agent `AgentRuntime` births carries a fixed 1 000 000-computron endowment
//! (`sdk/src/runtime.rs`, "1M computrons initial balance") and nothing in a game's reach refills
//! it.
//!
//! So a world that declares a FLAT per-turn fee `F` can commit exactly `1_000_000 / F` turns,
//! ever, and then every further move is `InsufficientBalance` mid-match with the board still live.
//! `F` has to cover the WIDEST turn — automatafl's genesis seed writes all 15 registers and all 121
//! board squares — so the widest turn's price is what the narrowest turn pays. Measured, before
//! the fix: 51 play turns, seven rounds.
//!
//! Two changes make the purse bound WORK instead of turn COUNT, and this test needs both:
//!
//!   * `WorldCell::with_metered_turn_fee` — the declared number becomes a CEILING and each turn is
//!     stamped with its own metered price under it, and
//!   * `AutomataflGame::effects_delta` — a play turn writes the fields it CHANGES, not the whole
//!     board back onto itself.
//!
//! Drop either one and this test goes red: without metering, a two-write `select` is still charged
//! for 138 writes; without the delta, a `select` still MAKES 138 writes and metering has nothing to
//! discount.

use dregg_automatafl::AutomataflOffering;
use dregg_automatafl::game::{SELECT, TURN_FEE};
use dreggnet_offerings::{Offering, SessionConfig};

/// The endowment `dregg_sdk::AgentRuntime` births the embedded agent with. Named here so the
/// arithmetic below is legible; if the SDK changes it, this test's COUNT moves and its CLAIM does
/// not.
const AGENT_ENDOWMENT: u64 = 1_000_000;

/// One automatafl round is seven committed turns: two seats × (`select` + `commit`), two
/// `reveal`s, one `resolve`.
const TURNS_PER_ROUND: u64 = 7;

/// A match must outlast the game. The automaton starts dead centre and moves at most one square
/// per resolution, so a win is five rounds away at the theoretical fastest and a contested match
/// is tens of rounds; 60 is a floor chosen to be comfortably past "the crude driver in
/// `surface::tests::the_automaton_can_be_pulled_to_a_goal_and_win` runs 12 rounds", not a
/// prediction of match length.
const ROUNDS_A_MATCH_MUST_SURVIVE: u64 = 60;

/// **The purse buys WORK, not a fixed number of turns.**
///
/// Drives real `select` turns — each moves one register, exactly what the surface's select does —
/// until the world refuses, and reports why. The `select` case's teeth (board `Immutable`,
/// `turn_no`/`winner` `Immutable`, the genesis sentinel frozen) all hold for a selection change,
/// so the only thing that can end this loop is the purse.
#[test]
fn a_match_outlasts_the_game_because_a_cheap_turn_is_charged_cheaply() {
    let offering = AutomataflOffering;
    let session = offering
        .open(SessionConfig::with_seed(7))
        .expect("the world deploys and the genesis seed lands");
    let game = session.game();
    let mut state = game.read_state();

    let mut landed = 0u64;
    let refusal = loop {
        // A REAL selection change: one register moves, so the committed delta is one `SetField`.
        state.sel[0] = if state.sel[0] == 1 { 2 } else { 1 };
        match game.commit_state(SELECT, &state) {
            Ok(_) => landed += 1,
            Err(error) => break error.to_string(),
        }
        assert!(
            landed < 20_000,
            "the loop is meant to end at the purse, not at its own guard"
        );
    };

    assert!(
        refusal.contains("balance") || refusal.contains("Balance"),
        "the wall must be the PURSE (every one of these turns is legal); the executor said: \
         {refusal}"
    );

    let rounds = landed / TURNS_PER_ROUND;
    // Report the measured headroom on SUCCESS too (`--nocapture`), so the number is a reading
    // taken from the deployed world rather than one recomputed from the cost table in a comment.
    println!(
        "match-length headroom: {landed} `select` turns ({rounds} rounds) on a \
         {AGENT_ENDOWMENT}-computron purse, then: {refusal}"
    );
    assert!(
        rounds >= ROUNDS_A_MATCH_MUST_SURVIVE,
        "a match must survive at least {ROUNDS_A_MATCH_MUST_SURVIVE} rounds; this world played \
         {landed} turns ({rounds} rounds) out of a {AGENT_ENDOWMENT}-computron purse before \
         {refusal}"
    );

    // NON-VACUITY, and the whole point of the fix in one line: charged FLAT at the declared
    // ceiling — which is what a world whose every turn rewrites its whole board must declare —
    // this same purse buys `AGENT_ENDOWMENT / TURN_FEE` turns and no more. If `landed` were not
    // far above that, nothing would have been metered and nothing discounted.
    let flat_fee_turns = AGENT_ENDOWMENT / TURN_FEE;
    assert!(
        flat_fee_turns < ROUNDS_A_MATCH_MUST_SURVIVE * TURNS_PER_ROUND,
        "this test only means something while a FLAT fee would be too few turns to finish a \
         match: at {TURN_FEE} computrons flat the purse buys {flat_fee_turns}"
    );
    assert!(
        landed > flat_fee_turns * 10,
        "a cheap turn must be charged cheaply: {landed} turns landed, against {flat_fee_turns} \
         under a flat fee of {TURN_FEE}"
    );
}
