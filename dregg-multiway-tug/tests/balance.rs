//! # The measured balance of a round, AFTER I-cut-you-choose was restored AND the terminal rule
//! reached the played game.
//!
//! The pre-change numbers were measured on the SCRIPTED engine (hardcoded action order,
//! `pick_highest` choosing the cards, no response step at all): **whoever took the round's last
//! action won ~57% of decided rounds** (alternating order 40.6/54.5; the mirrored "snake" order
//! 55.5/39.6 — the edge followed the last action, so no re-ordering of a single round fixed it).
//!
//! What changed structurally, and why the number can move at all: actions still alternate
//! A,B,A,B, so seat B always takes the last ACTION. But a round's last **turn** is a RESPONSE
//! whenever B's fourth action is an offer — and whether it is, is B's own choice. So "who moves
//! last" stopped being a property of the schedule and became a decision, which is exactly the
//! thing the old engine could not express.
//!
//! Both seats run the SAME policy here, so anything left is structural, not agent strength.
//! `TUG_BALANCE_ROUNDS` overrides the round count (the checked-in default is small so a normal
//! `cargo test` stays fast; the figures below were taken at 1500).
//!
//! # ⚑ THE DRAW RATE, THROUGH THE PATH A PLAYER ACTUALLY HITS
//!
//! This file used to carry a THIRD copy of the terminal rule — a local `adjudicated()` that
//! mirrored Lean's `roundWinner` so the fixed number could be *reported* beside the shipped one.
//! That was the shape of the whole wound: the fix existed, proven, in three places that were not
//! the game. `adjudicated()` is deleted. There is exactly one column now, and it is the played
//! one: `Engine::score` calls `@[export] dregg_multiway_tug_rules`, and the committed `winner`
//! goes through the deployed clause teeth.
//!
//! ⚑ MEASURED 2026-07-25, n=200, both seats maximin, THROUGH THE PLAYED PATH
//! (`cargo test -p dregg-multiway-tug --test balance`, 0.63s):
//!
//! ```text
//!                       BEFORE (`winner_of`)   NOW (Lean `roundWinner`, PLAYED)
//!   draws                     78.5%                    8.5%   (17/200)
//!   seat A / seat B        55.0 / 45.0              53.6 / 46.4
//!   LAST-TURN seat wins       77.6%                   62.3%
//!
//!   which clause decided (the deployed method the turn commits under):
//!     absolute bars  (score_charm_*, score_rows_*)   23.5%   <- ALL the old gate could commit
//!     tie-breaks     (score_lead_*, score_rowlead_*) 68.0%   <- ALL of it the old gate REFUSED
//!     dead heat      (score_draw)                     8.5%
//! ```
//!
//! Read the clause histogram, not just the draw rate: **68% of played rounds are decided by a
//! clause the previous deployed gate refused to admit**. The draw rate falling 78.5% -> 8.5% is
//! that same fact seen from the other side. (Independently, over ALL 2187 control-splits of the
//! seven rows the tie-break clauses decide 54.5% — the play-induced distribution leans on them
//! even harder than the uniform one.)
//!
//! The test ASSERTS the repair rather than printing it: a draw rate anywhere near the old bar's
//! is a failure, because a draw is now an EXACT dead heat on both charm and rows
//! (`roundWinner_draw_iff`) rather than "nobody cleared 11".
//!
//! Second finding, independent of the draw rate and NOT fixed here: **restoring I-cut-you-choose
//! made the last-mover edge LARGER, ~57% -> 62.3% measured**, because the final act of a round is a free
//! pick of the better half, so whoever answers last is handed value. 56.7% of rounds end on a
//! response, and a response after seat B's fourth action belongs to seat A. The honest port is
//! Hanamikoji's own — a multi-round match with an alternating opener — which is a match-state
//! change beyond this lane. Caveat, stated rather than buried: the ~57% baseline was taken with
//! greedy agents on the scripted engine and this with maximin agents on the new one, so the two
//! are not a controlled comparison; the DIRECTION is robust (a last free pick cannot be worth less
//! than zero), the exact delta is not.

use dregg_multiway_tug::reference::{Decision, Engine, INFLUENCE, N_GUILDS, Player, Projection};
use dregg_multiway_tug::rules;

fn rounds() -> u64 {
    std::env::var("TUG_BALANCE_ROUNDS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(200)
}

/// Charm lead from `seat`'s point of view, read off the committed placement counts.
fn board_value(proj: &Projection, seat: Player) -> i64 {
    let (mut me, mut them) = (0i64, 0i64);
    for g in 0..N_GUILDS {
        let a = proj.score[g][seat.idx()];
        let b = proj.score[g][seat.other().idx()];
        if a > b {
            me += INFLUENCE[g] as i64;
        } else if b > a {
            them += INFLUENCE[g] as i64;
        }
    }
    me - them
}

/// A genuine maximin agent: when CUTTING it assumes the opponent takes the half that is best
/// for them (the cake-cutting assumption), and when RESPONDING it takes the better half. This
/// is the cheapest policy that actually engages the restored dilemma.
fn maximin(e: &Engine, seat: Player) -> Decision {
    let opts = e.legal_decisions();
    assert!(
        !opts.is_empty(),
        "the seat to move always has a legal decision"
    );
    let mut best = opts[0];
    let mut best_v = i64::MIN;
    for d in &opts {
        let mut c = e.clone();
        if c.apply(seat, *d).is_err() {
            continue;
        }
        let v = match c.pending_offer() {
            // We just cut. Score the WORST half the opponent can leave us.
            Some(off) => {
                let mut worst = i64::MAX;
                for pick in 0..off.picks() {
                    let mut c2 = c.clone();
                    if c2
                        .apply(off.responder(), Decision::Respond { pick })
                        .is_ok()
                    {
                        worst = worst.min(board_value(&c2.projection(), seat));
                    }
                }
                worst
            }
            None => board_value(&c.projection(), seat),
        };
        if v > best_v {
            best_v = v;
            best = *d;
        }
    }
    best
}

struct Tally {
    decided: u64,
    draws: u64,
    wins: [u64; 2],
    /// Decided rounds in which the seat that took the FINAL turn won.
    last_turn_wins: u64,
    /// Rounds whose final turn was a RESPONSE rather than an action.
    ended_on_response: u64,
}

/// Play one round to completion under maximin and take the verdict the PLAYED path gives —
/// `Engine::score`, which is `@[export] dregg_multiway_tug_rules` over the proven `roundWinner`.
/// Returns `(winner, deciding clause, last seat to move, whether the last turn was a response)`.
fn play(seed: u64) -> (Option<Player>, u8, Player, bool) {
    let mut e = Engine::new(seed);
    let mut last_seat = Player::A;
    let mut last_was_response = false;
    while !e.round_complete() {
        let seat = e.current_player();
        let d = maximin(&e, seat);
        last_was_response = matches!(d, Decision::Respond { .. });
        e.apply(seat, d)
            .expect("the policy only plays legal decisions");
        last_seat = seat;
    }
    let winner = e
        .score()
        .expect("the Lean rules oracle adjudicates the round");
    (winner, e.win_branch(), last_seat, last_was_response)
}

#[test]
fn measured_balance_after_i_cut_you_choose() {
    assert!(
        rules::available(),
        "the multiway-tug rules oracle is absent — there is no Rust twin to fall back on, so this \
         measurement cannot be taken (link libdregg_lean.a / rebuild dregg-lean-ffi)"
    );
    let n = rounds();
    let mut t = Tally {
        decided: 0,
        draws: 0,
        wins: [0, 0],
        last_turn_wins: 0,
        ended_on_response: 0,
    };
    // How many rounds each clause of the terminal rule decided: 0..3 the absolute bars (all the
    // OLD gate could express), 4..7 the tie-breaks it refused, 8 a genuine dead heat.
    let mut by_clause = [0u64; 9];
    for seed in 0..n {
        let (winner, clause, last_seat, last_was_response) = play(seed);
        by_clause[clause as usize] += 1;
        if last_was_response {
            t.ended_on_response += 1;
        }
        match winner {
            None => t.draws += 1,
            Some(w) => {
                t.decided += 1;
                t.wins[w.idx()] += 1;
                if w == last_seat {
                    t.last_turn_wins += 1;
                }
            }
        }
    }
    let pct = |x: u64, d: u64| {
        if d == 0 {
            0.0
        } else {
            100.0 * x as f64 / d as f64
        }
    };
    let threshold_decided: u64 = by_clause[0..4].iter().sum();
    let adjudicated_decided: u64 = by_clause[4..8].iter().sum();

    println!("=== TUG BALANCE (n = {n}, both seats maximin, PLAYED path) ===");
    println!(
        "draws                     {:>6.1}%  ({}/{})   <- was 78.5% under the deleted `winner_of`",
        pct(t.draws, n),
        t.draws,
        n
    );
    println!(
        "seat A wins (of decided)  {:>6.1}%",
        pct(t.wins[0], t.decided)
    );
    println!(
        "seat B wins (of decided)  {:>6.1}%",
        pct(t.wins[1], t.decided)
    );
    println!(
        "LAST-TURN seat wins       {:>6.1}%   <- baseline was ~57%; the restored cut made it worse",
        pct(t.last_turn_wins, t.decided)
    );
    println!(
        "round ended on a RESPONSE {:>6.1}%  (endogenous: B chooses whether to cede the last word)",
        pct(t.ended_on_response, n)
    );
    println!();
    println!(
        "--- which clause of `roundWinner` decided (the deployed method it commits under) ---"
    );
    for (b, count) in by_clause.iter().enumerate() {
        println!(
            "  clause {b}  {:<16}  {:>6.1}%  ({count})",
            dregg_multiway_tug::state::score_method(b as u8),
            pct(*count, n)
        );
    }
    println!(
        "  absolute bars (0..3): {:.1}%   tie-breaks (4..7): {:.1}%   dead heat (8): {:.1}%",
        pct(threshold_decided, n),
        pct(adjudicated_decided, n),
        pct(by_clause[8], n)
    );

    // ── TEETH ──────────────────────────────────────────────────────────────────────────────────
    assert!(t.decided > 0, "no round was decided at all");
    assert!(
        t.wins[0] > 0 && t.wins[1] > 0,
        "one seat won every decided round ({:?}) — that is a structural landslide, not a game",
        t.wins
    );
    // ⚑ THE FALSIFIER FOR THE WHOLE LANE. Under the deleted twin this was 78.5%. A draw is now an
    // EXACT dead heat on BOTH charm and rows, which is rare; anything above 25% means the
    // adjudication stopped reaching the played path (a re-emit reverted, the oracle silently
    // failing, or a fallback creeping back in).
    assert!(
        pct(t.draws, n) < 25.0,
        "draw rate {:.1}% — the terminal rule is NOT reaching the played game (the truncated \
         absolute bar drew 78.5%)",
        pct(t.draws, n)
    );
    // And non-vacuously so: most decided rounds must be decided by a TIE-BREAK clause, i.e. by
    // exactly the branches the old deployed gate refused to admit.
    assert!(
        adjudicated_decided > threshold_decided,
        "only {adjudicated_decided} of {n} rounds were decided by a tie-break clause vs \
         {threshold_decided} by an absolute bar — if the tie-breaks were unreachable this test \
         would still pass on the thresholds alone, so it is asserted"
    );
    // Every clause the harness reports must be a real deployed method (the artifact's own list).
    assert_eq!(
        dregg_multiway_tug::program_loader::score_branch_methods().len(),
        9,
        "the emitted artifact carries one method per clause of the terminal rule"
    );
}
