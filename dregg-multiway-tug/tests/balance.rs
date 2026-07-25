//! # The measured balance of a round, AFTER I-cut-you-choose was restored.
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
//! # ⚑ MEASURED 2026-07-25, n=1500, both seats maximin — AND THE LAST-ACTOR EDGE GOT WORSE.
//!
//! ```text
//!                         shipped rule      PROVEN Lean `roundWinner`
//!                         (`winner_of`)     (adjudicated, NOT shipped)
//!   draws                     78.5%                 8.1%
//!   seat A / seat B        55.0 / 45.0           52.6 / 47.4
//!   LAST-TURN seat wins       77.6%                64.8%     <- baseline was ~57%
//! ```
//!
//! Read the right-hand column against the ~57% baseline (that figure was also measured under
//! adjudication). **Restoring I-cut-you-choose made the last-mover edge LARGER, 57% -> 64.8%**,
//! and the mechanism is structural rather than an artifact of agent strength: the final act of a
//! round is now a free pick of the better half, so whoever answers last is simply handed value.
//! 56.7% of rounds end on a response, and a response after seat B's fourth action belongs to
//! seat A — which is why A, who used to move first, now finishes ahead.
//!
//! CONCLUSION: **one round does not survive this measurement.** The honest port is Hanamikoji's
//! own — a multi-round match with an alternating opener — which is a match-state change beyond
//! the lane that restored the cut. Caveat, stated rather than buried: the ~57% baseline was
//! taken with greedy agents on the scripted engine and this with maximin agents on the new one,
//! so the two are not a controlled comparison; the DIRECTION is robust (a last free pick cannot
//! be worth less than zero), the exact delta is not.
//!
//! Second finding, independent of the above: the adjudication that took draws 66.1% -> 5.1% is
//! LEAN-ONLY. Rust `winner_of` still applies the absolute bar, so the game a player actually
//! plays draws **78.5%** of the time. See `adjudicated()` for why it cannot simply be wired in.

use dregg_multiway_tug::reference::{Decision, Engine, INFLUENCE, N_GUILDS, Player, Projection};

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

/// The ADJUDICATED terminal rule, mirroring the PROVEN Lean `roundWinner`
/// (`MultiwayTug.lean` §7B): absolute bar first (`Won`, unchanged), then higher total charm,
/// then more rows held, and only exact parity on both is a real dead heat.
///
/// ⚠ It is measured here and NOT shipped, because it CANNOT be: the deployed score method's
/// win-gate is `AnyOf[not(winner==p), charm>=11, guilds>=4]`, and Lean's own
/// `winTooth_admits_iff_Won` proves that gate IS the predicate `Won`. An adjudicated winner is
/// by definition one who cleared NEITHER bar, so the deployed referee would REFUSE the very
/// `winner` this rule names. Landing the draw-rate fix therefore needs the TEETH changed, not
/// just the engine.
fn adjudicated(proj: &Projection) -> Option<Player> {
    let (ca, cb) = (proj.charm[0], proj.charm[1]);
    let (ga, gb) = (proj.guilds_controlled[0], proj.guilds_controlled[1]);
    if ca >= 11 {
        return Some(Player::A);
    }
    if cb >= 11 {
        return Some(Player::B);
    }
    if ga >= 4 {
        return Some(Player::A);
    }
    if gb >= 4 {
        return Some(Player::B);
    }
    if cb < ca {
        return Some(Player::A);
    }
    if ca < cb {
        return Some(Player::B);
    }
    if gb < ga {
        return Some(Player::A);
    }
    if ga < gb {
        return Some(Player::B);
    }
    None
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

fn play(seed: u64) -> (Option<Player>, Option<Player>, Player, bool) {
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
    let winner = e.score();
    let adj = adjudicated(&e.projection());
    (winner, adj, last_seat, last_was_response)
}

#[test]
fn measured_balance_after_i_cut_you_choose() {
    let n = rounds();
    let mut t = Tally {
        decided: 0,
        draws: 0,
        wins: [0, 0],
        last_turn_wins: 0,
        ended_on_response: 0,
    };
    let mut a = Tally {
        decided: 0,
        draws: 0,
        wins: [0, 0],
        last_turn_wins: 0,
        ended_on_response: 0,
    };
    for seed in 0..n {
        let (winner, adj, last_seat, last_was_response) = play(seed);
        if last_was_response {
            t.ended_on_response += 1;
        }
        for (tally, w) in [(&mut t, winner), (&mut a, adj)] {
            match w {
                None => tally.draws += 1,
                Some(w) => {
                    tally.decided += 1;
                    tally.wins[w.idx()] += 1;
                    if w == last_seat {
                        tally.last_turn_wins += 1;
                    }
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
    println!("=== TUG BALANCE (n = {n}, both seats maximin) ===");
    println!(
        "draws                     {:>6.1}%  ({}/{})",
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
        "LAST-TURN seat wins       {:>6.1}%",
        pct(t.last_turn_wins, t.decided)
    );
    println!(
        "round ended on a RESPONSE {:>6.1}%  (endogenous: B chooses whether to cede the last word)",
        pct(t.ended_on_response, n)
    );
    println!();
    println!("--- under the PROVEN Lean `roundWinner` (adjudicated; NOT shipped, see above) ---");
    println!(
        "draws                     {:>6.1}%  ({}/{})",
        pct(a.draws, n),
        a.draws,
        n
    );
    println!(
        "seat A wins (of decided)  {:>6.1}%",
        pct(a.wins[0], a.decided)
    );
    println!(
        "seat B wins (of decided)  {:>6.1}%",
        pct(a.wins[1], a.decided)
    );
    println!(
        "LAST-TURN seat wins       {:>6.1}%   <-- baseline was ~57%; THIS GOT WORSE",
        pct(a.last_turn_wins, a.decided)
    );

    // Teeth, so this is a test and not a print statement: the falsifier for the whole lane is
    // that outcomes vary at all. A scripted engine produces ONE outcome per seed and, with a
    // symmetric schedule, a degenerate split.
    assert!(t.decided > 0, "no round was decided at all");
    assert!(
        t.wins[0] > 0 && t.wins[1] > 0,
        "one seat won every decided round ({:?}) — that is a structural landslide, not a game",
        t.wins
    );
}
