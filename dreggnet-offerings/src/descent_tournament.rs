//! # `descent_tournament` — a WEEKLY TOURNAMENT over The Descent
//!
//! A thin hook that runs a [`dreggnet_tournament`] no-cheat bracket **over The Descent**
//! ([`crate::daily_descent`]). Each ROUND is a fresh, **beacon-seeded daily descent** — the
//! same day's world for every competitor that round (fair) — and a competitor **ADVANCES
//! only on a VERIFIED WIN**: their run of the day is re-executed to the hoard through
//! ugc-dregg's audited [`verify_completion`](ugc_dregg::verify_completion) no-cheat gate. A
//! **forged / incomplete / lost** run does NOT advance. The champion is the last verified
//! survivor.
//!
//! ## How it welds the two layers
//!
//! * **The round universe is a daily descent.** [`descent_rounds`] turns each round's
//!   beacon epoch into today's committed seed ([`procgen_dregg::daily_seed`]), draws the
//!   day's permadeath world ([`crate::daily_descent::daily_scene`]), and publishes it as the
//!   round's [`ugc_dregg::Universe`] ([`crate::daily_descent::DailyDescent::universe`]). So a
//!   round IS a real no-cheat leaderboard over the flagship's own day — the tournament and
//!   the daily-descent offering deploy the byte-identical world.
//! * **A competitor submits a Descent win.** The winning line of a day's descent is a pure
//!   function of the day's warden HP + depth (both drawn from the beacon seed), so
//!   [`descent_winning_line`] reads them off the shared, published day source and produces
//!   the honest fight-heal-press-key-descend-seize line. An [`honest_descender`] plays it; a
//!   [`forging_descender`] retcons a step (drops the key) and is refused on re-verification.
//!
//! ## "Weekly" — the schedule
//!
//! A single-elimination bracket needs `ceil(log2 N)` rounds; a WEEKLY tournament maps those
//! rounds onto successive **days of the week**, each a fresh beacon-seeded daily. The bracket
//! ITSELF (fair rounds, verify-gated advancement, a champion) is what is real here; the LIVE
//! weekly cadence (one round per real day, entry windows, the reveal) and PRIZES (glory over
//! `$DREGG` services, never yield) are the named residual — the frontend/orchestrator above
//! this core. This module produces the champion; a scheduler decides *when* each round runs.
//!
//! ## Honest scope
//!
//! REAL: the bracket over The Descent, verify-gated on ugc-dregg's no-cheat gate (a forged
//! run cannot advance; the champion is a verified survivor; each round is a real daily-descent
//! leaderboard). NAMED, not built: the live weekly schedule/entry-window/reveal, seeding by
//! skill (seeding is entry order), and prize settlement (glory, not yield).

use dreggnet_tournament::{Entrant, RoundUniverse, Submission, Tournament};
use ugc_dregg::Universe;

use crate::daily_descent::{
    self, CORRIDOR_ON, GATE_HEAL, GATE_MEASURED, GATE_PRESS, HOARD_FORCE, HOARD_SEIZE, KEY_LEAVE,
    KEY_TAKE,
};

/// The author label the tournament publishes each round's daily descent under (a stable
/// name so the round universe is content-addressed identically for every competitor).
pub const TOURNAMENT_AUTHOR: &str = "descent-tournament";

/// **The round-universe provider for a Descent tournament.** Each round's beacon epoch
/// becomes today's committed seed, the day's permadeath descent is drawn, and it is
/// published as the round's [`Universe`] — a fresh, fair, everyone-derives-it-identically
/// daily. Invoked once per round, so every competitor that round faces the same day.
pub fn descent_rounds() -> RoundUniverse {
    Box::new(|_round, epoch| {
        let seed = procgen_dregg::daily_seed(epoch);
        let day = daily_descent::daily_scene(&seed);
        day.universe(TOURNAMENT_AUTHOR)
            .expect("today's descent publishes as a universe")
    })
}

/// Read the day's warden HP off a published descent source (`~ warden_hp = N` in the gate
/// passage). Falls back to the weakest warden if unparsable (never panics on a shared world).
fn parse_warden_hp(source: &str) -> u64 {
    for line in source.lines() {
        if let Some(rest) = line.trim().strip_prefix("~ warden_hp = ") {
            if let Ok(n) = rest.trim().parse::<u64>() {
                return n;
            }
        }
    }
    45
}

/// Count the day's connecting corridors (`=== corridor{i}` headers) between the key room
/// and the hoard gate — the beacon-drawn depth. One `CORRIDOR_ON` move per corridor.
fn count_corridors(source: &str) -> usize {
    source
        .lines()
        .filter(|l| l.trim_start().starts_with("=== corridor"))
        .count()
}

/// The gate fight line for a warden of `warden_hp`: measured blows (each 15 to you + 15 to
/// the warden, gated `hp >= 16`), interleaving the ONE field-dressing heal (+25) exactly
/// when the next needed blow would strand you. Mirrors the scene's HP arithmetic (player
/// starts at 50), so it fells any beacon-drawn warden without a killing blow.
fn gate_fight(warden_hp: u64) -> Vec<usize> {
    let mut hp: i64 = 50;
    let mut wh: i64 = warden_hp as i64;
    let mut healed = false;
    let mut moves = Vec::new();
    while wh > 0 {
        if hp >= 16 {
            hp -= 15;
            wh -= 15;
            moves.push(GATE_MEASURED);
        } else if !healed {
            hp += 25;
            healed = true;
            moves.push(GATE_HEAL);
        } else {
            // Unreachable for the beacon-drawn wardens (45/60): a defensive break.
            break;
        }
    }
    moves
}

/// **The honest winning line for a published day's descent** — a pure function of the day's
/// (shared, fair) source: fell the warden (with the heal if the warden is stout), press
/// past it, take the key, press through the beacon-drawn corridors, force the hoard-door,
/// and seize the hoard (the win: `gold == 500`, the scene ends). This is the exact move
/// sequence a competitor submits; the no-cheat gate re-executes it to the hoard.
pub fn descent_winning_line(day_source: &str) -> Vec<usize> {
    let warden_hp = parse_warden_hp(day_source);
    let corridors = count_corridors(day_source);
    let mut moves = gate_fight(warden_hp);
    moves.push(GATE_PRESS); // press past the felled warden -> keyroom
    moves.push(KEY_TAKE); // take the key -> the first corridor
    for _ in 0..corridors {
        moves.push(CORRIDOR_ON); // press through each deepening corridor
    }
    moves.push(HOARD_FORCE); // force the key-gated hoard-door -> hoard
    moves.push(HOARD_SEIZE); // seize the hoard -> END (the win)
    moves
}

/// **An honest Descent competitor** — plays the real day's winning line each round (derived
/// from the shared published world). Advances on the verified win.
pub fn honest_descender(name: impl Into<String>) -> Entrant {
    Entrant::new(
        name,
        Box::new(|u: &Universe| Submission::Play(descent_winning_line(u.source()))),
    )
}

/// **A forging Descent competitor** — records the honest winning line, then RETCONS the
/// key-take step to "press deeper empty-handed" ([`KEY_LEAVE`]). On re-verification the
/// keyless run is refused at the key-gated hoard-door — the forged run does NOT advance.
pub fn forging_descender(name: impl Into<String>) -> Entrant {
    Entrant::new(
        name,
        Box::new(|u: &Universe| {
            let moves = descent_winning_line(u.source());
            // The key-take is the move right after the gate fight + the press-past.
            let key_step = gate_fight(parse_warden_hp(u.source())).len() + 1;
            Submission::Forged {
                base_moves: moves,
                tamper_step: key_step,
                tamper_choice: KEY_LEAVE,
            }
        }),
    )
}

/// **Build a WEEKLY Descent tournament** pre-wired with beacon-seeded daily-descent rounds.
/// Enter competitors (e.g. [`honest_descender`] / [`forging_descender`] / [`Entrant::no_show`])
/// then `run` the bracket; advancement is verify-gated every round and the champion is the
/// last verified survivor.
pub fn weekly_descent_tournament(base_seed: [u8; 32]) -> Tournament {
    Tournament::new(base_seed, descent_rounds())
}

#[cfg(test)]
mod tests {
    //! The Descent tournament, DRIVEN end-to-end: a real win advances + a forged run does
    //! not; the bracket runs to a champion over beacon-seeded daily-descent rounds; a
    //! bracket of only cheats/no-shows crowns no champion; the rounds are fresh + fair.
    use super::*;
    use dreggnet_tournament::{SideOutcome, round_epoch};

    /// The honest winning line actually WINS a day's descent (the no-cheat gate re-executes
    /// it to the hoard) and a FORGED run is REJECTED on re-verification — non-vacuous.
    #[test]
    fn a_real_descent_win_advances_and_a_forged_run_does_not() {
        let mut t = weekly_descent_tournament([0x11; 32]);
        t.enter(honest_descender("ada"))
            .enter(forging_descender("mallory"));
        let out = t.run();

        let m = &out.rounds[0].matches[0];
        assert!(
            matches!(m.a_outcome, SideOutcome::Verified { .. }),
            "the honest Descent run must verify, got {:?}",
            m.a_outcome
        );
        assert!(
            matches!(m.b_outcome, SideOutcome::Rejected { .. }),
            "the forged Descent run must be rejected, got {:?}",
            m.b_outcome
        );
        let champ = out.champion.expect("a verified survivor is champion");
        assert_eq!(champ.name, "ada", "only the verified Descent win advances");
        assert!(
            !out.rounds[0]
                .advancers()
                .iter()
                .any(|c| c.name == "mallory"),
            "a forged Descent run NEVER advances"
        );
    }

    /// The bracket runs to a CHAMPION over multiple beacon-seeded daily-descent rounds; every
    /// advancement in the whole bracket is a verified win.
    #[test]
    fn the_bracket_runs_to_a_champion() {
        let mut t = weekly_descent_tournament([0x44; 32]);
        for name in ["ada", "bran", "cy", "del"] {
            t.enter(honest_descender(name));
        }
        let out = t.run();

        assert_eq!(out.rounds.len(), 2, "4 competitors -> 2 rounds");
        for r in &out.rounds {
            for c in r.advancers() {
                let m = r
                    .matches
                    .iter()
                    .find(|m| m.advanced.as_ref() == Some(&c))
                    .expect("an advancer has a match");
                let side = if m.a.as_ref() == Some(&c) {
                    &m.a_outcome
                } else {
                    &m.b_outcome
                };
                assert!(
                    matches!(side, SideOutcome::Verified { .. }),
                    "every advancer carries a verified Descent win, got {side:?}"
                );
            }
        }
        assert_eq!(out.rounds[0].advancers().len(), 2);
        assert_eq!(out.rounds[1].advancers().len(), 1);
        assert!(
            out.champion.is_some(),
            "the last verified survivor is champion"
        );
    }

    /// A bracket of only cheats + no-shows crowns NO champion — you cannot advance without a
    /// verified Descent win.
    #[test]
    fn cheats_and_no_shows_crown_no_champion() {
        let mut t = weekly_descent_tournament([0x55; 32]);
        t.enter(forging_descender("mallory"))
            .enter(Entrant::no_show("ghost"));
        let out = t.run();
        let m = &out.rounds[0].matches[0];
        assert!(matches!(m.a_outcome, SideOutcome::Rejected { .. }));
        assert!(matches!(m.b_outcome, SideOutcome::Absent));
        assert!(m.advanced.is_none(), "no verified win -> nobody advances");
        assert!(out.champion.is_none(), "no champion without a verified win");
    }

    /// The rounds are FRESH + FAIR: each round is the beacon-derived daily every competitor
    /// shares, re-derivable from the round epoch, and successive rounds are different days.
    #[test]
    fn rounds_are_fresh_and_fair() {
        let seed = [0x77; 32];
        let mut t = weekly_descent_tournament(seed);
        for name in ["ada", "bran", "cy", "del"] {
            t.enter(honest_descender(name));
        }
        let out = t.run();
        for (i, r) in out.rounds.iter().enumerate() {
            assert_eq!(
                r.epoch,
                round_epoch(&seed, i),
                "the round epoch is reproducible"
            );
            let expected = {
                let s = procgen_dregg::daily_seed(&r.epoch);
                daily_descent::daily_scene(&s)
                    .universe(TOURNAMENT_AUTHOR)
                    .expect("re-derive the round's daily")
            };
            assert_eq!(
                r.universe_id,
                expected.id(),
                "the round universe is exactly the beacon-derived daily descent"
            );
        }
        assert_ne!(
            out.rounds[0].universe_id, out.rounds[1].universe_id,
            "each round is a fresh day"
        );
    }
}
