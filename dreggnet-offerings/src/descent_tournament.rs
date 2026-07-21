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

use deos_view::{MenuItem, ViewNode};
use dreggnet_tournament::{
    CompetitorRef, Entrant, Outcome, RoundUniverse, SideOutcome, Submission, Tournament,
};
use ugc_dregg::Universe;

use crate::Surface;
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

// ═══════════════════════════════════════════════════════════════════════════════
// Standings — the tournament result, surfaced back as a renderable leaderboard.
// ═══════════════════════════════════════════════════════════════════════════════

/// **One competitor's line in the tournament standings.** Derived purely from a completed
/// bracket [`Outcome`] (no new state, no re-run): how far the competitor got and the best
/// verified result they posted. The no-cheat gate's verdicts (a [`SideOutcome::Verified`] win, a
/// [`SideOutcome::Rejected`] forgery, an [`SideOutcome::Absent`] no-show) are the only inputs, so a
/// forged / lost / absent run cannot out-place a verified survivor.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StandingRow {
    /// The competitor's display name.
    pub name: String,
    /// The competitor's seed index (bracket position / entry order) — the stable tie-break.
    pub seed: usize,
    /// How many rounds the competitor posted a VERIFIED win in (the no-cheat gate passed them).
    pub verified_wins: usize,
    /// The best (lowest) verified turns-to-win the competitor posted anywhere in the bracket, or
    /// `None` if they never posted a verified win (a forged / lost / absent competitor).
    pub best_turns: Option<usize>,
    /// The furthest round INDEX the competitor advanced out of (a verified win in round `r` means
    /// they reached round `r + 1`). `None` if they never advanced a single round.
    pub advanced_through: Option<usize>,
    /// Whether the competitor is the bracket champion (the last verified survivor).
    pub champion: bool,
    /// Whether ANY of the competitor's submissions was refused by the no-cheat gate (a forged /
    /// incomplete run somewhere) — the honesty flag a frontend paints beside the row.
    pub was_refused: bool,
}

impl StandingRow {
    /// The ranked position label a frontend paints (`"1st"`, `"2nd"`, `"3rd"`, `"4th"`, …).
    pub fn place_label(place: usize) -> String {
        let n = place + 1;
        let suffix = match (n % 10, n % 100) {
            (1, 11) | (2, 12) | (3, 13) => "th",
            (1, _) => "st",
            (2, _) => "nd",
            (3, _) => "rd",
            _ => "th",
        };
        format!("{n}{suffix}")
    }
}

/// **The tournament's final standings** — the ranked competitor board a frontend renders. Built
/// from a completed [`Outcome`] with [`from_outcome`](DescentStandings::from_outcome); the rows are
/// ordered by real merit (champion first, then furthest round reached, then verified wins, then
/// best turns, then entry order). This is the seam the integration gap named: the bracket produces a
/// champion, and this turns the whole result into a [`Surface`] every frontend already knows how to
/// paint (the same deos view-tree the dungeon / market render), so a tournament's outcome shows up
/// as a leaderboard rather than staying buried in the `Outcome` record.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DescentStandings {
    /// The competitor rows, best-placed first.
    pub rows: Vec<StandingRow>,
    /// The champion's name, if the final round produced a verified survivor.
    pub champion: Option<String>,
    /// The number of rounds the bracket ran.
    pub rounds: usize,
}

impl DescentStandings {
    /// **Derive the standings from a completed bracket [`Outcome`].** Walks every round's matches,
    /// tallying each competitor's verified wins, best verified turns, furthest round reached, and
    /// whether the gate ever refused them; then ranks the board. Pure over the `Outcome` — the same
    /// `Outcome` always yields the same standings.
    pub fn from_outcome(outcome: &Outcome) -> DescentStandings {
        use std::collections::BTreeMap;

        // Accumulate per competitor, keyed by their stable seed index.
        struct Acc {
            name: String,
            seed: usize,
            verified_wins: usize,
            best_turns: Option<usize>,
            advanced_through: Option<usize>,
            was_refused: bool,
        }
        let mut acc: BTreeMap<usize, Acc> = BTreeMap::new();

        let note = |acc: &mut BTreeMap<usize, Acc>,
                    who: &CompetitorRef,
                    round: usize,
                    outcome: &SideOutcome| {
            let e = acc.entry(who.seed).or_insert_with(|| Acc {
                name: who.name.clone(),
                seed: who.seed,
                verified_wins: 0,
                best_turns: None,
                advanced_through: None,
                was_refused: false,
            });
            match outcome {
                SideOutcome::Verified { turns } => {
                    e.verified_wins += 1;
                    e.best_turns = Some(e.best_turns.map_or(*turns, |b| b.min(*turns)));
                    e.advanced_through = Some(e.advanced_through.map_or(round, |r| r.max(round)));
                }
                SideOutcome::Rejected { .. } => e.was_refused = true,
                SideOutcome::Absent => {}
            }
        };

        for r in &outcome.rounds {
            for m in &r.matches {
                if let Some(a) = &m.a {
                    note(&mut acc, a, r.round, &m.a_outcome);
                }
                if let Some(b) = &m.b {
                    note(&mut acc, b, r.round, &m.b_outcome);
                }
            }
        }

        let champ_seed = outcome.champion.as_ref().map(|c| c.seed);
        let mut rows: Vec<StandingRow> = acc
            .into_values()
            .map(|a| StandingRow {
                name: a.name,
                seed: a.seed,
                verified_wins: a.verified_wins,
                best_turns: a.best_turns,
                advanced_through: a.advanced_through,
                champion: champ_seed == Some(a.seed),
                was_refused: a.was_refused,
            })
            .collect();

        // Rank by real merit: champion first; then furthest round reached (a `None` never
        // advanced); then more verified wins; then fewer turns (a `None` sorts last); then entry
        // order (seed) as the stable, deterministic tie-break.
        rows.sort_by(|x, y| {
            y.champion
                .cmp(&x.champion)
                .then(cmp_opt_desc(x.advanced_through, y.advanced_through))
                .then(y.verified_wins.cmp(&x.verified_wins))
                .then(cmp_best_turns(x.best_turns, y.best_turns))
                .then(x.seed.cmp(&y.seed))
        });

        DescentStandings {
            rows,
            champion: outcome.champion.as_ref().map(|c| c.name.clone()),
            rounds: outcome.rounds.len(),
        }
    }

    /// The champion's standing row, if a verified survivor was crowned.
    pub fn champion_row(&self) -> Option<&StandingRow> {
        self.rows.iter().find(|r| r.champion)
    }

    /// **Render the standings as a deos affordance [`Surface`]** — the leaderboard a frontend paints
    /// (the same view-tree the game offerings render). A titled section per placed competitor: their
    /// rank, name, verified wins + best turns, and an honesty pill when the gate refused a run. The
    /// champion is called out at the top. This is what closes the integration gap — a tournament's
    /// result becomes a renderable board, not a buried `Outcome`.
    pub fn surface(&self) -> Surface {
        let mut children: Vec<ViewNode> = Vec::new();

        children.push(ViewNode::Section {
            title: "Champion".to_string(),
            tag: "genuine".to_string(),
            children: vec![ViewNode::Text(match &self.champion {
                Some(name) => format!("{name} — the last verified survivor"),
                None => "no champion — nobody posted a verified win".to_string(),
            })],
        });

        let items: Vec<MenuItem> = self
            .rows
            .iter()
            .enumerate()
            .map(|(place, row)| {
                let turns = row
                    .best_turns
                    .map(|t| format!("{t} turns"))
                    .unwrap_or_else(|| "no verified win".to_string());
                let flag = if row.was_refused {
                    " — a run refused"
                } else {
                    ""
                };
                MenuItem {
                    label: format!(
                        "{place}  {name}  ({wins} verified, best {turns}){flag}",
                        place = StandingRow::place_label(place),
                        name = row.name,
                        wins = row.verified_wins,
                    ),
                    // A standings row is a read-only leaderboard entry, not an actuator: the "turn"
                    // is a stable inert verb and the arg is the competitor's seed (for a frontend
                    // that wants to deep-link a competitor's bracket record). Shown, never fired.
                    turn: "standing".to_string(),
                    arg: i64::try_from(row.seed)
                        .expect("the bounded tournament field fits the stable action wire"),
                    enabled: false,
                }
            })
            .collect();

        children.push(ViewNode::Section {
            title: "Standings".to_string(),
            tag: "accent".to_string(),
            children: vec![ViewNode::Menu { items }],
        });

        Surface(ViewNode::Section {
            title: format!("The Descent — Weekly Tournament ({} rounds)", self.rounds),
            tag: "accent".to_string(),
            children,
        })
    }
}

/// Descending compare of two `Option<usize>` "furthest round reached" keys — a `Some` (advanced)
/// always ranks ahead of a `None` (never advanced); a higher round ranks ahead of a lower one.
fn cmp_opt_desc(x: Option<usize>, y: Option<usize>) -> std::cmp::Ordering {
    match (x, y) {
        (Some(a), Some(b)) => b.cmp(&a),
        (Some(_), None) => std::cmp::Ordering::Less,
        (None, Some(_)) => std::cmp::Ordering::Greater,
        (None, None) => std::cmp::Ordering::Equal,
    }
}

/// Ascending compare of two best-turns keys where FEWER turns is better and a `None` (no verified
/// win) always ranks last.
fn cmp_best_turns(x: Option<usize>, y: Option<usize>) -> std::cmp::Ordering {
    match (x, y) {
        (Some(a), Some(b)) => a.cmp(&b),
        (Some(_), None) => std::cmp::Ordering::Less,
        (None, Some(_)) => std::cmp::Ordering::Greater,
        (None, None) => std::cmp::Ordering::Equal,
    }
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

    /// The STANDINGS surface the bracket result as a renderable leaderboard: the champion ranks
    /// first, a forger who was refused ranks BELOW every verified survivor and carries the
    /// refused flag, and the rendered surface names the competitors — non-vacuous.
    #[test]
    fn standings_rank_the_champion_first_and_a_forger_last() {
        let mut t = weekly_descent_tournament([0x11; 32]);
        t.enter(honest_descender("ada"))
            .enter(forging_descender("mallory"));
        let out = t.run();
        let standings = DescentStandings::from_outcome(&out);

        // Champion first.
        assert_eq!(standings.rows[0].name, "ada");
        assert!(standings.rows[0].champion, "the champion heads the board");
        assert_eq!(standings.champion.as_deref(), Some("ada"));
        assert!(
            standings.rows[0].best_turns.is_some(),
            "the champion posted a verified win"
        );

        // The forger ranks below and is flagged refused with no verified win.
        let mallory = standings
            .rows
            .iter()
            .find(|r| r.name == "mallory")
            .expect("mallory is on the board");
        assert!(mallory.was_refused, "the forger's run was refused");
        assert_eq!(mallory.verified_wins, 0, "a forged run is no verified win");
        assert!(mallory.best_turns.is_none());
        let ada_place = standings.rows.iter().position(|r| r.name == "ada").unwrap();
        let mallory_place = standings
            .rows
            .iter()
            .position(|r| r.name == "mallory")
            .unwrap();
        assert!(
            ada_place < mallory_place,
            "a verified survivor out-places a forger"
        );

        // The surface is a real leaderboard that names the competitors.
        let surface = standings.surface();
        let painted = format!("{:?}", surface.view());
        assert!(painted.contains("ada"), "the board paints the champion");
        assert!(painted.contains("mallory"), "the board paints the forger");
        assert!(painted.contains("Weekly Tournament"), "the board is titled");
    }

    /// Over a full 4-competitor bracket the standings rank strictly by furthest round reached:
    /// the champion (2 wins) tops the finalist (1 win) tops the round-0 losers (0 wins).
    #[test]
    fn standings_rank_by_how_far_each_competitor_reached() {
        let mut t = weekly_descent_tournament([0x44; 32]);
        for name in ["ada", "bran", "cy", "del"] {
            t.enter(honest_descender(name));
        }
        let out = t.run();
        let standings = DescentStandings::from_outcome(&out);

        assert_eq!(standings.rows.len(), 4, "all four competitors are ranked");
        assert!(standings.rows[0].champion, "the champion is first");
        assert_eq!(
            standings.rows[0].verified_wins, 2,
            "the champion won both rounds"
        );
        // The board is non-increasing in verified wins (merit order).
        for w in standings.rows.windows(2) {
            assert!(
                w[0].verified_wins >= w[1].verified_wins
                    || w[0].advanced_through >= w[1].advanced_through,
                "the standings are ranked by merit"
            );
        }
        // Every competitor advanced at least round 0 (all honest), so none is flagged refused.
        assert!(
            standings.rows.iter().all(|r| !r.was_refused),
            "an all-honest bracket refuses nobody"
        );
    }

    /// A bracket with NO verified winner crowns no champion, and the standings say so (the
    /// surface reports the empty champion) — the leaderboard is honest about a dead bracket.
    #[test]
    fn standings_report_no_champion_when_nobody_verifies() {
        let mut t = weekly_descent_tournament([0x55; 32]);
        t.enter(forging_descender("mallory"))
            .enter(Entrant::no_show("ghost"));
        let out = t.run();
        let standings = DescentStandings::from_outcome(&out);

        assert!(standings.champion.is_none(), "no verified win, no champion");
        assert!(standings.champion_row().is_none());
        let painted = format!("{:?}", standings.surface().view());
        assert!(
            painted.contains("no champion"),
            "the board is honest about a dead bracket"
        );
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
