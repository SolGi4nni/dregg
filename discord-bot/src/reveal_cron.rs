//! **The daily-reveal cron — the DESCENT rolls automatically at the UTC-day boundary.**
//!
//! `docs/GAME-STRATEGY.md` names the daily reveal: "at midnight … a new dungeon is revealed."
//! Today that was a manual `/descent play`; this closes the seam. A background tokio task
//! (`start`) ticks on an interval, computes the current UTC **day number**, and when the day
//! strictly advances it fires the reveal: it FETCHES today's live drand `quicknet` round (BLS-
//! verified — [`procgen_dregg::beacon::todays_beacon_or_pinned`]), CACHES that verified beacon so
//! every `/descent` surface serves it ([`crate::commands::descent::set_live_beacon`]), OPENS
//! today's [`DailyDescentOffering`] (fail-closed — a forged reveal opens nothing), and announces
//! the day. The daily then rolls on its own — no manual command.
//!
//! It mirrors the `starbridge-web-surface` `RevealReactor` pattern (a temporal tick → the daily
//! reveal) with the same **strictly-monotonic day** tooth: [`RevealClock`] only reveals a day that
//! strictly advances the last-revealed one, so a re-tick within the same day (or a replayed clock)
//! is an idempotent no-op — the daily cannot be double-revealed.
//!
//! ## What is live here vs the deploy remainder
//! - **Live (wired here):** the day-boundary trigger, the live drand fetch + verify, the verified
//!   beacon cached into every `/descent` surface, and today's world opened + published.
//! - **The deploy remainder (ops, not code):** a RUNNING bot instance with network access to a
//!   drand node (until then the offline pinned round is served — still a genuine BLS-verified
//!   reveal), and the crown's LIVE-NOTARY (the DM narrator over real MPC-TLS) — a separate frontier.
//!
//! ## Driven, not LARPed
//! The reveal CORE ([`reveal_day`] / [`open_todays_world`]) is a pure, `Discord`-free function
//! driven by the tests below over an in-memory character store + a real `ugc_dregg::Registry`: the
//! scheduler firing opens today's descent with today's beacon seed, a same-day re-tick is a no-op,
//! and a simulated new day (a different verified beacon) rolls a genuinely different dungeon.

use std::sync::Arc;
use std::time::Duration;

use serenity::all::{ChannelId, CreateMessage, Http};
use tokio::time;
use tracing::{info, warn};

use dreggnet_offerings::DreggIdentity;
use dreggnet_offerings::character::CharacterStore;
use dreggnet_offerings::daily_descent::{DailyDescentOffering, DailyRun};
use procgen_dregg::CommittedSeed;
use procgen_dregg::beacon::DailyBeacon;
use ugc_dregg::{Registry, UniverseId};

use crate::BotState;
use crate::commands::descent;

/// The leaderboard author label today's world is published under — MUST match
/// `commands::descent::BOARD_AUTHOR` so the cron-opened world is the SAME content-addressed
/// universe a `/descent play` publishes (a run recorded on one re-verifies on the other).
const BOARD_AUTHOR: &str = "the-descent";

/// The system identity the daily reveal opens today's world under (to PROVE the offering deploys,
/// fail-closed). No character earns on it; it never plays a run — it only rolls the day.
const REVEAL_IDENTITY: &str = "daily-reveal";

/// How often the cron re-checks the UTC-day clock. Five minutes is far finer than the daily grain
/// (a boundary is caught within one tick); the strictly-monotonic day gate makes extra ticks free.
const REVEAL_POLL: Duration = Duration::from_secs(300);

/// The strictly-monotonic day clock — mirrors the `RevealReactor`'s `StrictMonotonic` day tooth. A
/// day is revealed at most once; only a day strictly greater than the last rolls a new dungeon.
#[derive(Default)]
pub struct RevealClock {
    last_revealed_day: Option<u64>,
}

impl RevealClock {
    /// A fresh clock (nothing revealed yet — the first tick reveals today).
    pub fn new() -> RevealClock {
        RevealClock::default()
    }

    /// The last UTC day this clock revealed (`None` until the first reveal).
    pub fn last(&self) -> Option<u64> {
        self.last_revealed_day
    }
}

/// The result of a fired reveal — the day it opened and today's beacon-seeded world (the seed, the
/// drawn title, and the content-addressed leaderboard id). Plain data (`Send`), so the production
/// task can return it out of a `spawn_blocking`.
#[derive(Clone)]
pub struct DailyReveal {
    /// The UTC day number this reveal opened.
    pub day_number: u64,
    /// The committed seed today's world was drawn from (equals the day's beacon seed).
    pub seed: CommittedSeed,
    /// The drawn day title (e.g. "The Sunken Descent").
    pub title: String,
    /// Today's content-addressed no-cheat-board universe id.
    pub universe_id: UniverseId,
}

/// **Open today's descent + publish its world** — the reveal's core act. Verifies `beacon` (a
/// forged reveal opens NOTHING — fail-closed), draws today's world from the beacon seed, publishes
/// its [`ugc_dregg::Universe`] to `board`, and returns the [`DailyReveal`] summary alongside the
/// opened [`DailyRun`] (so a caller may persist / inspect it on the same thread — the run holds a
/// non-`Send` world cell, so it never crosses a thread boundary). No clock gate: the caller owns
/// the day-monotonicity (see [`reveal_day`]).
pub fn open_todays_world<S: CharacterStore>(
    offering: &DailyDescentOffering<S>,
    board: &mut Registry,
    day_number: u64,
    beacon: &DailyBeacon,
) -> Result<(DailyReveal, DailyRun), String> {
    // Fail-closed: a beacon that does not verify opens no run (you cannot roll a forged day).
    let run = offering
        .open(DreggIdentity(REVEAL_IDENTITY.to_string()), beacon)
        .map_err(|e| format!("today's descent did not open: {e}"))?;
    let day = run.day();
    let universe = day
        .universe(BOARD_AUTHOR)
        .map_err(|e| format!("could not author today's world: {e:?}"))?;
    let reveal = DailyReveal {
        day_number,
        seed: day.seed,
        title: day.title.clone(),
        universe_id: board.publish(universe),
    };
    Ok((reveal, run))
}

/// **Fire the reveal for `day_number`, strictly-monotonically.** If the day does not strictly
/// advance `clock` (a same-day re-tick, or a stale day), it is an idempotent no-op (`Ok(None)`) —
/// the daily is never double-revealed. Otherwise it opens today's world (via [`open_todays_world`])
/// and records the day. This is the driven CORE the tests exercise; the production task adds the
/// live fetch, the beacon cache, and the announcement around it.
pub fn reveal_day<S: CharacterStore>(
    clock: &mut RevealClock,
    offering: &DailyDescentOffering<S>,
    board: &mut Registry,
    day_number: u64,
    beacon: &DailyBeacon,
) -> Result<Option<DailyReveal>, String> {
    if let Some(last) = clock.last_revealed_day {
        if day_number <= last {
            return Ok(None);
        }
    }
    let (reveal, _run) = open_todays_world(offering, board, day_number, beacon)?;
    clock.last_revealed_day = Some(day_number);
    Ok(Some(reveal))
}

/// The drand HTTP API base the cron fetches today's round from — `DRAND_API_BASE` env override,
/// else the public League-of-Entropy endpoint.
fn drand_api_base() -> String {
    std::env::var("DRAND_API_BASE")
        .unwrap_or_else(|_| procgen_dregg::beacon::DRAND_API_BASE.to_string())
}

/// **Start the daily-reveal cron background task.** Ticks on [`REVEAL_POLL`]; on each tick it
/// computes the current UTC day and, when the day strictly advances, fetches + verifies today's
/// live drand round, caches it into every `/descent` surface, opens today's world (fail-closed),
/// and announces the reveal. Mirrors [`crate::activity_feed::start`] / [`crate::bot_reactor::start`].
pub fn start(state: Arc<BotState>, http: Arc<Http>) {
    tokio::spawn(async move {
        info!(
            "Daily-reveal cron started (the Descent rolls automatically at the UTC-day boundary)"
        );
        // Small initial delay to let the bot finish connecting (mirrors activity_feed).
        time::sleep(Duration::from_secs(5)).await;

        let mut last_revealed_day: Option<u64> = None;
        let mut ticker = time::interval(REVEAL_POLL);
        loop {
            ticker.tick().await;
            let day = procgen_dregg::beacon::current_utc_day();
            if last_revealed_day == Some(day) {
                continue; // already revealed today — nothing to roll.
            }

            // Fetch + verify today's LIVE drand round off the runtime (blocking client); fall back
            // to the pinned published round when offline. Open + publish today's world on the same
            // blocking thread (the world cell is not `Send`), returning only the `Send` summary.
            let characters = state.characters.clone();
            let base = drand_api_base();
            let opened: Result<(DailyReveal, DailyBeacon), String> =
                tokio::task::spawn_blocking(move || {
                    let beacon = procgen_dregg::beacon::todays_beacon_or_pinned(&base);
                    // Cache the verified beacon so /descent play|board|today serve today's LIVE
                    // round (the daily seed becomes the real unpredictable-until-revealed beacon).
                    descent::set_live_beacon(day, beacon.clone());
                    let offering = DailyDescentOffering::new(characters);
                    let mut board = Registry::new();
                    let (reveal, _run) = open_todays_world(&offering, &mut board, day, &beacon)?;
                    Ok((reveal, beacon))
                })
                .await
                .unwrap_or_else(|e| Err(format!("reveal task panicked: {e}")));

            match opened {
                Ok((reveal, _beacon)) => {
                    last_revealed_day = Some(day);
                    info!(
                        day = reveal.day_number,
                        title = %reveal.title,
                        seed = %hex_seed(&reveal.seed),
                        "Daily reveal: today's Descent rolled — {}",
                        reveal.title
                    );
                    announce(&http, &reveal).await;
                }
                Err(why) => {
                    warn!("Daily reveal did not fire (will retry next tick): {why}");
                }
            }
        }
    });
}

/// Announce today's reveal to the configured channel, if one is set (`DESCENT_ANNOUNCE_CHANNEL_ID`
/// env). No channel configured → the reveal is logged only (the roll still happened). A live posting
/// surface (a rich embed, a pinned spectator message) is the frontend lane above this core.
async fn announce(http: &Http, reveal: &DailyReveal) {
    let Some(channel_id) = std::env::var("DESCENT_ANNOUNCE_CHANNEL_ID")
        .ok()
        .and_then(|s| s.trim().parse::<u64>().ok())
    else {
        return;
    };
    let body = format!(
        "**{}** · today's Descent is open. A beacon-seeded, permadeath run everyone plays; a WON \
         run ranks on the no-cheat board. Descend with `/descent play`.",
        reveal.title
    );
    if let Err(e) = ChannelId::new(channel_id)
        .send_message(http, CreateMessage::new().content(body))
        .await
    {
        warn!("Daily reveal announcement failed to post: {e}");
    }
}

/// The day seed as hex (for the reveal log line).
fn hex_seed(seed: &CommittedSeed) -> String {
    seed.as_bytes()[..4]
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use dreggnet_offerings::character::InMemoryCharacterStore;
    use dreggnet_offerings::daily_descent::daily_scene;

    /// A SECOND, genuinely-different VERIFIED beacon (an offline hash-chain test beacon that passes
    /// `verify_beacon_round`) — stands in for "tomorrow's" drand round without a network, so the
    /// new-day roll is driven deterministically.
    fn a_second_verified_beacon() -> DailyBeacon {
        use dregg_dice::{Beacon, BeaconSchedule, HashChainBeacon};
        let root = [0x5c; 32];
        let length = 16;
        let round = 3;
        let hc = HashChainBeacon::new(
            root,
            length,
            b"drand/quicknet-test".to_vec(),
            BeaconSchedule {
                base_round: round,
                stride: 0,
            },
        );
        let output = hc.round_output(round);
        let beacon = DailyBeacon::from_parts(hc.params(), round, output, vec![]);
        beacon
            .verify()
            .expect("the test hash-chain beacon verifies");
        beacon
    }

    /// THE HARD GATE, DRIVEN: the scheduler firing opens today's Descent with today's BEACON SEED;
    /// a same-day re-tick is an idempotent no-op; a simulated NEW DAY (a different verified beacon)
    /// rolls a genuinely DIFFERENT dungeon.
    #[test]
    fn the_cron_opens_todays_descent_and_a_new_day_rolls_a_new_dungeon() {
        let off = DailyDescentOffering::new(InMemoryCharacterStore::new());
        let mut board = Registry::new();
        let mut clock = RevealClock::new();

        // Today's beacon (the pinned published round — verifies offline).
        let today = procgen_dregg::beacon::pinned_fallback_beacon();
        let today_seed = today.seed().expect("today's beacon seed");

        // (1) The scheduler fires for day D → the daily offering OPENS with today's beacon seed.
        let day_d = 20_000;
        let r0 = reveal_day(&mut clock, &off, &mut board, day_d, &today)
            .expect("the reveal fires")
            .expect("a new day reveals");
        assert_eq!(
            r0.seed.as_bytes(),
            today_seed.as_bytes(),
            "the reveal opened today's world with today's BEACON seed"
        );
        assert_eq!(clock.last(), Some(day_d), "the clock advanced to day D");
        assert!(
            board.universe(r0.universe_id).is_some(),
            "today's world was published to the no-cheat board"
        );

        // (2) A same-day re-tick is an idempotent no-op (strictly-monotonic day tooth).
        assert!(
            reveal_day(&mut clock, &off, &mut board, day_d, &today)
                .expect("no error")
                .is_none(),
            "the same day does NOT re-reveal (the daily cannot be double-rolled)"
        );
        // A STALE day (earlier than the last) is likewise a no-op.
        assert!(
            reveal_day(&mut clock, &off, &mut board, day_d - 1, &today)
                .expect("no error")
                .is_none(),
            "an earlier day does not roll"
        );

        // (3) A SIMULATED NEW DAY with a different verified beacon → a DIFFERENT dungeon.
        let tomorrow = a_second_verified_beacon();
        let tomorrow_seed = tomorrow.seed().expect("tomorrow's beacon seed");
        assert_ne!(
            today_seed.as_bytes(),
            tomorrow_seed.as_bytes(),
            "a different beacon → a different daily seed"
        );
        let r1 = reveal_day(&mut clock, &off, &mut board, day_d + 1, &tomorrow)
            .expect("the reveal fires")
            .expect("the new day rolls");
        assert_eq!(
            r1.seed.as_bytes(),
            tomorrow_seed.as_bytes(),
            "the new day opened with the new beacon's seed"
        );
        assert_eq!(clock.last(), Some(day_d + 1), "the clock advanced a day");
        // A genuinely different world: the drawn scene source differs.
        assert_ne!(
            daily_scene(&r0.seed).source,
            daily_scene(&r1.seed).source,
            "a new day's verified beacon gives a DIFFERENT dungeon"
        );
    }

    /// A FORGED beacon opens NO day (fail-closed) — the daily cannot be rolled from a faked reveal.
    /// NON-VACUOUS: the honest beacon rolls the day.
    #[test]
    fn a_forged_beacon_does_not_roll_the_day() {
        let off = DailyDescentOffering::new(InMemoryCharacterStore::new());
        let mut board = Registry::new();
        let mut clock = RevealClock::new();

        // Tamper the pinned round's signature — the pairing check must reject it on open.
        let mut sig = hex::decode(procgen_dregg::beacon::PINNED_FALLBACK_SIG_HEX).unwrap();
        sig[0] ^= 0x01;
        let forged = DailyBeacon::quicknet(procgen_dregg::beacon::PINNED_FALLBACK_ROUND, sig);
        assert!(
            reveal_day(&mut clock, &off, &mut board, 20_000, &forged).is_err(),
            "a forged beacon does not open (and does not roll) the day"
        );
        assert_eq!(
            clock.last(),
            None,
            "a failed reveal did not advance the clock"
        );

        // NON-VACUOUS: the honest beacon rolls the day.
        let honest = procgen_dregg::beacon::pinned_fallback_beacon();
        assert!(
            reveal_day(&mut clock, &off, &mut board, 20_000, &honest)
                .expect("the honest reveal fires")
                .is_some(),
            "the honest beacon rolls the day"
        );
    }
}
