//! Discord mounting for the Lean-authored Descent.
//!
//! The game and its surface live in
//! [`dreggnet_offerings::native_descent::NativeDescentOffering`]. This module
//! supplies only the Discord store metadata used by the generic `/play`
//! adapter; it contains no game rules and no second Descent state machine.
//!
//! # THE SHARE PATH
//!
//! A finished run leaves the channel as a link to its own run-card —
//! `{DESCENT_WEB_BASE}/descent/native/run/{id}` — the page that paints the shaft as it stood when
//! the light went out. [`share_finished_run`] is what puts it there: it POSTs the session's exact
//! [`PortableRecord`] to the web's native lane (`POST /descent/native/submit`), which re-executes
//! the whole tape through a fresh Offering and mints a card ONLY for a record that replays
//! byte-for-byte. The bot never asserts a run happened; it hands over the record and links what
//! the server's own replay produced.
//!
//! Two properties this depends on, both load-bearing:
//!
//! * **the day.** The web admits a native record only if its normalized seed is the one TODAY'S
//!   committed day commits to (`dreggnet_web::descent::native_seed_for_committed_day`). The
//!   browser at `/descent/play` opens on exactly that seed; so does this bot, via
//!   [`open_config_on_todays_day`]. Before that, every channel opened on its own channel id — a
//!   *different* one of the sixteen drawn maps per channel, and a record the board could never
//!   admit.
//! * **the message shape.** The link rides a public message's CONTENT
//!   ([`ack::followup_public`]), never an embed field: Discord unfurls OpenGraph only from
//!   content, and the run-card's `<head>` tags are the entire point of sharing it.

use std::collections::HashMap;
use std::sync::{Mutex, OnceLock};

use serenity::all::{ComponentInteraction, Context};

use dreggnet_offerings::native_descent::NativeDescentOffering;
use dreggnet_offerings::native_descent_wire::PortableRecord;
use dreggnet_offerings::{Audience, Offering, SessionConfig, project_for_audience};
use procgen_dregg::CommittedSeed;

use crate::commands::ack;
use crate::commands::offering::{DiscordOffering, Store, truncate, with_live};

/// **Today's verified drand day, as the native Descent's provenance source.**
///
/// This is [`crate::commands::descent::resolve_todays_day`] — the SINGLE day-selection every live
/// Descent surface shares, and the one `dreggnet_web::descent::todays_day` mirrors: today's
/// BLS-verified drand round when the reveal cron has one (`d{utc}-r{round}`), else the offline
/// date-derived day (`d{utc}-off`) that both processes derive purely and therefore agree on.
///
/// ⚑ It used to be [`crate::commands::descent::resolve_todays_beacon`] instead, whose fallback is
/// the PINNED quicknet round rather than the offline day. The doc-comment claimed that "rides the
/// SAME resolution `/descent` uses" — it did not: `/descent`'s served day is `resolve_todays_day`.
/// The consequence was not cosmetic. A pinned round paired with today's UTC day is refused by
/// `descent_day::resolve_day_key` as `RoundNotScheduled`, so on the fallback path the native
/// Descent played a world NO other process could re-derive: unshareable by construction. Both
/// branches here are days the web derives for itself, so a run played in Discord re-executes there.
pub fn todays_descent_day() -> Option<CommittedSeed> {
    Some(crate::commands::descent::resolve_todays_day().0.seed)
}

/// **The LIVE native Descent** — the constructor `/play offering:descent` opens through.
///
/// The day is re-resolved at EVERY open (the bot process outlives many UTC days), and the run
/// deploys on `native_descent_run_day_seed(day, seed)`. It never degrades to the pre-computable
/// deploy-seed-derived root: the binding is always a committed DAY.
///
/// What that day is worth is exactly [`todays_descent_day`]'s honesty. On the live branch (the
/// reveal cron holds today's BLS-verified round) a run's banked relics mint under a provenance
/// root that could not exist before that round was revealed — nobody, operator included, can
/// pre-compute or grind the day's relic ids. On the offline branch the day is date-derived and
/// therefore publicly pre-computable; the surface labels it as such (`BeaconStatus::PinnedFallback`,
/// and the web card's `offline-date` source) rather than presenting it as a fresh reveal.
pub fn live_offering() -> NativeDescentOffering {
    NativeDescentOffering::on_day_source(todays_descent_day)
}

/// **The session config `/play open offering:descent` opens on — TODAY'S day, not the channel.**
///
/// `NativeDescentOffering::open` normalizes this to `seed % 251 + 1` and deploys on
/// `native_descent_run_day_seed(day, normalized)`. Two consequences, and both are the reason this
/// function exists instead of a bare `SessionConfig::with_seed(channel)`:
///
/// 1. **the daily is actually daily.** The drawn map (which floor each relic sits on, how much
///    vitality each guardian has) is a function of the run day-seed, so a channel-derived seed gave
///    every Discord channel a different one of the sixteen maps — and a different map again from
///    the one the browser plays at `/descent/play`. Today's committed prefix is exactly what
///    `/descent/play` publishes to the tab as `nativeSeed`, so all three now open the same dungeon.
/// 2. **the run is shareable.** `POST /descent/native/submit` admits a record only when its
///    normalized seed is the one today's committed day commits to. A channel-seeded run is refused
///    there, which is why the native lane had no share link at all.
///
/// It also BINDS the channel to the day key the record will be submitted under, so a run that
/// finishes after UTC midnight is still ingested against the day it was played in rather than
/// silently re-executed against tomorrow's world.
pub fn open_config_on_todays_day(channel: u64) -> SessionConfig {
    let (day, _status) = crate::commands::descent::resolve_todays_day();
    bound_days()
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner())
        .insert(channel, day.key.clone());
    SessionConfig::with_seed(native_seed_word(&day.seed))
}

/// **The raw number a day is opened on** — the committed seed's first little-endian word.
///
/// The `% 251 + 1` normalization belongs to `NativeDescentOffering::open` and is NOT repeated
/// here; this is the same unnormalized prefix `/descent/play` publishes to the browser as
/// `nativeSeed`, so the tab and the bot hand the game boundary the identical input.
fn native_seed_word(day_seed: &CommittedSeed) -> u64 {
    let bytes = day_seed.as_bytes();
    u64::from(u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]))
}

/// Channel → the day key its live Descent was opened on (set by [`open_config_on_todays_day`]).
fn bound_days() -> &'static Mutex<HashMap<u64, String>> {
    static BOUND: OnceLock<Mutex<HashMap<u64, String>>> = OnceLock::new();
    BOUND.get_or_init(|| Mutex::new(HashMap::new()))
}

/// Channel → the journal root of the run already published from it, so a finished run is ingested
/// and announced EXACTLY once however many times its dead board is pressed afterwards.
fn published_roots() -> &'static Mutex<HashMap<u64, String>> {
    static PUBLISHED: OnceLock<Mutex<HashMap<u64, String>>> = OnceLock::new();
    PUBLISHED.get_or_init(|| Mutex::new(HashMap::new()))
}

impl DiscordOffering for NativeDescentOffering {
    const KEY: &'static str = "descent";
    const TITLE: &'static str = "The Descent";
    const COLOR: u32 = 0xB58B4A;
    const TAGLINE: &'static str =
        "Lean-authored custody dungeon · finite light · attenuating keys · banked relics";

    fn store() -> &'static Store<Self> {
        static SESSIONS: OnceLock<Store<NativeDescentOffering>> = OnceLock::new();
        SESSIONS.get_or_init(Store::spawn)
    }

    fn open_hint() -> String {
        "/play offering:descent".to_string()
    }

    fn status_line(&self, session: &Self::Session) -> String {
        let verification = self.verify(session);
        match session.completion() {
            Some(completion) => format!(
                "{} verified turns · {} banked relics{}",
                verification.turns,
                completion.banked_relics.len(),
                if completion.crowned {
                    " · crowned"
                } else {
                    ""
                }
            ),
            None => format!(
                "{} verified turns · depth {} · revision {}",
                verification.turns,
                session.game().sim().depth,
                session.revision()
            ),
        }
    }
}

// ═════════════════════════════════════════════════════════════════════════════════════════════
// THE SHARE PATH — a finished run leaves the channel as its own run-card.
// ═════════════════════════════════════════════════════════════════════════════════════════════

/// A run that is OVER, packaged for the web's native lane.
struct FinishedRun {
    /// The day key the record must be ingested against — the day the session was OPENED on, not
    /// whatever "today" is when the last press lands.
    day_key: String,
    /// The exact portable record `POST /descent/native/submit` re-executes.
    record: PortableRecord,
    /// The board as text — [`deos_view::text::render_text`] over the session's own `ViewNode`
    /// surface, which is the same `coordgrid_text` / `progress_text` projection the run-card's
    /// copyable form and every chat transport paint. Not a second drawing of the dungeon.
    board: String,
}

/// **Is this run finished, and if so what does it hand over?**
///
/// Two ways a descent ends: a proved exit (`flee`, which banks the pack and mints a completion),
/// or the light running out — every verb costs at least one light, so a run that cannot pay one can
/// never move again and every affordance goes dark. Both are read here off the LIVE session; the
/// server is still the referee (a record that is only an exact prefix is refused by the ingest with
/// its own reason), so this test can cost at most one wasted POST and can never mint a link.
fn finished_run(channel: u64) -> Option<FinishedRun> {
    let day_key = bound_days()
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner())
        .get(&channel)
        .cloned()?;
    with_live::<NativeDescentOffering, _>(channel, move |live| {
        let projection = project_for_audience(&live.offering, &live.session, &Audience::Shared);
        let over = live.session.completion().is_some()
            || !projection.actions.iter().any(|action| action.enabled);
        if !over {
            return None;
        }
        Some(FinishedRun {
            day_key,
            record: PortableRecord::from_record(&live.session.export_record()),
            board: deos_view::text::render_text(projection.surface.view()),
        })
    })
    .flatten()
}

/// POST the record to the web's native lane and return the ABSOLUTE run-card URL its own replay
/// minted. `Err` carries why there is no card — never a link that would 404, and never a link to a
/// run the server did not itself re-execute.
async fn publish(base: &str, finished: &FinishedRun) -> Result<String, String> {
    let client = reqwest::Client::builder()
        .timeout(std::time::Duration::from_secs(15))
        .build()
        .map_err(|error| format!("http client: {error}"))?;
    let response = client
        .post(format!("{base}/descent/native/submit"))
        .json(&serde_json::json!({
            "day": finished.day_key,
            "record": finished.record,
        }))
        .send()
        .await
        .map_err(|error| format!("native submit: {error}"))?;
    let status = response.status();
    let body: serde_json::Value = response
        .json()
        .await
        .map_err(|error| format!("native submit response ({status}): {error}"))?;
    if !status.is_success() || body.get("verified").and_then(|v| v.as_bool()) != Some(true) {
        return Err(format!(
            "the board refused the record ({status}): {}",
            body.get("error")
                .or_else(|| body.get("detail"))
                .and_then(|e| e.as_str())
                .unwrap_or("no reason given")
        ));
    }
    // The path the SERVER minted for the record it replayed — never a path this bot composed from
    // an id it guessed.
    let share = body
        .get("share")
        .and_then(|s| s.as_str())
        .ok_or_else(|| "the board accepted the record but named no card".to_string())?;
    Ok(format!("{base}{share}"))
}

/// **Publish a finished native run to the channel** — the one place `/play offering:descent` emits
/// a run link, and it emits the NATIVE card (`/descent/native/run/{id}`), the page that paints the
/// shaft. Called after every press has been rendered; a no-op until the run is over, and at most
/// once per run.
///
/// The message is public content, not an embed field, because Discord builds the OpenGraph preview
/// only from a URL in a message body (see [`ack::followup_public`]). The text board rides the same
/// message so the run is legible without a click — the card's copyable form and this are the same
/// projection.
///
/// Silent when `DESCENT_WEB_BASE` is unset (there is no host to link) and when the board refuses
/// the record; the refusal is logged with its reason rather than shown to the player, exactly as a
/// missing link is better than a lying one.
pub async fn share_finished_run(ctx: &Context, component: &ComponentInteraction) {
    let Some(base) = crate::commands::descent::descent_web_base() else {
        return;
    };
    let channel = component.channel_id.get();
    let Some(finished) = finished_run(channel) else {
        return;
    };
    // ONCE per run: after the settlement every remaining press lands on a dead board, and each one
    // would otherwise re-POST the same record and re-announce the same card.
    {
        let mut published = published_roots()
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        if published.get(&channel) == Some(&finished.record.root_hex) {
            return;
        }
        published.insert(channel, finished.record.root_hex.clone());
    }
    match publish(&base, &finished).await {
        Ok(url) => {
            let crowned = finished
                .record
                .completion
                .as_ref()
                .is_some_and(|completion| completion.crowned);
            let headline = match (&finished.record.completion, crowned) {
                (Some(_), true) => "**Crowned.** The Crown of the Deep came back up the shaft.",
                (Some(_), false) => "**Banked.** Everything in the pack is theirs now.",
                (None, _) => {
                    "**The light is dead.** Whatever was in that pack is still down there."
                }
            };
            // The BOARD is what gets clamped, never the URL: Discord refuses a message over 2000
            // characters outright, and a share message that lost its link is the failure this
            // whole path exists to remove. The fence is closed after the clamp so a long board
            // cannot leave the message ending mid-code-block either.
            ack::followup_public(
                ctx,
                component,
                // The URL sits on its own line and OUTSIDE every code fence: Discord does not
                // unfurl a URL inside backticks, so the card would never render.
                &format!(
                    "{headline}\n{url}\n```\n{}\n```",
                    truncate(&finished.board, 1700)
                ),
            )
            .await;
        }
        Err(why) => {
            // Let the next press try again — the run did not become shareable by our failing.
            published_roots()
                .lock()
                .unwrap_or_else(|poisoned| poisoned.into_inner())
                .remove(&channel);
            tracing::warn!(
                channel,
                day = %finished.day_key,
                reason = %why,
                "the native Descent run-card was NOT published — the channel got no share link"
            );
        }
    }
}

#[cfg(test)]
mod tests {
    use dreggnet_offerings::{
        Action, DreggIdentity, Outcome, SessionConfig, SessionId, SessionMoveLog,
    };

    use super::*;
    use crate::cipherclerk::UserCipherclerk;
    use crate::commands::offering::{
        Driven, Live, action_rows, close_in, drive, fire_id, fire_id_in, open_in, outcome_note,
        parse_press, surface_of, verify_live, with_live,
    };

    fn actor(tag: &str) -> DreggIdentity {
        DreggIdentity(format!("{tag}{}", "0".repeat(64 - tag.len())))
    }

    /// The exact seed test `dreggnet_web::descent::verify_native_record` applies to every submitted
    /// record: `native_seed_for_committed_day` = the committed seed's first little-endian word,
    /// `% 251 + 1`. Written out here rather than imported because `dreggnet-web` is a different
    /// workspace and this bot cannot link it — so it is repeated ONCE, in a test, where a drift
    /// shows up as a red assertion instead of as a silently refused submission.
    fn what_the_web_will_admit(day_seed: &CommittedSeed) -> u8 {
        let bytes = day_seed.as_bytes();
        let word = u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]);
        ((u64::from(word) % 251) + 1) as u8
    }

    /// Drive the channel's live run with its first legal affordance until nothing is legal or it
    /// settles. Returns the number of landed turns.
    fn descend_until_over(channel: u64, me: &DreggIdentity) -> usize {
        let mut turns = 0;
        for _ in 0..256 {
            let over = with_live::<NativeDescentOffering, _>(channel, |live| {
                live.session.completion().is_some()
            })
            .unwrap_or(true);
            if over {
                break;
            }
            let next = with_live::<NativeDescentOffering, _>(channel, |live| {
                live.offering
                    .actions(&live.session)
                    .into_iter()
                    .find(|action| action.enabled)
            })
            .flatten();
            let Some(action) = next else { break };
            let Some(id) = fire_id_in::<NativeDescentOffering>(channel, &action.turn, action.arg)
            else {
                break;
            };
            if !matches!(
                drive::<NativeDescentOffering>(channel, &id, me.clone()),
                Driven::Fired(Outcome::Landed { .. })
            ) {
                break;
            }
            turns += 1;
        }
        turns
    }

    /// **THE SHARE LINK IS ONLY REAL IF THE BOARD WILL ADMIT THE RECORD.**
    ///
    /// `POST /descent/native/submit` refuses any record whose normalized seed is not the one
    /// today's committed day commits to. `/play open offering:descent` used to open on the CHANNEL
    /// ID, so every Discord run was refused before it was even replayed — which is why the native
    /// lane had no share link at all, and why each channel was also playing a different one of the
    /// sixteen drawn maps than the web's daily.
    ///
    /// NON-VACUOUS: the old channel-seeded open is asserted to produce the seed the web REFUSES.
    #[test]
    fn the_bot_opens_on_the_day_seed_the_web_will_admit() {
        let channel = 0x5EED_0001;
        let (day, _status) = crate::commands::descent::resolve_todays_day();
        let expected = what_the_web_will_admit(&day.seed);

        close_in::<NativeDescentOffering>(channel);
        open_in(
            channel,
            live_offering,
            super::open_config_on_todays_day(channel),
        )
        .expect("today's Descent opens");
        let record = with_live::<NativeDescentOffering, _>(channel, |live| {
            PortableRecord::from_record(&live.session.export_record())
        })
        .expect("the session exports its record");
        assert_eq!(
            record.seed, expected,
            "the bot's run carries seed {} but the board admits only {expected} for day {}",
            record.seed, day.key
        );

        // ...and the day key the record will be submitted under is the one BOTH processes derive.
        assert_eq!(
            super::bound_days()
                .lock()
                .unwrap()
                .get(&channel)
                .map(String::as_str),
            Some(day.key.as_str()),
        );
        close_in::<NativeDescentOffering>(channel);

        // THE CONTROL: the pre-fix open. A channel-seeded run is a run the board refuses. (Guarded
        // against the astronomically unlikely coincidence that this channel id normalizes to the
        // day's seed, which would make the control vacuous rather than wrong.)
        let control_channel = 0x5EED_0002u64;
        if (control_channel % 251) as u8 + 1 != expected {
            close_in::<NativeDescentOffering>(control_channel);
            open_in(
                control_channel,
                live_offering,
                SessionConfig::with_seed(control_channel),
            )
            .expect("a channel-seeded Descent still opens");
            let refused = with_live::<NativeDescentOffering, _>(control_channel, |live| {
                PortableRecord::from_record(&live.session.export_record())
            })
            .expect("the control session exports its record");
            assert_ne!(
                refused.seed, expected,
                "the control must be a record the board REFUSES, or this test proves nothing"
            );
            close_in::<NativeDescentOffering>(control_channel);
        }
    }

    /// **A FINISHED DISCORD RUN IS A RECORD THE INGEST'S OWN GATE ACCEPTS.**
    ///
    /// `dreggnet_web`'s `verify_native_record` is the day-seed check above plus
    /// [`replay_portable_record`] — the ONE exact-replay gate, which lives in `dreggnet-offerings`
    /// and is therefore callable here. This drives a real run to its end through the Discord
    /// adapter, packages it exactly as [`share_finished_run`] does, and puts it through that gate.
    /// A green here plus the seed test above is the pair of conditions the ingest applies.
    #[test]
    fn a_finished_discord_run_passes_the_shared_native_replay_gate() {
        let channel = 0x5EED_0003;
        close_in::<NativeDescentOffering>(channel);
        open_in(
            channel,
            live_offering,
            super::open_config_on_todays_day(channel),
        )
        .expect("today's Descent opens");

        let me = actor("share-path");
        let turns = descend_until_over(channel, &me);
        assert!(turns > 0, "the run must actually move to have a card");

        let finished = super::finished_run(channel).expect(
            "a run with no legal affordance left (or a settlement) is FINISHED and must package",
        );
        assert_eq!(finished.record.events.len(), turns);
        // The two endings the web calls terminal: a proved exit, or the light gone.
        let terminal = finished.record.completion.is_some()
            || finished.record.events.last().is_some_and(|event| {
                event.post.spent + 1 > dreggnet_offerings::native_descent::LIGHT_BREATH
            });
        assert!(
            terminal,
            "the packaged run is neither settled nor out of light — the ingest would refuse it as \
             an exact prefix: {:?}",
            finished.record.completion
        );

        // THE GATE the web runs on every submitted record.
        dreggnet_offerings::native_descent_wire::replay_portable_record(&finished.record)
            .expect("the bot's own record must survive exact native re-execution");

        // The board rides the share message, and it is the SAME projection the run-card's copyable
        // form paints — a coordinate grid, plus the light clock as a literal bar.
        assert!(
            finished.board.contains('·') || finished.board.contains('@'),
            "the share message must carry the shaft board: {}",
            finished.board
        );
        assert!(
            finished.board.contains("light"),
            "the share message must carry the light clock: {}",
            finished.board
        );
        println!(
            "\n===== THE SHARE MESSAGE'S TEXT BOARD =====\n{}\n",
            finished.board
        );
        // The EXACT body the bot POSTs, printed under `--nocapture` so a live end-to-end against a
        // running `dreggnet-web` can be driven from this run's own record rather than a fixture.
        println!(
            "===SUBMIT-BODY-BEGIN===\n{}\n===SUBMIT-BODY-END===",
            serde_json::json!({ "day": finished.day_key, "record": finished.record })
        );

        close_in::<NativeDescentOffering>(channel);
    }

    /// **THE BOARD ACTUALLY REACHES DISCORD.** The sibling lane authored the shaft as a
    /// `ViewNode::CoordGrid` and the vitals as literal `ViewNode::Progress` meters; this drives
    /// the Discord render path a live `/play open offering:descent` takes and asserts the board
    /// SURVIVES it — code-fenced (Discord's embed description is a proportional font, so an
    /// unfenced 11-column shaft shears into noise), meters painted as bars, and every verb
    /// carrying its price.
    ///
    /// It also pins the affordance budget the whole design rests on: the shaft is 66 cells and
    /// Discord allows 25 components per message, so the cells are INERT and the `Menu` is the
    /// single affordance carrier. If a later change makes cells pressable, or grows the verb list
    /// past the cap, `action_rows_at`'s `chunks(5).take(5)` silently DROPS the overflow — a verb
    /// the player can never see or press. This asserts we are under the cap, with room.
    #[test]
    fn the_shaft_map_and_its_meters_reach_the_discord_board() {
        let channel = 0xB0A2D;
        close_in::<NativeDescentOffering>(channel);
        open_in(
            channel,
            NativeDescentOffering::new,
            SessionConfig::with_seed(channel),
        )
        .expect("the Descent opens");

        // Take a few real turns so the board shows a run in motion, not the mouth.
        let me = actor("board-render");
        for _ in 0..3 {
            let next = with_live::<NativeDescentOffering, _>(channel, |live| {
                live.offering
                    .actions(&live.session)
                    .into_iter()
                    .find(|action| action.enabled)
            })
            .flatten();
            let Some(action) = next else { break };
            let Some(id) = fire_id_in::<NativeDescentOffering>(channel, &action.turn, action.arg)
            else {
                break;
            };
            if !matches!(
                drive::<NativeDescentOffering>(channel, &id, me.clone()),
                Driven::Fired(Outcome::Landed { .. })
            ) {
                break;
            }
        }

        let (embed, rows) = with_live::<NativeDescentOffering, _>(channel, |live| {
            surface_of::<NativeDescentOffering>(live)
        })
        .expect("the live session renders");
        let json = serde_json::to_value(&embed).expect("the board embed serializes");
        let description = json["description"]
            .as_str()
            .expect("the board paints a description")
            .to_string();

        // Printed so a human can read the exact thing a channel receives (`--nocapture`).
        println!("\n===== THE DESCENT, AS A DISCORD CHANNEL RECEIVES IT =====\n{description}\n");

        assert!(
            description.contains("```"),
            "the shaft must be CODE-FENCED or a proportional font shears the grid: {description}"
        );
        for meter in ["light", "pack", "banked"] {
            assert!(
                description.contains(meter),
                "the `{meter}` meter must paint on the Discord board: {description}"
            );
        }
        assert!(
            description.contains('\u{2588}') || description.contains('\u{2591}'),
            "a Progress node must render as a literal BAR, not a bare ratio: {description}"
        );
        assert!(
            description.chars().count() <= 4000,
            "the board must fit Discord's embed-description cap or the edit 400s and the \
             surface freezes: {} chars",
            description.chars().count()
        );

        // The affordance budget: ≤5 rows, ≤25 buttons, and nothing silently dropped.
        let rows_json = serde_json::to_value(&rows).expect("the rows serialize");
        let rows_array = rows_json.as_array().expect("rows are an array");
        assert!(
            rows_array.len() <= 5,
            "Discord allows 5 action rows; the board minted {}",
            rows_array.len()
        );
        let buttons: usize = rows_array
            .iter()
            .filter_map(|row| row["components"].as_array().map(|c| c.len()))
            .sum();
        assert!(
            buttons <= 25,
            "Discord allows 25 components per message; the board minted {buttons}"
        );
        let verbs = with_live::<NativeDescentOffering, _>(channel, |live| {
            live.offering.actions(&live.session).len()
        })
        .expect("live");
        assert!(
            verbs <= 24,
            "{verbs} verbs + the standing re-verify row would overflow Discord's component cap \
             and `action_rows_at` would DROP the overflow silently"
        );

        close_in::<NativeDescentOffering>(channel);
    }

    #[test]
    fn generic_discord_path_drives_the_native_executor_and_replays() {
        let channel = 0xDE5CE7;
        close_in::<NativeDescentOffering>(channel);
        open_in(
            channel,
            NativeDescentOffering::new,
            SessionConfig::with_seed(channel),
        )
        .expect("native Descent opens");

        let first = with_live::<NativeDescentOffering, _>(channel, |live| {
            live.offering
                .actions(&live.session)
                .into_iter()
                .find(|action| action.enabled)
                .expect("at least one native action is currently legal")
        })
        .expect("session is live");
        let me = actor("native-descent");
        match drive::<NativeDescentOffering>(
            channel,
            &fire_id_in::<NativeDescentOffering>(channel, &first.turn, first.arg).unwrap(),
            me.clone(),
        ) {
            Driven::Fired(Outcome::Landed { .. }) => {}
            other => panic!("the generic Discord press must land natively: {other:?}"),
        }

        let (bound, revision) = with_live::<NativeDescentOffering, _>(channel, |live| {
            (live.session.actor().cloned(), live.session.revision())
        })
        .expect("session remains live");
        assert_eq!(bound.as_ref(), Some(&me));
        assert_eq!(revision, 1);
        let report = verify_live::<NativeDescentOffering>(channel).expect("session verifies");
        assert!(report.verified, "{}", report.detail);

        // The actor binding is a game boundary, not a presentation hint.
        let legal_now = with_live::<NativeDescentOffering, _>(channel, |live| {
            live.offering
                .actions(&live.session)
                .into_iter()
                .find(|action| action.enabled)
                .unwrap_or_else(|| Action::new("forged", "delve", 0, true))
        })
        .expect("session is live");
        match drive::<NativeDescentOffering>(
            channel,
            &fire_id_in::<NativeDescentOffering>(channel, &legal_now.turn, legal_now.arg).unwrap(),
            actor("intruder"),
        ) {
            Driven::Fired(Outcome::Refused(_)) => {}
            other => panic!("a second actor must not seize the run: {other:?}"),
        }
        assert_eq!(
            with_live::<NativeDescentOffering, _>(channel, |live| live.session.revision()),
            Some(1),
            "refusal is anti-ghost"
        );
        close_in::<NativeDescentOffering>(channel);
    }

    #[test]
    fn discord_preserves_native_actions_and_terminal_share_identity() {
        let offering = NativeDescentOffering::new();
        let mut session = offering
            .open(SessionConfig::with_seed(0xD15C_0A7D))
            .expect("native Descent opens");
        let player = DreggIdentity(
            UserCipherclerk::derive(&[31; 32], 41_001, [7; 32])
                .public_key_hex()
                .to_string(),
        );
        let actions = offering.actions(&session);
        let rows = action_rows::<NativeDescentOffering>(&actions);
        let json = serde_json::to_value(&rows).expect("Discord rows serialize");
        let row_values = json.as_array().expect("Discord rows are an array");
        let buttons: Vec<_> = row_values[..row_values.len() - 1]
            .iter()
            .flat_map(|row| {
                row["components"]
                    .as_array()
                    .expect("an action row has components")
            })
            .collect();
        assert_eq!(
            buttons.len(),
            actions.len(),
            "Discord consumes every native action in native order"
        );
        for (button, action) in buttons.iter().zip(&actions) {
            let custom_id = button["custom_id"].as_str().expect("button custom id");
            assert_eq!(
                custom_id,
                fire_id(NativeDescentOffering::KEY, &action.turn, action.arg)
            );
            assert_eq!(
                parse_press(custom_id),
                Some(crate::commands::offering::Press::Fire {
                    key: NativeDescentOffering::KEY.to_string(),
                    stamp: crate::commands::offering::ControlStamp::PERSISTENT,
                    turn: action.turn.clone(),
                    arg: action.arg,
                })
            );
            assert_eq!(
                button["label"]
                    .as_str()
                    .expect("button label")
                    .starts_with("🔒 "),
                !action.enabled,
                "locked state is visible without becoming a Discord legality rule"
            );
        }
        assert!(
            row_values
                .last()
                .expect("standing verify row")
                .to_string()
                .contains("verifychain:descent"),
            "the ordered game actions are followed by the live verify affordance"
        );

        let locked = actions
            .into_iter()
            .find(|action| !action.enabled)
            .expect("the complete locked catalogue stays visible");
        let before = session.revision();
        let refusal = offering.advance(&mut session, locked, player.clone());
        let reason = match &refusal {
            Outcome::Refused(reason) => reason,
            other => panic!("a locked Discord action must reach the executor: {other:?}"),
        };
        assert!(!reason.trim().is_empty());
        assert!(
            outcome_note(&refusal).contains(reason),
            "Discord preserves the executor's exact locked-action reason"
        );
        assert_eq!(session.revision(), before, "a refusal is anti-ghost");

        let mut ended = false;
        for _ in 0..64 {
            let action = offering
                .actions(&session)
                .into_iter()
                .find(|action| action.enabled)
                .expect("a live native Descent exposes an enabled action");
            match offering.advance(&mut session, action, player.clone()) {
                Outcome::Landed {
                    ended: turn_ended, ..
                } => {
                    if turn_ended {
                        ended = true;
                        break;
                    }
                }
                Outcome::Refused(reason) => {
                    panic!("an enabled native action was refused: {reason}")
                }
            }
        }
        assert!(ended, "the surface-driven line settles within 64 turns");
        let completion = session.completion().expect("terminal settlement");
        assert_eq!(&completion.actor, &player);
        let share_root = completion.root;
        let share_receipt = completion.settlement_receipt_hash;

        let live = Live {
            offering,
            session,
            round: None,
            generation: 1,
            control_head: 64,
            journal: SessionMoveLog::new(
                NativeDescentOffering::KEY,
                SessionId::new("native-descent-render-fixture"),
                SessionConfig::with_seed(0xD15C_0A7D),
            ),
            resume_store: None,
        };
        let (embed, terminal_rows) = surface_of::<NativeDescentOffering>(&live);
        let rendered = serde_json::to_value(embed)
            .expect("terminal embed serializes")
            .to_string();
        assert!(rendered.contains("proof/share record"), "{rendered}");
        assert!(rendered.contains(player.as_str()), "{rendered}");
        assert!(
            rendered.contains(&hex::encode(share_root)),
            "the share root is lossless: {rendered}"
        );
        assert!(
            rendered.contains(&hex::encode(share_receipt)),
            "the share receipt is lossless: {rendered}"
        );
        assert!(
            rendered.contains("re-verify this exact record"),
            "{rendered}"
        );
        assert_eq!(
            terminal_rows.len(),
            1,
            "settlement removes game actions but keeps re-verification"
        );
        assert!(
            serde_json::to_value(&terminal_rows)
                .expect("terminal rows serialize")
                .to_string()
                .contains("verifychain:descent"),
            "Discord keeps a pressable terminal proof check"
        );
    }
}
