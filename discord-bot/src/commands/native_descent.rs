//! Discord mounting for the Lean-authored Descent.
//!
//! The game and its surface live in
//! [`dreggnet_offerings::native_descent::NativeDescentOffering`]. This module
//! supplies only the Discord store metadata used by the generic `/play`
//! adapter; it contains no game rules and no second Descent state machine.

use std::sync::OnceLock;

use dreggnet_offerings::Offering;
use dreggnet_offerings::native_descent::NativeDescentOffering;
use procgen_dregg::CommittedSeed;

use crate::commands::offering::{DiscordOffering, Store};

/// **Today's verified drand day, as the native Descent's provenance source.** Rides the SAME
/// resolution `/descent` uses ([`crate::commands::descent::resolve_todays_beacon`] — the reveal
/// cron's live cached round, else the pinned published round), and `DailyBeacon::seed` runs the
/// BLS pairing check before it derives anything, so a reveal that does not verify yields `None`
/// and the open is refused. No network happens here: the cron owns the fetch.
pub fn todays_descent_day() -> Option<CommittedSeed> {
    crate::commands::descent::resolve_todays_beacon()
        .seed()
        .ok()
}

/// **The LIVE native Descent** — the constructor `/play offering:descent` opens through.
///
/// The day is re-resolved at EVERY open (the bot process outlives many UTC days), and the run
/// deploys on `native_descent_run_day_seed(day, seed)`, so a run's banked relics mint under a
/// provenance root that could not exist before that day's round was revealed: nobody — including
/// the operator — can pre-compute or grind the day's relic ids. Fail-closed: no verified day, no
/// session; it never degrades to the pre-computable deploy-seed-derived root.
pub fn live_offering() -> NativeDescentOffering {
    NativeDescentOffering::on_day_source(todays_descent_day)
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
