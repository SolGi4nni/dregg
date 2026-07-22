//! Discord mounting for the Lean-authored Descent.
//!
//! The game and its surface live in
//! [`dreggnet_offerings::native_descent::NativeDescentOffering`]. This module
//! supplies only the Discord store metadata used by the generic `/play`
//! adapter; it contains no game rules and no second Descent state machine.

use std::sync::OnceLock;

use dreggnet_offerings::Offering;
use dreggnet_offerings::native_descent::NativeDescentOffering;

use crate::commands::offering::{DiscordOffering, Store};

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
