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
    use dreggnet_offerings::{Action, DreggIdentity, Outcome, SessionConfig};

    use super::*;
    use crate::commands::offering::{
        Driven, close_in, drive, fire_id, open_in, verify_live, with_live,
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
            &fire_id(NativeDescentOffering::KEY, &first.turn, first.arg),
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
            &fire_id(NativeDescentOffering::KEY, &legal_now.turn, legal_now.arg),
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
}
