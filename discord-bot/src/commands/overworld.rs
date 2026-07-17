//! `/play overworld` — **the region map above dungeon + character, on Discord** (backlog #23,
//! the 13th `/play` key).
//!
//! [`dreggnet_offerings::overworld::OverworldOffering`] is the real thing — a deployed
//! region cell where TRAVEL is executor-gated on VERIFIED dungeon clears (a locked road is a
//! real `Refused`, a clear fires only after the run re-verifies by replay) — but it does not
//! `impl Offering` (its `open` takes the traveller's identity; travel/clear are inherent
//! methods). [`OverworldPlay`] is the thin bot-side adapter (the same move as
//! `portfolio::SeatedTug`): it maps the trait surface onto the inherent one, changing NOTHING
//! in the crate. The generic adapter then does the rest — buttons fire real region turns,
//! `verify` re-drives the whole traversal + every cleared dungeon by replay.
//!
//! HONEST SCOPE: the traversal is the CHANNEL's shared one (the session identity is derived
//! from the channel seed, matching how `/play trade|craft` open per-channel worlds); the
//! per-identity durable overworld is the crate's own named follow-up. "Clear" auto-plays the
//! location's dungeon to the win and credits it ONLY after replay re-verification
//! ([`OverworldOffering::play_and_clear`]) — interactive dungeon-play-through-the-overworld
//! is the next resolution.
//!
//! Registration residual (Repair applies centrally): the `"overworld"` `PLAY_KEYS` entry +
//! `/play` match arm (`commands/portfolio.rs`) and the `route_component`/`route_modal` key
//! arms (`commands/offering.rs`).

use std::sync::OnceLock;

use deos_view::ViewNode;
use dreggnet_offerings::overworld::{OverworldOffering, OverworldSession};
use dreggnet_offerings::{
    Action, DreggIdentity, Offering, OfferingError, Outcome, RunCost, SessionConfig, Surface,
    VerifyReport,
};

use crate::commands::offering::{DiscordOffering, Store};

/// The overworld mounted on the generic Discord adapter — a trait-surface shim over the
/// crate's inherent-method offering (nothing in `dreggnet-offerings` is modified).
pub struct OverworldPlay {
    inner: OverworldOffering,
}

impl OverworldPlay {
    /// Over the concrete `deepening_ways` region (four universes, hub-and-branch).
    pub fn new() -> Self {
        OverworldPlay {
            inner: OverworldOffering::new(),
        }
    }
}

impl Default for OverworldPlay {
    fn default() -> Self {
        OverworldPlay::new()
    }
}

/// The channel-shared traveller identity: a stable derivation from the session seed (the
/// channel id), hex-shaped like every other derived [`DreggIdentity`].
fn channel_traveller(seed: u64) -> DreggIdentity {
    let mut h = blake3::Hasher::new();
    h.update(b"discord-overworld-traveller/v1");
    h.update(&seed.to_le_bytes());
    DreggIdentity(hex::encode(h.finalize().as_bytes()))
}

impl Offering for OverworldPlay {
    type Session = OverworldSession;

    fn open(&self, cfg: SessionConfig) -> Result<OverworldSession, OfferingError> {
        let who = channel_traveller(cfg.seed.unwrap_or(0));
        self.inner.open(who, cfg)
    }

    /// The affordances: TRAVEL to every other location (dimmed when its road is gated on an
    /// uncleared prerequisite — the cap tooth shown, not hidden; the executor still referees
    /// a forged press), and CLEAR where you stand.
    fn actions(&self, s: &OverworldSession) -> Vec<Action> {
        let here = s.current_location();
        let open = s.available_destinations();
        let mut out = Vec::new();
        for (i, loc) in s.map().locations.iter().enumerate() {
            if loc.id == here {
                out.push(Action::new(
                    format!("Clear {}", loc.id),
                    "clear",
                    i as i64,
                    !s.is_cleared(&loc.id),
                ));
            } else {
                out.push(Action::new(
                    format!("Travel to {}", loc.id),
                    "travel",
                    i as i64,
                    open.contains(&loc.id),
                ));
            }
        }
        out
    }

    fn advance(&self, s: &mut OverworldSession, input: Action, _actor: DreggIdentity) -> Outcome {
        let Some(loc) = s
            .map()
            .locations
            .get(input.arg as usize)
            .map(|l| l.id.clone())
        else {
            return Outcome::Refused(format!("no location #{} in this region", input.arg));
        };
        match input.turn.as_str() {
            // A real region-cell turn: a locked road is the executor's OWN refusal.
            "travel" => self.inner.travel(s, &loc),
            // Auto-play the location's dungeon to the WIN; credit fires ONLY after the run
            // re-verifies by replay (the fail-closed completion gate).
            "clear" => match self.inner.play_and_clear(s, &loc) {
                Ok(receipt) => Outcome::Landed {
                    receipt,
                    ended: false,
                },
                Err(e) => Outcome::Refused(e.to_string()),
            },
            other => Outcome::Refused(format!("`{other}` is not an overworld turn")),
        }
    }

    /// Replay the WHOLE traversal on a fresh identically-seeded region cell + re-verify every
    /// cleared dungeon's playthrough — the crate's own tooth, surfaced verbatim.
    fn verify(&self, s: &OverworldSession) -> VerifyReport {
        self.inner.verify(s)
    }

    fn render(&self, s: &OverworldSession) -> Surface {
        let here = s.current_location();
        let open = s.available_destinations();
        let mut lines = vec![ViewNode::Text(format!("You stand at **{here}**."))];
        for loc in &s.map().locations {
            let mark = if s.is_cleared(&loc.id) {
                "✅ cleared (verified by replay)"
            } else {
                "· uncleared"
            };
            let you = if loc.id == here { "  ← you" } else { "" };
            lines.push(ViewNode::Text(format!("**{}** — {mark}{you}", loc.id)));
        }
        lines.push(ViewNode::Text(if open.is_empty() {
            "No roads are open from here — clear this location to unlock its gated roads."
                .to_string()
        } else {
            format!("Open roads: {}", open.join(", "))
        }));
        Surface(ViewNode::Section {
            title: format!(
                "Overworld — {} ({} / {} cleared)",
                s.map().id,
                s.cleared_count(),
                s.map().locations.len()
            ),
            tag: "accent".to_string(),
            children: lines,
        })
    }

    fn price(&self, _input: &Action) -> RunCost {
        RunCost::free()
    }
}

impl DiscordOffering for OverworldPlay {
    const KEY: &'static str = "overworld";
    const TITLE: &'static str = "Overworld";
    const COLOR: u32 = 0x2E8B57;
    const TAGLINE: &'static str =
        "the region map above the dungeons · travel is executor-gated on VERIFIED clears";
    fn store() -> &'static Store<Self> {
        static SESSIONS: OnceLock<Store<OverworldPlay>> = OnceLock::new();
        SESSIONS.get_or_init(Store::spawn)
    }
    fn status_line(&self, session: &Self::Session) -> String {
        format!(
            "{} verified turns · {} / {} cleared",
            self.verify(session).turns,
            session.cleared_count(),
            session.map().locations.len()
        )
    }
}

#[cfg(test)]
mod tests {
    //! The overworld DRIVEN through the SAME generic-adapter calls a live `/play` open +
    //! button press take: a gated road is a REAL refusal, a clear re-verifies, the road opens.
    use dreggnet_offerings::SessionConfig;

    use super::*;
    use crate::commands::offering::{self, Driven, close_in, drive, fire_id, with_live};

    fn actor(tag: &str) -> DreggIdentity {
        DreggIdentity(format!("{tag}{}", "0".repeat(64 - tag.len())))
    }

    /// Locate a location's index (the button `arg`) by id.
    fn arg_of(channel: u64, id: &str) -> i64 {
        with_live::<OverworldPlay, _>(channel, {
            let id = id.to_string();
            move |live| {
                live.session
                    .map()
                    .locations
                    .iter()
                    .position(|l| l.id == id)
                    .map(|i| i as i64)
            }
        })
        .flatten()
        .expect("the location exists")
    }

    /// **The 13th `/play` key is real teeth, not a picture**: a travel down a gated road is
    /// the executor's OWN refusal while nothing is cleared; clearing the current location
    /// (auto-play + replay re-verification) then opens it, and the whole traversal
    /// re-verifies by replay.
    #[test]
    fn overworld_gates_travel_on_verified_clears() {
        let channel = 772_300u64;
        close_in::<OverworldPlay>(channel);
        offering::open_in(
            channel,
            OverworldPlay::new,
            SessionConfig::with_seed(channel),
        )
        .expect("the overworld opens");
        let me = actor("ow");

        let (here, gated) = with_live::<OverworldPlay, _>(channel, |live| {
            let here = live.session.current_location();
            let open = live.session.available_destinations();
            let gated = live
                .session
                .map()
                .locations
                .iter()
                .map(|l| l.id.clone())
                .find(|id| *id != here && !open.contains(id));
            (here, gated)
        })
        .expect("live");

        // A gated road refuses BEFORE any clear (the region has at least one gated edge).
        if let Some(locked) = &gated {
            let arg = arg_of(channel, locked);
            match drive::<OverworldPlay>(
                channel,
                &fire_id(OverworldPlay::KEY, "travel", arg),
                me.clone(),
            ) {
                Driven::Fired(Outcome::Refused(why)) => {
                    assert!(!why.is_empty(), "the refusal carries the executor's reason")
                }
                other => panic!("a locked road must be a real refusal, got {other:?}"),
            }
        }

        // Clear where we stand: auto-play to the WIN, credited only after replay re-verifies.
        let here_arg = arg_of(channel, &here);
        match drive::<OverworldPlay>(
            channel,
            &fire_id(OverworldPlay::KEY, "clear", here_arg),
            me.clone(),
        ) {
            Driven::Fired(outcome) => assert!(
                outcome.landed(),
                "clearing the start location lands a real receipt: {outcome:?}"
            ),
            other => panic!("a clear press must drive a real turn, got {other:?}"),
        }

        // The whole traversal (region ops + the cleared dungeon's playthrough) re-verifies.
        let report = offering::verify_live::<OverworldPlay>(channel).expect("live");
        assert!(
            report.verified,
            "the traversal re-verifies: {}",
            report.detail
        );

        close_in::<OverworldPlay>(channel);
    }
}
