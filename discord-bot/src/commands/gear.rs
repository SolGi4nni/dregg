//! `/play gear` + `/play talents` — **the dreggnet-gear progression surfaces on Discord**
//! (backlog #20, the cheap half: both already `impl Offering` in `dreggnet-gear`; these are
//! purely the two `DiscordOffering` blocks the generic adapter needs).
//!
//! * **gear** ([`dreggnet_gear::LoadoutOffering`]) — forge → EQUIP → use: the flaming-sword
//!   ability unlocks BECAUSE you own+equip the peer gear-asset cell at a finalized root — a
//!   KERNEL `ObservedFieldEquals` cross-cell predicate, not a client `if`. Unequipped use is
//!   the executor's own refusal.
//! * **talents** ([`dreggnet_gear::TalentTreeOffering`]) — class-gated, prereq-chained talent
//!   claims priced in banked echoes, with a real RESPEC (a new generation invalidates the old
//!   tree's claims).
//!
//! Both are stateless factories over real substrate cells; the generic adapter
//! ([`crate::commands::offering`]) renders their deos surface, fires each press as ONE real
//! `advance` attributed to the presser's derived dregg identity, and surfaces `verify`
//! honestly (re-verification by replay).
//!
//! Registration residual (Repair applies centrally): the two `PLAY_KEYS` entries + `/play`
//! match arms (`commands/portfolio.rs`) and the `route_component`/`route_modal` key arms
//! (`commands/offering.rs`).
//!
//! The OTHER half of backlog #20 stays honestly unforced: `dreggnet-quest` /
//! `dreggnet-faction` have NO `Offering` impl yet — they need a thin crate-side offering
//! shim first (noted, not bodged here).

use std::sync::OnceLock;

use dreggnet_gear::{LoadoutOffering, TalentTreeOffering};
use dreggnet_offerings::Offering;

use crate::commands::offering::{DiscordOffering, Store};

/// The honest status line every portfolio offering carries: the count of committed turns its
/// chain re-verifies over (the same number `verify` reports).
fn verified_turns<O: Offering>(off: &O, session: &O::Session) -> String {
    format!("{} verified turns", off.verify(session).turns)
}

impl DiscordOffering for LoadoutOffering {
    const KEY: &'static str = "gear";
    const TITLE: &'static str = "Gear";
    const COLOR: u32 = 0x8C5A2B;
    const TAGLINE: &'static str =
        "forge · equip · use — the ability unlocks via a KERNEL cross-cell ownership predicate";
    fn store() -> &'static Store<Self> {
        static SESSIONS: OnceLock<Store<LoadoutOffering>> = OnceLock::new();
        SESSIONS.get_or_init(Store::spawn)
    }
    fn status_line(&self, session: &Self::Session) -> String {
        verified_turns(self, session)
    }
}

impl DiscordOffering for TalentTreeOffering {
    const KEY: &'static str = "talents";
    const TITLE: &'static str = "Talent Tree";
    const COLOR: u32 = 0x5A3A8C;
    const TAGLINE: &'static str =
        "class-gated, prereq-chained claims priced in banked echoes · respec is real";
    fn store() -> &'static Store<Self> {
        static SESSIONS: OnceLock<Store<TalentTreeOffering>> = OnceLock::new();
        SESSIONS.get_or_init(Store::spawn)
    }
    fn status_line(&self, session: &Self::Session) -> String {
        verified_turns(self, session)
    }
}

#[cfg(test)]
mod tests {
    //! Both gear surfaces DRIVEN at the logic level through the SAME generic-adapter calls a
    //! live `/play` open + button press take — against the real dreggnet-gear substrate.
    use dreggnet_offerings::{DreggIdentity, Outcome, SessionConfig};

    use super::*;
    use crate::commands::offering::{self, Driven, close_in, drive, fire_id, is_open, with_live};

    fn actor(tag: &str) -> DreggIdentity {
        DreggIdentity(format!("{tag}{}", "0".repeat(64 - tag.len())))
    }

    /// **`/play gear` opens + a real EQUIP turn lands** — the exact wiring gap #20 names: the
    /// offering existed, Discord could not reach it. The press drives one real turn on the
    /// substrate and the chain re-verifies.
    #[test]
    fn gear_opens_and_equips_on_discord() {
        let channel = 772_100u64;
        close_in::<LoadoutOffering>(channel);
        offering::open_in(
            channel,
            LoadoutOffering::new,
            SessionConfig::with_seed(channel),
        )
        .expect("gear opens");
        assert!(is_open::<LoadoutOffering>(channel));

        let me = actor("ge");
        // The first affordance is the equip (enabled on a fresh loadout).
        let first = with_live::<LoadoutOffering, _>(channel, |live| {
            live.offering.actions(&live.session).into_iter().next()
        })
        .flatten()
        .expect("the loadout offers an equip affordance");
        match drive::<LoadoutOffering>(
            channel,
            &fire_id(LoadoutOffering::KEY, &first.turn, first.arg),
            me,
        ) {
            Driven::Fired(outcome) => assert!(
                matches!(outcome, Outcome::Landed { .. }),
                "the equip lands as a real committed turn: {outcome:?}"
            ),
            other => panic!("a gear press must drive a real turn, got {other:?}"),
        }
        assert!(
            offering::verify_live::<LoadoutOffering>(channel)
                .expect("live")
                .verified,
            "the gear chain re-verifies"
        );
        close_in::<LoadoutOffering>(channel);
    }

    /// **`/play talents` opens and renders a claimable tree** — reachable + drivable through
    /// the generic adapter, and its chain re-verifies from the fresh open.
    #[test]
    fn talents_open_and_reverify_on_discord() {
        let channel = 772_101u64;
        close_in::<TalentTreeOffering>(channel);
        offering::open_in(
            channel,
            TalentTreeOffering::new,
            SessionConfig::with_seed(channel),
        )
        .expect("talents open");
        assert!(is_open::<TalentTreeOffering>(channel));
        let actions = with_live::<TalentTreeOffering, _>(channel, |live| {
            live.offering.actions(&live.session)
        })
        .expect("live");
        assert!(
            !actions.is_empty(),
            "the talent tree offers affordances (claims / respec)"
        );
        assert!(
            offering::verify_live::<TalentTreeOffering>(channel)
                .expect("live")
                .verified,
            "the talent chain re-verifies"
        );
        close_in::<TalentTreeOffering>(channel);
    }
}
