//! **The `/dungeon` adoption of the generic collective adapter (CONSERVATIVE).**
//!
//! `/dungeon` (`crate::commands::fiction`) still owns the LIVE Discord surface — its bespoke
//! ballot embeds, the per-run thread orchestration, and above all the paid narrator credit gate
//! (`narrate_room_gated`, a real Bedrock spend). That flow is intact and untouched.
//!
//! What this module adds is the proof — and the reachable capability — that the dungeon is ALSO a
//! first-class consumer of the generic [`crate::commands::offering`] adapter's **collective
//! mode**: [`dreggnet_offerings::dungeon::DungeonOffering`] runs through the SAME
//! [`CollectiveRound`](crate::commands::offering::CollectiveRound) → write-once ballots →
//! plurality → [`Offering::advance_collective`] path any collective offering does. The dungeon is
//! [`DiscordOffering::collective`] (its presses tally rather than fire immediately), and a round
//! close resolves the crowd's plurality winner as ONE real cap-bounded turn carrying the whole
//! `CollectiveDecision` (the electorate + the tally + the carrier) — closing the gap the
//! `/dungeon` frontend flagged, where the crowd turn was attributed to a nameless `party_actor()`
//! constant rather than the real voters.
//!
//! ## What is migrated vs precisely named
//!
//! MIGRATED (here, driven): the dungeon's ballot mechanism — write-once per derived dregg
//! identity, plurality winner, the crowd turn as `advance_collective` — is the generic adapter's
//! collective mode, exercised end-to-end against the real Warden's Keep world-cell.
//!
//! NAMED (the precise remaining cutover, deliberately NOT done to keep the paid `/dungeon` flow
//! unbroken): `fiction.rs`'s live handlers would delegate to the collective core —
//! `handle_component` → [`cast_vote`](crate::commands::offering::cast_vote), `handle_close` →
//! [`close_round`](crate::commands::offering::close_round) — with `narrate_room_gated` invoked in
//! the async layer AFTER `close_round` returns the next round's actions (the narrator gate is a
//! frontend concern the offering core deliberately does not carry). That swap is mechanical but
//! touches the thread-spin orchestration + the Bedrock spend path, so it is staged behind this
//! driven proof rather than risked in the same breath.

use std::sync::OnceLock;

use dreggnet_offerings::dungeon::{DungeonOffering, DungeonSession, KEEP_NAME};

use crate::commands::offering::{DiscordOffering, Store, ValuePrompt};

/// The dungeon brand colour (matches `fiction.rs`'s `DUNGEON_COLOR`).
const DUNGEON_COLOR: u32 = 0x7B2CBF;

impl DiscordOffering for DungeonOffering {
    const KEY: &'static str = "dungeon";
    const TITLE: &'static str = KEEP_NAME;
    const COLOR: u32 = DUNGEON_COLOR;
    const TAGLINE: &'static str = "the crowd decides · the world disposes · the chain remembers";

    fn store() -> &'static Store<Self> {
        static SESSIONS: OnceLock<Store<DungeonOffering>> = OnceLock::new();
        SESSIONS.get_or_init(Store::spawn)
    }

    fn value_prompt(_turn: &str) -> Option<ValuePrompt> {
        None
    }

    /// The dungeon is a COLLECTIVE offering — a press is a write-once ballot, and a round close
    /// resolves the plurality winner as one real crowd turn (`advance_collective`).
    fn collective() -> bool {
        true
    }

    fn status_line(&self, session: &DungeonSession) -> String {
        session.state_line()
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Tests — the generic collective mode DRIVEN against the REAL dungeon offering:
// write-once ballots per derived identity, a non-member refused, the plurality
// winner resolved as ONE real cap-bounded `advance_collective` (a genuine
// TurnReceipt), the crowd decision recorded, the chain re-verified. No live Discord.
// ─────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use dreggnet_offerings::{DreggIdentity, Offering, Outcome, SessionConfig};
    use dungeon_on_dregg::KP_PRESS_ON;

    use crate::commands::offering::{
        self, Cast, CollectiveClose, cast_vote, close_round, open_round, with_live, with_round,
    };

    fn member(tag: &str) -> DreggIdentity {
        DreggIdentity(format!("{tag}{}", "0".repeat(64 - tag.len())))
    }

    /// **The collective mode, end to end, on the real dungeon.** A restricted crowd casts
    /// write-once ballots (a repeat vote refused, a non-member refused); a round close tallies the
    /// plurality winner and drives it as ONE real cap-bounded `advance_collective` — a genuine
    /// TurnReceipt — recording the whole `CollectiveDecision` (the real electorate) beside the
    /// committed step; the playthrough re-verifies.
    #[test]
    fn the_collective_mode_drives_a_plurality_won_crowd_turn() {
        let channel = 92_401;
        offering::close_in::<DungeonOffering>(channel);
        // Opening a collective offering auto-opens an OPEN-crowd round; re-open it RESTRICTED to a
        // three-member electorate (a council-shaped crowd) so a non-member ballot is refused.
        offering::open_in(channel, DungeonOffering::new(), SessionConfig::with_seed(7))
            .expect("the Keep opens on a real world-cell");
        let members = vec![member("a1"), member("b0"), member("c2")];
        assert!(open_round::<DungeonOffering>(
            channel,
            Some(members.clone())
        ));

        // The ballot offers the ungated press-on move (arg == KP_PRESS_ON).
        let has_press_on = with_round::<DungeonOffering, _>(channel, |r| {
            r.position_of_arg(KP_PRESS_ON as i64).is_some()
        })
        .unwrap();
        assert!(has_press_on, "the gatehall ballot offers press-on");

        // Two members vote press-on; the first member's SECOND ballot is refused (write-once).
        assert_eq!(
            cast_vote::<DungeonOffering>(channel, members[0].clone(), KP_PRESS_ON as i64),
            Cast::Recorded
        );
        assert_eq!(
            cast_vote::<DungeonOffering>(channel, members[0].clone(), KP_PRESS_ON as i64),
            Cast::AlreadyVoted,
            "one write-once ballot per derived identity"
        );
        assert_eq!(
            cast_vote::<DungeonOffering>(channel, members[1].clone(), KP_PRESS_ON as i64),
            Cast::Recorded
        );

        // A voter OUTSIDE the electorate is refused — the crowd of record is cryptographic.
        let stranger = DreggIdentity("ff".repeat(32));
        assert_eq!(
            cast_vote::<DungeonOffering>(channel, stranger, KP_PRESS_ON as i64),
            Cast::NotEligible,
            "a non-member ballot is refused"
        );

        // Close the round → the plurality winner is driven as ONE real crowd turn.
        match close_round::<DungeonOffering>(channel) {
            CollectiveClose::Resolved(r) => {
                assert_eq!(r.round, 0);
                assert_eq!(
                    r.tally.winner, KP_PRESS_ON as i64,
                    "press-on won the plurality"
                );
                assert_eq!(r.tally.winning_votes(), 2);
                assert_eq!(r.electorate.len(), 2, "two voters of record");
                match r.outcome {
                    Outcome::Landed { receipt, ended } => {
                        assert!(!ended, "pressing on does not end the Keep");
                        assert_ne!(
                            receipt.turn_hash, [0u8; 32],
                            "a genuine committed crowd turn"
                        );
                    }
                    other => panic!("the plurality winner must land a real turn, got {other:?}"),
                }
            }
            _ => panic!("a plurality round must resolve, got a non-resolved close"),
        }

        // The dungeon recorded the CollectiveDecision (the real electorate) beside the step, and
        // the playthrough re-verifies by replay.
        let (recorded_electorate, verified, receipts) =
            with_live::<DungeonOffering, _>(channel, |l| {
                (
                    l.session.collective_of_step(0).map(|d| d.electorate_size()),
                    l.offering.verify(&l.session).verified,
                    l.session.receipts_len(),
                )
            })
            .unwrap();
        assert_eq!(
            recorded_electorate,
            Some(2),
            "the crowd decision is first-class beside the committed turn"
        );
        assert!(verified, "the honest playthrough re-verifies by replay");
        assert_eq!(receipts, 2, "genesis + the crowd's committed turn");

        offering::close_in::<DungeonOffering>(channel);
    }
}
