//! # `leaderboard` — the guild rank is the SUM of un-forgeable clears
//!
//! A guild's standing is not a number an officer types; it is the aggregate of its
//! members' PROVEN outcomes:
//!
//! * **Verified clears.** A clear counts only if [`ugc_dregg::verify_completion`]
//!   accepts it — a stranger re-executes the identically-seeded universe with the
//!   submitted moves and it reaches the WIN, or the completion is REJECTED
//!   (forged / edited / incomplete / result-tampered). A forged clear contributes
//!   NOTHING to the guild rank ([`GuildBoard::record_clear`] returns the exact
//!   [`RejectReason`](ugc_dregg::RejectReason)).
//! * **Survived runs.** A member's character either carries the WriteOnce-final
//!   `dead` flag or it does not. [`GuildBoard::record_survivor`] counts a survivor iff
//!   the character's [`CharacterSheet::dead`] is `0`. Because that flag is
//!   un-undoable and persists across runs (the character store), a dead character
//!   cannot re-enter the survivor board — you cannot pad a no-death-streak with a
//!   resurrection.
//!
//! And the roster is the cap set: only a member's clears count. A clear recorded for a
//! non-member is refused ([`ClearError::NotAMember`]) — you cannot inflate a guild with
//! a stranger's runs either.

use std::collections::{HashMap, HashSet};

use dreggnet_offerings::DreggIdentity;
use dreggnet_offerings::character::CharacterSheet;
use ugc_dregg::{Completion, RejectReason, Universe, verify_completion};

use crate::versus::GuildStats;

/// Why a clear / survivor record was refused at the board.
#[derive(Clone, Debug)]
pub enum ClearError {
    /// The identity is not a guild member — a non-member's run cannot inflate the
    /// guild rank (the cap-set tooth, at the board).
    NotAMember(DreggIdentity),
    /// The completion did not pass the no-cheat verify — a forged / edited /
    /// incomplete / result-tampered run. Carries the exact refusal
    /// ([`ugc_dregg::RejectReason`]); it counts for NOTHING.
    NoCheat(RejectReason),
}

impl std::fmt::Display for ClearError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ClearError::NotAMember(id) => {
                write!(f, "identity {} is not a guild member", id.as_str())
            }
            ClearError::NoCheat(reason) => {
                write!(f, "clear rejected by the no-cheat verify: {reason}")
            }
        }
    }
}

impl std::error::Error for ClearError {}

/// One member's proven contribution to the guild aggregate.
#[derive(Clone, Copy, Debug, Default)]
struct MemberRecord {
    /// Count of the member's ugc-verified clears.
    verified_clears: usize,
    /// Sum of the member's verified turns-to-win (the ranking depth).
    total_turns: usize,
    /// Whether the member's most-recently recorded character is a survivor (`dead == 0`).
    survivor: bool,
    /// Whether a survivor record has ever been taken for this member.
    survivor_known: bool,
}

/// **The guild leaderboard** — the aggregate of members' un-forgeable clears + survived
/// runs. The roster is the guild's cap set (enrolled by [`crate::Guild::admit`]); only a
/// member's proven outcomes are counted.
#[derive(Clone, Debug, Default)]
pub struct GuildBoard {
    members: HashSet<DreggIdentity>,
    records: HashMap<DreggIdentity, MemberRecord>,
}

impl GuildBoard {
    /// A fresh empty board.
    pub fn new() -> GuildBoard {
        GuildBoard::default()
    }

    /// Enrol a member onto the board (called by [`crate::Guild::admit`] — membership is
    /// the cap set). Idempotent.
    pub fn enrol(&mut self, who: DreggIdentity) {
        self.members.insert(who);
    }

    /// Whether `who` is enrolled (a guild member).
    pub fn is_member(&self, who: &DreggIdentity) -> bool {
        self.members.contains(who)
    }

    /// **Record a member's clear — counted ONLY if it survives the no-cheat verify.**
    /// Runs [`ugc_dregg::verify_completion`] against `universe`: a genuine winning
    /// playthrough is accepted and its verified turns added to the guild aggregate; a
    /// forged / incomplete / result-tampered completion is REJECTED
    /// ([`ClearError::NoCheat`]) and adds nothing. A clear for a non-member is refused
    /// ([`ClearError::NotAMember`]). Returns the verified turns-to-win on success.
    pub fn record_clear(
        &mut self,
        who: &DreggIdentity,
        universe: &Universe,
        completion: &Completion,
    ) -> Result<usize, ClearError> {
        if !self.members.contains(who) {
            return Err(ClearError::NotAMember(who.clone()));
        }
        // THE NO-CHEAT TOOTH — a stranger re-executes; a forged clear is refused here
        // and never reaches the aggregate.
        let turns = verify_completion(universe, completion).map_err(ClearError::NoCheat)?;
        let rec = self.records.entry(who.clone()).or_default();
        rec.verified_clears += 1;
        rec.total_turns += turns;
        Ok(turns)
    }

    /// **Record a member's survived-run fact** off the character's WriteOnce-final `dead`
    /// flag. A survivor (`sheet.dead == 0`) is counted; a dead character
    /// (`sheet.dead != 0`) is NOT — and because the flag is un-undoable and persists,
    /// a dead member cannot re-enter the survivor board. Refused for a non-member
    /// ([`ClearError::NotAMember`]). Returns whether the member counts as a survivor.
    pub fn record_survivor(
        &mut self,
        who: &DreggIdentity,
        sheet: &CharacterSheet,
    ) -> Result<bool, ClearError> {
        if !self.members.contains(who) {
            return Err(ClearError::NotAMember(who.clone()));
        }
        let survivor = sheet.dead == 0;
        let rec = self.records.entry(who.clone()).or_default();
        rec.survivor = survivor;
        rec.survivor_known = true;
        Ok(survivor)
    }

    /// The guild's aggregate proven stats — the SUM over members of verified clears,
    /// verified turns, and survivors. This is the guild-vs-guild ranking key; nothing
    /// here can be padded (every clear passed the no-cheat verify; every survivor is a
    /// live character).
    pub fn stats(&self) -> GuildStats {
        let mut s = GuildStats {
            members: self.members.len(),
            verified_clears: 0,
            total_turns: 0,
            survivors: 0,
        };
        for rec in self.records.values() {
            s.verified_clears += rec.verified_clears;
            s.total_turns += rec.total_turns;
            if rec.survivor_known && rec.survivor {
                s.survivors += 1;
            }
        }
        s
    }

    /// A member's verified-clear count (0 if none recorded).
    pub fn clears_of(&self, who: &DreggIdentity) -> usize {
        self.records
            .get(who)
            .map(|r| r.verified_clears)
            .unwrap_or(0)
    }
}
