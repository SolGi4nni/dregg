//! # `versus` — guild-vs-guild by aggregate PROVEN stats
//!
//! Two guilds are ranked by their [`GuildStats`], which the [`GuildBoard`](crate::GuildBoard)
//! only ever fills from un-forgeable clears + live-character survivors. So the outcome
//! is decided by proven play, not by roster size or an officer's say-so — a guild that
//! stuffs its roster with fakes gains nothing, because a forged clear never entered the
//! aggregate in the first place.

/// A guild's **aggregate proven stats** — the ranking key. Every field is a SUM the
/// board built only from outcomes that passed the no-cheat verify (clears) or read a
/// live character (survivors); none of it can be padded.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct GuildStats {
    /// The number of enrolled members (the cap set size).
    pub members: usize,
    /// The SUM of members' ugc-verified clears — the headline rank.
    pub verified_clears: usize,
    /// The SUM of members' verified turns-to-win (tie-break: fewer is better).
    pub total_turns: usize,
    /// The count of members whose character is a live survivor (`dead == 0`).
    pub survivors: usize,
}

/// The outcome of a guild-vs-guild comparison.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Standing {
    /// The first guild ranks higher.
    First,
    /// The second guild ranks higher.
    Second,
    /// The two guilds are tied on every proven measure.
    Tied,
}

/// **Rank two guilds by aggregate proven stats.** Order of precedence:
///
/// 1. more **verified clears** wins (the headline — un-forgeable);
/// 2. else more **survivors** wins (live characters, no resurrection padding);
/// 3. else fewer **total turns** wins (a tighter aggregate depth);
/// 4. else [`Standing::Tied`].
///
/// A guild cannot climb by padding fakes: `verified_clears`/`survivors` only ever hold
/// what the board's no-cheat verify admitted.
pub fn rank_guilds(a: &GuildStats, b: &GuildStats) -> Standing {
    if a.verified_clears != b.verified_clears {
        return if a.verified_clears > b.verified_clears {
            Standing::First
        } else {
            Standing::Second
        };
    }
    if a.survivors != b.survivors {
        return if a.survivors > b.survivors {
            Standing::First
        } else {
            Standing::Second
        };
    }
    if a.total_turns != b.total_turns {
        // Fewer turns is the tighter clear — the lower aggregate ranks higher.
        return if a.total_turns < b.total_turns {
            Standing::First
        } else {
            Standing::Second
        };
    }
    Standing::Tied
}
