//! # `GuildPage` — a **read-surface** over [`dreggnet_guild`].
//!
//! A guild's roster + its aggregate **verified-clears** leaderboard. Membership is the guild's cap
//! set (a member holds a real capability to the shared guild cell); the leaderboard is the SUM of
//! the members' un-forgeable clears ([`GuildBoard`](dreggnet_guild::GuildBoard) only ever counts a
//! clear that passed the ugc no-cheat verify) + live-character survivors. Nothing on this page is a
//! number an officer typed — it is all read off the real substrate aggregate.
//!
//! Read-only: joining / clearing happens through the game + membership turns, not this surface;
//! `render` is the payload. [`demo`](GuildPage::demo) seeds a REAL guild (members admitted via
//! genuine cap grants + one real verified clear) for the web/discord register state.

use dreggnet_guild::{Guild, GuildStats};
use dreggnet_offerings::character::CharacterSheet;
use dreggnet_offerings::{
    Action, DreggIdentity, Offering, OfferingError, Outcome, RunCost, SessionConfig, Surface,
    VerifyReport,
};
use dungeon_on_dregg::{CH_CLAIM, CH_DESCEND, CH_TAKE_LANTERN, DUNGEON};
use ugc_dregg::{Completion, Universe, WinCondition, record_playthrough};

use crate::{pill, row, section, text};
use deos_view::ViewNode;

/// The built-in winnable dungeon (win = `gold == 500`) the demo guild's verified clear runs on.
fn salt_shore() -> Universe {
    Universe::authored(
        "The Salt Shore Descent",
        "surfaces-guild-fixture",
        DUNGEON,
        WinCondition::ended_with(&[("gold", 500)]),
    )
    .expect("the salt-shore dungeon is a valid, deployable universe")
}

/// The minimal winning move sequence (take the lantern, descend the gate, claim the hoard).
const WIN_MOVES: [usize; 3] = [CH_TAKE_LANTERN, CH_DESCEND, CH_CLAIM];

/// **A live guild session** — the formed [`Guild`] (its real cap-gated world + leaderboard) plus the
/// member names in admit order (for a stable roster render).
pub struct GuildSession {
    guild: Guild,
    member_names: Vec<String>,
}

impl GuildSession {
    /// The guild's aggregate proven stats (verified clears / survivors / turns).
    pub fn stats(&self) -> GuildStats {
        self.guild.stats()
    }
    /// The roster size.
    pub fn roster_len(&self) -> usize {
        self.member_names.len()
    }
    /// Whether the guild is empty (no members).
    pub fn is_empty(&self) -> bool {
        self.member_names.is_empty()
    }
    /// The guild's name.
    pub fn name(&self) -> &str {
        self.guild.name()
    }
}

/// **The guild-page offering** — a read-surface factory. Construct with the roster to seed
/// ([`demo`](Self::demo) for a populated guild, [`new`](Self::new) empty).
pub struct GuildPage {
    name: String,
    members: Vec<String>,
    seed_clear: bool,
}

impl GuildPage {
    /// An EMPTY guild named `name` (the empty-state surface).
    pub fn new(name: impl Into<String>) -> Self {
        GuildPage {
            name: name.into(),
            members: Vec::new(),
            seed_clear: false,
        }
    }

    /// A guild `name` with `members` (a genuine verified clear seeded iff `seed_clear`).
    pub fn with_members(name: impl Into<String>, members: Vec<String>, seed_clear: bool) -> Self {
        GuildPage {
            name: name.into(),
            members,
            seed_clear,
        }
    }

    /// A populated DEMO guild — three members admitted via genuine capability grants, one real
    /// ugc-verified clear on the built-in dungeon, and live-character survivors (the web/discord
    /// register state).
    pub fn demo(name: impl Into<String>) -> Self {
        Self::with_members(
            name,
            vec!["Aria".to_string(), "Bram".to_string(), "Cyra".to_string()],
            true,
        )
    }
}

impl Offering for GuildPage {
    type Session = GuildSession;

    fn open(&self, _cfg: SessionConfig) -> Result<GuildSession, OfferingError> {
        let mut guild = Guild::form(&self.name);
        let mut member_names = Vec::new();
        for name in &self.members {
            let id = DreggIdentity(name.clone());
            // Joining IS a capability grant; the member then acts on guild state (a real cap-bounded
            // committed turn — a non-member's identical write would be a `CapabilityNotHeld` refusal).
            let cell = guild.admit(&id);
            let _ = guild.act_on_guild(cell);
            member_names.push(name.clone());
        }

        if self.seed_clear && !member_names.is_empty() {
            // One genuine verified clear for the first member — a real winning run the no-cheat
            // verify accepts (a forged clear would contribute nothing).
            let universe = salt_shore();
            if let Ok(play) = record_playthrough(&universe, &WIN_MOVES) {
                let completion = Completion {
                    universe: universe.id(),
                    player: member_names[0].clone(),
                    play,
                    claimed_turns: WIN_MOVES.len(),
                };
                let id0 = DreggIdentity(member_names[0].clone());
                let _ = guild.board_mut().record_clear(&id0, &universe, &completion);
            }
            // Live-character survivors (a dead character could not pad this — the flag is un-undoable).
            for name in &member_names {
                let id = DreggIdentity(name.clone());
                let _ = guild
                    .board_mut()
                    .record_survivor(&id, &CharacterSheet::default());
            }
        }

        Ok(GuildSession {
            guild,
            member_names,
        })
    }

    /// A read-surface exposes no moves.
    fn actions(&self, _s: &GuildSession) -> Vec<Action> {
        Vec::new()
    }

    /// Read-only: joining / clearing happens through the membership + game turns, not this page.
    fn advance(&self, _s: &mut GuildSession, _input: Action, _actor: DreggIdentity) -> Outcome {
        Outcome::Refused("the guild page is a read-only surface".into())
    }

    /// Re-check that every rostered member genuinely holds the guild cap (membership is the cap set).
    fn verify(&self, s: &GuildSession) -> VerifyReport {
        for name in &s.member_names {
            let id = DreggIdentity(name.clone());
            if !s.guild.is_member(&id) {
                return VerifyReport::broken(
                    s.member_names.len(),
                    format!("`{name}` is on the roster but holds no guild cap"),
                );
            }
        }
        VerifyReport::ok(s.member_names.len())
    }

    fn render(&self, s: &GuildSession) -> Surface {
        let mut children: Vec<ViewNode> = Vec::new();
        let stats = s.stats();

        children.push(section(
            "Guild",
            "muted",
            vec![text(format!("{} · {} member(s)", s.name(), s.roster_len()))],
        ));

        // The roster — a Table of members with a membership pill.
        if s.is_empty() {
            children.push(section(
                "Roster",
                "muted",
                vec![text("No members yet — admit a founder.")],
            ));
        } else {
            let mut rows: Vec<ViewNode> = vec![row(vec![text("Member"), text("Standing")])];
            for name in &s.member_names {
                let id = DreggIdentity(name.clone());
                let held = s.guild.is_member(&id);
                rows.push(row(vec![
                    text(name),
                    pill(
                        if held { "member" } else { "not a member" },
                        if held { "good" } else { "bad" },
                    ),
                ]));
            }
            children.push(section("Roster", "accent", vec![ViewNode::Table(rows)]));
        }

        // The leaderboard — the aggregate PROVEN stats (nothing here can be padded).
        let board = ViewNode::Table(vec![
            row(vec![
                text("Verified clears"),
                text(stats.verified_clears.to_string()),
            ]),
            row(vec![
                text("Total verified turns"),
                text(stats.total_turns.to_string()),
            ]),
            row(vec![text("Survivors"), text(stats.survivors.to_string())]),
            row(vec![text("Members"), text(stats.members.to_string())]),
        ]);
        children.push(section(
            "Leaderboard (aggregate proven)",
            "genuine",
            vec![board],
        ));

        Surface(section(format!("Guild — {}", s.name()), "accent", children))
    }

    fn price(&self, _input: &Action) -> RunCost {
        RunCost::free()
    }
}
