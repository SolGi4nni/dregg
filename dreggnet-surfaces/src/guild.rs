//! # `GuildPage` — the roster + verified-clears surface over [`dreggnet_guild`].
//!
//! A guild's roster + its aggregate **verified-clears** leaderboard. Membership is the guild's cap
//! set (a member holds a real capability to the shared guild cell); the leaderboard is the SUM of
//! the members' un-forgeable clears ([`GuildBoard`](dreggnet_guild::GuildBoard) only ever counts a
//! clear that passed the ugc no-cheat verify) + live-character survivors. Nothing on this page is a
//! number an officer typed — it is all read off the real substrate aggregate.
//!
//! ## One interactive move: **admit**
//!
//! The substrate exposes [`Guild::admit`] (a real capability grant) + [`Guild::act_on_guild`] (a
//! real cap-bounded committed turn). So this surface is *lightly playable*: an officer may **admit**
//! a pending applicant — the applicant is granted the guild cap and its first act on the guild cell
//! COMMITS a real membership turn (a genuine [`TurnReceipt`]). The teeth are non-vacuous: a
//! non-member (a stranger with no cap) writing the same guild cell is a real `CapabilityNotHeld`
//! executor refusal ([`GuildSession::stranger_write_refused`]), never a silent apply. Clearing a
//! run still happens through the game turns, not this surface; `render` is the payload.
//! [`demo`](GuildPage::demo) seeds a REAL guild (members admitted via genuine cap grants + one real
//! verified clear) plus a couple of pending applicants to admit.

use dregg_app_framework::TurnReceipt;
use dreggnet_guild::{Guild, GuildStats};
use dreggnet_offerings::character::CharacterSheet;
use dreggnet_offerings::{
    Action, DreggIdentity, Offering, OfferingError, Outcome, RunCost, SessionConfig, Surface,
    VerifyReport,
};
use dungeon_on_dregg::mud::CommandOutcome;
use dungeon_on_dregg::{CH_CLAIM, CH_DESCEND, CH_TAKE_LANTERN, DUNGEON};
use ugc_dregg::{Completion, Universe, WinCondition, record_playthrough};

use crate::{action_menu, menu, pill, row, section, text};
use deos_view::ViewNode;

/// The affordance verb an officer fires to admit a pending applicant (`arg` = the applicant index).
pub const TURN_ADMIT: &str = "admit";

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
    /// Applicants who have not yet been admitted (the `admit` action's pool, in a stable order).
    applicants: Vec<String>,
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
    /// The number of pending applicants (admittable via the `admit` action).
    pub fn applicant_count(&self) -> usize {
        self.applicants.len()
    }
    /// Whether the guild is empty (no members).
    pub fn is_empty(&self) -> bool {
        self.member_names.is_empty()
    }
    /// The guild's name.
    pub fn name(&self) -> &str {
        self.guild.name()
    }

    /// **The other side of the membership tooth** — install a stranger (a real inhabitant of the
    /// guild world holding NO cap to the guild cell) and drive its write on the guild cell. Returns
    /// `Some(reason)` iff the executor genuinely REFUSED it (`CapabilityNotHeld`) — proof the admit
    /// action's cap grant is load-bearing, not decorative. `None` would mean a non-member wrote
    /// through (a broken gate). The guild state is untouched by a refused write (anti-ghost).
    pub fn stranger_write_refused(&mut self) -> Option<String> {
        let stranger = self.guild.install_stranger();
        match self.guild.act_on_guild(stranger) {
            CommandOutcome::Refused { reason } => Some(reason),
            CommandOutcome::Committed { .. } => None,
        }
    }
}

/// **The guild-page offering** — a read-surface factory. Construct with the roster to seed
/// ([`demo`](Self::demo) for a populated guild, [`new`](Self::new) empty).
pub struct GuildPage {
    name: String,
    members: Vec<String>,
    applicants: Vec<String>,
    seed_clear: bool,
}

impl GuildPage {
    /// An EMPTY guild named `name` (the empty-state surface, no applicants).
    pub fn new(name: impl Into<String>) -> Self {
        GuildPage {
            name: name.into(),
            members: Vec::new(),
            applicants: Vec::new(),
            seed_clear: false,
        }
    }

    /// A guild `name` with `members` (a genuine verified clear seeded iff `seed_clear`, no
    /// applicants).
    pub fn with_members(name: impl Into<String>, members: Vec<String>, seed_clear: bool) -> Self {
        GuildPage {
            name: name.into(),
            members,
            applicants: Vec::new(),
            seed_clear,
        }
    }

    /// A guild `name` seeded with `members` (verified clear iff `seed_clear`) AND `applicants`
    /// waiting to be admitted (the `admit` action's pool).
    pub fn with_roster(
        name: impl Into<String>,
        members: Vec<String>,
        applicants: Vec<String>,
        seed_clear: bool,
    ) -> Self {
        GuildPage {
            name: name.into(),
            members,
            applicants,
            seed_clear,
        }
    }

    /// A populated DEMO guild — three members admitted via genuine capability grants, one real
    /// ugc-verified clear on the built-in dungeon, live-character survivors, and two pending
    /// applicants an officer can admit (the web/discord register state).
    pub fn demo(name: impl Into<String>) -> Self {
        Self::with_roster(
            name,
            vec!["Aria".to_string(), "Bram".to_string(), "Cyra".to_string()],
            vec!["Delia".to_string(), "Emrys".to_string()],
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
            applicants: self.applicants.clone(),
        })
    }

    /// One move per pending applicant: **admit** them (a real cap grant + committed membership turn).
    fn actions(&self, s: &GuildSession) -> Vec<Action> {
        s.applicants
            .iter()
            .enumerate()
            .map(|(i, name)| Action::new(format!("Admit {name}"), TURN_ADMIT, i as i64, true))
            .collect()
    }

    /// **Admit** a pending applicant — grant the guild cap ([`Guild::admit`]) and drive its first
    /// write on the guild cell ([`Guild::act_on_guild`]), which COMMITS a real membership turn. The
    /// non-vacuous other side (a non-member's write is a `CapabilityNotHeld` executor refusal) is
    /// [`GuildSession::stranger_write_refused`]. Clearing a run happens through the game turns.
    fn advance(&self, s: &mut GuildSession, input: Action, _actor: DreggIdentity) -> Outcome {
        if input.turn != TURN_ADMIT {
            return Outcome::Refused(format!(
                "the guild surface only admits (verb `{TURN_ADMIT}`)"
            ));
        }
        let idx = input.arg.max(0) as usize;
        let Some(name) = s.applicants.get(idx).cloned() else {
            return Outcome::Refused(format!("no pending applicant #{idx}"));
        };
        let id = DreggIdentity(name.clone());
        // The cap grant, then the applicant's first cap-bounded write on the guild cell — a real
        // committed turn (a non-member's identical write would be a `CapabilityNotHeld` refusal).
        let cell = s.guild.admit(&id);
        match s.guild.act_on_guild(cell) {
            CommandOutcome::Committed { receipt } => {
                s.applicants.remove(idx);
                s.member_names.push(name);
                Outcome::Landed {
                    receipt: TurnReceipt {
                        turn_hash: receipt,
                        ..Default::default()
                    },
                    ended: false,
                }
            }
            CommandOutcome::Refused { reason } => {
                Outcome::Refused(format!("admitting `{name}` refused: {reason}"))
            }
        }
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

        // Pending applicants — the `admit` action's pool (a real cap grant + membership turn each).
        if !s.applicants.is_empty() {
            let mut kids: Vec<ViewNode> = vec![text(format!(
                "{} applicant(s) awaiting a cap",
                s.applicants.len()
            ))];
            kids.push(menu(action_menu(self.actions(s))));
            children.push(section("Applicants", "warn", kids));
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
