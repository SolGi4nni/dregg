//! # `dreggnet-guild` — a formed persistent group on the REAL dregg substrate
//!
//! The roadmap's SOCIAL #5 (`docs/GAME-INFRA-ROADMAP.md`): a guild is not a server
//! row but a *cap-bounded shared cell* whose every guarantee is a primitive the
//! executor already re-checks. Four teeth, each consumed from an existing crate,
//! none reimplemented:
//!
//! ## 1. Membership IS the capability set
//!
//! A [`Guild`] owns a real [`World`](starbridge_v2::world::World) ledger with ONE
//! shared **guild cell** — a mud-style "room" (`dungeon-on-dregg/src/mud.rs`) that
//! only members hold a capability to. [`Guild::admit`] installs a member as a real
//! player cell holding the guild cap: **joining is a capability grant**. A member's
//! write to the guild cell commits ([`Guild::act_on_guild`] → [`CommandOutcome::Committed`]);
//! a NON-member's identical write is a real `CapabilityNotHeld` executor refusal
//! ([`CommandOutcome::Refused`], never a silent apply). You cannot forge your way
//! onto the roster.
//!
//! ## 2. The leaderboard SUMS un-forgeable clears
//!
//! [`GuildBoard`] aggregates the guild's rank from its members' **ugc-dregg-verified
//! completions** ([`ugc_dregg::verify_completion`] — a stranger re-executes the
//! identically-seeded universe and it reaches the WIN, or it is REJECTED) plus
//! **survived-run facts** read off the character's WriteOnce-final `dead` flag
//! ([`dreggnet_offerings::character::CharacterSheet`]). A forged clear fails the
//! no-cheat verify and contributes NOTHING to the guild; a dead character cannot
//! un-die to pad the survivor board (the flag is un-undoable and persists). And only
//! a MEMBER's clears count — a non-member's clear is refused at the board.
//!
//! ## 3. The treasury is escrow-custodied
//!
//! [`GuildTreasury`] locks contributions into the protocol-proven `SealedEscrow`
//! capacity ([`starbridge_escrow_market::SealedEscrowMarket`]): value leaves the
//! depositor's wallet into custody (conserved, witnessed), and the capacity permits
//! a reclaim ONLY to the leg's original depositor. **An officer (any non-depositor)
//! pulling a member's contribution is a real refusal** — no officer can abscond with
//! the bank.
//!
//! ## 4. Guild-vs-guild by aggregate PROVEN stats
//!
//! [`rank_guilds`] orders two guilds by their aggregate [`GuildStats`] — verified
//! clears first. You cannot win by padding fakes, because the aggregate only ever
//! counts what tooth #2 admitted.
//!
//! ## Optional governance
//!
//! [`governance::OfficerElection`] elects officers via the real quorum-certified
//! collective vote (`dungeon-on-dregg/src/collective.rs`): below quorum no officer is
//! seated, a non-seated key is Ineligible, a forged ballot signature is refused.
//!
//! ## Honest scope — named residuals (labelled, not hidden)
//!
//! * **Guild halls / persistent world places.** The guild cell here carries roster +
//!   presence state; a rich guild HALL (rooms, stalls, a living space) is a content
//!   layer above the cap set, not built here.
//! * **A durable guild store.** The guild's `World` + board are in-process; a durable
//!   image (the redb/pg-dregg seam the character store names) that survives a restart
//!   is a named follow-up. The membership/verify/escrow teeth are identical over it.
//! * **A pooled N-contributor bank.** The escrow treasury custodies via the 2-leg
//!   sealed escrow (the anti-abscond tooth is the capacity's depositor-only reclaim);
//!   an N-leg pooled guild vault with governance-gated disbursement is a follow-up.
//! * **Guild-vs-guild SEASONS.** Ranking is a point-in-time aggregate compare; a
//!   season abstraction (a hall-of-fame across boundaries) rides on top.

pub mod governance;
pub mod leaderboard;
pub mod treasury;
pub mod versus;

use std::collections::HashMap;

use dregg_cell::AuthRequired;
use dregg_turn::action::Effect;
use starbridge_v2::world::{CommitOutcome, World, make_open_cell, set_field};

use dregg_cell::CellId;
use dreggnet_offerings::DreggIdentity;
use dungeon_on_dregg::mud::{CommandOutcome, actor_tag};

pub use leaderboard::{ClearError, GuildBoard};
pub use treasury::{GuildTreasury, TreasuryError};
pub use versus::{GuildStats, Standing, rank_guilds};

/// The guild cell's roster/presence slot — a member's write stamps their identity
/// tag here (proof they hold the guild cap). A non-member's write never lands.
pub const SLOT_GUILD_PRESENCE: usize = 0;

/// The executor signing seed the guild's shared world commits receipts under (a fixed
/// per-crate key, so every committed guild turn carries a genuine executor signature).
const GUILD_EXECUTOR_SEED: [u8; 32] = [0x6E; 32];

/// The reserved genesis seed of the shared **guild cell** (distinct from the member
/// cells, which draw from an incrementing counter).
const GUILD_CELL_SEED: u8 = 0xF0;

/// **A guild** — a formed persistent group whose MEMBERSHIP is the capability set of
/// a shared [`World`] cell.
///
/// Holds the real ledger, the one shared guild cell (a mud-style room only members
/// hold a cap to), the identity→member-cell roster, and the [`GuildBoard`] that sums
/// un-forgeable clears. [`admit`](Self::admit) grants a member the guild cap;
/// [`act_on_guild`](Self::act_on_guild) is a real cap-bounded turn (a member commits;
/// a non-member is a `CapabilityNotHeld` refusal).
pub struct Guild {
    name: String,
    world: World,
    guild_cell: CellId,
    /// identity → the member's player cell (which holds the guild cap).
    members: HashMap<DreggIdentity, CellId>,
    board: GuildBoard,
    next_seed: u8,
}

impl Guild {
    /// **Form a guild** — stand up a fresh cap-gated world with one shared guild cell.
    /// The guild is born empty (no members); [`admit`](Self::admit) grants the first
    /// member the guild cap.
    pub fn form(name: impl Into<String>) -> Guild {
        let mut world = World::new().with_executor_signing_key(GUILD_EXECUTOR_SEED);
        let guild_cell = world.genesis_cell(GUILD_CELL_SEED, 0);
        Guild {
            name: name.into(),
            world,
            guild_cell,
            members: HashMap::new(),
            board: GuildBoard::new(),
            next_seed: 1,
        }
    }

    /// The guild's display name.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// The shared guild cell (the cap-gated "room" only members may act on).
    pub fn guild_cell(&self) -> CellId {
        self.guild_cell
    }

    fn take_seed(&mut self) -> u8 {
        // Skip the reserved guild-cell seed; wrap within the genesis range.
        loop {
            let s = self.next_seed;
            self.next_seed = self.next_seed.wrapping_add(1).max(1);
            if s != GUILD_CELL_SEED && s != 0 {
                return s;
            }
        }
    }

    /// **Admit `who` — joining IS a capability grant.** Installs a real player cell
    /// holding a cap to the guild cell (its membership mandate) and enrols the identity
    /// on the board. Returns the member's cell id (the actor its guild turns attribute
    /// to). Idempotent: re-admitting a member returns the existing cell.
    pub fn admit(&mut self, who: &DreggIdentity) -> CellId {
        if let Some(&cell) = self.members.get(who) {
            return cell;
        }
        let seed = self.take_seed();
        let mut cell = make_open_cell(seed, 0);
        cell.capabilities
            .grant(self.guild_cell, AuthRequired::None)
            .expect("granting the guild cap to a new member");
        let member = self.world.genesis_install(cell);
        self.members.insert(who.clone(), member);
        self.board.enrol(who.clone());
        member
    }

    /// **Install a NON-member cell** — a real inhabitant of the same world that holds
    /// NO cap to the guild cell. Its attempt to act on guild state is refused
    /// (`CapabilityNotHeld`) — the non-vacuous other side of the membership tooth.
    pub fn install_stranger(&mut self) -> CellId {
        let seed = self.take_seed();
        // An open cell with no guild cap (it may exist in the world, but cannot touch
        // the guild cell).
        self.world.genesis_install(make_open_cell(seed, 0))
    }

    /// Whether `who` is a member (holds the guild cap).
    pub fn is_member(&self, who: &DreggIdentity) -> bool {
        self.members.contains_key(who)
    }

    /// The member's player cell, if `who` is a member.
    pub fn member_cell(&self, who: &DreggIdentity) -> Option<CellId> {
        self.members.get(who).copied()
    }

    /// The current roster (member identities).
    pub fn roster(&self) -> impl Iterator<Item = &DreggIdentity> {
        self.members.keys()
    }

    /// **Act on the shared guild cell** as `actor` — a real cap-bounded turn on the
    /// executor (write the actor's identity tag into the guild presence slot). A member
    /// (holds the guild cap) COMMITS; a non-member (no cap) is a real `CapabilityNotHeld`
    /// refusal, never a silent apply. This is the membership tooth, driven end-to-end.
    pub fn act_on_guild(&mut self, actor: CellId) -> CommandOutcome {
        let effects: Vec<Effect> = vec![set_field(
            self.guild_cell,
            SLOT_GUILD_PRESENCE,
            actor_tag(actor),
        )];
        let turn = self.world.turn(actor, effects);
        match self.world.commit_turn(turn) {
            CommitOutcome::Committed { receipt, .. } => CommandOutcome::Committed {
                receipt: receipt.turn_hash,
            },
            CommitOutcome::Rejected { reason, .. } => CommandOutcome::Refused { reason },
            CommitOutcome::Queued { .. } => CommandOutcome::Refused {
                reason: "the guild world is suspended — the turn was staged, not committed".into(),
            },
        }
    }

    /// Read the guild cell's presence slot (the last member tag that landed) — `None`
    /// if unset. Used to prove anti-ghost: a refused non-member write leaves it untouched.
    pub fn presence(&self) -> Option<dregg_cell::FieldElement> {
        self.world
            .ledger()
            .get(&self.guild_cell)
            .map(|c| c.state.fields[SLOT_GUILD_PRESENCE])
    }

    /// Borrow the guild's leaderboard (the aggregate of un-forgeable clears).
    pub fn board(&self) -> &GuildBoard {
        &self.board
    }

    /// Mutably borrow the guild's leaderboard (to record verified clears / survivors).
    pub fn board_mut(&mut self) -> &mut GuildBoard {
        &mut self.board
    }

    /// The guild's aggregate proven stats — the guild-vs-guild ranking key.
    pub fn stats(&self) -> GuildStats {
        self.board.stats()
    }
}
