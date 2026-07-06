//! THE DUNGEON — a MUD world modelled as a graph of room/entity CELLS, with player
//! commands lowered to cap-bounded verified TURNS.
//!
//! The mapping (from `docs/deos/SPWEEN-ON-DREGG.md` §4.3 "A MUD"):
//!   - a **room** is a cell (`first-room`'s `Room { cell, .. }` shape) — its state fields hold
//!     what is in the room (who is present, what has been dropped, what has been said);
//!   - a **player / character** is an inhabitant cell that acts ONLY through a mandate it
//!     provably can't exceed — its held *capabilities*: which rooms/entities it may touch;
//!   - a **command** (`go north`, `take sword`, `say hi`) is a cap-bounded turn on a world
//!     cell: it re-verifies (a real signed `TurnReceipt`), nobody can forge another player's
//!     move (an ungranted target is a real `CapabilityNotHeld` executor refusal), and the
//!     world can't be secretly rewritten (turns land on the ledger).
//!
//! Everything here is REAL dregg: [`starbridge_v2::world::World`] cells + the real
//! `embedded-executor`. Nothing is stubbed — a "cheat" is an executor refusal, not app
//! bookkeeping.

use dregg_cell::{AuthRequired, CellId, FieldElement};
use dregg_turn::action::Effect;

use starbridge_v2::world::{make_open_cell, set_field, World};

/// The state slot a room uses for the "who is present" presence mark (a `go`/enter write).
pub const SLOT_PRESENCE: usize = 0;
/// The state slot a room uses for the last "say" glyph (a `say` write).
pub const SLOT_SAY: usize = 1;
/// The state slot an entity uses for its OWNER mark (a `take` write — the contested grab).
pub const SLOT_OWNER: usize = 0;

/// A player command — the MUD verbs, each of which lowers to the effects of ONE cap-bounded
/// turn on a world cell (see [`WorldCell::lower`]).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Command {
    /// `go <room>` — enter a room, marking your presence in its presence slot.
    Go { room: CellId },
    /// `take <entity>` — claim an entity by stamping your identity into its owner slot. Two
    /// players who `take` the SAME entity write the same address ⇒ a `#`-conflict at stitch.
    Take { entity: CellId },
    /// `say <glyph>` in a room — write a message glyph into the room's say slot.
    Say { room: CellId, glyph: FieldElement },
    /// A RAW forge attempt — try to drive `<target>`'s presence directly (e.g. force another
    /// player's character to move). Authorized ONLY if the actor holds a cap to `target`;
    /// otherwise a real `CapabilityNotHeld` refusal. This is how a "forge another player's
    /// move" is expressed and refused.
    Force { target: CellId, value: FieldElement },
}

/// **The WorldCell interface** — LOCAL definition (the world-state-as-cell + command→turn
/// lowering), reconciled with the real `spween-dregg` `WorldCell` at registration.
///
/// Honest seam: in the full spween-on-dregg stack the `WorldCell` is compiled from a spween
/// `Scene` — the passage graph becomes a `CellProgram` and choices/effects become the turnable
/// transitions (`SPWEEN-ON-DREGG.md` §6, the "spween → cell compiler"). Here we model the
/// command→turn lowering DIRECTLY over `set_field` effects; the trait is the seam the compiler
/// slots into, so a `mud-dregg` dungeon and a compiled spween world present the SAME surface:
/// a `focus` cell whose capability reach is the world in view, and a `lower` from a player's
/// command to the effects of a cap-bounded turn.
pub trait WorldCell {
    /// The focus cell whose capability reach defines the world in view — the cull centre a
    /// [`starbridge_v2::branch_stitch_session::BranchStitchSession`] forks around.
    fn focus(&self) -> CellId;

    /// Lower a player's command (issued by `actor`) to the effects of ONE cap-bounded turn.
    /// The executor still checks `actor` holds a cap to every cell these effects touch — the
    /// lowering grants no authority, it only *names* the world write a command intends.
    fn lower(&self, actor: CellId, cmd: &Command) -> Vec<Effect>;
}

/// A 32-byte identity tag derived from a cell id — the value a `go`/`take` write stamps so the
/// room/entity records WHO acted (and so two different actors writing the same slot genuinely
/// collide with distinct readings, never a coincidental match).
pub fn actor_tag(actor: CellId) -> FieldElement {
    let mut tag = [0u8; 32];
    let bytes = actor.as_bytes();
    let n = bytes.len().min(32);
    tag[..n].copy_from_slice(&bytes[..n]);
    // Salt the low byte so the tag can never be all-zero (the "empty slot" reading), keeping
    // a real write distinguishable from an untouched field.
    tag[31] ^= 0x9D;
    tag
}

/// The cell layout of the dungeon — the graph of room/entity/player cells. Also the
/// [`WorldCell`] for this world (its `focus` is the `dungeon` root; its `lower` is the MUD
/// command semantics).
#[derive(Clone, Copy, Debug)]
pub struct Layout {
    /// The dungeon ROOT cell — the WorldCell focus. It holds caps reaching every player and
    /// every room/entity, so it is the natural cull centre a branch-stitch session forks
    /// around (the whole dungeon is "in view").
    pub dungeon: CellId,
    /// The two players' character (inhabitant) cells — the turn agents. A command is signed by
    /// (attributed to) one of these; nobody can forge a command as another player.
    pub alice: CellId,
    pub bob: CellId,
    /// The entry hall (a room cell). Alice may act here; Bob may not.
    pub hall: CellId,
    /// The cavern (a room cell), reached by a north passage. Bob may act here; Alice may not.
    pub cavern: CellId,
    /// THE ONE SWORD (an entity cell), reachable by BOTH players — the contested resource whose
    /// `take` is the `#`-conflict when both grab it.
    pub sword: CellId,
}

impl WorldCell for Layout {
    fn focus(&self) -> CellId {
        self.dungeon
    }

    fn lower(&self, actor: CellId, cmd: &Command) -> Vec<Effect> {
        match cmd {
            Command::Go { room } => vec![set_field(*room, SLOT_PRESENCE, actor_tag(actor))],
            Command::Take { entity } => vec![set_field(*entity, SLOT_OWNER, actor_tag(actor))],
            Command::Say { room, glyph } => vec![set_field(*room, SLOT_SAY, *glyph)],
            Command::Force { target, value } => vec![set_field(*target, SLOT_PRESENCE, *value)],
        }
    }
}

/// A live dungeon: a real [`World`] plus its cell [`Layout`]. Single-player commands are issued
/// against this world; multiplayer divergent play forks it into a branch-stitch session
/// (see [`crate::scenario`]).
pub struct Dungeon {
    world: World,
    layout: Layout,
}

/// The outcome of issuing a command on the live dungeon — a thin, legible echo of the real
/// [`starbridge_v2::world::CommitOutcome`] so a caller/test reads the tooth directly.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CommandOutcome {
    /// The command committed — a real signed turn landed on the ledger; carries the receipt
    /// hash (proof it re-verified).
    Committed { receipt: [u8; 32] },
    /// The command was REFUSED by the real executor (e.g. `CapabilityNotHeld` — the actor holds
    /// no cap to a targeted cell: a forged move). Carries the executor's reason.
    Refused { reason: String },
}

impl CommandOutcome {
    /// Did the command commit (a genuine, receipted turn)?
    pub fn committed(&self) -> bool {
        matches!(self, CommandOutcome::Committed { .. })
    }
    /// Was the command refused (the cap tooth firing)?
    pub fn refused(&self) -> bool {
        matches!(self, CommandOutcome::Refused { .. })
    }
}

impl Dungeon {
    /// Build the dungeon world: five world cells and two players, wired with ORDINARY cap-gated
    /// genesis (no root self-grant). The capability grants ARE the players' mandates:
    ///
    /// | player | may act in |
    /// |--------|------------|
    /// | alice  | `hall`, `sword` |
    /// | bob    | `cavern`, `sword` |
    ///
    /// So the `sword` is shared (both may `take` it — the contested resource), the `hall` is
    /// Alice-only and the `cavern` Bob-only (disjoint reach — clean-merge territory), and
    /// anything OUTSIDE a player's grants (Alice into the cavern, or Alice forcing Bob's
    /// character) is a real executor refusal.
    pub fn new() -> Dungeon {
        let mut world = World::new().with_executor_signing_key([0x6Du8; 32]);

        // The room / entity cells (world state as cells).
        let hall = world.genesis_cell(0x51, 0);
        let cavern = world.genesis_cell(0x52, 0);
        let sword = world.genesis_cell(0x53, 0);

        // Alice — may act in the hall and grab the sword.
        let mut alice = make_open_cell(0x0A, 0);
        alice.capabilities.grant(hall, AuthRequired::None).unwrap();
        alice.capabilities.grant(sword, AuthRequired::None).unwrap();
        let alice = world.genesis_install(alice);

        // Bob — may act in the cavern and grab the sword.
        let mut bob = make_open_cell(0x0B, 0);
        bob.capabilities.grant(cavern, AuthRequired::None).unwrap();
        bob.capabilities.grant(sword, AuthRequired::None).unwrap();
        let bob = world.genesis_install(bob);

        // The dungeon ROOT — the WorldCell focus, reaching every player + room + entity so the
        // whole dungeon rides the cap-bounded cull when a branch is forked around it.
        let mut dungeon = make_open_cell(0x40, 0);
        dungeon
            .capabilities
            .grant(alice, AuthRequired::None)
            .unwrap();
        dungeon.capabilities.grant(bob, AuthRequired::None).unwrap();
        dungeon
            .capabilities
            .grant(hall, AuthRequired::None)
            .unwrap();
        dungeon
            .capabilities
            .grant(cavern, AuthRequired::None)
            .unwrap();
        dungeon
            .capabilities
            .grant(sword, AuthRequired::None)
            .unwrap();
        let dungeon = world.genesis_install(dungeon);

        Dungeon {
            world,
            layout: Layout {
                dungeon,
                alice,
                bob,
                hall,
                cavern,
                sword,
            },
        }
    }

    /// The dungeon's cell layout (the [`WorldCell`]).
    pub fn layout(&self) -> Layout {
        self.layout
    }

    /// The live world (read-only) — for reading a room/entity's committed state.
    pub fn world(&self) -> &World {
        &self.world
    }

    /// Consume the dungeon, yielding its `World` (to hand to a branch-stitch session) and its
    /// `Layout`.
    pub fn into_parts(self) -> (World, Layout) {
        (self.world, self.layout)
    }

    /// Read a cell's state field (e.g. a room's presence slot) — `None` if the cell is absent.
    pub fn field(&self, cell: CellId, slot: usize) -> Option<FieldElement> {
        self.world.ledger().get(&cell).map(|c| c.state.fields[slot])
    }

    /// **Issue a player command against the live dungeon** — the single-player path. Lowers the
    /// command through the [`WorldCell`] seam, builds a real turn signed by `actor`, and commits
    /// it through the real embedded executor. A command the actor's caps do not authorize is
    /// REFUSED fail-closed (the executor's `CapabilityNotHeld`), never silently applied.
    pub fn issue(&mut self, actor: CellId, cmd: &Command) -> CommandOutcome {
        let effects = self.layout.lower(actor, cmd);
        let turn = self.world.turn(actor, effects);
        match self.world.commit_turn(turn) {
            starbridge_v2::world::CommitOutcome::Committed { receipt, .. } => {
                CommandOutcome::Committed {
                    receipt: receipt.turn_hash,
                }
            }
            starbridge_v2::world::CommitOutcome::Rejected { reason, .. } => {
                CommandOutcome::Refused { reason }
            }
            starbridge_v2::world::CommitOutcome::Queued { .. } => CommandOutcome::Refused {
                reason: "the world is suspended — the command was staged, not committed".into(),
            },
        }
    }
}

impl Default for Dungeon {
    fn default() -> Self {
        Dungeon::new()
    }
}
