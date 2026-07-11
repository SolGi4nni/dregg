//! # `mud` — a MULTI-PLAYER shared world on the REAL multi-actor substrate
//!
//! WIDTH. The single-cell keep proved one serial writer; [`crate::multicell`] proved a
//! GRAPH of cells with a real cross-cell gate — but BOTH are driven by ONE identity (the
//! `EmbeddedExecutor` is a single writer under one agent nonce). This module closes the
//! other half of the ceiling this crate named (`lib.rs` §"CEILING 1 — the MULTI-CELL
//! boundary (concurrency & authority)"): a world inhabited by SEVERAL players AT ONCE,
//! each its OWN cell/identity, each acting through a mandate it provably cannot exceed.
//!
//! ## The model — one shared world, many player-cells
//!
//! The world is a graph of real cells sharing ONE [`World`] ledger:
//!
//! | cell | role |
//! |------|------|
//! | [`plaza`](Layout::plaza) | the shared entry hall — every player may act here |
//! | [`north_walk`](Layout::north_walk) | a room only ALICE holds a cap to |
//! | [`south_vault`](Layout::south_vault) | a room only BOB holds a cap to |
//! | [`lantern`](Layout::lantern) | the ONE contested ITEM — its own cell, `WriteOnce` owner slot |
//! | [`alice`](Layout::alice) / [`bob`](Layout::bob) / [`carol`](Layout::carol) | the PLAYER cells (turn agents) |
//!
//! A **player** is a real cell whose held [`CapabilitySet`](dregg_cell::CapabilitySet) IS
//! its mandate: which rooms/items it may touch. A **command** (`go`/`take`/`say`) lowers to
//! the effects of ONE cap-bounded turn ([`World::turn`] + [`World::commit_turn`]): the real
//! executor admits it IFF the acting player holds a cap to every touched cell. Nobody can
//! forge another player's move — an ungranted target is a real `CapabilityNotHeld` refusal
//! ([`MudWorld::issue`] returns [`CommandOutcome::Refused`], never a silent apply).
//!
//! ## The contested item — one owner, two ways it bites
//!
//! The lantern is the shared resource both Alice and Bob reach for. It bites in TWO real
//! registers, matching the `mud-dregg` precedent:
//!
//! * **Serialized (one shared world).** The lantern's cell carries a real
//!   [`StateConstraint::WriteOnce`] on its owner slot. On the ONE live world the first
//!   grabber's `take` commits (owner `0 → their tag`); a second player's `take` writes a
//!   DIFFERENT tag onto an already-set write-once slot and is a REAL executor refusal. The
//!   item ends with exactly ONE owner (anti-ghost) — [`MudWorld`], [`contested_take_one_owner`].
//! * **Concurrent (divergent timelines).** When the two grabs happen on genuinely
//!   CONCURRENT forks, [`BranchStitchSession`] merges the timelines under the
//!   settlement-sound gate: disjoint edits fold clean, but both players writing the ONE
//!   lantern's owner address is a real `#`-conflict (`ValueCollision`) held fail-closed —
//!   the stitch does not settle, and the conflict names the exact contested address. See
//!   [`concurrent_grab_is_a_stitch_conflict`].
//!
//! The world PERSISTS across players: one ledger, many actors. Alice's committed turn in
//! `north_walk` and Bob's in `south_vault` both stand in the same live world at once
//! ([`shared_world_reflects_every_players_committed_turn`]).
//!
//! ## Honest scope — what a FULL persistent MUD adds beyond this substrate
//!
//! This proves the SUBSTRATE — multiple player-cells acting via real turns on one shared,
//! authority-bounded world, with contested resources resolved as real conflicts. A shippable
//! always-on MUD adds three things ORTHOGONAL to it, each a named follow-on, not a hole here:
//!
//! * **Durable ledger persistence.** The world here is in-process (ephemeral). A live MUD
//!   needs the durable image ([`World::open`]'s redb dual-write / the pg-dregg seam) so the
//!   world survives a restart. The commit path is identical; only the backing store changes.
//! * **Real-time presence / notification.** Players here act turn-by-turn in one thread. A
//!   live MUD needs a transport that pushes each committed turn to every connected player
//!   (the dynamics stream → websockets / the federation `NodeTarget` fan-out) so others SEE a
//!   move as it lands. The turns are already events; the push layer is the add.
//! * **Matchmaking / session lifecycle.** Player cells are birthed at genesis here. A live
//!   MUD needs join/leave, identity onboarding (a player mints its own cell + caps), and
//!   room capacity — a session layer ABOVE the world, not a change to it.

use dregg_cell::{AuthRequired, CellId, CellProgram, FieldElement, StateConstraint};
use dregg_turn::action::Effect;

use starbridge_v2::world::{CommitOutcome, World, make_open_cell, set_field};

/// The room slot recording "who is present" — a `go`/enter write.
pub const SLOT_PRESENCE: usize = 0;
/// The room slot recording the last "say" glyph — a `say` write.
pub const SLOT_SAY: usize = 1;
/// The item slot recording its OWNER — a `take` write. Constrained `WriteOnce`, so the
/// first grabber's tag freezes it and a rival second claim is refused.
pub const SLOT_OWNER: usize = 0;

/// The executor signing seed the shared world commits receipts under (a fixed demo key,
/// so every committed receipt carries a genuine executor signature under one authority).
const EXECUTOR_SEED: [u8; 32] = [0x6D; 32];

/// A 32-byte identity tag derived from a player's cell id — the value a `go`/`take` write
/// stamps so the room/item records WHO acted, and two distinct players write distinct,
/// genuinely-colliding values (never a coincidental match, never the all-zero empty slot).
pub fn actor_tag(actor: CellId) -> FieldElement {
    let mut tag = [0u8; 32];
    let bytes = actor.as_bytes();
    let n = bytes.len().min(32);
    tag[..n].copy_from_slice(&bytes[..n]);
    tag[31] ^= 0x9D; // salt the low byte: a real write is never the empty reading.
    tag
}

/// A player command — the MUD verbs, each of which lowers to the effects of ONE cap-bounded
/// turn on a world cell (see [`Layout::lower`]). The executor still checks the acting player
/// holds a cap to every touched cell; the lowering NAMES the write, it grants no authority.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Command {
    /// `go <room>` — enter a room, marking your presence in its presence slot.
    Go { room: CellId },
    /// `take <item>` — claim an item by stamping your identity into its owner slot. Two
    /// players taking the SAME item write distinct tags onto its `WriteOnce` slot — the
    /// contested grab (serialized: the second is refused; concurrent: a stitch `#`-conflict).
    Take { item: CellId },
    /// `say <glyph>` in a room — write a message glyph into the room's say slot.
    Say { room: CellId, glyph: FieldElement },
    /// A RAW forge attempt — drive `<target>`'s presence directly (e.g. force another
    /// player's cell to move). Authorized ONLY if the actor holds a cap to `target`;
    /// otherwise a real `CapabilityNotHeld` refusal. This is how "forge another player's
    /// move" is expressed — and refused.
    Force { target: CellId, value: FieldElement },
}

/// The cell layout of the shared world — the graph of room / item / player cells, and the
/// command→turn lowering ([`Self::lower`]).
#[derive(Clone, Copy, Debug)]
pub struct Layout {
    /// The world ROOT cell — the cull centre a [`BranchStitchSession`] forks around. It
    /// holds caps reaching every player + room + item, so the whole world is "in view".
    pub root: CellId,
    /// The three player (inhabitant) cells — the turn agents. A command is attributed to
    /// exactly one of these; nobody can forge a command as another player.
    pub alice: CellId,
    pub bob: CellId,
    pub carol: CellId,
    /// The shared entry hall — every player holds a cap here.
    pub plaza: CellId,
    /// A room only Alice may act in (Bob/Carol hold no cap → over-reach is refused).
    pub north_walk: CellId,
    /// A room only Bob may act in.
    pub south_vault: CellId,
    /// THE ONE contested item — reachable by every player, `WriteOnce` owner: one grabber wins.
    pub lantern: CellId,
}

impl Layout {
    /// The cull centre a branch-stitch session forks around (the world root).
    pub fn focus(&self) -> CellId {
        self.root
    }

    /// Lower a player's command (issued by `actor`) to the effects of ONE cap-bounded turn.
    pub fn lower(&self, actor: CellId, cmd: &Command) -> Vec<Effect> {
        match cmd {
            Command::Go { room } => vec![set_field(*room, SLOT_PRESENCE, actor_tag(actor))],
            Command::Take { item } => vec![set_field(*item, SLOT_OWNER, actor_tag(actor))],
            Command::Say { room, glyph } => vec![set_field(*room, SLOT_SAY, *glyph)],
            Command::Force { target, value } => vec![set_field(*target, SLOT_PRESENCE, *value)],
        }
    }
}

/// The outcome of issuing a command on the shared world — a thin, legible echo of the real
/// [`CommitOutcome`] so a caller/test reads the tooth directly.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CommandOutcome {
    /// The command committed — a real signed turn landed on the shared ledger; carries the
    /// receipt's `turn_hash` (proof it re-verified).
    Committed { receipt: [u8; 32] },
    /// The command was REFUSED by the real executor (e.g. `CapabilityNotHeld` — the player
    /// holds no cap to a targeted cell: a forged / over-reaching move; or the lantern's
    /// `WriteOnce` refusing a rival second grab). Carries the executor's reason.
    Refused { reason: String },
}

impl CommandOutcome {
    /// Did the command commit (a genuine, receipted turn)?
    pub fn committed(&self) -> bool {
        matches!(self, CommandOutcome::Committed { .. })
    }
    /// Was the command refused (the cap / write-once tooth firing)?
    pub fn refused(&self) -> bool {
        matches!(self, CommandOutcome::Refused { .. })
    }
    /// The committed receipt hash, if it committed.
    pub fn receipt(&self) -> Option<[u8; 32]> {
        match self {
            CommandOutcome::Committed { receipt } => Some(*receipt),
            CommandOutcome::Refused { .. } => None,
        }
    }
    /// The refusal reason, if it was refused.
    pub fn reason(&self) -> Option<&str> {
        match self {
            CommandOutcome::Refused { reason } => Some(reason),
            CommandOutcome::Committed { .. } => None,
        }
    }
}

/// A live multi-player shared world: the real [`World`] ledger + its cell [`Layout`].
pub struct MudWorld {
    world: World,
    layout: Layout,
}

impl MudWorld {
    /// Build the shared world: rooms + the contested item + three players, wired with
    /// ORDINARY cap-gated genesis (no root self-grant). The capability grants ARE the
    /// players' mandates:
    ///
    /// | player | may act in |
    /// |--------|------------|
    /// | alice  | `plaza`, `north_walk`, `lantern` |
    /// | bob    | `plaza`, `south_vault`, `lantern` |
    /// | carol  | `plaza`, `lantern` |
    ///
    /// So the `lantern` is shared (all three may `take` it — the contested resource), the
    /// `plaza` is common ground, `north_walk`/`south_vault` are single-player rooms
    /// (disjoint reach), and anything OUTSIDE a player's grants (Carol into `north_walk`,
    /// Alice forcing Bob's cell) is a real executor refusal.
    pub fn new() -> MudWorld {
        let mut world = World::new().with_executor_signing_key(EXECUTOR_SEED);

        // The room / item cells (world state as cells). The lantern gets its own cell.
        let plaza = world.genesis_cell(0x51, 0);
        let north_walk = world.genesis_cell(0x52, 0);
        let south_vault = world.genesis_cell(0x53, 0);
        let lantern = world.genesis_cell(0x54, 0);

        // THE CONTESTED-ITEM TOOTH: the lantern's owner slot is WRITE-ONCE. The first
        // grabber (0 → their tag) commits; a rival second claim (tag → other) is a real
        // executor refusal on the item's OWN cell — one owner, first-grabber-wins.
        world.set_cell_program(
            &lantern,
            CellProgram::Predicate(vec![StateConstraint::WriteOnce {
                index: SLOT_OWNER as u8,
            }]),
        );

        // The three players — each its own cell/identity holding caps that are its mandate.
        let alice = install_player(&mut world, 0x0A, &[plaza, north_walk, lantern]);
        let bob = install_player(&mut world, 0x0B, &[plaza, south_vault, lantern]);
        let carol = install_player(&mut world, 0x0C, &[plaza, lantern]);

        // The world ROOT — the cull centre, reaching every player + room + item so the whole
        // world rides the cap-bounded cull when a branch is forked around it.
        let root = install_player(
            &mut world,
            0x40,
            &[alice, bob, carol, plaza, north_walk, south_vault, lantern],
        );

        MudWorld {
            world,
            layout: Layout {
                root,
                alice,
                bob,
                carol,
                plaza,
                north_walk,
                south_vault,
                lantern,
            },
        }
    }

    /// The shared world's cell [`Layout`].
    pub fn layout(&self) -> Layout {
        self.layout
    }

    /// The live world (read-only) — for reading a room/item's committed state.
    pub fn world(&self) -> &World {
        &self.world
    }

    /// Read a cell's state field (e.g. a room's presence, the item's owner) — `None` if the
    /// cell is absent from the shared ledger.
    pub fn field(&self, cell: CellId, slot: usize) -> Option<FieldElement> {
        self.world.ledger().get(&cell).map(|c| c.state.fields[slot])
    }

    /// Consume the world, yielding its [`World`] (to hand to a branch-stitch session) and
    /// its [`Layout`].
    pub fn into_parts(self) -> (World, Layout) {
        (self.world, self.layout)
    }

    /// **Issue a player command against the shared world** — the live multi-actor path.
    /// Lowers the command through [`Layout::lower`], builds a real turn attributed to
    /// `actor` ([`World::turn`]), and commits it through the real embedded executor
    /// ([`World::commit_turn`]). A command the actor's caps do not authorize is REFUSED
    /// fail-closed (the executor's `CapabilityNotHeld`), never silently applied; the
    /// lantern's `WriteOnce` refuses a rival second grab the same way.
    pub fn issue(&mut self, actor: CellId, cmd: &Command) -> CommandOutcome {
        let effects = self.layout.lower(actor, cmd);
        let turn = self.world.turn(actor, effects);
        match self.world.commit_turn(turn) {
            CommitOutcome::Committed { receipt, .. } => CommandOutcome::Committed {
                receipt: receipt.turn_hash,
            },
            CommitOutcome::Rejected { reason, .. } => CommandOutcome::Refused { reason },
            CommitOutcome::Queued { .. } => CommandOutcome::Refused {
                reason: "the world is suspended — the command was staged, not committed".into(),
            },
        }
    }
}

impl Default for MudWorld {
    fn default() -> Self {
        MudWorld::new()
    }
}

/// Install an open player/root cell holding caps (`AuthRequired::None`) reaching each cell
/// in `caps` — the cell's mandate. Returns its genesis cell id.
fn install_player(world: &mut World, seed: u8, caps: &[CellId]) -> CellId {
    let mut cell = make_open_cell(seed, 0);
    for &target in caps {
        cell.capabilities
            .grant(target, AuthRequired::None)
            .expect("granting a genesis cap to a player cell");
    }
    world.genesis_install(cell)
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_turn::umem::UKey;
    use starbridge_v2::branch_stitch_session::{BranchStitchSession, StitchVerdict};

    /// A `UKey` for a cell's state field — the universal-memory address a stitch
    /// merges/collides on.
    fn field_key(cell: CellId, slot: u64) -> UKey {
        UKey::Field { cell, slot }
    }

    /// The players are genuinely DISTINCT real cells in ONE shared ledger, and their tags
    /// collide-distinctly (a real `#` is possible, never a coincidence).
    #[test]
    fn players_are_distinct_cells_in_one_shared_ledger() {
        let mud = MudWorld::new();
        let l = mud.layout();
        // Distinct identities.
        assert_ne!(l.alice, l.bob);
        assert_ne!(l.bob, l.carol);
        assert_ne!(l.alice, l.carol);
        // All present in the SAME ledger (one world, many actors).
        for id in [
            l.alice,
            l.bob,
            l.carol,
            l.plaza,
            l.north_walk,
            l.south_vault,
            l.lantern,
        ] {
            assert!(
                mud.world().ledger().get(&id).is_some(),
                "every player/room/item is a real cell in the one shared ledger"
            );
        }
        // Distinct tags — two grabs of the one item genuinely collide with distinct readings.
        assert_ne!(actor_tag(l.alice), actor_tag(l.bob));
        assert_ne!(actor_tag(l.bob), actor_tag(l.carol));
    }

    /// TWO players act via REAL turns on ONE world. Alice enters the plaza (a real signed,
    /// receipted turn) and the plaza CELL records her; Bob enters the south vault and it
    /// records him. The single shared ledger holds BOTH players' committed state at once.
    #[test]
    fn two_players_act_via_real_turns_on_one_world() {
        let mut mud = MudWorld::new();
        let l = mud.layout();

        let a = mud.issue(l.alice, &Command::Go { room: l.plaza });
        assert!(a.committed(), "alice may act in the plaza: {a:?}");
        assert_ne!(a.receipt().unwrap(), [0u8; 32], "a genuine receipted turn");

        let b = mud.issue(
            l.bob,
            &Command::Go {
                room: l.south_vault,
            },
        );
        assert!(b.committed(), "bob may act in his vault: {b:?}");

        // The distinct receipts prove two independent players' turns landed.
        assert_ne!(a.receipt().unwrap(), b.receipt().unwrap());

        // The ONE shared world reflects BOTH committed turns simultaneously.
        assert_eq!(mud.field(l.plaza, SLOT_PRESENCE), Some(actor_tag(l.alice)));
        assert_eq!(
            mud.field(l.south_vault, SLOT_PRESENCE),
            Some(actor_tag(l.bob))
        );
    }

    /// A move a player is NOT capability-authorized for is a real `CapabilityNotHeld`
    /// refusal — nobody can forge another player's move, nor reach outside their mandate.
    #[test]
    fn unauthorized_move_is_a_real_capability_refusal() {
        let mut mud = MudWorld::new();
        let l = mud.layout();

        // Carol holds no cap to north_walk (Alice's room) — over-reach REFUSED.
        let reach = mud.issue(l.carol, &Command::Go { room: l.north_walk });
        assert!(reach.refused(), "carol has no cap to north_walk: {reach:?}");
        assert!(
            reach.reason().unwrap().to_lowercase().contains("cap"),
            "the refusal is a capability refusal, got: {}",
            reach.reason().unwrap()
        );
        assert_eq!(
            mud.field(l.north_walk, SLOT_PRESENCE),
            Some([0u8; 32]),
            "anti-ghost: the over-reach applied nothing"
        );

        // Alice tries to FORGE Bob's move — drive Bob's cell directly. No cap to `bob` → refused.
        let forge = mud.issue(
            l.alice,
            &Command::Force {
                target: l.bob,
                value: actor_tag(l.alice),
            },
        );
        assert!(forge.refused(), "alice cannot forge bob's move: {forge:?}");
        assert_eq!(
            mud.field(l.bob, SLOT_PRESENCE),
            Some([0u8; 32]),
            "anti-ghost: bob's cell is untouched by the forge"
        );
    }

    /// THE HARD GATE — the contested item, serialized on the ONE shared world. Alice grabs
    /// the lantern (a real `WriteOnce` transition `0 → alice`); Bob's rival grab of the SAME
    /// lantern (`alice → bob`) is a REAL executor refusal. The item ends with exactly ONE
    /// owner (anti-ghost) — the first grabber, held by the write that landed first.
    #[test]
    fn contested_take_one_owner() {
        let mut mud = MudWorld::new();
        let l = mud.layout();

        let first = mud.issue(l.alice, &Command::Take { item: l.lantern });
        assert!(first.committed(), "alice's first grab commits: {first:?}");
        assert_eq!(
            mud.field(l.lantern, SLOT_OWNER),
            Some(actor_tag(l.alice)),
            "the lantern belongs to alice"
        );

        // Bob reaches for the SAME lantern — the WriteOnce owner slot is already set → REFUSED.
        let rival = mud.issue(l.bob, &Command::Take { item: l.lantern });
        assert!(
            rival.refused(),
            "a rival grab of the one lantern is refused (WriteOnce): {rival:?}"
        );

        // Carol too — still refused; the item cannot be re-owned.
        let third = mud.issue(l.carol, &Command::Take { item: l.lantern });
        assert!(third.refused(), "carol's grab is refused too: {third:?}");

        // Anti-ghost: exactly ONE owner, and it is the first grabber.
        assert_eq!(
            mud.field(l.lantern, SLOT_OWNER),
            Some(actor_tag(l.alice)),
            "the lantern still has exactly one owner — alice, the first grabber"
        );
        assert_ne!(
            actor_tag(l.alice),
            actor_tag(l.bob),
            "a genuine value collision, not a coincidence"
        );
    }

    /// The shared world PERSISTS across players — one ledger, many actors. Alice acts in the
    /// north walk, Bob in the south vault, Carol says a glyph in the plaza; the single live
    /// world reflects every player's committed turn at once.
    #[test]
    fn shared_world_reflects_every_players_committed_turn() {
        let mut mud = MudWorld::new();
        let l = mud.layout();

        assert!(
            mud.issue(l.alice, &Command::Go { room: l.north_walk })
                .committed()
        );
        assert!(
            mud.issue(
                l.bob,
                &Command::Go {
                    room: l.south_vault
                }
            )
            .committed()
        );
        let glyph = dregg_app_framework::field_from_u64(0xBEEF);
        assert!(
            mud.issue(
                l.carol,
                &Command::Say {
                    room: l.plaza,
                    glyph
                }
            )
            .committed()
        );

        // ONE ledger holds all three actors' committed state simultaneously.
        assert_eq!(
            mud.field(l.north_walk, SLOT_PRESENCE),
            Some(actor_tag(l.alice))
        );
        assert_eq!(
            mud.field(l.south_vault, SLOT_PRESENCE),
            Some(actor_tag(l.bob))
        );
        assert_eq!(mud.field(l.plaza, SLOT_SAY), Some(glyph));
    }

    /// The CONCURRENT face of the contest — divergent player-timelines. Alice and Bob each
    /// FORK the shared world and BOTH grab the ONE lantern (the SAME owner address). At
    /// stitch this is a genuine `#`-conflict: the two timelines cannot silently merge. The
    /// stitch is WITHHELD fail-closed, surfaced as a conflict object naming the exact
    /// contested address — both readings kept, never a silent last-writer-wins.
    #[test]
    fn concurrent_grab_is_a_stitch_conflict() {
        let (world, l) = MudWorld::new().into_parts();
        let session = BranchStitchSession::open(world, l.focus(), 3);

        // Alice forks her own timeline and grabs the lantern.
        let mut alice = session.fork();
        alice
            .drive(alice.turn(
                l.alice,
                l.lower(l.alice, &Command::Take { item: l.lantern }),
            ))
            .expect("alice grabs the lantern on her own branch — a real verified turn");

        // Bob forks his own timeline and ALSO grabs the ONE lantern (same owner address).
        let mut bob = session.fork();
        bob.drive(bob.turn(l.bob, l.lower(l.bob, &Command::Take { item: l.lantern })))
            .expect("bob grabs the lantern on his own branch");

        let v: StitchVerdict = session.stitch(&alice, &bob);
        assert!(
            !v.settles(),
            "two players grabbing the one lantern is a genuine conflict — the stitch does NOT settle"
        );
        assert!(
            v.settled_root.is_none(),
            "no settled root while the conflict is live (fail-closed)"
        );
        assert_eq!(
            v.state_conflicts,
            vec![field_key(l.lantern, SLOT_OWNER as u64)],
            "the conflict names the EXACT contested address (lantern.owner) — both readings kept, no silent LWW"
        );
        // Main stayed pristine — the divergence was imaginary until a verdict is applied.
        assert_eq!(
            session
                .base()
                .ledger()
                .get(&l.lantern)
                .unwrap()
                .state
                .fields[SLOT_OWNER],
            [0u8; 32],
            "the shared world's lantern is untouched — the timelines were imaginary"
        );
    }

    /// The DISJOINT face — concurrent play that DOES merge. Alice explores the north walk on
    /// her fork, Bob the south vault on his (disjoint addresses); the stitch settles and both
    /// players' edits are present in the conflict-free union (co-drive, never LWW).
    #[test]
    fn concurrent_disjoint_play_merges_clean() {
        let (world, l) = MudWorld::new().into_parts();
        let session = BranchStitchSession::open(world, l.focus(), 3);

        let mut alice = session.fork();
        alice
            .drive(alice.turn(
                l.alice,
                l.lower(l.alice, &Command::Go { room: l.north_walk }),
            ))
            .expect("alice explores the north walk on her branch");

        let mut bob = session.fork();
        bob.drive(bob.turn(
            l.bob,
            l.lower(
                l.bob,
                &Command::Go {
                    room: l.south_vault,
                },
            ),
        ))
        .expect("bob explores the south vault on his branch");

        let v = session.stitch(&alice, &bob);
        assert!(
            v.settles(),
            "disjoint edits settle: {:?}",
            v.state_conflicts
        );
        assert!(
            v.settled_root.is_some(),
            "a settled stitch has a merged root"
        );
        assert!(
            v.merged
                .contains(&field_key(l.north_walk, SLOT_PRESENCE as u64)),
            "alice's north-walk edit is in the merge"
        );
        assert!(
            v.merged
                .contains(&field_key(l.south_vault, SLOT_PRESENCE as u64)),
            "bob's south-vault edit is in the merge"
        );
    }
}
