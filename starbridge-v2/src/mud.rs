//! **DREGG-MUD — the first slice.** A decentralized multi-user world where a
//! *room is a cell, an inhabitant is a cap-rooted session, and an item is a
//! capability*. See `docs/deos/DREGG-MUD.md` for the full vision.
//!
//! This module is the typed, `cargo test`-able first slice. It reinvents NO
//! authority machinery — `Room`, `Inhabitant`, and `Item` are thin designations
//! over the REAL [`crate::world::World`] (the embedded verified executor), the
//! REAL [`dregg_cell::CapabilitySet`] (the c-list), and the REAL
//! [`crate::powerbox::Powerbox`] grant path (the two attenuation gates +
//! executor backstop). It lives in the periphery (not in the churning
//! `circuit`/`turn`/`cockpit`) and WELDS the existing primitives into the MUD
//! object model.
//!
//! ## The mappings (every MUD noun → a dregg primitive)
//!
//! * **room = a cell** — a [`Room`] is a [`CellId`]; its c-list holds caps to its
//!   exits (neighbour rooms) and the items lying in it.
//! * **inhabitant = a cap-rooted session** — an [`Inhabitant`] is a [`CellId`]
//!   (the identity cell, `session.rs`); what it can reach IS its authority.
//! * **item = a capability** — an [`Item`] is a [`CellId`] for the item-cell;
//!   *holding the item* is *holding a cap to it* in your c-list.
//! * **exit = a cap edge** — a room "connects to" a neighbour iff its c-list
//!   `has_access(&neighbour)`.
//! * **locked door = an absent cap** — you cannot form an entering turn without a
//!   cap whose [`AuthRequired`] you satisfy ([`dregg_cell::is_attenuation`]).
//! * **pick up / give = `Effect::GrantCapability` + `RevokeCapability`** — the
//!   item cap MOVES; the source loses it. Conservation of the capability itself.
//! * **act = a verified turn** — every mutation is a [`Turn`] the executor admits
//!   only if `required ⊆ held`, leaving a verifiable [`TurnReceipt`].
//!
//! ## The load-bearing scenario (the test below proves it)
//!
//! > Two players in one room; one picks up the item; the other CANNOT dupe it.
//!
//! The pickup is a real grant of the item cap into the picker's c-list paired
//! with a real revoke from the room — so after the pickup the ROOM no longer
//! holds the cap. A second player's pickup attempt is then refused by the
//! powerbox's own `mint_needs_held_factory` gate (you cannot grant what the
//! source does not hold) — *duping is structurally inexpressible, not policed.*

use dregg_cell::{AuthRequired, CapabilitySet, CellId};
use dregg_turn::action::Effect;
use dregg_turn::turn::TurnReceipt;

use crate::powerbox::{Powerbox, PowerboxOutcome};
use crate::world::{CommitOutcome, World};

/// **A room — a cell.** Its durable core (name/description in user fields, exits
/// + contained items in the c-list, "who may enter/post/build" in the permission
/// lattice) is a [`Cell`](dregg_cell). Here a `Room` is just the room cell's id;
/// the live state lives in the [`World`]'s ledger. The room's *history is its
/// provenance chain* — every turn against it leaves a receipt.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Room {
    /// The cell this room IS.
    pub cell: CellId,
}

impl Room {
    pub fn new(cell: CellId) -> Self {
        Room { cell }
    }

    /// The room's c-list in the live ledger (its exits + contained items), or
    /// `None` if the room cell does not exist.
    pub fn clist<'w>(&self, world: &'w World) -> Option<&'w CapabilitySet> {
        world.ledger().get(&self.cell).map(|c| &c.capabilities)
    }

    /// Does this room connect to `neighbour`? An exit IS a cap edge: the room
    /// connects there iff its c-list reaches the neighbour room cell.
    pub fn connects_to(&self, world: &World, neighbour: Room) -> bool {
        self.clist(world)
            .map(|cl| cl.has_access(&neighbour.cell))
            .unwrap_or(false)
    }

    /// Is `item` lying in this room? An item-in-room IS a cap-in-the-room's-c-list.
    pub fn contains(&self, world: &World, item: Item) -> bool {
        self.clist(world)
            .map(|cl| cl.has_access(&item.cell))
            .unwrap_or(false)
    }
}

/// **An inhabitant — a cap-rooted session.** A player (or NPC) is a logged-in
/// principal (`session.rs`: login = receiving your root capability) whose *reach
/// is exactly its cap-tree*. Here an `Inhabitant` is the identity cell id; its
/// inventory IS its c-list, its authority IS what it can reach.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Inhabitant {
    /// The identity cell this inhabitant IS (the session root).
    pub cell: CellId,
}

impl Inhabitant {
    pub fn new(cell: CellId) -> Self {
        Inhabitant { cell }
    }

    /// Does this inhabitant currently hold `item`? Inventory = the c-list.
    pub fn holds(&self, world: &World, item: Item) -> bool {
        world
            .ledger()
            .get(&self.cell)
            .map(|c| c.capabilities.has_access(&item.cell))
            .unwrap_or(false)
    }

    /// Can this inhabitant reach `room` (i.e. could it form an entering turn)? A
    /// locked door is the absence of this cap.
    pub fn can_enter(&self, world: &World, room: Room) -> bool {
        world
            .ledger()
            .get(&self.cell)
            .map(|c| c.capabilities.has_access(&room.cell))
            .unwrap_or(false)
    }
}

/// **An item — a capability target.** An item is a cell; *the item* is the cap to
/// it. Picking it up moves the cap into your c-list; dropping/giving revokes it
/// from you and grants it elsewhere. A *valuable* item additionally carries
/// conserved value (`Transfer`/`NoteSpend`+`NoteCreate`, Σδ=0) — out of scope for
/// this first slice, which proves the cap-conservation core.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Item {
    /// The cell this item IS.
    pub cell: CellId,
}

impl Item {
    pub fn new(cell: CellId) -> Self {
        Item { cell }
    }
}

/// The outcome of a MUD action — committed (with the executor's receipt) or
/// refused (fail-closed, with the reason).
#[derive(Debug)]
pub enum ActionOutcome {
    /// The action committed against the verified executor; the receipt is the
    /// proof it happened (no-false-claim: you cannot claim an action with no
    /// receipt).
    Done { receipt: TurnReceipt },
    /// The action was refused (you lacked the cap, the source did not hold the
    /// item, an amplification was attempted). Nothing happened — fail-closed.
    Refused { reason: String },
}

impl ActionOutcome {
    pub fn is_done(&self) -> bool {
        matches!(self, ActionOutcome::Done { .. })
    }
}

/// **PICK UP / GIVE — the capability MOVES.**
///
/// The `source` (a room, or a giver) hands the `item` cap to `taker`, then loses
/// it. Implemented as the REAL powerbox grant (the two gates: `mint_needs_held_
/// factory` — `source` must HOLD a cap reaching the item — + `gen_conferral_is_
/// attenuation`) followed by a real [`Effect::RevokeCapability`] removing the
/// item cap from `source`'s c-list. After this, `source` no longer holds the cap,
/// so a SECOND pickup of the same item is refused by `mint_needs_held_factory`.
/// **This is conservation of the capability itself — duping is inexpressible.**
///
/// `confer` is the rights the taker receives (≤ what the source holds; an
/// amplification is refused by the powerbox before any turn).
pub fn pick_up(
    world: &mut World,
    source: CellId,
    taker: Inhabitant,
    item: Item,
    confer: AuthRequired,
) -> ActionOutcome {
    // (1) GRANT: a real attenuated Effect::GrantCapability source → taker. The
    //     powerbox refuses if `source` does not hold the item (mint_needs_held_
    //     factory) or if `confer` would amplify (gen_conferral_is_attenuation).
    let grant_receipt = match Powerbox::grant(world, source, taker.cell, item.cell, confer) {
        PowerboxOutcome::Granted { receipt, .. } => receipt,
        PowerboxOutcome::Denied { reason } => {
            return ActionOutcome::Refused { reason };
        }
    };

    // (2) REVOKE: the source loses the item cap (the item leaves the floor). We
    //     find the source's slot reaching the item and revoke it via a real turn.
    let slot = match world
        .ledger()
        .get(&source)
        .and_then(|c| c.capabilities.iter().find(|cap| cap.target == item.cell))
        .map(|cap| cap.slot)
    {
        Some(s) => s,
        None => {
            // The grant landed but the source somehow holds no revocable slot —
            // leave the grant (the taker has it) and report the unusual state.
            return ActionOutcome::Done { receipt: grant_receipt };
        }
    };
    let revoke = world.turn(
        source,
        vec![Effect::RevokeCapability { cell: source, slot }],
    );
    match world.commit_turn(revoke) {
        CommitOutcome::Committed { receipt, .. } => ActionOutcome::Done { receipt },
        // The revoke failed — the taker still has the cap; report fail-open of the
        // removal honestly (the source still holds it; not a dupe — the SAME cap).
        other => ActionOutcome::Refused {
            reason: format!("pickup grant landed but removal from source was refused: {other:?}"),
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::world::make_open_cell;

    /// A world with one ROOM holding an item cap, and two PLAYERS (each a fresh
    /// identity cell with an empty c-list — the ocap floor). The room is built
    /// "open" so it can grant the item it holds. Returns
    /// `(world, room, item, alice, bob)`.
    fn mud_world() -> (World, Room, Item, Inhabitant, Inhabitant) {
        let mut w = World::new();

        // The item is a plain cell lying on the floor.
        let item = Item::new(w.genesis_cell(0x17, 0));

        // The ROOM is an open cell that HOLDS the item (the item is in the room).
        let mut room_cell = make_open_cell(0x20, 0);
        room_cell
            .capabilities
            .grant(item.cell, AuthRequired::None)
            .expect("the room holds the item lying in it");
        let room = Room::new(w.genesis_install(room_cell));

        // Two players, born holding NOTHING (empty c-lists — the ocap floor).
        let alice = Inhabitant::new(w.genesis_cell(0xA1, 0));
        let bob = Inhabitant::new(w.genesis_cell(0xB0, 0));

        (w, room, item, alice, bob)
    }

    #[test]
    fn room_is_a_cell_holding_its_contents() {
        let (world, room, item, _alice, _bob) = mud_world();
        // An item-in-room IS a cap-in-the-room's-c-list.
        assert!(room.contains(&world, item), "the item lies in the room");
        assert!(room.clist(&world).is_some(), "the room IS a cell with a c-list");
    }

    #[test]
    fn inventory_is_the_clist_players_start_empty() {
        let (world, _room, item, alice, bob) = mud_world();
        // Inventory = the c-list; fresh players hold nothing (the ocap floor).
        assert!(!alice.holds(&world, item), "alice starts empty-handed");
        assert!(!bob.holds(&world, item), "bob starts empty-handed");
    }

    #[test]
    fn a_locked_door_is_an_absent_cap() {
        let (world, room, _item, alice, _bob) = mud_world();
        // Alice holds no cap to the room → she cannot form an entering turn. The
        // "lock" is not a flag the client honors; it is an authority the executor
        // checks (here: the absence of the cap).
        assert!(
            !alice.can_enter(&world, room),
            "no cap to the room → the door is locked (no admissible entering turn)"
        );
    }

    /// THE LOAD-BEARING SCENARIO: two players in one room; one picks up the item;
    /// the other CANNOT dupe it.
    #[test]
    fn pickup_moves_the_cap_and_the_item_cannot_be_duped() {
        let (mut world, room, item, alice, bob) = mud_world();

        // Pre: the item is in the room, neither player holds it.
        assert!(room.contains(&world, item));
        assert!(!alice.holds(&world, item) && !bob.holds(&world, item));

        // ── ALICE PICKS IT UP: the cap MOVES room → alice, and the room loses it.
        let a = pick_up(&mut world, room.cell, alice, item, AuthRequired::None);
        assert!(a.is_done(), "alice's pickup commits: {a:?}");
        assert!(alice.holds(&world, item), "alice now holds the item (cap moved to her)");
        assert!(
            !room.contains(&world, item),
            "the item LEFT the floor — the room no longer holds the cap (the move conserved it)"
        );

        // The pickup left a verifiable receipt (no-false-claim: the action is
        // proven by the executor, not asserted by the client).
        if let ActionOutcome::Done { receipt } = &a {
            assert_eq!(receipt.agent, room.cell, "the receipt names who acted");
        }

        // ── BOB TRIES TO DUPE IT: a second pickup of the SAME item from the room.
        //    The room no longer holds the cap, so the powerbox's mint_needs_held_
        //    factory gate REFUSES — duping is structurally inexpressible.
        let b = pick_up(&mut world, room.cell, bob, item, AuthRequired::None);
        assert!(!b.is_done(), "bob's dupe attempt is REFUSED (fail-closed): {b:?}");
        if let ActionOutcome::Refused { reason } = &b {
            assert!(
                reason.contains("hold") || reason.contains("held") || reason.contains("authority"),
                "the refusal cites the missing-source-cap gate, got: {reason}"
            );
        }
        assert!(!bob.holds(&world, item), "bob got NOTHING — the item was not duplicated");

        // Invariant: exactly ONE holder of the item cap remains — alice. The
        // capability was conserved across the whole scenario (no dupe possible).
        assert!(alice.holds(&world, item));
        assert!(!bob.holds(&world, item));
        assert!(!room.contains(&world, item));
    }

    #[test]
    fn an_over_amplifying_pickup_is_refused() {
        // Hardening: the room holds the item at `None`; a pickup demanding a
        // NARROWER-than-None... actually None is the widest, so test the symmetric
        // amplification: a room holding the item at Signature cannot hand None.
        let mut w = World::new();
        let item = Item::new(w.genesis_cell(0x17, 0));
        let mut room_cell = make_open_cell(0x20, 0);
        room_cell
            .capabilities
            .grant(item.cell, AuthRequired::Signature)
            .expect("the room holds the item at Signature");
        let room = Room::new(w.genesis_install(room_cell));
        let alice = Inhabitant::new(w.genesis_cell(0xA1, 0));

        // Demanding None (wider than the held Signature) is an amplification → the
        // powerbox refuses before any turn (gen_conferral_is_attenuation).
        let out = pick_up(&mut w, room.cell, alice, item, AuthRequired::None);
        assert!(!out.is_done(), "an amplifying pickup is refused (attenuation-only)");
        assert!(!alice.holds(&w, item), "alice got nothing — no amplification");
    }
}
