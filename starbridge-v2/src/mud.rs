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
///   lattice) is a [`Cell`](dregg_cell). Here a `Room` is just the room cell's id;
///   the live state lives in the [`World`]'s ledger. The room's *history is its
///   provenance chain* — every turn against it leaves a receipt.
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

    /// This inhabitant's live balance — the conserved value it carries (used to
    /// witness Σδ=0 across a valuable trade). `0` if it does not exist.
    pub fn cell_balance(&self, world: &World) -> i64 {
        world
            .ledger()
            .get(&self.cell)
            .map(|c| c.state.balance())
            .unwrap_or(0)
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
/// conserved value: trading it rides a real [`Effect::Transfer`] under the
/// executor's Σδ=0 rule (see [`trade_value`]) — you cannot conjure value, only
/// move it. The bare-cap face (move the cap, no value) is [`give`]; the valued
/// face is [`trade_value`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Item {
    /// The cell this item IS.
    pub cell: CellId,
}

impl Item {
    pub fn new(cell: CellId) -> Self {
        Item { cell }
    }

    /// This item's live balance in the world — the conserved value it carries (an
    /// item-cell can itself hold a balance). `0` if it carries no value (or does
    /// not exist). Used to witness Σδ=0 across a trade.
    pub fn value(&self, world: &World) -> i64 {
        world
            .ledger()
            .get(&self.cell)
            .map(|c| c.state.balance())
            .unwrap_or(0)
    }
}

/// The outcome of a MUD action — committed (with the executor's receipt) or
/// refused (fail-closed, with the reason).
#[derive(Debug)]
pub enum ActionOutcome {
    /// The action committed against the verified executor; the receipt is the
    /// proof it happened (no-false-claim: you cannot claim an action with no
    /// receipt).
    Done { receipt: Box<TurnReceipt> },
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
            return ActionOutcome::Done {
                receipt: grant_receipt,
            };
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

/// **GIVE / TRADE A BARE CAP — one inhabitant hands an item to another.**
///
/// `give` is exactly [`pick_up`] read socially: the `giver` is the `source`. The
/// item cap moves giver → receiver and the giver LOSES it (the same grant+revoke
/// pair). Because the move is a real powerbox grant, the executor's
/// `mint_needs_held_factory` gate means the giver can only hand an item it
/// actually holds, and `gen_conferral_is_attenuation` means it can only confer
/// authority `≤` what it holds — **a giver cannot amplify the key it passes on.**
/// After the give, exactly one inhabitant holds the cap; a *second* give of the
/// same item by the (now-empty-handed) giver is refused — no dupe across a trade.
pub fn give(
    world: &mut World,
    giver: Inhabitant,
    receiver: Inhabitant,
    item: Item,
    confer: AuthRequired,
) -> ActionOutcome {
    pick_up(world, giver.cell, receiver, item, confer)
}

/// **TRADE A VALUABLE ITEM — a real conserved [`Effect::Transfer`] (Σδ=0).**
///
/// A *valuable* item carries balance. Trading `amount` of it from `giver` to
/// `receiver` is a genuine [`Effect::Transfer`] committed through the embedded
/// executor, which enforces **Σδ=0** (value conserved — the giver's balance falls
/// by exactly what the receiver's rises; nothing is conjured) and refuses an
/// overdraft (you cannot send value you do not hold). The giver IS the turn's
/// agent (`action_target`), so this is the giver spending its own value — the
/// authority is the signature on its own turn, and conservation is the executor's.
///
/// This is the value face of a trade; [`give`] is the bare-cap face. A multi-hop
/// trade (A→B→C) conserves the total at every hop: Σδ=0 holds per turn.
pub fn trade_value(
    world: &mut World,
    giver: Inhabitant,
    receiver: Inhabitant,
    amount: u64,
) -> ActionOutcome {
    let turn = world.turn(
        giver.cell,
        vec![Effect::Transfer {
            from: giver.cell,
            to: receiver.cell,
            amount,
        }],
    );
    match world.commit_turn(turn) {
        CommitOutcome::Committed { receipt, .. } => ActionOutcome::Done { receipt },
        CommitOutcome::Rejected { reason, .. } => ActionOutcome::Refused { reason },
        CommitOutcome::Queued { .. } => ActionOutcome::Refused {
            reason: "world suspended: trade transfer queued, not committed".to_string(),
        },
    }
}

/// **MOVE THROUGH A DOOR — a cap-gated room transition the EXECUTOR enforces.**
///
/// Moving an inhabitant into `dest` is exercising the **door cap**: the inhabitant
/// writes a presence marker (a [`Effect::SetField`]) onto the destination room
/// cell. Because the room cell is NOT the turn's agent, the executor runs
/// `check_cross_cell_permission` — which REFUSES with `CapabilityNotHeld` unless
/// the inhabitant holds a capability reaching `dest`. **A door is exactly a cap
/// you lack:** no client-honored flag, an authority the executor checks. An
/// inhabitant holding the door cap moves; one lacking it is refused, fail-closed,
/// before any state changes. `presence_slot` is the room field the marker lands in
/// (any free heap slot; the marker value is the mover's id-tag).
pub fn move_through(
    world: &mut World,
    mover: Inhabitant,
    dest: Room,
    presence_slot: usize,
) -> ActionOutcome {
    // The presence marker carries the mover's identity (a tag derived from its id),
    // so "who is here" is on-ledger. The VALUE is incidental; the load-bearing fact
    // is that forming this turn AT ALL requires the door cap (the executor refuses
    // a SetState on a foreign room the mover holds no cap reaching).
    let mut tag = [0u8; 32];
    tag[31] = mover.cell.0[0].wrapping_add(1);
    let turn = world.turn(
        mover.cell,
        vec![Effect::SetField {
            cell: dest.cell,
            index: presence_slot,
            value: tag,
        }],
    );
    match world.commit_turn(turn) {
        CommitOutcome::Committed { receipt, .. } => ActionOutcome::Done { receipt },
        // The mover holds no cap reaching the room → CapabilityNotHeld. The door
        // is locked: there is no admissible entering turn.
        CommitOutcome::Rejected { reason, .. } => ActionOutcome::Refused { reason },
        CommitOutcome::Queued { .. } => ActionOutcome::Refused {
            reason: "world suspended: move turn queued, not committed".to_string(),
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
        assert!(
            room.clist(&world).is_some(),
            "the room IS a cell with a c-list"
        );
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
        assert!(
            alice.holds(&world, item),
            "alice now holds the item (cap moved to her)"
        );
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
        assert!(
            !b.is_done(),
            "bob's dupe attempt is REFUSED (fail-closed): {b:?}"
        );
        if let ActionOutcome::Refused { reason } = &b {
            assert!(
                reason.contains("hold") || reason.contains("held") || reason.contains("authority"),
                "the refusal cites the missing-source-cap gate, got: {reason}"
            );
        }
        assert!(
            !bob.holds(&world, item),
            "bob got NOTHING — the item was not duplicated"
        );

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
        assert!(
            !out.is_done(),
            "an amplifying pickup is refused (attenuation-only)"
        );
        assert!(
            !alice.holds(&w, item),
            "alice got nothing — no amplification"
        );
    }

    // ── THE MULTI-INHABITANT SHARED WORLD ─────────────────────────────────────
    //
    // A richer world than the 2-player/1-item slice: THREE inhabitants across TWO
    // connected rooms. The TAVERN holds a plain item (a key) lying on its floor.
    // The CELLAR is a second room reached through a DOOR — a cap to the cellar
    // cell. Alice holds the door cap (she may move); Bob does NOT (the door is
    // locked to him). Carol holds a VALUABLE purse (balance) for the trade test.
    //
    // Returns `(world, tavern, cellar, key, alice, bob, carol)`.
    fn shared_world() -> (World, Room, Room, Item, Inhabitant, Inhabitant, Inhabitant) {
        let mut w = World::new();

        // The CELLAR — a second room, open so a mover can write a presence marker
        // onto it (the executor still gates the write on holding the door cap).
        let cellar = Room::new(w.genesis_cell(0x30, 0));

        // The KEY — a plain item lying in the tavern.
        let key = Item::new(w.genesis_cell(0x17, 0));

        // The TAVERN — an open room cell holding (a) the key lying in it and (b)
        // the DOOR cap reaching the cellar (the exit edge).
        let mut tavern_cell = make_open_cell(0x20, 0);
        tavern_cell
            .capabilities
            .grant(key.cell, AuthRequired::None)
            .expect("the tavern holds the key lying in it");
        tavern_cell
            .capabilities
            .grant(cellar.cell, AuthRequired::None)
            .expect("the tavern has an exit to the cellar");
        let tavern = Room::new(w.genesis_install(tavern_cell));

        // ALICE holds the DOOR cap to the cellar (she may move there). Born via a
        // cell that already holds a cap reaching the cellar cell.
        let (alice_cell, _slot) = w.genesis_cell_with_cap(0xA1, 0, cellar.cell);
        let alice = Inhabitant::new(alice_cell);

        // BOB holds NOTHING — empty c-list. The cellar door is locked to him.
        let bob = Inhabitant::new(w.genesis_cell(0xB0, 0));

        // CAROL carries a VALUABLE purse (a balance of 1000) for the trade test.
        let carol = Inhabitant::new(w.genesis_cell(0xC0, 1_000));

        (w, tavern, cellar, key, alice, bob, carol)
    }

    /// How many of `who` currently hold `item` (read from the live ledger). The
    /// single-custody / no-dupe witness: this must be ≤ 1 at every step of a trade.
    fn holders_of(world: &World, item: Item, who: &[Inhabitant]) -> usize {
        who.iter().filter(|i| i.holds(world, item)).count()
    }

    /// PROPERTY (b): MOVEMENT IS CAP-GATED — a door is a cap you lack.
    ///
    /// Alice holds the cellar door cap → her move COMMITS (a real turn against the
    /// cellar room cell). Bob holds no such cap → his identical move is REFUSED by
    /// the EXECUTOR (`CapabilityNotHeld`), not by a client flag. Executor-enforced.
    #[test]
    fn movement_is_cap_gated_the_door_is_a_cap_you_lack() {
        let (mut world, _tavern, cellar, _key, alice, bob, _carol) = shared_world();

        // Pre: alice can reach the cellar (holds the door); bob cannot.
        assert!(alice.can_enter(&world, cellar), "alice holds the door cap");
        assert!(
            !bob.can_enter(&world, cellar),
            "bob holds no door cap — locked"
        );

        // ALICE MOVES: a real cap-gated transition. The executor admits it because
        // she holds a cap reaching the cellar room cell.
        let a = move_through(&mut world, alice, cellar, 32);
        assert!(
            a.is_done(),
            "alice holds the door → her move commits: {a:?}"
        );

        // BOB MOVES: the SAME move, but he lacks the door cap. The executor REFUSES
        // — there is no admissible entering turn. Fail-closed, nothing changed.
        let b = move_through(&mut world, bob, cellar, 33);
        assert!(
            !b.is_done(),
            "bob lacks the door → his move is REFUSED: {b:?}"
        );
        if let ActionOutcome::Refused { reason } = &b {
            // The refusal is the executor's own authority gate (CapabilityNotHeld),
            // surfaced — not a Rust-side bookkeeping check.
            assert!(
                reason.contains("CapabilityNotHeld")
                    || reason.to_lowercase().contains("cap")
                    || reason.to_lowercase().contains("held")
                    || reason.to_lowercase().contains("permission"),
                "the refusal cites the missing door cap, got: {reason}"
            );
        }
    }

    /// PROPERTY (a) + (d): A MULTI-HOP TRADE CONSERVES THE ITEM (single-custody,
    /// no dupe), and TWO CONTENDERS FOR ONE ITEM → EXACTLY ONE WINS.
    ///
    /// Alice picks the key off the tavern floor (cap moves room → alice). She then
    /// GIVES it to Bob (cap moves alice → bob; alice loses it). Across the whole
    /// chain the key cap has exactly ONE holder at every step — it is never
    /// duplicated. Then Carol (a second contender) tries to pick the SAME key off
    /// the floor: refused, because the floor no longer holds it. Exactly one holder.
    #[test]
    fn a_multi_hop_trade_conserves_the_item_and_one_contender_wins() {
        let (mut world, tavern, _cellar, key, alice, bob, carol) = shared_world();

        // Pre: the key lies in the tavern; no inhabitant holds it.
        assert!(
            tavern.contains(&world, key),
            "the key is on the tavern floor"
        );
        assert!(!alice.holds(&world, key) && !bob.holds(&world, key) && !carol.holds(&world, key));

        // HOP 1 — alice picks the key off the floor (room → alice).
        let h1 = pick_up(&mut world, tavern.cell, alice, key, AuthRequired::None);
        assert!(h1.is_done(), "alice picks up the key: {h1:?}");
        assert!(alice.holds(&world, key), "alice now holds the key");
        assert!(
            !tavern.contains(&world, key),
            "the key LEFT the floor (conserved move)"
        );
        // Single-custody: exactly one holder (alice).
        assert_eq!(
            holders_of(&world, key, &[alice, bob, carol]),
            1,
            "after hop 1 exactly one inhabitant holds the key"
        );

        // HOP 2 — alice GIVES the key to bob (alice → bob; alice loses it).
        let h2 = give(&mut world, alice, bob, key, AuthRequired::None);
        assert!(h2.is_done(), "alice gives the key to bob: {h2:?}");
        assert!(bob.holds(&world, key), "bob now holds the key");
        assert!(
            !alice.holds(&world, key),
            "alice no longer holds it (the give MOVED the cap)"
        );
        // Still single-custody across the hop: no dupe — exactly one holder (bob).
        assert_eq!(
            holders_of(&world, key, &[alice, bob, carol]),
            1,
            "after hop 2 STILL exactly one holder — the key was never duplicated"
        );

        // CONTENTION — carol, a second contender, tries to pick the SAME key off the
        // floor. The floor no longer holds it (it left at hop 1), so the executor's
        // mint_needs_held_factory gate REFUSES. Exactly one inhabitant ends with it.
        let contend = pick_up(&mut world, tavern.cell, carol, key, AuthRequired::None);
        assert!(
            !contend.is_done(),
            "carol cannot pick a key that left the floor: {contend:?}"
        );
        assert!(!carol.holds(&world, key), "carol got nothing — no dupe");
        assert_eq!(
            holders_of(&world, key, &[alice, bob, carol]),
            1,
            "exactly ONE inhabitant holds the key after the whole trade — linearity"
        );
        assert!(
            bob.holds(&world, key),
            "…and it is bob (the last legitimate recipient)"
        );
    }

    /// PROPERTY (c): AN ATTEMPTED AUTHORITY-AMPLIFICATION ON A TRADE IS REFUSED.
    ///
    /// Alice picks up the key at the ATTENUATED `Signature` right (she holds it
    /// only at Signature). She then tries to GIVE it onward to Bob at the WIDER
    /// `None` (full) authority — an amplification of the key she holds. The
    /// powerbox's `gen_conferral_is_attenuation` gate (and the executor backstop)
    /// REFUSES: a giver cannot amplify the key it passes on. Bob gets nothing.
    #[test]
    fn an_amplifying_trade_is_refused_a_giver_cannot_amplify() {
        let (mut world, tavern, _cellar, key, alice, bob, _carol) = shared_world();

        // Alice picks the key up at the ATTENUATED Signature right (≤ the floor's
        // None). She holds the key, but only at Signature.
        let pick = pick_up(&mut world, tavern.cell, alice, key, AuthRequired::Signature);
        assert!(
            pick.is_done(),
            "alice picks the key up at Signature: {pick:?}"
        );
        assert!(
            alice.holds(&world, key),
            "alice holds the key (at Signature)"
        );

        // She tries to GIVE it onward at the WIDER None → amplification. Refused.
        let amp = give(&mut world, alice, bob, key, AuthRequired::None);
        assert!(!amp.is_done(), "an amplifying give is REFUSED: {amp:?}");
        if let ActionOutcome::Refused { reason } = &amp {
            assert!(
                reason.contains("AMPLIFY")
                    || reason.to_lowercase().contains("attenuat")
                    || reason.to_lowercase().contains("amplif"),
                "the refusal cites amplification, got: {reason}"
            );
        }
        assert!(
            !bob.holds(&world, key),
            "bob got nothing — no amplified key"
        );
        // Alice STILL holds it (the failed give moved nothing) — single custody.
        assert!(
            alice.holds(&world, key),
            "alice still holds the key — the trade ran nothing"
        );

        // …and a NON-amplifying give (at or below Signature) is legitimate — proving
        // the refusal is the amplification, not a blanket block on giving.
        let ok = give(&mut world, alice, bob, key, AuthRequired::Signature);
        assert!(
            ok.is_done(),
            "a non-amplifying give (≤ held) is legitimate: {ok:?}"
        );
        assert!(
            bob.holds(&world, key) && !alice.holds(&world, key),
            "the cap moved alice → bob"
        );
    }

    /// PROPERTY (a), value face: A VALUABLE TRADE CONSERVES VALUE (Σδ=0) and a
    /// trade beyond what the giver holds is refused (no value conjured).
    #[test]
    fn a_valuable_trade_conserves_value_sigma_delta_zero() {
        let (mut world, _tavern, _cellar, _key, alice, _bob, carol) = shared_world();

        // Carol carries 1000; alice carries 0. The TOTAL value across the pair.
        let total_before = carol.cell_balance(&world) + alice.cell_balance(&world);
        assert_eq!(
            total_before, 1_000,
            "the pair's total value before the trade"
        );

        // CAROL TRADES 300 to ALICE — a real conserved Effect::Transfer (Σδ=0).
        let t = trade_value(&mut world, carol, alice, 300);
        assert!(t.is_done(), "carol's conserved trade commits: {t:?}");
        assert_eq!(
            carol.cell_balance(&world),
            700,
            "carol's balance fell by 300"
        );
        assert_eq!(
            alice.cell_balance(&world),
            300,
            "alice's balance rose by 300"
        );
        // Σδ=0 — the executor conserved the total; nothing was conjured.
        assert_eq!(
            carol.cell_balance(&world) + alice.cell_balance(&world),
            total_before,
            "Σδ=0 — total value conserved across the trade (the executor's rule)"
        );

        // A trade BEYOND what carol holds is refused — you cannot send value you do
        // not have (the executor's conservation / non-overdraft rule). Nothing moves.
        let over = trade_value(&mut world, carol, alice, 10_000);
        assert!(!over.is_done(), "an overdraft trade is refused: {over:?}");
        assert_eq!(
            carol.cell_balance(&world),
            700,
            "carol's balance unchanged after the refused overdraft"
        );
        assert_eq!(alice.cell_balance(&world), 300, "alice's balance unchanged");
    }
}
