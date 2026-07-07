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

use std::collections::BTreeMap;

use dregg_captp::data_plane::{Bus, ChannelName, DataPlaneError, Delivery, SendCap, TopicName};
use dregg_captp::FederationId;
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
    move_cap(world, source, taker.cell, item.cell, confer)
}

/// **THE CONSERVED CAP-MOVE** — the one primitive under [`pick_up`], [`give`],
/// and the presence-token move ([`enter`]/[`leave`]): a cap to `target` MOVES
/// `source` → `dest` (grant + revoke), and cannot be duped or amplified. Both
/// gates are the powerbox's/executor's own, never Rust bookkeeping.
pub fn move_cap(
    world: &mut World,
    source: CellId,
    dest: CellId,
    target: CellId,
    confer: AuthRequired,
) -> ActionOutcome {
    // (1) GRANT: a real attenuated Effect::GrantCapability source → dest. The
    //     powerbox refuses if `source` does not hold the target (mint_needs_held_
    //     factory) or if `confer` would amplify (gen_conferral_is_attenuation).
    let grant_receipt = match Powerbox::grant(world, source, dest, target, confer) {
        PowerboxOutcome::Granted { receipt, .. } => receipt,
        PowerboxOutcome::Denied { reason } => {
            return ActionOutcome::Refused { reason };
        }
    };

    // (2) REVOKE: the source loses the cap (the object leaves its hands). We
    //     find the source's slot reaching the target and revoke it via a real turn.
    let slot = match world
        .ledger()
        .get(&source)
        .and_then(|c| c.capabilities.iter().find(|cap| cap.target == target))
        .map(|cap| cap.slot)
    {
        Some(s) => s,
        None => {
            // The grant landed but the source somehow holds no revocable slot —
            // leave the grant (the dest has it) and report the unusual state.
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
        // The revoke failed — the dest still has the cap; report fail-open of the
        // removal honestly (the source still holds it; not a dupe — the SAME cap).
        other => ActionOutcome::Refused {
            reason: format!("cap-move grant landed but removal from source was refused: {other:?}"),
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

// =============================================================================
// PHASE 2 — PRESENCE (a conserved cap artifact) + SAY (over the captp data plane)
// =============================================================================
//
// This is the seam DEOS-RUNS.md names: *"presence is the door-cap-gated write
// (entry cap-gating proven; a fuller presence-token move/grant is future)"* —
// here the fuller move lands. Presence is NOT a Rust set:
//
//   * **presence = a conserved token** — a [`PresenceToken`] is a cell; *being in
//     a room* is *the room's c-list holding the cap to your token*. Entering
//     MOVES the token into the room ([`move_cap`] — the same grant+revoke pair as
//     [`pick_up`], gated by `mint_needs_held_factory`), leaving moves it back out.
//     Single custody of the cap ⇒ an inhabitant is never present in two rooms —
//     conservation, not bookkeeping.
//   * **"who is here" = a read of the room cell** — [`Room::hosts`] /
//     [`Room::who_is_here`] read the live ledger's c-list, nothing else.
//   * **entry is still the door tooth** — [`enter`] runs [`move_through`] FIRST:
//     the executor refuses (`CapabilityNotHeld`) unless the mover holds the door
//     cap, before the token moves. The phase-1 gate keeps passing.
//   * **say = a cap-gated enqueue on the Bus** — a room's chat rides the REAL
//     [`dregg_captp::data_plane::Bus`]: the speaker presents a [`SendCap`] into
//     the room's channel and [`Bus::enqueue`] admits or refuses at
//     [`SendCap::admits`] — a speaker who is not present presents a revoked (or
//     never-granted floor) cap and is refused BY THE CAP GATE
//     ([`DataPlaneError::Unauthorized`]), never by an if-statement here. Hearers
//     are the present inhabitants' inboxes (topic fan-out), drained in FIFO
//     order, each delivery a signed, verifying custody receipt.
//
// The room's own inbox doubles as its chat log — the same "room = a cell whose
// history is its messages" shape as `deos_matrix::cell::RoomCell`, without any
// deos-matrix dependency (the Bus inbox IS the history here).
//
// NAMED SEAM (cap-lifecycle weld): the speak-cap mint/revoke ([`RoomVoice::admit`]
// / [`RoomVoice::expel`]) is host-side issuance KEYED to the receipted,
// executor-gated enter/leave — the refusal itself is the Bus's cap gate, but the
// issuance is not yet itself a turn. The fuller weld (derive the speak cap as an
// attenuation of the on-ledger presence token, so issuance is also a receipted
// grant) is the next rung, and is what a 3-box net needs anyway (see the module
// report / HORIZONLOG).

/// **A presence token — presence as a conserved object.** One per inhabitant; a
/// cell whose cap MOVES with them. The room holding the cap IS "they are here".
/// When in no room, the inhabitant carries their own token (the cap sits in
/// their own c-list).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct PresenceToken {
    /// The cell this token IS.
    pub cell: CellId,
}

impl PresenceToken {
    pub fn new(cell: CellId) -> Self {
        PresenceToken { cell }
    }

    /// Does `holder` currently carry this token in its own c-list (i.e. the
    /// inhabitant is in no room — presence is *at hand*, not placed)?
    pub fn carried_by(&self, world: &World, holder: CellId) -> bool {
        world
            .ledger()
            .get(&holder)
            .map(|c| c.capabilities.has_access(&self.cell))
            .unwrap_or(false)
    }
}

impl Room {
    /// **"Is this inhabitant here?"** — a read of the room cell's live c-list:
    /// the room hosts a presence token iff it holds the cap to it. No Rust set.
    pub fn hosts(&self, world: &World, token: PresenceToken) -> bool {
        self.clist(world)
            .map(|cl| cl.has_access(&token.cell))
            .unwrap_or(false)
    }

    /// **"Who is here?"** — the roster filtered by the room cell's own state.
    /// `roster` is the world's directory of (inhabitant, their token); the answer
    /// is read entirely off the ledger.
    pub fn who_is_here(
        &self,
        world: &World,
        roster: &[(Inhabitant, PresenceToken)],
    ) -> Vec<Inhabitant> {
        roster
            .iter()
            .filter(|(_, t)| self.hosts(world, *t))
            .map(|(i, _)| *i)
            .collect()
    }
}

/// The hearer identity an inhabitant drains its room-chat from — its inbox
/// address on the [`Bus`] (the cell id bytes, verbatim).
pub fn hearer_id(who: Inhabitant) -> FederationId {
    FederationId(who.cell.0)
}

/// The outcome of a [`RoomVoice::say`] — heard (with the real deliveries) or
/// refused by the data plane's own cap gate.
#[derive(Debug)]
pub enum SayOutcome {
    /// The utterance was admitted: archived into the room's own inbox (the chat
    /// log) and fanned out to every present hearer, each with a signed receipt.
    Heard {
        /// The delivery into the room's own inbox (the room's history entry).
        archived: Delivery,
        /// One delivery per present hearer (the fan-out), in subscription order.
        heard: Vec<(FederationId, Delivery)>,
    },
    /// The say was refused — by [`SendCap::admits`] inside the Bus
    /// ([`DataPlaneError::Unauthorized`]) for an absent speaker; nothing was
    /// queued, no cursor ticked, no receipt minted (no phantom speech).
    Refused {
        /// The data plane's own error (the gate's verdict, verbatim).
        error: DataPlaneError,
    },
}

impl SayOutcome {
    pub fn is_heard(&self) -> bool {
        matches!(self, SayOutcome::Heard { .. })
    }
}

/// **A room's voice — its channel on the data-plane [`Bus`].**
///
/// One per room. The room has an inbox identity (its chat log), a channel name +
/// topic (both derived from the room cell id), a relay cap (the room fanning an
/// admitted utterance out to its occupants), and per-inhabitant SPEAK caps whose
/// lifecycle is welded to presence: minted fresh on a committed [`enter`],
/// revoked on a committed [`leave`]/[`move_rooms`]. An absent speaker therefore
/// presents a revoked cap (or the pre-revoked floor cap, if they never entered)
/// and [`Bus::enqueue`] refuses at [`SendCap::admits`] — presence gates speech
/// through the cap algebra, not through a presence check in this file.
pub struct RoomVoice {
    room: Room,
    /// The room's own inbox identity on the Bus — its chat log.
    fed: FederationId,
    /// The room-scoped channel name (`mud/say/<room cell id>`).
    name: ChannelName,
    /// The room-scoped topic the present hearers subscribe to (same bytes).
    topic: TopicName,
    /// The room's own broadcast cap: fans an ADMITTED utterance to its occupants.
    relay: SendCap,
    /// The floor cap a never-admitted speaker presents: minted REVOKED, so the
    /// gate (not this module) refuses them uniformly with a departed speaker.
    floor: SendCap,
    /// Per-inhabitant speak caps — minted on enter, revoked (in place) on leave.
    speak: BTreeMap<CellId, SendCap>,
}

impl RoomVoice {
    /// Open a room's voice on the Bus: register its topic, mint its relay cap and
    /// the pre-revoked floor cap.
    pub fn new(room: Room, bus: &mut Bus) -> Self {
        let fed = FederationId(room.cell.0);
        let mut bytes = b"mud/say/".to_vec();
        bytes.extend_from_slice(&room.cell.0);
        let name = ChannelName::new(bytes.clone());
        let topic = TopicName::new(bytes);
        bus.register_topic(topic.clone());
        let relay = SendCap::grant(fed, name.clone(), AuthRequired::Signature);
        let mut floor = SendCap::grant(fed, name.clone(), AuthRequired::Signature);
        floor.revoke();
        RoomVoice {
            room,
            fed,
            name,
            topic,
            relay,
            floor,
            speak: BTreeMap::new(),
        }
    }

    /// The room this voice speaks for.
    pub fn room(&self) -> Room {
        self.room
    }

    /// The room's own inbox identity (drain it to read the chat log).
    pub fn inbox(&self) -> FederationId {
        self.fed
    }

    /// The room-scoped channel name (for wake-by-name).
    pub fn channel(&self) -> &ChannelName {
        &self.name
    }

    /// Weld a committed ENTER to the channel: mint a fresh speak cap for `who`
    /// and subscribe their inbox to the room topic. Private on purpose — only
    /// the receipted, executor-gated [`enter`]/[`move_rooms`] reach it.
    fn admit(&mut self, bus: &mut Bus, who: Inhabitant) {
        self.speak.insert(
            who.cell,
            SendCap::grant(self.fed, self.name.clone(), AuthRequired::Signature),
        );
        bus.subscribe(self.topic.clone(), hearer_id(who));
        bus.wait(&self.name, hearer_id(who));
    }

    /// Weld a committed LEAVE to the channel: REVOKE `who`'s speak cap in place
    /// (the channel-level revocation switch — their next say is refused by
    /// [`SendCap::admits`]) and unsubscribe their inbox (they no longer hear).
    fn expel(&mut self, bus: &mut Bus, who: Inhabitant) {
        if let Some(cap) = self.speak.get_mut(&who.cell) {
            cap.revoke();
        }
        bus.unsubscribe(&self.topic, &hearer_id(who));
    }

    /// **SAY — a cap-gated enqueue over the data plane.**
    ///
    /// The speaker presents their speak cap (or, having never been admitted, the
    /// pre-revoked floor cap) and the utterance is:
    ///
    ///   1. **gated**: [`Bus::enqueue`] into the room's own inbox admits or
    ///      refuses at [`SendCap::admits`]. An absent speaker's cap is revoked ⇒
    ///      [`DataPlaneError::Unauthorized`] — the refusal is the data plane's,
    ///      and it leaves NO phantom work (nothing queued, no cursor tick, no
    ///      receipt).
    ///   2. **archived**: the admitted box lands in the room's inbox — the room's
    ///      chat history (the `RoomCell`-shaped log, as a Bus inbox).
    ///   3. **heard**: the room relays the admitted utterance to its topic —
    ///      one real enqueue + signed receipt per PRESENT hearer, delivered in
    ///      FIFO order (drain to hear).
    pub fn say(&self, bus: &mut Bus, speaker: Inhabitant, text: &[u8], now: u64) -> SayOutcome {
        let cap = self.speak.get(&speaker.cell).unwrap_or(&self.floor);

        // THE GATE — the Bus's own `SendCap::admits` seam decides. Present ⇒ the
        // fresh cap admits; departed ⇒ revoked cap refuses; never-entered ⇒ the
        // pre-revoked floor refuses. Same gate, all three polarities.
        let archived = match bus.enqueue(
            cap,
            self.fed,
            &self.name,
            AuthRequired::Signature,
            text.to_vec(),
            now,
        ) {
            Ok(d) => d,
            Err(error) => return SayOutcome::Refused { error },
        };

        // FAN-OUT — the room relays the ADMITTED utterance to its occupants (the
        // topic's subscribers are exactly the present inhabitants).
        match bus.publish(
            &self.topic,
            &self.relay,
            AuthRequired::Signature,
            text.to_vec(),
            now,
        ) {
            Ok(heard) => SayOutcome::Heard { archived, heard },
            Err(error) => SayOutcome::Refused { error },
        }
    }
}

/// **ENTER A ROOM — the door tooth, then the conserved presence move.**
///
/// Two real gates in sequence, both the machinery's own:
///
///   1. **the door** — [`move_through`]: the executor REFUSES
///      (`CapabilityNotHeld`) unless `mover` holds a cap reaching the room. A
///      locked door still locks; the token does not move; no speak cap is minted.
///   2. **the presence move** — [`move_cap`]: the mover's presence token MOVES
///      `from` (their own hands, or wherever it truly sits) into the room cell's
///      c-list. `mint_needs_held_factory` refuses a `from` that does not actually
///      hold the token — a lie about where you are cannot move your presence.
///
/// On commit, the room's voice ADMITS the mover: a fresh speak cap + a topic
/// subscription (they can now say and hear).
pub fn enter(
    world: &mut World,
    bus: &mut Bus,
    voice: &mut RoomVoice,
    mover: Inhabitant,
    token: PresenceToken,
    from: CellId,
    presence_slot: usize,
) -> ActionOutcome {
    // (1) THE DOOR — the phase-1 executor gate, unchanged and still load-bearing.
    let door = move_through(world, mover, voice.room(), presence_slot);
    if !door.is_done() {
        return door;
    }
    // (2) THE PRESENCE MOVE — the token's cap moves `from` → room (conserved).
    let moved = move_cap(
        world,
        from,
        voice.room().cell,
        token.cell,
        AuthRequired::None,
    );
    if !moved.is_done() {
        return moved;
    }
    // (3) THE VOICE WELD — presence now on-ledger; mint the speak cap.
    voice.admit(bus, mover);
    moved
}

/// **LEAVE A ROOM — the presence token moves back to the leaver's own hands.**
///
/// The same conserved [`move_cap`]: room → leaver. Leaving a room you are NOT in
/// is refused by `mint_needs_held_factory` (the room does not hold your token) —
/// the gate, not a check here. On commit the voice EXPELS the leaver: speak cap
/// REVOKED (their next say refused by the cap gate) and unsubscribed (silence,
/// both directions).
pub fn leave(
    world: &mut World,
    bus: &mut Bus,
    voice: &mut RoomVoice,
    leaver: Inhabitant,
    token: PresenceToken,
) -> ActionOutcome {
    let moved = move_cap(
        world,
        voice.room().cell,
        leaver.cell,
        token.cell,
        AuthRequired::None,
    );
    if !moved.is_done() {
        return moved;
    }
    voice.expel(bus, leaver);
    moved
}

/// **MOVE ROOM → ROOM — one conserved hop.** The door tooth on the destination,
/// then the token moves old room → new room directly (never duplicated, never in
/// two rooms: it is ONE cap, moving). The old room's voice expels; the new
/// room's admits.
pub fn move_rooms(
    world: &mut World,
    bus: &mut Bus,
    from_voice: &mut RoomVoice,
    to_voice: &mut RoomVoice,
    mover: Inhabitant,
    token: PresenceToken,
    presence_slot: usize,
) -> ActionOutcome {
    let door = move_through(world, mover, to_voice.room(), presence_slot);
    if !door.is_done() {
        return door;
    }
    let moved = move_cap(
        world,
        from_voice.room().cell,
        to_voice.room().cell,
        token.cell,
        AuthRequired::None,
    );
    if !moved.is_done() {
        return moved;
    }
    from_voice.expel(bus, mover);
    to_voice.admit(bus, mover);
    moved
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

    // ── PHASE 2: PRESENCE (conserved token) + SAY (over the data-plane Bus) ────
    //
    // TWO rooms (tavern + cellar) with a data-plane Bus carrying each room's
    // chat. ALICE holds door caps to both rooms; BOB holds the tavern door only;
    // MALLORY holds NO door caps (the locked-out would-be speaker). Each carries
    // their own presence token at genesis (present nowhere).
    struct SpeechWorld {
        world: World,
        bus: Bus,
        tavern: RoomVoice,
        cellar: RoomVoice,
        alice: Inhabitant,
        tok_a: PresenceToken,
        bob: Inhabitant,
        tok_b: PresenceToken,
        mallory: Inhabitant,
        tok_m: PresenceToken,
    }

    fn speech_world() -> SpeechWorld {
        let mut w = World::new();

        // Two rooms — plain open cells; entry is gated by the DOOR CAP the
        // executor checks, not by anything on the room itself.
        let tavern = Room::new(w.genesis_cell(0x40, 0));
        let cellar = Room::new(w.genesis_cell(0x41, 0));

        // Presence tokens — one cell each, minted before their owners so the
        // owners can be born carrying the cap to their own token.
        let tok_a = PresenceToken::new(w.genesis_cell(0x51, 0));
        let tok_b = PresenceToken::new(w.genesis_cell(0x52, 0));
        let tok_m = PresenceToken::new(w.genesis_cell(0x53, 0));

        // ALICE: doors to BOTH rooms + her own token at hand.
        let mut ac = make_open_cell(0xA1, 0);
        ac.capabilities
            .grant(tavern.cell, AuthRequired::None)
            .unwrap();
        ac.capabilities
            .grant(cellar.cell, AuthRequired::None)
            .unwrap();
        ac.capabilities
            .grant(tok_a.cell, AuthRequired::None)
            .unwrap();
        let alice = Inhabitant::new(w.genesis_install(ac));

        // BOB: the tavern door only + his token.
        let mut bc = make_open_cell(0xB0, 0);
        bc.capabilities
            .grant(tavern.cell, AuthRequired::None)
            .unwrap();
        bc.capabilities
            .grant(tok_b.cell, AuthRequired::None)
            .unwrap();
        let bob = Inhabitant::new(w.genesis_install(bc));

        // MALLORY: her token, NO doors — every entry is a locked door to her.
        let mut mc = make_open_cell(0xC0, 0);
        mc.capabilities
            .grant(tok_m.cell, AuthRequired::None)
            .unwrap();
        let mallory = Inhabitant::new(w.genesis_install(mc));

        // The data-plane Bus: a real relay identity whose FederationId IS its
        // Ed25519 pubkey, so every custody receipt verifies.
        let (sk, pk) = dregg_types::generate_keypair();
        let mut bus = Bus::new(FederationId(pk.0), sk, 1024, 65536);
        let tavern_voice = RoomVoice::new(tavern, &mut bus);
        let cellar_voice = RoomVoice::new(cellar, &mut bus);

        SpeechWorld {
            world: w,
            bus,
            tavern: tavern_voice,
            cellar: cellar_voice,
            alice,
            tok_a,
            bob,
            tok_b,
            mallory,
            tok_m,
        }
    }

    /// PRESENCE IS A CONSERVED TOKEN: two inhabitants in one room BOTH show in
    /// "who is here" (a ledger read); a door cap you lack still refuses entry
    /// (the phase-1 executor tooth, unchanged); and the token is NEVER in two
    /// rooms — moving rooms MOVES it (single custody), and you cannot leave a
    /// room you are not in (`mint_needs_held_factory` refuses).
    #[test]
    fn presence_is_a_conserved_token_and_the_door_still_refuses() {
        let mut s = speech_world();
        let roster = [(s.alice, s.tok_a), (s.bob, s.tok_b), (s.mallory, s.tok_m)];

        // Pre: everyone carries their own token; the rooms host nobody.
        assert!(s.tok_a.carried_by(&s.world, s.alice.cell));
        assert!(s.tavern.room().who_is_here(&s.world, &roster).is_empty());

        // ALICE and BOB enter the tavern — door-gated, then the token MOVES in.
        let a = enter(
            &mut s.world,
            &mut s.bus,
            &mut s.tavern,
            s.alice,
            s.tok_a,
            s.alice.cell,
            32,
        );
        assert!(
            a.is_done(),
            "alice holds the tavern door → enter commits: {a:?}"
        );
        let b = enter(
            &mut s.world,
            &mut s.bus,
            &mut s.tavern,
            s.bob,
            s.tok_b,
            s.bob.cell,
            33,
        );
        assert!(
            b.is_done(),
            "bob holds the tavern door → enter commits: {b:?}"
        );

        // WHO IS HERE — read off the room cell's live c-list: BOTH show.
        let here = s.tavern.room().who_is_here(&s.world, &roster);
        assert_eq!(
            here.len(),
            2,
            "two inhabitants present, both show: {here:?}"
        );
        assert!(here.contains(&s.alice) && here.contains(&s.bob));
        // …and their tokens LEFT their hands (the move conserved them).
        assert!(!s.tok_a.carried_by(&s.world, s.alice.cell));
        assert!(!s.tok_b.carried_by(&s.world, s.bob.cell));

        // THE DOOR STILL REFUSES: mallory holds no door cap. Her enter is refused
        // by the EXECUTOR (CapabilityNotHeld) — the phase-1 tooth — and her token
        // never moves: she is not present, and still carries it.
        let m = enter(
            &mut s.world,
            &mut s.bus,
            &mut s.tavern,
            s.mallory,
            s.tok_m,
            s.mallory.cell,
            34,
        );
        assert!(!m.is_done(), "no door cap → entry refused: {m:?}");
        if let ActionOutcome::Refused { reason } = &m {
            assert!(
                reason.contains("CapabilityNotHeld")
                    || reason.to_lowercase().contains("cap")
                    || reason.to_lowercase().contains("held")
                    || reason.to_lowercase().contains("permission"),
                "the refusal cites the missing door cap, got: {reason}"
            );
        }
        assert!(!s.tavern.room().hosts(&s.world, s.tok_m));
        assert!(s.tok_m.carried_by(&s.world, s.mallory.cell));

        // CONSERVATION ACROSS A MOVE: alice moves tavern → cellar. ONE cap moves;
        // she is present in exactly one room at every step, never two.
        let mv = move_rooms(
            &mut s.world,
            &mut s.bus,
            &mut s.tavern,
            &mut s.cellar,
            s.alice,
            s.tok_a,
            35,
        );
        assert!(
            mv.is_done(),
            "alice holds the cellar door → move commits: {mv:?}"
        );
        assert!(
            s.cellar.room().hosts(&s.world, s.tok_a),
            "alice is in the cellar"
        );
        assert!(
            !s.tavern.room().hosts(&s.world, s.tok_a),
            "…and NOT in the tavern — the token MOVED (never present in two rooms)"
        );

        // YOU CANNOT LEAVE WHERE YOU ARE NOT: bob "leaves" the cellar he never
        // entered — refused by mint_needs_held_factory (the cellar does not hold
        // his token), not by a presence check in this module.
        let ghost_leave = leave(&mut s.world, &mut s.bus, &mut s.cellar, s.bob, s.tok_b);
        assert!(
            !ghost_leave.is_done(),
            "leaving a room you are not in is refused by the gate: {ghost_leave:?}"
        );
        assert!(
            s.tavern.room().hosts(&s.world, s.tok_b),
            "bob is still exactly where he was"
        );
    }

    /// SAY RIDES THE BUS: a present speaker's utterance is a cap-gated enqueue
    /// (archived in the room's own inbox — its chat log) fanned to every present
    /// hearer, heard IN ORDER by both, each delivery a signed, verifying custody
    /// receipt witnessed on drain.
    #[test]
    fn say_over_the_bus_present_speakers_heard_in_order_by_both_hearers() {
        let mut s = speech_world();
        enter(
            &mut s.world,
            &mut s.bus,
            &mut s.tavern,
            s.alice,
            s.tok_a,
            s.alice.cell,
            32,
        );
        enter(
            &mut s.world,
            &mut s.bus,
            &mut s.tavern,
            s.bob,
            s.tok_b,
            s.bob.cell,
            33,
        );

        // Three utterances, interleaved speakers.
        let script: [(&Inhabitant, &[u8]); 3] = [
            (&s.alice, b"hello"),
            (&s.bob, b"well met"),
            (&s.alice, b"onward"),
        ];
        let mut archives = Vec::new();
        for (i, (speaker, text)) in script.iter().enumerate() {
            let out = s.tavern.say(&mut s.bus, **speaker, text, i as u64);
            match out {
                SayOutcome::Heard { archived, heard } => {
                    assert!(
                        archived.receipt.sig_verifies(),
                        "the archival receipt is a real signature"
                    );
                    assert_eq!(
                        heard.len(),
                        2,
                        "the utterance fanned to BOTH present hearers"
                    );
                    for (_, d) in &heard {
                        assert!(d.receipt.sig_verifies(), "each hearer's receipt verifies");
                    }
                    archives.push(archived);
                }
                SayOutcome::Refused { error } => {
                    panic!("a present speaker's say was refused: {error}")
                }
            }
        }

        // BOTH hearers drain their inboxes: every utterance, in say order (FIFO).
        let expected: Vec<Vec<u8>> = script.iter().map(|(_, t)| t.to_vec()).collect();
        for who in [s.alice, s.bob] {
            let boxes = s.bus.drain(&hearer_id(who));
            let got: Vec<Vec<u8>> = boxes.into_iter().map(|m| m.encrypted_payload).collect();
            assert_eq!(
                got, expected,
                "hearer {who:?} heard every utterance in order"
            );
        }

        // The ROOM'S OWN INBOX is its chat log — the same three, in order, and
        // draining it WITNESSES the archival deliveries (receipt-identity).
        let log = s.bus.drain(&s.tavern.inbox());
        let logged: Vec<Vec<u8>> = log.into_iter().map(|m| m.encrypted_payload).collect();
        assert_eq!(
            logged, expected,
            "the room's inbox is the ordered chat history"
        );
        for a in &archives {
            assert!(
                a.is_handled(s.bus.delivered_hashes(&s.tavern.inbox())),
                "each archived utterance is drain-witnessed (handled, not just promised)"
            );
        }
    }

    /// PRESENCE GATES SPEECH — through the CAP GATE, both polarities:
    /// a never-present speaker and a departed speaker are each refused by
    /// `SendCap::admits` inside the Bus (`DataPlaneError::Unauthorized`), leaving
    /// NO phantom work; leaving also SILENCES (the leaver hears nothing more);
    /// and re-entering restores the voice (the gate is not vacuously closed).
    #[test]
    fn an_absent_speaker_is_refused_by_the_cap_gate_and_leave_silences() {
        let mut s = speech_world();

        // MALLORY (never entered — she can't: no door cap) tries to speak. The
        // refusal is the Bus's own cap gate on the pre-revoked floor cap.
        let ghost = s.tavern.say(&mut s.bus, s.mallory, b"boo", 0);
        match ghost {
            SayOutcome::Refused { error } => assert!(
                matches!(error, DataPlaneError::Unauthorized { .. }),
                "the refusal is SendCap::admits' verdict, got: {error}"
            ),
            SayOutcome::Heard { .. } => panic!("an absent speaker was heard"),
        }
        // NO PHANTOM SPEECH: nothing queued anywhere, no cursor tick, no receipt.
        assert_eq!(s.bus.pending_count(&s.tavern.inbox()), 0);
        assert_eq!(s.bus.cursor(s.tavern.channel()), 0);

        // Alice and bob enter; bob then LEAVES (a receipted token move out).
        enter(
            &mut s.world,
            &mut s.bus,
            &mut s.tavern,
            s.alice,
            s.tok_a,
            s.alice.cell,
            32,
        );
        enter(
            &mut s.world,
            &mut s.bus,
            &mut s.tavern,
            s.bob,
            s.tok_b,
            s.bob.cell,
            33,
        );
        let out = leave(&mut s.world, &mut s.bus, &mut s.tavern, s.bob, s.tok_b);
        assert!(out.is_done(), "bob's leave commits: {out:?}");
        assert!(!s.tavern.room().hosts(&s.world, s.tok_b), "bob is gone");
        assert!(
            s.tok_b.carried_by(&s.world, s.bob.cell),
            "…carrying his token"
        );

        // THE DEPARTED SPEAKER: bob's speak cap is REVOKED — his say is refused
        // by the SAME cap gate (revocation, not an if-statement).
        let after = s.tavern.say(&mut s.bus, s.bob, b"one more thing", 1);
        match after {
            SayOutcome::Refused { error } => assert!(
                matches!(error, DataPlaneError::Unauthorized { .. }),
                "a departed speaker is refused by the cap gate, got: {error}"
            ),
            SayOutcome::Heard { .. } => panic!("a departed speaker was heard"),
        }

        // LEAVE SILENCES the other direction too: alice speaks; only SHE hears.
        let solo = s.tavern.say(&mut s.bus, s.alice, b"anyone?", 2);
        match solo {
            SayOutcome::Heard { heard, .. } => {
                assert_eq!(heard.len(), 1, "only the one present hearer");
                assert_eq!(heard[0].0, hearer_id(s.alice));
            }
            SayOutcome::Refused { error } => panic!("alice is present: {error}"),
        }
        assert_eq!(
            s.bus.pending_count(&hearer_id(s.bob)),
            0,
            "nothing lands in the departed hearer's inbox"
        );

        // RE-ENTRY RESTORES THE VOICE (non-vacuous): bob comes back through the
        // door he still holds, presence moves back in, a FRESH speak cap admits.
        let back = enter(
            &mut s.world,
            &mut s.bus,
            &mut s.tavern,
            s.bob,
            s.tok_b,
            s.bob.cell,
            34,
        );
        assert!(back.is_done(), "bob re-enters: {back:?}");
        let again = s.tavern.say(&mut s.bus, s.bob, b"i return", 3);
        assert!(
            again.is_heard(),
            "a re-admitted speaker is heard: {again:?}"
        );
    }
}
