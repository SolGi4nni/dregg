//! THE ROOM + INHABITANT — a world, felt. (ORGAN 5, headless model.)
//!
//! dregg read as a WORLD: a persistent place whose inhabitants — human or agent
//! — act ONLY through a MANDATE proven safe-forever. This module makes a ROOM a
//! first-class thing the desktop can render:
//!
//!   * a **ROOM** is a place that CONTAINS inhabitants. It is backed by a real
//!     room CELL in the embedded [`World`](crate::world) (an ENTITY, like any
//!     other), and it names which inhabitant cells are PRESENT in it (the
//!     containment relation — a room IS its membership).
//!   * an **INHABITANT** is a cell + a HELD MANDATE + presence-in-a-room. Its
//!     mandate and its live actions are NOT re-modeled here: they are exactly the
//!     [`AgentActivity`](crate::agent::AgentActivity) the agent-activity surface
//!     already grounds — the held cap-edges read from the cell's c-list, and the
//!     committed/refused turns read from the world's receipt log + dynamics
//!     stream. An inhabitant is precisely as powerful as the mandate it holds.
//!   * a **ROOM VIEW** renders a room: its inhabitants, each one's held mandate,
//!     and each one's live actions — and crucially surfaces every REFUSAL. When
//!     an inhabitant tries to exceed its mandate, the real executor refuses the
//!     turn ([`CommitOutcome::Rejected`](crate::world::CommitOutcome)); that
//!     refusal lands on the dynamics stream as a `TurnRejected`, and it renders
//!     IN-ROOM as an [`InRoomRefusal`] carrying the receipt-why. The anti-ghost
//!     tooth made visible: you cannot be fooled about what an inhabitant did, or
//!     may do — a refusal is the on-ledger truth, never faked as a success and
//!     never silently dropped.
//!
//! The mapping (ember's vision): a cell = an ENTITY (inhabitant / room / item);
//! a turn = an ACTION (cap-gated + receipted); a tool-delegation = a character's
//! VERBS; the held mandate = the colonist's JOB it provably can't exceed. This
//! module welds those onto the existing surface — it does NOT rebuild the
//! grounding (the executor, the ledger, the activity model already do that).
//!
//! gpui-FREE and `cargo test`-able, in the established `web_cells`/`agent`
//! discipline: the room model is built purely from the [`World`]; a gpui paint
//! layer (placing inhabitants in a 2-D room, drawing the refusal toast) is a
//! follow-on, NOT this organ. The view here is the data that layer renders.

use dregg_cell::CellId;

use crate::agent::{AgentAction, AgentActivity, MandateEdge};
use crate::world::World;

/// THE ROOM — a place that contains inhabitants. Backed by a real room cell in
/// the [`World`] (an entity), it names the inhabitant cells PRESENT in it (the
/// containment relation). The room is a pure membership overlay: it adds no
/// authority and bypasses no executor gate — an inhabitant's reach is its
/// mandate, whichever room it stands in. Presence is the WORLD-MODEL fact "this
/// cell is here"; what it may DO is still the executor's to decide.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Room {
    /// The room cell (the place's own entity in the ledger). A room is a cell,
    /// so a room can itself hold a balance, a program, caps — it is not special-
    /// cased; it is an entity like its inhabitants.
    pub cell: CellId,
    /// A short operator-legible name for the room (caller-supplied; the place's
    /// label in the world, e.g. "the workshop", "the courtyard").
    pub name: String,
    /// The inhabitant cells PRESENT in this room, in entry order. The
    /// containment relation: a room IS who is here. (Membership, not authority —
    /// an absent cell can still be acted upon by one that holds a cap to it; this
    /// records who is rendered IN the place.)
    present: Vec<CellId>,
}

impl Room {
    /// A new, empty room backed by `cell` with the legible `name`. No inhabitants
    /// are present until [`Room::enter`]'d.
    pub fn new(cell: CellId, name: impl Into<String>) -> Self {
        Room {
            cell,
            name: name.into(),
            present: Vec::new(),
        }
    }

    /// An inhabitant ENTERS the room (becomes present). Idempotent: entering a
    /// cell already present is a no-op (it does not appear twice). Returns `true`
    /// if presence changed (the cell was not already here).
    pub fn enter(&mut self, inhabitant: CellId) -> bool {
        if self.present.contains(&inhabitant) {
            return false;
        }
        self.present.push(inhabitant);
        true
    }

    /// An inhabitant LEAVES the room (is no longer present). Returns `true` if it
    /// was present (and is now removed).
    pub fn leave(&mut self, inhabitant: &CellId) -> bool {
        if let Some(i) = self.present.iter().position(|c| c == inhabitant) {
            self.present.remove(i);
            true
        } else {
            false
        }
    }

    /// `true` iff `inhabitant` is currently present in this room.
    pub fn contains(&self, inhabitant: &CellId) -> bool {
        self.present.contains(inhabitant)
    }

    /// The inhabitant cells present, in entry order (the containment relation).
    pub fn present(&self) -> &[CellId] {
        &self.present
    }

    /// How many inhabitants are present.
    pub fn occupancy(&self) -> usize {
        self.present.len()
    }

    /// RENDER this room from the live world: build each present inhabitant's view
    /// (held mandate + live actions + in-room refusals), bound by `max_actions`
    /// recent actions each. This is the data the gpui paint layer renders — the
    /// room felt, with every refusal surfaced. The render reads the REAL ledger +
    /// dynamics: nothing here is fabricated, and a refused turn renders as a
    /// refusal (never as a success, never dropped).
    pub fn render(&self, world: &World, max_actions: usize) -> RoomView {
        let short = crate::reflect::short_hex(self.cell.as_bytes());
        let backed = world.ledger().contains(&self.cell);
        let inhabitants: Vec<InhabitantView> = self
            .present
            .iter()
            .map(|&c| InhabitantView::render(world, c, max_actions))
            .collect();
        RoomView {
            cell: self.cell,
            short,
            name: self.name.clone(),
            backed,
            inhabitants,
        }
    }
}

/// THE RENDERED ROOM — the place, felt: its identity, whether it is a real cell,
/// and each present inhabitant with their held mandate + live actions + the
/// refusals that fired in-room. The headless model a gpui room-paint consumes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RoomView {
    /// The room cell.
    pub cell: CellId,
    /// A short operator-legible id for the room cell (abbreviated).
    pub short: String,
    /// The room's legible name.
    pub name: String,
    /// Whether the room cell is live in the ledger (a room grounded in a real
    /// entity, or not — shown honestly, never a phantom place).
    pub backed: bool,
    /// The present inhabitants, each rendered with mandate + actions + refusals,
    /// in entry order.
    pub inhabitants: Vec<InhabitantView>,
}

impl RoomView {
    /// How many inhabitants are rendered in the room.
    pub fn occupancy(&self) -> usize {
        self.inhabitants.len()
    }

    /// Every refusal that fired in this room, across all inhabitants — the
    /// in-room anti-ghost surface: the operator sees, in one place, every time an
    /// inhabitant tried to exceed its mandate and was refused (with the why).
    pub fn refusals(&self) -> Vec<&InRoomRefusal> {
        self.inhabitants
            .iter()
            .flat_map(|i| i.refusals.iter())
            .collect()
    }

    /// The total count of committed (genuine, on-ledger) actions across all
    /// inhabitants — the room's live activity at a glance.
    pub fn committed_action_count(&self) -> usize {
        self.inhabitants.iter().map(|i| i.committed_actions.len()).sum()
    }
}

/// THE RENDERED INHABITANT — a cell present in a room, with the mandate it holds
/// and the live actions it took. Its mandate + actions are the grounded
/// [`AgentActivity`]; this view splits the activity into the GENUINE (committed,
/// receipted) actions and the in-room REFUSALS so the paint layer can render the
/// two distinctly: a colonist doing its job, vs. the moment it was stopped.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InhabitantView {
    /// The inhabitant cell.
    pub cell: CellId,
    /// A short operator-legible id for the inhabitant (abbreviated).
    pub short: String,
    /// Whether the inhabitant cell is live in the ledger (present-but-real, or a
    /// ghost — shown honestly).
    pub backed: bool,
    /// The inhabitant's live balance (the resources it holds — pay-for-action).
    pub balance: i64,
    /// THE HELD MANDATE — the inhabitant's attenuated capability edges (its
    /// VERBS: which cells it may act upon, at what rights). Read from the live
    /// c-list; it is exactly as powerful as this mandate, nothing ambient.
    pub mandate: Vec<MandateEdge>,
    /// THE GENUINE ACTIONS — the inhabitant's committed, receipted turns
    /// (most-recent-first): what it actually did in the world, each carrying its
    /// receipt hash + a human-meaningful summary of its effects.
    pub committed_actions: Vec<AgentAction>,
    /// THE IN-ROOM REFUSALS — every turn this inhabitant ATTEMPTED that the real
    /// executor refused (it exceeded its mandate). Surfaced in-room with the
    /// receipt-why; never faked as a success, never dropped. The anti-ghost tooth.
    pub refusals: Vec<InRoomRefusal>,
}

impl InhabitantView {
    /// Render an inhabitant from the live world: build its grounded
    /// [`AgentActivity`] (held mandate + committed + refused turns) and split it
    /// into the genuine actions and the in-room refusals.
    pub fn render(world: &World, cell: CellId, max_actions: usize) -> Self {
        let activity = AgentActivity::build(world, cell, max_actions);
        Self::from_activity(activity)
    }

    /// Build the inhabitant view from an already-built [`AgentActivity`] (the
    /// pure split — reused by `render` and directly testable). The genuine
    /// actions keep their full receipt; the refused actions become
    /// [`InRoomRefusal`]s carrying the executor's refusal reason.
    pub fn from_activity(activity: AgentActivity) -> Self {
        let mut committed_actions = Vec::new();
        let mut refusals = Vec::new();
        for action in activity.actions {
            if action.committed {
                committed_actions.push(action);
            } else {
                // A refused turn never advanced the chain (height = None, no
                // receipt). The activity model already carries its reason in the
                // summary ("REFUSED — <why>"); surface it in-room with the why.
                refusals.push(InRoomRefusal {
                    reason: strip_refused_prefix(&action.summary),
                });
            }
        }
        InhabitantView {
            cell: activity.agent,
            short: activity.short,
            backed: activity.backed,
            balance: activity.balance,
            mandate: activity.mandate,
            committed_actions,
            refusals,
        }
    }
}

/// AN IN-ROOM REFUSAL — the visible firing of the verification guarantee: an
/// inhabitant tried to exceed its mandate and the real executor refused. It
/// carries the receipt-why (the executor's refusal reason). A refusal advanced
/// no chain and produced no receipt hash — that absence IS the truth: nothing
/// happened in the world, and the room shows exactly that (no faked success).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InRoomRefusal {
    /// The executor's reason for refusing the action (the receipt-why) — e.g. an
    /// over-grant of a cap the inhabitant does not hold, a non-conserving
    /// transfer, an effect its cell's permissions forbid.
    pub reason: String,
}

/// Strip the activity model's `"REFUSED — "` summary prefix so the in-room
/// refusal carries just the executor's reason (the why), not the redundant tag.
fn strip_refused_prefix(summary: &str) -> String {
    summary
        .strip_prefix("REFUSED — ")
        .unwrap_or(summary)
        .to_string()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::world::{grant_capability, transfer, World};

    /// A world with a room cell and an inhabitant that holds a mandate (a cap to
    /// a peer) and has committed a real cap-gated turn — the room to render.
    fn room_world() -> (World, Room, CellId, CellId) {
        let mut w = World::new();
        let peer = w.genesis_cell(0x33, 0);
        // The room is a cell (an entity). Its inhabitant is born holding a cap
        // reaching the peer (its mandate / verbs).
        let room_cell = w.genesis_cell(0x10, 0);
        let (dweller, _slot) = w.genesis_cell_with_cap(0x22, 10_000, peer);
        // The inhabitant does its job: a genuine cap-gated transfer to the peer.
        let t1 = w.turn(dweller, vec![transfer(dweller, peer, 1_000)]);
        assert!(w.commit_turn(t1).is_committed());

        let mut room = Room::new(room_cell, "the workshop");
        room.enter(dweller);
        (w, room, dweller, peer)
    }

    #[test]
    fn a_room_contains_inhabitants() {
        // CONTAINMENT: a room names who is present; enter/leave maintain it.
        let (_w, mut room, dweller, _peer) = room_world();
        assert_eq!(room.occupancy(), 1, "one inhabitant present");
        assert!(room.contains(&dweller), "the dweller is here");
        // Idempotent entry.
        assert!(!room.enter(dweller), "re-entering is a no-op");
        assert_eq!(room.occupancy(), 1, "still one inhabitant");
        // Leaving removes presence.
        assert!(room.leave(&dweller));
        assert!(!room.contains(&dweller), "the dweller has left");
        assert_eq!(room.occupancy(), 0);
        assert!(!room.leave(&dweller), "leaving an absent cell is false");
    }

    #[test]
    fn the_room_renders_its_inhabitants_with_held_mandate() {
        // GENUINE ✓ (mandate): the room renders each inhabitant with the mandate
        // it actually holds (read from the live c-list, not modeled here).
        let (w, room, dweller, peer) = room_world();
        let view = room.render(&w, 16);
        assert!(view.backed, "the room cell is a real entity");
        assert_eq!(view.name, "the workshop");
        assert_eq!(view.occupancy(), 1, "one inhabitant rendered");
        let inh = &view.inhabitants[0];
        assert_eq!(inh.cell, dweller);
        assert!(inh.backed, "the inhabitant is a live cell");
        assert!(!inh.mandate.is_empty(), "it holds a mandate (its verbs)");
        assert!(
            inh.mandate.iter().any(|m| m.target == peer),
            "the held mandate reaches the peer"
        );
    }

    #[test]
    fn the_room_renders_live_committed_actions_with_receipts() {
        // GENUINE ✓ (actions): the inhabitant's committed turn renders as a
        // genuine action carrying its real receipt + effect summary — what it
        // actually did in the world.
        let (w, room, _dweller, _peer) = room_world();
        let view = room.render(&w, 16);
        let inh = &view.inhabitants[0];
        assert_eq!(inh.committed_actions.len(), 1, "one genuine cap-gated action");
        let action = &inh.committed_actions[0];
        assert!(action.committed, "it is a genuine committed action");
        assert!(action.receipt_hash.is_some(), "carrying a real receipt hash");
        assert!(action.height.is_some(), "and a chain height");
        assert!(
            action.summary.contains("flow"),
            "the transfer summarizes its balance flow, got {:?}",
            action.summary
        );
        // No refusal fired — the inhabitant stayed within its mandate.
        assert!(inh.refusals.is_empty(), "no refusal for a within-mandate action");
        assert_eq!(view.committed_action_count(), 1);
    }

    #[test]
    fn a_cheat_attempt_renders_in_room_as_a_refusal_with_the_why_never_faked() {
        // CHEAT ✗ (refusal, never faked): an inhabitant that attempts to exceed
        // its mandate — granting a cap it does NOT hold — is REFUSED by the real
        // executor, and the room renders that refusal IN-ROOM with the receipt-
        // why. It is NOT faked as a committed action, and NOT silently dropped.
        let mut w = World::new();
        let room_cell = w.genesis_cell(0x10, 0);
        // The inhabitant holds NO cap to `target` (a confined mandate).
        let cheater = w.genesis_cell(0x55, 100);
        let target = w.genesis_cell(0x66, 0);

        let mut room = Room::new(room_cell, "the courtyard");
        room.enter(cheater);

        // It ATTEMPTS the over-grant — the real executor must refuse it.
        let bad = w.turn(cheater, vec![grant_capability(cheater, cheater, target, 0)]);
        assert!(
            !w.commit_turn(bad).is_committed(),
            "the over-grant must be refused by the real executor"
        );

        let view = room.render(&w, 16);
        let inh = &view.inhabitants[0];
        // The cheat did NOT render as a genuine action (no faked success).
        assert!(
            inh.committed_actions.is_empty(),
            "a refused cheat must NOT appear as a committed action"
        );
        // It DID render as an in-room refusal, carrying the receipt-why.
        assert_eq!(inh.refusals.len(), 1, "the refusal is surfaced in-room");
        let refusal = &inh.refusals[0];
        assert!(
            !refusal.reason.is_empty(),
            "the refusal carries the executor's why (non-empty), got {:?}",
            refusal.reason
        );
        assert!(
            !refusal.reason.starts_with("REFUSED"),
            "the why is the bare reason, not the redundant tag, got {:?}",
            refusal.reason
        );
        // The room's aggregate refusal surface sees it too.
        assert_eq!(view.refusals().len(), 1, "the room-wide refusal surface shows it");
        assert_eq!(view.committed_action_count(), 0, "nothing committed");
    }

    #[test]
    fn both_polarities_coexist_in_one_room() {
        // BOTH POLARITIES TOGETHER: one inhabitant does its job (genuine ✓) and
        // ALSO tries to overreach (cheat ✗). The room renders the genuine action
        // AND the refusal side-by-side — the colonist working, and the moment it
        // was stopped, both true on the ledger.
        let (mut w, room, dweller, _peer) = room_world();
        let stranger = w.genesis_cell(0x99, 0); // dweller holds NO cap to it
        // The dweller attempts to grant a cap it does not hold → refused.
        let bad = w.turn(dweller, vec![grant_capability(dweller, dweller, stranger, 1)]);
        assert!(!w.commit_turn(bad).is_committed(), "the overreach is refused");

        let view = room.render(&w, 16);
        let inh = view.inhabitants.iter().find(|i| i.cell == dweller).unwrap();
        // The genuine transfer is still there (committed, receipted)...
        assert_eq!(inh.committed_actions.len(), 1, "the genuine action remains");
        assert!(inh.committed_actions[0].receipt_hash.is_some());
        // ...alongside the refusal of the overreach.
        assert_eq!(inh.refusals.len(), 1, "the overreach renders as a refusal");
    }

    #[test]
    fn a_room_with_an_unbacked_cell_is_shown_honestly() {
        // ANTI-PHANTOM: a room backed by no real cell, holding a ghost
        // inhabitant, is rendered honestly — neither the place nor the dweller
        // can masquerade as live.
        let w = World::new();
        let ghost_room = CellId::from_bytes([0xAA; 32]);
        let ghost_dweller = CellId::from_bytes([0xBB; 32]);
        let mut room = Room::new(ghost_room, "nowhere");
        room.enter(ghost_dweller);
        let view = room.render(&w, 16);
        assert!(!view.backed, "the room cell is not real");
        let inh = &view.inhabitants[0];
        assert!(!inh.backed, "the inhabitant is a ghost");
        assert!(inh.mandate.is_empty(), "a ghost holds no mandate");
        assert!(inh.committed_actions.is_empty());
        assert!(inh.refusals.is_empty());
    }

    #[test]
    fn many_inhabitants_render_in_entry_order() {
        // MULTIPLICITY: several inhabitants are present and render in entry order
        // — the room as a populated place, each with its own grounded activity.
        let mut w = World::new();
        let room_cell = w.genesis_cell(0x10, 0);
        let a = w.genesis_cell(0x01, 10);
        let b = w.genesis_cell(0x02, 20);
        let c = w.genesis_cell(0x03, 30);
        let mut room = Room::new(room_cell, "the hall");
        room.enter(a);
        room.enter(b);
        room.enter(c);
        let view = room.render(&w, 8);
        assert_eq!(view.occupancy(), 3, "three inhabitants present");
        assert_eq!(view.inhabitants[0].cell, a, "entry order preserved");
        assert_eq!(view.inhabitants[1].cell, b);
        assert_eq!(view.inhabitants[2].cell, c);
        assert_eq!(view.inhabitants[1].balance, 20, "each carries its live state");
    }
}
