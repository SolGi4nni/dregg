//! THE ROOM + INHABITANT model — a place, felt, rendered from the live ledger.
//!
//! Mirrors `starbridge-v2/src/room.rs` (organ 5) in the gpui-free, dependency-light shape this
//! runnable demo needs: a [`Room`] is a place that CONTAINS inhabitants; an [`InhabitantView`]
//! renders an inhabitant's held mandate, its GENUINE (committed, receipted) actions, and its in-room
//! REFUSALS. The two render distinctly so the operator sees a colonist doing its job vs. the moment
//! it was stopped — the anti-ghost tooth made visible: a refusal is the on-ledger truth (it advanced
//! no chain, produced no receipt), never faked as a success and never silently dropped.
//!
//! Unlike the starbridge-v2 model (which reads the desktop `World`), this one is populated by the
//! [`scenario`](crate::scenario) driver from the REAL [`EmbeddedExecutor`] receipts/refusals, so the
//! crate stays a thin weld with no desktop-surface dependency.

use dregg_app_framework::CellId;

/// THE ROOM — a place that contains inhabitants. It is a pure membership + presentation overlay; it
/// adds no authority and bypasses no executor gate. An inhabitant's reach is its mandate, whichever
/// room it stands in.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Room {
    /// The room cell (the place's own entity).
    pub cell: CellId,
    /// A short operator-legible name for the room (e.g. "the workshop").
    pub name: String,
    /// The inhabitant views present in this room, in entry order.
    pub inhabitants: Vec<InhabitantView>,
}

impl Room {
    /// A new, empty room backed by `cell` with the legible `name`.
    pub fn new(cell: CellId, name: impl Into<String>) -> Self {
        Room {
            cell,
            name: name.into(),
            inhabitants: Vec::new(),
        }
    }

    /// An inhabitant ENTERS the room (becomes present, in entry order).
    pub fn enter(&mut self, inhabitant: InhabitantView) {
        self.inhabitants.push(inhabitant);
    }

    /// How many inhabitants are present.
    pub fn occupancy(&self) -> usize {
        self.inhabitants.len()
    }

    /// A read-only render of the room (its identity + present inhabitants).
    pub fn render(&self) -> RoomView {
        RoomView {
            cell: self.cell,
            name: self.name.clone(),
            inhabitants: self.inhabitants.clone(),
        }
    }

    /// Every refusal that fired in this room, across all inhabitants — the in-room anti-ghost
    /// surface: in one place, every time an inhabitant tried to exceed its mandate and was refused.
    pub fn refusals(&self) -> Vec<&InRoomRefusal> {
        self.inhabitants
            .iter()
            .flat_map(|i| i.refusals.iter())
            .collect()
    }

    /// The total count of committed (genuine, on-ledger) actions across all inhabitants.
    pub fn committed_action_count(&self) -> usize {
        self.inhabitants
            .iter()
            .map(|i| i.committed_actions.len())
            .sum()
    }
}

/// A read-only render of the room — the headless model a paint layer (or a printer) consumes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RoomView {
    pub cell: CellId,
    pub name: String,
    pub inhabitants: Vec<InhabitantView>,
}

/// THE RENDERED INHABITANT — a cell present in a room, with the mandate it holds and the live actions
/// it took, split into the GENUINE (committed, receipted) and the in-room REFUSALS.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InhabitantView {
    /// The inhabitant cell.
    pub cell: CellId,
    /// A short operator-legible id (abbreviated hex of the cell).
    pub short: String,
    /// A legible name for the inhabitant (e.g. "the colonist", "the buildr agent").
    pub name: String,
    /// THE HELD MANDATE — a legible description of the inhabitant's verbs / the job it holds. (Here:
    /// the colonist's DAG job and its budget/clearance — the thing it provably can't exceed.)
    pub mandate: String,
    /// THE GENUINE ACTIONS — the committed, receipted turns (entry order): what it actually did, each
    /// carrying a real receipt hash + a human-meaningful summary.
    pub committed_actions: Vec<GenuineAction>,
    /// THE IN-ROOM REFUSALS — every turn it ATTEMPTED that the real executor refused (it exceeded its
    /// mandate), surfaced in-room with the receipt-why. Never faked as a success, never dropped.
    pub refusals: Vec<InRoomRefusal>,
    /// The reward the inhabitant was PAID on settlement (0 until the job is done and the escrow
    /// releases). The pay-for-work loop, rendered.
    pub paid: u64,
}

impl InhabitantView {
    /// A genuine action's count.
    pub fn committed_count(&self) -> usize {
        self.committed_actions.len()
    }
}

/// A GENUINE, on-ledger action — a committed signed turn, with its real receipt hash + a summary of
/// what it did in the world.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GenuineAction {
    /// A human-meaningful summary of the effect (e.g. "gather (step 0→1, spend 3/9)").
    pub summary: String,
    /// The turn's real receipt hash (proof it committed).
    pub receipt_hash: [u8; 32],
}

/// AN IN-ROOM REFUSAL — the visible firing of the verification guarantee: an inhabitant tried to
/// exceed its mandate and the real executor refused. Carries the receipt-why (the executor's reason).
/// A refusal advanced no chain and produced no receipt — that absence IS the truth.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InRoomRefusal {
    /// What the inhabitant tried to do (the attempted verb / cheat).
    pub attempted: String,
    /// The executor's reason for refusing (the receipt-why) — e.g. a skipped prerequisite, an
    /// overspend, an out-of-clearance verb, a non-conserving settle.
    pub reason: String,
}

/// Abbreviate a cell id to a short operator-legible hex prefix.
pub fn short_hex(cell: &CellId) -> String {
    let b = cell.as_bytes();
    let n = b.len().min(4);
    let mut s = String::with_capacity(2 * n + 1);
    for x in &b[..n] {
        s.push_str(&format!("{x:02x}"));
    }
    s.push('…');
    s
}
