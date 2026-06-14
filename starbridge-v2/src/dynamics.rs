//! The live "dynamics" — an observation stream of state transitions.
//!
//! This is the model the visual layer renders, decoupled from gpui and from the
//! executor: a `World` EMITS [`WorldEvent`]s as it commits turns, and any view
//! (or test) CONSUMES them. It is the temporal/causal spine of the cockpit —
//! "cell born", "cap granted", "turn committed", "balance flowed", "receipt
//! linked" — the raw material for the cell-world animation, the blocklace
//! browser, and the activity feed.
//!
//! It is intentionally a plain append-only log with a cursor, not a callback
//! bus: views poll `since(cursor)` on each frame, which is trivially correct
//! under gpui's pull-render model and needs no shared-mutability plumbing.

use dregg_cell::CellId;
use serde::{Deserialize, Serialize};

/// One observed state transition in the live world.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum WorldEvent {
    /// A cell came into existence (genesis seed, or a `CreateCell` effect).
    CellBorn {
        cell: CellId,
        balance: i64,
        /// True if installed directly at genesis (vs. born by a committed turn).
        genesis: bool,
    },
    /// A turn committed against the verified executor (a new height/receipt).
    TurnCommitted {
        height: u64,
        agent: CellId,
        receipt_hash: [u8; 32],
        turn_hash: [u8; 32],
        action_count: usize,
        computrons: u64,
    },
    /// The real executor REJECTED a turn — an ocap/verification guarantee
    /// firing (recorded so the cockpit can show WHY authority was denied).
    TurnRejected { agent: CellId, reason: String },
    /// Value flowed into/out of a cell as a result of a committed turn.
    BalanceFlowed {
        cell: CellId,
        before: i64,
        after: i64,
    },
    /// A capability edge was granted (the ocap graph grew an edge).
    CapabilityGranted { from: CellId, to: CellId },
    /// A capability slot was revoked (the ocap graph lost an edge).
    CapabilityRevoked { cell: CellId, slot: u32 },
    /// A state field slot was written.
    FieldSet { cell: CellId, index: usize },
    /// A cell was sealed (lifecycle → Sealed; rejects effects until unsealed).
    CellSealed { cell: CellId },
    /// A sealed cell was unsealed (lifecycle → Live).
    CellUnsealed { cell: CellId },
    /// A cell was permanently retired (lifecycle → Destroyed; terminal).
    CellDestroyed { cell: CellId },
    /// Value was provably burned from a cell (supply reduced; no credit).
    Burned { cell: CellId, amount: u64 },
    /// An event was emitted by `sender` targeting `cell` (the async notify
    /// edge). This is the SENDER's committed turn record; the RECIPIENT
    /// cell drains it in its OWN separate future turn — NOT a synchronous
    /// joint turn. This is the A2 tool-call seam: an agent's `EmitEvent`
    /// action is the one receipted seam-record the swarm coordinator reads
    /// to wake the recipient, without coupling the two loops.
    EventEmitted {
        /// The cell that committed the `EmitEvent` effect (the sender).
        sender: CellId,
        /// The cell the event is addressed to (the intended recipient /
        /// notify target). Its inbox gains a pending `NotifyEdge`.
        cell: CellId,
        /// The topic hash (Blake3 of the topic string, as the executor sees it).
        topic_hash: [u8; 32],
        /// The data payload length (bytes), for the activity feed label.
        data_len: usize,
    },
}

impl WorldEvent {
    /// A short human label for the activity feed.
    pub fn label(&self) -> String {
        match self {
            WorldEvent::CellBorn { genesis, balance, .. } => {
                if *genesis {
                    format!("cell born (genesis, {balance})")
                } else {
                    format!("cell born ({balance})")
                }
            }
            WorldEvent::TurnCommitted {
                height,
                action_count,
                ..
            } => format!("turn committed @h{height} ({action_count} actions)"),
            WorldEvent::TurnRejected { reason, .. } => format!("turn REJECTED: {reason}"),
            WorldEvent::BalanceFlowed { before, after, .. } => {
                let d = after - before;
                let sign = if d >= 0 { "+" } else { "" };
                format!("balance flowed {sign}{d}")
            }
            WorldEvent::CapabilityGranted { .. } => "capability granted".into(),
            WorldEvent::CapabilityRevoked { slot, .. } => format!("capability revoked (slot {slot})"),
            WorldEvent::FieldSet { index, .. } => format!("field[{index}] set"),
            WorldEvent::CellSealed { .. } => "cell sealed".into(),
            WorldEvent::CellUnsealed { .. } => "cell unsealed".into(),
            WorldEvent::CellDestroyed { .. } => "cell destroyed (terminal)".into(),
            WorldEvent::Burned { amount, .. } => format!("burned {amount} (supply reduced)"),
            WorldEvent::EventEmitted { sender, cell, data_len, .. } => format!(
                "event emitted: {} → {} ({data_len}B) [notify edge]",
                crate::reflect::short_hex(sender.as_bytes()),
                crate::reflect::short_hex(cell.as_bytes()),
            ),
        }
    }
}

/// The append-only dynamics log with a monotonic cursor.
pub struct Dynamics {
    events: Vec<WorldEvent>,
}

impl Default for Dynamics {
    fn default() -> Self {
        Self::new()
    }
}

impl Dynamics {
    pub fn new() -> Self {
        Dynamics { events: Vec::new() }
    }

    /// Append an observed transition.
    pub fn emit(&mut self, event: WorldEvent) {
        self.events.push(event);
    }

    /// The current cursor (== total events emitted). A view stores this and
    /// passes it back to [`Self::since`] next frame to get only what's new.
    pub fn cursor(&self) -> usize {
        self.events.len()
    }

    /// All events at or after `cursor`.
    pub fn since(&self, cursor: usize) -> &[WorldEvent] {
        let start = cursor.min(self.events.len());
        &self.events[start..]
    }

    /// The whole log (most-recent-last).
    pub fn all(&self) -> &[WorldEvent] {
        &self.events
    }

    /// The last `n` events, most-recent-last.
    pub fn tail(&self, n: usize) -> &[WorldEvent] {
        let start = self.events.len().saturating_sub(n);
        &self.events[start..]
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cursor_yields_only_new_events() {
        let mut d = Dynamics::new();
        d.emit(WorldEvent::FieldSet {
            cell: CellId::ZERO,
            index: 0,
        });
        let c = d.cursor();
        assert_eq!(d.since(c).len(), 0);
        d.emit(WorldEvent::FieldSet {
            cell: CellId::ZERO,
            index: 1,
        });
        assert_eq!(d.since(c).len(), 1);
        assert_eq!(d.all().len(), 2);
    }

    #[test]
    fn tail_returns_most_recent() {
        let mut d = Dynamics::new();
        for i in 0..5 {
            d.emit(WorldEvent::FieldSet {
                cell: CellId::ZERO,
                index: i,
            });
        }
        let t = d.tail(2);
        assert_eq!(t.len(), 2);
        assert!(matches!(t[1], WorldEvent::FieldSet { index: 4, .. }));
    }
}
