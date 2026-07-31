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
//!
//! # Bounded retention (long-session memory)
//!
//! The stream is append-only from the *caller's* view — cursors are ABSOLUTE,
//! monotonic indices into the total history — but the backing storage is a
//! bounded ring: once the retained window exceeds [`Dynamics::cap()`], [`emit`]
//! evicts the oldest events. Without this a long-running node/desktop session
//! leaks memory forever (every `commit_turn` emits several events and nothing
//! ever shrinks the log — CORE-AUDIT #11).
//!
//! Eviction is cursor-SAFE. The struct keeps a monotonic [`base`](Dynamics::base())
//! offset — the number of events dropped off the front — so `cursor()` still
//! reports `base + retained`, exactly the total ever emitted. [`since`] resolves
//! a caller's absolute cursor against `max(cursor, base)`: a live cursor inside
//! the retained window resolves EXACTLY, and a cursor that fell BEHIND the
//! evicted window is clamped up to `base` and gets the retained tail — never a
//! panic and never a wrong slice. (A consumer that lags more than the whole
//! retained window therefore *misses* the evicted span; the one such consumer,
//! the desktop pulse pump, detects the lag via [`Dynamics::base()`] and recovers
//! conservatively — see `deos_desktop::DeosDesktop::pump_dynamics`.)
//!
//! [`emit`]: Dynamics::emit
//! [`since`]: Dynamics::since

use std::collections::{BTreeSet, HashSet};
use std::future::Future;
use std::pin::Pin;
use std::sync::{Arc, Mutex, MutexGuard};
use std::task::{Context as TaskContext, Poll, Waker};

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
    /// A turn was QUEUED rather than committed because the world is SUSPENDED
    /// (the meta-debug Suspend gate, `docs/deos/FIRMAMENT-REFLEXIVE-SUBSTRATE.md`
    /// §3.2). The live loop is halted: the turn lands in the pending queue, in
    /// arrival order, and does NOT advance the head. It commits on `resume(drain)`,
    /// at which point it emits the normal `TurnCommitted` events. Emitting THIS
    /// event keeps the dynamics stream complete under suspension (Seam 3: a
    /// silently-queued turn would be a stale-projection bug).
    TurnQueued { agent: CellId },
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
    /// A cell's NON-field state was mutated without a more specific event — the
    /// generic "this cell changed" tooth (nonce bump, sovereign flip, permissions
    /// / verification-key write, capability reshape). It exists so the M2 delta
    /// loop's invalidation is COMPLETE: every `commit_turn` effect that writes a
    /// cell the inspector renders names that cell in the dynamics stream, so a
    /// memoized projection of that cell is always invalidated. (Cache soundness =
    /// dynamics completeness — `.docs-history-noclaude/deos/EFFICIENCY-WELD-PLAN.md` §4.1.)
    CellMutated { cell: CellId },
    /// **A cell's universal-memory HEAP was written out-of-band and its committed
    /// `heap_root` resealed** (`World::set_cell_heap` — the shipping desktop
    /// document editor's persist path, `deos_desktop::commit_doc_to_umem_heap`).
    ///
    /// This is a DELIBERATELY DISTINCT tooth from [`CellMutated`](Self::CellMutated),
    /// not a nicer label for it. The heap register is ORTHOGONAL to `fields_map` —
    /// a heap write moves no field slot — while `CellMutated` routes to the
    /// consumers' conservative `invalidate_cell`, which dirties EVERY binding that
    /// reads the cell. The desktop's user cell carries both `AGENT_COUNTER_SLOT`
    /// (0, `agent_attach.rs`) and `DOC_REV_SLOT` (14, `deos_desktop/chrome.rs`), so
    /// emitting `CellMutated` per document keystroke would light every field bind on
    /// every open card, every beat of typing. A consumer that invalidates FIELD
    /// binds must therefore ignore this variant; a consumer that caches a whole-cell
    /// projection (which includes `heap_root`) must honour it.
    ///
    /// It still NAMES its cell in [`collect_named_cells`](Self::collect_named_cells)
    /// — the write-set completeness property ("cache soundness = dynamics
    /// completeness") is about the cell being named at all, not about which
    /// invalidation a consumer chooses to run.
    HeapWritten {
        /// The cell whose umem boundary was resealed.
        cell: CellId,
        /// The DISTINCT `heap_map` collections the written leaves landed in, sorted
        /// ascending. A `dregg_doc` document spreads across several at once (atoms
        /// 0, edges 1, fields 2, embeds 3, prose 4, history 5 — `dregg-doc`'s
        /// `COLL_*`), so a single `collection` field could not name the write; a
        /// consumer bound to one collection filters on this.
        collections: Vec<u32>,
        /// How many leaves the resealed boundary binds (the write replaces the heap
        /// WHOLESALE, so this is the post-write leaf count, not a delta).
        key_count: usize,
    },
    /// A cell was sealed (lifecycle → Sealed; rejects effects until unsealed).
    CellSealed { cell: CellId },
    /// A sealed cell was unsealed (lifecycle → Live).
    CellUnsealed { cell: CellId },
    /// A cell was permanently retired (lifecycle → Destroyed; terminal).
    CellDestroyed { cell: CellId },
    /// Value was provably burned from a cell (supply reduced; no credit).
    Burned { cell: CellId, amount: u64 },
    /// A surface's frame was advanced by a COMMITTED `present()` (the verified
    /// compositor frame advance — [`crate::scene::VerifiedScene::present`]). This
    /// is the compositor's "damage": the region(s) a committed present wrote, and
    /// must be repainted. It fires ONLY on a present the executor's scene-authority
    /// caveat gate admitted (T1∧T2∧T3) — a refused overpaint / label-spoof /
    /// double-focus leaves NO damage (fail-closed), so the dynamics stream
    /// observes only genuine, verified frame advances.
    SurfaceDamaged {
        /// The surface owner whose frame advanced (the presenter).
        owner: CellId,
        /// The compositor cell whose `present_digest` slot the executor wrote.
        cell: CellId,
        /// The new content digest the present committed (the advanced frame).
        digest: u64,
        /// How many regions the present painted (the damage extent).
        region_count: usize,
    },
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
            WorldEvent::CellBorn {
                genesis, balance, ..
            } => {
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
            WorldEvent::TurnQueued { agent } => format!(
                "turn QUEUED (suspended): {}",
                crate::reflect::short_hex(agent.as_bytes())
            ),
            WorldEvent::BalanceFlowed { before, after, .. } => {
                let d = after - before;
                let sign = if d >= 0 { "+" } else { "" };
                format!("balance flowed {sign}{d}")
            }
            WorldEvent::CapabilityGranted { .. } => "capability granted".into(),
            WorldEvent::CapabilityRevoked { slot, .. } => {
                format!("capability revoked (slot {slot})")
            }
            WorldEvent::FieldSet { index, .. } => format!("field[{index}] set"),
            WorldEvent::CellMutated { .. } => "cell mutated".into(),
            WorldEvent::HeapWritten {
                collections,
                key_count,
                ..
            } => {
                let colls: Vec<String> = collections.iter().map(|c| c.to_string()).collect();
                format!(
                    "heap written ({key_count} leaves, collection(s) {})",
                    colls.join("/")
                )
            }
            WorldEvent::CellSealed { .. } => "cell sealed".into(),
            WorldEvent::CellUnsealed { .. } => "cell unsealed".into(),
            WorldEvent::CellDestroyed { .. } => "cell destroyed (terminal)".into(),
            WorldEvent::Burned { amount, .. } => format!("burned {amount} (supply reduced)"),
            WorldEvent::SurfaceDamaged {
                region_count,
                digest,
                ..
            } => {
                format!("surface damaged: frame → {digest} ({region_count} region(s) repainted)")
            }
            WorldEvent::EventEmitted {
                sender,
                cell,
                data_len,
                ..
            } => format!(
                "event emitted: {} → {} ({data_len}B) [notify edge]",
                crate::reflect::short_hex(sender.as_bytes()),
                crate::reflect::short_hex(cell.as_bytes()),
            ),
        }
    }

    /// The specific cell id(s) this event NAMES for M2 cache invalidation — the
    /// cells whose memoized projection a consumer drops on seeing it. This
    /// mirrors the AUTHORITATIVE variant→invalidation table (the
    /// `cockpit::construct` module's `invalidate_for`): a cell is "named"
    /// here iff some emitted event drives an `invalidate_cell` for it.
    ///
    /// Deliberate exclusions:
    /// - The `CellBorn`/`CreateCell*` **ZERO sentinel** names NO specific cell
    ///   (the real id is unknown at emit — that consumer refreshes wholesale),
    ///   so it is not counted. This is exactly why a runtime-resolved newborn
    ///   still needs its own naming event from the write-set completeness pass.
    /// - `TurnCommitted`/`TurnRejected`/`TurnQueued` carry no per-cell
    ///   invalidation (a height tick invalidates nothing on its own), so the
    ///   `agent` they mention is NOT counted as named — a cell that mutated but
    ///   is only referenced by a `TurnCommitted.agent` must still be named by a
    ///   real per-cell event or the completeness pass.
    ///
    /// Used by `World::commit_turn`'s write-set completeness pass to decide which
    /// executor-written cells still need a conservative `CellMutated` tooth.
    pub(crate) fn collect_named_cells(&self, out: &mut HashSet<CellId>) {
        match self {
            WorldEvent::CellBorn { cell, .. } => {
                // ZERO is the CreateCell / CreateCellFromFactory sentinel — the
                // real newborn id is not known here, so it names no cell.
                if *cell != CellId::ZERO {
                    out.insert(*cell);
                }
            }
            WorldEvent::CellDestroyed { cell }
            | WorldEvent::BalanceFlowed { cell, .. }
            | WorldEvent::FieldSet { cell, .. }
            | WorldEvent::CellMutated { cell }
            | WorldEvent::HeapWritten { cell, .. }
            | WorldEvent::CellSealed { cell }
            | WorldEvent::CellUnsealed { cell }
            | WorldEvent::Burned { cell, .. }
            | WorldEvent::EventEmitted { cell, .. }
            | WorldEvent::CapabilityRevoked { cell, .. } => {
                out.insert(*cell);
            }
            WorldEvent::SurfaceDamaged { cell, owner, .. } => {
                out.insert(*cell);
                out.insert(*owner);
            }
            WorldEvent::CapabilityGranted { from, to } => {
                out.insert(*from);
                out.insert(*to);
            }
            WorldEvent::TurnCommitted { .. }
            | WorldEvent::TurnRejected { .. }
            | WorldEvent::TurnQueued { .. } => {}
        }
    }
}

/// Default retained-event ceiling for a live cockpit stream (64Ki events).
///
/// At a typical [`WorldEvent`] footprint (a few `CellId`s / a `[u8; 32]` and
/// small scalars — order 100 bytes) this bounds the live log to a few MB while
/// retaining far more scrollback than any pull-render view consumes between
/// frames. The desktop pulse beats at ~250ms; a beat cannot plausibly emit 64Ki
/// events, so no live consumer ever lags past the retained window under this cap
/// (and the one that theoretically could recovers conservatively — see the pump).
pub const DEFAULT_CAP: usize = 1 << 16;

/// The append-only dynamics log with a monotonic cursor and a BOUNDED retained
/// window.
///
/// Callers see an append-only log addressed by absolute, monotonic cursors; the
/// backing store is a bounded ring that evicts the oldest events once the
/// retained window exceeds [`Self::cap()`]. See the module docs for the
/// cursor-safety contract.
pub struct Dynamics {
    /// The retained window, most-recent-last. The absolute index of `events[0]`
    /// is [`Self::base()`]; eviction drains the oldest from the front.
    events: Vec<WorldEvent>,
    /// Number of events evicted off the front — a monotonic floor that keeps
    /// outstanding ABSOLUTE cursors valid across eviction. Invariant:
    /// `cursor() == base + events.len()` == total events ever emitted.
    base: usize,
    /// Retained-event ceiling. Once `events.len()` exceeds this, [`Self::emit`]
    /// batch-evicts the oldest down to a low-water mark (amortized O(1) per emit).
    cap: usize,
}

impl Default for Dynamics {
    fn default() -> Self {
        Self::new()
    }
}

impl Dynamics {
    /// A fresh log with the [`DEFAULT_CAP`] retained ceiling.
    pub fn new() -> Self {
        Self::with_cap(DEFAULT_CAP)
    }

    /// A fresh log with an explicit retained ceiling (`cap` events). `cap` is
    /// floored at 1 so the newest event is always retained. Useful for tests and
    /// for tuning a tighter live window.
    pub fn with_cap(cap: usize) -> Self {
        Dynamics {
            events: Vec::new(),
            base: 0,
            cap: cap.max(1),
        }
    }

    /// Append an observed transition, evicting the oldest events if the retained
    /// window now exceeds [`Self::cap()`]. Cursors stay valid: eviction only
    /// advances [`Self::base()`], never renumbers a surviving event.
    pub fn emit(&mut self, event: WorldEvent) {
        self.events.push(event);
        if self.events.len() > self.cap {
            self.evict();
        }
    }

    /// Batch-evict the oldest events down to a low-water mark.
    ///
    /// The physical buffer never exceeds `cap` (the memory bound), and each
    /// eviction removes ~`cap/4` events at once — a front `drain` costs
    /// O(retained), but happens only once per ~`cap/4` emits, so eviction is
    /// amortized O(1) per [`Self::emit`]. `base` advances by exactly the number
    /// dropped, so every outstanding absolute cursor keeps resolving.
    fn evict(&mut self) {
        let evict_batch = (self.cap / 4).max(1);
        let low_water = self.cap.saturating_sub(evict_batch).max(1);
        let drop = self.events.len().saturating_sub(low_water);
        if drop == 0 {
            return;
        }
        self.events.drain(0..drop);
        self.base += drop;
    }

    /// The current cursor (== total events EVER emitted, including evicted ones).
    /// A view stores this and passes it back to [`Self::since`] next frame to get
    /// only what is new. Monotonic and stable across eviction.
    pub fn cursor(&self) -> usize {
        self.base + self.events.len()
    }

    /// The absolute index of the oldest RETAINED event — i.e. how many events have
    /// been evicted off the front. A consumer whose saved cursor is `< base()`
    /// lagged past the retained window and lost the evicted span (see
    /// [`Self::since`]); the desktop pulse pump reads this to recover
    /// conservatively rather than silently under-invalidate.
    pub fn base(&self) -> usize {
        self.base
    }

    /// All retained events at or after the absolute `cursor`.
    ///
    /// The caller's absolute cursor is clamped into the retained window
    /// `[base, cursor())`: a cursor at/after the head yields the empty slice; a
    /// cursor that fell BEHIND the evicted window (`cursor < base`) is clamped up
    /// to `base` and yields the retained tail. Never panics, never mis-slices —
    /// but a caller clamped up this way has *missed* the events in
    /// `[cursor, base)`, which were evicted.
    pub fn since(&self, cursor: usize) -> &[WorldEvent] {
        let total = self.base + self.events.len();
        let start = cursor.clamp(self.base, total) - self.base;
        &self.events[start..]
    }

    /// The retained window (most-recent-last). After eviction this is the live
    /// tail, not the whole history — bounded by [`Self::cap()`].
    pub fn all(&self) -> &[WorldEvent] {
        &self.events
    }

    /// The last `n` events, most-recent-last (drawn from the retained window).
    pub fn tail(&self, n: usize) -> &[WorldEvent] {
        let start = self.events.len().saturating_sub(n);
        &self.events[start..]
    }

    /// The retained-event ceiling (`cap`) — introspection / test hook.
    pub fn cap(&self) -> usize {
        self.cap
    }
}

// ===========================================================================
// THE WAKE EDGE — "a committed turn owes its observers a repaint".
// ===========================================================================
//
// [`Dynamics`] above is a PULL log: a view stores a cursor and re-reads
// `since(cursor)` on each frame. That is trivially correct under gpui's
// pull-render model — but it only describes what a frame SEES, never what
// causes a frame to happen. The cockpit had no cause at all: zero
// `cx.observe` on the World, and its three async pumps all self-terminate on
// a default embedded image, so ~300ms after boot it repainted only when a
// click handler happened to call `cx.notify()`. A turn committed from
// anywhere else — an MCP bridge, a resident agent, another view's button, a
// test — moved the ledger and painted nothing.
//
// The [`WakeLedger`] is the missing edge, and it is deliberately NOT a
// callback bus: an observer REGISTERS an opaque handle, `World`'s emit
// choke-point marks every registered handle PENDING, and a single consumer
// drains the pending set later and repaints. Two properties matter:
//
//   * **It carries no gpui.** The handle is a bare `u64` (the visual layer's
//     `gpui::EntityId::as_u64()`), so this stays in the gpui-free lib half
//     that `--no-default-features --features embedded-executor` builds.
//   * **It never re-enters.** `wake` runs inside `World::commit_turn`, which
//     itself runs inside `cx.listener` — taking an entity lease there is a
//     `EntityMap::lease` double-lease PANIC, and with no panic hook in the
//     gpui loop that is a process abort. So `wake` only marks + wakes a
//     `Waker`; the repaint happens later, on the foreground executor, via the
//     lease-free `App::notify`.
//
// The `Waker` is what makes this an EDGE rather than a poll: a drain task
// awaits [`WakeLedger::woken`], which is `Pending` until a commit marks
// something. No timer, so no clock advance is needed to deliver a repaint —
// which is exactly the property a timer-based implementation cannot have.

/// The shared interior of a [`WakeLedger`].
#[derive(Default)]
struct WakeInner {
    /// Observer handles currently subscribed (a live view's entity id).
    registered: BTreeSet<u64>,
    /// Observers owed a repaint — drained by the one consumer.
    pending: BTreeSet<u64>,
    /// The drain task's waker, parked while `pending` is empty.
    waker: Option<Waker>,
    /// Total wakes ever signalled (a commit that found registered observers).
    /// Introspection for tests/diagnostics — never a correctness input.
    wakes: u64,
}

/// **THE WAKE LEDGER** — the observers a committed turn owes a repaint, and
/// the `Waker` that hands the debt to the foreground loop.
///
/// Cloning shares the same ledger (an `Arc` handle), so `World` and the visual
/// layer's drain task hold the same one. See the module section above for why
/// this is a marked-set + waker rather than a callback.
#[derive(Clone, Default)]
pub struct WakeLedger {
    inner: Arc<Mutex<WakeInner>>,
}

impl WakeLedger {
    fn lock(&self) -> MutexGuard<'_, WakeInner> {
        // A panic while holding this lock must not cascade into every later
        // commit: the invariant is a marked set, and recovering the poisoned
        // guard leaves it consistent (worst case one extra repaint).
        self.inner.lock().unwrap_or_else(|e| e.into_inner())
    }

    /// Subscribe `observer` (the visual layer's `EntityId::as_u64()`). Every
    /// later commit marks it pending until it is [`unregister`](Self::unregister)ed.
    pub fn register(&self, observer: u64) {
        self.lock().registered.insert(observer);
    }

    /// Unsubscribe `observer` and drop any repaint it was still owed.
    pub fn unregister(&self, observer: u64) {
        let mut g = self.lock();
        g.registered.remove(&observer);
        g.pending.remove(&observer);
    }

    /// How many observers are subscribed.
    pub fn observer_count(&self) -> usize {
        self.lock().registered.len()
    }

    /// **Mark every registered observer as owing a repaint, and wake the
    /// drain.** Called from `World`'s dynamics emit choke-point, so a state
    /// transition cannot reach the log without also reaching this.
    ///
    /// A no-op (no allocation, no wake) when nothing is subscribed — the
    /// headless/test/`fork` worlds pay nothing.
    pub fn wake(&self) {
        let mut g = self.lock();
        if g.registered.is_empty() {
            return;
        }
        let due: Vec<u64> = g.registered.iter().copied().collect();
        g.pending.extend(due);
        g.wakes += 1;
        let waker = g.waker.take();
        // Drop the guard BEFORE waking: the woken task may poll immediately on
        // this thread (gpui's foreground executor is the same thread) and
        // re-enter `lock`.
        drop(g);
        if let Some(w) = waker {
            w.wake();
        }
    }

    /// **Take the observers owed a repaint**, clearing the debt. This is the
    /// drain: exactly one consumer should call it, and it must then notify each
    /// returned handle.
    pub fn take_pending(&self) -> Vec<u64> {
        let mut g = self.lock();
        std::mem::take(&mut g.pending).into_iter().collect()
    }

    /// How many observers are currently owed a repaint (undrained).
    pub fn pending_len(&self) -> usize {
        self.lock().pending.len()
    }

    /// How many times a commit has signalled this ledger (introspection).
    pub fn wake_count(&self) -> u64 {
        self.lock().wakes
    }

    /// A future that resolves the moment some observer is owed a repaint.
    ///
    /// This is the edge the drain task awaits. It is `Pending` — parking its
    /// waker — while the debt is empty, and `Ready` the instant [`wake`](Self::wake)
    /// marks anything. NOTE it does NOT clear the debt: the consumer drains
    /// with [`take_pending`](Self::take_pending) after awaiting.
    pub fn woken(&self) -> Woken {
        Woken {
            ledger: self.clone(),
        }
    }
}

impl std::fmt::Debug for WakeLedger {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let g = self.lock();
        f.debug_struct("WakeLedger")
            .field("registered", &g.registered.len())
            .field("pending", &g.pending.len())
            .field("wakes", &g.wakes)
            .finish()
    }
}

/// The future [`WakeLedger::woken`] returns — ready when a repaint is owed.
pub struct Woken {
    ledger: WakeLedger,
}

impl Future for Woken {
    type Output = ();

    fn poll(self: Pin<&mut Self>, cx: &mut TaskContext<'_>) -> Poll<()> {
        let mut g = self.ledger.lock();
        if g.pending.is_empty() {
            g.waker = Some(cx.waker().clone());
            Poll::Pending
        } else {
            Poll::Ready(())
        }
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

    /// Emit `n` FieldSet events tagged `0..n` by their `index` slot so tests can
    /// identify exactly which events survived eviction.
    fn emit_tagged(d: &mut Dynamics, range: std::ops::Range<usize>) {
        for i in range {
            d.emit(WorldEvent::FieldSet {
                cell: CellId::ZERO,
                index: i,
            });
        }
    }

    fn indices(events: &[WorldEvent]) -> Vec<usize> {
        events
            .iter()
            .map(|e| match e {
                WorldEvent::FieldSet { index, .. } => *index,
                other => panic!("unexpected event {other:?}"),
            })
            .collect()
    }

    #[test]
    fn eviction_caps_memory_but_keeps_the_cursor_monotonic() {
        let mut d = Dynamics::with_cap(8);
        emit_tagged(&mut d, 0..1000);
        // The retained window never exceeds the cap, so RAM is bounded regardless
        // of how many events have flowed through the log.
        assert!(
            d.all().len() <= d.cap(),
            "retained {} exceeds cap {}",
            d.all().len(),
            d.cap()
        );
        // The cursor still reports the TOTAL ever emitted, and base == the number
        // evicted, so `cursor() == base + retained` holds.
        assert_eq!(d.cursor(), 1000);
        assert_eq!(d.base(), 1000 - d.all().len());
        // The retained window is genuinely the most-recent tail.
        let idx = indices(d.all());
        assert_eq!(*idx.last().unwrap(), 999);
        assert!(idx.windows(2).all(|w| w[1] == w[0] + 1));
    }

    #[test]
    fn a_live_cursor_keeps_working_across_eviction() {
        let mut d = Dynamics::with_cap(8);
        emit_tagged(&mut d, 0..6);
        // A view saves its cursor after 6 events (nothing evicted yet).
        let c = d.cursor();
        assert_eq!(c, 6);
        // More events arrive, tripping eviction (base advances off 0).
        emit_tagged(&mut d, 6..10);
        assert!(d.base() > 0, "expected eviction to advance base");
        // The saved cursor is still INSIDE the retained window, so `since` resolves
        // it EXACTLY — the view sees precisely the four events it had not yet read,
        // in order, none dropped, none duplicated.
        assert!(
            c >= d.base(),
            "cursor must remain within the retained window"
        );
        assert_eq!(indices(d.since(c)), vec![6, 7, 8, 9]);
        // And re-reading from the fresh head yields nothing new.
        assert!(d.since(d.cursor()).is_empty());
    }

    #[test]
    fn a_stale_cursor_is_clamped_safely_to_the_retained_tail() {
        let mut d = Dynamics::with_cap(8);
        emit_tagged(&mut d, 0..20);
        assert!(d.base() > 0, "expected eviction");
        let tail = indices(d.all());
        // A cursor from before the evicted window (0, or anything `< base`) does
        // NOT panic and does NOT mis-slice — it clamps up to `base` and hands back
        // exactly the retained tail.
        assert_eq!(indices(d.since(0)), tail);
        assert_eq!(indices(d.since(d.base() - 1)), tail);
        // A cursor exactly at the floor is the same retained tail.
        assert_eq!(indices(d.since(d.base())), tail);
        // A cursor at/after the head yields the empty slice (no over-read panic).
        assert!(d.since(d.cursor()).is_empty());
        assert!(d.since(d.cursor() + 100).is_empty());
        // A cursor strictly inside the window resolves to its exact suffix.
        let mid = d.base() + 3;
        assert_eq!(d.since(mid).len(), d.cursor() - mid);
    }

    #[test]
    fn a_tiny_cap_still_retains_the_newest_event() {
        // `cap` is floored at 1, so even a degenerate cap keeps the last event and
        // never drains the buffer empty on the same emit that pushed it.
        let mut d = Dynamics::with_cap(1);
        emit_tagged(&mut d, 0..5);
        assert_eq!(indices(d.all()), vec![4]);
        assert_eq!(d.cursor(), 5);
        assert_eq!(indices(d.since(0)), vec![4]);
    }

    // --- THE WAKE EDGE ------------------------------------------------------

    #[test]
    fn an_unsubscribed_ledger_owes_nothing() {
        // A headless / test / `fork` world has no observers, so a commit's wake
        // must allocate nothing and owe nothing — the edge is free when unused.
        let w = WakeLedger::default();
        w.wake();
        w.wake();
        assert_eq!(w.pending_len(), 0);
        assert_eq!(w.wake_count(), 0, "an unsubscribed wake is not signalled");
        assert!(w.take_pending().is_empty());
    }

    #[test]
    fn a_wake_owes_every_registered_observer_until_drained() {
        let w = WakeLedger::default();
        w.register(7);
        w.register(9);
        assert_eq!(w.observer_count(), 2);
        assert_eq!(w.pending_len(), 0, "registering owes nothing by itself");
        w.wake();
        assert_eq!(w.take_pending(), vec![7, 9]);
        // The DEBT is cleared by the drain (a second drain repaints nothing) —
        // but the SUBSCRIPTION survives, so the next commit owes them again.
        assert!(w.take_pending().is_empty());
        assert_eq!(w.observer_count(), 2);
        w.wake();
        assert_eq!(w.take_pending(), vec![7, 9]);
        // Unregistering drops both the subscription and any outstanding debt.
        w.wake();
        w.unregister(7);
        assert_eq!(w.take_pending(), vec![9]);
    }

    #[test]
    fn woken_is_pending_until_a_wake_and_needs_no_timer() {
        use std::sync::atomic::{AtomicUsize, Ordering};
        use std::task::{RawWaker, RawWakerVTable, Waker};

        // A counting waker: the ONLY thing that may resolve `woken()` is a wake,
        // never the passage of time.
        static WOKE: AtomicUsize = AtomicUsize::new(0);
        fn vtable() -> &'static RawWakerVTable {
            &RawWakerVTable::new(
                |_| RawWaker::new(std::ptr::null(), vtable()),
                |_| {
                    WOKE.fetch_add(1, Ordering::SeqCst);
                },
                |_| {
                    WOKE.fetch_add(1, Ordering::SeqCst);
                },
                |_| {},
            )
        }
        WOKE.store(0, Ordering::SeqCst);
        let waker = unsafe { Waker::from_raw(RawWaker::new(std::ptr::null(), vtable())) };
        let mut tcx = TaskContext::from_waker(&waker);

        let w = WakeLedger::default();
        w.register(1);

        let mut f = Box::pin(w.woken());
        assert!(
            f.as_mut().poll(&mut tcx).is_pending(),
            "no commit yet ⟹ nothing is owed ⟹ the drain parks"
        );
        assert_eq!(WOKE.load(Ordering::SeqCst), 0);

        w.wake();
        assert_eq!(
            WOKE.load(Ordering::SeqCst),
            1,
            "the commit itself wakes the parked drain — no timer in the loop"
        );
        assert!(f.as_mut().poll(&mut tcx).is_ready());
        // `woken` reports the debt; it does NOT clear it (the drain does).
        assert_eq!(w.pending_len(), 1);
    }
}
