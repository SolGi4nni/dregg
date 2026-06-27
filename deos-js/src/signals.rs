//! The **fine-grained signal-binding model** — the dirty-set → bindings layer for the
//! deos-js view language (`docs/deos/SCRIPTING-AND-DISTRIBUTED-DOM.md §7`).
//!
//! Today an applet's `view(s)` re-renders WHOLE on any change (immediate-mode): the
//! renderer rebuilds the entire [`crate::tree::ViewNode`] tree and re-reads every
//! `bind(() => s.x)` node. That is correct but coarse — a turn touching one field
//! repaints the world.
//!
//! This module is the model half of the SolidJS-shaped fix: a `bind(() => s.x)` node
//! records WHICH `(cell, slot)` of the live ledger it reads, so that when a turn
//! commits and names the changed `(cell, slot)`, ONLY the bindings that depend on that
//! exact source re-evaluate — not the tree.
//!
//! ```text
//!   register(b0, X, 0)   register(b1, X, 1)   register(b2, Y, 0)
//!                  │              │                    │
//!   invalidate(FieldSet X,0) ─────┴── returns [b0]  (b1, b2 stay clean)
//! ```
//!
//! It is **gpui-free** and (deliberately) **starbridge-free**: it does NOT depend on
//! `starbridge-v2::dynamics::WorldEvent` (that would be a dependency inversion — the
//! cockpit consumes deos-js, not the reverse). Instead it names the changed source
//! with its OWN minimal [`SourceEvent`], which the cockpit's adapter projects a
//! real `WorldEvent` into (the `FieldSet { cell, index }` / `CapabilityRevoked { cell,
//! slot }` / `CellMutated { cell }` cases — see the integration note on
//! [`SourceEvent`]). It is pure data with a cheap, exhaustive test.
//!
//! The renderer ([`deos-view`]) consumes [`BindingRegistry::invalidate`] as its
//! dirty-node set: on each committed turn it folds the turn's `WorldEvent`s through
//! `invalidate(...)`, gets back the exact `Vec<BindingId>` whose nodes changed, and
//! re-evaluates ONLY those nodes via [`BindingRegistry::reread`] (each `BindingId`
//! maps to a `ViewNode::Bind` the renderer holds) — leaving the rest of the rendered
//! tree untouched. The gpui repaint hook itself is a later deos-view concern; this is
//! only the dirty-set the hook drives.

use std::collections::BTreeMap;

use dregg_types::CellId;

/// A model slot of a cell's state (mirrors [`crate::applet::Slot`]). A `bind` reads one
/// `(cell, slot)`; a turn writes some `(cell, slot)`s; the registry intersects them.
pub type Slot = usize;

/// The identity of one `bind(() => …)` node in a rendered view-tree. The renderer mints
/// these (e.g. monotonically as it walks the tree) and keeps a `BindingId → ViewNode`
/// map; the registry only ever traffics in the ids, never the nodes (gpui-free).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct BindingId(pub u64);

/// The change a committed turn names: cell `cell`'s slot `slot` was written. This is the
/// registry's own minimal projection of a dynamics `WorldEvent`; the cockpit adapter
/// maps the relevant real events into it:
///
///   - `WorldEvent::FieldSet { cell, index }`        → `SourceEvent { cell, slot: index }`
///   - `WorldEvent::CapabilityRevoked { cell, slot }`→ `SourceEvent { cell, slot }`
///   - `WorldEvent::CellMutated { cell }`            → one `SourceEvent` per bound slot
///        of `cell` (the generic "this cell changed" tooth invalidates ALL of its
///        bindings; use [`BindingRegistry::invalidate_cell`]).
///
/// Events that name no `(cell, slot)` source a binding can read (TurnCommitted height,
/// EventEmitted, etc.) are simply not projected — they invalidate nothing.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SourceEvent {
    /// The cell whose state changed.
    pub cell: CellId,
    /// The slot of that cell that was written.
    pub slot: Slot,
}

impl SourceEvent {
    /// A `(cell, slot)` write event.
    pub fn new(cell: CellId, slot: Slot) -> Self {
        Self { cell, slot }
    }
}

/// The reverse index: `(cell, slot) → which bindings re-read it`.
///
/// Pure data. The registry maps each source `(CellId, Slot)` to the set of
/// [`BindingId`]s that read it, so an `invalidate` is a single map lookup returning
/// exactly the dirty bindings — O(touched-slots + dirty-bindings), never O(tree).
#[derive(Debug, Default, Clone)]
pub struct BindingRegistry {
    /// `(cell, slot) → bindings reading that source`, deduped and in id-order.
    by_source: BTreeMap<(CellId, Slot), Vec<BindingId>>,
    /// `binding → its single source`, so a binding can be re-pointed or removed
    /// (a `bind` that re-reads a different slot across renders) without scanning.
    source_of: BTreeMap<BindingId, (CellId, Slot)>,
}

impl BindingRegistry {
    /// An empty registry.
    pub fn new() -> Self {
        Self::default()
    }

    /// Record that `binding` re-reads `(cell, slot)`. If `binding` was already
    /// registered (on any source), its previous source is dropped first — a `bind`
    /// node has exactly one source at a time, so re-registering re-points it.
    pub fn register(&mut self, binding: BindingId, cell: CellId, slot: Slot) {
        self.unregister(binding);
        self.by_source
            .entry((cell, slot))
            .or_default()
            .push(binding);
        // Keep each source bucket sorted+deduped so `invalidate` returns a stable,
        // duplicate-free dirty set regardless of registration order.
        let bucket = self
            .by_source
            .get_mut(&(cell, slot))
            .expect("just inserted");
        bucket.sort_unstable();
        bucket.dedup();
        self.source_of.insert(binding, (cell, slot));
    }

    /// Remove `binding` entirely (its node left the rendered tree). A no-op if absent.
    pub fn unregister(&mut self, binding: BindingId) {
        if let Some(prev) = self.source_of.remove(&binding) {
            if let Some(bucket) = self.by_source.get_mut(&prev) {
                bucket.retain(|b| *b != binding);
                if bucket.is_empty() {
                    self.by_source.remove(&prev);
                }
            }
        }
    }

    /// The fine-grained win: given a turn's `(cell, slot)` write, return EXACTLY the
    /// bindings that read that source (id-sorted, deduped) — and nothing else. A write
    /// to an unbound `(cell, slot)` returns an empty vec (the view stays clean).
    pub fn invalidate(&self, event: SourceEvent) -> Vec<BindingId> {
        self.by_source
            .get(&(event.cell, event.slot))
            .cloned()
            .unwrap_or_default()
    }

    /// Fold several events into one deduped dirty set (one committed turn typically
    /// writes several slots). The union of each event's [`invalidate`](Self::invalidate),
    /// id-sorted and duplicate-free — so a binding read by two touched slots appears once.
    pub fn invalidate_all<I: IntoIterator<Item = SourceEvent>>(&self, events: I) -> Vec<BindingId> {
        let mut out: Vec<BindingId> = events
            .into_iter()
            .flat_map(|e| self.invalidate(e))
            .collect();
        out.sort_unstable();
        out.dedup();
        out
    }

    /// The generic "this whole cell changed" tooth (for `WorldEvent::CellMutated`,
    /// where the executor wrote the cell but did not name a slot): return every binding
    /// reading ANY slot of `cell`. Conservative but complete — never under-invalidates.
    pub fn invalidate_cell(&self, cell: CellId) -> Vec<BindingId> {
        let mut out: Vec<BindingId> = self
            .by_source
            .range((cell, Slot::MIN)..=(cell, Slot::MAX))
            .flat_map(|(_, bs)| bs.iter().copied())
            .collect();
        out.sort_unstable();
        out.dedup();
        out
    }

    /// Re-read the live value of `binding`'s bound source off the world, via the read
    /// closure. Returns `None` if `binding` is not registered.
    ///
    /// `read` is supplied by the caller (the renderer / applet host) and IS the same
    /// witnessed read the JS `bind` closure made: `|cell, slot| app.get_u64(slot)` for
    /// the embedded applet, or a cap-bounded ledger read for the attached cockpit. The
    /// registry stays gpui-free and world-type-agnostic by never holding the world
    /// itself — only the `(cell, slot)` to hand back to `read`.
    pub fn reread<R: Fn(CellId, Slot) -> u64>(&self, binding: BindingId, read: R) -> Option<u64> {
        let (cell, slot) = *self.source_of.get(&binding)?;
        Some(read(cell, slot))
    }

    /// The source a binding currently reads, if registered.
    pub fn source_of(&self, binding: BindingId) -> Option<(CellId, Slot)> {
        self.source_of.get(&binding).copied()
    }

    /// How many bindings are registered (for tests / instrumentation).
    pub fn len(&self) -> usize {
        self.source_of.len()
    }

    /// Whether any binding is registered.
    pub fn is_empty(&self) -> bool {
        self.source_of.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A distinct, deterministic cell id from a single byte (test fixtures).
    fn cid(tag: u8) -> CellId {
        let mut b = [0u8; 32];
        b[0] = tag;
        CellId::from_bytes(b)
    }

    /// Three bindings on three different (cell, slot) sources; firing ONE source
    /// returns ONLY its binding — the others stay clean (the fine-grained win).
    #[test]
    fn invalidate_is_fine_grained() {
        let x = cid(1);
        let y = cid(2);
        let mut reg = BindingRegistry::new();
        reg.register(BindingId(0), x, 0);
        reg.register(BindingId(1), x, 1);
        reg.register(BindingId(2), y, 0);
        assert_eq!(reg.len(), 3);

        // A turn touching (x, 0) re-renders ONLY b0.
        assert_eq!(reg.invalidate(SourceEvent::new(x, 0)), vec![BindingId(0)]);
        // (x, 1) → only b1; (y, 0) → only b2.
        assert_eq!(reg.invalidate(SourceEvent::new(x, 1)), vec![BindingId(1)]);
        assert_eq!(reg.invalidate(SourceEvent::new(y, 0)), vec![BindingId(2)]);
    }

    /// A turn on an unbound slot (or unbound cell) returns nothing — the view is clean.
    #[test]
    fn unbound_slot_invalidates_nothing() {
        let x = cid(1);
        let z = cid(9);
        let mut reg = BindingRegistry::new();
        reg.register(BindingId(0), x, 0);
        // Unbound slot of a bound cell.
        assert!(reg.invalidate(SourceEvent::new(x, 7)).is_empty());
        // Entirely unbound cell.
        assert!(reg.invalidate(SourceEvent::new(z, 0)).is_empty());
    }

    /// Two bindings on the SAME source both invalidate; the dirty set is deduped/sorted.
    #[test]
    fn shared_source_invalidates_both_deduped() {
        let x = cid(1);
        let mut reg = BindingRegistry::new();
        // Register out of order to prove the bucket sorts.
        reg.register(BindingId(5), x, 0);
        reg.register(BindingId(2), x, 0);
        assert_eq!(
            reg.invalidate(SourceEvent::new(x, 0)),
            vec![BindingId(2), BindingId(5)]
        );
    }

    /// `invalidate_all` unions several touched slots into one deduped dirty set.
    #[test]
    fn invalidate_all_unions_and_dedupes() {
        let x = cid(1);
        let y = cid(2);
        let mut reg = BindingRegistry::new();
        reg.register(BindingId(0), x, 0);
        reg.register(BindingId(1), x, 1);
        reg.register(BindingId(2), y, 0);
        // A turn that wrote (x,0) and (y,0), plus an unbound (x,5).
        let dirty = reg.invalidate_all([
            SourceEvent::new(x, 0),
            SourceEvent::new(y, 0),
            SourceEvent::new(x, 5),
        ]);
        assert_eq!(dirty, vec![BindingId(0), BindingId(2)]);
    }

    /// The CellMutated tooth: an unslotted whole-cell change invalidates every binding
    /// on that cell (and only that cell).
    #[test]
    fn invalidate_cell_returns_all_slots_of_cell() {
        let x = cid(1);
        let y = cid(2);
        let mut reg = BindingRegistry::new();
        reg.register(BindingId(0), x, 0);
        reg.register(BindingId(1), x, 3);
        reg.register(BindingId(2), y, 0);
        assert_eq!(reg.invalidate_cell(x), vec![BindingId(0), BindingId(1)]);
        assert_eq!(reg.invalidate_cell(y), vec![BindingId(2)]);
        assert!(reg.invalidate_cell(cid(9)).is_empty());
    }

    /// `reread` hands the binding's source to the caller's witnessed read and returns
    /// the live value; an unregistered binding reads nothing.
    #[test]
    fn reread_returns_live_value() {
        let x = cid(1);
        let y = cid(2);
        let mut reg = BindingRegistry::new();
        reg.register(BindingId(0), x, 0);
        reg.register(BindingId(1), y, 4);

        // A stand-in for the live ledger: slot's value depends on (cell tag, slot).
        let world =
            |cell: CellId, slot: Slot| -> u64 { (cell.as_bytes()[0] as u64) * 100 + slot as u64 };
        assert_eq!(reg.reread(BindingId(0), world), Some(100));
        assert_eq!(reg.reread(BindingId(1), world), Some(2 * 100 + 4));
        // Unregistered binding → None.
        assert_eq!(reg.reread(BindingId(99), world), None);
    }

    /// Re-registering a binding re-points it: the old source no longer invalidates it,
    /// the new one does (a `bind` node that reads a different slot across renders).
    #[test]
    fn register_repoints_binding() {
        let x = cid(1);
        let mut reg = BindingRegistry::new();
        reg.register(BindingId(0), x, 0);
        reg.register(BindingId(0), x, 1); // re-point to slot 1
        assert_eq!(reg.len(), 1);
        assert!(reg.invalidate(SourceEvent::new(x, 0)).is_empty());
        assert_eq!(reg.invalidate(SourceEvent::new(x, 1)), vec![BindingId(0)]);
    }

    /// `unregister` removes a binding and empties its source bucket.
    #[test]
    fn unregister_removes_binding() {
        let x = cid(1);
        let mut reg = BindingRegistry::new();
        reg.register(BindingId(0), x, 0);
        reg.unregister(BindingId(0));
        assert!(reg.is_empty());
        assert!(reg.invalidate(SourceEvent::new(x, 0)).is_empty());
        assert_eq!(reg.source_of(BindingId(0)), None);
    }
}
