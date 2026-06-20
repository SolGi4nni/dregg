//! THE FRACTAL META-DEBUG (M5) — suspend the live system, inspect it as an
//! object, recursively (debug the debugger).
//!
//! `docs/deos/FIRMAMENT-REFLEXIVE-SUBSTRATE.md` §2-§3 and
//! `docs/deos/REFLEXIVE-MIGRATION.md` §4 name the keystone: make a meta-level
//! *itself a [`FocusTarget`]*, so "debug the debugger" is literally focusing the
//! inspector on its own [`MetaDebugView`] — recursion through the SAME
//! [`Registry::present`](crate::presentable::Registry::present) dispatch, no new
//! mechanism. Three pieces, all reusing the existing spine:
//!
//!   * **Suspend = halt-the-live-loop** — distinct from Snapshot (which freezes a
//!     *cursor* while the loop runs). The gate + the pending queue live on
//!     [`World`](crate::world::World) ([`World::suspend`], [`World::resume`]); this
//!     module's [`MetaDebugView`] is the INSPECTABLE object over the
//!     frozen-but-live head.
//!   * **The one-arm reflexivity** — [`MetaDebugView`] `impl`s
//!     [`Presentable`](crate::presentable::Presentable), dispatched through the new
//!     [`FocusTarget::DebugFrame`](crate::presentable::FocusTarget::DebugFrame) /
//!     `::World` / `::Cockpit` arms. Focusing the inspector on a `DebugFrame`
//!     presents that meta-level's own view — the 3-Lisp tower, grounded at the gpui
//!     loop.
//!   * **The [`MetaStack`]** — the lazily-materialized tower (`push` to climb,
//!     `pop` to descend). A `MetaLevel` is paid for only when the operator presses
//!     "suspend & inspect". The recursion terminates because the floor (the native
//!     gpui loop) is not a `World` and holds no cap.
//!
//! ## The self-cycle is a unit-delay (STRATIFIED-FIXPOINT §7.3)
//!
//! A `MetaDebugView` reads the SUSPENDED head's WITNESSED state (the frozen
//! cursor's height + the live ledger paused at it), never a within-frame fixpoint
//! of "present including self". `present` stays PURE: it observes the suspended
//! world, it never mutates it and never confers authority. A meta-frame ON a
//! meta-frame reads the lower frame's committed view — the prior-frame read that
//! breaks the cycle (the firmament supplies the strata; the self-cycle is the
//! unit-delay).
//!
//! gpui-FREE and `cargo test`-able exactly as [`crate::presentable`] /
//! [`crate::ui_snapshot`] / [`crate::view_cell`] are.

use crate::presentable::{
    FocusTarget, Presentable, PresentCtx, Presentation, PresentationBody, PresentationKind,
};
use crate::reflect::{Field, Inspectable, ObjectKind};
use crate::ui_snapshot::{Liveness, WitnessCursor};
use crate::world::World;
use dregg_cell::CellId;

// ===========================================================================
// MetaLevelId — a stable handle for a level in the reflective tower.
// ===========================================================================

/// A stable identity for a level in the [`MetaStack`]. `0` is the base (the live
/// system the first suspend captures); each `push` materializes the next id.
/// Carried by [`FocusTarget::DebugFrame`](crate::presentable::FocusTarget) so a
/// focus on a meta-level resolves through the same `present` dispatch.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct MetaLevelId(pub usize);

impl MetaLevelId {
    /// The base level — the live system the first suspend froze (the 3-Lisp ground
    /// sits BELOW this, at the native gpui loop, which is not a `MetaLevel`).
    pub const BASE: MetaLevelId = MetaLevelId(0);

    /// The id one level up (the meta-level that reflects this one).
    pub fn up(self) -> MetaLevelId {
        MetaLevelId(self.0 + 1)
    }

    /// The raw depth (0 = base).
    pub fn depth(self) -> usize {
        self.0
    }

    /// A STABLE synthetic anchor id for this level, used by
    /// [`FocusTarget::cell`](crate::presentable::FocusTarget::cell) (every focus
    /// anchors on a `CellId`, and a `DebugFrame` is not a ledger cell — so it
    /// anchors on a deterministic non-cell id derived from the level). It is NEVER
    /// in the ledger (a meta-level is a frame-object, not a cell), so it only ever
    /// serves as a memo key, never resolves a ledger lookup. The high byte tag
    /// `0xDF` ("Debug Frame") + the little-endian level keeps distinct levels
    /// distinct and keeps these out of any real cell's id space.
    pub fn debug_frame_anchor(self) -> CellId {
        let mut bytes = [0u8; 32];
        bytes[0] = 0xDF;
        bytes[24..].copy_from_slice(&(self.0 as u64).to_le_bytes());
        CellId::from_bytes(bytes)
    }
}

// ===========================================================================
// MetaDebugView — the suspended/frozen world AS AN INSPECTABLE OBJECT.
// ===========================================================================

/// THE META-DEBUG VIEW — a suspended (or frozen) world presented as a first-class
/// object. It carries the [`WitnessCursor`] the level was captured at (the frozen
/// head) and its level id; `present` projects the suspended world's state — height,
/// suspension status, the staged continuation (the pending turns), and the
/// liveness stamp — through the SAME [`Presentable`] protocol every cell uses.
///
/// "Debug the debugger" = focusing the inspector on a `MetaDebugView` whose
/// `level` is a HIGHER level: the recursion is the same `present()` call. The
/// view is pure data + a `present` that READS the world; it owns no mutable copy
/// (the suspended world is the REAL live head, paused — `world.rs`'s gate, not a
/// fork-clone).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MetaDebugView {
    /// This view's level in the tower (`BASE` = the first suspend; higher = a
    /// meta-frame ON a meta-frame).
    pub level: MetaLevelId,
    /// The witness cursor the level was captured at — the FROZEN head (the real
    /// live head, paused), not a replayed past. The liveness stamp is derived from
    /// whether this cursor still names the live head.
    pub cursor: WitnessCursor,
}

impl MetaDebugView {
    /// Capture a meta-debug view over the live (now suspended) world at `level`.
    /// The cursor is stamped at the head the loop is paused on.
    pub fn capture(world: &World, level: MetaLevelId) -> Self {
        MetaDebugView {
            level,
            cursor: WitnessCursor::at_head(world),
        }
    }

    /// The liveness stamp of this meta-view over `world` — the HONESTY the operator
    /// reads (am I looking at a paused-live head or a frozen past?). It reuses the
    /// rehydration trichotomy:
    ///   * [`Liveness::Live`] — the cursor is still the head AND the world is NOT
    ///     suspended (a meta-view over a running system at its head);
    ///   * `Live`-but-paused is reported via [`MetaDebugView::is_paused_live`]
    ///     alongside this — a suspended head is "the live head, frozen", which we
    ///     surface as `Live` (it IS the current state, re-derived from no replay)
    ///     with the suspension flag carried separately (Seam 4);
    ///   * [`Liveness::ReplayedDeterministic`] — the cursor fell into the past (the
    ///     world advanced beyond where this level was captured).
    pub fn liveness(&self, world: &World) -> Liveness {
        if self.cursor.is_live_head(world) {
            Liveness::Live
        } else {
            Liveness::ReplayedDeterministic
        }
    }

    /// `true` iff this meta-view looks at a PAUSED-LIVE head: the cursor is the live
    /// head AND the world is suspended. This is the distinct register Seam 4 demands
    /// — "paused live" is neither Snapshot's `ReplayedDeterministic` nor a plain
    /// `Live`; the operator must know the head is HALTED, not merely current.
    pub fn is_paused_live(&self, world: &World) -> bool {
        self.cursor.is_live_head(world) && world.is_suspended()
    }
}

impl Presentable for MetaDebugView {
    fn object_kind(&self) -> ObjectKind {
        // A meta-debug frame is an image-shaped object (a whole world-as-an-object),
        // not a single cell.
        ObjectKind::Image
    }

    /// PURE: project the suspended world AS AN OBJECT. Reads the frozen head's
    /// state (height, receipts, suspension, the staged continuation) — it does NOT
    /// mutate the world and confers no authority. This is the read-reflection a
    /// `ReadState` mirror over `FocusTarget::World` yields.
    fn present(&self, ctx: &PresentCtx) -> Vec<Presentation> {
        let world = ctx.world;
        let liveness = self.liveness(world);
        let paused_live = self.is_paused_live(world);
        let pending = world.pending_len();

        // (1) RawFields — the MANDATORY floor: the suspended world's frame state.
        let mut fields: Vec<Field> = vec![
            Field::count("meta_level", self.level.depth() as u64),
            Field::count("frozen_height", self.cursor.height),
            Field::count("live_height", world.height()),
            Field::boolean("suspended", world.is_suspended()),
            Field::boolean("paused_live (head halted, not a past)", paused_live),
            Field::count("pending_turns (the continuation)", pending as u64),
            Field::text("liveness", liveness.slug()),
        ];
        match self.cursor.receipt_head {
            Some(h) => fields.push(Field::id("frozen_receipt_head", h)),
            None => fields.push(Field::text("frozen_receipt_head", "(genesis)".to_string())),
        }
        let insp = Inspectable {
            kind: ObjectKind::Image,
            title: format!("MetaDebugFrame · level {}", self.level.depth()),
            subtitle: format!(
                "{} · frozen@h{} · {} pending",
                if paused_live { "PAUSED-LIVE" } else { liveness.slug() },
                self.cursor.height,
                pending
            ),
            fields,
        };
        let mut out = vec![Presentation {
            kind: PresentationKind::RawFields,
            label: "Suspended Frame".to_string(),
            search_text: PresentationBody::Fields(insp.clone()).search_text(),
            body: PresentationBody::Fields(insp),
        }];

        // (2) Provenance — the staged CONTINUATION as a timeline: the pending turns,
        //     in arrival order (the partial turn whose holes are the not-yet-committed
        //     turns, §3.3). Read off the real pending queue, never a parallel model.
        let events: Vec<crate::presentable::TimelineEvent> = world
            .pending_turns()
            .enumerate()
            .map(|(i, t)| crate::presentable::TimelineEvent {
                at: i as u64,
                label: format!(
                    "queued turn {} · agent {} · {} root action(s)",
                    i,
                    crate::reflect::short_hex(t.agent.as_bytes()),
                    t.call_forest.roots.len()
                ),
                hash: None,
            })
            .collect();
        out.push(Presentation {
            kind: PresentationKind::Provenance,
            label: "Staged Continuation".to_string(),
            search_text: format!("continuation {pending} pending turns"),
            body: PresentationBody::Timeline(crate::presentable::TimelineView { events }),
        });

        out
    }
}

// ===========================================================================
// MetaStack — the lazily-materialized reflective tower (3-Lisp), push/pop.
// ===========================================================================

/// THE META-STACK — the reflective tower, lazily materialized. `levels[k]` is the
/// meta-debug view at depth `k`; `push` climbs (suspend & inspect one level
/// higher), `pop` descends. A level is paid for only when it exists (no infinite
/// materialization); the recursion grounds BELOW `levels[0]` at the native gpui
/// loop, which is not a `MetaLevel` and holds no cap (the 3-Lisp floor).
///
/// This replaces the cockpit's flat `Tab` sibling-panels with a push/pop stack
/// (`REFLEXIVE-MIGRATION.md` §4.2): the tower is exactly as tall as you climbed.
#[derive(Clone, Debug, Default)]
pub struct MetaStack {
    levels: Vec<MetaDebugView>,
}

impl MetaStack {
    /// An empty tower (no level materialized — the operator has not suspended yet).
    pub fn new() -> Self {
        MetaStack { levels: Vec::new() }
    }

    /// How tall the tower is (0 = nothing suspended; the live system runs).
    pub fn depth(&self) -> usize {
        self.levels.len()
    }

    /// `true` iff no meta-level is materialized (the base, running system).
    pub fn is_empty(&self) -> bool {
        self.levels.is_empty()
    }

    /// **SUSPEND & INSPECT** — push a new meta-level capturing the current frozen
    /// head. The first push materializes `BASE`; each subsequent push materializes
    /// the next id (the meta-frame ON the meta-frame — debug the debugger). Returns
    /// the new level's [`FocusTarget::DebugFrame`] focus, ready to hand to the
    /// inspector.
    ///
    /// This is the SUBSTRATE move; the caller is responsible for `world.suspend()`
    /// (the halt) — the stack is the reflective tower over a (suspended) world, the
    /// world owns the gate. Keeping them separate is the §2.3 invariant: the
    /// authority structure (who reflects whom) is independent of the suspend gate.
    pub fn push(&mut self, world: &World) -> FocusTarget {
        let level = MetaLevelId(self.levels.len());
        let view = MetaDebugView::capture(world, level);
        self.levels.push(view);
        FocusTarget::DebugFrame(level)
    }

    /// **DESCEND** — pop the top meta-level (close the innermost debugger), yielding
    /// it. `None` iff the tower is already at the floor (the gpui loop — you cannot
    /// pop below the base).
    pub fn pop(&mut self) -> Option<MetaDebugView> {
        self.levels.pop()
    }

    /// The meta-debug view at `level`, if materialized — the resolution
    /// [`FocusTarget::DebugFrame`] routes through (the registry holds the stack and
    /// looks the level up here).
    pub fn get(&self, level: MetaLevelId) -> Option<&MetaDebugView> {
        self.levels.get(level.depth())
    }

    /// The top (innermost) meta-level — the one the operator is currently debugging.
    pub fn top(&self) -> Option<&MetaDebugView> {
        self.levels.last()
    }
}

// ===========================================================================
// TESTS — the model, proven gpui-free.
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::presentable::Registry;
    use crate::world::{transfer, ResumeMode, World};
    use dregg_cell::CellId;

    /// A two-cell world: a treasury (1_000) and a sink (0), no turns yet.
    fn two_cell_world() -> (World, CellId, CellId) {
        let mut w = World::new();
        let treasury = w.genesis_cell(0x11, 1_000);
        let sink = w.genesis_cell(0x22, 0);
        (w, treasury, sink)
    }

    // ── SUSPEND HALTS: a submitted turn Queues, the head is frozen ───────────

    #[test]
    fn suspend_halts_the_loop_a_turn_queues_and_the_head_freezes() {
        let (mut w, treasury, sink) = two_cell_world();
        let h0 = w.height();
        let r0 = w.receipts().len();

        w.suspend();
        assert!(w.is_suspended(), "the loop is halted");

        // A submitted turn QUEUES — it does NOT commit, and the head is frozen.
        let turn = w.turn(treasury, vec![transfer(treasury, sink, 250)]);
        let outcome = w.commit_turn(turn);
        assert!(outcome.is_queued(), "a turn submitted while suspended queues, got otherwise");
        assert_eq!(w.height(), h0, "the head is FROZEN — no height advance");
        assert_eq!(w.receipts().len(), r0, "no receipt landed — the executor never ran");
        assert_eq!(w.pending_len(), 1, "the turn is staged in the pending queue");

        // The treasury balance is untouched (the real live head, paused).
        let bal = w.ledger().get(&treasury).unwrap().state.balance();
        assert_eq!(bal, 1_000, "the frozen head's balance is the pre-suspend value");

        // A TurnQueued event was emitted (dynamics completeness under suspension).
        assert!(
            w.dynamics()
                .all()
                .iter()
                .any(|e| matches!(e, crate::dynamics::WorldEvent::TurnQueued { .. })),
            "a TurnQueued event keeps the dynamics stream complete"
        );
    }

    // ── RESUME DRAINS: the queued turn commits ──────────────────────────────

    #[test]
    fn resume_drains_the_queue_and_the_turn_commits() {
        let (mut w, treasury, sink) = two_cell_world();
        w.suspend();
        let turn = w.turn(treasury, vec![transfer(treasury, sink, 250)]);
        assert!(w.commit_turn(turn).is_queued());

        let h0 = w.height();
        let outcomes = w.resume_drain();
        assert!(!w.is_suspended(), "the loop is running again after resume");
        assert_eq!(w.pending_len(), 0, "the queue is drained");
        assert_eq!(outcomes.len(), 1, "one staged turn committed on resume");
        assert!(outcomes[0].is_committed(), "the drained turn committed for real");
        assert_eq!(w.height(), h0 + 1, "the head advanced by the drained turn");

        // The transfer actually moved value (the real executor ran on resume).
        assert_eq!(w.ledger().get(&treasury).unwrap().state.balance(), 750);
        assert_eq!(w.ledger().get(&sink).unwrap().state.balance(), 250);
    }

    // ── RESUME(DRAIN) preserves arrival order across several queued turns ────

    #[test]
    fn resume_drain_applies_the_queue_in_arrival_order() {
        let (mut w, treasury, sink) = two_cell_world();
        w.suspend();
        // Three transfers staged in order.
        for amt in [100u64, 200, 50] {
            let t = w.turn(treasury, vec![transfer(treasury, sink, amt)]);
            assert!(w.commit_turn(t).is_queued());
        }
        assert_eq!(w.pending_len(), 3);

        let outcomes = w.resume_drain();
        assert_eq!(outcomes.len(), 3);
        assert!(outcomes.iter().all(|o| o.is_committed()), "all three drained committed");
        assert_eq!(w.height(), 3, "three turns advanced the head");
        // 1000 − 100 − 200 − 50 = 650.
        assert_eq!(w.ledger().get(&treasury).unwrap().state.balance(), 650);
    }

    // ── RESUME(MODIFIED): an edited continuation runs instead of the queue ───

    #[test]
    fn resume_modified_runs_the_edited_continuation_through_the_gate() {
        let (mut w, treasury, sink) = two_cell_world();
        w.suspend();
        // Stage a transfer of 250.
        let staged = w.turn(treasury, vec![transfer(treasury, sink, 250)]);
        assert!(w.commit_turn(staged).is_queued());
        assert_eq!(w.pending_len(), 1);

        // The operator EDITS the continuation: drop the 250 transfer, run a 10 one
        // instead. The staged queue is discarded; the edit runs through the full gate.
        let edited = w.turn(treasury, vec![transfer(treasury, sink, 10)]);
        let outcomes = w.resume(ResumeMode::Modified(vec![edited]));
        assert!(!w.is_suspended());
        assert_eq!(outcomes.len(), 1);
        assert!(outcomes[0].is_committed(), "the edited turn committed");
        // Only 10 moved — the edit replaced the staged 250 (the gate ran the edit).
        assert_eq!(w.ledger().get(&treasury).unwrap().state.balance(), 990);
        assert_eq!(w.ledger().get(&sink).unwrap().state.balance(), 10);
    }

    // ── A modified continuation still passes the per-turn invariant (gate) ────

    #[test]
    fn a_modified_continuation_turn_still_passes_the_executor_gate() {
        // The edit is to WHICH turns run, never to the per-turn invariant: an
        // over-draw transfer in a modified batch is REJECTED by the real executor,
        // proving the gate ran (a modified continuation cannot smuggle bad work).
        let (mut w, treasury, sink) = two_cell_world();
        w.suspend();
        // Edit: attempt to move MORE than the treasury holds.
        let bad = w.turn(treasury, vec![transfer(treasury, sink, 10_000)]);
        let outcomes = w.resume(ResumeMode::Modified(vec![bad]));
        assert_eq!(outcomes.len(), 1);
        assert!(
            matches!(outcomes[0], crate::world::CommitOutcome::Rejected { .. }),
            "an over-draw in the modified continuation is refused by the executor gate"
        );
        // The head is unmoved (the refusal changed nothing).
        assert_eq!(w.ledger().get(&treasury).unwrap().state.balance(), 1_000);
    }

    // ── A DebugFrame focus yields a real presentation of the suspended world ──

    #[test]
    fn a_debug_frame_focus_presents_the_suspended_world() {
        // INSPECT-THE-SUSPENDED-SYSTEM: suspend, push a meta-level, and focus the
        // inspector on the DebugFrame — it yields a real presentation set describing
        // the frozen head + the staged continuation.
        let (mut w, treasury, sink) = two_cell_world();
        w.suspend();
        let turn = w.turn(treasury, vec![transfer(treasury, sink, 250)]);
        assert!(w.commit_turn(turn).is_queued());

        let mut stack = MetaStack::new();
        let focus = stack.push(&w);
        assert_eq!(focus, FocusTarget::DebugFrame(MetaLevelId::BASE));

        // The view presents the suspended world.
        let view = stack.get(MetaLevelId::BASE).expect("the level is materialized");
        let ctx = PresentCtx::new(&w, treasury);
        let set = view.present(&ctx);
        assert!(!set.is_empty(), "the meta-view yields a real presentation set");

        let raw = set
            .iter()
            .find(|p| p.kind == PresentationKind::RawFields)
            .expect("the RawFields floor is present");
        match &raw.body {
            PresentationBody::Fields(i) => {
                assert!(i.fields.iter().any(|f| f.key == "suspended"));
                assert!(
                    i.fields.iter().any(|f| f.key == "pending_turns (the continuation)"),
                    "the staged continuation count is presented"
                );
            }
            other => panic!("the meta-view RawFields must carry a Fields body, got {other:?}"),
        }
        // It honestly reads PAUSED-LIVE (the head is halted, not a frozen past).
        assert!(view.is_paused_live(&w), "the meta-view looks at a paused-live head");

        // The staged continuation appears as a Provenance timeline (one queued turn).
        let prov = set
            .iter()
            .find(|p| p.kind == PresentationKind::Provenance)
            .expect("the continuation timeline is present");
        match &prov.body {
            PresentationBody::Timeline(t) => {
                assert_eq!(t.events.len(), 1, "the one queued turn appears in the continuation");
            }
            other => panic!("the continuation must be a Timeline, got {other:?}"),
        }
    }

    // ── The DebugFrame resolves through the SAME Registry::present dispatch ───

    #[test]
    fn the_registry_resolves_a_debug_frame_through_the_meta_stack() {
        // THE ONE-ARM EXTENSION: FocusTarget::DebugFrame resolves through the SAME
        // Registry::present dispatch (the registry consults the MetaStack). Focusing
        // the inspector on a meta-level goes through the identical pure projection a
        // cell does.
        let (mut w, _treasury, _sink) = two_cell_world();
        w.suspend();
        let mut stack = MetaStack::new();
        let focus = stack.push(&w);

        let reg = Registry::with_meta_stack(&w, &stack);
        let viewer = _treasury;
        let set = reg
            .present(focus, viewer)
            .expect("the DebugFrame focus resolves through the registry");
        assert!(set.iter().any(|p| p.kind == PresentationKind::RawFields));
        assert_eq!(reg.object_kind(focus), ObjectKind::Image);
        // The focus anchors on a stable id (the level), not a ledger cell.
        assert_eq!(focus.cell(), MetaLevelId::BASE.debug_frame_anchor());
    }

    // ── THE FRACTAL: a meta-frame ON a meta-frame nests (the MetaStack) ──────

    #[test]
    fn a_meta_frame_on_a_meta_frame_nests_the_tower() {
        // DEBUG THE DEBUGGER: push a level, then push ANOTHER — the tower climbs.
        // The recursion materializes lazily (a level is paid for only when pushed),
        // and grounds at the floor (you cannot pop below the base / gpui loop).
        let (mut w, treasury, sink) = two_cell_world();

        let mut stack = MetaStack::new();
        assert!(stack.is_empty(), "nothing suspended yet");

        // Level 0: suspend the live system, inspect it.
        w.suspend();
        let f0 = stack.push(&w);
        assert_eq!(f0, FocusTarget::DebugFrame(MetaLevelId(0)));
        assert_eq!(stack.depth(), 1);

        // Stage a turn into the suspended level-0 world (the continuation).
        let turn = w.turn(treasury, vec![transfer(treasury, sink, 5)]);
        assert!(w.commit_turn(turn).is_queued());

        // Level 1: DEBUG THE DEBUGGER — focus the inspector on the meta-level's own
        // view by pushing a frame ON the frame. Same present() dispatch.
        let f1 = stack.push(&w);
        assert_eq!(f1, FocusTarget::DebugFrame(MetaLevelId(1)), "the tower climbed one level");
        assert_eq!(stack.depth(), 2, "the MetaStack nested");

        // Both levels are materialized and each presents a real frame.
        let reg = Registry::with_meta_stack(&w, &stack);
        for f in [f0, f1] {
            let set = reg.present(f, treasury).expect("each materialized level resolves");
            assert!(set.iter().any(|p| p.kind == PresentationKind::RawFields));
        }
        // The top is the innermost debugger (level 1).
        assert_eq!(stack.top().unwrap().level, MetaLevelId(1));

        // DESCEND: pop level 1 (close the inner debugger); the floor stops the pop.
        assert_eq!(stack.pop().unwrap().level, MetaLevelId(1));
        assert_eq!(stack.depth(), 1);
        assert_eq!(stack.pop().unwrap().level, MetaLevelId(0));
        assert!(stack.is_empty(), "popped back to the floor (the gpui loop, not a level)");
        assert!(stack.pop().is_none(), "you cannot pop below the base — the 3-Lisp ground");
    }

    // ── A dangling DebugFrame (unmaterialized level) is surfaced honestly ────

    #[test]
    fn a_dangling_debug_frame_focus_is_surfaced_honestly() {
        let (w, _t, _s) = two_cell_world();
        let stack = MetaStack::new(); // empty — no level materialized
        let reg = Registry::with_meta_stack(&w, &stack);
        // A focus on a level that was never pushed resolves to None (never faked).
        assert!(reg.present(FocusTarget::DebugFrame(MetaLevelId(7)), _t).is_none());
    }

    // ── liveness: a meta-view falls to Replayed once the world advances past it ─

    #[test]
    fn a_meta_view_liveness_falls_to_replayed_after_the_head_advances() {
        let (mut w, treasury, sink) = two_cell_world();
        // Capture a meta-view at the head while NOT suspended (a live meta-view).
        let view = MetaDebugView::capture(&w, MetaLevelId::BASE);
        assert_eq!(view.liveness(&w), Liveness::Live, "at the head, the meta-view is live");
        assert!(!view.is_paused_live(&w), "not suspended → not paused-live");

        // The world advances past the captured head.
        let turn = w.turn(treasury, vec![transfer(treasury, sink, 1)]);
        assert!(w.commit_turn(turn).is_committed());

        // The meta-view's cursor is now in the past → ReplayedDeterministic.
        assert_eq!(
            view.liveness(&w),
            Liveness::ReplayedDeterministic,
            "after the head advances, the captured meta-view re-derives from the past"
        );
    }
}
