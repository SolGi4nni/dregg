//! THE TEMPORAL COCKPIT model — the gpui-free brain behind the "⏳ TIME" tab.
//!
//! The headline livability surface of deos: time-travel + suspend + fractal
//! meta-debug, as ONE control panel. This module is the pure projection the
//! cockpit's TIME tab renders — exactly the `reflect::Inspectable` /
//! [`crate::ui_snapshot`] / [`crate::meta_debug`] pattern: a gpui-free model the
//! view paints, so it is `cargo test`-able without a window.
//!
//! It REUSES the real models, never a parallel one:
//!
//!   * the REWIND SCRUBBER reads [`World::recorded_turns`] — the live world's own
//!     canonical [`crate::replay::History`] — and lands each tick by ROOT-VERIFIED
//!     [`History::replay_to`](crate::replay::History::replay_to). The
//!     [`Liveness`](crate::ui_snapshot::Liveness) badge is the rehydration model's
//!     honest trichotomy: [`Liveness::Live`] at the head, [`Liveness::ReplayedDeterministic`]
//!     in the past (the camera re-ran from the witnessed log).
//!   * the SUSPEND readout reads the M5 gate on [`World`] directly
//!     ([`World::is_suspended`], [`World::pending_turns`]) — the head is FROZEN and
//!     the staged continuation is the real pending queue.
//!   * the METASTACK breadcrumb reads [`crate::meta_debug::MetaStack`] — the
//!     lazily-materialized reflective tower (BASE → meta¹ → meta² …).
//!
//! The cockpit owns the mutable state (the scrubber cursor, the `MetaStack`) and
//! drives the real `World` gate (`suspend`/`resume`); this module turns a snapshot
//! of that state into a model. `present` stays pure: building a model NEVER mutates
//! the world.

use crate::meta_debug::{MetaLevelId, MetaStack};
use crate::replay::{History, ScrubSource, StateDiff};
use crate::ui_snapshot::Liveness;
use crate::world::World;
use dregg_cell::CellId;

// ===========================================================================
// The scrubber-tick model — one landing point on the rewind timeline.
// ===========================================================================

/// One tick on the rewind scrubber — a landing point in history (`step` in
/// `0..=history.len()`). The scrubber ticks ARE the turns (plus the genesis
/// installs and the empty-pre-genesis root). Dragging the scrubber to a tick
/// re-derives the focused views at that past point.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ScrubTick {
    /// The history step this tick lands on (`0` = empty pre-genesis ledger).
    pub step: usize,
    /// The canonical [`dregg_cell::Ledger::root`] recorded at this landing (the
    /// root tooth replay verifies against).
    pub root: [u8; 32],
    /// A short human label for the tick — the receipt/turn (or genesis) here.
    pub label: String,
    /// `true` iff this tick is a committed TURN (vs a genesis install or the
    /// empty root) — the scrubber draws turns as the "real" ticks.
    pub is_turn: bool,
    /// Whether the turn AT this tick can be UN-TURNED (the reversibility organ's
    /// verdict, `dregg_turn::Turn::is_reversible` over the pre-state): `Some(true)`
    /// = a reversible step (clean/contextual — rewinding past it restores state
    /// modulo the monotone nonce); `Some(false)` = a COMMITTED boundary (a spend /
    /// burn / revoke / terminal lifecycle — the scrubber cannot un-turn past it);
    /// `None` for genesis / the empty root (nothing to invert). This is the
    /// per-step reversibility the rewind UI draws so you SEE where the un-turn
    /// frontier is, not just where the cursor sits.
    pub reversible: Option<bool>,
}

// ===========================================================================
// The whole TIME-tab model.
// ===========================================================================

/// THE TEMPORAL COCKPIT MODEL — the full state the "⏳ TIME" tab paints, built
/// fresh each frame from the live [`World`] + the cockpit's scrubber cursor + the
/// [`MetaStack`]. Every field is RE-DERIVED from the real models (the verified
/// history, the suspend gate, the reflective tower); nothing is a parallel cache.
#[derive(Clone, Debug)]
pub struct TimeCockpitModel {
    // --- the REWIND SCRUBBER ------------------------------------------------
    /// Every landing point on the timeline (genesis → head), in order.
    pub ticks: Vec<ScrubTick>,
    /// Where the scrubber cursor sits (a step in `0..=history.len()`).
    pub cursor: usize,
    /// The head step (the live present — `history.len()`).
    pub head: usize,
    /// The verified reconstruction AT the cursor: the cells (id, balance, caps),
    /// sorted by id, re-derived by root-verified replay. Empty iff the replay
    /// failed (surfaced via `cursor_verified = false`, never faked).
    pub cursor_cells: Vec<(CellId, i64, usize)>,
    /// `true` iff the cursor's reconstruction root-verified against the recorded
    /// tooth (the anti-substitution tooth — `false` is a surfaced bug, not a panic).
    pub cursor_verified: bool,
    /// The canonical root at the cursor.
    pub cursor_root: [u8; 32],
    /// `true` iff the cursor's image was restored via the UMEM BOUNDARY (the O(1)
    /// `reify_ledger` inverse fold — the umem time-travel revolution), `false` iff
    /// the scrub fell back to genesis replay for a cell outside the faithful class.
    pub cursor_via_umem: bool,
    /// The honest liveness of the cursor view: [`Liveness::Live`] at the head,
    /// [`Liveness::ReplayedDeterministic`] in the past (the image rewound, the
    /// camera re-ran from the witnessed log).
    pub liveness: Liveness,
    /// The diff from the previous step to the cursor (what the cursor's turn did),
    /// `None` at genesis (step 0).
    pub diff_from_prev: Option<StateDiff>,

    // --- the ⏸ SUSPEND gate (M5) -------------------------------------------
    /// `true` iff the live loop is HALTED (the head is frozen). Distinct from the
    /// scrubber being in the past: suspend stops the REAL loop.
    pub suspended: bool,
    /// The live (head) turn-height — what the running loop is at.
    pub live_height: u64,
    /// The staged continuation — the pending turns queued while suspended, in
    /// arrival order (one label per queued turn). Empty unless suspended-with-work.
    pub pending: Vec<String>,

    // --- the METASTACK navigator (the fractal meta-debug) -------------------
    /// The reflective tower as a breadcrumb: BASE → meta¹ → meta² … . Empty iff
    /// no meta-level is materialized (the live system runs, un-reflected).
    pub metastack: Vec<MetaCrumb>,
}

/// One crumb in the METASTACK breadcrumb — a materialized meta-level.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MetaCrumb {
    /// The level depth (`0` = BASE, the first suspend; higher = a meta-frame on a
    /// meta-frame — "debug the debugger").
    pub level: usize,
    /// The frozen head-height this level was captured at.
    pub frozen_height: u64,
    /// `true` iff this is the innermost (top) level — the one the operator is
    /// currently debugging (the focus of "debug the debugger").
    pub is_top: bool,
}

impl TimeCockpitModel {
    /// Build the model for `world` with the scrubber at `cursor`, over the cockpit's
    /// `stack`. Performs the VERIFIED replay at the cursor (and the prev-step diff);
    /// a replay error is surfaced as an unverified cursor, never a panic. PURE — it
    /// never mutates the world.
    pub fn build(world: &World, cursor: usize, stack: &MetaStack) -> Self {
        let history: &History = world.recorded_turns();
        let head = history.len();
        let cursor = cursor.min(head);

        // The scrubber ticks — every landing (the empty root + each genesis/turn).
        // Reversibility is classified for ALL steps in ONE forward pass (O(N)); the
        // old per-tick `replay_to(step-1)` was O(N²) and — rebuilt every frame on the
        // paint path — is what hung the TIME tab as the history grew.
        let revs = history.reversibility_classification();
        let mut ticks: Vec<ScrubTick> = Vec::with_capacity(head + 1);
        for cp in history.checkpoints() {
            let (label, is_turn, reversible) = if cp.step == 0 {
                ("genesis (empty image)".to_string(), false, None)
            } else {
                let step = &history.steps()[cp.step - 1];
                match step {
                    crate::replay::RecordedStep::Committed { .. } => {
                        (step.label(), true, revs.get(cp.step - 1).copied().flatten())
                    }
                    crate::replay::RecordedStep::Genesis { .. } => (step.label(), false, None),
                }
            };
            ticks.push(ScrubTick {
                step: cp.step,
                root: cp.root,
                label,
                is_turn,
                reversible,
            });
        }

        // The verified reconstruction at the cursor — restored via the UMEM BOUNDARY
        // (`History::reify_to`: the O(1) `reify_ledger` inverse fold, root-verified),
        // falling back to genesis replay only for a cell outside the faithful class.
        let (cursor_cells, cursor_verified, cursor_via_umem) = match history.reify_to(cursor) {
            Ok((ledger, source)) => {
                let mut cells: Vec<(CellId, i64, usize)> = ledger
                    .iter()
                    .map(|(id, c)| (*id, c.state.balance(), c.capabilities.len()))
                    .collect();
                cells.sort_by(|a, b| a.0.as_bytes().cmp(b.0.as_bytes()));
                (cells, true, source == ScrubSource::UmemBoundary)
            }
            Err(_) => (Vec::new(), false, false),
        };
        let cursor_root = history.root_at(cursor);

        // The liveness badge: Live iff the cursor names the head (the live present);
        // ReplayedDeterministic once it falls into the past (the image rewound).
        let liveness = if cursor == head {
            Liveness::Live
        } else {
            Liveness::ReplayedDeterministic
        };

        // The diff from the previous step — what the cursor's turn did.
        let diff_from_prev = if cursor > 0 {
            history.diff(cursor - 1, cursor).ok()
        } else {
            None
        };

        // The suspend gate (M5) — read straight off the world.
        let suspended = world.is_suspended();
        let live_height = world.height();
        let pending: Vec<String> = world
            .pending_turns()
            .enumerate()
            .map(|(i, t)| {
                format!(
                    "queued #{i} · agent {} · {} root action(s)",
                    crate::reflect::short_hex(t.agent.as_bytes()),
                    t.call_forest.roots.len()
                )
            })
            .collect();

        // The metastack breadcrumb — the reflective tower (BASE → meta¹ → …).
        let depth = stack.depth();
        let metastack: Vec<MetaCrumb> = (0..depth)
            .filter_map(|d| {
                let view = stack.get(MetaLevelId(d))?;
                Some(MetaCrumb {
                    level: d,
                    frozen_height: view.cursor.height,
                    is_top: d + 1 == depth,
                })
            })
            .collect();

        TimeCockpitModel {
            ticks,
            cursor,
            head,
            cursor_cells,
            cursor_verified,
            cursor_root,
            cursor_via_umem,
            liveness,
            diff_from_prev,
            suspended,
            live_height,
            pending,
            metastack,
        }
    }

    /// `true` iff the scrubber cursor is at the live head (the present) — the badge
    /// reads `Live`, the image is the running state.
    pub fn at_head(&self) -> bool {
        self.cursor == self.head
    }

    /// The UN-TURN FLOOR: the highest step that is a COMMITTED boundary (a turn the
    /// reversibility organ classifies irreversible — a spend / burn / revoke /
    /// terminal). `undo_to` reverses a contiguous suffix most-recent-first, so it
    /// can rewind the image down to (but NOT past) this floor; `0` iff the whole
    /// history is reversible. The headline "you can rewind to k{floor}, not past the
    /// committed move there."
    pub fn undo_floor(&self) -> usize {
        self.ticks
            .iter()
            .filter(|t| t.reversible == Some(false))
            .map(|t| t.step)
            .max()
            .unwrap_or(0)
    }

    /// A human badge for the un-turn floor: where the rewind frontier is, in
    /// reversibility terms (the cockpit's TIME tab draws this above the scrubber).
    pub fn undo_floor_badge(&self) -> String {
        let floor = self.undo_floor();
        if floor == 0 {
            "↺ fully reversible — the whole image can be un-turned to genesis".to_string()
        } else {
            format!(
                "⊘ un-turn floor at k{floor} — a committed move (spend/burn/revoke/terminal) \
                 there cannot be reversed; the image rewinds to k{floor}, not past it"
            )
        }
    }

    /// The human badge text for the cursor's liveness (the operator reads "am I
    /// looking at the live present, or a re-derived past?").
    pub fn liveness_badge(&self) -> String {
        match self.liveness {
            Liveness::Live => "● LIVE · at the head (the present)".to_string(),
            Liveness::ReplayedDeterministic => format!(
                "⟲ REPLAYED · re-derived @k{} (root-verified from the log)",
                self.cursor
            ),
            Liveness::ReconstructedApproximate => {
                "≈ APPROXIMATE · the log does not reach this point".to_string()
            }
        }
    }
}

// ===========================================================================
// TESTS — gpui-free, exactly as replay.rs / ui_snapshot.rs / meta_debug.rs are.
// `cargo test --features embedded-executor`
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::world::{ResumeMode, World, transfer};

    /// A small world: a treasury (1_000) and a sink (0), three committed turns.
    fn fixture() -> (World, CellId, CellId) {
        let mut w = World::new();
        let treasury = w.genesis_cell(0x11, 1_000);
        let sink = w.genesis_cell(0x22, 0);
        for amt in [100u64, 200, 50] {
            let t = w.turn(treasury, vec![transfer(treasury, sink, amt)]);
            assert!(w.commit_turn(t).is_committed());
        }
        (w, treasury, sink)
    }

    // ── the SCRUBBER classifies per-step REVERSIBILITY (the un-turn frontier) ─

    #[test]
    fn the_scrubber_classifies_per_step_reversibility() {
        use crate::world::burn;
        let mut w = World::new();
        let treasury = w.genesis_cell(0x11, 1_000);
        let sink = w.genesis_cell(0x22, 0);
        // A reversible transfer, then an IRREVERSIBLE burn (a committed boundary).
        let t1 = w.turn(treasury, vec![transfer(treasury, sink, 10)]);
        assert!(w.commit_turn(t1).is_committed());
        let t2 = w.turn(treasury, vec![burn(treasury, 5)]);
        assert!(w.commit_turn(t2).is_committed(), "the burn commits");

        let stack = MetaStack::new();
        let m = TimeCockpitModel::build(&w, w.recorded_turns().len(), &stack);
        let turns: Vec<_> = m.ticks.iter().filter(|t| t.is_turn).collect();
        assert_eq!(turns.len(), 2, "two committed turns");
        // The REAL Turn::is_reversible verdict, per step — not a transcription.
        assert_eq!(turns[0].reversible, Some(true), "transfer reverses (clean)");
        assert_eq!(
            turns[1].reversible,
            Some(false),
            "burn is a committed boundary"
        );
        // The un-turn floor sits AT the burn step — the rewind can't go past it.
        assert_eq!(m.undo_floor(), turns[1].step);
        assert!(m.undo_floor_badge().contains("un-turn floor"));
        // Genesis / empty-root ticks have nothing to invert → None.
        assert!(
            m.ticks
                .iter()
                .filter(|t| !t.is_turn)
                .all(|t| t.reversible.is_none())
        );
    }

    #[test]
    fn a_fully_reversible_history_has_a_zero_undo_floor() {
        let (w, _t, _s) = fixture(); // three transfers — all reversible
        let stack = MetaStack::new();
        let m = TimeCockpitModel::build(&w, w.recorded_turns().len(), &stack);
        assert!(
            m.ticks
                .iter()
                .filter(|t| t.is_turn)
                .all(|t| t.reversible == Some(true))
        );
        assert_eq!(
            m.undo_floor(),
            0,
            "no committed boundary → rewind to genesis"
        );
        assert!(m.undo_floor_badge().contains("fully reversible"));
    }

    // ── the SCRUBBER ticks span genesis → head, turns flagged ────────────────

    #[test]
    fn the_scrubber_spans_genesis_to_head_with_turns_flagged() {
        let (w, _t, _s) = fixture();
        let stack = MetaStack::new();
        let head = w.recorded_turns().len(); // 2 genesis + 3 turns = 5
        let m = TimeCockpitModel::build(&w, head, &stack);
        assert_eq!(m.head, head);
        // One tick per landing (empty root + each step).
        assert_eq!(m.ticks.len(), head + 1);
        assert_eq!(
            m.ticks[0].step, 0,
            "the first tick is the empty pre-genesis root"
        );
        assert!(!m.ticks[0].is_turn, "the empty root is not a turn");
        // Exactly three ticks are committed TURNS.
        assert_eq!(m.ticks.iter().filter(|t| t.is_turn).count(), 3);
    }

    // ── the REWIND: dragging to the past re-derives the historical balance ───

    #[test]
    fn dragging_the_scrubber_rewinds_the_verified_image() {
        let (w, treasury, _sink) = fixture();
        let stack = MetaStack::new();
        let head = w.recorded_turns().len();

        // At the head: LIVE, treasury = 1000 − 100 − 200 − 50 = 650.
        let live = TimeCockpitModel::build(&w, head, &stack);
        assert!(live.at_head());
        assert_eq!(live.liveness, Liveness::Live);
        assert!(live.cursor_verified, "the head reconstruction verifies");
        let live_bal = live
            .cursor_cells
            .iter()
            .find(|(id, ..)| *id == treasury)
            .unwrap()
            .1;
        assert_eq!(live_bal, 650, "the head shows the live balance");

        // Rewind ONE turn (step head-1): the image rewinds, the badge says REPLAYED.
        let past = TimeCockpitModel::build(&w, head - 1, &stack);
        assert!(!past.at_head());
        assert_eq!(
            past.liveness,
            Liveness::ReplayedDeterministic,
            "the past is re-derived"
        );
        assert!(
            past.cursor_verified,
            "the past reconstruction root-verifies"
        );
        let past_bal = past
            .cursor_cells
            .iter()
            .find(|(id, ..)| *id == treasury)
            .unwrap()
            .1;
        assert_eq!(past_bal, 700, "rewound one turn: 1000 − 100 − 200 = 700");

        // The prev-step diff names what that turn did.
        assert!(
            past.diff_from_prev.is_some(),
            "a mid-history cursor has a prev-step diff"
        );
    }

    // ── the live scrub RESTORES VIA THE UMEM BOUNDARY (not genesis replay) ───

    #[test]
    fn the_live_scrub_restores_via_the_umem_boundary() {
        let (w, treasury, _sink) = fixture();
        let stack = MetaStack::new();
        let head = w.recorded_turns().len();

        // Drag to a PAST step: the cockpit model's image is restored by the umem
        // boundary (`reify_ledger`), not O(history) genesis replay — and it is
        // still root-verified and value-correct.
        let past = TimeCockpitModel::build(&w, head - 1, &stack);
        assert!(
            past.cursor_via_umem,
            "the live cockpit scrub restores via the umem boundary (the revolution, live)"
        );
        assert!(past.cursor_verified, "the umem restore root-verifies");
        let past_bal = past
            .cursor_cells
            .iter()
            .find(|(id, ..)| *id == treasury)
            .unwrap()
            .1;
        assert_eq!(
            past_bal, 700,
            "rewound one turn via umem: 1000 − 100 − 200 = 700"
        );

        // The head is also umem-restored.
        let live = TimeCockpitModel::build(&w, head, &stack);
        assert!(live.cursor_via_umem, "the head image is umem-restored too");
        assert!(live.at_head());
    }

    // ── the SUSPEND gate: the head freezes, the continuation is staged ───────

    #[test]
    fn suspend_freezes_the_head_and_stages_the_continuation() {
        let (mut w, treasury, sink) = fixture();
        let mut stack = MetaStack::new();
        let head = w.recorded_turns().len();

        // Not suspended: the gate readout is clear.
        let running = TimeCockpitModel::build(&w, head, &stack);
        assert!(!running.suspended);
        assert!(running.pending.is_empty());

        // SUSPEND, then stage a turn — it queues, the head freezes.
        w.suspend();
        let staged = w.turn(treasury, vec![transfer(treasury, sink, 10)]);
        assert!(w.commit_turn(staged).is_queued());

        let suspended = TimeCockpitModel::build(&w, w.recorded_turns().len(), &stack);
        assert!(suspended.suspended, "the gate readout shows SUSPENDED");
        assert_eq!(
            suspended.pending.len(),
            1,
            "the staged continuation is shown"
        );
        assert_eq!(
            suspended.live_height,
            head as u64 - 2,
            "head frozen (3 turns done, 2 genesis)"
        );

        // RESUME drains: the queue commits, the readout clears.
        let outcomes = w.resume(ResumeMode::Drain);
        assert!(outcomes.iter().all(|o| o.is_committed()));
        let resumed = TimeCockpitModel::build(&w, w.recorded_turns().len(), &stack);
        assert!(!resumed.suspended);
        assert!(resumed.pending.is_empty());
        let _ = &mut stack;
    }

    // ── the METASTACK breadcrumb: BASE → meta¹, top flagged ──────────────────

    #[test]
    fn the_metastack_breadcrumb_climbs_and_descends() {
        let (mut w, _t, _s) = fixture();
        let mut stack = MetaStack::new();

        // No level materialized: the breadcrumb is empty (the live system runs).
        let m0 = TimeCockpitModel::build(&w, w.recorded_turns().len(), &stack);
        assert!(m0.metastack.is_empty());

        // Suspend & push BASE.
        w.suspend();
        stack.push(&w);
        let m1 = TimeCockpitModel::build(&w, w.recorded_turns().len(), &stack);
        assert_eq!(m1.metastack.len(), 1);
        assert_eq!(m1.metastack[0].level, 0);
        assert!(
            m1.metastack[0].is_top,
            "the lone level is the top (currently debugging)"
        );

        // Push meta¹ — DEBUG THE DEBUGGER. The breadcrumb climbs.
        stack.push(&w);
        let m2 = TimeCockpitModel::build(&w, w.recorded_turns().len(), &stack);
        assert_eq!(m2.metastack.len(), 2);
        assert_eq!(m2.metastack[0].level, 0);
        assert_eq!(m2.metastack[1].level, 1);
        assert!(!m2.metastack[0].is_top, "BASE is no longer the top");
        assert!(m2.metastack[1].is_top, "meta¹ is the innermost debugger");

        // Pop descends back to BASE.
        stack.pop();
        let m3 = TimeCockpitModel::build(&w, w.recorded_turns().len(), &stack);
        assert_eq!(m3.metastack.len(), 1);
        assert!(m3.metastack[0].is_top);
    }

    // ── the liveness badge text reads honestly ───────────────────────────────

    #[test]
    fn the_liveness_badge_reads_live_at_head_and_replayed_in_the_past() {
        let (w, _t, _s) = fixture();
        let stack = MetaStack::new();
        let head = w.recorded_turns().len();
        assert!(
            TimeCockpitModel::build(&w, head, &stack)
                .liveness_badge()
                .contains("LIVE")
        );
        assert!(
            TimeCockpitModel::build(&w, 0, &stack)
                .liveness_badge()
                .contains("REPLAYED")
        );
    }
}
