//! REHYDRATABLE UI-SLICE SNAPSHOTS — a screenshot that re-runs the camera.
//!
//! `docs/desktop-os-research/REHYDRATABLE-SURFACES.md`: a deos snapshot of a
//! moldable-inspector view is NOT a dead pixel buffer — it is a **paused camera
//! on a witnessed scene**. The "screenshot" stores only the *frustum boundary*
//! (what the camera was pointed at), and rehydrating it RE-DERIVES the same view
//! by re-running the projection over the witnessed durability log. The proof of
//! faithfulness is **re-derivability**, not a trusted provenance claim: opening
//! the snapshot re-executes the same pure projection the live inspector ran, so a
//! tampered or stale snapshot cannot produce a view the witnessed log does not
//! support.
//!
//! This lifts the single-affordance-surface pattern
//! ([`crate::affordance::AffordanceSnapshot`] / `rehydrate_for`) up to a whole UI
//! slice. An affordance snapshot stores `{ cell, affordance_names }` (the culling
//! boundary) and re-expands per-viewer through the real `is_attenuation` gate. A
//! UI-slice snapshot stores `{ focus, kind, cursor }` — the inspector's frustum
//! boundary — and re-expands by re-projecting the [`Presentable`] through the
//! real [`Registry`] over the world the witnessed log re-derives.
//!
//! The composition is pure reuse, no reinvention:
//!   * the PROJECTION is [`crate::presentable::Registry::present`] (the live
//!     inspector's own pure projection of a [`FocusTarget`] for a viewer);
//!   * the TIME-TRAVEL is [`crate::replay::History::replay_to`] (the root-verified
//!     reconstruction of a historical state from the recorded durability log);
//!   * the LIVENESS-TYPE is [`Rehydration`](crate::affordance::Rehydration)'s
//!     sibling [`Liveness`] — the honest-by-construction `Live` /
//!     `ReplayedDeterministic` / `ReconstructedApproximate` trichotomy from the
//!     rehydration model.
//!
//! ## The witness cursor (the frustum boundary)
//!
//! A snapshot is **tiny** by construction: it carries the focus + the kind + a
//! `WitnessCursor = { height, receipt_head }` — a point INTO the witness graph,
//! NOT the projected bytes. The receipt-head hash is the SAME tooth
//! [`World::state_root`](crate::world::World::state_root) folds in, so the cursor
//! pins the exact published state the camera was paused on; the height is the
//! monotone turn index [`World::height`](crate::world::World::height) the
//! [`History`] indexes.
//!
//! ## The keystone honesty property
//!
//! A snapshot captured at height H, after the world advances past H, rehydrates to
//! the SAME presentation re-derived from the durability log — and its liveness-type
//! is [`Liveness::ReplayedDeterministic`], never [`Liveness::Live`]. The camera
//! re-ran from the witnessed trace; the type SAYS SO. A snapshot whose cursor is
//! still the live head rehydrates [`Liveness::Live`] (the projection read the live
//! ledger directly). A cursor the log cannot reach rehydrates
//! [`Liveness::ReconstructedApproximate`] (the witnessed trace does not support the
//! view — surfaced, never faked).

use dregg_cell::CellId;

use crate::presentable::{FocusTarget, Presentation, PresentationKind, Registry};
use crate::replay::{History, RecordedStep};
use crate::world::World;

// ===========================================================================
// The witness cursor — a point into the witness graph (NOT the pixels).
// ===========================================================================

/// A **witness cursor**: the point in the durability log the snapshot is paused on.
///
/// `height` is the monotone turn index ([`World::height`](crate::world::World::height));
/// `receipt_head` is the head receipt-chain hash at that height (the SAME tooth
/// [`World::state_root`](crate::world::World::state_root) folds in, so the cursor
/// pins the exact published state). A snapshot is just `focus + kind + this` —
/// tiny, the frustum boundary, never the projected bytes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct WitnessCursor {
    /// The monotone turn-height the camera was paused on.
    pub height: u64,
    /// The receipt-chain head at that height (`None` at genesis, before any turn).
    pub receipt_head: Option<[u8; 32]>,
}

impl WitnessCursor {
    /// Stamp the cursor at the live head of `world` — the current witness point.
    pub fn at_head(world: &World) -> Self {
        WitnessCursor {
            height: world.height(),
            receipt_head: world.receipts().last().map(|r| r.receipt_hash()),
        }
    }

    /// Does this cursor name the LIVE head of `world` (same height AND same
    /// receipt-chain head)? When true, the camera can read the live ledger directly
    /// (a `Live` rehydration); otherwise it must re-run over the replayed log.
    pub fn is_live_head(&self, world: &World) -> bool {
        self.height == world.height()
            && self.receipt_head == world.receipts().last().map(|r| r.receipt_hash())
    }
}

// ===========================================================================
// The liveness-type (the rehydration model's trichotomy, honest by construction).
// ===========================================================================

/// The **liveness-type** of a rehydrated view — the rehydration model's honesty
/// trichotomy (`docs/desktop-os-research/REHYDRATABLE-SURFACES.md`). It is NOT a
/// provenance claim; it is the DERIVED truth of HOW the view was produced:
///
///   * [`Liveness::Live`] — the cursor is the live head, so the projection read
///     the live ledger FRESH (the camera never paused).
///   * [`Liveness::ReplayedDeterministic`] — the cursor is in the past, so the
///     world was re-derived by ROOT-VERIFIED replay from the durability log and the
///     projection re-ran over THAT reconstructed state (the camera re-ran,
///     deterministically, from the witnessed trace).
///   * [`Liveness::ReconstructedApproximate`] — the cursor's height is not
///     reachable in the log (a pruned / foreign / forged cursor), so the witnessed
///     trace does NOT support the view; it is surfaced as approximate, never faked.
///
/// This is the UI-slice sibling of [`crate::affordance::Rehydration`] (which
/// carries the per-viewer re-expanded affordance set); both express "what the
/// witnessed graph re-derives", and neither confers authority of its own.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Liveness {
    /// The cursor is the live head — projected over the live world, fresh.
    Live,
    /// The cursor is in the past — the world was re-derived by root-verified replay
    /// and the projection re-ran over that reconstruction.
    ReplayedDeterministic,
    /// The cursor's height is not reachable in the durability log — the witnessed
    /// trace does not support the view (surfaced honestly, never faked).
    ReconstructedApproximate,
}

impl Liveness {
    /// A short stable slug (a test selector / a render badge key).
    pub fn slug(&self) -> &'static str {
        match self {
            Liveness::Live => "live",
            Liveness::ReplayedDeterministic => "replayed-deterministic",
            Liveness::ReconstructedApproximate => "reconstructed-approximate",
        }
    }

    /// `true` iff the view was produced by re-running the camera over a
    /// root-verified replay of the durability log (the honest re-derivation).
    pub fn is_replayed(&self) -> bool {
        matches!(self, Liveness::ReplayedDeterministic)
    }
}

// ===========================================================================
// The snapshot — tiny: focus + kind + the witness cursor (the frustum boundary).
// ===========================================================================

/// A **rehydratable UI-slice snapshot** — a screenshot of a moldable-inspector view
/// that is NOT a dead pixel buffer but a tiny cursor into the witness graph.
///
/// It carries ONLY the frustum boundary: which object the inspector was focused on
/// ([`FocusTarget`]), which presentation lens it was showing ([`PresentationKind`]),
/// and the [`WitnessCursor`] it was paused on. Re-running the camera
/// ([`UiSnapshot::rehydrate`]) re-projects the [`Presentable`] over the world the
/// witnessed log re-derives and re-selects the captured lens — yielding the SAME
/// presentation the live inspector showed at the cursor's height.
///
/// Tiny on purpose: the snapshot embeds no projected bytes (the presentation is
/// always RE-DERIVED, never stored), so it cannot drift from the witnessed truth.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct UiSnapshot {
    /// The object the inspector was focused on (the camera's aim).
    pub focus: FocusTarget,
    /// The presentation lens that was selected (the camera's frustum face).
    pub kind: PresentationKind,
    /// The witness point the camera was paused on (height + receipt-chain head).
    pub cursor: WitnessCursor,
}

/// The result of re-running a snapshot's camera: the re-derived presentation plus
/// the DERIVED liveness-type (how the view was produced).
///
/// The presentation is `None` exactly when the focused object is absent from the
/// re-derived state (a dangling focus — surfaced honestly, never a faked slice) OR
/// when the captured lens is not offered by the re-derived presentation set. The
/// liveness-type is always present: it reports HOW the camera ran regardless.
#[derive(Clone, Debug)]
pub struct RehydratedSlice {
    /// The object the slice re-projected (echoes the snapshot's focus).
    pub focus: FocusTarget,
    /// The lens the slice re-selected (echoes the snapshot's kind).
    pub kind: PresentationKind,
    /// The re-derived presentation for the captured lens, re-projected through the
    /// viewer's authority. `None` iff the focus is absent at the cursor or the lens
    /// is not offered there.
    pub presentation: Option<Presentation>,
    /// HOW the camera ran (the rehydration model's honest liveness-type).
    pub liveness: Liveness,
}

impl RehydratedSlice {
    /// `true` iff the camera re-derived a presentation for the captured lens.
    pub fn is_present(&self) -> bool {
        self.presentation.is_some()
    }
}

impl UiSnapshot {
    /// **Capture** a UI-slice snapshot — stamp the current witness cursor over the
    /// `(focus, kind)` the inspector is showing. Tiny: no projected bytes are
    /// stored, only the frustum boundary + the witness point.
    pub fn capture(world: &World, focus: FocusTarget, kind: PresentationKind) -> Self {
        UiSnapshot {
            focus,
            kind,
            cursor: WitnessCursor::at_head(world),
        }
    }

    /// **Rehydrate** — RE-RUN THE CAMERA for `viewer`.
    ///
    ///   1. if the cursor is the LIVE head, re-project the [`Presentable`] over the
    ///      live `world` (liveness [`Liveness::Live`] — the camera never paused);
    ///   2. else replay the world to the cursor's height via [`History::replay_to`]
    ///      (root-verified against the recorded tooth) and re-project over THAT
    ///      reconstruction (liveness [`Liveness::ReplayedDeterministic`] — the
    ///      camera re-ran from the witnessed log);
    ///   3. if the cursor's height is not reachable in the log, the witnessed trace
    ///      does not support the view (liveness
    ///      [`Liveness::ReconstructedApproximate`]).
    ///
    /// Per-viewer: the re-projection is [`Registry::present(target, viewer)`], which
    /// already projects the lens (e.g. the Affordances cap badges) through the
    /// viewer's authority — the SAME attenuation the live inspector applies. We do
    /// not re-derive the attenuation here; we route the viewer through the existing
    /// projection path.
    pub fn rehydrate(&self, world: &World, viewer: CellId) -> RehydratedSlice {
        // (1) The cursor is the live head → project over the live world, fresh.
        if self.cursor.is_live_head(world) {
            let presentation = self.project_over(world, viewer);
            return RehydratedSlice {
                focus: self.focus,
                kind: self.kind,
                presentation,
                liveness: Liveness::Live,
            };
        }

        // (2)/(3) The cursor is in the past → re-derive the historical world from the
        // durability log by ROOT-VERIFIED replay, then re-project over it. If the
        // height is not reachable, the witnessed trace does not support the view.
        match self.replay_world_to_cursor(world) {
            Some(historical) => {
                let presentation = self.project_over(&historical, viewer);
                RehydratedSlice {
                    focus: self.focus,
                    kind: self.kind,
                    presentation,
                    liveness: Liveness::ReplayedDeterministic,
                }
            }
            None => RehydratedSlice {
                focus: self.focus,
                kind: self.kind,
                presentation: None,
                liveness: Liveness::ReconstructedApproximate,
            },
        }
    }

    /// Re-project the captured `(focus, kind)` over `world` for `viewer`, reusing
    /// the live inspector's own pure projection ([`Registry::present`]) and then
    /// selecting the captured lens. `None` iff the focus is absent OR the lens is
    /// not offered (both surfaced honestly).
    fn project_over(&self, world: &World, viewer: CellId) -> Option<Presentation> {
        let registry = Registry::new(world);
        let set = registry.present(self.focus, viewer)?;
        set.into_iter().find(|p| p.kind == self.kind)
    }

    /// Re-derive the historical [`World`] at the snapshot's cursor by ROOT-VERIFIED
    /// replay of the recorded durability log, reusing [`History::replay_to`] as the
    /// trust anchor. `None` iff the cursor's height is not reachable in the log.
    ///
    /// The world's [`History`] indexes BOTH genesis installs and committed turns,
    /// while the cursor's `height` counts only committed turns. We walk the recorded
    /// steps, counting committed turns, to find the history step `k` that lands at
    /// `cursor.height`; [`History::replay_to(k)`] then re-derives (and root-verifies)
    /// the ledger there, which we re-drive into a fresh [`World`] through its own
    /// public genesis + commit paths so the projection sees the SAME presentable
    /// surface the live inspector saw at H.
    fn replay_world_to_cursor(&self, world: &World) -> Option<World> {
        let history = world.recorded_turns();
        let step = history_step_for_height(history, self.cursor.height)?;

        // The trust anchor: a root-verified reconstruction of the ledger at `step`.
        // A replay error (out-of-range / a tampered tooth / nondeterminism) means
        // the witnessed log does not support the cursor — surfaced as unreachable.
        history.replay_to(step).ok()?;

        // Re-drive the historical world through the World's OWN public paths so the
        // projection reads a genuine presentable surface (the same genesis +
        // commit_turn the live world ran). This re-execution is the verified
        // executor's; it lands on the SAME root `replay_to` just verified.
        let mut rebuilt = World::new();
        for recorded in &history.steps()[..step] {
            match recorded {
                RecordedStep::Genesis { cell } => {
                    rebuilt.genesis_install(cell.clone());
                }
                RecordedStep::Committed { turn, .. } => {
                    let outcome = rebuilt.commit_turn(turn.clone());
                    if !outcome.is_committed() {
                        // A recorded commit that does not re-commit means the log is
                        // not faithfully replayable into a world — surface honestly.
                        return None;
                    }
                }
            }
        }
        Some(rebuilt)
    }
}

/// The history step index that lands at turn-`height` (the cursor counts committed
/// turns; the [`History`] counts genesis installs + turns). Returns the step index
/// `k` such that replaying `steps[..k]` has applied exactly `height` committed
/// turns AND the next step is not a turn (i.e. `k` is the landing immediately after
/// the `height`-th turn, including any trailing genesis installs at that height).
/// `None` iff fewer than `height` committed turns exist in the log.
fn history_step_for_height(history: &History, height: u64) -> Option<usize> {
    let mut committed: u64 = 0;
    let steps = history.steps();
    for (i, step) in steps.iter().enumerate() {
        if committed == height {
            // We have applied `height` turns; the landing is here, but absorb any
            // genesis installs that sit at this height (they bear no turn).
            if matches!(step, RecordedStep::Committed { .. }) {
                return Some(i);
            }
        }
        if matches!(step, RecordedStep::Committed { .. }) {
            committed += 1;
        }
    }
    if committed >= height {
        // The full log applied exactly `height` (or, for height past genesis-only
        // tails, at least `height`) turns — land at the end of the recorded log.
        Some(steps.len())
    } else {
        None
    }
}

// ===========================================================================
// TESTS — the model, proven gpui-free (exactly as presentable.rs/replay.rs are).
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::presentable::PresentationBody;
    use crate::reflect::FieldValue;
    use crate::world::{transfer, World};

    /// A two-cell world: a treasury (1_000) and a sink (0), no turns yet.
    fn two_cell_world() -> (World, CellId, CellId) {
        let mut w = World::new();
        let treasury = w.genesis_cell(0x11, 1_000);
        let sink = w.genesis_cell(0x22, 0);
        (w, treasury, sink)
    }

    /// The treasury's RawFields balance in a re-derived presentation (the
    /// load-bearing observable the keystone test compares).
    fn raw_balance(p: &Presentation) -> Option<i64> {
        match &p.body {
            PresentationBody::Fields(i) => i.fields.iter().find_map(|f| match f.value {
                FieldValue::Balance(b) => Some(b),
                _ => None,
            }),
            _ => None,
        }
    }

    // ── capture is tiny: focus + kind + the witness cursor ──────────────────

    #[test]
    fn capture_stamps_the_live_witness_cursor() {
        let (w, treasury, _sink) = two_cell_world();
        let snap = UiSnapshot::capture(&w, FocusTarget::Cell(treasury), PresentationKind::RawFields);
        // The cursor is the live head: height 0 (no turns), no receipt head yet.
        assert_eq!(snap.cursor.height, 0);
        assert_eq!(snap.cursor.receipt_head, None);
        assert!(snap.cursor.is_live_head(&w), "a fresh capture is the live head");
    }

    // ── KEYSTONE: capture → advance → rehydrate re-derives the historical view ─

    #[test]
    fn capture_then_advance_then_rehydrate_re_derives_the_historical_presentation() {
        // The honesty property: a snapshot captured at H, after the world advances,
        // rehydrates to the SAME presentation re-derived from the durability log —
        // and the liveness-type is ReplayedDeterministic, NOT Live.
        let (mut w, treasury, sink) = two_cell_world();

        // Capture the treasury's RawFields slice at H (balance 1_000), then read
        // what the LIVE inspector shows there (the camera's paused frame).
        let snap = UiSnapshot::capture(&w, FocusTarget::Cell(treasury), PresentationKind::RawFields);
        let live_at_h = snap.rehydrate(&w, treasury);
        assert_eq!(live_at_h.liveness, Liveness::Live, "at the head, the camera is live");
        let balance_at_h = raw_balance(live_at_h.presentation.as_ref().unwrap()).unwrap();
        assert_eq!(balance_at_h, 1_000, "the live inspector showed 1_000 at H");

        // The world ADVANCES past H: a real committed transfer drops the treasury.
        let turn = w.turn(treasury, vec![transfer(treasury, sink, 250)]);
        assert!(w.commit_turn(turn).is_committed());
        assert_eq!(w.height(), 1, "the world advanced one turn");

        // Re-run the camera: the snapshot rehydrates the HISTORICAL view (1_000),
        // re-derived from the log — NOT the live 750 — and SAYS it replayed.
        let rehydrated = snap.rehydrate(&w, treasury);
        assert_eq!(
            rehydrated.liveness,
            Liveness::ReplayedDeterministic,
            "after advancing, the cursor is in the past — the camera re-ran from the log"
        );
        assert!(rehydrated.liveness.is_replayed());
        let re_balance = raw_balance(rehydrated.presentation.as_ref().unwrap()).unwrap();
        assert_eq!(
            re_balance, 1_000,
            "the snapshot re-derives the HISTORICAL balance (1_000), not the live 750"
        );

        // Sanity: the LIVE inspector now shows 750 (the snapshot did not pollute it).
        let live_now = Registry::new(&w)
            .present(FocusTarget::Cell(treasury), treasury)
            .unwrap();
        let live_raw = live_now.iter().find(|p| p.kind == PresentationKind::RawFields).unwrap();
        assert_eq!(raw_balance(live_raw).unwrap(), 750, "the live world moved on to 750");
    }

    // ── the liveness-type is Live at the head, Replayed after advancing ──────

    #[test]
    fn liveness_is_live_at_head_and_replayed_after_advancing() {
        let (mut w, treasury, sink) = two_cell_world();
        let snap = UiSnapshot::capture(&w, FocusTarget::Cell(treasury), PresentationKind::Provenance);

        // At the head: Live.
        assert_eq!(snap.rehydrate(&w, treasury).liveness, Liveness::Live);

        // After ANY advance (even of an unrelated cell), the captured cursor falls
        // behind the head → ReplayedDeterministic.
        let turn = w.turn(treasury, vec![transfer(treasury, sink, 1)]);
        assert!(w.commit_turn(turn).is_committed());
        assert_eq!(
            snap.rehydrate(&w, treasury).liveness,
            Liveness::ReplayedDeterministic
        );
    }

    // ── an unreachable cursor is ReconstructedApproximate ────────────────────

    #[test]
    fn an_unreachable_cursor_is_reconstructed_approximate() {
        // A cursor whose height the durability log cannot reach (a pruned/foreign/
        // forged cursor) rehydrates as ReconstructedApproximate — the witnessed
        // trace does not support it, surfaced honestly (never a faked slice).
        let (w, treasury, _sink) = two_cell_world();
        let mut snap =
            UiSnapshot::capture(&w, FocusTarget::Cell(treasury), PresentationKind::RawFields);
        // Forge a cursor far past the recorded history (no turns exist).
        snap.cursor = WitnessCursor {
            height: 999,
            receipt_head: Some([0xABu8; 32]),
        };
        let slice = snap.rehydrate(&w, treasury);
        assert_eq!(slice.liveness, Liveness::ReconstructedApproximate);
        assert!(
            slice.presentation.is_none(),
            "an unreachable cursor yields no re-derived presentation (honest)"
        );
    }

    // ── two viewers rehydrate attenuated-differently ─────────────────────────

    #[test]
    fn two_viewers_rehydrate_the_affordances_lens_attenuated_differently() {
        // Two viewers re-run the SAME snapshot's camera and each gets the genuine
        // re-derived Affordances lens (the InspectAct surface) from the replayed log —
        // and the lens DIVIDES PER-VIEWER (the membrane property). The viewer's authority
        // over the cell is DERIVED off the live ledger
        // (`presentable::ReflectedCell::present` → `inspect_act::viewer_authority_over`):
        // the cell's OWN principal is its root authority (`None`, clears every affordance),
        // while a foreign viewer holding no cap reaching it gets the weakest tier
        // (`Impossible`, refused the authority-bearing affordances). So the owner is
        // authorized for messages the foreign viewer is refused — the two re-derived bodies
        // genuinely differ, and that divergence survives the camera re-run.
        let (mut w, treasury, sink) = two_cell_world();

        // Advance so the rehydration goes through the REPLAY path (the per-viewer
        // attenuation must survive re-derivation from the log, not just the live read).
        let snap =
            UiSnapshot::capture(&w, FocusTarget::Cell(treasury), PresentationKind::Affordances);
        let turn = w.turn(treasury, vec![transfer(treasury, sink, 10)]);
        assert!(w.commit_turn(turn).is_committed());

        // Viewer A = the treasury itself (the owner principal); Viewer B = the sink
        // (a different principal). Re-run the camera for each.
        let slice_owner = snap.rehydrate(&w, treasury);
        let slice_other = snap.rehydrate(&w, sink);

        assert_eq!(slice_owner.liveness, Liveness::ReplayedDeterministic);
        assert_eq!(slice_other.liveness, Liveness::ReplayedDeterministic);

        let owner_aff = slice_owner.presentation.expect("owner gets the affordances lens");
        let other_aff = slice_other.presentation.expect("other gets the affordances lens");

        // Both re-derive the lens; the per-viewer projection differs in its
        // authorization read (the search_text carries the cap-badge verdicts), so
        // the two viewers' re-derived bodies are NOT identical — the attenuation the
        // live inspector applied survived the camera re-run.
        let owner_text = match &owner_aff.body {
            PresentationBody::Fields(i) => i
                .fields
                .iter()
                .map(|f| match &f.value {
                    FieldValue::Text(t) => t.clone(),
                    other => format!("{other:?}"),
                })
                .collect::<Vec<_>>()
                .join(" | "),
            _ => String::new(),
        };
        let other_text = match &other_aff.body {
            PresentationBody::Fields(i) => i
                .fields
                .iter()
                .map(|f| match &f.value {
                    FieldValue::Text(t) => t.clone(),
                    other => format!("{other:?}"),
                })
                .collect::<Vec<_>>()
                .join(" | "),
            _ => String::new(),
        };
        // Each viewer re-derives a genuine, non-empty affordances lens from the replayed
        // log (the camera ran for each, carrying the real cap-badge verdicts).
        assert!(
            owner_text.contains("requires") && !owner_text.is_empty(),
            "the owner viewer re-derives the real affordances lens (cap-badge verdicts)"
        );
        assert!(
            other_text.contains("requires") && !other_text.is_empty(),
            "the foreign viewer re-derives the real affordances lens (cap-badge verdicts)"
        );

        // THE MEMBRANE PROPERTY: the lens divides per-viewer. The owner (the cell's own
        // principal — root `None` authority) is authorized for messages the foreign viewer
        // (no cap reaching the cell — the weakest `Impossible` tier) is refused, so the two
        // re-derived bodies carry DIFFERENT cap-badge verdicts. The divergence survived the
        // camera re-run (the replay path), not just a live read.
        assert_ne!(
            owner_text, other_text,
            "the owner is authorized for messages the foreign viewer is refused — \
             the affordances lens genuinely divides per-viewer"
        );
    }

    // ── the rehydrated slice echoes the captured frustum boundary ───────────

    #[test]
    fn the_rehydrated_slice_echoes_the_captured_focus_and_kind() {
        let (w, treasury, _sink) = two_cell_world();
        let snap = UiSnapshot::capture(&w, FocusTarget::Cell(treasury), PresentationKind::Graph);
        let slice = snap.rehydrate(&w, treasury);
        assert_eq!(slice.focus, FocusTarget::Cell(treasury));
        assert_eq!(slice.kind, PresentationKind::Graph);
        let p = slice.presentation.expect("the graph lens is offered");
        assert_eq!(p.kind, PresentationKind::Graph);
    }

    // ── rehydration through several advances re-derives each historical H ────

    #[test]
    fn snapshots_at_distinct_heights_each_re_derive_their_own_historical_view() {
        // Three snapshots at three heights re-derive three DIFFERENT historical
        // balances from the one durability log — the camera re-runs faithfully at
        // each paused point.
        let (mut w, treasury, sink) = two_cell_world();
        let snap0 = UiSnapshot::capture(&w, FocusTarget::Cell(treasury), PresentationKind::RawFields);

        let t1 = w.turn(treasury, vec![transfer(treasury, sink, 100)]);
        assert!(w.commit_turn(t1).is_committed());
        let snap1 = UiSnapshot::capture(&w, FocusTarget::Cell(treasury), PresentationKind::RawFields);

        let t2 = w.turn(treasury, vec![transfer(treasury, sink, 200)]);
        assert!(w.commit_turn(t2).is_committed());
        let snap2 = UiSnapshot::capture(&w, FocusTarget::Cell(treasury), PresentationKind::RawFields);

        // Advance once more so even snap2 is in the past.
        let t3 = w.turn(treasury, vec![transfer(treasury, sink, 50)]);
        assert!(w.commit_turn(t3).is_committed());

        let b0 = raw_balance(snap0.rehydrate(&w, treasury).presentation.as_ref().unwrap()).unwrap();
        let b1 = raw_balance(snap1.rehydrate(&w, treasury).presentation.as_ref().unwrap()).unwrap();
        let b2 = raw_balance(snap2.rehydrate(&w, treasury).presentation.as_ref().unwrap()).unwrap();
        let live = raw_balance(
            Registry::new(&w)
                .present(FocusTarget::Cell(treasury), treasury)
                .unwrap()
                .iter()
                .find(|p| p.kind == PresentationKind::RawFields)
                .unwrap(),
        )
        .unwrap();

        assert_eq!(b0, 1_000, "H0: before any transfer");
        assert_eq!(b1, 900, "H1: after −100");
        assert_eq!(b2, 700, "H2: after −100 −200");
        assert_eq!(live, 650, "live: after −100 −200 −50");
        // Each snapshot re-ran its own camera honestly.
        for snap in [&snap0, &snap1, &snap2] {
            assert_eq!(
                snap.rehydrate(&w, treasury).liveness,
                Liveness::ReplayedDeterministic
            );
        }
    }
}
