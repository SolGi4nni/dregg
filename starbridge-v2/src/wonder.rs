//! THE WARM ROOM — the AOL-wonder front door over the live image.
//!
//! The cockpit ([`crate::cockpit`]) is a dense tabbed power-instrument: SHELL,
//! AGENT, SWARM, GRAPH, ORGANS, PROOFS — a bottomless workshop for the adept. The
//! LANDING portal ([`crate::landing`]) is the warm *prose* front door. THIS module
//! is the warm *room* front door: the same live image, presented as a small set of
//! **glowing, pokeable cells** a newcomer can click around with no manual — the
//! 1999-AOL-as-a-four-year-old half of the deos UX, where wonder precedes
//! comprehension. You click a cell, it tells you what it is; you grab one and drag
//! it onto another, and value flows; you never read a page of documentation.
//!
//! It is the SAME live image either surface presents, so the two halves fuse: the
//! room is also a Pharo-style live object browser. Every glowing cell IS a live
//! [`Inspectable`](crate::reflect::Inspectable) object (the *inspect* halo opens
//! exactly what the OBJECTS/inspector tab opens), every halo command maps to a REAL
//! protocol action, and a drag is a REAL verified turn — predicted first, then
//! committed, through the embedded executor. Nothing here is faked or decorative:
//!
//!   * **The glow is real.** A cell's liveliness is derived from the live
//!     [`Dynamics`](crate::dynamics::Dynamics) stream — how recently a committed
//!     turn touched it. A cell the image just moved value through glows bright; a
//!     cell at rest dims. The brightness IS the recent-activity signal the cockpit's
//!     activity feed reads, projected onto the cell.
//!   * **The halos are real.** Each cell carries a small ring of commands —
//!     *inspect* / *grab* / *explain* — and each maps to a genuine capability:
//!     *inspect* projects the cell through [`crate::reflect`] (the uniform
//!     reflective object); *grab* arms the drag-value intent; *explain* speaks a
//!     sentence drawn from the cell's real fields + its recent dynamics.
//!   * **The drag is a real turn.** Dragging value from cell A onto cell B mints a
//!     [`DragValue`] intent that lowers to a real [`Effect::Transfer`], predicts its
//!     consequences on a fork via [`crate::simulate`], and — only if the prediction
//!     commits — runs the IDENTICAL turn through [`World::commit_turn`]. The same
//!     conservation / ocap guarantees that gate the COMPOSER gate the drag; an
//!     over-drag is REFUSED in the prediction, before anything moves.
//!
//! gpui-free and `cargo test`-able, exactly like [`crate::landing`]: the room is a
//! pure projection of the live [`World`] into pokeable data, so the cockpit renders
//! it as native gpui cells while the *content* (and the glow, and the halo→action
//! mapping, and the drag→turn) is proven here without a GPU.

use dregg_cell::CellId;

use crate::dynamics::WorldEvent;
use crate::reflect::{self, Inspectable};
use crate::simulate::{self, EffectKind, IntentDraft, SimOutcome};
use crate::world::{CommitOutcome, World};

/// How many of the most-recent dynamics events the glow looks back over. A cell
/// touched within this window glows; older activity has decayed to rest. This is
/// the room's "recent" — the same tail the activity feed shows, projected per-cell.
pub const GLOW_WINDOW: usize = 16;

// ===========================================================================
// THE GLOWING CELL — a pokeable object carrying real liveliness.
// ===========================================================================

/// One **glowing cell** in the warm room: a live ledger cell projected as a
/// pokeable object, carrying the data the room renders (its id, its balance, its
/// cap count) plus a **liveliness** in `[0, 1]` derived from how recently the live
/// dynamics stream touched it. The renderer maps `liveliness` to glow intensity;
/// the model just says how alive the cell is, from the REAL activity stream.
#[derive(Clone, Debug, PartialEq)]
pub struct GlowingCell {
    /// The backing ledger cell (the live object this glow is about).
    pub cell: CellId,
    /// The cell's current balance (issuer wells carry −supply — rendered distinctly
    /// by the view, as in [`crate::reflect`]). Read live from the ledger.
    pub balance: i64,
    /// How many capabilities the cell holds (the size of its ocap web).
    pub cap_count: usize,
    /// **The glow** — liveliness in `[0, 1]`, derived from the live dynamics stream:
    /// `1.0` if the most recent event touched this cell, decaying toward `0.0` for
    /// cells the recent window did not touch. Never faked — it is a projection of
    /// [`Dynamics::tail`](crate::dynamics::Dynamics::tail).
    pub liveliness: f32,
    /// How many of the recent-window events touched this cell (the raw count behind
    /// `liveliness`, surfaced for the *explain* halo + tests).
    pub recent_touches: usize,
}

impl GlowingCell {
    /// Is this cell glowing at all (any recent activity touched it)?
    pub fn is_glowing(&self) -> bool {
        self.liveliness > 0.0
    }
}

// ===========================================================================
// THE HALO — the per-object command ring (hover → inspect ○ grab ○ explain).
// ===========================================================================

/// One **halo command** on a glowing cell — a single pokeable affordance in the
/// ring the renderer draws around a cell on hover. Each maps to a REAL action: the
/// room reuses the cockpit's own machinery, it does not reinvent a parallel one.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Halo {
    /// **Inspect** — open the cell as a live [`Inspectable`] object (the SAME
    /// uniform reflective object the OBJECTS/inspector tab shows). Maps to
    /// [`reflect::reflect_cell`].
    Inspect,
    /// **Grab** — arm the direct-manipulation DRAG-VALUE intent: pick this cell up
    /// as the *source* of a value drag, to be dropped on a target. Maps to
    /// [`DragValue::arm`].
    Grab,
    /// **Explain** — speak a plain sentence about the cell, drawn from its real
    /// fields + its recent dynamics. Maps to [`WonderRoom::explain`].
    Explain,
}

impl Halo {
    /// The full halo ring, in render order (the small set of commands every cell
    /// carries). Hover a cell → these light up.
    pub fn ring() -> [Halo; 3] {
        [Halo::Inspect, Halo::Grab, Halo::Explain]
    }

    /// The halo's glyph + short label (what the renderer draws on the ring button).
    /// Wonder-first: a child reads the glyph; an adept reads the label.
    pub fn glyph(&self) -> &'static str {
        match self {
            Halo::Inspect => "○",
            Halo::Grab => "✊",
            Halo::Explain => "?",
        }
    }

    /// A one-word label for the command (the adept's read of the glyph).
    pub fn label(&self) -> &'static str {
        match self {
            Halo::Inspect => "inspect",
            Halo::Grab => "grab",
            Halo::Explain => "explain",
        }
    }
}

// ===========================================================================
// THE DRAG-VALUE INTENT — drag from A onto B ⇒ a real conserving turn.
// ===========================================================================

/// A **drag-value intent** — the direct-manipulation gesture, modeled. Picking up
/// a cell (the *grab* halo) arms a drag whose `source` is that cell; dropping it on
/// another cell sets the `target`. Resolving the drag mints a real
/// [`Effect::Transfer`](dregg_turn::action::Effect) of `amount` from `source` to
/// `target`, which the room PREDICTS on a fork ([`crate::simulate`]) and then —
/// only if the prediction commits — runs through [`World::commit_turn`]. The same
/// conservation / ocap guarantees that gate the COMPOSER gate the drag.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DragValue {
    /// The cell the value is dragged FROM (the source — the grabbed cell).
    pub source: CellId,
    /// The cell the value is dropped ONTO (the target).
    pub target: CellId,
    /// How much value the drag moves (the gesture's magnitude — the renderer can
    /// derive it from the drop, e.g. a fixed pinch or a fraction of the source).
    pub amount: u64,
}

impl DragValue {
    /// **Arm** a drag from `source` (the *grab* halo's action): the source is
    /// grabbed, awaiting a drop. The `amount` is the value the gesture will move.
    pub fn arm(source: CellId, amount: u64) -> ArmedDrag {
        ArmedDrag { source, amount }
    }

    /// The [`IntentDraft`] this drag represents — a single [`EffectKind::Transfer`]
    /// from `source` to `target`, authored by `source` (the agent). This is the
    /// SAME draft shape the SIMULATE/COMPOSER panel builds, so the drag rides the
    /// identical predict-then-commit machinery — it does not reinvent a turn path.
    pub fn to_draft(&self) -> IntentDraft {
        let mut draft = IntentDraft::new(self.source);
        let action = draft.add_action(self.source);
        draft.add_effect(
            action,
            EffectKind::Transfer {
                to: self.target,
                amount: self.amount,
            },
        );
        draft
    }

    /// **Predict** the drag's consequences WITHOUT committing — fork the live world
    /// and run the transfer one turn ahead ([`crate::simulate::simulate`]). The live
    /// world is untouched; an over-drag surfaces as a refusal here, before anything
    /// moves. This is the wonder-safe rail: a child can drag freely and SEE what
    /// would happen before it happens.
    pub fn predict(&self, world: &World) -> SimOutcome {
        simulate::simulate(world, &self.to_draft())
    }

    /// **Resolve** the drag: predict first, and ONLY if the prediction commits, run
    /// the IDENTICAL turn on the live `world` ([`crate::simulate::commit`] →
    /// [`World::commit_turn`]). Returns the [`DragOutcome`]: the real committed
    /// receipt, or the refusal the prediction foresaw (the live world untouched).
    /// This is the predicted-first discipline the SIMULATE panel enforces, applied
    /// to the gesture — the drag NEVER commits something the prediction refused.
    pub fn resolve(&self, world: &mut World) -> DragOutcome {
        let draft = self.to_draft();
        match simulate::simulate(world, &draft) {
            SimOutcome::Predicted { .. } => match simulate::commit(world, &draft) {
                CommitOutcome::Committed { receipt, .. } => DragOutcome::Moved(receipt),
                // The prediction committed but the live commit did not — surface the
                // executor's own reason (this is the verification axis, fail-closed).
                CommitOutcome::Rejected { reason, .. } => DragOutcome::Refused { reason },
                // The world is suspended (meta-debug): the drag's turn staged, did
                // not move. Surfaced as a refusal (fail-closed, never faked moved).
                CommitOutcome::Queued { .. } => DragOutcome::Refused {
                    reason: "world suspended: turn queued, not committed".to_string(),
                },
            },
            SimOutcome::Refused { reason, .. } => DragOutcome::Refused { reason },
        }
    }
}

/// A drag whose `source` is grabbed, awaiting a drop (the *grab* halo's product).
/// Dropping it on a `target` cell completes it into a [`DragValue`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ArmedDrag {
    /// The grabbed source cell.
    pub source: CellId,
    /// The value the gesture will move once dropped.
    pub amount: u64,
}

impl ArmedDrag {
    /// **Drop** the grabbed cell onto `target`, completing the [`DragValue`].
    pub fn drop_on(self, target: CellId) -> DragValue {
        DragValue {
            source: self.source,
            target,
            amount: self.amount,
        }
    }
}

/// The outcome of resolving a [`DragValue`] — value moved (a real receipt), or the
/// executor's refusal (the live world untouched). Mirrors the COMPOSER's
/// committed/refused split, so the room surfaces a refusal the same honest way.
#[derive(Debug)]
pub enum DragOutcome {
    /// The drag committed a real conserving transfer — the executor's own receipt.
    Moved(Box<dregg_turn::turn::TurnReceipt>),
    /// The drag was REFUSED (a guarantee fired — over-drag, an ocap gate). The
    /// reason is the executor's own; the live world moved nothing.
    Refused { reason: String },
}

impl DragOutcome {
    /// Did the drag move value?
    pub fn moved(&self) -> bool {
        matches!(self, DragOutcome::Moved(_))
    }
}

// ===========================================================================
// THE WONDER ROOM — the whole warm front door, projected from the live image.
// ===========================================================================

/// THE WARM ROOM — every live cell as a glowing pokeable object, built fresh from
/// the [`World`] so the glows are the running image's actual recent activity. The
/// cockpit renders this as a room of cells the newcomer clicks around; the *content*
/// (the cells, the glows, the halos, the explanations) is built here, gpui-free.
#[derive(Clone, Debug, PartialEq)]
pub struct WonderRoom {
    /// The glowing cells, in ledger order (deterministic — sorted by id).
    pub cells: Vec<GlowingCell>,
    /// The live image's height (one warm fact the room shows: "this world has
    /// taken N turns"). Read from the live world.
    pub height: u64,
    /// How many events the room's glow looked back over (the recent window's
    /// actual extent — `min(GLOW_WINDOW, total events)`).
    pub window: usize,
}

impl WonderRoom {
    /// Build the room from the live world: project every ledger cell into a
    /// [`GlowingCell`] whose `liveliness` is derived from the recent dynamics
    /// stream, sorted by id for a stable layout.
    pub fn build(world: &World) -> Self {
        // The recent activity window — the SAME tail the activity feed reads.
        let recent: &[WorldEvent] = world.dynamics().tail(GLOW_WINDOW);
        let window = recent.len();

        let mut cells: Vec<(&CellId, &dregg_cell::Cell)> = world.ledger().iter().collect();
        cells.sort_by(|a, b| a.0.as_bytes().cmp(b.0.as_bytes()));

        let cells = cells
            .into_iter()
            .map(|(id, cell)| {
                let (liveliness, recent_touches) = glow_for(id, recent);
                GlowingCell {
                    cell: *id,
                    balance: cell.state.balance(),
                    cap_count: cell.capabilities.len(),
                    liveliness,
                    recent_touches,
                }
            })
            .collect();

        WonderRoom {
            cells,
            height: world.height(),
            window,
        }
    }

    /// Look up a glowing cell by id (the click target).
    pub fn cell(&self, id: &CellId) -> Option<&GlowingCell> {
        self.cells.iter().find(|c| &c.cell == id)
    }

    /// The brightest glowing cell — the image's current hotspot (where the eye is
    /// drawn first; `None` if nothing has happened yet). Wonder leads here.
    pub fn brightest(&self) -> Option<&GlowingCell> {
        self.cells.iter().filter(|c| c.is_glowing()).max_by(|a, b| {
            a.liveliness
                .partial_cmp(&b.liveliness)
                .unwrap_or(std::cmp::Ordering::Equal)
        })
    }

    /// The halo ring for any cell (the same small command set on every cell).
    pub fn halos(&self) -> [Halo; 3] {
        Halo::ring()
    }

    // --- the halo → real-action mappings (REUSE, never reinvent) -------------

    /// **The *inspect* halo's action.** Project `id`'s live cell into the uniform
    /// reflective [`Inspectable`] object — the SAME object the OBJECTS/inspector
    /// tab shows ([`reflect::reflect_cell`]). `None` if the cell is gone. This is
    /// the Pharo-liveness leg: a clicked glow opens a live, inspectable object.
    pub fn inspect(&self, world: &World, id: &CellId) -> Option<Inspectable> {
        world
            .ledger()
            .get(id)
            .map(|cell| reflect::reflect_cell(id, cell))
    }

    /// **The *grab* halo's action.** Arm a drag whose source is `id`, moving
    /// `amount` once dropped ([`DragValue::arm`]). The renderer hands back the
    /// drop target to complete it.
    pub fn grab(&self, id: CellId, amount: u64) -> ArmedDrag {
        DragValue::arm(id, amount)
    }

    /// **The *explain* halo's action.** Speak a plain sentence about the cell,
    /// drawn from its REAL fields (balance, caps) + its recent dynamics liveliness.
    /// No comprehension required to read it — this is the AOL-wonder leg: you poke
    /// a cell and it tells you, warmly, what it is, in its own words. Returns
    /// `None` if the cell is gone.
    pub fn explain(&self, id: &CellId) -> Option<String> {
        let g = self.cell(id)?;
        let who = reflect::short_hex(g.cell.as_bytes());
        let value = if g.balance < 0 {
            // An issuer well carries −supply (THE EPOCH) — name it warmly, not as a
            // scary negative.
            format!("an issuer well backing {} of supply", -g.balance)
        } else {
            format!("holds {} in value", g.balance)
        };
        let web = if g.cap_count == 0 {
            "reaches nothing yet".to_string()
        } else if g.cap_count == 1 {
            "reaches one other cell".to_string()
        } else {
            format!("reaches {} other cells", g.cap_count)
        };
        let alive = if g.recent_touches == 0 {
            "resting right now".to_string()
        } else if g.recent_touches == 1 {
            "the image just touched it once".to_string()
        } else {
            format!("the image touched it {} times recently", g.recent_touches)
        };
        Some(format!(
            "Cell {who} — {value}, {web}, and it is {alive}. Grab it and drop it on \
             another cell to move value; the image will show you what would happen first."
        ))
    }
}

/// The glow for one cell over a recent-event window: `(liveliness, touches)`.
///
/// `liveliness` is `1.0` if the cell is the MOST RECENT thing the window touched,
/// decaying linearly with how far back its most-recent touch was — a cell the image
/// just acted on glows full; one touched at the window's edge barely glows; one the
/// window never touched is dark (`0.0`). `touches` is the raw count of window events
/// that touched the cell (the *explain* halo + tests read it). Both come straight
/// from the real [`WorldEvent`] stream — never faked.
fn glow_for(id: &CellId, recent: &[WorldEvent]) -> (f32, usize) {
    let n = recent.len();
    if n == 0 {
        return (0.0, 0);
    }
    let mut touches = 0usize;
    // The index (within `recent`, oldest..newest) of this cell's MOST-RECENT touch.
    let mut last_touch: Option<usize> = None;
    for (i, ev) in recent.iter().enumerate() {
        if event_touches(ev, id) {
            touches += 1;
            last_touch = Some(i);
        }
    }
    let liveliness = match last_touch {
        // Most recent event (i == n-1) → 1.0; oldest (i == 0) → 1/n; untouched → 0.
        Some(i) => (i as f32 + 1.0) / (n as f32),
        None => 0.0,
    };
    (liveliness, touches)
}

/// Does a dynamics [`WorldEvent`] touch the cell `id`? This is the attribution that
/// turns the global activity stream into a per-cell glow — every variant that names
/// a cell counts (a balance flow, a field write, a cap edge either end, a birth, a
/// lifecycle transition, an emitted/received event). The `CellId::ZERO` sentinel a
/// create-effect emits (the born id isn't known at emit time, see
/// [`crate::world`]) is matched only if `id` is literally zero, which no real cell
/// is — so a birth's sentinel never spuriously lights an unrelated cell.
fn event_touches(ev: &WorldEvent, id: &CellId) -> bool {
    match ev {
        WorldEvent::CellBorn { cell, .. } => cell == id,
        WorldEvent::BalanceFlowed { cell, .. } => cell == id,
        WorldEvent::FieldSet { cell, .. } => cell == id,
        WorldEvent::CellMutated { cell } => cell == id,
        WorldEvent::CapabilityGranted { from, to } => from == id || to == id,
        WorldEvent::CapabilityRevoked { cell, .. } => cell == id,
        WorldEvent::CellSealed { cell } => cell == id,
        WorldEvent::CellUnsealed { cell } => cell == id,
        WorldEvent::CellDestroyed { cell } => cell == id,
        WorldEvent::Burned { cell, .. } => cell == id,
        WorldEvent::SurfaceDamaged { owner, cell, .. } => owner == id || cell == id,
        WorldEvent::EventEmitted { sender, cell, .. } => sender == id || cell == id,
        // A turn-commit / rejection names an agent — count the agent as touched (its
        // turn just moved the image), so the actor of a turn glows too.
        WorldEvent::TurnCommitted { agent, .. } => agent == id,
        WorldEvent::TurnRejected { agent, .. } => agent == id,
        // A queued turn (suspended world) names its agent — count it as touched.
        WorldEvent::TurnQueued { agent } => agent == id,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::world::{transfer, World};

    /// A small world: a treasury (1_000), a sink (0). No turns yet.
    fn two_cell_world() -> (World, CellId, CellId) {
        let mut w = World::new();
        let treasury = w.genesis_cell(0x11, 1_000);
        let sink = w.genesis_cell(0x22, 0);
        (w, treasury, sink)
    }

    #[test]
    fn the_room_projects_every_live_cell_as_a_glowing_object() {
        let (w, treasury, sink) = two_cell_world();
        let room = WonderRoom::build(&w);
        // Both cells are in the room, with their real balances.
        assert_eq!(room.cells.len(), 2);
        assert_eq!(room.cell(&treasury).unwrap().balance, 1_000);
        assert_eq!(room.cell(&sink).unwrap().balance, 0);
        // The room reports the live image's height.
        assert_eq!(room.height, w.height());
    }

    #[test]
    fn glow_reflects_real_dynamics_not_a_fake() {
        // THE GLOW IS REAL: before any turn, the genesis births are the only events,
        // so the freshly-born cells glow; after a transfer, the cells that turn
        // TOUCHED glow brightest, and a cell the turn did not touch dims.
        let (mut w, treasury, sink) = two_cell_world();
        let bystander = w.genesis_cell(0x33, 500);

        // Commit a real transfer treasury → sink (touches treasury + sink, NOT the
        // bystander).
        let t = w.turn(treasury, vec![transfer(treasury, sink, 250)]);
        assert!(w.commit_turn(t).is_committed());

        let room = WonderRoom::build(&w);
        let gt = room.cell(&treasury).unwrap();
        let gs = room.cell(&sink).unwrap();
        let gb = room.cell(&bystander).unwrap();

        // The two cells the turn moved value through are glowing (recent touches).
        assert!(gt.is_glowing(), "the treasury the turn debited must glow");
        assert!(gs.is_glowing(), "the sink the turn credited must glow");
        assert!(gt.recent_touches >= 1 && gs.recent_touches >= 1);

        // The bystander's only event was its genesis birth, which is OLDER than the
        // transfer's events — so it glows LESS than the freshly-touched cells (its
        // most-recent touch is further back in the window).
        assert!(
            gb.liveliness < gt.liveliness,
            "a cell the recent turn did not touch glows less than one it did \
             (bystander {} vs treasury {})",
            gb.liveliness,
            gt.liveliness
        );

        // The brightest cell is one the latest turn touched (the hotspot), never the
        // untouched bystander.
        let hot = room.brightest().unwrap();
        assert!(
            hot.cell == treasury || hot.cell == sink,
            "the hotspot is a cell the latest turn touched"
        );
    }

    #[test]
    fn glow_is_derived_from_the_live_stream_and_moves_with_it() {
        // A second turn touching the sink again should not LOWER the sink's glow
        // relative to the now-stale treasury: the glow tracks the LIVE stream, so the
        // most-recently-touched cell is always the brightest.
        let (mut w, treasury, sink) = two_cell_world();
        let t1 = w.turn(treasury, vec![transfer(treasury, sink, 100)]);
        assert!(w.commit_turn(t1).is_committed());
        // sink sends a little onward to treasury — now the LATEST events touch both,
        // but the very last balance-flow is on one of them.
        let t2 = w.turn(sink, vec![transfer(sink, treasury, 10)]);
        assert!(w.commit_turn(t2).is_committed());

        let room = WonderRoom::build(&w);
        // SOMETHING is glowing at full after a fresh turn (the most-recent event's
        // cell), proving the glow is anchored to the live stream's head.
        let max = room
            .cells
            .iter()
            .map(|c| c.liveliness)
            .fold(0.0_f32, f32::max);
        assert!(max > 0.0, "after live turns, the room has a bright cell");
        assert!(
            (max - 1.0).abs() < 1e-6,
            "the most-recently-touched cell glows full (1.0), got {max}"
        );
    }

    #[test]
    fn halos_map_to_real_actions() {
        let (w, treasury, sink) = two_cell_world();
        let room = WonderRoom::build(&w);

        // The halo ring is the small fixed command set.
        assert_eq!(room.halos(), [Halo::Inspect, Halo::Grab, Halo::Explain]);

        // INSPECT maps to the REAL reflective object — the SAME Inspectable the
        // OBJECTS tab shows (reflect::reflect_cell), with the cell's real fields.
        let obj = room.inspect(&w, &treasury).expect("the cell reflects");
        assert_eq!(obj.kind, crate::reflect::ObjectKind::Cell);
        assert!(
            obj.fields.iter().any(|f| f.key == "balance"),
            "inspect surfaces the real reflective fields"
        );
        // It is byte-for-byte the same projection reflect produces directly — the
        // room reuses reflect, it does not reinvent an object model.
        let direct = reflect::reflect_cell(&treasury, w.ledger().get(&treasury).unwrap());
        assert_eq!(obj.title, direct.title);
        assert_eq!(obj.subtitle, direct.subtitle);

        // GRAB maps to a real armed drag whose source is the grabbed cell.
        let armed = room.grab(treasury, 100);
        assert_eq!(armed.source, treasury);
        let drag = armed.drop_on(sink);
        assert_eq!(drag.source, treasury);
        assert_eq!(drag.target, sink);
        // The drag lowers to the SAME draft shape the COMPOSER/SIMULATE builds.
        let draft = drag.to_draft();
        assert_eq!(draft.agent, treasury);
        assert_eq!(draft.effect_count(), 1);

        // EXPLAIN maps to a real sentence drawn from the cell's real data (its
        // balance appears in the warm description).
        let say = room.explain(&treasury).expect("the cell explains");
        assert!(
            say.contains("1000"),
            "explain speaks the cell's real balance: {say}"
        );
        assert!(say.contains("Grab it"), "explain invites the drag gesture");
    }

    #[test]
    fn explain_names_an_issuer_well_warmly() {
        // A cell carrying negative balance (an issuer well, THE EPOCH) explains as a
        // backing well, not a scary negative — read from its REAL balance.
        let mut w = World::new();
        let mut well = crate::world::make_open_cell(0xEE, 0);
        let _ = well.state.well_debit_balance(1_000);
        let well_id = w.genesis_install(well);

        let room = WonderRoom::build(&w);
        let say = room.explain(&well_id).expect("the well explains");
        assert!(
            say.contains("issuer well"),
            "a −supply cell is explained as a well: {say}"
        );
        assert!(
            say.contains("1000"),
            "the backed supply is the real magnitude: {say}"
        );
    }

    #[test]
    fn a_drag_value_intent_simulates_then_commits_a_real_conserving_turn() {
        // THE DRAG IS A REAL TURN: drag value from treasury onto sink — predicted on
        // a fork first, then committed for real through World::commit_turn.
        let (mut w, treasury, sink) = two_cell_world();
        let room = WonderRoom::build(&w);

        // Grab the treasury, drop on the sink — a 250-value drag.
        let drag = room.grab(treasury, 250).drop_on(sink);

        // PREDICT FIRST — the live world is untouched by the prediction.
        let pred = drag.predict(&w);
        assert!(
            pred.would_commit(),
            "a conserving drag is predicted to commit"
        );
        assert_eq!(w.height(), 0, "the prediction did not touch the live world");
        assert_eq!(w.receipts().len(), 0);

        // RESOLVE — predicted-then-committed; value moves through the real executor.
        let outcome = drag.resolve(&mut w);
        assert!(outcome.moved(), "the drag moved value");
        // The real ledger updated — conservation held (250 left treasury, reached sink).
        assert_eq!(w.ledger().get(&treasury).unwrap().state.balance(), 750);
        assert_eq!(w.ledger().get(&sink).unwrap().state.balance(), 250);
        // A real receipt landed in the provenance log (the executor's own).
        assert_eq!(w.receipts().len(), 1, "a real receipt was appended");
        assert_eq!(w.height(), 1);
    }

    #[test]
    fn an_over_drag_is_refused_before_anything_moves() {
        // The verification axis, on the gesture: dragging MORE than the source holds
        // is REFUSED — predicted to refuse, and resolve never touches the live world.
        let (mut w, treasury, sink) = two_cell_world();
        let room = WonderRoom::build(&w);
        // treasury holds 1_000; try to drag 9_999.
        let drag = room.grab(treasury, 9_999).drop_on(sink);

        // The prediction foresees the refusal.
        assert!(
            !drag.predict(&w).would_commit(),
            "an over-drag is predicted to refuse"
        );

        // Resolving refuses with the executor's own reason, and moves NOTHING.
        let outcome = drag.resolve(&mut w);
        assert!(!outcome.moved(), "the over-drag moved nothing");
        match outcome {
            DragOutcome::Refused { reason } => {
                assert!(!reason.is_empty(), "a real reason is surfaced")
            }
            DragOutcome::Moved(_) => panic!("an over-drag must not commit"),
        }
        // The live world is exactly as it was — fail-closed.
        assert_eq!(w.ledger().get(&treasury).unwrap().state.balance(), 1_000);
        assert_eq!(w.ledger().get(&sink).unwrap().state.balance(), 0);
        assert_eq!(w.height(), 0);
        assert_eq!(w.receipts().len(), 0);
    }

    #[test]
    fn the_room_grows_with_the_image_it_describes() {
        // The room is a LIVE projection, not a static splash: a committed drag moves
        // the glows + the balances the next build reports.
        let (mut w, treasury, sink) = two_cell_world();
        let before = WonderRoom::build(&w);
        let before_sink = before.cell(&sink).unwrap().balance;

        let drag = before.grab(treasury, 100).drop_on(sink);
        assert!(drag.resolve(&mut w).moved());

        let after = WonderRoom::build(&w);
        let after_sink = after.cell(&sink).unwrap().balance;
        assert!(
            after_sink > before_sink,
            "the sink's balance grew after the real drag"
        );
        assert_ne!(before.cells, after.cells, "the room tracks the live image");
    }
}
