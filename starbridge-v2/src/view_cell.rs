//! THE UI-CELL SUBSTRATE (M3) — the cockpit's own view-state, self-hosted as
//! real dregg cells, by generalizing the proven [`BufferCell`](crate::buffer)
//! two-tier split.
//!
//! `docs/deos/REFLEXIVE-MIGRATION.md` §3 names the keystone: promote the
//! cockpit's ~50 plain-Rust *camera-aim* fields (focus, tab, present-index,
//! selection, …) into dregg **cells**, so the inspector becomes inspectable, the
//! UI becomes a witnessed graph, and the tools become objects in the image (the
//! Smalltalk knot). This module is the substrate move:
//!
//!   * [`ViewCell`] — one **UI cell** for an inspector view's `(focus,
//!     present_idx)` camera-aim. It is the [`BufferCell`] pattern verbatim, only
//!     the payload is the view's semantic state rather than a text digest: a
//!     **free in-memory draft** ([`ViewDoc`], mutated on every re-focus with no
//!     ledger cost) plus an **occasional witnessed commit** ([`ViewCell::commit`],
//!     a real cap-gated `Effect::SetField` turn). Its **revision = the backing
//!     cell's nonce** — the receipt chain IS the view's navigation history.
//!   * [`ViewCell`] is itself [`Presentable`] (registered through
//!     [`FocusTarget::ViewCell`](crate::presentable::FocusTarget)) — so you can
//!     **inspect the inspector**: open the moldable inspector ON a `ViewCell` and
//!     see its `(focus, present_idx, revision)` as a real presentation set.
//!   * [`WorkspaceCell`] — the wider semantic-UI-state subgraph (active tab +
//!     per-tab view aim), the same two-tier split over a backing cell, so the
//!     cockpit's `render()` reads its tab/focus selector FROM a cell
//!     (`render(workspace_subgraph)`, §3.4) rather than from a Rust field.
//!
//! ## The UI-mutation weight class (§3.5) and the self-cycle (STRATIFIED-FIXPOINT)
//!
//! A tab-switch / re-focus **conserves nothing** — it is the `SetField` weight
//! class, exactly as a buffer keystroke is. Free re-focus stays in the in-memory
//! draft; a witnessed **commit** (what makes the image durable/rewindable) lands a
//! `SetField` turn only occasionally. And the reflexive self-cycle (a `ViewCell`
//! that the inspector projects is itself view-state) is broken by **unit-delay**:
//! `present` reads the *committed* (prior-frame) cell state, never a within-frame
//! fixpoint — `present` stays PURE and observes authority, it never confers it
//! (the load-bearing M3 invariant).
//!
//! gpui-FREE and `cargo test`-able exactly as [`crate::buffer`] /
//! [`crate::presentable`] are; the cockpit maps a [`ViewCell`] onto its existing
//! moldable-inspector pane (only the *selector* moves from a Rust field to a cell
//! read).

use dregg_cell::{CellId, FieldElement};

use crate::presentable::{
    Presentable, PresentCtx, Presentation, PresentationBody, PresentationKind,
};
use crate::reflect::{self, Field, Inspectable, ObjectKind};
use crate::world::{self, World};

// ===========================================================================
// The backing-cell slot layout (low slots, like BUFFER_DIGEST_SLOT = 1).
// ===========================================================================

/// The state slot the backing cell carries the view's FOCUS cell id in (the 32
/// bytes ARE one field element). The all-zero element is the `None` sentinel (no
/// focus). A re-focus that commits advances the cell's `source_state_root` here,
/// exactly as a buffer edit advances [`BUFFER_DIGEST_SLOT`](crate::buffer::BUFFER_DIGEST_SLOT).
pub const VIEW_FOCUS_SLOT: usize = 2;

/// The state slot the backing cell carries the view's PRESENT-INDEX in (the
/// little-endian `u64` index into the resolved presentation set, in the low 8
/// bytes of the element).
pub const VIEW_PRESENT_IDX_SLOT: usize = 3;

/// Pack a `u64` into the low 8 bytes of a field element (little-endian); the rest
/// is zero. The inverse of [`unpack_u64`].
fn pack_u64(v: u64) -> FieldElement {
    let mut fe = [0u8; 32];
    fe[..8].copy_from_slice(&v.to_le_bytes());
    fe
}

/// Read a `u64` back out of the low 8 bytes of a field element (the inverse of
/// [`pack_u64`]).
fn unpack_u64(fe: &FieldElement) -> u64 {
    let mut b = [0u8; 8];
    b.copy_from_slice(&fe[..8]);
    u64::from_le_bytes(b)
}

/// The all-zero element — the `None`-focus sentinel for [`VIEW_FOCUS_SLOT`].
const FOCUS_NONE: FieldElement = [0u8; 32];

// ===========================================================================
// The free in-memory draft (the gpui-free "visible" view state).
// ===========================================================================

/// The gpui-free view DOCUMENT — the camera-aim a [`ViewCell`] shows: which cell
/// the inspector is focused on + which presentation lens (by index) is open.
/// Plain data so the model stays renderer-agnostic; mutating it is FREE (it does
/// NOT touch the ledger — see [`ViewCell::commit`] for the witnessed landing).
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct ViewDoc {
    /// The cell the inspector is focused on (the camera's aim). `None` = unfocused
    /// (the cockpit then falls to the first sorted cell, as today).
    focus: Option<CellId>,
    /// Which presentation in the resolved set the tab-strip has open (an index;
    /// the cockpit clamps it each render so it survives a re-focus).
    present_idx: usize,
}

impl ViewDoc {
    /// A fresh unfocused document (present index 0).
    pub fn new() -> Self {
        ViewDoc::default()
    }

    /// A document aimed at `focus` (present index 0).
    pub fn focused(focus: CellId) -> Self {
        ViewDoc { focus: Some(focus), present_idx: 0 }
    }

    /// The focused cell (the camera's aim), if any.
    pub fn focus(&self) -> Option<CellId> {
        self.focus
    }

    /// The open presentation index.
    pub fn present_idx(&self) -> usize {
        self.present_idx
    }

    /// FREE: re-aim the camera at `focus` (resets the lens to 0, as a re-focus
    /// does today). In-memory only — the ledger is untouched until [`ViewCell::commit`].
    pub fn set_focus(&mut self, focus: Option<CellId>) {
        self.focus = focus;
        self.present_idx = 0;
    }

    /// FREE: open presentation `idx` (the tab-strip click). In-memory only.
    pub fn set_present_idx(&mut self, idx: usize) {
        self.present_idx = idx;
    }
}

// ===========================================================================
// The ViewCell — the BufferCell two-tier pattern over a view's camera-aim.
// ===========================================================================

/// A **UI cell**: an inspector view's `(focus, present_idx)` camera-aim, backed
/// by a REAL ledger cell. The [`BufferCell`](crate::buffer::BufferCell) pattern,
/// only the payload is the view's semantic state:
///   * the visible [`ViewDoc`] is gpui-free and FREE to mutate (a re-focus);
///   * its authenticated state rides the backing cell's [`VIEW_FOCUS_SLOT`] +
///     [`VIEW_PRESENT_IDX_SLOT`], advanced only by [`ViewCell::commit`] through a
///     real `Effect::SetField` turn;
///   * its **revision = the backing cell's nonce** — the receipt chain IS the
///     view's navigation history.
///
/// The keystone reflexivity: a `ViewCell` is itself [`Presentable`], so the
/// inspector can focus ON it — *inspect the inspector*.
#[derive(Clone, Debug)]
pub struct ViewCell {
    /// The backing cell whose state holds the view's camera-aim + whose nonce is
    /// the view's revision. The REAL anchor in the live ledger.
    backing: CellId,
    /// The visible view document (the free in-memory draft).
    doc: ViewDoc,
    /// An operator-facing view name (e.g. "INSPECTOR"). The TRUSTED identity is
    /// the backing cell id; this is a label.
    name: String,
}

impl ViewCell {
    /// Open a view cell over `backing`, named `name`, with an empty draft.
    pub fn new(backing: CellId, name: impl Into<String>) -> Self {
        ViewCell { backing, doc: ViewDoc::new(), name: name.into() }
    }

    /// Open a view cell already aimed at `focus`.
    pub fn focused(backing: CellId, name: impl Into<String>, focus: CellId) -> Self {
        ViewCell { backing, doc: ViewDoc::focused(focus), name: name.into() }
    }

    /// Reconstruct a view cell from a backing cell's **witnessed (committed)**
    /// camera-aim on the live world (the draft = the committed aim). `None` iff
    /// the backing cell is absent. Used by [`Registry`](crate::presentable::Registry)
    /// — which holds only `&World` — to resolve a [`FocusTarget::ViewCell`](crate::presentable::FocusTarget)
    /// to the prior-frame state the projector reads (the unit-delay).
    pub fn from_world(world: &World, backing: CellId) -> Option<Self> {
        let probe = ViewCell::new(backing, "view");
        let aim = probe.committed_aim(world)?;
        Some(ViewCell { backing, doc: aim, name: "view".to_string() })
    }

    /// The backing cell id (the authenticated anchor).
    pub fn backing(&self) -> CellId {
        self.backing
    }

    /// The view name (the inspector pane title).
    pub fn name(&self) -> &str {
        &self.name
    }

    /// The visible draft (read-only borrow — the cockpit renders its aim).
    pub fn doc(&self) -> &ViewDoc {
        &self.doc
    }

    /// A MUTABLE borrow of the draft for FREE re-aiming (re-focus / lens change).
    /// Does NOT touch the ledger — see [`Self::commit`] for the witnessed landing.
    pub fn doc_mut(&mut self) -> &mut ViewDoc {
        &mut self.doc
    }

    /// The view's REVISION — the backing cell's nonce, advanced by each committed
    /// re-aim. `0` for a never-committed / missing view.
    pub fn revision(&self, world: &World) -> u64 {
        world
            .ledger()
            .get(&self.backing)
            .map(|c| c.state.nonce())
            .unwrap_or(0)
    }

    /// The COMMITTED (witnessed) camera-aim the backing cell currently stores —
    /// the *prior-frame* state the reflexive projector reads (the unit-delay that
    /// breaks the self-cycle, STRATIFIED-FIXPOINT §7.3). `None` iff the backing
    /// cell is gone.
    pub fn committed_aim(&self, world: &World) -> Option<ViewDoc> {
        let cell = world.ledger().get(&self.backing)?;
        let focus_fe = cell.state.fields[VIEW_FOCUS_SLOT];
        let focus = if focus_fe == FOCUS_NONE {
            None
        } else {
            Some(CellId::from_bytes(focus_fe))
        };
        let present_idx = unpack_u64(&cell.state.fields[VIEW_PRESENT_IDX_SLOT]) as usize;
        Some(ViewDoc { focus, present_idx })
    }

    /// Whether the backing cell is present AND the committed aim MATCHES the
    /// visible draft (no uncommitted re-focus). A view whose draft differs from
    /// the committed aim has an *uncommitted* camera move (dirty).
    pub fn is_clean(&self, world: &World) -> bool {
        match self.committed_aim(world) {
            Some(aim) => aim == self.doc,
            None => false,
        }
    }

    /// **COMMIT THE RE-AIM — the witnessed landing.** Writes the visible draft's
    /// `(focus, present_idx)` into the backing cell ([`VIEW_FOCUS_SLOT`],
    /// [`VIEW_PRESENT_IDX_SLOT`]) through a REAL `Effect::SetField` turn on the
    /// embedded executor — the SAME `TurnExecutor` every other dregg effect runs,
    /// generalizing [`BufferCell::commit`](crate::buffer::BufferCell::commit).
    ///
    /// A UI mutation is therefore a witnessed cell mutation: it advances the cell's
    /// nonce (the revision) and appends a real receipt to the world's provenance —
    /// no conservation moves (the §3.5 stream weight class). A refusal changes
    /// NOTHING. Returns the new revision.
    pub fn commit(&self, world: &mut World) -> Result<u64, ViewError> {
        if world.ledger().get(&self.backing).is_none() {
            return Err(ViewError::Unbacked);
        }
        let focus_fe = self.doc.focus.map(|f| *f.as_bytes()).unwrap_or(FOCUS_NONE);
        let idx_fe = pack_u64(self.doc.present_idx as u64);
        // Two SetField effects in ONE turn — focus + lens land atomically.
        let turn = world.turn(
            self.backing,
            vec![
                world::set_field(self.backing, VIEW_FOCUS_SLOT, focus_fe),
                world::set_field(self.backing, VIEW_PRESENT_IDX_SLOT, idx_fe),
            ],
        );
        match world.commit_turn(turn) {
            crate::CommitOutcome::Committed { .. } => Ok(self.revision(world)),
            crate::CommitOutcome::Rejected { reason, .. } => {
                Err(ViewError::ExecutorRejected(reason))
            }
            // The world is SUSPENDED (the meta-debug Suspend gate halts the loop):
            // the re-aim was STAGED, not yet witnessed. The free draft already moved
            // (the panel reflects the operator's aim); the witnessed state catches up
            // when the loop resumes. Honest, not a refusal.
            crate::CommitOutcome::Queued { .. } => Err(ViewError::Queued),
        }
    }
}

/// Why a view-cell commit did not land (fail-closed — a non-landing changes the
/// witnessed cell NOTHING; the free draft is unaffected).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ViewError {
    /// The backing cell is gone from the ledger (a dangling view).
    Unbacked,
    /// The `SetField` turn was REJECTED by the real executor (its `Permissions` /
    /// whole-turn guarantees fired). Carries the executor's reason.
    ExecutorRejected(String),
    /// The world is SUSPENDED — the re-aim was STAGED in the pending queue (the
    /// Suspend gate, FIRMAMENT-REFLEXIVE-SUBSTRATE §3); it witnesses on `resume`.
    Queued,
}

// ===========================================================================
// The keystone: a ViewCell is itself Presentable — inspect the inspector.
// ===========================================================================

impl Presentable for ViewCell {
    fn object_kind(&self) -> ObjectKind {
        // A UI cell is, at bottom, a real ledger cell.
        ObjectKind::Cell
    }

    /// PURE: project the view's COMMITTED (prior-frame) camera-aim. This is the
    /// load-bearing M3 invariant — `present` observes the witnessed cell state, it
    /// does NOT mutate the draft and never confers authority. Reading the committed
    /// (not the live draft) aim is the unit-delay that breaks the reflexive
    /// self-cycle (STRATIFIED-FIXPOINT §7.3): the projector reads the prior frame.
    fn present(&self, ctx: &PresentCtx) -> Vec<Presentation> {
        // The committed aim is the prior-frame state; the visible draft is what
        // the operator is mid-editing. We show BOTH (the witnessed truth + the
        // uncommitted draft) so the inspector tells the dirty story honestly.
        let committed = self.committed_aim(ctx.world);
        let revision = self.revision(ctx.world);
        let backed = committed.is_some();
        let clean = self.is_clean(ctx.world);

        let mut fields: Vec<Field> = vec![
            Field::id("backing", *self.backing.as_bytes()),
            Field::text("name", self.name.clone()),
            Field::count("revision", revision),
            Field::boolean("backed", backed),
            Field::boolean("clean (no uncommitted re-aim)", clean),
        ];
        // The COMMITTED (witnessed, prior-frame) camera-aim — what `present` reads.
        match committed.as_ref().and_then(|a| a.focus) {
            Some(f) => fields.push(Field::id("committed_focus", *f.as_bytes())),
            None => fields.push(Field::text("committed_focus", "(none)".to_string())),
        }
        fields.push(Field::count(
            "committed_present_idx",
            committed.as_ref().map(|a| a.present_idx as u64).unwrap_or(0),
        ));
        // The visible DRAFT (the uncommitted aim — what the operator is mid-move on).
        match self.doc.focus {
            Some(f) => fields.push(Field::id("draft_focus", *f.as_bytes())),
            None => fields.push(Field::text("draft_focus", "(none)".to_string())),
        }
        fields.push(Field::count("draft_present_idx", self.doc.present_idx as u64));

        let insp = Inspectable {
            kind: ObjectKind::Cell,
            title: format!("ViewCell · {}", self.name),
            subtitle: format!(
                "rev {revision} · {} · backing {}",
                if clean { "clean" } else { "dirty" },
                reflect::short_hex(self.backing.as_bytes())
            ),
            fields,
        };

        vec![Presentation {
            kind: PresentationKind::RawFields,
            label: "View State".to_string(),
            search_text: PresentationBody::Fields(insp.clone()).search_text(),
            body: PresentationBody::Fields(insp),
        }]
    }
}

// ===========================================================================
// WIDEN: the WorkspaceCell subgraph — the cockpit's semantic UI state as a cell.
// ===========================================================================

/// The state slot the workspace's ACTIVE-TAB index rides in (a `u64` index into
/// the cockpit's [`Tab`] order).
pub const WORKSPACE_TAB_SLOT: usize = 2;

/// The state slot the workspace's TORN-OFF-TABS bitset rides in: bit `i` set ⟺ the
/// tab at index `i` is currently popped out into its own OS window. A `u64` (the low
/// 8 bytes of the field element, little-endian — the same [`pack_u64`] layout as the
/// active tab) covers all 30-ish [`Tab`] indices with room to spare. This is the
/// RESTORATION cell: it survives a crash-relaunch exactly as the active tab does
/// (it lands a real `SetField` turn, replayed from the durable image), so a reopen
/// re-pops the windows that were torn off. Bounds are not packed here — a reopen
/// re-centers each window (the migration's `Bounds::centered` default); WHICH tabs
/// were torn off is the durable state.
pub const WORKSPACE_TORN_SLOT: usize = 4;

/// THE WORKSPACE CELL — the cockpit's wider semantic UI state as a real cell:
/// the active tab (the 24-arm `Tab` *selector*, §3.4). The same two-tier split as
/// [`ViewCell`]: a free in-memory draft (`active_tab` index) + an occasional
/// witnessed `SetField` commit. The cockpit's `render()` reads its tab selector
/// FROM this cell (`render(workspace_subgraph)`) — only the *selector* moves from
/// a Rust field to a cell read; the 24-arm match stays. It composes a child
/// [`ViewCell`] per inspector view (the workspace SUBGRAPH).
#[derive(Clone, Debug)]
pub struct WorkspaceCell {
    /// The backing cell whose state holds the active-tab index + whose nonce is
    /// the workspace's revision.
    backing: CellId,
    /// The visible active-tab index (the free draft selector).
    active_tab: usize,
    /// The visible TORN-OFF-TABS bitset (the free draft): bit `i` ⟺ tab `i` is
    /// popped out into its own OS window. The witnessed copy rides
    /// [`WORKSPACE_TORN_SLOT`]; a tear-off/pop-back sets a bit then [`Self::commit`]s
    /// (the §3.5 stream weight class), so the pop-out set survives a crash-relaunch.
    torn: u64,
}

impl WorkspaceCell {
    /// Open a workspace cell over `backing` with `active_tab` selected and NO tabs
    /// torn off.
    pub fn new(backing: CellId, active_tab: usize) -> Self {
        WorkspaceCell { backing, active_tab, torn: 0 }
    }

    /// Open a workspace cell whose free draft is RESTORED from the backing cell's
    /// witnessed state on `world` (the active tab + the torn-off-tabs bitset). The
    /// crash-relaunch seam: a reopened image rebuilds the workspace cell from the
    /// durable ledger, so the cockpit knows which tab is active AND which tabs were
    /// popped out. Falls back to `(0, no tabs torn)` if the backing cell is absent.
    pub fn from_world(world: &World, backing: CellId) -> Self {
        let probe = WorkspaceCell { backing, active_tab: 0, torn: 0 };
        let active_tab = probe.committed_tab(world).unwrap_or(0);
        let torn = probe.committed_torn(world);
        WorkspaceCell { backing, active_tab, torn }
    }

    /// The backing cell id (the authenticated anchor).
    pub fn backing(&self) -> CellId {
        self.backing
    }

    /// The visible active-tab index (the free draft).
    pub fn active_tab(&self) -> usize {
        self.active_tab
    }

    /// FREE: select tab `idx` (in-memory only — the ledger is untouched until
    /// [`Self::commit`]).
    pub fn set_active_tab(&mut self, idx: usize) {
        self.active_tab = idx;
    }

    /// The visible TORN-OFF-TABS bitset (the free draft): bit `i` ⟺ tab `i` is
    /// popped out into its own window.
    pub fn torn_bits(&self) -> u64 {
        self.torn
    }

    /// Whether tab `idx` is marked torn off in the visible draft.
    pub fn is_torn(&self, idx: usize) -> bool {
        idx < 64 && (self.torn & (1u64 << idx)) != 0
    }

    /// FREE: mark/unmark tab `idx` as torn off (in-memory only — the ledger is
    /// untouched until [`Self::commit`]). A tab index ≥ 64 is ignored (the bitset is
    /// a `u64`; the [`Tab`] order is far smaller).
    pub fn set_torn(&mut self, idx: usize, torn: bool) {
        if idx >= 64 {
            return;
        }
        if torn {
            self.torn |= 1u64 << idx;
        } else {
            self.torn &= !(1u64 << idx);
        }
    }

    /// The indices of every tab marked torn off in the visible draft (low→high),
    /// the set a crash-relaunch re-pops.
    pub fn torn_indices(&self) -> Vec<usize> {
        (0..64).filter(|&i| self.is_torn(i)).collect()
    }

    /// The COMMITTED (witnessed, prior-frame) active-tab index the backing cell
    /// stores. `None` iff the backing cell is gone.
    pub fn committed_tab(&self, world: &World) -> Option<usize> {
        world
            .ledger()
            .get(&self.backing)
            .map(|c| unpack_u64(&c.state.fields[WORKSPACE_TAB_SLOT]) as usize)
    }

    /// The COMMITTED (witnessed) torn-off-tabs bitset the backing cell stores — the
    /// durable pop-out set a reopen restores. `0` (nothing torn off) if the backing
    /// cell is gone.
    pub fn committed_torn(&self, world: &World) -> u64 {
        world
            .ledger()
            .get(&self.backing)
            .map(|c| unpack_u64(&c.state.fields[WORKSPACE_TORN_SLOT]))
            .unwrap_or(0)
    }

    /// The committed (witnessed) torn-off tab indices — what a crash-relaunch
    /// re-pops out into their own windows.
    pub fn committed_torn_indices(&self, world: &World) -> Vec<usize> {
        let bits = self.committed_torn(world);
        (0..64).filter(|i| (bits & (1u64 << i)) != 0).collect()
    }

    /// The workspace's revision (the backing cell's nonce).
    pub fn revision(&self, world: &World) -> u64 {
        world
            .ledger()
            .get(&self.backing)
            .map(|c| c.state.nonce())
            .unwrap_or(0)
    }

    /// Whether the visible selector AND the torn-off-tabs bitset match the committed
    /// ones (no uncommitted tab move and no uncommitted tear-off/pop-back).
    pub fn is_clean(&self, world: &World) -> bool {
        self.committed_tab(world) == Some(self.active_tab)
            && self.committed_torn(world) == self.torn
    }

    /// **COMMIT THE WORKSPACE STATE** — write the active-tab index AND the
    /// torn-off-tabs bitset into the backing cell through a REAL `Effect::SetField`
    /// turn (the §3.5 stream weight class: witnessed, conserves nothing). Both
    /// fields land atomically in one turn, so the active tab and the pop-out set are
    /// always consistent in the durable image. Returns the new revision.
    pub fn commit(&self, world: &mut World) -> Result<u64, ViewError> {
        if world.ledger().get(&self.backing).is_none() {
            return Err(ViewError::Unbacked);
        }
        let turn = world.turn(
            self.backing,
            vec![
                world::set_field(
                    self.backing,
                    WORKSPACE_TAB_SLOT,
                    pack_u64(self.active_tab as u64),
                ),
                world::set_field(self.backing, WORKSPACE_TORN_SLOT, pack_u64(self.torn)),
            ],
        );
        match world.commit_turn(turn) {
            crate::CommitOutcome::Committed { .. } => Ok(self.revision(world)),
            crate::CommitOutcome::Rejected { reason, .. } => {
                Err(ViewError::ExecutorRejected(reason))
            }
            crate::CommitOutcome::Queued { .. } => Err(ViewError::Queued),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::presentable::{FocusTarget, Registry};
    use crate::world::{transfer, World};

    /// A world with a treasury (1_000), a sink (0), and a fresh UI backing cell.
    fn world_with_ui_cell() -> (World, CellId, CellId, CellId) {
        let mut w = World::new();
        let treasury = w.genesis_cell(0x11, 1_000);
        let sink = w.genesis_cell(0x22, 0);
        let ui = w.genesis_cell(0x5E, 0); // the inspector's own backing cell
        (w, treasury, sink, ui)
    }

    // ── FREE re-aim does not touch the ledger ───────────────────────────────

    #[test]
    fn re_aiming_the_draft_is_free_and_does_not_touch_the_ledger() {
        let (w, treasury, _sink, ui) = world_with_ui_cell();
        let mut view = ViewCell::new(ui, "INSPECTOR");
        let h0 = w.height();
        view.doc_mut().set_focus(Some(treasury));
        view.doc_mut().set_present_idx(2);
        assert_eq!(w.height(), h0, "an in-memory re-aim does not advance the ledger");
        assert_eq!(view.doc().focus(), Some(treasury));
        assert_eq!(view.doc().present_idx(), 2);
    }

    // ── THE WITNESSED LANDING: a re-aim commits as a real turn ──────────────

    #[test]
    fn a_re_aim_commits_as_a_real_witnessed_turn() {
        // A UI mutation (re-focus) is a witnessed cell mutation: the SetField turn
        // advances the backing cell's nonce + appends a receipt (the §3.5 stream
        // weight class — witnessed, conserves nothing).
        let (mut w, treasury, _sink, ui) = world_with_ui_cell();
        let mut view = ViewCell::new(ui, "INSPECTOR");
        view.doc_mut().set_focus(Some(treasury));
        view.doc_mut().set_present_idx(3);

        assert!(!view.is_clean(&w), "an uncommitted re-aim is dirty");
        let h0 = w.height();
        let r0 = w.receipts().len();
        let rev = view.commit(&mut w).expect("the re-aim commits");
        assert!(rev >= 1, "the revision advanced (the backing cell's nonce)");
        assert_eq!(w.height(), h0 + 1, "a real turn was committed");
        assert_eq!(w.receipts().len(), r0 + 1, "a receipt was appended (provenance)");

        // The committed (witnessed) aim now equals the draft → clean.
        assert!(view.is_clean(&w), "after commit the view is clean");
        let aim = view.committed_aim(&w).unwrap();
        assert_eq!(aim.focus, Some(treasury));
        assert_eq!(aim.present_idx, 3);
    }

    // ── KEYSTONE: a ViewCell is Presentable — inspect the inspector ─────────

    #[test]
    fn focusing_a_view_cell_yields_a_real_presentation_set() {
        // THE REFLEXIVE LOOP: open the inspector ON a ViewCell. The ViewCell is
        // itself Presentable, so `present` yields a real presentation set carrying
        // its (focus, present_idx, revision) — inspect the inspector.
        let (mut w, treasury, _sink, ui) = world_with_ui_cell();
        let mut view = ViewCell::new(ui, "INSPECTOR");
        view.doc_mut().set_focus(Some(treasury));
        view.commit(&mut w).expect("commit the aim");

        let ctx = PresentCtx::new(&w, ui);
        let set = view.present(&ctx);
        assert!(!set.is_empty(), "a ViewCell yields a real presentation set");
        let raw = set
            .iter()
            .find(|p| p.kind == PresentationKind::RawFields)
            .expect("the RawFields floor is present");
        match &raw.body {
            PresentationBody::Fields(i) => {
                // The committed focus is the treasury (the witnessed aim).
                assert!(
                    i.fields.iter().any(|f| f.key == "committed_focus"),
                    "the view's committed focus is presented"
                );
                assert!(
                    i.fields.iter().any(|f| f.key == "revision"),
                    "the view's revision (nonce) is presented"
                );
            }
            other => panic!("ViewCell RawFields must carry a Fields body, got {other:?}"),
        }
    }

    // ── the reflexive loop through the Registry / FocusTarget::ViewCell ─────

    #[test]
    fn the_registry_resolves_a_view_cell_focus_to_its_presentation_set() {
        // THE ONE-ARM EXTENSION: FocusTarget::ViewCell resolves through the SAME
        // Registry::present dispatch — focusing the inspector on a ViewCell (the
        // inspector inspecting itself) goes through the identical pure projection.
        let (mut w, treasury, _sink, ui) = world_with_ui_cell();
        let mut view = ViewCell::new(ui, "INSPECTOR");
        view.doc_mut().set_focus(Some(treasury));
        view.doc_mut().set_present_idx(1);
        view.commit(&mut w).expect("commit the aim");

        let reg = Registry::new(&w);
        let set = reg
            .present(FocusTarget::ViewCell(ui), ui)
            .expect("the ViewCell focus resolves to a presentation set");
        assert!(set.iter().any(|p| p.kind == PresentationKind::RawFields));
        // The focus anchors on the backing cell id.
        assert_eq!(FocusTarget::ViewCell(ui).cell(), ui);
    }

    // ── present is PURE: it reads the COMMITTED (prior-frame) aim, unit-delay ─

    #[test]
    fn present_reads_the_committed_prior_frame_aim_not_the_live_draft() {
        // THE UNIT-DELAY / PURITY INVARIANT: `present` observes the WITNESSED
        // (committed) aim, never the uncommitted live draft. So a free re-aim that
        // has NOT yet committed does not change what `present` shows — the cycle is
        // broken by reading the prior frame, and `present` confers no authority.
        let (mut w, treasury, sink, ui) = world_with_ui_cell();
        let mut view = ViewCell::focused(ui, "INSPECTOR", treasury);
        view.commit(&mut w).expect("commit the initial aim (focus=treasury)");

        // Re-aim the DRAFT to the sink, but do NOT commit.
        view.doc_mut().set_focus(Some(sink));
        assert_eq!(view.doc().focus(), Some(sink), "the draft moved");

        // `present` still shows the COMMITTED (prior-frame) focus = treasury.
        let ctx = PresentCtx::new(&w, ui);
        let set = view.present(&ctx);
        let raw = &set[0];
        if let PresentationBody::Fields(i) = &raw.body {
            let committed = i
                .fields
                .iter()
                .find(|f| f.key == "committed_focus")
                .expect("committed_focus present");
            // The committed focus is still the treasury (the prior frame), proving
            // `present` does not read the uncommitted draft (unit-delay).
            match committed.value {
                reflect::FieldValue::Id(id) => {
                    assert_eq!(id, *treasury.as_bytes(), "present reads the prior-frame committed focus");
                }
                ref other => panic!("committed_focus should be an Id, got {other:?}"),
            }
        } else {
            panic!("expected a Fields body");
        }
    }

    // ── the committed aim survives a world advance (it IS witnessed state) ───

    #[test]
    fn the_committed_aim_is_real_ledger_state_and_survives_advances() {
        let (mut w, treasury, sink, ui) = world_with_ui_cell();
        let view = ViewCell::focused(ui, "INSPECTOR", treasury);
        view.commit(&mut w).expect("commit the aim");
        // An unrelated turn advances the world.
        let turn = w.turn(treasury, vec![transfer(treasury, sink, 10)]);
        assert!(w.commit_turn(turn).is_committed());
        // The view's committed aim is unchanged — it is real witnessed cell state.
        let aim = view.committed_aim(&w).expect("the backing cell is live");
        assert_eq!(aim.focus, Some(treasury), "the witnessed aim survives an advance");
    }

    // ── WIDEN: the WorkspaceCell tab selector is cell-backed ────────────────

    #[test]
    fn the_workspace_cell_tab_selector_is_witnessed() {
        // The cockpit's active-tab SELECTOR moves from a Rust field to a cell read:
        // a tab switch is a witnessed SetField turn (the §3.5 stream weight class).
        let (mut w, _treasury, _sink, ui) = world_with_ui_cell();
        let mut ws = WorkspaceCell::new(ui, 0);
        ws.set_active_tab(5);
        assert!(!ws.is_clean(&w), "an uncommitted tab move is dirty");
        let h0 = w.height();
        let rev = ws.commit(&mut w).expect("the tab move commits");
        assert!(rev >= 1);
        assert_eq!(w.height(), h0 + 1, "a real turn landed the tab move");
        assert_eq!(ws.committed_tab(&w), Some(5), "render() reads the tab from the cell");
        assert!(ws.is_clean(&w), "after commit the workspace is clean");
    }

    // ── RESTORATION: the torn-off-tabs bitset survives a relaunch ───────────

    #[test]
    fn the_torn_off_tabs_bitset_is_witnessed_and_restored_from_the_cell() {
        // THE POP-OUT RESTORATION (in-world relaunch): tearing off tabs sets bits in
        // the WorkspaceCell's torn-off bitset and commits them (the §3.5 stream weight
        // class). Rebuilding the cell from the world (`from_world` — the relaunch seam)
        // reads those bits back: the cockpit knows WHICH tabs to re-pop.
        let (mut w, _treasury, _sink, ui) = world_with_ui_cell();
        let mut ws = WorkspaceCell::new(ui, 0);
        // Tear off tabs 3 and 21 (the editor/terminal indices in a real cockpit).
        ws.set_torn(3, true);
        ws.set_torn(21, true);
        assert!(!ws.is_clean(&w), "an uncommitted tear-off is dirty");
        ws.commit(&mut w).expect("the tear-off set commits");
        assert!(ws.is_clean(&w), "after commit the workspace is clean");
        assert_eq!(ws.committed_torn_indices(&w), vec![3, 21], "the witnessed pop-out set");

        // RELAUNCH (rebuild from the durable cell): the torn set comes back.
        let restored = WorkspaceCell::from_world(&w, ui);
        assert_eq!(
            restored.torn_indices(),
            vec![3, 21],
            "a relaunch restores the torn-off tabs from the cell"
        );
        assert!(restored.is_torn(3) && restored.is_torn(21));
        assert!(!restored.is_torn(0), "tabs that were not torn off stay docked");
    }

    #[test]
    fn popping_a_tab_back_clears_its_bit_and_the_relaunch_no_longer_re_pops_it() {
        let (mut w, _treasury, _sink, ui) = world_with_ui_cell();
        let mut ws = WorkspaceCell::new(ui, 0);
        ws.set_torn(5, true);
        ws.set_torn(9, true);
        ws.commit(&mut w).expect("commit two pop-outs");

        // Pop tab 5 back into the dock (clear its bit + witness).
        ws.set_torn(5, false);
        ws.commit(&mut w).expect("commit the pop-back");

        let restored = WorkspaceCell::from_world(&w, ui);
        assert_eq!(restored.torn_indices(), vec![9], "only the still-torn tab re-pops");
    }

    #[test]
    fn a_genuine_durable_relaunch_restores_the_torn_off_windows() {
        // THE REAL CRASH-RELAUNCH: build a DURABLE image, tear off tabs (a witnessed
        // SetField turn dual-writes to the store), DROP the world (the "crash"), then
        // REOPEN the image off disk and assert the torn-off tabs come back. This is the
        // genuine restoration path — recovery replays the SetField turn, so the reopened
        // WorkspaceCell carries the pop-out set. (Bounds default on reopen; WHICH tabs
        // were torn off is the durable state.)
        use crate::world::make_open_cell;
        use dregg_turn::ComputronCosts;

        // A deterministic scratch image path + a pinned clock (so recovery re-derives).
        const RTS: i64 = 1_700_000_000;
        let dir = std::env::temp_dir().join(format!(
            "sbv2-tearoff-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .map(|d| d.as_nanos())
                .unwrap_or(0)
        ));
        std::fs::create_dir_all(&dir).expect("scratch dir");
        let path = dir.join("image");

        // The workspace backing cell's id is DERIVED from its genesis seed, so it is
        // the SAME id across the first launch and the reopen — the cell the cockpit
        // re-creates with `genesis_cell(0x5F, …)` each boot.
        let backing = make_open_cell(0x5F, 0).id();

        // FIRST LAUNCH: open a durable image, genesis the backing cell, tear off tabs
        // 3 + 21, commit (dual-writes to the store).
        {
            let mut w = World::open_with_timestamp(&path, ComputronCosts::zero(), RTS)
                .expect("open a fresh durable image");
            assert!(w.is_durable(), "the image is durable");
            let id = w.genesis_cell(0x5F, 0);
            assert_eq!(id, backing, "the workspace backing id is seed-deterministic");
            let mut ws = WorkspaceCell::new(backing, 0);
            ws.set_active_tab(7);
            ws.set_torn(3, true);
            ws.set_torn(21, true);
            ws.commit(&mut w).expect("the tear-off + active-tab commit dual-writes");
            assert_eq!(ws.committed_torn_indices(&w), vec![3, 21]);
            // …and the world drops here — the "crash".
        }

        // RELAUNCH: reopen the SAME image off disk; recovery replays the SetField turn.
        {
            let w = World::open_with_timestamp(&path, ComputronCosts::zero(), RTS)
                .expect("reopen the durable image");
            // Re-create the workspace cell over the SAME (re-genesis'd by recovery)
            // backing id and restore from the recovered ledger.
            let restored = WorkspaceCell::from_world(&w, backing);
            assert_eq!(
                restored.committed_tab(&w),
                Some(7),
                "the active tab survives the relaunch (as it did before)"
            );
            assert_eq!(
                restored.torn_indices(),
                vec![3, 21],
                "the TORN-OFF WINDOWS are restored from the durable image after a relaunch"
            );
        }

        let _ = std::fs::remove_dir_all(&dir);
    }

    // ── WIDEN: the cockpit's active-tab resolution path (cell-driven selector) ──

    #[test]
    fn the_active_tab_resolves_from_the_committed_cell_not_the_draft() {
        // This mirrors the cockpit's `active_tab()` widen: the render dispatch reads
        // the active tab from the WorkspaceCell's COMMITTED index (a cell read), not
        // the free draft. A free tab move that has NOT committed leaves the witnessed
        // selector at the prior index — the §3.4 `render(workspace_subgraph)` source.
        let (mut w, _treasury, _sink, ui) = world_with_ui_cell();
        let mut ws = WorkspaceCell::new(ui, 3);
        ws.commit(&mut w).expect("commit the boot tab index (3)");
        assert_eq!(ws.committed_tab(&w), Some(3), "the witnessed selector is index 3");

        // Move the FREE draft to index 7 but do NOT commit (a free tab switch).
        ws.set_active_tab(7);
        assert_eq!(ws.active_tab(), 7, "the free draft moved");
        assert_eq!(
            ws.committed_tab(&w),
            Some(3),
            "render() still dispatches on the COMMITTED index (3) until the witness lands"
        );

        // Witness it (the occasional commit `witness_tab` lands) → the cell read catches up.
        ws.commit(&mut w).expect("witness the tab move");
        assert_eq!(ws.committed_tab(&w), Some(7), "after the witness, render() reads index 7");
    }

    #[test]
    fn a_missing_workspace_cell_has_no_committed_tab_so_render_falls_to_the_draft() {
        // The cockpit's `active_tab()` degrades to the live `self.tab` draft when the
        // backing cell is absent (never the boot path) — so the cockpit is never blank.
        let mut w = World::new();
        let ghost = CellId::from_bytes([0x77; 32]); // never installed
        let ws = WorkspaceCell::new(ghost, 4);
        assert!(ws.committed_tab(&w).is_none(), "a missing cell has no committed tab");
        assert!(!ws.is_clean(&w), "an unbacked workspace cell is not clean");
        assert!(matches!(ws.commit(&mut w), Err(ViewError::Unbacked)), "it cannot commit");
    }

    // ── a view over a missing cell is unbacked and cannot commit ────────────

    #[test]
    fn a_view_over_a_missing_cell_is_unbacked() {
        let mut w = World::new();
        let ghost = CellId::from_bytes([0x99; 32]); // never installed
        let view = ViewCell::new(ghost, "ghost");
        assert!(view.committed_aim(&w).is_none(), "a missing cell has no committed aim");
        assert!(!view.is_clean(&w), "an unbacked view is not clean");
        let r = view.commit(&mut w);
        assert!(matches!(r, Err(ViewError::Unbacked)), "a dangling view cannot commit, got {r:?}");
    }
}
