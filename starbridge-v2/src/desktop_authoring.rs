//! DESKTOP AUTHORING — making the desktop-as-document EDITABLE as a witnessed,
//! rewindable object (hyperdreggmedia authoring surface #6,
//! `docs/deos/HYPERDREGGMEDIA-NOTES.md §6`).
//!
//! [`view_cell::WorkspaceCell`](crate::view_cell::WorkspaceCell) already proved
//! the desktop's LAYOUT is durable witnessed state — but only for the bits it
//! models: the active tab (`WORKSPACE_TAB_SLOT`) and a torn-off-tabs *bitset*
//! (`WORKSPACE_TORN_SLOT`). It does NOT model an ordered list of arbitrary
//! windows or their z-order. The arbitrary-window / embed-order reading lives in
//! [`desktop_doc`](crate::desktop_doc) / `dregg_doc::composition` as a
//! `LayoutGraph` of `Op::Embed` atoms — but THAT graph is in-memory only; it is
//! not witnessed into a cell, so editing it leaves no receipt and does not
//! rewind.
//!
//! This module closes that gap **minimally**, reusing the EXACT machinery
//! [`WorkspaceCell`](crate::view_cell::WorkspaceCell) uses (the same two-tier
//! split: a free in-memory draft + an occasional witnessed `Effect::SetField`
//! commit on a backing layout cell). It extends the witnessed-layout idea — not
//! by widening `WorkspaceCell`, which stays untouched — by committing a
//! light-client-checkable **layout commitment** of the *ordered window list*
//! into a fresh state slot:
//!
//!   * [`DesktopAuthoring`] — the gpui-free logic core over the desktop layout
//!     cell. Its free draft is an ordered [`Vec`] of [`WindowSpec`] (the window
//!     owner cell + z metadata), exactly the renderer-agnostic surface shape
//!     [`desktop_doc`](crate::desktop_doc) projects through the `Op::Embed`
//!     algebra. Mutating the draft is FREE (no ledger cost); the witnessed
//!     landing is the commit.
//!   * [`DesktopAuthoring::open`] / [`close`](DesktopAuthoring::close) /
//!     [`raise`](DesktopAuthoring::raise) / [`lower`](DesktopAuthoring::lower)
//!     — each a layout-edit TURN: it mutates the ordered draft, derives the new
//!     `dregg_doc::desktop::desktop_commit` of the ordered window list, and
//!     writes it into [`LAYOUT_COMMIT_SLOT`] through a REAL `Effect::SetField`
//!     turn on the backing cell (the same `TurnExecutor` every other dregg
//!     effect runs). So opening/closing/reordering a window advances the cell's
//!     nonce and appends a receipt — the desktop *layout itself* is a witnessed,
//!     rewindable, branchable object.
//!   * [`DesktopAuthoring::layout`] reads the ordered window list (the draft);
//!     [`DesktopAuthoring::from_world`] rebuilds the cell's witnessed layout
//!     commitment off the durable ledger (the crash-relaunch seam — the layout
//!     commitment survives a round-trip exactly as the active tab does).
//!
//! The z-order IS the layout (draft) order: front-to-back = first-to-last in the
//! ordered list, so [`raise`](DesktopAuthoring::raise) moves a window toward the
//! front and [`lower`](DesktopAuthoring::lower) toward the back — a reorder that
//! is a real turn, not a free Rust-field shuffle.
//!
//! gpui-FREE and `cargo test`-able exactly as [`crate::view_cell`] is. The
//! cockpit maps its live `compositor::CompositorScene` onto a [`DesktopAuthoring`]
//! draft (each `CompositedSurface` → a [`WindowSpec`]) and authors the desktop
//! through this core; the committed commitment is the agreement two parties
//! check (a forged window changes it — the anti-forge tooth inherited from the
//! document, `desktop_doc.rs`).

use dregg_cell::{CellId, FieldElement};
use dregg_doc::desktop::{self as doc_desktop, DesktopSurface};
use dregg_doc::Author;

use crate::world::{self, World};

/// The state slot the backing LAYOUT cell carries the witnessed **layout
/// commitment** in: the 32-byte `dregg_doc::desktop::desktop_commit` of the
/// current ordered window list (the heap root two parties agree on iff they see
/// the same desktop). A layout edit (open/close/raise/lower) advances the cell's
/// `source_state_root` here, exactly as a `WorkspaceCell` tab move advances
/// [`WORKSPACE_TAB_SLOT`](crate::view_cell::WORKSPACE_TAB_SLOT). Chosen distinct
/// from the `WorkspaceCell` slots (`WORKSPACE_TAB_SLOT = 2`,
/// `WORKSPACE_TORN_SLOT = 4`) so the same backing cell could carry BOTH a tab
/// selector and a window-layout commitment without aliasing.
pub const LAYOUT_COMMIT_SLOT: usize = 5;

/// The all-zero element — the EMPTY-layout sentinel for [`LAYOUT_COMMIT_SLOT`]
/// (a cell that has never committed a layout, or whose layout is empty AND has
/// the same commit as the empty desktop, reads its commitment directly).
const COMMIT_NONE: FieldElement = [0u8; 32];

/// The author the layout-document projection binds into its commitment (the
/// owning operator's own desktop). A different author => a different commitment,
/// so a layout is attributable. Matches `desktop_doc.rs`'s `Author(1)` default
/// for the owning operator's full-authority view.
const LAYOUT_AUTHOR: Author = Author(1);

// ===========================================================================
// The free in-memory draft: an ordered window list (the layout-as-document).
// ===========================================================================

/// One window in the desktop layout — the gpui-free, renderer-agnostic shape a
/// live `compositor::CompositedSurface` maps onto. Carries the OWNER cell (the
/// authority lineage the layout commitment binds — a window cannot describe a
/// cell it does not own without changing the commitment), the cell state-root +
/// frame digest it projects, and whether it holds focus. Its z-order is its
/// POSITION in the ordered draft (not a field here), so a reorder is a list
/// move, witnessed by re-committing the whole ordered list.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct WindowSpec {
    /// The owning cell's id — the window IS an embed of this cell.
    pub owner: CellId,
    /// The cell state-root this window is a genuine projection of.
    pub source_state_root: u64,
    /// The frame digest currently shown.
    pub content_digest: u64,
    /// Whether this window holds input focus (at most one, the focus-exclusive
    /// gate — the core does not enforce it, the cockpit's compositor does).
    pub focus: bool,
}

impl WindowSpec {
    /// A window onto `owner`, projecting `(source_state_root, content_digest)`,
    /// unfocused.
    pub fn new(owner: CellId, source_state_root: u64, content_digest: u64) -> Self {
        WindowSpec {
            owner,
            source_state_root,
            content_digest,
            focus: false,
        }
    }

    /// This window holding focus.
    pub fn focused(mut self) -> Self {
        self.focus = true;
        self
    }
}

/// Project one [`WindowSpec`] at paint layer `z` onto the renderer-agnostic
/// [`DesktopSurface`] the document commitment is computed over. The z-layer is
/// derived from the window's POSITION in the ordered draft (front = highest z),
/// so the ordered list IS the z-order and a reorder changes the commitment.
fn to_surface(w: &WindowSpec, z: i64) -> DesktopSurface {
    DesktopSurface {
        owner: *w.owner.as_bytes(),
        source_state_root: w.source_state_root,
        content_digest: w.content_digest,
        z_layer: z,
        focus_flag: w.focus,
    }
}

/// The ordered draft [`WindowSpec`]s as paint-order [`DesktopSurface`]s. The
/// FIRST window is front-most (highest z); the layout walk descends to the back.
/// This pins the z-order to the list order, so `raise`/`lower` (list moves) move
/// a window in paint order — and the commitment over these surfaces changes.
fn surfaces_of(windows: &[WindowSpec]) -> Vec<DesktopSurface> {
    let n = windows.len() as i64;
    windows
        .iter()
        .enumerate()
        // Front (index 0) gets the highest z; back gets the lowest.
        .map(|(i, w)| to_surface(w, n - 1 - i as i64))
        .collect()
}

/// The witnessed **layout commitment** of an ordered window list — the
/// `dregg_doc::desktop::desktop_commit` heap root two parties agree on iff they
/// see the same desktop (the anti-forge tooth: a forged/added/reordered window
/// changes it). This is the value [`DesktopAuthoring::commit`] writes into
/// [`LAYOUT_COMMIT_SLOT`]. The active-tab argument is folded as `0` here — the
/// arbitrary-window layout is the concern; a `WorkspaceCell` carries the tab
/// selector separately (see the module note on the tab-vs-window split).
pub fn layout_commit(windows: &[WindowSpec]) -> FieldElement {
    doc_desktop::desktop_commit(&surfaces_of(windows), 0, LAYOUT_AUTHOR)
}

// ===========================================================================
// The DesktopAuthoring core — the two-tier split over the layout cell.
// ===========================================================================

/// The desktop layout authoring core: an ordered window list (the free in-memory
/// draft) over a backing LAYOUT cell whose state holds the witnessed layout
/// commitment + whose nonce is the layout's revision. The
/// [`WorkspaceCell`](crate::view_cell::WorkspaceCell) pattern, generalized from a
/// tab selector + torn bitset to an ordered list of ARBITRARY windows:
///   * the visible [`WindowSpec`] list is gpui-free and FREE to reshape;
///   * its authenticated state rides the backing cell's [`LAYOUT_COMMIT_SLOT`],
///     advanced only by a real `Effect::SetField` turn;
///   * its **revision = the backing cell's nonce** — the receipt chain IS the
///     desktop's layout history (rewindable, branchable).
#[derive(Clone, Debug)]
pub struct DesktopAuthoring {
    /// The backing layout cell whose state holds the layout commitment + whose
    /// nonce is the revision. The REAL anchor in the live ledger.
    backing: CellId,
    /// The visible ordered window list (front-most first). The free draft.
    windows: Vec<WindowSpec>,
}

impl DesktopAuthoring {
    /// Open an authoring core over `backing` with an EMPTY layout (no windows).
    pub fn new(backing: CellId) -> Self {
        DesktopAuthoring {
            backing,
            windows: Vec::new(),
        }
    }

    /// Open an authoring core over `backing` whose free draft is the given
    /// ordered window list.
    pub fn with_windows(backing: CellId, windows: Vec<WindowSpec>) -> Self {
        DesktopAuthoring { backing, windows }
    }

    /// The backing layout cell id (the authenticated anchor).
    pub fn backing(&self) -> CellId {
        self.backing
    }

    /// READ: the ordered window list (front-most first) — the current layout.
    pub fn layout(&self) -> &[WindowSpec] {
        &self.windows
    }

    /// The number of windows in the current layout.
    pub fn len(&self) -> usize {
        self.windows.len()
    }

    /// Whether the layout is empty (no windows).
    pub fn is_empty(&self) -> bool {
        self.windows.is_empty()
    }

    /// The index of the window owned by `owner` in the ordered draft, if open.
    fn index_of(&self, owner: CellId) -> Option<usize> {
        self.windows.iter().position(|w| w.owner == owner)
    }

    /// FREE: add `window` to the front of the draft (front-most), or — if a
    /// window onto the same owner is already open — replace it in place (a window
    /// is identified by its owner cell). In-memory only; the ledger is untouched
    /// until [`Self::commit`]. Returns the draft index it landed at.
    pub fn open_draft(&mut self, window: WindowSpec) -> usize {
        if let Some(i) = self.index_of(window.owner) {
            self.windows[i] = window;
            i
        } else {
            self.windows.insert(0, window);
            0
        }
    }

    /// FREE: remove the window onto `owner` from the draft (if open). In-memory
    /// only. Returns whether a window was removed.
    pub fn close_draft(&mut self, owner: CellId) -> bool {
        match self.index_of(owner) {
            Some(i) => {
                self.windows.remove(i);
                true
            }
            None => false,
        }
    }

    /// FREE: move the window onto `owner` toward the FRONT by one z-step (a raise)
    /// in the draft. In-memory only. Returns whether the order changed.
    pub fn raise_draft(&mut self, owner: CellId) -> bool {
        match self.index_of(owner) {
            Some(i) if i > 0 => {
                self.windows.swap(i, i - 1);
                true
            }
            _ => false,
        }
    }

    /// FREE: move the window onto `owner` toward the BACK by one z-step (a lower)
    /// in the draft. In-memory only. Returns whether the order changed.
    pub fn lower_draft(&mut self, owner: CellId) -> bool {
        match self.index_of(owner) {
            Some(i) if i + 1 < self.windows.len() => {
                self.windows.swap(i, i + 1);
                true
            }
            _ => false,
        }
    }

    // ── THE WITNESSED LANDINGS — each a real verified turn ─────────────────

    /// **OPEN A WINDOW — a layout-edit turn.** Add `window` to the front of the
    /// layout (or replace the existing window onto the same owner), then witness
    /// the new layout by committing its commitment ([`Self::commit`]). A real
    /// `Effect::SetField` turn lands — advancing the cell's nonce + appending a
    /// receipt — so the OPEN is a witnessed, rewindable layout mutation. Returns
    /// the new revision.
    pub fn open(&mut self, window: WindowSpec, world: &mut World) -> Result<u64, LayoutError> {
        self.open_draft(window);
        self.commit(world)
    }

    /// **CLOSE A WINDOW — a layout-edit turn.** Remove the window onto `owner`,
    /// then witness the new layout (a real `SetField` turn). A close on a window
    /// that is not open is [`LayoutError::NoSuchWindow`] (fail-closed — nothing
    /// is witnessed). Returns the new revision.
    pub fn close(&mut self, owner: CellId, world: &mut World) -> Result<u64, LayoutError> {
        if !self.close_draft(owner) {
            return Err(LayoutError::NoSuchWindow);
        }
        self.commit(world)
    }

    /// **RAISE A WINDOW — a z-order layout-edit turn.** Move the window onto
    /// `owner` one step toward the front, then witness the reorder (a real
    /// `SetField` turn — the commitment changes because the surface z-layers
    /// change). A raise of an already-front-most window (or one not open) is
    /// [`LayoutError::NoReorder`] (nothing to witness). Returns the new revision.
    pub fn raise(&mut self, owner: CellId, world: &mut World) -> Result<u64, LayoutError> {
        if !self.raise_draft(owner) {
            return Err(LayoutError::NoReorder);
        }
        self.commit(world)
    }

    /// **LOWER A WINDOW — a z-order layout-edit turn.** Move the window onto
    /// `owner` one step toward the back, then witness the reorder (a real
    /// `SetField` turn). A lower of an already-back-most window (or one not open)
    /// is [`LayoutError::NoReorder`]. Returns the new revision.
    pub fn lower(&mut self, owner: CellId, world: &mut World) -> Result<u64, LayoutError> {
        if !self.lower_draft(owner) {
            return Err(LayoutError::NoReorder);
        }
        self.commit(world)
    }

    /// **COMMIT THE LAYOUT — the witnessed landing.** Write the current ordered
    /// window list's [`layout_commit`] into the backing cell's
    /// [`LAYOUT_COMMIT_SLOT`] through a REAL `Effect::SetField` turn on the
    /// embedded executor — the SAME `TurnExecutor` every other dregg effect runs,
    /// exactly like [`WorkspaceCell::commit`](crate::view_cell::WorkspaceCell::commit).
    /// A layout mutation is therefore a witnessed cell mutation: it advances the
    /// cell's nonce (the revision) and appends a real receipt (the §3.5 stream
    /// weight class — witnessed, conserves nothing). A refusal changes NOTHING.
    /// Returns the new revision.
    pub fn commit(&self, world: &mut World) -> Result<u64, LayoutError> {
        if world.ledger().get(&self.backing).is_none() {
            return Err(LayoutError::Unbacked);
        }
        let commit_fe = layout_commit(&self.windows);
        let turn = world.turn(
            self.backing,
            vec![world::set_field(
                self.backing,
                LAYOUT_COMMIT_SLOT,
                commit_fe,
            )],
        );
        match world.commit_turn(turn) {
            crate::CommitOutcome::Committed { .. } => Ok(self.revision(world)),
            crate::CommitOutcome::Rejected { reason, .. } => {
                Err(LayoutError::ExecutorRejected(reason))
            }
            crate::CommitOutcome::Queued { .. } => Err(LayoutError::Queued),
        }
    }

    /// The layout's REVISION — the backing cell's nonce, advanced by each
    /// committed layout edit. `0` for a never-committed / missing layout.
    pub fn revision(&self, world: &World) -> u64 {
        world
            .ledger()
            .get(&self.backing)
            .map(|c| c.state.nonce())
            .unwrap_or(0)
    }

    /// The COMMITTED (witnessed) layout commitment the backing cell currently
    /// stores — the prior-frame state a light client / a relaunch reads. The
    /// all-zero sentinel ([`COMMIT_NONE`]) iff the cell never committed a layout
    /// (or the backing cell is gone). Distinct from [`Self::draft_commit`]: this
    /// is the witnessed truth, that is the uncommitted draft.
    pub fn committed_commit(&self, world: &World) -> FieldElement {
        world
            .ledger()
            .get(&self.backing)
            .map(|c| c.state.fields[LAYOUT_COMMIT_SLOT])
            .unwrap_or(COMMIT_NONE)
    }

    /// The commitment of the current (uncommitted) draft window list — what a
    /// commit WOULD witness. Equals [`Self::committed_commit`] iff the layout is
    /// clean (no uncommitted edit).
    pub fn draft_commit(&self) -> FieldElement {
        layout_commit(&self.windows)
    }

    /// Whether the backing cell is present AND its committed layout commitment
    /// MATCHES the draft's commitment (no uncommitted layout edit). A draft whose
    /// commitment differs from the committed one is DIRTY.
    pub fn is_clean(&self, world: &World) -> bool {
        world.ledger().get(&self.backing).is_some()
            && self.committed_commit(world) == self.draft_commit()
    }

    /// Rebuild an authoring core over `backing` from the durable world, carrying
    /// `windows` as the draft, and CONFIRM the witnessed layout commitment off the
    /// recovered ledger matches that draft. The crash-relaunch / branch-stitch
    /// seam: a reopened image rebuilds the core and re-derives the layout
    /// commitment from the durable cell. `None` iff the backing cell is absent.
    ///
    /// The commitment (not the window list) is what survives in-cell — like a
    /// `WorkspaceCell` storing the torn-off BITSET rather than each window's
    /// bounds: WHAT the layout commits to is the durable state, and the live
    /// window list is rehydrated (here: handed in by the caller, then verified
    /// against the witnessed commitment via [`Self::is_clean`]).
    pub fn from_world(world: &World, backing: CellId, windows: Vec<WindowSpec>) -> Option<Self> {
        world.ledger().get(&backing)?;
        Some(DesktopAuthoring { backing, windows })
    }
}

/// Why a layout edit did not land (fail-closed — a non-landing changes the
/// witnessed cell NOTHING; the free draft is unaffected unless the edit's
/// draft-mutation already ran, which the typed `open/close/raise/lower` only do
/// when they will then commit).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LayoutError {
    /// The backing layout cell is gone from the ledger (a dangling desktop).
    Unbacked,
    /// A [`close`](DesktopAuthoring::close) named a window that is not open.
    NoSuchWindow,
    /// A [`raise`](DesktopAuthoring::raise) / [`lower`](DesktopAuthoring::lower)
    /// would not change the order (the window is already at that extreme, or not
    /// open) — nothing to witness.
    NoReorder,
    /// The `SetField` turn was REJECTED by the real executor (its `Permissions` /
    /// whole-turn guarantees fired). Carries the executor's reason.
    ExecutorRejected(String),
    /// The world is SUSPENDED — the layout edit was STAGED in the pending queue
    /// (the Suspend gate); it witnesses on `resume`.
    Queued,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::world::World;

    /// A world with three window-owner cells + a layout backing cell.
    fn world_with_layout_cell() -> (World, CellId, CellId, CellId, CellId) {
        let mut w = World::new();
        let a = w.genesis_cell(0xA1, 0);
        let b = w.genesis_cell(0xB2, 0);
        let c = w.genesis_cell(0xC3, 0);
        let layout = w.genesis_cell(0x10, 0); // the desktop layout cell
        (w, a, b, c, layout)
    }

    fn win(owner: CellId, root: u64) -> WindowSpec {
        WindowSpec::new(owner, root, 100 + root)
    }

    // ── open two windows: layout() lists them, each a witnessed turn ────────

    #[test]
    fn opening_two_windows_lists_them_and_each_is_a_real_turn() {
        let (mut w, a, b, _c, layout) = world_with_layout_cell();
        let mut desk = DesktopAuthoring::new(layout);
        assert!(desk.is_empty(), "the desktop starts empty");

        let h0 = w.height();
        let r0 = w.receipts().len();

        let rev_a = desk.open(win(a, 10), &mut w).expect("open A is a turn");
        let rev_b = desk.open(win(b, 20), &mut w).expect("open B is a turn");

        // Each open advanced the ledger (a real verified turn + a receipt).
        assert_eq!(w.height(), h0 + 2, "two layout-edit turns landed");
        assert_eq!(w.receipts().len(), r0 + 2, "two receipts appended");
        assert!(rev_a >= 1 && rev_b > rev_a, "the revision advances per edit");

        // layout() lists BOTH windows; the last-opened (B) is front-most.
        let owners: Vec<CellId> = desk.layout().iter().map(|win| win.owner).collect();
        assert_eq!(owners, vec![b, a], "both windows open; B opened last is front");
        assert!(desk.is_clean(&w), "after commit the layout is clean");
    }

    // ── raise the back window → z-order changes (a turn) ────────────────────

    #[test]
    fn raising_the_back_window_changes_z_order_as_a_turn() {
        let (mut w, a, b, _c, layout) = world_with_layout_cell();
        let mut desk = DesktopAuthoring::new(layout);
        desk.open(win(a, 10), &mut w).unwrap();
        desk.open(win(b, 20), &mut w).unwrap(); // order: [B, A], A is back

        let before = desk.committed_commit(&w);
        let h0 = w.height();

        // Raise A (the back window) → it moves toward the front: [A, B].
        let rev = desk.raise(a, &mut w).expect("raise A is a turn");
        assert_eq!(w.height(), h0 + 1, "the reorder is a real turn");
        assert!(rev >= 3, "the revision advanced again");

        let owners: Vec<CellId> = desk.layout().iter().map(|win| win.owner).collect();
        assert_eq!(owners, vec![a, b], "A raised to the front");

        // The witnessed layout commitment CHANGED — a reorder is observable to a
        // light client (the z-layers in the surface set changed).
        assert_ne!(
            desk.committed_commit(&w),
            before,
            "the reorder changed the witnessed layout commitment"
        );
        assert!(desk.is_clean(&w));

        // Raising the already-front-most window is a no-op (nothing to witness).
        assert_eq!(desk.raise(a, &mut w), Err(LayoutError::NoReorder));
    }

    // ── lower mirrors raise (a turn) ────────────────────────────────────────

    #[test]
    fn lowering_the_front_window_changes_z_order_as_a_turn() {
        let (mut w, a, b, _c, layout) = world_with_layout_cell();
        let mut desk = DesktopAuthoring::new(layout);
        desk.open(win(a, 10), &mut w).unwrap();
        desk.open(win(b, 20), &mut w).unwrap(); // [B, A]

        let rev = desk.lower(b, &mut w).expect("lower B is a turn");
        assert!(rev >= 3);
        let owners: Vec<CellId> = desk.layout().iter().map(|win| win.owner).collect();
        assert_eq!(owners, vec![a, b], "B lowered to the back");
        // Lowering the already-back-most window is a no-op.
        assert_eq!(desk.lower(b, &mut w), Err(LayoutError::NoReorder));
    }

    // ── close one → it's gone (a turn) ──────────────────────────────────────

    #[test]
    fn closing_a_window_removes_it_as_a_turn() {
        let (mut w, a, b, c, layout) = world_with_layout_cell();
        let mut desk = DesktopAuthoring::new(layout);
        desk.open(win(a, 10), &mut w).unwrap();
        desk.open(win(b, 20), &mut w).unwrap();
        desk.open(win(c, 30), &mut w).unwrap(); // [C, B, A]

        let h0 = w.height();
        let rev = desk.close(b, &mut w).expect("close B is a turn");
        assert_eq!(w.height(), h0 + 1, "the close is a real turn");
        assert!(rev >= 4);

        let owners: Vec<CellId> = desk.layout().iter().map(|win| win.owner).collect();
        assert_eq!(owners, vec![c, a], "B is gone; C and A remain in order");

        // Closing a window that is not open is fail-closed (nothing witnessed).
        assert_eq!(desk.close(b, &mut w), Err(LayoutError::NoSuchWindow));
        assert!(desk.is_clean(&w));
    }

    // ── the layout survives a from_world round-trip (durable layout-as-cell) ─

    #[test]
    fn the_layout_commitment_survives_a_from_world_round_trip() {
        let (mut w, a, b, _c, layout) = world_with_layout_cell();
        let mut desk = DesktopAuthoring::new(layout);
        desk.open(win(a, 10), &mut w).unwrap();
        desk.open(win(b, 20), &mut w).unwrap(); // [B, A]
        let committed = desk.committed_commit(&w);
        assert_ne!(committed, COMMIT_NONE, "a populated layout commits non-empty");

        // REBUILD off the world with the SAME ordered window list (the relaunch
        // re-hydrates the live windows; the witnessed commitment is durable). The
        // rebuilt core is CLEAN against the durable cell — the layout-as-cell
        // round-trips, exactly as the active tab does.
        let restored =
            DesktopAuthoring::from_world(&w, layout, desk.layout().to_vec()).expect("backed");
        assert_eq!(
            restored.committed_commit(&w),
            committed,
            "the witnessed layout commitment is durable across the round-trip"
        );
        assert!(
            restored.is_clean(&w),
            "the rehydrated window list matches the witnessed commitment"
        );

        // A DIFFERENT order rehydrated against the SAME cell is DIRTY — the
        // commitment is the anti-forge tooth: a relaunch that reconstructs the
        // wrong layout is detectable, never silently accepted.
        let mut reordered = desk.layout().to_vec();
        reordered.swap(0, 1);
        let wrong = DesktopAuthoring::from_world(&w, layout, reordered).expect("backed");
        assert!(
            !wrong.is_clean(&w),
            "a mis-reconstructed layout does not match the witnessed commitment"
        );
    }

    // ── the witnessed commitment is real ledger state and survives advances ──

    #[test]
    fn the_committed_layout_survives_unrelated_world_advances() {
        let (mut w, a, b, _c, layout) = world_with_layout_cell();
        let mut desk = DesktopAuthoring::new(layout);
        desk.open(win(a, 10), &mut w).unwrap();
        let committed = desk.committed_commit(&w);

        // An unrelated transfer advances the world.
        let turn = w.turn(a, vec![world::transfer(a, b, 0)]);
        assert!(w.commit_turn(turn).is_committed());

        assert_eq!(
            desk.committed_commit(&w),
            committed,
            "the witnessed layout commitment is real cell state and survives advances"
        );
    }

    // ── a layout over a missing cell is unbacked and cannot commit ──────────

    #[test]
    fn a_layout_over_a_missing_cell_is_unbacked() {
        let mut w = World::new();
        let a = w.genesis_cell(0xA1, 0);
        let ghost = CellId::from_bytes([0x99; 32]); // never installed
        let mut desk = DesktopAuthoring::new(ghost);
        assert!(!desk.is_clean(&w), "an unbacked layout is not clean");
        assert_eq!(
            desk.open(win(a, 10), &mut w),
            Err(LayoutError::Unbacked),
            "a dangling desktop cannot commit"
        );
        assert!(
            DesktopAuthoring::from_world(&w, ghost, vec![]).is_none(),
            "from_world over a missing cell is None"
        );
    }
}
