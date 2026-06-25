//! **THE deos DESKTOP** — a Windows-NT / Pharo-Smalltalk workbench over the live
//! verified World.
//!
//! This is the answer to the cockpit's three holes: NO WAY TO ACTUATE OR COMPOSE
//! the parts, ZERO METAPHORS, ZERO SPATIAL PERSISTENCE. The desktop gives the user
//! the oldest, densest, most legible metaphors there are — a **desktop of icons**,
//! **overlapping windows**, **right-click context menus**, a **menu bar**, and a
//! reflexive **inspector** — and wires every one of them to REAL substance:
//!
//!   * **Icons ARE cells.** Each icon on the desktop is one sovereign cell read off
//!     the live `World` ledger ([`crate::world::World`]): its id, its kind, its
//!     balance/nonce/lifecycle. Drag it and it MOVES; its position is SAVED.
//!   * **Spatial persistence** (the #1 missing thing). The desktop layout — every
//!     icon position, every open window's geometry — is real state, serialized to a
//!     sidecar ([`DesktopLayout`]) and RESTORED on reopen. You arrange your world
//!     and it STAYS.
//!   * **Windows.** Double-click an icon → it opens in a movable NT window (title
//!     bar, min/max/close, a dense inspector body). Windows overlap; their geometry
//!     persists too.
//!   * **Right-click context menus** — the ACTUATION. Right-click any cell-icon → a
//!     menu of EVERY action available on it (inspect, fire its affordances as
//!     verified turns, grant a cap, transfer), lit if the cap is held, dim if not.
//!     This is Smalltalk "do it": the user actually DOES things to the parts.
//!   * **Compose** — drag one cell-icon ONTO another to act across them (transfer /
//!     grant), the dropped affordance.
//!
//! REAL UNDERNEATH: a fired action commits a real `dregg_turn` through the embedded
//! verified executor ([`crate::world::World::commit_turn`]) leaving a `TurnReceipt`;
//! the inspector shows the cell's real reflected faces; the layout persists as real
//! JSON state. Built NEW, beside the cockpit — it does not touch the cockpit tree.

// ── Submodules ────────────────────────────────────────────────────────────────────
// The desktop is split into a reusable chrome kit + a persistence layer + this glue.
//   * `chrome`  — the NT widget infrastructure (palette, bevel/face primitives,
//                 id/number formatting). The reusable component layer.
//   * `layout`  — the spatial + content persistence (DesktopLayout and friends).
// The remaining surfaces (windows, menus, document editing, properties, actuation,
// rendering) live here as `impl DeosDesktop` blocks over the shared chrome/layout.
pub mod android_window;
pub mod chrome;
pub mod layout;
pub mod workflow;

pub use workflow::{IntentKind, WorkflowState, WorkflowStep};

use std::cell::RefCell;
use std::collections::HashMap;
use std::path::PathBuf;
use std::rc::Rc;

use gpui::prelude::FluentBuilder;
use gpui::{
    AnyElement, AppContext, ClickEvent, Context, Div, Entity, FontWeight, InteractiveElement,
    IntoElement, MouseButton, MouseDownEvent, MouseMoveEvent, MouseUpEvent, ParentElement, Pixels,
    Point, Render, Stateful, StatefulInteractiveElement, Styled, Subscription, Window, div, px,
};

use gpui_component::input::{Input, InputEvent, InputState};

use dregg_cell::lifecycle::CellLifecycle;
use dregg_types::CellId;

use dregg_doc::{Author, Doc, Granularity};

use crate::world::{World, grant_capability, transfer};

// The chrome kit + persistence types are re-exported so existing call sites
// (`deos_desktop::id_hex`, `deos_desktop::DesktopLayout`, …) keep working.
pub use android_window::{ANDROID_WINDOW_TITLE, AndroidInputCmd, AndroidWindow};
pub use chrome::{
    DOC_CHUNK_BYTES, DOC_MAX_CHUNKS, DOC_REV_SLOT, DOC_TEXT_BASE, GLYPH_CLOSE, GLYPH_GRIP,
    GLYPH_MAX, GLYPH_MIN, GLYPH_RESTORE, ICON_H, ICON_W, MENUBAR_H, NT_DESKTOP_BG, NT_DIM, NT_FACE,
    NT_FACE_DARK, NT_HILIGHT, NT_ICON_LABEL, NT_MENU_HILIGHT, NT_SELECT, NT_SHADOW, NT_TEXT,
    NT_TITLE_ACTIVE, NT_TITLE_TEXT, WIN_MIN_H, WIN_MIN_W, bevel_raised, face_gauge, face_row,
    face_row_color, face_section, fmt_balance, id_hex, id_short, pxf,
};
pub use layout::{DesktopLayout, DesktopPrefs, DocText, IconPos, WinGeom, WinKindTag};

/// Parse a document line back to the `CellId` it transcludes, if any. The compose
/// gesture writes `{transclude dregg://<64-hex> · <kind> · balance <b> · <life>}`
/// (see [`DeosDesktop::transclude_into`]); this reverses the `dregg://<hex>` head so
/// a transclusion becomes a STRUCTURED link the Links window can resolve to live
/// faces + invert into a backlink. Returns `None` for any non-transclusion line.
fn parse_transclusion_ref(line: &str) -> Option<CellId> {
    let after = line.split("dregg://").nth(1)?;
    // The hex id runs up to the first delimiter (space, middot, or closing brace).
    let hex: String = after
        .chars()
        .take_while(|c| c.is_ascii_hexdigit())
        .collect();
    if hex.len() != 64 {
        return None;
    }
    let mut bytes = [0u8; 32];
    for (i, b) in bytes.iter_mut().enumerate() {
        *b = u8::from_str_radix(&hex[i * 2..i * 2 + 2], 16).ok()?;
    }
    Some(CellId::from_bytes(bytes))
}

// ── A live, open inspector window over one cell ───────────────────────────────────

/// The faces an inspector window shows of a cell (read fresh off the live ledger
/// each render — a fired affordance updates them in place).
struct WindowState {
    /// The cell this window inspects (also the `HashMap` key; kept inline so a
    /// `WindowState` is self-describing when iterated).
    #[allow(dead_code)]
    cell: CellId,
    title: String,
    x: f32,
    y: f32,
    w: f32,
    h: f32,
    minimized: bool,
    z: u32,
    /// The TYPE of this window — inspector, document editor, links/backlinks, or
    /// the transcript/receipt-log. The same cell can be open in several kinds.
    kind: WinKind,
}

/// **The window-type vocabulary** — the NT/Pharo density beyond a lone inspector.
/// Each is a distinct surface over the same live cell.
#[derive(Clone)]
enum WinKind {
    /// The reflective inspector (identity + live state + affordances + properties).
    Inspector,
    /// **A real document editor.** Holds a live `dregg_doc::Doc` — typing diffs
    /// into a receipted patch (the chronicle advances) AND lands a verified turn on
    /// the cell. The document IS the cell (its prose lives in the cell's heap).
    DocEditor {
        doc: Doc,
        /// The text currently in the edit buffer (committed-on-edit / on the bake).
        buffer: String,
    },
    /// A links / backlinks view — which cells this one reaches (its caps) and which
    /// reach it, plus the transclusions composed into it.
    Links,
    /// The transcript / receipt-log — the World's receipt chain, the chronicle the
    /// user's "do it"s have written.
    Transcript,
    /// **The workflow-composer surface** — intents/workflows/refinement as first-class
    /// objects. The window's editing state (steps + baseline) lives in the desktop's
    /// `workflows` map keyed by the subject cell, so this variant is a marker.
    WorkflowComposer,
}

impl WinKind {
    fn label(&self) -> &'static str {
        match self {
            WinKind::Inspector => "Inspector",
            WinKind::DocEditor { .. } => "Document",
            WinKind::Links => "Links",
            WinKind::Transcript => "Transcript",
            WinKind::WorkflowComposer => "Workflow",
        }
    }
}

// ── The actuation surface: every action available on a cell ───────────────────────

/// One entry of a cell's right-click context menu — an action the user can "do it"
/// on. `held` reflects whether the user holds the cap for it (lit vs. dim).
struct MenuAction {
    label: String,
    held: bool,
    kind: ActionKind,
    /// A non-actionable divider row (groups the deep menu visually). Rendered as a
    /// thin rule; clicking does nothing.
    separator: bool,
}

impl MenuAction {
    /// An actionable menu row.
    fn new(label: impl Into<String>, held: bool, kind: ActionKind) -> MenuAction {
        MenuAction {
            label: label.into(),
            held,
            kind,
            separator: false,
        }
    }

    /// A divider row in a deep context menu.
    fn sep() -> MenuAction {
        MenuAction {
            label: String::new(),
            held: false,
            kind: ActionKind::Inspect,
            separator: true,
        }
    }
}

#[derive(Clone)]
enum ActionKind {
    /// Open the inspector window on the cell.
    Inspect,
    /// Open the cell as a DOCUMENT EDITOR (the document-as-cell surface).
    OpenDoc,
    /// Open the links / backlinks view over the cell.
    OpenLinks,
    /// Open the transcript / receipt-log window (the World chronicle).
    OpenTranscript,
    /// Open the WORKFLOW-COMPOSER window over the cell — compose intents into a
    /// workflow and check flow-refinement (the real `dregg_deploy::refine` game).
    OpenWorkflow,
    /// Open the PROPERTY inspector/editor for the cell (the NT property-dialog +
    /// Pharo inspect-everything surface — view and edit the cell's properties).
    Properties,
    /// Open the WINDOW property sheet (the window's persisted layout properties) for
    /// the given window kind on the acted-on cell.
    WindowProperties { tag: WinKindTag },
    /// Fire a real verified turn: transfer `amount` from this cell to the
    /// desktop's "user" anchor (a self-contained demo of actuation).
    Transfer { amount: u64 },
    /// Grant a capability reaching `target` to this cell at the next free slot
    /// (the ocap "grant" verb) — a real `GrantCapability` turn.
    Grant { target: CellId },
    /// Bump the cell's nonce via a real `IncrementNonce` turn (the simplest
    /// always-available affordance — proves the actuation path lands a receipt).
    BumpNonce,
    /// **Set a state field via a receipted `SetField` turn** — the property-editor's
    /// write verb (editing a cell property IS a verified turn). Writes `value` into
    /// slot `index` of the cell's state.
    SetField { index: usize, value: u64 },
    /// **COMPOSE: transclude this cell into the named target document** — embed a
    /// provenanced reference to this cell's content into `into`'s document (a
    /// receipted patch + a verified turn). The genuine cross-cell compose gesture.
    TranscludeInto { into: CellId },
    /// Seal / unseal the cell (a lifecycle turn) — a window-control-ish actuation
    /// surfaced in the deep menu.
    ToggleSeal,
    /// **Cascade every open window** — re-stagger all open windows from the top-left
    /// (the NT "Cascade Windows" command). A pure layout/view actuation: it moves
    /// windows and re-persists their geometry, firing NO verified turn.
    CascadeWindows,
    /// **Tile every open window** in a grid filling the desktop (the NT "Tile" command).
    /// Pure layout actuation.
    TileWindows,
    /// **Close every open window** (the NT "Close All"). Pure layout actuation.
    CloseAllWindows,
}

// ── A floating context menu (rendered as an NT popup overlay) ─────────────────────

struct OpenMenu {
    /// The object the menu acts on. `None` = the desktop-background menu (no cell).
    cell: Option<CellId>,
    /// The menu's heading (the named object: a cell kind + id, a window title, or
    /// "Desktop").
    heading: String,
    at: Point<Pixels>,
    actions: Vec<MenuAction>,
}

/// **The property inspector/editor** — a modal NT property-dialog open over one
/// object (a cell or a window). It lists the object's properties and lets the user
/// EDIT them: a cell-property edit fires a receipted `SetField` turn; a window /
/// desktop property edit is a persisted layout change. The Pharo "inspect anything"
/// fused with the NT "Properties…" dialog.
struct PropertyDialog {
    subject: PropSubject,
    at: Point<Pixels>,
    w: f32,
    h: f32,
}

#[derive(Clone)]
enum PropSubject {
    /// A cell's properties (view + receipted edits via SetField turns).
    Cell(CellId),
    /// A window's layout properties (view + persisted layout edits) — keyed by the
    /// cell + window kind so it targets the right open window.
    Window(CellId, WinKindTag),
    /// The desktop's customization preferences.
    Desktop,
}

// ── A live drag in flight (an icon being moved, or a window being moved/resized) ───

enum Drag {
    Icon {
        cell: CellId,
        // The grab offset from the icon's top-left to the mouse.
        grab: Point<Pixels>,
    },
    WinMove {
        key: WinKey,
        grab: Point<Pixels>,
    },
    WinResize {
        key: WinKey,
        // The window's top-left at grab; we resize the bottom-right corner.
        origin: Point<Pixels>,
    },
}

/// A window-instance key — a cell plus the window TYPE, so one cell can be open as
/// an inspector AND a document editor AND a links view at once.
type WinKey = (CellId, WinKindTag);

/// **THE deos DESKTOP** — the root `Render` view. Owns the live `World`, the icon
/// layout, the open inspector windows, the in-flight drag, the open context menu,
/// and the persisted [`DesktopLayout`]. Every spatial gesture mutates the layout and
/// re-saves it; every actuation commits a real verified turn on the World.
pub struct DeosDesktop {
    world: Rc<RefCell<World>>,
    /// The cells to show as icons (the live ledger's cells, ordered stably by id).
    cells: Vec<CellId>,
    /// The "user" anchor — the default transfer/grant counterparty for the demo
    /// actuation verbs (so a context-menu action is fully self-contained).
    user: CellId,
    layout: DesktopLayout,
    layout_path: PathBuf,
    windows: HashMap<WinKey, WindowState>,
    open_menu: Option<OpenMenu>,
    /// The open property dialog, if any (the NT Properties… surface).
    open_prop: Option<PropertyDialog>,
    drag: Option<Drag>,
    next_z: u32,
    /// The author identity stamped on document patches (the operator). A document
    /// edit's `dregg_doc::Patch` carries this; blame/provenance flow from it.
    author: Author,
    /// A short log of the last actuations (receipt height / outcome) shown in the
    /// status bar — the user sees their "do it" landed a real verified turn.
    status: String,
    /// **The per-cell workflow-composer state** — the intents/workflow being composed
    /// over each subject cell, plus the pinned refinement baseline. Read by the
    /// workflow window body; the REAL `dregg_deploy::refine` flow + decision run over
    /// it. Keyed by the subject cell so each cell has its own workflow.
    workflows: HashMap<CellId, workflow::WorkflowState>,
    /// **The real free-typing document editors** — one live `gpui-component`
    /// `InputState` (a rope-backed, multi-line text widget) per open document cell.
    /// Keystrokes flow through its `Change` event into [`Self::edit_doc`], which
    /// commits the prose into the cell's COMMITTED heap (`commit_doc_text_to_heap` →
    /// `SetField`) as a receipted patch. Created lazily on first render of the doc
    /// body (where `window`/`cx` are in hand). The `Change` subscription's lifetime
    /// is kept in `doc_subs`.
    doc_inputs: HashMap<CellId, Entity<InputState>>,
    /// The per-document `Change`-event subscription handles (kept alive so the
    /// keystroke→heap commit fires for the editor's whole lifetime).
    doc_subs: HashMap<CellId, Subscription>,
    /// Cells whose document text was changed OUTSIDE the editor widget (a transclude
    /// drop / a bake edit) and so the live `InputState` must be re-seeded from the
    /// cached buffer on the next render (those paths lack `&mut Window`, which
    /// `InputState::set_value` needs). Drained in `render_doc_body`.
    doc_resync: std::collections::HashSet<CellId>,
}

impl DeosDesktop {
    /// Open the desktop over a live `World`, restoring the persisted layout. `user`
    /// is the default counterparty for the demo transfer/grant verbs.
    pub fn new(
        world: Rc<RefCell<World>>,
        user: CellId,
        layout_path: PathBuf,
        _window: &mut Window,
        _cx: &mut Context<Self>,
    ) -> Self {
        let cells: Vec<CellId> = {
            let w = world.borrow();
            let mut v: Vec<CellId> = w.ledger().iter().map(|(id, _)| *id).collect();
            v.sort();
            v
        };
        let layout = DesktopLayout::load(&layout_path);

        let mut desk = DeosDesktop {
            world,
            cells,
            user,
            layout,
            layout_path,
            windows: HashMap::new(),
            open_menu: None,
            open_prop: None,
            drag: None,
            next_z: 1,
            // A stable operator author derived from the user anchor — every document
            // patch is blamed on it.
            author: Author(u64::from_le_bytes(
                user.as_bytes()[..8].try_into().unwrap_or([0u8; 8]),
            )),
            status: "deos desktop — right-click ANYTHING for its menu · double-click to inspect · \
                     drag to arrange (persisted) · Open as Document to author"
                .to_string(),
            workflows: HashMap::new(),
            doc_inputs: HashMap::new(),
            doc_subs: HashMap::new(),
            doc_resync: std::collections::HashSet::new(),
        };
        // Re-open any windows the persisted layout remembers (spatial persistence
        // for windows, not just icons — and now for window TYPE too).
        let geoms: Vec<WinGeom> = desk.layout.windows.clone();
        for g in geoms {
            if let Some(cell) = desk.cells.iter().find(|c| id_hex(&c) == g.cell).copied() {
                desk.open_window_at(cell, g.kind, g.x, g.y, g.w, g.h, g.minimized);
            }
        }
        desk
    }

    /// The auto-arranged default grid position for a cell with no persisted slot —
    /// a left-edge column of icons (so a fresh desktop is legible before any drag).
    fn default_icon_pos(&self, idx: usize) -> Point<Pixels> {
        let rows = self.layout.prefs.grid_rows.max(1) as usize;
        let col = (idx / rows) as f32;
        let row = (idx % rows) as f32;
        Point::new(
            px(24.0 + col * (ICON_W + 16.0)),
            px(MENUBAR_H + 18.0 + row * (ICON_H + 14.0)),
        )
    }

    fn icon_pos(&self, idx: usize, cell: &CellId) -> Point<Pixels> {
        self.layout
            .icon_pos(&id_hex(&cell))
            .unwrap_or_else(|| self.default_icon_pos(idx))
    }

    /// Build a fresh window-kind body for `cell` and `tag` — for the document editor
    /// this loads the cell's persisted/heap-stored prose into a live `dregg_doc::Doc`.
    fn make_kind(&self, cell: CellId, tag: WinKindTag) -> WinKind {
        match tag {
            WinKindTag::Inspector => WinKind::Inspector,
            WinKindTag::Links => WinKind::Links,
            WinKindTag::Transcript => WinKind::Transcript,
            WinKindTag::Workflow => WinKind::WorkflowComposer,
            WinKindTag::DocEditor => {
                let text = self.load_doc_text(&cell);
                let g = if self.layout.prefs.word_granularity {
                    Granularity::Word
                } else {
                    Granularity::Line
                };
                let mut doc = Doc::new(g);
                if !text.is_empty() {
                    doc.edit(self.author, &text);
                }
                WinKind::DocEditor { doc, buffer: text }
            }
            // Other window TYPEs owned by concurrent surfaces fall back to an
            // inspector body until their own arm lands (swarm self-heal).
            _ => WinKind::Inspector,
        }
    }

    fn open_window_at(
        &mut self,
        cell: CellId,
        tag: WinKindTag,
        x: f32,
        y: f32,
        w: f32,
        h: f32,
        minimized: bool,
    ) {
        let z = self.next_z;
        self.next_z += 1;
        let kind = self.make_kind(cell, tag);
        let title = format!(
            "{} {} — {}",
            self.cell_kind(&cell),
            id_short(&cell),
            kind.label()
        );
        self.windows.insert(
            (cell, tag),
            WindowState {
                cell,
                title,
                x,
                y,
                w: w.max(WIN_MIN_W),
                h: h.max(WIN_MIN_H),
                minimized,
                z,
                kind,
            },
        );
    }

    /// Open (or focus) the inspector window on `cell` (the legacy double-click).
    fn open_window(&mut self, cell: CellId) {
        self.open_kind(cell, WinKindTag::Inspector);
    }

    /// Open (or focus) the WORKFLOW-COMPOSER window on `cell` — the surface that
    /// composes intents into a workflow and decides flow-refinement.
    pub(super) fn open_workflow_window(&mut self, cell: CellId) {
        self.open_kind(cell, WinKindTag::Workflow);
        self.status = format!(
            "Workflow composer on {} — compose intents, check refinement A ≤ᶠ B.",
            id_short(&cell)
        );
    }

    /// The user anchor — the default counterparty for the workflow's intent steps
    /// (transfer/grant target). Exposed to the `workflow` submodule.
    pub(super) fn workflow_user(&self) -> CellId {
        self.user
    }

    /// Open (or focus) a window of `tag` on `cell`, restoring its persisted geometry
    /// if any, else a cascade default. The same cell can hold several window kinds.
    fn open_kind(&mut self, cell: CellId, tag: WinKindTag) {
        if let Some(ws) = self.windows.get_mut(&(cell, tag)) {
            ws.minimized = false;
            ws.z = self.next_z;
            self.next_z += 1;
            return;
        }
        // Document/links/transcript windows open a touch wider than the inspector.
        let (dw, dh) = match tag {
            WinKindTag::DocEditor => (440.0, 340.0),
            WinKindTag::Transcript => (440.0, 300.0),
            WinKindTag::Links => (380.0, 300.0),
            WinKindTag::Inspector => (360.0, 300.0),
            WinKindTag::Workflow => (420.0, 460.0),
            _ => (380.0, 320.0),
        };
        if let Some(g) = self.layout.win_geom(&id_hex(&cell), tag) {
            self.open_window_at(cell, tag, g.x, g.y, g.w, g.h, false);
        } else {
            let n = self.windows.len() as f32;
            self.open_window_at(cell, tag, 300.0 + n * 26.0, 80.0 + n * 26.0, dw, dh, false);
        }
        self.persist_window((cell, tag));
    }

    fn close_window(&mut self, key: WinKey) {
        self.windows.remove(&key);
        // Drop the live editor entity + its Change subscription when a document window
        // closes, so a reopen re-seeds the widget from the committed cell heap.
        if key.1 == WinKindTag::DocEditor {
            self.doc_inputs.remove(&key.0);
            self.doc_subs.remove(&key.0);
            self.doc_resync.remove(&key.0);
        }
        self.layout.drop_win(&id_hex(&key.0), key.1);
        self.layout.save(&self.layout_path);
    }

    fn persist_window(&mut self, key: WinKey) {
        if let Some(ws) = self.windows.get(&key) {
            self.layout.set_win_geom(WinGeom {
                cell: id_hex(&key.0),
                x: ws.x,
                y: ws.y,
                w: ws.w,
                h: ws.h,
                minimized: ws.minimized,
                kind: key.1,
            });
            self.layout.save(&self.layout_path);
        }
    }

    /// Whether the user holds the authority to act on a cell. The embedded World is
    /// single-custody (the operator is the authority), so every action is HELD here;
    /// a federated/cap-bounded desktop would dim the ones the held cap can't reach.
    /// We mark the issuer well (negative balance) as "system" (dim) to show the
    /// lit/dim distinction the metaphor needs.
    fn holds(&self, cell: &CellId) -> bool {
        self.cell_balance(cell) >= 0
    }

    fn cell_balance(&self, cell: &CellId) -> i64 {
        self.world
            .borrow()
            .ledger()
            .get(cell)
            .map(|c| c.state.balance())
            .unwrap_or(0)
    }

    fn cell_nonce(&self, cell: &CellId) -> u64 {
        self.world
            .borrow()
            .ledger()
            .get(cell)
            .map(|c| c.state.nonce())
            .unwrap_or(0)
    }

    fn cell_lifecycle(&self, cell: &CellId) -> String {
        match self
            .world
            .borrow()
            .ledger()
            .get(cell)
            .map(|c| c.lifecycle.clone())
        {
            Some(CellLifecycle::Live) => "Live".into(),
            Some(CellLifecycle::Sealed { .. }) => "Sealed".into(),
            Some(CellLifecycle::Migrated { .. }) => "Migrated".into(),
            Some(CellLifecycle::Destroyed { .. }) => "Destroyed".into(),
            Some(CellLifecycle::Archived { .. }) => "Archived".into(),
            None => "—".into(),
        }
    }

    fn cell_cap_count(&self, cell: &CellId) -> usize {
        self.world
            .borrow()
            .ledger()
            .get(cell)
            .map(|c| c.capabilities.iter().count())
            .unwrap_or(0)
    }

    /// Read state slot `index` of a cell as a u64 (the low 8 bytes of the field) —
    /// the property editor's read-back.
    fn cell_field_u64(&self, cell: &CellId, index: usize) -> u64 {
        self.world
            .borrow()
            .ledger()
            .get(cell)
            .and_then(|c| c.state.fields.get(index).copied())
            .map(|f| u64::from_le_bytes(f[..8].try_into().unwrap_or([0u8; 8])))
            .unwrap_or(0)
    }

    /// Whether the cell is currently sealed (drives the seal/unseal menu label).
    fn cell_sealed(&self, cell: &CellId) -> bool {
        matches!(
            self.world.borrow().ledger().get(cell).map(|c| &c.lifecycle),
            Some(CellLifecycle::Sealed { .. })
        )
    }

    // ── Document text: the document-as-cell payload ──────────────────────────────
    // A document is a CELL: editing diffs into a `dregg_doc::Patch` (the chronicle
    // advances) AND lands real `SetField` turns that write the prose itself into the
    // cell's COMMITTED heap (`fields_map`, ext keys >= STATE_SLOTS, committed via
    // `fields_root`) plus a revision bump into slot 14. The committed truth is the
    // cell heap: a doc edit is a verified, receipted turn whose value reads back from
    // the committed state and survives reopen FROM THE LEDGER. The layout sidecar is
    // kept only as a fast cache / pre-heap-migration fallback.

    /// Load a document cell's prose from the COMMITTED cell heap (`fields_map`),
    /// falling back to the layout sidecar only for cells whose prose predates the
    /// heap-write path (migration) — empty for a fresh doc. The committed heap is the
    /// source of truth: reopen restores from the ledger, not the sidecar.
    fn load_doc_text(&self, cell: &CellId) -> String {
        if let Some(text) = self.read_doc_from_heap(cell) {
            return text;
        }
        // Migration / cache fallback: a doc authored before the heap-write path.
        self.layout.doc_text(&id_hex(cell)).unwrap_or_default()
    }

    /// Read a document's prose back from the cell's committed heap (`fields_map`):
    /// `DOC_TEXT_BASE` holds the byte length, `DOC_TEXT_BASE + 1 + i` the chunks.
    /// Returns `None` when the cell carries no committed document (length key absent)
    /// so the caller can fall back to the sidecar. The bytes are the verbatim values
    /// committed by `fields_root` — a read off the live ledger.
    fn read_doc_from_heap(&self, cell: &CellId) -> Option<String> {
        let w = self.world.borrow();
        let state = &w.ledger().get(cell)?.state;
        let len_fe = state.get_field_ext(DOC_TEXT_BASE)?;
        let byte_len = u64::from_le_bytes(len_fe[..8].try_into().ok()?) as usize;
        let mut bytes = Vec::with_capacity(byte_len);
        let mut chunk = 0u64;
        while bytes.len() < byte_len && chunk < DOC_MAX_CHUNKS {
            let fe = state
                .get_field_ext(DOC_TEXT_BASE + 1 + chunk)
                .unwrap_or([0u8; 32]);
            let take = (byte_len - bytes.len()).min(DOC_CHUNK_BYTES);
            bytes.extend_from_slice(&fe[..take]);
            chunk += 1;
        }
        Some(String::from_utf8_lossy(&bytes).into_owned())
    }

    /// The sum of all live cell balances — the conservation invariant the World keeps
    /// at zero (issuer wells are negative, accounts positive; Σδ = 0). A read-only
    /// projection over the live ledger, shown in the World-summary widget.
    fn world_balance_sum(&self) -> i64 {
        self.world
            .borrow()
            .ledger()
            .iter()
            .map(|(_, c)| c.state.balance())
            .sum()
    }

    /// The count of receipts in the World chronicle whose agent is `cell` — the
    /// cell's own turn history length, surfaced in the inspector. A read-only filter
    /// over the existing receipt log.
    fn cell_receipt_count(&self, cell: &CellId) -> usize {
        self.world
            .borrow()
            .receipts()
            .iter()
            .filter(|r| &r.agent == cell)
            .count()
    }

    /// The largest live cell balance (a denominator for the inspector's balance
    /// gauge, so a cell's value reads relative to the World's biggest holder).
    fn world_max_balance(&self) -> i64 {
        self.world
            .borrow()
            .ledger()
            .iter()
            .map(|(_, c)| c.state.balance())
            .max()
            .unwrap_or(1)
            .max(1)
    }

    /// A short kind label for a cell, derived from its balance — the icon's caption.
    fn cell_kind(&self, cell: &CellId) -> &'static str {
        let b = self.cell_balance(cell);
        if b < 0 {
            "issuer well"
        } else if b > 500_000 {
            "treasury"
        } else if b == 0 {
            "service"
        } else {
            "account"
        }
    }

    /// **The actuation surface for `cell`** — a DEEP, contextual list of everything
    /// you can do to a cell-icon (the Pharo "right-click anything and there's a menu
    /// of everything"). Open-as surfaces, verified-turn affordances, the compose
    /// gesture, lifecycle, and Properties. Lit if the cap is held, dim if not.
    fn actions_for(&self, cell: CellId) -> Vec<MenuAction> {
        use ActionKind as A;
        let held = self.holds(&cell);
        let mut v = vec![
            // ── Open-as surfaces (the window-type vocabulary) ──
            MenuAction::new("Inspect…", true, A::Inspect),
            MenuAction::new("Open as Document…", true, A::OpenDoc),
            MenuAction::new("Links & Backlinks…", true, A::OpenLinks),
            MenuAction::new("Transcript (receipt log)…", true, A::OpenTranscript),
            MenuAction::new(
                "Compose Workflow… (intents + refinement)",
                true,
                A::OpenWorkflow,
            ),
            MenuAction::sep(),
            // ── Verified-turn affordances (do it) ──
            MenuAction::new("Bump nonce  (verified turn)", held, A::BumpNonce),
        ];
        if cell != self.user {
            v.push(MenuAction::new(
                format!("Transfer 1,000 → {}", id_short(&self.user)),
                held && self.cell_balance(&cell) >= 1_000,
                A::Transfer { amount: 1_000 },
            ));
        }
        v.push(MenuAction::new(
            format!("Grant cap → {}", id_short(&self.user)),
            held,
            A::Grant { target: self.user },
        ));
        v.push(MenuAction::new(
            format!("Set field[{DOC_REV_SLOT}] += 1  (SetField turn)"),
            held,
            A::SetField {
                index: DOC_REV_SLOT,
                value: self.cell_field_u64(&cell, DOC_REV_SLOT) + 1,
            },
        ));
        v.push(MenuAction::sep());
        // ── Compose: transclude this cell into every OPEN document ──
        let mut doc_targets: Vec<CellId> = self
            .windows
            .keys()
            .filter(|(_, t)| *t == WinKindTag::DocEditor)
            .map(|(c, _)| *c)
            .collect();
        doc_targets.sort();
        doc_targets.dedup();
        if doc_targets.is_empty() {
            v.push(MenuAction::new(
                "Transclude into… (open a Document first)",
                false,
                A::OpenDoc,
            ));
        } else {
            for into in doc_targets {
                v.push(MenuAction::new(
                    format!("Transclude into doc {}", id_short(&into)),
                    true,
                    A::TranscludeInto { into },
                ));
            }
        }
        v.push(MenuAction::sep());
        // ── Lifecycle ──
        v.push(MenuAction::new(
            if self.cell_sealed(&cell) {
                "Unseal cell  (lifecycle turn)"
            } else {
                "Seal cell  (lifecycle turn)"
            },
            held,
            A::ToggleSeal,
        ));
        v.push(MenuAction::sep());
        // ── Properties (the property inspector/editor) ──
        v.push(MenuAction::new("Properties…", true, A::Properties));
        v
    }

    /// The deep right-click menu for an OPEN WINDOW (its title bar / chrome) — open
    /// the same cell in other surfaces, and the window's / cell's Properties.
    fn window_actions(&self, _cell: CellId, tag: WinKindTag) -> Vec<MenuAction> {
        use ActionKind as A;
        vec![
            MenuAction::new("Inspect this cell…", true, A::Inspect),
            MenuAction::new("Open as Document…", true, A::OpenDoc),
            MenuAction::new("Links & Backlinks…", true, A::OpenLinks),
            MenuAction::new("Transcript…", true, A::OpenTranscript),
            MenuAction::sep(),
            MenuAction::new("Window Properties…", true, A::WindowProperties { tag }),
            MenuAction::new("Cell Properties…", true, A::Properties),
        ]
    }

    /// The right-click menu for the bare desktop background — the World transcript and
    /// desktop Preferences/customization. The Transcript/Preferences open without a
    /// cell context (handled in `actuate_desktop`).
    fn desktop_actions(&self) -> Vec<MenuAction> {
        use ActionKind as A;
        let any_win = !self.windows.is_empty();
        vec![
            MenuAction::new("World Transcript (receipt log)…", true, A::OpenTranscript),
            MenuAction::sep(),
            MenuAction::new("Cascade windows", any_win, A::CascadeWindows),
            MenuAction::new("Tile windows", any_win, A::TileWindows),
            MenuAction::new("Close all windows", any_win, A::CloseAllWindows),
            MenuAction::sep(),
            MenuAction::new("Preferences & Customize…", true, A::Properties),
        ]
    }

    /// The pull-down for one menu-bar item (acts on the `user` anchor cell). Dense,
    /// per-menu vocabulary — the NT menu bar fleshed out.
    fn menubar_actions(&self, name: &str) -> Vec<MenuAction> {
        use ActionKind as A;
        let u = self.user;
        match name {
            "World" => vec![
                MenuAction::new("Transcript (receipt log)…", true, A::OpenTranscript),
                MenuAction::sep(),
                MenuAction::new("Preferences & Customize…", true, A::Properties),
            ],
            "Cell" => vec![
                MenuAction::new("Inspect user cell…", true, A::Inspect),
                MenuAction::new("Open as Document…", true, A::OpenDoc),
                MenuAction::new("Bump nonce  (verified turn)", self.holds(&u), A::BumpNonce),
                MenuAction::new("Properties…", true, A::Properties),
            ],
            "View" => vec![
                MenuAction::new("Links & Backlinks…", true, A::OpenLinks),
                MenuAction::new("Transcript…", true, A::OpenTranscript),
                MenuAction::new("Workflow Composer…", true, A::OpenWorkflow),
            ],
            "Window" => {
                let any_win = !self.windows.is_empty();
                vec![
                    MenuAction::new("New Inspector…", true, A::Inspect),
                    MenuAction::new("New Document…", true, A::OpenDoc),
                    MenuAction::new("New Transcript…", true, A::OpenTranscript),
                    MenuAction::new("New Workflow Composer…", true, A::OpenWorkflow),
                    MenuAction::sep(),
                    MenuAction::new("Cascade windows", any_win, A::CascadeWindows),
                    MenuAction::new("Tile windows", any_win, A::TileWindows),
                    MenuAction::new("Close all windows", any_win, A::CloseAllWindows),
                ]
            }
            _ => vec![MenuAction::new(
                "deos desktop — right-click anything",
                false,
                A::Inspect,
            )],
        }
    }

    /// **DO IT** — fire a real verified turn for a context-menu action, commit it on
    /// the live World, and record the outcome in the status bar. This is the ACTUATION:
    /// the user's right-click "do it" lands a real `TurnReceipt` on the cell's chain.
    fn actuate(&mut self, cell: CellId, kind: &ActionKind) {
        match kind {
            ActionKind::Inspect => {
                self.open_window(cell);
                self.status = format!(
                    "Inspecting {} ({}).",
                    id_short(&cell),
                    self.cell_kind(&cell)
                );
            }
            ActionKind::BumpNonce => {
                let turn = {
                    let w = self.world.borrow();
                    w.turn(
                        cell,
                        vec![dregg_turn::action::Effect::IncrementNonce { cell }],
                    )
                };
                let outcome = self.world.borrow_mut().commit_turn(turn);
                self.status = format!(
                    "Bump nonce on {} → {} (height {}).",
                    id_short(&cell),
                    if outcome.is_committed() {
                        "committed"
                    } else {
                        "rejected"
                    },
                    self.world.borrow().height()
                );
            }
            ActionKind::Transfer { amount } => {
                let turn = {
                    let w = self.world.borrow();
                    w.turn(cell, vec![transfer(cell, self.user, *amount)])
                };
                let outcome = self.world.borrow_mut().commit_turn(turn);
                self.status = format!(
                    "Transfer {} {} → {} → {} (height {}).",
                    amount,
                    id_short(&cell),
                    id_short(&self.user),
                    if outcome.is_committed() {
                        "committed"
                    } else {
                        "rejected"
                    },
                    self.world.borrow().height()
                );
            }
            ActionKind::Grant { target } => {
                let slot = self.cell_cap_count(&cell) as u32 + 1;
                let turn = {
                    let w = self.world.borrow();
                    w.turn(cell, vec![grant_capability(cell, cell, *target, slot)])
                };
                let outcome = self.world.borrow_mut().commit_turn(turn);
                self.status = format!(
                    "Grant cap {} → {} @{} → {} (height {}).",
                    id_short(&cell),
                    id_short(&target),
                    slot,
                    if outcome.is_committed() {
                        "committed"
                    } else {
                        "rejected"
                    },
                    self.world.borrow().height()
                );
            }
            ActionKind::OpenDoc => {
                self.open_kind(cell, WinKindTag::DocEditor);
                self.status = format!("Document editor open on {}.", id_short(&cell));
            }
            ActionKind::OpenLinks => {
                self.open_kind(cell, WinKindTag::Links);
                self.status = format!("Links & backlinks of {}.", id_short(&cell));
            }
            ActionKind::OpenTranscript => {
                self.open_kind(cell, WinKindTag::Transcript);
                self.status = "Transcript — the World receipt log.".into();
            }
            ActionKind::OpenWorkflow => {
                self.open_workflow_window(cell);
            }
            ActionKind::Properties => {
                self.open_properties(PropSubject::Cell(cell));
                self.status = format!("Properties of {}.", id_short(&cell));
            }
            ActionKind::WindowProperties { tag } => {
                self.open_properties(PropSubject::Window(cell, *tag));
                self.status = format!("Window properties of {} {:?}.", id_short(&cell), tag);
            }
            ActionKind::SetField { index, value } => {
                let ok = self.commit_set_field(cell, *index, *value);
                self.status = format!(
                    "SetField {} field[{index}] = {value} → {} (height {}).",
                    id_short(&cell),
                    if ok { "committed" } else { "rejected" },
                    self.world.borrow().height()
                );
            }
            ActionKind::ToggleSeal => {
                let sealed = self.cell_sealed(&cell);
                let eff = if sealed {
                    dregg_turn::action::Effect::CellUnseal { target: cell }
                } else {
                    dregg_turn::action::Effect::CellSeal {
                        target: cell,
                        reason: [0u8; 32],
                    }
                };
                let turn = {
                    let w = self.world.borrow();
                    w.turn(cell, vec![eff])
                };
                let outcome = self.world.borrow_mut().commit_turn(turn);
                self.status = format!(
                    "{} {} → {} (height {}).",
                    if sealed { "Unseal" } else { "Seal" },
                    id_short(&cell),
                    if outcome.is_committed() {
                        "committed"
                    } else {
                        "rejected"
                    },
                    self.world.borrow().height()
                );
            }
            ActionKind::TranscludeInto { into } => {
                self.transclude_into(cell, *into);
            }
            ActionKind::CascadeWindows => self.cascade_windows(),
            ActionKind::TileWindows => self.tile_windows(),
            ActionKind::CloseAllWindows => self.close_all_windows(),
        }
    }

    /// Commit a `SetField` turn writing `value` (LE u64) into `index` — the property
    /// editor's write verb. Returns whether the verified turn committed.
    fn commit_set_field(&mut self, cell: CellId, index: usize, value: u64) -> bool {
        let mut fe = [0u8; 32];
        fe[..8].copy_from_slice(&value.to_le_bytes());
        let turn = {
            let w = self.world.borrow();
            w.turn(
                cell,
                vec![dregg_turn::action::Effect::SetField {
                    cell,
                    index,
                    value: fe,
                }],
            )
        };
        self.world.borrow_mut().commit_turn(turn).is_committed()
    }

    /// **Commit a document's prose into the cell's COMMITTED heap** as ONE verified
    /// turn: a `SetField` into `DOC_TEXT_BASE` (the byte length) plus one per 32-byte
    /// chunk into `DOC_TEXT_BASE + 1 + i`. Stale trailing chunks from a previously
    /// longer revision are zeroed in the same turn so a shrunk document leaves no
    /// committed garbage. These write `fields_map` (ext keys >= STATE_SLOTS) via
    /// `set_field_ext`, recomputing `fields_root` — the prose is on-ledger, receipted,
    /// and replays from committed state. Returns whether the turn committed.
    fn commit_doc_text_to_heap(&mut self, cell: CellId, text: &str) -> bool {
        use dregg_turn::action::Effect;
        let bytes = text.as_bytes();
        let byte_len = bytes.len();
        let new_chunks = byte_len.div_ceil(DOC_CHUNK_BYTES) as u64;

        // The previously-committed length, to know how many trailing chunks to clear.
        let prev_len = {
            let w = self.world.borrow();
            w.ledger()
                .get(&cell)
                .and_then(|c| c.state.get_field_ext(DOC_TEXT_BASE))
                .map(|fe| u64::from_le_bytes(fe[..8].try_into().unwrap_or([0u8; 8])) as usize)
                .unwrap_or(0)
        };
        let prev_chunks = (prev_len.div_ceil(DOC_CHUNK_BYTES) as u64).min(DOC_MAX_CHUNKS);

        let mut effects: Vec<Effect> = Vec::new();
        // Length felt (LE u64 in the low 8 bytes).
        let mut len_fe = [0u8; 32];
        len_fe[..8].copy_from_slice(&(byte_len as u64).to_le_bytes());
        effects.push(Effect::SetField {
            cell,
            index: DOC_TEXT_BASE as usize,
            value: len_fe,
        });
        // The chunk felts: 32 verbatim UTF-8 bytes each.
        let n = new_chunks.min(DOC_MAX_CHUNKS);
        for i in 0..n {
            let start = (i as usize) * DOC_CHUNK_BYTES;
            let end = (start + DOC_CHUNK_BYTES).min(byte_len);
            let mut fe = [0u8; 32];
            fe[..end - start].copy_from_slice(&bytes[start..end]);
            effects.push(Effect::SetField {
                cell,
                index: (DOC_TEXT_BASE + 1 + i) as usize,
                value: fe,
            });
        }
        // Zero any trailing chunks left over from a longer prior revision.
        for i in n..prev_chunks {
            effects.push(Effect::SetField {
                cell,
                index: (DOC_TEXT_BASE + 1 + i) as usize,
                value: [0u8; 32],
            });
        }

        let turn = {
            let w = self.world.borrow();
            w.turn(cell, effects)
        };
        self.world.borrow_mut().commit_turn(turn).is_committed()
    }

    /// **COMPOSE — transclude a cell into a document.** Embed a provenanced reference
    /// to `src`'s content (its id, kind, balance, lifecycle) as a line into the open
    /// document on `into`. This is a genuine cross-cell compose: a receipted
    /// `dregg_doc::Patch` lands on the document AND a verified `SetField` turn bumps
    /// the document cell's revision (so the composed doc is real, receipted state).
    fn transclude_into(&mut self, src: CellId, into: CellId) {
        // The transclusion line — a live, provenanced quote of the source cell.
        let line = format!(
            "{{transclude dregg://{} · {} · balance {} · {}}}\n",
            id_hex(&src),
            self.cell_kind(&src),
            fmt_balance(self.cell_balance(&src)),
            self.cell_lifecycle(&src),
        );
        let author = self.author;
        let mut committed = false;
        if let Some(ws) = self.windows.get_mut(&(into, WinKindTag::DocEditor)) {
            if let WinKind::DocEditor { doc, buffer } = &mut ws.kind {
                buffer.push_str(&line);
                let new_text = buffer.clone();
                doc.edit(author, &new_text);
                committed = true;
            }
        }
        if committed {
            // Commit the composed prose into the cell's COMMITTED heap + bump the doc
            // cell's revision (real verified turns). The sidecar is kept as a cache.
            let text = self.load_doc_buffer(into);
            let prose_ok = self.commit_doc_text_to_heap(into, &text);
            self.layout.set_doc_text(&id_hex(&into), &text);
            self.layout.save(&self.layout_path);
            let rev = self.cell_field_u64(&into, DOC_REV_SLOT) + 1;
            let ok = prose_ok && self.commit_set_field(into, DOC_REV_SLOT, rev);
            // The live editor widget must pick up the transcluded line on next render
            // (this path has no `&mut Window` to push into `InputState` directly).
            self.doc_resync.insert(into);
            self.status = format!(
                "COMPOSE: transcluded {} into doc {} → patch + heap {} (height {}).",
                id_short(&src),
                id_short(&into),
                if ok { "committed" } else { "rejected" },
                self.world.borrow().height()
            );
        } else {
            self.status = format!(
                "COMPOSE: no open Document on {} — Open as Document first.",
                id_short(&into)
            );
        }
    }

    /// Read the current edit buffer of an open document window (the composed prose).
    fn load_doc_buffer(&self, cell: CellId) -> String {
        match self
            .windows
            .get(&(cell, WinKindTag::DocEditor))
            .map(|w| &w.kind)
        {
            Some(WinKind::DocEditor { buffer, .. }) => buffer.clone(),
            _ => self.load_doc_text(&cell),
        }
    }

    /// Open the property dialog over `subject`, cascading it onto the desktop.
    fn open_properties(&mut self, subject: PropSubject) {
        let n = self.windows.len() as f32;
        self.open_prop = Some(PropertyDialog {
            subject,
            at: Point::new(px(360.0 + n * 8.0), px(150.0 + n * 8.0)),
            w: 340.0,
            h: 300.0,
        });
        self.open_menu = None;
    }

    /// **Ensure the live free-typing editor exists for `cell`** — a real
    /// `gpui-component` `InputState` (rope-backed, multi-line) seeded with the cell's
    /// current committed prose, with a `Change` subscription that commits every
    /// keystroke through [`Self::edit_doc`] into the cell's heap (a receipted patch +
    /// verified revision turn). Idempotent: a second call is a no-op. Needs `window`
    /// + `cx` to build the entity, so it runs from `render_doc_body` (which threads
    /// them) rather than the `window`-less open paths.
    fn ensure_doc_input(&mut self, cell: CellId, window: &mut Window, cx: &mut Context<Self>) {
        if self.doc_inputs.contains_key(&cell) {
            return;
        }
        let seed = self.load_doc_buffer(cell);
        let input = cx.new(|cx| {
            InputState::new(window, cx)
                .multi_line(true)
                .soft_wrap(true)
                .placeholder(
                    "Type your document — every keystroke is a receipted patch on the cell heap…",
                )
                .default_value(seed)
        });
        // The keystroke → heap seam: on every Change, fold the editor's rope into the
        // cell's committed prose (the SAME `edit_doc` the canned buttons call). The
        // editor IS the buffer; the heap commit is its side effect.
        let sub = cx.subscribe_in(
            &input,
            window,
            move |this, input, event: &InputEvent, _window, cx| {
                if matches!(event, InputEvent::Change) {
                    let text = input.read(cx).value().to_string();
                    this.edit_doc(cell, text);
                    cx.notify();
                }
            },
        );
        // Focus the editor the moment it opens — "Open as Document" lands you with a
        // live caret, ready to type (a real editor, not a click-to-focus surface). The
        // desktop is hosted under a `gpui_component::Root` (the editor widget reaches it
        // for its overlay/focus plumbing), so this is always safe.
        input.update(cx, |st, cx| st.focus(window, cx));
        self.doc_inputs.insert(cell, input);
        self.doc_subs.insert(cell, sub);
    }

    /// **The document-editor edit gesture** — replace the buffer with `new_text`,
    /// diff it into a receipted `dregg_doc::Patch` (the chronicle advances), persist
    /// the prose, and bump the document cell's revision via a real `SetField` turn.
    fn edit_doc(&mut self, cell: CellId, new_text: String) {
        let author = self.author;
        let mut patches = 0usize;
        if let Some(ws) = self.windows.get_mut(&(cell, WinKindTag::DocEditor)) {
            if let WinKind::DocEditor { doc, buffer } = &mut ws.kind {
                *buffer = new_text.clone();
                doc.edit(author, &new_text);
                patches = doc.history().len();
            }
        }
        // Commit the prose itself into the cell's COMMITTED heap (a verified turn into
        // `fields_map`), then bump the revision. The sidecar is kept as a fast cache;
        // the committed truth is the cell heap, restored from the ledger on reopen.
        let prose_ok = self.commit_doc_text_to_heap(cell, &new_text);
        self.layout.set_doc_text(&id_hex(&cell), &new_text);
        self.layout.save(&self.layout_path);
        let rev = self.cell_field_u64(&cell, DOC_REV_SLOT) + 1;
        let ok = prose_ok && self.commit_set_field(cell, DOC_REV_SLOT, rev);
        self.status = format!(
            "EDIT doc {} → patch #{patches} + heap {} (rev {rev}, height {}).",
            id_short(&cell),
            if ok { "committed" } else { "rejected" },
            self.world.borrow().height()
        );
    }

    /// Actuate a desktop-background menu action (no cell context).
    fn actuate_desktop(&mut self, kind: &ActionKind) {
        match kind {
            ActionKind::OpenTranscript => {
                // The transcript over the World — anchor it on the user cell's window.
                self.open_kind(self.user, WinKindTag::Transcript);
                self.status = "World Transcript — the receipt log of every turn.".into();
            }
            ActionKind::Properties => {
                self.open_properties(PropSubject::Desktop);
                self.status = "Desktop Preferences & customization.".into();
            }
            ActionKind::CascadeWindows => self.cascade_windows(),
            ActionKind::TileWindows => self.tile_windows(),
            ActionKind::CloseAllWindows => self.close_all_windows(),
            _ => {}
        }
    }

    /// **COMPOSE** — drop cell `src` ONTO cell `dst`: act across them with the
    /// dropped affordance. A transfer when `src` has balance, else a cap grant. This
    /// is the spatial compose gesture (drag one icon onto another).
    fn compose_drop(&mut self, src: CellId, dst: CellId) {
        if src == dst {
            return;
        }
        let bal = self.cell_balance(&src);
        if bal >= 1_000 {
            let turn = {
                let w = self.world.borrow();
                w.turn(src, vec![transfer(src, dst, 1_000)])
            };
            let outcome = self.world.borrow_mut().commit_turn(turn);
            self.status = format!(
                "COMPOSE: dropped {} → {}: transfer 1,000 {} (height {}).",
                id_short(&src),
                id_short(&dst),
                if outcome.is_committed() {
                    "committed"
                } else {
                    "rejected"
                },
                self.world.borrow().height()
            );
        } else {
            let slot = self.cell_cap_count(&src) as u32 + 1;
            let turn = {
                let w = self.world.borrow();
                w.turn(src, vec![grant_capability(src, src, dst, slot)])
            };
            let outcome = self.world.borrow_mut().commit_turn(turn);
            self.status = format!(
                "COMPOSE: dropped {} → {}: grant cap @{} {} (height {}).",
                id_short(&src),
                id_short(&dst),
                slot,
                if outcome.is_committed() {
                    "committed"
                } else {
                    "rejected"
                },
                self.world.borrow().height()
            );
        }
    }

    // ── Window arrangement (pure layout actuation — NO verified turn) ────────────
    // The NT "Window" menu's Cascade / Tile / Close-All commands. Each only moves or
    // drops open windows and re-persists their geometry to the sidecar — view-state
    // only, the same persistence path a manual drag uses.

    /// **Cascade** every open (non-minimized) window from the top-left, staggered, and
    /// re-persist their geometry. Restores minimized windows so the cascade is whole.
    fn cascade_windows(&mut self) {
        let mut keys: Vec<WinKey> = self.windows.keys().copied().collect();
        keys.sort_by_key(|k| self.windows[k].z);
        for (i, key) in keys.iter().enumerate() {
            let off = i as f32 * 28.0;
            if let Some(ws) = self.windows.get_mut(key) {
                ws.x = 300.0 + off;
                ws.y = MENUBAR_H + 12.0 + off;
                ws.minimized = false;
                ws.z = self.next_z;
                self.next_z += 1;
            }
            self.persist_window(*key);
        }
        self.status = format!("Cascaded {} window(s).", keys.len());
    }

    /// **Tile** every open window into a near-square grid filling the desktop below
    /// the menu bar, and re-persist. A pure layout actuation.
    fn tile_windows(&mut self) {
        let mut keys: Vec<WinKey> = self.windows.keys().copied().collect();
        keys.sort_by_key(|k| self.windows[k].z);
        let n = keys.len().max(1);
        let cols = (n as f32).sqrt().ceil() as usize;
        let rows = n.div_ceil(cols);
        // Tile across the left ~2/3 of a 1600-wide desktop so the icons + summary
        // widget on the right stay legible (the desktop is laid out for ~1600×1000).
        let area_x = 240.0;
        let area_y = MENUBAR_H + 8.0;
        let area_w = 1080.0;
        let area_h = 940.0;
        let cw = (area_w / cols as f32).max(WIN_MIN_W);
        let ch = (area_h / rows as f32).max(WIN_MIN_H);
        for (i, key) in keys.iter().enumerate() {
            let col = (i % cols) as f32;
            let row = (i / cols) as f32;
            if let Some(ws) = self.windows.get_mut(key) {
                ws.x = area_x + col * cw;
                ws.y = area_y + row * ch;
                ws.w = (cw - 8.0).max(WIN_MIN_W);
                ws.h = (ch - 8.0).max(WIN_MIN_H);
                ws.minimized = false;
            }
            self.persist_window(*key);
        }
        self.status = format!("Tiled {n} window(s) in a {cols}×{rows} grid.");
    }

    /// **Close all** open windows (and drop their persisted geometry).
    fn close_all_windows(&mut self) {
        let keys: Vec<WinKey> = self.windows.keys().copied().collect();
        let n = keys.len();
        for key in keys {
            self.close_window(key);
        }
        self.status = format!("Closed {n} window(s).");
    }

    /// Focus (raise + un-minimize) a window — what a taskbar-stub click does.
    fn focus_window(&mut self, key: WinKey) {
        if let Some(ws) = self.windows.get_mut(&key) {
            ws.minimized = false;
            ws.z = self.next_z;
            self.next_z += 1;
            self.persist_window(key);
        }
    }

    // ── Global mouse handling for the in-flight drag ─────────────────────────────

    fn on_mouse_move(&mut self, ev: &MouseMoveEvent, cx: &mut Context<Self>) {
        let Some(drag) = &self.drag else { return };
        match drag {
            Drag::Icon { cell, grab } => {
                let cell = *cell;
                let nx = pxf(ev.position.x - grab.x).max(0.0);
                let ny = pxf(ev.position.y - grab.y).max(MENUBAR_H);
                self.layout.set_icon_pos(&id_hex(&cell), nx, ny);
                cx.notify();
            }
            Drag::WinMove { key, grab } => {
                let key = *key;
                let nx = pxf(ev.position.x - grab.x);
                let ny = pxf(ev.position.y - grab.y).max(MENUBAR_H);
                if let Some(ws) = self.windows.get_mut(&key) {
                    ws.x = nx;
                    ws.y = ny;
                }
                cx.notify();
            }
            Drag::WinResize { key, origin } => {
                let key = *key;
                let nw = pxf(ev.position.x - origin.x).max(WIN_MIN_W);
                let nh = pxf(ev.position.y - origin.y).max(WIN_MIN_H);
                if let Some(ws) = self.windows.get_mut(&key) {
                    ws.w = nw;
                    ws.h = nh;
                }
                cx.notify();
            }
        }
    }

    fn on_mouse_up(&mut self, ev: &MouseUpEvent, cx: &mut Context<Self>) {
        let Some(drag) = self.drag.take() else { return };
        match drag {
            Drag::Icon { cell, .. } => {
                // Persist the new icon position (the spatial-persistence write).
                self.layout.save(&self.layout_path);
                // COMPOSE: if released over an OPEN DOCUMENT window, transclude the
                // cell into it. Else if over ANOTHER cell-icon, act across them.
                if let Some(into) = self.doc_window_under(ev.position) {
                    if into != cell {
                        self.transclude_into(cell, into);
                    }
                } else if let Some(dst) = self.icon_under(ev.position, Some(cell)) {
                    self.compose_drop(cell, dst);
                }
            }
            Drag::WinMove { key, .. } | Drag::WinResize { key, .. } => {
                self.persist_window(key);
            }
        }
        cx.notify();
    }

    /// Which OPEN document window (if any) sits under `p` — the drop target for the
    /// drag-to-transclude compose gesture.
    fn doc_window_under(&self, p: Point<Pixels>) -> Option<CellId> {
        let mut best: Option<(u32, CellId)> = None;
        for ((cell, tag), ws) in self.windows.iter() {
            if *tag != WinKindTag::DocEditor || ws.minimized {
                continue;
            }
            let within = p.x >= px(ws.x)
                && p.x <= px(ws.x + ws.w)
                && p.y >= px(ws.y)
                && p.y <= px(ws.y + ws.h);
            if within && best.map(|(z, _)| ws.z > z).unwrap_or(true) {
                best = Some((ws.z, *cell));
            }
        }
        best.map(|(_, c)| c)
    }

    /// Which cell-icon (other than `exclude`) sits under `p` — used by the compose
    /// drop to find the drop target.
    fn icon_under(&self, p: Point<Pixels>, exclude: Option<CellId>) -> Option<CellId> {
        for (idx, cell) in self.cells.iter().enumerate() {
            if Some(*cell) == exclude {
                continue;
            }
            let pos = self.icon_pos(idx, cell);
            let within_x = p.x >= pos.x && p.x <= pos.x + px(ICON_W);
            let within_y = p.y >= pos.y && p.y <= pos.y + px(ICON_H);
            if within_x && within_y {
                return Some(*cell);
            }
        }
        None
    }

    // ── Bake / test hooks (drive the live gestures headlessly) ───────────────────
    // These mirror exactly what the interactive mouse handlers do, so a headless
    // bake (or a test) can open windows, fire an actuation, and persist a drag —
    // and assert the real verified turn landed and the layout saved.

    /// Open an inspector window on `cell` (what a double-click does).
    pub fn bake_open_window(&mut self, cell: CellId) {
        self.open_window(cell);
    }

    /// Fire a transfer actuation `src → dst` of `amount` (what the right-click
    /// "Transfer" menu action does) — a REAL verified turn on the live World.
    pub fn bake_actuate_transfer(&mut self, src: CellId, _dst: CellId, amount: u64) {
        self.actuate(src, &ActionKind::Transfer { amount });
    }

    /// Move `cell`'s icon to `(x, y)` and persist the layout (what a drag-end does).
    pub fn bake_drag_icon(&mut self, cell: CellId, x: f32, y: f32) {
        self.layout.set_icon_pos(&id_hex(&cell), x, y);
        self.layout.save(&self.layout_path);
    }

    /// Open the right-click context menu on `cell` at `(x, y)` (the ACTUATION
    /// surface) so it is visible in a bake.
    pub fn bake_open_menu(&mut self, cell: CellId, x: f32, y: f32) {
        self.open_menu = Some(OpenMenu {
            cell: Some(cell),
            heading: format!("{} · {}", self.cell_kind(&cell), id_short(&cell)),
            at: Point::new(px(x), px(y)),
            actions: self.actions_for(cell),
        });
    }

    /// Open a DOCUMENT EDITOR window on `cell` (what "Open as Document" does).
    pub fn bake_open_doc(&mut self, cell: CellId) {
        self.open_kind(cell, WinKindTag::DocEditor);
    }

    /// Type `text` into `cell`'s document editor — a receipted patch + a verified
    /// SetField revision turn (what the live editor's keystrokes do).
    pub fn bake_edit_doc(&mut self, cell: CellId, text: &str) {
        if self.windows.get(&(cell, WinKindTag::DocEditor)).is_none() {
            self.open_kind(cell, WinKindTag::DocEditor);
        }
        self.edit_doc(cell, text.to_string());
        // The live editor widget re-seeds from the buffer on next render (this bake
        // hook has no `&mut Window` to push into `InputState` directly).
        self.doc_resync.insert(cell);
    }

    /// COMPOSE: transclude `src` into the open document on `into` (a receipted patch
    /// + verified turn) — what dragging a cell-icon onto a document does.
    pub fn bake_transclude(&mut self, src: CellId, into: CellId) {
        self.transclude_into(src, into);
    }

    /// Open the LINKS / BACKLINKS window on `cell` (what "Links & Backlinks" does).
    pub fn bake_open_links(&mut self, cell: CellId) {
        self.open_kind(cell, WinKindTag::Links);
    }

    /// Open the TRANSCRIPT / receipt-log window (what "Transcript" does).
    pub fn bake_open_transcript(&mut self, cell: CellId) {
        self.open_kind(cell, WinKindTag::Transcript);
    }

    /// Open the PROPERTY inspector/editor over `cell` (what "Properties…" does).
    pub fn bake_open_properties(&mut self, cell: CellId) {
        self.open_properties(PropSubject::Cell(cell));
    }

    /// How many windows of `tag` are open (a bake/test assertion hook).
    pub fn bake_window_count(&self, kind_is_doc: bool) -> usize {
        let want = if kind_is_doc {
            WinKindTag::DocEditor
        } else {
            WinKindTag::Inspector
        };
        self.windows.keys().filter(|(_, t)| *t == want).count()
    }

    /// The current edit-buffer text of `cell`'s open document (a bake/test hook).
    pub fn bake_doc_text(&self, cell: CellId) -> String {
        self.load_doc_buffer(cell)
    }

    /// The live `InputState` editor entity for `cell`'s open document, if the doc body
    /// has rendered at least once (so `ensure_doc_input` built it). A test hook: lets a
    /// headless test TYPE into the REAL widget (`insert`/`set_value`) and assert the
    /// keystroke→heap seam fires, exercising the genuine `Change` subscription rather
    /// than a bypass.
    pub fn bake_doc_input(&self, cell: CellId) -> Option<Entity<InputState>> {
        self.doc_inputs.get(&cell).cloned()
    }

    /// **Structured link assertion (a bake/test hook)** — does `doc`'s document carry
    /// a transclusion that resolves to `target` (an OUTBOUND link), and does `target`'s
    /// Links view see `doc` as a BACKLINK (← mentions this)? Returns `(outbound, back)`.
    /// Reuses the exact `parse_transclusion_ref` the Links window renders with, so the
    /// assertion tracks the real surface.
    pub fn bake_doc_links(&self, doc: CellId, target: CellId) -> (bool, bool) {
        let prose = self.load_doc_buffer(doc);
        let outbound = prose
            .lines()
            .filter_map(parse_transclusion_ref)
            .any(|t| t == target);
        // The backlink is the same parse inverted: target sees doc mentioning it.
        let back = self
            .read_doc_from_heap(&doc)
            .or_else(|| Some(prose.clone()))
            .unwrap_or_default()
            .lines()
            .filter_map(parse_transclusion_ref)
            .any(|t| t == target)
            && doc != target;
        (outbound, back)
    }

    /// **Cascade** all open windows (the Window→Cascade command) — a bake/test hook.
    /// Pure layout; fires NO verified turn. Returns the open-window count moved.
    pub fn bake_cascade_windows(&mut self) -> usize {
        let n = self.windows.len();
        self.cascade_windows();
        n
    }

    /// **Tile** all open windows (the Window→Tile command) — a bake/test hook.
    pub fn bake_tile_windows(&mut self) -> usize {
        let n = self.windows.len();
        self.tile_windows();
        n
    }

    /// The total open-window count across ALL kinds (a bake/test assertion hook).
    pub fn bake_total_window_count(&self) -> usize {
        self.windows.len()
    }

    /// The World's conservation sum (Σ balance) — a bake/test hook over the live
    /// ledger (the desktop's World-summary widget reflects it; it must read 0).
    pub fn bake_world_balance_sum(&self) -> i64 {
        self.world_balance_sum()
    }
}

// ── Rendering ─────────────────────────────────────────────────────────────────────
// (The `bevel_raised` / `face_section` / `face_row` chrome primitives live in
// `chrome.rs` and are imported above.)

impl Render for DeosDesktop {
    fn render(&mut self, window: &mut Window, cx: &mut Context<Self>) -> impl IntoElement {
        let mut root = div()
            .id("deos-desktop-root")
            .size_full()
            .bg(gpui::rgb(self.layout.prefs.bg))
            .text_color(gpui::rgb(NT_TEXT))
            .font_family("Lilex")
            .text_size(px(12.0))
            // Global drag handling (move/up anywhere on the desktop drive the
            // in-flight icon/window drag).
            .on_mouse_move(
                cx.listener(|this, ev: &MouseMoveEvent, _w, cx| this.on_mouse_move(ev, cx)),
            )
            .on_mouse_up(
                MouseButton::Left,
                cx.listener(|this, ev: &MouseUpEvent, _w, cx| this.on_mouse_up(ev, cx)),
            )
            // A left-click on the bare desktop dismisses an open menu/dialog.
            .on_mouse_down(
                MouseButton::Left,
                cx.listener(|this, _ev: &MouseDownEvent, _w, cx| {
                    if this.open_menu.take().is_some() {
                        cx.notify();
                    }
                }),
            )
            // A right-click on the bare desktop opens the DESKTOP context menu.
            .on_mouse_down(
                MouseButton::Right,
                cx.listener(|this, ev: &MouseDownEvent, _w, cx| {
                    this.open_menu = Some(OpenMenu {
                        cell: None,
                        heading: "Desktop".into(),
                        at: ev.position,
                        actions: this.desktop_actions(),
                    });
                    cx.notify();
                }),
            );

        // ── The menu bar (NT-style) ──────────────────────────────────────────────
        root = root.child(self.render_menubar(cx));

        // ── The desktop icons (cells) ────────────────────────────────────────────
        let cells = self.cells.clone();
        for (idx, cell) in cells.iter().enumerate() {
            root = root.child(self.render_icon(idx, *cell, cx));
        }

        // ── The World-summary widget (pinned top-right, fills the empty margin) ───
        root = root.child(self.render_world_widget());

        // ── The open windows (z-ordered) ─────────────────────────────────────────
        let mut wins: Vec<WinKey> = self.windows.keys().copied().collect();
        wins.sort_by_key(|k| self.windows[k].z);
        for key in wins {
            root = root.child(self.render_window(key, window, cx));
        }

        // ── The context menu overlay (the ACTUATION) ─────────────────────────────
        if self.open_menu.is_some() {
            root = root.child(self.render_context_menu(cx));
        }

        // ── The property dialog overlay (the PROPERTY inspector/editor) ───────────
        if self.open_prop.is_some() {
            root = root.child(self.render_property_dialog(cx));
        }

        // ── The taskbar (open-window stubs) + the status bar ─────────────────────
        root = root.child(self.render_taskbar(cx));
        root = root.child(self.render_statusbar());

        root
    }
}

impl DeosDesktop {
    fn render_menubar(&self, cx: &mut Context<Self>) -> impl IntoElement {
        let menus = ["World", "Cell", "View", "Window", "Help"];
        let user = self.user;
        let mut bar = div()
            .absolute()
            .left(px(0.0))
            .top(px(0.0))
            .w_full()
            .h(px(MENUBAR_H))
            .flex()
            .flex_row()
            .items_center()
            .bg(gpui::rgb(NT_FACE))
            .border_b_1()
            .border_color(gpui::rgb(NT_SHADOW));
        // The deos mark on the far left (the "Start"-equivalent system menu).
        bar = bar.child(
            div()
                .px_2()
                .h_full()
                .flex()
                .items_center()
                .bg(gpui::rgb(NT_FACE_DARK))
                .child(div().font_weight(FontWeight::BOLD).child("deos")),
        );
        for (i, name) in menus.iter().enumerate() {
            let name = *name;
            let at_x = 64.0 + i as f32 * 56.0;
            bar = bar.child(
                div()
                    .id(gpui::SharedString::from(format!("menu-{name}")))
                    .px_3()
                    .h_full()
                    .flex()
                    .items_center()
                    .hover(|s| {
                        s.bg(gpui::rgb(NT_MENU_HILIGHT))
                            .text_color(gpui::rgb(NT_TITLE_TEXT))
                    })
                    // Clicking a menu-bar item drops its menu (the NT pull-down).
                    .on_mouse_down(
                        MouseButton::Left,
                        cx.listener(move |this, _ev: &MouseDownEvent, _w, cx| {
                            let actions = this.menubar_actions(name);
                            this.open_menu = Some(OpenMenu {
                                cell: Some(user),
                                heading: name.to_string(),
                                at: Point::new(px(at_x), px(MENUBAR_H)),
                                actions,
                            });
                            cx.notify();
                        }),
                    )
                    .child(name.to_string()),
            );
        }
        // A live height/cell-count readout on the far right (the World face).
        let h = self.world.borrow().height();
        let n = self.cells.len();
        bar = bar.child(
            div()
                .ml_auto()
                .px_3()
                .h_full()
                .flex()
                .items_center()
                .text_color(gpui::rgb(NT_DIM))
                .child(format!("World · {n} cells · height {h}")),
        );
        let _ = cx;
        bar
    }

    fn render_icon(&self, idx: usize, cell: CellId, cx: &mut Context<Self>) -> impl IntoElement {
        let pos = self.icon_pos(idx, &cell);
        let kind = self.cell_kind(&cell);
        let bal = self.cell_balance(&cell);
        let held = self.holds(&cell);
        // A font-safe single-letter kind badge (the geometric/dingbat icon glyphs are
        // tofu in the bake font, so a dense letter stands in: T/W/S/A).
        let glyph = match kind {
            "treasury" => "T",
            "issuer well" => "W",
            "service" => "S",
            _ => "A",
        };
        let label = if self.layout.prefs.show_balances {
            format!("{}\n{}\n{}", kind, id_short(&cell), fmt_balance(bal))
        } else {
            format!("{}\n{}", kind, id_short(&cell))
        };

        div()
            .id(gpui::SharedString::from(format!("icon-{}", id_hex(&cell))))
            .absolute()
            .left(pos.x)
            .top(pos.y)
            .w(px(ICON_W))
            .h(px(ICON_H))
            .flex()
            .flex_col()
            .items_center()
            .justify_start()
            .pt_1()
            // Drag to move; the mouse-down records the grab offset and starts a drag.
            .on_mouse_down(
                MouseButton::Left,
                cx.listener(move |this, ev: &MouseDownEvent, _w, cx| {
                    this.open_menu = None;
                    let idx = this.cells.iter().position(|c| *c == cell).unwrap_or(0);
                    let p = this.icon_pos(idx, &cell);
                    this.drag = Some(Drag::Icon {
                        cell,
                        grab: Point::new(ev.position.x - p.x, ev.position.y - p.y),
                    });
                    cx.notify();
                }),
            )
            // Double-click opens the inspector window.
            .on_click(cx.listener(move |this, ev: &ClickEvent, _w, cx| {
                if ev.click_count() >= 2 {
                    this.open_window(cell);
                    cx.notify();
                }
            }))
            // Right-click opens the context menu (the ACTUATION surface).
            .on_mouse_down(
                MouseButton::Right,
                cx.listener(move |this, ev: &MouseDownEvent, _w, cx| {
                    this.open_menu = Some(OpenMenu {
                        cell: Some(cell),
                        heading: format!("{} · {}", this.cell_kind(&cell), id_short(&cell)),
                        at: ev.position,
                        actions: this.actions_for(cell),
                    });
                    cx.notify();
                }),
            )
            .child(
                // The 32x32 glyph tile (a raised NT bevel face).
                bevel_raised(div())
                    .w(px(40.0))
                    .h(px(40.0))
                    .flex()
                    .items_center()
                    .justify_center()
                    .text_size(px(22.0))
                    .when(!held, |d| d.opacity(0.55))
                    .child(glyph),
            )
            .child(
                div()
                    .mt_1()
                    .px_1()
                    .text_size(px(10.0))
                    .text_color(gpui::rgb(NT_ICON_LABEL))
                    .text_center()
                    .child(label),
            )
    }

    fn render_window(
        &mut self,
        key: WinKey,
        window: &mut Window,
        cx: &mut Context<Self>,
    ) -> AnyElement {
        let (cell, tag) = key;
        let (x, y, w, h, title, minimized) = {
            let ws = &self.windows[&key];
            (ws.x, ws.y, ws.w, ws.h, ws.title.clone(), ws.minimized)
        };

        if minimized {
            // A minimized window collapses to a title-bar stub at its origin.
            return div()
                .id(gpui::SharedString::from(format!(
                    "winmin-{}-{:?}",
                    id_hex(&cell),
                    tag as u8
                )))
                .absolute()
                .left(px(x))
                .top(px(y))
                .w(px(180.0))
                .child(self.render_titlebar(key, &title, true, cx))
                .into_any_element();
        }

        // The body varies by window TYPE — the NT/Pharo density.
        let body = match tag {
            WinKindTag::Inspector => self.render_inspector_body(cell, cx),
            WinKindTag::DocEditor => self.render_doc_body(cell, window, cx),
            WinKindTag::Links => self.render_links_body(cell),
            WinKindTag::Transcript => self.render_transcript_body(),
            WinKindTag::Workflow => self.render_workflow_body(cell, cx),
            _ => self.render_inspector_body(cell, cx),
        };

        let resize_grip = div()
            .id(gpui::SharedString::from(format!(
                "resize-{}-{:?}",
                id_hex(&cell),
                tag as u8
            )))
            .absolute()
            .right(px(0.0))
            .bottom(px(0.0))
            .w(px(14.0))
            .h(px(14.0))
            .bg(gpui::rgb(NT_FACE_DARK))
            .on_mouse_down(
                MouseButton::Left,
                cx.listener(move |this, _ev: &MouseDownEvent, _w, cx| {
                    if let Some(ws) = this.windows.get(&key) {
                        this.drag = Some(Drag::WinResize {
                            key,
                            origin: Point::new(px(ws.x), px(ws.y)),
                        });
                    }
                    cx.notify();
                }),
            )
            .text_size(px(8.0))
            .flex()
            .items_center()
            .justify_center()
            .child(GLYPH_GRIP);

        div()
            .id(gpui::SharedString::from(format!(
                "win-{}-{:?}",
                id_hex(&cell),
                tag as u8
            )))
            .absolute()
            .left(px(x))
            .top(px(y))
            .w(px(w))
            .h(px(h))
            .flex()
            .flex_col()
            .bg(gpui::rgb(NT_FACE))
            .border_2()
            .border_color(gpui::rgb(NT_SHADOW))
            // Clicking anywhere in the window raises it.
            .on_mouse_down(
                MouseButton::Left,
                cx.listener(move |this, _ev: &MouseDownEvent, _w, cx| {
                    if let Some(ws) = this.windows.get_mut(&key) {
                        ws.z = this.next_z;
                        this.next_z += 1;
                    }
                    cx.notify();
                }),
            )
            // Right-click anywhere on the window chrome opens the WINDOW menu.
            .on_mouse_down(MouseButton::Right, {
                let title_for_menu = title.clone();
                cx.listener(move |this, ev: &MouseDownEvent, _w, cx| {
                    this.open_menu = Some(OpenMenu {
                        cell: Some(cell),
                        heading: title_for_menu.clone(),
                        at: ev.position,
                        actions: this.window_actions(cell, tag),
                    });
                    cx.notify();
                })
            })
            .child(self.render_titlebar(key, &title, false, cx))
            .child(body)
            .child(resize_grip)
            .into_any_element()
    }

    /// The classic reflective inspector body (identity + live state + affordances +
    /// a Properties button).
    fn render_inspector_body(&self, cell: CellId, cx: &mut Context<Self>) -> AnyElement {
        let bal = self.cell_balance(&cell);
        let nonce = self.cell_nonce(&cell);
        let lifecycle = self.cell_lifecycle(&cell);
        let caps = self.cell_cap_count(&cell);
        let kind = self.cell_kind(&cell);
        let rev = self.cell_field_u64(&cell, DOC_REV_SLOT);
        let held = self.holds(&cell);
        let receipts = self.cell_receipt_count(&cell);
        // The balance gauge denominator — the World's largest holder.
        let gauge = (bal.max(0) as f32) / (self.world_max_balance() as f32);
        // The lifecycle reads green when Live, amber otherwise (a sealed/migrated cell).
        let life_color = if lifecycle == "Live" {
            0x0a7a2a
        } else {
            0xa06000
        };

        let mut col = div()
            .id(gpui::SharedString::from(format!(
                "winbody-{}",
                id_hex(&cell)
            )))
            .flex_1()
            .min_h(px(0.0))
            .overflow_y_scroll()
            .bg(gpui::rgb(0xf4f4f4))
            .p_2()
            .flex()
            .flex_col()
            .gap_1()
            .child(face_section("Identity"))
            .child(face_row("id", &id_hex(&cell)))
            .child(face_row("kind", kind))
            .child(face_row_color(
                "authority",
                if held { "held (lit)" } else { "system (dim)" },
                if held { 0x0a7a2a } else { NT_DIM },
            ))
            .child(face_section("State (live)"))
            .child(face_row("balance", &fmt_balance(bal)))
            .child(face_gauge(gauge))
            .child(face_row("nonce", &nonce.to_string()))
            .child(face_row_color("lifecycle", &lifecycle, life_color))
            .child(face_row("capabilities", &caps.to_string()))
            .child(face_row("doc revision", &rev.to_string()))
            .child(face_row("turns by cell", &receipts.to_string()));

        // ── State slots (the raw committed fields — Pharo "inspect everything") ──
        col = col.child(face_section("State slots (committed fields)"));
        for slot in 0..8usize {
            let v = self.cell_field_u64(&cell, slot);
            // Only show non-zero slots plus slot 0 (keeps the dense view legible).
            if v != 0 || slot == 0 {
                col = col.child(face_row(&format!("field[{slot}]"), &v.to_string()));
            }
        }

        // ── The committed document, if this cell carries one (the inspector REFLECTS
        //    the document that IS the cell — a prose preview off the committed heap) ──
        if let Some(prose) = self.read_doc_from_heap(&cell) {
            col = col.child(face_section("Document (committed prose)"));
            let bytes = prose.len();
            let lines = prose
                .lines()
                .count()
                .max(if prose.is_empty() { 0 } else { 1 });
            col = col.child(face_row("bytes on heap", &bytes.to_string()));
            col = col.child(face_row("lines", &lines.to_string()));
            let preview: String = prose.chars().take(140).collect();
            let preview = if prose.chars().count() > 140 {
                format!("{preview}…")
            } else {
                preview
            };
            col = col.child(
                div()
                    .my_1()
                    .p_1()
                    .bg(gpui::rgb(0xffffff))
                    .border_1()
                    .border_color(gpui::rgb(NT_FACE_DARK))
                    .text_size(px(10.0))
                    .child(if preview.is_empty() {
                        "(empty document)".to_string()
                    } else {
                        preview
                    }),
            );
        }

        // ── Recent turns whose agent IS this cell (the cell's own chronicle) ──
        col = col.child(face_section("Recent turns (this cell)"));
        let cell_receipts: Vec<String> = {
            let w = self.world.borrow();
            w.receipts()
                .iter()
                .filter(|r| r.agent == cell)
                .rev()
                .take(5)
                .map(|r| {
                    let hh: String = r.turn_hash[..3]
                        .iter()
                        .map(|b| format!("{b:02x}"))
                        .collect();
                    let post: String = r.post_state_hash[..3]
                        .iter()
                        .map(|b| format!("{b:02x}"))
                        .collect();
                    format!("turn {hh} → post {post}")
                })
                .collect()
        };
        if cell_receipts.is_empty() {
            col = col.child(face_row("(none)", "actuate to write a receipt"));
        } else {
            for (i, line) in cell_receipts.iter().enumerate() {
                col = col.child(face_row(&format!("[{i}]"), line));
            }
        }

        col.child(face_section("Affordances (do it)"))
            .child(self.affordance_button(cell, "Bump nonce", ActionKind::BumpNonce, cx))
            .child(self.affordance_button(
                cell,
                &format!("Transfer 1,000 → {}", id_short(&self.user)),
                ActionKind::Transfer { amount: 1_000 },
                cx,
            ))
            .child(self.affordance_button(
                cell,
                &format!("Grant cap → {}", id_short(&self.user)),
                ActionKind::Grant { target: self.user },
                cx,
            ))
            .child(self.affordance_button(cell, "Open as Document…", ActionKind::OpenDoc, cx))
            .child(self.affordance_button(cell, "Properties…", ActionKind::Properties, cx))
            .into_any_element()
    }

    /// **The document-editor body** — the cell's prose, the live chronicle (patch
    /// count), and the receipted-edit controls. Typing here is a `dregg_doc::Patch`
    /// plus a verified revision turn (the document IS the cell).
    fn render_doc_body(
        &mut self,
        cell: CellId,
        window: &mut Window,
        cx: &mut Context<Self>,
    ) -> AnyElement {
        // Build the live free-typing editor on first render of this doc body (it needs
        // `window`/`cx`). Keystrokes flow Change → `edit_doc` → committed heap.
        self.ensure_doc_input(cell, window, cx);
        // Apply a pending external edit (transclude / bake) into the live widget — the
        // editing paths that lack `&mut Window` deferred the `set_value` to here.
        if self.doc_resync.remove(&cell) {
            let text = self.load_doc_buffer(cell);
            if let Some(input) = self.doc_inputs.get(&cell).cloned() {
                input.update(cx, |st, cx| st.set_value(&text, window, cx));
            }
        }

        let patches = match self
            .windows
            .get(&(cell, WinKindTag::DocEditor))
            .map(|w| &w.kind)
        {
            Some(WinKind::DocEditor { doc, .. }) => doc.history().len(),
            _ => 0,
        };
        let rev = self.cell_field_u64(&cell, DOC_REV_SLOT);
        let input = self.doc_inputs.get(&cell).cloned();
        div()
            .id(gpui::SharedString::from(format!(
                "docbody-{}",
                id_hex(&cell)
            )))
            .flex_1()
            .min_h(px(0.0))
            .overflow_y_scroll()
            .bg(gpui::rgb(0xfbfbf0))
            .p_2()
            .flex()
            .flex_col()
            .gap_1()
            .child(face_section(
                "Document (free-typing — every keystroke is a receipted patch)",
            ))
            .child(
                // THE PROSE SURFACE — a REAL editable text field (gpui-component's
                // rope-backed multi-line `Input`). Click in and type; each keystroke
                // commits into the cell's heap. Drag a cell-icon here to transclude it.
                div()
                    .id(gpui::SharedString::from(format!(
                        "docprose-{}",
                        id_hex(&cell)
                    )))
                    .flex_1()
                    .min_h(px(120.0))
                    .bg(gpui::rgb(0xffffff))
                    .border_1()
                    .border_color(gpui::rgb(NT_FACE_DARK))
                    .text_size(px(12.0))
                    .when_some(input, |this, input| this.child(Input::new(&input).h_full())),
            )
            .child(face_section("Chronicle"))
            .child(face_row("patches", &patches.to_string()))
            .child(face_row("cell revision", &rev.to_string()))
            .child(face_row("author", &format!("{}", self.author.0 & 0xffff)))
            .into_any_element()
    }

    /// **The links / backlinks body** — which cells this one reaches (its caps),
    /// which transclusions are composed into it, and the World's reach.
    fn render_links_body(&self, cell: CellId) -> AnyElement {
        let caps = self.cell_cap_count(&cell);
        let mut col = div()
            .id(gpui::SharedString::from(format!(
                "linksbody-{}",
                id_hex(&cell)
            )))
            .flex_1()
            .min_h(px(0.0))
            .overflow_y_scroll()
            .bg(gpui::rgb(0xf0f4f8))
            .p_2()
            .flex()
            .flex_col()
            .gap_1()
            .child(face_section("Outbound (capabilities)"))
            .child(face_row("cap count", &caps.to_string()));
        // ── Composed-in: transclusions this cell's document reaches. Each line is
        //    parsed back to a STRUCTURED reference and the referenced cell's LIVE faces
        //    (kind · balance · lifecycle) are re-read off the ledger — so a backlink
        //    reflects the target's current state, not the stale text snapshot. ──
        let doc = self.load_doc_buffer(cell);
        let outbound: Vec<CellId> = doc.lines().filter_map(parse_transclusion_ref).collect();
        col = col.child(face_section("Composed-in (transclusions →)"));
        if outbound.is_empty() {
            col = col.child(face_row(
                "transclusions",
                "(none — drag a cell onto its doc)",
            ));
        } else {
            for tgt in &outbound {
                if self.world.borrow().ledger().get(tgt).is_some() {
                    col = col.child(face_row(
                        &format!("→ {}", id_short(tgt)),
                        &format!(
                            "{} · {} · {}",
                            self.cell_kind(tgt),
                            fmt_balance(self.cell_balance(tgt)),
                            self.cell_lifecycle(tgt),
                        ),
                    ));
                } else {
                    col = col.child(face_row(&format!("→ {}", id_short(tgt)), "(no such cell)"));
                }
            }
        }

        // ── Backlinks: which OTHER cells' documents transclude THIS one. A reverse
        //    scan over every committed document on the desktop (the open windows +
        //    the heap-backed prose) — "what points here". ──
        let here = cell;
        let backlinks: Vec<CellId> = self
            .cells
            .iter()
            .filter(|other| **other != here)
            .filter(|other| {
                let prose = self
                    .read_doc_from_heap(other)
                    .or_else(|| {
                        self.windows
                            .get(&(**other, WinKindTag::DocEditor))
                            .and_then(|w| match &w.kind {
                                WinKind::DocEditor { buffer, .. } => Some(buffer.clone()),
                                _ => None,
                            })
                    })
                    .unwrap_or_default();
                prose
                    .lines()
                    .filter_map(parse_transclusion_ref)
                    .any(|t| t == here)
            })
            .copied()
            .collect();
        col = col.child(face_section("Backlinks (← mentions this)"));
        if backlinks.is_empty() {
            col = col.child(face_row("backlinks", "(none point here yet)"));
        } else {
            for src in &backlinks {
                col = col.child(face_row(
                    &format!("← {}", id_short(src)),
                    &format!("{} mentions this", self.cell_kind(src)),
                ));
            }
        }

        col = col
            .child(face_section("World"))
            .child(face_row("cells", &self.cells.len().to_string()))
            .child(face_row(
                "height",
                &self.world.borrow().height().to_string(),
            ));
        col.into_any_element()
    }

    /// **The transcript / receipt-log body** — the World's receipt chain, the
    /// chronicle the user's "do it"s have written.
    fn render_transcript_body(&self) -> AnyElement {
        let w = self.world.borrow();
        let receipts = w.receipts();
        let n = receipts.len();
        let mut col = div()
            .id("transcript-body")
            .flex_1()
            .min_h(px(0.0))
            .overflow_y_scroll()
            .bg(gpui::rgb(0x101820))
            .text_color(gpui::rgb(0x9fe0a0))
            .p_2()
            .flex()
            .flex_col()
            .gap_1()
            .child(div().text_color(gpui::rgb(0x6fc0ff)).child(format!(
                "── World receipt log · {n} turns · height {} ",
                w.height()
            )));
        // The last ~24 receipts, newest last (the dense scrolling log).
        let start = n.saturating_sub(24);
        for (i, r) in receipts.iter().enumerate().skip(start) {
            let hash = r.turn_hash;
            let hh: String = hash[..4].iter().map(|b| format!("{b:02x}")).collect();
            let post: String = r.post_state_hash[..4]
                .iter()
                .map(|b| format!("{b:02x}"))
                .collect();
            col = col.child(div().text_size(px(11.0)).child(format!(
                "#{i:<4} turn {hh} → post {post}  agent {}",
                id_short(&r.agent)
            )));
        }
        if n == 0 {
            col = col.child(div().child("(no turns yet — actuate a cell)"));
        }
        col.into_any_element()
    }

    fn render_titlebar(
        &self,
        key: WinKey,
        title: &str,
        minimized: bool,
        cx: &mut Context<Self>,
    ) -> Stateful<Div> {
        let (cell, tag) = key;
        // A font-safe 3-letter kind badge (the geometric window glyphs render as tofu
        // in the bake font, so the dense legible tag stands in for them).
        let glyph = kind_short(tag);
        // NT navy title bar with min/max/close glyph buttons. The bar grabs a
        // window-move drag on mouse-down; the buttons fire close/minimize.
        div()
            .id(gpui::SharedString::from(format!(
                "title-{}-{:?}",
                id_hex(&cell),
                tag as u8
            )))
            .h(px(22.0))
            .flex()
            .flex_row()
            .items_center()
            .bg(gpui::rgb(NT_TITLE_ACTIVE))
            .text_color(gpui::rgb(NT_TITLE_TEXT))
            .px_1()
            .on_mouse_down(
                MouseButton::Left,
                cx.listener(move |this, ev: &MouseDownEvent, _w, cx| {
                    if let Some(ws) = this.windows.get(&key) {
                        this.drag = Some(Drag::WinMove {
                            key,
                            grab: Point::new(ev.position.x - px(ws.x), ev.position.y - px(ws.y)),
                        });
                    }
                    cx.notify();
                }),
            )
            // Right-click the title bar → the deep WINDOW menu.
            .on_mouse_down(
                MouseButton::Right,
                cx.listener(move |this, ev: &MouseDownEvent, _w, cx| {
                    this.open_menu = Some(OpenMenu {
                        cell: Some(cell),
                        heading: format!("{} {}", glyph, id_short(&cell)),
                        at: ev.position,
                        actions: this.window_actions(cell, tag),
                    });
                    cx.notify();
                }),
            )
            .child(
                div()
                    .mx_1()
                    .px_1()
                    .text_size(px(9.0))
                    .bg(gpui::rgb(0x000050))
                    .text_color(gpui::rgb(0xc0d0ff))
                    .child(glyph),
            )
            .child(
                div()
                    .flex_1()
                    .px_1()
                    .text_size(px(11.0))
                    .font_weight(FontWeight::BOLD)
                    .child(title.to_string()),
            )
            // A live status badge for document windows — the receipt landing in the
            // title bar as you type (rev · patches · saved✓), read off committed state.
            .when(tag == WinKindTag::DocEditor, |row| {
                let rev = self.cell_field_u64(&cell, DOC_REV_SLOT);
                let patches = match self
                    .windows
                    .get(&(cell, WinKindTag::DocEditor))
                    .map(|w| &w.kind)
                {
                    Some(WinKind::DocEditor { doc, .. }) => doc.history().len(),
                    _ => 0,
                };
                row.child(
                    div()
                        .mx_1()
                        .px_1()
                        .text_size(px(9.0))
                        .bg(gpui::rgb(0x0a3a14))
                        .text_color(gpui::rgb(0x9fe0a8))
                        .child(format!("rev {rev} · {patches}¶ · heap✓")),
                )
            })
            .child(self.title_btn(key, GLYPH_MIN, TitleBtn::Minimize, cx))
            .child(self.title_btn(
                key,
                if minimized { GLYPH_RESTORE } else { GLYPH_MAX },
                TitleBtn::Maximize,
                cx,
            ))
            .child(self.title_btn(key, GLYPH_CLOSE, TitleBtn::Close, cx))
    }

    fn title_btn(
        &self,
        key: WinKey,
        glyph: &str,
        which: TitleBtn,
        cx: &mut Context<Self>,
    ) -> impl IntoElement {
        let (cell, tag) = key;
        let glyph = glyph.to_string();
        div()
            .id(gpui::SharedString::from(format!(
                "titlebtn-{}-{:?}-{glyph}",
                id_hex(&cell),
                tag as u8
            )))
            .ml_1()
            .w(px(16.0))
            .h(px(14.0))
            .flex()
            .items_center()
            .justify_center()
            .bg(gpui::rgb(NT_FACE))
            .text_color(gpui::rgb(NT_TEXT))
            .text_size(px(9.0))
            .border_1()
            .border_color(gpui::rgb(NT_SHADOW))
            .hover(|s| s.bg(gpui::rgb(NT_FACE_DARK)))
            .on_mouse_down(
                MouseButton::Left,
                cx.listener(move |this, _ev: &MouseDownEvent, _w, cx| {
                    // Swallow the title-drag the parent bar would otherwise start, and
                    // perform the window-control action.
                    this.drag = None;
                    match which {
                        TitleBtn::Close => this.close_window(key),
                        TitleBtn::Minimize => {
                            if let Some(ws) = this.windows.get_mut(&key) {
                                ws.minimized = true;
                            }
                            this.persist_window(key);
                        }
                        TitleBtn::Maximize => {
                            if let Some(ws) = this.windows.get_mut(&key) {
                                ws.minimized = false;
                            }
                            this.persist_window(key);
                        }
                    }
                    cx.notify();
                }),
            )
            .child(glyph)
    }

    /// A title-bar action wired through the desktop (close/min uses a click handler
    /// on the wrapping element; broken out so the drag handler can sit on the bar).
    fn affordance_button(
        &self,
        cell: CellId,
        label: &str,
        kind: ActionKind,
        cx: &mut Context<Self>,
    ) -> impl IntoElement {
        let held = match &kind {
            ActionKind::Transfer { amount } => {
                self.holds(&cell) && self.cell_balance(&cell) >= *amount as i64
            }
            _ => self.holds(&cell),
        };
        let kind2 = kind.clone();
        bevel_raised(
            div()
                .id(gpui::SharedString::from(format!(
                    "aff-{}-{label}",
                    id_hex(&cell)
                )))
                .px_2()
                .py_1()
                .my_1()
                .text_size(px(11.0)),
        )
        .when(!held, |d| d.opacity(0.5).text_color(gpui::rgb(NT_DIM)))
        .when(held, |d| {
            d.on_mouse_down(
                MouseButton::Left,
                cx.listener(move |this, _ev: &MouseDownEvent, _w, cx| {
                    this.actuate(cell, &kind2);
                    cx.notify();
                }),
            )
        })
        .child(label.to_string())
    }

    fn render_context_menu(&self, cx: &mut Context<Self>) -> impl IntoElement {
        let menu = self.open_menu.as_ref().unwrap();
        let cell = menu.cell;
        let heading = menu.heading.clone();
        let key_base = cell.map(|c| id_hex(&c)).unwrap_or_else(|| "desktop".into());
        let mut m = div()
            .absolute()
            .left(menu.at.x)
            .top(menu.at.y)
            .w(px(268.0))
            .bg(gpui::rgb(NT_FACE))
            .border_2()
            .border_color(gpui::rgb(NT_SHADOW))
            .py_1()
            .flex()
            .flex_col();
        // A header naming the object the menu acts on.
        m = m.child(
            div()
                .px_2()
                .py_1()
                .text_size(px(10.0))
                .font_weight(FontWeight::BOLD)
                .text_color(gpui::rgb(NT_TITLE_ACTIVE))
                .border_b_1()
                .border_color(gpui::rgb(NT_FACE_DARK))
                .child(heading),
        );
        for (i, action) in menu.actions.iter().enumerate() {
            if action.separator {
                m = m.child(div().mx_2().my_1().h(px(1.0)).bg(gpui::rgb(NT_FACE_DARK)));
                continue;
            }
            let kind = action.kind.clone();
            let held = action.held;
            let row = div()
                .id(gpui::SharedString::from(format!("ctx-{key_base}-{i}")))
                .px_3()
                .py_1()
                .text_size(px(12.0))
                .when(!held, |d| d.opacity(0.45).text_color(gpui::rgb(NT_DIM)))
                .when(held, |d| {
                    d.hover(|s| {
                        s.bg(gpui::rgb(NT_SELECT))
                            .text_color(gpui::rgb(NT_TITLE_TEXT))
                    })
                    .on_mouse_down(
                        MouseButton::Left,
                        cx.listener(move |this, _ev: &MouseDownEvent, _w, cx| {
                            match cell {
                                Some(c) => this.actuate(c, &kind),
                                None => this.actuate_desktop(&kind),
                            }
                            this.open_menu = None;
                            cx.notify();
                        }),
                    )
                })
                .child(action.label.clone());
            m = m.child(row);
        }
        m
    }

    /// **The property inspector/editor dialog** — an NT property sheet over a cell, a
    /// window, or the desktop. Cell properties are EDITABLE via receipted `SetField`
    /// turns; window/desktop properties are persisted layout changes.
    fn render_property_dialog(&self, cx: &mut Context<Self>) -> AnyElement {
        let dlg = self.open_prop.as_ref().unwrap();
        let (x, y, w, h) = (dlg.at.x, dlg.at.y, dlg.w, dlg.h);
        let (heading, body) = match dlg.subject.clone() {
            PropSubject::Cell(cell) => (
                format!("Properties — {} {}", self.cell_kind(&cell), id_short(&cell)),
                self.prop_body_cell(cell, cx),
            ),
            PropSubject::Window(cell, tag) => (
                format!("Window Properties — {}", id_short(&cell)),
                self.prop_body_window(cell, tag, cx),
            ),
            PropSubject::Desktop => (
                "Desktop Preferences & Customize".to_string(),
                self.prop_body_desktop(cx),
            ),
        };
        div()
            .id("prop-dialog")
            .absolute()
            .left(x)
            .top(y)
            .w(px(w))
            .h(px(h))
            .flex()
            .flex_col()
            .bg(gpui::rgb(NT_FACE))
            .border_2()
            .border_color(gpui::rgb(NT_SHADOW))
            .child(
                // The dialog title bar (with a close X).
                div()
                    .h(px(22.0))
                    .flex()
                    .flex_row()
                    .items_center()
                    .bg(gpui::rgb(NT_TITLE_ACTIVE))
                    .text_color(gpui::rgb(NT_TITLE_TEXT))
                    .px_1()
                    .child(
                        div()
                            .mx_1()
                            .px_1()
                            .text_size(px(9.0))
                            .bg(gpui::rgb(0x000050))
                            .text_color(gpui::rgb(0xc0d0ff))
                            .child("CFG"),
                    )
                    .child(
                        div()
                            .flex_1()
                            .px_1()
                            .text_size(px(11.0))
                            .font_weight(FontWeight::BOLD)
                            .child(heading),
                    )
                    .child(
                        div()
                            .id("prop-close")
                            .w(px(16.0))
                            .h(px(14.0))
                            .flex()
                            .items_center()
                            .justify_center()
                            .bg(gpui::rgb(NT_FACE))
                            .text_color(gpui::rgb(NT_TEXT))
                            .text_size(px(9.0))
                            .border_1()
                            .border_color(gpui::rgb(NT_SHADOW))
                            .on_mouse_down(
                                MouseButton::Left,
                                cx.listener(|this, _ev: &MouseDownEvent, _w, cx| {
                                    this.open_prop = None;
                                    cx.notify();
                                }),
                            )
                            .child(GLYPH_CLOSE),
                    ),
            )
            .child(body)
            .into_any_element()
    }

    fn prop_body_cell(&self, cell: CellId, cx: &mut Context<Self>) -> AnyElement {
        let bal = self.cell_balance(&cell);
        let nonce = self.cell_nonce(&cell);
        let rev = self.cell_field_u64(&cell, DOC_REV_SLOT);
        div()
            .id(gpui::SharedString::from(format!(
                "propcell-{}",
                id_hex(&cell)
            )))
            .flex_1()
            .min_h(px(0.0))
            .overflow_y_scroll()
            .bg(gpui::rgb(0xf4f4f4))
            .p_2()
            .flex()
            .flex_col()
            .gap_1()
            .child(face_section("Read-only"))
            .child(face_row("id", &id_hex(&cell)))
            .child(face_row("kind", self.cell_kind(&cell)))
            .child(face_row("balance", &fmt_balance(bal)))
            .child(face_row("nonce", &nonce.to_string()))
            .child(face_row("lifecycle", &self.cell_lifecycle(&cell)))
            .child(face_section("Editable (receipted SetField turn)"))
            .child(face_row("field[14] revision", &rev.to_string()))
            // The property-edit controls: each is a verified turn.
            .child(self.prop_setfield_button(cell, "revision +1", DOC_REV_SLOT, rev + 1, cx))
            .child(self.prop_setfield_button(cell, "revision =0", DOC_REV_SLOT, 0, cx))
            .child(self.prop_setfield_button(cell, "field[13] =42", 13, 42, cx))
            .into_any_element()
    }

    fn prop_setfield_button(
        &self,
        cell: CellId,
        label: &str,
        index: usize,
        value: u64,
        cx: &mut Context<Self>,
    ) -> impl IntoElement {
        let held = self.holds(&cell);
        bevel_raised(
            div()
                .id(gpui::SharedString::from(format!(
                    "propset-{}-{label}",
                    id_hex(&cell)
                )))
                .px_2()
                .py_1()
                .my_1()
                .text_size(px(11.0)),
        )
        .when(!held, |d| d.opacity(0.5).text_color(gpui::rgb(NT_DIM)))
        .when(held, |d| {
            d.on_mouse_down(
                MouseButton::Left,
                cx.listener(move |this, _ev: &MouseDownEvent, _w, cx| {
                    this.actuate(cell, &ActionKind::SetField { index, value });
                    cx.notify();
                }),
            )
        })
        .child(label.to_string())
    }

    fn prop_body_window(
        &self,
        cell: CellId,
        tag: WinKindTag,
        cx: &mut Context<Self>,
    ) -> AnyElement {
        let geom = self
            .windows
            .get(&(cell, tag))
            .map(|w| (w.x, w.y, w.w, w.h))
            .unwrap_or((0.0, 0.0, 0.0, 0.0));
        let _ = cx;
        div()
            .flex_1()
            .min_h(px(0.0))
            .bg(gpui::rgb(0xf4f4f4))
            .p_2()
            .flex()
            .flex_col()
            .gap_1()
            .child(face_section("Window (persisted layout)"))
            .child(face_row("x", &format!("{:.0}", geom.0)))
            .child(face_row("y", &format!("{:.0}", geom.1)))
            .child(face_row("w", &format!("{:.0}", geom.2)))
            .child(face_row("h", &format!("{:.0}", geom.3)))
            .into_any_element()
    }

    /// **The desktop Preferences body — customization.** Toggling these persists to
    /// the layout sidecar (a pure layout change: appearance/behaviour, no authority).
    fn prop_body_desktop(&self, cx: &mut Context<Self>) -> AnyElement {
        let p = &self.layout.prefs;
        div()
            .id("propdesktop")
            .flex_1()
            .min_h(px(0.0))
            .overflow_y_scroll()
            .bg(gpui::rgb(0xf4f4f4))
            .p_2()
            .flex()
            .flex_col()
            .gap_1()
            .child(face_section("Appearance"))
            .child(face_row("background", &format!("#{:06x}", p.bg)))
            // The background palette — clicking a swatch persists it.
            .child(
                div()
                    .flex()
                    .flex_row()
                    .gap_1()
                    .my_1()
                    .child(self.pref_swatch(NT_DESKTOP_BG, cx))
                    .child(self.pref_swatch(0x202830, cx))
                    .child(self.pref_swatch(0x2a1a3a, cx))
                    .child(self.pref_swatch(0x103020, cx)),
            )
            .child(face_section("Behaviour"))
            .child(self.pref_toggle(
                "Show icon balances",
                p.show_balances,
                PrefToggle::Balances,
                cx,
            ))
            .child(self.pref_toggle(
                "Word-granularity doc edits",
                p.word_granularity,
                PrefToggle::WordGran,
                cx,
            ))
            .child(face_row("grid rows", &p.grid_rows.to_string()))
            .child(
                div()
                    .flex()
                    .flex_row()
                    .gap_1()
                    .my_1()
                    .child(self.pref_rows_button(4, cx))
                    .child(self.pref_rows_button(6, cx))
                    .child(self.pref_rows_button(8, cx)),
            )
            .into_any_element()
    }

    fn pref_swatch(&self, color: u32, cx: &mut Context<Self>) -> impl IntoElement {
        let selected = self.layout.prefs.bg == color;
        div()
            .id(gpui::SharedString::from(format!("swatch-{color:06x}")))
            .w(px(28.0))
            .h(px(20.0))
            .bg(gpui::rgb(color))
            .border_2()
            .border_color(gpui::rgb(if selected { NT_HILIGHT } else { NT_SHADOW }))
            .on_mouse_down(
                MouseButton::Left,
                cx.listener(move |this, _ev: &MouseDownEvent, _w, cx| {
                    this.layout.prefs.bg = color;
                    this.layout.save(&this.layout_path);
                    this.status = format!("Desktop background → #{color:06x} (persisted).");
                    cx.notify();
                }),
            )
    }

    fn pref_toggle(
        &self,
        label: &str,
        on: bool,
        which: PrefToggle,
        cx: &mut Context<Self>,
    ) -> impl IntoElement {
        bevel_raised(
            div()
                .id(gpui::SharedString::from(format!("pref-{label}")))
                .px_2()
                .py_1()
                .my_1()
                .text_size(px(11.0)),
        )
        .on_mouse_down(
            MouseButton::Left,
            cx.listener(move |this, _ev: &MouseDownEvent, _w, cx| {
                match which {
                    PrefToggle::Balances => {
                        this.layout.prefs.show_balances = !this.layout.prefs.show_balances
                    }
                    PrefToggle::WordGran => {
                        this.layout.prefs.word_granularity = !this.layout.prefs.word_granularity
                    }
                }
                this.layout.save(&this.layout_path);
                cx.notify();
            }),
        )
        .child(format!("[{}] {label}", if on { "✓" } else { " " }))
    }

    fn pref_rows_button(&self, rows: u32, cx: &mut Context<Self>) -> impl IntoElement {
        bevel_raised(
            div()
                .id(gpui::SharedString::from(format!("rows-{rows}")))
                .px_2()
                .py_1()
                .text_size(px(11.0)),
        )
        .on_mouse_down(
            MouseButton::Left,
            cx.listener(move |this, _ev: &MouseDownEvent, _w, cx| {
                this.layout.prefs.grid_rows = rows;
                this.layout.save(&this.layout_path);
                cx.notify();
            }),
        )
        .child(format!("{rows} rows"))
    }

    fn render_statusbar(&self) -> impl IntoElement {
        let h = self.world.borrow().height();
        div()
            .absolute()
            .left(px(0.0))
            .bottom(px(0.0))
            .w_full()
            .h(px(22.0))
            .flex()
            .flex_row()
            .items_center()
            .px_2()
            .bg(gpui::rgb(NT_FACE))
            .border_t_2()
            .border_color(gpui::rgb(NT_HILIGHT))
            .text_size(px(11.0))
            .text_color(gpui::rgb(NT_TEXT))
            .child(div().flex_1().child(self.status.clone()))
            // A right-aligned height "tray" readout (the NT clock corner).
            .child(
                div()
                    .px_2()
                    .border_l_1()
                    .border_color(gpui::rgb(NT_FACE_DARK))
                    .text_color(gpui::rgb(0x303030))
                    .child(format!("World height {h}")),
            )
    }

    /// **The taskbar** — a row of stubs for every open window, just above the status
    /// bar (the NT taskbar). Each stub names the window and click-focuses it; a
    /// minimized window's stub reads dimmed. Pure view-state over `self.windows`.
    fn render_taskbar(&self, cx: &mut Context<Self>) -> impl IntoElement {
        let mut keys: Vec<WinKey> = self.windows.keys().copied().collect();
        keys.sort_by_key(|k| (self.windows[k].minimized, self.windows[k].z));
        let mut bar = div()
            .absolute()
            .left(px(0.0))
            .bottom(px(22.0))
            .w_full()
            .h(px(24.0))
            .flex()
            .flex_row()
            .items_center()
            .gap_1()
            .px_1()
            .bg(gpui::rgb(NT_FACE))
            .border_t_1()
            .border_color(gpui::rgb(NT_FACE_DARK));
        // A leading "Windows" caption (the taskbar's system corner).
        bar = bar.child(
            div()
                .px_2()
                .h(px(20.0))
                .flex()
                .items_center()
                .bg(gpui::rgb(NT_FACE_DARK))
                .text_size(px(10.0))
                .font_weight(FontWeight::BOLD)
                .child(format!("{} open", keys.len())),
        );
        for key in keys {
            let (cell, tag) = key;
            let ws = &self.windows[&key];
            let min = ws.minimized;
            // Font-safe label: the cell id + the 3-letter kind tag (no tofu glyph).
            let label = format!("{} · {}", id_short(&cell), kind_short(tag));
            bar = bar.child(
                bevel_raised(
                    div()
                        .id(gpui::SharedString::from(format!(
                            "task-{}-{:?}",
                            id_hex(&cell),
                            tag as u8
                        )))
                        .h(px(20.0))
                        .px_2()
                        .flex()
                        .items_center()
                        .text_size(px(10.0)),
                )
                .when(min, |d| d.opacity(0.55))
                .hover(|s| s.bg(gpui::rgb(NT_FACE_DARK)))
                .on_mouse_down(
                    MouseButton::Left,
                    cx.listener(move |this, _ev: &MouseDownEvent, _w, cx| {
                        this.focus_window(key);
                        cx.notify();
                    }),
                )
                .child(label),
            );
        }
        bar
    }

    /// **The World-summary widget** — a small NT info panel pinned to the desktop's
    /// top-right, reflecting the live World invariants: height, cell count, total
    /// receipts, and the conservation sum (Σ balance, the net of issuer wells vs.
    /// accounts). Read-only over the live ledger; it fills the empty right margin and
    /// teaches the invariant at a glance. The sum is INVARIANT under value-conserving
    /// turns (transfers move value, they do not create it), so the widget's headline
    /// is its stability, shown as the constant net.
    fn render_world_widget(&self) -> impl IntoElement {
        let (h, n, receipts) = {
            let w = self.world.borrow();
            (w.height(), self.cells.len(), w.receipts().len())
        };
        let sum = self.world_balance_sum();
        div()
            .absolute()
            .right(px(16.0))
            .top(px(MENUBAR_H + 12.0))
            .w(px(216.0))
            .bg(gpui::rgb(NT_FACE))
            .border_2()
            .border_color(gpui::rgb(NT_SHADOW))
            .flex()
            .flex_col()
            .child(
                div()
                    .h(px(20.0))
                    .flex()
                    .items_center()
                    .px_2()
                    .bg(gpui::rgb(NT_TITLE_ACTIVE))
                    .text_color(gpui::rgb(NT_TITLE_TEXT))
                    .text_size(px(11.0))
                    .font_weight(FontWeight::BOLD)
                    .child("World"),
            )
            .child(
                div()
                    .p_2()
                    .flex()
                    .flex_col()
                    .gap_1()
                    .child(face_row("height", &h.to_string()))
                    .child(face_row("cells", &n.to_string()))
                    .child(face_row("receipts", &receipts.to_string()))
                    .child(face_row_color("Σ balance", &fmt_balance(sum), 0x0a4a7a))
                    .child(
                        div()
                            .mt_1()
                            .text_size(px(10.0))
                            .text_color(gpui::rgb(NT_DIM))
                            .child("net of wells vs accounts — invariant under transfers"),
                    ),
            )
    }
}

/// A 3-letter window-kind tag for the taskbar stub (dense, fixed-width).
fn kind_short(tag: WinKindTag) -> &'static str {
    match tag {
        WinKindTag::Inspector => "INS",
        WinKindTag::DocEditor => "DOC",
        WinKindTag::Links => "LNK",
        WinKindTag::Transcript => "LOG",
        WinKindTag::Workflow => "WFL",
        WinKindTag::AndroidCell => "AND",
    }
}

#[derive(Clone, Copy)]
enum TitleBtn {
    Minimize,
    Maximize,
    Close,
}

/// Which boolean preference a desktop-Preferences toggle flips.
#[derive(Clone, Copy)]
enum PrefToggle {
    Balances,
    WordGran,
}

// (Small render helpers — `face_section` / `face_row` / `fmt_balance` / `group` —
// live in `chrome.rs` and are imported at the top of this module.)
