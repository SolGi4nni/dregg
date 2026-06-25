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
    AnyElement, ClickEvent, Context, Div, FontWeight, InteractiveElement, IntoElement, MouseButton,
    MouseDownEvent, MouseMoveEvent, MouseUpEvent, ParentElement, Pixels, Point, Render, Stateful,
    StatefulInteractiveElement, Styled, Window, div, px,
};

use dregg_cell::lifecycle::CellLifecycle;
use dregg_types::CellId;

use dregg_doc::{Author, Doc, Granularity};

use crate::world::{World, grant_capability, transfer};

// The chrome kit + persistence types are re-exported so existing call sites
// (`deos_desktop::id_hex`, `deos_desktop::DesktopLayout`, …) keep working.
pub use android_window::{ANDROID_WINDOW_TITLE, AndroidInputCmd, AndroidWindow};
pub use chrome::{
    DOC_CHUNK_BYTES, DOC_MAX_CHUNKS, DOC_REV_SLOT, DOC_TEXT_BASE, ICON_H, ICON_W, MENUBAR_H,
    NT_DESKTOP_BG, NT_DIM, NT_FACE, NT_FACE_DARK, NT_HILIGHT, NT_ICON_LABEL, NT_MENU_HILIGHT,
    NT_SELECT, NT_SHADOW, NT_TEXT, NT_TITLE_ACTIVE, NT_TITLE_TEXT, WIN_MIN_H, WIN_MIN_W,
    bevel_raised, face_row, face_section, fmt_balance, id_hex, id_short, pxf,
};
pub use layout::{DesktopLayout, DesktopPrefs, DocText, IconPos, WinGeom, WinKindTag};

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
        vec![
            MenuAction::new("World Transcript (receipt log)…", true, A::OpenTranscript),
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
            "Window" => vec![
                MenuAction::new("New Inspector…", true, A::Inspect),
                MenuAction::new("New Document…", true, A::OpenDoc),
                MenuAction::new("New Transcript…", true, A::OpenTranscript),
                MenuAction::new("New Workflow Composer…", true, A::OpenWorkflow),
            ],
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
}

// ── Rendering ─────────────────────────────────────────────────────────────────────
// (The `bevel_raised` / `face_section` / `face_row` chrome primitives live in
// `chrome.rs` and are imported above.)

impl Render for DeosDesktop {
    fn render(&mut self, _window: &mut Window, cx: &mut Context<Self>) -> impl IntoElement {
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

        // ── The open windows (z-ordered) ─────────────────────────────────────────
        let mut wins: Vec<WinKey> = self.windows.keys().copied().collect();
        wins.sort_by_key(|k| self.windows[k].z);
        for key in wins {
            root = root.child(self.render_window(key, cx));
        }

        // ── The context menu overlay (the ACTUATION) ─────────────────────────────
        if self.open_menu.is_some() {
            root = root.child(self.render_context_menu(cx));
        }

        // ── The property dialog overlay (the PROPERTY inspector/editor) ───────────
        if self.open_prop.is_some() {
            root = root.child(self.render_property_dialog(cx));
        }

        // ── The status bar (the receipt of the last actuation) ───────────────────
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
                .child(div().font_weight(FontWeight::BOLD).child("◆ deos")),
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
        let glyph = match kind {
            "treasury" => "▣",
            "issuer well" => "◈",
            "service" => "⚙",
            _ => "▤",
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

    fn render_window(&self, key: WinKey, cx: &mut Context<Self>) -> AnyElement {
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
            WinKindTag::DocEditor => self.render_doc_body(cell, cx),
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
            .child("◢");

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
        div()
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
            .child(face_section("State (live)"))
            .child(face_row("balance", &fmt_balance(bal)))
            .child(face_row("nonce", &nonce.to_string()))
            .child(face_row("lifecycle", &lifecycle))
            .child(face_row("capabilities", &caps.to_string()))
            .child(face_row("doc revision", &rev.to_string()))
            .child(face_section("Affordances (do it)"))
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
    fn render_doc_body(&self, cell: CellId, cx: &mut Context<Self>) -> AnyElement {
        let (text, patches) = match self
            .windows
            .get(&(cell, WinKindTag::DocEditor))
            .map(|w| &w.kind)
        {
            Some(WinKind::DocEditor { buffer, doc }) => (buffer.clone(), doc.history().len()),
            _ => (self.load_doc_text(&cell), 0),
        };
        let rev = self.cell_field_u64(&cell, DOC_REV_SLOT);
        let shown = if text.is_empty() {
            "(empty — type below, or drag a cell-icon here to transclude it)".to_string()
        } else {
            text.clone()
        };
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
            .child(face_section("Document (receipted patches)"))
            .child(
                // The prose surface — a parchment field showing the live folded text.
                div()
                    .id(gpui::SharedString::from(format!(
                        "docprose-{}",
                        id_hex(&cell)
                    )))
                    .flex_1()
                    .min_h(px(90.0))
                    .p_2()
                    .bg(gpui::rgb(0xffffff))
                    .border_1()
                    .border_color(gpui::rgb(NT_FACE_DARK))
                    .text_size(px(12.0))
                    .child(shown),
            )
            .child(face_section("Chronicle"))
            .child(face_row("patches", &patches.to_string()))
            .child(face_row("cell revision", &rev.to_string()))
            .child(face_row("author", &format!("{}", self.author.0 & 0xffff)))
            .child(face_section("Edit (each lands a receipt)"))
            // A couple of canned edits drive the receipted-patch path live.
            .child(self.doc_edit_button(cell, "Append a line ¶", "\nA new authored line.\n", cx))
            .child(self.doc_edit_button(cell, "Append a heading #", "\n# Section\n", cx))
            .into_any_element()
    }

    /// A document-edit button: appends `append` to the buffer as a receipted patch +
    /// verified revision turn.
    fn doc_edit_button(
        &self,
        cell: CellId,
        label: &str,
        append: &str,
        cx: &mut Context<Self>,
    ) -> impl IntoElement {
        let append = append.to_string();
        bevel_raised(
            div()
                .id(gpui::SharedString::from(format!(
                    "docedit-{}-{label}",
                    id_hex(&cell)
                )))
                .px_2()
                .py_1()
                .my_1()
                .text_size(px(11.0)),
        )
        .on_mouse_down(
            MouseButton::Left,
            cx.listener(move |this, _ev: &MouseDownEvent, _w, cx| {
                let cur = this.load_doc_buffer(cell);
                this.edit_doc(cell, format!("{cur}{append}"));
                cx.notify();
            }),
        )
        .child(label.to_string())
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
        // Transclusions composed into this cell's document (parsed from the prose).
        let doc = self.load_doc_buffer(cell);
        let incoming: Vec<&str> = doc
            .lines()
            .filter(|l| l.contains("{transclude dregg://"))
            .collect();
        col = col.child(face_section("Composed-in (transclusions)"));
        if incoming.is_empty() {
            col = col.child(face_row(
                "transclusions",
                "(none — drag a cell onto its doc)",
            ));
        } else {
            for (i, l) in incoming.iter().enumerate() {
                col = col.child(face_row(&format!("[{i}]"), l.trim()));
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
        let glyph = match tag {
            WinKindTag::DocEditor => "▤",
            WinKindTag::Links => "↹",
            WinKindTag::Transcript => "≣",
            WinKindTag::Inspector => "▣",
            WinKindTag::Workflow => "⛓",
            _ => "▣",
        };
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
            .child(div().px_1().child(glyph))
            .child(
                div()
                    .flex_1()
                    .px_1()
                    .text_size(px(11.0))
                    .font_weight(FontWeight::BOLD)
                    .child(title.to_string()),
            )
            .child(self.title_btn(key, "_", TitleBtn::Minimize, cx))
            .child(self.title_btn(
                key,
                if minimized { "▢" } else { "❐" },
                TitleBtn::Maximize,
                cx,
            ))
            .child(self.title_btn(key, "✕", TitleBtn::Close, cx))
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
                    .child(div().px_1().child("⚙"))
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
                            .child("✕"),
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
            .child(self.prop_setfield_button(cell, "revision ＋1", DOC_REV_SLOT, rev + 1, cx))
            .child(self.prop_setfield_button(cell, "revision ＝0", DOC_REV_SLOT, 0, cx))
            .child(self.prop_setfield_button(cell, "field[13] ＝42", 13, 42, cx))
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
        div()
            .absolute()
            .left(px(0.0))
            .bottom(px(0.0))
            .w_full()
            .h(px(22.0))
            .flex()
            .items_center()
            .px_2()
            .bg(gpui::rgb(NT_FACE))
            .border_t_2()
            .border_color(gpui::rgb(NT_HILIGHT))
            .text_size(px(11.0))
            .text_color(gpui::rgb(NT_TEXT))
            .child(self.status.clone())
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
