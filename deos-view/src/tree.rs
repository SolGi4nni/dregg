//! The **view-tree model** — the Rust shape of the deos-js `deos.ui.*` element-tree.
//!
//! `deos-js` builds a *serializable* element-tree (data, NOT gpui) in real
//! SpiderMonkey: `deos.ui.{vstack,row,text,bind,button,input,list,table}`. A button's
//! `onClick` is `{turn, arg}`; a `bind(()=>expr)` is a fine-grained signal binding.
//! That JS object is `JSON.stringify`-ed by the engine and read back into Rust (see
//! [`crate::bridge`]); this module is the Rust mirror it parses into. The renderer
//! ([`crate::render`]) walks this tree into real gpui-component widgets.
//!
//! NOTE on `bind`: `JSON.stringify` drops the closure (`node.read` is a function), so
//! a serialized `bind` node carries only `kind:"bind"`. The renderer re-reads the
//! bound value off the live applet ledger directly (the binding IS `app.get(slot)`),
//! which is the same witnessed read the JS closure made — see [`ViewNode::Bind`].

use serde::Deserialize;

/// A node of the view-tree, mirroring the JS `deos.ui.*` shape exactly.
///
/// The JS shape is `{ kind, props, children? , read? }`. We deserialize via the raw
/// [`RawNode`] (a faithful JSON mirror) and lift it into this typed enum so the
/// renderer matches on real variants.
#[derive(Debug, Clone)]
pub enum ViewNode {
    /// `vstack(...children)` → a vertical column (`v_flex`).
    VStack(Vec<ViewNode>),
    /// `row(...children)` → a horizontal row (`h_flex`).
    Row(Vec<ViewNode>),
    /// `text(s)` → a `Label`.
    Text(String),
    /// `bind(() => expr)` → a signal binding. The closure does not survive
    /// serialization; the renderer re-reads the bound value off the live ledger
    /// (the model slot the JS closure read). `slot` is the model slot to re-read
    /// (the counter shape binds slot 0); `label` is an optional prefix.
    Bind { slot: usize, label: String },
    /// `button(label, aff, arg)` → a `Button` whose onClick fires affordance `turn`
    /// with `arg` (a REAL cap-gated verified turn through the applet).
    Button {
        label: String,
        turn: String,
        arg: i64,
    },
    /// `input(viewKey)` → a text input bound to ephemeral view-state `bind_view`.
    ///
    /// EXTENDED (the richness expansion): the draft can feed a turn arg. When `fire_turn`
    /// is non-empty the field's committed draft is parsed into the `arg` of `fire_turn` on
    /// submit (Enter / a paired submit button); `submit_label` labels that button. An empty
    /// `fire_turn` keeps the legacy ephemeral-draft-only behaviour. Unlocks the
    /// `ServiceExplorer` arg rows, the `WebShell` URL bar, the predicate composer (input →
    /// verified turn).
    Input {
        bind_view: String,
        /// The affordance the submitted draft fires (its `arg` is the parsed draft). Empty →
        /// a plain ephemeral draft field (no turn).
        fire_turn: String,
        /// The submit button's label (when `fire_turn` is set). Empty → a sensible default.
        submit_label: String,
    },
    /// `list(items)` → a vertical list of child nodes.
    List(Vec<ViewNode>),
    /// `table(rows)` → a table; each row is itself a node (a `row` of cells).
    Table(Vec<ViewNode>),

    // ── The RICHNESS EXPANSION (docs/deos/DEOS-VIEW-RICHNESS-EXPANSION.md) — growing the
    //    vocabulary toward native-cockpit parity so liberating a surface into a card is
    //    LOSSLESS. Batch 1: a container, an actuation+selection node, a bound visual, a leaf.
    /// `section(title, ...children)` → a titled, bordered container (the uniform "styled
    /// section"). `tag` selects a styling accent (the existing `props.tag` convention —
    /// `genuine`/`refusal`/…). Unlocks Organs, the Trust/Devtools blocks, every panel's
    /// `section_title` + bordered-box idiom.
    Section {
        title: String,
        tag: String,
        children: Vec<ViewNode>,
    },
    /// `tabs({tabs, selectedSlot, selectTurn}, ...panels)` → a tab-strip whose visible panel
    /// is bound to model slot `selected_slot`. A tab click fires `select_turn` with `arg =
    /// the tab index` (a REAL verified turn that writes the slot). Unlocks Lanes, Devtools,
    /// Moldable. The renderer walks ALL panels (keeping the bind cursor aligned) and displays
    /// only the selected one.
    Tabs {
        /// The tab labels, one per panel (in `panels` order).
        tabs: Vec<String>,
        /// The model slot holding the active tab index (read live each paint).
        selected_slot: usize,
        /// The affordance a tab click fires (`arg` is the clicked tab's index).
        select_turn: String,
        /// The tab bodies — one per label; only the selected one is displayed.
        panels: Vec<ViewNode>,
    },
    /// `gauge({slot, max, label})` → a bound progress / balance bar. The fill is
    /// `get_u64(slot) / max`, clamped to `[0,1]`. Reads its slot IMMEDIATE-MODE (it does not
    /// consume the tree-walk bind cursor — it is not a `Bind`). Unlocks `face_gauge`, the
    /// Time liveness bar, any "glow = activity" indicator.
    Gauge {
        slot: usize,
        max: u64,
        label: String,
    },
    /// `divider()` → a thin full-width horizontal rule (a groove / separator). A pure leaf.
    Divider,

    // ── The COMPOSITION KEYSTONE (docs/deos/CELL-HOSTED-VIEWTREE.md) — a cell is a
    //    first-class hostable COMPONENT whose committed heap stores its own evolving
    //    view-tree; `host` MOUNTS that whole tree here as a subtree. This is distinct from
    //    `bind` (reads ONE scalar value off `(cell, slot)`) and from value-transclusion (a
    //    value snapshot from another cell): `host` mounts an ENTIRE view-tree sourced from the
    //    hosted cell's committed heap. Hosted trees contain `host` nodes for OTHER cells →
    //    fractal recursion (cells-host-cells-host-view-trees, to arbitrary depth). ──
    /// `host(cellId)` → mount the hosted cell's WHOLE view-tree here, as a subtree.
    ///
    /// `cell` is the hosted cell's id (hex). `view` is the RESOLVED hosted view-tree:
    /// - `None` — an UNRESOLVED mount (a bare reference). The renderer paints an honest
    ///   `‹mount cell …: unresolved›` placeholder until [`resolve_mounts`] fills it from the
    ///   cell's committed heap (the cell-heap-as-view-source — see [`crate::mount`]).
    /// - `Some(tree)` — the resolved/provided subtree, mounted whole. A resolver emits this;
    ///   an author may also carry a pre-baked subtree inline (the first-cut provided source).
    ///
    /// `host` stays PURE DATA (a cell-id string + an optional resolved subtree, NO live
    /// `Applet`/`Ledger` handle) so the gpui-free + deos-js-free `web`/`discord` renderers
    /// walk the IDENTICAL resolved tree — the heap read happens OUTSIDE the IR, at the
    /// boundary, and the result is spliced back in. The hosted subtree participates in the
    /// SAME pre-order bind cursor (every renderer recurses `view` at the host's position).
    Host {
        cell: String,
        view: Option<Box<ViewNode>>,
    },

    // ── The RICHNESS EXPANSION batch 2 — the actuation crown + the rest of the §1 vocabulary
    //    (docs/deos/DEOS-VIEW-RICHNESS-EXPANSION.md). Each node carries its affordance(s) in the
    //    `{turn, arg}` shape so the cap-gated-verified-turn routing is reused unchanged; bound
    //    nodes name their `slot` and read it immediate-mode (no bind cursor). ──────────────────
    /// `grid({cols}, ...children)` → a wrapping spatial cell field. `cols` caps how many cells
    /// sit per row (0 → free wrap). Unlocks Wonder's glowing-cell grid, the desktop icon field,
    /// the Powerbox app tiles. Recurses children in declaration order (the bind cursor stays
    /// aligned).
    Grid {
        cols: usize,
        children: Vec<ViewNode>,
    },
    /// `breadcrumb({items})` → a navigation path joined by `→`. A crumb carrying a non-empty
    /// `turn` is clickable (fires a verified turn). Unlocks Time's metastack breadcrumb, the
    /// Docs transclusion path.
    Breadcrumb { items: Vec<Crumb> },
    /// `progress({value, max, label})` → a STATIC (literal-valued) progress bar — the non-bound
    /// gauge. Unlocks a swarm-member completion bar, a download tile.
    Progress { value: u64, max: u64, label: String },
    /// `pill({text, tag})` → a colored status badge (leaf). `tag` selects the semantic palette
    /// (`good`/`warn`/`bad`/`accent`/`muted`). Unlocks the cockpit's ubiquitous `pill(text,
    /// color)` — authority badges, LIVE/REVOKED chips, kind/lifecycle badges.
    Pill { text: String, tag: String },
    /// `icon({glyph, tag})` → a glyph indicator (leaf), tinted by `tag`. Unlocks the Wonder ✦/○
    /// glow glyphs, the scrubber markers, the toggle ✓/○.
    Icon { glyph: String, tag: String },
    /// `menu({items})` → a right-click / context actuation menu — a list of `{label, turn, arg,
    /// enabled}` rows. A `!enabled` row is the cap tooth shown rather than hidden (a dimmed,
    /// non-firing row). Unlocks the `deos_desktop` right-click actuation list.
    Menu { items: Vec<MenuItem> },
    /// `halo({targetSlot, handles})` → the Pharo direct-manipulation handle-ring: a node carrying
    /// its handles, each a `{glyph, turn, arg, enabled}` affordance the renderer rings around the
    /// target (the compass-anchor geometry is renderer-side layout, not card data). A `!enabled`
    /// handle is cap-refused, shown dimmed. Unlocks `deos_desktop/halo.rs`.
    Halo {
        /// The slot whose object the ring floats on (informational; the geometry is the
        /// renderer's). 0 if unbound.
        target_slot: usize,
        handles: Vec<HaloHandle>,
    },
    /// `slider({slot, min, max, turn})` → a bound draggable value → seek turn. The thumb sits at
    /// `get_u64(slot)` (read immediate-mode); a drag fires `turn` with `arg = the chosen value`.
    /// Unlocks Time's rewind scrubber, Replay.
    Slider {
        slot: usize,
        min: u64,
        max: u64,
        turn: String,
    },
    /// `toggle({slot, onTurn, offTurn, glyphOn, glyphOff, label})` → an affordance checkbox. The
    /// glyph is `glyph_on` when `get_u64(slot) != 0` else `glyph_off`; a click fires `on_turn`
    /// when currently off, `off_turn` when currently on. Unlocks Share's cull toggles, any
    /// boolean affordance.
    Toggle {
        slot: usize,
        on_turn: String,
        off_turn: String,
        glyph_on: String,
        glyph_off: String,
        label: String,
    },
    /// `tile({handle, w, h})` → a card-referenced native paint region (the genuine ceiling). The
    /// card does NOT carry the pixels; it references an opaque host-resolved region (a Servo
    /// render, a video, a map). An unresolvable handle paints a labelled placeholder. Unlocks
    /// `WebShell`'s Servo render tile, any embedded native surface.
    Tile { handle: String, w: u32, h: u32 },
}

/// A `breadcrumb` crumb — a path segment, optionally clickable (a non-empty `turn` fires a
/// verified turn carrying `arg`).
#[derive(Debug, Clone)]
pub struct Crumb {
    pub label: String,
    pub turn: String,
    pub arg: i64,
}

/// A `menu` row — a `{label, turn, arg}` actuation with a cap-tooth `enabled` flag (a disabled
/// row is shown dimmed, never hidden — the in-band refusal).
#[derive(Debug, Clone)]
pub struct MenuItem {
    pub label: String,
    pub turn: String,
    pub arg: i64,
    pub enabled: bool,
}

/// A `halo` handle — a `{glyph, turn, arg}` affordance the renderer rings around the target,
/// with a cap-tooth `enabled` flag (a disabled handle is shown dimmed).
#[derive(Debug, Clone)]
pub struct HaloHandle {
    pub glyph: String,
    pub turn: String,
    pub arg: i64,
    pub enabled: bool,
}

/// The raw JSON mirror of a `deos.ui.*` node (`{ kind, props, children }`). The
/// engine's `JSON.stringify(tree)` produces exactly this; we then [`RawNode::lift`]
/// it into the typed [`ViewNode`].
#[derive(Debug, Clone, Deserialize)]
pub struct RawNode {
    pub kind: String,
    #[serde(default)]
    pub props: RawProps,
    #[serde(default)]
    pub children: Vec<RawNode>,
}

/// The raw `props` bag — every field optional (a node uses only the ones for its kind).
#[derive(Debug, Clone, Default, Deserialize)]
pub struct RawProps {
    #[serde(default)]
    pub text: Option<String>,
    #[serde(default)]
    pub label: Option<String>,
    // The JS prelude (`deos.ui.button`) emits the camelCase key `onClick`; deserialize it
    // by that name (with the snake_case alias kept) so the affordance `{turn, arg}` the
    // engine produced survives the parse into BOTH renderers — the native `Button`'s
    // on_click AND the web `<button data-turn data-arg>`. Without the rename the engine's
    // `onClick` silently dropped to a `{turn:"", arg:0}` default.
    #[serde(default, rename = "onClick", alias = "on_click")]
    pub on_click: Option<RawOnClick>,
    #[serde(default, rename = "bindView", alias = "bind_view")]
    pub bind_view: Option<String>,
    /// For a `bind` node the renderer needs to know WHICH model slot to re-read.
    /// The JS closure isn't serializable, so the applet author tags the bind node's
    /// props with `slot` (the counter shape uses slot 0). Absent → slot 0. Also the
    /// model slot a `gauge` reads its fill ratio from.
    #[serde(default)]
    pub slot: Option<usize>,

    // ── The richness-expansion props (batch 1: section / tabs / gauge). Every field
    //    optional; a node reads only the ones for its kind (the raw `props` bag idiom). ──
    /// A `section`'s header title.
    #[serde(default)]
    pub title: Option<String>,
    /// A styling accent / disclosure tag (`section`, `pill`, …): the existing `props.tag`
    /// convention (`genuine`/`refusal`/…), reused by the disclosure filter.
    #[serde(default)]
    pub tag: Option<String>,
    /// A `gauge`'s denominator (the fill is `slot_value / max`, clamped to `[0,1]`).
    #[serde(default)]
    pub max: Option<u64>,
    /// A `tabs` node's tab labels, one per panel (camelCase `tabs`, snake alias).
    #[serde(default, alias = "tab_labels")]
    pub tabs: Option<Vec<String>>,
    /// A `tabs` node's model slot holding the active tab index (camelCase `selectedSlot`).
    #[serde(default, rename = "selectedSlot", alias = "selected_slot")]
    pub selected_slot: Option<usize>,
    /// A `tabs` node's select affordance (`arg` is the clicked tab index; camelCase).
    #[serde(default, rename = "selectTurn", alias = "select_turn")]
    pub select_turn: Option<String>,
    /// A `host` node's hosted cell id (hex) — the mount reference. The hosted cell's WHOLE
    /// view-tree is read from its committed heap and mounted here (see [`ViewNode::Host`]).
    #[serde(default, alias = "cellId")]
    pub cell: Option<String>,

    // ── batch-2 props (the actuation crown + the rest of §1). Every field optional; a node
    //    reads only the ones for its kind. ────────────────────────────────────────────────
    /// A `grid`'s column cap (cells per row; 0 → free wrap).
    #[serde(default)]
    pub cols: Option<usize>,
    /// A `menu`/`breadcrumb`'s rows (the `{label, turn, arg, enabled}` list).
    #[serde(default)]
    pub items: Option<Vec<RawItem>>,
    /// A `halo`'s handles (the `{glyph, turn, arg, enabled}` ring).
    #[serde(default)]
    pub handles: Option<Vec<RawItem>>,
    /// A `halo`'s target slot (the object the ring floats on; camelCase `targetSlot`).
    #[serde(default, rename = "targetSlot", alias = "target_slot")]
    pub target_slot: Option<usize>,
    /// A `progress`'s literal value (the non-bound gauge's fill numerator).
    #[serde(default)]
    pub value: Option<u64>,
    /// A `slider`'s minimum (the low end of the draggable range).
    #[serde(default)]
    pub min: Option<u64>,
    /// A single affordance `turn` (a `slider` seek; the `arg` is the chosen value).
    #[serde(default)]
    pub turn: Option<String>,
    /// A `toggle`'s on/off affordances (camelCase `onTurn`/`offTurn`).
    #[serde(default, rename = "onTurn", alias = "on_turn")]
    pub on_turn: Option<String>,
    #[serde(default, rename = "offTurn", alias = "off_turn")]
    pub off_turn: Option<String>,
    /// An `icon`'s glyph; a `toggle`'s on/off glyphs (camelCase `glyphOn`/`glyphOff`).
    #[serde(default)]
    pub glyph: Option<String>,
    #[serde(default, rename = "glyphOn", alias = "glyph_on")]
    pub glyph_on: Option<String>,
    #[serde(default, rename = "glyphOff", alias = "glyph_off")]
    pub glyph_off: Option<String>,
    /// An extended `input`'s submit affordance + button label (camelCase `fireTurn`/`submitLabel`).
    #[serde(default, rename = "fireTurn", alias = "fire_turn")]
    pub fire_turn: Option<String>,
    #[serde(default, rename = "submitLabel", alias = "submit_label")]
    pub submit_label: Option<String>,
    /// A `tile`'s host-side render-source handle + its pixel size.
    #[serde(default)]
    pub handle: Option<String>,
    #[serde(default)]
    pub w: Option<u32>,
    #[serde(default)]
    pub h: Option<u32>,
}

/// A raw `{label?, glyph?, turn?, arg?, enabled?}` row — the JSON mirror of a `menu` item, a
/// `halo` handle, or a `breadcrumb` crumb (each node lifts only the fields it needs). `enabled`
/// defaults to `true` (a row is fireable unless the author/cap explicitly dims it).
#[derive(Debug, Clone, Deserialize)]
pub struct RawItem {
    #[serde(default)]
    pub label: String,
    #[serde(default)]
    pub glyph: String,
    #[serde(default)]
    pub turn: String,
    #[serde(default)]
    pub arg: i64,
    #[serde(default = "raw_item_enabled_default")]
    pub enabled: bool,
}

/// A `RawItem`'s `enabled` defaults to `true` (a row fires unless explicitly dimmed by the cap).
fn raw_item_enabled_default() -> bool {
    true
}

/// `onClick = { turn, arg }` — the affordance a button fires.
#[derive(Debug, Clone, Deserialize)]
pub struct RawOnClick {
    pub turn: String,
    #[serde(default)]
    pub arg: i64,
}

impl RawNode {
    /// Lift a raw JSON node into the typed [`ViewNode`]. An unknown kind renders as a
    /// labelled placeholder text (honest: the renderer shows what it could not map).
    pub fn lift(&self) -> ViewNode {
        let kids = || self.children.iter().map(|c| c.lift()).collect::<Vec<_>>();
        match self.kind.as_str() {
            "vstack" => ViewNode::VStack(kids()),
            "row" => ViewNode::Row(kids()),
            "text" => ViewNode::Text(self.props.text.clone().unwrap_or_default()),
            "bind" => ViewNode::Bind {
                slot: self.props.slot.unwrap_or(0),
                label: self.props.label.clone().unwrap_or_default(),
            },
            "button" => {
                let oc = self.props.on_click.clone().unwrap_or(RawOnClick {
                    turn: String::new(),
                    arg: 0,
                });
                ViewNode::Button {
                    label: self.props.label.clone().unwrap_or_default(),
                    turn: oc.turn,
                    arg: oc.arg,
                }
            }
            "input" => ViewNode::Input {
                bind_view: self.props.bind_view.clone().unwrap_or_default(),
                fire_turn: self.props.fire_turn.clone().unwrap_or_default(),
                submit_label: self.props.submit_label.clone().unwrap_or_default(),
            },
            "list" => ViewNode::List(kids()),
            "table" => ViewNode::Table(kids()),
            "section" => ViewNode::Section {
                title: self.props.title.clone().unwrap_or_default(),
                tag: self.props.tag.clone().unwrap_or_default(),
                children: kids(),
            },
            "tabs" => ViewNode::Tabs {
                tabs: self.props.tabs.clone().unwrap_or_default(),
                selected_slot: self.props.selected_slot.unwrap_or(0),
                select_turn: self.props.select_turn.clone().unwrap_or_default(),
                panels: kids(),
            },
            "gauge" => ViewNode::Gauge {
                slot: self.props.slot.unwrap_or(0),
                max: self.props.max.unwrap_or(0),
                label: self.props.label.clone().unwrap_or_default(),
            },
            "divider" => ViewNode::Divider,
            "grid" => ViewNode::Grid {
                cols: self.props.cols.unwrap_or(0),
                children: kids(),
            },
            "breadcrumb" => ViewNode::Breadcrumb {
                items: self
                    .props
                    .items
                    .clone()
                    .unwrap_or_default()
                    .into_iter()
                    .map(|i| Crumb {
                        label: i.label,
                        turn: i.turn,
                        arg: i.arg,
                    })
                    .collect(),
            },
            "progress" => ViewNode::Progress {
                value: self.props.value.unwrap_or(0),
                max: self.props.max.unwrap_or(0),
                label: self.props.label.clone().unwrap_or_default(),
            },
            "pill" => ViewNode::Pill {
                text: self.props.text.clone().unwrap_or_default(),
                tag: self.props.tag.clone().unwrap_or_default(),
            },
            "icon" => ViewNode::Icon {
                glyph: self.props.glyph.clone().unwrap_or_default(),
                tag: self.props.tag.clone().unwrap_or_default(),
            },
            "menu" => ViewNode::Menu {
                items: self
                    .props
                    .items
                    .clone()
                    .unwrap_or_default()
                    .into_iter()
                    .map(|i| MenuItem {
                        label: i.label,
                        turn: i.turn,
                        arg: i.arg,
                        enabled: i.enabled,
                    })
                    .collect(),
            },
            "halo" => ViewNode::Halo {
                target_slot: self.props.target_slot.unwrap_or(0),
                handles: self
                    .props
                    .handles
                    .clone()
                    .unwrap_or_default()
                    .into_iter()
                    .map(|h| HaloHandle {
                        glyph: h.glyph,
                        turn: h.turn,
                        arg: h.arg,
                        enabled: h.enabled,
                    })
                    .collect(),
            },
            "slider" => ViewNode::Slider {
                slot: self.props.slot.unwrap_or(0),
                min: self.props.min.unwrap_or(0),
                max: self.props.max.unwrap_or(0),
                turn: self.props.turn.clone().unwrap_or_default(),
            },
            "toggle" => ViewNode::Toggle {
                slot: self.props.slot.unwrap_or(0),
                on_turn: self.props.on_turn.clone().unwrap_or_default(),
                off_turn: self.props.off_turn.clone().unwrap_or_default(),
                glyph_on: self.props.glyph_on.clone().unwrap_or_else(|| "✓".into()),
                glyph_off: self.props.glyph_off.clone().unwrap_or_else(|| "○".into()),
                label: self.props.label.clone().unwrap_or_default(),
            },
            "tile" => ViewNode::Tile {
                handle: self.props.handle.clone().unwrap_or_default(),
                w: self.props.w.unwrap_or(0),
                h: self.props.h.unwrap_or(0),
            },
            // `host(cellId)` — a child (if present) is the provided/pre-baked hosted subtree;
            // no child = an UNRESOLVED mount (filled later from the cell heap by
            // [`resolve_mounts`]). At most one hosted subtree (a host mounts ONE cell's tree).
            "host" => ViewNode::Host {
                cell: self.props.cell.clone().unwrap_or_default(),
                view: self.children.first().map(|c| Box::new(c.lift())),
            },
            other => ViewNode::Text(format!("‹unmapped node: {other}›")),
        }
    }
}

/// A source of cells' hosted view-trees — the cell-heap-as-view-source seen abstractly. A
/// [`resolve_mounts`] walk asks it for the hosted view-tree of each [`ViewNode::Host`]'s
/// cell. The native [`crate::mount`] impl reads the tree out of the cell's committed heap;
/// tests / provided sources use an in-memory [`MapMountSource`]. Any
/// `Fn(&str) -> Option<ViewNode>` is a `MountSource` (the blanket impl below).
pub trait MountSource {
    /// The hosted view-tree of `cell` (hex id), or `None` if the cell hosts no tree (the
    /// host then stays an unresolved placeholder — honest, never a crash).
    fn hosted_tree(&self, cell: &str) -> Option<ViewNode>;
}

impl<F: Fn(&str) -> Option<ViewNode>> MountSource for F {
    fn hosted_tree(&self, cell: &str) -> Option<ViewNode> {
        self(cell)
    }
}

/// An in-memory `cell-id → hosted view-tree` source (a provided source / the test source).
#[derive(Debug, Default, Clone)]
pub struct MapMountSource(pub std::collections::BTreeMap<String, ViewNode>);

impl MapMountSource {
    /// Insert a cell's hosted view-tree (builder-style).
    pub fn with(mut self, cell: impl Into<String>, tree: ViewNode) -> Self {
        self.0.insert(cell.into(), tree);
        self
    }
}

impl MountSource for MapMountSource {
    fn hosted_tree(&self, cell: &str) -> Option<ViewNode> {
        self.0.get(cell).cloned()
    }
}

/// The maximum mount DEPTH (`host` nesting) the resolver unfolds before fail-safing. Bounds
/// a huge-but-acyclic mount tree so it can never blow the stack (cycles are caught separately
/// by the visited-path check). 16 levels of cells-host-cells is far past any real surface.
pub const MAX_MOUNT_DEPTH: usize = 16;

/// **Resolve every `host` mount against a [`MountSource`]** — the cell-hosted-view-tree
/// composition keystone. Walks `tree`, and for each [`ViewNode::Host`] fills its `view` from
/// the source's hosted tree for that cell (recursing into it so nested `host`s — fractal
/// cells-host-cells — resolve too). Returns a fully-resolved tree every renderer walks
/// identically.
///
/// FAIL-SAFE BY CONSTRUCTION (the recursion contract):
/// - **cycle** — a `host{cell}` naming a cell already on the mount path (self-host, or an
///   a→b→a cycle) resolves to a `‹mount cycle: …›` body inside the host frame (the cell is
///   still shown; only the self-reference is cut). Never an infinite unfold.
/// - **depth** — at [`MAX_MOUNT_DEPTH`] the resolver stops with a `‹mount depth exceeded›`
///   body (a huge acyclic tree can't blow the stack).
/// - **source miss** — a cell the source can't supply stays `view: None` (the unresolved
///   placeholder). A `host` already carrying a `view` (provided/pre-baked) is recursed for
///   nested hosts but otherwise kept.
pub fn resolve_mounts(tree: &ViewNode, source: &dyn MountSource) -> ViewNode {
    let mut path: Vec<String> = Vec::new();
    resolve_rec(tree, source, &mut path, 0)
}

fn resolve_rec(
    node: &ViewNode,
    source: &dyn MountSource,
    path: &mut Vec<String>,
    depth: usize,
) -> ViewNode {
    let recur = |children: &[ViewNode], path: &mut Vec<String>| -> Vec<ViewNode> {
        children
            .iter()
            .map(|c| resolve_rec(c, source, path, depth))
            .collect()
    };
    match node {
        ViewNode::Host { cell, view } => {
            // Cycle: this cell is already being mounted on the current path.
            if path.iter().any(|c| c == cell) {
                return ViewNode::Host {
                    cell: cell.clone(),
                    view: Some(Box::new(ViewNode::Text(format!("‹mount cycle: {cell}›")))),
                };
            }
            // Depth: a huge (acyclic) mount chain fail-safes rather than blowing the stack.
            if depth >= MAX_MOUNT_DEPTH {
                return ViewNode::Host {
                    cell: cell.clone(),
                    view: Some(Box::new(ViewNode::Text("‹mount depth exceeded›".into()))),
                };
            }
            // The hosted subtree: the provided/pre-baked `view`, else the source's tree for
            // this cell. A miss leaves it unresolved (the honest placeholder).
            let hosted = match view {
                Some(v) => Some((**v).clone()),
                None => source.hosted_tree(cell),
            };
            let resolved = hosted.map(|h| {
                path.push(cell.clone());
                let r = resolve_rec(&h, source, path, depth + 1);
                path.pop();
                Box::new(r)
            });
            ViewNode::Host {
                cell: cell.clone(),
                view: resolved,
            }
        }
        ViewNode::VStack(cs) => ViewNode::VStack(recur(cs, path)),
        ViewNode::Row(cs) => ViewNode::Row(recur(cs, path)),
        ViewNode::List(cs) => ViewNode::List(recur(cs, path)),
        ViewNode::Table(cs) => ViewNode::Table(recur(cs, path)),
        ViewNode::Section {
            title,
            tag,
            children,
        } => ViewNode::Section {
            title: title.clone(),
            tag: tag.clone(),
            children: recur(children, path),
        },
        ViewNode::Tabs {
            tabs,
            selected_slot,
            select_turn,
            panels,
        } => ViewNode::Tabs {
            tabs: tabs.clone(),
            selected_slot: *selected_slot,
            select_turn: select_turn.clone(),
            panels: recur(panels, path),
        },
        // The `grid` container recurses its children (a child may host a cell), like the other
        // containers.
        ViewNode::Grid { cols, children } => ViewNode::Grid {
            cols: *cols,
            children: recur(children, path),
        },
        // Leaves carry no mounts — cloned through unchanged. (The actuation/indicator nodes hold
        // affordance/value DATA, not `ViewNode` children, so no mount can hide inside them.)
        ViewNode::Text(_)
        | ViewNode::Bind { .. }
        | ViewNode::Button { .. }
        | ViewNode::Input { .. }
        | ViewNode::Gauge { .. }
        | ViewNode::Divider
        | ViewNode::Breadcrumb { .. }
        | ViewNode::Progress { .. }
        | ViewNode::Pill { .. }
        | ViewNode::Icon { .. }
        | ViewNode::Menu { .. }
        | ViewNode::Halo { .. }
        | ViewNode::Slider { .. }
        | ViewNode::Toggle { .. }
        | ViewNode::Tile { .. } => node.clone(),
    }
}

/// Parse the engine's `JSON.stringify(viewTree)` string into a typed [`ViewNode`].
pub fn parse_view_tree(json: &str) -> Result<ViewNode, String> {
    let raw: RawNode = serde_json::from_str(json).map_err(|e| format!("view-tree JSON: {e}"))?;
    Ok(raw.lift())
}

#[cfg(test)]
mod mount_tests {
    use super::*;

    /// A `host(cell)` with no child lifts to an UNRESOLVED mount (`view: None`).
    #[test]
    fn host_lifts_unresolved_from_bare_reference() {
        let tree =
            parse_view_tree(r#"{ "kind":"host", "props":{ "cell":"abcd" } }"#).expect("parse host");
        match tree {
            ViewNode::Host { cell, view } => {
                assert_eq!(cell, "abcd", "the host carries the cell ref");
                assert!(view.is_none(), "a bare host reference is unresolved");
            }
            _ => panic!("root is a host node"),
        }
    }

    /// `resolve_mounts` fills a host's `view` from the source — and recurses, so a FRACTAL
    /// 2-level nest (parent hosts child, child hosts grandchild) resolves end-to-end.
    #[test]
    fn resolve_mounts_unfolds_a_fractal_two_level_nest() {
        let grandchild = ViewNode::Section {
            title: "G".into(),
            tag: String::new(),
            children: vec![ViewNode::Text("grandchild leaf".into())],
        };
        // The child hosts the grandchild (a host node inside the child's own tree).
        let child = ViewNode::Section {
            title: "C".into(),
            tag: String::new(),
            children: vec![
                ViewNode::Text("child body".into()),
                ViewNode::Host {
                    cell: "gc".into(),
                    view: None,
                },
            ],
        };
        let source = MapMountSource::default()
            .with("child", child)
            .with("gc", grandchild);
        let parent = ViewNode::VStack(vec![
            ViewNode::Text("parent".into()),
            ViewNode::Host {
                cell: "child".into(),
                view: None,
            },
        ]);

        let resolved = resolve_mounts(&parent, &source);
        // Walk down: parent → host(child) → child Section → host(gc) → grandchild Section.
        let ViewNode::VStack(top) = &resolved else {
            panic!("root vstack")
        };
        let ViewNode::Host {
            view: Some(child_v),
            ..
        } = &top[1]
        else {
            panic!("host(child) resolved")
        };
        let ViewNode::Section {
            children: child_kids,
            ..
        } = &**child_v
        else {
            panic!("child is a section")
        };
        let ViewNode::Host {
            view: Some(gc_v), ..
        } = &child_kids[1]
        else {
            panic!("host(gc) resolved INSIDE the child — the fractal nest")
        };
        let ViewNode::Section {
            title: gc_title, ..
        } = &**gc_v
        else {
            panic!("grandchild is a section")
        };
        assert_eq!(gc_title, "G", "the grandchild tree mounted two levels deep");
    }

    /// A cell hosting ITSELF is caught — the resolver fail-safes to a cycle placeholder
    /// rather than unfolding forever.
    #[test]
    fn resolve_mounts_breaks_a_self_cycle() {
        // `loop` hosts a tree that hosts `loop` again.
        let looping = ViewNode::Host {
            cell: "loop".into(),
            view: None,
        };
        let source = MapMountSource::default().with("loop", looping.clone());
        let resolved = resolve_mounts(&looping, &source);
        let ViewNode::Host { view: Some(v), .. } = &resolved else {
            panic!("the outer host resolved once")
        };
        // Its body is the inner host(loop), which is a CYCLE — its body is the placeholder.
        let ViewNode::Host {
            view: Some(inner), ..
        } = &**v
        else {
            panic!("inner host present")
        };
        match &**inner {
            ViewNode::Text(t) => assert!(t.contains("mount cycle"), "self-cycle is cut: {t}"),
            _ => panic!("the self-cycle resolves to the cycle placeholder"),
        }
    }

    /// A mutual a→b→a cycle is caught the same way (the visited PATH, not just self).
    #[test]
    fn resolve_mounts_breaks_a_mutual_cycle() {
        let a = ViewNode::Host {
            cell: "b".into(),
            view: None,
        };
        let b = ViewNode::Host {
            cell: "a".into(),
            view: None,
        };
        let source = MapMountSource::default().with("a", a).with("b", b);
        let root = ViewNode::Host {
            cell: "a".into(),
            view: None,
        };
        // Just terminating (no stack overflow / hang) + producing a tree is the property.
        let resolved = resolve_mounts(&root, &source);
        let rendered = format!("{resolved:?}");
        assert!(
            rendered.contains("mount cycle"),
            "the mutual cycle is cut with a placeholder"
        );
    }

    /// A pre-baked (provided) `view` is kept AND recursed for nested hosts.
    #[test]
    fn resolve_mounts_keeps_and_recurses_a_provided_subtree() {
        let provided = ViewNode::Host {
            cell: "outer".into(),
            view: Some(Box::new(ViewNode::Host {
                cell: "inner".into(),
                view: None,
            })),
        };
        let source =
            MapMountSource::default().with("inner", ViewNode::Text("inner resolved".into()));
        let resolved = resolve_mounts(&provided, &source);
        let ViewNode::Host { view: Some(v), .. } = &resolved else {
            panic!("outer kept its provided view")
        };
        let ViewNode::Host {
            view: Some(inner), ..
        } = &**v
        else {
            panic!("the nested host inside the provided subtree was visited")
        };
        assert!(
            matches!(&**inner, ViewNode::Text(t) if t == "inner resolved"),
            "the nested host inside a provided subtree resolved from the source"
        );
    }
}

#[cfg(test)]
mod batch2_lift_tests {
    //! The richness-expansion batch-2 nodes lift from their `{kind, props, children}` wire shape
    //! into the typed [`ViewNode`] (the serde round-trip on the new `RawProps` fields), and a
    //! `grid` recurses through [`resolve_mounts`] so a hosted cell nested in a grid still mounts.
    use super::*;

    #[test]
    fn the_actuation_and_indicator_nodes_lift_from_the_wire() {
        // menu — a list of {label, turn, arg, enabled} rows; `enabled` defaults to true.
        let menu = parse_view_tree(
            r#"{ "kind":"menu", "props":{ "items":[
                 { "label":"Open", "turn":"open", "arg":1 },
                 { "label":"Delete", "turn":"del", "arg":2, "enabled":false } ] } }"#,
        )
        .expect("parse menu");
        let ViewNode::Menu { items } = &menu else {
            panic!("root is a menu")
        };
        assert_eq!(items.len(), 2);
        assert_eq!(items[0].turn, "open");
        assert!(items[0].enabled, "absent enabled defaults true");
        assert!(!items[1].enabled, "an explicit enabled:false dims the row");

        // halo — a ring of {glyph, turn, arg} handles around a target slot.
        let halo = parse_view_tree(
            r#"{ "kind":"halo", "props":{ "targetSlot":3, "handles":[
                 { "glyph":"✕", "turn":"close", "arg":0 },
                 { "glyph":"⤢", "turn":"resize", "arg":0, "enabled":false } ] } }"#,
        )
        .expect("parse halo");
        let ViewNode::Halo {
            target_slot,
            handles,
        } = &halo
        else {
            panic!("root is a halo")
        };
        assert_eq!(*target_slot, 3);
        assert_eq!(handles.len(), 2);
        assert_eq!(handles[0].glyph, "✕");
        assert!(!handles[1].enabled);

        // slider — a bound draggable value firing `turn` with `arg = value`.
        let slider = parse_view_tree(
            r#"{ "kind":"slider", "props":{ "slot":2, "min":0, "max":99, "turn":"seek" } }"#,
        )
        .expect("parse slider");
        assert!(matches!(
            slider,
            ViewNode::Slider { slot: 2, min: 0, max: 99, ref turn } if turn == "seek"
        ));

        // toggle — defaults the glyphs to ✓/○ when absent.
        let toggle = parse_view_tree(
            r#"{ "kind":"toggle", "props":{ "slot":4, "onTurn":"on", "offTurn":"off", "label":"cull " } }"#,
        )
        .expect("parse toggle");
        let ViewNode::Toggle {
            slot,
            on_turn,
            off_turn,
            glyph_on,
            glyph_off,
            label,
        } = &toggle
        else {
            panic!("root is a toggle")
        };
        assert_eq!(
            (*slot, on_turn.as_str(), off_turn.as_str()),
            (4, "on", "off")
        );
        assert_eq!((glyph_on.as_str(), glyph_off.as_str()), ("✓", "○"));
        assert_eq!(label, "cull ");

        // breadcrumb / progress / pill / icon / tile + the extended input.
        assert!(matches!(
            parse_view_tree(r#"{ "kind":"progress", "props":{ "value":3, "max":4, "label":"build " } }"#).unwrap(),
            ViewNode::Progress { value: 3, max: 4, ref label } if label == "build "
        ));
        assert!(matches!(
            parse_view_tree(r#"{ "kind":"pill", "props":{ "text":"LIVE", "tag":"good" } }"#).unwrap(),
            ViewNode::Pill { ref text, ref tag } if text == "LIVE" && tag == "good"
        ));
        assert!(matches!(
            parse_view_tree(r#"{ "kind":"icon", "props":{ "glyph":"✦", "tag":"accent" } }"#).unwrap(),
            ViewNode::Icon { ref glyph, ref tag } if glyph == "✦" && tag == "accent"
        ));
        assert!(matches!(
            parse_view_tree(r#"{ "kind":"tile", "props":{ "handle":"servo:webview-1", "w":640, "h":480 } }"#).unwrap(),
            ViewNode::Tile { ref handle, w: 640, h: 480 } if handle == "servo:webview-1"
        ));
        let bc = parse_view_tree(
            r#"{ "kind":"breadcrumb", "props":{ "items":[
                 { "label":"BASE", "turn":"seek", "arg":0 }, { "label":"now" } ] } }"#,
        )
        .unwrap();
        let ViewNode::Breadcrumb { items } = &bc else {
            panic!("root is a breadcrumb")
        };
        assert_eq!(items.len(), 2);
        assert_eq!(items[0].turn, "seek");
        assert!(items[1].turn.is_empty(), "a plain crumb has no turn");

        // the extended input carries its submit affordance.
        assert!(matches!(
            parse_view_tree(r#"{ "kind":"input", "props":{ "bindView":"url", "fireTurn":"navigate", "submitLabel":"Go" } }"#).unwrap(),
            ViewNode::Input { ref bind_view, ref fire_turn, ref submit_label }
                if bind_view == "url" && fire_turn == "navigate" && submit_label == "Go"
        ));
        // a plain input keeps the legacy ephemeral-draft shape (empty fire_turn).
        assert!(matches!(
            parse_view_tree(r#"{ "kind":"input", "props":{ "bindView":"draft" } }"#).unwrap(),
            ViewNode::Input { ref fire_turn, .. } if fire_turn.is_empty()
        ));
    }

    #[test]
    fn a_grid_recurses_a_hosted_cell_through_resolve_mounts() {
        let grid = ViewNode::Grid {
            cols: 3,
            children: vec![
                ViewNode::Icon {
                    glyph: "✦".into(),
                    tag: String::new(),
                },
                ViewNode::Host {
                    cell: "tile".into(),
                    view: None,
                },
            ],
        };
        let source =
            MapMountSource::default().with("tile", ViewNode::Text("mounted in a grid".into()));
        let resolved = resolve_mounts(&grid, &source);
        let ViewNode::Grid { cols, children } = &resolved else {
            panic!("root is a grid")
        };
        assert_eq!(*cols, 3);
        let ViewNode::Host { view: Some(v), .. } = &children[1] else {
            panic!("the grid's host child resolved")
        };
        assert!(matches!(&**v, ViewNode::Text(t) if t == "mounted in a grid"));
    }
}
