//! The gpui cockpit — the comprehensive visual master interface.
//!
//! This is the visual layer (gpui-gated, `native-full` only). It renders the
//! embedded [`World`](crate::world::World) — the live local dregg image — across
//! the four dregg-surpasses-Smalltalk axes, each a panel:
//!
//!   * CELL WORLD (left rail) — every cell as a live object; click to inspect.
//!     The ocap axis: the cap count + the graph edges are first-class.
//!   * INSPECTOR (center) — the selected object reflected through the uniform
//!     [`reflect`](crate::reflect) model: cell ⟷ receipt ⟷ image, navigable.
//!   * BLOCKLACE (center-low) — the provenance axis: the receipt chain as a
//!     navigable causal history (time-travel).
//!   * COMPOSER (right) — direct-manipulation turn composition: pick a verb,
//!     watch the EMBEDDED EXECUTOR run it and the image + receipts update live.
//!   * DYNAMICS (right-low) — the live activity feed off the dynamics stream.
//!   * IMAGE/FEDERATION (rail header) — the distribution axis: this image's
//!     state-root commitment, presented as one sovereign image among a
//!     federation.
//!
//! gpui is single-threaded; the `World` is shared as `Rc<RefCell<World>>`. Every
//! verb button mutates it through `World::commit_turn` (the REAL executor) and
//! the views re-render from the post-state on the next frame.

pub(crate) use std::cell::RefCell;
pub(crate) use std::rc::Rc;

pub(crate) use gpui::{
    div, prelude::*, px, uniform_list, AnyElement, App, Context, Entity, FocusHandle, Hsla,
    IntoElement, KeyDownEvent, MouseButton, ParentElement, Render, ScrollStrategy, SharedString,
    Styled, UniformListScrollHandle, WeakEntity, Window,
};

pub(crate) use dregg_cell::CellId;

// THE COMPONENT KIT — the vendored gpui-component widgets the cockpit's panels
// migrate onto for a coherent, real-component look (buttons/rows/lists). `Button`
// carries the kit's variants + sizing; `ButtonVariants`/`Sizable` are the traits
// that enable `.primary()`/`.ghost()`/`.small()`; `Size` for explicit sizing;
// `ClickEvent` is the `on_click` event the `cx.listener` consumes. The kit is
// already `gpui_component::init(cx)`-booted in `main.rs`.
pub(crate) use gpui::ClickEvent;
pub(crate) use gpui_component::button::{Button, ButtonVariants};
pub(crate) use gpui_component::{Selectable, Sizable};

// THE L6 PANED WORKSPACE — the vendored resizable-split/dock engine. The right
// pane's flat 28-tab list is hosted as a `PaneGroup` of `Pane`s, each holding the
// tabs as `TabSurface`s (the adapter below). Splitting a pane puts two surfaces
// side-by-side behind the draggable `PaneAxisElement` divider.
pub(crate) use starbridge_v2::dock::{
    ActivePaneDecorator, CockpitSurface, Pane, PaneGroup, SplitDirection,
    SurfaceId as DockSurfaceId, WindowRegistry,
};

pub(crate) use crate::views::{pill, section_title, theme};
pub(crate) use starbridge_v2::dynamics;
pub(crate) use starbridge_v2::meta_debug::MetaStack;
pub(crate) use starbridge_v2::palette::{Category, CommandId, CommandPalette};
pub(crate) use starbridge_v2::reflect::{self, Field, FieldValue, Inspectable, ObjectKind};
pub(crate) use starbridge_v2::shell::{Scene, Shell};
pub(crate) use starbridge_v2::surface::{SurfaceCapability, SurfaceId};
pub(crate) use starbridge_v2::time_travel::{TimeBranch, TimeCockpitModel};
pub(crate) use starbridge_v2::ui_snapshot::{Liveness, UiSnapshot};
pub(crate) use starbridge_v2::world::{self, CommitOutcome, ResumeMode, World};
// THE ⤳ SHARE surface — the frustum / snapshot editor (cull + pare + verify + share).
pub(crate) use starbridge_v2::affordance::{AffordanceSurface, CellAffordance};
pub(crate) use starbridge_v2::snapshot_editor::{
    recipient_window_cap, PareOutcome, ShareError, SnapshotEditor,
};
// The L1 PRESENTATION SPINE + the moldable inspector framework primitives.
pub(crate) use starbridge_v2::cv_provenance::CvProvenance;
pub(crate) use starbridge_v2::presentable::{
    FocusTarget, GaugeView, GraphView, Halo, LatticeView, MerkleTreeView, PresentCtx, PresentMemo,
    Presentable, Presentation, PresentationBody, PresentationKind, Registry, Spotter, SpotterHit,
    StateMachineView, TimelineView, TraceView,
};
// The newer inspector LANES (L4–L10) — each a real `Presentable` over a live
// protocol object. The moldable inspector reaches them through its lens-family
// picker, projecting each through the SAME generic `render_presentation_body`.
pub(crate) use starbridge_v2::cell_inspector::DeepCell;
pub(crate) use starbridge_v2::circuit_inspector::StateCommitmentBinding;
pub(crate) use starbridge_v2::federation_inspector::FederationSurvey;
pub(crate) use starbridge_v2::receipts_inspector::{ReflectedReceipt, ReflectedReceiptChain};
pub(crate) use starbridge_v2::settlement_inspector::SettlementFamily;
pub(crate) use starbridge_v2::token_inspector::InspectedToken;
// The standalone moldable surfaces + the lane gadgets — each drives its real model
// methods (validate→predict→commit), surfacing refusals as features.
pub(crate) use starbridge_v2::cap_inspector::{AttenuationDial, HeldCapability};
pub(crate) use starbridge_v2::inspect_act::{InspectAct, InspectFocus, SendResult};
pub(crate) use starbridge_v2::predicate_composer::{self, Atom, Composite, PredicateComposer};
pub(crate) use starbridge_v2::service_explorer::{InvokeOutcome, ServiceExplorer};
pub(crate) use starbridge_v2::token_inspector::TokenLoopGadget;
pub(crate) use starbridge_v2::turn_builder::CommittingTurnGadget;
pub(crate) use starbridge_v2::wonder::WonderRoom;
pub(crate) use starbridge_v2::workspace::Workspace;
pub(crate) use starbridge_v2::{Gadget, GadgetInput};
// The feature panels — wired in as tabs of the master interface.
pub(crate) use starbridge_v2::{cipherclerk, debug, edit, replay};
// The A1 DEVELOPER content surfaces — the IDE's editor + terminal panes.
pub(crate) use starbridge_v2::buffer::{BufferCell, BufferView};
pub(crate) use starbridge_v2::terminal::{Command, TerminalCell, TerminalView};
// The A2 SWARM surface — multi-agent cap-coordinated swarm with notify edges.
pub(crate) use starbridge_v2::swarm::{Swarm, SwarmView};
// The four-surface KILLER DEMO (N5) — the pug-handoff evaluation artifact, driven
// live in the SWARM tab (mint → agent turn → notify handoff → the dual refusal).
pub(crate) use starbridge_v2::demo::HeadlineDemo;

/// Which object the inspector is focused on.
#[derive(Clone)]
pub enum Selection {
    Cell(CellId),
    Receipt(usize),
    Image,
}

/// Which **lens family** the moldable inspector is focused through. The default
/// `Cell` lens rides the `Registry`/`Spotter`/memo dispatch (the established
/// spine); the remaining variants make the newer inspector lanes (L4–L10)
/// REACHABLE — each builds its real `Presentable` off the focused cell / the
/// live world and renders its presentation SET through the SAME generic
/// `render_presentation_body`, so a lane needs NO new gpui code to become
/// clickable. The picker cycles the family; the focus cell (and the
/// receipt/slot ordinal) come from the inspector's own camera-aim.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum MoldableLens {
    /// L1 — the live ledger cell (the `Registry`/`Spotter`/memo spine).
    Cell,
    /// L4 — the focused cell's held capabilities (its c-list), each a
    /// [`HeldCapability`] presentation set.
    Capability,
    /// L5 — the focused cell's DEEP reflection ([`DeepCell`]).
    DeepCell,
    /// L6 — the live receipt chain ([`ReflectedReceiptChain`]) + the latest
    /// receipt ([`ReflectedReceipt`]).
    Receipt,
    /// L7 — a real minted macaroon, decoded ([`InspectedToken`]).
    Token,
    /// L9 — the focused cell's canonical state-commitment binding
    /// ([`StateCommitmentBinding`]).
    Circuit,
    /// L10 — a proven settlement family (escrow), its deal-terms +
    /// state-machine ([`SettlementFamily`]).
    Settlement,
    /// L8 — the federation survey (the captp-only remote-path catalog in the
    /// embedded image, surfaced honestly via [`FederationSurvey`]).
    Federation,
    /// ⌖ BLAME (cv) — "why does this cell exist": the ClusterVision provenance of
    /// the focused cell's backing source file (the swarm's reasoning that wrote it),
    /// dialed live as a subprocess and rendered through the SAME generic body widget
    /// ([`CvProvenance`](crate::cv_provenance::CvProvenance)). Degrades honestly when
    /// cv is absent from PATH — never a fabricated provenance edge.
    Blame,
    /// 🔒 READ-CAP / PRIVACY — the focused cell's read-confidentiality membrane,
    /// welded onto the `dregg_cell_crypto::read_cap` organ ([`starbridge_v2::read_cap_lens`]): the
    /// encrypted-field set off the live field-visibility, the `granted ⊆ held`
    /// read-lattice, and the byte-identical-commitment invariant demonstrated live.
    ReadCap,
    /// ⟲ HISTORY / UNDO — the cell's per-cell reversibility, welded onto the
    /// `dregg_turn::reversible` organ ([`starbridge_v2::history_lens`]): the reversibility
    /// map (each change-kind classified by the real `Effect::invert` over the live
    /// ledger) + the cell's lifecycle posture + the un-turn model.
    History,
}

impl MoldableLens {
    /// The lens families in picker order (Cell first — the established spine).
    const ALL: [MoldableLens; 11] = [
        MoldableLens::Cell,
        MoldableLens::Capability,
        MoldableLens::DeepCell,
        MoldableLens::Receipt,
        MoldableLens::Token,
        MoldableLens::Circuit,
        MoldableLens::Settlement,
        MoldableLens::Federation,
        MoldableLens::Blame,
        MoldableLens::ReadCap,
        MoldableLens::History,
    ];

    /// The operator-legible lens label + lane tag.
    fn label(self) -> &'static str {
        match self {
            MoldableLens::Cell => "cell (L1)",
            MoldableLens::Capability => "cap (L4)",
            MoldableLens::DeepCell => "deep-cell (L5)",
            MoldableLens::Receipt => "receipts (L6)",
            MoldableLens::Token => "token (L7)",
            MoldableLens::Circuit => "circuit (L9)",
            MoldableLens::Settlement => "settlement (L10)",
            MoldableLens::Federation => "federation (L8)",
            MoldableLens::Blame => "⌖ blame (cv)",
            MoldableLens::ReadCap => "🔒 read-cap / privacy",
            MoldableLens::History => "⟲ history / undo",
        }
    }

    /// The next family in the cycle (the picker chip's click).
    fn next(self) -> MoldableLens {
        let i = MoldableLens::ALL
            .iter()
            .position(|l| *l == self)
            .unwrap_or(0);
        MoldableLens::ALL[(i + 1) % MoldableLens::ALL.len()]
    }
}

/// The service root key the moldable inspector's Token lens mints against — the
/// SAME key the cockpit's `lane_token` gadget is built with (so the L7 lens
/// decodes the minted macaroon against the right service key).
const MOLDABLE_TOKEN_ROOT_KEY: [u8; 32] = [0x11u8; 32];

/// The source path the ⌖ BLAME (cv) lens dials ClusterVision on. A domain cell is
/// content-addressed (it carries no filesystem path), so "why does this cell exist"
/// resolves to the inspector IMAGE's own provenance — the agent reasoning that wrote
/// the live cockpit — keyed on the focused cell's identity. The cv-bridge degrades
/// honestly when cv is absent from PATH (`docs/deos/REFLEXIVE-DISTRIBUTED-IMAGE.md`
/// §2.5).
const CV_BLAME_SOURCE_PATH: &str = "starbridge-v2/src/cockpit.rs";

// (`weld_pending_presentation` removed: both the read-cap/privacy and history/undo
// lenses are now WELDED onto their landed organs — `read_cap_lens` + `history_lens`.
// No moldable lens degrades to a "weld pending" placeholder any more.)

/// Which workspace tab the right-hand pane presents. The master interface
/// surfaces the composer alongside the four feature panels.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Tab {
    /// The LANDING portal — the warm, alive front door of the live verified
    /// image (the boot view). A text-rich greeting that names the running
    /// system reflectively (the embedded executor · the live cells · the
    /// receipt nervous system · the organs) and invites exploration. See
    /// [`starbridge_v2::landing`].
    Home,
    Shell,
    Agent,
    /// The IDE's EDITOR pane — a text buffer as a cap-confined Surface cell
    /// (A1). Distinct from `Editor` (the artifact-authoring Live Editor).
    Buffer,
    /// The IDE's TERMINAL pane — a command surface as a cap-confined Surface
    /// cell (A1; the home of the ADOS tool-call seam).
    Terminal,
    Composer,
    /// The SIMULATE tab — the WHAT-IF intent composer (studio-parity): compose
    /// any intent over any cell(s) across a broad effect palette, PREDICT its
    /// consequences in a forked throwaway world (the real executor over a deep
    /// copy of the live ledger) — the predicted post-state + receipt or refusal —
    /// then COMMIT the identical turn for real. The live world is untouched until
    /// commit. See [`starbridge_v2::simulate`].
    Simulate,
    Objects,
    Debugger,
    Replay,
    Cipherclerk,
    Editor,
    /// The A2 SWARM tab — multi-agent cap-coordinated activity surface.
    /// N agent panes as confined Surface cells, coordinating via the
    /// notify-edge inbox (EmitEvent → NotifyEdge → async drain turn).
    Swarm,
    /// The ORGANS tab — reflects each dregg organ's live cell-state (trustline /
    /// flash-well live in embed-core; channel / mailbox / court surfaced honestly
    /// as remote-path). See [`starbridge_v2::organs`].
    Organs,
    /// The GRAPH tab — the whole-graph ocap delegation layout (the View tree IS
    /// the ocap graph): nodes = cells, edges = capability grants, with multi-hop
    /// reachability + a layered delegation-depth layout. See
    /// [`starbridge_v2::graph`].
    Graph,
    /// The PROOFS tab — the proof-attach + STARK verification-status board: each
    /// committed turn's verification tier + the attach/verify route. See
    /// [`starbridge_v2::proofs`].
    Proofs,
    /// The WEB-OF-CELLS tab — the cockpit as a native BROWSER of the `dregg://`
    /// docuverse: the addressable cells (the real `WebOfCells` attested fetch +
    /// ledger-drawn `OriginChrome`), an opened cell's per-viewer affordance
    /// surface (the real `AffordanceSurface::project_for` attenuation) + its
    /// rehydration liveness-type, firing through the embedded executor. See
    /// [`starbridge_v2::web_cells`].
    WebOfCells,
    /// THE WEB-SHELL BROWSER tab — a general `http(s)://` BROWSER surface (distinct
    /// from `WebOfCells`, which browses the `dregg://` web-of-cells). A real
    /// gpui-component text [`gpui_component::input::InputState`] URL bar
    /// (Enter-to-go), back / forward / reload navigation over a URL history stack,
    /// and a content tile that calls
    /// [`servo_render::webview::render_url_to_frame`] (the real
    /// `ServoBuilder → WebViewBuilder → SWGL → read_to_image` flow behind the
    /// [`CapGate`](servo_render::webview) net-cap allowlist) and paints the returned
    /// `RgbaFrame` through the same `img()` path the web-of-cells tab uses. A
    /// `dregg://` address routes to the `WebOfCells` browser (the existing web-of-cells
    /// resolution path); an `http(s)://` address renders here. Fail-closed: a render
    /// error / cap refusal is shown in-band, the tile never silently blanks. See
    /// [`super::panels_webshell`].
    WebShell,
    /// The WHAT-LINKS-HERE tab — Ted Nelson's two-way link, navigable: for the
    /// focused cell it renders the REAL `Backlinks` witness-graph (who transcludes
    /// ME), navigated by the genuine `DreggverseMap` and PROJECTED through the
    /// focused agent's `Membrane` (the link fog-of-war — a backlink the viewer's
    /// caps cannot admit is OMITTED). Each backlink is clickable to navigate into
    /// the observing cell (and recursively its own "what links here"). See
    /// [`starbridge_v2::links_here`].
    LinksHere,
    /// The POWERBOX tab (CapDesk) — the trusted designation flow: a confined
    /// app-cell requests a capability it lacks; the TRUSTED powerbox (the cockpit
    /// principal, NOT the app) presents a picker filtered to what the USER actually
    /// holds (`mint_needs_held_factory` made visible — you can't grant what you
    /// don't hold); the user designates a target + the rights to confer; the
    /// powerbox MINTS a fresh ATTENUATED capability into the app's c-list via a REAL
    /// grant turn through the embedded executor. See [`starbridge_v2::powerbox`].
    Powerbox,
    /// THE MOLDABLE INSPECTOR (the Pharo moldable inspector made visible) — picks a
    /// focused object, resolves its [`Registry`]-built presentation SET, and renders
    /// it as a tab-strip (one sub-tab per [`Presentation`]) through the GENERIC
    /// presentation renderer (one widget per [`PresentationBody`] variant), with the
    /// [`Halo`] ring and a [`Spotter`] search box (⌘K-style) that re-focuses. Adding
    /// a new `Presentable` later needs NO new gpui code. See
    /// [`starbridge_v2::presentable`] + `docs/deos/INSPECTOR-FRAMEWORK.md`.
    Moldable,
    /// THE INSPECT→ACT loop — the Smalltalk inspect→act→inspect keystone: the
    /// focused object's reflected state PLUS the messages it understands (its
    /// cap-gated affordances, each with a cap badge), sending one as a REAL verified
    /// turn and re-inspecting the post-state. See [`starbridge_v2::inspect_act`].
    InspectAct,
    /// THE SERVICE EXPLORER (🛰 SERVICES) — the Postman-like surface over
    /// CELLS-AS-SERVICE-OBJECTS: it discovers a focused cell's PUBLISHED INTERFACE
    /// (the methods its program dispatches on, derived via
    /// `InterfaceDescriptor::derive_replayable`), lists each method with its arity
    /// / auth requirement / replay-vs-serviced semantics / a cap badge, and lets
    /// you INVOKE a replayable method as a REAL verified turn — the deos-interior
    /// face of the `invoke()` front door. The invocation DESUGARS to an ordinary
    /// method-targeting turn (no kernel `Effect::Invoke`); an unknown / serviced /
    /// unauthorized method is refused in-band. See
    /// [`starbridge_v2::service_explorer`].
    ServiceExplorer,
    /// THE SERVICE DIRECTORY (📇 DIRECTORY) — the WHOLE-IMAGE sibling of the
    /// per-cell [`Tab::ServiceExplorer`]: it BROWSES the live image for every cell
    /// that publishes a service interface (each cell's interface derived live via
    /// [`dregg_cell::interface::InterfaceDescriptor::derive_replayable`]), listing
    /// each discovered service with its interface-id, method count, kind, and
    /// whether it has been ANNOUNCED. Selecting a service and pressing "announce"
    /// publishes its interface as a REAL verified turn (an `Effect::EmitEvent`
    /// carrying the canonical announce topic, committed through the embedded
    /// executor), leaving a witnessed receipt the next discover reads back — the
    /// publish loop closes over the real ledger, not a transient flag. See
    /// [`starbridge_v2::service_directory`].
    ServiceDirectory,
    /// THE WORKSPACE — the doIt / printIt / inspectIt evaluator: compose an intent,
    /// evaluate it in a FORKED throwaway world (predict, never mutate), print the
    /// predicted receipt, inspect the predicted post-state as live objects, then
    /// commit-or-discard. See [`starbridge_v2::workspace`].
    Workspace,
    /// THE WONDER ROOM — the AOL-wonder front door: every cell a pokeable glowing
    /// object (glow = real recent activity), with direct-manipulation halos
    /// (inspect / grab / explain). See [`starbridge_v2::wonder`].
    Wonder,
    /// THE LANES — the moldable-inspector gadgets made reachable: the predicate
    /// composer (caveat language), the turn builder, the attenuation dial, and the
    /// macaroon token loop — each driving its real model methods
    /// (validate→predict→commit / build), surfacing refusals as features.
    Lanes,
    /// THE TEMPORAL COCKPIT (⏳ TIME) — the headline livability surface: time-travel
    /// + suspend + fractal meta-debug as ONE control panel. The REWIND SCRUBBER drags
    ///   over the verified witness history (genesis → head) and re-derives the focused
    ///   views at any past point (root-verified [`crate::replay::History::replay_to`])
    ///   with a live [`Liveness`] badge; the ⏸ SUSPEND button halts the real loop (the
    ///   M5 gate) and stages the continuation, ▶ RESUME drains it; the METASTACK
    ///   navigator climbs a reflective tower over the suspended world (debug the
    ///   debugger). All over the REAL models — see [`starbridge_v2::time_travel`] /
    ///   [`starbridge_v2::replay`] / [`starbridge_v2::meta_debug`].
    Time,
    /// THE ⤳ SHARE surface (the FRUSTUM / SNAPSHOT EDITOR) — the share-with-
    /// attenuation pre-send editor: take a [`crate::ui_snapshot::UiSnapshot`] of the
    /// focused view, then CULL the frustum (which lenses / sub-objects are in the
    /// shared slice), PARE the authority (the REAL [`crate::cap_inspector::AttenuationDial`]
    /// over `is_attenuation` — an amplifying choice is REFUSED in-band), VERIFY live
    /// (the membrane-projected per-viewer preview = the genuine
    /// [`crate::affordance::AffordanceSnapshot::rehydrate_for`]), and SHARE a
    /// revocable, attenuated, rehydratable [`crate::snapshot_editor::SharedArtifact`].
    /// The GitHub-org-settings cap UX over the sound substrate. See
    /// [`starbridge_v2::snapshot_editor`] + `docs/desktop-os-research/REHYDRATABLE-SURFACES.md`.
    Share,
    /// THE DOCS EDITOR (📄 DOCS) — the dreggverse DOCUMENT LANGUAGE as a cockpit
    /// surface (`docs/deos/DOCUMENT-LANGUAGE.md`). A document IS a real cell; an
    /// edit IS a cap-gated turn through the genuine `dregg_turn::TurnExecutor`
    /// (riding [`dregg_doc::ExecutorDrivenDoc`]) leaving a real receipt — an
    /// unauthorized region-edit is REFUSED in-band (the anti-ghost tooth). A
    /// CONFLICT is a first-class STATE you live in: two live alternatives rendered
    /// inline, EACH tagged with who wrote it (the provenance receipt), with a
    /// one-click RESOLVE (a resolving patch). Transclusion + backlinks reuse the
    /// built Nelson pieces (`web_cells` / `links_here`). See
    /// [`starbridge_v2::doc_editor`].
    Docs,
    /// THE ⚷ TRUST surface — the human-layer "you cannot lose your own OS" face
    /// ([`starbridge_v2::trust_panel`], human-layer M1): WHO-I-AM (your devices,
    /// your guardians-as-faces with the K-of-N threshold drawn, the KEL rotation
    /// timeline) + the recovery UX ("ask your guardians" quorum gauge mirroring the
    /// executor's threshold floor, the cooling window as a safety feature). Built off
    /// the REAL `dregg_sdk::identity::inspect_identity` decode (a representative
    /// identity until an on-ledger identity cell is wired — HORIZONLOG).
    Trust,
    /// THE ⚙ DEVTOOLS surface — "Firebug for a verified OS": ONE tab with three
    /// inspector sub-tabs over the live image — NETWORK (the data plane:
    /// deliveries / inbox queues / wakes / notify edges, browser-Network-tab
    /// style), LOG/RECEIPTS (the blocklace + receipt timeline as a filterable
    /// drill-down console), and FEDERATION (committee · epoch · checkpoint ·
    /// bridges · revocation). See [`super::panels_devtools`].
    Devtools,
}

impl Tab {
    const ALL: [Tab; 32] = [
        Tab::Docs,
        Tab::Trust,
        Tab::Devtools,
        Tab::Home,
        Tab::Wonder,
        Tab::Time,
        Tab::Moldable,
        Tab::InspectAct,
        Tab::ServiceExplorer,
        Tab::ServiceDirectory,
        Tab::Workspace,
        Tab::Lanes,
        Tab::Shell,
        Tab::Agent,
        Tab::Swarm,
        Tab::Graph,
        Tab::Organs,
        Tab::Proofs,
        Tab::WebOfCells,
        Tab::WebShell,
        Tab::LinksHere,
        Tab::Powerbox,
        Tab::Share,
        Tab::Buffer,
        Tab::Terminal,
        Tab::Composer,
        Tab::Simulate,
        Tab::Objects,
        Tab::Debugger,
        Tab::Replay,
        Tab::Cipherclerk,
        Tab::Editor,
    ];
    /// This tab's index in [`Tab::ALL`] — the `u64` the [`WorkspaceCell`] witnesses
    /// (the §3.4 selector that moves from a Rust field to a cell read).
    fn index(self) -> usize {
        Tab::ALL.iter().position(|t| *t == self).unwrap_or(0)
    }

    /// The tab at `idx` in [`Tab::ALL`] (the inverse of [`Tab::index`]) — how
    /// `render()` resolves the witnessed [`WorkspaceCell`] index back to a `Tab`.
    /// Out-of-range degrades to the first tab (`Home`), never panics.
    fn from_index(idx: usize) -> Tab {
        Tab::ALL.get(idx).copied().unwrap_or(Tab::Home)
    }

    fn label(self) -> &'static str {
        match self {
            Tab::Home => "HOME",
            Tab::Shell => "SHELL",
            Tab::Agent => "AGENT",
            Tab::Swarm => "SWARM",
            Tab::Graph => "GRAPH",
            Tab::Organs => "ORGANS",
            Tab::Proofs => "PROOFS",
            Tab::WebOfCells => "WEB-OF-CELLS",
            Tab::WebShell => "🌐 WEB-SHELL",
            Tab::LinksHere => "WHAT-LINKS-HERE",
            Tab::Powerbox => "POWERBOX",
            Tab::Moldable => "INSPECTOR",
            Tab::InspectAct => "INSPECT-ACT",
            Tab::ServiceExplorer => "🛰 SERVICES",
            Tab::ServiceDirectory => "📇 DIRECTORY",
            Tab::Workspace => "WORKSPACE",
            Tab::Wonder => "WONDER",
            Tab::Lanes => "LANES",
            Tab::Time => "⏳ TIME",
            Tab::Share => "⤳ SHARE",
            Tab::Docs => "📄 DOCS",
            Tab::Trust => "⚷ TRUST",
            Tab::Devtools => "⚙ DEVTOOLS",
            Tab::Buffer => "BUFFER",
            Tab::Terminal => "TERMINAL",
            Tab::Composer => "COMPOSER",
            Tab::Simulate => "SIMULATE",
            Tab::Objects => "OBJECTS",
            Tab::Debugger => "DEBUGGER",
            Tab::Replay => "REPLAY",
            Tab::Cipherclerk => "CIPHERCLERK",
            Tab::Editor => "EDITOR",
        }
    }

    /// Resolve a surface label (a [`Tab::label`] string) back to its [`Tab`] — the
    /// inverse of [`Tab::label`]. How the cockpit maps a layout cell's surface rows
    /// (the [`deos_js::LayoutModel::surfaces_of`] strings, which ARE these labels)
    /// back to the renderable `Tab`s. `None` for an unknown label (the layout names
    /// a surface the cockpit has no tab for — the read-side skips it).
    pub(crate) fn from_label(label: &str) -> Option<Tab> {
        Tab::ALL.into_iter().find(|t| t.label() == label)
    }
}

/// THE DOCK ADAPTER — one cockpit [`Tab`], wrapped as a dockable
/// [`CockpitSurface`] so it can live inside a resizable/splittable
/// [`Pane`]. It holds a weak handle onto the live cockpit and, on
/// [`render_body`](CockpitSurface::render_body), re-enters it to call the single
/// per-tab dispatch [`Cockpit::panel_for_tab`] — so a hosted surface renders the
/// SAME body the flat tab list did.
///
/// WHY THE RE-ENTRY IS SOUND: a [`Pane`] is rendered by the [`PaneGroup`] through
/// `AnyView::from(pane).cached(..)`. gpui's cached-view path renders the pane in a
/// *later* layout pass — after `Cockpit::render` has returned and the cockpit
/// entity is back in its slot — so `cockpit.update(..)` here never collides with
/// the cockpit's own (already-finished) render lease. (Mirrors Zed's
/// workspace↔item rendering, where an item re-reads workspace state from inside
/// its own deferred render.)
///
/// Cheap to clone (a weak handle + an enum + a focus handle), so splitting a pane
/// — which `boxed_clone`s the surface into the new pane — is free.
struct TabSurface {
    tab: Tab,
    cockpit: WeakEntity<Cockpit>,
    focus: FocusHandle,
}

impl TabSurface {
    fn new(tab: Tab, cockpit: WeakEntity<Cockpit>, focus: FocusHandle) -> Self {
        Self {
            tab,
            cockpit,
            focus,
        }
    }
}

impl CockpitSurface for TabSurface {
    fn item_id(&self) -> DockSurfaceId {
        DockSurfaceId(self.tab.index() as u64)
    }

    fn tab_label(&self) -> SharedString {
        SharedString::from(self.tab.label())
    }

    fn render_body(&mut self, _window: &mut Window, cx: &mut App) -> AnyElement {
        let tab = self.tab;
        self.cockpit
            .update(cx, |cockpit, cx| cockpit.panel_for_tab(tab, cx))
            .unwrap_or_else(|_| {
                div()
                    .flex()
                    .items_center()
                    .justify_center()
                    .size_full()
                    .text_color(theme::muted())
                    .child(SharedString::from(tab.label()))
                    .into_any_element()
            })
    }

    fn focus_handle(&self, _cx: &App) -> FocusHandle {
        self.focus.clone()
    }

    fn boxed_clone(&self) -> Box<dyn CockpitSurface> {
        Box::new(TabSurface {
            tab: self.tab,
            cockpit: self.cockpit.clone(),
            focus: self.focus.clone(),
        })
    }
}

/// The whole cockpit — owns the shared world + the current selection + a
/// dynamics cursor for the activity feed, plus the four feature panels' UI
/// state (the modules kept their renders gpui-free; the cockpit owns the state
/// and maps the render-models onto gpui).
pub struct Cockpit {
    world: Rc<RefCell<World>>,
    /// Stable, sorted list of cell ids (so the rail order is deterministic and
    /// selection survives across commits).
    cells: Vec<CellId>,
    /// M2 DELTA LOOP — the last dynamics cursor this view folded. Each render
    /// folds `world.dynamics().since(self.dynamics_cursor)` into per-slice
    /// invalidation, then advances to `world.dynamics().cursor()`. This is the
    /// producer↔consumer JOIN: turning per-frame O(ledger) projection into
    /// O(changed-cells) (`docs/deos/EFFICIENCY-WELD-PLAN.md` §2.1).
    dynamics_cursor: usize,
    /// The per-(focus,viewer) projection memo, wrapping the unchanged-pure
    /// `Registry::present`, valid while the live head is unchanged (§2.3).
    present_memo: PresentMemo,
    selection: Selection,
    /// The last action's outcome banner (committed hash / rejection reason).
    last_outcome: Option<String>,
    /// Three anchor cells for the demo verbs (treasury, service, user).
    anchors: [CellId; 3],
    /// The active right-pane tab — the FREE in-memory draft selector (a tab switch
    /// conserves nothing, the §3.5 stream weight class: mutated freely, no ledger
    /// cost). It is the *visible* aim; the witnessed (rewindable) selector rides
    /// [`Self::workspace_cell`], to which it is synced + occasionally committed.
    tab: Tab,
    /// THE DEV DOCK — whether the collapsible bottom dev strip is open (⌘J). The
    /// dev workspace (terminal/editor/shell), available in any mode.
    dock_open: bool,
    /// FIRST-RUN — whether the cockpit shows the calm, sparse FIRST-VIEW overlay
    /// (a warm "welcome to your world", a FEW clickable cells, ONE "try this"
    /// affordance, and a quiet "explore" to reveal the full frame) INSTEAD of the
    /// full 5-mode wall. `true` only on a brand-new image (set by login via
    /// [`Self::set_first_run`]); `false` for a returning owner (their wall is
    /// familiar) and after the operator clicks "explore" (or fires "try this").
    /// The full chrome is one click away — progressive disclosure, not a separate
    /// mode. Defaults `false` (the headless cockpit bake / a re-mount shows the
    /// full frame unless asked).
    first_run: bool,
    /// M3 WIDEN (`docs/deos/REFLEXIVE-MIGRATION.md` §3.4 — `render(workspace_subgraph)`).
    /// The cockpit's active-tab SELECTOR self-hosted as a REAL cell: the same
    /// [`BufferCell`] two-tier split [`ViewCell`] uses, only the payload is the
    /// active-tab index. `render()` resolves its dispatch FROM this cell's committed
    /// index ([`Self::active_tab`]), so the WHOLE cockpit selector is cell-driven —
    /// the 24-arm `Tab` match stays; only its *source* moved from a Rust field to a
    /// witnessed cell read. A tab switch advances the cell's nonce (the rewindable
    /// UI history), conserving nothing.
    workspace_cell: starbridge_v2::view_cell::WorkspaceCell,
    /// OPTIMISTIC NAV — `true` while a deferred [`Self::witness_tab`] commit is
    /// already queued on the foreground async executor. A tab click moves the free
    /// draft (`self.tab`) + repaints IMMEDIATELY, then schedules the witnessed
    /// `SetField` commit OFF the paint path. This flag coalesces a burst of rapid
    /// tab-flips: the first click queues the task, the rest just move the draft, and
    /// the single queued task commits the LATEST `self.tab` (one turn per burst, not
    /// one per click — so the witnessed UI-history does not balloon either).
    tab_witness_pending: bool,

    // --- DEBUGGER panel state ----------------------------------------------
    /// The turn the debugger inspects (a demo transfer the operator can run);
    /// re-executed faithfully via `debug::render` against the live world.
    debug_turn: dregg_turn::turn::Turn,
    /// The breakpoints the debugger evaluates over the turn's steps.
    breakpoints: Vec<debug::Breakpoint>,

    // --- REPLAY panel state ------------------------------------------------
    /// The time-travel scrubber cursor (a step in `0..=history.len()`).
    replay_cursor: usize,
    /// An optional pinned what-if fork (the cockpit owns it; `replay::Fork`).
    replay_fork: Option<replay::Fork>,

    // --- ⏳ TEMPORAL COCKPIT (the TIME tab) state --------------------------
    /// The REWIND SCRUBBER cursor — a step in `0..=history.len()` (the live
    /// world's own [`World::recorded_turns`] history). Dragging it re-derives the
    /// focused views at that past point (root-verified replay) with a `Liveness`
    /// badge; `head` = the live present. Distinct from `replay_cursor` so the TIME
    /// tab and the legacy REPLAY tab scrub independently.
    time_cursor: usize,
    /// THE METASTACK — the lazily-materialized reflective tower over the suspended
    /// world (the M5 fractal meta-debug: BASE → meta¹ → meta² …). The cockpit owns
    /// it; "suspend & inspect" pushes a level, "descend" pops. Empty until the
    /// operator first suspends + climbs (the live system runs un-reflected).
    meta_stack: MetaStack,
    /// THE ⑂ DIVERGENT BRANCH — the result of forking the past at the scrubber
    /// cursor ([`dregg_turn::reversible::ReversibleHistory::fork_at`]) and driving
    /// a divergent verified turn from it. `None` until the operator clicks "⑂
    /// BRANCH HERE"; pinned so the TIME tab can paint the divergent future beside
    /// the (untouched) live line. The temporal dual of the spatial branch-and-stitch
    /// fork — a verified future grown from the past, the parent timeline immune.
    time_branch: Option<TimeBranch>,

    // --- CIPHERCLERK panel state -------------------------------------------
    /// The HD-derived identity vault (real `AgentCipherclerk`s).
    clerk: cipherclerk::Cipherclerk,
    /// The last cipherclerk action's result banner (real mint/attenuate/
    /// delegate/discharge outcome).
    clerk_outcome: Option<cipherclerk::ClerkOutcome>,

    // --- EDITOR panel state ------------------------------------------------
    /// The live-editor's authoring/validation/deploy state.
    editor: edit::EditorState,

    // --- the cap-first SHELL / compositor ----------------------------------
    /// The cap-first window manager / compositor over the live world. Every
    /// window op routes through its CAP-GATED API.
    shell: Shell,
    /// The operator's cap-vault: the [`SurfaceCapability`] held for each open
    /// surface. The cockpit IS the operator (it holds every surface's cap), but
    /// it can ONLY drive a surface by presenting the cap from here — so the
    /// shell's ocap discipline is real, not bypassed. The console's cap lives
    /// here too (under `console_surface`).
    surface_caps: std::collections::HashMap<SurfaceId, SurfaceCapability>,
    /// The console surface's id (the privileged trusted-root surface).
    console_surface: SurfaceId,
    /// A monotonic frame-digest counter for the verified-scene present teaching
    /// moments (so every `present()` genuinely advances the frame).
    frame_seq: u64,

    // --- the AGENT-ACTIVITY surface (the ADOS keystone) --------------------
    /// The agent cell bound to the agent-activity surface — a cap-confined VIEW
    /// of an agent loop's provable activity (held mandate · cap-gated turns +
    /// receipts · authorization boundary), rendered as a Surface cell. The
    /// service cell stands in as a live, cap-holding, turn-committing agent.
    agent_surface: starbridge_v2::agent::AgentSurface,

    // --- AGENT MEMORY as a umem (the revolution, made a clickable affordance) -
    /// The last checkpoint of the LIVE agent's working-set
    /// ([`agent_memory::AgentMemoryCheckpoint`]), captured off the live World by the
    /// Agent tab's "⛂ checkpoint" affordance and resumed into a fresh verified
    /// context by "↺ resume". `None` until the operator checkpoints. This makes
    /// agent-memory-as-umem load-bearing in a user-facing flow — the sibling of the
    /// TIME tab's `reify_ledger` verified reconstruction (`b1bd3305`).
    agent_memory: Option<starbridge_v2::agent_memory::AgentMemoryCheckpoint>,
    /// The last agent-memory action verdict (checkpoint captured / resumed-and-verified
    /// / a fail-closed refusal), shown in the Agent panel's memory section.
    agent_memory_status: Option<String>,
    /// The resumed working-set witness from the last "↺ resume into fresh context":
    /// `(working_slot_0, all_teeth_passed)` — the verified handoff readout shown live.
    agent_memory_resumed: Option<(u64, bool)>,

    // --- the A1 EDITOR/BUFFER surface (a text buffer as a Surface cell) -----
    /// The editor buffer — a cap-confined text buffer backed by a real cell
    /// (its digest rides the cell's state; an edit is a cap-gated turn). The
    /// IDE's editor pane.
    editor_buffer: BufferCell,
    /// The WRITE capability the cockpit holds for `editor_buffer` (the shell
    /// minted it on open). The cockpit can only COMMIT an edit by presenting
    /// this — a read-only mirror could not (the §7 cap discipline at the editor).
    editor_buffer_cap: SurfaceCapability,

    // --- the A1 TERMINAL surface (a command surface as a Surface cell) ------
    /// The terminal — a cap-confined command surface whose backing cell's
    /// c-list IS the command authority (a command outside it REFUSES). The home
    /// of the ADOS A0 tool-call seam; the IDE's terminal pane.
    terminal: TerminalCell,

    // --- the A2 SWARM surface (multi-agent cap-coordination) ----------------
    /// The swarm coordinator: N agent cells coordinating as confined Surface
    /// cells with the notify-edge inbox (EmitEvent → NotifyEdge → drain turn).
    /// The treasury is the "coordinator" (holds caps to both service + user);
    /// service and user are the "workers" it orchestrates via emit-event.
    swarm: Swarm,

    // --- the four-surface KILLER DEMO (N5) — the pug-handoff artifact --------
    /// The headline killer demo, driven live in the SWARM tab one frame per button
    /// press (mint → agent turn → notify handoff → the DUAL REFUSAL). It owns its
    /// OWN metered verified world (so the budget meter accrues real computrons and
    /// the Stingray ceiling can bite), separate from the cockpit's free-play world —
    /// the demo is a self-contained scripted scenario the operator drives to the
    /// climax. The four frames + both refusals are the single runnable end-to-end
    /// story a stranger runs to judge whether the substrate is real and usable.
    ///
    /// LAZY (`None` until first needed): booting it builds a metered verified world
    /// + deploys the mint factory, and the demo's turns are the slow proof-bearing
    ///   metered path. It is therefore NOT booted at window-open — it boots on the
    ///   first navigation to the SWARM tab (or the first killer-demo verb), so it
    ///   never sits on the first-paint path. Access it through [`Self::killer_demo`].
    killer_demo: Option<HeadlineDemo>,
    /// The render lines the killer demo has emitted so far (one per advanced frame),
    /// shown in the SWARM-tab demo strip. Newest appended last.
    killer_demo_lines: Vec<String>,

    /// The PENDING demo seed turns — the five real executor turns that populate the
    /// HOME image (treasury/user/service flows + the ocap grant + a field write).
    /// The window opens on the bare genesis image (these NOT yet run), and a
    /// foreground async task drives [`Self::seed_next_demo_turn`] after first paint,
    /// committing one per yield so the cells/receipts fill in LIVE. `None`/exhausted
    /// once fully seeded. (The headless/test path pre-seeds and passes `None`.)
    pending_seed: Option<world::DemoSeed>,

    // --- the ⌘K COMMAND PALETTE --------------------------------------------
    /// The command palette over EVERY action (open with ⌘K). The cockpit feeds
    /// it keystrokes and dispatches its selected `CommandId` through the same
    /// `&mut Cockpit` verbs the buttons call.
    palette: CommandPalette,
    /// Scroll handle for the palette's result list, so keyboard navigation
    /// (↑/↓) can scroll the highlighted row back into view — the list
    /// virtualizes over the FULL match set (no fixed cap), so every matched
    /// command is reachable by mouse-scroll AND by holding arrow-down.
    palette_scroll: UniformListScrollHandle,
    /// Focus handle for the root, so the cockpit receives key events.
    focus: FocusHandle,

    // --- the LIVE NODE connection (the remote-federation panel) -------------
    /// An optional LIVE connection to a remote dregg node (`--node <url>`). The
    /// embedded world is the headline; this is the master interface ALSO watching
    /// a running federation's receipt nervous system + reflecting its cells. `None`
    /// when no node URL was supplied (the pure embedded image).
    live_node: Option<starbridge_v2::client::LiveNode>,
    /// The background SSE reader handle (`/api/events/stream`). The cockpit drains
    /// its channel each frame and fires `cx.notify()` per streamed receipt — so the
    /// live receipt list advances PER RECEIPT, not on a manual snapshot reload.
    live_stream: Option<starbridge_v2::client::ReceiptStreamHandle>,
    /// The live receipt feed: the cursor + bounded ring the stream fills (the
    /// thing that REPLACES the static snapshot). Drained under `cx.notify()`.
    live_feed: starbridge_v2::live_node::ReceiptFeed,
    /// The last blocking snapshot of the live node (status + cell reflections),
    /// projected into the uniform `Inspectable` model. Refreshed by the "sync"
    /// verb; the per-receipt updates come from `live_stream`.
    live_snapshot: Option<starbridge_v2::client::LiveSnapshot>,

    // --- the WEB-OF-CELLS browser panel state ------------------------------
    /// Which `dregg://` cell the web-of-cells browser has OPENED (the focused
    /// row whose affordance surface is projected). `None` opens the first
    /// addressable cell. Clicking a row in the panel sets this.
    web_cells_opened: Option<CellId>,
    /// The viewer authority the browser projects the affordance surface FOR — the
    /// `AuthRequired` the cockpit holds over the surface (what gates the
    /// progressive attenuation). Defaults to the EDITOR tier (`Either`): a real
    /// principal that genuinely clears view/comment/edit but NOT admin, so the
    /// attenuation the panel shows is true, not a demo. The "view as root" toggle
    /// lifts it to the root tier (`None`) to reveal the attenuated-away affordances.
    web_cells_viewer_rights: dregg_cell::AuthRequired,
    /// The last web-of-cells affordance-fire outcome banner (a REAL executor
    /// verdict — committed receipt / refused-with-reason, or the in-band
    /// anti-ghost refusal).
    web_cells_outcome: Option<String>,
    /// IF the user pressed "⚡ make interactive" on the transclusion row and the
    /// powerbox GRANTED: the upgraded semi-reinteractive transclusion (the host now
    /// holds an attenuated affordance cap reaching the source). The panel then shows
    /// the INTERACTIVE state + a fire button. `None` = the quote is still read-only
    /// (the default — a verified quote is free; interacting needs a powerbox grant).
    web_cells_upgraded: Option<starbridge_v2::web_cells::SemiReinteractiveTransclusion>,
    /// The last transclusion-upgrade / transcluded-fire outcome banner (a REAL
    /// powerbox grant-turn verdict, or the in-band read-only/over-wide refusal).
    web_cells_transclusion_outcome: Option<String>,

    // --- the WHAT-LINKS-HERE panel state -----------------------------------
    /// Which cell the what-links-here panel is FOCUSED on (the cell the question
    /// "who transcludes ME?" is asked of). `None` focuses the cockpit's own `user`
    /// principal. Clicking a backlink row sets this to the OBSERVING cell — so the
    /// panel navigates INTO the cell that links here (and renders ITS own backlinks).
    links_here_focus: Option<CellId>,
    /// The depth bound the transitive backlink walk uses (backlinks-of-backlinks):
    /// `1` = the direct backlinks of the focus only; higher reaches further out. The
    /// walk is cycle-safe + depth-bounded, so it is always finite + cheap. Toggleable
    /// in the panel (1 ⇄ 2 ⇄ 3) so the operator can watch the docuverse map deepen.
    links_here_depth: usize,
    /// The viewer authority the what-links-here map is PROJECTED for — the held
    /// authority that decides the link fog-of-war (`DreggverseMap::project_for`
    /// through this viewer's `Membrane`). The focus's backlinks are gated behind a
    /// `Proof` link lineage, so a `None` (root) viewer projects it and SEES them, while
    /// an INCOMPARABLE `Signature` viewer is FOGGED (the membrane refuses the lineage).
    /// Defaults to `None` (root, sees all); the panel toggles None ⇄ Signature so the
    /// operator can watch a gated backlink reveal/fog — the membrane made navigational.
    /// (Distinct from the web-of-cells `web_cells_viewer_rights`, whose None ⇄ Either
    /// drives the affordance attenuation — a different lattice line.)
    links_here_viewer_rights: dregg_cell::AuthRequired,

    // --- the DOCS editor panel state (the dreggverse document language) -----
    /// THE DOCUMENT EDITOR — a document riding a real cell, edited through the
    /// genuine executor (a patch IS a cap-gated turn), with conflicts-as-states +
    /// the hypermedia (transclusion/backlinks) faces. See
    /// [`starbridge_v2::doc_editor`].
    doc_editor: starbridge_v2::doc_editor::DocEditor,
    /// The last DOCS-editor edit/resolve outcome banner (a REAL executor verdict:
    /// committed receipt or the in-band cap refusal).
    doc_outcome: Option<String>,

    /// The confined APP-cell whose capability request the powerbox is mediating —
    /// a real cell in the live ledger holding NO ambient authority (a freshly
    /// "launched" app-as-cell). The powerbox grants designated, attenuated caps
    /// INTO this cell's c-list. Seeded at boot with a demo app, then repointed by
    /// the RUNTIME app-launcher (`run_launch_confined_app`) at each fresh confined
    /// app it spawns — so the powerbox mediates whichever app was most recently
    /// launched.
    powerbox_app: Option<CellId>,
    /// The rights tier the powerbox would CONFER on the next designation — the
    /// attenuation the user picks (the granted cap is `≤` the user's held
    /// authority; the powerbox refuses to amplify past the held ceiling). Defaults
    /// to the narrow `Signature` so a click demonstrates real attenuation away from
    /// a wider held right; toggleable to the wider tiers (still gated by the held
    /// ceiling + the executor's no-amplification rule).
    powerbox_confer_rights: dregg_cell::AuthRequired,
    /// The last powerbox designation outcome banner (a REAL grant-turn verdict —
    /// the executor's own receipt on a mint, or the in-band amplification/
    /// no-such-target refusal).
    powerbox_outcome: Option<String>,
    /// The apps LAUNCHED at runtime through the app-launcher (each a fresh confined
    /// app-cell birthed into the live world, holding no ambient authority). The
    /// most-recently-launched app is the one whose request the powerbox panel is
    /// currently mediating (`powerbox_app` points at it). Pressing "+ launch confined
    /// app" births a NEW one and routes its request through the existing powerbox.
    launched_apps: Vec<starbridge_v2::powerbox::LaunchedApp>,
    /// THE PRE-BUILT APP LAUNCHER roster — the wired starbridge-apps (gallery /
    /// sealed-auction / bounty-board / … / polis) LAUNCHED onto the cockpit's live
    /// World from the POWERBOX/LAUNCHER surface. Each is a real app cell + program
    /// seeded onto the live ledger, its representative affordance fired as a real
    /// verified turn (so the cell + receipt are on `World::ledger()` /
    /// `World::receipts()`, inspectable). Pressing a "launch" row appends one (a fresh
    /// app instance). See [`super::panels_app_launcher`].
    #[cfg(feature = "app-registry")]
    apps_launched: Vec<panels_app_launcher::LaunchedAppRecord>,
    /// The last pre-built-app launch outcome banner (the executor's verdict — a real
    /// committed receipt, or the in-band launch refusal).
    #[cfg(feature = "app-registry")]
    apps_outcome: Option<String>,

    // --- the WHAT-IF / SIMULATE intent composer (studio-parity) -------------
    /// The intent under composition: the agent + a forest of actions/effects the
    /// operator builds before simulating. Driven by the SIMULATE panel's pickers.
    sim_draft: starbridge_v2::simulate::IntentDraft,
    /// Index into [`sorted_cells`] for the TARGET the next added effect acts on
    /// (the "target" picker cycles this). The agent picker cycles `sim_draft.agent`.
    sim_target_idx: usize,
    /// Which effect-kind template the next "+ add" will append (the effect picker
    /// cycles this over the full palette — the studio-parity coverage).
    sim_effect_idx: usize,
    /// The last what-if outcome (the predicted post-state + receipt, or the
    /// refusal), shown in the results area. `None` until the first SIMULATE.
    sim_outcome: Option<starbridge_v2::simulate::SimOutcome>,
    /// A short banner for the last commit-for-real (the REAL executor's verdict on
    /// the committed intent), distinct from the prediction. `None` until committed.
    sim_commit_banner: Option<String>,

    // --- THE MOLDABLE INSPECTOR (the Pharo moldable inspector) ---------------
    /// M3 — THE INSPECTOR'S OWN VIEW CELL (`docs/deos/REFLEXIVE-MIGRATION.md` §3).
    /// The moldable inspector's `(focus, present_idx)` camera-aim is self-hosted as
    /// a REAL cell (the [`BufferCell`] two-tier split, generalized): the visible
    /// draft (`inspector_view.doc()`) is free to re-aim; its WITNESSED state rides
    /// the backing cell, advanced by an occasional [`ViewCell::commit`]. So the
    /// inspector's camera-aim is a witnessed dregg graph, the panel reads its focus
    /// FROM the cell, and the inspector is itself inspectable
    /// ([`FocusTarget::ViewCell`]) — *inspect the inspector*. The `moldable_focus` /
    /// `moldable_present_idx` Rust fields are SUBSUMED into this view cell.
    inspector_view: starbridge_v2::view_cell::ViewCell,
    /// Whether the inspector is turned ON ITSELF — the reflexive toggle. When true,
    /// the panel focuses [`FocusTarget::ViewCell`] on the inspector's own backing
    /// cell (the inspector inspects its own view state); when false, it focuses the
    /// drafted domain cell. This is the live "inspect the inspector" switch.
    inspector_reflexive: bool,
    /// Browser-style navigation HISTORY of the cockpit's UI state (the nav-API
    /// `capture_nav` snapshot + its `nav_key`). Every navigation appends; the
    /// back/forward controls (← → and ⌘[ / ⌘]) restore through it. The
    /// programmatic nav API made interactive.
    nav_hist: Vec<(String, CockpitNavState)>,
    nav_cursor: usize,
    /// Suppresses history recording while a back/forward restore is in flight.
    nav_jumping: bool,
    /// PINNED VIEWS (bookmarks): saved `(label, captured-state)` the operator can
    /// jump back to with one click (the ☆ in the nav bar). Session-scoped.
    nav_pins: Vec<(String, CockpitNavState)>,
    /// MACRO recording (⏺▶): when `Some`, the `(history-length, world-snapshot)` at
    /// record start. The recorded turn-sequence becomes a `dregg_turn::script::Script`
    /// (a macro = a recorded replayable turn-sequence; see docs/deos/MACRO-AS-CUSTOM-VK.md).
    macro_recording: Option<(usize, World)>,
    /// The last recorded macro — the captured `Script` + the world state it was
    /// recorded from. Replay re-runs it on a FORK of that start state (the live
    /// world is never touched; this is a verified preview of the macro).
    last_macro: Option<(dregg_turn::script::Script, World)>,
    macro_outcome: Option<String>,
    /// The [`Spotter`] search query (the ⌘K-style box). Each typed char re-runs the
    /// universal search; a hit click re-focuses the inspector.
    moldable_query: String,
    /// Which **lens family** the moldable inspector is focused through (the
    /// picker that makes the L4–L10 inspector lanes reachable; `Cell` rides the
    /// `Registry` spine, the rest build their lane `Presentable` off the focus).
    moldable_lens: MoldableLens,
    /// Whether the DEEP native moldable presentation set (Registry · Spotter · Halo ·
    /// lens-strip · RawFields) is REVEALED below the live inspector card. Default
    /// `false`: when the deos-js inspector card is mounted, it IS the Inspect surface
    /// and the native presentation set does NOT also draw in the same bounds (NOTHING
    /// DRAWS TWICE). A deliberate "⊕ deep reflection (native presentation set)" toggle
    /// opens it as a distinct, scrolled-to companion face below the card — never an
    /// underlay. When NO card is mounted (fail-soft / card-pane off), the native set is
    /// the surface and renders unconditionally.
    moldable_show_native: bool,

    // --- THE INSPECT→ACT loop -----------------------------------------------
    /// The cell the inspect→act loop is focused on. `None` focuses the first cell.
    inspect_act_focus: Option<CellId>,
    /// The last `send` outcome banner (a REAL committed receipt / an in-band refusal).
    inspect_act_outcome: Option<String>,

    // --- THE SERVICE EXPLORER (the Postman-like invoke() surface) -----------
    /// The cell the service explorer is focused on. `None` focuses the first cell.
    service_explorer_focus: Option<CellId>,
    /// The method symbol the explorer has selected to invoke (`None` = none picked).
    service_explorer_selected: Option<[u8; 32]>,
    /// The args string the user typed (comma-separated decimals → felts). The
    /// explorer parses it into the `args` vector an invocation carries.
    service_explorer_args: String,
    /// The last invoke outcome banner (a REAL committed receipt / an in-band refusal).
    service_explorer_outcome: Option<String>,

    // --- THE SERVICE DIRECTORY (the whole-image discover/announce surface) ---
    /// The discovered service the directory has SELECTED to announce (its backing
    /// cell). `None` = none picked yet; a row's "select" sets it, and "announce"
    /// publishes its interface as a real verified turn. See
    /// [`super::panels_service_directory`].
    service_directory_selected: Option<CellId>,
    /// Whether the directory listing includes the opaque (no-interface) capability
    /// cells too (the `include_non_services` filter — toggled in the panel).
    service_directory_include_caps: bool,
    /// The last announce outcome banner (a REAL committed receipt / an in-band
    /// refusal — nothing to announce / the executor gated the announcer).
    service_directory_outcome: Option<String>,

    // --- THE WORKSPACE (doIt / printIt / inspectIt) -------------------------
    /// The live workspace evaluator — composes an intent, evaluates it in a forked
    /// throwaway world (predict, never mutate), and commits-or-discards.
    workspace: Workspace,
    /// Index into [`sorted_cells`] the workspace's "+ add transfer to" picker cycles.
    workspace_target_idx: usize,

    // --- THE LANES (the gadget surfaces) ------------------------------------
    /// Which lane the LANES panel has open (0=predicate · 1=turn · 2=cap · 3=token).
    lane_idx: usize,
    /// The predicate composer's current composite (the caveat-language gadget). Built
    /// over the focused cell; `validate()` / `build()` are the real model methods.
    lane_composite: Composite,
    /// The committing turn-builder gadget (emits a real `IntentDraft` → predict/commit).
    lane_turn: CommittingTurnGadget,
    /// The attenuation dial over a held cap (the cap-attenuation value gadget), if the
    /// cockpit principal holds one (else the lane explains the absence honestly).
    lane_dial: Option<AttenuationDial>,
    /// The macaroon mint→attenuate→delegate→discharge loop gadget (a verifier gadget).
    lane_token: TokenLoopGadget,
    /// The last lane-gadget outcome banner (a REAL build/predict/commit/discharge verdict).
    lane_outcome: Option<String>,

    // --- THE ⤳ SHARE surface (the frustum / snapshot editor) ----------------
    /// The live snapshot editor the ⤳ SHARE tab sculpts: a captured
    /// `UiSnapshot` of the focused view + the `Frustum` being culled + the
    /// `AttenuationDial` paring the authority. `None` until the operator captures
    /// the focused view (the tab shows the "capture this view" call-to-action).
    /// Built fresh by [`Self::share_capture`] so it tracks the live focus.
    share_editor: Option<starbridge_v2::snapshot_editor::SnapshotEditor>,
    /// The shared artifacts this session has minted (the audit trail — each a
    /// revocable, attenuated, rehydratable slice). Newest last; "⊘ revoke" flips one.
    share_artifacts: Vec<starbridge_v2::snapshot_editor::SharedArtifact>,
    /// The recipient-preview tier the SHARE tab previews "what they would see" AS:
    /// `true` = a WIDE (Either) recipient, `false` = a NARROW (Signature) recipient.
    /// The membrane-projected preview re-derives per this toggle (the two members).
    share_preview_wide: bool,
    /// The last SHARE action's outcome banner (a captured slice / a refused pare /
    /// a minted artifact / a revocation — REAL verdicts, surfaced).
    share_outcome: Option<String>,

    // --- THE L6 PANED WORKSPACE (the right pane) -----------------------------
    /// The right pane's resizable-split tree. The flat 28-tab list is hosted as a
    /// [`PaneGroup`]: the un-split base case is ONE [`Pane`] holding every tab as a
    /// [`TabSurface`] (so it looks like today's tabbed right pane), and a split puts
    /// two surfaces side-by-side behind the draggable divider. `None` until the
    /// first render seeds it (it needs `window`/`cx` + the cockpit's own
    /// [`WeakEntity`], not cleanly available in the constructor).
    pane_group: Option<PaneGroup>,
    /// The pane that currently has focus within [`Self::pane_group`] — the split
    /// target + the active-pane border anchor. Kept in sync as panes are
    /// activated/split. `None` until the group is seeded.
    active_pane: Option<Entity<Pane>>,

    // --- SURFACE MIGRATION (the Local→Surface tear-off) ---------------------
    /// THE WINDOW REGISTRY — the record of which surfaces are currently TORN OFF
    /// into their own OS windows (`docs/deos/SURFACE-MIGRATION.md`, the first
    /// concrete migration). A tear-off relocates a surface along the firmament
    /// distance axis from `Surface`-in-the-cockpit to its OWN `Surface` window,
    /// identity preserved (the same [`Tab`] body over the same cell). The cockpit
    /// drives `tear_off`/`pop_back` through this; an empty registry is the
    /// single-window cockpit (the headless bake never tears off). See
    /// [`Self::tear_off_tab`].
    window_registry: WindowRegistry,
    /// One-shot guard: whether the durable image's torn-off windows have been
    /// re-opened yet (the crash-relaunch RESTORATION). A reopened image carries a
    /// witnessed torn-off-tabs bitset on the [`WorkspaceCell`]; on the first render
    /// the cockpit re-pops those windows ([`Self::restore_torn_windows`]) and sets
    /// this so it runs exactly once (re-opening every frame would mint duplicates).
    torn_restored: bool,

    // --- THE ⚙ DEVTOOLS surface ---------------------------------------------
    /// Which DEVTOOLS inspector sub-tab is open, as a `u8` index
    /// (0 = NETWORK · 1 = LOG/RECEIPTS · 2 = FEDERATION). A free in-memory
    /// selector (conserves nothing); decoded by `DevtoolsSub::from_index`.
    devtools_sub: u8,
    /// The DEVTOOLS row filter (case-insensitive substring over the NETWORK /
    /// LOG row text). Set by the filter-bar preset chips; empty = show all.
    devtools_filter: String,

    // --- THE WEB-SHELL BROWSER surface (a general http(s):// browser) --------
    /// The URL bar — a real gpui-component single-line text [`gpui_component::input::InputState`].
    /// LAZY (`None` until the first render): the input entity needs a live
    /// `&mut Window` (`InputState::new(window, cx)`) + the cockpit's own weak handle
    /// for the Enter subscription, neither cleanly available in the constructor; it
    /// is seeded by [`Self::ensure_webshell_input`] on the first paint and the
    /// `InputEvent::PressEnter` subscription drives [`Self::webshell_go`]. `None` on
    /// the gpui-free / headless path (which drives navigation through `webshell_go`
    /// directly).
    webshell_input: Option<Entity<gpui_component::input::InputState>>,
    /// The navigation HISTORY stack of URLs the browser has visited (the back /
    /// forward spine). Each entry is a URL string; [`Self::webshell_cursor`] points
    /// at the current one. A fresh navigation truncates any forward tail and pushes.
    webshell_history: Vec<String>,
    /// The cursor into [`Self::webshell_history`] — the currently-shown URL. Back
    /// decrements, forward increments, both re-drive the render of the URL at the
    /// new cursor (so back/forward genuinely re-fetch, not just relabel).
    webshell_cursor: usize,
    /// The last render's status / loading line (e.g. "rendered N×M", a cap refusal,
    /// a parse error, or the net-cap seam note). Fail-closed: a render error is
    /// SHOWN here, the previous tile is kept (the surface never silently blanks).
    webshell_status: String,
    /// The last successfully-rendered page frame (the content tile). `Some` once a
    /// page has rendered; retained across a failing navigation (fail-closed). Gated
    /// on `servo` (the `RgbaFrame` type only exists when the render crate is in).
    #[cfg(feature = "servo")]
    webshell_frame: Option<servo_render::RgbaFrame>,
    /// A PENDING URL-bar value to write into [`Self::webshell_input`] on the next
    /// render (where a live `&mut Window` is in hand — `InputState::set_value` needs
    /// it). Set by back/forward/programmatic navigation so the address bar mirrors
    /// the viewed URL; applied + cleared in [`Self::ensure_webshell_input`]. `None`
    /// while the bar already reflects the cursor (so user typing is never stomped).
    webshell_input_pending: Option<String>,
    /// **THE PERSISTENT LIVE WEBVIEW** (`SERVO-INTERACTIVE.md §5.1`) — one long-lived
    /// `servo::WebView` on one `servo::Servo` engine, held across frames so the web-shell
    /// pane is LIVE-interactive (scroll / click / type → re-render) rather than a static
    /// per-navigation snapshot. `None` until the first navigation opens it; thereafter
    /// [`Self::webshell_apply_live_input`] feeds gpui pane events into it and pulls the
    /// fresh tile into [`Self::webshell_frame`]. `RefCell` because the render `&self`
    /// helpers + the event listeners both reach it; `!Send` (servo is `Rc`-based) — the
    /// cockpit is a main-thread gpui view, so this never crosses a thread. Gated on
    /// `web-shell` (the `LiveWebView` type lives behind `servo-render/libservo`).
    #[cfg(feature = "web-shell")]
    webshell_live: std::cell::RefCell<Option<servo_render::webview::LiveWebView>>,
    /// The web-shell content tile's last painted WINDOW-SPACE bounds, recorded each
    /// frame by a transparent `canvas` overlay covering the tile. The pane's scroll /
    /// click / move listeners report positions in WINDOW coordinates; subtracting this
    /// origin yields the WebView-local device point fed to `apply_input`. `None` until
    /// the tile has painted once. `Cell` (the recorder runs on the `&self` paint path).
    #[cfg(feature = "servo")]
    webshell_tile_bounds: std::cell::Cell<Option<gpui::Bounds<gpui::Pixels>>>,
    /// **THE WEB-SHELL TILE FOCUS HANDLE** — the focus the rendered-page tile holds so
    /// it can TAKE KEYBOARD INPUT. A click on the page focuses this handle (distinct
    /// from the URL-bar input's own focus); while it holds focus, the tile's
    /// `on_key_down` routes each typed character to [`Self::webshell_live_key`] →
    /// `LiveWebView::apply_input(WebInput::KeyChar)`, so you can TYPE into a web form /
    /// search box. LAZY (`None` until the first paint seeds it via
    /// [`Self::ensure_webshell_input`], which has the live `&mut Window` a
    /// `cx.focus_handle()` wants on the paint path). Gated on `web-shell` (only the
    /// live build routes keys into the page).
    #[cfg(feature = "web-shell")]
    webshell_tile_focus: Option<gpui::FocusHandle>,
    /// **THE LIVE INSPECTOR CARD** (rung 2) — the cockpit's Inspect-mode main surface
    /// reborn as a deos-js card. LAZY: `None` until the Inspect surface first paints,
    /// then built by [`Self::ensure_inspector_card`] from the focused cell's moldable
    /// faces over the LIVE `World` (a [`CardPane`] entity + its shared attached applet),
    /// and rebuilt when the focus changes. Hosting the entity in `moldable_panel`
    /// renders the focused cell's faces live; an affordance button fires a real turn on
    /// the cockpit's World. `None` on the gpui-free / `card-pane`-off build (which keeps
    /// the Rust moldable inspector as the surface).
    #[cfg(all(feature = "dev-surfaces", feature = "card-pane"))]
    inspector_card: Option<InspectorCardMount>,
    /// **THE SIX LANDED CARDS AS THEIR MODE'S MAIN-PANE SURFACE** — the composer / objects /
    /// graph / dynamics / agent / links cards, each mounted as a [`CardPane`] over the live
    /// `World` (the SAME pattern as [`Self::inspector_card`], generalized). LAZY: a mount is
    /// `None` until its mode's surface first paints, then built by [`Self::ensure_mode_card`]
    /// and rebuilt when the focus moves. Keyed by [`ModeCard`]. `None` on the gpui-free /
    /// `card-pane`-off build (which keeps the Rust panels as the surfaces).
    #[cfg(all(feature = "dev-surfaces", feature = "card-pane"))]
    mode_cards:
        std::collections::HashMap<starbridge_v2::dock::card_surface::ModeCard, ModeCardMount>,
    /// **FRAME-SCOPED ONE-HOST GUARD for the live cards.** A gpui [`Entity`] may be hosted
    /// at most ONCE per frame — rendering the same entity in two element positions in one
    /// frame re-enters its render lease and aborts the process (the same one-window
    /// invariant the torn-off placeholder enforces across windows, now WITHIN one window).
    /// Every pane in the L6 [`PaneGroup`] holds ALL tabs, so two split panes can both have
    /// the same card-tab (e.g. Objects) active at once, calling
    /// [`Self::mode_card_surface`] / hosting the inspector card TWICE in one frame. This set
    /// records which surfaces a `CardPane` entity has already been hosted for THIS frame
    /// (cleared at the top of [`render`](crate::cockpit::render)); the second host shows a
    /// calm "shown in another pane" placeholder instead of re-hosting the entity.
    /// `RefCell` because the hosts are `&self` render helpers.
    #[cfg(all(feature = "dev-surfaces", feature = "card-pane"))]
    frame_hosted_cards:
        std::cell::RefCell<std::collections::HashSet<starbridge_v2::dock::card_surface::ModeCard>>,
    /// Frame-scoped one-host guard for the live INSPECTOR card (same hazard as
    /// [`Self::frame_hosted_cards`]: two panes both showing the Moldable surface would host
    /// the inspector `CardPane` entity twice in one frame). `true` once hosted this frame;
    /// cleared at the top of `render`.
    #[cfg(all(feature = "dev-surfaces", feature = "card-pane"))]
    frame_hosted_inspector: std::cell::Cell<bool>,
    /// **THE LIVE LAYOUT CELL** (rung 3) — the cockpit's OWN structure (its mode→surface
    /// arrangement) as a deos-js [`LayoutCard`](deos_js::LayoutCard), superseding the
    /// hardcoded [`CockpitMode::surfaces`]/[`CockpitMode::ALL`]/[`Tab::mode`]. The rail
    /// ([`Self::mode_rail`]) renders [`deos_js::LayoutModel::mode_order`], each mode's
    /// sub-nav ([`Self::mode_subnav`]) renders [`deos_js::LayoutModel::surfaces_of`]
    /// (resolving each surface label → `Tab` via [`Tab::from_label`]), and a `Go<Surface>`
    /// jump's rail highlight ([`Self::active_mode`]) reads [`deos_js::LayoutModel::mode_of`]
    /// — so the chrome's STRUCTURE is editable DATA, not compiled code. A `move:<SURFACE>`
    /// affordance dispatches [`deos_js::LayoutCard::reshape`] and the rail re-renders
    /// (receipted, cap-gated). LAZY: `None` until the first paint, then built by
    /// [`Self::ensure_layout_card`] (default [`deos_js::LayoutModel::cockpit_default`], which
    /// mirrors the hardcoded arrangement exactly). `None` on the gpui-free / `card-pane`-off
    /// build, where the reads degrade to the hardcoded `CockpitMode`/`Tab` fallback.
    #[cfg(all(feature = "dev-surfaces", feature = "card-pane"))]
    layout_card: Option<deos_js::LayoutCard>,
    /// **MAKE YOUR FIRST CARD** — the onboarding keystone mount. `None` until a first-timer
    /// clicks "make your first card →" on the calm first-view, then a real editable starter
    /// card minted over the LIVE `World` (its substance the stranger's own home cell) by
    /// [`Self::make_first_card`]. While `Some`, the cockpit shows the dedicated FIRST-CARD
    /// view ([`Self::first_card_view`]) — the card live, plus two real edit affordances
    /// ("add a button", "rename the title", each a receipted patch) and the card's own `+1`
    /// (a real verified turn). "explore everything" dismisses it into the full frame (the
    /// card stays minted on the ledger). `None` on the gpui-free / `card-pane`-off build.
    #[cfg(all(feature = "dev-surfaces", feature = "card-pane"))]
    first_card: Option<FirstCardMount>,
}

/// The cockpit's live mount of the onboarding FIRST CARD — the [`CardPane`] gpui entity
/// (rendered over the live World) and the [`ModeCardSurface`] holding its editable view
/// document (the edit-from-within route the onboarding edit affordances drive). Minted by
/// [`Cockpit::make_first_card`]; hosted by [`Cockpit::first_card_view`].
#[cfg(all(feature = "dev-surfaces", feature = "card-pane"))]
pub(crate) struct FirstCardMount {
    pub(crate) entity: Entity<starbridge_v2::card_pane::CardPane>,
    pub(crate) surface: starbridge_v2::dock::card_surface::ModeCardSurface,
    /// A short, friendly note on the last onboarding gesture (the minted / fired / edited
    /// outcome), shown under the card so a first-timer SEES that their click did something
    /// real (a receipt, a patch). Refreshed by each first-card affordance.
    pub(crate) note: Option<String>,
}

/// The cockpit's live mount of a [`ModeCard`] as a mode's main-pane surface: the
/// [`CardPane`] gpui entity (rendered over the live World), the [`ModeCardSurface`] (which
/// holds the editable view document — the edit-from-within route), and the focused cell the
/// view-tree was generated for (so [`Cockpit::ensure_mode_card`] rebuilds on a focus move).
#[cfg(all(feature = "dev-surfaces", feature = "card-pane"))]
pub(crate) struct ModeCardMount {
    pub(crate) entity: Entity<starbridge_v2::card_pane::CardPane>,
    pub(crate) surface: starbridge_v2::dock::card_surface::ModeCardSurface,
    pub(crate) focus: CellId,
    /// A cheap digest of the cockpit-side [`SurfaceState`] this card was built from (0 for a
    /// stateless card). [`Cockpit::ensure_mode_card`] rebuilds when it changes, so a stateful
    /// card (cipherclerk / debugger / replay) never shows stale data after the operator mutates
    /// the live state (a mint, a scrubber move, a new turn under the lens).
    pub(crate) state_fp: u64,
}

/// The cockpit's live inspector-card mount: the [`CardPane`] gpui entity, the shared
/// live attached applet the rendered widgets drive (so a fire lands on the operator's
/// real cell + a `bind` re-reads it), and the focused cell the view-tree was generated
/// for (so [`Cockpit::ensure_inspector_card`] rebuilds when the focus moves).
#[cfg(all(feature = "dev-surfaces", feature = "card-pane"))]
pub(crate) struct InspectorCardMount {
    pub(crate) entity: Entity<starbridge_v2::card_pane::CardPane>,
    #[allow(dead_code)] // held to keep the live attached applet alive for the mounted card
    pub(crate) applet: starbridge_v2::card_pane::SharedAttached,
    pub(crate) focus: CellId,
}

/// A navigation action over the cockpit's pure-navigation controls — the edge
/// vocabulary of the atlas's UI-exploration tree.
#[derive(Clone, Copy, Debug)]
pub enum NavAction {
    Tab(usize),
    CycleFocus,
    CycleLens,
    ToggleReflexive,
    CyclePresent,
    CycleInspectFocus,
    /// Cycle the SERVICE EXPLORER's focused cell.
    CycleServiceFocus,
    CycleSimTarget,
    CycleSimEffect,
    SetLane(usize),
    ToggleWebViewer,
    OpenWebCell,
    CycleLinksDepth,
    ToggleLinksViewer,
    CycleLinksFocus,
    CyclePowerboxConfer,
    ToggleSharePreview,
    ReplayNext,
    ReplayPrev,
    TimeNext,
    TimePrev,
}

/// A captured snapshot of the cockpit's navigation-relevant UI state — enough to
/// restore the rendered view exactly (the explorer's backtrack token).
#[derive(Clone)]
pub struct CockpitNavState {
    tab_idx: usize,
    selection: Selection,
    moldable_lens: MoldableLens,
    inspector_reflexive: bool,
    iv_focus: Option<CellId>,
    iv_present: usize,
    inspect_act_focus: Option<CellId>,
    service_explorer_focus: Option<CellId>,
    sim_target_idx: usize,
    sim_effect_idx: usize,
    lane_idx: usize,
    web_viewer: dregg_cell::AuthRequired,
    web_opened: Option<CellId>,
    links_focus: Option<CellId>,
    links_depth: usize,
    links_viewer: dregg_cell::AuthRequired,
    powerbox_confer: dregg_cell::AuthRequired,
    share_wide: bool,
    replay_cursor: usize,
    time_cursor: usize,
}

// ===========================================================================
// THE COCKPIT, SPLIT INTO FOCUSED SUBMODULES.
//
// `Cockpit` (the model struct + the shared types above) lives here; its behaviour
// is a single logical `impl Cockpit` carved across the modules below (Rust lets
// one type's inherent impl span many files of the same crate). Each submodule
// pulls the shared imports + types through `use super::*;`. The free render
// helpers live in `helpers` and are re-exported here so every panel module sees
// them. Nothing here changes behaviour — it is purely the old god-module
// re-shelved by responsibility.
// ===========================================================================

mod helpers;
pub(crate) use helpers::*;

mod actions;
mod construct;
mod dispatch;
mod docs;
mod frame;
pub use frame::CockpitMode;
mod live;
mod nav;
mod panels_app_launcher;
mod panels_devtools;
mod panels_main;
mod panels_moldable;
mod panels_service_directory;
mod panels_web;
mod panels_webshell;
mod panels_workspace;
mod render;
pub mod root;
mod shell_ops;
mod time;
