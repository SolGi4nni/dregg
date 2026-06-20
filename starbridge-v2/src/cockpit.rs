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

use std::cell::RefCell;
use std::rc::Rc;

use gpui::{
    div, prelude::*, px, Context, FocusHandle, Hsla, IntoElement, KeyDownEvent, MouseButton,
    ParentElement, Render, SharedString, Styled, Window,
};

use dregg_cell::CellId;

use crate::views::{pill, section_title, theme};
use starbridge_v2::dynamics;
use starbridge_v2::palette::{Category, CommandId, CommandPalette};
use starbridge_v2::reflect::{self, Field, FieldValue, Inspectable, ObjectKind};
use starbridge_v2::shell::{Scene, Shell};
use starbridge_v2::surface::{SurfaceCapability, SurfaceId};
use starbridge_v2::world::{self, CommitOutcome, ResumeMode, World};
use starbridge_v2::meta_debug::MetaStack;
use starbridge_v2::time_travel::TimeCockpitModel;
use starbridge_v2::ui_snapshot::{Liveness, UiSnapshot};
// THE ⤳ SHARE surface — the frustum / snapshot editor (cull + pare + verify + share).
use starbridge_v2::affordance::{AffordanceSurface, CellAffordance};
use starbridge_v2::snapshot_editor::{
    recipient_window_cap, PareOutcome, ShareError, SnapshotEditor,
};
// The L1 PRESENTATION SPINE + the moldable inspector framework primitives.
use starbridge_v2::presentable::{
    FocusTarget, GaugeView, GraphView, Halo, LatticeView, MerkleTreeView, PresentCtx, PresentMemo,
    Presentable, Presentation, PresentationBody, PresentationKind, Registry, Spotter, SpotterHit,
    StateMachineView, TimelineView, TraceView,
};
use starbridge_v2::cv_provenance::CvProvenance;
// The newer inspector LANES (L4–L10) — each a real `Presentable` over a live
// protocol object. The moldable inspector reaches them through its lens-family
// picker, projecting each through the SAME generic `render_presentation_body`.
use starbridge_v2::cell_inspector::DeepCell;
use starbridge_v2::circuit_inspector::StateCommitmentBinding;
use starbridge_v2::federation_inspector::FederationSurvey;
use starbridge_v2::receipts_inspector::{ReflectedReceipt, ReflectedReceiptChain};
use starbridge_v2::settlement_inspector::SettlementFamily;
use starbridge_v2::token_inspector::InspectedToken;
// The standalone moldable surfaces + the lane gadgets — each drives its real model
// methods (validate→predict→commit), surfacing refusals as features.
use starbridge_v2::inspect_act::{InspectAct, InspectFocus, SendResult};
use starbridge_v2::workspace::Workspace;
use starbridge_v2::wonder::WonderRoom;
use starbridge_v2::predicate_composer::{self, Atom, Composite, PredicateComposer};
use starbridge_v2::turn_builder::CommittingTurnGadget;
use starbridge_v2::cap_inspector::{AttenuationDial, HeldCapability};
use starbridge_v2::token_inspector::TokenLoopGadget;
use starbridge_v2::{Gadget, GadgetInput};
// The feature panels — wired in as tabs of the master interface.
use starbridge_v2::{cipherclerk, debug, edit, replay};
// The A1 DEVELOPER content surfaces — the IDE's editor + terminal panes.
use starbridge_v2::buffer::{BufferCell, BufferView};
use starbridge_v2::terminal::{Command, TerminalCell, TerminalView};
// The A2 SWARM surface — multi-agent cap-coordinated swarm with notify edges.
use starbridge_v2::swarm::{Swarm, SwarmView};
// The four-surface KILLER DEMO (N5) — the pug-handoff evaluation artifact, driven
// live in the SWARM tab (mint → agent turn → notify handoff → the dual refusal).
use starbridge_v2::demo::HeadlineDemo;

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
    /// welded onto the `dregg_cell::read_cap` organ ([`starbridge_v2::read_cap_lens`]): the
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
        let i = MoldableLens::ALL.iter().position(|l| *l == self).unwrap_or(0);
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
#[derive(Clone, Copy, PartialEq, Eq)]
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
    /// over the verified witness history (genesis → head) and re-derives the focused
    /// views at any past point (root-verified [`crate::replay::History::replay_to`])
    /// with a live [`Liveness`] badge; the ⏸ SUSPEND button halts the real loop (the
    /// M5 gate) and stages the continuation, ▶ RESUME drains it; the METASTACK
    /// navigator climbs a reflective tower over the suspended world (debug the
    /// debugger). All over the REAL models — see [`starbridge_v2::time_travel`] /
    /// [`starbridge_v2::replay`] / [`starbridge_v2::meta_debug`].
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
}

impl Tab {
    const ALL: [Tab; 28] = [
        Tab::Docs,
        Tab::Trust,
        Tab::Home,
        Tab::Wonder,
        Tab::Time,
        Tab::Moldable,
        Tab::InspectAct,
        Tab::Workspace,
        Tab::Lanes,
        Tab::Shell,
        Tab::Agent,
        Tab::Swarm,
        Tab::Graph,
        Tab::Organs,
        Tab::Proofs,
        Tab::WebOfCells,
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
            Tab::LinksHere => "WHAT-LINKS-HERE",
            Tab::Powerbox => "POWERBOX",
            Tab::Moldable => "INSPECTOR",
            Tab::InspectAct => "INSPECT-ACT",
            Tab::Workspace => "WORKSPACE",
            Tab::Wonder => "WONDER",
            Tab::Lanes => "LANES",
            Tab::Time => "⏳ TIME",
            Tab::Share => "⤳ SHARE",
            Tab::Docs => "📄 DOCS",
            Tab::Trust => "⚷ TRUST",
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
    /// M3 WIDEN (`docs/deos/REFLEXIVE-MIGRATION.md` §3.4 — `render(workspace_subgraph)`).
    /// The cockpit's active-tab SELECTOR self-hosted as a REAL cell: the same
    /// [`BufferCell`] two-tier split [`ViewCell`] uses, only the payload is the
    /// active-tab index. `render()` resolves its dispatch FROM this cell's committed
    /// index ([`Self::active_tab`]), so the WHOLE cockpit selector is cell-driven —
    /// the 24-arm `Tab` match stays; only its *source* moved from a Rust field to a
    /// witnessed cell read. A tab switch advances the cell's nonce (the rewindable
    /// UI history), conserving nothing.
    workspace_cell: starbridge_v2::view_cell::WorkspaceCell,

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
    /// metered path. It is therefore NOT booted at window-open — it boots on the
    /// first navigation to the SWARM tab (or the first killer-demo verb), so it
    /// never sits on the first-paint path. Access it through [`Self::killer_demo`].
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
    web_cells_upgraded:
        Option<starbridge_v2::web_cells::SemiReinteractiveTransclusion>,
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
    /// The [`Spotter`] search query (the ⌘K-style box). Each typed char re-runs the
    /// universal search; a hit click re-focuses the inspector.
    moldable_query: String,
    /// Which **lens family** the moldable inspector is focused through (the
    /// picker that makes the L4–L10 inspector lanes reachable; `Cell` rides the
    /// `Registry` spine, the rest build their lane `Presentable` off the focus).
    moldable_lens: MoldableLens,

    // --- THE INSPECT→ACT loop -----------------------------------------------
    /// The cell the inspect→act loop is focused on. `None` focuses the first cell.
    inspect_act_focus: Option<CellId>,
    /// The last `send` outcome banner (a REAL committed receipt / an in-band refusal).
    inspect_act_outcome: Option<String>,

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
}

impl Cockpit {
    /// Construct the cockpit, optionally connecting to a LIVE remote node at
    /// `node_url` (the master interface ALSO watching a running federation). When
    /// present, the SSE receipt stream is opened immediately so the live receipt
    /// list begins filling (each streamed receipt fires `cx.notify()` on render).
    pub fn with_node(
        world: Rc<RefCell<World>>,
        anchors: [CellId; 3],
        focus: FocusHandle,
        node_url: Option<String>,
        pending_seed: Option<world::DemoSeed>,
    ) -> Self {
        let cells = sorted_cells(&world.borrow());

        // Seed the debugger with a demo turn (treasury → user transfer) that
        // the operator can step + explain against the live world.
        let [treasury, service, user] = anchors;
        let debug_turn = world.borrow().turn(treasury, vec![world::transfer(treasury, user, 1_000)]);

        // Seed the cipherclerk vault with two real HD-derived identities.
        let mut clerk = cipherclerk::Cipherclerk::new();
        clerk.add_identity(cipherclerk::Identity::from_byte("alice", "dregg/cockpit", 0x01));
        clerk.add_identity(cipherclerk::Identity::from_byte("bob", "dregg/cockpit", 0x02));

        // Seed the editor with a conserving demo forest already validated.
        let mut editor = edit::EditorState::default();
        editor.set_artifact("Transfer 250 treasury→user (1 root, conserving)");
        {
            let mut fb = edit::ForestBuilder::new();
            fb.root(
                edit::ActionBuilder::new(treasury)
                    .effect(dregg_turn::action::Effect::Transfer { from: treasury, to: user, amount: 250 }),
            );
            editor.set_verdict(edit::validate(fb.forest()));
        }

        // Start the replay scrubber at the head of the live world's history.
        let replay_cursor = world.borrow().recorded_turns().len();
        // The ⏳ TIME tab's scrubber also starts at the live present (the head).
        let time_cursor = replay_cursor;

        // Boot the cap-first SHELL: open the privileged console surface (the
        // cockpit's own trusted root, run as the treasury/operator identity),
        // then open the three anchor cells as cap-confined cell-view surfaces so
        // the compositor boots into a LIVE multi-surface scene over real cells.
        let mut shell = Shell::new();
        let mut surface_caps = std::collections::HashMap::new();
        let console_cap = shell.open_console(treasury, "Master Console");
        let console_surface = console_cap.surface();
        surface_caps.insert(console_surface, console_cap);
        let mut service_surface = None;
        for (cell, name) in [(treasury, "Treasury"), (user, "User"), (service, "Service")] {
            let cap = shell.open_cell_view(cell, name);
            if cell == service {
                service_surface = Some(cap.surface());
            }
            surface_caps.insert(cap.surface(), cap);
        }
        // The AGENT-ACTIVITY surface: the service cell is the demo agent (it
        // holds a cap to the user cell — a real mandate — and commits cap-gated
        // turns in `demo_world`). Bind it as an agent surface so the Agent panel
        // renders its grounded-seam activity. Falls back to a fresh agent-view
        // surface id if the service surface somehow wasn't opened.
        let agent_surface = starbridge_v2::agent::AgentSurface::new(
            service_surface.unwrap_or(console_surface),
            service,
        );

        // The A1 EDITOR/BUFFER surface: a fresh dedicated cell backs the buffer
        // (its state slot carries the content digest; the cockpit holds the
        // WRITE cap the shell mints). Open it as a real shell surface so it
        // composites under the A0 verified scene like every other surface.
        let buffer_backing = world.borrow_mut().genesis_cell(0x5B, 0);
        let editor_buffer_cap = shell.open_cell_view(buffer_backing, "scratch.txt");
        surface_caps.insert(editor_buffer_cap.surface(), editor_buffer_cap.clone());
        let editor_buffer = BufferCell::new(
            editor_buffer_cap.surface(),
            buffer_backing,
            "scratch.txt",
            "// a cap-confined buffer — its digest rides a real cell.\n\
             // editing is free; COMMIT is a cap-gated verified turn.\n",
        );

        // M3 — THE INSPECTOR'S OWN VIEW CELL (the reflexive migration §3): the
        // moldable inspector's camera-aim (focus + present-idx) is self-hosted as a
        // REAL cell (the BufferCell two-tier split, generalized). A fresh dedicated
        // cell backs it; the draft is aimed at the treasury and committed once so the
        // witnessed (prior-frame) aim is populated. A re-focus mutates the free draft
        // and lands an occasional witnessed SetField commit (the §3.5 stream weight
        // class). The inspector is now itself inspectable (FocusTarget::ViewCell).
        let inspector_view_backing = world.borrow_mut().genesis_cell(0x5E, 0);
        let inspector_view = {
            let v = starbridge_v2::view_cell::ViewCell::focused(
                inspector_view_backing,
                "INSPECTOR",
                treasury,
            );
            // Land the initial aim so the witnessed state matches the boot draft.
            let _ = v.commit(&mut world.borrow_mut());
            v
        };

        // M3 WIDEN — THE WORKSPACE CELL (the §3.4 selector move): the cockpit's
        // active-tab selector is self-hosted as a REAL cell (the same two-tier split
        // as the inspector's view cell). A fresh dedicated cell backs it; the draft is
        // seeded to the boot tab (`Home` = index 0) and committed once so the witnessed
        // (prior-frame) selector is populated. A tab switch mutates the free draft
        // (`self.tab`) and lands an occasional witnessed `SetField` commit — the active
        // tab becomes a rewindable dregg-graph mutation, conserving nothing.
        let workspace_cell_backing = world.borrow_mut().genesis_cell(0x5F, 0);
        let workspace_cell = {
            let ws = starbridge_v2::view_cell::WorkspaceCell::new(
                workspace_cell_backing,
                Tab::Home.index(),
            );
            let _ = ws.commit(&mut world.borrow_mut());
            ws
        };

        // The POWERBOX (CapDesk) demo: birth a fresh CONFINED app-cell that holds
        // NO ambient authority (a freshly-launched app-as-cell), and seed the user
        // principal (the cockpit's own identity, `user`) with a held cap reaching
        // the `service` cell — so the powerbox picker is non-empty (the user has
        // SOMETHING to designate) and a grant demonstrates real attenuation away
        // from the held authority. The user genuinely holds this cap; the powerbox
        // can only ever offer the user's own authority (`mint_needs_held_factory`).
        let powerbox_app = world.borrow_mut().genesis_cell(0xA9, 0);
        // The user holds full (None) authority reaching `service` — the powerbox can
        // confer this or any narrower right, never wider.
        let _ = world.borrow_mut().genesis_grant_cap(&user, service);
        // …and reaching `treasury` too, so the WEB-OF-CELLS ⚡ "make interactive"
        // upgrade (a real powerbox grant over the transcluded SOURCE) lands on a cell
        // the user genuinely holds whatever the transclusion picks as its source among
        // the principal cells (the powerbox still REFUSES any source the user does not
        // hold — `mint_needs_held_factory` — so this broadens the demo's reach without
        // faking authority). Both caps are installed via the real genesis grant path.
        let _ = world.borrow_mut().genesis_grant_cap(&user, treasury);

        // The A1 TERMINAL surface: the SERVICE cell backs it — it holds a REAL
        // cap reaching the user cell (a genuine mandate), so a command targeting
        // the user is in-mandate (commits) and one targeting an out-of-reach cell
        // REFUSES (the ADOS tool-call seam, confined). Opened as a shell surface.
        let term_cap = shell.open_cell_view(service, "service-term");
        let terminal_surface = term_cap.surface();
        surface_caps.insert(terminal_surface, term_cap);
        let terminal = TerminalCell::new(terminal_surface, service, "service-term");

        // The A2 SWARM: service IS the coordinator (born holding a cap to user
        // in demo_world — its live mandate). User is worker-a (reachable from
        // service). Treasury is worker-b (NOT reachable from service, so the
        // swarm panel's cap-gate REFUSES any action targeting it — illustrating
        // the confined boundary). The swarm reads the real cap-graph.
        let swarm = {
            let w = world.borrow();
            Swarm::new(
                &w,
                [
                    (service, "coordinator"),
                    (user, "worker-a"),
                    (treasury, "worker-b (unreachable — the confinement boundary)"),
                ],
            )
        };

        // The LIVE NODE connection (`--node <url>`): wrap an HTTP client, open the
        // SSE receipt stream right away (the reader runs on its own thread and feeds
        // the pure parser; the cockpit drains the channel under `cx.notify()`), and
        // take one blocking snapshot for the initial reflections. All best-effort:
        // an unreachable node leaves the embedded image fully usable.
        let (live_node, live_stream, live_snapshot) = match node_url {
            Some(url) => {
                let ln = starbridge_v2::client::LiveNode::new(
                    starbridge_v2::client::NodeClient::http(url),
                );
                let stream = ln.connect_stream();
                let snapshot = ln.sync().ok();
                (Some(ln), stream, snapshot)
            }
            None => (None, None, None),
        };
        let live_feed = starbridge_v2::live_node::ReceiptFeed::new(256);

        // The attenuation dial's ceiling: the FIRST cap the `user` principal genuinely
        // holds (the constructor granted user→service + user→treasury via the real
        // genesis grant path). Computed here, before `world` is moved into the struct.
        let lane_dial = HeldCapability::all_for(&world.borrow(), user)
            .first()
            .map(AttenuationDial::over_held);

        // Seed the dynamics cursor at the live head so the first render does not
        // re-fold the genesis events whose cells `self.cells` already carries.
        let dynamics_cursor = world.borrow().dynamics().cursor();

        Self {
            world,
            cells,
            dynamics_cursor,
            present_memo: PresentMemo::new(),
            selection: Selection::Image,
            last_outcome: None,
            anchors,
            // BOOT into the warm landing PORTAL — the alive front door of the
            // live verified image (text-rich, self-describing). SHELL and the
            // other rooms are one click (or ⌘K) away.
            tab: Tab::Home,
            workspace_cell,
            debug_turn,
            breakpoints: vec![debug::Breakpoint::OnRefusal, debug::Breakpoint::OnConservationBreak],
            replay_cursor,
            replay_fork: None,
            time_cursor,
            meta_stack: MetaStack::new(),
            clerk,
            clerk_outcome: None,
            editor,
            shell,
            surface_caps,
            console_surface,
            frame_seq: 0,
            agent_surface,
            editor_buffer,
            editor_buffer_cap,
            terminal,
            swarm,
            // LAZY: the metered demo world + factory deploy + the slow proof-bearing
            // demo turns must NOT sit on the first-paint path. Booted on first SWARM
            // navigation / killer-demo verb (see `killer_demo()` + `set_tab`).
            killer_demo: None,
            killer_demo_lines: Vec::new(),
            pending_seed,
            palette: CommandPalette::new(),
            focus,
            live_node,
            live_stream,
            live_feed,
            live_snapshot,
            web_cells_opened: None,
            web_cells_viewer_rights: dregg_cell::AuthRequired::Either,
            web_cells_outcome: None,
            web_cells_upgraded: None,
            web_cells_transclusion_outcome: None,
            // WHAT-LINKS-HERE: focus the cockpit's own `user` principal at depth 2
            // (direct backlinks + one hop of backlinks-of-backlinks) so the panel
            // boots into a populated docuverse map rather than an empty pane. Boot as
            // ROOT (None) so the gated backlinks are visible; the toggle drops to
            // Signature to watch them fog.
            links_here_focus: None,
            links_here_depth: 2,
            links_here_viewer_rights: dregg_cell::AuthRequired::None,
            // THE DOCS EDITOR boots on a real document cell with a single seeded
            // sentence (a real cap-gated turn), so the panel opens on live content.
            doc_editor: starbridge_v2::doc_editor::DocEditor::new(),
            doc_outcome: None,
            powerbox_app: Some(powerbox_app),
            // Default to the narrow Signature tier so a click demonstrates real
            // attenuation away from the user's wider (None) held authority.
            powerbox_confer_rights: dregg_cell::AuthRequired::Signature,
            powerbox_outcome: None,
            // The boot-seeded demo app (above) is the FIRST entry — the launcher
            // appends a fresh confined app per "+ launch" press.
            launched_apps: Vec::new(),
            // The SIMULATE composer boots with the treasury as agent, the target
            // picker on the first cell, the effect picker on the first palette
            // entry, and a seeded example action (a small treasury→user transfer)
            // so the panel opens on a runnable what-if rather than an empty forest.
            sim_draft: {
                let [treasury, _service, user] = anchors;
                let mut d = starbridge_v2::simulate::IntentDraft::new(treasury);
                let ai = d.add_action(treasury);
                d.add_effect(
                    ai,
                    starbridge_v2::simulate::EffectKind::Transfer { to: user, amount: 250 },
                );
                d
            },
            sim_target_idx: 0,
            sim_effect_idx: 0,
            sim_outcome: None,
            sim_commit_banner: None,

            // THE MOLDABLE INSPECTOR boots focused on the treasury (a populated
            // presentation set: RawFields + Affordances + Provenance + Graph +
            // Lifecycle), on its first sub-tab, with an empty spotter box. The
            // focus/present-idx now ride `inspector_view` (the M3 view cell).
            inspector_view,
            inspector_reflexive: false,
            moldable_query: String::new(),
            moldable_lens: MoldableLens::Cell,

            // THE INSPECT→ACT loop boots on the treasury too.
            inspect_act_focus: Some(treasury),
            inspect_act_outcome: None,

            // THE WORKSPACE boots with a seeded conserving transfer draft so the
            // panel opens on a runnable doIt rather than an empty expression.
            workspace: {
                let mut ws = Workspace::new(treasury);
                ws.draft_mut().add_action(treasury);
                let ai = 0;
                ws.draft_mut().add_effect(
                    ai,
                    starbridge_v2::simulate::EffectKind::Transfer { to: user, amount: 250 },
                );
                ws
            },
            workspace_target_idx: 0,

            // THE LANES boot on the predicate composer, with a real non-vacuous
            // composite (a solvency floor), a turn-builder seeded with a conserving
            // transfer, the attenuation dial over a cap the user genuinely holds (the
            // constructor granted user→service + user→treasury), and a macaroon loop.
            lane_idx: 0,
            lane_composite: Composite::Leaf(Atom::BalanceGte { min: 100 }),
            lane_turn: {
                let mut g = CommittingTurnGadget::new(treasury);
                g.action_with(
                    user,
                    starbridge_v2::simulate::EffectKind::Transfer { to: user, amount: 250 },
                );
                g
            },
            lane_dial,
            lane_token: TokenLoopGadget::new([0x5Au8; 64], "dregg/service", [0x11u8; 32]),
            lane_outcome: None,
            // The ⤳ SHARE surface starts empty — the operator captures the focused
            // view to open the editor. The preview defaults to the WIDE recipient.
            share_editor: None,
            share_artifacts: Vec::new(),
            share_preview_wide: true,
            share_outcome: None,
        }
    }

    fn refresh_cells(&mut self) {
        self.cells = sorted_cells(&self.world.borrow());
    }

    /// M2 — THE DELTA FOLD. Pull every dynamics event since the last render and
    /// route each into per-slice invalidation (the dirty-set), then advance the
    /// cursor to the live head. This is the producer↔consumer join: the touched
    /// cell, alone, re-lights its projection (`EFFICIENCY-WELD-PLAN.md` §2.1).
    fn fold_dynamics(&mut self) {
        let new = {
            let w = self.world.borrow();
            let from = self.dynamics_cursor;
            // Clone the slice out so we drop the world borrow before mutating self.
            let slice = w.dynamics().since(from).to_vec();
            self.dynamics_cursor = w.dynamics().cursor();
            slice
        };
        for ev in &new {
            self.invalidate_for(ev);
        }
    }

    /// The §2.2 variant→invalidation table: what each `WorldEvent` dirties.
    fn invalidate_for(&mut self, ev: &dynamics::WorldEvent) {
        use dynamics::WorldEvent as E;
        match ev {
            // A cell was born. ZERO is the `CreateCell`/`FromFactory` sentinel (the
            // real id isn't known at emit): we don't know which cell appeared, so
            // refresh `self.cells` from the ledger (the bounded full-rescan case,
            // once per cell-creating turn) and drop the whole projection cache.
            E::CellBorn { cell, .. } => {
                if *cell == CellId::ZERO {
                    self.refresh_cells();
                    self.present_memo.invalidate_all();
                } else {
                    // A real-id birth (genesis seed): keep cells sorted-correct and
                    // drop any (now-resolvable) cached projection for it.
                    if !self.cells.contains(cell) {
                        self.cells.push(*cell);
                        self.cells.sort_by(|a, b| a.as_bytes().cmp(b.as_bytes()));
                    }
                    self.present_memo.invalidate_cell(*cell);
                }
            }
            E::CellDestroyed { cell } => {
                self.cells.retain(|c| c != cell);
                self.present_memo.invalidate_cell(*cell);
            }
            E::BalanceFlowed { cell, .. }
            | E::FieldSet { cell, .. }
            | E::CellMutated { cell }
            | E::CellSealed { cell }
            | E::CellUnsealed { cell }
            | E::Burned { cell, .. }
            | E::EventEmitted { cell, .. } => {
                self.present_memo.invalidate_cell(*cell);
            }
            E::SurfaceDamaged { cell, owner, .. } => {
                self.present_memo.invalidate_cell(*cell);
                self.present_memo.invalidate_cell(*owner);
            }
            // Cap-edge deltas reach OTHER cells' affordance badges (viewer-non-
            // local, §4.2): conservatively drop the whole affordance cache.
            E::CapabilityGranted { from, to } => {
                self.present_memo.invalidate_cell(*from);
                self.present_memo.invalidate_cell(*to);
                self.present_memo.invalidate_affordances_all();
            }
            E::CapabilityRevoked { cell, .. } => {
                self.present_memo.invalidate_cell(*cell);
                self.present_memo.invalidate_affordances_all();
            }
            // A height tick carries no cell-specific invalidation of its own; the
            // per-cell events in the SAME commit batch carry the actual deltas, and
            // `rail_header` re-reads the root via the M1 memo (height bumped).
            E::TurnCommitted { .. } => {}
            // Nothing moved — only the outcome banner (already a Rust field).
            E::TurnRejected { .. } => {}
            // A turn was STAGED while the world is suspended (the meta-debug
            // Suspend gate). The head is frozen — nothing in the ledger moved —
            // but the staged continuation grew, which a `DebugFrame` view reads
            // off the world directly. Drop any cached meta-frame projection so a
            // re-present picks up the new pending count.
            E::TurnQueued { .. } => {}
        }
    }

    /// Whether there are demo seed turns still waiting to be committed (drives the
    /// post-paint async seeding loop in `main::run_window`).
    pub fn has_pending_seed(&self) -> bool {
        self.pending_seed.as_ref().is_some_and(|s| !s.is_done())
    }

    /// **Commit the NEXT demo seed turn** against the live world (the real executor),
    /// refresh the cell rail + the live banner, and `cx.notify()` so the new cell/
    /// receipt paints immediately. Returns `true` if MORE seed turns remain (the
    /// caller loops, yielding between calls so the UI breathes), `false` once the
    /// image is fully seeded.
    ///
    /// This is the paint-friendly counterpart to `demo_world`'s eager seeding: the
    /// SAME five verified turns, run one-per-yield AFTER the window is already up,
    /// so the cockpit was alive instantly and the demo provenance fills in live.
    pub fn seed_next_demo_turn(&mut self, cx: &mut Context<Self>) -> bool {
        let Some(seed) = self.pending_seed.as_mut() else {
            return false;
        };
        // Commit exactly one real turn against the shared world.
        let label = {
            let mut w = self.world.borrow_mut();
            seed.next(&mut w)
        };
        let more = !self.pending_seed.as_ref().unwrap().is_done();
        if let Some(label) = label {
            // A live status line so the operator SEES the image populating.
            let remaining = self.pending_seed.as_ref().unwrap().remaining();
            self.last_outcome = Some(if more {
                format!("seeding the live image — {label} ({remaining} more)")
            } else {
                format!("seeding the live image — {label} (demo image ready)")
            });
            self.refresh_cells();
        }
        if !more {
            // Fully seeded — drop the plan.
            self.pending_seed = None;
        }
        cx.notify();
        more
    }

    // --- the verbs (each runs the REAL embedded executor) -------------------

    fn run_demo_transfer(&mut self, cx: &mut Context<Self>) {
        let [treasury, _service, user] = self.anchors;
        let outcome = {
            let mut w = self.world.borrow_mut();
            let turn = w.turn(treasury, vec![world::transfer(treasury, user, 1_000)]);
            w.commit_turn(turn)
        };
        self.note_outcome(outcome);
        self.refresh_cells();
        cx.notify();
    }

    fn run_demo_grant(&mut self, cx: &mut Context<Self>) {
        let [_treasury, service, user] = self.anchors;
        // Re-grant the service's user-cap to a fresh slot (legitimate).
        let outcome = {
            let mut w = self.world.borrow_mut();
            let slot = w
                .ledger()
                .get(&service)
                .map(|c| c.capabilities.len() as u32)
                .unwrap_or(0);
            let turn = w.turn(service, vec![world::grant_capability(service, service, user, slot)]);
            w.commit_turn(turn)
        };
        self.note_outcome(outcome);
        self.refresh_cells();
        cx.notify();
    }

    fn run_demo_create(&mut self, cx: &mut Context<Self>) {
        let [treasury, _service, _user] = self.anchors;
        let seed = (self.world.borrow().cell_count() as u8).wrapping_add(0x40);
        let outcome = {
            let mut w = self.world.borrow_mut();
            let turn = w.turn(treasury, vec![world::create_cell(seed)]);
            w.commit_turn(turn)
        };
        self.note_outcome(outcome);
        self.refresh_cells();
        cx.notify();
    }

    /// **LAUNCH a confined app at RUNTIME** — the powerbox's missing first half.
    ///
    /// The boot-seeded `powerbox_app` is one demo app; this spawns an ARBITRARY
    /// confined app on demand. It calls the real [`AppLauncher::launch`]: births a
    /// fresh app-cell into the live world holding NO ambient authority (an empty
    /// c-list — a genuine confined app-as-cell), records it, and makes IT the app
    /// whose [`CapabilityRequest`] the powerbox panel now mediates (`powerbox_app`
    /// points at the freshly launched cell). The request then routes through the
    /// EXISTING [`Powerbox::present`] the panel already renders — the launcher
    /// supplies the confined requester; the powerbox supplies the grant. Re-runnable:
    /// each press births a distinct app and switches the panel to it.
    fn run_launch_confined_app(&mut self, cx: &mut Context<Self>) {
        use starbridge_v2::powerbox::AppLauncher;
        let n = self.launched_apps.len() + 1;
        let launched = {
            let mut w = self.world.borrow_mut();
            AppLauncher::launch(
                &mut w,
                format!("launched-app-{n}"),
                "this app launched at runtime and needs to reach one peer/resource — designate exactly one",
                dregg_cell::AuthRequired::None,
            )
        };
        // The freshly launched confined app is now the powerbox's current requester:
        // its standing request is routed through the existing Powerbox::present the
        // panel renders. Switch to the POWERBOX tab so the designation flow is in view.
        self.powerbox_app = Some(launched.app_cell);
        self.powerbox_outcome = Some(format!(
            "launched: {} — a fresh CONFINED app (no ambient authority); it can only ASK. Designate a held target below.",
            launched.label()
        ));
        self.launched_apps.push(launched);
        self.tab = Tab::Powerbox;
        self.refresh_cells();
        cx.notify();
    }

    fn run_over_grant(&mut self, cx: &mut Context<Self>) {
        // Demonstrate the ocap guarantee FIRING: an illegitimate grant.
        let [treasury, _service, user] = self.anchors;
        let outcome = {
            let mut w = self.world.borrow_mut();
            // treasury holds no cap to user → no-amplification rejects this.
            let turn = w.turn(treasury, vec![world::grant_capability(treasury, treasury, user, 0)]);
            w.commit_turn(turn)
        };
        self.note_outcome(outcome);
        self.refresh_cells();
        cx.notify();
    }

    /// Birth a fresh cell and SEAL it in one demo flow — shows the lifecycle
    /// verb running through the real executor (seal must target the acting cell;
    /// we genesis the cell, then seal it). Re-runnable: each press seals a new
    /// fresh cell so the lifecycle column grows.
    fn run_seal(&mut self, cx: &mut Context<Self>) {
        let outcome = {
            let mut w = self.world.borrow_mut();
            let seed = (w.cell_count() as u8).wrapping_add(0x70);
            let id = w.genesis_cell(seed, 0);
            let turn = w.turn(id, vec![world::seal(id, "operator seal demo")]);
            w.commit_turn(turn)
        };
        self.note_outcome(outcome);
        self.refresh_cells();
        cx.notify();
    }

    /// Burn value from the treasury — supply provably reduced, no credit. The
    /// receipt's `was_burn` flag is bound into its hash (the cockpit's proof
    /// view surfaces it).
    fn run_burn(&mut self, cx: &mut Context<Self>) {
        let [treasury, _service, _user] = self.anchors;
        let outcome = {
            let mut w = self.world.borrow_mut();
            let turn = w.turn(treasury, vec![world::burn(treasury, 1_000)]);
            w.commit_turn(turn)
        };
        self.note_outcome(outcome);
        self.refresh_cells();
        cx.notify();
    }

    /// Compose a MULTI-ACTION turn — treasury pays BOTH service and user in one
    /// atomic verified turn (two sibling actions, one receipt). Demonstrates the
    /// call-forest composer driving the real executor.
    fn run_compose_multi(&mut self, cx: &mut Context<Self>) {
        let [treasury, service, user] = self.anchors;
        let outcome = {
            let mut w = self.world.borrow_mut();
            let turn = w.forest_turn(
                treasury,
                vec![
                    (treasury, vec![world::transfer(treasury, service, 500)]),
                    (treasury, vec![world::transfer(treasury, user, 750)]),
                ],
            );
            w.commit_turn(turn)
        };
        self.note_outcome(outcome);
        self.refresh_cells();
        cx.notify();
    }

    // --- the WHAT-IF / SIMULATE composer verbs ------------------------------
    //
    // These build an `IntentDraft` (compose any intent over any cell), run it
    // through a FORKED throwaway world to PREDICT the outcome (the real executor,
    // live world untouched), then — on commit — fire the SAME turn for real.

    /// Cycle the SIMULATE composer's AGENT through the live cells (the cell that
    /// authorizes + submits the composed turn). A fresh draft is started on the new
    /// agent (the prior forest is cleared, since its actions referenced the old
    /// agent's intent); the prediction is invalidated.
    fn sim_cycle_agent(&mut self, cx: &mut Context<Self>) {
        let cells = &self.cells;
        if cells.is_empty() {
            return;
        }
        let cur = cells.iter().position(|c| *c == self.sim_draft.agent).unwrap_or(0);
        let next = cells[(cur + 1) % cells.len()];
        self.sim_draft = starbridge_v2::simulate::IntentDraft::new(next);
        self.sim_outcome = None;
        self.sim_commit_banner = None;
        cx.notify();
    }

    /// Cycle the TARGET cell the next added effect will act on (the action's
    /// acting cell). Wraps over the live cells.
    fn sim_cycle_target(&mut self, cx: &mut Context<Self>) {
        let cells = &self.cells;
        if cells.is_empty() {
            return;
        }
        self.sim_target_idx = (self.sim_target_idx + 1) % cells.len();
        cx.notify();
    }

    /// Cycle the EFFECT KIND the next "+ add" will append, over the full palette
    /// (the studio-parity coverage — every single-custody-simulable effect).
    fn sim_cycle_effect(&mut self, cx: &mut Context<Self>) {
        self.sim_effect_idx = (self.sim_effect_idx + 1) % self.sim_effect_palette().len();
        cx.notify();
    }

    /// The effect palette, with the CURRENT target/peer cells filled in (so the
    /// templates reference real live cells). The "+ add" verb appends the entry at
    /// `sim_effect_idx`. Order is the coverage display order.
    fn sim_effect_palette(&self) -> Vec<starbridge_v2::simulate::EffectKind> {
        use starbridge_v2::simulate::EffectKind as E;
        let cells = &self.cells;
        let target = cells.get(self.sim_target_idx).copied().unwrap_or(self.sim_draft.agent);
        // A "peer" distinct from the target where possible (for transfer/grant dests).
        let peer = cells
            .iter()
            .find(|c| **c != target)
            .copied()
            .unwrap_or(target);
        vec![
            E::Transfer { to: peer, amount: 250 },
            E::GrantCapability { to: peer, target, slot: 0 },
            E::RevokeCapability { slot: 0 },
            E::EmitEvent { topic: "what-if".into() },
            E::IncrementNonce,
            E::CreateCell { seed: 0x9A },
            E::SetField { index: 0, value: [7u8; 32] },
            E::SetPermissionsOpen,
            E::MakeSovereign,
            E::Seal { reason: "what-if seal".into() },
            E::Unseal,
            E::Destroy,
            E::Burn { amount: 1_000 },
        ]
    }

    /// Append the currently-picked effect (on the currently-picked target) to the
    /// draft as a new action root. Invalidates the prior prediction.
    fn sim_add_effect(&mut self, cx: &mut Context<Self>) {
        let cells = &self.cells;
        let Some(target) = cells.get(self.sim_target_idx).copied() else {
            return;
        };
        let palette = self.sim_effect_palette();
        let Some(effect) = palette.get(self.sim_effect_idx).cloned() else {
            return;
        };
        let ai = self.sim_draft.add_action(target);
        self.sim_draft.add_effect(ai, effect);
        self.sim_outcome = None;
        self.sim_commit_banner = None;
        cx.notify();
    }

    /// Drop the most-recently-added action from the draft (the panel's undo).
    fn sim_pop_action(&mut self, cx: &mut Context<Self>) {
        let n = self.sim_draft.actions.len();
        if n > 0 {
            self.sim_draft.remove_action(n - 1);
        }
        self.sim_outcome = None;
        self.sim_commit_banner = None;
        cx.notify();
    }

    /// Clear the draft to an empty forest on the same agent.
    fn sim_clear(&mut self, cx: &mut Context<Self>) {
        self.sim_draft = starbridge_v2::simulate::IntentDraft::new(self.sim_draft.agent);
        self.sim_outcome = None;
        self.sim_commit_banner = None;
        cx.notify();
    }

    /// **SIMULATE the draft** — predict its consequences in a forked throwaway
    /// world (the real executor, live world UNTOUCHED). Stores the [`SimOutcome`]
    /// the panel renders (the predicted post-state + receipt, or the refusal).
    fn sim_run(&mut self, cx: &mut Context<Self>) {
        let outcome = {
            let w = self.world.borrow();
            starbridge_v2::simulate::simulate(&w, &self.sim_draft)
        };
        self.sim_outcome = Some(outcome);
        self.sim_commit_banner = None;
        cx.notify();
    }

    /// **COMMIT the draft for real** — run the IDENTICAL turn on the LIVE world.
    /// Only meaningful after a SIMULATE that predicted a commit; the button is
    /// disabled otherwise. Surfaces the real executor's verdict (which matches the
    /// prediction) + refreshes the image.
    fn sim_commit(&mut self, cx: &mut Context<Self>) {
        // Only commit a draft the prediction said would commit (the panel disables
        // the button otherwise; this guards the keyboard/palette path too).
        let predicted_ok = matches!(
            self.sim_outcome,
            Some(starbridge_v2::simulate::SimOutcome::Predicted { .. })
        );
        if !predicted_ok {
            self.sim_commit_banner =
                Some("SIMULATE first — commit is enabled only after a predicted-commit".into());
            cx.notify();
            return;
        }
        let outcome = {
            let mut w = self.world.borrow_mut();
            starbridge_v2::simulate::commit(&mut w, &self.sim_draft)
        };
        self.sim_commit_banner = Some(match &outcome {
            CommitOutcome::Committed { receipt, events } => format!(
                "COMMITTED for real — {} action(s), {} computrons, {} dynamics event(s). \
                 The prediction held.",
                receipt.action_count,
                receipt.computrons_used,
                events.len()
            ),
            CommitOutcome::Rejected { reason, at_action } => {
                format!("REJECTED by the live executor: {reason} @ {at_action:?}")
            }
            // The world is suspended (meta-debug Suspend gate): the turn was staged,
            // not run, so the prediction is neither confirmed nor refused — it waits
            // on resume. Surface the halt honestly rather than claim an outcome.
            CommitOutcome::Queued { agent } => {
                format!("QUEUED — world suspended; the staged turn from {} commits on resume", world::short(agent))
            }
        });
        // The committed turn changed the image; also drop the stale prediction (the
        // pre-state it predicted against is now spent).
        self.sim_outcome = None;
        self.note_outcome(outcome);
        self.refresh_cells();
        cx.notify();
    }

    // --- the CIPHERCLERK action loop (real macaroons) -----------------------
    //
    // These drive the REAL `AgentCipherclerk` via the `cipherclerk` action
    // layer (mint → attenuate → delegate → discharge). The demo acts on the two
    // seeded identities (alice mints/attenuates/delegates; bob receives) and the
    // "dns" service, so the operator can watch the wallet + delegation vault
    // grow and see the discharge verdict.

    fn run_clerk_mint(&mut self, cx: &mut Context<Self>) {
        let out = self.clerk.mint("alice", "dns");
        self.clerk_outcome = Some(out);
        cx.notify();
    }

    fn run_clerk_attenuate(&mut self, cx: &mut Context<Self>) {
        // Confine alice's dns root to read-only with a far-future expiry.
        let out = self.clerk.attenuate_latest("alice", "dns", "r", Some(4_000_000_000));
        self.clerk_outcome = Some(out);
        cx.notify();
    }

    fn run_clerk_delegate(&mut self, cx: &mut Context<Self>) {
        // Hand a dns/read capability to bob as a real signed envelope.
        let out = self.clerk.delegate_to("alice", "bob", "dns", "r");
        self.clerk_outcome = Some(out);
        cx.notify();
    }

    fn run_clerk_discharge(&mut self, cx: &mut Context<Self>) {
        // Discharge alice's dns token against an atomic 'r' (read) request now.
        // (The macaroon action vocabulary is the atomic letters r/w/c/d/C.)
        let now = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_secs() as i64)
            .unwrap_or(0);
        let out = self.clerk.discharge("alice", "dns", "r", now);
        self.clerk_outcome = Some(out);
        cx.notify();
    }

    // --- the A1 EDITOR/BUFFER surface ops (cap-gated edits) ------------------
    //
    // Editing the buffer's text is free (an in-memory doc edit); LANDING it is a
    // cap-gated verified turn — the cockpit presents the WRITE cap and the
    // backing cell's digest advances (a real receipt). A read-only buffer would
    // refuse — the no-amplification rule at the editor.

    /// Type a line into the editor buffer (free, in-memory) — the operator can
    /// watch the doc become DIRTY (its digest now differs from the committed one).
    fn buffer_type_demo(&mut self, cx: &mut Context<Self>) {
        let stamp = self.world.borrow().height();
        self.editor_buffer
            .doc_mut()
            .insert(&format!("edit @ h{stamp}\n"));
        self.last_outcome = Some(
            "buffer: typed a line (in-memory — the doc is now DIRTY until a cap-gated commit)"
                .to_string(),
        );
        self.tab = Tab::Buffer;
        cx.notify();
    }

    /// COMMIT the editor buffer — write its digest into the backing cell through
    /// a REAL verified turn (cap-gated; the cockpit presents the WRITE cap).
    fn buffer_commit(&mut self, cx: &mut Context<Self>) {
        let cap = self.editor_buffer_cap.clone();
        let result = {
            let mut w = self.world.borrow_mut();
            self.editor_buffer.commit(&mut w, &cap)
        };
        self.last_outcome = Some(match result {
            Ok(rev) => format!(
                "buffer: COMMITTED — digest written to the backing cell as a verified turn (revision {rev})"
            ),
            Err(e) => format!("buffer: commit REFUSED — {}", e.explain()),
        });
        self.refresh_cells();
        self.tab = Tab::Buffer;
        cx.notify();
    }

    /// Attempt to COMMIT through a READ-ONLY mirror — the no-amplification rule
    /// firing at the editor. The cockpit narrows its write cap to a read-only
    /// (Signature) mirror via a REAL GrantCapability share, then tries to commit
    /// through it: the buffer-cap gate REFUSES (a read-only buffer cannot write).
    fn buffer_readonly_write_demo(&mut self, cx: &mut Context<Self>) {
        let cap = self.editor_buffer_cap.clone();
        // Narrow to a read-only mirror through the real executor (None → Signature).
        let mirror = match self.shell.share(&cap, /*peer app*/ 0x4E0, dregg_cell::AuthRequired::Signature) {
            Ok(m) => m,
            Err(e) => {
                self.last_outcome = Some(format!("buffer: could not make a read-only mirror — {}", shell_err(&e)));
                cx.notify();
                return;
            }
        };
        self.surface_caps.insert(mirror.surface(), mirror.clone());
        // A read-only buffer rendered into the mirror's surface.
        let ro_buffer = BufferCell::new(
            mirror.surface(),
            self.editor_buffer.backing(),
            "scratch.txt (read-only mirror)",
            self.editor_buffer.doc().text(),
        );
        let result = {
            let mut w = self.world.borrow_mut();
            ro_buffer.commit(&mut w, &mirror)
        };
        self.last_outcome = Some(match result {
            Ok(_) => "buffer: read-only write UNEXPECTEDLY committed (should have refused!)".to_string(),
            Err(e) => format!("buffer: ⚠ read-only write REFUSED — {} (no-amplification at the editor)", e.explain()),
        });
        self.tab = Tab::Buffer;
        cx.notify();
    }

    // --- the A1 TERMINAL surface ops (the ADOS tool-call seam) ---------------
    //
    // A command is cap-gated on the terminal-cell's c-list: an in-mandate target
    // COMMITS (its receipt is the output); an out-of-mandate one REFUSES. This is
    // the agent's Bash confined to its mandate, made a surface.

    /// Run an IN-MANDATE command — the service terminal-cell holds a cap reaching
    /// the user cell, so a transfer to the user COMMITS (its receipt is the output).
    fn terminal_run_in_mandate(&mut self, cx: &mut Context<Self>) {
        let [_treasury, _service, user] = self.anchors;
        let line = {
            let mut w = self.world.borrow_mut();
            self.terminal.run(&mut w, Command::Transfer { target: user, amount: 100 })
        };
        self.last_outcome = Some(match line {
            Ok(l) => format!("terminal: command COMMITTED — {} (receipt is the output)", l.result),
            Err(e) => format!("terminal: command REFUSED — {}", e.explain()),
        });
        self.refresh_cells();
        self.tab = Tab::Terminal;
        cx.notify();
    }

    /// Run an OUT-OF-MANDATE command — target a cell the terminal-cell holds NO
    /// cap for; the command cap-gate REFUSES it (the agent's Bash confined). Uses
    /// the treasury (the service holds no cap reaching it).
    fn terminal_run_out_of_mandate(&mut self, cx: &mut Context<Self>) {
        let [treasury, _service, _user] = self.anchors;
        let line = {
            let mut w = self.world.borrow_mut();
            self.terminal.run(&mut w, Command::Transfer { target: treasury, amount: 1 })
        };
        self.last_outcome = Some(match line {
            Ok(_) => "terminal: out-of-mandate command UNEXPECTEDLY committed (should have refused!)".to_string(),
            Err(e) => format!("terminal: ⚠ command REFUSED — {} (cap-gate, BEFORE any turn)", e.explain()),
        });
        self.tab = Tab::Terminal;
        cx.notify();
    }

    // --- the A2 SWARM surface ops (notify-edge-routed cap-coordination) ------

    /// Swarm action: coordinator EMITS a notify event targeting worker-a.
    /// This is the grounded seam: the emit is a cap-gated turn; the
    /// `NotifyEdge` lands in worker-a's inbox (async, NOT a joint turn).
    /// Swarm layout: service = coordinator (cap to user), user = worker-a.
    fn swarm_coordinator_emit_a(&mut self, cx: &mut Context<Self>) {
        let [_treasury, coord, worker_a] = self.anchors; // service=coord, user=worker-a
        let outcome = {
            let mut w = self.world.borrow_mut();
            self.swarm.run(&mut w, coord, vec![world::emit_event(worker_a, "task/go", vec![])])
        };
        self.last_outcome = Some(match &outcome {
            Ok(ao) => format!(
                "swarm: coordinator emitted task/go → worker-a (receipt {}) — {} notify edge(s) deposited",
                ao.receipt_hash.map(|h| reflect::short_hex(&h)).unwrap_or_default(),
                ao.notify_edges.len(),
            ),
            Err(e) => format!("swarm: REFUSED — {}", e.label()),
        });
        self.refresh_cells();
        self.tab = Tab::Swarm;
        cx.notify();
    }

    /// Swarm action: worker-a DRAINS its pending notification (its own async ack turn).
    /// This is a wholly independent turn from the coordinator's emit — different
    /// receipt, different height, different provenance. The async model at work.
    fn swarm_worker_a_drain(&mut self, cx: &mut Context<Self>) {
        let [_treasury, _coord, worker_a] = self.anchors; // user=worker-a
        let outcome = {
            let mut w = self.world.borrow_mut();
            self.swarm.drain_notify(&mut w, worker_a)
        };
        self.last_outcome = Some(match outcome {
            Ok(receipt) => format!(
                "swarm: worker-a DRAINED its notify inbox (ack receipt {}) — async, separate from sender's turn",
                reflect::short_hex(&receipt),
            ),
            Err(e) => format!("swarm: drain REFUSED — {}", e.label()),
        });
        self.refresh_cells();
        self.tab = Tab::Swarm;
        cx.notify();
    }

    /// Swarm action: coordinator (service) sends value to worker-a (user) AND emits
    /// a wake to worker-a, in ONE multi-effect turn. One seam, two effects, real receipt.
    /// (worker-b = treasury = unreachable from service; transfer to treasury would REFUSE.)
    fn swarm_coordinator_transfer_and_wake(&mut self, cx: &mut Context<Self>) {
        let [_treasury, coord, worker_a] = self.anchors; // service=coord, user=worker-a
        let outcome = {
            let mut w = self.world.borrow_mut();
            self.swarm.run(
                &mut w,
                coord,
                vec![
                    world::transfer(coord, worker_a, 500),
                    world::emit_event(worker_a, "task/done", vec![]),
                ],
            )
        };
        self.last_outcome = Some(match &outcome {
            Ok(ao) => format!(
                "swarm: coordinator transferred 500 + woke worker-a (receipt {}) — {} notify edge(s)",
                ao.receipt_hash.map(|h| reflect::short_hex(&h)).unwrap_or_default(),
                ao.notify_edges.len(),
            ),
            Err(e) => format!("swarm: REFUSED — {}", e.label()),
        });
        self.refresh_cells();
        self.tab = Tab::Swarm;
        cx.notify();
    }

    // --- the four-surface KILLER DEMO (N5) live driver ----------------------

    /// **Advance the killer demo by ONE frame** — the SWARM-tab "next frame" button.
    /// Each press runs the next step of the headline script (mint → agent turn →
    /// notify → drain → over-grant REFUSAL → over-spend REFUSAL) through the demo's
    /// OWN embedded verified world, appending the frame's render line to the strip.
    /// When the script is complete, the button reports it (and the operator can
    /// reset to replay).
    /// The killer demo, BOOTED ON FIRST ACCESS. Building it constructs a metered
    /// verified world + deploys the mint factory; that (and its slow proof-bearing
    /// turns) is exactly what we keep off the first-paint path — so the demo is
    /// `None` until the operator first reaches the SWARM tab or a killer-demo verb,
    /// at which point this materializes it. Every later access reuses the same one.
    fn killer_demo(&mut self) -> &mut HeadlineDemo {
        self.killer_demo.get_or_insert_with(HeadlineDemo::boot)
    }

    fn killer_demo_advance(&mut self, cx: &mut Context<Self>) {
        if self.killer_demo().is_complete() {
            self.last_outcome =
                Some("killer demo: the script is complete — reset to replay it.".to_string());
        } else if let Some(line) = self.killer_demo().advance() {
            self.killer_demo_lines.push(line.clone());
            // The trimmed first line of the frame, for the outcome banner.
            let banner = line.lines().next().unwrap_or(&line).trim().to_string();
            self.last_outcome = Some(format!("killer demo: {banner}"));
        }
        self.tab = Tab::Swarm;
        cx.notify();
    }

    /// **Run the WHOLE killer demo at once** — the SWARM-tab "run all" button. Drives
    /// the full four-frame + dual-refusal script and reports the verdict (the
    /// `--headless` self-check, in the cockpit). Captures every frame line into the
    /// strip so the operator can read the four frames + both refusals.
    fn killer_demo_run_all(&mut self, cx: &mut Context<Self>) {
        // Reset to a fresh world so "run all" is a clean replay from frame 0.
        self.killer_demo().reset();
        self.killer_demo_lines.clear();
        while let Some(line) = self.killer_demo().advance() {
            self.killer_demo_lines.push(line);
            if self.killer_demo().is_complete() {
                break;
            }
        }
        self.last_outcome = Some(if self.killer_demo().contract_holds() {
            "killer demo ✓ — four frames committed, two distinct handoff receipts, \
             BOTH refusals fired fail-closed. (pg step 5 deferred.)"
                .to_string()
        } else {
            "killer demo ✗ — the headline contract did NOT hold (a regression).".to_string()
        });
        self.tab = Tab::Swarm;
        cx.notify();
    }

    /// **The pixel-layer OVER-SHARE refusal** — the SWARM-tab "⚠ over-share at the
    /// glass" button: the THIRD register of the same no-amplification law. Opens the
    /// demo's minted budget cell as a cap-confined surface (in the cockpit's live
    /// shell), shares it READ-ONLY, then tries to promote it to WRITABLE — the real
    /// executor REJECTS the widening (`DelegationDenied`), surfaced as `⚠ over-share`
    /// at the PIXEL layer. Requires the demo to have MINTED its token cell (frame 1).
    fn killer_demo_over_share(&mut self, cx: &mut Context<Self>) {
        // Ensure the demo is booted, then drive it. We can't go through the
        // `killer_demo()` accessor here (it would hold a &mut borrow of `self`
        // across the `&mut self.shell` arg); boot it, then reach the now-`Some`
        // field directly so `shell` is a disjoint borrow.
        let _ = self.killer_demo();
        let demo = self.killer_demo.as_mut().expect("just booted");
        let result = demo.refuse_over_share(&mut self.shell);
        let line = match result {
            Ok(reason) => format!("killer demo: {reason}"),
            Err(why) => format!("killer demo: over-share path — {why}"),
        };
        self.killer_demo_lines.push(line.clone());
        self.last_outcome = Some(line);
        self.tab = Tab::Swarm;
        cx.notify();
    }

    /// **Reset the killer demo** to a fresh world at frame 0 (the SWARM-tab "reset"
    /// button) so the operator can replay the script from the start.
    fn killer_demo_reset(&mut self, cx: &mut Context<Self>) {
        self.killer_demo().reset();
        self.killer_demo_lines.clear();
        self.last_outcome = Some("killer demo: reset to frame 0 — ready to replay.".to_string());
        self.tab = Tab::Swarm;
        cx.notify();
    }

    // --- replay scrubber + debugger retarget (palette-drivable) -------------

    fn replay_step_back(&mut self, cx: &mut Context<Self>) {
        self.replay_cursor = self.replay_cursor.saturating_sub(1);
        cx.notify();
    }

    fn replay_step_forward(&mut self, cx: &mut Context<Self>) {
        let len = self.world.borrow().recorded_turns().len();
        self.replay_cursor = (self.replay_cursor + 1).min(len);
        cx.notify();
    }

    fn replay_to_genesis(&mut self, cx: &mut Context<Self>) {
        self.replay_cursor = 0;
        cx.notify();
    }

    fn replay_to_head(&mut self, cx: &mut Context<Self>) {
        self.replay_cursor = self.world.borrow().recorded_turns().len();
        cx.notify();
    }

    /// Pin a what-if FORK at the current scrubber cursor: re-run the cursor's
    /// real turn as the "alternate" (a no-op divergence baseline) so the panel
    /// shows the fork machinery live. (A richer alt-turn editor is a follow-on;
    /// this proves the verified-fork path through the palette.)
    fn replay_fork_here(&mut self, cx: &mut Context<Self>) {
        let w = self.world.borrow();
        let history = w.recorded_turns();
        let k = self.replay_cursor.min(history.len());
        // Use the treasury anchor for a representative alternate transfer.
        let [treasury, _service, user] = self.anchors;
        // A small alternate transfer the branch point can apply.
        let alt = world::bare_turn(
            treasury,
            history
                .replay_to(k)
                .ok()
                .and_then(|l| l.get(&treasury).map(|c| c.state.nonce()))
                .unwrap_or(0),
            vec![world::transfer(treasury, user, 1)],
        );
        match history.fork_at(k, alt) {
            Ok(fork) => {
                drop(w);
                self.replay_fork = Some(fork);
            }
            Err(_) => {
                drop(w);
                self.replay_fork = None;
            }
        }
        cx.notify();
    }

    fn replay_clear_fork(&mut self, cx: &mut Context<Self>) {
        self.replay_fork = None;
        cx.notify();
    }

    /// Retarget the debugger to a transfer FROM the currently-selected cell (so
    /// the operator can step any cell's outgoing turn, not just the seeded one).
    fn debug_retarget_selected(&mut self, cx: &mut Context<Self>) {
        if let Selection::Cell(id) = self.selection {
            let [_t, _s, user] = self.anchors;
            // Target = the selected cell; pay a token amount to `user` so there
            // is an effect to step (the debugger re-executes faithfully).
            let to = if user == id { self.anchors[0] } else { user };
            self.debug_turn = self.world.borrow().turn(id, vec![world::transfer(id, to, 100)]);
            self.tab = Tab::Debugger;
            cx.notify();
        } else {
            self.last_outcome = Some("debugger retarget: select a cell first".to_string());
            cx.notify();
        }
    }

    // --- the cap-first SHELL ops (each routes through the CAP-GATED shell) ---
    //
    // The cockpit IS the operator: it holds every surface's cap in `surface_caps`.
    // But it can ONLY drive a surface by presenting that cap to the shell's
    // gated API — so the window manager's ocap discipline is demonstrated, not
    // bypassed. (A window op with no held cap simply has nothing to present and
    // is refused — exactly the no-ambient-authority property.)

    /// Open the currently-selected cell as a new cap-confined SURFACE. The shell
    /// mints the surface's cap; the cockpit files it in its vault. (Opening a
    /// cell that isn't selected falls back to the service anchor so the verb is
    /// always live.)
    fn shell_open_selected(&mut self, cx: &mut Context<Self>) {
        let cell = match self.selection {
            Selection::Cell(id) => id,
            _ => self.anchors[1], // service, as a sensible default
        };
        let short = reflect::short_hex(cell.as_bytes());
        let cap = self.shell.open_cell_view(cell, format!("cell {short}"));
        self.surface_caps.insert(cap.surface(), cap);
        self.last_outcome = Some(format!("shell: opened surface for cell {short} (cap minted)"));
        self.tab = Tab::Shell;
        cx.notify();
    }

    /// Focus + raise the front-most NON-console surface (a cap-gated op). The
    /// cockpit presents the held cap; the shell authenticates it before raising.
    fn shell_focus_front(&mut self, cx: &mut Context<Self>) {
        // Find the current front non-console surface in the live scene.
        let front = {
            let w = self.world.borrow();
            let scene = self.shell.compose(&w);
            scene
                .items
                .iter()
                .rev()
                .find(|it| !it.surface.is_console())
                .map(|it| it.surface.id())
        };
        if let Some(id) = front {
            self.with_cap(id, |shell, cap| shell.focus(cap), cx, "focus");
        } else {
            self.last_outcome = Some("shell: no cell surface to focus".to_string());
            cx.notify();
        }
    }

    /// Close the focused surface (cap-gated; the console is protected, so closing
    /// it is refused — a refusal the operator can watch). The cap is dropped when
    /// the surface closes.
    fn shell_close_focused(&mut self, cx: &mut Context<Self>) {
        let Some(id) = self.shell.focused() else {
            self.last_outcome = Some("shell: nothing focused to close".to_string());
            cx.notify();
            return;
        };
        let outcome = match self.surface_caps.get(&id) {
            Some(cap) => self.shell.close(cap),
            None => Err(starbridge_v2::shell::ShellError::Unauthorized),
        };
        match outcome {
            Ok(()) => {
                self.surface_caps.remove(&id);
                self.last_outcome = Some("shell: closed the focused surface (cap retired)".to_string());
            }
            Err(e) => {
                self.last_outcome = Some(format!("shell: close REFUSED — {}", shell_err(&e)));
            }
        }
        cx.notify();
    }

    /// Minimize the focused surface (cap-gated).
    fn shell_minimize_focused(&mut self, cx: &mut Context<Self>) {
        let Some(id) = self.shell.focused() else {
            self.last_outcome = Some("shell: nothing focused to minimize".to_string());
            cx.notify();
            return;
        };
        self.with_cap(id, |shell, cap| shell.set_minimized(cap, true), cx, "minimize");
    }

    /// SHARE the focused window with another app — an ATTENUATING (read-only
    /// mirror) hand-off through a REAL `Effect::GrantCapability` turn on the
    /// firmament executor. Commits; the recipient's narrowed window cap is filed
    /// in the vault (so its shared window is drivable), demonstrating "a window =
    /// a firmament cap" delegated through the real executor — granted ⊆ held.
    fn shell_share_focused(&mut self, cx: &mut Context<Self>) {
        let Some(id) = self.shell.focused() else {
            self.last_outcome = Some("shell: nothing focused to share".to_string());
            cx.notify();
            return;
        };
        let Some(cap) = self.surface_caps.get(&id).cloned() else {
            self.last_outcome = Some("shell: no held cap for the focused surface".to_string());
            cx.notify();
            return;
        };
        // Hand a READ-ONLY mirror (Signature ⊆ the held rights) to a peer app.
        match self.shell.share(&cap, /*peer app*/ 0x5EED, dregg_cell::AuthRequired::Signature) {
            Ok(shared) => {
                self.surface_caps.insert(shared.surface(), shared);
                self.last_outcome = Some(
                    "shell: shared a read-only window mirror (real GrantCapability turn committed)"
                        .to_string(),
                );
            }
            Err(e) => {
                self.last_outcome = Some(format!("shell: share REFUSED — {}", shell_err(&e)));
            }
        }
        self.tab = Tab::Shell;
        cx.notify();
    }

    /// ⚠ Attempt to OVER-SHARE the focused window — the no-amplification
    /// guarantee firing at the desktop. We first share a read-only mirror to a
    /// peer (commits), then have THAT peer try to re-share its window with WIDER
    /// authority than it holds; the REAL executor REJECTS the widening
    /// (`DelegationDenied`). This is the window-manager analogue of the composer's
    /// ⚠ over-grant verb — a refusal the operator can watch.
    fn shell_overshare_focused(&mut self, cx: &mut Context<Self>) {
        let Some(id) = self.shell.focused() else {
            self.last_outcome = Some("shell: nothing focused to over-share".to_string());
            cx.notify();
            return;
        };
        let Some(cap) = self.surface_caps.get(&id).cloned() else {
            self.last_outcome = Some("shell: no held cap for the focused surface".to_string());
            cx.notify();
            return;
        };
        // Step 1: legitimately hand a peer a read-only mirror (commits).
        let mirror = match self.shell.share(&cap, /*peer*/ 0xA11CE, dregg_cell::AuthRequired::Signature) {
            Ok(m) => m,
            Err(e) => {
                self.last_outcome = Some(format!("shell: setup share failed — {}", shell_err(&e)));
                cx.notify();
                return;
            }
        };
        self.surface_caps.insert(mirror.surface(), mirror.clone());
        // Step 2: that read-only-mirror peer tries to OVER-SHARE (Signature →
        // Either is WIDER). The real executor REJECTS it — watch it fire.
        match self.shell.share(&mirror, /*victim*/ 0xBAD, dregg_cell::AuthRequired::Either) {
            Ok(_) => {
                self.last_outcome =
                    Some("shell: over-share UNEXPECTEDLY committed (should have rejected!)".to_string());
            }
            Err(e) => {
                self.last_outcome = Some(format!(
                    "shell: ⚠ over-share REJECTED by the real executor — {} (no-amplification on glass)",
                    shell_err(&e)
                ));
            }
        }
        self.tab = Tab::Shell;
        cx.notify();
    }

    /// Cycle the compositor layout (float → tile → stack). A shell-global op (it
    /// rearranges the whole scene), so it is not surface-cap-scoped.
    fn shell_cycle_layout(&mut self, cx: &mut Context<Self>) {
        self.shell.cycle_layout();
        self.last_outcome = Some(format!("shell: layout → {}", self.shell.layout().label()));
        self.tab = Tab::Shell;
        cx.notify();
    }

    // --- THE VERIFIED-SCENE teaching moments (T1/T2/T3 at the pixel layer) ---
    //
    // These exercise the compositor's `present()` path so the operator can WATCH
    // the scene-authority teeth bite — exactly the over-share teaching moment,
    // one hop out (the no-amplification guarantee firing at the GLASS).

    /// PRESENT honestly from the FOCUSED surface: paint its own region, claim
    /// focus (it IS the focus holder), advance the frame. COMMITS — the scene
    /// the operator sees is the genuine projection (the commit polarity).
    fn shell_present_focused(&mut self, cx: &mut Context<Self>) {
        let Some(id) = self.shell.focused() else {
            self.last_outcome = Some("shell: nothing focused to present".to_string());
            cx.notify();
            return;
        };
        let Some(cap) = self.surface_caps.get(&id).cloned() else {
            self.last_outcome = Some("shell: no held cap for the focused surface".to_string());
            cx.notify();
            return;
        };
        let region = id.region();
        let digest = self.next_frame_digest();
        let w = self.world.borrow();
        match self.shell.present(&cap, &w, vec![region], /*claims_focus*/ true, digest) {
            Ok(commit) => {
                self.last_outcome = Some(format!(
                    "shell: present COMMITTED — frame {} on the focused surface (genuine projection)",
                    commit.digest
                ));
            }
            Err(e) => {
                self.last_outcome = Some(format!("shell: present REFUSED — {}", shell_err(&e)));
            }
        }
        drop(w);
        self.tab = Tab::Shell;
        cx.notify();
    }

    /// Attempt an OVERPAINT: the focused surface tries to paint the FRONT OTHER
    /// surface's region — the T1 non-overlap tooth REFUSES it (a cell cannot
    /// paint a region another cell owns). The pixel-layer over-grant.
    fn shell_overpaint_focused(&mut self, cx: &mut Context<Self>) {
        let Some(id) = self.shell.focused() else {
            self.last_outcome = Some("shell: nothing focused to present".to_string());
            cx.notify();
            return;
        };
        let Some(cap) = self.surface_caps.get(&id).cloned() else {
            self.last_outcome = Some("shell: no held cap for the focused surface".to_string());
            cx.notify();
            return;
        };
        // Compute the frame digest BEFORE borrowing the world (the digest
        // counter is `&mut self`; the present below holds an immutable borrow).
        let digest = self.next_frame_digest();
        // Find ANOTHER surface's region to overpaint (a genuinely-distinct attack
        // — a real second surface's region, not a malformed one).
        let w = self.world.borrow();
        let victim_region = self
            .shell
            .compose_scene(&w)
            .surfaces
            .iter()
            .find(|s| Some(s.owner) != self.shell.focused_cell())
            .and_then(|s| s.regions.first().copied());
        let Some(victim_region) = victim_region else {
            drop(w);
            self.last_outcome =
                Some("shell: need a second surface to demo an overpaint".to_string());
            cx.notify();
            return;
        };
        match self.shell.present(&cap, &w, vec![victim_region], true, digest) {
            Ok(_) => {
                self.last_outcome = Some(
                    "shell: overpaint UNEXPECTEDLY committed (should have rejected!)".to_string(),
                );
            }
            Err(e) => {
                self.last_outcome = Some(format!(
                    "shell: ⚠ overpaint REFUSED by the verified scene — {} (T1 no-amplification on glass)",
                    shell_err(&e)
                ));
            }
        }
        drop(w);
        self.tab = Tab::Shell;
        cx.notify();
    }

    /// Attempt an INPUT-STEAL: a NON-focused surface presents its own region but
    /// asserts input focus to steal the keystroke — the T3 input-routing tooth
    /// REFUSES it (input routes only to the focus holder).
    fn shell_input_steal(&mut self, cx: &mut Context<Self>) {
        // Compute the frame digest BEFORE borrowing the world (the digest counter
        // is `&mut self`; the present below holds an immutable borrow of it).
        let digest = self.next_frame_digest();
        // Find a non-focused, non-console surface to play the thief.
        let w = self.world.borrow();
        let thief = self
            .shell
            .surfaces_in_z_order()
            .into_iter()
            .find(|s| !s.is_console() && Some(s.id()) != self.shell.focused())
            .map(|s| s.id());
        let Some(thief) = thief else {
            drop(w);
            self.last_outcome =
                Some("shell: need a second surface to demo an input-steal".to_string());
            cx.notify();
            return;
        };
        let Some(cap) = self.surface_caps.get(&thief).cloned() else {
            drop(w);
            self.last_outcome = Some("shell: no held cap for the thief surface".to_string());
            cx.notify();
            return;
        };
        let region = thief.region();
        match self.shell.present(&cap, &w, vec![region], /*claims_focus*/ true, digest) {
            Ok(_) => {
                self.last_outcome = Some(
                    "shell: input-steal UNEXPECTEDLY committed (should have rejected!)".to_string(),
                );
            }
            Err(e) => {
                self.last_outcome = Some(format!(
                    "shell: ⚠ input-steal REFUSED by the verified scene — {} (T3 only the focus holder gets input)",
                    shell_err(&e)
                ));
            }
        }
        drop(w);
        self.tab = Tab::Shell;
        cx.notify();
    }

    /// A monotonic frame digest for the present teaching moments (so every
    /// present genuinely advances the frame — the Lean `new ≠ old` leg).
    fn next_frame_digest(&mut self) -> u64 {
        self.frame_seq = self.frame_seq.wrapping_add(1);
        0xF00D_0000 + self.frame_seq
    }

    /// Focus a surface by id when the operator clicks it in the scene. The click
    /// is only a HINT — the cockpit then presents the held cap, and the shell's
    /// cap-gated `focus` is the actual authority (no held cap ⇒ no focus).
    fn shell_click_surface(&mut self, id: SurfaceId, cx: &mut Context<Self>) {
        self.with_cap(id, |shell, cap| shell.focus(cap), cx, "focus");
    }

    /// Drive a cap-gated shell op for surface `id`: look up the held cap, present
    /// it to the shell, and surface the verdict. Centralizes the "present the
    /// cap or it's refused" discipline so every op goes through it.
    fn with_cap<F>(&mut self, id: SurfaceId, op: F, cx: &mut Context<Self>, what: &str)
    where
        F: FnOnce(&mut Shell, &SurfaceCapability) -> Result<(), starbridge_v2::shell::ShellError>,
    {
        let result = match self.surface_caps.get(&id) {
            Some(cap) => op(&mut self.shell, cap),
            // No held cap for this surface → nothing to present → refused. This
            // IS the no-ambient-authority property (you can't act without a cap).
            None => Err(starbridge_v2::shell::ShellError::Unauthorized),
        };
        if let Err(e) = result {
            self.last_outcome = Some(format!("shell: {what} REFUSED — {}", shell_err(&e)));
        }
        cx.notify();
    }

    // --- THE CENTRAL DISPATCHER — one path for buttons AND the palette -------

    /// Run a palette [`CommandId`] through the SAME `&mut Cockpit` verbs the
    /// buttons call. This is what keeps the ⌘K palette honestly "over ALL
    /// actions": there is no parallel action path — every command lands here and
    /// routes to the one method that already implements it.
    fn dispatch(&mut self, id: CommandId, cx: &mut Context<Self>) {
        match id {
            CommandId::Transfer => self.run_demo_transfer(cx),
            CommandId::ComposeMulti => self.run_compose_multi(cx),
            CommandId::Grant => self.run_demo_grant(cx),
            CommandId::CreateCell => self.run_demo_create(cx),
            CommandId::Seal => self.run_seal(cx),
            CommandId::Burn => self.run_burn(cx),
            CommandId::OverGrant => self.run_over_grant(cx),

            // The WHAT-IF / SIMULATE composer (navigate to the tab on a verb so
            // the prediction is in view).
            CommandId::SimRun => {
                self.set_tab(Tab::Simulate, cx);
                self.sim_run(cx);
            }
            CommandId::SimCommit => {
                self.set_tab(Tab::Simulate, cx);
                self.sim_commit(cx);
            }
            CommandId::SimAddEffect => {
                self.set_tab(Tab::Simulate, cx);
                self.sim_add_effect(cx);
            }

            CommandId::GoComposer => self.set_tab(Tab::Composer, cx),
            CommandId::GoSimulate => self.set_tab(Tab::Simulate, cx),
            CommandId::GoObjects => self.set_tab(Tab::Objects, cx),
            CommandId::GoDebugger => self.set_tab(Tab::Debugger, cx),
            CommandId::GoReplay => self.set_tab(Tab::Replay, cx),
            CommandId::GoCipherclerk => self.set_tab(Tab::Cipherclerk, cx),
            CommandId::GoEditor => self.set_tab(Tab::Editor, cx),
            CommandId::GoHome => self.set_tab(Tab::Home, cx),
            CommandId::GoShell => self.set_tab(Tab::Shell, cx),
            CommandId::GoAgent => self.set_tab(Tab::Agent, cx),
            CommandId::GoBuffer => self.set_tab(Tab::Buffer, cx),
            CommandId::GoTerminal => self.set_tab(Tab::Terminal, cx),
            CommandId::GoSwarm => self.set_tab(Tab::Swarm, cx),
            CommandId::GoGraph => self.set_tab(Tab::Graph, cx),
            CommandId::GoOrgans => self.set_tab(Tab::Organs, cx),
            CommandId::GoProofs => self.set_tab(Tab::Proofs, cx),
            CommandId::GoPowerbox => self.set_tab(Tab::Powerbox, cx),
            CommandId::LaunchConfinedApp => self.run_launch_confined_app(cx),

            CommandId::BufferType => self.buffer_type_demo(cx),
            CommandId::BufferCommit => self.buffer_commit(cx),
            CommandId::BufferReadOnlyWrite => self.buffer_readonly_write_demo(cx),
            CommandId::TerminalRunInMandate => self.terminal_run_in_mandate(cx),
            CommandId::TerminalRunOutOfMandate => self.terminal_run_out_of_mandate(cx),

            CommandId::SwarmCoordinatorEmitA => self.swarm_coordinator_emit_a(cx),
            CommandId::SwarmWorkerADrain => self.swarm_worker_a_drain(cx),
            CommandId::SwarmCoordinatorTransferAndWake => {
                self.swarm_coordinator_transfer_and_wake(cx)
            }

            CommandId::KillerDemoAdvance => self.killer_demo_advance(cx),
            CommandId::KillerDemoRunAll => self.killer_demo_run_all(cx),
            CommandId::KillerDemoOverShare => self.killer_demo_over_share(cx),
            CommandId::KillerDemoReset => self.killer_demo_reset(cx),

            CommandId::ShellOpenSelected => self.shell_open_selected(cx),
            CommandId::ShellFocusFront => self.shell_focus_front(cx),
            CommandId::ShellCloseFocused => self.shell_close_focused(cx),
            CommandId::ShellCycleLayout => self.shell_cycle_layout(cx),
            CommandId::ShellMinimizeFocused => self.shell_minimize_focused(cx),
            CommandId::ShellShareFocused => self.shell_share_focused(cx),
            CommandId::ShellOverShareFocused => self.shell_overshare_focused(cx),
            CommandId::ShellPresentFocused => self.shell_present_focused(cx),
            CommandId::ShellOverpaintFocused => self.shell_overpaint_focused(cx),
            CommandId::ShellInputSteal => self.shell_input_steal(cx),

            CommandId::ReplayStepBack => self.replay_step_back(cx),
            CommandId::ReplayStepForward => self.replay_step_forward(cx),
            CommandId::ReplayToGenesis => self.replay_to_genesis(cx),
            CommandId::ReplayToHead => self.replay_to_head(cx),
            CommandId::ReplayForkHere => self.replay_fork_here(cx),
            CommandId::ReplayClearFork => self.replay_clear_fork(cx),

            CommandId::ClerkMint => self.run_clerk_mint(cx),
            CommandId::ClerkAttenuate => self.run_clerk_attenuate(cx),
            CommandId::ClerkDelegate => self.run_clerk_delegate(cx),
            CommandId::ClerkDischarge => self.run_clerk_discharge(cx),

            CommandId::DebugRetargetSelected => self.debug_retarget_selected(cx),
            CommandId::SelectImage => {
                self.selection = Selection::Image;
                cx.notify();
            }
            CommandId::Dismiss => {
                self.palette.close();
                cx.notify();
            }
        }
    }

    fn set_tab(&mut self, tab: Tab, cx: &mut Context<Self>) {
        // Navigating to SWARM is where the killer demo lives — boot it lazily HERE
        // (on the click), so the metered-world + factory-deploy cost lands on the
        // navigation rather than on the first paint. The SWARM panel then always
        // has a booted demo to reflect. (Every other tab leaves it `None`.)
        if matches!(tab, Tab::Swarm) {
            let _ = self.killer_demo();
        }
        self.tab = tab;
        // M3 WIDEN — witness the tab move into the workspace cell (the §3.4 selector
        // is now a rewindable dregg-graph mutation). The free draft (`self.tab`)
        // already moved; this lands the occasional `SetField` commit so the cell
        // read `render()` dispatches on catches up.
        self.witness_tab();
        cx.notify();
    }

    /// M3 WIDEN — THE WITNESSED ACTIVE TAB (`render(workspace_subgraph)`, §3.4). The
    /// tab `render()` dispatches on, read FROM the [`WorkspaceCell`]'s committed
    /// (prior-frame) selector index — the whole cockpit selector is cell-driven, not
    /// a Rust field. The free draft (`self.tab`) is the *visible* aim; the committed
    /// cell index is the *witnessed* one. They agree after [`Self::witness_tab`]; a
    /// dangling cell (gone from the ledger) degrades to the live draft.
    fn active_tab(&self) -> Tab {
        match self.workspace_cell.committed_tab(&self.world.borrow()) {
            Some(idx) => Tab::from_index(idx),
            // The backing cell is absent (never in the boot path) — fall to the free
            // draft so the cockpit is never blank.
            None => self.tab,
        }
    }

    /// M3 WIDEN — sync the workspace cell's free draft to the live `self.tab` and land
    /// an occasional witnessed `SetField` commit (the [`BufferCell`] commit discipline,
    /// generalized to the tab selector). A no-op when already clean. A commit failure
    /// leaves the free draft moved (the panel still reflects the operator's aim); the
    /// witnessed selector catches up on the next successful witness. The active tab is
    /// therefore a real, rewindable cell mutation, conserving nothing (§3.5).
    fn witness_tab(&mut self) {
        self.workspace_cell.set_active_tab(self.tab.index());
        if !self.workspace_cell.is_clean(&self.world.borrow()) {
            let _ = self.workspace_cell.commit(&mut self.world.borrow_mut());
        }
    }

    /// Focus the cockpit root so it receives key events (called on window open).
    pub fn focus_on_open(&mut self, window: &mut Window, cx: &mut Context<Self>) {
        window.focus(&self.focus, cx);
    }

    // --- the ⌘K key handler -------------------------------------------------

    /// Handle a key event. ⌘K toggles the palette; while it is open, typed
    /// characters filter, ↑/↓ move the selection, Enter dispatches, Esc closes.
    /// Returns nothing — it mutates palette state + may dispatch a command.
    fn on_key(&mut self, ev: &KeyDownEvent, cx: &mut Context<Self>) {
        let ks = &ev.keystroke;
        let key = ks.key.as_str();
        let cmd = ks.modifiers.platform || ks.modifiers.control;

        // ⌘K / Ctrl-K toggles the palette from anywhere.
        if cmd && key == "k" {
            self.palette.toggle();
            cx.notify();
            return;
        }

        if !self.palette.is_open() {
            return;
        }

        match key {
            "escape" => {
                self.palette.close();
                cx.notify();
            }
            "enter" => {
                if let Some(id) = self.palette.accept() {
                    self.dispatch(id, cx);
                }
                cx.notify();
            }
            "backspace" => {
                self.palette.backspace();
                cx.notify();
            }
            "down" => {
                self.palette.select_next();
                cx.notify();
            }
            "up" => {
                self.palette.select_prev();
                cx.notify();
            }
            _ => {
                // A typed character (cmd not held) filters the query.
                if !cmd {
                    if let Some(ch) = ks.key_char.as_ref().and_then(|s| s.chars().next()) {
                        if !ch.is_control() {
                            self.palette.push_char(ch);
                            cx.notify();
                        }
                    }
                }
            }
        }
    }

    fn note_outcome(&mut self, outcome: CommitOutcome) {
        self.last_outcome = Some(match outcome {
            CommitOutcome::Committed { receipt, .. } => {
                // Jump the inspector to the new receipt.
                let idx = self.world.borrow().receipts().len().saturating_sub(1);
                self.selection = Selection::Receipt(idx);
                format!("committed · receipt {}", reflect::short_hex(&receipt.receipt_hash()))
            }
            CommitOutcome::Rejected { reason, .. } => format!("REJECTED by executor: {reason}"),
            // Suspended: the turn was staged in the pending queue, not run. The
            // live loop is halted (meta-debug Suspend gate); it commits on resume.
            CommitOutcome::Queued { agent } => {
                format!("queued · world suspended · {}", world::short(&agent))
            }
        });
    }

    // --- panels --------------------------------------------------------------

    fn rail_header(&self) -> impl IntoElement {
        let w = self.world.borrow();
        let root = reflect::short_hex(&w.state_root());
        div()
            .flex()
            .flex_col()
            .gap_1()
            .p_3()
            .border_b_1()
            .border_color(theme::border())
            .child(div().text_lg().text_color(theme::text()).child("Starbridge v2"))
            .child(
                div()
                    .text_xs()
                    .text_color(theme::muted())
                    .child("the live, verified, ocap image"),
            )
            .child(
                div()
                    .text_xs()
                    .text_color(theme::accent())
                    .child("⌘K · command palette (every action)"),
            )
            .child(
                div()
                    .flex()
                    .gap_2()
                    .mt_2()
                    .child(pill("embedded executor", theme::good()))
                    .child(pill(format!("h{}", w.height()), theme::accent())),
            )
            .child(
                div()
                    .text_xs()
                    .text_color(theme::muted())
                    .child(format!("image root: {root}")),
            )
            .child(
                div()
                    .text_xs()
                    .text_color(theme::muted())
                    .child(format!(
                        "{} cells · {} receipts",
                        w.cell_count(),
                        w.receipts().len()
                    )),
            )
            .children(self.live_node_strip())
    }

    /// The LIVE NODE strip in the rail header (only when `--node <url>` connected):
    /// the remote node's liveness/producer/height + the LIVE receipt feed head
    /// (the SSE stream filling per receipt) + the resume cursor. This is the
    /// distribution axis's REMOTE half — the master interface watching a running
    /// federation alongside its own embedded image.
    fn live_node_strip(&self) -> Option<gpui::AnyElement> {
        let ln = self.live_node.as_ref()?;
        let mut strip = div()
            .flex()
            .flex_col()
            .gap_1()
            .mt_2()
            .pt_2()
            .border_t_1()
            .border_color(theme::border())
            .child(section_title("LIVE NODE · remote federation"));
        // The connection target + (from the last snapshot) the producer/liveness.
        let desc = ln.client().describe();
        strip = strip.child(
            div()
                .flex()
                .flex_wrap()
                .gap_1()
                .items_center()
                .child(pill(desc, theme::accent()))
                .children(self.live_snapshot.as_ref().map(|s| {
                    pill(
                        format!(
                            "{} · producer {}",
                            if s.status.healthy { "healthy" } else { "DOWN" },
                            s.status.state_producer
                        ),
                        if s.status.healthy { theme::good() } else { theme::warn() },
                    )
                }))
                .children(self.live_snapshot.as_ref().map(|s| {
                    pill(format!("h{}", s.status.latest_height), theme::accent())
                })),
        );
        // The LIVE receipt feed: head index + count + resume cursor (the SSE drain).
        let feed = &self.live_feed;
        let head = feed
            .latest()
            .map(|e| format!("#{} · {}", e.chain_index, e.finality))
            .unwrap_or_else(|| "(awaiting first receipt)".to_string());
        strip = strip.child(
            div()
                .flex()
                .flex_wrap()
                .gap_1()
                .items_center()
                .child(pill(format!("{} streamed", feed.receipts().len()), theme::good()))
                .child(pill(format!("head {head}"), theme::accent()))
                .children(
                    feed.resume_cursor()
                        .map(|c| pill(format!("cursor {c}"), theme::muted())),
                ),
        );
        strip = strip.child(div().text_xs().text_color(theme::muted()).child(
            "the SSE receipt stream (/api/events/stream) advances this PER RECEIPT \
             (cx.notify), not on reload — the live receipt nervous system",
        ));
        Some(strip.into_any_element())
    }

    fn cell_world(&self, cx: &mut Context<Self>) -> impl IntoElement {
        let w = self.world.borrow();
        let mut col = div().flex().flex_col().gap_1().p_2();
        col = col.child(section_title("CELL WORLD · ocap").mb_1());
        // The image object itself, selectable.
        col = col.child(self.image_row(cx));
        for id in &self.cells {
            if let Some(cell) = w.ledger().get(id) {
                col = col.child(self.cell_row(*id, cell, cx));
            }
        }
        col
    }

    fn image_row(&self, cx: &mut Context<Self>) -> impl IntoElement {
        let selected = matches!(self.selection, Selection::Image);
        div()
            .id("image-row")
            .flex()
            .justify_between()
            .px_2()
            .py_1()
            .rounded_md()
            .bg(if selected { theme::panel_hi() } else { theme::panel() })
            .cursor_pointer()
            .on_mouse_down(
                MouseButton::Left,
                cx.listener(|this, _ev, _w, cx| {
                    this.selection = Selection::Image;
                    cx.notify();
                }),
            )
            .child(div().text_color(theme::accent()).child("◆ this image"))
    }

    fn cell_row(&self, id: CellId, cell: &dregg_cell::Cell, cx: &mut Context<Self>) -> impl IntoElement {
        let selected = matches!(self.selection, Selection::Cell(s) if s == id);
        let bal = cell.state.balance();
        let caps = cell.capabilities.len();
        let bal_color = if bal < 0 { theme::warn() } else { theme::text() };
        div()
            .id(SharedString::from(format!("cell-{}", reflect::short_hex(id.as_bytes()))))
            .flex()
            .flex_col()
            .gap_0p5()
            .px_2()
            .py_1()
            .rounded_md()
            .bg(if selected { theme::panel_hi() } else { theme::panel() })
            .cursor_pointer()
            .on_mouse_down(
                MouseButton::Left,
                cx.listener(move |this, _ev, _w, cx| {
                    this.selection = Selection::Cell(id);
                    cx.notify();
                }),
            )
            .child(
                div()
                    .flex()
                    .justify_between()
                    .child(div().text_color(theme::text()).child(format!("⬡ {}", reflect::short_hex(id.as_bytes()))))
                    .child(div().text_color(bal_color).child(format!("{bal}"))),
            )
            .child(
                div()
                    .flex()
                    .gap_2()
                    .child(div().text_xs().text_color(theme::muted()).child(format!("{caps} caps")))
                    .when(cell.delegate.is_some(), |d| {
                        d.child(div().text_xs().text_color(theme::muted()).child("delegate"))
                    })
                    .when(!matches!(cell.program, dregg_cell::CellProgram::None), |d| {
                        d.child(div().text_xs().text_color(theme::accent()).child("program"))
                    }),
            )
    }

    fn inspector(&self) -> impl IntoElement {
        let w = self.world.borrow();
        let obj: Option<Inspectable> = match &self.selection {
            Selection::Image => Some(reflect::reflect_image(&w)),
            Selection::Cell(id) => w.ledger().get(id).map(|c| reflect::reflect_cell(id, c)),
            Selection::Receipt(i) => w.receipts().get(*i).map(reflect::reflect_receipt),
        };
        let mut panel = div().flex().flex_col().gap_1().p_3().size_full();
        panel = panel.child(section_title("INSPECTOR · reflective").mb_1());
        match obj {
            Some(obj) => {
                panel = panel.child(
                    div().text_color(theme::text()).child(obj.title.clone()),
                );
                panel = panel.child(
                    div().text_xs().text_color(theme::muted()).mb_2().child(obj.subtitle.clone()),
                );
                panel = panel.child(kind_badge(obj.kind));
                for f in &obj.fields {
                    panel = panel.child(field_row(f));
                }
            }
            None => {
                panel = panel.child(div().text_color(theme::muted()).child("(nothing selected)"));
            }
        }
        panel
    }

    fn blocklace(&self, cx: &mut Context<Self>) -> impl IntoElement {
        let w = self.world.borrow();
        let mut col = div().flex().flex_col().gap_1().p_2();
        col = col.child(section_title("BLOCKLACE · provenance").mb_1());
        if w.receipts().is_empty() {
            col = col.child(div().text_xs().text_color(theme::muted()).child("(no receipts yet — run a verb)"));
        }
        // Most-recent first.
        for (i, r) in w.receipts().iter().enumerate().rev() {
            let selected = matches!(self.selection, Selection::Receipt(s) if s == i);
            let hash = reflect::short_hex(&r.receipt_hash());
            col = col.child(
                div()
                    .id(SharedString::from(format!("rcpt-{i}")))
                    .flex()
                    .justify_between()
                    .px_2()
                    .py_0p5()
                    .rounded_md()
                    .bg(if selected { theme::panel_hi() } else { theme::panel() })
                    .cursor_pointer()
                    .on_mouse_down(
                        MouseButton::Left,
                        cx.listener(move |this, _ev, _w, cx| {
                            this.selection = Selection::Receipt(i);
                            cx.notify();
                        }),
                    )
                    .child(div().text_xs().text_color(theme::accent()).child(format!("●─ {hash}")))
                    .child(div().text_xs().text_color(theme::muted()).child(format!("{} eff", r.action_count))),
            );
        }
        col
    }

    fn composer(&self, cx: &mut Context<Self>) -> impl IntoElement {
        div()
            .flex()
            .flex_col()
            .gap_2()
            .p_3()
            .child(section_title("COMPOSER · drive the executor"))
            .child(div().text_xs().text_color(theme::muted()).child(
                "Each verb composes a turn and runs it through the EMBEDDED VERIFIED executor. \
                 Watch the image, receipts, and dynamics update live.",
            ))
            .child(verb_button(cx, "transfer 1,000 → user", theme::good(), Cockpit::run_demo_transfer))
            .child(verb_button(cx, "compose multi-action (pay service + user)", theme::good(), Cockpit::run_compose_multi))
            .child(verb_button(cx, "grant capability (service→user)", theme::accent(), Cockpit::run_demo_grant))
            .child(verb_button(cx, "create cell (conserves value)", theme::accent(), Cockpit::run_demo_create))
            .child(verb_button(cx, "seal a fresh cell (lifecycle)", theme::accent(), Cockpit::run_seal))
            .child(verb_button(cx, "burn 1,000 (supply reduced)", theme::warn(), Cockpit::run_burn))
            .child(verb_button(cx, "⚠ over-grant (watch it REJECT)", theme::warn(), Cockpit::run_over_grant))
            .child(self.outcome_banner())
    }

    /// The WHAT-IF / SIMULATE panel: compose any intent over any cell across the
    /// effect palette, PREDICT its consequences in a forked throwaway world (the
    /// real executor, live world untouched), then COMMIT the identical turn.
    fn simulate_panel(&self, cx: &mut Context<Self>) -> impl IntoElement {
        use starbridge_v2::simulate::SimOutcome;
        let cells = &self.cells;
        let target = cells.get(self.sim_target_idx).copied().unwrap_or(self.sim_draft.agent);
        let palette = self.sim_effect_palette();
        let effect = palette.get(self.sim_effect_idx).cloned();
        let effect_label = effect.as_ref().map(|e| e.label()).unwrap_or_default();
        let agent_short = reflect::short_hex(&self.sim_draft.agent.0);
        let target_short = reflect::short_hex(&target.0);
        let n_actions = self.sim_draft.actions.len();
        let n_effects = self.sim_draft.effect_count();
        let predicted_ok = matches!(self.sim_outcome, Some(SimOutcome::Predicted { .. }));

        let mut col = div().flex().flex_col().gap_2().p_3().size_full().overflow_hidden();
        col = col.child(section_title(
            "SIMULATE · compose any intent · PREDICT before committing",
        ));
        col = col.child(div().text_xs().text_color(theme::muted()).child(
            "Build a turn over any cell(s) across the effect palette, run it through a \
             FORKED throwaway world (the real executor over a deep copy of the live image) \
             to see the predicted post-state + receipt or refusal — the LIVE world is \
             untouched — then COMMIT the identical turn for real.",
        ));

        // --- the pickers (agent · target · effect) ---
        col = col.child(
            div()
                .flex()
                .flex_wrap()
                .items_center()
                .gap_1()
                .child(div().text_xs().text_color(theme::muted()).child("agent:"))
                .child(cycle_chip(
                    cx,
                    "sim-agent",
                    format!("{agent_short} (cycle)"),
                    theme::accent(),
                    Cockpit::sim_cycle_agent,
                ))
                .child(div().text_xs().text_color(theme::muted()).child("· target:"))
                .child(cycle_chip(
                    cx,
                    "sim-target",
                    format!("{target_short} (cycle)"),
                    theme::good(),
                    Cockpit::sim_cycle_target,
                ))
                .child(div().text_xs().text_color(theme::muted()).child("· effect:"))
                .child(cycle_chip(
                    cx,
                    "sim-effect",
                    format!("{effect_label} (cycle)"),
                    theme::warn(),
                    Cockpit::sim_cycle_effect,
                )),
        );
        // --- the build verbs ---
        col = col.child(
            div()
                .flex()
                .flex_wrap()
                .gap_1()
                .child(small_button(cx, "sim-add", "+ add effect", theme::good(), Cockpit::sim_add_effect))
                .child(small_button(cx, "sim-pop", "− last action", theme::muted(), Cockpit::sim_pop_action))
                .child(small_button(cx, "sim-clear", "clear draft", theme::muted(), Cockpit::sim_clear)),
        );

        // --- the draft forest ---
        col = col.child(
            div()
                .flex()
                .flex_wrap()
                .items_center()
                .gap_1()
                .child(pill(format!("{n_actions} action(s)"), theme::accent()))
                .child(pill(format!("{n_effects} effect(s)"), theme::accent())),
        );
        let mut forest_box = div()
            .flex()
            .flex_col()
            .gap_0p5()
            .p_2()
            .rounded_md()
            .bg(theme::panel())
            .max_h(px(150.))
            .overflow_hidden();
        if self.sim_draft.actions.is_empty() {
            forest_box = forest_box.child(
                div().text_xs().text_color(theme::muted()).child(
                    "(empty forest — pick a target + effect and press + add)",
                ),
            );
        } else {
            for (i, a) in self.sim_draft.actions.iter().enumerate() {
                let tgt = reflect::short_hex(&a.target.0);
                let effs = a
                    .effects
                    .iter()
                    .map(|e| e.label())
                    .collect::<Vec<_>>()
                    .join(" · ");
                forest_box = forest_box.child(
                    div()
                        .text_xs()
                        .text_color(theme::text())
                        .child(format!("[{i}] on {tgt}: {effs}")),
                );
            }
        }
        col = col.child(forest_box);

        // --- the SIMULATE + COMMIT verbs ---
        col = col.child(
            div()
                .flex()
                .flex_wrap()
                .gap_1()
                .child(small_button(cx, "sim-run", "▶ SIMULATE (predict)", theme::accent(), Cockpit::sim_run))
                .child({
                    // The commit button is enabled (and colored go) only after a
                    // predicted-commit; otherwise it is dimmed + explains itself.
                    let (label, color) = if predicted_ok {
                        ("✓ COMMIT for real", theme::good())
                    } else {
                        ("✓ commit (simulate first)", theme::muted())
                    };
                    small_button(cx, "sim-commit", label, color, Cockpit::sim_commit)
                }),
        );

        // --- the prediction results ---
        col = col.child(self.simulate_results());

        // --- the real-commit banner (distinct from the prediction) ---
        if let Some(b) = &self.sim_commit_banner {
            let color = if b.contains("REJECTED") || b.contains("simulate first") {
                theme::warn()
            } else {
                theme::good()
            };
            col = col.child(
                div().mt_1().p_2().rounded_md().bg(theme::panel()).text_xs().text_color(color).child(b.clone()),
            );
        }
        col
    }

    /// Render the last SIMULATE outcome — the predicted receipt + per-cell deltas +
    /// dynamics, or the refusal (the executor's verdict run one turn ahead).
    fn simulate_results(&self) -> gpui::AnyElement {
        use starbridge_v2::simulate::SimOutcome;
        let mut box_ = div()
            .flex()
            .flex_col()
            .gap_1()
            .mt_1()
            .p_2()
            .rounded_md()
            .border_1()
            .border_color(theme::border())
            .bg(theme::panel());
        match &self.sim_outcome {
            None => {
                return box_
                    .child(
                        div()
                            .text_xs()
                            .text_color(theme::muted())
                            .child("(no prediction yet — press ▶ SIMULATE)"),
                    )
                    .into_any_element();
            }
            Some(SimOutcome::Predicted {
                receipt,
                deltas,
                events,
                cell_count_delta,
                predicted_root,
                ..
            }) => {
                box_ = box_.child(
                    div()
                        .flex()
                        .flex_wrap()
                        .items_center()
                        .gap_1()
                        .child(pill("PREDICTED: would COMMIT", theme::good()))
                        .child(pill(format!("{} action(s)", receipt.action_count), theme::accent()))
                        .child(pill(format!("{} computrons", receipt.computrons_used), theme::accent()))
                        .child(pill(
                            format!("receipt {}", reflect::short_hex(&receipt.receipt_hash())),
                            theme::muted(),
                        )),
                );
                box_ = box_.child(
                    div()
                        .flex()
                        .flex_wrap()
                        .items_center()
                        .gap_1()
                        .child(div().text_xs().text_color(theme::muted()).child("predicted image root:"))
                        .child(pill(reflect::short_hex(predicted_root), theme::accent()))
                        .when(*cell_count_delta != 0, |d| {
                            d.child(pill(
                                format!("cells {:+}", cell_count_delta),
                                theme::good(),
                            ))
                        }),
                );
                box_ = box_.child(section_title("predicted cell deltas"));
                if deltas.iter().all(|d| !d.balance_changed() && d.before.is_some()) {
                    box_ = box_.child(
                        div().text_xs().text_color(theme::muted()).child(
                            "(no balance moved — a non-value effect; the receipt above still binds it)",
                        ),
                    );
                }
                for d in deltas {
                    let cell = reflect::short_hex(&d.cell.0);
                    let line = match (d.before, d.after) {
                        (None, Some(a)) => format!("· {cell}  BORN → balance {a}"),
                        (Some(_), None) => format!("· {cell}  RETIRED"),
                        (Some(b), Some(a)) if b != a => format!("· {cell}  {b} → {a}"),
                        (Some(b), Some(_)) => format!("· {cell}  unchanged ({b})"),
                        (None, None) => format!("· {cell}  (absent)"),
                    };
                    let color = if d.balance_changed() { theme::text() } else { theme::muted() };
                    box_ = box_.child(div().text_xs().text_color(color).child(line));
                }
                if !events.is_empty() {
                    box_ = box_.child(section_title("predicted dynamics"));
                    for ev in events.iter().take(8) {
                        box_ = box_.child(
                            div().text_xs().text_color(theme::muted()).child(format!("· {}", ev.label())),
                        );
                    }
                }
                box_.into_any_element()
            }
            Some(SimOutcome::Refused {
                reason,
                static_refusal,
                at_action,
                ..
            }) => {
                let badge = if *static_refusal {
                    "PREDICTED: REFUSED (static rail — caught before submission)"
                } else {
                    "PREDICTED: REFUSED (the executor's guarantee would fire)"
                };
                box_ = box_.child(
                    div()
                        .flex()
                        .flex_wrap()
                        .items_center()
                        .gap_1()
                        .child(pill(badge, theme::bad()))
                        .when(!at_action.is_empty(), |d| {
                            d.child(pill(format!("@ action {at_action:?}"), theme::warn()))
                        }),
                );
                box_ = box_.child(
                    div().text_xs().text_color(theme::bad()).child(reason.clone()),
                );
                box_ = box_.child(div().text_xs().text_color(theme::muted()).child(
                    "this is the live executor's verdict, run one turn ahead — no gas spent, \
                     the live image untouched.",
                ));
                box_.into_any_element()
            }
        }
    }

    fn outcome_banner(&self) -> impl IntoElement {
        let (txt, color) = match &self.last_outcome {
            // A rejected turn OR a refused shell op — the guarantee firing.
            Some(s) if s.contains("REJECTED") || s.contains("REFUSED") => (s.clone(), theme::bad()),
            Some(s) => (s.clone(), theme::good()),
            None => ("(no turn run yet)".to_string(), theme::muted()),
        };
        div()
            .mt_2()
            .p_2()
            .rounded_md()
            .bg(theme::panel())
            .text_xs()
            .text_color(color)
            .child(txt)
    }

    // =======================================================================
    // THE GENERIC PRESENTATION RENDERER — the keystone of the moldable inspector.
    //
    // ONE gpui function per `PresentationBody` variant. Every `Presentable` (cell,
    // receipt chain, held cap, reflected constraint, inspected token, …) renders
    // through this single dispatch — adding a `Presentable` later needs NO new gpui
    // code; adding a genuinely new visual kind adds ONE arm here. The model is pure
    // data (proven by `cargo test`); this is the thin render layer the doc's §1.3
    // promises.
    // =======================================================================

    /// THE dispatch: one `PresentationBody` → one widget. Pure (reads the body data
    /// the model already computed off the live world; touches no `self`).
    fn render_presentation_body(body: &PresentationBody) -> gpui::AnyElement {
        match body {
            PresentationBody::Fields(i) => inspectable_row(i).into_any_element(),
            PresentationBody::Graph(g) => render_graph_body(g).into_any_element(),
            PresentationBody::StateMachine(sm) => render_state_machine(sm).into_any_element(),
            PresentationBody::Gauge(g) => render_gauge(g).into_any_element(),
            PresentationBody::Timeline(t) => render_timeline(t).into_any_element(),
            PresentationBody::MerkleTree(m) => render_merkle(m).into_any_element(),
            PresentationBody::Lattice(l) => render_lattice(l).into_any_element(),
            PresentationBody::Trace(t) => render_trace(t).into_any_element(),
            PresentationBody::Prose(p) => div()
                .p_2()
                .text_xs()
                .text_color(theme::text())
                .child(p.clone())
                .into_any_element(),
        }
    }

    // =======================================================================
    // THE MOLDABLE INSPECTOR panel — the Pharo moldable inspector made visible.
    // =======================================================================

    /// Build the presentation SET for a NON-`Cell` lens family, off the focused
    /// cell / the live world. Each arm constructs the lane's real `Presentable`
    /// and returns its `present(ctx)` set — the SAME `Vec<Presentation>` the
    /// `Cell` lens yields, rendered through the SAME generic body widget. This is
    /// what makes the L4–L10 inspector lanes reachable WITHOUT any new gpui code.
    /// `None` iff the lane has nothing to present over this focus (a held-cap-less
    /// cell, an empty receipt chain) — surfaced honestly, never faked.
    fn lens_present_set(&self, w: &World, focus: CellId) -> Option<Vec<Presentation>> {
        let ctx = PresentCtx::new(w, focus);
        match self.moldable_lens {
            // Already handled by the Registry/memo spine in the caller.
            MoldableLens::Cell => Registry::new(w)
                .present(FocusTarget::Cell(focus), focus),

            // L4 — the focused cell's FIRST held capability (its c-list head).
            MoldableLens::Capability => {
                let held = HeldCapability::all_for(w, focus);
                held.into_iter().next().map(|h| h.present(&ctx))
            }

            // L5 — the focused cell's DEEP reflection.
            MoldableLens::DeepCell => {
                DeepCell::from_world(w, focus).map(|d| d.present(&ctx))
            }

            // L6 — the live receipt chain + (when present) the latest receipt.
            // The chain is always presentable (empty chain ⟹ an empty timeline,
            // which is still an honest presentation set, so this never `None`s
            // on an empty image).
            MoldableLens::Receipt => {
                let chain = ReflectedReceiptChain::from_world(w);
                let mut set = chain.present(&ctx);
                if let Some(last) = w.receipts().last() {
                    set.extend(ReflectedReceipt::new(last.clone()).present(&ctx));
                }
                Some(set)
            }

            // L7 — a real minted macaroon, decoded. The cockpit's own
            // `lane_token` gadget mints against its service root key; we re-derive
            // a fresh clerk (it is not Clone) and mint the root token, then wrap it
            // as the decoded `InspectedToken`. Real HMAC chain, real caveats.
            MoldableLens::Token => {
                let mut clerk = self.lane_token.fresh_clerk();
                let token = self.lane_token.mint_root(&mut clerk);
                Some(InspectedToken::new(token, MOLDABLE_TOKEN_ROOT_KEY).present(&ctx))
            }

            // L9 — the focused cell's canonical state-commitment binding (the
            // 8-felt commitment + the anti-omission readout + the absorb trace).
            MoldableLens::Circuit => {
                StateCommitmentBinding::from_world(w, focus).map(|s| s.present(&ctx))
            }

            // L10 — a proven settlement family (a sample escrow deal), its
            // deal-terms + real lifecycle state machine + the genuine descriptor's
            // perpetual-constraint invariant. The terms are a concrete legible
            // deal (the lane is reachable; the SIMULATE/LANES tabs author real
            // ones).
            MoldableLens::Settlement => {
                let escrow = SettlementFamily::Escrow(dregg_cell::blueprint::EscrowTerms {
                    amount: 100,
                    depositor: dregg_cell::field_from_u64(2222),
                    beneficiary: dregg_cell::field_from_u64(1111),
                    condition: dregg_cell::field_from_u64(99),
                    timeout_height: 50,
                });
                Some(escrow.present(&ctx))
            }

            // L8 — the federation survey. In the embedded image no consensus node
            // is connected, so the survey is `disconnected()` — but it still
            // surfaces the captp-only remote-path catalog as a real RawFields
            // presentation (honest about the remote-only reach), so the lane is
            // never blank.
            MoldableLens::Federation => {
                let survey = FederationSurvey::disconnected();
                Some(vec![survey.remote_presentation()])
            }

            // ⌖ BLAME (cv) — "why does this cell exist": dial ClusterVision for the
            // agent reasoning that wrote the focused cell's backing source file. A
            // domain cell is content-addressed (no path of its own), so the question
            // resolves to the inspector image's OWN provenance: the swarm reasoning
            // that wrote the cockpit, keyed on the focused cell's identity. The dial
            // degrades HONESTLY inside `CvProvenance::dial` when cv is absent from
            // PATH — never a fabricated provenance edge. Renders through the SAME
            // generic body widget (Timeline / Prose / Fields all already handled).
            MoldableLens::Blame => {
                Some(CvProvenance::dial(focus, CV_BLAME_SOURCE_PATH).present(&ctx))
            }

            // 🔒 READ-CAP / PRIVACY — the read-confidentiality membrane, WELDED onto
            // the landed `dregg_cell::read_cap` organ (the privacy M0 weld commit):
            // the encrypted-field set read off the live field-visibility, the
            // `granted ⊆ held` read-lattice (the real `ReadCap::attenuate`), and the
            // byte-identical-commitment invariant demonstrated live. The lens is real
            // now; a cell with no committed slots degrades honestly inside `present`.
            MoldableLens::ReadCap => {
                starbridge_v2::read_cap_lens::ReadConfidentiality::from_world(w, focus)
                    .map(|v| v.present(&ctx))
            }

            // ⟲ HISTORY / UNDO — per-cell reversibility, WELDED onto the landed
            // `dregg_turn::reversible` organ (M-REV-0). The reversibility map (each
            // change-kind to this cell classified by the real Effect::invert over the
            // live ledger into clean/contextual/committed) + the cell's lifecycle
            // posture + the un-turn model. The per-cell, lens-shaped view of the same
            // reversibility the REPLAY tab time-travels for the whole image.
            MoldableLens::History => {
                starbridge_v2::history_lens::CellReversibility::from_world(w, focus)
                    .map(|v| v.present(&ctx))
            }
        }
    }

    /// THE MOLDABLE INSPECTOR — pick a focused object, render its `Registry`-resolved
    /// presentation SET as a tab-strip (one sub-tab per `Presentation`) through the
    /// generic renderer, with the `Halo` ring + a `Spotter` search box that re-focuses.
    fn moldable_panel(&self, cx: &mut Context<Self>) -> gpui::AnyElement {
        let w = self.world.borrow();
        let cells = &self.cells;
        // M3: the camera-aim is read FROM the inspector's own view cell (the §3.4
        // `render(workspace_subgraph)` selector move — the focus is a cell read, not
        // a Rust field). The free in-memory draft is the live aim.
        let focus = self.inspector_view.doc().focus().or_else(|| cells.first().copied());
        let mut col = div().flex().flex_col().gap_2().p_3().size_full().overflow_hidden();
        col = col.child(section_title(
            "INSPECTOR · the moldable presentation set (Registry · Spotter · Halo)",
        ));
        // The reflexive toggle — turn the inspector ON ITSELF (inspect the inspector).
        {
            let reflexive = self.inspector_reflexive;
            let backing_short = reflect::short_hex(self.inspector_view.backing().as_bytes());
            let rev = self.inspector_view.revision(&w);
            col = col.child(
                div()
                    .flex()
                    .items_center()
                    .gap_1()
                    .child(div().text_xs().text_color(theme::muted()).child(
                        "self-host: the inspector's (focus, present-idx) IS a witnessed cell — ",
                    ))
                    .child(cycle_chip(
                        cx,
                        "mold-reflexive",
                        if reflexive {
                            format!("⟲ inspecting ITSELF (view cell {backing_short} · rev {rev})")
                        } else {
                            "⟲ inspect the inspector".to_string()
                        },
                        if reflexive { theme::accent() } else { theme::good() },
                        Cockpit::moldable_toggle_reflexive,
                    )),
            );
        }
        col = col.child(div().text_xs().text_color(theme::muted()).child(
            "Every protocol object offers a SET of named presentations (the 7 kinds; \
             RawFields is the universal floor). Pick an object, browse its lenses across \
             the tab-strip — each rendered by the ONE generic widget per body. Search \
             every object's every presentation with the spotter; a hit re-focuses here.",
        ));

        // --- the ⌘K-style Spotter search box + its ranked hits ---
        col = col.child(
            div()
                .flex()
                .items_center()
                .gap_1()
                .child(div().text_xs().text_color(theme::muted()).child("🔍 spotter:"))
                .child(
                    div()
                        .px_2()
                        .py_0p5()
                        .rounded_md()
                        .bg(theme::panel())
                        .border_1()
                        .border_color(theme::border())
                        .text_xs()
                        .text_color(theme::text())
                        .min_w(px(220.))
                        .child(if self.moldable_query.is_empty() {
                            "(type to search every object's every presentation)".to_string()
                        } else {
                            self.moldable_query.clone()
                        }),
                )
                .child(small_button(cx, "mold-clear", "clear", theme::muted(), Cockpit::moldable_clear_query)),
        );
        // A small fixed set of example queries the operator can fire (a click drives
        // the REAL `Spotter::search` — gpui has no text input here; the box mirrors it).
        col = col.child(
            div()
                .flex()
                .flex_wrap()
                .gap_1()
                .items_center()
                .child(div().text_xs().text_color(theme::muted()).child("try:"))
                .child(cycle_chip(cx, "mold-q-life", "lifecycle".into(), theme::accent(), |this, cx| {
                    this.moldable_query = "lifecycle".into();
                    cx.notify();
                }))
                .child(cycle_chip(cx, "mold-q-graph", "ocap Graph".into(), theme::accent(), |this, cx| {
                    this.moldable_query = "ocap Graph".into();
                    cx.notify();
                }))
                .child(cycle_chip(cx, "mold-q-bal", "balance".into(), theme::accent(), |this, cx| {
                    this.moldable_query = "balance".into();
                    cx.notify();
                })),
        );
        if let Some(viewer) = focus {
            let spotter = Spotter::new(&w, viewer);
            let hits: Vec<SpotterHit> = spotter.search(&self.moldable_query);
            if !self.moldable_query.trim().is_empty() {
                let mut hits_box = div().flex().flex_col().gap_0p5().p_2().rounded_md().bg(theme::panel());
                if hits.is_empty() {
                    hits_box = hits_box.child(div().text_xs().text_color(theme::muted()).child("(no hits)"));
                }
                for (n, h) in hits.iter().take(8).enumerate() {
                    let hit_cell = h.focus.cell();
                    let id = SharedString::from(format!("mold-hit-{n}"));
                    hits_box = hits_box.child(
                        div()
                            .id(id)
                            .flex()
                            .justify_between()
                            .px_1()
                            .py_0p5()
                            .rounded_md()
                            .cursor_pointer()
                            .hover(|s| s.bg(theme::border()))
                            .on_mouse_down(
                                MouseButton::Left,
                                cx.listener(move |this, _ev, _w, cx| {
                                    this.moldable_refocus(Some(hit_cell), cx);
                                }),
                            )
                            .child(div().text_xs().text_color(theme::text()).child(format!(
                                "⬡ {} · {}",
                                reflect::short_hex(hit_cell.as_bytes()),
                                h.snippet
                            )))
                            .child(pill(format!("{} · {}", h.matched_kind.slug(), h.score), theme::accent())),
                    );
                }
                col = col.child(hits_box);
            }
        }

        // --- the object picker (cycle the focused cell) + the Halo ring ---
        let Some(focus) = focus else {
            return col
                .child(div().text_xs().text_color(theme::muted()).child("(no cells in the image yet)"))
                .into_any_element();
        };
        let reg = Registry::new(&w);
        let halo: Halo = reg.halo(FocusTarget::Cell(focus));
        col = col.child(
            div()
                .flex()
                .flex_wrap()
                .items_center()
                .gap_1()
                .child(div().text_xs().text_color(theme::muted()).child("focus:"))
                .child(cycle_chip(
                    cx,
                    "mold-focus",
                    format!("⬡ {} (cycle)", reflect::short_hex(focus.as_bytes())),
                    theme::good(),
                    Cockpit::moldable_cycle_focus,
                ))
                .child(div().text_xs().text_color(theme::muted()).child("· halo:"))
                .children(halo.commands.iter().map(|c| {
                    pill(format!("{} {}", c.glyph(), c.label()), theme::accent())
                })),
        );

        // --- the LENS-FAMILY picker — makes the newer inspector lanes (L4–L10)
        // reachable. `Cell` rides the Registry/memo spine; each other family
        // builds its real lane `Presentable` off the focused cell / the live
        // world and renders its set through the SAME generic body widget. ---
        col = col.child(
            div()
                .flex()
                .flex_wrap()
                .items_center()
                .gap_1()
                .child(div().text_xs().text_color(theme::muted()).child("lens:"))
                .child(cycle_chip(
                    cx,
                    "mold-lens",
                    format!("⌖ {} (cycle)", self.moldable_lens.label()),
                    theme::accent(),
                    Cockpit::moldable_cycle_lens,
                )),
        );

        // --- the presentation SET as a tab-strip + the rendered body ---
        // M2: the `Cell` lens projects through the memo (valid while the live head
        // is unchanged; the delta fold drops touched cells). Same `Presentation`
        // set as the pure `reg.present`, now cached (EFFICIENCY-WELD-PLAN §2.3).
        // M3: when the reflexive toggle is on, the camera-aim is the inspector's
        // OWN view cell (FocusTarget::ViewCell) — *inspect the inspector* through
        // the SAME memo + Registry dispatch. The non-`Cell` lenses build their
        // lane `Presentable` directly off the focus / the live world (the L4–L10
        // reach), rendered through the SAME generic body widget below.
        let set: Vec<Presentation> = if self.moldable_lens == MoldableLens::Cell {
            let target = if self.inspector_reflexive {
                FocusTarget::ViewCell(self.inspector_view.backing())
            } else {
                FocusTarget::Cell(focus)
            };
            match self.present_memo.present(&w, target, focus) {
                Some(s) => s,
                None => {
                    return col
                        .child(div().text_xs().text_color(theme::bad()).child(
                            "(the focused object is absent from the live image — a dangling focus)",
                        ))
                        .into_any_element();
                }
            }
        } else {
            match self.lens_present_set(&w, focus) {
                Some(s) => s,
                None => {
                    return col
                        .child(div().text_xs().text_color(theme::warn()).child(format!(
                            "(the {} lens has nothing to present over the focused object yet)",
                            self.moldable_lens.label()
                        )))
                        .into_any_element();
                }
            }
        };
        let idx = self.inspector_view.doc().present_idx().min(set.len().saturating_sub(1));
        // the tab-strip (one sub-tab per Presentation).
        let mut strip = div().flex().flex_wrap().gap_1().mt_1();
        for (i, p) in set.iter().enumerate() {
            let active = i == idx;
            let id = SharedString::from(format!("mold-sub-{i}"));
            strip = strip.child(
                div()
                    .id(id)
                    .px_2()
                    .py_0p5()
                    .rounded_md()
                    .bg(if active { theme::panel_hi() } else { theme::panel() })
                    .text_xs()
                    .text_color(if active { theme::accent() } else { theme::muted() })
                    .cursor_pointer()
                    .hover(|s| s.bg(theme::border()))
                    .on_mouse_down(
                        MouseButton::Left,
                        cx.listener(move |this, _ev, _w, cx| {
                            this.moldable_set_present_idx(i, cx);
                        }),
                    )
                    .child(format!("{} · {}", p.kind.slug(), p.label)),
            );
        }
        col = col.child(strip);
        if let Some(p) = set.get(idx) {
            col = col.child(
                div()
                    .flex()
                    .flex_col()
                    .gap_1()
                    .p_2()
                    .mt_1()
                    .rounded_md()
                    .border_1()
                    .border_color(theme::border())
                    .bg(theme::panel())
                    .child(Self::render_presentation_body(&p.body)),
            );
        }
        col.into_any_element()
    }

    // =======================================================================
    // THE ⚷ TRUST tab — the human-layer WHO-I-AM + recovery surface.
    // =======================================================================

    /// Render the TRUST tab: the WHO-I-AM identity card, the KEL rotation timeline,
    /// and the "ask your guardians" recovery gauge — the human-layer face of "you
    /// cannot lose your own OS" (human-layer M1). Built off the REAL `trust_panel`
    /// model (a representative identity until a live identity cell is wired —
    /// HORIZONLOG) and rendered through the SAME generic body widget every lens uses,
    /// so it needs no bespoke gpui.
    fn trust_tab(&self, _cx: &mut Context<Self>) -> gpui::AnyElement {
        let panel = starbridge_v2::trust_panel::TrustPanel::demo();
        let mut col = div()
            .flex()
            .flex_col()
            .gap_2()
            .p_3()
            .size_full()
            .overflow_hidden()
            .child(section_title(
                "⚷ TRUST · who-i-am — your devices, your guardians, your recovery",
            ))
            .child(
                div()
                    .text_xs()
                    .text_color(theme::muted())
                    .child(panel.summary()),
            );
        for p in panel.present() {
            col = col.child(
                div()
                    .flex()
                    .flex_col()
                    .gap_1()
                    .p_2()
                    .mt_1()
                    .rounded_md()
                    .border_1()
                    .border_color(theme::border())
                    .bg(theme::panel())
                    .child(
                        div()
                            .text_xs()
                            .text_color(theme::accent())
                            .child(format!("{} · {}", p.kind.slug(), p.label)),
                    )
                    .child(Self::render_presentation_body(&p.body)),
            );
        }
        col.into_any_element()
    }

    // =======================================================================
    // THE INSPECT→ACT loop panel.
    // =======================================================================

    /// THE INSPECT→ACT loop — the focused object's reflected state + the messages it
    /// understands (cap-badged), sending one as a REAL verified turn + re-inspecting.
    fn inspect_act_panel(&self, cx: &mut Context<Self>) -> gpui::AnyElement {
        let w = self.world.borrow();
        let cells = &self.cells;
        let focus = self.inspect_act_focus.or_else(|| cells.first().copied());
        let mut col = div().flex().flex_col().gap_2().p_3().size_full().overflow_hidden();
        col = col.child(section_title("INSPECT-ACT · the messages it understands → send → re-inspect"));
        col = col.child(div().text_xs().text_color(theme::muted()).child(
            "The Smalltalk inspect→act→inspect loop: an inspected object shows the messages \
             it understands inline (cap-badged for the viewer), you send one as a REAL verified \
             turn, and the post-state re-inspects. A refused send is shown in-band, never swallowed.",
        ));
        let Some(focus) = focus else {
            return col.child(div().text_xs().text_color(theme::muted()).child("(no cells yet)")).into_any_element();
        };
        col = col.child(
            div()
                .flex()
                .items_center()
                .gap_1()
                .child(div().text_xs().text_color(theme::muted()).child("focus:"))
                .child(cycle_chip(
                    cx,
                    "ia-focus",
                    format!("⬡ {} (cycle)", reflect::short_hex(focus.as_bytes())),
                    theme::good(),
                    Cockpit::inspect_act_cycle_focus,
                )),
        );

        // Build the genuine inspect→act view for the viewer (the cockpit acts as the
        // focused cell itself — the highest authority over its own window).
        let ia = InspectAct::build(&w, InspectFocus::Cell(focus), focus, dregg_cell::AuthRequired::Either);
        if let Some(insp) = &ia.inspectable {
            col = col.child(section_title("inspected state"));
            col = col.child(inspectable_row(insp));
        }
        col = col.child(section_title("messages understood"));
        if ia.messages.is_empty() {
            col = col.child(div().text_xs().text_color(theme::muted()).child("(no messages)"));
        }
        for m in &ia.messages {
            let name = m.name.clone();
            let (badge, badge_color) = if m.authorized {
                ("you may send", theme::good())
            } else {
                ("refused: insufficient authority", theme::bad())
            };
            let id = SharedString::from(format!("ia-send-{name}"));
            let row = div()
                .flex()
                .justify_between()
                .items_center()
                .px_2()
                .py_0p5()
                .rounded_md()
                .bg(theme::panel())
                .child(
                    div()
                        .flex()
                        .flex_col()
                        .child(div().text_xs().text_color(theme::text()).child(format!("⟶ {} · {}", m.name, m.effect)))
                        .child(div().text_xs().text_color(theme::muted()).child(format!("requires {:?}", m.required))),
                )
                .child(
                    div()
                        .flex()
                        .items_center()
                        .gap_1()
                        .child(pill(badge, badge_color))
                        .when(m.authorized, |d| {
                            let send_name = name.clone();
                            d.child(
                                div()
                                    .id(id)
                                    .px_2()
                                    .py_0p5()
                                    .rounded_md()
                                    .bg(theme::panel_hi())
                                    .border_1()
                                    .border_color(theme::border())
                                    .text_xs()
                                    .text_color(theme::accent())
                                    .cursor_pointer()
                                    .hover(|s| s.bg(theme::border()))
                                    .on_mouse_down(
                                        MouseButton::Left,
                                        cx.listener(move |this, _ev, _w, cx| {
                                            this.inspect_act_send(&send_name, cx);
                                        }),
                                    )
                                    .child("send"),
                            )
                        }),
                );
            col = col.child(row);
        }
        if let Some(b) = &self.inspect_act_outcome {
            let color = if b.contains("REFUSED") { theme::bad() } else { theme::good() };
            col = col.child(div().mt_1().p_2().rounded_md().bg(theme::panel()).text_xs().text_color(color).child(b.clone()));
        }
        col.into_any_element()
    }

    // =======================================================================
    // THE WORKSPACE panel — doIt / printIt / inspectIt.
    // =======================================================================

    /// THE WORKSPACE — compose an intent, evaluate it in a forked throwaway world
    /// (doIt = predict, never mutate), print the predicted receipt (printIt), inspect
    /// the predicted post-state as live objects (inspectIt), then commit-or-discard.
    fn workspace_panel(&self, cx: &mut Context<Self>) -> gpui::AnyElement {
        let cells = &self.cells;
        let target = cells.get(self.workspace_target_idx).copied().unwrap_or(self.workspace.draft().agent);
        let mut col = div().flex().flex_col().gap_2().p_3().size_full().overflow_hidden();
        col = col.child(section_title("WORKSPACE · doIt · printIt · inspectIt"));
        col = col.child(div().text_xs().text_color(theme::muted()).child(
            "The live evaluator: compose an expression (a turn), doIt to evaluate it in a \
             FORKED throwaway world (predict, never mutate), printIt to echo the predicted \
             receipt, inspectIt to browse the predicted post-state as live objects, then \
             commit-for-real or discard. The live image is untouched until commit.",
        ));

        // the expression composer.
        let agent_short = reflect::short_hex(&self.workspace.draft().agent.0);
        let n_actions = self.workspace.draft().actions.len();
        let n_effects = self.workspace.draft().effect_count();
        col = col.child(
            div()
                .flex()
                .flex_wrap()
                .items_center()
                .gap_1()
                .child(div().text_xs().text_color(theme::muted()).child(format!("agent {agent_short} ·")))
                .child(div().text_xs().text_color(theme::muted()).child("transfer 100 →"))
                .child(cycle_chip(
                    cx,
                    "ws-target",
                    format!("⬡ {} (cycle)", reflect::short_hex(&target.0)),
                    theme::good(),
                    Cockpit::workspace_cycle_target,
                ))
                .child(small_button(cx, "ws-add", "+ add transfer", theme::good(), Cockpit::workspace_add_transfer))
                .child(small_button(cx, "ws-clear", "clear", theme::muted(), Cockpit::workspace_clear)),
        );
        col = col.child(
            div()
                .flex()
                .gap_1()
                .child(pill(format!("{n_actions} action(s)"), theme::accent()))
                .child(pill(format!("{n_effects} effect(s)"), theme::accent())),
        );

        // the doIt / commit / discard verbs.
        let can_commit = self.workspace.can_commit();
        col = col.child(
            div()
                .flex()
                .flex_wrap()
                .gap_1()
                .child(small_button(cx, "ws-doit", "▶ doIt (evaluate)", theme::accent(), Cockpit::workspace_do_it))
                .child({
                    let (label, color) = if can_commit {
                        ("✓ commit for real", theme::good())
                    } else {
                        ("✓ commit (doIt first)", theme::muted())
                    };
                    small_button(cx, "ws-commit", label, color, Cockpit::workspace_commit)
                })
                .child(small_button(cx, "ws-discard", "discard", theme::muted(), Cockpit::workspace_discard)),
        );

        // printIt + inspectIt.
        if let Some(eval) = self.workspace.last() {
            let printed = eval.print_it();
            let color = if printed.contains("REFUSED") { theme::bad() } else { theme::good() };
            col = col.child(section_title("printIt"));
            col = col.child(div().p_2().rounded_md().bg(theme::panel()).text_xs().text_color(color).child(printed));
            let inspected = eval.inspect_it();
            if !inspected.is_empty() {
                col = col.child(section_title("inspectIt · predicted post-state"));
                let mut ibox = div().flex().flex_col().gap_1().max_h(px(260.)).overflow_hidden();
                for ins in inspected.iter().take(8) {
                    ibox = ibox.child(inspectable_row(ins));
                }
                col = col.child(ibox);
            }
        } else {
            col = col.child(div().text_xs().text_color(theme::muted()).child("(no evaluation yet — press ▶ doIt)"));
        }
        if let Some(b) = &self.lane_outcome {
            // shared commit banner reuse is avoided; the workspace uses its own echo above.
            let _ = b;
        }
        col.into_any_element()
    }

    // =======================================================================
    // THE WONDER ROOM panel — the AOL glowing-cell room.
    // =======================================================================

    /// THE WONDER ROOM — the AOL-wonder front door: every cell a pokeable glowing
    /// object (glow = real recent activity), with the direct-manipulation halo ring.
    fn wonder_panel(&self, cx: &mut Context<Self>) -> gpui::AnyElement {
        let w = self.world.borrow();
        let room = WonderRoom::build(&w);
        let mut col = div().flex().flex_col().gap_2().p_3().size_full().overflow_hidden();
        col = col.child(section_title("WONDER · every cell a glowing pokeable object"));
        col = col.child(div().text_xs().text_color(theme::muted()).child(
            "The AOL-wonder front door: click around, absorb, no comprehension needed. Every \
             cell GLOWS with its real recent activity; each carries the universal halo \
             (inspect · grab · explain). A brighter cell did more, lately.",
        ));

        // the glowing-cell grid.
        let mut grid = div().flex().flex_wrap().gap_2().mt_1();
        for id in &self.cells {
            let Some(gc) = room.cell(id) else { continue };
            let glowing = gc.is_glowing();
            let (border, text) = if glowing {
                (theme::accent(), theme::text())
            } else {
                (theme::border(), theme::muted())
            };
            let cell_id = *id;
            let dom = SharedString::from(format!("wonder-{}", reflect::short_hex(id.as_bytes())));
            grid = grid.child(
                div()
                    .id(dom)
                    .flex()
                    .flex_col()
                    .items_center()
                    .gap_0p5()
                    .px_3()
                    .py_2()
                    .rounded_md()
                    .bg(theme::panel())
                    .border_1()
                    .border_color(border)
                    .cursor_pointer()
                    .hover(|s| s.bg(theme::panel_hi()))
                    .on_mouse_down(
                        MouseButton::Left,
                        cx.listener(move |this, _ev, _w, cx| {
                            // poke = inspect: re-focus the moldable inspector on it
                            // (a witnessed re-aim of the inspector's own view cell).
                            this.inspector_reflexive = false;
                            this.tab = Tab::Moldable;
                            this.moldable_refocus(Some(cell_id), cx);
                        }),
                    )
                    .child(div().text_lg().text_color(if glowing { theme::accent() } else { theme::muted() }).child(if glowing { "✦" } else { "○" }))
                    .child(div().text_xs().text_color(text).child(reflect::short_hex(id.as_bytes())))
                    .child(div().text_xs().text_color(theme::muted()).child(if glowing { "glowing" } else { "quiet" })),
            );
        }
        col = col.child(grid);

        // explain the brightest cell (a plain-sentence "what just happened here").
        if let Some(bright) = room.brightest() {
            if let Some(sentence) = room.explain(&bright.cell) {
                col = col.child(section_title("the brightest cell explains itself"));
                col = col.child(div().p_2().rounded_md().bg(theme::panel()).text_xs().text_color(theme::text()).child(sentence));
            }
        }
        col = col.child(div().text_xs().text_color(theme::muted()).mt_1().child("(click a cell to inspect it in the moldable INSPECTOR)"));
        col.into_any_element()
    }

    // =======================================================================
    // THE LANES panel — the gadget surfaces (validate→predict→commit / build).
    // =======================================================================

    /// THE LANES — the moldable-inspector gadgets made reachable: the predicate
    /// composer, the turn builder, the attenuation dial, and the macaroon token loop.
    /// Each drives its REAL model methods; a refusal is surfaced as a feature.
    fn lanes_panel(&self, cx: &mut Context<Self>) -> gpui::AnyElement {
        let mut col = div().flex().flex_col().gap_2().p_3().size_full().overflow_hidden();
        col = col.child(section_title("LANES · the moldable gadgets (validate → predict → commit)"));
        // the lane selector.
        let names = ["predicate composer", "turn builder", "attenuation dial", "token loop"];
        let mut strip = div().flex().flex_wrap().gap_1();
        for (i, name) in names.iter().enumerate() {
            let active = i == self.lane_idx;
            let id = SharedString::from(format!("lane-sel-{i}"));
            strip = strip.child(
                div()
                    .id(id)
                    .px_2()
                    .py_0p5()
                    .rounded_md()
                    .bg(if active { theme::panel_hi() } else { theme::panel() })
                    .text_xs()
                    .text_color(if active { theme::accent() } else { theme::muted() })
                    .cursor_pointer()
                    .hover(|s| s.bg(theme::border()))
                    .on_mouse_down(
                        MouseButton::Left,
                        cx.listener(move |this, _ev, _w, cx| {
                            this.lane_idx = i;
                            this.lane_outcome = None;
                            cx.notify();
                        }),
                    )
                    .child(*name),
            );
        }
        col = col.child(strip);

        col = col.child(match self.lane_idx {
            0 => self.lane_predicate(cx),
            1 => self.lane_turn(cx),
            2 => self.lane_cap(cx),
            _ => self.lane_token(cx),
        });

        if let Some(b) = &self.lane_outcome {
            let color = if b.contains("REFUSED") || b.contains("DENIED") || b.contains("incomplete") {
                theme::bad()
            } else {
                theme::good()
            };
            col = col.child(div().mt_1().p_2().rounded_md().bg(theme::panel()).text_xs().text_color(color).child(b.clone()));
        }
        col.into_any_element()
    }

    /// LANE 0 — the predicate composer (the caveat-language gadget). Drives the REAL
    /// `validate`/`build`, showing the live fail-closed verdict + the source prose +
    /// cost class. A vacuous/strippable caveat is REFUSED (surfaced as a feature).
    fn lane_predicate(&self, cx: &mut Context<Self>) -> gpui::AnyElement {
        let validation = predicate_composer::validate(&self.lane_composite);
        let mut col = div().flex().flex_col().gap_1().mt_1();
        col = col.child(div().text_xs().text_color(theme::muted()).child(
            "Compose a predicate caveat from real atoms; validate() runs the genuine \
             non-vacuity / anti-strip / cost check; build() lowers to the protocol \
             StateConstraint. A vacuous or proof-strippable caveat is refused.",
        ));
        // a few pickable atoms — each replaces the composite (a Leaf) and re-validates.
        col = col.child(
            div()
                .flex()
                .flex_wrap()
                .gap_1()
                .items_center()
                .child(div().text_xs().text_color(theme::muted()).child("atom:"))
                .child(cycle_chip(cx, "lp-bgte", "balance ≥ 100".into(), theme::accent(), |this, cx| {
                    this.lane_composite = Composite::Leaf(Atom::BalanceGte { min: 100 });
                    this.lane_outcome = None;
                    cx.notify();
                }))
                .child(cycle_chip(cx, "lp-blte", "balance ≤ 1000".into(), theme::accent(), |this, cx| {
                    this.lane_composite = Composite::Leaf(Atom::BalanceLte { max: 1000 });
                    this.lane_outcome = None;
                    cx.notify();
                }))
                .child(cycle_chip(cx, "lp-feq", "slot 0 = 7".into(), theme::accent(), |this, cx| {
                    this.lane_composite = Composite::Leaf(Atom::FieldEquals { index: 0, value: 7 });
                    this.lane_outcome = None;
                    cx.notify();
                }))
                .child(cycle_chip(cx, "lp-empty", "∅ AnyOf (vacuous!)".into(), theme::warn(), |this, cx| {
                    this.lane_composite = Composite::AnyOf(vec![]);
                    this.lane_outcome = None;
                    cx.notify();
                })),
        );
        // the live verdict.
        let composer = PredicateComposer::new(
            self.anchors[0],
            self.anchors[0],
            self.lane_composite.clone(),
        );
        let (vtext, vcolor) = match composer.build() {
            Ok(c) => (format!("✓ buildable · lowers to {c:?}"), theme::good()),
            Err(e) => (format!("REFUSED · {e:?}"), theme::bad()),
        };
        col = col.child(div().p_2().rounded_md().bg(theme::panel()).text_xs().text_color(vcolor).child(vtext));
        col = col.child(div().text_xs().text_color(theme::muted()).child(format!("validate(): {validation:?}")));
        // the source prose (the "what-is" face).
        if let Ok(c) = composer.build() {
            let refl = predicate_composer::ReflectedConstraint::new(c);
            col = col.child(section_title("source"));
            col = col.child(div().p_2().rounded_md().bg(theme::panel()).text_xs().text_color(theme::text()).child(refl.source_prose()));
            col = col.child(Self::render_presentation_body(&PresentationBody::Trace(refl.trace())));
        }
        col.into_any_element()
    }

    /// LANE 1 — the committing turn builder. Drives the REAL `validate`/`predict`,
    /// showing the live fail-closed verdict + the predicted outcome (no commit here —
    /// the SIMULATE/COMPOSER tabs commit; this lane demonstrates the gadget shape).
    fn lane_turn(&self, cx: &mut Context<Self>) -> gpui::AnyElement {
        let w = self.world.borrow();
        let mut col = div().flex().flex_col().gap_1().mt_1();
        col = col.child(div().text_xs().text_color(theme::muted()).child(
            "The committing turn gadget: build a call-forest, validate() the well-formedness \
             floor, then predict() its consequences in a fork (the same IntentDraft → simulate \
             spine). An empty/malformed turn cannot build.",
        ));
        col = col.child(
            div()
                .flex()
                .flex_wrap()
                .gap_1()
                .items_center()
                .child(div().text_xs().text_color(theme::muted()).child("agent:"))
                .child(pill(reflect::short_hex(&self.lane_turn.agent_cell().0), theme::accent()))
                .child(small_button(cx, "lt-add", "+ add transfer action", theme::good(), Cockpit::lane_turn_add))
                .child(small_button(cx, "lt-clear", "clear", theme::muted(), Cockpit::lane_turn_clear)),
        );
        col = col.child(
            div()
                .flex()
                .gap_1()
                .child(pill(format!("{} action(s)", self.lane_turn.draft().actions.len()), theme::accent()))
                .child(pill(format!("{} effect(s)", self.lane_turn.effect_count()), theme::accent())),
        );
        // the live validate() + predict().
        let (vtext, vcolor) = match self.lane_turn.validate() {
            starbridge_v2::GadgetValidation::Ok => ("✓ validate(): Ok".to_string(), theme::good()),
            starbridge_v2::GadgetValidation::Invalid { reason } => (format!("REFUSED · {reason}"), theme::bad()),
        };
        col = col.child(div().p_2().rounded_md().bg(theme::panel()).text_xs().text_color(vcolor).child(vtext));
        col = col.child(section_title("predict()"));
        let predicted = starbridge_v2::turn_builder::render_prediction(&self.lane_turn, &w);
        col = col.child(div().p_2().rounded_md().bg(theme::panel()).text_xs().text_color(theme::text()).child(predicted));
        col.into_any_element()
    }

    /// LANE 2 — the attenuation dial (the cap-attenuation value gadget). Drives the
    /// REAL `is_attenuation` check; an amplifying designation is REFUSED.
    fn lane_cap(&self, cx: &mut Context<Self>) -> gpui::AnyElement {
        let mut col = div().flex().flex_col().gap_1().mt_1();
        col = col.child(div().text_xs().text_color(theme::muted()).child(
            "The attenuation dial: pick a narrower rights tier; the dial's build() runs the \
             REAL is_attenuation lattice check, refusing any tier that would AMPLIFY the held \
             ceiling. Granting mints a real attenuated cap through the powerbox.",
        ));
        let Some(dial) = &self.lane_dial else {
            return col
                .child(div().text_xs().text_color(theme::warn()).child(
                    "(the cockpit principal holds no firmament cap to attenuate — the lane is honest about the absence)",
                ))
                .into_any_element();
        };
        col = col.child(
            div()
                .flex()
                .flex_wrap()
                .gap_1()
                .items_center()
                .child(div().text_xs().text_color(theme::muted()).child(format!("ceiling {:?} · designate:", dial.ceiling()))),
        );
        col = col.child(
            div()
                .flex()
                .flex_wrap()
                .gap_1()
                .child(cycle_chip(cx, "lc-sig", "Signature".into(), theme::accent(), |this, cx| {
                    this.lane_dial_set("Signature", cx);
                }))
                .child(cycle_chip(cx, "lc-proof", "Proof".into(), theme::accent(), |this, cx| {
                    this.lane_dial_set("Proof", cx);
                }))
                .child(cycle_chip(cx, "lc-imposs", "Impossible (narrowest)".into(), theme::accent(), |this, cx| {
                    this.lane_dial_set("Impossible", cx);
                }))
                .child(cycle_chip(cx, "lc-none", "None (amplify! refused)".into(), theme::warn(), |this, cx| {
                    this.lane_dial_set("None", cx);
                })),
        );
        let (vtext, vcolor) = match dial.build() {
            Ok(c) => (format!("✓ buildable attenuated cap · rights {:?}", c.rights), theme::good()),
            Err(e) => (format!("REFUSED · {e:?}"), theme::bad()),
        };
        col = col.child(div().p_2().rounded_md().bg(theme::panel()).text_xs().text_color(vcolor).child(vtext));
        col.into_any_element()
    }

    /// LANE 3 — the macaroon token loop (a verifier gadget). build() runs the REAL
    /// mint → attenuate → delegate → discharge crypto end-to-end + returns the verdict.
    fn lane_token(&self, cx: &mut Context<Self>) -> gpui::AnyElement {
        let mut col = div().flex().flex_col().gap_1().mt_1();
        col = col.child(div().text_xs().text_color(theme::muted()).child(
            "The macaroon loop: mint a root token, attenuate (confine to a service/action), \
             delegate, and DISCHARGE service-side — build() runs the REAL cipherclerk crypto \
             (HMAC chain + caveat evaluation) and returns the live verdict.",
        ));
        col = col.child(
            div()
                .flex()
                .gap_1()
                .child(small_button(cx, "ltok-run", "▶ run the loop (build)", theme::accent(), Cockpit::lane_token_run)),
        );
        col.into_any_element()
    }

    // =======================================================================
    // THE ⤳ SHARE panel — the FRUSTUM / SNAPSHOT EDITOR (the share-with-attenuation
    // surface): cull the frustum · pare the authority · verify live · share.
    // =======================================================================

    /// THE ⤳ SHARE surface — sculpt a UI-slice snapshot of the focused view, pare
    /// its authority (the REAL [`AttenuationDial`] over `is_attenuation`), watch the
    /// membrane-projected per-viewer preview live, then mint a revocable, attenuated,
    /// rehydratable artifact. The GitHub-org-settings cap UX over the sound substrate
    /// (`docs/desktop-os-research/REHYDRATABLE-SURFACES.md`). gpui-free model below.
    fn share_panel(&self, cx: &mut Context<Self>) -> gpui::AnyElement {
        let mut col = div().flex().flex_col().gap_2().p_3().size_full().overflow_hidden();
        col = col.child(section_title(
            "⤳ SHARE · sculpt → pare → verify → extend a revocable attenuated right to re-view",
        ));
        col = col.child(div().text_xs().text_color(theme::muted()).child(
            "\"Sharing a screenshot\" becomes \"extending a revocable, attenuated, audited \
             right to re-view a witnessed slice.\" CULL the frustum (which lenses / \
             sub-objects are in the slice — visibility) · PARE the authority (the role, \
             on the REAL attenuation lattice — a widening is REFUSED in-band) · VERIFY \
             live (the membrane projects what each recipient would actually see) · SHARE.",
        ));

        let Some(editor) = &self.share_editor else {
            // No editor yet — the call-to-action: capture the focused view.
            let focus = self
                .inspector_view
                .doc()
                .focus()
                .or_else(|| self.cells.first().copied());
            let focus_label = focus
                .map(|c| reflect::short_hex(c.as_bytes()))
                .unwrap_or_else(|| "(no focus)".to_string());
            return col
                .child(div().mt_2().text_xs().text_color(theme::text()).child(format!(
                    "focused object: {focus_label} — capture this view to open the share editor."
                )))
                .child(
                    div().mt_1().child(small_button(
                        cx,
                        "share-capture",
                        "📸 capture this view (open the editor)",
                        theme::accent(),
                        Cockpit::share_capture,
                    )),
                )
                .into_any_element();
        };

        // ── the captured snapshot header (focus + lens + the witness cursor) ──
        let snap = editor.snapshot();
        col = col.child(
            div()
                .flex()
                .flex_wrap()
                .gap_1()
                .items_center()
                .child(div().text_xs().text_color(theme::muted()).child("captured slice:"))
                .child(pill(format!("focus {}", reflect::short_hex(snap.focus.cell().as_bytes())), theme::accent()))
                .child(pill(format!("lens {}", snap.kind.slug()), theme::accent()))
                .child(pill(format!("@ height {}", snap.cursor.height), theme::muted()))
                .child(small_button(cx, "share-recapture", "↺ recapture focus", theme::muted(), Cockpit::share_capture)),
        );

        // ── 1. CULL THE FRUSTUM (visibility) ─────────────────────────────────
        col = col.child(section_title("1 · cull the frustum (visibility — what's in the slice)"));
        // lens toggles.
        let mut lens_row = div().flex().flex_wrap().gap_1().items_center()
            .child(div().text_xs().text_color(theme::muted()).child("lenses:"));
        for lens in starbridge_v2::snapshot_editor::ALL_LENSES {
            let inside = editor.frustum().has_lens(lens);
            let id = SharedString::from(format!("share-lens-{}", lens.slug()));
            let slug = lens.slug().to_string();
            lens_row = lens_row.child(
                div()
                    .id(id)
                    .px_2()
                    .py_0p5()
                    .rounded_md()
                    .bg(if inside { theme::panel_hi() } else { theme::panel() })
                    .text_xs()
                    .text_color(if inside { theme::good() } else { theme::muted() })
                    .cursor_pointer()
                    .hover(|s| s.bg(theme::border()))
                    .on_mouse_down(
                        MouseButton::Left,
                        cx.listener(move |this, _ev, _w, cx| this.share_cull_lens(&slug, cx)),
                    )
                    .child(format!("{} {}", if inside { "✓" } else { "○" }, lens.slug())),
            );
        }
        col = col.child(lens_row);
        // affordance (sub-object) toggles.
        let mut aff_row = div().flex().flex_wrap().gap_1().items_center()
            .child(div().text_xs().text_color(theme::muted()).child("sub-objects:"));
        for name in editor.frustum().captured_affordances() {
            let inside = editor.frustum().has_affordance(name);
            let id = SharedString::from(format!("share-aff-{name}"));
            let nm = name.clone();
            aff_row = aff_row.child(
                div()
                    .id(id)
                    .px_2()
                    .py_0p5()
                    .rounded_md()
                    .bg(if inside { theme::panel_hi() } else { theme::panel() })
                    .text_xs()
                    .text_color(if inside { theme::good() } else { theme::muted() })
                    .cursor_pointer()
                    .hover(|s| s.bg(theme::border()))
                    .on_mouse_down(
                        MouseButton::Left,
                        cx.listener(move |this, _ev, _w, cx| this.share_cull_affordance(&nm, cx)),
                    )
                    .child(format!("{} {name}", if inside { "✓" } else { "○" })),
            );
        }
        col = col.child(aff_row);

        // ── 2. PARE THE AUTHORITY (the role, on the lattice) ─────────────────
        col = col.child(section_title("2 · pare the authority (the recipient's role — attenuation-only)"));
        let mut role_row = div().flex().flex_wrap().gap_1().items_center()
            .child(div().text_xs().text_color(theme::muted()).child(format!(
                "held ceiling {:?} · grant the recipient:", editor.held().rights()
            )));
        for slug in editor.pare_choices() {
            let id = SharedString::from(format!("share-pare-{slug}"));
            let s = slug.clone();
            // A choice that would amplify the held ceiling is colored as a warning
            // (it will be REFUSED in-band when picked — surfaced, never silent).
            role_row = role_row.child(
                div()
                    .id(id)
                    .px_2()
                    .py_0p5()
                    .rounded_md()
                    .bg(theme::panel())
                    .text_xs()
                    .text_color(theme::accent())
                    .cursor_pointer()
                    .hover(|s| s.bg(theme::border()))
                    .on_mouse_down(
                        MouseButton::Left,
                        cx.listener(move |this, _ev, _w, cx| this.share_pare(&s, cx)),
                    )
                    .child(slug),
            );
        }
        col = col.child(role_row);

        // ── 3. LIVE VERIFICATION (the membrane-projected preview) ────────────
        col = col.child(section_title("3 · verify (the membrane projects what each recipient sees)"));
        let v = editor.verify();
        let (vtext, vcolor) = if v.sound {
            (
                format!("✓ SOUND attenuation · recipient role {:?} ⊆ held (is_attenuation holds)", v.pared_rights),
                theme::good(),
            )
        } else {
            (
                "✗ NOT a sound attenuation yet — pick a role ⊆ the held ceiling (a widening is refused)".to_string(),
                theme::bad(),
            )
        };
        col = col.child(div().p_2().rounded_md().bg(theme::panel()).text_xs().text_color(vcolor).child(vtext));
        // the preview-as toggle (which recipient member we preview).
        let preview_wide = self.share_preview_wide;
        col = col.child(
            div()
                .flex()
                .flex_wrap()
                .gap_1()
                .items_center()
                .child(div().text_xs().text_color(theme::muted()).child("preview as:"))
                .child(small_button(
                    cx,
                    "share-preview-toggle",
                    if preview_wide { "a WIDE recipient (Either)" } else { "a NARROW recipient (Signature)" },
                    theme::accent(),
                    Cockpit::share_toggle_preview,
                )),
        );
        // the genuine membrane-projected preview for the chosen recipient tier.
        let preview = self.share_recipient_preview(editor);
        let lens_names: Vec<String> = v.recipient_lenses.iter().map(|l| l.slug().to_string()).collect();
        col = col.child(
            div()
                .p_2()
                .rounded_md()
                .bg(theme::panel())
                .flex()
                .flex_col()
                .gap_0p5()
                .child(div().text_xs().text_color(theme::muted()).child(format!(
                    "this recipient would SEE — lenses: [{}]",
                    lens_names.join(", ")
                )))
                .child(div().text_xs().text_color(theme::text()).child(format!(
                    "affordances (membrane-projected through is_attenuation, frustum-confined): [{}]",
                    if preview.is_empty() { "(nothing)".to_string() } else { preview.join(", ") }
                ))),
        );

        // ── 4. SHARE (mint the revocable artifact) ───────────────────────────
        col = col.child(section_title("4 · share (extend the revocable, attenuated, audited right)"));
        col = col.child(
            div().child(small_button(
                cx,
                "share-mint",
                "⤳ share this slice (mint the revocable artifact)",
                if v.sound { theme::good() } else { theme::muted() },
                Cockpit::share_mint,
            )),
        );

        if let Some(b) = &self.share_outcome {
            let color = if b.contains("REFUSED") || b.contains("amplif") || b.contains("AMPLIFY") {
                theme::bad()
            } else {
                theme::good()
            };
            col = col.child(div().mt_1().p_2().rounded_md().bg(theme::panel()).text_xs().text_color(color).child(b.clone()));
        }

        // ── the audit trail of minted artifacts (members of the org) ─────────
        if !self.share_artifacts.is_empty() {
            col = col.child(section_title("shared artifacts (the audit trail — revocable per recipient)"));
            let mut list = div().flex().flex_col().gap_1().max_h(px(220.)).overflow_hidden();
            for (i, art) in self.share_artifacts.iter().enumerate() {
                let live = art.is_live();
                let id = SharedString::from(format!("share-revoke-{i}"));
                let mut row = div()
                    .flex()
                    .flex_wrap()
                    .items_center()
                    .gap_1()
                    .p_1()
                    .rounded_md()
                    .bg(theme::panel())
                    .child(pill(
                        format!("slice → {} · role {:?}", reflect::short_hex(art.backing.as_bytes()), art.attenuated_rights),
                        if live { theme::accent() } else { theme::muted() },
                    ))
                    .child(pill(
                        format!("{} sub-object(s)", art.affordance_scope.affordance_names.len()),
                        theme::muted(),
                    ))
                    .child(pill(if live { "LIVE" } else { "REVOKED" }.to_string(), if live { theme::good() } else { theme::bad() }));
                if live {
                    row = row.child(
                        div()
                            .id(id)
                            .px_2()
                            .py_0p5()
                            .rounded_md()
                            .bg(theme::panel_hi())
                            .text_xs()
                            .text_color(theme::bad())
                            .cursor_pointer()
                            .hover(|s| s.bg(theme::border()))
                            .on_mouse_down(
                                MouseButton::Left,
                                cx.listener(move |this, _ev, _w, cx| this.share_revoke(i, cx)),
                            )
                            .child("⊘ revoke"),
                    );
                }
                list = list.child(row);
            }
            col = col.child(list);
        }

        col.into_any_element()
    }

    /// Build a real native [`AffordanceSurface`] over `cell` — the four-tier shape
    /// (view / comment / edit / admin) that genuinely exercises the membrane
    /// (`is_attenuation` divides them per recipient). Each affordance fires a REAL
    /// `dregg_turn::Effect`; the surface is the witness-graph the membrane projects
    /// through. The same htmx-on-crack shape `web_cells` publishes, native here.
    fn share_surface_for(cell: CellId) -> AffordanceSurface {
        use dregg_cell::AuthRequired;
        use dregg_turn::action::{Effect, Event};
        AffordanceSurface::new(cell)
            .declare(CellAffordance::new(
                "view",
                AuthRequired::Signature, // tier-1: any signer
                Effect::EmitEvent { cell, event: Event::new([1u8; 32], vec![]) },
            ))
            .declare(CellAffordance::new(
                "comment",
                AuthRequired::Either, // tier-2: the editor tier
                Effect::EmitEvent { cell, event: Event::new([2u8; 32], vec![]) },
            ))
            .declare(CellAffordance::new(
                "edit",
                AuthRequired::Either, // tier-2: a real SetField write
                Effect::SetField { cell, index: 1, value: [7u8; 32] },
            ))
            .declare(CellAffordance::new(
                "admin",
                AuthRequired::None, // tier-3: only the root holder clears it
                Effect::IncrementNonce { cell },
            ))
    }

    /// The membrane-projected preview for the chosen recipient tier — the REAL
    /// per-viewer slice (`AffordanceSnapshot::rehydrate_for` through `is_attenuation`,
    /// frustum-confined). The preview-as toggle picks WIDE (Either) vs NARROW
    /// (Signature) — the two members the org-settings page lets you "view as".
    fn share_recipient_preview(&self, editor: &SnapshotEditor) -> Vec<String> {
        let backing = editor.snapshot().focus.cell();
        let rights = if self.share_preview_wide {
            dregg_cell::AuthRequired::Either
        } else {
            dregg_cell::AuthRequired::Signature
        };
        let recipient = recipient_window_cap(SurfaceId(0xA1), backing, rights);
        editor.preview_for(&recipient)
    }

    // =======================================================================
    // THE HANDLERS — the `&mut Cockpit` verbs the new panels' buttons call. Each
    // drives a REAL model method; a refusal is captured into the panel's banner.
    // =======================================================================

    /// ⤳ CAPTURE — pause the camera on the focused view and OPEN the share editor.
    /// Takes a REAL [`UiSnapshot`] of the focused cell at the live head, builds the
    /// native four-tier affordance surface, and mints a held window cap over it (the
    /// attenuation ceiling). Re-captures fresh so the editor tracks the live focus.
    fn share_capture(&mut self, cx: &mut Context<Self>) {
        let world = self.world.borrow();
        let Some(focus) = self
            .inspector_view
            .doc()
            .focus()
            .or_else(|| self.cells.first().copied())
        else {
            self.share_outcome = Some("REFUSED · no focused cell to capture".to_string());
            drop(world);
            cx.notify();
            return;
        };
        // The captured snapshot — the inspector's own paused camera (we carry it).
        let snap = UiSnapshot::capture(&world, FocusTarget::Cell(focus), PresentationKind::Affordances);
        drop(world);
        let surface = Self::share_surface_for(focus);
        // The held window cap = the ceiling. The cockpit principal holds the broad
        // root tier over the focused surface (it is the operator); the pare narrows
        // from there. (A narrower honest ceiling would only restrict the dial more.)
        let held = recipient_window_cap(SurfaceId(0xA1), focus, dregg_cell::AuthRequired::None);
        let n_aff = surface.all_names().len();
        self.share_editor = Some(SnapshotEditor::open(snap, surface, held));
        self.share_outcome = Some(format!(
            "captured the focused view ({}) — {n_aff} sub-object(s), every lens, the full slice. Now cull + pare.",
            reflect::short_hex(focus.as_bytes())
        ));
        cx.notify();
    }

    /// Cull a presentation LENS in/out of the shared slice (visibility).
    fn share_cull_lens(&mut self, slug: &str, cx: &mut Context<Self>) {
        if let Some(ed) = &mut self.share_editor {
            if let Some(lens) = starbridge_v2::snapshot_editor::ALL_LENSES
                .into_iter()
                .find(|l| l.slug() == slug)
            {
                let inside = ed.cull_lens(lens);
                self.share_outcome = Some(format!(
                    "lens `{slug}` {} the shared slice",
                    if inside { "→ added back to" } else { "← culled OUT of" }
                ));
            }
        }
        cx.notify();
    }

    /// Cull an affordance SUB-OBJECT in/out of the shared slice (visibility).
    fn share_cull_affordance(&mut self, name: &str, cx: &mut Context<Self>) {
        if let Some(ed) = &mut self.share_editor {
            let inside = ed.cull_affordance(name);
            self.share_outcome = Some(format!(
                "sub-object `{name}` {} the shared slice",
                if inside { "→ added back to" } else { "← culled OUT of" }
            ));
        }
        cx.notify();
    }

    /// PARE the authority to a rights tier — the REAL [`AttenuationDial`]. An
    /// amplifying choice is REFUSED in-band (fail-closed), surfaced in the banner.
    fn share_pare(&mut self, slug: &str, cx: &mut Context<Self>) {
        if let Some(ed) = &mut self.share_editor {
            self.share_outcome = Some(match ed.pare_to(slug) {
                PareOutcome::Pared { rights } => {
                    format!("pared the recipient role to {rights:?} (a sound attenuation ⊆ held)")
                }
                PareOutcome::Refused { reason } => format!("REFUSED · {reason}"),
            });
        }
        cx.notify();
    }

    /// Toggle the recipient preview tier (WIDE Either ↔ NARROW Signature).
    fn share_toggle_preview(&mut self, cx: &mut Context<Self>) {
        self.share_preview_wide = !self.share_preview_wide;
        cx.notify();
    }

    /// ⤳ SHARE — mint the revocable, attenuated, rehydratable artifact. The
    /// no-amplification gate is IN-BAND: an over-wide / incomplete pare is REFUSED
    /// (you cannot mint an over-wide artifact through this editor).
    fn share_mint(&mut self, cx: &mut Context<Self>) {
        if let Some(ed) = &self.share_editor {
            match ed.share() {
                Ok(artifact) => {
                    let role = artifact.attenuated_rights.clone();
                    let n = artifact.affordance_scope.affordance_names.len();
                    self.share_artifacts.push(artifact);
                    self.share_outcome = Some(format!(
                        "⤳ shared · minted a revocable artifact (role {role:?}, {n} sub-object(s)). \
                         The recipient gets a re-runnable camera + an attenuated cap — not your session."
                    ));
                }
                Err(ShareError::PareIncomplete) => {
                    self.share_outcome = Some(
                        "REFUSED · pick a recipient role first (the pare is incomplete — fail-closed)".to_string(),
                    );
                }
                Err(ShareError::WouldAmplify { held, pared }) => {
                    self.share_outcome = Some(format!(
                        "REFUSED · role {pared:?} would AMPLIFY the held {held:?} — \
                         you cannot share more than you hold (is_attenuation refused it)"
                    ));
                }
            }
        }
        cx.notify();
    }

    /// ⊘ REVOKE a shared artifact — withdraw the right to re-view (org "remove
    /// member"). The membrane re-checks authority at each reacquisition, so a revoked
    /// artifact rehydrates NOTHING thereafter, regardless of caps held.
    fn share_revoke(&mut self, idx: usize, cx: &mut Context<Self>) {
        if let Some(art) = self.share_artifacts.get_mut(idx) {
            art.revoke();
            self.share_outcome = Some(format!(
                "⊘ revoked artifact #{idx} — the right to re-view is withdrawn (rehydrates nothing now)"
            ));
        }
        cx.notify();
    }

    fn moldable_clear_query(&mut self, cx: &mut Context<Self>) {
        self.moldable_query.clear();
        cx.notify();
    }

    /// Cycle the moldable inspector's LENS FAMILY (the L4–L10 reach). Resets the
    /// present-idx to the new lens's first presentation so the tab-strip lands on
    /// a valid sub-tab; the witnessed camera-aim catches up on the next re-aim.
    fn moldable_cycle_lens(&mut self, cx: &mut Context<Self>) {
        self.moldable_lens = self.moldable_lens.next();
        self.inspector_view.doc_mut().set_present_idx(0);
        let _ = self.inspector_view.commit(&mut self.world.borrow_mut());
        cx.notify();
    }

    fn moldable_cycle_focus(&mut self, cx: &mut Context<Self>) {
        let cells = &self.cells;
        if cells.is_empty() {
            return;
        }
        let cur = self
            .inspector_view
            .doc()
            .focus()
            .and_then(|f| cells.iter().position(|c| *c == f))
            .unwrap_or(0);
        let next = cells[(cur + 1) % cells.len()];
        self.moldable_refocus(Some(next), cx);
    }

    /// M3 — RE-AIM the inspector's camera (a witnessed UI mutation). Re-focus the
    /// FREE in-memory draft (the §3.5 stream weight class: free edit), then land an
    /// occasional witnessed `SetField` commit so the inspector's camera-aim is a
    /// real, rewindable dregg-graph mutation (the BufferCell commit discipline,
    /// generalized). A commit failure leaves the free draft moved (the panel still
    /// reflects the operator's aim); the witnessed state catches up on the next
    /// successful commit.
    fn moldable_refocus(&mut self, focus: Option<CellId>, cx: &mut Context<Self>) {
        self.inspector_view.doc_mut().set_focus(focus);
        let _ = self.inspector_view.commit(&mut self.world.borrow_mut());
        cx.notify();
    }

    /// M3 — open presentation `idx` (a tab-strip click). Re-aim the free draft's
    /// lens, then witness it with an occasional commit (the same discipline as a
    /// re-focus).
    fn moldable_set_present_idx(&mut self, idx: usize, cx: &mut Context<Self>) {
        self.inspector_view.doc_mut().set_present_idx(idx);
        let _ = self.inspector_view.commit(&mut self.world.borrow_mut());
        cx.notify();
    }

    /// M3 — toggle the inspector ON ITSELF (inspect the inspector). When on, the
    /// panel focuses [`FocusTarget::ViewCell`] on the inspector's own backing cell —
    /// the reflexive loop through the SAME `Registry::present` dispatch.
    fn moldable_toggle_reflexive(&mut self, cx: &mut Context<Self>) {
        self.inspector_reflexive = !self.inspector_reflexive;
        cx.notify();
    }

    fn inspect_act_cycle_focus(&mut self, cx: &mut Context<Self>) {
        let cells = &self.cells;
        if cells.is_empty() {
            return;
        }
        let cur = self.inspect_act_focus.and_then(|f| cells.iter().position(|c| *c == f)).unwrap_or(0);
        self.inspect_act_focus = Some(cells[(cur + 1) % cells.len()]);
        self.inspect_act_outcome = None;
        cx.notify();
    }

    /// SEND a message through the REAL inspect→act loop (a verified turn), capturing
    /// the executor's verdict / the in-band refusal into the banner + refreshing.
    fn inspect_act_send(&mut self, message: &str, cx: &mut Context<Self>) {
        let Some(focus) = self.inspect_act_focus.or_else(|| self.cells.first().copied()) else {
            return;
        };
        let result = {
            let mut w = self.world.borrow_mut();
            let ia = InspectAct::build(&w, InspectFocus::Cell(focus), focus, dregg_cell::AuthRequired::Either);
            ia.send(&mut w, message, dregg_cell::AuthRequired::Either)
        };
        self.inspect_act_outcome = Some(match result {
            SendResult::Committed { receipt, .. } => format!(
                "committed `{message}` · receipt {} · {} action(s)",
                reflect::short_hex(&receipt.receipt_hash()),
                receipt.action_count
            ),
            SendResult::Refused { reason, by_executor } => format!(
                "REFUSED `{message}` ({}): {reason}",
                if by_executor { "executor" } else { "cap-gate" }
            ),
        });
        self.refresh_cells();
        cx.notify();
    }

    fn workspace_cycle_target(&mut self, cx: &mut Context<Self>) {
        let n = self.cells.len().max(1);
        self.workspace_target_idx = (self.workspace_target_idx + 1) % n;
        cx.notify();
    }

    fn workspace_add_transfer(&mut self, cx: &mut Context<Self>) {
        let cells = &self.cells;
        let Some(target) = cells.get(self.workspace_target_idx).copied() else { return };
        let agent = self.workspace.draft().agent;
        let ai = self.workspace.draft_mut().add_action(agent);
        self.workspace.draft_mut().add_effect(
            ai,
            starbridge_v2::simulate::EffectKind::Transfer { to: target, amount: 100 },
        );
        cx.notify();
    }

    fn workspace_clear(&mut self, cx: &mut Context<Self>) {
        let agent = self.workspace.draft().agent;
        self.workspace = Workspace::new(agent);
        cx.notify();
    }

    fn workspace_do_it(&mut self, cx: &mut Context<Self>) {
        let w = self.world.borrow();
        self.workspace.evaluate(&w);
        cx.notify();
    }

    fn workspace_commit(&mut self, cx: &mut Context<Self>) {
        if !self.workspace.can_commit() {
            return;
        }
        {
            let mut w = self.world.borrow_mut();
            self.workspace.commit(&mut w);
        }
        self.refresh_cells();
        cx.notify();
    }

    fn workspace_discard(&mut self, cx: &mut Context<Self>) {
        self.workspace.discard();
        cx.notify();
    }

    fn lane_turn_add(&mut self, cx: &mut Context<Self>) {
        let agent = self.lane_turn.agent_cell();
        self.lane_turn.action_with(
            agent,
            starbridge_v2::simulate::EffectKind::Transfer { to: agent, amount: 50 },
        );
        cx.notify();
    }

    fn lane_turn_clear(&mut self, cx: &mut Context<Self>) {
        self.lane_turn = CommittingTurnGadget::new(self.lane_turn.agent_cell());
        cx.notify();
    }

    /// Set the attenuation dial's designated tier through the REAL `Gadget::set`
    /// (the same path the form's keystroke drives), then capture build()'s verdict.
    fn lane_dial_set(&mut self, slug: &str, cx: &mut Context<Self>) {
        if let Some(dial) = &mut self.lane_dial {
            dial.set("rights", GadgetInput::Variant(slug.to_string()));
            self.lane_outcome = Some(match dial.build() {
                Ok(c) => format!("designated {slug} → buildable attenuated cap (rights {:?})", c.rights),
                Err(e) => format!("REFUSED designation {slug}: {e:?}"),
            });
        }
        cx.notify();
    }

    /// RUN the macaroon loop's REAL crypto via the gadget's `build()` (mint →
    /// attenuate → delegate → discharge), capturing the live verdict into the banner.
    fn lane_token_run(&mut self, cx: &mut Context<Self>) {
        self.lane_outcome = Some(match self.lane_token.build() {
            Ok(r) => format!(
                "loop ran · service `{}` mask `{}` · authorizes_own={} denies_wider={} · {} caveat(s) added",
                r.service, r.mask, r.authorizes_own, r.denies_wider, r.caveats_added
            ),
            Err(e) => format!("REFUSED · the loop could not build: {e:?}"),
        });
        cx.notify();
    }

    fn dynamics_feed(&self) -> impl IntoElement {
        let w = self.world.borrow();
        let mut col = div().flex().flex_col().gap_0p5().p_2();
        col = col.child(section_title("DYNAMICS · live").mb_1());
        let tail = w.dynamics().tail(12);
        if tail.is_empty() {
            col = col.child(div().text_xs().text_color(theme::muted()).child("(quiet)"));
        }
        for ev in tail.iter().rev() {
            let is_reject = matches!(ev, dynamics::WorldEvent::TurnRejected { .. });
            col = col.child(
                div()
                    .text_xs()
                    .text_color(if is_reject { theme::bad() } else { theme::muted() })
                    .child(format!("· {}", ev.label())),
            );
        }
        col
    }

    // --- the workspace tab bar + the four feature panels ---------------------

    /// The tab strip that switches the right-pane workspace.
    fn tab_bar(&self, cx: &mut Context<Self>) -> impl IntoElement {
        let mut row = div().flex().gap_1().p_2().border_b_1().border_color(theme::border());
        // M3 WIDEN — the active-tab highlight reads the witnessed cell selector too.
        let active_tab = self.active_tab();
        for t in Tab::ALL {
            let active = active_tab == t;
            row = row.child(
                div()
                    .id(SharedString::from(format!("tab-{}", t.label())))
                    .px_2()
                    .py_1()
                    .rounded_md()
                    .bg(if active { theme::panel_hi() } else { theme::panel() })
                    .text_xs()
                    .text_color(if active { theme::accent() } else { theme::muted() })
                    .cursor_pointer()
                    .hover(|s| s.bg(theme::border()))
                    .on_mouse_down(
                        MouseButton::Left,
                        cx.listener(move |this, _ev, _w, cx| {
                            // M3 WIDEN — a tab click witnesses through `set_tab` (the
                            // single selector seam: lazy-boots SWARM + commits the cell).
                            this.set_tab(t, cx);
                        }),
                    )
                    .child(t.label()),
            );
        }
        row
    }

    /// The active right-pane workspace panel.
    fn workspace(&self, cx: &mut Context<Self>) -> gpui::AnyElement {
        // M3 WIDEN — the dispatch SELECTOR is the witnessed [`WorkspaceCell`] read
        // (`render(workspace_subgraph)`, §3.4), not the Rust field. The per-tab match
        // is unchanged; only its source moved to a cell read.
        match self.active_tab() {
            Tab::Home => self.home_panel().into_any_element(),
            Tab::Shell => self.shell_panel(cx).into_any_element(),
            Tab::Agent => self.agent_panel().into_any_element(),
            Tab::Swarm => self.swarm_panel(cx).into_any_element(),
            Tab::Graph => self.graph_panel().into_any_element(),
            Tab::Organs => self.organs_panel().into_any_element(),
            Tab::Proofs => self.proofs_panel().into_any_element(),
            Tab::WebOfCells => self.web_of_cells_panel(cx).into_any_element(),
            Tab::LinksHere => self.links_here_panel(cx).into_any_element(),
            Tab::Powerbox => self.powerbox_panel(cx).into_any_element(),
            Tab::Moldable => self.moldable_panel(cx).into_any_element(),
            Tab::InspectAct => self.inspect_act_panel(cx).into_any_element(),
            Tab::Workspace => self.workspace_panel(cx).into_any_element(),
            Tab::Wonder => self.wonder_panel(cx).into_any_element(),
            Tab::Lanes => self.lanes_panel(cx).into_any_element(),
            Tab::Time => self.time_panel(cx).into_any_element(),
            Tab::Share => self.share_panel(cx).into_any_element(),
            Tab::Docs => self.docs_panel(cx).into_any_element(),
            Tab::Trust => self.trust_tab(cx).into_any_element(),
            Tab::Buffer => self.buffer_panel(cx).into_any_element(),
            Tab::Terminal => self.terminal_panel(cx).into_any_element(),
            Tab::Composer => self.composer(cx).into_any_element(),
            Tab::Simulate => self.simulate_panel(cx).into_any_element(),
            Tab::Objects => self.objects_panel().into_any_element(),
            Tab::Debugger => self.debugger_panel().into_any_element(),
            Tab::Replay => self.replay_panel().into_any_element(),
            Tab::Cipherclerk => self.cipherclerk_panel(cx).into_any_element(),
            Tab::Editor => self.editor_panel().into_any_element(),
        }
    }

    /// THE HOME panel — the warm LANDING portal (the boot view). Renders the
    /// [`LandingPortal`](starbridge_v2::landing::LandingPortal) text model
    /// (built fresh from the live [`World`], so its numbers are the running
    /// image's actual numbers) as native gpui text: a big greeting, then a stack
    /// of titled cards that name the running system reflectively — where you are,
    /// the image right now, the verified heart, the receipt nervous system, the
    /// organs, and how to begin. This is the alive front door: real, abundant
    /// text inviting you in (the anti-blank surface).
    fn home_panel(&self) -> impl IntoElement {
        let portal = starbridge_v2::landing::LandingPortal::build(&self.world.borrow());

        // The greeting masthead — the big "you have arrived" headline + subtitle,
        // with a live liveness pill so the portal visibly breathes.
        let w = self.world.borrow();
        let masthead = div()
            .flex()
            .flex_col()
            .gap_1()
            .p_4()
            .rounded_md()
            .border_1()
            .border_color(theme::accent())
            .bg(theme::panel())
            .child(div().text_2xl().text_color(theme::text()).child(portal.headline.clone()))
            .child(div().text_sm().text_color(theme::muted()).child(portal.subtitle.clone()))
            .child(
                div()
                    .flex()
                    .flex_wrap()
                    .gap_1()
                    .mt_1()
                    .child(pill("● live", theme::good()))
                    .child(pill("embedded verified executor", theme::good()))
                    .child(pill(format!("h{}", w.height()), theme::accent()))
                    .child(pill(format!("{} cells", w.cell_count()), theme::accent()))
                    .child(pill(format!("{} receipts", w.receipts().len()), theme::accent())),
            );
        drop(w);

        // Each portal section becomes a card; each line is real text, colored by
        // its semantic tone.
        let mut col = div()
            .flex()
            .flex_col()
            .gap_3()
            .p_4()
            .size_full()
            .overflow_hidden()
            .child(masthead);

        for section in &portal.sections {
            let mut card = div()
                .flex()
                .flex_col()
                .gap_1()
                .p_3()
                .rounded_md()
                .border_1()
                .border_color(theme::border())
                .bg(theme::panel())
                .child(section_title(section.title.clone()).mb_1());
            for line in &section.lines {
                let color = portal_tone_color(line.tone);
                let text_div = match line.tone {
                    // Headings render a touch larger; everything else is xs body.
                    starbridge_v2::landing::Tone::Heading => {
                        div().text_sm().text_color(color).child(line.text.clone())
                    }
                    _ => div().text_xs().text_color(color).child(line.text.clone()),
                };
                card = card.child(text_div);
            }
            col = col.child(card);
        }

        // The closing call-to-action.
        col = col.child(
            div()
                .text_sm()
                .text_color(theme::accent())
                .child(portal.invitation.clone()),
        );
        col
    }

    /// THE SHELL panel — the cap-first window manager / compositor. Composes the
    /// live [`Scene`] (surfaces over real cells, z-ordered) and renders each
    /// surface as a window with: a SHELL-DRAWN trusted-path identity header
    /// (anti-spoof — the owning cell id + lifecycle, read from the live ledger),
    /// the surface's own title, cap-gated window controls, and a body of the
    /// real cell's state. The whole compositor reacts to real turns (it re-reads
    /// the world each frame).
    fn shell_panel(&self, cx: &mut Context<Self>) -> impl IntoElement {
        let w = self.world.borrow();
        let scene: Scene = self.shell.compose(&w);
        let layout = scene.layout;
        let focused = scene.focused;

        let mut col = div().flex().flex_col().gap_2().p_3().size_full();
        col = col.child(section_title("SHELL · cap-first compositor over real cells").mb_1());
        col = col.child(div().text_xs().text_color(theme::muted()).child(
            "Each dregg CELL is a cap-confined SURFACE. Every window op (focus · close · \
             minimize) is GATED by the surface's capability — there is no ambient authority. \
             The identity badge on each surface is drawn by the SHELL from the live ledger \
             (anti-spoof), so a surface cannot impersonate another cell.",
        ));

        // The compositor toolbar: layout + the cap-gated ops.
        col = col.child(
            div()
                .flex()
                .flex_wrap()
                .gap_1()
                .items_center()
                .child(pill(format!("layout: {}", layout.label()), theme::accent()))
                .child(pill(format!("{} surfaces", self.shell.surface_count()), theme::good()))
                .child(pill(format!("console s{}", self.console_surface.as_u64()), theme::warn()))
                .child(shell_button(cx, "open selected as surface", theme::good(), Cockpit::shell_open_selected))
                .child(shell_button(cx, "focus front", theme::accent(), Cockpit::shell_focus_front))
                .child(shell_button(cx, "minimize focused", theme::accent(), Cockpit::shell_minimize_focused))
                .child(shell_button(cx, "present focused (commits)", theme::good(), Cockpit::shell_present_focused))
                .child(shell_button(cx, "⚠ overpaint (T1 REJECT)", theme::warn(), Cockpit::shell_overpaint_focused))
                .child(shell_button(cx, "⚠ input-steal (T3 REJECT)", theme::warn(), Cockpit::shell_input_steal))
                .child(shell_button(cx, "share (read-only mirror)", theme::good(), Cockpit::shell_share_focused))
                .child(shell_button(cx, "⚠ over-share (watch it REJECT)", theme::warn(), Cockpit::shell_overshare_focused))
                .child(shell_button(cx, "close focused", theme::warn(), Cockpit::shell_close_focused))
                .child(shell_button(cx, "cycle layout", theme::accent(), Cockpit::shell_cycle_layout)),
        );
        col = col.child(self.outcome_banner());
        // The verified-scene legend: the three teeth the compositor enforces.
        col = col.child(div().text_xs().text_color(theme::muted()).child(
            "Verified scene (the Lean Compositor AppSpec, on glass): T1 NON-OVERLAP — a surface \
             paints only its own cap-authorized region (overpaint REFUSED); T2 LABEL-BINDING — the \
             identity badge is a function of the owner + state-root the SHELL reads (spoof REFUSED); \
             T3 FOCUS-EXCLUSIVITY — input routes only to the one focused surface (steal REFUSED).",
        ));
        // The frame log: how many genuine presents have committed (provenance).
        col = col.child(
            div()
                .flex()
                .gap_1()
                .items_center()
                .child(pill(format!("{} frames committed", self.shell.frame_log().len()), theme::accent()))
                .child(div().text_xs().text_color(theme::muted()).child(
                    "each frame is a present that passed T1∧T2∧T3 (a refused present logs none — fail-closed)",
                )),
        );

        // The composed scene: surfaces front-to-back (front first, so the most
        // recently focused window reads at the top of the list).
        let mut stack = div().flex().flex_col().gap_2().mt_1();
        for item in scene.items.iter().rev() {
            let id = item.surface.id();
            let is_focused = focused == Some(id);
            let is_console = item.surface.is_console();
            let held_cap = self.surface_caps.contains_key(&id);

            // The trusted-path identity header — SHELL-drawn, from the ledger.
            let (badge_label, badge_color) = identity_badge(item.identity.lifecycle);
            let owner = if is_console {
                "SYSTEM (trusted root)".to_string()
            } else {
                format!("owner cell {}", item.identity.short)
            };

            // The window body: the real cell's live state (balance/nonce/caps/
            // lifecycle), read fresh from the ledger — never a mock.
            let body = self.surface_body(&item.surface.cell(), &w, is_console);

            let border = if is_focused { theme::accent() } else { theme::border() };
            stack = stack.child(
                div()
                    .id(SharedString::from(format!("surface-{}", id.as_u64())))
                    .flex()
                    .flex_col()
                    .rounded_md()
                    .border_1()
                    .border_color(border)
                    .bg(theme::panel())
                    .cursor_pointer()
                    // Clicking the surface is a HINT; the cap-gated focus is the
                    // authority (routed through `shell_click_surface`).
                    .on_mouse_down(
                        MouseButton::Left,
                        cx.listener(move |this, _ev, _w, cx| {
                            this.shell_click_surface(id, cx);
                        }),
                    )
                    // The title bar: identity badge (shell-drawn) + title + chrome.
                    .child(
                        div()
                            .flex()
                            .justify_between()
                            .items_center()
                            .px_2()
                            .py_1()
                            .rounded_md()
                            .bg(if is_focused { theme::panel_hi() } else { theme::panel() })
                            .border_b_1()
                            .border_color(theme::border())
                            .child(
                                div()
                                    .flex()
                                    .gap_2()
                                    .items_center()
                                    .child(div().text_xs().text_color(if is_console { theme::warn() } else { theme::accent() }).child(if is_console { "◆" } else { "⬡" }))
                                    .child(div().text_color(theme::text()).child(item.surface.title().to_string()))
                                    .child(pill(badge_label, badge_color)),
                            )
                            .child(
                                div()
                                    .flex()
                                    .gap_1()
                                    .items_center()
                                    .child(div().text_xs().text_color(theme::muted()).child(format!("z{}", item.surface.z())))
                                    .when(is_focused, |d| d.child(pill("focused", theme::good())))
                                    .when(item.surface.is_minimized(), |d| d.child(pill("min", theme::muted())))
                                    .when(!held_cap, |d| d.child(pill("no cap", theme::bad()))),
                            ),
                    )
                    // The trusted-path provenance line (anti-spoof): the owner the
                    // SHELL attests, plus whether the cell is backed in the ledger.
                    .child(
                        div()
                            .flex()
                            .justify_between()
                            .px_2()
                            .py_0p5()
                            .child(div().text_xs().text_color(theme::muted()).child(owner))
                            .child(
                                div()
                                    .text_xs()
                                    .text_color(if item.identity.backed || is_console { theme::muted() } else { theme::bad() })
                                    .child(if is_console {
                                        "trusted-path: system console".to_string()
                                    } else if item.identity.backed {
                                        "trusted-path: shell-attested ✓".to_string()
                                    } else {
                                        "trusted-path: UNBACKED (cell missing)".to_string()
                                    }),
                            ),
                    )
                    // The body (the real cell's live state) — hidden when minimized.
                    .when(!item.surface.is_minimized(), |d| d.child(body)),
            );
        }
        col = col.child(stack);
        col
    }

    /// The body of a surface: the backing cell's LIVE state, read from the
    /// ledger. For the console it shows the image summary instead (it is the
    /// system's own root, not a single cell's view). Never a mock — this is the
    /// surface "reacting to real turns".
    fn surface_body(&self, cell: &CellId, w: &World, is_console: bool) -> gpui::AnyElement {
        let mut body = div().flex().flex_col().gap_0p5().px_2().py_1();
        if is_console {
            body = body
                .child(div().text_xs().text_color(theme::muted()).child(format!(
                    "image · {} cells · h{} · {} receipts",
                    w.cell_count(),
                    w.height(),
                    w.receipts().len()
                )))
                .child(div().text_xs().text_color(theme::accent()).child(format!(
                    "root {}",
                    reflect::short_hex(&w.state_root())
                )));
            return body.into_any_element();
        }
        match w.ledger().get(cell) {
            Some(c) => {
                let bal = c.state.balance();
                let bal_color = if bal < 0 { theme::warn() } else { theme::text() };
                body = body
                    .child(
                        div()
                            .flex()
                            .justify_between()
                            .child(div().text_xs().text_color(theme::muted()).child("balance"))
                            .child(div().text_xs().text_color(bal_color).child(format!("{bal}"))),
                    )
                    .child(
                        div()
                            .flex()
                            .justify_between()
                            .child(div().text_xs().text_color(theme::muted()).child("nonce"))
                            .child(div().text_xs().text_color(theme::text()).child(format!("{}", c.state.nonce()))),
                    )
                    .child(
                        div()
                            .flex()
                            .justify_between()
                            .child(div().text_xs().text_color(theme::muted()).child("capabilities"))
                            .child(div().text_xs().text_color(theme::text()).child(format!("{}", c.capabilities.len()))),
                    )
                    .child(
                        div()
                            .flex()
                            .justify_between()
                            .child(div().text_xs().text_color(theme::muted()).child("lifecycle"))
                            .child(div().text_xs().text_color(theme::text()).child(format!("{:?}", c.lifecycle))),
                    );
            }
            None => {
                body = body.child(
                    div()
                        .text_xs()
                        .text_color(theme::bad())
                        .child("(backing cell is not in the ledger — a dangling surface)"),
                );
            }
        }
        body.into_any_element()
    }

    /// THE AGENT-ACTIVITY panel — the ADOS keystone. Renders an agent loop's
    /// PROVABLE activity as a cap-gated surface cell: its held mandate (the
    /// attenuated authority it runs under), its recent cap-gated turns + their
    /// receipts (the grounded seam, read from the embedded World's receipt log +
    /// dynamics stream), and the legible boundary of what it is authorized to do.
    /// Maps `agent::AgentActivity` (gpui-free) onto gpui — you watch the
    /// executor's receipts, not the agent's self-report.
    fn agent_panel(&self) -> impl IntoElement {
        let w = self.world.borrow();
        let act = self.agent_surface.activity(&w, 24);

        let mut col = div().flex().flex_col().gap_2().p_3().size_full();
        col = col.child(section_title("AGENT · the grounded loop (provable activity as a surface)").mb_1());
        col = col.child(div().text_xs().text_color(theme::muted()).child(
            "An agent is an intricate LOOP; dregg grounds the ONE seam that matters — its ACTIONS, \
             at the tool-call/turn boundary — by making every action a cap-gated, RECEIPTED, \
             conservation-checked turn. This surface renders that seam: the mandate it holds, the \
             turns it committed (with receipts), and the boundary of what it may do. You watch the \
             executor's truth, never the agent's self-report.",
        ));

        // The agent header: who it is + its live resources + grounded step count.
        let backed_color = if act.backed { theme::good() } else { theme::bad() };
        col = col.child(
            div()
                .flex()
                .flex_wrap()
                .gap_1()
                .items_center()
                .child(pill(format!("agent {}", act.short), theme::accent()))
                .child(pill(
                    if act.backed { "live" } else { "UNBACKED" }.to_string(),
                    backed_color,
                ))
                .child(pill(format!("balance {}", act.balance), theme::text()))
                .child(pill(format!("{} committed turns", act.committed_action_count()), theme::good()))
                .child(pill(format!("reach {} cell(s)", act.reach()), theme::accent()))
                .child(pill(format!("nonce {}", act.nonce), theme::muted())),
        );

        // --- THE HELD MANDATE (the attenuated authority the loop runs under) ---
        col = col.child(section_title("held mandate (adoption = attenuation)").mt_2());
        if act.mandate.is_empty() {
            col = col.child(div().text_xs().text_color(theme::muted()).child(
                "holds NO outbound capability — this agent is confined to itself (the narrowest mandate).",
            ));
        } else {
            let mut edges = div().flex().flex_col().gap_0p5();
            for m in &act.mandate {
                let rights_color = match m.rights_label() {
                    "open" => theme::warn(),
                    "locked" => theme::bad(),
                    _ => theme::good(),
                };
                edges = edges.child(
                    div()
                        .flex()
                        .justify_between()
                        .items_center()
                        .px_2()
                        .py_0p5()
                        .rounded_md()
                        .bg(theme::panel())
                        .child(
                            div()
                                .flex()
                                .gap_2()
                                .items_center()
                                .child(div().text_xs().text_color(theme::muted()).child(format!("slot {}", m.slot)))
                                .child(div().text_xs().text_color(theme::text()).child(format!(
                                    "→ {}",
                                    reflect::short_hex(m.target.as_bytes())
                                )))
                                .child(pill(m.rights_label(), rights_color)),
                        )
                        .child(
                            div()
                                .flex()
                                .gap_1()
                                .items_center()
                                .when(m.faceted, |d| d.child(pill("faceted", theme::accent())))
                                .when(m.expires_at.is_some(), |d| {
                                    d.child(pill(format!("expires @{}", m.expires_at.unwrap()), theme::warn()))
                                }),
                        ),
                );
            }
            col = col.child(edges);
        }

        // --- THE CAP-GATED ACTIONS (turns) + their RECEIPTS (the grounded seam) ---
        col = col.child(section_title("recent cap-gated actions (turns + receipts)").mt_2());
        if act.actions.is_empty() {
            col = col.child(div().text_xs().text_color(theme::muted()).child(
                "no actions yet — this agent's loop has not committed (or attempted) a turn.",
            ));
        } else {
            let mut rows = div().flex().flex_col().gap_0p5();
            for a in &act.actions {
                let (mark, mark_color) = if a.committed {
                    ("✓", theme::good())
                } else {
                    ("✗", theme::bad())
                };
                let height_label = a
                    .height
                    .map(|h| format!("h{h}"))
                    .unwrap_or_else(|| "—".to_string());
                rows = rows.child(
                    div()
                        .flex()
                        .justify_between()
                        .items_center()
                        .px_2()
                        .py_0p5()
                        .child(
                            div()
                                .flex()
                                .gap_2()
                                .items_center()
                                .child(div().text_xs().text_color(mark_color).child(mark))
                                .child(div().text_xs().text_color(theme::muted()).child(height_label))
                                .child(div().text_xs().text_color(if a.committed { theme::text() } else { theme::bad() }).child(a.summary.clone())),
                        )
                        .child(
                            div()
                                .flex()
                                .gap_1()
                                .items_center()
                                .when(a.committed, |d| {
                                    d.child(div().text_xs().text_color(theme::muted()).child(format!("{} act · {} ⚙", a.action_count, a.computrons)))
                                })
                                .when(a.receipt_hash.is_some(), |d| {
                                    d.child(pill(reflect::short_hex(&a.receipt_hash.unwrap()), theme::good()))
                                }),
                        ),
                );
            }
            col = col.child(rows);
        }

        // --- WHAT IT IS AUTHORIZED TO DO (the boundary of the loop's reach) ---
        col = col.child(section_title("what it is authorized to do (the boundary)").mt_2());
        let mut auths = div().flex().flex_col().gap_0p5();
        for a in &act.authorizations {
            let (mark, mark_color) = if a.permitted {
                ("CAN", theme::good())
            } else {
                ("CANNOT", theme::bad())
            };
            auths = auths.child(
                div()
                    .flex()
                    .justify_between()
                    .items_center()
                    .px_2()
                    .py_0p5()
                    .child(
                        div()
                            .flex()
                            .gap_2()
                            .items_center()
                            .child(pill(mark, mark_color))
                            .child(div().text_xs().text_color(theme::text()).child(a.verb)),
                    )
                    .child(div().text_xs().text_color(theme::muted()).child(a.note.clone())),
            );
        }
        col = col.child(auths);
        col
    }

    /// THE A2 SWARM PANEL — multi-agent cap-coordination surface.
    ///
    /// Renders the [`SwarmView`]: each member's mandate + action count + inbox,
    /// the inter-member notify-edge activity feed, and the demo action row
    /// (emit a wake / drain the inbox / transfer-and-wake in one turn).
    ///
    /// The point: you watch the EXECUTOR's receipts for each member's committed
    /// turns, and the INBOX accumulates pending wakes from peers' emits — all
    /// on-ledger truth, never a self-report. The async model (send ≠ receive)
    /// is visible: the coordinator's emit receipt and worker-a's drain receipt
    /// are DIFFERENT turns with DIFFERENT heights.
    fn swarm_panel(&self, cx: &mut Context<Self>) -> impl IntoElement {
        let w = self.world.borrow();
        let view = SwarmView::build(&self.swarm, &w);
        drop(w);

        let mut col = div().flex().flex_col().gap_2().p_3().size_full();
        col = col.child(section_title("SWARM (A2) · multi-agent cap-coordination · notify-edge inbox").mb_1());
        col = col.child(div().text_xs().text_color(theme::muted()).child(
            "N agent cells coordinating as confined Surface cells. Every action is a cap-gated, \
             receipted turn at the ONE seam. An EmitEvent deposits a NotifyEdge in the \
             recipient's inbox; the recipient drains it in its OWN separate future turn \
             (async — not a joint turn). You watch the executor's truth, never a self-report.",
        ));

        // Header: swarm stats.
        col = col.child(
            div()
                .flex()
                .flex_wrap()
                .gap_1()
                .items_center()
                .child(pill(format!("{} members", view.members.len()), theme::accent()))
                .child(pill(format!("{} total actions", view.total_actions), theme::good()))
                .child(pill(
                    format!("{} pending wakes", view.total_pending),
                    if view.total_pending > 0 { theme::warn() } else { theme::muted() },
                )),
        );

        // Members: one row per member.
        col = col.child(section_title("members (cap-confined, mandate-gated)").mt_2());
        let mut members_col = div().flex().flex_col().gap_1();
        for m in &view.members {
            let backed_color = if m.backed { theme::good() } else { theme::bad() };
            let inbox_color = if m.pending_notify > 0 { theme::warn() } else { theme::muted() };
            members_col = members_col.child(
                div()
                    .flex()
                    .flex_col()
                    .gap_0p5()
                    .px_2()
                    .py_1()
                    .rounded_md()
                    .bg(theme::panel())
                    .child(
                        div()
                            .flex()
                            .gap_1()
                            .items_center()
                            .child(pill(m.name.clone(), theme::accent()))
                            .child(pill(m.short.clone(), theme::muted()))
                            .child(pill(if m.backed { "live" } else { "UNBACKED" }, backed_color))
                            .child(pill(format!("bal {}", m.balance), theme::text()))
                            .child(pill(format!("{} actions", m.action_count), theme::good()))
                            .child(pill(
                                format!("{} pending", m.pending_notify),
                                inbox_color,
                            )),
                    )
                    .when(!m.inbox.is_empty(), |d| {
                        let mut inbox_div = div().flex().flex_col().gap_0p5().mt_1();
                        for n in &m.inbox {
                            let (mark, color) = if n.drained {
                                ("✓", theme::muted())
                            } else {
                                ("⚡", theme::warn())
                            };
                            inbox_div = inbox_div.child(
                                div()
                                    .flex()
                                    .gap_1()
                                    .items_center()
                                    .text_xs()
                                    .px_2()
                                    .child(div().text_color(color).child(mark))
                                    .child(
                                        div()
                                            .text_color(if n.drained { theme::muted() } else { theme::text() })
                                            .child(n.label()),
                                    ),
                            );
                        }
                        d.child(inbox_div)
                    }),
            );
        }
        col = col.child(members_col);

        // Action row: the demo verbs.
        col = col.child(section_title("demo actions (the A2 seam)").mt_2());
        col = col.child(
            div()
                .flex()
                .flex_wrap()
                .gap_1()
                .child(verb_button(cx, "coordinator emit task/go → worker-a", theme::accent(), Cockpit::swarm_coordinator_emit_a))
                .child(verb_button(cx, "worker-a DRAIN inbox (own ack turn)", theme::good(), Cockpit::swarm_worker_a_drain))
                .child(verb_button(cx, "coordinator: transfer + wake (one seam)", theme::warn(), Cockpit::swarm_coordinator_transfer_and_wake)),
        );

        // ── THE FOUR-SURFACE KILLER DEMO (N5) — the pug-handoff artifact ──────
        col = col.child(
            section_title("⚑ the killer demo (N5) · the pug-handoff evaluation artifact").mt_3(),
        );
        col = col.child(div().text_xs().text_color(theme::muted()).child(
            "ONE end-to-end story, every step a real receipted turn: (1) MINT a token \
             cell via factory-birth · (2) AGENT A acts in-mandate (a budget spend) · \
             (3) A NOTIFIES B who drains it in its OWN turn (two distinct receipts) · \
             (4) the DUAL REFUSAL — an over-grant AND an over-spend, BOTH fail-closed \
             through the real executor. (pg step 5 deferred.)",
        ));
        // Demo state header: where the script is + the verified budget meter.
        // `set_tab(Swarm)` boots the demo before this renders, so it is normally
        // `Some`; the `None` arm is a graceful "booting" fallback only.
        {
            let mut hdr = div().flex().flex_wrap().gap_1().items_center().mt_1();
            if let Some(demo) = self.killer_demo.as_ref() {
                let cursor = demo.cursor();
                let total = HeadlineDemo::TOTAL_STEPS;
                let next = demo.next_step_label();
                hdr = hdr.child(pill(format!("frame {cursor}/{total}"), theme::accent()));
                if let Some(label) = next {
                    hdr = hdr.child(pill(format!("next: {label}"), theme::warn()));
                } else {
                    hdr = hdr.child(pill("script complete", theme::good()));
                }
                if let Some(v) = demo.swarm().stingray_view() {
                    hdr = hdr.child(pill(
                        format!("budget {}/{} computrons", v.total_drawn, v.ceiling),
                        if v.exhausted { theme::bad() } else { theme::good() },
                    ));
                }
            } else {
                hdr = hdr.child(pill("booting the demo…", theme::muted()));
            }
            col = col.child(hdr);
        }
        // The driver buttons.
        col = col.child(
            div()
                .flex()
                .flex_wrap()
                .gap_1()
                .mt_1()
                .child(verb_button(cx, "▶ next frame", theme::accent(), Cockpit::killer_demo_advance))
                .child(verb_button(cx, "⏩ run all (the self-check)", theme::good(), Cockpit::killer_demo_run_all))
                .child(verb_button(cx, "⚠ over-share at the glass (pixel-layer refusal)", theme::warn(), Cockpit::killer_demo_over_share))
                .child(verb_button(cx, "↺ reset demo", theme::muted(), Cockpit::killer_demo_reset)),
        );
        // The captured frame strip (the four frames + both refusals, as run).
        if self.killer_demo_lines.is_empty() {
            col = col.child(div().text_xs().text_color(theme::muted()).mt_1().child(
                "press ▶ to run the first frame, or ⏩ to drive the whole script at once.",
            ));
        } else {
            let mut strip = div().flex().flex_col().gap_0p5().mt_1();
            for line in &self.killer_demo_lines {
                // A refusal line (carries "REFUSED") is colored as the teaching
                // moment; a commit line is neutral. The executor's reason (the
                // second line, indented) is muted.
                let is_refusal = line.contains("REFUSED");
                let color = if is_refusal { theme::warn() } else { theme::text() };
                for (i, sub) in line.lines().enumerate() {
                    let c = if i == 0 { color } else { theme::muted() };
                    strip = strip.child(
                        div()
                            .text_xs()
                            .px_2()
                            .text_color(c)
                            .child(sub.trim_end().to_string()),
                    );
                }
            }
            col = col.child(strip);
        }

        // Activity feed: recent swarm actions (newest-first).
        col = col.child(section_title("activity feed (executor receipts · notify edges)").mt_2());
        if view.activity.is_empty() {
            col = col.child(div().text_xs().text_color(theme::muted()).child(
                "no swarm actions yet — use the buttons above to run the first turns.",
            ));
        } else {
            let mut feed = div().flex().flex_col().gap_0p5();
            for entry in &view.activity {
                let (mark, mark_color) = if entry.committed {
                    ("✓", theme::good())
                } else {
                    ("✗", theme::bad())
                };
                let height_label = entry.height.map(|h| format!("h{h}")).unwrap_or_else(|| "—".to_string());
                let receipt_label = entry.receipt_short.as_deref().unwrap_or("—");
                feed = feed.child(
                    div()
                        .flex()
                        .flex_col()
                        .gap_0p5()
                        .px_2()
                        .py_0p5()
                        .rounded_sm()
                        .bg(theme::panel())
                        .child(
                            div()
                                .flex()
                                .gap_2()
                                .items_center()
                                .child(div().text_xs().text_color(mark_color).child(mark))
                                .child(div().text_xs().text_color(theme::muted()).child(height_label))
                                .child(div().text_xs().text_color(theme::accent()).child(entry.member_short.clone()))
                                .child(
                                    div()
                                        .text_xs()
                                        .text_color(if entry.committed { theme::text() } else { theme::bad() })
                                        .child(entry.summary.clone()),
                                )
                                .when(entry.committed, |d| {
                                    d.child(pill(receipt_label.to_string(), theme::good()))
                                }),
                        )
                        .when(!entry.notify_edges.is_empty(), |d| {
                            let mut edges_div = div().flex().flex_col().gap_0p5().px_2();
                            for edge_label in &entry.notify_edges {
                                edges_div = edges_div.child(
                                    div()
                                        .text_xs()
                                        .text_color(theme::warn())
                                        .child(format!("  ⚡ {edge_label}")),
                                );
                            }
                            d.child(edges_div)
                        }),
                );
            }
            col = col.child(feed);
        }

        col
    }

    /// THE TURN DEBUGGER panel — maps `debug::render`'s gpui-free model onto
    /// gpui elements (step list, conservation Σδ, the refusal explanation).
    fn debugger_panel(&self) -> impl IntoElement {
        let w = self.world.borrow();
        let panel = debug::render(&w, &self.debug_turn, &self.breakpoints);

        let mut col = div().flex().flex_col().gap_1().p_3().size_full();
        col = col.child(section_title("DEBUGGER · step · inspect · explain").mb_1());
        col = col.child(div().text_color(theme::text()).child(panel.title.clone()));
        col = col.child(div().text_xs().text_color(theme::muted()).mb_2().child(panel.subtitle.clone()));

        // The step list.
        let mut steps = div().flex().flex_col().gap_0p5();
        for s in &panel.steps {
            let color = if !s.committed {
                theme::bad()
            } else if s.is_break {
                theme::warn()
            } else {
                theme::text()
            };
            steps = steps.child(
                div()
                    .flex()
                    .justify_between()
                    .px_2()
                    .child(div().text_xs().text_color(color).child(format!(
                        "{} k{} {}",
                        if s.is_break { "◆" } else { "·" },
                        s.index,
                        s.label
                    )))
                    .child(div().text_xs().text_color(theme::muted()).child(format!("Σδ={}", s.conservation_delta))),
            );
        }
        col = col.child(steps);

        // The refusal explanation (the prize) or the conserving commit line.
        col = col.child(match &panel.refusal {
            Some(r) => div()
                .mt_2()
                .p_2()
                .rounded_md()
                .bg(theme::panel())
                .flex()
                .flex_col()
                .gap_0p5()
                .child(div().text_xs().text_color(theme::bad()).child(format!("REFUSED · guard: {}", r.guard)))
                .child(div().text_xs().text_color(theme::text()).child(r.headline.clone()))
                .child(div().text_xs().text_color(theme::muted()).child(r.detail.clone())),
            None => div()
                .mt_2()
                .p_2()
                .rounded_md()
                .bg(theme::panel())
                .text_xs()
                .text_color(theme::good())
                .child(format!("COMMITS · final Σδ = {} (conserves)", panel.final_conservation_delta)),
        });
        col
    }

    /// THE REPLAY / TIME-TRAVEL panel — `replay::replay_panel` returns gpui
    /// directly; the cockpit owns the cursor + any pinned fork and rebuilds the
    /// model each frame from the live world's REAL history.
    fn replay_panel(&self) -> impl IntoElement {
        let w = self.world.borrow();
        let history = w.recorded_turns();
        let cursor = self.replay_cursor.min(history.len());
        let model = replay::ReplayPanelModel::build(history, cursor, self.replay_fork.as_ref());
        div()
            .flex()
            .flex_col()
            .size_full()
            .child(replay::replay_panel(&model))
    }

    /// THE CIPHERCLERK panel — maps `cipherclerk::render`'s reflective lists
    /// onto the cockpit's shared inspector rows.
    fn cipherclerk_panel(&self, cx: &mut Context<Self>) -> impl IntoElement {
        let panel = cipherclerk::render(&self.clerk);
        let mut col = div().flex().flex_col().gap_1().p_3().size_full();
        col = col.child(section_title("CIPHERCLERK · identities · tokens · delegations").mb_1());

        // The REAL macaroon action loop (mint → attenuate → delegate → discharge),
        // each driving `AgentCipherclerk`. Acts on alice (the holder) + bob (the
        // delegatee) over the "dns" service.
        col = col.child(div().text_xs().text_color(theme::muted()).child("ACTIONS (alice · service 'dns')"));
        col = col.child(
            div()
                .flex()
                .flex_wrap()
                .gap_1()
                .child(clerk_button(cx, "mint root", theme::good(), Cockpit::run_clerk_mint))
                .child(clerk_button(cx, "attenuate → r", theme::accent(), Cockpit::run_clerk_attenuate))
                .child(clerk_button(cx, "delegate → bob", theme::accent(), Cockpit::run_clerk_delegate))
                .child(clerk_button(cx, "discharge (verify)", theme::warn(), Cockpit::run_clerk_discharge)),
        );
        // The real action result banner.
        col = col.child(self.clerk_banner());

        col = col.child(div().text_xs().text_color(theme::muted()).mt_1().child("IDENTITIES"));
        for ins in &panel.identities {
            col = col.child(inspectable_row(ins));
        }
        col = col.child(div().text_xs().text_color(theme::muted()).mt_2().child("HELD TOKENS"));
        if panel.tokens.is_empty() {
            col = col.child(div().text_xs().text_color(theme::muted()).px_2().child("(none minted yet)"));
        }
        for ins in &panel.tokens {
            col = col.child(inspectable_row(ins));
        }
        col = col.child(div().text_xs().text_color(theme::muted()).mt_2().child("DELEGATIONS"));
        if panel.delegations.is_empty() {
            col = col.child(div().text_xs().text_color(theme::muted()).px_2().child("(none recorded)"));
        }
        for ins in &panel.delegations {
            col = col.child(inspectable_row(ins));
        }
        col
    }

    /// The cipherclerk action result banner (the real mint/attenuate/delegate/
    /// discharge outcome). Colors a denied discharge or a failure red.
    fn clerk_banner(&self) -> impl IntoElement {
        let (txt, color) = match &self.clerk_outcome {
            None => ("(run a clerk action above)".to_string(), theme::muted()),
            Some(o) => {
                let denied = matches!(
                    o,
                    cipherclerk::ClerkOutcome::Discharged { authorized: false, .. }
                );
                let color = if !o.is_ok() || denied {
                    theme::bad()
                } else {
                    theme::good()
                };
                (o.banner(), color)
            }
        };
        div()
            .mt_1()
            .mb_1()
            .p_2()
            .rounded_md()
            .bg(theme::panel())
            .text_xs()
            .text_color(color)
            .child(txt)
    }

    /// THE OBJECTS panel — the reflective object views over the protocol
    /// surface beyond cells/receipts: each committed turn's PROOF / STARK status,
    /// the NULLIFIERS (consumed one-time authorities) it spent, and the
    /// lifecycle of every cell (live / sealed / destroyed). All projected through
    /// `reflect` from the live world — never a parallel schema.
    fn objects_panel(&self) -> impl IntoElement {
        let w = self.world.borrow();
        let mut col = div().flex().flex_col().gap_1().p_3().size_full();
        col = col.child(section_title("OBJECTS · proofs · nullifiers · lifecycle").mb_1());

        // Lifecycle column: every cell's lifecycle state (the seal/destroy axis).
        col = col.child(div().text_xs().text_color(theme::muted()).mt_1().child("CELL LIFECYCLE"));
        for id in &self.cells {
            if let Some(cell) = w.ledger().get(id) {
                let (label, color) = lifecycle_badge(&cell.lifecycle);
                col = col.child(
                    div()
                        .flex()
                        .justify_between()
                        .px_2()
                        .py_0p5()
                        .child(div().text_xs().text_color(theme::text()).child(format!("⬡ {}", reflect::short_hex(id.as_bytes()))))
                        .child(div().text_xs().text_color(color).child(label)),
                );
            }
        }

        // Proof status + nullifiers for the most recent receipts.
        col = col.child(div().text_xs().text_color(theme::muted()).mt_2().child("TURN PROOFS (most recent)"));
        if w.receipts().is_empty() {
            col = col.child(div().text_xs().text_color(theme::muted()).px_2().child("(no turns yet)"));
        }
        for r in w.receipts().iter().rev().take(6) {
            let proof = reflect::reflect_proof_status(r);
            col = col.child(inspectable_row(&proof));
            for null in reflect::reflect_nullifiers(r) {
                col = col.child(inspectable_row(&null));
            }
        }
        col
    }

    /// THE GRAPH panel — the whole-graph ocap delegation layout. Renders the
    /// capability graph as nodes (cells, with in/out degree) + edges (grants,
    /// with rights), and — rooted on the first source cell — the LAYERED
    /// multi-hop delegation depth (root at depth 0, its grantees at depth 1, …)
    /// plus each source's transitive blast radius. The View tree IS the ocap
    /// graph (`starbridge_v2::graph`).
    fn graph_panel(&self) -> impl IntoElement {
        let w = self.world.borrow();
        let g = starbridge_v2::graph::OcapGraph::build(&w);
        let mut col = div().flex().flex_col().gap_1().p_3().size_full();
        col = col.child(section_title("GRAPH · ocap delegation (multi-hop)").mb_1());
        col = col.child(
            div().text_xs().text_color(theme::muted()).child(format!(
                "{} cells · {} capability edges",
                g.node_count(),
                g.edge_count()
            )),
        );

        // The EDGES — the literal ocap graph (holder ──rights──▶ target).
        col = col.child(div().text_xs().text_color(theme::muted()).mt_2().child("CAPABILITY EDGES"));
        if g.edge_count() == 0 {
            col = col.child(div().text_xs().text_color(theme::muted()).px_2().child("(no capability edges yet)"));
        }
        for e in g.edges().iter().take(24) {
            let deleg = if e.is_delegated() { " · delegated" } else { "" };
            let facet = if e.faceted { " · faceted" } else { "" };
            col = col.child(
                div()
                    .flex()
                    .justify_between()
                    .px_2()
                    .py_0p5()
                    .child(
                        div().text_xs().text_color(theme::text()).child(format!(
                            "⬡ {} ──▶ {}",
                            reflect::short_hex(e.holder.as_bytes()),
                            reflect::short_hex(e.target.as_bytes()),
                        )),
                    )
                    .child(
                        div()
                            .text_xs()
                            .text_color(theme::accent())
                            .child(format!("[{}]{deleg}{facet}", e.rights_label())),
                    ),
            );
        }

        // The LAYERED multi-hop layout, rooted on each source cell (no inbound
        // edge — the authority origins), with the transitive blast radius.
        col = col.child(div().text_xs().text_color(theme::muted()).mt_2().child("MULTI-HOP LAYOUT (by delegation depth)"));
        let roots = g.source_roots();
        if roots.is_empty() {
            col = col.child(div().text_xs().text_color(theme::muted()).px_2().child("(no source root — the graph may be cyclic)"));
        }
        for root in roots.iter().take(4) {
            let reach = g.reach_count(root);
            col = col.child(
                div().text_xs().text_color(theme::good()).px_2().mt_1().child(format!(
                    "root {} · reaches {} cell(s) transitively{}",
                    reflect::short_hex(root.as_bytes()),
                    reach,
                    if g.has_cycle_from(root) { " · ⟳ cyclic" } else { "" },
                )),
            );
            for layer in g.layered_from(root) {
                if layer.cells.is_empty() {
                    continue;
                }
                let cells: Vec<String> = layer
                    .cells
                    .iter()
                    .map(|c| reflect::short_hex(c.as_bytes()))
                    .collect();
                col = col.child(
                    div().text_xs().text_color(theme::text()).px_3().child(format!(
                        "depth {}: {}",
                        layer.depth,
                        cells.join(", ")
                    )),
                );
            }
        }
        col
    }

    /// THE ORGANS panel — reflects each dregg organ's live cell-state. Trustline
    /// and flash-well organs are LIVE (embed-core: their enforcement is the cell's
    /// executor-installed program, fully readable from the embedded ledger);
    /// channel / mailbox / court are surfaced HONESTLY as remote-path (behind
    /// captp). See [`starbridge_v2::organs`].
    fn organs_panel(&self) -> impl IntoElement {
        let w = self.world.borrow();
        let survey = starbridge_v2::organs::OrganSurvey::build(&w);
        let mut col = div().flex().flex_col().gap_1().p_3().size_full();
        col = col.child(section_title("ORGANS · live organ cell-state").mb_1());
        col = col.child(
            div().text_xs().text_color(theme::muted()).child(format!(
                "{} live organ(s) (embed-core) · {} remote-path",
                survey.live_count(),
                survey.remote.len()
            )),
        );

        // LIVE trustline organs.
        col = col.child(div().text_xs().text_color(theme::muted()).mt_2().child("TRUSTLINES (live)"));
        if survey.trustlines.is_empty() {
            col = col.child(div().text_xs().text_color(theme::muted()).px_2().child("(no trustline organ in the world)"));
        }
        for t in &survey.trustlines {
            col = col.child(
                div().flex().flex_col().px_2().py_0p5()
                    .child(div().text_xs().text_color(theme::text()).child(format!("⬡ {} (trustline)", t.short)))
                    .child(div().text_xs().text_color(theme::accent()).child(t.summary())),
            );
        }

        // LIVE flash-well organs.
        col = col.child(div().text_xs().text_color(theme::muted()).mt_2().child("FLASH WELLS (live)"));
        if survey.flash_wells.is_empty() {
            col = col.child(div().text_xs().text_color(theme::muted()).px_2().child("(no flash-well organ in the world)"));
        }
        for f in &survey.flash_wells {
            col = col.child(
                div().flex().flex_col().px_2().py_0p5()
                    .child(div().text_xs().text_color(theme::text()).child(format!("⬡ {} (flash well)", f.short)))
                    .child(div().text_xs().text_color(theme::accent()).child(f.summary())),
            );
        }

        // REMOTE-PATH organs (honest — kind + seam + route, not faked state).
        col = col.child(div().text_xs().text_color(theme::muted()).mt_2().child("REMOTE-PATH ORGANS (need a connected node)"));
        for o in &survey.remote {
            col = col.child(
                div().flex().flex_col().px_2().py_0p5()
                    .child(div().text_xs().text_color(theme::warn()).child(format!("⬡ {} — remote-path", o.kind)))
                    .child(div().text_xs().text_color(theme::muted()).child(o.seam.to_string())),
            );
        }
        col
    }

    /// THE PROOFS panel — the proof-attach + STARK verification-status board.
    /// Each committed turn's verification tier (verified-by-construction /
    /// executor-signed / STARK-attached) + the honest route to the next tier.
    /// See [`starbridge_v2::proofs`].
    fn proofs_panel(&self) -> impl IntoElement {
        let w = self.world.borrow();
        let board = starbridge_v2::proofs::ProofBoard::build(&w, 16);
        let mut col = div().flex().flex_col().gap_1().p_3().size_full();
        col = col.child(section_title("PROOFS · attach + STARK verification status").mb_1());
        col = col.child(
            div().text_xs().text_color(theme::muted()).child(format!(
                "{} verified-by-construction · {} signed · {} STARK-attached",
                board.by_construction, board.signed, board.stark_attached
            )),
        );
        if board.is_empty() {
            col = col.child(div().text_xs().text_color(theme::muted()).px_2().mt_1().child("(no committed turns yet)"));
        }
        for e in &board.entries {
            let tier_color = match e.tier {
                starbridge_v2::proofs::VerificationTier::StarkAttached => theme::good(),
                starbridge_v2::proofs::VerificationTier::ExecutorSigned => theme::accent(),
                starbridge_v2::proofs::VerificationTier::VerifiedByConstruction => theme::text(),
            };
            col = col.child(
                div().flex().flex_col().px_2().py_0p5()
                    .child(
                        div().flex().justify_between()
                            .child(div().text_xs().text_color(theme::text()).child(format!("h{} · {}", e.height, e.receipt_short)))
                            .child(div().text_xs().text_color(tier_color).child(e.tier.label())),
                    )
                    .child(div().text_xs().text_color(theme::muted()).child(e.summary())),
            );
            if let Some(route) = e.upgrade_route() {
                col = col.child(div().text_xs().text_color(theme::muted()).px_3().child(format!("→ next: {route}")));
            }
        }
        col
    }

    /// THE WEB-OF-CELLS BROWSER panel — the cockpit as a native browser of the
    /// `dregg://` docuverse. It browses the live image's cells AS the web of
    /// cells: each cell is a `dregg://` page (the real [`starbridge_web_surface`]
    /// attested fetch + ledger-drawn origin chrome), an opened cell shows its
    /// per-viewer affordance surface (the real `AffordanceSurface::project_for`
    /// progressive attenuation) + its derived rehydration liveness-type + a
    /// transcluded field, and FIRING an affordance runs through THIS crate's
    /// embedded executor (the seam the web crate could only model, closed). The
    /// transclusion row carries the SEMI-REINTERACTIVE "⚡ make interactive" button:
    /// it runs the real
    /// [`WebCellsBrowser::upgrade_transclusion_via_powerbox`](starbridge_v2::web_cells::WebCellsBrowser::upgrade_transclusion_via_powerbox)
    /// so the
    /// user confers an ATTENUATED affordance cap reaching the transcluded SOURCE into
    /// the HOST document (a read-only quote becomes act-on-able via a powerbox grant —
    /// held-authority + non-amplification enforced by the real powerbox + executor),
    /// after which the host may fire exactly the granted affordance on the source and
    /// no wider. The model is built gpui-free in [`starbridge_v2::web_cells`] (so it is
    /// `cargo test`-able); this maps it onto gpui. See [`starbridge_v2::web_cells`].
    fn web_of_cells_panel(&self, cx: &mut Context<Self>) -> impl IntoElement {
        let viewer = self.anchors[2]; // the "user" principal the cockpit browses as
        let rights = self.web_cells_viewer_rights.clone();
        let browser = {
            let w = self.world.borrow();
            starbridge_v2::web_cells::WebCellsBrowser::build(
                &w,
                viewer,
                rights.clone(),
                self.web_cells_opened,
            )
        };
        let is_root = matches!(rights, dregg_cell::AuthRequired::None);

        let mut col = div().flex().flex_col().gap_1().p_3().size_full().overflow_hidden();
        col = col.child(
            section_title("WEB-OF-CELLS · browse the dregg:// docuverse natively").mb_1(),
        );
        // The viewer + tier header, with the "view as root/editor" toggle that
        // reveals/hides the attenuated affordances (the property, made tangible).
        col = col.child(
            div()
                .flex()
                .flex_wrap()
                .items_center()
                .gap_1()
                .child(pill(
                    format!("viewer {}", reflect::short_hex(&viewer.0)),
                    theme::accent(),
                ))
                .child(pill(format!("holds {}", browser.viewer_tier), theme::good()))
                .child(
                    div()
                        .id("web-cells-tier-toggle")
                        .px_2()
                        .py_0p5()
                        .rounded_md()
                        .bg(theme::panel_hi())
                        .border_1()
                        .border_color(theme::border())
                        .text_xs()
                        .text_color(theme::accent())
                        .cursor_pointer()
                        .hover(|s| s.bg(theme::border()))
                        .child(if is_root {
                            "view as EDITOR (attenuate)"
                        } else {
                            "view as ROOT (reveal all)"
                        })
                        .on_mouse_down(
                            MouseButton::Left,
                            cx.listener(|this, _ev, _w, cx| {
                                this.web_cells_viewer_rights = match this.web_cells_viewer_rights {
                                    dregg_cell::AuthRequired::None => {
                                        dregg_cell::AuthRequired::Either
                                    }
                                    _ => dregg_cell::AuthRequired::None,
                                };
                                // The conferred tier of a ⚡ upgrade is the viewer's
                                // tier; changing it invalidates a prior grant — drop
                                // the upgrade so re-pressing ⚡ confers the new tier.
                                this.web_cells_upgraded = None;
                                this.web_cells_transclusion_outcome = None;
                                cx.notify();
                            }),
                        ),
                ),
        );
        col = col.child(div().text_xs().text_color(theme::muted()).child(
            "A dregg:// link is a CAPABILITY into a cell; fetching it is a verified, \
             attested cross-cell read. The origin chrome is drawn from the LEDGER, never \
             the page. You see exactly the affordances your caps authorize.",
        ));

        // The web-of-cells fire outcome banner (a REAL executor verdict).
        if let Some(banner) = &self.web_cells_outcome {
            let good = banner.starts_with("committed");
            col = col.child(
                div()
                    .mt_1()
                    .px_2()
                    .py_0p5()
                    .rounded_md()
                    .bg(theme::panel_hi())
                    .text_xs()
                    .text_color(if good { theme::good() } else { theme::warn() })
                    .child(banner.clone()),
            );
        }

        // ── THE ADDRESSABLE CELLS (the dregg:// rows; clicking opens one) ──
        col = col.child(
            section_title(format!("addressable cells · {} dregg:// pages", browser.cells.len()))
                .mt_2()
                .mb_1(),
        );
        for row in &browser.cells {
            let opened = browser.opened == Some(row.cell);
            let cell = row.cell;
            let att_color = if row.attested { theme::good() } else { theme::bad() };
            col = col.child(
                div()
                    .id(SharedString::from(format!("web-cell-{}", reflect::short_hex(&cell.0))))
                    .flex()
                    .flex_col()
                    .px_2()
                    .py_0p5()
                    .rounded_md()
                    .bg(if opened { theme::panel_hi() } else { theme::panel() })
                    .border_1()
                    .border_color(if opened { theme::accent() } else { theme::border() })
                    .cursor_pointer()
                    .hover(|s| s.bg(theme::panel_hi()))
                    .on_mouse_down(
                        MouseButton::Left,
                        cx.listener(move |this, _ev, _w, cx| {
                            this.web_cells_opened = Some(cell);
                            this.web_cells_outcome = None;
                            // Opening a different cell changes the transclusion
                            // (a new host/source); drop any stale powerbox upgrade
                            // so the ⚡ interactive state never mismatches the row.
                            this.web_cells_upgraded = None;
                            this.web_cells_transclusion_outcome = None;
                            cx.notify();
                        }),
                    )
                    .child(
                        div()
                            .flex()
                            .justify_between()
                            .child(
                                div()
                                    .text_xs()
                                    .text_color(theme::text())
                                    .child(row.chrome_badge.clone()),
                            )
                            .child(
                                div()
                                    .text_xs()
                                    .text_color(att_color)
                                    .child(if row.attested { "✓ attested" } else { "⚠ unattested" }),
                            ),
                    )
                    .child(
                        div()
                            .text_xs()
                            .text_color(theme::muted())
                            .child(row.preview.clone()),
                    ),
            );
        }

        // ── THE OPENED CELL'S AFFORDANCE SURFACE (per-viewer projection) ──
        if let Some(opened) = browser.opened {
            col = col.child(
                section_title(format!("opened dregg://{} · affordance surface", reflect::short_hex(&opened.0)))
                    .mt_2()
                    .mb_1(),
            );
            col = col.child(div().text_xs().text_color(theme::muted()).child(format!(
                "you see {} of {} declared affordances — the rest are ATTENUATED away by your caps (progressive enhancement → progressive attenuation)",
                browser.affordances.len(),
                browser.affordances_declared,
            )));
            for aff in &browser.affordances {
                let name = aff.name.clone();
                let opened_cell = opened;
                let viewer_id = viewer;
                let viewer_rights = rights.clone();
                col = col.child(
                    div()
                        .flex()
                        .items_center()
                        .justify_between()
                        .px_2()
                        .py_0p5()
                        .child(
                            div().flex().flex_col().child(
                                div()
                                    .text_xs()
                                    .text_color(theme::text())
                                    .child(format!("{} → {}", aff.name, aff.effect)),
                            ).child(
                                div()
                                    .text_xs()
                                    .text_color(theme::muted())
                                    .child(format!("requires {}", aff.required)),
                            ),
                        )
                        .child(
                            // THE FIRE BUTTON — fires the affordance through the
                            // REAL embedded executor (the closed seam).
                            div()
                                .id(SharedString::from(format!("web-fire-{name}")))
                                .px_2()
                                .py_0p5()
                                .rounded_md()
                                .bg(theme::panel_hi())
                                .border_1()
                                .border_color(theme::border())
                                .text_xs()
                                .text_color(theme::good())
                                .cursor_pointer()
                                .hover(|s| s.bg(theme::border()))
                                .child("▶ fire")
                                .on_mouse_down(
                                    MouseButton::Left,
                                    cx.listener(move |this, _ev, _w, cx| {
                                        let banner = {
                                            let mut w = this.world.borrow_mut();
                                            match starbridge_v2::web_cells::WebCellsBrowser::fire_affordance(
                                                &mut w,
                                                opened_cell,
                                                viewer_id,
                                                viewer_rights.clone(),
                                                &name,
                                            ) {
                                                Ok(o) if o.is_committed() => {
                                                    format!("committed: fired '{name}' → real verified turn")
                                                }
                                                Ok(starbridge_v2::affordance::FireOutcome::Refused { reason, .. }) => {
                                                    format!("refused by executor: '{name}' — {reason}")
                                                }
                                                Ok(_) => format!("committed: fired '{name}'"),
                                                Err(e) => format!("refused in-band (anti-ghost): '{name}' — {e}"),
                                            }
                                        };
                                        this.web_cells_outcome = Some(banner);
                                        this.refresh_cells();
                                        cx.notify();
                                    }),
                                ),
                        ),
                );
            }

            // The rehydration liveness-type (DERIVED from the attested fetch).
            col = col.child(
                div()
                    .mt_1()
                    .px_2()
                    .child(pill(
                        format!("rehydration: {}", browser.rehydration_badge),
                        theme::accent(),
                    )),
            );

            // ── THE TED-NELSON TRANSCLUSION (one transcluded field + provenance) ──
            if let Some(t) = &browser.transclusion {
                col = col.child(
                    section_title("transclusion · a field included from another cell")
                        .mt_2()
                        .mb_1(),
                );
                col = col.child(div().text_xs().text_color(theme::text()).child(format!(
                    "this cell transcludes field {} from dregg://{}",
                    t.transcluded_field,
                    reflect::short_hex(&t.source.0),
                )));
                col = col.child(div().text_xs().text_color(theme::muted()).child(format!(
                    "provenance receipt {} · source finalized={} (the inclusion is CHECKABLE, not trusted)",
                    t.provenance_receipt, t.source_finalized,
                )));

                // ── SEMI-REINTERACTIVE UPGRADE (the ⚡ "make interactive" button) ──
                //
                // A plain transclusion is a READ-ONLY quote — the free verified
                // observation (a quote is a read, not a key). Pressing ⚡ runs a REAL
                // `Powerbox::grant` (via `upgrade_transclusion_via_powerbox`) so the
                // user confers an ATTENUATED affordance cap reaching the SOURCE into
                // the HOST document's c-list — the host can then FIRE one of the
                // source's affordances, attenuated to what the user holds, and no
                // wider. The conferred tier is the viewer's current tier (the
                // "view as ROOT/EDITOR" toggle), so the attenuation is the user's own
                // authority. The `view` affordance (the Signature-tier default) is the
                // one made act-on-able. Held-authority + non-amplification are enforced
                // by the real powerbox + executor — a denial leaves the quote read-only.
                let upgraded_here = self.web_cells_upgraded.as_ref().filter(|u| {
                    u.read.host == t.host && u.read.source == t.source && u.interactive
                });
                match upgraded_here {
                    // INTERACTIVE: the powerbox granted — show the conferred state +
                    // a button that fires the granted affordance on the SOURCE through
                    // the real embedded executor (and refuses any wider affordance).
                    Some(upgraded) => {
                        let fire_name = upgraded
                            .granted_affordance
                            .clone()
                            .unwrap_or_else(|| "view".to_string());
                        col = col.child(
                            div()
                                .mt_1()
                                .px_2()
                                .py_0p5()
                                .rounded_md()
                                .bg(theme::panel_hi())
                                .text_xs()
                                .text_color(theme::good())
                                .child(upgraded.affordance_note()),
                        );
                        let fire_name_btn = fire_name.clone();
                        col = col.child(
                            div()
                                .id("web-transclusion-fire")
                                .mt_1()
                                .px_2()
                                .py_0p5()
                                .rounded_md()
                                .bg(theme::panel_hi())
                                .border_1()
                                .border_color(theme::border())
                                .text_xs()
                                .text_color(theme::good())
                                .cursor_pointer()
                                .hover(|s| s.bg(theme::border()))
                                .child(format!("▶ fire `{fire_name}` on the source"))
                                .on_mouse_down(
                                    MouseButton::Left,
                                    cx.listener(move |this, _ev, _w, cx| {
                                        let banner = match this.web_cells_upgraded.clone() {
                                            Some(up) => {
                                                let mut w = this.world.borrow_mut();
                                                match starbridge_v2::web_cells::WebCellsBrowser::fire_transcluded_affordance(
                                                    &mut w,
                                                    &up,
                                                    &fire_name_btn,
                                                ) {
                                                    Ok(o) if o.is_committed() => format!(
                                                        "committed: fired `{fire_name_btn}` on the transcluded source → real verified turn"
                                                    ),
                                                    Ok(starbridge_v2::affordance::FireOutcome::Refused { reason, .. }) => format!(
                                                        "refused by executor: `{fire_name_btn}` — {reason}"
                                                    ),
                                                    Ok(_) => format!("committed: fired `{fire_name_btn}`"),
                                                    Err(e) => format!(
                                                        "refused in-band (anti-ghost): `{fire_name_btn}` — {e}"
                                                    ),
                                                }
                                            }
                                            None => "no upgraded transclusion to fire".to_string(),
                                        };
                                        this.web_cells_transclusion_outcome = Some(banner);
                                        this.refresh_cells();
                                        cx.notify();
                                    }),
                                ),
                        );
                    }
                    // READ-ONLY: offer the ⚡ upgrade. Pressing it runs the real
                    // powerbox grant through THIS crate's embedded executor.
                    None => {
                        col = col.child(div().text_xs().text_color(theme::muted()).child(
                            "READ-ONLY: this verified quote is free. Make it act-on-able with a \
                             powerbox-granted, attenuated affordance cap (a real grant turn).",
                        ));
                        let host = t.host;
                        let source = t.source;
                        let field = t.transcluded_field.clone();
                        let receipt = t.provenance_receipt.clone();
                        let finalized = t.source_finalized;
                        let confer = rights.clone();
                        col = col.child(
                            div()
                                .id("web-transclusion-make-interactive")
                                .mt_1()
                                .px_2()
                                .py_0p5()
                                .rounded_md()
                                .bg(theme::panel_hi())
                                .border_1()
                                .border_color(theme::accent())
                                .text_xs()
                                .text_color(theme::accent())
                                .cursor_pointer()
                                .hover(|s| s.bg(theme::border()))
                                .child("⚡ make interactive (powerbox-grant a source affordance)")
                                .on_mouse_down(
                                    MouseButton::Left,
                                    cx.listener(move |this, _ev, _w, cx| {
                                        // Reconstruct the read-only quote for the
                                        // currently-shown transclusion + UPGRADE it via
                                        // the POWERBOX: confer the viewer's tier over the
                                        // source so the host may fire `view`, attenuated.
                                        let read = starbridge_v2::web_cells::Transclusion {
                                            host,
                                            source,
                                            transcluded_field: field.clone(),
                                            provenance_receipt: receipt.clone(),
                                            source_finalized: finalized,
                                        };
                                        let principal = this.anchors[2]; // the cockpit user (granter)
                                        let banner = {
                                            let mut w = this.world.borrow_mut();
                                            match starbridge_v2::web_cells::WebCellsBrowser::upgrade_transclusion_via_powerbox(
                                                &mut w,
                                                read,
                                                principal,
                                                "view",
                                                confer.clone(),
                                            ) {
                                                Ok(upgraded) => {
                                                    let note = upgraded.affordance_note();
                                                    this.web_cells_upgraded = Some(upgraded);
                                                    format!("upgraded via powerbox: {note}")
                                                }
                                                Err((still_read_only, reason)) => {
                                                    this.web_cells_upgraded = Some(still_read_only);
                                                    format!("powerbox refused the upgrade: {reason}")
                                                }
                                            }
                                        };
                                        this.web_cells_transclusion_outcome = Some(banner);
                                        this.refresh_cells();
                                        cx.notify();
                                    }),
                                ),
                        );
                    }
                }

                // The transclusion-upgrade / transcluded-fire outcome banner (a REAL
                // powerbox grant-turn verdict, or the in-band read-only/over-wide refusal).
                if let Some(banner) = &self.web_cells_transclusion_outcome {
                    let good = banner.starts_with("upgraded") || banner.starts_with("committed");
                    col = col.child(
                        div()
                            .mt_1()
                            .px_2()
                            .py_0p5()
                            .rounded_md()
                            .bg(theme::panel_hi())
                            .text_xs()
                            .text_color(if good { theme::good() } else { theme::warn() })
                            .child(banner.clone()),
                    );
                }
            }
        }

        // ── THE DREGGVERSE DOCUMENT (Nelson's EDL made honest — the rich span
        //    model welded in from `deos-web-cells`) ──
        //
        // Where the transclusion above is ONE whole-field quote, this is a MULTI-SPAN
        // document: OWN content interleaved with byte-RANGE quotes of peer cells,
        // resolved PER-VIEWER through the REAL membrane. A span the viewer's projected
        // fetch-allowlist cannot reach renders DARKENED — its provenance survives (the
        // citation), its bytes withheld (never forged). The model is built gpui-free in
        // `starbridge_v2::web_cells` (so the composed text + the darkened span + the
        // surviving provenance are `cargo test`-proven); this maps it onto gpui.
        if let Some(doc) = &browser.document {
            col = col.child(section_title(doc.title.clone()).mt_2().mb_1());

            // The per-viewer summary pills: the document's shape + how much of it THIS
            // viewer can read (a darkened span ⇒ "not fully readable for you").
            col = col.child(
                div()
                    .flex()
                    .flex_row()
                    .gap_1()
                    .child(pill(
                        format!("{} spans", doc.span_count),
                        theme::accent(),
                    ))
                    .child(pill(
                        format!("{} verified quotes", doc.quote_count),
                        theme::good(),
                    ))
                    .child(pill(
                        if doc.darkened_count == 0 {
                            "fully readable".to_string()
                        } else {
                            format!("{} darkened (per-viewer)", doc.darkened_count)
                        },
                        if doc.full { theme::good() } else { theme::warn() },
                    )),
            );

            // The composed text THIS viewer sees (OWN + reachable quotes; a darkened
            // span contributes nothing — the honest per-viewer render).
            col = col.child(
                div()
                    .mt_1()
                    .px_2()
                    .py_0p5()
                    .rounded_md()
                    .bg(theme::panel())
                    .text_xs()
                    .text_color(theme::text())
                    .child(format!("\u{201C}{}\u{201D}", doc.composed_text)),
            );

            // The EDL, span by span — OWN content, a verified quote (with its cited
            // byte range + provenance), or a DARKENED span (citation kept, bytes
            // withheld). Each row is styled by kind so the docuverse skeleton is
            // visible: the reader sees WHICH spans exist + where they are quoted from,
            // even the one they cannot read.
            for span in &doc.spans {
                let row = match span.kind {
                    starbridge_v2::web_cells::DocumentSpanKind::Own => div()
                        .text_xs()
                        .text_color(theme::text())
                        .child(format!("own · \u{201C}{}\u{201D}", span.text)),
                    starbridge_v2::web_cells::DocumentSpanKind::Quote => div()
                        .text_xs()
                        .text_color(theme::good())
                        .child(format!(
                            "quote {} · \u{201C}{}\u{201D} · from {} · commitment {} · receipt {}",
                            span.range.as_deref().unwrap_or("?"),
                            span.text,
                            span.source.as_deref().unwrap_or("?"),
                            span.content_commitment.as_deref().unwrap_or("?"),
                            span.provenance_receipt.as_deref().unwrap_or("?"),
                        )),
                    starbridge_v2::web_cells::DocumentSpanKind::Darkened => div()
                        .text_xs()
                        .text_color(theme::muted())
                        .child(format!(
                            "darkened {} · [you lack authority to read this span] · cites {} · commitment {} · receipt {}",
                            span.range.as_deref().unwrap_or("?"),
                            span.source.as_deref().unwrap_or("?"),
                            span.content_commitment.as_deref().unwrap_or("?"),
                            span.provenance_receipt.as_deref().unwrap_or("?"),
                        )),
                };
                col = col.child(row.mt_0p5().px_2());
            }

            // The per-viewer authority note — WHY some spans darken (the real membrane
            // fetch-allowlist meet, never a forgery).
            col = col.child(
                div()
                    .mt_1()
                    .px_2()
                    .text_xs()
                    .text_color(theme::muted())
                    .child(doc.viewer_note.clone()),
            );
        }

        // ── THE SERVO LAYER ──
        // With feature `servo` ON and a rendered tile present, paint the REAL
        // cap-gated SWGL frame of the opened cell's attested `dregg://` page —
        // the first real rendered `dregg://` CONTENT in the tab. Otherwise
        // (feature-off, or the cap refused the page so no frame) fall back to the
        // servo_layer_note() placeholder that NAMES the next layer.
        #[cfg(feature = "servo")]
        let servo_tile: Option<gpui::AnyElement> =
            browser.rendered_tile.as_ref().map(|frame| {
                div()
                    .mt_2()
                    .p_2()
                    .rounded_md()
                    .border_1()
                    .border_color(theme::good())
                    .bg(theme::panel())
                    .child(
                        div()
                            .text_xs()
                            .text_color(theme::good())
                            .child("SERVO: real cap-gated SWGL render of the opened cell's attested dregg:// page"),
                    )
                    .child(
                        gpui::img(rgba_frame_to_image(frame))
                            .w(gpui::px(frame.width as f32))
                            .h(gpui::px(frame.height as f32)),
                    )
                    .into_any_element()
            });
        #[cfg(not(feature = "servo"))]
        let servo_tile: Option<gpui::AnyElement> = None;

        col = col.child(servo_tile.unwrap_or_else(|| {
            div()
                .mt_2()
                .p_2()
                .rounded_md()
                .border_1()
                .border_color(theme::border())
                .bg(theme::panel())
                .child(
                    div()
                        .text_xs()
                        .text_color(theme::muted())
                        .child(browser.servo_layer_note()),
                )
                .into_any_element()
        }));
        col
    }

    /// THE WHAT-LINKS-HERE panel — Ted Nelson's two-way link, navigable.
    ///
    /// For the focused cell it renders the REAL [`Backlinks`] witness-graph (who
    /// transcludes ME), navigated by the genuine
    /// [`DreggverseMap`](starbridge_v2::dreggverse_map::DreggverseMap) and PROJECTED
    /// through the focused agent's [`Membrane`] via
    /// [`DreggverseMap::project_for`](starbridge_v2::dreggverse_map::DreggverseMap::project_for):
    /// a backlink whose link lineage the viewer's held authority cannot admit (the
    /// REAL `is_attenuation` lattice) is OMITTED — the link fog-of-war. Each visible
    /// backlink carries its cited receipt + content commitment (a verifiable fact) and
    /// is CLICKABLE to navigate INTO the observing cell (whose own what-links-here then
    /// renders — recursive docuverse navigation). The cockpit owns the render +
    /// click-to-navigate; the verified per-viewer graph is the vendored map's. The
    /// model is built gpui-free in [`starbridge_v2::links_here`] (so it is `cargo
    /// test`-able); this maps it onto gpui.
    ///
    /// The viewer authority is the panel's own held-authority lens
    /// (`links_here_viewer_rights`, None ⇄ Signature): the focus's backlinks are gated
    /// behind a `Proof` link lineage, so a `None` (root) viewer projects it and SEES
    /// them while an INCOMPARABLE `Signature` viewer is FOGGED — flipping the toggle
    /// reveals/fogs the gated backlink, the membrane made navigational. The focused
    /// cell defaults to the cockpit's own `user` principal.
    fn links_here_panel(&self, cx: &mut Context<Self>) -> impl IntoElement {
        let focus = self.links_here_focus.unwrap_or(self.anchors[2]); // the cockpit `user`
        let rights = self.links_here_viewer_rights.clone();
        let depth = self.links_here_depth;
        let panel = {
            let w = self.world.borrow();
            starbridge_v2::links_here::LinksHerePanel::build(&w, focus, rights.clone(), depth)
        };
        let is_root = matches!(rights, dregg_cell::AuthRequired::None);

        let mut col = div().flex().flex_col().gap_1().p_3().size_full().overflow_hidden();
        col = col.child(
            section_title("WHAT-LINKS-HERE · Ted Nelson's two-way link, navigable").mb_1(),
        );
        col = col.child(div().text_xs().text_color(theme::muted()).child(
            "The forward link points OUT (a cell transcludes another). This is the link the \
             OTHER way — who transcludes ME — the REAL Backlinks witness-graph, navigated by \
             DreggverseMap and PROJECTED through your membrane. Each backlink carries its cited \
             receipt + content commitment (a verifiable fact). Click a backlink to navigate into \
             the observing cell.",
        ));

        // ── THE FOCUS + VIEWER HEADER (with the held-authority + depth toggles) ──
        col = col.child(
            div()
                .flex()
                .flex_wrap()
                .items_center()
                .gap_1()
                .child(pill(
                    format!("focus {}", reflect::short_hex(&focus.0)),
                    theme::accent(),
                ))
                .child(pill(format!("holds {}", panel.viewer_tier), theme::good()))
                .child(pill(format!("depth {}", panel.depth), theme::accent()))
                // The held-authority toggle (None ⇄ Signature): the viewer's authority
                // decides the link fog-of-war. At ROOT (None) the Proof-gated backlinks
                // are visible; dropping to the INCOMPARABLE Signature tier FOGS them
                // (the membrane refuses the lineage) — the property made tangible.
                .child(
                    div()
                        .id("links-here-tier-toggle")
                        .px_2()
                        .py_0p5()
                        .rounded_md()
                        .bg(theme::panel_hi())
                        .border_1()
                        .border_color(theme::border())
                        .text_xs()
                        .text_color(theme::accent())
                        .cursor_pointer()
                        .hover(|s| s.bg(theme::border()))
                        .child(if is_root {
                            "view as SIGNATURE (fog the gated links)"
                        } else {
                            "view as ROOT (reveal all)"
                        })
                        .on_mouse_down(
                            MouseButton::Left,
                            cx.listener(|this, _ev, _w, cx| {
                                this.links_here_viewer_rights = match this.links_here_viewer_rights {
                                    dregg_cell::AuthRequired::None => {
                                        dregg_cell::AuthRequired::Signature
                                    }
                                    _ => dregg_cell::AuthRequired::None,
                                };
                                cx.notify();
                            }),
                        ),
                )
                // The depth toggle (1 ⇄ 2 ⇄ 3): how many hops of backlinks-of-backlinks
                // the transitive walk reaches. The walk is cycle-safe + depth-bounded.
                .child(
                    div()
                        .id("links-here-depth-toggle")
                        .px_2()
                        .py_0p5()
                        .rounded_md()
                        .bg(theme::panel_hi())
                        .border_1()
                        .border_color(theme::border())
                        .text_xs()
                        .text_color(theme::accent())
                        .cursor_pointer()
                        .hover(|s| s.bg(theme::border()))
                        .child("cycle depth")
                        .on_mouse_down(
                            MouseButton::Left,
                            cx.listener(|this, _ev, _w, cx| {
                                // 1 → 2 → 3 → 1 (a small, finite, demonstrable range).
                                this.links_here_depth = match this.links_here_depth {
                                    0 | 1 => 2,
                                    2 => 3,
                                    _ => 1,
                                };
                                cx.notify();
                            }),
                        ),
                ),
        );

        // The focus address + a "navigate to user (home focus)" affordance so the
        // operator can always return to the principal's docuverse after drilling in.
        col = col.child(
            div()
                .flex()
                .items_center()
                .gap_1()
                .mt_1()
                .child(div().text_xs().text_color(theme::text()).child(format!(
                    "asking: who links to {} ?",
                    panel.focus_uri
                )))
                .child(
                    div()
                        .id("links-here-refocus-user")
                        .px_2()
                        .py_0p5()
                        .rounded_md()
                        .bg(theme::panel_hi())
                        .border_1()
                        .border_color(theme::border())
                        .text_xs()
                        .text_color(theme::muted())
                        .cursor_pointer()
                        .hover(|s| s.bg(theme::border()))
                        .child("↺ focus the user principal")
                        .on_mouse_down(
                            MouseButton::Left,
                            cx.listener(|this, _ev, _w, cx| {
                                this.links_here_focus = None; // None = the user anchor
                                cx.notify();
                            }),
                        ),
                ),
        );

        // ── THE VISIBLE-OF-TOTAL READOUT (the fog made legible) ──
        let fogged = panel.fogged_count();
        col = col.child(div().text_xs().text_color(theme::muted()).child(format!(
            "you see {} of {} backlink(s) within {} hop(s) — {} fogged by your caps · {} navigable node(s)",
            panel.backlinks.len(),
            panel.total_link_count,
            panel.depth,
            fogged,
            panel.visible_nodes,
        )));
        if panel.has_gated_links && fogged > 0 {
            col = col.child(div().text_xs().text_color(theme::warn()).child(
                "some backlinks are GATED behind a link lineage your held authority cannot project \
                 — the membrane omits them (try 'view as ROOT'). This is the link fog-of-war: two \
                 viewers navigate DIFFERENT maps of the same docuverse.",
            ));
        }

        // ── THE BACKLINK ROWS (each clickable to navigate INTO the observer) ──
        if panel.is_empty() {
            col = col.child(
                div()
                    .mt_2()
                    .px_2()
                    .py_1()
                    .text_xs()
                    .text_color(theme::muted())
                    .child(
                        "no backlinks visible to you — nobody you are cleared to see transcludes \
                         this cell (an honest empty readout, never a dangling guess).",
                    ),
            );
        } else {
            col = col.child(
                section_title(format!("backlinks · {} two-way link(s) you can see", panel.backlinks.len()))
                    .mt_2()
                    .mb_1(),
            );
        }
        for b in &panel.backlinks {
            let observer = b.observer;
            col = col.child(
                div()
                    .id(SharedString::from(format!("links-here-{}", reflect::short_hex(&observer.0))))
                    .flex()
                    .flex_col()
                    .px_2()
                    .py_0p5()
                    .rounded_md()
                    .bg(theme::panel())
                    .border_1()
                    .border_color(theme::border())
                    .cursor_pointer()
                    .hover(|s| s.bg(theme::panel_hi()))
                    .on_mouse_down(
                        MouseButton::Left,
                        cx.listener(move |this, _ev, _w, cx| {
                            // NAVIGATE INTO the observing cell — render ITS own
                            // what-links-here (recursive docuverse navigation).
                            this.links_here_focus = Some(observer);
                            cx.notify();
                        }),
                    )
                    .child(
                        div()
                            .flex()
                            .justify_between()
                            .child(
                                div()
                                    .text_xs()
                                    .text_color(theme::accent())
                                    .child(format!("← {}", b.observer_uri)),
                            )
                            .child(
                                div()
                                    .text_xs()
                                    .text_color(theme::muted())
                                    .child(format!("hop {}", b.hops)),
                            ),
                    )
                    .child(
                        div()
                            .text_xs()
                            .text_color(theme::muted())
                            .child(format!(
                                "transcludes dregg://{} · receipt {} · commitment {}",
                                reflect::short_hex(&b.source.0),
                                b.receipt_hash,
                                b.content_hash,
                            )),
                    ),
            );
        }

        // ── THE SEEDED-GRAPH NOTE (named honestly in the panel) ──
        col = col.child(
            div()
                .mt_2()
                .p_2()
                .rounded_md()
                .border_1()
                .border_color(theme::border())
                .bg(theme::panel())
                .child(
                    div()
                        .text_xs()
                        .text_color(theme::muted())
                        .child(panel.seeded_note()),
                ),
        );
        col
    }

    /// THE POWERBOX panel (CapDesk) — the trusted designation flow, rendered.
    ///
    /// The cockpit `user` principal is the GRANTING identity; a confined demo
    /// app-cell (`powerbox_app`) is the requester. The panel presents the powerbox
    /// over the live world: the app's request, then the picker of GRANTABLE targets
    /// (every cell the USER actually holds a cap reaching — `mint_needs_held_factory`
    /// made visible). Designating a target MINTS a fresh attenuated cap into the
    /// app's c-list via a REAL [`Powerbox::grant`] turn through the embedded executor
    /// — the conferral is `≤` the user's held authority (the powerbox refuses to
    /// amplify; the executor is the backstop). The panel content is exactly the
    /// powerbox model's [`Powerbox::all_text`], so the gpui-free `cargo test` proves
    /// the rendered tree without a GPU.
    fn powerbox_panel(&self, cx: &mut Context<Self>) -> impl IntoElement {
        use starbridge_v2::powerbox::{CapabilityRequest, Powerbox};

        let principal = self.anchors[2]; // the cockpit's own `user` identity — the granter
        let app = self
            .powerbox_app
            .unwrap_or(principal); // the confined requester (a demo app-as-cell)
        let confer = self.powerbox_confer_rights.clone();

        // The app's standing request (it holds no authority; it can only ask). If `app`
        // was LAUNCHED at runtime (via the app-launcher), use ITS OWN recorded request
        // (the real `CapabilityRequest` the launched confined app raised) — so the panel
        // routes the genuine launched-app request through the existing powerbox; the
        // boot-seeded demo app falls back to the standing demo request.
        let request = self
            .launched_apps
            .iter()
            .find(|a| a.app_cell == app)
            .map(|a| a.request.clone())
            .unwrap_or_else(|| {
                CapabilityRequest::new(
                    app,
                    "this app needs to reach one peer/resource — designate exactly one",
                    dregg_cell::AuthRequired::None,
                )
            });
        let pb = {
            let w = self.world.borrow();
            Powerbox::present(&w, principal, &request)
        };
        let launched_count = self.launched_apps.len();

        let mut col = div().flex().flex_col().gap_1().p_3().size_full().overflow_hidden();
        col = col.child(
            section_title("POWERBOX · CapDesk — designate a held cap into a confined app").mb_1(),
        );
        col = col.child(
            div()
                .flex()
                .flex_wrap()
                .items_center()
                .gap_1()
                .child(pill(
                    format!("you (granter) {}", reflect::short_hex(&principal.0)),
                    theme::accent(),
                ))
                .child(pill(
                    format!("app (requester) {}", reflect::short_hex(&app.0)),
                    theme::good(),
                ))
                // The confer-tier toggle: the rights the next designation confers. The
                // grant is ≤ the user's held authority; the powerbox refuses to amplify
                // past the held ceiling, so a wider tier than the user holds is refused.
                .child(
                    div()
                        .id("powerbox-tier-toggle")
                        .px_2()
                        .py_0p5()
                        .rounded_md()
                        .bg(theme::panel_hi())
                        .border_1()
                        .border_color(theme::border())
                        .text_xs()
                        .text_color(theme::accent())
                        .cursor_pointer()
                        .hover(|s| s.bg(theme::border()))
                        .child(format!("confer: {confer:?} (cycle)"))
                        .on_mouse_down(
                            MouseButton::Left,
                            cx.listener(|this, _ev, _w, cx| {
                                // Cycle Signature → Either → None → Signature: from the
                                // narrowest (a strong attenuation) up through the wider
                                // tiers (still gated by the held ceiling + the executor).
                                this.powerbox_confer_rights = match this.powerbox_confer_rights {
                                    dregg_cell::AuthRequired::Signature => {
                                        dregg_cell::AuthRequired::Either
                                    }
                                    dregg_cell::AuthRequired::Either => {
                                        dregg_cell::AuthRequired::None
                                    }
                                    _ => dregg_cell::AuthRequired::Signature,
                                };
                                cx.notify();
                            }),
                        ),
                )
                // THE RUNTIME APP-LAUNCHER button — birth a fresh confined app (no
                // ambient authority) and route ITS request through this powerbox. The
                // powerbox's missing first half: spawn the confined requester on demand.
                .child(
                    div()
                        .id("powerbox-launch-app")
                        .px_2()
                        .py_0p5()
                        .rounded_md()
                        .bg(theme::panel_hi())
                        .border_1()
                        .border_color(theme::accent())
                        .text_xs()
                        .text_color(theme::good())
                        .cursor_pointer()
                        .hover(|s| s.bg(theme::border()))
                        .child("+ launch confined app")
                        .on_mouse_down(
                            MouseButton::Left,
                            cx.listener(|this, _ev, _w, cx| {
                                // Births a fresh confined app-cell + routes its request
                                // through the existing powerbox (sets it as powerbox_app).
                                this.run_launch_confined_app(cx);
                            }),
                        ),
                ),
        );
        col = col.child(div().text_xs().text_color(theme::muted()).child(
            "The app holds NO ambient authority — it can only ASK. The powerbox (this \
             trusted UI, NOT the app) can grant ONLY from YOUR own held caps: you can't \
             grant what you don't hold (mint_needs_held_factory). Designating a target \
             MINTS a fresh ATTENUATED cap into the app via a real verified grant turn. \
             Press '+ launch confined app' to SPAWN a new confined app at runtime (it \
             holds nothing — it requests through this powerbox).",
        ));
        // The runtime-launched apps roster (each a fresh confined app birthed on demand).
        if launched_count > 0 {
            col = col.child(div().text_xs().text_color(theme::accent()).child(format!(
                "{launched_count} confined app(s) launched at runtime · now mediating: {}",
                reflect::short_hex(&app.0)
            )));
        }
        col = col.child(div().text_xs().text_color(theme::muted()).italic().child(format!(
            "reason: {}",
            pb.reason
        )));

        // The last designation outcome banner (a REAL grant-turn verdict).
        if let Some(banner) = &self.powerbox_outcome {
            let good = banner.starts_with("granted");
            col = col.child(
                div()
                    .mt_1()
                    .px_2()
                    .py_0p5()
                    .rounded_md()
                    .bg(theme::panel_hi())
                    .text_xs()
                    .text_color(if good { theme::good() } else { theme::warn() })
                    .child(banner.clone()),
            );
        }

        // ── THE PICKER: every target the USER holds (the only things designable) ──
        col = col.child(
            section_title(format!(
                "designate a target you hold · {} grantable (you can't grant what you don't hold)",
                pb.grantable.len()
            ))
            .mt_2()
            .mb_1(),
        );
        if pb.grantable.is_empty() {
            col = col.child(div().text_xs().text_color(theme::warn()).child(
                "(you hold no grantable targets — the powerbox can confer nothing, by construction)",
            ));
        }
        for g in &pb.grantable {
            let target = g.target;
            let held = g.held_rights.clone();
            let confer_now = confer.clone();
            col = col.child(
                div()
                    .id(SharedString::from(format!(
                        "powerbox-target-{}",
                        reflect::short_hex(&target.0)
                    )))
                    .flex()
                    .justify_between()
                    .items_center()
                    .px_2()
                    .py_0p5()
                    .rounded_md()
                    .bg(theme::panel())
                    .border_1()
                    .border_color(theme::border())
                    .cursor_pointer()
                    .hover(|s| s.bg(theme::panel_hi()))
                    .on_mouse_down(
                        MouseButton::Left,
                        cx.listener(move |this, _ev, _w, cx| {
                            // THE DESIGNATION: mint a fresh attenuated cap into the app
                            // via a REAL grant turn through the embedded executor.
                            let outcome = {
                                let mut w = this.world.borrow_mut();
                                Powerbox::grant(
                                    &mut w,
                                    this.anchors[2],
                                    this.powerbox_app.unwrap_or(this.anchors[2]),
                                    target,
                                    this.powerbox_confer_rights.clone(),
                                )
                            };
                            this.powerbox_outcome = Some(match outcome {
                                starbridge_v2::powerbox::PowerboxOutcome::Granted {
                                    conferred,
                                    receipt,
                                } => format!(
                                    "granted: app {} now holds {:?} reaching {} (slot {}) — receipt {}",
                                    reflect::short_hex(&conferred.app_cell.0),
                                    conferred.conferred_rights,
                                    reflect::short_hex(&conferred.target.0),
                                    conferred.slot,
                                    reflect::short_hex(&receipt.receipt_hash())
                                ),
                                starbridge_v2::powerbox::PowerboxOutcome::Denied { reason } => {
                                    format!("denied: {reason}")
                                }
                            });
                            this.refresh_cells();
                            cx.notify();
                        }),
                    )
                    .child(
                        div()
                            .text_xs()
                            .text_color(theme::text())
                            .child(format!("{}  (you hold {:?})", g.label, held)),
                    )
                    .child(
                        div()
                            .text_xs()
                            .text_color(theme::accent())
                            .child(format!("→ grant {confer_now:?}")),
                    ),
            );
        }

        col
    }

    /// THE ⌘K COMMAND PALETTE overlay — a centered, fuzzy-filtered list over
    /// EVERY action. Rendered on top of the cockpit when open. The query +
    /// selection live in `self.palette`; keystrokes are handled in [`on_key`];
    /// a click on a row also dispatches it.
    fn palette_overlay(&self, cx: &mut Context<Self>) -> impl IntoElement {
        let results = self.palette.results();
        let selected = self.palette.selected();
        let query = self.palette.query().to_string();

        // A full-screen scrim that closes the palette on a click-out.
        let scrim = div()
            .id("palette-scrim")
            .absolute()
            .top_0()
            .left_0()
            .size_full()
            .bg(gpui::rgba(0x00000088))
            .flex()
            .flex_col()
            .items_center()
            .on_mouse_down(
                MouseButton::Left,
                cx.listener(|this, _ev, _w, cx| {
                    this.palette.close();
                    cx.notify();
                }),
            );

        // The palette card.
        let mut card = div()
            .id("palette-card")
            .mt(px(120.))
            .w(px(560.))
            .max_h(px(440.))
            .flex()
            .flex_col()
            .rounded_md()
            .border_1()
            .border_color(theme::accent())
            .bg(theme::panel())
            // Swallow clicks on the card so they don't reach the scrim's close.
            .on_mouse_down(MouseButton::Left, |_ev, _w, cx| cx.stop_propagation());

        // The query line.
        card = card.child(
            div()
                .flex()
                .justify_between()
                .px_3()
                .py_2()
                .border_b_1()
                .border_color(theme::border())
                .child(
                    div()
                        .text_color(theme::text())
                        .child(if query.is_empty() {
                            "⌘K  type to search every action…".to_string()
                        } else {
                            format!("⌘K  {query}▌")
                        }),
                )
                .child(
                    div()
                        .text_xs()
                        .text_color(theme::muted())
                        .child(format!("{} match", results.len())),
                ),
        );

        // The results list.
        let mut list = div().flex().flex_col().gap_0p5().p_1().overflow_hidden();
        if results.is_empty() {
            list = list.child(
                div()
                    .px_2()
                    .py_1()
                    .text_xs()
                    .text_color(theme::muted())
                    .child("(no matching action — Esc to close)"),
            );
        }
        for (i, hit) in results.iter().enumerate().take(12) {
            let active = i == selected;
            let (badge, bcolor) = category_badge(hit.command.category);
            let id = hit.command.id;
            list = list.child(
                div()
                    .id(SharedString::from(format!("palette-row-{i}")))
                    .flex()
                    .justify_between()
                    .items_center()
                    .px_2()
                    .py_1()
                    .rounded_md()
                    .bg(if active { theme::panel_hi() } else { theme::panel() })
                    .cursor_pointer()
                    .hover(|s| s.bg(theme::border()))
                    .on_mouse_down(
                        MouseButton::Left,
                        cx.listener(move |this, _ev, _w, cx| {
                            this.palette.close();
                            this.dispatch(id, cx);
                            cx.notify();
                        }),
                    )
                    .child(
                        div()
                            .text_xs()
                            .text_color(if active { theme::accent() } else { theme::text() })
                            .child(format!("{} {}", if active { "▸" } else { " " }, hit.command.title)),
                    )
                    .child(pill(badge, bcolor)),
            );
        }
        card = card.child(list);

        // Footer hint.
        card = card.child(
            div()
                .px_3()
                .py_1()
                .border_t_1()
                .border_color(theme::border())
                .text_xs()
                .text_color(theme::muted())
                .child("↑↓ select · ⏎ run · esc close"),
        );

        scrim.child(card)
    }

    /// THE A1 EDITOR/BUFFER panel — a text buffer as a cap-confined Surface cell.
    /// Maps `buffer::BufferView` (gpui-free) onto gpui: the buffer header (its
    /// backing cell, revision, read-only/dirty badges, digests), the cap-gated
    /// action row (type · commit · the read-only-write REFUSE teaching moment),
    /// and the buffer body (the editable text, with line numbers). You watch the
    /// authenticated digest advance through a verified turn — not a self-report.
    fn buffer_panel(&self, cx: &mut Context<Self>) -> impl IntoElement {
        let w = self.world.borrow();
        let v = BufferView::build(&self.editor_buffer, &w, Some(&self.editor_buffer_cap));
        drop(w);

        let mut col = div().flex().flex_col().gap_2().p_3().size_full();
        col = col.child(section_title("EDITOR · a text buffer as a cap-confined Surface cell").mb_1());
        col = col.child(div().text_xs().text_color(theme::muted()).child(
            "The buffer is backed by a REAL cell: its content DIGEST rides the cell's state, and \
             its REVISION is the cell's nonce. Editing the text is free (in-memory); COMMITTING is \
             a CAP-GATED verified turn (a SetField writing the digest). A read-only buffer holds an \
             ATTENUATED cap — a write to it REFUSES (no-amplification at the editor).",
        ));

        // The buffer header: backing cell, state, badges, digests.
        let backed_color = if v.backed { theme::good() } else { theme::bad() };
        let rw_badge = if v.read_only { ("read-only", theme::warn()) } else { ("writable", theme::good()) };
        let clean_badge = if v.clean { ("clean", theme::good()) } else { ("DIRTY (unsaved)", theme::warn()) };
        col = col.child(
            div()
                .flex()
                .flex_wrap()
                .gap_1()
                .items_center()
                .child(pill(v.name.clone(), theme::accent()))
                .child(pill(format!("cell {}", v.backing_short), theme::text()))
                .child(pill(if v.backed { "live" } else { "UNBACKED" }.to_string(), backed_color))
                .child(pill(rw_badge.0, rw_badge.1))
                .child(pill(clean_badge.0, clean_badge.1))
                .child(pill(format!("rev {}", v.revision), theme::muted())),
        );
        col = col.child(
            div()
                .flex()
                .flex_wrap()
                .gap_1()
                .items_center()
                .child(div().text_xs().text_color(theme::muted()).child("doc digest"))
                .child(pill(v.doc_digest_short.clone(), theme::accent()))
                .when(v.stored_digest_short.is_some(), |d| {
                    d.child(div().text_xs().text_color(theme::muted()).child("committed"))
                        .child(pill(v.stored_digest_short.clone().unwrap(), theme::good()))
                }),
        );

        // The cap-gated action row.
        col = col.child(
            div()
                .flex()
                .flex_wrap()
                .gap_1()
                .items_center()
                .mt_1()
                .child(shell_button(cx, "type a line", theme::accent(), Cockpit::buffer_type_demo))
                .child(shell_button(cx, "commit (cap-gated turn)", theme::good(), Cockpit::buffer_commit))
                .child(shell_button(cx, "⚠ read-only write (REFUSE)", theme::warn(), Cockpit::buffer_readonly_write_demo)),
        );

        // The buffer body: the editable text with line numbers.
        col = col.child(section_title("buffer (the surface content)").mt_2());
        let mut body = div().flex().flex_col().gap_0p5().p_2().rounded_md().bg(theme::panel());
        for (i, line) in v.lines.iter().enumerate() {
            body = body.child(
                div()
                    .flex()
                    .gap_2()
                    .child(div().text_xs().text_color(theme::muted()).w(px(28.)).child(format!("{:>3}", i + 1)))
                    .child(div().text_xs().text_color(theme::text()).font_family("Menlo").child(line.clone())),
            );
        }
        col = col.child(body);
        col = col.child(
            div().text_xs().text_color(theme::muted()).mt_1().child(format!(
                "cursor @ byte {} · {} line(s) — the digest above is what a COMMIT would bind into the cell",
                v.cursor,
                v.lines.len()
            )),
        );
        col
    }

    /// THE A1 TERMINAL panel — a command surface as a cap-confined Surface cell
    /// (the home of the ADOS tool-call seam). Maps `terminal::TerminalView`
    /// (gpui-free) onto gpui: the terminal header (its backing cell + its
    /// MANDATE — the targets it may reach), the cap-gated action row (an
    /// in-mandate command COMMITS; an out-of-mandate one REFUSES), and the output
    /// body (each command + its REAL receipt, or its REFUSAL — never faked).
    fn terminal_panel(&self, cx: &mut Context<Self>) -> impl IntoElement {
        let w = self.world.borrow();
        let v = TerminalView::build(&self.terminal, &w);
        drop(w);

        let mut col = div().flex().flex_col().gap_2().p_3().size_full();
        col = col.child(section_title("TERMINAL · a command surface as a cap-confined Surface cell").mb_1());
        col = col.child(div().text_xs().text_color(theme::muted()).child(
            "A command is a CAP-GATED action: the terminal-cell holds the cap for what it may run / \
             touch, and the output is its receipt. This is WHERE THE ADOS TOOL-CALL SEAM LIVES — an \
             agent's Bash routed through the terminal-cell's cap. A command whose target is within \
             the cell's mandate COMMITS (its receipt is the output); one outside it REFUSES.",
        ));

        // The terminal header: backing cell + the mandate (reachable targets).
        let backed_color = if v.backed { theme::good() } else { theme::bad() };
        col = col.child(
            div()
                .flex()
                .flex_wrap()
                .gap_1()
                .items_center()
                .child(pill(v.name.clone(), theme::accent()))
                .child(pill(format!("cell {}", v.backing_short), theme::text()))
                .child(pill(if v.backed { "live" } else { "UNBACKED" }.to_string(), backed_color))
                .child(pill(format!("{} committed", v.committed_count), theme::good())),
        );
        col = col.child(section_title("mandate — the targets this terminal may reach").mt_1());
        let mut mandate = div().flex().flex_wrap().gap_1().items_center();
        for t in &v.reachable_short {
            mandate = mandate.child(pill(format!("→ {t}"), theme::accent()));
        }
        col = col.child(mandate);

        // The cap-gated action row.
        col = col.child(
            div()
                .flex()
                .flex_wrap()
                .gap_1()
                .items_center()
                .mt_1()
                .child(shell_button(cx, "run in-mandate (COMMITS)", theme::good(), Cockpit::terminal_run_in_mandate))
                .child(shell_button(cx, "⚠ run out-of-mandate (REFUSE)", theme::warn(), Cockpit::terminal_run_out_of_mandate)),
        );

        // The output body: commands + receipts / refusals (oldest-first).
        col = col.child(section_title("output (commands + receipts — the surface content)").mt_2());
        if v.lines.is_empty() {
            col = col.child(div().text_xs().text_color(theme::muted()).child(
                "no commands yet — run one above; an in-mandate target COMMITS, an out-of-mandate one REFUSES.",
            ));
        } else {
            let mut body = div().flex().flex_col().gap_0p5();
            for l in &v.lines {
                let (mark, mark_color) = if l.committed { ("$", theme::good()) } else { ("✗", theme::bad()) };
                body = body.child(
                    div()
                        .flex()
                        .flex_col()
                        .gap_0p5()
                        .px_2()
                        .py_0p5()
                        .rounded_md()
                        .bg(theme::panel())
                        .child(
                            div()
                                .flex()
                                .gap_2()
                                .items_center()
                                .child(div().text_xs().text_color(mark_color).child(mark))
                                .child(div().text_xs().text_color(theme::text()).font_family("Menlo").child(l.command.clone()))
                                .when(l.committed, |d| {
                                    d.child(pill(format!("{} ⚙", l.computrons), theme::muted()))
                                })
                                .when(l.receipt_short().is_some(), |d| {
                                    d.child(pill(l.receipt_short().unwrap(), theme::good()))
                                }),
                        )
                        .child(
                            div()
                                .text_xs()
                                .text_color(if l.committed { theme::muted() } else { theme::bad() })
                                .font_family("Menlo")
                                .child(l.result.clone()),
                        ),
                );
            }
            col = col.child(body);
        }
        col
    }

    /// THE LIVE EDITOR panel — `edit::render_panel` is gpui-free text; the
    /// cockpit presents it line-by-line.
    fn editor_panel(&self) -> impl IntoElement {
        let text = edit::render_panel(&self.editor);
        let mut col = div().flex().flex_col().p_3().size_full();
        col = col.child(section_title("LIVE EDITOR · author · validate · deploy").mb_1());
        for line in text.lines() {
            col = col.child(div().text_xs().text_color(theme::text()).font_family("Menlo").child(line.to_string()));
        }
        col
    }
}

impl Cockpit {
    /// Drain the LIVE NODE's SSE receipt stream into the feed (called once per
    /// render). Each streamed receipt is ingested into `live_feed` (deduped by
    /// chain index); if any were NEW, we `cx.notify()` so the cockpit re-renders
    /// promptly — that is the per-receipt live update REPLACING the static
    /// snapshot. When a receipt stream is connected we ALSO schedule a follow-up
    /// frame (a short deferral) so a continuously-streaming node keeps the loop
    /// turning even between input events. No-op when no node is connected.
    fn drain_live_stream(&mut self, cx: &mut Context<Self>) {
        let Some(stream) = &self.live_stream else {
            return;
        };
        let records = stream.drain();
        if records.is_empty() {
            return;
        }
        let new = self.live_feed.ingest_records(records);
        if new > 0 {
            // The ReceiptInspector advances live — notify to re-render.
            cx.notify();
        }
    }

    /// Whether a LIVE NODE receipt stream is connected (so the post-paint pump in
    /// `main::run_window` should keep turning). `false` for the pure embedded image
    /// (no `--node`), which stops the pump immediately.
    pub fn has_live_stream(&self) -> bool {
        self.live_stream.is_some()
    }

    /// **The LIVE PUMP tick — drain the node's SSE stream off gpui's async
    /// executor.**
    ///
    /// `drain_live_stream` runs at the top of `render`, but gpui only re-renders on
    /// `cx.notify()` or input — so a receipt a remote node streams while the UI is
    /// idle would sit unconsumed in the reader's channel until the next input. This
    /// is the fix the recovered design calls for ("move the cockpit reads onto
    /// gpui's async executor"): a foreground task in `run_window` calls this on a
    /// short timer, so a connected node's receipts are drained — and the
    /// ReceiptInspector / live organ panels advance LIVE — with no user input. Each
    /// freshly-arrived receipt fires `cx.notify()` (inside `drain_live_stream`), so
    /// the next paint reflects it. Returns whether the pump should keep running (a
    /// stream is still connected). No-op (returns `false`) for the embedded-only image.
    pub fn pump_live(&mut self, cx: &mut Context<Self>) -> bool {
        if self.live_stream.is_none() {
            return false;
        }
        self.drain_live_stream(cx);
        true
    }
}

impl Render for Cockpit {
    fn render(&mut self, _window: &mut Window, cx: &mut Context<Self>) -> impl IntoElement {
        // LIVE: drain the node's receipt stream first so this frame reflects every
        // receipt that arrived (per-receipt `cx.notify()`, not a snapshot reload).
        self.drain_live_stream(cx);
        // M2 DELTA LOOP: fold this frame's dynamics into per-slice invalidation so
        // the projection memo reflects exactly the cells that changed (O(changed),
        // not O(ledger)) — the producer↔consumer JOIN (EFFICIENCY-WELD-PLAN §2.1).
        self.fold_dynamics();
        // M3 WIDEN: witness the active tab into the workspace cell. The scattered free
        // `self.tab = …` draft writes (the §3.5 stream weight class) catch up here with
        // an occasional `SetField` commit, so `render()` dispatches on the cell read
        // (`active_tab()`) — the §3.4 `render(workspace_subgraph)` selector is now
        // cell-driven, not a Rust field. Clean ⟹ no commit (idempotent).
        self.witness_tab();
        let palette_open = self.palette.is_open();
        div()
            .id("cockpit-root")
            .track_focus(&self.focus)
            .key_context("Cockpit")
            // ⌘K + the palette's typing/selection all flow through one handler.
            .on_key_down(cx.listener(|this, ev: &KeyDownEvent, _w, cx| {
                this.on_key(ev, cx);
            }))
            .relative()
            .flex()
            .size_full()
            .bg(theme::bg())
            .text_color(theme::text())
            .font_family("Menlo")
            // Left rail: image header + cell world + dynamics feed.
            .child(
                div()
                    .flex()
                    .flex_col()
                    .w(px(320.))
                    .h_full()
                    .border_r_1()
                    .border_color(theme::border())
                    .bg(theme::panel())
                    .child(self.rail_header())
                    .child(div().flex_1().child(self.cell_world(cx)))
                    .child(
                        div()
                            .border_t_1()
                            .border_color(theme::border())
                            .child(self.dynamics_feed()),
                    ),
            )
            // Center: inspector over blocklace.
            .child(
                div()
                    .flex()
                    .flex_col()
                    .w(px(460.))
                    .h_full()
                    .border_r_1()
                    .border_color(theme::border())
                    .child(div().flex_1().child(self.inspector()))
                    .child(
                        div()
                            .h(px(260.))
                            .border_t_1()
                            .border_color(theme::border())
                            .bg(theme::panel())
                            .child(self.blocklace(cx)),
                    ),
            )
            // Right: the workspace — tab bar over the active feature panel
            // (composer · debugger · replay · cipherclerk · editor).
            .child(
                div()
                    .flex()
                    .flex_col()
                    .flex_1()
                    .h_full()
                    .child(self.tab_bar(cx))
                    .child(div().flex_1().overflow_hidden().child(self.workspace(cx))),
            )
            // THE ⌘K COMMAND PALETTE overlay (absolute, on top) when open.
            .when(palette_open, |root| root.child(self.palette_overlay(cx)))
    }
}

// --- small render helpers ---------------------------------------------------

/// The sorted live cells, freshly collected from the ledger. Used ONLY to seed /
/// refresh `Cockpit.cells` (construction + `refresh_cells`); every render-hot read
/// site routes through that cached `self.cells` instead (the M1 re-sort weld), so
/// the full `HashMap` drain+sort runs once per mutating handler, not per frame.
fn sorted_cells(w: &World) -> Vec<CellId> {
    let mut ids: Vec<CellId> = w.ledger().iter().map(|(id, _)| *id).collect();
    ids.sort_by(|a, b| a.as_bytes().cmp(b.as_bytes()));
    ids
}

// ===========================================================================
// THE GENERIC PER-BODY RENDER HELPERS — one widget per `PresentationBody` variant.
// Pure (they read the body data the model already computed). The Fields + Prose
// variants are rendered inline by `render_presentation_body`; these cover the
// six structural visual kinds.
// ===========================================================================

/// Graph body — reuses the GRAPH tab's drawing vocabulary (nodes + directed
/// `holder ──rights──▶ target` edges), centered on the focused cell.
fn render_graph_body(g: &GraphView) -> impl IntoElement {
    let mut col = div().flex().flex_col().gap_0p5();
    col = col.child(div().text_xs().text_color(theme::muted()).child(format!(
        "{} node(s) · {} edge(s){}",
        g.nodes.len(),
        g.edges.len(),
        g.focus.map(|f| format!(" · focus ⬡ {}", reflect::short_hex(f.as_bytes()))).unwrap_or_default(),
    )));
    if g.edges.is_empty() {
        col = col.child(div().text_xs().text_color(theme::muted()).child("(no capability edges)"));
    }
    for e in g.edges.iter().take(24) {
        col = col.child(
            div()
                .flex()
                .justify_between()
                .px_2()
                .py_0p5()
                .child(div().text_xs().text_color(theme::text()).child(format!(
                    "⬡ {} ──▶ {}",
                    reflect::short_hex(e.holder.as_bytes()),
                    reflect::short_hex(e.target.as_bytes()),
                )))
                .child(div().text_xs().text_color(theme::accent()).child(format!("[{}]", e.rights_label()))),
        );
    }
    col
}

/// StateMachine body — states (terminal marked) + the current readout + the
/// directed verb transitions.
fn render_state_machine(sm: &StateMachineView) -> impl IntoElement {
    let mut col = div().flex().flex_col().gap_0p5();
    col = col.child(div().text_xs().text_color(theme::good()).child(format!("current: {}", sm.current)));
    let mut states_row = div().flex().flex_wrap().gap_1();
    for st in &sm.states {
        let active = st.name == sm.current;
        let color = if active {
            theme::accent()
        } else if st.terminal {
            theme::warn()
        } else {
            theme::muted()
        };
        states_row = states_row.child(pill(
            if st.terminal { format!("{} ⊣", st.name) } else { st.name.clone() },
            color,
        ));
    }
    col = col.child(states_row);
    col = col.child(div().text_xs().text_color(theme::muted()).mt_1().child("transitions"));
    for t in &sm.transitions {
        col = col.child(div().text_xs().text_color(theme::text()).child(format!(
            "{} ──{}──▶ {}",
            t.from, t.verb, t.to
        )));
    }
    col
}

/// Gauge body — a bounded value (drawn / ceiling) drawn as a simple bar, with the
/// named ratchet rungs.
fn render_gauge(g: &GaugeView) -> impl IntoElement {
    let frac: f32 = match g.ceiling {
        Some(c) if c > 0 => (g.value as f32 / c as f32).clamp(0.0, 1.0),
        _ => 0.0,
    };
    let mut col = div().flex().flex_col().gap_0p5();
    col = col.child(div().text_xs().text_color(theme::text()).child(format!(
        "{}: {}{}",
        g.label,
        g.value,
        g.ceiling.map(|c| format!(" / {c}")).unwrap_or_else(|| " (unbounded)".into()),
    )));
    if g.ceiling.is_some() {
        col = col.child(
            div()
                .w_full()
                .h(px(8.))
                .rounded_md()
                .bg(theme::panel_hi())
                .child(
                    div()
                        .h(px(8.))
                        .w(gpui::relative(frac))
                        .rounded_md()
                        .bg(if frac > 0.9 { theme::bad() } else { theme::accent() }),
                ),
        );
    }
    if !g.rungs.is_empty() {
        let mut rungs = div().flex().flex_wrap().gap_1();
        for r in &g.rungs {
            rungs = rungs.child(pill(r.clone(), theme::muted()));
        }
        col = col.child(rungs);
    }
    col
}

/// Timeline body — ordered events (a receipt chain / epoch history / lineage), each
/// with its monotone key + an optional navigable hash.
fn render_timeline(t: &TimelineView) -> impl IntoElement {
    let mut col = div().flex().flex_col().gap_0p5();
    if t.events.is_empty() {
        col = col.child(div().text_xs().text_color(theme::muted()).child("(no events yet)"));
    }
    for e in t.events.iter().take(32) {
        col = col.child(
            div()
                .flex()
                .gap_1()
                .child(div().text_xs().text_color(theme::muted()).min_w(px(28.)).child(format!("#{}", e.at)))
                .child(div().text_xs().text_color(theme::text()).child(e.label.clone()))
                .when(e.hash.is_some(), |d| {
                    d.child(pill(reflect::short_hex(&e.hash.unwrap()), theme::good()))
                }),
        );
    }
    col
}

/// MerkleTree body — leaves + the committed root + an optional highlighted path.
fn render_merkle(m: &MerkleTreeView) -> impl IntoElement {
    let mut col = div().flex().flex_col().gap_0p5();
    col = col.child(div().text_xs().text_color(theme::text()).child(format!("{} · {} leaf/leaves", m.label, m.leaves.len())));
    col = col.child(
        div()
            .flex()
            .gap_1()
            .child(div().text_xs().text_color(theme::muted()).child("root:"))
            .child(pill(reflect::short_hex(&m.root), theme::accent())),
    );
    for (i, leaf) in m.leaves.iter().take(24).enumerate() {
        let on_path = m.path.contains(leaf);
        col = col.child(div().text_xs().text_color(if on_path { theme::good() } else { theme::muted() }).child(format!(
            "{} leaf[{i}] {}",
            if on_path { "▣" } else { "·" },
            leaf
        )));
    }
    col
}

/// Lattice body — a partial order (rights tiers / finality levels), with the live
/// current element + the covering relations.
fn render_lattice(l: &LatticeView) -> impl IntoElement {
    let mut col = div().flex().flex_col().gap_0p5();
    let mut nodes_row = div().flex().flex_wrap().gap_1();
    for (i, n) in l.nodes.iter().enumerate() {
        let active = l.current == Some(i);
        nodes_row = nodes_row.child(pill(
            if active { format!("● {n}") } else { n.clone() },
            if active { theme::accent() } else { theme::muted() },
        ));
    }
    col = col.child(nodes_row);
    col = col.child(div().text_xs().text_color(theme::muted()).mt_1().child("⊑ covering relations"));
    for (a, b) in &l.edges {
        if let (Some(na), Some(nb)) = (l.nodes.get(*a), l.nodes.get(*b)) {
            col = col.child(div().text_xs().text_color(theme::text()).child(format!("{na} ⊑ {nb}")));
        }
    }
    col
}

/// Trace body — step-by-step evaluation (an HMAC chain / constraint eval / absorb),
/// numbered in evaluation order.
fn render_trace(t: &TraceView) -> impl IntoElement {
    let mut col = div().flex().flex_col().gap_0p5();
    if t.steps.is_empty() {
        col = col.child(div().text_xs().text_color(theme::muted()).child("(no steps)"));
    }
    for s in t.steps.iter().take(32) {
        col = col.child(
            div()
                .flex()
                .gap_1()
                .child(div().text_xs().text_color(theme::muted()).min_w(px(24.)).child(format!("{}.", s.index)))
                .child(div().text_xs().text_color(theme::text()).child(s.label.clone())),
        );
    }
    col
}

/// A human reason for a refused shell op (the window-manager ocap guarantee
/// firing). Surfaced in the outcome banner the same way the executor's
/// rejections are — a refusal is a feature, not an error to hide.
fn shell_err(e: &starbridge_v2::shell::ShellError) -> String {
    use starbridge_v2::shell::ShellError;
    match e {
        ShellError::Unauthorized => "no valid capability presented (no ambient authority)".to_string(),
        ShellError::NoSuchSurface(id) => format!("surface {} does not exist", id.as_u64()),
        ShellError::ConsoleProtected => "the system console is the trusted root (cannot close)".to_string(),
        ShellError::ShareDenied(why) => format!("widening share refused by the executor: {why}"),
        // The verified-scene tooth that bit (T1 overpaint / T2 spoof / T3
        // misroute|double-focus), surfaced for the operator log.
        ShellError::PresentRefused(p) => p.explain(),
    }
}

fn kind_badge(kind: ObjectKind) -> impl IntoElement {
    let (label, color) = match kind {
        ObjectKind::Cell => ("cell", theme::accent()),
        ObjectKind::Receipt => ("receipt", theme::good()),
        ObjectKind::Capability => ("capability", theme::accent()),
        ObjectKind::Image => ("image", theme::warn()),
        ObjectKind::Proof => ("proof", theme::good()),
        ObjectKind::Factory => ("factory", theme::accent()),
        ObjectKind::Nullifier => ("nullifier", theme::warn()),
        ObjectKind::Document => ("document", theme::accent()),
    };
    div().mb_2().child(pill(label, color))
}

/// A short label + color for a cell's lifecycle state (the OBJECTS panel's
/// lifecycle column). Matches the protocol's `CellLifecycle` variants.
fn lifecycle_badge(lc: &dregg_cell::lifecycle::CellLifecycle) -> (&'static str, Hsla) {
    use dregg_cell::lifecycle::CellLifecycle;
    match lc {
        CellLifecycle::Live => ("live", theme::good()),
        CellLifecycle::Sealed { .. } => ("sealed", theme::warn()),
        CellLifecycle::Destroyed { .. } => ("destroyed", theme::bad()),
        CellLifecycle::Migrated { .. } => ("migrated", theme::muted()),
        CellLifecycle::Archived { .. } => ("archived", theme::accent()),
    }
}

/// A compact row for a reflected object (the cipherclerk panel's identity /
/// token / delegation entries), showing its title, kind badge, and fields.
fn inspectable_row(ins: &Inspectable) -> impl IntoElement {
    let mut col = div()
        .flex()
        .flex_col()
        .gap_0p5()
        .px_2()
        .py_1()
        .rounded_md()
        .bg(theme::panel())
        .child(
            div()
                .flex()
                .justify_between()
                .child(div().text_xs().text_color(theme::text()).child(ins.title.clone()))
                .child(kind_badge(ins.kind)),
        )
        .child(div().text_xs().text_color(theme::muted()).child(ins.subtitle.clone()));
    for f in &ins.fields {
        col = col.child(field_row(f));
    }
    col
}

fn field_row(f: &Field) -> impl IntoElement {
    let (val, color): (String, Hsla) = match &f.value {
        FieldValue::Text(s) => (s.clone(), theme::text()),
        FieldValue::Balance(b) => (
            b.to_string(),
            if *b < 0 { theme::warn() } else { theme::text() },
        ),
        FieldValue::Count(c) => (c.to_string(), theme::text()),
        FieldValue::Bool(b) => (
            b.to_string(),
            if *b { theme::good() } else { theme::muted() },
        ),
        FieldValue::Id(id) => (reflect::short_hex(id), theme::accent()),
        FieldValue::Hash(h) => (reflect::short_hex(h), theme::good()),
        FieldValue::CapEdge { target, slot } => {
            (format!("→ {} (slot {slot})", reflect::short_hex(target)), theme::accent())
        }
        FieldValue::FieldSlot { hex, .. } => (reflect::short_hex_hexstr(hex), theme::muted()),
    };
    div()
        .flex()
        .justify_between()
        .py_0p5()
        .child(div().text_xs().text_color(theme::muted()).child(f.key.clone()))
        .child(div().text_xs().text_color(color).child(val))
}

/// A verb button that runs a `&mut Cockpit` method through the listener.
fn verb_button(
    cx: &mut Context<Cockpit>,
    label: &str,
    color: Hsla,
    handler: fn(&mut Cockpit, &mut Context<Cockpit>),
) -> impl IntoElement {
    let id = SharedString::from(format!("verb-{label}"));
    div()
        .id(id)
        .px_3()
        .py_2()
        .rounded_md()
        .bg(theme::panel_hi())
        .border_1()
        .border_color(theme::border())
        .text_color(color)
        .cursor_pointer()
        .hover(|s| s.bg(theme::border()))
        .on_mouse_down(
            MouseButton::Left,
            cx.listener(move |this, _ev, _window, cx| {
                handler(this, cx);
            }),
        )
        .child(label.to_string())
}

/// A compact cipherclerk action button (smaller than a composer verb; the
/// clerk panel has four in a wrap row).
fn clerk_button(
    cx: &mut Context<Cockpit>,
    label: &str,
    color: Hsla,
    handler: fn(&mut Cockpit, &mut Context<Cockpit>),
) -> impl IntoElement {
    let id = SharedString::from(format!("clerk-{label}"));
    div()
        .id(id)
        .px_2()
        .py_1()
        .rounded_md()
        .bg(theme::panel_hi())
        .border_1()
        .border_color(theme::border())
        .text_xs()
        .text_color(color)
        .cursor_pointer()
        .hover(|s| s.bg(theme::border()))
        .on_mouse_down(
            MouseButton::Left,
            cx.listener(move |this, _ev, _window, cx| {
                handler(this, cx);
            }),
        )
        .child(label.to_string())
}

/// A compact action button with an EXPLICIT element id (so two buttons that share
/// a label don't collide) — the SIMULATE panel's build/run/commit verbs.
fn small_button(
    cx: &mut Context<Cockpit>,
    id: &'static str,
    label: &str,
    color: Hsla,
    handler: fn(&mut Cockpit, &mut Context<Cockpit>),
) -> impl IntoElement {
    div()
        .id(id)
        .px_2()
        .py_1()
        .rounded_md()
        .bg(theme::panel_hi())
        .border_1()
        .border_color(theme::border())
        .text_xs()
        .text_color(color)
        .cursor_pointer()
        .hover(|s| s.bg(theme::border()))
        .on_mouse_down(
            MouseButton::Left,
            cx.listener(move |this, _ev, _window, cx| {
                handler(this, cx);
            }),
        )
        .child(label.to_string())
}

/// A clickable "cycle" chip — a small pill that runs `handler` on click (the
/// SIMULATE panel's agent/target/effect pickers cycle their selection).
fn cycle_chip(
    cx: &mut Context<Cockpit>,
    id: &'static str,
    label: String,
    color: Hsla,
    handler: fn(&mut Cockpit, &mut Context<Cockpit>),
) -> impl IntoElement {
    div()
        .id(id)
        .px_2()
        .py_0p5()
        .rounded_md()
        .bg(theme::panel_hi())
        .border_1()
        .border_color(theme::border())
        .text_xs()
        .text_color(color)
        .cursor_pointer()
        .hover(|s| s.bg(theme::border()))
        .on_mouse_down(
            MouseButton::Left,
            cx.listener(move |this, _ev, _window, cx| {
                handler(this, cx);
            }),
        )
        .child(label)
}

/// Map a landing-portal [`Tone`](starbridge_v2::landing::Tone) (a semantic role,
/// kept gpui-free in the model) onto a theme color for the HOME render.
fn portal_tone_color(tone: starbridge_v2::landing::Tone) -> Hsla {
    use starbridge_v2::landing::Tone;
    match tone {
        Tone::Body => theme::text(),
        Tone::Muted => theme::muted(),
        Tone::Good => theme::good(),
        Tone::Accent => theme::accent(),
        Tone::Heading => theme::text(),
    }
}

/// A short label + color for a palette command's category badge.
fn category_badge(cat: Category) -> (&'static str, Hsla) {
    match cat {
        Category::Verb => (cat.label(), theme::good()),
        Category::Navigate => (cat.label(), theme::accent()),
        Category::Replay => (cat.label(), theme::warn()),
        Category::Clerk => (cat.label(), theme::accent()),
        Category::Shell => (cat.label(), theme::accent()),
        Category::Ide => (cat.label(), theme::good()),
        Category::Debug => (cat.label(), theme::warn()),
        Category::Inspect => (cat.label(), theme::muted()),
        Category::Palette => (cat.label(), theme::muted()),
    }
}

/// A short label + color for a surface's SHELL-DRAWN trusted-path lifecycle
/// badge (the anti-spoof identity chrome). Mirrors the shell's lifecycle strings.
fn identity_badge(lifecycle: &str) -> (&'static str, Hsla) {
    match lifecycle {
        "live" => ("live", theme::good()),
        "sealed" => ("sealed", theme::warn()),
        "destroyed" => ("destroyed", theme::bad()),
        "migrated" => ("migrated", theme::muted()),
        "archived" => ("archived", theme::accent()),
        "system" => ("system", theme::warn()),
        _ => ("missing", theme::bad()),
    }
}

/// A compact shell-toolbar button (the cap-first compositor's window ops). Same
/// shape as a clerk button; runs a `&mut Cockpit` method through the listener.
fn shell_button(
    cx: &mut Context<Cockpit>,
    label: &str,
    color: Hsla,
    handler: fn(&mut Cockpit, &mut Context<Cockpit>),
) -> impl IntoElement {
    let id = SharedString::from(format!("shell-{label}"));
    div()
        .id(id)
        .px_2()
        .py_1()
        .rounded_md()
        .bg(theme::panel_hi())
        .border_1()
        .border_color(theme::border())
        .text_xs()
        .text_color(color)
        .cursor_pointer()
        .hover(|s| s.bg(theme::border()))
        .on_mouse_down(
            MouseButton::Left,
            cx.listener(move |this, _ev, _window, cx| {
                handler(this, cx);
            }),
        )
        .child(label.to_string())
}

/// Convert a servo-render [`servo_render::RgbaFrame`] (RGBA8, row-major) into a
/// gpui [`gpui::RenderImage`] the cockpit paints with `img()`. gpui's
/// `RenderImage` holds **BGRA** frames (see `gpui::Image::to_image_data`, which
/// swaps R↔B after decode), so we swap the red/blue channels of the SWGL frame's
/// bytes the same way before wrapping them in an `image::Frame`. This is the SAME
/// raw-bytes -> `RenderImage::new(vec![Frame::new(buf)])` path the upstream
/// `repl::outputs::ImageView` uses — no parallel renderer, no re-fetch: just the
/// already-rendered cap-gated pixels handed to gpui.
#[cfg(feature = "servo")]
fn rgba_frame_to_image(frame: &servo_render::RgbaFrame) -> std::sync::Arc<gpui::RenderImage> {
    // Copy the RGBA8 bytes and swap R<->B in place to land in gpui's BGRA layout.
    let mut bgra = frame.bytes.clone();
    for px in bgra.chunks_exact_mut(4) {
        px.swap(0, 2);
    }
    let buffer = image::RgbaImage::from_raw(frame.width, frame.height, bgra)
        .expect("RgbaFrame carries width*height*4 RGBA8 bytes");
    std::sync::Arc::new(gpui::RenderImage::new(vec![image::Frame::new(buffer)]))
}

// ===========================================================================
// ⏳ THE TEMPORAL COCKPIT — the headline livability surface (the "⏳ TIME" tab):
// time-travel + suspend + fractal meta-debug as ONE clickable control panel.
//
// This block holds the TIME tab's verbs (the rewind scrubber, the M5 suspend
// gate, the MetaStack navigator) + its render, all over the REAL models
// (`time_travel::TimeCockpitModel` over `World::recorded_turns` / the suspend gate /
// `meta_debug::MetaStack`). Appended as its own `impl Cockpit` so it stays out of
// the way of the densely-co-edited Tab/dispatch/state regions above.
// ===========================================================================
impl Cockpit {
    /// The head step of the live history (the live present — where `Liveness::Live`).
    fn time_head(&self) -> usize {
        self.world.borrow().recorded_turns().len()
    }

    /// Drag the REWIND SCRUBBER to history step `k` (clamped to the head). The TIME
    /// tab re-derives the focused views at that point (root-verified replay); the
    /// image rewinds, the `Liveness` badge flips to `ReplayedDeterministic`.
    fn time_scrub_to(&mut self, k: usize, cx: &mut Context<Self>) {
        self.time_cursor = k.min(self.time_head());
        cx.notify();
    }

    /// Rewind the scrubber one turn (one history step back).
    fn time_step_back(&mut self, cx: &mut Context<Self>) {
        self.time_cursor = self.time_cursor.saturating_sub(1);
        cx.notify();
    }

    /// Advance the scrubber one turn (toward the live head).
    fn time_step_forward(&mut self, cx: &mut Context<Self>) {
        self.time_cursor = (self.time_cursor + 1).min(self.time_head());
        cx.notify();
    }

    /// Jump the scrubber to genesis (the empty pre-history image).
    fn time_to_genesis(&mut self, cx: &mut Context<Self>) {
        self.time_cursor = 0;
        cx.notify();
    }

    /// Jump the scrubber back to the live head (the present — `Liveness::Live`).
    fn time_to_head(&mut self, cx: &mut Context<Self>) {
        self.time_cursor = self.time_head();
        cx.notify();
    }

    /// ⏸ SUSPEND — halt the live loop via the M5 gate ([`World::suspend`]). The head
    /// FREEZES; a turn submitted while suspended STAGES in the pending queue (the
    /// continuation) instead of committing. Distinct from the scrubber being in the
    /// past: this stops the REAL loop.
    fn time_suspend(&mut self, cx: &mut Context<Self>) {
        self.world.borrow_mut().suspend();
        cx.notify();
    }

    /// ▶ RESUME (drain) — drain the staged continuation through the executor gate
    /// ([`ResumeMode::Drain`]): the queued turns commit in arrival order and the
    /// loop runs again. The scrubber follows the head forward; the tower grounds.
    fn time_resume(&mut self, cx: &mut Context<Self>) {
        let outcomes = self.world.borrow_mut().resume(ResumeMode::Drain);
        let committed = outcomes.iter().filter(|o| o.is_committed()).count();
        self.time_cursor = self.time_head();
        self.last_outcome = Some(format!(
            "▶ resumed · {committed} staged turn(s) drained through the gate"
        ));
        self.meta_stack = MetaStack::new();
        cx.notify();
    }

    /// STAGE a demo continuation turn while suspended — a small transfer the operator
    /// can watch QUEUE (it does not commit; the head stays frozen). Proves the
    /// suspend gate live: the pending queue grows, the image is untouched.
    fn time_stage_demo_turn(&mut self, cx: &mut Context<Self>) {
        let [treasury, _service, user] = self.anchors;
        let turn = {
            let w = self.world.borrow();
            w.turn(treasury, vec![world::transfer(treasury, user, 1)])
        };
        let outcome = self.world.borrow_mut().commit_turn(turn);
        self.last_outcome = Some(match outcome {
            CommitOutcome::Queued { .. } => {
                "⏸ staged · a turn QUEUED into the frozen continuation".to_string()
            }
            CommitOutcome::Committed { receipt, .. } => {
                self.time_cursor = self.time_head();
                format!(
                    "committed (not suspended) · {}",
                    reflect::short_hex(&receipt.receipt_hash())
                )
            }
            CommitOutcome::Rejected { reason, .. } => format!("refused · {reason}"),
        });
        cx.notify();
    }

    /// SUSPEND & INSPECT — push a meta-level onto the [`MetaStack`] (the fractal
    /// meta-debug). The first push suspends the loop (if not already) + materializes
    /// `BASE`; each subsequent push climbs one level — "debug the debugger". The new
    /// level captures the frozen head as an inspectable object.
    fn time_metastack_push(&mut self, cx: &mut Context<Self>) {
        {
            let mut w = self.world.borrow_mut();
            if !w.is_suspended() {
                w.suspend();
            }
        }
        let focus = {
            let w = self.world.borrow();
            self.meta_stack.push(&w)
        };
        self.last_outcome = Some(format!(
            "⊕ pushed meta-level · debugging {focus:?} (the tower climbed)"
        ));
        cx.notify();
    }

    /// DESCEND — pop the innermost meta-level (close the inner debugger). The floor
    /// (the gpui loop) stops the pop: you cannot descend below the base.
    fn time_metastack_pop(&mut self, cx: &mut Context<Self>) {
        match self.meta_stack.pop() {
            Some(view) => {
                self.last_outcome =
                    Some(format!("⊖ popped meta-level {} (descended)", view.level.depth()));
            }
            None => {
                self.last_outcome =
                    Some("(at the floor — the gpui loop is not a level to pop)".to_string());
            }
        }
        cx.notify();
    }

    /// THE ⏳ TIME PANEL — the temporal cockpit, painted from the pure
    /// [`TimeCockpitModel`] (built fresh from the live world + the scrubber cursor +
    /// the MetaStack). Three clickable powers stacked: (1) the REWIND SCRUBBER with
    /// the live `Liveness` badge + the verified reconstruction at the cursor; (2) the
    /// ⏸ SUSPEND / ▶ RESUME gate + the staged continuation; (3) the METASTACK
    /// breadcrumb navigator (push to climb / pop to descend — debug the debugger).
    fn time_panel(&self, cx: &mut Context<Self>) -> impl IntoElement {
        let model = {
            let w = self.world.borrow();
            TimeCockpitModel::build(&w, self.time_cursor, &self.meta_stack)
        };

        let mut col = div().flex().flex_col().gap_2().p_3().size_full().overflow_hidden();
        col = col.child(section_title(
            "⏳ TEMPORAL COCKPIT · time-travel · suspend · fractal meta-debug",
        ));

        // --- the LIVENESS badge — am I at the live present, or a re-derived past? --
        let (badge_color, badge_bg) = match model.liveness {
            Liveness::Live => (theme::good(), theme::panel()),
            Liveness::ReplayedDeterministic => (theme::warn(), theme::panel_hi()),
            Liveness::ReconstructedApproximate => (theme::bad(), theme::panel_hi()),
        };
        col = col.child(
            div()
                .flex()
                .items_center()
                .gap_2()
                .p_2()
                .rounded_md()
                .border_1()
                .border_color(badge_color)
                .bg(badge_bg)
                .child(div().text_sm().text_color(badge_color).child(model.liveness_badge()))
                .child(
                    div()
                        .text_xs()
                        .text_color(theme::muted())
                        .child(format!("k{} / head k{}", model.cursor, model.head)),
                )
                .child(if model.cursor_verified {
                    pill(format!("✓ root {}", short_root(&model.cursor_root)), theme::good())
                } else {
                    pill("✗ root UNVERIFIED".to_string(), theme::bad())
                }),
        );

        // ====================================================================
        // (2) THE ⏸ SUSPEND GATE — halt the real loop; the staged continuation.
        // ====================================================================
        col = col.child(section_title("⏸ SUSPEND GATE · halt the live loop (M5)").mt_1());
        if model.suspended {
            // SUSPENDED banner — the head is FROZEN.
            col = col.child(
                div()
                    .flex()
                    .items_center()
                    .gap_2()
                    .p_2()
                    .rounded_md()
                    .border_1()
                    .border_color(theme::warn())
                    .bg(theme::panel_hi())
                    .child(div().text_sm().text_color(theme::warn()).child("⏸ SUSPENDED"))
                    .child(
                        div()
                            .text_xs()
                            .text_color(theme::muted())
                            .child(format!("head FROZEN @h{} · the loop is halted", model.live_height)),
                    ),
            );
            col = col.child(
                div()
                    .flex()
                    .flex_wrap()
                    .gap_1()
                    .child(time_button(cx, "time-resume", "▶ RESUME (drain)", theme::good(), Cockpit::time_resume))
                    .child(time_button(cx, "time-stage", "⊕ stage a turn", theme::accent(), Cockpit::time_stage_demo_turn)),
            );
            // The staged continuation (the pending queue) — the real partial turn.
            col = col.child(
                div()
                    .text_xs()
                    .text_color(theme::muted())
                    .mt_1()
                    .child(format!("STAGED CONTINUATION · {} pending turn(s)", model.pending.len())),
            );
            if model.pending.is_empty() {
                col = col.child(
                    div()
                        .text_xs()
                        .text_color(theme::muted())
                        .px_2()
                        .child("(empty — stage a turn to fill the continuation)"),
                );
            }
            for line in &model.pending {
                col = col.child(div().text_xs().text_color(theme::accent()).px_2().child(format!("· {line}")));
            }
        } else {
            // RUNNING — the loop is live; offer the suspend button.
            col = col.child(
                div()
                    .flex()
                    .items_center()
                    .gap_2()
                    .child(div().text_xs().text_color(theme::good()).child(format!("● running @h{}", model.live_height)))
                    .child(time_button(cx, "time-suspend", "⏸ SUSPEND", theme::warn(), Cockpit::time_suspend)),
            );
        }

        // ====================================================================
        // (1) THE REWIND SCRUBBER — drag over the verified witness history.
        // ====================================================================
        col = col.child(section_title("⟲ REWIND SCRUBBER · the verified witness history").mt_2());
        col = col.child(
            div()
                .flex()
                .flex_wrap()
                .gap_1()
                .child(time_button(cx, "time-genesis", "⏮ genesis", theme::muted(), Cockpit::time_to_genesis))
                .child(time_button(cx, "time-back", "◀ −1 turn", theme::accent(), Cockpit::time_step_back))
                .child(time_button(cx, "time-fwd", "+1 turn ▶", theme::accent(), Cockpit::time_step_forward))
                .child(time_button(cx, "time-head", "live head ⏭", theme::good(), Cockpit::time_to_head)),
        );
        // The ticks — every landing (genesis → head). Each is CLICKABLE: drag the
        // scrubber to that step. The cursor tick glows; turns vs genesis are distinct.
        let mut ticks = div().flex().flex_col().gap_0p5().mt_1();
        for tick in &model.ticks {
            let at_cursor = tick.step == model.cursor;
            let is_head = tick.step == model.head;
            let step = tick.step;
            let marker = if at_cursor { "▸" } else if tick.is_turn { "•" } else { "·" };
            let label_color = if at_cursor {
                theme::accent()
            } else if tick.is_turn {
                theme::text()
            } else {
                theme::muted()
            };
            ticks = ticks.child(
                div()
                    .id(SharedString::from(format!("time-tick-{step}")))
                    .flex()
                    .justify_between()
                    .items_center()
                    .px_2()
                    .py_0p5()
                    .rounded_md()
                    .bg(if at_cursor { theme::panel_hi() } else { theme::panel() })
                    .cursor_pointer()
                    .hover(|s| s.bg(theme::border()))
                    .on_mouse_down(
                        MouseButton::Left,
                        cx.listener(move |this, _ev, _w, cx| {
                            this.time_scrub_to(step, cx);
                        }),
                    )
                    .child(
                        div()
                            .text_xs()
                            .text_color(label_color)
                            .child(format!("{marker} k{step}  {}{}", tick.label, if is_head { "  ⟵ head (live)" } else { "" })),
                    )
                    .child(div().text_xs().text_color(theme::muted()).child(short_root(&tick.root))),
            );
        }
        col = col.child(ticks);

        // The VERIFIED reconstruction at the cursor — the image, rewound. Re-derived
        // by root-verified replay (`time_travel` → `History::replay_to`).
        col = col.child(
            div()
                .text_xs()
                .text_color(theme::muted())
                .mt_1()
                .child(format!("IMAGE @k{} ({} cells, verified replay)", model.cursor, model.cursor_cells.len())),
        );
        if model.cursor_cells.is_empty() && !model.cursor_verified {
            col = col.child(
                div()
                    .text_xs()
                    .text_color(theme::bad())
                    .px_2()
                    .child("(replay refused — the witnessed log does not support this point)"),
            );
        }
        for (id, bal, caps) in &model.cursor_cells {
            col = col.child(
                div()
                    .flex()
                    .justify_between()
                    .px_2()
                    .child(div().text_xs().text_color(theme::text()).child(format!("⬡ {}", reflect::short_hex(id.as_bytes()))))
                    .child(
                        div()
                            .text_xs()
                            .text_color(if *bal < 0 { theme::warn() } else { theme::text() })
                            .child(format!("{bal} · {caps} caps")),
                    ),
            );
        }
        // The diff from the previous step — what the cursor's turn DID (the receipt).
        if let Some(diff) = &model.diff_from_prev {
            col = col.child(
                div()
                    .text_xs()
                    .text_color(theme::muted())
                    .mt_1()
                    .child(format!("Δ this turn (k{}→k{}) · {} cell(s) changed", model.cursor.saturating_sub(1), model.cursor, diff.len())),
            );
            for (id, change) in &diff.changes {
                col = col.child(
                    div()
                        .text_xs()
                        .text_color(theme::accent())
                        .px_2()
                        .child(format!("{} {}", reflect::short_hex(id.as_bytes()), change.label())),
                );
            }
        }

        // ====================================================================
        // (3) THE METASTACK NAVIGATOR — the fractal meta-debug tower.
        // ====================================================================
        col = col.child(section_title("⊞ METASTACK · debug the debugger (the reflective tower)").mt_2());
        col = col.child(
            div()
                .flex()
                .flex_wrap()
                .gap_1()
                .child(time_button(cx, "meta-push", "⊕ suspend & inspect (climb)", theme::accent(), Cockpit::time_metastack_push))
                .child(time_button(cx, "meta-pop", "⊖ descend (pop)", theme::muted(), Cockpit::time_metastack_pop)),
        );
        // The breadcrumb: BASE → meta¹ → meta² … (the top is the current debugger).
        let mut crumbs = div().flex().flex_wrap().items_center().gap_1().mt_1();
        crumbs = crumbs.child(div().text_xs().text_color(theme::muted()).child("BASE (the live image)"));
        if model.metastack.is_empty() {
            crumbs = crumbs.child(
                div()
                    .text_xs()
                    .text_color(theme::muted())
                    .child("— un-reflected (push to suspend & climb)"),
            );
        }
        for crumb in &model.metastack {
            let color = if crumb.is_top { theme::accent() } else { theme::text() };
            crumbs = crumbs.child(div().text_xs().text_color(theme::muted()).child("→"));
            crumbs = crumbs.child(
                div()
                    .px_2()
                    .py_0p5()
                    .rounded_md()
                    .bg(if crumb.is_top { theme::panel_hi() } else { theme::panel() })
                    .border_1()
                    .border_color(if crumb.is_top { theme::accent() } else { theme::border() })
                    .text_xs()
                    .text_color(color)
                    .child(format!(
                        "meta{} · frozen@h{}{}",
                        crumb.level,
                        crumb.frozen_height,
                        if crumb.is_top { " ◀ debugging" } else { "" }
                    )),
            );
        }
        col = col.child(crumbs);

        // The action banner (the last suspend/resume/stage/meta verdict).
        if let Some(msg) = &self.last_outcome {
            col = col.child(
                div()
                    .mt_2()
                    .p_2()
                    .rounded_md()
                    .bg(theme::panel())
                    .text_xs()
                    .text_color(theme::muted())
                    .child(msg.clone()),
            );
        }

        col
    }
}

/// A ⏳ TIME-tab action button — an explicit-id clickable verb (so two buttons
/// that share a label don't collide), driving a `&mut Cockpit` verb. Mirrors
/// `small_button`, kept local to the temporal cockpit block.
fn time_button(
    cx: &mut Context<Cockpit>,
    id: &'static str,
    label: &str,
    color: Hsla,
    handler: fn(&mut Cockpit, &mut Context<Cockpit>),
) -> impl IntoElement {
    div()
        .id(id)
        .px_2()
        .py_1()
        .rounded_md()
        .bg(theme::panel_hi())
        .border_1()
        .border_color(theme::border())
        .text_xs()
        .text_color(color)
        .cursor_pointer()
        .hover(|s| s.bg(theme::border()))
        .on_mouse_down(
            MouseButton::Left,
            cx.listener(move |this, _ev, _window, cx| {
                handler(this, cx);
            }),
        )
        .child(label.to_string())
}

/// First 6 bytes of a 32-byte canonical root, hex — the scrubber-tick root tooth.
fn short_root(root: &[u8; 32]) -> String {
    reflect::short_hex(root)
}

// ══════════════════════════════════════════════════════════════════════════
// THE 📄 DOCS EDITOR — the dreggverse document language as a cockpit surface.
// Each edit/resolve is a real cap-gated TURN through the genuine executor
// (riding `dregg_doc::ExecutorDrivenDoc`); a CONFLICT is a first-class STATE
// (both alternatives rendered, each tagged with who wrote it); transclusion +
// backlinks reuse the built Nelson pieces. See `starbridge_v2::doc_editor`.
// (A SEPARATE impl block at EOF so it never clobbers a peer's mid-file edits.)
// ══════════════════════════════════════════════════════════════════════════
impl Cockpit {
    // ── the edit verbs (each an edit = a real cap-gated turn) ─────────────────

    /// Append text to the document as ALICE — a real cap-gated turn leaving a
    /// receipt. The banner shows the executor verdict.
    fn doc_append_alice(&mut self, _cx: &mut Context<Cockpit>) {
        let out = self.doc_editor.append(
            "And every edit is a witnessed turn. ",
            starbridge_v2::doc_editor::DocAuthor::ALICE,
        );
        self.doc_outcome = Some(out.banner());
    }

    /// Attempt the same append on the UNAUTHORIZED editor (no region cap) — the
    /// executor's cross-cell cap gate REFUSES it IN-BAND (`CapabilityNotHeld`); the
    /// document is untouched. The refusal is the feature (the anti-ghost tooth).
    fn doc_attempt_unauthorized(&mut self, _cx: &mut Context<Cockpit>) {
        let out = self.doc_editor.attempt_unauthorized(
            "a forbidden region edit ",
            starbridge_v2::doc_editor::DocAuthor::BOB,
        );
        self.doc_outcome = Some(out.banner());
    }

    /// Sow a first-class PROSE conflict: two co-authors append a different
    /// continuation after the same tail atom (both real turns). The document now
    /// LIVES IN a conflict state.
    fn doc_sow_prose_conflict(&mut self, _cx: &mut Context<Cockpit>) {
        let (a, b) = self
            .doc_editor
            .sow_prose_conflict("Cats are the best. ", "Dogs are the best. ");
        self.doc_outcome = Some(format!(
            "sowed a prose conflict · alice: {} · bob: {}",
            if a.committed() { "✓" } else { "✗" },
            if b.committed() { "✓" } else { "✗" },
        ));
    }

    /// Sow a first-class FIELD conflict (the conservation/authority regime): two
    /// co-authors set a different `title` — both survive as a clash a resolution
    /// must CHOOSE (it may need consensus).
    fn doc_sow_field_conflict(&mut self, _cx: &mut Context<Cockpit>) {
        let (a, b) = self.doc_editor.sow_field_conflict("title", "On Cats", "On Dogs");
        self.doc_outcome = Some(format!(
            "sowed a field conflict (title) · alice: {} · bob: {}",
            if a.committed() { "✓" } else { "✗" },
            if b.committed() { "✓" } else { "✗" },
        ));
    }

    /// RESOLVE the first prose conflict by KEEPING its first alternative (drop the
    /// rest) — a real cap-gated resolving turn that collapses the antichain.
    fn doc_resolve_prose_keep(&mut self, _cx: &mut Context<Cockpit>) {
        let prose: Vec<_> = self
            .doc_editor
            .conflicts()
            .into_iter()
            .filter(|c| c.regime == dregg_doc::Regime::Prose)
            .collect();
        if let Some(c) = prose.first() {
            let heads: Vec<dregg_doc::AtomId> = c.alternatives.iter().map(|a| a.head).collect();
            if let Some((keep, drop)) = heads.split_first() {
                let out = self.doc_editor.resolve_prose_keep(
                    *keep,
                    drop,
                    starbridge_v2::doc_editor::DocAuthor::ALICE,
                );
                self.doc_outcome = Some(format!("resolve (keep alice's): {}", out.banner()));
            }
        } else {
            self.doc_outcome = Some("no prose conflict to resolve".into());
        }
    }

    /// RESOLVE the first prose conflict by ORDERING its alternatives (both kept) —
    /// a real cap-gated resolving `Connect` turn.
    fn doc_resolve_prose_order(&mut self, _cx: &mut Context<Cockpit>) {
        let prose: Vec<_> = self
            .doc_editor
            .conflicts()
            .into_iter()
            .filter(|c| c.regime == dregg_doc::Regime::Prose)
            .collect();
        if let Some(c) = prose.first() {
            let heads: Vec<dregg_doc::AtomId> = c.alternatives.iter().map(|a| a.head).collect();
            let out = self
                .doc_editor
                .resolve_prose_order(&heads, starbridge_v2::doc_editor::DocAuthor::ALICE);
            self.doc_outcome = Some(format!("resolve (order both): {}", out.banner()));
        } else {
            self.doc_outcome = Some("no prose conflict to resolve".into());
        }
    }

    /// RESOLVE the title FIELD conflict by CHOOSING alice's value — a real
    /// superseding `SetField` turn (the settling authority recorded).
    fn doc_resolve_field(&mut self, _cx: &mut Context<Cockpit>) {
        let out = self.doc_editor.resolve_field_choose(
            "title",
            "On Cats",
            starbridge_v2::doc_editor::DocAuthor::ALICE,
        );
        self.doc_outcome = Some(format!("settle title = 'On Cats': {}", out.banner()));
    }

    /// THE 📄 DOCS PANEL — the document editor surface: the linearized content,
    /// conflicts-as-states inline (both alternatives + provenance), one-click
    /// resolve, and the transclusion/backlinks hypermedia faces.
    fn docs_panel(&self, cx: &mut Context<Self>) -> gpui::AnyElement {
        let rendered = self.doc_editor.rendered();
        let conflicts = self.doc_editor.conflicts();
        let region = self.doc_editor.region_id();
        let editor = self.doc_editor.editor_id();
        let commitment = self.doc_editor.commitment();
        let seam_ok = self.doc_editor.commitment_matches();

        // The hypermedia faces, reusing the built `web_cells`/`links_here` pieces.
        let viewer = self.anchors[2]; // the cockpit `user` principal
        let (transclusion, backlinks) = {
            let w = self.world.borrow();
            let t = self
                .doc_editor
                .transclusion(&w, viewer, dregg_cell::AuthRequired::None);
            let b = self
                .doc_editor
                .backlinks(&w, region, dregg_cell::AuthRequired::None, 1);
            (t, b)
        };

        let mut col = div()
            .flex()
            .flex_col()
            .gap_1()
            .p_3()
            .size_full()
            .overflow_hidden();
        col = col.child(
            section_title("📄 DOCS · the dreggverse document language · a patch IS a turn").mb_1(),
        );
        col = col.child(div().text_xs().text_color(theme::muted()).child(
            "A document is a CELL; an edit is a PATCH is a cap-gated TURN (a real receipt). A \
             CONFLICT is a first-class STATE you live in — two live alternatives, each tagged \
             with who wrote it — resolved by a later patch, never an error. Transclusion is a \
             verified cross-cell quote; backlinks are the witness-graph read backward.",
        ));

        // ── THE SUBSTRATE HEADER — the document IS a real cell ───────────────
        col = col.child(
            div()
                .flex()
                .flex_wrap()
                .items_center()
                .gap_1()
                .mt_1()
                .child(pill(format!("doc cell {}", reflect::short_hex(&region.0)), theme::accent()))
                .child(pill(format!("editor {}", reflect::short_hex(&editor.0)), theme::accent()))
                .child(pill(format!("commit {}", reflect::short_hex(&commitment)), theme::muted()))
                .child(pill(
                    if seam_ok { "seam: commitment == projection" } else { "seam DRIFT" },
                    if seam_ok { theme::good() } else { theme::bad() },
                ))
                .child(pill(
                    if rendered.has_conflict() { "conflicted" } else { "clean" },
                    if rendered.has_conflict() { theme::warn() } else { theme::good() },
                )),
        );

        // ── THE EDIT VERBS (each an edit = a real cap-gated turn) ────────────
        col = col.child(
            div()
                .flex()
                .flex_wrap()
                .gap_1()
                .mt_1()
                .child(small_button(cx, "docs-append", "✎ edit (commit a turn)", theme::good(), Cockpit::doc_append_alice))
                .child(small_button(cx, "docs-unauthorized", "⛔ try unauthorized edit", theme::bad(), Cockpit::doc_attempt_unauthorized))
                .child(small_button(cx, "docs-sow-prose", "⑂ sow prose conflict", theme::warn(), Cockpit::doc_sow_prose_conflict))
                .child(small_button(cx, "docs-sow-field", "⑂ sow field conflict (title)", theme::warn(), Cockpit::doc_sow_field_conflict)),
        );

        // ── THE OUTCOME BANNER (the real executor verdict) ───────────────────
        if let Some(banner) = &self.doc_outcome {
            col = col.child(
                div()
                    .mt_1()
                    .px_2()
                    .py_1()
                    .rounded_md()
                    .bg(theme::panel_hi())
                    .border_1()
                    .border_color(theme::border())
                    .text_xs()
                    .font_family("Menlo")
                    .text_color(theme::text())
                    .child(banner.clone()),
            );
        }

        // ── THE RENDERED DOCUMENT (clean runs + inline conflict markers) ─────
        col = col.child(section_title("THE DOCUMENT (linearized content)").mt_2().mb_1());
        let mut doc_box = div()
            .flex()
            .flex_col()
            .gap_1()
            .p_2()
            .rounded_md()
            .bg(theme::panel())
            .border_1()
            .border_color(theme::border());
        for seg in &rendered.segments {
            match seg {
                dregg_doc::Segment::Clean(t) => {
                    doc_box = doc_box.child(div().text_sm().text_color(theme::text()).child(t.clone()));
                }
                dregg_doc::Segment::Conflict(_) => {
                    doc_box = doc_box.child(
                        div()
                            .text_xs()
                            .text_color(theme::warn())
                            .child("⑂ — a conflict region lives here (see below) —"),
                    );
                }
            }
        }
        col = col.child(doc_box);

        // ── CONFLICTS-AS-STATES: both alternatives, each with PROVENANCE ─────
        if !conflicts.is_empty() {
            col = col.child(
                section_title("CONFLICTS — a STATE you live in (both alternatives + who wrote each)")
                    .mt_2()
                    .mb_1(),
            );
            for c in conflicts.iter() {
                let regime_color = if c.needs_consensus { theme::bad() } else { theme::warn() };
                let mut cbox = div()
                    .flex()
                    .flex_col()
                    .gap_1()
                    .p_2()
                    .rounded_md()
                    .bg(theme::panel_hi())
                    .border_1()
                    .border_color(regime_color);
                cbox = cbox.child(
                    div()
                        .flex()
                        .flex_wrap()
                        .items_center()
                        .gap_1()
                        .child(pill(format!("{} regime", c.regime.label()), regime_color))
                        .when(c.field.is_some(), |d| {
                            d.child(pill(
                                format!("field: {}", c.field.clone().unwrap_or_default()),
                                theme::accent(),
                            ))
                        })
                        .child(pill(
                            if c.needs_consensus { "may need consensus" } else { "unilaterally resolvable" },
                            theme::muted(),
                        )),
                );
                for alt in &c.alternatives {
                    let prov = match alt.receipt_hash {
                        Some(h) => format!("receipt {}", reflect::short_hex(&h)),
                        None => "(witness-only)".to_string(),
                    };
                    cbox = cbox.child(
                        div()
                            .flex()
                            .flex_col()
                            .gap_0p5()
                            .px_2()
                            .py_1()
                            .rounded_md()
                            .bg(theme::panel())
                            .border_1()
                            .border_color(theme::border())
                            .child(
                                div()
                                    .flex()
                                    .items_center()
                                    .gap_1()
                                    .child(pill(format!("@{}", alt.author_name), theme::accent()))
                                    .child(pill(prov, theme::muted())),
                            )
                            .child(div().text_sm().text_color(theme::text()).child(
                                if alt.text.is_empty() { "(empty)".to_string() } else { alt.text.clone() },
                            )),
                    );
                }
                let resolve_row = if c.regime == dregg_doc::Regime::Field {
                    div().flex().flex_wrap().gap_1().mt_1().child(small_button(
                        cx,
                        "docs-resolve-field",
                        "✓ settle title = alice's",
                        theme::good(),
                        Cockpit::doc_resolve_field,
                    ))
                } else {
                    div()
                        .flex()
                        .flex_wrap()
                        .gap_1()
                        .mt_1()
                        .child(small_button(cx, "docs-resolve-keep", "✓ resolve: keep alice's", theme::good(), Cockpit::doc_resolve_prose_keep))
                        .child(small_button(cx, "docs-resolve-order", "✓ resolve: order both", theme::good(), Cockpit::doc_resolve_prose_order))
                };
                cbox = cbox.child(resolve_row);
                col = col.child(cbox);
            }
        }

        // ── THE HYPERMEDIA FACES (the built Nelson pieces, reused) ───────────
        col = col.child(
            section_title("HYPERMEDIA · transclusion + backlinks (Nelson, verified)").mt_2().mb_1(),
        );
        if let Some(t) = &transclusion {
            col = col.child(
                div()
                    .flex()
                    .flex_col()
                    .gap_0p5()
                    .px_2()
                    .py_1()
                    .rounded_md()
                    .bg(theme::panel())
                    .border_1()
                    .border_color(theme::border())
                    .child(div().text_xs().text_color(theme::muted()).child(
                        "TRANSCLUSION — a verified cross-cell quote (content-addressed + receipt; \
                         the quote IS the source's committed value, never a copy):",
                    ))
                    .child(div().text_xs().text_color(theme::text()).font_family("Menlo").child(format!(
                        "{} quotes {} · field {} · receipt {} · {}",
                        reflect::short_hex(&t.host.0),
                        reflect::short_hex(&t.source.0),
                        t.transcluded_field,
                        t.provenance_receipt,
                        if t.source_finalized { "FINALIZED" } else { "tentative" },
                    ))),
            );
        } else {
            col = col.child(
                div().text_xs().text_color(theme::muted()).child("(too few cells to compose a transclusion yet)"),
            );
        }
        col = col.child(
            div().text_xs().text_color(theme::muted()).mt_1().child(format!(
                "WHAT-LINKS-HERE (who transcludes this document) · {} backlink(s) · viewer holds {} \
                 — a backlink the viewer's caps cannot admit is fogged",
                backlinks.backlinks.len(),
                backlinks.viewer_tier,
            )),
        );
        for bl in backlinks.backlinks.iter().take(6) {
            col = col.child(
                div().text_xs().text_color(theme::text()).font_family("Menlo").child(format!("← {}", bl.observer_uri)),
            );
        }

        col.into_any_element()
    }
}
