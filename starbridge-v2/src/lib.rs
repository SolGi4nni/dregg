//! Starbridge v2 — the native dregg master interface (library core).
//!
//! The headless, gpui-free heart lives here so it is `cargo test`-able and
//! reusable by both builds:
//!   * [`world`] — the embedded verified executor + live local dregg world.
//!   * [`dynamics`] — the observation/event stream of state transitions.
//!   * [`reflect`] — the uniform reflective object model the views consume.
//!   * [`surface`] / [`shell`] / [`compositor`] — the cap-first multi-SURFACE
//!     desktop shell: each dregg cell can be a cap-confined surface
//!     (apps-as-cells), the shell is a cap-first window manager over the live
//!     world, and the [`compositor`] enforces the VERIFIED-SCENE discipline
//!     (T1 non-overlap · T2 label-binding · T3 focus-exclusivity — the Lean
//!     `Dregg2.Apps.Compositor` teeth) at the pixel layer.
//!   * [`agent`] — the AGENT-ACTIVITY surface (the ADOS keystone): an agent
//!     loop's provable activity (held mandate · cap-gated turns · receipts ·
//!     authorization), rendered as a cap-gated surface cell.
//!
//!   * [`swarm`] — the SWARM COORDINATOR (A2 tool-call seam): N agent cells
//!     coordinating as confined Surface cells, with the notify-edge inbox
//!     threading async wakes (`EmitEvent` → `NotifyEdge` → drain turn) between
//!     them. Every action is cap-gated + receipted; the notify edge is async
//!     (the recipient drains in its OWN future turn, not a joint turn).
//!
//! The `native-full` binary (`src/main.rs`) wires these into the gpui cockpit.
//! The wire-contract client (`client`/`model`) lives in the binary crate for
//! the remote-node + `sel4-thin` paths.

// The wire-contract DATA MODEL (`GET /status`, `/api/cells`, `/api/events/stream`
// receipt events, the `POST /turn/submit` request shape). Pure serde structs (no
// reqwest, no gpui), so they compile in BOTH builds and are `cargo test`-able —
// the embedded build's LIVE-NODE panel reflects a remote node through these, and
// the sel4-thin build speaks them as its only contract. Single-sourced here (the
// bin re-exports them) so the live-node lane and the thin client share one mirror.
#[cfg(any(feature = "embedded-executor", feature = "sel4-thin"))]
pub mod model;
// The wire-contract CLIENT (`NodeClient::{Mock,Http}`) + the SSE/snapshot I/O.
// The HTTP/SSE byte-pull is gated on `live-node` (pulls `reqwest`); the Mock
// backend + the wire types are always available. Lives in the library so the
// embedded master interface's live-node panel reuses it (not just the thin bin).
#[cfg(any(feature = "embedded-executor", feature = "sel4-thin"))]
pub mod client;

// The LIVE NODE connection — the SSE-drain + live-reflection heart (the pure
// layer is gpui-free + `cargo test`-able; the reqwest I/O is gated on `live-node`).
#[cfg(feature = "embedded-executor")]
pub mod live_node;

// The native deos AFFORDANCE surface — htmx-on-crack with the firing→executed-turn
// seam CLOSED through the embedded executor (the thesis `starbridge-web-surface`
// could only model). gpui-free, `cargo test`-able.
#[cfg(feature = "embedded-executor")]
pub mod affordance;

// The WEB-OF-CELLS browser — the cockpit as a native browser of the `dregg://`
// docuverse: it lists the addressable cells (the real `WebOfCells` attested
// fetch + ledger-drawn `OriginChrome`), opens one to its per-viewer affordance
// surface (the real `AffordanceSurface::project_for` attenuation) + rehydration
// liveness-type, and fires an affordance through THIS crate's embedded executor.
// gpui-free, `cargo test`-able (the model is pure data, like `landing`).
#[cfg(feature = "embedded-executor")]
pub mod web_cells;

// The DREGGVERSE navigation — "what links here", the verified per-viewer query on
// the witness-graph. VENDORED byte-identical from the committed
// `dregg_app_framework::dreggverse_map` (a thin pure navigation over the REAL
// `starbridge_web_surface` `Backlinks` + `Membrane`, both already deps here), so the
// cockpit renders the genuine `DreggverseMap::project_for` WITHOUT dragging
// app-framework's heavy tokio/axum/captp tree into this standalone workspace.
#[cfg(feature = "embedded-executor")]
pub mod dreggverse_map;

// The WHAT-LINKS-HERE panel model — Ted Nelson's two-way link, navigable: for the
// focused cell it builds a REAL `Backlinks` witness-graph from the live image, walks
// it with the vendored `DreggverseMap`, and projects through the focused agent's
// `Membrane` (the link fog-of-war). gpui-free, `cargo test`-able (pure data, like
// `web_cells`/`landing`).
#[cfg(feature = "embedded-executor")]
pub mod links_here;

// The interactive POWERBOX (CapDesk) — the trusted designation flow: an app-cell
// requests a capability it lacks; the trusted UI (the cockpit principal, NOT the app)
// presents a picker filtered to what the USER actually holds (mint_needs_held_factory
// made visible); the user designates a target + attenuated rights; the powerbox mints
// a fresh attenuated cap into the app's c-list via a REAL grant turn through the
// embedded executor. gpui-free, `cargo test`-able (pure flow model, like `web_cells`).
#[cfg(feature = "embedded-executor")]
pub mod powerbox;

#[cfg(feature = "embedded-executor")]
pub mod agent;
#[cfg(feature = "embedded-executor")]
pub mod buffer;
#[cfg(feature = "embedded-executor")]
pub mod cipherclerk;
#[cfg(feature = "embedded-executor")]
pub mod compositor;
#[cfg(feature = "embedded-executor")]
pub mod coordination;
#[cfg(feature = "embedded-executor")]
pub mod debug;
#[cfg(feature = "embedded-executor")]
pub mod demo;
#[cfg(feature = "embedded-executor")]
pub mod dynamics;
#[cfg(feature = "embedded-executor")]
pub mod edit;
#[cfg(feature = "embedded-executor")]
pub mod graph;
#[cfg(feature = "embedded-executor")]
pub mod landing;
#[cfg(feature = "embedded-executor")]
pub mod narration;
#[cfg(feature = "embedded-executor")]
pub mod organs;
#[cfg(feature = "embedded-executor")]
pub mod palette;
#[cfg(feature = "embedded-executor")]
pub mod proofs;
#[cfg(feature = "embedded-executor")]
pub mod reflect;
#[cfg(feature = "embedded-executor")]
pub mod replay;
#[cfg(feature = "embedded-executor")]
pub mod scene;
// WHAT-IF SIMULATION — compose any intent over any cell + an exhaustive effect
// palette, predict its consequences in a FORKED throwaway world (the real
// executor over a deep copy of the live ledger), then commit it for real. The
// prediction is the live executor's verdict run one turn ahead; the live world is
// never touched until commit. gpui-free, `cargo test`-able.
#[cfg(feature = "embedded-executor")]
pub mod simulate;
#[cfg(feature = "embedded-executor")]
pub mod shell;
#[cfg(feature = "embedded-executor")]
pub mod surface;
#[cfg(feature = "embedded-executor")]
pub mod organ_ops;
#[cfg(feature = "embedded-executor")]
pub mod swarm;
#[cfg(feature = "embedded-executor")]
pub mod swarm_budget;
#[cfg(feature = "embedded-executor")]
pub mod terminal;
#[cfg(feature = "embedded-executor")]
pub mod token_inspector;
#[cfg(feature = "embedded-executor")]
pub mod world;
// NATIVE WORLD PERSISTENCE (M4 — docs/deos/WORLD-PERSISTENCE-PLAN.md): the
// durable-image weld onto the node's already-built `dregg-persist` spine (redb
// commit log + checkpoint⊕overlay recovery). gpui-free, `cargo test`-able.
#[cfg(feature = "embedded-executor")]
pub mod persistence;

// THE LIVE INSPECT→ACT LOOP — the Smalltalk inspect→act→inspect keystone: an
// inspected object shows the messages it understands (its cap-gated affordances)
// inline, fires one as a real verified turn, and re-inspects the post-state.
// gpui-free, `cargo test`-able (reuses `reflect` + `affordance` + `world`).
#[cfg(feature = "embedded-executor")]
pub mod inspect_act;
// THE LIVE WORKSPACE — the doIt / printIt / inspectIt evaluator: compose an
// intent, evaluate it in a forked throwaway world (predict, never mutate), print
// the predicted receipt, inspect the predicted post-state as live objects, then
// commit-or-discard. gpui-free, `cargo test`-able (reuses `simulate` + `reflect`).
#[cfg(feature = "embedded-executor")]
pub mod workspace;
// THE WONDER ROOM — the AOL-wonder front door: every cell a pokeable glowing
// object (glow = real recent activity from `dynamics`), with direct-manipulation
// halos (inspect/grab/explain) and drag-value transfers (predict-then-commit).
// gpui-free, `cargo test`-able. See `docs/deos/AOL-WONDER.md`.
#[cfg(feature = "embedded-executor")]
pub mod wonder;
// THE PRESENTATION SPINE (L1) — the Pharo-moldable framework primitive: every protocol
// object offers MULTIPLE named presentations (the 7 PresentationKinds; RawFields = the
// existing reflect::Inspectable floor) + the Gadget/CommittingGadget traits (interactive
// construction on the simulate→commit spine) + Spotter (universal search) + the
// generalized Halo. The spine everything inherits. See docs/deos/INSPECTOR-FRAMEWORK.md.
#[cfg(feature = "embedded-executor")]
pub mod presentable;
// THE REHYDRATABLE UI-SLICE SNAPSHOT — "the camera you can re-run": a tiny witness-cursor
// (focus + presentation-kind + height/receipt-head) that re-derives the SAME inspector view
// from the durability log (replay → re-project), liveness-typed (Live/ReplayedDeterministic/
// ReconstructedApproximate). The screenshot keeps the angle, drops the frame. See REHYDRATABLE-SURFACES.md.
#[cfg(feature = "embedded-executor")]
pub mod ui_snapshot;
// THE UI-CELL SUBSTRATE (M3 · reflexive migration §3) — the cockpit's own view-state
// self-hosted as real dregg cells via the proven BufferCell two-tier split: ViewCell
// (a view's focus/present-idx camera-aim, free in-memory draft + occasional witnessed
// SetField commit, revision = backing nonce) is itself Presentable (FocusTarget::ViewCell)
// so the inspector can inspect ITSELF; WorkspaceCell carries the active-tab selector.
// `present` stays PURE and reads the COMMITTED (prior-frame) aim — the unit-delay that
// breaks the reflexive self-cycle. See docs/deos/{REFLEXIVE-MIGRATION,STRATIFIED-FIXPOINT}.md.
#[cfg(feature = "embedded-executor")]
pub mod view_cell;
// THE FRACTAL META-DEBUG (M5 · reflexive migration §4) — suspend the live system,
// inspect it as an object, recursively (debug the debugger). Suspend=halt-the-live-loop
// (the World gate + pending queue, distinct from Snapshot=freeze-a-cursor); MetaDebugView
// impl Presentable over the suspended world (FocusTarget::DebugFrame/World/Cockpit — the
// one-arm reflexivity); the MetaStack is the lazily-materialized 3-Lisp tower, grounded at
// the gpui loop. See docs/deos/{FIRMAMENT-REFLEXIVE-SUBSTRATE,REFLEXIVE-MIGRATION,STRATIFIED-FIXPOINT}.md.
#[cfg(feature = "embedded-executor")]
pub mod meta_debug;
#[cfg(feature = "embedded-executor")]
pub mod cell_inspector;
#[cfg(feature = "embedded-executor")]
pub mod receipts_inspector;
#[cfg(feature = "embedded-executor")]
pub mod cap_inspector;
#[cfg(feature = "embedded-executor")]
pub mod predicate_composer;
// THE TRUST PANEL (human-layer M1 · docs/deos/HUMAN-LAYER.md §3) — the WHO-I-AM face
// (identity card: devices = the current key set, guardians-as-faces = the recovery
// council with its M-of-N threshold drawn, the KEL/rotation timeline) + the recovery
// UX (set guardians, "ask your guardians" quorum progress, the cooling window as a
// safety feature). A gpui-free Presentable over the REAL `dregg_sdk::identity`
// reflection + cipherclerk, the same shape as the other inspector lanes.
#[cfg(feature = "embedded-executor")]
pub mod trust_panel;
// L1-LANE INSPECTORS/GADGETS (the moldable-inspector multiplicity, all on the spine):
// turn_builder (effect/call-forest/turn) · predicate_composer (the caveat-language uplift) ·
// cap_inspector (attenuation/cap-crown) · cell_inspector (deep state) · receipts_inspector
// (time-travel) · token_inspector (macaroon loop). See docs/deos/INSPECTOR-FRAMEWORK.md.
#[cfg(feature = "embedded-executor")]
pub mod turn_builder;
#[cfg(feature = "embedded-executor")]
pub mod settlement_inspector;
// L8/L9 INSPECTORS: federation_inspector (consensus/blocklace/finality — wire-backed +
// honest remote-path catalog) · circuit_inspector (the 8-felt commitment anti-omission
// binding, nullifier non-membership, proof tiers). On the spine; see INSPECTOR-FRAMEWORK.md.
#[cfg(feature = "embedded-executor")]
pub mod federation_inspector;
#[cfg(feature = "embedded-executor")]
pub mod circuit_inspector;
// THE CV-BRIDGE (milestone #1): "blame this cell" — ClusterVision's provenance
// (`cv blame`) wired into the inspector as a Presentable. Bridges EXTERNALLY (cv
// as the read/query face; no substrate change), degrades honestly when cv is
// absent. See docs/deos/REFLEXIVE-DISTRIBUTED-IMAGE.md §2.5/§3.3.
#[cfg(feature = "embedded-executor")]
pub mod cv_provenance;

#[cfg(feature = "embedded-executor")]
pub use presentable::{
    CommittingGadget, FocusTarget, Gadget, GadgetError, GadgetField, GadgetInput, GadgetKind,
    GadgetValidation, GaugeView, GraphView, Halo, HaloCommand, LatticeView, MerkleTreeView,
    Presentable, PresentableExt, Presentation, PresentationBody, PresentationKind, PresentCtx,
    ReflectedCell, Registry, SmState, SmTransition, Spotter, SpotterHit, StateMachineView,
    TimelineEvent, TimelineView, TraceStep, TraceView,
};
#[cfg(feature = "embedded-executor")]
pub use view_cell::{ViewCell, ViewDoc, ViewError, WorkspaceCell};

#[cfg(feature = "embedded-executor")]
pub use affordance::{
    AffordanceIntent, AffordanceSnapshot, AffordanceSurface, CellAffordance, EffectSummary,
    FireError, FireOutcome, Rehydration,
};
#[cfg(feature = "embedded-executor")]
pub use web_cells::{
    AffordanceRow, CellRow, SemiReinteractiveTransclusion, Transclusion, WebCellsBrowser,
};
#[cfg(feature = "embedded-executor")]
pub use dreggverse_map::{DreggverseGraph, DreggverseLink, DreggverseMap};
#[cfg(feature = "embedded-executor")]
pub use links_here::{BacklinkRow, LinksHerePanel};
#[cfg(feature = "embedded-executor")]
pub use powerbox::{
    AppLauncher, CapabilityRequest, GrantableTarget, GrantedCap, LaunchedApp, Powerbox,
    PowerboxOutcome,
};
#[cfg(feature = "embedded-executor")]
pub use agent::{AgentActivity, AgentSurface};
#[cfg(feature = "embedded-executor")]
pub use buffer::{BufferCell, BufferDoc, BufferError, BufferView};
#[cfg(feature = "embedded-executor")]
pub use live_node::{LiveReflection, ReceiptFeed, SseParser, SseRecord};
#[cfg(feature = "embedded-executor")]
pub use compositor::{
    label_of, CompositedSurface, Compositor, CompositorScene, FrameCommit, Present, PresentError,
    RegionId,
};
#[cfg(feature = "embedded-executor")]
pub use coordination::{MandateArrow, NotifyArrow, SwarmGraph, SwarmNode};
#[cfg(feature = "embedded-executor")]
pub use demo::{render_headless_report, DemoError, DemoFrame, HeadlineDemo};
#[cfg(feature = "embedded-executor")]
pub use graph::{GraphEdge, GraphLayer, GraphNode, OcapGraph};
#[cfg(feature = "embedded-executor")]
pub use landing::{LandingPortal, PortalLine, PortalSection, Tone};
#[cfg(feature = "embedded-executor")]
pub use narration::{
    ClaimPosture, ClaimedAction, Correlation, Divergence, NarrationPanel, NarrationRow,
};
#[cfg(feature = "embedded-executor")]
pub use organs::{
    FlashWellReflection, OrganKind, OrganReach, OrganSurvey, RemoteOrgan, TrustlineReflection,
};
#[cfg(feature = "embedded-executor")]
pub use proofs::{AttachStatus, ProofBoard, ProofEntry, VerificationTier};
#[cfg(feature = "embedded-executor")]
pub use scene::{
    baked_admit_table, compositor_program, scene_admit, surface_factory, PresentVerdict,
    VerifiedScene, PRESENT_DIGEST_SLOT, SURFACE_FACTORY_VK,
};
#[cfg(feature = "embedded-executor")]
pub use simulate::{
    commit as simulate_commit, render_outcome, simulate, CellDelta, DraftAction, EffectKind,
    IntentDraft, SimOutcome,
};
#[cfg(feature = "embedded-executor")]
pub use organ_ops::{OrganDriver, OrganOp, OrganOpError, OrganOpOutcome};
#[cfg(feature = "embedded-executor")]
pub use swarm::{
    BudgetMeter, NotifyEdge, Swarm, SwarmBudget, SwarmError, SwarmMember, SwarmMemberView,
    SwarmView,
};
#[cfg(feature = "embedded-executor")]
pub use swarm_budget::{
    StingrayBudgetView, StingrayDrawError, StingraySwarmBudget, SWARM_POOL_SILO,
};
#[cfg(feature = "embedded-executor")]
pub use terminal::{Command, CommandError, OutputLine, TerminalCell, TerminalView};
#[cfg(feature = "embedded-executor")]
pub use shell::{Layout, Scene, SceneItem, Shell, ShellError};
#[cfg(feature = "embedded-executor")]
pub use surface::{Rect, Surface, SurfaceCapability, SurfaceId, SurfaceKind};
#[cfg(feature = "embedded-executor")]
pub use world::{demo_genesis, demo_world, CommitOutcome, DemoSeed, World};
