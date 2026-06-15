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
pub mod world;

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
pub use world::{CommitOutcome, World};
