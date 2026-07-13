//! # deos-view — render a deos-js applet's view-tree, native (gpui) OR web (HTML).
//!
//! THE RENDERER EXTRACTION (mirroring the deos-reflect extraction ember asked for):
//! `deos-js` stays GPUI-FREE — it produces the serializable `deos.ui.*` view-tree
//! ([`tree::ViewNode`]) and drives the verified turns. `deos-view` holds the renderers
//! that turn that DATA into a surface.
//!
//! TWO RENDERERS, ONE VIEW-TREE — the card is renderer-INDEPENDENT:
//!
//! * **`native`** (default, feature-gated) — `ViewNode` → real gpui-component pixels:
//!     1. `bridge::build_live_view` runs an applet's JS in real SpiderMonkey, extracts
//!        its view-tree and hands back the live `Applet` paired with the parsed
//!        [`tree::ViewNode`].
//!     2. `render::AppletView` walks the tree into gpui widgets (`vstack→v_flex`,
//!        `button→Button`, `text→Label`, `bind→Label` re-read, …); a button's `on_click`
//!        fires a REAL cap-gated verified turn; a `bind` re-reads the live ledger.
//!     3. `faces::FacesView` renders the moldable `present()` faces through the SAME
//!        vocabulary; `headless` bakes any view to a PNG offscreen (the cockpit's path).
//!
//! * **`web`** (feature-gated, gpui-FREE + deos-js-FREE) — the IDENTICAL
//!   [`tree::ViewNode`] → an HTML/DOM string ([`web::render_card_document`]),
//!   node-for-node mirroring the gpui vocabulary, into a browser-loadable `.html`. This
//!   is the web-projection of the reflective cockpit: the SAME card paints in a browser,
//!   not just the native window. See the `web_render_card` example for the bake.
//!
//! ONE PARITY EXCEPTION (honest boundary): "renderer-INDEPENDENT" is exact for the
//! view-tree DATA and holds for every node's *content*; the single INTERACTIVITY gap
//! is `input` — a real editable `<input>` on web, but display-only on native (a
//! read-only label; deos-view has no native text-entry widget yet), so a native
//! `input` reflects only agent-seeded draft state and an unseeded submit fires
//! `arg = 0`. See the `render` module's NATIVE/WEB PARITY note (audit finding #17).

// The view-tree MODEL is renderer-independent (gpui-free serializable DATA): it is
// always compiled, under BOTH the `native` and `web` renderers.
/// The ONE affordance-transport codec — encode/decode a `{turn, arg}` affordance for whatever
/// channel a surface backend carries it on (Discord custom-id / Telegram callback / web). Always
/// compiled (every backend decodes through it).
pub mod affordance;
/// The [`SurfaceBackend`](backend::SurfaceBackend) trait — the one seat every renderer of the
/// [`ViewNode`] IR shares (`render(tree, binds)` + `decode(id)`). Always compiled.
pub mod backend;
pub mod console;
pub mod fmt;
/// The dregg-native forge's VISUAL surface — a repo / diff / pull-request /
/// review-thread as a serializable [`tree::ViewNode`] tree, so the forge paints in
/// every glass (native gpui / web HTML / discord / seL4). PURE serde + `tree` (no
/// `dregg-doc`, no gpui): the self-contained `ForgeView` data model + `forge_view`.
pub mod forge_card;
/// The grain economy's VISUAL surface — a CI pipeline / rented-grain run (a CWM charter
/// of steps run in a rented, metered, confined grain; a PR can be a bounty) as a
/// serializable [`tree::ViewNode`] tree, so a grain run paints in every glass (native
/// gpui / web HTML / discord / seL4). PURE serde + `tree` (no `agent-platform`, no gpui):
/// the self-contained `GrainRun` snapshot + `grain_run_view`, mirroring `forge_card`.
pub mod grain_run_card;
/// Console data-source honesty: unreachable ≠ empty ≠ fixtures (never render a
/// live-green surface over an unreachable node). Wired into `console::ConsoleModel`
/// (`ConsoleModel::health` drives the page banner + panel gate + per-surface notes).
pub mod source_health;
/// The shared [`ViewNode`](tree::ViewNode) → plain-text walk — the prose projection BOTH chat
/// transports use (Telegram's message text, WeChat's OA message body). One walk, never two subset
/// walkers. Always compiled (pure `tree`).
pub mod text;
pub mod tree;
pub use affordance::{
    affordance_id, affordance_id_with_text, parse_affordance_id_with_text, wechat_reply_index,
    AffordanceTransport,
};
pub use backend::{actuations, actuations_with, Actuation, SurfaceBackend};
pub use console::{
    console_bind_values, console_card, console_slot_seeds, demo_console, ConsoleModel,
    HermesStatus, HermesView, LedgerView, MandateEdge, ReceiptRow, SpendLine, VatState, VatView,
    WitnessStance,
};
pub use fmt::BindFmt;
pub use forge_card::{
    forge_view, forge_view_json, CheckStatus, CheckView, ConflictView, DiffHunk, DiffKind,
    DiffLine, FileEntry, FileStatus, ForgeView, MergeGate, PullRequest, Repo, ReviewEntry,
    ReviewKind,
};
pub use grain_run_card::{
    grain_run_view, grain_run_view_json, BountyState, BountyView, CheckGate, GrainRun, LeaseStatus,
    LeaseView, StepStatus, StepView,
};
pub use source_health::{Banner, SourceHealth, SurfaceNote};
pub use tree::{
    disclose, parse_view_tree, pill_display, resolve_mounts, Crumb, Disclosure, HaloHandle,
    MapMountSource, MenuItem, MountSource, PillCase, RawItem, RawNode, RawPillCase, RawProps,
    ViewNode, MAX_MOUNT_DEPTH, MAX_MOUNT_NODES,
};

// ── THE INTEGRATION SEAM (feature `integration`, folded into `native`): the ONE gate +
//    the surface→card bridge — the only place that names BOTH the Lean-mirrored
//    membrane/reactive surface (`starbridge-web-surface`) AND the reflective faces
//    (`deos-reflect`) without a cargo cycle (see Cargo.toml). gpui-FREE + deos-js-FREE. ──
/// [`gate`] — an actuation node's `enabled` from the FULL 4-conjunct gate
/// (`is_attenuation ∧ disclosure ∧ transition ∧ window`), NOT `is_attenuation` alone.
#[cfg(feature = "integration")]
pub mod gate;
/// [`lower`] — the surface→card bridge: `deos_reflect::Presentation → ViewNode`, one
/// lossless path to "liberate any surface into a card".
#[cfg(feature = "integration")]
pub mod lower;
/// [`pipeline`] — THE RENDER ENTRY, with the gate LIVE in it: `resolve_mounts → disclose →
/// gate_actuation_nodes → backend.render`. An actuation's `enabled` is COMPUTED at render time from
/// the FULL 4-conjunct gate for the viewer at the height, not read off the author's bool.
#[cfg(feature = "integration")]
pub mod pipeline;
#[cfg(feature = "integration")]
pub use gate::{gate_actuation_nodes, reactive_membrane_enabled, ReactiveSurfaceGate};
#[cfg(feature = "integration")]
pub use lower::{presentation_to_view, presentations_to_view};
#[cfg(feature = "integration")]
pub use pipeline::{gated_view, render_actuations, render_surface, NoMounts, RenderRequest};

// ── THE CAP-SCOPE (feature `cap`): the REAL, cap-scoped console read surface — a `Catalog`
//    source trait bound to our cells + the dregg-auth caveat-chain subject gate (a resource
//    is shown iff its owner-cap subject == the viewer). PURE (gpui-free + deos-js-free): only
//    serde + the sibling `dregg-auth` credential core, so it rides the DEFAULT build AND
//    compiles standalone (`cargo test --no-default-features --features cap --lib` — no gpui,
//    no SpiderMonkey), and never bloats the tiny `web` bake. ──
#[cfg(feature = "cap")]
pub mod catalog;
#[cfg(feature = "cap")]
pub use catalog::{
    demo_catalog, subject_credential, CapScope, CapTurn, Catalog, SnapshotCatalog, SUBJECT_ATTR,
};

// ── The NATIVE renderer: `ViewNode` → real gpui-component pixels (the heavy stack
//    + deos-js live verified turns). Gated on `native` so the `web` build stays tiny. ──
#[cfg(feature = "native")]
pub mod bridge;
#[cfg(feature = "native")]
pub mod faces;
#[cfg(feature = "native")]
pub mod headless;
// The cell-heap-as-view-source — read a cell's hosted view-tree out of its committed heap
// (the native half of the composition keystone). Needs dregg-cell, so native-only.
#[cfg(feature = "native")]
pub mod mount;
#[cfg(feature = "native")]
pub mod render;

#[cfg(feature = "native")]
pub use bridge::{build_live_view, view_tree_key, LiveView};
#[cfg(feature = "native")]
pub use faces::FacesView;
#[cfg(feature = "native")]
pub use mount::{
    cell_id_from_hex, cell_id_hex, ledger_mount_source, view_tree_from_cell_heap, VIEWTREE_COLL,
};
#[cfg(feature = "native")]
pub use render::{AppletView, SharedApplet};

// ── The WEB renderer: the SAME `ViewNode` → an HTML/DOM string. gpui-free + deos-js-
//    free (only serde). This is the web-projection of the reflective cockpit — the
//    card paints in a browser, not just the native cockpit. ──
#[cfg(feature = "web")]
pub mod web;
#[cfg(feature = "web")]
pub use web::{
    render_card_document, render_card_live_document, render_doccollab_live_document,
    render_gallery_document, render_html, render_inspector_live_document,
    render_kvstore_live_document, render_session_forms, render_tally_live_document,
    render_trustless_cell_document, GalleryCard, HeapSlotOpening, SessionFormBackend,
    TrustlessAttestation, WebBackend,
};

// ── The DISCORD renderer: the SAME `ViewNode` → a serenity `CreateEmbed` + button
//    components. gpui-free + deos-js-free (serde + serenity builder/model). The FOURTH
//    backend — the discord-bot's surfaces ARE these cards. ──
#[cfg(feature = "discord")]
pub mod discord;
#[cfg(feature = "discord")]
pub use discord::{
    affordance_custom_id, parse_affordance_id, render_card, DiscordBackend, DiscordCard,
    TURN_PREFIX,
};

// ── The TELEGRAM backend: the SAME `ViewNode` → Telegram message text (the non-affordance
//    half; the affordance half becomes the frontend's inline keyboard). gpui-free + deos-js-free
//    (serde only). The frontend crate renders through this instead of its own subset walker. ──
#[cfg(feature = "telegram")]
pub mod telegram;
#[cfg(feature = "telegram")]
pub use telegram::{render_text, TelegramBackend};

// ── The WECHAT backend: the SAME `ViewNode` → a WeChat Official-Account text message + its
//    NUMBERED REPLY LIST (the OA channel has no buttons: the user replies with the number). The
//    prose is the SHARED `text::render_text` walk (no second subset walker); the affordance half is
//    the tree's actuations, 1-based, a refused one shown LOCKED. gpui-free + deos-js-free (serde
//    only). The FIFTH backend over the one IR. ──
#[cfg(feature = "wechat")]
pub mod wechat;
#[cfg(feature = "wechat")]
pub use wechat::{render_message, WeChatBackend, WeChatMessage, WeChatOption, LOCK_GLYPH};
