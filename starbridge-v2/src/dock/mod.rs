//! The dregg cockpit's resizable-split + dock engine.
//!
//! VENDORED-AND-ADAPTED from Zed's `crates/workspace` (rev `407a6ff`), shorn of
//! the editor/project/collab world so it depends only on `gpui` + a local
//! [`theme`]. It hosts arbitrary cockpit surfaces ([`CockpitSurface`]) in
//! resizable, splittable, dockable panes — the substrate for turning the
//! cockpit's flat 28-tab right pane into a Pharo-style multiplicity of live
//! inspectors.
//!
//! Layout:
//!   * [`surface`] — [`CockpitSurface`], the slim ~8-method item trait (the
//!     cockpit analogue of Zed's ~60-method `ItemHandle`). A `*_panel(cx)` body
//!     becomes one of these.
//!   * [`pane`] — [`Pane`], a gpui entity holding a tabbed list of surfaces with
//!     a swappable tab-bar renderer (the ~15% core of Zed's `Pane`).
//!   * [`pane_group`] — [`PaneGroup`]/[`Member`]/[`PaneAxis`]/[`SplitDirection`]
//!     + the custom `PaneAxisElement`: the recursive resizable-split tree with
//!     the draggable divider (the ~90%-as-is engine).
//!   * [`dock`] — [`Dock`]/[`DockPosition`]/[`DockPanel`]/[`DraggedDock`]: the
//!     Left/Bottom/Right edge container with its 6px resize handle (slim).
//!
//! NOT yet wired into `cockpit.rs` (a sibling agent owns that file); this module
//! is self-contained and compiling, ready to integrate as a clean next step.
//! See the migration note in the module that mounts it.

// The gpui-bearing dock engine (theme/pane/split-tree/tearoff). These need gpui,
// so they compile only on the gpui paths. The `migrate` verb below is gpui-FREE
// (it depends only on the firmament cap), so it stays available on the gpui-free
// `process-pd` live-transport path too (this whole module is now reachable under
// `process-pd` for `Shell::migrate_surface`; only these gpui members are gated).
#[cfg(any(feature = "gpui-ui", feature = "gpui-web"))]
mod theme;

#[cfg(any(feature = "gpui-ui", feature = "gpui-web"))]
pub mod dock;
#[cfg(any(feature = "gpui-ui", feature = "gpui-web"))]
pub mod pane;
#[cfg(any(feature = "gpui-ui", feature = "gpui-web"))]
pub mod pane_group;
#[cfg(any(feature = "gpui-ui", feature = "gpui-web"))]
pub mod surface;

// SURFACE MIGRATION (the Local→Surface tear-off): a dock pane pops OUT into its
// own OS window with its surface identity preserved — the first concrete
// migration of `docs/deos/SURFACE-MIGRATION.md`. gpui-only (no host-type
// dependency); the cockpit drives it through a stored render callback.
#[cfg(any(feature = "gpui-ui", feature = "gpui-web"))]
pub mod tearoff;

// SURFACE MIGRATION (the `migrate(surface_cap, target)` verb): relocate a surface
// CAP along the firmament distance axis — the Local→HostPd leg of
// `docs/deos/SURFACE-MIGRATION.md` §2(b). The re-mint + the attenuating gate are
// real here; the live present re-home is the named remaining compositor seam.
// gpui-free in body (depends only on the firmament + the surface cap), but lives
// under `dock/` next to its tear-off sibling; gated on `embedded-executor`, which
// brings in `crate::surface::SurfaceCapability` + the `dregg_firmament` cap types.
#[cfg(feature = "embedded-executor")]
pub mod migrate;

// The self-hosting dev-loop surfaces (the light, gpui-native ones): a real editor
// + a real terminal as dock panes, so deos development happens INSIDE deos. Chat
// (matrix-rust-sdk's heavy async tree) is deliberately NOT statically linked here —
// per docs/deos/DEOS-DISTRIBUTION.md it belongs in a lazily-launched confined PD.
#[cfg(feature = "dev-surfaces")]
pub mod chat_surface;
#[cfg(feature = "dev-surfaces")]
pub mod editor_surface;
#[cfg(feature = "dev-surfaces")]
pub mod hermes_surface;
#[cfg(feature = "dev-surfaces")]
pub mod terminal_surface;

#[cfg(any(feature = "gpui-ui", feature = "gpui-web"))]
pub use dock::{Dock, DockPanel, DockPosition, DraggedDock};
#[cfg(feature = "embedded-executor")]
pub use migrate::{migrate, MigrateError, MigrationTarget};
#[cfg(any(feature = "gpui-ui", feature = "gpui-web"))]
pub use pane::Pane;
#[cfg(any(feature = "gpui-ui", feature = "gpui-web"))]
pub use pane_group::{
    ActivePaneDecorator, Member, PaneAxis, PaneGroup, PaneLeaderDecorator, SplitDirection,
    HANDLE_HITBOX_SIZE,
};
#[cfg(any(feature = "gpui-ui", feature = "gpui-web"))]
pub use surface::{CockpitSurface, SurfaceId};
#[cfg(any(feature = "gpui-ui", feature = "gpui-web"))]
pub use tearoff::{TornOffWindow, TornSurfaceId, WindowRegistry};
