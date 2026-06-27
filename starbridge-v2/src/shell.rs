//! The shell — a cap-first window manager + compositor over real cells.
//!
//! This is the native desktop-OS pillar of the master interface. The [`Shell`]
//! owns a set of [`Surface`]s, the z-order stack, the focus, and the
//! **firmament surface-fabric** the window caps are checked against. It is a
//! CAP-FIRST window manager: every window op — focus, raise, move, resize,
//! minimize, close, share — is GATED by the surface's capability. There is no
//! ambient authority over a window; you drive a surface only by presenting the
//! cap the shell minted when it opened.
//!
//! **The authority is the REAL `dregg_firmament` capability** (`docs/
//! DREGG-DESKTOP-OS.md` §7 — the one latent divergence, closed). The shell owns
//! a [`SurfaceBacking`](dregg_firmament::SurfaceBacking): a real
//! [`dregg_cell::Ledger`] + [`dregg_turn::TurnExecutor`]. When a surface opens,
//! the shell seeds a fresh *backing surface-cell* + an *owner holder* in that
//! fabric and installs the owner's original grant over the backing cell; the
//! returned [`SurfaceCapability`] carries the REAL
//! [`Capability`](dregg_firmament::Capability) `target = Surface(backing_cell)`.
//! Every op authenticates by RESOLVING that cap through the firmament's
//! `granted ⊆ held` ([`is_attenuation`](dregg_firmament::is_attenuation)) gate —
//! the SAME gate the local (`seL4_CNode_Mint`) and distributed (`recKDelegate
//! Atten`) backings use, no special-casing. A window-SHARE
//! ([`Shell::share`]) runs a GENUINE `Effect::GrantCapability` turn, so a
//! WIDENING share is REJECTED by the real executor — the no-amplification
//! guarantee firing at the desktop. There is NO bearer-secret model.
//!
//! Each surface is a view of a REAL cell in the embedded [`World`](crate::world)
//! (apps-as-cells). The shell reads the live world ledger to:
//!   * derive each surface's TRUSTED-PATH identity label (the owning cell's real
//!     id + lifecycle) — anti-spoof chrome the shell draws, not the surface, so
//!     a surface cannot impersonate another cell, and
//!   * compose a [`Scene`]: the ordered, gpui-free description of what to paint
//!     (back-to-front), which the cockpit maps onto a gpui scene.
//!
//! Two ledgers, two distinct roles: the firmament fabric holds the AUTHORITY
//! cap-graph (what the cap gate checks); the embedded world holds the rendered
//! CONTENT + identity (what `compose` reads). The viewed cell (identity) and the
//! backing surface-cell (authority) are kept distinct — exactly as a surface and
//! its cap are distinct objects.
//!
//! The compositor framing: the cockpit is ONE privileged [`SurfaceKind::Console`]
//! surface; the other surfaces are cap-confined cell views, tiled/floated/
//! stacked in z-order. Surfaces show real cell state and react to real turns
//! (re-read each frame).
//!
//! This module is gpui-free and `cargo test`-able. The cockpit owns the gpui
//! mapping + the input routing.

use dregg_cell::lifecycle::CellLifecycle;
use dregg_cell::CellId;
use dregg_firmament::{AuthRequired, Capability, ResolveError, SurfaceBacking};

use crate::compositor::{
    label_of, CompositedSurface, Compositor, CompositorScene, FrameCommit, Present, PresentError,
};
use crate::surface::{Rect, Surface, SurfaceCapability, SurfaceId, SurfaceKind};
use crate::world::World;

/// Why a window op was refused. The shell's refusals are a FEATURE — they are
/// the ocap discipline of the window manager firing (the same spirit as the
/// executor rejecting an over-grant), surfaced so the operator can see WHY an
/// op was denied.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ShellError {
    /// The presented capability does not authenticate: it names no live surface,
    /// its authority targets the wrong backing cell (cap confusion), or the
    /// firmament's `granted ⊆ held` gate refused the requested rights. The op is
    /// refused — authority over a surface is exactly the REAL firmament cap it
    /// carries, checked through [`SurfaceBacking::invoke`].
    Unauthorized,
    /// The named surface does not exist (already closed, or never opened).
    NoSuchSurface(SurfaceId),
    /// A protected op on the console surface (the console can't be closed — it
    /// is the trusted root; closing it would orphan the whole shell).
    ConsoleProtected,
    /// A window-SHARE was REJECTED by the REAL executor — a WIDENING share (a
    /// surface trying to hand out MORE authority over the glass than it holds)
    /// is refused by the genuine `Effect::GrantCapability` attenuation gate
    /// (`DelegationDenied`). This is the no-amplification guarantee firing at the
    /// window-manager layer; carries the executor's reason for the operator log.
    ShareDenied(String),
    /// A `present()` was REFUSED by the compositor's VERIFIED-SCENE authority —
    /// the surface tried to overpaint another surface's region (T1), declare a
    /// label that is not its genuine owner-binding (T2), steal input focus or
    /// composite into an ambiguous-focus scene (T3). This is the anti-ghost
    /// tooth firing at the PIXEL layer (the Lean `present_*_rejected` theorems),
    /// surfaced so the operator sees WHICH tooth bit. Carries the
    /// [`PresentError`] — distinct from `Unauthorized` (which is the WINDOW-cap
    /// gate): a present can hold a valid window cap and STILL be refused because
    /// the scene authority is a separate gate enforced on top (§5).
    PresentRefused(PresentError),
}

/// How the shell lays out surfaces. The compositor supports three classic
/// arrangements; all paint in z-order, but the geometry the shell assigns
/// differs. (Float = the surfaces keep their own rects; tile/stack = the shell
/// arranges them.)
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Layout {
    /// Surfaces float at their own rects (free placement; move/resize honored).
    Float,
    /// Non-console surfaces tile the work area in a simple grid; the console
    /// keeps its rect (it is the anchored master console).
    Tile,
    /// Non-console surfaces stack centered + offset (a cascade); the front one
    /// is fully visible.
    Stack,
}

impl Layout {
    pub fn label(self) -> &'static str {
        match self {
            Layout::Float => "float",
            Layout::Tile => "tile",
            Layout::Stack => "stack",
        }
    }
}

/// The trusted-path identity of a surface, drawn by the SHELL from the live
/// ledger (never from the surface's self-description). This is the anti-spoof
/// chrome: a surface labels itself with a title, but the *identity badge* — the
/// owning cell's real id + whether that cell is live/sealed/destroyed/missing —
/// comes from the shell reading the ledger, so a surface cannot impersonate
/// another cell's identity.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IdentityLabel {
    /// The owning cell id (the REAL anchor — what the surface is a view of).
    pub cell: CellId,
    /// A short, operator-legible identity string (the cell id, abbreviated).
    pub short: String,
    /// The live lifecycle of the backing cell, as a badge ("live"/"sealed"/
    /// "destroyed"/"migrated"/"archived"), or "missing" if the cell is gone from
    /// the ledger (a dangling surface — the shell tells the truth about it).
    pub lifecycle: &'static str,
    /// Whether this is the trusted system console (labelled distinctly so it is
    /// never confused with a cell-owned surface).
    pub is_console: bool,
    /// Whether the backing cell is actually present in the live ledger. A
    /// cell-view whose cell was destroyed/removed is `false` — the chrome shows
    /// it as a dangling/missing view rather than letting it masquerade as live.
    pub backed: bool,
}

/// One painted item in the composed scene: a surface plus its shell-derived
/// chrome (identity label, focus, z). The cockpit renders these back-to-front.
#[derive(Clone, Debug)]
pub struct SceneItem {
    pub surface: Surface,
    pub identity: IdentityLabel,
    /// Whether this surface currently holds focus (drawn with an active border).
    pub focused: bool,
}

/// The composed scene: the ordered (back-to-front) list of surfaces to paint,
/// plus the shell's current layout. Gpui-free — a pure description.
#[derive(Clone, Debug)]
pub struct Scene {
    pub items: Vec<SceneItem>,
    pub layout: Layout,
    /// The focused surface id, if any (also flagged per-item).
    pub focused: Option<SurfaceId>,
}

impl Scene {
    /// The front-most (top of z-order) surface in the scene, if any.
    pub fn front(&self) -> Option<&SceneItem> {
        self.items.last()
    }
}

/// The per-surface authority binding in the firmament fabric: the backing
/// surface-cell whose cap the window IS, and the owner holder whose c-list the
/// `granted ⊆ held` gate checks a presented cap against. Mints monotonically so
/// every surface gets a fresh, non-confusable backing cell + owner.
#[derive(Clone, Copy, Debug)]
struct SurfaceAuthority {
    /// The firmament cell that backs this surface — the cell a window cap's
    /// `Surface(cell)` target names. (Distinct from the surface's *viewed* cell,
    /// which is the identity anchor read from the live world ledger.)
    backing_cell: CellId,
    /// The owner holder whose installed grant over `backing_cell` the firmament's
    /// `invoke` checks a presented cap against (the surface's "owner" identity in
    /// the fabric — the cockpit acts as it).
    owner: CellId,
}

/// The cap-first window manager. Owns the surfaces, the z-order, the focus, the
/// layout, and the REAL firmament surface-fabric the window caps ride.
pub struct Shell {
    surfaces: Vec<Surface>,
    /// The REAL firmament surface-fabric: a `dregg_cell::Ledger` +
    /// `dregg_turn::TurnExecutor`. Every window cap is a
    /// `Capability{ Surface(backing_cell), rights }` resolved against THIS via
    /// the genuine `granted ⊆ held` gate; a window-SHARE is a genuine
    /// `Effect::GrantCapability` turn through its executor. The bearer-secret
    /// model is GONE (§7).
    fabric: SurfaceBacking,
    /// The per-surface authority registry: surface id → its backing cell + owner
    /// in the fabric. A presented cap authenticates iff its `surface` is here AND
    /// its authority targets that surface's `backing_cell` AND the firmament
    /// `invoke(owner, backing_cell, cap.rights)` succeeds. (Replaces the secret
    /// table — authority is now the real cap, not a guessable token.)
    authorities: Vec<(SurfaceId, SurfaceAuthority)>,
    /// The focused surface, if any.
    focus: Option<SurfaceId>,
    /// The current compositor layout.
    layout: Layout,
    /// Monotonic surface-id allocator.
    next_id: u64,
    /// A deterministic seed counter mixed into each surface's fresh backing-cell
    /// + owner derivation (so two surfaces opened in a session get distinct,
    ///   non-confusable backing cells without an RNG dependency).
    cell_seq: u8,
    /// Recipient apps seeded in the fabric for window-SHARES, keyed by a caller
    /// app id → its fabric cell. Seeded once so re-sharing to the same app reuses
    /// its cell (the firmament ledger inserts a cell exactly once).
    recipients: Vec<(u64, CellId)>,
    /// The shell's logical work-area size (for tile/stack arrangement).
    area: Rect,
    /// THE VERIFIED-SCENE COMPOSITOR: enforces the T1/T2/T3 scene-authority
    /// teeth (`docs/DREGG-DESKTOP-OS.md` §5; the Lean `Dregg2.Apps.Compositor`).
    /// The shell rebuilds its scene each present from the live surfaces + world
    /// ([`Shell::compose_scene`]) and routes every `present()` / input through
    /// it. This is a SEPARATE gate from the firmament cap-fabric above: the
    /// fabric decides who may DRIVE a window (focus/move/share); the compositor
    /// decides what a surface may PAINT and where input goes — a present can
    /// hold a valid window cap and STILL be refused for overpaint/spoof/misroute.
    compositor: Compositor,
    /// The per-surface content digest the compositor advances on a committed
    /// present (surface id → current frame digest). Seeded when a surface opens;
    /// the present path advances it, fail-closed on a refusal.
    frame_digests: Vec<(SurfaceId, u64)>,
    /// The MIGRATED surfaces: surface id → its re-homed cap (a
    /// `Capability{ Target::HostPd { pd }, rights }` the `migrate` verb minted).
    /// A surface here no longer paints through the in-process `compositor`; its
    /// `present`/`route_input` dispatch over the firmament Endpoint to the
    /// confined child PD ([`Shell::present_transport`]). The cap's `Target::HostPd`
    /// is the live-transport address the [`crate::dock::migrate::PresentTransport`]
    /// round-trips against. Populated only under the `process-pd` live wire
    /// ([`Shell::migrate_surface`]).
    #[cfg(all(feature = "process-pd", unix))]
    migrated: Vec<(SurfaceId, SurfaceCapability)>,
    /// THE LIVE-TRANSPORT re-home (`process-pd`): the firmament surface Endpoint(s)
    /// to the migrated surfaces' confined child PDs. Once a surface migrates
    /// ([`Shell::migrate_surface`]), the shell routes its `present`/`route_input`
    /// through this instead of the in-process compositor — the GLASS follows the
    /// cap to the child. `None` until the first surface migrates.
    #[cfg(all(feature = "process-pd", unix))]
    present_transport: Option<crate::dock::migrate::PresentTransport>,
}

impl Default for Shell {
    fn default() -> Self {
        Self::new()
    }
}

impl Shell {
    /// A fresh shell with no surfaces, floating layout, a default work area, and
    /// an empty single-machine (`n = 1`) firmament surface-fabric.
    pub fn new() -> Self {
        Shell {
            surfaces: Vec::new(),
            fabric: SurfaceBacking::new(),
            authorities: Vec::new(),
            focus: None,
            layout: Layout::Float,
            next_id: 1,
            cell_seq: 0,
            recipients: Vec::new(),
            area: Rect::new(0.0, 0.0, 1280.0, 760.0),
            compositor: Compositor::new(),
            frame_digests: Vec::new(),
            #[cfg(all(feature = "process-pd", unix))]
            migrated: Vec::new(),
            #[cfg(all(feature = "process-pd", unix))]
            present_transport: None,
        }
    }

    // --- opening / closing surfaces (the cap-MINTING + cap-gated paths) ------

    /// Open the privileged CONSOLE surface (the cockpit's own window). Returns
    /// its [`SurfaceCapability`] — the console is cap-owned like any surface
    /// (the operator holds its cap), it is just the trusted root that can't be
    /// closed. `cell` is the identity the console runs as (the operator cell).
    pub fn open_console(&mut self, cell: CellId, title: impl Into<String>) -> SurfaceCapability {
        let rect = Rect::new(0.0, 0.0, self.area.w, self.area.h);
        self.open_surface(SurfaceKind::Console, cell, title.into(), rect)
    }

    /// Open a cap-confined VIEW of `cell` as a new floating surface. Returns the
    /// [`SurfaceCapability`] the opener now holds — the ONLY authority over the
    /// new surface. The surface is raised to the front + focused on open.
    pub fn open_cell_view(&mut self, cell: CellId, title: impl Into<String>) -> SurfaceCapability {
        // Cascade fresh cell views so they don't all stack on the origin.
        let n = self.surfaces.iter().filter(|s| !s.is_console()).count() as f32;
        let rect = Rect::new(80.0 + n * 36.0, 80.0 + n * 36.0, 420.0, 300.0);
        self.open_surface(SurfaceKind::CellView, cell, title.into(), rect)
    }

    /// The single surface-creation path: allocate an id, seed a fresh backing
    /// surface-cell + owner in the REAL firmament fabric, install the owner's
    /// original (full-rights) grant over the backing cell, mint the REAL
    /// `Capability{ Surface(backing_cell), rights }` the opener now holds,
    /// install the surface at the top of the z-order, focus it, and hand back
    /// the cap. (Crate-internal — `open_console`/`open_cell_view` are the public
    /// doors.) Authority over the window is now exactly this firmament cap; the
    /// shell holds NO secret.
    fn open_surface(
        &mut self,
        kind: SurfaceKind,
        cell: CellId,
        title: String,
        rect: Rect,
    ) -> SurfaceCapability {
        let id = SurfaceId(self.next_id);
        self.next_id += 1;

        // Seed this surface's authority in the firmament fabric: a fresh backing
        // surface-cell + an owner holder, both at distinct deterministic seeds so
        // surfaces are never confusable. The owner is granted the FULL (widest,
        // `None`) authority over the backing cell — the original window cap, from
        // which any share is a strict narrowing through the real executor.
        let backing_seed = self.next_cell_seed();
        let backing_cell = self.fabric.seed_surface(backing_seed);
        let owner_seed = self.next_cell_seed();
        let owner = self.fabric.seed_surface(owner_seed);
        let full = AuthRequired::None;
        self.fabric.install(owner, backing_cell, full.clone());

        let z = self.top_z() + 1;
        let surface = Surface::new(id, kind, cell, title, rect, z);
        self.surfaces.push(surface);
        self.authorities.push((
            id,
            SurfaceAuthority {
                backing_cell,
                owner,
            },
        ));
        // Seed the compositor frame digest for this surface (the initial frame,
        // keyed off the surface id so it is non-trivial + distinct per surface).
        self.frame_digests.push((id, 0x100 + id.as_u64()));
        self.focus = Some(id);

        // The opener holds the REAL firmament cap over the backing surface-cell.
        SurfaceCapability::new(id, Capability::surface(backing_cell, full))
    }

    /// Close the surface the capability authorizes. Refuses if the cap doesn't
    /// authenticate, or if it names the console (the trusted root is protected).
    /// On success the surface + its firmament authority binding are dropped (the
    /// cap becomes dead — its backing-cell/owner are no longer registered, so it
    /// stops resolving), and focus moves to the new front-most surface.
    pub fn close(&mut self, cap: &SurfaceCapability) -> Result<(), ShellError> {
        let id = self.authorize(cap)?;
        if let Some(s) = self.get(id) {
            if s.is_console() {
                return Err(ShellError::ConsoleProtected);
            }
        }
        self.surfaces.retain(|s| s.id() != id);
        // Drop the surface's firmament authority binding — the cap is now dead
        // (no registered backing cell/owner ⇒ `invoke` has nothing to satisfy,
        // so the cap stops authenticating: a closed window's authority is gone).
        self.authorities.retain(|(sid, _)| *sid != id);
        // Drop its compositor frame digest (a closed surface paints no more).
        self.frame_digests.retain(|(sid, _)| *sid != id);
        if self.focus == Some(id) {
            self.focus = self.front_id();
        }
        Ok(())
    }

    // --- cap-gated window ops (each authenticates the cap FIRST) --------------

    /// Focus + raise the capability's surface to the front of the z-order. The
    /// canonical "click to bring forward" op — but it is the *cap*, not a click,
    /// that authorizes it.
    pub fn focus(&mut self, cap: &SurfaceCapability) -> Result<(), ShellError> {
        let id = self.authorize(cap)?;
        self.raise_to_front(id);
        self.focus = Some(id);
        Ok(())
    }

    /// Raise the capability's surface to the front WITHOUT changing focus
    /// (rarely needed alone; `focus` is the usual op). Cap-gated.
    pub fn raise(&mut self, cap: &SurfaceCapability) -> Result<(), ShellError> {
        let id = self.authorize(cap)?;
        self.raise_to_front(id);
        Ok(())
    }

    /// Move the capability's surface by `(dx, dy)` (honored under `Float`; under
    /// tile/stack the shell re-derives geometry, so a move is recorded but the
    /// arrangement overrides it until the layout returns to float). Cap-gated.
    pub fn move_by(&mut self, cap: &SurfaceCapability, dx: f32, dy: f32) -> Result<(), ShellError> {
        let id = self.authorize(cap)?;
        if let Some(s) = self.get_mut(id) {
            let r = s.rect().translated(dx, dy);
            s.set_rect(r);
        }
        Ok(())
    }

    /// Resize the capability's surface to `(w, h)` (clamped to a sane minimum).
    /// Cap-gated.
    pub fn resize(&mut self, cap: &SurfaceCapability, w: f32, h: f32) -> Result<(), ShellError> {
        let id = self.authorize(cap)?;
        if let Some(s) = self.get_mut(id) {
            let r = s.rect();
            s.set_rect(Rect::new(r.x, r.y, w.max(140.0), h.max(90.0)));
        }
        Ok(())
    }

    /// Minimize / restore the capability's surface (collapse out of the scene
    /// body but keep it owned + present). Cap-gated. Minimizing the focused
    /// surface moves focus to the new front.
    pub fn set_minimized(
        &mut self,
        cap: &SurfaceCapability,
        minimized: bool,
    ) -> Result<(), ShellError> {
        let id = self.authorize(cap)?;
        if let Some(s) = self.get_mut(id) {
            s.set_minimized(minimized);
        }
        if minimized && self.focus == Some(id) {
            self.focus = self.front_id();
        } else if !minimized {
            // Restoring raises + focuses it.
            self.raise_to_front(id);
            self.focus = Some(id);
        }
        Ok(())
    }

    /// Rename the capability's surface title. Cap-gated — only the owner may
    /// change the (operator-facing) title. (The IDENTITY label is shell-derived
    /// from the ledger and is NOT affected by this — anti-spoof.)
    pub fn set_title(
        &mut self,
        cap: &SurfaceCapability,
        title: impl Into<String>,
    ) -> Result<(), ShellError> {
        let id = self.authorize(cap)?;
        if let Some(s) = self.get_mut(id) {
            s.set_title(title.into());
        }
        Ok(())
    }

    /// SHARE the capability's window with another app — hand it an ATTENUATED
    /// surface cap through a GENUINE `Effect::GrantCapability` turn on the real
    /// executor. The presented `cap` is authenticated first (you can only share a
    /// window you hold); then the surface owner delegates `narrower` rights over
    /// the SAME backing cell to the recipient app (seeded once in the fabric,
    /// keyed by `recipient_app`).
    ///
    /// **A WIDENING share is REJECTED** — `narrower` must be `⊆` the rights the
    /// presented cap holds, else the real executor refuses it
    /// ([`ShellError::ShareDenied`], the `DelegationDenied` surfaced). This is
    /// the no-amplification guarantee firing at the window-manager layer: a
    /// surface cannot hand out more authority over the glass than it carries —
    /// byte-for-byte the executor's deployed attenuation semantics, mirroring the
    /// firmament's own `real_executor_rejects_widening_surface_share`.
    ///
    /// On success the shared window becomes a NEW surface (a fresh
    /// [`SurfaceId`]) over the SAME backing authority cell, owned in the fabric
    /// by the recipient at the narrowed rights; the returned
    /// [`SurfaceCapability`] is the recipient's handle to it. A NARROWING share
    /// COMMITS; a widening one is refused and changes nothing.
    pub fn share(
        &mut self,
        cap: &SurfaceCapability,
        recipient_app: u64,
        narrower: AuthRequired,
    ) -> Result<SurfaceCapability, ShellError> {
        // You can only share a window you actually hold (cap-gated like every op).
        let id = self.authorize(cap)?;
        let auth = self
            .authorities
            .iter()
            .find(|(sid, _)| *sid == id)
            .map(|(_, a)| *a)
            .ok_or(ShellError::Unauthorized)?;

        // Resolve (seed once) the recipient app's cell in the fabric.
        let recipient = self.recipient_cell(recipient_app);

        // The REAL delegating turn: owner --GrantCapability(narrower)--> recipient.
        // The executor enforces `granted ⊆ held`; a WIDENING share is rejected
        // here (DelegationDenied), and nothing is granted.
        self.fabric
            .delegate(auth.owner, recipient, auth.backing_cell, narrower.clone())
            .map_err(|e| match e {
                ResolveError::BackingRejected(why) => ShellError::ShareDenied(why),
                ResolveError::Unauthorized(why) => ShellError::ShareDenied(why),
                ResolveError::TargetNotFound => {
                    ShellError::ShareDenied("share target not found in the fabric".to_string())
                }
            })?;

        // The share landed: register a NEW surface (over the SAME backing cell,
        // owned by the recipient) and hand back the recipient's narrowed cap.
        let new_id = SurfaceId(self.next_id);
        self.next_id += 1;
        let view_cell = self.get(id).map(|s| s.cell()).unwrap_or(auth.backing_cell);
        let kind = SurfaceKind::CellView; // a shared window is a cap-confined view
        let z = self.top_z() + 1;
        let n = self.surfaces.iter().filter(|s| !s.is_console()).count() as f32;
        let rect = Rect::new(100.0 + n * 28.0, 100.0 + n * 28.0, 420.0, 300.0);
        let surface = Surface::new(
            new_id,
            kind,
            view_cell,
            format!("shared s{}", id.as_u64()),
            rect,
            z,
        );
        self.surfaces.push(surface);
        self.authorities.push((
            new_id,
            SurfaceAuthority {
                backing_cell: auth.backing_cell,
                owner: recipient,
            },
        ));
        self.frame_digests.push((new_id, 0x100 + new_id.as_u64()));
        Ok(SurfaceCapability::new(
            new_id,
            Capability::surface(auth.backing_cell, narrower),
        ))
    }

    // --- layout (a shell-global op; not surface-scoped) ----------------------

    /// Set the compositor layout (float/tile/stack). This is a shell-wide op the
    /// operator (console) drives, not a per-surface one, so it is not cap-gated
    /// on an individual surface — it rearranges the whole scene.
    pub fn set_layout(&mut self, layout: Layout) {
        self.layout = layout;
    }

    pub fn layout(&self) -> Layout {
        self.layout
    }

    /// Cycle the layout float → tile → stack → float (the console's "rearrange"
    /// affordance / a palette command).
    pub fn cycle_layout(&mut self) {
        self.layout = match self.layout {
            Layout::Float => Layout::Tile,
            Layout::Tile => Layout::Stack,
            Layout::Stack => Layout::Float,
        };
    }

    /// Set the shell's logical work-area size (the cockpit calls this with the
    /// window size so tile/stack arrange to fit).
    pub fn set_area(&mut self, w: f32, h: f32) {
        self.area = Rect::new(0.0, 0.0, w.max(320.0), h.max(240.0));
    }

    // --- read surface --------------------------------------------------------

    /// The number of surfaces currently open (including the console).
    pub fn surface_count(&self) -> usize {
        self.surfaces.len()
    }

    /// The focused surface id, if any.
    pub fn focused(&self) -> Option<SurfaceId> {
        self.focus
    }

    /// The CELL owning the focused surface, if any — the unique focus holder of
    /// the verified scene (T3: input routes only here). Used by the cockpit to
    /// pick a genuinely-distinct foreign surface for the overpaint teaching moment.
    pub fn focused_cell(&self) -> Option<CellId> {
        self.focus.and_then(|id| self.get(id).map(|s| s.cell()))
    }

    /// Whether the capability still authenticates (its surface is live + the
    /// firmament `granted ⊆ held` gate admits it). Lets a holder check liveness
    /// without performing an op.
    pub fn validates(&self, cap: &SurfaceCapability) -> bool {
        self.authorize(cap).is_ok()
    }

    /// All open surfaces in z-order (back-to-front). Read-only.
    pub fn surfaces_in_z_order(&self) -> Vec<&Surface> {
        let mut v: Vec<&Surface> = self.surfaces.iter().collect();
        v.sort_by_key(|s| s.z());
        v
    }

    /// Compose the [`Scene`] to paint, reading the live `World` for each
    /// surface's trusted-path identity chrome + (under tile/stack) arranging the
    /// geometry. Back-to-front order; the front-most is last. This is the
    /// COMPOSITOR: it turns the owned-surface set + the live ledger into an
    /// ordered paint list.
    pub fn compose(&self, world: &World) -> Scene {
        // Order by z (back-to-front).
        let mut ordered: Vec<&Surface> = self.surfaces.iter().collect();
        ordered.sort_by_key(|s| s.z());

        // Geometry per layout. Float honors each surface's own rect; tile/stack
        // arrange the NON-console surfaces (the console keeps its anchored rect).
        let tiled = self.arranged_rects(&ordered);

        let items = ordered
            .iter()
            .enumerate()
            .map(|(i, s)| {
                let rect = tiled.get(i).copied().unwrap_or_else(|| s.rect());
                let mut surface = (*s).clone();
                surface.set_rect(rect);
                let identity = self.identity_of(s, world);
                SceneItem {
                    surface,
                    identity,
                    focused: self.focus == Some(s.id()),
                }
            })
            .collect();

        Scene {
            items,
            layout: self.layout,
            focused: self.focus,
        }
    }

    /// Hit-test: the front-most non-minimized surface containing the point, if
    /// any (the cockpit uses this to translate a click in the scene into a
    /// focus, but only the CAP it then looks up authorizes the focus — the click
    /// is a hint, the cap is the authority).
    pub fn hit_test(&self, px: f32, py: f32, world: &World) -> Option<SurfaceId> {
        let scene = self.compose(world);
        // Front-to-back: the topmost hit wins.
        scene
            .items
            .iter()
            .rev()
            .find(|it| !it.surface.is_minimized() && it.surface.rect().contains(px, py))
            .map(|it| it.surface.id())
    }

    // --- THE VERIFIED-SCENE COMPOSITOR (T1/T2/T3 enforcement) ----------------
    //
    // The shell rebuilds the compositor's scene from its live surfaces + the
    // world (region ownership, focus, the shell-drawn label), then routes
    // `present()` and input through it. This is the Rust realization of the Lean
    // `Dregg2.Apps.Compositor` discipline (§5): a SEPARATE gate from the window-
    // cap fabric, enforcing what a surface may PAINT + where input goes.

    /// Build the compositor's verified scene from the shell's live surfaces and
    /// the world. Each surface owns exactly its cap-authorized region (the §5 T1
    /// region-set, derived from its [`SurfaceId`] so two surfaces own DISJOINT
    /// regions). The focus flag is the shell's single focus (T3: at-most-one by
    /// construction). The source-state-root + the genuine label are drawn from
    /// the SHELL's view of the live world (the §5 T2 binding — NEVER the
    /// surface's self-description). Minimized surfaces are excluded (they paint
    /// nothing). This is the closed-over scene the §4 `sceneAdmit` decides over.
    pub fn compose_scene(&self, world: &World) -> CompositorScene {
        let mut ordered: Vec<&Surface> =
            self.surfaces.iter().filter(|s| !s.is_minimized()).collect();
        ordered.sort_by_key(|s| s.z());
        let surfaces = ordered
            .iter()
            .map(|s| {
                let root = self.source_state_root(s.cell(), world);
                CompositedSurface {
                    owner: s.cell(),
                    regions: vec![s.id().region()],
                    content_digest: self.frame_digest(s.id()),
                    source_state_root: root,
                    z_layer: s.z() as i64,
                    focus_flag: self.focus == Some(s.id()),
                }
            })
            .collect();
        CompositorScene { surfaces }
    }

    /// PRESENT through the verified scene: a cap-gated frame advance for the
    /// capability's surface, enforcing the T1/T2/T3 scene-authority teeth.
    ///
    /// Two gates fire, in order (§5 "the scene authority is a SEPARATE gate the
    /// executor enforces on top" of the surface cap):
    ///   1. THE WINDOW-CAP GATE ([`Self::authorize`]) — the presented cap must
    ///      authenticate through the firmament's `granted ⊆ held` (you can only
    ///      present a window you hold).
    ///   2. THE SCENE-AUTHORITY GATE ([`Compositor::scene_admit`]) — T1 (the
    ///      target region-set ⊆ the surface's owned region, disjoint from foreign
    ///      surfaces), T2 (the declared label is the genuine owner-binding the
    ///      SHELL computes), T3 (input routes only to the focus holder; the scene
    ///      is focus-exclusive). A present that holds a valid window cap and
    ///      OVERPAINTS / SPOOFS / STEALS-FOCUS is still REFUSED here.
    ///
    /// On success the compositor advances the surface's frame digest (recorded
    /// in its frame log — the scene's provenance) and the shell mirrors it; a
    /// refusal changes NOTHING (fail-closed, the Lean `present_*_rejected`
    /// polarity). The cockpit surfaces the refused tooth as a teaching moment.
    pub fn present(
        &mut self,
        cap: &SurfaceCapability,
        world: &World,
        regions: Vec<crate::compositor::RegionId>,
        claims_focus: bool,
        new_digest: u64,
    ) -> Result<FrameCommit, ShellError> {
        // (0) the GLASS-FOLLOWS-THE-CAP fork: if this surface MIGRATED to a
        // confined child PD, the present does NOT go to the in-process compositor
        // — it crosses the firmament Endpoint to the child, which renders in its
        // own MMU-isolated memory and returns the frame (the digest folds into the
        // shell's bookkeeping below). The in-process path is untouched for every
        // non-migrated surface. (The registry is only ever populated under the
        // `process-pd` live wire — `migrate_surface` is gated on it.)
        #[cfg(all(feature = "process-pd", unix))]
        if self.is_migrated(cap.surface()) {
            return self.present_migrated(cap, world, regions, new_digest);
        }

        // (1) the WINDOW-cap gate: you can only present a window you hold.
        let id = self.authorize(cap)?;
        let Some(surface) = self.get(id) else {
            return Err(ShellError::Unauthorized);
        };
        let presenter = surface.cell();
        let source_state_root = self.source_state_root(presenter, world);
        // The genuine label the compositor binds (the §5 T2 binding — a function
        // of the owner + the source-state-root, computed by the SHELL).
        let declared_label = label_of(&presenter, source_state_root);

        // (2) the SCENE-authority gate: rebuild the scene + fold in T1/T2/T3.
        // (Compose into a local first so the immutable borrow of `self` ends
        // before the mutable borrow of `self.compositor`.)
        let scene = self.compose_scene(world);
        self.compositor.set_scene(scene);
        let present = Present {
            target: regions,
            source_state_root,
            declared_label,
            claims_focus,
            new_digest,
        };
        let commit = self
            .compositor
            .present(&presenter, present)
            .map_err(ShellError::PresentRefused)?;
        // Mirror the advanced frame digest into the shell's per-surface table
        // (the compositor advanced its own scene copy; keep the shell in step).
        self.set_frame_digest(id, new_digest);
        Ok(commit)
    }

    /// Route an input event to the focus holder through the verified scene's T3
    /// gate: input is delivered ONLY to the cell the user demonstrably chose (the
    /// focus holder). `claimed` is the cell some component believes should
    /// receive the event; the gate confirms it against the unique focus holder,
    /// refusing a misroute. Returns the (single) cell input is delivered to.
    pub fn route_input(&mut self, claimed: CellId, world: &World) -> Result<CellId, ShellError> {
        // (0) the GLASS-FOLLOWS-THE-CAP fork: if the input is for a surface that
        // MIGRATED to a confined child PD, it crosses the firmament Endpoint to the
        // child (which folds it into its private surface state and re-renders),
        // NOT the in-process compositor's focus gate. The claimed cell still has to
        // be the unique focus holder — the T3 routing law is enforced first below,
        // then (if it names a migrated surface) the event is delivered over the
        // child's Endpoint.
        let scene = self.compose_scene(world);
        self.compositor.set_scene(scene);
        let delivered = self
            .compositor
            .route_input(&claimed)
            .map_err(ShellError::PresentRefused)?;
        // The compositor confirmed `claimed` is the focus holder. If that focus
        // holder's surface is migrated, deliver the input over the child's Endpoint
        // (the glass + the input both flow through the confined child now).
        #[cfg(all(feature = "process-pd", unix))]
        if let Some(id) = self.migrated_surface_for_cell(delivered) {
            let cap = self.migrated_cap(id).ok_or(ShellError::Unauthorized)?;
            let _frame = self.route_input_migrated(&cap)?;
        }
        Ok(delivered)
    }

    // --- SURFACE MIGRATION dispatch (the glass-follows-the-cap re-home) -------
    //
    // `migrate(surface_cap, HostPd{pd})` (dock/migrate.rs) re-mints the surface's
    // cap onto a confined child PD; these methods make the SHELL route that
    // surface's present/route_input over the child's firmament Endpoint instead of
    // the in-process compositor. The migration registry + the lookups are
    // unconditional (gpui-free); only the live dispatch needs the `process-pd`
    // wire.

    /// Whether a surface has MIGRATED to a confined child PD (its present/input now
    /// dispatch over the firmament Endpoint, not the in-process compositor).
    #[cfg(all(feature = "process-pd", unix))]
    fn is_migrated(&self, id: SurfaceId) -> bool {
        self.migrated.iter().any(|(sid, _)| *sid == id)
    }

    /// The re-homed (`Target::HostPd`) cap recorded for a migrated surface, if any.
    #[cfg(all(feature = "process-pd", unix))]
    fn migrated_cap(&self, id: SurfaceId) -> Option<SurfaceCapability> {
        self.migrated
            .iter()
            .find(|(sid, _)| *sid == id)
            .map(|(_, c)| c.clone())
    }

    /// The migrated surface (if any) owning `cell` — the bridge from
    /// `route_input`'s claimed CellId to a re-homed surface. A migrated surface
    /// keeps its viewed-cell identity (migration relocates transport, not the
    /// cell), so the focus holder's cell maps back to its surface here.
    #[cfg(all(feature = "process-pd", unix))]
    fn migrated_surface_for_cell(&self, cell: CellId) -> Option<SurfaceId> {
        self.migrated
            .iter()
            .find_map(|(sid, _)| self.get(*sid).filter(|s| s.cell() == cell).map(|_| *sid))
    }

    /// MIGRATE a held surface to a confined child PD and bind its live transport —
    /// the full glass-follows-the-cap move through the SHELL. This re-mints the
    /// surface's cap onto `target` (the attenuating `migrate` verb, which refuses a
    /// widening), records the surface as migrated, and installs the
    /// [`PresentTransport`](crate::dock::migrate::PresentTransport) (the firmament
    /// surface Endpoint to the child whose surface socket has been registered).
    /// Thereafter [`Shell::present`]/[`Shell::route_input`] for this surface
    /// dispatch over that Endpoint — the in-process compositor never sees it again.
    ///
    /// Returns the re-homed [`SurfaceCapability`] (the cap now naming
    /// `Target::HostPd { pd }`). The presented `cap` is authenticated FIRST (you
    /// can only migrate a window you hold) through the same firmament gate every
    /// op runs.
    #[cfg(all(feature = "process-pd", unix))]
    pub fn migrate_surface(
        &mut self,
        cap: &SurfaceCapability,
        target: crate::dock::migrate::MigrationTarget,
        transport: crate::dock::migrate::PresentTransport,
    ) -> Result<SurfaceCapability, ShellError> {
        // You can only migrate a window you actually hold (cap-gated like every op).
        let id = self.authorize(cap)?;
        // The attenuating re-mint (refuses a widening migration — `granted ⊆ held`).
        let rehomed = crate::dock::migrate::migrate(cap, &target)
            .map_err(|e| ShellError::ShareDenied(e.to_string()))?;
        // Record the surface as migrated + install the live transport. From now on
        // its present/input cross the child's Endpoint.
        self.migrated.retain(|(sid, _)| *sid != id);
        self.migrated.push((id, rehomed.clone()));
        self.present_transport = Some(transport);
        Ok(rehomed)
    }

    /// PRESENT a migrated surface over the child PD's firmament Endpoint (the
    /// `process-pd` live transport). The confined child renders the frame; its
    /// digest folds into the shell's `frame_digests` + a [`FrameCommit`] (so the
    /// migrated frame is recorded in the shell's bookkeeping exactly like an
    /// in-process one). The cap's rights gate the round-trip through the SAME
    /// `granted ⊆ held` law (the host backing's `present_over_endpoint`).
    #[cfg(all(feature = "process-pd", unix))]
    fn present_migrated(
        &mut self,
        cap: &SurfaceCapability,
        world: &World,
        _regions: Vec<crate::compositor::RegionId>,
        new_digest: u64,
    ) -> Result<FrameCommit, ShellError> {
        let id = cap.surface();
        // The re-homed cap (Target::HostPd) the transport addresses. We dispatch
        // against the RECORDED cap (the migration authority), not the presented one
        // — they share the SurfaceId, and the recorded cap carries the live target.
        let rehomed = self.migrated_cap(id).ok_or(ShellError::Unauthorized)?;
        // The present sequence is the new digest's low bits (a monotone-ish seq the
        // child echoes; the child's returned digest is the load-bearing frame id).
        let seq = new_digest;
        let frame = {
            let transport = self
                .present_transport
                .as_ref()
                .ok_or(ShellError::Unauthorized)?;
            transport
                .present(&rehomed, seq)
                .map_err(|e| ShellError::ShareDenied(format!("{e:?}")))?
        };
        Ok(self.commit_migrated_frame(id, world, frame.digest))
    }

    /// ROUTE an input to a migrated surface over the child PD's Endpoint — the
    /// child folds it into its private surface state and re-renders. The returned
    /// frame's digest folds into the shell's bookkeeping (the input AND the glass
    /// both flow through the confined child now).
    #[cfg(all(feature = "process-pd", unix))]
    fn route_input_migrated(&mut self, cap: &SurfaceCapability) -> Result<FrameCommit, ShellError> {
        let id = cap.surface();
        let rehomed = self.migrated_cap(id).ok_or(ShellError::Unauthorized)?;
        // The input code: the surface id (a stable, surface-scoped event code for
        // the e2e — the real cockpit threads the actual keystroke/pointer code).
        let code = id.as_u64();
        let frame = {
            let transport = self
                .present_transport
                .as_ref()
                .ok_or(ShellError::Unauthorized)?;
            transport
                .route_input(&rehomed, code)
                .map_err(|e| ShellError::ShareDenied(format!("{e:?}")))?
        };
        // Fold the child's re-rendered frame into the shell (no world needed — an
        // input re-render keeps the surface's source-state binding).
        Ok(self.commit_migrated_frame_digest(id, frame.digest))
    }

    /// Fold a CONFINED-CHILD frame digest into the shell's bookkeeping: advance the
    /// per-surface `frame_digests` and synthesize a [`FrameCommit`] bound to the
    /// surface's live source-state-root + genuine label (so a migrated frame is
    /// recorded with the SAME provenance shape as an in-process present). Used by
    /// the `present` path (it has the world for the live root).
    #[cfg(all(feature = "process-pd", unix))]
    fn commit_migrated_frame(&mut self, id: SurfaceId, world: &World, digest: u64) -> FrameCommit {
        let (presenter, root) = match self.get(id) {
            Some(s) => {
                let cell = s.cell();
                (cell, self.source_state_root(cell, world))
            }
            None => (CellId::from_bytes([0u8; 32]), 0xDEAD_0000_DEAD_0000),
        };
        self.set_frame_digest(id, digest);
        FrameCommit {
            presenter,
            regions: vec![id.region()],
            digest,
            source_state_root: root,
            label: label_of(&presenter, root),
        }
    }

    /// Like [`Self::commit_migrated_frame`] but without re-reading the world (the
    /// input re-render path): advance the digest + record a FrameCommit bound to
    /// the surface's presenter cell at the digest's own root sentinel. The
    /// load-bearing fact is the child's digest crossing back into the shell.
    #[cfg(all(feature = "process-pd", unix))]
    fn commit_migrated_frame_digest(&mut self, id: SurfaceId, digest: u64) -> FrameCommit {
        let presenter = self
            .get(id)
            .map(|s| s.cell())
            .unwrap_or_else(|| CellId::from_bytes([0u8; 32]));
        self.set_frame_digest(id, digest);
        FrameCommit {
            presenter,
            regions: vec![id.region()],
            digest,
            source_state_root: digest,
            label: label_of(&presenter, digest),
        }
    }

    /// The compositor's committed frame log (the scene's provenance — every
    /// genuine present that advanced a frame). Read-only.
    pub fn frame_log(&self) -> &[FrameCommit] {
        self.compositor.frames()
    }

    // --- internals -----------------------------------------------------------

    /// Authenticate a presented capability through the REAL firmament gate. The
    /// cap must (1) name a live surface, (2) carry an authority whose
    /// `Surface(cell)` target IS that surface's registered backing cell (no cap
    /// confusion — a cap for another window, or one targeting the wrong cell, is
    /// refused), and (3) RESOLVE through the firmament's
    /// [`SurfaceBacking::invoke`] — the genuine `granted ⊆ held`
    /// ([`dregg_firmament::is_attenuation`]) check against the surface owner's
    /// installed grant. Returns the authorized surface id, or
    /// [`ShellError::Unauthorized`]. THIS is the ocap check at the heart of the
    /// cap-first window manager — every op routes through it, and it is now the
    /// SAME gate every other firmament cap uses, not a secret match.
    fn authorize(&self, cap: &SurfaceCapability) -> Result<SurfaceId, ShellError> {
        // (1) the surface must be live + registered.
        let auth = self
            .authorities
            .iter()
            .find(|(sid, _)| *sid == cap.surface())
            .map(|(_, a)| a)
            .ok_or(ShellError::Unauthorized)?;
        // (2) anti cap-confusion: the cap's authority must target THIS surface's
        // backing cell (a cap minted for another window is refused here).
        if cap.backing_cell() != Some(auth.backing_cell) {
            return Err(ShellError::Unauthorized);
        }
        // (3) the REAL `granted ⊆ held` resolution: invoke the owner's grant over
        // the backing cell at the presented rights. A cap whose rights exceed the
        // owner-grant (or a fabricated cap the fabric never granted) is refused by
        // the genuine is_attenuation gate — exactly the no-amplification rule the
        // local/distributed backings enforce.
        self.fabric
            .invoke(auth.owner, auth.backing_cell, cap.rights())
            .map_err(|_| ShellError::Unauthorized)?;
        Ok(cap.surface())
    }

    /// The source state-root a surface's content projects — the §5 T2 bind a
    /// light client can independently check. Drawn from the SHELL's view of the
    /// live world (the owning cell's real state: balance ⊕ nonce ⊕ cap-count ⊕
    /// lifecycle-tag), NOT the surface's self-description. A missing cell folds
    /// to a distinct sentinel root (a dangling surface projects nothing real).
    /// This is the value the genuine label binds to ([`label_of`]); it advances
    /// as the cell's state changes (a turn that moves balance moves the root, so
    /// the label re-binds — exactly the state-root binding §5 wants).
    fn source_state_root(&self, cell: CellId, world: &World) -> u64 {
        match world.ledger().get(&cell) {
            Some(c) => {
                let bal = c.state.balance() as u64;
                let nonce = c.state.nonce();
                let caps = c.capabilities.len() as u64;
                let life = match &c.lifecycle {
                    CellLifecycle::Live => 1u64,
                    CellLifecycle::Sealed { .. } => 2,
                    CellLifecycle::Destroyed { .. } => 3,
                    CellLifecycle::Migrated { .. } => 4,
                    CellLifecycle::Archived { .. } => 5,
                };
                // A simple deterministic fold (a state digest — distinct states
                // give distinct roots for the executable model; the real
                // compositor commits the cell's authenticated root).
                bal.wrapping_mul(0x9E37_79B9_7F4A_7C15)
                    ^ nonce.wrapping_mul(0xBF58_476D_1CE4_E5B9)
                    ^ caps.wrapping_mul(0x94D0_49BB_1331_11EB)
                    ^ life.wrapping_mul(0xD6E8_FEB8_6659_FD93)
            }
            // A dangling surface (cell gone): a distinct sentinel so its label
            // can never collide with a live cell's binding.
            None => 0xDEAD_0000_DEAD_0000,
        }
    }

    /// The current compositor frame digest for a surface (0 if unknown).
    fn frame_digest(&self, id: SurfaceId) -> u64 {
        self.frame_digests
            .iter()
            .find(|(sid, _)| *sid == id)
            .map(|(_, d)| *d)
            .unwrap_or(0)
    }

    /// Mirror an advanced frame digest into the shell's per-surface table after
    /// a committed present (keeps the shell in step with the compositor scene).
    fn set_frame_digest(&mut self, id: SurfaceId, digest: u64) {
        if let Some((_, d)) = self.frame_digests.iter_mut().find(|(sid, _)| *sid == id) {
            *d = digest;
        } else {
            self.frame_digests.push((id, digest));
        }
    }

    /// Derive a surface's trusted-path identity from the LIVE ledger (anti-spoof
    /// chrome). The console is labelled as the trusted root; a cell-view's badge
    /// reflects the backing cell's real lifecycle (or "missing" if it's gone).
    fn identity_of(&self, s: &Surface, world: &World) -> IdentityLabel {
        let cell = s.cell();
        let short = crate::reflect::short_hex(cell.as_bytes());
        let backed = world.ledger().contains(&cell);
        let lifecycle = if s.is_console() {
            "system"
        } else {
            match world.ledger().get(&cell).map(|c| &c.lifecycle) {
                Some(CellLifecycle::Live) => "live",
                Some(CellLifecycle::Sealed { .. }) => "sealed",
                Some(CellLifecycle::Destroyed { .. }) => "destroyed",
                Some(CellLifecycle::Migrated { .. }) => "migrated",
                Some(CellLifecycle::Archived { .. }) => "archived",
                None => "missing",
            }
        };
        IdentityLabel {
            cell,
            short,
            lifecycle,
            is_console: s.is_console(),
            backed,
        }
    }

    /// Compute the per-surface rects for the current layout, in the SAME order
    /// as `ordered`. Float → each surface's own rect; tile → a grid of the
    /// non-console surfaces in the work area; stack → a centered cascade.
    fn arranged_rects(&self, ordered: &[&Surface]) -> Vec<Rect> {
        match self.layout {
            Layout::Float => ordered.iter().map(|s| s.rect()).collect(),
            Layout::Tile => self.tile_rects(ordered),
            Layout::Stack => self.stack_rects(ordered),
        }
    }

    fn tile_rects(&self, ordered: &[&Surface]) -> Vec<Rect> {
        // Tiles only the non-console, non-minimized surfaces; the console keeps
        // its anchored rect; minimized surfaces keep their own rect (they're not
        // painted in the body anyway).
        let tileable: Vec<usize> = ordered
            .iter()
            .enumerate()
            .filter(|(_, s)| !s.is_console() && !s.is_minimized())
            .map(|(i, _)| i)
            .collect();
        let n = tileable.len().max(1);
        // A near-square grid.
        let cols = (n as f32).sqrt().ceil() as usize;
        let rows = n.div_ceil(cols);
        let pad = 8.0;
        let cw = (self.area.w - pad * (cols as f32 + 1.0)) / cols as f32;
        let ch = (self.area.h - pad * (rows as f32 + 1.0)) / rows as f32;

        let mut out: Vec<Rect> = ordered.iter().map(|s| s.rect()).collect();
        for (k, &idx) in tileable.iter().enumerate() {
            let col = k % cols;
            let row = k / cols;
            let x = pad + col as f32 * (cw + pad);
            let y = pad + row as f32 * (ch + pad);
            out[idx] = Rect::new(x, y, cw.max(140.0), ch.max(90.0));
        }
        out
    }

    fn stack_rects(&self, ordered: &[&Surface]) -> Vec<Rect> {
        let mut out: Vec<Rect> = ordered.iter().map(|s| s.rect()).collect();
        let w = (self.area.w * 0.6).max(360.0);
        let h = (self.area.h * 0.6).max(260.0);
        let base_x = (self.area.w - w) / 2.0;
        let base_y = (self.area.h - h) / 2.0;
        let mut k = 0.0;
        for (idx, s) in ordered.iter().enumerate() {
            if s.is_console() || s.is_minimized() {
                continue;
            }
            let off = k * 28.0;
            out[idx] = Rect::new(base_x + off, base_y + off, w, h);
            k += 1.0;
        }
        out
    }

    /// Advance the deterministic seed counter for a fresh firmament backing /
    /// owner cell (each surface consumes two: its backing cell + its owner). The
    /// distinct seeds keep surface cells non-confusable within the session; the
    /// real unforgeability barrier is the firmament's `granted ⊆ held` gate, not
    /// a hidden token.
    fn next_cell_seed(&mut self) -> u8 {
        let s = self.cell_seq;
        self.cell_seq = self.cell_seq.wrapping_add(1);
        s
    }

    /// Resolve a recipient app id to its fabric cell, seeding it ONCE (the
    /// firmament ledger inserts a cell exactly once, so re-sharing to the same
    /// app reuses its existing cell rather than re-seeding).
    fn recipient_cell(&mut self, recipient_app: u64) -> CellId {
        if let Some((_, c)) = self.recipients.iter().find(|(k, _)| *k == recipient_app) {
            return *c;
        }
        let seed = self.next_cell_seed();
        let cell = self.fabric.seed_surface(seed);
        self.recipients.push((recipient_app, cell));
        cell
    }

    fn top_z(&self) -> u32 {
        self.surfaces.iter().map(|s| s.z()).max().unwrap_or(0)
    }

    /// The id of the front-most (highest z) surface that is ELIGIBLE for focus —
    /// i.e. not minimized. (A minimized surface is collapsed out of the body and
    /// must not become the focus target; focus falls through to the next visible
    /// surface, and to the console if nothing else remains.)
    fn front_id(&self) -> Option<SurfaceId> {
        self.surfaces
            .iter()
            .filter(|s| !s.is_minimized())
            .max_by_key(|s| s.z())
            .map(|s| s.id())
    }

    /// Raise a surface to the front by giving it `top_z + 1` (keeps the relative
    /// order of the rest). Idempotent if it is already on top.
    fn raise_to_front(&mut self, id: SurfaceId) {
        let top = self.top_z();
        if let Some(s) = self.get_mut(id) {
            if s.z() <= top {
                s.set_z(top + 1);
            }
        }
    }

    fn get(&self, id: SurfaceId) -> Option<&Surface> {
        self.surfaces.iter().find(|s| s.id() == id)
    }

    fn get_mut(&mut self, id: SurfaceId) -> Option<&mut Surface> {
        self.surfaces.iter_mut().find(|s| s.id() == id)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::world::demo_world;

    // A small helper: a fresh shell over the demo world + a console.
    fn shell_with_console() -> (Shell, World, [CellId; 3], SurfaceCapability) {
        let (world, anchors) = demo_world();
        let mut shell = Shell::new();
        let console_cap = shell.open_console(anchors[0], "Console");
        (shell, world, anchors, console_cap)
    }

    #[test]
    fn opening_a_surface_mints_an_authorizing_cap() {
        let (mut shell, world, anchors, _console) = shell_with_console();
        let [_treasury, service, _user] = anchors;
        let cap = shell.open_cell_view(service, "Service");
        // The cap authenticates; a window op succeeds.
        assert!(shell.validates(&cap));
        assert!(shell.focus(&cap).is_ok());
        // It is backed by the real service cell.
        let scene = shell.compose(&world);
        let item = scene
            .items
            .iter()
            .find(|it| it.surface.cell() == service)
            .unwrap();
        assert!(
            item.identity.backed,
            "the cell-view is backed by a real ledger cell"
        );
        assert_eq!(item.identity.lifecycle, "live");
    }

    #[test]
    fn a_forged_capability_is_refused_every_op() {
        // The ocap heart: an op presented with a cap the firmament never granted
        // is refused by the REAL `granted ⊆ held` gate. Naming the SurfaceId is
        // NOT enough — the cap's authority must target the surface's actual
        // backing cell AND resolve against the owner's installed grant.
        use dregg_firmament::{AuthRequired, Capability, CellId as FCellId, Target};
        let (mut shell, _world, anchors, _console) = shell_with_console();
        let real = shell.open_cell_view(anchors[1], "Service");

        // Forge a cap for the SAME surface id but an authority over a DIFFERENT
        // (attacker-chosen) backing cell — anti cap-confusion refuses it (the
        // cap's Surface(cell) target ≠ the surface's registered backing cell).
        let ghost_cell = {
            let mut k = [0u8; 32];
            k[0] = 0xEE;
            FCellId::derive_raw(&k, &[0u8; 32])
        };
        let forged = SurfaceCapability::new(
            real.surface(),
            Capability::surface(ghost_cell, AuthRequired::None),
        );
        assert!(!shell.validates(&forged));
        assert_eq!(shell.focus(&forged), Err(ShellError::Unauthorized));
        assert_eq!(
            shell.move_by(&forged, 10.0, 10.0),
            Err(ShellError::Unauthorized)
        );
        assert_eq!(shell.close(&forged), Err(ShellError::Unauthorized));

        // A cap for a surface that doesn't exist is likewise refused.
        let nobody = SurfaceCapability::new(
            SurfaceId(9999),
            Capability::surface(ghost_cell, AuthRequired::None),
        );
        assert_eq!(shell.focus(&nobody), Err(ShellError::Unauthorized));

        // A non-surface authority (e.g. a Local target) over the right surface id
        // is also refused — it carries no backing surface cell to bind.
        let mislabeled =
            SurfaceCapability::new(real.surface(), Capability::local(0, AuthRequired::None));
        assert!(matches!(
            mislabeled.authority().target,
            Target::Local { .. }
        ));
        assert_eq!(shell.focus(&mislabeled), Err(ShellError::Unauthorized));

        // The REAL cap still works — the gate refuses forgeries, not the holder.
        assert!(shell.validates(&real));
    }

    #[test]
    fn a_narrowing_window_share_commits_and_a_widening_share_rejects() {
        // THE no-amplification guarantee firing at the desktop. A window-SHARE is
        // a REAL `Effect::GrantCapability` turn on the firmament executor; it
        // commits iff attenuating and is REJECTED (DelegationDenied) when
        // widening — mirroring the firmament's own
        // `real_executor_rejects_widening_surface_share`, now at the
        // window-manager layer.
        use dregg_firmament::AuthRequired;
        let (mut shell, _world, anchors, _console) = shell_with_console();

        // App A opens a window — it holds the FULL (widest, None) surface cap.
        let a = shell.open_cell_view(anchors[1], "Service");
        assert_eq!(a.rights(), &AuthRequired::None);

        // A shares a READ-ONLY MIRROR (None -> Signature, a strict narrowing)
        // with app B. This COMMITS through the real executor; B gets a real,
        // narrowed window cap, and the share opened B a new surface.
        let b = shell
            .share(&a, /*recipient app*/ 0xB, AuthRequired::Signature)
            .expect("a narrowing window-share COMMITS through the real executor");
        assert_eq!(b.rights(), &AuthRequired::Signature);
        // B's cap is a REAL firmament surface cap over the SAME backing cell as A.
        assert_eq!(b.backing_cell(), a.backing_cell());
        assert!(b.authority().target.is_surface());
        // B's window actually authenticates (B holds the narrowed authority).
        assert!(shell.validates(&b));

        // Now B (a read-only mirror, Signature) tries to WIDEN the share —
        // handing app C a fully-writable (Either) cap it does NOT hold. The REAL
        // executor REJECTS it (DelegationDenied), surfaced as ShareDenied, and C
        // gets NOTHING.
        let widened = shell.share(&b, /*recipient app*/ 0xC, AuthRequired::Either);
        assert!(
            matches!(widened, Err(ShellError::ShareDenied(_))),
            "a WIDENING window-share must be REJECTED by the real executor, got {widened:?}"
        );

        // The refusal changed nothing: no new surface was registered for C, and
        // B's own window still works (the rejection is local to the bad share).
        assert!(shell.validates(&b));

        // And B CAN still share what it legitimately holds: an equal-or-narrower
        // share (Signature -> Signature) COMMITS.
        let c_ok = shell
            .share(&b, 0xC, AuthRequired::Signature)
            .expect("an attenuating re-share COMMITS");
        assert_eq!(c_ok.rights(), &AuthRequired::Signature);
        assert!(shell.validates(&c_ok));
    }

    #[test]
    fn focus_raises_to_front_of_the_z_order() {
        let (mut shell, world, anchors, console) = shell_with_console();
        let [_t, service, user] = anchors;
        let a = shell.open_cell_view(service, "Service");
        let b = shell.open_cell_view(user, "User");
        // b opened last → it's the front. Focusing a raises it above b.
        assert_eq!(shell.compose(&world).front().unwrap().surface.cell(), user);
        shell.focus(&a).unwrap();
        assert_eq!(
            shell.compose(&world).front().unwrap().surface.cell(),
            service
        );
        // The console is still present, behind.
        assert!(shell.validates(&console));
        assert_eq!(shell.surface_count(), 3);
        let _ = b;
    }

    #[test]
    fn closing_a_surface_kills_its_capability() {
        let (mut shell, _world, anchors, _console) = shell_with_console();
        let cap = shell.open_cell_view(anchors[1], "Service");
        assert_eq!(shell.surface_count(), 2);
        assert!(shell.close(&cap).is_ok());
        assert_eq!(shell.surface_count(), 1);
        // The cap is now dead — further ops refuse.
        assert!(!shell.validates(&cap));
        assert_eq!(shell.focus(&cap), Err(ShellError::Unauthorized));
    }

    #[test]
    fn the_console_is_protected_from_close() {
        let (mut shell, _world, _anchors, console) = shell_with_console();
        // Even WITH the console's real cap, close is refused (trusted root).
        assert_eq!(shell.close(&console), Err(ShellError::ConsoleProtected));
        assert_eq!(shell.surface_count(), 1);
    }

    #[test]
    fn move_is_cap_gated_and_honored_under_float() {
        let (mut shell, world, anchors, _console) = shell_with_console();
        let cap = shell.open_cell_view(anchors[1], "Service");
        let before = shell
            .compose(&world)
            .items
            .iter()
            .find(|it| it.surface.cell() == anchors[1])
            .unwrap()
            .surface
            .rect();
        shell.move_by(&cap, 50.0, 25.0).unwrap();
        let after = shell
            .compose(&world)
            .items
            .iter()
            .find(|it| it.surface.cell() == anchors[1])
            .unwrap()
            .surface
            .rect();
        assert_eq!(after.x, before.x + 50.0);
        assert_eq!(after.y, before.y + 25.0);
    }

    #[test]
    fn the_trusted_path_label_tracks_the_live_cell_lifecycle() {
        // Anti-spoof: the identity badge is the SHELL's, read from the ledger.
        // Seal the backing cell through the real executor and the badge follows.
        let (mut shell, mut world, _anchors, _console) = shell_with_console();
        // Open a view of a fresh cell we then seal.
        let fresh = world.genesis_cell(0x5A, 0);
        let _cap = shell.open_cell_view(fresh, "Fresh");
        let live_badge = shell
            .compose(&world)
            .items
            .iter()
            .find(|it| it.surface.cell() == fresh)
            .unwrap()
            .identity
            .lifecycle;
        assert_eq!(live_badge, "live");

        // Seal it (agent == target) through the verified executor.
        let t = world.turn(fresh, vec![crate::world::seal(fresh, "lock")]);
        assert!(world.commit_turn(t).is_committed());
        let sealed_badge = shell
            .compose(&world)
            .items
            .iter()
            .find(|it| it.surface.cell() == fresh)
            .unwrap()
            .identity
            .lifecycle;
        assert_eq!(
            sealed_badge, "sealed",
            "the shell's identity badge follows the live ledger"
        );
    }

    #[test]
    fn a_dangling_surface_is_labelled_missing_not_spoofable() {
        // A surface whose backing cell is NOT in the ledger is shown as
        // unbacked/missing — it can't masquerade as a live cell.
        let (mut shell, world, _anchors, _console) = shell_with_console();
        let ghost = CellId::from_bytes([0x77; 32]); // never installed
        let _cap = shell.open_cell_view(ghost, "Ghost");
        let item = shell
            .compose(&world)
            .items
            .iter()
            .find(|it| it.surface.cell() == ghost)
            .cloned()
            .unwrap();
        assert!(!item.identity.backed, "an un-installed cell is not backed");
        assert_eq!(item.identity.lifecycle, "missing");
    }

    #[test]
    fn layout_tiles_and_stacks_the_non_console_surfaces() {
        let (mut shell, world, anchors, _console) = shell_with_console();
        let _a = shell.open_cell_view(anchors[1], "Service");
        let _b = shell.open_cell_view(anchors[2], "User");

        shell.set_area(1200.0, 700.0);
        shell.set_layout(Layout::Tile);
        let scene = shell.compose(&world);
        assert_eq!(scene.layout, Layout::Tile);
        // The two cell views tile to non-overlapping, in-bounds rects.
        let cell_rects: Vec<Rect> = scene
            .items
            .iter()
            .filter(|it| !it.surface.is_console())
            .map(|it| it.surface.rect())
            .collect();
        assert_eq!(cell_rects.len(), 2);
        for r in &cell_rects {
            assert!(r.x >= 0.0 && r.y >= 0.0);
            assert!(r.x + r.w <= 1200.0 + 1.0);
        }

        // Cycle to stack: the front view is centered-ish and large.
        shell.set_layout(Layout::Stack);
        let scene = shell.compose(&world);
        assert_eq!(scene.layout, Layout::Stack);
        let front = scene.front().unwrap();
        assert!(!front.surface.is_console());
        assert!(front.surface.rect().w >= 360.0);
    }

    #[test]
    fn minimize_drops_focus_to_the_front_and_restore_refocuses() {
        let (mut shell, _world, anchors, _console) = shell_with_console();
        let a = shell.open_cell_view(anchors[1], "Service");
        let b = shell.open_cell_view(anchors[2], "User");
        // b is focused (opened last). Minimize b → focus falls to the new front.
        shell.set_minimized(&b, true).unwrap();
        assert_ne!(shell.focused(), Some(b.surface()));
        // Restoring b raises + refocuses it.
        shell.set_minimized(&b, false).unwrap();
        assert_eq!(shell.focused(), Some(b.surface()));
        let _ = a;
    }

    #[test]
    fn hit_test_finds_the_front_surface_under_a_point() {
        let (mut shell, world, anchors, _console) = shell_with_console();
        shell.set_layout(Layout::Float);
        let a = shell.open_cell_view(anchors[1], "Service");
        // Place a known rect and hit its center.
        shell.resize(&a, 200.0, 150.0).unwrap();
        // Move it to a clear spot.
        let item = shell
            .compose(&world)
            .items
            .iter()
            .find(|it| it.surface.cell() == anchors[1])
            .unwrap()
            .surface
            .rect();
        let cx = item.x + item.w / 2.0;
        let cy = item.y + item.h / 2.0;
        assert_eq!(shell.hit_test(cx, cy, &world), Some(a.surface()));
        // A point far outside any surface hits nothing... unless the console
        // (full-area) is under it — the console spans the work area, so a point
        // inside the area but outside the cell view falls through to the console.
        let hit = shell.hit_test(5.0, 5.0, &world);
        assert!(
            hit.is_some(),
            "a point in the work area hits at least the console"
        );
    }

    #[test]
    fn cycle_layout_rotates_float_tile_stack() {
        let mut shell = Shell::new();
        assert_eq!(shell.layout(), Layout::Float);
        shell.cycle_layout();
        assert_eq!(shell.layout(), Layout::Tile);
        shell.cycle_layout();
        assert_eq!(shell.layout(), Layout::Stack);
        shell.cycle_layout();
        assert_eq!(shell.layout(), Layout::Float);
    }

    // --- THE VERIFIED-SCENE COMPOSITOR (T1/T2/T3) on the shell's real surfaces ---

    #[test]
    fn compose_scene_gives_each_surface_a_disjoint_region_and_one_focus() {
        // The shell's scene mirrors the Lean `Scene`: each surface owns exactly
        // its (distinct) region-set, and at-most-one holds focus (T3 by
        // construction). The label/source-root come from the live world (T2).
        let (mut shell, world, anchors, _console) = shell_with_console();
        let a = shell.open_cell_view(anchors[1], "Service");
        let _b = shell.open_cell_view(anchors[2], "User");
        let scene = shell.compose_scene(&world);
        // Every surface owns disjoint regions.
        let mut all_regions: Vec<u64> = scene
            .surfaces
            .iter()
            .flat_map(|s| s.regions.clone())
            .collect();
        let n = all_regions.len();
        all_regions.sort_unstable();
        all_regions.dedup();
        assert_eq!(
            all_regions.len(),
            n,
            "surface regions are pairwise-disjoint (T1)"
        );
        // At-most-one focus flag (T3 focus-exclusivity, by construction).
        assert!(scene.surfaces.iter().filter(|s| s.focus_flag).count() <= 1);
        let _ = a;
    }

    #[test]
    fn an_honest_present_by_the_focused_surface_commits() {
        // THE COMMIT POLARITY on the shell's real surfaces: the focused surface
        // presenting its OWN region, claiming focus, COMMITS — advancing the
        // frame digest + logging it (the scene the operator sees is genuine).
        let (mut shell, world, anchors, _console) = shell_with_console();
        let a = shell.open_cell_view(anchors[1], "Service");
        // `a` is focused (opened last). It paints its own region, claims focus.
        let region = a.surface().region();
        let commit = shell
            .present(&a, &world, vec![region], /*claims_focus*/ true, 0xABCD)
            .expect("the honest present by the focused surface commits");
        assert_eq!(commit.digest, 0xABCD);
        assert_eq!(
            shell.frame_log().len(),
            1,
            "the present is logged (provenance)"
        );
    }

    #[test]
    fn an_overpaint_present_is_refused_with_the_t1_tooth() {
        // THE T1 TOOTH on the shell: surface `a` tries to paint surface `b`'s
        // region — REFUSED (overpaint), even though `a` holds a valid window cap.
        // The scene authority is a SEPARATE gate on top of the window cap.
        let (mut shell, world, anchors, _console) = shell_with_console();
        let a = shell.open_cell_view(anchors[1], "Service");
        let b = shell.open_cell_view(anchors[2], "User");
        // `a` holds a valid cap (it can drive its own window)...
        assert!(shell.validates(&a));
        // ...but presenting into `b`'s region overpaints — refused (T1).
        let b_region = b.surface().region();
        let r = shell.present(&a, &world, vec![b_region], false, 0x1111);
        assert!(
            matches!(
                r,
                Err(ShellError::PresentRefused(PresentError::Overpaint { .. }))
            ),
            "overpainting another surface's region is refused (T1), got {r:?}"
        );
        // Fail-closed: nothing was logged.
        assert_eq!(shell.frame_log().len(), 0);
    }

    #[test]
    fn an_input_steal_present_is_refused_with_the_t3_tooth() {
        // THE T3 TOOTH on the shell: the NON-focused surface asserting focus (to
        // steal the keystroke) is REFUSED, even with a valid window cap + its own
        // region. Input routes only to the focus holder.
        let (mut shell, world, anchors, _console) = shell_with_console();
        let a = shell.open_cell_view(anchors[1], "Service");
        let _b = shell.open_cell_view(anchors[2], "User");
        // `b` opened last so it is focused; `a` is NOT focused. `a` paints its
        // own region (T1 ok) but asserts focus → input-misroute (T3).
        let a_region = a.surface().region();
        let r = shell.present(
            &a,
            &world,
            vec![a_region],
            /*claims_focus*/ true,
            0x2222,
        );
        assert!(
            matches!(
                r,
                Err(ShellError::PresentRefused(
                    PresentError::InputMisroute { .. }
                ))
            ),
            "a non-focused surface asserting focus is refused (T3), got {r:?}"
        );
        assert_eq!(shell.frame_log().len(), 0);
    }

    #[test]
    fn route_input_delivers_only_to_the_focused_surface_cell() {
        // THE T3 INPUT GATE on the shell: input is delivered only to the focus
        // holder's cell; a misroute to a non-focused cell is refused.
        let (mut shell, world, anchors, _console) = shell_with_console();
        let _a = shell.open_cell_view(anchors[1], "Service");
        let _b = shell.open_cell_view(anchors[2], "User");
        // `b` (anchors[2], the User cell) is focused (opened last).
        assert_eq!(shell.route_input(anchors[2], &world), Ok(anchors[2]));
        // Routing input to the non-focused Service cell is refused.
        assert!(matches!(
            shell.route_input(anchors[1], &world),
            Err(ShellError::PresentRefused(
                PresentError::InputMisroute { .. }
            ))
        ));
    }

    #[test]
    fn a_present_without_a_held_cap_is_refused_by_the_window_gate_first() {
        // The two gates compose: a forged cap is refused by the WINDOW-cap gate
        // (Unauthorized) BEFORE the scene authority even runs — you can't present
        // a window you don't hold.
        use dregg_firmament::{AuthRequired, Capability, CellId as FCellId};
        let (mut shell, world, anchors, _console) = shell_with_console();
        let real = shell.open_cell_view(anchors[1], "Service");
        let ghost_cell = {
            let mut k = [0u8; 32];
            k[0] = 0xEE;
            FCellId::derive_raw(&k, &[0u8; 32])
        };
        let forged = SurfaceCapability::new(
            real.surface(),
            Capability::surface(ghost_cell, AuthRequired::None),
        );
        let region = real.surface().region();
        let r = shell.present(&forged, &world, vec![region], true, 0x3333);
        assert_eq!(
            r,
            Err(ShellError::Unauthorized),
            "the window-cap gate refuses a forged cap first"
        );
    }

    #[test]
    fn the_t2_label_binding_tracks_the_live_state_root() {
        // T2 on the shell: the genuine label binds to the owner + the live
        // source-state-root, which MOVES when the cell's state changes. After a
        // committed turn that changes balance, a present must declare the NEW
        // binding — the shell computes it (the app never supplies the label), so
        // a present always carries the genuine, current binding. We witness that
        // the source-state-root the shell computes differs across a real turn.
        let (mut shell, mut world, _anchors, _console) = shell_with_console();
        let fresh = world.genesis_cell(0x6B, 1_000);
        let other = world.genesis_cell(0x6C, 0);
        let cap = shell.open_cell_view(fresh, "Fresh");
        let root_before = shell.source_state_root(fresh, &world);
        // A real transfer changes `fresh`'s balance → its state-root moves.
        let t = world.turn(fresh, vec![crate::world::transfer(fresh, other, 100)]);
        assert!(world.commit_turn(t).is_committed());
        let root_after = shell.source_state_root(fresh, &world);
        assert_ne!(
            root_before, root_after,
            "the source-state-root moves with the cell's live state"
        );
        // The genuine label re-binds to the new root (the §5 state-root binding).
        assert_ne!(
            label_of(&fresh, root_before),
            label_of(&fresh, root_after),
            "the T2 label re-binds as the state-root advances"
        );
        // A present now carries the CURRENT binding (computed by the shell), so
        // an honest present by the focused surface still commits.
        let region = cap.surface().region();
        assert!(shell
            .present(&cap, &world, vec![region], true, 0x4242)
            .is_ok());
    }
}
