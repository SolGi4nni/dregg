//! Surfaces — cap-confined cell views (the apps-as-cells primitive).
//!
//! The desktop-OS pillar: every dregg CELL can be opened as its own SURFACE (a
//! window) in the shell. A surface is not a free-floating widget — it is OWNED
//! via a [`SurfaceCapability`], and only the cap-holder may render or drive it.
//! This is the ocap discipline the rest of dregg runs, applied to the *window
//! manager itself*: there is no ambient authority to raise, move, focus, or
//! close a window — you must present the capability that authorizes it.
//!
//! **The capability is the REAL `dregg_firmament` capability** (`docs/
//! DREGG-DESKTOP-OS.md` §1, §7): a window IS a
//! [`Capability`](dregg_firmament::Capability) over a
//! [`Target::Surface(cell)`](dregg_firmament::Target::Surface). Holding /
//! attenuating / delegating / revoking a window is exactly holding /
//! attenuating / delegating / revoking that cap, through the SAME
//! `granted ⊆ held` ([`is_attenuation`](dregg_firmament::is_attenuation)) gate
//! and the SAME real [`dregg_turn::TurnExecutor`] as every other dregg cap. We
//! do NOT keep a parallel bearer-secret model — window authority rides the
//! firmament fabric the local and distributed backings already proved. (§7 "the
//! one latent divergence to close": the secret model is GONE.)
//!
//! A surface is backed by a REAL cell (`CellId`) viewed through the embedded
//! [`World`](crate::world::World): its title, its trusted-path identity label,
//! and its body all read the live ledger — there are NO mock surfaces. When a
//! turn changes the cell, the surface re-reads and reflects it. (Authority is
//! the firmament cap over the surface's *backing* cell; identity is shell-drawn
//! from the live world — two distinct ledgers, two distinct roles.)
//!
//! This module is gpui-free and `cargo test`-able. The shell ([`crate::shell`])
//! owns the surfaces + the z-order + the firmament surface-fabric the caps are
//! checked against; the cockpit maps the shell's composed scene onto gpui.

use dregg_cell::CellId;
use dregg_firmament::{Capability, Rights, Target};

/// A monotonic surface handle (stable across the surface's life; the shell
/// assigns these in open order). Distinct from the backing `CellId` so the same
/// cell can (in principle) back more than one surface, and so a closed-then-
/// reopened cell gets a fresh, non-confusable surface.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct SurfaceId(pub u64);

impl SurfaceId {
    pub fn as_u64(self) -> u64 {
        self.0
    }
}

/// A token that confers authority over a surface — **a REAL `dregg_firmament`
/// capability over the surface's backing cell**, paired with the [`SurfaceId`]
/// (the window handle) it authorizes.
///
/// This is NOT a bearer secret (the parallel model is gone, §7). The
/// load-bearing half is [`Self::authority`]: a
/// [`Capability`](dregg_firmament::Capability) whose target is
/// `Surface(backing_cell)` and whose `rights` are on the REAL
/// [`AuthRequired`](dregg_firmament::AuthRequired) lattice. The shell
/// authenticates a presented cap by resolving it through the firmament's
/// [`SurfaceBacking`](dregg_firmament::SurfaceBacking) — the `granted ⊆ held`
/// ([`is_attenuation`](dregg_firmament::is_attenuation)) gate — so:
///   * the cap names exactly one surface AND its `authority` must target that
///     surface's backing cell (no cap confusion — a cap for one window can't
///     drive another, and a cap targeting the wrong cell is refused), and
///   * authority is exactly the firmament cap's rights `⊆` the rights the
///     surface's owner-grant holds — it can be obtained only by being *granted*
///     (the shell installs the owner-grant + hands back the cap; an attenuated
///     copy obtained via [`crate::shell::Shell::share`] narrows it through a
///     REAL `Effect::GrantCapability` turn), never by naming the surface.
///
/// This is the window-manager realization of the executor's no-amplification
/// rule: it IS the executor's rule, on glass — the SAME gate the local and
/// distributed firmament backings use, with no special-casing.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SurfaceCapability {
    surface: SurfaceId,
    /// The REAL firmament capability — `target = Surface(backing_cell)`, rights
    /// on the genuine `AuthRequired` lattice. The window's authority IS this.
    authority: Capability,
}

impl SurfaceCapability {
    /// The surface this capability authorizes.
    pub fn surface(&self) -> SurfaceId {
        self.surface
    }

    /// The REAL firmament capability this token carries (target =
    /// `Surface(backing_cell)`, rights on the `AuthRequired` lattice). This is
    /// the load-bearing authority the shell checks via `granted ⊆ held`.
    pub fn authority(&self) -> &Capability {
        &self.authority
    }

    /// The backing cell this cap's authority targets, if it is a `Surface`
    /// target (it always is for a shell-minted cap). Used by the shell to bind
    /// the presented cap to the right surface (anti-confusion) before the
    /// `is_attenuation` check.
    pub fn backing_cell(&self) -> Option<CellId> {
        match self.authority.target {
            Target::Surface { cell } => Some(cell),
            _ => None,
        }
    }

    /// The rights this cap carries over its backing surface cell.
    pub fn rights(&self) -> &Rights {
        &self.authority.rights
    }

    /// Construct from a [`SurfaceId`] + the REAL firmament cap over its backing
    /// cell. CRATE-PRIVATE: only the shell (which seeds the surface-fabric cell +
    /// installs the owner-grant) mints these, so a cap that the firmament's
    /// `granted ⊆ held` gate will admit cannot be forged from outside.
    pub(crate) fn new(surface: SurfaceId, authority: Capability) -> Self {
        SurfaceCapability { surface, authority }
    }
}

/// What a surface presents. The cockpit is ONE privileged surface (the master
/// console); every other surface is a cap-confined VIEW of a single cell.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SurfaceKind {
    /// The privileged master-console surface (the cockpit itself). It is still a
    /// surface in the shell — focusable, stackable — but it is the system's own
    /// trusted root, labelled as such (it is not a spoofable cell identity).
    Console,
    /// A cap-confined view of a single cell (apps-as-cells). The body reads the
    /// backing cell from the live ledger.
    CellView,
}

impl SurfaceKind {
    pub fn label(self) -> &'static str {
        match self {
            SurfaceKind::Console => "console",
            SurfaceKind::CellView => "cell",
        }
    }
}

/// A rectangle in shell-space (logical pixels). Plain data so the model stays
/// gpui-free; the cockpit maps it onto gpui `px()` bounds.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Rect {
    pub x: f32,
    pub y: f32,
    pub w: f32,
    pub h: f32,
}

impl Rect {
    pub fn new(x: f32, y: f32, w: f32, h: f32) -> Self {
        Rect { x, y, w, h }
    }

    /// Whether a point lies inside the rect (used for hit-testing focus).
    pub fn contains(&self, px: f32, py: f32) -> bool {
        px >= self.x && px <= self.x + self.w && py >= self.y && py <= self.y + self.h
    }

    /// Translate the rect by a delta, clamping the top-left to `>= 0` so a
    /// surface can't be dragged off the top/left of the shell (it stays
    /// reachable — a trusted-path property: a surface you own can't be hidden).
    pub fn translated(&self, dx: f32, dy: f32) -> Rect {
        Rect {
            x: (self.x + dx).max(0.0),
            y: (self.y + dy).max(0.0),
            w: self.w,
            h: self.h,
        }
    }
}

/// A live surface: a cap-confined window backed by a real cell.
///
/// The surface holds NO copy of the cell's state — it holds the cell's id and
/// re-reads the live ledger when it renders, so it cannot drift from what the
/// executor holds. The geometry/stacking fields are the window-manager state the
/// shell maintains; mutating them goes through the shell's CAP-GATED ops, never
/// directly.
#[derive(Clone, Debug)]
pub struct Surface {
    id: SurfaceId,
    kind: SurfaceKind,
    /// The cell this surface is a view OF. For the console this is the operator/
    /// system identity the console runs as; for a cell-view it is the viewed cell.
    cell: CellId,
    /// The window title (operator-facing). The TRUSTED-PATH identity label is
    /// derived separately from the live cell id (see [`crate::shell`]) so a
    /// surface's title can never *be* the spoof — the identity chrome is the
    /// shell's, drawn from the ledger, not the surface's self-description.
    title: String,
    /// Window geometry in shell-space.
    rect: Rect,
    /// Stacking order — higher is nearer the front. The shell keeps these dense
    /// and unique; the compositor paints in ascending z.
    z: u32,
    /// Whether the surface is minimized (collapsed out of the scene body but
    /// still owned + present in the shell, reachable via its cap).
    minimized: bool,
}

impl Surface {
    /// CRATE-PRIVATE constructor: only the shell creates surfaces (it owns the
    /// id allocator + the cap registry), so a `Surface` cannot be conjured
    /// outside the trusted window manager.
    pub(crate) fn new(
        id: SurfaceId,
        kind: SurfaceKind,
        cell: CellId,
        title: String,
        rect: Rect,
        z: u32,
    ) -> Self {
        Surface {
            id,
            kind,
            cell,
            title,
            rect,
            z,
            minimized: false,
        }
    }

    pub fn id(&self) -> SurfaceId {
        self.id
    }
    pub fn kind(&self) -> SurfaceKind {
        self.kind
    }
    /// The backing cell id — the surface's REAL anchor in the live ledger.
    pub fn cell(&self) -> CellId {
        self.cell
    }
    pub fn title(&self) -> &str {
        &self.title
    }
    pub fn rect(&self) -> Rect {
        self.rect
    }
    pub fn z(&self) -> u32 {
        self.z
    }
    pub fn is_minimized(&self) -> bool {
        self.minimized
    }
    pub fn is_console(&self) -> bool {
        matches!(self.kind, SurfaceKind::Console)
    }

    // --- crate-private mutators (the shell drives these AFTER a cap check) ----

    pub(crate) fn set_z(&mut self, z: u32) {
        self.z = z;
    }
    pub(crate) fn set_rect(&mut self, rect: Rect) {
        self.rect = rect;
    }
    pub(crate) fn set_minimized(&mut self, m: bool) {
        self.minimized = m;
    }
    pub(crate) fn set_title(&mut self, title: String) {
        self.title = title;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rect_contains_and_translate_clamp() {
        let r = Rect::new(10.0, 20.0, 100.0, 80.0);
        assert!(r.contains(50.0, 50.0));
        assert!(!r.contains(5.0, 50.0));
        assert!(r.contains(10.0, 20.0)); // top-left corner inclusive
        // Translating past the top-left clamps to 0 (can't be dragged off-screen).
        let t = r.translated(-1000.0, -1000.0);
        assert_eq!(t.x, 0.0);
        assert_eq!(t.y, 0.0);
        // The size is preserved under translation.
        assert_eq!(t.w, 100.0);
        assert_eq!(t.h, 80.0);
    }

    #[test]
    fn a_capability_carries_a_real_firmament_cap_over_its_backing_cell() {
        // The token's authority is a REAL firmament cap over a Surface(cell)
        // target on the genuine AuthRequired lattice — NOT a bearer secret.
        fn cid(b: u8) -> CellId {
            let mut k = [0u8; 32];
            k[0] = b;
            CellId::derive_raw(&k, &[0u8; 32])
        }
        let backing = cid(0x2A);
        let cap = SurfaceCapability::new(
            SurfaceId(7),
            Capability::surface(backing, dregg_firmament::AuthRequired::Either),
        );
        assert_eq!(cap.surface(), SurfaceId(7));
        // The authority targets the backing surface cell (anti cap-confusion).
        assert_eq!(cap.backing_cell(), Some(backing));
        assert!(cap.authority().target.is_surface());
        assert_eq!(cap.rights(), &dregg_firmament::AuthRequired::Either);

        // The cap narrows by the REAL is_attenuation lattice (a writable window
        // → a read-only mirror), exactly like the firmament's local/distributed
        // caps — and refuses to widen (a mirror can't promote itself).
        let mirror = cap
            .authority()
            .attenuate(dregg_firmament::AuthRequired::Signature)
            .expect("Either -> Signature is a genuine narrowing");
        assert_eq!(mirror.rights, dregg_firmament::AuthRequired::Signature);
        assert_eq!(mirror.target, cap.authority().target); // same window, narrowed
        let mirror_only = Capability::surface(backing, dregg_firmament::AuthRequired::Signature);
        assert!(mirror_only.attenuate(dregg_firmament::AuthRequired::Either).is_none());
    }
}
