//! The embedder boundary IS the cap gate.
//!
//! `docs/EMBEDDED-WEB-SURFACE.md §2/§4.1`: libservo surfaces every
//! authority-bearing operation a `WebView` can perform as a `WebViewDelegate`
//! callback, and "a delegate is a trait that the embedder installs its own impl
//! for — so the embedding boundary IS the cap gate." This module is that, real:
//!
//! - [`WebSurfaceDelegate`] is the trait, shaped one-to-one against libservo's
//!   real `WebViewDelegate` (method names verified against `doc.servo.org` as of
//!   the doc's 2026-06-13 pin): `load_web_resource`, `allow_navigation`,
//!   `request_open_auxiliary_webview`, `request_permission`, `authenticate`.
//! - [`CapGatedDelegate`] is a real impl: each callback discharges the surface's
//!   held capability c-list, so a fetch / navigation / new-window / permission /
//!   auth the cap does not permit is refused *at the callback*, before the engine
//!   acts. The check is the GENUINE [`dregg_cell::is_attenuation`]
//!   (`granted ⊆ held`) — the same gate the firmament runs for every cap.
//! - [`MockSurface`] stands in for the libservo `WebView` (**the LIBSERVO SEAM**):
//!   a real `WebView` + a `WebViewDelegate` impl that forwards to
//!   [`CapGatedDelegate`] plugs in exactly where `MockSurface` sits, without the
//!   heavy libservo + Metal/wgpu toolchain this crate deliberately does not link.
//!
//! ## The no-amplification keystone
//!
//! An iframe / script-opened window is an **attenuation of its opener — it cannot
//! amplify** (`EMBEDDED-WEB-SURFACE.md §3`). [`CapGatedDelegate::open_auxiliary`]
//! mints the child surface's authority as the parent's *plus strictly-narrowing*
//! rights, routed through the same `is_attenuation` gate; a child that asks for
//! *wider* fetch authority than its opener holds is refused for the same
//! structural reason a widening window-share is `DelegationDenied`. The web's "an
//! ad iframe inherits the page's ambient reach" footgun is closed by construction.

use std::collections::BTreeSet;

use dregg_cell::{is_attenuation, AuthRequired};
use dregg_firmament::{Capability, Target};
use dregg_types::CellId;

/// The authority a web surface (a `WebView`) holds, grounded in the REAL
/// firmament cap model.
///
/// `docs/EMBEDDED-WEB-SURFACE.md §1`: "a web surface IS a `SurfaceCapability`
/// over a backing cell." This is that: a [`dregg_firmament::Capability`] whose
/// [`Target::Surface`] names the cell backing the `WebView`, carrying the
/// firmament `rights` lattice. We do NOT invent a windowing model or an authority
/// model — we attach the *web-relevant* attenuations (which origins this tab may
/// fetch / navigate to, which permissions it carries) as caveats on top of that
/// real handle.
///
/// The window-rights answer *which surface and can-it-be-touched-at-all*
/// (focus/move/close, the firmament `granted ⊆ held` on the surface cap); the
/// web caveats answer *what the page inside may reach*. Both narrow only.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SurfaceCapability {
    /// The REAL firmament window handle: `Capability{ target: Surface(cell),
    /// rights }`. Holding/attenuating/delegating the window is exactly
    /// holding/attenuating/delegating this cap, through the firmament's gate.
    pub window: Capability,
    /// The origins this tab may FETCH subresources from (the
    /// `load_web_resource` allowlist). A web caveat — an *allowlist*, so it
    /// narrows only: a child surface's set is `⊆` the parent's. `None` is the
    /// wildcard (fetch anything) — the root authority; any attenuation replaces
    /// it with a concrete, finite set.
    pub fetch_allow: Option<BTreeSet<String>>,
    /// The origins this tab may NAVIGATE the main frame to (the
    /// `allow_navigation` allowlist). Same narrowing discipline as
    /// [`Self::fetch_allow`]. `None` is the wildcard.
    pub navigate_allow: Option<BTreeSet<String>>,
    /// The permissions (geolocation, camera, …) this tab carries. A web caveat;
    /// a child's set is `⊆` the parent's (default-deny: an empty set grants
    /// nothing).
    pub permissions: BTreeSet<PermissionKind>,
}

impl SurfaceCapability {
    /// Mint a ROOT web surface authority over `cell` with full firmament
    /// `rights` and the wildcard web caveats (fetch/navigate anything, no
    /// permissions). This is the powerbox handing a top-level tab its authority;
    /// every iframe/popup below it is an attenuation of this.
    pub fn root(cell: CellId, rights: AuthRequired) -> Self {
        SurfaceCapability {
            window: Capability::surface(cell, rights),
            fetch_allow: None,
            navigate_allow: None,
            permissions: BTreeSet::new(),
        }
    }

    /// Mint a web surface authority over `cell` whose fetch + navigate are
    /// restricted to `origins` (a finite allowlist) and which carries
    /// `permissions`. The convenience constructor for "this tab may reach only
    /// `*.example.com`, no storage, geolocation only".
    pub fn scoped(
        cell: CellId,
        rights: AuthRequired,
        origins: impl IntoIterator<Item = String>,
        permissions: impl IntoIterator<Item = PermissionKind>,
    ) -> Self {
        let set: BTreeSet<String> = origins.into_iter().collect();
        SurfaceCapability {
            window: Capability::surface(cell, rights),
            fetch_allow: Some(set.clone()),
            navigate_allow: Some(set),
            permissions: permissions.into_iter().collect(),
        }
    }

    /// The cell backing this surface (the `WebView`'s content-addressed
    /// identity — its ViewRef). Reads it straight off the firmament target;
    /// a non-surface target has no backing cell.
    pub fn cell(&self) -> Option<CellId> {
        match self.window.target {
            Target::Surface { cell } => Some(cell),
            _ => None,
        }
    }

    /// Does this surface's fetch allowlist permit `origin`?
    ///
    /// `None` (wildcard root) permits anything; a concrete set permits exactly
    /// its members. This is the check [`CapGatedDelegate::load_web_resource`]
    /// runs — the `load_web_resource` cap gate.
    pub fn may_fetch(&self, origin: &str) -> bool {
        match &self.fetch_allow {
            None => true,
            Some(set) => set.contains(origin),
        }
    }

    /// Does this surface's navigate allowlist permit `origin`?
    pub fn may_navigate(&self, origin: &str) -> bool {
        match &self.navigate_allow {
            None => true,
            Some(set) => set.contains(origin),
        }
    }

    /// Does this surface carry `permission`?
    pub fn has_permission(&self, permission: PermissionKind) -> bool {
        self.permissions.contains(&permission)
    }

    /// Attenuate this surface to a CHILD — the no-amplification keystone.
    ///
    /// `docs/EMBEDDED-WEB-SURFACE.md §3`: "an iframe, or a script-opened window,
    /// is an ATTENUATION of its opener — it cannot amplify." The child:
    ///
    /// - binds a (possibly different) `child_cell`, but with `child_rights` that
    ///   must be `⊆` the parent's firmament rights — checked by the GENUINE
    ///   [`is_attenuation`] (`granted ⊆ held`), the same gate a widening
    ///   window-share hits (`DelegationDenied`);
    /// - its fetch/navigate allowlists are the INTERSECTION with the parent's (a
    ///   child can only ever clear origins, never add them — wildcard ∩ X = X,
    ///   X ∩ Y = X∩Y);
    /// - its permissions are the INTERSECTION with the parent's.
    ///
    /// Returns `None` (the amplification refusal) if `child_rights` is not `⊆`
    /// the parent's window rights, OR if the requested child fetch/navigate/
    /// permission sets are not subsets of what the parent holds. A sub-frame can
    /// only ever hold `≤` the authority of the frame that spawned it.
    pub fn attenuate_child(
        &self,
        child_cell: CellId,
        child_rights: AuthRequired,
        child_fetch: Option<BTreeSet<String>>,
        child_navigate: Option<BTreeSet<String>>,
        child_permissions: BTreeSet<PermissionKind>,
    ) -> Option<SurfaceCapability> {
        // (1) The window rights must attenuate by the REAL firmament gate.
        if !is_attenuation(&self.window.rights, &child_rights) {
            return None;
        }
        // (2) Fetch allowlist: the child set must be ⊆ the parent's reach, and
        //     the result is the intersection (never wider than the parent).
        let fetch_allow = intersect_allow(&self.fetch_allow, child_fetch)?;
        // (3) Navigate allowlist: same.
        let navigate_allow = intersect_allow(&self.navigate_allow, child_navigate)?;
        // (4) Permissions: the child set must be ⊆ the parent's.
        if !child_permissions.is_subset(&self.permissions) {
            return None;
        }
        Some(SurfaceCapability {
            window: Capability::surface(child_cell, child_rights),
            fetch_allow,
            navigate_allow,
            permissions: child_permissions,
        })
    }
}

/// Intersect a parent allowlist with a requested child allowlist, refusing
/// amplification.
///
/// Semantics (allowlist = a *set of permitted origins*, where `None` is the
/// wildcard "all origins"):
/// - parent wildcard (`None`) ∩ child `req` = `req` (the child narrows freely
///   from the wildcard — any concrete set, or stay wildcard);
/// - parent concrete `p` ∩ child wildcard (`None`) = `p` (a child that asks for
///   the wildcard is held to the parent's concrete reach — it does NOT widen);
/// - parent concrete `p` ∩ child concrete `c`: REFUSE (`None`) if `c ⊄ p` (the
///   child asked for an origin the parent cannot reach — amplification); else the
///   result is `c` (⊆ `p`).
fn intersect_allow(
    parent: &Option<BTreeSet<String>>,
    child: Option<BTreeSet<String>>,
) -> Option<Option<BTreeSet<String>>> {
    match (parent, child) {
        (None, req) => Some(req),
        (Some(p), None) => Some(Some(p.clone())),
        (Some(p), Some(c)) => {
            if c.is_subset(p) {
                Some(Some(c))
            } else {
                // The child asked to reach an origin the parent cannot — refuse.
                None
            }
        }
    }
}

/// A distinct web permission — each is its own capability
/// (`EMBEDDED-WEB-SURFACE.md §2`: "each permission is a distinct cap").
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum PermissionKind {
    Geolocation,
    Camera,
    Microphone,
    Notifications,
    Clipboard,
}

/// The decision a [`WebSurfaceDelegate`] returns for a navigation request.
///
/// Mirrors libservo's `allow_navigation` (which, per the doc, returns a policy:
/// "NavigationRequests are accepted by default" — so the cap gate must
/// AFFIRMATIVELY decide, which is why this is an explicit allow/deny).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NavigationDecision {
    /// The navigation is within the surface's `navigate` allowlist — allowed.
    Allow,
    /// The requested origin is not in the allowlist — denied (the shell shows
    /// the refusal in trusted chrome; the carried origin is what was refused).
    Deny { origin: String },
}

/// The decision a [`WebSurfaceDelegate`] returns for a resource load.
///
/// Mirrors libservo's `load_web_resource` ("the load may be intercepted… alternate
/// contents loaded by calling `WebResourceLoad::intercept`"): the cap gate either
/// lets the load continue or intercepts it with a cap-denied body.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ResourceDecision {
    /// The requested origin is within the surface's `fetch` allowlist — the load
    /// continues to the network as normal.
    Continue,
    /// The requested origin is NOT in the allowlist — intercepted with a visible
    /// `dregg: blocked by capability` body (the bytes the renderer gets instead
    /// of the real resource), so the page sees a refusal, never the resource.
    Intercept { reason: String, body: Vec<u8> },
}

impl ResourceDecision {
    /// Was the load allowed to continue (vs. cap-intercepted)?
    pub fn is_continue(&self) -> bool {
        matches!(self, ResourceDecision::Continue)
    }
}

/// The decision a [`WebSurfaceDelegate`] returns for a permission request.
///
/// Mirrors libservo's `request_permission` ("allow or deny… cached value or
/// query the user"). Default-deny is the ocap stance.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PermissionDecision {
    /// The surface's cap carries this permission — allowed.
    Allow,
    /// The surface's cap does not carry this permission — denied.
    Deny,
}

/// The embedder's mediation surface for a web engine — shaped one-to-one against
/// libservo's `WebViewDelegate`.
///
/// `docs/EMBEDDED-WEB-SURFACE.md §4.1`: the `WebView` / `WebViewDelegate` API is
/// libservo's first-class embedder surface, "modeled explicitly on the delegates
/// in Apple's WebKit API — the embedder installs an impl of the delegate trait
/// and Servo calls *out* to it at every authority point." Each method here is one
/// of those authority points; **the embedder's impl IS the cap gate**
/// ([`CapGatedDelegate`] is the cap-enforcing one). The libservo method names are
/// pinned at the doc's 2026-06-13 date (Servo's API is pre-1.0); these are the
/// SHAPE.
///
/// `surface` is the held authority (the c-list entry) for the `WebView` the
/// callback concerns — the delegate decides by discharging it.
pub trait WebSurfaceDelegate {
    /// libservo `load_web_resource` — "the load may be intercepted; alternate
    /// contents loaded by calling `WebResourceLoad::intercept`."
    ///
    /// The fetch/cookie/download chokepoint: the cap gate either lets the load
    /// continue or intercepts it with a cap-denied body. Called for ANY
    /// HTTP/HTTPS subresource, not just navigation.
    fn load_web_resource(&self, surface: &SurfaceCapability, origin: &str) -> ResourceDecision;

    /// libservo `allow_navigation` / `request_navigation` — decides per-load
    /// (main frame + nested iframes); "accepted by default", so the gate must
    /// affirmatively decide.
    fn allow_navigation(&self, surface: &SurfaceCapability, origin: &str) -> NavigationDecision;

    /// libservo `request_open_auxiliary_webview` / `request_create_new` — "web
    /// content requests to open a new WebView" (`window.open`, target=_blank,
    /// script-opened auxiliary).
    ///
    /// Returns the CHILD surface authority (an attenuation of `parent` — the
    /// no-amplification keystone), or `None` if the requested child authority
    /// would amplify (refused, exactly as a widening window-share is
    /// `DelegationDenied`). `child_cell` is the cell that will back the new
    /// `WebView`.
    fn request_open_auxiliary_webview(
        &self,
        parent: &SurfaceCapability,
        child_cell: CellId,
        requested_rights: AuthRequired,
        requested_fetch: Option<BTreeSet<String>>,
        requested_navigate: Option<BTreeSet<String>>,
        requested_permissions: BTreeSet<PermissionKind>,
    ) -> Option<SurfaceCapability>;

    /// libservo `request_permission` — "allow or deny… cached value or query the
    /// user." Each permission is a distinct cap; granted iff the surface carries
    /// it, else denied (default-deny).
    fn request_permission(
        &self,
        surface: &SurfaceCapability,
        permission: PermissionKind,
    ) -> PermissionDecision;

    /// libservo `request_authentication` — "supply credentials for HTTP auth";
    /// route to a cap-scoped credential store, never an ambient keychain.
    ///
    /// Returns the credential bytes the surface's cap names for `origin`, or
    /// `None` (the prompt is denied) if the surface holds no credential cap for
    /// that origin. We model "the surface only gets creds its cap names" as: a
    /// credential is available iff `origin` is in the surface's fetch allowlist
    /// (the surface is scoped to that origin) — a stand-in for the cipherclerk-
    /// held secret store the real wiring consults.
    fn authenticate(&self, surface: &SurfaceCapability, origin: &str) -> Option<Vec<u8>>;
}

/// The cap-enforcing delegate: every callback discharges the held capability.
///
/// This is the real `WebViewDelegate` impl `docs/EMBEDDED-WEB-SURFACE.md §2`
/// describes — "the delegate callback is the powerbox." It holds NO ambient
/// authority of its own; every decision is a function of the `surface` argument's
/// held caps (the c-list entry) checked against the request. The checks are the
/// GENUINE dregg ones: navigation/fetch allowlists narrow only, the new-window
/// mint routes through [`is_attenuation`] (`granted ⊆ held`), permissions are
/// default-deny.
#[derive(Clone, Debug, Default)]
pub struct CapGatedDelegate;

impl CapGatedDelegate {
    pub fn new() -> Self {
        CapGatedDelegate
    }

    /// Open an auxiliary `WebView` as an attenuation of `parent` (the
    /// no-amplification keystone, exposed as a named method for the demo +
    /// tests). Delegates to [`SurfaceCapability::attenuate_child`].
    pub fn open_auxiliary(
        &self,
        parent: &SurfaceCapability,
        child_cell: CellId,
        requested_rights: AuthRequired,
        requested_fetch: Option<BTreeSet<String>>,
        requested_navigate: Option<BTreeSet<String>>,
        requested_permissions: BTreeSet<PermissionKind>,
    ) -> Option<SurfaceCapability> {
        parent.attenuate_child(
            child_cell,
            requested_rights,
            requested_fetch,
            requested_navigate,
            requested_permissions,
        )
    }
}

impl WebSurfaceDelegate for CapGatedDelegate {
    fn load_web_resource(&self, surface: &SurfaceCapability, origin: &str) -> ResourceDecision {
        if surface.may_fetch(origin) {
            ResourceDecision::Continue
        } else {
            ResourceDecision::Intercept {
                reason: format!("dregg: blocked by capability — fetch to {origin} not permitted"),
                body: format!("dregg: blocked by capability (fetch to {origin})").into_bytes(),
            }
        }
    }

    fn allow_navigation(&self, surface: &SurfaceCapability, origin: &str) -> NavigationDecision {
        if surface.may_navigate(origin) {
            NavigationDecision::Allow
        } else {
            NavigationDecision::Deny {
                origin: origin.to_string(),
            }
        }
    }

    fn request_open_auxiliary_webview(
        &self,
        parent: &SurfaceCapability,
        child_cell: CellId,
        requested_rights: AuthRequired,
        requested_fetch: Option<BTreeSet<String>>,
        requested_navigate: Option<BTreeSet<String>>,
        requested_permissions: BTreeSet<PermissionKind>,
    ) -> Option<SurfaceCapability> {
        self.open_auxiliary(
            parent,
            child_cell,
            requested_rights,
            requested_fetch,
            requested_navigate,
            requested_permissions,
        )
    }

    fn request_permission(
        &self,
        surface: &SurfaceCapability,
        permission: PermissionKind,
    ) -> PermissionDecision {
        if surface.has_permission(permission) {
            PermissionDecision::Allow
        } else {
            PermissionDecision::Deny
        }
    }

    fn authenticate(&self, surface: &SurfaceCapability, origin: &str) -> Option<Vec<u8>> {
        // The surface only gets creds its cap names: available iff the surface is
        // scoped to `origin` (it is in the fetch allowlist). A wildcard surface
        // holds no specific credential cap (it is not scoped to any one origin),
        // so it gets nothing — credentials are an explicit, scoped grant.
        match &surface.fetch_allow {
            Some(set) if set.contains(origin) => {
                Some(format!("cap-scoped-credential-for:{origin}").into_bytes())
            }
            _ => None,
        }
    }
}

/// **THE LIBSERVO SEAM.** A stand-in for the libservo `WebView`.
///
/// `docs/EMBEDDED-WEB-SURFACE.md §0/§6`: the surface/shell discipline + the cap
/// model are real today; "the libservo embed behind the cap gate is a near-term
/// build." This crate deliberately does NOT link libservo (a multi-MB Rust
/// codebase + a Metal/wgpu toolchain that does not build cleanly in this
/// environment). `MockSurface` is the seam: it carries the held
/// [`SurfaceCapability`] and a current URL, and routes each authority-bearing
/// operation through a [`WebSurfaceDelegate`] — exactly as a real `WebView` calls
/// out to its `WebViewDelegate`.
///
/// ## How the real libservo `WebView` plugs in here
///
/// ```text
/// // LIBSERVO SEAM — replace `MockSurface` with a real libservo WebView whose
/// // WebViewDelegate impl forwards to a CapGatedDelegate:
/// //
/// //   use servo::{WebView, WebViewBuilder};
/// //   use servo::webview_delegate::WebViewDelegate;
/// //
/// //   struct CapGate { surface: SurfaceCapability, gate: CapGatedDelegate }
/// //   impl WebViewDelegate for CapGate {
/// //       fn load_web_resource(&self, _wv, load: WebResourceLoad) {
/// //           let origin = load.request().url().origin().ascii_serialization();
/// //           match self.gate.load_web_resource(&self.surface, &origin) {
/// //               ResourceDecision::Continue => { /* let it proceed */ }
/// //               ResourceDecision::Intercept { body, .. } =>
/// //                   load.intercept(/* a Response with `body` */),
/// //           }
/// //       }
/// //       fn allow_navigation(&self, _wv, nav) -> bool { /* gate.allow_navigation -> bool */ }
/// //       fn request_open_auxiliary_webview(&self, _wv) -> Option<WebView> { /* gate.open_auxiliary */ }
/// //       fn request_permission(&self, _wv, req) { /* gate.request_permission */ }
/// //       fn request_authentication(&self, _wv, req) { /* gate.authenticate */ }
/// //   }
/// //   let webview = WebViewBuilder::new(&servo).delegate(Rc::new(CapGate{..})).build();
/// ```
///
/// Everything `CapGatedDelegate` gates against — the cap model, `is_attenuation`,
/// the no-amplification mint — is the REAL dregg machinery and unchanged when the
/// seam closes. Only `MockSurface` is replaced.
pub struct MockSurface<D: WebSurfaceDelegate> {
    /// The held authority for this `WebView` — the c-list entry the delegate
    /// discharges. Carried by the surface, not by the (untrusted) page.
    pub surface: SurfaceCapability,
    /// The URL the surface is currently navigated to — the *committed* origin
    /// the trusted chrome reads (`EMBEDDED-WEB-SURFACE.md §1`: "the URL the badge
    /// shows is the one `notify_url_changed` committed, bound to the surface
    /// cell"). Starts unset; set only by a delegate-ALLOWED navigation.
    pub current_url: Option<String>,
    /// The embedder's delegate — the cap gate. A real `WebView` holds an
    /// `Rc<dyn WebViewDelegate>`; here we hold the concrete gate.
    pub delegate: D,
}

impl<D: WebSurfaceDelegate> MockSurface<D> {
    /// Open a (mock) `WebView` for `surface`, gated by `delegate`. The real
    /// `WebViewBuilder::new(&servo).delegate(..).build()` lands here.
    pub fn open(surface: SurfaceCapability, delegate: D) -> Self {
        MockSurface {
            surface,
            current_url: None,
            delegate,
        }
    }

    /// Drive a navigation. The (mock) engine asks the delegate first
    /// (`allow_navigation`); on allow it COMMITS the URL (so the trusted chrome
    /// updates), on deny it leaves the current URL untouched and returns the
    /// refusal. This is libservo's "navigation policy" path: Servo calls out to
    /// the delegate, the cap gate decides.
    pub fn navigate(&mut self, origin: &str, url: &str) -> NavigationDecision {
        let decision = self.delegate.allow_navigation(&self.surface, origin);
        if let NavigationDecision::Allow = decision {
            // notify_url_changed: bind the committed URL to the surface — the
            // trusted chrome reads THIS, never page-painted chrome.
            self.current_url = Some(url.to_string());
        }
        decision
    }

    /// Drive a subresource fetch. The (mock) engine asks the delegate
    /// (`load_web_resource`); the cap gate either lets it continue or intercepts
    /// with a cap-denied body. Returns the decision (the bytes the renderer
    /// would receive on an intercept).
    pub fn fetch(&self, origin: &str) -> ResourceDecision {
        self.delegate.load_web_resource(&self.surface, origin)
    }

    /// Drive a permission request. The (mock) engine asks the delegate
    /// (`request_permission`); default-deny unless the surface carries the cap.
    pub fn request_permission(&self, permission: PermissionKind) -> PermissionDecision {
        self.delegate.request_permission(&self.surface, permission)
    }

    /// Drive an HTTP-auth prompt. The (mock) engine asks the delegate
    /// (`authenticate`); the surface only gets creds its cap names for `origin`.
    pub fn authenticate(&self, origin: &str) -> Option<Vec<u8>> {
        self.delegate.authenticate(&self.surface, origin)
    }

    /// Open an auxiliary `WebView` (a `window.open` / popup) as an attenuation of
    /// THIS surface (`request_open_auxiliary_webview`). Returns the child mock
    /// surface (sharing the same delegate type), or `None` if the requested
    /// child authority would amplify — refused at the boundary.
    pub fn open_auxiliary(
        &self,
        child_cell: CellId,
        requested_rights: AuthRequired,
        requested_fetch: Option<BTreeSet<String>>,
        requested_navigate: Option<BTreeSet<String>>,
        requested_permissions: BTreeSet<PermissionKind>,
    ) -> Option<MockSurface<D>>
    where
        D: Clone,
    {
        let child = self.delegate.request_open_auxiliary_webview(
            &self.surface,
            child_cell,
            requested_rights,
            requested_fetch,
            requested_navigate,
            requested_permissions,
        )?;
        Some(MockSurface::open(child, self.delegate.clone()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn cid(b: u8) -> CellId {
        let mut k = [0u8; 32];
        k[0] = b;
        CellId::derive_raw(&k, &[0u8; 32])
    }

    fn origins(list: &[&str]) -> BTreeSet<String> {
        list.iter().map(|s| s.to_string()).collect()
    }

    #[test]
    fn a_navigation_the_caps_allow_succeeds() {
        // The surface is scoped to example.com; a navigation there is ALLOWED and
        // COMMITS the URL (the trusted chrome will read it).
        let surface = SurfaceCapability::scoped(
            cid(1),
            AuthRequired::Either,
            [String::from("https://example.com")],
            [],
        );
        let mut wv = MockSurface::open(surface, CapGatedDelegate::new());

        let d = wv.navigate("https://example.com", "https://example.com/home");
        assert_eq!(d, NavigationDecision::Allow);
        assert_eq!(wv.current_url.as_deref(), Some("https://example.com/home"));
    }

    #[test]
    fn a_navigation_the_caps_dont_allow_is_refused() {
        // The same example.com-scoped surface; a navigation to evil.com is DENIED
        // and the committed URL is UNCHANGED (no spoofable chrome update).
        let surface = SurfaceCapability::scoped(
            cid(1),
            AuthRequired::Either,
            [String::from("https://example.com")],
            [],
        );
        let mut wv = MockSurface::open(surface, CapGatedDelegate::new());
        // Establish a legitimate current URL first.
        let _ = wv.navigate("https://example.com", "https://example.com/home");

        let d = wv.navigate("https://evil.com", "https://evil.com/phish");
        assert_eq!(
            d,
            NavigationDecision::Deny {
                origin: "https://evil.com".into()
            }
        );
        // The refused navigation did NOT change the committed URL.
        assert_eq!(wv.current_url.as_deref(), Some("https://example.com/home"));
    }

    #[test]
    fn a_fetch_the_caps_allow_continues_one_they_dont_is_intercepted() {
        let surface = SurfaceCapability::scoped(
            cid(2),
            AuthRequired::Either,
            [String::from("https://cdn.example.com")],
            [],
        );
        let wv = MockSurface::open(surface, CapGatedDelegate::new());

        // In-allowlist fetch continues to the network.
        assert!(wv.fetch("https://cdn.example.com").is_continue());

        // Out-of-allowlist fetch is intercepted with a cap-denied body (the page
        // gets the refusal bytes, never the real tracker resource).
        let d = wv.fetch("https://tracker.ad-network.com");
        match d {
            ResourceDecision::Intercept { body, .. } => {
                let s = String::from_utf8(body).unwrap();
                assert!(s.contains("blocked by capability"));
            }
            ResourceDecision::Continue => panic!("out-of-allowlist fetch must be intercepted"),
        }
    }

    #[test]
    fn an_attenuated_cap_narrows_what_a_sub_surface_can_fetch() {
        // Facet 2 (a) in miniature: a parent surface scoped to two origins opens a
        // child (iframe/popup) attenuated to ONE of them. The child can fetch the
        // one; it CANNOT fetch the other (narrowed); and it cannot fetch anything
        // outside the parent's reach at all.
        let parent = SurfaceCapability::scoped(
            cid(3),
            AuthRequired::Either,
            origins(&["https://a.example.com", "https://b.example.com"]),
            [],
        );
        let parent_wv = MockSurface::open(parent, CapGatedDelegate::new());

        // The child requests only a.example.com (a ⊆ {a,b}) — minted.
        let child_wv = parent_wv
            .open_auxiliary(
                cid(4),
                AuthRequired::Either,
                Some(origins(&["https://a.example.com"])),
                Some(origins(&["https://a.example.com"])),
                BTreeSet::new(),
            )
            .expect("a narrowing child must be minted");

        // The child CAN fetch its one allowed origin.
        assert!(child_wv.fetch("https://a.example.com").is_continue());
        // The child CANNOT fetch the sibling origin the parent held — narrowed.
        assert!(!child_wv.fetch("https://b.example.com").is_continue());
        // And nothing outside the parent's reach.
        assert!(!child_wv.fetch("https://c.other.com").is_continue());
    }

    #[test]
    fn a_child_cannot_amplify_beyond_its_opener() {
        // The no-amplification keystone: a child of an example.com-scoped parent
        // that asks to fetch a DIFFERENT origin (evil.com ⊄ {example.com}) is
        // REFUSED at the boundary — no child surface is minted.
        let parent = SurfaceCapability::scoped(
            cid(5),
            AuthRequired::Either,
            origins(&["https://example.com"]),
            [],
        );
        let parent_wv = MockSurface::open(parent, CapGatedDelegate::new());

        let refused = parent_wv.open_auxiliary(
            cid(6),
            AuthRequired::Either,
            Some(origins(&["https://evil.com"])), // ⊄ {example.com}
            None,
            BTreeSet::new(),
        );
        assert!(
            refused.is_none(),
            "a child asking to reach a new origin must be refused"
        );
    }

    #[test]
    fn a_child_cannot_amplify_window_rights() {
        // The window-rights half of no-amplification: a parent holding only a
        // read-only mirror (Signature) cannot open a child with broader (None)
        // window rights — refused by the REAL is_attenuation gate.
        let parent = SurfaceCapability::root(cid(7), AuthRequired::Signature);
        let parent_wv = MockSurface::open(parent, CapGatedDelegate::new());

        // Signature -> None is a WIDENING; refused.
        let refused =
            parent_wv.open_auxiliary(cid(8), AuthRequired::None, None, None, BTreeSet::new());
        assert!(
            refused.is_none(),
            "a child widening window rights must be refused"
        );

        // Signature -> Signature (equal) is fine.
        let ok =
            parent_wv.open_auxiliary(cid(9), AuthRequired::Signature, None, None, BTreeSet::new());
        assert!(ok.is_some(), "an equal/narrowing child must be minted");
    }

    #[test]
    fn permissions_are_default_deny_and_narrow() {
        // A surface carrying geolocation grants it; one without does not; a child
        // cannot gain a permission its parent lacks.
        let parent = SurfaceCapability::scoped(
            cid(10),
            AuthRequired::Either,
            [String::from("https://example.com")],
            [PermissionKind::Geolocation],
        );
        let wv = MockSurface::open(parent.clone(), CapGatedDelegate::new());

        assert_eq!(
            wv.request_permission(PermissionKind::Geolocation),
            PermissionDecision::Allow
        );
        assert_eq!(
            wv.request_permission(PermissionKind::Camera),
            PermissionDecision::Deny
        );

        // A child cannot gain Camera (parent lacks it).
        let mut want = BTreeSet::new();
        want.insert(PermissionKind::Camera);
        let refused = parent.attenuate_child(cid(11), AuthRequired::Either, None, None, want);
        assert!(
            refused.is_none(),
            "a child cannot gain a permission its parent lacks"
        );

        // A child CAN inherit Geolocation (⊆ parent's).
        let mut want_geo = BTreeSet::new();
        want_geo.insert(PermissionKind::Geolocation);
        let child = parent
            .attenuate_child(cid(12), AuthRequired::Either, None, None, want_geo)
            .expect("a child inheriting a held permission is minted");
        assert!(child.has_permission(PermissionKind::Geolocation));
    }

    #[test]
    fn authenticate_only_returns_creds_for_a_scoped_origin() {
        // A surface scoped to example.com gets a cap-scoped credential for it; a
        // wildcard surface (not scoped to any one origin) gets none.
        let scoped = SurfaceCapability::scoped(
            cid(13),
            AuthRequired::Either,
            [String::from("https://example.com")],
            [],
        );
        let scoped_wv = MockSurface::open(scoped, CapGatedDelegate::new());
        assert!(scoped_wv.authenticate("https://example.com").is_some());
        assert!(scoped_wv.authenticate("https://other.com").is_none());

        let wildcard = SurfaceCapability::root(cid(14), AuthRequired::Either);
        let wildcard_wv = MockSurface::open(wildcard, CapGatedDelegate::new());
        assert!(
            wildcard_wv.authenticate("https://example.com").is_none(),
            "a wildcard surface holds no specific credential cap"
        );
    }

    #[test]
    fn the_surface_is_a_real_firmament_surface_cap() {
        // Anti-toy: the web surface IS a firmament Capability with a Surface
        // target — not a parallel model.
        let cell = cid(20);
        let surface = SurfaceCapability::root(cell, AuthRequired::Either);
        assert!(surface.window.target.is_surface());
        assert_eq!(surface.cell(), Some(cell));
        assert_eq!(
            surface.window,
            Capability::surface(cell, AuthRequired::Either)
        );
    }
}
