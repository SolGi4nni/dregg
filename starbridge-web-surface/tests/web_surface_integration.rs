//! Integration tests — exercise the crate's PUBLIC API as an external consumer
//! (compiled as a normal dependency, so this is the standalone-crate contract).
//!
//! These pin the three behaviours the deliverable names explicitly:
//!   * a navigation the caps ALLOW succeeds;
//!   * one they DON'T is refused;
//!   * an attenuated cap narrows what a sub-surface can fetch;
//!     plus the `dregg://` end-to-end fetch + attestation verification.

use std::collections::BTreeSet;

use starbridge_web_surface::{
    AuthRequired, CapGatedDelegate, Capability, CellId, MockSurface, NavigationDecision,
    ResourceDecision, SurfaceCapability, Target, WebOfCells,
};

fn cid(b: u8) -> CellId {
    let mut k = [0u8; 32];
    k[0] = b;
    CellId::derive_raw(&k, &[0u8; 32])
}

fn origins(list: &[&str]) -> BTreeSet<String> {
    list.iter().map(|s| s.to_string()).collect()
}

#[test]
fn a_web_surface_is_a_real_firmament_surface_capability() {
    // Anti-toy: the public `SurfaceCapability.window` IS a firmament
    // `Capability{ target: Surface(cell), rights }` — the genuine handle.
    let cell = cid(1);
    let surface = SurfaceCapability::root(cell, AuthRequired::Either);
    assert_eq!(
        surface.window,
        Capability::surface(cell, AuthRequired::Either)
    );
    assert!(matches!(surface.window.target, Target::Surface { .. }));
}

#[test]
fn navigation_the_caps_allow_succeeds_and_one_they_dont_is_refused() {
    let surface = SurfaceCapability::scoped(
        cid(2),
        AuthRequired::Either,
        [String::from("https://example.com")],
        [],
    );
    let mut wv = MockSurface::open(surface, CapGatedDelegate::new());

    // ALLOW.
    assert_eq!(
        wv.navigate("https://example.com", "https://example.com/a"),
        NavigationDecision::Allow
    );
    assert_eq!(wv.current_url.as_deref(), Some("https://example.com/a"));

    // DENY — and the committed URL is unchanged (no spoofable chrome update).
    assert_eq!(
        wv.navigate("https://evil.com", "https://evil.com/x"),
        NavigationDecision::Deny {
            origin: "https://evil.com".into()
        }
    );
    assert_eq!(wv.current_url.as_deref(), Some("https://example.com/a"));
}

#[test]
fn an_attenuated_cap_narrows_what_a_sub_surface_can_fetch() {
    // The per-DOM-region cap idea (Facet 2 (a)) in miniature: a parent scoped to
    // {a, b} opens a child attenuated to {a}; the child can fetch a, not b.
    let parent = SurfaceCapability::scoped(
        cid(3),
        AuthRequired::Either,
        origins(&["https://a.example.com", "https://b.example.com"]),
        [],
    );
    let parent_wv = MockSurface::open(parent, CapGatedDelegate::new());

    let child_wv = parent_wv
        .open_auxiliary(
            cid(4),
            AuthRequired::Either,
            Some(origins(&["https://a.example.com"])),
            Some(origins(&["https://a.example.com"])),
            BTreeSet::new(),
        )
        .expect("a narrowing child is minted");

    assert!(matches!(
        child_wv.fetch("https://a.example.com"),
        ResourceDecision::Continue
    ));
    assert!(matches!(
        child_wv.fetch("https://b.example.com"),
        ResourceDecision::Intercept { .. }
    ));

    // And a child that tries to AMPLIFY to a new origin is refused outright.
    assert!(parent_wv
        .open_auxiliary(
            cid(5),
            AuthRequired::Either,
            Some(origins(&["https://c.other.com"])),
            None,
            BTreeSet::new(),
        )
        .is_none());
}

#[test]
fn dregg_ref_fetched_end_to_end_returns_attested_content() {
    // The web-of-cells facet: publish a page into a real cell, fetch its dregg://
    // ref, and verify the attestation chain end-to-end.
    let mut web = WebOfCells::new(3);
    let body = b"<!doctype html><title>cell page</title>";
    let uri = web.publish(7, body, "dregg://home");

    let (resource, chrome) = web.fetch(&uri).expect("fetch resolves");

    assert_eq!(resource.content_bytes, body);
    assert!(resource.verify().is_ok(), "the attestation must verify");
    assert!(resource.attested_root.is_v4_receipt_complete());

    // The trusted chrome is ledger-drawn (the cell id + committed URL), not the
    // page.
    assert_eq!(chrome.cell, uri.cell);
    assert_eq!(chrome.committed_url.as_deref(), Some("dregg://home"));
    assert!(chrome.finalized);
}
