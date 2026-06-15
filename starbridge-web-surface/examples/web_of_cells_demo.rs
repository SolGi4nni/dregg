//! End-to-end demo of both facets — run with:
//!
//! ```text
//! cd starbridge-web-surface && cargo run --example web_of_cells_demo
//! ```
//!
//! It shows, against the REAL dregg cap + attestation primitives:
//!
//! 1. **The embedded web surface as a cap gate** (`EMBEDDED-WEB-SURFACE.md`): a
//!    `MockSurface` (the LIBSERVO SEAM) scoped to `example.com` allows a
//!    navigation it permits, refuses one it doesn't, opens an attenuated child
//!    (an iframe/popup) that can fetch LESS than its parent, and refuses a child
//!    that tries to amplify.
//! 2. **The `dregg://` web of cells** (`DISTRIBUTED-SERVO-FACETS.md` Facet 1): a
//!    page is published into a real cell, fetched via its `dregg://` ref as an
//!    attested resource, verified end-to-end (the genuine `AttestedRoot` chain),
//!    and its trusted-path origin chrome is drawn from the ledger — so a phishing
//!    page body cannot spoof the origin badge.

use std::collections::BTreeSet;

use starbridge_web_surface::{
    AuthRequired, CapGatedDelegate, CellId, MockSurface, NavigationDecision, SurfaceCapability,
    WebOfCells,
};

fn cid(b: u8) -> CellId {
    let mut k = [0u8; 32];
    k[0] = b;
    CellId::derive_raw(&k, &[0u8; 32])
}

fn origins(list: &[&str]) -> BTreeSet<String> {
    list.iter().map(|s| s.to_string()).collect()
}

fn main() {
    println!("== Facet: the embedded web surface IS a cap gate ==\n");

    // A top-level tab scoped to example.com (and its CDN). The surface IS a real
    // firmament Capability{ target: Surface(cell), rights }.
    let tab = SurfaceCapability::scoped(
        cid(1),
        AuthRequired::Either,
        origins(&["https://example.com", "https://cdn.example.com"]),
        [],
    );
    println!(
        "tab surface cap: target.is_surface()={}, cell={:02x?}…",
        tab.window.target.is_surface(),
        &tab.cell().unwrap().0[..4]
    );

    let mut webview = MockSurface::open(tab, CapGatedDelegate::new());

    // A navigation the caps ALLOW.
    let d = webview.navigate("https://example.com", "https://example.com/home");
    println!(
        "navigate example.com -> {d:?}; committed_url={:?}",
        webview.current_url
    );

    // A navigation the caps DON'T allow (a phishing redirect).
    let d = webview.navigate("https://evil.com", "https://evil.com/phish");
    println!(
        "navigate evil.com   -> {d:?}; committed_url UNCHANGED={:?}",
        webview.current_url
    );
    assert!(matches!(d, NavigationDecision::Deny { .. }));

    // A subresource fetch the caps allow, and one they don't.
    println!(
        "fetch cdn.example.com -> continue? {}",
        webview.fetch("https://cdn.example.com").is_continue()
    );
    println!(
        "fetch tracker.ads     -> continue? {}",
        webview.fetch("https://tracker.ads").is_continue()
    );

    // Open an attenuated child (an iframe/popup) restricted to ONLY example.com —
    // the no-amplification keystone.
    let child = webview
        .open_auxiliary(
            cid(2),
            AuthRequired::Either,
            Some(origins(&["https://example.com"])),
            Some(origins(&["https://example.com"])),
            BTreeSet::new(),
        )
        .expect("a narrowing child is minted");
    println!("\nopened attenuated child (iframe/popup):");
    println!(
        "  child fetch example.com     -> continue? {}",
        child.fetch("https://example.com").is_continue()
    );
    println!(
        "  child fetch cdn.example.com -> continue? {} (NARROWED away)",
        child.fetch("https://cdn.example.com").is_continue()
    );

    // A child that tries to AMPLIFY (reach a new origin) is refused at the boundary.
    let refused = webview.open_auxiliary(
        cid(3),
        AuthRequired::Either,
        Some(origins(&["https://evil.com"])),
        None,
        BTreeSet::new(),
    );
    println!(
        "child requesting evil.com (amplify) -> minted? {}",
        refused.is_some()
    );
    assert!(refused.is_none());

    println!("\n== Facet: the dregg:// web of cells (a link is a cap, a fetch is a verified attested read) ==\n");

    let mut web = WebOfCells::new(3); // a 3-of-3 federation quorum

    // Publish a page into a real cell. NOTE the body contains a phishing string —
    // we'll see the chrome ignore it.
    let body = b"<!doctype html><h1>https://yourbank.com login</h1><p>served from a dregg cell</p>";
    let uri = web.publish(10, body, "dregg://not-your-bank");
    println!("published page; link = {}", uri.to_uri_string());

    // Fetch the dregg:// ref → an attested resource + the ledger-drawn chrome.
    let (resource, chrome) = web.fetch(&uri).expect("fetch resolves");

    // CLIENT-SIDE verification BEFORE rendering — the genuine AttestedRoot chain.
    match resource.verify() {
        Ok(()) => println!("attestation VERIFIED: content-addressed + receipt-in-stream + real receipt-stream root + quorum"),
        Err(e) => {
            println!("attestation FAILED ({e:?}) — would render 'dregg: unattested content', never the bytes");
            std::process::exit(1);
        }
    }
    println!(
        "  v4 receipt-complete? {}",
        resource.attested_root.is_v4_receipt_complete()
    );
    println!("  content_hash = {:02x?}…", &resource.content_hash[..6]);

    // The trusted-path origin chrome — drawn from the LEDGER, never the page.
    println!("\ntrusted-path origin badge (shell-drawn, page cannot reach it):");
    println!("  {}", chrome.badge());
    assert!(
        !chrome.badge().contains("yourbank.com"),
        "the page's phishing string must NOT appear in the chrome"
    );
    println!("  (the page body's 'https://yourbank.com' string does NOT appear in the badge)");

    // Show tampering is caught: a lying node hands back different bytes.
    let mut tampered = resource.clone();
    tampered.content_bytes = b"injected content".to_vec();
    println!(
        "\ntampered-bytes verify -> {:?} (rejected; page never renders)",
        tampered.verify()
    );

    println!("\nOK — both facets run on the real dregg cap + attestation primitives.");
}
