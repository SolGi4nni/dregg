//! **The `publish_as` gate** — publishing an EXISTING cell id onto the `dregg://`
//! web of cells, and quoting it.
//!
//! ## What was blocked
//!
//! [`WebOfCells::publish`] derives its own origin cell from a `u8` seed
//! (`seed_origin`), so there was NO entry point anywhere that published a cell id
//! the caller already holds. A live desktop cell (a `starbridge_v2::world` anchor,
//! an agent cell, a document cell) could therefore never become a `dregg://`
//! origin, which is why a whole-cell transclusion against a real desktop cell was
//! structurally uncallable: the transclusion path needs a `DreggUri` denoting THAT
//! cell, and no constructor could produce one.
//!
//! [`WebOfCells::publish_as`] is that entry point. This file is its gate.
//!
//! ## What this test asserts against, and why not `WholeCellTransclusion::embed`
//!
//! `WholeCellTransclusion::embed` lives in `starbridge-v2`, which **depends on this
//! crate** (`starbridge-v2/Cargo.toml:780`, as `web_aff`). The dependency direction
//! forbids naming it here. What `embed` actually *does* is:
//!
//! ```text
//! let surface_read = TranscludedField::include(web, source_uri)
//!     .map_err(WholeCellTransclusionError::Surface)?;
//! Ok(WholeCellTransclusion { host, source: source_uri.cell, surface_read, .. })
//! ```
//!
//! — i.e. every check `embed` performs is `TranscludedField::include`, and the rest
//! is field assignment (`starbridge-v2/src/cell_transclusion.rs:129-148`). So this
//! gate drives [`TranscludedField::include`] — `embed`'s entire verification body,
//! which lives in THIS crate — against a `publish_as` origin. The final
//! `WholeCellTransclusion::embed` call is the next commit in the chain (a
//! starbridge-v2 file this lane does not own).
//!
//! ## The teeth
//!
//! 1. a REAL desktop cell id publishes, and the quote cites **that exact cell**;
//! 2. `publish` **cannot reach** that cell id for ANY of its 256 seeds — measured,
//!    not asserted from the source (so `publish_as` is not a redundant door);
//! 3. a cell id that was **never published** yields **no quote** (the anti-forge
//!    tooth: an unpublished origin is `OriginNotFound`, never a fabricated read);
//! 4. `publish`'s own finalization behaviour is untouched by the shared body.

use starbridge_web_surface::transclusion::{TranscludedField, TransclusionError};
use starbridge_web_surface::web_of_cells::{DreggUri, FetchError, WebOfCells};
use starbridge_web_surface::CellId;

/// The demo desktop's USER anchor cell id, derived exactly as the live cockpit
/// derives it.
///
/// `starbridge_v2::world::demo_world()` seeds its three anchors through
/// `seed_demo_genesis_onto` → `w.genesis_cell(0x33, 5_000)` → `make_open_cell(0x33,
/// 5_000)` (`starbridge-v2/src/world/mod.rs:1665-1672`), which builds
/// `pk[0] = seed; pk[31] = seed.wrapping_mul(37)` and takes
/// `Cell::with_balance(pk, [0u8; 32], balance).id()` — and `Cell::with_balance`
/// sets `id = CellId::derive_raw(&public_key, &token_id)`
/// (`cell/src/cell.rs:578-580`). The balance never enters the id, so the value
/// below is **byte-identical** to `demo_world().1[2]`, computed through the REAL
/// `CellId::derive_raw`. We recompute it here rather than depending on
/// `starbridge-v2` (which depends on this crate — a cycle).
fn desktop_anchor(seed: u8) -> CellId {
    let mut pk = [0u8; 32];
    pk[0] = seed;
    pk[31] = seed.wrapping_mul(37);
    CellId::derive_raw(&pk, &[0u8; 32])
}

#[test]
fn publish_as_makes_an_existing_desktop_cell_a_dregg_origin_a_quote_can_cite() {
    let mut web = WebOfCells::new(3);
    // A cell the caller ALREADY HOLDS — the demo desktop's user anchor, born in a
    // different ledger entirely (the cockpit's `World`), never derived from a
    // web-of-cells seed.
    let user = desktop_anchor(0x33);
    let body = b"<h1>ember's desktop</h1><p>published from the live cell</p>";

    let h0 = web.height();
    let uri = web.publish_as(user, body, "dregg://desktop/user");

    // (1) THE POINT: the origin is the caller's cell, not one the surface invented.
    assert_eq!(
        uri.cell, user,
        "publish_as must publish AS the given cell, never a derived one"
    );
    assert!(
        web.height() > h0,
        "the federation attestation height advanced"
    );

    // (2) The `dregg://` fetch resolves and the attested read verifies against the
    //     federation's own committee — the genuine chain, unchanged by the new door.
    let (resource, chrome) = web.fetch(&uri).expect("the published cell resolves");
    assert_eq!(resource.content_bytes, body);
    assert!(resource.verify_anchored(&web.committee()).is_ok());
    assert_eq!(chrome.cell, user);
    assert_eq!(
        chrome.committed_url.as_deref(),
        Some("dregg://desktop/user")
    );
    assert!(chrome.finalized, "the read is quorum-finalized");

    // (3) THE GATE — `WholeCellTransclusion::embed`'s entire verification body
    //     (`TranscludedField::include`) succeeds against a cell that came from
    //     OUTSIDE this crate. This is the call that was structurally impossible
    //     before `publish_as`: there was no way to obtain a `DreggUri` for `user`.
    let quote = TranscludedField::include(&web, &uri)
        .expect("a whole-cell embed of a live desktop cell must open");

    // The quote cites THAT EXACT CELL — not a seed-derived stand-in.
    assert_eq!(
        quote.cite().source.cell,
        user,
        "the citation must name the caller's cell"
    );
    assert_eq!(
        quote.quoted_bytes(),
        body,
        "the quote shows the source bytes"
    );
    assert!(quote.cite().finalized, "the citation is a finalized read");
    assert!(quote.verify().is_ok(), "the provenance recomputes");
    assert_eq!(
        quote.cite().content_hash,
        *blake3::hash(body).as_bytes(),
        "the citation pins the content address of the published bytes"
    );
}

#[test]
fn publish_cannot_reach_a_desktop_cell_id_for_any_seed() {
    // Why `publish_as` is not a redundant door, MEASURED rather than read off the
    // source: run the real `publish` for every one of its 256 possible seeds and
    // collect the origin cells it can produce. The desktop anchors are in none of
    // them — `publish`'s derivation (`pk[31] = seed * 11`) and the desktop's
    // (`pk[31] = seed * 37`) are different families, so no seed names a live cell.
    let mut web = WebOfCells::new(1);
    let mut reachable = Vec::with_capacity(256);
    for seed in 0u8..=255 {
        reachable.push(web.publish(seed, b"x", "dregg://probe").cell);
    }
    for anchor_seed in [0x11u8, 0x22, 0x33, 0xEE] {
        let anchor = desktop_anchor(anchor_seed);
        assert!(
            !reachable.contains(&anchor),
            "publish reached desktop anchor {anchor_seed:#x} — the premise is wrong"
        );
    }
}

#[test]
fn a_cell_that_was_never_published_yields_no_quote() {
    // THE ANTI-FORGE TOOTH. `publish_as` opens a door for a caller-supplied cell id;
    // it must not make an ARBITRARY cell id quotable. A cell that was never
    // published has no committed content and no serve receipt, so the fetch refuses
    // at the origin and no provenance is ever opened.
    let mut web = WebOfCells::new(3);
    let published = desktop_anchor(0x33);
    let _ = web.publish_as(published, b"real", "dregg://desktop/user");

    let never = desktop_anchor(0x44);
    assert_ne!(never, published);
    match TranscludedField::include(&web, &DreggUri::new(never)) {
        Ok(_) => panic!("an unpublished cell must not be quotable"),
        Err(e) => assert_eq!(e, TransclusionError::Fetch(FetchError::OriginNotFound)),
    }
    assert_eq!(
        web.fetch(&DreggUri::new(never)),
        Err(FetchError::OriginNotFound)
    );
}

#[test]
fn publish_and_publish_as_do_not_drift() {
    // The two doors share one commit/finalize body; the only difference is where the
    // origin cell id comes from. Publishing the SAME bytes through each must produce
    // the same served/finalized shape — same content hash, same finalized status,
    // same committed URL binding — differing only in the origin cell.
    let body = b"<p>one body, two doors</p>";

    let mut a = WebOfCells::new(3);
    let seeded = a.publish(9, body, "dregg://same");
    let (ra, ca) = a.fetch(&seeded).expect("seeded origin resolves");

    let mut b = WebOfCells::new(3);
    let as_uri = b.publish_as(desktop_anchor(0x55), body, "dregg://same");
    let (rb, cb) = b.fetch(&as_uri).expect("caller-supplied origin resolves");

    assert_eq!(ra.content_bytes, rb.content_bytes);
    assert_eq!(ra.content_hash, rb.content_hash);
    assert_eq!(ca.committed_url, cb.committed_url);
    assert_eq!(ca.finalized, cb.finalized);
    assert_eq!(ca.rights, cb.rights, "same surface rights lineage");
    assert_ne!(ca.cell, cb.cell, "different origins, as intended");
    assert!(TranscludedField::include(&a, &seeded).is_ok());
    assert!(TranscludedField::include(&b, &as_uri).is_ok());
}

#[test]
fn republishing_the_same_cell_serves_the_new_bytes() {
    // A caller-supplied cell id can be published MORE THAN ONCE (unlike a seeded
    // origin, whose `insert_cell` would refuse a duplicate). The node's byte and URL
    // stores must be re-pointed, not appended — otherwise the fetch would find the
    // FIRST entry and serve bytes the origin no longer commits, which the serve-turn
    // binding would then refuse as `ContentDoesNotMatchCommitment`.
    let mut web = WebOfCells::new(3);
    let cell = desktop_anchor(0x66);
    let _ = web.publish_as(cell, b"v0", "dregg://doc/v0");
    let uri = web.publish_as(cell, b"v1", "dregg://doc/v1");

    let (resource, chrome) = web.fetch(&uri).expect("the republished cell resolves");
    assert_eq!(resource.content_bytes, b"v1".to_vec());
    assert_eq!(chrome.committed_url.as_deref(), Some("dregg://doc/v1"));
    assert!(TranscludedField::include(&web, &uri).is_ok());
}
