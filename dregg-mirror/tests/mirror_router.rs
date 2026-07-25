//! # The mirror's teeth.
//!
//! These drive the REAL handler (`Mirror::handle`) over the REAL `deos-view` renderer —
//! the same code path the socket serves. The trust-labelling assertions are the point:
//! that is the requirement most likely to rot, because a page keeps working perfectly
//! while its honesty quietly drains out of it.

use dregg_mirror::object::{Attestation, GateOutcome, content_addr};
use dregg_mirror::store::{MemoryStore, ObjectStore};
use dregg_mirror::uri::Kind;
use dregg_mirror::{Mirror, MirrorConfig, PageConfig, fixtures};
use http_serve::WebRequest;

const ORIGIN: &str = "dregg.gg";

/// The marker that a `deos-view` card was actually RENDERED into the page. The bare class
/// name is not that marker: it appears as a CSS selector in every page's stylesheet,
/// including the error pages that render no object at all.
const CARD_MARKUP: &str = r#"<div class="deos-card">"#;

fn cfg() -> MirrorConfig {
    MirrorConfig {
        page: PageConfig {
            origin: ORIGIN.into(),
            extension_url: "https://dregg.gg/extension".into(),
        },
        ..Default::default()
    }
}

/// A mirror holding one poll, plus that poll's full address.
fn one_poll() -> (Mirror<MemoryStore>, String) {
    let mut store = MemoryStore::new();
    let addr = store.insert(
        Kind::Poll,
        fixtures::poll(
            "Should the mirror ship?",
            &[("yes", 41), ("no", 3), ("show me first", 12)],
            30,
        ),
    );
    (Mirror::new(store, cfg()), addr)
}

fn get(m: &Mirror<MemoryStore>, path: &str) -> (u16, String) {
    let res = m.handle(&WebRequest::get(path));
    (res.status, res.body_str().into_owned())
}

// ─────────────────────────────────────────────────────────────────────────────
// RESOLUTION
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn good_address_renders_the_object() {
    let (m, addr) = one_poll();
    let (status, body) = get(&m, &format!("/poll/b3_{addr}"));
    assert_eq!(status, 200);
    assert!(body.contains("Should the mirror ship?"));
    // The object's own surface, rendered by deos-view — not markup written here.
    assert!(body.contains("deos-card"), "the deos-view card is missing");
    assert!(body.contains("show me first"));
    // The committed tally, which lives inside the content address.
    assert!(body.contains("41"));
}

#[test]
fn the_b3_tag_is_optional_in_the_path_and_mandatory_in_the_canonical_string() {
    let (m, addr) = one_poll();
    let (tagged, body_tagged) = get(&m, &format!("/poll/b3_{addr}"));
    let (bare, body_bare) = get(&m, &format!("/poll/{addr}"));
    assert_eq!((tagged, bare), (200, 200));
    assert_eq!(body_tagged, body_bare);
    assert!(body_bare.contains(&format!("dregg://poll/b3_{addr}")));
}

#[test]
fn truncated_but_unambiguous_prefix_resolves() {
    let (m, addr) = one_poll();
    // What survives being read off a truncated post: 8 hex, git-style.
    let (status, body) = get(&m, &format!("/poll/{}", &addr[..8]));
    assert_eq!(status, 200, "a unique 8-hex prefix must resolve");
    assert!(body.contains("Should the mirror ship?"));
    // And the page always hands back the FULL address, never the prefix it arrived as.
    assert!(body.contains(&format!("dregg://poll/b3_{addr}")));
}

#[test]
fn ambiguous_prefix_is_a_404_and_never_a_pick() {
    let mut store = MemoryStore::new();
    let shared = "abcdef01";
    let a = format!("{shared}{}", "1".repeat(56));
    let b = format!("{shared}{}", "2".repeat(56));
    store.insert_at(Kind::Poll, &a, fixtures::poll("first", &[("y", 1)], 1));
    store.insert_at(Kind::Poll, &b, fixtures::poll("second", &[("y", 1)], 1));
    let m = Mirror::new(store, cfg());

    let (status, body) = get(&m, &format!("/poll/{shared}"));
    assert_eq!(status, 404, "an ambiguous prefix must refuse, not pick");
    assert!(body.contains("Ambiguous address"));
    // Neither candidate's content leaked into the refusal page.
    assert!(!body.contains("first"));
    assert!(!body.contains("second"));
    // Both candidates are offered so a human can disambiguate, git-style.
    assert!(body.contains(&a));
    assert!(body.contains(&b));
}

#[test]
fn too_short_a_prefix_is_refused_not_guessed() {
    let (m, addr) = one_poll();
    let (status, body) = get(&m, &format!("/poll/{}", &addr[..6]));
    assert_eq!(status, 400);
    assert!(body.contains("Address too short"));
}

#[test]
fn unknown_kind_is_a_clean_404() {
    let (m, addr) = one_poll();
    let (status, body) = get(&m, &format!("/wombat/{addr}"));
    assert_eq!(status, 404);
    assert!(body.contains("Unknown kind"));
    // It says what it DOES know rather than guessing a renderer.
    assert!(body.contains("<code>poll</code>"));
    assert!(body.contains("will not guess"));
}

#[test]
fn unresolvable_reference_renders_an_honest_error_not_a_blank() {
    let (m, _) = one_poll();
    let (status, body) = get(&m, &format!("/poll/{}", "0".repeat(64)));
    assert_eq!(status, 404);
    assert!(body.contains("No object at that reference"));
    assert!(!body.is_empty());
    // Fail-closed, and it says so.
    assert!(body.contains("fails closed"));
}

#[test]
fn the_spec_alias_path_still_works() {
    let (m, addr) = one_poll();
    // §1's published mirror form — the one `extension/src/detect.ts` writes today. Links
    // already in the wild must keep resolving forever.
    let (status, body) = get(&m, &format!("/d/poll/b3_{addr}"));
    assert_eq!(status, 200);
    assert!(body.contains("Should the mirror ship?"));
}

#[test]
fn query_params_are_hints_and_never_reach_the_page() {
    let (m, addr) = one_poll();
    let (status, body) = get(
        &m,
        &format!("/poll/{addr}?label=TRUST%20ME%20I%20AM%20VERIFIED"),
    );
    assert_eq!(status, 200);
    assert!(
        !body.contains("TRUST ME"),
        "a query hint is never rendered (§1: hints only, never trusted)"
    );
}

#[test]
fn every_registered_kind_renders() {
    let mut store = MemoryStore::new();
    let seeded = vec![
        (
            Kind::Poll,
            store.insert(Kind::Poll, fixtures::poll("P", &[("y", 1)], 1)),
            "P",
        ),
        (
            Kind::Doc,
            store.insert(Kind::Doc, fixtures::doc("D", &["body"], None)),
            "D",
        ),
        (
            Kind::DocText,
            store.insert(Kind::DocText, fixtures::doctext("T", "text", 1)),
            "T",
        ),
        (
            Kind::Story,
            store.insert(Kind::Story, fixtures::story("S", "a room", &["go"])),
            "S",
        ),
        (
            Kind::Descent,
            store.insert(Kind::Descent, fixtures::descent("R", "ab", &[("e", 1, 2)])),
            "R",
        ),
    ];
    let m = Mirror::new(store, cfg());
    for (kind, addr, title) in seeded {
        let (status, body) = get(&m, &format!("/{kind}/{addr}"));
        assert_eq!(status, 200, "{kind} did not render");
        assert!(body.contains(title), "{kind} lost its title");
        assert!(body.contains("(trust the origin)"), "{kind} lost its tier");
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// TRUST LABELLING — the requirement most likely to rot
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn trust_tier_language_is_on_every_object_page() {
    let (m, addr) = one_poll();
    let (status, body_ok) = get(&m, &format!("/poll/{addr}"));
    assert_eq!(status, 200);

    // §5's badge, with its qualifier. The ✓ never travels alone.
    assert!(
        body_ok.contains(&format!("✓ verified by {ORIGIN} (trust the origin)")),
        "§5's tier-`server` badge text is missing or has drifted"
    );
    // The reflected tier, machine-readable (§5's `trust=` attribute).
    assert!(body_ok.contains(r#"data-trust="server""#));
    // Plain words, not a footnote: who checked, and what the reader does NOT have.
    assert!(body_ok.contains("Who checked this?"));
    assert!(body_ok.contains(&format!("{ORIGIN} checked this object. You did not.")));
    assert!(body_ok.contains("no independent evidence"));
    assert!(body_ok.contains("Nothing on this page is evidence you hold."));
    // The residual named in both directions.
    assert!(body_ok.contains("without breaking the digest"));
    assert!(body_ok.contains("stale-but-valid"));
    // §7's ladder, with the reader's rung marked.
    assert!(body_ok.contains("YOU ARE HERE"));
    assert!(body_ok.contains("ladder-here"));
}

#[test]
fn the_badge_is_never_the_extension_tiers_green() {
    let (m, addr) = one_poll();
    let (_, body) = get(&m, &format!("/poll/{addr}"));
    assert!(body.contains(r#"class="tier-badge tier-server""#));
    assert!(
        !body.contains(r#"class="tier-badge tier-extension""#),
        "the mirror must never wear the tier a reader's own agent earns"
    );
    // The one green thing on the page is the DESCRIPTION of the tier above, in the
    // upgrade block — never this page's own badge.
    let badge_line = body
        .split(r#"class="tier-badge"#)
        .nth(1)
        .expect("a badge on the page");
    assert!(badge_line.starts_with(" tier-server"));
}

#[test]
fn the_canonical_reference_and_the_extension_upgrade_are_on_the_page() {
    let (m, addr) = one_poll();
    let (_, body) = get(&m, &format!("/poll/{}", &addr[..10]));
    // The canonical string, in a field a reader can select and copy.
    assert!(body.contains(&format!(r#"value="dregg://poll/b3_{addr}""#)));
    assert!(body.contains("canonical reference"));
    // The pointer to the tier where they check it themselves.
    assert!(body.contains("Check it yourself"));
    assert!(body.contains("https://dregg.gg/extension"));
    assert!(body.contains("verified by your cipherclerk"));
    assert!(body.contains("That is the difference between this page and evidence."));
}

#[test]
fn affordances_are_inert_and_the_page_says_so() {
    let (m, addr) = one_poll();
    let (_, body) = get(&m, &format!("/poll/{addr}"));
    // The object's real affordances are still shown — the object has them.
    assert!(body.contains("data-turn=\"castBallot\""));
    // …inside a natively-disabled fieldset. No script, no DOM surgery, no dead-live button.
    assert!(body.contains(r#"<fieldset class="mirror-inert" disabled>"#));
    assert!(body.contains("Every control below is disabled on this surface"));
    assert!(body.contains("custody lives in"));
    // And the mirror ships NO affordance wire: a page with no executor must not carry
    // script that looks like it could fire one.
    assert!(
        !body.contains("<script"),
        "the mirror must not ship an affordance wire it cannot honour"
    );
}

#[test]
fn skipped_gates_are_shown_as_not_checked_never_folded_into_a_pass() {
    let (m, addr) = one_poll();
    let (_, body) = get(&m, &format!("/poll/{addr}"));
    assert!(body.contains("What the origin checked"));
    // Gate 1 ran.
    assert!(body.contains("blake3(bytes) == the address in the link"));
    // Gates 2–4 did not, and say so in those words.
    assert!(body.contains("NOT CHECKED"));
    assert!(body.contains("carried no federation attestation"));
    assert!(body.contains("not checked rather than quietly folded into a pass"));
}

#[test]
fn an_attested_object_reports_the_full_ladder() {
    let leaf = content_addr(b"a serve receipt");
    let root = dregg_mirror::object::receipt_stream_root(std::slice::from_ref(&leaf));
    let mut store = MemoryStore::new();
    let addr = store.insert_attested(
        Kind::Poll,
        fixtures::poll("attested", &[("y", 2)], 2),
        Some(Attestation {
            receipt_hash: leaf.clone(),
            receipt_set: vec![leaf],
            receipt_stream_root: root,
            threshold: 1,
            quorum_signatures: vec![dregg_mirror::object::QuorumSig {
                signer: "aa".repeat(32),
                sig: "bb".repeat(64),
            }],
            threshold_qc: None,
        }),
    );
    let m = Mirror::new(store, cfg());
    let (status, body) = get(&m, &format!("/poll/{addr}"));
    assert_eq!(status, 200);
    // No trusted committee is configured, so the structural gate ran — and the page says
    // the signatures were COUNTED, not anchored. That distinction is the whole gate.
    assert!(body.contains("signatures were COUNTED, not cryptographically anchored"));
    assert!(!body.contains("NOT CHECKED"));
}

// ─────────────────────────────────────────────────────────────────────────────
// FAIL-CLOSED
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn substituted_bytes_fail_closed_and_render_none_of_the_object() {
    let mut store = MemoryStore::new();
    let honest = fixtures::poll("the real question", &[("yes", 1), ("no", 99)], 10);
    let addr = content_addr(&honest);
    // A hostile origin serves DIFFERENT bytes under the honest address.
    store.insert_at(
        Kind::Poll,
        &addr,
        fixtures::poll("the swapped question", &[("yes", 99), ("no", 1)], 10),
    );
    let m = Mirror::new(store, cfg());

    let (status, body) = get(&m, &format!("/poll/{addr}"));
    assert_eq!(status, 502);
    assert!(body.contains("This object did not verify"));
    assert!(body.contains("blake3(bytes) == the address in the link"));
    // NOTHING of the substituted object reached the page. (`deos-card` appears as a CSS
    // SELECTOR in every page's stylesheet — the marker of a rendered card is the MARKUP.)
    assert!(!body.contains("the swapped question"));
    assert!(!body.contains(CARD_MARKUP));
    assert!(!body.contains("mirror-inert\" disabled"));
    // And the page wears the tier-`none` badge, verbatim from §5.
    assert!(body.contains("⚠ unverified — original link shown"));
    assert!(body.contains(r#"data-trust="none""#));
}

#[test]
fn kind_in_the_link_must_match_the_object() {
    let mut store = MemoryStore::new();
    // A STORY's bytes, filed (and therefore linkable) under /poll/.
    let addr = store.insert(Kind::Poll, fixtures::story("a story", "a room", &["go"]));
    let m = Mirror::new(store, cfg());

    let (status, body) = get(&m, &format!("/poll/{addr}"));
    assert_eq!(status, 502);
    assert!(body.contains("Kind mismatch"));
    assert!(!body.contains("a room"));
}

#[test]
fn unreadable_bytes_render_no_partial_guess() {
    let mut store = MemoryStore::new();
    let addr = store.insert(Kind::Poll, b"this is not an object at all".to_vec());
    let m = Mirror::new(store, cfg());

    let (status, body) = get(&m, &format!("/poll/{addr}"));
    assert_eq!(status, 502);
    assert!(body.contains("Unreadable object"));
    assert!(!body.contains(CARD_MARKUP));
}

#[test]
fn error_pages_never_wear_the_server_tiers_badge() {
    let (m, _) = one_poll();
    for path in ["/poll/00000000", "/wombat/00000000", "/poll/ab", "/nope"] {
        let (status, body) = get(&m, path);
        assert!(status >= 400, "{path} should refuse");
        assert!(
            body.contains("⚠ unverified — original link shown"),
            "{path} lost the tier-`none` badge"
        );
        // §7's ladder still prints every rung's language (that block is the same on
        // every page — it is what orients the reader). What must NOT appear is this
        // page wearing the tier-`server` badge itself.
        assert!(
            !body.contains(r#"class="tier-badge tier-server""#),
            "{path} claims a tier it did not reach"
        );
        assert!(body.contains(r#"class="tier-badge tier-none""#));
        assert!(!body.contains(CARD_MARKUP), "{path} rendered a card anyway");
        // An error page is still a real page, with the way up on it.
        assert!(body.contains("Check it yourself"));
    }
}

#[test]
fn the_mirror_only_reads() {
    let (m, addr) = one_poll();
    let res = m.handle(&WebRequest::new(
        http_serve::HttpMethod::Post,
        &format!("/poll/{addr}"),
        b"vote=1".to_vec(),
    ));
    assert_eq!(res.status, 405);
    assert!(res.body_str().contains("custody"));
}

#[test]
fn a_crafted_title_cannot_break_out_of_the_page() {
    let mut store = MemoryStore::new();
    let addr = store.insert(
        Kind::Poll,
        fixtures::object(
            "poll",
            "</title><script>alert(1)</script>",
            fixtures::text("x"),
            &[],
            None,
        ),
    );
    let m = Mirror::new(store, cfg());
    let (status, body) = get(&m, &format!("/poll/{addr}"));
    assert_eq!(status, 200);
    assert!(!body.contains("<script>alert(1)</script>"));
}

// ─────────────────────────────────────────────────────────────────────────────
// THE REST OF THE SURFACE
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn the_index_explains_the_surface_and_the_link_shape() {
    let (m, _) = one_poll();
    let (status, body) = get(&m, "/");
    assert_eq!(status, 200);
    assert!(body.contains("dregg mirror"));
    assert!(body.contains("https://dregg.gg/&lt;kind&gt;/&lt;address&gt;"));
    assert!(body.contains("An ambiguous prefix is refused, never"));
    // Every registered kind is named, and it says an unregistered one 404s.
    for k in Kind::ALL {
        assert!(body.contains(&format!("<code>{k}</code>")), "{k} unlisted");
    }
    assert!(body.contains("does not guess a renderer"));
}

#[test]
fn health_is_a_plain_probe() {
    let (m, _) = one_poll();
    let res = m.handle(&WebRequest::get("/healthz"));
    assert_eq!(res.status, 200);
    assert_eq!(res.body_str(), "ok");
}

#[test]
fn store_listing_backs_the_index_counts() {
    let (m, _) = one_poll();
    assert_eq!(m.store().list(Kind::Poll).len(), 1);
    assert_eq!(m.store().list(Kind::Story).len(), 0);
}

#[test]
fn the_gate_report_is_a_disclosure_not_a_verdict() {
    // The ladder passing server-side does NOT promote the tier: the tier names who ran
    // the gates, and here that is never the reader.
    let (m, addr) = one_poll();
    let (_, body) = get(&m, &format!("/poll/{addr}"));
    let report = dregg_mirror::object::verify(
        &m.store().get(Kind::Poll, &addr).unwrap(),
        &addr,
        &Default::default(),
    );
    assert!(!report.refused());
    assert!(matches!(report.gates[0].1, GateOutcome::Passed(_)));
    assert!(body.contains(r#"data-trust="server""#));
    assert!(!body.contains(r#"data-trust="extension""#));
}
