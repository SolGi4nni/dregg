//! THE MARKETING SITE REACHES THE DEPLOYED GAMES — the last hop of the funnel, driven.
//!
//! `descent_funnel.rs` closed the joint *inside* the served app (the game host's own landing links
//! `/descent/play`). The hop before it was still severed: **the marketing landing**
//! (`site/root/index.html`, deployed at `/`) never linked the running games at all. Its
//! "Play with it" section listed only the in-tab WebAssembly surfaces — deos, cards, explorer,
//! light-client, transclusion, atlas, gpui — so a visitor who arrived at the front door could not
//! reach The Descent, the offering catalog, or the no-cheat board from anywhere on the page.
//!
//! This suite asserts the reachability AND that what is linked is real:
//!
//! 1. **The three deployed surfaces are linked** from the landing (`/descent/play`, `/offerings`,
//!    `/descent`).
//! 2. **Every game link on the landing resolves to a real route** — each linked path is driven
//!    against the REAL merged app (`make_app`, axum `oneshot`) and must serve, so a marketing link
//!    at a path this server does not mount is RED here rather than a 404 for a visitor.
//! 3. **The tiles are well-formed** — the anchors/spans the section adds are balanced, and each
//!    game tile carries the same eyebrow/name/desc/go shape as the tiles already there.
//!
//! The exclusion legs are what make this non-vacuous: an unmounted path drives to a NON-2xx through
//! the same helper (so leg 2 discriminates), and the landing must NOT claim the hosted games run
//! client-side (the section's in-tab claim is scoped, not extended over a server-hosted surface).

use axum::body::Body;
use axum::http::{Request, StatusCode};
use tower::ServiceExt; // oneshot

use dreggnet_web::{DESCENT_PLAY_PATH, make_app};

/// The live host serving the games: a Tailscale Funnel in front of the `dreggnet-web-server`
/// systemd user unit on hbox (`deploy/games/dregg-web-games-funnel.service`;
/// `docs/LIVE-SURFACE-TRUST.md` §"Web games"). `demo.dregg.net` is the PLANNED product subdomain
/// (`docs/DEPLOY-PLAN.md` Phase 0) — linking it today would be a dead link, so the landing carries
/// the surface that actually answers.
const GAME_HOST: &str = "https://hbox-dregg.skunk-emperor.ts.net";

fn landing_html() -> String {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../site/root/index.html")
        .canonicalize()
        .expect("the marketing landing exists on disk");
    std::fs::read_to_string(&path).expect("the marketing landing reads")
}

/// Every `href` on the landing that points at the live game host, as its PATH.
fn linked_game_paths(html: &str) -> Vec<String> {
    let mut out = Vec::new();
    for (_, rest) in html
        .match_indices("href=\"")
        .map(|(i, m)| (i, &html[i + m.len()..]))
    {
        let Some(end) = rest.find('"') else { continue };
        let href = &rest[..end];
        if let Some(path) = href.strip_prefix(GAME_HOST) {
            let path = if path.is_empty() { "/" } else { path };
            if !out.iter().any(|p| p == path) {
                out.push(path.to_string());
            }
        }
    }
    out
}

async fn status_of(app: &axum::Router, uri: &str) -> StatusCode {
    app.clone()
        .oneshot(Request::builder().uri(uri).body(Body::empty()).unwrap())
        .await
        .unwrap()
        .status()
}

/// **THE FLAW.** The landing links the three deployed game surfaces. Before the fix it linked none
/// of them — grepping `site/root/index.html` for `descent`, `offerings`, or the game host returned
/// nothing, and the running games were unreachable from the front door.
#[test]
fn the_landing_links_the_three_deployed_game_surfaces() {
    let html = landing_html();
    let linked = linked_game_paths(&html);

    for (path, what) in [
        (DESCENT_PLAY_PATH, "the playable Descent"),
        (
            "/offerings",
            "the offering catalog (council / market / tug / automatafl)",
        ),
        ("/descent", "the re-verified no-cheat board"),
    ] {
        assert!(
            linked.iter().any(|p| p == path),
            "the landing must link {what} at `{path}`; it links {linked:?}"
        );
    }
}

/// **EVERY GAME LINK RESOLVES TO A REAL ROUTE.** Each path the landing points at is driven against
/// the real merged app — a marketing link at a path this server does not mount fails here.
#[tokio::test]
async fn every_game_link_on_the_landing_serves_on_the_real_app() {
    let html = landing_html();
    let linked = linked_game_paths(&html);
    assert!(!linked.is_empty(), "the landing links the game host at all");

    let app = make_app();
    for path in &linked {
        let status = status_of(&app, path).await;
        assert!(
            status.is_success(),
            "the landing links `{path}`, which the served app answers {status}"
        );
    }

    // NON-VACUOUS: the same helper discriminates — an unmounted path is not a success.
    let bogus = status_of(&app, "/definitely-not-a-mounted-surface").await;
    assert!(
        !bogus.is_success(),
        "the route check has teeth (an unmounted path answered {bogus})"
    );
}

/// **WELL-FORMED, AND HONEST ABOUT WHERE IT RUNS.** The added tiles reuse the existing tile shape
/// (balanced anchors, the four spans), and the section's "runs in your tab / nothing leaves your
/// machine" claim stays scoped to the WebAssembly group — a server-hosted game must not be sold as
/// client-side.
#[test]
fn the_game_tiles_are_well_formed_and_scoped_honestly() {
    let html = landing_html();

    // Balanced markup across the whole landing (the cheap structural check: what we add closes).
    let opens = html.matches("<a ").count() + html.matches("<a>").count();
    let closes = html.matches("</a>").count();
    assert_eq!(opens, closes, "every anchor on the landing closes");
    let div_opens = html.matches("<div ").count() + html.matches("<div>").count();
    let div_closes = html.matches("</div>").count();
    assert_eq!(div_opens, div_closes, "every div on the landing closes");
    let span_opens = html.matches("<span ").count() + html.matches("<span>").count();
    let span_closes = html.matches("</span>").count();
    assert_eq!(span_opens, span_closes, "every span on the landing closes");

    // Each game tile mirrors the tiles already there rather than inventing a component.
    for path in linked_game_paths(&html) {
        let anchor = format!("<a class=\"tile\" href=\"{GAME_HOST}{path}\">");
        let start = html.find(&anchor).unwrap_or_else(|| {
            panic!("`{path}` is linked from a tile, matching the existing tiles")
        });
        let tile = &html[start..start + html[start..].find("</a>").expect("the tile closes")];
        for cls in ["tile__eyebrow", "tile__name", "tile__desc", "tile__go"] {
            assert!(
                tile.contains(cls),
                "the `{path}` tile carries `{cls}` like its neighbours"
            );
        }
    }

    // The in-tab claim is SCOPED — it may not blanket a section that now hosts server-side games,
    // in the intro OR in the heading above it.
    assert!(
        !html.contains("Each surface below loads a verified executor compiled to WebAssembly"),
        "the blanket in-tab claim must be scoped once hosted surfaces join the section"
    );
    assert!(
        !html.contains("Everything here is live, in your tab"),
        "the section heading must not claim in-tab for the hosted group either"
    );
    assert!(
        html.contains("hosted devnet"),
        "the hosted group is labelled as hosted, not sold as client-side"
    );
}
