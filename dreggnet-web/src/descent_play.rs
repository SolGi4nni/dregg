//! # `descent_play` — the Lean-authored Descent, playable in a plain browser.
//!
//! `GET /descent/play` is the flagship web front door. It offers the SAME
//! `dreggnet_offerings::native_descent::NativeDescentOffering` through two engines, and the reader
//! picks which one runs it ([`Engine`]):
//!
//! * **`?engine=` absent — the SERVER, and this is the default.** The offering runs here and the
//!   page is `/offerings/descent/session/…`: plain HTML, one form POST per verb, nothing
//!   downloaded, works with JavaScript off.
//! * **`?engine=browser` — the reader's own tab, opted into by name.** wasm `NativeDescentWorld`, a
//!   transport wrapper around the same offering, so every click still crosses the same
//!   executor-backed `Offering::advance` boundary as Discord, Telegram, and `/offerings/descent`.
//!
//! **Why it is opt-in.** Running the whole ruleset in a tab costs a tens-of-megabytes one-time
//! download and a visibly slower first paint, and it used to be imposed on every visitor who
//! pressed the flagship CTA — on a deployment with no bundle, that CTA was a dead end reading *"The
//! native WebAssembly artifact is unavailable; no substitute game was opened"* while a complete,
//! working, server-side copy of the same game sat one URL away and was never mentioned.
//!
//! **What the browser engine BUYS**, so the opt-in has a reason attached rather than being a toggle
//! nobody understands: it is the mode where you do not have to trust this server about your run. The
//! tab verifies today's drand beacon by BLS pairing ITSELF before it will open a day
//! (`NativeDescentWorld.fromBeacon`, fail-closed), it replays its own receipts locally (`Verify full
//! record`), and the run lives in `localStorage` rather than in this server's session store — where
//! the hosted page states outright that your moves, the dungeon and the result all live here and
//! anyone with the link can read them. That is the whole of the difference, and it is the only part
//! worth a download.
//!
//! The installed game program is the checked-in Lean emission. This module contains presentation
//! and persistence glue only: it does not reproduce a move rule.
//!
//! ## What a deployment has to serve (the funnel's contract)
//!
//! The browser engine's bundle is a BUILD OUTPUT, never a committed blob — `wasm/pkg/.gitignore` is
//! a single `*`, so a fresh clone has none. Build it with `scripts/build-descent-wasm.sh` (the one
//! build path: the flag pair, the name-section strip, the provenance stamp, and the freshness gate)
//! and point [`DESCENT_PLAY_ASSET_DIR`](play_asset_dirs) at the resulting directory. Three routes
//! read out of it and nothing else does: `dregg_wasm.js`, `dregg_wasm_bg.wasm`, and `snippets/**`.
//! A deployment that skips the build is not broken — [`browser_bundle_present`] answers `false`, the
//! door says the browser engine is unavailable here, and the server engine carries the page.
//!
//! The browser retains a versioned public-input record in `localStorage`. Reopening imports that
//! record only by fresh native replay and exact receipt/state/root comparison. Ordinary in-progress
//! play never uploads the move tape; but a run played to its **terminal settlement** (`flee`)
//! AUTO-ANCHORS — the completed record is submitted once to `/descent/native/submit`, so the run
//! reaches the day's no-cheat leaderboard (a crowned exit ranks; every exact settlement gets its
//! share card) without a separate manual publish. The manual "Publish verified run" button stays
//! as an explicit re-submit. A `localStorage` mark keeps a reload from re-submitting; the server
//! replay-gate is unchanged, so a forged/invalid record is refused exactly as before and never
//! ranks.
//!
//! ## Security posture — the `/tg/link` review's discipline (`docs/TG-LINK-SECURITY-REVIEW-2026-07-18.md`)
//!
//! Every script the page loads is **same-origin** (the bootstrap, wasm glue, and generated snippets),
//! so [`PLAY_CSP`] can be strict: `script-src 'self' 'wasm-unsafe-eval'` (the `'wasm-unsafe-eval'` is
//! the one concession WebAssembly instantiation needs — NOT `'unsafe-eval'`, NOT `'unsafe-inline'`
//! for scripts), `connect-src 'self'` (the glue fetches the `.wasm` same-origin), and no CDN. This
//! closes the "a CDN/MITM serves attacker JS" hole exactly as the link-page review did — the whole
//! point of serving the wasm bundle from our own origin, never `esm.sh` / a public wasm CDN.
//!
//! The only generated browser artifact is `wasm/pkg`, rebuilt by the games deployment before the
//! native server binary. The server first honors `DESCENT_PLAY_ASSET_DIR`, then a vendored asset
//! directory, then the workspace `wasm/pkg`.
//!
//! ⚠ MISSING wasm fails closed with a visible notice (503, tested). **STALE wasm does not, and
//! this line used to claim it did.** Nothing here checks an mtime, a hash, or a manifest — and
//! the cost of that false claim is measured, not hypothetical: the served bundle sat at
//! `PORTABLE_VERSION = 1` for five days while the server moved to 3 and hard-refuses it, and
//! `NativeDescentWorld.fromBeacon` — which this file calls on every live-beacon day — was not in
//! the binary at all. The hero "Play" CTA threw a TypeError before the game opened, silently,
//! because a sentence in a doc-comment was standing in for a check nobody had written.
//!
//! The BUILD side is now covered: `scripts/build-web-artifacts.sh` stamps
//! `dregg-wasm-provenance.json` (a sha256 over the wasm32 local-crate closure) and
//! `scripts/check-wasm-freshness.sh` fails on a changed source, a swapped artifact, or missing
//! provenance. The SERVE side is still open: this handler does not read that provenance. Wiring
//! it — `build.rs` stamps `DREGG_GIT_HEAD`, this file compares against the JSON beside the bundle
//! and fails closed on mismatch — is the remaining half, and it is the half that would have
//! caught the five days.

use std::path::{Component, Path as FsPath, PathBuf};

use axum::{
    Router,
    extract::Path as AxumPath,
    http::{StatusCode, header},
    response::{Html, IntoResponse, Response},
    routing::get,
};
use dreggnet_offerings::native_descent::{DayWorld, NativeDescentOffering};
use procgen_dregg::beacon::DailyBeacon;

/// The strict Content-Security-Policy for the play page. `'wasm-unsafe-eval'` is the single
/// concession WebAssembly instantiation requires (it is NOT `'unsafe-eval'` and does NOT loosen JS
/// eval); everything the page loads is same-origin, so scripts get no `'unsafe-inline'` and there is
/// no CDN origin. `connect-src 'self'` is what the wasm glue's same-origin `fetch` of the `.wasm`
/// blob needs; `style-src 'unsafe-inline'` covers the site `<style>` + the element's closed-shadow
/// stylesheet (DOM `<style>` text, not a script).
const PLAY_CSP: &str = "default-src 'none'; \
    script-src 'self' 'wasm-unsafe-eval'; \
    style-src 'unsafe-inline'; \
    connect-src 'self'; \
    img-src 'self' data:; \
    font-src 'self'; \
    base-uri 'none'; object-src 'none'; form-action 'none'; \
    frame-ancestors 'none'";

/// The `text/javascript` content-type every served module carries (same string the sibling
/// same-origin-asset routes use).
const JS_CT: &str = "text/javascript; charset=utf-8";

/// The play page's query string. One field, and it is the engine opt-in
/// ([`Engine::from_query`]); `serde` defaults it to `None`, so a bare `/descent/play` is the server
/// engine.
#[derive(Debug, Default, serde::Deserialize)]
pub(crate) struct PlayQuery {
    /// `browser` (or `wasm`) selects the in-tab WebAssembly executor. Anything else is the server.
    #[serde(default)]
    engine: Option<String>,
}

/// The route serving TODAY's resolved day as JSON — the same-origin descriptor the bootstrap reads
/// so the page opens the day the BOARD is keeping score on, not a fixture.
const DAY_JSON_PATH: &str = "/descent/play/static/day.json";

/// **Build the playable-Descent router.** Additive + state-free — merge it onto the same app as
/// [`descent_router`](crate::descent_router) / [`router`](crate::router). Serves:
/// - `GET /descent/play` — the strict-CSP native game shell;
/// - `GET /descent/play/static/app.js` — the same-origin native controller;
/// - `GET /descent/play/static/actions.js` — the presentation-only accessible action menu;
/// - `GET /descent/play/static/dregg_wasm.js` — the vendored wasm glue (or a placeholder);
/// - `GET /descent/play/static/dregg_wasm_bg.wasm` — the vendored wasm blob (or an honest `503`).
/// - `GET /descent/play/static/snippets/*` — wasm-bindgen's generated same-origin JS imports.
pub fn descent_play_router() -> Router {
    Router::new()
        .route("/descent/play", get(get_descent_play))
        .route("/descent/play/static/app.js", get(get_play_app_js))
        .route("/descent/play/static/actions.js", get(get_play_actions_js))
        .route(DAY_JSON_PATH, get(get_play_day_json))
        .route(
            "/descent/play/static/dregg_wasm.js",
            get(get_play_wasm_glue),
        )
        .route(
            "/descent/play/static/dregg_wasm_bg.wasm",
            get(get_play_wasm_blob),
        )
        .route(
            "/descent/play/static/snippets/{*path}",
            get(get_play_wasm_snippet),
        )
}

/// `GET /descent/play` — the play page shell. No executable text is interpolated into the page;
/// the strict-CSP same-origin controller builds the live surface with DOM text nodes.
///
/// ⚑ **The one dynamic identity input**: a browser holding a CLAIMED identity
/// ([`crate::seed_identity`]) gets its public key rendered into `data-claimed-actor`, and
/// [`NATIVE_PLAY_APP_JS`]'s `browserActor()` prefers it over the pseudonym it would otherwise mint
/// into `localStorage`. That is what makes a native run's actor — the name bound into the run's
/// hash chain and printed on the native board — a thing the player can reproduce from 24 words
/// instead of losing with their site data. A visitor with no claim is byte-for-byte unaffected: the
/// attribute is absent and the old minted pseudonym is used.
///
/// ⚑ **The engine is chosen by `?engine=`, and it defaults to the SERVER.** In-browser execution is
/// a large one-time download and a slower start, so it is opted into by name
/// ([`Engine::from_query`]) rather than imposed on everyone who presses the flagship CTA. Every
/// other value — absent, empty, misspelt — lands on the server engine, which is the direction a
/// default should fail in.
async fn get_descent_play(
    headers: axum::http::HeaderMap,
    axum::extract::Query(query): axum::extract::Query<PlayQuery>,
) -> Response {
    let claimed = crate::seed_identity::claimed_pubkey(&headers);
    let engine = Engine::from_query(query.engine.as_deref());
    let mut response = (
        [(header::CONTENT_SECURITY_POLICY, PLAY_CSP)],
        Html(shell_page(claimed.as_deref(), engine)),
    )
        .into_response();
    // The page now varies by cookie. Without this a shared cache could serve one player's claimed
    // actor to the next browser through the door.
    if claimed.is_some() {
        response.headers_mut().insert(
            header::CACHE_CONTROL,
            header::HeaderValue::from_static("private, no-store"),
        );
    }
    response
}

/// `GET /descent/play/static/app.js` — the bootstrap module, served SAME-ORIGIN so the strict CSP
/// forbids inline script (a CDN swap / XSS of the mount glue has no foothold).
async fn get_play_app_js() -> impl IntoResponse {
    ([(header::CONTENT_TYPE, JS_CT)], NATIVE_PLAY_APP_JS)
}

async fn get_play_actions_js() -> impl IntoResponse {
    (
        [(header::CONTENT_TYPE, JS_CT)],
        include_str!("../assets/descent-play-actions.mjs"),
    )
}

/// `GET /descent/play/static/day.json` — **TODAY'S REAL DAY**, as the descriptor the in-page
/// resolver opens the world from.
///
/// This closes the third joint of the funnel. The page used to open a FIXED demo day: a hardcoded
/// `dregg://descent/b3_de5ce0` whose epoch the client derived by hashing the addr tail, so the
/// served game was a fixture world decoupled from the board's — you could play it, but your run
/// belonged to no day anyone was scoring. The day is now resolved from
/// [`crate::descent::todays_day`] — the SAME [`procgen_dregg::descent_day`] helper the board and the
/// Discord bot resolve. The committed epoch remains public provenance; the in-tab
/// `NativeDescentWorld` wraps the distinct Lean-native
/// [`NativeDescentOffering`](dreggnet_offerings::native_descent::NativeDescentOffering) and derives
/// its normalized seed from this same committed day. Its record therefore goes to
/// `/descent/native/submit`, never the procgen choice-tape endpoint.
///
/// `no-store`: the day rolls at UTC midnight, and a cached descriptor would pin a stale world.
async fn get_play_day_json() -> Response {
    let day = crate::descent::todays_day();
    let mut body = serde_json::json!({
        "key": day.key,
        "uri": day.descent_uri(),
        // Full committed-day provenance. The native game does not consume this as a procgen scene;
        // it consumes `nativeSeed` below under its own Lean-authored ruleset.
        "epochHex": day.epoch_hex(),
        "seedTag": day.seed_tag(),
        // `NativeDescentOffering::open` performs the canonical `% 251 + 1`
        // normalization. Publishing the raw committed prefix keeps that one
        // normalization in the game boundary rather than mirroring it here.
        "nativeSeed": native_seed_for_day(&day),
        "utcDay": day.utc_day,
        // HONEST PROVENANCE, carried so the surface can never render the offline day as a fresh
        // reveal: `beacon` = a BLS-verified drand round, `offline-date` = the date-derived day.
        "source": if day.source.is_live_beacon() { "beacon" } else { "offline-date" },
    });
    // ⚑ BEACON-BIND THE TAB. When today resolved to a verified beacon, hand the browser the raw
    // drand `(round, signature)` pair so it opens `NativeDescentWorld.fromBeacon` and runs the BLS
    // pairing check ITSELF (fail-closed) — the run's banked-relic provenance root is then bound to
    // a revealed round, unpredictable until it matured, instead of the pre-computable deploy seed.
    // Absent (the offline day) the fields are omitted and the tab opens the seed-derived practice
    // world under its honest `offline-date` label. The signature is not trusted: a forged pair does
    // not verify in the tab, so there is no world and no day (exactly the offering's own tooth).
    if let Some(beacon) = play_beacon(&day) {
        body["round"] = serde_json::json!(beacon.round);
        body["signatureHex"] = serde_json::json!(lower_hex(&beacon.signature));
    }
    // ⚑ THE DAY'S GUARDIANS. The map — relic homes AND per-floor guardian vitality — is drawn from
    // the committed day-seed, so the vitality table is a DAY FACT, not a constant, and the page
    // cannot carry it as a literal. Published here from the offering the tab is about to open
    // (`todays_day_world`), so the meter the browser sizes is sized against the guardian the
    // executor will actually make it fight. Omitted when no map resolved: the tab then opens no
    // world rather than drawing day 0's guardians over today's dungeon.
    if let Some(world) = todays_day_world(&day) {
        body["guardHp"] = serde_json::json!(world.ghp);
    }
    (
        [
            (header::CONTENT_TYPE, "application/json; charset=utf-8"),
            (header::CACHE_CONTROL, "no-store"),
        ],
        body.to_string(),
    )
        .into_response()
}

fn native_seed_for_day(day: &procgen_dregg::descent_day::DescentDay) -> u32 {
    let bytes = day.seed.as_bytes();
    u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]])
}

/// The day's raw drand pair **exactly when the tab will open `fromBeacon` on it**: today resolved
/// to a verified beacon AND this process still holds that beacon. One helper so the descriptor,
/// the shell, and the published map cannot disagree about which world the tab is about to deploy.
fn play_beacon(day: &procgen_dregg::descent_day::DescentDay) -> Option<DailyBeacon> {
    day.source
        .is_live_beacon()
        .then(crate::descent::todays_live_beacon)
        .flatten()
}

/// **TODAY's drawn map — resolved by the OFFERING the tab is about to open, not mirrored.**
///
/// The Descent's map is a function of the committed day-seed: which floor each relic is minted on,
/// and **how much vitality each floor's guardian has**. Sixteen maps exist and day 0 is one of
/// them, so a page carrying `descent::guard_hp`'s day-0 table draws a guardian meter that is wrong
/// on fifteen days in sixteen — a `1/1` bar under a guardian that takes two blows, and a "one
/// strike and the hoard opens" reading that costs the player the light to discover.
///
/// This asks [`NativeDescentOffering::day_world_for_seed`] under the SAME day binding the tab uses
/// (`fromBeacon` on a live beacon day, else the seed-derived practice world) with the SAME native
/// seed the descriptor publishes, so the served table is the table the deployed session plays.
/// `None` — an unverifiable beacon — publishes no map, and the tab then opens no world, which is
/// the same fail-closed answer `fromBeacon` itself gives.
fn todays_day_world(day: &procgen_dregg::descent_day::DescentDay) -> Option<DayWorld> {
    let offering = match play_beacon(day) {
        Some(beacon) => NativeDescentOffering::on_beacon(&beacon).ok()?,
        None => NativeDescentOffering::new(),
    };
    offering
        .day_world_for_seed(u64::from(native_seed_for_day(day)))
        .ok()
}

/// The day's guardian-vitality table as the comma-joined list the shell's `data-guard-hp` carries
/// (empty when no map resolved — the tab then refuses rather than guessing day 0).
fn todays_guard_hp_attr(day: &procgen_dregg::descent_day::DescentDay) -> String {
    todays_day_world(day)
        .map(|world| {
            world
                .ghp
                .iter()
                .map(u64::to_string)
                .collect::<Vec<_>>()
                .join(",")
        })
        .unwrap_or_default()
}

/// Lowercase-hex encode the day's beacon signature for the tab's `fromBeacon` call.
fn lower_hex(bytes: &[u8]) -> String {
    let mut out = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        out.push(char::from_digit(u32::from(byte >> 4), 16).expect("nibble is a hex digit"));
        out.push(char::from_digit(u32::from(byte & 0x0f), 16).expect("nibble is a hex digit"));
    }
    out
}

/// `GET /descent/play/static/dregg_wasm.js` — the vendored wasm glue (`wasm-pack --target web`).
/// Absent → [`WASM_GLUE_PLACEHOLDER_JS`] (its default `init` throws), so the bootstrap degrades to
/// an honest notice. Its default init fetches `dregg_wasm_bg.wasm` relative to THIS url, i.e.
/// `/descent/play/static/dregg_wasm_bg.wasm` (the same-origin blob route below).
async fn get_play_wasm_glue() -> Response {
    match read_play_asset("dregg_wasm.js") {
        Some(bytes) => ([(header::CONTENT_TYPE, JS_CT)], bytes).into_response(),
        None => ([(header::CONTENT_TYPE, JS_CT)], WASM_GLUE_PLACEHOLDER_JS).into_response(),
    }
}

/// `GET /descent/play/static/dregg_wasm_bg.wasm` — the vendored wasm blob, served
/// `application/wasm` (so `WebAssembly.instantiateStreaming` accepts it). Absent → an honest `503`
/// naming the `wasm-pack` step, never a broken `200`.
///
/// NOTE: this reads the (large) blob from disk per request via `std::fs`. That is fine for the demo
/// server + a low-traffic play page; a production deployment should front the `static/` prefix with
/// a caching static file server (as `site/` already serves `pkg/`), which this route's fixed paths
/// make a drop-in.
async fn get_play_wasm_blob() -> Response {
    match read_play_asset("dregg_wasm_bg.wasm") {
        Some(bytes) => ([(header::CONTENT_TYPE, "application/wasm")], bytes).into_response(),
        None => (
            StatusCode::SERVICE_UNAVAILABLE,
            [(header::CONTENT_TYPE, "text/plain; charset=utf-8")],
            "The Descent WebAssembly bundle (dregg_wasm_bg.wasm) is not vendored on this deployment.\n\
             Build it with `wasm-pack build wasm --target web --out-dir pkg --release`.\n\
             See dreggnet-web/src/descent_play.rs.",
        )
            .into_response(),
    }
}

/// wasm-bindgen may emit tiny `snippets/<crate-hash>/inlineN.js` modules and import them from the
/// top-level glue. Serve only relative, normal path components below the generated `snippets/`
/// directory; traversal, absolute paths, and non-JavaScript requests fail closed.
async fn get_play_wasm_snippet(AxumPath(path): AxumPath<String>) -> Response {
    match read_play_snippet(&path) {
        Some(bytes) => ([(header::CONTENT_TYPE, JS_CT)], bytes).into_response(),
        None => (
            StatusCode::NOT_FOUND,
            [(header::CONTENT_TYPE, "text/plain; charset=utf-8")],
            "Unknown Descent WebAssembly snippet.\n",
        )
            .into_response(),
    }
}

/// Ordered generated-asset roots. An explicit deployment override is exclusive
/// (and therefore fail-closed when wrong); the normal development/deployment path
/// accepts either deliberately vendored assets or the freshly built wasm workspace.
fn play_asset_dirs() -> Vec<PathBuf> {
    if let Ok(dir) = std::env::var("DESCENT_PLAY_ASSET_DIR")
        && !dir.trim().is_empty()
    {
        return vec![PathBuf::from(dir.trim())];
    }
    vec![
        PathBuf::from(concat!(env!("CARGO_MANIFEST_DIR"), "/assets/descent")),
        PathBuf::from(concat!(env!("CARGO_MANIFEST_DIR"), "/../wasm/pkg")),
    ]
}

/// Read a vendored play asset by its fixed basename (never user input — each route passes a literal,
/// so there is no path-traversal surface). `None` when the artifact has not been vendored yet.
fn read_play_asset(name: &str) -> Option<Vec<u8>> {
    play_asset_dirs().into_iter().find_map(|mut path| {
        path.push(name);
        std::fs::read(path).ok()
    })
}

fn safe_snippet_path(path: &str) -> Option<&FsPath> {
    let path = FsPath::new(path);
    (path.extension().and_then(|ext| ext.to_str()) == Some("js")
        && path
            .components()
            .all(|component| matches!(component, Component::Normal(_))))
    .then_some(path)
}

fn read_play_snippet(path: &str) -> Option<Vec<u8>> {
    let relative = safe_snippet_path(path)?;
    play_asset_dirs().into_iter().find_map(|mut root| {
        root.push("snippets");
        root.push(relative);
        std::fs::read(root).ok()
    })
}

/// **The play surface's own room.**
///
/// This is the only page on the product that is a GAME rather than a document, and it is dressed
/// as one. Three decisions carry it:
///
/// 1. **One palette, and it is the brand's night palette** (`dregg-posters/theme.typ`,
///    `dregg-site/static/css/site.css`): ground `#0b0a10`, panel `#131118`, ink `#dcd8e4`,
///    brass `#b08d57`/`#d8b47e`, violet `#a89fd8`/`#cfc8f0`. The page's cool site accent is
///    retuned to brass here (scoped to this stylesheet, which is served on this route only) so the
///    room reads as torchlight rather than as a dashboard. Colour MEANS something and there are
///    only three meanings: **brass is light** (the torch, relics, the floor you stand on, what
///    your torch reveals you may act on), **violet is proof** (banked custody, a verified replay,
///    a settled receipt), **rust-red is peril** (a shut way, a standing guardian, a guttering
///    clock). Nothing is coloured for decoration.
/// 2. **Two faces, deliberately.** A system SERIF carries the voice — headings, the standing line,
///    the pressure lines, the verbs — because a dungeon speaks in prose; the mono voice carries
///    every measured thing — glyphs, counters, seeds, roots. No third face, no webfont, no CDN:
///    every face here is resident on the reader's machine, so there is no silent fallback and no
///    off-origin request the strict CSP would have to admit.
/// 3. **The room is LIT, and the light is the game.** `--nd-dim` and `--nd-glow` are set on the
///    live shell from the run's remaining light; `--nd-depth` is the floor the player stands on.
///    So the shaft carries a real pool of torchlight that SLIDES DOWN with the player and CLOSES
///    IN as the clock burns down. That is not decoration either — it is the one resource the run
///    cannot refill, drawn as the thing it is. When the run settles, the lights come up: a closed
///    record is a receipt to read, not a dungeon to survive.
///
/// Motion is short, clarifies, and never gates input: a relic landing in the pack, a pip going
/// out, a bar growing. All of it is off under `prefers-reduced-motion`.
const PLAY_STYLE: &str = r##"<style>
/* ═══ TOKENS — the night palette, the two faces, the scale ════════════════ */
:root{
--nd-ground:#0b0a10;--nd-deep:#07060b;--nd-panel:#131118;--nd-stone:#191621;
--nd-line:#272233;--nd-line-soft:#1c1826;--nd-line-lit:#3a3247;
--nd-ink:#dcd8e4;--nd-soft:#a49fb4;--nd-faint:#6d6880;--nd-ghost:#463f57;
--nd-torch:#d8b47e;--nd-torch-deep:#b08d57;--nd-torch-hot:#f0c98d;--nd-ember:#c2703c;
--nd-proof:#a89fd8;--nd-proof-lit:#cfc8f0;
--nd-peril:#c96a5e;--nd-peril-lit:#e59289;
--nd-serif:ui-serif,"Iowan Old Style","Palatino Linotype",Palatino,"Book Antiqua",Georgia,"Times New Roman",serif;
--nd-mono:ui-monospace,SFMono-Regular,"SF Mono",Menlo,Consolas,"DejaVu Sans Mono","Liberation Mono",monospace;
--nd-ease:cubic-bezier(.2,.7,.3,1);
--nd-f1:.6875rem;--nd-f2:.8125rem;--nd-f3:.9375rem;--nd-f4:1.0625rem;--nd-f5:1.3125rem;
/* The shared chrome's cyan accent becomes torchlight for this route: links and the focus ring */
/* belong to the same room as the board. */
--accent:#d8b47e;--line-soft:#1c1826}
/* The ground the whole page stands on: a warm breath of light from the mouth of the shaft above, */
/* a cold violet from the proof layer below. */
body{background:
radial-gradient(122% 78% at 50% -12%,rgba(216,180,126,.062),transparent 62%),
radial-gradient(96% 56% at 50% 118%,rgba(168,159,216,.05),transparent 66%),
var(--nd-ground);background-attachment:fixed}
/* ═══ THE DOOR — a title, one rule of the game, then the board ════════════ */
.nd-page{max-width:62rem}
.nd-intro{max-width:46rem;margin:clamp(1.4rem,4.5vw,2.6rem) 0 clamp(1.1rem,3vw,1.8rem)}
.nd-kicker{display:flex;align-items:center;gap:.6rem;margin:0 0 .85rem;font-family:var(--nd-mono);font-size:var(--nd-f1);letter-spacing:.22em;text-transform:uppercase;color:var(--nd-torch-deep)}
.nd-kicker::before{content:"";flex:0 0 auto;width:1.5rem;height:1px;background:linear-gradient(90deg,transparent,var(--nd-torch-deep))}
.nd-intro h1{font-family:var(--nd-serif);font-weight:600;font-size:clamp(2.1rem,6.6vw,3.5rem);line-height:1.02;letter-spacing:-.022em;margin:0 0 .7rem;color:#f4efe3;text-shadow:0 0 44px rgba(216,180,126,.22)}
.nd-intro p{margin:0;max-width:52ch;font-family:var(--nd-serif);font-size:var(--nd-f4);line-height:1.62;color:var(--nd-soft)}
/* ═══ THE SHELL — cut stone, not a rounded card ═══════════════════════════ */
.nd-shell{position:relative;border:1px solid var(--nd-line);border-radius:3px;padding:clamp(.9rem,2.4vw,1.5rem);background:linear-gradient(180deg,var(--nd-panel),var(--nd-deep));box-shadow:0 44px 96px -60px #000,inset 0 1px 0 rgba(255,255,255,.028)}
/* The dark closing in. A whisper on the shell (the shaft below carries the real weight), driven */
/* from the run's own remaining light. */
/* Opacity, not a gradient colour stop, so the dark ARRIVES rather than steps: gradients do not
   interpolate, and a light clock that jumps between states would read as a rendering bug. */
.nd-shell::after{content:"";position:absolute;inset:0;pointer-events:none;border-radius:inherit;background:radial-gradient(120% 88% at 50% 34%,transparent 46%,#030206 100%);opacity:calc(var(--nd-dim,0) * .34);transition:opacity .55s var(--nd-ease)}
/* ═══ THE RUN HEADER — one word, one sentence, the provenance ═════════════ */
.nd-run{display:grid;grid-template-columns:minmax(0,1fr) auto;gap:.35rem 1.4rem;align-items:start;margin:0 0 1.05rem;padding:0 0 .9rem;border-bottom:1px solid var(--nd-line-soft)}
.nd-status{grid-column:1;display:flex;flex-wrap:wrap;gap:.4rem .55rem;align-items:center;margin:0 0 .5rem}
.nd-pill{display:inline-flex;align-items:center;gap:.42rem;padding:.24rem .62rem;border-radius:2px;border:1px solid currentColor;font-family:var(--nd-mono);font-size:var(--nd-f1);font-weight:700;letter-spacing:.17em;text-transform:uppercase;line-height:1.3}
.nd-pill::before{content:"";flex:0 0 auto;width:.36rem;height:.36rem;border-radius:50%;background:currentColor;box-shadow:0 0 8px currentColor}
.nd-pill.good{color:var(--nd-proof-lit);background:rgba(168,159,216,.1)}
.nd-pill.warn{color:var(--nd-torch);background:rgba(216,180,126,.09)}
.nd-pill.bad{color:var(--nd-peril-lit);background:rgba(201,106,94,.11)}
.nd-terminal{font-family:var(--nd-mono);font-size:var(--nd-f1);letter-spacing:.17em;text-transform:uppercase;color:var(--nd-torch-hot)}
.nd-standing{grid-column:1;margin:0;font-family:var(--nd-serif);font-size:var(--nd-f5);line-height:1.32;letter-spacing:-.01em;color:var(--nd-ink)}
.nd-meta{grid-column:2;grid-row:1/span 2;display:grid;gap:.22rem;justify-items:end;text-align:right;font-family:var(--nd-mono);font-size:var(--nd-f1);letter-spacing:.05em;color:var(--nd-faint);white-space:nowrap}
.nd-proof{color:var(--nd-proof-lit)}
.nd-proof.bad{color:var(--nd-peril-lit)}
/* ═══ THE TORCH — the clock, and the most alive thing on the page ═════════
   26 pips, one per breath, because a turn-based clock is COUNTED, not estimated: a player reads
   "four moves left" straight off the band instead of eyeballing a percentage. The lit run burns
   left to right like a fuse; the burning edge is `.tip` and it breathes. */
.nd-torch{position:relative;overflow:hidden;margin:0 0 1.1rem;padding:.85rem 1rem .9rem;border:1px solid var(--nd-line);border-radius:3px;background:linear-gradient(180deg,rgba(216,180,126,.05),rgba(11,10,16,.45));transition:border-color .4s var(--nd-ease),background .4s var(--nd-ease)}
.nd-torch::before{content:"";position:absolute;left:0;top:0;bottom:0;width:2px;background:linear-gradient(180deg,var(--nd-torch-hot),var(--nd-torch-deep));opacity:.85}
.nd-torch-head{display:flex;flex-wrap:wrap;align-items:baseline;gap:.25rem .85rem;margin:0 0 .6rem}
.nd-torch-label{font-family:var(--nd-mono);font-size:var(--nd-f1);letter-spacing:.24em;text-transform:uppercase;color:var(--nd-torch-deep)}
.nd-torch-say{margin:0;font-family:var(--nd-serif);font-size:var(--nd-f3);line-height:1.5;color:var(--nd-soft)}
.nd-torch .nd-meter{grid-template-columns:minmax(0,1fr) auto;gap:0 1rem;align-items:center}
.nd-torch .nd-meter-label{display:none}
.nd-torch .nd-meter-track{grid-column:1;grid-row:1;display:flex;align-items:stretch;gap:.2rem;height:auto;border:0;border-radius:0;background:none;overflow:visible;box-shadow:none}
.nd-torch .nd-meter-value{grid-column:2;grid-row:1;display:flex;align-items:baseline;gap:.06rem;line-height:1}
.nd-torch .nd-meter-value b{font-weight:600;font-size:clamp(1.75rem,6vw,2.4rem);letter-spacing:-.035em;color:var(--nd-torch-hot)}
.nd-torch .nd-meter-value i{font-style:normal;font-size:var(--nd-f2);color:var(--nd-faint)}
.nd-pip{position:relative;flex:1 1 0;min-width:0;height:1.45rem;border-radius:1px;background:var(--nd-stone);box-shadow:inset 0 0 0 1px rgba(255,255,255,.03)}
.nd-pip.lit{background:linear-gradient(180deg,var(--nd-torch-hot),var(--nd-torch-deep));box-shadow:0 0 10px -3px rgba(216,180,126,.7),inset 0 1px 0 rgba(255,255,255,.32)}
.nd-pip.spent{background:linear-gradient(180deg,#15121b,#0c0a11)}
.nd-pip.tip{background:linear-gradient(180deg,#fff2d8,var(--nd-torch));box-shadow:0 0 15px -1px rgba(240,201,141,.75);animation:nd-flicker 3.6s ease-in-out infinite}
/* The pip that went dark on THIS turn keeps an ember for a beat — the only feedback that says */
/* "you just spent one" without a number moving. */
.nd-pip.guttered::after{content:"";position:absolute;inset:0;border-radius:inherit;background:var(--nd-ember);animation:nd-gutter .75s var(--nd-ease) forwards}
@keyframes nd-gutter{from{opacity:.85}to{opacity:0}}
@keyframes nd-flicker{0%,100%{opacity:1}44%{opacity:.74}72%{opacity:.95}}
/* Burning low: the flame cools from gold to ember and the band's frame warns. */
.nd-torch[data-state=low]{border-color:rgba(194,112,60,.42)}
.nd-torch[data-state=low] .nd-meter-value b{color:#f0aa66}
.nd-torch[data-state=guttering]{border-color:rgba(201,106,94,.55);background:linear-gradient(180deg,rgba(201,106,94,.1),rgba(11,10,16,.5))}
.nd-torch[data-state=guttering] .nd-pip.lit{background:linear-gradient(180deg,#f0a15e,var(--nd-ember));box-shadow:0 0 12px -3px rgba(194,112,60,.8)}
.nd-torch[data-state=guttering] .nd-pip.tip{background:linear-gradient(180deg,#ffd7a8,#e08050);animation-duration:1.15s}
.nd-torch[data-state=guttering] .nd-meter-value b{color:var(--nd-peril-lit)}
.nd-torch[data-state=dead]{border-color:rgba(201,106,94,.4);background:#0a090e}
.nd-torch[data-state=dead] .nd-torch-say{color:var(--nd-peril-lit)}
.nd-torch[data-state=out]{opacity:.72}
/* ═══ THE ARENA — board left, vitals right; one column on a phone ═════════ */
.nd-arena{display:grid;grid-template-columns:minmax(0,1fr);gap:1.05rem;margin:0 0 1.1rem}
@media(min-width:56rem){.nd-arena{grid-template-columns:minmax(0,1fr) 16.5rem;align-items:start}}
/* ═══ THE SHAFT — a relic keeps its COLUMN, so you watch it travel ════════ */
.nd-shaft{min-width:0}
.nd-shaft-heading{display:flex;align-items:baseline;gap:.55rem;margin:0 0 .5rem;font-family:var(--nd-mono);font-size:var(--nd-f1);font-weight:700;letter-spacing:.22em;text-transform:uppercase;color:var(--nd-faint)}
.nd-mapwrap{overflow-x:auto;overscroll-behavior-x:contain;-webkit-overflow-scrolling:touch;padding-bottom:2px}
.nd-map{position:relative;isolation:isolate;min-width:15.5rem;display:grid;gap:.2rem;padding:.5rem;border:1px solid var(--nd-line);border-radius:3px;background:linear-gradient(180deg,#100e16,#07060b);box-shadow:inset 0 0 46px -12px #000,inset 0 1px 0 rgba(255,255,255,.028)}
/* THE DARK CLOSING IN. `--nd-dim` is the run's own spent light, so the shaft's corners go black as
   the clock burns down. */
.nd-map::after{content:"";position:absolute;inset:0;pointer-events:none;z-index:2;border-radius:inherit;background:radial-gradient(86% 68% at 50% 42%,transparent 30%,#030206 100%);opacity:var(--nd-dim,0);transition:opacity .55s var(--nd-ease)}
/* THE POOL OF TORCHLIGHT. It is centred on the floor you stand on — `--nd-depth` is a plain floor
   number, so the geometry is exact rather than a tuned percentage — and it SLIDES DOWN the shaft
   as you delve. `--nd-glow` is your remaining light, so the pool also weakens as you burn. Depth 0
   puts it above floor one, which is light coming down from the mouth of the shaft. */
.nd-floors{position:relative;display:grid;gap:.2rem}
.nd-floors::before{content:"";position:absolute;left:-14%;right:-14%;top:calc((var(--nd-depth,0) - .5) / 4 * 100%);height:150%;transform:translateY(-50%);pointer-events:none;z-index:0;background:radial-gradient(closest-side,rgba(240,201,141,.2),rgba(216,180,126,.06) 52%,transparent 76%);opacity:var(--nd-glow,1);transition:top .45s var(--nd-ease),opacity .45s var(--nd-ease)}
.nd-row{position:relative;z-index:1;display:grid;grid-template-columns:repeat(var(--nd-cols,11),minmax(0,1fr));gap:.2rem}
/* A row holding the keyboard's focus rises ABOVE the closing dark, so the focus ring stays a
   focus ring even when the torch is nearly out. */
.nd-row:focus-within{z-index:4}
/* The manifest: eight anonymous columns become eight named ones. */
.nd-row-head .nd-cell{aspect-ratio:auto;height:1.05rem;border:0;background:none;color:var(--nd-ghost);font-size:.58rem}
.nd-head-span{grid-column:span 3;display:grid;place-items:center;font-family:var(--nd-mono);font-size:.54rem;letter-spacing:.15em;text-transform:uppercase;color:var(--nd-ghost)}
/* The floor you stand on is the LIT one — the row itself, not a badge on it. */
.nd-row.here .nd-cell{background:rgba(216,180,126,.05);border-color:rgba(216,180,126,.1)}
.nd-row.here .nd-cell.tag-void{color:#4d4560}
/* The shaft is a PLACE; the pack and the vault are a LEDGER. They share the columns (that is the
   whole point) but they are not floors five and six, so they sit on their own ground — and above
   the closing dark (z-index over `.nd-map::after`), because custody is not lit by your torch. As
   the run burns out the shaft goes black around you and your ledger keeps reading. */
.nd-rule{position:relative;z-index:3;height:1px;margin:.42rem .15rem;background:linear-gradient(90deg,transparent,var(--nd-line-lit),transparent)}
.nd-band{position:relative;z-index:3;display:grid;gap:.2rem;padding:.32rem .28rem .28rem;border-radius:2px;background:rgba(168,159,216,.035);box-shadow:inset 0 0 0 1px rgba(168,159,216,.07)}
.nd-cell{position:relative;display:grid;place-items:center;aspect-ratio:1/1;min-width:0;margin:0;padding:0;border:1px solid transparent;border-radius:2px;background:rgba(255,255,255,.014);color:var(--nd-ghost);font-family:var(--nd-mono);font-size:clamp(.68rem,2.05vw,.95rem);font-weight:600;line-height:1;-webkit-appearance:none;appearance:none;transition:color .16s,border-color .16s,background .16s,box-shadow .18s,transform .1s var(--nd-ease)}
.nd-cell.tag-void{color:#2f2a3b;font-size:.56rem}
.nd-cell.tag-mark{color:var(--nd-faint);font-size:.62rem}
.nd-cell.tag-you{color:#100c07;background:linear-gradient(180deg,var(--nd-torch-hot),var(--nd-torch-deep));border-color:var(--nd-torch-hot);box-shadow:0 0 16px -4px rgba(240,201,141,.85);font-weight:700}
.nd-cell.tag-crown{color:#fff4dd;background:rgba(240,201,141,.16);border-color:rgba(240,201,141,.42);text-shadow:0 0 14px rgba(240,201,141,.7)}
.nd-cell.tag-relic{color:var(--nd-torch);text-shadow:0 0 10px rgba(216,180,126,.45)}
.nd-cell.tag-vault{color:var(--nd-proof-lit);text-shadow:0 0 12px rgba(168,159,216,.55)}
.nd-cell.tag-open{color:#5d7566}
.nd-cell.tag-shut{color:var(--nd-peril);background:rgba(201,106,94,.08);border-color:rgba(201,106,94,.22)}
.nd-cell.tag-guard{color:var(--nd-peril-lit);background:rgba(201,106,94,.1);border-color:rgba(201,106,94,.3)}
.nd-cell.tag-fallen{color:#4b4457}
/* A guardian on a floor you are not standing on: present, but out of your torch's reach. */
.nd-cell.tag-dim{color:#413b4f}
/* WHAT YOUR TORCH SHOWS YOU MAY DO. Brass ring plus a corner tick, so the affordance is a SHAPE */
/* and not only a hue. Eligibility is the offering's own verdict — see `buildMap`. */
button.nd-cell{cursor:pointer;font:inherit;font-family:var(--nd-mono);font-size:clamp(.68rem,2.05vw,.95rem);font-weight:600}
.nd-cell.actionable{color:#fff6e6;border-color:rgba(240,201,141,.62);background:rgba(240,201,141,.1);box-shadow:0 0 0 1px rgba(240,201,141,.14),0 0 18px -7px rgba(240,201,141,.9)}
.nd-cell.actionable::after{content:"";position:absolute;right:2px;bottom:2px;width:.26rem;height:.26rem;border-radius:50%;background:var(--nd-torch-hot);box-shadow:0 0 6px var(--nd-torch-hot)}
button.nd-cell.actionable:hover{background:rgba(240,201,141,.19);border-color:var(--nd-torch-hot);transform:translateY(-1px)}
button.nd-cell.actionable:active{transform:translateY(0) scale(.95)}
button.nd-cell:focus-visible{outline:2px solid var(--nd-proof-lit);outline-offset:2px;z-index:4}
/* A relic that moved on THIS turn lands with weight — the one animation that says a move HAPPENED. */
.nd-cell.moved{animation:nd-land .4s var(--nd-ease) both}
@keyframes nd-land{0%{transform:scale(1.5);filter:brightness(2.1)}62%{transform:scale(.96)}100%{transform:none;filter:none}}
.nd-legend{display:flex;flex-wrap:wrap;gap:.28rem .8rem;margin:.6rem 0 0;padding:0;list-style:none;font-family:var(--nd-serif);font-size:var(--nd-f2);line-height:1.5;color:var(--nd-faint)}
.nd-legend li{display:inline-flex;align-items:center;gap:.36rem;white-space:nowrap}
.nd-legend b{display:grid;place-items:center;flex:0 0 auto;width:1.1rem;height:1.1rem;border-radius:2px;border:1px solid var(--nd-line);background:rgba(255,255,255,.03);font-family:var(--nd-mono);font-size:.64rem;font-weight:600;color:var(--nd-soft)}
.nd-legend-note{margin:.5rem 0 0;font-family:var(--nd-serif);font-size:var(--nd-f2);line-height:1.55;color:var(--nd-ghost);max-width:60ch}
/* ═══ THE RAIL — the three secondary meters and the pressure lines ════════ */
.nd-rail{display:grid;gap:.85rem;align-content:start;min-width:0}
.nd-panel{border:1px solid var(--nd-line-soft);border-radius:3px;background:rgba(255,255,255,.016);padding:.8rem .85rem .85rem}
.nd-panel-head{margin:0 0 .65rem;font-family:var(--nd-mono);font-size:var(--nd-f1);font-weight:700;letter-spacing:.2em;text-transform:uppercase;color:var(--nd-faint)}
.nd-meters{display:grid;gap:.7rem}
.nd-meter{display:grid;grid-template-columns:minmax(0,1fr) auto;gap:.3rem .6rem;align-items:baseline}
.nd-meter-label{grid-column:1;grid-row:1;font-family:var(--nd-mono);font-size:var(--nd-f1);letter-spacing:.15em;text-transform:uppercase;color:var(--nd-faint)}
.nd-meter-value{grid-column:2;grid-row:1;font-family:var(--nd-mono);font-size:var(--nd-f2);color:var(--nd-ink);font-variant-numeric:tabular-nums}
.nd-meter-value i{font-style:normal;color:var(--nd-faint)}
.nd-meter-track{grid-column:1/-1;grid-row:2;position:relative;height:.34rem;border-radius:2px;background:rgba(255,255,255,.05);box-shadow:inset 0 0 0 1px rgba(255,255,255,.03);overflow:hidden}
.nd-meter-fill{display:block;height:100%;border-radius:inherit;background:linear-gradient(90deg,var(--nd-torch-deep),var(--nd-torch));transition:width .34s var(--nd-ease)}
.nd-meter.low .nd-meter-fill{background:linear-gradient(90deg,#8a3f38,var(--nd-peril-lit))}
.nd-meter.done .nd-meter-fill{background:linear-gradient(90deg,var(--nd-proof),var(--nd-proof-lit))}
/* The things you are about to lose to. A coloured rule, not a warning emoji — the register is a */
/* quiet dungeon, not a browser alert. */
.nd-pressure{display:flex;gap:.55rem;margin:.6rem 0 0;font-family:var(--nd-serif);font-size:var(--nd-f2);line-height:1.5;color:var(--nd-soft)}
.nd-panel .nd-pressure:first-of-type{margin-top:0}
.nd-pressure::before{content:"";flex:0 0 auto;width:2px;border-radius:1px;background:var(--nd-line-lit);align-self:stretch}
.nd-pressure.warn::before{background:var(--nd-torch-deep)}
.nd-pressure.peril{color:var(--nd-peril-lit)}
.nd-pressure.peril::before{background:var(--nd-peril)}
.nd-pressure.proof::before{background:var(--nd-proof)}
/* ═══ THE VERBS — every one names its price, so colour names its family ═══ */
.nd-action-menu{min-width:0;margin:0 0 1rem}
.nd-action-header{display:flex;flex-wrap:wrap;align-items:baseline;justify-content:space-between;gap:.3rem 1rem;margin:0 0 .5rem}
.nd-action-heading{margin:0;font-family:var(--nd-mono);font-size:var(--nd-f1);font-weight:700;letter-spacing:.2em;text-transform:uppercase;color:var(--nd-faint)}
.nd-action-summary{margin:0;font-family:var(--nd-serif);font-size:var(--nd-f2);color:var(--nd-soft)}
.nd-action-assurance{margin:0 0 .7rem;max-width:62ch;font-size:var(--nd-f1);line-height:1.5;color:var(--nd-ghost)}
.nd-actions{display:grid;grid-template-columns:repeat(auto-fit,minmax(13.5rem,1fr));gap:.5rem}
.nd-actions button{position:relative;min-height:3rem;padding:.6rem .85rem .6rem 1rem;border:1px solid var(--nd-line-lit);border-left-width:2px;border-left-color:var(--nd-line-lit);border-radius:3px;background:linear-gradient(180deg,rgba(255,255,255,.028),rgba(255,255,255,.008));color:var(--nd-ink);font-family:var(--nd-serif);font-size:var(--nd-f3);font-weight:500;line-height:1.35;text-align:left;cursor:pointer;overflow-wrap:anywhere;touch-action:manipulation;transition:border-color .15s,background .15s,color .15s,transform .1s var(--nd-ease),box-shadow .2s}
/* The verb families, by the one colour system: descending and taking are TORCH work, striking and
   gambling are PERIL, and the climb out is the PROOF that makes a run yours. The offering already
   names each verb's price in its own label, so the rule is the only decoration a button needs.
   A verb this sheet has never heard of keeps the neutral rule rather than going unstyled — the
   action list is the offering's, and it is allowed to grow. */
.nd-actions button[data-turn=delve]{border-left-color:var(--nd-torch-deep)}
.nd-actions button[data-turn=unlock]{border-left-color:var(--nd-torch)}
.nd-actions button[data-turn=loot]{border-left-color:var(--nd-torch-hot)}
.nd-actions button[data-turn=smite]{border-left-color:var(--nd-peril)}
.nd-actions button[data-turn=lunge]{border-left-color:var(--nd-ember)}
.nd-actions button[data-turn=flee]{border-left-color:var(--nd-proof);background:linear-gradient(180deg,rgba(168,159,216,.1),rgba(255,255,255,.01))}
.nd-actions button:hover{border-color:rgba(240,201,141,.55);color:#fff6e6;background:linear-gradient(180deg,rgba(240,201,141,.13),rgba(255,255,255,.02));transform:translateY(-1px);box-shadow:0 10px 24px -18px rgba(240,201,141,.95)}
.nd-actions button[data-turn=flee]:hover{border-color:rgba(207,200,240,.6);color:#f3f0ff;background:linear-gradient(180deg,rgba(168,159,216,.18),rgba(255,255,255,.02))}
.nd-actions button:active{transform:translateY(0) scale(.995)}
.nd-actions button:focus-visible,.nd-tools button:focus-visible,.nd-unavailable summary:focus-visible{outline:2px solid var(--nd-proof-lit);outline-offset:2px}
.nd-unavailable{margin:.8rem 0 0;padding:.65rem 0 0;border-top:1px solid var(--nd-line-soft);color:var(--nd-faint)}
.nd-unavailable summary{display:flex;align-items:center;min-height:2.6rem;font-family:var(--nd-mono);font-size:var(--nd-f2);letter-spacing:.05em;cursor:pointer;touch-action:manipulation}
.nd-unavailable summary:hover{color:var(--nd-soft)}
.nd-unavailable ul{list-style:none;margin:.5rem 0 0;padding:0;display:grid;gap:.28rem}
.nd-unavailable li{display:flex;justify-content:space-between;gap:1rem;padding:.22rem 0;border-bottom:1px solid rgba(255,255,255,.022);font-size:var(--nd-f2)}
.nd-unavailable-label{color:var(--nd-soft);font-family:var(--nd-serif);overflow-wrap:anywhere}
.nd-unavailable-reason{flex:0 0 auto;max-width:16rem;text-align:right;color:var(--nd-ghost);font-family:var(--nd-mono);font-size:var(--nd-f1);overflow-wrap:anywhere}
/* ═══ THE LOG — what just happened, in the dungeon's voice ════════════════ */
.nd-message{margin:0 0 1rem;padding:.7rem .9rem .7rem 1rem;min-height:3.1rem;border:1px solid var(--nd-line-soft);border-left:2px solid var(--nd-line-lit);border-radius:0 3px 3px 0;background:rgba(255,255,255,.016);font-family:var(--nd-serif);font-size:var(--nd-f3);line-height:1.55;color:var(--nd-soft)}
.nd-message.good{border-left-color:var(--nd-proof);color:var(--nd-ink)}
.nd-message.bad{border-left-color:var(--nd-peril);background:rgba(201,106,94,.055);color:var(--nd-peril-lit)}
.nd-message.fresh{animation:nd-log-in .3s var(--nd-ease) both}
@keyframes nd-log-in{from{opacity:0;transform:translateX(-4px)}to{opacity:1;transform:none}}
/* ═══ THE SETTLEMENT — when the run ends, the receipt IS the surface ══════ */
.nd-settled{margin:0 0 1.05rem;padding:.95rem 1.05rem 1rem;border:1px solid rgba(168,159,216,.34);border-radius:3px;background:linear-gradient(180deg,rgba(168,159,216,.1),rgba(11,10,16,.35))}
.nd-settled h2{margin:0 0 .3rem;font-family:var(--nd-serif);font-weight:600;font-size:var(--nd-f5);color:var(--nd-proof-lit)}
.nd-settled p{margin:0;max-width:56ch;font-family:var(--nd-serif);font-size:var(--nd-f3);line-height:1.55;color:var(--nd-soft)}
.nd-share{display:inline-flex;align-items:center;gap:.4rem;margin:.75rem 0 0;padding:.5rem .8rem;border:1px solid rgba(168,159,216,.45);border-radius:3px;background:rgba(168,159,216,.08);color:var(--nd-proof-lit);font-family:var(--nd-mono);font-size:var(--nd-f2);text-decoration:none}
.nd-share:hover{border-color:var(--nd-proof-lit);background:rgba(168,159,216,.16);color:#fff}
/* ═══ THE RECORD — provenance tools, deliberately quiet ═══════════════════ */
.nd-record{margin:1.05rem 0 0;padding:.9rem 0 0;border-top:1px solid var(--nd-line-soft)}
.nd-tools{display:flex;flex-wrap:wrap;gap:.45rem}
.nd-tools button{appearance:none;-webkit-appearance:none;display:inline-flex;align-items:center;justify-content:center;min-height:2.6rem;padding:.5rem .8rem;border:1px solid var(--nd-line);border-radius:3px;background:rgba(255,255,255,.02);color:var(--nd-soft);font-family:var(--nd-mono);font-size:var(--nd-f2);cursor:pointer;transition:border-color .15s,color .15s,background .15s}
.nd-tools button:hover:not(:disabled){border-color:var(--nd-line-lit);color:var(--nd-ink);background:rgba(255,255,255,.045)}
.nd-tools button:disabled{opacity:.38;cursor:not-allowed}
.nd-tools button.primary{border-color:rgba(168,159,216,.5);background:rgba(168,159,216,.1);color:var(--nd-proof-lit)}
.nd-tools button.primary:hover:not(:disabled){border-color:var(--nd-proof-lit);background:rgba(168,159,216,.18);color:#fff}
.nd-tools button.danger:hover:not(:disabled){border-color:rgba(201,106,94,.5);color:var(--nd-peril-lit);background:rgba(201,106,94,.08)}
.nd-root{margin:.8rem 0 0;font-family:var(--nd-mono);font-size:var(--nd-f1);line-height:1.65;color:var(--nd-ghost);overflow-wrap:anywhere}
/* ═══ BOOT + REFUSAL — the two states before there is a game ══════════════ */
.nd-boot{display:flex;align-items:center;gap:.65rem;margin:1.4rem 0;padding:.95rem 1.05rem;border:1px solid var(--nd-line);border-left:2px solid var(--nd-torch-deep);border-radius:0 3px 3px 0;background:rgba(255,255,255,.015);color:var(--nd-soft);font-family:var(--nd-serif);font-size:var(--nd-f3)}
.nd-boot::before{content:"";flex:0 0 auto;width:.5rem;height:.5rem;border-radius:50%;background:var(--nd-torch);box-shadow:0 0 12px var(--nd-torch);animation:nd-breathe 2.1s ease-in-out infinite}
@keyframes nd-breathe{0%,100%{opacity:1;transform:scale(1)}50%{opacity:.45;transform:scale(.82)}}
.nd-fatal{margin:1.4rem 0;padding:.95rem 1.05rem;border:1px solid rgba(201,106,94,.45);border-left:2px solid var(--nd-peril);border-radius:0 3px 3px 0;background:rgba(201,106,94,.06);color:var(--nd-peril-lit);font-family:var(--nd-serif);font-size:var(--nd-f3);line-height:1.55;overflow-wrap:anywhere}
.nd-offline{margin:1.4rem 0;padding:.95rem 1.05rem;border:1px solid var(--nd-line);border-left:2px solid var(--nd-proof);border-radius:0 3px 3px 0;background:rgba(255,255,255,.015);color:var(--nd-soft);font-family:var(--nd-serif);font-size:var(--nd-f3);line-height:1.6}
.nd-offline a{color:var(--nd-proof-lit)}
/* ═══ THE ENGINE DOOR — where the game runs, chosen rather than assumed ═══════════
   Two cards, side by side, both real. The LIVE one wears the torch (this is the engine you are on);
   the other is stated at full contrast rather than dimmed into an afterthought, because the whole
   point is that both are the same game and neither is a downgrade. The unavailable browser card is
   the one thing that greys out — an option this deployment genuinely does not have. */
.nd-doors{margin:clamp(1.1rem,3vw,1.7rem) 0 0}
.nd-doors h2{margin:0 0 .7rem;font-family:var(--nd-mono);font-size:var(--nd-f1);letter-spacing:.2em;text-transform:uppercase;color:var(--nd-torch-deep);font-weight:700}
.nd-door-grid{display:grid;grid-template-columns:repeat(auto-fit,minmax(min(100%,17rem),1fr));gap:.75rem}
.nd-door{padding:.95rem 1.05rem 1.05rem;border:1px solid var(--nd-line);border-left:2px solid var(--nd-line-lit);border-radius:0 3px 3px 0;background:linear-gradient(180deg,rgba(19,17,24,.9),rgba(11,10,16,.92))}
.nd-door.nd-door-live{border-left-color:var(--nd-torch-deep);background:linear-gradient(180deg,rgba(216,180,126,.05),rgba(11,10,16,.92))}
.nd-door h3{margin:0 0 .45rem;display:flex;flex-wrap:wrap;align-items:baseline;gap:.5rem;font-family:var(--nd-serif);font-weight:600;font-size:var(--nd-f4);letter-spacing:-.01em;color:var(--nd-ink)}
.nd-door-tag{font-family:var(--nd-mono);font-size:var(--nd-f1);letter-spacing:.17em;text-transform:uppercase;color:var(--nd-torch);font-weight:700}
.nd-door p{margin:0 0 .6rem;font-family:var(--nd-serif);font-size:var(--nd-f2);line-height:1.6;color:var(--nd-soft);max-width:46ch}
.nd-door p:last-child{margin-bottom:0}
.nd-door-go{display:inline-block;padding:.5rem .95rem;border:1px solid var(--nd-torch-deep);border-radius:2px;background:rgba(216,180,126,.1);color:var(--nd-torch-hot);font-family:var(--nd-mono);font-size:var(--nd-f2);font-weight:700;letter-spacing:.04em;text-decoration:none}
.nd-door-go:hover{background:rgba(216,180,126,.18);border-color:var(--nd-torch);color:#f7e6c8}
.nd-door-state{font-family:var(--nd-mono);font-size:var(--nd-f1);letter-spacing:.05em;color:var(--nd-faint)}
.nd-door-state a{color:var(--nd-torch)}
.nd-door-off{color:var(--nd-peril-lit)}
/* ⚑ THE START BUTTON — one press, at the top, into the hosted game. It is bigger and warmer than
   `.nd-door-go` because it is not one option among two any more: on the default engine it is the
   page's ONE action, and the in-tab alternative below it is a sentence. */
.nd-start{display:flex;flex-wrap:wrap;align-items:center;gap:.8rem;margin:clamp(1rem,2.6vw,1.5rem) 0 0}
.nd-start-go{padding:.68rem 1.35rem;font-size:var(--nd-f3);box-shadow:0 0 34px -14px rgba(216,180,126,.5)}
.nd-alt{font-family:var(--nd-mono);font-size:var(--nd-f1);letter-spacing:.08em;text-transform:uppercase;color:var(--nd-faint)}
.nd-alt a{color:var(--nd-torch)}
/* The demoted engine offer: a full sentence in the page's serif voice, not a card and not a chooser. */
.nd-alt-block{display:block;margin:.9rem 0 0;max-width:58ch;font-family:var(--nd-serif);font-size:var(--nd-f2);letter-spacing:0;text-transform:none;line-height:1.62;color:var(--nd-soft)}
/* ═══ THE RULES, IN ONE SCREEN — what a stranger needs before their first press ═══
   Automatafl and the tug each carry this block on their own landing; the Descent had none, so a
   first-time player met a shaft, a torch band and seven verbs with no statement of the objective.
   Torch-lit rather than violet: these are the rules of the room, not a claim about proof. */
.nd-rules{margin:clamp(1.4rem,4vw,2.2rem) 0 0;padding:1.05rem 1.15rem 1.15rem;border:1px solid var(--nd-line);border-left:3px solid var(--nd-torch-deep);border-radius:0 3px 3px 0;background:linear-gradient(180deg,rgba(19,17,24,.9),rgba(11,10,16,.92))}
.nd-rules h2{margin:0 0 .75rem;font-family:var(--nd-serif);font-weight:600;font-size:var(--nd-f5);letter-spacing:-.01em;color:var(--nd-torch-hot)}
.nd-rules ul{list-style:none;margin:0;padding:0;display:grid;gap:.55rem}
.nd-rules li{position:relative;padding-left:1.05rem;font-family:var(--nd-serif);font-size:var(--nd-f3);line-height:1.6;color:var(--nd-soft);max-width:64ch}
.nd-rules li::before{content:"";position:absolute;left:0;top:.66em;width:.32rem;height:.32rem;background:var(--nd-torch-deep);transform:rotate(45deg)}
.nd-rules strong{color:var(--nd-ink);font-weight:650}
.nd-rules p{margin:.9rem 0 0;font-family:var(--nd-serif);font-size:var(--nd-f2);line-height:1.62;color:var(--nd-faint);max-width:68ch}
.nd-rules a{color:var(--nd-proof-lit)}
.nd-rules code{font-family:var(--nd-mono);font-size:.9em;color:var(--nd-torch)}
/* ═══ THE PHONE — one column, and the shaft still fits without a swipe ════ */
@media(max-width:44rem){
.nd-page{padding-left:.9rem!important;padding-right:.9rem!important}
.nd-shell{padding:.85rem .8rem 1rem}
.nd-run{grid-template-columns:minmax(0,1fr);gap:.45rem}
.nd-meta{grid-column:1;grid-row:auto;display:flex;flex-wrap:wrap;gap:.2rem .9rem;justify-items:start;text-align:left}
.nd-torch{padding:.75rem .8rem .8rem}
.nd-pip{height:1.15rem}
.nd-actions{grid-template-columns:1fr}
.nd-unavailable li{flex-direction:column;gap:.1rem}
.nd-unavailable-reason{max-width:none;text-align:left}
.nd-tools button{flex:1 1 9rem}
}
/* Below ~26rem the 26-pip band and a big numeral cannot share a line honestly, so the count goes */
/* above the fuse rather than squeezing it into a comb nobody can count. */
@media(max-width:26rem){
.nd-torch .nd-meter{grid-template-columns:minmax(0,1fr)}
.nd-torch .nd-meter-value{grid-column:1;grid-row:1;margin:0 0 .4rem}
.nd-torch .nd-meter-track{grid-row:2;gap:.09rem}
.nd-torch .nd-meter-value b{font-size:1.7rem}
.nd-pip{height:1rem}
.nd-map{gap:.15rem;padding:.35rem}
.nd-row{gap:.15rem}
}
/* ═══ REDUCED MOTION — every one of the above is a nicety, and none is the ═
   information. Under `prefers-reduced-motion` the surface still says everything it says. */
@media(prefers-reduced-motion:reduce){
.nd-page *,.nd-page *::before,.nd-page *::after{animation-duration:.001ms!important;animation-iteration-count:1!important;transition-duration:.001ms!important}
}
</style>"##;

/// **The rules, in one screen** — the block automatafl (`automatafl_web::rules_html`) and the tug
/// (`tug_web::rules_html`) each carry on their own landing, and which the Descent did not have at
/// all. A first-time player arrived at a shaft, a torch band and seven verbs with no statement of
/// the objective, no price list and no word on the one-life stake; the pattern already existed on
/// two of the three shipped games, so this is the third rather than an invention.
///
/// Every number is read from the game's own constants (`dungeon_on_dregg::descent`, re-exported by
/// `dreggnet_offerings::native_descent`), so a rules change that moves the light budget or the carry
/// cap cannot leave this panel quietly wrong.
///
/// `live_beacon` decides the provenance paragraph rather than the copy hedging over both cases:
/// **never let an absence speak for itself** (`docs/reference/UX-QA-SWEEP-2026-07-26.md`). A day
/// that fell back to the date is *predictable*, and a page claiming "nobody could pick it in
/// advance" on such a day would be lying — so the offline branch says the date derived it.
fn rules_html(live_beacon: bool) -> String {
    use dreggnet_offerings::native_descent::{
        CARRY_CAP, DUNGEON_DAYS, DUNGEON_FLOORS, DUNGEON_RELICS, LIGHT_BREATH,
    };
    let provenance = if live_beacon {
        format!(
            "<p><strong>Everyone gets the same dungeon today.</strong> It was drawn from a public \
             random number published today by a public randomness service, so nobody, us included, \
             could pick it in advance. There are {DUNGEON_DAYS} possible dungeons, every one of them \
             checked beforehand to be beatable, and on any given day the best possible line spends \
             between 24 and {LIGHT_BREATH} of your {LIGHT_BREATH} breaths. There is almost no \
             slack.</p>"
        )
    } else {
        format!(
            "<p><strong>Everyone gets the same dungeon today</strong>, but today's was derived \
             from the date, because the public randomness service could not be reached. It is the \
             same dungeon for everybody and it is beatable, and it was also predictable in advance; \
             the label at the top of the run says which kind of day you are on. There are \
             {DUNGEON_DAYS} possible dungeons and on any given day the best possible line spends \
             between 24 and {LIGHT_BREATH} of your {LIGHT_BREATH} breaths.</p>"
        )
    };
    format!(
        "<section class=\"nd-rules\" aria-labelledby=\"nd-rules-h\">\
         <h2 id=\"nd-rules-h\">The rules, in one screen</h2>\
         <ul>\
         <li><strong>Get to the bottom, take the prize, climb back out.</strong> The dungeon is \
         {DUNGEON_FLOORS} floors deep and the prize lies on the lowest one. Nothing counts until you \
         are standing on the surface again.</li>\
         <li><strong>The torch is the clock and it never refills.</strong> You have {LIGHT_BREATH} \
         breaths of light for the whole run, every button spends at least one, and there is no way \
         to get more.</li>\
         <li><strong>The climb costs a breath a floor, and it is the only way out.</strong> So the \
         light you have left is never the real number: subtract how deep you are. Standing on the \
         bottom floor, {DUNGEON_FLOORS} of your remaining breaths are already spoken for.</li>\
         <li><strong>Three of the {DUNGEON_RELICS} relics are keys.</strong> A locked way opens only \
         if you are carrying its key, and a key is never hidden behind the door it opens, so every \
         way down is openable if you go and fetch the key first.</li>\
         <li><strong>A guardian can be pressed or lunged at.</strong> Pressing costs two breaths and \
         nothing else. Lunging does the same for one breath and permanently costs you one carrying \
         slot for the rest of the run: cheap now, expensive at the bottom.</li>\
         <li><strong>You can carry {CARRY_CAP}, minus how deep you are, minus any lunge damage.</strong> \
         That is {shallow} slots on floor 1 and {deep} at the bottom, and the bottom needs three \
         keys plus the prize, which is exactly {deep}. The dungeon gets stingier the further in you \
         go, on purpose.</li>\
         <li><strong>Banking ends the run, and you only get one.</strong> You can bank only on the \
         surface. Everything you carried out is yours; everything still down there is gone. There is \
         no second attempt today.</li>\
         </ul>\
         {provenance}\
         <p><strong>Where your run lives.</strong> A run in progress is stored in this browser. By \
         default you are identified by a browser cookie with no password and <strong>no \
         recovery</strong>, so clearing your browser data loses it with no way back. If a recovery \
         phrase is offered in the navigation, claiming one is what makes an identity survive that, \
         and until you claim one it does not. A run you play to its end is submitted once to \
         <a href=\"/descent\">the day's board</a>, which re-plays every move before it will rank \
         it: a run that does not replay is shown as FAIL and never ranks.</p>\
         </section>",
        provenance = provenance,
        shallow = CARRY_CAP - 1,
        deep = CARRY_CAP - DUNGEON_FLOORS,
    )
}

/// **WHICH ENGINE RUNS THE GAME** — the choice the page is now explicit about.
///
/// Both engines execute the SAME `NativeDescentOffering` over the same Lean-authored ruleset and
/// the same committed day, so neither is a lesser game. What differs is WHERE the executor runs and
/// therefore what you have to trust and what you have to download.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Engine {
    /// **The default.** The offering runs on this server; the page is plain HTML and one form POST
    /// per verb. No WebAssembly, no download, works with JavaScript off, starts instantly.
    Server,
    /// **Opt-in.** The whole ruleset is compiled to WebAssembly and executed in the reader's own
    /// tab. It costs a tens-of-megabytes one-time download and a slower first paint, and it is not
    /// available at all on a deployment whose bundle was never built.
    Browser,
}

impl Engine {
    /// The engine a `?engine=` value names. Anything else — absent, empty, misspelt — is
    /// [`Engine::Server`]: the browser engine is opt-IN, so it is never reached by accident, by a
    /// stale link, or by a typo.
    fn from_query(value: Option<&str>) -> Engine {
        match value.map(str::trim) {
            Some("browser") | Some("wasm") => Engine::Browser,
            _ => Engine::Server,
        }
    }

    /// The `data-engine` attribute value the bootstrap reads. `app.js` boots the wasm module ONLY
    /// for `browser`, so the default page issues no `import()`, no `.wasm` fetch and no BLS work.
    fn attr(self) -> &'static str {
        match self {
            Engine::Server => "server",
            Engine::Browser => "browser",
        }
    }
}

/// The server-side entry — the SAME `NativeDescentOffering`, hosted, rendered as forms. This is the
/// route the catalog already advertises for every non-table offering, named once so the play page
/// and the catalog cannot point at two different front doors.
const SERVER_ENGINE_HREF: &str = "/offerings/descent/session/descent-web";

/// **Is the browser bundle actually on this deployment?**
///
/// A `metadata()` probe, NOT [`read_play_asset`] — the blob is tens of megabytes and the question is
/// "does it exist", asked on every page render. Mirrors [`play_asset_dirs`] exactly, so a deployment
/// pointing `DESCENT_PLAY_ASSET_DIR` somewhere empty answers `false` here and gets a door that says
/// so, instead of a button that boots into a `TypeError`.
fn browser_bundle_present() -> bool {
    play_asset_dirs().into_iter().any(|mut path| {
        path.push("dregg_wasm_bg.wasm");
        std::fs::metadata(&path).is_ok_and(|meta| meta.is_file() && meta.len() > 0)
    })
}

/// ⚑ **THE ENGINE DOOR** — the block that makes in-browser execution a CHOICE.
///
/// The page used to boot WebAssembly unconditionally, which meant the flagship "Play" CTA was, for
/// every visitor, a tens-of-megabytes download before the first frame — and on a deployment with no
/// bundle it was a dead end reading *"The native WebAssembly artifact is unavailable; no substitute
/// game was opened"* beside a stack trace, with a fully working server-side copy of the same game
/// one URL away and never mentioned.
///
/// So the default is the server, the browser engine is opted into by name, and the trade is stated
/// rather than implied: **what the browser engine buys is not needing to trust this server about
/// your run.** It verifies the day's drand beacon by BLS pairing in your own tab (`fromBeacon`), it
/// replays its own receipts locally (`Verify full record`), and the run lives in your browser rather
/// than in this server's session store — the hosted page says plainly that your moves, the dungeon
/// and the result all live here. That is a real difference and it is the only one worth a download.
///
/// ⚑ **BUT ON THE DEFAULT ENGINE IT IS DEMOTED TO A LINE, because it was standing between a player
/// and the game.** On `Engine::Server` this page renders an EMPTY mount div (that is correct — see
/// [`shell_page`]'s `root_body`: a spinner for a load that never starts is worse), so what a visitor
/// who pressed the product's flagship "Play" CTA actually got was an intro, a *"Where do you want it
/// to run?"* chooser, and a rules block — a page ABOUT the game, with the game one more click away
/// inside a card. The two-card grid now renders only for a player who has already CHOSEN the browser
/// engine, where it is the switch-back control they need; the default gets [`start_here`]'s primary
/// CTA at the top of the page and this offer as one quiet sentence.
fn engine_door(engine: Engine, bundle: bool) -> String {
    // THE DEFAULT PATH: one line, below the CTA that already starts the game. Same URL, same
    // opt-in-by-name, same honest cost — just no longer shaped like a decision the player must make
    // before they may play.
    if engine == Engine::Server {
        return if bundle {
            "<p class=\"nd-alt nd-alt-block\">Or <a href=\"/descent/play?engine=browser\">run the \
             whole game inside this tab instead</a>: nothing about the run leaves your browser, and \
             the tab checks today's public random number itself rather than taking this server's word \
             for it. It costs a large one-time download and is slower to start.</p>"
                .to_string()
        } else {
            // Absent bundle, said BEFORE the click. `wasm/pkg` is gitignored, so this is the honest
            // state of any deployment that did not run `scripts/build-descent-wasm.sh`.
            "<p class=\"nd-alt nd-alt-block nd-door-off\">Running the game inside your own tab is \
             not available on this deployment: the WebAssembly bundle was not built here. The \
             hosted game above is the whole game.</p>"
                .to_string()
        };
    }
    let browser_card = if bundle {
        "<p class=\"nd-door-state\">Running in your browser now. \
         <a href=\"/descent/play\">Switch back to the server</a> if it is slow.</p>"
            .to_string()
    } else {
        "<p class=\"nd-door-state nd-door-off\">Not available on this deployment: the \
         WebAssembly bundle was not built here. The server engine above is the whole game.</p>"
            .to_string()
    };
    format!(
        "<section class=\"nd-doors\" aria-labelledby=\"nd-doors-h\">\
         <h2 id=\"nd-doors-h\">Where do you want it to run?</h2>\
         <div class=\"nd-door-grid\">\
         <div class=\"nd-door{server_live}\">\
         <h3>On the server <span class=\"nd-door-tag\">default</span></h3>\
         <p>Starts immediately, downloads nothing, and works with JavaScript turned off. Your \
         moves, the dungeon and the result live on this server, and anyone with your session link \
         can read them.</p>\
         <p><a class=\"nd-door-go\" href=\"{server}\">Play now</a></p>\
         </div>\
         <div class=\"nd-door{browser_live}\">\
         <h3>In your browser</h3>\
         <p>The whole ruleset is compiled to WebAssembly and runs in this tab. Nothing about the \
         run leaves your browser, and the tab checks today's public random beacon itself rather \
         than taking this server's word for it. It costs a large one-time download and is slower \
         to start.</p>\
         {browser_card}\
         </div>\
         </div>\
         </section>",
        server = SERVER_ENGINE_HREF,
        // The early return above means only the BROWSER engine reaches this grid, so the server card
        // is never the live one here and the browser card is live exactly when it can actually run.
        server_live = "",
        browser_live = if bundle { " nd-door-live" } else { "" },
        browser_card = browser_card,
    )
}

/// ⚑ **THE PAGE'S PRIMARY ACTION, AT THE TOP, GOING STRAIGHT INTO THE GAME.**
///
/// Measured click count from the landing page to a first legal move was **three**: the product's
/// "Play The Descent" CTA landed here, and here you got an intro, a *"Where do you want it to run?"*
/// chooser and a rules block, with the game itself behind a "Play now" link inside one of the two
/// cards — a page ABOUT the game rather than the game. The middle click was not a decision anybody
/// arrived wanting to make. This is the button that was missing.
///
/// **Why a CTA and not the playable surface mounted here** (the other repair on the table):
/// * this route's own [`PLAY_CSP`] carries `form-action 'none'`, and the server engine IS plain HTML
///   forms — one per move. A server-rendered board on this page could not submit a single turn
///   without relaxing the exact directive the route exists to hold.
/// * [`descent_play_router`] is deliberately additive and **state-free** — it holds no
///   `CatalogState`, so there is nothing here to render an offering session FROM.
/// * `#descent-play-root` is the wasm controller's own DOM root and `notice()`/`render()` call
///   `replaceChildren` on it, so server-rendered forms parked there would be erased the moment
///   anyone switched engines.
/// * `dreggnet-web/tests/descent_funnel.rs` pins `GET /descent/play` at `200` carrying
///   `id="descent-play-root"` — this URL serving the shell is already a decided property, so a
///   redirect straight to the session would contradict a pinned decision rather than a preference.
///
/// So each engine keeps ONE home and this is the door to it, one press wide. The hosted game's
/// address is [`SERVER_ENGINE_HREF`] — the same URL the `<noscript>` fallback and the demoted engine
/// line point at, so there is exactly one hosted-game address on the page.
fn start_here() -> String {
    format!(
        "<p class=\"nd-start\"><a class=\"nd-door-go nd-start-go\" href=\"{server}\">\
         Start today's run <span aria-hidden=\"true\">→</span></a>\
         <span class=\"nd-alt\">Starts immediately · downloads nothing · plays with JavaScript \
         off</span></p>",
        server = SERVER_ENGINE_HREF,
    )
}

/// Static, strict-CSP chrome around the same-origin native wasm bootstrap.
///
/// `claimed_actor` is the viewer's claimed public key when they hold one — rendered into
/// `data-claimed-actor` so the run this tab records is filed under a recoverable identity. `None`
/// (the anonymous default) omits the attribute entirely, leaving the page byte-identical to before.
///
/// `engine` decides whether the in-tab executor boots at all: the root carries `data-engine`, and
/// [`NATIVE_PLAY_APP_JS`]'s `boot()` returns immediately unless it reads `browser`. On the default
/// the page therefore issues no dynamic `import()` and fetches no `.wasm`.
fn shell_page(claimed_actor: Option<&str>, engine: Engine) -> String {
    let bundle = browser_bundle_present();
    let day = crate::descent::todays_day();
    // Escaped like every other attribute here, even though a claimed actor is 64 chars of
    // lowercase hex by construction (`parse_claim_label` refuses anything else): the escape is what
    // makes that a belt-and-braces rather than a load-bearing assumption about a cookie's contents.
    let claimed_attr = claimed_actor
        .map(|actor| format!(" data-claimed-actor=\"{}\"", crate::esc(actor)))
        .unwrap_or_default();
    format!(
        "<!doctype html><html lang=\"en\"><head><meta charset=\"utf-8\">\
         <meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\
         <meta name=\"color-scheme\" content=\"dark\">\
         <title>Play The Descent · {product}</title>{style}{play_style}</head><body>{topbar}\
         <main class=\"session nd-page\">\
         <header class=\"nd-intro\"><p class=\"nd-kicker\">Lean-authored · every move re-checked</p>\
         <h1>The Descent</h1>\
         <p>You go down carrying a torch that does not refill. Every verb spends one breath of it, \
         the climb out included, and a relic is only yours once a proved exit banks it.</p>\
         </header>\
         {start}{door}\
         <div id=\"descent-play-root\" data-engine=\"{engine}\" data-day-key=\"{day_key}\" \
         data-native-seed=\"{native_seed}\" data-day-source=\"{day_source}\" \
         data-guard-hp=\"{guard_hp}\"{claimed_attr}>{root_body}\
         </div>\
         <noscript><p class=\"nd-offline\" role=\"status\">The browser engine needs JavaScript \
         on. The server engine does not; it is plain HTML and one form per move, and it is the \
         same game: <a href=\"{server}\">play it here</a>.</p></noscript>\
         {rules}\
         </main>{footer}\
         <script type=\"module\" src=\"/descent/play/static/app.js\"></script>\
         </body></html>",
        // The `<title>` used to be hardcoded `DreggNet`, which the surface is no longer called;
        // every other served page reads the one constant, so this one does too.
        product = crate::PRODUCT_NAME,
        style = crate::STYLE,
        play_style = PLAY_STYLE,
        topbar = crate::topbar("descent"),
        // The primary CTA rides only on the DEFAULT engine, where the mount below it is empty and the
        // game lives at another URL. On the browser engine the game is already in this tab, so a
        // button sending the player somewhere else would be the wrong offer in the loudest place.
        start = match engine {
            Engine::Server => start_here(),
            Engine::Browser => String::new(),
        },
        door = engine_door(engine, bundle),
        engine = engine.attr(),
        server = SERVER_ENGINE_HREF,
        // The mount point is EMPTY on the default engine. "Striking a light…" is a promise that
        // something is about to boot, and on the server engine nothing is — leaving it there was a
        // spinner for a load that never starts.
        root_body = match (engine, bundle) {
            (Engine::Browser, true) => "<p class=\"nd-boot\" role=\"status\">Striking a light…</p>",
            (Engine::Browser, false) =>
                "<p class=\"nd-fatal\" role=\"status\">This deployment \
                 has no WebAssembly bundle, so the browser engine cannot start. Nothing was \
                 downloaded. Use the server engine above: it is the same game.</p>",
            (Engine::Server, _) => "",
        },
        day_key = crate::esc(&day.key),
        native_seed = native_seed_for_day(&day),
        day_source = if day.source.is_live_beacon() {
            "beacon"
        } else {
            "offline-date"
        },
        // TODAY's guardian vitalities, so a tab whose `day.json` fetch fails still sizes its
        // guardian meter against the map it is actually playing. Empty when no map resolved.
        guard_hp = crate::esc(&todays_guard_hp_attr(&day)),
        claimed_attr = claimed_attr,
        // THE RULES, BELOW THE BOARD — the same place automatafl and the tug put theirs. Passed
        // today's day provenance so the panel states which kind of day this is rather than
        // asserting the beacon on a date-derived fallback.
        rules = rules_html(day.source.is_live_beacon()),
        footer = crate::footer(),
    )
}

/// Same-origin controller for the native wasm wrapper. Dynamic values only enter
/// text nodes; game and proof material is never interpolated as HTML.
const NATIVE_PLAY_APP_JS: &str = r##"// Lean-native Descent browser controller.
import { mountDescentActionMenu } from "./actions.js";

const root = document.getElementById("descent-play-root");
const ACTOR_KEY = "dregg.native-descent.actor.v1";
let NativeDescentWorld = null;
let world = null;
let actor = null;
let recordKey = null;
let lastMessage = "A fresh run is ready. The first landed move binds it to this browser-local pseudonym.";
let lastKind = "";
let lastShare = null;
let lastShareRanked = false;
// The log's own clock. `render()` runs on every repaint, so a log line that animated on every
// render would twitch at the player constantly; it animates only when the SENTENCE changed.
let logStamp = 0;
let paintedStamp = -1;

// Say something in the run log. One place, so every message also stamps the log clock.
function say(kind, text) {
  lastKind = kind;
  lastMessage = text;
  logStamp += 1;
}
// Today's verified drand pair, when day.json resolved a beacon day. A fresh open then goes through
// `fromBeacon`, which runs the BLS pairing check in this tab (fail-closed): the run's banked-relic
// provenance root binds to the revealed round instead of the pre-computable deploy seed. Null on
// the offline day, where a fresh open falls back to the seed-derived practice world.
let dayBeaconRound = null;
let dayBeaconSig = null;
// Guards the single in-flight submit so the on-completion auto-anchor and the manual publish
// button never race one another into a double POST.
let anchorInFlight = false;

// Open a FRESH world for `seed` — beacon-bound when today is a live beacon (verified in-tab), else
// the seed-derived practice world. Restore-from-record is a separate path: a portable record
// carries its own day-seed and re-derives under it.
function openFreshWorld(seed) {
  if (dayBeaconRound !== null && dayBeaconSig) {
    return NativeDescentWorld.fromBeacon(seed, BigInt(dayBeaconRound), dayBeaconSig);
  }
  return new NativeDescentWorld(seed);
}

function notice(msg) {
  const p = document.createElement("p");
  p.className = "nd-fatal";
  p.setAttribute("role", "status");
  p.textContent = msg;
  if (root) root.replaceChildren(p);
}

function errorText(e) {
  if (e && e.stack) return String(e.stack);
  return e && e.message ? e.message : String(e);
}

function storedGet(key) {
  try { return localStorage.getItem(key); } catch (_) { return null; }
}

function storedSet(key, value) {
  try { localStorage.setItem(key, value); return true; } catch (_) { return false; }
}

function storedRemove(key) {
  try { localStorage.removeItem(key); } catch (_) {}
}

// WHO THIS RUN IS FILED UNDER.
//
// A CLAIMED identity wins over everything: the server put the viewer's public key in
// `data-claimed-actor` because they hold 24 words that reproduce it, so binding the run's hash
// chain to it means a cleared site-data costs them nothing they cannot type back. It also makes the
// actor here byte-identical to the identity the catalog attributes their automatafl/tug turns to,
// so one player is ONE name across all three shipped games.
//
// With no claim we keep the original behaviour exactly: a random per-browser pseudonym in
// localStorage. It is durable-but-unrecoverable, which is the honest deal for someone who has not
// asked for anything more, and the page's own copy says so.
function browserActor() {
  const claimed = root && root.dataset ? root.dataset.claimedActor : "";
  if (claimed && claimed.length <= 512) return claimed;
  const old = storedGet(ACTOR_KEY);
  if (old && old.length <= 512) return old;
  const bytes = new Uint8Array(24);
  crypto.getRandomValues(bytes);
  const made = "web:" + Array.from(bytes, b => b.toString(16).padStart(2, "0")).join("");
  storedSet(ACTOR_KEY, made);
  return made;
}

function node(tag, className, text) {
  const n = document.createElement(tag);
  if (className) n.className = className;
  if (text !== undefined) n.textContent = text;
  return n;
}

function shortRoot(value) {
  return value ? value.slice(0, 16) + "…" : "—";
}

function save() {
  if (recordKey && world) storedSet(recordKey, world.recordJson());
}

// The day-scoped mark that a completed run has already been anchored to the board. It keeps a
// page reload of a finished run from re-POSTing (the submit is idempotent server-side, but a
// silent mark avoids the redundant round-trip). Cleared whenever a fresh run opens.
function anchorMarkKey() {
  return recordKey ? "dregg.native-descent.anchored.v1:" + recordKey : null;
}
function anchoredAlready() {
  const key = anchorMarkKey();
  return key ? storedGet(key) !== null : false;
}
function markAnchored(runId) {
  const key = anchorMarkKey();
  if (key) storedSet(key, runId || "yes");
}
function clearAnchored() {
  const key = anchorMarkKey();
  if (key) storedRemove(key);
}

// Submit the full native record to the board's native lane — SHARED by the automatic
// on-completion anchor (`auto = true`) and the manual "Publish verified run" button
// (`auto = false`). The server runs the same exact-replay no-cheat gate either way, so a
// forged/invalid record is refused identically and never ranks; `auto` only shapes the copy.
async function submitVerifiedRun(auto) {
  if (anchorInFlight || !world) return;
  let snapshot;
  try { snapshot = JSON.parse(world.stateJson()); } catch (_) { return; }
  if (!snapshot.ended || !world.verify()) return;
  anchorInFlight = true;
  if (!auto) {
    say("", "Submitting the full native record for fresh server replay…");
    render();
  }
  try {
    const response = await fetch("/descent/native/submit", {
      method: "POST",
      headers: { "content-type": "application/json" },
      body: JSON.stringify({
        day: root.dataset.dayKey,
        record: JSON.parse(world.recordJson()),
      }),
    });
    const result = await response.json();
    if (!response.ok || !result.verified) {
      throw new Error(result.error || result.detail || "native replay was refused");
    }
    lastShare = result.share;
    lastShareRanked = result.ranked === true;
    markAnchored(result.run_id);
    const durability = result.durable === true
      ? " The artifact is in the durable Descent store."
      : " The server did not persist this artifact; keep your local replay record.";
    const anchored = result.settled === true
      ? " Anchored on the devnet node's ledger."
      : "";
    const outcome = lastShareRanked
      ? "Exact server replay passed. This crowned run now ranks in the native lane."
      : "Exact server replay passed. This settlement is shareable but did not crown, so it does not rank.";
    say("good", (auto ? "Run settled: auto-anchored to the board. " : "") + outcome + durability + anchored);
  } catch (e) {
    lastShare = null;
    say("bad", (auto
      ? "Auto-anchor did not complete; your local record is intact and the Publish button remains: "
      : "Publication refused; the local record remains intact: ") + errorText(e));
  } finally {
    anchorInFlight = false;
  }
  render();
}

// Fire the on-completion anchor exactly once per finished run: when the run has reached its
// terminal settlement and still verifies, and it has not already been anchored. This is what
// closes play -> rank end-to-end without a manual publish click.
function maybeAutoAnchor() {
  if (!world || anchorInFlight || anchoredAlready()) return;
  let snapshot;
  try { snapshot = JSON.parse(world.stateJson()); } catch (_) { return; }
  if (!snapshot.ended || !world.verify()) return;
  submitVerifiedRun(true);
}

// ═══════════════════════════════════════════════════════════════════════════════
// THE DUNGEON, PAINTED — the shaft map, the light clock, the carry ceiling.
//
// PRESENTATION ONLY. Nothing here decides a move: every "you may act on this" mark is read off
// the OFFERING'S OWN action list (`actionsJson` -> `enabled`), which is the executor-backed
// verdict, never a rule re-derived in the browser.
// ═══════════════════════════════════════════════════════════════════════════════

// The world's Lean-sourced constants, mirrored here to SIZE bars and LABEL rows. They decide
// nothing. `dreggnet-web/tests/descent_play_map.rs` pins every one of them against the Rust
// constant it mirrors, so this block cannot drift away from the game in silence.
//
// Only the numbers that are the SAME EVERY DAY may live here as literals. The map is drawn from
// the committed day-seed, so the guardian vitality table is NOT a constant: it arrives from
// `day.json` / the shell's `data-guard-hp` below, resolved by the same offering the tab opens.
const FLOORS = 4;
const RELICS = 8;
const BREATH = 30;
const CAP = 8;
const CARRIED = 8;
const BANKED = 9;
// The two prices the WAY HOME is made of. `flee` demands the surface and the climb buys one floor
// at a time, so these are the numbers every decision below ground is weighed against — see
// `climbHome`. Pinned against `dreggnet_offerings::native_descent::{LIGHT_ASCEND, LIGHT_FLEE}`.
const LIGHT_ASCEND = 1;
const LIGHT_FLEE = 1;

// TODAY's `guardHp(depth)`, indexed by depth 0..FLOORS — the drawn map's, not day 0's. Populated
// by `boot()` before anything renders; a page that could not resolve it opens no world at all,
// because a guardian meter sized against the wrong day tells a player one blow will open the hoard
// when today it takes two. FAIL-CLOSED, never a default table.
let GUARD_HP = null;

// Parse a served guardian-vitality table: exactly `FLOORS + 1` non-negative integers, depth 0
// first. Anything else is not a map and yields null (the caller refuses the open).
function parseGuardHp(raw) {
  let list = raw;
  if (typeof raw === "string") {
    list = raw.split(",").map(part => Number(part.trim()));
  }
  if (!Array.isArray(list) || list.length !== FLOORS + 1) return null;
  for (const entry of list) {
    if (!Number.isInteger(entry) || entry < 0) return null;
  }
  return list;
}

// One character per cell, so the map is the same map the Discord/Telegram/WeChat text grid paints.
const GLYPH_EMPTY = "·";
// The floor you stand on. A GLYPH, not a highlight: the highlight means "you may act on this now",
// and standing somewhere is not a move.
const GLYPH_YOU = ">";
const GLYPH_WAY_OPEN = "/";
const GLYPH_WAY_SHUT = "#";
// A guardian still standing paints the BLOWS IT OWES (a digit) — see `buildMap`. This is the
// fallen one.
const GLYPH_GUARDIAN_SLAIN = "x";
const GLYPH_CROWN = "C";
const GLYPH_KEY = "k";
const GLYPH_TREASURE = "*";
const GLYPH_PACK = "@";
const GLYPH_VAULT = "$";
// marker + way + guardian, then ONE COLUMN PER RELIC.
const MAP_COLS = 3 + RELICS;

function relicGlyph(relic) {
  if (relic === 0) return GLYPH_CROWN;
  return relic <= 3 ? GLYPH_KEY : GLYPH_TREASURE;
}

// Colour means ONE of three things on this surface: brass is light (what your torch reaches —
// relics, the floor you stand on, what you may act on), violet is proof (banked custody, a
// verified replay), rust is peril (a shut way, a standing guardian, a guttering clock). A relic
// in the dark or in the pack is lit by the torch you are burning; a banked one is lit by the
// proof that made it yours, which is why the vault row does not dim as the run runs out.
function relicTag(relic) {
  return relic === 0 ? "crown" : "relic";
}

function countCustody(sim, code) {
  return sim.custody.filter(c => c === code).length;
}

// The previous paint's custody row and remaining light. They exist so a MOVE CAN FEEL LIKE IT
// HAPPENED: the relic that changed hands lands with weight, and the breath that just went out
// keeps an ember for a beat. Both are pure presentation and both are cleared on a fresh run.
let lastCustody = null;
let lastLight = null;
// The last painted fill ratio per meter, so a bar that moved GROWS instead of teleporting. The
// DOM is rebuilt on every render, so a bare CSS transition would have nothing to move from.
const lastFill = Object.create(null);

function forgetLastPaint() {
  lastCustody = null;
  lastLight = null;
  for (const key of Object.keys(lastFill)) delete lastFill[key];
}

// A labelled meter: the bar is the argument, the numbers are the proof.
//
// `ticks` draws the track as `max` discrete pips instead of a continuous fill. That is the light
// clock's form and it is a deliberate one — this is a turn-based game where one breath buys
// exactly one verb, so the player should be able to COUNT the moves left rather than estimate a
// percentage. The pips burn left to right like a fuse; the burning edge is the flame.
function meter(label, value, max, tone, ticks) {
  const box = node("div", "nd-meter" + (tone ? " " + tone : ""));
  box.append(node("span", "nd-meter-label", label));
  const track = node("span", "nd-meter-track");
  const ratio = max > 0 ? Math.max(0, Math.min(1, value / max)) : 0;
  if (ticks) {
    for (let i = 0; i < max; i += 1) {
      const lit = i < value;
      let cls = "nd-pip " + (lit ? "lit" : "spent");
      if (lit && i === value - 1) cls += " tip";
      if (!lit && lastLight !== null && i < lastLight) cls += " guttered";
      track.append(node("span", cls));
    }
  } else {
    const fill = node("span", "nd-meter-fill");
    const from = label in lastFill ? lastFill[label] : ratio;
    fill.style.width = (from * 100).toFixed(1) + "%";
    if (from !== ratio && typeof requestAnimationFrame === "function") {
      requestAnimationFrame(() => { fill.style.width = (ratio * 100).toFixed(1) + "%"; });
    }
    lastFill[label] = ratio;
    track.append(fill);
  }
  const readout = node("span", "nd-meter-value");
  readout.append(node("b", "", String(value)), node("i", "", "/" + max));
  box.append(track, readout);
  box.setAttribute("role", "img");
  box.setAttribute("aria-label", label + " " + value + " of " + max);
  return box;
}

// One square of the shaft. `action` is an OFFERING-SUPPLIED admissible move or null — when it is a
// move the cell IS the button that takes it, so the board is directly playable and the verb list
// below stays the canonical, labelled, keyboard-first surface. A cell never decides anything: the
// only reason it lights is that the offering's own action list said `enabled: true`, and the
// executor still re-checks the move when it is submitted.
function mapCell(glyph, tag, action, title, moved) {
  const cls = "nd-cell" + (tag ? " tag-" + tag : "") + (action ? " actionable" : "") +
    (moved ? " moved" : "");
  if (!action) {
    const cell = node("span", cls, glyph);
    // The board is narrated once, as a sentence, below — sixty-six glyph cells read aloud one at
    // a time is noise, not information.
    cell.setAttribute("aria-hidden", "true");
    if (title) cell.title = title;
    return cell;
  }
  const cell = node("button", cls, glyph);
  cell.type = "button";
  cell.title = title ? title + " · " + action.label : action.label;
  cell.setAttribute("aria-label", action.label);
  cell.dataset.turn = action.turn;
  cell.dataset.arg = String(action.arg);
  cell.addEventListener("click", () => takeTurn(action));
  return cell;
}

// The shaft: a manifest row that names the eight relic columns, four floor rows, then — across a
// rule and on their own ground, because they are a LEDGER and not floors five and six — the pack
// row and the vault row. A relic keeps its COLUMN for the whole run, so you watch it travel out of
// the dark, into your pack, and into the vault.
function buildMap(sim, actions) {
  const can = (turn, arg) =>
    actions.find(a => a.turn === turn && a.arg === arg && a.enabled === true) || null;
  const moved = relic => lastCustody !== null && lastCustody[relic] !== sim.custody[relic];
  const grid = node("div", "nd-map");
  grid.style.setProperty("--nd-cols", String(MAP_COLS));
  // Which floor the torch pool sits on. The light follows the player DOWN the shaft.
  grid.style.setProperty("--nd-depth", String(sim.depth));
  grid.setAttribute("role", "group");
  grid.setAttribute("aria-label", "The shaft");

  const manifest = node("div", "nd-row nd-row-head");
  manifest.append(node("span", "nd-head-span", "shaft"));
  for (let relic = 0; relic < RELICS; relic += 1) {
    manifest.append(mapCell(relicGlyph(relic), "", null, "Relic " + relic + "'s column"));
  }
  grid.append(manifest);

  const floors = node("div", "nd-floors");
  for (let floor = 1; floor <= FLOORS; floor += 1) {
    const here = sim.depth === floor;
    const row = node("div", "nd-row" + (here ? " here" : ""));
    row.append(mapCell(here ? GLYPH_YOU : String(floor), here ? "you" : "mark", null,
      here ? "You stand on floor " + floor : "Floor " + floor));

    const open = floor === 1 || sim.ways[floor - 2] === 1;
    const passable = floor === sim.depth + 1 ? can("delve", 0) : null;
    const openable = floor >= 2 ? can("unlock", floor) : null;
    row.append(mapCell(open ? GLYPH_WAY_OPEN : GLYPH_WAY_SHUT, open ? "open" : "shut",
      open ? passable : openable,
      open ? "The way into floor " + floor + " is open" : "The way into floor " + floor + " is shut"));

    // ⚑ THE FLOOR'S PRICE, NOT JUST ITS OCCUPANT. This cell was a flat `G` on every floor, so the
    // board showed WHERE the relics were and never what reaching them costs — and guardian vitality
    // is drawn from the committed day-seed, so it IS the difference between today's dungeon and
    // yesterday's. The glyph is the BLOWS THE GUARDIAN STILL OWES: on the floor you stand on, what
    // is left of this fight (wounds are per-standing-floor); on a floor below, what that fight opens
    // at. Read out of the day's own `GUARD_HP`, never a literal.
    const vitality = GUARD_HP[floor];
    const owed = Math.max(0, vitality - (here ? sim.wounds : 0));
    const slain = here && vitality > 0 && owed === 0;
    // A floor with no guardian minted on it says nothing stands here rather than calling an absence
    // a corpse. No drawn day does this; the page still must not invent one.
    const guardGlyph = vitality === 0 ? GLYPH_EMPTY
      : owed === 0 ? GLYPH_GUARDIAN_SLAIN : String(owed);
    row.append(mapCell(guardGlyph,
      vitality === 0 ? "void" : here ? (slain ? "fallen" : "guard") : "dim",
      here ? can("smite", 0) : null,
      vitality === 0 ? "No guardian was minted on floor " + floor
        : slain ? "The floor " + floor + " guardian has fallen"
        : "The floor " + floor + " guardian owes " + owed + " more blow" + (owed === 1 ? "" : "s")));

    for (let relic = 0; relic < RELICS; relic += 1) {
      if (sim.custody[relic] === floor) {
        row.append(mapCell(relicGlyph(relic), relicTag(relic), can("loot", relic),
          "Relic " + relic + " lies on floor " + floor, moved(relic)));
      } else {
        row.append(mapCell(GLYPH_EMPTY, "void", null, null));
      }
    }
    floors.append(row);
  }
  grid.append(floors);

  grid.append(node("div", "nd-rule"));
  const band = node("div", "nd-band");
  const custodyRow = (marker, code, cellTag, what) => {
    const row = node("div", "nd-row");
    row.append(mapCell(marker, cellTag, null, what));
    row.append(mapCell(GLYPH_EMPTY, "void", null, null));
    row.append(mapCell(GLYPH_EMPTY, "void", null, null));
    for (let relic = 0; relic < RELICS; relic += 1) {
      if (sim.custody[relic] === code) {
        row.append(mapCell(relicGlyph(relic), cellTag, null, what, moved(relic)));
      } else {
        row.append(mapCell(GLYPH_EMPTY, "void", null, null));
      }
    }
    band.append(row);
  };
  custodyRow(GLYPH_PACK, CARRIED, "relic", "In your pack · still losable");
  custodyRow(GLYPH_VAULT, BANKED, "vault", "Banked · a proved exit made it yours");
  grid.append(band);
  return grid;
}

// What the glyphs mean, as a scannable list rather than two dense mono paragraphs. Built from the
// glyph constants themselves so the legend cannot fall out of step with the board.
function buildLegend() {
  const list = node("ul", "nd-legend");
  // A glyph key is a visual aid for a visual board; the board itself is narrated as a sentence
  // just above, so reading ten glyph names aloud would only be in the way.
  list.setAttribute("aria-hidden", "true");
  const entry = (glyph, meaning) => {
    const item = node("li");
    item.append(node("b", "", glyph), node("span", "", meaning));
    list.append(item);
  };
  entry(GLYPH_YOU, "you");
  entry(GLYPH_WAY_OPEN, "open way");
  entry(GLYPH_WAY_SHUT, "shut way");
  // A standing guardian paints the BLOWS IT OWES, so the legend names the digit rather than a
  // letter — that number is what a floor costs before you commit the light to reach it.
  entry("2", "blows the guardian owes");
  entry(GLYPH_GUARDIAN_SLAIN, "fallen");
  entry(GLYPH_CROWN, "the crown");
  entry(GLYPH_KEY, "way-key");
  entry(GLYPH_TREASURE, "treasure");
  entry(GLYPH_PACK, "your pack");
  entry(GLYPH_VAULT, "banked");
  return list;
}

// The board, said once, for a screen reader. Reading sixty-six cells aloud is not a board.
function narrateMap(sim, ended, carried, banked) {
  const where = ended
    ? "The run is settled."
    : sim.depth === 0
      ? "You stand at the mouth of the shaft."
      : "You stand on floor " + sim.depth + " of " + FLOORS + ".";
  return "The shaft has " + FLOORS + " floors and " + RELICS + " relics, one to a column. " +
    where + " " + carried + " relic" + (carried === 1 ? " is" : "s are") + " in your pack and " +
    banked + " " + (banked === 1 ? "is" : "are") + " banked." +
    (ended ? "" : " Every move you may make now is a verb in the list below.");
}

// THE WAY HOME — the clock the run actually plays against.
//
// `flee` demands the SURFACE and the climb buys one floor at a time, so a run standing below ground
// owes `depth` climbs plus the exit before it owes anything else. The page used to say "climbing out
// costs 1" from any depth — the price of the exit ALONE — which told a player on floor 3 holding
// 4 light that they had three to spare when they had none, and that is exactly the position that
// strands a run for good.
//
// `{ ok: true, cost }` is what the way home will take; `{ ok: false, floors }` is the doomed case
// (the light buys `floors` of climb and then dies), which the Lean model proves can never bank from
// any continuation whatsoever (`Dungeon.doomed_never_banks`). Mirrors the offering's own
// `climb_home`, which WALKS the mover's verbs rather than pricing them.
function climbHome(sim) {
  const light = Math.max(0, BREATH - sim.spent);
  const cost = sim.depth * LIGHT_ASCEND + LIGHT_FLEE;
  if (cost <= light) return { ok: true, cost: cost };
  return { ok: false, floors: Math.min(sim.depth, Math.floor(light / LIGHT_ASCEND)) };
}

// The run's one-word state. `ended` is the record's own settled bit; a run that cannot pay the one
// light every verb costs can never move again — and a run below ground whose light cannot pay the
// climb is already over while it can still move, which is the most dramatic thing this game has to
// say and used to read DELVING.
function standing(sim, ended) {
  if (ended) return { word: "BANKED", tone: "good" };
  if (sim.spent + 1 > BREATH) return { word: "THE LIGHT IS DEAD", tone: "bad" };
  if (!climbHome(sim).ok) return { word: "STRANDED", tone: "bad" };
  return { word: "DELVING", tone: "warn" };
}

// Where you are, in one sentence, in the dungeon's own voice.
function standingLine(sim, ended, banked, hoardHere) {
  if (ended) {
    return banked === 0
      ? "The tomb is closed. You came out with nothing."
      : "The tomb is closed. " + banked + " relic" + (banked === 1 ? "" : "s") +
        " came out with you.";
  }
  if (sim.depth === 0) return "You stand at the mouth of the shaft.";
  if (!climbHome(sim).ok) {
    const pack = countCustody(sim, CARRIED);
    return "Floor " + sim.depth + " is as high as the light reaches. " + pack + " relic" +
      (pack === 1 ? "" : "s") + " in the pack will never be banked, and no move from here " +
      "changes that.";
  }
  return "Floor " + sim.depth + " of " + FLOORS + ": " + (hoardHere === 0
    ? "nothing is left lying in the dark here."
    : hoardHere + " relic" + (hoardHere === 1 ? "" : "s") + " still lie" +
      (hoardHere === 1 ? "s" : "") + " in the dark here.");
}

// The torch's four states. This is the whole emotional arc of a run, so the surface names it
// rather than leaving it implicit in a number: lit, low, guttering, dead — and `out` once the
// record is closed and the clock stops meaning anything.
function torchState(light, ended) {
  if (ended) return "out";
  if (light <= 0) return "dead";
  if (light <= 4) return "guttering";
  if (light <= 8) return "low";
  return "lit";
}

function torchSay(light, ended) {
  if (ended) return "the torch is out; the record is closed.";
  if (light <= 0) return "the dark has closed: no verb can be paid for, and nothing more can be banked.";
  // ⚑ The climb is a verb PER FLOOR, not one verb. This line used to say "it costs one of these",
  // which is the price of the exit alone and the reason a player misreads the last four breaths.
  if (light <= 4) return "guttering. the climb out is a breath PER FLOOR, and then the exit.";
  if (light <= 8) return "burning low. every verb costs one breath, and the climb out is one per floor.";
  return "every verb costs one breath. what is not banked when the light dies was never yours.";
}

// The things a player is about to lose to, said out loud. Each line carries a tone so the rail can
// grade them — the peril ones are the ones that end runs.
function pressures(sim, ended) {
  const lines = [];
  if (ended) return lines;
  const light = Math.max(0, BREATH - sim.spent);
  // ⚑ THE CLIMB GOES FIRST, EVERY TURN. Below ground the light a run may actually SPEND is what is
  // left minus the way home, and that is the number every decision down here is weighed against —
  // so it is stated always, not only once the band is nearly out. (See `climbHome`.)
  if (sim.depth >= 1) {
    const home = climbHome(sim);
    if (home.ok) {
      lines.push({ tone: light - home.cost <= 2 ? "peril" : "warn",
        text: "the way home costs " + home.cost + " light: " + sim.depth + " floor" +
          (sim.depth === 1 ? "" : "s") + " of climb and the exit itself. " +
          (light - home.cost) + " light left to spend down here." });
    } else {
      lines.push({ tone: "peril", text: "STRANDED · " + light +
        " light cannot buy the way out of floor " + sim.depth + ": it pays for " + home.floors +
        " floor" + (home.floors === 1 ? "" : "s") + " of climb and then dies. Nothing in the pack " +
        "will ever be banked." });
    }
  } else if (light <= 4) {
    // At the mouth the way home IS the exit, so the old wording is true here and only here.
    lines.push({ tone: "peril", text: "the light is guttering: " + light +
      " left, and the exit itself costs " + LIGHT_FLEE });
  }
  if (sim.depth >= 1 && sim.wounds < GUARD_HP[sim.depth]) {
    const left = GUARD_HP[sim.depth] - sim.wounds;
    lines.push({ tone: "peril", text: "the guardian stands: the hoard here stays shut until it falls (" +
      left + " more strike" + (left === 1 ? "" : "s") + ", " + left * 2 + " light)" });
  }
  const pack = countCustody(sim, CARRIED);
  if (pack + 1 + sim.depth > CAP) {
    lines.push({ tone: "warn", text:
      "carrying rights are spent at this depth: the next relic would not fit" });
  }
  if (pack > 0) {
    lines.push({ tone: "proof", text: pack + " relic" + (pack === 1 ? "" : "s") +
      " ride" + (pack === 1 ? "s" : "") +
      " in the pack: nothing is yours until a proved exit banks it" });
  }
  // ⚑ NEVER LET AN ABSENCE SPEAK FOR ITSELF. With nothing pressing, the whole panel used to vanish —
  // and a missing panel is indistinguishable from a broken one. That is exactly the page a first-time
  // player opens on: turn 0, at the mouth. It is the only state that reaches here (below ground the
  // climb always has a price, and a pack is always losable), so it can name itself precisely.
  if (lines.length === 0) {
    lines.push({ tone: "", text: "nothing presses on you yet: you stand at the mouth, the light " +
      "is long and the pack is empty. Every floor you take costs a breath to leave again." });
  }
  return lines;
}

// Take a move. ONE path for the board's lit cells and the verb list alike, so a click on the
// dungeon and a click on a button are the same submitted turn across the same executor boundary.
function takeTurn(action) {
  let result;
  try { result = JSON.parse(world.advance(action.turn, action.arg, actor)); }
  catch (e) { notice("The native turn boundary failed: " + errorText(e)); return; }
  if (result.ok) {
    save();
    lastShare = null;
    say("good", "Turn committed · revision " + result.revision + " · receipt " +
      shortRoot(result.receiptHashHex));
  } else {
    say("bad", "Refused without advancing: " +
      (result.error || "the native executor declined the move"));
  }
  render();
  // If that landed move settled the run, auto-anchor it to the board (once) — no manual
  // publish needed to rank.
  maybeAutoAnchor();
}

// Keyboard play has to survive a repaint. `render()` replaces the whole shell, so without this the
// focus ring falls to the document body after every move and a keyboard player Tabs back in each
// turn. If the move that had focus is spent, focus lands on the first verb still available.
function focusKeyOf(el) {
  if (!el || !el.dataset || !el.dataset.turn) return null;
  // The same move is reachable from two places — a lit cell on the board and its verb button — so
  // the key carries WHICH, and focus comes back to the surface the player was actually using.
  const where = el.classList && el.classList.contains("nd-cell") ? "cell" : "verb";
  return where + ":" + el.dataset.turn + ":" + el.dataset.arg;
}

function restoreFocus(shell, wanted) {
  if (!wanted || !shell.querySelectorAll) return;
  for (const control of shell.querySelectorAll("[data-turn]")) {
    if (focusKeyOf(control) === wanted) { control.focus({ preventScroll: true }); return; }
  }
  const first = shell.querySelector(".nd-actions button");
  if (first) first.focus({ preventScroll: true });
}

function render() {
  const held = root.contains && root.contains(document.activeElement)
    ? focusKeyOf(document.activeElement) : null;
  const snapshot = JSON.parse(world.stateJson());
  const sim = snapshot.state;
  const actions = JSON.parse(world.actionsJson(actor));
  const carried = countCustody(sim, CARRIED);
  const banked = countCustody(sim, BANKED);
  const hoardHere = countCustody(sim, sim.depth);
  const light = Math.max(0, BREATH - sim.spent);
  const ratio = BREATH > 0 ? light / BREATH : 0;

  const shell = node("section", "nd-shell");
  // ── THE ROOM IS LIT BY THE RUN ──
  // `--nd-dim` is the dark closing in and `--nd-glow` is how far the torch still reaches. Both are
  // read straight off the light the executor has actually charged for, so the atmosphere is the
  // resource — not a mood setting layered on top of it. Neither decides anything.
  //
  // AND WHEN THE RUN ENDS, THE LIGHTS COME UP. A settled surface is no longer a dungeon you are
  // trying to survive; it is the receipt for one, and a receipt has to be read.
  shell.style.setProperty("--nd-dim",
    (snapshot.ended ? 0.12 : Math.pow(1 - ratio, 1.6) * 0.62).toFixed(3));
  shell.style.setProperty("--nd-glow", (snapshot.ended ? 0.5 : 0.26 + 0.74 * ratio).toFixed(3));

  // ── THE RUN HEADER: one word, one sentence, the provenance. ──
  const state = standing(sim, snapshot.ended);
  const head = node("header", "nd-run");
  const status = node("div", "nd-status");
  status.append(node("span", "nd-pill " + state.tone, state.word));
  if (snapshot.ended) {
    status.append(node("span", "nd-terminal", snapshot.crowned ? "crowned exit" : "exit settled"));
  }
  head.append(status);
  head.append(node("p", "nd-standing", standingLine(sim, snapshot.ended, banked, hoardHere)));
  const verified = world.verify();
  const meta = node("div", "nd-meta");
  meta.append(node("span", "", "day " + (root.dataset.dayKey || "local")));
  meta.append(node("span", "", "turn " + snapshot.revision + " · seed " + snapshot.seed));
  meta.append(node("span", "", root.dataset.daySource === "beacon"
    ? "drand beacon day" : "offline-date day"));
  meta.append(node("span", "nd-proof" + (verified ? "" : " bad"),
    verified ? "replay verified" : "verification failed"));
  head.append(meta);
  shell.append(head);

  // ── THE TORCH: the clock, and the loudest thing on the page. ──
  const torch = node("div", "nd-torch");
  torch.dataset.state = torchState(light, snapshot.ended);
  const torchHead = node("div", "nd-torch-head");
  torchHead.append(node("span", "nd-torch-label", "torch"));
  torchHead.append(node("p", "nd-torch-say", torchSay(light, snapshot.ended)));
  torch.append(torchHead);
  torch.append(meter("light", Math.max(0, BREATH - sim.spent), BREATH,
    light <= 4 ? "low" : "", true));
  shell.append(torch);

  // ── THE SETTLEMENT: once the run ends, the receipt is the surface. ──
  if (snapshot.ended) {
    const settled = node("div", "nd-settled");
    settled.append(node("h2", "", snapshot.crowned ? "A crowned exit" : "The exit settled"));
    settled.append(node("p", "", snapshot.crowned
      ? "Every relic in the shaft came out with you. The record is closed, and once the server's own replay accepts it this run ranks in the day's native lane."
      : banked + " relic" + (banked === 1 ? "" : "s") + " banked. The record is closed; a settlement that is not crowned stays shareable and verifiable, but it does not rank."));
    if (lastShare) {
      const share = node("a", "nd-share",
        lastShareRanked ? "Open ranked native proof →" : "Open verified native record →");
      share.href = lastShare;
      settled.append(share);
    }
    shell.append(settled);
  }

  // ── THE ARENA: the shaft, and the vitals beside it. ──
  const arena = node("div", "nd-arena");
  const shaft = node("section", "nd-shaft");
  shaft.append(node("h2", "nd-shaft-heading", "the shaft"));
  const mapwrap = node("div", "nd-mapwrap");
  mapwrap.append(buildMap(sim, actions));
  shaft.append(mapwrap);
  shaft.append(buildLegend());
  shaft.append(node("p", "nd-legend-note",
    "One column per relic, kept for the whole run: you watch a relic travel out of the dark, " +
    "into the pack, into the vault. A cell your torch picks out is one you may act on now: " +
    "press it, or take the same move from the verbs below."));
  arena.append(shaft);

  const rail = node("aside", "nd-rail");
  const vitals = node("div", "nd-panel");
  vitals.append(node("h2", "nd-panel-head", "vitals"));
  const meters = node("div", "nd-meters");
  meters.append(meter("pack", carried, Math.max(0, CAP - sim.depth),
    carried + 1 + sim.depth > CAP ? "low" : ""));
  if (sim.depth >= 1) {
    meters.append(meter("guardian", sim.wounds, GUARD_HP[sim.depth],
      sim.wounds >= GUARD_HP[sim.depth] ? "done" : ""));
  }
  meters.append(meter("banked", banked, RELICS, banked > 0 ? "done" : ""));
  vitals.append(meters);
  rail.append(vitals);

  const pressing = pressures(sim, snapshot.ended);
  if (pressing.length > 0) {
    const panel = node("div", "nd-panel");
    panel.append(node("h2", "nd-panel-head", "pressure"));
    for (const line of pressing) panel.append(node("p", "nd-pressure " + line.tone, line.text));
    rail.append(panel);
  }
  arena.append(rail);
  shell.append(arena);

  // ── THE VERBS. ──
  const actionMenu = node("section", "nd-action-menu");
  mountDescentActionMenu(actionMenu, actions, { ended: snapshot.ended, onChoose: takeTurn });
  shell.append(actionMenu);

  // ── THE LOG: what just happened. It animates only when the sentence CHANGED. ──
  // ⚑ AND WHERE THE BOARD NOW STANDS. `narrateMap` — the board said ONCE, as a sentence, instead of
  // sixty-six cells read aloud — used to sit beside the map in a plain `sr-only` paragraph with no
  // live region anywhere on the page, so after a move NOTHING pointed a screen-reader user at the
  // updated position: the map is redrawn silently and the only announced line was the log. It is now
  // the second half of this one `role="status"` element (implicitly `aria-atomic`, so both are read
  // together): what happened, then where that leaves you. The board itself stays out of every live
  // region — the whole point of narrating it once.
  const message = node("p",
    ["nd-message", lastKind, logStamp !== paintedStamp ? "fresh" : ""].filter(Boolean).join(" "),
    lastMessage);
  message.setAttribute("role", "status");
  message.append(node("span", "sr-only",
    " " + narrateMap(sim, snapshot.ended, carried, banked)));
  paintedStamp = logStamp;
  shell.append(message);

  // ── THE RECORD: provenance tools, deliberately quiet. ──
  const record = node("footer", "nd-record");
  const tools = node("div", "nd-tools");
  const verify = node("button", "", "Verify full record");
  verify.type = "button";
  verify.addEventListener("click", () => {
    const report = JSON.parse(world.verifyJson());
    say(report.verified ? "good" : "bad", report.verified
      ? "Fresh replay accepted all " + report.turns + " receipts."
      : "Replay verification refused: " + report.detail);
    render();
  });
  const copy = node("button", "", "Copy replay record");
  copy.type = "button";
  copy.addEventListener("click", async () => {
    try {
      await navigator.clipboard.writeText(world.recordJson());
      say("good", "The versioned replay record is on your clipboard.");
    } catch (e) {
      say("bad", "Clipboard refused; your local run remains intact: " + errorText(e));
    }
    render();
  });
  // A terminal run auto-anchors on completion, so this button is an explicit RE-submit (the same
  // idempotent POST). It stays enabled after an auto-anchor so a player can re-publish on demand.
  const publish = node("button", snapshot.ended ? "primary" : "",
    snapshot.ended ? "Publish verified run" : "Settle before publishing");
  publish.type = "button";
  publish.disabled = !snapshot.ended || !verified;
  publish.addEventListener("click", () => { submitVerifiedRun(false); });
  const restart = node("button", "danger", "Abandon this run");
  restart.type = "button";
  restart.addEventListener("click", () => {
    if (restart.dataset.armed !== "yes") {
      restart.dataset.armed = "yes";
      restart.textContent = "Press again to abandon";
      setTimeout(() => {
        restart.dataset.armed = "";
        restart.textContent = "Abandon this run";
      }, 4000);
      return;
    }
    storedRemove(recordKey);
    clearAnchored();
    try { world.free(); } catch (_) {}
    world = openFreshWorld(Number(root.dataset.nativeSeed));
    lastShare = null;
    forgetLastPaint();
    say("", "Fresh run opened. No previous record was installed.");
    render();
  });
  tools.append(verify, copy, publish, restart);
  record.append(tools);
  record.append(node("p", "nd-root",
    "journal root " + snapshot.rootHex + " · actor " + (snapshot.actor || "unclaimed")));
  shell.append(record);

  root.replaceChildren(shell);
  restoreFocus(shell, held);
  // What this paint SAW, so the next one can show what changed.
  lastCustody = sim.custody.slice();
  lastLight = light;
}

async function boot() {
  if (!root) return;
  // ⚑ THE OPT-IN GATE. The server renders data-engine="server" unless the reader asked for the
  // browser engine by name, and on the server engine this module does NOTHING: no dynamic import,
  // no .wasm fetch, no day.json request, no BLS pairing. Running the whole ruleset in a tab is a
  // tens-of-megabytes download and a slow first paint, so it happens because somebody chose it.
  // The server-side door is rendered above this mount point by `engine_door`, in plain HTML, so it
  // is there whether or not this script ever runs.
  if (root.dataset.engine !== "browser") return;
  let wasm;
  try {
    wasm = await import("/descent/play/static/dregg_wasm.js");
    await wasm.default();
  } catch (e) {
    notice("The browser engine could not start: this deployment is not serving a WebAssembly "
      + "bundle. Nothing is lost. The same game runs on the server, from the link above. ("
      + errorText(e) + ")");
    return;
  }
  if (typeof wasm.NativeDescentWorld !== "function") {
    notice("The WebAssembly artifact predates NativeDescentWorld; refusing to open the older game.");
    return;
  }
  NativeDescentWorld = wasm.NativeDescentWorld;

  let today = null;
  try {
    const response = await fetch("/descent/play/static/day.json", { cache: "no-store" });
    if (response.ok) today = await response.json();
  } catch (_) {}
  const dayKey = today && today.key ? today.key : root.dataset.dayKey;
  const nativeSeed = today && Number.isInteger(today.nativeSeed)
    ? today.nativeSeed : Number(root.dataset.nativeSeed);
  if (!dayKey || !Number.isInteger(nativeSeed) || nativeSeed < 0) {
    notice("Today's native seed descriptor is malformed; no world was opened.");
    return;
  }
  // TODAY's guardian vitalities — the drawn map's, from the descriptor (or the shell's fallback
  // attribute). Not a constant and not defaulted: the map varies with the day-seed, and a meter
  // sized against day 0's guardians misprices the one resource the run cannot refill.
  GUARD_HP = parseGuardHp(today && today.guardHp) || parseGuardHp(root.dataset.guardHp);
  if (!GUARD_HP) {
    notice("Today's dungeon map did not resolve, so no guardian could be sized honestly; no world was opened.");
    return;
  }
  root.dataset.dayKey = dayKey;
  root.dataset.nativeSeed = String(nativeSeed);
  // A verified beacon day carries its raw drand pair; a fresh open then binds the run's provenance
  // to that revealed round through `fromBeacon` (the in-tab BLS check). The offline day omits it.
  if (today && today.source === "beacon"
      && Number.isInteger(today.round) && typeof today.signatureHex === "string"
      && today.signatureHex.length > 0) {
    dayBeaconRound = today.round;
    dayBeaconSig = today.signatureHex;
  } else {
    dayBeaconRound = null;
    dayBeaconSig = null;
  }
  actor = browserActor();
  recordKey = "dregg.native-descent.record.v1:" + dayKey;
  const retained = storedGet(recordKey);
  try {
    world = retained
      ? NativeDescentWorld.fromRecordJson(retained)
      : openFreshWorld(nativeSeed);
    const snapshot = JSON.parse(world.stateJson());
    const expected = (nativeSeed % 251) + 1;
    if (snapshot.seed !== expected) throw new Error("retained record belongs to another native day");
    if (retained) say("", "Local record restored only after exact native replay.");
  } catch (e) {
    storedRemove(recordKey);
    clearAnchored();
    try { world = openFreshWorld(nativeSeed); }
    catch (openError) { notice("Native world deployment refused: " + errorText(openError)); return; }
    say("bad", "A retained record was refused and discarded: " + errorText(e));
  }
  // The first paint has nothing to compare against, so nothing lands or gutters on it.
  forgetLastPaint();
  render();
  // A restored run that already reached its terminal settlement but was never anchored (e.g. the
  // tab closed the moment it settled) auto-anchors now. A run anchored in a prior visit carries
  // its mark and is skipped.
  maybeAutoAnchor();
}

boot().catch(e => notice("Could not start The Descent: " + errorText(e)));
"##;

/// The placeholder served for `dregg_wasm.js` until the real `wasm-pack --target web` glue is
/// built. Its default `init` throws, so the bootstrap's try/catch degrades to an honest notice.
const WASM_GLUE_PLACEHOLDER_JS: &str = r##"// PLACEHOLDER — the wasm `--target web` glue is NOT vendored on this build.
// Build it in the workspace package directory:
//   wasm-pack build wasm --target web --out-dir pkg --release
export default async function () {
  throw new Error("dregg_wasm.js placeholder: the wasm bundle is not vendored (see descent_play.rs).");
}
export const __DESCENT_WASM_PLACEHOLDER = true;
"##;

#[cfg(test)]
mod tests {
    use axum::response::IntoResponse;

    #[tokio::test]
    async fn the_play_page_ships_a_strict_wasm_csp_and_mounts_the_native_root() {
        let resp = super::get_descent_play(
            axum::http::HeaderMap::new(),
            axum::extract::Query(super::PlayQuery::default()),
        )
        .await;
        let csp = resp
            .headers()
            .get("content-security-policy")
            .expect("CSP header present")
            .to_str()
            .unwrap();
        // Strict, same-origin scripts + the one WebAssembly concession — never unsafe-inline/eval.
        assert!(
            csp.contains("script-src 'self' 'wasm-unsafe-eval'"),
            "wasm CSP"
        );
        assert!(
            !csp.contains("'unsafe-inline'") || !csp.contains("script-src 'self' 'unsafe-inline'")
        );
        assert!(!csp.contains("'unsafe-eval'") || csp.contains("'wasm-unsafe-eval'"));
        assert!(csp.contains("connect-src 'self'"), "same-origin wasm fetch");

        let html = super::shell_page(None, super::Engine::Browser);
        assert!(html.contains("id=\"descent-play-root\""));
        assert!(
            !html.contains("<dregg-descent"),
            "the older procgen custom element must not remain the flagship"
        );
        let day = crate::descent::todays_day();
        assert!(
            html.contains(&format!(
                "data-native-seed=\"{}\"",
                super::native_seed_for_day(&day)
            )),
            "the native game gets a deterministic committed daily seed"
        );
        assert!(
            html.contains("/descent/play/static/app.js"),
            "same-origin bootstrap module"
        );
        // No CDN / external script origin (the /tg/link discipline).
        assert!(!html.contains("esm.sh") && !html.contains("https://cdn"));
        // The no-script fallback is the SERVER ENGINE — the same offering, hosted, as forms.
        assert!(
            html.contains("<noscript>") && html.contains(super::SERVER_ENGINE_HREF),
            "no-script fallback points at the server engine"
        );
    }

    /// ⚑ **IN-BROWSER EXECUTION IS OPT-IN.** A bare `/descent/play` must mount the SERVER engine:
    /// no `data-engine="browser"`, so `app.js`'s `boot()` returns before it imports anything, and no
    /// visitor pays a tens-of-megabytes download for pressing the flagship CTA. The browser engine
    /// is reached only by asking for it by name.
    #[test]
    fn the_browser_engine_is_opt_in_and_the_server_engine_is_the_default() {
        let default_page = super::shell_page(None, super::Engine::Server);
        assert!(
            default_page.contains("data-engine=\"server\""),
            "the default page mounts the server engine"
        );
        assert!(
            !default_page.contains("data-engine=\"browser\""),
            "nothing on the default page asks the bootstrap to load WebAssembly"
        );
        // The server engine is not merely the default — it is REACHABLE from the default page, as a
        // real link, in server-rendered HTML that does not need the script to run.
        assert!(
            default_page.contains(&format!("href=\"{}\"", super::SERVER_ENGINE_HREF)),
            "the default page links to the hosted game"
        );
        // And the browser engine is offered BY NAME, with its cost stated, never silently entered.
        assert!(
            default_page.contains("href=\"/descent/play?engine=browser\"")
                || default_page.contains("was not built here"),
            "the browser engine is an explicit choice (or is honestly reported as unavailable)"
        );

        // Only the named values select it, and every other input falls to the server — a default
        // must fail toward the cheap, always-available engine.
        assert_eq!(
            super::Engine::from_query(Some("browser")),
            super::Engine::Browser
        );
        assert_eq!(
            super::Engine::from_query(Some("wasm")),
            super::Engine::Browser
        );
        for miss in [None, Some(""), Some("Browser"), Some("server"), Some("yes")] {
            assert_eq!(
                super::Engine::from_query(miss),
                super::Engine::Server,
                "{miss:?} must not opt anyone into the browser engine"
            );
        }

        // The opted-in page really does mount it (so the assertions above are not vacuous).
        let opted = super::shell_page(None, super::Engine::Browser);
        assert!(opted.contains("data-engine=\"browser\""));
    }

    /// ⚑ **THE BOOTSTRAP OBEYS THE GATE.** The opt-in is only worth anything if the module honours
    /// it, so pin the guard in the served JavaScript itself: `boot()` returns before its dynamic
    /// `import()` unless the root says `browser`.
    #[tokio::test]
    async fn the_bootstrap_refuses_to_load_wasm_unless_the_browser_engine_was_chosen() {
        use axum::body::to_bytes;
        let resp = super::get_play_app_js().await.into_response();
        let js = String::from_utf8(
            to_bytes(resp.into_body(), 1 << 22)
                .await
                .expect("app.js body")
                .to_vec(),
        )
        .expect("app.js is utf-8");
        let gate = js
            .find(r#"if (root.dataset.engine !== "browser") return;"#)
            .expect("boot() carries the engine gate");
        let import = js
            .find(r#"import("/descent/play/static/dregg_wasm.js")"#)
            .expect("boot() imports the glue");
        assert!(
            gate < import,
            "the gate must precede the import, or the download happens anyway"
        );
    }

    #[tokio::test]
    async fn the_bootstrap_wires_native_replay_persistence_and_actions() {
        use axum::body::to_bytes;
        let resp = super::get_play_app_js().await.into_response();
        assert_eq!(
            resp.headers().get("content-type").unwrap(),
            "text/javascript; charset=utf-8"
        );
        let body = to_bytes(resp.into_body(), 1 << 20).await.unwrap();
        let js = std::str::from_utf8(&body).unwrap();
        // No extension-side mirror: this is the thin controller over the native
        // Offering wrapper, including exact restore and verification.
        for needle in [
            "mountDescentActionMenu",
            "./actions.js",
            "NativeDescentWorld",
            "fromRecordJson",
            "recordJson",
            "stateJson",
            "actionsJson",
            "world.advance",
            "verifyJson",
            "localStorage",
            "/descent/play/static/dregg_wasm.js",
            "/descent/play/static/day.json",
            "/descent/native/submit",
            "Publish verified run",
        ] {
            assert!(js.contains(needle), "bootstrap references {needle}");
        }
        assert!(
            !js.contains("DescentEngine"),
            "old game engine is not mounted"
        );
    }

    /// The controller AUTO-ANCHORS a completed run to the board — the on-completion submit that
    /// closes play -> rank without a manual publish — while keeping the explicit Publish button and
    /// the same-origin submit endpoint. String-level (the wasm-driven runtime path is exercised
    /// server-side by `tests/descent_native_leaderboard.rs`).
    #[tokio::test]
    async fn the_controller_auto_anchors_a_completed_run() {
        use axum::body::to_bytes;
        let resp = super::get_play_app_js().await.into_response();
        let body = to_bytes(resp.into_body(), 1 << 20).await.unwrap();
        let js = std::str::from_utf8(&body).unwrap();
        // The shared submit + the on-completion trigger, fired from a landed move and from boot.
        for needle in [
            "submitVerifiedRun",
            "maybeAutoAnchor",
            "snapshot.ended",
            "/descent/native/submit",
            // The idempotence mark that keeps a reload from re-POSTing.
            "dregg.native-descent.anchored.v1:",
            // The explicit re-submit stays.
            "Publish verified run",
        ] {
            assert!(
                js.contains(needle),
                "auto-anchor controller references {needle}"
            );
        }
        // The auto-anchor is triggered right after a landed move renders, and once on boot.
        assert_eq!(
            js.matches("maybeAutoAnchor();").count(),
            2,
            "auto-anchor fires on the terminal move and on a restored-completed boot"
        );
        // A run still in progress must never be uploaded: the trigger is gated on the terminal
        // settlement + a passing verify.
        assert!(js.contains("!snapshot.ended || !world.verify()"));
    }

    #[tokio::test]
    async fn the_accessible_action_helper_is_a_same_origin_javascript_asset() {
        use axum::body::to_bytes;

        let resp = super::get_play_actions_js().await.into_response();
        assert_eq!(
            resp.headers().get("content-type").unwrap(),
            "text/javascript; charset=utf-8"
        );
        let body = to_bytes(resp.into_body(), 1 << 20).await.unwrap();
        let js = std::str::from_utf8(&body).unwrap();
        assert!(js.contains("export function mountDescentActionMenu"));
        assert!(js.contains("enabled === true"));
        assert!(js.contains("unavailable"));
    }

    #[test]
    fn wasm_snippet_route_accepts_only_nested_javascript_components() {
        assert!(super::safe_snippet_path("biscuit-auth-deadbeef/inline0.js").is_some());
        for refused in [
            "../secret.js",
            "crate/../../secret.js",
            "/absolute/secret.js",
            "crate/inline0.wasm",
            "crate/inline0",
        ] {
            assert!(
                super::safe_snippet_path(refused).is_none(),
                "must refuse {refused}"
            );
        }
    }

    /// `day.json` serves TODAY'S committed day descriptor with an honest provenance label,
    /// uncached. Procgen and native game modes derive their distinct deterministic worlds from it.
    #[tokio::test]
    async fn the_day_route_serves_todays_real_day() {
        let resp = super::get_play_day_json().await;
        assert_eq!(
            resp.headers().get("cache-control").unwrap(),
            "no-store",
            "a cached descriptor would pin a stale day"
        );
        let body = axum::body::to_bytes(resp.into_body(), 1 << 16)
            .await
            .unwrap();
        let v: serde_json::Value = serde_json::from_slice(&body).unwrap();
        let day = crate::descent::todays_day();
        assert_eq!(v["key"], day.key, "the cross-process day key");
        assert_eq!(v["epochHex"], day.epoch_hex());
        assert_eq!(
            v["nativeSeed"],
            super::native_seed_for_day(&day),
            "the browser and server derive the same native seed input"
        );
        // The provenance is REPORTED, never assumed live.
        assert!(v["source"] == "beacon" || v["source"] == "offline-date");
        // The full epoch re-derives the procgen board seed. Native play intentionally consumes the
        // separately published normalized native input and submits to its distinct replay lane.
        assert_eq!(
            procgen_dregg::daily_seed(&day.epoch).as_bytes(),
            day.seed.as_bytes()
        );
    }

    /// **THE DAY'S GUARDIANS ARE PUBLISHED, AND THEY ARE THE SESSION'S.**
    ///
    /// The map — relic homes and per-floor guardian vitality — is drawn from the committed
    /// day-seed. The page used to carry `descent::guard_hp`'s DAY-0 table as a JS literal, so on
    /// fifteen of the sixteen drawn days it sized the guardian meter against a guardian that does
    /// not exist: a `0/1` bar under a two-point guardian, and a hoard that stays shut after the
    /// blow the picture said would open it.
    ///
    /// The pin is not "the descriptor carries some numbers" — it is that the descriptor's table is
    /// the table a session OPENED the way the tab opens it actually plays. A mirror re-derived
    /// here would only pin this test against itself.
    #[tokio::test]
    async fn the_descriptor_publishes_the_days_own_guardian_vitalities() {
        use dreggnet_offerings::{Offering, SessionConfig};

        let day = crate::descent::todays_day();
        let seed = u64::from(super::native_seed_for_day(&day));
        // No process armed a live beacon in a test, so the tab's own branch here is the
        // seed-derived practice world — the same one `todays_day_world` resolves.
        assert!(
            super::play_beacon(&day).is_none(),
            "this test asserts the seed-derived branch; a live beacon armed in-process changes it"
        );
        let session = dreggnet_offerings::native_descent::NativeDescentOffering::new()
            .open(SessionConfig::with_seed(seed))
            .expect("today's native world opens");
        let played: Vec<u64> = session.day_world().ghp.to_vec();

        let body = axum::body::to_bytes(super::get_play_day_json().await.into_body(), 1 << 16)
            .await
            .unwrap();
        let v: serde_json::Value = serde_json::from_slice(&body).unwrap();
        assert_eq!(
            v["guardHp"],
            serde_json::json!(played),
            "the descriptor publishes the guardian vitalities the DEPLOYED session fights, not a \
             constant table"
        );

        // The shell's fallback attribute carries the same table, so a tab whose `day.json` fetch
        // fails still sizes its meter against today's dungeon rather than day 0's.
        let html = super::shell_page(None, super::Engine::Browser);
        let attr = format!(
            "data-guard-hp=\"{}\"",
            played
                .iter()
                .map(u64::to_string)
                .collect::<Vec<_>>()
                .join(",")
        );
        assert!(
            html.contains(&attr),
            "the shell carries today's guardian table as `{attr}`:\n{html}"
        );

        // And it is a DAY fact, not day 0's table wearing a new name: on any day the draw moved a
        // guardian, the published numbers move with it.
        let day_zero: Vec<u64> = dungeon_on_dregg::descent::CANON_WORLD.ghp.to_vec();
        if played != day_zero {
            assert_ne!(
                v["guardHp"],
                serde_json::json!(day_zero),
                "today's drawn map is not day 0's, so the published table must not be day 0's"
            );
        }
    }

    /// **THE PAGE CARRIES ITS OWN LOOK — no off-origin byte, no silent webfont.**
    ///
    /// The design leans on typography, so the temptation to reach for a font CDN is real and it is
    /// exactly the hole the `/tg/link` review closed for scripts. `font-src 'self'` already
    /// refuses one at runtime, which means a stylesheet that asked for a remote face would not
    /// degrade — it would render in a fallback nobody chose, silently, only in production. So the
    /// stylesheet is pinned to name no remote origin at all, and to set both faces from stacks
    /// that are already resident on the reader's machine.
    ///
    /// Falsifier: paste a `@import url(https://fonts.googleapis.com/...)` into [`PLAY_STYLE`].
    #[test]
    fn the_play_surface_is_self_contained_and_typeset_from_resident_faces() {
        let page = super::shell_page(None, super::Engine::Browser);
        for smell in [
            "@import",
            "url(http",
            "url('http",
            "fonts.googleapis",
            "fonts.gstatic",
            "cdn.jsdelivr",
            "unpkg.com",
            "//esm.sh",
        ] {
            assert!(
                !page.contains(smell),
                "the play page must fetch nothing off-origin, and it references `{smell}`"
            );
        }
        // Two faces, both resident: a serif for the dungeon's voice, a mono for everything the
        // game measures. Neither names a webfont family.
        assert!(
            super::PLAY_STYLE.contains("--nd-serif:ui-serif,")
                && super::PLAY_STYLE.contains("--nd-mono:ui-monospace,"),
            "the type stacks start at the platform's own UI faces"
        );
    }

    /// **THE LIGHT IS THE GAME, SO THE SURFACE IS LIT BY IT.**
    ///
    /// Three properties, each of which a restyle could quietly drop while still looking fine on a
    /// full torch:
    ///
    /// - the light clock is DISCRETE — one pip per breath, because one breath buys exactly one
    ///   verb and a player should be able to COUNT the moves left rather than eyeball a bar;
    /// - the shaft's own lighting (`--nd-dim`, `--nd-glow`, `--nd-depth`) is computed from the run
    ///   the executor has actually charged, so the dark closing in is the RESOURCE and not a mood;
    /// - motion is honoured as optional: `prefers-reduced-motion` turns all of it off, and none of
    ///   the information lives in the motion.
    #[tokio::test]
    async fn the_light_clock_is_counted_and_the_room_is_lit_by_the_run() {
        use axum::body::to_bytes;
        let resp = super::get_play_app_js().await.into_response();
        let js =
            String::from_utf8(to_bytes(resp.into_body(), 1 << 20).await.unwrap().to_vec()).unwrap();

        // The clock is drawn as BREATH discrete pips (the `ticks` argument), with the burning edge
        // marked, and the breath just spent keeps an ember for one beat of feedback.
        assert!(
            js.contains("meter(\"light\", Math.max(0, BREATH - sim.spent), BREATH,")
                && js.contains("light <= 4 ? \"low\" : \"\", true)"),
            "the light meter is the TICKED one — a plain fill would make the one countable \
             resource in the game uncountable"
        );
        for needle in ["nd-pip", "\" tip\"", "\" guttered\""] {
            assert!(js.contains(needle), "the pip clock draws {needle}");
        }
        // The atmosphere is a function of the run, not a constant.
        for needle in ["--nd-dim", "--nd-glow", "--nd-depth"] {
            assert!(
                js.contains(needle),
                "the controller drives `{needle}` from the live snapshot"
            );
        }
        assert!(
            js.contains("snapshot.ended ? 0.12 :"),
            "a settled run brings the lights UP — a closed record is a receipt to read"
        );
        // Motion is a nicety everywhere it appears.
        assert!(
            super::PLAY_STYLE.contains("@media(prefers-reduced-motion:reduce)"),
            "every animation on this surface is disabled for readers who asked for that"
        );
    }

    /// **THE BOARD IS PLAYABLE, AND IT IS STILL NOT A REFEREE.**
    ///
    /// A lit cell is a real button that takes the move, which is what makes the surface feel like
    /// a game rather than a readout — but the whole risk of that change is a browser that starts
    /// deciding what is legal. It does not: a cell lights only because the OFFERING's own action
    /// list decorated that `{turn, arg}` `enabled: true`, and pressing it goes through the same
    /// single [`takeTurn`] path (and therefore the same `world.advance` executor boundary) as the
    /// labelled verb list. The verb list stays the canonical surface — every move, including the
    /// refused ones, with its price named.
    #[tokio::test]
    async fn a_lit_cell_is_the_offerings_verdict_and_takes_the_same_executor_path() {
        use axum::body::to_bytes;
        let resp = super::get_play_app_js().await.into_response();
        let js =
            String::from_utf8(to_bytes(resp.into_body(), 1 << 20).await.unwrap().to_vec()).unwrap();

        assert!(
            js.contains(
                "actions.find(a => a.turn === turn && a.arg === arg && a.enabled === true)"
            ),
            "a cell lights from the offering's own action row, never from a rule re-derived here"
        );
        assert!(
            js.contains("cell.addEventListener(\"click\", () => takeTurn(action));")
                && js.contains("onChoose: takeTurn"),
            "the board and the verb list submit through ONE path"
        );
        assert_eq!(
            js.matches("world.advance(").count(),
            1,
            "there is exactly one place a turn crosses the executor boundary"
        );
        // Keyboard play has to survive the repaint that a landed move causes.
        assert!(
            js.contains("restoreFocus(shell, held)"),
            "focus is restored after the shell is replaced, or every move costs a keyboard \
             player a Tab hunt"
        );
        // Wide content scrolls in its OWN well; the page body never scrolls sideways on a phone.
        assert!(
            super::PLAY_STYLE.contains(".nd-mapwrap{overflow-x:auto"),
            "the shaft gets its own scroll container"
        );
    }

    #[tokio::test]
    async fn an_unvendored_wasm_blob_fails_closed_with_an_honest_503() {
        // An explicit bad asset root is exclusive, so the blob route is an honest
        // 503 rather than silently serving an arbitrary stale workspace build.
        // SAFETY: single-threaded set of a process env for this scoped assertion.
        unsafe {
            std::env::set_var(
                "DESCENT_PLAY_ASSET_DIR",
                "/nonexistent/dregg-descent-play-assets",
            );
        }
        let blob = super::get_play_wasm_blob().await;
        assert_eq!(blob.status(), axum::http::StatusCode::SERVICE_UNAVAILABLE);

        let glue = super::get_play_wasm_glue().await;
        assert_eq!(glue.status(), axum::http::StatusCode::OK);
        let cbody = axum::body::to_bytes(glue.into_body(), 1 << 16)
            .await
            .unwrap();
        assert!(
            std::str::from_utf8(&cbody)
                .unwrap()
                .contains("__DESCENT_WASM_PLACEHOLDER")
        );
        unsafe {
            std::env::remove_var("DESCENT_PLAY_ASSET_DIR");
        }
    }

    /// ⚑ THE PANEL EXISTS AND IS ON THE PAGE. Automatafl and the tug each carry a rules block on
    /// their own landing; the Descent's play page carried none, so a first-time player met a shaft,
    /// a torch band and seven priced verbs with no statement of the objective. Pinned as a
    /// structural fact, not as prose: the heading and the section must reach the served shell.
    #[test]
    fn the_play_page_states_the_rules_before_the_first_press() {
        let page = super::shell_page(None, super::Engine::Browser);
        assert!(
            page.contains("class=\"nd-rules\"") && page.contains("The rules, in one screen"),
            "the play page must carry the rules block the other two shipped games carry"
        );
        assert!(
            super::PLAY_STYLE.contains(".nd-rules{"),
            "the rules block must be styled, not fall back to unstyled default HTML"
        );
        // The objective, the clock and the stake — the three a stranger cannot infer from a board.
        for claim in ["climb back out", "never refills", "Banking ends the run"] {
            assert!(page.contains(claim), "the rules omit `{claim}`");
        }
    }

    /// The panel's numbers are the GAME's, so a rules change cannot leave it quietly wrong. Checked
    /// against the constants rather than against the literals the panel happens to print today.
    #[test]
    fn the_rules_quote_the_games_own_constants() {
        use dreggnet_offerings::native_descent::{CARRY_CAP, DUNGEON_FLOORS, LIGHT_BREATH};
        let rules = super::rules_html(true);
        assert!(
            rules.contains(&format!("{LIGHT_BREATH} breaths")),
            "the light budget must be the game's: {rules}"
        );
        assert!(
            rules.contains(&format!("{DUNGEON_FLOORS} floors deep")),
            "the depth must be the game's"
        );
        assert!(
            rules.contains(&format!("carry {CARRY_CAP}")),
            "the carry cap must be the game's"
        );
        // The bottom-floor squeeze is the whole design; it must be stated as the derived number.
        assert!(
            rules.contains(&format!("{} at the bottom", CARRY_CAP - DUNGEON_FLOORS)),
            "the bottom-floor capacity must be derived, not typed: {rules}"
        );
    }

    /// ⚑ NEVER LET AN ABSENCE SPEAK FOR ITSELF (`docs/reference/UX-QA-SWEEP-2026-07-26.md`). On a
    /// beacon day the dungeon genuinely could not be picked in advance; on the date-derived
    /// fallback it could. The panel must say which, and must NOT carry the unpredictability claim
    /// on the day where it is false.
    #[test]
    fn the_provenance_claim_is_true_on_both_kinds_of_day() {
        let beacon = super::rules_html(true);
        assert!(
            beacon.contains("could pick it in advance"),
            "a beacon day may state the unpredictability: {beacon}"
        );
        let offline = super::rules_html(false);
        assert!(
            !offline.contains("could pick it in advance"),
            "a date-derived day must not claim nobody could pick it in advance: {offline}"
        );
        assert!(
            offline.contains("derived from the date"),
            "the date-derived day must say so: {offline}"
        );
    }

    /// The DEFAULT identity is an unsigned cookie with no recovery, and the in-progress run lives in
    /// this browser. The panel must warn rather than reassure — a player who clears their browser
    /// loses everything, and finding that out afterwards is the worst possible way.
    ///
    /// The claim is written to stay true while [`crate::seed_identity`] lands beside it: the cookie
    /// default is what you get by DOING NOTHING, which no opt-in recovery phrase changes. Once that
    /// route is live and settled, this paragraph should get stronger — it should name the phrase and
    /// link it — and this test should tighten with it.
    #[test]
    fn the_rules_do_not_promise_a_durable_run() {
        let rules = super::rules_html(true);
        assert!(
            rules.contains("no recovery"),
            "the cookie default's lack of recovery must be stated: {rules}"
        );
        assert!(
            rules.contains("clearing your browser data loses it"),
            "the cookie/localStorage loss must be stated plainly: {rules}"
        );
        for lie in ["your account", "saved to your profile", "sign in", "log in"] {
            assert!(
                !rules.to_lowercase().contains(lie),
                "the rules imply a durable identity with `{lie}`"
            );
        }
    }
}
